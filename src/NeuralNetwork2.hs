{-# LANGUAGE DataKinds, KindSignatures, TypeOperators, GADTs, TemplateHaskell, TypeFamilies, UndecidableInstances, Rank2Types, AllowAmbiguousTypes, ScopedTypeVariables, MultiParamTypeClasses, FlexibleInstances, FlexibleContexts, PolyKinds, BangPatterns #-}
{-# OPTIONS_GHC -fplugin=GHC.TypeLits.Normalise #-}

module NeuralNetwork2 where

import Data.Array.Accelerate.LLVM.Native as B
import qualified Data.Type.List as L
import Helpers
import GHC.TypeLits
import Data.Maybe
import Data.Singletons
import Data.Singletons.TH
import Data.Promotion.TH
import Data.Singletons.TypeLits
import Data.Singletons.Prelude.Eq
import Data.Singletons.Prelude.Bool
import Data.Singletons.Prelude.Num
import Data.Singletons.Prelude.Maybe
import Data.Singletons.Prelude.List
import Data.Graph.Inductive
import Data.Type.Equality
import Data.Typeable
import Data.Array.Accelerate as A
import Data.List
import ValueAndDerivative
import Debug.Trace

--trace _ = id
--traceShow _ = id

mse :: (A.Num e) => [Acc (Matrix e)] -> [Acc (Array DIM4 e)] -> Acc (Array DIM2 e)
mse t o = A.fold (A.+) 0 $ A.fold (A.+) 0 $ Prelude.foldl1 (A.zipWith (A.+)) s
  where to = Prelude.zip t o
        d = Prelude.map (\(t, o) -> z t o) to
        s = Prelude.map (A.map $ \x -> x A.* x) d
        z t o =
          let
            Z :. w :. h :. _ :. _ = unlift $ shape o :: Z :. Exp Int :. Exp Int :. Exp Int :. Exp Int
            t' = A.replicate (lift $ Z :. w :. h :. All :. All) t
          in
            A.zipWith (-) t' o

unsingleton :: (Elt e) => Acc (Array DIM4 e) -> Acc (Matrix e)
unsingleton a =
  let
    Z:. _:. _ :. w :. h = unlift $ shape a :: Z :. Exp Int :. Exp Int :. Exp Int :. Exp Int
  in
    A.reshape (lift $ Z:.w:.h) a

singleton :: (Elt e) => Acc (Matrix e) -> Acc (Array DIM4 e)
singleton a =
  let
    Z :. w :. h = unlift $ shape a :: Z :. Exp Int :. Exp Int
  in
    A.reshape (lift $ Z:.(1 :: Exp Int):.(1 :: Exp Int):.w:.h) a

singleton' :: (Elt e) => Acc (Matrix e) -> Acc (Array DIM4 e)
singleton' a =
  let
    Z :. w :. h = unlift $ shape a :: Z :. Exp Int :. Exp Int
  in
    A.reshape (lift $ Z:.w:.h:.(1 :: Exp Int):.(1 :: Exp Int)) a

pFlatten :: (Elt e) => PList l e -> Acc (Vector e)
pFlatten PNil = A.use $ A.fromList (Z:.0) []
pFlatten (PCons _ _ a pt) = (A.flatten a) A.++ (pFlatten pt)

pUnflatten :: (Elt e) => Sing l -> Acc (Vector e) -> PList l e
pUnflatten SNil a = PNil
pUnflatten (SCons (STuple2 sw sh) sl) a =
  let
    i = A.take (expVal sw * expVal sh) a
    r = A.drop (expVal sw * expVal sh) a
  in
    pCons2 sw sh (reshape (index2 (expVal sw) (expVal sh)) i) (pUnflatten sl r)

jacobian :: forall e . (A.Num e) => (Acc (Array DIM4 (ValueAndDerivative e)) -> Acc (Array DIM4 (ValueAndDerivative e))) -> Acc (Matrix e) -> Acc (Array DIM4 e)
jacobian f a = b'
  where Z:. w :. h = unlift $ shape a :: Z :. Exp Int :. Exp Int
        a' = A.replicate (lift $ Z :. w :. h :. All :. All) $ A.map fromValue a
        diag k =
          let
            Z:. i' :. j' :. i :. j = unlift $ k :: Z :. Exp Int :. Exp Int :. Exp Int :. Exp Int
          in
            i A.== i' A.&& j A.== j'
        a'' = A.imap (\k x -> cond (diag k) (lift1 (withDerivative 1) x) x) $ a'
        b = f a''
        b' = A.map derivative b

timesJacobian1 :: (A.Num e) => (Acc (Array DIM4 (ValueAndDerivative e)) -> Acc (Array DIM4 (ValueAndDerivative e))) -> Acc (Matrix e) -> Acc (Matrix e) -> Acc (Matrix e)
timesJacobian1 f !v !t = seq r r
  where Z:. w :. h = unlift $ shape v :: Z :. Exp Int :. Exp Int
        Z:. w' :. h' = unlift $ shape t :: Z :. Exp Int :. Exp Int
        t' = A.replicate (lift $ Z :. w :. h :. All :. All) t
        j = jacobian f v
        p = A.zipWith (A.*) j t'
        r = fold (A.+) 0 $ fold (A.+) 0 p

applyExcept :: Int -> ([a] -> a) -> [a] -> a -> a
applyExcept j f xs y =
  let
    xs' = Prelude.map (\(i, x) -> if i Prelude.== j then y else x) (Prelude.zip [0..] xs)
  in
    f xs'

mapApplyExcept :: ([a] -> a) -> [a] -> [a -> a]
mapApplyExcept f xs = Prelude.map (\i -> applyExcept i f xs) [0..(Prelude.length xs - 1)]

timesJacobianL :: (A.Num e) => ([Acc (Array DIM4 (ValueAndDerivative e))] -> Acc (Array DIM4 (ValueAndDerivative e))) -> [Acc (Matrix e)] -> Acc (Matrix e) -> [Acc (Matrix e)]
timesJacobianL f as b = Prelude.map (\(f, a) -> timesJacobian1 f a b) $ Prelude.zip fs as
  where fs = mapApplyExcept f $ Prelude.map (singleton . A.map fromValue) as

timesJacobianL' :: (A.Num e) => ([Acc (Array DIM4 (ValueAndDerivative e))] -> Acc (Array DIM4 (ValueAndDerivative e))) -> [Acc (Matrix e)] -> Acc (Matrix e) -> [Acc (Matrix e)]
timesJacobianL' f as b = Prelude.map (\(f, a) -> A.use $ B.run1 (\x -> let (b, c) = unlift x in timesJacobian1 f c b) $ (B.run a, B.run b)) $ Prelude.zip fs as
  where fs = mapApplyExcept f $ Prelude.map (singleton . A.map fromValue) as

timesJacobian2 :: (A.Num e) => (Acc (Array DIM4 (ValueAndDerivative e)) -> Acc (Array DIM4 (ValueAndDerivative e)) -> Acc (Array DIM4 (ValueAndDerivative e))) -> Acc (Matrix e) -> Acc (Matrix e) -> Acc (Matrix e) -> (Acc (Matrix e), Acc (Matrix e))
timesJacobian2 f a1 a2 b = (r1, r2)
  where f' [a1, a2] = f a1 a2
        [r1, r2] = timesJacobianL f' [a1, a2] b

data AtIndexNat (l :: [Nat]) (e :: Nat) (i :: Nat) where
  HeadNat :: AtIndexNat (x ': xs) x 0
  TailNat :: AtIndexNat t x i -> AtIndexNat (h ': t) x (i + 1)

data AtIndex (l :: [(Nat, Nat)]) (e :: (Nat, Nat)) (i :: Nat) where
  Head :: AtIndex ('(w, h) ': xs) '(w, h) 0
  Tail :: AtIndex t x i -> AtIndex (h ': t) x (i + 1)

type Matrix e = Array DIM2 e

data PList (l :: [(Nat, Nat)]) e where
  PNil :: PList '[] e
  PCons :: Sing w -> Sing h -> !(Acc (Matrix e)) -> !(PList l e) -> PList ('(w, h) ': l) e

pNil :: (A.Elt e) => PList '[] e
pNil = PNil

pCons :: (A.Elt e) => PList ('(w, h) ': '[]) e -> PList l e -> PList ('(w, h) ': l) e
pCons (PCons sw sh a PNil) pl = PCons sw sh a pl

pCons2 :: (A.Elt e) => SNat w -> SNat h -> Acc (Matrix e) -> PList l e -> PList ('(w, h) ': l) e
pCons2 sw sh a pl = PCons sw sh a pl

pUncons :: (A.Elt e) => PList ('(w, h) ': l) e -> (PList ('(w, h) ': '[]) e, PList l e)
pUncons (PCons sw sh a pl) =
    (PCons sw sh a PNil, pl)

pUncons2 :: (A.Elt e) => PList ('(w, h) ': l) e -> ((SNat w, SNat h, Acc (Matrix e)), PList l e)
pUncons2 pl =
  let
    (ph, pt) = pUncons pl
  in
    (pBreak2 ph, pt)

pHead :: (A.Elt e) => PList ('(w, h) ': l) e -> PList ('(w, h) ': '[]) e
pHead = Prelude.fst . pUncons

pTail :: (A.Elt e) => PList ('(w, h) ': l) e -> PList l e
pTail = Prelude.snd . pUncons

pSingleton2 :: (A.Elt e) => SNat w -> SNat h -> Acc (Matrix e) -> PList ('(w, h) ': '[]) e
pSingleton2 sw sh a = pCons2 sw sh a pNil

pBreak2 :: (A.Elt e) => PList ('(w, h) ': '[]) e -> (SNat w, SNat h, Acc (Matrix e))
pBreak2 (PCons sw sh a PNil) = (sw, sh, a)

pAdd :: (A.Num e) => AtIndex l '(w, h) i -> PList l e -> PList ('(w, h) ': '[]) e -> PList l e
pAdd Head pl ps =
  let
    (sw, sh, b) = pBreak2 ps
    ((_, _, a), pt) = pUncons2 pl
  in
    pCons2 sw sh (A.zipWith (A.+) a b) pt
pAdd (Tail p) pl@(PCons _ _ _ _) ps =
  let
    (ph, pt) = pUncons pl
  in
    pCons ph (pAdd p pt ps)

pAt :: (A.Elt e) => AtIndex l '(w, h) i -> PList l e -> PList ('(w, h) ': '[]) e
pAt Head pl = pHead pl
pAt (Tail p) pl@(PCons _ _ _ _) = pAt p (pTail pl)

pAt2 :: (A.Elt e) => AtIndex l '(w, h) i -> PList l e -> Acc (Matrix e)
pAt2 Head pl =
  let
    ph = pHead pl
    (_, _, a) = pBreak2 ph
  in
    a
pAt2 (Tail p) pl@(PCons _ _ _ _) = pAt2 p (pTail pl)

pSplit :: (Elt e) => Sing l -> Sing l' -> PList (l :++ l') e -> (PList l e, PList l' e)
pSplit SNil sl' pl = (pNil, pl)
pSplit (SCons (STuple2 sw sh) sl) sl' pl =
  let
    (ph, pt) = pUncons pl
    (p1, p2) = pSplit sl sl' pt
  in
    (pCons ph p1, p2)

pJoin :: (Elt e) => PList l e -> PList l' e -> PList (l :++ l') e
pJoin PNil pl' = pl'
pJoin pl@(PCons _ _ _ _) pl' =
  let
    (ph, pt) = pUncons pl
  in
    pCons ph (pJoin pt pl')

newtype Label = Label String
instance Show Label where
  show (Label s) = s

type UnaryFunction e (w :: Nat) (h :: Nat) (w' :: Nat) (h' :: Nat) = (Elt e) => (SNat w, SNat h, SNat w', SNat h', Acc (Array DIM4 e) -> Acc (Array DIM4 e), Label)
type BinaryFunction e (w :: Nat) (h :: Nat) (w' :: Nat) (h' :: Nat) (w'' :: Nat) (h'' :: Nat) = (Elt e) => (SNat w, SNat h, SNat w', SNat h', SNat w'', SNat h'', Acc (Array DIM4 e) -> Acc (Array DIM4 e) -> Acc (Array DIM4 e), Label)

tnh :: (A.Floating a, Elt a) => Exp a -> Exp a
tnh x = ((exp x) - (exp (-x))) / ((exp x) + (exp (-x)))

tanh ::(A.Floating a) => SNat w -> SNat h -> UnaryFunction a w h w h
tanh sw sh = (sw, sh, sw, sh, A.map tnh, Label "tanh")

sgm :: (A.Floating a, Elt a) => Exp a -> Exp a
sgm x = 1 / (1 + exp (-x))

sigm ::(A.Floating a) => SNat w -> SNat h -> UnaryFunction a w h w h
sigm sw sh = (sw, sh, sw, sh, A.map sgm, Label "sigm")

esum :: (A.Num e) => SNat w -> SNat h -> BinaryFunction e w h w h w h
esum sw sh = (sw, sh, sw, sh, sw, sh, A.zipWith (+), Label ".+")

eprod :: (A.Num e) => SNat w -> SNat h -> BinaryFunction e w h w h w h
eprod sw sh = (sw, sh, sw, sh, sw, sh, A.zipWith (*), Label ".*")

matchArgs a b = (a', b')
  where Z :. w  :. h  :. k :. l = unlift (shape a) :: Z :. Exp Int :. Exp Int :. Exp Int :. Exp Int
        Z :. w' :. h' :. m :. n = unlift (shape b) :: Z :. Exp Int :. Exp Int :. Exp Int :. Exp Int
        a' = acond (w  A.* h  A.== 1) (A.replicate (lift $ Z :. w' :. h' :. All :. All) $ A.reshape (lift $ Z :. k :. l) a) a
        b' = acond (w' A.* h' A.== 1) (A.replicate (lift $ Z :. w  :. h  :. All :. All) $ A.reshape (lift $ Z :. m :. n) b) b

prd :: (A.Num e, Elt e) => Acc (Array DIM4 e) -> Acc (Array DIM4 e) -> Acc (Array DIM4 e)
prd a b = A.fold (+) 0 $ A.zipWith (*) aRepl bRepl
  where
    Z :. w  :. h  :. rowsA :.     z = unlift (shape a)    :: Z :. Exp Int :. Exp Int :. Exp Int :. Exp Int
    Z :. w' :. h' :.     _ :. colsB = unlift (shape b)    :: Z :. Exp Int :. Exp Int :. Exp Int :. Exp Int
    (a', b') = matchArgs a b
    aRepl = A.replicate (lift $ Z :. All :. All :. All   :. colsB :. All) a'
    bRepl = A.replicate (lift $ Z :. All :. All :. rowsA :. All   :. All) (A.backpermute (permute $ shape b') permute b')
    permute :: Exp DIM4 -> Exp DIM4
    permute = lift1 $ \(Z:.(x :: Exp Int):.(y :: Exp Int):.(z :: Exp Int):.(w :: Exp Int)) -> Z:.x:.y:.w:.z

prod :: (A.Num e, Elt e) => SNat a -> SNat b -> SNat c -> BinaryFunction e a b b c a c
prod sa sb sc = (sa, sb, sb, sc, sa, sc, prd, Label "*")

concat :: forall e a b c . SNat a -> SNat b -> SNat c -> BinaryFunction e a b a c a (b+c)
concat sa sb sc = (sa, sb, sa, sc, sa, sb %:+ sc, \a b -> let (a', b') = matchArgs a b in a' A.++ b', Label "++")

data NeuralNetwork a (l :: [(Nat, Nat)]) (w :: [(Nat, Nat)]) (i :: [(Nat, Nat)]) (ps :: [(Nat, Nat)]) (po :: [(Nat, Nat)]) (s :: [(Nat, Nat)]) (o :: [(Nat, Nat)]) where
  Empty :: NeuralNetwork a '[] '[] '[] '[] '[] '[] '[]
  Unity :: SNat w -> SNat h -> NeuralNetwork a ('(w, h) ': '[]) '[] '[] '[] '[] '[] '[]
  Weight :: SNat w -> SNat h -> NeuralNetwork a ('(w, h) ': '[]) ('(w, h) ': '[]) '[] '[] '[] '[] '[]
  Input :: SNat w -> SNat h -> NeuralNetwork a ('(w, h) ': '[]) '[] ('(w, h) ': '[]) '[] '[] '[] '[]
  PreviousState :: SNat w -> SNat h -> NeuralNetwork a ('(w, h) ': '[]) '[] '[] ('(w, h) ': '[]) '[] '[] '[]
  PreviousOutput :: SNat w -> SNat h -> NeuralNetwork a ('(w, h) ': '[]) '[] '[] '[] ('(w, h) ': '[]) '[] '[]
  State :: AtIndex l '(w, h) i -> NeuralNetwork a l ww ii ps po s o -> SNat i -> SNat w -> SNat h -> NeuralNetwork a ('(w, h) ': l) ww ii ps po ('(w, h) ': s) o
  Output :: AtIndex l '(w, h) i -> NeuralNetwork a l ww ii ps po s o -> SNat i -> SNat w -> SNat h -> NeuralNetwork a ('(w, h) ': l) ww ii ps po s ('(w, h) ': o)
  Union :: NeuralNetwork a l1 w1 i1 ps1 po1 s1 o1 -> Sing l1 -> Sing w1 -> Sing i1 -> Sing ps1 -> Sing po1 -> Sing s1 -> Sing o1 -> NeuralNetwork a l2 w2 i2 ps2 po2 s2 o2 -> Sing l2 -> Sing w2 -> Sing i2 -> Sing ps2 -> Sing po2 -> Sing s2 -> Sing o2 -> NeuralNetwork a (l1 :++ l2) (w1 :++ w2) (i1 :++ i2) (ps1 :++ ps2) (po1 :++ po2) (s1 :++ s2) (o1 :++ o2)
  Unary :: (Elt a) => AtIndex l '(w, h) i -> NeuralNetwork a l ww ii ps po s o -> SNat i -> SNat w -> SNat h -> UnaryFunction a w h w' h' -> NeuralNetwork a ('(w', h') ': l) ww ii ps po s o
  Binary :: (Elt a) => AtIndex l '(w, h) i -> AtIndex l '(w', h') j -> NeuralNetwork a l ww ii ps po s o -> SNat i -> SNat w -> SNat h -> SNat j -> SNat w' -> SNat h' -> BinaryFunction a w h w' h' w'' h'' -> NeuralNetwork a ('(w'', h'') ': l) ww ii ps po s o

concat_with_nil :: Sing (l :: [(Nat, Nat)]) -> l :~: Concat (l ': '[] ': '[])
concat_with_nil SNil = Refl
concat_with_nil (SCons _ sl) = gcastWith (concat_with_nil sl) Refl

addWeight :: Sing l -> Sing ww -> Sing i -> Sing ps -> Sing po -> Sing s -> Sing o -> SNat w -> SNat h -> NeuralNetwork a l ww i ps po s o -> NeuralNetwork a ('(w, h) ': l) ('(w, h) ': ww) i ps po s o
addWeight sl sww si sps spo ss so sw sh nn =
    Union (Weight sw sh) (SCons (STuple2 sw sh) SNil) (SCons (STuple2 sw sh) SNil) SNil SNil SNil SNil SNil nn sl sww si sps spo ss so

addWeightedEdge :: (A.Num e, Elt e) => AtIndex l '(a, b) i -> Sing l -> Sing w -> Sing ii -> Sing ps -> Sing po -> Sing s -> Sing o -> SNat a -> SNat b -> SNat c -> SNat i -> NeuralNetwork e l w ii ps po s o -> NeuralNetwork e ('(a, c) ': '(b, c) ': l) ('(b, c) ': w) ii ps po s o
addWeightedEdge sp sl sw sii sps spo ss so sa sb sc si nn =
  let
    (nn', sp') = (addWeight sl sw sii sps spo ss so sb sc nn, Head)
  in
    Binary (Tail sp) sp' nn' (si %:+ (sing :: SNat 1)) sa sb (sing :: SNat 0) sb sc (prod sa sb sc)

addInducedLocalField :: (A.Num e, Elt e) => AtIndex l '(a, b) i -> Sing l -> Sing w -> Sing ii -> Sing ps -> Sing po -> Sing s -> Sing o -> SNat a -> SNat b -> SNat c -> SNat i -> NeuralNetwork e l w ii ps po s o -> NeuralNetwork e ('(a, c) ': '(b+1, c) ': '(a, b+1) ': '(a, 1) ': l) ('(b+1, c) ': w) ii ps po s o
addInducedLocalField sp sl sw sii sps spo ss so sa sb sc si nn =
  let
    s0 = sing :: SNat 0
    s1 = sing :: SNat 1
    nn' = Union (Unity sa s1) (SCons (STuple2 sa s1) SNil) SNil SNil SNil SNil SNil SNil nn sl sw sii sps spo ss so
    sl' = SCons (STuple2 sa s1) sl
    sp' = Tail sp
    nn'' = Binary sp' Head nn' (si %:+ s1) sa sb s0 sa s1 (NeuralNetwork2.concat sa sb s1)
    sl'' = SCons (STuple2 sa (sb %:+ s1)) sl'
  in
    addWeightedEdge Head sl'' sw sii sps spo ss so sa (sb %:+ s1) sc s0 nn''

addNeuron :: (A.Num e, Elt e) => UnaryFunction e 1 o 1 o -> AtIndex l '(1, i) x -> Sing l -> Sing w -> Sing ii -> Sing ps -> Sing po -> Sing s -> Sing oo -> SNat i -> SNat o -> SNat x -> NeuralNetwork e l w ii ps po s oo -> NeuralNetwork e ('(1, o) ': '(1, o) ': '(i+1, o) ': '(1, i+1) ': '(1, 1) ': l) ('(i+1, o) ': w) ii ps po s oo
addNeuron sf sp sl sw sii sps spo ss soo si so sx nn =
  let
    s0 = sing :: SNat 0
    s1 = sing :: SNat 1
    nn' = addInducedLocalField sp sl sw sii sps spo ss soo s1 si so sx nn
  in
    Unary Head nn' s0 s1 so sf
  
addLSTMLayer :: forall e i o l x w ii ps po s oo . (A.Floating e, Elt e) => AtIndex l '(1, i) x -> Sing l -> Sing w -> Sing ii -> Sing ps -> Sing po -> Sing s -> Sing oo -> SNat i -> SNat o -> SNat x -> NeuralNetwork e l w ii ps po s oo -> (NeuralNetwork e ('(1, o) ': '(1, o) ': '(1, o) ': '(1, o) ': '(1, o) ': '(1, o) ': '(1, o) ': '(1, o) ': '(1, o) ': '(1, o) ': '(i+o+1, o) ': '(1, i+o+1) ': '(1, 1) ': '(1, o) ': '(1, o) ': '(i+o+1, o) ': '(1, i+o+1) ': '(1, 1) ': '(1, o) ': '(1, o) ': '(i+o+1, o) ': '(1, i+o+1) ': '(1, 1) ': '(1, o) ': '(1, o) ': '(i+o+1, o) ': '(1, i+o+1) ': '(1, 1) ': '(1, i+o) ': '(1, o) ': l) ('(i+o+1, o) ': '(i+o+1, o) ': '(i+o+1, o) ': '(i+o+1, o) ': w) ii ('(1, o) ': ps) ('(1, o) ': po) ('(1, o) ': s) ('(1, o) ': oo), Sing ('(1, o) ': '(1, o) ': '(1, o) ': '(1, o) ': '(1, o) ': '(1, o) ': '(1, o) ': '(1, o) ': '(1, o) ': '(1, o) ': '(i+o+1, o) ': '(1, i+o+1) ': '(1, 1) ': '(1, o) ': '(1, o) ': '(i+o+1, o) ': '(1, i+o+1) ': '(1, 1) ': '(1, o) ': '(1, o) ': '(i+o+1, o) ': '(1, i+o+1) ': '(1, 1) ': '(1, o) ': '(1, o) ': '(i+o+1, o) ': '(1, i+o+1) ': '(1, 1) ': '(1, i+o) ': '(1, o) ': l), Sing ('(i+o+1, o) ': '(i+o+1, o) ': '(i+o+1, o) ': '(i+o+1, o) ': w), Sing ii, Sing ('(1, o) ': ps), Sing ('(1, o) ': po), Sing ('(1, o) ': s), Sing ('(1, o) ': oo))
addLSTMLayer sp sl sw sii spstate spoutput ss soo si so sx nn =
  let
    s0 = sing :: SNat 0
    s1 = sing :: SNat 1
    s2 = sing :: SNat 2
    s3 = sing :: SNat 3
    s4 = sing :: SNat 4
    s5 = sing :: SNat 5
    sio = si %:+ so

    nn' = Union (PreviousOutput s1 so) (SCons (STuple2 s1 so) SNil) SNil SNil SNil (SCons (STuple2 s1 so) SNil) SNil SNil nn sl sw sii spstate spoutput ss soo
    sl' = SCons (STuple2 s1 so) sl
    spoutput' = SCons (STuple2 s1 so) spoutput
    sx' = sx %:+ s1
    sp' = Tail sp
    
    nn'' = Binary sp' Head nn' sx' s1 si s0 s1 so (NeuralNetwork2.concat s1 si so)
    sl'' = SCons (STuple2 s1 sio) sl'
    sx'' = s0
    sp'' = Head

    nn''' = addNeuron (sigm s1 so) sp'' sl'' sw sii spstate spoutput' ss soo sio so sx'' nn''
    sl''' = SCons (STuple2 s1 so) $ SCons (STuple2 s1 so) $ SCons (STuple2 (sio %:+ s1) so) $ SCons (STuple2 s1 (sio %:+ s1)) $ SCons (STuple2 s1 s1) sl''
    sw' = SCons (STuple2 (sio %:+ s1) so) sw
    sx''' = sx'' %:+ s5
    sp''' = Tail $ Tail $ Tail $ Tail $ Tail sp''

    nn'''' = addNeuron (sigm s1 so) sp''' sl''' sw' sii spstate spoutput' ss soo sio so sx''' nn'''
    sl'''' = SCons (STuple2 s1 so) $ SCons (STuple2 s1 so) $ SCons (STuple2 (sio %:+ s1) so) $ SCons (STuple2 s1 (sio %:+ s1)) $ SCons (STuple2 s1 s1) sl'''
    sw'' = SCons (STuple2 (sio %:+ s1) so) sw'
    sx'''' = sx''' %:+ s5
    sp'''' = Tail $ Tail $ Tail $ Tail $ Tail sp'''

    nn''''' = addNeuron (sigm s1 so) sp'''' sl'''' sw'' sii spstate spoutput' ss soo sio so sx'''' nn''''
    sl''''' = SCons (STuple2 s1 so) $ SCons (STuple2 s1 so) $ SCons (STuple2 (sio %:+ s1) so) $ SCons (STuple2 s1 (sio %:+ s1)) $ SCons (STuple2 s1 s1) sl''''
    sw''' = SCons (STuple2 (sio %:+ s1) so) sw''
    sx''''' = sx'''' %:+ s5
    sp''''' = Tail $ Tail $ Tail $ Tail $ Tail sp''''

    nn'''''' = addNeuron (NeuralNetwork2.tanh s1 so) sp''''' sl''''' sw''' sii spstate spoutput' ss soo sio so sx''''' nn'''''
    sl'''''' = SCons (STuple2 s1 so) $ SCons (STuple2 s1 so) $ SCons (STuple2 (sio %:+ s1) so) $ SCons (STuple2 s1 (sio %:+ s1)) $ SCons (STuple2 s1 s1) sl'''''
    sw'''' = SCons (STuple2 (sio %:+ s1) so) sw'''
    sx'''''' = sx''''' %:+ s5
    sp'''''' = Tail $ Tail $ Tail $ Tail $ Tail sp'''''

    nn''''''' =  Union (PreviousState s1 so) (SCons (STuple2 s1 so) SNil) SNil SNil (SCons (STuple2 s1 so) SNil) SNil SNil SNil nn'''''' sl'''''' sw'''' sii spstate spoutput' ss soo
    sl''''''' = SCons (STuple2 s1 so) sl''''''
    spstate' = SCons (STuple2 s1 so) spstate

    spst = s0
    sc  = s1
    sou = s1 %:+ s5
    sin = s1 %:+ s5 %:+ s5
    sf  = s1 %:+ s5 %:+ s5 %:+ s5
    sps = Head
    spc = Tail $ Head
    spo = Tail $ Tail $ Tail $ Tail $ Tail spc
    spi = Tail $ Tail $ Tail $ Tail $ Tail spo
    spf = Tail $ Tail $ Tail $ Tail $ Tail spi

    nn'''''''' = Binary spf sps nn'''''''  sf s1 so spst s1 so (eprod s1 so)
    sl'''''''' = SCons (STuple2 s1 so) $ sl'''''''

    nn''''''''' = Binary (Tail spi) (Tail spc) nn''''''''  (s1 %:+ sin) s1 so (s1 %:+ sc) s1 so (eprod s1 so)
    sl''''''''' = SCons (STuple2 s1 so) $ sl''''''''

    nn'''''''''' = Binary Head (Tail Head) nn'''''''''  s0 s1 so s1 s1 so (esum s1 so)
    sl'''''''''' = SCons (STuple2 s1 so) $ sl'''''''''

    snst = s0
    spns = Head

    nn''''''''''' = Unary Head nn''''''''''  s0 s1 so (NeuralNetwork2.tanh s1 so)
    sl''''''''''' = SCons (STuple2 s1 so) $ sl''''''''''

    nn'''''''''''' = Binary Head (Tail $ Tail $ Tail $ Tail spo) nn'''''''''''  s0 s1 so (s4 %:+ sou) s1 so (eprod s1 so)
    sl'''''''''''' = SCons (STuple2 s1 so) $ sl'''''''''''
    
    nn''''''''''''' = State (Tail $ Tail Head) nn'''''''''''' (s2 %:+ snst) s1 so
    sl''''''''''''' = SCons (STuple2 s1 so) $ sl''''''''''''
    ss' = SCons (STuple2 s1 so) $ ss

    nn'''''''''''''' = Output (Tail Head) nn''''''''''''' s1 s1 so
    sl'''''''''''''' = SCons (STuple2 s1 so) $ sl'''''''''''''
    soo' = SCons (STuple2 s1 so) $ soo
  in
    (
      nn'''''''''''''',
      sl'''''''''''''',
      sw'''',
      sii,
      spstate',
      spoutput',
      ss',
      soo'
    )

showVal :: Sing (n :: Nat) -> String
showVal sn = show $ fromInteger $ withKnownNat sn $ natVal sn

val :: Graph gr => Sing (n :: Nat) -> gr a b -> Int
val sn g = noNodes g - 1 - (fromInteger $ withKnownNat sn $ natVal sn)

toFGL' :: DynGraph gr => gr Label Label -> NeuralNetwork e l w i ps po s o -> gr Label Label
toFGL' g Empty = g
toFGL' g (Unity w h) = ([], noNodes g, Label ("U:"Prelude.++(showVal w)Prelude.++"x"Prelude.++(showVal h)), []) & g
toFGL' g (Weight w h) = ([], noNodes g, Label ("W:"Prelude.++(showVal w)Prelude.++"x"Prelude.++(showVal h)), []) & g
toFGL' g (Input w h) = ([], noNodes g, Label ("I:"Prelude.++(showVal w)Prelude.++"x"Prelude.++(showVal h)), []) & g
toFGL' g (PreviousState w h) = ([], noNodes g, Label ("PS:"Prelude.++(showVal w)Prelude.++"x"Prelude.++(showVal h)), []) & g
toFGL' g (PreviousOutput w h) = ([], noNodes g, Label ("PO:"Prelude.++(showVal w)Prelude.++"x"Prelude.++(showVal h)), []) & g
toFGL' g (State _ nn i w h) =
  let
    g' = toFGL' g  nn
  in
  ([(Label((showVal w)Prelude.++"x"Prelude.++(showVal h)), val i g')], noNodes g', Label("S:"Prelude.++(showVal w)Prelude.++"x"Prelude.++(showVal h)), []) & g'
toFGL' g (Output _ nn i w h) =
  let
    g' = toFGL' g  nn
  in
  ([(Label((showVal w)Prelude.++"x"Prelude.++(showVal h)), val i g')], noNodes g', Label("O"Prelude.++(showVal w)Prelude.++"x"Prelude.++(showVal h)), []) & g'
toFGL' g (Union nn1 _ _ _ _ _ _ _ nn2 _ _ _ _ _ _ _) = toFGL' (toFGL' g nn2) nn1
toFGL' g (Unary _ nn i sw sh (_, _, _, _, f, l)) =
  let
    g' = toFGL' g  nn
  in
  ([(Label((showVal sw)Prelude.++"x"Prelude.++(showVal sh)), val i g')], noNodes g', l, []) & g'
toFGL' g (Binary _ _ nn i sw sh j sw' sh' (_, _, _, _, _, _, f, l)) =
  let
    g' = toFGL' g  nn
  in
  ([(Label((showVal sw)Prelude.++"x"Prelude.++(showVal sh)), val i g'), (Label((showVal sw')Prelude.++"x"Prelude.++(showVal sh')), val j g')], noNodes g', l, []) & g'

toFGL'' :: DynGraph gr => NeuralNetwork e l w i ps po s o -> gr Label Label
toFGL'' = toFGL' empty

expVal :: Sing (n :: Nat) -> Exp Int
expVal sn = the $ unit $ constant $ fromInteger $ withKnownNat sn $ natVal sn

intVal :: Sing (n :: Nat) -> Int
intVal sn = fromInteger $ withKnownNat sn $ natVal sn

init :: (Elt e, A.Floating e) => Exp e -> Sing (l :: [(Nat, Nat)]) -> PList l e
init _ SNil = pNil
init x (SCons (STuple2 w h) sl) = pCons2 w h (generate (index2 (expVal w) (expVal h)) (\_ -> x)) (NeuralNetwork2.init x sl)

keepParams :: (A.Elt e) => NeuralNetwork (ValueAndDerivative e) l w i ps po s o -> PList l e -> (PList w e, PList ps e, PList po e, PList s e, PList o e)
keepParams (Unity _ _) _ = (pNil, pNil, pNil, pNil, pNil)
keepParams (Weight w h) l = (pAt Head l, pNil, pNil, pNil, pNil)
keepParams (Input _ _) _ = (pNil, pNil, pNil, pNil, pNil)
keepParams (PreviousState w h) l = (pNil, pAt Head l, pNil, pNil, pNil)
keepParams (PreviousOutput w h) l = (pNil, pNil, pAt Head l, pNil, pNil)
keepParams (State _ nn _ w h) l =
  let
    (lh, lt) = pUncons l
    (ww, ps, po, s, o) = keepParams nn lt
  in
    (ww, ps, po, pCons lh s, o)
keepParams (Output _ nn _ w h) l =
  let
    (lh, lt) = pUncons l
    (ww, ps, po, s, o) = keepParams nn lt
  in
    (ww, ps, po, s, pCons lh o)
keepParams (Union nn1 sl1 _ _ _ _ _ _ nn2 sl2 _ _ _ _  _ _) l =
  let
    (l1, l2) = pSplit sl1 sl2 l
    (w1, ps1, po1, s1, o1) = keepParams nn1 l1
    (w2, ps2, po2, s2, o2) = keepParams nn2 l2
  in
    (pJoin w1 w2, pJoin ps1 ps2, pJoin po1 po2, pJoin s1 s2, pJoin o1 o2)
keepParams (Unary _ nn _ _ _ _) l  = keepParams nn $ pTail l
keepParams (Binary _ _ nn _ _ _ _ _ _ _) l = keepParams nn $ pTail l

copyParams :: (A.Num e) => NeuralNetwork (ValueAndDerivative e) l w i ps po s o -> PList w e -> PList s e -> PList o e -> PList l e -> PList l e
copyParams (Unity _ _) ww s o l = l
copyParams (Weight w h) ww s o l = ww
copyParams (Input _ _) ww s o l = l
copyParams (PreviousState w h) ww s o l = l
copyParams (PreviousOutput _ _) ww s o l = l
copyParams (State _ nn _ w h) ww s o l =
  let
    (sh, st) = pUncons s
    (lh, lt) = pUncons l
  in
    pAdd Head (pCons lh $ copyParams nn ww st o lt) sh
copyParams (Output _ nn _ w h) ww s o l =
  let
    (oh, ot) = pUncons o
    (lh, lt) = pUncons l
  in
    pAdd Head (pCons lh $ copyParams nn ww s ot lt) oh
copyParams (Union nn1 sl1 sw1 _ _ _ ss1 so1 nn2 sl2 sw2 _ _ _ ss2 so2) ww s o l =
  let
    (s1, s2) = pSplit ss1 ss2 s
    (o1, o2) = pSplit so1 so2 o
    (w1, w2) = pSplit sw1 sw2 ww
    (l1, l2) = pSplit sl1 sl2 l
  in
    pJoin (copyParams nn1 w1 s1 o1 l1) (copyParams nn2 w2 s2 o2 l2)
copyParams (Unary _ nn _ _ _ _) ww s o l =
  let
    (lh, lt) = pUncons l
  in
    pCons lh $ copyParams nn ww s o lt
copyParams (Binary _ _ nn _ _ _ _ _ _ _) ww s o l =
  let
    (lh, lt) = pUncons l
  in
    pCons lh $ copyParams nn ww s o lt

toSomeSNat :: Int -> SomeSNat
toSomeSNat 0 = SomeSNat (sing :: SNat 0)
toSomeSNat i | i Prelude.> 0 = case toSomeSNat (i-1) of
                 SomeSNat s -> SomeSNat (s %:+ (sing :: SNat 1))
toSomeSNat i | i Prelude.< 0 = case toSomeSNat (i+1) of
                 SomeSNat s -> SomeSNat (s %:- (sing :: SNat 1))

data SomeSNat where
  SomeSNat :: forall n . SNat n -> SomeSNat

evalBackward :: (A.Num e) => Sing l -> NeuralNetwork (ValueAndDerivative e) l w i ps po s o -> PList l e -> PList l e -> PList l e
evalBackward sl (Unity w h) !v !adj = adj
evalBackward sl (Weight w h) !v !adj = adj
evalBackward sl (Input w h) !v !adj = adj
evalBackward sl (PreviousState w h) !v !adj = adj
evalBackward sl (PreviousOutput w h) !v !adj = adj
evalBackward (SCons _ sl) (State p nn i w h) !v !adj =
  let
    (adjh, adjt) = pUncons adj
    adjS' = pAdd p adjt adjh
  in
    pCons adjh $! evalBackward sl nn (pTail v) adjS'
evalBackward (SCons _ sl) (Output p nn i w h) !v !adj =
  let
    (adjh, adjt) = pUncons adj
    adjO' = pAdd p adjt adjh
  in
    pCons adjh $! evalBackward sl nn (pTail v) adjO'
evalBackward sl (Union nn1 sl1 sw1 si1 sps1 spo1 _ ss1 nn2 sl2 sw2 si2 sps2 spo2 _ _) !v !adj =
  let
    (adj1, adj2) = pSplit sl1 sl2 adj
    (v1, v2) = pSplit sl1 sl2 v
    adj1' = id $! evalBackward sl1 nn1 v1 adj1
    adj2' = id $! evalBackward sl2 nn2 v2 adj2
  in
    pJoin adj1' adj2'
evalBackward (SCons _ sl) (Unary p nn i w h ff@(_, _, w', h', f, l)) !v !adj =
  let
    (adjh, adjt) = pUncons adj
    (_, _, a) = pBreak2 adjh
    vt = pTail v
    x = timesJacobian1 f (pAt2 p vt) a
    adjU = pAdd p adjt $ pSingleton2 w h x
  in
    pCons adjh $! evalBackward sl nn vt adjU
evalBackward (SCons _ sl) (Binary p q nn i w h j w' h' ff@(_, _, _, _, w'', h'', f,  l)) !v !adj =
  let
    (adjh, adjt) = pUncons adj
    (_, _, a) = pBreak2 adjh
    vt = pTail v
    (x1, x2) = timesJacobian2 f (pAt2 p vt) (pAt2 q vt) a
    adjB = pAdd p (pAdd q adjt $ pSingleton2 w' h' x2) $ pSingleton2 w h x1
  in
    pCons adjh $! evalBackward sl nn vt adjB

pSize :: Sing (l :: [(Nat, Nat)]) -> Int
pSize sl =
  let
    l = fromSing sl
  in
    Prelude.fromInteger $ Prelude.foldl (\r (a,b) -> r+a*b) 0 l

pExtend :: (A.Floating e) => Sing l -> AtIndex l '(1, os) 0 -> PList ('(1, os) ': '[]) e -> PList l e
pExtend sl p e =
  let
    pl = NeuralNetwork2.init 0 sl
  in
    pAdd p pl e

evalBackwardL :: forall e l os w i s o . (A.Floating e) => Sing l -> SNat os -> AtIndex l '(1, os) 0 -> NeuralNetwork (ValueAndDerivative e) l w i s o s o -> [PList l e] -> [PList ('(1, os) ': '[]) e] -> PList l e
evalBackwardL sl sos p nn i a = pUnflatten sl $ A.use $ foldr (\a b -> B.run1 (trace "backward" . step) (b, a)) z args
  where sa = SCons (STuple2 (sing :: SNat 1) sos) SNil
        z = B.run $ pFlatten $ NeuralNetwork2.init 0 sl
        args = Prelude.zip (Prelude.map (B.run . pFlatten) i) (Prelude.map (B.run . pFlatten) a)
        step x =
          let
            (adjj, y) = unlift x :: (Acc (Vector e), Acc (Vector e, Vector e))
            (ii', aa') = unlift y
            adj = pUnflatten sl adjj
            ii = pUnflatten sl ii'
            aa = pUnflatten sa aa'
            adj' = pExtend sl p aa
            (pw, ps, po, _, _) = keepParams nn adj
            adj'' = copyParams nn pw ps po adj'
            r = pFlatten $ evalBackward sl nn ii adj''
          in
            r

evalForwardL :: forall e l s o i w . (A.Num e) => Sing l -> Sing s -> Sing o -> Sing i -> NeuralNetwork (ValueAndDerivative e) l w i s o s o -> PList w e -> [PList i e] -> PList s e -> PList o e -> [PList l e]
evalForwardL sl sngs sngo sngi nn w i s o = Prelude.fst $ foldl' step ([], (B.run $ pFlatten s, B.run $ pFlatten o)) (Prelude.map (B.run . pFlatten) i)
  where step (r, (s, o)) i =
          let
            (r', s', o') = B.run1 (trace "forward" . step') (s, o, i)
          in
            ((pUnflatten sl $ A.use r') : r, (s', o'))
        step' x =          
          let
            (s, o, i) = unlift x
            ps = pUnflatten sngs s
            po = pUnflatten sngo o
            pi = pUnflatten sngi i
            r = evalForward sl nn w pi ps po
            (_, _, _, s', o') = keepParams nn r
          in
            lift (pFlatten r, pFlatten s', pFlatten o')

evalForward :: (A.Num e) => Sing l -> NeuralNetwork (ValueAndDerivative e) l w i ps po s o -> PList w e -> PList i e -> PList ps e -> PList po e -> PList l e
evalForward sl (Unity w h) _ _ _ _ = pSingleton2 w h (generate (index2 (expVal w) (expVal h)) (\_ -> 1))
evalForward sl (Weight w h) ww _ _ _ = ww
evalForward sl (Input w h) _ ii _ _ = ii
evalForward sl (PreviousState w h) _ _ ps _ = ps
evalForward sl (PreviousOutput w h) _ _ _ po = po
evalForward (SCons _ sl) (State p nn i w h) ww ii ps po =
  let
    t = evalForward sl nn ww ii ps po
  in
    pCons (pAt p t) t
evalForward (SCons _ sl) (Output p nn i w h) ww ii ps po =
  let
    t = evalForward sl nn ww ii ps po
  in
    pCons (pAt p t) t
evalForward sl (Union nn1 sl1 sw1 si1 sps1 spo1 _ _ nn2 sl2 sw2 si2 sps2 spo2 _ _) ww ii ps po =
  let
    (ww1, ww2) = pSplit sw1 sw2 ww
    (ii1, ii2) = pSplit si1 si2 ii
    (ps1, ps2) = pSplit sps1 sps2 ps 
    (po1, po2) = pSplit spo1 spo2 po
    t1 = evalForward sl1 nn1 ww1 ii1 ps1 po1
    t2 = evalForward sl2 nn2 ww2 ii2 ps2 po2
  in
    pJoin t1 t2
evalForward (SCons _ sl) (Unary p nn i w h ff@(_, _, w', h', f, l)) ww ii ps po =
  let
    t = evalForward sl nn ww ii ps po
    d = pAt2 p t
    v = unsingleton $ A.map (lift1 value) $ f $ A.map (lift1 fromValue) $ singleton d
  in
    pCons2 w' h' v t
evalForward (SCons _ sl) (Binary p q nn i w h j w' h' ff@(_, _, _, _, w'', h'', f,  l)) ww ii ps po =
  let
    t = evalForward sl nn ww ii ps po
    d1 = pAt2 p t
    d2 = pAt2 q t
    v = unsingleton $ A.map (lift1 value) $ f (A.map (lift1 fromValue) $ singleton d1) (A.map (lift1 fromValue) $ singleton d2)
  in
    pCons2 w'' h'' v t

data SomeNeuralNetwork e is os where
  SomeNeuralNetwork :: forall e l w i s o is os . (A.Floating e) => AtIndex l '(1, is) (Length l :- 1) -> AtIndex l '(1, os) 0 -> Sing l -> Sing w -> Sing i -> Sing s -> Sing o -> NeuralNetwork (ValueAndDerivative e) l w i s o s o -> SomeNeuralNetwork e is os

gradientParams :: (Exp e) -> (Exp e) -> Sing is -> Sing os -> SomeNeuralNetwork e is os -> [Acc (Vector e)]
gradientParams x y sis sos nn =
  case nn of
    SomeNeuralNetwork q1 q2 _ sw si ss so nn' ->
      let
        sp = (sw %:++ ss %:++ so)
        dp = fromSing sp
        np = Prelude.map (index1 . the . unit. constant) ([0..(fromInteger (foldl (\r (a, b) -> (r + a*b)) 0 dp)-1)] :: [Int])
        p = pFlatten $ NeuralNetwork2.init x sp
        mp = Prelude.map (\i -> A.imap (\j v -> cond (unindex1 j A.== unindex1 i) y v) p) np
      in
        mp
        
forwardParams :: (Exp e) -> Sing is -> Sing os -> SomeNeuralNetwork e is os -> Acc (Vector e)
forwardParams x sis sos nn =
  case nn of
    SomeNeuralNetwork q1 q2 sl sw si ss so nn' ->
      let
        pw = NeuralNetwork2.init x sw
        ps = NeuralNetwork2.init x ss
        po = NeuralNetwork2.init x so
        r = pFlatten $ pJoin pw (pJoin ps po)
      in
        r

gradient2 :: forall e is os . (Prelude.Floating e, A.Floating e, Lift Exp e, e ~ Plain e) => Sing is -> Sing os -> SomeNeuralNetwork e is os -> ([Acc (Array DIM4 (ValueAndDerivative e))] -> Acc (Matrix (ValueAndDerivative e))) -> [Acc (Vector e)] -> Acc (Vector e) -> Acc (Vector e)
gradient2 sis sos nn f i p =
  case nn of
    SomeNeuralNetwork q1 q2 sl sw si ss so nn' ->
      let
        s1 = sing :: SNat 1
        pl = pUnflatten (sw %:++ ss %:++ so) p
        pi = Prelude.map (pUnflatten si) i
        (pw, pso) = pSplit sw (ss %:++ so) pl
        (ps, po) = pSplit ss so pso
        v = evalForwardL sl ss so si nn' pw pi ps po
        err = A.map value $ A.reshape (lift $ Z) $ f $ Prelude.map (singleton . A.map fromValue . pAt2 q2) v
        adj = Prelude.map (pSingleton2 s1 sos) $ timesJacobianL' (singleton' . f) (Prelude.map (pAt2 q2) v) $ A.reshape (index2 1 1) $ err
        g = evalBackwardL sl sos q2 nn' v adj
        (w', ps', po', _, _) = keepParams nn' g
        rw = pFlatten $ w'
        rs = pFlatten $ ps'
        ro = pFlatten $ po'
      in
        rw A.++ rs A.++ ro

gradient :: forall e is os . (Prelude.Floating e, A.Floating e, Lift Exp e, e ~ Plain e) => Sing is -> Sing os -> SomeNeuralNetwork (ValueAndDerivative e) is os -> ([PList ('(1, os) ': '[]) (ValueAndDerivative e)] -> Acc (Scalar (ValueAndDerivative e))) -> [Acc (Vector e)] -> Acc (Vector e)
gradient sis sos nn f i =
  let
    g = gradient' sis sos nn f (Prelude.map (A.map (lift1 fromValue)) i)
  in
    A.map (lift1 derivative) g

gradient' :: forall e is os . (Prelude.Floating e, A.Elt e, Lift Exp e, e ~ Plain e) => Sing is -> Sing os -> SomeNeuralNetwork (ValueAndDerivative e) is os -> ([PList ('(1, os) ': '[]) (ValueAndDerivative e)] -> Acc (Scalar (ValueAndDerivative e))) -> [Acc (Vector (ValueAndDerivative e))] -> Acc (Vector (ValueAndDerivative e))
gradient' sis sos nn f i =
  let
    gp = gradientParams (lift $ ValueAndDerivative (0.5 :: e) (0 :: e)) (lift $ ValueAndDerivative (0.5 :: e) (1 :: e)) sis sos nn
    rs = Prelude.map (\p -> forward sis sos nn f p i) gp :: [Acc (Scalar (ValueAndDerivative e))]
    ds = Prelude.map (reshape (index1 1)) rs
  in
    foldl (A.++) (A.use $ A.fromList (Z:.0) []) ds

forward :: Sing is -> Sing os -> SomeNeuralNetwork e is os -> ([PList ('(1, os) ': '[]) e] -> Acc (Scalar e)) -> Acc (Vector e) -> [Acc (Vector e)] -> Acc (Scalar e)
forward sis sos nn f p i =
  case nn of
    SomeNeuralNetwork q1 q2 sl sw si ss so nn' ->
      let
        pl = pUnflatten (sw %:++ ss %:++ so) p
        pi = Prelude.map (pUnflatten si) i
        (pw, pso) = pSplit sw (ss %:++ so) pl
        (ps, po) = pSplit ss so pso
        r = evalForwardL sl ss so si nn' pw pi ps po
      in
        f $ Prelude.map (\rr -> pSingleton2 (sing ::SNat 1) sos (pAt2 q2 rr)) r

forward' :: Sing is -> Sing os -> SomeNeuralNetwork e is os -> Acc (Vector e) -> [Acc (Vector e)] -> [Acc (Matrix e)]
forward' sis sos nn p i =
  case nn of
    SomeNeuralNetwork q1 q2 sl sw si ss so nn' ->
      let
        pl = pUnflatten (sw %:++ ss %:++ so) p
        pi = Prelude.map (pUnflatten si) i
        (pw, pso) = pSplit sw (ss %:++ so) pl
        (ps, po) = pSplit ss so pso
        r = evalForwardL sl ss so si nn' pw pi ps po        
      in
        Prelude.map (pAt2 q2) r

toFGL :: DynGraph gr => SomeNeuralNetwork e i o -> gr Label Label
toFGL nn = case nn of
  SomeNeuralNetwork _ _ _ _ _ _ _ nn' -> toFGL'' nn'

addLayer :: (Elt e) => SNat i -> SNat o -> SNat o' -> SomeNeuralNetwork e i o -> SomeNeuralNetwork e i o'
addLayer sis sos sos' nn =
  let
    s0 = sing :: SNat 0
    s1 = sing :: SNat 1
  in
    case nn of
      SomeNeuralNetwork spi spo sl sw si ss so nn' ->
        let
          (nn'', sl', sw', si', ss', so', _, _) = addLSTMLayer spo sl sw si ss so ss so sos sos' s0 nn'
        in
          SomeNeuralNetwork $(tailN 30 [e|spi|]) Head sl' sw' si' ss' so' nn''

addLayers :: (Elt e) => SNat i -> SNat o -> Sing ((o' ': l) :: [Nat]) -> SomeNeuralNetwork e i o -> SomeNeuralNetwork e i o'
addLayers si so (SCons so' SNil) nn = addLayer si so so' nn
addLayers si so (SCons sx (SCons sy sl)) nn = addLayer si sy sx $ addLayers si so (SCons sy sl) nn

makeNetwork :: (A.Floating e, Elt e) => SNat i -> Sing (l :: [Nat]) -> SNat o -> SomeNeuralNetwork e i o
makeNetwork si sl so =
  let
    s1 = sing :: SNat 1
    nn = SomeNeuralNetwork Head Head (SCons (STuple2 s1 si) SNil) SNil (SCons (STuple2 s1 si) SNil) SNil SNil $ Input s1 si
  in
    addLayers si si (SCons so (sReverse sl)) nn

initParams :: (Prelude.Floating e, A.Floating e, Lift Exp e, e ~ Plain e) => e -> SomeNeuralNetwork e is os -> Vector e
initParams x nn =
  case nn of
    SomeNeuralNetwork q1 q2 sl sw si ss so nn' ->
        B.run $ pFlatten $ NeuralNetwork2.init (the $ unit $ constant x) (sw %:++ ss %:++ so)

infList :: (a -> a) -> a -> [a]
infList f i = i:(infList f (f i))

gradientDescent :: forall e is os . (Prelude.Floating e, A.Floating e, Lift Exp e, e ~ Plain e) => e -> Sing is -> Sing os -> SomeNeuralNetwork e is os -> ([Acc (Array DIM4 (ValueAndDerivative e))] -> Acc (Matrix (ValueAndDerivative e))) -> [Acc (Vector e)] -> Vector e -> [(Vector e)]
gradientDescent eta sis sos nn f i p = infList (\a -> trace "gradient" $ B.run $ step $ A.use a) p
  where
    updateParam :: Exp e -> Exp e -> Exp e -> Exp e
    updateParam eta p g = p - eta * g
    step :: Acc (Vector e) -> Acc (Vector e)
    step p =
      let
        g = gradient2 sis sos nn f i p
        p' = A.zipWith (updateParam (the $ unit $ constant $ eta)) p g
      in
        p'
