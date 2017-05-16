{-# LANGUAGE DataKinds, KindSignatures, TypeOperators, GADTs, TemplateHaskell, TypeFamilies, UndecidableInstances, Rank2Types, AllowAmbiguousTypes, ScopedTypeVariables, MultiParamTypeClasses, FlexibleInstances, FlexibleContexts, PolyKinds #-}
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

safeZipWith1 :: (Elt a, Elt b, Elt c) => (Exp a -> Exp b -> Exp c) -> Acc (Vector a) -> Acc (Vector b) -> Acc (Vector c)
safeZipWith1 = A.zipWith

safeZipWith2 :: (Elt a, Elt b, Elt c) => (Exp a -> Exp b -> Exp c) -> Acc (Matrix a) -> Acc (Matrix b) -> Acc (Matrix c)
safeZipWith2 = A.zipWith

safeZipWith3 :: (Elt a, Elt b, Elt c) => (Exp a -> Exp b -> Exp c) -> Acc (Array DIM3 a) -> Acc (Array DIM3 b) -> Acc (Array DIM3 c)
safeZipWith3 = A.zipWith
{-
safeZipWith1 :: (Elt a, Elt b, Elt c) => (Exp a -> Exp b -> Exp c) -> Acc (Vector a) -> Acc (Vector b) -> Acc (Vector c)
safeZipWith1 f a b =
  let
    x = I.run $ unit $ unindex1 $ shape a
    y = I.run $ unit $ unindex1 $ shape b
  in
    if (x Prelude.== y) then (A.zipWith f a b) else error $ "invalid bounds: " Prelude.++ (show $ I.run $ unit $ shape a) Prelude.++ ", " Prelude.++ (show $ I.run $ unit $ shape b)

safeZipWith2 :: (Elt a, Elt b, Elt c) => (Exp a -> Exp b -> Exp c) -> Acc (Matrix a) -> Acc (Matrix b) -> Acc (Matrix c)
safeZipWith2 f a b =
  let
    x = I.run $ unit $ unindex2 $ shape a
    y = I.run $ unit $ unindex2 $ shape b
  in
    if (x Prelude.== y) then (A.zipWith f a b) else error $ "invalid bounds: " Prelude.++ (show $ I.run $ unit $ shape a) Prelude.++ ", " Prelude.++ (show $ I.run $ unit $ shape b)

safeZipWith3 :: (Elt a, Elt b, Elt c) => (Exp a -> Exp b -> Exp c) -> Acc (Array DIM3 a) -> Acc (Array DIM3 b) -> Acc (Array DIM3 c)
safeZipWith3 f a b =
  let
    x = I.run $ unit $ unindex3 $ shape a
    y = I.run $ unit $ unindex3 $ shape b
  in
    if (x Prelude.== y) then (A.zipWith f a b) else error $ "invalid bounds: " Prelude.++ (show $ I.run $ unit $ shape a) Prelude.++ ", " Prelude.++ (show $ I.run $ unit $ shape b)
-}
data AtIndexNat (l :: [Nat]) (e :: Nat) (i :: Nat) where
  HeadNat :: AtIndexNat (x ': xs) x 0
  TailNat :: AtIndexNat t x i -> AtIndexNat (h ': t) x (i + 1)

data AtIndex (l :: [(Nat, Nat)]) (e :: (Nat, Nat)) (i :: Nat) where
  Head :: AtIndex ('(w, h) ': xs) '(w, h) 0
  Tail :: AtIndex t x i -> AtIndex (h ': t) x (i + 1)

type Matrix e = Array DIM2 e

data PList (l :: [(Nat, Nat)]) e where
  PList :: Sing l -> Acc (Vector e) -> PList l e

pNil :: (A.Elt e) => PList '[] e
pNil = PList SNil $ A.use $ fromList (Z:.0) []

pCons'' :: (A.Elt e) => PList ('(w, h) ': '[]) e -> PList l e -> PList ('(w, h) ': l) e
pCons'' (PList (SCons (STuple2 sw sh) SNil) a) (PList sl b) = PList (SCons (STuple2 sw sh) sl) (a A.++ b)

pCons :: (A.Elt e) => SNat w -> SNat h -> Acc (Matrix e) -> PList l e -> PList ('(w, h) ': l) e
pCons sw sh a (PList sl b) = PList (SCons (STuple2 sw sh) sl) ((A.flatten a) A.++ b)

pCons' :: (A.Elt e) => SNat w -> SNat h -> Acc (Vector e) -> PList l e -> PList ('(w, h) ': l) e
pCons' sw sh a (PList sl b) = PList (SCons (STuple2 sw sh) sl) (a A.++ b)

pUncons :: (A.Elt e) => PList ('(w, h) ': l) e -> (PList ('(w, h) ': '[]) e, PList l e)
pUncons (PList (SCons (STuple2 sw sh) sl) a) =
  let
    w = expVal sw
    h = expVal sh
    n = w A.* h
    hd = A.take n a
    tl = A.drop n a
  in
    (PList (SCons (STuple2 sw sh) SNil) hd, PList sl tl)

pUncons' :: (A.Elt e) => PList ('(w, h) ': l) e -> ((SNat w, SNat h, Acc (Vector e)), PList l e)
pUncons' pl =
  let
    (ph, pt) = pUncons pl
  in
    (pBreak' ph, pt)

pHead :: (A.Elt e) => PList ('(w, h) ': l) e -> PList ('(w, h) ': '[]) e
pHead = Prelude.fst . pUncons

pTail :: (A.Elt e) => PList ('(w, h) ': l) e -> PList l e
pTail = Prelude.snd . pUncons

pSingleton' :: (A.Elt e) => SNat w -> SNat h -> Acc (Vector e) -> PList ('(w, h) ': '[]) e
pSingleton' sw sh a = pCons' sw sh a pNil

pSingleton :: (A.Elt e) => SNat w -> SNat h -> Acc (Matrix e) -> PList ('(w, h) ': '[]) e
pSingleton sw sh a = pCons sw sh a pNil

pBreak' :: (A.Elt e) => PList ('(w, h) ': '[]) e -> (SNat w, SNat h, Acc (Vector e))
pBreak' (PList (SCons (STuple2 sw sh) SNil) a) = (sw, sh, a)

pBreak :: (A.Elt e) => PList ('(w, h) ': '[]) e -> (SNat w, SNat h, Acc (Matrix e))
pBreak ps =
  let
    (sw, sh, a) = pBreak' ps
  in
    (sw, sh, A.reshape (index2 (expVal sw) (expVal sh)) a)

pAdd :: (A.Num e) => AtIndex l '(w, h) i -> PList l e -> PList ('(w, h) ': '[]) e -> PList l e
pAdd Head pl ps =
  let
    (sw, sh, b) = pBreak' ps
    ((_, _, a), pt) = pUncons' pl
  in
    pCons' sw sh (safeZipWith1 (A.+) a b) pt
pAdd (Tail p) pl@(PList (SCons (STuple2 sw sh) _) _) ps =
  let
    (ph, pt) = pUncons pl
  in
    pCons'' ph (pAdd p pt ps)

pAt' :: (A.Elt e) => AtIndex l '(w, h) i -> PList l e -> Acc (Vector e)
pAt' Head pl@(PList (SCons (STuple2 sw sh) _) _) =
  let
    ph = pHead pl
    (_, _, a) = pBreak' ph
  in
    a
pAt' (Tail p) pl@(PList (SCons (STuple2 sw sh) _) _) = pAt' p (pTail pl)

pAt :: (A.Elt e) => AtIndex l '(w, h) i -> PList l e -> Acc (Matrix e)
pAt Head pl@(PList (SCons _ _) _) =
  let
    ph = pHead pl
    (_, _, a) = pBreak ph
  in
    a
pAt (Tail p) pl@(PList (SCons (STuple2 sw sh) _) _) = pAt p (pTail pl)

pSplit :: (Elt e) => Sing l -> Sing l' -> PList (l :++ l') e -> (PList l e, PList l' e)
pSplit SNil sl' pl = (pNil, pl)
pSplit (SCons (STuple2 sw sh) sl) sl' pl =
  let
    (ph, pt) = pUncons pl
    (p1, p2) = pSplit sl sl' pt
  in
    (pCons'' ph p1, p2)

pJoin :: (Elt e) => PList l e -> PList l' e -> PList (l :++ l') e
pJoin (PList SNil _) pl' = pl'
pJoin pl@(PList (SCons (STuple2 sw sh) _) _) pl' =
  let
    (ph, pt) = pUncons pl
  in
    pCons'' ph (pJoin pt pl')

newtype Label = Label String
instance Show Label where
  show (Label s) = s

type UnaryFunction e (w :: Nat) (h :: Nat) (w' :: Nat) (h' :: Nat) = (Elt e) => (SNat w, SNat h, SNat w', SNat h', Acc (Matrix e) -> Acc (Matrix e), Label)
type BinaryFunction e (w :: Nat) (h :: Nat) (w' :: Nat) (h' :: Nat) (w'' :: Nat) (h'' :: Nat) = (Elt e) => (SNat w, SNat h, SNat w', SNat h', SNat w'', SNat h'', Acc (Matrix e) -> Acc (Matrix e) -> Acc (Matrix e), Label)

jacobian1 :: (A.Num a) => UnaryFunction (ValueAndDerivative a) w h w' h' -> PList ('(w, h) ': '[]) a -> [[Acc (Matrix a)]]
jacobian1 f@(sw, sh, _, _, _, _) v =
  let
    r = Prelude.map (\j -> Prelude.map (\i -> jacobian1' (unit $ constant i) (unit $ constant j) f v) [0..(fromInteger $ fromSing sw)-1]) [0..(fromInteger $ fromSing sh)-1]
  in
    r

jacobian1' :: (A.Num a) => Acc (Scalar Int) -> Acc (Scalar Int) -> UnaryFunction (ValueAndDerivative a) w h w' h' -> PList ('(w, h) ': '[]) a -> Acc (Matrix a)
jacobian1' k l (sw, sh, sw', sh', f, _) pl = 
  let
    (_, _, a) = pBreak pl
    i = index2 (the k) (the l)
    a' = A.map (lift1 fromValue) a
    a'' = A.imap (\j v -> cond (unindex2 j A.== unindex2 i) (lift $ ValueAndDerivative (value v) 1) v) a'
  in
    A.map (lift1 derivative) (f a'')

jacobianl :: (A.Num a) => SNat w -> ([PList ('(1, w) ': '[]) (ValueAndDerivative a)] -> Acc (Scalar (ValueAndDerivative a))) -> [PList ('(1, w) ': '[]) a] -> [Acc (Matrix a)]
jacobianl sw f v =
  let
    r = Prelude.map (\j -> Prelude.foldl (A.++) (A.use $ fromList (Z:.1:.0) []) $ Prelude.map (\i -> A.reshape (index2 1 (expVal sw)) $ jacobianl' sw (unit $ constant i) j f v) [0..(fromInteger $ fromSing sw)-1]) [0..(Prelude.length v)-1]
  in
    r

jacobianl' :: (A.Num a) => SNat w -> Acc (Scalar Int) -> Int -> ([PList ('(1, w) ': '[]) (ValueAndDerivative a)] -> Acc (Scalar (ValueAndDerivative a))) -> [PList ('(1, w) ': '[]) a] -> Acc (Scalar a)
jacobianl' sw k l f vv = 
  let
    s1 = sing :: SNat 1
    i = index2 0 (the k)
    vv' = Prelude.map (\pl -> let (_, _, a) = pBreak pl in A.map (lift1 fromValue) a) vv
    a'' = Prelude.map (\m -> if m Prelude./= l then pSingleton s1 sw (vv' Prelude.!! m) else pSingleton s1 sw $ A.imap (\j v -> cond (unindex2 j A.== unindex2 i) (lift $ ValueAndDerivative (value v) 1) v) (vv' Prelude.!! m)) [0..((Prelude.length vv)-1)]
  in
    A.map (lift1 derivative) (f a'')

jacobian2 :: (A.Num a) => BinaryFunction (ValueAndDerivative a) w h w' h' w'' h'' -> PList ('(w, h) ': '[]) a -> PList ('(w', h') ': '[]) a -> ([[Acc (Matrix a)]], [[Acc (Matrix a)]])
jacobian2 f@(sw, sh, sw', sh', _, _, _, _) v1 v2 =
  let
    r1 = Prelude.map (\j -> Prelude.map (\i -> jacobian2l' (unit $ constant i) (unit $ constant j) f v1 v2) [0..(fromInteger $ fromSing sw)-1]) [0..(fromInteger $ fromSing sh)-1]
    r2 = Prelude.map (\j -> Prelude.map (\i -> jacobian2r' (unit $ constant i) (unit $ constant j) f v1 v2) [0..(fromInteger $ fromSing sw')-1]) [0..(fromInteger $ fromSing sh')-1]    
  in
    (r1, r2)

jacobian2l' :: (A.Num a) => Acc (Scalar Int) -> Acc (Scalar Int) -> BinaryFunction (ValueAndDerivative a) w h w' h' w'' h'' -> PList ('(w, h) ': '[]) a -> PList ('(w', h') ': '[]) a -> Acc (Matrix a)
jacobian2l' k l (sw, sh, sw', sh', sw'', sh'', f, _) pa pb = 
  let
    (_, _, a) = pBreak pa
    (_, _, b) = pBreak pb
    i = index2 (the k) (the l)
    a' = A.map (lift1 fromValue) a
    b' = A.map (lift1 fromValue) b
    a'' = A.imap (\j v -> cond (unindex2 j A.== unindex2 i) (lift $ ValueAndDerivative (value v) 1) v) a'
  in
    A.map (lift1 derivative) (f a'' b')

jacobian2r' :: (A.Num a) => Acc (Scalar Int) -> Acc (Scalar Int) -> BinaryFunction (ValueAndDerivative a) w h w' h' w'' h'' -> PList ('(w, h) ': '[]) a -> PList ('(w', h') ': '[]) a -> Acc (Matrix a)
jacobian2r' k l (sw, sh, sw', sh', sw'', sh'', f, _) pa pb = 
  let
    (_, _, a) = pBreak pa
    (_, _, b) = pBreak pb
    i = index2 (the k) (the l)
    a' = A.map (lift1 fromValue) a
    b' = A.map (lift1 fromValue) b
    b'' = A.imap (\j v -> cond (unindex2 j A.== unindex2 i) (lift $ ValueAndDerivative (value v) 1) v) b'
  in
    A.map (lift1 derivative) (f a' b'')

tnh :: (A.Floating a, Elt a) => Exp a -> Exp a
tnh x = ((exp x) - (exp (-x))) / ((exp x) + (exp (-x)))

tanh ::(A.Floating a) => SNat w -> SNat h -> UnaryFunction a w h w h
tanh sw sh = (sw, sh, sw, sh, A.map tnh, Label "tanh")

sgm :: (A.Floating a, Elt a) => Exp a -> Exp a
sgm x = 1 / (1 + exp (-x))

sigm ::(A.Floating a) => SNat w -> SNat h -> UnaryFunction a w h w h
sigm sw sh = (sw, sh, sw, sh, A.map sgm, Label "sigm")

esum :: (A.Num e) => SNat w -> SNat h -> BinaryFunction e w h w h w h
esum sw sh = (sw, sh, sw, sh, sw, sh, safeZipWith2 (+), Label ".+")

eprod :: (A.Num e) => SNat w -> SNat h -> BinaryFunction e w h w h w h
eprod sw sh = (sw, sh, sw, sh, sw, sh, safeZipWith2 (*), Label ".*")

prd :: (A.Num e, Elt e) => Acc (Matrix e) -> Acc (Matrix e) -> Acc (Matrix e)
prd a b = A.fold (+) 0 $ safeZipWith3 (*) aRepl bRepl
  where
    Z :. rowsA :.     _ = unlift (shape a)    :: Z :. Exp Int :. Exp Int
    Z :.     _ :. colsB = unlift (shape b)    :: Z :. Exp Int :. Exp Int
    aRepl = A.replicate (lift $ Z :. All   :. colsB :. All) a
    bRepl = A.replicate (lift $ Z :. rowsA :. All   :. All) (A.transpose b)

prod :: (A.Num e, Elt e) => SNat a -> SNat b -> SNat c -> BinaryFunction e a b b c a c
prod sa sb sc = (sa, sb, sb, sc, sa, sc, prd, Label "*")

concat :: forall e a b c . SNat a -> SNat b -> SNat c -> BinaryFunction e a b a c a (b+c)
concat sa sb sc = (sa, sb, sa, sc, sa, sb %:+ sc, (A.++), Label "++")

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
init x (SCons (STuple2 w h) sl) = pCons w h (generate (index2 (expVal w) (expVal h)) (\_ -> x)) (NeuralNetwork2.init x sl)

keepParams :: (A.Elt e) => NeuralNetwork (ValueAndDerivative e) l w i ps po s o -> PList l e -> (PList w e, PList ps e, PList po e, PList s e, PList o e)
keepParams (Unity _ _) _ = (pNil, pNil, pNil, pNil, pNil)
keepParams (Weight w h) l = (pSingleton w h (pAt Head l), pNil, pNil, pNil, pNil)
keepParams (Input _ _) _ = (pNil, pNil, pNil, pNil, pNil)
keepParams (PreviousState w h) l = (pNil, pSingleton w h (pAt Head l), pNil, pNil, pNil)
keepParams (PreviousOutput w h) l = (pNil, pNil, pSingleton w h (pAt Head l), pNil, pNil)
keepParams (State _ nn _ w h) l =
  let
    (lh, lt) = pUncons l
    (w, h, a) = pBreak' lh
    (ww, ps, po, s, o) = keepParams nn lt
  in
    (ww, ps, po, pCons' w h a s, o)
keepParams (Output _ nn _ w h) l =
  let
    (lh, lt) = pUncons l
    (w, h, a) = pBreak' lh
    (ww, ps, po, s, o) = keepParams nn lt
  in
    (ww, ps, po, s, pCons' w h a o)
keepParams (Union nn1 sl1 _ _ _ _ _ _ nn2 sl2 _ _ _ _  _ _) l =
  let
    (l1, l2) = pSplit sl1 sl2 l
    (w1, ps1, po1, s1, o1) = keepParams nn1 l1
    (w2, ps2, po2, s2, o2) = keepParams nn2 l2
  in
    (pJoin w1 w2, pJoin ps1 ps2, pJoin po1 po2, pJoin s1 s2, pJoin o1 o2)
keepParams (Unary _ nn _ _ _ _) l  = keepParams nn $ pTail l
keepParams (Binary _ _ nn _ _ _ _ _ _ _) l = keepParams nn $ pTail l

copyParams :: (A.Num e) => NeuralNetwork (ValueAndDerivative e) l w i ps po s o -> PList s e -> PList o e -> PList l e -> PList l e
copyParams (Unity _ _) s o l = l
copyParams (Weight _ _) s o l = l
copyParams (Input _ _) s o l = l
copyParams (PreviousState _ _) s o l = l
copyParams (PreviousOutput _ _) s o l = l
copyParams (State _ nn _ w h) s o l =
  let
    (sh, st) = pUncons s
    (lh, lt) = pUncons l
    (_, _, as) = pBreak' sh
    (_, _, al) = pBreak' lh
  in
    pAdd Head (pCons' w h al $ copyParams nn st o lt) (pSingleton' w h as)
copyParams (Output _ nn _ w h) s o l =
  let
    (oh, ot) = pUncons o
    (lh, lt) = pUncons l
    (_, _, ao) = pBreak' oh
    (_, _, al) = pBreak' lh
  in
    pAdd Head (pCons' w h al $ copyParams nn s ot lt) (pSingleton' w h ao)
copyParams (Union nn1 sl1 _ _ _ _ ss1 so1 nn2 sl2 _ _ _ _ ss2 so2) s o l =
  let
    (s1, s2) = pSplit ss1 ss2 s
    (o1, o2) = pSplit so1 so2 o
    (l1, l2) = pSplit sl1 sl2 l
  in
    pJoin (copyParams nn1 s1 o1 l1) (copyParams nn2 s2 o2 l2)
copyParams (Unary _ nn _ _ _ _) s o l =
  let
    (lh, lt) = pUncons l
    (w, h, al) = pBreak' lh
  in
    pCons' w h al $ copyParams nn s o lt
copyParams (Binary _ _ nn _ _ _ _ _ _ _) s o l =
  let
    (lh, lt) = pUncons l
    (w, h, al) = pBreak' lh
  in
    pCons' w h al $ copyParams nn s o lt

toSomeSNat :: Int -> SomeSNat
toSomeSNat 0 = SomeSNat (sing :: SNat 0)
toSomeSNat i | i Prelude.> 0 = case toSomeSNat (i-1) of
                 SomeSNat s -> SomeSNat (s %:+ (sing :: SNat 1))
toSomeSNat i | i Prelude.< 0 = case toSomeSNat (i+1) of
                 SomeSNat s -> SomeSNat (s %:- (sing :: SNat 1))

data SomeSNat where
  SomeSNat :: forall n . SNat n -> SomeSNat

evalBackward :: (A.Num e) => Sing l -> NeuralNetwork (ValueAndDerivative e) l w i ps po s o -> PList l e -> PList l e -> PList l e
evalBackward sl (Unity w h) v adj = adj
evalBackward sl (Weight w h) v adj = adj
evalBackward sl (Input w h) v adj = adj
evalBackward sl (PreviousState w h) v adj = adj
evalBackward sl (PreviousOutput w h) v adj = adj
evalBackward (SCons _ sl) (State p nn i w h) v adj =
  let
    (adjh, adjt) = pUncons adj
    adjS' = pAdd p adjt adjh
  in
    pCons'' adjh $ evalBackward sl nn (pTail v) adjS'
evalBackward (SCons _ sl) (Output p nn i w h) v adj =
  let
    (adjh, adjt) = pUncons adj
    adjO' = pAdd p adjt adjh
  in
    pCons'' adjh $ evalBackward sl nn (pTail v) adjO'
evalBackward sl (Union nn1 sl1 sw1 si1 sps1 spo1 _ ss1 nn2 sl2 sw2 si2 sps2 spo2 _ _) v adj =
  let
    (adj1, adj2) = pSplit sl1 sl2 adj
    (v1, v2) = pSplit sl1 sl2 v
    adj1' = evalBackward sl1 nn1 v1 adj1
    adj2' = evalBackward sl2 nn2 v2 adj2
  in
    pJoin adj1' adj2'
evalBackward (SCons _ sl) (Unary p nn i w h ff@(_, _, w', h', f, l)) v adj =
  let
    (adjh, adjt) = pUncons adj
    (_, _, a) = pBreak adjh
    vt = pTail v
    j = jacobian1 ff (pSingleton w h $ pAt p vt)
    x' = Prelude.map (Prelude.map (A.reshape (index2 1 1) . A.sum . safeZipWith2 (A.*) a)) j
    x = Prelude.foldl (A.++) (A.use $ A.fromList (Z:.(fromInteger $ fromSing w):.0) []) $ Prelude.map (A.transpose . Prelude.foldl (A.++) (A.use $ A.fromList (Z:.1:.0) [])) x'
    adjU' = pAdd p adjt $ pSingleton w h x
  in
    pCons w' h' a $ evalBackward sl nn vt adjU'
evalBackward (SCons _ sl) (Binary p q nn i w h j w' h' ff@(_, _, _, _, w'', h'', f,  l)) v adj =
  let
    (adjh, adjt) = pUncons adj
    (_, _, a) = pBreak adjh
    vt = pTail v
    (j1, j2) = jacobian2 ff (pSingleton w h $ pAt p vt) (pSingleton w' h' $ pAt q vt)
    x1' = Prelude.map (Prelude.map (A.reshape (index2 (1 :: Exp Int) (1 :: Exp Int)) . A.sum . safeZipWith2 (A.*) a)) j1
    x2' = Prelude.map (Prelude.map (A.reshape (index2 (1 :: Exp Int) (1 :: Exp Int)) . A.sum . safeZipWith2 (A.*) a)) j2
    x1 = Prelude.foldl (A.++) (A.use $ A.fromList (Z:.(fromInteger $ fromSing w):.0) []) $ Prelude.map (A.transpose . Prelude.foldl (A.++) (A.use $ A.fromList (Z:.1:.0) [])) x1'
    x2 = Prelude.foldl (A.++) (A.use $ A.fromList (Z:.(fromInteger $ fromSing w'):.0) []) $ Prelude.map (A.transpose . Prelude.foldl (A.++) (A.use $ A.fromList (Z:.1:.0) [])) x2'
    adjB' = pAdd p (pAdd q adjt $ pSingleton w' h' x2) $ pSingleton w h x1
  in
    pCons w'' h'' a $ evalBackward sl nn vt adjB'

pSize :: Sing (l :: [(Nat, Nat)]) -> Int
pSize sl =
  let
    l = fromSing sl
  in
    Prelude.fromInteger $ Prelude.foldl (\r (a,b) -> r+a*b) 0 l

pExtend :: (A.Num e) => Sing l -> AtIndex l '(1, os) 0 -> PList ('(1, os) ': '[]) e -> PList l e
pExtend sl p e =
  let
    a = A.fill (index1 $ the $ unit $ constant $ pSize sl) 0
    pl = PList sl a
  in
    pAdd p pl e

evalBackwardL :: forall e l os w i s o . (A.Floating e) => Sing l -> SNat os -> AtIndex l '(1, os) 0 -> NeuralNetwork (ValueAndDerivative e) l w i s o s o -> [PList l e] -> [PList ('(1, os) ': '[]) e] -> PList s e -> PList o e -> PList l e
evalBackwardL sl sos p nn i a ps po = PList sl $ A.use $ foldr (\a b -> run1 step (B.run ((A.use b) A.++ (A.use a)))) (let (PList _ y) = NeuralNetwork2.init 0 sl in B.run y) (Prelude.map (\(PList _ p) -> B.run p) $ Prelude.zipWith (pJoin) i a)
  where sa = SCons (STuple2 (sing :: SNat 1) sos) SNil
        step x =
          let
            (adj, ia) = pSplit sl (sl %:++ sa) (PList (sl %:++ sl %:++ sa) x)
            (ii, aa) = pSplit sl sa ia
            (_, ps, po, _, _) = keepParams nn adj
            adj' = pExtend sl p aa
            adj'' = copyParams nn ps po adj'
            (PList _ r) = evalBackward sl nn ii adj''
          in
            r

evalForwardL :: forall e l s o i w . (A.Num e) => Sing l -> Sing s -> Sing o -> Sing i -> NeuralNetwork (ValueAndDerivative e) l w i s o s o -> PList w e -> [PList i e] -> PList s e -> PList o e -> [PList l e]
evalForwardL sl sngs sngo sngi nn w i s o = Prelude.fst $ foldl' step ([], (s, o)) i
  where step (r, (s, o)) i =
          let
            (PList _ x) = pJoin s (pJoin o i)
            r' = PList sl $ A.use $ run1 step' $ B.run x
            (_, _, _, s', o') = keepParams nn r'
          in
            (r' : r, (s', o'))
        step' x =
          let
            p = PList (sngs %:++ sngo %:++ sngi) x
            (ps, poi) = pSplit sngs (sngo %:++ sngi) p
            (po, pi) = pSplit sngo sngi poi            
            (PList _ r) = evalForward sl nn w pi ps po
          in
            r

evalForward :: (A.Num e) => Sing l -> NeuralNetwork (ValueAndDerivative e) l w i ps po s o -> PList w e -> PList i e -> PList ps e -> PList po e -> PList l e
evalForward sl (Unity w h) _ _ _ _ = pSingleton w h (generate (index2 (expVal w) (expVal h)) (\_ -> 1))
evalForward sl (Weight w h) ww _ _ _ = ww
evalForward sl (Input w h) _ ii _ _ = ii
evalForward sl (PreviousState w h) _ _ ps _ = ps
evalForward sl (PreviousOutput w h) _ _ _ po = po
evalForward (SCons _ sl) (State p nn i w h) ww ii ps po =
  let
    t = evalForward sl nn ww ii ps po
  in
    pCons w h (pAt p t) t
evalForward (SCons _ sl) (Output p nn i w h) ww ii ps po =
  let
    t = evalForward sl nn ww ii ps po
  in
    pCons w h (pAt p t) t
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
    d = pAt p t
    v = A.map (lift1 value) $ f $ A.map (lift1 fromValue) d
  in
    pCons w' h' v t
evalForward (SCons _ sl) (Binary p q nn i w h j w' h' ff@(_, _, _, _, w'', h'', f,  l)) ww ii ps po =
  let
    t = evalForward sl nn ww ii ps po
    d1 = pAt p t
    d2 = pAt q t
    v = A.map (lift1 value) $ f (A.map (lift1 fromValue) d1) (A.map (lift1 fromValue) d2)
  in
    pCons w'' h'' v t

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
        (PList _ p) = NeuralNetwork2.init x sp
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
        (PList _ r) = pJoin pw (pJoin ps po)
      in
        r

gradient2 :: forall e is os . (Prelude.Floating e, A.Floating e, Lift Exp e, e ~ Plain e) => Sing is -> Sing os -> SomeNeuralNetwork e is os -> ([PList ('(1, os) ': '[]) (ValueAndDerivative e)] -> Acc (Scalar (ValueAndDerivative e))) -> [Acc (Vector e)] -> Acc (Vector e) -> Acc (Vector e)
gradient2 sis sos nn f i p =
  case nn of
    SomeNeuralNetwork q1 q2 sl sw si ss so nn' ->
      let
        s1 = sing :: SNat 1
        pl = PList (sw %:++ ss %:++ so) p
        pi = Prelude.map (PList si) i
        (pw, pso) = pSplit sw (ss %:++ so) pl
        (ps, po) = pSplit ss so pso
        v = evalForwardL sl ss so si nn' pw pi ps po
        j = Prelude.map (\a -> pSingleton s1 sos a) $ jacobianl sos f (Prelude.map (\l -> pSingleton s1 sos (pAt q2 l)) v)
        g = evalBackwardL sl sos q2 nn' v j (NeuralNetwork2.init 0 ss) (NeuralNetwork2.init 0 so)
        (w', ps', po', _, _) = keepParams nn' g
        (PList _ rw) = w'
        (PList _ rs) = w'
        (PList _ ro) = w'
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
        pl = PList (sw %:++ ss %:++ so) p
        pi = Prelude.map (PList si) i
        (pw, pso) = pSplit sw (ss %:++ so) pl
        (ps, po) = pSplit ss so pso
        r = evalForwardL sl ss so si nn' pw pi ps po        
      in
        f $ Prelude.map (\rr -> pSingleton (sing ::SNat 1) sos (pAt q2 rr)) r

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
      let
        (PList _ r) = NeuralNetwork2.init (the $ unit $ constant x) (sw %:++ si %:++ ss)
      in
        B.run $ r

infList :: (a -> a) -> a -> [a]
infList f i = i:(infList f (f i))

gradientDescent :: forall e is os . (Prelude.Floating e, A.Floating e, Lift Exp e, e ~ Plain e) => e -> Sing is -> Sing os -> SomeNeuralNetwork e is os -> ([PList ('(1, os) ': '[]) (ValueAndDerivative e)] -> Acc (Scalar (ValueAndDerivative e))) -> [Acc (Vector e)] -> Vector e -> [(Vector e)]
gradientDescent eta sis sos nn f i p = infList (trace "forward" . run1 step) p
  where
    updateParam :: Exp e -> Exp e -> Exp e -> Exp e
    updateParam eta p g = p - eta * g
    step :: Acc (Vector e) -> Acc (Vector e)
    step p =
      let
        g = gradient2 sis sos nn f i p
        p' = safeZipWith1 (updateParam (the $ unit $ constant $ eta)) p g
      in
        p'
