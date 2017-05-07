{-# LANGUAGE DataKinds, KindSignatures, TypeOperators, GADTs, TemplateHaskell, TypeFamilies, UndecidableInstances, Rank2Types, AllowAmbiguousTypes, ScopedTypeVariables, MultiParamTypeClasses, FlexibleInstances, FlexibleContexts, PolyKinds #-}
{-# OPTIONS_GHC -fplugin=GHC.TypeLits.Normalise #-}

module NeuralNetwork2 where

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
import ValueAndDerivative

data AtIndexNat (l :: [Nat]) (e :: Nat) (i :: Nat) where
  HeadNat :: AtIndexNat (x ': xs) x 0
  TailNat :: AtIndexNat t x i -> AtIndexNat (h ': t) x (i + 1)

data AtIndex (l :: [(Nat, Nat)]) (e :: (Nat, Nat)) (i :: Nat) where
  Head :: AtIndex ('(w, h) ': xs) '(w, h) 0
  Tail :: AtIndex t x i -> AtIndex (h ': t) x (i + 1)

type Matrix e = Array DIM2 e

data PList (l :: [(Nat, Nat)]) e where
  PNil :: PList '[] e
  PCons :: SNat w -> SNat h -> Acc (Matrix e) -> PList l e -> PList ('(w, h) ': l) e

pSingleton :: SNat w -> SNat h -> Acc (Matrix e) -> PList ('(w, h) ': []) e
pSingleton sw sh a = PCons sw sh a PNil

pAdd :: AtIndex l '(w, h) i -> PList l e -> PList ('(w, 'h) ': '[]) e -> PList l e
pAdd Head (PCons sw sh a pt) (PCons _ _ b PNil) = PCons sw sh (A.zipWith (A.+) a b) pt
pAdd (Tail p) (PCons _ _ _ pt) pb = pAdd p pt pb

pAt :: AtIndex l '(w, h) i -> PList l e -> Acc (Matrix e)
pAt Head (PCons _ _ a _) = a
pAt (Tail p) (PCons _ _ _ l) = pAt p l

pSplit :: Sing l -> Sing l' -> PList (l :++ l') e -> (PList l e, PList l' e)
pSplit SNil sl' pl = (PNil, pl)
pSplit (SCons _ sl) sl' (PCons w h a pl) =
  let
    (p1, p2) = pSplit sl sl' pl
  in
    (PCons w h a p1, p2)

pJoin :: PList l e -> PList l' e -> PList (l :++ l') e
pJoin PNil pl' = pl'
pJoin (PCons w h a pl) pl' = PCons w h a (pJoin pl pl')

newtype Label = Label String
instance Show Label where
  show (Label s) = s

type UnaryFunction e (w :: Nat) (h :: Nat) (w' :: Nat) (h' :: Nat) = (Elt e) => (SNat w, SNat h, SNat w', SNat h', Acc (Matrix e) -> Acc (Matrix e), Label)
type BinaryFunction e (w :: Nat) (h :: Nat) (w' :: Nat) (h' :: Nat) (w'' :: Nat) (h'' :: Nat) = (Elt e) => (SNat w, SNat h, SNat w', SNat h', SNat w'', SNat h'', Acc (Matrix e) -> Acc (Matrix e) -> Acc (Matrix e), Label)

jacobian :: UnaryFunction a w h w' h' -> PList ('(w, h) ': '[]) e -> Matrix 

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

prd :: (A.Num e, Elt e) => Acc (Matrix e) -> Acc (Matrix e) -> Acc (Matrix e)
prd a b = A.fold (+) 0 $ A.zipWith (*) aRepl bRepl
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
expVal sn = fromInteger $ withKnownNat sn $ natVal sn

intVal :: Sing (n :: Nat) -> Int
intVal sn = fromInteger $ withKnownNat sn $ natVal sn

init :: (Elt e, A.Floating e) => Exp e -> Sing (l :: [(Nat, Nat)]) -> PList l e
init _ SNil = PNil
init x (SCons (STuple2 w h) sl) = PCons w h (generate (index2 (expVal w) (expVal h)) (\_ -> x)) (NeuralNetwork2.init x sl)

flatten :: (Elt e) => PList l e -> Acc (Vector e)
flatten PNil = A.use $ A.fromList (Z:.0) []
flatten (PCons _ _ a pt) = (A.flatten a) A.++ (NeuralNetwork2.flatten pt)

unflatten :: (Elt e) => Sing l -> Acc (Vector e) -> PList l e
unflatten SNil a = PNil
unflatten (SCons (STuple2 sw sh) sl) a =
  let
    i = A.take (expVal sw * expVal sh) a
    r = A.drop (expVal sw * expVal sh) a
  in
    PCons sw sh (reshape (index2 (expVal sw) (expVal sh)) i) (unflatten sl r) 

eval :: (A.Num e) => Sing l -> Sing os -> AtIndex l '(1, os) 0 -> NeuralNetwork e l w i ps po s o -> PList w e -> [PList i e] -> PList ps e -> PList po e -> ([PList ('(1, os) ': '[]) e] -> Acc (Scalar e)) -> Acc (Scalar e)
eval sl sos p nn ww ii ps po f = f $ eval'' sl sos p nn ww ii ps po

eval'' :: (A.Num e) => Sing l -> Sing os -> AtIndex l '(1, os) 0 -> NeuralNetwork e l w i ps po s o -> PList w e -> [PList i e] -> PList ps e -> PList po e -> [PList ('(1, os) ': '[]) e]
eval'' _ _ _ _ _ [] _ _ = []
eval'' sl sos p nn ww (ih:it) ps po =
  let
    r = PCons (sing :: SNat 1) sos (pAt p $ eval' sl nn ww ih ps po) PNil
  in
    r : eval'' sl sos p nn ww it ps po

evalComplete :: (A.Num e) => Sing l -> Sing os -> AtIndex l '(1, os) 0 -> NeuralNetwork e l w i ps po s o -> PList w e -> [PList i e] -> PList ps e -> PList po e -> [PList l e]
evalComplete _ _ _ _ _ [] _ _ = []
evalComplete sl sos p nn ww (ih:it) ps po =
  let
    r = eval' sl nn ww ih ps po
  in
    r : evalComplete sl sos p nn ww it ps po

ax = ay * dy/dx

evalBlaBla :: (A.Num e) => PList ('(w, h) ': '[]) e -> NeuralNetwork e ('(w, h) ': l) w i ps po s o -> PList l e -> PList l e
eval' a (Unity _ _) = id
eval' a (State p _ _ _ _) tape = pAdd p tape a
eval' a (Output p _ _ _ _) tape = pAdd p tape a
eval' a (Union _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) = id
eval' a (Unary p nn _ _ _ (_, _, _, _, f, _)) tape =
  let
    t = eval' sl nn ww ii ps po
  in
    PCons w' h' (f (pAt p t)) t
eval' (SCons _ sl) (Binary p q nn i w h j w' h' (_, _, _, _, w'', h'', f,  l)) ww ii ps po =
  let
    t = eval' sl nn ww ii ps po
  in
    PCons w'' h'' (f (pAt p t) (pAt q t)) t

eval' :: (A.Num e) => Sing l -> NeuralNetwork e l w i ps po s o -> PList w e -> PList i e -> PList ps e -> PList po e -> PList l e
eval' sl (Unity w h) PNil PNil PNil PNil = PCons w h (generate (index2 (expVal w) (expVal h)) (\_ -> 1)) PNil
eval' sl (Weight w h) ww PNil PNil PNil = ww
eval' sl (Input w h) PNil ii PNil PNil = ii
eval' sl (PreviousState w h) PNil PNil ps PNil = ps
eval' sl (PreviousOutput w h) PNil PNil PNil po = po
eval' (SCons _ sl) (State p nn i w h) ww ii ps po =
  let
    t = eval' sl nn ww ii ps po
  in
    PCons w h (pAt p t) t
eval' (SCons _ sl) (Output p nn i w h) ww ii ps po =
  let
    t = eval' sl nn ww ii ps po
  in
    PCons w h (pAt p t) t
eval' sl (Union nn1 sl1 sw1 si1 sps1 spo1 _ ss1 nn2 sl2 sw2 si2 sps2 spo2 _ _) ww ii ps po =
  let
    (ww1, ww2) = pSplit sw1 sw2 ww
    (ii1, ii2) = pSplit si1 si2 ii
    (ps1, ps2) = pSplit sps1 sps2 ps 
    (po1, po2) = pSplit spo1 spo2 po
    t1 = eval' sl1 nn1 ww1 ii1 ps1 po1
    t2 = eval' sl2 nn2 ww2 ii2 ps2 po2
  in
    pJoin t1 t2
eval' (SCons _ sl) (Unary p nn i w h (_, _, w', h', f, l)) ww ii ps po =
  let
    t = eval' sl nn ww ii ps po
  in
    PCons w' h' (f (pAt p t)) t
eval' (SCons _ sl) (Binary p q nn i w h j w' h' (_, _, _, _, w'', h'', f,  l)) ww ii ps po =
  let
    t = eval' sl nn ww ii ps po
  in
    PCons w'' h'' (f (pAt p t) (pAt q t)) t

data SomeNeuralNetwork e is os where
  SomeNeuralNetwork :: forall e l w i s o is os . (A.Floating e) => AtIndex l '(1, is) (Length l :- 1) -> AtIndex l '(1, os) 0 -> Sing l -> Sing w -> Sing i -> Sing s -> Sing o -> NeuralNetwork e l w i s o s o -> SomeNeuralNetwork e is os

gradientParams :: (Exp e) -> (Exp e) -> Sing is -> Sing os -> SomeNeuralNetwork e is os -> [Acc (Vector e)]
gradientParams x y sis sos nn =
  case nn of
    SomeNeuralNetwork q1 q2 _ sw si ss so nn' ->
      let
        sp = (sw %:++ ss %:++ so)
        dp = fromSing sp
        np = Prelude.map (index1 . lift) ([0..(fromInteger (foldl (\r (a, b) -> (r + a*b)) 0 dp)-1)] :: [Int])
        p = NeuralNetwork2.flatten $ NeuralNetwork2.init x sp
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
      in
        NeuralNetwork2.flatten $ pJoin pw (pJoin ps po)

gradient :: forall e is os . (Prelude.Num e, A.Num e, Lift Exp e, e ~ Plain e) => Sing is -> Sing os -> SomeNeuralNetwork (ValueAndDerivative e) is os -> ([PList ('(1, os) ': '[]) (ValueAndDerivative e)] -> Acc (Scalar (ValueAndDerivative e))) -> [Acc (Vector e)] -> Acc (Vector e)
gradient sis sos nn f i =
  let
    g = gradient' sis sos nn f (Prelude.map (A.map (lift1 fromValue)) i)
  in
    A.map (lift1 derivative) g

gradient' :: forall e is os . (Prelude.Num e, A.Elt e, Lift Exp e, e ~ Plain e) => Sing is -> Sing os -> SomeNeuralNetwork (ValueAndDerivative e) is os -> ([PList ('(1, os) ': '[]) (ValueAndDerivative e)] -> Acc (Scalar (ValueAndDerivative e))) -> [Acc (Vector (ValueAndDerivative e))] -> Acc (Vector (ValueAndDerivative e))
gradient' sis sos nn f i =
  let
    gp = gradientParams (lift $ ValueAndDerivative (0 :: e) (0 :: e)) (lift $ ValueAndDerivative (0 :: e) (1 :: e)) sis sos nn
    rs = Prelude.map (\p -> forward sis sos nn f p i) gp :: [Acc (Scalar (ValueAndDerivative e))]
    ds = Prelude.map (reshape (index1 1)) rs
  in
    foldl (A.++) (A.use $ A.fromList (Z:.0) []) ds

forward :: Sing is -> Sing os -> SomeNeuralNetwork e is os -> ([PList ('(1, os) ': '[]) e] -> Acc (Scalar e)) -> Acc (Vector e) -> [Acc (Vector e)] -> Acc (Scalar e)
forward sis sos nn f p i =
  case nn of
    SomeNeuralNetwork q1 q2 sl sw si ss so nn' ->
      let
        pl = unflatten (sw %:++ ss %:++ so) p
        pi = Prelude.map (unflatten si) i
        (pw, pso) = pSplit sw (ss %:++ so) pl
        (ps, po) = pSplit ss so pso
      in
        eval sl sos q2 nn' pw pi ps po f

toFGL :: DynGraph gr => SomeNeuralNetwork e i o -> gr Label Label
toFGL nn = case nn of
  SomeNeuralNetwork _ _ _ _ _ _ _ nn' -> toFGL'' nn'

data SomeSNat where
  SomeSNat :: SNat n -> SomeSNat

toSomeSNat :: Int -> Maybe SomeSNat
toSomeSNat n
  | n Prelude.> 0 = case toSomeSNat (n-1) of
      Just (SomeSNat sn) -> Just $ SomeSNat $ sn %:+ (sing :: SNat 1)
  | n Prelude.< 0 = Nothing
  | otherwise = Just $ SomeSNat (sing :: SNat 0)

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
