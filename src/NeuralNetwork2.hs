{-# LANGUAGE DataKinds, KindSignatures, TypeOperators, GADTs, TemplateHaskell, TypeFamilies, UndecidableInstances, Rank2Types, AllowAmbiguousTypes, ScopedTypeVariables, MultiParamTypeClasses, FlexibleInstances, FlexibleContexts #-}
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
import Data.Array.Accelerate as A

data AtIndexNat (l :: [Nat]) (e :: Nat) (i :: Nat) where
  HeadNat :: AtIndexNat (x ': xs) x 0
  TailNat :: AtIndexNat t x i -> AtIndexNat (h ': t) x (i + 1)

data AtIndex (l :: [(Nat, Nat)]) (e :: (Nat, Nat)) (i :: Nat) where
  Head :: AtIndex (x ': xs) x 0
  Tail :: AtIndex t x i -> AtIndex (h ': t) x (i + 1)

type Matrix e = Array DIM2 e

newtype Label = Label String
instance Show Label where
  show (Label s) = s

type UnaryFunction e (w :: Nat) (h :: Nat) (w' :: Nat) (h' :: Nat) = (Elt e) => (Acc (Matrix e) -> Acc (Matrix e), Label)
type BinaryFunction e (w :: Nat) (h :: Nat) (w' :: Nat) (h' :: Nat) (w'' :: Nat) (h'' :: Nat) = (Elt e) => (Acc (Matrix e) -> Acc (Matrix e) -> Acc (Matrix e), Label)

tnh :: (IsFloating a, Elt a) => Exp a -> Exp a
tnh x = ((exp x) - (exp (-x))) / ((exp x) + (exp (-x)))

tanh ::(IsFloating a) => UnaryFunction a w h w h
tanh = (A.map tnh, Label "tanh")

sgm :: (IsFloating a, Elt a) => Exp a -> Exp a
sgm x = 1 / (1 + exp (-x))

sigm ::(IsFloating a) => UnaryFunction a w h w h
sigm = (A.map sgm, Label "sigm")

esum :: (IsNum e) => SNat w -> SNat h -> BinaryFunction e w h w h w h
esum _ _ = (A.zipWith (+), Label ".+")

eprod :: (IsNum e) => SNat w -> SNat h -> BinaryFunction e w h w h w h
eprod _ _ = (A.zipWith (*), Label ".*")

prd :: (IsNum e, Elt e) => Acc (Matrix e) -> Acc (Matrix e) -> Acc (Matrix e)
prd a b = A.fold (+) 0 $ A.zipWith (*) aRepl bRepl
  where
    Z :. rowsA :.     _ = unlift (shape a)    :: Z :. Exp Int :. Exp Int
    Z :.     _ :. colsB = unlift (shape b)    :: Z :. Exp Int :. Exp Int
    aRepl = A.replicate (lift $ Z :. All   :. colsB :. All) a
    bRepl = A.replicate (lift $ Z :. rowsA :. All   :. All) (A.transpose b)

prod :: (IsNum e, Elt e) => SNat a -> SNat b -> SNat c -> BinaryFunction e a b b c a c
prod _ _ _= (prd, Label "*")

concat :: forall e a b c . SNat a -> SNat b -> SNat c -> BinaryFunction e a b a c a (b+c)
concat sa sb sc = ((A.++), Label "++")

data NeuralNetwork a (l :: [(Nat, Nat)]) where
  Empty :: NeuralNetwork a '[]
  Unity :: SNat w -> SNat h -> NeuralNetwork a ('(w, h) ': '[])
  Weight :: SNat w -> SNat h -> NeuralNetwork a ('(w, h) ': '[])
  Input :: SNat w -> SNat h -> NeuralNetwork a ('(w, h) ': '[])
  PreviousState :: SNat w -> SNat h -> NeuralNetwork a ('(w, h) ': '[])
  PreviousOutput :: SNat w -> SNat h -> NeuralNetwork a ('(w, h) ': '[])
  State :: AtIndex l '(w, h) i -> NeuralNetwork a l -> SNat i -> SNat w -> SNat h -> NeuralNetwork a ('(w, h) ': l)
  Output :: AtIndex l '(w, h) i -> NeuralNetwork a l -> SNat i -> SNat w -> SNat h -> NeuralNetwork a ('(w, h) ': l)
  Union :: NeuralNetwork a l1 -> NeuralNetwork a l2 -> NeuralNetwork a (Concat (l1 ': l2 ': '[]))
  Unary :: (Elt a) => AtIndex l '(w, h) i -> NeuralNetwork a l -> SNat i -> SNat w -> SNat h -> UnaryFunction a w h w' h' -> NeuralNetwork a ('(w, h) ': l)
  Binary :: (Elt a) => AtIndex l '(w, h) i -> AtIndex l '(w', h') j -> NeuralNetwork a l -> SNat i -> SNat w -> SNat h -> SNat j -> SNat w' -> SNat h' -> BinaryFunction a w h w' h' w'' h'' -> NeuralNetwork a ('(w'', h'') ': l)

concat_with_nil :: Sing (l :: [(Nat, Nat)]) -> l :~: Concat (l ': '[] ': '[])
concat_with_nil SNil = Refl
concat_with_nil (SCons _ sl) = gcastWith (concat_with_nil sl) Refl

addWeight :: Sing l -> SNat w -> SNat h -> NeuralNetwork a l -> (NeuralNetwork a ('(w, h) ': l), AtIndex ('(w, h) ': l) '(w, h) 0)
addWeight sl sw sh nn =
    gcastWith (concat_with_nil sl) $ (Union (Weight sw sh) nn, Head)

addWeightedEdge :: (IsNum e, Elt e) => AtIndex l '(a, b) i -> Sing l -> SNat a -> SNat b -> SNat c -> SNat i -> NeuralNetwork e l -> NeuralNetwork e ('(a, c) ': '(b, c) ': l)
addWeightedEdge sp sl sa sb sc si nn =
  let
    (nn', sp') = addWeight sl sb sc nn
  in
    Binary (Tail sp) sp' nn' (si %:+ (sing :: SNat 1)) sa sb (sing :: SNat 0) sb sc (prod sa sb sc)

addInducedLocalField :: (IsNum e, Elt e) => AtIndex l '(a, b) i -> Sing l -> SNat a -> SNat b -> SNat c -> SNat i -> NeuralNetwork e l -> NeuralNetwork e ('(a, c) ': '(b+1, c) ': '(a, b+1) ': '(a, 1) ': l)
addInducedLocalField sp sl sa sb sc si nn =
  let
    s0 = sing :: SNat 0
    s1 = sing :: SNat 1
    nn' = Union (Unity sa s1) nn
    sl' = SCons (STuple2 sa s1) sl
    sp' = Tail sp
    nn'' = Binary sp' Head (gcastWith (concat_with_nil sl) nn') (si %:+ s1) sa sb s0 sa s1 (NeuralNetwork2.concat sa sb s1)
    sl'' = SCons (STuple2 sa (sb %:+ s1)) sl'
  in
    addWeightedEdge Head sl'' sa (sb %:+ s1) sc s0 nn''

addNeuron :: (IsNum e, Elt e) => UnaryFunction e 1 o 1 o -> AtIndex l '(1, i) x -> Sing l -> SNat i -> SNat o -> SNat x -> NeuralNetwork e l -> NeuralNetwork e ('(1, o) ': '(1, o) ': '(i+1, o) ': '(1, i+1) ': '(1, 1) ': l)
addNeuron sf sp sl si so sx nn =
  let
    s0 = sing :: SNat 0
    s1 = sing :: SNat 1
    nn' = addInducedLocalField sp sl s1 si so sx nn
    sl' = SCons (STuple2 s1 so) $ SCons (STuple2 (si %:+ s1) so) $ SCons (STuple2 s1 (si %:+ s1)) $ SCons (STuple2 s1 s1) sl
  in
    Unary Head nn' s0 s1 so sf
  
addLSTMLayer :: forall e i o l x . (IsFloating e, Elt e) => AtIndex l '(1, i) x -> Sing l -> SNat i -> SNat o -> SNat x -> NeuralNetwork e l -> (NeuralNetwork e ('(1, o) ': '(1, o) ': '(1, o) ': '(1, o) ': '(1, o) ': '(1, o) ': '(1, o) ': '(1, o) ': '(1, o) ': '(1, o) ': '(i+o+1, o) ': '(1, i+o+1) ': '(1, 1) ': '(1, o) ': '(1, o) ': '(i+o+1, o) ': '(1, i+o+1) ': '(1, 1) ': '(1, o) ': '(1, o) ': '(i+o+1, o) ': '(1, i+o+1) ': '(1, 1) ': '(1, o) ': '(1, o) ': '(i+o+1, o) ': '(1, i+o+1) ': '(1, 1) ': '(1, i+o) ': '(1, o) ': l), Sing ('(1, o) ': '(1, o) ': '(1, o) ': '(1, o) ': '(1, o) ': '(1, o) ': '(1, o) ': '(1, o) ': '(1, o) ': '(1, o) ': '(i+o+1, o) ': '(1, i+o+1) ': '(1, 1) ': '(1, o) ': '(1, o) ': '(i+o+1, o) ': '(1, i+o+1) ': '(1, 1) ': '(1, o) ': '(1, o) ': '(i+o+1, o) ': '(1, i+o+1) ': '(1, 1) ': '(1, o) ': '(1, o) ': '(i+o+1, o) ': '(1, i+o+1) ': '(1, 1) ': '(1, i+o) ': '(1, o) ': l))
addLSTMLayer sp sl si so sx nn =
  let
    s0 = sing :: SNat 0
    s1 = sing :: SNat 1
    s2 = sing :: SNat 2
    s3 = sing :: SNat 3
    s4 = sing :: SNat 4
    s5 = sing :: SNat 5
    sio = si %:+ so

    nn' = gcastWith (concat_with_nil sl) $ Union (PreviousOutput s1 so) nn :: NeuralNetwork e ('(1, o) ': l)
    sl' = SCons (STuple2 s1 so) sl
    sx' = sx %:+ s1
    sp' = Tail sp
    
    nn'' = Binary sp' Head nn'  sx' s1 si s0 s1 so (NeuralNetwork2.concat s1 si so)
    sl'' = SCons (STuple2 s1 sio) sl'
    sx'' = s0
    sp'' = Head

    nn''' = addNeuron sigm sp'' sl'' sio so sx'' nn''
    sl''' = SCons (STuple2 s1 so) $ SCons (STuple2 s1 so) $ SCons (STuple2 (sio %:+ s1) so) $ SCons (STuple2 s1 (sio %:+ s1)) $ SCons (STuple2 s1 s1) sl''
    sx''' = sx'' %:+ s5
    sp''' = Tail $ Tail $ Tail $ Tail $ Tail sp''

    nn'''' = addNeuron sigm sp''' sl''' sio so sx''' nn'''
    sl'''' = SCons (STuple2 s1 so) $ SCons (STuple2 s1 so) $ SCons (STuple2 (sio %:+ s1) so) $ SCons (STuple2 s1 (sio %:+ s1)) $ SCons (STuple2 s1 s1) sl'''
    sx'''' = sx''' %:+ s5
    sp'''' = Tail $ Tail $ Tail $ Tail $ Tail sp'''

    nn''''' = addNeuron sigm sp'''' sl'''' sio so sx'''' nn''''
    sl''''' = SCons (STuple2 s1 so) $ SCons (STuple2 s1 so) $ SCons (STuple2 (sio %:+ s1) so) $ SCons (STuple2 s1 (sio %:+ s1)) $ SCons (STuple2 s1 s1) sl''''
    sx''''' = sx'''' %:+ s5
    sp''''' = Tail $ Tail $ Tail $ Tail $ Tail sp''''

    nn'''''' = addNeuron NeuralNetwork2.tanh sp''''' sl''''' sio so sx''''' nn'''''
    sl'''''' = SCons (STuple2 s1 so) $ SCons (STuple2 s1 so) $ SCons (STuple2 (sio %:+ s1) so) $ SCons (STuple2 s1 (sio %:+ s1)) $ SCons (STuple2 s1 s1) sl'''''
    sx'''''' = sx''''' %:+ s5
    sp'''''' = Tail $ Tail $ Tail $ Tail $ Tail sp'''''

    nn''''''' = gcastWith (concat_with_nil sl) $ Union (PreviousState s1 so) nn''''''
    sl''''''' = SCons (STuple2 s1 so) sl''''''

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

    nn''''''''''' = Unary Head nn''''''''''  s0 s1 so NeuralNetwork2.tanh
    sl''''''''''' = SCons (STuple2 s1 so) $ sl''''''''''

    nn'''''''''''' = Binary Head (Tail $ Tail $ Tail $ Tail spo) nn'''''''''''  s0 s1 so (s4 %:+ sou) s1 so (eprod s1 so)
    sl'''''''''''' = SCons (STuple2 s1 so) $ sl'''''''''''
    
    nn''''''''''''' = State (Tail $ Tail Head) nn'''''''''''' (s2 %:+ snst) s1 so
    sl''''''''''''' = SCons (STuple2 s1 so) $ sl''''''''''''

    nn'''''''''''''' = Output (Tail Head) nn''''''''''''' s1 s1 so
    sl'''''''''''''' = SCons (STuple2 s1 so) $ sl'''''''''''''
  in
    (
      nn'''''''''''''',
      sl''''''''''''''
    )

showVal :: Sing (n :: Nat) -> String
showVal sn = show $ fromInteger $ withKnownNat sn $ natVal sn

val :: Graph gr => Sing (n :: Nat) -> gr a b -> Int
val sn g = noNodes g - 1 - (fromInteger $ withKnownNat sn $ natVal sn)

toFGL' :: DynGraph gr => gr Label Label -> NeuralNetwork e l -> gr Label Label
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
toFGL' g (Union nn1 nn2) = toFGL' (toFGL' g nn2) nn1
toFGL' g (Unary _ nn i sw sh (f, l)) =
  let
    g' = toFGL' g  nn
  in
  ([(Label((showVal sw)Prelude.++"x"Prelude.++(showVal sh)), val i g')], noNodes g', l, []) & g'
toFGL' g (Binary _ _ nn i sw sh j sw' sh' (f, l)) =
  let
    g' = toFGL' g  nn
  in
  ([(Label((showVal sw)Prelude.++"x"Prelude.++(showVal sh)), val i g'), (Label((showVal sw')Prelude.++"x"Prelude.++(showVal sh')), val j g')], noNodes g', l, []) & g'

toFGL'' :: DynGraph gr => NeuralNetwork e l -> gr Label Label
toFGL'' = toFGL' empty

data SomeNeuralNetwork e i o where
  SomeNeuralNetwork :: forall e i o (l :: [(Nat, Nat)]) (ww :: [(Nat, Nat)]) (ii :: [(Nat, Nat)]) (ps :: [(Nat, Nat)]) (po :: [(Nat, Nat)]) (s :: [(Nat, Nat)]) (oo :: [(Nat, Nat)]) . (IsFloating e) => Sing l -> AtIndex l '(1, i) ((Length l) - 1) -> AtIndex l '(1, o) 0 -> NeuralNetwork e l -> SomeNeuralNetwork e i o

toFGL :: DynGraph gr => SomeNeuralNetwork e i o -> gr Label Label
toFGL nn = case nn of
  SomeNeuralNetwork _ _ _ nn' -> toFGL'' nn'

data SomeSNat where
  SomeSNat :: SNat n -> SomeSNat

toSomeSNat :: Int -> Maybe SomeSNat
toSomeSNat n
  | n > 0 = case toSomeSNat (n-1) of
      Just (SomeSNat sn) -> Just $ SomeSNat $ sn %:+ (sing :: SNat 1)
  | n < 0 = Nothing
  | otherwise = Just $ SomeSNat (sing :: SNat 0)

addLayer :: (Elt e) => SNat i -> SNat o -> SNat o' -> SomeNeuralNetwork e i o -> SomeNeuralNetwork e i o'
addLayer si so so' nn =
  let
    s0 = sing :: SNat 0
    s1 = sing :: SNat 1
  in
    case nn of
      SomeNeuralNetwork sl spi spo nn' ->
        let
          (nn'', sl') = addLSTMLayer spo sl so so' s0 nn'
        in
          SomeNeuralNetwork sl' $(tailN 30 [e|spi|]) Head nn''

addLayers :: (Elt e) => SNat i -> SNat o -> Sing ((o' ': l) :: [Nat]) -> SomeNeuralNetwork e i o -> SomeNeuralNetwork e i o'
addLayers si so (SCons so' SNil) nn = addLayer si so so' nn
addLayers si so (SCons sx (SCons sy sl)) nn = addLayer si sy sx $ addLayers si so (SCons sy sl) nn

makeNetwork :: (IsFloating e, Elt e) => SNat i -> Sing (l :: [Nat]) -> SNat o -> SomeNeuralNetwork e i o
makeNetwork si sl so =
  let
    s1 = sing :: SNat 1
    nn = SomeNeuralNetwork (SCons (STuple2 s1 si) SNil) Head Head $ Input s1 si
  in
    addLayers si si (SCons so (sReverse sl)) nn
