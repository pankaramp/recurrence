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
import Data.Array.IArray
import Data.Graph.Inductive
import Data.Type.Equality

data AtIndexNat (l :: [Nat]) (e :: Nat) (i :: Nat) where
  HeadNat :: AtIndexNat (x ': xs) x 0
  TailNat :: AtIndexNat t x i -> AtIndexNat (h ': t) x (i + 1)

data AtIndex (l :: [(Nat, Nat)]) (e :: (Nat, Nat)) (i :: Nat) where
  Head :: AtIndex (x ': xs) x 0
  Tail :: AtIndex t x i -> AtIndex (h ': t) x (i + 1)

type UnaryFunction e (w :: Nat) (h :: Nat) (w' :: Nat) (h' :: Nat) = forall a w h w' h' . (IArray a e) => (a (Int, Int) e) -> (a (Int, Int) e)
type BinaryFunction e (w :: Nat) (h :: Nat) (w' :: Nat) (h' :: Nat) (w'' :: Nat) (h'' :: Nat) = forall a w h w' h' w'' h'' .(IArray a e) => (a (Int, Int) e) -> (a (Int, Int) e) -> (a (Int, Int) e)

tnh x = ((exp x) - (exp (-x))) / ((exp x) + (exp (-x)))

tanh ::(Floating a) => UnaryFunction a w h w h
tanh = amap tnh

sgm :: (Floating a) => a -> a
sgm x = 1 / (1 + exp (-x))

sigm ::(Floating a) => UnaryFunction a w h w h
sigm = amap sgm

sum :: forall e w h . (Num e) => SNat w -> SNat h -> BinaryFunction e w h w h w h
sum sw sh a1 a2 = listArray resultBounds (zipWith (+) (elems a1) (elems a2))
  where iw = fromInteger $ withKnownNat sw $ natVal sw
        ih = fromInteger $ withKnownNat sh $ natVal sh
        ((li , lj ), (ui , uj )) = bounds a1
        ((li', lj'), (ui', uj')) = bounds a2
        resultBounds
          | (li, lj, ui, uj, li', lj', ui', uj') == (0, 0, iw-1, ih-1, 0, 0, iw-1, ih-1) = ((li, lj), (ui, uj))
          | otherwise                                                                    = error "sum: invalid bounds"

prod :: forall e w h . (Num e) => SNat w -> SNat h -> BinaryFunction e w h w h w h
prod sw sh a1 a2 = listArray resultBounds (zipWith (*) (elems a1) (elems a2))
  where iw = fromInteger $ withKnownNat sw $ natVal sw
        ih = fromInteger $ withKnownNat sh $ natVal sh
        ((li , lj ), (ui , uj )) = bounds a1
        ((li', lj'), (ui', uj')) = bounds a2
        resultBounds
          | (li, lj, ui, uj, li', lj', ui', uj') == (0, 0, iw-1, ih-1, 0, 0, iw-1, ih-1) = ((li, lj), (ui, uj))
          | otherwise                                                                    = error "prod: invalid bounds"

dotprod :: forall e a b c . (Num e) => SNat a -> SNat b -> SNat c -> BinaryFunction e a b b c a c
dotprod sa sb sc a1 a2 = array resultBounds [((i,j), Prelude.sum [a1!(i, k) * a2!(k, j)
                                             | k <- range (lj, uj)])
                                | i <- range (li , ui),
                                  j <- range (lj', uj')]
  where ia = fromInteger $ withKnownNat sa $ natVal sa
        ib = fromInteger $ withKnownNat sb $ natVal sb
        ic = fromInteger $ withKnownNat sc $ natVal sc
        ((li , lj ), (ui , uj))  = bounds a1
        ((li', lj'), (ui', uj')) = bounds a2
        resultBounds
          | (li, lj, ui, uj, li', lj', ui', uj') == (0, 0, ia-1, ib-1, 0, 0, ib-1, ic-1) = ((li, lj'), (ui, uj'))
          | otherwise                                                                    = error "dotprod: invalid bounds"

concat :: forall e a b c . SNat a -> SNat b -> SNat c -> BinaryFunction e a b a c a (b+c)
concat sa sb sc a1 a2 = array resultBounds [((i,j), if j < ib then a1!(i, j) else a2!(i, j-ib))
                                | i <- range (0 , ia-1),
                                  j <- range (0, ib+ic-1)]
  where ia = fromInteger $ withKnownNat sa $ natVal sa
        ib = fromInteger $ withKnownNat sb $ natVal sb
        ic = fromInteger $ withKnownNat sc $ natVal sc
        ((li , lj ), (ui , uj))  = bounds a1
        ((li', lj'), (ui', uj')) = bounds a2
        resultBounds
          | (li, lj, ui, uj, li', lj', ui', uj') == (0, 0, ia-1, ib-1, 0, 0, ia-1, ic-1) = ((0, 0), (ia-1, ib+ic-1))
          | otherwise                                                                    = error "concat: invalid bounds"

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
  Unary :: AtIndex l '(w, h) i -> NeuralNetwork a l -> SNat i -> SNat w -> SNat h -> UnaryFunction a w h w' h' -> String -> NeuralNetwork a ('(w, h) ': l)
  Binary :: AtIndex l '(w, h) i -> AtIndex l '(w', h') j -> NeuralNetwork a l -> SNat i -> SNat w -> SNat h -> SNat j -> SNat w' -> SNat h' -> BinaryFunction a w h w' h' w'' h'' -> String -> NeuralNetwork a ('(w'', h'') ': l)

concat_with_nil :: Sing (l :: [(Nat, Nat)]) -> l :~: Concat (l ': '[] ': '[])
concat_with_nil SNil = Refl
concat_with_nil (SCons _ sl) = gcastWith (concat_with_nil sl) Refl

addWeight :: Sing l -> SNat w -> SNat h -> NeuralNetwork a l -> (NeuralNetwork a ('(w, h) ': l), AtIndex ('(w, h) ': l) '(w, h) 0)
addWeight sl sw sh nn =
    gcastWith (concat_with_nil sl) $ (Union (Weight sw sh) nn, Head)

addWeightedEdge :: forall e l a b c i . (Num e) => AtIndex l '(a, b) i -> Sing l -> SNat a -> SNat b -> SNat c -> SNat i -> NeuralNetwork e l -> NeuralNetwork e ('(a, c) ': '(b, c) ': l)
addWeightedEdge sp sl sa sb sc si nn =
  let
    (nn', sp') = addWeight sl sb sc nn
  in
    Binary (Tail sp) sp' nn' (si %:+ (sing :: SNat 1)) sa sb (sing :: SNat 0) sb sc (dotprod sa sb sc) "dot"

addInducedLocalField :: forall e l a b c i . (Num e) => AtIndex l '(a, b) i -> Sing l -> SNat a -> SNat b -> SNat c -> SNat i -> NeuralNetwork e l -> NeuralNetwork e ('(a, c) ': '(b+1, c) ': '(a, b+1) ': '(a, 1) ': l)
addInducedLocalField sp sl sa sb sc si nn =
  let
    s0 = sing :: SNat 0
    s1 = sing :: SNat 1
    nn' = Union (Unity sa s1) nn
    sl' = SCons (STuple2 sa s1) sl
    sp' = Tail sp
    nn'' = Binary sp' Head (gcastWith (concat_with_nil sl) nn') (si %:+ s1) sa sb s0 sa s1 (NeuralNetwork2.concat sa sb s1) "concat"
    sl'' = SCons (STuple2 sa (sb %:+ s1)) sl'
  in
    addWeightedEdge Head sl'' sa (sb %:+ s1) sc s0 nn''

addNeuron :: forall e l i o x . (Num e) => UnaryFunction e 1 o 1 o -> String -> AtIndex l '(1, i) x -> Sing l -> SNat i -> SNat o -> SNat x -> NeuralNetwork e l -> NeuralNetwork e ('(1, o) ': '(1, o) ': '(i+1, o) ': '(1, i+1) ': '(1, 1) ': l)
addNeuron sf sn sp sl si so sx nn =
  let
    s0 = sing :: SNat 0
    s1 = sing :: SNat 1
    nn' = addInducedLocalField sp sl s1 si so sx nn
    sl' = SCons (STuple2 s1 so) $ SCons (STuple2 (si %:+ s1) so) $ SCons (STuple2 s1 (si %:+ s1)) $ SCons (STuple2 s1 s1) sl
  in
    Unary Head nn' s0 s1 so sf sn
  
addLSTMLayer :: forall e l i o x . (Floating e) => AtIndex l '(1, i) x -> Sing l -> SNat i -> SNat o -> SNat x -> NeuralNetwork e l -> (NeuralNetwork e ('(1, o) ': '(1, o) ': '(1, o) ': '(1, o) ': '(1, o) ': '(1, o) ': '(1, o) ': '(1, o) ': '(1, o) ': '(1, o) ': '(i+o+1, o) ': '(1, i+o+1) ': '(1, 1) ': '(1, o) ': '(1, o) ': '(i+o+1, o) ': '(1, i+o+1) ': '(1, 1) ': '(1, o) ': '(1, o) ': '(i+o+1, o) ': '(1, i+o+1) ': '(1, 1) ': '(1, o) ': '(1, o) ': '(i+o+1, o) ': '(1, i+o+1) ': '(1, 1) ': '(1, i+o) ': '(1, o) ': l), Sing ('(1, o) ': '(1, o) ': '(1, o) ': '(1, o) ': '(1, o) ': '(1, o) ': '(1, o) ': '(1, o) ': '(1, o) ': '(1, o) ': '(i+o+1, o) ': '(1, i+o+1) ': '(1, 1) ': '(1, o) ': '(1, o) ': '(i+o+1, o) ': '(1, i+o+1) ': '(1, 1) ': '(1, o) ': '(1, o) ': '(i+o+1, o) ': '(1, i+o+1) ': '(1, 1) ': '(1, o) ': '(1, o) ': '(i+o+1, o) ': '(1, i+o+1) ': '(1, 1) ': '(1, i+o) ': '(1, o) ': l))
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
    
    nn'' = Binary sp' Head nn'  sx' s1 si s0 s1 so (NeuralNetwork2.concat s1 si so) "concat"
    sl'' = SCons (STuple2 s1 sio) sl'
    sx'' = s0
    sp'' = Head

    nn''' = addNeuron sigm "sigm" sp'' sl'' sio so sx'' nn''
    sl''' = SCons (STuple2 s1 so) $ SCons (STuple2 s1 so) $ SCons (STuple2 (sio %:+ s1) so) $ SCons (STuple2 s1 (sio %:+ s1)) $ SCons (STuple2 s1 s1) sl''
    sx''' = sx'' %:+ s5
    sp''' = Tail $ Tail $ Tail $ Tail $ Tail sp''

    nn'''' = addNeuron sigm "sigm" sp''' sl''' sio so sx''' nn'''
    sl'''' = SCons (STuple2 s1 so) $ SCons (STuple2 s1 so) $ SCons (STuple2 (sio %:+ s1) so) $ SCons (STuple2 s1 (sio %:+ s1)) $ SCons (STuple2 s1 s1) sl'''
    sx'''' = sx''' %:+ s5
    sp'''' = Tail $ Tail $ Tail $ Tail $ Tail sp'''

    nn''''' = addNeuron sigm "sigm" sp'''' sl'''' sio so sx'''' nn''''
    sl''''' = SCons (STuple2 s1 so) $ SCons (STuple2 s1 so) $ SCons (STuple2 (sio %:+ s1) so) $ SCons (STuple2 s1 (sio %:+ s1)) $ SCons (STuple2 s1 s1) sl''''
    sx''''' = sx'''' %:+ s5
    sp''''' = Tail $ Tail $ Tail $ Tail $ Tail sp''''

    nn'''''' = addNeuron NeuralNetwork2.tanh "tanh" sp''''' sl''''' sio so sx''''' nn'''''
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

    nn'''''''' = Binary spf sps nn'''''''  sf s1 so spst s1 so (prod s1 so) "*"
    sl'''''''' = SCons (STuple2 s1 so) $ sl'''''''

    nn''''''''' = Binary (Tail spi) (Tail spc) nn''''''''  (s1 %:+ sin) s1 so (s1 %:+ sc) s1 so (prod s1 so) "*"
    sl''''''''' = SCons (STuple2 s1 so) $ sl''''''''

    nn'''''''''' = Binary Head (Tail Head) nn'''''''''  s0 s1 so s1 s1 so (NeuralNetwork2.sum s1 so) "+"
    sl'''''''''' = SCons (STuple2 s1 so) $ sl'''''''''

    snst = s0
    spns = Head

    nn''''''''''' = Unary Head nn''''''''''  s0 s1 so NeuralNetwork2.tanh "tanh"
    sl''''''''''' = SCons (STuple2 s1 so) $ sl''''''''''

    nn'''''''''''' = Binary Head (Tail $ Tail $ Tail $ Tail spo) nn'''''''''''  s0 s1 so (s4 %:+ sou) s1 so (prod s1 so) "*"
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

toFGL' :: DynGraph gr => gr String String -> NeuralNetwork e l -> gr String String
toFGL' g Empty = g
toFGL' g (Unity w h) = ([], noNodes g, "U"++(showVal w)++"x"++(showVal h), []) & g
toFGL' g (Weight w h) = ([], noNodes g, "W"++(showVal w)++"x"++(showVal h), []) & g
toFGL' g (Input w h) = ([], noNodes g, "I"++(showVal w)++"x"++(showVal h), []) & g
toFGL' g (PreviousState w h) = ([], noNodes g, "PS"++(showVal w)++"x"++(showVal h), []) & g
toFGL' g (PreviousOutput w h) = ([], noNodes g, "PO"++(showVal w)++"x"++(showVal h), []) & g
toFGL' g (State _ nn i w h) =
  let
    g' = toFGL' g  nn
  in
  ([((showVal w)++"x"++(showVal h), val i g')], noNodes g', "S"++(showVal w)++"x"++(showVal h), []) & g'
toFGL' g (Output _ nn i w h) =
  let
    g' = toFGL' g  nn
  in
  ([((showVal w)++"x"++(showVal h), val i g')], noNodes g', "O"++(showVal w)++"x"++(showVal h), []) & g'
toFGL' g (Union nn1 nn2) = toFGL' (toFGL' g nn2) nn1
toFGL' g (Unary _ nn i sw sh f l) =
  let
    g' = toFGL' g  nn
  in
  ([((showVal sw)++"x"++(showVal sh), val i g')], noNodes g', l, []) & g'
toFGL' g (Binary _ _ nn i sw sh j sw' sh' f l) =
  let
    g' = toFGL' g  nn
  in
  ([((showVal sw)++"x"++(showVal sh), val i g'), ((showVal sw')++"x"++(showVal sh'), val j g')], noNodes g', l, []) & g'

toFGL'' :: DynGraph gr => NeuralNetwork e l -> gr String String
toFGL'' = toFGL' empty

data SomeNeuralNetwork e i o where
  SomeNeuralNetwork :: forall e i o (l :: [(Nat, Nat)]) . (Floating e) => Sing l -> AtIndex l '(1, i) ((Length l) - 1) -> AtIndex l '(1, o) 0 -> NeuralNetwork e l -> SomeNeuralNetwork e i o

toFGL :: DynGraph gr => SomeNeuralNetwork e i o -> gr String String
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

addLayer :: SNat i -> SNat o -> SNat o' -> SomeNeuralNetwork e i o -> SomeNeuralNetwork e i o'
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

addLayers :: SNat i -> SNat o -> Sing ((o' ': l) :: [Nat]) -> SomeNeuralNetwork e i o -> SomeNeuralNetwork e i o'
addLayers si so (SCons so' SNil) nn = addLayer si so so' nn
addLayers si so (SCons sx (SCons sy sl)) nn = addLayer si sy sx $ addLayers si so (SCons sy sl) nn

makeNetwork :: (Floating e) => SNat i -> Sing (l :: [Nat]) -> SNat o -> SomeNeuralNetwork e i o
makeNetwork si sl so =
  let
    s1 = sing :: SNat 1
    nn = SomeNeuralNetwork (SCons (STuple2 s1 si) SNil) Head Head $ Input s1 si
  in
    addLayers si si (SCons so (sReverse sl)) nn
