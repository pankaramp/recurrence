{-# LANGUAGE DataKinds, KindSignatures, TypeOperators, GADTs, TemplateHaskell, TypeFamilies, UndecidableInstances, Rank2Types, AllowAmbiguousTypes, ScopedTypeVariables, MultiParamTypeClasses, FlexibleInstances, FlexibleContexts #-}
{-# OPTIONS_GHC -fplugin=GHC.TypeLits.Normalise #-}
{-# OPTIONS_GHC -ddump-splices #-}

module NeuralNetwork2 where

import qualified Data.Type.List as L
import GHC.TypeLits
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

prod :: forall e a b c . (Num e) => SNat a -> SNat b -> SNat c -> BinaryFunction e a b b c a c
prod sa sb sc a1 a2 = array resultBounds [((i,j), Prelude.sum [a1!(i, k) * a2!(k, j)
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
          | otherwise                                                                    = error "prod: invalid bounds"

data NeuralNetwork a (l :: [(Nat, Nat)]) where
  Empty :: NeuralNetwork a '[]
  Unity :: SNat w -> SNat h -> NeuralNetwork a ('(w, h) ': '[])
  Weight :: SNat w -> SNat h -> NeuralNetwork a ('(w, h) ': '[])
  Input :: SNat w -> SNat h -> NeuralNetwork a ('(w, h) ': '[])
  PreviousState :: SNat w -> SNat h -> NeuralNetwork a ('(w, h) ': '[])
  PreviousOutput :: SNat w -> SNat h -> NeuralNetwork a ('(w, h) ': '[])
  State :: AtIndex l '(w, h) i -> NeuralNetwork a l -> SNat i -> NeuralNetwork a ('(w, h) ': l)
  Output :: AtIndex l '(w, h) i -> NeuralNetwork a l -> SNat i -> NeuralNetwork a ('(w, h) ': l)
  Union :: NeuralNetwork a l1 -> NeuralNetwork a l2 -> NeuralNetwork a (Concat (l1 ': l2 ': '[]))
  Unary :: AtIndex l '(w, h) i -> NeuralNetwork a l -> SNat i -> UnaryFunction a w h w' h' -> String -> NeuralNetwork a ('(w, h) ': l)
  Binary :: AtIndex l '(w, h) i -> AtIndex l '(w', h') j -> NeuralNetwork a l -> SNat i -> SNat j -> BinaryFunction a w h w' h' w'' h'' -> String -> NeuralNetwork a ('(w'', h'') ': l)
  Concat :: AtIndex l '(w, h1) i -> AtIndex l '(w, h2) j -> NeuralNetwork a l -> SNat i -> SNat j -> NeuralNetwork a ('(w, h1+h2) ': l)

concat_with_nil :: Sing (l :: [(Nat, Nat)]) -> l :~: Concat (l ': ('[]) ': '[])
concat_with_nil SNil = Refl


addWeight :: Sing l -> SNat w -> SNat h -> NeuralNetwork a l -> (NeuralNetwork a ('(w, h) ': l), AtIndex ('(w, h) ': l) '(w, h) 0)
addWeight sl sw sh nn =
    gcastWith (concat_with_nil sl) $ (Union (Weight sw sh) nn, Head)

addWeightedEdge :: forall e l a b c i . (Num e) => AtIndex l '(a, b) i -> Sing l -> SNat a -> SNat b -> SNat c -> SNat i -> NeuralNetwork e l -> NeuralNetwork e ('(a, c) ': '(b, c) ': l)
addWeightedEdge sp sl sa sb sc si nn =
  let
    (nn', sp') = addWeight sl sb sc nn
  in
    Binary (Tail sp) sp' nn' (si %:+ (sing :: SNat 1)) (sing :: SNat 0) (prod sa sb sc) "*"

addInducedLocalField :: forall e l a b c i . (Num e) => AtIndex l '(a, b) i -> Sing l -> SNat a -> SNat b -> SNat c -> SNat i -> NeuralNetwork e l -> NeuralNetwork e ('(a, c) ': '(b+1, c) ': '(a, b+1) ': '(a, 1) ': l)
addInducedLocalField sp sl sa sb sc si nn =
  let
    s0 = sing :: SNat 0
    s1 = sing :: SNat 1
    nn' = Union (Unity sa s1) nn
    sl' = SCons (STuple2 sa s1) sl
    sp' = Tail sp
    nn'' = Concat sp' Head (gcastWith (concat_with_nil sl) nn') (si %:+ s1) s0
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
    Unary Head nn' s0 sf sn
