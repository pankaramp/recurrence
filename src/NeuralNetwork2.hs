{-# LANGUAGE DataKinds, KindSignatures, TypeOperators, GADTs, TemplateHaskell, TypeFamilies, UndecidableInstances, Rank2Types, AllowAmbiguousTypes, ScopedTypeVariables #-}
{-# OPTIONS_GHC -fplugin=TypeNatSolver #-}

module NeuralNetwork2 where

import qualified Data.Type.List as L
import GHC.TypeLits
import Data.Singletons
import Data.Promotion.TH
import Data.Singletons.TypeLits
import Data.Singletons.Prelude.Num
import Data.Singletons.Prelude.List
import Data.Array.IArray
import Data.Graph.Inductive

$(promoteOnly [d|
                m :: Nat -> (Nat, (Nat, Nat)) -> (Nat, (Nat, Nat))
                m n (x, y) = ((n+x), y)
                |])

type UnaryFunction e (w :: Nat) (h :: Nat) (w' :: Nat) (h' :: Nat) = forall a w h w' h' . (IArray a e) => (a (Int, Int) e) -> (a (Int, Int) e)
type BinaryFunction e (w :: Nat) (h :: Nat) (w' :: Nat) (h' :: Nat) (w'' :: Nat) (h'' :: Nat) = forall a w h w' h' w'' h'' .(IArray a e) => (a (Int, Int) e) -> (a (Int, Int) e) -> (a (Int, Int) e)

tnh x = ((exp x) - (exp (-x))) / ((exp x) + (exp (-x)))

tanh ::(Floating a) => UnaryFunction a w h w h
tanh = amap tnh

sgm :: (Floating a) => a -> a
sgm x = 1 / (1 + exp (-x))

sigm ::(Floating a) => UnaryFunction a w h w h
sigm = amap sgm

sum :: forall e w h . (Num e, KnownNat w, KnownNat h) => BinaryFunction e w h w h w h
sum a1 a2 = listArray resultBounds (zipWith (+) (elems a1) (elems a2))
  where sw = fromInteger $ natVal (sing :: SNat w)
        sh = fromInteger $ natVal (sing :: SNat h)
        ((li , lj ), (ui , uj )) = bounds a1
        ((li', lj'), (ui', uj')) = bounds a2
        resultBounds
          | (li, lj, ui, uj, li', lj', ui', uj') == (0, 0, sw-1, sh-1, 0, 0, sw-1, sh-1) = ((li, lj), (ui, uj))
          | otherwise                                                                    = error "sum: invalid bounds"

prod :: forall e a b c . (Num e, KnownNat a, KnownNat b, KnownNat c) => BinaryFunction e a b b c a c
prod a1 a2 = array resultBounds [((i,j), Prelude.sum [a1!(i, k) * a2!(k, j)
                                             | k <- range (lj, uj)])
                                | i <- range (li , ui),
                                  j <- range (lj', uj')]
  where sa = fromInteger $ natVal (sing :: SNat a)
        sb = fromInteger $ natVal (sing :: SNat b)
        sc = fromInteger $ natVal (sing :: SNat c)
        ((li , lj ), (ui , uj))  = bounds a1
        ((li', lj'), (ui', uj')) = bounds a2
        resultBounds
          | (li, lj, ui, uj, li', lj', ui', uj') == (0, 0, sa-1, sb-1, 0, 0, sb-1, sc-1) = ((li, lj'), (ui, uj'))
          | otherwise                                                                    = error "prod: invalid bounds"

data NeuralNetwork (n :: Nat) (l :: [(Nat, (Nat, Nat))]) where
  Empty :: NeuralNetwork 0 '[]
  Close :: NeuralNetwork n l -> SNat i -> NeuralNetwork n (L.Remove '(i, (L.Lookup i l)) l)
  Unity :: SNat w -> SNat h -> NeuralNetwork 1 ('(0, '(w, h)) ': '[])
  Weight :: SNat w -> SNat h -> NeuralNetwork 1 ('(0, '(w, h)) ': '[])
  Input :: SNat w -> SNat h -> NeuralNetwork 1 ('(0, '(w, h)) ': '[])
  PreviousState :: SNat w -> SNat h -> NeuralNetwork 1 ('(0, '(w, h)) ': '[])
  PreviousOutput :: SNat w -> SNat h -> NeuralNetwork 1 ('(0, '(w, h)) ': '[])
  State :: (L.Find '(i, '(w, h)) l ~ True) => NeuralNetwork n l -> SNat i -> SNat w -> SNat h -> NeuralNetwork (n+1) l
  Output :: (L.Find '(i, '(w, h)) l ~ True) => NeuralNetwork n l -> SNat i -> SNat w -> SNat h -> NeuralNetwork (n+1) l
  Union :: NeuralNetwork n1 l1 -> NeuralNetwork n2 l2 -> NeuralNetwork (n1 + n2) (Concat (l1 ': (Map (MSym1 n1) l2) ': '[]))
  Unary :: (L.Find '(i, '(w, h)) l ~ True) => NeuralNetwork n l -> SNat i -> SNat w -> SNat h -> (forall a . UnaryFunction a w h w' h') -> String -> NeuralNetwork (n+1) ('(n, '(w, h)) ': l)
  Binary :: (L.Find '(i, '(w, h)) l ~ True, L.Find '(j, '(w, h)) l ~ True) => NeuralNetwork n l -> SNat i -> SNat w -> SNat h -> SNat j -> SNat w' -> SNat h' -> (forall a . BinaryFunction a w h w' h' w'' h'') -> String -> NeuralNetwork (n+1) ('(n, '(w'', h'')) ': l)

val :: Sing (n :: Nat) -> Int
val sn = fromInteger $ withKnownNat sn $ natVal sn

toFGL' :: DynGraph gr => gr String String -> NeuralNetwork n l -> gr String String
toFGL' g Empty = g
toFGL' g (Close nn i) = toFGL' g nn
toFGL' g (Unity w h) = ([], noNodes g, "U"++(show $ val w)++"x"++(show $ val h), []) & g
toFGL' g (Weight w h) = ([], noNodes g, "W"++(show $ val w)++"x"++(show $ val h), []) & g
toFGL' g (Input w h) = ([], noNodes g, "I"++(show $ val w)++"x"++(show $ val h), []) & g
toFGL' g (PreviousState w h) = ([], noNodes g, "PS"++(show $ val w)++"x"++(show $ val h), []) & g
toFGL' g (PreviousOutput w h) = ([], noNodes g, "PO"++(show $ val w)++"x"++(show $ val h), []) & g
toFGL' g (State nn i w h) =
  let
    g' = toFGL' g  nn
  in
  ([((show $ val w)++"x"++(show $ val h), val i)], noNodes g', "S"++(show $ val w)++"x"++(show $ val h), []) & g'
toFGL' g (Output nn i w h) =
  let
    g' = toFGL' g  nn
  in
  ([((show $ val w)++"x"++(show $ val h), val i)], noNodes g', "O"++(show $ val w)++"x"++(show $ val h), []) & g'
toFGL' g (Union nn1 nn2) = toFGL' (toFGL' g nn1) nn2
toFGL' g (Unary nn i sw sh f l) =
  let
    g' = toFGL' g  nn
  in
  ([((show $ val sw)++"x"++(show $ val sh), val i)], noNodes g', l, []) & g'
toFGL' g (Binary nn i sw sh j sw' sh' f l) =
  let
    g' = toFGL' g  nn
  in
  ([((show $ val sw)++"x"++(show $ val sh), val i), ((show $ val sw')++"x"++(show $ val sh'), val j)], noNodes g', l, []) & g'

toFGL :: DynGraph gr => NeuralNetwork n l -> gr String String
toFGL = toFGL' empty

addWeight :: SNat w -> SNat h -> NeuralNetwork n l -> NeuralNetwork (n+1) (Concat (l ': ('(n, '(w, h)) ': '[]) ': '[]))
addWeight sw sh nn =
    Union nn (Weight sw sh)
