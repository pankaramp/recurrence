{-# LANGUAGE DataKinds, NoMonomorphismRestriction #-}

module Main (main) where

import Data.Graph.Inductive.Dot
import Data.Graph.Inductive.PatriciaTree
import NeuralNetwork
import Math
import Proofs
import Numeric.AD

main =
  let
    nn0 = NeuralNetwork.init (SS SZ)
    (nn, o) = lstmNeuron nn0 ((SF ZF) `Cons` Nil) ZF
--    (nn', o') = lstmNeuron nn (o `Cons` Nil) ZF
    i = [1..1000]
    x = fmap (\a -> ((a/1000.0) `Cons` Nil)) i
    y = fmap (\a -> ((sin a) `Cons` Nil)) i
    --dot = showDot (fglToDot $ (toFGL nn' :: Gr String ()))
  in
    print $ take 10 $ gd (mse y) nn x (zero, zero) zero
    --do
      --writeFile "file.dot" dot
