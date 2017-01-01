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
    (nn0, u, i) = NeuralNetwork.init (SS (SS SZ))
    (nn1, o1) = lstmLayer (SS (SS SZ)) nn0 i u
    (nn, o) = lstmLayer (SS SZ) nn1 o1 u
--    (nn', o') = lstmNeuron nn (o `Cons` Nil) ZF
{-    i = [1..1000]
    x = fmap (\a -> ((a/1000.0) `Cons` Nil)) i
    y = fmap (\a -> ((sin a) `Cons` Nil)) i-}
    dot = case nn of
      NN n -> showDot (fglToDot $ (toFGL n :: Gr String ()))
  in
    --print $ take 10 $ gd (mse y) nn x (zero, zero) zero
    do
      writeFile "file.dot" dot
