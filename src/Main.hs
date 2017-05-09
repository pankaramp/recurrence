{-# LANGUAGE DataKinds, NoMonomorphismRestriction, TypeOperators, TypeFamilies, FlexibleContexts #-}

module Main (main) where

import Data.Array.Accelerate as A
import Data.Array.Accelerate.LLVM.Native
import Data.Graph.Inductive.Dot
import Data.Graph.Inductive.PatriciaTree
import NeuralNetwork2
import Data.Singletons
import GHC.TypeLits
import Data.Singletons.TypeLits
import Data.Singletons.Prelude.List
import ValueAndDerivative

main :: IO ()
main =
  let
    ir = [[1]]
    ia = (Prelude.map (A.use . A.fromList (Z:.1:.1)) ir) :: [Acc (Matrix Double)]
    i = Prelude.map (\a -> PCons s1 s1 a PNil) ia
    f = (\(PCons _ _ a PNil) -> A.sum a) :: PList ('(1, 1) ': '[]) (ValueAndDerivative Double) -> Acc (Scalar (ValueAndDerivative Double))
    e = (Prelude.foldr (A.zipWith (A.+)) (fill index0 1)) . (Prelude.map f)
    s1 = sing :: SNat 1
    nn = makeNetwork s1 (SNil) s1 :: SomeNeuralNetwork Double 1 1
    --p = forwardParams (lift (1.01 :: Double)) s1 s1 nn
  in
    do
      writeFile "file.dot" $ showDot (fglToDot $ (toFGL nn :: Gr Label Label))
      print $ run $ gradient2 s1 s1 nn e (Prelude.map NeuralNetwork2.flatten i)


