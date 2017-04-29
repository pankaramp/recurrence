{-# LANGUAGE DataKinds, NoMonomorphismRestriction, TypeOperators, TypeFamilies #-}

module Main (main) where

import Data.Array.Accelerate.Interpreter
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
    s5 = sing :: SNat 5
    s6 = sing :: SNat 6
    s3 = sing :: SNat 3
    nn = makeNetwork s5 (SCons s6 SNil) s3 :: SomeNeuralNetwork (ValueAndDerivative Double) 5 3
    prog = case nn of
      SomeNeuralNetwork sl _ _ nn' ->
        let
          (w, i, ps, po) = NeuralNetwork2.initD 0 0 0 sl
        in
          eval sl nn' w i ps po
  in
    do
      writeFile "file.dot" $ showDot (fglToDot $ (toFGL nn :: Gr Label Label))
      print $ run $ prog !! 0


