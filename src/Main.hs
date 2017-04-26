{-# LANGUAGE DataKinds, NoMonomorphismRestriction, TypeOperators, TypeFamilies #-}

module Main (main) where

import Data.Graph.Inductive.Dot
import Data.Graph.Inductive.PatriciaTree
import NeuralNetwork2
import Data.Singletons
import GHC.TypeLits
import Data.Singletons.TypeLits
import Data.Singletons.Prelude.List

main :: IO ()
main =
  let
    s5 = sing :: SNat 5
    s6 = sing :: SNat 6
    s3 = sing :: SNat 3
    nn = makeNetwork s5 (SCons s6 SNil) s3
  in
    writeFile "file.dot" $ showDot (fglToDot $ (toFGL nn :: Gr String String))

