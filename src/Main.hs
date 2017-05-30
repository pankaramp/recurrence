{-# LANGUAGE DataKinds, NoMonomorphismRestriction, TypeOperators, TypeFamilies, FlexibleContexts, OverloadedStrings #-}

module Main (main) where

import Data.Array.Accelerate as A
import Data.Array.Accelerate.Interpreter as B
import Data.Graph.Inductive.Dot
import Data.Graph.Inductive.PatriciaTree
import NeuralNetwork2
import Data.Singletons
import GHC.TypeLits
import Data.Singletons.TypeLits
import Data.Singletons.Prelude.List
import ValueAndDerivative

import Data.Array.Accelerate.Debug
import System.Metrics
import System.Remote.Monitoring

main :: IO ()
main =
  let
    ir = [1, 1.1, 1.2]
    or = fmap Prelude.sin ir
    ia = (Prelude.map (A.use . A.fromList (Z:.1:.1) . (: [])) ir) :: [Acc (Matrix (Double))]
    oa = Prelude.map (A.map fromValue . A.use . A.fromList (Z:.1:.1) . (\a -> a : [])) or ::[Acc (Matrix (ValueAndDerivative Double))]
    i = Prelude.map (\a -> pSingleton2 s1 s1 a) ia
    s1 = sing :: SNat 1
    nn2 = makeNetwork s1 (SNil) s1 :: SomeNeuralNetwork Double 1 1
--    nn = makeNetwork s1 (SNil) s1 :: SomeNeuralNetwork (ValueAndDerivative Double) 1 1
    --p = forwardParams (lift (1.01 :: Double)) s1 s1 nn
    p = Prelude.last $ Prelude.take 3 $ gradientDescent 0.05 s1 s1 nn2 (mse oa) (Prelude.map pFlatten i) (NeuralNetwork2.initParams 0.5 nn2)
--    out = 
  in
    do
      store <- initAccMetrics
      registerGcMetrics store -- optional
      server <- forkServerWith store "localhost" 8001
      writeFile "file.dot" $ showDot (fglToDot $ (toFGL nn2 :: Gr Label Label))
      --print $ run $ A.zipWith (A.-) (gradient2 s1 s1 nn2 e (Prelude.map NeuralNetwork2.pFlatten i)) (gradient s1 s1 nn2 e (Prelude.map NeuralNetwork2.pFlatten i))
      print $ show $ p --forward s1 s1 nn2 f' (use p) (Prelude.map (\(PList _ a) -> a) i)
      --print $ show $ forward s1 s1 nn2 e (NeuralNetwork2.initParams 0.5 nn2) (Prelude.map NeuralNetwork2.flatten i)
