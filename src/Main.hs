{-# LANGUAGE DataKinds, NoMonomorphismRestriction, TypeOperators, TypeFamilies, FlexibleContexts, OverloadedStrings #-}

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

import Data.Array.Accelerate.Debug
import System.Metrics
import System.Remote.Monitoring

main :: IO ()
main =
  let
    ir = [1, 1.1..10]
    or = fmap Prelude.sin ir
    ia = (Prelude.map (A.use . A.fromList (Z:.1:.1) . (: [])) ir) :: [Acc (Matrix (Double))]
    oa = (A.map fromValue $ A.use $ A.fromList (Z:.(Prelude.length or)) or) :: Acc (Vector (ValueAndDerivative Double))
    i = Prelude.map (\a -> PCons s1 s1 a PNil) ia
    f = (\(PCons _ _ a PNil) -> reshape (index1 1) $ A.sum a) :: PList ('(1, 1) ': '[]) (ValueAndDerivative Double) -> Acc (Vector (ValueAndDerivative Double))
    f' = (A.sum . Prelude.foldr (A.++) (A.use $ A.fromList (Z:.0) [])) . (Prelude.map (\(PCons _ _ a PNil) -> reshape (index1 1) $ A.sum a)) :: [PList ('(1, 1) ': '[]) Double] -> Acc (Scalar Double)
    e = (A.map (\a -> a / (constant $ Prelude.fromIntegral $ Prelude.length or)) . A.sum . A.zipWith (\a b -> (a A.- b) * (a A.- b)) oa) . (Prelude.foldr (A.++) (A.use $ A.fromList (Z:.0) [])) . (Prelude.map f)
    s1 = sing :: SNat 1
    nn2 = makeNetwork s1 (SNil) s1 :: SomeNeuralNetwork Double 1 1
--    nn = makeNetwork s1 (SNil) s1 :: SomeNeuralNetwork (ValueAndDerivative Double) 1 1
    --p = forwardParams (lift (1.01 :: Double)) s1 s1 nn
    p = Prelude.last $ Prelude.take 20 $ gradientDescent 0.05 s1 s1 nn2 e (Prelude.map NeuralNetwork2.flatten i) (NeuralNetwork2.initParams 0.5 nn2)
--    out = 
  in
    do
      store <- initAccMetrics
      registerGcMetrics store -- optional
      server <- forkServerWith store "localhost" 8001
      writeFile "file.dot" $ showDot (fglToDot $ (toFGL nn2 :: Gr Label Label))
      --print $ run $ A.zipWith (A.-) (gradient2 s1 s1 nn2 e (Prelude.map NeuralNetwork2.flatten i)) (gradient s1 s1 nn e (Prelude.map NeuralNetwork2.flatten i))
      print $ show $ forward s1 s1 nn2 f' (use p) (Prelude.map NeuralNetwork2.flatten i)
      --print $ show $ forward s1 s1 nn2 e (NeuralNetwork2.initParams 0.5 nn2) (Prelude.map NeuralNetwork2.flatten i)
