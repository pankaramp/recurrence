{-# LANGUAGE DataKinds, NoMonomorphismRestriction, TypeOperators, TypeFamilies #-}

module Main (main) where

import Data.Graph.Inductive.Dot
import Data.Graph.Inductive.PatriciaTree
import NeuralNetwork
import Math
import Proofs
import Numeric.AD
import Data.Type.Equality
import Data.Singletons

eq :: SNat n -> SNat m -> n :~: m
eq SZ SZ = Refl
eq (SS n) (SS m) = gcastWith (eq n m) Refl

main :: IO ()
main =
  let
    (nn0, u, i) = NeuralNetwork.init (SS SZ)
    (nn1, o1) = lstmLayer (SS (SS (SS (SS (SS (SS SZ)))))) nn0 i u
    (nn2, o2) = lstmLayer (SS (SS (SS (SS (SS (SS SZ)))))) nn1 o1 u
    (nn, o) = lstmLayer (SS SZ) nn2 o2 u
--    (nn', o') = lstmNeuron nn (o `Cons` Nil) ZF
    ii = [1..100]
    x = fmap (\a -> ((a/100.0) `Cons` Nil)) ii :: [List (S Z) Double]
    y = fmap (\a -> (((1 + sin (a/50)) / 2) `Cons` Nil)) ii
    --dot = case nn of
      --NN n -> showDot (fglToDot $ (toFGL n :: Gr String ()))
  in
    do
--      print y
      case nn of
        NN n ->
          --print $ suffix (SS SZ) $ snd $ getStatesAndOutputs n
          case params n of
            (_, w, s, ps, SS SZ, o, po, _) ->
              print $ evalA n (zeroA $ toInt w) (zeroA $ toInt ps) (zeroA $ 1) (zeroA $ toInt po)
              {-gcastWith (eq o po) $
              withSingI (sPlus s (sPlus o w))$
              gcastWith (eq s ps) $
              withSingI s $
              withSingI o $
              withSingI w $-}
              --print $ Prelude.map (NeuralNetwork.error (SS SZ) (mse y) n x (zero, zero)) (take 10 $ gd (SS SZ) (mse y) n x (zero, zero) zero)
              --print $ NeuralNetwork.evaluate (SS SZ) n x (Prelude.last $ take 20 $ gd (SS SZ) (mse y) n x zero)
              --print $ Prelude.last $ take 2 $ gd (SS SZ) (mse y) n x (zero, zero) zero
      --writeFile "file.dot" dot
