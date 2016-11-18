{-# LANGUAGE DataKinds, KindSignatures, GADTs, TemplateHaskell #-}

module NeuralNetwork where

import Proofs
import Data.Singletons
import Data.Singletons.TH
import Data.Singletons.Prelude
import Data.Promotion.Prelude
import Math
import Data.Type.Equality

data NeuralNetwork (n :: Nat) a where
  Weight :: NeuralNetwork (S Z) a
  Input :: SNat i -> NeuralNetwork (S Z) a
  Output :: SNat i -> NeuralNetwork (S Z) a
  Union :: NeuralNetwork n a -> NeuralNetwork m a -> NeuralNetwork (Plus n m) a
  Operator :: NeuralNetwork k a -> DifferentiableFunction n a -> List n (Fin k) -> NeuralNetwork (S k) a

addWeight :: SNat n -> NeuralNetwork n a -> NeuralNetwork (S n) a
addWeight sn nn = gcastWith (commutativity sn (SS SZ)) (Union nn Weight)

addWeightedEdge :: Num a => SNat k -> NeuralNetwork k a -> Fin k -> (NeuralNetwork (S (S k)) a, Fin (S (S k)))
addWeightedEdge sk nn v =
  let
    nn' = addWeight sk nn
  in
    (
      Operator nn' (prod (SS (SS SZ))) ((gcastWith (minus_pred sk) $ weaken (SS sk) sk (SS SZ) v) `Cons` ((asFin sk) `Cons` Nil)),
      asFin (SS sk)
    )      

addWeightedEdges :: Num a => SNat k -> SNat n -> NeuralNetwork k a -> List n (Fin k) -> (NeuralNetwork (Plus n (Plus n k)) a, List n (Fin (Plus n (Plus n k))))
addWeightedEdges sk SZ nn Nil = (nn, Nil)
addWeightedEdges sk (SS sn) nn (h `Cons` t) =
  let
    (nn', v) = addWeightedEdge sk nn h
    (nn'', vs) = addWeightedEdges (SS (SS sk)) sn nn' (gcastWith (minus_pred_pred sk) $ gcastWith (minus_pred sk) $ weakenList (SS (SS sk)) sk (SS (SS SZ)) t)
  in
    (
      gcastWith (successor_of_sum sn sk) $
      gcastWith (successor_of_sum sn (SS (sk))) $
      gcastWith (successor_of_sum sn (SS (sPlus sn sk))) $
      nn'',
      (
        gcastWith (minus_plus' (sPlus sn sn) sk) $
        gcastWith (associativity (SS sn) (SS sn) sk) $
        gcastWith (commutativity sn (SS sn)) $
        gcastWith (minus_plus (sPlus sn sn) sk) $
        weaken (sPlus (SS sn) (sPlus (SS sn) sk)) (SS (SS sk)) (sPlus sn sn) v
      )
      `Cons`
      (
        gcastWith (successor_of_sum sn (SS sk)) $
        gcastWith (successor_of_sum sn sk) $
        gcastWith (successor_of_sum sn (SS (sPlus sn sk))) $
        vs
      )
    )

addInducedLocalField :: Num a => SNat k -> SNat n -> NeuralNetwork k a -> List n (Fin k) -> Fin k -> (NeuralNetwork (S (S (S (Plus n (Plus n k))))) a, Fin (S (S (S (Plus n (Plus n k))))))
addInducedLocalField sk sn nn vs o =
  let
    (nn', vs') = addWeightedEdges sk (SS sn) nn (o `Cons` vs)
  in
    (
      gcastWith (successor_of_sum sn (sPlus sn sk)) $
      (Operator nn' (Math.sum (SS sn)) vs', asFin (SS (SS (sPlus sn (sPlus sn sk)))))
    )

addProduct :: Num a => SNat k -> SNat n -> NeuralNetwork k a -> List n (Fin k) -> (NeuralNetwork (S k) a, Fin (S k))
addProduct sk sn nn vs = (Operator nn (prod sn) vs, asFin sk)

addSum :: Num a => SNat k -> SNat n -> NeuralNetwork k a -> List n (Fin k) -> (NeuralNetwork (S k) a, Fin (S k))
addSum sk sn nn vs = (Operator nn (Math.sum sn) vs, asFin sk)

addNeuron :: Num a => SNat k -> SNat n -> NeuralNetwork k a -> List n (Fin k) -> Fin k -> DifferentiableFunction (S Z) a -> (NeuralNetwork (S (S (S (S (Plus n (Plus n k)))))) a, Fin (S (S (S (S (Plus n (Plus n k)))))))
addNeuron sk sn nn vs o f =
  let
    (nn', v) = addInducedLocalField sk sn nn vs o
  in
    (Operator nn' f (v `Cons` Nil), asFin (SS (SS (SS (sPlus sn (sPlus sn sk))))))


addLSTMNeuron1 :: (Floating a) => SNat k -> SNat i -> NeuralNetwork k a -> List i (Fin k) -> Fin k -> Fin k -> Fin k -> (NeuralNetwork $(tksize 4 2) a, Fin $(tksize 16 8))
addLSTMNeuron1 sk si nn i o c u =
  let
    io = o `Cons` i
    sio = SS si
    (nn', v) = addNeuron sk sio nn io u sigm
  in
    (
      nn',
      $(weakenProof 4 1 $ [e|
      weaken $(ksize 16 8) $(ksize 4 2) $(iosize 12 6)
      v
      |])
    )

addLSTMNeuron2 :: (Floating a) => SNat k -> SNat i -> NeuralNetwork $(tksize 4 2) a -> List i (Fin k) -> Fin k -> Fin k -> Fin k -> (NeuralNetwork $(tksize 8 4) a, Fin $(tksize 16 8))
addLSTMNeuron2 sk si nn i o c u =
  let
    io = o `Cons` i
    sio = SS si
    sk' = (SS (SS (SS (SS (sPlus sio (sPlus sio sk))))))
    (io', u') =
      $(weakenProof 1 0 $ [e|
      (
        weakenList sk' sk $(iosize 4 2) io,
        weaken sk' sk $(iosize 4 2) u
      )|])      
    (nn', v) = addNeuron sk' sio nn io' u' sigm
  in
    (
      $(normalize 4 1 [e|nn'|]),
      $(weakenProof 4 2 $ normalize 4 1 [e| weaken $(ksize 16 8) $(ksize 8 4) $(iosize 8 4) v|])
    )

addLSTMNeuron3 :: (Floating a) => SNat k -> SNat i -> NeuralNetwork $(tksize 8 4) a -> List i (Fin k) -> Fin k -> Fin k -> Fin k -> (NeuralNetwork $(tksize 12 6) a, Fin $(tksize 16 8))
addLSTMNeuron3 sk si nn i o c u =
  let
    io = o `Cons` i
    sio = SS si
    sk' = $(ksize 8 4)
    (io', u') =
      $(weakenProof 2 0 [e|
      (
        weakenList sk' sk $(iosize 8 4) io,
        weaken sk' sk $(iosize 8 4) u
      )|])
    (nn', v) = addNeuron sk' sio nn io' u' sigm      
  in
    (
      $(normalize 4 2 [e|nn'|]),
      $(weakenProof 4 3 $ normalize 4 2 $ [e|weaken $(ksize 16 8) $(ksize 12 6) $(iosize 4 2) v|])
    )

addLSTMNeuron4 :: (Floating a) => SNat k -> SNat i -> NeuralNetwork $(tksize 12 6) a -> List i (Fin k) -> Fin k -> Fin k -> Fin k -> (NeuralNetwork $(tksize 16 8) a, Fin $(tksize 16 8))
addLSTMNeuron4 sk si nn i o c u =
  let
    io = o `Cons` i
    sio = SS si
    sk' = $(ksize 12 6)
    (io', u') =
      $(weakenProof 3 0 $ [e|
      (
        weakenList sk' sk $(iosize 12 6) io,
        weaken sk' sk $(iosize 12 6) u
      )|])
    (nn', v) = addNeuron sk' sio nn io' u' Math.tanh
  in
    $(normalize 4 3 $ [e|(nn', v)|])

addLSTMNeuron :: (Floating a) => SNat k -> SNat i -> NeuralNetwork k a -> List i (Fin k) -> Fin k -> Fin k -> Fin k -> (NeuralNetwork $(tksize 21 8) a, Fin $(tksize 21 8), Fin $(tksize 21 8))
addLSTMNeuron sk si nn i o c u =
  let
    sio = SS si
    sk' = $(ksize 16 8)
    cc = $(weakenProof 4 0 [e|weaken sk' sk $(iosize 16 8) c|])
    (nn', f) = addLSTMNeuron1 sk si nn i o c u
    (nn'', i') = addLSTMNeuron2 sk si nn' i o c u
    (nn''', t') = addLSTMNeuron3 sk si nn'' i o c u
    (nn'''', t) = addLSTMNeuron4 sk si nn''' i o c u
    (nn''''', t1) = addProduct sk' (SS (SS SZ)) nn'''' (f `Cons` (cc `Cons` Nil))
    (nn'''''', t2) = addProduct (SS sk') (SS (SS SZ)) nn''''' (weakenListOne sk' $ i' `Cons` (t `Cons` Nil))
    (nn''''''', c') = addSum (SS (SS sk')) (SS (SS SZ)) nn'''''' ((weakenOne (SS sk') t1) `Cons` (t2 `Cons` Nil))
    (nn'''''''', t3) = (Operator nn''''''' Math.tanh (c' `Cons` Nil), asFin (SS (SS (SS sk'))))
    (nnf, o') = addProduct (SS (SS (SS (SS sk')))) (SS (SS SZ)) nn'''''''' (t3 `Cons` ((weakenOne (SS (SS (SS sk'))) $ weakenOne (SS (SS sk')) $ weakenOne (SS sk') $ weakenOne sk' t') `Cons` Nil))
  in
    (nnf, weakenOne (SS (SS (SS (SS sk')))) $ weakenOne (SS (SS (SS sk'))) c', o')
