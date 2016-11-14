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

addNeuron :: Num a => SNat k -> SNat n -> NeuralNetwork k a -> List n (Fin k) -> Fin k -> DifferentiableFunction (S Z) a -> (NeuralNetwork (S (S (S (S (Plus n (Plus n k)))))) a, Fin (S (S (S (S (Plus n (Plus n k)))))))
addNeuron sk sn nn vs o f =
  let
    (nn', v) = addInducedLocalField sk sn nn vs o
  in
    (Operator nn' f (v `Cons` Nil), asFin (SS (SS (SS (sPlus sn (sPlus sn sk))))))


--b sio sk e = $(weakenProof 12 6 (ksize 0 2)) $ gcastWith ($(minusplus 12 6 (ksize 0 2))) $ e

addLSTMNeuron1 :: (Floating a) => SNat k -> SNat i -> NeuralNetwork k a -> List i (Fin k) -> Fin k -> Fin k -> Fin k -> (NeuralNetwork (S (S (S (S (Plus (S i) (Plus (S i) k)))))) a, Fin (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (Plus (S i) (Plus (S i) (Plus (S i) (Plus (S i) (Plus (S i) (Plus (S i) (Plus (S i) (Plus (S i) k)))))))))))))))))))))))))
addLSTMNeuron1 sk si nn i o c u =
  let
    io = o `Cons` i
    sio = SS si
    (nn', v) = addNeuron sk sio nn io u sigm
  in
    (
      nn',
      $(weakenProof 6 2 $ [e|
      weaken $(ksize 16 8) $(ksize 4 2) $(iosize 12 6)
      v
      |])
    )

addLSTMNeuron2 :: (Floating a) => SNat k -> SNat i -> NeuralNetwork (S (S (S (S (Plus (S i) (Plus (S i) k)))))) a -> List i (Fin k) -> Fin k -> Fin k -> Fin k -> (NeuralNetwork (S (S (S (S (S (S (S (S (Plus (S i) (Plus (S i) (Plus (S i) (Plus (S i) k)))))))))))) a, Fin (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (Plus (S i) (Plus (S i) (Plus (S i) (Plus (S i) (Plus (S i) (Plus (S i) (Plus (S i) (Plus (S i) k)))))))))))))))))))))))))
addLSTMNeuron2 sk si nn i o c u =
  let
    io = o `Cons` i
    sio = SS si
    sk' = (SS (SS (SS (SS (sPlus sio (sPlus sio sk))))))
    (io', u') =
      $(weakenProof 2 0 $ [e|
      (
        weakenList sk' sk (SS (SS (SS (SS (sPlus sio sio))))) io,
        weaken sk' sk (SS (SS (SS (SS (sPlus sio sio))))) u
      )|])      
    (nn', v) = addNeuron sk' sio nn io' u' sigm
  in
    (
      gcastWith (successor_of_sum sio (SS (SS (SS (sPlus sio (sPlus sio sk)))))) $
      gcastWith (successor_of_sum sio (SS (SS (sPlus sio (sPlus sio sk))))) $
      gcastWith (successor_of_sum sio (SS (sPlus sio (sPlus sio sk)))) $
      gcastWith (successor_of_sum sio (sPlus sio (sPlus sio sk))) $
      gcastWith (successor_of_sum sio (SS (SS (SS (sPlus sio (sPlus sio (sPlus sio sk))))))) $
      gcastWith (successor_of_sum sio (SS (SS (sPlus sio (sPlus sio (sPlus sio sk)))))) $
      gcastWith (successor_of_sum sio (SS (sPlus sio (sPlus sio (sPlus sio sk))))) $
      gcastWith (successor_of_sum sio (sPlus sio (sPlus sio (sPlus sio sk)))) $
      nn',
      gcastWith (associativity sio sio (sPlus sio (sPlus sio (sPlus sio (sPlus sio sk))))) $
      gcastWith (associativity sio (sPlus sio sio) (sPlus sio (sPlus sio (sPlus sio (sPlus sio sk))))) $
      gcastWith (associativity sio (sPlus sio (sPlus sio sio)) (sPlus sio (sPlus sio (sPlus sio (sPlus sio sk))))) $
      gcastWith (commutativity (sPlus sio (sPlus sio (sPlus sio sio))) (sPlus sio (sPlus sio (sPlus sio (sPlus sio sk))))) $
      gcastWith (successor_of_sum (SS (SS (SS (SS (sPlus sio (sPlus sio (sPlus sio (sPlus sio sk)))))))) (sPlus sio (sPlus sio (sPlus sio sio)))) $
      gcastWith (successor_of_sum (SS (SS (SS (SS (sPlus sio (sPlus sio (sPlus sio (sPlus sio sk)))))))) (SS (sPlus sio (sPlus sio (sPlus sio sio))))) $
      gcastWith (successor_of_sum (SS (SS (SS (SS (sPlus sio (sPlus sio (sPlus sio (sPlus sio sk)))))))) (SS (SS (sPlus sio (sPlus sio (sPlus sio sio)))))) $
      gcastWith (successor_of_sum (SS (SS (SS (SS (sPlus sio (sPlus sio (sPlus sio (sPlus sio sk)))))))) (SS (SS (SS (sPlus sio (sPlus sio (sPlus sio sio))))))) $
      gcastWith (successor_of_sum (SS (SS (SS (SS (sPlus sio (sPlus sio (sPlus sio (sPlus sio sk)))))))) (SS (SS (SS (SS (sPlus sio (sPlus sio (sPlus sio sio)))))))) $
      gcastWith (successor_of_sum (SS (SS (SS (SS (sPlus sio (sPlus sio (sPlus sio (sPlus sio sk)))))))) (SS (SS (SS (SS (SS (sPlus sio (sPlus sio (sPlus sio sio))))))))) $
      gcastWith (successor_of_sum (SS (SS (SS (SS (sPlus sio (sPlus sio (sPlus sio (sPlus sio sk)))))))) (SS (SS (SS (SS (SS (SS (sPlus sio (sPlus sio (sPlus sio sio)))))))))) $
      gcastWith (successor_of_sum (SS (SS (SS (SS (sPlus sio (sPlus sio (sPlus sio (sPlus sio sk)))))))) (SS (SS (SS (SS (SS (SS (SS (sPlus sio (sPlus sio (sPlus sio sio))))))))))) $
      gcastWith (minus_plus (SS (SS (SS (SS (SS (SS (SS (SS (sPlus sio (sPlus sio (sPlus sio (sPlus sio sk)))))))))))) (SS (SS (SS (SS (SS (SS (SS (SS (sPlus sio (sPlus sio (sPlus sio sio)))))))))))) $
      gcastWith (successor_of_sum sio (SS (SS (SS (sPlus sio (sPlus sio sk)))))) $
      gcastWith (successor_of_sum sio (SS (SS (sPlus sio (sPlus sio sk))))) $
      gcastWith (successor_of_sum sio (SS (sPlus sio (sPlus sio sk)))) $
      gcastWith (successor_of_sum sio (sPlus sio (sPlus sio sk))) $
      gcastWith (successor_of_sum sio (SS (SS (SS (sPlus sio (sPlus sio (sPlus sio sk))))))) $
      gcastWith (successor_of_sum sio (SS (SS (sPlus sio (sPlus sio (sPlus sio sk)))))) $
      gcastWith (successor_of_sum sio (SS (sPlus sio (sPlus sio (sPlus sio sk))))) $
      gcastWith (successor_of_sum sio (sPlus sio (sPlus sio (sPlus sio sk)))) $
      weaken
      (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (sPlus sio (sPlus sio (sPlus sio (sPlus sio (sPlus sio (sPlus sio (sPlus sio (sPlus sio sk))))))))))))))))))))))))
      (SS (SS (SS (SS (SS (SS (SS (SS (sPlus sio (sPlus sio (sPlus sio (sPlus sio sk))))))))))))
      (SS (SS (SS (SS (SS (SS (SS (SS (sPlus sio (sPlus sio (sPlus sio sio)))))))))))
      v
    )

addLSTMNeuron3 :: (Floating a) => SNat k -> SNat i -> NeuralNetwork (S (S (S (S (S (S (S (S (Plus (S i) (Plus (S i) (Plus (S i) (Plus (S i) k)))))))))))) a -> List i (Fin k) -> Fin k -> Fin k -> Fin k -> (NeuralNetwork (S (S (S (S (S (S (S (S (S (S (S (S (Plus (S i) (Plus (S i) (Plus (S i) (Plus (S i) (Plus (S i) (Plus (S i) k)))))))))))))))))) a, Fin (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (Plus (S i) (Plus (S i) (Plus (S i) (Plus (S i) (Plus (S i) (Plus (S i) (Plus (S i) (Plus (S i) k)))))))))))))))))))))))))
addLSTMNeuron3 sk si nn i o c u =
  let
    io = o `Cons` i
    sio = SS si
    sk' = (SS (SS (SS (SS (SS (SS (SS (SS (sPlus sio (sPlus sio (sPlus sio (sPlus sio sk))))))))))))
    (io', u') =
      $(weakenProof 4 0 [e|
      (
        weakenList sk' sk (SS (SS (SS (SS (SS (SS (SS (SS (sPlus sio (sPlus sio (sPlus sio sio))))))))))) io,
        weaken sk' sk (SS (SS (SS (SS (SS (SS (SS (SS (sPlus sio (sPlus sio (sPlus sio sio))))))))))) u
      )|])
    (nn', v) = addNeuron sk' sio nn io' u' sigm      
  in
    (
      gcastWith (successor_of_sum sio (SS (SS (SS (SS (SS (SS (SS (sPlus sio (sPlus sio (sPlus sio (sPlus sio sk)))))))))))) $
      gcastWith (successor_of_sum sio (SS (SS (SS (SS (SS (SS (sPlus sio (sPlus sio (sPlus sio (sPlus sio sk))))))))))) $
      gcastWith (successor_of_sum sio (SS (SS (SS (SS (SS (sPlus sio (sPlus sio (sPlus sio (sPlus sio sk)))))))))) $
      gcastWith (successor_of_sum sio (SS (SS (SS (SS (sPlus sio (sPlus sio (sPlus sio (sPlus sio sk))))))))) $
      gcastWith (successor_of_sum sio (SS (SS (SS (SS (SS (SS (SS (sPlus sio (sPlus sio (sPlus sio (sPlus sio (sPlus sio sk))))))))))))) $
      gcastWith (successor_of_sum sio (SS (SS (SS (SS (SS (SS (sPlus sio (sPlus sio (sPlus sio (sPlus sio (sPlus sio sk)))))))))))) $
      gcastWith (successor_of_sum sio (SS (SS (SS (SS (SS (sPlus sio (sPlus sio (sPlus sio (sPlus sio (sPlus sio sk))))))))))) $
      gcastWith (successor_of_sum sio (SS (SS (SS (SS (sPlus sio (sPlus sio (sPlus sio (sPlus sio (sPlus sio sk)))))))))) $
      gcastWith (successor_of_sum sio (SS (SS (SS (sPlus sio (sPlus sio (sPlus sio (sPlus sio sk)))))))) $
      gcastWith (successor_of_sum sio (SS (SS (sPlus sio (sPlus sio (sPlus sio (sPlus sio sk))))))) $
      gcastWith (successor_of_sum sio (SS (sPlus sio (sPlus sio (sPlus sio (sPlus sio sk)))))) $
      gcastWith (successor_of_sum sio (sPlus sio (sPlus sio (sPlus sio (sPlus sio sk))))) $
      gcastWith (successor_of_sum sio (SS (SS (SS (sPlus sio (sPlus sio (sPlus sio (sPlus sio (sPlus sio sk))))))))) $
      gcastWith (successor_of_sum sio (SS (SS (sPlus sio (sPlus sio (sPlus sio (sPlus sio (sPlus sio sk)))))))) $
      gcastWith (successor_of_sum sio (SS (sPlus sio (sPlus sio (sPlus sio (sPlus sio (sPlus sio sk))))))) $
      gcastWith (successor_of_sum sio (sPlus sio (sPlus sio (sPlus sio (sPlus sio (sPlus sio sk)))))) $
      nn',
      gcastWith (associativity sio sio (sPlus sio (sPlus sio (sPlus sio (sPlus sio (sPlus sio (sPlus sio sk))))))) $
      gcastWith (commutativity (sPlus sio sio) (sPlus sio (sPlus sio (sPlus sio (sPlus sio (sPlus sio (sPlus sio sk))))))) $
      gcastWith (successor_of_sum (sPlus sio (sPlus sio (sPlus sio (sPlus sio (sPlus sio (sPlus sio sk)))))) (sPlus sio sio)) $
      gcastWith (successor_of_sum (sPlus sio (sPlus sio (sPlus sio (sPlus sio (sPlus sio (sPlus sio sk)))))) (SS (sPlus sio sio))) $
      gcastWith (successor_of_sum (sPlus sio (sPlus sio (sPlus sio (sPlus sio (sPlus sio (sPlus sio sk)))))) (SS (SS (sPlus sio sio)))) $
      gcastWith (successor_of_sum (sPlus sio (sPlus sio (sPlus sio (sPlus sio (sPlus sio (sPlus sio sk)))))) (SS (SS (SS (sPlus sio sio))))) $
      gcastWith (minus_plus (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (sPlus sio (sPlus sio (sPlus sio (sPlus sio (sPlus sio (sPlus sio sk)))))))))))))))))) (SS (SS (SS (SS (sPlus sio sio)))))) $
      gcastWith (successor_of_sum sio (SS (SS (SS (SS (SS (SS (SS (sPlus sio (sPlus sio (sPlus sio (sPlus sio sk)))))))))))) $
      gcastWith (successor_of_sum sio (SS (SS (SS (SS (SS (SS (sPlus sio (sPlus sio (sPlus sio (sPlus sio sk))))))))))) $
      gcastWith (successor_of_sum sio (SS (SS (SS (SS (SS (sPlus sio (sPlus sio (sPlus sio (sPlus sio sk)))))))))) $
      gcastWith (successor_of_sum sio (SS (SS (SS (SS (sPlus sio (sPlus sio (sPlus sio (sPlus sio sk))))))))) $
      gcastWith (successor_of_sum sio (SS (SS (SS (SS (SS (SS (SS (sPlus sio (sPlus sio (sPlus sio (sPlus sio (sPlus sio sk))))))))))))) $
      gcastWith (successor_of_sum sio (SS (SS (SS (SS (SS (SS (sPlus sio (sPlus sio (sPlus sio (sPlus sio (sPlus sio sk)))))))))))) $
      gcastWith (successor_of_sum sio (SS (SS (SS (SS (SS (sPlus sio (sPlus sio (sPlus sio (sPlus sio (sPlus sio sk))))))))))) $
      gcastWith (successor_of_sum sio (SS (SS (SS (SS (sPlus sio (sPlus sio (sPlus sio (sPlus sio (sPlus sio sk)))))))))) $
      gcastWith (successor_of_sum sio (SS (SS (SS (sPlus sio (sPlus sio (sPlus sio (sPlus sio sk)))))))) $
      gcastWith (successor_of_sum sio (SS (SS (sPlus sio (sPlus sio (sPlus sio (sPlus sio sk))))))) $
      gcastWith (successor_of_sum sio (SS (sPlus sio (sPlus sio (sPlus sio (sPlus sio sk)))))) $
      gcastWith (successor_of_sum sio (sPlus sio (sPlus sio (sPlus sio (sPlus sio sk))))) $
      gcastWith (successor_of_sum sio (SS (SS (SS (sPlus sio (sPlus sio (sPlus sio (sPlus sio (sPlus sio sk))))))))) $
      gcastWith (successor_of_sum sio (SS (SS (sPlus sio (sPlus sio (sPlus sio (sPlus sio (sPlus sio sk)))))))) $
      gcastWith (successor_of_sum sio (SS (sPlus sio (sPlus sio (sPlus sio (sPlus sio (sPlus sio sk))))))) $
      gcastWith (successor_of_sum sio (sPlus sio (sPlus sio (sPlus sio (sPlus sio (sPlus sio sk)))))) $
      weaken
      (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (sPlus sio (sPlus sio (sPlus sio (sPlus sio (sPlus sio (sPlus sio (sPlus sio (sPlus sio sk))))))))))))))))))))))))
      (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (sPlus sio (sPlus sio (sPlus sio (sPlus sio (sPlus sio (sPlus sio sk))))))))))))))))))
      (SS (SS (SS (SS (sPlus sio sio)))))
      v
    )

addLSTMNeuron4 :: (Floating a) => SNat k -> SNat i -> NeuralNetwork (S (S (S (S (S (S (S (S (S (S (S (S (Plus (S i) (Plus (S i) (Plus (S i) (Plus (S i) (Plus (S i) (Plus (S i) k)))))))))))))))))) a -> List i (Fin k) -> Fin k -> Fin k -> Fin k -> (NeuralNetwork (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (Plus (S i) (Plus (S i) (Plus (S i) (Plus (S i) (Plus (S i) (Plus (S i) (Plus (S i) (Plus (S i) k)))))))))))))))))))))))) a, Fin (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (Plus (S i) (Plus (S i) (Plus (S i) (Plus (S i) (Plus (S i) (Plus (S i) (Plus (S i) (Plus (S i) k)))))))))))))))))))))))))
addLSTMNeuron4 sk si nn i o c u =
  let
    io = o `Cons` i
    sio = SS si
    sk' = (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (sPlus sio (sPlus sio (sPlus sio (sPlus sio (sPlus sio (sPlus sio sk))))))))))))))))))
    (io', u') =
      gcastWith (associativity sio sio sk) $
      gcastWith (associativity sio (sPlus sio sio) sk) $
      gcastWith (associativity sio (sPlus sio (sPlus sio sio)) sk) $
      gcastWith (associativity sio (sPlus sio (sPlus sio (sPlus sio sio))) sk) $
      gcastWith (associativity sio (sPlus sio (sPlus sio (sPlus sio (sPlus sio sio)))) sk) $
      gcastWith (commutativity (sPlus sio (sPlus sio (sPlus sio (sPlus sio (sPlus sio sio))))) sk) $
      gcastWith (successor_of_sum sk (sPlus sio (sPlus sio (sPlus sio (sPlus sio (sPlus sio sio)))))) $
      gcastWith (successor_of_sum sk (SS (sPlus sio (sPlus sio (sPlus sio (sPlus sio (sPlus sio sio))))))) $
      gcastWith (successor_of_sum sk (SS (SS (sPlus sio (sPlus sio (sPlus sio (sPlus sio (sPlus sio sio)))))))) $
      gcastWith (successor_of_sum sk (SS (SS (SS (sPlus sio (sPlus sio (sPlus sio (sPlus sio (sPlus sio sio))))))))) $
      gcastWith (successor_of_sum sk (SS (SS (SS (SS (sPlus sio (sPlus sio (sPlus sio (sPlus sio (sPlus sio sio)))))))))) $
      gcastWith (successor_of_sum sk (SS (SS (SS (SS (SS (sPlus sio (sPlus sio (sPlus sio (sPlus sio (sPlus sio sio))))))))))) $
      gcastWith (successor_of_sum sk (SS (SS (SS (SS (SS (SS (sPlus sio (sPlus sio (sPlus sio (sPlus sio (sPlus sio sio)))))))))))) $
      gcastWith (successor_of_sum sk (SS (SS (SS (SS (SS (SS (SS (sPlus sio (sPlus sio (sPlus sio (sPlus sio (sPlus sio sio))))))))))))) $
      gcastWith (successor_of_sum sk (SS (SS (SS (SS (SS (SS (SS (SS (sPlus sio (sPlus sio (sPlus sio (sPlus sio (sPlus sio sio)))))))))))))) $
      gcastWith (successor_of_sum sk (SS (SS (SS (SS (SS (SS (SS (SS (SS (sPlus sio (sPlus sio (sPlus sio (sPlus sio (sPlus sio sio))))))))))))))) $
      gcastWith (successor_of_sum sk (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (sPlus sio (sPlus sio (sPlus sio (sPlus sio (sPlus sio sio)))))))))))))))) $
      gcastWith (successor_of_sum sk (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (sPlus sio (sPlus sio (sPlus sio (sPlus sio (sPlus sio sio))))))))))))))))) $
      gcastWith (minus_plus sk (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (sPlus sio (sPlus sio (sPlus sio (sPlus sio (sPlus sio sio)))))))))))))))))) $
      (
        weakenList sk' sk (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (sPlus sio (sPlus sio (sPlus sio (sPlus sio (sPlus sio sio))))))))))))))))) io,
        weaken sk' sk (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (sPlus sio (sPlus sio (sPlus sio (sPlus sio (sPlus sio sio))))))))))))))))) u
      )
    (nn', v) = addNeuron sk' sio nn io' u' Math.tanh
  in
    gcastWith (successor_of_sum sio (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (sPlus sio (sPlus sio (sPlus sio (sPlus sio (sPlus sio (sPlus sio sk)))))))))))))))))) $
    gcastWith (successor_of_sum sio (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (sPlus sio (sPlus sio (sPlus sio (sPlus sio (sPlus sio (sPlus sio sk))))))))))))))))) $
    gcastWith (successor_of_sum sio (SS (SS (SS (SS (SS (SS (SS (SS (SS (sPlus sio (sPlus sio (sPlus sio (sPlus sio (sPlus sio (sPlus sio sk)))))))))))))))) $
    gcastWith (successor_of_sum sio (SS (SS (SS (SS (SS (SS (SS (SS (sPlus sio (sPlus sio (sPlus sio (sPlus sio (sPlus sio (sPlus sio sk))))))))))))))) $
    gcastWith (successor_of_sum sio (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (sPlus sio (sPlus sio (sPlus sio (sPlus sio (sPlus sio (sPlus sio (sPlus sio sk))))))))))))))))))) $
    gcastWith (successor_of_sum sio (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (sPlus sio (sPlus sio (sPlus sio (sPlus sio (sPlus sio (sPlus sio (sPlus sio sk)))))))))))))))))) $
    gcastWith (successor_of_sum sio (SS (SS (SS (SS (SS (SS (SS (SS (SS (sPlus sio (sPlus sio (sPlus sio (sPlus sio (sPlus sio (sPlus sio (sPlus sio sk))))))))))))))))) $
    gcastWith (successor_of_sum sio (SS (SS (SS (SS (SS (SS (SS (SS (sPlus sio (sPlus sio (sPlus sio (sPlus sio (sPlus sio (sPlus sio (sPlus sio sk)))))))))))))))) $
    gcastWith (successor_of_sum sio (SS (SS (SS (SS (SS (SS (SS (sPlus sio (sPlus sio (sPlus sio (sPlus sio (sPlus sio (sPlus sio sk)))))))))))))) $
    gcastWith (successor_of_sum sio (SS (SS (SS (SS (SS (SS (sPlus sio (sPlus sio (sPlus sio (sPlus sio (sPlus sio (sPlus sio sk))))))))))))) $
    gcastWith (successor_of_sum sio (SS (SS (SS (SS (SS (sPlus sio (sPlus sio (sPlus sio (sPlus sio (sPlus sio (sPlus sio sk)))))))))))) $
    gcastWith (successor_of_sum sio (SS (SS (SS (SS (sPlus sio (sPlus sio (sPlus sio (sPlus sio (sPlus sio (sPlus sio sk))))))))))) $
    gcastWith (successor_of_sum sio (SS (SS (SS (SS (SS (SS (SS (sPlus sio (sPlus sio (sPlus sio (sPlus sio (sPlus sio (sPlus sio (sPlus sio sk))))))))))))))) $
    gcastWith (successor_of_sum sio (SS (SS (SS (SS (SS (SS (sPlus sio (sPlus sio (sPlus sio (sPlus sio (sPlus sio (sPlus sio (sPlus sio sk)))))))))))))) $
    gcastWith (successor_of_sum sio (SS (SS (SS (SS (SS (sPlus sio (sPlus sio (sPlus sio (sPlus sio (sPlus sio (sPlus sio (sPlus sio sk))))))))))))) $
    gcastWith (successor_of_sum sio (SS (SS (SS (SS (sPlus sio (sPlus sio (sPlus sio (sPlus sio (sPlus sio (sPlus sio (sPlus sio sk)))))))))))) $
    gcastWith (successor_of_sum sio (SS (SS (SS (sPlus sio (sPlus sio (sPlus sio (sPlus sio (sPlus sio (sPlus sio sk)))))))))) $
    gcastWith (successor_of_sum sio (SS (SS (sPlus sio (sPlus sio (sPlus sio (sPlus sio (sPlus sio (sPlus sio sk))))))))) $
    gcastWith (successor_of_sum sio (SS (sPlus sio (sPlus sio (sPlus sio (sPlus sio (sPlus sio (sPlus sio sk)))))))) $
    gcastWith (successor_of_sum sio (sPlus sio (sPlus sio (sPlus sio (sPlus sio (sPlus sio (sPlus sio sk))))))) $
    gcastWith (successor_of_sum sio (SS (SS (SS (sPlus sio (sPlus sio (sPlus sio (sPlus sio (sPlus sio (sPlus sio (sPlus sio sk))))))))))) $
    gcastWith (successor_of_sum sio (SS (SS (sPlus sio (sPlus sio (sPlus sio (sPlus sio (sPlus sio (sPlus sio (sPlus sio sk)))))))))) $
    gcastWith (successor_of_sum sio (SS (sPlus sio (sPlus sio (sPlus sio (sPlus sio (sPlus sio (sPlus sio (sPlus sio sk))))))))) $
    gcastWith (successor_of_sum sio (sPlus sio (sPlus sio (sPlus sio (sPlus sio (sPlus sio (sPlus sio (sPlus sio sk)))))))) $
    (nn', v)

{-addLSTMNeuron :: (Floating a) => SNat k -> SNat i -> NeuralNetwork k a -> List i (Fin k) -> Fin k -> Fin k -> Fin k -> NeuralNetwork (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (Plus (S i) (Plus (S i) (Plus (S i) (Plus (S i) (Plus (S i) (Plus (S i) (Plus (S i) (Plus (S i) k)))))))))))))))))))))))) a
addLSTMNeuron sk si nn i o c u =
  let
    sio = SS si
    sk' = (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (sPlus sio (sPlus sio (sPlus sio (sPlus sio (sPlus sio (sPlus sio (sPlus sio (sPlus sio sk))))))))))))))))))))))))
    cc =
      gcastWith (associativity sio sio sk) $
      gcastWith (associativity sio (sPlus sio sio) sk) $
      gcastWith (associativity sio (sPlus sio (sPlus sio sio)) sk) $
      gcastWith (associativity sio (sPlus sio (sPlus sio (sPlus sio sio))) sk) $
      gcastWith (associativity sio (sPlus sio (sPlus sio (sPlus sio (sPlus sio sio)))) sk) $
      gcastWith (associativity sio (sPlus sio (sPlus sio (sPlus sio (sPlus sio (sPlus (sio sio)))))) sk) $
      gcastWith (associativity sio (sPlus sio (sPlus sio (sPlus sio (sPlus sio (sPlus (sio (sPlus (sio sio)))))) sk) $
      gcastWith (associativity sio (sPlus sio (sPlus sio (sPlus sio (sPlus sio (sPlus (sio (sPlus (sio (sPlus (sio sio)))))) sk) $
      gcastWith (associativity sio (sPlus sio (sPlus sio (sPlus sio (sPlus sio (sPlus (sio (sPlus (sio (sPlus (sio (sPlus (sio sio)))))) sk) $
      gcastWith (associativity sio (sPlus sio (sPlus sio (sPlus sio (sPlus sio (sPlus (sio (sPlus (sio (sPlus (sio (sPlus (sio (sPlus (sio sio)))))) sk) $
      gcastWith (associativity sio (sPlus sio (sPlus sio (sPlus sio (sPlus sio (sPlus (sio (sPlus (sio (sPlus (sio (sPlus (sio (sPlus (sio (sPlus (sio sio)))))) sk) $
      gcastWith (associativity sio (sPlus sio (sPlus sio (sPlus (sio (sPlus (sio (sPlus (sio (sPlus (sio (sPlus (sio (sPlus (sio (sPlus sio (sPlus sio (sPlus (sio sio)))))) sk) $      
      gcastWith (commutativity (sPlus sio (sPlus sio (sPlus sio (sPlus sio (sPlus sio sio))))) sk) $
      weaken sk' sk (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (sPlus sio (sPlus sio (sPlus sio (sPlus sio (sPlus sio (sPlus sio (sPlus sio (sPlus sio sio)))))))))))))))))))))))) c
    (nn', f) = addLSTMNeuron1 sk si nn i o c u
    (nn'', i') = addLSTMNeuron2 sk si nn' i o c u
    (nn''', o') = addLSTMNeuron3 sk si nn'' i o c u
    (nn'''', c') = addLSTMNeuron4 sk si nn''' i o c u
    (nn''''', t1) = addProduct sk' (SS (SS SZ)) nn'''' (f `Cons` (cc `Cons` Nil))
  in
    nn''''-}
