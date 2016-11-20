{-# LANGUAGE DataKinds, KindSignatures, GADTs, TemplateHaskell #-}

module NeuralNetwork(NeuralNetwork(..), toFGL, lstmNeuron, NeuralNetwork.nodes) where

import Proofs
import Data.Singletons
import Data.Singletons.TH
import Data.Singletons.Prelude
import Data.Promotion.Prelude
import Math
import Data.Type.Equality
import Data.Graph.Inductive

data NeuralNetwork (n :: Nat) (w :: Nat) (s :: Nat) (ps :: Nat) (i :: Nat) (o :: Nat) (po :: Nat) (u :: Nat) a where
  Unity :: NeuralNetwork (S Z) Z Z Z Z Z Z (S Z) a
  PreviousState :: NeuralNetwork (S Z) Z Z (S Z) Z Z Z Z a
  State :: NeuralNetwork (S Z) Z (S Z) Z Z Z Z Z a
  Weight :: NeuralNetwork (S Z) (S Z) Z Z Z Z Z Z a
  Input :: SNat i -> NeuralNetwork (S Z) Z Z Z (S Z) Z Z Z a
  PreviousOutput :: SNat i -> NeuralNetwork (S Z) Z Z Z Z Z (S Z) Z a
  Output :: SNat i -> NeuralNetwork (S Z) Z Z Z Z (S Z) Z Z a
  Union :: NeuralNetwork n w1 s1 ps1 i1 o1 po1 u1 a -> NeuralNetwork m w2 s2 ps2 i2 o2 po2 u2 a -> NeuralNetwork (Plus n m) (Plus w1 w2) (Plus s1 s2) (Plus ps1 ps2) (Plus i1 i2) (Plus o1 o2) (Plus po1 po2) (Plus u1 u2) a
  Operator :: NeuralNetwork k w s ps i o po u a -> DifferentiableFunction n a -> List n (Fin k) -> NeuralNetwork (S k) w s ps i o po u a

toFGL' :: DynGraph gr => gr String () -> NeuralNetwork n w s ps i o po u a -> gr String ()
toFGL' g Weight = ([], noNodes g, "W", []) & g
toFGL' g Unity = ([], noNodes g, "1", []) & g
toFGL' g State = ([], noNodes g, "S", []) & g
toFGL' g (Input l) = ([], noNodes g, "I" ++ show l, []) & g
toFGL' g (Output l) = ([], noNodes g, "O" ++ show l, []) & g
toFGL' g (Union nn1 nn2) = toFGL' (toFGL' g nn1) nn2
toFGL' g (Operator nn f l) =
  let
    (_, _, fl) = f
    l' = map (\v -> ((), fToInt v)) $ toList l
    g' = toFGL' g nn
  in
    (l', noNodes g', fl, []) & g'

toFGL :: DynGraph gr => NeuralNetwork n w s ps i o po u a -> gr String ()
toFGL = toFGL' empty

size :: SNat k -> NeuralNetwork k w s ps i o po u a -> SNat k
size s _ = s

nodes :: (SingI k) => NeuralNetwork k w s ps i o po u a -> Int
nodes nn = toInt $ NeuralNetwork.size sing nn

addWeight :: NeuralNetwork n w s ps i o po u a -> NeuralNetwork (S n) (S w) s ps i o po u a
addWeight nn = Union Weight nn

addWeightedEdge :: Num a => SNat k -> NeuralNetwork k w s ps i o po u a -> Fin k -> (NeuralNetwork (S (S k)) (S w) s ps i o po u a, Fin (S (S k)))
addWeightedEdge sk nn v =
  let
    nn' = addWeight nn
  in
    (
      Operator nn' (prod (SS (SS SZ))) ((gcastWith (minus_pred sk) $ weaken (SS sk) sk (SS SZ) v) `Cons` ((asFin sk) `Cons` Nil)),
      asFin (SS sk)
    )      

addWeightedEdges :: Num a => SNat k -> SNat w -> SNat n -> NeuralNetwork k w s ps i o po u a -> List n (Fin k) -> (NeuralNetwork (Plus n (Plus n k)) (Plus n w) s ps i o po u a, List n (Fin (Plus n (Plus n k))))
addWeightedEdges sk sw SZ nn Nil = (nn, Nil)
addWeightedEdges sk sw (SS sn) nn (h `Cons` t) =
  let
    (nn', v) = addWeightedEdge sk nn h
    (nn'', vs) = addWeightedEdges (SS (SS sk)) (SS sw) sn nn' (gcastWith (minus_pred_pred sk) $ gcastWith (minus_pred sk) $ weakenList (SS (SS sk)) sk (SS (SS SZ)) t)
  in
    (
      gcastWith (successor_of_sum sn sk) $
      gcastWith (successor_of_sum sn (SS (sk))) $
      gcastWith (successor_of_sum sn (SS (sPlus sn sk))) $
      gcastWith (successor_of_sum sn sw) $
      gcastWith (successor_of_sum sn (SS (sw))) $
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

addInducedLocalField :: Num a => SNat k -> SNat w -> SNat n -> NeuralNetwork k w s ps i o po u a -> List n (Fin k) -> Fin k -> (NeuralNetwork (S (S (S (Plus n (Plus n k))))) (S (Plus n w)) s ps i o po u a, Fin (S (S (S (Plus n (Plus n k))))))
addInducedLocalField sk sw sn nn vs o =
  let
    (nn', vs') = addWeightedEdges sk sw (SS sn) nn (o `Cons` vs)
  in
    (
      gcastWith (successor_of_sum sn (sPlus sn sk)) $
      (Operator nn' (Math.sum (SS sn)) vs', asFin (SS (SS (sPlus sn (sPlus sn sk)))))
    )

addProduct :: Num a => SNat k -> SNat n -> NeuralNetwork k w s ps i o po u a -> List n (Fin k) -> (NeuralNetwork (S k) w s ps i o po u a, Fin (S k))
addProduct sk sn nn vs = (Operator nn (prod sn) vs, asFin sk)

addSum :: Num a => SNat k -> SNat n -> NeuralNetwork k w s ps i o po u a -> List n (Fin k) -> (NeuralNetwork (S k) w s ps i o po u a, Fin (S k))
addSum sk sn nn vs = (Operator nn (Math.sum sn) vs, asFin sk)

addNeuron :: Num a => SNat k -> SNat w -> SNat n -> NeuralNetwork k w s ps i o po u a -> List n (Fin k) -> Fin k -> DifferentiableFunction (S Z) a -> (NeuralNetwork (S (S (S (S (Plus n (Plus n k)))))) (S (Plus n w)) s ps i o po u a, Fin (S (S (S (S (Plus n (Plus n k)))))))
addNeuron sk sw sn nn vs o f =
  let
    (nn', v) = addInducedLocalField sk sw sn nn vs o
  in
    (Operator nn' f (v `Cons` Nil), asFin (SS (SS (SS (sPlus sn (sPlus sn sk))))))


addLSTMNeuron1 :: (Floating a) => SNat k -> SNat w -> SNat i -> NeuralNetwork k w s ps ii o po u a -> List i (Fin k) -> Fin k -> Fin k -> Fin k -> (NeuralNetwork $(tksize 4 2) $(twsize 1 1) s ps ii o po u a, Fin $(tksize 16 8))
addLSTMNeuron1 sk sw si nn i o c u =
  let
    io = o `Cons` i
    sio = SS si
    (nn', v) = addNeuron sk sw sio nn io u sigm
  in
    (
      nn',
      $(weakenProof 4 1 $ [e|
      weaken $(ksize 16 8) $(ksize 4 2) $(iosize 12 6)
      v
      |])
    )

addLSTMNeuron2 :: (Floating a) => SNat k -> SNat w -> SNat i -> NeuralNetwork $(tksize 4 2) $(twsize 1 1) s ps ii o po u a -> List i (Fin k) -> Fin k -> Fin k -> Fin k -> (NeuralNetwork $(tksize 8 4) $(twsize 2 2) s ps ii o po u a, Fin $(tksize 16 8))
addLSTMNeuron2 sk sw si nn i o c u =
  let
    io = o `Cons` i
    sio = SS si
    sk' = $(ksize 4 2)
    (io', u') =
      $(weakenProof 1 0 $ [e|
      (
        weakenList sk' sk $(iosize 4 2) io,
        weaken sk' sk $(iosize 4 2) u
      )|])      
    (nn', v) = addNeuron sk' $(wsize 1 1) sio nn io' u' sigm
  in
    (
      $(normalize 4 1 $ normalizeW 4 1 [e|nn'|]),
      $(weakenProof 4 2 $ normalize 4 1 [e| weaken $(ksize 16 8) $(ksize 8 4) $(iosize 8 4) v|])
    )

addLSTMNeuron3 :: (Floating a) => SNat k -> SNat w -> SNat i -> NeuralNetwork $(tksize 8 4) $(twsize 2 2) s ps ii o po u a -> List i (Fin k) -> Fin k -> Fin k -> Fin k -> (NeuralNetwork $(tksize 12 6) $(twsize 3 3) s ps ii o po u a, Fin $(tksize 16 8))
addLSTMNeuron3 sk sw si nn i o c u =
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
    (nn', v) = addNeuron sk' $(wsize 2 2) sio nn io' u' sigm      
  in
    (
      $(normalize 4 2 $ normalizeW 4 2 [e|nn'|]),
      $(weakenProof 4 3 $ normalize 4 2 $ [e|weaken $(ksize 16 8) $(ksize 12 6) $(iosize 4 2) v|])
    )

addLSTMNeuron4 :: (Floating a) => SNat k -> SNat w -> SNat i -> NeuralNetwork $(tksize 12 6) $(twsize 3 3) s ps ii o po u a -> List i (Fin k) -> Fin k -> Fin k -> Fin k -> (NeuralNetwork $(tksize 16 8) $(twsize 4 4) s ps ii o po u a, Fin $(tksize 16 8))
addLSTMNeuron4 sk sw si nn i o c u =
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
    (nn', v) = addNeuron sk' $(wsize 3 3) sio nn io' u' Math.tanh
  in
    $(normalize 4 3 $ normalizeW 4 3 [e|(nn', v)|])

addLSTMNeuron :: (Floating a) => SNat k -> SNat w -> SNat i -> NeuralNetwork k w s ps ii o po u a -> List i (Fin k) -> Fin k -> Fin k -> Fin k -> (NeuralNetwork $(tksize 21 8) $(twsize 4 4) s ps ii o po u a, Fin $(tksize 21 8), Fin $(tksize 21 8))
addLSTMNeuron sk sw si nn i o c u =
  let
    sio = SS si
    sk' = $(ksize 16 8)
    cc = $(weakenProof 4 0 [e|weaken sk' sk $(iosize 16 8) c|])
    (nn', f) = addLSTMNeuron1 sk sw si nn i o c u
    (nn'', i') = addLSTMNeuron2 sk sw si nn' i o c u
    (nn''', t') = addLSTMNeuron3 sk sw si nn'' i o c u
    (nn'''', t) = addLSTMNeuron4 sk sw si nn''' i o c u
    (nn''''', t1) = addProduct sk' (SS (SS SZ)) nn'''' (f `Cons` (cc `Cons` Nil))
    (nn'''''', t2) = addProduct (SS sk') (SS (SS SZ)) nn''''' (weakenListOne sk' $ i' `Cons` (t `Cons` Nil))
    (nn''''''', c') = addSum (SS (SS sk')) (SS (SS SZ)) nn'''''' ((weakenOne (SS sk') t1) `Cons` (t2 `Cons` Nil))
    (nn'''''''', t3) = (Operator nn''''''' Math.tanh (c' `Cons` Nil), asFin (SS (SS (SS sk'))))
    (nnf, o') = addProduct (SS (SS (SS (SS sk')))) (SS (SS SZ)) nn'''''''' (t3 `Cons` ((weakenOne (SS (SS (SS sk'))) $ weakenOne (SS (SS sk')) $ weakenOne (SS sk') $ weakenOne sk' t') `Cons` Nil))
  in
    (nnf, weakenOne (SS (SS (SS (SS sk')))) $ weakenOne (SS (SS (SS sk'))) c', o')

lstmNeuron :: (Floating a, SingI k, SingI w, SingI i) => NeuralNetwork k w s ps ii o po u a -> List i (Fin k) -> Fin k -> Fin k -> Fin k -> (NeuralNetwork $(tksize 21 8) $(twsize 4 4) s ps ii o po u a, Fin $(tksize 21 8), Fin $(tksize 21 8))
lstmNeuron = addLSTMNeuron sing sing sing
