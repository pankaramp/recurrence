{-# LANGUAGE DataKinds, KindSignatures, GADTs, TemplateHaskell, ScopedTypeVariables, FlexibleContexts, Rank2Types #-}

module NeuralNetwork(NeuralNetwork(..), toFGL, lstmNeuron, NeuralNetwork.params, NeuralNetwork.init, gd, mse, zero, lstmLayer, NN(..)) where

import Proofs
import Data.Singletons
import Data.Singletons.TH
import Data.Singletons.Prelude
import Data.Promotion.Prelude
import Math
import Data.Maybe
import Data.Type.Equality
import Data.Graph.Inductive
import Numeric.AD
import qualified Numeric.AD.Internal.Reverse as R
import qualified Data.Reflection as Ref
import Numeric.AD.Newton hiding (eval)

data NN a where
  NN :: forall a (n :: Nat) (w :: Nat) (s :: Nat) (ps :: Nat) (i :: Nat) (o :: Nat) (po :: Nat) (u :: Nat) . NeuralNetwork n w s ps i o po u a -> NN a

data L a where
    L :: forall a (n :: Nat)  . List n a -> L a

data NeuralNetwork (n :: Nat) (w :: Nat) (s :: Nat) (ps :: Nat) (i :: Nat) (o :: Nat) (po :: Nat) (u :: Nat) a where
  Empty :: NeuralNetwork Z Z Z Z Z Z Z Z a
  Unity :: NeuralNetwork (S Z) Z Z Z Z Z Z (S Z) a
  PreviousState :: NeuralNetwork (S Z) Z Z (S Z) Z Z Z Z a
  State :: NeuralNetwork k w s ps i o po u a -> Fin k -> NeuralNetwork (S k) w (S s) ps i o po u a
  Weight :: NeuralNetwork (S Z) (S Z) Z Z Z Z Z Z a
  Input :: NeuralNetwork (S Z) Z Z Z (S Z) Z Z Z a
  PreviousOutput :: NeuralNetwork (S Z) Z Z Z Z Z (S Z) Z a
  Output :: NeuralNetwork k w s ps i o po u a -> Fin k -> NeuralNetwork (S k) w s ps i (S o) po u a
  Union :: NeuralNetwork n w1 s1 ps1 i1 o1 po1 u1 a -> NeuralNetwork m w2 s2 ps2 i2 o2 po2 u2 a -> NeuralNetwork (Plus n m) (Plus w1 w2) (Plus s1 s2) (Plus ps1 ps2) (Plus i1 i2) (Plus o1 o2) (Plus po1 po2) (Plus u1 u2) a
  Operator :: NeuralNetwork k w s ps i o po u a -> DifferentiableFunction n a -> List n (Fin k) -> NeuralNetwork (S k) w s ps i o po u a

params :: NeuralNetwork k w s ps i o po u a -> (SNat k, SNat w, SNat s, SNat ps, SNat i, SNat o, SNat po, SNat u)
params Empty = (SZ, SZ, SZ, SZ, SZ, SZ, SZ, SZ)
params Unity = (SS SZ, SZ, SZ, SZ, SZ, SZ, SZ, SS SZ)
params Weight = (SS SZ, SS SZ, SZ, SZ, SZ, SZ, SZ, SZ)
params (State nn _) =
  let
    (k, w, s, ps, i, o, po, u) = params nn
  in
    (SS k, w, SS s, ps, i, o, po, u)
params Input = (SS SZ, SZ, SZ, SZ, SS SZ, SZ, SZ, SZ)
params PreviousState = (SS SZ, SZ, SZ, SS SZ, SZ, SZ, SZ, SZ)
params PreviousOutput = (SS SZ, SZ, SZ, SZ, SZ, SZ, SS SZ, SZ)
params (Output nn _) =
  let
    (k, w, s, ps, i, o, po, u) = params nn
  in
    (SS k, w, s, ps, i, SS o, po, u)
params (Union nn1 nn2) =
  let
    (k1, w1, s1, ps1, i1, o1, po1, u1) = params nn1
    (k2, w2, s2, ps2, i2, o2, po2, u2) = params nn2
  in
    (sPlus k1 k2, sPlus w1 w2, sPlus s1 s2, sPlus ps1 ps2, sPlus i1 i2, sPlus o1 o2, sPlus po1 po2, sPlus u1 u2)
params (Operator nn _ _) =
  let
    (k, w, s, ps, i, o, po, u) = params nn
  in
    (SS k, w, s, ps, i, o, po, u)

size nn =
  let
    (k, _, _, _, _, _, _, _) = params nn
  in
    k

toFGL' :: DynGraph gr => gr String () -> NeuralNetwork n w s ps i o po u a -> gr String ()
toFGL' g Empty = g
toFGL' g Weight = ([], noNodes g, "W", []) & g
toFGL' g PreviousState = ([], noNodes g, "PS", []) & g
toFGL' g PreviousOutput = ([], noNodes g, "PO", []) & g
toFGL' g Unity = ([], noNodes g, "1", []) & g
toFGL' g (State nn f) = ([((), fToInt f)], noNodes (toFGL' g nn), "S", []) & (toFGL' g nn)
toFGL' g Input = ([], noNodes g, "I", []) & g
toFGL' g (Output nn f) = ([((), fToInt f)], noNodes (toFGL' g nn), "O", []) & (toFGL' g nn)
toFGL' g (Union nn1 nn2) = toFGL' (toFGL' g nn1) nn2
toFGL' g (Operator nn f l) =
  let
    (_, _, fl) = f
    l' = Prelude.map (\v -> ((), fToInt v)) $ toList l
    g' = toFGL' g nn
  in
    (l', noNodes g', fl, []) & g'

toFGL :: DynGraph gr => NeuralNetwork n w s ps i o po u a -> gr String ()
toFGL = toFGL' empty

addWeight :: NeuralNetwork n w s ps i o po u a -> NeuralNetwork (S n) (S w) s ps i o po u a
addWeight nn =
  let
    (k, w, s, ps, ii, o, po, u) = params nn
  in
    gcastWith (commutativity k (SS SZ)) $
    gcastWith (commutativity w (SS SZ)) $
    gcastWith (commutativity s SZ) $
    gcastWith (commutativity ps SZ) $
    gcastWith (commutativity ii SZ) $
    gcastWith (commutativity o SZ) $
    gcastWith (commutativity po SZ) $
    gcastWith (commutativity u SZ) $
    Union nn Weight

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

lstmNeuron1 :: (Floating a) => NeuralNetwork k w s ps ii o po u a -> NeuralNetwork (S (S k)) w s (S ps) ii o (S po) u a
lstmNeuron1 nn =
  let
    (k, w, s, ps, ii, o, po, u) = params nn
  in
    gcastWith (commutativity k (SS (SS SZ))) $
    gcastWith (commutativity w SZ) $
    gcastWith (commutativity s SZ) $
    gcastWith (commutativity ps (SS SZ)) $
    gcastWith (commutativity ii SZ) $
    gcastWith (commutativity o SZ) $
    gcastWith (commutativity po (SS SZ)) $
    gcastWith (commutativity u SZ) $
    Union nn (Union PreviousOutput PreviousState)

lstmNeuron2 :: (Floating a) => NeuralNetwork (S (S k)) w s (S ps) ii o (S po) u a -> List i (Fin k) -> Fin k -> (NeuralNetwork $(tksize 23 8) $(twsize 4 4) s (S ps) ii o (S po) u a, Fin $(tksize 23 8), Fin $(tksize 23 8))
lstmNeuron2 nn' i u =
  let
    (sk', w, _, _, _, _, _, _) = params nn'
    sk = (sPred (sPred sk'))
    si = Math.length i
    sio = SS si
    o = weakenOne (SS sk) $ asFin sk
    c = asFin (SS sk)
    (nn'', o', c') = addLSTMNeuron (SS (SS sk)) w si nn' (weakenListOne (SS sk) $ weakenListOne sk i) o c (weakenOne (SS sk) $ weakenOne sk u)
  in
    $(normalize' 2 8 [e|(nn'', o', c')|])

lstmNeuron :: (Floating a) => NeuralNetwork k w s ps ii o po u a -> List i (Fin k) -> Fin k -> (NeuralNetwork $(tksize 25 8) $(twsize 4 4) (S s) (S ps) ii (S o) (S po) u a, Fin $(tksize 25 8))
lstmNeuron nn i u =
  let
    (sk, w, _, _, _, _, _, _) = params nn
    nn' =  lstmNeuron1 nn
    si = Math.length i
    sio = SS si
    o = weakenOne (SS sk) $ asFin sk
    c = asFin (SS sk)
    (nn'', o', c') = lstmNeuron2 nn' i u
    nn''' = Output (State nn'' c') (weakenOne $(ksize 23 8) o')
  in
    (nn''', weakenOne $(ksize 24 8) $ weakenOne $(ksize 23 8) o')

eval' :: (Num a) => NeuralNetwork n w s ps i o po u a -> List w a -> List ps a -> List po a -> List i a -> List n (Maybe a) -> List n a
eval' Empty Nil Nil Nil Nil Nil = Nil
eval' _ _ _ _ _ l@(_ `Cons` _) | isJust $ Math.last l = Math.map fromJust l
eval' Unity Nil Nil Nil Nil (Nothing `Cons` Nil) = 1 `Cons` Nil
eval' Weight (v `Cons` Nil) Nil Nil Nil (Nothing `Cons` Nil) = (v `Cons` Nil)
eval' PreviousState Nil (v `Cons` Nil) Nil Nil (Nothing `Cons` Nil) = (v `Cons` Nil)
eval' PreviousOutput Nil Nil (v `Cons` Nil) Nil (Nothing `Cons` Nil) = (v `Cons` Nil)
eval' Input Nil Nil Nil (v `Cons` Nil) (Nothing `Cons` Nil) = (v `Cons` Nil)
eval' (Output nn f) ws pss pos is ns =
  let
    ns' = Math.reverse $ Math.tail $ Math.reverse ns
    r = eval' nn ws pss pos is ns'
    rr = Math.element f r
    rrr = rr `Cons` Nil
  in
    gcastWith (commutativity (Math.length r) (SS SZ)) $ Math.conc r rrr
eval' (State nn f) ws pss pos is ns =
  let
    ns' = Math.reverse $ Math.tail $ Math.reverse ns
    r = eval' nn ws pss pos is ns'
    rr = Math.element f r
    rrr = rr `Cons` Nil
  in
    gcastWith (commutativity (Math.length r) (SS SZ)) $ Math.conc r rrr
eval' (Union nn1 nn2) ws pss pos is ns =
  let
    (k1, w1, s1, ps1, i1, o1, po1, u1) = params nn1
    (k2, w2, s2, ps2, i2, o2, po2, u2) = params nn2
    (wa, wb) = split w1 w2 ws
    (psa, psb) = split ps1 ps2 pss
    (poa, pob) = split po1 po2 pos
    (ia, ib) = split i1 i2 is
    (na, nb) = split k1 k2 ns
    r1 = eval' nn1 wa psa poa ia na
    r2 = eval' nn2 wb psb pob ib nb
  in
    Math.conc r1 r2
eval' (Operator nn (f, _, _) xs) ws pss pos is ns =
  let
    ns' = Math.reverse $ Math.tail $ Math.reverse ns
    r = eval' nn ws pss pos is ns'
    rr = Math.map (\l -> Math.element l r) xs
    rrr = (f rr) `Cons` Nil
  in
    gcastWith (commutativity (Math.length r) (SS SZ)) $ Math.conc r rrr

conc' :: List n a -> List m a -> List (Plus m n) a
conc' x y = gcastWith (commutativity (Math.length x) (Math.length y)) $ conc x y

getStatesAndOutputs :: NeuralNetwork n w s ps i o po u a -> (List s (Fin n), List o (Fin n))
getStatesAndOutputs Empty = (Nil, Nil)
getStatesAndOutputs (State nn f) =
  let
    (sss, ooo) = getStatesAndOutputs nn
  in
    (weakenListOne (NeuralNetwork.size nn) $ conc' sss (f `Cons` Nil), weakenListOne (NeuralNetwork.size nn) ooo)
getStatesAndOutputs (Output nn f) =
  let
    (sss, ooo) = getStatesAndOutputs nn
  in
    (weakenListOne (NeuralNetwork.size nn) sss, weakenListOne (NeuralNetwork.size nn) $ conc' ooo (f `Cons` Nil))
getStatesAndOutputs (Operator nn _ _) =
  let
    (sss, ooo) = getStatesAndOutputs nn
  in
    (weakenListOne (NeuralNetwork.size nn) sss, weakenListOne (NeuralNetwork.size nn) ooo)
getStatesAndOutputs (Union nn1 nn2) =
  let
    k1 = NeuralNetwork.size nn1
    k2 = NeuralNetwork.size nn2
    (sss1, ooo1, sss2, ooo2) = getStatesAndOutputs' nn1 nn2
    (sss, ooo) = (Math.conc sss1 sss2, Math.conc ooo1 ooo2)
  in
    (sss, ooo)
getStatesAndOutputs Weight = (Nil, Nil)
getStatesAndOutputs Unity = (Nil, Nil)
getStatesAndOutputs Input = (Nil, Nil)
getStatesAndOutputs PreviousState = (Nil, Nil)
getStatesAndOutputs PreviousOutput = (Nil, Nil)

getStatesAndOutputs' :: NeuralNetwork n1 w1 s1 ps1 i1 o1 po1 u1 a -> NeuralNetwork n2 w2 s2 ps2 i2 o2 po2 u2 a -> (List s1 (Fin (Plus n1 n2)), List o1 (Fin (Plus n1 n2)), List s2 (Fin (Plus n1 n2)), List o2 (Fin (Plus n1 n2)))
getStatesAndOutputs' nn1 nn2 =
  let
    k1 = NeuralNetwork.size nn1
    k2 = NeuralNetwork.size nn2
    (sss1, ooo1) = getStatesAndOutputs nn1
    (sss2, ooo2) = getStatesAndOutputs nn2
    sss1' = gcastWith (minus_plus k1 k2) $ weakenList (sPlus k1 k2) k1 k2 sss1
    sss2' = gcastWith (minus_plus' k1 k2) $ weakenList (sPlus k1 k2) k2 k1 sss2
    ooo1' = gcastWith (minus_plus k1 k2) $ weakenList (sPlus k1 k2) k1 k2 ooo1
    ooo2' = gcastWith (minus_plus' k1 k2) $ weakenList (sPlus k1 k2) k2 k1 ooo2
  in
    (sss1', ooo1', sss2', ooo2')

eval'' :: (Num a) => SNat n -> NeuralNetwork n w s ps i o po u a -> List w a -> List ps a -> List po a -> List i a -> List n a
eval'' sn nn w ps po i = eval' nn w ps po i (Math.map (\_ -> Nothing) (range sn))

eval''' :: (Num a) => NeuralNetwork n w s ps i o po u a -> List w a -> List ps a -> List po a -> List i a -> List n a
eval''' nn = eval'' (NeuralNetwork.size nn) nn

eval :: (Num a) => NeuralNetwork n w s ps i o po u a -> List w a -> List i a -> (List ps a, List po a) -> (List s a, List o a)
eval nn w i (ps, po) =
  let
    r = eval''' nn w ps po i
    (s, o) = getStatesAndOutputs nn
  in
    (Math.map (\l -> Math.element l r) s, Math.map (\l -> Math.element l r) o)

evalR' :: (Num a) => NeuralNetwork n w s s i o o u a -> List w a -> [List i a] -> (List s a, List o a) -> (List s a, [List o a])
evalR' nn w [] (s, o) = (s, [o])
evalR' nn w (x:xs) i =
  let
    (s, oo) = evalR' nn w xs i
    (s', o') = eval nn w x (s, Prelude.head oo)
  in
    (s', o':oo)

evalR :: (Num a) => NeuralNetwork n w s s i o o u a -> List w a -> [List i a] -> (List s a, List o a) -> (List s a, [List o a])
evalR nn w xs i =
  let
    (s, o) = evalR' nn w (Prelude.reverse xs) i
  in
    (s, Prelude.reverse $ Prelude.tail o)

error :: (Num a) => ([List o a] -> a) -> NeuralNetwork n w s s i o o u a -> List w a -> [List i a] -> (List s a, List o a) -> a
error f nn w xs i =
  let
    (_, os) = evalR  nn w xs i
  in
    f os

{-errorW :: (Num a) => (List ii (List o a) -> a) -> NeuralNetwork n w s s i o o u a -> List w a -> List ii (List i a) -> (List s a, List o a) -> Fin w -> a -> a
errorW f nn w xs i ww v =
  NeuralNetwork.error f nn (replace v ww w) xs i

errorsW :: (Num a) => (List ii (List o a) -> a) -> NeuralNetwork n w s s i o o u a -> List w a -> List ii (List i a) -> (List s a, List o a) -> List w (a -> a)
errorsW f nn w xs i = Math.map (errorW f nn w xs i) (range (Math.length w))

fromList :: SNat n -> [a] -> Maybe (List n a)
fromList SZ [] = Just Nil
fromList (SS sn) (h:t) =
  let
    hh = fromList sn t
  in
    if isNothing hh then Nothing
    else Just $ h `Cons` (fromJust hh)
fromList _ _ = Nothing-}

mse' :: (Num a) => [List (S Z) a] -> [List (S Z) a] -> a
mse' [] [] = 0
mse' ((h `Cons` Nil):t) ((h' `Cons` Nil):t') =
  let
    e = mse' t t'
  in
    e + (h-h')*(h-h')

mse :: (Fractional a) => [List (S Z) a] -> [List (S Z) a] -> a
mse a b = (mse' a b) / (fromIntegral $ Prelude.length a)

zero' :: (Num a) => SNat n -> List n a
zero' SZ = Nil
zero' (SS n) = 0 `Cons` (zero' n)

zero :: (SingI n, Num a) => List n a
zero = zero' sing

gd :: forall a n w s i o u . (Floating a, Ord a, Enum a) => (forall a . (Enum a, Floating a) => [List o a] -> a) -> (forall a . (Floating a) => NeuralNetwork n w s s i o o u a) -> [List i a] -> (List s a, List o a) -> List w a -> [List w a]
gd f nn xs i = gradientDescent e
  where e :: forall t . (Enum t, Floating t, Scalar t ~ a, Mode t) => List w t -> t
        e w = NeuralNetwork.error f nn w (fmap (fmap auto) xs) (fmap auto $ fst i, fmap auto $ snd i)

data Proxy a = Proxy

init i = (NN $ init' NeuralNetwork.Proxy i (SS SZ), 0, [1..(toInt i)])

init' :: (Num a) => NeuralNetwork.Proxy a -> SNat i -> SNat u -> NeuralNetwork (Plus i u) Z Z Z i Z Z u a
init' a i (SS u) =
  gcastWith (successor_of_sum i u) $ Union Unity (NeuralNetwork.init' a i u)
init' a (SS i) SZ =
  let
    nn' = NeuralNetwork.init' a i SZ
    nn = Union Input nn'
  in
    nn
init' a SZ SZ = Empty

mkFin :: SNat k -> Int -> Fin k
mkFin (SS sn) 0 = ZF
mkFin (SS sn) n = SF (mkFin sn $ n-1)

mkFinList :: SNat k -> [Int] -> L (Fin k)
mkFinList sk [] = L Nil
mkFinList sk (h:t) =
  case mkFinList sk t of
    L l -> L $ (mkFin sk h) `Cons` l

lstmLayer  :: (Floating a) => SNat n -> NN a -> [Int] -> Int -> (NN a, [Int])
lstmLayer SZ nn _ _ = (nn, [])
lstmLayer (SS sn) nn i u =
  let
    (nn', os) = lstmLayer sn nn i u
    (nn'', y) =
      case nn' of
        NN n ->
          let
            (k, _, _, _, _, _, _, _) = params n
          in
            case mkFinList k i of
              L l ->
                let
                  (n', o) = lstmNeuron n l (mkFin k u)
                in
                  (NN n', (fToInt o):os)
  in
    (nn'', y)
