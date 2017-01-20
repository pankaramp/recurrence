{-# LANGUAGE DataKinds, KindSignatures, GADTs, TemplateHaskell, ScopedTypeVariables, FlexibleContexts, Rank2Types #-}

module NeuralNetwork(NeuralNetwork(..), lstmNeuron, NeuralNetwork.params, NeuralNetwork.init, gd, mse, zero, lstmLayer, NN(..), NeuralNetwork.error, evaluate, getStatesAndOutputs, suffix, toFGL) where

import Proofs
import Data.Singletons
import Data.Singletons.TH
import Data.Singletons.Prelude
import Data.Promotion.Prelude
import Math
import Data.Maybe
import Data.Type.Equality
import Data.Graph.Inductive hiding (Node)
import Numeric.AD
import qualified Numeric.AD.Internal.Reverse as R
import qualified Data.Reflection as Ref
import Numeric.AD.Newton hiding (eval)

data NN where
  NN :: forall (n :: Nat) (w :: Nat) (s :: Nat) (ps :: Nat) (i :: Nat) (o :: Nat) (po :: Nat) (u :: Nat) . NeuralNetwork n w s ps i o po u -> NN

data L a where
    L :: forall a (n :: Nat)  . List n a -> L a

data Node a = U | PS Int | St Int Int | W Int | I Int | PO Int | O Int Int | Op ([a] -> a) [Int]

fromList :: SNat n -> [a] -> List n a
fromList SZ [] = Nil
fromList (SS sn) (h:t) = h `Cons` (fromList sn t)

toFunction :: SNat n -> Function n a -> [a] -> a
toFunction sn f = f . (fromList sn)

toNodeList :: (Floating a) => NeuralNetwork (n :: Nat) (w :: Nat) (s :: Nat) (ps :: Nat) (i :: Nat) (o :: Nat) (po :: Nat) (u :: Nat) -> [[Node a]]
toNodeList nn =
  let
    (l, _) = toNodeList' nn ([], (0, 0, 0, 0, 0, 0))
    r = Prelude.reverse l
    m = foldr max 0 $ Prelude.map snd r
  in
    Prelude.map (\n -> Prelude.map fst $ filter (\x -> snd x == n) $ r) [0..m]

toNodeList' :: (Floating a) => NeuralNetwork (n :: Nat) (w :: Nat) (s :: Nat) (ps :: Nat) (i :: Nat) (o :: Nat) (po :: Nat) (u :: Nat) -> ([(Node a, Int)], (Int, Int, Int, Int, Int, Int)) -> ([(Node a, Int)],(Int, Int, Int, Int, Int, Int))
toNodeList' Empty (l, p) = (l, p)
toNodeList' Unity (l, p) = ((U, 0):l, p)
toNodeList' PreviousState (l, (ps, st, w, i, po, o)) = ((PS ps, 0):l, (ps+1, st, w, i, po, o))
toNodeList' (State nn f) (l, p) =
  let
    (l', (ps, st, w, i, po, o)) = toNodeList' nn (l, p)
    f' = fToInt f
    (_, r) =  (Prelude.reverse l') !! f'
  in
    ((St st f', r+1):l', (ps, st+1, w, i, po, o))
toNodeList' Weight (l, (ps, st, w, i, po, o)) = ((W w, 0):l, (ps, st, w+1, i, po, o))
toNodeList' Input (l, (ps, st, w, i, po, o)) = ((I i, 0):l, (ps, st, w, i+1, po, o))
toNodeList' PreviousOutput (l, (ps, st, w, i, po, o)) = ((PO po, 0):l, (ps, st, w, i, po+1, o))
toNodeList' (Output nn f) (l, p) =
  let
    (l', (ps, st, w, i, po, o)) = toNodeList' nn (l, p)
    f' = fToInt f
    (_, r) =  (Prelude.reverse l') !! f'
  in
    ((O o f', r+1):l', (ps, st, w, i, po, o+1))
toNodeList' (Union nn1 nn2) (l, p) =
  let
    (l', p') = toNodeList' nn1 (l, p)
  in
    toNodeList' nn2 (l', p')
toNodeList' (Operator nn df x) (l, p) =
  let
    (l', p') = toNodeList' nn (l, p)
    xx = Prelude.map fToInt $ toList x
    r = foldr max 0 $ Prelude.map (snd . ((Prelude.reverse l') !!)) xx
    (f, _, _) = df
  in
    ((Op (toFunction (Math.length x) f) xx, r+1):l', p')

data NeuralNetwork (n :: Nat) (w :: Nat) (s :: Nat) (ps :: Nat) (i :: Nat) (o :: Nat) (po :: Nat) (u :: Nat) where
  Empty :: NeuralNetwork Z Z Z Z Z Z Z Z
  Unity :: NeuralNetwork (S Z) Z Z Z Z Z Z (S Z)
  PreviousState :: NeuralNetwork (S Z) Z Z (S Z) Z Z Z Z
  State :: NeuralNetwork k w s ps i o po u -> Fin k -> NeuralNetwork (S k) w (S s) ps i o po u
  Weight :: NeuralNetwork (S Z) (S Z) Z Z Z Z Z Z
  Input :: NeuralNetwork (S Z) Z Z Z (S Z) Z Z Z
  PreviousOutput :: NeuralNetwork (S Z) Z Z Z Z Z (S Z) Z
  Output :: NeuralNetwork k w s ps i o po u -> Fin k -> NeuralNetwork (S k) w s ps i (S o) po u
  Union :: (SingI n, SingI w1, SingI s1, SingI ps1, SingI i1, SingI o1, SingI po1, SingI u1, SingI m, SingI w2, SingI s2, SingI ps2, SingI i2, SingI o2, SingI po2, SingI u2) => NeuralNetwork n w1 s1 ps1 i1 o1 po1 u1 -> NeuralNetwork m w2 s2 ps2 i2 o2 po2 u2 -> NeuralNetwork (Plus n m) (Plus w1 w2) (Plus s1 s2) (Plus ps1 ps2) (Plus i1 i2) (Plus o1 o2) (Plus po1 po2) (Plus u1 u2)
  Operator :: NeuralNetwork k w s ps i o po u -> (forall a . Floating a => DifferentiableFunction n a) -> List n (Fin k) -> NeuralNetwork (S k) w s ps i o po u

params :: NeuralNetwork k w s ps i o po u -> (SNat k, SNat w, SNat s, SNat ps, SNat i, SNat o, SNat po, SNat u)
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
params (Union (nn1 :: NeuralNetwork n w1 s1 ps1 i1 o1 po1 u1) (nn2 :: NeuralNetwork m w2 s2 ps2 i2 o2 po2 u2)) =
  let
    (k1, w1, s1, ps1, i1, o1, po1, u1) = (sing :: SNat n, sing :: SNat w1, sing :: SNat s1, sing :: SNat ps1, sing :: SNat i1, sing :: SNat o1, sing :: SNat po1, sing :: SNat u1)
    (k2, w2, s2, ps2, i2, o2, po2, u2) = (sing :: SNat m, sing :: SNat w2, sing :: SNat s2, sing :: SNat ps2, sing :: SNat i2, sing :: SNat o2, sing :: SNat po2, sing :: SNat u2)
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

toFGL' :: DynGraph gr => gr String () -> NeuralNetwork n w s ps i o po u -> gr String ()
toFGL' g Empty = g
toFGL' g Weight = ([], noNodes g, "W", []) & g
toFGL' g PreviousState = ([], noNodes g, "PS", []) & g
toFGL' g PreviousOutput = ([], noNodes g, "PO", []) & g
toFGL' g Unity = ([], noNodes g, "1", []) & g
toFGL' g (State nn f) = ([((), fToInt f)], noNodes (toFGL' g nn), "S", []) & (toFGL' g nn)
toFGL' g Input = ([], noNodes g, "I", []) & g
toFGL' g (Output nn f) = ([((), fToInt f)], noNodes (toFGL' g nn), "O", []) & (toFGL' g nn)
toFGL' g (Union nn1 nn2) = toFGL' (toFGL' g nn1) nn2
toFGL' g (Operator nn (f :: DifferentiableFunction n Double) l) =
  let
    fl = label f
    l' = Prelude.map (\v -> ((), fToInt v)) $ toList l    
    g' = toFGL' g nn
  in
    (l', noNodes g', fl, []) & g'

toFGL :: DynGraph gr => NeuralNetwork n w s ps i o po u -> gr String ()
toFGL = toFGL' empty

addWeight :: NeuralNetwork n w s ps i o po u -> NeuralNetwork (S n) (S w) s ps i o po u
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
    withSingI k $
    withSingI w $
    withSingI s $
    withSingI ps $
    withSingI ii $
    withSingI o $
    withSingI po $
    withSingI u $
    Union nn Weight

addWeightedEdge :: SNat k -> NeuralNetwork k w s ps i o po u -> Fin k -> (NeuralNetwork (S (S k)) (S w) s ps i o po u, Fin (S (S k)))
addWeightedEdge sk nn v =
  let
    nn' = addWeight nn
  in
    (
      Operator nn' (prod (SS (SS SZ))) ((gcastWith (minus_pred sk) $ weaken (SS sk) sk (SS SZ) v) `Cons` ((asFin sk) `Cons` Nil)),
      asFin (SS sk)
    )      

addWeightedEdges :: SNat k -> SNat w -> SNat n -> NeuralNetwork k w s ps i o po u -> List n (Fin k) -> (NeuralNetwork (Plus n (Plus n k)) (Plus n w) s ps i o po u, List n (Fin (Plus n (Plus n k))))
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

addInducedLocalField :: SNat k -> SNat w -> SNat n -> NeuralNetwork k w s ps i o po u -> List n (Fin k) -> Fin k -> (NeuralNetwork (S (S (S (Plus n (Plus n k))))) (S (Plus n w)) s ps i o po u, Fin (S (S (S (Plus n (Plus n k))))))
addInducedLocalField sk sw sn nn vs o =
  let
    (nn', vs') = addWeightedEdges sk sw (SS sn) nn (o `Cons` vs)
  in
    (
      gcastWith (successor_of_sum sn (sPlus sn sk)) $
      (Operator nn' (Math.sum (SS sn)) vs', asFin (SS (SS (sPlus sn (sPlus sn sk)))))
    )

addProduct :: SNat k -> SNat n -> NeuralNetwork k w s ps i o po u -> List n (Fin k) -> (NeuralNetwork (S k) w s ps i o po u, Fin (S k))
addProduct sk sn nn vs = (Operator nn (prod sn) vs, asFin sk)

addSum :: SNat k -> SNat n -> NeuralNetwork k w s ps i o po u -> List n (Fin k) -> (NeuralNetwork (S k) w s ps i o po u, Fin (S k))
addSum sk sn nn vs = (Operator nn (Math.sum sn) vs, asFin sk)

addNeuron :: SNat k -> SNat w -> SNat n -> NeuralNetwork k w s ps i o po u -> List n (Fin k) -> Fin k -> (forall a . (Floating a) => DifferentiableFunction (S Z) a) -> (NeuralNetwork (S (S (S (S (Plus n (Plus n k)))))) (S (Plus n w)) s ps i o po u, Fin (S (S (S (S (Plus n (Plus n k)))))))
addNeuron sk sw sn nn vs o f =
  let
    (nn', v) = addInducedLocalField sk sw sn nn vs o
  in
    (Operator nn' f (v `Cons` Nil), asFin (SS (SS (SS (sPlus sn (sPlus sn sk))))))

addLSTMNeuron1 :: SNat k -> SNat w -> SNat i -> NeuralNetwork k w s ps ii o po u -> List i (Fin k) -> Fin k -> Fin k -> Fin k -> (NeuralNetwork $(tksize 4 2) $(twsize 1 1) s ps ii o po u, Fin $(tksize 16 8))
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

addLSTMNeuron2 :: SNat k -> SNat w -> SNat i -> NeuralNetwork $(tksize 4 2) $(twsize 1 1) s ps ii o po u -> List i (Fin k) -> Fin k -> Fin k -> Fin k -> (NeuralNetwork $(tksize 8 4) $(twsize 2 2) s ps ii o po u, Fin $(tksize 16 8))
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

addLSTMNeuron3 :: SNat k -> SNat w -> SNat i -> NeuralNetwork $(tksize 8 4) $(twsize 2 2) s ps ii o po u -> List i (Fin k) -> Fin k -> Fin k -> Fin k -> (NeuralNetwork $(tksize 12 6) $(twsize 3 3) s ps ii o po u, Fin $(tksize 16 8))
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

addLSTMNeuron4 :: SNat k -> SNat w -> SNat i -> NeuralNetwork $(tksize 12 6) $(twsize 3 3) s ps ii o po u -> List i (Fin k) -> Fin k -> Fin k -> Fin k -> (NeuralNetwork $(tksize 16 8) $(twsize 4 4) s ps ii o po u, Fin $(tksize 16 8))
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

addLSTMNeuron :: SNat k -> SNat w -> SNat i -> NeuralNetwork k w s ps ii o po u -> List i (Fin k) -> Fin k -> Fin k -> Fin k -> (NeuralNetwork $(tksize 21 8) $(twsize 4 4) s ps ii o po u, Fin $(tksize 21 8), Fin $(tksize 21 8))
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

lstmNeuron1 :: NeuralNetwork k w s ps ii o po u -> NeuralNetwork (S (S k)) w s (S ps) ii o (S po) u
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
    withSingI k $
    withSingI w $
    withSingI s $
    withSingI ps $
    withSingI ii $
    withSingI o $
    withSingI po $
    withSingI u $
    Union nn (Union PreviousOutput PreviousState)

lstmNeuron2 :: NeuralNetwork (S (S k)) w s (S ps) ii o (S po) u -> List i (Fin k) -> Fin k -> (NeuralNetwork $(tksize 23 8) $(twsize 4 4) s (S ps) ii o (S po) u, Fin $(tksize 23 8), Fin $(tksize 23 8))
lstmNeuron2 nn' i u =
  let
    (sk', w, _, _, _, _, _, _) = params nn'
    sk = (sPred (sPred sk'))
    si = Math.length i
    sio = SS si
    o = weakenOne (SS sk) $ asFin sk
    c = asFin (SS sk)
    (nn'', c', o') = addLSTMNeuron (SS (SS sk)) w si nn' (weakenListOne (SS sk) $ weakenListOne sk i) o c (weakenOne (SS sk) $ weakenOne sk u)
  in
    $(normalize' 2 8 [e|(nn'', o', c')|])

lstmNeuron :: NeuralNetwork k w s ps ii o po u -> List i (Fin k) -> Fin k -> (NeuralNetwork $(tksize 25 8) $(twsize 4 4) (S s) (S ps) ii (S o) (S po) u, Fin $(tksize 25 8))
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

exceptLast' :: SNat n -> List (S n) a -> List n a
exceptLast' SZ (x `Cons` Nil) = Nil
exceptLast' (SS sn) (x `Cons` t) = x `Cons` (exceptLast' sn t)

exceptLast :: (SingI n) => List (S n) a -> List n a
exceptLast l = exceptLast' sing l

eval' :: (Floating a, SingI n) => NeuralNetwork n w s ps i o po u -> List w a -> List ps a -> List po a -> List i a -> List n (Maybe a) -> List n a
eval' Empty Nil Nil Nil Nil Nil = Nil
eval' _ _ _ _ _ l@(_ `Cons` _) | isJust $ Math.last l = Math.map fromJust l
eval' Unity Nil Nil Nil Nil (Nothing `Cons` Nil) = 1 `Cons` Nil
eval' Weight (v `Cons` Nil) Nil Nil Nil (Nothing `Cons` Nil) = (v `Cons` Nil)
eval' PreviousState Nil (v `Cons` Nil) Nil Nil (Nothing `Cons` Nil) = (v `Cons` Nil)
eval' PreviousOutput Nil Nil (v `Cons` Nil) Nil (Nothing `Cons` Nil) = (v `Cons` Nil)
eval' Input Nil Nil Nil (v `Cons` Nil) (Nothing `Cons` Nil) = (v `Cons` Nil)
eval' (Output nn f) ws pss pos is (ns :: List n (Maybe a))  =
  let
    sn = sing :: SNat n
    ns' = withSingI (sPred sn) $ exceptLast ns
    r = withSingI (sPred sn) $ eval' nn ws pss pos is ns'
    rr = Math.element f r
    rrr = rr `Cons` Nil
  in
    gcastWith (commutativity (Math.length r) (SS SZ)) $ Math.conc r rrr
eval' (State nn f) ws pss pos is (ns :: List n (Maybe a)) =
  let
    sn = sing :: SNat n
    ns' = withSingI (sPred sn) $ exceptLast ns
    r = withSingI (sPred sn) $ eval' nn ws pss pos is ns'
    rr = Math.element f r
    rrr = rr `Cons` Nil
  in
    gcastWith (commutativity (Math.length r) (SS SZ)) $ Math.conc r rrr
eval' (Union (nn1 :: NeuralNetwork n w1 s1 ps1 i1 o1 po1 u1) (nn2 :: NeuralNetwork m w2 s2 ps2 i2 o2 po2 u2)) ws pss pos is ns =
  let
    (k1, w1, s1, ps1, i1, o1, po1, u1) = (sing :: SNat n, sing :: SNat w1, sing :: SNat s1, sing :: SNat ps1, sing :: SNat i1, sing :: SNat o1, sing :: SNat po1, sing :: SNat u1)
    (k2, w2, s2, ps2, i2, o2, po2, u2) = (sing :: SNat m, sing :: SNat w2, sing :: SNat s2, sing :: SNat ps2, sing :: SNat i2, sing :: SNat o2, sing :: SNat po2, sing :: SNat u2)
    (wa, wb) = split w1 w2 ws
    (psa, psb) = split ps1 ps2 pss
    (poa, pob) = split po1 po2 pos
    (ia, ib) = split i1 i2 is
    (na, nb) = split k1 k2 ns
    r1 = withSingI k1 $ withSingI k2 $ eval' nn1 wa psa poa ia na
    r2 = eval' nn2 wb psb pob ib nb
  in
    Math.conc r1 r2
eval' (Operator nn (f, _, _) xs) ws pss pos is (ns :: List n (Maybe a)) =
  let
    sn = sing :: SNat n
    ns' = withSingI (sPred sn) $ exceptLast ns
    r = withSingI (sPred sn) $ eval' nn ws pss pos is ns'
    rr = Math.map (\l -> Math.element l r) xs
    rrr = (f rr) `Cons` Nil
  in
    gcastWith (commutativity (Math.length r) (SS SZ)) $ Math.conc r rrr

conc' :: List n a -> List m a -> List (Plus m n) a
conc' x y = gcastWith (commutativity (Math.length x) (Math.length y)) $ conc x y

newtype ListTriple n m k a = ListTriple (List n a, List m a, List k a) 

instance Functor (ListTriple n m k) where
  fmap f (ListTriple (a, b, c)) = ListTriple (fmap f a, fmap f b, fmap f c)

instance Foldable (ListTriple n m k) where
  foldr k z (ListTriple (a, b, c)) = foldr k (foldr k (foldr k z a) b) c

instance Traversable (ListTriple n m k) where
  sequenceA (ListTriple (a, b, c)) = (\x y z -> ListTriple (x, y, z)) <$> sequenceA a <*> sequenceA b <*> sequenceA c

getStatesAndOutputs :: NeuralNetwork n w s ps i o po u -> (List s (Fin n), List o (Fin n))
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
    (sss1, ooo1, sss2, ooo2) = getStatesAndOutputs' nn1 nn2
    (sss, ooo) = (Math.conc sss1 sss2, Math.conc ooo1 ooo2)
  in
    (sss, ooo)
getStatesAndOutputs Weight = (Nil, Nil)
getStatesAndOutputs Unity = (Nil, Nil)
getStatesAndOutputs Input = (Nil, Nil)
getStatesAndOutputs PreviousState = (Nil, Nil)
getStatesAndOutputs PreviousOutput = (Nil, Nil)

getStatesAndOutputs' :: (SingI n1, SingI n2) => NeuralNetwork n1 w1 s1 ps1 i1 o1 po1 u1 -> NeuralNetwork n2 w2 s2 ps2 i2 o2 po2 u2 -> (List s1 (Fin (Plus n1 n2)), List o1 (Fin (Plus n1 n2)), List s2 (Fin (Plus n1 n2)), List o2 (Fin (Plus n1 n2)))
getStatesAndOutputs' (nn1 :: NeuralNetwork n1 w1 s1 ps1 i1 o1 po1 u1) (nn2 :: NeuralNetwork n2 w2 s2 ps2 i2 o2 po2 u2) =
  let
    k1 = sing :: SNat n1
    k2 = sing :: SNat n2
    (sss1, ooo1) = getStatesAndOutputs nn1
    (sss2, ooo2) = getStatesAndOutputs nn2
    sss1' = gcastWith (minus_plus k1 k2) $ weakenList (sPlus k1 k2) k1 k2 sss1
    sss2' = gcastWith (minus_plus' k1 k2) $ weakenList (sPlus k1 k2) k2 k1 sss2
    ooo1' = gcastWith (minus_plus k1 k2) $ weakenList (sPlus k1 k2) k1 k2 ooo1
    ooo2' = gcastWith (minus_plus' k1 k2) $ weakenList (sPlus k1 k2) k2 k1 ooo2
  in
    (sss1', ooo1', sss2', ooo2')

eval'' :: (Floating a) => SNat n -> NeuralNetwork n w s ps i o po u -> List w a -> List ps a -> List po a -> List i a -> List n a
eval'' sn nn w ps po i = withSingI (NeuralNetwork.size nn) $ eval' nn w ps po i (Math.map (\_ -> Nothing) (range sn))

eval''' :: (Floating a) => NeuralNetwork n w s ps i o po u -> List w a -> List ps a -> List po a -> List i a -> List n a
eval''' nn = eval'' (NeuralNetwork.size nn) nn

eval :: (Floating a) => (List s (Fin n), List o (Fin n)) -> NeuralNetwork n w s ps i o po u -> List w a -> List i a -> (List ps a, List po a) -> (List s a, List o a)
eval so nn w i (ps, po) =
  let
    r = eval''' nn w ps po i
    (s, o) = so
  in
    (Math.map (\l -> Math.element l r) s, Math.map (\l -> Math.element l r) o)

evalR' :: (Floating a) => (List s (Fin n), List o (Fin n)) -> NeuralNetwork n w s s i o o u -> List w a -> [List i a] -> (List s a, List o a) -> (List s a, [List o a])
evalR' so nn w [] (s, o) = (s, [o])
evalR' so nn w (x:xs) i =
  let
    (s, oo) = evalR' so nn w xs i
    (s', o') = eval so nn w x (s, Prelude.head oo)
  in
    (s', o':oo)

prefix' :: SNat n -> SNat m -> List n a -> List m a
prefix' _ SZ l = Nil
prefix' (SS n) (SS m) (h `Cons` t) = h `Cons` (prefix' n m t)

prefix :: SNat m -> List n a -> List m a
prefix m l = prefix' (Math.length l) m l

suffix :: SNat m -> List n a -> List m a
suffix m = Math.reverse . (prefix m) . Math.reverse

evalR :: (Floating a) => (List s (Fin n), List o (Fin n)) -> SNat f -> NeuralNetwork n w s s i o o u -> List w a -> [List i a] -> (List s a, List o a) -> (List s a, [List f a])
evalR so f nn w xs i =
  let
    (s, o') = evalR' so nn w (Prelude.reverse xs) i
    o = fmap (suffix f) o'
  in
    (s, Prelude.tail $ Prelude.reverse o)

error :: (Floating a) => (List s (Fin n), List o (Fin n)) -> SNat f -> ([List f a] -> a) -> NeuralNetwork n w s s i o o u -> [List i a] -> (List s a, List o a) -> List w a -> a
error so sf f nn xs i w =
  let
    (_, os) = evalR so sf nn w xs i
  in
    f os

evaluate :: (Floating a) => SNat f -> NeuralNetwork n w s s i o o u -> [List i a] -> ListTriple s o w a  -> [List f a]
evaluate sf nn xs (ListTriple (s, o, w)) =
  let
    (_, sw, ss, _, _, so, _, _) = params nn
    (_, os) = evalR (getStatesAndOutputs nn) sf nn w xs (s, o)
  in
    os

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

mse' :: (Floating a) => [List (S Z) a] -> [List (S Z) a] -> a
mse' [] [] = 0
mse' ((h `Cons` Nil):t) ((h' `Cons` Nil):t') =
  let
    e = mse' t t'
  in
    e + (h-h')*(h-h')/2

mse :: (Floating a) => [List (S Z) a] -> [List (S Z) a] -> a
mse a b = (mse' a b) -- / (fromIntegral $ Prelude.length a)

zero' :: (Floating a) => SNat n -> List n a
zero' SZ = Nil
zero' (SS n) = 0.5 `Cons` (zero' n)

zero :: (SingI s, SingI o, SingI w, Floating a) => ListTriple s o w a
zero = ListTriple (zero' sing, zero' sing, zero' sing)

gd :: forall a f n w s i o u . (Floating a, Ord a, Enum a) => SNat f -> (forall b . (Enum b, Floating b) => [List f b] -> b) -> NeuralNetwork n w s s i o o u -> [List i a] -> ListTriple s o w a -> [ListTriple s o w a]
gd sf f nn xs = gradientDescent e
  where (_, sw, ss, _, _, so, _, _) = params nn
        sao = getStatesAndOutputs nn
        e :: forall t . (Enum t, Floating t, Scalar t ~ a, Mode t) => (ListTriple s o w t) -> t
        e (ListTriple (s, o, w)) = NeuralNetwork.error sao sf f nn (fmap (fmap auto) xs) (s, o) w

data Proxy a = Proxy

init i = (NN $ init' i (SS SZ), 0, [1..(toInt i)])

init' :: SNat i -> SNat u -> NeuralNetwork (Plus i u) Z Z Z i Z Z u
init' i (SS u) =
  gcastWith (successor_of_sum i u) $ withSingI (sPlus i u) $ withSingI i $ withSingI u $ Union Unity (NeuralNetwork.init' i u)
init' (SS i) SZ =
  let
    nn' = NeuralNetwork.init' i SZ
    nn = withSingI (sPlus i SZ) $ withSingI i $ Union Input nn'
  in
    nn
init' SZ SZ = Empty

mkFin :: SNat k -> Int -> Fin k
mkFin (SS sn) 0 = ZF
mkFin (SS sn) n = SF (mkFin sn $ n-1)

mkFinList :: SNat k -> [Int] -> L (Fin k)
mkFinList sk [] = L Nil
mkFinList sk (h:t) =
  case mkFinList sk t of
    L l -> L $ (mkFin sk h) `Cons` l

lstmLayer  :: SNat n -> NN -> [Int] -> Int -> (NN, [Int])
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
