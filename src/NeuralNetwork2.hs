{-# LANGUAGE DataKinds, KindSignatures, TypeOperators, GADTs, TemplateHaskell, TypeFamilies, UndecidableInstances, Rank2Types, AllowAmbiguousTypes, ScopedTypeVariables, MultiParamTypeClasses, FlexibleInstances, FlexibleContexts, PolyKinds #-}
{-# OPTIONS_GHC -fplugin=GHC.TypeLits.Normalise #-}

module NeuralNetwork2 where

import qualified Data.Type.List as L
import Helpers
import GHC.TypeLits
import Data.Maybe
import Data.Singletons
import Data.Singletons.TH
import Data.Promotion.TH
import Data.Singletons.TypeLits
import Data.Singletons.Prelude.Eq
import Data.Singletons.Prelude.Bool
import Data.Singletons.Prelude.Num
import Data.Singletons.Prelude.Maybe
import Data.Singletons.Prelude.List
import Data.Graph.Inductive
import Data.Type.Equality
import Data.Typeable
import Data.Array.Accelerate as A
import ValueAndDerivative

singletons [d|
              data NodeType = W | I | S | O | PS | PO | Etc
                deriving Prelude.Eq
             |]

singletonsOnly [d|
                  match :: NodeType -> (NodeType, Nat, Nat) -> Bool
                  match b (a, _, _) = b Prelude.== a
                 |]

data AtIndexNat (l :: [Nat]) (e :: Nat) (i :: Nat) where
  HeadNat :: AtIndexNat (x ': xs) x 0
  TailNat :: AtIndexNat t x i -> AtIndexNat (h ': t) x (i + 1)

data AtIndex (l :: [(NodeType, Nat, Nat)]) (e :: (Nat, Nat)) (i :: Nat) where
  Head :: AtIndex ('(t, w, h) ': xs) '(w, h) 0
  Tail :: AtIndex t x i -> AtIndex (h ': t) x (i + 1)

type Matrix e = Array DIM2 e

newtype Label = Label String
instance Show Label where
  show (Label s) = s

type UnaryFunction e (w :: Nat) (h :: Nat) (w' :: Nat) (h' :: Nat) = (Elt e) => (Acc (Matrix e) -> Acc (Matrix e), Label)
type BinaryFunction e (w :: Nat) (h :: Nat) (w' :: Nat) (h' :: Nat) (w'' :: Nat) (h'' :: Nat) = (Elt e) => (Acc (Matrix e) -> Acc (Matrix e) -> Acc (Matrix e), Label)

tnh :: (A.Floating a, Elt a) => Exp a -> Exp a
tnh x = ((exp x) - (exp (-x))) / ((exp x) + (exp (-x)))

tanh ::(A.Floating a) => UnaryFunction a w h w h
tanh = (A.map tnh, Label "tanh")

sgm :: (A.Floating a, Elt a) => Exp a -> Exp a
sgm x = 1 / (1 + exp (-x))

sigm ::(A.Floating a) => UnaryFunction a w h w h
sigm = (A.map sgm, Label "sigm")

esum :: (A.Num e) => SNat w -> SNat h -> BinaryFunction e w h w h w h
esum _ _ = (A.zipWith (+), Label ".+")

eprod :: (A.Num e) => SNat w -> SNat h -> BinaryFunction e w h w h w h
eprod _ _ = (A.zipWith (*), Label ".*")

prd :: (A.Num e, Elt e) => Acc (Matrix e) -> Acc (Matrix e) -> Acc (Matrix e)
prd a b = A.fold (+) 0 $ A.zipWith (*) aRepl bRepl
  where
    Z :. rowsA :.     _ = unlift (shape a)    :: Z :. Exp Int :. Exp Int
    Z :.     _ :. colsB = unlift (shape b)    :: Z :. Exp Int :. Exp Int
    aRepl = A.replicate (lift $ Z :. All   :. colsB :. All) a
    bRepl = A.replicate (lift $ Z :. rowsA :. All   :. All) (A.transpose b)

prod :: (A.Num e, Elt e) => SNat a -> SNat b -> SNat c -> BinaryFunction e a b b c a c
prod _ _ _= (prd, Label "*")

concat :: forall e a b c . SNat a -> SNat b -> SNat c -> BinaryFunction e a b a c a (b+c)
concat sa sb sc = ((A.++), Label "++")

data NeuralNetwork a (l :: [(NodeType, Nat, Nat)]) where
  Empty :: NeuralNetwork a '[]
  Unity :: SNat w -> SNat h -> NeuralNetwork a ('(Etc, w, h) ': '[])
  Weight :: SNat w -> SNat h -> NeuralNetwork a ('(W, w, h) ': '[])
  Input :: SNat w -> SNat h -> NeuralNetwork a ('(I, w, h) ': '[])
  PreviousState :: SNat w -> SNat h -> NeuralNetwork a ('(PS, w, h) ': '[])
  PreviousOutput :: SNat w -> SNat h -> NeuralNetwork a ('(PO, w, h) ': '[])
  State :: AtIndex l '(w, h) i -> NeuralNetwork a l -> SNat i -> SNat w -> SNat h -> NeuralNetwork a ('(S, w, h) ': l)
  Output :: AtIndex l '(w, h) i -> NeuralNetwork a l -> SNat i -> SNat w -> SNat h -> NeuralNetwork a ('(O, w, h) ': l)
  Union :: NeuralNetwork a l1 -> Sing l1 -> NeuralNetwork a l2 -> Sing l2 -> NeuralNetwork a (Concat (l1 ': l2 ': '[]))
  Unary :: (Elt a) => AtIndex l '(w, h) i -> NeuralNetwork a l -> SNat i -> SNat w -> SNat h -> UnaryFunction a w h w' h' -> NeuralNetwork a ('(Etc, w, h) ': l)
  Binary :: (Elt a) => AtIndex l '(w, h) i -> AtIndex l '(w', h') j -> NeuralNetwork a l -> SNat i -> SNat w -> SNat h -> SNat j -> SNat w' -> SNat h' -> BinaryFunction a w h w' h' w'' h'' -> NeuralNetwork a ('(Etc, w'', h'') ': l)

concat_with_nil :: Sing (l :: [(NodeType, Nat, Nat)]) -> l :~: Concat (l ': '[] ': '[])
concat_with_nil SNil = Refl
concat_with_nil (SCons _ sl) = gcastWith (concat_with_nil sl) Refl

addWeight :: Sing l -> SNat w -> SNat h -> NeuralNetwork a l -> (NeuralNetwork a ('(W, w, h) ': l), AtIndex ('(W, w, h) ': l) '(w, h) 0)
addWeight sl sw sh nn =
    gcastWith (concat_with_nil sl) $ (Union (Weight sw sh) (SCons (STuple3 SW sw sh) SNil) nn sl, Head)

addWeightedEdge :: (A.Num e, Elt e) => AtIndex l '(a, b) i -> Sing l -> SNat a -> SNat b -> SNat c -> SNat i -> NeuralNetwork e l -> NeuralNetwork e ('(Etc, a, c) ': '(W, b, c) ': l)
addWeightedEdge sp sl sa sb sc si nn =
  let
    (nn', sp') = addWeight sl sb sc nn
  in
    Binary (Tail sp) sp' nn' (si %:+ (sing :: SNat 1)) sa sb (sing :: SNat 0) sb sc (prod sa sb sc)

addInducedLocalField :: (A.Num e, Elt e) => AtIndex l '(a, b) i -> Sing l -> SNat a -> SNat b -> SNat c -> SNat i -> NeuralNetwork e l -> NeuralNetwork e ('(Etc, a, c) ': '(W, b+1, c) ': '(Etc, a, b+1) ': '(Etc, a, 1) ': l)
addInducedLocalField sp sl sa sb sc si nn =
  let
    s0 = sing :: SNat 0
    s1 = sing :: SNat 1
    nn' = Union (Unity sa s1) (SCons (STuple3 SEtc sa s1) SNil) nn sl
    sl' = SCons (STuple3 SEtc sa s1) sl
    sp' = Tail sp
    nn'' = Binary sp' Head (gcastWith (concat_with_nil sl) nn') (si %:+ s1) sa sb s0 sa s1 (NeuralNetwork2.concat sa sb s1)
    sl'' = SCons (STuple3 SEtc sa (sb %:+ s1)) sl'
  in
    addWeightedEdge Head sl'' sa (sb %:+ s1) sc s0 nn''

addNeuron :: (A.Num e, Elt e) => UnaryFunction e 1 o 1 o -> AtIndex l '(1, i) x -> Sing l -> SNat i -> SNat o -> SNat x -> NeuralNetwork e l -> NeuralNetwork e ('(Etc, 1, o) ': '(Etc, 1, o) ': '(W, i+1, o) ': '(Etc, 1, i+1) ': '(Etc, 1, 1) ': l)
addNeuron sf sp sl si so sx nn =
  let
    s0 = sing :: SNat 0
    s1 = sing :: SNat 1
    nn' = addInducedLocalField sp sl s1 si so sx nn
  in
    Unary Head nn' s0 s1 so sf
  
addLSTMLayer :: forall e i o l x . (A.Floating e, Elt e) => AtIndex l '(1, i) x -> Sing l -> SNat i -> SNat o -> SNat x -> NeuralNetwork e l -> (NeuralNetwork e ('(O, 1, o) ': '(S, 1, o) ': '(Etc, 1, o) ': '(Etc, 1, o) ': '(Etc, 1, o) ': '(Etc, 1, o) ': '(Etc, 1, o) ': '(PS, 1, o) ': '(Etc, 1, o) ': '(Etc, 1, o) ': '(W, i+o+1, o) ': '(Etc, 1, i+o+1) ': '(Etc, 1, 1) ': '(Etc, 1, o) ': '(Etc, 1, o) ': '(W, i+o+1, o) ': '(Etc, 1, i+o+1) ': '(Etc, 1, 1) ': '(Etc, 1, o) ': '(Etc, 1, o) ': '(W, i+o+1, o) ': '(Etc, 1, i+o+1) ': '(Etc, 1, 1) ': '(Etc, 1, o) ': '(Etc, 1, o) ': '(W, i+o+1, o) ': '(Etc, 1, i+o+1) ': '(Etc, 1, 1) ': '(Etc, 1, i+o) ': '(PO, 1, o) ': l), Sing ('(O, 1, o) ': '(S, 1, o) ': '(Etc, 1, o) ': '(Etc, 1, o) ': '(Etc, 1, o) ': '(Etc, 1, o) ': '(Etc, 1, o) ': '(PS, 1, o) ': '(Etc, 1, o) ': '(Etc, 1, o) ': '(W, i+o+1, o) ': '(Etc, 1, i+o+1) ': '(Etc, 1, 1) ': '(Etc, 1, o) ': '(Etc, 1, o) ': '(W, i+o+1, o) ': '(Etc, 1, i+o+1) ': '(Etc, 1, 1) ': '(Etc, 1, o) ': '(Etc, 1, o) ': '(W, i+o+1, o) ': '(Etc, 1, i+o+1) ': '(Etc, 1, 1) ': '(Etc, 1, o) ': '(Etc, 1, o) ': '(W, i+o+1, o) ': '(Etc, 1, i+o+1) ': '(Etc, 1, 1) ': '(Etc, 1, i+o) ': '(PO, 1, o) ': l))
addLSTMLayer sp sl si so sx nn =
  let
    s0 = sing :: SNat 0
    s1 = sing :: SNat 1
    s2 = sing :: SNat 2
    s3 = sing :: SNat 3
    s4 = sing :: SNat 4
    s5 = sing :: SNat 5
    sio = si %:+ so

    nn' = gcastWith (concat_with_nil sl) $ Union (PreviousOutput s1 so) (SCons (STuple3 SPO s1 so) SNil) nn sl :: NeuralNetwork e ('(PO, 1, o) ': l)
    sl' = SCons (STuple3 SPO s1 so) sl
    sx' = sx %:+ s1
    sp' = Tail sp
    
    nn'' = Binary sp' Head nn'  sx' s1 si s0 s1 so (NeuralNetwork2.concat s1 si so)
    sl'' = SCons (STuple3 SEtc s1 sio) sl'
    sx'' = s0
    sp'' = Head

    nn''' = addNeuron sigm sp'' sl'' sio so sx'' nn''
    sl''' = SCons (STuple3 SEtc s1 so) $ SCons (STuple3 SEtc s1 so) $ SCons (STuple3 SW (sio %:+ s1) so) $ SCons (STuple3 SEtc s1 (sio %:+ s1)) $ SCons (STuple3 SEtc s1 s1) sl''
    sx''' = sx'' %:+ s5
    sp''' = Tail $ Tail $ Tail $ Tail $ Tail sp''

    nn'''' = addNeuron sigm sp''' sl''' sio so sx''' nn'''
    sl'''' = SCons (STuple3 SEtc s1 so) $ SCons (STuple3 SEtc s1 so) $ SCons (STuple3 SW (sio %:+ s1) so) $ SCons (STuple3 SEtc s1 (sio %:+ s1)) $ SCons (STuple3 SEtc s1 s1) sl'''
    sx'''' = sx''' %:+ s5
    sp'''' = Tail $ Tail $ Tail $ Tail $ Tail sp'''

    nn''''' = addNeuron sigm sp'''' sl'''' sio so sx'''' nn''''
    sl''''' = SCons (STuple3 SEtc s1 so) $ SCons (STuple3 SEtc s1 so) $ SCons (STuple3 SW (sio %:+ s1) so) $ SCons (STuple3 SEtc s1 (sio %:+ s1)) $ SCons (STuple3 SEtc  s1 s1) sl''''
    sx''''' = sx'''' %:+ s5
    sp''''' = Tail $ Tail $ Tail $ Tail $ Tail sp''''

    nn'''''' = addNeuron NeuralNetwork2.tanh sp''''' sl''''' sio so sx''''' nn'''''
    sl'''''' = SCons (STuple3 SEtc s1 so) $ SCons (STuple3 SEtc s1 so) $ SCons (STuple3 SW (sio %:+ s1) so) $ SCons (STuple3 SEtc s1 (sio %:+ s1)) $ SCons (STuple3 SEtc s1 s1) sl'''''
    sx'''''' = sx''''' %:+ s5
    sp'''''' = Tail $ Tail $ Tail $ Tail $ Tail sp'''''

    nn''''''' = gcastWith (concat_with_nil sl) $ Union (PreviousState s1 so) (SCons (STuple3 SPS s1 so) SNil) nn'''''' sl''''''
    sl''''''' = SCons (STuple3 SPS s1 so) sl''''''

    spst = s0
    sc  = s1
    sou = s1 %:+ s5
    sin = s1 %:+ s5 %:+ s5
    sf  = s1 %:+ s5 %:+ s5 %:+ s5
    sps = Head
    spc = Tail $ Head
    spo = Tail $ Tail $ Tail $ Tail $ Tail spc
    spi = Tail $ Tail $ Tail $ Tail $ Tail spo
    spf = Tail $ Tail $ Tail $ Tail $ Tail spi

    nn'''''''' = Binary spf sps nn'''''''  sf s1 so spst s1 so (eprod s1 so)
    sl'''''''' = SCons (STuple3 SEtc s1 so) $ sl'''''''

    nn''''''''' = Binary (Tail spi) (Tail spc) nn''''''''  (s1 %:+ sin) s1 so (s1 %:+ sc) s1 so (eprod s1 so)
    sl''''''''' = SCons (STuple3 SEtc s1 so) $ sl''''''''

    nn'''''''''' = Binary Head (Tail Head) nn'''''''''  s0 s1 so s1 s1 so (esum s1 so)
    sl'''''''''' = SCons (STuple3 SEtc s1 so) $ sl'''''''''

    snst = s0
    spns = Head

    nn''''''''''' = Unary Head nn''''''''''  s0 s1 so NeuralNetwork2.tanh
    sl''''''''''' = SCons (STuple3 SEtc s1 so) $ sl''''''''''

    nn'''''''''''' = Binary Head (Tail $ Tail $ Tail $ Tail spo) nn'''''''''''  s0 s1 so (s4 %:+ sou) s1 so (eprod s1 so)
    sl'''''''''''' = SCons (STuple3 SEtc s1 so) $ sl'''''''''''
    
    nn''''''''''''' = State (Tail $ Tail Head) nn'''''''''''' (s2 %:+ snst) s1 so
    sl''''''''''''' = SCons (STuple3 SS s1 so) $ sl''''''''''''

    nn'''''''''''''' = Output (Tail Head) nn''''''''''''' s1 s1 so
    sl'''''''''''''' = SCons (STuple3 SO s1 so) $ sl'''''''''''''
  in
    (
      nn'''''''''''''',
      sl''''''''''''''
    )

showVal :: Sing (n :: Nat) -> String
showVal sn = show $ fromInteger $ withKnownNat sn $ natVal sn

val :: Graph gr => Sing (n :: Nat) -> gr a b -> Int
val sn g = noNodes g - 1 - (fromInteger $ withKnownNat sn $ natVal sn)

toFGL' :: DynGraph gr => gr Label Label -> NeuralNetwork e l -> gr Label Label
toFGL' g Empty = g
toFGL' g (Unity w h) = ([], noNodes g, Label ("U:"Prelude.++(showVal w)Prelude.++"x"Prelude.++(showVal h)), []) & g
toFGL' g (Weight w h) = ([], noNodes g, Label ("W:"Prelude.++(showVal w)Prelude.++"x"Prelude.++(showVal h)), []) & g
toFGL' g (Input w h) = ([], noNodes g, Label ("I:"Prelude.++(showVal w)Prelude.++"x"Prelude.++(showVal h)), []) & g
toFGL' g (PreviousState w h) = ([], noNodes g, Label ("PS:"Prelude.++(showVal w)Prelude.++"x"Prelude.++(showVal h)), []) & g
toFGL' g (PreviousOutput w h) = ([], noNodes g, Label ("PO:"Prelude.++(showVal w)Prelude.++"x"Prelude.++(showVal h)), []) & g
toFGL' g (State _ nn i w h) =
  let
    g' = toFGL' g  nn
  in
  ([(Label((showVal w)Prelude.++"x"Prelude.++(showVal h)), val i g')], noNodes g', Label("S:"Prelude.++(showVal w)Prelude.++"x"Prelude.++(showVal h)), []) & g'
toFGL' g (Output _ nn i w h) =
  let
    g' = toFGL' g  nn
  in
  ([(Label((showVal w)Prelude.++"x"Prelude.++(showVal h)), val i g')], noNodes g', Label("O"Prelude.++(showVal w)Prelude.++"x"Prelude.++(showVal h)), []) & g'
toFGL' g (Union nn1 _ nn2 _) = toFGL' (toFGL' g nn2) nn1
toFGL' g (Unary _ nn i sw sh (f, l)) =
  let
    g' = toFGL' g  nn
  in
  ([(Label((showVal sw)Prelude.++"x"Prelude.++(showVal sh)), val i g')], noNodes g', l, []) & g'
toFGL' g (Binary _ _ nn i sw sh j sw' sh' (f, l)) =
  let
    g' = toFGL' g  nn
  in
  ([(Label((showVal sw)Prelude.++"x"Prelude.++(showVal sh)), val i g'), (Label((showVal sw')Prelude.++"x"Prelude.++(showVal sh')), val j g')], noNodes g', l, []) & g'

toFGL'' :: DynGraph gr => NeuralNetwork e l -> gr Label Label
toFGL'' = toFGL' empty

expVal :: Sing (n :: Nat) -> Exp Int
expVal sn = fromInteger $ withKnownNat sn $ natVal sn

intVal :: Sing (n :: Nat) -> Int
intVal sn = fromInteger $ withKnownNat sn $ natVal sn

init' :: (Elt e, A.Floating e) => Sing (l :: [(NodeType, Nat, Nat)]) -> [Acc (Matrix e)]
init' SNil = []
init' (SCons (STuple3 _ w h) sl) = generate (index2 (expVal w) (expVal h)) (\_ -> 1.1) : init' sl

init :: (Elt e, A.Floating e) => Sing (l :: [(NodeType, Nat, Nat)]) -> ([Acc (Matrix e)], [Acc (Matrix e)], [Acc (Matrix e)], [Acc (Matrix e)])
init sl =
  let
    sww = sFilter (singFun1 (Proxy :: Proxy (MatchSym1 W)) (sMatch SW)) sl
    sii = sFilter (singFun1 (Proxy :: Proxy (MatchSym1 I)) (sMatch SI)) sl
    sps = sFilter (singFun1 (Proxy :: Proxy (MatchSym1 PS)) (sMatch SPS)) sl
    spo = sFilter (singFun1 (Proxy :: Proxy (MatchSym1 PO)) (sMatch SPO)) sl
  in
    (init' sww, init' sii, init' sps, init' spo)

initD :: (A.Floating e, Prelude.Floating e, Plain e ~ e, Lift Exp e) => Int -> Int -> Int -> Sing (l :: [(NodeType, Nat, Nat)]) -> ([Acc (Matrix (ValueAndDerivative e))], [Acc (Matrix (ValueAndDerivative e))], [Acc (Matrix (ValueAndDerivative e))], [Acc (Matrix (ValueAndDerivative e))])
initD i a b sl =
  let
    sww = sFilter (singFun1 (Proxy :: Proxy (MatchSym1 W)) (sMatch SW)) sl
    sii = sFilter (singFun1 (Proxy :: Proxy (MatchSym1 I)) (sMatch SI)) sl
    sps = sFilter (singFun1 (Proxy :: Proxy (MatchSym1 PS)) (sMatch SPS)) sl
    spo = sFilter (singFun1 (Proxy :: Proxy (MatchSym1 PO)) (sMatch SPO)) sl
  in
    (initD' i a b sww, init' sii, init' sps, init' spo)

initD' :: forall e l . (A.Floating e, Prelude.Floating e, Plain e ~ e, Lift Exp e) => Int -> Int -> Int -> Sing (l :: [(NodeType, Nat, Nat)]) -> [Acc (Matrix (ValueAndDerivative e))]
initD' _ _ _ SNil = []
initD' 0 a b (SCons (STuple3 _ w h) sl) = generate (index2 (expVal w) (expVal h)) (\i -> let k = unindex2 i in cond (A.fst k A.== Prelude.fromIntegral a A.&& A.snd k A.== Prelude.fromIntegral b) (lift (ValueAndDerivative 1.1 1 :: ValueAndDerivative e)) (lift (ValueAndDerivative 1.1 0 :: ValueAndDerivative e))) : initD' (-1) a b sl
initD' i a b (SCons (STuple3 _ w h) sl) = generate (index2 (expVal w) (expVal h)) (\_ -> 1.1) : initD' (i-1) a b sl

eval' :: (A.Num e) => Sing l -> NeuralNetwork (ValueAndDerivative e) l -> [Acc (Matrix (ValueAndDerivative e))] -> [Acc (Matrix (ValueAndDerivative e))] -> [Acc (Matrix (ValueAndDerivative e))] -> [Acc (Matrix (ValueAndDerivative e))] -> [Acc (Matrix (ValueAndDerivative e))]
eval' = eval

eval :: (A.Num e) => Sing l -> NeuralNetwork e l -> [Acc (Matrix e)] -> [Acc (Matrix e)] -> [Acc (Matrix e)] -> [Acc (Matrix e)] -> [Acc (Matrix e)]
eval sl (Unity w h) [] [] [] [] = [generate (index2 (expVal w) (expVal h)) (\_ -> 1)]
eval sl (Weight w h) ww [] [] [] = ww
eval sl (Input w h) [] ii [] [] = ii
eval sl (PreviousState w h) [] [] ps [] = ps
eval sl (PreviousOutput w h) [] [] [] po = po
eval (SCons _ sl) (State _ nn i w h) ww ii ps po =
  let
    t = eval sl nn ww ii ps po
  in
    (t Prelude.!! (intVal i)) : t
eval (SCons _ sl) (Output _ nn i w h) ww ii ps po =
  let
    t = eval sl nn ww ii ps po
  in
    (t Prelude.!! (intVal i)) : t
eval sl (Union nn1 sl1 nn2 sl2) ww ii ps po =
  let
    nww1 = intVal $ sLength $ sFilter (singFun1 (Proxy :: Proxy (MatchSym1 W)) (sMatch SW)) sl1
    nii1 = intVal $ sLength $ sFilter (singFun1 (Proxy :: Proxy (MatchSym1 I)) (sMatch SI)) sl1
    nps1 = intVal $ sLength $ sFilter (singFun1 (Proxy :: Proxy (MatchSym1 PS)) (sMatch SPS)) sl1
    npo1 = intVal $ sLength $ sFilter (singFun1 (Proxy :: Proxy (MatchSym1 PO)) (sMatch SPO)) sl1
    (ww1, ww2) = splitAt nww1 ww
    (ii1, ii2) = splitAt nii1 ii
    (ps1, ps2) = splitAt nps1 ps
    (po1, po2) = splitAt npo1 po
    t1 = eval sl1 nn1 ww1 ii1 ps1 po1
    t2 = eval sl2 nn2 ww2 ii2 ps2 po2
  in
    t1 Prelude.++ t2
eval (SCons _ sl) (Unary _ nn i w h (f, l)) ww ii ps po =
  let
    t = eval sl nn ww ii ps po
  in
    f (t Prelude.!! (intVal i)) : t
eval (SCons _ sl) (Binary _ _ nn i w h j w' h' (f, l)) ww ii ps po =
  let
    t = eval sl nn ww ii ps po
  in
    f (t Prelude.!! (intVal i)) (t Prelude.!! (intVal j)) : t

data SomeNeuralNetwork e i o where
  SomeNeuralNetwork :: forall e i o (l :: [(NodeType, Nat, Nat)]) . (A.Floating e) => Sing l -> AtIndex l '(1, i) ((Length l) - 1) -> AtIndex l '(1, o) 0 -> NeuralNetwork e l -> SomeNeuralNetwork e i o

toFGL :: DynGraph gr => SomeNeuralNetwork e i o -> gr Label Label
toFGL nn = case nn of
  SomeNeuralNetwork _ _ _ nn' -> toFGL'' nn'

data SomeSNat where
  SomeSNat :: SNat n -> SomeSNat

toSomeSNat :: Int -> Maybe SomeSNat
toSomeSNat n
  | n Prelude.> 0 = case toSomeSNat (n-1) of
      Just (SomeSNat sn) -> Just $ SomeSNat $ sn %:+ (sing :: SNat 1)
  | n Prelude.< 0 = Nothing
  | otherwise = Just $ SomeSNat (sing :: SNat 0)

addLayer :: (Elt e) => SNat i -> SNat o -> SNat o' -> SomeNeuralNetwork e i o -> SomeNeuralNetwork e i o'
addLayer si so so' nn =
  let
    s0 = sing :: SNat 0
    s1 = sing :: SNat 1
  in
    case nn of
      SomeNeuralNetwork sl spi spo nn' ->
        let
          (nn'', sl') = addLSTMLayer spo sl so so' s0 nn'
        in
          SomeNeuralNetwork sl' $(tailN 30 [e|spi|]) Head nn''

addLayers :: (Elt e) => SNat i -> SNat o -> Sing ((o' ': l) :: [Nat]) -> SomeNeuralNetwork e i o -> SomeNeuralNetwork e i o'
addLayers si so (SCons so' SNil) nn = addLayer si so so' nn
addLayers si so (SCons sx (SCons sy sl)) nn = addLayer si sy sx $ addLayers si so (SCons sy sl) nn

makeNetwork :: (A.Floating e, Elt e) => SNat i -> Sing (l :: [Nat]) -> SNat o -> SomeNeuralNetwork e i o
makeNetwork si sl so =
  let
    s1 = sing :: SNat 1
    nn = SomeNeuralNetwork (SCons (STuple3 SI s1 si) SNil) Head Head $ Input s1 si
  in
    addLayers si si (SCons so (sReverse sl)) nn
