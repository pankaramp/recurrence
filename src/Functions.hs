{-# LANGUAGE MultiParamTypeClasses, TemplateHaskell, KindSignatures, DataKinds, ScopedTypeVariables, GADTs, TypeFamilies, FlexibleInstances, TypeOperators, UndecidableInstances, InstanceSigs, FlexibleContexts #-}

module Functions where

import Data.Singletons
import Data.Singletons.TH
import Data.Singletons.Prelude
import Data.Promotion.Prelude
import Data.Type.Equality

singletons [d|
              data Nat = Z | S Nat
                deriving Eq

              data NatMaybe = NatJust Nat | NatNothing
                         
              minus n Z = NatJust n
              minus Z (S _) = NatNothing
              minus (S n) (S m) = minus n m

              plus Z n = n
              plus (S n) m = S (plus n m)

              pred (S n) = n
             |]

minus_pred :: SNat n -> NatJust (S Z) :~: Minus (S n) n
minus_pred SZ = Refl
minus_pred (SS n) = gcastWith (minus_pred n) Refl

succ_pred :: SNat n -> n :~: S (Pred n)
succ_pred (SS n) = Refl

plus_minus :: ((Minus n m) ~ NatJust k) => SNat n -> SNat m -> SNat k -> n :~: Plus m k
plus_minus n SZ k = Refl
plus_minus (SS n) (SS m) k = gcastWith (plus_minus n m k) Refl

commutativity' :: SNat n -> SNat m -> Plus (S n) m :~: Plus n (S m)
commutativity' n m = gcastWith (commutativity' n m) Refl

commutativity'' :: SNat n -> SNat m -> Plus (S n) m :~: Plus (S m) n
commutativity'' n m = gcastWith (commutativity n m) Refl

successor_of_sum :: SNat n -> SNat m -> S (Plus n m) :~: Plus n (S m)
successor_of_sum n m =
  gcastWith (commutativity n m) $
  gcastWith (commutativity n (SS m)) $
  Refl

commutativity :: SNat n -> SNat m -> Plus n m :~: Plus m n
commutativity SZ SZ = Refl
commutativity (SS n) SZ = gcastWith (commutativity n SZ) Refl
commutativity SZ (SS n) = gcastWith (commutativity SZ n) Refl
commutativity (SS n) (SS m) =
  gcastWith (commutativity'' (SS n) m) $
  gcastWith (commutativity' (SS n) m) $
  Refl

zero_right_identity :: SNat n -> Plus n Z :~: n
zero_right_identity n = gcastWith (commutativity n SZ) Refl

data NatProxy (n :: Nat) = NatProxy

data Fin (n :: Nat) where
  ZF :: Fin (S n)
  SF :: Fin n -> Fin (S n)

data List (n :: Nat) a  where
  Nil :: List Z a
  Cons :: a -> List n a -> List (S n) a

toList :: (List n a) -> [a]
toList Nil = []
toList (h `Cons` t) = h:(toList t)

{-class Indexes m n where
  element :: NatProxy m -> (List n a) -> a
  replace :: a -> NatProxy m -> (List n a) -> (List n a)

instance Indexes Z n where
  element (NatProxy :: NatProxy Z) (h `Cons` _) = h
  replace i (NatProxy :: NatProxy Z) (_ `Cons` t) = i `Cons` t

instance Indexes m n => Indexes (S m) (S n) where
  element (NatProxy :: NatProxy (S m)) (_ `Cons` t) = element (NatProxy :: NatProxy m) t
  replace i (NatProxy :: NatProxy (S m)) (h `Cons` t) = h `Cons` (replace i (NatProxy :: NatProxy m) t)-}

type Function n a = List n a -> a

type DifferentiableFunction n a = (Function n a, List n (Function n a))

replace :: a -> Fin n -> List n a -> List n a
replace r ZF (_ `Cons` t) = r `Cons` t
replace r (SF n) (h `Cons` t) = r `Cons` (replace r n t)

element :: Fin n -> List n a -> a
element ZF (h `Cons` _) = h
element (SF n) (_ `Cons` t) = element n t

op :: Num a => (a -> a -> a) -> a -> Function n a
op o i = foldr o i . toList

opExcept :: (Num a) => (a -> a -> a) -> a -> Fin n -> Function n a
opExcept o i n = foldr o i . toList . replace i n

asFunction :: DifferentiableFunction n a -> Function n a
asFunction a = fst a

asDerivative :: Fin n -> DifferentiableFunction n a -> Function n a
asDerivative n = element n . snd

toFunction :: (a -> a) -> Function (S Z) a
toFunction f (x `Cons` Nil) = f x

tanh :: Floating a => DifferentiableFunction (S Z) a
tanh = (toFunction Prelude.tanh, (toFunction (\x -> 1 - (Prelude.tanh x) ^ 2)) `Cons` Nil)

sigmoid x = 1 / (1 + exp (-x))

sigm :: Floating a => DifferentiableFunction (S Z) a
sigm = (toFunction sigmoid, (toFunction (\x -> (sigmoid x) * (1 - sigmoid x))) `Cons` Nil)

type Node = Int

type Context (m :: Nat) (n :: Nat) a = (List n (Fin m), DifferentiableFunction n a)

data NeuralNetwork (n :: Nat) (w :: Nat) (i :: Nat) (o :: Nat) a where
  Empty :: NeuralNetwork Z Z Z Z a
  Weight :: NatProxy w -> NeuralNetwork n w i o a -> NeuralNetwork (S n) (S w) i o a
  Input :: NatProxy i -> NeuralNetwork n w i o a -> NeuralNetwork (S n) w (S i) o a
  Output :: NatProxy o -> NeuralNetwork n w i o a -> NeuralNetwork (S n) w i (S o) a
  Operator :: Context n k a -> NeuralNetwork n w i o a -> NeuralNetwork (S n) w i o a

size :: NeuralNetwork n w i o a -> Fin (S n)
size Empty = ZF
size (Weight _ nn) = SF (size nn)
size (Input _ nn) = SF (size nn)
size (Output _ nn) = SF (size nn)
size (Operator _ nn) = SF (size nn)

map :: (a -> b) -> List n a -> List n b
map _ Nil = Nil
map f (h `Cons` t) = (f h) `Cons` (Functions.map f t)

class Range n where
  range :: List n (Fin n)
  
instance Range Z where
  range = Nil

instance Range n => Range (S n) where
  range = ZF `Cons` (Functions.map SF (range :: List n (Fin n)))

weaken :: forall n m k . (SingI n, SingI m, SingI k, (Minus m n) ~ NatJust k) => Fin n -> Fin m
weaken = weaken' sing sing sing

weaken' :: forall n m k . ((Minus m n) ~ NatJust k) => SNat m -> SNat n -> SNat k -> Fin n -> Fin m
weaken' sm sn sk ZF =  gcastWith (apply Refl $ plus_minus sm sn sk) ZF
weaken' sm sn sk (SF n) = gcastWith (apply Refl $ succ_pred sm) (SF (weaken' (sPred sm) (sPred sn) sk n))

weakenList' :: forall n m k l. ((Minus m n) ~ NatJust k) => SNat m ->  SNat n -> SNat k -> List l (Fin n) -> List l (Fin m)
weakenList' sm sn sk = Functions.map (weaken' sm sn sk)

weakenList :: forall n m k l. (SingI n, SingI m, SingI k, (Minus m n) ~ NatJust k) => List l (Fin n) -> List l (Fin m)
weakenList = weakenList' sing sing sing

prod :: (Num a, Range n) => NatProxy n -> DifferentiableFunction n a
prod _ = (op (*) 1, Functions.map (opExcept (*) 1) range)

sum :: (Num a, Range n) => NatProxy n -> DifferentiableFunction n a
sum _ = (op (+) 0, Functions.map (\_ -> op (\_ _ -> 1) 1) range)

addWeightedEdge :: forall n w i o a . (SingI n, Num a) => NeuralNetwork n w i o a -> Fin n -> NeuralNetwork (S (S n)) (S w) i o a
addWeightedEdge nn v =
  let
    sn = sing :: SNat n
    wnn = Weight NatProxy nn
  in
    Operator (((gcastWith (minus_pred sn) $ weaken v) `Cons` ((size nn) `Cons` Nil)), prod NatProxy) wnn

addProduct :: forall n w i o a k . (Num a, Range k, SingI k, SingI n, SingI w) => NeuralNetwork n w i o a -> List k (Fin n) -> (NeuralNetwork (S (Plus n k)) (Plus w k) i o a, Fin (S (Plus n k)))
addProduct nn vs =
  let
    (nn', l) = addWeights nn vs
  in
    (Operator (l, prod NatProxy) nn', size nn')

addWeights :: forall n w i o a k . (SingI n, SingI w, SingI k) => NeuralNetwork n w i o a -> List k (Fin n) -> (NeuralNetwork (Plus n k) (Plus w k) i o a, List k (Fin (Plus n k)))
addWeights = addWeights' sing sing sing

addWeights' :: forall n w i o a k . SNat n -> SNat w -> SNat k -> NeuralNetwork n w i o a -> List k (Fin n) -> (NeuralNetwork (Plus n k) (Plus w k) i o a, List k (Fin (Plus n k)))
addWeights' sn sw _ nn Nil =
  ((gcastWith (zero_right_identity sn) $
  gcastWith (zero_right_identity sw) $
  nn), Nil)
addWeights' sn sw sk nn (_ `Cons` t) =
  let
    (nn', l) = addWeights' sn sw (sPred sk) nn t
    s = gcastWith (apply Refl $ successor_of_sum sn (sPred sk)) (size nn')
  in
    (
      gcastWith (commutativity sn (sPred sk)) $
      gcastWith (commutativity sw (sPred sk)) $
      gcastWith (commutativity sn sk) $
      gcastWith (commutativity sw sk) $
      (Weight NatProxy nn'),
      s `Cons` (gcastWith (minus_pred (sPlus sn (sPred sk))) $
                gcastWith (commutativity sn (sPred sk)) $
                gcastWith (commutativity sn sk) $
                weakenList' (SS (sPlus sn (sPred sk))) (sPlus sn (sPred sk)) (SS SZ) l)
    )

addInducedLocalField :: forall n w i o a k . (SingI n, SingI k, SingI w, Num a, Range k) => NeuralNetwork n w i o a -> List k (Fin n) -> (NeuralNetwork (S (S (Plus n k))) (S (Plus w k)) i o a, Fin (S (S (Plus n k))))
addInducedLocalField = addInducedLocalField' sing sing sing

addInducedLocalField' :: forall n w i o a k . (Num a, Range k) => SNat n -> SNat k -> SNat w -> NeuralNetwork n w i o a -> List k (Fin n) -> (NeuralNetwork (S (S (Plus n k))) (S (Plus w k)) i o a, Fin (S (S (Plus n k))))
addInducedLocalField' sn sk sw nn vs =
  let
    (nn', l') = addWeights' sn sw sk nn vs
    l = gcastWith (minus_pred (sPlus sn sk)) $ weakenList' (SS (sPlus sn sk)) (sPlus sn sk) (SS SZ) l' :: List k (Fin (S (Plus n k)))
    nn'' = Weight NatProxy nn'
  in
    (Operator (size nn' `Cons` l, Functions.sum NatProxy) nn'', size nn'')

{-lstmNeuron' :: forall n w i o a . SNat n -> SNat w -> NeuralNetwork n w i o a -> Fin n -> Fin n -> Fin n -> NeuralNetwork (Plus n (S (S (S (S (S (S (S (S Z))))))))) (Plus w (S (S (S (S (S (S Z))))))) i o a
lstmNeuron' sn sw nn ps po i =
  let
    (nn', v) = addInducedLocalField' sn (SS (SS SZ)) sw nn (po `Cons` (i `Cons` Nil))
    nn'' = Operator (v `Cons` Nil, Functions.sigm) nn'
    po' =
      gcastWith (apply Refl $ minus_pred (SS (SS (SS (SS sn))))) $
      gcastWith (minus_pred (SS (SS (SS sn)))) $
      gcastWith (minus_pred (SS (SS sn))) $
      gcastWith (minus_pred (SS sn)) $
      gcastWith (minus_pred sn) $
      weaken' (SS (SS (SS (SS (SS sn))))) sn (SS (SS (SS (SS (SS SZ))))) po
    i' = weaken' (SS (SS (SS (SS (SS sn))))) sn (SS (SS (SS (SS (SS SZ))))) i
    (nn''', v') = addInducedLocalField' (SS (SS (SS (sPlus sn (SS (SS SZ)))))) (SS (SS SZ)) (SS (SS (sPlus sn (SS (SS SZ))))) nn'' (po' `Cons` (i' `Cons` Nil))
  in
    nn''-}

{-
data AnyNat = forall (n :: Nat) . SingI n => AnyNat (P n)

fromInteger :: Int -> AnyNat
fromInteger 0 = AnyNat (P :: P Z)
fromInteger n =
  case fromInteger (n - 1) of
    (AnyNat (P :: P m)) -> AnyNat (P :: P (S m))


replace :: a -> Nat -> List n a -> List n a
replace r Z (_ `Cons` t) = r `Cons` t
replace r (S n) (h `Cons` t) = h `Cons` (replace r n t)

range :: SingI n => List n Nat
range = range' sing

range' :: SNat n -> List n Nat
range' SZ = Nil
range' (SS m) = (fromSing m) `Cons` (range' m)

map :: (a -> b) -> List n a -> List n b
map _ Nil = Nil
map f (h `Cons` t) = (f h) `Cons` (map f t)

data AnyDifferentiableFunction a = forall (n :: Nat) . SingI n => AnyDifferentiableFunction (DifferentiableFunction n a)






sumF :: (Num a) => Int -> Either String (AnyDifferentiableFunction a)
sumF i = if i >= 0 then
           case fromInteger i of
             AnyNat (P :: P m) -> Right $ AnyDifferentiableFunction ((op (+) 0, map (\_ _ -> 1) range) :: Num a => DifferentiableFunction m a)
          else Left "prodF: Illegal number of arguments"
              




addWeightedEdge :: DynGraph gr => NeuralNet gr -> Node -> (NeuralNet gr, Node)
addWeightedEdge (g, weights, inputs, outputs) n =
  let [n', wn] = newNodes 2 g in
  case prodF 2 of
    Right (AnyDifferentiableFunction p) ->
      (
        (
          ([], wn, Weight weights, [((), n')]) & (([((), n)], n', Operation p, []) & g),
          weights + 1,
          inputs,
          outputs
        ),
        n'
      )

addOp :: DynGraph gr => (Int -> Either String (AnyDifferentiableFunction Double)) -> NeuralNet gr -> [Node] -> Either String (NeuralNet gr, Node)
addOp op nn@(g, weights, inputs, outputs) ns =
  let
    ((g', weights', _, _), is) = foldr (\v (nn, t) ->
                                           let
                                             (nnn, h) = addWeightedEdge nn v
                                           in
                                             (nnn, h:t)
                                         ) (nn, []) ns
    [v] = newNodes 1 g'
  in
    if null ns then Left "Need at least one node"
    else
      do
        o <- op (length ns)
        case o of
          AnyDifferentiableFunction o' ->
            Right
            (
              (
                ((map ((,) ()) is), v, Operation o', []) & g',
                weights' + 1,
                inputs,
                outputs
              ),
              v
            )

addSummer :: DynGraph gr => NeuralNet gr -> [Node] -> Either String (NeuralNet gr, Node)
addSummer = addOp sumF
  
--addActivationFunction :: DynGraph gr => DifferentiableFunction (S Z) Double -> NeuralNet gr -> Node -> (NeuralNet gr, Node)
--addActivationFunction f n v = (\(Right x) -> x) $ addOp f n [v]
-}
