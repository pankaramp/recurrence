{-# LANGUAGE MultiParamTypeClasses, TemplateHaskell, KindSignatures, DataKinds, ScopedTypeVariables, GADTs, TypeFamilies, FlexibleInstances, TypeOperators, UndecidableInstances, InstanceSigs, FlexibleContexts, Rank2Types #-}

module Math( Nat(..), Sing(..), SNat(..), NatMaybe(..), minus, plus, times, Math.pred, Minus, Plus, Times, Pred, fPlus, fPred, sPlus, sPred, sTimes, List(..), Fin(..), Function, DifferentiableFunction, commutativity, associativity, zero_right_identity, minus_pred, minus_pred_pred, minus_plus, minus_plus', successor_of_sum, prod, Math.sum, weaken, weakenList, Math.conc, Math.tanh, sigm, asFin, weakenOne, weakenListOne, toList, fToInt, toInt, split, Math.map, Math.last, Math.length, range, element, Math.tail, Math.head, Math.reverse, replace, toFin) where

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

              times Z _ = Z
              times (S n) k = plus (times n k) k
             |]

toInt :: SNat n -> Int
toInt SZ = 0
toInt (SS sn) = 1 + (toInt sn)

instance Show (SNat n) where
  show = show . toInt

minus_pred :: SNat n -> NatJust (S Z) :~: Minus (S n) n
minus_pred SZ = Refl
minus_pred (SS n) = gcastWith (minus_pred n) Refl

minus_pred_pred :: SNat n -> NatJust (S (S Z)) :~: Minus (S (S n)) n
minus_pred_pred n = gcastWith (commutativity n (SS (SS SZ))) $ minus_plus n (SS (SS SZ))

succ_pred :: SNat n -> n :~: S (Pred n)
succ_pred (SS n) = Refl

minus_plus :: SNat n -> SNat m -> NatJust m :~: (Minus (Plus n m) n)
minus_plus SZ m = Refl
minus_plus (SS n) m = gcastWith (minus_plus n m) Refl

minus_plus' :: SNat n -> SNat m -> NatJust n :~: (Minus (Plus n m) m)
minus_plus' sn sm = gcastWith (commutativity sn sm) (minus_plus sm sn)

plus_minus :: ((Minus n m) ~ NatJust k) => SNat n -> SNat m -> SNat k -> n :~: Plus m k
plus_minus n SZ k = Refl
plus_minus (SS n) (SS m) k = gcastWith (plus_minus n m k) Refl

associativity :: (Plus m k ~ u, Plus n m ~ v) => SNat n -> SNat m -> SNat k -> (Plus n u) :~: (Plus v k)
associativity SZ m k = Refl
associativity (SS n) m k = gcastWith (associativity n m k) Refl

commutativity' :: SNat n -> SNat m -> Plus (S n) m :~: Plus n (S m)
commutativity' SZ m = Refl
commutativity' (SS n) m = gcastWith (commutativity' n m) Refl

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
  gcastWith (commutativity' n m) $
  gcastWith (commutativity (SS n) m) $
  Refl

zero_right_identity :: SNat n -> Plus n Z :~: n
zero_right_identity n = gcastWith (commutativity n SZ) Refl

data Fin (n :: Nat) where
  ZF :: Fin (S n)
  SF :: Fin n -> Fin (S n)

instance Show (Fin n) where
  show = show . fToInt

toFin :: SNat n -> Fin (S n)
toFin SZ = ZF
toFin (SS x) = SF (toFin x)

fToInt :: Fin n -> Int
fToInt ZF = 0
fToInt (SF fn) = 1 + (fToInt fn)

fPlus :: SNat n -> SNat m -> Fin n -> Fin m -> Fin (Plus n m)
fPlus sn sm ZF m = gcastWith (minus_plus' sn sm) $ weaken (sPlus sn sm) sm sn m
fPlus sn sm (SF n) m = SF (fPlus (sPred sn) sm n m)

fPred :: Fin (S n) -> Fin n
fPred (SF ZF) = ZF
fPred (SF n) =  n

data List (n :: Nat) a  where
  Nil :: List Z a
  Cons :: a -> List n a -> List (S n) a

instance (Show a) => Show (List n a) where
  show = show . toList

instance Functor (List n) where
  fmap _ Nil = Nil
  fmap f (h `Cons` t) = (f h) `Cons` (fmap f t)

instance Foldable (List n) where
  foldr _ z Nil = z
  foldr k z (h `Cons` t) = h `k` (foldr k z t)

instance Traversable (List n) where
  sequenceA Nil = pure Nil
  sequenceA (h `Cons` t) = Cons <$> h <*> sequenceA t

map :: (a -> b) -> List n a -> List n b
map _ Nil = Nil
map f (h `Cons` t) = (f h) `Cons` (Math.map f t)

length :: List n a -> SNat n
length Nil = SZ
length (_ `Cons` xs) = SS (Math.length xs)

conc :: List n a -> List m a -> List (Plus n m) a
conc Nil b = b
conc (h `Cons` t) b = h `Cons` (conc t b)

reverse'' :: SNat n -> SNat m -> List n a -> List m a -> List (Plus n m) a
reverse'' SZ _ Nil acc = acc
reverse'' (SS n) m (x `Cons` xs) acc = gcastWith (successor_of_sum n m) $ reverse'' n (SS m) xs (x `Cons` acc)

reverse' :: List n a -> List m a -> List (Plus n m) a
reverse' a b = reverse'' (Math.length a) (Math.length b) a b

reverse :: List n a -> List n a
reverse a = gcastWith (commutativity (Math.length a) SZ) $ reverse' a Nil

head :: List (S n) a -> a
head (x `Cons` _) = x

tail :: List (S n) a -> List n a
tail (_ `Cons` xs) = xs

element :: Fin n -> List n a -> a
element ZF (x `Cons` _) = x
element (SF f) (_ `Cons` xs) = element f xs

last = Math.head . Math.reverse

toList :: (List n a) -> [a]
toList Nil = []
toList (h `Cons` t) = h:(toList t)

type Function n a = List n a -> a

op :: (a -> a -> a) -> a -> Function n a
op o i = foldr o i

opExcept :: (a -> a -> a) -> a -> Fin n -> Function n a
opExcept o i n = foldr o i . replace i n

select :: Fin n -> List n a -> a
select ZF (h `Cons` _) = h
select (SF f) (_ `Cons` t) = select f t

range :: SNat n -> List n (Fin n)
range SZ = Nil
range (SS n) = ZF `Cons` (Math.map SF (range n))

replace :: a -> Fin n -> List n a -> List n a
replace r ZF (_ `Cons` t) = r `Cons` t
replace r (SF n) (h `Cons` t) = r `Cons` (replace r n t)

type DifferentiableFunction n a = (Function n a, List n (Function n a), String)

prod :: (Num a) => SNat n -> DifferentiableFunction n a
prod n = (op (*) 1, Math.map (opExcept (*) 1) (range n), "*")

sum :: (Num a) => SNat n -> DifferentiableFunction n a
sum n = (op (+) 0, Math.map (\_ _ -> 1) (range n), "+")

weakenOne :: SNat k -> Fin k -> Fin (S k)
weakenOne (SS _) ZF = ZF
weakenOne (SS n) (SF f) = SF (weakenOne n f)

weakenListOne :: SNat k -> List n (Fin k) -> List n (Fin (S k))
weakenListOne sk = Math.map (weakenOne sk)

weaken :: forall n m k . ((Minus m n) ~ NatJust k) => SNat m -> SNat n -> SNat k -> Fin n -> Fin m
weaken sm sn sk ZF =  gcastWith (apply Refl $ plus_minus sm sn sk) ZF
weaken sm sn sk (SF n) = gcastWith (apply Refl $ succ_pred sm) (SF (weaken (sPred sm) (sPred sn) sk n))

weakenList :: forall n m k l. ((Minus m n) ~ NatJust k) => SNat m ->  SNat n -> SNat k -> List l (Fin n) -> List l (Fin m)
weakenList sm sn sk = Math.map (weaken sm sn sk)

toFunction :: (a -> a) -> Function (S Z) a
toFunction f (x `Cons` Nil) = f x

tanh :: (Floating a) => DifferentiableFunction (S Z) a
tanh = (toFunction Prelude.tanh, (toFunction (\x -> 1 - (Prelude.tanh x) ^ 2)) `Cons` Nil, "tanh")

sigmoid :: (Floating a) => a -> a
sigmoid x = 1 / (1 + exp (-x))

sigm :: (Floating a) => DifferentiableFunction (S Z) a
sigm = (toFunction sigmoid, (toFunction (\x -> (sigmoid x) * (1 - sigmoid x))) `Cons` Nil, "sigm")

asFin :: SNat k -> Fin (S k)
asFin SZ = ZF
asFin (SS n) = SF (asFin n)

split :: SNat n -> SNat m -> List (Plus n m) a -> (List n a, List m a)
split SZ _ l = (Nil, l)
split (SS sn) sm (x `Cons` xs) =
  let
    (a, b) = split sn sm xs
  in
    (x `Cons` a, b)
