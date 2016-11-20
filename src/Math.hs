{-# LANGUAGE MultiParamTypeClasses, TemplateHaskell, KindSignatures, DataKinds, ScopedTypeVariables, GADTs, TypeFamilies, FlexibleInstances, TypeOperators, UndecidableInstances, InstanceSigs, FlexibleContexts #-}

module Math( Nat(..), Sing(..), SNat(..), NatMaybe(..), minus, plus, times, Math.pred, Minus, Plus, Times, Pred, fPlus, fPred, sPlus, sPred, sTimes, List(..), Fin(..), Function, DifferentiableFunction, commutativity, associativity, zero_right_identity, minus_pred, minus_pred_pred, minus_plus, minus_plus', successor_of_sum, prod, Math.sum, weaken, weakenList, Math.foldr, Math.conc, Math.tanh, sigm, asFin, weakenOne, weakenListOne, toList, fToInt, weaken1, weaken2, weaken3, weaken4, weaken5, weaken6, toInt) where

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

map :: (a -> b) -> List n a -> List n b
map _ Nil = Nil
map f (h `Cons` t) = (f h) `Cons` (Math.map f t)

foldr :: (a -> b -> b) -> b -> List n a -> b
foldr _ z Nil = z
foldr k z (h `Cons` t) = h `k` (Math.foldr k z t)

conc :: List n a -> List m a -> List (Plus n m) a
conc Nil b = b
conc (h `Cons` t) b = h `Cons` (conc t b)

toList :: (List n a) -> [a]
toList Nil = []
toList (h `Cons` t) = h:(toList t)

type Function n a = List n a -> a

op :: Num a => (a -> a -> a) -> a -> Function n a
op o i = Math.foldr o i

opExcept :: (Num a) => (a -> a -> a) -> a -> Fin n -> Function n a
opExcept o i n = Math.foldr o i . replace i n

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

tanh :: Floating a => DifferentiableFunction (S Z) a
tanh = (toFunction Prelude.tanh, (toFunction (\x -> 1 - (Prelude.tanh x) ^ 2)) `Cons` Nil, "tanh")

sigmoid :: Floating a => a -> a
sigmoid x = 1 / (1 + exp (-x))

sigm :: Floating a => DifferentiableFunction (S Z) a
sigm = (toFunction sigmoid, (toFunction (\x -> (sigmoid x) * (1 - sigmoid x))) `Cons` Nil, "sigm")

asFin :: SNat k -> Fin (S k)
asFin SZ = ZF
asFin (SS n) = SF (asFin n)

weaken1 :: (SingI k) => Fin k -> Fin (S k)
weaken1 = weakenOne sing

weaken2 :: (SingI k) => Fin k -> Fin (S (S k))
weaken2 = weaken1 . weaken1

weaken3 :: (SingI k) => Fin k -> Fin (S (S (S k)))
weaken3 = weaken1 . weaken2

weaken4 :: (SingI k) => Fin k -> Fin (S (S (S (S k))))
weaken4 = weaken1 . weaken3

weaken5 :: (SingI k) => Fin k -> Fin (S (S (S (S (S k)))))
weaken5 = weaken1 . weaken4

weaken6 :: (SingI k) => Fin k -> Fin (S (S (S (S (S (S k))))))
weaken6 = weaken1 . weaken5
