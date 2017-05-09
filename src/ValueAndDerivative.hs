{-# LANGUAGE ScopedTypeVariables, TypeFamilies, UndecidableInstances, MultiParamTypeClasses, FlexibleInstances, ConstraintKinds, FlexibleContexts #-}
module ValueAndDerivative where

import Prelude as P
import Data.Typeable
import Data.Array.Accelerate as A
import Data.Array.Accelerate.Product
import Data.Array.Accelerate.Array.Sugar
import Data.Array.Accelerate.Smart

type instance EltRepr (ValueAndDerivative e) = EltRepr (e, e)

data ValueAndDerivative e = ValueAndDerivative e e
  deriving (Typeable, Show, P.Eq)

derivative :: forall e . (Elt e) => Exp (ValueAndDerivative e) -> Exp e
derivative e = let (ValueAndDerivative (_ :: Exp e) x) = unlift e in x

value :: forall e . (Elt e) => Exp (ValueAndDerivative e) -> Exp e
value e = let (ValueAndDerivative x (_ :: Exp e)) = unlift e in x

fromValue :: (A.Num e) => Exp e -> Exp (ValueAndDerivative e)
fromValue e = lift (ValueAndDerivative e 0)

instance Elt e => Elt (ValueAndDerivative e) where
  eltType (_ :: ValueAndDerivative e) = eltType (undefined :: (e, e))
  toElt vd = let (v, d) = toElt vd in ValueAndDerivative v d
  fromElt (ValueAndDerivative v d) = fromElt (v, d)

instance cst e => IsProduct cst (ValueAndDerivative e) where
  type ProdRepr (ValueAndDerivative e) = ProdRepr (e, e)
  fromProd cst (ValueAndDerivative a b) = fromProd cst (a, b)
  toProd cst t                     = let (a, b) = toProd cst t in ValueAndDerivative a b
  prod cst _                     = prod cst (undefined :: (e, e))

instance (Elt (Plain e), Lift Exp e) => Lift Exp (ValueAndDerivative e) where
  type Plain (ValueAndDerivative e) = ValueAndDerivative (Plain e)
  lift (ValueAndDerivative a b)
      = Exp . Tuple
      $ NilTup `SnocTup` lift  a `SnocTup` lift b

instance (Elt a) => Unlift Exp (ValueAndDerivative (Exp a)) where
  unlift e
    = let v     = Exp $ SuccTupIdx ZeroTupIdx `Prj` e
          d     = Exp $ ZeroTupIdx `Prj` e
      in
      ValueAndDerivative v d

instance P.Num e => P.Num (ValueAndDerivative e) where
  (ValueAndDerivative a b) + (ValueAndDerivative c d) = ValueAndDerivative (a+c) (b+d)
  (ValueAndDerivative a b) - (ValueAndDerivative c d) = ValueAndDerivative (a-c) (b-d)
  (ValueAndDerivative a b) * (ValueAndDerivative c d) = ValueAndDerivative (a*c) (a*d+b*c)
  abs (ValueAndDerivative a b) = undefined
  signum (ValueAndDerivative a b) = undefined
  fromInteger a = ValueAndDerivative (fromInteger a) 0

instance P.Fractional e => P.Fractional (ValueAndDerivative e) where
  recip (ValueAndDerivative a b) = ValueAndDerivative (recip a) (-(recip a)*(recip a)*b)
  fromRational a = ValueAndDerivative (fromRational a) 0

instance P.Floating e => P.Floating (ValueAndDerivative e) where
  pi = ValueAndDerivative pi 0
  exp (ValueAndDerivative a b) = ValueAndDerivative (exp a) ((exp a) * b)
  log (ValueAndDerivative a b) = ValueAndDerivative (log a) ((recip a) * b)
  sin (ValueAndDerivative a b) = ValueAndDerivative (sin a) ((cos a) * b)
  cos (ValueAndDerivative a b) = ValueAndDerivative (cos a) (-(sin a) * b)
  asin (ValueAndDerivative a b) = ValueAndDerivative (asin a) ((recip (sqrt (1 - a*a))) * b)
  acos (ValueAndDerivative a b) = ValueAndDerivative (acos a) (-(recip (sqrt (1 - a*a))) * b)
  atan (ValueAndDerivative a b) = ValueAndDerivative (atan a) ((recip (1 + a*a)) * b)
  sinh (ValueAndDerivative a b) = ValueAndDerivative (sinh a) ((cosh a) * b)
  cosh (ValueAndDerivative a b) = ValueAndDerivative (cosh a) ((sinh a) * b)
  asinh (ValueAndDerivative a b) = ValueAndDerivative (asinh a) ((recip (sqrt (1 + a*a))) * b)
  acosh (ValueAndDerivative a b) = ValueAndDerivative (acosh a) (-(recip (sqrt (- 1 + a*a))) * b)
  atanh (ValueAndDerivative a b) = ValueAndDerivative (atanh a) ((recip (1 - a*a)) * b)


instance A.Num e => P.Num (Exp (ValueAndDerivative e)) where
  (+) = lift2 ((+) :: ValueAndDerivative (Exp e) -> ValueAndDerivative (Exp e) -> ValueAndDerivative (Exp e))
  (-) = lift2 ((-) :: ValueAndDerivative (Exp e) -> ValueAndDerivative (Exp e) -> ValueAndDerivative (Exp e))
  (*) = lift2 ((*) :: ValueAndDerivative (Exp e) -> ValueAndDerivative (Exp e) -> ValueAndDerivative (Exp e))
  negate = lift1 (negate :: ValueAndDerivative (Exp e) -> ValueAndDerivative (Exp e))
  signum = lift1 (signum :: ValueAndDerivative (Exp e) -> ValueAndDerivative (Exp e))
  abs = lift1 (abs :: ValueAndDerivative (Exp e) -> ValueAndDerivative (Exp e))
  fromInteger n = lift (fromInteger n :: ValueAndDerivative (Exp e))

instance A.Fractional e => P.Fractional (Exp (ValueAndDerivative e)) where
  recip = lift1 (recip :: ValueAndDerivative (Exp e) -> ValueAndDerivative (Exp e))
  fromRational r = lift (fromRational r :: ValueAndDerivative (Exp e))

instance A.Floating e => P.Floating (Exp (ValueAndDerivative e)) where
  pi = lift (pi :: ValueAndDerivative (Exp e))
  log = lift1 (log :: ValueAndDerivative (Exp e) -> ValueAndDerivative (Exp e))
  exp = lift1 (exp :: ValueAndDerivative (Exp e) -> ValueAndDerivative (Exp e))
  sin = lift1 (sin :: ValueAndDerivative (Exp e) -> ValueAndDerivative (Exp e))
  cos = lift1 (cos :: ValueAndDerivative (Exp e) -> ValueAndDerivative (Exp e))
  tan = lift1 (tan :: ValueAndDerivative (Exp e) -> ValueAndDerivative (Exp e))
  sinh = lift1 (sinh :: ValueAndDerivative (Exp e) -> ValueAndDerivative (Exp e))
  cosh = lift1 (cosh :: ValueAndDerivative (Exp e) -> ValueAndDerivative (Exp e))
  tanh = lift1 (tanh :: ValueAndDerivative (Exp e) -> ValueAndDerivative (Exp e))
  asin = lift1 (asin :: ValueAndDerivative (Exp e) -> ValueAndDerivative (Exp e))
  acos = lift1 (acos :: ValueAndDerivative (Exp e) -> ValueAndDerivative (Exp e))
  atan = lift1 (atan :: ValueAndDerivative (Exp e) -> ValueAndDerivative (Exp e))
  asinh = lift1 (asinh :: ValueAndDerivative (Exp e) -> ValueAndDerivative (Exp e))
  acosh = lift1 (acosh :: ValueAndDerivative (Exp e) -> ValueAndDerivative (Exp e))
  atanh = lift1 (atanh :: ValueAndDerivative (Exp e) -> ValueAndDerivative (Exp e))
