{-# LANGUAGE TemplateHaskell #-}

module Proofs(weakenProof, minusplus, ksize, iosize, succsums, commut, assocs, assoc) where

import Data.List
import Control.Monad
import Language.Haskell.TH

appEn n f e = foldr (\_ -> appE f) e [1..n]

spioN n e = appEn n (appE (varE (mkName "sPlus")) (varE (mkName "sio"))) e

ssN n e = appEn n (conE (mkName "SS")) e

reflN n e = appEn n (appE (varE (mkName "apply")) (conE (mkName "Refl"))) e

reflreflN n e = appEn n (appE (varE (mkName "apply")) (appE (appE (varE (mkName "apply")) (conE (mkName "Refl"))) (conE (mkName "Refl")))) e

iosize n m = ssN n (spioN (m-1) (varE (mkName "sio")))
ksize n m = ssN n (spioN m (varE (mkName "sk")))

cast e t = appE (appE (varE (mkName "gcastWith")) e) t

assoc n e = cast $ appE (appE (appE (varE (mkName "associativity")) (varE (mkName "sio"))) (iosize 0 n)) e

assocs n e t = foldl' (\a i -> (assoc i e) a) t [1..(n-1)]

commut n e = cast $ appE (appE (varE (mkName "commutativity")) (iosize 0 n)) e

succsum n m e = cast $ appE (appE (varE (mkName "successor_of_sum")) e) (iosize n m)

succsums n m e t = foldl' (\a i -> (succsum i m e) a) t [0..(n-1)]

minusplus n m e = cast $ appE (appE (varE (mkName "minus_plus")) e) (iosize n m)

weakenProof n k t = assocs n (ksize 0 k) $ commut n (ksize 0 k) $ succsums (2*n) n (ksize 0 k) $ minusplus (2*n) n (ksize (2*k) k) $ t
