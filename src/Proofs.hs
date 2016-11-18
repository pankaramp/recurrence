{-# LANGUAGE TemplateHaskell #-}

module Proofs(weakenProof, minusplus, ksize, iosize, succsums, commut, assocs, assoc, normalize, tksize, tiosize) where

import Data.List
import Control.Monad
import Language.Haskell.TH

appEn n f e = foldr (\_ -> appE f) e [1..n]

appTn n f e = foldr (\_ -> appT f) e [1..n]

spioN n e = appEn n (appE (varE (mkName "sPlus")) (varE (mkName "sio"))) e

ssN n e = appEn n (conE (mkName "SS")) e

tpioN n e = appTn n (appT (conT (mkName "Plus")) (appT (conT (mkName "S"))(varT (mkName "i")))) e

tsN n e = appTn n (conT (mkName "S")) e

iosize n m = ssN n (spioN (m-1) (varE (mkName "sio")))
ksize n m = ssN n (spioN m (varE (mkName "sk")))

tiosize n m = tsN n (tpioN (m-1) (appT (conT (mkName "S")) (varT (mkName "i"))))
tksize n m = tsN n (tpioN m (varT (mkName "k")))

cast e t = appE (appE (varE (mkName "gcastWith")) e) t

assoc n e = cast $ appE (appE (appE (varE (mkName "associativity")) (varE (mkName "sio"))) (iosize 0 n)) e

assocs n e t = foldl' (\a i -> (assoc i e) a) t [1..(n-1)]

commut n e = cast $ appE (appE (varE (mkName "commutativity")) (iosize 0 n)) e

succsum n m e = cast $ appE (appE (varE (mkName "successor_of_sum")) e) (iosize n m)

succsums n m e t = foldl' (\a i -> (succsum i m e) a) t [0..(n-1)]

succsum' e = cast $ appE (appE (varE (mkName "successor_of_sum")) (iosize 0 1)) e

minusplus n m e = cast $ appE (appE (varE (mkName "minus_plus")) e) (iosize n m)

weakenProof n k t = assocs (2*n-2*k) (ksize 0 (2*k)) $ commut (2*n-2*k) (ksize 0 (2*k)) $ succsums (4*n-4*k) (2*n-2*k) (ksize 0 (2*k)) $ minusplus (4*n-4*k) (2*n-2*k) (ksize (4*k) (2*k)) $ t

normalize n k t = foldl' (\a i -> foldl' (\b j -> succsum' (ksize j i) b) a [0..(4*k-1)]) t [2*k..2*n-1] 