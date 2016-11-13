{-# LANGUAGE TemplateHaskell #-}

module Proofs(weakenProof, minusplus, ksize, iosize, succsums', assocs') where

import Data.List
import Control.Monad
import Language.Haskell.TH

appEn n f e = foldr (\_ -> appE f) e [1..n]

spioN n e = appEn n (appE (varE (mkName "sPlus")) (varE (mkName "sio"))) e

ssN n e = appEn n (conE (mkName "SS")) e

reflN n e = appEn n (appE (varE (mkName "apply")) (conE (mkName "Refl"))) e

iosize n m = ssN n (spioN (m-1) (varE (mkName "sio")))
ksize n m = ssN n (spioN m (varE (mkName "sk")))

assoc' r l n m = reflN r (appE (appE (appE (varE (mkName "associativity")) (varE (mkName "sio"))) (iosize 0 l)) (ksize 0 (n+m)))

assoc r n e = reflN r (appE (appE (appE (varE (mkName "associativity")) (varE (mkName "sio"))) (iosize 0 n)) e)

assocs r n e = foldl' (\a i -> appE (appE (varE (mkName "trans")) a) (assoc (r+n-1-i) i e)) (conE (mkName "Refl")) [1..(n-1)]

assocs' r n m = foldl' (\a i -> appE (appE (varE (mkName "trans")) a) (assoc' r i (n-1-i) m)) (conE (mkName "Refl")) [1..(n-1)]

commut r n e = reflN r (appE (appE (varE (mkName "commutativity")) (iosize 0 n)) e)

succsum' r l n m = reflN r (appE (appE (varE (mkName "successor_of_sum")) (iosize 0 l)) (ksize n m))

succsum r n m e = reflN r (appE (appE (varE (mkName "successor_of_sum")) e) (iosize n m))

succsums' l n m = foldl' (\a i -> appE (appE (varE (mkName "trans")) a) (succsum' (n-1-i) l i m)) (conE (mkName "Refl")) [0..(n-1)]

succsums r n m e = foldl' (\a i -> appE (appE (varE (mkName "trans")) a) (succsum (r+n-1-i) i m e)) (conE (mkName "Refl")) [0..(n-1)]

minusplus n m e = appE (appE (varE (mkName "minus_plus")) e) (iosize n m)

weakenProof r n e = appE (appE (varE (mkName "trans")) (appE (appE (varE (mkName "trans")) (assocs r n e)) (commut r n e))) (succsums 0 r n e)
