{-# LANGUAGE TemplateHaskell #-}

module Helpers(tailN) where

import Data.List
import Control.Monad
import Language.Haskell.TH

tailN n e = Data.List.foldr (\_ -> appE (conE (mkName "Tail"))) e [1..n]
