{-# language UndecidableInstances #-}
module Data.Singletons.Laws
  ( 
    module Data.Eq.Singletons.Laws,
    module Data.Ord.Singletons.Laws,
    module Data.Singletons.Base.Enum.Laws,
    module Data.Constraint,
  ) where

import Data.Constraint
import Data.Singletons.Base.TH
import Prelude.Singletons

import Data.Eq.Singletons.Laws
import Data.Ord.Singletons.Laws
import Data.Singletons.Base.Enum.Laws
