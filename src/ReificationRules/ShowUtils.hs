{-# LANGUAGE CPP #-}
{-# OPTIONS_GHC -Wall #-}

-- {-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP
-- {-# OPTIONS_GHC -fno-warn-unused-binds   #-} -- TEMP

----------------------------------------------------------------------
-- |
-- Module      :  LambdaCCC.ShowUtils
-- Copyright   :  (c) 2013 Tabula, Inc.
-- License     :  BSD3
-- 
-- Maintainer  :  conal@tabula.com
-- Stability   :  experimental
-- 
-- Helpers for implementing Show
----------------------------------------------------------------------

module ReificationRules.ShowUtils
  ( showsPair
  , OpInfo(..), HasOpInfo(..)
  , module Circat.ShowUtils
  , module Circat.Show
  ) where

import Circat.ShowUtils
import Circat.Show

{--------------------------------------------------------------------
    Show helpers
--------------------------------------------------------------------}

showsPair :: (Show a, Show b) => Prec -> a -> b -> ShowS
showsPair _ a b = showParen True $
  showsPrec 0 a . showChar ',' . showsPrec 0 b

-- Simpler, but I don't like the resulting spaces around ",":
-- 
-- showsPair = showsOp2 True "," (-1,AssocNone)

data OpInfo = OpInfo String Fixity

class HasOpInfo p where
  opInfo :: p a -> Maybe OpInfo
