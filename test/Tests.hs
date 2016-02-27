-- {-# LANGUAGE #-}
{-# OPTIONS_GHC -Wall #-}

{-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP
-- {-# OPTIONS_GHC -fno-warn-unused-binds   #-} -- TEMP

----------------------------------------------------------------------
-- |
-- Module      :  Tests
-- Copyright   :  (c) 2016 Conal Elliott
-- License     :  BSD3
--
-- Maintainer  :  conal@conal.net
-- Stability   :  experimental
-- 
-- Reification tests
----------------------------------------------------------------------

module Tests where

-- TODO: explicit exports

import ReificationRules.Misc (Unop)

import ReificationRules.HOS (EP,reifyP)

-- t1 :: EP (Unop Bool)
-- t1 = reifyP not

-- t2 :: EP Bool
-- t2 = reifyP (not False)

-- t3 :: EP Bool
-- t3 = reifyP ((4 :: Int) > 3)

-- ta :: EP (Bool -> Bool)
-- ta = reifyP (\ x -> x)

t4 :: EP (Int -> Bool)
t4 = reifyP (\ x -> x > 3)

-- t4' :: EP (Bool -> Bool)
-- t4' = reifyP (\ x -> not (not x))

-- t5 :: EP (Int -> Int -> Bool)
-- t5 = reifyP (>)
