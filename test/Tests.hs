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

-- module Tests where

-- TODO: explicit exports

import ReificationRules.Misc (Unop)

import ReificationRules.HOS (EP,reifyP)

import Circat.Doubli

-- t1 :: EP (Unop Bool)
-- t1 = reifyP not

-- t2 :: EP Bool
-- t2 = reifyP (not False)

-- t3 :: EP Bool
-- t3 = reifyP ((4 :: Int) > 3)

-- ta :: EP (Bool -> Bool)
-- ta = reifyP (\ x -> x)

-- t4 :: EP (Int -> Bool)
-- t4 = reifyP (\ x -> x > 3)

-- t5 :: EP (Bool -> Bool)
-- t5 = reifyP (\ x -> not (not x))

-- t6 :: EP (Bool -> Bool -> Bool)
-- t6 = reifyP (\ x y -> x || not y)

foo :: EP (Int -> Int -> Bool)
foo = reifyP (\ x y -> x > y + 3)

-- foo :: EP (Double -> Double -> Bool)
-- foo = reifyP (\ x y -> x > y + 3)

main :: IO ()
main = print (fst foo)
