{-# LANGUAGE ScopedTypeVariables #-}

{-# LANGUAGE FlexibleContexts #-}  -- gro

-- For Pair (to remove)
{-# LANGUAGE TypeFamilies #-}

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
import ReificationRules.HOS (EP,toE,reifyP,repr,abst)
import ReificationRules.Run (run,Okay)

import Circat.Doubli

import Circat.Pair  -- TEMP

-- TEMP

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

-- foo :: EP (Int -> Int -> Bool)
-- foo = reifyP (\ x y -> x > y + 3)

-- foo :: EP (Double -> Double -> Bool)
-- foo = reifyP (\ x y -> x > y + 3)

-- foo :: EP (Int,Int)
-- foo = reifyP (repr (2 :# 3))

-- foo :: EP (Pair Int)
-- foo = reifyP (abst (5,6))

-- foo :: EP (Int,Int)
-- foo = reifyP (5,6)

main :: IO ()

-- main = go "foo" foo
-- main = print (toE foo)

main = go "foo" (\ (x :: Int) y -> x > y + 3)

{--------------------------------------------------------------------
    Running
--------------------------------------------------------------------}

-- The go rule in Run no longer fires, so redo here.
-- TODO: Investigate further

{-# RULES "go" forall name f. go name f = run name [] (reifyP f) #-}

go :: Okay a => String -> a -> IO ()
go = error "go -- oops"
{-# NOINLINE go #-}

