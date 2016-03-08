{-# LANGUAGE CPP, ScopedTypeVariables, LambdaCase #-}
{-# LANGUAGE FlexibleContexts #-}  -- go

-- For Pair (to remove)
{-# LANGUAGE TypeFamilies #-}

-- For HR experiment
{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies, FlexibleInstances #-}

{-# OPTIONS_GHC -Wall #-}

{-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP
{-# OPTIONS_GHC -fno-warn-unused-binds   #-} -- TEMP

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

-- TEMP
import TypeUnary.TyNat
import Circat.Pair
import Circat.RTree

import qualified Circat.Rep as R -- TEMP

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

-- main = print (toE (reifyP (abst :: (Int,Int) -> Pair Int)))

-- main = print (toE (reifyP (3 :# 5 :: Pair Int)))

main = print (toE (reifyP (\ case a :# b -> a + b :: Int)))

-- main = print (toE (reifyP ((\ case L a -> a) :: Tree N0 Int -> Int)))

-- main = print ((abst (5,6) :: Pair Int), (repr (7 :# 8) :: (Int,Int)))

-- main = print ((abst'' (5,6) :: Pair Int), (repr'' (7 :# 8) :: (Int,Int)))

-- main = print (abst (repr (5 :# 6)) :: Pair Int)

-- main = go "foo" (abst (repr (5 :# 6)) :: Pair Int)

-- main = go "foo" (abst (5,6) :: Pair Int)

-- main = print (toE foo)

-- main = go "foo" (\ (x :: Int) y -> x > y + 3)

#if 1
{--------------------------------------------------------------------
    Running
--------------------------------------------------------------------}

-- The go rule in Run no longer fires, so redo here.
-- TODO: Investigate further

{-# RULES "go" forall name f. go name f = run name [] (reifyP f) #-}

go :: Okay a => String -> a -> IO ()
go = error "go -- oops"
{-# NOINLINE go #-}

#endif

{--------------------------------------------------------------------
    other experiments
--------------------------------------------------------------------}

#if 0

scrutinee :: R.HasRep a => a -> a
scrutinee = id
{-# NOINLINE scrutinee #-}

{-# RULES

"scrutinee Pair" forall p. scrutinee p = case repr p of (a,b) -> a :# b

"scrutinee RTree Z" forall t. scrutinee t = L (repr t)
"scrutinee RTree S" forall t. scrutinee t = B (repr t)

-- "reify case P" forall p f.
--   reifyP (case p of { a :# b -> f a b }) = reifyP (case repr p of { (a,b) -> f a b })

 #-}

#endif

#if 0
class HR a r | a -> r where
  abst' :: r -> a
  repr' :: a -> r

instance HR (Pair a) (a,a) where
  abst' (a,b) = (a :# b)
  repr' (a :# b) = (a,b)

abst'' :: HR a r => r -> a
repr'' :: HR a r => a -> r

abst'' = abst'
repr'' = repr'

{-# NOINLINE abst'' #-}
{-# NOINLINE repr'' #-}

#endif
