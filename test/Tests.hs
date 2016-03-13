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

import ReificationRules.Misc (Unop,BinRel)
import ReificationRules.FOS (EP,toE,reifyP,repr,abst)
import ReificationRules.Run (run,Okay)

import Circat.Doubli

-- TEMP
import TypeUnary.TyNat
import Circat.Pair
import Circat.RTree

import qualified Circat.Rep as R -- TEMP

-- bar :: Unop Bool
-- bar = not

-- bar :: EP Bool
-- bar = not False

-- bar :: EP Bool
-- bar = (4 :: Int) > 3

-- bar :: Bool -> Bool
-- bar = \ x -> x

-- bar :: Int -> Bool
-- bar = \ x -> x > 3

-- bar :: Bool -> Bool
-- bar = \ x -> not (not x)

-- bar :: Int -> Int
-- bar = \ x -> x

-- bar :: EP Int
-- bar = 3

-- bar :: EP Doubli
-- bar = 3

-- bar :: Bool -> Bool -> Bool
-- bar = \ x y -> x || not y

-- bar :: Int -> Int -> Bool
-- bar = \ x y -> x > y + 3

-- bar :: Int -> Int -> Int
-- bar = \ x y -> x

-- bar :: Double -> Double -> Bool
-- bar = \ x y -> x > y + 3

-- bar :: (Int,Bool) -> Bool
-- bar = snd

-- bar :: Int -> Bool -> (Bool,Int)
-- bar x y = (y,x)

-- bar :: Int
-- bar = 3

-- bar :: Doubli
-- bar = 3.0

-- bar :: (Int,Bool) -> (Bool,Int)
-- bar p = (snd p, fst p)

-- bar :: (Int,Int)
-- bar = repr (2 :# 3)

-- bar :: Pair Int
-- bar = abst (5,6)

-- bar :: (Int,Int)
-- bar = (5,6)

bar :: Pair Int -> Int
bar = \ case a :# b -> a + b

-- bar :: Int -> Pair Int
-- bar x = 2 :# (3 * x)

main :: IO ()

-- main = print (toE (reifyP (abst :: (Int,Int) -> Pair Int)))

-- main = print (toE (reifyP ((:#) :: Int -> Int -> Pair Int)))

-- main = print (toE (reifyP (3 :# 5 :: Pair Int)))

-- main = print (toE (reifyP (\ case a :# b -> a + b :: Int)))

-- main = go "foo" (\ case a :# b -> a + b :: Int)

-- main = print (toE (reifyP ((\ case L a -> a) :: Tree N0 Int -> Int)))

-- main = print ((abst (5,6) :: Pair Int), (repr (7 :# 8) :: (Int,Int)))

-- main = print ((abst'' (5,6) :: Pair Int), (repr'' (7 :# 8) :: (Int,Int)))

-- main = print (abst (repr (5 :# 6)) :: Pair Int)

-- main = go "foo" (abst (repr (5 :# 6)) :: Pair Int)

-- main = go "foo" (abst (5,6) :: Pair Int)

-- main = print (toE foo)

-- main = go "foo" (\ (x :: Int) y -> x > y + 3)

-- main = go "foo" ((\ x y -> x > y + 3) :: BinRel Int)

-- main = print (toE (reifyP (fmap :: (Int -> Bool) -> Pair Int -> Pair Bool)))

-- main = print (toE foo)

main = print (toE (reifyP bar))

-- bar :: Pair Int -> Pair Bool
-- bar = fmap (> 0)

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

-- "scrutinee Pair" forall p. scrutinee p = case repr p of (a,b) -> a :# b

-- "scrutinee RTree Z" forall t. scrutinee t = L (repr t)
-- "scrutinee RTree S" forall t. scrutinee t = B (repr t)

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
