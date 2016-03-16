{-# LANGUAGE LambdaCase, GADTs, TypeOperators #-}

{-# OPTIONS_GHC -Wall -fno-warn-missing-signatures #-}

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

import Data.Foldable

import Data.Monoid

import ReificationRules.Misc (Unop,Binop,BinRel)
import ReificationRules.FOS (EP,repr,abst,reify)
import ReificationRules.Run (go,Okay)

import Circat.Doubli

-- TEMP
import TypeUnary.TyNat
import Circat.Pair
import Circat.RTree

import qualified Circat.Rep as R -- TEMP

main :: IO ()

-- main = print (reify t)

main = go "foo" t

{--------------------------------------------------------------------
    Working examples
--------------------------------------------------------------------}

-- t = not

-- t = not False

-- t = (4 :: Int) > 3

-- t = \ (x :: Bool) -> x

-- t = \ (x :: Int) -> x

-- t = \ (x :: Int) -> x > 3

-- t = \ x -> not (not x)

-- t = 3 :: Int

-- t = 3 :: Float

-- t = \ x y -> x || not y

-- t = \ (x :: Int) y -> x > y + 3

-- t = \ (x :: Int) (_y :: Int) -> x

-- t :: (Int,Bool) -> Bool
-- t = snd

-- t :: Int -> Bool -> (Bool,Int)
-- t x y = (y,x)

-- t (p :: (Int,Bool)) = (snd p, fst p)

-- t = (5,6) :: (Int,Int)

-- t = repr (2 :# 3 :: Pair Int)

-- t = abst (5,6)  :: Pair Int

-- t = abst :: (Int,Int) -> Pair Int

-- t = repr :: Pair Int -> (Int,Int)

-- t = 3 :# 5 :: Pair Int

-- t (x :: Int) = y * y where y = x + x

-- t = \ case u :# v -> u + v :: Int

-- t = \ case (B ts :: Tree N2 Int) -> ts

-- t = (1 +) :: Unop Int

-- t = (+ 1) :: Unop Int

-- t = (:#) :: Int -> Int -> Pair Int

-- t x = 2 :# (3 * x) :: Pair Int

-- t = fmap :: (Int -> Bool) -> Pair Int -> Pair Bool

-- t = fmap not :: Unop (Pair Bool)

-- t = fmap :: (Int -> Bool) -> Tree N0 Int -> Tree N0 Bool

-- t = fmap :: (Int -> Bool) -> Tree N4 Int -> Tree N4 Bool

-- t = fmap not :: Unop (Tree N4 Bool)

-- t = Sum (3 :: Int)

-- t = getSum :: Sum Int -> Int

-- t = \ (Sum (x :: Int)) -> Sum (x + 1)

-- t = \ (Sum (x :: Int)) (Sum (y :: Int)) -> Sum (y + x)

-- t = mappend :: Binop (Sum Int)

t = sum :: Tree N10 Int -> Int

{--------------------------------------------------------------------
    In progress
--------------------------------------------------------------------}

{--------------------------------------------------------------------
    Non-working examples
--------------------------------------------------------------------}

-- -- I don't yet handle Double. To do: switch from Doubli to Double in circat.
-- t :: Double -> Double -> Bool
-- t = \ x y -> x > y + 3

-- t = 3.0 :: Doubli
