{-# LANGUAGE LambdaCase #-}

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

import ReificationRules.Misc (Unop,Binop,BinRel)
import ReificationRules.FOS (EP,repr,abst,reify)
import ReificationRules.Run (run,Okay)

import Circat.Doubli

-- TEMP
import TypeUnary.TyNat
import Circat.Pair
import Circat.RTree

import qualified Circat.Rep as R -- TEMP

main :: IO ()
main = print (reify t)

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

-- t :: Int
-- t = 3

-- t :: Doubli
-- t = 3.0

-- t (p :: (Int,Bool)) = (snd p, fst p)

-- t = (5,6) :: (Int,Int)

-- t = repr (2 :# 3 :: Pair Int)

-- t = abst (5,6)  :: Pair Int

-- t = abst :: (Int,Int) -> Pair Int

-- t = 3 :# 5 :: Pair Int

-- t (x :: Int) = y * y where y = x + x

-- t = \ case u :# v -> u + v :: Int

-- t = \ case (B ts :: Tree N2 Int) -> ts

t = (1 +) :: Unop Int

-- t = (+ 1) :: Unop Int

{--------------------------------------------------------------------
    Non-working examples
--------------------------------------------------------------------}

-- -- The constructor arguments get simplified with inlining, including $fNumInt_$c*.
-- t x = 2 :# (3 * x) :: Pair Int

-- -- I don't yet handle Double. To do: switch from Doubli to Double in Circat
-- t :: Double -> Double -> Bool
-- t = \ x y -> x > y + 3

-- -- Unsaturated non-standard constructor
-- t = (:#) :: Int -> Int -> Pair Int

-- -- I'm not yet inlining reify args
-- t = fmap :: (Int -> Bool) -> Pair Int -> Pair Bool
