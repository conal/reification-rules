{-# LANGUAGE CPP, LambdaCase, GADTs, TypeOperators, DataKinds #-}

{-# OPTIONS_GHC -Wall -fno-warn-unticked-promoted-constructors -fno-warn-missing-signatures #-}

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
import Data.Tuple (swap)

import ReificationRules.Misc (Unop,Binop,BinRel,transpose)
import ReificationRules.HOS (EP,repr,abst,reify)
import ReificationRules.Run

import Circat.Doubli

-- Seems to be needed for Rep (Sum Int) --> Int
-- TODO: Find a better way.
import Circat.Rep ()

import ShapedTypes.Nat
import ShapedTypes.Pair
import ShapedTypes.Vec
import qualified ShapedTypes.RPow as R
import qualified ShapedTypes.LPow as L
import ShapedTypes.Linear

type RTree = R.Pow Pair
type LTree = L.Pow Pair

main :: IO ()

-- main = print (reify t)

main = go "foo" t

-- main = goSep "foo" 10 t

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

-- t :: (Int,Bool) -> (Bool,Int)
-- t = swap

-- t (p :: (Int,Bool)) = (snd p, fst p)

-- t = (5,6) :: (Int,Int)

-- t = repr (2 :# 3 :: Pair Int)

-- t = abst (5,6)  :: Pair Int

-- t = abst :: (Int,Int) -> Pair Int

-- t = repr :: Pair Int -> (Int,Int)

-- t = 3 :# 5 :: Pair Int

-- t (x :: Int) = y * y where y = x + x

-- t = \ case u :# v -> u + v :: Int

-- t = \ case (R.B ts :: R.Pow Pair N2 Int) -> ts

-- t = \ case (R.B ts :: RTree N2 Int) -> ts

-- t = (1 +) :: Unop Int

-- t = (+ 1) :: Unop Int

-- t = (:#) :: Int -> Int -> Pair Int

-- t x = 2 :# (3 * x) :: Pair Int

-- t = fmap :: (Int -> Bool) -> Pair Int -> Pair Bool

-- t = fmap not :: Unop (Pair Bool)

-- t = fmap :: (Int -> Bool) -> RTree N0 Int -> RTree N0 Bool

-- t = fmap :: (Int -> Bool) -> RTree N4 Int -> RTree N4 Bool

-- t = fmap not :: Unop (RTree N4 Bool)

-- t = Sum (3 :: Int)

-- t = getSum :: Sum Int -> Int

-- t = \ (Sum (x :: Int)) -> Sum (x + 1)

-- t = \ (Sum (x :: Int)) (Sum (y :: Int)) -> Sum (y + x)

-- t = mappend :: Binop (Sum Int)

-- t = sum :: RTree N6 Int -> Int

-- t = transpose :: Unop (Pair (Pair Bool))

-- t = transpose :: Pair (RTree N6 Bool) -> RTree N6 (Pair Bool)

-- -- simpl-tick-factor bump
-- t = transpose :: RTree N3 (RTree N4 Bool) -> RTree N4 (RTree N3 Bool)

-- t = (<.>) :: Pair Int -> Pair Int -> Int

-- t = dotG :: Pair (RTree N1 Int) -> Int

t = (<.>) :: RTree N5 Int -> RTree N5 Int -> Int

{--------------------------------------------------------------------
    In progress
--------------------------------------------------------------------}

{--------------------------------------------------------------------
    Broken
--------------------------------------------------------------------}

-- -- I don't yet handle Double. To do: switch from Doubli to Double in circat.
-- t :: Double -> Double -> Bool
-- t = \ x y -> x > y + 3

-- t = 3.0 :: Doubli

{--------------------------------------------------------------------
    Helpers
--------------------------------------------------------------------}

-- Generalized matrices

type Matrix  m n a = Vec    n (Vec    m a)
type MatrixT m n a = RTree  n (RTree  m a)
-- type MatrixG p q a = Ragged q (Ragged p a)

#if 0

{--------------------------------------------------------------------
    Permutations
--------------------------------------------------------------------}

invertR :: IsNat n => RTree n a -> LTree n a
invertR = invertR' nat

invertR' :: Nat n -> RTree n a -> LTree n a
invertR' Zero     = \ (R.L a ) -> L.L a
invertR' (Succ m) = \ (R.B ts) -> L.B (invertR' m (transpose ts))
-- invertR' (Succ m) = \ (R.B ts) -> L.B (transpose (invertR' m <$> ts))

#if 0
R.unB    :: RTree (S n)   a  -> Pair (RTree n a)
transpose :: Pair (RTree n a) -> RTree n (Pair a)
invertR   :: RTree n (Pair a) -> LTree n (Pair a)
L.B      :: LTree n (Pair a) -> LTree (S n)   a

R.unB       :: RTree (S n)   a  -> Pair (RTree n a)
fmap invertR :: Pair (RTree n a) -> Pair (LTree n a)
transpose    :: Pair (LTree n a) -> LTree n (Pair a)
L.B         :: LTree n (Pair a) -> LTree (S n)   a
#endif

-- We needed the IsNat n for Applicative on RTree n.
-- The reverse transformation is easier, since we know Pair is Applicative.

invertL :: LTree n a -> RTree n a
invertL (L.L a ) = R.L a
invertL (L.B ts) = R.B (transpose (invertL ts))
-- invertL (L.B ts) = R.B (invertL <$> transpose ts)

-- invertR' (Succ m) = \ (R.B ts) -> L.B (transpose (invertR' m <$> ts))

#if 0
L.unB    :: LTree (S n)   a  -> LTree n (Pair a)
invertL   :: LTree n (Pair a) -> RTree n (Pair a)
transpose :: RTree n (Pair a) -> Pair (RTree n a)
R.B      :: Pair (RTree n a) -> RTree (S n)   a

L.unB       :: LTree (S n)   a  -> LTree n (Pair a)
transpose    :: LTree n (Pair a) -> Pair (LTree n a)
fmap invertL :: Pair (LTree n a) -> Pair (RTree n a)
R.B         :: Pair (RTree n a) -> RTree (S n)   a
#endif

#endif
