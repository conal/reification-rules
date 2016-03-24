{-# LANGUAGE CPP, LambdaCase, GADTs, TypeOperators, DataKinds, TypeApplications #-}

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

import Circat.Complex

-- Seems to be needed for Rep (Sum Int) --> Int
-- TODO: Find a better way.
import Circat.Rep ()

import ShapedTypes.Nat
import ShapedTypes.Pair
import ShapedTypes.Vec
import qualified ShapedTypes.RPow as R
import qualified ShapedTypes.LPow as L
import ShapedTypes.Sized
import ShapedTypes.Linear
import ShapedTypes.Scan
import ShapedTypes.FFT

type RTree = R.Pow Pair
type LTree = L.Pow Pair

main :: IO ()

-- main = print (reify t)

main = go "foo" t

-- main = goSep "foo" 2 t


-- main = goSep "fft-r2-8" 16 (fft :: RTree N8 C -> LTree N8 C)

-- main = goSep "fft-l2-6" 12 (fft :: LTree N6 C -> RTree N6 C)

-- main = goSep "fft-r3-4" 4 (fft :: R.Pow (Vec N3) N4 C -> L.Pow (Vec N3) N4 C)

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

-- t :: Double -> Double -> Bool
-- t = \ x y -> x > y + 3

-- t = 3.0 :: Double

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

-- t x = if x then 2 else 1 :: Int

-- t x = if x then (2,False) else (1 :: Int,True)

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

-- t = (<.>) :: RTree N5 Int -> RTree N5 Int -> Int

-- t = ($@) :: MatrixR N3 N2 Int -> RTree N3 Int -> RTree N2 Int

-- t = ($@) :: MatrixL N3 N2 Int -> LTree N3 Int -> LTree N2 Int

-- t = (.@) :: MatrixR N3 N4 Int -> MatrixR N2 N3 Int -> MatrixR N2 N4 Int

-- t = lsums :: Pair Int -> (Pair Int, Int)

-- t = lsums :: RTree N4 Int -> (RTree N4 Int, Int)

-- t = lsums :: LTree N4 Int -> (LTree N4 Int, Int)

-- t = powers :: Int -> RTree N4 Int

-- t = evalPoly :: RTree N4 Int -> Int -> Int

-- The tree lscan examples (lsums, powers, evalPoly etc) work if I *don't* use
-- genericLscan

-- t = fft :: Unop (Pair C)

-- t = fft :: LTree N3 C -> RTree N3 C

-- t = fft :: RTree N2 C -> LTree N2 C

-- -- StateL casts
-- t = lsums :: Vec N12 Int -> (Vec N12 Int, Int)

{--------------------------------------------------------------------
    In progress
--------------------------------------------------------------------}

-- t x = x && not x

-- t = 3 ^ (4 :: Int) :: Int

t (x :: Int) = (3 :: Int) ^ x

-- t = (^) :: Binop Int

-- t = sum (pure 1 :: Vec N4 Int)

-- t = size @Pair

-- t = size @(Vec N3)

-- t = size @(RTree N3)

-- t = size @(LTree N8)

-- t = size @(R.Pow (Vec N3) N4)



-- t = fft :: Unop (Vec N3 C)

{--------------------------------------------------------------------
    Broken
--------------------------------------------------------------------}

-- t = mappend :: Binop Any

{--------------------------------------------------------------------
    Helpers
--------------------------------------------------------------------}

-- Generalized matrices

type Matrix  m n a = Vec    n (Vec    m a)
type MatrixR m n a = RTree  n (RTree  m a)
type MatrixL m n a = LTree  n (LTree  m a)

-- type MatrixG p q a = Ragged q (Ragged p a)


powers :: (LScan f, Applicative f, Num a) => a -> f a
powers = fst . lproducts . pure

evalPoly :: (LScan f, Applicative f, Foldable f, Num a) => f a -> a -> a
evalPoly coeffs x = coeffs <.> powers x

type C = Complex Double

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
