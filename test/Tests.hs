{-# LANGUAGE CPP, LambdaCase, GADTs, TypeOperators, DataKinds, TypeApplications, TypeFamilies #-}

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
import GHC.Generics hiding (C)

import ReificationRules.Misc (Unop,Binop,BinRel,transpose)
import ReificationRules.HOS (EP,repr,abst,reify,succI)
import ReificationRules.Run

import Circat.Complex

-- Seems to be needed for Rep (Sum Int) --> Int
-- TODO: Find a better way.
import Circat.Rep ()

import ShapedTypes.Nat
import ShapedTypes.Pair
import ShapedTypes.Vec
import ShapedTypes.LPow (LPow)
import ShapedTypes.RPow (RPow)
import qualified ShapedTypes.LPow as L
import qualified ShapedTypes.RPow as R
import ShapedTypes.Sized
import ShapedTypes.Linear
import ShapedTypes.Scan
import ShapedTypes.FFT

type RTree = RPow Pair
type LTree = LPow Pair

main :: IO ()

-- main = print (reify t)

main = go "foo" t

-- main = goSep "foo" 2 t


-- main = goSep "fft-r2-8" 16 (fft :: RTree N8 C -> LTree N8 C)

-- main = goSep "fft-l2-6" 12 (fft :: LTree N6 C -> RTree N6 C)

-- main = goSep "fft-r3-4" 4 (fft :: RPow (Vec N3) N4 C -> LPow (Vec N3) N4 C)

{--------------------------------------------------------------------
    Working examples
--------------------------------------------------------------------}

-- t = not

-- t = not False

-- t x = x && not x

-- t = (4 :: Int) > 3

-- t = \ (x :: Bool) -> x

-- t = \ (x :: Int) -> x

-- t = \ x -> not x

-- t = \ x -> not (not x)

-- t x y = x || not y

-- t = \ (x :: Int) -> x > 3

-- t = 3 :: Int

-- t = 3 :: Float

-- t :: Double -> Double -> Bool
-- t = \ x y -> x > y + 3

-- t = 3.0 :: Double

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

-- t x = if x then 1 :+ 2 else 3 :+ 4 :: Complex Double

-- t = (^) :: Binop Int

-- t = \ (a :: Int) -> (a + 1) ^ (3 :: Int)

-- -- Show off balanced product trees (4,5,6,8)
-- t = \ (a :: Double) -> (a + 1) ^ (6 :: Int)

-- t = \ (a :: Double) -> (a + 1) ^ (7 :: Int)

-- t (x :: Int) = (3 :: Int) ^ x

-- t = (5,6) :: (Int,Int)

-- t = repr (2 :# 3 :: Pair Int)

-- t = abst (5,6)  :: Pair Int

-- t = abst :: (Int,Int) -> Pair Int

-- t = repr :: Pair Int -> (Int,Int)

-- t = (:#) :: Int -> Int -> Pair Int

-- t = 3 :# 5 :: Pair Int

-- t = \ case u :# v -> u + v :: Int

-- t (x :: Int) = y * y where y = x + x

-- t = \ case (R.B ts :: RPow Pair N2 Int) -> ts

-- t = \ case (R.B ts :: RTree N2 Int) -> ts

-- t = (1 +) :: Unop Int

-- t = (+ 1) :: Unop Int

-- t x = 2 :# (3 * x) :: Pair Int

-- t = fmap not :: Unop (Pair Bool)

-- t = fmap (< 3) :: RTree N2 Int -> RTree N2 Bool

-- t = Sum (3 :: Int)

-- t = getSum :: Sum Int -> Int

-- t = \ (Sum (x :: Int)) -> Sum (x + 1)

-- t = \ (Sum (x :: Int)) (Sum (y :: Int)) -> Sum (y + x)

-- t = mappend :: Binop (Sum Int)

-- t = sum :: RTree N1 Int -> Int

-- t = sum (pure 1 :: Vec N4 Int)

-- t = size @Pair

-- t = size @(Vec N3)

-- t = size @(RTree N3)

-- t = size @(LTree N8)

-- t = size @(RPow (Vec N3) N4)

-- t = genericSize @Pair

-- t = genericSize @(RPow (Vec N3) N4)

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

-- t = lsums :: LTree N6 Int -> (LTree N6 Int, Int)

-- t = lsums :: Vec N6 Int -> (Vec N6 Int, Int)

-- t = powers :: Int -> RTree N4 Int

-- t = evalPoly :: RTree N4 Int -> Int -> Int

{--------------------------------------------------------------------
    In progress
--------------------------------------------------------------------}

#if 0
class Foo a where
  foo :: a -> Bool
--   dummy_Foo :: a
--   dummy_Foo = undefined

instance Foo Int where
  foo x = x > 0
#else
class Foo a where
  type Bar a
  foo :: a -> Bar a
--   dummy_Foo :: a
--   dummy_Foo = undefined

instance Foo Int where
  type Bar Int = Bool
  foo x = x > 0
#endif

-- t = foo :: Int -> Bool

-- t = foo (5 :: Int) :: Bool

-- t = repr (3 :# 5 :: Pair Int)

-- t = from1 :: Pair Int -> Rep1 Pair Int

-- t = from1 (3 :# 5 :: Pair Int)

-- -- (^) seems to be getting inlined.
-- t = fft :: Unop (Vec N3 C)

-- t = (^) :: Double -> Int -> Double

-- t = (*) :: Binop C

t = (^ (12 :: Int)) :: Unop C

-- t = dftTraversable @Pair @Double

-- t = fft @Pair @Double

-- t = genericFft @(RTree N1) @Double

{--------------------------------------------------------------------
    Broken
--------------------------------------------------------------------}


-- The tree lscan examples (lsums, powers, evalPoly etc) work if I *don't* use
-- genericLscan

-- t = fft :: Unop (Pair C)

-- t = fft :: LTree N4 C -> RTree N4 C

-- t = fft @(LTree N4) @Double

-- t = fft @(RTree N4) @Double

-- t :: Int
-- t = getProduct (Product 3)

-- t :: Product Int -> Int
-- t = getProduct

-- t :: Int -> Product Int
-- t = Product

-- t :: Product Int
-- t = Product 3

-- t = fft :: RTree N1 C -> LTree N1 C

--     (reifyP
--        @ (Pow (FFO Pair) 'Z (FFO Pair (Complex Double))
--           -> Pow (FFO Pair) ('S 'Z) (Complex Double))
--        (B @ (FFO Pair)
--           @ ('S 'Z)
--           @ (Complex Double)
--           @ 'Z
--           @~ (<'S 'Z>_N :: 'S 'Z ~# 'S 'Z)))



-- t :: (RPow (FFO Pair) Z :.: FFO Pair) C -> RPow (FFO Pair) Z (FFO Pair C)
-- t q = unComp1 q :: RPow (FFO Pair) Z (FFO Pair C)

-- t = unComp1

-- Okay

-- t = genericSize @(RTree N1)

-- t :: (Pair :.: Pair) Int -> Pair (Pair Int)
-- t = unComp1

-- t :: Pair (Pair Int) -> (Pair :.: Pair) Int
-- t = Comp1

-- t :: Unop ((Pair :.: Pair) Int)
-- t = Comp1 . unComp1

-- t :: Unop (Pair (Pair Int)) -> Unop ((Pair :.: Pair) Int)
-- t f = Comp1 . f . unComp1

----

-- -- Includes unboxed integers. Compiled without INLINE.
-- t = succI

-- -- No GenBuses instance
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
