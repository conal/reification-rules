{-# LANGUAGE CPP                 #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE PatternSynonyms     #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeOperators       #-}

-- TEMP
{-# LANGUAGE TypeSynonymInstances, FlexibleInstances, KindSignatures
  , TypeFamilies, UndecidableInstances #-}

{-# OPTIONS_GHC -Wall #-}

{-# OPTIONS_GHC -fno-warn-missing-signatures #-}

{-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP
{-# OPTIONS_GHC -fno-warn-unused-binds   #-} -- TEMP

----------------------------------------------------------------------
-- |
-- Module      :  Suite
-- Copyright   :  (c) 2016 Conal Elliott
-- License     :  BSD3
--
-- Maintainer  :  conal@conal.net
-- Stability   :  experimental
-- 
-- Suite of automated tests
----------------------------------------------------------------------

{-# OPTIONS_GHC -fplugin=ReificationRules.Plugin -dcore-lint -fexpose-all-unfoldings #-}
{-# OPTIONS_GHC -dsuppress-idinfo -dsuppress-module-prefixes -dsuppress-uniques #-}

-- {-# OPTIONS_GHC -fplugin-opt=ReificationRules.Plugin:trace  #-}

module Suite (tests) where

import Data.Tuple (swap)
import GHC.Generics hiding (S)

import Distribution.TestSuite

import ReificationRules.HOS (E,Prim,reify)
import qualified ReificationRules.Run as Run
import ReificationRules.Misc (Unop,transpose) -- ,Binop,BinRel

import Circat.Complex

import ShapedTypes.Nat
import ShapedTypes.Pair
import ShapedTypes.Vec
import ShapedTypes.LPow (LPow)
import ShapedTypes.RPow (RPow)
import qualified ShapedTypes.LPow as L
import qualified ShapedTypes.RPow as R
import qualified ShapedTypes.Fams as F
import ShapedTypes.Sized
import ShapedTypes.Linear
import ShapedTypes.Scan
import ShapedTypes.FFT
import ShapedTypes.Orphans ()

-- TEMP
import Data.Monoid (Sum(..))
import Control.Arrow ((***))

-- GADT versions
type RBin = RPow Pair
type LBin = LPow Pair

-- -- Type family versions
-- type RBin n = F.RPow Pair n
-- type LBin n = F.LPow Pair n

-- Whether to render to a PDF (vs print reified expression)
render :: Bool
render = True -- False

-- For FP & parallelism talk
tests :: IO [Test]
tests = return
  [ nopTest

--   -- no-opt
--   , test 0.5 "sum-lvec6" (sum @(F.LVec N6) @Int)
--   , test 0.5 "sum-rvec6" (sum @(F.RVec N6) @Int)
--   , test 1   "sum-rt4"   (sum :: RBin N4 Int -> Int)

--   , test 0.5 "lsumsT-rvec6" (lscanT (+) 0 :: F.RVec N6 Int -> (F.RVec N6 Int, Int))
--   , test 0.5 "lsumsT-rt2"   (lscanT (+) 0 :: RBin  N2 Int -> (RBin  N2 Int, Int))
--   , test 0.5 "lsumsT-rt3"   (lscanT (+) 0 :: RBin  N3 Int -> (RBin  N3 Int, Int))
--   , test 0.5 "lsumsT-rt4"   (lscanT (+) 0 :: RBin  N4 Int -> (RBin  N4 Int, Int))

--   , test 2 "lsums-rt2" (lsums @(RBin N2) @Int)
--   , test 3 "lsums-rt3" (lsums @(RBin N3) @Int)
--   , test 3 "lsums-rt4" (lsums @(RBin N4) @Int)

--   , test 5 "lsums-rt5" (lsums @(RBin N5) @Int)
--   , test 3 "lsums-lt5" (lsums @(LBin N5) @Int)

  -- end no-opt

--   , test 1 "lsumsp-rt1" (lsums' @(RBin N1) @Int)
--   , test 1 "lsumsp-rt2" (lsums' @(RBin N2) @Int)
--   , test 2 "lsumsp-rt3" (lsums' @(RBin N3) @Int)
--   , test 4 "lsumsp-rt4" (lsums' @(RBin N4) @Int)

--   , test 0.5   "lsums-id" (lsums @Par1 @Int)

--   , test 0.5   "lsums-p" (lsums @Pair @Int)

--   , test 0.5   "lsums-rt1" (lsums @(RBin N1) @Int)
--   , test 1   "lsums-rt2" (lsums @(RBin N2) @Int)
--   , test 1.5 "lsums-rt3" (lsums @(RBin N3) @Int)
--   , test 3   "lsums-rt4" (lsums @(RBin N4) @Int)

--   , test 0.5 "powers-vec6" (powers @(Vec N6) @Int)
--   , test 0.5 "evalPoly-vec6" (evalPoly @(Vec N6) @Int)

--   , test 2.2 "powers-rt4"   (powers @(RBin N4) @Int)
--   , test 1.6 "evalPoly-rt4" (evalPoly @(RBin N4) @Int)

--   , test 0.5 "lsums-lvec6" (lsums @(F.LVec N6) @Int)
--   , test 0.5 "lsums-rvec6" (lsums @(F.RVec N6) @Int)

--   , test 0.5 "lsums-lvec3" (lsums @(F.LVec N3) @Int)

--   , test 3 "lsums-rp3-lv3" (lsums @(F.RPow (F.LVec N3) N3) @Int)
--   , test 8 "lsums-rp3-lp2" (lsums @(F.RPow (F.LPow Pair N2) N3) @Int)

--   , test 0.5 "lsums-q0" (lsums @(QBin N0) @Int)
--   , test 1   "lsums-q1" (lsums @(QBin N1) @Int)
--   , test 2   "lsums-q2" (lsums @(QBin N2) @Int)
--   , test 8   "lsums-q3" (lsums @(QBin N3) @Int)
--   , test 32  "lsums-q4" (lsums @(QBin N4) @Int)

  , test 8 "fft-rt5" (fft @(RBin N5) @Double)

--   , test 8 "fft-lt5" (fft @(LBin N5) @Double)

--   -- Simplifier ticks exhausted.
--   -- Probably an infinite simplification loop.
--   , test 3 "fft-v5-v4" (fft @(Vec N5 :.: Vec N4) @Double)
--   , test 3 "fft-v5-v4-v3" (fft @(Vec N5 :.: Vec N4 :.: Vec N3) @Double)

  ]

type QBin n = PPow n Pair

-- Root trees
type family PPow n (h :: * -> *) where
  PPow Z h     = h
  PPow (S n) h = PPow n (h :.: h)

#if 0
class LScan' f where
  lscan' :: Monoid a => f a -> (f a, a)
  lscan_foo :: f ()
  lscan_foo = undefined

instance LScan' (RBin Z) where
  lscan' (R.L a)    = (R.L mempty, a)

instance (Functor (RBin n), LScan' (RBin n)) => LScan' (RBin (S n)) where
  lscan' (R.B (u :# v))  = (R.B (u' :# fmap adjust v'), adjust vTot)
    where
      (u',uTot)  = lscan' u
      (v',vTot)  = lscan' v
      adjust x   = uTot `mappend` x

lsums' :: (Functor f, LScan' f, Num a) => f a -> (f a, a)
lsums' = (fmap getSum *** getSum) . lscan' . fmap Sum
#endif

#if 0
tests2 :: IO [Test]
tests2 = return
  [ test 0.5 "unit" ()

  , test 0.5 "not" not
  , test 0.5 "or-not" (\ x y -> x || not y)
  , test 0.5 "pow-6" (\ (a :: Double) -> (a + 1) ^ (6 :: Int))  -- product tree
  , test 0.5 "pow-7" (\ (a :: Double) -> (a + 1) ^ (7 :: Int))
  , test 0.5 "swap" (swap @Int @Bool)
  , test 0.5 "pair-con" (3 :# 5 :: Pair Int)
  , test 0.5 "pair-case" (\ case u :# v -> u + v :: Int)
  , test 1.0 "map-rt2" (fmap (< 3) :: RBin N2 Int -> RBin N2 Bool)
  , test 0.5 "sum-rt3" (sum :: RBin N3 Int -> Int)
  , test 0.5 "sum-pure-v" (sum (pure 1 :: Vec N4 Int))
  , test 0.5 "size-pair"(size @Pair)
  , test 0.5 "size-v3" (size @(Vec N3))
  , test 0.5 "size-rt3" (size @(RBin N3))
  , test 0.5 "size-lt2" (size @(LBin N2))
  , test 0.5 "size-r3-4" (size @(RPow (Vec N3) N4))
  , test 0.5 "transpose-p-p" (transpose @ Pair @Pair @Bool)
  , test 2.0 "transpose-p-rt3" (transpose @Pair @(RBin N3) @Bool)
  , test 15  "transpose-rt3-rt4" (transpose @(RBin N3) @(RBin N4) @Bool)
  , test 0.5 "dot" ((<.>) @Pair @Int)
  , test 1.0 "dotG-p-rt3" (dotG :: Pair (RBin N3 Int) -> Int)
  , test 1.0 "dot-rt3" ((<.>) @(RBin N3) @Int)
  , test 1.5 "linapp-v3-2" (($@) :: Matrix N3 N2 Int -> Vec N3 Int -> Vec N2 Int)
  , test 5.0 "linapp-r3-2" (($@) :: MatrixR N3 N2 Int -> RBin N3 Int -> RBin N2 Int)
  , test 5.0 "linapp-l3-2" (($@) :: MatrixL N3 N2 Int -> LBin N3 Int -> LBin N2 Int)
  , test 10  "lincomp-r342" ((.@) :: MatrixR N3 N4 Int -> MatrixR N2 N3 Int -> MatrixR N2 N4 Int)
  , test 0.5 "lsums-p" (lsums @Pair @Int)

  , test 8 "lsums-rt8" (lsums @(RBin N8) @Int)

  , test 8 "lsums-lt8" (lsums @(LBin N8) @Int)

  , test 0.5 "lsums-v6" (lsums @(RVec N6) @Int)
  , test 1.5 "powers-rt4" (powers @(RBin N4) @Int)

  , test 2.5 "evalPoly-rt6" (evalPoly @(RBin N6) @Int)

  , test 1.0 "fft-p" (fft @Pair @Double)

--   , test 6 "fft-lt6" (fft @(LBin N6) @Double)
--   , test 6 "fft-rt6" (fft @(RBin N6) @Double)

-- Broken

--    , test 0.5 "fft-v3" (fft @(Vec N3) @Double)

  ]
#endif

{--------------------------------------------------------------------
    Example helpers
--------------------------------------------------------------------}

-- Generalized matrices

type Matrix  m n a = Vec   n (Vec   m a)
type MatrixR m n a = RBin  n (RBin  m a)
type MatrixL m n a = LBin  n (LBin  m a)

-- type MatrixG p q a = Ragged q (Ragged p a)

#if 0
powers :: (LScan f, Applicative f, Num a) => a -> f a
powers = fst . lproducts . pure

evalPoly :: (LScan f, Applicative f, Foldable f, Num a) => f a -> a -> a
evalPoly coeffs x = coeffs <.> powers x
#else
type And1 f = f :*: Par1

pattern And1 :: f a -> a -> And1 f a
pattern And1 fa a = fa :*: Par1 a

andTot :: (f a, a) -> And1 f a
andTot = uncurry And1

powers :: (LScan f, Applicative f, Num a) => a -> And1 f a
powers = andTot . lproducts . pure

evalPoly :: (LScan f, Applicative f, Foldable f, Num a) => And1 f a -> a -> a
evalPoly coeffs x = coeffs <.> powers x
#endif

type C = Complex Double

{--------------------------------------------------------------------
    Testing utilities
--------------------------------------------------------------------}

test :: Run.Okay a => Double -> String -> a -> Test
test _ _ _ = error "test called"
{-# NOINLINE test #-}

{-# RULES "test" forall nm sep a. test sep nm a = mkTest sep nm (reify a) #-}

mkTest :: Run.Okay a => Double -> String -> E Prim a -> Test
mkTest sep nm e = Test inst
 where
   inst = TestInstance
            { run       = Finished Pass <$ go e
            , name      = nm
            , tags      = []
            , options   = []
            , setOption = \_ _ -> Right inst
            }
   go | render    = Run.run nm [Run.ranksep sep]
      | otherwise = print

nopTest :: Test
nopTest = Group "nop" False []
