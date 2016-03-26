{-# LANGUAGE CPP              #-}
{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs            #-}
{-# LANGUAGE LambdaCase       #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators    #-}

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

import Distribution.TestSuite

import ReificationRules.HOS (E,Prim,reify)
import qualified ReificationRules.Run as Run
import ReificationRules.Misc (Unop,transpose) -- ,Binop,BinRel

import Circat.Complex

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

-- Whether to render to a PDF (vs print reified expression)
render :: Bool
render = True -- False

tests :: IO [Test]
tests = return
  [ test 0.5 "not" not
--   , test 0.5 "or-not" (\ x y -> x || not y)
--   , test 0.5 "pow-6" (\ (a :: Double) -> (a + 1) ^ (6 :: Int))  -- product tree
--   , test 0.5 "pow-7" (\ (a :: Double) -> (a + 1) ^ (7 :: Int))
--   , test 0.5 "swap" (swap @Int @Bool)
--   , test 0.5 "pair-con" (3 :# 5 :: Pair Int)
--   , test 0.5 "pair-case" (\ case u :# v -> u + v :: Int)
--   , test 1.0 "map-rt2" (fmap (< 3) :: RTree N2 Int -> RTree N2 Bool)
--   , test 0.5 "sum-rt3" (sum :: RTree N3 Int -> Int)
--   , test 0.5 "sum-pure-v" (sum (pure 1 :: Vec N4 Int))
--   , test 0.5 "size-pair"(size @Pair)
--   , test 0.5 "size-v3" (size @(Vec N3))
--   , test 0.5 "size-rt3" (size @(RTree N3))
--   , test 0.5 "size-lt2" (size @(LTree N2))
--   , test 0.5 "size-r3-4" (size @(R.Pow (Vec N3) N4))
--   , test 0.5 "transpose-p-p" (transpose @ Pair @Pair @Bool)
--   , test 2.0 "transpose-p-rt3" (transpose @Pair @(RTree N3) @Bool)
--   , test 15  "transpose-rt3-rt4" (transpose @(RTree N3) @(RTree N4) @Bool)
--   , test 0.5 "dot" ((<.>) @Pair @Int)
--   , test 1.0 "dotG-p-rt3" (dotG :: Pair (RTree N3 Int) -> Int)
--   , test 1.0 "dot-rt3" ((<.>) @(RTree N3) @Int)
--   , test 1.5 "linapp-v3-2" (($@) :: Matrix N3 N2 Int -> Vec N3 Int -> Vec N2 Int)
--   , test 5.0 "linapp-r3-2" (($@) :: MatrixR N3 N2 Int -> RTree N3 Int -> RTree N2 Int)
--   , test 5.0 "linapp-l3-2" (($@) :: MatrixL N3 N2 Int -> LTree N3 Int -> LTree N2 Int)
--   , test 10  "lincomp-r342" ((.@) :: MatrixR N3 N4 Int -> MatrixR N2 N3 Int -> MatrixR N2 N4 Int)
--   , test 0.5 "lsums-p" (lsums @Pair @Int)
--   , test 1.5 "lsums-rt4" (lsums @(RTree N4) @Int)
--   , test 3.0 "lsums-lt6" (lsums @(LTree N6) @Int)
--   , test 0.5 "lsums-v6" (lsums @(Vec N6) @Int)
--   , test 1.5 "powers-rt4" (powers @(RTree N4) @Int)
--   , test 1.5 "evalPoly-rt4" (evalPoly @(RTree N4) @Int)
--   , test 1.0 "fft-p" (fft @Pair @Pair @Double)
--   , test 2.5 "fft-lt3" (fft @(LTree N3) @(RTree N3) @Double)
--   , test 2.0 "fft-rt2" (fft @(RTree N2) @(LTree N2) @Double)
  ]

  -- TODO: TypeApplications

{--------------------------------------------------------------------
    Example helpers
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
