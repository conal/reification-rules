-- -*- flycheck-disabled-checkers: '(haskell-ghc haskell-stack-ghc); -*-

{-# LANGUAGE CPP                 #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-# OPTIONS_GHC -Wall #-}

{-# OPTIONS_GHC -fno-warn-missing-signatures #-}
{-# OPTIONS_GHC -fno-warn-unused-imports #-}
{-# OPTIONS_GHC -fno-warn-unused-binds   #-}

----------------------------------------------------------------------
-- |
-- Module      :  Basic
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

-- When I list the plugin in the test suite's .cabal target instead of here, I get
--
--   <command line>: Could not find module ‘ReificationRules.Plugin’
--   It is a member of the hidden package ‘reification-rules-0.0.0’.
--   Perhaps you need to add ‘reification-rules’ to the build-depends in your .cabal file.

module Basic (tests) where

import Data.Tuple (swap)
import Distribution.TestSuite

import ReificationRules.HOS (E,Prim,reify)
import qualified ReificationRules.Run as Run
import ReificationRules.Misc (Binop)

-- Whether to render to a PDF (vs print reified expression)
render :: Bool
render = True -- False

-- For FP & parallelism talk
tests :: IO [Test]
tests = return
  [ nopTest
--   , test 0.5 "foo-a" (\ x -> x * (-1) :: Double)
  , test 0.5 "foo-b" (\ x y -> x - y * (-1) :: Double)
  , test 0.5 "foo-c" (\ x y -> x - (-1) * y :: Double)
  , test 0.5 "foo-d" (\ x y -> (-1) * y - x :: Double)
  , test 0.5 "foo-e" (\ x y -> y * (-1) - x :: Double)
  
--   , test 0.5 "not" not          -- works
--   , test 0.5 "fst" (fst :: (Int,Bool) -> Int)
--   , test 0.5 "if" (\ (a :: Int) -> if a > 0 then a else negate a)
--   , test 0.5 "or-not" (\ x y -> x || not y)
--   , test 0.5 "pow-6" (\ (a :: Double) -> (a + 1) ^ (6 :: Int))  -- product tree
--   , test 0.5 "pow-7" (\ (a :: Double) -> (a + 1) ^ (7 :: Int))
--   , test 0.5 "swap" (swap @Int @Bool)
--   , test 0.5 "map-just" (fmap not . Just)
--   , test 0.5 "nothing" (Nothing :: Maybe Bool)
--   , test 0.5 "undefined" (undefined :: ())
  -- , test 0.5 "min-int" (min :: Binop Int) -- fails
  ]

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
