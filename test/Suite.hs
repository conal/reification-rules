{-# LANGUAGE FlexibleContexts #-}
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

module Suite (tests) where

import Distribution.TestSuite

import ReificationRules.HOS (E,Prim)
import qualified ReificationRules.Run as Run

import ExamplesForSuite

tests :: IO [Test]

tests = return
  [ mkTest "reNot"   reNot
  , mkTest "reOrNot" reOrNot
  ]

render :: Bool
render = True -- False

mkTest :: Run.Okay a => String -> E Prim a -> Test
mkTest nm e = Test inst
 where
   inst = TestInstance
            { run       = do if render then
                               Run.run nm [] e
                              else
                               print e
                             return $ Finished Pass
            , name      = nm
            , tags      = []
            , options   = []
            , setOption = \_ _ -> Right inst
            }

-- tests = return []

-- <https://www.haskell.org/cabal/users-guide/developing-packages.html#test-suites>

-- tests = return [ Test succeeds, Test fails ]
--   where
--     succeeds = TestInstance
--         { run = return $ Finished Pass
--         , name = "succeeds"
--         , tags = []
--         , options = []
--         , setOption = \_ _ -> Right succeeds
--         }
--     fails = TestInstance
--         { run = return $ Finished $ Fail "Always fails!"
--         , name = "fails"
--         , tags = []
--         , options = []
--         , setOption = \_ _ -> Right fails
--         }
