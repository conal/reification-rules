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

{-# OPTIONS_GHC -fplugin=ReificationRules.Plugin -dcore-lint -fexpose-all-unfoldings #-}
{-# OPTIONS_GHC -dsuppress-idinfo -dsuppress-module-prefixes -dsuppress-uniques #-}

-- {-# OPTIONS_GHC -fplugin-opt=ReificationRules.Plugin:trace  #-}

module Suite (tests) where

import Distribution.TestSuite

import ReificationRules.HOS (E,Prim,reify)
import qualified ReificationRules.Run as Run

tests :: IO [Test]
tests = return
  [ test "reNot"   $ not
  , test "reOrNot" $ \ x y -> x || not y
  , test "true"    $ True
  , test "false"   $ False
  ]

render :: Bool
render = True -- False

test :: Run.Okay a => String -> a -> Test
test _ _ = error "test called"
{-# NOINLINE test #-}

{-# RULES "test" forall nm a.
  test nm a = mkTest nm (reify a)
  #-}

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
