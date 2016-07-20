{-# LANGUAGE CPP                 #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE TypeApplications    #-}

{-# OPTIONS_GHC -Wall #-}

{-# OPTIONS_GHC -fno-warn-missing-signatures #-}
-- {-# OPTIONS_GHC -fno-warn-unused-imports #-}
{-# OPTIONS_GHC -fno-warn-unused-binds   #-}

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

-- Whether to render to a PDF (vs print reified expression)
render :: Bool
render = True -- False

-- For FP & parallelism talk
tests :: IO [Test]
tests = return
  [ nopTest
  , test 0.5 "not" not          -- works
  , test 0.5 "foo" foo          -- crashes
  ]

foo :: Bool -> Maybe Bool
foo a = fmap id (Just a)

-- 	reification residuals:
--   [error
--      @ 'PtrRepLifted
--      @ Double
--      ((PushCallStack
--          undefined9
--          undefined2
--          (PushCallStack
--             (unpackAppendCString# "undefined"# ([] @ Char))
--             (SrcLoc
--                (unpackAppendCString#
--                   "circat-0.6.5-AmvE9jjODIwFrwiEjWMa0K"# ([] @ Char))
--                (unpackAppendCString# "Circat.Rep"# ([] @ Char))
--                (unpackAppendCString# "src/Circat/Rep.hs"# ([] @ Char))
--                (I# 142#)
--                (I# 26#)
--                (I# 142#)
--                (I# 35#))
--             EmptyCallStack))
--       `cast` (Sym (N:IP[0] <"callStack">_N <CallStack>_N)
--               :: (CallStack :: *) ~R# ((?callStack::CallStack) :: Constraint)))
--      undefined1]

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
