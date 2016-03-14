{-# LANGUAGE CPP #-}
{-# LANGUAGE TypeOperators, ExistentialQuantification, FlexibleContexts #-}
{-# LANGUAGE ConstraintKinds, StandaloneDeriving, ViewPatterns #-}

-- Okay
{-# LANGUAGE FlexibleInstances, UndecidableInstances #-}

{-# OPTIONS_GHC -Wall #-}

-- {-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP
-- {-# OPTIONS_GHC -fno-warn-unused-binds   #-} -- TEMP

----------------------------------------------------------------------
-- |
-- Module      :  Run
-- Copyright   :  (c) 2016 Conal Elliott
-- 
-- Maintainer  :  conal@tabula.com
-- Stability   :  experimental
-- 
-- Run a test: reify, CCC, circuit
----------------------------------------------------------------------

-- {-# OPTIONS_GHC -ddump-rules #-}

module ReificationRules.Run
  ( Okay, go,go',goSep,run,runSep,goM,goM',goMSep, reify
  ) where

-- TODO: clean up interfaces.

import Prelude

import Control.Monad (when)

import ReificationRules.FOS (EP,reifyP,renameVars)
import ReificationRules.ToCCC (toCCC)

import Circat.Category (Uncurriable)
import Circat.Circuit (Attr,mkGraph,UU,writeDot,displayDot,unitize',(:>))

import Circat.Netlist (saveAsVerilog)
import Circat.Mealy (Mealy(..))

import Circat.Mealy (asFun)

ranksep :: Double -> Attr
ranksep n = ("ranksep",show n)

type Okay = Uncurriable (:>) ()

reify :: a -> EP a
reify a = error "reify: not implemented" a
-- reify f = renameVars (reifyP f)
{-# NOINLINE reify #-}

go :: Okay a => String -> a -> IO ()
go = error "go: not implemented"
-- go name = go' name []
{-# NOINLINE go #-}

go' :: Okay a => String -> [Attr] -> a -> IO ()
go' = error "go': not implemented"
-- go' name attrs f = run name attrs (reifyP f)
{-# NOINLINE go' #-}

goSep :: Okay a => String -> Double -> a -> IO ()
goSep = error "goSep: not implemented"
-- goSep name s = go' name [ranksep s]
{-# NOINLINE goSep #-}

-- Experimenting with rules instead of INLINE.

{-# RULES

"reify & rename" forall f. reify f = renameVars (reifyP f)

"go" forall name f. go name f = run name [] (reify f)

-- "go"    forall name         . go name          = go' name []

"go'"   forall name attrs f . go' name attrs f = run name attrs (reify f)

"goSep" forall name s       . goSep name s     = go' name [ranksep s]

 #-}

genVerilog :: Bool
genVerilog = False

genPdf :: Bool
genPdf = True

showPretty :: Bool
showPretty = True

showGraph :: Bool
showGraph = False

-- Run an example: reify, CCC, circuit.
run :: Okay a => String -> [Attr] -> EP a -> IO ()
run name attrs e = do when showPretty $ putStrLn (name ++ " = " ++ show e)
                      outGV name attrs (unitize' (toCCC e))
{-# NOINLINE run #-}

runSep :: Okay a => String -> Double -> EP a -> IO ()
runSep name s = run name [ranksep s]

-- Diagram and Verilog
outGV :: String -> [Attr] -> UU -> IO ()
outGV name attrs circ =
  do when showGraph $ putStrLn $ "outGV: Graph \n" ++ show g
     writeDot attrs g
     when genPdf $ displayDot ("pdf","") name
     -- displayDot ("svg","") 
     -- displayDot ("png","-Gdpi=200")
     when genVerilog $ saveAsVerilog g
 where
   g = mkGraph name circ
{-# NOINLINE outGV #-}

-- TODO: Move file-saving code from outD and saveVerilog to here.

{--------------------------------------------------------------------
    State machines
--------------------------------------------------------------------}

goM :: Okay (a -> b) => String -> Mealy a b -> IO ()
goM name = goM' name []
{-# INLINE goM #-}

goMSep :: Okay (a -> b) => String -> Double -> Mealy a b -> IO ()
goMSep name s = goM' name [ranksep s]
{-# INLINE goMSep #-}

goM' :: Okay (a -> b) => String -> [Attr] -> Mealy a b -> IO ()
{-# INLINE goM' #-}

goM' name attrs = go' name attrs . asFun
