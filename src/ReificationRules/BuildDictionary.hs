{-# LANGUAGE CPP #-}
{-# OPTIONS_GHC -Wall #-}

-- {-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP
-- {-# OPTIONS_GHC -fno-warn-unused-binds   #-} -- TEMP

----------------------------------------------------------------------
-- |
-- Module      :  ReificationRules.BuildDictionary
-- Copyright   :  (c) 2016 Conal Elliott
-- License     :  BSD3
--
-- Maintainer  :  conal@conal.net
-- Stability   :  experimental
-- 
-- Adaptation of HERMIT's buildDictionaryT
----------------------------------------------------------------------

module ReificationRules.BuildDictionary where

-- TODO: explicit exports

import System.IO.Unsafe (unsafePerformIO)

import GhcPlugins
-- import DynamicLoading
-- import Kind (isLiftedTypeKind)
-- import Type (coreView)
-- import TcType (isIntegerTy)

#if __GLASGOW_HASKELL__ > 710 
import Control.Arrow (second)
import           TcRnMonad (getCtLocM)
import           TcRnTypes (cc_ev)
import TcSMonad (runTcS)
import TcEvidence (evBindMapBinds)
#else
import           TcRnMonad (getCtLoc)
#endif

import DsMonad
import DsBinds
import           TcSimplify
import           TcRnTypes
import ErrUtils (pprErrMsgBagWithLoc)

import HERMIT.GHC.Typechecker (initTcFromModGuts)

runTcM :: ModGuts -> TcM a -> CoreM a
runTcM guts m = do
    env <- getHscEnv
    dflags <- getDynFlags
    -- What is the effect of HsSrcFile (should we be using something else?)
    -- What should the boolean flag be set to?
    (msgs, mr) <- liftIO $ initTcFromModGuts env guts HsSrcFile False m
    let showMsgs (warns, errs) = showSDoc dflags $ vcat
                                                 $    text "Errors:" : pprErrMsgBagWithLoc errs
                                                   ++ text "Warnings:" : pprErrMsgBagWithLoc warns
    maybe (fail $ showMsgs msgs) return mr

runDsM :: ModGuts -> DsM a -> CoreM a
runDsM guts = runTcM guts . initDsTc

runTcMUnsafe :: HscEnv -> DynFlags -> ModGuts -> TcM a -> a
runTcMUnsafe env dflags guts m = unsafePerformIO $ do
    -- What is the effect of HsSrcFile (should we be using something else?)
    -- What should the boolean flag be set to?
    (msgs, mr) <- initTcFromModGuts env guts HsSrcFile False m
    let showMsgs (warns, errs) = showSDoc dflags $ vcat
                                                 $    text "Errors:" : pprErrMsgBagWithLoc errs
                                                   ++ text "Warnings:" : pprErrMsgBagWithLoc warns
    maybe (fail $ showMsgs msgs) return mr

runDsMUnsafe :: HscEnv -> DynFlags -> ModGuts -> DsM a -> a
runDsMUnsafe env dflags guts = runTcMUnsafe env dflags guts . initDsTc

-- | Build a dictionary for the given
buildDictionary :: HscEnv -> DynFlags -> ModGuts -> Id -> (Id, [CoreBind])
buildDictionary env dflags guts evar =
    let (i, bs) = runTcMUnsafe env dflags guts $ do
#if __GLASGOW_HASKELL__ > 710 
        loc <- getCtLocM (GivenOrigin UnkSkol) Nothing
#else
        loc <- getCtLoc $ GivenOrigin UnkSkol
#endif
        let predTy = varType evar
#if __GLASGOW_HASKELL__ > 710 
            nonC = mkNonCanonical $ CtWanted { ctev_pred = predTy, ctev_dest = EvVarDest evar, ctev_loc = loc }
            wCs = mkSimpleWC [cc_ev nonC]
        -- TODO: Make sure solveWanteds is the right function to call.
        (_wCs', bnds) <- second evBindMapBinds <$> runTcS (solveWanteds wCs)
#else
            nonC = mkNonCanonical $ CtWanted { ctev_pred = predTy, ctev_evar = evar, ctev_loc = loc }
            wCs = mkSimpleWC [nonC]
        (_wCs', bnds) <- solveWantedsTcM wCs
#endif
        -- reportAllUnsolved _wCs' -- this is causing a panic with dictionary instantiation
                                  -- revist and fix!
        return (evar, bnds)
    in
      (i, runDsMUnsafe env dflags guts (dsEvBinds bs))

#if 1

#endif
