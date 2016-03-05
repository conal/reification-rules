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

module ReificationRules.BuildDictionary (buildDictionary,mkEqBox) where

-- TODO: explicit exports

import Control.Monad (guard)
import Data.Char (isSpace)
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
import TysWiredIn (heqDataCon)
import Pair (Pair(..))
#else
import           TcRnMonad (getCtLoc)
#endif

import DsMonad
import DsBinds
import           TcSimplify
import           TcRnTypes
import ErrUtils (pprErrMsgBagWithLoc)
import Encoding (zEncodeString)
import Unique (mkUniqueGrimily)

import HERMIT.GHC.Typechecker (initTcFromModGuts)

runTcMUnsafe :: HscEnv -> DynFlags -> ModGuts -> TcM a -> a
runTcMUnsafe env dflags guts m = unsafePerformIO $ do
    -- What is the effect of HsSrcFile (should we be using something else?)
    -- What should the boolean flag be set to?
    (msgs, mr) <- initTcFromModGuts env guts HsSrcFile False m
    let showMsgs (warns, errs) = showSDoc dflags $ vcat
                                                 $    text "Errors:" : pprErrMsgBagWithLoc errs
                                                   ++ text "Warnings:" : pprErrMsgBagWithLoc warns
    maybe (fail $ showMsgs msgs) return mr

-- TODO: Try initTcForLookup or initTcInteractive in place of initTcFromModGuts.
-- If successful, drop dflags and guts arguments.

runDsMUnsafe :: HscEnv -> DynFlags -> ModGuts -> DsM a -> a
runDsMUnsafe env dflags guts = runTcMUnsafe env dflags guts . initDsTc

-- | Build a dictionary for the given
buildDictionary' :: HscEnv -> DynFlags -> ModGuts -> Id -> (Id, [CoreBind])
buildDictionary' env dflags guts evar =
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
                                  -- revisit and fix!
        return (evar, bnds)
    in
      (i, runDsMUnsafe env dflags guts (dsEvBinds bs))

-- TODO: Why return the given evar?

-- TODO: Try to combine the two runTcMUnsafe calls.

buildDictionary :: HscEnv -> DynFlags -> ModGuts -> InScopeEnv -> Type -> Maybe CoreExpr
buildDictionary env dflags guts inScope ty =
  do guard (notNull bnds)
     return $
       case bnds of
         -- The common case that we would have gotten a single non-recursive let
         [NonRec v e] | i == v -> e
         _                     -> mkCoreLets bnds (varToCoreExpr i)
 where
   binder   = localId inScope
                ("$d" ++ zEncodeString (filter (not . isSpace) (showPpr dflags ty))) ty
   (i,bnds) = buildDictionary' env dflags guts binder

-- | Make a unique identifier for a specified type, using a provided name.
localId :: InScopeEnv -> String -> Type -> Id
localId (inScopeSet,_) str ty =
  uniqAway inScopeSet (mkLocalId (stringToName str) ty)

stringToName :: String -> Name
stringToName str =
  mkSystemVarName (mkUniqueGrimily (fromIntegral (hashString str)))
                  (mkFastString str)

#if __GLASGOW_HASKELL__ > 710 

-- Modified definition from GHC 7.8.2:
-- This take a ~# b (or a ~# R b) and returns a ~ b (or Coercible a b)
mkEqBox :: Coercion -> CoreExpr
mkEqBox co = -- ASSERT2( typeKind ty2 `eqKind` k, ppr co $$ ppr ty1 $$ ppr ty2 $$ ppr (typeKind ty1) $$ ppr (typeKind ty2) )
             Var (dataConWorkId datacon) `mkTyApps` [k1, k2, ty1, ty2] `App` Coercion co
  where Pair ty1 ty2 = coercionKind co
        k1 = typeKind ty1
        k2 = typeKind ty2
        datacon = case coercionRole co of 
            Nominal ->          heqDataCon
            Representational -> coercibleDataCon
            Phantom ->          pprPanic "mkEqBox does not support boxing phantom coercions"
                                         (ppr co)

-- (~~) :: forall k1 k2. k1 -> k2 -> Constraint

-- Adapted from mkHEqBoxTy in GHC's Inst module

-- -- | This takes @a ~# b@ and returns @a ~~ b@.
-- mkHEqBoxTy :: Coercion -> Type -> Type -> Type
-- mkHEqBoxTy co ty1 ty2 =
--   mkTyConApp (promoteDataCon heqDataCon)
--              [typeKind ty1, typeKind ty2, ty1, ty2, mkCoercionTy co]

#if 0

-- | This takes @a ~# b@ and returns @a ~ b@.
mkEqBoxTy :: Coercion -> Type -> Type -> TcM Type
mkEqBoxTy co ty1 ty2
  = do { eq_tc <- tcLookupTyCon eqTyConName
       ; let [datacon] = tyConDataCons eq_tc
       ; hetero <- mkHEqBoxTy co ty1 ty2
       ; return $ mkTyConApp (promoteDataCon datacon) [k, ty1, ty2, hetero] }
  where k = typeKind ty1

#endif

#endif
