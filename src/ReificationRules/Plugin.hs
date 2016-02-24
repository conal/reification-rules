{-# LANGUAGE CPP, RecordWildCards, LambdaCase, OverloadedStrings #-}
{-# OPTIONS_GHC -Wall #-}

{-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP
-- {-# OPTIONS_GHC -fno-warn-unused-binds   #-} -- TEMP

----------------------------------------------------------------------
-- |
-- Module      :  ReificationRules.Plugin
-- Copyright   :  (c) 2016 Conal Elliott
-- License     :  BSD3
--
-- Maintainer  :  conal@conal.net
-- Stability   :  experimental
-- 
-- Core reification via rewrite rules
----------------------------------------------------------------------

module ReificationRules.Plugin where

-- TODO: explicit exports

import GhcPlugins
import DynamicLoading
import TypeRep

import HERMIT.Name (newIdH)

import HERMIT.Extras (subst,exprType',uqVarName)

import LambdaCCC.Misc (Unop,Binop)

{--------------------------------------------------------------------
    Reification
--------------------------------------------------------------------}

-- Reification operations
data LamOps = LamOps { eTyCon  :: TyCon
                     , unpackV :: Id
                     , reifyV  :: Id
                     , evalV   :: Id
                     , appV    :: Id
                     , lamV    :: Id
                     }

reify :: LamOps -> DynFlags -> InScopeEnv -> CoreExpr -> Maybe CoreExpr
reify (LamOps {..}) _dflags _inScope = \ case 
  App u v | not (isTyCoArg v)
          , Just (dom,ran) <- splitFunTy_maybe (exprType' u) ->
    Just $ varApps appV [ran,dom] (mkReify <$> [u,v])  -- note ran,dom
  Lam x e | not (isTyVar x) ->
    Just $ varApps lamV [varType x, exprType' e]
             [ unpackStr (uqVarName y)
             , mkReify (subst [(x,varApps evalV [xty] [Var y])] e) ]
    where
      xty           = varType x
      y             = setVarType x (mkE xty) -- *
      unpackStr str = Var unpackV `App` Lit (mkMachString str)
  _ -> -- pprTrace "reify" (text "Unhandled" <+> ppr e) $
       Nothing
 where
   mkE ty = TyConApp eTyCon [ty]
   mkReify arg = varApps reifyV [exprType' arg] [arg]

varApps :: Id -> [Type] -> [CoreExpr] -> CoreExpr
varApps v tys es = mkCoreApps (Var v) (map Type tys ++ es)

-- * Is it okay for me to reuse x's unique here? If not, use uniqAway x and then
-- setVarType. I can also avoid the issue by forming reify . f . eval. I could
-- include the Id for (.) in LamOps. Or bundle reify <~ eval as reifyFun.

-- forall (f :: a -> b).  reify f = lam (\y. reify (f (eval y)))

{--------------------------------------------------------------------
    Plugin installation
--------------------------------------------------------------------}

#if 0
  | BuiltinRule {
        ru_name  :: RuleName,   -- ^ As above
        ru_fn    :: Name,       -- ^ As above
        ru_nargs :: Int,        -- ^ Number of arguments that 'ru_try' consumes
        ru_try   :: RuleFun
    }

type RuleFun = DynFlags -> InScopeEnv -> Id -> [CoreExpr] -> Maybe CoreExpr
type InScopeEnv = (InScopeSet, IdUnfoldingFun)
#endif

mkReifyRule :: CoreM CoreRule
mkReifyRule = reRule <$> mkLamOps
 where
   reRule :: LamOps -> CoreRule
   reRule ops =
     BuiltinRule { ru_name  = fsLit "reify"
                 , ru_fn    = varName (reifyV ops)
                 , ru_nargs = 1
                 , ru_try   = \ dflags inScope _fn [arg] ->
                                 reify ops dflags inScope arg
                 }

install :: [CommandLineOption] -> [CoreToDo] -> CoreM [CoreToDo]
install _opts todos = do
  reinitializeGlobals
  rr <- mkReifyRule
  let reifyPass = pure . on_mg_rules (rr :)
  return $ CoreDoPluginPass "Reify" reifyPass : todos

mkLamOps :: CoreM LamOps
mkLamOps = do
  hsc_env <- getHscEnv
  let lookupRdr :: ModuleName -> (Name -> CoreM a) -> String -> CoreM a
      lookupRdr modu mk str =
        maybe (panic ("reify installation: couldn't find " ++ str)) mk =<<
          liftIO (lookupRdrNameInModuleForPlugins hsc_env modu (mkVarUnqual (fsLit str)))
      lookupLam = lookupRdr (mkModuleName "LambdaCCC.Lambda")
      findLamTc = lookupLam lookupTyCon
      findLamId = lookupLam lookupId    
  eTyCon  <- findLamTc "EP"
  unpackV <- lookupRdr (mkModuleName "GHC.CString") lookupId "unpackCString#"
  reifyV  <- findLamId "reifyEP"
  evalV   <- findLamId "evalEP"
  appV    <- findLamId "appP"
  lamV    <- findLamId "lamP"
  return (LamOps { .. })

-- * I'm assuming changes to lamP: note ran, dom. check.
-- 
--   lamP :: forall b a. String -> (E a -> E b) -> E (a -> b)
-- 
-- The string is a name suggestion. Choose name to avoid shadowing.
-- I could instead pass in a fqVarName and use the name given.

{--------------------------------------------------------------------
    Misc
--------------------------------------------------------------------}

on_mg_rules :: Unop [CoreRule] -> Unop ModGuts
on_mg_rules f mg = mg { mg_rules = f (mg_rules mg) }
