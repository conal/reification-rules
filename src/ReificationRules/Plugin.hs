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
data LamOps = LamOps { mkE     :: Unop Type
                     , mkReify :: Unop CoreExpr
                     , mkEval  :: Unop CoreExpr
                     , mkApp   :: Binop CoreExpr
                     , mkLam   :: String -> Unop CoreExpr
                     }

reify :: LamOps -> InScopeEnv -> CoreExpr -> Maybe CoreExpr
reify (LamOps {..}) _inScope = \ case 
  App u v -> Just $ mkApp (mkReify u) (mkReify v)
  Lam x e -> Just (mkLam (uqVarName y) (mkReify (subst [(x,mkEval (Var y))] e)))
    where
      y = setVarType x (mkE (varType x)) -- *
  e -> -- pprTrace "reify" (text "Unhandled" <+> ppr e) $
      return e

-- * Is it okay for me to reuse x's unique here? If not, let uniqAway x and then
-- setVarType. I can also avoid the issue by forming reify . f . eval, which
-- requires making *un-applied* reify & eval.

-- forall (f :: a -> b).  reify f = lam (\y. reify (f (eval y)))

{--------------------------------------------------------------------
    Plugin installation
--------------------------------------------------------------------}

#if 0
  | BuiltinRule {
        ru_name  :: RuleName,   -- ^ As above
        ru_fn    :: Name,       -- ^ As above
        ru_nargs :: Int,        -- ^ Number of arguments that 'ru_try' consumes,
                                -- if it fires, including type arguments
        ru_try   :: RuleFun
                -- ^ This function does the rewrite.  It given too many
                -- arguments, it simply discards them; the returned 'CoreExpr'
                -- is just the rewrite of 'ru_fn' applied to the first 'ru_nargs' args
    }
                -- See Note [Extra args in rule matching] in Rules.lhs

type RuleFun = DynFlags -> InScopeEnv -> Id -> [CoreExpr] -> Maybe CoreExpr
type InScopeEnv = (InScopeSet, IdUnfoldingFun)
#endif

reifyRule :: CoreM CoreRule
reifyRule = reRule <$> mkLamOps
 where
   reRule :: LamOps -> CoreRule
   reRule ops =
     BuiltinRule { ru_name = fsLit "reify"
                 , ru_fn = error "reifyRule ru_fn"
                 , ru_nargs = 1
                 , ru_try = \ _dflags inScope _fn [arg] -> reify ops inScope arg
                 }


-- Hm. RuleFun does not involve CoreM. How to generate new identifiers?
-- How does eta-expansion work?

#if 0
install :: [CommandLineOption] -> [CoreToDo] -> CoreM [CoreToDo]
install _opts todos = do
  reinitializeGlobals
  ...
  return $ CoreDoPluginPass "Reify" reifyPass : todos
#endif

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
  eTc     <- findLamTc "EP"
  appV    <- findLamId "appP"
  lamV    <- findLamId "lamP"
  reifyV  <- findLamId "reifyEP"
  evalV   <- findLamId "evalEP"
  unpackV <- lookupRdr (mkModuleName "GHC.CString") lookupId "unpackCString#"
  let unpackStr str = Var unpackV `App` Lit (mkMachString str)
  let apps v tys vals = mkCoreApps (Var v) (map Type tys ++ vals)
      mkE    ty = TyConApp eTc [ty]
      mkReify e = apps reifyV [exprType e] [e]
      mkEval  e = apps  evalV [exprType e] [e] -- WRONG! unE
      mkApp u v = apps   appV [ran,dom] [u,v]  -- note ran, dom. WRONG! unE
       where
         (dom,ran) = splitFunTy (exprType' u)
      mkLam str f = apps lamV [ran,dom] [unpackStr str,f] -- *
       where
         (dom,ran) = splitFunTy (exprType' f)
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

-- type Rewrite a = a -> CoreM a

-- type ReExpr = Rewrite CoreExpr
-- type ReType = Rewrite Type

-- type ReExpr2 = CoreExpr -> ReExpr
