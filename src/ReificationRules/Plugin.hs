{-# LANGUAGE CPP, RecordWildCards, LambdaCase #-}
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

import HERMIT.Extras (subst,exprType')

import LambdaCCC.Misc (Unop,Binop)


-- Reification operations
data LamOps = LamOps { mkE     :: Unop  Type
                     , mkReify :: Unop  CoreExpr
                     , mkEval  :: Unop  CoreExpr
                     , mkApp   :: Binop CoreExpr
                     , mkLam   :: Unop CoreExpr
                     }

reify :: LamOps -> ReExpr
reify (LamOps {..}) = \ case 
  App u v -> return $ mkApp (mkReify u) (mkReify v)
  Lam x e -> do y <- newIdH "y" (mkE (varType x))
                return $ mkLam (mkReify (subst [(x,mkEval (Var y))] e))
  e -> -- pprTrace "reify" (text "Unhandled" <+> ppr e) $
      return e

-- forall (f :: a -> b).  reify f = lam (\y. reify (f (eval y)))

{--------------------------------------------------------------------
    Plugin installation
--------------------------------------------------------------------}

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
  eTc    <- findLamTc "EP"
  appV   <- findLamId "appP"
  lamV   <- findLamId "lamP"
  reifyV <- findLamId "reifyEP"
  evalV  <- findLamId "evalEP"
  let apps v tys vals = mkCoreApps (Var v) (map Type tys ++ vals)
      mkE    ty = TyConApp eTc [ty]
      mkReify e = apps reifyV [exprType e] [e]
      mkEval  e = apps  evalV [exprType e] [e]
      mkApp u v = apps   appV [ran,dom] [u,v]  -- note ran, dom
       where
         (dom,ran) = splitFunTy (exprType' u)
      mkLam f = apps lamV [ran,dom] [f] -- note ran, dom. check.
       where
         (dom,ran) = splitFunTy (exprType' f)
  return (LamOps { .. })

{--------------------------------------------------------------------
    Misc
--------------------------------------------------------------------}

type Rewrite a = a -> CoreM a

type ReExpr = Rewrite CoreExpr
type ReType = Rewrite Type

-- type ReExpr2 = CoreExpr -> ReExpr
