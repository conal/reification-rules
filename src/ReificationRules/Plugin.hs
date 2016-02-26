{-# LANGUAGE CPP               #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternGuards     #-}
{-# LANGUAGE RecordWildCards   #-}

{-# OPTIONS_GHC -Wall #-}

-- {-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP
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

module ReificationRules.Plugin (plugin) where

import GhcPlugins
import DynamicLoading

{--------------------------------------------------------------------
    Reification
--------------------------------------------------------------------}

-- Reification operations
data LamOps = LamOps { unpackV :: Id
                     , reifyV  :: Id
                     , evalV   :: Id
                     , appV    :: Id
                     , lamV    :: Id
                     }

#define Tracing
traceRewrite :: (Outputable a, Outputable b) =>
                String -> Unop (a -> Maybe b)
#ifdef Tracing
traceRewrite str f a = fmap tr (f a)
 where
   tr b = pprTrace str (ppr a <+> text "-->" <+> ppr b) b
#else
traceRewrite = id
#endif

reify :: LamOps -> DynFlags -> InScopeEnv -> CoreExpr -> Maybe CoreExpr
reify (LamOps {..}) _dflags _inScope = traceRewrite "reify" $ \ case 
  e | pprTrace "reify" (ppr e) False -> undefined
  App u v | not (isTyCoArg v)
          , Just (dom,ran) <- splitFunTy_maybe (exprType u) ->
    Just $ varApps appV [dom,ran] (mkReify <$> [u,v])
  Lam x e | not (isTyVar x) ->
    Just $ varApps lamV [varType x, exprType e]
             [ unpackStr (uqVarName y) -- later, uqVarName & HOAS
             , mkReify (subst [(x,varApps evalV [xty] [Var y])] e) ]
    where
      xty           = varType x
      y             = setVarType x (exprType (mkReify (Var x)))
                      -- setVarType x (mkE xty) -- *
      unpackStr str = Var unpackV `App` Lit (mkMachString str)
  _ -> -- pprTrace "reify" (text "Unhandled" <+> ppr e) $
       Nothing
 where
   mkReify arg = varApps reifyV [exprType arg] [arg]

-- * Is it safe to reuse x's unique here? If not, use uniqAway x and then
-- setVarType. I can also avoid the issue by forming reify . f . eval. I could
-- include the Id for (.) in LamOps. Or bundle reify <~ eval as reifyFun.

varApps :: Id -> [Type] -> [CoreExpr] -> CoreExpr
varApps v tys es = mkCoreApps (Var v) (map Type tys ++ es)

{--------------------------------------------------------------------
    Plugin installation
--------------------------------------------------------------------}

mkReifyRule :: CoreM CoreRule
mkReifyRule = reRule <$> mkLamOps
 where
   reRule :: LamOps -> CoreRule
   reRule ops =
     BuiltinRule { ru_name  = fsLit "reify"
                 , ru_fn    = varName (reifyV ops)
                 , ru_nargs = 2  -- including type arg
                 , ru_try   = \ dflags inScope _fn [_ty,arg] ->
                                 reify ops dflags inScope arg
                 }

plugin :: Plugin
plugin = defaultPlugin { installCoreToDos = install }

install :: [CommandLineOption] -> [CoreToDo] -> CoreM [CoreToDo]
install _opts todos =
  do reinitializeGlobals
     rr <- mkReifyRule
     -- For now, just insert the rule.
     -- TODO: add "reify_" bindings and maybe rules.
     pprTrace "plugin install" (ppr rr) (return ())
     let pass = pure . on_mg_rules (rr :)
     return $ CoreDoPluginPass "Reify insert rule" pass : todos

mkLamOps :: CoreM LamOps
mkLamOps = do
  hsc_env <- getHscEnv
  let lookupRdr :: ModuleName -> (Name -> CoreM a) -> String -> CoreM a
      lookupRdr modu mk str =
        maybe (panic err) mk =<<
          liftIO (lookupRdrNameInModuleForPlugins hsc_env modu
                     (mkVarUnqual (fsLit str)))
       where
         err = "reify installation: couldn't find "
               ++ str ++ " in " ++ moduleNameString modu
      lookupHos = lookupRdr (mkModuleName "ReificationRules.HOS")
      findHosId = lookupHos lookupId
  unpackV <- lookupRdr (mkModuleName "GHC.CString") lookupId "unpackCString#"
  reifyV  <- findHosId "reifyP"
  evalV   <- findHosId "evalP"
  appV    <- findHosId "appP"
  lamV    <- findHosId "lamP"
  return (LamOps { .. })

{--------------------------------------------------------------------
    Misc
--------------------------------------------------------------------}

on_mg_rules :: Unop [CoreRule] -> Unop ModGuts
on_mg_rules f mg = mg { mg_rules = f (mg_rules mg) }

type Unop a = a -> a

uqVarName :: Var -> String
uqVarName = getOccString . varName

-- | Substitute new subexpressions for variables in an expression
subst :: [(Id,CoreExpr)] -> Unop CoreExpr
subst ps = substExpr (error "subst: no SDoc") (foldr add emptySubst ps)
 where
   add (v,new) sub = extendIdSubst sub v new
