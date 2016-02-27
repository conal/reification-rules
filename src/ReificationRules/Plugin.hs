{-# LANGUAGE CPP               #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternGuards     #-}
{-# LANGUAGE RecordWildCards   #-}
{-# LANGUAGE ViewPatterns      #-}

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

module ReificationRules.Plugin (plugin) where

import Control.Applicative ((<|>))
import Control.Monad (guard)
import Data.Maybe (fromMaybe)

import GhcPlugins
import DynamicLoading
import Kind (isLiftedTypeKind)
import Type (coreView)
import TcType (isIntegerTy)

{--------------------------------------------------------------------
    Reification
--------------------------------------------------------------------}

-- #define UseFos

-- Reification operations
data LamOps = LamOps { unpackV :: Id
#ifdef UseFos
                     , varV    :: Id
#endif
                     , appV    :: Id
                     , lamV    :: Id
                     , reifyV  :: Id
                     , evalV   :: Id
                     }

-- TODO: drop reifyV, since it's in the rule
-- TODO: drop unpackV, since I'll probably replace String by Addr# for names.

-- #define Tracing

traceRewrite :: (Outputable a, Outputable b, Functor f) =>
                String -> Unop (a -> f b)
#ifdef Tracing
traceRewrite str f a = tr <$> f a
 where
   tr b = pprTrace str (ppr a <+> text "-->" <+> ppr b) b
#else
traceRewrite _ = id
#endif

reify :: LamOps -> DynFlags -> InScopeEnv -> CoreExpr -> Maybe CoreExpr
reify (LamOps {..}) _dflags _inScope = traceRewrite "reify go" go
 where
   go :: CoreExpr -> Maybe CoreExpr
   go = \ case 
     e | pprTrace "reify go:" (ppr e) False -> undefined
     App u v | not (isTyCoArg v)
             , Just (dom,ran) <- splitFunTy_maybe (exprType u) ->
       varApps appV [dom,ran] <$> mapM tryReify [u,v]
   #ifdef UseFos
     Lam x e | not (isTyVar x) ->
       do e' <- tryReify (subst1 x (varApps evalV [xty] [varApps varV [xty] [ystr]]) e)
          return $ varApps lamV [varType x, exprType e] [ystr, e']
      where
        xty  = varType x
        ystr = stringExpr (uniqVarName x)
   #else
     Lam x e | not (isTyVar x) ->
       do e' <- tryReify (subst1 x (varApps evalV [xty] [Var y]) e)
          return $ varApps lamV [xty, exprType e]
                     [stringExpr (uqVarName y), Lam y e']
       where
         xty           = varType x
         y             = setVarType x (exprType (mkReify (Var x)))
                         -- setVarType x (mkE xty) -- *
   #endif
     _e -> pprTrace "reify" (text "Unhandled:" <+> ppr _e) $
           Nothing
    where
      stringExpr :: String -> CoreExpr
      stringExpr str = {- Var unpackV `App` -} Lit (mkMachString str)
      mkReify :: CoreExpr -> CoreExpr
      mkReify e = varApps reifyV [exprType e] [e]
      tryReify :: CoreExpr -> Maybe CoreExpr
      -- tryReify e | pprTrace "tryReify" (ppr e) False = undefined
      -- tryReify e = guard (reifiableExpr e) >> (go e <|> Just (mkReify e))
      tryReify e | reifiableExpr e = go e <|> Just (mkReify e)
                 | otherwise = pprTrace "Not reifiable:" (ppr e) Nothing

-- TODO: Replace unpackV by unpackStr in LamOps.

-- * Is it safe to reuse x's unique here? If not, use uniqAway x and then
-- setVarType. I can also avoid the issue by forming reify . f . eval. I could
-- include the Id for (.) in LamOps. Or bundle reify <~ eval as reifyFun.

varApps :: Id -> [Type] -> [CoreExpr] -> CoreExpr
varApps v tys es = mkApps (Var v) (map Type tys ++ es)

reifiableKind :: Kind -> Bool
reifiableKind = isLiftedTypeKind

-- reifiableType :: Type -> Bool
-- reifiableType ty = reifiableKind (typeKind ty)

-- Types we know how to handle
reifiableType :: Type -> Bool
reifiableType (coreView -> Just ty) = reifiableType ty
reifiableType (splitFunTy_maybe -> Just (dom,ran)) = reifiableType dom && reifiableType ran
reifiableType ty = not (or (($ ty) <$> bads))
 where
   bads = [ isForAllTy
          , not . reifiableKind . typeKind
          , isPredTy
          , badTyConApp
          , badTyConArg
          ]

badTyConArg :: Type -> Bool
badTyConArg (coreView -> Just ty)             = badTyConArg ty
badTyConArg (tyConAppArgs_maybe -> Just args) = not (all reifiableType args)
badTyConArg _                                 = False

badTyConApp :: Type -> Bool
-- badTyConApp ty | pprTrace "badTyConApp try" (ppr ty) False = undefined
badTyConApp (coreView -> Just ty)            = badTyConApp ty
badTyConApp (tyConAppTyCon_maybe -> Just tc) = badTyCon tc
badTyConApp _                                = False

badTyCon :: TyCon -> Bool
-- badTyCon tc | pprTrace "badTyCon try" (ppr tc <+> text (qualifiedName (tyConName tc))) False = undefined
badTyCon tc = qualifiedName (tyConName tc) `elem`
  [ "GHC.Integer.Type"
  , "GHC.Types.[]"
  , "GHC.Types.IO"
  , "ReificationRules.Exp.E"
  ]

-- ReificationRules.Exp.E

reifiableExpr :: CoreExpr -> Bool
reifiableExpr e = not (isTyCoArg e) && reifiableType (exprType e)

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
      lookupHos = lookupRdr (mkModuleName
#ifdef UseFos
                             "ReificationRules.FOS"
#else
                             "ReificationRules.HOS"
#endif
                            )
      findHosId = lookupHos lookupId
  unpackV <- lookupRdr (mkModuleName "GHC.CString") lookupId "unpackCString#"
#ifdef UseFos
  varV    <- findHosId "varP"
#endif
  appV    <- findHosId "appP"
  lamV    <- findHosId "lamP"
  reifyV  <- findHosId "reifyP"
  evalV   <- findHosId "evalP"
  return (LamOps { .. })

{--------------------------------------------------------------------
    Misc
--------------------------------------------------------------------}

on_mg_rules :: Unop [CoreRule] -> Unop ModGuts
on_mg_rules f mg = mg { mg_rules = f (mg_rules mg) }

type Unop a = a -> a

#ifdef UseFos
uniqVarName :: Var -> String
uniqVarName v = uqVarName v ++ "_" ++ show (varUnique v)
#endif

uqVarName :: Var -> String
uqVarName = getOccString . varName

-- Swiped from HERMIT.GHC
-- | Get the fully qualified name from a 'Name'.
qualifiedName :: Name -> String
qualifiedName nm = modStr ++ getOccString nm
    where modStr = maybe "" (\m -> moduleNameString (moduleName m) ++ ".") (nameModule_maybe nm)

-- | Substitute new subexpressions for variables in an expression
subst :: [(Id,CoreExpr)] -> Unop CoreExpr
subst ps = substExpr (error "subst: no SDoc") (foldr add emptySubst ps)
 where
   add (v,new) sub = extendIdSubst sub v new

subst1 :: Id -> CoreExpr -> Unop CoreExpr
subst1 v e = subst [(v,e)]
