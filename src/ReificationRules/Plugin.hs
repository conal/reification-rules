{-# LANGUAGE CPP               #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternGuards     #-}
{-# LANGUAGE PatternSynonyms   #-}
{-# LANGUAGE RecordWildCards   #-}
{-# LANGUAGE ViewPatterns      #-}

{-# OPTIONS_GHC -Wall #-}

{-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP
{-# OPTIONS_GHC -fno-warn-unused-binds   #-} -- TEMP

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

import Control.Arrow (first,second)
import Control.Applicative (liftA2,(<|>))
import Control.Monad (unless,guard,(<=<))
import Data.Maybe (fromMaybe,isJust)
import Data.List (stripPrefix,isPrefixOf,isSuffixOf)
import Data.Char (toLower)
import qualified Data.Map as M
import qualified Data.Set as S
import Text.Printf (printf)

import System.IO.Unsafe (unsafePerformIO)

import GhcPlugins
import CoreArity (etaExpand)
import CoreLint (lintExpr)
import CoreSeq (seqExpr)
import DynamicLoading
import Kind (isLiftedTypeKind)
import Pair (Pair(..))
import Type (coreView,mkAppTy)
import TcType (isIntegerTy)
import FamInstEnv (normaliseType)
import SimplCore (simplifyExpr)
import TyCoRep                          -- TODO: explicit imports

import ReificationRules.Misc (Unop,Binop)
import ReificationRules.BuildDictionary (buildDictionary,mkEqBox)
import ReificationRules.Simplify (simplifyE)

{--------------------------------------------------------------------
    Reification
--------------------------------------------------------------------}

-- Information needed for reification. We construct this info in
-- CoreM and use it in the reify rule, which must be pure.
data ReifyEnv = ReifyEnv { varV       :: Id
                         , appV       :: Id
                         , lamV       :: Id
                         , letV       :: Id
                         , letPairV   :: Id
                         , reifyV     :: Id
                         , evalV      :: Id
                         , primFun    :: PrimFun
                         , isPrim     :: Id -> Bool
                         , abstV      :: Id
                         , reprV      :: Id
                         , abst'V     :: Id
                         , repr'V     :: Id
                         , abstPV     :: Id
                         , reprPV     :: Id
                         , fstV       :: Id
                         , sndV       :: Id
                         , idV        :: Id
                         , composeV   :: Id
                         , prePostV   :: Id
                         , hasRepMeth :: HasRepMeth
                         , hasLit     :: HasLit
                         , expTy      :: Type
                         , tracing    :: Bool
                         }

-- TODO: Perhaps drop reifyV, since it's in the rule

-- TODO: try replacing the identifiers with convenient functions that use them,
-- thus shifting some complexity from reify to mkReifyEnv. 

-- Whether to run Core Lint after every step
lintSteps :: Bool
lintSteps = True -- False

-- Keep this one False for simplifier synergy.
recursively :: Bool
recursively = False -- True

type Rewrite a = a -> Maybe a
type ReExpr = Rewrite CoreExpr

-- Apply a rewrite, lint the result, and check that the type is preserved.
lintReExpr :: DynFlags -> Type -> Unop ReExpr
lintReExpr dflags expTy rew before | lintSteps =
  do after <- rew before
     let oops str doc = pprPanic ("reify post-transfo check. " ++ str)
                          (doc <> ppr before $$ text "-->" $$ ppr after)
         beforeTy = mkAppTy expTy (exprType before)
         afterTy  = exprType after
     maybe (if beforeTy `eqType` afterTy then
              return after
            else
              oops "type change" (ppr beforeTy <+> text "vs" <+> ppr afterTy
                                  <+> text "in" $$ text ""))
           (oops "Lint" empty)
       (lintExpr dflags (varSetElems (exprFreeVars before)) before)
lintReExpr _ _ rew before = rew before

-- #define AboutTo(str) e | dtrace ("About to " ++ (str)) (e `seq` empty) False -> undefined

#define AboutTo(str)

-- Use of e in a dtrace argument prevents the dtrace call from getting hoisted.

reify :: ReifyEnv -> ModGuts -> DynFlags -> InScopeEnv -> ReExpr
reify (ReifyEnv {..}) guts dflags inScope =
  traceRewrite "reify" $
  lintReExpr dflags expTy $
  go
 where
   go :: ReExpr
   go = \ case 
     -- e | dtrace "reify go:" (ppr e) False -> undefined
     -- lamP :: forall a b. Name# -> EP b -> EP (a -> b)
     -- (\ x -> e) --> lamP "x" e[x/eval (var "x")]
     AboutTo("lambda")
     Lam x e | not (isTyVar x) ->
       -- TODO: maybe use mkVarEvald
       do let x' = varApps varV [xty] [str]
          e' <- tryReify (subst1 x (varApps evalV [xty] [x']) e)
          return $ varApps lamV [xty, exprType e] [str, e']
       where
         str = stringExpr (uniqVarName y)
         xty = varType x
         y   = zapIdOccInfo $ setVarType x (exprType (mkReify (Var x))) -- *
     AboutTo("let")
     Let (NonRec v rhs) body
        | not (reifiableExpr rhs) || cheap rhs -> Let (NonRec v rhs) <$> tryReify body
       -- | isEvalVar rhs -> go (subst1 v rhs body)
       -- The not.isEvalVar test prevents a simplifier loop that keeps
       -- let-abstracting terms of the form evalP (varP x). The immediate go
       -- delays GHC re-hoisting long enough to avoid an infinite loop. See
       -- journal entry 2016-03-15.
        | otherwise ->
#if 0
          go (Lam v body `App` rhs)
#else
          -- Alternatively use letP. Works as well but more complicated.
          -- letP :: forall a b. Name# -> EP a -> EP b -> EP b
          let (name,evald) = mkVarEvald v in
            liftA2 (\ rhs' body' -> varApps letV [exprType rhs, exprType body]
                                      [name,rhs',body'])
                   (tryReify rhs)
                   (tryReify (subst1 v evald body))
#endif
     AboutTo("case-of-cast")
     Case (Cast e co) wild ty alts ->
       do scrut' <- (`App` e) <$> recast co
          tryReify (Case scrut' wild ty alts)
     AboutTo("case-of-case")
     e@(Case (Case {}) _ _ _) -> tryReify (simplE False e) -- still necessary?
     AboutTo("pair scrutinee")
     e@(Case scrut wild rhsTy [(DataAlt dc, [a,b], rhs)])
         | isBoxedTupleTyCon (dataConTyCon dc)
         , reifiableExpr rhs ->
       do -- To start, require v to be unused. Later, extend.
          unless (isDeadBinder wild) $
            pprPanic "reify - case with live wild var (not yet handled)" (ppr e)
          -- TODO: handle live wild var.
          -- letPairP :: forall a b c. Name# -> Name# -> EP (a :* b) -> EP c -> EP c
          liftA2 (\ rhs' scrut' -> varApps letPairV [varType a, varType b, rhsTy]
                                     [nameA,nameB,scrut',rhs'])
                 (tryReify (subst [(a,evalA),(b,evalB)] rhs))
                 (tryReify scrut)
      where
        (nameA,evalA) = mkVarEvald a
        (nameB,evalB) = mkVarEvald b
     AboutTo("abstReprCase")
     Case scrut v altsTy alts
       | not (alreadyAbstReprd scrut)
       , Just meth <- hrMeth scrut
       -> tryReify $ -- go  -- Less chatty with go
          Case (meth abst'V `App` (meth reprV `App` scrut)) v altsTy alts
     AboutTo("unfold scrutinee")
     Case scrut v altsTy alts
       | Just scrut' <- unfoldMaybe scrut
       -> tryReify $ Case scrut' v altsTy alts
     AboutTo("cast")
     Cast e co -> tryReify =<< (`App` e) <$> recast co
     AboutTo("repMeth <+ lit")
     (repMeth <+ lit -> Just e) -> Just e
     AboutTo("abstReprCon")
     -- Constructor applied to type-only arguments.
     e@(collectTyCoDictArgs -> (Var (isDataConId_maybe -> Just dc),_))
       | let (binds,body) = collectBinders (etaExpand (dataConRepArity dc) e)
       , Just meth <- hrMeth body
       -> do tryReify $
               mkLams binds $
                 meth abstV `App` (simplE True (meth repr'V `App` body))
     AboutTo("primitive")
     -- Primitive functions
     e@(collectTyArgs -> (Var v, tys))
       | j@(Just _) <- primFun (exprType e) v tys -> j
     -- reify (eval e) --> e.
     AboutTo("eval")
     (collectArgs -> (Var v,[Type _,e])) | v == evalV -> Just e
     AboutTo("unfold")
     (unfoldMaybe -> Just e') -> tryReify e'
     -- TODO: try to handle non-standard constructor applications along with unfold.
     -- Other applications
     AboutTo("app")
     App u v | not (isTyCoArg v)
             , Just (dom,ran) <- splitFunTy_maybe (exprType u)
             , Just reU <- tryReify u
             , Just reV <- tryReify v
       ->
        Just (varApps appV [dom,ran] [reU,reV])
     _e -> pprTrace "reify" (text "Unhandled:" <+> ppr _e) $
           Nothing
   -- TODO: Refactor a bit to reduce the collectArgs applications.
   -- v --> ("v", eval (varP "v"))
   mkVarEvald :: Id -> (CoreExpr,CoreExpr)
   mkVarEvald v = (vstr, varApps evalV [vty] [varApps varV [vty] [vstr]])
    where
      vty  = varType     v
      vstr = varNameExpr v
   -- Helpers
   mkReify :: Unop CoreExpr
   mkReify e = varApps reifyV [exprType e] [e]
   tryReify :: ReExpr
   -- tryReify e | pprTrace "tryReify" (ppr e) False = undefined
   -- tryReify e = guard (reifiableExpr e) >> (go e <|> Just (mkReify e))
   tryReify e | reifiableExpr e = (guard recursively >> go e) <|> Just (mkReify e)
              | otherwise = -- pprTrace "Not reifiable:" (ppr e)
                            Nothing
   hrMeth :: CoreExpr -> Maybe (Id -> CoreExpr)
   hrMeth = hasRepMeth dflags guts inScope . exprType
   lit :: ReExpr
   lit = hasLit dflags guts inScope
   repMeth :: ReExpr
   repMeth (collectArgs -> (Var v, args@(length -> 4))) =
     do nm <- stripPrefix "ReificationRules.FOS." (fqVarName v)
        case nm of
          "abst" -> wrap abstPV
          "repr" -> wrap reprPV
          _      -> Nothing
    where
      wrap :: Id -> Maybe CoreExpr
      wrap prim = Just (mkApps (Var prim) args)
   repMeth _ = Nothing
   -- Has the form evalP (varP x)
   isEvalVar :: CoreExpr -> Bool
   isEvalVar (Var ev `App` Type _ `App` (Var vv `App` Type _ `App` _)) =
     ev == evalV && vv == varV
   isEvalVar _ = False
   -- Experimental
   cheap :: CoreExpr -> Bool
   -- cheap e | pprTrace "cheap?" (ppr e) False = undefined
   cheap e | isTyCoDictArg e = True
   cheap (Var v)             = not (isPrim v) &&
                               maybe True cheap (inlineMaybe v)
   cheap (Lit _)             = True
   cheap (Lam _ body)        = cheap body
   cheap (App u v)           = cheap u && cheap v  -- Watch out
   cheap (Cast e _)          = cheap e
   cheap _                   = False
   -- I don't know how hard to try with inlining. Might work better to simplify
   -- after reifying, since inlining and case-removal will have happened.
   simplE :: Bool -> Unop CoreExpr
#if 1
   simplE inlining = -- traceUnop ("simplify " ++ show inlining) $
     simplifyE dflags inlining
#else
   -- Simplify to fixed point
   simplE inlining = sim 0
    where
      sim :: Int -> Unop CoreExpr
      sim n e | n >= 10            = e
              | e' `cheapEqExpr` e = e
              | otherwise          = sim (n+1) e'
       where
         e' = traceUnop ("simplify " ++ show inlining ++ ", pass " ++ show n)
              (simplifyE dflags inlining) e
#endif
   -- Convert a coercion (being used in a cast) to an equivalent Core function to
   -- apply.
   -- TODO: Consider handling casts one layer at a time (non-recursively),
   -- leaving behind simpler casts.
   recast :: Coercion -> Maybe CoreExpr
   recast (Refl _r ty) = Just (unfolded (varApps idV [ty] []))
   recast (FunCo _r domCo ranCo) =
     liftA2 mkPrePost (recast (mkSymCo domCo)) (recast ranCo) -- co/contravariant
    where
      mkPrePost f g = unfolded $ varApps prePostV [a,b,a',b'] [f,g]
       where
         -- (-->) :: forall a b a' b'.
         --          (a' -> a) -> (b -> b') -> ((a -> b) -> (a' -> b'))
         Just (a',a) = splitFunTy_maybe (exprType f)
         Just (b,b') = splitFunTy_maybe (exprType g)
   recast co@(       AxiomInstCo {} ) = recastRep reprV pFst co
   recast co@(SymCo (AxiomInstCo {})) = recastRep abstV pSnd co
   -- Panic for now, to reduce output.
   -- Maybe stick with the panic, and drop the Maybe.
   recast co = pprPanic "recast: unhandled coercion" (ppr co)
   -- recast co = dtrace "recast: unhandled coercion" (ppr co) Nothing
   recastRep v get co =
     ($ v) <$> hasRepMeth dflags guts inScope (get (coercionKind co))
   unfolded :: Unop CoreExpr
   unfolded e = fromMaybe e (unfoldMaybe e)               
   -- Unfold application head, if possible.
   unfoldMaybe :: ReExpr
   unfoldMaybe = -- traceRewrite "unfold" $
                 onAppsFun inlineMaybe
   inlineMaybe :: Id -> Maybe CoreExpr
   inlineMaybe v = guard (not (isPrim v)) >>
                   maybeUnfoldingTemplate (realIdUnfolding v)
   -- See match_inline from PrelRules, as used with 'inline'.
   inlineable :: Id -> Bool
   inlineable = isJust . inlineMaybe
   -- Tracing
   dtrace :: String -> SDoc -> a -> a
   dtrace str doc | tracing   = pprTrace str doc
                  | otherwise = id
   pprTrans :: (Outputable a, Outputable b) => String -> a -> b -> b
   pprTrans str a b = dtrace str (ppr a $$ text "-->" $$ ppr b) b
   traceUnop :: (Outputable a, Outputable b) => String -> Unop (a -> b)
   traceUnop str f a = pprTrans str a (f a)
   traceRewrite :: (Outputable a, Outputable b, Functor f) =>
                   String -> Unop (a -> f b)
   traceRewrite str f a = pprTrans str a <$> f a

-- TODO: Should I unfold (inline application head) earlier? Doing so might
-- result in much simpler generated code by avoiding many beta-redexes. If I
-- do, take care not to inline "primitives". I think it'd be fairly easy.

onAppsFun :: (Id -> Maybe CoreExpr) -> ReExpr
onAppsFun h (collectArgs -> (Var f, args)) = simpleOptExpr . (`mkApps` args) <$> h f
onAppsFun _ _ = Nothing

hasUnfolding :: Id -> Bool
hasUnfolding (uqVarName -> "inline") = False
hasUnfolding (idUnfolding -> NoUnfolding) = False
hasUnfolding _ = True

-- Don't do abstReprCase, since it's been done already. Check the outer function
-- being applied to see whether it's abst', $fHasRepFoo_$cabst (for some Foo),
-- or is a constructor worker or wrapper.
-- TODO: Rename this test. I think it's really about saying not to abstRepr.
alreadyAbstReprd :: CoreExpr -> Bool
alreadyAbstReprd (collectArgs -> (h,_)) =
  case h of
    Var  v   ->
         name == "abst'"
      || name == "inline"
      || ("$fHasRep" `isPrefixOf` name && "_$cabst" `isSuffixOf` name)
      || isJust (isDataConId_maybe v)
     where
       name = uqVarName v
    Case {} -> True
    _       -> False

infixl 3 <+
(<+) :: Binop (Rewrite a)
(<+) = liftA2 (<|>)

varApps :: Id -> [Type] -> [CoreExpr] -> CoreExpr
varApps v tys es = mkApps (Var v) (map Type tys ++ es)

reifiableKind :: Kind -> Bool
reifiableKind = isLiftedTypeKind

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
badTyCon tc = qualifiedName (tyConName tc) `elem`
  [ "GHC.Integer.Type"
  , "GHC.Types.[]"
  , "GHC.Types.IO"
  , "ReificationRules.Exp.E"
  ]

reifiableExpr :: CoreExpr -> Bool
reifiableExpr e = not (isTyCoArg e) && reifiableType (exprType e)

{--------------------------------------------------------------------
    Primitive translation
--------------------------------------------------------------------}

stdClassOpInfo :: [(String,String,[String],[(String,String)])]
stdClassOpInfo =
   [ ( "Eq","BinRel",["Bool","Int","Doubli"]
     , [("==","Eq"), ("/=","Ne")])
   , ( "Ord","BinRel",["Bool","Int","Doubli"]
     , [("<","Lt"),(">","Gt"),("<=","Le"),(">=","Ge")])
   , ( "Num","Unop",["Int","Doubli"]
     , [("negate","Negate")])
   , ( "Num","Binop",["Int","Doubli"]
     , [("+","Add"),("-","Sub"),("*","Mul")])
   , ( "Floating","Unop",["Doubli"]
     , [("exp","Exp"),("cos","Cos"),("sin","Sin")])
   , ( "Fractional","Unop",["Doubli"]
     , [("recip","Recip")])
   , ( "Fractional","Binop",["Doubli"]
     , [("/","Divide")])
   ]

-- Name of prim type specialization in MonoPrims
primAt :: String -> String -> String
primAt prim ty = toLower (head ty) : prim

-- Map "$fNumInt_$c+" to MonoPrims names "iAdd" etc
stdMethMap :: M.Map String String
stdMethMap = M.fromList $
  [ (opName cls ty op prim, primAt prim ty)
  | (cls,_,tys,ps) <- stdClassOpInfo, ty <- tys, (op,prim) <- ps ]
  ++
  [ ("not","notP"), ("||","orP"), ("&&","andP")
  , ("fst","exlP"), ("snd","exrP"), ("(,)","pairP")
  ]
 where
   -- Unqualified method name, e.g., "$fNumInt_$c+".
   -- Eq & Ord for Int use "eqInt" etc.
   opName :: String -> String -> String -> String -> String
   opName cls ty op prim
     | ty == "Int" && cls `elem` ["Eq","Ord"] = onHead toLower prim ++ "Int"
     | otherwise                              = printf "$f%s%s_$c%s" cls ty op

-- If I give up on using a rewrite rule, then I can precede the first simplifier
-- pass, so the built-in class op unfoldings don't have to fire first.

{--------------------------------------------------------------------
    Plugin installation
--------------------------------------------------------------------}

mkReifyRule :: [CommandLineOption] -> CoreM (ModGuts -> CoreRule)
mkReifyRule opts = reRule <$> mkReifyEnv opts
 where
   reRule :: ReifyEnv -> ModGuts -> CoreRule
   reRule ops guts =
     BuiltinRule { ru_name  = fsLit "reify"
                 , ru_fn    = varName (reifyV ops)
                 , ru_nargs = 2  -- including type arg
                 , ru_try   = \ dflags inScope _fn [_ty,arg] ->
                                 reify ops guts dflags inScope arg
                 }

plugin :: Plugin
plugin = defaultPlugin { installCoreToDos = install }

install :: [CommandLineOption] -> [CoreToDo] -> CoreM [CoreToDo]
install opts todos =
  do reinitializeGlobals
     rr <- mkReifyRule opts
     -- For now, just insert the rule.
     -- TODO: add "reify_" bindings and maybe rules.
     let pass guts = pure (on_mg_rules (rr guts :) guts)
     return $ CoreDoPluginPass "Reify insert rule" pass : todos

type PrimFun = Type -> Id -> [Type] -> Maybe CoreExpr

mkReifyEnv :: [CommandLineOption] -> CoreM ReifyEnv
mkReifyEnv opts = do
  -- liftIO $ putStrLn ("Options: " ++ show opts)
  hsc_env <- getHscEnv
  let lookupRdr :: ModuleName -> (Name -> CoreM a) -> String -> CoreM a
      lookupRdr modu mk str =
        maybe (panic err) mk =<<
          liftIO (lookupRdrNameInModuleForPlugins hsc_env modu
                     (mkVarUnqual (fsLit str)))
       where
         err = "reify installation: couldn't find "
               ++ str ++ " in " ++ moduleNameString modu
      findId modu = lookupRdr (mkModuleName modu) lookupId
      findExpId   = findId "ReificationRules.FOS"
      findTupleId = findId "Data.Tuple"
      findBaseId  = findId "GHC.Base"
      findMiscId  = findId "ReificationRules.Misc"
      findMonoId  = findId "ReificationRules.MonoPrims"
  varV     <- findExpId "varP"
  appV     <- findExpId "appP"
  lamV     <- findExpId "lamP"
  letV     <- findExpId "letP"
  letPairV <- findExpId "letPairP"
  reifyV   <- findExpId "reifyP"
  evalV    <- findExpId "evalP"
  constV   <- findExpId "constP"
  abstV    <- findExpId "abst"
  reprV    <- findExpId "repr"
  abst'V   <- findExpId "abst'"
  repr'V   <- findExpId "repr'"
  abstPV   <- findExpId "abstP"
  reprPV   <- findExpId "reprP"
  fstV     <- findTupleId "fst"
  sndV     <- findTupleId "snd"
  idV      <- findBaseId "id"
  composeV <- findBaseId "."
  prePostV <- findMiscId "-->"
  primMap  <- mapM findMonoId stdMethMap
  let lookupPrim v = M.lookup (uqVarName v) primMap
      primFun ty v tys = (\ primId -> varApps constV [ty] [varApps primId tys []])
                         <$> lookupPrim v
      isPrim = isJust . lookupPrim
  hasRepMeth <- hasRepMethodM (repTcsFromAbstPTy (varType abstPV))
  toLitV <- findExpId "litE"
  let hasLitTc = tcFromToLitETy (varType toLitV)
  hasLit <- toLitM (hasLitTc,toLitV)
  let expTy = expTyFromReifyTy (varType reifyV)
  let tracing = "trace" `elem` opts
  return (ReifyEnv { .. })
 where
   -- Used to extract Prim tycon argument
   tyArg1 :: Unop Type
   tyArg1 (tyConAppArgs_maybe -> Just [arg]) = arg
   tyArg1 ty = pprPanic "mkReifyEnv/tyArg1 non-unary" (ppr ty)

-- * I'm assuming that it's safe to reuse x's unique here, since x is
-- eliminated. If not, use uniqAway x and then setVarType.

-- The next few functions extract types and tycons from the types of looked-up
-- identifiers. I'd rather learn how to look up the types and tycons directly,
-- as I do with (value) identifiers.

expTyFromReifyTy :: Type -> Type
expTyFromReifyTy reifyTy = expTy
 where
   Just (_a,expA) = splitFunTy_maybe (dropForAlls reifyTy)
   Just (expTy,_) = splitAppTy_maybe expA

-- Extract HasRep and Rep from the type of abst
repTcsFromAbstTy :: Type -> (TyCon,TyCon)
repTcsFromAbstTy abstTy = (hasRepTc, repTc)
 where
   -- abst :: HasRep a => Rep a -> a
   ([hasRepTy,repa],_) = splitFunTys (dropForAlls abstTy)
   Just hasRepTc       = tyConAppTyCon_maybe hasRepTy
   Just repTc          = tyConAppTyCon_maybe repa

-- Extract HasRep and Rep from the type of abstPV
repTcsFromAbstPTy :: Type -> (TyCon,TyCon)
repTcsFromAbstPTy abstPvTy = -- pprTrace "repTcsFromAbstPTy. eqTy" (ppr eqTy) $
                             (hasRepTc, repTc)
 where
   -- abstP :: (HasRep a, Rep a ~~ a') => EP (a' -> a)
   ([hasRepTy,eqTy],_)       = splitFunTys (dropForAlls abstPvTy)
   Just hasRepTc             = tyConAppTyCon_maybe hasRepTy
   Just [_ka, _ka',repATy,_] = tyConAppArgs_maybe eqTy
   Just repTc                = tyConAppTyCon_maybe repATy

-- Extract HasLit TyCon from the type of toLitE
tcFromToLitETy :: Type -> TyCon
tcFromToLitETy toLitETy = tc
 where
   -- litE :: HasLit a => a -> EP a
   (hasLitA,_) = splitFunTy (dropForAlls toLitETy)
   Just tc = tyConAppTyCon_maybe hasLitA

type HasRepMeth = DynFlags -> ModGuts -> InScopeEnv -> Type -> Maybe (Id -> CoreExpr)

hasRepMethodM :: (TyCon,TyCon) -> CoreM HasRepMeth
hasRepMethodM (hasRepTc,repTc) =
  do hscEnv <- getHscEnv
     eps    <- liftIO (hscEPS hscEnv)
     return $ \ dflags guts inScope ty ->
       let (mkEqBox -> eq,ty') =
             normaliseType (eps_fam_inst_env eps, mg_fam_inst_env guts)
                           Nominal (mkTyConApp repTc [ty])
           mfun :: CoreExpr -> Id -> CoreExpr
           mfun dict = -- pprTrace "hasRepMeth dict" (ppr dict) $
                       \ meth -> -- pprTrace "hasRepMeth meth" (ppr meth) $
                                 varApps meth [ty,ty'] [dict,eq]
                                 -- varApps meth [ty] [dict]
       in
         -- pprTrace "hasRepMeth ty" (ppr ty) $
         mfun <$> buildDictionary hscEnv dflags guts inScope
                    (mkTyConApp hasRepTc [ty])

type HasLit = DynFlags -> ModGuts -> InScopeEnv -> ReExpr

toLitM :: (TyCon,Id) -> CoreM HasLit
toLitM (hasLitTc,toLitV) =
  do hscEnv <- getHscEnv
     return $ \ dflags guts inScope e ->
       guard (isConApp e) >>            -- TODO: expand is-literal test
       let ty = exprType e
           lfun :: CoreExpr -> CoreExpr
           lfun dict = -- dtrace "toLit" (ppr e) $
                       varApps toLitV [ty] [dict,e]
       in
         lfun <$> buildDictionary hscEnv dflags guts inScope
                    (mkTyConApp hasLitTc [ty])

-- TODO: move the CoreM stuff in hasRepMethodM and toLitM into calling code.

-- TODO: refactor hasRepMethodM and toLitM.

{--------------------------------------------------------------------
    Misc
--------------------------------------------------------------------}

on_mg_rules :: Unop [CoreRule] -> Unop ModGuts
on_mg_rules f mg = mg { mg_rules = f (mg_rules mg) }

fqVarName :: Var -> String
fqVarName = qualifiedName . varName

uqVarName :: Var -> String
uqVarName = getOccString . varName

-- Keep consistent with stripName in Exp.
uniqVarName :: Var -> String
uniqVarName v = uqVarName v ++ "_" ++ show (varUnique v)

-- Swiped from HERMIT.GHC
-- | Get the fully qualified name from a 'Name'.
qualifiedName :: Name -> String
qualifiedName nm = modStr ++ getOccString nm
    where modStr = maybe "" (\m -> moduleNameString (moduleName m) ++ ".") (nameModule_maybe nm)

-- | Substitute new subexpressions for variables in an expression
subst :: [(Id,CoreExpr)] -> Unop CoreExpr
subst ps = substExpr (text "subst") (foldr add emptySubst ps)
 where
   add (v,new) sub = extendIdSubst sub v new

subst1 :: Id -> CoreExpr -> Unop CoreExpr
subst1 v e = subst [(v,e)]

onHead :: Unop a -> Unop [a]
onHead f (c:cs) = f c : cs
onHead _ []     = []

collectTyArgs :: CoreExpr -> (CoreExpr,[Type])
collectTyArgs = go []
 where
   go tys (App e (Type ty)) = go (ty:tys) e
   go tys e                 = (e,tys)

collectArgsPred :: (CoreExpr -> Bool) -> CoreExpr -> (CoreExpr,[CoreExpr])
collectArgsPred p = go []
 where
   go args (App fun arg) | p arg = go (arg:args) fun
   go args e                     = (e,args)

collectTyCoDictArgs :: CoreExpr -> (CoreExpr,[CoreExpr])
collectTyCoDictArgs = collectArgsPred isTyCoDictArg

isTyCoDictArg :: CoreExpr -> Bool
isTyCoDictArg e = isTyCoArg e || isPredTy (exprType e)

isConApp :: CoreExpr -> Bool
isConApp (collectArgs -> (Var (isDataConId_maybe -> Just _), _)) = True
isConApp _ = False

-- TODO: More efficient isConApp, discarding args early.

stringExpr :: String -> CoreExpr
stringExpr = Lit . mkMachString

varNameExpr :: Id -> CoreExpr
varNameExpr = stringExpr . uniqVarName

pattern FunCo :: Role -> Coercion -> Coercion -> Coercion
pattern FunCo r dom ran <- TyConAppCo r (isFunTyCon -> True) [dom,ran]
 where
   FunCo r dom ran = TyConAppCo r funTyCon [dom,ran]
