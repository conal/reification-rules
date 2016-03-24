{-# LANGUAGE CPP               #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE MultiWayIf        #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternGuards     #-}
{-# LANGUAGE PatternSynonyms   #-}
{-# LANGUAGE RecordWildCards   #-}
{-# LANGUAGE TupleSections     #-}
{-# LANGUAGE ViewPatterns      #-}

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

import Control.Applicative (liftA2,(<|>))
import Control.Monad (unless,guard)
import Data.Maybe (fromMaybe,isJust)
import Data.List (isPrefixOf,isSuffixOf,elemIndex)
import Data.Char (toLower)
import qualified Data.Map as M
import Text.Printf (printf)

import GhcPlugins hiding (substTy)
import Class (classAllSelIds)
import CoreArity (etaExpand)
import CoreLint (lintExpr)
import DynamicLoading
-- import Kind (isLiftedTypeKind)
import MkId (mkDictSelRhs)
import Pair (Pair(..))
import Type (coreView)
-- import TcType (isIntegerTy)
import FamInstEnv (normaliseType)
import TyCoRep                          -- TODO: explicit imports

import ReificationRules.Misc (Unop,Binop)
import ReificationRules.BuildDictionary (buildDictionary,mkEqBox)
import ReificationRules.Simplify (simplifyE)

{--------------------------------------------------------------------
    Reification
--------------------------------------------------------------------}

-- Information needed for reification. We construct this info in
-- CoreM and use it in the reify rule, which must be pure.
data ReifyEnv = ReifyEnv { appV       :: Id
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
                         , idV        :: Id
                         , composeV   :: Id
                         , prePostV   :: Id
                         , ifPV       :: Id
                         , ifCatTy    :: Type -> Type
                         , hasRepMeth :: HasRepMeth
                         , hasLit     :: HasLit
                         , tracing    :: Bool
                         , hsc_env    :: HscEnv
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

-- #define Trying(str) e | dtrace ("Trying " ++ (str)) (e `seq` empty) False -> undefined

#define Trying(str)

-- Use of e in a dtrace argument prevents the dtrace call from getting hoisted.

reify :: ReifyEnv -> ModGuts -> DynFlags -> InScopeEnv -> ReExpr
reify (ReifyEnv {..}) guts dflags inScope =
  -- pprTrace "reify rule" empty $
  traceRewrite "reify" $
  lintReExpr $
  go
 where
   go :: ReExpr
   go = \ case 
     -- e | dtrace "reify go:" (ppr e) False -> undefined
     Trying("lambda")
     Lam x e | not (isTyVar x) ->
       -- lamP :: forall a b. Name# -> (EP a -> EP b) -> EP (a -> b)
       -- (\ x -> e) --> lamP "x" (\ x' -> e[x/eval x'])
       do e' <- -- dtrace "lambda" (ppr (subst1 x evalY e) <+> dcolon <+> ppr (exprType (subst1 x evalY e))) $
                -- dtrace "lambda" (ppr (reifiableType (exprType (subst1 x evalY e))))
                tryReify (subst1 x evalY e)
          return $ varApps lamV [varType x, exprType e] [strY, Lam y e']
       where
         (y,strY,evalY) = mkVarEvald x
     Trying("let")
     Let (NonRec x rhs) body
        | not (reifiableExpr rhs) || cheap rhs -> Let (NonRec x rhs) <$> tryReify body
       -- | isEvalVar rhs -> go (subst1 v rhs body)
       -- The not.isEvalVar test prevents a simplifier loop that keeps
       -- let-abstracting terms of the form evalP (varP x). The immediate go
       -- delays GHC re-hoisting long enough to avoid an infinite loop. See
       -- journal entry 2016-03-15.
        | otherwise ->
#if 0
          go (Lam x body `App` rhs)
#else
          -- Alternatively, use letP. Works as well but more complicated.
          -- letP :: forall a b. Name# -> EP a -> (EP a -> EP b) -> EP b
          let (y,strY,evalY) = mkVarEvald x in
            liftA2 (\ rhs' body' -> varApps letV [exprType rhs, exprType body]
                                      [strY,rhs',Lam y body'])
                   (tryReify rhs)
                   (tryReify (subst1 x evalY body))
#endif
     Trying("case-of-cast")
     Case (Cast e co) wild ty alts ->
       do scrut' <- (`App` e) <$> recast co
          tryReify (Case scrut' wild ty alts)
     Trying("case-of-case")
     e@(Case (Case {}) _ _ _) -> tryReify (simplE False e) -- still necessary?
     Trying("if-then-else")
     e@(Case scrut wild rhsTy [ (DataAlt false, [], falseVal)
                              , (DataAlt true , [],  trueVal) ])
       | false == falseDataCon, true == trueDataCon ->
         if isDeadBinder wild then
           (varApps ifPV [rhsTy] . (buildDict (ifCatTy rhsTy) :))
             <$> mapM tryReify [scrut,trueVal,falseVal]
         else
           pprPanic "reify - case with live wild var (not yet handled)" (ppr e)
           -- TODO: handle live wild var.
     Trying("unit scrutinee")
     e@(Case _scrut wild _rhsTy [(DataAlt dc, [], rhs)])
         | isBoxedTupleTyCon (dataConTyCon dc)
         , reifiableExpr rhs ->
       do -- To start, require v to be unused. Later, extend.
          unless (isDeadBinder wild) $
            pprPanic "reify - case with live wild var (not yet handled)" (ppr e)
          -- TODO: handle live wild var.
          tryReify rhs
     Trying("pair scrutinee")
     e@(Case scrut wild rhsTy [(DataAlt dc, [a,b], rhs)])
         | isBoxedTupleTyCon (dataConTyCon dc)
         , reifiableExpr rhs ->
       do -- To start, require v to be unused. Later, extend.
          unless (isDeadBinder wild) $
            pprPanic "reify - case with live wild var (not yet handled)" (ppr e)
          -- TODO: handle live wild var.
          -- letPairP :: forall a b c. Name# -> Name# -> EP (a :* b) -> (EP a -> EP b -> EP c) -> EP c
          liftA2 (\ rhs' scrut' -> varApps letPairV [varType a, varType b, rhsTy]
                                     [strA,strB,scrut',mkLams [a',b'] rhs'])
                 (tryReify (subst [(a,evalA),(b,evalB)] rhs))
                 (tryReify scrut)
      where
        (a',strA,evalA) = mkVarEvald a
        (b',strB,evalB) = mkVarEvald b
     Trying("abstReprCase")
     Case scrut v altsTy alts
       | not (alreadyAbstReprd scrut)
       , Just meth <- hrMeth (exprType scrut)
       -> tryReify $ -- go  -- Less chatty with go
          Case (meth abst'V `App` (meth reprV `App` scrut)) v altsTy alts
     Trying("unfold scrutinee")
     Case scrut v altsTy alts
       | Just scrut' <- unfoldMaybe scrut
       -> tryReify $ Case scrut' v altsTy alts
     Trying("cast")
     Cast e (recast -> Just f) -> tryReify (App f e)
     Trying("repMeth")
     (repMeth -> Just e) -> Just e
     Trying("literal")
     (literal -> Just e) -> Just e
     Trying("abstReprCon")
     -- Constructor applied to ty/co/dict arguments
     e@(collectTyCoDictArgs -> (Var (isDataConId_maybe -> Just dc),_))
       | let (binds,body) = collectBinders (etaExpand (dataConRepArity dc) e)
       , Just meth <- hrMeth (exprType body)
       -> do tryReify $
               mkLams binds $
                 meth abstV `App` (simplE True (meth repr'V `App` body))
     Trying("primitive")
     -- Primitive functions
     e@(collectTyArgs -> (Var v, tys))
       | j@(Just _) <- primFun (exprType e) v tys -> j
     -- reify (eval e) --> e.
     Trying("eval")
     (collectArgs -> (Var v,[Type _,e])) | v == evalV -> Just e
     Trying("unfold")
     (unfoldMaybe -> Just e') -> tryReify e'
     -- TODO: try to handle non-standard constructor applications along with unfold.
     -- Other applications
     Trying("case-apps")
     -- Push arguments into case alternatives. TODO: take care when multi-alt
     -- and runtime args.
     e@(collectArgs -> (c@(Case {}), args@(_:_))) ->
       tryReify (-- traceUnop "onCaseRhs" 
                 (onCaseRhs (exprType e) (`mkApps` args)) c)
     Trying("app")
     App u v | not (isTyCoArg v)
             , Just (dom,ran) <- splitFunTy_maybe (exprType u)
             , Just reU <- tryReify u
             , Just reV <- tryReify v
       ->
        Just (varApps appV [dom,ran] [reU,reV])
     _e -> pprTrace "reify" (text "Unhandled:" <+> ppr _e) $
           Nothing
   -- TODO: Refactor a bit to reduce the collectArgs applications.
   -- v --> ("v'", eval v')
   mkVarEvald :: Id -> (Id,CoreExpr,CoreExpr)
   mkVarEvald x = (y,strY, varApps evalV [xty] [Var y])
    where
      xty  = varType     x
      y    = zapIdOccInfo (setVarType x (exprType (mkReify (Var x))))
      strY = varNameExpr y
   -- Helpers
   mkReify :: Unop CoreExpr
   mkReify e = varApps reifyV [exprType e] [e]
   tryReify :: ReExpr
   -- tryReify e | pprTrace "tryReify" (ppr e) False = undefined
   -- tryReify e = guard (reifiableExpr e) >> (go e <|> Just (mkReify e))
   tryReify e | reifiableExpr e = (guard recursively >> go e) <|> Just (mkReify e)
              | otherwise = -- pprTrace "Not reifiable:" (ppr e)
                            Nothing
   hrMeth :: Type -> Maybe (Id -> CoreExpr)
   hrMeth = hasRepMeth dflags guts inScope
   literal :: ReExpr
   literal = hasLit dflags guts inScope
   repMeth :: ReExpr
   repMeth (collectArgs -> (Var v, args@(length -> 4))) =
     if | v == abstV -> wrap abstPV
        | v == reprV -> wrap reprPV
        | otherwise  -> Nothing
     -- TODO: Rewrite using List.lookup with [(abstV,abstPV),(reprV,reprPV)]
     -- and fmap (\ prim -> mkApps (Var prim) args)
    where
      wrap :: Id -> Maybe CoreExpr
      wrap prim = Just (mkApps (Var prim) args)
   repMeth _ = Nothing
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
   recast (SubCo co) = recast co
   -- Panic for now, to reduce output.
   -- Maybe stick with the panic, and drop the Maybe.
   recast co = pprPanic "recast: unhandled coercion" (ppr co)
   -- recast co = dtrace "recast: unhandled coercion" (ppr co) Nothing
   recastRep v get co = ($ v) <$> hrMeth (get (coercionKind co))
   -- TODO: Check the type, in case the coercion is not
   -- Rep a -> a or a -> Rep a.

   unfolded :: Unop CoreExpr
   unfolded e = fromMaybe e (unfoldMaybe e)               
   -- Unfold application head, if possible.
   unfoldMaybe :: ReExpr
   unfoldMaybe = -- traceRewrite "unfold" $
                 onAppsFun inlineMaybe
   inlineMaybe :: Id -> Maybe CoreExpr
   inlineMaybe v = guard (not (isPrim v)) >>
                   (inlineId <+ -- onInlineFail <+ traceRewrite "inlineClassOp"
                                inlineClassOp) v
   -- onInlineFail :: Id -> Maybe CoreExpr
   -- onInlineFail v =
   --   pprTrace "onInlineFail idDetails" (ppr v <+> colon <+> ppr (idDetails v))
   --   Nothing
   buildDict :: Type -> CoreExpr
   buildDict ty = fromMaybe (pprPanic "reify - couldn't build dictionary for" (ppr ty)) $
                  buildDictionary hsc_env dflags guts inScope ty
   -- Tracing
   dtrace :: String -> SDoc -> a -> a
   dtrace str doc | tracing   = pprTrace str doc
                  | otherwise = id
   pprTrans :: (Outputable a, Outputable b) => String -> a -> b -> b
   pprTrans str a b = dtrace str (ppr a $$ text "-->" $$ ppr b) b
   -- traceUnop :: (Outputable a, Outputable b) => String -> Unop (a -> b)
   -- traceUnop str f a = pprTrans str a (f a)
   traceRewrite :: (Outputable a, Outputable b, Functor f) =>
                   String -> Unop (a -> f b)
   traceRewrite str f a = pprTrans str a <$> f a
   -- Apply a rewrite, lint the result, and check that the type is preserved.
   lintReExpr :: Unop ReExpr
   lintReExpr rew before | lintSteps =
     do after <- rew before
        let oops str doc = pprPanic ("reify post-transfo check. " ++ str)
                             (doc $$ ppr before $$ text "-->" $$ ppr after)
            beforeTy = exprType (mkReify before)
            afterTy  = exprType after
        maybe (if beforeTy `eqType` afterTy then
                 return after
               else
                 oops "type change" (ppr beforeTy <+> text "vs" <+> ppr afterTy
                                     <+> text "in" $$ text ""))
              (oops "Lint")
          (lintExpr dflags (varSetElems (exprFreeVars before)) before)
   lintReExpr rew before = rew before

-- TODO: Should I unfold (inline application head) earlier? Doing so might
-- result in much simpler generated code by avoiding many beta-redexes. If I
-- do, take care not to inline "primitives". I think it'd be fairly easy.

-- Try to inline an identifier.
-- TODO: Also class ops
inlineId :: Id -> Maybe CoreExpr
inlineId v = maybeUnfoldingTemplate (realIdUnfolding v)

-- Adapted from Andrew Farmer's getUnfoldingsT in HERMIT.Dictionary.Inline:
inlineClassOp :: Id -> Maybe CoreExpr
inlineClassOp v =
  case idDetails v of
    ClassOpId cls -> mkDictSelRhs cls <$> elemIndex v (classAllSelIds cls)
    _             -> Nothing

onAppsFun :: (Id -> Maybe CoreExpr) -> ReExpr
onAppsFun h (collectArgs -> (Var f, args)) = simpleOptExpr . (`mkApps` args) <$> h f
onAppsFun _ _ = Nothing

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
(<+) :: Binop (a -> Maybe b)
(<+) = liftA2 (<|>)

apps :: CoreExpr -> [Type] -> [CoreExpr] -> CoreExpr
apps e tys es = mkApps e (map Type tys ++ es)

varApps :: Id -> [Type] -> [CoreExpr] -> CoreExpr
varApps = apps . Var

conApps :: DataCon -> [Type] -> [CoreExpr] -> CoreExpr
conApps = varApps . dataConWorkId

-- reifiableKind :: Kind -> Bool
-- reifiableKind = isLiftedTypeKind

-- Types we know how to handle
reifiableType :: Type -> Bool
-- reifiableType ty | pprTrace "reifiableType" (ppr ty) False = undefined
reifiableType (coreView -> Just ty) = reifiableType ty
reifiableType (splitFunTy_maybe -> Just (dom,ran)) = reifiableType dom && reifiableType ran
reifiableType ty = not (or (($ ty) <$> bads))
 where
   bads = [ try "isForAllTy" $ isForAllTy
      --  , try "not . reifiableKind . typeKind" $ not . reifiableKind . typeKind
          , try "isPredTy" $ isPredTy
          , try "badTyConArg" $ badTyConArg
          , try "badTyConApp" $ badTyConApp
          ]
   try :: String -> Unop (Type -> Bool)
   try _str p x = -- pprTrace (_str ++ ":") (ppr y)
                  y
     where y = p x

-- badTyConArg is problematic with the reifiableKind test. Consider Pow Pair,
-- which has reifiable kind, but Pair doesn't. What do I really want?

badTyConArg :: Type -> Bool
-- badTyConArg ty | pprTrace "badTyConArg" (ppr ty) False = undefined
badTyConArg (coreView -> Just ty)             = badTyConArg ty
badTyConArg (tyConAppArgs_maybe -> Just args) = -- pprTrace "tyConAppArgs" (ppr args) $
                                                not (all reifiableType args)
badTyConArg _                                 = False

badTyConApp :: Type -> Bool
-- badTyConApp ty | pprTrace "badTyConApp" (ppr ty) False = undefined
badTyConApp (coreView -> Just ty)            = badTyConApp ty
badTyConApp (tyConAppTyCon_maybe -> Just tc) = badTyCon tc
badTyConApp _                                = False
-- TODO: rename

badTyCon :: TyCon -> Bool
-- badTyCon tc | pprTrace "badTyCon" (ppr tc) False = undefined
badTyCon tc = qualifiedName (tyConName tc) `elem`
  [ "GHC.Integer.Type"
  , "GHC.Types.[]"
  , "GHC.Types.IO"
  , "ReificationRules.Exp.E"            -- TODO: Fix for HOS or okay?
  ]

reifiableExpr :: CoreExpr -> Bool
reifiableExpr e = not (isTyCoArg e) && reifiableType (exprType e)

{--------------------------------------------------------------------
    Primitive translation
--------------------------------------------------------------------}

stdClassOpInfo :: [(String,String,[String],[(String,String)])]
stdClassOpInfo =
   [ ( "Eq","BinRel",["Bool","Int","Double"]
     , [("==","Eq"), ("/=","Ne")])
   , ( "Ord","BinRel",["Bool","Int","Double"]
     , [("<","Lt"),(">","Gt"),("<=","Le"),(">=","Ge")])
   , ( "Num","Unop",["Int","Double"]
     , [("negate","Negate")])
   , ( "Num","Binop",["Int","Double"]
     , [("+","Add"),("-","Sub"),("*","Mul")])
   , ( "Floating","Unop",["Double"]
     , [("exp","Exp"),("cos","Cos"),("sin","Sin")])
   , ( "Fractional","Unop",["Double"]
     , [("recip","Recip")])
   , ( "Fractional","Binop",["Double"]
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
  , ("ifThenElse","ifP")]
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
  let lookupRdr :: ModuleName -> (String -> OccName) -> (Name -> CoreM a) -> String -> CoreM a
      lookupRdr modu mkOcc mkThing str =
        maybe (panic err) mkThing =<<
          liftIO (lookupRdrNameInModuleForPlugins hsc_env modu (Unqual (mkOcc str)))
       where
         err = "reify installation: couldn't find "
               ++ str ++ " in " ++ moduleNameString modu
      lookupTh mkOcc mk modu = lookupRdr (mkModuleName modu) mkOcc mk
      findId = lookupTh mkVarOcc  lookupId
      findTc = lookupTh mkTcOcc   lookupTyCon
      findExpId   = findId "ReificationRules.HOS"
      findRepTc   = findTc "Circat.Rep"
      findBaseId  = findId "GHC.Base"
      findMiscId  = findId "ReificationRules.Misc"
      findMonoId  = findId "ReificationRules.MonoPrims"
  appV     <- findExpId "appP"
  lamV     <- findExpId "lamP"
  letV     <- findExpId "letP"
  letPairV <- findExpId "letPairP"
  ifPV     <- findExpId "ifP"
  reifyV   <- findExpId "reifyP"
  evalV    <- findExpId "evalP"
  constV   <- findExpId "constP"
  abstV    <- findExpId "abst"
  reprV    <- findExpId "repr"
  abst'V   <- findExpId "abst'"
  repr'V   <- findExpId "repr'"
  abstPV   <- findExpId "abstP"
  reprPV   <- findExpId "reprP"
  idV      <- findBaseId "id"
  composeV <- findBaseId "."
  prePostV <- findMiscId "-->"
  primMap  <- mapM findMonoId stdMethMap
  let lookupPrim v = M.lookup (uqVarName v) primMap
      primFun ty v tys = (\ primId -> varApps constV [ty] [varApps primId tys []])
                         <$> lookupPrim v
      isPrim = isJust . lookupPrim
  hasRepTc   <- findRepTc "HasRep"
  repTc      <- findRepTc "Rep"
  hasRepMeth <- hasRepMethodM hasRepTc repTc idV
  toLitV     <- findExpId "litE"
  hasLitTc   <- findTc "ReificationRules.Prim" "HasLit"
  hasLit     <- toLitM hasLitTc toLitV
  circuitTc  <- findTc "Circat.Circuit" ":>"
  ifCatTc    <- findTc "Circat.Classes" "IfCat"
  let circuitTy = mkTyConApp circuitTc []
      ifCatTy t = mkTyConApp ifCatTc [circuitTy,t]
      tracing   = "trace" `elem` opts
  return (ReifyEnv { .. })

--   primTc     <- findTc "ReificationRules.Prim" "Prim"

      -- findDc = lookupTh mkDataOcc lookupDataCon
      -- findPrimDc = findDc "ReificationRules.Prim"

-- * I'm assuming that it's safe to reuse x's unique here, since x is
-- eliminated. If not, use uniqAway x and then setVarType.

-- The next few functions extract types and tycons from the types of looked-up
-- identifiers. I'd rather learn how to look up the types and tycons directly,
-- as I do with (value) identifiers.

type HasRepMeth = DynFlags -> ModGuts -> InScopeEnv -> Type -> Maybe (Id -> CoreExpr)

hasRepMethodM :: TyCon -> TyCon -> Id -> CoreM HasRepMeth
hasRepMethodM hasRepTc repTc idV =
  do hscEnv <- getHscEnv
     eps    <- liftIO (hscEPS hscEnv)
     return $ \ dflags guts inScope ty ->
       let newtypeRep :: Maybe (CoreExpr,(Coercion,Type))
#if 0
           newtypeRep = Nothing
#else
           newtypeRep =
             do (tc,tyArgs) <- splitTyConApp_maybe ty
                (tvs,newtyRhs,_coax) <- unwrapNewTyCon_maybe tc
                -- TODO: refactor to isolate the Maybe stuff.
                let repTy = mkTyConApp repTc [ty]
                    ty'   = substTy (zipTvSubst tvs tyArgs) newtyRhs
                    [hasRepDc] = tyConDataCons hasRepTc
                    mkIdFun t = varApps idV [t] []
                    repNt = UnivCo (PluginProv "RepNT") Representational ty repTy
                    reflTo t = mkFunCo Representational (mkRepReflCo t)
                    mkMeth t co = mkCast (mkIdFun t) (reflTo t co)
                    -- repNtIs = mkUnbranchedAxInstCo Nominal _coax tyArgs
                    --             (mkNomReflCo <$> [ty])  -- tyArgs ?? repTy?
                    repNtIs = UnivCo (PluginProv "RepNtIs") Nominal repTy ty'
                    repr = mkMeth    ty          repNt
                    abst = mkMeth repTy (mkSymCo repNt)
                    dict = conApps hasRepDc [ty] [repr,abst]
                return (dict,(repNtIs,ty'))
#endif
           findRep :: Maybe (CoreExpr,(Coercion,Type))
           findRep =
             (, normaliseType (eps_fam_inst_env eps, mg_fam_inst_env guts)
                  Nominal (mkTyConApp repTc [ty]) )
             <$> buildDictionary hscEnv dflags guts inScope
                   (mkTyConApp hasRepTc [ty])
           mkMethApp (dict,(co,ty')) =
             -- pprTrace "hasRepMeth" (ppr (dict,co,ty')) $
             \ meth -> -- pprTrace "hasRepMeth meth" (ppr meth) $
                       varApps meth [ty,ty'] [dict,mkEqBox co]
       in
          -- Real dictionary or synthesize
          mkMethApp <$> (findRep <|> newtypeRep)

-- <Sum a>_R -> Data.Monoid.N:Sum[0]
--               (Sub (Sym (Circat.Rep.D:R:RepSum[0] <a>_N)))
-- :: (Sum a -> Sum a) ~R# (Sum a -> Rep (Sum a))


-- mkUnbranchedAxInstCo :: Role -> CoAxiom Unbranched
--                      -> [Type] -> [Coercion] -> Coercion

-- Maybe useful:

-- mkUnbranchedAxInstRHS :: CoAxiom Unbranched -> [Type] -> [Coercion] -> Type
-- mkUnbranchedAxInstRHS ax = mkAxInstRHS ax 0


-- mkReflCo :: Role -> Type -> Coercion
-- mkFunCo :: Role -> Coercion -> Coercion -> Coercion


-- unwrapNewTyCon_maybe :: TyCon -> Maybe ([TyVar], Type, CoAxiom Unbranched)
-- splitTyConApp_maybe :: Type -> Maybe (TyCon, [Type])

-- zipVarEnv         :: [Var] -> [a] -> VarEnv a

-- zipTvSubst :: [TyVar] -> [Type] -> TCvSubst

-- TyCoRep.substTy ::
--   ?callStack::GHC.Stack.Types.CallStack => TCvSubst -> Type -> Type
--   	-- Defined in ‘TyCoRep’


type HasLit = DynFlags -> ModGuts -> InScopeEnv -> ReExpr

toLitM :: TyCon -> Id -> CoreM HasLit
toLitM hasLitTc toLitV =
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

-- fqVarName :: Var -> String
-- fqVarName = qualifiedName . varName

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

onCaseRhs :: Type -> Unop (Unop CoreExpr)
onCaseRhs altsTy' f (Case scrut v _ alts) =
  Case scrut v altsTy' (onAltRhs f <$> alts)
onCaseRhs _ _ e = pprPanic "onCaseRhs. Not a case: " (ppr e)

onAltRhs :: Unop CoreExpr -> Unop CoreAlt
onAltRhs f (con,bs,rhs) = (con,bs,f rhs)
