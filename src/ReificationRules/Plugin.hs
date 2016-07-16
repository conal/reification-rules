{-# LANGUAGE CPP               #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE MultiWayIf        #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternGuards     #-}
{-# LANGUAGE PatternSynonyms   #-}
{-# LANGUAGE RankNTypes        #-}
{-# LANGUAGE RecordWildCards   #-}
{-# LANGUAGE TupleSections     #-}
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

import Control.Arrow (first)
import Control.Applicative (liftA2,(<|>))
import Control.Monad (unless,guard)
import Data.Maybe (fromMaybe,isJust,catMaybes)
import Data.List (isPrefixOf,isSuffixOf,elemIndex,sort)
import Data.Char (toLower)
import qualified Data.Map as M
import Text.Printf (printf)

import GhcPlugins hiding (substTy)
import Class (classAllSelIds)
import CoreArity (etaExpand)
import CoreLint (lintExpr)
import DynamicLoading
import MkId (mkDictSelRhs)
import Pair (Pair(..))
import PrelNames (leftDataConName,rightDataConName)
import Type (coreView)
import TcType (isIntTy, isFloatTy, isDoubleTy)
import FamInstEnv (normaliseType)
import TyCoRep                          -- TODO: explicit imports
import Unique (mkBuiltinUnique)

import ReificationRules.Misc (Unop,Binop)
import ReificationRules.BuildDictionary (buildDictionary{-,mkEqBox-})
import ReificationRules.Simplify (simplifyE)

{--------------------------------------------------------------------
    Reification
--------------------------------------------------------------------}

-- Information needed for reification. We construct this info in
-- CoreM and use it in the reify rule, which must be pure.
data ReifyEnv = ReifyEnv { appV             :: Id
                         , lamV             :: Id
                         , letV             :: Id
                         , letPairV         :: Id
                         , reifyV           :: Id
                         , evalV            :: Id
                         , primFun          :: PrimFun
                         , isPrimApp        :: CoreExpr -> Bool
                         , abstV            :: Id
                         , reprV            :: Id
                         , abst'V           :: Id
                         , repr'V           :: Id
                         , abstPV           :: Id
                         , reprPV           :: Id
                         , unIV             :: Id
                         , idV              :: Id
                         , composeV         :: Id
                         , prePostV         :: Id
                         , ifPV             :: Id
                         , ifCatTy          :: Type -> Type
                         , epTy             :: Type
                         , repTc            :: TyCon
                         , hasRepMeth       :: HasRepMeth
                         , hasRepFromAbstCo :: Coercion -> CoreExpr
                         , hasLit           :: HasLit
                         , dtrace           :: forall a. String -> SDoc -> a -> a
                         , hsc_env          :: HscEnv
                         }

-- TODO: Perhaps drop reifyV, since it's in the rule

-- TODO: try replacing the identifiers with convenient functions that use them,
-- thus shifting some complexity from reify to mkReifyEnv. For instance, replace
-- composeV with mkCompose and prePostV with mkPrePost.

-- Whether to run Core Lint after every step
lintSteps :: Bool
lintSteps = True -- False

-- -- Keep this one False for simplifier synergy.
-- recursively :: Bool
-- recursively = False -- True

type Rewrite a = a -> Maybe a
type ReExpr = Rewrite CoreExpr

-- #define Trying(str) e | dtrace ("Trying " ++ (str)) (e `seq` empty) False -> undefined

#define Trying(str)

-- Use of e in a dtrace argument prevents the dtrace call from getting hoisted.

reify :: ReifyEnv -> ModGuts -> DynFlags -> InScopeEnv -> ReExpr
reify (ReifyEnv {..}) guts dflags inScope =
  traceRewrite "reifyP" $
  (if lintSteps then lintReExpr else id) $
  go
 where
   go :: ReExpr
   go = \ case 
     e | dtrace "reify go:" (ppr e) False -> undefined
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
     Trying("case-default")
     Case _scrut (isDeadBinder -> True) _rhsTy [(DEFAULT,[],rhs)] ->
       tryReify rhs
     Trying("if-then-else")
     e@(Case scrut wild rhsTy [ (DataAlt false, [], falseVal)
                              , (DataAlt true , [],  trueVal) ])
       | false == falseDataCon, true == trueDataCon
       , Just ifDict <- buildDictMaybe (ifCatTy rhsTy)
       ->
         if isDeadBinder wild then
           (varApps ifPV [rhsTy] . (ifDict :))
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
     Trying("sum scrutinee")
     Case _scrut _wild _rhsTy [ (DataAlt left , [_],  _leftVal)
                              , (DataAlt right, [_], _rightVal) ]
       | dataConName left  ==  leftDataConName
       , dataConName right == rightDataConName ->
         -- TODO: reify
         dtrace "reify sum (not yet implemented)" empty $
         Nothing
     Trying("product scrutinee")
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
#if 0
     -- I'm still noodling over this one. As is, unI# gets inlined, leading to
     -- the same sort of scrutinee.
     Trying("Int scrutinee")
     --  (case scrut of I# n -> RHS) --> (let { w = scrut; n = unI# w } in RHS)
     Case scrut w _rhsTy [(DataAlt _dc, [n], rhs)]
         | isIntTy (varType w')
         , reifiableExpr rhs ->
       tryReify $
         mkCoreLet (NonRec n (App (Var unIV) scrut)) rhs
--          mkCoreLets [ (NonRec w' scrut)
--                     , (NonRec n ({-mkCoreApp "reifyP" -} App (Var unIV) (Var w'))) ]
--            rhs
      where
        w' = zapIdOccInfo w
#endif
     Trying("abstReprCase")
     Case scrut v altsTy alts
       | {-dtrace "abstReprCase. scrut:" (ppr scrut <+> brackets (ppr (alreadyAbstReprd scrut))) True
       , -}not (alreadyAbstReprd scrut)
       , Just meth <- hrMeth (exprType scrut)
       -> tryReify $ -- go  -- Less chatty with go
          Case (simplE True (meth abst'V) `App` (meth reprV `App` scrut)) v altsTy alts
#if 1
     -- Can these two ever help? They did, I think.
     Trying("recast scrutinee")
     Case scrut@(Cast e co) wild ty alts
       | reifiableExpr scrut
       , not (isJust (setNominalRole_maybe co))
       , Just scrut' <- recast e co ->
       dtrace "recast scrutinee:" (ppr scrut $$ ppr scrut') $
       tryReify (Case scrut' wild ty alts)
     Trying("unfold scrutinee")
     Case scrut v altsTy alts
       -- | dtrace ("unfold scrutinee -- trying") (ppr scrut) False -> undefined
       | Just scrut' <- unfoldMaybe scrut
       -> tryReify $ Case scrut' v altsTy alts
#endif
#if 1
     -- Still useful?
     Trying("case-of-case")
     -- Give the simplifier another shot
     e@(Case _scrut@(Case {}) _ _ _) -> -- Nothing
         dtrace ("case-of-case -- trying") (ppr _scrut) $
         tryReify (simplE False e) -- still necessary?
#endif
     Trying("cast-of-reify")
     Cast e co | Just nco <- setNominalRole_maybe co ->
       let co' = mkAppCo (mkRepReflCo epTy) nco in  -- why *Rep*ReflCo?
         dtrace "cast-of-reify" (ppr nco) $
         (`Cast` co') <$> tryReify e
     Trying("recast")
     Cast e co | Just e' <- recast e co -> go e' -- tryReify
--      -- Now done in recast
--      Trying("unfold castee")
--      -- Does this one ever fire anymore?
--      Cast (unfoldMaybe -> Just e') co -> dtrace "unfold castee" empty $
--                                          tryReify $ Cast e' co
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
             -- TODO: Try simpleE on just (meth repr'V), not body.
     Trying("primitive")
     -- Primitive functions
     e@(collectTysDictsArgs -> (Var v, tys, _dicts))
       | j@(Just _) <- primFun (exprType e) v tys -> j
     -- reify (eval e) --> e.
     Trying("eval")
     (collectArgs -> (Var v,[Type _,e])) | v == evalV -> Just e
     Trying("unfold")
     -- Only unfold applications if the arguments are non-reifiable, so we can
     -- use synthesized reify rules. TODO: reconsider our other uses of
     -- unfoldMaybe.
     e@(collectArgsPred isTyCoDictArg -> (Var _v,_))
       | -- dtrace "reify unfold try" (ppr _v <+> text "... -->" <+> ppr (unfoldMaybe e)) True,
       Just e' <- unfoldMaybe e -> tryReify e'

--      e@(collectArgs -> (Var v, _)) | uqVarName v == "$dmsum", pprTrace "reify $dmsum" (ppr e $$ ppr (collectTysDictsArgs e)) False -> undefined
--      e@(collectTysDictsArgs -> (Var _,_,_))
--        | Just e' <- unfoldMaybe e -> tryReify e'
--      -- (unfoldMaybe -> Just e') -> tryReify e'

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
     _e -> dtrace "reifyP" ("Unhandled:" <+> ppr _e) $
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
   tryReify e | reifiableExpr e = -- (guard recursively >> go e) <|>
                                  Just (mkReify e)
              | otherwise = dtrace "tryReify: not reifiable:" (ppr e <+> dcolon <+> ppr (exprType e))
                            Nothing
   hrMeth :: Type -> Maybe (Id -> CoreExpr)
   hrMeth ty = -- dtrace "hasRepMeth:" (ppr ty) $
               hasRepMeth dflags guts inScope ty
   literal :: ReExpr
   literal = hasLit dflags guts inScope
   repMeth :: ReExpr
   repMeth (collectArgs -> (Var v, args@(length -> 2))) =  -- 4
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
           | isPrimApp e     = False
   cheap (Var v)             = maybe True cheap (inlineMaybe v)
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
   -- Convert a cast into a more reifiable form (but don't reify)
   recast :: CoreExpr -> Coercion -> Maybe CoreExpr
   recast _ co | dtrace "recast" (ppr co <+> dcolon <+> ppr (coercionType co)) False = undefined
   -- If we have a nominal(able) coercion, let another reify pass handle it.
   -- Importantly, 'go' above tries this case before recast. Thus, if we see a
   -- nominal coercion here, we've already made progress.
   -- I'm not really sure about this argument, so take care!
   recast e co | Just _ <- setNominalRole_maybe co = Just (mkCast e co)
   recast e (Refl {}) = Just e  -- or leave for the simplifier
   recast e (FunCo _r domCo ranCo) =
     Just (Lam x (mkCast (e `App` mkCast (Var x) (mkSymCo domCo)) ranCo))
     -- TODO: Will the simplifier move the outer mkCast back out through the Lam
     -- to make another FunCo? If so, rethink.
     -- Lam x <$> recast (e `App` mkCast (Var x) (mkSymCo domCo)) ranCo
    where
      x = freshId (exprFreeVars e) "x" (pSnd (coercionKind domCo))
      -- TODO: take care with the directions
      -- TODO: drop prePostV
   recast e co
     | dom `eqType` repTy ran =
         Just $ varApps abstV [ran] [hasRepFromAbstCo co,e]
     | ran `eqType` repTy dom =
         Just $ varApps reprV [dom] [hasRepFromAbstCo (mkSymCo co),e]
     | AxiomInstCo {} <- co =
         -- co :: dom ~#R ran for a newtype instance dom and its representation ran.
         -- repCo :: Rep dom ~# ran
         let repCo = UnivCo UnsafeCoerceProv Representational (repTy dom) ran in
           dtrace "recast AxiomInstCo:" (ppr repCo) $
           Just $ Cast (mkCast e (TransCo co (mkSymCo (mkSubCo repCo)))) repCo
           -- Outer Cast instead of mkCast to avoid optimization.
     | SymCo (AxiomInstCo {}) <- co =
         -- co :: dom ~#R ran for a newtype instance ran
         -- repCo :: Rep ran ~# dom
         let repCo = UnivCo UnsafeCoerceProv Representational (repTy ran) dom in
           Just $ Cast (mkCast e (mkSymCo repCo)) (TransCo (mkSubCo repCo) co)
           -- recast (mkCast e (mkSymCo repCo)) (TransCo (mkSubCo repCo) co)
           -- 
           -- EXPERIMENT: return just a cast. I may have to change the receiver
           -- to use 'go' instead of 'tryReify', to avoid having the simplifier
           -- undo our work.
           -- Just (Cast (mkCast e (mkSymCo repCo)) (TransCo (mkSubCo repCo) co))
    where
      Pair dom ran = coercionKind co
--    recast (AppCo fun arg)
--      | dtrace "recast AppCo:" (ppr (fun,arg)) False = undefined
     -- Does this one ever fire anymore?
   -- TransCo must come after the abst (dom == Rep ran) and repr (ran == Rep
   -- dom) cases, since the AxiomInstCo (newtype) cases create transitive
   -- coercions having those shapes.
   recast e (TransCo inner outer) = -- Use at least one recursive recast so
                                    -- the simplifier doesn't recombine.
                                    dtrace "TransCo" empty $ -- order?
                                    recast (mkCast e inner) outer
   recast (unfoldMaybe -> Just e') co = dtrace "unfold castee" empty $
                                        Just $ Cast e' co
   recast _ co = dtrace ("recast: unhandled " ++ coercionTag co ++ " coercion:")
                   (ppr co {- <+> dcolon $$ ppr (coercionType co)-}) Nothing
   -- TODO: Check the type, in case the coercion is not
   repTy :: Unop Type
   repTy t = mkTyConApp repTc [t]
   -- Rep a -> a or a -> Rep a.
   unfolded :: Unop CoreExpr
   unfolded e = fromMaybe e (unfoldMaybe e)               
   -- Inline in applications (function part) and casts.
   unfoldMaybe :: ReExpr
   unfoldMaybe = traceRewrite "unfoldMaybe" $
                 \ e ->
                   dtrace "unfoldMaybe: isPrimApp" (parens (ppr e) <+> text "=" <+> ppr (isPrimApp e)) (return ()) >>
                   guard (not (isPrimApp e)) >>
                   onExprHead (traceRewrite "inlineMaybe" inlineMaybe) e
   inlineMaybe :: Id -> Maybe CoreExpr
   -- inlineMaybe v | dtrace "inlineMaybe" (ppr v) False = undefined
   inlineMaybe v = (inlineId <+ -- onInlineFail <+ traceRewrite "inlineClassOp"
                                inlineClassOp) v
   onInlineFail :: Id -> Maybe CoreExpr
   onInlineFail v =
     pprTrace "onInlineFail idDetails" (ppr v <+> colon <+> ppr (idDetails v))
     Nothing
   buildDictMaybe :: Type -> Maybe CoreExpr
   buildDictMaybe = buildDictionary hsc_env dflags guts inScope
   buildDict :: Type -> CoreExpr
   buildDict ty = fromMaybe (pprPanic "reify - couldn't build dictionary for" (ppr ty)) $
                  buildDictMaybe ty
   pprTrans :: (Outputable a, Outputable b) => String -> a -> b -> b
   pprTrans str a b = dtrace str (ppr a $$ "-->" $$ ppr b) b
   -- traceUnop :: (Outputable a, Outputable b) => String -> Unop (a -> b)
   -- traceUnop str f a = pprTrans str a (f a)
#if 0
   -- This version sometimes (usually/always?) fails to work. It used to be
   -- reliable. What happened?
   traceRewrite :: (Outputable a, Outputable b) =>
                   String -> Unop (a -> Maybe b)
   traceRewrite str f a = pprTrans str a <$> f a
#else
   traceRewrite :: (Outputable a, Outputable (f b)) =>
                   String -> Unop (a -> f b)
   traceRewrite str f a = pprTrans str a (f a)
#endif
   -- Apply a rewrite, lint the result, and check that the type is preserved.
   lintReExpr :: Unop ReExpr
   lintReExpr rew before =
     do after <- rew before
        let before' = mkReify before
            oops str doc = pprPanic ("reify post-transfo check. " ++ str)
                             (doc $$ ppr before' $$ "-->" $$ ppr after)
            beforeTy = exprType before'
            afterTy  = exprType after
        maybe (if beforeTy `eqType` afterTy then
                 return after
               else
                 oops "type change"
                  (ppr beforeTy <+> "vs" <+> ppr afterTy <+> "in"))
              (oops "Lint")
          (lintExpr dflags (varSetElems (exprFreeVars before)) before)
   mkCompose :: Binop CoreExpr
   g `mkCompose` f = varApps composeV [b,c,a] [g,f]
    where
      -- (.) :: forall b c a. (b -> c) -> (a -> b) -> a -> c
      Just (b,c) = splitFunTy_maybe (exprType g)
      Just (a,_) = splitFunTy_maybe (exprType f)
   mkPrePost f g = unfolded $ varApps prePostV [a,b,a',b'] [f,g]
    where
      -- (-->) :: forall a b a' b'.
      --          (a' -> a) -> (b -> b') -> ((a -> b) -> (a' -> b'))
      Just (a',a) = splitFunTy_maybe (exprType f)
      Just (b,b') = splitFunTy_maybe (exprType g)

-- I could also handle Let, but I think the simplifier does for me.

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

-- Split into Var head, type arguments, and other arguments (breaking at first
-- non-type).
unVarApps :: CoreExpr -> Maybe (Id,[Type],[CoreExpr])
unVarApps (collectArgs -> (Var v,allArgs)) = Just (v,tys,others)
 where
   (tys,others) = first (map unType) (span isTypeArg allArgs)
   unType (Type t) = t
   unType e        = pprPanic "unVarApps - unType" (ppr e)
unVarApps _ = Nothing

-- Types we know how to handle
reifiableType :: Type -> Bool
-- reifiableType ty | pprTrace "reifiableType" (ppr ty) False = undefined
reifiableType (coreView -> Just ty) = reifiableType ty
reifiableType (splitFunTy_maybe -> Just (dom,ran)) = reifiableType dom && reifiableType ran
reifiableType ty = not (or (($ ty) <$> bads))
 where
   bads = [ try "isForAllTy"  $ isForAllTy
          , try "non-lifted"  $ not . isLiftedTypeKind . typeKind
          , try "isPredTy"    $ isPredTy
          , try "badTyConApp" $ badTyConApp
          ]
   try :: SDoc -> Unop (Type -> Bool)
   try _why p t = {-(if b then
                    pprTrace "reifiableType"
                      (ppr t <+> dcolon <+> ppr (typeKind t) <+> "rejected via" <+> _why)
                  else id)-} b
    where b = p t

-- typeKind (ForAllTy (Anon _) _) = liftedTypeKind

badTyConApp :: Type -> Bool
-- badTyConApp ty | pprTrace "badTyConApp" (ppr ty) False = undefined
badTyConApp (coreView -> Just ty)            = badTyConApp ty
badTyConApp (tyConAppTyCon_maybe -> Just tc) = badTyCon tc
badTyConApp _                                = False

badTyCon :: TyCon -> Bool
-- badTyCon tc | pprTrace "badTyCon" (ppr tc) False = undefined
badTyCon (tyConName -> name) =
  qualifiedName name `elem`
     [ "GHC.Types.[]"
     , "GHC.Integer.Type.Integer"          -- or use isIntegerTy in badTyConApp
     , "GHC.Types.IO"
     , "ReificationRules.Exp.E"            -- TODO: Fix for HOS or okay?
     ]
  || badModule (moduleNameString . moduleName <$> nameModule_maybe name)
 where
   badModule = maybe False (`elem` badMods)
   badMods = [ "Circat.Circuit", "Circat.Category", "Circat.Classes" ]

reifiableExpr :: CoreExpr -> Bool
reifiableExpr e = not (isTyCoArg e) && reifiableType (exprType e)

{--------------------------------------------------------------------
    Primitive translation
--------------------------------------------------------------------}

#if 1
-- Generate code for MonoPrims
monoPrimDefs :: String
monoPrimDefs = unlines $ sort
  [ printf "%-7s = %6sP :: Prim (%-6s %-6s)" pat prim tyOp ty
  | (_cls,tyOp,tys,ps) <- stdClassOpInfo, ty <- tys
  , (_op,prim) <- ps, let pat = primAt prim ty ]
#endif

stdClassOpInfo :: [(String,String,[String],[(String,String)])]
stdClassOpInfo =
   [ ( "Eq","BinRel",bifd
     , [("==","Eq"), ("/=","Ne")])
   , ( "Ord","BinRel",bifd
     , [("<","Lt"),(">","Gt"),("<=","Le"),(">=","Ge")])
   , ( "Num","Unop",ifd
     , [("negate","Negate")])
   , ( "Num","Binop",ifd
     , [("+","Add"),("-","Sub"),("*","Mul")])
   , ( "Bogus","PowIop",ifd
     , [("^","PowI")])
   , ( "Floating","Unop",fd
     , [("exp","Exp"),("cos","Cos"),("sin","Sin")])
   , ( "Fractional","Unop",fd
     , [("recip","Recip")])
   , ( "Fractional","Binop",fd
     , [("/","Divide")])
   ]
 where
   fd   = ["Float","Double"]
   ifd  = "Int" : fd
   bifd = "Bool" : ifd

-- Name of prim type specialization in MonoPrims
primAt :: String -> String -> String
primAt prim ty = toLower (head ty) : prim

-- Map "$fNumInt_$c+" to MonoPrims names "iAdd" etc
stdMethMap :: M.Map String String
stdMethMap = M.fromList $
  [ (opName cls ty op prim, primAt prim ty)
  | (cls,_,tys,ps) <- stdClassOpInfo, ty <- tys, (op,prim) <- ps ]
  ++
  [ ("fst","exlP"), ("snd","exrP"), ("(,)","pairP")
  -- Experiment: let these boolean operations inline,
  -- and rediscover them in circuit optimization.
  , ("not","notP"), ("||","orP"), ("&&","andP")
  , ("ifThenElse","ifP")
  , ("eqDouble","dEq"), ("eqFloat","fEq")  -- odd exceptions
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

reifyRule :: ReifyEnv -> ModGuts -> CoreRule
reifyRule env guts =
  BuiltinRule { ru_name  = fsLit "reifyP"
              , ru_fn    = varName (reifyV env)
              , ru_nargs = 2  -- including type arg
              , ru_try   = \ dflags inScope _fn [_ty,arg] ->
                              reify env guts dflags inScope arg
              }

plugin :: Plugin
plugin = defaultPlugin { installCoreToDos = install }

install :: [CommandLineOption] -> [CoreToDo] -> CoreM [CoreToDo]
install opts todos =
  do -- pprTrace ("Reify install " ++ show opts) empty (return ())
     dflags <- getDynFlags
     -- Unfortunately, the plugin doesn't work in GHCi. Until I can fix it,
     -- disable under GHCi, so we can at least type-check conveniently.
     if hscTarget dflags == HscInterpreted then
        return todos
      else
       do reinitializeGlobals
          env <- mkReifyEnv opts
          -- Add the rule after existing ones, so that automatically generated
          -- specialized reify rules are tried first.
          let addRule guts = pure (on_mg_rules (++ [reifyRule env guts]) guts)
          return $   CoreDoPluginPass "Add reify definitions" (return . addReifyRules env)
                   : CoreDoPluginPass "Reify insert rule" addRule
                   : CoreDoSimplify 2 mode
                   : todos
 where
   -- Extra simplifier pass for reification.
   -- Rules on, no inlining, and case-of-case.
   mode = SimplMode { sm_names      = ["Reify simplifier pass"]
                    , sm_phase      = InitialPhase
                    , sm_rules      = True  -- important
                    , sm_inline     = False -- important
                    , sm_eta_expand = False -- ??
                    , sm_case_case  = True  -- important
                    }

-- type PluginPass = ModGuts -> CoreM ModGuts

addReifyRules :: ReifyEnv -> Unop ModGuts
addReifyRules (ReifyEnv { .. }) guts = -- pprTrace "addReifyRules old rules" (ppr (mg_rules guts)) $
                                       -- pprTrace "addReifyRules new rules" (ppr rules) $
                                       on_mg_rules (++ rules) guts
 where
   rules = reifyDefRules =<< mg_binds guts
#if 1
   reifyDefRules :: CoreBind -> [CoreRule]
   reifyDefRules = catMaybes . map defRule . flattenBinds . pure
    where
      defRule :: (Id,CoreExpr) -> Maybe CoreRule
      defRule (v,rhs) = -- pprTrace "reifyDefRules" (ppr v) $
                        dtrace "mbRule" (ppr mbRule) $
                        mbRule
       where
         mbRule :: Maybe CoreRule
         mbRule = rule v <$> collectOuter rhs
#else
   reifyDefRules :: CoreBind -> [CoreRule]
   reifyDefRules (Rec bs) = -- pprTrace "reifyDefRules Rec" (ppr (fst <$> bs)) $
                            pprTrace "reifyDefRules Rec group" (ppr (Rec bs)) $
                            [] -- concat (reifyDefRules <$> bs)
   reifyDefRules (NonRec v rhs) = pprTrace "reifyDefRules" (ppr v) $
                                  dtrace "rules" (ppr rs) $
                                  rs
    where
      rs :: [CoreRule]
      rs = maybeToList (rule v <$> collectOuter rhs)
#endif
   rule :: Id -> ([Var],CoreExpr) -> CoreRule
   rule v (vs,rhs) = mkRule (mg_module guts)
                            False                             -- auto
                            False                             -- local
                            (fsLit ("reify " ++ uqVarName v)) -- name
                            AlwaysActive                      -- act
                            (varName reifyV)                  -- fn
                            vs                                -- bndrs
                            args                              -- args
                            rhs                               -- rhs
     where
       args = [Type (exprType arg),arg]
       arg = mkCoreApps (Var v) (varToCoreExpr <$> vs)
   collectOuter :: CoreExpr -> Maybe ([Var],CoreExpr)
   collectOuter e | dtrace "collectOuter" (ppr e <+> dcolon <+> ppr (exprType e)) False = undefined
                  | isTyCoDictArg e = dtrace "collectOuter isTyCoDictArg" empty $
                                      Nothing
                  | otherwise       = 
     case (exprType e, e) of
       (_, Lam v body) | isTyCoVar v || isDictTy (idType v) ->
         dtrace "collectOuter Lam" empty $
         first (v:) <$> collectOuter body
       -- TODO: Rethink this case. etaExpand can leave casts unchanged, which
       -- was causing an infinite loop here.
       -- 
       -- (FunTy dom _, _) | not (reifiableType dom), not (isLam e) -> dtrace "collectOuter non-re domain" (ppr dom) $
       --                                                              etaRetry
       (ForAllTy (Named {}) _,_)          -> dtrace "collectOuter ForAllTy" empty $
                                             etaRetry
       (ty,_)           | reifiableExpr e -> dtrace "collectOuter done" empty $
                                             Just ([], varApps reifyV [ty] [e])
                        | otherwise       -> dtrace "collectOuter bailing:" empty $
                                             Nothing
    where
      etaRetry = collectOuter (etaExpand 1 e)
      isLam (Lam {}) = True
      isLam _        = False


type PrimFun = Type -> Id -> [Type] -> Maybe CoreExpr

mkReifyEnv :: [CommandLineOption] -> CoreM ReifyEnv
mkReifyEnv opts = do
  -- liftIO $ putStrLn ("Options: " ++ show opts)
  hsc_env <- getHscEnv
  let tracing = "trace" `elem` opts
      dtrace :: String -> SDoc -> a -> a
      dtrace str doc | tracing   = pprTrace str doc
                     | otherwise = id
      lookupRdr :: ModuleName -> (String -> OccName) -> (Name -> CoreM a) -> String -> CoreM a
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
  ruleBase <- getRuleBase
  dtrace "mkReifyEnv: getRuleBase ==" (ppr ruleBase) (return ())
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
  unIV     <- findExpId "unI#"
  idV      <- findBaseId "id"
  composeV <- findBaseId "."
  prePostV <- findMiscId "-->"
  primMap  <- mapM findMonoId stdMethMap
--   let RuleInfo rules _ = ruleInfo (idInfo reifyV) in
--     do drace "reify install: reifyP rule info" (ppr rules) (return ())
--        drace "reify install: reifyV unique: " (ppr (idUnique reifyV)) (return ())
  let lookupPrim v tys = M.lookup (tweak (uqVarName v) tys) primMap
      primFun ty v tys = (\ primId -> varApps constV [ty] [varApps primId tys {- [] -} []])
                         <$> lookupPrim v tys
      isPrimApp (unVarApps -> Just (v,tys,_)) = -- isJust (isClassOpId_maybe v) || -- experimenetal
                                                isJust (lookupPrim v tys)
      isPrimApp _ = False
      -- tweak nm ts | pprTrace "mkReifyEnv / tweak" (nm <+> ppr ts) False = undefined
      tweak "^" [a,isIntTy -> True] | isIntTy    a = "$fBogusInt_$c^"
                                    | isFloatTy  a = "$fBogusFloat_$c^"
                                    | isDoubleTy a = "$fBogusDouble_$c^"
      tweak nm _ = nm
  hasRepTc   <- findRepTc "HasRep"
  repTc      <- findRepTc "Rep"
  hasRepMeth <- hasRepMethodM tracing hasRepTc repTc idV
  toLitV     <- findExpId "litE"
  hasLitTc   <- findTc "ReificationRules.Prim" "HasLit"
  hasLit     <- toLitM hasLitTc toLitV
  circuitTc  <- findTc "Circat.Circuit" ":>"
  ifCatTc    <- findTc "Circat.Classes" "IfCat"
  epTc       <- findTc "ReificationRules.HOS" "EP"
  let epTy      = mkTyConApp epTc []
      circuitTy = mkTyConApp circuitTc []
      ifCatTy t = mkTyConApp ifCatTc [circuitTy,t]
      
      -- New ones
      idAt t = Var idV `App` Type t     -- varApps idV [t] []
      [hasRepDc] = tyConDataCons hasRepTc
      mkHasRep :: Binop CoreExpr
      mkHasRep repr abst = conApps hasRepDc [ty] [repr,abst]
       where
         FunTy ty _ = exprType repr
      -- co :: Rep t ~#R t, i.e., abst. repr comes first in the dictionary.
      hasRepFromAbstCo co = mkHasRep (caster (mkSymCo co)) (caster co)
       where
         Pair dom ran = coercionKind co
      caster :: Coercion -> CoreExpr
      caster co@(pFst . coercionKind -> dom) =
        mkCast (idAt dom) (mkFunCo Representational (mkRepReflCo dom) co)

  return (ReifyEnv { .. })

--   primTc     <- findTc "ReificationRules.Prim" "Prim"

      -- findDc = lookupTh mkDataOcc lookupDataCon
      -- findPrimDc = findDc "ReificationRules.Prim"

-- * I'm assuming that it's safe to reuse x's unique here, since x is
-- eliminated. If not, use uniqAway x and then setVarType.

type HasRepMeth = DynFlags -> ModGuts -> InScopeEnv -> Type -> Maybe (Id -> CoreExpr)

hasRepMethodM :: Bool -> TyCon -> TyCon -> Id -> CoreM HasRepMeth
hasRepMethodM tracing hasRepTc repTc _idV =
  do hscEnv <- getHscEnv
     _eps   <- liftIO (hscEPS hscEnv)
     return $ \ dflags guts inScope ty ->
       let dtrace str doc a | tracing   = pprTrace str doc a
                            | otherwise = a
           repTy = mkTyConApp repTc [ty]
#if 1
           newtypeDict :: Maybe CoreExpr
           newtypeDict = Nothing
#else
           newtypeDict :: Maybe (CoreExpr,(Coercion,Type))
           newtypeDict =
             do (tc,tyArgs) <- splitTyConApp_maybe ty
                (tvs,newtyRhs,_coax) <- unwrapNewTyCon_maybe tc
                -- TODO: refactor to isolate the Maybe stuff.
                -- dtrace "newtypeDict. coax:" (ppr _coax) (return ())
                let ty'   = substTy (zipTvSubst tvs tyArgs) newtyRhs
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
           findDict :: Maybe CoreExpr
           findDict = buildDictionary hscEnv dflags guts inScope
                         (mkTyConApp hasRepTc [ty])
           mkMethApp dict =
             dtrace "hasRepMeth" (ppr ty <+> "-->" <+> ppr dict) $
             \ meth -> varApps meth [ty] [dict]
       in
          -- Real dictionary or synthesize
          mkMethApp <$> (findDict <|> newtypeDict)

type HasLit = DynFlags -> ModGuts -> InScopeEnv -> ReExpr

toLitM :: TyCon -> Id -> CoreM HasLit
toLitM hasLitTc toLitV =
  do hscEnv <- getHscEnv
     return $ \ dflags guts inScope e ->
       guard (isLiteral e) >>
       let ty = exprType e
           lfun :: CoreExpr -> CoreExpr
           lfun dict = -- dtrace "toLit" (ppr e) $
                       varApps toLitV [ty] [dict,e]
       in
         lfun <$> buildDictionary hscEnv dflags guts inScope
                    (mkTyConApp hasLitTc [ty])
 where
   isLiteral (collectArgs -> (Var v, _)) =
     isJust (isDataConId_maybe v) ||
     uqVarName v `elem`
       [ "$fNumInt_$cfromInteger", "$fNumFloat_$cfromInteger"
       , "$fNumDouble_$cfromInteger","int2Double" ]
   isLiteral _ = False

-- TODO: check args in isLiteral to make sure that they don't need reifying.

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
subst ps = substExpr "subst" (foldr add emptySubst ps)
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

collectTysDictsArgs :: CoreExpr -> (CoreExpr,[Type],[CoreExpr])
collectTysDictsArgs e = (h,tys,dicts)
 where
   (e',dicts) = collectArgsPred isPred e
   (h,tys)    = collectTyArgs e'
   isPred ex  = not (isTyCoArg ex) && isPredTy (exprType ex)

collectArgsPred :: (CoreExpr -> Bool) -> CoreExpr -> (CoreExpr,[CoreExpr])
collectArgsPred p = go []
 where
   go args (App fun arg) | p arg = go (arg:args) fun
   go args e                     = (e,args)

collectTyCoDictArgs :: CoreExpr -> (CoreExpr,[CoreExpr])
collectTyCoDictArgs = collectArgsPred isTyCoDictArg

isTyCoDictArg :: CoreExpr -> Bool
isTyCoDictArg e = isTyCoArg e || isPredTy (exprType e)

-- isConApp :: CoreExpr -> Bool
-- isConApp (collectArgs -> (Var (isDataConId_maybe -> Just _), _)) = True
-- isConApp _ = False

-- TODO: More efficient isConApp, discarding args early.

stringExpr :: String -> CoreExpr
stringExpr = Lit . mkMachString

varNameExpr :: Id -> CoreExpr
varNameExpr = stringExpr . uniqVarName

pattern FunTy :: Type -> Type -> Type
pattern FunTy dom ran <- (splitFunTy_maybe -> Just (dom,ran))
 where FunTy = mkFunTy

-- TODO: Replace explicit uses of splitFunTy_maybe

-- TODO: Look for other useful pattern synonyms

pattern FunCo :: Role -> Coercion -> Coercion -> Coercion
pattern FunCo r dom ran <- TyConAppCo r (isFunTyCon -> True) [dom,ran]
 where FunCo = mkFunCo

onCaseRhs :: Type -> Unop (Unop CoreExpr)
onCaseRhs altsTy' f (Case scrut v _ alts) =
  Case scrut v altsTy' (onAltRhs f <$> alts)
onCaseRhs _ _ e = pprPanic "onCaseRhs. Not a case: " (ppr e)

onAltRhs :: Unop CoreExpr -> Unop CoreAlt
onAltRhs f (con,bs,rhs) = (con,bs,f rhs)

-- To help debug. Sometimes I'm unsure what constructor goes with what ppr.
coercionTag :: Coercion -> String
coercionTag Refl        {} = "Refl"
coercionTag TyConAppCo  {} = "TyConAppCo"
coercionTag AppCo       {} = "AppCo"
coercionTag ForAllCo    {} = "ForAllCo"
coercionTag CoVarCo     {} = "CoVarCo"
coercionTag AxiomInstCo {} = "AxiomInstCo"
coercionTag UnivCo      {} = "UnivCo"
coercionTag SymCo       {} = "SymCo"
coercionTag TransCo     {} = "TransCo"
coercionTag AxiomRuleCo {} = "AxiomRuleCo"
coercionTag NthCo       {} = "NthCo"
coercionTag LRCo        {} = "LRCo"
coercionTag InstCo      {} = "InstCo"
coercionTag CoherenceCo {} = "CoherenceCo"
coercionTag KindCo      {} = "KindCo"
coercionTag SubCo       {} = "SubCo"

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

onExprHead :: (Id -> Maybe CoreExpr) -> ReExpr
onExprHead h = (fmap.fmap) simpleOptExpr $
               go id
 where
   go cont (Var v)       = cont <$> h v
   go cont (App fun arg) = go (cont . (`App` arg)) fun
   go cont (Cast e co)   = go (cont . (`Cast` co)) e
   go _ _                = Nothing

-- The simpleOptExpr here helps keep simplification going.

-- Identifier not occurring in a given variable set
freshId :: VarSet -> String -> Type -> Id
freshId used nm ty =
  uniqAway (mkInScopeSet used) $
  mkSysLocal (fsLit nm) (mkBuiltinUnique 17) ty
