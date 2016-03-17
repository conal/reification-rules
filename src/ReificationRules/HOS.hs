{-# LANGUAGE CPP, GADTs, KindSignatures, ExplicitForAll, ConstraintKinds, MagicHash, TypeOperators #-}
{-# OPTIONS_GHC -Wall #-}

-- Prevent warnings about inlining fst, snd, not, etc.
-- Might be worthwhile to turn back on and inspect warnings occasionally.
{-# OPTIONS_GHC -fno-warn-inline-rule-shadowing #-}

#define Testing

-- {-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP
#ifdef Testing
{-# OPTIONS_GHC -fno-warn-unused-binds   #-} -- TEMP
#endif

----------------------------------------------------------------------
-- |
-- Module      :  ReificationRules.HOS
-- Copyright   :  (c) 2016 Conal Elliott
-- License     :  BSD3
--
-- Maintainer  :  conal@conal.net
-- Stability   :  experimental
-- 
-- Higher-order syntax interface to lambda expressions. Based on "Using Circular
-- Programs for Higher-Order Syntax" by Emil Axelsson and Koen Claessen
-- <http://www.cse.chalmers.se/~emax/documents/axelsson2013using.pdf>.
----------------------------------------------------------------------

module ReificationRules.HOS
  ( EP,toE,constP,appP,lamP,letP,letPairP,evalP,reifyP,reify, litE
  , abst,repr,abst',repr', abstP,reprP
  ) where

import Data.Map

import GHC.Types (type (~~))  -- 
import GHC.Prim (Addr#)
import GHC.CString (unpackCString#)

#ifdef Testing
import Circat.Misc (Unop,Binop,Ternop,(:*))
#endif
import qualified Circat.Rep as Rep
import Circat.Rep (HasRep,Rep)

-- import Circat.Doubli
-- import Circat.Pair (Pair(..)) -- TEMP
-- import qualified Circat.RTree as R
-- import qualified Circat.LTree as L

import ReificationRules.Misc (Evalable)
import ReificationRules.Exp
import ReificationRules.Prim
import ReificationRules.ShowUtils

-- TODO: Drastically trim LambdaCCC.Lambda. See NewLambda for a start.

type NameMap = Map Name Int

bot :: NameMap
bot = mempty

lub :: NameMap -> NameMap -> NameMap
lub = unionWith max

type E' p a = (E p a, NameMap)

toE :: E' p a -> E p a
toE = fst

app :: E' p (a -> b) -> E' p a -> E' p b
(f,mf) `app` (x,mx) = (f :^ x, mf `lub` mx)

-- Establish a new name based on nm, augmenting name map as needed
bump :: Unop (Name, NameMap)
bump (nm,m) = (maybe nm ((nm ++) . show) mbN,m')
 where
   (mbN,m') = insertLookupWithKey (const (+)) nm 1 m

-- insertLookupWithKey ::
--   Ord k => (k -> a -> a -> a) -> k -> a -> Map k a -> (Maybe a, Map k a)

lam :: Name -> (E' p a -> E' p b) -> E' p (a -> b)
lam nma f = (Lam (VarPat (V nma')) body, mb)
 where
   (body,ma) = f (Var (V nma'),bot)
   (nma',mb) = bump (nma,ma)

lamPair :: Name -> Name -> (E' p a -> E' p b -> E' p c) -> E' p (a :* b -> c)
lamPair nma nmb f = (Lam (VarPat (V nma') :$ VarPat (V nmb')) body, mc)
 where
   (body,ma) = f (Var (V nma'),bot) (Var (V nmb'),bot)
   (nma',mb) = bump (nma,ma)
   (nmb',mc) = bump (nmb,mb)

-- TODO: Maybe switch to bump :: Name -> State NameMap Name.
-- Especially convenient with lamPair. Maybe not, considering the circularity.

letE' :: Name -> E' p a -> (E' p a -> E' p b) -> E' p b
letE' x a f = lam x f `app` a

letPair' :: Name -> Name -> E' p (a :* b) -> (E' p a -> E' p b -> E' p c) -> E' p c
letPair' x y ab f = lamPair x y f `app` ab

constE' :: p a -> E' p a
constE' p = (ConstE p, bot)

reifyE' :: a -> E' p a
reifyE' e = (reifyE e,bot)

evalE' :: (Show' p, HasOpInfo p, Evalable p) => E' p a -> a
evalE' (e,_) = evalE e

{--------------------------------------------------------------------
    Specializations to Prim
--------------------------------------------------------------------}

-- TODO: Eliminate these specialized definitions and pass Prim explicitly during
-- reification.

type EP a = E' Prim a

type Name# = Addr#

appP :: forall a b. EP (a -> b) -> EP a -> EP b
appP = app
{-# NOINLINE appP #-}

-- ## BAZINGA!

lamP :: forall a b. Name# -> (EP a -> EP b) -> EP (a -> b)
lamP x = lam (unpackCString# x)
{-# NOINLINE lamP #-}

letP :: forall a b. Name# -> EP a -> (EP a -> EP b) -> EP b
letP x = letE' (unpackCString# x)

letPairP :: forall a b c. Name# -> Name# -> EP (a :* b) -> (EP a -> EP b -> EP c) -> EP c
letPairP x y = letPair' (unpackCString# x) (unpackCString# y)

-- letP :: forall a b. Name# -> EP a -> EP b -> EP b
-- letP x a b = Lam (varPat# x) b `appP` a
-- {-# NOINLINE letP #-}

reifyP :: forall a. a -> EP a
reifyP = reifyE'
{-# NOINLINE reifyP #-}

reify :: a -> E Prim a
reify _ = error "reify: not implemented"
-- reify f = renameVars (first (reifyP f))
{-# NOINLINE reify #-}

{-# RULES "reify & rename" forall f. reify f = renameVars (fst (reifyP f)) #-}
-- {-# RULES "reify & drop name-map (temporary)" forall f. reify f = fst (reifyP f) #-}

evalP :: forall a. EP a -> a
evalP = evalE'
{-# NOINLINE evalP #-}

constP :: forall a. Prim a -> EP a
constP = constE'
{-# NOINLINE constP #-}

-- The explicit 'forall's here help with reification.

-- The NOINLINEs are just to reduce noise when examining Core output.
-- Remove them later.

{--------------------------------------------------------------------
    HasRep
--------------------------------------------------------------------}

-- Synonyms for HasRep methods. Using these names postpones the method selector
-- unfolding built-in rule.

-- abst :: HasRep a => Rep a -> a
-- repr :: HasRep a => a -> Rep a

abst :: (HasRep a, Rep a ~~ a') => a' -> a
repr :: (HasRep a, Rep a ~~ a') => a -> a'

abst = Rep.abst
repr = Rep.repr

{-# NOINLINE abst #-}
{-# NOINLINE repr #-}

-- abst' :: HasRep a => Rep a -> a
-- repr' :: HasRep a => a -> Rep a

abst' :: (HasRep a, Rep a ~~ a') => a' -> a
repr' :: (HasRep a, Rep a ~~ a') => a -> a'

abst' = Rep.abst
repr' = Rep.repr

-- I don't know why, but I was unable to find AbstP or ReprP from Plugin.

-- abstP :: HasRep a => EP (Rep a -> a)
-- reprP :: HasRep a => EP (a -> Rep a)

abstP :: (HasRep a, Rep a ~~ a') => EP (a' -> a)
reprP :: (HasRep a, Rep a ~~ a') => EP (a -> a')

abstP = constP AbstP
reprP = constP ReprP

litE :: HasLit a => a -> EP a
litE = constP . LitP . toLit

#ifdef Testing

{--------------------------------------------------------------------
    Tests
--------------------------------------------------------------------}

app1 :: p (a -> b) -> E' p a -> E' p b
app1 p = app (constE' p)

app2 :: p (a -> b -> c) -> E' p a -> E' p b -> E' p c
app2 f a b = app (app1 f a) b

twice :: Unop (Unop a)
twice f = f . f

notOf :: Unop (EP Bool)
notOf = app1 NotP

orOf :: Binop (EP Bool)
orOf = app2 OrP

t1 :: EP (Bool -> Bool)
t1 = constE' NotP
-- (not,fromList [])

t2 :: EP (Unop Bool)
t2 = lam "b" notOf
-- (\ b -> not b,fromList [("b",1)])

t3 :: EP (Unop Bool)
t3 = lam "b" (twice notOf)
-- (\ b -> not (not b),fromList [("b",1)])

t4 :: EP (Unop Bool)
t4 = lam "b" (twice (twice notOf))
-- (\ b -> not (not (not (not b))),fromList [("b",1)])

t5 :: EP (Unop Bool)
t5 = lam "x" (\ x -> orOf x (notOf x))
-- (\ x -> x || not x,fromList [("x",1)])

t6 :: EP (Binop Bool)
t6 = lam "x" $ \ x -> lam "x" $ \ y -> orOf x (notOf y)
-- (\ x1 -> \ x -> x1 || not x,fromList [("x",2)])

t7 :: EP (Ternop Bool)
t7 = lam "x" $ \ x -> lam "x" $ \ y -> lam "x" $ \ z -> orOf x (notOf (orOf y z))
-- (\ x2 -> \ x1 -> \ x -> x2 || not (x1 || x),fromList [("x",3)])

#endif
