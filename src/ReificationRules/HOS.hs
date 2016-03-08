{-# LANGUAGE CPP, GADTs, KindSignatures, ExplicitForAll, ConstraintKinds, MagicHash, TypeOperators #-}
{-# OPTIONS_GHC -Wall #-}

-- Prevent warnings about inlining fst, snd, not, etc.
-- Might be worthwhile to turn back on and inspect warnings occasionally.
{-# OPTIONS_GHC -fno-warn-inline-rule-shadowing #-}

-- #define Testing

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
  ( EP,toE,appP,lamP,reifyP,evalP,constP
  , abst,repr,abst',repr', abstP,reprP, abstReprScrut 
  ) where

-- TODO: explicit exports

import Data.Map

import GHC.Types (type (~~),Int(..))
import GHC.Prim (Addr#)
import GHC.CString (unpackCString#)

#ifdef Testing
import Circat.Misc (Unop,Binop,Ternop)
#endif
import qualified Circat.Rep as Rep
import Circat.Rep (HasRep,Rep)

import Circat.Doubli
-- import Circat.Pair (Pair(..)) -- TEMP

import ReificationRules.Exp
import ReificationRules.Prim

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

lam :: Name -> (E' p a -> E' p b) -> E' p (a -> b)
lam nm f = (Lam (VarPat (V nm')) body, mf)
 where
   (body,mb) = f (Var (V nm'),bot)
   (mbN,mf)  = insertLookupWithKey (const (+)) nm 1 mb
   nm'       = maybe nm ((nm ++) . show) mbN

-- insertLookupWithKey ::
--   Ord k => (k -> a -> a -> a) -> k -> a -> Map k a -> (Maybe a, Map k a)

constE' :: p a -> E' p a
constE' p = (ConstE p, bot)

reifyE' :: a -> E' p a
reifyE' e = (reifyE e,bot)

evalE' :: E' p a -> a
evalE' (e,_) = evalE e

{--------------------------------------------------------------------
    Specializations to Prim
--------------------------------------------------------------------}

-- TODO: Eliminate these specialized definitions and pass Prim explicitly during
-- reification.

type EP a = E' Prim a

appP :: forall a b. EP (a -> b) -> EP a -> EP b
appP = app
{-# NOINLINE appP #-}

-- lamP :: forall a b. Name -> (EP a -> EP b) -> EP (a -> b)
-- lamP = lam
-- {-# NOINLINE lamP #-}

lamP :: forall a b. Addr# -> (EP a -> EP b) -> EP (a -> b)
lamP addr = lam (unpackCString# addr)
{-# NOINLINE lamP #-}

reifyP :: forall a. a -> EP a
reifyP = reifyE'
{-# NOINLINE reifyP #-}

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

-- Probably move elsewhere

abstReprScrut :: HasRep a => a -> a
abstReprScrut a = abst' (repr a)

-- abstReprScrut a = Rep.abst (repr a)


-- abstReprd :: a -> a
-- abstReprd = id
-- {-# NOINLINE abstReprd #-} -- for now

{--------------------------------------------------------------------
    Rules
--------------------------------------------------------------------}

litE :: HasLit a => a -> EP a
litE = constP . LitP . toLit

{-# RULES

"reifyP . evalP" forall e. reifyP (evalP e) = e

"reify abst" reifyP abst = constP AbstP
"reify repr" reifyP repr = constP ReprP

-- -- I don't know why these rules don't fire.
-- "reify abst" reifyP abst = abstP
-- "reify repr" reifyP repr = reprP

"reifyP not"  reifyP not  = constP NotP
"reifyP (&&)" reifyP (&&) = constP AndP
"reifyP (||)" reifyP (||) = constP OrP

"reifyP fst" reifyP fst = constP ExlP
"reifyP snd" reifyP snd = constP ExrP
"reifyP (,)" reifyP (,) = constP PairP

"reifyP True"  reifyP True  = litE True
"reifyP False" reifyP False = litE False

"reifyP I#" forall n. reifyP (I#     n) = litE (I# n)
"reifyP D#" forall n. reifyP (Doubli n) = litE (Doubli n)

-- TODO: Drop Doubli, and use
-- 
-- "reifyP D#" forall n. reifyP (D# n) = litE (D# n)

-- "reifyP :#" forall x y. reifyP (x :# y) = reifyP (abst (x,y))

-- "reifyP :#" reifyP (:#) = reifyP (\ x y -> abst (x,y))

-- TODO: Move the RHS reification elsewhere so it happens only once.


  #-}

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
