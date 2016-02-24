{-# LANGUAGE GADTs, KindSignatures #-}
{-# OPTIONS_GHC -Wall #-}

-- {-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP
-- {-# OPTIONS_GHC -fno-warn-unused-binds   #-} -- TEMP

----------------------------------------------------------------------
-- |
-- Module      :  ReificationRules.HOS
-- Copyright   :  (c) 2016 Conal Elliott
-- License     :  BSD3
--
-- Maintainer  :  conal@conal.net
-- Stability   :  experimental
-- 
-- Higher-order syntax interface to lambda expressions
--
-- "Using Circular Programs for Higher-Order Syntax" by Emil Axelsson and Koen Claessen
-- <http://www.cse.chalmers.se/~emax/documents/axelsson2013using.pdf>.
----------------------------------------------------------------------

module ReificationRules.HOS where

-- TODO: explicit exports

import Data.Map

import LambdaCCC.Lambda (E(..),V(..),Pat(..),reifyE,evalE)
import LambdaCCC.Prim (Prim(..))

type Name = String

type NameMap = Map Name Int

bot :: NameMap
bot = mempty

lub :: NameMap -> NameMap -> NameMap
lub = unionWith max

type E' p a = (E p a, NameMap)

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

constE :: p a -> E' p a
constE p = (ConstE p, bot)

type EP a = E' Prim a

appP :: EP (a -> b) -> EP a -> EP b
appP = app

lamP :: Name -> (EP a -> EP b) -> EP (a -> b)
lamP = lam

reifyP :: a -> EP a
reifyP e = (reifyE e,bot)

evalP :: EP a -> a
evalP (e,_) = evalE e

{--------------------------------------------------------------------
    Tests
--------------------------------------------------------------------}

type Unop a = a -> a
type Binop a = a -> Unop a
type Ternop a = a -> Binop a

twice :: Unop (Unop a)
twice f = f . f

app2 :: E' p (a1 -> a -> b) -> E' p a1 -> E' p a -> E' p b
app2 f a b = app (app f a) b

notOf :: Unop (EP Bool)
notOf = app (constE NotP)

orOf :: Binop (EP Bool)
orOf = app2 (constE OrP)

-- orOf a b = app (app (constE OrP) a) b

t1 :: EP (Bool -> Bool)
t1 = constE NotP
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
