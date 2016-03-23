{-# LANGUAGE CPP, ScopedTypeVariables, LambdaCase #-}
{-# LANGUAGE FlexibleContexts #-}  -- go

-- For Pair (to remove)
{-# LANGUAGE TypeFamilies #-}

-- For HR experiment
{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies, FlexibleInstances #-}

{-# OPTIONS_GHC -Wall #-}

{-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP
{-# OPTIONS_GHC -fno-warn-unused-binds   #-} -- TEMP

----------------------------------------------------------------------
-- |
-- Module      :  Tests
-- Copyright   :  (c) 2016 Conal Elliott
-- License     :  BSD3
--
-- Maintainer  :  conal@conal.net
-- Stability   :  experimental
-- 
-- Reification tests
----------------------------------------------------------------------

module RuleTest where

-- TODO: explicit exports

import GHC.Exts (inline)

import ReificationRules.Misc (Unop)
import ReificationRules.HOS (EP,toE,reifyP,repr,abst,constP,abstP)
import ReificationRules.Prim (Prim(..))
import ReificationRules.Run (run,Okay)

import TypeUnary.TyNat (S,Z)
import Circat.Pair
import Circat.RTree

import Circat.Rep (HasRep,Rep)
import qualified Circat.Rep as R

scrutinee :: a -> a
scrutinee = id
-- {-# NOINLINE scrutinee #-}

scrutinee' :: HasRep a => a -> Rep a
scrutinee' a = scrutinee (repr a)

{-# RULES

"scrutinee Pair"    forall p. scrutinee p = case repr p of (a,b) -> a :# b
"scrutinee RTree Z" forall t. scrutinee t = L (repr t)
"scrutinee RTree S" forall t. scrutinee t = B (repr t)

-- "reify :#" forall a b . reifyP (a :# b) = reifyP (abst (a,b))
-- "reify L"  forall a   . reifyP (L a )   = reifyP (abst a )
-- "reify B"  forall ts  . reifyP (B ts)   = reifyP (abst ts)

"reify :#" reifyP (:#) = abstP2
"reify L"  reifyP L    = abstP
"reify B"  reifyP B    = abstP

-- "reify L"  reifyP L    = reifyP abst
-- "reify B"  reifyP B    = reifyP abst

-- -- Doesn't work. Why not?
-- "reify abst" reifyP abst = constP AbstP
-- "reify repr" reifyP repr = constP ReprP

 #-}

-- abst2 :: (HasRep p, Rep p ~ (a,b)) => a -> b -> p
-- abst2 = curry abst
-- -- abst2 a b = abst (a,b)

-- "reify :#" reifyP (:#) = reifyP (inline abst2)

abstP2 :: (HasRep p, Rep p ~ (a,b)) => EP (a -> b -> p)
abstP2 = reifyP (curry abst)
-- abstP2 = reifyP (inline abst2)

abstP3 :: (HasRep p, Rep p ~ ((a,b),c)) => EP (a -> b -> c -> p)
abstP3 = reifyP (\ a b c -> abst ((a,b),c))

abstP4 :: (HasRep p, Rep p ~ ((a,b),(c,d))) => EP (a -> b -> c -> d -> p)
abstP4 = reifyP (\ a b c d -> abst ((a,b),(c,d)))

reifyCon :: HasRep a => a -> EP a
reifyCon q = reifyP (abst (inline repr q))

{--------------------------------------------------------------------
    Tests
--------------------------------------------------------------------}

scrutPair :: Pair Int -> Int
scrutPair p = case scrutinee p of (a :# b) -> a + b

scrutRTreeZ :: RTree Z Int -> Int
scrutRTreeZ t = case scrutinee t of L a -> a

scrutRTreeS :: RTree (S n) Int -> Pair (RTree n Int)
scrutRTreeS t = case scrutinee t of B ts -> ts

conPair :: Int -> EP (Pair Int)
conPair n = reifyP (n :# n)

conRTreeZ :: Int -> EP (RTree Z Int)
conRTreeZ x = reifyP (L x)

conRTreeS :: Pair (RTree n Int) -> EP (RTree (S n) Int)
conRTreeS ts = reifyP (B ts)

-- reifyAbst1 :: EP ((Int,Int) -> Pair Int)
-- reifyAbst1 = reifyP abst

-- reifyAbst :: (Int,Int) -> EP (Pair Int)
-- reifyAbst p = reifyP (abst p)
