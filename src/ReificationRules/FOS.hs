{-# LANGUAGE CPP, GADTs, KindSignatures, ExplicitForAll, ConstraintKinds, MagicHash #-}
{-# LANGUAGE TypeOperators #-}
{-# OPTIONS_GHC -Wall #-}

-- #define Testing

-- {-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP
#ifdef Testing
{-# OPTIONS_GHC -fno-warn-unused-binds   #-} -- TEMP
#endif

----------------------------------------------------------------------
-- |
-- Module      :  ReificationRules.FOS
-- Copyright   :  (c) 2016 Conal Elliott
-- License     :  BSD3
--
-- Maintainer  :  conal@conal.net
-- Stability   :  experimental
-- 
-- First-order syntax interface. GHC seems to be shy about applying rules under lambdas.
----------------------------------------------------------------------

-- {-# OPTIONS_GHC -ddump-rules #-}

module ReificationRules.FOS
  ( EP,varP,constP,appP,lamP,letP,letPairP,evalP,reifyP,reify, litE
  , abst,repr,abst',repr', abstP,reprP
  , renameVars
  ) where

-- TODO: explicit exports

import GHC.Types (type (~~))
import GHC.Prim (Addr#)
import GHC.CString (unpackCString#)

#ifdef Testing
import Circat.Misc (Unop,Binop,Ternop)
#endif
import qualified Circat.Rep as Rep
import Circat.Rep (HasRep,Rep)

import ReificationRules.Misc ((:*))
import ReificationRules.Exp
import ReificationRules.Prim

type EP a = E Prim a

type Name# = Addr#

-- varP :: Name -> EP a
-- varP = Var . V

var# :: Name# -> V a
var# addr = V (unpackCString# addr)

varP :: Name# -> EP a
varP addr = Var (var# addr)
{-# NOINLINE varP #-}

constP :: forall a. Prim a -> EP a
constP = ConstE
{-# NOINLINE constP #-}

appP :: forall a b. EP (a -> b) -> EP a -> EP b
appP = (:^)
{-# NOINLINE appP #-}

varPat# :: Name# -> Pat a
varPat# addr = VarPat (var# addr)

lamP :: forall a b. Name# -> EP b -> EP (a -> b)
lamP addr body = Lam (varPat# addr) body
{-# NOINLINE lamP #-}

letP :: forall a b. Name# -> EP a -> EP b -> EP b
letP x a b = Lam (varPat# x) b `appP` a
{-# NOINLINE letP #-}

letPairP :: forall a b c. Name# -> Name# -> EP (a :* b) -> EP c -> EP c
letPairP x y ab c = Lam (varPat# x :$ varPat# y) c `appP` ab
{-# NOINLINE letPairP #-}

reifyP :: forall a. a -> EP a
reifyP a = reifyE a
{-# NOINLINE reifyP #-}

reify :: a -> EP a
reify _ = error "reify: not implemented"
-- reify f = renameVars (reifyP f)
{-# NOINLINE reify #-}

{-# RULES "reify & rename" forall f. reify f = renameVars (reifyP f) #-}

evalP :: forall a. EP a -> a
evalP = evalE
{-# NOINLINE evalP #-}

-- The explicit 'forall's here help with reification.

-- The NOINLINEs are just to reduce noise when examining Core output.
-- Perhaps remove all but reifyP and evalP later.

{--------------------------------------------------------------------
    HasRep
--------------------------------------------------------------------}

-- Synonyms for HasRep methods. Using these names postpones the method selector
-- unfolding built-in rule.

-- abst :: HasRep a => Rep a -> a
-- repr :: HasRep a => a -> Rep a

-- TODO: Try simpler signatures, now that I'm handling casts.

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

{--------------------------------------------------------------------
    Rules
--------------------------------------------------------------------}

litE :: HasLit a => a -> EP a
litE = constP . LitP . toLit

-- TODO: rename to "litP".

#ifdef Testing

{--------------------------------------------------------------------
    Tests
--------------------------------------------------------------------}

-- Needs fixing for FOS

app1 :: p (a -> b) -> E p a -> E p b
app1 p = (ConstE p :^)

app2 :: p (a -> b -> c) -> E p a -> E p b -> E p c
app2 f a b = app1 f a :^ b

twice :: Unop (Unop a)
twice f = f . f

notOf :: Unop (EP Bool)
notOf = app1 NotP

orOf :: Binop (EP Bool)
orOf = app2 OrP

t1 :: EP (Bool -> Bool)
t1 = constP NotP
-- (not,fromList [])

t2 :: EP (Unop Bool)
t2 = lamP "b"# notOf
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
