{-# LANGUAGE CPP            #-}
{-# LANGUAGE GADTs          #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PatternGuards  #-}
{-# LANGUAGE TypeOperators  #-}

{-# OPTIONS_GHC -Wall #-}

{-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP
-- {-# OPTIONS_GHC -fno-warn-unused-binds   #-} -- TEMP

----------------------------------------------------------------------
-- |
-- Module      :  ReificationRules.Exp
-- Copyright   :  (c) 2016 Conal Elliott
-- License     :  BSD3
--
-- Maintainer  :  conal@conal.net
-- Stability   :  experimental
-- 
-- Lambda expressions
----------------------------------------------------------------------

-- Whether to sugar during show, including 'let'
#define Sugared

module ReificationRules.Exp where

import Data.Functor.Classes

import ReificationRules.Misc (Unit,(:*),Eq1'(..))
import ReificationRules.ShowUtils

-- | Variable names
type Name = String

-- | Typed variable. Phantom
data V a = V Name

instance Show (V a) where
  showsPrec _ (V n) = showString n

varName :: V a -> Name
varName (V name) = name

instance Eq1' V where
  V a ==== V b = a == b

infixr 1 :$
infixr 8 :@

-- | Binding patterns
data Pat :: * -> * where
  UnitPat :: Pat Unit
  VarPat  :: V a -> Pat a
  (:$)    :: Pat a -> Pat b -> Pat (a :* b)
  (:@)    :: Pat a -> Pat a -> Pat a

-- NOTE: ":@" is named to suggest "as patterns", but is more general ("and patterns").

-- TODO: Rename UnitPat and VarPat to PUnit and PVar

instance Show (Pat a) where
  showsPrec _ UnitPat     = showString "()"
  showsPrec p (VarPat v)  = showsPrec p v
  showsPrec p (a :$ b)    = showsPair p a b
  showsPrec p (a :@ b)    = showsOp2 False "@" (8,AssocRight) p a b

infixl 9 :^
-- | Lambda expressions
data E :: (* -> *) -> (* -> *) where
  Var     :: V a -> E p a
  ConstE  :: p a -> E p a
  (:^)    :: E p (a -> b) -> E p a -> E p b
  Lam     :: Pat a -> E p b -> E p (a -> b)

instance (HasOpInfo prim, Show' prim) => Show (E prim a) where
#ifdef Sugared
--   showsPrec p (Either (Lam q a) (Lam r b) :^ ab) =
--     showParen (p > 0) $
--     showString "case " . showsPrec 0 ab . showString " of { "
--                        . showsPrec 0 q . showString " -> " . showsPrec 0 a . showString " ; "
--                        . showsPrec 0 r . showString " -> " . showsPrec 0 b . showString " } "
  showsPrec p (Lam q body :^ rhs) =  -- beta redex as "let"
    showParen (p > 0) $
    showString "let " . showsPrec 0 q . showString " = " . showsPrec 0 rhs
    . showString " in " . showsPrec 0 body
--   showsPrec p (ConstE ((==== pairP) -> True) :^ u :^ v)
--                           = showsPair p u v
#endif
  showsPrec p (ConstE prim :^ u :^ v) | Just (OpInfo op fixity) <- opInfo prim =
    showsOp2 False op fixity p u v
  showsPrec _ (Var (V n)) = showString n
  showsPrec p (ConstE c)  = showsPrec' p c
  showsPrec p (u :^ v)      = showsApp p u v
  showsPrec p (Lam q e)     =
    showParen (p > 0) $
    showString "\\ " . showsPrec 0 q . showString " -> " . showsPrec 0 e
--   showsPrec p (Either f g) = showsOp2' "|||" (2,AssocRight) p f g
--   showsPrec p (Loop h) = showsApp1 "loop" p h
--   showsPrec p (CoerceE e)  = showsApp1 "coerce" p e

-- TODO: Multi-line pretty printer with indentation

{--------------------------------------------------------------------
    Special expressions
--------------------------------------------------------------------}

reifyE :: a -> E p a
reifyE _ = error "reifyE: Oops -- not eliminated."
{-# NOINLINE reifyE #-}  -- to give reify/eval rules a chance

evalE :: E p a -> a
evalE _ = error "evalE: not implemented"
{-# NOINLINE evalE #-}  -- to give reify/eval rules a chance

-- TODO: Fill in evalE from LambdaCCC.Lambda if useful or fun.


