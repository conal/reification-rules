{-# LANGUAGE TypeOperators, TypeFamilies, MultiParamTypeClasses, CPP #-}
{-# LANGUAGE ExplicitForAll    #-}
{-# OPTIONS_GHC -Wall #-}

-- {-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP
-- {-# OPTIONS_GHC -fno-warn-unused-binds   #-} -- TEMP

----------------------------------------------------------------------
-- |
-- Module      :  ReificationRules.Misc
-- Copyright   :  (c) 2016 Conal Elliott
-- License     :  BSD3
-- 
-- Maintainer  :  conal@conal.net
-- Stability   :  experimental
-- 
-- Miscellany
----------------------------------------------------------------------

module ReificationRules.Misc
  ( module Circat.Misc
  , BinRel, (-->)
  , Eq1'(..), (===?)
  , PrimBasics(..), Evalable(..)
--   , ifThenElse
  ) where

import Unsafe.Coerce (unsafeCoerce)     -- see below

import Data.Proof.EQ ((:=:)(..))

import Circat.Misc hiding (Evalable(..))

type BinRel a = a -> a -> Bool

-- | Add pre- and post-processing.
-- Used dynamically by recast.
(-->) :: forall a b a' b'. (a' -> a) -> (b -> b') -> ((a -> b) -> (a' -> b'))
(f --> h) g = h . g . f
-- f --> h = \ g x -> h (g (f x))
{-# INLINE (-->) #-}

-- ifThenElse :: Bool -> Binop a
-- ifThenElse i t e = if i then t else e
-- {-# NOINLINE ifThenElse #-}  -- avoid transformation loop

{--------------------------------------------------------------------
    Equality
--------------------------------------------------------------------}

-- TODO: Rename Eq1'

-- | Equality when we don't know that the type parameters match.
class Eq1' f where
  (====) :: f a -> f b -> Bool

-- | Test for equality. If equal, generate a type equality proof. The proof
-- generation is done with @unsafeCoerce@, so it's very important that equal
-- terms really do have the same type.
(===?) :: Eq1' f => f a -> f b -> Maybe (a :=: b)
a ===? b | a ==== b  = unsafeCoerce (Just Refl)
         | otherwise = Nothing

-- TODO: Explore replacing Eq1' by TestEquality from Data.Type.Equality

-- TODO: Maybe eliminate Eq' and ==?. If so, rename (====) and (===?).

{--------------------------------------------------------------------
    
--------------------------------------------------------------------}

class PrimBasics p where
  unitP :: p Unit
  pairP :: p (a :=> b :=> a :* b)

class Evalable p where eval :: p a -> a
