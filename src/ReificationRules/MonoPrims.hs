{-# LANGUAGE FlexibleContexts, TypeOperators #-}
{-# OPTIONS_GHC -Wall #-}

-- {-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP
-- {-# OPTIONS_GHC -fno-warn-unused-binds   #-} -- TEMP

{-# OPTIONS_GHC -fno-warn-missing-signatures #-}

----------------------------------------------------------------------
-- |
-- Module      :  ReificationRules.MonoPrims
-- Copyright   :  (c) 2016 Conal Elliott
-- License     :  BSD3
--
-- Maintainer  :  conal@conal.net
-- Stability   :  experimental
-- 
-- Monomorphic Prim specializations
----------------------------------------------------------------------

module ReificationRules.MonoPrims where

import ReificationRules.Prim (Prim(..),CircuitIf)
import ReificationRules.Misc (Unop,Binop,BinRel,(:*))

-- Synonyms, just because I don't know how to look up constructors successfully.
-- 
-- TODO: Revisit, now that I do know how.

notP  = NotP
andP  = AndP
orP   = OrP

pairP = PairP
exlP  = ExlP
exrP  = ExrP

ifP :: CircuitIf a => Prim (Bool :* (a :* a) -> a)
ifP = IfP

type PowIop a = a -> Int -> a

-- Prim specializations generated by "putStr monoPrimDefs" from Plugin:

bEq     =     EqP :: Prim (BinRel Bool  )
bGe     =     GeP :: Prim (BinRel Bool  )
bGt     =     GtP :: Prim (BinRel Bool  )
bLe     =     LeP :: Prim (BinRel Bool  )
bLt     =     LtP :: Prim (BinRel Bool  )
bNe     =     NeP :: Prim (BinRel Bool  )
dAdd    =    AddP :: Prim (Binop  Double)
dCos    =    CosP :: Prim (Unop   Double)
dDivide = DivideP :: Prim (Binop  Double)
dEq     =     EqP :: Prim (BinRel Double)
dExp    =    ExpP :: Prim (Unop   Double)
dGe     =     GeP :: Prim (BinRel Double)
dGt     =     GtP :: Prim (BinRel Double)
dLe     =     LeP :: Prim (BinRel Double)
dLt     =     LtP :: Prim (BinRel Double)
dMul    =    MulP :: Prim (Binop  Double)
dNe     =     NeP :: Prim (BinRel Double)
dNegate = NegateP :: Prim (Unop   Double)
dPowI   =   PowIP :: Prim (PowIop Double)
dRecip  =  RecipP :: Prim (Unop   Double)
dSin    =    SinP :: Prim (Unop   Double)
dSub    =    SubP :: Prim (Binop  Double)
fAdd    =    AddP :: Prim (Binop  Float )
fCos    =    CosP :: Prim (Unop   Float )
fDivide = DivideP :: Prim (Binop  Float )
fEq     =     EqP :: Prim (BinRel Float )
fExp    =    ExpP :: Prim (Unop   Float )
fGe     =     GeP :: Prim (BinRel Float )
fGt     =     GtP :: Prim (BinRel Float )
fLe     =     LeP :: Prim (BinRel Float )
fLt     =     LtP :: Prim (BinRel Float )
fMul    =    MulP :: Prim (Binop  Float )
fNe     =     NeP :: Prim (BinRel Float )
fNegate = NegateP :: Prim (Unop   Float )
fPowI   =   PowIP :: Prim (PowIop Float )
fRecip  =  RecipP :: Prim (Unop   Float )
fSin    =    SinP :: Prim (Unop   Float )
fSub    =    SubP :: Prim (Binop  Float )
iAdd    =    AddP :: Prim (Binop  Int   )
iEq     =     EqP :: Prim (BinRel Int   )
iGe     =     GeP :: Prim (BinRel Int   )
iGt     =     GtP :: Prim (BinRel Int   )
iLe     =     LeP :: Prim (BinRel Int   )
iLt     =     LtP :: Prim (BinRel Int   )
iMul    =    MulP :: Prim (Binop  Int   )
iNe     =     NeP :: Prim (BinRel Int   )
iNegate = NegateP :: Prim (Unop   Int   )
iPowI   =   PowIP :: Prim (PowIop Int   )
iSub    =    SubP :: Prim (Binop  Int   )
