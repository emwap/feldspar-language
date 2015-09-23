{-# LANGUAGE CPP #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

--
-- Copyright (c) 2009-2011, ERICSSON AB
-- All rights reserved.
--
-- Redistribution and use in source and binary forms, with or without
-- modification, are permitted provided that the following conditions are met:
--
--     * Redistributions of source code must retain the above copyright notice,
--       this list of conditions and the following disclaimer.
--     * Redistributions in binary form must reproduce the above copyright
--       notice, this list of conditions and the following disclaimer in the
--       documentation and/or other materials provided with the distribution.
--     * Neither the name of the ERICSSON AB nor the names of its contributors
--       may be used to endorse or promote products derived from this software
--       without specific prior written permission.
--
-- THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
-- AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
-- IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
-- DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE
-- FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
-- DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
-- SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
-- CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,
-- OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
-- OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
--

-- | Implementation of constructs and operations on 'Bits'
module Feldspar.Core.Constructs.Bits
    ( BITS (..)
    , BitsSuper
    ) where

import Data.Typeable

import Language.Syntactic
import Language.Syntactic.Constructs.Literal
import Language.Syntactic.Constructs.Binding

import Feldspar.Range
import Feldspar.Core.Types
import Feldspar.Core.Interpretation
import Feldspar.Core.Constructs.Logic
import Feldspar.Core.Constructs.Eq
import Feldspar.Core.Constructs.Ord

import Data.Bits.Compat

type BitsSuper a = ( Type a
                   , Bounded a
                   , FiniteBits a
                   , Ord a
                   , Size a ~ Range a
                   )

-- | Bits constructs
data BITS a
  where
    BAnd          :: (BitsSuper a) => BITS (a :-> a :-> Full a)
    BOr           :: (BitsSuper a) => BITS (a :-> a :-> Full a)
    BXor          :: (BitsSuper a) => BITS (a :-> a :-> Full a)
    Complement    :: (BitsSuper a) => BITS (a :->       Full a)

    Bit           :: (BitsSuper a) => BITS (Index :->       Full a)
    SetBit        :: (BitsSuper a) => BITS (a :-> Index :-> Full a)
    ClearBit      :: (BitsSuper a) => BITS (a :-> Index :-> Full a)
    ComplementBit :: (BitsSuper a) => BITS (a :-> Index :-> Full a)
    TestBit       :: (BitsSuper a) => BITS (a :-> Index :-> Full Bool)

    ShiftLU       :: (BitsSuper a) => BITS (a :-> Index :-> Full a)
    ShiftRU       :: (BitsSuper a) => BITS (a :-> Index :-> Full a)
    ShiftL        :: (BitsSuper a) => BITS (a :-> IntN  :-> Full a)
    ShiftR        :: (BitsSuper a) => BITS (a :-> IntN  :-> Full a)
    RotateLU      :: (BitsSuper a) => BITS (a :-> Index :-> Full a)
    RotateRU      :: (BitsSuper a) => BITS (a :-> Index :-> Full a)
    RotateL       :: (BitsSuper a) => BITS (a :-> IntN  :-> Full a)
    RotateR       :: (BitsSuper a) => BITS (a :-> IntN  :-> Full a)
    ReverseBits   :: (BitsSuper a) => BITS (a :->           Full a)

    BitScan       :: (BitsSuper a) => BITS (a :-> Full Index)
    BitCount      :: (BitsSuper a) => BITS (a :-> Full Index)

instance Semantic BITS
  where
    {-# SPECIALIZE instance Semantic BITS #-}
    {-# INLINABLE semantics #-}
    semantics BAnd          = Sem "(.&.)"      (.&.)
    semantics BOr           = Sem "(.|.)"      (.|.)
    semantics BXor          = Sem "xor"        xor
    semantics Complement    = Sem "complement" complement

    semantics Bit           = Sem "bit"           (bit . fromIntegral)
    semantics SetBit        = Sem "setBit"        (liftIntWord setBit)
    semantics ClearBit      = Sem "clearBit"      (liftIntWord clearBit)
    semantics ComplementBit = Sem "complementBit" (liftIntWord complementBit)
    semantics TestBit       = Sem "testBit"       (liftIntWord testBit)

    semantics ShiftLU       = Sem "shiftLU"     (liftIntWord shiftL)
    semantics ShiftRU       = Sem "shiftRU"     (liftIntWord shiftR)
    semantics ShiftL        = Sem "shiftL"      (liftInt shiftL)
    semantics ShiftR        = Sem "shiftR"      (liftInt shiftR)
    semantics RotateLU      = Sem "rotateLU"    (liftIntWord rotateL)
    semantics RotateRU      = Sem "rotateRU"    (liftIntWord rotateR)
    semantics RotateL       = Sem "rotateL"     (liftInt rotateL)
    semantics RotateR       = Sem "rotateR"     (liftInt rotateR)
    semantics ReverseBits   = Sem "reverseBits" evalReverseBits

    semantics BitScan       = Sem "bitScan"  evalBitScan
    semantics BitCount      = Sem "bitCount" (fromIntegral.popCount)

liftIntWord :: (a -> Int -> b) -> a -> WordN -> b
liftIntWord f x = f x . fromIntegral
{-# INLINABLE liftIntWord #-}

liftInt :: (a -> Int -> b) -> a -> IntN -> b
liftInt f x = f x . fromIntegral
{-# INLINABLE liftInt #-}

evalReverseBits :: (FiniteBits b) => b -> b
evalReverseBits b = revLoop b 0 zeroBits
  where
    bSz = finiteBitSize b
    revLoop x i n | i >= bSz    = n
                  | testBit x i = revLoop x (i+1) (setBit n (bSz - i - 1))
                  | otherwise   = revLoop x (i+1) n
{-# INLINABLE evalReverseBits #-}

evalBitScan :: (FiniteBits b) => b -> WordN
evalBitScan b = fromIntegral
              $ if isSigned b
                then countLeadingZeros (complement b) - 1
                else countLeadingZeros b
{-# INLINABLE evalBitScan #-}

semanticInstances ''BITS

instance EvalBind BITS where
  {-# SPECIALIZE instance EvalBind BITS #-}

instance AlphaEq dom dom dom env => AlphaEq BITS BITS dom env
  where
    {-# SPECIALIZE instance AlphaEq dom dom dom env =>
          AlphaEq BITS BITS dom env #-}

instance Sharable BITS where {-# SPECIALIZE instance Sharable BITS #-}

instance Cumulative BITS where
    {-# SPECIALIZE instance Cumulative BITS #-}
    {-# INLINABLE cumulativeDec #-}
    cumulativeDec ShiftRU (a :* b :* Nil)
        | RangeSet r <- infoRange $ getInfo b
        , isNatural r
        = [a]
    cumulativeDec _ _ = []

instance SizeProp (BITS :|| Type)
  where
    {-# SPECIALIZE instance SizeProp (BITS :|| Type) #-}
    {-# INLINABLE sizeProp #-}
    sizeProp (C' BAnd) (WrapFull a :* WrapFull b :* Nil) = rangeAnd (infoSize a) (infoSize b)
    sizeProp (C' BOr)  (WrapFull a :* WrapFull b :* Nil) = rangeOr  (infoSize a) (infoSize b)
    sizeProp (C' BXor) (WrapFull a :* WrapFull b :* Nil) = rangeXor (infoSize a) (infoSize b)

    sizeProp (C' ShiftLU) (WrapFull a :* WrapFull b :* Nil) = rangeShiftLU (infoSize a) (infoSize b)
    sizeProp (C' ShiftRU) (WrapFull a :* WrapFull b :* Nil) = rangeShiftRU (infoSize a) (infoSize b)

    sizeProp (C' Complement) (WrapFull a :* Nil) = rangeComplement (infoSize a)

    sizeProp (C' BitCount) (WrapFull a :* Nil) = rangeBitCount (infoSize a)

    sizeProp a@(C' _) args = sizePropDefault a args


instance ( (BITS  :|| Type) :<: dom
         , (Logic :|| Type) :<: dom
         , (EQ    :|| Type) :<: dom
         , (ORD   :|| Type) :<: dom
         , Cumulative dom
         , OptimizeSuper dom
         )
      => Optimize (BITS :|| Type) dom
  where
    {-# SPECIALIZE instance ( (BITS  :|| Type) :<: dom
                            , (Logic :|| Type) :<: dom
                            , (EQ    :|| Type) :<: dom
                            , (ORD   :|| Type) :<: dom
                            , Cumulative dom
                            , OptimizeSuper dom
                            ) => Optimize (BITS :|| Type) dom #-}
    constructFeatOpt _ (C' BAnd) (a :* b :* Nil)
        | Just zeroBits <- viewLiteral a              = return a
        | Just x <- viewLiteral a, isAllOnes x = return b
        | Just zeroBits <- viewLiteral b              = return b
        | Just x <- viewLiteral b, isAllOnes x = return a

    constructFeatOpt _ (C' BOr) (a :* b :* Nil)
        | Just zeroBits <- viewLiteral a              = return b
        | Just x <- viewLiteral a, isAllOnes x = return a
        | Just zeroBits <- viewLiteral b              = return a
        | Just x <- viewLiteral b, isAllOnes x = return b

    constructFeatOpt opts (C' BXor) (a :* b :* Nil)
        | Just zeroBits <- viewLiteral a              = return b
        | Just x <- viewLiteral a, isAllOnes x = constructFeat opts (c' Complement) (b :* Nil)
        | Just zeroBits <- viewLiteral b              = return a
        | Just x <- viewLiteral b, isAllOnes x = constructFeat opts (c' Complement) (a :* Nil)

    constructFeatOpt _ (C' BXor) ((xo :$ v1 :$ v2) :* v3 :* Nil)
        | Just (C' BXor) <- prjF xo
        , alphaEq v2 v3
        = return v1

    -- complement . complement ==> id
    constructFeatOpt _ (C' Complement) ((cmpl :$ a) :* Nil)
        | Just (C' Complement) <- prjF cmpl
        = return a

    constructFeatOpt opts (C' TestBit) ((xo :$ v1 :$ v2) :* v3 :* Nil)
        | Just (C' BXor) <- prjF xo
        , Just a <- viewLiteral v2
        , Just b <- viewLiteral v3
        , a == bit (fromIntegral b)
        = do tb <- constructFeat opts (c' TestBit) (v1 :* v3 :* Nil)
             constructFeat opts (c' Not) (tb :* Nil)

    -- shiftRU (shiftRU b i) j ==> shiftRU b (i + j)
    constructFeatOpt opts x@(C' ShiftRU) ((op :$ b :$ i) :* j :* Nil)
        | Just (C' ShiftRU) <- prjF op
        , Just i' <- viewLiteral i
        , Just j' <- viewLiteral j
        = constructFeat opts x (b :* literalDecor (i'+j') :* Nil)

    -- shiftLU (shiftLU b i) j ==> shiftLU b (i + j)
    constructFeatOpt opts x@(C' ShiftLU) ((op :$ b :$ i) :* j :* Nil)
        | Just (C' ShiftLU) <- prjF op
        , Just i' <- viewLiteral i
        , Just j' <- viewLiteral j
        = constructFeat opts x (b :* literalDecor (i'+j') :* Nil)

    constructFeatOpt opts x@(C' ShiftLU)  args = optZero opts x args
    constructFeatOpt opts x@(C' ShiftRU)  args = optZero opts x args
    constructFeatOpt opts x@(C' ShiftL)   args = optZero opts x args
    constructFeatOpt opts x@(C' ShiftR)   args = optZero opts x args
    constructFeatOpt opts x@(C' RotateLU) args = optZero opts x args
    constructFeatOpt opts x@(C' RotateRU) args = optZero opts x args
    constructFeatOpt opts x@(C' RotateL)  args = optZero opts x args
    constructFeatOpt opts x@(C' RotateR)  args = optZero opts x args

    constructFeatOpt opts feat args = constructFeatUnOpt opts feat args
    {-# INLINABLE constructFeatOpt #-}

    constructFeatUnOpt opts x@(C' _) = constructFeatUnOptDefault opts x
    {-# INLINABLE constructFeatUnOpt #-}


isAllOnes :: (Bits a) => a -> Bool
isAllOnes x = x Prelude.== complement zeroBits

optZero :: ( Typeable a
           , (Literal :|| Type) :<: dom
           , Optimize feature dom
           )
        => FeldOpts -> feature (a :-> (b :-> Full a))
        -> Args (AST (Decor Info (dom :|| Typeable))) (a :-> (b :-> Full a))
        -> Opt (AST (Decor Info (dom :|| Typeable)) (Full a))
optZero opts f args@(a :* b :* Nil)
    | Just zeroBits <- viewLiteral b = return a
    | otherwise                      = constructFeatUnOpt opts f args
