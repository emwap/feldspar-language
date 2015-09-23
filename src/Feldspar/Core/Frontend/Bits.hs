{-# LANGUAGE CPP #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeSynonymInstances #-}
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

module Feldspar.Core.Frontend.Bits
where

import Prelude hiding (Integral(..))

import Data.Int
import Data.Word

import Feldspar.Core.Types
import Feldspar.Core.Constructs
import Feldspar.Core.Constructs.Bits
import Feldspar.Core.Frontend.Integral
import Feldspar.Core.Frontend.Literal

import qualified Data.Bits as B

infixl 5 .<<.,.>>.
infixl 4 ⊕

class (BitsSuper a) => Bits a
  where
    -- * Logical operations
    (.&.)         :: Data a -> Data a -> Data a
    (.&.)         = sugarSymF BAnd
    {-# INLINABLE (.&.) #-}
    (.|.)         :: Data a -> Data a -> Data a
    (.|.)         = sugarSymF BOr
    {-# INLINABLE (.|.) #-}
    xor           :: Data a -> Data a -> Data a
    xor           = sugarSymF BXor
    {-# INLINABLE xor #-}
    complement    :: Data a -> Data a
    complement    = sugarSymF Complement
    {-# INLINABLE complement #-}

    -- * Bitwise operations
    bit           :: Data Index -> Data a
    bit           = sugarSymF Bit
    {-# INLINABLE bit #-}
    setBit        :: Data a -> Data Index -> Data a
    setBit        = sugarSymF SetBit
    {-# INLINABLE setBit #-}
    clearBit      :: Data a -> Data Index -> Data a
    clearBit      = sugarSymF ClearBit
    {-# INLINABLE clearBit #-}
    complementBit :: Data a -> Data Index -> Data a
    complementBit = sugarSymF ComplementBit
    {-# INLINABLE complementBit #-}
    testBit       :: Data a -> Data Index -> Data Bool
    testBit       = sugarSymF TestBit
    {-# INLINABLE testBit #-}

    -- * Movement operations
    shiftLU       :: Data a -> Data Index -> Data a
    shiftLU       = sugarSymF ShiftLU
    {-# INLINABLE shiftLU #-}
    shiftRU       :: Data a -> Data Index -> Data a
    shiftRU       = sugarSymF ShiftRU
    {-# INLINABLE shiftRU #-}
    shiftL        :: Data a -> Data IntN -> Data a
    shiftL        = sugarSymF ShiftL
    {-# INLINABLE shiftL #-}
    shiftR        :: Data a -> Data IntN -> Data a
    shiftR        = sugarSymF ShiftR
    {-# INLINABLE shiftR #-}
    rotateLU      :: Data a -> Data Index -> Data a
    rotateLU      = sugarSymF RotateLU
    {-# INLINABLE rotateLU #-}
    rotateRU      :: Data a -> Data Index -> Data a
    rotateRU      = sugarSymF RotateRU
    {-# INLINABLE rotateRU #-}
    rotateL       :: Data a -> Data IntN -> Data a
    rotateL       = sugarSymF RotateL
    {-# INLINABLE rotateL #-}
    rotateR       :: Data a -> Data IntN -> Data a
    rotateR       = sugarSymF RotateR
    {-# INLINABLE rotateR #-}
    reverseBits   :: Data a -> Data a
    reverseBits   = sugarSymF ReverseBits
    {-# INLINABLE reverseBits #-}

    -- * Query operations
    bitScan       :: Data a -> Data Index
    bitScan       = sugarSymF BitScan
    {-# INLINABLE bitScan #-}
    bitCount      :: Data a -> Data Index
    bitCount      = sugarSymF BitCount
    {-# INLINABLE bitCount #-}

    bitSize       :: Data a -> Data Index
    bitSize       = value . bitSize'
    {-# INLINABLE bitSize #-}
    bitSize'      :: Data a -> Index
    bitSize'      = const $ fromIntegral $ finiteBitSize (undefined :: a)
    {-# INLINABLE bitSize' #-}

    isSigned      :: Data a -> Data Bool
    isSigned      = value . isSigned'
    {-# INLINABLE isSigned #-}
    isSigned'     :: Data a -> Bool
    isSigned'     = const $ B.isSigned (undefined :: a)
    {-# INLINABLE isSigned' #-}

#if defined(__GLASGOW_HASKELL__) && __GLASGOW_HASKELL__ >= 708
finiteBitSize :: (B.FiniteBits b) => b -> Int
finiteBitSize = B.finiteBitSize
#else
finiteBitSize :: (B.Bits b) => b -> Int
finiteBitSize = B.bitSize
#endif
{-# INLINABLE finiteBitSize #-}

instance Bits Word8  where {-# SPECIALIZE instance Bits Word8 #-}
instance Bits Word16 where {-# SPECIALIZE instance Bits Word16 #-}
instance Bits Word32 where {-# SPECIALIZE instance Bits Word32 #-}
instance Bits Word64 where {-# SPECIALIZE instance Bits Word64 #-}
instance Bits WordN  where {-# SPECIALIZE instance Bits WordN #-}
instance Bits Int8   where {-# SPECIALIZE instance Bits Int8 #-}
instance Bits Int16  where {-# SPECIALIZE instance Bits Int16 #-}
instance Bits Int32  where {-# SPECIALIZE instance Bits Int32 #-}
instance Bits Int64  where {-# SPECIALIZE instance Bits Int64 #-}
instance Bits IntN   where {-# SPECIALIZE instance Bits IntN #-}

-- * Combinators

(⊕)    :: (Bits a) => Data a -> Data a -> Data a
(⊕)    =  xor
{-# INLINABLE (⊕) #-}
(.<<.) :: (Bits a) => Data a -> Data Index -> Data a
(.<<.) =  shiftLU
{-# INLINABLE (.<<.) #-}
(.>>.) :: (Bits a) => Data a -> Data Index -> Data a
(.>>.) =  shiftRU
{-# INLINABLE (.>>.) #-}

-- | Set all bits to one
allOnes :: Bits a => Data a
allOnes = value $ B.complement B.zeroBits
{-# INLINABLE allOnes #-}

-- | Set the `n` lowest bits to one
oneBits :: Bits a => Data Index -> Data a
oneBits n = complement (allOnes .<<. n)
{-# INLINABLE oneBits #-}

-- | Extract the `k` lowest bits
lsbs :: Bits a => Data Index -> Data a -> Data a
lsbs k i = i .&. oneBits k
{-# INLINABLE lsbs #-}
