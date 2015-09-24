{-# LANGUAGE CPP #-}
{-# LANGUAGE ConstraintKinds #-}

module Data.Bits.Compat
  ( module Base
#if !MIN_VERSION_base(4,7,0)
  , FiniteBits
  , finiteBitSize
  , zeroBits
#endif
#if !MIN_VERSION_base(4,8,0)
  , countLeadingZeros
#endif
  ) where

import Data.Bits as Base

#if !MIN_VERSION_base(4,7,0)
type FiniteBits b = Bits b

finiteBitSize :: (FiniteBits b) => b -> Int
finiteBitSize = bitSize

zeroBits :: (Bits a) => a
zeroBits = clearBit (bit 0) 0
#endif

#if !MIN_VERSION_base(4,8,0)
countLeadingZeros :: (FiniteBits b) => b -> Int
countLeadingZeros x = (w-1) - go (w-1)
  where
    go i | i < 0       = i -- no bit set
         | testBit x i = i
         | otherwise   = go (i-1)

    w = finiteBitSize x
#endif
