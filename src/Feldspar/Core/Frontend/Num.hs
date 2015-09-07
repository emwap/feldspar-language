{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleContexts #-}
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

module Feldspar.Core.Frontend.Num where

import Data.Complex
import Data.Int
import Data.Word

import Feldspar.Core.Types
import Feldspar.Core.Constructs
import Feldspar.Core.Constructs.Num
import Feldspar.Core.Frontend.Literal



-- There are three possibilities for making a `Num` instance for `Data`:
--
--   1. instance (Type a, Num a, Num (Size a)) => Num (Data a)
--
--   2. instance Num (Data Word8)
--      instance Num (Data Word16)
--      instance Num (Data Word32)
--      ...
--
--   3. The implementation in this module
--
-- #1 has the problem with #1 that it leaks implementation details.
--
-- #2 has the problem that it is verbose: The methods have to be implemented in each instance
-- (which, of course, can be taken care of using TemplateHaskell).
--
-- #3 avoids the above problems, but does so at the expense of having two numeric classes, which may
-- be confusing to the user.



class (Type a, Num a, Num (Size a)) => Numeric a
  where
    fromIntegerNum :: Integer -> Data a
    fromIntegerNum =  value . fromInteger
    {-# INLINABLE fromIntegerNum #-}
    absNum         :: (Num (Size a)) => Data a -> Data a
    absNum         =  sugarSymF Abs
    {-# INLINABLE absNum #-}
    signumNum      :: Data a -> Data a
    signumNum      =  sugarSymF Sign
    {-# INLINABLE signumNum #-}
    addNum         :: Data a -> Data a -> Data a
    addNum         =  sugarSymF Add
    {-# INLINABLE addNum #-}
    subNum         :: Data a -> Data a -> Data a
    subNum         =  sugarSymF Sub
    {-# INLINABLE subNum #-}
    mulNum         :: Data a -> Data a -> Data a
    mulNum         =  sugarSymF Mul
    {-# INLINABLE mulNum #-}

instance Numeric Word8 where {-# SPECIALIZE instance Numeric Word8 #-}
instance Numeric Word16 where {-# SPECIALIZE instance Numeric Word16 #-}
instance Numeric Word32 where {-# SPECIALIZE instance Numeric Word32 #-}
instance Numeric Word64 where {-# SPECIALIZE instance Numeric Word64 #-}
instance Numeric WordN where {-# SPECIALIZE instance Numeric WordN #-}
instance Numeric Int8 where {-# SPECIALIZE instance Numeric Int8 #-}
instance Numeric Int16 where {-# SPECIALIZE instance Numeric Int16 #-}
instance Numeric Int32 where {-# SPECIALIZE instance Numeric Int32 #-}
instance Numeric Int64 where {-# SPECIALIZE instance Numeric Int64 #-}
instance Numeric IntN where {-# SPECIALIZE instance Numeric IntN #-}

instance Numeric Float where {-# SPECIALIZE instance Numeric Float #-}
instance Numeric Double where {-# SPECIALIZE instance Numeric Double #-}

instance (Type a, RealFloat a) => Numeric (Complex a) where
  {-# SPECIALIZE instance Numeric (Complex Float) #-}
  {-# SPECIALIZE instance Numeric (Complex Double) #-}

instance (Numeric a) => Num (Data a)
  where
    {-# SPECIALIZE instance (Numeric a) => Num (Data a) #-}
    {-# SPECIALIZE instance Num (Data Word8) #-}
    {-# SPECIALIZE instance Num (Data Word16) #-}
    {-# SPECIALIZE instance Num (Data Word32) #-}
    {-# SPECIALIZE instance Num (Data Word64) #-}
    {-# SPECIALIZE instance Num (Data WordN) #-}
    {-# SPECIALIZE instance Num (Data Int8) #-}
    {-# SPECIALIZE instance Num (Data Int16) #-}
    {-# SPECIALIZE instance Num (Data Int32) #-}
    {-# SPECIALIZE instance Num (Data Int64) #-}
    {-# SPECIALIZE instance Num (Data IntN) #-}
    {-# SPECIALIZE instance Num (Data Float) #-}
    {-# SPECIALIZE instance Num (Data Double) #-}
    {-# INLINABLE fromInteger #-}
    {-# INLINABLE abs #-}
    {-# INLINABLE signum #-}
    {-# INLINABLE (+) #-}
    {-# INLINABLE (-) #-}
    {-# INLINABLE (*) #-}
    fromInteger = fromIntegerNum
    abs         = absNum
    signum      = signumNum
    (+)         = addNum
    (-)         = subNum
    (*)         = mulNum
