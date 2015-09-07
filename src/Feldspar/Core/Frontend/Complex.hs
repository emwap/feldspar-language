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

module Feldspar.Core.Frontend.Complex
where

import Data.Complex (Complex)

import Feldspar.Core.Constructs (Data,sugarSymF)
import Feldspar.Core.Constructs.Complex (COMPLEX(..))
import Feldspar.Core.Frontend.Num (Numeric)

complex :: (Numeric a, RealFloat a) => Data a -> Data a -> Data (Complex a)
complex = sugarSymF MkComplex
{-# INLINABLE complex #-}

realPart :: (Numeric a, RealFloat a) => Data (Complex a) -> Data a
realPart = sugarSymF RealPart
{-# INLINABLE realPart #-}

imagPart :: (Numeric a, RealFloat a) => Data (Complex a) -> Data a
imagPart = sugarSymF ImagPart
{-# INLINABLE imagPart #-}

conjugate :: (Numeric a, RealFloat a) => Data (Complex a) -> Data (Complex a)
conjugate = sugarSymF Conjugate
{-# INLINABLE conjugate #-}

mkPolar :: (Numeric a, RealFloat a) => Data a -> Data a -> Data (Complex a)
mkPolar = sugarSymF MkPolar
{-# INLINABLE mkPolar #-}

cis :: (Numeric a, RealFloat a) => Data a -> Data (Complex a)
cis = sugarSymF Cis
{-# INLINABLE cis #-}

magnitude :: (Numeric a, RealFloat a) => Data (Complex a) -> Data a
magnitude = sugarSymF Magnitude
{-# INLINABLE magnitude #-}

phase :: (Numeric a, RealFloat a) => Data (Complex a) -> Data a
phase = sugarSymF Phase
{-# INLINABLE phase #-}

polar :: (Numeric a, RealFloat a) => Data (Complex a) -> (Data a, Data a)
polar c = (magnitude c, phase c)
{-# INLINABLE polar #-}

infixl 6 +.

(+.) :: (Numeric a, RealFloat a) => Data a -> Data a -> Data (Complex a)
(+.) = complex
{-# INLINABLE (+.) #-}

iunit :: (Numeric a, RealFloat a) => Data (Complex a)
iunit = 0 +. 1
{-# INLINABLE iunit #-}
