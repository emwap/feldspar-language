module Feldspar.Algorithm.FFT.Twids where

import qualified Prelude

import Feldspar
import Feldspar.Vector

twid :: (Type a, Floating a, Prelude.RealFloat a)
     => Data Index -> Data Length -> Data Index -> Data (Complex a)
twid scale n k = share (1 / i2f n) $ \d -> cis (i2f scale * 2 * pi * i2f k * d)

twids :: (Type a, Floating a, Prelude.RealFloat a)
      => Data Length -> Pull1 (Complex a)
twids n = indexed1 (n `div` 2) $ twid (-1) n

itwids :: (Type a, Floating a, Prelude.RealFloat a)
       => Data Length -> Pull1 (Complex a)
itwids n = indexed1 (n `div` 2) $ twid 1 n
