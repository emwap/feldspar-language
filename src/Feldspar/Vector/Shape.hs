{-# LANGUAGE CPP               #-}
{-# LANGUAGE GADTs             #-}
{-# LANGUAGE TypeFamilies      #-}
{-# LANGUAGE TypeOperators     #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ImplicitParams    #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Feldspar.Vector.Shape where

import qualified Prelude as P
#if defined(MIN_VERSION_base) && MIN_VERSION_base(4,7,0)
import GHC.Stack
#endif

import Data.Monoid

import Feldspar
import Feldspar.Core.Frontend.LoopM
import Feldspar.Core.Frontend.Mutable

infixl 3 :.
data Z
data tail :. head

type DIM0 = Z
type DIM1 = DIM0 :. Data Length
type DIM2 = DIM1 :. Data Length
type DIM3 = DIM2 :. Data Length

data Shape sh where
  Z :: Shape Z
  (:.) :: Shape tail -> Data Length -> Shape (tail :. Data Length)

foldShape :: forall sh m. (Monoid m)
          => (Data Length -> m) -> Shape sh -> m
foldShape f = go
  where
    go :: forall sh'. Shape sh' -> m
    go Z         = mempty
    go (sh :. l) = go sh `mappend` f l

-- | The dimensionality of @sh@
dim :: Shape sh -> Int
dim = P.length . toList
{-# INLINABLE dim #-}

-- | The total number of elements in @sh@
size :: Shape sh -> Data Length
size = P.product . toList
{-# INLINABLE size #-}

toIndex :: Shape sh -> Shape sh -> Data Index
toIndex Z Z = 0
toIndex (sh1 :. sh2) (sh1' :. sh2') = sh2' + sh2 * toIndex sh1 sh1'

fromIndex :: Shape sh -> Data Index -> Shape sh
fromIndex Z _ = Z
fromIndex sh@(_sh :. l) ix = fromIndexOne sh ix

fromIndexOne :: Shape (sh :. Data Index) -> Data Index ->
                Shape (sh :. Data Index)
fromIndexOne (Z :. _) ix = Z :. ix
fromIndexOne (ds@(_ :. _) :. d) ix
  = fromIndexOne ds (ix `quot` d) :. (ix `rem` d)

intersectDim :: Shape sh -> Shape sh -> Shape sh
intersectDim Z Z = Z
intersectDim (sh1 :. n1) (sh2 :. n2)
  = intersectDim sh1 sh2 :. min n1 n2

inRange :: Shape sh -> Shape sh -> Shape sh -> Data Bool
inRange Z Z Z    = true
inRange (shL :. l) (shU :. u) (sh :. i)
  = l <= i && i < u && inRange shL shU sh

-- | Walk the shape, performing @k@ at each index
forShape :: Shape sh -> (Shape sh -> M ()) -> M ()
forShape Z k = k Z
forShape (sh :. l) k = forM l (\i -> forShape sh (\sh -> k (sh :. i)))

-- | Unpack the shape to a list with the innermost dimension first
toList :: Shape sh -> [Data Length]
toList Z         = []
toList (sh :. i) = i : toList sh
{-# INLINABLE toList #-}

-- | Deconstruct the shape
uncons :: Shape (sh :. Data Length) -> (Shape sh, Data Length)
uncons (sh :. i) = (sh,i)
{-# INLINABLE uncons #-}

shapeEq :: Shape sh -> Shape sh -> Data Bool
shapeEq Z Z = true
shapeEq (sh1 :. i) (sh2 :. j) = i == j && shapeEq sh1 sh2
{-# INLINABLE shapeEq #-}

class Shapely sh where
  zeroDim   :: Shape sh
  unitDim   :: Shape sh
#if defined(MIN_VERSION_base) && MIN_VERSION_base(4,7,0)
  fakeShape :: (?cs :: CallStack) => Shape sh
#else
  fakeShape :: Shape sh
#endif
  toShape   :: Int -> Data [Length] -> Shape sh

instance Shapely Z where
  {-# SPECIALIZE instance Shapely Z #-}
  {-# INLINABLE zeroDim #-}
  {-# INLINABLE unitDim #-}
  {-# INLINABLE fakeShape #-}
  {-# INLINABLE toShape #-}
  zeroDim   = Z
  unitDim   = Z
  fakeShape = Z
  toShape _ _ = Z

instance Shapely sh => Shapely (sh :. Data Length) where
  {-# SPECIALIZE instance (Shapely sh) => Shapely (sh :. Data Length) #-}
  {-# INLINABLE zeroDim #-}
  {-# INLINABLE unitDim #-}
  {-# INLINABLE fakeShape #-}
  {-# INLINABLE toShape #-}
  zeroDim   = zeroDim   :. 0
  unitDim   = unitDim   :. 1
#if defined(MIN_VERSION_base) && MIN_VERSION_base(4,7,0)
  fakeShape = fakeShape :. P.error ("You shall not inspect the syntax tree!\n" P.++ showCallStack ?cs)
#else
  fakeShape = fakeShape :. P.error ("You shall not inspect the syntax tree!")
#endif
  toShape i arr = toShape (i+1) arr :. (arr ! P.fromIntegral i)

-- | Concatenating shapes.
class ShapeConc sh1 sh2 where
  type ShapeConcT sh1 sh2
  shapeConc  :: Shape sh1 -> Shape sh2 -> Shape (ShapeConcT sh1 sh2)
  splitIndex :: Shape (ShapeConcT sh1 sh2) -> Shape sh1 -> (Shape sh1,Shape sh2)

instance ShapeConc Z sh2 where
  {-# SPECIALIZE instance ShapeConc Z sh2 #-}
  {-# INLINABLE shapeConc #-}
  {-# INLINABLE splitIndex #-}
  type ShapeConcT Z sh2 = sh2
  shapeConc Z sh2 = sh2
  splitIndex sh Z = (Z,sh)

instance ShapeConc sh1 sh2 => ShapeConc (sh1 :. Data Length) sh2 where
  {-# SPECIALIZE instance ShapeConc sh1 sh2 => ShapeConc (sh1 :. Data Length) sh2 #-}
  {-# INLINABLE shapeConc #-}
  {-# INLINABLE splitIndex #-}
  type ShapeConcT (sh1 :. Data Length) sh2 = ShapeConcT sh1 sh2 :. Data Length
  shapeConc (sh1 :. l) sh2 = shapeConc sh1 sh2 :. l
  splitIndex (sh :. i) (sh1 :. _) = (i1 :. i,i2)
    where (i1,i2) = splitIndex sh sh1


-- KFFs extensions

peelLeft :: Shape (sh :. Data Length) -> (Data Length, Shape sh)
peelLeft (Z :. n) = (n, Z)
peelLeft (sh :. n :. n') = (m, sh' :. n')   -- The extra (leftmost and below) ':.' is necessary for type checking the recursive call
  where (m, sh') = peelLeft (sh :. n)

peelLeft2 :: Shape (sh :. Data Length :. Data Length) -> (Data Length, Data Length, Shape sh)
peelLeft2 sh = (m, n, sh'')
  where (m, sh') = peelLeft sh
        (n, sh'') = peelLeft sh'

insLeft :: Data Length -> Shape sh -> Shape (sh :. Data Length)
insLeft m Z = Z :. m
insLeft m (sh :. n) = insLeft m sh :. n
