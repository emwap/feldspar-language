{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}

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

module Feldspar.Stream
    (Stream
    ,head
    ,tail
    ,map,mapNth
    ,maps
    ,intersperse
    ,interleave
    ,downsample
    ,duplicate
    ,scan, scan1
    ,mapAccum
    ,iterate
    ,repeat
    ,unfold
    ,drop
    ,zip,zipWith
    ,unzip
    ,take
    ,splitAt
    ,cycle
    ,streamAsVector, streamAsVectorSize
    ,recurrenceO, recurrenceI, recurrenceIO, recurrenceIIO
    ,slidingAvg
    ,iir,fir
    )
    where

import qualified Prelude as P

import Control.Applicative

import Feldspar
import Feldspar.Vector
          (Pull, Pull1, fromZero, toPull, arrToManifest
          ,freezePull1, indexed1, value1, fromList
          ,sum,length,replicate1,scalarProd)
import Feldspar.Vector.Shape (Shape(..),DIM1)

-- | Infinite streams.
data Stream a where
  Stream :: M (M a) -> Stream a
    -- The outer monadic layer is for initialization and the inner layer
    -- for extracting elements.

type instance Elem      (Stream a) = a
type instance CollIndex (Stream a) = Data Index

loop = return

-- | Take the first element of a stream
head :: Syntax a => Stream a -> a
head (Stream init) = runMutable (init >>= id)

-- | Drop the first element of a stream
tail :: Syntax a => Stream a -> Stream a
tail (Stream init) = Stream $ do
    next <- init
    next
    loop next

-- | The stream 'pre v s' first returns 'v' and then behaves like 's'.
pre :: Syntax a => a -> Stream a -> Stream a
pre v (Stream init) = Stream $ do
    next <- init
    r <- newRef v
    loop $ do
      a <- next
      b <- getRef r
      setRef r a
      return b

-- | 'map f str' transforms every element of the stream 'str' using the
--   function 'f'
map :: (a -> b) -> Stream a -> Stream b
map f (Stream init) = Stream $ fmap (fmap f) init

-- | 'mapNth f n k str' transforms every 'n'th element with offset 'k'
--    of the stream 'str' using the function 'f'
mapNth :: (Syntax a) =>
          (a -> a) -> Data Index -> Data Index -> Stream a -> Stream a
mapNth f n k (Stream init) = Stream $ do
    next <- init
    r <- newRef 0
    loop $ do
      a <- next
      i <- getRef r
      setRef r ((i+1) `mod` n)
      return (i==k ? f a $ a)

-- | 'maps fs str' uses one of the functions from 'fs' successively to modify
--   the elements of 'str'
maps :: (Syntax a) =>
        [a -> a] -> Stream a -> Stream a
maps fs (Stream init) = Stream $ do
    next <- init
    r <- newRef (0 :: Data Index)
    loop $ do
      a <- next
      i <- getRef r
      setRef r ((i+1) `mod` P.fromIntegral (P.length fs))
      return $
        (P.foldr (\ (k,f) x ->
                            i==(P.fromIntegral k) ? f a $ x))
         a (P.zip [(1::Index)..] fs)

-- | 'intersperse a str' inserts an 'a' between each element of the stream
--    'str'.
intersperse :: Syntax a => a -> Stream a -> Stream a
intersperse a s = interleave s (repeat a)

-- | Create a new stream by alternating between the elements from
--   the two input streams
interleave :: Syntax a => Stream a -> Stream a -> Stream a
interleave (Stream init1) (Stream init2) = Stream $ do
    next1 <- init1
    next2 <- init2
    r <- newRef true
    loop $ do
      b <- getRef r
      setRef r (not b)
      ifM b next1 next2

-- | 'downsample n str' takes every 'n'th element of the input stream
downsample :: Syntax a => Data Index -> Stream a -> Stream a
downsample n (Stream init) = Stream $ do
    next <- init
    loop $ do
      forM (n-1) (\_ -> next)
      next

-- | 'duplicate n str' stretches the stream by duplicating the elements 'n' times
duplicate :: Syntax a => Data Index -> Stream a -> Stream a
duplicate n (Stream init) = Stream $ do
    next <- init
    a    <- next
    r1   <- newRef a
    r2   <- newRef (1 :: Data Index)
    loop $ do
        i <- getRef r2
        setRef r2 ((i+1)`mod`n)
        ifM (i==0)
          (do a <- next
              setRef r1 a
              return a)
          (getRef r1)

-- | 'scan f a str' produces a stream by successively applying 'f' to
--   each element of the input stream 'str' and the previous element of
--   the output stream.
scan :: Syntax a => (a -> b -> a) -> a -> Stream b -> Stream a
scan f a (Stream init) = Stream $ do
    next <- init
    r <- newRef a
    loop $ do
      x <- next
      acc <- getRef r
      setRef r (f acc x)
      return acc

-- | A scan but without an initial element.
scan1 :: Syntax a => (a -> a -> a) -> Stream a -> Stream a
scan1 f (Stream init) = Stream $ do
    next <- init
    a    <- next
    r    <- newRef a
    loop $ do
      a <- getRef r
      b <- next
      let c = f a b
      setRef r c
      return c

-- | Maps a function over a stream using an accumulator.
mapAccum :: (Syntax acc, Syntax b) =>
            (acc -> a -> (acc,b)) -> acc -> Stream a -> Stream b
mapAccum f acc (Stream init) = Stream $ do
    next <- init
    r <- newRef acc
    loop $ do
      x <- getRef r
      a <- next
      let (acc',b) = f x a
      setRef r acc'
      return b

-- | Iteratively applies a function to a starting element. All the successive
--   results are used to create a stream.
--
-- @iterate f a == [a, f a, f (f a), f (f (f a)) ...]@
iterate :: Syntax a => (a -> a) -> a -> Stream a
iterate f a = Stream $ do
    r <- newRef a
    loop $ do
      x <- getRef r
      setRef r (f x)
      return x

-- | Repeat an element indefinitely.
--
-- @repeat a = [a, a, a, ...]@
repeat :: a -> Stream a
repeat a = Stream $ loop $ return a

-- | @unfold f acc@ creates a new stream by successively applying 'f' to
--   to the accumulator 'acc'.
unfold :: (Syntax a, Syntax c) => (c -> (a,c)) -> c -> Stream a
unfold next init = Stream $ do
    r <- newRef init
    loop $ do
      c <- getRef r
      let (a,c') = next c
      setRef r c'
      return a

-- | Drop a number of elements from the front of a stream
drop :: Syntax a => Data Length -> Stream a -> Stream a
drop i (Stream init) = Stream $ do
    next <- init
    forM i (\_ -> next)
    loop next

-- | Pairs together two streams into one.
zip :: Stream a -> Stream b -> Stream (a,b)
zip = zipWith (,)

-- | Pairs together two streams using a function to combine the
--   corresponding elements.
zipWith :: (a -> b -> c) -> Stream a -> Stream b -> Stream c
zipWith f (Stream init1) (Stream init2) = Stream $ do
    next1 <- init1
    next2 <- init2
    loop $ do
      a <- next1
      b <- next2
      return (f a b)

-- | Given a stream of pairs, split it into two stream.
unzip :: (Syntax a, Syntax b) => Stream (a,b) -> (Stream a, Stream b)
unzip stream = (map fst stream, map snd stream)

app :: Stream (a -> b) -> Stream a -> Stream b
app = zipWith ($)

instance Functor Stream where
  fmap f = map f

instance Applicative Stream where
  pure = repeat
  (<*>) = app

instance Syntax a => Indexed (Stream a) where
  (Stream init) ! n = runMutable $ do
                        next <- init
                        forM (n-1) (\_ -> next)
                        next

instance Num a => Num (Stream a) where
  (+) = liftA2 (+)
  (-) = liftA2 (-)
  (*) = liftA2 (*)
  negate a = fmap negate a
  abs    a = fmap abs    a
  signum a = fmap signum a
  fromInteger a = repeat (fromInteger a)

-- | 'take n str' allocates 'n' elements from the stream 'str' into a
--   core array.
take :: (Syntax a) => Data Length -> Stream a -> Data [Internal a]
take n (Stream init)
    = runMutableArray $ do
        marr <- newArr_ n
        next <- init
        forM n $ \ix -> do
          a <- next
          setArr marr ix (desugar a)
        return marr

-- | 'splitAt n str' allocates 'n' elements from the stream 'str' into a
--   core array and returns the rest of the stream continuing from
--   element 'n+1'.
splitAt :: (Syntax a) =>
           Data Length -> Stream a -> (Data [Internal a], Stream a)
splitAt n stream = (take n stream,drop n stream)

-- | Loops through a vector indefinitely to produce a stream.
cycle :: Syntax a => Pull DIM1 a -> Stream a
cycle vec = Stream $ do
    c <- newRef (0 :: Data Index)
    loop $ do
      i <- getRef c
      setRef c ((i + 1) `rem` length vec)
      return (vec ! (Z :. i))

unsafeVectorToStream :: Syntax a => Pull DIM1 a -> Stream a
unsafeVectorToStream vec = Stream $ do
    r <- newRef 0
    loop $ do
      i <- getRef r
      setRef r (i + 1)
      return (vec ! (Z :. i))

-- | A convenience function for translating an algorithm on streams to an algorithm on vectors.
--   The result vector will have the same length as the input vector.
--   It is important that the stream function doesn't drop any elements of
--   the input stream.
--
--   This function allocates memory for the output vector.
streamAsVector :: (Syntax a, Syntax b) =>
                  (Stream a -> Stream b)
               -> (Pull DIM1 a -> Pull DIM1 b)
streamAsVector f v = toPull $ arrToManifest (fromList [lv], take lv $ f $ unsafeVectorToStream v)
  where lv = length v

-- | Similar to 'streamAsVector' except the size of the output array is computed by the second argument
--   which is given the size of the input vector as a result.
streamAsVectorSize :: (Syntax a, Syntax b) =>
                      (Stream a -> Stream b) -> (Data Length -> Data Length)
                   -> (Pull DIM1 a -> Pull DIM1 b)
streamAsVectorSize f s v = toPull $ arrToManifest (fromList [lv], take lv $ f $ cycle v)
  where lv = s $ length v

-- | A combinator for descibing recurrence equations, or feedback loops.
--   The recurrence equation may refer to previous outputs of the stream,
--   but only as many as the length of the input stream
--   It uses memory proportional to the input vector.
--
-- For exaple one can define the fibonacci sequence as follows:
--
-- > fib = recurrenceO (vector [0,1]) (\fib -> fib!0 + fib!1)
--
-- The expressions @fib!0@ and @fib!1@ refer to previous elements in the
-- stream defined one step back and two steps back respectively.
recurrenceO :: Type a =>
               Pull1 a ->
               (Pull1 a -> Data a) ->
               Stream (Data a)
recurrenceO initV mkExpr = Stream $ do
      buf <- thawArray (freezePull1 initV)
      r   <- newRef (0 :: Data Index)
      loop $ do
        ix <- getRef r
        setRef r (ix + 1)
        a <- withArray buf
             (\ibuf -> return $ mkExpr
                       (indexed1 len (\i -> getIx ibuf ((i + ix) `rem` len))))
        result <- getArr buf (ix `rem` len)
        setArr buf (ix `rem` len) a
        return result
  where
    len  = length initV

-- | A recurrence combinator with input. The function 'recurrenceI' is
--   similar to 'recurrenceO'. The difference is that that it has an input
--   stream, and that the recurrence equation may only refer to previous
--   inputs, it may not refer to previous outputs.
--
-- The sliding average of a stream can easily be implemented using
-- 'recurrenceI'.
--
-- > slidingAvg :: Data WordN -> Stream (Data WordN) -> Stream (Data WordN)
-- > slidingAvg n str = recurrenceI (replicate n 0) str
-- >                    (\input -> sum input `quot` n)
recurrenceI :: (Type a, Type b) =>
               Pull1 a -> Stream (Data a) ->
               (Pull1 a -> Data b) ->
               Stream (Data b)
recurrenceI ii stream mkExpr
    = recurrenceIO ii stream (toPull $ value1 []) (\i _ -> mkExpr i)

-- | 'recurrenceIO' is a combination of 'recurrenceO' and 'recurrenceI'. It
--   has an input stream and the recurrence equation may refer both to
--   previous inputs and outputs.
--
--   'recurrenceIO' is used when defining the 'iir' filter.
recurrenceIO :: (Type a, Type b) =>
                Pull1 a -> Stream (Data a) -> Pull1 b ->
                (Pull1 a -> Pull1 b -> Data b) ->
                Stream (Data b)
recurrenceIO ii (Stream init) io mkExpr = Stream $ do
    ibuf <- thawArray (freezePull1 ii)
    obuf <- thawArray (freezePull1 io)
    next <- init
    r    <- newRef (0 :: Data Index)
    loop $ do
      ix <- getRef r
      setRef r (ix + 1)
      a <- next
      when (lenI /= 0) $ setArr ibuf (ix `rem` lenI) a
      b <- withArray ibuf (\ib ->
             withArray obuf (\ob ->
               return $ mkExpr
                          (indexed1 lenI (\i -> getIx ib ((i + ix) `rem` lenI)))
                          (indexed1 lenO (\i -> getIx ob ((i + ix - 1) `rem` lenO)))
                            ))
      ifM (lenO /= 0)
        (do o <- getArr obuf (ix `rem` lenO)
            setArr obuf (ix `rem` lenO) b
            return o)
        (return b)
  where
    lenI = length ii
    lenO = length io

-- | Similar to 'recurrenceIO' but takes two input streams.
recurrenceIIO :: (Type a, Type b, Type c) =>
                 Pull1 a -> Stream (Data a) -> Pull1 b -> Stream (Data b) ->
                 Pull1 c ->
                 (Pull1 a -> Pull1 b -> Pull1 c -> Data c) ->
                 Stream (Data c)
recurrenceIIO i1 (Stream init1) i2 (Stream init2) io mkExpr = Stream $ do
    ibuf1 <- thawArray (freezePull1 i1)
    next1 <- init1
    ibuf2 <- thawArray (freezePull1 i2)
    next2 <- init2
    obuf  <- thawArray (freezePull1 io)
    c     <- newRef (0 :: Data Index)
    loop $ do
      ix <- getRef c
      setRef c (ix + 1)
      a <- next1
      b <- next2
      when (len1 /= 0) $ setArr ibuf1 (ix `rem` len1) a
      when (len2 /= 0) $ setArr ibuf2 (ix `rem` len2) b
      out <- withArray ibuf1 (\ib1 ->
               withArray ibuf2 (\ib2 ->
                 withArray obuf (\ob ->
                   return $ mkExpr (indexed1 len1 (\i -> getIx ib1 ((i + ix) `rem` len1)))
                                   (indexed1 len2 (\i -> getIx ib2 ((i + ix) `rem` len2)))
                                   (indexed1 lenO (\i -> getIx ob  ((i + ix) `rem` lenO)))
                                )))
      ifM (lenO /= 0)
          (do o <- getArr obuf (ix `rem` lenO)
              setArr obuf (ix `rem` lenO) out
              return o)
          (return out)
  where
    len1 = length i1
    len2 = length i2
    lenO = length io

slidingAvg :: Data WordN -> Stream (Data WordN) -> Stream (Data WordN)
slidingAvg n str = recurrenceI (replicate1 n 0) str
                   (\input -> (fromZero $ sum input) `quot` n)

-- | A fir filter on streams
fir :: Pull1 Float ->
       Stream (Data Float) -> Stream (Data Float)
fir b inp =
    recurrenceI (replicate1 (length b) 0) inp
                (scalarProd b)

-- | An iir filter on streams
iir :: Data Float -> Pull1 Float -> Pull1 Float ->
       Stream (Data Float) -> Stream (Data Float)
iir a0 a b inp =
    recurrenceIO (replicate1 (length b) 0) inp
                 (replicate1 (length a) 0)
      (\i o -> 1 / a0 * ( scalarProd b i
                        - scalarProd a o)
      )

