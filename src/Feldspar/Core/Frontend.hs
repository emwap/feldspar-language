{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ConstraintKinds #-}
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

{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE OverlappingInstances #-}

module Feldspar.Core.Frontend
    ( module Data.Patch
    , Syntactic
    , Internal

    , FeldDomainAll
    , Data
    , Syntax

    , module Frontend

    , reifyFeld
    , showExpr
    , printExpr
    , showAST
    , drawAST
    , showDecor
    , drawDecor
    , eval
    , evalTarget
    , desugar
    , sugar
    , resugar

    -- * QuickCheck
    , (===>)
    , (===)

    -- * Type constraints
    , tData
    , tArr1
    , tArr2
--    , tM

    -- * Functions
    , ilog2
    , nlz
    ) where


import Prelude as P

import Control.Monad.State
import Test.QuickCheck

import Data.Patch
import Data.Typeable

import Language.Syntactic hiding
    (desugar, sugar, resugar, printExpr, showAST, drawAST)
import qualified Language.Syntactic as Syntactic
import qualified Language.Syntactic.Constructs.Decoration as Syntactic
import Language.Syntactic.Constructs.Binding
import Language.Syntactic.Constructs.Binding.HigherOrder
import Language.Syntactic.Sharing.SimpleCodeMotion

import Feldspar.Range
import Feldspar.Core.Types
import Feldspar.Core.Interpretation hiding (showDecor, drawDecor)
import Feldspar.Core.Constructs
import Feldspar.Core.Frontend.Array            as Frontend
--import Feldspar.Core.Frontend.Binding          as Frontend
import Feldspar.Core.Frontend.Bits             as Frontend
import Feldspar.Core.Frontend.Complex          as Frontend
import Feldspar.Core.Frontend.Condition        as Frontend
--import Feldspar.Core.Frontend.ConditionM       as Frontend
import Feldspar.Core.Frontend.Conversion       as Frontend
import Feldspar.Core.Frontend.Eq               as Frontend
import Feldspar.Core.Frontend.Error            as Frontend
import Feldspar.Core.Frontend.FFI              as Frontend
import Feldspar.Core.Frontend.Floating         as Frontend
import Feldspar.Core.Frontend.Fractional       as Frontend
import Feldspar.Core.Frontend.Future           as Frontend
import Feldspar.Core.Frontend.Integral         as Frontend
import Feldspar.Core.Frontend.Literal          as Frontend
import Feldspar.Core.Frontend.Logic            as Frontend
import Feldspar.Core.Frontend.Loop             as Frontend
--import Feldspar.Core.Frontend.Mutable          as Frontend
--import Feldspar.Core.Frontend.MutableArray     as Frontend
--import Feldspar.Core.Frontend.MutableReference as Frontend
--import Feldspar.Core.Frontend.MutableToPure    as Frontend
import Feldspar.Core.Frontend.NoInline         as Frontend
import Feldspar.Core.Frontend.Num              as Frontend
import Feldspar.Core.Frontend.Ord              as Frontend
--import Feldspar.Core.Frontend.Par              as Frontend
import Feldspar.Core.Frontend.Save             as Frontend
import Feldspar.Core.Frontend.Select           as Frontend
import Feldspar.Core.Frontend.SizeProp         as Frontend
import Feldspar.Core.Frontend.SourceInfo       as Frontend
import Feldspar.Core.Frontend.Trace            as Frontend
import Feldspar.Core.Frontend.Tuple            as Frontend

{-
bindDict :: BindDict
    TypeCtx
    (Decor Info (Lambda TypeCtx :+: Variable TypeCtx :+: FeldDomain))
bindDict = BindDict
    { prjVariable = \a -> case a of
        Decor _ (prj -> Just (Variable v)) -> Just v
        _ -> Nothing

    , prjLambda = \a -> case a of
        Decor _ (prj -> Just (Lambda v)) -> Just v
        _ -> Nothing

    , injVariable = injVar
    , injLambda   = injLam
    , injLet      = injLt
    }

injVar :: forall a . Sat a
    => ASTF (Decor Info (Lambda :+: Variable :+: FeldDomain)) a
    -> VarId
    -> (Decor Info (Lambda :+: Variable :+: FeldDomain)) (Full a)
injVar a v
    = Decor (getInfo a) (inj (Variable v))

injLam :: forall a b . (Sat a, Sat b)
    => ASTF (Decor Info (Lambda :+: Variable :+: FeldDomain)) b
    -> VarId
    -> (Decor Info (Lambda :+: Variable :+: FeldDomain)) (b :-> Full (a -> b))
injLam b v
    = Decor
        ((mkInfoTy (FunType typeRep typeRep)) {infoSize = infoSize (getInfo b)})
        (inj (Lambda v))

injLt :: forall a b . (Sat a, Sat b)
    => ASTF (Decor Info (Lambda :+: Variable :+: FeldDomain)) b
    -> (Decor Info (Lambda :+: Variable :+: FeldDomain)) (a :-> (a -> b) :-> Full b)
injLt b
    = Decor (getInfo b) (inj Let)
-}

{-
bindDict :: BindDict ((Lambda :+: Variable :+: FeldDomain) :|| Typeable)
bindDict = BindDict
    { prjVariable = \a -> do
        Variable v <- prj a
        return v
    , prjLambda = \a -> do
        Lambda v <- prj a
        return v
    , injVariable = \ref v -> case exprDict ref of
        Dict -> injC (Variable v)
    , injLambda = \refa refb v -> case (exprDict refa, exprDict refb) of
        (Dict,Dict) -> injC (Lambda v)
    , injLet = \ref -> case exprDict ref of
        Dict -> injC Let  -- TODO Generalize the pattern of `Dict` matching
                          --      followed by `injC`
    }
-}

instance Sharable ((Lambda :+: Variable :+: FeldDomain) :|| Typeable)
    where
      sharable _ = True

type SyntacticFeld a = (Syntactic a FeldDomainAll, Typeable (Internal a))

-- | Reification and optimization of a Feldspar program
reifyFeld :: SyntacticFeld a
    => BitWidth n
    -> a
    -> ASTF (Decor Info FeldDomain) (Internal a)
reifyFeld n = flip evalState 0 .
    (   return
--    <=< codeMotion bindDict sharable
    .   optimize
    .   targetSpecialization n
    <=< reifyM
    .   Syntactic.desugar
    )
  -- Note that it's important to do 'codeMotion' after 'optimize'. There may be
  -- sub-expressions that appear more than once in the original program, but
  -- where 'optimize' removes all but one occurrence. If 'codeMotion' was run
  -- first, these sub-expressions would be let bound, preventing subsequent
  -- optimizations.

instance Optimize Empty dom
  where
    constructFeatUnOpt _ _ = error "can't optimzie Empty"

showExpr :: SyntacticFeld a => a -> String
showExpr = render . reifyFeld N32

printExpr :: SyntacticFeld a => a -> IO ()
printExpr = Syntactic.printExpr . reifyFeld N32

showAST :: SyntacticFeld a => a -> String
showAST = Syntactic.showAST . reifyFeld N32

drawAST :: SyntacticFeld a => a -> IO ()
drawAST = Syntactic.drawAST . reifyFeld N32

-- | Draw a syntax tree decorated with type and size information
showDecor :: SyntacticFeld a => a -> String
showDecor = Syntactic.showDecor . reifyFeld N32

-- | Draw a syntax tree decorated with type and size information
drawDecor :: SyntacticFeld a => a -> IO ()
drawDecor = Syntactic.drawDecor . reifyFeld N32

eval :: SyntacticFeld a => a -> Internal a
eval = evalBind . reifyFeld N32

evalTarget
    :: ( SyntacticFeld a
       , BoundedInt (GenericInt U n)
       , BoundedInt (GenericInt S n)
       )
    => BitWidth n -> a -> Internal a
evalTarget n = evalBind . reifyFeld n
  -- TODO This doesn't work yet, because 'targetSpecialization' is not
  --      implemented

desugar :: Syntax a => a -> Data (Internal a)
desugar = Syntactic.resugar

sugar :: Syntax a => Data (Internal a) -> a
sugar = Syntactic.resugar

resugar :: (Syntax a, Syntax b, Internal a ~ Internal b) => a -> b
resugar = Syntactic.resugar



--------------------------------------------------------------------------------
-- * QuickCheck
--------------------------------------------------------------------------------

instance (Type a, Arbitrary a) => Arbitrary (Data a)
  where
    arbitrary = fmap value arbitrary

instance Testable (Data Bool)
  where
    property = property . eval

(===>) :: Testable prop => Data Bool -> prop -> Property
a ===> b = eval a ==> b


class Equal a
  where
    (===) :: a -> a -> Property

instance (P.Eq a, Show a) => Equal a
  where
    x === y = printTestCase ("Evaluated property: " ++ show x ++ " === " ++ show y)
            $ property (x P.== y)

instance (Show a, Arbitrary a, Equal b) => Equal (a -> b)
  where
    f === g = property (\x -> f x === g x)


--------------------------------------------------------------------------------
-- * Type annotations
--------------------------------------------------------------------------------

tData :: Patch a a -> Patch (Data a) (Data a)
tData _ = id

tArr1 :: Patch a a -> Patch (Data [a]) (Data [a])
tArr1 _ = id

tArr2 :: Patch a a -> Patch (Data [[a]]) (Data [[a]])
tArr2 _ = id

--tM :: Patch a a -> Patch (M a) (M a)
--tM _ = id


--------------------------------------------------------------------------------
-- * Functions
--------------------------------------------------------------------------------

-- | Integer logarithm in base 2
--   Based on an algorithm in Hacker's Delight
ilog2 :: (Bits a) => Data a -> Data Index
ilog2 x = bitSize x - 1 - nlz x

-- | Count leading zeros
--   Based on an algorithm in Hacker's Delight
nlz :: (Bits a) => Data a -> Data Index
nlz x = bitCount $ complement $ foldl go x $ takeWhile (P.< bitSize' x) $ P.map (2 P.^) [(0::Integer)..]
  where
    go b s = b .|. (b .>>. value s)

