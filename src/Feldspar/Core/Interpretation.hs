{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}
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

-- | Defines different interpretations of Feldspar programs

module Feldspar.Core.Interpretation
    ( module Language.Syntactic.Constructs.Decoration
    , module Feldspar.Core.Interpretation.Typed

    , targetSpecialization
    , Sharable (..)
    , SizeProp (..)
    , sizePropDefault
    , resultType
    , SourceInfo
    , Info (..)
    , mkInfo
    , mkInfoTy
    , infoRange
    , LatticeSize1 (..)
    , viewLiteral
    , literal
    , literalDecor
    , literalDecorSrc
    , constFold
    , SomeInfo (..)
    , SomeType (..)
    , Env (..)
    , FeldOpts (..)
    , Target (..)
    , inTarget
    , defaultFeldOpts
    , localVar
    , localSource
    , Opt
    , Optimize (..)
    , OptimizeSuper
    , constructFeat
    , optimizeM
    , optimize
    , constructFeatUnOptDefaultTyp
    , constructFeatUnOptDefault
    , optimizeFeatDefault
    , prjF
    , c'
    , Cumulative (..)
    , viewCumulativeInc
    , viewCumulativeDec
    ) where



import Control.Applicative ((<$>))
import Control.Exception
import Control.Monad.Reader
import Data.Map as Map
import Data.Typeable (Typeable)
import System.IO.Unsafe

import Language.Syntactic
import Language.Syntactic.Constructs.Decoration
import Language.Syntactic.Constructs.Literal
import Language.Syntactic.Constructs.Binding

import Feldspar.Range (isSingleton, lowerBound)
import Feldspar.Lattice
import Feldspar.Core.Types
import Feldspar.Core.Interpretation.Typed


--------------------------------------------------------------------------------
-- * Target specialization
--------------------------------------------------------------------------------

-- | Specialize the program for a target platform with the given native bit
-- width
targetSpecialization :: BitWidth n -> ASTF dom a -> ASTF dom a
-- TODO targetSpecialization :: BitWidth n -> ASTF dom a -> ASTF dom (TargetType n a)
targetSpecialization = const id
{-# INLINABLE targetSpecialization #-}



--------------------------------------------------------------------------------
-- * Code motion
--------------------------------------------------------------------------------

-- | Indication whether a symbol is sharable or not
class Sharable dom
  where
    sharable :: dom a -> Bool
    sharable = const True
    {-# INLINABLE sharable #-}

    hoistOver :: dom a -> Bool
    hoistOver = const True
    {-# INLINABLE hoistOver #-}


instance (Sharable sub1, Sharable sub2) => Sharable (sub1 :+: sub2)
  where
    {-# SPECIALIZE instance (Sharable sub1, Sharable sub2) => Sharable (sub1 :+: sub2) #-}
    {-# INLINABLE sharable #-}
    sharable (InjL a) = sharable a
    sharable (InjR a) = sharable a

    hoistOver (InjL a) = hoistOver a
    hoistOver (InjR a) = hoistOver a
    {-# INLINABLE hoistOver #-}

instance Sharable sym => Sharable (sym :|| pred)
  where
    {-# SPECIALIZE instance (Sharable sym) => Sharable (sym :|| pred) #-}
    sharable (C' s) = sharable s
    {-# INLINABLE sharable #-}

    hoistOver (C' s) = hoistOver s
    {-# INLINABLE hoistOver #-}

instance Sharable sym => Sharable (SubConstr2 c sym p1 p2)
  where
    {-# SPECIALIZE instance (Sharable sym) => Sharable (SubConstr2 c sym p1 p2) #-}
    sharable (SubConstr2 s) = sharable s
    {-# INLINABLE sharable #-}

    hoistOver (SubConstr2 s) = hoistOver s
    {-# INLINABLE hoistOver #-}

instance Sharable dom => Sharable (Decor Info dom)
  where
    {-# SPECIALIZE instance (Sharable dom) => Sharable (Decor Info dom) #-}
    sharable = sharable . decorExpr
    {-# INLINABLE sharable #-}

    hoistOver = hoistOver . decorExpr
    {-# INLINABLE hoistOver #-}

instance Sharable Empty



--------------------------------------------------------------------------------
-- * Size propagation
--------------------------------------------------------------------------------

-- | Forwards size propagation
class SizeProp feature
  where
    -- | Size propagation for a symbol given a list of argument sizes
    sizeProp :: feature a -> Args (WrapFull Info) a -> Size (DenResult a)
    {-# INLINABLE sizeProp #-}
    default sizeProp :: (Type (DenResult a))
                     => feature a -> Args (WrapFull Info) a -> Size (DenResult a)
    sizeProp = sizePropDefault

-- | Convenient default implementation of 'sizeProp'
sizePropDefault :: (Type (DenResult a))
                => feature a -> Args (WrapFull Info) a -> Size (DenResult a)
sizePropDefault = const (const universal)
{-# INLINABLE sizePropDefault #-}

--------------------------------------------------------------------------------
-- * Optimization and type/size inference
--------------------------------------------------------------------------------

-- | Compute a type representation of a symbol's result type
resultType :: Type (DenResult a) => c a -> TypeRep (DenResult a)
resultType = const typeRep
{-# INLINABLE resultType #-}

data SomeType
  where
    SomeType :: TypeRep a -> SomeType

type VarInfo = Map VarId SomeType

-- | Information about the source code of an expression
type SourceInfo = String

-- | Type and size information of a Feldspar program
data Info a
  where
    Info
      :: (Show (Size a), Lattice (Size a))
      => { infoType   :: TypeRep a
         , infoSize   :: Size a
         , infoVars   :: VarInfo
         , infoSource :: SourceInfo
         }
      -> Info a

instance Show (Info a)
  where
    show i@(Info {}) = show (infoType i) ++ szStr ++ srcStr
      where
        szStr = case show (infoSize i) of
          "AnySize" -> ""
          str       -> " | " ++ str

        srcStr = case infoSource i of
          ""  -> ""
          src -> " | " ++ src

mkInfo :: Type a => Size a -> Info a
mkInfo sz = Info typeRep sz Map.empty ""
{-# INLINABLE mkInfo #-}

mkInfoTy :: (Show (Size a), Lattice (Size a)) => TypeRep a -> Info a
mkInfoTy t = Info t universal Map.empty ""
{-# INLINABLE mkInfoTy #-}

infoRange :: Info a -> RangeSet a
infoRange info = case infoType info of
                   IntType _ _ -> RangeSet $ infoSize info
                   _           -> Universal
{-# INLINABLE infoRange #-}

-- | This class is used to allow constructs to be abstract in the monad. Its
-- purpose is similar to that of 'MonadType'.
class LatticeSize1 m
  where
    mergeSize :: Lattice (Size a) =>
        Info (m a) -> Size (m a) -> Size (m a) -> Size (m a)
  -- TODO Is this class needed? See comment to `MonadType`.

instance LatticeSize1 Mut
  where
    mergeSize = const (\/)

instance LatticeSize1 Elements
  where
    mergeSize = const (\/)

-- | 'Info' with hidden result type
data SomeInfo
  where
    SomeInfo :: Typeable a => Info a -> SomeInfo

data Env = Env
    { varEnv    :: [(VarId, SomeInfo)]
    , sourceEnv :: SourceInfo
    }

-- | Possible compilation targets in a broad sense.
data Target = RegionInf | Wool | CSE | SICS | BA
  deriving Eq

-- | A record with options for explicit passing in rewrite rules.
data FeldOpts = FeldOpts
    { targets    :: [Target]
    }

-- | Default options.
defaultFeldOpts :: FeldOpts
defaultFeldOpts = FeldOpts { targets = [] }

-- | Decide whether a Target is enabled in FeldOpts.
inTarget :: Target -> FeldOpts -> Bool
inTarget t opts = t `elem` (targets opts)
{-# INLINABLE inTarget #-}

-- | Initial environment
initEnv :: Env
initEnv = Env [] ""

-- | Insert a variable into the environment
localVar :: Typeable b => VarId -> Info b -> Opt a -> Opt a
localVar v info = local $ \env -> env {varEnv = (v, SomeInfo info):varEnv env}

-- | Change the 'SourceInfo' environment
localSource :: SourceInfo -> Opt a -> Opt a
localSource src = local $ \env -> env {sourceEnv = src}

-- | It the expression is a literal, its value is returned, otherwise 'Nothing'
viewLiteral :: forall info dom a. ((Literal :|| Type) :<: dom)
            => ASTF (Decor info (dom :|| Typeable)) a -> Maybe a
viewLiteral (prjF -> Just (C' (Literal a))) = Just a
viewLiteral _ = Nothing
{-# INLINABLE viewLiteral #-}

prjF :: Project (sub :|| Type) sup => sup sig -> Maybe ((sub :|| Type) sig)
prjF = prj
{-# INLINABLE prjF #-}

-- | Construct a 'Literal'
literal :: (Type a, (Literal :|| Type) :<: dom) =>
    a -> ASTF (dom :|| Typeable) a
literal a = Sym $ C' $ inj $ c' $ Literal a

-- | Construct a 'Literal' decorated with 'Info'
literalDecorSrc :: (Type a, (Literal :|| Type) :<: dom)
                => SourceInfo -> a -> ASTF (Decor Info (dom :|| Typeable)) a
literalDecorSrc src a = Sym $ Decor (Info typeRep (sizeOf a) Map.empty src)
                            $ C' $ inj $ c' $ Literal a
{-# INLINABLE literalDecorSrc #-}

c' :: (Type (DenResult sig)) => feature sig -> (feature :|| Type) sig
c' = C'
{-# INLINABLE c' #-}

-- | Construct a 'Literal' decorated with 'Info'
literalDecor :: (Type a, (Literal :|| Type) :<: dom)
             => a -> ASTF (Decor Info (dom :|| Typeable)) a
literalDecor = literalDecorSrc ""
{-# INLINABLE literalDecor #-}
  -- Note: This function could get the 'SourceInfo' from the environment and
  -- insert it in the 'infoSource' field. But then it needs to be monadic which
  -- makes optimizations uglier.

-- | Replaces an expression with a literal if the type permits, otherwise
-- returns the expression unchanged.
constFold :: (Typed dom, EvalBind dom, (Literal :|| Type) :<: dom)
    => ASTF (Decor Info (dom :|| Typeable)) a
    -> ASTF (Decor Info (dom :|| Typeable)) a

-- Return expression unchanged if it is a `Literal`
constFold expr
    | Just (C' (Literal _)) <- prjF expr
    = expr
-- Replace with a literal if the range on the expression is a singleton
constFold expr
    | Just Dict <- typeDict expr
    , info      <- getInfo expr
    , RangeSet sz <- infoRange info
    , isSingleton sz
    = Sym $ Decor info $  C' $ inj $ c' $ Literal $ lowerBound sz
-- Replace with a literal if the expression is closed
constFold expr
    | Just Dict <- typeDict expr
    , info      <- getInfo expr
    , Map.null $ infoVars info   -- closed expression
    , Right a   <- evalBindEither expr
    = Sym $ Decor info $ C' $ inj $ c' $ Literal a
constFold expr = expr

-- | Evaluate an AST and catch any exceptions
evalBindEither
  :: (Constrained dom, Sat dom :< Typeable, EvalBind dom) =>
     ASTF dom a -> Either String a
evalBindEither a = unsafePerformIO $ do
    e <- try $ return $! evalBind a
    return $ case e of
        Left msg -> Left (show (msg :: SomeException))
        Right b  -> Right b
{-# NOINLINE evalBindEither #-}

-- | Environment for optimization
type Opt = Reader Env

-- | Basic optimization of a feature
--
-- This optimization is similar to 'Synt.Optimize', but it also performs size
-- inference. Size inference has to be done simultaneously with other
-- optimizations in order to avoid iterating the phases. (Size information may
-- help optimization and optimization may help size inference.)
class Optimize feature dom
  where
    -- | Size Propagation in the presence of variables
    sizePropEnv :: feature a
                -> Args (AST (Decor Info (dom :|| Typeable))) a
                -> Opt (Size (DenResult a))
    {-# INLINABLE sizePropEnv #-}

    default sizePropEnv :: (SizeProp feature)
                        => feature a
                        -> Args (AST (Decor Info (dom :|| Typeable))) a
                        -> Opt (Size (DenResult a))
    sizePropEnv feat args = return $ sizeProp feat $ mapArgs (WrapFull . getInfo) args

    -- | Top-down and bottom-up optimization of a feature
    optimizeFeat
        :: ( Typeable (DenResult a)
           , OptimizeSuper dom
           )
        => FeldOpts -> feature a
        -> Args (AST (dom :|| Typeable)) a
        -> Opt (ASTF (Decor Info (dom :|| Typeable)) (DenResult a))
    optimizeFeat = optimizeFeatDefault
    {-# INLINABLE optimizeFeat #-}

    -- | Optimized construction of an expression from a symbol and its optimized
    -- arguments
    --
    -- Note: This function should normally not be called directly. Instead, use
    -- 'constructFeat' which has more accurate propagation of 'Info'.
    constructFeatOpt
        :: ( Typeable (DenResult a))
        => FeldOpts -> feature a
        -> Args (AST (Decor Info (dom :|| Typeable))) a
        -> Opt (ASTF (Decor Info (dom :|| Typeable)) (DenResult a))
    constructFeatOpt = constructFeatUnOpt
    {-# INLINABLE constructFeatOpt #-}

    -- | Unoptimized construction of an expression from a symbol and its
    -- optimized arguments
    constructFeatUnOpt
        :: ( Typeable (DenResult a))
        => FeldOpts -> feature a
        -> Args (AST (Decor Info (dom :|| Typeable))) a
        -> Opt (ASTF (Decor Info (dom :|| Typeable)) (DenResult a))

    default constructFeatUnOpt
        :: ( Typeable (DenResult a)
           , Type (DenResult a)
           , SizeProp feature
           , feature :<: dom)
        => FeldOpts -> feature a
        -> Args (AST (Decor Info (dom :|| Typeable))) a
        -> Opt (ASTF (Decor Info (dom :|| Typeable)) (DenResult a))
    constructFeatUnOpt = constructFeatUnOptDefault
    {-# INLINABLE constructFeatUnOpt #-}

instance Optimize Empty dom
  where
    constructFeatUnOpt = error "Not implemented: constructFeatUnOpt for Empty"
    sizePropEnv = error "Not implemented: sizePropEnv for Empty"

-- These classes used to be super-classes of `Optimize`, but after switching to
-- GHC 7.4, that lead to looping dictionaries (at run time). The problem arises
-- when you make instances like
--
--     instance Optimize dom dom => Optimize MyConstruct dom
--
-- Since the second parameter does not change, this seems to create a loop
-- whenever you want to access super-class methods through a
-- `Optimize MyConstruct dom` constraint.
--
-- This may or may not be related to the following (unconfirmed) bug:
--
--   http://hackage.haskell.org/trac/ghc/ticket/5913
--
-- To revert the class hierarchy:
--
--   * Make `OptimizeSuper` (expanded) a super-class of `Optimize`
--   * Make `WitnessCons feature` a super-class of `Optimize`
--   * Replace the context of `optimizeFeat` with `Optimize dom dom`
--   * Replace all references to `OptimizeSuper dom` with `Optimize dom dom`
--   * Remove `OptimizeSuper`
class
    ( AlphaEq dom dom (dom :|| Typeable) [(VarId, VarId)]
    , AlphaEq dom dom (Decor Info (dom :|| Typeable)) [(VarId, VarId)]
    , EvalBind dom
    , (Literal :|| Type) :<: dom
    , Typed dom
    , Render dom -- For debug
    , Constrained dom
    , Optimize dom dom
    ) =>
      OptimizeSuper dom

instance
    ( AlphaEq dom dom (dom :|| Typeable) [(VarId, VarId)]
    , AlphaEq dom dom (Decor Info (dom :|| Typeable)) [(VarId, VarId)]
    , EvalBind dom
    , (Literal  :|| Type) :<: dom
    , Typed dom
    , Render dom
    , Constrained dom
    , Optimize dom dom
    ) =>
      OptimizeSuper dom where
        {-# SPECIALIZE instance
             ( AlphaEq dom dom (dom :|| Typeable) [(VarId,VarId)]
             , AlphaEq dom dom (Decor Info (dom :|| Typeable)) [(VarId,VarId)]
             , EvalBind dom
             , (Literal :|| Type) :<: dom
             , Typed dom
             , Render dom
             , Constrained dom
             , Optimize dom dom
             ) => OptimizeSuper dom #-}

-- | Optimized construction of an expression from a symbol and its optimized
-- arguments
constructFeat :: ( Typeable (DenResult a)
                 , Optimize feature dom)
    => FeldOpts -> feature a
    -> Args (AST (Decor Info (dom :|| Typeable))) a
    -> Opt (ASTF (Decor Info (dom :|| Typeable)) (DenResult a))
constructFeat opts a args = do
    sz   <- sizePropEnv a args
    aOpt <- constructFeatOpt opts a args
    return $ updateDecor (\info -> info {infoSize = sz}) aOpt
  -- This function uses `constructFeatOpt` for optimization and
  -- `sizePropEnv` for size propagation. This is because
  -- `constructFeatOpt` may produce less accurate size information than
  -- `sizePropEnv`.

instance
    ( Optimize sub1 dom
    , Optimize sub2 dom
    ) =>
      Optimize (sub1 :+: sub2) dom
  where
    {-# SPECIALIZE instance (Optimize sub1 dom, Optimize sub2 dom) => Optimize (sub1 :+: sub2) dom #-}
    sizePropEnv (InjL a) = sizePropEnv a
    sizePropEnv (InjR a) = sizePropEnv a
    {-# INLINABLE sizePropEnv #-}

    optimizeFeat opts (InjL a) = optimizeFeat opts a
    optimizeFeat opts (InjR a) = optimizeFeat opts a
    {-# INLINABLE optimizeFeat #-}

    constructFeatOpt opts (InjL a) = constructFeatOpt opts a
    constructFeatOpt opts (InjR a) = constructFeatOpt opts a
    {-# INLINABLE constructFeatOpt #-}

    constructFeatUnOpt opts (InjL a) = constructFeatUnOpt opts a
    constructFeatUnOpt opts (InjR a) = constructFeatUnOpt opts a
    {-# INLINABLE constructFeatUnOpt #-}

-- | Optimization of an expression
--
-- In addition to running 'optimizeFeat', this function performs constant
-- folding on all closed expressions, provided that the type permits making a
-- literal.
optimizeM :: (OptimizeSuper dom)
          => FeldOpts -> ASTF (dom :|| Typeable) a -> Opt (ASTF (Decor Info (dom :|| Typeable)) a)
optimizeM opts a
    | Dict <- exprDict a
    = constFold <$> matchTrans (\(C' x) -> optimizeFeat opts x) a
{-# INLINABLE optimizeM #-}

-- | Optimization of an expression. This function runs 'optimizeM' and extracts
-- the result.
optimize :: (OptimizeSuper dom)
         => FeldOpts -> ASTF (dom :|| Typeable) a -> ASTF (Decor Info (dom :|| Typeable)) a
optimize opts = flip runReader initEnv . optimizeM opts
{-# INLINABLE optimize #-}

-- | Convenient default implementation of 'constructFeatUnOpt'. Uses 'sizeProp'
-- to propagate size.
constructFeatUnOptDefaultTyp
    :: ( feature :<: dom
       , SizeProp feature
       , Typeable (DenResult a)
       , Show (Size (DenResult a))
       , Lattice (Size (DenResult a))
       )
    => FeldOpts -> TypeRep (DenResult a)
    -> feature a
    -> Args (AST (Decor Info (dom :|| Typeable))) a
    -> Opt (ASTF (Decor Info (dom :|| Typeable)) (DenResult a))
constructFeatUnOptDefaultTyp _ typ feat args
    = do
        src <- asks sourceEnv
        let sz   = sizeProp feat $ mapArgs (WrapFull . getInfo) args
            vars = Map.unions $ listArgs (infoVars . getInfo) args
        return $ appArgs (Sym $ Decor (Info typ sz vars src) $ C' $ inj feat) args

-- | Like 'constructFeatUnOptDefaultTyp' but without an explicit 'TypeRep'
constructFeatUnOptDefault
    :: ( feature :<: dom
       , SizeProp feature
       , Type (DenResult a)
       )
    => FeldOpts -> feature a
    -> Args (AST (Decor Info (dom :|| Typeable))) a
    -> Opt (ASTF (Decor Info (dom :|| Typeable)) (DenResult a))
constructFeatUnOptDefault = flip constructFeatUnOptDefaultTyp typeRep
{-# INLINABLE constructFeatUnOptDefault #-}

-- | Convenient default implementation of 'optimizeFeat'
optimizeFeatDefault
    :: ( Optimize feature dom
       , Typeable (DenResult a)
       , OptimizeSuper dom
       )
    => FeldOpts -> feature a
    -> Args (AST (dom :|| Typeable)) a
    -> Opt (ASTF (Decor Info (dom :|| Typeable)) (DenResult a))
optimizeFeatDefault opts feat args
    = constructFeat opts feat =<< mapArgsM (optimizeM opts) args
{-# INLINABLE optimizeFeatDefault #-}


-- | The 'Cumulative' class captures the concept of functions that always increase or decrease their
-- arguments (not the same as monotonicity)
class Cumulative feature where
    -- | Return the arguments which the symbol weakly cumulativeInc
    --
    -- prop> forAll a. [a] = cumulativeInc (f a) ==> f a >= a
    --
    cumulativeInc :: feature a
              -> Args (AST (Decor Info (dom :|| Typeable))) a
              -> [ASTF (Decor Info (dom :|| Typeable)) (DenResult a)]
    cumulativeInc = const (const [])
    {-# INLINABLE cumulativeInc #-}

    -- | Return the arguments for which the symbol is monotonic decreasing
    --
    -- prop> forAll a. [a] = cumulativeDec (f a) ==> f a <= a
    --
    cumulativeDec :: feature a
                 -> Args (AST (Decor Info (dom :|| Typeable))) a
                 -> [ASTF (Decor Info (dom :|| Typeable)) (DenResult a)]
    cumulativeDec = const (const [])
    {-# INLINABLE cumulativeDec #-}

instance (Cumulative sub1, Cumulative sub2) => Cumulative (sub1 :+: sub2) where
    {-# SPECIALIZE instance (Cumulative sub1, Cumulative sub2) => Cumulative (sub1 :+: sub2) #-}
    cumulativeInc (InjL a) = cumulativeInc a
    cumulativeInc (InjR a) = cumulativeInc a
    cumulativeDec (InjL a) = cumulativeDec a
    cumulativeDec (InjR a) = cumulativeDec a
    {-# INLINABLE cumulativeInc #-}
    {-# INLINABLE cumulativeDec #-}

instance (Cumulative sym) => Cumulative (sym :|| pred) where
    {-# SPECIALIZE instance (Cumulative sym) => Cumulative (sym :|| pred) #-}
    cumulativeInc (C' s) = cumulativeInc s
    cumulativeDec (C' s) = cumulativeDec s
    {-# INLINABLE cumulativeInc #-}
    {-# INLINABLE cumulativeDec #-}

instance (Cumulative sym) => Cumulative (SubConstr2 c sym p1 p2) where
    {-# SPECIALIZE instance (Cumulative sym) => Cumulative (SubConstr2 c sym p1 p2) #-}
    cumulativeInc (SubConstr2 s) = cumulativeInc s
    cumulativeDec (SubConstr2 s) = cumulativeDec s
    {-# INLINABLE cumulativeInc #-}
    {-# INLINABLE cumulativeDec #-}

instance (Cumulative dom) => Cumulative (Decor Info dom) where
    {-# SPECIALIZE instance (Cumulative dom) => Cumulative (Decor Info dom) #-}
    cumulativeInc = cumulativeInc . decorExpr
    cumulativeDec = cumulativeDec . decorExpr
    {-# INLINABLE cumulativeInc #-}
    {-# INLINABLE cumulativeDec #-}

instance Cumulative Empty

-- | Extract sub-expressions for which the expression is (weak) monotonic
-- increasing
viewCumulativeInc :: (Cumulative dom)
                  => ASTF (Decor Info (dom :|| Typeable)) a
                  -> [ASTF (Decor Info (dom :|| Typeable)) a]
viewCumulativeInc = simpleMatch cumulativeInc
{-# INLINABLE viewCumulativeInc #-}

-- | Extract sub-expressions for which the expression is (weak) monotonic
-- decreasing
viewCumulativeDec :: (Cumulative dom)
                  => ASTF (Decor Info (dom :|| Typeable)) a
                  -> [ASTF (Decor Info (dom :|| Typeable)) a]
viewCumulativeDec = simpleMatch cumulativeDec
{-# INLINABLE viewCumulativeDec #-}
