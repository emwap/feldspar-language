{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Feldspar.Core.Constructs.RealFloat
    ( REALFLOAT (..)
    ) where

import Language.Syntactic
import Language.Syntactic.Constructs.Binding

import Feldspar.Core.Types
import Feldspar.Core.Interpretation

data REALFLOAT a
  where
    Atan2   :: (Type a, RealFloat a) => REALFLOAT (a :-> a :-> Full a)

instance Semantic REALFLOAT
  where
    {-# SPECIALIZE instance Semantic REALFLOAT #-}
    {-# INLINABLE semantics #-}
    semantics Atan2   = Sem "atan2" Prelude.atan2

semanticInstances ''REALFLOAT

instance EvalBind REALFLOAT where
  {-# SPECIALIZE instance EvalBind REALFLOAT #-}

instance AlphaEq dom dom dom env => AlphaEq REALFLOAT REALFLOAT dom env
  where
    {-# SPECIALIZE instance AlphaEq dom dom dom env =>
          AlphaEq REALFLOAT REALFLOAT dom env #-}

instance Sharable REALFLOAT where {-# SPECIALIZE instance Sharable REALFLOAT #-}

instance Cumulative REALFLOAT where {-# SPECIALIZE instance Cumulative REALFLOAT #-}

instance Typed REALFLOAT

instance SizeProp (REALFLOAT :|| Type)
  where
    {-# SPECIALIZE instance SizeProp (REALFLOAT :|| Type) #-}
    {-# INLINABLE sizeProp #-}
    sizeProp (C' s) = sizePropDefault s

instance ( (REALFLOAT :|| Type) :<: dom
         , OptimizeSuper dom)
      => Optimize (REALFLOAT :|| Type) dom
  where
    {-# SPECIALIZE instance ( (REALFLOAT :|| Type) :<: dom
                            , OptimizeSuper dom)
                         => Optimize (REALFLOAT :|| Type) dom #-}
    {-# INLINABLE constructFeatUnOpt #-}
    constructFeatUnOpt opts a@(C' _) = constructFeatUnOptDefault opts a
