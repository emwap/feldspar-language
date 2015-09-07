{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Feldspar.Core.Constructs.Switch where

import Language.Syntactic
import Language.Syntactic.Constructs.Binding

import Feldspar.Core.Types
import Feldspar.Core.Interpretation
import Feldspar.Core.Constructs.Eq
import Feldspar.Core.Constructs.Condition

import Data.Typeable

data Switch a
  where
    Switch :: (Type b) => Switch (b :-> Full b)

instance Semantic Switch
  where
    {-# SPECIALIZE instance Semantic Switch #-}
    {-# INLINABLE semantics #-}
    semantics Switch = Sem "switch" id

semanticInstances ''Switch

instance EvalBind Switch where
  {-# SPECIALIZE instance EvalBind Switch #-}

instance AlphaEq dom dom dom env => AlphaEq Switch Switch dom env
  where
    {-# SPECIALIZE instance AlphaEq dom dom dom env =>
          AlphaEq Switch Switch dom env #-}

instance Sharable Switch where {-# SPECIALIZE instance Sharable Switch #-}

instance Cumulative Switch where {-# SPECIALIZE instance Cumulative Switch #-}

instance SizeProp (Switch :|| Type)
  where
    {-# SPECIALIZE instance SizeProp (Switch :|| Type) #-}
    {-# INLINABLE sizeProp #-}
    sizeProp (C' Switch) (WrapFull sz :* Nil) = infoSize sz

instance
    ( (Switch    :|| Type) :<: dom
    , (EQ        :|| Type) :<: dom
    , (Condition :|| Type) :<: dom
    , OptimizeSuper dom
    ) =>
      Optimize (Switch :|| Type) dom
  where
    {-# SPECIALIZE instance ( (Switch    :|| Type) :<: dom
                            , (EQ        :|| Type) :<: dom
                            , (Condition :|| Type) :<: dom
                            , OptimizeSuper dom
                            ) => Optimize (Switch :|| Type) dom #-}
    -- If the arguments still have the shape of a condition tree (right
    -- spine), keep it as a Switch otherwise just return the expressions within
    constructFeatOpt opts sym@(C' Switch) args@((cond :$ (op :$ _ :$ s) :$ _ :$ f ) :* Nil)
        | Just (C' Condition) <- prjF cond
        , Just (C' Equal)     <- prjF op
        , isTree s f
        = constructFeatUnOptDefault opts sym args

    constructFeatOpt _ (C' Switch) (a :* Nil) = return a
    {-# INLINABLE constructFeatOpt #-}

    constructFeatUnOpt opts x@(C' _) = constructFeatUnOptDefault opts x
    {-# INLINABLE constructFeatUnOpt #-}

isTree :: ( (EQ        :|| Type) :<: dom
          , (Condition :|| Type) :<: dom
          , AlphaEq dom dom (Decor Info (dom :|| Typeable)) [(VarId,VarId)]
          )
       => ASTF (Decor Info (dom :|| Typeable)) a -> ASTF (Decor Info (dom :|| Typeable)) b -> Bool
isTree s (cond :$ (op :$ c :$ a) :$ t :$ f)
    | Just (C' Condition) <- prjF cond
    , Just (C' Equal)     <- prjF op
    = alphaEq s a && isTree s f
isTree _ _ = True
