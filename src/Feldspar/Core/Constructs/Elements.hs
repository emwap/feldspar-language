{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Feldspar.Core.Constructs.Elements where

import Language.Syntactic

import Feldspar.Lattice (universal)
import Feldspar.Core.Types
import Feldspar.Core.Interpretation
import Feldspar.Core.Constructs.Binding
import Data.List (genericTake, sortBy)
import Data.Function (on)

data ElementsFeat a
  where
    EMaterialize :: Type a => ElementsFeat (Length :-> Elements a :-> Full [a])
    EWrite       :: Type a => ElementsFeat (Index :-> a :-> Full (Elements a))
    ESkip        :: Type a => ElementsFeat (Full (Elements a))
    EPar         :: Type a => ElementsFeat (Elements a :-> Elements a :-> Full (Elements a))
    EparFor      :: Type a => ElementsFeat (Length :-> (Index -> Elements a) :-> Full (Elements a))

instance Semantic ElementsFeat
  where
    {-# SPECIALIZE instance Semantic ElementsFeat #-}
    {-# INLINABLE semantics #-}
    semantics EMaterialize    = Sem "materialize" ematerialize
    semantics EWrite          = Sem "write" (\ix e -> Elements [(ix, e)])
    semantics ESkip           = Sem "skip" (Elements [])
    semantics EPar            = Sem "par" (\(Elements l) (Elements r) -> Elements (l ++ r))
    semantics EparFor         = Sem "parFor" eparFor

instance Typed ElementsFeat
  where
    {-# SPECIALIZE instance Typed ElementsFeat #-}
    {-# INLINABLE typeDictSym #-}
    typeDictSym = const Nothing

ematerialize :: Length -> Elements a -> [a]
ematerialize l (Elements xs) = map snd xs'
  where xs' = genericTake l $ sortBy (compare `on` fst) xs

eparFor :: Length -> (Index -> Elements a) -> Elements a
eparFor len ixf = Elements $ concatMap (\(Elements vs) -> vs) xs
      where xs = genericTake len $ map ixf [0..]

semanticInstances ''ElementsFeat

instance EvalBind ElementsFeat where
  {-# SPECIALIZE instance EvalBind ElementsFeat #-}

instance AlphaEq dom dom dom env => AlphaEq ElementsFeat ElementsFeat dom env
  where
    {-# SPECIALIZE instance AlphaEq dom dom dom env =>
          AlphaEq ElementsFeat ElementsFeat dom env #-}

instance Sharable ElementsFeat where {-# SPECIALIZE instance Sharable ElementsFeat #-}

instance Cumulative ElementsFeat where {-# SPECIALIZE instance Cumulative ElementsFeat #-}

instance SizeProp ElementsFeat
  where
    {-# SPECIALIZE instance SizeProp ElementsFeat #-}
    {-# INLINABLE sizeProp #-}
    sizeProp EMaterialize (WrapFull len :* WrapFull arr :* Nil) = infoSize arr
    sizeProp EWrite       _                                     = universal
    sizeProp ESkip        _                                     = universal
    sizeProp EPar         (WrapFull p1 :* WrapFull p2 :* Nil)   = universal -- TODO: p1 U p2
    sizeProp EparFor      _                                     = universal

instance ( ElementsFeat :<: dom
         , OptimizeSuper dom
         )
      => Optimize ElementsFeat dom
  where
    {-# SPECIALIZE instance (ElementsFeat :<: dom, OptimizeSuper dom) =>
          Optimize ElementsFeat dom #-}
    {-# INLINABLE constructFeatOpt #-}
    constructFeatOpt _ EPar (a :* b :* Nil)
     | Just ESkip <- prj b = return a
     | Just ESkip <- prj a = return b

    constructFeatOpt opts a args = constructFeatUnOpt opts a args

    {-# INLINABLE constructFeatUnOpt #-}
    constructFeatUnOpt opts EMaterialize = constructFeatUnOptDefaultTyp opts typeRep EMaterialize
    constructFeatUnOpt opts EWrite = constructFeatUnOptDefaultTyp opts typeRep EWrite
    constructFeatUnOpt opts ESkip = constructFeatUnOptDefaultTyp opts typeRep ESkip
    constructFeatUnOpt opts EPar = constructFeatUnOptDefaultTyp opts typeRep EPar
    constructFeatUnOpt opts EparFor = constructFeatUnOptDefaultTyp opts typeRep EparFor
