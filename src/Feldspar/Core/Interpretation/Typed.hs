{-# LANGUAGE CPP #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

-- | Witness 'Type' constraints

module Feldspar.Core.Interpretation.Typed
  ( Typed(..)
  , typeDict
  )
where

import Language.Syntactic
import Language.Syntactic.Constructs.Condition  (Condition)
import Language.Syntactic.Constructs.Decoration (Decor(..))
import Language.Syntactic.Constructs.Identity   (Identity)
import Language.Syntactic.Constructs.Binding    (Variable,Lambda,Let)

import Feldspar.Core.Types (Type)

-- | Class representing a possible dictionary to witness a 'Type'
-- constraint.
class Typed dom
  where
    typeDictSym :: dom a -> Maybe (Dict (Type (DenResult a)))
    {-# INLINABLE typeDictSym #-}
    typeDictSym = const Nothing

instance Typed sub => Typed (sub :|| pred) where
  {-# SPECIALIZE instance (Typed sub) => Typed (sub :|| pred) #-}
  {-# INLINABLE typeDictSym #-}
  typeDictSym (C' s) = typeDictSym s

instance Typed sub => Typed (sub :| pred) where
  {-# SPECIALIZE instance (Typed sub) => Typed (sub :| pred) #-}
  {-# INLINABLE typeDictSym #-}
  typeDictSym (C s) = typeDictSym s

instance Typed (SubConstr2 c sub Type Top) where
  {-# SPECIALIZE instance Typed (SubConstr2 c sub Type Top) #-}
  {-# INLINABLE typeDictSym #-}
  typeDictSym (SubConstr2 _) = Nothing

instance (Typed sub, Typed sup) => Typed (sub :+: sup) where
  {-# SPECIALIZE instance (Typed sub, Typed sup) => Typed (sub :+: sup) #-}
  {-# INLINABLE typeDictSym #-}
  typeDictSym (InjL s) = typeDictSym s
  typeDictSym (InjR s) = typeDictSym s

instance (Typed sub) => Typed (Decor info sub) where
  {-# SPECIALIZE instance (Typed sub) => Typed (Decor info sub) #-}
  {-# INLINABLE typeDictSym #-}
  typeDictSym (Decor _ s) = typeDictSym s

instance Typed Empty
instance Typed Condition
instance Typed Identity
instance Typed Variable
instance Typed Lambda
instance Typed Let

-- | Extract a possible 'Type' constraint witness from an 'AST'
typeDict :: Typed dom => ASTF dom a -> Maybe (Dict (Type a))
typeDict = simpleMatch (const . typeDictSym)
{-# INLINABLE typeDict #-}
