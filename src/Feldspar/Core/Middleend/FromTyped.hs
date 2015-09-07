{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Feldspar.Core.Middleend.FromTyped
  ( untype
  , untypeType
  )
  where

import Data.Complex
import Data.Typeable (Typeable)

import Language.Syntactic
import Language.Syntactic.Constructs.Binding hiding (Variable, Let)
import Language.Syntactic.Constructs.Binding.HigherOrder hiding (Let)

import Feldspar.Core.Types
import Feldspar.Core.Interpretation hiding (literal, optimize)
import Feldspar.Core.Constructs (FeldDom)
import Feldspar.Core.Constructs.Array
import Feldspar.Core.Constructs.Bits
import Feldspar.Core.Constructs.Literal
import Feldspar.Core.Constructs.Complex
import Feldspar.Core.Constructs.Condition
import Feldspar.Core.Constructs.ConditionM
import Feldspar.Core.Constructs.Conversion
import Feldspar.Core.Constructs.Elements
import Feldspar.Core.Constructs.Error
import Feldspar.Core.Constructs.Eq
import Feldspar.Core.Constructs.Floating
import Feldspar.Core.Constructs.FFI
import Feldspar.Core.Constructs.Fractional
import Feldspar.Core.Constructs.Future
import Feldspar.Core.Constructs.Integral
import Feldspar.Core.Constructs.Loop
import Feldspar.Core.Constructs.Logic
import Feldspar.Core.Constructs.Par
import Feldspar.Core.Constructs.Mutable
import Feldspar.Core.Constructs.MutableArray
import Feldspar.Core.Constructs.MutableReference
import Feldspar.Core.Constructs.MutableToPure
import Feldspar.Core.Constructs.NoInline
import Feldspar.Core.Constructs.Num
import Feldspar.Core.Constructs.Ord
import Feldspar.Core.Constructs.RealFloat
import Feldspar.Core.Constructs.Save
import Feldspar.Core.Constructs.SizeProp
import Feldspar.Core.Constructs.SourceInfo
import Feldspar.Core.Constructs.Switch
import Feldspar.Core.Constructs.Tuple
import qualified Feldspar.Core.Constructs.Binding as Core
import Feldspar.Core.UntypedRepresentation hiding ( Lambda, UntypedFeldF(..)
                                                  , Size, Type(..), Signedness
                                                  , Op(..)
                                                  )
import qualified Feldspar.Core.UntypedRepresentation as Ut
import Feldspar.Core.Middleend.CreateTasks
import Feldspar.Core.Middleend.LetSinking
import Feldspar.Core.Middleend.OptimizeUntyped

-- A self contained translation from the Syntactic format into UntypedFeld.
--
-- The file begins with the necessary Untype-functions and
-- Untype-instances and tucks in some local helper functions at the
-- end. "untype" is the only exported function.

-- | A minimal complete instance has to define either 'untypeProgSym' or
-- 'untypeExprSym'.
class Untype sub dom
  where
    {-# INLINABLE untypeProgSym #-}
    untypeProgSym
        :: sub a
        -> Info (DenResult a)
        -> Args (AST (Decor Info dom)) a
        -> UntypedFeld
    untypeProgSym = untypeProgFresh

instance (Untype sub1 dom, Untype sub2 dom) =>
    Untype (sub1 :+: sub2) dom
  where
    {-# SPECIALIZE instance (Untype sub1 dom, Untype sub2 dom) =>
                       Untype (sub1 :+: sub2) dom #-}
    {-# INLINABLE untypeProgSym #-}
    untypeProgSym (InjL a) = untypeProgSym a
    untypeProgSym (InjR a) = untypeProgSym a

instance Untype FeldDom FeldDom
  where
    {-# SPECIALIZE instance Untype FeldDom FeldDom #-}
    {-# INLINABLE untypeProgSym #-}
    untypeProgSym (C' a) = untypeProgSym a

instance Untype Empty dom
  where
    untypeProgSym _ = error "Can't untype Empty"

untypeProgDecor :: Untype dom dom
    => Decor Info dom a
    -> Args (AST (Decor Info dom)) a
    -> UntypedFeld
untypeProgDecor (Decor info a) = untypeProgSym a info
{-# INLINABLE untypeProgDecor #-}

-- | External module interface.
untype :: Untype dom dom => FeldOpts -> ASTF (Decor Info dom) a -> UntypedFeld
untype opts = createTasks opts . optimize . sinkLets . untypeProg
{-# INLINABLE untype #-}

untypeProg :: Untype dom dom =>
    ASTF (Decor Info dom) a -> UntypedFeld
untypeProg = simpleMatch untypeProgDecor
{-# INLINABLE untypeProg #-}

-- | Implementation of 'untypeProgSym' that generates code into a fresh
-- variable.
untypeProgFresh :: Untype sub dom
    => sub a
    -> Info (DenResult a)
    -> Args (AST (Decor Info dom)) a
    -> UntypedFeld
untypeProgFresh = untypeProgSym
{-# INLINABLE untypeProgFresh #-}

untypeProgSymDefault :: (Untype dom dom)
                     => Ut.Op
                     -> Info (DenResult a)
                     -> Args (AST (Decor Info dom)) a
                     -> UntypedFeld
untypeProgSymDefault sym info = In . Ut.App sym t . listArgs untypeProg
  where
    t = untypeType (infoType info) (infoSize info)
{-# INLINABLE untypeProgSymDefault #-}

instance ( Untype dom dom )
      => Untype (Array :|| Type) dom
  where
    {-# SPECIALIZE instance ( Untype dom dom )
                         => Untype (Array :|| Type) dom #-}
    {-# INLINABLE untypeProgSym #-}
    untypeProgSym (C' Parallel)   = untypeProgSymDefault Ut.Parallel
    untypeProgSym (C' Sequential) = untypeProgSymDefault Ut.Sequential
    untypeProgSym (C' Append)     = untypeProgSymDefault Ut.Append
    untypeProgSym (C' SetIx)      = untypeProgSymDefault Ut.SetIx
    untypeProgSym (C' GetIx)      = untypeProgSymDefault Ut.GetIx
    untypeProgSym (C' SetLength)  = untypeProgSymDefault Ut.SetLength
    untypeProgSym (C' GetLength)  = untypeProgSymDefault Ut.GetLength

instance Untype (Core.Variable :|| Type) dom
  where
    {-# SPECIALIZE instance Untype (Core.Variable :|| Type) dom #-}
    {-# INLINABLE untypeProgSym #-}
    untypeProgSym (C' (Core.Variable v)) info _
        = In (Ut.Variable (Ut.Var (fromIntegral v) t'))
           where t' = untypeType (infoType info) (infoSize info)

instance (Untype dom dom) => Untype (CLambda Type) dom
  where
    {-# SPECIALIZE instance (Untype dom dom) => Untype (CLambda Type) dom #-}
    {-# INLINABLE untypeProgSym #-}
    untypeProgSym (SubConstr2 (Lambda v)) info (body :* Nil)
     = In (Ut.Lambda (Ut.Var (fromIntegral v) t') (untypeProg body))
        where t' = untypeType (argType $ infoType info) (fst $ infoSize info)

instance (Untype dom dom) => Untype Core.Let dom
  where
    {-# SPECIALIZE instance (Untype dom dom) => Untype Core.Let dom #-}
    {-# INLINABLE untypeProgSym #-}
    untypeProgSym Core.Let info (a :* b :* Nil)
        = In (Ut.App Ut.Let t' [untypeProg a, untypeProg b])
          where t' = untypeType (infoType info) (infoSize info)

instance (Untype dom dom) => Untype (Condition :|| Type) dom
  where
    {-# SPECIALIZE instance (Untype dom dom) => Untype (Condition :|| Type) dom #-}
    {-# INLINABLE untypeProgSym #-}
    untypeProgSym (C' Condition) = untypeProgSymDefault Ut.Condition

instance (Untype dom dom) => Untype (ConditionM m) dom
  where
    {-# SPECIALIZE instance (Untype dom dom) => Untype (ConditionM m) dom #-}
    {-# INLINABLE untypeProgSym #-}
    untypeProgSym ConditionM = untypeProgSymDefault Ut.ConditionM

instance (Untype dom dom) => Untype (Error :|| Type) dom
  where
    {-# SPECIALIZE instance (Untype dom dom) => Untype (Error :|| Type) dom #-}
    {-# INLINABLE untypeProgSym #-}
    untypeProgSym (C' Undefined) = untypeProgSymDefault Ut.Undefined
    untypeProgSym (C' (Assert msg)) = untypeProgSymDefault (Ut.Assert msg)

instance (Untype dom dom) => Untype ElementsFeat dom
  where
    {-# SPECIALIZE instance (Untype dom dom) => Untype ElementsFeat dom #-}
    {-# INLINABLE untypeProgSym #-}
    untypeProgSym EMaterialize = untypeProgSymDefault Ut.EMaterialize
    untypeProgSym EWrite = untypeProgSymDefault Ut.EWrite
    untypeProgSym EPar = untypeProgSymDefault Ut.EPar
    untypeProgSym EparFor = untypeProgSymDefault Ut.EparFor
    untypeProgSym ESkip = untypeProgSymDefault Ut.ESkip

instance (Untype dom dom) => Untype (FFI :|| Type) dom
  where
    {-# SPECIALIZE instance (Untype dom dom) => Untype (FFI :|| Type) dom #-}
    {-# INLINABLE untypeProgSym #-}
    -- No use for second argument at this stage.
    untypeProgSym (C' (ForeignImport name _)) = untypeProgSymDefault (Ut.ForeignImport name)

instance Untype dom dom => Untype (FUTURE :|| Type) dom
  where
    {-# SPECIALIZE instance Untype dom dom => Untype (FUTURE :|| Type) dom #-}
    {-# INLINABLE untypeProgSym #-}
    untypeProgSym (C' MkFuture) = untypeProgSymDefault Ut.MkFuture
    untypeProgSym (C' Await) = untypeProgSymDefault Ut.Await

instance Untype (Literal :|| Type) dom
  where
    {-# SPECIALIZE instance Untype (Literal :|| Type) dom #-}
    {-# INLINABLE untypeProgSym #-}
    untypeProgSym (C' (Literal a)) info Nil
      = In (Ut.Literal (literal (infoType info) (infoSize info) a))

instance (Untype dom dom) => Untype (Loop :|| Type) dom
  where
    {-# SPECIALIZE instance (Untype dom dom) => Untype (Loop :|| Type) dom #-}
    {-# INLINABLE untypeProgSym #-}
    untypeProgSym (C' ForLoop) = untypeProgSymDefault Ut.ForLoop
    untypeProgSym (C' WhileLoop) = untypeProgSymDefault Ut.WhileLoop

instance (Untype dom dom) => Untype (LoopM Mut) dom
  where
    {-# SPECIALIZE instance (Untype dom dom) => Untype (LoopM Mut) dom #-}
    {-# INLINABLE untypeProgSym #-}
    untypeProgSym For = untypeProgSymDefault Ut.For
    untypeProgSym While = untypeProgSymDefault Ut.While

instance (Untype dom dom) => Untype MutableToPure dom
  where
    {-# SPECIALIZE instance (Untype dom dom) => Untype MutableToPure dom #-}
    {-# INLINABLE untypeProgSym #-}
    untypeProgSym WithArray = untypeProgSymDefault Ut.WithArray
    untypeProgSym RunMutableArray = untypeProgSymDefault Ut.RunMutableArray

instance (Untype dom dom) => Untype (MONAD Par) dom
  where
    {-# SPECIALIZE instance (Untype dom dom) => Untype (MONAD Par) dom #-}
    {-# INLINABLE untypeProgSym #-}
    untypeProgSym Bind = untypeProgSymDefault Ut.Bind
    untypeProgSym Then = untypeProgSymDefault Ut.Then
    untypeProgSym Return = untypeProgSymDefault Ut.Return
    untypeProgSym When = untypeProgSymDefault Ut.When

instance (Untype dom dom) => Untype (MONAD Mut) dom
  where
    {-# SPECIALIZE instance (Untype dom dom) => Untype (MONAD Mut) dom #-}
    {-# INLINABLE untypeProgSym #-}
    untypeProgSym Bind = untypeProgSymDefault Ut.Bind
    untypeProgSym Then = untypeProgSymDefault Ut.Then
    untypeProgSym Return = untypeProgSymDefault Ut.Return
    untypeProgSym When = untypeProgSymDefault Ut.When

instance (Untype dom dom) => Untype MutableArray dom
  where
    {-# SPECIALIZE instance (Untype dom dom) => Untype MutableArray dom #-}
    {-# INLINABLE untypeProgSym #-}
    untypeProgSym NewArr_ = untypeProgSymDefault Ut.NewArr_
    untypeProgSym NewArr = untypeProgSymDefault Ut.NewArr
    untypeProgSym GetArr = untypeProgSymDefault Ut.GetArr
    untypeProgSym SetArr = untypeProgSymDefault Ut.SetArr
    untypeProgSym ArrLength = untypeProgSymDefault Ut.ArrLength

instance (Untype dom dom) => Untype Mutable dom
  where
    {-# SPECIALIZE instance (Untype dom dom) => Untype Mutable dom #-}
    {-# INLINABLE untypeProgSym #-}
    untypeProgSym Run = untypeProgSymDefault Ut.Run

instance (Untype dom dom) => Untype MutableReference dom
  where
    {-# SPECIALIZE instance (Untype dom dom) => Untype MutableReference dom #-}
    {-# INLINABLE untypeProgSym #-}
    untypeProgSym NewRef = untypeProgSymDefault Ut.NewRef
    untypeProgSym GetRef = untypeProgSymDefault Ut.GetRef
    untypeProgSym SetRef = untypeProgSymDefault Ut.SetRef
    untypeProgSym ModRef = untypeProgSymDefault Ut.ModRef

instance (Untype dom dom) => Untype (NoInline :|| Type) dom
  where
    {-# SPECIALIZE instance (Untype dom dom) => Untype (NoInline :|| Type) dom #-}
    {-# INLINABLE untypeProgSym #-}
    untypeProgSym (C' NoInline) = untypeProgSymDefault Ut.NoInline

instance (Untype dom dom) => Untype ParFeature dom
  where
    {-# SPECIALIZE instance (Untype dom dom) => Untype ParFeature dom #-}
    {-# INLINABLE untypeProgSym #-}
    untypeProgSym ParRun = untypeProgSymDefault Ut.ParRun
    untypeProgSym ParNew = untypeProgSymDefault Ut.ParNew
    untypeProgSym ParGet = untypeProgSymDefault Ut.ParGet
    untypeProgSym ParPut = untypeProgSymDefault Ut.ParPut
    untypeProgSym ParFork = untypeProgSymDefault Ut.ParFork
    untypeProgSym ParYield = untypeProgSymDefault Ut.ParYield

-- | Converts symbols to primitive function calls
instance Untype dom dom => Untype Semantics dom
  where
    {-# SPECIALIZE instance Untype dom dom => Untype Semantics dom #-}
    {-# INLINABLE untypeProgSym #-}
    untypeProgSym (Sem _ _) _ = error "untypesemantics"

-- | Convenient implementation of 'untypeExprSym' for primitive functions
untypePrim :: (Semantic expr, Untype dom dom)
    => (expr :|| Type) a
    -> Info (DenResult a)
    -> Args (AST (Decor Info dom)) a
    -> UntypedFeld
untypePrim (C' s) = untypeProgSym (semantics s)
{-# INLINABLE untypePrim #-}

instance (Untype dom dom) => Untype (BITS :|| Type) dom
  where
    {-# SPECIALIZE instance (Untype dom dom) => Untype (BITS :|| Type) dom #-}
    {-# INLINABLE untypeProgSym #-}
    untypeProgSym (C' BAnd) = untypeProgSymDefault Ut.BAnd
    untypeProgSym (C' BOr) = untypeProgSymDefault Ut.BOr
    untypeProgSym (C' BXor) = untypeProgSymDefault Ut.BXor
    untypeProgSym (C' Complement) = untypeProgSymDefault Ut.Complement
    untypeProgSym (C' Bit) = untypeProgSymDefault Ut.Bit
    untypeProgSym (C' SetBit) = untypeProgSymDefault Ut.SetBit
    untypeProgSym (C' ClearBit) = untypeProgSymDefault Ut.ClearBit
    untypeProgSym (C' ComplementBit) = untypeProgSymDefault Ut.ComplementBit
    untypeProgSym (C' TestBit) = untypeProgSymDefault Ut.TestBit
    untypeProgSym (C' ShiftLU) = untypeProgSymDefault Ut.ShiftLU
    untypeProgSym (C' ShiftRU) = untypeProgSymDefault Ut.ShiftRU
    untypeProgSym (C' ShiftL) = untypeProgSymDefault Ut.ShiftL
    untypeProgSym (C' ShiftR) = untypeProgSymDefault Ut.ShiftR
    untypeProgSym (C' RotateLU) = untypeProgSymDefault Ut.RotateLU
    untypeProgSym (C' RotateRU) = untypeProgSymDefault Ut.RotateRU
    untypeProgSym (C' RotateL) = untypeProgSymDefault Ut.RotateL
    untypeProgSym (C' RotateR) = untypeProgSymDefault Ut.RotateR
    untypeProgSym (C' ReverseBits) = untypeProgSymDefault Ut.ReverseBits
    untypeProgSym (C' BitScan) = untypeProgSymDefault Ut.BitScan
    untypeProgSym (C' BitCount) = untypeProgSymDefault Ut.BitCount

instance (Untype dom dom) => Untype (COMPLEX :|| Type) dom
  where
    {-# SPECIALIZE instance (Untype dom dom) => Untype (COMPLEX :|| Type) dom #-}
    {-# INLINABLE untypeProgSym #-}
    untypeProgSym (C' MkComplex) = untypeProgSymDefault Ut.MkComplex
    untypeProgSym (C' RealPart) = untypeProgSymDefault Ut.RealPart
    untypeProgSym (C' ImagPart) = untypeProgSymDefault Ut.ImagPart
    untypeProgSym (C' MkPolar) = untypeProgSymDefault Ut.MkPolar
    untypeProgSym (C' Conjugate) = untypeProgSymDefault Ut.Conjugate
    untypeProgSym (C' Magnitude) = untypeProgSymDefault Ut.Magnitude
    untypeProgSym (C' Phase) = untypeProgSymDefault Ut.Phase
    untypeProgSym (C' Cis) = untypeProgSymDefault Ut.Cis

instance (Untype dom dom) => Untype (Conversion :|| Type) dom
  where
    {-# SPECIALIZE instance (Untype dom dom) => Untype (Conversion :|| Type) dom #-}
    {-# INLINABLE untypeProgSym #-}
    untypeProgSym (C' F2I) = untypeProgSymDefault Ut.F2I
    untypeProgSym (C' I2N) = untypeProgSymDefault Ut.I2N
    untypeProgSym (C' B2I) = untypeProgSymDefault Ut.B2I
    untypeProgSym (C' Round) = untypeProgSymDefault Ut.Round
    untypeProgSym (C' Ceiling) = untypeProgSymDefault Ut.Ceiling
    untypeProgSym (C' Floor) = untypeProgSymDefault Ut.Floor

instance (Untype dom dom) => Untype (EQ :|| Type) dom
  where
    {-# SPECIALIZE instance (Untype dom dom) => Untype (EQ :|| Type) dom #-}
    {-# INLINABLE untypeProgSym #-}
    untypeProgSym (C' Equal) = untypeProgSymDefault Ut.Equal
    untypeProgSym (C' NotEqual) = untypeProgSymDefault Ut.NotEqual

instance (Untype dom dom) => Untype (FLOATING :|| Type) dom
  where
    {-# SPECIALIZE instance (Untype dom dom) => Untype (FLOATING :|| Type) dom #-}
    {-# INLINABLE untypeProgSym #-}
    untypeProgSym (C' Pi) = untypeProgSymDefault Ut.Pi
    untypeProgSym (C' Feldspar.Core.Constructs.Floating.Exp) = untypeProgSymDefault Ut.Exp
    untypeProgSym (C' Sqrt) = untypeProgSymDefault Ut.Sqrt
    untypeProgSym (C' Log) = untypeProgSymDefault Ut.Log
    untypeProgSym (C' Pow) = untypeProgSymDefault Ut.Pow
    untypeProgSym (C' LogBase) = untypeProgSymDefault Ut.LogBase
    untypeProgSym (C' Sin) = untypeProgSymDefault Ut.Sin
    untypeProgSym (C' Tan) = untypeProgSymDefault Ut.Tan
    untypeProgSym (C' Cos) = untypeProgSymDefault Ut.Cos
    untypeProgSym (C' Asin) = untypeProgSymDefault Ut.Asin
    untypeProgSym (C' Atan) = untypeProgSymDefault Ut.Atan
    untypeProgSym (C' Acos) = untypeProgSymDefault Ut.Acos
    untypeProgSym (C' Sinh) = untypeProgSymDefault Ut.Sinh
    untypeProgSym (C' Tanh) = untypeProgSymDefault Ut.Tanh
    untypeProgSym (C' Cosh) = untypeProgSymDefault Ut.Cosh
    untypeProgSym (C' Asinh) = untypeProgSymDefault Ut.Asinh
    untypeProgSym (C' Atanh) = untypeProgSymDefault Ut.Atanh
    untypeProgSym (C' Acosh) = untypeProgSymDefault Ut.Acosh

instance (Untype dom dom) => Untype (FRACTIONAL :|| Type) dom
  where
    {-# SPECIALIZE instance (Untype dom dom) => Untype (FRACTIONAL :|| Type) dom #-}
    {-# INLINABLE untypeProgSym #-}
    untypeProgSym (C' DivFrac) = untypeProgSymDefault Ut.DivFrac

instance (Untype dom dom) => Untype (INTEGRAL :|| Type) dom
  where
    {-# SPECIALIZE instance (Untype dom dom) => Untype (INTEGRAL :|| Type) dom #-}
    {-# INLINABLE untypeProgSym #-}
    untypeProgSym (C' Quot) = untypeProgSymDefault Ut.Quot
    untypeProgSym (C' Rem) = untypeProgSymDefault Ut.Rem
    untypeProgSym (C' Div) = untypeProgSymDefault Ut.Div
    untypeProgSym (C' Mod) = untypeProgSymDefault Ut.Mod
    untypeProgSym (C' Feldspar.Core.Constructs.Integral.Exp) = untypeProgSymDefault Ut.IExp

instance (Untype dom dom) => Untype (Logic :|| Type) dom
  where
    {-# SPECIALIZE instance (Untype dom dom) => Untype (Logic :|| Type) dom #-}
    {-# INLINABLE untypeProgSym #-}
    untypeProgSym (C' And) = untypeProgSymDefault Ut.And
    untypeProgSym (C' Or) = untypeProgSymDefault Ut.Or
    untypeProgSym (C' Not) = untypeProgSymDefault Ut.Not

instance (Untype dom dom) => Untype (NUM :|| Type) dom
  where
    {-# SPECIALIZE instance (Untype dom dom) => Untype (NUM :|| Type) dom #-}
    {-# INLINABLE untypeProgSym #-}
    untypeProgSym (C' Abs) = untypeProgSymDefault Ut.Abs
    untypeProgSym (C' Sign) = untypeProgSymDefault Ut.Sign
    untypeProgSym (C' Add) = untypeProgSymDefault Ut.Add
    untypeProgSym (C' Sub) = untypeProgSymDefault Ut.Sub
    untypeProgSym (C' Mul) = untypeProgSymDefault Ut.Mul

instance (Untype dom dom) => Untype (ORD :|| Type) dom
  where
    {-# SPECIALIZE instance (Untype dom dom) => Untype (ORD :|| Type) dom #-}
    {-# INLINABLE untypeProgSym #-}
    untypeProgSym (C' LTH) = untypeProgSymDefault Ut.LTH
    untypeProgSym (C' GTH) = untypeProgSymDefault Ut.GTH
    untypeProgSym (C' LTE) = untypeProgSymDefault Ut.LTE
    untypeProgSym (C' GTE) = untypeProgSymDefault Ut.GTE
    untypeProgSym (C' Min) = untypeProgSymDefault Ut.Min
    untypeProgSym (C' Max) = untypeProgSymDefault Ut.Max

instance (Untype dom dom) => Untype (REALFLOAT :|| Type) dom
  where
    {-# SPECIALIZE instance (Untype dom dom) => Untype (REALFLOAT :|| Type) dom #-}
    {-# INLINABLE untypeProgSym #-}
    untypeProgSym (C' Atan2) = untypeProgSymDefault Ut.Atan2

instance (Untype dom dom) => Untype (Save :|| Type) dom
  where
    {-# SPECIALIZE instance (Untype dom dom) => Untype (Save :|| Type) dom #-}
    {-# INLINABLE untypeProgSym #-}
    untypeProgSym (C' Save) _ (a :* Nil) = untypeProg a

instance (Untype dom dom) => Untype (PropSize :|| Type) dom
  where
    {-# SPECIALIZE instance (Untype dom dom) => Untype (PropSize :|| Type) dom #-}
    {-# INLINABLE untypeProgSym #-}
    untypeProgSym (C' (PropSize _)) info (_ :* b :* Nil)
      = In (Ut.App Ut.PropSize t' [untypeProg b])
        where t' = untypeType (infoType info) (infoSize info)

instance (Untype dom dom) => Untype (Decor SourceInfo1 Identity :|| Type) dom
  where
    {-# SPECIALIZE instance (Untype dom dom) => Untype (Decor SourceInfo1 Identity :|| Type) dom #-}
    {-# INLINABLE untypeProgSym #-}
    untypeProgSym (C' (Decor (SourceInfo1 comment) Id)) = untypeProgSymDefault (Ut.SourceInfo comment)

instance (Untype dom dom) => Untype (Switch :|| Type) dom
  where
    {-# SPECIALIZE instance (Untype dom dom) => Untype (Switch :|| Type) dom #-}
    {-# INLINABLE untypeProgSym #-}
    untypeProgSym (C' Switch) = untypeProgSymDefault Ut.Switch

instance (Untype dom dom) => Untype (Tuple :|| Type) dom
  where
    {-# SPECIALIZE instance (Untype dom dom) => Untype (Tuple :|| Type) dom #-}
    {-# INLINABLE untypeProgSym #-}
    untypeProgSym (C' Tup2) = untypeProgSymDefault Ut.Tup2
    untypeProgSym (C' Tup3) = untypeProgSymDefault Ut.Tup3
    untypeProgSym (C' Tup4) = untypeProgSymDefault Ut.Tup4
    untypeProgSym (C' Tup5) = untypeProgSymDefault Ut.Tup5
    untypeProgSym (C' Tup6) = untypeProgSymDefault Ut.Tup6
    untypeProgSym (C' Tup7) = untypeProgSymDefault Ut.Tup7
    untypeProgSym (C' Tup8) = untypeProgSymDefault Ut.Tup8
    untypeProgSym (C' Tup9) = untypeProgSymDefault Ut.Tup9
    untypeProgSym (C' Tup10) = untypeProgSymDefault Ut.Tup10
    untypeProgSym (C' Tup11) = untypeProgSymDefault Ut.Tup11
    untypeProgSym (C' Tup12) = untypeProgSymDefault Ut.Tup12
    untypeProgSym (C' Tup13) = untypeProgSymDefault Ut.Tup13
    untypeProgSym (C' Tup14) = untypeProgSymDefault Ut.Tup14
    untypeProgSym (C' Tup15) = untypeProgSymDefault Ut.Tup15

instance (Untype dom dom) => Untype (Select :|| Type) dom
  where
    {-# SPECIALIZE instance (Untype dom dom) => Untype (Select :|| Type) dom #-}
    {-# INLINABLE untypeProgSym #-}
    untypeProgSym (C' Sel1) = untypeProgSymDefault Ut.Sel1
    untypeProgSym (C' Sel2) = untypeProgSymDefault Ut.Sel2
    untypeProgSym (C' Sel3) = untypeProgSymDefault Ut.Sel3
    untypeProgSym (C' Sel4) = untypeProgSymDefault Ut.Sel4
    untypeProgSym (C' Sel5) = untypeProgSymDefault Ut.Sel5
    untypeProgSym (C' Sel6) = untypeProgSymDefault Ut.Sel6
    untypeProgSym (C' Sel7) = untypeProgSymDefault Ut.Sel7
    untypeProgSym (C' Sel8) = untypeProgSymDefault Ut.Sel8
    untypeProgSym (C' Sel9) = untypeProgSymDefault Ut.Sel9
    untypeProgSym (C' Sel10) = untypeProgSymDefault Ut.Sel10
    untypeProgSym (C' Sel11) = untypeProgSymDefault Ut.Sel11
    untypeProgSym (C' Sel12) = untypeProgSymDefault Ut.Sel12
    untypeProgSym (C' Sel13) = untypeProgSymDefault Ut.Sel13
    untypeProgSym (C' Sel14) = untypeProgSymDefault Ut.Sel14
    untypeProgSym (C' Sel15) = untypeProgSymDefault Ut.Sel15

untypeType :: TypeRep a -> Size a -> Ut.Type
untypeType UnitType _               = Ut.UnitType
untypeType BoolType _               = Ut.BoolType
untypeType (IntType s n) _          = Ut.IntType (convSign s) (convSize n)
untypeType FloatType _              = Ut.FloatType
untypeType DoubleType _             = Ut.DoubleType
untypeType (ComplexType t) _        = Ut.ComplexType (untypeType t (defaultSize t))
untypeType (Tup2Type a b) (sa,sb)
  = Ut.Tup2Type (untypeType a sa) (untypeType b sb)
untypeType (Tup3Type a b c) (sa,sb,sc)
  = Ut.Tup3Type (untypeType a sa) (untypeType b sb) (untypeType c sc)
untypeType (Tup4Type a b c d) (sa,sb,sc,sd)
  = Ut.Tup4Type (untypeType a sa) (untypeType b sb) (untypeType c sc)
                (untypeType d sd)
untypeType (Tup5Type a b c d e) (sa,sb,sc,sd,se)
  = Ut.Tup5Type (untypeType a sa) (untypeType b sb) (untypeType c sc)
                (untypeType d sd) (untypeType e se)
untypeType (Tup6Type a b c d e f) (sa,sb,sc,sd,se,sf)
  = Ut.Tup6Type (untypeType a sa) (untypeType b sb) (untypeType c sc)
                (untypeType d sd) (untypeType e se) (untypeType f sf)
untypeType (Tup7Type a b c d e f g) (sa,sb,sc,sd,se,sf,sg)
  = Ut.Tup7Type (untypeType a sa) (untypeType b sb) (untypeType c sc)
                (untypeType d sd) (untypeType e se) (untypeType f sf)
                (untypeType g sg)
untypeType (Tup8Type a b c d e f g h) (sa,sb,sc,sd,se,sf,sg,sh)
  = Ut.Tup8Type (untypeType a sa) (untypeType b sb) (untypeType c sc)
                (untypeType d sd) (untypeType e se) (untypeType f sf)
                (untypeType g sg) (untypeType h sh)
untypeType (Tup9Type a b c d e f g h i) (sa,sb,sc,sd,se,sf,sg,sh,si)
  = Ut.Tup9Type (untypeType a sa) (untypeType b sb) (untypeType c sc)
                (untypeType d sd) (untypeType e se) (untypeType f sf)
                (untypeType g sg) (untypeType h sh) (untypeType i si)
untypeType (Tup10Type a b c d e f g h i j) (sa,sb,sc,sd,se,sf,sg,sh,si,sj)
  = Ut.Tup10Type (untypeType a sa) (untypeType b sb) (untypeType c sc)
                (untypeType d sd) (untypeType e se) (untypeType f sf)
                (untypeType g sg) (untypeType h sh) (untypeType i si)
                (untypeType j sj)
untypeType (Tup11Type a b c d e f g h i j k) (sa,sb,sc,sd,se,sf,sg,sh,si,sj,sk)
  = Ut.Tup11Type (untypeType a sa) (untypeType b sb) (untypeType c sc)
                (untypeType d sd) (untypeType e se) (untypeType f sf)
                (untypeType g sg) (untypeType h sh) (untypeType i si)
                (untypeType j sj) (untypeType k sk)
untypeType (Tup12Type a b c d e f g h i j k l) (sa,sb,sc,sd,se,sf,sg,sh,si,sj,sk,sl)
  = Ut.Tup12Type (untypeType a sa) (untypeType b sb) (untypeType c sc)
                (untypeType d sd) (untypeType e se) (untypeType f sf)
                (untypeType g sg) (untypeType h sh) (untypeType i si)
                (untypeType j sj) (untypeType k sk) (untypeType l sl)
untypeType (Tup13Type a b c d e f g h i j k l m) (sa,sb,sc,sd,se,sf,sg,sh,si,sj,sk,sl,sm)
  = Ut.Tup13Type (untypeType a sa) (untypeType b sb) (untypeType c sc)
                (untypeType d sd) (untypeType e se) (untypeType f sf)
                (untypeType g sg) (untypeType h sh) (untypeType i si)
                (untypeType j sj) (untypeType k sk) (untypeType l sl)
                (untypeType m sm)
untypeType (Tup14Type a b c d e f g h i j k l m n) (sa,sb,sc,sd,se,sf,sg,sh,si,sj,sk,sl,sm,sn)
  = Ut.Tup14Type (untypeType a sa) (untypeType b sb) (untypeType c sc)
                (untypeType d sd) (untypeType e se) (untypeType f sf)
                (untypeType g sg) (untypeType h sh) (untypeType i si)
                (untypeType j sj) (untypeType k sk) (untypeType l sl)
                (untypeType m sm) (untypeType n sn)
untypeType (Tup15Type a b c d e f g h i j k l m n o) (sa,sb,sc,sd,se,sf,sg,sh,si,sj,sk,sl,sm,sn,so)
  = Ut.Tup15Type (untypeType a sa) (untypeType b sb) (untypeType c sc)
                (untypeType d sd) (untypeType e se) (untypeType f sf)
                (untypeType g sg) (untypeType h sh) (untypeType i si)
                (untypeType j sj) (untypeType k sk) (untypeType l sl)
                (untypeType m sm) (untypeType n sn) (untypeType o so)
untypeType (MutType a) sz           = Ut.MutType (untypeType a sz)
untypeType (RefType a) sz           = Ut.RefType (untypeType a sz)
untypeType (ArrayType a) (rs :> es) = Ut.ArrayType rs (untypeType a es)
untypeType (MArrType a) (rs :> es)  = Ut.MArrType rs (untypeType a es)
untypeType (ParType a) sz           = Ut.ParType (untypeType a sz)
untypeType (ElementsType a) (_ :> es) = Ut.ElementsType (untypeType a es)
untypeType (IVarType a) sz          = Ut.IVarType $ untypeType a sz
untypeType (FunType a b) (sa, sz)   = Ut.FunType (untypeType a sa) (untypeType b sz)
untypeType (FValType a) sz          = Ut.FValType (untypeType a sz)
untypeType _ _                    = error "untypeType: missing "


-- Helper functions.

literal :: TypeRep a -> Size a -> a -> Lit
literal t@UnitType        sz a = literalConst t sz a
literal t@BoolType        sz a = literalConst t sz a
literal t@IntType{}       sz a = literalConst t sz a
literal t@FloatType       sz a = literalConst t sz a
literal t@DoubleType      sz a = literalConst t sz a
literal t@ComplexType{}   sz a = literalConst t sz a
literal t@ArrayType{}     sz a = literalConst t sz a
literal (Tup2Type ta tb) (sa,sb) (a,b)
    = LTup2 (literal ta sa a) (literal tb sb b)

literal (Tup3Type ta tb tc) (sa,sb,sc) (a,b,c)
    = LTup3 (literal ta sa a) (literal tb sb b) (literal tc sc c)

literal (Tup4Type ta tb tc td) (sa,sb,sc,sd) (a,b,c,d)
    = LTup4 (literal ta sa a) (literal tb sb b) (literal tc sc c)
            (literal td sd d)

literal (Tup5Type ta tb tc td te) (sa,sb,sc,sd,se) (a,b,c,d,e)
    = LTup5 (literal ta sa a) (literal tb sb b) (literal tc sc c)
            (literal td sd d) (literal te se e)

literal (Tup6Type ta tb tc td te tf) (sa,sb,sc,sd,se,sf) (a,b,c,d,e,f)
    = LTup6 (literal ta sa a) (literal tb sb b) (literal tc sc c)
            (literal td sd d) (literal te se e) (literal tf sf f)

literal (Tup7Type ta tb tc td te tf tg) (sa,sb,sc,sd,se,sf,sg) (a,b,c,d,e,f,g)
    = LTup7 (literal ta sa a) (literal tb sb b) (literal tc sc c)
            (literal td sd d) (literal te se e) (literal tf sf f)
            (literal tg sg g)
literal _ _ _ = error "Missing pattern: FromTyped.hs: literal"

literalConst :: TypeRep a -> Size a -> a -> Lit
literalConst UnitType        _  ()     = LUnit
literalConst BoolType        _  a      = LBool a
literalConst (IntType s n)   _  a      = LInt (convSign s) (convSize n) (toInteger a)
literalConst FloatType       _  a      = LFloat a
literalConst DoubleType      _  a      = LDouble a
literalConst (ArrayType t)   _  a      = LArray t' $ map (literalConst t (defaultSize t)) a
  where t' = untypeType t (defaultSize t)
literalConst (ComplexType t) _  (r:+i) = LComplex re ie
  where re = literalConst t (defaultSize t) r
        ie = literalConst t (defaultSize t) i

convSign :: Signedness a -> Ut.Signedness
convSign U       = Unsigned
convSign S       = Signed

convSize :: BitWidth a -> Ut.Size
convSize N8      = S8
convSize N16     = S16
convSize N32     = S32
convSize N64     = S64
convSize NNative = S32
