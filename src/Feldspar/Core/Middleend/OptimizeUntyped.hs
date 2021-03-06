module Feldspar.Core.Middleend.OptimizeUntyped ( optimize ) where

import Feldspar.Core.UntypedRepresentation

-- | General simplification. Could in theory be done at earlier stages.
optimize :: UntypedFeld -> UntypedFeld
optimize = go . go

go :: UntypedFeld -> UntypedFeld
go e@(In Variable{}) = e
go (In (Lambda v e)) = In (Lambda v (go e))
go (In (LetFun (s, f, e1) e2)) = In (LetFun (s, f, go e1) (go e2))
go l@(In Literal{}) = l

go (In (App Let _ [e1, In (Lambda x body)]))
 | (In Variable{}) <- e1 -- let x = y in e ==> [y/x]e
 = go $ subst e1 x body
 | linear x body
 = go $ subst e1 x body

go (In (App Mul _ [e1, e2]))
 | (In (Literal (LInt _ _ 0))) <- e1 = e1
 | (In (Literal (LInt _ _ 0))) <- e2 = e2
 | (In (Literal (LInt _ _ 1))) <- e1 = go e2
 | (In (Literal (LInt _ _ 1))) <- e2 = go e1

go (In (App Add _ [e1, e2]))
 | (In (Literal (LInt _ _ 0))) <- e1 = go e2
 | (In (Literal (LInt _ _ 0))) <- e2 = go e1

-- Basic constant folder.
go e@(In (App p _ [In (Literal l1), In (Literal l2)]))
  | p `elem` [Add, Sub, Mul]
  = constFold e p l1 l2

-- For 1 (\v -> body) ==> [0/v]body
go (In (App p _ [In (Literal (LInt s sz 1)), In (Lambda v body)]))
  | p `elem` [For, EparFor]
  = go $ subst (In (Literal (LInt s sz 0))) v body

-- Create a 1 element long array (frequent with MultiDim) and immediately select that
-- element. Can e seen in the metrics test in feldspar-compiler.
-- (RunMutableArray (Bind (NewArr_ 1)
--                        (\v3 -> Then (SetArr v3 0 e3) (Return v3)))) ! 0
go (In (App GetIx _ [arr, In (Literal (LInt _ _ 0))]))
 | (In (App RunMutableArray _ [In (App Bind _ [In (App NewArr_ _ [l]), e'])])) <- arr
 , (In (Literal (LInt _ _ 1))) <- l
 , (In (Lambda v1 (In (App Then _  [sarr, ret])))) <- e'
 , (In (App SetArr _ [In (Variable v3), In (Literal (LInt _ _ 0)), e3])) <- sarr
 , (In (App Return _ [In (Variable v2)])) <- ret
 , v1 == v2
 , v1 == v3 = go e3

-- Same rule as previous rule but with Elements as backing write.
go (In (App GetIx _ [arr, In (Literal (LInt _ _ n))]))
 | In (App EMaterialize _ [In Literal{}, e@(In (App EPar _ _))]) <- arr
 , Just e3 <- grabWrite n e = go e3

-- Tuple selections, 1..15. Deliberately avoiding take 1 . drop k which will
-- result in funny things with broken input.
go (In (App Sel1 _ [In (App p _ (e:_))]))
  | p `elem` [Tup2, Tup3, Tup4, Tup5, Tup6, Tup7, Tup8, Tup9, Tup10
             , Tup11, Tup12, Tup13, Tup14, Tup15]
  = go e
go (In (App Sel2 _ [In (App p _ (_:e:_))]))
  | p `elem` [Tup2, Tup3, Tup4, Tup5, Tup6, Tup7, Tup8, Tup9, Tup10
             , Tup11, Tup12, Tup13, Tup14, Tup15]
  = go e
go (In (App Sel3 _ [In (App p _ (_:_:e:_))]))
  | p `elem` [Tup2, Tup3, Tup4, Tup5, Tup6, Tup7, Tup8, Tup9, Tup10
             , Tup11, Tup12, Tup13, Tup14, Tup15]
  = go e
go (In (App Sel4 _ [In (App p _ (_:_:_:e:_))]))
  | p `elem` [Tup2, Tup3, Tup4, Tup5, Tup6, Tup7, Tup8, Tup9, Tup10
             , Tup11, Tup12, Tup13, Tup14, Tup15]
  = go e
go (In (App Sel5 _ [In (App p _ (_:_:_:_:e:_))]))
  | p `elem` [Tup2, Tup3, Tup4, Tup5, Tup6, Tup7, Tup8, Tup9, Tup10
             , Tup11, Tup12, Tup13, Tup14, Tup15]
  = go e
go (In (App Sel6 _ [In (App p _ (_:_:_:_:_:e:_))]))
  | p `elem` [Tup2, Tup3, Tup4, Tup5, Tup6, Tup7, Tup8, Tup9, Tup10
             , Tup11, Tup12, Tup13, Tup14, Tup15]
  = go e
go (In (App Sel7 _ [In (App p _ (_:_:_:_:_:_:e:_))]))
  | p `elem` [Tup2, Tup3, Tup4, Tup5, Tup6, Tup7, Tup8, Tup9, Tup10
             , Tup11, Tup12, Tup13, Tup14, Tup15]
  = go e
go (In (App Sel8 _ [In (App p _ (_:_:_:_:_:_:_:e:_))]))
  | p `elem` [Tup2, Tup3, Tup4, Tup5, Tup6, Tup7, Tup8, Tup9, Tup10
             , Tup11, Tup12, Tup13, Tup14, Tup15]
  = go e
go (In (App Sel9 _ [In (App p _ (_:_:_:_:_:_:_:_:e:_))]))
  | p `elem` [Tup2, Tup3, Tup4, Tup5, Tup6, Tup7, Tup8, Tup9, Tup10
             , Tup11, Tup12, Tup13, Tup14, Tup15]
  = go e
go (In (App Sel10 _ [In (App p _ (_:_:_:_:_:_:_:_:_:e:_))]))
  | p `elem` [Tup2, Tup3, Tup4, Tup5, Tup6, Tup7, Tup8, Tup9, Tup10
             , Tup11, Tup12, Tup13, Tup14, Tup15]
  = go e
go (In (App Sel11 _ [In (App p _ (_:_:_:_:_:_:_:_:_:_:e:_))]))
  | p `elem` [Tup2, Tup3, Tup4, Tup5, Tup6, Tup7, Tup8, Tup9, Tup10
             , Tup11, Tup12, Tup13, Tup14, Tup15]
  = go e
go (In (App Sel12 _ [In (App p _ (_:_:_:_:_:_:_:_:_:_:_:e:_))]))
  | p `elem` [Tup2, Tup3, Tup4, Tup5, Tup6, Tup7, Tup8, Tup9, Tup10
             , Tup11, Tup12, Tup13, Tup14, Tup15]
  = go e
go (In (App Sel13 _ [In (App p _ (_:_:_:_:_:_:_:_:_:_:_:_:e:_))]))
  | p `elem` [Tup2, Tup3, Tup4, Tup5, Tup6, Tup7, Tup8, Tup9, Tup10
             , Tup11, Tup12, Tup13, Tup14, Tup15]
  = go e
go (In (App Sel14 _ [In (App p _ (_:_:_:_:_:_:_:_:_:_:_:_:_:e:_))]))
  | p `elem` [Tup2, Tup3, Tup4, Tup5, Tup6, Tup7, Tup8, Tup9, Tup10
             , Tup11, Tup12, Tup13, Tup14, Tup15]
  = go e
go (In (App Sel15 _ [In (App p _ (_:_:_:_:_:_:_:_:_:_:_:_:_:_:e:_))]))
  | p `elem` [Tup2, Tup3, Tup4, Tup5, Tup6, Tup7, Tup8, Tup9, Tup10
             , Tup11, Tup12, Tup13, Tup14, Tup15]
  = go e

-- Fallthrough.
go (In (App p t es)) = In (App p t $ map go es)

linear :: Var -> UntypedFeld -> Bool
linear v e = count v e <= 1

-- | Occurence counter. Cares about dynamic behavior, so loops count as a lot.
count :: Var -> UntypedFeld -> Integer
count v (In (Variable v')) = if v == v' then 1 else 0
count v e@(In (Lambda v' _))
  | v == v' || v `notElem` fv e = 0
  | otherwise                  = 100 -- Possibly inside loop
count v (In (LetFun (_, _, e1) e2)) = count v e1 + count v e2
count _ (In Literal{}) = 0
count v (In (App Let _ [e1, In (Lambda x body)]))
  | v == x    = count v e1
  | otherwise = count v e1 + count v body
count _ (In (App Await _ _)) = 100 -- Do not inline.
count _ (In (App NoInline _ _)) = 100 -- Do not inline.
count v (In (App _ _ es)) = sum $ map (count v) es

-- TODO: Improve precision of switch.

constFold :: UntypedFeld -> Op -> Lit -> Lit -> UntypedFeld
constFold _ Add (LInt sz n n1) (LInt _ _ n2) = In (Literal (LInt sz n (n1 + n2)))
constFold _ Sub (LInt sz n n1) (LInt _ _ n2) = In (Literal (LInt sz n (n1 - n2)))
constFold _ Mul (LInt sz n n1) (LInt _ _ n2) = In (Literal (LInt sz n (n1 * n2)))
constFold e _ _ _ = e

-- | Scan an Epar/Ewrite-nest and return the element written to a position.
grabWrite :: Integer -> UntypedFeld -> Maybe UntypedFeld
grabWrite n (In (App EPar _ [e1,e2]))
 | Nothing <- r1 = grabWrite n e2
 | otherwise = r1
   where r1 = grabWrite n e1
grabWrite n (In (App EWrite _ [In (Literal (LInt _ _ k)), e]))
 | k == n = Just e
grabWrite _ _ = Nothing
