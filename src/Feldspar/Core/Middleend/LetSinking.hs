module Feldspar.Core.Middleend.LetSinking ( sinkLets ) where

import Feldspar.Core.UntypedRepresentation

-- | Sink lets that are stuck between two lambdas.
-- Necessary invariant: lambdas can only appear in special places.
sinkLets :: UntypedFeld -> UntypedFeld
sinkLets = go
  where go e@(In Variable{}) = e
        go (In (Lambda v e))
         | (bs1, In (Lambda v' body)) <- collectLetBinders e
         , not $ null bs1
         = In (Lambda v (In (Lambda v' (go $ mkLets (bs1, body)))))
        go (In (Lambda v e)) = In (Lambda v (go e))
        go (In (Let e1 (In (Lambda v e2)))) = In (Let (go e1) (In (Lambda v (go e2))))
        go l@(In Literal{}) = l
        go (In (App p t es)) = In (App p t $ map go es)
