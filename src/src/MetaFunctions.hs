-------------------------------------------------------------------------------
-- | Erasure ------------------------------------------------------------------
-------------------------------------------------------------------------------

{-@ reflect εTerm @-}
{-@ εTerm :: Label -> t:Term -> Term / [size t] @-} 
εTerm :: Label -> Term -> Term 
εTerm _ THole          = THole
εTerm _ TTrue          = TTrue
εTerm _ TFalse         = TFalse
εTerm _ TUnit          = TUnit
εTerm _ (TVar v)       = TVar v 
εTerm l (TLam v t)     = TLam v (εTerm l t)
εTerm l (TApp t1 t2)   = TApp (εTerm l t1) (εTerm l t2)
εTerm l (TFix t)       = TFix (εTerm l t) 
εTerm l (TIF t1 t2 t3) = TIF (εTerm l t1) (εTerm l t2) (εTerm l t3)

εTerm l v@(TLabel _)   = v

εTerm l TGetLabel     = TGetLabel
εTerm l TGetClearance = TGetClearance
εTerm l (TLowerClearance t) = TLowerClearance (εTerm l t)

{-@ reflect ε @-}
ε :: Label -> Program -> Program
ε l (Pg lcur c m t) 
  | lcur `canFlowTo` l 
  = Pg lcur c m (εTerm l t)
  | otherwise 
  = Pg lcur c m THole 

-------------------------------------------------------------------------------
-- | Safety -------------------------------------------------------------------
-------------------------------------------------------------------------------

{-@ reflect ςTerm @-}
ςTerm :: Term -> Bool  
ςTerm THole          = True
ςTerm TTrue          = True
ςTerm TFalse         = True
ςTerm TUnit          = True
ςTerm (TVar _)       = True 
ςTerm (TLam _ t)     = ςTerm t
ςTerm (TApp t1 t2)   = ςTerm t1 && ςTerm t2
ςTerm (TFix t)       = ςTerm t 
ςTerm (TIF t1 t2 t3) = ςTerm t1 && ςTerm t2 && ςTerm t3

ςTerm (TLabel _)     = True 

ςTerm TGetLabel      = True 
ςTerm TGetClearance  = True 
ςTerm (TLowerClearance t)  = ςTerm t

{-@ reflect ς @-}
ς :: Program -> Bool 
ς (Pg _ _ _ t) = ςTerm t 

