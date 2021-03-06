{-@ LIQUID "--exactdc"                                  @-}
{-@ LIQUID "--higherorder"                              @-}
{-@ LIQUID "--automatic-instances=liquidinstanceslocal" @-}
-- {-@ LIQUID "--no-case-expand" @-}

module Simulations.Language where

import Label
import Language
import Programs
import MetaFunctions 
import ProofCombinators

{-@ propagateExceptionFalseEvalsToNonexception 
 :: {t : Term | not (propagateException t)}
 -> v : {not (eval t == TException)}
 @-}
propagateExceptionFalseEvalsToNonexception :: Term -> Proof
propagateExceptionFalseEvalsToNonexception t | propagateException t = unreachable
propagateExceptionFalseEvalsToNonexception TException = unreachable
-- propagateExceptionFalseEvalsToNonexception t = $wine eval t
propagateExceptionFalseEvalsToNonexception t@(TFix (TLam x t1)) = 
        eval t
    ==. subst (Sub x (TFix (TLam x t1))) t1
    *** QED
propagateExceptionFalseEvalsToNonexception t@(TFix t1) = 
        eval t
    ==. TFix (eval t1)
    *** QED
propagateExceptionFalseEvalsToNonexception t@(TIf TTrue t2 _) = 
        eval t
    ==. t2
    *** QED
propagateExceptionFalseEvalsToNonexception t@(TIf TFalse _ t3) = 
        eval t
    ==. t3
    *** QED
propagateExceptionFalseEvalsToNonexception t@(TIf t1 t2 t3) = 
        eval t
    ==. TIf (eval t1) t2 t3
    *** QED

propagateExceptionFalseEvalsToNonexception t@(TApp (TLam x t1) t2) = 
        eval t
    ==. subst (Sub x t2) t1
    *** QED
propagateExceptionFalseEvalsToNonexception t@(TApp t1 t2) = 
        eval t
    ==. TApp (eval t1) t2
    *** QED

propagateExceptionFalseEvalsToNonexception t@(TJoin (TVLabel l1) (TVLabel l2)) = 
        eval t
    ==. TVLabel (join l1 l2)
    *** QED
propagateExceptionFalseEvalsToNonexception t@(TJoin (TVLabel l1) t2) = 
        eval t
    ==. TJoin (TVLabel l1) (eval t2)
    *** QED
propagateExceptionFalseEvalsToNonexception t@(TJoin t1 t2) = 
        eval t
    ==. TJoin (eval t1) t2
    *** QED

propagateExceptionFalseEvalsToNonexception t@(TMeet (TVLabel l1) (TVLabel l2)) = 
        eval t
    ==. TVLabel (meet l1 l2)
    *** QED
propagateExceptionFalseEvalsToNonexception t@(TMeet (TVLabel l1) t2) = 
        eval t
    ==. TMeet (TVLabel l1) (eval t2)
    *** QED
propagateExceptionFalseEvalsToNonexception t@(TMeet t1 t2) = 
        eval t
    ==. TMeet (eval t1) t2
    *** QED

propagateExceptionFalseEvalsToNonexception t@(TCanFlowTo (TVLabel l1) (TVLabel l2)) = 
        eval t
    ==. boolToTerm (canFlowTo l1 l2)
    *** QED
propagateExceptionFalseEvalsToNonexception t@(TCanFlowTo (TVLabel l1) t2) = 
        eval t
    ==. TCanFlowTo (TVLabel l1) (eval t2)
    *** QED
propagateExceptionFalseEvalsToNonexception t@(TCanFlowTo t1 t2) = 
        eval t
    ==. TCanFlowTo (eval t1) t2
    *** QED

propagateExceptionFalseEvalsToNonexception t@(TLowerClearance t1) = 
        eval t
    ==. TLowerClearance (eval t1)
    *** QED

propagateExceptionFalseEvalsToNonexception t@(TUnlabel t1) = 
        eval t
    ==. TUnlabel (eval t1)
    *** QED

propagateExceptionFalseEvalsToNonexception t@(TLabel l@(TVLabel _) t2) = 
        eval t
    ==. TLabel l (eval t2)
    *** QED

propagateExceptionFalseEvalsToNonexception t@(TLabel t1 t2) = 
        eval t
    ==. TLabel (eval t1) t2
    *** QED

propagateExceptionFalseEvalsToNonexception t@(TLabelOf (TLabeledTCB l _ )) = 
        eval t
    ==. TVLabel l
    *** QED
propagateExceptionFalseEvalsToNonexception t@(TLabelOf t1) = 
        eval t
    ==. TLabelOf (eval t1)
    *** QED

propagateExceptionFalseEvalsToNonexception t@(TToLabeled l@(TVLabel _) t2) = 
        eval t
    ==. TToLabeled l (eval t2)
    *** QED
propagateExceptionFalseEvalsToNonexception t@(TToLabeled t1 t2) = 
        eval t
    ==. TToLabeled (eval t1) t2
    *** QED

propagateExceptionFalseEvalsToNonexception t =
        eval t
    ==. t
    *** QED


{-@ erasePropagateExceptionFalse
 :: l : Label
 -> {t : Term | not (propagateException t)}
 -> {not (propagateException (εTerm l t))}
 / [size t]
 @-}
erasePropagateExceptionFalse :: Label -> Term -> Proof
erasePropagateExceptionFalse l TException = unreachable
erasePropagateExceptionFalse l t@(TLam v t1) = 
        not (propagateException (εTerm l t))
    ==. not (propagateException (TLam v (εTerm l t1))) ? erasePropagateExceptionFalse l t1
    *** QED
erasePropagateExceptionFalse l t@(TApp t1 t2) = 
        not (propagateException (εTerm l t))
    ==. not (propagateException (TApp (εTerm l t1) (εTerm l t2))) ? erasePropagateExceptionFalse l t1 &&& erasePropagateExceptionFalse l t2
    *** QED
erasePropagateExceptionFalse l t@(TFix t1) = 
        not (propagateException (εTerm l t))
    ==. not (propagateException (TFix (εTerm l t1))) ? erasePropagateExceptionFalse l t1
    *** QED
erasePropagateExceptionFalse l t@(TIf t1 t2 t3) = 
        not (propagateException (εTerm l t))
    ==. not (propagateException (TIf (εTerm l t1) (εTerm l t2) (εTerm l t3))) ? erasePropagateExceptionFalse l t1 &&& erasePropagateExceptionFalse l t2 &&& erasePropagateExceptionFalse l t3
    *** QED
erasePropagateExceptionFalse l t@(TJoin t1 t2) = 
        not (propagateException (εTerm l t))
    ==. not (propagateException (TJoin (εTerm l t1) (εTerm l t2))) ? erasePropagateExceptionFalse l t1 &&& erasePropagateExceptionFalse l t2
    *** QED
erasePropagateExceptionFalse l t@(TMeet t1 t2) = 
        not (propagateException (εTerm l t))
    ==. not (propagateException (TMeet (εTerm l t1) (εTerm l t2))) ? erasePropagateExceptionFalse l t1 &&& erasePropagateExceptionFalse l t2
    *** QED
erasePropagateExceptionFalse l t@(TCanFlowTo t1 t2) = 
        not (propagateException (εTerm l t))
    ==. not (propagateException (TCanFlowTo (εTerm l t1) (εTerm l t2))) ? erasePropagateExceptionFalse l t1 &&& erasePropagateExceptionFalse l t2
    *** QED
erasePropagateExceptionFalse l t@(TBind t1 t2) = 
        not (propagateException (εTerm l t))
    ==. not (propagateException (TBind (εTerm l t1) (εTerm l t2))) ? erasePropagateExceptionFalse l t1 &&& erasePropagateExceptionFalse l t2
    *** QED
erasePropagateExceptionFalse l t@(TLowerClearance t1) = 
        not (propagateException (εTerm l t))
    ==. not (propagateException (TLowerClearance (εTerm l t1))) ? erasePropagateExceptionFalse l t1
    *** QED
erasePropagateExceptionFalse l t@(TLabeledTCB l' t1) | l' `canFlowTo` l = 
        not (propagateException (εTerm l t))
    ==. not (propagateException (TLabeledTCB l' (εTerm l t1)))
    *** QED
erasePropagateExceptionFalse l t@(TLabeledTCB l' t1) = 
        not (propagateException (εTerm l t))
    ==. not (propagateException (TLabeledTCB l' THole))
    *** QED
erasePropagateExceptionFalse l t@(TLabelOf t1) = 
        not (propagateException (εTerm l t))
    ==. not (propagateException (TLabelOf (εTerm l t1))) ? erasePropagateExceptionFalse l t1
    *** QED
erasePropagateExceptionFalse l t@(TLabel t1 t2) =
        not (propagateException (εTerm l t))
    ==. not (propagateException (TLabel (εTerm l t1) (εTerm l t2))) ? erasePropagateExceptionFalse l t1 &&& erasePropagateExceptionFalse l t2
    *** QED
erasePropagateExceptionFalse l t@(TUnlabel t1) = 
        not (propagateException (εTerm l t))
    ==. not (propagateException (TUnlabel (εTerm l t1))) ? erasePropagateExceptionFalse l t1
    *** QED
erasePropagateExceptionFalse l t@(TToLabeled t1 t2) =
        not (propagateException (εTerm l t))
    ==. not (propagateException (TToLabeled (εTerm l t1) (εTerm l t2))) ? erasePropagateExceptionFalse l t1
    *** QED
erasePropagateExceptionFalse l t = 
        not (propagateException (εTerm l t))
    ==. not (propagateException t)
    *** QED

-- {-@ automatic-instances erasePropagateExceptionFalseEvalsToNonexception @-}
{-@ erasePropagateExceptionFalseEvalsToNonexception
 :: l : Label
 -> {t : Term | not (eval t == TException)}
 -> {v : Proof | not (eval (εTerm l t) == TException)}
 / [size t]
 @-}
erasePropagateExceptionFalseEvalsToNonexception :: Label -> Term -> Proof
erasePropagateExceptionFalseEvalsToNonexception l t | propagateException t = assertEqual (eval t) TException
erasePropagateExceptionFalseEvalsToNonexception l TException = unreachable
erasePropagateExceptionFalseEvalsToNonexception l t@(TLam v t1) =
        eval (εTerm l t)
    ==. eval (TLam v (εTerm l t1))
    ==. TLam v (εTerm l t1) ?
            erasePropagateExceptionFalse l t1
        -- &&& propagateExceptionFalseEvalsToNonexception (TLam v (εTerm l t1))
    *** QED

erasePropagateExceptionFalseEvalsToNonexception l t@(TApp (TLam x t1) t2) =
        eval (εTerm l t)
    ==. eval (TApp (εTerm l (TLam x t1)) (εTerm l t2))
    ==. eval (TApp (TLam x (εTerm l t1)) (εTerm l t2))
    ==. subst (Sub x (εTerm l t2)) (εTerm l t1) ?
            erasePropagateExceptionFalse l t1
        &&& erasePropagateExceptionFalse l t2
        -- &&& propagateExceptionFalseEvalsToNonexception (εTerm l t1)
    *** QED

erasePropagateExceptionFalseEvalsToNonexception l t@(TApp t1 t2) =
    let et1 = eval (εTerm l t1) in
    let et2 = εTerm l t2 in
        eval (εTerm l t)
    ==. eval (TApp (εTerm l t1) (εTerm l t2))
    ==. TApp (eval (εTerm l t1)) (εTerm l t2) ? 
            erasePropagateExceptionFalse l t1
        &&& erasePropagateExceptionFalse l t2
        -- &&& propagateExceptionFalseEvalsToNonexception (εTerm l t1)
    *** QED

erasePropagateExceptionFalseEvalsToNonexception l t@(TFix (TLam x t1)) =
        eval (εTerm l t)
    ==. eval (TFix (εTerm l (TLam x t1)))
    ==. eval (TFix (TLam x (εTerm l t1)))
    ==. subst (Sub x (TFix (TLam x (εTerm l t1)))) (εTerm l t1) ?
            erasePropagateExceptionFalse l t1
        -- &&& propagateExceptionFalseEvalsToNonexception (εTerm l t1)
    *** QED

erasePropagateExceptionFalseEvalsToNonexception l t@(TFix t1) =
        eval (εTerm l t)
    ==. eval (TFix (εTerm l t1))
    ==. TFix (eval (εTerm l t1)) ? 
            erasePropagateExceptionFalse l t1
        -- &&& propagateExceptionFalseEvalsToNonexception (εTerm l t1)
    *** QED
    
erasePropagateExceptionFalseEvalsToNonexception l t@(TIf TTrue t2 t3) =
        eval (εTerm l t)
    ==. eval (TIf (εTerm l TTrue) (εTerm l t2) (εTerm l t3))
    ==. eval (TIf TTrue (εTerm l t2) (εTerm l t3))
    ==. εTerm l t2 ? 
            erasePropagateExceptionFalse l t2
        -- &&& propagateExceptionFalseEvalsToNonexception (εTerm l t2)
        &&& erasePropagateExceptionFalse l t3
        -- &&& propagateExceptionFalseEvalsToNonexception (εTerm l t3)
    *** QED
        
erasePropagateExceptionFalseEvalsToNonexception l t@(TIf TFalse t2 t3) =
        eval (εTerm l t)
    ==. eval (TIf (εTerm l TFalse) (εTerm l t2) (εTerm l t3))
    ==. eval (TIf TFalse (εTerm l t2) (εTerm l t3))
    ==. εTerm l t3 ? 
            erasePropagateExceptionFalse l t2
        -- &&& propagateExceptionFalseEvalsToNonexception (εTerm l t2)
        &&& erasePropagateExceptionFalse l t3
        -- &&& propagateExceptionFalseEvalsToNonexception (εTerm l t3)
    *** QED
        
erasePropagateExceptionFalseEvalsToNonexception l t@(TIf t1 t2 t3) =
        eval (εTerm l t)
    ==. eval (TIf (εTerm l t1) (εTerm l t2) (εTerm l t3))
    ==. TIf (eval (εTerm l t1)) (εTerm l t2) (εTerm l t3) ?
            erasePropagateExceptionFalse l t1
        &&& erasePropagateExceptionFalse l t2
        &&& erasePropagateExceptionFalse l t3
    *** QED

erasePropagateExceptionFalseEvalsToNonexception l t@(TJoin t1@(TVLabel l1) t2@(TVLabel l2)) =
        eval (εTerm l t)
    ==. eval (TJoin (εTerm l t1) (εTerm l t2))
    ==. eval (TJoin t1 t2)
    ==. TVLabel (join l1 l2)
    *** QED

erasePropagateExceptionFalseEvalsToNonexception l t@(TJoin t1@(TVLabel l1) t2) =
        eval (εTerm l t)
    ==. eval (TJoin (εTerm l t1) (εTerm l t2))
    ==. eval (TJoin t1 (εTerm l t2))
    ==. TJoin t1 (eval (εTerm l t2)) ?
            erasePropagateExceptionFalse l t2
    *** QED

erasePropagateExceptionFalseEvalsToNonexception l t@(TJoin t1 t2) =
        eval (εTerm l t)
    ==. eval (TJoin (εTerm l t1) (εTerm l t2))
    ==. TJoin (eval (εTerm l t1)) (εTerm l t2) ?
            erasePropagateExceptionFalse l t1
        &&& erasePropagateExceptionFalse l t2
    *** QED

erasePropagateExceptionFalseEvalsToNonexception l t@(TMeet t1@(TVLabel l1) t2@(TVLabel l2)) =
        eval (εTerm l t)
    ==. eval (TMeet (εTerm l t1) (εTerm l t2))
    ==. eval (TMeet t1 t2)
    ==. TVLabel (meet l1 l2)
    *** QED

erasePropagateExceptionFalseEvalsToNonexception l t@(TMeet t1@(TVLabel l1) t2) =
        eval (εTerm l t)
    ==. eval (TMeet (εTerm l t1) (εTerm l t2))
    ==. eval (TMeet t1 (εTerm l t2))
    ==. TMeet t1 (eval (εTerm l t2)) ?
            erasePropagateExceptionFalse l t2
    *** QED

erasePropagateExceptionFalseEvalsToNonexception l t@(TMeet t1 t2) =
        eval (εTerm l t)
    ==. eval (TMeet (εTerm l t1) (εTerm l t2))
    ==. TMeet (eval (εTerm l t1)) (εTerm l t2) ?
            erasePropagateExceptionFalse l t1
        &&& erasePropagateExceptionFalse l t2
    *** QED

erasePropagateExceptionFalseEvalsToNonexception l t@(TCanFlowTo t1@(TVLabel l1) t2@(TVLabel l2)) =
        eval (εTerm l t)
    ==. eval (TCanFlowTo (εTerm l t1) (εTerm l t2))
    ==. eval (TCanFlowTo t1 t2)
    ==. boolToTerm (canFlowTo l1 l2)
    *** QED

erasePropagateExceptionFalseEvalsToNonexception l t@(TCanFlowTo t1@(TVLabel l1) t2) =
        eval (εTerm l t)
    ==. eval (TCanFlowTo (εTerm l t1) (εTerm l t2))
    ==. eval (TCanFlowTo t1 (εTerm l t2))
    ==. TCanFlowTo t1 (eval (εTerm l t2)) ?
            erasePropagateExceptionFalse l t2
    *** QED

erasePropagateExceptionFalseEvalsToNonexception l t@(TCanFlowTo t1 t2) =
        eval (εTerm l t)
    ==. eval (TCanFlowTo (εTerm l t1) (εTerm l t2))
    ==. TCanFlowTo (eval (εTerm l t1)) (εTerm l t2) ?
            erasePropagateExceptionFalse l t1
        &&& erasePropagateExceptionFalse l t2
    *** QED

erasePropagateExceptionFalseEvalsToNonexception l t@(TLowerClearance t1) =
        eval (εTerm l t)
    ==. eval (TLowerClearance (εTerm l t1))
    ==. TLowerClearance (eval (εTerm l t1)) ?
            erasePropagateExceptionFalse l t1
    *** QED
    
erasePropagateExceptionFalseEvalsToNonexception l t@(TUnlabel t1) =
        eval (εTerm l t)
    ==. eval (TUnlabel (εTerm l t1))
    ==. TUnlabel (eval (εTerm l t1)) ?
            erasePropagateExceptionFalse l t1
    *** QED
    
erasePropagateExceptionFalseEvalsToNonexception l t@(TLabel t1 t2) =
        eval (εTerm l t)
    ==. eval (TLabel (εTerm l t1) (εTerm l t2))
    ==. TLabel (eval (εTerm l t1)) (εTerm l t2) ?
            erasePropagateExceptionFalse l t1
        &&& erasePropagateExceptionFalse l t2
    *** QED
    
erasePropagateExceptionFalseEvalsToNonexception l t@(TLabeledTCB l' t1) | l' `canFlowTo` l  = 
        eval (εTerm l t)
    ==. eval (TLabeledTCB l' (εTerm l t1))
    ==. TLabeledTCB l' (εTerm l t1)
    *** QED

erasePropagateExceptionFalseEvalsToNonexception l t@(TLabeledTCB l' t1) = 
        eval (εTerm l t)
    ==. eval (TLabeledTCB l' THole)
    ==. TLabeledTCB l' THole
    *** QED

erasePropagateExceptionFalseEvalsToNonexception l t@(TLabelOf t'@(TLabeledTCB l' _)) = 
        eval (εTerm l t)
    ==. eval (TLabelOf (εTerm l t'))
    ==. TVLabel l' ?
            erasePropagateExceptionFalse l t'
    *** QED

erasePropagateExceptionFalseEvalsToNonexception l t@(TLabelOf t1) =
        eval (εTerm l t)
    ==. eval (TLabelOf (εTerm l t1))
    ==. TLabelOf (eval (εTerm l t1)) ?
            erasePropagateExceptionFalse l t1
    *** QED

erasePropagateExceptionFalseEvalsToNonexception l t@(TToLabeled t1@(TVLabel _) t2) =
        eval (εTerm l t)
    ==. eval (TToLabeled (εTerm l t1) (εTerm l t2))
    ==. eval (TToLabeled t1 (εTerm l t2))
    ==. TToLabeled t1 (eval (εTerm l t2))
    *** QED

erasePropagateExceptionFalseEvalsToNonexception l t@(TToLabeled t1 t2) =
        eval (εTerm l t)
    ==. eval (TToLabeled (εTerm l t1) (εTerm l t2))
    ==. TToLabeled (eval (εTerm l t1)) (εTerm l t2) ?
            erasePropagateExceptionFalse l t1
    *** QED

erasePropagateExceptionFalseEvalsToNonexception l t@(TBind t1 t2) =
        eval (εTerm l (TBind t1 t2))
    ==. eval (TBind (εTerm l t1) (εTerm l t2))
    ==. TBind (εTerm l t1) (εTerm l t2) ?
            erasePropagateExceptionFalse l t1
        &&& erasePropagateExceptionFalse l t2
    *** QED
    
erasePropagateExceptionFalseEvalsToNonexception l t = 
    let t' = eval t in
        eval (εTerm l t)
    ==. eval t
    ==. t'
    *** QED

