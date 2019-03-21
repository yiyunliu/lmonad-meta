{-@ LIQUID "--reflection"  @-}
{-@ infix :  @-}

module LabelUpdateCheckJN where

import Labels 
import Predicates 
import Prelude hiding (Maybe(..), fromJust, isJust)
import Programs 
import Simulations.Predicates
import ProofCombinators 

-- copy/pasted from LabelUpdateCheckNothingJust.hs
-- used global text substitution and extra lemmas for the proof to go through
-- as long as SMT solver is happy

{-@ 
updateRowsCheckEqJN
  :: (Eq l, Label l)
  => l:l
  -> lc:{l | canFlowTo lc l}
  -> lf:l
  -> ti:{TInfo l | canFlowTo (tableLabel ti) l}
  -> p:Pred
  -> l2:l
  -> v2:SDBTerm l
  -> rs: {[Row l] | 
      (canFlowTo (lfRows p ti rs) l)} 
  -> {(updateRowsCheckJN lc lf ti p l2 v2 rs ==
        updateRowsCheckJN lc lf ti p l2 (if (canFlowTo l2 l) then (εTerm l v2) else THole) (εRows l ti rs)) }
  / [len rs] @-}
updateRowsCheckEqJN :: (Eq l, Label l) => l -> l -> l -> TInfo l -> Pred -> l -> Term l -> [Row l] -> Proof
updateRowsCheckEqJN l lc lφ ti p l2 v2 []
  = assert (updateRowsCheckJN lc lφ ti p l2 v2 [] ==
        updateRowsCheckJN lc lφ ti p l2 (if (canFlowTo l2 l) then (εTerm l v2) else THole) (εRows l ti []))
  
updateRowsCheckEqJN l lc lφ ti p l2 v2 (r:rs)
  =   updateRowsCheckJN lc lφ ti p l2 v2 (r:rs)
      ? ( lfRows p ti (r:rs)
      ==. (lfRow p ti r `join` lfRows p ti rs)
      *** QED
      )
      ? joinCanFlowTo (lfRow p ti r) (lfRows p ti rs) l
      ? assert (lfRow p ti r `canFlowTo` l )
      ? assert (lfRows p ti rs `canFlowTo` l)

  ==! (updateRowCheckJN lc lφ ti p l2 v2 r &&
        updateRowsCheckJN lc lφ ti p l2 v2 rs)
      ? lawFlowTransitivity (field1Label ti) (tableLabel ti) l
      ? assert (canFlowTo (field1Label ti) l)
      ? updateRowsCheckEqJN l lc lφ ti p l2 v2 rs
      ? updateRowCheckEqJN l lc lφ ti p l2 v2 r
  ==! (updateRowCheckJN lc lφ ti p l2 εv2 (εRow l ti r) &&
        updateRowsCheckJN lc lφ ti p l2 εv2 (εRows l ti rs))
  ==! updateRowsCheckJN lc lφ ti p l2 εv2 (εRow l ti r : εRows l ti rs)
  ==! updateRowsCheckJN lc lφ ti p l2 εv2 (εRows l ti (r:rs)) 
  *** QED
  where εv2 = if (canFlowTo l2 l) then (εTerm l v2) else THole





{-@ 
updateRowCheckEqJN
  :: (Eq l, Label l)
  => l:l
  -> lc:{l | canFlowTo lc l}
  -> lf:l
  -> ti:{TInfo l | canFlowTo (tableLabel ti) l}
  -> p:Pred
  -> l1:l
  -> v1:SDBTerm l
  -> r: {Row l | (canFlowTo (lfRow p ti r) l)}
  -> {(updateRowCheckJN lc lf ti p l1 v1 r ==
        updateRowCheckJN lc lf ti p l1 (if (canFlowTo l1 l) then (εTerm l v1) else THole) (εRow l ti r))}
@-}

updateRowCheckEqJN :: (Eq l, Label l) => l -> l -> l -> TInfo l -> Pred -> l -> Term l -> Row l -> Proof
updateRowCheckEqJN l lc lφ ti p l1 v1 r@(Row k o1 o2)
  | not (l1 `canFlowTo` field1Label ti)
  =   assert (canFlowTo (field1Label ti) (tableLabel ti))
      ? lawFlowTransitivity l1 (field1Label ti) l
      ? lawFlowTransitivity (field1Label ti) (tableLabel ti) l

      ? assert (canFlowTo (field1Label ti) l)
      ? ( εr
      ==. εRow l ti (Row k o1 o2)
      ==. Row k (εTerm l o1) (εTerm l o2)
      *** QED)
      ? (εo1 ==. εTerm l o1 ==.  o1 *** QED)
      ? (εo2 ==. εTerm l o2 ==.  o2 *** QED)

      ? joinCanFlowTo (field1Label ti) (makeValLabel ti (rowField1 r)) l
      ? use (lfRow p ti r == makeValLabel ti o1)
      ? use (labelPredRow p ti r == (field1Label ti `join` makeValLabel ti o1))
      ? simulationsEvalPred p r l ti

      -- joinCanFlow proofs for updateRowLabel1
      ? joinCanFlowTo (l1 `join` lc) lφ (field1Label ti)
      ? joinCanFlowTo l1 lc (field1Label ti)

      ? joinCanFlowTo (l1 `join` lc) lφ (field1Label ti)
      ? joinCanFlowTo l1 lc (field1Label ti)      
    
      ? assert (not (updateRowLabel1 lc lφ ti p l1 v1 (makeValLabel ti o1)  o2 r))
      ? assert (not (updateRowLabel1 lc lφ ti p l1 εv1
                     (makeValLabel ti (rowField1 (εRow l ti r)) ) (rowField2 (εRow l ti r))
                     (εRow l ti r)))
      ? ( updateRowCheckJN lc lφ ti p l1 εv1 (εRow l ti r)
      ==. (updateRowLabel1 lc lφ ti p l1 εv1 (makeValLabel ti εo1) εo2 εr && updateRowLabel2 lc lφ ti p l1 εv1 (makeValLabel ti εo1) εo2 εr)
      ==. False 
      *** QED)
      ? ( updateRowCheckJN lc lφ ti p l1 v1 r
      ==. (updateRowLabel1 lc lφ ti p l1 v1 (makeValLabel ti o1) o2 r && updateRowLabel2 lc lφ ti p l1 v1 (makeValLabel ti o1) o2 r)
      ==. False
      *** QED)
  *** QED
  | otherwise
  =   updateRowCheckJN lc lφ ti p l1 v1 r
  ==. updateRowLabel1 lc lφ ti p l1 v1 (makeValLabel ti o1)  o2 r
  ==. (updateRowLabel2 lc lφ ti p l1 v1 (makeValLabel ti o1) o2 r)
  ==. ((l1 `join` lc) `join` lφ) `canFlowTo` field1Label ti
      ? ( εr
      ==. εRow l ti (Row k o1 o2)
      ==. Row k (εTerm l o1) (εTerm l o2)
      *** QED)
      ? (εo1 ==. εTerm l o1 ==.  o1 *** QED)
      ? (εo2 ==. εTerm l o2 ==.  o2 *** QED)  
      ? joinCanFlowTo l1 lc (field1Label ti)
      ? joinCanFlowTo (l1 `join` lc) lφ (field1Label ti)
      ? assert (canFlowTo (field1Label ti) (tableLabel ti))
      ? lawFlowTransitivity l1 (field1Label ti) l
      ? lawFlowTransitivity (field1Label ti) (tableLabel ti) l
      ? assert (canFlowTo (field1Label ti) l)
      ? use (εo1 == o1)
      ? assert (canFlowTo l1 l)
      ? lawFlowTransitivity (field1Label ti) (tableLabel ti) l
      ? joinCanFlowTo (field1Label ti) (makeValLabel ti (rowField1 r)) l
      ? use (lfRow p ti r == makeValLabel ti o1)
      ? use (labelPredRow p ti r == (field1Label ti `join` makeValLabel ti o1))
      ? simulationsEvalPred p r l ti
      ? ( updateRowCheckJN lc lφ ti p l1 εv1 (εRow l ti r)
      ==. (updateRowLabel1 lc lφ ti p l1 εv1 (makeValLabel ti εo1) εo2 εr && updateRowLabel2 lc lφ ti p l1 εv1 (makeValLabel ti εo1) εo2 εr)
      *** QED)
      ? ( updateRowCheckJN lc lφ ti p l1 v1 r
      ==. (updateRowLabel1 lc lφ ti p l1 v1 (makeValLabel ti o1) o2 r && updateRowLabel2 lc lφ ti p l1 v1 (makeValLabel ti o1) o2 r)
      *** QED)      
  ==. ((l1 `join` lc) `join` lφ) `canFlowTo` makeValLabel ti (rowField1 (εRow l ti r))
  ==. updateRowLabel1 lc lφ ti p (field1Label ti) (rowField1 (εRow l ti r)) l1 εv1 (εRow l ti r)
  ==. updateRowCheckJN lc lφ ti p l1 εv1 (εRow l ti r)
  ==. updateRowCheckJN lc lφ ti p l1 (if (canFlowTo l1 l) then (εTerm l v1) else THole) (εRow l ti r)
  *** QED
  where -- εo1 = if (canFlowTo (field1Label ti) l) then (εTerm l o1) else THole
        εv1 = if (canFlowTo l1 l) then (εTerm l v1) else THole
        εr  = εRow l ti r
        Row _ εo1 εo2  = εRow l ti r
        

{-@ 
labelUpdateCheckEqJN
  :: (Eq l, Label l)
  => l:l 
  -> lc:{l | canFlowTo lc l }
  -> p:Pred
  -> l2:l
  -> v2:SDBTerm l
  -> t:{Table l | canFlowTo (tableLabel (tableInfo t)) l}
  -> { (canFlowTo (lfTable p t)  l) 
  => updateLabelCheckJN lc t p l2 v2 == updateLabelCheckJN lc (εTable l t) p l2 (if (canFlowTo l2 l) then (εTerm l v2) else THole) }
@-}
labelUpdateCheckEqJN :: (Eq l, Label l) => l -> l -> Pred -> l -> Term l -> Table l -> Proof 
labelUpdateCheckEqJN l lc p l2 v2 t@(Table ti@(TInfo lt _ lf1 _ _) rs)
   | canFlowTo (lfTable p t) l
  =   updateLabelCheckJN lc (εTable l (Table ti rs)) p l2 εv2
  ==. updateLabelCheckJN lc (Table ti (εRows l ti rs)) p l2 εv2
  ==. updateRowsCheckJN lc (lfTable p (Table ti (εRows l ti rs))) ti p l2 εv2 (εRows l ti rs)
      ? (   lfTable p (Table ti (εRows l ti rs))
        ==. lfRows p ti rs
            ? assert ((field1Label ti) `canFlowTo` (tableLabel ti))
            ? lawFlowTransitivity  (field1Label ti)  (tableLabel ti)  l
            ? lfRowsEq l p ti rs 
        ==. lfRows p ti (εRows l ti rs)
        ==. lfTable p (Table ti rs) *** QED )
      ? assert (ti == tableInfo t)
      ? updateRowsCheckEqJN l lc  (lfTable p t) ti p l2 v2 rs 
  ==. updateRowsCheckJN lc (lfTable p (Table ti rs)) ti p l2 v2 rs
  ==. updateLabelCheckJN lc (Table ti rs) p l2 v2 
  *** QED 
   | otherwise
   = () 
  where
    εv2 = if (canFlowTo l2 l) then (εTerm l v2) else THole

{-@ 
lfRowsEq 
  :: (Eq l, Label l)
  => l:l 
  -> p:Pred 
  -> ti:{TInfo l | canFlowTo (field1Label ti) l }
  -> rs:[Row l] 
  -> { lfRows p ti rs == lfRows p ti (εRows l ti rs) }
  / [len rs] @-}
lfRowsEq :: (Eq l, Label l) => l -> Pred -> TInfo l -> [Row l] -> Proof 
lfRowsEq l p ti []
  =   lfRows p ti (εRows l ti []) 
  ==. bot 
  ==. lfRows p ti [] 
  *** QED 

lfRowsEq l p ti (r@(Row k o1 o2):rs)
  =   lfRows p ti (εRows l ti (r:rs))
  ==. lfRows p ti (εRow l ti r:εRows l ti rs)
  ==. lfRow p ti (εRow l ti r) `join` lfRows p ti (εRows l ti rs)
      ? assert (canFlowTo (field1Label ti) l)
      ? assert (εTerm l o1 == o1)
      ? assert ((rowField1 r) == (rowField1 (εRow l ti r))) 
      ? lfRowsEq l p ti rs  
  ==. lfRow p ti r `join` lfRows p ti rs
  ==. lfRows p ti (r:rs)
  *** QED 


