{-@ LIQUID "--reflection"  @-}
{-@ infix :  @-}
module LabelUpdateCheckNothingJust where

import Labels 
import Predicates 
import Prelude hiding (Maybe(..), fromJust, isJust)
import Programs 
import Simulations.Predicates
import ProofCombinators 

{-@ 
updateRowsCheckEqNothingJust
  :: (Eq l, Label l)
  => l:l
  -> lc:{l | canFlowTo lc l}
  -> lf:l
  -> ti:{TInfo l | canFlowTo (field1Label ti) l}
  -> p:Pred
  -> l2:l
  -> v2:SDBTerm l
  -> rs:[Row l]
  -> {(updateRowsCheckNothingJust lc lf ti p l2 v2 rs ==
        updateRowsCheckNothingJust lc lf ti p l2 (if (canFlowTo l2 l) then (εTerm l v2) else THole) (εRows l ti rs)) }
  / [len rs] @-}
updateRowsCheckEqNothingJust :: (Eq l, Label l) => l -> l -> l -> TInfo l -> Pred -> l -> Term l -> [Row l] -> Proof
updateRowsCheckEqNothingJust l lc lφ ti p l2 v2 []
  = assert (updateRowsCheckNothingJust lc lφ ti p l2 v2 [] ==
        updateRowsCheckNothingJust lc lφ ti p l2 (if (canFlowTo l2 l) then (εTerm l v2) else THole) (εRows l ti []))
  
updateRowsCheckEqNothingJust l lc lφ ti p l2 v2 (r:rs)
  =   updateRowsCheckNothingJust lc lφ ti p l2 v2 (r:rs)
  ==. (updateRowCheckNothingJust lc lφ ti p l2 v2 r &&
        updateRowsCheckNothingJust lc lφ ti p l2 v2 rs)
      ? assert (canFlowTo (field1Label ti) l)
      ? updateRowsCheckEqNothingJust l lc lφ ti p l2 v2 rs
      ? updateRowCheckEqNothingJust l lc lφ ti p l2 v2 r
  ==. (updateRowCheckNothingJust lc lφ ti p l2 εv2 (εRow l ti r) &&
        updateRowsCheckNothingJust lc lφ ti p l2 εv2 (εRows l ti rs))
  ==. updateRowsCheckNothingJust lc lφ ti p l2 εv2 (εRow l ti r : εRows l ti rs)
  ==. updateRowsCheckNothingJust lc lφ ti p l2 εv2 (εRows l ti (r:rs)) 
  *** QED
  where εv2 = if (canFlowTo l2 l) then (εTerm l v2) else THole



{-@ 
updateRowCheckEqNothingJust
  :: (Eq l, Label l)
  => l:l
  -> lc:{l | canFlowTo lc l}
  -> lf:l
  -> ti:{TInfo l | canFlowTo (field1Label ti) l}
  -> p:Pred
  -> l2:l
  -> v2:SDBTerm l
  -> r: Row l
  -> {(updateRowCheckNothingJust lc lf ti p l2 v2 r ==
        updateRowCheckNothingJust lc lf ti p l2 (if (canFlowTo l2 l) then (εTerm l v2) else THole) (εRow l ti r))}
@-}

updateRowCheckEqNothingJust :: (Eq l, Label l) => l -> l -> l -> TInfo l -> Pred -> l -> Term l -> Row l -> Proof
updateRowCheckEqNothingJust l lc lφ ti p l2 v2 r@(Row k v1 _) 
  =   updateRowCheckNothingJust lc lφ ti p l2 v2 r
  ==. updateRowLabel2 lc lφ ti p (field1Label ti) v1 l2 v2 r
  ==. ((l2 `join` lc) `join` lφ) `canFlowTo` makeValLabel ti v1
      ? assert (canFlowTo (field1Label ti) l)
      ? assert (εv1 == v1)
      ? assert (evalPred p r == evalPred p (εRow l ti r))
  ==. ((l2 `join` lc) `join` lφ) `canFlowTo` makeValLabel ti (rowField1 (εRow l ti r))
  ==. updateRowLabel2 lc lφ ti p (field1Label ti) (rowField1 (εRow l ti r)) l2 εv2 (εRow l ti r)
  ==. updateRowCheckNothingJust lc lφ ti p l2 εv2 (εRow l ti r)
  ==. updateRowCheckNothingJust lc lφ ti p l2 (if (canFlowTo l2 l) then (εTerm l v2) else THole) (εRow l ti r)
  *** QED
  where εv1 = if (canFlowTo (field1Label ti) l) then (εTerm l v1) else THole
        εv2 = if (canFlowTo l2 l) then (εTerm l v2) else THole

        

{-@ 
labelUpdateCheckEqNothingJust
  :: (Eq l, Label l)
  => l:l 
  -> lc:{l | canFlowTo lc l }
  -> p:Pred
  -> l2:l
  -> v2:SDBTerm l
  -> t:{Table l | canFlowTo (tableLabel (tableInfo t)) l }
  -> { (canFlowTo (field1Label (tableInfo t))  l) 
  => updateLabelCheckNothingJust lc t p l2 v2 == updateLabelCheckNothingJust lc (εTable l t) p l2 (if (canFlowTo l2 l) then (εTerm l v2) else THole) }
@-}
labelUpdateCheckEqNothingJust :: (Eq l, Label l) => l -> l -> Pred -> l -> Term l -> Table l -> Proof 
labelUpdateCheckEqNothingJust l lc p l2 v2 t@(Table ti@(TInfo lt _ lf1 _ _) rs)
   | canFlowTo (tableLabel ti) l && canFlowTo (field1Label (tableInfo t)) l
  =   updateLabelCheckNothingJust lc (εTable l (Table ti rs)) p l2 εv2
  ==. updateLabelCheckNothingJust lc (Table ti (εRows l ti rs)) p l2 εv2
  ==. updateRowsCheckNothingJust lc (labelPred p (Table ti (εRows l ti rs))) ti p l2 εv2 (εRows l ti rs)
      ? (   labelPred p (Table ti (εRows l ti rs))
        ==. (field1Label ti) `join` labelPredField2Rows p ti rs 
            ? labelPredField2RowsEq l p ti rs 
        ==. (field1Label ti) `join` labelPredField2Rows p ti (εRows l ti rs)
        ==. labelPred p (Table ti rs) *** QED )
      ? assert (ti == tableInfo t)
      ? updateRowsCheckEqNothingJust l lc  (labelPred p t) ti p l2 v2 rs

  ==. updateRowsCheckNothingJust lc (labelPred p (Table ti rs)) ti p l2 v2 rs
  ==. updateLabelCheckNothingJust lc (Table ti rs) p l2 v2 
  *** QED 
   | otherwise
   = () 
  where
    εv2 = if (canFlowTo l2 l) then (εTerm l v2) else THole

{-@ ple labelPredField2RowsEq @-}
{-@ 
labelPredField2RowsEq
  :: (Eq l, Label l)
  => l:l 
  -> p:Pred 
  -> ti:{TInfo l | canFlowTo (field1Label ti) l }
  -> rs:[Row l] 
  -> { labelPredField2Rows p ti rs == labelPredField2Rows p ti (εRows l ti rs) }
  / [len rs] @-}
labelPredField2RowsEq :: (Eq l, Label l) => l -> Pred -> TInfo l -> [Row l] -> Proof 
labelPredField2RowsEq l p ti []
  =   labelPredField2Rows p ti []
  ==. bot
  ==. labelPredField2Rows p ti (εRows l ti [])
  *** QED

labelPredField2RowsEq l p ti (r@(Row _ o1 _):rs)
  =   labelPredField2Rows p ti (r:rs)
  ==. labelPredField2Row p ti r `join` labelPredField2Rows p ti rs
  ==. makeValLabel ti (rowField1 r) `join` labelPredField2Rows p ti rs
  ==. makeValLabel ti (rowField1 (εRow l ti r)) `join` labelPredField2Rows p ti (εRows l ti rs)
  ==. labelPredField2Row p ti (εRow l ti r) `join` labelPredField2Rows p ti (εRows l ti rs)
  ==. labelPredField2Rows p ti (εRow l ti r : εRows l ti rs)
  ==. labelPredField2Rows p ti (εRows l ti (r:rs))
      ? assert (canFlowTo (field1Label ti) l)
      ? assert (εTerm l o1 == o1)
      ? assert ((rowField1 r) == (rowField1 (εRow l ti r))) 
      ? labelPredField2RowsEq  l p ti rs
      ? assert (rowField1 r == rowField1 (εRow l ti r))
  *** QED
