{-@ LIQUID "--reflection"  @-}
module LabelPredErase where

import Labels 
import Predicates 
import Prelude hiding (Maybe(..), fromJust, isJust)
import Programs 

import ProofCombinators 
import LabelPredImplies

labelPredErase :: (Eq l, Label l) => l -> Pred -> TName -> DB l -> Proof
{-@ labelPredErase :: Label l => l:l -> p:Pred -> n:TName 
  -> db:{DB l | isJust (lookupTable n db) && isJust (lookupTable n (εDB l db)) } 
  -> { not (canFlowTo (labelPredTable p (fromJust (lookupTable n db))) l) <=> not (canFlowTo (labelPredTable p (fromJust (lookupTable n (εDB l db)))) l) }
 @-}
labelPredErase l p n [] 
  = assert (isJust (lookupTable n (εDB l []))) 
labelPredErase l p n' (Pair n t@(Table ti rs):db)
  | n == n', tableLabel ti `canFlowTo` l
  =   labelPred p (fromJust (lookupTable n' (εDB l (Pair n t:db)))) `canFlowTo` l
  ==. labelPred p (fromJust (lookupTable n' (Pair n (εTable l t):εDB l db))) `canFlowTo` l
  ==. labelPred p (fromJust (Just (εTable l t))) `canFlowTo` l
  ==. labelPred p (εTable l t) `canFlowTo` l
      ? assert (tableLabel ti `canFlowTo` l)
  ==. labelPred p (Table ti (εRows l ti rs)) `canFlowTo` l
  ==. field1Label ti `join` labelPredField2Rows p ti (εRows l ti rs) `canFlowTo` l
      ? field1Label ti `join` labelPredField2RowsErase l p ti rs 
  ==. field1Label ti `join` labelPredField2Rows p ti rs `canFlowTo` l
  ==. labelPred p t `canFlowTo` l
  ==. labelPred p (fromJust (Just t)) `canFlowTo` l
  ==. labelPred p (fromJust (lookupTable n' (Pair n t:db))) `canFlowTo` l
  *** QED 
labelPredErase l p n' (Pair n t@(Table ti rs):db)
  | n == n'
  =   labelPred p (fromJust (lookupTable n' (εDB l (Pair n t:db)))) `canFlowTo` l
  ==. labelPred p (fromJust (lookupTable n' (Pair n (εTable l t):εDB l db))) `canFlowTo` l
  ==. labelPred p (fromJust (Just (εTable l t))) `canFlowTo` l
  ==. labelPred p (εTable l t) `canFlowTo` l
  ==. labelPred p (Table ti []) `canFlowTo` l
  ==. field1Label ti `join` labelPredField2Rows p ti [] `canFlowTo` l
  ==. (tableLabel ti `join` field1Label ti) `canFlowTo` l
      ? joinCanFlowTo (tableLabel ti) (field1Label ti) l
  ==. False 
  ==. tableLabel ti `canFlowTo` l 
       ? tableLabelDep l p ti rs 
  ==. field1Label ti `join` labelPredField2Rows p ti rs `canFlowTo` l
  ==. labelPred p t `canFlowTo` l
  ==. labelPred p (fromJust (Just t)) `canFlowTo` l
  ==. labelPred p (fromJust (lookupTable n' (Pair n t:db))) `canFlowTo` l
  *** QED 


labelPredErase l p n' (Pair n t:db)
  =   labelPred p (fromJust (lookupTable n' (εDB l (Pair n t:db))))
  ==. labelPred p (fromJust (lookupTable n' (Pair n (εTable l t):εDB l db)))
  ==. labelPred p (fromJust (lookupTable n' (εDB l db)))       
      ? assert (lookupTable n' db == lookupTable n' (Pair n t:db))
      ? labelPredErase l p n' db  
  ==. labelPred p (fromJust (lookupTable n' db))
  ==. labelPred p (fromJust (lookupTable n' (Pair n t:db)))
  *** QED 

field1Label ti `join` labelPredField2RowsErase :: (Eq l, Label l) => l -> Pred -> TInfo l -> [Row l] -> Proof
{-@ field1Label ti `join` labelPredField2RowsErase 
  :: Label l 
  => l:l 
  -> p:Pred 
  -> ti:{TInfo l | canFlowTo (tableLabel ti) l } 
  -> rs:[Row l]
  -> { not (canFlowTo (field1Label ti `join` labelPredField2Rows p ti rs) l) <=> not (canFlowTo (field1Label ti `join` labelPredField2Rows p ti (εRows l ti rs)) l) }
 @-}

field1Label ti `join` labelPredField2RowsErase l p ti rs 
   | not (pDep1 p)      
  =   field1Label ti `join` labelPredField2Rows p ti (εRows l ti rs) `canFlowTo` l 
  ==. tableLabel ti `canFlowTo` l 
  ==. field1Label ti `join` labelPredField2Rows p ti rs `canFlowTo` l 
  *** QED 


field1Label ti `join` labelPredField2RowsErase l p ti [] 
  =   field1Label ti `join` labelPredField2Rows p ti (εRows l ti []) `canFlowTo` l 
  ==. field1Label ti `join` labelPredField2Rows p ti [] `canFlowTo` l 
  *** QED 


field1Label ti `join` labelPredField2RowsErase l p ti (r:rs)
  =   field1Label ti `join` labelPredField2Rows p ti (εRows l ti (r:rs)) `canFlowTo` l 
  ==. field1Label ti `join` labelPredField2Rows p ti (εRow l ti r:εRows l ti rs) `canFlowTo` l 
  ==. ((tableLabel ti `join` labelPredRow p ti (εRow l ti r)) `join` field1Label ti `join` labelPredField2Rows p ti (εRows l ti rs)) `canFlowTo` l 
      ? unjoinCanFlowTo (tableLabel ti) (labelPredRow p ti (εRow l ti r)) l 
      ?   joinCanFlowTo (tableLabel ti) (labelPredRow p ti (εRow l ti r)) l 
      ? unjoinCanFlowTo (tableLabel ti `join` labelPredRow p ti (εRow l ti r)) (field1Label ti `join` labelPredField2Rows p ti (εRows l ti rs)) l 
      ?   joinCanFlowTo (tableLabel ti `join` labelPredRow p ti (εRow l ti r)) (field1Label ti `join` labelPredField2Rows p ti (εRows l ti rs)) l 
  ==. (  tableLabel ti         `canFlowTo` l 
    &&
        labelPredRow p ti (εRow l ti r) `canFlowTo` l 
    &&
      field1Label ti `join` labelPredField2Rows p ti (εRows l ti rs) `canFlowTo` l
      )
      ? unjoinCanFlowTo (field1Label ti) (makeValLabel ti (rowField1 (εRow l ti r))) l 
      ?   joinCanFlowTo (field1Label ti) (makeValLabel ti (rowField1 (εRow l ti r))) l 

  ==. ( tableLabel ti         `canFlowTo` l 
    &&
        (field1Label ti `join` makeValLabel ti (rowField1 (εRow l ti r))) `canFlowTo` l 
    &&
      field1Label ti `join` labelPredField2Rows p ti (εRows l ti rs) `canFlowTo` l
      )
      ? unjoinCanFlowTo (field1Label ti) (makeValLabel ti (rowField1 (εRow l ti r))) l 
      ?   joinCanFlowTo (field1Label ti) (makeValLabel ti (rowField1 (εRow l ti r))) l 
  ==. ( tableLabel ti         `canFlowTo` l 
    &&
        field1Label ti `canFlowTo` l 
    && 
        makeValLabel ti (rowField1 (εRow l ti r)) `canFlowTo` l 
    &&
      field1Label ti `join` labelPredField2Rows p ti (εRows l ti rs) `canFlowTo` l
      )
      ? field1Label ti `join` labelPredField2RowsErase l p ti rs
      ? assert (εTerm l  (rowField1 r) == rowField1 r)
  ==. ( tableLabel ti         `canFlowTo` l 
    &&
        field1Label ti `canFlowTo` l 
    && 
        makeValLabel ti (rowField1 r)   `canFlowTo` l 
    &&
      field1Label ti `join` labelPredField2Rows p ti rs `canFlowTo` l
      )
      ? unjoinCanFlowTo (field1Label ti) (makeValLabel ti (rowField1 r)) l 
      ?   joinCanFlowTo (field1Label ti) (makeValLabel ti (rowField1 r)) l 
  ==. ( tableLabel ti         `canFlowTo` l 
    &&
        (field1Label ti `join` makeValLabel ti (rowField1 r))   `canFlowTo` l 
    &&
      field1Label ti `join` labelPredField2Rows p ti rs `canFlowTo` l
      )
  ==. ( tableLabel ti         `canFlowTo` l 
    &&
        labelPredRow p ti r `canFlowTo` l 
    && 
        field1Label ti `join` labelPredField2Rows p ti rs `canFlowTo` l
      )
      ? unjoinCanFlowTo (tableLabel ti) (labelPredRow p ti r) l 
      ?   joinCanFlowTo (tableLabel ti) (labelPredRow p ti r) l 
      ? unjoinCanFlowTo ((tableLabel ti `join` labelPredRow p ti r)) (field1Label ti `join` labelPredField2Rows p ti rs) l 
      ?   joinCanFlowTo ((tableLabel ti `join` labelPredRow p ti r)) (field1Label ti `join` labelPredField2Rows p ti rs) l 
  ==. ((tableLabel ti `join` labelPredRow p ti r) `join` field1Label ti `join` labelPredField2Rows p ti rs) `canFlowTo` l 
  ==. field1Label ti `join` labelPredField2Rows p ti (r:rs) `canFlowTo` l 
  *** QED 





 
