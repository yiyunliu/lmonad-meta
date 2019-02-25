{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"  @-}
{-@ infix :  @-}
module LabelPredImplies where

import Labels 
import Predicates 
import Prelude hiding (Maybe(..), fromJust, isJust)
import Programs 

import ProofCombinators 


labelPredImplies :: (Label l, Eq l) => l -> Pred -> Table l -> Proof
{-@ ple labelPredImplies @-}
{-@ labelPredImplies 
  :: Label l 
  => l:l 
  -> p:Pred 
  -> t:Table l
  -> { canFlowTo (labelPred p t) l => 
       ( (pDep1 p=> canFlowTo (field1Label (tableInfo t)) l) && 
         canFlowTo (tableLabel (tableInfo t)) l )} @-}
labelPredImplies l p t@(Table ti [])
  | labelPred p t `canFlowTo` l 
  = tableLabelDep l p ti []

 

labelPredImplies l p t@(Table ti (r:rs))
  | labelPred p t `canFlowTo` l, pDep2 p 
  =   labelPred p (Table ti (r:rs)) 
  ==. field1Label ti `join` labelPredField2Rows p ti (r:rs) 
  ==. (tableLabel ti `join` labelPredRow p ti r) `join` field1Label ti `join` labelPredField2Rows p ti rs
  ==. (tableLabel ti `join` (field1Label ti `join` makeValLabel ti (rowField1 r))) `join` field1Label ti `join` labelPredField2Rows p ti rs
  *** QED 
  ? tableLabelDep l p ti rs
  ? joinCanFlowTo (tableLabel ti) (labelPredRow p ti r)  l 
  ? joinCanFlowTo (tableLabel ti `join` labelPredRow p ti r) (field1Label ti `join` labelPredField2Rows p ti rs) l 
  ? joinCanFlowTo (field1Label ti) (makeValLabel ti (rowField1 r)) l 

labelPredImplies l p t@(Table ti (r:rs))
  | labelPred p t `canFlowTo` l 
  =   labelPred p (Table ti (r:rs)) 
  ==. field1Label ti `join` labelPredField2Rows p ti (r:rs) 
  ==. (tableLabel ti `join` labelPredRow p ti r) `join` field1Label ti `join` labelPredField2Rows p ti rs
  ==. (tableLabel ti `join` field1Label ti) `join` field1Label ti `join` labelPredField2Rows p ti rs
  *** QED 
  ? tableLabelDep l p ti rs
  ? joinCanFlowTo (tableLabel ti) (field1Label ti) l 
  ? joinCanFlowTo (tableLabel ti `join` field1Label ti) (field1Label ti `join` labelPredField2Rows p ti rs) l 



labelPredImplies l p t 
  = () 


tableLabelDep :: (Eq l, Label l) => l -> Pred -> TInfo l -> [Row l] -> Proof 
{-@ tableLabelDep 
  :: (Eq l, Label l) 
  => l:l 
  -> p:Pred 
  -> ti:TInfo l 
  -> rs:[Row l] 
  -> { (canFlowTo (join (field1Label ti) (labelPredField2Rows p ti rs)) l) => (canFlowTo (tableLabel ti) l) } @-}
tableLabelDep l p ti rs 
  | not (pDep1 p)      
  =   field1Label ti `join` labelPredField2Rows p ti rs `canFlowTo` l 
  ==. tableLabel ti         `canFlowTo` l 
  *** QED  

tableLabelDep l p ti [] 
  =   field1Label ti `join` labelPredField2Rows p ti [] `canFlowTo` l 
  ==. (tableLabel ti `join` field1Label ti) `canFlowTo` l 
      ? joinCanFlowTo (tableLabel ti) (field1Label ti) l 
  *** QED  
tableLabelDep l p ti (r:rs) 
  =   field1Label ti `join` labelPredField2Rows p ti (r:rs) `canFlowTo` l 
  =>. ((tableLabel ti `join` labelPredRow p ti r) `join` field1Label ti `join` labelPredField2Rows p ti rs) `canFlowTo` l 
       ? joinCanFlowTo (tableLabel ti) (labelPredRow p ti r) l 
       ? joinCanFlowTo (tableLabel ti `join` labelPredRow p ti r) (field1Label ti `join` labelPredField2Rows p ti rs) l 
  =>. (tableLabel ti `canFlowTo` l 
      && 
      labelPredRow p ti r `canFlowTo` l  
     && 
      field1Label ti `join` labelPredField2Rows p ti rs `canFlowTo` l 
      )
      ? tableLabelDep l p ti rs 
  =>. tableLabel ti         `canFlowTo` l 
  *** QED 
