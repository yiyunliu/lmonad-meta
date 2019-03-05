{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple" @-}
module SemanticEq where
import ProofCombinators
import Labels
import Predicates
import Programs
import Prelude hiding (Maybe(..), fromJust, isJust)


{-@ reflect labelPred @-}
labelPred :: (Eq l, Label l) => Pred -> Table l -> l
labelPred p (Table ti rs)
  | pDep2 p
  = field1Label ti `join` labelPredField2Rows p ti rs
  | pDep1 p
  = field1Label ti
  | otherwise
  = bot

{-@ reflect labelPredField2Rows @-}
labelPredField2Rows :: (Eq l, Label l) => Pred -> TInfo l -> [Row l] -> l
labelPredField2Rows _ _ []     = bot
labelPredField2Rows p ti (r:rs) = labelPredField2Row p ti r `join` labelPredField2Rows p ti rs

{-@ reflect labelPredField2Row @-}
labelPredField2Row :: (Eq l, Label l) => Pred -> TInfo l -> Row l -> l
labelPredField2Row _ ti r = makeValLabel ti (rowField1 r)

{-@ reflect updateLabelCheckNothingJust' @-}
updateLabelCheckNothingJust' :: (Label l, Eq l) => l -> Table l -> Pred -> l -> Term l -> Bool 
updateLabelCheckNothingJust' lc t@(Table ti rs) p l2 v2  
  = updateRowsCheckNothingJust' lc (labelPred p t) ti p l2 v2 rs 

{-@ reflect updateRowsCheckNothingJust' @-}
updateRowsCheckNothingJust' :: (Label l, Eq l) => l -> l -> TInfo l -> Pred -> l -> Term l -> [Row l] -> Bool 
{-@ updateRowsCheckNothingJust' :: (Label l, Eq l) => l -> l -> TInfo l -> Pred -> l -> Term l -> rs:[Row l] -> Bool / [len rs] @-}
-- todo: restructure it so v1 is examined in updateRowCheckNothingJust
updateRowsCheckNothingJust' _ _ _ _ _ _ []            = True 
updateRowsCheckNothingJust' lc lφ ti p l2 v2 (r:rs) =
  updateRowCheckNothingJust' lc lφ ti p l2 v2 r &&
  updateRowsCheckNothingJust' lc lφ ti p l2 v2 rs

{-@ reflect updateRowCheckNothingJust' @-}
updateRowCheckNothingJust' :: (Label l, Eq l) => l -> l -> TInfo l -> Pred -> l -> Term l -> Row l -> Bool 
updateRowCheckNothingJust' lc lφ ti p l2 v2 r@(Row _ v1 _)
  =  if evalPred p r then updateRowLabel2' lc lφ ti p (field1Label ti) v1 l2 v2 r else True



{-@ reflect updateRowLabel2' @-}
updateRowLabel2'
  :: (Label l, Eq l)   
  => l -> l -> TInfo l -> Pred -> l -> Term l -> l -> Term l -> Row l 
  -> Bool 
updateRowLabel2' lc lφ ti p l1 v1 l2 v2 r -- @(Row _ o1 o2)   
  = if True {- o2 /= v2-}  then 
       (((l2 `join` lc) `join` lφ) `canFlowTo` makeValLabel ti v1) else True  


{-@ updateLabelCheckOldNewEq :: 
   (Label l, Eq l)
=> lc:l
-> t:Table l
-> p:Pred
-> l2:l
-> v2:Term l
-> {updateLabelCheckNothingJust lc t p l2 v2 == updateLabelCheckNothingJust' lc t p l2 v2}
@-}

updateLabelCheckOldNewEq :: (Label l, Eq l) => l -> Table l -> Pred -> l -> Term l -> Proof
updateLabelCheckOldNewEq lc t@(Table ti rs) p l2 v2 
  =   updateRowsCheckOldNewEq lc (lfTable p t) (labelPred p t) ti p l2 v2 rs
    ? 
  
