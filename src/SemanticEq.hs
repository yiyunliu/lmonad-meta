{-@ LIQUID "--reflection"  @-}
module SemanticEq where
import Programs
import ProofCombinators
import Labels
import Predicates
import Prelude hiding (Maybe(..), fromJust, isJust)
-- YL:
-- update nothing just
-- I'll only show label check and lc' are equal

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

labelPredField2Row :: (Eq l, Label l) => Pred -> TInfo l -> Row l -> l
labelPredField2Row _ ti r = makeValLabel ti (rowField1 r)

{-@ reflect updateLabelCheckNJAlt @-}
updateLabelCheckNJAlt :: (Label l, Eq l) => l -> Table l -> Pred -> l -> Term l -> Bool 
updateLabelCheckNJAlt lc t@(Table ti rs) p l2 v2  
  = updateRowsCheckNothingJust lc (labelPred p t) ti p l2 v2 rs 

-- {-@ reflect updateRowsCheckNJAlt @-}
-- updateRowsCheckNJAlt :: (Label l, Eq l) => l -> l -> TInfo l -> Pred -> l -> Term l -> [Row l] -> Bool 
-- {-@ updateRowsCheckNJAlt :: (Label l, Eq l) => l -> l -> TInfo l -> Pred -> l -> Term l -> rs:[Row l] -> Bool / [len rs] @-}
-- -- todo: restructure it so v1 is examined in updateRowCheckNJAlt
-- updateRowsCheckNJAlt _ _ _ _ _ _ []            = True 
-- updateRowsCheckNJAlt lc lφ ti p l2 v2 (r:rs) =
--   updateRowCheckNJAlt lc lφ ti p l2 v2 r &&
--   updateRowsCheckNJAlt lc lφ ti p l2 v2 rs

-- {-@ reflect updateRowCheckNJAlt @-}
-- updateRowCheckNJAlt :: (Label l, Eq l) => l -> l -> TInfo l -> Pred -> l -> Term l -> Row l -> Bool 
-- updateRowCheckNJAlt lc lφ ti p l2 v2 r@(Row _ v1 _)
--   | evalPred p r
--   =  updateRowLabel2 lc lφ ti p (field1Label ti) v1 l2 v2 r
--   | otherwise
--   = True

{-@ reflect labelPredRowsAlt @-}
labelPredRowsAlt :: (Eq l, Label l) => Pred -> TInfo l -> [Row l] -> l
labelPredRowsAlt p ti rs 
  | pDep2 p
  = field1Label ti `join`labelPredField2Rows p ti rs
  | pDep1 p
  = field1Label ti
  | otherwise
  = bot


{-@ ple updateLabelCheckNJEq @-}
{-@ updateLabelCheckNJEq :: (Label l, Eq l)
  => lc:l
  -> t:Table l
  -> p:Pred
  -> l2:l
  -> v2:Term l
  -> {updateLabelCheckNJAlt lc t p l2 v2 == updateLabelCheckNothingJust lc t p l2 v2} @-}
updateLabelCheckNJEq :: (Eq l, Label l) => l -> Table l -> Pred -> l -> Term l -> Proof
updateLabelCheckNJEq lc t@(Table ti rs) p l2 v2 
  =   updateLabelCheckNJAlt lc t p l2 v2
  ==. updateRowsCheckNothingJust lc (labelPred p t) ti p l2 v2 rs
  ==. updateRowsCheckNothingJust lc (labelPredRowsAlt p ti rs) ti p l2 v2 rs
      -- todo
      ? updateRowsCheckNJEq lc p ti rs l2 v2
  ==. updateRowsCheckNothingJust lc (lfRows p ti rs) ti p l2 v2 rs
  ==. updateRowsCheckNothingJust lc (lfTable p t) ti p l2 v2 rs
  ==. updateLabelCheckNothingJust lc t p l2 v2
  *** QED

{-@ updateRowsCheckNJEq :: (Label l, Eq l)
  => lc:l
  -> p:Pred
  -> ti:TInfo l
  -> rs:[Row l]
  -> l2:l
  -> v2:Term l
  -> {updateRowsCheckNothingJust lc (labelPredRowsAlt p ti rs) ti p l2 v2 rs ==
      updateRowsCheckNothingJust lc (lfRows p ti rs) ti p l2 v2 rs} @-}

updateRowsCheckNJEq :: (Label l, Eq l) =>
  l -> Pred -> TInfo l -> [Row l] -> l -> Term l -> Proof

updateRowsCheckNJEq lc p ti [] l2 v2
  =   updateRowsCheckNothingJust lc (labelPredRowsAlt p ti []) ti p l2 v2 []
  ==. True
  ==. updateRowsCheckNothingJust lc (lfRows p ti []) ti p l2 v2 []
  *** QED
updateRowsCheckNJEq lc p ti (r:rs) l2 v2
  =   updateRowsCheckNothingJust lc (labelPredRowsAlt p ti (r:rs)) ti p l2 v2 (r:rs)
  -- actually they are not equal
  ==. (updateRowCheckNothingJust lc (lfRow p ti r `join` lfRows p ti rs ) ti p l2 v2 r &&
      updateRowsCheckNothingJust lc (lfRow p ti r `join` lfRows p ti rs ) ti p l2 v2 rs)
  ==. updateRowsCheckNothingJust lc (lfRow p ti r `join` lfRows p ti rs ) ti p l2 v2 (r:rs)
  ==. updateRowsCheckNothingJust lc (lfRows p ti (r:rs)) ti p l2 v2 (r:rs)
  *** QED
  
  
