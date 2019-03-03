{-@ LIQUID "--reflection"  @-}

module Simulations.UpdateNothingJustHelper where

import ProofCombinators
import Labels 
import Programs 
import Predicates 

import Simulations.DeleteHelpers
import Idempotence
import LabelPredImplies
import EraseTableAnyNothingJust
import LookupTableErase 
import LabelPredEraseEqual
import LabelUpdateCheck
import Simulations.Terms 
import Simulations.UpdateNothingJust
import LabelUpdateCheckNothingJust
import Simulations.UpdateOneNothingJust

import Prelude hiding (Maybe(..), fromJust, isJust)

{-@ simulationsUpdateNJF1Flow ::
  (Eq l, Label l)
  => l:l
  -> lc:{l | canFlowTo lc l}
  -> db: DB l
  -> n:{TName | isJust(lookupTable n db)}
  -> p:Pred
  -> l2:l
  -> v2: SDBTerm l
  -> t: {Table l | (Just t == lookupTable n db) &&
                   (canFlowTo (tableLabel (tableInfo t)) l) &&
                   (canFlowTo (field1Label (tableInfo t)) l) &&
                   (not (canFlowTo (lfTable p t) l)) &&
                   (not (updateLabelCheckNothingJust lc t p l2 v2))}
  -> εt:{Table l | (Just εt == lookupTable n (εDB l db)) && (tableInfo εt == tableInfo t) &&
                   (updateLabelCheckNothingJust lc εt p l2 (if (canFlowTo l2 l) then (εTerm l v2) else THole)) &&
                   (lfTable p t == lfTable p εt) &&
                   (not (canFlowTo (lfTable p εt) l))}
  -> { εDB l (updateDBNothingJust (εDB l db) n p (if (canFlowTo l2 l) then v2 else THole)) == εDB l db }
@-}

simulationsUpdateNJF1Flow :: (Eq l, Label l) =>
  l -> l -> DB l -> TName -> Pred -> l -> Term l -> Table l -> Table l -> Proof
simulationsUpdateNJF1Flow l lc [] n p l2 v2 _ _
  =   εDB l []
  ==. εDB l (updateDBNothingJust (εDB l []) n p εv2) 
  *** QED 
  where
    εv2 = if (canFlowTo l2 l) then v2 else THole


simulationsUpdateNJF1Flow l lc ((Pair n' t@(Table ti rs)):ts) n p l2 v2 t' εt'
  -- stolen from Update.hs
  | n /= n' 
  =  (Just t' ==. 
      lookupTable n ((Pair n' (Table ti rs)):ts) ==. 
      Just t 
      *** QED)
  &&& (Just εt' ==. 
      lookupTable n (εDB l ((Pair n' (Table ti rs)):ts)) ==. 
      lookupTable n (Pair n' (εTable l (Table ti rs)):εDB l ts) ==. 
      Just (εTable l t) 
      *** QED)
  &&& (εDB l (updateDBNothingJust (εDB l ((Pair n' t):ts)) n p εv2)
  ==.  εDB l (updateDBNothingJust ((Pair n' (εTable l t)):εDB l ts) n p εv2)
  ==.  εDB l (Pair n' (εTable l (Table ti rs)): updateDBNothingJust (εDB l ts) n p εv2)
  ==.  Pair n' (εTable l (εTable l (Table ti rs))):εDB l (updateDBNothingJust (εDB l ts) n p εv2)
      ? simulationsUpdateNJF1Flow l lc ts n  p l2 v2 t' εt'
      ? εTableIdempotent l (Table ti rs)

  ==. Pair n' (εTable l (Table ti rs)):εDB l ts
  ==. εDB l (Pair n' (Table ti rs):ts)
  *** QED)

  -- stolen code ends here
  
  | otherwise
  =   εDB l (updateDBNothingJust (εDB l ((Pair n' t):ts)) n p εv2)
      ? assert (v2 == εTerm l v2)
      ? (Just t' ==. 
      lookupTable n ((Pair n' (Table ti rs)):ts) ==. 
      Just t 
      *** QED)
      ? (Just εt' ==. 
      lookupTable n (εDB l ((Pair n' (Table ti rs)):ts)) ==. 
      lookupTable n (Pair n' (εTable l (Table ti rs)):εDB l ts) ==. 
      Just (εTable l t) 
      *** QED)
      -- ? ( updateLabelCheckNothingJust lc t p l2 v2
      -- ==! updateRowsCheckNothingJust lc (lfTable p t) ti p l2 v2 rs
      -- *** QED)
      ? assert (updateLabelCheckNothingJust lc εt' p l2 εv2)
      ? ( updateLabelCheckNothingJust lc εt' p l2 εv2
      ==! updateRowsCheckNothingJust lc (lfTable p εt') ti p l2 εv2 (εRows l ti rs)
      *** QED)
  ==. εDB l (updateDBNothingJust ((Pair n' (εTable l t)):εDB l ts) n p εv2)
  ==. εDB l (updateDBNothingJust ((Pair n' (εTable l (Table ti rs))):εDB l ts) n p εv2)
  ==. εDB l (updateDBNothingJust ((Pair n' (Table ti (εRows l ti rs))):εDB l ts) n p εv2)
  ==. εDB l (Pair n' (Table ti (updateRowsNothingJust p εv2 (εRows l ti rs))):εDB l ts) 
  ==. Pair n' (εTable l (Table ti (updateRowsNothingJust p εv2 (εRows l ti rs)))):εDB l (εDB l ts)
  ==. Pair n' (Table ti (εRows l ti (updateRowsNothingJust p εv2 (εRows l ti rs)))):εDB l (εDB l ts)

      ? εDBIdempotent l ts
      ? assert (updateRowsCheckNothingJust lc (lfTable p εt') ti p l2 (if (canFlowTo l2 l) then v2 else THole) (εRows l ti rs))
      ? simulationsUpdateRowsNJF1Flow l lc (lfTable p εt') ti p l2 v2 rs

  
  ==. Pair n' (Table ti (εRows l ti rs)):εDB l ts 
  ==. Pair n' (εTable l (Table ti rs)):εDB l ts 
  ==. εDB l (Pair n' (Table ti rs):ts)


  *** QED
  where εv2 = if (canFlowTo l2 l) then v2 else THole
        lφ  = lawFlowReflexivity (lfRows p ti rs) `cast` lfTable p (Table ti rs)
        εlφ = lawFlowReflexivity (lfRows p ti (εRows l ti rs)) `cast` lfTable p (Table ti (εRows l ti rs))




{-@ simulationsUpdateRowsNJF1Flow
  :: (Label l, Eq l)
  => l:l
  -> lc:{l | canFlowTo lc l}
  -> lf:{l |not (canFlowTo lf l)}
  -> ti:{TInfo l | canFlowTo (tableLabel ti) l}
  -> p:Pred
  -> l2:l 
  -> v2: SDBTerm l 
  -> rs:{[Row l] | updateRowsCheckNothingJust lc lf ti p l2 (if (canFlowTo l2 l) then v2 else THole) (εRows l ti rs)} 
  -> { (εRows l ti (updateRowsNothingJust p (if (canFlowTo l2 l) then v2 else THole) (εRows l ti rs)) = εRows l ti rs) } 
   / [len rs] @-}
simulationsUpdateRowsNJF1Flow
  :: (Label l, Eq l)
  => l -> l -> l -> TInfo l -> Pred -> l -> Term l -> [Row l] -> Proof
simulationsUpdateRowsNJF1Flow l lc lf ti p l2 v2 [] 
  =   εRows l ti (updateRowsNothingJust p εv2 (εRows l ti []))
  ==. εRows l ti (updateRowsNothingJust p εv2 [])
  ==. εRows l ti []
  *** QED   
  where
    εv2 = if (canFlowTo l2 l) then v2 else THole

simulationsUpdateRowsNJF1Flow l lc lf ti p l2 v2 (r:rs) 
  =   εRows l ti (updateRowsNothingJust p εv2 (εRows l ti (r:rs)))
  ==. εRows l ti (updateRowsNothingJust p εv2 (εRow l ti r:εRows l ti rs))
  ==. εRows l ti (updateRowNothingJust p εv2 (εRow l ti r):updateRowsNothingJust p εv2 (εRows l ti rs))
  ==. εRow l ti (updateRowNothingJust p εv2 (εRow l ti r)):εRows l ti (updateRowsNothingJust p εv2 (εRows l ti rs))
      ? ( updateRowsCheckNothingJust lc lf ti p l2 εv2 (εRows l ti (r:rs))
      ==. updateRowsCheckNothingJust lc lf ti p l2 εv2 (εRow l ti r : εRows l ti rs)
      ==. (updateRowCheckNothingJust lc lf ti p l2 εv2 (εRow l ti r) &&
        updateRowsCheckNothingJust lc lf ti p l2 εv2 (εRows l ti rs))
      *** QED)
      ? simulationsUpdateRowsNJF1Flow l lc lf ti p l2 v2 rs
      ? simulationsUpdateRowNJF1Flow l lc lf ti p l2 v2 r
  ==. εRow  l ti r:εRows l ti rs
  ==. εRows l ti (r:rs)
  *** QED  
  where
    εv2 = if (canFlowTo l2 l) then v2 else THole

{-@ simulationsUpdateRowNJF1Flow
  :: (Label l, Eq l)
  => l:l
  -> lc:{l | canFlowTo lc l}
  -> lf:{l | not (canFlowTo lf l)}
  -> ti:{TInfo l | canFlowTo (tableLabel ti) l}
  -> p:Pred
  -> l2:l 
  -> v2: SDBTerm l 
  -> r:{Row l | updateRowCheckNothingJust lc lf ti p l2 (if (canFlowTo l2 l) then v2 else THole) (εRow l ti r) } 
  -> { εRow l ti (updateRowNothingJust p (if (canFlowTo l2 l) then v2 else THole) (εRow l ti r)) == εRow  l ti r  } 
@-}
simulationsUpdateRowNJF1Flow
  :: (Label l, Eq l)
  => l -> l -> l -> TInfo l -> Pred -> l -> Term l -> Row l -> Proof
simulationsUpdateRowNJF1Flow l lc lf ti p l2 v2 r@(Row k o1 o2)
  | not (field1Label ti `canFlowTo` l)
  -- contradiction
  =   lawFlowTransitivity (field1Label ti) (tableLabel ti) l
  | makeValLabel ti o1 `canFlowTo` l, εep
  =   εRow l ti (updateRowNothingJust p εv2 (εRow l ti r))
  ==. εRow l ti (if εep then Row k o1 v2 else (εRow l ti r))
  ==. εRow l ti (Row k o1 v2)
      ? assert (o1 == εTerm l o1)
      ? assert (o2 == εTerm l o2)
      ? ( εr
      ==! εRow l ti (Row k o1 o2)
      ==! Row k (εTerm l o1) (εTerm l o2)
      ==! Row k o1 o2
      *** QED)
      ? ( updateRowCheckNothingJust lc lf ti p l2 εv2 εr
      ==! updateRowCheckNothingJust lc lf ti p l2 εv2 (Row k o1 o2)
      ==! (if evalPred p (Row k o1 o2) then updateRowLabel2 lc lf ti p (field1Label ti) o1 l2 εv2 (Row k o1 o2) else True)
      ==! updateRowLabel2 lc lf ti p (field1Label ti) o1 l2 εv2 εr
      ==! ((((l2 `join` lc) `join` lf) `canFlowTo` makeValLabel ti o1))
      *** QED)
      ? joinCanFlowTo (l2 `join` lc) lf (makeValLabel ti o1)
      ? lawFlowTransitivity lf (makeValLabel ti o1) l

  ==. εRow l ti (Row k o1 o2)
  ==. εRow l ti r
  *** QED

  -- contradiction
  | makeValLabel ti o1 `canFlowTo` l
  =   εRow l ti r
    ? εRowIdempotent l ti r
  ==. εRow l ti εr
  ==. εRow l ti (if εep then Row k o1 v2 else εr)
  ==. εRow l ti (updateRowNothingJust p εv2 r)
  ==. εRow l ti (updateRowNothingJust p εv2 εr)
  *** QED
  -- erased
  | εep
  =   εRow l ti (updateRowNothingJust p εv2 εr)
  ==. εRow l ti (updateRowNothingJust p εv2 (Row k o1 THole))
      ? assert (o1 == εTerm l o1)
      ? assert (THole == εTerm l THole)
  ==. εRow l ti (if evalPred p (Row k o1 THole) then (Row k o1 εv2)  else (Row k o1 THole))
  ==. εRow l ti (Row k o1 εv2)
  ==. Row k o1 THole
  ==. εRow l ti r
  *** QED
  | otherwise
  =   εRow l ti (updateRowNothingJust p εv2 εr)
  ==. εRow l ti (updateRowNothingJust p εv2 (Row k o1 THole))
      ? assert (o1 == εTerm l o1)
      ? assert (THole == εTerm l THole)
  ==. εRow l ti (if evalPred p (Row k o1 THole) then (Row k o1 εv2)  else (Row k o1 THole))
  ==. εRow l ti (Row k o1 THole)
  ==. Row k o1 THole
  ==. εRow l ti r
  *** QED  
  where 
    εv2 = if (canFlowTo l2 l) then v2 else THole
    εr  = εRow l ti r
    εep  = evalPred p εr



 
{-@ simulationsUpdateNJF1Flow' ::
  (Eq l, Label l)
  => l:l
  -> lc:{l | canFlowTo lc l}
  -> db: DB l
  -> n:{TName | isJust(lookupTable n db)}
  -> p:Pred
  -> l2:l
  -> v2: SDBTerm l
  -> t: {Table l | (Just t == lookupTable n db) &&
                   (canFlowTo (tableLabel (tableInfo t)) l) &&
                   (canFlowTo (field1Label (tableInfo t)) l) &&
                   (not (canFlowTo (lfTable p t) l)) &&
                   (not (updateLabelCheckNothingJust lc t p l2 v2))}
  -> εt:{Table l | (Just εt == lookupTable n (εDB l db)) && (tableInfo εt == tableInfo t) &&
                   (updateLabelCheckNothingJust lc t p l2 v2) &&
                   (lfTable p t == lfTable p εt) &&
                   (not (canFlowTo (lfTable p t) l))}
  -> { εDB l db == εDB l (updateDBNothingJust db n p v2) }
@-}

simulationsUpdateNJF1Flow' :: (Eq l, Label l) =>
  l -> l -> DB l -> TName -> Pred -> l -> Term l -> Table l -> Table l -> Proof
simulationsUpdateNJF1Flow' l lc [] n p l2 v2 _ _
  =   εDB l []
  ==. εDB l (updateDBNothingJust [] n p v2) 
  *** QED 
  -- where
  --   εv2 = if (canFlowTo l2 l) then v2 else THole


simulationsUpdateNJF1Flow' l lc ((Pair n' t@(Table ti rs)):ts) n p l2 v2 t' εt'
  -- stolen from Update.hs
  | n /= n' 
  =  (Just t' ==. 
      lookupTable n ((Pair n' (Table ti rs)):ts) ==. 
      Just t 
      *** QED)
  &&& (Just εt' ==. 
      lookupTable n (εDB l ((Pair n' (Table ti rs)):ts)) ==. 
      lookupTable n (Pair n' (εTable l (Table ti rs)):εDB l ts) ==. 
      Just (εTable l t) 
      *** QED)
  &&& (εDB l (updateDBNothingJust ((Pair n' t):ts) n p v2)
  -- ==.  εDB l (updateDBNothingJust ((Pair n' (εTable l t)):εDB l ts) n p v2)
  ==.  εDB l (Pair n' (Table ti rs): updateDBNothingJust ts n p v2)
  ==.  Pair n' (εTable l (Table ti rs)):εDB l (updateDBNothingJust (εDB l ts) n p v2)
      ? simulationsUpdateNJF1Flow' l lc ts n  p l2 v2 t' εt'
      -- ? εTableIdempotent l (Table ti rs)

  ==. Pair n' (εTable l (Table ti rs)):εDB l ts
  ==. εDB l (Pair n' (Table ti rs):ts)
  *** QED)

  -- stolen code ends here
  
  | otherwise
  =   εDB l (updateDBNothingJust ((Pair n' t):ts) n p v2)
      ? assert (v2 == εTerm l v2)
      ? (Just t' ==. 
      lookupTable n ((Pair n' (Table ti rs)):ts) ==. 
      Just t 
      *** QED)
      ? (Just εt' ==. 
      lookupTable n (εDB l ((Pair n' (Table ti rs)):ts)) ==. 
      lookupTable n (Pair n' (εTable l (Table ti rs)):εDB l ts) ==. 
      Just (εTable l t) 
      *** QED)
      -- ? ( updateLabelCheckNothingJust lc t p l2 v2
      -- ==! updateRowsCheckNothingJust lc (lfTable p t) ti p l2 v2 rs
      -- *** QED)
      ? assert (updateLabelCheckNothingJust lc t' p l2 v2)
      ? ( updateLabelCheckNothingJust lc t' p l2 v2
      ==! updateRowsCheckNothingJust lc (lfTable p t') ti p l2 v2 (εRows l ti rs)
      *** QED)
  -- ==. εDB l (updateDBNothingJust ((Pair n' (εTable l t)):εDB l ts) n p v2)
  -- ==. εDB l (updateDBNothingJust ((Pair n' (εTable l (Table ti rs))):εDB l ts) n p εv2)
  -- ==. εDB l (updateDBNothingJust ((Pair n' (Table ti (εRows l ti rs))):εDB l ts) n p εv2)
  ==. εDB l (Pair n' (Table ti (updateRowsNothingJust p v2 rs)):ts) 
  ==. Pair n' (εTable l (Table ti (updateRowsNothingJust p v2 rs))):εDB l ts
  ==. Pair n' (Table ti (εRows l ti (updateRowsNothingJust p v2 rs))):εDB l ts

      ? assert (updateRowsCheckNothingJust lc (lfTable p t') ti p l2 v2 rs)
      ? simulationsUpdateRowsNJF1Flow' l lc (lfTable p t') ti p l2 v2 rs

  
  ==. Pair n' (Table ti (εRows l ti rs)):εDB l ts 
  ==. Pair n' (εTable l (Table ti rs)):εDB l ts 
  ==. εDB l (Pair n' (Table ti rs):ts)


  *** QED





{-@ simulationsUpdateRowsNJF1Flow'
  :: (Label l, Eq l)
  => l:l
  -> lc:{l | canFlowTo lc l}
  -> lf:{l |not (canFlowTo lf l)}
  -> ti:{TInfo l | canFlowTo (tableLabel ti) l}
  -> p:Pred
  -> l2:l 
  -> v2: SDBTerm l 
  -> rs:{[Row l] | updateRowsCheckNothingJust lc lf ti p l2 v2 rs} 
  -> { (εRows l ti (updateRowsNothingJust p v2 rs) == εRows l ti rs) } 
   / [len rs] @-}
simulationsUpdateRowsNJF1Flow'
  :: (Label l, Eq l)
  => l -> l -> l -> TInfo l -> Pred -> l -> Term l -> [Row l] -> Proof
simulationsUpdateRowsNJF1Flow' l lc lf ti p l2 v2 [] 
  =   εRows l ti (updateRowsNothingJust p v2 (εRows l ti []))
  ==. εRows l ti (updateRowsNothingJust p v2 [])
  ==. εRows l ti []
  *** QED   
  where
    εv2 = if (canFlowTo l2 l) then v2 else THole

simulationsUpdateRowsNJF1Flow' l lc lf ti p l2 v2 (r:rs) 
  =   εRows l ti (updateRowsNothingJust p v2 (r:rs))
  ==. εRows l ti (updateRowNothingJust p v2 r:updateRowsNothingJust p v2 rs)
  ==. εRow l ti (updateRowNothingJust p v2 r):εRows l ti (updateRowsNothingJust p v2 rs)
      ? ( updateRowsCheckNothingJust lc lf ti p l2 v2 (r:rs)
      ==. (updateRowCheckNothingJust lc lf ti p l2 v2 r &&
        updateRowsCheckNothingJust lc lf ti p l2 v2 rs)
      *** QED)
      ? simulationsUpdateRowsNJF1Flow' l lc lf ti p l2 v2 rs
      ? simulationsUpdateRowNJF1Flow' l lc lf ti p l2 v2 r
  ==. εRow  l ti r:εRows l ti rs
  ==. εRows l ti (r:rs)
  *** QED  
  where
    εv2 = if (canFlowTo l2 l) then v2 else THole

{-@ simulationsUpdateRowNJF1Flow'
  :: (Label l, Eq l)
  => l:l
  -> lc:{l | canFlowTo lc l}
  -> lf:{l | not (canFlowTo lf l)}
  -> ti:{TInfo l | canFlowTo (tableLabel ti) l}
  -> p:Pred
  -> l2:l 
  -> v2: SDBTerm l 
  -> r:{Row l | updateRowCheckNothingJust lc lf ti p l2 v2 r } 
  -> { εRow l ti (updateRowNothingJust p v2 r) == εRow  l ti r  } 
@-}
simulationsUpdateRowNJF1Flow'
  :: (Label l, Eq l)
  => l -> l -> l -> TInfo l -> Pred -> l -> Term l -> Row l -> Proof
simulationsUpdateRowNJF1Flow' l lc lf ti p l2 v2 r@(Row k o1 o2)
  | not (field1Label ti `canFlowTo` l)
  -- contradiction
  =   lawFlowTransitivity (field1Label ti) (tableLabel ti) l
  | makeValLabel ti o1 `canFlowTo` l, evalPred p r
  =   εRow l ti (updateRowNothingJust p v2 r)
  ==. εRow l ti (if evalPred p r then Row k o1 v2 else r)
  ==. εRow l ti (Row k o1 v2)
      ? assert (o1 == εTerm l o1)
      ? assert (o2 == εTerm l o2)
      ? ( updateRowCheckNothingJust lc lf ti p l2 v2 r
      ==! updateRowCheckNothingJust lc lf ti p l2 v2 (Row k o1 o2)
      ==! (if evalPred p (Row k o1 o2) then updateRowLabel2 lc lf ti p (field1Label ti) o1 l2 v2 (Row k o1 o2) else True)
      ==! updateRowLabel2 lc lf ti p (field1Label ti) o1 l2 v2 r
      ==! ((((l2 `join` lc) `join` lf) `canFlowTo` makeValLabel ti o1))
      *** QED)
      ? joinCanFlowTo (l2 `join` lc) lf (makeValLabel ti o1)
      ? lawFlowTransitivity lf (makeValLabel ti o1) l

  ==. εRow l ti (Row k o1 o2)
  ==. εRow l ti r
  *** QED

  -- contradiction
  | makeValLabel ti o1 `canFlowTo` l
  =   εRow l ti r
  ==. εRow l ti (if evalPred p r then Row k o1 v2 else r)
  ==. εRow l ti (updateRowNothingJust p v2 r)
  ==. εRow l ti (updateRowNothingJust p v2 r)
  *** QED
  -- erased
  | evalPred p r
  =   εRow l ti (updateRowNothingJust p v2 r)
      ? assert (o1 == εTerm l o1)
      ? assert (THole == εTerm l THole)
  ==. εRow l ti (if evalPred p (Row k o1 v2) then (Row k o1 o2)  else (Row k o1 o2))
  ==. εRow l ti (Row k o1 v2)
  ==. Row k o1 THole
  ==. εRow l ti r
  *** QED
  | otherwise
  =   εRow l ti (updateRowNothingJust p v2 r)
      ? assert (o1 == εTerm l o1)
      ? assert (THole == εTerm l THole)
  ==. εRow l ti (if evalPred p (Row k o1 v2) then (Row k o1 o2)  else (Row k o1 o2))
  ==. εRow l ti (Row k o1 o2)
  *** QED  

