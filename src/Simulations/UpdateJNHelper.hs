{-@ LIQUID "--reflection"  @-}

module Simulations.UpdateJNHelper where

import ProofCombinators
import Labels 
import Programs 
import Predicates 

import Idempotence

import Prelude hiding (Maybe(..), fromJust, isJust)

{-@ simulationsUpdateJNF1Flow ::
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
                   (not (updateLabelCheckJN lc t p l2 v2))}
  -> εt:{Table l | (Just εt == lookupTable n (εDB l db)) && (tableInfo εt == tableInfo t) &&
                   (updateLabelCheckJN lc εt p l2 (if (canFlowTo l2 l) then (εTerm l v2) else THole)) &&
                   (lfTable p t == lfTable p εt) &&
                   (not (canFlowTo (lfTable p εt) l))}
  -> { εDB l (updateDBJN (εDB l db) n p (if (canFlowTo l2 l) then v2 else THole)) == εDB l db }
@-}

simulationsUpdateJNF1Flow :: (Eq l, Label l) =>
  l -> l -> DB l -> TName -> Pred -> l -> Term l -> Table l -> Table l -> Proof
simulationsUpdateJNF1Flow l lc [] n p l2 v2 _ _
  =   εDB l []
  ==. εDB l (updateDBJN (εDB l []) n p εv2) 
  *** QED 
  where
    εv2 = if (canFlowTo l2 l) then v2 else THole


simulationsUpdateJNF1Flow l lc ((Pair n' t@(Table ti rs)):ts) n p l2 v2 t' εt'
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
  &&& (εDB l (updateDBJN (εDB l ((Pair n' t):ts)) n p εv2)
  ==.  εDB l (updateDBJN ((Pair n' (εTable l t)):εDB l ts) n p εv2)
  ==.  εDB l (Pair n' (εTable l (Table ti rs)): updateDBJN (εDB l ts) n p εv2)
  ==.  Pair n' (εTable l (εTable l (Table ti rs))):εDB l (updateDBJN (εDB l ts) n p εv2)
      ? simulationsUpdateJNF1Flow l lc ts n  p l2 v2 t' εt'
      ? εTableIdempotent l (Table ti rs)

  ==. Pair n' (εTable l (Table ti rs)):εDB l ts
  ==. εDB l (Pair n' (Table ti rs):ts)
  *** QED)

  -- stolen code ends here
  
  | otherwise
  =   εDB l (updateDBJN (εDB l ((Pair n' t):ts)) n p εv2)
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
      -- ? ( updateLabelCheckJN lc t p l2 v2
      -- ==! updateRowsCheckJN lc (lfTable p t) ti p l2 v2 rs
      -- *** QED)
      ? assert (updateLabelCheckJN lc εt' p l2 εv2)
      ? ( updateLabelCheckJN lc εt' p l2 εv2
      ==! updateRowsCheckJN lc (lfTable p εt') ti p l2 εv2 (εRows l ti rs)
      *** QED)
  ==. εDB l (updateDBJN ((Pair n' (εTable l t)):εDB l ts) n p εv2)
  ==. εDB l (updateDBJN ((Pair n' (εTable l (Table ti rs))):εDB l ts) n p εv2)
  ==. εDB l (updateDBJN ((Pair n' (Table ti (εRows l ti rs))):εDB l ts) n p εv2)
  ==. εDB l (Pair n' (Table ti (updateRowsJN p εv2 (εRows l ti rs))):εDB l ts) 
  ==. Pair n' (εTable l (Table ti (updateRowsJN p εv2 (εRows l ti rs)))):εDB l (εDB l ts)
  ==. Pair n' (Table ti (εRows l ti (updateRowsJN p εv2 (εRows l ti rs)))):εDB l (εDB l ts)

      ? εDBIdempotent l ts
      ? assert (updateRowsCheckJN lc (lfTable p εt') ti p l2 (if (canFlowTo l2 l) then v2 else THole) (εRows l ti rs))
      ? simulationsUpdateRowsJNF1Flow l lc (lfTable p εt') ti p l2 v2 rs

  
  ==. Pair n' (Table ti (εRows l ti rs)):εDB l ts 
  ==. Pair n' (εTable l (Table ti rs)):εDB l ts 
  ==. εDB l (Pair n' (Table ti rs):ts)


  *** QED
  where εv2 = if (canFlowTo l2 l) then v2 else THole
        lφ  = lawFlowReflexivity (lfRows p ti rs) `cast` lfTable p (Table ti rs)
        εlφ = lawFlowReflexivity (lfRows p ti (εRows l ti rs)) `cast` lfTable p (Table ti (εRows l ti rs))




{-@ simulationsUpdateRowsJNF1Flow
  :: (Label l, Eq l)
  => l:l
  -> lc:{l | canFlowTo lc l}
  -> lf:{l |not (canFlowTo lf l)}
  -> ti:{TInfo l | canFlowTo (tableLabel ti) l}
  -> p:Pred
  -> l2:l 
  -> v2: SDBTerm l 
  -> rs:{[Row l] | updateRowsCheckJN lc lf ti p l2 (if (canFlowTo l2 l) then v2 else THole) (εRows l ti rs)} 
  -> { (εRows l ti (updateRowsJN p (if (canFlowTo l2 l) then v2 else THole) (εRows l ti rs)) = εRows l ti rs) } 
   / [len rs] @-}
simulationsUpdateRowsJNF1Flow
  :: (Label l, Eq l)
  => l -> l -> l -> TInfo l -> Pred -> l -> Term l -> [Row l] -> Proof
simulationsUpdateRowsJNF1Flow l lc lf ti p l2 v2 [] 
  =   εRows l ti (updateRowsJN p εv2 (εRows l ti []))
  ==. εRows l ti (updateRowsJN p εv2 [])
  ==. εRows l ti []
  *** QED   
  where
    εv2 = if (canFlowTo l2 l) then v2 else THole

simulationsUpdateRowsJNF1Flow l lc lf ti p l2 v2 (r:rs) 
  =   εRows l ti (updateRowsJN p εv2 (εRows l ti (r:rs)))
  ==. εRows l ti (updateRowsJN p εv2 (εRow l ti r:εRows l ti rs))
  ==. εRows l ti (updateRowJN p εv2 (εRow l ti r):updateRowsJN p εv2 (εRows l ti rs))
  ==. εRow l ti (updateRowJN p εv2 (εRow l ti r)):εRows l ti (updateRowsJN p εv2 (εRows l ti rs))
      ? ( updateRowsCheckJN lc lf ti p l2 εv2 (εRows l ti (r:rs))
      ==. updateRowsCheckJN lc lf ti p l2 εv2 (εRow l ti r : εRows l ti rs)
      ==. (updateRowCheckJN lc lf ti p l2 εv2 (εRow l ti r) &&
        updateRowsCheckJN lc lf ti p l2 εv2 (εRows l ti rs))
      *** QED)
      ? simulationsUpdateRowsJNF1Flow l lc lf ti p l2 v2 rs
      ? simulationsUpdateRowJNF1Flow l lc lf ti p l2 v2 r
  ==. εRow  l ti r:εRows l ti rs
  ==. εRows l ti (r:rs)
  *** QED  
  where
    εv2 = if (canFlowTo l2 l) then v2 else THole

{-@ simulationsUpdateRowJNF1Flow
  :: (Label l, Eq l)
  => l:l
  -> lc:{l | canFlowTo lc l}
  -> lf:{l | not (canFlowTo lf l)}
  -> ti:{TInfo l | canFlowTo (tableLabel ti) l}
  -> p:Pred
  -> l2:l 
  -> v2: SDBTerm l 
  -> r:{Row l | updateRowCheckJN lc lf ti p l2 (if (canFlowTo l2 l) then v2 else THole) (εRow l ti r) } 
  -> { εRow l ti (updateRowJN p (if (canFlowTo l2 l) then v2 else THole) (εRow l ti r)) == εRow  l ti r  } 
@-}
simulationsUpdateRowJNF1Flow
  :: (Label l, Eq l)
  => l -> l -> l -> TInfo l -> Pred -> l -> Term l -> Row l -> Proof
simulationsUpdateRowJNF1Flow l lc lf ti p l1 v1 r@(Row k o1 o2)
  | not (field1Label ti `canFlowTo` l)
  -- contradiction
  =   lawFlowTransitivity (field1Label ti) (tableLabel ti) l
  -- contradiction
  | εep
  = ( updateRowCheckJN lc lf ti p l1 εv1 εr
  ==. updateRowCheckJN lc lf ti p l1 εv1 (Row k εo1 εo2)
  ==. ((updateRowLabel1 lc lf ti p l1 εv1 (makeValLabel ti εo1) εo2 εr)
   && (updateRowLabel2 lc lf ti p l1 εv1 (makeValLabel ti εo1) εo2 εr))
  *** QED)
    ? assert (updateRowLabel1 lc lf ti p l1 εv1 (makeValLabel ti εo1) εo2 εr)
    ? assert (((l1 `join` lc) `join` lf) `canFlowTo` field1Label ti)
    ? joinCanFlowTo (l1 `join` lc) lf (field1Label ti)
    ? lawFlowTransitivity lf (field1Label ti) l
    
  | otherwise
  =   εRow l ti (updateRowJN p εv1 (εRow l ti r))
  ==. εRow l ti (εRow l ti r)
      ? εRowIdempotent l ti r
  ==. εRow l ti r
  *** QED
  where 
    εv1 = if (canFlowTo l1 l) then v1 else THole
    εr  = εRow l ti r
    Row k εo1 εo2 = εr
    εep  = evalPred p εr



 
{-@ simulationsUpdateJNF1Flow' ::
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
                   (not (canFlowTo (lfTable p t) l))}
  -> εt:{Table l | (Just εt == lookupTable n (εDB l db)) && (tableInfo εt == tableInfo t) &&
                   (updateLabelCheckJN lc t p l2 v2) &&
                   (lfTable p t == lfTable p εt) &&
                   (not (canFlowTo (lfTable p t) l))}
  -> { εDB l db == εDB l (updateDBJN db n p v2) }
@-}

simulationsUpdateJNF1Flow' :: (Eq l, Label l) =>
  l -> l -> DB l -> TName -> Pred -> l -> Term l -> Table l -> Table l -> Proof
simulationsUpdateJNF1Flow' l lc [] n p l2 v2 _ _
  =   εDB l []
  ==. εDB l (updateDBJN [] n p v2) 
  *** QED 
  -- where
  --   εv2 = if (canFlowTo l2 l) then v2 else THole


simulationsUpdateJNF1Flow' l lc ((Pair n' t@(Table ti rs)):ts) n p l2 v2 t' εt'
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
  &&& (εDB l (updateDBJN ((Pair n' t):ts) n p v2)
  -- ==.  εDB l (updateDBJN ((Pair n' (εTable l t)):εDB l ts) n p v2)
  ==.  εDB l (Pair n' (Table ti rs): updateDBJN ts n p v2)
  ==.  Pair n' (εTable l (Table ti rs)):εDB l (updateDBJN (εDB l ts) n p v2)
      ? simulationsUpdateJNF1Flow' l lc ts n  p l2 v2 t' εt'
      -- ? εTableIdempotent l (Table ti rs)

  ==. Pair n' (εTable l (Table ti rs)):εDB l ts
  ==. εDB l (Pair n' (Table ti rs):ts)
  *** QED)

  -- stolen code ends here
  
  | otherwise
  =   εDB l (updateDBJN ((Pair n' t):ts) n p v2)
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
      -- ? ( updateLabelCheckJN lc t p l2 v2
      -- ==! updateRowsCheckJN lc (lfTable p t) ti p l2 v2 rs
      -- *** QED)
      ? assert (updateLabelCheckJN lc t' p l2 v2)
      ? ( updateLabelCheckJN lc t' p l2 v2
      ==! updateRowsCheckJN lc (lfTable p t') ti p l2 v2 rs
      *** QED)
  -- ==. εDB l (updateDBJN ((Pair n' (εTable l t)):εDB l ts) n p v2)
  -- ==. εDB l (updateDBJN ((Pair n' (εTable l (Table ti rs))):εDB l ts) n p εv2)
  -- ==. εDB l (updateDBJN ((Pair n' (Table ti (εRows l ti rs))):εDB l ts) n p εv2)
  ==. εDB l (Pair n' (Table ti (updateRowsJN p v2 rs)):ts) 
  ==. Pair n' (εTable l (Table ti (updateRowsJN p v2 rs))):εDB l ts
  ==. Pair n' (Table ti (εRows l ti (updateRowsJN p v2 rs))):εDB l ts

      ? assert (updateRowsCheckJN lc (lfTable p t') ti p l2 v2 rs)
      ? simulationsUpdateRowsJNF1Flow' l lc (lfTable p t') ti p l2 v2 rs

  
  ==. Pair n' (Table ti (εRows l ti rs)):εDB l ts 
  ==. Pair n' (εTable l (Table ti rs)):εDB l ts 
  ==. εDB l (Pair n' (Table ti rs):ts)


  *** QED





{-@ simulationsUpdateRowsJNF1Flow'
  :: (Label l, Eq l)
  => l:l
  -> lc:{l | canFlowTo lc l}
  -> lf:{l |not (canFlowTo lf l)}
  -> ti:{TInfo l | canFlowTo (tableLabel ti) l}
  -> p:Pred
  -> l2:l 
  -> v2: SDBTerm l 
  -> rs:{[Row l] | updateRowsCheckJN lc lf ti p l2 v2 rs} 
  -> { (εRows l ti (updateRowsJN p v2 rs) == εRows l ti rs) } 
   / [len rs] @-}
simulationsUpdateRowsJNF1Flow'
  :: (Label l, Eq l)
  => l -> l -> l -> TInfo l -> Pred -> l -> Term l -> [Row l] -> Proof
simulationsUpdateRowsJNF1Flow' l lc lf ti p l2 v2 [] 
  =   εRows l ti (updateRowsJN p v2 (εRows l ti []))
  ==. εRows l ti (updateRowsJN p v2 [])
  ==. εRows l ti []
  *** QED   
  where
    εv2 = if (canFlowTo l2 l) then v2 else THole

simulationsUpdateRowsJNF1Flow' l lc lf ti p l2 v2 (r:rs) 
  =   εRows l ti (updateRowsJN p v2 (r:rs))
  ==. εRows l ti (updateRowJN p v2 r:updateRowsJN p v2 rs)
  ==. εRow l ti (updateRowJN p v2 r):εRows l ti (updateRowsJN p v2 rs)
      ? ( updateRowsCheckJN lc lf ti p l2 v2 (r:rs)
      ==. (updateRowCheckJN lc lf ti p l2 v2 r &&
        updateRowsCheckJN lc lf ti p l2 v2 rs)
      *** QED)
      ? simulationsUpdateRowsJNF1Flow' l lc lf ti p l2 v2 rs
      ? simulationsUpdateRowJNF1Flow' l lc lf ti p l2 v2 r
  ==. εRow  l ti r:εRows l ti rs
  ==. εRows l ti (r:rs)
  *** QED  
  where
    εv2 = if (canFlowTo l2 l) then v2 else THole

{-@ simulationsUpdateRowJNF1Flow'
  :: (Label l, Eq l)
  => l:l
  -> lc:{l | canFlowTo lc l}
  -> lf:{l | not (canFlowTo lf l)}
  -> ti:{TInfo l | canFlowTo (tableLabel ti) l}
  -> p:Pred
  -> l2:l 
  -> v2: SDBTerm l 
  -> r:{Row l | updateRowCheckJN lc lf ti p l2 v2 r } 
  -> { εRow l ti (updateRowJN p v2 r) == εRow  l ti r  } 
@-}
simulationsUpdateRowJNF1Flow'
  :: (Label l, Eq l)
  => l -> l -> l -> TInfo l -> Pred -> l -> Term l -> Row l -> Proof
simulationsUpdateRowJNF1Flow' l lc lf ti p l1 v1 r@(Row k o1 o2)
  | not (field1Label ti `canFlowTo` l)
  -- contradiction
  =   lawFlowTransitivity (field1Label ti) (tableLabel ti) l
  | evalPred p r
  = ( updateRowCheckJN lc lf ti p l1 v1 r
  ==. updateRowCheckJN lc lf ti p l1 v1 (Row k o1 o2)
  ==. ((updateRowLabel1 lc lf ti p l1 v1 (makeValLabel ti o1) o2 r)
   && (updateRowLabel2 lc lf ti p l1 v1 (makeValLabel ti o1) o2 r))
  *** QED)
    ? assert (updateRowLabel1 lc lf ti p l1 v1 (makeValLabel ti o1) o2 r)
    ? assert (((l1 `join` lc) `join` lf) `canFlowTo` field1Label ti)
    ? joinCanFlowTo (l1 `join` lc) lf (field1Label ti)
    ? lawFlowTransitivity lf (field1Label ti) l

  | otherwise
  =   εRow l ti (updateRowJN p v1 r)
  ==. εRow l ti r
  *** QED

