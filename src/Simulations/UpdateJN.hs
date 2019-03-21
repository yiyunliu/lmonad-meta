{-@ LIQUID "--reflection"  @-}

module Simulations.UpdateJN where

import ProofCombinators
import Labels 
import Programs 
import Predicates 

import Idempotence 
import Simulations.Terms 
import Simulations.Predicates

import Prelude hiding (Maybe(..), fromJust, isJust)
{-@ simulationsUpdateJN
  :: Label l => l:l -> lc:{l | canFlowTo lc l } 
  -> db:DB l 
  -> n:{TName | isJust (lookupTable n db) }
  -> p:Pred
  -> l1:l  
  -> v1:SDBTerm l 
  -> t: {Table l | (Just t == lookupTable n db) && (updateLabelCheckJN lc t p l1 v1)}
  -> εt:{Table l | (Just εt == lookupTable n (εDB l db)) &&
                   (updateLabelCheckJN lc εt p l1 (if (canFlowTo l1 l) then v1 else THole)) } 
  -> { εDB l (updateDBJN (εDB l db) n p (if (canFlowTo l1 l) then v1 else THole)) == εDB l (updateDBJN db n p v1) } @-}

simulationsUpdateJN :: (Label l, Eq l) 
  => l -> l -> DB l -> TName -> Pred -> l -> Term l -> Table l -> Table l  -> Proof
simulationsUpdateJN l lc [] n p l1 v1 _ _
  =   εDB l (updateDBJN [] n p v1) 
  ==. εDB l [] 
  ==. εDB l (updateDBJN (εDB l []) n p εv1) 
  *** QED 
  where
    εv1 = if (canFlowTo l1 l) then v1 else THole

    -- is this file needed at all?
simulationsUpdateJN l lc ((Pair n' t@(Table ti rs)):ts) n p l1 v1 t' εt'
  | n == n' && not (tableLabel ti `canFlowTo` l)
  =   εDB l (updateDBJN (εDB l ((Pair n' t):ts)) n p εv1)
  ==. εDB l (updateDBJN (Pair n' (εTable l t): εDB l ts) n p εv1)
  ==. εDB l (updateDBJN (Pair n' (Table ti []): εDB l ts) n p εv1)
  ==. εDB l (Pair n' (Table ti (updateRowsJN p εv1 [])): εDB l ts)
  ==. εDB l (Pair n' (Table ti []): εDB l ts)
  ==. Pair n' (εTable l (Table ti [])) : εDB l (εDB l ts)
      ? εDBIdempotent l ts
  ==. Pair n' (Table ti []) : εDB l ts
  ==. Pair n' (εTable l (Table ti (updateRowsJN p v1 rs))):εDB l ts
  ==. εDB l (Pair n' (Table ti (updateRowsJN p v1 rs)):ts)
  ==. εDB l (updateDBJN (Pair n' t:ts) n p v1)
  *** QED
  | n == n' && tableLabel ti `canFlowTo` l
  =  (Just t' ==. 
      lookupTable n ((Pair n' (Table ti rs)):ts) ==. 
      Just t 
      *** QED)
  &&& (Just εt' ==. 
      lookupTable n (εDB l ((Pair n' (Table ti rs)):ts)) ==. 
      lookupTable n (Pair n' (εTable l (Table ti rs)):εDB l ts) ==. 
      Just (εTable l t) 
      *** QED)
  &&& (εDB l (updateDBJN (εDB l ((Pair n' t):ts)) n p εv1)
  ==.  εDB l (updateDBJN ((Pair n' (εTable l t)):εDB l ts) n p εv1)
  ==.  εDB l (updateDBJN ((Pair n' (εTable l (Table ti rs))):εDB l ts) n p εv1)
  ==.  εDB l (updateDBJN ((Pair n' (Table ti (εRows l ti rs))):εDB l ts) n p εv1)
  ==.  εDB l (Pair n' (Table ti (updateRowsJN p εv1 (εRows l ti rs))):εDB l ts) 
  ==.  Pair n' (εTable l (Table ti (updateRowsJN p εv1 (εRows l ti rs)))):εDB l (εDB l ts)
  ==.  Pair n' (Table ti (εRows l ti (updateRowsJN p εv1 (εRows l ti rs)))):εDB l (εDB l ts)
      ? assert (updateLabelCheckJN lc t p l1 v1)
      ? assert (updateLabelCheckJN lc εt' p l1 εv1)
      ? simulationsUpdateRowsJN l lc lφ εlφ ti p l1 v1 rs
      ? assert (εRows l ti (updateRowsJN p εv1 (εRows l ti rs)) == εRows l ti (updateRowsJN p v1 rs))
      ? εDBIdempotent l ts
  ==. Pair n' (Table ti (εRows l ti (updateRowsJN p v1 rs))):εDB l ts 
  ==. Pair n' (εTable l (Table ti (updateRowsJN p v1 rs))):εDB l ts 
  ==. εDB l (Pair n' (Table ti (updateRowsJN p v1 rs)):ts) 
  ==. εDB l (updateDBJN (Pair n' (Table ti rs):ts) n p v1)
  *** QED) 

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
  &&& (εDB l (updateDBJN (εDB l ((Pair n' t):ts)) n p εv1)
  ==.  εDB l (updateDBJN ((Pair n' (εTable l t)):εDB l ts) n p εv1)
  ==.  εDB l (Pair n' (εTable l (Table ti rs)): updateDBJN (εDB l ts) n p εv1)
  ==.  Pair n' (εTable l (εTable l (Table ti rs))):εDB l (updateDBJN (εDB l ts) n p εv1)
      ? simulationsUpdateJN l lc ts n p l1 v1 t' εt'
      ? assert (εDB l (updateDBJN (εDB l ts) n p εv1) == εDB l (updateDBJN ts n p v1))
      ? εTableIdempotent l (Table ti rs)
  ==. Pair n' (εTable l (Table ti rs)):εDB l (updateDBJN ts n p v1)
  ==. εDB l (Pair n' (Table ti rs):updateDBJN ts n p v1)
  ==. εDB l (updateDBJN (Pair n' (Table ti rs):ts) n p v1)
  *** QED) 

  where
    εv1 = if (canFlowTo l1 l) then v1 else THole
    lφ  = lawFlowReflexivity (lfRows p ti rs) `cast` lfTable p (Table ti rs)
    εlφ = lawFlowReflexivity (lfRows p ti (εRows l ti rs)) `cast` lfTable p (Table ti (εRows l ti rs))

{-@ simulationsUpdateRowsJN
  :: (Label l, Eq l)
  => l:l -> lc:{l | canFlowTo lc l }
  -> lf:l -> elf:l 
  -> ti:TInfo l 
  -> p:Pred
  -> l1:l 
  -> v1: SDBTerm l 
  -> rs:{[Row l] | (canFlowTo (lfRows p ti rs) lf) && (canFlowTo (lfRows p ti (εRows l ti rs)) elf) && (updateRowsCheckJN lc lf ti p l1 v1 rs) && (updateRowsCheckJN lc elf ti p l1 (if (canFlowTo l1 l) then v1 else THole) (εRows l ti rs))} 
  -> { (εRows l ti (updateRowsJN p (if (canFlowTo l1 l) then v1 else THole) (εRows l ti rs)) = εRows l ti (updateRowsJN p v1 rs)) } 
   / [len rs] @-}
simulationsUpdateRowsJN
  :: (Label l, Eq l)
  => l -> l -> l -> l-> TInfo l -> Pred -> l -> Term l -> [Row l] -> Proof 
simulationsUpdateRowsJN l lc _ _ ti p l1 v1 [] 
  =   εRows l ti (updateRowsJN p εv1 (εRows l ti []))
  ==. εRows l ti (updateRowsJN p v1 [])
  ==. εRows l ti []
  *** QED   
  where
    εv1 = if (canFlowTo l1 l) then v1 else THole

simulationsUpdateRowsJN l lc lφ εlφ ti p l1 v1 (r:rs)
  -- | evalPred p r, evalPred p εr
  =   εRows l ti (updateRowsJN p εv1 (εRows l ti (r:rs)))
  ==. εRows l ti (updateRowsJN p εv1 (εRow l ti r:εRows l ti rs))
  ==. εRows l ti (updateRowJN p εv1 (εRow l ti r):updateRowsJN p εv1 (εRows l ti rs))
  ==. εRow l ti (updateRowJN p εv1 (εRow l ti r)):εRows l ti (updateRowsJN p εv1 (εRows l ti rs))
      ? assert (updateRowsCheckJN lc εlφ ti p l1 εv1 (εRows l ti (r:rs)))
      ? assert (updateRowsCheckJN lc εlφ ti p l1 εv1 (εRow l ti r:εRows l ti rs))
      ? assert (updateRowCheckJN lc εlφ ti p l1 εv1 (εRow l ti r))
      ? assert (updateRowsCheckJN lc εlφ ti p l1 εv1 (εRows l ti rs))
      ? assert (updateRowsCheckJN lc lφ ti p l1 v1 (r:rs))
      ? assert (updateRowsCheckJN lc lφ ti p l1 v1 rs)
      ? assert (updateRowCheckJN lc lφ ti p l1 v1 r)
      ? assert (lfRows p ti (r:rs) `canFlowTo` lφ)
      ? assert ((lfRow p ti r `join` lfRows p ti rs) `canFlowTo` lφ)
      ? joinCanFlowTo (lfRow p ti r) (lfRows p ti rs) lφ
      ? assert (lfRows p ti (εRows l ti (r:rs)) `canFlowTo` εlφ)
      ? assert (lfRows p ti (εRow l ti r:εRows l ti rs) `canFlowTo` εlφ)
      ? assert ((lfRow p ti (εRow l ti r) `join` lfRows p ti (εRows l ti rs)) `canFlowTo` εlφ)
      ? joinCanFlowTo (lfRow p ti (εRow l ti r)) (lfRows p ti (εRows l ti rs)) εlφ
      ? assert (updateRowCheckJN lc lφ ti p l1 v1 r)
      ? simulationsUpdateRowsJN l lc lφ εlφ ti p l1 v1 rs
      ? simulationsUpdateRowJN  l lc lφ εlφ ti p l1 v1 r
  ==. εRow  l ti (updateRowJN p v1 r):εRows l ti (updateRowsJN p v1 rs)
  ==. εRows l ti (updateRowJN p v1 r:updateRowsJN p v1 rs)
  ==. εRows l ti (updateRowsJN p v1 (r:rs))
  *** QED
  where
    εv1 = if (canFlowTo l1 l) then v1 else THole
    εr  = εRow l ti r
    Row k o1 o2 = r
    


{-@ simulationsUpdateRowJN
  :: (Label l, Eq l)
  => l:l -> lc:{l | canFlowTo lc l } -> lf:l -> elf:l
  -> ti:TInfo l 
  -> p:Pred
  -> l1:l 
  -> v1: SDBTerm l 
  -> r: {Row l | (canFlowTo (lfRow p ti r) lf) && (canFlowTo (lfRow p ti (εRow l ti r)) elf) && (updateRowCheckJN lc lf ti p l1 v1 r) && (updateRowCheckJN lc elf ti p l1 (if (canFlowTo l1 l) then v1 else THole) (εRow l ti r)) } 
  -> { εRow l ti (updateRowJN p (if (canFlowTo l1 l) then v1 else THole) (εRow l ti r)) = εRow l ti (updateRowJN p v1 r) } @-}
simulationsUpdateRowJN
  :: (Label l, Eq l)
  => l -> l -> l -> l -> TInfo l -> Pred -> l -> Term l -> Row l -> Proof 
simulationsUpdateRowJN l lc lφ εlφ ti p l1 v1 r@(Row k o1 o2)
  =   εRow l ti (updateRowJN p εv1 (εRow l ti (Row k o1 o2))) 
      ? globals
  ==. εRow l ti (updateRowJN p v1 (Row k o1 o2))
  *** QED 
    where 
      εr  = Row k (εTerm l o1) THole
      εv1 = if (canFlowTo l1 l) then v1 else THole
      εo2 = if makeValLabel ti o1 `canFlowTo` l then (εTerm l v1) else THole
      εv2 = if (canFlowTo l2 l) then o2 else THole
      v2 = o2
      l2 = makeValLabel ti o1
      lφR  = lfRow p ti r  
      lφER = lfRow p ti (εRow l ti r)
      globals = 
          assert (updateRowCheckJN  lc εlφ ti p l1 εv1 (εRow l ti r))
        ? use (updateRowLabel1 lc εlφ ti p l1 εv1 l2 εv2 (εRow l ti r))
        ? use (updateRowLabel2 lc εlφ ti p l1 εv1 l2 εv2 (εRow l ti r))
        ? assert (updateRowCheckJN  lc lφ ti p l1 v1 r)
        ? use (updateRowLabel1 lc lφ ti p l1 v1 l2 v2 r)
        ? use (updateRowLabel2 lc lφ ti p l1 v1 l2 v2 r)
        ? assert (lφR  `canFlowTo`  lφ)
        ? assert (lφER `canFlowTo` εlφ)
        ? joinCanFlowTo (l1 `join` lc) lφ (field1Label ti)
        ? lawFlowTransitivity lφR  lφ (field1Label ti) 
        ? joinCanFlowTo (l1 `join` lc) εlφ (field1Label ti)
        ? lawFlowTransitivity lφER  εlφ (field1Label ti) 
        ? joinCanFlowTo l1 lc (field1Label ti)
        ? joinCanFlowTo (l2 `join` lc) lφ (makeValLabel ti v1)
        ? lawFlowTransitivity lφR  lφ (makeValLabel ti v1) 
        ? joinCanFlowTo (l2 `join` lc) εlφ (makeValLabel ti v1)
        ? lawFlowTransitivity lφER  εlφ (makeValLabel ti v1) 
        ? joinCanFlowTo l2 lc (makeValLabel ti v1)
        ? joinCanFlowTo (l2 `join` lc)  lφ (makeValLabel ti εv1)
        ? lawFlowTransitivity lφR  lφ (makeValLabel ti εv1) 
        ? joinCanFlowTo (l2 `join` lc) εlφ (makeValLabel ti εv1)
        ? lawFlowTransitivity lφER  εlφ (makeValLabel ti εv1) 
        ? joinCanFlowTo l2 lc (makeValLabel ti εv1)
        ? lawFlowTransitivity l2 (makeValLabel ti o1)  l 
        ? lawFlowTransitivity l2 (makeValLabel ti v1)  l 
        ? lawFlowTransitivity l2 (makeValLabel ti εv1) l 
        ? lawFlowTransitivity l1 (field1Label ti)      l 
        ? lawFlowTransitivity (makeValLabel ti o1) (field1Label ti)      l 
        ? lawFlowTransitivity (makeValLabel ti o1) (makeValLabel ti εv1) l 
        ? lawFlowTransitivity (makeValLabel ti o1) (makeValLabel ti  v1) l 
        ? lawFlowTransitivity (field1Label ti) (makeValLabel ti εv1) l 
        ? lawFlowTransitivity (field1Label ti) (makeValLabel ti  v1) l 
        ? assert (εTerm l THole == THole)
        ? assert (εTerm l v1 == v1 )  
        ? assert (εTerm l v2 == v2 )  
        ? assert (εTerm l o1 == o1 )  
        ? assert (εTerm l o2 == o2 )  
        ? (evalPred p r *** QED )
        ? (evalPred p (εRow l ti r) *** QED )
        ? (evalPred p εr *** QED )

