{-@ LIQUID "--reflection"  @-}

module Simulations.UpdateAnyJN (simulationsUpdateAnyJN)  where

import ProofCombinators
import Labels 
import Programs 
import Predicates 

import Idempotence 
import Simulations.Terms 

import Prelude hiding (Maybe(..), fromJust, isJust)


{-@ simulationsUpdateAnyJN
  :: Label l 
  => l:l -> lc:{l | not (canFlowTo lc l) } 
  -> db:DB l 
  -> n:{TName | isJust (lookupTable n db) }
  -> p:Pred
  -> l1:l 
  -> v1:SDBTerm l
  -> t:{Table l | (Just t == lookupTable n db) && updateLabelCheckJN lc t p l1 v1} 
  -> { εDB l db == εDB l (updateDBJN db n p v1) } 
  @-}
  
simulationsUpdateAnyJN :: (Label l, Eq l) 
  => l -> l -> DB l -> TName -> Pred -> l -> Term l -> Table l  -> Proof
simulationsUpdateAnyJN l lc [] n p l1 v1 ti 
  = εDB l [] == εDB l (updateDBJN [] n p v1) *** QED 


simulationsUpdateAnyJN l lc ((Pair n' t@(Table ti rs)):ts) n p l1 v1 t' 
  | n == n'
  =  (Just t' ==. 
      lookupTable n ((Pair n' (Table ti rs)):ts) ==. 
      Just t 
      *** QED)
  &&& (εDB l (updateDBJN ((Pair n' (Table ti rs)):ts) n p v1)
  ==. εDB l (Pair n' (Table ti (updateRowsJN p v1 rs)):ts)
  ==. Pair n' (εTable l (Table ti (updateRowsJN p v1 rs))):εDB l ts
      ? assert (updateLabelCheckJN lc t p l1 v1)
      ? simulationsUpdateRowsJN l lc (lfTable p t) ti p l1 v1 rs
  ==. Pair n' (εTable l (Table ti rs)):εDB l ts 
  ==. εDB l (Pair n' (Table ti rs)    :ts) 
  *** QED) 


simulationsUpdateAnyJN l lc (Pair n' t:ts) n p l1 v1 t' 
  =   (Just t' ==. 
      lookupTable n ((Pair n' t):ts) ==. 
      lookupTable n ts
      *** QED)
  &&& (εDB l (updateDBJN ((Pair n' t):ts) n p v1)
  ==. εDB l (Pair n' t:updateDBJN ts n p v1)
  ==. Pair n' (εTable l t):εDB l (updateDBJN ts n p v1)
      ? simulationsUpdateAnyJN l lc ts n p l1 v1 t'
  ==. Pair n' (εTable l t):εDB l ts 
  ==. εDB l (Pair n' t    :ts) 
  *** QED)  

{-@ simulationsUpdateRowsJN
  :: (Label l, Eq l)
  => l:l -> lc:{l | not (canFlowTo lc l) } -> lf:l
  -> ti:TInfo l 
  -> p:Pred 
  -> l1:l 
  -> v1: SDBTerm l
  -> rs:{[Row l] | (updateRowsCheckJN lc lf ti p l1 v1 rs) } 
  -> { ( εRows l ti rs = εRows l ti (updateRowsJN p v1 rs)) } / [len rs] @-}
simulationsUpdateRowsJN
  :: (Label l, Eq l)
  => l -> l -> l -> TInfo l -> Pred -> l -> Term l -> [Row l] -> Proof 
simulationsUpdateRowsJN l lc lφ ti p l1 v1  [] 
  =   εRows l ti (updateRowsJN p v1 [])
  ==. εRows l ti []
  *** QED   

simulationsUpdateRowsJN l lc lφ ti p l1 v1  (r:rs) 
  =   εRows l ti (updateRowsJN p v1 (r:rs))
  ==. εRows l ti (updateRowJN p v1 r :updateRowsJN p v1 rs)
  ==. εRow l ti (updateRowJN p v1 r):εRows l ti (updateRowsJN p v1 rs)
      ? (if evalPred p r then
           (   assert (updateRowsCheckJN lc lφ ti p l1 v1 (r:rs))
             ? ( updateRowsCheckJN lc lφ ti p l1 v1 (r:rs)
                 ==. (updateRowCheckJN lc lφ ti p l1 v1 r && updateRowsCheckJN lc lφ ti p l1 v1 rs)
                 *** QED)
             ?simulationsUpdateRowJN  l lc lφ ti p l1 v1 r
           ? ())
         else
           ( updateRowsCheckJN lc lφ ti p l1 v1 (r:rs)
         ==. updateRowsCheckJN lc lφ ti p l1 v1 rs
         *** QED))
      ? assert (updateRowsCheckJN lc lφ ti p l1 v1 rs)
      ? simulationsUpdateRowsJN l lc lφ ti p l1 v1 rs
  ==. εRow l ti r:εRows l ti rs
  ==. εRows l ti (r:rs)
  *** QED   

{-@ simulationsUpdateRowJN
  :: (Label l, Eq l)
  => l:l -> lc:{l | not (canFlowTo lc l) } -> lf:l 
  -> ti:TInfo l 
  -> p:Pred 
  -> l1:l 
  -> v1: SDBTerm l 
  -> r: {Row l | (updateRowCheckJN lc lf ti p l1 v1 r) } 
  -> { ( εRow l ti r = εRow l ti (updateRowJN p v1 r)) } @-}
simulationsUpdateRowJN
  :: (Label l, Eq l)
  => l -> l -> l -> TInfo l -> Pred -> l -> Term l -> Row l -> Proof 
simulationsUpdateRowJN l lc lφ ti p l1 v1 r@(Row k o1 o2) 
  =   εRow l ti r 
      ? assert (updateRowCheckJN lc lφ ti p l1 v1 r) 
      ? assert (updateRowLabel1 lc lφ ti p l1 v1 (makeValLabel ti o1) o2 r) 
      ? joinCanFlowTo (l1 `join` lc) lφ (field1Label ti)
      ? joinCanFlowTo l1 lc (field1Label ti)
      ? lawFlowTransitivity lc (field1Label ti) l
      ? assert (not (field1Label ti `canFlowTo` l))
  ==. Row k THole THole
  ==. εRow l ti (updateRowJN p v1 r)
  *** QED 
