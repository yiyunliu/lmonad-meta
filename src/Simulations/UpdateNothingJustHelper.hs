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
  -> db: DB l
  -> n:{TName | isJust(lookupTable n db)}
  -> p:Pred
  -> l2:l
  -> v2: SDBTerm l
  -> t: {Table l | (Just t == lookupTable n db) &&
                   (canFlowTo (tableLabel (tableInfo t)) l) && (canFlowTo (field1Label (tableInfo t)) l)}
  -> εt:{Table l | (Just εt == lookupTable n (εDB l db)) && (tableInfo εt == tableInfo t) }
  -> { εDB l (updateDBNothingJust (εDB l db) n p (if (canFlowTo l2 l) then v2 else THole)) == εDB l db }
@-}

simulationsUpdateNJF1Flow :: (Eq l, Label l) =>
  l -> DB l -> TName -> Pred -> l -> Term l -> Table l -> Table l -> Proof
simulationsUpdateNJF1Flow l [] n p l2 v2 _ _
  =   εDB l []
  ==. εDB l (updateDBNothingJust (εDB l []) n p εv2) 
  *** QED 
  where
    εv2 = if (canFlowTo l2 l) then v2 else THole


simulationsUpdateNJF1Flow l ((Pair n' t@(Table ti rs)):ts) n p l2 v2 t' εt'
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
      ? simulationsUpdateNJF1Flow l ts n  p l2 v2 t' εt'
      ? εTableIdempotent l (Table ti rs)
  ==. Pair n' (εTable l (Table ti rs)):εDB l ts
  ==. εDB l (Pair n' (Table ti rs):ts)
  *** QED)

  -- stolen code ends here
  
  | otherwise
  =   εDB l (updateDBNothingJust (εDB l ((Pair n' t):ts)) n p εv2)
      ? (Just t' ==. 
      lookupTable n ((Pair n' (Table ti rs)):ts) ==. 
      Just t 
      *** QED)
      ? (Just εt' ==. 
      lookupTable n (εDB l ((Pair n' (Table ti rs)):ts)) ==. 
      lookupTable n (Pair n' (εTable l (Table ti rs)):εDB l ts) ==. 
      Just (εTable l t) 
      *** QED)
  ==. εDB l (updateDBNothingJust ((Pair n' (εTable l t)):εDB l ts) n p εv2)
  ==. εDB l (updateDBNothingJust ((Pair n' (εTable l (Table ti rs))):εDB l ts) n p εv2)
  ==. εDB l (updateDBNothingJust ((Pair n' (Table ti (εRows l ti rs))):εDB l ts) n p εv2)
  ==. εDB l (Pair n' (Table ti (updateRowsNothingJust p εv2 (εRows l ti rs))):εDB l ts) 
  ==. Pair n' (εTable l (Table ti (updateRowsNothingJust p εv2 (εRows l ti rs)))):εDB l (εDB l ts)
  ==. Pair n' (Table ti (εRows l ti (updateRowsNothingJust p εv2 (εRows l ti rs)))):εDB l (εDB l ts)

      ? εDBIdempotent l ts
      ? simulationsUpdateRowsNJF1Flow l ti p l2 v2 rs

  
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
  -> ti:{TInfo l | canFlowTo (tableLabel ti) l}
  -> p:Pred
  -> l2:l 
  -> v2: SDBTerm l 
  -> rs:[Row l]
  -> { (εRows l ti (updateRowsNothingJust p (if (canFlowTo l2 l) then v2 else THole) (εRows l ti rs)) = εRows l ti rs) } 
   / [len rs] @-}
simulationsUpdateRowsNJF1Flow
  :: (Label l, Eq l)
  => l -> TInfo l -> Pred -> l -> Term l -> [Row l] -> Proof
simulationsUpdateRowsNJF1Flow l ti p l2 v2 [] 
  =   εRows l ti (updateRowsNothingJust p εv2 (εRows l ti []))
  ==. εRows l ti (updateRowsNothingJust p εv2 [])
  ==. εRows l ti []
  *** QED   
  where
    εv2 = if (canFlowTo l2 l) then v2 else THole

simulationsUpdateRowsNJF1Flow l ti p l2 v2 (r:rs) 
  =   εRows l ti (updateRowsNothingJust p εv2 (εRows l ti (r:rs)))
  ==. εRows l ti (updateRowsNothingJust p εv2 (εRow l ti r:εRows l ti rs))
  ==. εRows l ti (updateRowNothingJust p εv2 (εRow l ti r):updateRowsNothingJust p εv2 (εRows l ti rs))
  ==. εRow l ti (updateRowNothingJust p εv2 (εRow l ti r)):εRows l ti (updateRowsNothingJust p εv2 (εRows l ti rs))
      ? simulationsUpdateRowsNJF1Flow l ti p l2 v2 rs
      ? assume (εRow l ti (updateRowNothingJust p εv2 (εRow l ti r)) == εRow  l ti r)
  ==. εRow  l ti r:εRows l ti rs
  ==. εRows l ti (r:rs)
  *** QED  
  where
    εv2 = if (canFlowTo l2 l) then v2 else THole

{-@ simulationsUpdateRowNJF1Flow
  :: (Label l, Eq l)
  => l:l
  -> ti:{TInfo l | canFlowTo (tableLabel ti) l}
  -> p:Pred
  -> l2:l 
  -> v2: SDBTerm l 
  -> r:Row l
  -> { εRow l ti (updateRowNothingJust p (if (canFlowTo l2 l) then v2 else THole) (εRow l ti r)) == εRow  l ti r  } 
@-}
simulationsUpdateRowNJF1Flow
  :: (Label l, Eq l)
  => l -> TInfo l -> Pred -> l -> Term l -> Row l -> Proof
simulationsUpdateRowNJF1Flow l ti p l2 v2 r@(Row k o1 o2)
  | not (field1Label ti `canFlowTo` l)
  -- contradiction
  =   lawFlowTransitivity (field1Label ti) (tableLabel ti) l
  | makeValLabel ti o1 `canFlowTo` l
  =   εRow l ti r
  ==. Row k (εTerm l o1) (εTerm l o2)
    ? assert (εTerm l o1 == o1)
    ? assert (εTerm l o2 == o2)
    
  ==. Row k o1 o2


  ==. εRow l ti (updateRowNothingJust p εv2 r)
  ==. εRow l ti (updateRowNothingJust p εv2 (εRow l ti r))
  *** QED
  where 
    εv2 = if (canFlowTo l2 l) then v2 else THole    



