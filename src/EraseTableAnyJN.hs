{-@ LIQUID "--reflection"  @-}
module EraseTableAnyJN where

import Labels 
import Predicates 
import Prelude hiding (Maybe(..), fromJust, isJust)
import Programs 

import ProofCombinators 



{-@ εTableAnyJN
  :: (Label l, Eq l) 
  => l:l 
  -> n:TName 
  -> db:{DB l |  (isJust (lookupTable n db)) && not (canFlowTo (tableLabel (tableInfo (fromJust (lookupTable n db)))) l)}
  -> p:Pred -> v1:SDBTerm l
  -> {εDB l (updateDBJN db n p v1) == εDB l db }
@-}

εTableAnyJN :: (Eq l, Label l) => l -> TName -> DB l -> Pred -> Term l -> Proof 
εTableAnyJN l n [] p v1
  =   εDB l (updateDBJN [] n p v1) 
  ==. εDB l []
  *** QED  

εTableAnyJN l n db@((Pair n' t@(Table ti rs)):ts) p v1
  | n == n'
  =   tableInfo (fromJust (lookupTable n ((Pair n' (Table ti rs)):ts)))
  ==. tableInfo (fromJust (Just (Table ti rs)))
  ==. ti *** QED 
      ? assert (not (tableLabel ti `canFlowTo` l))
      ? (εDB l (updateDBJN db n p v1)
  ==. εDB l (Pair n (Table ti (updateRowsJN p v1 rs)):ts) 
  ==. Pair n (εTable l (Table ti (updateRowsJN p v1 rs))):εDB l ts 
  ==. Pair n (Table ti []):εDB l ts 
  ==. Pair n (εTable l (Table ti rs)):εDB l ts 
  ==. εDB l db
  *** QED )

εTableAnyJN l n db@((Pair n' t):ts) p v1
  =  (tableInfo (fromJust (lookupTable n ((Pair n' t):ts)))
  ==. tableInfo (fromJust (lookupTable n ts))
  *** QED )
  ? ( εDB l (updateDBJN db n p v1)
  ==. εDB l (Pair n' t: updateDBJN ts n p v1) 
  ==. Pair n' (εTable l t):εDB l (updateDBJN ts n p v1)
      ? εTableAnyJN l n ts p v1
  ==. Pair n' (εTable l t):εDB l ts 
  ==. εDB l ((Pair n' t):ts)
  *** QED ) 
