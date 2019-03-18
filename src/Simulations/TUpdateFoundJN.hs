{-@ LIQUID "--reflection"  @-}

module Simulations.TUpdateFoundJN where

import ProofCombinators
import Labels 
import Programs 
import Predicates 

import Idempotence 
import EraseTableAny 
import LookupTableErase 
import LabelPredEraseEqual
import LabelUpdateCheck
import Simulations.Terms 
import Simulations.Update 
import Simulations.UpdateOne

import Prelude hiding (Maybe(..), fromJust, isJust)


{-@ simulationsUpdateFlowsFoundJN
  :: Label l => l:l 
  -> lc:{l | canFlowTo lc l }
  -> db:DB l 
  -> n:TName 
  -> p:Pred 
  -> l1:l
  -> v1:SDBTerm l
  -> t:{Table l  | Just t == lookupTable n db } 
  -> εt:{Table l | (Just εt == lookupTable n (εDB l db)) && (tableInfo t == tableInfo εt) } 
  -> { ε l (eval (ε l (Pg lc db (TUpdate n (TPred p) (TJust (TLabeled l1 v1)) TNothing)))) == ε l (eval (Pg lc db (TUpdate n (TPred p) (TJust (TLabeled l1 v1)) TNothing))) } 
  @-}
simulationsUpdateFlowsFoundJN :: (Label l, Eq l) 
  => l -> l -> DB l -> TName -> Pred -> l -> Term l -> Table l -> Table l -> Proof

simulationsUpdateFlowsFoundJN l lc db n p l1 v1 t εt = ()

