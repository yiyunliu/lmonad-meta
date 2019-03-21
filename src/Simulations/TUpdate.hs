{-@ LIQUID "--reflection"  @-}

module Simulations.TUpdate where

import ProofCombinators
import Labels 
import Programs 
import Predicates 

import Idempotence 
import LookupTableErase 
import LabelPredErase
import LabelPredEraseEqual
import Simulations.Terms 
import Simulations.UpdateAny
import Simulations.UpdateAnyNothingJust
import Simulations.UpdateAnyJN
import Simulations.TUpdateFound
import Simulations.TUpdateFoundNothingJust
import Simulations.TUpdateFoundJN
  
import Prelude hiding (Maybe(..), fromJust, isJust) 

{-@ simulationsTUpdate  
  :: Label l => l:l 
  -> lc:l
  -> db:DB l 
  -> n:TName 
  -> t1:Term l 
  -> t2:Term l 
  -> t3:{Term l | terminates (Pg lc db (TUpdate n t1 t2 t3)) && ς (Pg lc db (TUpdate n t1 t2 t3))}
  -> { ε l (eval (ε l (Pg lc db (TUpdate n t1 t2 t3)))) == ε l (eval (Pg lc db (TUpdate n t1 t2 t3))) } 
  @-}
simulationsTUpdate :: (Label l, Eq l) 
  => l -> l -> DB l -> TName -> Term l -> Term l -> Term l -> Proof
simulationsTUpdate l lc db n t1@(TPred p) t2@(TJust (TLabeled l1 v1)) t3@(TJust (TLabeled l2 v2))  
  | lc `canFlowTo` l 
  = assert (ς (Pg lc db (TUpdate n t1 t2 t3))) &&& 
    simulationsUpdateFlows l lc db n p l1 v1 l2 v2  
  | otherwise 
  = assert (ς (Pg lc db (TUpdate n t1 t2 t3))) &&& 
    simulationsUpdateDoesNotFlow l lc db n p l1 v1 l2 v2


simulationsTUpdate l lc db n t1@(TPred p) t2@TNothing t3@(TJust (TLabeled l2 v2))  
 | lc `canFlowTo` l
  -- todo
 = assert (ς (Pg lc db (TUpdate n t1 t2 t3))) &&&
    simulationsUpdateFlowsNothingJust l lc db n p l2 v2
  | otherwise
  = assert (ς (Pg lc db (TUpdate n t1 t2 t3))) &&&
    simulationsUpdateDoesNotFlowNothingJust l lc db n p l2 v2


simulationsTUpdate l lc db n t1@(TPred p) t2@(TJust (TLabeled l1 v1)) t3@TNothing 
 | lc `canFlowTo` l
  -- todo
 = assert (ς (Pg lc db (TUpdate n t1 t2 t3))) &&&
    simulationsUpdateFlowsJN  l lc db n p l1 v1
  | otherwise
  = assert (ς (Pg lc db (TUpdate n t1 t2 t3))) &&&
    simulationsUpdateDoesNotFlowJN l lc db n p l1 v1


simulationsTUpdate _ lc db n p t1 t2 
  = assert (ς (Pg lc db (TUpdate n p t1 t2)))
  ? assert False 


{-@ simulationsUpdateFlows  
  :: Label l => l:l 
  -> lc:{l | canFlowTo lc l }
  -> db:DB l 
  -> n:TName 
  -> p:Pred 
  -> l1:l
  -> v1:SDBTerm l 
  -> l2:l
  -> v2:SDBTerm l 
  -> { ε l (eval (ε l (Pg lc db (TUpdate n (TPred p) (TJust (TLabeled l1 v1)) (TJust (TLabeled l2 v2)))))) == ε l (eval (Pg lc db (TUpdate n (TPred p) (TJust (TLabeled l1 v1)) (TJust (TLabeled l2 v2))))) } 
  @-}
simulationsUpdateFlows :: (Label l, Eq l) 
  => l -> l -> DB l -> TName -> Pred -> l -> Term l -> l -> Term l -> Proof
simulationsUpdateFlows l lc db n p l1 v1 l2 v2 
  | Just t  <- lookupTable n db
  , Just εt <- lookupTable n (εDB l db)
  =   lookupTableErase l n db 
  &&& simulationsUpdateFlowsFound l lc db n p l1 v1 l2 v2 t εt
simulationsUpdateFlows l lc db n p l1 v1 l2 v2 
  =   ε l (eval (ε l (Pg lc db (TUpdate n (TPred p) (TJust (TLabeled l1 v1)) (TJust (TLabeled l2 v2))))))
  ==. ε l (eval (Pg lc (εDB l db) (εTerm l (TUpdate n (TPred p) (TJust (TLabeled l1 v1)) (TJust (TLabeled l2 v2)))))) 
  ==. ε l (eval (Pg lc (εDB l db) (TUpdate n (εTerm l (TPred p)) (εTerm l (TJust (TLabeled l1 v1))) (εTerm l (TJust (TLabeled l2 v2))))))
  ==. ε l (eval (Pg lc (εDB l db) (TUpdate n (εTerm l (TPred p)) (TJust (εTerm l (TLabeled l1 v1))) (TJust (εTerm l (TLabeled l2 v2))))))
      ? lookupTableErase l n db 
      ? (case lookupTable n (εDB l db) of 
          Just _ -> assert (isJust (lookupTable n db))
          Nothing -> assert (not (isJust (lookupTable n db))))
      ? (case lookupTable n db of 
          Just _ -> assert (isJust (lookupTable n (εDB l db)))
          Nothing -> assert (not (isJust (lookupTable n (εDB l db)))))
  ==. ε l (Pg lc (εDB l db) TException) 
  ==. Pg lc (εDB l (εDB l db)) (εTerm l TException) 
      ? εDBIdempotent l db 
  ==. Pg lc (εDB l db) (εTerm l TException) 
  ==. ε l (Pg lc db TException) 
      ? lookupTableErase l n db 
  ==. ε l (eval (Pg lc db (TUpdate n (TPred p) (TJust (TLabeled l1 v1)) (TJust (TLabeled l2 v2))))) 
  *** QED 

{-@ simulationsUpdateDoesNotFlow  
  :: Label l => l:l 
  -> lc:{l | not (canFlowTo lc l) }
  -> db:DB l 
  -> n:TName 
  -> p:Pred 
  -> l1:l
  -> v1:SDBTerm l 
  -> l2:l
  -> v2:{SDBTerm l | ς (Pg lc db (TUpdate n (TPred p) (TJust (TLabeled l1 v1)) (TJust (TLabeled l2 v2))))} 
  -> { ε l (eval (ε l (Pg lc db (TUpdate n (TPred p) (TJust (TLabeled l1 v1)) (TJust (TLabeled l2 v2)))))) == ε l (eval (Pg lc db (TUpdate n (TPred p) (TJust (TLabeled l1 v1)) (TJust (TLabeled l2 v2))))) } 
  @-}
simulationsUpdateDoesNotFlow :: (Label l, Eq l) 
  => l -> l -> DB l -> TName -> Pred -> l -> Term l ->  l -> Term l -> Proof

simulationsUpdateDoesNotFlow l lc db n p l1 v1 l2 v2 
  | Just t <- lookupTable n db
  ,  updateLabelCheck lc t p l1 v1 l2 v2      
  =   let lc' = (field1Label (tableInfo t) `join` l1) `join` tableLabel (tableInfo t) in 
      ε l (eval (ε l (Pg lc db (TUpdate n t1 t2 t3)))) 
  ==. ε l (eval (PgHole (εDB l db))) 
  ==. ε l (PgHole (εDB l db)) 
  ==. PgHole (εDB l (εDB l db)) 
      ? εDBIdempotent l db 
  ==. PgHole (εDB l db)
      ? assert (isJust (lookupTable n db))
      ? assert (Just t == lookupTable n db)
      ? lookupTableErase l n db 
      ? assert (isJust (lookupTable n (εDB l db)))
      ? assert (updateLabelCheck lc t p l1 v1 l2 v2)
      ? simulationsUpdateAny l lc db n p l1 v1 l2 v2 t 
      ? assert (εDB l db == εDB l (updateDB db n p v1 v2)) 
  ==. PgHole (εDB l (updateDB db n p v1 v2))
      ? joinCanFlowTo lc lc' l 
  ==. ε l (Pg (lc `join` lc') (updateDB db n p v1 v2) TUnit) 
  ==. ε l (eval (Pg lc db (TUpdate n t1 t2 t3))) 
  *** QED 
  where
    t1 = TPred p 
    t2 = TJust (TLabeled l1 v1)
    t3 = TJust (TLabeled l2 v2)

simulationsUpdateDoesNotFlow l lc db n p l1 v1 l2 v2   
  | Just t <- lookupTable n db 
  =   let lc' = (field1Label (tableInfo t) `join` l1) `join` tableLabel (tableInfo t) in 
      ε l (eval (ε l (Pg lc db (TUpdate n t1 t2 t3)))) 
  ==. ε l (eval (PgHole (εDB l db))) 
  ==. ε l (PgHole (εDB l db)) 
  ==. PgHole (εDB l (εDB l db)) 
      ? εDBIdempotent l db 
  ==. PgHole (εDB l db)
      ? joinCanFlowTo lc lc' l 
  ==. ε l (Pg (lc `join` lc') db (TReturn TException)) 
  ==. ε l (eval (Pg lc db (TUpdate n t1 t2 t3))) 
  *** QED 
  where
    t1 = TPred p 
    t2 = TJust (TLabeled l1 v1)
    t3 = TJust (TLabeled l2 v2)

-- a separate function
-- todo: update label check success. nothing just.

-- todo: update label check fail. table found. nothing just

simulationsUpdateDoesNotFlow l lc db n p l1 v1 l2 v2  
  =   ε l (eval (ε l (Pg lc db (TUpdate n t1 t2 t3)))) 
  ==. ε l (eval (PgHole (εDB l db))) 
  ==. ε l (PgHole (εDB l db)) 
  ==. PgHole (εDB l (εDB l db)) 
      ? εDBIdempotent l db 
  ==. PgHole (εDB l db)
  ==. ε l (Pg lc db TException) 
  ==. ε l (eval (Pg lc db (TUpdate n t1 t2 t3))) 
  *** QED 
  where
    t1 = TPred p 
    t2 = TJust (TLabeled l1 v1)
    t3 = TJust (TLabeled l2 v2)

-- todo : table not found.



{-@ simulationsUpdateDoesNotFlowNothingJust
  :: Label l => l:l 
  -> lc:{l | not (canFlowTo lc l) }
  -> db:DB l 
  -> n:TName 
  -> p:Pred 
  -> l2:l
  -> v2:{SDBTerm l | ς (Pg lc db (TUpdate n (TPred p) TNothing (TJust (TLabeled l2 v2))))} 
  -> { ε l (eval (ε l (Pg lc db (TUpdate n (TPred p) TNothing (TJust (TLabeled l2 v2)))))) == ε l (eval (Pg lc db (TUpdate n (TPred p) TNothing (TJust (TLabeled l2 v2))))) } 
  @-}
simulationsUpdateDoesNotFlowNothingJust :: (Label l, Eq l) 
  => l -> l -> DB l -> TName -> Pred -> l -> Term l -> Proof
simulationsUpdateDoesNotFlowNothingJust l lc db n p l2 v2
  | Just t <- lookupTable n db
  -- this case eval part flows
  , updateLabelCheckNothingJust lc t p l2 v2
  =   let lc' = ((field1Label (tableInfo t)
                         `join` lfTable p t) `join` tableLabel (tableInfo t)) in
      ε l (eval (ε l (Pg lc db (TUpdate n t1 t2 t3))))
  ==. ε l (eval (PgHole (εDB l db)))
  ==. ε l (PgHole (εDB l db))
  ==. PgHole (εDB l (εDB l db))
      ? εDBIdempotent l db
  ==. PgHole (εDB l db)
      -- copy over similar conditions
      ? assert (isJust (lookupTable n db))
      ? assert (Just t == lookupTable n db)
      ? lookupTableErase l n db
      ? assert (isJust (lookupTable n (εDB l db)))
      ? assert (updateLabelCheckNothingJust lc t p l2 v2)
      ? simulationsUpdateAnyNothingJust l lc db n p l2 v2 t
      ? assert (εDB l db == εDB l (updateDBNothingJust db n p v2)) 
  -- the other end of proof
  -- up to this step it's getting hard since we need to actually evaluate it
  ==. PgHole (εDB l (updateDBNothingJust db n p v2))
      ? joinCanFlowTo lc lc' l
  ==. ε l (Pg (lc `join` lc') (updateDBNothingJust db n p v2) TUnit)
  ==. ε l (eval (Pg lc db (TUpdate n t1 t2 t3)))
  *** QED
  where t1 = TPred p
        t2 = TNothing
        t3 = TJust (TLabeled l2 v2)


-- the other two cases are trivial

simulationsUpdateDoesNotFlowNothingJust l lc db n p l2 v2   
  | Just t <- lookupTable n db 
  =   let lc' = ((field1Label (tableInfo t)
                         `join` lfTable p t) `join` tableLabel (tableInfo t)) in 
      ε l (eval (ε l (Pg lc db (TUpdate n t1 t2 t3)))) 
  ==. ε l (eval (PgHole (εDB l db))) 
  ==. ε l (PgHole (εDB l db)) 
  ==. PgHole (εDB l (εDB l db)) 
      ? εDBIdempotent l db 
  ==. PgHole (εDB l db)
      ? joinCanFlowTo lc lc' l 
  ==. ε l (Pg (lc `join` lc') db (TReturn TException)) 
  ==. ε l (eval (Pg lc db (TUpdate n t1 t2 t3))) 
  *** QED 
  where
    t1 = TPred p 
    t2 = TNothing
    t3 = TJust (TLabeled l2 v2)


simulationsUpdateDoesNotFlowNothingJust l lc db n p l2 v2  
  =   ε l (eval (ε l (Pg lc db (TUpdate n t1 t2 t3)))) 
  ==. ε l (eval (PgHole (εDB l db))) 
  ==. ε l (PgHole (εDB l db)) 
  ==. PgHole (εDB l (εDB l db)) 
      ? εDBIdempotent l db 
  ==. PgHole (εDB l db)
  ==. ε l (Pg lc db TException) 
  ==. ε l (eval (Pg lc db (TUpdate n t1 t2 t3))) 
  *** QED 
  where
    t1 = TPred p 
    t2 = TNothing
    t3 = TJust (TLabeled l2 v2)


{-@ simulationsUpdateFlowsNothingJust
  :: Label l => l:l 
  -> lc:{l | canFlowTo lc l }
  -> db:DB l 
  -> n:TName 
  -> p:Pred
  -> l2:l
  -> v2:SDBTerm l 
  -> { ε l (eval (ε l (Pg lc db (TUpdate n (TPred p) TNothing (TJust (TLabeled l2 v2)))))) == ε l (eval (Pg lc db (TUpdate n (TPred p) TNothing (TJust (TLabeled l2 v2))))) } 
  @-}
simulationsUpdateFlowsNothingJust :: (Label l, Eq l) 
  => l -> l -> DB l -> TName -> Pred -> l -> Term l -> Proof
simulationsUpdateFlowsNothingJust l lc db n p l2 v2 
  | Just t  <- lookupTable n db
  , Just εt <- lookupTable n (εDB l db)
  =   lookupTableErase l n db 
  &&& simulationsUpdateFlowsFoundNothingJust l lc db n p l2 v2 t εt
simulationsUpdateFlowsNothingJust l lc db n p l2 v2 
  =   ε l (eval (ε l (Pg lc db (TUpdate n (TPred p) TNothing (TJust (TLabeled l2 v2))))))
  ==. ε l (eval (Pg lc (εDB l db) (εTerm l (TUpdate n (TPred p) TNothing (TJust (TLabeled l2 v2)))))) 
  ==. ε l (eval (Pg lc (εDB l db) (TUpdate n (εTerm l (TPred p)) (εTerm l TNothing) (εTerm l (TJust (TLabeled l2 v2))))))
  ==. ε l (eval (Pg lc (εDB l db) (TUpdate n (εTerm l (TPred p)) TNothing (TJust (εTerm l (TLabeled l2 v2))))))
      ? lookupTableErase l n db 
      ? (case lookupTable n (εDB l db) of 
          Just _ -> assert (isJust (lookupTable n db))
          Nothing -> assert (not (isJust (lookupTable n db))))
      ? (case lookupTable n db of 
          Just _ -> assert (isJust (lookupTable n (εDB l db)))
          Nothing -> assert (not (isJust (lookupTable n (εDB l db)))))
  ==. ε l (Pg lc (εDB l db) TException) 
  ==. Pg lc (εDB l (εDB l db)) (εTerm l TException) 
      ? εDBIdempotent l db 
  ==. Pg lc (εDB l db) (εTerm l TException) 
  ==. ε l (Pg lc db TException) 
      ? lookupTableErase l n db 
  ==. ε l (eval (Pg lc db (TUpdate n (TPred p) TNothing (TJust (TLabeled l2 v2))))) 
  *** QED 





{-@ simulationsUpdateFlowsJN
  :: Label l => l:l 
  -> lc:{l | canFlowTo lc l }
  -> db:DB l 
  -> n:TName 
  -> p:Pred 
  -> l1:l
  -> v1:SDBTerm l 
  -> { ε l (eval (ε l (Pg lc db (TUpdate n (TPred p) (TJust (TLabeled l1 v1)) TNothing)))) == ε l (eval (Pg lc db (TUpdate n (TPred p) (TJust (TLabeled l1 v1)) TNothing))) } 
  @-}
simulationsUpdateFlowsJN :: (Label l, Eq l) 
  => l -> l -> DB l -> TName -> Pred -> l -> Term l -> Proof
simulationsUpdateFlowsJN l lc db n p l1 v1
  | Just t  <- lookupTable n db
  , Just εt <- lookupTable n (εDB l db)
  =   lookupTableErase l n db 
  &&& simulationsUpdateFlowsFoundJN l lc db n p l1 v1 t εt
simulationsUpdateFlowsJN l lc db n p l1 v1
  =   ε l (eval (ε l (Pg lc db (TUpdate n (TPred p) (TJust (TLabeled l1 v1)) TNothing))))
  ==. ε l (eval (Pg lc (εDB l db) (εTerm l (TUpdate n (TPred p) (TJust (TLabeled l1 v1)) TNothing)))) 
  ==. ε l (eval (Pg lc (εDB l db) (TUpdate n (εTerm l (TPred p)) (εTerm l (TJust (TLabeled l1 v1))) (εTerm l TNothing))))
  ==. ε l (eval (Pg lc (εDB l db) (TUpdate n (εTerm l (TPred p)) (TJust (εTerm l (TLabeled l1 v1))) TNothing)))
      ? lookupTableErase l n db 
      ? (case lookupTable n (εDB l db) of 
          Just _ -> assert (isJust (lookupTable n db))
          Nothing -> assert (not (isJust (lookupTable n db))))
      ? (case lookupTable n db of 
          Just _ -> assert (isJust (lookupTable n (εDB l db)))
          Nothing -> assert (not (isJust (lookupTable n (εDB l db)))))
  ==. ε l (Pg lc (εDB l db) TException) 
  ==. Pg lc (εDB l (εDB l db)) (εTerm l TException) 
      ? εDBIdempotent l db 
  ==. Pg lc (εDB l db) (εTerm l TException) 
  ==. ε l (Pg lc db TException) 
      ? lookupTableErase l n db 
  ==. ε l (eval (Pg lc db (TUpdate n (TPred p) (TJust (TLabeled l1 v1)) TNothing))) 
  *** QED 





{-@ simulationsUpdateDoesNotFlowJN
  :: Label l => l:l 
  -> lc:{l | not (canFlowTo lc l) }
  -> db:DB l 
  -> n:TName 
  -> p:Pred 
  -> l1:l
  -> v1:{SDBTerm l | ς (Pg lc db (TUpdate n (TPred p) (TJust (TLabeled l1 v1)) TNothing))} 
  -> { ε l (eval (ε l (Pg lc db (TUpdate n (TPred p) (TJust (TLabeled l1 v1)) TNothing)))) == ε l (eval (Pg lc db (TUpdate n (TPred p) (TJust (TLabeled l1 v1)) TNothing))) } 
  @-}
simulationsUpdateDoesNotFlowJN :: (Label l, Eq l) 
  => l -> l -> DB l -> TName -> Pred -> l -> Term l -> Proof

simulationsUpdateDoesNotFlowJN l lc db n p l1 v1 
  | Just t <- lookupTable n db
  ,  updateLabelCheckJN lc t p l1 v1 
  =   let lc' = ((l1
                         `join` (lfTable p t))
                         `join` tableLabel (tableInfo t))  in 
      ε l (eval (ε l (Pg lc db (TUpdate n t1 t2 t3)))) 
  ==. ε l (eval (PgHole (εDB l db))) 
  ==. ε l (PgHole (εDB l db)) 
  ==. PgHole (εDB l (εDB l db)) 
      ? εDBIdempotent l db 
  ==. PgHole (εDB l db)
      ? assert (isJust (lookupTable n db))
      ? assert (Just t == lookupTable n db)
      ? lookupTableErase l n db 
      ? assert (isJust (lookupTable n (εDB l db)))
      ? assert (updateLabelCheckJN lc t p l1 v1)
      ? simulationsUpdateAnyJN l lc db n p l1 v1 t 
      ? assert (εDB l db == εDB l (updateDBJN db n p v1)) 
  ==. PgHole (εDB l (updateDBJN db n p v1))
      ? joinCanFlowTo lc lc' l 
  ==. ε l (Pg (lc `join` lc') (updateDBJN db n p v1) TUnit) 
  ==. ε l (eval (Pg lc db (TUpdate n t1 t2 t3))) 
  *** QED 
  where
    t1 = TPred p 
    t2 = TJust (TLabeled l1 v1)
    t3 = TNothing

simulationsUpdateDoesNotFlowJN l lc db n p l1 v1 
  | Just t <- lookupTable n db 
  =   let lc' = ((l1
                         `join` (lfTable p t))
                         `join` tableLabel (tableInfo t)) in 
      ε l (eval (ε l (Pg lc db (TUpdate n t1 t2 t3)))) 
  ==. ε l (eval (PgHole (εDB l db))) 
  ==. ε l (PgHole (εDB l db)) 
  ==. PgHole (εDB l (εDB l db)) 
      ? εDBIdempotent l db 
  ==. PgHole (εDB l db)
      ? joinCanFlowTo lc lc' l 
  ==. ε l (Pg (lc `join` lc') db (TReturn TException)) 
  ==. ε l (eval (Pg lc db (TUpdate n t1 t2 t3))) 
  *** QED 
  where
    t1 = TPred p 
    t2 = TJust (TLabeled l1 v1)
    t3 = TNothing

-- a separate function
-- todo: update label check success. nothing just.

-- todo: update label check fail. table found. nothing just

simulationsUpdateDoesNotFlowJN l lc db n p l1 v1 
  =   ε l (eval (ε l (Pg lc db (TUpdate n t1 t2 t3)))) 
  ==. ε l (eval (PgHole (εDB l db))) 
  ==. ε l (PgHole (εDB l db)) 
  ==. PgHole (εDB l (εDB l db)) 
      ? εDBIdempotent l db 
  ==. PgHole (εDB l db)
  ==. ε l (Pg lc db TException) 
  ==. ε l (eval (Pg lc db (TUpdate n t1 t2 t3))) 
  *** QED 
  where
    t1 = TPred p 
    t2 = TJust (TLabeled l1 v1)
    t3 = TNothing
