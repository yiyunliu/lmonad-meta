{-@ LIQUID "--reflection"  @-}

module Simulations.TUpdateFoundNothingJust where

import ProofCombinators
import Labels 
import Programs 
import Predicates 

import Simulations.DeleteHelpers
import Idempotence
import LabelPredImplies
import Simulations.UpdateNothingJustHelper
import EraseTableAnyNothingJust
import LookupTableErase 
import LabelPredEraseEqual
import LabelUpdateCheck
import Simulations.Terms 
import Simulations.UpdateNothingJust
import LabelUpdateCheckNothingJust

import Prelude hiding (Maybe(..), fromJust, isJust)

{-@ simulationsUpdateFlowsFoundNothingJust
  :: Label l => l:l 
  -> lc:{l | canFlowTo lc l }
  -> db:DB l 
  -> n:TName 
  -> p:Pred
  -> l2:l
  -> v2:SDBTerm l
  -> t:{Table l  | Just t == lookupTable n db } 
  -> εt:{Table l | (Just εt == lookupTable n (εDB l db)) && (tableInfo t == tableInfo εt) } 
  -> { ε l (eval (ε l (Pg lc db (TUpdate n (TPred p) TNothing (TJust (TLabeled l2 v2)))))) == ε l (eval (Pg lc db (TUpdate n (TPred p) TNothing (TJust (TLabeled l2 v2))))) } 
  @-}
simulationsUpdateFlowsFoundNothingJust :: (Label l, Eq l) 
  => l -> l -> DB l -> TName -> Pred -> l -> Term l -> Table l -> Table l -> Proof

simulationsUpdateFlowsFoundNothingJust l lc db n p l2 v2 t εt
  | a && εa  && (tableLabel ti `canFlowTo` l )
  =   ε l (eval (ε l (Pg lc db (TUpdate n (TPred p)
                                  TNothing
                                  (TJust (TLabeled l2 v2))))))
  ==. ε l (eval (Pg lc (εDB l db)
                  (εTerm l (TUpdate n (TPred p)
                             TNothing
                             (TJust (TLabeled l2 v2)))))) 
  ==. ε l (eval (Pg lc (εDB l db)
                  (TUpdate n (εTerm l (TPred p))
                   (εTerm l TNothing)
                   (εTerm l (TJust (TLabeled l2 v2))))))
  ==. ε l (eval (Pg lc (εDB l db)
                  (TUpdate n (εTerm l (TPred p))
                   TNothing
                   (TJust (εTerm l  (TLabeled l2 v2))))))
  ==. ε l (eval (Pg lc (εDB l db) (TUpdate n (TPred p)
                                     TNothing
                                     (TJust (TLabeled l2 εv2)))))
  ==. ε l (Pg εlc' (updateDBNothingJust (εDB l db) n p εv2) (TReturn TUnit))
      ? globals
  ==. (if εlc' `canFlowTo` l 
         then Pg εlc' (εDB l (updateDBNothingJust (εDB l db) n p εv2)) (εTerm l (TReturn TUnit))
         else PgHole  (εDB l (updateDBNothingJust (εDB l db) n p εv2))
      )

 -- stuck here (top to bottom)
      
  ==. (if tableLabel ti `canFlowTo` l 
         then Pg εlc' (εDB l (updateDBNothingJust (εDB l db) n p εv2)) (εTerm l (TReturn TUnit))
              ? globals
              -- does not hold
              ? assert (εlc' == lc')
         else PgHole  (εDB l (updateDBNothingJust (εDB l db) n p εv2))
      )
      ? globals 
      ? assert (updateLabelCheckNothingJust lc t p l2 v2)
      ? simulationsUpdateNothingJust l lc db n p l2 v2 t εt 
      ? assert (εDB l (updateDBNothingJust (εDB l db) n p εv2) == εDB l (updateDBNothingJust db n p v2)) 
  ==. (if field1Label ti `canFlowTo` l  
        then Pg lc' (εDB l (updateDBNothingJust db n p v2)) (εTerm l (TReturn TUnit))
        else PgHole (εDB l (updateDBNothingJust db n p v2)))
      ? globals
  ==. (if lc' `canFlowTo` l  
        then Pg lc' (εDB l (updateDBNothingJust db n p v2)) (εTerm l (TReturn TUnit))
        else PgHole (εDB l (updateDBNothingJust db n p v2)))


 --  -- stuck here (bottom to top)
    
  ==. ε l (Pg lc' (updateDBNothingJust db n p v2) (TReturn TUnit))
  ==. ε l (eval (Pg lc db (TUpdate n (TPred p) TNothing (TJust (TLabeled l2 v2)))))
  *** QED
  -- table does not flow
  | a && εa
  =   ε l (eval (ε l (Pg lc db (TUpdate n (TPred p)
                                  TNothing
                                  (TJust (TLabeled l2 v2))))))
  ==. ε l (eval (Pg lc (εDB l db)
                  (εTerm l (TUpdate n (TPred p)
                             TNothing
                             (TJust (TLabeled l2 v2)))))) 
  ==. ε l (eval (Pg lc (εDB l db)
                  (TUpdate n (εTerm l (TPred p))
                   (εTerm l TNothing)
                   (εTerm l (TJust (TLabeled l2 v2))))))
  ==. ε l (eval (Pg lc (εDB l db)
                  (TUpdate n (εTerm l (TPred p))
                   TNothing
                   (TJust (εTerm l  (TLabeled l2 v2))))))
  ==. ε l (eval (Pg lc (εDB l db) (TUpdate n (TPred p)
                                     TNothing
                                     (TJust (TLabeled l2 εv2)))))
  ==. ε l (Pg εlc' (updateDBNothingJust (εDB l db) n p εv2) (TReturn TUnit))
  -- ==. (if εlc' `canFlowTo` l 
  --        then Pg εlc' (εDB l (updateDBNothingJust (εDB l db) n p εv2)) (εTerm l (TReturn TUnit))
  --        else PgHole  (εDB l (updateDBNothingJust (εDB l db) n p εv2))
  --     )
      ? globals
      ? lawFlowTransitivity (tableLabel ti) εlc' l
      ? assert (not (εlc' `canFlowTo` l))
 -- stuck here (top to bottom)

      ? globals 
      ? assert (updateLabelCheckNothingJust lc t p l2 v2)
      ? simulationsUpdateNothingJust l lc db n p l2 v2 t εt 
      ? assert (εDB l (updateDBNothingJust (εDB l db) n p εv2) == εDB l (updateDBNothingJust db n p v2)) 
  ==. (if field1Label ti `canFlowTo` l  
        then Pg lc' (εDB l (updateDBNothingJust db n p v2)) (εTerm l (TReturn TUnit))
        else PgHole (εDB l (updateDBNothingJust db n p v2)))
      ? globals
  ==. (if lc' `canFlowTo` l  
        then Pg lc' (εDB l (updateDBNothingJust db n p v2)) (εTerm l (TReturn TUnit))
        else PgHole (εDB l (updateDBNothingJust db n p v2)))


  -- stuck here (bottom to top)
    
  ==. ε l (Pg lc' (updateDBNothingJust db n p v2) (TReturn TUnit))
  ==. ε l (eval (Pg lc db (TUpdate n (TPred p) TNothing (TJust (TLabeled l2 v2)))))
  *** QED

  
  | not (canFlowTo (tableLabel ti) l)
  -- TUpdateFound.C2: 
  {- The erased always succeds 
     The non erased can succed or fail depending on whether the table is empty or not
  -}
  =   ε l (eval (ε l (Pg lc db (TUpdate n (TPred p) TNothing (TJust (TLabeled l2 v2))))))
  ==. ε l (eval (Pg lc (εDB l db) (εTerm l (TUpdate n (TPred p) TNothing (TJust (TLabeled l2 v2))))))
  ==. ε l (eval (Pg lc (εDB l db) (TUpdate n (εTerm l (TPred p)) (εTerm l TNothing) (εTerm l (TJust (TLabeled l2 v2))))))
  ==. ε l (eval (Pg lc (εDB l db) (TUpdate n (εTerm l (TPred p)) TNothing (TJust ((εTerm l (TLabeled l2 v2)))))))
  ==. ε l (eval (Pg lc (εDB l db) (TUpdate n (TPred p) TNothing (TJust (TLabeled l2 εv2))))) 
  ==. ε l (if εa 
            then Pg εlc' (updateDBNothingJust (εDB l db) n p εv2) (TReturn TUnit)
            else Pg εlc' (εDB l db) (TReturn TException))
      ? globals
      ? use (not (εlc' `canFlowTo` l))
  ==. (if εa 
         then PgHole (εDB l (updateDBNothingJust (εDB l db) n p εv2)) 
         else PgHole (εDB l (εDB l db)))
      ? εTableAnyNothingJust l n (εDB l db) p εv2
  ==. PgHole (εDB l (εDB l db))
       ? εDBIdempotent l db 
  ==. PgHole (εDB l db)
      ? εTableAnyNothingJust l n db p v2
  ==.(if a  
        then PgHole (εDB l (updateDBNothingJust db n p v2))
        else PgHole (εDB l db))
      ? globals
      ? use (not (εlc' `canFlowTo` l))
  ==. ε l (if a 
            then Pg lc' (updateDBNothingJust db n p v2) (TReturn TUnit)
            else Pg lc' db (TReturn TException)) 
  ==. ε l (eval (Pg lc db (TUpdate n (TPred p) TNothing (TJust (TLabeled l2 v2)))))
  *** QED 

  | (a /= εa) && lfTable p t `canFlowTo` l
  =   ε l (eval (ε l (Pg lc db (TUpdate n (TPred p) TNothing (TJust (TLabeled l2 v2))))))
      ? labelUpdateCheckEqNothingJust l lc p l2 v2 t
  *** QED

  
  | a && not εa 
  =   ε l (eval (ε l (Pg lc db (TUpdate n (TPred p) TNothing (TJust (TLabeled l2 v2))))))
      ? globals
      ? assert (εlc' == lc' )
      ? assert (not (lfTable p t `canFlowTo` l))
      ? assert (not (lc' `canFlowTo` l))
  ==. ε l (eval (Pg lc (εDB l db) (εTerm l (TUpdate n (TPred p) TNothing (TJust (TLabeled l2 v2))))))
  ==. ε l (eval (Pg lc (εDB l db) (TUpdate n (εTerm l (TPred p)) (εTerm l TNothing) (εTerm l (TJust (TLabeled l2 v2))))))
  ==. ε l (eval (Pg lc (εDB l db) (TUpdate n (εTerm l (TPred p)) TNothing (TJust (εTerm l (TLabeled l2 v2))))))
  ==. ε l (eval (Pg lc (εDB l db) (TUpdate n (TPred p) TNothing (TJust (TLabeled l2 εv2)))))
  ==. ε l (Pg εlc' (εDB l db) (TReturn TException))
      ? assert (εlc' == lc' )
      ? globals
  ==. PgHole (εDB l (εDB l db))
      ? εDBIdempotent l db
  ==. PgHole (εDB l db)
      -- todo
      ? lawFlowTransitivity (field1Label ti)  (tableLabel ti) l
      ? simulationsUpdateNJF1Flow' l lc db n p l2 v2 t εt
  ==. PgHole (εDB l (updateDBNothingJust db n p v2))
      ? globals  
  ==. ε l (Pg lc' (updateDBNothingJust db n p v2) (TReturn TUnit))
  ==. ε l (eval (Pg lc db (TUpdate n (TPred p) TNothing (TJust (TLabeled l2 v2)))))
  *** QED 



  | not a && εa 
  =   ε l (eval (ε l (Pg lc db (TUpdate n (TPred p) TNothing (TJust (TLabeled l2 v2))))))
      ? globals
      ? assert (εlc' == lc' )
      ? assert (not (lc' `canFlowTo` l))
  ==! ε l (eval (Pg lc (εDB l db) (εTerm l (TUpdate n (TPred p) TNothing (TJust (TLabeled l2 v2)))))) 
  ==! ε l (eval (Pg lc (εDB l db) (TUpdate n (εTerm l (TPred p)) (εTerm l TNothing) (εTerm l (TJust (TLabeled l2 v2))))))
  ==! ε l (eval (Pg lc (εDB l db) (TUpdate n (εTerm l (TPred p)) TNothing (TJust (εTerm l (TLabeled l2 v2)))))) 
  ==! ε l (eval (Pg lc (εDB l db) (TUpdate n (TPred p) TNothing (TJust (TLabeled l2 εv2))))) 
  ==! ε l (Pg εlc' (updateDBNothingJust (εDB l db) n p εv2) (TReturn TUnit))
      ? simulationsUpdateNJF1Flow l lc db n p l2 v2 t εt
      
  ==! PgHole  (εDB l (updateDBNothingJust (εDB l db) n p εv2))

  ==! PgHole (εDB l db) 
  ==! ε l (Pg lc' db (TReturn TException))
  ==! ε l (eval (Pg lc db (TUpdate n (TPred p) TNothing (TJust (TLabeled l2 v2)))))
  *** QED 
  | not a && not εa 
  =   ε l (eval (ε l (Pg lc db (TUpdate n (TPred p) TNothing (TJust (TLabeled l2 v2))))))
  ==. ε l (eval (Pg lc (εDB l db) (εTerm l (TUpdate n (TPred p) TNothing (TJust (TLabeled l2 v2))))))
  ==. ε l (eval (Pg lc (εDB l db) (TUpdate n (εTerm l (TPred p)) (εTerm l TNothing) (εTerm l (TJust (TLabeled l2 v2)))))) 
  ==. ε l (eval (Pg lc (εDB l db) (TUpdate n (εTerm l (TPred p)) TNothing (TJust (εTerm l (TLabeled l2 v2))))))
  ==. ε l (eval (Pg lc (εDB l db) (TUpdate n (TPred p) TNothing (TJust (TLabeled l2 εv2))))) 
  ==. ε l (Pg εlc' (εDB l db) (TReturn TException)) 
      ? assert (lc' == εlc') 
  ==. ε l (Pg lc' (εDB l db) (TReturn TException)) 
  ==. (if lc' `canFlowTo` l 
        then Pg lc' (εDB l (εDB l db)) (εTerm l (TReturn TException))
        else PgHole (εDB l (εDB l db)))
      ? εDBIdempotent l db 
  ==. (if lc' `canFlowTo` l 
        then Pg lc' (εDB l db) (εTerm l (TReturn TException))
        else PgHole (εDB l db))
  ==. ε l (Pg lc' db (TReturn TException))
  ==. ε l (eval (Pg lc db (TUpdate n (TPred p) TNothing (TJust (TLabeled l2 v2)))))
  *** QED


  -- debug start
  | otherwise = ()
  -- debug end
  
  where
    ti = tableInfo t

    a  = updateLabelCheckNothingJust lc t  p l2 v2
    εa = updateLabelCheckNothingJust lc εt p l2 εv2

    lc'  = lc `join` ((field1Label ti `join` lfTable p t) `join` tableLabel ti)
    εlc' = lc `join` ((field1Label ti `join` lfTable p εt) `join` tableLabel ti)

    εv2  = if l2 `canFlowTo` l then (εTerm l v2) else THole

    globals = assert (Just t  == lookupTable n db)
              ? assert (field1Label ti `canFlowTo` tableLabel ti)
              ? lawFlowTransitivity (field1Label ti) (tableLabel ti) l
              
              ? lfTableEq l p t
              
              ? joinCanFlowTo lc ((field1Label ti `join` lfTable p t) `join` tableLabel ti) l
              ? joinCanFlowTo (field1Label ti `join` lfTable p t) (tableLabel ti) l
              ? joinCanFlowTo (field1Label ti) (lfTable p t) l
              
              ? joinCanFlowTo (field1Label ti) (lfTable p t) l


              ? lfTableEq l p εt
              ? joinCanFlowTo lc ((field1Label ti `join` lfTable p εt) `join` tableLabel ti) l
              ? joinCanFlowTo (field1Label ti `join` lfTable p εt) (tableLabel ti) l
              ? joinCanFlowTo (field1Label ti) (lfTable p εt) l
              ? joinCanFlowTo (field1Label ti) (lfTable p εt) l              

              ? joinCanFlowTo (tableLabel ti) (field1Label ti) l
              ? assert (Just εt == lookupTable n (εDB l db)) 
              ? pTable n l db t 
              ? assert (Just (εTable l t) == lookupTable n (εDB l db))

{-@ lfTableEq
  :: (Eq l, Label l)
  => l:l
  -> p:Pred
  -> t:Table l
  -> { (canFlowTo (tableLabel (tableInfo t)) l =>
       lfTable p t = lfTable p (εTable l t)) }
@-}

lfTableEq :: (Eq l, Label l) => l -> Pred -> Table l -> Proof
lfTableEq l p t@(Table ti rs)
  | canFlowTo (tableLabel (tableInfo t)) l
  =   lfTable p t
  ==. lfRows p ti rs
      ? assert (canFlowTo (field1Label ti) (tableLabel ti))
      ? lawFlowTransitivity (field1Label ti) (tableLabel ti) l
      ? LabelUpdateCheckNothingJust.lfRowsEq l p ti rs
  ==! lfRows p ti (εRows l ti rs)
  ==! lfTable p (Table ti (εRows l ti rs))
  ==! lfTable p (εTable l t)
  *** QED
  | otherwise = ()
  

  


{-@ getInv :: ti:TInfo l -> {canFlowTo (field1Label ti) (tableLabel ti)} @-} 
getInv :: TInfo l -> Proof 
getInv (TInfo _ _ _ _ _) = ()
      

pTable :: (Eq l, Label l) => TName -> l -> DB l -> Table l -> Proof 
{-@ pTable :: (Eq l, Label l) =>  n:TName -> l:l -> db:DB l 
    -> t:{Table l | Just t == lookupTable n db && isJust (lookupTable n db) }
    -> {Just (εTable l t) == lookupTable n (εDB l db)} / [len db] @-}
pTable n l [] t = Nothing ==. lookupTable n [] *** QED 
pTable n l db'@(Pair n' t':ts) t | n == n' 
      =   lookupTable n (εDB l (Pair n' t':ts))
      ==. lookupTable n (Pair n' (εTable l t'):εDB l ts)
      ==. Just (εTable l t') 
      ==. Just (εTable l (fromJust (Just t')))
      ==. Just (εTable l (fromJust (lookupTable n (Pair n' t':ts))))
      *** QED 
      
pTable n l db'@(Pair n' t':ts) t 
      =   Just (εTable l (fromJust (lookupTable n (Pair n' t':ts))))
      ==. Just (εTable l (fromJust (lookupTable n ts)))
      ==. lookupTable n (εDB l ts) ? pTable n l ts t 
      ==. lookupTable n (Pair n' (εTable l t'):εDB l ts)
      ==. lookupTable n (εDB l (Pair n' t':ts))
      *** QED 


