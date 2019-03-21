{-@ LIQUID "--reflection"  @-}

module Simulations.TUpdateFoundJN where

import ProofCombinators
import Labels 
import Programs 
import Predicates 

import Idempotence 
import EraseTableAnyJN
import LookupTableErase
import LabelUpdateCheckJN (labelUpdateCheckEqJN)
import Simulations.Terms 
import Simulations.UpdateJN
import Simulations.UpdateJNHelper

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

simulationsUpdateFlowsFoundJN l lc db n p l1 v1 t εt
  | not (tableLabel ti `canFlowTo` l )
  =   ε l (eval (ε l (Pg lc db (TUpdate n (TPred p) (TJust (TLabeled l1 v1)) TNothing))))
    ? globals
  ==. ε l (eval (Pg lc (εDB l db)
                  (εTerm l (TUpdate n (TPred p)
                             (TJust (TLabeled l1 v1))
                             TNothing)))) 
  ==. ε l (eval (Pg lc (εDB l db)
                  (TUpdate n (εTerm l (TPred p))
                   (εTerm l (TJust (TLabeled l1 v1)))
                   (εTerm l TNothing))))
  ==. ε l (eval (Pg lc (εDB l db)
                  (TUpdate n (εTerm l (TPred p))
                   (TJust (εTerm l  (TLabeled l1 v1)))
                   TNothing)))
    ? assert (not (εlc' `canFlowTo` l))
    ? assert (not (lc' `canFlowTo` l))
  ==. ε l (eval (Pg lc (εDB l db) (TUpdate n (TPred p)
                                     (TJust (TLabeled l1 εv1))
                                     TNothing)))
      ? εDBIdempotent l db
  ==. (if εa
       then ε l (Pg εlc' (updateDBJN (εDB l db) n p εv1) (TReturn TUnit))
            ? εTableAnyJN l n (εDB l db) p εv1
        ==. ε l (Pg εlc' (εDB l (εDB l db)) (TReturn TUnit))
        ==. ε l (Pg εlc' (εDB l db) (TReturn TUnit))
       else ε l (Pg εlc' (εDB l db) (TReturn TException))
      )

  ==. PgHole (εDB l (εDB l db))
  ==. PgHole (εDB l db)
  ==. (if a
       then ε l (Pg lc' (updateDBJN db n p v1) (TReturn TUnit))
        ==. PgHole (εDB l (updateDBJN db n p v1))
            ? εTableAnyJN l n db p v1
            ? assert (εDB l (updateDBJN db n p v1) == εDB l db)
       else ε l (Pg lc' db TException)
      )
  ==. ε l (eval (Pg lc db (TUpdate n (TPred p) (TJust (TLabeled l1 v1)) TNothing)))  
  *** QED
  | a && εa
  =   ε l (eval (ε l (Pg lc db (TUpdate n (TPred p)
                                  (TJust (TLabeled l1 v1))
                                   TNothing))))
  ==. ε l (eval (Pg lc (εDB l db)
                  (εTerm l (TUpdate n (TPred p)
                             (TJust (TLabeled l1 v1))
                             TNothing))))       
  ==. ε l (eval (Pg lc (εDB l db)
                  (TUpdate n (εTerm l (TPred p))
                   (εTerm l (TJust (TLabeled l1 v1)))
                   (εTerm l TNothing))))
  ==. ε l (eval (Pg lc (εDB l db)
                  (TUpdate n (εTerm l (TPred p))
                   (TJust (εTerm l  (TLabeled l1 v1)))
                   TNothing)))
      -- ? assert (not (εlc' `canFlowTo` l))
      -- ? assert (not (lc' `canFlowTo` l))
  ==. ε l (eval (Pg lc (εDB l db) (TUpdate n (TPred p)
                                     (TJust (TLabeled l1 εv1))
                                     TNothing)))
      ? εDBIdempotent l db
      ? assert (εlc' == lc')
  ==. ε l (Pg εlc' (updateDBJN (εDB l db) n p εv1) (TReturn TUnit))
  ==. (if εlc' `canFlowTo` l
       then Pg εlc' (εDB l (updateDBJN (εDB l db) n p εv1)) (TReturn TUnit)
       else PgHole (εDB l (updateDBJN (εDB l db) n p εv1))
      )
      ? simulationsUpdateJN l lc db n p l1 v1 t εt
  ==. (if lc' `canFlowTo` l
       then Pg lc' (εDB l (updateDBJN db n p v1)) (TReturn TUnit)
       else PgHole (εDB l (updateDBJN db n p v1))
      )
  ==. ε l (Pg lc' (updateDBJN db n p v1) (TReturn TUnit))
  ==. ε l (eval (Pg lc db (TUpdate n (TPred p) (TJust (TLabeled l1 v1)) TNothing)))
  *** QED

  | not a , not εa
  =   ε l (eval (ε l (Pg lc db (TUpdate n (TPred p) (TJust (TLabeled l1 v1)) TNothing))))
    ? globals
  ==. ε l (eval (Pg lc (εDB l db)
                  (εTerm l (TUpdate n (TPred p)
                             (TJust (TLabeled l1 v1))
                             TNothing)))) 
  ==. ε l (eval (Pg lc (εDB l db)
                  (TUpdate n (εTerm l (TPred p))
                   (εTerm l (TJust (TLabeled l1 v1)))
                   (εTerm l TNothing))))
  ==. ε l (eval (Pg lc (εDB l db)
                  (TUpdate n (εTerm l (TPred p))
                   (TJust (εTerm l  (TLabeled l1 v1)))
                   TNothing)))
  ==. ε l (eval (Pg lc (εDB l db) (TUpdate n (TPred p)
                                     (TJust (TLabeled l1 εv1))
                                     TNothing)))
  ==. ε l (Pg εlc' (εDB l db) (TReturn TException))
      ? εDBIdempotent l db
      ? assert (εlc' == lc')
  ==. (if εlc' `canFlowTo` l
       then Pg εlc' (εDB l (εDB l db)) (TReturn TUnit)
       else PgHole (εDB l (εDB l db))
      )

  ==. (if lc' `canFlowTo` l
       then Pg lc' (εDB l db) (TReturn TUnit)
       else PgHole (εDB l db)
      )
  
  ==. ε l (Pg lc' (updateDBJN db n p v1) (TReturn TUnit))
  ==. ε l (eval (Pg lc db (TUpdate n (TPred p) (TJust (TLabeled l1 v1)) TNothing)))
  *** QED  
  | lfTable p t `canFlowTo` l
  =   labelUpdateCheckEqJN l lc p l1 v1 t
    ? assert (a == εa)
  | a && not εa
  =   ε l (eval (ε l (Pg lc db (TUpdate n (TPred p)
                                  (TJust (TLabeled l1 v1))
                                   TNothing))))
  ==. ε l (eval (Pg lc (εDB l db)
                  (εTerm l (TUpdate n (TPred p)
                             (TJust (TLabeled l1 v1))
                             TNothing))))       
  ==. ε l (eval (Pg lc (εDB l db)
                  (TUpdate n (εTerm l (TPred p))
                   (εTerm l (TJust (TLabeled l1 v1)))
                   (εTerm l TNothing))))
  ==. ε l (eval (Pg lc (εDB l db)
                  (TUpdate n (εTerm l (TPred p))
                   (TJust (εTerm l  (TLabeled l1 v1)))
                   TNothing)))
      
  ==. ε l (eval (Pg lc (εDB l db) (TUpdate n (TPred p)
                                     (TJust (TLabeled l1 εv1))
                                     TNothing)))
      ? εDBIdempotent l db
      ? assert (εlc' == lc')
      ? assert (not (εlc' `canFlowTo` l))
      ? simulationsUpdateJNF1Flow' l lc db n p l1 v1 t εt
  ==. ε l (Pg εlc' (εDB l db) (TReturn TException))
  ==. PgHole (εDB l (εDB l db) )
  ==. PgHole (εDB l db)

  ==. PgHole (εDB l (updateDBJN db n p v1))
  ==. ε l (Pg lc' (updateDBJN db n p v1) (TReturn TUnit))
  ==. ε l (eval (Pg lc db (TUpdate n (TPred p) (TJust (TLabeled l1 v1)) TNothing)))
  *** QED
  | not a && εa

  =   ε l (eval (ε l (Pg lc db (TUpdate n (TPred p)
                                  (TJust (TLabeled l1 v1))
                                   TNothing))))
  ==. ε l (eval (Pg lc (εDB l db)
                  (εTerm l (TUpdate n (TPred p)
                             (TJust (TLabeled l1 v1))
                             TNothing))))       
  ==. ε l (eval (Pg lc (εDB l db)
                  (TUpdate n (εTerm l (TPred p))
                   (εTerm l (TJust (TLabeled l1 v1)))
                   (εTerm l TNothing))))
  ==. ε l (eval (Pg lc (εDB l db)
                  (TUpdate n (εTerm l (TPred p))
                   (TJust (εTerm l  (TLabeled l1 v1)))
                   TNothing)))

  ==. ε l (eval (Pg lc (εDB l db) (TUpdate n (TPred p)
                                     (TJust (TLabeled l1 εv1))
                                     TNothing)))
      ? εDBIdempotent l db
      ? assert (εlc' == lc')
      ? assert (not (εlc' `canFlowTo` l))
      ? simulationsUpdateJNF1Flow l lc db n p l1 v1 t εt
  ==. ε l (Pg εlc' (updateDBJN (εDB l db) n p εv1) (TReturn TUnit))
  ==. PgHole (εDB l (updateDBJN (εDB l db) n p εv1))

  ==. PgHole (εDB l db)
  ==. ε l (Pg lc' db (TReturn TException))
  ==. ε l (eval (Pg lc db (TUpdate n (TPred p) (TJust (TLabeled l1 v1)) TNothing)))
  *** QED

  
  where
    ti = tableInfo t

    a  = updateLabelCheckJN lc t  p l1 v1
    εa = updateLabelCheckJN lc εt p l1 εv1 

    lc'  = lc `join` ((l1
                         `join` (lfTable p t))
                         `join` tableLabel ti)
    εlc' = lc `join` ((l1
                         `join` (lfTable p εt))
                         `join` tableLabel ti)

    εv1  = if l1 `canFlowTo` l then (εTerm l v1) else THole

    globals = assert (Just t  == lookupTable n db)
              -- ? tableLabelCanFlowLabelPred p t
              ? assert (field1Label ti `canFlowTo` tableLabel ti)
              ? lawFlowTransitivity (field1Label ti) (tableLabel ti) l
              
              ? lfTableEq l p t
              -- ? lfTableImplies l p t

              ? joinCanFlowTo lc ((l1 `join` (lfTable p t)) `join` tableLabel ti) l

              ? joinCanFlowTo (l1 `join` (lfTable p t)) (tableLabel ti) l
              ? joinCanFlowTo l1 (lfTable p t) l


              ? joinCanFlowTo lc ((l1 `join` (lfTable p εt)) `join` tableLabel ti) l

              ? joinCanFlowTo (l1 `join` (lfTable p εt)) (tableLabel ti) l
              ? joinCanFlowTo l1 (lfTable p εt) l              
              
              ? lfTableEq l p εt

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
      ? lfRowsEq l p ti rs
  ==. lfRows p ti (εRows l ti rs)
  ==. lfTable p (Table ti (εRows l ti rs))
  ==. lfTable p (εTable l t)
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


{-@ 
lfRowsEq 
  :: (Eq l, Label l)
  => l:l 
  -> p:Pred 
  -> ti:{TInfo l | canFlowTo (field1Label ti) l }
  -> rs:[Row l] 
  -> { lfRows p ti rs == lfRows p ti (εRows l ti rs) }
  / [len rs] @-}
lfRowsEq :: (Eq l, Label l) => l -> Pred -> TInfo l -> [Row l] -> Proof 
lfRowsEq l p ti []
  =   lfRows p ti (εRows l ti []) 
  ==. bot 
  ==. lfRows p ti [] 
  *** QED 

lfRowsEq l p ti (r@(Row k o1 o2):rs)
  =   lfRows p ti (εRows l ti (r:rs))
  ==. lfRows p ti (εRow l ti r:εRows l ti rs)
  ==. lfRow p ti (εRow l ti r) `join` lfRows p ti (εRows l ti rs)
      ? assert (canFlowTo (field1Label ti) l)
      ? assert (εTerm l o1 == o1)
      ? assert ((rowField1 r) == (rowField1 (εRow l ti r))) 
      ? lfRowsEq l p ti rs  
  ==. lfRow p ti r `join` lfRows p ti rs
  ==. lfRows p ti (r:rs)
  *** QED 
