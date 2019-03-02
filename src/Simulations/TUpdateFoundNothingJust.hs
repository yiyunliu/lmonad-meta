{-@ LIQUID "--reflection"  @-}

module Simulations.TUpdateFoundNothingJust where

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
 --  | a && εa  && (tableLabel ti `canFlowTo` l )
 --  =   ε l (eval (ε l (Pg lc db (TUpdate n (TPred p)
 --                                  TNothing
 --                                  (TJust (TLabeled l2 v2))))))
 --  ==. ε l (eval (Pg lc (εDB l db)
 --                  (εTerm l (TUpdate n (TPred p)
 --                             TNothing
 --                             (TJust (TLabeled l2 v2)))))) 
 --  ==. ε l (eval (Pg lc (εDB l db)
 --                  (TUpdate n (εTerm l (TPred p))
 --                   (εTerm l TNothing)
 --                   (εTerm l (TJust (TLabeled l2 v2))))))
 --  ==. ε l (eval (Pg lc (εDB l db)
 --                  (TUpdate n (εTerm l (TPred p))
 --                   TNothing
 --                   (TJust (εTerm l  (TLabeled l2 v2))))))
 --  ==. ε l (eval (Pg lc (εDB l db) (TUpdate n (TPred p)
 --                                     TNothing
 --                                     (TJust (TLabeled l2 εv2)))))
 --  ==. ε l (Pg εlc' (updateDBNothingJust (εDB l db) n p εv2) (TReturn TUnit))
 --      ? globals
 --  ==. (if εlc' `canFlowTo` l 
 --         then Pg εlc' (εDB l (updateDBNothingJust (εDB l db) n p εv2)) (εTerm l (TReturn TUnit))
 --         else PgHole  (εDB l (updateDBNothingJust (εDB l db) n p εv2))
 --      )

 -- -- stuck here (top to bottom)
      
 --  ==. (if tableLabel ti `canFlowTo` l 
 --         then Pg εlc' (εDB l (updateDBNothingJust (εDB l db) n p εv2)) (εTerm l (TReturn TUnit))
 --              ? globals
 --              -- does not hold
 --              ? assert (εlc' == lc')
 --         else PgHole  (εDB l (updateDBNothingJust (εDB l db) n p εv2))
 --      )
 --      ? globals 
 --      ? assert (updateLabelCheckNothingJust lc t p l2 v2)
 --      ? simulationsUpdateNothingJust l lc db n p l2 v2 t εt 
 --      ? assert (εDB l (updateDBNothingJust (εDB l db) n p εv2) == εDB l (updateDBNothingJust db n p v2)) 
 --  ==. (if field1Label ti `canFlowTo` l  
 --        then Pg lc' (εDB l (updateDBNothingJust db n p v2)) (εTerm l (TReturn TUnit))
 --        else PgHole (εDB l (updateDBNothingJust db n p v2)))
 --      ? globals
 --  ==. (if lc' `canFlowTo` l  
 --        then Pg lc' (εDB l (updateDBNothingJust db n p v2)) (εTerm l (TReturn TUnit))
 --        else PgHole (εDB l (updateDBNothingJust db n p v2)))


 --  -- stuck here (bottom to top)
    
 --  ==. ε l (Pg lc' (updateDBNothingJust db n p v2) (TReturn TUnit))
 --  ==. ε l (eval (Pg lc db (TUpdate n (TPred p) TNothing (TJust (TLabeled l2 v2)))))
 --  *** QED
 --  -- table does not flow
 --  | a && εa
 --  =   ε l (eval (ε l (Pg lc db (TUpdate n (TPred p)
 --                                  TNothing
 --                                  (TJust (TLabeled l2 v2))))))
 --  ==. ε l (eval (Pg lc (εDB l db)
 --                  (εTerm l (TUpdate n (TPred p)
 --                             TNothing
 --                             (TJust (TLabeled l2 v2)))))) 
 --  ==. ε l (eval (Pg lc (εDB l db)
 --                  (TUpdate n (εTerm l (TPred p))
 --                   (εTerm l TNothing)
 --                   (εTerm l (TJust (TLabeled l2 v2))))))
 --  ==. ε l (eval (Pg lc (εDB l db)
 --                  (TUpdate n (εTerm l (TPred p))
 --                   TNothing
 --                   (TJust (εTerm l  (TLabeled l2 v2))))))
 --  ==. ε l (eval (Pg lc (εDB l db) (TUpdate n (TPred p)
 --                                     TNothing
 --                                     (TJust (TLabeled l2 εv2)))))
 --  ==. ε l (Pg εlc' (updateDBNothingJust (εDB l db) n p εv2) (TReturn TUnit))
 --  -- ==. (if εlc' `canFlowTo` l 
 --  --        then Pg εlc' (εDB l (updateDBNothingJust (εDB l db) n p εv2)) (εTerm l (TReturn TUnit))
 --  --        else PgHole  (εDB l (updateDBNothingJust (εDB l db) n p εv2))
 --  --     )
 --      ? globals
 --      ? assert (tableLabel ti `canFlowTo` labelPredTable p t)
 --      ? lawFlowTransitivity (tableLabel ti) εlc' l
 --      ? assert (not (εlc' `canFlowTo` l))
 -- -- stuck here (top to bottom)

 --      ? globals 
 --      ? assert (updateLabelCheckNothingJust lc t p l2 v2)
 --      ? simulationsUpdateNothingJust l lc db n p l2 v2 t εt 
 --      ? assert (εDB l (updateDBNothingJust (εDB l db) n p εv2) == εDB l (updateDBNothingJust db n p v2)) 
 --  ==. (if field1Label ti `canFlowTo` l  
 --        then Pg lc' (εDB l (updateDBNothingJust db n p v2)) (εTerm l (TReturn TUnit))
 --        else PgHole (εDB l (updateDBNothingJust db n p v2)))
 --      ? globals
 --  ==. (if lc' `canFlowTo` l  
 --        then Pg lc' (εDB l (updateDBNothingJust db n p v2)) (εTerm l (TReturn TUnit))
 --        else PgHole (εDB l (updateDBNothingJust db n p v2)))


 --  -- stuck here (bottom to top)
    
 --  ==. ε l (Pg lc' (updateDBNothingJust db n p v2) (TReturn TUnit))
 --  ==. ε l (eval (Pg lc db (TUpdate n (TPred p) TNothing (TJust (TLabeled l2 v2)))))
 --  *** QED

  
 --  | not (canFlowTo (tableLabel ti) l)
 --  -- TUpdateFound.C2: 
 --  {- The erased always succeds 
 --     The non erased can succed or fail depending on whether the table is empty or not
 --  -}
 --  =   ε l (eval (ε l (Pg lc db (TUpdate n (TPred p) TNothing (TJust (TLabeled l2 v2)))))) 
 --  ==. ε l (eval (Pg lc (εDB l db) (εTerm l (TUpdate n (TPred p) TNothing (TJust (TLabeled l2 v2))))))
 --  ==. ε l (eval (Pg lc (εDB l db) (TUpdate n (εTerm l (TPred p)) (εTerm l TNothing) (εTerm l (TJust (TLabeled l2 v2))))))
 --  ==. ε l (eval (Pg lc (εDB l db) (TUpdate n (εTerm l (TPred p)) TNothing (TJust ((εTerm l (TLabeled l2 v2)))))))
 --  ==. ε l (eval (Pg lc (εDB l db) (TUpdate n (TPred p) TNothing (TJust (TLabeled l2 εv2))))) 
 --  ==. ε l (if εa 
 --            then Pg εlc' (updateDBNothingJust (εDB l db) n p εv2) (TReturn TUnit)
 --            else Pg εlc' (εDB l db) (TReturn TException))
 --      ? globals
 --      ? use (not (εlc' `canFlowTo` l))
 --  ==. (if εa 
 --         then PgHole (εDB l (updateDBNothingJust (εDB l db) n p εv2)) 
 --         else PgHole (εDB l (εDB l db)))
 --      ? εTableAnyNothingJust l n (εDB l db) p εv2
 --  ==. PgHole (εDB l (εDB l db))
 --       ? εDBIdempotent l db 
 --  ==. PgHole (εDB l db)
 --      ? εTableAnyNothingJust l n db p v2
 --  ==.(if a  
 --        then PgHole (εDB l (updateDBNothingJust db n p v2))
 --        else PgHole (εDB l db))
 --      ? globals
 --      ? use (not (εlc' `canFlowTo` l))
 --  ==. ε l (if a 
 --            then Pg lc' (updateDBNothingJust db n p v2) (TReturn TUnit)
 --            else Pg lc' db (TReturn TException)) 
 --  ==. ε l (eval (Pg lc db (TUpdate n (TPred p) TNothing (TJust (TLabeled l2 v2)))))
 --  *** QED 

  | (a /= εa) && labelPredTable p t `canFlowTo` l
  =   ε l (eval (ε l (Pg lc db (TUpdate n (TPred p) TNothing (TJust (TLabeled l2 v2))))))
      ? assume (tableLabel ti `canFlowTo` l) 
      ? labelUpdateCheckEqNothingJust l lc p l2 v2 t
  *** QED

  
  | a && not εa 
  =   ε l (eval (ε l (Pg lc db (TUpdate n (TPred p) TNothing (TJust (TLabeled l2 v2))))))
      -- -- debug
      ?assume (tableLabel ti `canFlowTo` l)
      -- -- debug
      ? globals
      ? assert (εlc' == lc' )
      ? assert (not (labelPredTable p t `canFlowTo` l))
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
      ? assume ((εDB l (updateDBNothingJust db n p v2)) == (εDB l db))
  ==. PgHole (εDB l (updateDBNothingJust db n p v2))
      ? globals  
  ==. ε l (Pg lc' (updateDBNothingJust db n p v2) (TReturn TUnit))
  ==. ε l (eval (Pg lc db (TUpdate n (TPred p) TNothing (TJust (TLabeled l2 v2)))))
  *** QED 



  | not a && εa 
  =   ε l (eval (ε l (Pg lc db (TUpdate n (TPred p) TNothing (TJust (TLabeled l2 v2))))))
     ? assume (tableLabel ti `canFlowTo` l)
      ? globals
      ? assert (εlc' == lc' )
      ? assert (not (labelPredTable p t `canFlowTo` l))
      ? assert (not (lc' `canFlowTo` l))
  ==! ε l (eval (Pg lc (εDB l db) (εTerm l (TUpdate n (TPred p) TNothing (TJust (TLabeled l2 v2)))))) 
  ==! ε l (eval (Pg lc (εDB l db) (TUpdate n (εTerm l (TPred p)) (εTerm l TNothing) (εTerm l (TJust (TLabeled l2 v2))))))
  ==! ε l (eval (Pg lc (εDB l db) (TUpdate n (εTerm l (TPred p)) TNothing (TJust (εTerm l (TLabeled l2 v2)))))) 
  ==! ε l (eval (Pg lc (εDB l db) (TUpdate n (TPred p) TNothing (TJust (TLabeled l2 εv2))))) 
  ==! ε l (Pg εlc' (updateDBNothingJust (εDB l db) n p εv2) (TReturn TUnit))
        ? assume ((εDB l (updateDBNothingJust (εDB l db) n p εv2)) == (εDB l db))

      
  ==! PgHole  (εDB l (updateDBNothingJust (εDB l db) n p εv2))

  ==! PgHole (εDB l db) 
  ==! ε l (Pg lc' db (TReturn TException))
  ==! ε l (eval (Pg lc db (TUpdate n (TPred p) TNothing (TJust (TLabeled l2 v2)))))
  *** QED 
  -- | not a && not εa 
  -- =   ε l (eval (ε l (Pg lc db (TUpdate n (TPred p) TNothing (TJust (TLabeled l2 v2)))))) 
  -- ==. ε l (eval (Pg lc (εDB l db) (εTerm l (TUpdate n (TPred p) TNothing (TJust (TLabeled l2 v2))))))
  -- ==. ε l (eval (Pg lc (εDB l db) (TUpdate n (εTerm l (TPred p)) (εTerm l TNothing) (εTerm l (TJust (TLabeled l2 v2)))))) 
  -- ==. ε l (eval (Pg lc (εDB l db) (TUpdate n (εTerm l (TPred p)) TNothing (TJust (εTerm l (TLabeled l2 v2))))))
  -- ==. ε l (eval (Pg lc (εDB l db) (TUpdate n (TPred p) TNothing (TJust (TLabeled l2 εv2))))) 
  -- ==. ε l (Pg εlc' (εDB l db) (TReturn TException)) 
  --     ? assert (lc' == εlc') 
  -- ==. ε l (Pg lc' (εDB l db) (TReturn TException)) 
  -- ==. (if lc' `canFlowTo` l 
  --       then Pg lc' (εDB l (εDB l db)) (εTerm l (TReturn TException))
  --       else PgHole (εDB l (εDB l db)))
  --     ? εDBIdempotent l db 
  -- ==. (if lc' `canFlowTo` l 
  --       then Pg lc' (εDB l db) (εTerm l (TReturn TException))
  --       else PgHole (εDB l db))
  -- ==. ε l (Pg lc' db (TReturn TException))
  -- ==. ε l (eval (Pg lc db (TUpdate n (TPred p) TNothing (TJust (TLabeled l2 v2)))))
  -- *** QED


  -- debug start
  | otherwise = ()
  -- debug end
  
  where
    ti = tableInfo t

    a  = updateLabelCheckNothingJust lc t  p l2 v2
    εa = updateLabelCheckNothingJust lc εt p l2 εv2

    lc'  = lc `join` (field1Label ti `join` labelPredTable p t)
    εlc' = lc `join` (field1Label ti `join` labelPredTable p εt)

    εv2  = if l2 `canFlowTo` l then (εTerm l v2) else THole

    globals = assert (Just t  == lookupTable n db)
              ? tableLabelCanFlowLabelPred p t
              ? assert (field1Label ti `canFlowTo` tableLabel ti)
              ? lawFlowTransitivity (field1Label ti) (tableLabel ti) l
              
              ? labelPredTableEq l p t
              ? labelPredTableImplies l p t
              ? joinCanFlowTo lc (field1Label ti `join` labelPredTable p t) l
              ? joinCanFlowTo (field1Label ti) (labelPredTable p t) l
              -- ? labelPredTableEraseEq l p t
              ? readCanFlowToPred p t
              ? labelPredTableErase l p t


              ? tableLabelCanFlowLabelPred p εt
              ? labelPredTableEq l p εt
              ? labelPredTableImplies l p εt
              ? joinCanFlowTo lc (field1Label (tableInfo εt) `join` labelPredTable p εt) l
              ? joinCanFlowTo (field1Label (tableInfo εt)) (labelPredTable p εt) l
              -- ? labelPredTableEraseEq l p εt
              ? readCanFlowToPred p εt
              ? labelPredTableErase l p εt

              ? joinCanFlowTo (tableLabel ti) (field1Label ti) l
              ? assert (Just εt == lookupTable n (εDB l db)) 
              ? pTable n l db t 
              ? assert (Just (εTable l t) == lookupTable n (εDB l db))


{-@ tableLabelCanFlowLabelPred
  :: (Eq l, Label l)
  => 
   p:Pred
  -> t:Table l
  -> {canFlowTo (tableLabel (tableInfo t)) (labelPredTable p t)}
@-}

tableLabelCanFlowLabelPred :: (Eq l, Label l) => Pred -> Table l -> Proof
tableLabelCanFlowLabelPred p t@(Table ti rs) =
      labelPredTable p t
  ==. labelPredRows p ti rs
  ? tableLabelCanFlowLabelPredRows p ti rs
  *** QED


{-@ tableLabelCanFlowLabelPredRows
  :: (Eq l, Label l)
  => 
   p:Pred
  -> ti:TInfo l
  -> rs:[Row l]
  -> {canFlowTo (tableLabel ti) (labelPredRows p ti rs)}
@-}
tableLabelCanFlowLabelPredRows :: (Eq l, Label l) => Pred -> TInfo l -> [Row l] -> Proof
tableLabelCanFlowLabelPredRows p ti rs
  | not (pDep1 p)
  = (labelPredRows p ti rs ==. tableLabel ti *** QED)
    ? lawFlowReflexivity (tableLabel ti)
    *** QED
tableLabelCanFlowLabelPredRows p ti []
  = (labelPredRows p ti [] ==. (tableLabel ti `join` field1Label ti) *** QED) &&&
    joinCanFlowTo (tableLabel ti ) (field1Label ti ) (labelPredRows p ti [])
    ? lawFlowReflexivity (labelPredRows p ti [])
    *** QED
tableLabelCanFlowLabelPredRows p ti (r:rs)
  = (labelPredRows p ti (r:rs) ==. ((tableLabel ti `join` labelPredRow p ti r) `join` labelPredRows p ti rs) *** QED) &&&
  lawFlowReflexivity (labelPredRows p ti (r:rs))
  ? joinCanFlowTo (tableLabel ti `join` labelPredRow p ti r) (labelPredRows p ti rs) ((tableLabel ti `join` labelPredRow p ti r) `join` labelPredRows p ti rs)
  ? joinCanFlowTo (tableLabel ti) (labelPredRow p ti r) ((tableLabel ti `join` labelPredRow p ti r) `join` labelPredRows p ti rs)

    

{-@ labelPredTableEq
  :: (Eq l, Label l)
  => l:l
  -> p:Pred
  -> t:Table l
  -> { (canFlowTo (tableLabel (tableInfo t)) l =>
       labelPredTable p t = labelPredTable p (εTable l t)) }
@-}

labelPredTableEq :: (Eq l, Label l) => l -> Pred -> Table l -> Proof
labelPredTableEq l p t@(Table ti rs)
  | canFlowTo (tableLabel (tableInfo t)) l
  =   labelPredTable p t
  ==! labelPredRows p ti rs
      ? assert (canFlowTo (field1Label ti) (tableLabel ti))
      ? lawFlowTransitivity (field1Label ti) (tableLabel ti) l
      ? labelPredRowsEq l p ti rs
  ==! labelPredRows p ti (εRows l ti rs)
  ==! labelPredTable p (Table ti (εRows l ti rs))
  ==! labelPredTable p (εTable l t)
  *** QED
  | otherwise = ()
  

  

{-@ labelPredRowsEq
  :: (Eq l, Label l)
  => l:l
  -> p:Pred
  -> ti:{TInfo l | canFlowTo (field1Label ti) l}
  -> rs:[Row l]
  -> {(labelPredRows p ti rs == labelPredRows p ti (εRows l ti rs)) }
@-}
labelPredRowsEq :: (Eq l, Label l) => l -> Pred -> TInfo l -> [Row l] -> Proof
labelPredRowsEq l p ti rs
  | not (pDep1 p)
  = (labelPredRows p ti rs ==. tableLabel ti ==. labelPredRows p ti (εRows l ti rs) *** QED)
    &&& (lawFlowReflexivity (tableLabel ti))

labelPredRowsEq l p ti []
  =   labelPredRows p ti []
      ? joinCanFlowTo (tableLabel ti) (field1Label ti) (labelPredRows p ti [])
  ==. labelPredRows p ti (εRows l ti [])
  *** QED
labelPredRowsEq l p ti (r:rs)
  =   labelPredRows p ti (r:rs)
  ==. (tableLabel ti `join` labelPredRow p ti r) `join` labelPredRows p ti rs
      ? labelPredRowsEq l p ti rs
      ? labelPredRowEq l p ti r
  ==. (tableLabel ti `join` labelPredRow p ti (εRow l ti r)) `join` labelPredRows p ti (εRows l ti rs)
  ==. labelPredRows p ti (εRow l ti r : εRows l ti rs)
  ==. labelPredRows p ti (εRows l ti (r:rs))
  *** QED

{-@ labelPredRowEq
  :: (Eq l, Label l)
  => l:l
  -> p:Pred
  -> ti:{TInfo l | canFlowTo (field1Label ti) l}
  -> r:Row l
  -> {labelPredRow p ti r == labelPredRow p ti (εRow l ti r)}
@-}
labelPredRowEq :: (Eq l, Label l) => l -> Pred -> TInfo l -> Row l -> Proof
labelPredRowEq l p ti r@(Row k o1 o2) 
  | pDep2 p
  =   labelPredRow p ti r
  ==. field1Label ti `join` makeValLabel ti (rowField1 r)
    ? globals
  ==. field1Label ti `join` makeValLabel ti (rowField1 εr)
  ==. labelPredRow p ti εr
  *** QED
  | otherwise
  =   labelPredRow p ti r ==. field1Label ti ==. labelPredRow p ti εr *** QED
  where  εr = εRow l ti r
         globals =   assert (canFlowTo (field1Label ti) l)
                   &&& (rowField1 εr
                    ==. εTerm l o1
                    ==. rowField1 r *** QED)



-- {-@ labelPredTableEq ::
--  (Label l, Eq l) =>
--   l:l ->
--   p:Pred ->
--   t:Table l ->
--   {(not (pDep2 p) => labelPredTable p t == labelPredTable p (εTable l t) )} @-}
-- labelPredTableEq :: (Eq l, Label l) => l -> Pred -> Table l -> Proof
-- labelPredTableEq l p t = 


    

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


