{-@ LIQUID "--exactdc"                                  @-}
{-@ LIQUID "--higherorder"                              @-}
{-@ LIQUID "--trustinternals"                           @-}

{-@ LIQUID "--automatic-instances=liquidinstanceslocal" @-}

{-# LANGUAGE CPP                                        #-}

module LLIO where

import ProofCombinators

import Language
import Label
import Programs
import MetaFunctions

import Determinacy
import Simulations

-- Hack for liquidhaskell#1102
_hackImport  :: Term 
_hackImport = THole 

εEquiv :: Label -> Program -> Program -> Bool 
{-@ reflect εEquiv @-}
εEquiv l k k' = ε l k == ε l k'

-- NV QUESTION: Is this enought or should I set up existentials properly?
{-@ 
nonInterference
   :: l:Label  
   -> k1:{Program  | terminates k1} 
   -> k2:{Program  | terminates k2}
   -> {v:Proof     | εEquiv l k1 k2}
   -> k1':{Program | evalProgram k1 == k1' } 
   -> k2':{Program | evalProgram k2 == k2' } 
   -> {v:Proof     | εEquiv l k1' k2'}  
 @-}

nonInterference
   :: Label 
   -> Program -> Program -> Proof
   -> Program -> Program 
   -> Proof  
nonInterference l k1 k2 equivProof k1' k2'  
  = case simulationsCorollary k1 k1' l trivial of 
      p1 -> {- p1 proves evalEraseProgram (ε l k1) l = Pair n1' (ε l k1') -}
                    case simulationsCorollary k2 k2' l trivial of 
                      p2 -> {- p2 proves evalEraseProgram (ε l k2) l = Pair n2' (ε l k2') -}
                                        εEquiv l k1' k2'
                                    ==. ε l k1' == ε l k2'
                                    ==. True  
                                      ? 
                                      (
                                        (ε l k1 == ε l k2 ==. εEquiv l k1 k2 ? equivProof *** QED ) 
                                        &&& 
                                        determinacy l (ε l k1) 
                                                 (ε l k1') 
                                                 (ε l k2') 
                                                 (p1 &&& p2)
                                      )
                                    *** QED 
