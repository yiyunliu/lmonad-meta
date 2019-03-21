{-# LANGUAGE BangPatterns #-}

module Main where

import RunLiquid

main :: IO ()
main = liquid [
    "EraseTableAny.hs"
  , "EraseTableAnyNothingJust.hs"
  , "EraseTableAnyJN.hs"
  , "LabelUpdateCheck.hs"
  , "LabelUpdateCheckNothingJust.hs"
  , "LabelUpdateCheckJN.hs"
  , "UpdateNothingJustHelper.hs"
  , "UpdateJNHelper.hs"
  , "Simulations/UpdateAny.hs"
  , "Simulations/UpdateAnyNothingJust.hs"
  , "Simulations/UpdateAnyJN.hs"
  , "Simulations/UpdateRowBySMT.hs"
  , "Simulations/UpdateOne.hs"
  , "Simulations/Update.hs"
  , "Simulations/UpdateNothingJust.hs"
  , "Simulations/UpdateJN.hs"
  , "Simulations/TUpdateFound.hs"
  , "Simulations/TUpdateFoundNothingJust.hs"
  , "Simulations/TUpdateFoundJN.hs"
  , "Simulations/TUpdate.hs"
  ]
