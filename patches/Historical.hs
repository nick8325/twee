module Twee.Historical(Historical, now, at, initial, put, modify, tick) where

import Data.Map(Map)
import qualified Data.Map.Strict as Map

data Historical t a =
  Historical {
    now :: !a,
    history :: Map t a }

at :: (Show t, Ord t) => Historical t a -> Maybe t -> a
h `at` Nothing = now h
h `at` Just t =
  case Map.lookup t (history h) of
    Nothing -> error $ "time not found: " ++ show (t, Map.keys (history h))
    Just x -> x

initial :: a -> Historical t a
initial x =
  Historical {
    now = x,
    history = Map.empty }

put :: a -> Historical t a -> Historical t a
put x h = h { now = x }

modify :: (a -> a) -> Historical t a -> Historical t a
modify f h = put (f (now h)) h

tick :: Ord t => t -> Historical t a -> Historical t a
tick t h =
  h {
    history = Map.insert t (now h) (history h) }

