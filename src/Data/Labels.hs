-- | Assign integer labels to a fixed-in-advance set of values.
-- Meant for efficient serialisation, so the labels are Int32.

module Data.Labels(Labels, labels, label, value, putLabels, getLabels, putWithLabels, getWithLabels, mapLabels) where

import Twee.Utils
import Data.Map(Map)
import qualified Data.Map.Strict as Map
import Data.IntMap(IntMap)
import qualified Data.IntMap.Strict as IntMap
import Data.Serialize hiding (label)
import Data.Int

data Labels a =
  Labels {
    labelMap :: Map a Int,
    valueMap :: IntMap a }

labels :: Ord a => [a] -> Labels a
labels xs =
  Labels {
    labelMap = Map.fromList (zip ys [0..]),
    valueMap = IntMap.fromList (zip [0..] ys) }
  where
    ys = usort xs

label :: Ord a => a -> Labels a -> Int32
label x labels =
  fromIntegral $ Map.findWithDefault (error "label: not found") x (labelMap labels)

value :: Int32 -> Labels a -> a
value x labels =
  IntMap.findWithDefault (error "value: not found") (fromIntegral x) (valueMap labels)

putLabels :: Putter a -> Putter (Labels a)
putLabels put labels = putListOf put (IntMap.elems (valueMap labels))

getLabels :: Ord a => Get a -> Get (Labels a)
getLabels get = labels <$> getListOf get

putWithLabels :: (Ord a, Serialize a) => [a] -> (Labels a -> Putter b) -> Putter b
putWithLabels xs putter x = do
  let labs = labels xs
  put labs
  putter labs x

getWithLabels :: (Ord a, Serialize a) => (Labels a -> Get b) -> Get b
getWithLabels getter = do
  labs <- get
  getter labs

mapLabels :: (Ord a, Ord b) => (a -> b) -> Labels a -> Labels b
mapLabels f labels =
  Labels {
    labelMap = Map.fromList [(f x, n) | (x, n) <- Map.toList (labelMap labels)],
    valueMap = fmap f (valueMap labels) }

instance (Ord a, Serialize a) => Serialize (Labels a) where
  put = putLabels put
  get = getLabels get
