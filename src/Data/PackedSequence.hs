-- | Sequences which are stored compactly in memory
-- by serialising their contents as a @ByteString@.
module Data.PackedSequence(PackedSequence, empty, null, size, fromList, toList, uncons) where

import Prelude hiding (null)
import Data.Serialize
import Data.ByteString(ByteString)
import qualified Data.ByteString as BS
import Data.List(unfoldr)

-- | A sequence, stored in a serialised form
data PackedSequence a =
  Seq {-# UNPACK #-} !Int {-# UNPACK #-} !ByteString
  deriving Eq

-- | An empty sequence.
empty :: PackedSequence a
empty = Seq 0 BS.empty

-- | Is a given sequency empty?
null :: PackedSequence a -> Bool
null s = size s == 0

-- | Find the number of items in a sequence.
size :: PackedSequence a -> Int
size (Seq n _) = n

-- | Convert a list into a sequence.
{-# INLINEABLE fromList #-}
fromList :: Serialize a => [a] -> PackedSequence a
fromList xs = Seq (length xs) (runPut (mapM_ put xs))

-- | Convert a sequence into a list.
{-# INLINEABLE toList #-}
toList :: Serialize a => PackedSequence a -> [a]
toList = unfoldr uncons

-- | Find and remove the first value from a sequence.
{-# INLINEABLE uncons #-}
uncons :: Serialize a => PackedSequence a -> Maybe (a, PackedSequence a)
uncons (Seq 0 _) = Nothing
uncons (Seq n bs) =
  Just $ case runGetState get bs 0 of
    Left err -> error err
    Right (x, bs) -> (x, Seq (n-1) bs)
