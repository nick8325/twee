-- | Sequences which are stored compactly in memory
-- by serialising their contents as a @ByteString@.
{-# LANGUAGE DeriveAnyClass #-}
module Data.PackedSequence(PackedSequence, empty, null, size, fromList, toList, uncons) where

import Prelude hiding (null)
import Data.Binary
import Data.Binary.Get
import Data.Binary.Put
import qualified Data.Binary.Sharing as Sharing
import Data.ByteString(ByteString)
import qualified Data.ByteString as BS
import Data.List(unfoldr)
import GHC.Generics

-- | A sequence, stored in a serialised form
data PackedSequence a =
  Seq {-# UNPACK #-} !Int {-# UNPACK #-} !ByteString
  deriving (Eq, Generic, Sharing.Binary)

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
fromList :: Binary a => [a] -> PackedSequence a
fromList xs = Seq (length xs) (BS.toStrict (runPut (mapM_ put xs)))

-- | Convert a sequence into a list.
{-# INLINEABLE toList #-}
toList :: Binary a => PackedSequence a -> [a]
toList = unfoldr uncons

-- | Find and remove the first value from a sequence.
{-# INLINEABLE uncons #-}
uncons :: Binary a => PackedSequence a -> Maybe (a, PackedSequence a)
uncons (Seq 0 _) = Nothing
uncons (Seq n bs) =
  Just $ case runGetOrFail get (BS.fromStrict bs) of
    Left (_, _, err) -> error err
    Right (bs, _, x) -> (x, Seq (n-1) (BS.toStrict bs))
