-- Church-encoded lists. Used in Twee.CP to make sure that fusion happens.
{-# LANGUAGE Rank2Types, BangPatterns #-}
module Twee.ChurchList where

import Prelude(Functor(..), Applicative(..), Monad(..), Bool(..), Maybe(..), (.), ($), id)
import qualified Prelude
import GHC.Magic(oneShot)
import GHC.Exts(build)
import Control.Monad(MonadPlus(..), liftM2)
import Control.Applicative(Alternative(..))

newtype ChurchList a =
  ChurchList (forall b. (a -> b -> b) -> b -> b)

{-# INLINE foldr #-}
foldr :: (a -> b -> b) -> b -> ChurchList a -> b
foldr op e (ChurchList f) = eta (f op (eta e))
  -- Using eta here seems to help with eta-expanding foldl'

{-# INLINE[0] eta #-}
eta :: a -> a
eta x = x
{-# RULES "eta" forall f. eta f = \x -> f x #-}

{-# INLINE nil #-}
nil :: ChurchList a
nil = ChurchList (\_ n -> n)

{-# INLINE unit #-}
unit :: a -> ChurchList a
unit x = ChurchList (\c n -> c x n)

{-# INLINE cons #-}
cons :: a -> ChurchList a -> ChurchList a
cons x xs = ChurchList (\c n -> c x (foldr c n xs))

{-# INLINE append #-}
append :: ChurchList a -> ChurchList a -> ChurchList a
append xs ys = ChurchList (\c n -> foldr c (foldr c n ys) xs)

{-# INLINE join #-}
join :: ChurchList (ChurchList a) -> ChurchList a
join xss = ChurchList (\c n -> foldr (\xs ys -> foldr c ys xs) n xss)

instance Functor ChurchList where
  {-# INLINE fmap #-}
  fmap f xs = ChurchList (\c n -> foldr (c . f) n xs)

instance Applicative ChurchList where
  {-# INLINE pure #-}
  pure = return
  {-# INLINE (<*>) #-}
  (<*>) = liftM2 ($)

instance Monad ChurchList where
  {-# INLINE return #-}
  return = unit
  {-# INLINE (>>=) #-}
  xs >>= f = join (fmap f xs)

instance Alternative ChurchList where
  {-# INLINE empty #-}
  empty = nil
  {-# INLINE (<|>) #-}
  (<|>) = append

instance MonadPlus ChurchList where
  {-# INLINE mzero #-}
  mzero = empty
  {-# INLINE mplus #-}
  mplus = (<|>)

{-# INLINE fromList #-}
fromList :: [a] -> ChurchList a
fromList xs = ChurchList (\c n -> Prelude.foldr c n xs)

{-# INLINE toList #-}
toList :: ChurchList a -> [a]
toList (ChurchList f) = build f

{-# INLINE foldl' #-}
foldl' :: (b -> a -> b) -> b -> ChurchList a -> b
foldl' op e xs =
  foldr (\x f -> oneShot (\ (!acc) -> f (op acc x))) id xs e

{-# INLINE filter #-}
filter :: (a -> Bool) -> ChurchList a -> ChurchList a
filter p xs =
  ChurchList $ \c n ->
    let            
      {-# INLINE op #-}
      op x xs = if p x then c x xs else xs
    in
      foldr op n xs

{-# INLINE fromMaybe #-}
fromMaybe :: Maybe a -> ChurchList a
fromMaybe Nothing = nil
fromMaybe (Just x) = unit x
