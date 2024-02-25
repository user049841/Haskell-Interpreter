{-- Backward lists for maintaining information in contexts. --}
{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
module MinHS.Bwd where

data Bwd a = BEmpty | Bwd a :< a
  deriving (Read, Eq, Show, Functor, Foldable, Traversable)

infixl 5 :<

(<><) :: Bwd a -> [a] -> Bwd a
xs <>< []       = xs
xs <>< (y : ys) = xs :< y <>< ys

infixl 4 <><

dropWhilst :: (a -> Bool) -> Bwd a -> Bwd a
dropWhilst _ BEmpty = BEmpty
dropWhilst f (xs :< x) | f x = dropWhilst f xs
                       | otherwise = xs :< x

takeWhilst :: (a -> Bool) -> Bwd a -> Bwd a
takeWhilst _ BEmpty = BEmpty
takeWhilst f (xs :< x) | f x = takeWhilst f xs :< x
                       | otherwise = BEmpty

span :: (a -> Bool) -> Bwd a -> (Bwd a  , Bwd a)
span f xs = (dropWhilst f xs, takeWhilst f xs)
