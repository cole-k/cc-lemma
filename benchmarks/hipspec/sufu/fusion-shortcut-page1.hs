{-# LANGUAGE DeriveDataTypeable,FlexibleInstances #-}
module Test where

import HipSpec
import Prelude(Eq, Ord, return, div, (-))

data Bool = True | False deriving (Eq, Typeable, Ord)

instance Names Bool where
  names _ = ["var0_0", "var0_1", "var0_2"]

instance Arbitrary Bool where
  arbitrary = sized arb
    where
      arb 0 = frequency
        [
          (1, do
            return True
          ),
          (1, do
            return False
          )
        ]
      arb n = frequency
        [
          (1, do
            return True
          ),
          (1, do
            return False
          )
        ]

instance Partial Bool where
  unlifted True = return True
  unlifted False = return False


data Unit = Null deriving (Eq, Typeable, Ord)

instance Names Unit where
  names _ = ["var0_0", "var0_1", "var0_2"]

instance Arbitrary Unit where
  arbitrary = sized arb
    where
      arb 0 = frequency
        [
          (1, do
            return Null
          )
        ]
      arb n = frequency
        [
          (1, do
            return Null
          )
        ]

instance Partial Unit where
  unlifted Null = return Null


data Nat = Zero | Succ Nat deriving (Eq, Typeable, Ord)

instance Names Nat where
  names _ = ["var0_0", "var0_1", "var0_2"]

instance Arbitrary Nat where
  arbitrary = sized arb
    where
      arb 0 = frequency
        [
          (1, do
            return Zero
          )
        ]
      arb n = frequency
        [
          (1, do
            return Zero
          ),
          (n, do
            let n' = n - 1
            x0 <- arb n'
            return (Succ x0)
          )
        ]

instance Partial Nat where
  unlifted Zero = return Zero
  unlifted (Succ x0) = do
    x0' <- lifted x0
    return (Succ x0')


data List = Nil Unit | Cons Nat List deriving (Eq, Typeable, Ord)

instance Names List where
  names _ = ["var0_0", "var0_1", "var0_2"]

instance Arbitrary List where
  arbitrary = sized arb
    where
      arb 0 = frequency
        [
          (1, do
            x0 <- arbitrary
            return (Nil x0)
          )
        ]
      arb n = frequency
        [
          (1, do
            x0 <- arbitrary
            return (Nil x0)
          ),
          (n, do
            let n' = n - 1
            x0 <- arbitrary
            x1 <- arb n'
            return (Cons x0 x1)
          )
        ]

instance Partial List where
  unlifted (Nil x0) = do
    x0' <- lifted x0
    return (Nil x0')
  unlifted (Cons x0 x1) = do
    x0' <- lifted x0
    x1' <- lifted x1
    return (Cons x0' x1')


data BoolList = Bnil Unit | Bcons Bool BoolList deriving (Eq, Typeable, Ord)

instance Names BoolList where
  names _ = ["var0_0", "var0_1", "var0_2"]

instance Arbitrary BoolList where
  arbitrary = sized arb
    where
      arb 0 = frequency
        [
          (1, do
            x0 <- arbitrary
            return (Bnil x0)
          )
        ]
      arb n = frequency
        [
          (1, do
            x0 <- arbitrary
            return (Bnil x0)
          ),
          (n, do
            let n' = n - 1
            x0 <- arbitrary
            x1 <- arb n'
            return (Bcons x0 x1)
          )
        ]

instance Partial BoolList where
  unlifted (Bnil x0) = do
    x0' <- lifted x0
    return (Bnil x0')
  unlifted (Bcons x0 x1) = do
    x0' <- lifted x0
    x1' <- lifted x1
    return (Bcons x0' x1')


tf1 :: List -> BoolList
tf1 (Nil tv6) = (Bnil Null)
tf1 (Cons tv7 tv8) = (Bcons (p tv7) (tf0 tv8))

tf0 :: List -> BoolList
tf0 tv3 = (tf1 tv3)

map :: List -> BoolList
map tv1 = (tf0 tv1)

geq :: Nat -> Nat -> Bool
geq Zero (Succ x) = False
geq x Zero = True
geq (Succ x) (Succ y) = (geq x y)

p :: Nat -> Bool
p tv9 = (geq Zero tv9)

and :: Bool -> Bool -> Bool
and False x = False
and x False = False
and True True = True

tf3 :: BoolList -> Bool
tf3 (Bnil tv13) = True
tf3 (Bcons tv14 tv15) = (and tv14 (tf2 tv15))

tf2 :: BoolList -> Bool
tf2 tv11 = (tf3 tv11)

all :: BoolList -> Bool
all tv10 = (tf2 tv10)

main :: List -> Bool
main tv16 = (all (map tv16))

lq :: Nat -> Nat -> Bool
lq Zero (Succ x) = True
lq x Zero = False
lq (Succ x) (Succ y) = (lq x y)

tf5 :: List -> Bool
tf5 (Nil tv21) = True
tf5 (Cons tv22 tv23) = (and (tf4 tv23) (lq tv22 (Succ Zero)))

tf4 :: List -> Bool
tf4 tv19 = (tf5 tv19)

mapNew :: List -> Bool
mapNew tv18 = (tf4 tv18)

mainNew :: List -> Bool
mainNew tv24 = (mapNew tv24)

optimize inp0 = (main inp0)=:=(mainNew inp0)
