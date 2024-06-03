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


data Tree = Leaf Nat | Branch Tree Tree deriving (Eq, Typeable, Ord)

instance Names Tree where
  names _ = ["var0_0", "var0_1", "var0_2"]

instance Arbitrary Tree where
  arbitrary = sized arb
    where
      arb 0 = frequency
        [
          (1, do
            x0 <- arbitrary
            return (Leaf x0)
          )
        ]
      arb n = frequency
        [
          (1, do
            x0 <- arbitrary
            return (Leaf x0)
          ),
          (n, do
            let n' = n `div` 2
            x0 <- arb n'
            x1 <- arb n'
            return (Branch x0 x1)
          )
        ]

instance Partial Tree where
  unlifted (Leaf x0) = do
    x0' <- lifted x0
    return (Leaf x0')
  unlifted (Branch x0 x1) = do
    x0' <- lifted x0
    x1' <- lifted x1
    return (Branch x0' x1')


plus :: Nat -> Nat -> Nat
plus Zero x = x
plus (Succ x) y = (Succ (plus x y))

times :: Nat -> Nat -> Nat
times Zero x = Zero
times (Succ x) y = (plus (times x y) y)

square :: Nat -> Nat
square tv0 = (times tv0 tv0)

tf1 :: Tree -> Tree
tf1 (Leaf tv4) = (Leaf (square tv4))
tf1 (Branch tv5 tv6) = (Branch (tf0 tv5) (tf0 tv6))

tf0 :: Tree -> Tree
tf0 tv2 = (tf1 tv2)

squaretr :: Tree -> Tree
squaretr tv1 = (tf0 tv1)

tf3 :: Tree -> Nat
tf3 (Leaf tv10) = tv10
tf3 (Branch tv11 tv12) = (plus (tf2 tv11) (tf2 tv12))

tf2 :: Tree -> Nat
tf2 tv8 = (tf3 tv8)

sumtr :: Tree -> Nat
sumtr tv7 = (tf2 tv7)

main :: Tree -> Nat
main tv13 = (sumtr (squaretr tv13))

tf5 :: Tree -> Nat
tf5 (Leaf tv17) = (square tv17)
tf5 (Branch tv18 tv19) = (plus (tf4 tv18) (tf4 tv19))

tf4 :: Tree -> Nat
tf4 tv15 = (tf5 tv15)

squaretrNew :: Tree -> Nat
squaretrNew tv14 = (tf4 tv14)

mainNew :: Tree -> Nat
mainNew tv20 = (squaretrNew tv20)

optimize inp0 = (main inp0)=:=(mainNew inp0)
