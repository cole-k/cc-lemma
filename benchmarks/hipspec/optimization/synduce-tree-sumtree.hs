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


data Tree = Nil Unit | Node Nat Tree Tree deriving (Eq, Typeable, Ord)

instance Names Tree where
  names _ = ["var0_0", "var0_1", "var0_2"]

instance Arbitrary Tree where
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
            let n' = n `div` 2
            x0 <- arbitrary
            x1 <- arb n'
            x2 <- arb n'
            return (Node x0 x1 x2)
          )
        ]

instance Partial Tree where
  unlifted (Nil x0) = do
    x0' <- lifted x0
    return (Nil x0')
  unlifted (Node x0 x1 x2) = do
    x0' <- lifted x0
    x1' <- lifted x1
    x2' <- lifted x2
    return (Node x0' x1' x2')


plus :: Nat -> Nat -> Nat
plus Zero x = x
plus (Succ x) y = (Succ (plus x y))

tf1 :: Nat -> Tree -> Nat
tf1 tv4 (Nil tv5) = tv4
tf1 tv4 (Node tv6 tv7 tv8) = (tf0 (plus (tf0 tv4 tv7) tv6) tv8)

tf0 :: Nat -> Tree -> Nat
tf0 tv1 tv2 = (tf1 tv1 tv2)

spec :: Tree -> Nat
spec tv0 = (tf0 Zero tv0)

tf3 :: Tree -> Tree
tf3 (Nil tv12) = (Nil Null)
tf3 (Node tv13 tv14 tv15) = (Node tv13 (tf2 tv14) (tf2 tv15))

tf2 :: Tree -> Tree
tf2 tv10 = (tf3 tv10)

repr :: Tree -> Tree
repr tv9 = (tf2 tv9)

main :: Tree -> Nat
main tv16 = (spec (repr tv16))

tf5 :: Tree -> Nat
tf5 (Nil tv20) = Zero
tf5 (Node tv21 tv22 tv23) = (plus (tf4 tv23) (plus (tf4 tv22) tv21))

tf4 :: Tree -> Nat
tf4 tv18 = (tf5 tv18)

reprNew :: Tree -> Nat
reprNew tv17 = (tf4 tv17)

mainNew :: Tree -> Nat
mainNew tv24 = (reprNew tv24)

optimize inp0 = (main inp0)=:=(mainNew inp0)
