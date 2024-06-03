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


lq :: Nat -> Nat -> Bool
lq Zero (Succ x) = True
lq x Zero = False
lq (Succ x) (Succ y) = (lq x y)

ite1 :: Bool -> Nat -> Nat -> Nat
ite1 True x y = x
ite1 False x y = y

max :: Nat -> Nat -> Nat
max tv0 tv1 = (ite1 (lq tv0 tv1) tv1 tv0)

tf1 :: Nat -> Tree -> Nat
tf1 tv6 (Nil tv7) = tv6
tf1 tv6 (Node tv8 tv9 tv10) = (max tv8 (tf0 (tf0 tv6 tv10) tv9))

tf0 :: Nat -> Tree -> Nat
tf0 tv3 tv4 = (tf1 tv3 tv4)

spec :: Tree -> Nat
spec tv2 = (tf0 Zero tv2)

tf3 :: Tree -> Tree
tf3 (Nil tv14) = (Nil Null)
tf3 (Node tv15 tv16 tv17) = (Node tv15 (tf2 tv16) (tf2 tv17))

tf2 :: Tree -> Tree
tf2 tv12 = (tf3 tv12)

repr :: Tree -> Tree
repr tv11 = (tf2 tv11)

main :: Tree -> Nat
main tv18 = (spec (repr tv18))

tf5 :: Tree -> Nat
tf5 (Nil tv22) = Zero
tf5 (Node tv23 tv24 tv25) = (max tv23 (max (tf4 tv25) (tf4 tv24)))

tf4 :: Tree -> Nat
tf4 tv20 = (tf5 tv20)

reprNew :: Tree -> Nat
reprNew tv19 = (tf4 tv19)

mainNew :: Tree -> Nat
mainNew tv26 = (reprNew tv26)

optimize inp0 = (main inp0)=:=(mainNew inp0)
