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


data Tree = Nil Unit | Leaf Nat | Node Nat Tree Tree deriving (Eq, Typeable, Ord)

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
          ),
          (1, do
            x0 <- arbitrary
            return (Leaf x0)
          )
        ]
      arb n = frequency
        [
          (1, do
            x0 <- arbitrary
            return (Nil x0)
          ),
          (1, do
            x0 <- arbitrary
            return (Leaf x0)
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
  unlifted (Leaf x0) = do
    x0' <- lifted x0
    return (Leaf x0')
  unlifted (Node x0 x1 x2) = do
    x0' <- lifted x0
    x1' <- lifted x1
    x2' <- lifted x2
    return (Node x0' x1' x2')


plus :: Nat -> Nat -> Nat
plus Zero x = x
plus (Succ x) y = (Succ (plus x y))

tf1 :: Tree -> Nat
tf1 (Nil tv3) = Zero
tf1 (Leaf tv4) = (Succ Zero)
tf1 (Node tv5 tv6 tv7) = (plus (Succ Zero) (plus (tf0 tv6) (tf0 tv7)))

tf0 :: Tree -> Nat
tf0 tv1 = (tf1 tv1)

size :: Tree -> Nat
size tv0 = (tf0 tv0)

and :: Bool -> Bool -> Bool
and False x = False
and x False = False
and True True = True

nateq :: Nat -> Nat -> Bool
nateq Zero Zero = True
nateq Zero (Succ x) = False
nateq (Succ x) Zero = False
nateq (Succ x) (Succ y) = (nateq x y)

tf3 :: Tree -> Bool
tf3 (Node tv11 tv12 tv13) = (and (nateq Zero (size tv13)) (tf2 tv12))
tf3 (Nil tv14) = True
tf3 (Leaf tv15) = True

tf2 :: Tree -> Bool
tf2 tv9 = (tf3 tv9)

emptyright :: Tree -> Bool
emptyright tv8 = (tf2 tv8)

tf5 :: Tree -> Nat
tf5 (Nil tv19) = Zero
tf5 (Leaf tv20) = tv20
tf5 (Node tv21 tv22 tv23) = (plus tv21 (plus (tf4 tv22) (tf4 tv23)))

tf4 :: Tree -> Nat
tf4 tv17 = (tf5 tv17)

spec :: Tree -> Nat
spec tv16 = (tf4 tv16)

tf7 :: Tree -> Tree
tf7 (Nil tv27) = (Nil Null)
tf7 (Leaf tv28) = (Leaf tv28)
tf7 (Node tv29 tv30 tv31) = (Node tv29 (tf6 tv30) tv31)

tf6 :: Tree -> Tree
tf6 tv25 = (tf7 tv25)

target :: Tree -> Tree
target tv24 = (tf6 tv24)

ite1 :: Bool -> Nat -> Nat
ite1 True x = x
ite1 False x = Zero

main :: Tree -> Nat
main tv32 = (ite1 (emptyright tv32) (spec (target tv32)))

tf9 :: Tree -> Nat
tf9 (Nil tv36) = Zero
tf9 (Leaf tv37) = tv37
tf9 (Node tv38 tv39 tv40) = (plus (tf8 tv39) tv38)

tf8 :: Tree -> Nat
tf8 tv34 = (tf9 tv34)

targetNew :: Tree -> Nat
targetNew tv33 = (tf8 tv33)

mainNew :: Tree -> Nat
mainNew tv41 = (ite1 (emptyright tv41) (targetNew tv41))

optimize inp0 = (main inp0)=:=(mainNew inp0)
