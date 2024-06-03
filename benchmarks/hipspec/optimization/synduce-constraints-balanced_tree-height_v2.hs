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

plus :: Nat -> Nat -> Nat
plus Zero x = x
plus (Succ x) y = (Succ (plus x y))

tf1 :: Tree -> Nat
tf1 (Nil tv5) = Zero
tf1 (Node tv6 tv7 tv8) = (plus (Succ Zero) (max (tf0 tv7) (tf0 tv8)))

tf0 :: Tree -> Nat
tf0 tv3 = (tf1 tv3)

height :: Tree -> Nat
height tv2 = (tf0 tv2)

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
tf3 (Nil tv12) = True
tf3 (Node tv13 tv14 tv15) = (and (and (nateq (height tv14) (height tv15)) (tf2 tv14)) (tf2 tv15))

tf2 :: Tree -> Bool
tf2 tv10 = (tf3 tv10)

balanced :: Tree -> Bool
balanced tv9 = (tf2 tv9)

tf5 :: Tree -> Tree
tf5 (Nil tv19) = (Nil Null)
tf5 (Node tv20 tv21 tv22) = (Node tv20 (tf4 tv21) tv22)

tf4 :: Tree -> Tree
tf4 tv17 = (tf5 tv17)

target :: Tree -> Tree
target tv16 = (tf4 tv16)

main :: Tree -> Nat
main tv23 = (ite1 (balanced tv23) (height (target tv23)) Zero)

tf7 :: Tree -> Nat
tf7 (Nil tv27) = Zero
tf7 (Node tv28 tv29 tv30) = (plus (tf6 tv29) (max (tf6 tv29) (Succ Zero)))

tf6 :: Tree -> Nat
tf6 tv25 = (tf7 tv25)

targetNew :: Tree -> Nat
targetNew tv24 = (tf6 tv24)

mainNew :: Tree -> Nat
mainNew tv31 = (ite1 (balanced tv31) (targetNew tv31) Zero)

optimize inp0 = (main inp0)=:=(mainNew inp0)
