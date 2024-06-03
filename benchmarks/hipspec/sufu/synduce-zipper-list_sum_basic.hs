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


data Zipper = Zip List List deriving (Eq, Typeable, Ord)

instance Names Zipper where
  names _ = ["var0_0", "var0_1", "var0_2"]

instance Arbitrary Zipper where
  arbitrary = sized arb
    where
      arb 0 = frequency
        [
          (1, do
            x0 <- arbitrary
            x1 <- arbitrary
            return (Zip x0 x1)
          )
        ]
      arb n = frequency
        [
          (1, do
            x0 <- arbitrary
            x1 <- arbitrary
            return (Zip x0 x1)
          )
        ]

instance Partial Zipper where
  unlifted (Zip x0 x1) = do
    x0' <- lifted x0
    x1' <- lifted x1
    return (Zip x0' x1')


tf1 :: List -> List -> List
tf1 tv5 (Nil tv6) = tv5
tf1 tv5 (Cons tv7 tv8) = (Cons tv7 (tf0 tv8 tv5))

tf0 :: List -> List -> List
tf0 tv2 tv3 = (tf1 tv3 tv2)

concat :: List -> List -> List
concat tv0 tv1 = (tf0 tv0 tv1)

tf3 :: List -> List
tf3 (Nil tv12) = (Nil Null)
tf3 (Cons tv13 tv14) = (concat (tf2 tv14) (Cons tv13 (Nil Null)))

tf2 :: List -> List
tf2 tv10 = (tf3 tv10)

rev :: List -> List
rev tv9 = (tf2 tv9)

plus :: Nat -> Nat -> Nat
plus Zero x = x
plus (Succ x) y = (Succ (plus x y))

tf5 :: List -> Nat
tf5 (Nil tv18) = Zero
tf5 (Cons tv19 tv20) = (plus tv19 (tf4 tv20))

tf4 :: List -> Nat
tf4 tv16 = (tf5 tv16)

sum :: List -> Nat
sum tv15 = (tf4 tv15)

tf6 :: Zipper -> List
tf6 (Zip tv22 tv23) = (concat (rev tv22) tv23)

repr :: Zipper -> List
repr tv21 = (tf6 tv21)

tf8 :: Zipper -> Zipper
tf8 (Zip tv26 tv27) = (Zip tv26 tv27)

tf7 :: Zipper -> Zipper
tf7 tv25 = (tf8 tv25)

target :: Zipper -> Zipper
target tv24 = (tf7 tv24)

main :: Zipper -> Nat
main tv28 = (sum (repr (target tv28)))

tf10 :: Zipper -> Nat
tf10 (Zip tv31 tv32) = (plus (sum tv31) (sum tv32))

tf9 :: Zipper -> Nat
tf9 tv30 = (tf10 tv30)

targetNew :: Zipper -> Nat
targetNew tv29 = (tf9 tv29)

mainNew :: Zipper -> Nat
mainNew tv33 = (targetNew tv33)

optimize inp0 = (main inp0)=:=(mainNew inp0)
