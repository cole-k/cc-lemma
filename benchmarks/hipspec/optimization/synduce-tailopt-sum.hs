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


plus :: Nat -> Nat -> Nat
plus Zero x = x
plus (Succ x) y = (Succ (plus x y))

tf1 :: List -> Nat
tf1 (Nil tv3) = Zero
tf1 (Cons tv4 tv5) = (plus tv4 (tf0 tv5))

tf0 :: List -> Nat
tf0 tv1 = (tf1 tv1)

spec :: List -> Nat
spec tv0 = (tf0 tv0)

tf3 :: Nat -> List -> List
tf3 tv11 (Nil tv12) = (Cons tv11 (Nil Null))
tf3 tv11 (Cons tv13 tv14) = (Cons tv13 (tf2 tv14 tv11))

tf2 :: List -> Nat -> List
tf2 tv8 tv9 = (tf3 tv9 tv8)

snoc :: List -> Nat -> List
snoc tv6 tv7 = (tf2 tv6 tv7)

tf5 :: List -> List -> List
tf5 tv19 (Nil tv20) = tv19
tf5 tv19 (Cons tv21 tv22) = (tf4 (snoc tv19 tv21) tv22)

tf4 :: List -> List -> List
tf4 tv16 tv17 = (tf5 tv16 tv17)

repr :: List -> List
repr tv15 = (tf4 (Nil Null) tv15)

main :: List -> Nat
main tv23 = (spec (repr tv23))

tf7 :: Nat -> List -> Nat
tf7 tv28 (Nil tv29) = tv28
tf7 tv28 (Cons tv30 tv31) = (tf6 (plus tv28 tv30) tv31)

tf6 :: Nat -> List -> Nat
tf6 tv25 tv26 = (tf7 tv25 tv26)

reprNew :: List -> Nat
reprNew tv24 = (tf6 Zero tv24)

mainNew :: List -> Nat
mainNew tv32 = (reprNew tv32)

optimize inp0 = (main inp0)=:=(mainNew inp0)
