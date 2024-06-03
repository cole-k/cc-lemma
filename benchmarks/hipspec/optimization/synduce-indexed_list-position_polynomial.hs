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


data IndexedList = Inil Unit | Icons Nat Nat IndexedList deriving (Eq, Typeable, Ord)

instance Names IndexedList where
  names _ = ["var0_0", "var0_1", "var0_2"]

instance Arbitrary IndexedList where
  arbitrary = sized arb
    where
      arb 0 = frequency
        [
          (1, do
            x0 <- arbitrary
            return (Inil x0)
          )
        ]
      arb n = frequency
        [
          (1, do
            x0 <- arbitrary
            return (Inil x0)
          ),
          (n, do
            let n' = n - 1
            x0 <- arbitrary
            x1 <- arbitrary
            x2 <- arb n'
            return (Icons x0 x1 x2)
          )
        ]

instance Partial IndexedList where
  unlifted (Inil x0) = do
    x0' <- lifted x0
    return (Inil x0')
  unlifted (Icons x0 x1 x2) = do
    x0' <- lifted x0
    x1' <- lifted x1
    x2' <- lifted x2
    return (Icons x0' x1' x2')


plus :: Nat -> Nat -> Nat
plus Zero x = x
plus (Succ x) y = (Succ (plus x y))

tf1 :: List -> Nat
tf1 (Nil tv3) = Zero
tf1 (Cons tv4 tv5) = (plus (Succ Zero) (tf0 tv5))

tf0 :: List -> Nat
tf0 tv1 = (tf1 tv1)

length :: List -> Nat
length tv0 = (tf0 tv0)

tf3 :: List -> IndexedList
tf3 (Nil tv9) = (Inil Null)
tf3 (Cons tv10 tv11) = (Icons tv10 (length tv11) (tf2 tv11))

tf2 :: List -> IndexedList
tf2 tv7 = (tf3 tv7)

repr :: List -> IndexedList
repr tv6 = (tf2 tv6)

times :: Nat -> Nat -> Nat
times Zero x = Zero
times (Succ x) y = (plus (times x y) y)

tf5 :: IndexedList -> Nat
tf5 (Inil tv15) = Zero
tf5 (Icons tv16 tv17 tv18) = (plus (times tv16 tv17) (tf4 tv18))

tf4 :: IndexedList -> Nat
tf4 tv13 = (tf5 tv13)

spec :: IndexedList -> Nat
spec tv12 = (tf4 tv12)

main :: List -> Nat
main tv19 = (spec (repr tv19))

tf7 :: List -> Nat
tf7 (Nil tv23) = Zero
tf7 (Cons tv24 tv25) = (plus (tf6 tv25) (times (length tv25) tv24))

tf6 :: List -> Nat
tf6 tv21 = (tf7 tv21)

reprNew :: List -> Nat
reprNew tv20 = (tf6 tv20)

mainNew :: List -> Nat
mainNew tv26 = (reprNew tv26)

optimize inp0 = (main inp0)=:=(mainNew inp0)
