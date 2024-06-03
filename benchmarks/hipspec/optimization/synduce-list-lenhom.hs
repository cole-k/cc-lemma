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


data CList = Cnil Unit | Single Nat | Concat CList CList deriving (Eq, Typeable, Ord)

instance Names CList where
  names _ = ["var0_0", "var0_1", "var0_2"]

instance Arbitrary CList where
  arbitrary = sized arb
    where
      arb 0 = frequency
        [
          (1, do
            x0 <- arbitrary
            return (Cnil x0)
          ),
          (1, do
            x0 <- arbitrary
            return (Single x0)
          )
        ]
      arb n = frequency
        [
          (1, do
            x0 <- arbitrary
            return (Cnil x0)
          ),
          (1, do
            x0 <- arbitrary
            return (Single x0)
          ),
          (n, do
            let n' = n `div` 2
            x0 <- arb n'
            x1 <- arb n'
            return (Concat x0 x1)
          )
        ]

instance Partial CList where
  unlifted (Cnil x0) = do
    x0' <- lifted x0
    return (Cnil x0')
  unlifted (Single x0) = do
    x0' <- lifted x0
    return (Single x0')
  unlifted (Concat x0 x1) = do
    x0' <- lifted x0
    x1' <- lifted x1
    return (Concat x0' x1')


plus :: Nat -> Nat -> Nat
plus Zero x = x
plus (Succ x) y = (Succ (plus x y))

tf1 :: List -> Nat
tf1 (Nil tv3) = Zero
tf1 (Cons tv4 tv5) = (plus (Succ Zero) (tf0 tv5))

tf0 :: List -> Nat
tf0 tv1 = (tf1 tv1)

spec :: List -> Nat
spec tv0 = (tf0 tv0)

tf3 :: List -> List -> List
tf3 tv11 (Nil tv12) = tv11
tf3 tv11 (Cons tv13 tv14) = (Cons tv13 (tf2 tv14 tv11))

tf2 :: List -> List -> List
tf2 tv8 tv9 = (tf3 tv9 tv8)

cat :: List -> List -> List
cat tv6 tv7 = (tf2 tv6 tv7)

tf5 :: CList -> List
tf5 (Cnil tv18) = (Nil Null)
tf5 (Single tv19) = (Cons tv19 (Nil Null))
tf5 (Concat tv20 tv21) = (cat (tf4 tv20) (tf4 tv21))

tf4 :: CList -> List
tf4 tv16 = (tf5 tv16)

repr :: CList -> List
repr tv15 = (tf4 tv15)

main :: CList -> Nat
main tv22 = (spec (repr tv22))

tf7 :: CList -> Nat
tf7 (Cnil tv26) = Zero
tf7 (Single tv27) = (Succ Zero)
tf7 (Concat tv28 tv29) = (plus (tf6 tv29) (tf6 tv28))

tf6 :: CList -> Nat
tf6 tv24 = (tf7 tv24)

reprNew :: CList -> Nat
reprNew tv23 = (tf6 tv23)

mainNew :: CList -> Nat
mainNew tv30 = (reprNew tv30)

optimize inp0 = (main inp0)=:=(mainNew inp0)
