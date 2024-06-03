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


gq :: Nat -> Nat -> Bool
gq Zero x = False
gq (Succ x) Zero = True
gq (Succ x) (Succ y) = (gq x y)

and :: Bool -> Bool -> Bool
and False x = False
and x False = False
and True True = True

tf1 :: CList -> Bool
tf1 (Cnil tv3) = True
tf1 (Single tv4) = (gq tv4 Zero)
tf1 (Concat tv5 tv6) = (and (tf0 tv5) (tf0 tv6))

tf0 :: CList -> Bool
tf0 tv1 = (tf1 tv1)

allpos :: CList -> Bool
allpos tv0 = (tf0 tv0)

tf3 :: List -> List -> List
tf3 tv11 (Cons tv13 tv14) = (Cons tv13 (tf2 tv14 tv11))
tf3 tv11 (Nil tv15) = tv11

tf2 :: List -> List -> List
tf2 tv9 tv10 = (tf3 tv10 tv9)

cat :: List -> List -> List
cat tv7 tv8 = (tf2 tv7 tv8)

tf5 :: CList -> List
tf5 (Cnil tv19) = (Nil Null)
tf5 (Single tv20) = (Cons tv20 (Nil Null))
tf5 (Concat tv21 tv22) = (cat (tf4 tv21) (tf4 tv22))

tf4 :: CList -> List
tf4 tv17 = (tf5 tv17)

repr :: CList -> List
repr tv16 = (tf4 tv16)

lq :: Nat -> Nat -> Bool
lq Zero (Succ x) = True
lq x Zero = False
lq (Succ x) (Succ y) = (lq x y)

ite2 :: Bool -> Nat -> Nat -> Nat
ite2 True x y = x
ite2 False x y = y

max :: Nat -> Nat
max tv23 = (ite2 (lq tv23 Zero) Zero tv23)

plus :: Nat -> Nat -> Nat
plus Zero x = x
plus (Succ x) y = (Succ (plus x y))

tf7 :: List -> Nat
tf7 (Nil tv28) = Zero
tf7 (Cons tv29 tv30) = (max (plus (tf6 tv30) tv29))

tf6 :: List -> Nat
tf6 tv26 = (tf7 tv26)

spec :: List -> Nat
spec tv25 = (tf6 tv25)

tf9 :: CList -> CList
tf9 (Cnil tv34) = (Cnil Null)
tf9 (Single tv35) = (Single tv35)
tf9 (Concat tv36 tv37) = (Concat (tf8 tv36) (tf8 tv37))

tf8 :: CList -> CList
tf8 tv32 = (tf9 tv32)

target :: CList -> CList
target tv31 = (tf8 tv31)

main :: CList -> Nat
main tv38 = (ite2 (allpos tv38) (spec (repr (target tv38))) Zero)

tf11 :: CList -> Nat
tf11 (Cnil tv42) = Zero
tf11 (Single tv43) = tv43
tf11 (Concat tv44 tv45) = (plus (tf10 tv45) (tf10 tv44))

tf10 :: CList -> Nat
tf10 tv40 = (tf11 tv40)

targetNew :: CList -> Nat
targetNew tv39 = (tf10 tv39)

mainNew :: CList -> Nat
mainNew tv46 = (ite2 (allpos tv46) (targetNew tv46) Zero)

optimize inp0 = (main inp0)=:=(mainNew inp0)
