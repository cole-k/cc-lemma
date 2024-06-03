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

tf5 :: List -> List
tf5 (Nil tv18) = (Nil Null)
tf5 (Cons tv19 tv20) = (Cons tv19 (tf4 tv20))

tf4 :: List -> List
tf4 tv16 = (tf5 tv16)

listrepr :: List -> List
listrepr tv15 = (tf4 tv15)

plus :: Nat -> Nat -> Nat
plus Zero x = x
plus (Succ x) y = (Succ (plus x y))

tf7 :: List -> Nat
tf7 (Nil tv24) = Zero
tf7 (Cons tv25 tv26) = (plus tv25 (tf6 tv26))

tf6 :: List -> Nat
tf6 tv22 = (tf7 tv22)

sum :: List -> Nat
sum tv21 = (tf6 tv21)

tf8 :: Zipper -> List
tf8 (Zip tv28 tv29) = (concat (rev tv28) (listrepr tv29))

repr :: Zipper -> List
repr tv27 = (tf8 tv27)

main :: Zipper -> Nat
main tv30 = (sum (repr tv30))

tf10 :: List -> Nat
tf10 (Nil tv34) = Zero
tf10 (Cons tv35 tv36) = (plus tv35 (tf9 tv36))

tf9 :: List -> Nat
tf9 tv32 = (tf10 tv32)

revNew :: List -> Nat
revNew tv31 = (tf9 tv31)

tf12 :: List -> Nat
tf12 (Nil tv40) = Zero
tf12 (Cons tv41 tv42) = (plus (tf11 tv42) tv41)

tf11 :: List -> Nat
tf11 tv38 = (tf12 tv38)

listreprNew :: List -> Nat
listreprNew tv37 = (tf11 tv37)

tf13 :: Zipper -> Nat
tf13 (Zip tv44 tv45) = (plus (revNew tv44) (listreprNew tv45))

reprNew :: Zipper -> Nat
reprNew tv43 = (tf13 tv43)

mainNew :: Zipper -> Nat
mainNew tv46 = (reprNew tv46)

optimize inp0 = (main inp0)=:=(mainNew inp0)
