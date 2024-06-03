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

tf1 :: List -> Nat
tf1 (Nil tv5) = Zero
tf1 (Cons tv6 tv7) = (plus tv6 (tf0 tv7))

tf0 :: List -> Nat
tf0 tv3 = (tf1 tv3)

sum :: List -> Nat
sum tv2 = (tf0 tv2)

tf3 :: List -> Nat
tf3 (Nil tv11) = Zero
tf3 (Cons tv12 tv13) = (max (plus tv12 (sum tv13)) (tf2 tv13))

tf2 :: List -> Nat
tf2 tv9 = (tf3 tv9)

mts :: List -> Nat
mts tv8 = (tf2 tv8)

spec :: List -> Nat
spec tv14 = (mts tv14)

tf5 :: List -> List
tf5 (Nil tv18) = (Nil Null)
tf5 (Cons tv19 tv20) = (Cons tv19 (tf4 tv20))

tf4 :: List -> List
tf4 tv16 = (tf5 tv16)

repr :: List -> List
repr tv15 = (tf4 tv15)

main :: List -> Nat
main tv21 = (spec (repr tv21))

data Tuple2 = MakeTuple2 Nat Nat deriving (Eq, Typeable, Ord)

instance Names Tuple2 where
  names _ = ["var0_0", "var0_1", "var0_2"]

instance Arbitrary Tuple2 where
  arbitrary = sized arb
    where
      arb 0 = frequency
        [
          (1, do
            x0 <- arbitrary
            x1 <- arbitrary
            return (MakeTuple2 x0 x1)
          )
        ]
      arb n = frequency
        [
          (1, do
            x0 <- arbitrary
            x1 <- arbitrary
            return (MakeTuple2 x0 x1)
          )
        ]

instance Partial Tuple2 where
  unlifted (MakeTuple2 x0 x1) = do
    x0' <- lifted x0
    x1' <- lifted x1
    return (MakeTuple2 x0' x1')


fst2 :: Tuple2 -> Nat
fst2 (MakeTuple2 x0 x1) = x0

snd2 :: Tuple2 -> Nat
snd2 (MakeTuple2 x0 x1) = x1

tf7 :: List -> Tuple2
tf7 (Nil tv25) = (MakeTuple2 Zero Zero)
tf7 (Cons tv26 tv27) = (MakeTuple2 (max (fst2 (tf6 tv27)) (plus tv26 (snd2 (tf6 tv27)))) (plus tv26 (snd2 (tf6 tv27))))

tf6 :: List -> Tuple2
tf6 tv23 = (tf7 tv23)

reprNew :: List -> Tuple2
reprNew tv22 = (tf6 tv22)

mainNew :: List -> Nat
mainNew tv28 = (fst2 (reprNew tv28))

optimize inp0 = (main inp0)=:=(mainNew inp0)
