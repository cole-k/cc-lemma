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


data List = Cons Nat List | Nil Unit deriving (Eq, Typeable, Ord)

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
          (n, do
            let n' = n - 1
            x0 <- arbitrary
            x1 <- arb n'
            return (Cons x0 x1)
          ),
          (1, do
            x0 <- arbitrary
            return (Nil x0)
          )
        ]

instance Partial List where
  unlifted (Cons x0 x1) = do
    x0' <- lifted x0
    x1' <- lifted x1
    return (Cons x0' x1')
  unlifted (Nil x0) = do
    x0' <- lifted x0
    return (Nil x0')


tf1 :: List -> List -> List
tf1 tv4 (Nil tv5) = tv4
tf1 tv4 (Cons tv6 tv7) = (Cons tv6 (tf0 tv7))

tf0 :: List -> List
tf0 tv2 = (tf1 tv2 tv2)

tf2 :: List -> Nat
tf2 tv9 = (mts (tf0 tv9))

singlepass :: List -> Nat
singlepass tv1 = (tf2 tv1)

lq :: Nat -> Nat -> Bool
lq Zero (Succ x) = True
lq x Zero = False
lq (Succ x) (Succ y) = (lq x y)

ite1 :: Bool -> Nat -> Nat -> Nat
ite1 True x y = x
ite1 False x y = y

max :: Nat -> Nat -> Nat
max tv10 tv11 = (ite1 (lq tv10 tv11) tv11 tv10)

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


plus :: Nat -> Nat -> Nat
plus Zero x = x
plus (Succ x) y = (Succ (plus x y))

snd2 :: Tuple2 -> Nat
snd2 (MakeTuple2 x0 x1) = x1

fst2 :: Tuple2 -> Nat
fst2 (MakeTuple2 x0 x1) = x0

tf4 :: List -> Tuple2
tf4 (Nil tv15) = (MakeTuple2 Zero Zero)
tf4 (Cons tv16 tv17) = (MakeTuple2 (max (plus (snd2 (tf3 tv17)) tv16) (fst2 (tf3 tv17))) (plus (snd2 (tf3 tv17)) tv16))

tf3 :: List -> Tuple2
tf3 tv13 = (tf4 tv13)

mts :: List -> Nat
mts tv12 = (fst2 (tf3 tv12))

main :: List -> Nat
main tv18 = (singlepass tv18)

tf6 :: List -> Tuple2
tf6 (Nil tv23) = (MakeTuple2 Zero Zero)
tf6 (Cons tv24 tv25) = (MakeTuple2 (ite1 (lq (plus tv24 (snd2 (tf5 tv25))) (fst2 (tf5 tv25))) (fst2 (tf5 tv25)) (plus tv24 (snd2 (tf5 tv25)))) (plus tv24 (snd2 (tf5 tv25))))

tf5 :: List -> Tuple2
tf5 tv21 = (tf6 tv21)

tf7 :: List -> Nat
tf7 tv26 = (fst2 (tf5 tv26))

singlepassNew :: List -> Nat
singlepassNew tv20 = (tf7 tv20)

mainNew :: List -> Nat
mainNew tv27 = (singlepassNew tv27)

optimize inp0 = (main inp0)=:=(mainNew inp0)
