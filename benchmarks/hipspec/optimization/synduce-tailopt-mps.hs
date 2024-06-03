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


gq :: Nat -> Nat -> Bool
gq Zero x = False
gq (Succ x) Zero = True
gq (Succ x) (Succ y) = (gq x y)

ite1 :: Bool -> Nat -> Nat -> Nat
ite1 True x y = x
ite1 False x y = y

max :: Nat -> Nat -> Nat
max tv0 tv1 = (ite1 (gq tv0 tv1) tv0 tv1)

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

fst2 :: Tuple2 -> Nat
fst2 (MakeTuple2 x0 x1) = x0

snd2 :: Tuple2 -> Nat
snd2 (MakeTuple2 x0 x1) = x1

tf1 :: List -> Tuple2
tf1 (Nil tv5) = (MakeTuple2 Zero Zero)
tf1 (Cons tv6 tv7) = (MakeTuple2 (plus tv6 (fst2 (tf0 tv7))) (max Zero (plus tv6 (snd2 (tf0 tv7)))))

tf0 :: List -> Tuple2
tf0 tv3 = (tf1 tv3)

spec :: List -> Nat
spec tv2 = (snd2 (tf0 tv2))

tf3 :: Nat -> List -> List
tf3 tv13 (Nil tv14) = (Cons tv13 (Nil Null))
tf3 tv13 (Cons tv15 tv16) = (Cons tv15 (tf2 tv16 tv13))

tf2 :: List -> Nat -> List
tf2 tv10 tv11 = (tf3 tv11 tv10)

snoc :: List -> Nat -> List
snoc tv8 tv9 = (tf2 tv8 tv9)

tf5 :: List -> List -> List
tf5 tv21 (Nil tv22) = tv21
tf5 tv21 (Cons tv23 tv24) = (tf4 (snoc tv21 tv23) tv24)

tf4 :: List -> List -> List
tf4 tv18 tv19 = (tf5 tv18 tv19)

repr :: List -> List
repr tv17 = (tf4 (Nil Null) tv17)

main :: List -> Nat
main tv25 = (spec (repr tv25))

tf7 :: Tuple2 -> List -> Tuple2
tf7 tv30 (Nil tv31) = tv30
tf7 tv30 (Cons tv32 tv33) = (tf6 (MakeTuple2 (max (fst2 tv30) (plus tv32 (snd2 tv30))) (plus tv32 (snd2 tv30))) tv33)

tf6 :: Tuple2 -> List -> Tuple2
tf6 tv27 tv28 = (tf7 tv27 tv28)

reprNew :: List -> Tuple2
reprNew tv26 = (tf6 (MakeTuple2 Zero Zero) tv26)

mainNew :: List -> Nat
mainNew tv34 = (fst2 (reprNew tv34))

optimize inp0 = (main inp0)=:=(mainNew inp0)
