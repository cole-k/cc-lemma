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


data List = Cons Bool List | Nil Unit deriving (Eq, Typeable, Ord)

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


tf2 :: List -> Nat
tf2 tv9 = (count10p (tf0 tv9))

singlepass :: List -> Nat
singlepass tv1 = (tf2 tv1)

and :: Bool -> Bool -> Bool
and False x = False
and x False = False
and True True = True

ite1 :: Bool -> Nat -> Nat -> Nat
ite1 True x y = x
ite1 False x y = y

not :: Bool -> Bool
not True = False
not False = True

or :: Bool -> Bool -> Bool
or True x = True
or x True = True
or False False = False

plus :: Nat -> Nat -> Nat
plus Zero x = x
plus (Succ x) y = (Succ (plus x y))

tf4 :: Bool -> Bool -> List -> Nat
tf4 tv15 tv16 (Nil tv17) = Zero
tf4 tv15 tv16 (Cons tv18 tv19) = (plus (ite1 (and tv16 tv18) (Succ Zero) Zero) (tf3 tv18 (and (not tv18) (or tv15 tv16)) tv19))

tf3 :: Bool -> Bool -> List -> Nat
tf3 tv11 tv12 tv13 = (tf4 tv11 tv12 tv13)

count10p :: List -> Nat
count10p tv10 = (tf3 False False tv10)

main :: List -> Nat
main tv20 = (singlepass tv20)

tf5 :: List -> Bool
tf5 (Nil tv22) = False
tf5 (Cons tv23 tv24) = tv23

alhead :: List -> Bool
alhead tv21 = (tf5 tv21)

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


nateq :: Nat -> Nat -> Bool
nateq Zero Zero = True
nateq Zero (Succ x) = False
nateq (Succ x) Zero = False
nateq (Succ x) (Succ y) = (nateq x y)

fst2 :: Tuple2 -> Nat
fst2 (MakeTuple2 x0 x1) = x0

snd2 :: Tuple2 -> Nat
snd2 (MakeTuple2 x0 x1) = x1

tf7 :: List -> Tuple2
tf7 (Nil tv29) = (MakeTuple2 Zero Zero)
tf7 (Cons tv30 tv31) = (MakeTuple2 (ite1 (or (or (not tv30) (nateq (fst2 (tf6 tv31)) (snd2 (tf6 tv31)))) (alhead tv31)) (fst2 (tf6 tv31)) (plus (Succ Zero) (fst2 (tf6 tv31)))) (ite1 (not tv30) (snd2 (tf6 tv31)) (plus (Succ Zero) (snd2 (tf6 tv31)))))

tf6 :: List -> Tuple2
tf6 tv27 = (tf7 tv27)

tf8 :: List -> Nat
tf8 tv32 = (fst2 (tf6 tv32))

singlepassNew :: List -> Nat
singlepassNew tv26 = (tf8 tv26)

mainNew :: List -> Nat
mainNew tv33 = (singlepassNew tv33)

optimize inp0 = (main inp0)=:=(mainNew inp0)
