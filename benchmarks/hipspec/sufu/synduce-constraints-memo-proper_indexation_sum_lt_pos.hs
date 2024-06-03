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


data IDList = Inil Unit | Icons Nat Nat IDList deriving (Eq, Typeable, Ord)

instance Names IDList where
  names _ = ["var0_0", "var0_1", "var0_2"]

instance Arbitrary IDList where
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

instance Partial IDList where
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

tf1 :: IDList -> Nat
tf1 (Inil tv3) = Zero
tf1 (Icons tv4 tv5 tv6) = (plus (Succ Zero) (tf0 tv6))

tf0 :: IDList -> Nat
tf0 tv1 = (tf1 tv1)

length :: IDList -> Nat
length tv0 = (tf0 tv0)

and :: Bool -> Bool -> Bool
and False x = False
and x False = False
and True True = True

nateq :: Nat -> Nat -> Bool
nateq Zero Zero = True
nateq Zero (Succ x) = False
nateq (Succ x) Zero = False
nateq (Succ x) (Succ y) = (nateq x y)

tf3 :: IDList -> Bool
tf3 (Inil tv10) = True
tf3 (Icons tv11 tv12 tv13) = (and (tf2 tv13) (nateq tv12 (length tv13)))

tf2 :: IDList -> Bool
tf2 tv8 = (tf3 tv8)

isindexed :: IDList -> Bool
isindexed tv7 = (tf2 tv7)

tf5 :: IDList -> List
tf5 (Inil tv17) = (Nil Null)
tf5 (Icons tv18 tv19 tv20) = (Cons tv18 (tf4 tv20))

tf4 :: IDList -> List
tf4 tv15 = (tf5 tv15)

repr :: IDList -> List
repr tv14 = (tf4 tv14)

tf7 :: List -> Nat
tf7 (Nil tv24) = Zero
tf7 (Cons tv25 tv26) = (plus (Succ Zero) (tf6 tv26))

tf6 :: List -> Nat
tf6 tv22 = (tf7 tv22)

len :: List -> Nat
len tv21 = (tf6 tv21)

gq :: Nat -> Nat -> Bool
gq Zero x = False
gq (Succ x) Zero = True
gq (Succ x) (Succ y) = (gq x y)

ite2 :: Bool -> Nat -> Nat -> Nat
ite2 True x y = x
ite2 False x y = y

tf9 :: List -> Nat
tf9 (Nil tv30) = Zero
tf9 (Cons tv31 tv32) = (ite2 (gq tv31 (len tv32)) (plus tv31 (tf8 tv32)) (tf8 tv32))

tf8 :: List -> Nat
tf8 tv28 = (tf9 tv28)

spec :: List -> Nat
spec tv27 = (tf8 tv27)

tf11 :: IDList -> IDList -> IDList
tf11 tv36 (Inil tv37) = tv36
tf11 tv36 (Icons tv38 tv39 tv40) = (Icons tv38 tv39 (tf10 tv40))

tf10 :: IDList -> IDList
tf10 tv34 = (tf11 tv34 tv34)

target :: IDList -> IDList
target tv33 = (tf10 tv33)

main :: IDList -> Nat
main tv41 = (ite2 (isindexed tv41) (spec (repr (target tv41))) Zero)

data Tuple3 = MakeTuple3 Nat Nat deriving (Eq, Typeable, Ord)

instance Names Tuple3 where
  names _ = ["var0_0", "var0_1", "var0_2"]

instance Arbitrary Tuple3 where
  arbitrary = sized arb
    where
      arb 0 = frequency
        [
          (1, do
            x0 <- arbitrary
            x1 <- arbitrary
            return (MakeTuple3 x0 x1)
          )
        ]
      arb n = frequency
        [
          (1, do
            x0 <- arbitrary
            x1 <- arbitrary
            return (MakeTuple3 x0 x1)
          )
        ]

instance Partial Tuple3 where
  unlifted (MakeTuple3 x0 x1) = do
    x0' <- lifted x0
    x1' <- lifted x1
    return (MakeTuple3 x0' x1')


leq :: Nat -> Nat -> Bool
leq Zero x = True
leq (Succ x) Zero = False
leq (Succ x) (Succ y) = (leq x y)

snd3 :: Tuple3 -> Nat
snd3 (MakeTuple3 x0 x1) = x1

fst3 :: Tuple3 -> Nat
fst3 (MakeTuple3 x0 x1) = x0

tf13 :: IDList -> Tuple3
tf13 (Inil tv45) = (MakeTuple3 Zero Zero)
tf13 (Icons tv46 tv47 tv48) = (MakeTuple3 (ite2 (leq tv46 (snd3 (tf12 tv48))) (fst3 (tf12 tv48)) (plus tv46 (fst3 (tf12 tv48)))) (plus (snd3 (tf12 tv48)) (Succ Zero)))

tf12 :: IDList -> Tuple3
tf12 tv43 = (tf13 tv43)

targetNew :: IDList -> Tuple3
targetNew tv42 = (tf12 tv42)

mainNew :: IDList -> Nat
mainNew tv49 = (ite2 (isindexed tv49) (fst3 (targetNew tv49)) Zero)

optimize inp0 = (main inp0)=:=(mainNew inp0)
