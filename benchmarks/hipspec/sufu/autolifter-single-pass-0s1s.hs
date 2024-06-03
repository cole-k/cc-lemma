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

tf2 :: List -> Bool
tf2 tv9 = (zsos (tf0 tv9))

singlepass :: List -> Bool
singlepass tv1 = (tf2 tv1)

and :: Bool -> Bool -> Bool
and False x = False
and x False = False
and True True = True

or :: Bool -> Bool -> Bool
or True x = True
or x True = True
or False False = False

not :: Bool -> Bool
not True = False
not False = True

ite1 :: Bool -> Bool -> Bool
ite1 True x = x
ite1 False x = False

tf4 :: Bool -> List -> Bool
tf4 tv14 (Nil tv15) = True
tf4 tv14 (Cons tv16 tv17) = (ite1 (or (not tv16) (and tv14 tv16)) (tf3 (and tv14 tv16) tv17))

tf3 :: Bool -> List -> Bool
tf3 tv11 tv12 = (tf4 tv11 tv12)

zsos :: List -> Bool
zsos tv10 = (tf3 True tv10)

main :: List -> Bool
main tv18 = (singlepass tv18)

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


data Tuple2 = MakeTuple2 Bool Nat deriving (Eq, Typeable, Ord)

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


fst2 :: Tuple2 -> Bool
fst2 (MakeTuple2 x0 x1) = x0

nateq :: Nat -> Nat -> Bool
nateq Zero Zero = True
nateq Zero (Succ x) = False
nateq (Succ x) Zero = False
nateq (Succ x) (Succ y) = (nateq x y)

snd2 :: Tuple2 -> Nat
snd2 (MakeTuple2 x0 x1) = x1

plus :: Nat -> Nat -> Nat
plus Zero x = x
plus (Succ x) y = (Succ (plus x y))

ite3 :: Bool -> Nat -> Nat -> Nat
ite3 True x y = x
ite3 False x y = y

tf6 :: List -> Tuple2
tf6 (Nil tv23) = (MakeTuple2 True Zero)
tf6 (Cons tv24 tv25) = (MakeTuple2 (or (and tv24 (fst2 (tf5 tv25))) (nateq (snd2 (tf5 tv25)) Zero)) (ite3 (not tv24) (snd2 (tf5 tv25)) (plus (Succ Zero) (snd2 (tf5 tv25)))))

tf5 :: List -> Tuple2
tf5 tv21 = (tf6 tv21)

tf7 :: List -> Bool
tf7 tv26 = (fst2 (tf5 tv26))

singlepassNew :: List -> Bool
singlepassNew tv20 = (tf7 tv20)

mainNew :: List -> Bool
mainNew tv27 = (singlepassNew tv27)

optimize inp0 = (main inp0)=:=(mainNew inp0)
