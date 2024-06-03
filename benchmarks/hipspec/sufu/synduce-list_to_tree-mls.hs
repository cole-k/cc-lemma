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


data Tree = Empty Unit | Node Nat Tree Tree deriving (Eq, Typeable, Ord)

instance Names Tree where
  names _ = ["var0_0", "var0_1", "var0_2"]

instance Arbitrary Tree where
  arbitrary = sized arb
    where
      arb 0 = frequency
        [
          (1, do
            x0 <- arbitrary
            return (Empty x0)
          )
        ]
      arb n = frequency
        [
          (1, do
            x0 <- arbitrary
            return (Empty x0)
          ),
          (n, do
            let n' = n `div` 2
            x0 <- arbitrary
            x1 <- arb n'
            x2 <- arb n'
            return (Node x0 x1 x2)
          )
        ]

instance Partial Tree where
  unlifted (Empty x0) = do
    x0' <- lifted x0
    return (Empty x0')
  unlifted (Node x0 x1 x2) = do
    x0' <- lifted x0
    x1' <- lifted x1
    x2' <- lifted x2
    return (Node x0' x1' x2')


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

ite2 :: Bool -> Nat -> Nat -> Nat
ite2 True x y = x
ite2 False x y = y

max :: Nat -> Nat -> Nat
max tv0 tv1 = (ite2 (lq tv0 tv1) tv1 tv0)

tf1 :: List -> Tree -> List
tf1 tv6 (Empty tv7) = tv6
tf1 tv6 (Node tv8 tv9 tv10) = (Cons tv8 (tf0 (tf0 tv6 tv9) tv10))

tf0 :: List -> Tree -> List
tf0 tv3 tv4 = (tf1 tv3 tv4)

tf3 :: Tree -> List
tf3 (Empty tv13) = (Nil Null)
tf3 (Node tv14 tv15 tv16) = (Cons tv14 (tf0 (tf2 tv15) tv16))

tf2 :: Tree -> List
tf2 tv11 = (tf3 tv11)

repr :: Tree -> List
repr tv2 = (tf2 tv2)

tf5 :: Tree -> Tree
tf5 (Empty tv20) = (Empty Null)
tf5 (Node tv21 tv22 tv23) = (Node tv21 (tf4 tv22) (tf4 tv23))

tf4 :: Tree -> Tree
tf4 tv18 = (tf5 tv18)

target :: Tree -> Tree
target tv17 = (tf4 tv17)

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


plus :: Nat -> Nat -> Nat
plus Zero x = x
plus (Succ x) y = (Succ (plus x y))

fst3 :: Tuple3 -> Nat
fst3 (MakeTuple3 x0 x1) = x0

snd3 :: Tuple3 -> Nat
snd3 (MakeTuple3 x0 x1) = x1

tf7 :: List -> Tuple3
tf7 (Nil tv27) = (MakeTuple3 Zero Zero)
tf7 (Cons tv28 tv29) = (MakeTuple3 (plus tv28 (fst3 (tf6 tv29))) (max (snd3 (tf6 tv29)) (plus tv28 (fst3 (tf6 tv29)))))

tf6 :: List -> Tuple3
tf6 tv25 = (tf7 tv25)

spec :: List -> Tuple3
spec tv24 = (tf6 tv24)

main :: Tree -> Tuple3
main tv30 = (spec (repr (target tv30)))

tf9 :: Tree -> Tuple3
tf9 (Empty tv34) = (MakeTuple3 Zero Zero)
tf9 (Node tv35 tv36 tv37) = (MakeTuple3 (plus (plus (fst3 (tf8 tv37)) (fst3 (tf8 tv36))) tv35) (ite2 (lq (max (plus (snd3 (tf8 tv37)) (fst3 (tf8 tv36))) (snd3 (tf8 tv36))) (plus (fst3 (tf8 tv37)) (max (plus (fst3 (tf8 tv36)) tv35) (fst3 (tf8 tv36))))) (plus (fst3 (tf8 tv37)) (max (plus (fst3 (tf8 tv36)) tv35) (fst3 (tf8 tv36)))) (max (plus (snd3 (tf8 tv37)) (fst3 (tf8 tv36))) (snd3 (tf8 tv36)))))

tf8 :: Tree -> Tuple3
tf8 tv32 = (tf9 tv32)

targetNew :: Tree -> Tuple3
targetNew tv31 = (tf8 tv31)

mainNew :: Tree -> Tuple3
mainNew tv38 = (MakeTuple3 (fst3 (targetNew tv38)) (snd3 (targetNew tv38)))

optimize inp0 = (main inp0)=:=(mainNew inp0)
