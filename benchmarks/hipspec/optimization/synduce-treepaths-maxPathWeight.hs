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


data BTree = Empty Unit | Node Nat BTree BTree deriving (Eq, Typeable, Ord)

instance Names BTree where
  names _ = ["var0_0", "var0_1", "var0_2"]

instance Arbitrary BTree where
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

instance Partial BTree where
  unlifted (Empty x0) = do
    x0' <- lifted x0
    return (Empty x0')
  unlifted (Node x0 x1 x2) = do
    x0' <- lifted x0
    x1' <- lifted x1
    x2' <- lifted x2
    return (Node x0' x1' x2')


data Zipper = Top Unit | Left Nat BTree Zipper | Right Nat BTree Zipper deriving (Eq, Typeable, Ord)

instance Names Zipper where
  names _ = ["var0_0", "var0_1", "var0_2"]

instance Arbitrary Zipper where
  arbitrary = sized arb
    where
      arb 0 = frequency
        [
          (1, do
            x0 <- arbitrary
            return (Top x0)
          )
        ]
      arb n = frequency
        [
          (1, do
            x0 <- arbitrary
            return (Top x0)
          ),
          (n, do
            let n' = n - 1
            x0 <- arbitrary
            x1 <- arbitrary
            x2 <- arb n'
            return (Left x0 x1 x2)
          ),
          (n, do
            let n' = n - 1
            x0 <- arbitrary
            x1 <- arbitrary
            x2 <- arb n'
            return (Right x0 x1 x2)
          )
        ]

instance Partial Zipper where
  unlifted (Top x0) = do
    x0' <- lifted x0
    return (Top x0')
  unlifted (Left x0 x1 x2) = do
    x0' <- lifted x0
    x1' <- lifted x1
    x2' <- lifted x2
    return (Left x0' x1' x2')
  unlifted (Right x0 x1 x2) = do
    x0' <- lifted x0
    x1' <- lifted x1
    x2' <- lifted x2
    return (Right x0' x1' x2')


lq :: Nat -> Nat -> Bool
lq Zero (Succ x) = True
lq x Zero = False
lq (Succ x) (Succ y) = (lq x y)

ite2 :: Bool -> Nat -> Nat -> Nat
ite2 True x y = x
ite2 False x y = y

max :: Nat -> Nat -> Nat
max tv0 tv1 = (ite2 (lq tv0 tv1) tv1 tv0)

plus :: Nat -> Nat -> Nat
plus Zero x = x
plus (Succ x) y = (Succ (plus x y))

tf1 :: BTree -> Nat
tf1 (Empty tv5) = Zero
tf1 (Node tv6 tv7 tv8) = (plus tv6 (max (tf0 tv7) (tf0 tv8)))

tf0 :: BTree -> Nat
tf0 tv3 = (tf1 tv3)

mpath :: BTree -> Nat
mpath tv2 = (tf0 tv2)

tf3 :: Zipper -> BTree
tf3 (Top tv12) = (Empty Null)
tf3 (Left tv13 tv14 tv15) = (Node tv13 tv14 (tf2 tv15))
tf3 (Right tv16 tv17 tv18) = (Node tv16 (tf2 tv18) tv17)

tf2 :: Zipper -> BTree
tf2 tv10 = (tf3 tv10)

repr :: Zipper -> BTree
repr tv9 = (tf2 tv9)

main :: Zipper -> Nat
main tv19 = (mpath (repr tv19))

tf5 :: Zipper -> Nat
tf5 (Top tv23) = Zero
tf5 (Left tv24 tv25 tv26) = (plus tv24 (max (tf4 tv26) (mpath tv25)))
tf5 (Right tv27 tv28 tv29) = (plus tv27 (max (tf4 tv29) (mpath tv28)))

tf4 :: Zipper -> Nat
tf4 tv21 = (tf5 tv21)

reprNew :: Zipper -> Nat
reprNew tv20 = (tf4 tv20)

mainNew :: Zipper -> Nat
mainNew tv30 = (reprNew tv30)

optimize inp0 = (main inp0)=:=(mainNew inp0)
