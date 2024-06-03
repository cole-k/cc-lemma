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


plus :: Nat -> Nat -> Nat
plus Zero x = x
plus (Succ x) y = (Succ (plus x y))

tf1 :: BTree -> Nat
tf1 (Empty tv3) = Zero
tf1 (Node tv4 tv5 tv6) = (plus tv4 (plus (tf0 tv5) (tf0 tv6)))

tf0 :: BTree -> Nat
tf0 tv1 = (tf1 tv1)

sum :: BTree -> Nat
sum tv0 = (tf0 tv0)

tf3 :: Zipper -> BTree
tf3 (Top tv10) = (Empty Null)
tf3 (Left tv11 tv12 tv13) = (Node tv11 tv12 (tf2 tv13))
tf3 (Right tv14 tv15 tv16) = (Node tv14 (tf2 tv16) tv15)

tf2 :: Zipper -> BTree
tf2 tv8 = (tf3 tv8)

repr :: Zipper -> BTree
repr tv7 = (tf2 tv7)

main :: Zipper -> Nat
main tv17 = (sum (repr tv17))

tf5 :: Zipper -> Nat
tf5 (Top tv21) = Zero
tf5 (Left tv22 tv23 tv24) = (plus (tf4 tv24) (plus tv22 (sum tv23)))
tf5 (Right tv25 tv26 tv27) = (plus (tf4 tv27) (plus tv25 (sum tv26)))

tf4 :: Zipper -> Nat
tf4 tv19 = (tf5 tv19)

reprNew :: Zipper -> Nat
reprNew tv18 = (tf4 tv18)

mainNew :: Zipper -> Nat
mainNew tv28 = (reprNew tv28)

optimize inp0 = (main inp0)=:=(mainNew inp0)
