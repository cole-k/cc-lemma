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

tf5 :: BTree -> BTree
tf5 (Empty tv22) = (Empty Null)
tf5 (Node tv23 tv24 tv25) = (Node tv23 (tf4 tv24) (tf4 tv25))

tf4 :: BTree -> BTree
tf4 tv20 = (tf5 tv20)

treerec :: BTree -> BTree
treerec tv19 = (tf4 tv19)

tf7 :: Zipper -> Zipper
tf7 (Top tv29) = (Top Null)
tf7 (Left tv30 tv31 tv32) = (Left tv30 (treerec tv31) (tf6 tv32))
tf7 (Right tv33 tv34 tv35) = (Right tv33 (treerec tv34) (tf6 tv35))

tf6 :: Zipper -> Zipper
tf6 tv27 = (tf7 tv27)

ziprec :: Zipper -> Zipper
ziprec tv26 = (tf6 tv26)

main :: Zipper -> Nat
main tv36 = (mpath (repr (ziprec tv36)))

tf9 :: BTree -> Nat
tf9 (Empty tv40) = Zero
tf9 (Node tv41 tv42 tv43) = (plus tv41 (max (tf8 tv43) (tf8 tv42)))

tf8 :: BTree -> Nat
tf8 tv38 = (tf9 tv38)

treerecNew :: BTree -> Nat
treerecNew tv37 = (tf8 tv37)

tf11 :: Zipper -> Nat
tf11 (Top tv47) = Zero
tf11 (Left tv48 tv49 tv50) = (plus tv48 (max (tf10 tv50) (treerecNew tv49)))
tf11 (Right tv51 tv52 tv53) = (plus tv51 (max (tf10 tv53) (treerecNew tv52)))

tf10 :: Zipper -> Nat
tf10 tv45 = (tf11 tv45)

ziprecNew :: Zipper -> Nat
ziprecNew tv44 = (tf10 tv44)

mainNew :: Zipper -> Nat
mainNew tv54 = (ziprecNew tv54)

optimize inp0 = (main inp0)=:=(mainNew inp0)
