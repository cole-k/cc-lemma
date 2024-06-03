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


data Tree = Leaf Nat | Node Nat Tree Tree deriving (Eq, Typeable, Ord)

instance Names Tree where
  names _ = ["var0_0", "var0_1", "var0_2"]

instance Arbitrary Tree where
  arbitrary = sized arb
    where
      arb 0 = frequency
        [
          (1, do
            x0 <- arbitrary
            return (Leaf x0)
          )
        ]
      arb n = frequency
        [
          (1, do
            x0 <- arbitrary
            return (Leaf x0)
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
  unlifted (Leaf x0) = do
    x0' <- lifted x0
    return (Leaf x0')
  unlifted (Node x0 x1 x2) = do
    x0' <- lifted x0
    x1' <- lifted x1
    x2' <- lifted x2
    return (Node x0' x1' x2')


data TreeMemo = Mleaf Nat Nat | Mnode Nat Nat TreeMemo TreeMemo deriving (Eq, Typeable, Ord)

instance Names TreeMemo where
  names _ = ["var0_0", "var0_1", "var0_2"]

instance Arbitrary TreeMemo where
  arbitrary = sized arb
    where
      arb 0 = frequency
        [
          (1, do
            x0 <- arbitrary
            x1 <- arbitrary
            return (Mleaf x0 x1)
          )
        ]
      arb n = frequency
        [
          (1, do
            x0 <- arbitrary
            x1 <- arbitrary
            return (Mleaf x0 x1)
          ),
          (n, do
            let n' = n `div` 2
            x0 <- arbitrary
            x1 <- arbitrary
            x2 <- arb n'
            x3 <- arb n'
            return (Mnode x0 x1 x2 x3)
          )
        ]

instance Partial TreeMemo where
  unlifted (Mleaf x0 x1) = do
    x0' <- lifted x0
    x1' <- lifted x1
    return (Mleaf x0' x1')
  unlifted (Mnode x0 x1 x2 x3) = do
    x0' <- lifted x0
    x1' <- lifted x1
    x2' <- lifted x2
    x3' <- lifted x3
    return (Mnode x0' x1' x2' x3')


tf0 :: TreeMemo -> Nat
tf0 (Mleaf tv1 tv2) = tv1
tf0 (Mnode tv3 tv4 tv5 tv6) = tv3

memo :: TreeMemo -> Nat
memo tv0 = (tf0 tv0)

and :: Bool -> Bool -> Bool
and False x = False
and x False = False
and True True = True

geq :: Nat -> Nat -> Bool
geq Zero (Succ x) = False
geq x Zero = True
geq (Succ x) (Succ y) = (geq x y)

lq :: Nat -> Nat -> Bool
lq Zero (Succ x) = True
lq x Zero = False
lq (Succ x) (Succ y) = (lq x y)

nateq :: Nat -> Nat -> Bool
nateq Zero Zero = True
nateq Zero (Succ x) = False
nateq (Succ x) Zero = False
nateq (Succ x) (Succ y) = (nateq x y)

ite3 :: Bool -> Bool -> Bool -> Bool
ite3 True x y = x
ite3 False x y = y

plus :: Nat -> Nat -> Nat
plus Zero x = x
plus (Succ x) y = (Succ (plus x y))

ite4 :: Bool -> Nat -> Nat -> Nat
ite4 True x y = x
ite4 False x y = y

tf2 :: TreeMemo -> Bool
tf2 (Mleaf tv10 tv11) = (and (geq tv10 Zero) (ite3 (lq tv11 (Succ (Succ Zero))) (nateq tv10 (Succ Zero)) (nateq tv10 Zero)))
tf2 (Mnode tv12 tv13 tv14 tv15) = (and (and (geq tv12 Zero) (nateq tv12 (plus (ite4 (lq tv13 (Succ (Succ Zero))) (Succ Zero) Zero) (plus (memo tv14) (memo tv15))))) (and (tf1 tv14) (tf1 tv15)))

tf1 :: TreeMemo -> Bool
tf1 tv8 = (tf2 tv8)

ismemo :: TreeMemo -> Bool
ismemo tv7 = (tf1 tv7)

tf4 :: TreeMemo -> Tree
tf4 (Mleaf tv19 tv20) = (Leaf tv20)
tf4 (Mnode tv21 tv22 tv23 tv24) = (Node tv22 (tf3 tv23) (tf3 tv24))

tf3 :: TreeMemo -> Tree
tf3 tv17 = (tf4 tv17)

repr :: TreeMemo -> Tree
repr tv16 = (tf3 tv16)

tf6 :: Tree -> Nat
tf6 (Leaf tv28) = (ite4 (lq tv28 (Succ (Succ Zero))) (Succ Zero) Zero)
tf6 (Node tv29 tv30 tv31) = (ite4 (lq tv29 (Succ (Succ Zero))) (plus (Succ Zero) (plus (tf5 tv30) (tf5 tv31))) (plus (tf5 tv30) (tf5 tv31)))

tf5 :: Tree -> Nat
tf5 tv26 = (tf6 tv26)

spec :: Tree -> Nat
spec tv25 = (tf5 tv25)

ite5 :: Bool -> TreeMemo -> TreeMemo -> TreeMemo
ite5 True x y = x
ite5 False x y = y

tf8 :: TreeMemo -> TreeMemo -> TreeMemo
tf8 tv34 (Mleaf tv35 tv36) = (ite5 (lq tv36 (Succ (Succ Zero))) tv34 tv34)
tf8 tv34 (Mnode tv37 tv38 tv39 tv40) = (ite5 (lq tv38 (Succ (Succ Zero))) tv34 tv34)

tf7 :: TreeMemo -> TreeMemo
tf7 tv33 = (tf8 tv33 tv33)

target :: TreeMemo -> TreeMemo
target tv32 = (tf7 tv32)

main :: TreeMemo -> Nat
main tv41 = (ite4 (ismemo tv41) (spec (repr (target tv41))) Zero)

mainNew :: TreeMemo -> Nat
mainNew tv42 = (ite4 (ismemo tv42) (memo tv42) Zero)

optimize inp0 = (main inp0)=:=(mainNew inp0)
