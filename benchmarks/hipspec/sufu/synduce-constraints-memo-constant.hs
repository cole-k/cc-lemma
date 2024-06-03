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


data TreeMemo = Mleaf Nat | Mnode Nat Nat TreeMemo TreeMemo deriving (Eq, Typeable, Ord)

instance Names TreeMemo where
  names _ = ["var0_0", "var0_1", "var0_2"]

instance Arbitrary TreeMemo where
  arbitrary = sized arb
    where
      arb 0 = frequency
        [
          (1, do
            x0 <- arbitrary
            return (Mleaf x0)
          )
        ]
      arb n = frequency
        [
          (1, do
            x0 <- arbitrary
            return (Mleaf x0)
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
  unlifted (Mleaf x0) = do
    x0' <- lifted x0
    return (Mleaf x0')
  unlifted (Mnode x0 x1 x2 x3) = do
    x0' <- lifted x0
    x1' <- lifted x1
    x2' <- lifted x2
    x3' <- lifted x3
    return (Mnode x0' x1' x2' x3')


tf0 :: TreeMemo -> Nat
tf0 (Mleaf tv1) = (Succ Zero)
tf0 (Mnode tv2 tv3 tv4 tv5) = tv2

memo :: TreeMemo -> Nat
memo tv0 = (tf0 tv0)

and :: Bool -> Bool -> Bool
and False x = False
and x False = False
and True True = True

nateq :: Nat -> Nat -> Bool
nateq Zero Zero = True
nateq Zero (Succ x) = False
nateq (Succ x) Zero = False
nateq (Succ x) (Succ y) = (nateq x y)

plus :: Nat -> Nat -> Nat
plus Zero x = x
plus (Succ x) y = (Succ (plus x y))

tf2 :: TreeMemo -> Bool
tf2 (Mleaf tv9) = True
tf2 (Mnode tv10 tv11 tv12 tv13) = (and (nateq tv10 (plus (Succ Zero) (plus (memo tv12) (memo tv13)))) (and (tf1 tv12) (tf1 tv13)))

tf1 :: TreeMemo -> Bool
tf1 tv7 = (tf2 tv7)

ismemo :: TreeMemo -> Bool
ismemo tv6 = (tf1 tv6)

tf4 :: TreeMemo -> Tree
tf4 (Mleaf tv17) = (Leaf tv17)
tf4 (Mnode tv18 tv19 tv20 tv21) = (Node tv19 (tf3 tv20) (tf3 tv21))

tf3 :: TreeMemo -> Tree
tf3 tv15 = (tf4 tv15)

repr :: TreeMemo -> Tree
repr tv14 = (tf3 tv14)

tf6 :: TreeMemo -> TreeMemo
tf6 (Mleaf tv24) = (Mleaf tv24)
tf6 (Mnode tv25 tv26 tv27 tv28) = (Mnode tv25 tv26 tv27 tv28)

tf5 :: TreeMemo -> TreeMemo
tf5 tv23 = (tf6 tv23)

target :: TreeMemo -> TreeMemo
target tv22 = (tf5 tv22)

tf7 :: Tree -> Nat
tf7 (Leaf tv30) = (Succ Zero)
tf7 (Node tv31 tv32 tv33) = (Succ Zero)

spec :: Tree -> Nat
spec tv29 = (tf7 tv29)

ite2 :: Bool -> Nat -> Nat
ite2 True x = x
ite2 False x = Zero

main :: TreeMemo -> Nat
main tv34 = (ite2 (ismemo tv34) (spec (repr (target tv34))))

mainNew :: TreeMemo -> Nat
mainNew tv35 = (ite2 (ismemo tv35) (Succ Zero))

optimize inp0 = (main inp0)=:=(mainNew inp0)
