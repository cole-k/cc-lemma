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


data Tree = Tip Nat | Bin Tree Tree deriving (Eq, Typeable, Ord)

instance Names Tree where
  names _ = ["var0_0", "var0_1", "var0_2"]

instance Arbitrary Tree where
  arbitrary = sized arb
    where
      arb 0 = frequency
        [
          (1, do
            x0 <- arbitrary
            return (Tip x0)
          )
        ]
      arb n = frequency
        [
          (1, do
            x0 <- arbitrary
            return (Tip x0)
          ),
          (n, do
            let n' = n `div` 2
            x0 <- arb n'
            x1 <- arb n'
            return (Bin x0 x1)
          )
        ]

instance Partial Tree where
  unlifted (Tip x0) = do
    x0' <- lifted x0
    return (Tip x0')
  unlifted (Bin x0 x1) = do
    x0' <- lifted x0
    x1' <- lifted x1
    return (Bin x0' x1')


tf3 :: Tree -> Tree
tf3 (Tip tv13) = (Tip (op tv13))
tf3 (Bin tv14 tv15) = (Bin (tf2 tv14) (tf2 tv15))

tf2 :: Tree -> Tree
tf2 tv10 = (tf3 tv10)

tf1 :: Tree -> Tree
tf1 (Tip tv6) = (Tip Zero)
tf1 (Bin tv7 tv8) = (Bin (tf2 (tf0 tv7)) (tf2 (tf0 tv8)))

tf0 :: Tree -> Tree
tf0 tv3 = (tf1 tv3)

tri :: Tree -> Tree
tri tv1 = (tf0 tv1)

plus :: Nat -> Nat -> Nat
plus Zero x = x
plus (Succ x) y = (Succ (plus x y))

op :: Nat -> Nat
op tv16 = (plus (Succ Zero) tv16)

lq :: Nat -> Nat -> Bool
lq Zero (Succ x) = True
lq x Zero = False
lq (Succ x) (Succ y) = (lq x y)

ite1 :: Bool -> Nat -> Nat -> Nat
ite1 True x y = x
ite1 False x y = y

max :: Nat -> Nat -> Nat
max tv17 tv18 = (ite1 (lq tv17 tv18) tv18 tv17)

tf5 :: Tree -> Nat
tf5 (Tip tv22) = tv22
tf5 (Bin tv23 tv24) = (max (tf4 tv23) (tf4 tv24))

tf4 :: Tree -> Nat
tf4 tv20 = (tf5 tv20)

maximum :: Tree -> Nat
maximum tv19 = (tf4 tv19)

main :: Tree -> Nat
main tv25 = (maximum (tri tv25))

tf7 :: Tree -> Nat
tf7 (Tip tv30) = Zero
tf7 (Bin tv31 tv32) = (ite1 (lq (tf6 tv31) (tf6 tv32)) (plus (Succ Zero) (tf6 tv32)) (plus (Succ Zero) (tf6 tv31)))

tf6 :: Tree -> Nat
tf6 tv28 = (tf7 tv28)

triNew :: Tree -> Nat
triNew tv27 = (tf6 tv27)

mainNew :: Tree -> Nat
mainNew tv33 = (triNew tv33)

optimize inp0 = (main inp0)=:=(mainNew inp0)
