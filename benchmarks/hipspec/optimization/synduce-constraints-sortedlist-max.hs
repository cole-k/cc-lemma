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


data List = Elt Nat | Cons Nat List deriving (Eq, Typeable, Ord)

instance Names List where
  names _ = ["var0_0", "var0_1", "var0_2"]

instance Arbitrary List where
  arbitrary = sized arb
    where
      arb 0 = frequency
        [
          (1, do
            x0 <- arbitrary
            return (Elt x0)
          )
        ]
      arb n = frequency
        [
          (1, do
            x0 <- arbitrary
            return (Elt x0)
          ),
          (n, do
            let n' = n - 1
            x0 <- arbitrary
            x1 <- arb n'
            return (Cons x0 x1)
          )
        ]

instance Partial List where
  unlifted (Elt x0) = do
    x0' <- lifted x0
    return (Elt x0')
  unlifted (Cons x0 x1) = do
    x0' <- lifted x0
    x1' <- lifted x1
    return (Cons x0' x1')


geq :: Nat -> Nat -> Bool
geq Zero (Succ x) = False
geq x Zero = True
geq (Succ x) (Succ y) = (geq x y)

and :: Bool -> Bool -> Bool
and False x = False
and x False = False
and True True = True

tf1 :: Nat -> List -> Bool
tf1 tv4 (Elt tv5) = (geq tv4 tv5)
tf1 tv4 (Cons tv6 tv7) = (and (geq tv4 tv6) (tf0 tv6 tv7))

tf0 :: Nat -> List -> Bool
tf0 tv1 tv2 = (tf1 tv1 tv2)

tf3 :: List -> Bool
tf3 (Elt tv9) = True
tf3 (Cons tv10 tv11) = (tf0 tv10 tv11)

tf2 :: List -> Bool
tf2 tv8 = (tf3 tv8)

issorted :: List -> Bool
issorted tv0 = (tf2 tv0)

lq :: Nat -> Nat -> Bool
lq Zero (Succ x) = True
lq x Zero = False
lq (Succ x) (Succ y) = (lq x y)

ite1 :: Bool -> Nat -> Nat -> Nat
ite1 True x y = x
ite1 False x y = y

max :: Nat -> Nat -> Nat
max tv12 tv13 = (ite1 (lq tv12 tv13) tv13 tv12)

tf5 :: List -> Nat
tf5 (Elt tv17) = tv17
tf5 (Cons tv18 tv19) = (max tv18 (tf4 tv19))

tf4 :: List -> Nat
tf4 tv15 = (tf5 tv15)

maximum :: List -> Nat
maximum tv14 = (tf4 tv14)

tf7 :: List -> List -> List
tf7 tv22 (Elt tv23) = tv22
tf7 tv22 (Cons tv24 tv25) = tv22

tf6 :: List -> List
tf6 tv21 = (tf7 tv21 tv21)

target :: List -> List
target tv20 = (tf6 tv20)

main :: List -> Nat
main tv26 = (ite1 (issorted tv26) (maximum (target tv26)) Zero)

tf9 :: List -> Nat
tf9 (Elt tv29) = tv29
tf9 (Cons tv30 tv31) = tv30

tf8 :: List -> Nat
tf8 tv28 = (tf9 tv28)

targetNew :: List -> Nat
targetNew tv27 = (tf8 tv27)

mainNew :: List -> Nat
mainNew tv32 = (ite1 (issorted tv32) (targetNew tv32) Zero)

optimize inp0 = (main inp0)=:=(mainNew inp0)
