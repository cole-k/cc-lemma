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


data MList = Ielt Nat | Icons Nat Nat MList deriving (Eq, Typeable, Ord)

instance Names MList where
  names _ = ["var0_0", "var0_1", "var0_2"]

instance Arbitrary MList where
  arbitrary = sized arb
    where
      arb 0 = frequency
        [
          (1, do
            x0 <- arbitrary
            return (Ielt x0)
          )
        ]
      arb n = frequency
        [
          (1, do
            x0 <- arbitrary
            return (Ielt x0)
          ),
          (n, do
            let n' = n - 1
            x0 <- arbitrary
            x1 <- arbitrary
            x2 <- arb n'
            return (Icons x0 x1 x2)
          )
        ]

instance Partial MList where
  unlifted (Ielt x0) = do
    x0' <- lifted x0
    return (Ielt x0')
  unlifted (Icons x0 x1 x2) = do
    x0' <- lifted x0
    x1' <- lifted x1
    x2' <- lifted x2
    return (Icons x0' x1' x2')


tf1 :: MList -> List
tf1 (Ielt tv3) = (Elt tv3)
tf1 (Icons tv4 tv5 tv6) = (Cons tv4 (tf0 tv6))

tf0 :: MList -> List
tf0 tv1 = (tf1 tv1)

repr :: MList -> List
repr tv0 = (tf0 tv0)

plus :: Nat -> Nat -> Nat
plus Zero x = x
plus (Succ x) y = (Succ (plus x y))

tf3 :: List -> Nat
tf3 (Elt tv10) = tv10
tf3 (Cons tv11 tv12) = (plus tv11 (tf2 tv12))

tf2 :: List -> Nat
tf2 tv8 = (tf3 tv8)

sum :: List -> Nat
sum tv7 = (tf2 tv7)

and :: Bool -> Bool -> Bool
and False x = False
and x False = False
and True True = True

nateq :: Nat -> Nat -> Bool
nateq Zero Zero = True
nateq Zero (Succ x) = False
nateq (Succ x) Zero = False
nateq (Succ x) (Succ y) = (nateq x y)

tf5 :: MList -> MList -> Bool
tf5 tv16 (Ielt tv17) = True
tf5 tv16 (Icons tv18 tv19 tv20) = (and (nateq tv19 (sum (repr tv16))) (tf4 tv20))

tf4 :: MList -> Bool
tf4 tv14 = (tf5 tv14 tv14)

ismemo :: MList -> Bool
ismemo tv13 = (tf4 tv13)

lq :: Nat -> Nat -> Bool
lq Zero (Succ x) = True
lq x Zero = False
lq (Succ x) (Succ y) = (lq x y)

ite2 :: Bool -> Nat -> Nat -> Nat
ite2 True x y = x
ite2 False x y = y

max :: Nat -> Nat -> Nat
max tv21 tv22 = (ite2 (lq tv21 tv22) tv22 tv21)

tf7 :: List -> List -> Nat
tf7 tv25 (Elt tv27) = tv27
tf7 tv25 (Cons tv28 tv29) = (max (tf6 tv29) (sum tv25))

tf6 :: List -> Nat
tf6 tv24 = (tf7 tv24 tv24)

spec :: List -> Nat
spec tv23 = (tf6 tv23)

tf9 :: MList -> MList -> MList
tf9 tv33 (Ielt tv34) = tv33
tf9 tv33 (Icons tv35 tv36 tv37) = (Icons tv35 tv36 (tf8 tv37))

tf8 :: MList -> MList
tf8 tv31 = (tf9 tv31 tv31)

target :: MList -> MList
target tv30 = (tf8 tv30)

main :: MList -> Nat
main tv38 = (ite2 (ismemo tv38) (spec (repr (target tv38))) Zero)

tf11 :: MList -> Nat
tf11 (Ielt tv42) = tv42
tf11 (Icons tv43 tv44 tv45) = (ite2 (lq (tf10 tv45) tv44) tv44 (tf10 tv45))

tf10 :: MList -> Nat
tf10 tv40 = (tf11 tv40)

targetNew :: MList -> Nat
targetNew tv39 = (tf10 tv39)

mainNew :: MList -> Nat
mainNew tv46 = (ite2 (ismemo tv46) (targetNew tv46) Zero)

optimize inp0 = (main inp0)=:=(mainNew inp0)
