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


data CList = Single Nat | Concat CList CList deriving (Eq, Typeable, Ord)

instance Names CList where
  names _ = ["var0_0", "var0_1", "var0_2"]

instance Arbitrary CList where
  arbitrary = sized arb
    where
      arb 0 = frequency
        [
          (1, do
            x0 <- arbitrary
            return (Single x0)
          )
        ]
      arb n = frequency
        [
          (1, do
            x0 <- arbitrary
            return (Single x0)
          ),
          (n, do
            let n' = n `div` 2
            x0 <- arb n'
            x1 <- arb n'
            return (Concat x0 x1)
          )
        ]

instance Partial CList where
  unlifted (Single x0) = do
    x0' <- lifted x0
    return (Single x0')
  unlifted (Concat x0 x1) = do
    x0' <- lifted x0
    x1' <- lifted x1
    return (Concat x0' x1')


tf1 :: List -> List -> List
tf1 tv5 (Elt tv6) = (Cons tv6 tv5)
tf1 tv5 (Cons tv7 tv8) = (Cons tv7 (tf0 tv8 tv5))

tf0 :: List -> List -> List
tf0 tv2 tv3 = (tf1 tv3 tv2)

cat :: List -> List -> List
cat tv0 tv1 = (tf0 tv0 tv1)

tf3 :: CList -> List
tf3 (Single tv12) = (Elt tv12)
tf3 (Concat tv13 tv14) = (cat (tf2 tv13) (tf2 tv14))

tf2 :: CList -> List
tf2 tv10 = (tf3 tv10)

repr :: CList -> List
repr tv9 = (tf2 tv9)

lq :: Nat -> Nat -> Bool
lq Zero (Succ x) = True
lq x Zero = False
lq (Succ x) (Succ y) = (lq x y)

ite2 :: Bool -> Nat -> Nat -> Nat
ite2 True x y = x
ite2 False x y = y

max :: Nat -> Nat -> Nat
max tv15 tv16 = (ite2 (lq tv15 tv16) tv16 tv15)

tf5 :: CList -> Nat
tf5 (Single tv20) = tv20
tf5 (Concat tv21 tv22) = (max (tf4 tv21) (tf4 tv22))

tf4 :: CList -> Nat
tf4 tv18 = (tf5 tv18)

lmax :: CList -> Nat
lmax tv17 = (tf4 tv17)

min :: Nat -> Nat -> Nat
min tv23 tv24 = (ite2 (lq tv23 tv24) tv23 tv24)

tf7 :: CList -> Nat
tf7 (Single tv28) = tv28
tf7 (Concat tv29 tv30) = (min (tf6 tv29) (tf6 tv30))

tf6 :: CList -> Nat
tf6 tv26 = (tf7 tv26)

lmin :: CList -> Nat
lmin tv25 = (tf6 tv25)

and :: Bool -> Bool -> Bool
and False x = False
and x False = False
and True True = True

tf9 :: CList -> Bool
tf9 (Single tv34) = True
tf9 (Concat tv35 tv36) = (and (lq (lmax tv35) (lmin tv36)) (and (tf8 tv35) (tf8 tv36)))

tf8 :: CList -> Bool
tf8 tv32 = (tf9 tv32)

ispart :: CList -> Bool
ispart tv31 = (tf8 tv31)

tf11 :: List -> Nat
tf11 (Elt tv40) = tv40
tf11 (Cons tv41 tv42) = (min tv41 (tf10 tv42))

tf10 :: List -> Nat
tf10 tv38 = (tf11 tv38)

spec :: List -> Nat
spec tv37 = (tf10 tv37)

tf13 :: CList -> CList -> CList
tf13 tv46 (Single tv47) = tv46
tf13 tv46 (Concat tv48 tv49) = (Concat (tf12 tv48) tv49)

tf12 :: CList -> CList
tf12 tv44 = (tf13 tv44 tv44)

target :: CList -> CList
target tv43 = (tf12 tv43)

main :: CList -> Nat
main tv50 = (ite2 (ispart tv50) (spec (repr (target tv50))) Zero)

tf15 :: CList -> Nat
tf15 (Single tv54) = tv54
tf15 (Concat tv55 tv56) = (tf14 tv55)

tf14 :: CList -> Nat
tf14 tv52 = (tf15 tv52)

targetNew :: CList -> Nat
targetNew tv51 = (tf14 tv51)

mainNew :: CList -> Nat
mainNew tv57 = (ite2 (ispart tv57) (targetNew tv57) Zero)

optimize inp0 = (main inp0)=:=(mainNew inp0)
