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


data UList = Uelt Nat | Usplit UList Nat Nat UList deriving (Eq, Typeable, Ord)

instance Names UList where
  names _ = ["var0_0", "var0_1", "var0_2"]

instance Arbitrary UList where
  arbitrary = sized arb
    where
      arb 0 = frequency
        [
          (1, do
            x0 <- arbitrary
            return (Uelt x0)
          )
        ]
      arb n = frequency
        [
          (1, do
            x0 <- arbitrary
            return (Uelt x0)
          ),
          (n, do
            let n' = n `div` 2
            x0 <- arb n'
            x1 <- arbitrary
            x2 <- arbitrary
            x3 <- arb n'
            return (Usplit x0 x1 x2 x3)
          )
        ]

instance Partial UList where
  unlifted (Uelt x0) = do
    x0' <- lifted x0
    return (Uelt x0')
  unlifted (Usplit x0 x1 x2 x3) = do
    x0' <- lifted x0
    x1' <- lifted x1
    x2' <- lifted x2
    x3' <- lifted x3
    return (Usplit x0' x1' x2' x3')


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


tf1 :: List -> UList -> List
tf1 tv4 (Uelt tv5) = (Cons tv5 tv4)
tf1 tv4 (Usplit tv6 tv7 tv8 tv9) = (tf0 (Cons tv7 (Cons tv8 (tf0 tv4 tv9))) tv6)

tf0 :: List -> UList -> List
tf0 tv1 tv2 = (tf1 tv1 tv2)

tf3 :: UList -> List
tf3 (Uelt tv12) = (Elt tv12)
tf3 (Usplit tv13 tv14 tv15 tv16) = (tf0 (Cons tv14 (Cons tv15 (tf2 tv16))) tv13)

tf2 :: UList -> List
tf2 tv10 = (tf3 tv10)

repr :: UList -> List
repr tv0 = (tf2 tv0)

gq :: Nat -> Nat -> Bool
gq Zero x = False
gq (Succ x) Zero = True
gq (Succ x) (Succ y) = (gq x y)

and :: Bool -> Bool -> Bool
and False x = False
and x False = False
and True True = True

tf5 :: Nat -> List -> Bool
tf5 tv21 (Elt tv22) = (gq tv21 tv22)
tf5 tv21 (Cons tv23 tv24) = (and (gq tv21 tv23) (tf4 tv23 tv24))

tf4 :: Nat -> List -> Bool
tf4 tv18 tv19 = (tf5 tv18 tv19)

lq :: Nat -> Nat -> Bool
lq Zero (Succ x) = True
lq x Zero = False
lq (Succ x) (Succ y) = (lq x y)

ite2 :: Bool -> Bool -> Bool -> Bool
ite2 True x y = x
ite2 False x y = y

tf7 :: Nat -> List -> Bool
tf7 tv28 (Elt tv29) = (lq tv28 tv29)
tf7 tv28 (Cons tv30 tv31) = (ite2 (lq tv28 tv30) (tf6 tv30 tv31) (tf4 tv30 tv31))

tf6 :: Nat -> List -> Bool
tf6 tv25 tv26 = (tf7 tv25 tv26)

tf9 :: List -> Bool
tf9 (Elt tv33) = True
tf9 (Cons tv34 tv35) = (tf6 tv34 tv35)

tf8 :: List -> Bool
tf8 tv32 = (tf9 tv32)

isunimodal :: List -> Bool
isunimodal tv17 = (tf8 tv17)

ite3 :: Bool -> Nat -> Nat -> Nat
ite3 True x y = x
ite3 False x y = y

max :: Nat -> Nat -> Nat
max tv36 tv37 = (ite3 (lq tv36 tv37) tv37 tv36)

tf11 :: List -> Nat
tf11 (Elt tv41) = tv41
tf11 (Cons tv42 tv43) = (max tv42 (tf10 tv43))

tf10 :: List -> Nat
tf10 tv39 = (tf11 tv39)

spec :: List -> Nat
spec tv38 = (tf10 tv38)

ite4 :: Bool -> UList -> UList -> UList
ite4 True x y = x
ite4 False x y = y

tf13 :: UList -> UList
tf13 (Uelt tv47) = (Uelt tv47)
tf13 (Usplit tv48 tv49 tv50 tv51) = (ite4 (gq tv49 tv50) (Usplit (tf12 tv48) tv49 tv50 tv51) (Usplit tv48 tv49 tv50 (tf12 tv51)))

tf12 :: UList -> UList
tf12 tv45 = (tf13 tv45)

target :: UList -> UList
target tv44 = (tf12 tv44)

main :: UList -> Nat
main tv52 = (ite3 (isunimodal (repr tv52)) (spec (repr (target tv52))) Zero)

tf15 :: UList -> Nat
tf15 (Uelt tv56) = tv56
tf15 (Usplit tv57 tv58 tv59 tv60) = (ite3 (gq tv58 tv59) (max tv58 (tf14 tv57)) (max tv59 (tf14 tv60)))

tf14 :: UList -> Nat
tf14 tv54 = (tf15 tv54)

targetNew :: UList -> Nat
targetNew tv53 = (tf14 tv53)

mainNew :: UList -> Nat
mainNew tv61 = (ite3 (isunimodal (repr tv61)) (targetNew tv61) Zero)

optimize inp0 = (main inp0)=:=(mainNew inp0)
