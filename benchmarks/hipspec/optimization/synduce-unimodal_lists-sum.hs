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


data UList = Unil Unit | Uelt Nat | Usplit UList Nat Nat UList deriving (Eq, Typeable, Ord)

instance Names UList where
  names _ = ["var0_0", "var0_1", "var0_2"]

instance Arbitrary UList where
  arbitrary = sized arb
    where
      arb 0 = frequency
        [
          (1, do
            x0 <- arbitrary
            return (Unil x0)
          ),
          (1, do
            x0 <- arbitrary
            return (Uelt x0)
          )
        ]
      arb n = frequency
        [
          (1, do
            x0 <- arbitrary
            return (Unil x0)
          ),
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
  unlifted (Unil x0) = do
    x0' <- lifted x0
    return (Unil x0')
  unlifted (Uelt x0) = do
    x0' <- lifted x0
    return (Uelt x0')
  unlifted (Usplit x0 x1 x2 x3) = do
    x0' <- lifted x0
    x1' <- lifted x1
    x2' <- lifted x2
    x3' <- lifted x3
    return (Usplit x0' x1' x2' x3')


data List = Nil Unit | Cons Nat List deriving (Eq, Typeable, Ord)

instance Names List where
  names _ = ["var0_0", "var0_1", "var0_2"]

instance Arbitrary List where
  arbitrary = sized arb
    where
      arb 0 = frequency
        [
          (1, do
            x0 <- arbitrary
            return (Nil x0)
          )
        ]
      arb n = frequency
        [
          (1, do
            x0 <- arbitrary
            return (Nil x0)
          ),
          (n, do
            let n' = n - 1
            x0 <- arbitrary
            x1 <- arb n'
            return (Cons x0 x1)
          )
        ]

instance Partial List where
  unlifted (Nil x0) = do
    x0' <- lifted x0
    return (Nil x0')
  unlifted (Cons x0 x1) = do
    x0' <- lifted x0
    x1' <- lifted x1
    return (Cons x0' x1')


tf1 :: List -> UList -> List
tf1 tv4 (Unil tv5) = tv4
tf1 tv4 (Uelt tv6) = (Cons tv6 tv4)
tf1 tv4 (Usplit tv7 tv8 tv9 tv10) = (tf0 (Cons tv8 (Cons tv9 (tf0 tv4 tv10))) tv7)

tf0 :: List -> UList -> List
tf0 tv1 tv2 = (tf1 tv1 tv2)

repr :: UList -> List
repr tv0 = (tf0 (Nil Null) tv0)

and :: Bool -> Bool -> Bool
and False x = False
and x False = False
and True True = True

geq :: Nat -> Nat -> Bool
geq Zero (Succ x) = False
geq x Zero = True
geq (Succ x) (Succ y) = (geq x y)

tf3 :: Nat -> List -> Bool
tf3 tv15 (Nil tv16) = True
tf3 tv15 (Cons tv17 tv18) = (and (geq tv15 tv17) (tf2 tv17 tv18))

tf2 :: Nat -> List -> Bool
tf2 tv12 tv13 = (tf3 tv12 tv13)

leq :: Nat -> Nat -> Bool
leq Zero x = True
leq (Succ x) Zero = False
leq (Succ x) (Succ y) = (leq x y)

ite2 :: Bool -> Bool -> Bool -> Bool
ite2 True x y = x
ite2 False x y = y

tf5 :: Nat -> List -> Bool
tf5 tv22 (Nil tv23) = True
tf5 tv22 (Cons tv24 tv25) = (ite2 (leq tv22 tv24) (tf4 tv24 tv25) (tf2 tv24 tv25))

tf4 :: Nat -> List -> Bool
tf4 tv19 tv20 = (tf5 tv19 tv20)

tf7 :: List -> Bool
tf7 (Nil tv27) = True
tf7 (Cons tv28 tv29) = (tf4 tv28 tv29)

tf6 :: List -> Bool
tf6 tv26 = (tf7 tv26)

isunimodal :: List -> Bool
isunimodal tv11 = (tf6 tv11)

plus :: Nat -> Nat -> Nat
plus Zero x = x
plus (Succ x) y = (Succ (plus x y))

tf9 :: List -> Nat
tf9 (Nil tv33) = Zero
tf9 (Cons tv34 tv35) = (plus tv34 (tf8 tv35))

tf8 :: List -> Nat
tf8 tv31 = (tf9 tv31)

spec :: List -> Nat
spec tv30 = (tf8 tv30)

tf11 :: UList -> UList
tf11 (Unil tv39) = (Unil Null)
tf11 (Uelt tv40) = (Uelt tv40)
tf11 (Usplit tv41 tv42 tv43 tv44) = (Usplit (tf10 tv41) tv42 tv43 (tf10 tv44))

tf10 :: UList -> UList
tf10 tv37 = (tf11 tv37)

target :: UList -> UList
target tv36 = (tf10 tv36)

ite3 :: Bool -> Nat -> Nat
ite3 True x = x
ite3 False x = Zero

main :: UList -> Nat
main tv45 = (ite3 (isunimodal (repr tv45)) (spec (repr (target tv45))))

tf13 :: UList -> Nat
tf13 (Unil tv49) = Zero
tf13 (Uelt tv50) = tv50
tf13 (Usplit tv51 tv52 tv53 tv54) = (plus (tf12 tv54) (plus (tf12 tv51) (plus tv52 tv53)))

tf12 :: UList -> Nat
tf12 tv47 = (tf13 tv47)

targetNew :: UList -> Nat
targetNew tv46 = (tf12 tv46)

mainNew :: UList -> Nat
mainNew tv55 = (ite3 (isunimodal (repr tv55)) (targetNew tv55))

optimize inp0 = (main inp0)=:=(mainNew inp0)
