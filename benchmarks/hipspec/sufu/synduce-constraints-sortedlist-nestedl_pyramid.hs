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


data NList = Line List | Ncons List NList deriving (Eq, Typeable, Ord)

instance Names NList where
  names _ = ["var0_0", "var0_1", "var0_2"]

instance Arbitrary NList where
  arbitrary = sized arb
    where
      arb 0 = frequency
        [
          (1, do
            x0 <- arbitrary
            return (Line x0)
          )
        ]
      arb n = frequency
        [
          (1, do
            x0 <- arbitrary
            return (Line x0)
          ),
          (n, do
            let n' = n - 1
            x0 <- arbitrary
            x1 <- arb n'
            return (Ncons x0 x1)
          )
        ]

instance Partial NList where
  unlifted (Line x0) = do
    x0' <- lifted x0
    return (Line x0')
  unlifted (Ncons x0 x1) = do
    x0' <- lifted x0
    x1' <- lifted x1
    return (Ncons x0' x1')


lq :: Nat -> Nat -> Bool
lq Zero (Succ x) = True
lq x Zero = False
lq (Succ x) (Succ y) = (lq x y)

ite2 :: Bool -> Nat -> Nat -> Nat
ite2 True x y = x
ite2 False x y = y

max :: Nat -> Nat -> Nat
max tv0 tv1 = (ite2 (lq tv0 tv1) tv1 tv0)

tf1 :: List -> Nat
tf1 (Elt tv5) = tv5
tf1 (Cons tv6 tv7) = (max tv6 (tf0 tv7))

tf0 :: List -> Nat
tf0 tv3 = (tf1 tv3)

lmax :: List -> Nat
lmax tv2 = (tf0 tv2)

min :: Nat -> Nat -> Nat
min tv8 tv9 = (ite2 (lq tv8 tv9) tv8 tv9)

tf3 :: List -> Nat
tf3 (Elt tv13) = tv13
tf3 (Cons tv14 tv15) = (min tv14 (tf2 tv15))

tf2 :: List -> Nat
tf2 tv11 = (tf3 tv11)

lmin :: List -> Nat
lmin tv10 = (tf2 tv10)

leq :: Nat -> Nat -> Bool
leq Zero x = True
leq (Succ x) Zero = False
leq (Succ x) (Succ y) = (leq x y)

and :: Bool -> Bool -> Bool
and False x = False
and x False = False
and True True = True

tf5 :: Nat -> NList -> Bool
tf5 tv20 (Line tv21) = (leq tv20 (lmax tv21))
tf5 tv20 (Ncons tv22 tv23) = (and (leq tv20 (lmax tv22)) (tf4 (lmax tv22) tv23))

tf4 :: Nat -> NList -> Bool
tf4 tv17 tv18 = (tf5 tv17 tv18)

tf7 :: NList -> Bool
tf7 (Line tv25) = True
tf7 (Ncons tv26 tv27) = (tf4 (lmax tv26) tv27)

tf6 :: NList -> Bool
tf6 tv24 = (tf7 tv24)

issorted :: NList -> Bool
issorted tv16 = (tf6 tv16)

data Tuple3 = MakeTuple3 Nat Nat deriving (Eq, Typeable, Ord)

instance Names Tuple3 where
  names _ = ["var0_0", "var0_1", "var0_2"]

instance Arbitrary Tuple3 where
  arbitrary = sized arb
    where
      arb 0 = frequency
        [
          (1, do
            x0 <- arbitrary
            x1 <- arbitrary
            return (MakeTuple3 x0 x1)
          )
        ]
      arb n = frequency
        [
          (1, do
            x0 <- arbitrary
            x1 <- arbitrary
            return (MakeTuple3 x0 x1)
          )
        ]

instance Partial Tuple3 where
  unlifted (MakeTuple3 x0 x1) = do
    x0' <- lifted x0
    x1' <- lifted x1
    return (MakeTuple3 x0' x1')


fst3 :: Tuple3 -> Nat
fst3 (MakeTuple3 x0 x1) = x0

snd3 :: Tuple3 -> Nat
snd3 (MakeTuple3 x0 x1) = x1

tf9 :: List -> Tuple3
tf9 (Elt tv31) = (MakeTuple3 tv31 tv31)
tf9 (Cons tv32 tv33) = (MakeTuple3 (min (fst3 (tf8 tv33)) tv32) (max (snd3 (tf8 tv33)) tv32))

tf8 :: List -> Tuple3
tf8 tv29 = (tf9 tv29)

interval :: List -> Tuple3
interval tv28 = (tf8 tv28)

data Tuple4 = MakeTuple4 Nat Nat Bool deriving (Eq, Typeable, Ord)

instance Names Tuple4 where
  names _ = ["var0_0", "var0_1", "var0_2"]

instance Arbitrary Tuple4 where
  arbitrary = sized arb
    where
      arb 0 = frequency
        [
          (1, do
            x0 <- arbitrary
            x1 <- arbitrary
            x2 <- arbitrary
            return (MakeTuple4 x0 x1 x2)
          )
        ]
      arb n = frequency
        [
          (1, do
            x0 <- arbitrary
            x1 <- arbitrary
            x2 <- arbitrary
            return (MakeTuple4 x0 x1 x2)
          )
        ]

instance Partial Tuple4 where
  unlifted (MakeTuple4 x0 x1 x2) = do
    x0' <- lifted x0
    x1' <- lifted x1
    x2' <- lifted x2
    return (MakeTuple4 x0' x1' x2')


fst4 :: Tuple4 -> Nat
fst4 (MakeTuple4 x0 x1 x2) = x0

snd4 :: Tuple4 -> Nat
snd4 (MakeTuple4 x0 x1 x2) = x1

third4 :: Tuple4 -> Bool
third4 (MakeTuple4 x0 x1 x2) = x2

geq :: Nat -> Nat -> Bool
geq Zero (Succ x) = False
geq x Zero = True
geq (Succ x) (Succ y) = (geq x y)

tf11 :: NList -> Tuple4
tf11 (Line tv37) = (MakeTuple4 (fst3 (interval tv37)) (snd3 (interval tv37)) True)
tf11 (Ncons tv38 tv39) = (MakeTuple4 (min (fst3 (interval tv38)) (fst4 (tf10 tv39))) (max (snd3 (interval tv38)) (snd4 (tf10 tv39))) (and (third4 (tf10 tv39)) (and (leq (fst4 (tf10 tv39)) (fst3 (interval tv38))) (geq (snd4 (tf10 tv39)) (snd3 (interval tv38))))))

tf10 :: NList -> Tuple4
tf10 tv35 = (tf11 tv35)

spec :: NList -> Bool
spec tv34 = (third4 (tf10 tv34))

tf13 :: NList -> NList -> NList
tf13 tv43 (Line tv44) = tv43
tf13 tv43 (Ncons tv45 tv46) = (Ncons tv45 (tf12 tv46))

tf12 :: NList -> NList
tf12 tv41 = (tf13 tv41 tv41)

target :: NList -> NList
target tv40 = (tf12 tv40)

ite5 :: Bool -> Bool -> Bool
ite5 True x = x
ite5 False x = False

main :: NList -> Bool
main tv47 = (ite5 (issorted tv47) (spec (target tv47)))

data Tuple6 = MakeTuple6 Bool Nat deriving (Eq, Typeable, Ord)

instance Names Tuple6 where
  names _ = ["var0_0", "var0_1", "var0_2"]

instance Arbitrary Tuple6 where
  arbitrary = sized arb
    where
      arb 0 = frequency
        [
          (1, do
            x0 <- arbitrary
            x1 <- arbitrary
            return (MakeTuple6 x0 x1)
          )
        ]
      arb n = frequency
        [
          (1, do
            x0 <- arbitrary
            x1 <- arbitrary
            return (MakeTuple6 x0 x1)
          )
        ]

instance Partial Tuple6 where
  unlifted (MakeTuple6 x0 x1) = do
    x0' <- lifted x0
    x1' <- lifted x1
    return (MakeTuple6 x0' x1')


fst6 :: Tuple6 -> Bool
fst6 (MakeTuple6 x0 x1) = x0

snd6 :: Tuple6 -> Nat
snd6 (MakeTuple6 x0 x1) = x1

tf15 :: NList -> Tuple6
tf15 (Line tv51) = (MakeTuple6 True (fst3 (interval tv51)))
tf15 (Ncons tv52 tv53) = (MakeTuple6 (and (fst6 (tf14 tv53)) (leq (snd6 (tf14 tv53)) (lmin tv52))) (snd6 (tf14 tv53)))

tf14 :: NList -> Tuple6
tf14 tv49 = (tf15 tv49)

targetNew :: NList -> Tuple6
targetNew tv48 = (tf14 tv48)

mainNew :: NList -> Bool
mainNew tv54 = (ite5 (issorted tv54) (fst6 (targetNew tv54)))

optimize inp0 = (main inp0)=:=(mainNew inp0)
