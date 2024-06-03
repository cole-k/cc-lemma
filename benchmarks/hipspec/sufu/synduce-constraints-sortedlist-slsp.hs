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


data CList = Single Nat | Concat Nat CList CList deriving (Eq, Typeable, Ord)

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
            x0 <- arbitrary
            x1 <- arb n'
            x2 <- arb n'
            return (Concat x0 x1 x2)
          )
        ]

instance Partial CList where
  unlifted (Single x0) = do
    x0' <- lifted x0
    return (Single x0')
  unlifted (Concat x0 x1 x2) = do
    x0' <- lifted x0
    x1' <- lifted x1
    x2' <- lifted x2
    return (Concat x0' x1' x2')


tf1 :: List -> List -> List
tf1 tv5 (Elt tv6) = (Cons tv6 tv5)
tf1 tv5 (Cons tv7 tv8) = (Cons tv7 (tf0 tv8 tv5))

tf0 :: List -> List -> List
tf0 tv2 tv3 = (tf1 tv3 tv2)

cat :: List -> List -> List
cat tv0 tv1 = (tf0 tv0 tv1)

tf3 :: CList -> List
tf3 (Single tv12) = (Elt tv12)
tf3 (Concat tv13 tv14 tv15) = (cat (tf2 tv14) (tf2 tv15))

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
max tv16 tv17 = (ite2 (lq tv16 tv17) tv17 tv16)

min :: Nat -> Nat -> Nat
min tv18 tv19 = (ite2 (lq tv18 tv19) tv18 tv19)

tf5 :: CList -> Nat
tf5 (Single tv23) = tv23
tf5 (Concat tv24 tv25 tv26) = (max (tf4 tv25) (tf4 tv26))

tf4 :: CList -> Nat
tf4 tv21 = (tf5 tv21)

tf7 :: CList -> Nat
tf7 (Single tv29) = tv29
tf7 (Concat tv30 tv31 tv32) = (min (tf6 tv31) (tf6 tv32))

tf6 :: CList -> Nat
tf6 tv27 = (tf7 tv27)

and :: Bool -> Bool -> Bool
and False x = False
and x False = False
and True True = True

tf9 :: CList -> Bool
tf9 (Single tv35) = True
tf9 (Concat tv36 tv37 tv38) = (and (and (lq (tf4 tv37) tv36) (lq tv36 (tf6 tv38))) (and (tf8 tv37) (tf8 tv38)))

tf8 :: CList -> Bool
tf8 tv33 = (tf9 tv33)

isparti :: CList -> Bool
isparti tv20 = (tf8 tv20)

data Tuple3 = MakeTuple3 Nat Bool deriving (Eq, Typeable, Ord)

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


geq :: Nat -> Nat -> Bool
geq Zero (Succ x) = False
geq x Zero = True
geq (Succ x) (Succ y) = (geq x y)

snd3 :: Tuple3 -> Bool
snd3 (MakeTuple3 x0 x1) = x1

plus :: Nat -> Nat -> Nat
plus Zero x = x
plus (Succ x) y = (Succ (plus x y))

fst3 :: Tuple3 -> Nat
fst3 (MakeTuple3 x0 x1) = x0

tf11 :: List -> Tuple3
tf11 (Elt tv42) = (MakeTuple3 (max Zero tv42) (geq tv42 Zero))
tf11 (Cons tv43 tv44) = (MakeTuple3 (ite2 (and (geq tv43 Zero) (snd3 (tf10 tv44))) (plus (fst3 (tf10 tv44)) tv43) (fst3 (tf10 tv44))) (and (geq tv43 Zero) (snd3 (tf10 tv44))))

tf10 :: List -> Tuple3
tf10 tv40 = (tf11 tv40)

spec :: List -> Nat
spec tv39 = (fst3 (tf10 tv39))

leq :: Nat -> Nat -> Bool
leq Zero x = True
leq (Succ x) Zero = False
leq (Succ x) (Succ y) = (leq x y)

ite4 :: Bool -> CList -> CList -> CList
ite4 True x y = x
ite4 False x y = y

tf13 :: CList -> CList -> CList
tf13 tv48 (Single tv49) = tv48
tf13 tv48 (Concat tv50 tv51 tv52) = (ite4 (leq tv50 Zero) (Concat tv50 tv51 (tf12 tv52)) (Concat tv50 (tf12 tv51) (tf12 tv52)))

tf12 :: CList -> CList
tf12 tv46 = (tf13 tv46 tv46)

target :: CList -> CList
target tv45 = (tf12 tv45)

main :: CList -> Nat
main tv53 = (ite2 (isparti tv53) (spec (repr (target tv53))) Zero)

tf15 :: CList -> Nat
tf15 (Single tv57) = (max tv57 Zero)
tf15 (Concat tv58 tv59 tv60) = (ite2 (leq tv58 Zero) (tf14 tv60) (plus (tf14 tv60) (tf14 tv59)))

tf14 :: CList -> Nat
tf14 tv55 = (tf15 tv55)

targetNew :: CList -> Nat
targetNew tv54 = (tf14 tv54)

mainNew :: CList -> Nat
mainNew tv61 = (ite2 (isparti tv61) (targetNew tv61) Zero)

optimize inp0 = (main inp0)=:=(mainNew inp0)
