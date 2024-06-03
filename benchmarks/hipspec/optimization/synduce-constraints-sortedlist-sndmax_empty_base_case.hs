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


data CList = Empty Unit | Elt Nat | Concat CList CList deriving (Eq, Typeable, Ord)

instance Names CList where
  names _ = ["var0_0", "var0_1", "var0_2"]

instance Arbitrary CList where
  arbitrary = sized arb
    where
      arb 0 = frequency
        [
          (1, do
            x0 <- arbitrary
            return (Empty x0)
          ),
          (1, do
            x0 <- arbitrary
            return (Elt x0)
          )
        ]
      arb n = frequency
        [
          (1, do
            x0 <- arbitrary
            return (Empty x0)
          ),
          (1, do
            x0 <- arbitrary
            return (Elt x0)
          ),
          (n, do
            let n' = n `div` 2
            x0 <- arb n'
            x1 <- arb n'
            return (Concat x0 x1)
          )
        ]

instance Partial CList where
  unlifted (Empty x0) = do
    x0' <- lifted x0
    return (Empty x0')
  unlifted (Elt x0) = do
    x0' <- lifted x0
    return (Elt x0')
  unlifted (Concat x0 x1) = do
    x0' <- lifted x0
    x1' <- lifted x1
    return (Concat x0' x1')


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


tf1 :: List -> List -> List
tf1 tv5 (Nil tv6) = tv5
tf1 tv5 (Cons tv7 tv8) = (Cons tv7 (tf0 tv8 tv5))

tf0 :: List -> List -> List
tf0 tv2 tv3 = (tf1 tv3 tv2)

cat :: List -> List -> List
cat tv0 tv1 = (tf0 tv0 tv1)

tf3 :: CList -> List
tf3 (Empty tv12) = (Nil Null)
tf3 (Elt tv13) = (Cons tv13 (Nil Null))
tf3 (Concat tv14 tv15) = (cat (tf2 tv14) (tf2 tv15))

tf2 :: CList -> List
tf2 tv10 = (tf3 tv10)

repr :: CList -> List
repr tv9 = (tf2 tv9)

geq :: Nat -> Nat -> Bool
geq Zero (Succ x) = False
geq x Zero = True
geq (Succ x) (Succ y) = (geq x y)

tf4 :: Nat -> List -> Bool
tf4 tv18 (Nil tv19) = True
tf4 tv18 (Cons tv20 tv21) = (geq tv18 tv20)

geqhead :: Nat -> List -> Bool
geqhead tv16 tv17 = (tf4 tv16 tv17)

and :: Bool -> Bool -> Bool
and False x = False
and x False = False
and True True = True

tf6 :: List -> Bool
tf6 (Nil tv25) = True
tf6 (Cons tv26 tv27) = (and (geqhead tv26 tv27) (tf5 tv27))

tf5 :: List -> Bool
tf5 tv23 = (tf6 tv23)

issorted :: List -> Bool
issorted tv22 = (tf5 tv22)

lq :: Nat -> Nat -> Bool
lq Zero (Succ x) = True
lq x Zero = False
lq (Succ x) (Succ y) = (lq x y)

ite2 :: Bool -> Nat -> Nat -> Nat
ite2 True x y = x
ite2 False x y = y

min :: Nat -> Nat -> Nat
min tv28 tv29 = (ite2 (lq tv28 tv29) tv28 tv29)

gq :: Nat -> Nat -> Bool
gq Zero x = False
gq (Succ x) Zero = True
gq (Succ x) (Succ y) = (gq x y)

max :: Nat -> Nat -> Nat
max tv30 tv31 = (ite2 (gq tv30 tv31) tv30 tv31)

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

tf8 :: List -> Tuple3
tf8 (Nil tv35) = (MakeTuple3 Zero Zero)
tf8 (Cons tv36 tv37) = (MakeTuple3 (max (fst3 (tf7 tv37)) tv36) (max (snd3 (tf7 tv37)) (min (fst3 (tf7 tv37)) tv36)))

tf7 :: List -> Tuple3
tf7 tv33 = (tf8 tv33)

spec :: List -> Nat
spec tv32 = (snd3 (tf7 tv32))

tf10 :: CList -> CList -> CList
tf10 tv41 (Empty tv42) = tv41
tf10 tv41 (Elt tv43) = tv41
tf10 tv41 (Concat tv44 tv45) = (Concat (tf9 tv44) (tf9 tv45))

tf9 :: CList -> CList
tf9 tv39 = (tf10 tv39 tv39)

target :: CList -> CList
target tv38 = (tf9 tv38)

main :: CList -> Nat
main tv46 = (ite2 (issorted (repr tv46)) (spec (repr (target tv46))) Zero)

nateq :: Nat -> Nat -> Bool
nateq Zero Zero = True
nateq Zero (Succ x) = False
nateq (Succ x) Zero = False
nateq (Succ x) (Succ y) = (nateq x y)

plus :: Nat -> Nat -> Nat
plus Zero x = x
plus (Succ x) y = (Succ (plus x y))

tf12 :: CList -> Tuple3
tf12 (Empty tv50) = (MakeTuple3 Zero Zero)
tf12 (Elt tv51) = (MakeTuple3 Zero (max tv51 Zero))
tf12 (Concat tv52 tv53) = (MakeTuple3 (ite2 (and (lq (fst3 (tf11 tv52)) (snd3 (tf11 tv52))) (nateq (fst3 (tf11 tv52)) Zero)) (snd3 (tf11 tv53)) (ite2 (nateq (fst3 (tf11 tv52)) Zero) (plus (fst3 (tf11 tv52)) (fst3 (tf11 tv53))) (fst3 (tf11 tv52)))) (max (snd3 (tf11 tv52)) (snd3 (tf11 tv53))))

tf11 :: CList -> Tuple3
tf11 tv48 = (tf12 tv48)

targetNew :: CList -> Tuple3
targetNew tv47 = (tf11 tv47)

mainNew :: CList -> Nat
mainNew tv54 = (ite2 (issorted (repr tv54)) (fst3 (targetNew tv54)) Zero)

optimize inp0 = (main inp0)=:=(mainNew inp0)
