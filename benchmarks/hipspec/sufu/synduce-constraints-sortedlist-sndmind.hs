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


data Tuple0 = MakeTuple0 Nat Nat deriving (Eq, Typeable, Ord)

instance Names Tuple0 where
  names _ = ["var0_0", "var0_1", "var0_2"]

instance Arbitrary Tuple0 where
  arbitrary = sized arb
    where
      arb 0 = frequency
        [
          (1, do
            x0 <- arbitrary
            x1 <- arbitrary
            return (MakeTuple0 x0 x1)
          )
        ]
      arb n = frequency
        [
          (1, do
            x0 <- arbitrary
            x1 <- arbitrary
            return (MakeTuple0 x0 x1)
          )
        ]

instance Partial Tuple0 where
  unlifted (MakeTuple0 x0 x1) = do
    x0' <- lifted x0
    x1' <- lifted x1
    return (MakeTuple0 x0' x1')


data CList = Ctwo Nat Nat | Concat CList CList deriving (Eq, Typeable, Ord)

instance Names CList where
  names _ = ["var0_0", "var0_1", "var0_2"]

instance Arbitrary CList where
  arbitrary = sized arb
    where
      arb 0 = frequency
        [
          (1, do
            x0 <- arbitrary
            x1 <- arbitrary
            return (Ctwo x0 x1)
          )
        ]
      arb n = frequency
        [
          (1, do
            x0 <- arbitrary
            x1 <- arbitrary
            return (Ctwo x0 x1)
          ),
          (n, do
            let n' = n `div` 2
            x0 <- arb n'
            x1 <- arb n'
            return (Concat x0 x1)
          )
        ]

instance Partial CList where
  unlifted (Ctwo x0 x1) = do
    x0' <- lifted x0
    x1' <- lifted x1
    return (Ctwo x0' x1')
  unlifted (Concat x0 x1) = do
    x0' <- lifted x0
    x1' <- lifted x1
    return (Concat x0' x1')


data List = Two Nat Nat | Cons Nat List deriving (Eq, Typeable, Ord)

instance Names List where
  names _ = ["var0_0", "var0_1", "var0_2"]

instance Arbitrary List where
  arbitrary = sized arb
    where
      arb 0 = frequency
        [
          (1, do
            x0 <- arbitrary
            x1 <- arbitrary
            return (Two x0 x1)
          )
        ]
      arb n = frequency
        [
          (1, do
            x0 <- arbitrary
            x1 <- arbitrary
            return (Two x0 x1)
          ),
          (n, do
            let n' = n - 1
            x0 <- arbitrary
            x1 <- arb n'
            return (Cons x0 x1)
          )
        ]

instance Partial List where
  unlifted (Two x0 x1) = do
    x0' <- lifted x0
    x1' <- lifted x1
    return (Two x0' x1')
  unlifted (Cons x0 x1) = do
    x0' <- lifted x0
    x1' <- lifted x1
    return (Cons x0' x1')


tf1 :: List -> List -> List
tf1 tv5 (Two tv6 tv7) = (Cons tv6 (Cons tv7 tv5))
tf1 tv5 (Cons tv8 tv9) = (Cons tv8 (tf0 tv9 tv5))

tf0 :: List -> List -> List
tf0 tv2 tv3 = (tf1 tv3 tv2)

cat :: List -> List -> List
cat tv0 tv1 = (tf0 tv0 tv1)

tf3 :: CList -> List
tf3 (Ctwo tv13 tv14) = (Two tv13 tv14)
tf3 (Concat tv15 tv16) = (cat (tf2 tv15) (tf2 tv16))

tf2 :: CList -> List
tf2 tv11 = (tf3 tv11)

repr :: CList -> List
repr tv10 = (tf2 tv10)

lq :: Nat -> Nat -> Bool
lq Zero (Succ x) = True
lq x Zero = False
lq (Succ x) (Succ y) = (lq x y)

ite3 :: Bool -> Nat -> Nat -> Nat
ite3 True x y = x
ite3 False x y = y

min :: Nat -> Nat -> Nat
min tv17 tv18 = (ite3 (lq tv17 tv18) tv17 tv18)

max :: Nat -> Nat -> Nat
max tv19 tv20 = (ite3 (lq tv19 tv20) tv20 tv19)

fst0 :: Tuple0 -> Nat
fst0 (MakeTuple0 x0 x1) = x0

snd0 :: Tuple0 -> Nat
snd0 (MakeTuple0 x0 x1) = x1

tf5 :: List -> Tuple0
tf5 (Two tv24 tv25) = (MakeTuple0 (min tv24 tv25) (max tv24 tv25))
tf5 (Cons tv26 tv27) = (MakeTuple0 (min (fst0 (tf4 tv27)) tv26) (min (snd0 (tf4 tv27)) (max (fst0 (tf4 tv27)) tv26)))

tf4 :: List -> Tuple0
tf4 tv22 = (tf5 tv22)

spec :: List -> Nat
spec tv21 = (snd0 (tf4 tv21))

and :: Bool -> Bool -> Bool
and False x = False
and x False = False
and True True = True

gq :: Nat -> Nat -> Bool
gq Zero x = False
gq (Succ x) Zero = True
gq (Succ x) (Succ y) = (gq x y)

tf7 :: Nat -> List -> Bool
tf7 tv32 (Two tv33 tv34) = (and (gq tv32 tv33) (gq tv33 tv34))
tf7 tv32 (Cons tv35 tv36) = (and (gq tv32 tv35) (tf6 tv35 tv36))

tf6 :: Nat -> List -> Bool
tf6 tv29 tv30 = (tf7 tv29 tv30)

tf9 :: List -> Bool
tf9 (Two tv38 tv39) = (gq tv38 tv39)
tf9 (Cons tv40 tv41) = (tf6 tv40 tv41)

tf8 :: List -> Bool
tf8 tv37 = (tf9 tv37)

issorted :: List -> Bool
issorted tv28 = (tf8 tv28)

tf11 :: CList -> CList -> CList
tf11 tv45 (Ctwo tv46 tv47) = tv45
tf11 tv45 (Concat tv48 tv49) = (Concat tv48 (tf10 tv49))

tf10 :: CList -> CList
tf10 tv43 = (tf11 tv43 tv43)

target :: CList -> CList
target tv42 = (tf10 tv42)

main :: CList -> Nat
main tv50 = (ite3 (issorted (repr tv50)) (spec (repr (target tv50))) Zero)

tf13 :: CList -> Nat
tf13 (Ctwo tv54 tv55) = tv54
tf13 (Concat tv56 tv57) = (tf12 tv57)

tf12 :: CList -> Nat
tf12 tv52 = (tf13 tv52)

targetNew :: CList -> Nat
targetNew tv51 = (tf12 tv51)

mainNew :: CList -> Nat
mainNew tv58 = (ite3 (issorted (repr tv58)) (targetNew tv58) Zero)

optimize inp0 = (main inp0)=:=(mainNew inp0)
