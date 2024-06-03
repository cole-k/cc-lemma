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


data CList = Sglt List | Cat CList Nat CList deriving (Eq, Typeable, Ord)

instance Names CList where
  names _ = ["var0_0", "var0_1", "var0_2"]

instance Arbitrary CList where
  arbitrary = sized arb
    where
      arb 0 = frequency
        [
          (1, do
            x0 <- arbitrary
            return (Sglt x0)
          )
        ]
      arb n = frequency
        [
          (1, do
            x0 <- arbitrary
            return (Sglt x0)
          ),
          (n, do
            let n' = n `div` 2
            x0 <- arb n'
            x1 <- arbitrary
            x2 <- arb n'
            return (Cat x0 x1 x2)
          )
        ]

instance Partial CList where
  unlifted (Sglt x0) = do
    x0' <- lifted x0
    return (Sglt x0')
  unlifted (Cat x0 x1 x2) = do
    x0' <- lifted x0
    x1' <- lifted x1
    x2' <- lifted x2
    return (Cat x0' x1' x2')


tf1 :: NList -> CList -> NList
tf1 tv4 (Sglt tv5) = (Ncons tv5 tv4)
tf1 tv4 (Cat tv6 tv7 tv8) = (tf0 (tf0 tv4 tv8) tv6)

tf0 :: NList -> CList -> NList
tf0 tv1 tv2 = (tf1 tv1 tv2)

tf3 :: CList -> NList
tf3 (Sglt tv11) = (Line tv11)
tf3 (Cat tv12 tv13 tv14) = (tf0 (tf2 tv14) tv12)

tf2 :: CList -> NList
tf2 tv9 = (tf3 tv9)

c2n :: CList -> NList
c2n tv0 = (tf2 tv0)

plus :: Nat -> Nat -> Nat
plus Zero x = x
plus (Succ x) y = (Succ (plus x y))

tf5 :: List -> Nat
tf5 (Elt tv18) = tv18
tf5 (Cons tv19 tv20) = (plus tv19 (tf4 tv20))

tf4 :: List -> Nat
tf4 tv16 = (tf5 tv16)

lsum :: List -> Nat
lsum tv15 = (tf4 tv15)

lq :: Nat -> Nat -> Bool
lq Zero (Succ x) = True
lq x Zero = False
lq (Succ x) (Succ y) = (lq x y)

ite3 :: Bool -> Nat -> Nat -> Nat
ite3 True x y = x
ite3 False x y = y

min :: Nat -> Nat -> Nat
min tv21 tv22 = (ite3 (lq tv21 tv22) tv21 tv22)

max :: Nat -> Nat -> Nat
max tv23 tv24 = (ite3 (lq tv23 tv24) tv24 tv23)

tf7 :: CList -> Nat
tf7 (Sglt tv28) = (lsum tv28)
tf7 (Cat tv29 tv30 tv31) = (min (tf6 tv29) (tf6 tv31))

tf6 :: CList -> Nat
tf6 tv26 = (tf7 tv26)

tf9 :: CList -> Nat
tf9 (Sglt tv34) = (lsum tv34)
tf9 (Cat tv35 tv36 tv37) = (max (tf8 tv35) (tf8 tv37))

tf8 :: CList -> Nat
tf8 tv32 = (tf9 tv32)

and :: Bool -> Bool -> Bool
and False x = False
and x False = False
and True True = True

tf11 :: CList -> Bool
tf11 (Sglt tv40) = True
tf11 (Cat tv41 tv42 tv43) = (and (and (lq (tf8 tv41) tv42) (lq tv42 (tf6 tv43))) (and (tf10 tv41) (tf10 tv43)))

tf10 :: CList -> Bool
tf10 tv38 = (tf11 tv38)

sorted :: CList -> Bool
sorted tv25 = (tf10 tv25)

data Tuple4 = MakeTuple4 Nat Bool deriving (Eq, Typeable, Ord)

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
            return (MakeTuple4 x0 x1)
          )
        ]
      arb n = frequency
        [
          (1, do
            x0 <- arbitrary
            x1 <- arbitrary
            return (MakeTuple4 x0 x1)
          )
        ]

instance Partial Tuple4 where
  unlifted (MakeTuple4 x0 x1) = do
    x0' <- lifted x0
    x1' <- lifted x1
    return (MakeTuple4 x0' x1')


geq :: Nat -> Nat -> Bool
geq Zero (Succ x) = False
geq x Zero = True
geq (Succ x) (Succ y) = (geq x y)

snd4 :: Tuple4 -> Bool
snd4 (MakeTuple4 x0 x1) = x1

fst4 :: Tuple4 -> Nat
fst4 (MakeTuple4 x0 x1) = x0

tf13 :: NList -> Tuple4
tf13 (Line tv47) = (MakeTuple4 (max Zero (lsum tv47)) (geq (lsum tv47) Zero))
tf13 (Ncons tv48 tv49) = (MakeTuple4 (ite3 (and (snd4 (tf12 tv49)) (geq (lsum tv48) Zero)) (plus (fst4 (tf12 tv49)) (lsum tv48)) (fst4 (tf12 tv49))) (and (snd4 (tf12 tv49)) (geq (lsum tv48) Zero)))

tf12 :: NList -> Tuple4
tf12 tv45 = (tf13 tv45)

spec :: NList -> Nat
spec tv44 = (fst4 (tf12 tv44))

tf15 :: List -> List -> List
tf15 tv53 (Elt tv54) = tv53
tf15 tv53 (Cons tv55 tv56) = (Cons tv55 (tf14 tv56))

tf14 :: List -> List
tf14 tv51 = (tf15 tv51 tv51)

leq :: Nat -> Nat -> Bool
leq Zero x = True
leq (Succ x) Zero = False
leq (Succ x) (Succ y) = (leq x y)

ite5 :: Bool -> CList -> CList -> CList
ite5 True x y = x
ite5 False x y = y

tf17 :: CList -> CList
tf17 (Sglt tv59) = (Sglt (tf14 tv59))
tf17 (Cat tv60 tv61 tv62) = (ite5 (leq tv61 Zero) (Cat tv60 tv61 (tf16 tv62)) (Cat (tf16 tv60) tv61 (tf16 tv62)))

tf16 :: CList -> CList
tf16 tv57 = (tf17 tv57)

target :: CList -> CList
target tv50 = (tf16 tv50)

main :: CList -> Nat
main tv63 = (ite3 (sorted tv63) (spec (c2n (target tv63))) Zero)

tf19 :: List -> Nat
tf19 (Elt tv67) = tv67
tf19 (Cons tv68 tv69) = (plus (tf18 tv69) tv68)

tf18 :: List -> Nat
tf18 tv65 = (tf19 tv65)

tf21 :: CList -> Nat
tf21 (Sglt tv72) = (max (tf18 tv72) Zero)
tf21 (Cat tv73 tv74 tv75) = (ite3 (leq tv74 Zero) (tf20 tv75) (plus (tf20 tv75) (tf20 tv73)))

tf20 :: CList -> Nat
tf20 tv70 = (tf21 tv70)

targetNew :: CList -> Nat
targetNew tv64 = (tf20 tv64)

mainNew :: CList -> Nat
mainNew tv76 = (ite3 (sorted tv76) (targetNew tv76) Zero)

optimize inp0 = (main inp0)=:=(mainNew inp0)
