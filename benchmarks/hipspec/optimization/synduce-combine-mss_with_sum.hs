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


data IdxList = Ielt Nat | Icons Nat Nat IdxList deriving (Eq, Typeable, Ord)

instance Names IdxList where
  names _ = ["var0_0", "var0_1", "var0_2"]

instance Arbitrary IdxList where
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

instance Partial IdxList where
  unlifted (Ielt x0) = do
    x0' <- lifted x0
    return (Ielt x0')
  unlifted (Icons x0 x1 x2) = do
    x0' <- lifted x0
    x1' <- lifted x1
    x2' <- lifted x2
    return (Icons x0' x1' x2')


lq :: Nat -> Nat -> Bool
lq Zero (Succ x) = True
lq x Zero = False
lq (Succ x) (Succ y) = (lq x y)

ite2 :: Bool -> Nat -> Nat -> Nat
ite2 True x y = x
ite2 False x y = y

max :: Nat -> Nat -> Nat
max tv0 tv1 = (ite2 (lq tv0 tv1) tv1 tv0)

plus :: Nat -> Nat -> Nat
plus Zero x = x
plus (Succ x) y = (Succ (plus x y))

tf1 :: List -> Nat
tf1 (Elt tv5) = tv5
tf1 (Cons tv6 tv7) = (plus tv6 (tf0 tv7))

tf0 :: List -> Nat
tf0 tv3 = (tf1 tv3)

hsum :: List -> Nat
hsum tv2 = (tf0 tv2)

data Tuple3 = MakeTuple3 Nat Nat Nat deriving (Eq, Typeable, Ord)

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
            x2 <- arbitrary
            return (MakeTuple3 x0 x1 x2)
          )
        ]
      arb n = frequency
        [
          (1, do
            x0 <- arbitrary
            x1 <- arbitrary
            x2 <- arbitrary
            return (MakeTuple3 x0 x1 x2)
          )
        ]

instance Partial Tuple3 where
  unlifted (MakeTuple3 x0 x1 x2) = do
    x0' <- lifted x0
    x1' <- lifted x1
    x2' <- lifted x2
    return (MakeTuple3 x0' x1' x2')


gq :: Nat -> Nat -> Bool
gq Zero x = False
gq (Succ x) Zero = True
gq (Succ x) (Succ y) = (gq x y)

ite3 :: Bool -> Tuple3 -> Tuple3
ite3 True x = x
ite3 False x = (MakeTuple3 Zero Zero Zero)

fst3 :: Tuple3 -> Nat
fst3 (MakeTuple3 x0 x1 x2) = x0

snd3 :: Tuple3 -> Nat
snd3 (MakeTuple3 x0 x1 x2) = x1

third3 :: Tuple3 -> Nat
third3 (MakeTuple3 x0 x1 x2) = x2

tf3 :: List -> Tuple3
tf3 (Elt tv11) = (ite3 (gq tv11 Zero) (MakeTuple3 tv11 tv11 tv11))
tf3 (Cons tv12 tv13) = (MakeTuple3 (max (plus tv12 (hsum tv13)) (fst3 (tf2 tv13))) (max (plus tv12 (snd3 (tf2 tv13))) Zero) (max (max (plus tv12 (snd3 (tf2 tv13))) Zero) (third3 (tf2 tv13))))

tf2 :: List -> Tuple3
tf2 tv9 = (tf3 tv9)

mss :: List -> Nat
mss tv8 = (third3 (tf2 tv8))

spec :: List -> Nat
spec tv14 = (mss tv14)

tf5 :: IdxList -> List
tf5 (Ielt tv18) = (Elt tv18)
tf5 (Icons tv19 tv20 tv21) = (Cons tv19 (tf4 tv21))

tf4 :: IdxList -> List
tf4 tv16 = (tf5 tv16)

repr :: IdxList -> List
repr tv15 = (tf4 tv15)

main :: IdxList -> Nat
main tv22 = (spec (repr tv22))

data Tuple4 = MakeTuple4 Nat Nat deriving (Eq, Typeable, Ord)

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


and :: Bool -> Bool -> Bool
and False x = False
and x False = False
and True True = True

snd4 :: Tuple4 -> Nat
snd4 (MakeTuple4 x0 x1) = x1

fst4 :: Tuple4 -> Nat
fst4 (MakeTuple4 x0 x1) = x0

tf7 :: IdxList -> Tuple4
tf7 (Ielt tv26) = (MakeTuple4 (max tv26 Zero) tv26)
tf7 (Icons tv27 tv28 tv29) = (MakeTuple4 (ite2 (and (lq (plus tv27 (snd4 (tf6 tv29))) (fst4 (tf6 tv29))) (lq tv27 (fst4 (tf6 tv29)))) (fst4 (tf6 tv29)) (ite2 (lq (snd4 (tf6 tv29)) Zero) tv27 (plus tv27 (snd4 (tf6 tv29))))) (plus tv27 (max (snd4 (tf6 tv29)) Zero)))

tf6 :: IdxList -> Tuple4
tf6 tv24 = (tf7 tv24)

reprNew :: IdxList -> Tuple4
reprNew tv23 = (tf6 tv23)

mainNew :: IdxList -> Nat
mainNew tv30 = (fst4 (reprNew tv30))

optimize inp0 = (main inp0)=:=(mainNew inp0)
