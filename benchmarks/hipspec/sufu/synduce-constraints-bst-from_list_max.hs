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


data Tree = Leaf Nat | Node Nat Tree Tree deriving (Eq, Typeable, Ord)

instance Names Tree where
  names _ = ["var0_0", "var0_1", "var0_2"]

instance Arbitrary Tree where
  arbitrary = sized arb
    where
      arb 0 = frequency
        [
          (1, do
            x0 <- arbitrary
            return (Leaf x0)
          )
        ]
      arb n = frequency
        [
          (1, do
            x0 <- arbitrary
            return (Leaf x0)
          ),
          (n, do
            let n' = n `div` 2
            x0 <- arbitrary
            x1 <- arb n'
            x2 <- arb n'
            return (Node x0 x1 x2)
          )
        ]

instance Partial Tree where
  unlifted (Leaf x0) = do
    x0' <- lifted x0
    return (Leaf x0')
  unlifted (Node x0 x1 x2) = do
    x0' <- lifted x0
    x1' <- lifted x1
    x2' <- lifted x2
    return (Node x0' x1' x2')


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


lq :: Nat -> Nat -> Bool
lq Zero (Succ x) = True
lq x Zero = False
lq (Succ x) (Succ y) = (lq x y)

ite2 :: Bool -> Nat -> Nat -> Nat
ite2 True x y = x
ite2 False x y = y

min :: Nat -> Nat -> Nat
min tv0 tv1 = (ite2 (lq tv0 tv1) tv0 tv1)

max :: Nat -> Nat -> Nat
max tv2 tv3 = (ite2 (lq tv2 tv3) tv3 tv2)

tf1 :: Tree -> Nat
tf1 (Leaf tv7) = tv7
tf1 (Node tv8 tv9 tv10) = (min tv8 (min (tf0 tv9) (tf0 tv10)))

tf0 :: Tree -> Nat
tf0 tv5 = (tf1 tv5)

tmin :: Tree -> Nat
tmin tv4 = (tf0 tv4)

tf3 :: Tree -> Nat
tf3 (Leaf tv14) = tv14
tf3 (Node tv15 tv16 tv17) = (max tv15 (max (tf2 tv16) (tf2 tv17)))

tf2 :: Tree -> Nat
tf2 tv12 = (tf3 tv12)

tmax :: Tree -> Nat
tmax tv11 = (tf2 tv11)

and :: Bool -> Bool -> Bool
and False x = False
and x False = False
and True True = True

geq :: Nat -> Nat -> Bool
geq Zero (Succ x) = False
geq x Zero = True
geq (Succ x) (Succ y) = (geq x y)

leq :: Nat -> Nat -> Bool
leq Zero x = True
leq (Succ x) Zero = False
leq (Succ x) (Succ y) = (leq x y)

tf5 :: Tree -> Bool
tf5 (Leaf tv21) = True
tf5 (Node tv22 tv23 tv24) = (and (and (geq tv22 (tmax tv23)) (leq tv22 (tmin tv24))) (and (tf4 tv23) (tf4 tv24)))

tf4 :: Tree -> Bool
tf4 tv19 = (tf5 tv19)

isbst :: Tree -> Bool
isbst tv18 = (tf4 tv18)

tf7 :: List -> List -> List
tf7 tv29 (Cons tv31 tv32) = (Cons tv31 (tf6 tv32 tv29))
tf7 tv29 (Elt tv33) = (Cons tv33 tv29)

tf6 :: List -> List -> List
tf6 tv27 tv28 = (tf7 tv28 tv27)

cat :: List -> List -> List
cat tv25 tv26 = (tf6 tv25 tv26)

tf9 :: Tree -> List
tf9 (Leaf tv37) = (Elt tv37)
tf9 (Node tv38 tv39 tv40) = (cat (tf8 tv39) (Cons tv38 (tf8 tv40)))

tf8 :: Tree -> List
tf8 tv35 = (tf9 tv35)

repr :: Tree -> List
repr tv34 = (tf8 tv34)

tf11 :: List -> Nat
tf11 (Elt tv44) = tv44
tf11 (Cons tv45 tv46) = (max tv45 (tf10 tv46))

tf10 :: List -> Nat
tf10 tv42 = (tf11 tv42)

spec :: List -> Nat
spec tv41 = (tf10 tv41)

tf13 :: Tree -> Tree
tf13 (Leaf tv50) = (Leaf tv50)
tf13 (Node tv51 tv52 tv53) = (Node tv51 tv52 (tf12 tv53))

tf12 :: Tree -> Tree
tf12 tv48 = (tf13 tv48)

target :: Tree -> Tree
target tv47 = (tf12 tv47)

main :: Tree -> Nat
main tv54 = (ite2 (isbst tv54) (spec (repr (target tv54))) Zero)

tf15 :: Tree -> Nat
tf15 (Leaf tv58) = tv58
tf15 (Node tv59 tv60 tv61) = (tf14 tv61)

tf14 :: Tree -> Nat
tf14 tv56 = (tf15 tv56)

targetNew :: Tree -> Nat
targetNew tv55 = (tf14 tv55)

mainNew :: Tree -> Nat
mainNew tv62 = (ite2 (isbst tv62) (targetNew tv62) Zero)

optimize inp0 = (main inp0)=:=(mainNew inp0)
