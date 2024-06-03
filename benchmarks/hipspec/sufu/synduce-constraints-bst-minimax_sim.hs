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


lq :: Nat -> Nat -> Bool
lq Zero (Succ x) = True
lq x Zero = False
lq (Succ x) (Succ y) = (lq x y)

ite1 :: Bool -> Nat -> Nat -> Nat
ite1 True x y = x
ite1 False x y = y

min :: Nat -> Nat -> Nat
min tv0 tv1 = (ite1 (lq tv0 tv1) tv0 tv1)

max :: Nat -> Nat -> Nat
max tv2 tv3 = (ite1 (lq tv2 tv3) tv3 tv2)

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

data Tuple2 = MakeTuple2 Nat Nat deriving (Eq, Typeable, Ord)

instance Names Tuple2 where
  names _ = ["var0_0", "var0_1", "var0_2"]

instance Arbitrary Tuple2 where
  arbitrary = sized arb
    where
      arb 0 = frequency
        [
          (1, do
            x0 <- arbitrary
            x1 <- arbitrary
            return (MakeTuple2 x0 x1)
          )
        ]
      arb n = frequency
        [
          (1, do
            x0 <- arbitrary
            x1 <- arbitrary
            return (MakeTuple2 x0 x1)
          )
        ]

instance Partial Tuple2 where
  unlifted (MakeTuple2 x0 x1) = do
    x0' <- lifted x0
    x1' <- lifted x1
    return (MakeTuple2 x0' x1')


fst2 :: Tuple2 -> Nat
fst2 (MakeTuple2 x0 x1) = x0

snd2 :: Tuple2 -> Nat
snd2 (MakeTuple2 x0 x1) = x1

tf7 :: Tree -> Tuple2
tf7 (Leaf tv28) = (MakeTuple2 tv28 tv28)
tf7 (Node tv29 tv30 tv31) = (MakeTuple2 (max tv29 (max (fst2 (tf6 tv30)) (fst2 (tf6 tv31)))) (min tv29 (min (snd2 (tf6 tv30)) (snd2 (tf6 tv31)))))

tf6 :: Tree -> Tuple2
tf6 tv26 = (tf7 tv26)

spec :: Tree -> Tuple2
spec tv25 = (tf6 tv25)

tf9 :: Tree -> Tree
tf9 (Leaf tv34) = (Leaf tv34)
tf9 (Node tv35 tv36 tv37) = (Node tv35 tv36 tv37)

tf8 :: Tree -> Tree
tf8 tv33 = (tf9 tv33)

target :: Tree -> Tree
target tv32 = (tf8 tv32)

ite2 :: Bool -> Tuple2 -> Tuple2
ite2 True x = x
ite2 False x = (MakeTuple2 Zero Zero)

main :: Tree -> Tuple2
main tv38 = (ite2 (isbst tv38) (spec (target tv38)))

tf11 :: Tree -> Tuple2
tf11 (Leaf tv41) = (MakeTuple2 tv41 tv41)
tf11 (Node tv42 tv43 tv44) = (MakeTuple2 (tmax tv44) (tmin tv43))

tf10 :: Tree -> Tuple2
tf10 tv40 = (tf11 tv40)

targetNew :: Tree -> Tuple2
targetNew tv39 = (tf10 tv39)

mainNew :: Tree -> Tuple2
mainNew tv45 = (ite2 (isbst tv45) (MakeTuple2 (fst2 (targetNew tv45)) (snd2 (targetNew tv45))))

optimize inp0 = (main inp0)=:=(mainNew inp0)
