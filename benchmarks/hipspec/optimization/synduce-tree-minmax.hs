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

max :: Nat -> Nat -> Nat
max tv0 tv1 = (ite1 (lq tv0 tv1) tv1 tv0)

gq :: Nat -> Nat -> Bool
gq Zero x = False
gq (Succ x) Zero = True
gq (Succ x) (Succ y) = (gq x y)

min :: Nat -> Nat -> Nat
min tv2 tv3 = (ite1 (gq tv2 tv3) tv3 tv2)

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

tf1 :: Tuple2 -> Tree -> Tuple2
tf1 tv9 (Leaf tv10) = (MakeTuple2 (min tv10 (fst2 tv9)) (max tv10 (snd2 tv9)))
tf1 tv9 (Node tv11 tv12 tv13) = (tf0 (tf0 (MakeTuple2 (min tv11 (fst2 tv9)) (max tv11 (snd2 tv9))) tv12) tv13)

tf0 :: Tuple2 -> Tree -> Tuple2
tf0 tv6 tv7 = (tf1 tv6 tv7)

g :: Tuple2 -> Tree -> Tuple2
g tv4 tv5 = (tf0 tv4 tv5)

tf3 :: Tree -> Tuple2
tf3 (Leaf tv16) = (MakeTuple2 tv16 tv16)
tf3 (Node tv17 tv18 tv19) = (g (MakeTuple2 (fst2 (g (MakeTuple2 tv17 tv17) tv18)) (snd2 (g (MakeTuple2 tv17 tv17) tv18))) tv19)

tf2 :: Tree -> Tuple2
tf2 tv15 = (tf3 tv15)

spec :: Tree -> Tuple2
spec tv14 = (tf2 tv14)

tf5 :: Tree -> Tree
tf5 (Leaf tv23) = (Leaf tv23)
tf5 (Node tv24 tv25 tv26) = (Node tv24 (tf4 tv25) (tf4 tv26))

tf4 :: Tree -> Tree
tf4 tv21 = (tf5 tv21)

repr :: Tree -> Tree
repr tv20 = (tf4 tv20)

main :: Tree -> Tuple2
main tv27 = (spec (repr tv27))

tf7 :: Tree -> Tuple2
tf7 (Leaf tv31) = (MakeTuple2 tv31 tv31)
tf7 (Node tv32 tv33 tv34) = (MakeTuple2 (min (fst2 (tf6 tv33)) (min (fst2 (tf6 tv34)) tv32)) (max (snd2 (tf6 tv33)) (max (snd2 (tf6 tv34)) tv32)))

tf6 :: Tree -> Tuple2
tf6 tv29 = (tf7 tv29)

reprNew :: Tree -> Tuple2
reprNew tv28 = (tf6 tv28)

mainNew :: Tree -> Tuple2
mainNew tv35 = (MakeTuple2 (fst2 (reprNew tv35)) (snd2 (reprNew tv35)))

optimize inp0 = (main inp0)=:=(mainNew inp0)
