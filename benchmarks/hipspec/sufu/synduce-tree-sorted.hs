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


data Tuple1 = MakeTuple1 Nat Bool deriving (Eq, Typeable, Ord)

instance Names Tuple1 where
  names _ = ["var0_0", "var0_1", "var0_2"]

instance Arbitrary Tuple1 where
  arbitrary = sized arb
    where
      arb 0 = frequency
        [
          (1, do
            x0 <- arbitrary
            x1 <- arbitrary
            return (MakeTuple1 x0 x1)
          )
        ]
      arb n = frequency
        [
          (1, do
            x0 <- arbitrary
            x1 <- arbitrary
            return (MakeTuple1 x0 x1)
          )
        ]

instance Partial Tuple1 where
  unlifted (MakeTuple1 x0 x1) = do
    x0' <- lifted x0
    x1' <- lifted x1
    return (MakeTuple1 x0' x1')


and :: Bool -> Bool -> Bool
and False x = False
and x False = False
and True True = True

lq :: Nat -> Nat -> Bool
lq Zero (Succ x) = True
lq x Zero = False
lq (Succ x) (Succ y) = (lq x y)

fst1 :: Tuple1 -> Nat
fst1 (MakeTuple1 x0 x1) = x0

snd1 :: Tuple1 -> Bool
snd1 (MakeTuple1 x0 x1) = x1

tf1 :: Tree -> Tuple1
tf1 (Leaf tv3) = (MakeTuple1 tv3 True)
tf1 (Node tv4 tv5 tv6) = (MakeTuple1 tv4 (and (and (and (lq (fst1 (tf0 tv5)) tv4) (lq tv4 (fst1 (tf0 tv6)))) (snd1 (tf0 tv5))) (snd1 (tf0 tv6))))

tf0 :: Tree -> Tuple1
tf0 tv1 = (tf1 tv1)

spec :: Tree -> Bool
spec tv0 = (snd1 (tf0 tv0))

tf3 :: Tree -> Tree
tf3 (Leaf tv10) = (Leaf tv10)
tf3 (Node tv11 tv12 tv13) = (Node tv11 (tf2 tv12) (tf2 tv13))

tf2 :: Tree -> Tree
tf2 tv8 = (tf3 tv8)

repr :: Tree -> Tree
repr tv7 = (tf2 tv7)

main :: Tree -> Bool
main tv14 = (spec (repr tv14))

data Tuple2 = MakeTuple2 Bool Nat deriving (Eq, Typeable, Ord)

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


snd2 :: Tuple2 -> Nat
snd2 (MakeTuple2 x0 x1) = x1

fst2 :: Tuple2 -> Bool
fst2 (MakeTuple2 x0 x1) = x0

tf5 :: Tree -> Tuple2
tf5 (Leaf tv18) = (MakeTuple2 True tv18)
tf5 (Node tv19 tv20 tv21) = (MakeTuple2 (and (and (and (lq (snd2 (tf4 tv20)) tv19) (fst2 (tf4 tv21))) (fst2 (tf4 tv20))) (lq tv19 (snd2 (tf4 tv21)))) tv19)

tf4 :: Tree -> Tuple2
tf4 tv16 = (tf5 tv16)

reprNew :: Tree -> Tuple2
reprNew tv15 = (tf4 tv15)

mainNew :: Tree -> Bool
mainNew tv22 = (fst2 (reprNew tv22))

optimize inp0 = (main inp0)=:=(mainNew inp0)
