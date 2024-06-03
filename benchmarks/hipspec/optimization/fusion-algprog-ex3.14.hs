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


data Tree = Tip Nat | Bin Tree Tree deriving (Eq, Typeable, Ord)

instance Names Tree where
  names _ = ["var0_0", "var0_1", "var0_2"]

instance Arbitrary Tree where
  arbitrary = sized arb
    where
      arb 0 = frequency
        [
          (1, do
            x0 <- arbitrary
            return (Tip x0)
          )
        ]
      arb n = frequency
        [
          (1, do
            x0 <- arbitrary
            return (Tip x0)
          ),
          (n, do
            let n' = n `div` 2
            x0 <- arb n'
            x1 <- arb n'
            return (Bin x0 x1)
          )
        ]

instance Partial Tree where
  unlifted (Tip x0) = do
    x0' <- lifted x0
    return (Tip x0')
  unlifted (Bin x0 x1) = do
    x0' <- lifted x0
    x1' <- lifted x1
    return (Bin x0' x1')


data Tuple1 = MakeTuple1 Nat Nat deriving (Eq, Typeable, Ord)

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


data PTree = Ptip Nat Nat | Pbin PTree PTree deriving (Eq, Typeable, Ord)

instance Names PTree where
  names _ = ["var0_0", "var0_1", "var0_2"]

instance Arbitrary PTree where
  arbitrary = sized arb
    where
      arb 0 = frequency
        [
          (1, do
            x0 <- arbitrary
            x1 <- arbitrary
            return (Ptip x0 x1)
          )
        ]
      arb n = frequency
        [
          (1, do
            x0 <- arbitrary
            x1 <- arbitrary
            return (Ptip x0 x1)
          ),
          (n, do
            let n' = n `div` 2
            x0 <- arb n'
            x1 <- arb n'
            return (Pbin x0 x1)
          )
        ]

instance Partial PTree where
  unlifted (Ptip x0 x1) = do
    x0' <- lifted x0
    x1' <- lifted x1
    return (Ptip x0' x1')
  unlifted (Pbin x0 x1) = do
    x0' <- lifted x0
    x1' <- lifted x1
    return (Pbin x0' x1')


plus :: Nat -> Nat -> Nat
plus Zero x = x
plus (Succ x) y = (Succ (plus x y))

tf3 :: PTree -> PTree
tf3 (Ptip tv8 tv9) = (Ptip (plus tv8 (Succ Zero)) tv9)
tf3 (Pbin tv10 tv11) = (Pbin (tf2 tv10) (tf2 tv11))

tf2 :: PTree -> PTree
tf2 tv6 = (tf3 tv6)

tf1 :: Tree -> PTree
tf1 (Tip tv3) = (Ptip Zero tv3)
tf1 (Bin tv4 tv5) = (Pbin (tf2 (tf0 tv4)) (tf2 (tf0 tv5)))

tf0 :: Tree -> PTree
tf0 tv1 = (tf1 tv1)

tri :: Tree -> PTree
tri tv0 = (tf0 tv0)

times :: Nat -> Nat -> Nat
times Zero x = Zero
times (Succ x) y = (plus (times x y) y)

tf5 :: PTree -> Nat
tf5 (Ptip tv15 tv16) = (times tv15 tv16)
tf5 (Pbin tv17 tv18) = (plus (tf4 tv17) (tf4 tv18))

tf4 :: PTree -> Nat
tf4 tv13 = (tf5 tv13)

tsum :: PTree -> Nat
tsum tv12 = (tf4 tv12)

main :: Tree -> Nat
main tv19 = (tsum (tri tv19))

fst1 :: Tuple1 -> Nat
fst1 (MakeTuple1 x0 x1) = x0

snd1 :: Tuple1 -> Nat
snd1 (MakeTuple1 x0 x1) = x1

tf7 :: Tree -> Tuple1
tf7 (Tip tv23) = (MakeTuple1 Zero tv23)
tf7 (Bin tv24 tv25) = (MakeTuple1 (plus (plus (plus (fst1 (tf6 tv24)) (snd1 (tf6 tv24))) (fst1 (tf6 tv25))) (snd1 (tf6 tv25))) (plus (snd1 (tf6 tv24)) (snd1 (tf6 tv25))))

tf6 :: Tree -> Tuple1
tf6 tv21 = (tf7 tv21)

triNew :: Tree -> Tuple1
triNew tv20 = (tf6 tv20)

mainNew :: Tree -> Nat
mainNew tv26 = (fst1 (triNew tv26))

optimize inp0 = (main inp0)=:=(mainNew inp0)
