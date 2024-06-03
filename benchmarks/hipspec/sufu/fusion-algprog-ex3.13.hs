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


data PList = Pnil Unit | Pcons Nat Nat PList deriving (Eq, Typeable, Ord)

instance Names PList where
  names _ = ["var0_0", "var0_1", "var0_2"]

instance Arbitrary PList where
  arbitrary = sized arb
    where
      arb 0 = frequency
        [
          (1, do
            x0 <- arbitrary
            return (Pnil x0)
          )
        ]
      arb n = frequency
        [
          (1, do
            x0 <- arbitrary
            return (Pnil x0)
          ),
          (n, do
            let n' = n - 1
            x0 <- arbitrary
            x1 <- arbitrary
            x2 <- arb n'
            return (Pcons x0 x1 x2)
          )
        ]

instance Partial PList where
  unlifted (Pnil x0) = do
    x0' <- lifted x0
    return (Pnil x0')
  unlifted (Pcons x0 x1 x2) = do
    x0' <- lifted x0
    x1' <- lifted x1
    x2' <- lifted x2
    return (Pcons x0' x1' x2')


plus :: Nat -> Nat -> Nat
plus Zero x = x
plus (Succ x) y = (Succ (plus x y))

tf3 :: PList -> PList
tf3 (Pnil tv8) = (Pnil Null)
tf3 (Pcons tv9 tv10 tv11) = (Pcons (plus tv9 (Succ Zero)) tv10 (tf2 tv11))

tf2 :: PList -> PList
tf2 tv6 = (tf3 tv6)

tf1 :: List -> PList
tf1 (Nil tv3) = (Pnil Null)
tf1 (Cons tv4 tv5) = (Pcons Zero tv4 (tf2 (tf0 tv5)))

tf0 :: List -> PList
tf0 tv1 = (tf1 tv1)

tri :: List -> PList
tri tv0 = (tf0 tv0)

times :: Nat -> Nat -> Nat
times Zero x = Zero
times (Succ x) y = (plus (times x y) y)

tf5 :: PList -> Nat
tf5 (Pnil tv15) = Zero
tf5 (Pcons tv16 tv17 tv18) = (plus (times tv16 tv17) (tf4 tv18))

tf4 :: PList -> Nat
tf4 tv13 = (tf5 tv13)

tsum :: PList -> Nat
tsum tv12 = (tf4 tv12)

main :: List -> Nat
main tv19 = (tsum (tri tv19))

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

tf7 :: List -> Tuple2
tf7 (Nil tv23) = (MakeTuple2 Zero Zero)
tf7 (Cons tv24 tv25) = (MakeTuple2 (fst2 (MakeTuple2 (plus (fst2 (tf6 tv25)) (snd2 (tf6 tv25))) (snd2 (tf6 tv25)))) (plus (snd2 (MakeTuple2 (plus (fst2 (tf6 tv25)) (snd2 (tf6 tv25))) (snd2 (tf6 tv25)))) tv24))

tf6 :: List -> Tuple2
tf6 tv21 = (tf7 tv21)

triNew :: List -> Tuple2
triNew tv20 = (tf6 tv20)

mainNew :: List -> Nat
mainNew tv26 = (fst2 (triNew tv26))

optimize inp0 = (main inp0)=:=(mainNew inp0)
