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


data NList = Single List | Ncons List NList deriving (Eq, Typeable, Ord)

instance Names NList where
  names _ = ["var0_0", "var0_1", "var0_2"]

instance Arbitrary NList where
  arbitrary = sized arb
    where
      arb 0 = frequency
        [
          (1, do
            x0 <- arbitrary
            return (Single x0)
          )
        ]
      arb n = frequency
        [
          (1, do
            x0 <- arbitrary
            return (Single x0)
          ),
          (n, do
            let n' = n - 1
            x0 <- arbitrary
            x1 <- arb n'
            return (Ncons x0 x1)
          )
        ]

instance Partial NList where
  unlifted (Single x0) = do
    x0' <- lifted x0
    return (Single x0')
  unlifted (Ncons x0 x1) = do
    x0' <- lifted x0
    x1' <- lifted x1
    return (Ncons x0' x1')


tf1 :: NList -> List
tf1 (Single tv6) = (Cons (product tv6) (Nil Null))
tf1 (Ncons tv7 tv8) = (Cons (product tv7) (tf0 tv8))

tf0 :: NList -> List
tf0 tv3 = (tf1 tv3)

map :: NList -> List
map tv1 = (tf0 tv1)

plus :: Nat -> Nat -> Nat
plus Zero x = x
plus (Succ x) y = (Succ (plus x y))

tf3 :: List -> Nat
tf3 (Nil tv12) = Zero
tf3 (Cons tv13 tv14) = (plus tv13 (tf2 tv14))

tf2 :: List -> Nat
tf2 tv10 = (tf3 tv10)

sum :: List -> Nat
sum tv9 = (tf2 tv9)

times :: Nat -> Nat -> Nat
times Zero x = Zero
times (Succ x) y = (plus (times x y) y)

tf5 :: List -> Nat
tf5 (Nil tv18) = (Succ Zero)
tf5 (Cons tv19 tv20) = (times tv19 (tf4 tv20))

tf4 :: List -> Nat
tf4 tv16 = (tf5 tv16)

product :: List -> Nat
product tv15 = (tf4 tv15)

tf7 :: List -> List -> NList
tf7 tv24 (Nil tv25) = (Single tv24)
tf7 tv24 (Cons tv26 tv27) = (Ncons tv24 (tf6 tv27))

tf6 :: List -> NList
tf6 tv22 = (tf7 tv22 tv22)

tails :: List -> NList
tails tv21 = (tf6 tv21)

main :: List -> Nat
main tv28 = (sum (map (tails tv28)))

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

tf9 :: List -> Tuple2
tf9 (Nil tv32) = (MakeTuple2 (Succ Zero) (Succ Zero))
tf9 (Cons tv33 tv34) = (MakeTuple2 (plus (fst2 (tf8 tv34)) (times tv33 (snd2 (tf8 tv34)))) (times tv33 (snd2 (tf8 tv34))))

tf8 :: List -> Tuple2
tf8 tv30 = (tf9 tv30)

tailsNew :: List -> Tuple2
tailsNew tv29 = (tf8 tv29)

mainNew :: List -> Nat
mainNew tv35 = (fst2 (tailsNew tv35))

optimize inp0 = (main inp0)=:=(mainNew inp0)
