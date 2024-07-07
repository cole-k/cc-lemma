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


data NList = Nnil Unit | Ncons List NList deriving (Eq, Typeable, Ord)

instance Names NList where
  names _ = ["var0_0", "var0_1", "var0_2"]

instance Arbitrary NList where
  arbitrary = sized arb
    where
      arb 0 = frequency
        [
          (1, do
            x0 <- arbitrary
            return (Nnil x0)
          )
        ]
      arb n = frequency
        [
          (1, do
            x0 <- arbitrary
            return (Nnil x0)
          ),
          (n, do
            let n' = n - 1
            x0 <- arbitrary
            x1 <- arb n'
            return (Ncons x0 x1)
          )
        ]

instance Partial NList where
  unlifted (Nnil x0) = do
    x0' <- lifted x0
    return (Nnil x0')
  unlifted (Ncons x0 x1) = do
    x0' <- lifted x0
    x1' <- lifted x1
    return (Ncons x0' x1')

max :: Nat -> Nat -> Nat
max Zero Zero = Zero 
max (Succ x) Zero = Succ x
max Zero (Succ x) = Succ x
max (Succ x) (Succ y) = Succ (max x y)

tf1 :: List -> Nat
tf1 (Nil tv5) = Zero
tf1 (Cons tv6 tv7) = (max tv6 (tf0 tv7))

tf0 :: List -> Nat
tf0 tv3 = (tf1 tv3)

maximum :: List -> Nat
maximum tv2 = (tf0 tv2)

plus :: Nat -> Nat -> Nat
plus Zero x = x
plus (Succ x) y = (Succ (plus x y))

times :: Nat -> Nat -> Nat
times Zero x = Zero
times (Succ x) y = (plus (times x y) y)

tf3 :: List -> Nat
tf3 (Nil tv11) = (Succ Zero)
tf3 (Cons tv12 tv13) = (times tv12 (tf2 tv13))

tf2 :: List -> Nat
tf2 tv9 = (tf3 tv9)

product :: List -> Nat
product tv8 = (tf2 tv8)

tf5 :: NList -> List
tf5 (Nnil tv17) = (Nil Null)
tf5 (Ncons tv18 tv19) = (Cons (product tv18) (tf4 tv19))

tf4 :: NList -> List
tf4 tv15 = (tf5 tv15)

map :: NList -> List
map tv14 = (tf4 tv14)

tf7 :: List -> List -> NList
tf7 tv22 (Nil tv24) = (Ncons (Nil Null) (Nnil Null))
tf7 tv22 (Cons tv25 tv26) = (Ncons tv22 (tf6 tv26))

tf6 :: List -> NList
tf6 tv21 = (tf7 tv21 tv21)

tails :: List -> NList
tails tv20 = (tf6 tv20)

main :: List -> Nat
main tv27 = (maximum (map (tails tv27)))

data Tuple3 = MakeTuple3 Nat Nat deriving (Eq, Typeable, Ord)

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
            return (MakeTuple3 x0 x1)
          )
        ]
      arb n = frequency
        [
          (1, do
            x0 <- arbitrary
            x1 <- arbitrary
            return (MakeTuple3 x0 x1)
          )
        ]

instance Partial Tuple3 where
  unlifted (MakeTuple3 x0 x1) = do
    x0' <- lifted x0
    x1' <- lifted x1
    return (MakeTuple3 x0' x1')


fst3 :: Tuple3 -> Nat
fst3 (MakeTuple3 x0 x1) = x0

snd3 :: Tuple3 -> Nat
snd3 (MakeTuple3 x0 x1) = x1

step :: Nat -> Tuple3 -> Tuple3
step tv28 tv29 = (MakeTuple3 (max (fst3 tv29) (times tv28 (snd3 tv29))) (times tv28 (snd3 tv29)))

tf9 :: Tuple3 -> List -> Tuple3
tf9 tv35 (Nil tv36) = tv35
tf9 tv35 (Cons tv37 tv38) = (step tv37 (tf8 tv38 tv35))

tf8 :: List -> Tuple3 -> Tuple3
tf8 tv32 tv33 = (tf9 tv33 tv32)

fold :: List -> Tuple3
fold tv30 = (tf8 tv30 (MakeTuple3 (Succ Zero) (Succ Zero)))

mainNew :: List -> Nat
mainNew tv39 = (fst3 (fold tv39))

optimize inp0 = (main inp0) =:= (mainNew inp0)
