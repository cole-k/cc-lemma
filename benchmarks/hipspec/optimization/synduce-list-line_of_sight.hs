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


data List = Single Nat | Cons Nat List deriving (Eq, Typeable, Ord)

instance Names List where
  names _ = ["var0_0", "var0_1", "var0_2"]

instance Arbitrary List where
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
            return (Cons x0 x1)
          )
        ]

instance Partial List where
  unlifted (Single x0) = do
    x0' <- lifted x0
    return (Single x0')
  unlifted (Cons x0 x1) = do
    x0' <- lifted x0
    x1' <- lifted x1
    return (Cons x0' x1')


data CList = Elt Nat | Cat CList CList deriving (Eq, Typeable, Ord)

instance Names CList where
  names _ = ["var0_0", "var0_1", "var0_2"]

instance Arbitrary CList where
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
            let n' = n `div` 2
            x0 <- arb n'
            x1 <- arb n'
            return (Cat x0 x1)
          )
        ]

instance Partial CList where
  unlifted (Elt x0) = do
    x0' <- lifted x0
    return (Elt x0')
  unlifted (Cat x0 x1) = do
    x0' <- lifted x0
    x1' <- lifted x1
    return (Cat x0' x1')


lq :: Nat -> Nat -> Bool
lq Zero (Succ x) = True
lq x Zero = False
lq (Succ x) (Succ y) = (lq x y)

ite2 :: Bool -> Nat -> Nat -> Nat
ite2 True x y = x
ite2 False x y = y

max :: Nat -> Nat -> Nat
max tv0 tv1 = (ite2 (lq tv0 tv1) tv1 tv0)

data Tuple3 = MakeTuple3 Nat Nat Bool deriving (Eq, Typeable, Ord)

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


snd3 :: Tuple3 -> Nat
snd3 (MakeTuple3 x0 x1 x2) = x1

gq :: Nat -> Nat -> Bool
gq Zero x = False
gq (Succ x) Zero = True
gq (Succ x) (Succ y) = (gq x y)

tf1 :: List -> Tuple3
tf1 (Single tv5) = (MakeTuple3 tv5 tv5 True)
tf1 (Cons tv6 tv7) = (MakeTuple3 tv6 (max (snd3 (tf0 tv7)) tv6) (gq tv6 (snd3 (tf0 tv7))))

tf0 :: List -> Tuple3
tf0 tv3 = (tf1 tv3)

third3 :: Tuple3 -> Bool
third3 (MakeTuple3 x0 x1 x2) = x2

spec :: List -> Bool
spec tv2 = (third3 (tf0 tv2))

tf3 :: List -> List -> List
tf3 tv13 (Single tv14) = (Cons tv14 tv13)
tf3 tv13 (Cons tv15 tv16) = (Cons tv15 (tf2 tv16 tv13))

tf2 :: List -> List -> List
tf2 tv10 tv11 = (tf3 tv11 tv10)

catlist :: List -> List -> List
catlist tv8 tv9 = (tf2 tv8 tv9)

tf5 :: CList -> List
tf5 (Elt tv20) = (Single tv20)
tf5 (Cat tv21 tv22) = (catlist (tf4 tv21) (tf4 tv22))

tf4 :: CList -> List
tf4 tv18 = (tf5 tv18)

repr :: CList -> List
repr tv17 = (tf4 tv17)

main :: CList -> Bool
main tv23 = (spec (repr tv23))

data Tuple4 = MakeTuple4 Bool Nat deriving (Eq, Typeable, Ord)

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

fst4 :: Tuple4 -> Bool
fst4 (MakeTuple4 x0 x1) = x0

snd4 :: Tuple4 -> Nat
snd4 (MakeTuple4 x0 x1) = x1

tf7 :: CList -> Tuple4
tf7 (Elt tv27) = (MakeTuple4 True tv27)
tf7 (Cat tv28 tv29) = (MakeTuple4 (and (fst4 (tf6 tv28)) (lq (snd4 (tf6 tv29)) (snd4 (tf6 tv28)))) (max (snd4 (tf6 tv29)) (snd4 (tf6 tv28))))

tf6 :: CList -> Tuple4
tf6 tv25 = (tf7 tv25)

reprNew :: CList -> Tuple4
reprNew tv24 = (tf6 tv24)

mainNew :: CList -> Bool
mainNew tv30 = (fst4 (reprNew tv30))

optimize inp0 = (main inp0)=:=(mainNew inp0)
