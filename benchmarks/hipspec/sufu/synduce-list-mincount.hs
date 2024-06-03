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


data CList = Single Nat | Concat CList CList deriving (Eq, Typeable, Ord)

instance Names CList where
  names _ = ["var0_0", "var0_1", "var0_2"]

instance Arbitrary CList where
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
            let n' = n `div` 2
            x0 <- arb n'
            x1 <- arb n'
            return (Concat x0 x1)
          )
        ]

instance Partial CList where
  unlifted (Single x0) = do
    x0' <- lifted x0
    return (Single x0')
  unlifted (Concat x0 x1) = do
    x0' <- lifted x0
    x1' <- lifted x1
    return (Concat x0' x1')


lq :: Nat -> Nat -> Bool
lq Zero (Succ x) = True
lq x Zero = False
lq (Succ x) (Succ y) = (lq x y)

ite2 :: Bool -> Nat -> Nat -> Nat
ite2 True x y = x
ite2 False x y = y

min :: Nat -> Nat -> Nat
min tv0 tv1 = (ite2 (lq tv0 tv1) tv0 tv1)

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

plus :: Nat -> Nat -> Nat
plus Zero x = x
plus (Succ x) y = (Succ (plus x y))

snd3 :: Tuple3 -> Nat
snd3 (MakeTuple3 x0 x1) = x1

nateq :: Nat -> Nat -> Bool
nateq Zero Zero = True
nateq Zero (Succ x) = False
nateq (Succ x) Zero = False
nateq (Succ x) (Succ y) = (nateq x y)

tf1 :: List -> Tuple3
tf1 (Elt tv5) = (MakeTuple3 tv5 (Succ Zero))
tf1 (Cons tv6 tv7) = (MakeTuple3 (min (fst3 (tf0 tv7)) tv6) (ite2 (lq tv6 (fst3 (tf0 tv7))) (Succ Zero) (plus (snd3 (tf0 tv7)) (ite2 (nateq tv6 (fst3 (tf0 tv7))) (Succ Zero) Zero))))

tf0 :: List -> Tuple3
tf0 tv3 = (tf1 tv3)

spec :: List -> Nat
spec tv2 = (snd3 (tf0 tv2))

tf3 :: List -> List -> List
tf3 tv13 (Elt tv14) = (Cons tv14 tv13)
tf3 tv13 (Cons tv15 tv16) = (Cons tv15 (tf2 tv16 tv13))

tf2 :: List -> List -> List
tf2 tv10 tv11 = (tf3 tv11 tv10)

cat :: List -> List -> List
cat tv8 tv9 = (tf2 tv8 tv9)

tf5 :: CList -> List
tf5 (Single tv20) = (Elt tv20)
tf5 (Concat tv21 tv22) = (cat (tf4 tv21) (tf4 tv22))

tf4 :: CList -> List
tf4 tv18 = (tf5 tv18)

repr :: CList -> List
repr tv17 = (tf4 tv17)

main :: CList -> Nat
main tv23 = (spec (repr tv23))

tf7 :: CList -> Tuple3
tf7 (Single tv27) = (MakeTuple3 (Succ Zero) tv27)
tf7 (Concat tv28 tv29) = (MakeTuple3 (ite2 (lq (snd3 (tf6 tv28)) (snd3 (tf6 tv29))) (fst3 (tf6 tv28)) (ite2 (nateq (snd3 (tf6 tv29)) (snd3 (tf6 tv28))) (plus (fst3 (tf6 tv29)) (fst3 (tf6 tv28))) (fst3 (tf6 tv29)))) (min (snd3 (tf6 tv29)) (snd3 (tf6 tv28))))

tf6 :: CList -> Tuple3
tf6 tv25 = (tf7 tv25)

reprNew :: CList -> Tuple3
reprNew tv24 = (tf6 tv24)

mainNew :: CList -> Nat
mainNew tv30 = (fst3 (reprNew tv30))

optimize inp0 = (main inp0)=:=(mainNew inp0)
