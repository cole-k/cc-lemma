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


data Tree = Leaf Nat | Node Tree Tree deriving (Eq, Typeable, Ord)

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
            x0 <- arb n'
            x1 <- arb n'
            return (Node x0 x1)
          )
        ]

instance Partial Tree where
  unlifted (Leaf x0) = do
    x0' <- lifted x0
    return (Leaf x0')
  unlifted (Node x0 x1) = do
    x0' <- lifted x0
    x1' <- lifted x1
    return (Node x0' x1')


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


tf1 :: List -> List -> List
tf1 tv5 (Nil tv6) = tv5
tf1 tv5 (Cons tv7 tv8) = (Cons tv7 (tf0 tv8 tv5))

tf0 :: List -> List -> List
tf0 tv2 tv3 = (tf1 tv3 tv2)

cat :: List -> List -> List
cat tv0 tv1 = (tf0 tv0 tv1)

lq :: Nat -> Nat -> Bool
lq Zero (Succ x) = True
lq x Zero = False
lq (Succ x) (Succ y) = (lq x y)

ite2 :: Bool -> Nat -> Nat -> Nat
ite2 True x y = x
ite2 False x y = y

max :: Nat -> Nat -> Nat
max tv9 tv10 = (ite2 (lq tv9 tv10) tv10 tv9)

plus :: Nat -> Nat -> Nat
plus Zero x = x
plus (Succ x) y = (Succ (plus x y))

tf3 :: Tree -> Nat
tf3 (Leaf tv14) = Zero
tf3 (Node tv15 tv16) = (plus (Succ Zero) (max (tf2 tv15) (tf2 tv16)))

tf2 :: Tree -> Nat
tf2 tv12 = (tf3 tv12)

depth :: Tree -> Nat
depth tv11 = (tf2 tv11)

data Tuple3 = MakeTuple3 List Tree deriving (Eq, Typeable, Ord)

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


gq :: Nat -> Nat -> Bool
gq Zero x = False
gq (Succ x) Zero = True
gq (Succ x) (Succ y) = (gq x y)

snd3 :: Tuple3 -> Tree
snd3 (MakeTuple3 x0 x1) = x1

fst3 :: Tuple3 -> List
fst3 (MakeTuple3 x0 x1) = x0

nateq :: Nat -> Nat -> Bool
nateq Zero Zero = True
nateq Zero (Succ x) = False
nateq (Succ x) Zero = False
nateq (Succ x) (Succ y) = (nateq x y)

ite3 :: Bool -> Tuple3 -> Tuple3 -> Tuple3
ite3 True x y = x
ite3 False x y = y

tf5 :: Tree -> Tree -> Tuple3
tf5 tv20 (Leaf tv21) = (MakeTuple3 (Cons tv21 (Nil Null)) tv20)
tf5 tv20 (Node tv22 tv23) = (ite3 (gq (depth (snd3 (tf4 tv22))) (depth (snd3 (tf4 tv23)))) (MakeTuple3 (fst3 (tf4 tv22)) tv20) (ite3 (nateq (depth (snd3 (tf4 tv22))) (depth (snd3 (tf4 tv23)))) (MakeTuple3 (cat (fst3 (tf4 tv22)) (fst3 (tf4 tv23))) tv20) (MakeTuple3 (fst3 (tf4 tv23)) tv20)))

tf4 :: Tree -> Tuple3
tf4 tv18 = (tf5 tv18 tv18)

deepest :: Tree -> Tuple3
deepest tv17 = (tf4 tv17)

main :: Tree -> List
main tv24 = (fst3 (deepest tv24))

data Tuple4 = MakeTuple4 List Nat deriving (Eq, Typeable, Ord)

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


snd4 :: Tuple4 -> Nat
snd4 (MakeTuple4 x0 x1) = x1

fst4 :: Tuple4 -> List
fst4 (MakeTuple4 x0 x1) = x0

ite4 :: Bool -> Tuple4 -> Tuple4 -> Tuple4
ite4 True x y = x
ite4 False x y = y

tf7 :: Tree -> Tuple4
tf7 (Leaf tv28) = (MakeTuple4 (Cons tv28 (Nil Null)) Zero)
tf7 (Node tv29 tv30) = (ite4 (gq (snd4 (tf6 tv29)) (snd4 (tf6 tv30))) (MakeTuple4 (fst4 (tf6 tv29)) (plus (Succ Zero) (snd4 (tf6 tv29)))) (ite4 (nateq (snd4 (tf6 tv29)) (snd4 (tf6 tv30))) (MakeTuple4 (cat (fst4 (tf6 tv29)) (fst4 (tf6 tv30))) (plus (snd4 (tf6 tv29)) (Succ Zero))) (MakeTuple4 (fst4 (tf6 tv30)) (plus (snd4 (tf6 tv30)) (Succ Zero)))))

tf6 :: Tree -> Tuple4
tf6 tv26 = (tf7 tv26)

deepestNew :: Tree -> Tuple4
deepestNew tv25 = (tf6 tv25)

mainNew :: Tree -> List
mainNew tv31 = (fst4 (deepestNew tv31))

optimize inp0 = (main inp0)=:=(mainNew inp0)
