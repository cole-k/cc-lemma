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


data SList = Elt Nat | Cons Nat SList deriving (Eq, Typeable, Ord)

instance Names SList where
  names _ = ["var0_0", "var0_1", "var0_2"]

instance Arbitrary SList where
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

instance Partial SList where
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


tf1 :: SList -> SList -> SList
tf1 tv5 (Elt tv6) = (Cons tv6 tv5)
tf1 tv5 (Cons tv7 tv8) = (Cons tv7 (tf0 tv8 tv5))

tf0 :: SList -> SList -> SList
tf0 tv2 tv3 = (tf1 tv3 tv2)

catlist :: SList -> SList -> SList
catlist tv0 tv1 = (tf0 tv0 tv1)

tf3 :: CList -> SList
tf3 (Single tv12) = (Elt tv12)
tf3 (Concat tv13 tv14) = (catlist (tf2 tv13) (tf2 tv14))

tf2 :: CList -> SList
tf2 tv10 = (tf3 tv10)

repr :: CList -> SList
repr tv9 = (tf2 tv9)

data Tuple2 = MakeTuple2 Nat Nat Bool deriving (Eq, Typeable, Ord)

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
            x2 <- arbitrary
            return (MakeTuple2 x0 x1 x2)
          )
        ]
      arb n = frequency
        [
          (1, do
            x0 <- arbitrary
            x1 <- arbitrary
            x2 <- arbitrary
            return (MakeTuple2 x0 x1 x2)
          )
        ]

instance Partial Tuple2 where
  unlifted (MakeTuple2 x0 x1 x2) = do
    x0' <- lifted x0
    x1' <- lifted x1
    x2' <- lifted x2
    return (MakeTuple2 x0' x1' x2')


snd2 :: Tuple2 -> Nat
snd2 (MakeTuple2 x0 x1 x2) = x1

and :: Bool -> Bool -> Bool
and False x = False
and x False = False
and True True = True

third2 :: Tuple2 -> Bool
third2 (MakeTuple2 x0 x1 x2) = x2

lq :: Nat -> Nat -> Bool
lq Zero (Succ x) = True
lq x Zero = False
lq (Succ x) (Succ y) = (lq x y)

fst2 :: Tuple2 -> Nat
fst2 (MakeTuple2 x0 x1 x2) = x0

tf5 :: SList -> Tuple2
tf5 (Elt tv18) = (MakeTuple2 tv18 tv18 True)
tf5 (Cons tv19 tv20) = (MakeTuple2 tv19 (snd2 (tf4 tv20)) (and (third2 (tf4 tv20)) (lq tv19 (fst2 (tf4 tv20)))))

tf4 :: SList -> Tuple2
tf4 tv16 = (tf5 tv16)

spec :: SList -> Bool
spec tv15 = (third2 (tf4 tv15))

main :: CList -> Bool
main tv21 = (spec (repr tv21))

data Tuple3 = MakeTuple3 Bool Nat Nat deriving (Eq, Typeable, Ord)

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


fst3 :: Tuple3 -> Bool
fst3 (MakeTuple3 x0 x1 x2) = x0

third3 :: Tuple3 -> Nat
third3 (MakeTuple3 x0 x1 x2) = x2

snd3 :: Tuple3 -> Nat
snd3 (MakeTuple3 x0 x1 x2) = x1

tf7 :: CList -> Tuple3
tf7 (Single tv25) = (MakeTuple3 True tv25 tv25)
tf7 (Concat tv26 tv27) = (MakeTuple3 (and (and (fst3 (tf6 tv26)) (fst3 (tf6 tv27))) (lq (third3 (tf6 tv26)) (snd3 (tf6 tv27)))) (snd3 (tf6 tv26)) (third3 (tf6 tv27)))

tf6 :: CList -> Tuple3
tf6 tv23 = (tf7 tv23)

reprNew :: CList -> Tuple3
reprNew tv22 = (tf6 tv22)

mainNew :: CList -> Bool
mainNew tv28 = (fst3 (reprNew tv28))

optimize inp0 = (main inp0)=:=(mainNew inp0)
