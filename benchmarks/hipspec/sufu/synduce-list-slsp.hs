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


data CnList = Sglt Nat | Cat CnList Nat CnList deriving (Eq, Typeable, Ord)

instance Names CnList where
  names _ = ["var0_0", "var0_1", "var0_2"]

instance Arbitrary CnList where
  arbitrary = sized arb
    where
      arb 0 = frequency
        [
          (1, do
            x0 <- arbitrary
            return (Sglt x0)
          )
        ]
      arb n = frequency
        [
          (1, do
            x0 <- arbitrary
            return (Sglt x0)
          ),
          (n, do
            let n' = n `div` 2
            x0 <- arb n'
            x1 <- arbitrary
            x2 <- arb n'
            return (Cat x0 x1 x2)
          )
        ]

instance Partial CnList where
  unlifted (Sglt x0) = do
    x0' <- lifted x0
    return (Sglt x0')
  unlifted (Cat x0 x1 x2) = do
    x0' <- lifted x0
    x1' <- lifted x1
    x2' <- lifted x2
    return (Cat x0' x1' x2')


gq :: Nat -> Nat -> Bool
gq Zero x = False
gq (Succ x) Zero = True
gq (Succ x) (Succ y) = (gq x y)

ite2 :: Bool -> Nat -> Nat -> Nat
ite2 True x y = x
ite2 False x y = y

max :: Nat -> Nat -> Nat
max tv0 tv1 = (ite2 (gq tv0 tv1) tv0 tv1)

tf1 :: List -> List -> List
tf1 tv7 (Elt tv8) = (Cons tv8 tv7)
tf1 tv7 (Cons tv9 tv10) = (Cons tv9 (tf0 tv10 tv7))

tf0 :: List -> List -> List
tf0 tv4 tv5 = (tf1 tv5 tv4)

catlist :: List -> List -> List
catlist tv2 tv3 = (tf0 tv2 tv3)

tf3 :: CnList -> List
tf3 (Sglt tv14) = (Elt tv14)
tf3 (Cat tv15 tv16 tv17) = (catlist (tf2 tv15) (tf2 tv17))

tf2 :: CnList -> List
tf2 tv12 = (tf3 tv12)

repr :: CnList -> List
repr tv11 = (tf2 tv11)

data Tuple3 = MakeTuple3 Nat Bool deriving (Eq, Typeable, Ord)

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


geq :: Nat -> Nat -> Bool
geq Zero (Succ x) = False
geq x Zero = True
geq (Succ x) (Succ y) = (geq x y)

and :: Bool -> Bool -> Bool
and False x = False
and x False = False
and True True = True

snd3 :: Tuple3 -> Bool
snd3 (MakeTuple3 x0 x1) = x1

plus :: Nat -> Nat -> Nat
plus Zero x = x
plus (Succ x) y = (Succ (plus x y))

fst3 :: Tuple3 -> Nat
fst3 (MakeTuple3 x0 x1) = x0

tf5 :: List -> Tuple3
tf5 (Elt tv21) = (MakeTuple3 (max Zero tv21) (geq tv21 Zero))
tf5 (Cons tv22 tv23) = (MakeTuple3 (ite2 (and (snd3 (tf4 tv23)) (geq tv22 Zero)) (plus tv22 (fst3 (tf4 tv23))) (fst3 (tf4 tv23))) (and (snd3 (tf4 tv23)) (geq tv22 Zero)))

tf4 :: List -> Tuple3
tf4 tv19 = (tf5 tv19)

spec :: List -> Nat
spec tv18 = (fst3 (tf4 tv18))

main :: CnList -> Nat
main tv24 = (spec (repr tv24))

data Tuple4 = MakeTuple4 Nat Nat Nat Nat deriving (Eq, Typeable, Ord)

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
            x2 <- arbitrary
            x3 <- arbitrary
            return (MakeTuple4 x0 x1 x2 x3)
          )
        ]
      arb n = frequency
        [
          (1, do
            x0 <- arbitrary
            x1 <- arbitrary
            x2 <- arbitrary
            x3 <- arbitrary
            return (MakeTuple4 x0 x1 x2 x3)
          )
        ]

instance Partial Tuple4 where
  unlifted (MakeTuple4 x0 x1 x2 x3) = do
    x0' <- lifted x0
    x1' <- lifted x1
    x2' <- lifted x2
    x3' <- lifted x3
    return (MakeTuple4 x0' x1' x2' x3')


times :: Nat -> Nat -> Nat
times Zero x = Zero
times (Succ x) y = (plus (times x y) y)

or :: Bool -> Bool -> Bool
or True x = True
or x True = True
or False False = False

nateq :: Nat -> Nat -> Bool
nateq Zero Zero = True
nateq Zero (Succ x) = False
nateq (Succ x) Zero = False
nateq (Succ x) (Succ y) = (nateq x y)

fourth4 :: Tuple4 -> Nat
fourth4 (MakeTuple4 x0 x1 x2 x3) = x3

fst4 :: Tuple4 -> Nat
fst4 (MakeTuple4 x0 x1 x2 x3) = x0

third4 :: Tuple4 -> Nat
third4 (MakeTuple4 x0 x1 x2 x3) = x2

lq :: Nat -> Nat -> Bool
lq Zero (Succ x) = True
lq x Zero = False
lq (Succ x) (Succ y) = (lq x y)

snd4 :: Tuple4 -> Nat
snd4 (MakeTuple4 x0 x1 x2 x3) = x1

tf7 :: CnList -> Tuple4
tf7 (Sglt tv28) = (MakeTuple4 (max tv28 Zero) (times (Succ (Succ Zero)) (max tv28 Zero)) tv28 tv28)
tf7 (Cat tv29 tv30 tv31) = (MakeTuple4 (ite2 (or (and (nateq (fourth4 (tf6 tv31)) Zero) (nateq (fst4 (tf6 tv31)) (third4 (tf6 tv31)))) (lq (fst4 (tf6 tv31)) (snd4 (tf6 tv31)))) (plus (fst4 (tf6 tv31)) (fst4 (tf6 tv29))) (fst4 (tf6 tv31))) (ite2 (or (or (and (lq (fst4 (tf6 tv31)) (snd4 (tf6 tv31))) (lq (fst4 (tf6 tv29)) (snd4 (tf6 tv29)))) (and (nateq (fourth4 (tf6 tv31)) Zero) (nateq (fst4 (tf6 tv31)) (third4 (tf6 tv31))))) (and (nateq (fourth4 (tf6 tv29)) Zero) (nateq (fst4 (tf6 tv29)) (third4 (tf6 tv29))))) (plus (snd4 (tf6 tv31)) (snd4 (tf6 tv29))) (ite2 (or (and (lq Zero (fourth4 (tf6 tv31))) (nateq (fst4 (tf6 tv31)) (snd4 (tf6 tv31)))) (lq (third4 (tf6 tv31)) (fst4 (tf6 tv31)))) (fst4 (tf6 tv31)) (plus (fst4 (tf6 tv31)) (fst4 (tf6 tv29))))) (plus (third4 (tf6 tv31)) (third4 (tf6 tv29))) (max (fourth4 (tf6 tv31)) (fourth4 (tf6 tv29))))

tf6 :: CnList -> Tuple4
tf6 tv26 = (tf7 tv26)

reprNew :: CnList -> Tuple4
reprNew tv25 = (tf6 tv25)

mainNew :: CnList -> Nat
mainNew tv32 = (fst4 (reprNew tv32))

optimize inp0 = (main inp0)=:=(mainNew inp0)
