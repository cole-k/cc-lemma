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


data NList = Line List | Ncons List NList deriving (Eq, Typeable, Ord)

instance Names NList where
  names _ = ["var0_0", "var0_1", "var0_2"]

instance Arbitrary NList where
  arbitrary = sized arb
    where
      arb 0 = frequency
        [
          (1, do
            x0 <- arbitrary
            return (Line x0)
          )
        ]
      arb n = frequency
        [
          (1, do
            x0 <- arbitrary
            return (Line x0)
          ),
          (n, do
            let n' = n - 1
            x0 <- arbitrary
            x1 <- arb n'
            return (Ncons x0 x1)
          )
        ]

instance Partial NList where
  unlifted (Line x0) = do
    x0' <- lifted x0
    return (Line x0')
  unlifted (Ncons x0 x1) = do
    x0' <- lifted x0
    x1' <- lifted x1
    return (Ncons x0' x1')


lq :: Nat -> Nat -> Bool
lq Zero (Succ x) = True
lq x Zero = False
lq (Succ x) (Succ y) = (lq x y)

ite2 :: Bool -> Nat -> Nat -> Nat
ite2 True x y = x
ite2 False x y = y

max :: Nat -> Nat -> Nat
max tv0 tv1 = (ite2 (lq tv0 tv1) tv1 tv0)

gq :: Nat -> Nat -> Bool
gq Zero x = False
gq (Succ x) Zero = True
gq (Succ x) (Succ y) = (gq x y)

min :: Nat -> Nat -> Nat
min tv2 tv3 = (ite2 (gq tv2 tv3) tv3 tv2)

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

tf1 :: List -> Tuple3
tf1 (Elt tv7) = (MakeTuple3 tv7 tv7)
tf1 (Cons tv8 tv9) = (MakeTuple3 (min tv8 (fst3 (tf0 tv9))) (max tv8 (snd3 (tf0 tv9))))

tf0 :: List -> Tuple3
tf0 tv5 = (tf1 tv5)

interval :: List -> Tuple3
interval tv4 = (tf0 tv4)

data Tuple4 = MakeTuple4 Nat Nat Bool deriving (Eq, Typeable, Ord)

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
            return (MakeTuple4 x0 x1 x2)
          )
        ]
      arb n = frequency
        [
          (1, do
            x0 <- arbitrary
            x1 <- arbitrary
            x2 <- arbitrary
            return (MakeTuple4 x0 x1 x2)
          )
        ]

instance Partial Tuple4 where
  unlifted (MakeTuple4 x0 x1 x2) = do
    x0' <- lifted x0
    x1' <- lifted x1
    x2' <- lifted x2
    return (MakeTuple4 x0' x1' x2')


fst4 :: Tuple4 -> Nat
fst4 (MakeTuple4 x0 x1 x2) = x0

snd4 :: Tuple4 -> Nat
snd4 (MakeTuple4 x0 x1 x2) = x1

and :: Bool -> Bool -> Bool
and False x = False
and x False = False
and True True = True

third4 :: Tuple4 -> Bool
third4 (MakeTuple4 x0 x1 x2) = x2

leq :: Nat -> Nat -> Bool
leq Zero x = True
leq (Succ x) Zero = False
leq (Succ x) (Succ y) = (leq x y)

tf3 :: NList -> Tuple4
tf3 (Line tv13) = (MakeTuple4 (fst3 (interval tv13)) (snd3 (interval tv13)) True)
tf3 (Ncons tv14 tv15) = (MakeTuple4 (min (fst4 (tf2 tv15)) (fst3 (interval tv14))) (max (snd4 (tf2 tv15)) (snd3 (interval tv14))) (and (third4 (tf2 tv15)) (and (leq (fst4 (tf2 tv15)) (fst3 (interval tv14))) (leq (snd4 (tf2 tv15)) (snd3 (interval tv14))))))

tf2 :: NList -> Tuple4
tf2 tv11 = (tf3 tv11)

spec :: NList -> Bool
spec tv10 = (third4 (tf2 tv10))

tf5 :: NList -> NList -> NList
tf5 tv19 (Line tv20) = tv19
tf5 tv19 (Ncons tv21 tv22) = (Ncons tv21 (tf4 tv22))

tf4 :: NList -> NList
tf4 tv17 = (tf5 tv17 tv17)

target :: NList -> NList
target tv16 = (tf4 tv16)

main :: NList -> Bool
main tv23 = (spec (target tv23))

data Tuple5 = MakeTuple5 Bool Nat Nat deriving (Eq, Typeable, Ord)

instance Names Tuple5 where
  names _ = ["var0_0", "var0_1", "var0_2"]

instance Arbitrary Tuple5 where
  arbitrary = sized arb
    where
      arb 0 = frequency
        [
          (1, do
            x0 <- arbitrary
            x1 <- arbitrary
            x2 <- arbitrary
            return (MakeTuple5 x0 x1 x2)
          )
        ]
      arb n = frequency
        [
          (1, do
            x0 <- arbitrary
            x1 <- arbitrary
            x2 <- arbitrary
            return (MakeTuple5 x0 x1 x2)
          )
        ]

instance Partial Tuple5 where
  unlifted (MakeTuple5 x0 x1 x2) = do
    x0' <- lifted x0
    x1' <- lifted x1
    x2' <- lifted x2
    return (MakeTuple5 x0' x1' x2')


snd5 :: Tuple5 -> Nat
snd5 (MakeTuple5 x0 x1 x2) = x1

fst5 :: Tuple5 -> Bool
fst5 (MakeTuple5 x0 x1 x2) = x0

third5 :: Tuple5 -> Nat
third5 (MakeTuple5 x0 x1 x2) = x2

tf7 :: NList -> Tuple5
tf7 (Line tv27) = (MakeTuple5 True (fst3 (interval tv27)) (snd3 (interval tv27)))
tf7 (Ncons tv28 tv29) = (MakeTuple5 (and (and (leq (snd5 (tf6 tv29)) (fst3 (interval tv28))) (fst5 (tf6 tv29))) (leq (third5 (tf6 tv29)) (snd3 (interval tv28)))) (snd5 (tf6 tv29)) (snd3 (interval tv28)))

tf6 :: NList -> Tuple5
tf6 tv25 = (tf7 tv25)

targetNew :: NList -> Tuple5
targetNew tv24 = (tf6 tv24)

mainNew :: NList -> Bool
mainNew tv30 = (fst5 (targetNew tv30))

optimize inp0 = (main inp0)=:=(mainNew inp0)
