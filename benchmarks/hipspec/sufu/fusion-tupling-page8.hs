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


data MyNat = Myzero Unit | Mysucc MyNat deriving (Eq, Typeable, Ord)

instance Names MyNat where
  names _ = ["var0_0", "var0_1", "var0_2"]

instance Arbitrary MyNat where
  arbitrary = sized arb
    where
      arb 0 = frequency
        [
          (1, do
            x0 <- arbitrary
            return (Myzero x0)
          )
        ]
      arb n = frequency
        [
          (1, do
            x0 <- arbitrary
            return (Myzero x0)
          ),
          (n, do
            let n' = n - 1
            x0 <- arb n'
            return (Mysucc x0)
          )
        ]

instance Partial MyNat where
  unlifted (Myzero x0) = do
    x0' <- lifted x0
    return (Myzero x0')
  unlifted (Mysucc x0) = do
    x0' <- lifted x0
    return (Mysucc x0')


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


plus :: Nat -> Nat -> Nat
plus Zero x = x
plus (Succ x) y = (Succ (plus x y))

tf1 :: MyNat -> Nat
tf1 (Myzero tv3) = Zero
tf1 (Mysucc (Myzero tv4)) = (Succ Zero)
tf1 (Mysucc (Mysucc tv5)) = (plus (tf0 tv5) (tf0 (Mysucc tv5)))

tf0 :: MyNat -> Nat
tf0 tv1 = (tf1 tv1)

fib :: MyNat -> Nat
fib tv0 = (tf0 tv0)

tf3 :: MyNat -> MyNat -> MyNat
tf3 tv9 (Myzero tv10) = tv9
tf3 tv9 (Mysucc tv11) = (Mysucc (tf2 tv11))

tf2 :: MyNat -> MyNat
tf2 tv7 = (tf3 tv7 tv7)

repr :: MyNat -> MyNat
repr tv6 = (tf2 tv6)

main :: MyNat -> Nat
main tv12 = (fib (repr tv12))

data Tuple0 = MakeTuple0 Nat Nat deriving (Eq, Typeable, Ord)

instance Names Tuple0 where
  names _ = ["var0_0", "var0_1", "var0_2"]

instance Arbitrary Tuple0 where
  arbitrary = sized arb
    where
      arb 0 = frequency
        [
          (1, do
            x0 <- arbitrary
            x1 <- arbitrary
            return (MakeTuple0 x0 x1)
          )
        ]
      arb n = frequency
        [
          (1, do
            x0 <- arbitrary
            x1 <- arbitrary
            return (MakeTuple0 x0 x1)
          )
        ]

instance Partial Tuple0 where
  unlifted (MakeTuple0 x0 x1) = do
    x0' <- lifted x0
    x1' <- lifted x1
    return (MakeTuple0 x0' x1')


nateq :: Nat -> Nat -> Bool
nateq Zero Zero = True
nateq Zero (Succ x) = False
nateq (Succ x) Zero = False
nateq (Succ x) (Succ y) = (nateq x y)

fst0 :: Tuple0 -> Nat
fst0 (MakeTuple0 x0 x1) = x0

snd0 :: Tuple0 -> Nat
snd0 (MakeTuple0 x0 x1) = x1

ite1 :: Bool -> Nat -> Nat -> Nat
ite1 True x y = x
ite1 False x y = y

tf5 :: MyNat -> Tuple0
tf5 (Myzero tv16) = (MakeTuple0 Zero Zero)
tf5 (Mysucc tv17) = (MakeTuple0 (ite1 (nateq (fst0 (tf4 tv17)) (snd0 (tf4 tv17))) (plus (Succ Zero) (fst0 (tf4 tv17))) (plus (fst0 (tf4 tv17)) (snd0 (tf4 tv17)))) (fst0 (tf4 tv17)))

tf4 :: MyNat -> Tuple0
tf4 tv14 = (tf5 tv14)

reprNew :: MyNat -> Tuple0
reprNew tv13 = (tf4 tv13)

mainNew :: MyNat -> Nat
mainNew tv18 = (fst0 (reprNew tv18))

optimize inp0 = (main inp0)=:=(mainNew inp0)
