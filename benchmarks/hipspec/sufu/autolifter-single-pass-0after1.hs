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


data List = Nil Unit | Cons Bool List deriving (Eq, Typeable, Ord)

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
tf1 tv4 (Nil tv5) = tv4
tf1 tv4 (Cons tv6 tv7) = (Cons tv6 (tf0 tv7))

tf0 :: List -> List
tf0 tv2 = (tf1 tv2 tv2)

tf2 :: List -> Bool
tf2 tv9 = (zafter1 (tf0 tv9))

singlepass :: List -> Bool
singlepass tv1 = (tf2 tv1)

and :: Bool -> Bool -> Bool
and False x = False
and x False = False
and True True = True

not :: Bool -> Bool
not True = False
not False = True

or :: Bool -> Bool -> Bool
or True x = True
or x True = True
or False False = False

ite1 :: Bool -> Bool -> Bool
ite1 True y = True
ite1 False y = y

tf4 :: Bool -> List -> Bool
tf4 tv14 (Nil tv15) = False
tf4 tv14 (Cons tv16 tv17) = (ite1 (and tv14 (not tv16)) (tf3 (or tv14 tv16) tv17))

tf3 :: Bool -> List -> Bool
tf3 tv11 tv12 = (tf4 tv11 tv12)

zafter1 :: List -> Bool
zafter1 tv10 = (tf3 False tv10)

main :: List -> Bool
main tv18 = (singlepass tv18)

data Tuple2 = MakeTuple2 Bool Bool deriving (Eq, Typeable, Ord)

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


snd2 :: Tuple2 -> Bool
snd2 (MakeTuple2 x0 x1) = x1

fst2 :: Tuple2 -> Bool
fst2 (MakeTuple2 x0 x1) = x0

tf6 :: List -> Tuple2
tf6 (Nil tv23) = (MakeTuple2 False True)
tf6 (Cons tv24 tv25) = (MakeTuple2 (or (and tv24 (not (snd2 (tf5 tv25)))) (fst2 (tf5 tv25))) (and tv24 (snd2 (tf5 tv25))))

tf5 :: List -> Tuple2
tf5 tv21 = (tf6 tv21)

tf7 :: List -> Bool
tf7 tv26 = (fst2 (tf5 tv26))

singlepassNew :: List -> Bool
singlepassNew tv20 = (tf7 tv20)

mainNew :: List -> Bool
mainNew tv27 = (singlepassNew tv27)

optimize inp0 = (main inp0)=:=(mainNew inp0)
