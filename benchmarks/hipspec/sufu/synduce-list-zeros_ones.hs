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


data List = Elt Bool | Cons Bool List deriving (Eq, Typeable, Ord)

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


data CList = Single Bool | Concat CList CList deriving (Eq, Typeable, Ord)

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


tf1 :: List -> List -> List
tf1 tv5 (Elt tv6) = (Cons tv6 tv5)
tf1 tv5 (Cons tv7 tv8) = (Cons tv7 (tf0 tv8 tv5))

tf0 :: List -> List -> List
tf0 tv2 tv3 = (tf1 tv3 tv2)

catlist :: List -> List -> List
catlist tv0 tv1 = (tf0 tv0 tv1)

tf3 :: CList -> List
tf3 (Single tv12) = (Elt tv12)
tf3 (Concat tv13 tv14) = (catlist (tf2 tv13) (tf2 tv14))

tf2 :: CList -> List
tf2 tv10 = (tf3 tv10)

repr :: CList -> List
repr tv9 = (tf2 tv9)

data Tuple2 = MakeTuple2 Bool Bool Bool deriving (Eq, Typeable, Ord)

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


and :: Bool -> Bool -> Bool
and False x = False
and x False = False
and True True = True

fst2 :: Tuple2 -> Bool
fst2 (MakeTuple2 x0 x1 x2) = x0

snd2 :: Tuple2 -> Bool
snd2 (MakeTuple2 x0 x1 x2) = x1

or :: Bool -> Bool -> Bool
or True x = True
or x True = True
or False False = False

not :: Bool -> Bool
not True = False
not False = True

third2 :: Tuple2 -> Bool
third2 (MakeTuple2 x0 x1 x2) = x2

tf5 :: List -> Tuple2
tf5 (Elt tv18) = (MakeTuple2 tv18 True tv18)
tf5 (Cons tv19 tv20) = (MakeTuple2 (and (fst2 (tf4 tv20)) tv19) (and (snd2 (tf4 tv20)) (or (fst2 (tf4 tv20)) (not tv19))) (third2 (tf4 tv20)))

tf4 :: List -> Tuple2
tf4 tv16 = (tf5 tv16)

spec :: List -> Bool
spec tv15 = (snd2 (tf4 tv15))

main :: CList -> Bool
main tv21 = (spec (repr tv21))

tf7 :: CList -> Tuple2
tf7 (Single tv25) = (MakeTuple2 True tv25 tv25)
tf7 (Concat tv26 tv27) = (MakeTuple2 (or (and (and (not (third2 (tf6 tv26))) (fst2 (tf6 tv26))) (fst2 (tf6 tv27))) (and (and (fst2 (tf6 tv26)) (fst2 (tf6 tv27))) (snd2 (tf6 tv27)))) (snd2 (tf6 tv26)) (third2 (tf6 tv27)))

tf6 :: CList -> Tuple2
tf6 tv23 = (tf7 tv23)

reprNew :: CList -> Tuple2
reprNew tv22 = (tf6 tv22)

mainNew :: CList -> Bool
mainNew tv28 = (fst2 (reprNew tv28))

optimize inp0 = (main inp0)=:=(mainNew inp0)
