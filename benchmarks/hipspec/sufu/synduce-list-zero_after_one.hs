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


data BList = Nil Unit | Cons Bool BList deriving (Eq, Typeable, Ord)

instance Names BList where
  names _ = ["var0_0", "var0_1", "var0_2"]

instance Arbitrary BList where
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

instance Partial BList where
  unlifted (Nil x0) = do
    x0' <- lifted x0
    return (Nil x0')
  unlifted (Cons x0 x1) = do
    x0' <- lifted x0
    x1' <- lifted x1
    return (Cons x0' x1')


data CList = Emp Unit | Single Bool | Concat CList CList deriving (Eq, Typeable, Ord)

instance Names CList where
  names _ = ["var0_0", "var0_1", "var0_2"]

instance Arbitrary CList where
  arbitrary = sized arb
    where
      arb 0 = frequency
        [
          (1, do
            x0 <- arbitrary
            return (Emp x0)
          ),
          (1, do
            x0 <- arbitrary
            return (Single x0)
          )
        ]
      arb n = frequency
        [
          (1, do
            x0 <- arbitrary
            return (Emp x0)
          ),
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
  unlifted (Emp x0) = do
    x0' <- lifted x0
    return (Emp x0')
  unlifted (Single x0) = do
    x0' <- lifted x0
    return (Single x0')
  unlifted (Concat x0 x1) = do
    x0' <- lifted x0
    x1' <- lifted x1
    return (Concat x0' x1')


or :: Bool -> Bool -> Bool
or True x = True
or x True = True
or False False = False

opor :: Bool -> Bool -> Bool
opor tv0 tv1 = (or tv0 tv1)

tf1 :: BList -> BList -> BList
tf1 tv7 (Nil tv8) = tv7
tf1 tv7 (Cons tv9 tv10) = (Cons tv9 (tf0 tv10 tv7))

tf0 :: BList -> BList -> BList
tf0 tv4 tv5 = (tf1 tv5 tv4)

catlist :: BList -> BList -> BList
catlist tv2 tv3 = (tf0 tv2 tv3)

tf3 :: CList -> BList
tf3 (Emp tv14) = (Nil Null)
tf3 (Single tv15) = (Cons tv15 (Nil Null))
tf3 (Concat tv16 tv17) = (catlist (tf2 tv16) (tf2 tv17))

tf2 :: CList -> BList
tf2 tv12 = (tf3 tv12)

repr :: CList -> BList
repr tv11 = (tf2 tv11)

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


fst2 :: Tuple2 -> Bool
fst2 (MakeTuple2 x0 x1 x2) = x0

snd2 :: Tuple2 -> Bool
snd2 (MakeTuple2 x0 x1 x2) = x1

and :: Bool -> Bool -> Bool
and False x = False
and x False = False
and True True = True

not :: Bool -> Bool
not True = False
not False = True

third2 :: Tuple2 -> Bool
third2 (MakeTuple2 x0 x1 x2) = x2

tf5 :: BList -> Tuple2
tf5 (Nil tv21) = (MakeTuple2 False False False)
tf5 (Cons tv22 tv23) = (MakeTuple2 (or (fst2 (tf4 tv23)) tv22) (or (snd2 (tf4 tv23)) (and (fst2 (tf4 tv23)) (not tv22))) (or (third2 (tf4 tv23)) (not tv22)))

tf4 :: BList -> Tuple2
tf4 tv19 = (tf5 tv19)

spec :: BList -> Bool
spec tv18 = (snd2 (tf4 tv18))

main :: CList -> Bool
main tv24 = (spec (repr tv24))

data Tuple3 = MakeTuple3 Bool Bool Bool Bool deriving (Eq, Typeable, Ord)

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
            x3 <- arbitrary
            return (MakeTuple3 x0 x1 x2 x3)
          )
        ]
      arb n = frequency
        [
          (1, do
            x0 <- arbitrary
            x1 <- arbitrary
            x2 <- arbitrary
            x3 <- arbitrary
            return (MakeTuple3 x0 x1 x2 x3)
          )
        ]

instance Partial Tuple3 where
  unlifted (MakeTuple3 x0 x1 x2 x3) = do
    x0' <- lifted x0
    x1' <- lifted x1
    x2' <- lifted x2
    x3' <- lifted x3
    return (MakeTuple3 x0' x1' x2' x3')


snd3 :: Tuple3 -> Bool
snd3 (MakeTuple3 x0 x1 x2 x3) = x1

third3 :: Tuple3 -> Bool
third3 (MakeTuple3 x0 x1 x2 x3) = x2

fst3 :: Tuple3 -> Bool
fst3 (MakeTuple3 x0 x1 x2 x3) = x0

fourth3 :: Tuple3 -> Bool
fourth3 (MakeTuple3 x0 x1 x2 x3) = x3

tf7 :: CList -> Tuple3
tf7 (Emp tv28) = (MakeTuple3 False True True False)
tf7 (Single tv29) = (MakeTuple3 False tv29 False False)
tf7 (Concat tv30 tv31) = (MakeTuple3 (or (or (and (and (not (snd3 (tf6 tv30))) (not (third3 (tf6 tv31)))) (opor (fst3 (tf6 tv31)) (snd3 (tf6 tv31)))) (and (and (opor (fst3 (tf6 tv31)) (fourth3 (tf6 tv30))) (not (third3 (tf6 tv31)))) (opor (fst3 (tf6 tv31)) (snd3 (tf6 tv31))))) (opor (fst3 (tf6 tv31)) (fst3 (tf6 tv30)))) (or (and (snd3 (tf6 tv31)) (snd3 (tf6 tv30))) (and (snd3 (tf6 tv30)) (not (third3 (tf6 tv30))))) (and (third3 (tf6 tv31)) (third3 (tf6 tv30))) (or (or (and (and (not (snd3 (tf6 tv31))) (not (third3 (tf6 tv30)))) (opor (snd3 (tf6 tv31)) (snd3 (tf6 tv30)))) (and (and (not (snd3 (tf6 tv30))) (not (third3 (tf6 tv31)))) (opor (snd3 (tf6 tv31)) (fourth3 (tf6 tv31))))) (opor (fourth3 (tf6 tv31)) (fourth3 (tf6 tv30)))))

tf6 :: CList -> Tuple3
tf6 tv26 = (tf7 tv26)

reprNew :: CList -> Tuple3
reprNew tv25 = (tf6 tv25)

mainNew :: CList -> Bool
mainNew tv32 = (fst3 (reprNew tv32))

optimize inp0 = (main inp0)=:=(mainNew inp0)
