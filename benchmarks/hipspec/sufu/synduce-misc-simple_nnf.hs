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


data Formula = Flit Bool | Fand Formula Formula | Forr Formula Formula | Fnot Formula deriving (Eq, Typeable, Ord)

instance Names Formula where
  names _ = ["var0_0", "var0_1", "var0_2"]

instance Arbitrary Formula where
  arbitrary = sized arb
    where
      arb 0 = frequency
        [
          (1, do
            x0 <- arbitrary
            return (Flit x0)
          )
        ]
      arb n = frequency
        [
          (1, do
            x0 <- arbitrary
            return (Flit x0)
          ),
          (n, do
            let n' = n `div` 2
            x0 <- arb n'
            x1 <- arb n'
            return (Fand x0 x1)
          ),
          (n, do
            let n' = n `div` 2
            x0 <- arb n'
            x1 <- arb n'
            return (Forr x0 x1)
          ),
          (n, do
            let n' = n - 1
            x0 <- arb n'
            return (Fnot x0)
          )
        ]

instance Partial Formula where
  unlifted (Flit x0) = do
    x0' <- lifted x0
    return (Flit x0')
  unlifted (Fand x0 x1) = do
    x0' <- lifted x0
    x1' <- lifted x1
    return (Fand x0' x1')
  unlifted (Forr x0 x1) = do
    x0' <- lifted x0
    x1' <- lifted x1
    return (Forr x0' x1')
  unlifted (Fnot x0) = do
    x0' <- lifted x0
    return (Fnot x0')


data NnfFormula = Nfneglit Bool | Nflit Bool | Nfand NnfFormula NnfFormula | Nfor NnfFormula NnfFormula deriving (Eq, Typeable, Ord)

instance Names NnfFormula where
  names _ = ["var0_0", "var0_1", "var0_2"]

instance Arbitrary NnfFormula where
  arbitrary = sized arb
    where
      arb 0 = frequency
        [
          (1, do
            x0 <- arbitrary
            return (Nfneglit x0)
          ),
          (1, do
            x0 <- arbitrary
            return (Nflit x0)
          )
        ]
      arb n = frequency
        [
          (1, do
            x0 <- arbitrary
            return (Nfneglit x0)
          ),
          (1, do
            x0 <- arbitrary
            return (Nflit x0)
          ),
          (n, do
            let n' = n `div` 2
            x0 <- arb n'
            x1 <- arb n'
            return (Nfand x0 x1)
          ),
          (n, do
            let n' = n `div` 2
            x0 <- arb n'
            x1 <- arb n'
            return (Nfor x0 x1)
          )
        ]

instance Partial NnfFormula where
  unlifted (Nfneglit x0) = do
    x0' <- lifted x0
    return (Nfneglit x0')
  unlifted (Nflit x0) = do
    x0' <- lifted x0
    return (Nflit x0')
  unlifted (Nfand x0 x1) = do
    x0' <- lifted x0
    x1' <- lifted x1
    return (Nfand x0' x1')
  unlifted (Nfor x0 x1) = do
    x0' <- lifted x0
    x1' <- lifted x1
    return (Nfor x0' x1')


and :: Bool -> Bool -> Bool
and False x = False
and x False = False
and True True = True

or :: Bool -> Bool -> Bool
or True x = True
or x True = True
or False False = False

ite2 :: Bool -> Bool
ite2 True = False
ite2 False = True

tf1 :: Formula -> Bool
tf1 (Flit tv3) = tv3
tf1 (Fand tv4 tv5) = (and (tf0 tv4) (tf0 tv5))
tf1 (Forr tv6 tv7) = (or (tf0 tv6) (tf0 tv7))
tf1 (Fnot tv8) = (ite2 (tf0 tv8))

tf0 :: Formula -> Bool
tf0 tv1 = (tf1 tv1)

spec :: Formula -> Bool
spec tv0 = (tf0 tv0)

tf3 :: NnfFormula -> Formula
tf3 (Nflit tv12) = (Flit tv12)
tf3 (Nfneglit tv13) = (Fnot (Flit tv13))
tf3 (Nfand tv14 tv15) = (Fand (tf2 tv14) (tf2 tv15))
tf3 (Nfor tv16 tv17) = (Forr (tf2 tv16) (tf2 tv17))

tf2 :: NnfFormula -> Formula
tf2 tv10 = (tf3 tv10)

repr :: NnfFormula -> Formula
repr tv9 = (tf2 tv9)

main :: NnfFormula -> Bool
main tv18 = (spec (repr tv18))

not :: Bool -> Bool
not True = False
not False = True

tf5 :: NnfFormula -> Bool
tf5 (Nflit tv22) = tv22
tf5 (Nfneglit tv23) = (not tv23)
tf5 (Nfand tv24 tv25) = (and (tf4 tv25) (tf4 tv24))
tf5 (Nfor tv26 tv27) = (or (tf4 tv26) (tf4 tv27))

tf4 :: NnfFormula -> Bool
tf4 tv20 = (tf5 tv20)

reprNew :: NnfFormula -> Bool
reprNew tv19 = (tf4 tv19)

mainNew :: NnfFormula -> Bool
mainNew tv28 = (reprNew tv28)

optimize inp0 = (main inp0)=:=(mainNew inp0)
