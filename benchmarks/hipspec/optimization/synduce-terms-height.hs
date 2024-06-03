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


data ArithOp = APlus Unit | AMinus Unit | AGt Unit deriving (Eq, Typeable, Ord)

instance Names ArithOp where
  names _ = ["var0_0", "var0_1", "var0_2"]

instance Arbitrary ArithOp where
  arbitrary = sized arb
    where
      arb 0 = frequency
        [
          (1, do
            x0 <- arbitrary
            return (APlus x0)
          ),
          (1, do
            x0 <- arbitrary
            return (AMinus x0)
          ),
          (1, do
            x0 <- arbitrary
            return (AGt x0)
          )
        ]
      arb n = frequency
        [
          (1, do
            x0 <- arbitrary
            return (APlus x0)
          ),
          (1, do
            x0 <- arbitrary
            return (AMinus x0)
          ),
          (1, do
            x0 <- arbitrary
            return (AGt x0)
          )
        ]

instance Partial ArithOp where
  unlifted (APlus x0) = do
    x0' <- lifted x0
    return (APlus x0')
  unlifted (AMinus x0) = do
    x0' <- lifted x0
    return (AMinus x0')
  unlifted (AGt x0) = do
    x0' <- lifted x0
    return (AGt x0')


data BoolOp = BNot Unit | BAnd Unit | BOr Unit | BEq Unit deriving (Eq, Typeable, Ord)

instance Names BoolOp where
  names _ = ["var0_0", "var0_1", "var0_2"]

instance Arbitrary BoolOp where
  arbitrary = sized arb
    where
      arb 0 = frequency
        [
          (1, do
            x0 <- arbitrary
            return (BNot x0)
          ),
          (1, do
            x0 <- arbitrary
            return (BAnd x0)
          ),
          (1, do
            x0 <- arbitrary
            return (BOr x0)
          ),
          (1, do
            x0 <- arbitrary
            return (BEq x0)
          )
        ]
      arb n = frequency
        [
          (1, do
            x0 <- arbitrary
            return (BNot x0)
          ),
          (1, do
            x0 <- arbitrary
            return (BAnd x0)
          ),
          (1, do
            x0 <- arbitrary
            return (BOr x0)
          ),
          (1, do
            x0 <- arbitrary
            return (BEq x0)
          )
        ]

instance Partial BoolOp where
  unlifted (BNot x0) = do
    x0' <- lifted x0
    return (BNot x0')
  unlifted (BAnd x0) = do
    x0' <- lifted x0
    return (BAnd x0')
  unlifted (BOr x0) = do
    x0' <- lifted x0
    return (BOr x0')
  unlifted (BEq x0) = do
    x0' <- lifted x0
    return (BEq x0')


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


data Term = TArithBin ArithOp Term Term | TBoolBin BoolOp Term Term | TArithUn ArithOp Term | TBoolUn BoolOp Term | TVar Nat | TCInt Nat | TCBool Bool deriving (Eq, Typeable, Ord)

instance Names Term where
  names _ = ["var0_0", "var0_1", "var0_2"]

instance Arbitrary Term where
  arbitrary = sized arb
    where
      arb 0 = frequency
        [
          (1, do
            x0 <- arbitrary
            return (TVar x0)
          ),
          (1, do
            x0 <- arbitrary
            return (TCInt x0)
          ),
          (1, do
            x0 <- arbitrary
            return (TCBool x0)
          )
        ]
      arb n = frequency
        [
          (n, do
            let n' = n `div` 2
            x0 <- arbitrary
            x1 <- arb n'
            x2 <- arb n'
            return (TArithBin x0 x1 x2)
          ),
          (n, do
            let n' = n `div` 2
            x0 <- arbitrary
            x1 <- arb n'
            x2 <- arb n'
            return (TBoolBin x0 x1 x2)
          ),
          (n, do
            let n' = n - 1
            x0 <- arbitrary
            x1 <- arb n'
            return (TArithUn x0 x1)
          ),
          (n, do
            let n' = n - 1
            x0 <- arbitrary
            x1 <- arb n'
            return (TBoolUn x0 x1)
          ),
          (1, do
            x0 <- arbitrary
            return (TVar x0)
          ),
          (1, do
            x0 <- arbitrary
            return (TCInt x0)
          ),
          (1, do
            x0 <- arbitrary
            return (TCBool x0)
          )
        ]

instance Partial Term where
  unlifted (TArithBin x0 x1 x2) = do
    x0' <- lifted x0
    x1' <- lifted x1
    x2' <- lifted x2
    return (TArithBin x0' x1' x2')
  unlifted (TBoolBin x0 x1 x2) = do
    x0' <- lifted x0
    x1' <- lifted x1
    x2' <- lifted x2
    return (TBoolBin x0' x1' x2')
  unlifted (TArithUn x0 x1) = do
    x0' <- lifted x0
    x1' <- lifted x1
    return (TArithUn x0' x1')
  unlifted (TBoolUn x0 x1) = do
    x0' <- lifted x0
    x1' <- lifted x1
    return (TBoolUn x0' x1')
  unlifted (TVar x0) = do
    x0' <- lifted x0
    return (TVar x0')
  unlifted (TCInt x0) = do
    x0' <- lifted x0
    return (TCInt x0')
  unlifted (TCBool x0) = do
    x0' <- lifted x0
    return (TCBool x0')


data Op = OpPlus Unit | OpMinus Unit | OpNot Unit | OpAnd Unit | OpOr Unit | OpGt Unit | OpEq Unit deriving (Eq, Typeable, Ord)

instance Names Op where
  names _ = ["var0_0", "var0_1", "var0_2"]

instance Arbitrary Op where
  arbitrary = sized arb
    where
      arb 0 = frequency
        [
          (1, do
            x0 <- arbitrary
            return (OpPlus x0)
          ),
          (1, do
            x0 <- arbitrary
            return (OpMinus x0)
          ),
          (1, do
            x0 <- arbitrary
            return (OpNot x0)
          ),
          (1, do
            x0 <- arbitrary
            return (OpAnd x0)
          ),
          (1, do
            x0 <- arbitrary
            return (OpOr x0)
          ),
          (1, do
            x0 <- arbitrary
            return (OpGt x0)
          ),
          (1, do
            x0 <- arbitrary
            return (OpEq x0)
          )
        ]
      arb n = frequency
        [
          (1, do
            x0 <- arbitrary
            return (OpPlus x0)
          ),
          (1, do
            x0 <- arbitrary
            return (OpMinus x0)
          ),
          (1, do
            x0 <- arbitrary
            return (OpNot x0)
          ),
          (1, do
            x0 <- arbitrary
            return (OpAnd x0)
          ),
          (1, do
            x0 <- arbitrary
            return (OpOr x0)
          ),
          (1, do
            x0 <- arbitrary
            return (OpGt x0)
          ),
          (1, do
            x0 <- arbitrary
            return (OpEq x0)
          )
        ]

instance Partial Op where
  unlifted (OpPlus x0) = do
    x0' <- lifted x0
    return (OpPlus x0')
  unlifted (OpMinus x0) = do
    x0' <- lifted x0
    return (OpMinus x0')
  unlifted (OpNot x0) = do
    x0' <- lifted x0
    return (OpNot x0')
  unlifted (OpAnd x0) = do
    x0' <- lifted x0
    return (OpAnd x0')
  unlifted (OpOr x0) = do
    x0' <- lifted x0
    return (OpOr x0')
  unlifted (OpGt x0) = do
    x0' <- lifted x0
    return (OpGt x0')
  unlifted (OpEq x0) = do
    x0' <- lifted x0
    return (OpEq x0')


data Term2 = Bin Op Term2 Term2 | Un Op Term2 | Var Nat | CInt Nat | CBool Bool deriving (Eq, Typeable, Ord)

instance Names Term2 where
  names _ = ["var0_0", "var0_1", "var0_2"]

instance Arbitrary Term2 where
  arbitrary = sized arb
    where
      arb 0 = frequency
        [
          (1, do
            x0 <- arbitrary
            return (Var x0)
          ),
          (1, do
            x0 <- arbitrary
            return (CInt x0)
          ),
          (1, do
            x0 <- arbitrary
            return (CBool x0)
          )
        ]
      arb n = frequency
        [
          (n, do
            let n' = n `div` 2
            x0 <- arbitrary
            x1 <- arb n'
            x2 <- arb n'
            return (Bin x0 x1 x2)
          ),
          (n, do
            let n' = n - 1
            x0 <- arbitrary
            x1 <- arb n'
            return (Un x0 x1)
          ),
          (1, do
            x0 <- arbitrary
            return (Var x0)
          ),
          (1, do
            x0 <- arbitrary
            return (CInt x0)
          ),
          (1, do
            x0 <- arbitrary
            return (CBool x0)
          )
        ]

instance Partial Term2 where
  unlifted (Bin x0 x1 x2) = do
    x0' <- lifted x0
    x1' <- lifted x1
    x2' <- lifted x2
    return (Bin x0' x1' x2')
  unlifted (Un x0 x1) = do
    x0' <- lifted x0
    x1' <- lifted x1
    return (Un x0' x1')
  unlifted (Var x0) = do
    x0' <- lifted x0
    return (Var x0')
  unlifted (CInt x0) = do
    x0' <- lifted x0
    return (CInt x0')
  unlifted (CBool x0) = do
    x0' <- lifted x0
    return (CBool x0')


tf0 :: Term -> Term -> Op -> Term
tf0 tv3 tv4 (OpPlus tv5) = (TArithBin (APlus Null) tv4 tv3)
tf0 tv3 tv4 (OpMinus tv6) = (TArithBin (AMinus Null) tv4 tv3)
tf0 tv3 tv4 (OpNot tv7) = (TBoolBin (BNot Null) tv4 tv3)
tf0 tv3 tv4 (OpAnd tv8) = (TBoolBin (BAnd Null) tv4 tv3)
tf0 tv3 tv4 (OpOr tv9) = (TBoolBin (BOr Null) tv4 tv3)
tf0 tv3 tv4 (OpGt tv10) = (TArithBin (AGt Null) tv4 tv3)
tf0 tv3 tv4 (OpEq tv11) = (TBoolBin (BEq Null) tv4 tv3)

mkbin :: Term -> Term -> Op -> Term
mkbin tv0 tv1 tv2 = (tf0 tv1 tv0 tv2)

tf1 :: Term -> Op -> Term
tf1 tv14 (OpPlus tv15) = (TArithUn (APlus Null) tv14)
tf1 tv14 (OpMinus tv16) = (TArithUn (AMinus Null) tv14)
tf1 tv14 (OpNot tv17) = (TBoolUn (BNot Null) tv14)
tf1 tv14 (OpAnd tv18) = (TBoolUn (BAnd Null) tv14)
tf1 tv14 (OpOr tv19) = (TBoolUn (BOr Null) tv14)
tf1 tv14 (OpGt tv20) = (TArithUn (AGt Null) tv14)
tf1 tv14 (OpEq tv21) = (TBoolUn (BEq Null) tv14)

mkun :: Term -> Op -> Term
mkun tv12 tv13 = (tf1 tv12 tv13)

tf3 :: Term2 -> Term
tf3 (Bin tv25 tv26 tv27) = (mkbin (tf2 tv26) (tf2 tv27) tv25)
tf3 (Un tv28 tv29) = (mkun (tf2 tv29) tv28)
tf3 (Var tv30) = (TVar tv30)
tf3 (CInt tv31) = (TCInt tv31)
tf3 (CBool tv32) = (TCBool tv32)

tf2 :: Term2 -> Term
tf2 tv23 = (tf3 tv23)

repr :: Term2 -> Term
repr tv22 = (tf2 tv22)

lq :: Nat -> Nat -> Bool
lq Zero (Succ x) = True
lq x Zero = False
lq (Succ x) (Succ y) = (lq x y)

ite6 :: Bool -> Nat -> Nat -> Nat
ite6 True x y = x
ite6 False x y = y

max :: Nat -> Nat -> Nat
max tv33 tv34 = (ite6 (lq tv33 tv34) tv34 tv33)

plus :: Nat -> Nat -> Nat
plus Zero x = x
plus (Succ x) y = (Succ (plus x y))

tf5 :: Term -> Nat
tf5 (TArithBin tv38 tv39 tv40) = (plus (Succ Zero) (max (tf4 tv39) (tf4 tv40)))
tf5 (TBoolBin tv41 tv42 tv43) = (plus (Succ Zero) (max (tf4 tv42) (tf4 tv43)))
tf5 (TArithUn tv44 tv45) = (plus (Succ Zero) (tf4 tv45))
tf5 (TBoolUn tv46 tv47) = (plus (Succ Zero) (tf4 tv47))
tf5 (TVar tv48) = (Succ Zero)
tf5 (TCInt tv49) = (Succ Zero)
tf5 (TCBool tv50) = (Succ Zero)

tf4 :: Term -> Nat
tf4 tv36 = (tf5 tv36)

spec :: Term -> Nat
spec tv35 = (tf4 tv35)

tf7 :: Term2 -> Term2
tf7 (Bin tv54 tv55 tv56) = (Bin tv54 (tf6 tv55) (tf6 tv56))
tf7 (Un tv57 tv58) = (Un tv57 (tf6 tv58))
tf7 (Var tv59) = (Var tv59)
tf7 (CInt tv60) = (CInt tv60)
tf7 (CBool tv61) = (CBool tv61)

tf6 :: Term2 -> Term2
tf6 tv52 = (tf7 tv52)

target :: Term2 -> Term2
target tv51 = (tf6 tv51)

main :: Term2 -> Nat
main tv62 = (spec (repr (target tv62)))

tf9 :: Term2 -> Nat
tf9 (Bin tv66 tv67 tv68) = (plus (Succ Zero) (max (tf8 tv67) (tf8 tv68)))
tf9 (Un tv69 tv70) = (plus (Succ Zero) (tf8 tv70))
tf9 (Var tv71) = (Succ Zero)
tf9 (CInt tv72) = (Succ Zero)
tf9 (CBool tv73) = (Succ Zero)

tf8 :: Term2 -> Nat
tf8 tv64 = (tf9 tv64)

targetNew :: Term2 -> Nat
targetNew tv63 = (tf8 tv63)

mainNew :: Term2 -> Nat
mainNew tv74 = (targetNew tv74)

optimize inp0 = (main inp0)=:=(mainNew inp0)
