{-

    All properties from the article.

-}
module Properties where

import HipSpec
import Prelude(Bool(..))
import Definitions

-- Theorems

prop_1 :: Nat -> Prop Nat
prop_1 x = double x =:= x + x

prop_2 :: [a] -> [a] -> Prop Nat
prop_2 x y = length (x ++ y ) =:= length (y ++ x)

prop_3 :: [a] -> [a] -> Prop Nat
prop_3 x y = length (x ++ y ) =:= length (y ) + length x

prop_4 :: [a] -> Prop Nat
prop_4 x = length (x ++ x) =:= double (length x)

prop_5 :: [a] -> Prop Nat
prop_5 x = length (rev x) =:= length x

prop_6 :: [a] -> [a] -> Prop Nat
prop_6 x y = length (rev (x ++ y )) =:= length x + length y

prop_7 :: [a] -> [a] -> Prop Nat
prop_7 x y = length (qrev x y) =:= length x + length y

prop_8 :: Nat -> Nat -> [a] -> Prop [a]
prop_8 x y z = drop x (drop y z) =:= drop y (drop x z)

prop_9 :: Nat -> Nat -> [a] -> Nat -> Prop [a]
prop_9 x y z w = drop w (drop x (drop y z)) =:= drop y (drop x (drop w z))

prop_10 :: [a] -> Prop [a]
prop_10 x = rev (rev x) =:= x

prop_11 :: [a] -> [a] -> Prop [a]
prop_11 x y = rev (rev x ++ rev y) =:= y ++ x

prop_12 :: [a] -> [a] -> Prop [a]
prop_12 x y = qrev x y =:= rev x ++ y

prop_13 :: Nat -> Prop Nat
prop_13 x = half (x + x) =:= x

prop_14 :: [Nat] -> Prop Bool
prop_14 x = proveBool (sorted (isort x))

prop_15 :: Nat -> Prop Nat
prop_15 x = x + S x =:= S (x + x)

prop_16 :: Nat -> Prop Bool
prop_16 x = proveBool (even (x + x))

prop_17 :: [a] -> [a] -> Prop [a]
prop_17 x y = rev (rev (x ++ y)) =:= rev (rev x) ++ rev (rev y)

prop_18 :: [a] -> [a] -> Prop [a]
prop_18 x y = rev (rev x ++ y) =:= rev y ++ x

prop_19 :: [a] -> [a] -> Prop [a]
prop_19 x y = rev (rev x) ++ y =:= rev (rev (x ++ y))

prop_20 :: [a] -> Prop Bool
prop_20 x = proveBool (even (length (x ++ x)))

prop_21 :: [a] -> [a] -> Prop [a]
prop_21 x y = rotate (length x) (x ++ y) =:= y ++ x

prop_22 :: [a] -> [a] -> Prop Bool
prop_22 x y = even (length (x ++ y)) =:= even (length (y ++ x))

prop_23 :: [a] -> [a] -> Prop Nat
prop_23 x y = half (length (x ++ y)) =:= half (length (y ++ x))

prop_24 :: Nat -> Nat -> Prop Bool
prop_24 x y = even (x + y) =:= even (y + x)

prop_25 :: [a] -> [a] -> Prop Bool
prop_25 x y = even (length (x ++ y)) =:= even (length y + length x)

prop_26 :: Nat -> Nat -> Prop Nat
prop_26 x y = half (x + y) =:= half (y + x)

prop_27 :: [a] -> Prop [a]
prop_27 x = rev x =:= qrev x []

prop_28 :: [[a]] -> Prop [a]
prop_28 x = revflat x =:= qrevflat x []

prop_29 :: [a] -> Prop [a]
prop_29 x = rev (qrev x []) =:= x

prop_30 :: [a] -> Prop [a]
prop_30 x = rev (rev x ++ []) =:= x

prop_31 :: [a] -> Prop [a]
prop_31 x = qrev (qrev x []) [] =:= x

prop_32 :: [a] -> Prop [a]
prop_32 x = rotate (length x) x =:= x

prop_33 :: Nat -> Prop Nat
prop_33 x = fac x =:= qfac x one

prop_34 :: Nat -> Nat -> Prop Nat
prop_34 x y = x * y =:= mult x y zero

prop_35 :: Nat -> Nat -> Prop Nat
prop_35 x y = exp x y =:= qexp x y one

prop_36 :: Nat -> [Nat] -> [Nat] -> Prop Bool
prop_36 x y z = givenBool (x `elem` y) (proveBool (x `elem` (y ++ z)))

prop_37 :: Nat -> [Nat] -> [Nat] -> Prop Bool
prop_37 x y z = givenBool (x `elem` z) (proveBool (x `elem` (y ++ z)))

prop_38 :: Nat -> [Nat] -> [Nat] -> Prop Bool
prop_38 x y z = givenBool (x `elem` y)
               ( givenBool (x `elem` z)
               ( proveBool (x `elem` (y ++ z))))

prop_39 :: Nat -> Nat -> [Nat] -> Prop Bool
prop_39 x y z = givenBool (x `elem` drop y z) (proveBool (x `elem` z))

prop_40 :: [Nat] -> [Nat] -> Prop [Nat]
prop_40 x y = givenBool (x `subset` y) ((x `union` y) =:= y)

prop_41 :: [Nat] -> [Nat] -> Prop [Nat]
prop_41 x y = givenBool (x `subset` y) ((x `intersect` y) =:= x)

prop_42 :: Nat -> [Nat] -> [Nat] -> Prop Bool
prop_42 x y z = givenBool (x `elem` y) (proveBool (x `elem` (y `union` z)))

prop_43 :: Nat -> [Nat] -> [Nat] -> Prop Bool
prop_43 x y z = givenBool (x `elem` y) (proveBool (x `elem` (z `union` y)))

prop_44 :: Nat -> [Nat] -> [Nat] -> Prop Bool
prop_44 x y z = givenBool (x `elem` y)
               ( givenBool (x `elem` z)
               ( proveBool (x `elem` (y `intersect` z))))

prop_45 :: Nat -> [Nat] -> Prop Bool
prop_45 x y = proveBool (x `elem` insert x y)

prop_46 :: Nat -> Nat -> [Nat] -> Prop Bool
prop_46 x y z = x =:= y ==> proveBool (x `elem` insert y z)

prop_47 :: Nat -> Nat -> [Nat] -> Prop Bool
prop_47 x y z = givenBool (x /= y) ((x `elem` insert y z) =:= x `elem` z)

prop_48 :: [Nat] -> Prop Nat
prop_48 x = length (isort x) =:= length x

prop_49 :: Nat -> [Nat] -> Prop Bool
prop_49 x y = givenBool (x `elem` isort y) (proveBool (x `elem` y))

prop_50 :: Nat -> [Nat] -> Prop Nat
prop_50 x y = count x (isort y) =:= count x y

prop_75 :: [a] -> [a] -> Prop [a]
prop_75 x y = rev x ++ y =:= qrev x y

prop_76 :: [[a]] -> [a] -> Prop [a]
prop_76 x y = revflat x ++ y =:= qrevflat x y

prop_77 :: [a] -> [a] -> Prop [a]
prop_77 x y = rev (qrev x y) =:= (rev y) ++ x

prop_78 :: [a] -> [a] -> Prop [a]
prop_78 x y = rev (qrev x (rev y)) =:= y ++ x

prop_79 :: [a] -> [a] -> Prop [a]
prop_79 x y = rev (rev x ++ y) =:= rev y ++ x

prop_80 :: [a] -> [a] -> Prop [a]
prop_80 x y = rev (rev x ++ rev y) =:= y ++ x

prop_81 :: [a] -> [a] -> Prop [a]
prop_81 x y = qrev (qrev x y) [] =:= rev y ++ x

prop_82 :: [a] -> [a] -> Prop [a]
prop_82 x y = qrev (qrev x (rev y)) [] =:= y ++ x

prop_83 :: [a] -> [a] -> Prop [a]
prop_83 x y = rotate (length x) (x ++ y) =:= y ++ x

prop_84 :: Nat -> Nat -> Prop Nat
prop_84 x y = fac x * y =:= qfac x y

prop_85 :: Nat -> Nat -> Nat -> Prop Nat
prop_85 x y z = (x * y) + z =:= mult x y z

prop_86 :: Nat -> Nat -> Nat -> Prop Nat
prop_86 x y z = (exp x y) * z =:= qexp x y z

prop_assoc_mult :: Nat -> Nat -> Nat -> Prop Nat
prop_assoc_mult x y z = (x * y) * z =:= x * (y * z)
