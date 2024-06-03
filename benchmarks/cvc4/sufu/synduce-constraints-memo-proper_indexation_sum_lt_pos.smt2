  (declare-datatypes () ((MyBool (MyTrue) (MyFalse))))
  (declare-datatypes () ((Unit (Null))))
  (declare-datatypes () ((Nat (Zero) (Succ (proj_Succ_0 Nat)))))
  (declare-datatypes () ((List (Nil (proj_Nil_0 Unit)) (Cons (proj_Cons_0 Nat) (proj_Cons_1 List)))))
  (declare-datatypes () ((IDList (Inil (proj_Inil_0 Unit)) (Icons (proj_Icons_0 Nat) (proj_Icons_1 Nat) (proj_Icons_2 IDList)))))
  (declare-fun plus (Nat Nat) Nat)
  (declare-fun tf1 (IDList) Nat)
  (declare-fun tf0 (IDList) Nat)
  (declare-fun length (IDList) Nat)
  (declare-fun myand (MyBool MyBool) MyBool)
  (declare-fun nateq (Nat Nat) MyBool)
  (declare-fun tf3 (IDList) MyBool)
  (declare-fun tf2 (IDList) MyBool)
  (declare-fun isindexed (IDList) MyBool)
  (declare-fun tf5 (IDList) List)
  (declare-fun tf4 (IDList) List)
  (declare-fun repr (IDList) List)
  (declare-fun tf7 (List) Nat)
  (declare-fun tf6 (List) Nat)
  (declare-fun len (List) Nat)
  (declare-fun gq (Nat Nat) MyBool)
  (declare-fun ite2 (MyBool Nat Nat) Nat)
  (declare-fun tf9 (List) Nat)
  (declare-fun tf8 (List) Nat)
  (declare-fun spec (List) Nat)
  (declare-fun tf11 (IDList IDList) IDList)
  (declare-fun tf10 (IDList) IDList)
  (declare-fun target (IDList) IDList)
  (declare-fun main (IDList) Nat)
  (declare-datatypes () ((Tuple3 (MakeTuple3 (proj_MakeTuple3_0 Nat) (proj_MakeTuple3_1 Nat)))))
  (declare-fun leq (Nat Nat) MyBool)
  (declare-fun snd3 (Tuple3) Nat)
  (declare-fun fst3 (Tuple3) Nat)
  (declare-fun tf13 (IDList) Tuple3)
  (declare-fun tf12 (IDList) Tuple3)
  (declare-fun targetNew (IDList) Tuple3)
  (declare-fun mainNew (IDList) Nat)
  (assert (forall ((x Nat)) (= (plus Zero x) x)))
  (assert (forall ((y Nat) (x Nat)) (= (plus (Succ x) y) (Succ (plus x y)))))
  (assert (forall ((tv3 Unit)) (= (tf1 (Inil tv3)) Zero)))
  (assert (forall ((tv6 IDList) (tv5 Nat) (tv4 Nat)) (= (tf1 (Icons tv4 tv5 tv6)) (plus (Succ Zero) (tf0 tv6)))))
  (assert (forall ((tv1 IDList)) (= (tf0 tv1) (tf1 tv1))))
  (assert (forall ((tv0 IDList)) (= (length tv0) (tf0 tv0))))
  (assert (forall ((x MyBool)) (= (myand MyFalse x) MyFalse)))
  (assert (forall ((true MyBool)) (= (myand true MyFalse) MyFalse)))
  (assert (= (myand MyTrue MyTrue) MyTrue))
  (assert (= (nateq Zero Zero) MyTrue))
  (assert (forall ((x Nat)) (= (nateq Zero (Succ x)) MyFalse)))
  (assert (forall ((x Nat)) (= (nateq (Succ x) Zero) MyFalse)))
  (assert (forall ((y Nat) (x Nat)) (= (nateq (Succ x) (Succ y)) (nateq x y))))
  (assert (forall ((tv10 Unit)) (= (tf3 (Inil tv10)) MyTrue)))
  (assert (forall ((tv13 IDList) (tv12 Nat) (tv11 Nat)) (= (tf3 (Icons tv11 tv12 tv13)) (myand (tf2 tv13) (nateq tv12 (length tv13))))))
  (assert (forall ((tv8 IDList)) (= (tf2 tv8) (tf3 tv8))))
  (assert (forall ((tv7 IDList)) (= (isindexed tv7) (tf2 tv7))))
  (assert (forall ((tv17 Unit)) (= (tf5 (Inil tv17)) (Nil Null))))
  (assert (forall ((tv20 IDList) (tv19 Nat) (tv18 Nat)) (= (tf5 (Icons tv18 tv19 tv20)) (Cons tv18 (tf4 tv20)))))
  (assert (forall ((tv15 IDList)) (= (tf4 tv15) (tf5 tv15))))
  (assert (forall ((tv14 IDList)) (= (repr tv14) (tf4 tv14))))
  (assert (forall ((tv24 Unit)) (= (tf7 (Nil tv24)) Zero)))
  (assert (forall ((tv26 List) (tv25 Nat)) (= (tf7 (Cons tv25 tv26)) (plus (Succ Zero) (tf6 tv26)))))
  (assert (forall ((tv22 List)) (= (tf6 tv22) (tf7 tv22))))
  (assert (forall ((tv21 List)) (= (len tv21) (tf6 tv21))))
  (assert (forall ((x Nat)) (= (gq Zero x) MyFalse)))
  (assert (forall ((x Nat)) (= (gq (Succ x) Zero) MyTrue)))
  (assert (forall ((y Nat) (x Nat)) (= (gq (Succ x) (Succ y)) (gq x y))))
  (assert (forall ((y Nat) (x Nat)) (= (ite2 MyTrue x y) x)))
  (assert (forall ((y Nat) (x Nat)) (= (ite2 MyFalse x y) y)))
  (assert (forall ((tv30 Unit)) (= (tf9 (Nil tv30)) Zero)))
  (assert (forall ((tv32 List) (tv31 Nat)) (= (tf9 (Cons tv31 tv32)) (ite2 (gq tv31 (len tv32)) (plus tv31 (tf8 tv32)) (tf8 tv32)))))
  (assert (forall ((tv28 List)) (= (tf8 tv28) (tf9 tv28))))
  (assert (forall ((tv27 List)) (= (spec tv27) (tf8 tv27))))
  (assert (forall ((tv37 Unit) (tv36 IDList)) (= (tf11 tv36 (Inil tv37)) tv36)))
  (assert (forall ((tv40 IDList) (tv39 Nat) (tv38 Nat) (tv36 IDList)) (= (tf11 tv36 (Icons tv38 tv39 tv40)) (Icons tv38 tv39 (tf10 tv40)))))
  (assert (forall ((tv34 IDList)) (= (tf10 tv34) (tf11 tv34 tv34))))
  (assert (forall ((tv33 IDList)) (= (target tv33) (tf10 tv33))))
  (assert (forall ((tv41 IDList)) (= (main tv41) (ite2 (isindexed tv41) (spec (repr (target tv41))) Zero))))
  (assert (forall ((x Nat)) (= (leq Zero x) MyTrue)))
  (assert (forall ((x Nat)) (= (leq (Succ x) Zero) MyFalse)))
  (assert (forall ((y Nat) (x Nat)) (= (leq (Succ x) (Succ y)) (leq x y))))
  (assert (forall ((x1 Nat) (x0 Nat)) (= (snd3 (MakeTuple3 x0 x1)) x1)))
  (assert (forall ((x1 Nat) (x0 Nat)) (= (fst3 (MakeTuple3 x0 x1)) x0)))
  (assert (forall ((tv45 Unit)) (= (tf13 (Inil tv45)) (MakeTuple3 Zero Zero))))
  (assert (forall ((tv48 IDList) (tv47 Nat) (tv46 Nat)) (= (tf13 (Icons tv46 tv47 tv48)) (MakeTuple3 (ite2 (leq tv46 (snd3 (tf12 tv48))) (fst3 (tf12 tv48)) (plus tv46 (fst3 (tf12 tv48)))) (plus (snd3 (tf12 tv48)) (Succ Zero))))))
  (assert (forall ((tv43 IDList)) (= (tf12 tv43) (tf13 tv43))))
  (assert (forall ((tv42 IDList)) (= (targetNew tv42) (tf12 tv42))))
  (assert (forall ((tv49 IDList)) (= (mainNew tv49) (ite2 (isindexed tv49) (fst3 (targetNew tv49)) Zero))))
  (assert (not (forall ((inp0 IDList)) (= (main inp0) (mainNew inp0)))))
  (check-sat)
