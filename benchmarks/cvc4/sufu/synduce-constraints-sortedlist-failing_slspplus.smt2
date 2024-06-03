  (declare-datatypes () ((MyBool (MyTrue) (MyFalse))))
  (declare-datatypes () ((Nat (Zero) (Succ (proj_Succ_0 Nat)))))
  (declare-datatypes () ((List (Elt (proj_Elt_0 Nat)) (Cons (proj_Cons_0 Nat) (proj_Cons_1 List)))))
  (declare-datatypes () ((NList (Line (proj_Line_0 List)) (Ncons (proj_Ncons_0 List) (proj_Ncons_1 NList)))))
  (declare-datatypes () ((CList (Sglt (proj_Sglt_0 List)) (Cat (proj_Cat_0 CList) (proj_Cat_1 Nat) (proj_Cat_2 CList)))))
  (declare-fun tf1 (NList CList) NList)
  (declare-fun tf0 (NList CList) NList)
  (declare-fun tf3 (CList) NList)
  (declare-fun tf2 (CList) NList)
  (declare-fun c2n (CList) NList)
  (declare-fun plus (Nat Nat) Nat)
  (declare-fun tf5 (List) Nat)
  (declare-fun tf4 (List) Nat)
  (declare-fun lsum (List) Nat)
  (declare-fun lq (Nat Nat) MyBool)
  (declare-fun ite3 (MyBool Nat Nat) Nat)
  (declare-fun min (Nat Nat) Nat)
  (declare-fun max (Nat Nat) Nat)
  (declare-fun tf7 (CList) Nat)
  (declare-fun tf6 (CList) Nat)
  (declare-fun tf9 (CList) Nat)
  (declare-fun tf8 (CList) Nat)
  (declare-fun myand (MyBool MyBool) MyBool)
  (declare-fun tf11 (CList) MyBool)
  (declare-fun tf10 (CList) MyBool)
  (declare-fun sorted (CList) MyBool)
  (declare-datatypes () ((Tuple4 (MakeTuple4 (proj_MakeTuple4_0 Nat) (proj_MakeTuple4_1 MyBool)))))
  (declare-fun geq (Nat Nat) MyBool)
  (declare-fun snd4 (Tuple4) MyBool)
  (declare-fun fst4 (Tuple4) Nat)
  (declare-fun tf13 (NList) Tuple4)
  (declare-fun tf12 (NList) Tuple4)
  (declare-fun spec (NList) Nat)
  (declare-fun tf15 (List List) List)
  (declare-fun tf14 (List) List)
  (declare-fun leq (Nat Nat) MyBool)
  (declare-fun ite5 (MyBool CList CList) CList)
  (declare-fun tf17 (CList) CList)
  (declare-fun tf16 (CList) CList)
  (declare-fun target (CList) CList)
  (declare-fun main (CList) Nat)
  (declare-fun tf19 (List) Nat)
  (declare-fun tf18 (List) Nat)
  (declare-fun tf21 (CList) Nat)
  (declare-fun tf20 (CList) Nat)
  (declare-fun targetNew (CList) Nat)
  (declare-fun mainNew (CList) Nat)
  (assert (forall ((tv5 List) (tv4 NList)) (= (tf1 tv4 (Sglt tv5)) (Ncons tv5 tv4))))
  (assert (forall ((tv8 CList) (tv7 Nat) (tv6 CList) (tv4 NList)) (= (tf1 tv4 (Cat tv6 tv7 tv8)) (tf0 (tf0 tv4 tv8) tv6))))
  (assert (forall ((tv2 CList) (tv1 NList)) (= (tf0 tv1 tv2) (tf1 tv1 tv2))))
  (assert (forall ((tv11 List)) (= (tf3 (Sglt tv11)) (Line tv11))))
  (assert (forall ((tv13 Nat) (tv14 CList) (tv12 CList)) (= (tf3 (Cat tv12 tv13 tv14)) (tf0 (tf2 tv14) tv12))))
  (assert (forall ((tv9 CList)) (= (tf2 tv9) (tf3 tv9))))
  (assert (forall ((tv0 CList)) (= (c2n tv0) (tf2 tv0))))
  (assert (forall ((x Nat)) (= (plus Zero x) x)))
  (assert (forall ((y Nat) (x Nat)) (= (plus (Succ x) y) (Succ (plus x y)))))
  (assert (forall ((tv18 Nat)) (= (tf5 (Elt tv18)) tv18)))
  (assert (forall ((tv20 List) (tv19 Nat)) (= (tf5 (Cons tv19 tv20)) (plus tv19 (tf4 tv20)))))
  (assert (forall ((tv16 List)) (= (tf4 tv16) (tf5 tv16))))
  (assert (forall ((tv15 List)) (= (lsum tv15) (tf4 tv15))))
  (assert (= (lq Zero Zero) MyFalse))
  (assert (forall ((x Nat)) (= (lq Zero (Succ x)) MyTrue)))
  (assert (forall ((x Nat)) (= (lq (Succ x) Zero) MyFalse)))
  (assert (forall ((y Nat) (x Nat)) (= (lq (Succ x) (Succ y)) (lq x y))))
  (assert (forall ((y Nat) (x Nat)) (= (ite3 MyTrue x y) x)))
  (assert (forall ((y Nat) (x Nat)) (= (ite3 MyFalse x y) y)))
  (assert (forall ((tv22 Nat) (tv21 Nat)) (= (min tv21 tv22) (ite3 (lq tv21 tv22) tv21 tv22))))
  (assert (forall ((tv24 Nat) (tv23 Nat)) (= (max tv23 tv24) (ite3 (lq tv23 tv24) tv24 tv23))))
  (assert (forall ((tv28 List)) (= (tf7 (Sglt tv28)) (lsum tv28))))
  (assert (forall ((tv31 CList) (tv30 Nat) (tv29 CList)) (= (tf7 (Cat tv29 tv30 tv31)) (min (tf6 tv29) (tf6 tv31)))))
  (assert (forall ((tv26 CList)) (= (tf6 tv26) (tf7 tv26))))
  (assert (forall ((tv34 List)) (= (tf9 (Sglt tv34)) (lsum tv34))))
  (assert (forall ((tv37 CList) (tv36 Nat) (tv35 CList)) (= (tf9 (Cat tv35 tv36 tv37)) (max (tf8 tv35) (tf8 tv37)))))
  (assert (forall ((tv32 CList)) (= (tf8 tv32) (tf9 tv32))))
  (assert (forall ((x MyBool)) (= (myand MyFalse x) MyFalse)))
  (assert (forall ((true MyBool)) (= (myand true MyFalse) MyFalse)))
  (assert (= (myand MyTrue MyTrue) MyTrue))
  (assert (forall ((tv40 List)) (= (tf11 (Sglt tv40)) MyTrue)))
  (assert (forall ((tv43 CList) (tv42 Nat) (tv41 CList)) (= (tf11 (Cat tv41 tv42 tv43)) (myand (myand (lq (tf8 tv41) tv42) (lq tv42 (tf6 tv43))) (myand (tf10 tv41) (tf10 tv43))))))
  (assert (forall ((tv38 CList)) (= (tf10 tv38) (tf11 tv38))))
  (assert (forall ((tv25 CList)) (= (sorted tv25) (tf10 tv25))))
  (assert (= (geq Zero Zero) MyTrue))
  (assert (forall ((x Nat)) (= (geq Zero (Succ x)) MyFalse)))
  (assert (forall ((x Nat)) (= (geq (Succ x) Zero) MyTrue)))
  (assert (forall ((y Nat) (x Nat)) (= (geq (Succ x) (Succ y)) (geq x y))))
  (assert (forall ((x1 MyBool) (x0 Nat)) (= (snd4 (MakeTuple4 x0 x1)) x1)))
  (assert (forall ((x1 MyBool) (x0 Nat)) (= (fst4 (MakeTuple4 x0 x1)) x0)))
  (assert (forall ((tv47 List)) (= (tf13 (Line tv47)) (MakeTuple4 (max Zero (lsum tv47)) (geq (lsum tv47) Zero)))))
  (assert (forall ((tv49 NList) (tv48 List)) (= (tf13 (Ncons tv48 tv49)) (MakeTuple4 (ite3 (myand (snd4 (tf12 tv49)) (geq (lsum tv48) Zero)) (plus (fst4 (tf12 tv49)) (lsum tv48)) (fst4 (tf12 tv49))) (myand (snd4 (tf12 tv49)) (geq (lsum tv48) Zero))))))
  (assert (forall ((tv45 NList)) (= (tf12 tv45) (tf13 tv45))))
  (assert (forall ((tv44 NList)) (= (spec tv44) (fst4 (tf12 tv44)))))
  (assert (forall ((tv54 Nat) (tv53 List)) (= (tf15 tv53 (Elt tv54)) tv53)))
  (assert (forall ((tv56 List) (tv55 Nat) (tv53 List)) (= (tf15 tv53 (Cons tv55 tv56)) (Cons tv55 (tf14 tv56)))))
  (assert (forall ((tv51 List)) (= (tf14 tv51) (tf15 tv51 tv51))))
  (assert (forall ((x Nat)) (= (leq Zero x) MyTrue)))
  (assert (forall ((x Nat)) (= (leq (Succ x) Zero) MyFalse)))
  (assert (forall ((y Nat) (x Nat)) (= (leq (Succ x) (Succ y)) (leq x y))))
  (assert (forall ((y CList) (x CList)) (= (ite5 MyTrue x y) x)))
  (assert (forall ((y CList) (x CList)) (= (ite5 MyFalse x y) y)))
  (assert (forall ((tv59 List)) (= (tf17 (Sglt tv59)) (Sglt (tf14 tv59)))))
  (assert (forall ((tv62 CList) (tv61 Nat) (tv60 CList)) (= (tf17 (Cat tv60 tv61 tv62)) (ite5 (leq tv61 Zero) (Cat tv60 tv61 (tf16 tv62)) (Cat (tf16 tv60) tv61 (tf16 tv62))))))
  (assert (forall ((tv57 CList)) (= (tf16 tv57) (tf17 tv57))))
  (assert (forall ((tv50 CList)) (= (target tv50) (tf16 tv50))))
  (assert (forall ((tv63 CList)) (= (main tv63) (ite3 (sorted tv63) (spec (c2n (target tv63))) Zero))))
  (assert (forall ((tv67 Nat)) (= (tf19 (Elt tv67)) tv67)))
  (assert (forall ((tv69 List) (tv68 Nat)) (= (tf19 (Cons tv68 tv69)) (plus (tf18 tv69) tv68))))
  (assert (forall ((tv65 List)) (= (tf18 tv65) (tf19 tv65))))
  (assert (forall ((tv72 List)) (= (tf21 (Sglt tv72)) (max (tf18 tv72) Zero))))
  (assert (forall ((tv75 CList) (tv74 Nat) (tv73 CList)) (= (tf21 (Cat tv73 tv74 tv75)) (ite3 (leq tv74 Zero) (tf20 tv75) (plus (tf20 tv75) (tf20 tv73))))))
  (assert (forall ((tv70 CList)) (= (tf20 tv70) (tf21 tv70))))
  (assert (forall ((tv64 CList)) (= (targetNew tv64) (tf20 tv64))))
  (assert (forall ((tv76 CList)) (= (mainNew tv76) (ite3 (sorted tv76) (targetNew tv76) Zero))))
  (assert (not (forall ((inp0 CList)) (= (main inp0) (mainNew inp0)))))
  (check-sat)