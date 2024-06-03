  (declare-datatypes () ((MyBool (MyTrue) (MyFalse))))
  (declare-datatypes () ((Unit (Null))))
  (declare-datatypes () ((Nat (Zero) (Succ (proj_Succ_0 Nat)))))
  (declare-datatypes () ((List (Nil (proj_Nil_0 Unit)) (Cons (proj_Cons_0 Nat) (proj_Cons_1 List)))))
  (declare-datatypes () ((NList (Single (proj_Single_0 List)) (Ncons (proj_Ncons_0 List) (proj_Ncons_1 NList)))))
  (declare-fun tf1 (NList) List)
  (declare-fun tf0 (NList) List)
  (declare-fun map (NList) List)
  (declare-fun plus (Nat Nat) Nat)
  (declare-fun tf3 (List) Nat)
  (declare-fun tf2 (List) Nat)
  (declare-fun sum (List) Nat)
  (declare-fun times (Nat Nat) Nat)
  (declare-fun tf5 (List) Nat)
  (declare-fun tf4 (List) Nat)
  (declare-fun product (List) Nat)
  (declare-fun tf7 (List List) NList)
  (declare-fun tf6 (List) NList)
  (declare-fun tails (List) NList)
  (declare-fun main (List) Nat)
  (declare-datatypes () ((Tuple2 (MakeTuple2 (proj_MakeTuple2_0 Nat) (proj_MakeTuple2_1 Nat)))))
  (declare-fun fst2 (Tuple2) Nat)
  (declare-fun snd2 (Tuple2) Nat)
  (declare-fun tf9 (List) Tuple2)
  (declare-fun tf8 (List) Tuple2)
  (declare-fun tailsNew (List) Tuple2)
  (declare-fun mainNew (List) Nat)
  (assert (forall ((tv6 List)) (= (tf1 (Single tv6)) (Cons (product tv6) (Nil Null)))))
  (assert (forall ((tv8 NList) (tv7 List)) (= (tf1 (Ncons tv7 tv8)) (Cons (product tv7) (tf0 tv8)))))
  (assert (forall ((tv3 NList)) (= (tf0 tv3) (tf1 tv3))))
  (assert (forall ((tv1 NList)) (= (map tv1) (tf0 tv1))))
  (assert (forall ((x Nat)) (= (plus Zero x) x)))
  (assert (forall ((y Nat) (x Nat)) (= (plus (Succ x) y) (Succ (plus x y)))))
  (assert (forall ((tv12 Unit)) (= (tf3 (Nil tv12)) Zero)))
  (assert (forall ((tv14 List) (tv13 Nat)) (= (tf3 (Cons tv13 tv14)) (plus tv13 (tf2 tv14)))))
  (assert (forall ((tv10 List)) (= (tf2 tv10) (tf3 tv10))))
  (assert (forall ((tv9 List)) (= (sum tv9) (tf2 tv9))))
  (assert (forall ((x Nat)) (= (times Zero x) Zero)))
  (assert (forall ((y Nat) (x Nat)) (= (times (Succ x) y) (plus (times x y) y))))
  (assert (forall ((tv18 Unit)) (= (tf5 (Nil tv18)) (Succ Zero))))
  (assert (forall ((tv20 List) (tv19 Nat)) (= (tf5 (Cons tv19 tv20)) (times tv19 (tf4 tv20)))))
  (assert (forall ((tv16 List)) (= (tf4 tv16) (tf5 tv16))))
  (assert (forall ((tv15 List)) (= (product tv15) (tf4 tv15))))
  (assert (forall ((tv25 Unit) (tv24 List)) (= (tf7 tv24 (Nil tv25)) (Single tv24))))
  (assert (forall ((tv27 List) (tv26 Nat) (tv24 List)) (= (tf7 tv24 (Cons tv26 tv27)) (Ncons tv24 (tf6 tv27)))))
  (assert (forall ((tv22 List)) (= (tf6 tv22) (tf7 tv22 tv22))))
  (assert (forall ((tv21 List)) (= (tails tv21) (tf6 tv21))))
  (assert (forall ((tv28 List)) (= (main tv28) (sum (map (tails tv28))))))
  (assert (forall ((x1 Nat) (x0 Nat)) (= (fst2 (MakeTuple2 x0 x1)) x0)))
  (assert (forall ((x1 Nat) (x0 Nat)) (= (snd2 (MakeTuple2 x0 x1)) x1)))
  (assert (forall ((tv32 Unit)) (= (tf9 (Nil tv32)) (MakeTuple2 (Succ Zero) (Succ Zero)))))
  (assert (forall ((tv34 List) (tv33 Nat)) (= (tf9 (Cons tv33 tv34)) (MakeTuple2 (plus (fst2 (tf8 tv34)) (times tv33 (snd2 (tf8 tv34)))) (times tv33 (snd2 (tf8 tv34)))))))
  (assert (forall ((tv30 List)) (= (tf8 tv30) (tf9 tv30))))
  (assert (forall ((tv29 List)) (= (tailsNew tv29) (tf8 tv29))))
  (assert (forall ((tv35 List)) (= (mainNew tv35) (fst2 (tailsNew tv35)))))
  (assert (not (forall ((inp0 List)) (= (main inp0) (mainNew inp0)))))
  (check-sat)