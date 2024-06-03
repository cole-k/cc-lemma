  (declare-datatypes () ((MyBool (MyTrue) (MyFalse))))
  (declare-datatypes () ((Nat (Zero) (Succ (proj_Succ_0 Nat)))))
  (declare-datatypes () ((Tree (Leaf (proj_Leaf_0 Nat)) (Node (proj_Node_0 Nat) (proj_Node_1 Tree) (proj_Node_2 Tree)))))
  (declare-datatypes () ((TreeMemo (Mleaf (proj_Mleaf_0 Nat)) (Mnode (proj_Mnode_0 Nat) (proj_Mnode_1 Nat) (proj_Mnode_2 TreeMemo) (proj_Mnode_3 TreeMemo)))))
  (declare-fun tf0 (TreeMemo) Nat)
  (declare-fun memo (TreeMemo) Nat)
  (declare-fun myand (MyBool MyBool) MyBool)
  (declare-fun nateq (Nat Nat) MyBool)
  (declare-fun plus (Nat Nat) Nat)
  (declare-fun tf2 (TreeMemo) MyBool)
  (declare-fun tf1 (TreeMemo) MyBool)
  (declare-fun ismemo (TreeMemo) MyBool)
  (declare-fun tf4 (TreeMemo) Tree)
  (declare-fun tf3 (TreeMemo) Tree)
  (declare-fun repr (TreeMemo) Tree)
  (declare-fun tf6 (TreeMemo) TreeMemo)
  (declare-fun tf5 (TreeMemo) TreeMemo)
  (declare-fun target (TreeMemo) TreeMemo)
  (declare-fun tf7 (Tree) Nat)
  (declare-fun spec (Tree) Nat)
  (declare-fun ite2 (MyBool Nat) Nat)
  (declare-fun main (TreeMemo) Nat)
  (declare-fun mainNew (TreeMemo) Nat)
  (assert (forall ((tv1 Nat)) (= (tf0 (Mleaf tv1)) (Succ Zero))))
  (assert (forall ((tv5 TreeMemo) (tv4 TreeMemo) (tv3 Nat) (tv2 Nat)) (= (tf0 (Mnode tv2 tv3 tv4 tv5)) tv2)))
  (assert (forall ((tv0 TreeMemo)) (= (memo tv0) (tf0 tv0))))
  (assert (forall ((x MyBool)) (= (myand MyFalse x) MyFalse)))
  (assert (forall ((true MyBool)) (= (myand true MyFalse) MyFalse)))
  (assert (= (myand MyTrue MyTrue) MyTrue))
  (assert (= (nateq Zero Zero) MyTrue))
  (assert (forall ((x Nat)) (= (nateq Zero (Succ x)) MyFalse)))
  (assert (forall ((x Nat)) (= (nateq (Succ x) Zero) MyFalse)))
  (assert (forall ((y Nat) (x Nat)) (= (nateq (Succ x) (Succ y)) (nateq x y))))
  (assert (forall ((x Nat)) (= (plus Zero x) x)))
  (assert (forall ((y Nat) (x Nat)) (= (plus (Succ x) y) (Succ (plus x y)))))
  (assert (forall ((tv9 Nat)) (= (tf2 (Mleaf tv9)) MyTrue)))
  (assert (forall ((tv13 TreeMemo) (tv11 Nat) (tv12 TreeMemo) (tv10 Nat)) (= (tf2 (Mnode tv10 tv11 tv12 tv13)) (myand (nateq tv10 (plus (Succ Zero) (plus (memo tv12) (memo tv13)))) (myand (tf1 tv12) (tf1 tv13))))))
  (assert (forall ((tv7 TreeMemo)) (= (tf1 tv7) (tf2 tv7))))
  (assert (forall ((tv6 TreeMemo)) (= (ismemo tv6) (tf1 tv6))))
  (assert (forall ((tv17 Nat)) (= (tf4 (Mleaf tv17)) (Leaf tv17))))
  (assert (forall ((tv21 TreeMemo) (tv20 TreeMemo) (tv19 Nat) (tv18 Nat)) (= (tf4 (Mnode tv18 tv19 tv20 tv21)) (Node tv19 (tf3 tv20) (tf3 tv21)))))
  (assert (forall ((tv15 TreeMemo)) (= (tf3 tv15) (tf4 tv15))))
  (assert (forall ((tv14 TreeMemo)) (= (repr tv14) (tf3 tv14))))
  (assert (forall ((tv24 Nat)) (= (tf6 (Mleaf tv24)) (Mleaf tv24))))
  (assert (forall ((tv27 TreeMemo) (tv28 TreeMemo) (tv26 Nat) (tv25 Nat)) (= (tf6 (Mnode tv25 tv26 tv27 tv28)) (Mnode tv25 tv26 tv27 tv28))))
  (assert (forall ((tv23 TreeMemo)) (= (tf5 tv23) (tf6 tv23))))
  (assert (forall ((tv22 TreeMemo)) (= (target tv22) (tf5 tv22))))
  (assert (forall ((tv30 Nat)) (= (tf7 (Leaf tv30)) (Succ Zero))))
  (assert (forall ((tv33 Tree) (tv32 Tree) (tv31 Nat)) (= (tf7 (Node tv31 tv32 tv33)) (Succ Zero))))
  (assert (forall ((tv29 Tree)) (= (spec tv29) (tf7 tv29))))
  (assert (forall ((x Nat)) (= (ite2 MyTrue x) x)))
  (assert (forall ((x Nat)) (= (ite2 MyFalse x) Zero)))
  (assert (forall ((tv34 TreeMemo)) (= (main tv34) (ite2 (ismemo tv34) (spec (repr (target tv34)))))))
  (assert (forall ((tv35 TreeMemo)) (= (mainNew tv35) (ite2 (ismemo tv35) (Succ Zero)))))
  (assert (not (forall ((inp0 TreeMemo)) (= (main inp0) (mainNew inp0)))))
  (check-sat)