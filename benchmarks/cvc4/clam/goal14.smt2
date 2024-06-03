(declare-datatypes () ((Nat (succ (pred Nat)) (zero))))
(declare-datatypes () ((Lst (cons (head Nat) (tail Lst)) (nil))))
(declare-datatypes () ((Tree (node (data Nat) (left Tree) (right Tree)) (leaf))))
(declare-datatypes () ((Pair (mkpair (first Nat) (second Nat)))
                       (ZLst (zcons (zhead Pair) (ztail ZLst)) (znil))))
(declare-fun less (Nat Nat) Bool)
(declare-fun plus (Nat Nat) Nat)
(declare-fun mult (Nat Nat) Nat)
(declare-fun qmult (Nat Nat Nat) Nat)
(declare-fun exp (Nat Nat) Nat)
(declare-fun qexp (Nat Nat Nat) Nat)
(declare-fun fac (Nat) Nat)
(declare-fun qfac (Nat Nat) Nat)
(declare-fun double (Nat) Nat)
(declare-fun half (Nat) Nat)
(declare-fun even (Nat) Bool)
(declare-fun append (Lst Lst) Lst)
(declare-fun len (Lst) Nat)
(declare-fun drop (Nat Lst) Lst)
(declare-fun take (Nat Lst) Lst)
(declare-fun count (Nat Lst) Nat)
(declare-fun mem (Nat Lst) Bool)
(declare-fun rev (Lst) Lst)
(declare-fun qreva (Lst Lst) Lst)
(declare-fun insort (Nat Lst) Lst)
(declare-fun sorted (Lst) Bool)
(declare-fun sort (Lst) Lst)
(declare-fun rotate (Nat Lst) Lst)
(declare-fun revflat (Tree) Lst)
(declare-fun qrevaflat (Tree Lst) Lst)
(declare-fun lst-mem (Nat Lst) Bool)
(declare-fun lst-subset (Lst Lst) Bool)
(declare-fun lst-eq (Lst Lst) Bool)
(declare-fun lst-intersection (Lst Lst) Lst)
(declare-fun lst-union (Lst Lst) Lst)
(declare-fun eq (Nat Nat) Bool)
(assert (eq zero zero))
(assert (forall ((y Nat)) (not (eq zero (succ y)))))
(assert (forall ((x Nat)) (not (eq (succ x) zero))))
(assert (forall ((x Nat) (y Nat)) (= (eq (succ x) (succ y)) (eq x y))))
(define-fun leq ((x Nat) (y Nat)) Bool (or (eq x y) (less x y)))
(assert (forall ((x Nat)) (= (less x zero) false)))
(assert (forall ((x Nat)) (= (less zero (succ x)) true)))
(assert (forall ((x Nat) (y Nat)) (= (less (succ x) (succ y)) (less x y))))
(assert (forall ((i Nat)) (= (insort i nil) (cons i nil))))
(assert (forall ((i Nat) (x Nat) (y Lst)) (= (insort i (cons x y)) (ite (less i x) (cons i (cons x y)) (cons x (insort i y))))))
(assert (= (sorted nil) true))
(assert (forall ((x Nat)) (= (sorted (cons x nil)) true)))
(assert (forall ((x Nat) (z Nat) (y Lst)) (= (sorted (cons x (cons z y))) (and (sorted (cons z y)) (leq x z)))))
(assert (= (sort nil) nil))
(assert (forall ((x Nat) (y Lst)) (= (sort (cons x y)) (insort x (sort y)))))
(assert (not 
(forall ((x Lst)) (sorted (sort x)))  ; G14 
))
(check-sat)
