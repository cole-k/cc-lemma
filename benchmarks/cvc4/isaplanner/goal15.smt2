(declare-datatypes () ((Nat (succ (pred Nat)) (zero))))
(declare-datatypes () ((Lst (cons (head Nat) (tail Lst)) (nil))))
(declare-datatypes () ((Tree (node (data Nat) (left Tree) (right Tree)) (leaf))))
(declare-datatypes () ((Pair (mkpair (first Nat) (second Nat)))
                       (ZLst (zcons (zhead Pair) (ztail ZLst)) (znil))))
(declare-fun P (Nat) Bool)
(declare-fun f (Nat) Nat)
(declare-fun less (Nat Nat) Bool)
(declare-fun plus (Nat Nat) Nat)
(declare-fun minus (Nat Nat) Nat)
(declare-fun mult (Nat Nat) Nat)
(declare-fun nmax (Nat Nat) Nat)
(declare-fun nmin (Nat Nat) Nat)
(declare-fun append (Lst Lst) Lst)
(declare-fun len (Lst) Nat)
(declare-fun drop (Nat Lst) Lst)
(declare-fun take (Nat Lst) Lst)
(declare-fun count (Nat Lst) Nat)
(declare-fun last (Lst) Nat)
(declare-fun butlast (Lst) Lst)
(declare-fun mem (Nat Lst) Bool)
(declare-fun delete (Nat Lst) Lst)
(declare-fun rev (Lst) Lst)
(declare-fun lmap (Lst) Lst)
(declare-fun filter (Lst) Lst)
(declare-fun dropWhile (Lst) Lst)
(declare-fun takeWhile (Lst) Lst)
(declare-fun ins1 (Nat Lst) Lst)
(declare-fun insort (Nat Lst) Lst)
(declare-fun sorted (Lst) Bool)
(declare-fun sort (Lst) Lst)
(declare-fun zip (Lst Lst) ZLst)
(declare-fun zappend (ZLst ZLst) ZLst)
(declare-fun zdrop (Nat ZLst) ZLst)
(declare-fun ztake (Nat ZLst) ZLst)
(declare-fun zrev (ZLst) ZLst)
(declare-fun mirror (Tree) Tree)
(declare-fun height (Tree) Nat)
(define-fun leq ((x Nat) (y Nat)) Bool (or (= x y) (less x y)))
(assert (forall ((x Nat)) (= (less x zero) false)))
(assert (forall ((x Nat)) (= (less zero (succ x)) true)))
(assert (forall ((x Nat) (y Nat)) (= (less (succ x) (succ y)) (less x y))))
(assert (= (len nil) zero))
(assert (forall ((x Nat) (y Lst)) (= (len (cons x y)) (succ (len y)))))
(assert (forall ((i Nat)) (= (insort i nil) (cons i nil))))
(assert (forall ((i Nat) (x Nat) (y Lst)) (= (insort i (cons x y)) (ite (less i x) (cons i (cons x y)) (cons x (insort i y))))))
(assert (= (sort nil) nil))
(assert (forall ((x Nat) (y Lst)) (= (sort (cons x y)) (insort x (sort y)))))
(assert (not 
(forall ((x Nat) (l Lst)) (= (len (insort x l)) (succ (len l)))) ; G15 
))
(check-sat)
