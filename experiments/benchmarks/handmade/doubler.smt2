;; An easy problem; the point is to check that we get a good summary
(set-logic HORN)
(declare-fun |doubler| (Int Int) Bool)

(assert (forall ((n Int) (x Int)) (=> (and (= n 0) (= x 1)) (doubler n x))))
(assert (forall ((n Int) (x Int)) (=> (doubler n x) (doubler (+ n 1) (+ x x)))))
(assert (forall ((n Int) (x Int)) (=> (and (< x 0) (doubler n x)) false)))

(check-sat)
