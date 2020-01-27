;; An non-linear CHC problem; the point is to check that we get a good summary
(set-logic HORN)
(declare-fun |nldoubler| (Int Int) Bool)

(assert (forall ((n Int) (x Int)) (=> (and (= n 0) (= x 1)) (nldoubler n x))))
(assert (forall ((n Int) (x1 Int) (x2 Int)) (=> (and (nldoubler n x1) (nldoubler n x2)) (nldoubler (+ n 1) (+ x1 x2)))))
(assert (forall ((n Int) (x Int)) (=> (and (< x 0) (nldoubler n x)) false)))

(check-sat)
