;; An non-trivial non-linear CHC problem that we might actually be able to prove sat
(set-logic HORN)
(declare-fun |doubler| (Int Int) Bool)
(declare-fun |nldoubler| (Int Int) Bool)

(assert (forall ((n Int) (x Int)) (=> (and (= n 0) (= x 1)) (doubler n x))))
(assert (forall ((n Int) (x Int)) (=> (doubler n x) (doubler (+ n 1) (+ x x)))))

(assert (forall ((n Int) (x Int)) (=> (and (= n 0) (= x 1)) (nldoubler n x))))
(assert (forall ((n Int) (x1 Int) (x2 Int)) (=> (and (nldoubler n x1) (nldoubler n x2)) (nldoubler (+ n 1) (+ x1 x2)))))

(assert (forall ((n1 Int) (x1 Int) (n2 Int) (x2 Int)) (=> (and (doubler n1 x1) (nldoubler n2 x2) (= n1 n2) (> x1 x2)) false)))

(check-sat)
