(set-logic QF_LRA)
(declare-const x Real) (declare-const y Real)
(assert (> (+ x y) 1.5)) (assert (< x (- 1))) (assert (<= y (/ 1 4)))
(check-sat)
