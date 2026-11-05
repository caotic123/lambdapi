(set-logic QF_LIA)
(declare-const x Int) (declare-const y Int)
(assert (= (+ (* 2 x) (* 4 y)) 7))
(check-sat)
