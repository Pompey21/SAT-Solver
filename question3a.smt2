(set-option :print-success false)
(set-logic QF_UFIDL)

(declare-fun x0 () Int)
(declare-fun x1 () Int)
(assert (>= x0 0))
(assert (>= x1 0))
(assert (= (- x0 x1) 1))


(check-sat)
(get-model)
(exit)