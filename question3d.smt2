(set-option :print-success false)
(set-logic QF_LIRA)

(declare-fun x0 () Real)
(declare-fun x1 () Real)
(assert (>= x0 0))
(assert (>= x1 0))
(assert (= (/ x0 x1) 2))
(check-sat)

(get-model)
(exit)
