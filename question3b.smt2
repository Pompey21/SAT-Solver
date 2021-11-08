(set-option :print-success false)
(set-logic QF_UFBV)

(declare-fun v0 () (_ BitVec 4))
(declare-fun v1 () (_ BitVec 4))
(declare-fun f ((_ BitVec 4)) (_ BitVec 4))
(declare-fun g ((_ BitVec 4)) (_ BitVec 4))
(assert (= (f v0) (g v0)))
(assert (not (= (f v1) (g v1))))


(check-sat)
(get-model)
(exit)