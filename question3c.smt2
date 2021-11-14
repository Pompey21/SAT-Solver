(set-option :print-success false)
(set-logic QF_BV)


(declare-fun x2 () (_ BitVec 32))
(declare-fun x1 () (_ BitVec 32))
(declare-fun b1 () Bool)
(assert (= ((_ extract 0 0) (bvxor x1 x2)) #b1))


(check-sat)
(get-model)
(exit)