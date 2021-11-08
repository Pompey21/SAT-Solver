(set-option :print-success false)
(set-logic ALIA)

(declare-fun a () (Array Int Int))
(assert (forall ((i Int)) (= (select a i) 0)))


(check-sat)
(get-model)
(exit)