(set-option :print-success false)
(set-logic ALIA)

(declare-fun a () (Array Int Int))
(declare-fun b () (Array Int Int))
(assert (forall ((i Int))
(exists ((j Int))
(= (select a i) (select b j)))))


(check-sat)
(get-model)
(exit)