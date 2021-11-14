(set-option :print-success false)
(set-logic QF_LIA)
; alpha: !(a || b) ? h : !(a==b) ? f : g
; beta:
(declare-const a Bool)
(declare-const b Bool)
(declare-const g Bool)
(declare-const f Bool)
(declare-const h Bool)
(declare-const alpha Bool)
(declare-const beta Bool)

;; Defining Alpha
(assert (= alpha (ite (not (or a b))
                h
                (ite (not (= a b))
                      f
                      g))))

;; Defining Beta
(assert (= beta (ite (not (or (not a) (not b)))
                     g
                     (ite (and (not a) (not b)) h f))))

;; Defining Equivalence
(assert (not (= alpha beta)))

(check-sat)
;(get-model)
(exit)

