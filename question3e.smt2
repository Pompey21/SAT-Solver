(set-option :print-success false)
(set-logic QF_S)

(declare-fun x () String)
(declare-const I Int)
(assert (= x "\0\1\2\3\04\005\x06\7\8\9ABC\\""\t\a\b"))
(assert (= I (str.len x)))


(check-sat)
(get-model)
(exit)