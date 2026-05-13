(set-logic ALL)

(declare-const x1 Real)
(declare-const x2 Real)

(assert (= (* x1 x1 x1) x1))
(assert (> (* x1 x2) 1))
(assert (< (* x2 x2) 1/2))

(check-sat)
