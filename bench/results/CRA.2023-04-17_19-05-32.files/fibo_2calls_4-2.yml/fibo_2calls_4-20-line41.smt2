(declare-const |param0':700| Int)
(declare-const |return':699| Int)
(assert (and (<= (+ (* -2 |return':699|) |param0':700| 4) 0)
               (<= (+ (* -2 |return':699|) (- |param0':700|) 4) 0)
               (<= (+ |param0':700| -4) 0) (= (+ |return':699| -3) 0)))
(check-sat)