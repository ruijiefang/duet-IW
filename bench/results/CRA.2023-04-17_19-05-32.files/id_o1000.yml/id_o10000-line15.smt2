(declare-const havoc Int)
(declare-const |param0':119| Int)
(declare-const |return':118| Int)
(assert (and (<= (- havoc) 0) (= (+ |return':118| (- havoc)) 0)
               (= |param0':119| 0) (<= (- havoc) 0)
               (= (+ |return':118| -1000) 0)))
(check-sat)