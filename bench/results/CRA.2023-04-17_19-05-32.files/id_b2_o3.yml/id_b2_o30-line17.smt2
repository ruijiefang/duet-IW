(declare-const havoc Int)
(declare-const |return':161| Int)
(declare-const |param0':162| Int)
(assert (and (<= (- havoc) 0) (= |param0':162| 0)
               (<= (+ |return':161| (- havoc)) 0) (<= (- |return':161|) 0)
               (= (+ |return':161| -3) 0)))
(check-sat)
