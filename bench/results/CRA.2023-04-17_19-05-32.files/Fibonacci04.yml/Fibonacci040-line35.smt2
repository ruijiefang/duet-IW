(declare-const |return':229| Int)
(declare-const havoc Int)
(declare-const |param0':230| Int)
(assert (and (<= (+ |param0':230| (- havoc)) 0) (<= (+ (- havoc) 5) 0)
               (<= (+ havoc -5) 0) (not (= (+ |return':229| -3) 0))))
(check-sat)
