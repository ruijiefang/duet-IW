(declare-const |param0@width':107| Int)
(declare-const |K:112| Int)
(declare-const |type_err:58| Int)
(declare-const |param0':105| Int)
(declare-const |type_err:59| Int)
(declare-const |param0@pos':106| Int)
(assert (and (or (not (<= (- |K:112|) 0))
                   (= (+ |param0':105| (* 2 |K:112|) -2) 0)) (= |K:112| 0)
               (= (+ (- |param0@width':107|) |type_err:58|) 0)
               (= (+ (- |param0@pos':106|) |type_err:59|) 0)
               (= (+ (- |param0':105|) 2) 0) (<= (- |K:112|) 0)
               (<= (+ (- |param0':105|) 3) 0) (<= (+ (- |param0':105|) 4) 0)
               (<= (+ |param0':105| -4) 0)))
(check-sat)
