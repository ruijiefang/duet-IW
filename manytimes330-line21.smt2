(declare-const |phi___retres2:59:620| Int)
(declare-const |havoc:9| Int)
(declare-const havoc Int)
(declare-const |phi___retres2:59:62| Int)
(assert (and (or (and (<= (- havoc) 0)
                        (= (+ (- |phi___retres2:59:62|) havoc) 0))
                   (and (< havoc 0)
                          (= (+ (- |phi___retres2:59:62|) (- havoc)) 0)))
               (or (and (<= (- |havoc:9|) 0)
                          (= (+ (- |phi___retres2:59:620|) |havoc:9|) 0))
                     (and (< |havoc:9| 0)
                            (= (+ (- |phi___retres2:59:620|) (- |havoc:9|)) 0)))
               (not (= (+ (- |phi___retres2:59:620|) 1) 0))))
(check-sat)