(declare-const |tmp':30| Int)
(declare-const |x':29| Int)
(declare-const tmp Int)
(declare-const |K:34| Int)
(declare-const |havoc:0:28| Int)
(assert (and (or (not (<= (- |K:34|) 0)) (= (+ |x':29| (- |K:34|)) 0))
               (or (and (= |K:34| 0) (= (+ (- |tmp':30|) tmp) 0)
                          (= (- |x':29|) 0))
                     (and (<= (+ (- |K:34|) 1) 0) (<= (+ (- |x':29|) 1) 0)))
               (<= (- |K:34|) 0) (<= (- |x':29|) 0) (= |havoc:0:28| 0)
               (not (<= (- |x':29|) 0))))
(check-sat)
