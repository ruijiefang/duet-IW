(declare-const |K:28| Int)
(declare-const havoc Int)
(declare-const |x':25| Int)
(assert (and (<= (- havoc) 0)
               (or (not (<= (- |K:28|) 0))
                     (= (+ |x':25| (- |K:28|) (- havoc)) 0))
               (or (and (= |K:28| 0) (= (+ (- |x':25|) havoc) 0))
                     (and (<= (+ (- |K:28|) 1) 0) (<= (+ havoc -268435454) 0)
                            (<= (- havoc) 0) (<= (+ |x':25| -268435455) 0)
                            (<= (+ (- |x':25|) 1) 0))) (<= (- |K:28|) 0)
               (<= (- |x':25|) 0) (<= (+ (- |x':25|) 268435455) 0)
               (not (<= (+ (- |x':25|) 268435455) 0))))
(check-sat)
