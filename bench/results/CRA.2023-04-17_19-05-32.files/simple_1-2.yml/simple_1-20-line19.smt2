(declare-const |x':24| Int)
(declare-const |K:27| Int)
(assert (and (or (not (<= (- |K:27|) 0)) (= (+ |x':24| (* -2 |K:27|)) 0))
               (or (and (= |K:27| 0) (= (- |x':24|) 0))
                     (and (<= (+ (- |K:27|) 1) 0)
                            (<= (+ |x':24| -268435456) 0)
                            (<= (+ (- |x':24|) 2) 0))) (<= (- |K:27|) 0)
               (<= (- |x':24|) 0) (<= (+ (- |x':24|) 268435455) 0)
               (not (= (mod |x':24| 2) 0))))
(check-sat)
