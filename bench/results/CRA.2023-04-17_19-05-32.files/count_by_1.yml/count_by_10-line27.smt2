(declare-const |i':39| Int)
(declare-const |K:42| Int)
(assert (and (or (not (<= (- |K:42|) 0)) (= (+ |i':39| (- |K:42|)) 0))
               (or (and (= |K:42| 0) (= (- |i':39|) 0))
                     (and (<= (+ (- |K:42|) 1) 0) (<= (+ |i':39| -1000000) 0)
                            (<= (+ (- |i':39|) 1) 0))) (<= (- |K:42|) 0)
               (<= (- |i':39|) 0) (<= (+ (- |i':39|) 1000000) 0)
               (not (= (+ |i':39| -1000000) 0))))
(check-sat)
