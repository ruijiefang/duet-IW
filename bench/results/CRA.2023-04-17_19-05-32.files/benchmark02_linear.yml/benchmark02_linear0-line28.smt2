(declare-const havoc Int)
(declare-const |i':36:42| Int)
(declare-const |havoc:4| Int)
(declare-const |K:40:41| Int)
(assert (and (< (- |havoc:4|) 0)
               (or (not (<= (- |K:40:41|) 0))
                     (= (+ |i':36:42| (- |K:40:41|) (- |havoc:4|)) 0))
               (or (and (= |K:40:41| 0) (= (+ (- |i':36:42|) |havoc:4|) 0))
                     (and (<= (+ (- |K:40:41|) 1) 0)
                            (<= (+ (- havoc) |havoc:4| 1) 0)
                            (<= (+ (- |havoc:4|) 1) 0)
                            (<= (+ (- havoc) |i':36:42|) 0)
                            (<= (+ (- |i':36:42|) 2) 0)))
               (<= (- |K:40:41|) 0) (< (- |i':36:42|) 0)
               (<= (+ havoc (- |i':36:42|)) 0)
               (not (<= (+ (- |havoc:4|) 1) 0))))
(check-sat)