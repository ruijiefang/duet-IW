(declare-const |K:36:37:39| Int)
(declare-const havoc Int)
(declare-const |x':32:38:40| Int)
(declare-const |havoc:2| Int)
(assert (and (= havoc 0) (< (- |havoc:2|) 0)
               (or (not (<= (- |K:36:37:39|) 0))
                     (= (+ |x':32:38:40| (- |K:36:37:39|) (- havoc)) 0))
               (or (and (= |K:36:37:39| 0) (= (+ (- |x':32:38:40|) havoc) 0))
                     (and (<= (+ (- |K:36:37:39|) 1) 0)
                            (<= (+ (- |havoc:2|) havoc 1) 0) (<= (- havoc) 0)
                            (<= (+ |x':32:38:40| (- |havoc:2|)) 0)
                            (<= (+ (- |x':32:38:40|) 1) 0)))
               (<= (- |K:36:37:39|) 0) (<= (- |x':32:38:40|) 0)
               (< (- |havoc:2|) 0) (<= (+ (- |x':32:38:40|) |havoc:2|) 0)
               (not (= (+ |x':32:38:40| (- |havoc:2|)) 0))))
(check-sat)