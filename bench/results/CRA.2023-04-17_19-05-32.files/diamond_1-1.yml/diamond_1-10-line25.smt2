(declare-const |havoc:0| Int)
(declare-const |K:37| Int)
(declare-const |x':32| Int)
(assert (and (<= (- |havoc:0|) 0)
               (or (not (<= (- |K:37|) 0))
                     (= (+ |x':32| (* (mod |havoc:0| 2) |K:37|) (* -2 |K:37|)) 0))
               (or (not (<= (- |K:37|) 0)) (<= (+ |x':32| (* -2 |K:37|)) 0))
               (or (not (<= (- |K:37|) 0)) (<= (+ (- |x':32|) |K:37|) 0))
               (or (and (= |K:37| 0) (= (- |x':32|) 0))
                     (and (<= (+ (- |K:37|) 1) 0)
                            (<= (+ (mod |havoc:0| 2) -1) 0)
                            (<= (- (mod |havoc:0| 2)) 0) (<= (- |havoc:0|) 0)
                            (<= (+ (mod |havoc:0| 2) |x':32| -100) 0)
                            (<= (+ (mod |havoc:0| 2) -1) 0)
                            (<= (- (mod |havoc:0| 2)) 0) (<= (- |havoc:0|) 0)
                            (<= (+ (- (mod |havoc:0| 2)) (- |x':32|) 2) 0)))
               (<= (- |K:37|) 0) (<= (- |havoc:0|) 0) (<= (- |x':32|) 0)
               (<= (+ (- |x':32|) 99) 0)
               (not (= (+ (mod |x':32| 2) (- (mod |havoc:0| 2))) 0))))
(check-sat)
