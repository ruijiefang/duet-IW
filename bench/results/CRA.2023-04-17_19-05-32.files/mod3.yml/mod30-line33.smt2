(declare-const |havoc:2:60| Int)
(declare-const havoc Int)
(declare-const tmp___0 Int)
(declare-const |tmp___1':72| Int)
(declare-const |x':69| Int)
(declare-const |K:77| Int)
(declare-const |tmp___0':71| Int)
(declare-const tmp___1 Int)
(declare-const |y':70| Int)
(assert (and (or (not (<= (- |K:77|) 0))
                   (<= (+ (- havoc) |x':69| (* -5 |K:77|)) 0))
               (or (not (<= (- |K:77|) 0)) (<= (+ |y':70| (- |K:77|) -1) 0))
               (or (not (<= (- |K:77|) 0))
                     (<= (+ (* 3 |y':70|) havoc (- |x':69|) |K:77| -3) 0))
               (or (not (<= (- |K:77|) 0))
                     (<= (+ havoc (- |x':69|) |K:77|) 0))
               (or (and (= |K:77| 0) (= (+ (- |tmp___1':72|) tmp___1) 0)
                          (= (+ (- |tmp___0':71|) tmp___0) 0)
                          (= (+ (- |y':70|) 1) 0) (= (+ havoc (- |x':69|)) 0))
                     (and (<= (+ (- |K:77|) 1) 0) (<= (+ (mod havoc 3) -2) 0)
                            (<= (- (mod havoc 3)) 0) (<= (+ |y':70| -1) 0)
                            (<= (- |y':70|) 0))) (<= (- |K:77|) 0)
               (<= (- |y':70|) 0) (= |havoc:2:60| 0) (= |y':70| 0)
               (not (= (mod |x':69| 3) 0))))
(check-sat)