(declare-const |c':62| Int)
(declare-const havoc Int)
(declare-const |havoc:2| Int)
(declare-const |havoc:1| Int)
(declare-const |x':60| Int)
(declare-const |K:74| Int)
(declare-const |y':61| Int)
(assert (and (or (not (<= (- |K:74|) 0)) (= (+ |c':62| (- |K:74|) -1) 0))
               (or (and (= |K:74| 0) (= (+ (- |c':62|) 1) 0)
                          (= (+ (- |y':61|) 1) 0)
                          (= (+ (- |x':60|) |havoc:1|) 0))
                     (and (<= (+ (- |K:74|) 1) 0) (<= (+ (- |havoc:2|) 2) 0)
                            (<= (+ (- |havoc:2|) |c':62|) 0)
                            (<= (+ (- |c':62|) 2) 0))) (<= (- |K:74|) 0)
               (< (- |c':62|) 0)
               (not (= (+ (* havoc |x':60|) (- |x':60|) |havoc:1|
                            (- (* havoc |havoc:1| |y':61|))) 0))))
(check-sat)
