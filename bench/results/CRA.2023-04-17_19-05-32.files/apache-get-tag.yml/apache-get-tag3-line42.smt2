(declare-const |tmp':65:73| Int)
(declare-const havoc Int)
(declare-const tmp Int)
(declare-const |K:71:72| Int)
(declare-const |havoc:3:16:63| Int)
(declare-const |t':64:74| Int)
(assert (and (<= (+ (- havoc) 1) 0)
               (or (not (and (<= (- |K:71:72|) 0) (<= |K:71:72| 0)))
                     (= (+ (- tmp) |tmp':65:73|) 0))
               (or (not (<= (+ (- |K:71:72|) 1) 0)) (= |tmp':65:73| 0))
               (or (not (<= (- |K:71:72|) 0))
                     (= (+ |t':64:74| (- |K:71:72|)) 0))
               (or (and (= |K:71:72| 0) (= (+ tmp (- |tmp':65:73|)) 0)
                          (= (- |t':64:74|) 0))
                     (and (<= (+ (- |K:71:72|) 1) 0) (<= (+ (- havoc) 2) 0)
                            (= |tmp':65:73| 0)
                            (<= (+ |t':64:74| (- havoc) 1) 0)
                            (<= (+ (- |t':64:74|) 1) 0)))
               (<= (- |K:71:72|) 0) (<= (- |t':64:74|) 0)
               (<= (+ (- havoc) 1) 0) (not (= (+ |t':64:74| (- havoc) 1) 0))
               (= |havoc:3:16:63| 0) (<= (- |t':64:74|) 0)
               (not (<= (+ |t':64:74| (- havoc) 1) 0))))
(check-sat)
