(declare-const |x':56:68:72| Int)
(declare-const havoc Int)
(declare-const |K:65:66:70| Int)
(declare-const |z':58:67:71| Int)
(declare-const |havoc:1| Int)
(declare-const |y':57:69:73| Int)
(assert (and (<= (- havoc) 0) (<= (+ havoc -1000000) 0) (<= (- |havoc:1|) 0)
               (or (not (<= (- |K:65:66:70|) 0))
                     (= (+ |z':58:67:71| (- |K:65:66:70|)) 0))
               (or (not (<= (- |K:65:66:70|) 0))
                     (= (+ |x':56:68:72| |K:65:66:70| (- havoc)) 0))
               (or (not (<= (- |K:65:66:70|) 0))
                     (= (+ |y':57:69:73| (* 2 |K:65:66:70|) (- |havoc:1|)) 0))
               (or (and (= |K:65:66:70| 0) (= (- |z':58:67:71|) 0)
                          (= (+ (- |y':57:69:73|) |havoc:1|) 0)
                          (= (+ (- |x':56:68:72|) havoc) 0))
                     (and (<= (+ (- |K:65:66:70|) 1) 0)
                            (<= (+ (- havoc) 1) 0) (<= (- |x':56:68:72|) 0)
                            (<= (+ (- |z':58:67:71|) 1) 0)))
               (<= (- |K:65:66:70|) 0) (<= (- |z':58:67:71|) 0)
               (<= (- |x':56:68:72|) 0) (<= (- |x':56:68:72|) 0)
               (<= |x':56:68:72| 0) (= (+ (- |havoc:1|) havoc) 0)
               (not (= (+ |y':57:69:73| |z':58:67:71|) 0))))
(check-sat)
