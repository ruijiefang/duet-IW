(declare-const |p':59:70:73| Int)
(declare-const havoc Int)
(declare-const |havoc:2| Int)
(declare-const |K:68:69:72| Int)
(declare-const |havoc:1| Int)
(declare-const |i':60:71:74| Int)
(assert (and (< (+ havoc -1000000) 0) (< (+ |havoc:1| -1000000) 0)
               (< (+ |havoc:2| -1000000) 0) (< (- havoc) 0)
               (< (- |havoc:1|) 0) (< (- |havoc:2|) 0)
               (<= (+ (- |havoc:1|) havoc) 0)
               (<= (+ (* 2 |havoc:2|) (- |havoc:1|) havoc) 0)
               (or (not (and (<= (- |K:68:69:72|) 0) (<= |K:68:69:72| 0)))
                     (= (+ |p':59:70:73| (* -2 |K:68:69:72|) (- havoc)) 0))
               (or (not (<= (+ (- |K:68:69:72|) 1) 0))
                     (= (+ |p':59:70:73| (* -2 |K:68:69:72|) (- havoc)) 0))
               (or (not (and (<= (- |K:68:69:72|) 0) (<= |K:68:69:72| 0)))
                     (= (+ |i':60:71:74| (- |K:68:69:72|)) 0))
               (or (not (<= (+ (- |K:68:69:72|) 1) 0))
                     (= (+ |i':60:71:74| (- |K:68:69:72|)) 0))
               (or (and (= |K:68:69:72| 0) (= (- |i':60:71:74|) 0)
                          (= (+ (- |p':59:70:73|) havoc) 0))
                     (and (<= (+ (- |K:68:69:72|) 1) 0)
                            (<= (+ (- |havoc:2|) 1) 0) (<= (+ (- havoc) 1) 0)
                            (<= (+ (- |havoc:1|) havoc 2) 0)
                            (<= (+ (- |havoc:1|) havoc 3) 0)
                            (= (+ (* 2 |i':60:71:74|) (- |p':59:70:73|) havoc) 0)
                            (<= (+ |p':59:70:73| (* -2 |havoc:2|) (- havoc)) 0)
                            (<= (+ (- |p':59:70:73|) 3) 0)
                            (<= (+ |p':59:70:73| (- |havoc:1|)) 0)
                            (<= (+ (- |p':59:70:73|) havoc 2) 0)
                            (<= (+ (- |havoc:1|) havoc 3) 0)))
               (<= (- |K:68:69:72|) 0) (< (- |havoc:1|) 0)
               (<= (- |i':60:71:74|) 0) (< (- |p':59:70:73|) 0)
               (< (- |havoc:2|) 0) (< (+ (- |havoc:1|) havoc) 0)
               (= (+ (* 2 |i':60:71:74|) (- |p':59:70:73|) havoc) 0)
               (< (+ |i':60:71:74| (- |havoc:2|)) 0)
               (< (+ (- |havoc:1|) havoc 2) 0) (not (<= (- |p':59:70:73|) 0))))
(check-sat)
