(declare-const |y':78:89| Int)
(declare-const |havoc:0| Int)
(declare-const |K:85:86| Int)
(declare-const |phi_tmp___0:16| Int)
(declare-const |x':77:88| Int)
(declare-const |__cost':76:87| Int)
(assert (and (or (not (<= (- |K:85:86|) 0))
                   (= (+ |__cost':76:87| (- |K:85:86|)) 0))
               (or (not (<= (- |K:85:86|) 0))
                     (= (+ (- |y':78:89|) (* 2 |x':77:88|) (- |K:85:86|)) 0))
               (or (not (<= (- |K:85:86|) 0))
                     (<= (+ |y':78:89| (- |K:85:86|)) 0))
               (or (not (<= (- |K:85:86|) 0))
                     (<= (+ (- |y':78:89|) (- |K:85:86|)) 0))
               (or (and (= |K:85:86| 0) (= (- |y':78:89|) 0)
                          (= (- |x':77:88|) 0) (= (- |__cost':76:87|) 0))
                     (and (<= (+ (- |K:85:86|) 1) 0)
                            (<= (+ (- |__cost':76:87|) 1) 0)
                            (<= (- |x':77:88|) 0) (<= (- |y':78:89|) 0)))
               (<= (- |K:85:86|) 0) (<= (- |x':77:88|) 0)
               (<= (- |y':78:89|) 0) (<= (+ |havoc:0| (- |x':77:88|)) 0)
               (<= |y':78:89| 0)
               (or (and (<= |havoc:0| 0) (= (- |phi_tmp___0:16|) 0))
                     (and (< (- |havoc:0|) 0)
                            (= (+ (- |phi_tmp___0:16|) |havoc:0|) 0)))
               (not (<= (+ (* -2 |phi_tmp___0:16|) |__cost':76:87|) 0))))
(check-sat)
