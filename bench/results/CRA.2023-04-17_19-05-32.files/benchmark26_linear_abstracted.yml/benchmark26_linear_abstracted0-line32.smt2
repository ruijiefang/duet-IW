(declare-const havoc Int)
(declare-const |phi_x:16:19| Int)
(declare-const |havoc:6:13:17| Int)
(declare-const |havoc:2| Int)
(declare-const |phi_x:14:15:18| Int)
(assert (and (< (+ (- |havoc:2|) havoc) 0)
               (or (and (< (+ (- |havoc:2|) havoc) 0)
                          (< (+ |havoc:6:13:17| (- |havoc:2|)) 0)
                          (or (and (<= (+ (- |havoc:6:13:17|) |havoc:2|) 0)
                                     (= (+ (- |phi_x:14:15:18|)
                                             |havoc:6:13:17|) 0))
                                (and (< (+ |havoc:6:13:17| (- |havoc:2|)) 0)
                                       (= (+ (- |phi_x:14:15:18|)
                                               |havoc:6:13:17| 1) 0)))
                          (<= (+ (- |phi_x:14:15:18|) |havoc:2|) 0)
                          (= (+ (- |phi_x:16:19|) |phi_x:14:15:18|) 0))
                     (and (<= (+ |havoc:2| (- havoc)) 0)
                            (= (+ (- |phi_x:16:19|) havoc) 0)))
               (not (= (+ |phi_x:16:19| (- |havoc:2|)) 0))))
(check-sat)