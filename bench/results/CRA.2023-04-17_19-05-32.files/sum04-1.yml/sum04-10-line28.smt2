(declare-const |i':40| Int)
(declare-const |K:45| Int)
(declare-const |sn':41| Int)
(declare-const |phi_tmp:9:13:15| Int)
(declare-const |phi_tmp:14:16| Int)
(assert (and (or (not (<= (- |K:45|) 0)) (= (+ |i':40| (- |K:45|) -1) 0))
               (or (not (<= (- |K:45|) 0))
                     (<= (+ (* 5 |sn':41|) (* |K:45| |K:45|) (* -15 |K:45|)) 0))
               (or (not (<= (- |K:45|) 0)) (<= (+ |sn':41| (* -2 |K:45|)) 0))
               (or (not (<= (- |K:45|) 0)) (<= (- |sn':41|) 0))
               (or (not (<= (- |K:45|) 0))
                     (<= (+ (* -3 |sn':41|) (- (* |K:45| |K:45|))
                              (* 7 |K:45|)) 0))
               (or (and (= |K:45| 0) (= (- |sn':41|) 0)
                          (= (+ (- |i':40|) 1) 0))
                     (and (<= (+ (- |K:45|) 1) 0) (<= (+ |i':40| -9) 0)
                            (<= (- |sn':41|) 0) (<= (+ (- |i':40|) 2) 0)
                            (<= (+ (* -3 |sn':41|) (* -2 |i':40|) 10) 0)))
               (<= (- |K:45|) 0) (<= (- |sn':41|) 0) (< (- |i':40|) 0)
               (< (+ (- |i':40|) 8) 0)
               (or (and (not (= (+ |sn':41| -16) 0))
                          (or (and (not (= |sn':41| 0))
                                     (= (- |phi_tmp:9:13:15|) 0))
                                (and (= |sn':41| 0)
                                       (= (+ (- |phi_tmp:9:13:15|) 1) 0)))
                          (= (+ (- |phi_tmp:14:16|) |phi_tmp:9:13:15|) 0))
                     (and (= (+ |sn':41| -16) 0)
                            (= (+ (- |phi_tmp:14:16|) 1) 0)))
               (= |phi_tmp:14:16| 0)))
(check-sat)