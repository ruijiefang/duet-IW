(declare-const |K:64:65| Int)
(declare-const |phi_tmp___0:17:19:53:70| Int)
(declare-const |sn':57:68| Int)
(declare-const |j':56:66| Int)
(declare-const |i':55:67| Int)
(declare-const |phi_tmp___0:14:16:18:52:69| Int)
(declare-const |havoc:0| Int)
(assert (and (<= (- |havoc:0|) 0) (not (= (+ |havoc:0| -2147483647) 0))
               (or (not (and (<= (- |K:64:65|) 0) (<= |K:64:65| 0)))
                     (= (+ |j':56:66| |K:64:65| -10) 0))
               (or (not (<= (+ (- |K:64:65|) 1) 0))
                     (= (+ |j':56:66| |K:64:65| -10) 0))
               (or (not (and (<= (- |K:64:65|) 0) (<= |K:64:65| 0)))
                     (= (+ |i':55:67| (- |K:64:65|) -1) 0))
               (or (not (<= (+ (- |K:64:65|) 1) 0))
                     (= (+ |i':55:67| (- |K:64:65|) -1) 0))
               (or (not (and (<= (- |K:64:65|) 0) (<= |K:64:65| 0)))
                     (<= (+ (* -5 |sn':57:68|) (- (* |K:64:65| |K:64:65|))
                              (* 11 |K:64:65|)) 0))
               (or (not (<= (+ (- |K:64:65|) 1) 0))
                     (<= (+ (* -5 |sn':57:68|) (- (* |K:64:65| |K:64:65|))
                              (* 11 |K:64:65|)) 0))
               (or (not (<= (- |K:64:65|) 0))
                     (<= (+ |sn':57:68| (* -2 |K:64:65|)) 0))
               (or (not (<= (- |K:64:65|) 0)) (<= (- |sn':57:68|) 0))
               (or (and (= |K:64:65| 0) (= (- |sn':57:68|) 0)
                          (= (+ (- |j':56:66|) 10) 0)
                          (= (+ (- |i':55:67|) 1) 0))
                     (and (<= (+ (- |K:64:65|) 1) 0)
                            (<= (+ (- |havoc:0|) 1) 0)
                            (= (+ |i':55:67| |j':56:66| -11) 0)
                            (<= (+ |i':55:67| (- |havoc:0|) -1) 0)
                            (<= (- |sn':57:68|) 0)
                            (<= (+ (- |i':55:67|) 2) 0)
                            (<= (+ (* -5 |sn':57:68|) (* -2 |i':55:67|) 14) 0)))
               (<= (- |K:64:65|) 0) (<= (- |sn':57:68|) 0)
               (< (- |i':55:67|) 0) (<= (- |havoc:0|) 0)
               (= (+ |i':55:67| |j':56:66| -11) 0)
               (< (+ (- |i':55:67|) |havoc:0|) 0)
               (or (and (not (= (+ |sn':57:68| (* -2 |havoc:0|)) 0))
                          (or (and (not (= |sn':57:68| 0))
                                     (= (- |phi_tmp___0:14:16:18:52:69|) 0))
                                (and (= |sn':57:68| 0)
                                       (= (+ (- |phi_tmp___0:14:16:18:52:69|)
                                               1) 0)))
                          (= (+ (- |phi_tmp___0:17:19:53:70|)
                                  |phi_tmp___0:14:16:18:52:69|) 0))
                     (and (= (+ |sn':57:68| (* -2 |havoc:0|)) 0)
                            (= (+ (- |phi_tmp___0:17:19:53:70|) 1) 0)))
               (= |phi_tmp___0:17:19:53:70| 0)))
(check-sat)
