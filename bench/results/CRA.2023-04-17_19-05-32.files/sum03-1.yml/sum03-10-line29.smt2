(declare-const |tmp___1':38| Int)
(declare-const |phi_tmp___1:12:14:35| Int)
(declare-const tmp___1 Int)
(declare-const |x':37| Int)
(declare-const |sn':36| Int)
(declare-const |K:44| Int)
(declare-const |phi_sn:9:33| Int)
(declare-const |havoc:0| Int)
(declare-const |havoc:2| Int)
(declare-const |phi_tmp___1:10:11:13:34| Int)
(assert (and (<= (- |havoc:0|) 0) (<= (- |havoc:2|) 0)
               (or (not (<= (- |K:44|) 0)) (= (+ |x':37| (- |K:44|)) 0))
               (or (not (and (<= (- |K:44|) 0) (<= |K:44| 0)))
                     (= (+ (- tmp___1) |tmp___1':38|) 0))
               (or (not (<= (+ (- |K:44|) 1) 0)) (= (+ |tmp___1':38| -1) 0))
               (or (not (<= (- |K:44|) 0)) (<= (+ |sn':36| (* -2 |K:44|)) 0))
               (or (not (<= (- |K:44|) 0)) (<= (- |sn':36|) 0))
               (or (not (<= (- |K:44|) 0))
                     (<= (+ (* -10 |sn':36|) (- (* |K:44| |K:44|))
                              (* 21 |K:44|)) 0))
               (or (and (= |K:44| 0) (= (+ tmp___1 (- |tmp___1':38|)) 0)
                          (= (- |x':37|) 0) (= (- |sn':36|) 0))
                     (and (<= (+ (- |K:44|) 1) 0) (= (+ |tmp___1':38| -1) 0)
                            (<= (+ |sn':36| (* -2 |x':37|)) 0)
                            (<= (- |sn':36|) 0)
                            (<= (+ (* -5 |sn':36|) (- |x':37|) 11) 0)))
               (<= (- |K:44|) 0) (<= (- |x':37|) 0) (<= (- |sn':36|) 0)
               (or (and (<= (+ (- |x':37|) 10) 0)
                          (= (+ (- |phi_sn:9:33|) |sn':36|) 0))
                     (and (< (+ |x':37| -10) 0)
                            (= (+ (- |phi_sn:9:33|) |sn':36| 2) 0)))
               (or (and (not (= (+ |phi_sn:9:33| (* -2 |x':37|) -2) 0))
                          (or (and (not (= |phi_sn:9:33| 0))
                                     (= (- |phi_tmp___1:10:11:13:34|) 0))
                                (and (= |phi_sn:9:33| 0)
                                       (= (+ (- |phi_tmp___1:10:11:13:34|) 1) 0)))
                          (= (+ (- |phi_tmp___1:12:14:35|)
                                  |phi_tmp___1:10:11:13:34|) 0))
                     (and (= (+ |phi_sn:9:33| (* -2 |x':37|) -2) 0)
                            (= (+ (- |phi_tmp___1:12:14:35|) 1) 0)))
               (= |phi_tmp___1:12:14:35| 0)))
(check-sat)
