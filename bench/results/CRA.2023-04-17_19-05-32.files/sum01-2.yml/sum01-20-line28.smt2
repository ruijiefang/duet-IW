(declare-const |phi_tmp___0:11:12:14:51:56| Int)
(declare-const havoc Int)
(declare-const |K:47:48:53| Int)
(declare-const |sn':41:49:54| Int)
(declare-const |phi_tmp___0:13:15:52:57| Int)
(declare-const |i':40:50:55| Int)
(assert (and (< (+ havoc -1000) 0) (<= (+ (- havoc) -1000) 0)
               (or (not (and (<= (- |K:47:48:53|) 0) (<= |K:47:48:53| 0)))
                     (= (+ |sn':41:49:54| (* -2 |K:47:48:53|)) 0))
               (or (not (<= (+ (- |K:47:48:53|) 1) 0))
                     (= (+ |sn':41:49:54| (* -2 |K:47:48:53|)) 0))
               (or (not (and (<= (- |K:47:48:53|) 0) (<= |K:47:48:53| 0)))
                     (= (+ |i':40:50:55| (- |K:47:48:53|) -1) 0))
               (or (not (<= (+ (- |K:47:48:53|) 1) 0))
                     (= (+ |i':40:50:55| (- |K:47:48:53|) -1) 0))
               (or (and (= |K:47:48:53| 0) (= (- |sn':41:49:54|) 0)
                          (= (+ (- |i':40:50:55|) 1) 0))
                     (and (<= (+ (- |K:47:48:53|) 1) 0)
                            (<= (+ (- havoc) 1) 0)
                            (= (+ (* 2 |i':40:50:55|) (- |sn':41:49:54|) -2) 0)
                            (<= (+ |sn':41:49:54| (* -2 havoc)) 0)
                            (<= (+ (- |sn':41:49:54|) 2) 0)))
               (<= (- |K:47:48:53|) 0) (<= (- |sn':41:49:54|) 0)
               (< (- |i':40:50:55|) 0)
               (= (+ (* -2 |i':40:50:55|) |sn':41:49:54| 2) 0)
               (< (+ (- |i':40:50:55|) havoc) 0)
               (or (and (not (= (+ |sn':41:49:54| (* -2 havoc)) 0))
                          (or (and (not (= |sn':41:49:54| 0))
                                     (= (- |phi_tmp___0:11:12:14:51:56|) 0))
                                (and (= |sn':41:49:54| 0)
                                       (= (+ (- |phi_tmp___0:11:12:14:51:56|)
                                               1) 0)))
                          (= (+ (- |phi_tmp___0:13:15:52:57|)
                                  |phi_tmp___0:11:12:14:51:56|) 0))
                     (and (= (+ |sn':41:49:54| (* -2 havoc)) 0)
                            (= (+ (- |phi_tmp___0:13:15:52:57|) 1) 0)))
               (= |phi_tmp___0:13:15:52:57| 0)))
(check-sat)
