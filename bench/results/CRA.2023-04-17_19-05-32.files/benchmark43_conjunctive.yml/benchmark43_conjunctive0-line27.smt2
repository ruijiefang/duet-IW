(declare-const havoc Int)
(declare-const |phi_tmp___1:13:14:47:52| Int)
(declare-const |K:43:44:49| Int)
(declare-const |phi_tmp___1:15:48:53| Int)
(declare-const |y':38:45:50| Int)
(declare-const |x':37:46:51| Int)
(declare-const |havoc:2| Int)
(assert (and (< (+ havoc -100) 0) (< (+ |havoc:2| -100) 0)
               (or (not (<= (- |K:43:44:49|) 0))
                     (= (+ |y':38:45:50| (- |K:43:44:49|) (- |havoc:2|)) 0))
               (or (not (<= (- |K:43:44:49|) 0))
                     (= (+ |x':37:46:51| (- |K:43:44:49|) (- havoc)) 0))
               (or (and (= |K:43:44:49| 0)
                          (= (+ (- |y':38:45:50|) |havoc:2|) 0)
                          (= (+ (- |x':37:46:51|) havoc) 0))
                     (and (<= (+ (- |K:43:44:49|) 1) 0)
                            (<= (+ |havoc:2| -99) 0) (<= (+ havoc -99) 0)
                            (<= (+ |y':38:45:50| -100) 0)
                            (<= (+ |x':37:46:51| -100) 0)))
               (<= (- |K:43:44:49|) 0)
               (or (<= (+ (- |x':37:46:51|) 100) 0)
                     (and (< (+ |x':37:46:51| -100) 0)
                            (<= (+ (- |y':38:45:50|) 100) 0)))
               (or (and (not (= (+ |x':37:46:51| -100) 0))
                          (or (and (not (= (+ |y':38:45:50| -100) 0))
                                     (= (- |phi_tmp___1:13:14:47:52|) 0))
                                (and (= (+ |y':38:45:50| -100) 0)
                                       (= (+ (- |phi_tmp___1:13:14:47:52|) 1) 0)))
                          (= (+ (- |phi_tmp___1:15:48:53|)
                                  |phi_tmp___1:13:14:47:52|) 0))
                     (and (= (+ |x':37:46:51| -100) 0)
                            (= (+ (- |phi_tmp___1:15:48:53|) 1) 0)))
               (= |phi_tmp___1:15:48:53| 0)))
(check-sat)
