(declare-const |phi_tmp___2:17:18:20:61:66| Int)
(declare-const |k':48:56:59:64| Int)
(declare-const havoc Int)
(declare-const |i':47:57:60:65| Int)
(declare-const |K:54:55:58:63| Int)
(declare-const |havoc:4| Int)
(declare-const |havoc:2| Int)
(declare-const |phi_tmp___2:19:21:62:67| Int)
(assert (and (= havoc 0) (= |havoc:2| 0) (< (- |havoc:4|) 0)
               (or (not (and (<= (- |K:54:55:58:63|) 0)
                               (<= |K:54:55:58:63| 0)))
                     (= (+ |k':48:56:59:64| (- |K:54:55:58:63|) (- |havoc:2|)) 0))
               (or (not (<= (+ (- |K:54:55:58:63|) 1) 0))
                     (= (+ (* 2 |k':48:56:59:64|) (* -2 |K:54:55:58:63|)
                             (- |havoc:2|) (- havoc)) 0))
               (or (not (and (<= (- |K:54:55:58:63|) 0)
                               (<= |K:54:55:58:63| 0)))
                     (= (+ |i':47:57:60:65| (- |K:54:55:58:63|) (- havoc)) 0))
               (or (not (<= (+ (- |K:54:55:58:63|) 1) 0))
                     (= (+ (* 2 |i':47:57:60:65|) (* -2 |K:54:55:58:63|)
                             (- |havoc:2|) (- havoc)) 0))
               (or (and (= |K:54:55:58:63| 0)
                          (= (+ (- |k':48:56:59:64|) |havoc:2|) 0)
                          (= (+ (- |i':47:57:60:65|) havoc) 0))
                     (and (<= (+ (- |K:54:55:58:63|) 1) 0)
                            (= (+ |havoc:2| (- havoc)) 0)
                            (<= (+ (- |havoc:4|) havoc 1) 0) (<= (- havoc) 0)
                            (= (+ (- |i':47:57:60:65|) |k':48:56:59:64|) 0)
                            (<= (+ |i':47:57:60:65| (- |havoc:4|)) 0)
                            (<= (+ (- |i':47:57:60:65|) 1) 0)))
               (<= (- |K:54:55:58:63|) 0) (<= (- |i':47:57:60:65|) 0)
               (<= (- |k':48:56:59:64|) 0) (< (- |havoc:4|) 0)
               (= (+ |i':47:57:60:65| (- |k':48:56:59:64|)) 0)
               (<= (+ (- |i':47:57:60:65|) |havoc:4|) 0)
               (or (and (= (+ |i':47:57:60:65| (- |k':48:56:59:64|)) 0)
                          (or (and (not (= (+ |k':48:56:59:64| (- |havoc:4|)) 0))
                                     (= (- |phi_tmp___2:17:18:20:61:66|) 0))
                                (and (= (+ |k':48:56:59:64| (- |havoc:4|)) 0)
                                       (= (+ (- |phi_tmp___2:17:18:20:61:66|)
                                               1) 0)))
                          (= (+ (- |phi_tmp___2:19:21:62:67|)
                                  |phi_tmp___2:17:18:20:61:66|) 0))
                     (and (not (= (+ |i':47:57:60:65| (- |k':48:56:59:64|)) 0))
                            (= (- |phi_tmp___2:19:21:62:67|) 0)))
               (= |phi_tmp___2:19:21:62:67| 0)))
(check-sat)