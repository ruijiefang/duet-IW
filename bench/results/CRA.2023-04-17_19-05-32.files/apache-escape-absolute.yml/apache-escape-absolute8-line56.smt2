(declare-const |cp':84:94:97| Int)
(declare-const havoc Int)
(declare-const |havoc:8:24:104| Int)
(declare-const |tmp':85:93:96| Int)
(declare-const |phi_tmp:103:105| Int)
(declare-const |havoc:2| Int)
(declare-const tmp Int)
(declare-const |K:91:92:95| Int)
(declare-const |havoc:7:23:81| Int)
(declare-const |havoc:1| Int)
(assert (and (<= (+ havoc -1000000) 0) (<= (+ (- havoc) -1000000) 0)
               (<= (+ |havoc:1| -1000000) 0)
               (<= (+ (- |havoc:1|) -1000000) 0)
               (<= (+ |havoc:2| -1000000) 0)
               (<= (+ (- |havoc:2|) -1000000) 0) (< (- havoc) 0)
               (< (- |havoc:1|) 0) (<= (- |havoc:2|) 0) (not (= |havoc:2| 0))
               (<= (+ |havoc:2| (- havoc) 1) 0)
               (< (+ |havoc:2| (- havoc) -1) 0) (<= (+ (- |havoc:2|) 1) 0)
               (not (= |havoc:7:23:81| 0)) (< (+ |havoc:2| (- havoc)) 0)
               (<= (- |havoc:2|) 0)
               (or (not (and (<= (- |K:91:92:95|) 0) (<= |K:91:92:95| 0)))
                     (= (+ (- tmp) |tmp':85:93:96|) 0))
               (or (not (<= (+ (- |K:91:92:95|) 1) 0)) (= |tmp':85:93:96| 0))
               (or (not (<= (- |K:91:92:95|) 0))
                     (= (+ |cp':84:94:97| (- |K:91:92:95|) (- |havoc:2|)) 0))
               (or (and (= |K:91:92:95| 0) (= (+ tmp (- |tmp':85:93:96|)) 0)
                          (= (+ (- |cp':84:94:97|) |havoc:2|) 0))
                     (and (<= (+ (- |K:91:92:95|) 1) 0)
                            (<= (+ |havoc:2| (- havoc) 2) 0)
                            (<= (+ (- |havoc:2|) 1) 0) (= |tmp':85:93:96| 0)
                            (<= (+ |cp':84:94:97| (- havoc) 1) 0)
                            (<= (+ (- |cp':84:94:97|) 2) 0)))
               (<= (- |K:91:92:95|) 0) (< (- |cp':84:94:97|) 0)
               (< (- havoc) 0)
               (or (and (or (< (+ |cp':84:94:97| (- havoc) 1) 0)
                              (< (+ (- |cp':84:94:97|) havoc -1) 0))
                          (not (= |havoc:8:24:104| 0))
                          (= (+ (- |phi_tmp:103:105|) |havoc:8:24:104|) 0))
                     (and (<= (+ (- |cp':84:94:97|) havoc -1) 0)
                            (<= (+ |cp':84:94:97| (- havoc) 1) 0)
                            (= (+ (- |phi_tmp:103:105|) |tmp':85:93:96|) 0)))
               (< (+ |cp':84:94:97| (- havoc)) 0) (<= (- |cp':84:94:97|) 0)
               (not (= (+ |cp':84:94:97| (- havoc) 1) 0))
               (not (< (+ |cp':84:94:97| (- havoc) 1) 0))))
(check-sat)
