(declare-const havoc Int)
(declare-const |r':81:93| Int)
(declare-const |havoc:1| Int)
(declare-const |u':79:91| Int)
(declare-const |v':80:92| Int)
(declare-const |K:89:90| Int)
(assert (and (not (= (ite (< (+ (- havoc) (* |havoc:1| |havoc:1|)
                                  (* -2 |havoc:1|) 1) 0)
                          1 0) 0))
               (not (= (ite (= (+ (mod havoc 2) -1) 0) 1 0) 0))
               (or (not (<= (- |K:89:90|) 0))
                     (= (+ |v':80:92| |u':79:91| (* -2 |K:89:90|)
                             (* -2 |havoc:1|) -2) 0))
               (or (not (<= (- |K:89:90|) 0))
                     (<= (+ |v':80:92| (* -2 |K:89:90|) -1) 0))
               (or (not (<= (- |K:89:90|) 0)) (<= (+ (- |v':80:92|) 1) 0))
               (or (and (= |K:89:90| 0)
                          (= (+ (- |r':81:93|) (- havoc)
                                  (* |havoc:1| |havoc:1|)) 0)
                          (= (+ (- |v':80:92|) 1) 0)
                          (= (+ (- |u':79:91|) (* 2 |havoc:1|) 1) 0))
                     (and (<= (+ (- |K:89:90|) 1) 0)
                            (<= (+ (- |v':80:92|) 1) 0)))
               (<= (- |K:89:90|) 0) (< (- |v':80:92|) 0)
               (= (+ (* 4 |r':81:93|) (* |v':80:92| |v':80:92|)
                       (* -2 |v':80:92|) (- (* |u':79:91| |u':79:91|))
                       (* 2 |u':79:91|) (* 4 havoc)) 0) (<= (- |r':81:93|) 0)
               (<= |r':81:93| 0)
               (not (= (+ (* |v':80:92| |v':80:92|) (* -2 |v':80:92|)
                            (- (* |u':79:91| |u':79:91|)) (* 2 |u':79:91|)
                            (* 4 havoc)) 0))))
(check-sat)
