(declare-const |j':78:87:108| Int)
(declare-const |v':91:105| Int)
(declare-const |K:84:85:106| Int)
(declare-const |havoc:0:21:24| Int)
(declare-const v Int)
(declare-const |k':77:86:107| Int)
(declare-const |i':92:103| Int)
(declare-const |K:101:102| Int)
(declare-const |k':77:104| Int)
(assert (and (<= (- |havoc:0:21:24|) 0) (< (+ |havoc:0:21:24| -10) 0)
               (or (not (and (<= (- |K:101:102|) 0) (<= |K:101:102| 0)))
                     (= |i':92:103| 0))
               (or (not (<= (+ (- |K:101:102|) 1) 0))
                     (= (+ |i':92:103| -1) 0))
               (or (not (<= (- |K:101:102|) 0))
                     (<= (+ |k':77:104| (* -10000 |K:101:102|)) 0))
               (or (not (<= (- |K:101:102|) 0))
                     (<= (+ (- |k':77:104|) (* 2000 |K:101:102|)) 0))
               (or (and (= |K:101:102| 0) (= (- |k':77:104|) 0)
                          (= (- |i':92:103|) 0) (= (+ (- |v':91:105|) v) 0))
                     (and (<= (+ (- |K:101:102|) 1) 0)
                            (= (+ |havoc:0:21:24| -1) 0)
                            (= (+ |i':92:103| -1) 0)
                            (= (+ |havoc:0:21:24| -1) 0)
                            (<= (+ (- |k':77:104|) 2000) 0)
                            (<= (- |v':91:105|) 0)
                            (<= (+ (* -2000 |v':91:105|) (- |k':77:104|) 4000) 0)))
               (<= (- |K:101:102|) 0) (<= (- |k':77:104|) 0)
               (<= (- |i':92:103|) 0) (<= (- |havoc:0:21:24|) 0)
               (<= (+ (- |i':92:103|) |havoc:0:21:24|) 0)
               (or (not (<= (- |K:84:85:106|) 0))
                     (= (+ |k':77:86:107| |K:84:85:106| (- |k':77:104|)) 0))
               (or (not (<= (- |K:84:85:106|) 0))
                     (= (+ |j':78:87:108| (- |K:84:85:106|)) 0))
               (or (and (= |K:84:85:106| 0) (= (- |j':78:87:108|) 0)
                          (= (+ (- |k':77:86:107|) |k':77:104|) 0))
                     (and (<= (+ (- |K:84:85:106|) 1) 0)
                            (<= (+ (- |havoc:0:21:24|) 1) 0)
                            (<= (+ (- |k':77:104|) 1) 0)
                            (<= (+ |j':78:87:108| (- |havoc:0:21:24|)) 0)
                            (<= (- |k':77:86:107|) 0)
                            (<= (+ (- |j':78:87:108|) 1) 0)))
               (<= (- |K:84:85:106|) 0) (<= (- |j':78:87:108|) 0)
               (<= (- |k':77:86:107|) 0) (<= (- |havoc:0:21:24|) 0)
               (< (+ |j':78:87:108| (- |havoc:0:21:24|)) 0)
               (not (< (- |k':77:86:107|) 0))))
(check-sat)
