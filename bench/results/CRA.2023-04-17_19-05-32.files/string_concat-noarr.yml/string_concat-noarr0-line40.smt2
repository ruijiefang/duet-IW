(declare-const tmp Int)
(declare-const |tmp':69| Int)
(declare-const tmp___0 Int)
(declare-const |K:73| Int)
(declare-const |tmp___0':56:66| Int)
(declare-const |i':54:64| Int)
(declare-const |K:62:63| Int)
(declare-const |i':54| Int)
(declare-const |havoc:3:53:67| Int)
(declare-const |havoc:0:68| Int)
(declare-const |j':55:65| Int)
(assert (and (or (not (<= (- |K:73|) 0)) (= (+ |i':54| (- |K:73|)) 0))
               (or (and (= |K:73| 0) (= (+ (- |tmp':69|) tmp) 0)
                          (= (- |i':54|) 0))
                     (and (<= (+ (- |K:73|) 1) 0) (<= (+ |i':54| -1000000) 0)
                            (<= (+ (- |i':54|) 1) 0))) (<= (- |K:73|) 0)
               (<= (- |i':54|) 0)
               (or (= |havoc:0:68| 0)
                     (and (not (= |havoc:0:68| 0))
                            (<= (+ (- |i':54|) 1000000) 0)))
               (< (+ |i':54| -100) 0)
               (or (not (<= (- |K:62:63|) 0))
                     (= (+ |i':54:64| (- |K:62:63|) (- |i':54|)) 0))
               (or (not (<= (- |K:62:63|) 0))
                     (= (+ |j':55:65| (- |K:62:63|)) 0))
               (or (and (= |K:62:63| 0)
                          (= (+ (- |tmp___0':56:66|) tmp___0) 0)
                          (= (- |j':55:65|) 0)
                          (= (+ (- |i':54:64|) |i':54|) 0))
                     (and (<= (+ (- |K:62:63|) 1) 0)
                            (<= (+ |i':54| -999999) 0) (<= (- |i':54|) 0)
                            (<= (+ |i':54:64| -1000000) 0)
                            (<= (+ (- |j':55:65|) 1) 0)
                            (<= (+ (- |i':54:64|) 1) 0)))
               (<= (- |K:62:63|) 0) (<= (- |j':55:65|) 0)
               (<= (- |i':54:64|) 0)
               (or (= |havoc:3:53:67| 0)
                     (and (not (= |havoc:3:53:67| 0))
                            (<= (+ (- |i':54:64|) 1000000) 0)))
               (< (+ |j':55:65| -100) 0) (not (< (+ |i':54:64| -200) 0))))
(check-sat)
