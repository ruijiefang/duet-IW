(declare-const |tmp___0':69| Int)
(declare-const havoc Int)
(declare-const |havoc:3:63| Int)
(declare-const tmp___0 Int)
(declare-const |phi_i:14| Int)
(declare-const |j':66| Int)
(declare-const |a':67| Int)
(declare-const |K:77| Int)
(declare-const |b':68| Int)
(declare-const |i':65| Int)
(assert (and (or (and (= havoc 0) (= (+ (- |phi_i:14|) 1) 0))
                   (and (not (= havoc 0)) (= (- |phi_i:14|) 0)))
               (or (not (<= (- |K:77|) 0)) (= (+ |a':67| (- |K:77|)) 0))
               (or (not (<= (- |K:77|) 0))
                     (= (+ |i':65| (* -2 |K:77|) (- |phi_i:14|)) 0))
               (or (not (<= (- |K:77|) 0))
                     (<= (+ |j':66| (* -2 |K:77|) -1) 0))
               (or (not (<= (- |K:77|) 0))
                     (<= (+ (- |b':68|) (- (* |K:77| |K:77|)) (* 2 |K:77|)
                              (- (* |K:77| |phi_i:14|))) 0))
               (or (not (<= (- |K:77|) 0)) (<= (+ (- |j':66|) |K:77| 1) 0))
               (or (and (= |K:77| 0) (= (+ (- |tmp___0':69|) tmp___0) 0)
                          (= (- |b':68|) 0) (= (- |a':67|) 0)
                          (= (+ (- |j':66|) 1) 0)
                          (= (+ (- |i':65|) |phi_i:14|) 0))
                     (and (<= (+ (- |K:77|) 1) 0)
                            (<= (+ (mod (+ |phi_i:14| 2) 2) -1) 0)
                            (<= (- (mod (+ |phi_i:14| 2) 2)) 0)
                            (<= (- |phi_i:14|) 0)
                            (<= (+ (mod |i':65| 2) -1) 0)
                            (<= (+ (- |a':67|) 1) 0)
                            (<= (- (mod |i':65| 2)) 0)
                            (<= (+ (- (mod |i':65| 2)) (- |j':66|) 3) 0)
                            (<= (+ (- |i':65|) 2) 0))) (<= (- |K:77|) 0)
               (< (- |j':66|) 0) (<= (- |i':65|) 0) (<= (- |a':67|) 0)
               (= |havoc:3:63| 0) (not (= havoc 0))
               (not (= (+ (- |b':68|) |a':67|) 0))))
(check-sat)