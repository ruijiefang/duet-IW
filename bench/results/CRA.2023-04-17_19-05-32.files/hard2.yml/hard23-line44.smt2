(declare-fun pow (Real Real) Real)
(declare-const |K:75| Int)
(declare-const |r':83:96| Int)
(declare-const havoc Int)
(declare-const |p':65| Int)
(declare-const |K:94:95| Int)
(declare-const |p':65:98| Int)
(declare-const |d':64:99| Int)
(declare-const |d':64| Int)
(declare-const |q':84:97| Int)
(assert (and (or (not (and (<= (- |K:75|) 0) (<= |K:75| 0)))
                   (= (+ (- (pow 2 |K:75|)) |d':64|) 0))
               (or (not (<= (+ (- |K:75|) 1) 0))
                     (= (+ (- (pow 2 |K:75|)) |d':64|) 0))
               (or (not (and (<= (- |K:75|) 0) (<= |K:75| 0)))
                     (= (+ |p':65| (- (pow 2 |K:75|))) 0))
               (or (not (<= (+ (- |K:75|) 1) 0))
                     (= (+ |p':65| (- (pow 2 |K:75|))) 0))
               (or (not (<= (- |K:75|) 0))
                     (<= (+ |p':65| (- (* havoc |K:75|)) -1) 0))
               (or (not (<= (- |K:75|) 0)) (<= (+ (- |p':65|) |K:75| 1) 0))
               (or (and (= |K:75| 0) (= (+ (- |p':65|) 1) 0)
                          (= (+ (- |d':64|) 1) 0))
                     (and (<= (+ (- |K:75|) 1) 0) (<= (+ (- havoc) 1) 0)
                            (= (+ (- |p':65|) |d':64|) 0)
                            (<= (+ (* -2 havoc) |p':65|) 0)
                            (<= (+ (- |p':65|) 2) 0))) (<= (- |K:75|) 0)
               (< (- |p':65|) 0) (< (- |d':64|) 0)
               (= (+ |p':65| (- |d':64|)) 0) (= (+ (- |p':65|) |d':64|) 0)
               (< (+ havoc (- |d':64|)) 0)
               (or (not (and (<= (- |K:94:95|) 0) (<= |K:94:95| 0)))
                     (= (+ |q':84:97| |r':83:96| (- havoc)) 0))
               (or (not (<= (+ (- |K:94:95|) 1) 0))
                     (= (+ |q':84:97| |r':83:96| (- havoc)) 0))
               (or (not (<= (- |K:94:95|) 0))
                     (<= (+ |p':65:98| |q':84:97| (- |p':65|)) 0))
               (or (not (<= (- |K:94:95|) 0))
                     (<= (+ |p':65:98| |K:94:95| (- |p':65|)) 0))
               (or (not (<= (- |K:94:95|) 0)) (<= (- |q':84:97|) 0))
               (or (and (= |K:94:95| 0) (= (- |q':84:97|) 0)
                          (= (+ (- |p':65:98|) |p':65|) 0)
                          (= (+ (- |d':64:99|) |d':64|) 0)
                          (= (+ (- |r':83:96|) havoc) 0))
                     (and (<= (+ (- |K:94:95|) 1) 0)
                            (= (+ |p':65| (- |d':64|)) 0)
                            (= (+ |p':65| (- |d':64|)) 0)
                            (= (+ (to_int (* (/ 1 2) |p':65|))
                                    (- (to_int (* (/ 1 2) |d':64|)))) 0)
                            (<= (+ (* -2 (to_int (* (/ 1 2) |d':64|)))
                                     |d':64| -1) 0)
                            (<= (+ (- (to_int (* (/ 1 2) |d':64|))) 1) 0)
                            (<= (+ (* 2 (to_int (* (/ 1 2) |d':64|)))
                                     (- |d':64|)) 0)
                            (= (+ (- |q':84:97|) (- |r':83:96|) havoc) 0)
                            (= (+ |d':64:99| (- |p':65:98|)) 0)
                            (= (+ |q':84:97| |r':83:96| (- havoc)) 0)
                            (<= (+ (- |q':84:97|) (- |r':83:96|) havoc) 0)
                            (<= (+ (- |q':84:97|) (- |r':83:96|) havoc) 0)
                            (<= (+ (- |p':65:98|) 1) 0) (<= (- |q':84:97|) 0)))
               (<= (- |K:94:95|) 0) (< (- |p':65:98|) 0) (< (- |d':64:99|) 0)
               (<= (- |q':84:97|) 0)
               (= (+ |q':84:97| |r':83:96| (- havoc)) 0)
               (= (+ (- |d':64:99|) |p':65:98|) 0)
               (not (= (+ (- |q':84:97|) (- |r':83:96|) havoc) 0))))
(check-sat)
