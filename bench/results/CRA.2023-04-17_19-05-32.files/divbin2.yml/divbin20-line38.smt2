(declare-const |b':62:73| Int)
(declare-const havoc Int)
(declare-const |r':61:71| Int)
(declare-const |b':62| Int)
(declare-const |K:77| Int)
(declare-const |q':60:72| Int)
(declare-fun pow (Real Real) Real)
(declare-const |K:69:70| Int)
(assert (and (<= (- havoc) 0)
               (or (not (<= (- |K:77|) 0))
                     (= (+ (- (pow 2 |K:77|)) |b':62|) 0))
               (or (not (<= (- |K:77|) 0))
                     (<= (+ |b':62| (- (* |K:77| havoc)) -1) 0))
               (or (not (<= (- |K:77|) 0)) (<= (+ (- |b':62|) |K:77| 1) 0))
               (or (and (= |K:77| 0) (= (+ (- |b':62|) 1) 0))
                     (and (<= (+ (- |K:77|) 1) 0) (<= (+ (- havoc) 1) 0)
                            (<= (+ |b':62| (* -2 havoc)) 0)
                            (<= (+ (- |b':62|) 2) 0))) (<= (- |K:77|) 0)
               (< (- |b':62|) 0) (<= (- havoc) 0) (< (+ (- |b':62|) havoc) 0)
               (or (not (<= (- |K:69:70|) 0)) (<= (+ |r':61:71| (- havoc)) 0))
               (or (not (<= (- |K:69:70|) 0))
                     (<= (+ (* 2 |q':60:72|) |r':61:71|
                              (- (* |K:69:70| havoc)) (- havoc)) 0))
               (or (not (<= (- |K:69:70|) 0))
                     (<= (+ |b':62:73| |K:69:70| (- |b':62|)) 0))
               (or (not (<= (- |K:69:70|) 0)) (<= (- |q':60:72|) 0))
               (or (not (<= (- |K:69:70|) 0))
                     (<= (+ |b':62:73| (- |r':61:71|) (- |b':62|) havoc) 0))
               (or (not (<= (- |K:69:70|) 0))
                     (<= (+ |b':62:73| (- |q':60:72|) (- |r':61:71|)
                              |K:69:70| (- |b':62|) havoc) 0))
               (or (not (<= (- |K:69:70|) 0))
                     (<= (+ (* 2 |q':60:72|) (- |r':61:71|) (* -2 |K:69:70|)
                              (- (* |K:69:70| havoc)) havoc) 0))
               (or (not (<= (- |K:69:70|) 0))
                     (<= (+ (- |r':61:71|) (- (* |K:69:70| havoc)) havoc) 0))
               (or (and (= |K:69:70| 0) (= (+ (- |b':62:73|) |b':62|) 0)
                          (= (+ (- |r':61:71|) havoc) 0) (= (- |q':60:72|) 0))
                     (and (<= (+ (- |K:69:70|) 1) 0)
                            (<= (+ (- (* |b':62| havoc)) (* 2 havoc)) 0)
                            (<= (+ (- (* |b':62| havoc)) (* 2 havoc)) 0)
                            (<= (+ (* -2 (to_int (* (/ 1 2) |b':62|)))
                                     |b':62| -1) 0)
                            (<= (+ (- (to_int (* (/ 1 2) |b':62|))) 1) 0)
                            (<= (+ (* 2 (to_int (* (/ 1 2) |b':62|)))
                                     (- |b':62|)) 0) (<= (- havoc) 0)
                            (<= (+ |q':60:72| |r':61:71| (- havoc)) 0)
                            (<= (+ (- |b':62:73|) 1) 0) (<= (- |r':61:71|) 0)
                            (<= (- |q':60:72|) 0))) (<= (- |K:69:70|) 0)
               (<= (- |q':60:72|) 0) (< (- |b':62:73|) 0)
               (<= (- |r':61:71|) 0) (<= (- havoc) 0)
               (not (= (+ (- (* |b':62:73| |q':60:72|)) (- |r':61:71|) havoc) 0))))
(check-sat)
