(declare-const |x':51| Int)
(declare-const |c':52| Int)
(declare-const |y':50| Int)
(declare-const |K:62| Int)
(declare-const havoc Int)
(assert (and (or (not (and (<= (- |K:62|) 0) (<= |K:62| 0)))
                   (= (+ |c':52| (- |K:62|)) 0))
               (or (not (<= (+ (- |K:62|) 1) 0)) (= (+ |c':52| (- |K:62|)) 0))
               (or (not (and (<= (- |K:62|) 0) (<= |K:62| 0)))
                     (= (+ |y':50| (- |K:62|)) 0))
               (or (not (<= (+ (- |K:62|) 1) 0)) (= (+ |y':50| (- |K:62|)) 0))
               (or (not (and (<= (- |K:62|) 0) (<= |K:62| 0)))
                     (= (+ (* 6 |x':51|) (* -2 (* |K:62| (* |K:62| |K:62|)))
                             (* -3 (* |K:62| |K:62|)) (- |K:62|)) 0))
               (or (not (and (<= (+ (- |K:62|) 1) 0) (<= (+ |K:62| -1) 0)))
                     (= (+ (* 6 |x':51|) (* -2 (* |K:62| (* |K:62| |K:62|)))
                             (* -3 (* |K:62| |K:62|)) (- |K:62|)) 0))
               (or (not (and (<= (+ (- |K:62|) 2) 0) (<= (+ |K:62| -2) 0)))
                     (= (+ (* 6 |x':51|) (* -2 (* |K:62| (* |K:62| |K:62|)))
                             (* -3 (* |K:62| |K:62|)) (- |K:62|)) 0))
               (or (not (and (<= (+ (- |K:62|) 3) 0) (<= (+ |K:62| -3) 0)))
                     (= (+ (* 6 |x':51|) (* -2 (* |K:62| (* |K:62| |K:62|)))
                             (* -3 (* |K:62| |K:62|)) (- |K:62|)) 0))
               (or (not (<= (+ (- |K:62|) 4) 0))
                     (= (+ (* 6 |x':51|) (* -2 (* |K:62| (* |K:62| |K:62|)))
                             (* -3 (* |K:62| |K:62|)) (- |K:62|)) 0))
               (or (not (and (<= (- |K:62|) 0) (<= |K:62| 0)))
                     (<= (+ (* 10 |x':51|)
                              (* -4
                                   (* |K:62|
                                        (* (* |K:62| |K:62|)
                                             (* |K:62| |K:62|))))
                              (* 10 (* (* |K:62| |K:62|) (* |K:62| |K:62|)))
                              (* -10 (* |K:62| (* |K:62| |K:62|)))
                              (* -5 (* |K:62| |K:62|)) (- |K:62|)) 0))
               (or (not (and (<= (+ (- |K:62|) 1) 0) (<= (+ |K:62| -1) 0)))
                     (<= (+ (* 10 |x':51|)
                              (* -4
                                   (* |K:62|
                                        (* (* |K:62| |K:62|)
                                             (* |K:62| |K:62|))))
                              (* 10 (* (* |K:62| |K:62|) (* |K:62| |K:62|)))
                              (* -10 (* |K:62| (* |K:62| |K:62|)))
                              (* -5 (* |K:62| |K:62|)) (- |K:62|)) 0))
               (or (not (and (<= (+ (- |K:62|) 2) 0) (<= (+ |K:62| -2) 0)))
                     (<= (+ (* 10 |x':51|)
                              (* -4
                                   (* |K:62|
                                        (* (* |K:62| |K:62|)
                                             (* |K:62| |K:62|))))
                              (* 10 (* (* |K:62| |K:62|) (* |K:62| |K:62|)))
                              (* -10 (* |K:62| (* |K:62| |K:62|)))
                              (* -5 (* |K:62| |K:62|)) (- |K:62|)) 0))
               (or (not (and (<= (+ (- |K:62|) 3) 0) (<= (+ |K:62| -3) 0)))
                     (<= (+ (* 10 |x':51|)
                              (* -4
                                   (* |K:62|
                                        (* (* |K:62| |K:62|)
                                             (* |K:62| |K:62|))))
                              (* 10 (* (* |K:62| |K:62|) (* |K:62| |K:62|)))
                              (* -10 (* |K:62| (* |K:62| |K:62|)))
                              (* -5 (* |K:62| |K:62|)) (- |K:62|)) 0))
               (or (not (and (<= (+ (- |K:62|) 4) 0) (<= (+ |K:62| -4) 0)))
                     (<= (+ (* 10 |x':51|)
                              (* -4
                                   (* |K:62|
                                        (* (* |K:62| |K:62|)
                                             (* |K:62| |K:62|))))
                              (* 10 (* (* |K:62| |K:62|) (* |K:62| |K:62|)))
                              (* -10 (* |K:62| (* |K:62| |K:62|)))
                              (* -5 (* |K:62| |K:62|)) (- |K:62|)) 0))
               (or (not (<= (+ (- |K:62|) 5) 0))
                     (<= (+ (* 10 |x':51|)
                              (* -4
                                   (* |K:62|
                                        (* (* |K:62| |K:62|)
                                             (* |K:62| |K:62|))))
                              (* 10 (* (* |K:62| |K:62|) (* |K:62| |K:62|)))
                              (* -10 (* |K:62| (* |K:62| |K:62|)))
                              (* -5 (* |K:62| |K:62|)) (- |K:62|)) 0))
               (or (not (and (<= (- |K:62|) 0) (<= |K:62| 0)))
                     (<= (+ (* 20 |x':51|)
                              (* -8
                                   (* |K:62|
                                        (* (* |K:62| |K:62|)
                                             (* |K:62| |K:62|))))
                              (* 5 (* (* |K:62| |K:62|) (* |K:62| |K:62|)))
                              (* 10 (* |K:62| (* |K:62| |K:62|)))
                              (* -25 (* |K:62| |K:62|)) (* -2 |K:62|)) 0))
               (or (not (and (<= (+ (- |K:62|) 1) 0) (<= (+ |K:62| -1) 0)))
                     (<= (+ (* 20 |x':51|)
                              (* -8
                                   (* |K:62|
                                        (* (* |K:62| |K:62|)
                                             (* |K:62| |K:62|))))
                              (* 5 (* (* |K:62| |K:62|) (* |K:62| |K:62|)))
                              (* 10 (* |K:62| (* |K:62| |K:62|)))
                              (* -25 (* |K:62| |K:62|)) (* -2 |K:62|)) 0))
               (or (not (and (<= (+ (- |K:62|) 2) 0) (<= (+ |K:62| -2) 0)))
                     (<= (+ (* 20 |x':51|)
                              (* -8
                                   (* |K:62|
                                        (* (* |K:62| |K:62|)
                                             (* |K:62| |K:62|))))
                              (* 5 (* (* |K:62| |K:62|) (* |K:62| |K:62|)))
                              (* 10 (* |K:62| (* |K:62| |K:62|)))
                              (* -25 (* |K:62| |K:62|)) (* -2 |K:62|)) 0))
               (or (not (and (<= (+ (- |K:62|) 3) 0) (<= (+ |K:62| -3) 0)))
                     (<= (+ (* 20 |x':51|)
                              (* -8
                                   (* |K:62|
                                        (* (* |K:62| |K:62|)
                                             (* |K:62| |K:62|))))
                              (* 5 (* (* |K:62| |K:62|) (* |K:62| |K:62|)))
                              (* 10 (* |K:62| (* |K:62| |K:62|)))
                              (* -25 (* |K:62| |K:62|)) (* -2 |K:62|)) 0))
               (or (not (and (<= (+ (- |K:62|) 4) 0) (<= (+ |K:62| -4) 0)))
                     (<= (+ (* 20 |x':51|)
                              (* -8
                                   (* |K:62|
                                        (* (* |K:62| |K:62|)
                                             (* |K:62| |K:62|))))
                              (* 5 (* (* |K:62| |K:62|) (* |K:62| |K:62|)))
                              (* 10 (* |K:62| (* |K:62| |K:62|)))
                              (* -25 (* |K:62| |K:62|)) (* -2 |K:62|)) 0))
               (or (not (<= (+ (- |K:62|) 5) 0))
                     (<= (+ (* 20 |x':51|)
                              (* -8
                                   (* |K:62|
                                        (* (* |K:62| |K:62|)
                                             (* |K:62| |K:62|))))
                              (* 5 (* (* |K:62| |K:62|) (* |K:62| |K:62|)))
                              (* 10 (* |K:62| (* |K:62| |K:62|)))
                              (* -25 (* |K:62| |K:62|)) (* -2 |K:62|)) 0))
               (or (not (and (<= (- |K:62|) 0) (<= |K:62| 0)))
                     (<= (+ (- |x':51|) (* |K:62| |K:62|)) 0))
               (or (not (<= (+ (- |K:62|) 1) 0))
                     (<= (+ (- |x':51|) (* |K:62| |K:62|)) 0))
               (or (and (= |K:62| 0) (= (- |c':52|) 0) (= (- |x':51|) 0)
                          (= (- |y':50|) 0))
                     (and (<= (+ (- |K:62|) 1) 0) (<= (+ (- havoc) 1) 0)
                            (= (+ (- |y':50|) |c':52|) 0)
                            (= (+ (* -6 |x':51|)
                                    (* 2 (* |y':50| (* |y':50| |y':50|)))
                                    (* 3 (* |y':50| |y':50|)) |y':50|) 0)
                            (<= (+ (* -6 |x':51|) (* 9 (* |y':50| |y':50|))
                                     (* -5 |y':50|) 2) 0)
                            (<= (+ (- havoc) |y':50|) 0)
                            (<= (+ (* 6 |x':51|)
                                     (* 6 (* |y':50| (* |y':50| |y':50|)))
                                     (* -5 (* |y':50| |y':50|))
                                     (* -6 (* |x':51| |y':50|))
                                     (* -2 |y':50|) 1) 0)
                            (<= (+ (- (* |y':50| |y':50|)) (* 2 |y':50|) -1) 0)
                            (<= (+ (- |y':50|) 1) 0)
                            (<= (+ (* 6 |x':51|)
                                     (* -2 (* |y':50| (* |y':50| |y':50|)))
                                     (* -3 (* |y':50| |y':50|)) (- |y':50|)) 0)
                            (<= (+ (* 30 |x':51|)
                                     (* 12 (* |y':50| (* |y':50| |y':50|)))
                                     (* -37 (* |y':50| |y':50|))
                                     (* -12 (* |x':51| |y':50|))
                                     (* 11 |y':50|) -4) 0)))
               (<= (- |K:62|) 0) (<= (- |c':52|) 0) (<= (- |y':50|) 0)
               (= (+ (- |y':50|) |c':52|) 0)
               (not (= (+ (* 6 |x':51|)
                            (* -2 (* |y':50| (* |y':50| |y':50|)))
                            (* -3 (* |y':50| |y':50|)) (- |y':50|)) 0))))
(check-sat)
