(declare-const |c':52| Int)
(declare-const |x':51| Int)
(declare-const |K:63| Int)
(declare-const |y':50| Int)
(declare-const havoc Int)
(assert (and (or (not (and (<= (- |K:63|) 0) (<= |K:63| 0)))
                   (= (+ |y':50| (- |K:63|)) 0))
               (or (not (<= (+ (- |K:63|) 1) 0)) (= (+ |y':50| (- |K:63|)) 0))
               (or (not (and (<= (- |K:63|) 0) (<= |K:63| 0)))
                     (= (+ |c':52| (- |K:63|)) 0))
               (or (not (<= (+ (- |K:63|) 1) 0)) (= (+ |c':52| (- |K:63|)) 0))
               (or (not (and (<= (- |K:63|) 0) (<= |K:63| 0)))
                     (= (+ (* 4 |x':51|)
                             (- (* (* |K:63| |K:63|) (* |K:63| |K:63|)))
                             (* -2 (* |K:63| (* |K:63| |K:63|)))
                             (- (* |K:63| |K:63|))) 0))
               (or (not (and (<= (+ (- |K:63|) 1) 0) (<= (+ |K:63| -1) 0)))
                     (= (+ (* 4 |x':51|)
                             (- (* (* |K:63| |K:63|) (* |K:63| |K:63|)))
                             (* -2 (* |K:63| (* |K:63| |K:63|)))
                             (- (* |K:63| |K:63|))) 0))
               (or (not (and (<= (+ (- |K:63|) 2) 0) (<= (+ |K:63| -2) 0)))
                     (= (+ (* 4 |x':51|)
                             (- (* (* |K:63| |K:63|) (* |K:63| |K:63|)))
                             (* -2 (* |K:63| (* |K:63| |K:63|)))
                             (- (* |K:63| |K:63|))) 0))
               (or (not (and (<= (+ (- |K:63|) 3) 0) (<= (+ |K:63| -3) 0)))
                     (= (+ (* 4 |x':51|)
                             (- (* (* |K:63| |K:63|) (* |K:63| |K:63|)))
                             (* -2 (* |K:63| (* |K:63| |K:63|)))
                             (- (* |K:63| |K:63|))) 0))
               (or (not (and (<= (+ (- |K:63|) 4) 0) (<= (+ |K:63| -4) 0)))
                     (= (+ (* 4 |x':51|)
                             (- (* (* |K:63| |K:63|) (* |K:63| |K:63|)))
                             (* -2 (* |K:63| (* |K:63| |K:63|)))
                             (- (* |K:63| |K:63|))) 0))
               (or (not (<= (+ (- |K:63|) 5) 0))
                     (= (+ (* 4 |x':51|)
                             (- (* (* |K:63| |K:63|) (* |K:63| |K:63|)))
                             (* -2 (* |K:63| (* |K:63| |K:63|)))
                             (- (* |K:63| |K:63|))) 0))
               (or (not (and (<= (- |K:63|) 0) (<= |K:63| 0)))
                     (<= (+ (* 4 |x':51|)
                              (- (* (* |K:63| |K:63|) (* |K:63| |K:63|)))
                              (* -2 (* |K:63| (* |K:63| |K:63|)))
                              (- (* |K:63| |K:63|))) 0))
               (or (not (and (<= (+ (- |K:63|) 1) 0) (<= (+ |K:63| -1) 0)))
                     (<= (+ (* 4 |x':51|)
                              (- (* (* |K:63| |K:63|) (* |K:63| |K:63|)))
                              (* -2 (* |K:63| (* |K:63| |K:63|)))
                              (- (* |K:63| |K:63|))) 0))
               (or (not (and (<= (+ (- |K:63|) 2) 0) (<= (+ |K:63| -2) 0)))
                     (<= (+ (* 4 |x':51|)
                              (- (* (* |K:63| |K:63|) (* |K:63| |K:63|)))
                              (* -2 (* |K:63| (* |K:63| |K:63|)))
                              (- (* |K:63| |K:63|))) 0))
               (or (not (<= (+ (- |K:63|) 3) 0))
                     (<= (+ (* 4 |x':51|)
                              (- (* (* |K:63| |K:63|) (* |K:63| |K:63|)))
                              (* -2 (* |K:63| (* |K:63| |K:63|)))
                              (- (* |K:63| |K:63|))) 0))
               (or (not (and (<= (- |K:63|) 0) (<= |K:63| 0)))
                     (<= (+ (- |x':51|) (* |K:63| (* |K:63| |K:63|))) 0))
               (or (not (and (<= (+ (- |K:63|) 1) 0) (<= (+ |K:63| -1) 0)))
                     (<= (+ (- |x':51|) (* |K:63| (* |K:63| |K:63|))) 0))
               (or (not (<= (+ (- |K:63|) 2) 0))
                     (<= (+ (- |x':51|) (* |K:63| (* |K:63| |K:63|))) 0))
               (or (and (= |K:63| 0) (= (- |c':52|) 0) (= (- |x':51|) 0)
                          (= (- |y':50|) 0))
                     (and (<= (+ (- |K:63|) 1) 0) (<= (+ (- havoc) 1) 0)
                            (= (+ |c':52| (- |y':50|)) 0)
                            (= (+ (* -4 |x':51|)
                                    (* (* |y':50| |y':50|)
                                         (* |y':50| |y':50|))
                                    (* 2 (* |y':50| (* |y':50| |y':50|)))
                                    (* |y':50| |y':50|)) 0)
                            (<= (+ (* -4 |x':51|)
                                     (* (* |y':50| |y':50|)
                                          (* |y':50| |y':50|))
                                     (* -4 (* |y':50| (* |y':50| |y':50|)))
                                     (* 19 (* |y':50| |y':50|))
                                     (* -18 |y':50|) 6) 0)
                            (<= (+ (- havoc) |y':50|) 0)
                            (<= (+ (- (* (* |y':50| |y':50|)
                                           (* |y':50| |y':50|)))
                                     (* 4 (* |y':50| (* |y':50| |y':50|)))
                                     (* -6 (* |y':50| |y':50|)) (* 4 |y':50|)
                                     -1) 0)
                            (<= (+ (- (* (* |y':50| |y':50|)
                                           (* |y':50| |y':50|)))
                                     (* 4 (* |y':50| (* |y':50| |y':50|)))
                                     (* -6 (* |y':50| |y':50|)) (* 4 |y':50|)
                                     -1) 0)
                            (<= (+ (- (* |y':50| |y':50|)) (* 2 |y':50|) -1) 0)
                            (<= (+ (- |y':50|) 1) 0)
                            (<= (+ (* 4 |x':51|)
                                     (- (* (* |y':50| |y':50|)
                                             (* |y':50| |y':50|)))
                                     (* -2 (* |y':50| (* |y':50| |y':50|)))
                                     (- (* |y':50| |y':50|))) 0)))
               (<= (- |K:63|) 0) (<= (- |c':52|) 0) (<= (- |y':50|) 0)
               (= (+ |c':52| (- |y':50|)) 0)
               (= (+ (* 4 |x':51|)
                       (- (* (* |y':50| |y':50|) (* |y':50| |y':50|)))
                       (* -2 (* |y':50| (* |y':50| |y':50|)))
                       (- (* |y':50| |y':50|))) 0)
               (<= (+ havoc (- |c':52|)) 0)
               (= (+ (- (* |y':50| |y':50|)) (* havoc |y':50|)) 0)
               (not (= (+ (* 4 |x':51|)
                            (- (* (* |y':50| |y':50|) (* |y':50| |y':50|)))
                            (* -2 (* |y':50| (* |y':50| |y':50|)))
                            (- (* |y':50| |y':50|))) 0))))
(check-sat)
