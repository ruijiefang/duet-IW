(declare-const |z':66| Int)
(declare-const |y':65| Int)
(declare-const |K:80| Int)
(declare-const |x':64| Int)
(declare-const havoc Int)
(declare-const |n':63| Int)
(assert (and (or (not (and (<= (- |K:80|) 0) (<= |K:80| 0)))
                   (= (+ |n':63| (- |K:80|)) 0))
               (or (not (<= (+ (- |K:80|) 1) 0)) (= (+ |n':63| (- |K:80|)) 0))
               (or (not (and (<= (- |K:80|) 0) (<= |K:80| 0)))
                     (= (+ |z':66| (* -6 |K:80|) -6) 0))
               (or (not (<= (+ (- |K:80|) 1) 0))
                     (= (+ |z':66| (* -6 |K:80|) -6) 0))
               (or (not (<= (- |K:80|) 0))
                     (= (+ |y':65| (* -3 (* |K:80| |K:80|)) (* -3 |K:80|) -1) 0))
               (or (not (<= (- |K:80|) 0))
                     (= (+ |x':64| (- (* |K:80| (* |K:80| |K:80|)))) 0))
               (or (and (= |K:80| 0) (= (+ (- |z':66|) 6) 0)
                          (= (+ (- |y':65|) 1) 0) (= (- |x':64|) 0)
                          (= (- |n':63|) 0))
                     (and (<= (+ (- |K:80|) 1) 0) (<= (- havoc) 0)
                            (= (+ (* 12 |y':65|) (- (* |z':66| |z':66|))
                                    (* 6 |z':66|) -12) 0)
                            (= (+ (* -18 |x':64|) (* -12 |y':65|)
                                    (* |y':65| |z':66|) (* 2 |z':66|) -6) 0)
                            (= (+ (* -36 |x':64|) (* -12 |y':65|)
                                    (- (* |z':66| |z':66|))
                                    (* 2 (* |y':65| |z':66|)) (* 10 |z':66|)
                                    -24) 0)
                            (= (+ (- |z':66|) (* 6 |n':63|) 6) 0)
                            (<= (+ (* 18 |x':64|) (* 12 |y':65|)
                                     (- (* |y':65| |z':66|)) (* -2 |z':66|) 6) 0)
                            (<= (+ (- (* |z':66| |z':66|)) (* 24 |z':66|)
                                     -144) 0)
                            (<= (+ (* 18 |x':64|) (* 12 |y':65|)
                                     (- (* |y':65| |z':66|)) (* -2 |z':66|) 6) 0)
                            (<= (+ (* 36 |x':64|) (* 12 |y':65|)
                                     (* |z':66| |z':66|)
                                     (* -2 (* |y':65| |z':66|))
                                     (* -10 |z':66|) 24) 0)
                            (<= (+ (* 36 |x':64|) (* 12 |y':65|)
                                     (* |z':66| |z':66|)
                                     (* -2 (* |y':65| |z':66|))
                                     (* -10 |z':66|) 24) 0)
                            (<= (+ (* -6 havoc) |z':66| -12) 0)
                            (<= (+ (* 36 |x':64|) (* 12 |y':65|)
                                     (* |z':66| |z':66|)
                                     (* -2 (* |y':65| |z':66|))
                                     (* -10 |z':66|) 24) 0)
                            (<= (+ (- |z':66|) 12) 0)
                            (<= (+ (* -12 |x':64|) (* |z':66| |z':66|)
                                     (* -18 |z':66|) 84) 0)))
               (<= (- |K:80|) 0) (<= (- |x':64|) 0) (< (- |y':65|) 0)
               (<= (- |n':63|) 0) (< (- |z':66|) 0)
               (= (+ (- |z':66|) (* 6 |n':63|) 6) 0)
               (= (+ |z':66| (* -6 |n':63|) -6) 0)
               (= (+ |y':65| (* -3 (* |n':63| |n':63|)) (* -3 |n':63|) -1) 0)
               (= (+ |x':64| (- (* |n':63| (* |n':63| |n':63|)))) 0)
               (= (+ (* -18 |x':64|) (* -12 |y':65|) (* |y':65| |z':66|)
                       (* 2 |z':66|) -6) 0)
               (= (+ (* -12 |y':65|) (* |z':66| |z':66|) (* -6 |z':66|) 12) 0)
               (< (+ havoc (- |n':63|)) 0)
               (= (+ |z':66| (* -6 |n':63|) -6) 0)
               (= (+ (* 6 (* havoc |x':64|)) (* 12 |x':64|)
                       (- (* |x':64| |z':66|))) 0)
               (= (+ (* -6 havoc) (* -2 |y':65|) (* havoc |z':66|)
                       (* 2 |z':66|) -10) 0)
               (not (= (+ (* -18 |x':64|) (* 2 (* |y':65| |y':65|))
                            (* -10 |y':65|) (* -3 (* |x':64| |z':66|))
                            (* 3 |z':66|) -10) 0))))
(check-sat)
