(declare-const |j':50:59| Int)
(declare-const |havoc:2| Int)
(declare-const havoc Int)
(declare-const |K:57:58| Int)
(declare-const |havoc:1| Int)
(assert (and (= (+ (- (ite (<= (- |havoc:1|) 0) (to_int (/ |havoc:1| 32))
                           (- (to_int (/ (- |havoc:1|) 32))))) havoc) 0)
               (or (not (<= (- |K:57:58|) 0))
                     (= (+ |j':50:59| (- |K:57:58|)) 0))
               (or (and (= |K:57:58| 0) (= (- |j':50:59|) 0))
                     (and (<= (+ (- |K:57:58|) 1) 0)
                            (<= (+ (- (to_int (* (/ 1 8) |havoc:1|))) 1) 0)
                            (<= (+ (- |havoc:2|) 1) 0) (<= (+ (- havoc) 1) 0)
                            (<= (+ (* -8 (to_int (* (/ 1 8) |havoc:1|)))
                                     |havoc:1| -7) 0)
                            (<= (+ (* 8 (to_int (* (/ 1 8) |havoc:1|)))
                                     (- |havoc:1|)) 0)
                            (<= (+ (- (to_int (* (/ 1 8) |havoc:1|)))
                                     |j':50:59|) 0)
                            (<= (+ (- |havoc:2|) |j':50:59|) 0)
                            (<= (+ (* -4
                                        (to_int (+ (* (/ 1 4) |j':50:59|)
                                                     (/ -1 4)))) |j':50:59|
                                     -4) 0)
                            (<= (+ (to_int (+ (* (/ 1 4) |j':50:59|) (/ -1 4)))
                                     (- havoc) 1) 0)
                            (<= (+ (* -8 (to_int (* (/ 1 8) |havoc:1|)))
                                     |havoc:1| -7) 0)
                            (<= (+ (* 8 (to_int (* (/ 1 8) |havoc:1|)))
                                     (- |havoc:1|)) 0)
                            (<= (- (to_int (+ (* (/ 1 4) |j':50:59|) (/ -1 4)))) 0)
                            (<= (+ (* 4
                                        (to_int (+ (* (/ 1 4) |j':50:59|)
                                                     (/ -1 4))))
                                     (- |j':50:59|) 1) 0)))
               (<= (- |K:57:58|) 0) (<= (- |j':50:59|) 0)
               (< (+ (- (ite (<= (- |havoc:1|) 0) (to_int (/ |havoc:1| 8))
                             (- (to_int (/ (- |havoc:1|) 8))))) |j':50:59|) 0)
               (< (+ (- |havoc:2|) |j':50:59|) 0) (not (<= (- |j':50:59|) 0))))
(check-sat)
