(declare-const |K:85| Int)
(declare-const |xy':71| Int)
(declare-const |y':69| Int)
(declare-const |yx':72| Int)
(declare-const havoc Int)
(declare-const |x':68| Int)
(declare-const |v':70| Int)
(declare-const xy Int)
(declare-const yx Int)
(declare-const |havoc:1| Int)
(assert (and (or (not (<= (- |K:85|) 0)) (= (+ |x':68| (- |K:85|)) 0))
               (or (not (and (<= (- |K:85|) 0) (<= |K:85| 0)))
                     (= (+ (- yx) |yx':72| (- (* |havoc:1| |K:85|))) 0))
               (or (not (<= (+ (- |K:85|) 1) 0))
                     (= (+ |havoc:1| |yx':72| (- (* |havoc:1| |K:85|))) 0))
               (or (not (<= (- |K:85|) 0))
                     (<= (+ (- havoc) (- |v':70|) (* 2 |havoc:1|)
                              (* -2 (* havoc |K:85|))
                              (* 2 (* |havoc:1| |K:85|))) 0))
               (or (not (<= (- |K:85|) 0)) (<= (+ |y':69| (- |K:85|)) 0))
               (or (not (<= (- |K:85|) 0)) (<= (- |y':69|) 0))
               (or (not (<= (- |K:85|) 0))
                     (<= (+ havoc |v':70| (* -2 |havoc:1|)
                              (* -2 (* |havoc:1| |K:85|))) 0))
               (or (and (= |K:85| 0) (= (+ yx (- |yx':72|)) 0)
                          (= (+ (- |xy':71|) xy) 0)
                          (= (+ (- havoc) (- |v':70|) (* 2 |havoc:1|)) 0)
                          (= (- |y':69|) 0) (= (- |x':68|) 0))
                     (and (<= (+ (- |K:85|) 1) 0) (<= (- havoc) 0)
                            (= (+ |havoc:1| |yx':72|
                                    (- (* |havoc:1| |x':68|))) 0)
                            (<= (+ (* -2 |xy':71|) (* -3 havoc) (- |v':70|)
                                     (* 2 |havoc:1|)
                                     (* 2 (* |havoc:1| |x':68|))) 0)
                            (<= (+ (- havoc) |x':68| -1) 0)
                            (<= (+ |xy':71| (- (* |y':69| havoc))) 0)
                            (<= (- |y':69|) 0) (<= (- |xy':71|) 0)
                            (<= (+ (- |x':68|) 1) 0)
                            (<= (+ |xy':71| (- (* |y':69| havoc))) 0)
                            (<= (+ (* 2 |xy':71|) havoc |v':70|
                                     (* -2 |havoc:1|)
                                     (* -2 (* |havoc:1| |x':68|))) 0)))
               (<= (- |K:85|) 0) (<= (- |y':69|) 0) (<= (- |x':68|) 0)
               (not (= (+ (* -2 (* |y':69| havoc)) (- havoc) (- |v':70|)
                            (* 2 |havoc:1|) (* 2 (* |havoc:1| |x':68|))) 0))))
(check-sat)
