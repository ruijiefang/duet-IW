(declare-const |y':72:85| Int)
(declare-const |x':71:86| Int)
(declare-const |c':73:84| Int)
(declare-const havoc Int)
(declare-const |havoc:1| Int)
(declare-const |K:82:83| Int)
(assert (and (not (= (ite (<= (+ (- havoc) 1) 0) 1 0) 0))
               (not (= (ite (<= (+ (- |havoc:1|) 1) 0) 1 0) 0))
               (or (not (<= (- |K:82:83|) 0))
                     (= (+ |c':73:84| (- |K:82:83|) -1) 0))
               (or (and (= |K:82:83| 0) (= (+ (- |c':73:84|) 1) 0)
                          (= (+ (- |y':72:85|) havoc) 0)
                          (= (+ (- |x':71:86|) 1) 0))
                     (and (<= (+ (- |K:82:83|) 1) 0)
                            (<= (+ (- |havoc:1|) 2) 0)
                            (<= (+ |c':73:84| (- |havoc:1|)) 0)
                            (<= (+ (- |c':73:84|) 2) 0)))
               (<= (- |K:82:83|) 0) (< (- |c':73:84|) 0)
               (not (= (+ (- |x':71:86|) (- |y':72:85|) (* |x':71:86| havoc)
                            1) 0))))
(check-sat)
