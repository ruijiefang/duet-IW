(declare-const tmp Int)
(declare-const |x':41| Int)
(declare-const |y':42| Int)
(declare-const |havoc:1:39| Int)
(declare-const |K:49| Int)
(declare-const |tmp':43| Int)
(assert (and (or (not (<= (- |K:49|) 0)) (= (+ |x':41| (- |K:49|)) 0))
               (or (not (<= (- |K:49|) 0))
                     (<= (+ (* 1000 |y':42|) (- (* |K:49| |K:49|)) |K:49|
                              -500000) 0))
               (or (not (<= (- |K:49|) 0)) (<= (+ |y':42| (- |K:49|) -500) 0))
               (or (not (<= (- |K:49|) 0)) (<= (+ (- |y':42|) 500) 0))
               (or (and (= |K:49| 0) (= (+ (- |tmp':43|) tmp) 0)
                          (= (+ (- |y':42|) 500) 0) (= (- |x':41|) 0))
                     (and (<= (+ (- |K:49|) 1) 0) (<= (+ (- |x':41|) 1) 0)
                            (<= (+ (- |y':42|) 1) 0))) (<= (- |K:49|) 0)
               (< (- |y':42|) 0) (<= (- |x':41|) 0) (= |havoc:1:39| 0)
               (not (or (< (+ |y':42| -1000) 0) (< (+ (- |y':42|) 1000) 0)))))
(check-sat)
