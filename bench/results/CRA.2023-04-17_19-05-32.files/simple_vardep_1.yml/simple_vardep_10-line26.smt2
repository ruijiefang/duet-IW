(declare-const |k':34| Int)
(declare-const |j':33| Int)
(declare-const |i':32| Int)
(declare-const |K:41| Int)
(assert (and (or (not (and (<= (- |K:41|) 0) (<= |K:41| 0)))
                   (= (+ |j':33| (* -2 |K:41|)) 0))
               (or (not (<= (+ (- |K:41|) 1) 0))
                     (= (+ |j':33| (* -2 |K:41|)) 0))
               (or (not (and (<= (- |K:41|) 0) (<= |K:41| 0)))
                     (= (+ |k':34| (* -3 |K:41|)) 0))
               (or (not (<= (+ (- |K:41|) 1) 0))
                     (= (+ |k':34| (* -3 |K:41|)) 0))
               (or (not (and (<= (- |K:41|) 0) (<= |K:41| 0)))
                     (= (+ |i':32| (- |K:41|)) 0))
               (or (not (<= (+ (- |K:41|) 1) 0)) (= (+ |i':32| (- |K:41|)) 0))
               (or (and (= |K:41| 0) (= (- |k':34|) 0) (= (- |j':33|) 0)
                          (= (- |i':32|) 0))
                     (and (<= (+ (- |K:41|) 1) 0)
                            (= (+ (* 2 |k':34|) (* -3 |j':33|)) 0)
                            (= (+ (* 2 |i':32|) (- |j':33|)) 0)
                            (<= (+ |j':33| -178956970) 0)
                            (<= (+ (- |j':33|) 2) 0))) (<= (- |K:41|) 0)
               (<= (- |j':33|) 0) (<= (- |i':32|) 0) (<= (- |k':34|) 0)
               (= (+ (* -2 |k':34|) (* 3 |j':33|)) 0)
               (= (+ (* 3 |i':32|) (- |k':34|)) 0)
               (< (+ |k':34| -268435455) 0)
               (not (= (+ (- |i':32|) |k':34| (- |j':33|)) 0))))
(check-sat)
