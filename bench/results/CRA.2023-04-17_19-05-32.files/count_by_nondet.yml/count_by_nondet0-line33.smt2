(declare-const |i':51| Int)
(declare-const |K:58| Int)
(declare-const |j':53| Int)
(declare-const |k':52| Int)
(declare-const j Int)
(assert (and (or (not (<= (- |K:58|) 0)) (= (+ |k':52| (- |K:58|)) 0))
               (or (not (<= (- |K:58|) 0))
                     (<= (+ |i':51| (* -999999 |K:58|)) 0))
               (or (not (<= (- |K:58|) 0)) (<= (+ (- |i':51|) |K:58|) 0))
               (or (and (= |K:58| 0) (= (+ (- |j':53|) j) 0)
                          (= (- |k':52|) 0) (= (- |i':51|) 0))
                     (and (<= (+ (- |K:58|) 1) 0)
                            (<= (+ (- |j':53|) |i':51| -999999) 0)
                            (<= (+ |j':53| -999999) 0)
                            (<= (+ (- |k':52|) 1) 0) (<= (+ (- |j':53|) 1) 0)
                            (<= (+ |j':53| (- |i':51|)) 0)))
               (<= (- |K:58|) 0) (<= (- |k':52|) 0) (<= (- |i':51|) 0)
               (<= (+ (- |i':51|) 1000000) 0)
               (not (<= (+ |k':52| -1000000) 0))))
(check-sat)
