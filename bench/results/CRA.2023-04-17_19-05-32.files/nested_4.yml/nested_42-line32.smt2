(declare-const |d':51| Int)
(declare-const |K:96| Int)
(declare-const |b':71| Int)
(declare-const |a':87| Int)
(declare-const |c':59| Int)
(assert (and (or (not (and (<= (- |K:96|) 0) (<= |K:96| 0)))
                   (= (+ |b':71| -6) 0))
               (or (not (<= (+ (- |K:96|) 1) 0)) (= (+ |b':71| -6) 0))
               (or (not (and (<= (- |K:96|) 0) (<= |K:96| 0)))
                     (= (+ |d':51| -6) 0))
               (or (not (<= (+ (- |K:96|) 1) 0)) (= (+ |d':51| -6) 0))
               (or (not (and (<= (- |K:96|) 0) (<= |K:96| 0)))
                     (= (+ |c':59| -6) 0))
               (or (not (<= (+ (- |K:96|) 1) 0)) (= (+ |c':59| -6) 0))
               (or (not (<= (- |K:96|) 0)) (= (+ |a':87| (- |K:96|)) 0))
               (or (not (<= (- |K:96|) 0))
                     (<= (+ |d':51| (* -5 |K:96|) -6) 0))
               (or (not (<= (- |K:96|) 0))
                     (<= (+ |c':59| (* -5 |K:96|) -6) 0))
               (or (not (<= (- |K:96|) 0))
                     (<= (+ |b':71| (* -5 |K:96|) -6) 0))
               (or (and (= |K:96| 0) (= (+ (- |d':51|) 6) 0)
                          (= (+ (- |c':59|) 6) 0) (= (+ (- |b':71|) 6) 0)
                          (= (- |a':87|) 0))
                     (and (<= (+ (- |K:96|) 1) 0) (= (+ |d':51| -6) 0)
                            (= (+ |c':59| -6) 0) (= (+ |b':71| -6) 0)
                            (<= (+ |a':87| -6) 0) (<= (+ (- |a':87|) 1) 0)))
               (<= (- |K:96|) 0) (< (- |d':51|) 0) (< (- |c':59|) 0)
               (< (- |b':71|) 0) (<= (- |a':87|) 0) (<= (+ (- |a':87|) 6) 0)
               (= (+ |a':87| -6) 0) (= (+ |b':71| -6) 0)
               (not (= (+ |c':59| -6) 0))))
(check-sat)
