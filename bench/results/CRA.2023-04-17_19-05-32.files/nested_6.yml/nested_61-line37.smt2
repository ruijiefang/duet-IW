(declare-const |e':87| Int)
(declare-const |d':99| Int)
(declare-const |b':135| Int)
(declare-const |K:172| Int)
(declare-const |c':115| Int)
(declare-const |f':79| Int)
(declare-const |a':159| Int)
(assert (and (or (not (and (<= (- |K:172|) 0) (<= |K:172| 0)))
                   (= (+ |b':135| -6) 0))
               (or (not (<= (+ (- |K:172|) 1) 0)) (= (+ |b':135| -6) 0))
               (or (not (and (<= (- |K:172|) 0) (<= |K:172| 0)))
                     (= (+ |f':79| -6) 0))
               (or (not (<= (+ (- |K:172|) 1) 0)) (= (+ |f':79| -6) 0))
               (or (not (<= (- |K:172|) 0)) (= (+ |a':159| (- |K:172|)) 0))
               (or (not (and (<= (- |K:172|) 0) (<= |K:172| 0)))
                     (= (+ |e':87| -6) 0))
               (or (not (<= (+ (- |K:172|) 1) 0)) (= (+ |e':87| -6) 0))
               (or (not (and (<= (- |K:172|) 0) (<= |K:172| 0)))
                     (= (+ |c':115| -6) 0))
               (or (not (<= (+ (- |K:172|) 1) 0)) (= (+ |c':115| -6) 0))
               (or (not (and (<= (- |K:172|) 0) (<= |K:172| 0)))
                     (= (+ |d':99| -6) 0))
               (or (not (<= (+ (- |K:172|) 1) 0)) (= (+ |d':99| -6) 0))
               (or (not (<= (- |K:172|) 0))
                     (<= (+ |f':79| (* -5 |K:172|) -6) 0))
               (or (not (<= (- |K:172|) 0))
                     (<= (+ |e':87| (* -5 |K:172|) -6) 0))
               (or (not (<= (- |K:172|) 0))
                     (<= (+ |d':99| (* -5 |K:172|) -6) 0))
               (or (not (<= (- |K:172|) 0))
                     (<= (+ |c':115| (* -5 |K:172|) -6) 0))
               (or (not (<= (- |K:172|) 0))
                     (<= (+ |b':135| (* -5 |K:172|) -6) 0))
               (or (and (= |K:172| 0) (= (+ (- |f':79|) 6) 0)
                          (= (+ (- |e':87|) 6) 0) (= (+ (- |d':99|) 6) 0)
                          (= (+ (- |c':115|) 6) 0) (= (+ (- |b':135|) 6) 0)
                          (= (- |a':159|) 0))
                     (and (<= (+ (- |K:172|) 1) 0) (= (+ |f':79| -6) 0)
                            (= (+ |e':87| -6) 0) (= (+ |d':99| -6) 0)
                            (= (+ |c':115| -6) 0) (= (+ |b':135| -6) 0)
                            (<= (+ |a':159| -6) 0) (<= (+ (- |a':159|) 1) 0)))
               (<= (- |K:172|) 0) (< (- |f':79|) 0) (< (- |e':87|) 0)
               (< (- |d':99|) 0) (< (- |c':115|) 0) (< (- |b':135|) 0)
               (<= (- |a':159|) 0) (<= (+ (- |a':159|) 6) 0)
               (= (+ |a':159| -6) 0) (not (= (+ |b':135| -6) 0))))
(check-sat)
