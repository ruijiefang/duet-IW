(declare-const havoc Int)
(declare-const |x':25:30| Int)
(declare-const |K:28:29| Int)
(assert (and (<= (- havoc) 0)
               (or (not (<= (- |K:28:29|) 0))
                     (= (+ |x':25:30| (- |K:28:29|) (- havoc)) 0))
               (or (and (= |K:28:29| 0) (= (+ (- |x':25:30|) havoc) 0))
                     (and (<= (+ (- |K:28:29|) 1) 0) (<= (+ havoc -99) 0)
                            (<= (- havoc) 0) (<= (+ |x':25:30| -100) 0)
                            (<= (+ (- |x':25:30|) 1) 0)))
               (<= (- |K:28:29|) 0) (<= (- |x':25:30|) 0)
               (or (<= (+ (- |x':25:30|) 100) 0)
                     (and (< (+ |x':25:30| -100) 0) (< |x':25:30| 0)))
               (not (<= (+ (- |x':25:30|) 100) 0))))
(check-sat)
