(declare-const |v':41:53| Int)
(declare-const |K:49:50| Int)
(declare-const |i':43:51| Int)
(declare-const |s':42:52| Int)
(declare-const havoc Int)
(assert (and (not (= havoc 0))
               (or (not (<= (- |K:49:50|) 0))
                     (= (+ |i':43:51| (- |K:49:50|)) 0))
               (or (and (= |K:49:50| 0) (= (- |i':43:51|) 0)
                          (= (- |s':42:52|) 0) (= (- |v':41:53|) 0))
                     (and (<= (+ (- |K:49:50|) 1) 0) (<= (+ (- havoc) 1) 0)
                            (<= (+ |i':43:51| (- havoc)) 0)
                            (<= (+ (- |i':43:51|) 1) 0)))
               (<= (- |K:49:50|) 0) (<= (- |i':43:51|) 0)
               (<= (+ (- |i':43:51|) havoc) 0)
               (< (+ (- |v':41:53|) |s':42:52|) 0)))
(check-sat)
