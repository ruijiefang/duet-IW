(declare-const |return':165| Int)
(declare-const |param1':167| Int)
(declare-const |param0':166| Int)
(assert (and (= (+ |return':165| -5) 0)
               (= (+ |param0':166| |param1':167| -5) 0)
               (<= (+ (- |param1':167|) 5) 0) (<= (+ (- |param1':167|) 3) 0)
               (or (< (+ |return':165| -5) 0) (< (+ (- |return':165|) 5) 0))))
(check-sat)