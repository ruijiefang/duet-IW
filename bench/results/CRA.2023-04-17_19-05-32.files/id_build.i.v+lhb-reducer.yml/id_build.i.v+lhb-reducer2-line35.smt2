(declare-const |main__j':67| Int)
(declare-const havoc Int)
(declare-const |K:113| Int)
(declare-const main__j Int)
(declare-const |main__i':66| Int)
(assert (and (= |K:113| 0) (= (+ (- |main__j':67|) main__j) 0)
               (= (- |main__i':66|) 0) (<= (- |K:113|) 0) (= |main__i':66| 0)
               (= |main__i':66| 0) (< (+ (- havoc) |main__i':66|) 0)
               (= (ite (<= (+ (- havoc) |main__i':66| 1) 0) 1 0) 0)))
(check-sat)
