(declare-const |main__y':76| Int)
(declare-const |main____CPAchecker_TMP_0':77| Int)
(declare-const havoc Int)
(declare-const |K:83| Int)
(declare-const |main____CPAchecker_TMP_1':78| Int)
(declare-const |havoc:2:66| Int)
(declare-const |main__x':75| Int)
(declare-const main____CPAchecker_TMP_0 Int)
(declare-const main____CPAchecker_TMP_1 Int)
(assert (and (or (not (<= (- |K:83|) 0))
                   (<= (+ (- havoc) |main__x':75| (* -5 |K:83|)) 0))
               (or (not (<= (- |K:83|) 0))
                     (<= (+ |main__y':76| (- |K:83|) -1) 0))
               (or (not (<= (- |K:83|) 0))
                     (<= (+ (* 3 |main__y':76|) havoc (- |main__x':75|)
                              |K:83| -3) 0))
               (or (not (<= (- |K:83|) 0))
                     (<= (+ havoc (- |main__x':75|) |K:83|) 0))
               (or (and (= |K:83| 0)
                          (= (+ (- |main____CPAchecker_TMP_1':78|)
                                  main____CPAchecker_TMP_1) 0)
                          (= (+ (- |main____CPAchecker_TMP_0':77|)
                                  main____CPAchecker_TMP_0) 0)
                          (= (+ (- |main__y':76|) 1) 0)
                          (= (+ havoc (- |main__x':75|)) 0))
                     (and (<= (+ (- |K:83|) 1) 0) (<= (+ (mod havoc 3) -2) 0)
                            (<= (- (mod havoc 3)) 0)
                            (<= (+ |main__y':76| -1) 0)
                            (<= (- |main__y':76|) 0))) (<= (- |K:83|) 0)
               (<= (- |main__y':76|) 0) (= |havoc:2:66| 0)
               (= |main__y':76| 0)
               (= (ite (= (mod |main__x':75| 3) 0) 1 0) 0)))
(check-sat)
