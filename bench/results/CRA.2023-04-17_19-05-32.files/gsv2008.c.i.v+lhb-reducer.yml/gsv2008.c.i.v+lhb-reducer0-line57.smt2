(declare-const |main____CPAchecker_TMP_0':67:81:86:91| Int)
(declare-const |havoc:0| Int)
(declare-const |main__x':65:78:83:88| Int)
(declare-const |__tmp_55_0':64:80:85:90| Int)
(declare-const |main__y':66:79:84:89| Int)
(declare-const |K:76:77:82:87| Int)
(assert (and (< (+ (- |havoc:0|) -1000) 0) (< (+ |havoc:0| -1000000) 0)
               (or (not (<= (- |K:76:77:82:87|) 0))
                     (= (+ (* 2 |main__x':65:78:83:88|)
                             (- (* |K:76:77:82:87| |K:76:77:82:87|))
                             (- |K:76:77:82:87|)
                             (* -2 (* |K:76:77:82:87| |havoc:0|))
                             (* -2 |havoc:0|) 100) 0))
               (or (not (and (<= (- |K:76:77:82:87|) 0)
                               (<= |K:76:77:82:87| 0)))
                     (= (+ |main__y':66:79:84:89| (- |K:76:77:82:87|)
                             (- |havoc:0|) -1) 0))
               (or (not (<= (+ (- |K:76:77:82:87|) 1) 0))
                     (= (+ |main__y':66:79:84:89| (- |K:76:77:82:87|)
                             (- |havoc:0|) -1) 0))
               (or (not (and (<= (- |K:76:77:82:87|) 0)
                               (<= |K:76:77:82:87| 0)))
                     (= (+ |__tmp_55_0':64:80:85:90| (- |K:76:77:82:87|)
                             (- |havoc:0|)) 0))
               (or (not (<= (+ (- |K:76:77:82:87|) 1) 0))
                     (= (+ |__tmp_55_0':64:80:85:90| (- |K:76:77:82:87|)
                             (- |havoc:0|)) 0))
               (or (not (and (<= (- |K:76:77:82:87|) 0)
                               (<= |K:76:77:82:87| 0)))
                     (= (+ |main____CPAchecker_TMP_0':67:81:86:91|
                             (- |K:76:77:82:87|) (- |havoc:0|)) 0))
               (or (not (<= (+ (- |K:76:77:82:87|) 1) 0))
                     (= (+ |main____CPAchecker_TMP_0':67:81:86:91|
                             (- |K:76:77:82:87|) (- |havoc:0|) 1) 0))
               (or (and (= |K:76:77:82:87| 0)
                          (= (+ (- |main____CPAchecker_TMP_0':67:81:86:91|)
                                  |havoc:0|) 0)
                          (= (+ (- |main__y':66:79:84:89|) |havoc:0| 1) 0)
                          (= (+ (- |main__x':65:78:83:88|) |havoc:0| -50) 0)
                          (= (+ (- |__tmp_55_0':64:80:85:90|) |havoc:0|) 0))
                     (and (<= (+ (- |K:76:77:82:87|) 1) 0)
                            (<= (+ |havoc:0| -49) 0)
                            (= (+ |__tmp_55_0':64:80:85:90|
                                    (- |main__y':66:79:84:89|) 1) 0)
                            (= (+ |main____CPAchecker_TMP_0':67:81:86:91|
                                    (- |main__y':66:79:84:89|) 2) 0)
                            (<= (+ (- |main__y':66:79:84:89|)
                                     |main__x':65:78:83:88| 2) 0)))
               (<= (- |K:76:77:82:87|) 0)
               (= (+ |__tmp_55_0':64:80:85:90| (- |main__y':66:79:84:89|) 1) 0)
               (<= (- |main__x':65:78:83:88|) 0)
               (= (ite (< (- |main__y':66:79:84:89|) 0) 1 0) 0)))
(check-sat)
