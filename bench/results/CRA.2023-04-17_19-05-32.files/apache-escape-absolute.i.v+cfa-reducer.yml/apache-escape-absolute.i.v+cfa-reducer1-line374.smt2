(declare-const havoc Int)
(declare-const |__VERIFIER_assert__cond___16':155:168:173:179:201| Int)
(declare-const |K:165:166:171:177:199| Int)
(declare-const __VERIFIER_assert__cond___15 Int)
(declare-const |havoc:9:61:176:198| Int)
(declare-const __VERIFIER_assert__cond___16 Int)
(declare-const main____CPAchecker_TMP_1 Int)
(declare-const |havoc:1| Int)
(declare-const |main____CPAchecker_TMP_1':153:167:172:178:200| Int)
(declare-const |havoc:2| Int)
(declare-const |main__cp':152:170:175:181:203| Int)
(declare-const |__VERIFIER_assert__cond___15':154:169:174:180:202| Int)
(declare-const |havoc:12:62:151:197:204| Int)
(assert (and (<= (+ havoc -1000000) 0) (<= (+ (- havoc) -1000000) 0)
               (<= (+ |havoc:1| -1000000) 0)
               (<= (+ (- |havoc:1|) -1000000) 0)
               (<= (+ |havoc:2| -1000000) 0)
               (<= (+ (- |havoc:2|) -1000000) 0) (< (- havoc) 0)
               (< (- |havoc:1|) 0) (<= (- |havoc:2|) 0) (not (= |havoc:2| 0))
               (<= (+ |havoc:2| (- havoc) 1) 0)
               (not (= (ite (< (+ |havoc:2| (- havoc) -1) 0) 1 0) 0))
               (not (= (ite (<= (+ (- |havoc:2|) 1) 0) 1 0) 0))
               (not (= |havoc:9:61:176:198| 0))
               (not (= (ite (< (+ |havoc:2| (- havoc)) 0) 1 0) 0))
               (not (= (ite (<= (- |havoc:2|) 0) 1 0) 0))
               (or (not (and (<= (- |K:165:166:171:177:199|) 0)
                               (<= |K:165:166:171:177:199| 0)))
                     (= (+ (- main____CPAchecker_TMP_1)
                             |main____CPAchecker_TMP_1':153:167:172:178:200|) 0))
               (or (not (<= (+ (- |K:165:166:171:177:199|) 1) 0))
                     (= |main____CPAchecker_TMP_1':153:167:172:178:200| 0))
               (or (not (and (<= (- |K:165:166:171:177:199|) 0)
                               (<= |K:165:166:171:177:199| 0)))
                     (= (+ (- __VERIFIER_assert__cond___16)
                             |__VERIFIER_assert__cond___16':155:168:173:179:201|) 0))
               (or (not (<= (+ (- |K:165:166:171:177:199|) 1) 0))
                     (= (+ |__VERIFIER_assert__cond___16':155:168:173:179:201|
                             -1) 0))
               (or (not (and (<= (- |K:165:166:171:177:199|) 0)
                               (<= |K:165:166:171:177:199| 0)))
                     (= (+ (- __VERIFIER_assert__cond___15)
                             |__VERIFIER_assert__cond___15':154:169:174:180:202|) 0))
               (or (not (<= (+ (- |K:165:166:171:177:199|) 1) 0))
                     (= (+ |__VERIFIER_assert__cond___15':154:169:174:180:202|
                             -1) 0))
               (or (not (<= (- |K:165:166:171:177:199|) 0))
                     (= (+ |main__cp':152:170:175:181:203|
                             (- |K:165:166:171:177:199|) (- |havoc:2|)) 0))
               (or (and (= |K:165:166:171:177:199| 0)
                          (= (+ __VERIFIER_assert__cond___16
                                  (- |__VERIFIER_assert__cond___16':155:168:173:179:201|)) 0)
                          (= (+ __VERIFIER_assert__cond___15
                                  (- |__VERIFIER_assert__cond___15':154:169:174:180:202|)) 0)
                          (= (+ main____CPAchecker_TMP_1
                                  (- |main____CPAchecker_TMP_1':153:167:172:178:200|)) 0)
                          (= (+ (- |main__cp':152:170:175:181:203|) |havoc:2|) 0))
                     (and (<= (+ (- |K:165:166:171:177:199|) 1) 0)
                            (<= (+ |havoc:2| (- havoc) 2) 0)
                            (<= (+ (- |havoc:2|) 1) 0)
                            (= (+ |__VERIFIER_assert__cond___16':155:168:173:179:201|
                                    -1) 0)
                            (= (+ |__VERIFIER_assert__cond___15':154:169:174:180:202|
                                    -1) 0)
                            (= |main____CPAchecker_TMP_1':153:167:172:178:200| 0)
                            (<= (+ |main__cp':152:170:175:181:203| (- 
                                     havoc) 1) 0)
                            (<= (+ (- |main__cp':152:170:175:181:203|) 2) 0)))
               (<= (- |K:165:166:171:177:199|) 0) (< (- havoc) 0)
               (< (- |main__cp':152:170:175:181:203|) 0)
               (or (< (+ |main__cp':152:170:175:181:203| (- havoc) 1) 0)
                     (< (+ (- |main__cp':152:170:175:181:203|) havoc -1) 0))
               (= |havoc:12:62:151:197:204| 0)
               (= (ite (< (+ |main__cp':152:170:175:181:203| (- havoc)) 0) 1
                       0) 0)))
(check-sat)