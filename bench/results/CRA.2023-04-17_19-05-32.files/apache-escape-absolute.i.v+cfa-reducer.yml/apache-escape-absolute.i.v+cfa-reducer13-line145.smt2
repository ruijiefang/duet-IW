(declare-const |main____CPAchecker_TMP_1':153:167:172:647:655| Int)
(declare-const |havoc:9:61:176:653| Int)
(declare-const havoc Int)
(declare-const |__VERIFIER_assert__cond___15':154:169:174:649:657| Int)
(declare-const |main__cp':152:170:175:650:658| Int)
(declare-const __VERIFIER_assert__cond___15 Int)
(declare-const __VERIFIER_assert__cond___16 Int)
(declare-const |__VERIFIER_assert__cond___16':155:168:173:648:656| Int)
(declare-const main____CPAchecker_TMP_1 Int)
(declare-const |havoc:1| Int)
(declare-const |havoc:2| Int)
(declare-const |K:165:166:171:646:654| Int)
(declare-const |phi_main____CPAchecker_TMP_1:256:257:651:659| Int)
(declare-const |havoc:12:62:258:652:660| Int)
(assert (and (<= (+ havoc -1000000) 0) (<= (+ (- havoc) -1000000) 0)
               (<= (+ |havoc:1| -1000000) 0)
               (<= (+ (- |havoc:1|) -1000000) 0)
               (<= (+ |havoc:2| -1000000) 0)
               (<= (+ (- |havoc:2|) -1000000) 0) (< (- havoc) 0)
               (< (- |havoc:1|) 0) (<= (- |havoc:2|) 0) (not (= |havoc:2| 0))
               (<= (+ |havoc:2| (- havoc) 1) 0)
               (not (= (ite (< (+ |havoc:2| (- havoc) -1) 0) 1 0) 0))
               (not (= (ite (<= (+ (- |havoc:2|) 1) 0) 1 0) 0))
               (not (= |havoc:9:61:176:653| 0))
               (not (= (ite (< (+ |havoc:2| (- havoc)) 0) 1 0) 0))
               (not (= (ite (<= (- |havoc:2|) 0) 1 0) 0))
               (or (not (and (<= (- |K:165:166:171:646:654|) 0)
                               (<= |K:165:166:171:646:654| 0)))
                     (= (+ (- main____CPAchecker_TMP_1)
                             |main____CPAchecker_TMP_1':153:167:172:647:655|) 0))
               (or (not (<= (+ (- |K:165:166:171:646:654|) 1) 0))
                     (= |main____CPAchecker_TMP_1':153:167:172:647:655| 0))
               (or (not (and (<= (- |K:165:166:171:646:654|) 0)
                               (<= |K:165:166:171:646:654| 0)))
                     (= (+ (- __VERIFIER_assert__cond___16)
                             |__VERIFIER_assert__cond___16':155:168:173:648:656|) 0))
               (or (not (<= (+ (- |K:165:166:171:646:654|) 1) 0))
                     (= (+ |__VERIFIER_assert__cond___16':155:168:173:648:656|
                             -1) 0))
               (or (not (and (<= (- |K:165:166:171:646:654|) 0)
                               (<= |K:165:166:171:646:654| 0)))
                     (= (+ (- __VERIFIER_assert__cond___15)
                             |__VERIFIER_assert__cond___15':154:169:174:649:657|) 0))
               (or (not (<= (+ (- |K:165:166:171:646:654|) 1) 0))
                     (= (+ |__VERIFIER_assert__cond___15':154:169:174:649:657|
                             -1) 0))
               (or (not (<= (- |K:165:166:171:646:654|) 0))
                     (= (+ |main__cp':152:170:175:650:658|
                             (- |K:165:166:171:646:654|) (- |havoc:2|)) 0))
               (or (and (= |K:165:166:171:646:654| 0)
                          (= (+ __VERIFIER_assert__cond___16
                                  (- |__VERIFIER_assert__cond___16':155:168:173:648:656|)) 0)
                          (= (+ __VERIFIER_assert__cond___15
                                  (- |__VERIFIER_assert__cond___15':154:169:174:649:657|)) 0)
                          (= (+ main____CPAchecker_TMP_1
                                  (- |main____CPAchecker_TMP_1':153:167:172:647:655|)) 0)
                          (= (+ (- |main__cp':152:170:175:650:658|) |havoc:2|) 0))
                     (and (<= (+ (- |K:165:166:171:646:654|) 1) 0)
                            (<= (+ |havoc:2| (- havoc) 2) 0)
                            (<= (+ (- |havoc:2|) 1) 0)
                            (= (+ |__VERIFIER_assert__cond___16':155:168:173:648:656|
                                    -1) 0)
                            (= (+ |__VERIFIER_assert__cond___15':154:169:174:649:657|
                                    -1) 0)
                            (= |main____CPAchecker_TMP_1':153:167:172:647:655| 0)
                            (<= (+ |main__cp':152:170:175:650:658| (- 
                                     havoc) 1) 0)
                            (<= (+ (- |main__cp':152:170:175:650:658|) 2) 0)))
               (<= (- |K:165:166:171:646:654|) 0) (< (- havoc) 0)
               (< (- |main__cp':152:170:175:650:658|) 0)
               (or (and (<= (+ (- |main__cp':152:170:175:650:658|) havoc -1) 0)
                          (<= (+ |main__cp':152:170:175:650:658| (- havoc) 1) 0)
                          (= (+ (- |phi_main____CPAchecker_TMP_1:256:257:651:659|)
                                  |main____CPAchecker_TMP_1':153:167:172:647:655|) 0))
                     (and (or (< (+ |main__cp':152:170:175:650:658| (- 
                                      havoc) 1) 0)
                                (< (+ (- |main__cp':152:170:175:650:658|)
                                        havoc -1) 0))
                            (not (= |havoc:12:62:258:652:660| 0))
                            (= (+ |havoc:12:62:258:652:660|
                                    (- |phi_main____CPAchecker_TMP_1:256:257:651:659|)) 0)))
               (= (ite (< (+ |main__cp':152:170:175:650:658| (- havoc)) 0) 1
                       0) 0)))
(check-sat)