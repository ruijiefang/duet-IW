(declare-const |main__j':67| Int)
(declare-const |__VERIFIER_assert__cond___1':81:91:96:127| Int)
(declare-const |__VERIFIER_assert__cond___0':80:92:97:128| Int)
(declare-const havoc Int)
(declare-const |main__i':66:94:99:130| Int)
(declare-const |K:113| Int)
(declare-const main__j Int)
(declare-const |main__j':67:93:98:129| Int)
(declare-const |K:89:90:95:126| Int)
(declare-const __VERIFIER_assert__cond___1 Int)
(declare-const |main__i':66| Int)
(declare-const __VERIFIER_assert__cond___0 Int)
(assert (and (= |K:113| 0) (= (+ (- |main__j':67|) main__j) 0)
               (= (- |main__i':66|) 0) (<= (- |K:113|) 0) (= |main__i':66| 0)
               (= |main__i':66| 0) (< (+ (- havoc) |main__i':66|) 0)
               (not (= (ite (<= (+ (- havoc) |main__i':66| 1) 0) 1 0) 0))
               (or (not (and (<= (- |K:89:90:95:126|) 0)
                               (<= |K:89:90:95:126| 0)))
                     (= (+ (- __VERIFIER_assert__cond___1)
                             |__VERIFIER_assert__cond___1':81:91:96:127|) 0))
               (or (not (<= (+ (- |K:89:90:95:126|) 1) 0))
                     (= (+ |__VERIFIER_assert__cond___1':81:91:96:127| -1) 0))
               (or (not (and (<= (- |K:89:90:95:126|) 0)
                               (<= |K:89:90:95:126| 0)))
                     (= (+ (- __VERIFIER_assert__cond___0)
                             |__VERIFIER_assert__cond___0':80:92:97:128|) 0))
               (or (not (<= (+ (- |K:89:90:95:126|) 1) 0))
                     (= (+ |__VERIFIER_assert__cond___0':80:92:97:128| -1) 0))
               (or (not (<= (- |K:89:90:95:126|) 0))
                     (<= (+ (* 8 |main__i':66:94:99:130|)
                              |main__j':67:93:98:129| (- |K:89:90:95:126|)
                              (* -8 |main__i':66|)) 0))
               (or (not (<= (- |K:89:90:95:126|) 0))
                     (<= (+ |main__i':66:94:99:130| |K:89:90:95:126|
                              (- (* |K:89:90:95:126| havoc))
                              (- |main__i':66|)) 0))
               (or (not (<= (- |K:89:90:95:126|) 0))
                     (<= (+ (- |main__i':66:94:99:130|) |main__i':66|) 0))
               (or (and (= |K:89:90:95:126| 0)
                          (= (+ __VERIFIER_assert__cond___1
                                  (- |__VERIFIER_assert__cond___1':81:91:96:127|)) 0)
                          (= (+ __VERIFIER_assert__cond___0
                                  (- |__VERIFIER_assert__cond___0':80:92:97:128|)) 0)
                          (= (- |main__j':67:93:98:129|) 0)
                          (= (+ (- |main__i':66:94:99:130|) |main__i':66|) 0))
                     (and (<= (+ (- |K:89:90:95:126|) 1) 0)
                            (<= (+ (- havoc) |main__i':66| 1) 0)
                            (<= (- |main__i':66|) 0)
                            (= (+ |__VERIFIER_assert__cond___0':80:92:97:128|
                                    -1) 0)
                            (= (+ |__VERIFIER_assert__cond___1':81:91:96:127|
                                    -1) 0)
                            (<= (+ |main__j':67:93:98:129| -7) 0)
                            (<= (+ |main__i':66:94:99:130| (- havoc) 1) 0)
                            (<= (- |main__i':66:94:99:130|) 0)
                            (<= (- |main__j':67:93:98:129|) 0)
                            (<= (+ (- |main__i':66:94:99:130|)
                                     (- |main__j':67:93:98:129|) 1) 0)))
               (<= (- |K:89:90:95:126|) 0) (<= (- |main__j':67:93:98:129|) 0)
               (< (- havoc) 0) (<= (- |main__i':66:94:99:130|) 0)
               (= (ite (< (+ (- |main__i':66:94:99:130|) -1) 0) 1 0) 0)))
(check-sat)
