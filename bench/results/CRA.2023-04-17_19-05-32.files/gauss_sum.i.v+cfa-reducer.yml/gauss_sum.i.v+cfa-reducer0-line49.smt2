(declare-const |main__i':56:65:68| Int)
(declare-const |K:62:63:66| Int)
(declare-const havoc Int)
(declare-const |main__sum':55:64:67| Int)
(assert (and (<= (+ (- havoc) 1) 0) (<= (+ havoc -1000) 0)
               (or (not (<= (- |K:62:63:66|) 0))
                     (= (+ (* 2 |main__sum':55:64:67|)
                             (- (* |K:62:63:66| |K:62:63:66|))
                             (- |K:62:63:66|)) 0))
               (or (not (<= (- |K:62:63:66|) 0))
                     (= (+ |main__i':56:65:68| (- |K:62:63:66|) -1) 0))
               (or (and (= |K:62:63:66| 0)
                          (= (+ (- |main__i':56:65:68|) 1) 0)
                          (= (- |main__sum':55:64:67|) 0))
                     (and (<= (+ (- |K:62:63:66|) 1) 0)
                            (<= (+ (- havoc) 1) 0)
                            (<= (+ |main__i':56:65:68|
                                     (- |main__sum':55:64:67|) -1) 0)
                            (<= (+ |main__i':56:65:68| (- havoc) -1) 0)
                            (<= (+ (- |main__i':56:65:68|) 2) 0)))
               (<= (- |K:62:63:66|) 0) (< (- |main__i':56:65:68|) 0)
               (< (- havoc) 0) (<= (- |main__sum':55:64:67|) 0)
               (< (+ (- |main__i':56:65:68|) havoc) 0)
               (= (ite (= (+ (* 2 |main__sum':55:64:67|) (- (* havoc havoc))
                               (- havoc)) 0)
                       1 0) 0)))
(check-sat)
