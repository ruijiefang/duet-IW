(declare-const |i':61:83:87| Int)
(declare-const |l':73:82:86| Int)
(declare-const |havoc:1| Int)
(declare-const |K:79:80:84| Int)
(declare-const havoc Int)
(declare-const |k':72:81:85| Int)
(declare-const |i':61:67:69| Int)
(declare-const |K:65:66:68| Int)
(declare-const i Int)
(assert (and (< (- |havoc:1|) 0) (< (+ |havoc:1| -1000000) 0)
               (< (+ havoc -1000000) 0)
               (or (not (<= (- |K:79:80:84|) 0))
                     (= (+ |k':72:81:85| (- |K:79:80:84|) -1) 0))
               (or (not (<= (- |K:79:80:84|) 0))
                     (<= (+ |l':73:82:86| (- |K:79:80:84|) (- |havoc:1|)) 0))
               (or (not (<= (- |K:79:80:84|) 0))
                     (<= (+ (- |l':73:82:86|) |havoc:1|) 0))
               (or (and (= |K:79:80:84| 0)
                          (= (+ (- |l':73:82:86|) |havoc:1|) 0)
                          (= (+ (- |k':72:81:85|) 1) 0)
                          (= (+ (- |i':61:83:87|) i) 0))
                     (and (<= (+ (- |K:79:80:84|) 1) 0)
                            (<= (+ (- havoc) 2) 0) (<= (+ (- |havoc:1|) 1) 0)
                            (<= (+ |k':72:81:85| (- havoc)) 0)
                            (<= (+ (- |i':61:83:87|) havoc) 0)
                            (<= (+ (- |i':61:83:87|) |l':73:82:86| -1) 0)
                            (<= (+ |i':61:83:87| (- |l':73:82:86|) (- 
                                     havoc) 1) 0)
                            (<= (+ (- |k':72:81:85|) 2) 0)))
               (<= (- |K:79:80:84|) 0) (< (- |k':72:81:85|) 0)
               (< (- |l':73:82:86|) 0) (< (+ |k':72:81:85| (- havoc)) 0)
               (or (not (<= (- |K:65:66:68|) 0))
                     (= (+ |i':61:67:69| (- |K:65:66:68|) (- |l':73:82:86|)) 0))
               (or (and (= |K:65:66:68| 0)
                          (= (+ (- |i':61:67:69|) |l':73:82:86|) 0))
                     (and (<= (+ (- |K:65:66:68|) 1) 0)
                            (<= (+ |l':73:82:86| (- havoc) 1) 0)
                            (<= (+ (- |l':73:82:86|) 1) 0)
                            (<= (+ |i':61:67:69| (- havoc)) 0)
                            (<= (+ (- |i':61:67:69|) 2) 0)))
               (<= (- |K:65:66:68|) 0) (< (- |i':61:67:69|) 0)
               (< (- havoc) 0) (< (+ |i':61:67:69| (- havoc)) 0)
               (not (<= (+ (- |i':61:67:69|) 1) 0))))
(check-sat)