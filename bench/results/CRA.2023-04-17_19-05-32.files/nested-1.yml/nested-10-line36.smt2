(declare-const |k':62:87:91:95| Int)
(declare-const |K:85:86:90:94| Int)
(declare-const |j':63:89:93:97| Int)
(declare-const havoc Int)
(declare-const j Int)
(declare-const |i':76:88:92:96| Int)
(declare-const |havoc:2| Int)
(assert (and (<= (+ (- havoc) 10) 0) (<= (+ havoc -10000) 0)
               (<= (+ (- |havoc:2|) 10) 0) (<= (+ |havoc:2| -10000) 0)
               (or (not (<= (- |K:85:86:90:94|) 0))
                     (= (+ |k':62:87:91:95| (- (* |K:85:86:90:94| |havoc:2|))) 0))
               (or (not (<= (- |K:85:86:90:94|) 0))
                     (= (+ |i':76:88:92:96| (- |K:85:86:90:94|)) 0))
               (or (not (and (<= (- |K:85:86:90:94|) 0)
                               (<= |K:85:86:90:94| 0)))
                     (= (+ (- j) |j':63:89:93:97|) 0))
               (or (not (<= (+ (- |K:85:86:90:94|) 1) 0))
                     (= (+ |j':63:89:93:97| (- |havoc:2|)) 0))
               (or (and (= |K:85:86:90:94| 0)
                          (= (+ j (- |j':63:89:93:97|)) 0)
                          (= (- |i':76:88:92:96|) 0)
                          (= (- |k':62:87:91:95|) 0))
                     (and (<= (+ (- |K:85:86:90:94|) 1) 0)
                            (<= (+ (- havoc) 1) 0) (<= (+ (- |havoc:2|) 1) 0)
                            (= (+ |j':63:89:93:97| (- |havoc:2|)) 0)
                            (<= (+ (- |k':62:87:91:95|) |havoc:2|) 0)
                            (<= (+ |i':76:88:92:96| (- havoc)) 0)
                            (<= (+ (- |i':76:88:92:96|) 1) 0)
                            (<= (+ (- |havoc:2|) 1) 0)))
               (<= (- |K:85:86:90:94|) 0) (<= (- |k':62:87:91:95|) 0)
               (<= (- |i':76:88:92:96|) 0) (< (- |havoc:2|) 0)
               (< (- havoc) 0) (<= (+ (- |i':76:88:92:96|) havoc) 0)
               (not (<= (+ (- |k':62:87:91:95|) 100) 0))))
(check-sat)