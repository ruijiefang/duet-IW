(declare-const havoc Int)
(declare-const |tmp___1':98:109:114:216| Int)
(declare-const |t':64:107:112:214| Int)
(declare-const tmp Int)
(declare-const |havoc:6:18:202:219| Int)
(declare-const |tmp':65:73| Int)
(declare-const |havoc:3:16:63:212| Int)
(declare-const |K:71:72| Int)
(declare-const tmp___0 Int)
(declare-const tmp___1 Int)
(declare-const |tmp___0':97:110:115:217| Int)
(declare-const |havoc:5:17:90:139:218| Int)
(declare-const |K:105:106:111:213| Int)
(declare-const tmp___2 Int)
(declare-const |t':64:74| Int)
(declare-const |tmp___2':99:108:113:215| Int)
(assert (and (<= (+ (- havoc) 1) 0)
               (or (not (and (<= (- |K:71:72|) 0) (<= |K:71:72| 0)))
                     (= (+ (- tmp) |tmp':65:73|) 0))
               (or (not (<= (+ (- |K:71:72|) 1) 0)) (= |tmp':65:73| 0))
               (or (not (<= (- |K:71:72|) 0))
                     (= (+ |t':64:74| (- |K:71:72|)) 0))
               (or (and (= |K:71:72| 0) (= (+ tmp (- |tmp':65:73|)) 0)
                          (= (- |t':64:74|) 0))
                     (and (<= (+ (- |K:71:72|) 1) 0) (<= (+ (- havoc) 2) 0)
                            (= |tmp':65:73| 0)
                            (<= (+ |t':64:74| (- havoc) 1) 0)
                            (<= (+ (- |t':64:74|) 1) 0)))
               (<= (- |K:71:72|) 0) (<= (- |t':64:74|) 0)
               (<= (+ (- havoc) 1) 0) (not (= (+ |t':64:74| (- havoc) 1) 0))
               (not (= |havoc:3:16:63:212| 0)) (<= (- |t':64:74|) 0)
               (<= (+ |t':64:74| (- havoc) 1) 0)
               (or (not (<= (- |K:105:106:111:213|) 0))
                     (<= (+ |t':64:107:112:214| (* -2 |K:105:106:111:213|)
                              (- |t':64:74|) -1) 0))
               (or (not (<= (- |K:105:106:111:213|) 0))
                     (<= (+ |t':64:107:112:214| (* 2 |K:105:106:111:213|)
                              (- |t':64:74|)
                              (- (* |K:105:106:111:213| havoc)) -1) 0))
               (or (not (<= (- |K:105:106:111:213|) 0))
                     (<= (+ (- |t':64:107:112:214|) |K:105:106:111:213|
                              |t':64:74| 1) 0))
               (or (and (= |K:105:106:111:213| 0)
                          (= (+ (- |tmp___2':99:108:113:215|) tmp___2) 0)
                          (= (+ (- |tmp___1':98:109:114:216|) tmp___1) 0)
                          (= (+ (- |tmp___0':97:110:115:217|) tmp___0) 0)
                          (= (+ (- |t':64:107:112:214|) |t':64:74| 1) 0))
                     (and (<= (+ (- |K:105:106:111:213|) 1) 0)
                            (<= (+ |t':64:74| (- havoc) 3) 0)
                            (<= (- |t':64:74|) 0)
                            (<= (+ |t':64:107:112:214| (- havoc) 1) 0)
                            (<= (+ (- |t':64:107:112:214|) 2) 0)))
               (<= (- |K:105:106:111:213|) 0) (< (- |t':64:107:112:214|) 0)
               (<= (+ (- havoc) 1) 0)
               (not (= (+ |t':64:107:112:214| (- havoc) 1) 0))
               (= |havoc:5:17:90:139:218| 0) (not (= |havoc:6:18:202:219| 0))
               (<= (- |t':64:107:112:214|) 0)
               (not (<= (+ |t':64:107:112:214| (- havoc) 1) 0))))
(check-sat)
