(declare-const |havoc:5:17:90:139:166| Int)
(declare-const |tmp___2':99:108:113:163| Int)
(declare-const havoc Int)
(declare-const |K:71:72| Int)
(declare-const tmp Int)
(declare-const |tmp':65:73| Int)
(declare-const |t':64:107:112:162| Int)
(declare-const |t':64:74| Int)
(declare-const tmp___0 Int)
(declare-const tmp___1 Int)
(declare-const |havoc:3:16:63:160| Int)
(declare-const |K:105:106:111:161| Int)
(declare-const |havoc:8:19:140:167| Int)
(declare-const tmp___2 Int)
(declare-const |tmp___1':98:109:114:164| Int)
(declare-const |tmp___0':97:110:115:165| Int)
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
               (not (= |havoc:3:16:63:160| 0)) (<= (- |t':64:74|) 0)
               (<= (+ |t':64:74| (- havoc) 1) 0)
               (or (not (<= (- |K:105:106:111:161|) 0))
                     (<= (+ |t':64:107:112:162| (* -2 |K:105:106:111:161|)
                              (- |t':64:74|) -1) 0))
               (or (not (<= (- |K:105:106:111:161|) 0))
                     (<= (+ |t':64:107:112:162| (* 2 |K:105:106:111:161|)
                              (- |t':64:74|)
                              (- (* |K:105:106:111:161| havoc)) -1) 0))
               (or (not (<= (- |K:105:106:111:161|) 0))
                     (<= (+ (- |t':64:107:112:162|) |K:105:106:111:161|
                              |t':64:74| 1) 0))
               (or (and (= |K:105:106:111:161| 0)
                          (= (+ (- |tmp___2':99:108:113:163|) tmp___2) 0)
                          (= (+ (- |tmp___1':98:109:114:164|) tmp___1) 0)
                          (= (+ (- |tmp___0':97:110:115:165|) tmp___0) 0)
                          (= (+ (- |t':64:107:112:162|) |t':64:74| 1) 0))
                     (and (<= (+ (- |K:105:106:111:161|) 1) 0)
                            (<= (+ |t':64:74| (- havoc) 3) 0)
                            (<= (- |t':64:74|) 0)
                            (<= (+ |t':64:107:112:162| (- havoc) 1) 0)
                            (<= (+ (- |t':64:107:112:162|) 2) 0)))
               (<= (- |K:105:106:111:161|) 0) (< (- |t':64:107:112:162|) 0)
               (<= (+ (- havoc) 1) 0)
               (not (= (+ |t':64:107:112:162| (- havoc) 1) 0))
               (not (= |havoc:5:17:90:139:166| 0))
               (not (= |havoc:8:19:140:167| 0))
               (<= (- |t':64:107:112:162|) 0)
               (<= (+ |t':64:107:112:162| (- havoc) 1) 0)
               (= (+ |t':64:107:112:162| (- havoc) 2) 0)
               (<= (+ (- |t':64:107:112:162|) -1) 0)
               (not (<= (+ |t':64:107:112:162| (- havoc) 2) 0))))
(check-sat)
