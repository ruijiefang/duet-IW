(declare-const |z':108:114:180| Int)
(declare-const |type_err:12:13:20| Int)
(declare-const |type_err:8:9:18| Int)
(declare-const |K:112:113:179| Int)
(declare-const phi_param0 Int)
(declare-const havoc Int)
(declare-const |type_err:7:10:19| Int)
(declare-const |type_err:11:14:21| Int)
(declare-const phi_param0@width Int)
(declare-fun pow (Real Real) Real)
(declare-const phi_param0@pos Int)
(declare-const |havoc:49:67:70| Int)
(assert (and (or (and (not (= havoc 0)) (= (+ (- phi_param0) 1) 0)
                        (= (+ (- phi_param0@pos) |type_err:12:13:20|) 0)
                        (= (+ (- phi_param0@width) |type_err:11:14:21|) 0))
                   (and (= havoc 0) (= (+ (- phi_param0) 2) 0)
                          (= (+ |type_err:8:9:18| (- phi_param0@pos)) 0)
                          (= (+ |type_err:7:10:19| (- phi_param0@width)) 0)))
               (<= (+ |havoc:49:67:70| -1073741823) 0)
               (or (not (<= (- |K:112:113:179|) 0))
                     (= (+ (- (pow 2 |K:112:113:179|)) |z':108:114:180|) 0))
               (or (not (<= (- |K:112:113:179|) 0))
                     (<= (+ |z':108:114:180| |K:112:113:179|
                              (- (* |K:112:113:179| |havoc:49:67:70|)) -1) 0))
               (or (not (<= (- |K:112:113:179|) 0))
                     (<= (+ (- |z':108:114:180|) |K:112:113:179| 1) 0))
               (or (and (= |K:112:113:179| 0)
                          (= (+ (- |z':108:114:180|) 1) 0))
                     (and (<= (+ (- |K:112:113:179|) 1) 0)
                            (<= (+ (- |havoc:49:67:70|) 2) 0)
                            (<= (+ |z':108:114:180| (* -2 |havoc:49:67:70|) 2) 0)
                            (<= (+ (- |z':108:114:180|) 2) 0)))
               (<= (- |K:112:113:179|) 0) (< (- |z':108:114:180|) 0)
               (<= (+ (- |z':108:114:180|) |havoc:49:67:70|) 0)
               (not (<= (+ (- |z':108:114:180|) 1) 0))))
(check-sat)
