(declare-const havoc Int)
(declare-const |k':128:160:163| Int)
(declare-const |havoc:1| Int)
(declare-const |b':166| Int)
(declare-const |k':128| Int)
(declare-const |c':127| Int)
(declare-const |K:196| Int)
(declare-const |r':169| Int)
(declare-const |a':165| Int)
(declare-const |p':167| Int)
(declare-const |s':170| Int)
(declare-const |K:158:159:162| Int)
(declare-const |q':168| Int)
(declare-const |c':127:161:164| Int)
(assert (and (not (= (ite (<= (+ (- havoc) 1) 0) 1 0) 0))
               (not (= (ite (<= (+ (- |havoc:1|) 1) 0) 1 0) 0))
               (not (= (ite (< (+ (* |havoc:1| havoc) -2147483647) 0) 1 0) 0))
               (not (= (ite (< (+ (* |havoc:1| |havoc:1|) -2147483647) 0) 1 0) 0))
               (or (not (and (<= (- |K:196|) 0) (<= |K:196| 0)))
                     (= (+ (- |c':127|) |b':166| (- |havoc:1|)) 0))
               (or (not (<= (+ (- |K:196|) 1) 0))
                     (= (+ (- |c':127|) |b':166|) 0))
               (or (not (<= (- |K:196|) 0))
                     (<= (+ |a':165| |k':128| |b':166| (- |havoc:1|)
                              (- havoc)) 0))
               (or (not (<= (- |K:196|) 0))
                     (<= (+ |a':165| |b':166| (- |havoc:1|) (- havoc)) 0))
               (or (not (<= (- |K:196|) 0))
                     (<= (+ |b':166| |K:196| (- |havoc:1|)) 0))
               (or (and (= |K:196| 0) (= (- |k':128|) 0) (= (- |c':127|) 0)
                          (= (+ (- |s':170|) 1) 0) (= (- |r':169|) 0)
                          (= (- |q':168|) 0) (= (+ (- |p':167|) 1) 0)
                          (= (+ (- |b':166|) |havoc:1|) 0)
                          (= (+ (- |a':165|) havoc) 0))
                     (and (<= (+ (- |K:196|) 1) 0)
                            (= (+ |a':165| (- (* |r':169| |havoc:1|))
                                    (- (* |p':167| havoc))) 0)
                            (= (+ (- |c':127|) |b':166|) 0)
                            (= (+ (- (* |r':169| (* |havoc:1| |havoc:1|)))
                                    (* |a':165| |havoc:1|)
                                    (- (* |p':167| |havoc:1| havoc))) 0)
                            (<= (- |k':128|) 0)
                            (<= (+ |c':127| (- (* |r':169| |havoc:1|))
                                     (- (* |p':167| havoc)) 1) 0)))
               (<= (- |K:196|) 0) (<= (- |k':128|) 0)
               (or (< |b':166| 0) (< (- |b':166|) 0))
               (or (not (<= (- |K:158:159:162|) 0))
                     (= (+ |k':128:160:163| (- |K:158:159:162|)) 0))
               (or (not (<= (- |K:158:159:162|) 0))
                     (= (+ |c':127:161:164| (- |a':165|)
                             (* |K:158:159:162| |b':166|)) 0))
               (or (and (= |K:158:159:162| 0) (= (- |k':128:160:163|) 0)
                          (= (+ (- |c':127:161:164|) |a':165|) 0))
                     (and (<= (+ (- |K:158:159:162|) 1) 0)
                            (= (+ (- |b':166|) (* |s':170| |havoc:1|)
                                    (* |q':168| havoc)) 0)
                            (= (+ (- (* |s':170| (* |havoc:1| |havoc:1|)))
                                    (* |b':166| |havoc:1|)
                                    (- (* |q':168| |havoc:1| havoc))) 0)
                            (= (+ (- |a':165|) (* |r':169| |havoc:1|)
                                    (* |p':167| havoc)) 0)
                            (<= (+ (- |a':165|) |b':166|) 0)
                            (= (+ (- |b':166|) (* |s':170| |havoc:1|)
                                    (* |q':168| havoc)) 0)
                            (= (+ (- (* |s':170| (* |havoc:1| |havoc:1|)))
                                    (* |b':166| |havoc:1|)
                                    (- (* |q':168| |havoc:1| havoc))) 0)
                            (= (+ (- |a':165|) (* |r':169| |havoc:1|)
                                    (* |p':167| havoc)) 0)
                            (= (+ |c':127:161:164| (- |a':165|)
                                    (* |k':128:160:163| |b':166|)) 0)
                            (<= (+ (- |k':128:160:163|) 1) 0)
                            (<= (- |c':127:161:164|) 0)
                            (<= (+ (- (* |c':127:161:164| |k':128:160:163|))
                                     |a':165|
                                     (- (* |k':128:160:163| |b':166|))) 0)))
               (<= (- |K:158:159:162|) 0) (<= (- |k':128:160:163|) 0)
               (not (= (+ (- |c':127:161:164|) |a':165|
                            (- (* |k':128:160:163| |b':166|))) 0))))
(check-sat)
