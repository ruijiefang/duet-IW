(declare-const havoc Int)
(declare-const |K:110:111| Int)
(declare-const |q':95:115| Int)
(declare-const |r':96:112| Int)
(declare-const |b':76:113| Int)
(declare-fun pow (Real Real) Real)
(declare-const |a':75:114| Int)
(declare-const |havoc:1| Int)
(assert (and (not (= (ite (<= (+ (- |havoc:1|) 1) 0) 1 0) 0))
               (or (not (<= (- |K:110:111|) 0))
                     (<= (+ (- havoc) |r':96:112| (* |K:110:111| |havoc:1|)) 0))
               (or (not (<= (- |K:110:111|) 0))
                     (<= (+ |b':76:113| (- havoc) |r':96:112|) 0))
               (or (not (<= (- |K:110:111|) 0))
                     (<= (+ (- havoc) |r':96:112| |K:110:111|) 0))
               (or (not (<= (- |K:110:111|) 0))
                     (<= (+ (- |q':95:115|) |a':75:114|) 0))
               (or (not (<= (- |K:110:111|) 0))
                     (<= (+ (- |q':95:115|) |K:110:111|) 0))
               (or (and (= |K:110:111| 0) (= (- |b':76:113|) 0)
                          (= (- |a':75:114|) 0)
                          (= (+ havoc (- |r':96:112|)) 0)
                          (= (- |q':95:115|) 0))
                     (and (<= (+ (- |K:110:111|) 1) 0) (= (+ (pow 2 0) -1) 0)
                            (<= (+ (- havoc) |havoc:1|) 0)
                            (<= (+ (- havoc) 1) 0)
                            (= (+ |b':76:113| (- havoc) |r':96:112|
                                    (* |q':95:115| |havoc:1|)
                                    (- (* |a':75:114| |havoc:1|))) 0)
                            (= (+ (pow 2 0) -1) 0)
                            (<= (+ (* -2 |b':76:113|) havoc
                                     (- (* |q':95:115| |havoc:1|))
                                     (* |a':75:114| |havoc:1|) 1) 0)
                            (<= (+ (- |b':76:113|) |havoc:1|) 0)
                            (<= (+ (- |q':95:115|) |a':75:114|) 0)
                            (<= (+ (- (* |q':95:115| |b':76:113|))
                                     (* |a':75:114| |b':76:113|)
                                     (- (* |q':95:115| |r':96:112|))
                                     (* |a':75:114| |r':96:112|)
                                     (* |q':95:115| |havoc:1|)
                                     (- (* |a':75:114| |havoc:1|))) 0)
                            (<= (+ |q':95:115| (- |a':75:114|)
                                     (- (* |q':95:115| |b':76:113|))
                                     (* |a':75:114| |b':76:113|)
                                     (- (* |q':95:115| |r':96:112|))
                                     (* |a':75:114| |r':96:112|)) 0)
                            (<= (+ (- |a':75:114|) 1) 0)
                            (<= (+ |b':76:113| (- havoc)
                                     (* |q':95:115| |havoc:1|)
                                     (- (* |a':75:114| |havoc:1|))) 0)))
               (<= (- |K:110:111|) 0) (<= (- |q':95:115|) 0)
               (<= (- |a':75:114|) 0) (<= (- |b':76:113|) 0)
               (= (+ |b':76:113| (- (* |a':75:114| |havoc:1|))) 0)
               (not (= (+ havoc (- |r':96:112|) (- (* |q':95:115| |havoc:1|))) 0))))
(check-sat)
