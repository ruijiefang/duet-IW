(declare-const havoc Int)
(declare-const |param1':187| Int)
(declare-const |param1':1870| Int)
(declare-const |return':185| Int)
(declare-const |g':184| Int)
(declare-const |param0':186| Int)
(declare-const |param0':1860| Int)
(declare-const |g':1840| Int)
(declare-const |return':1850| Int)
(assert (and (= (+ |param1':187| (- (ite (= havoc 0) 1 0)) (- havoc)) 0)
               (= (+ |g':184| (- (ite (= havoc 0) 1 0)) (- havoc)) 0)
               (= |param0':186| 0) (= |return':185| 0)
               (= (+ |param1':1870| (- (ite (= havoc 0) 1 0)) (- havoc)) 0)
               (= (+ |g':1840| (- (ite (= havoc 0) 1 0)) (- havoc)) 0)
               (= |param0':1860| 0) (= |return':1850| 0) (not (= havoc 0))))
(check-sat)
