(declare-const |param1':419:430:440| Int)
(declare-const havoc Int)
(declare-const |return':417:432:442| Int)
(declare-const |havoc:3:24:439| Int)
(declare-const |param0':418:431:441| Int)
(assert (and (< (- havoc) 0) (<= (+ havoc -2147483647) 0)
               (< (- |havoc:3:24:439|) 0)
               (<= (+ |havoc:3:24:439| -2147483647) 0)
               (<= (+ |param1':419:430:440| (- |havoc:3:24:439|)) 0)
               (<= (+ |param0':418:431:441| (- havoc)) 0)
               (< (+ |return':417:432:442| -1) 0) (< (- havoc) 0)
               (< (- |havoc:3:24:439|) 0)))
(check-sat)