(declare-const havoc Int)
(declare-const |param0':392:417:429| Int)
(declare-const |return':391:419:432| Int)
(declare-const |param1':393:418:430| Int)
(declare-const |param0':392:404:427| Int)
(declare-const |return':391:406:431| Int)
(declare-const |param1':393:405:428| Int)
(declare-const |havoc:3:34:426| Int)
(assert (and (<= (- havoc) 0) (<= (+ havoc -46340) 0)
               (<= (- |havoc:3:34:426|) 0) (<= (+ |havoc:3:34:426| -46340) 0)
               (= (+ |param0':392:404:427| (- havoc)) 0)
               (= |param1':393:405:428| 0)
               (= (+ |param0':392:417:429| (- |havoc:3:34:426|)) 0)
               (= |param1':393:418:430| 0)
               (or (< (+ (- |return':391:419:432|) |return':391:406:431|) 0)
                     (< (+ |return':391:419:432| (- |return':391:406:431|)) 0))
               (< (- havoc) 0) (< (- |havoc:3:34:426|) 0)))
(check-sat)