(declare-const |param0':733:916:940| Int)
(declare-const |counter':731:917:943| Int)
(declare-const havoc Int)
(declare-const |param1':734:914:938| Int)
(declare-const |param3':736:913:937| Int)
(declare-const |param2':735:915:939| Int)
(declare-const |return':907:932:942| Int)
(declare-const |param0':908:931:941| Int)
(assert (and (<= (+ (- havoc) 1) 0) (<= (+ havoc -31) 0)
               (= (+ |param1':734:914:938| |param3':736:913:937| -3) 0)
               (= (+ |param2':735:915:939| -3) 0) (= |param0':733:916:940| 0)
               (= (+ |param0':908:931:941| -1) 0)
               (not (= (+ (- |counter':731:917:943|) |return':907:932:942|) 0))))
(check-sat)
