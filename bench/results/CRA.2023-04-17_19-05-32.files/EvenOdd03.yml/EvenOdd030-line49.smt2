(declare-const |phi_return:432:437:453| Int)
(declare-const |return@pos':411:417:423:439:455| Int)
(declare-const |phi_return@pos:430:440:456| Int)
(declare-const |return':409:416:422:435:451| Int)
(declare-const |param0@pos':412:418:424:441:457| Int)
(declare-const |return@width':413:419:425:443:459| Int)
(declare-const |phi_param0@width:427:446:462| Int)
(declare-const |param0@width':414:420:426:445:461| Int)
(declare-const |phi_return@width:428:444:460| Int)
(declare-const |phi_param0:431:438:454| Int)
(declare-const |type_err:71:72:74| Int)
(declare-const |phi___retres3:433:436:452| Int)
(declare-const |param0':410:415:421:434:450| Int)
(declare-const havoc Int)
(declare-const return Int)
(declare-const |phi___retres3:92:447:463| Int)
(declare-const return@width Int)
(declare-const |phi_param0@pos:429:442:458| Int)
(declare-const return@pos Int)
(declare-const |type_err:70:73:75| Int)
(assert (and (<= (- havoc) 0)
               (or (and (not (= havoc 0)) (not (= (+ havoc -1) 0))
                          (<= (+ (- |return':409:416:422:435:451|)
                                   (* 2 |param0':410:415:421:434:450|)
                                   (- havoc) 1) 0)
                          (<= (+ |param0':410:415:421:434:450| -1) 0)
                          (<= (+ |return':409:416:422:435:451|
                                   (- |param0':410:415:421:434:450|)) 0)
                          (= (+ (- |phi___retres3:433:436:452|)
                                  |return':409:416:422:435:451|) 0)
                          (= (+ (- |phi_return:432:437:453|)
                                  |return':409:416:422:435:451|) 0)
                          (= (+ (- |phi_param0:431:438:454|)
                                  |param0':410:415:421:434:450|) 0)
                          (= (+ (- |phi_return@pos:430:440:456|)
                                  |return@pos':411:417:423:439:455|) 0)
                          (= (+ (- |phi_param0@pos:429:442:458|)
                                  |param0@pos':412:418:424:441:457|) 0)
                          (= (+ (- |phi_return@width:428:444:460|)
                                  |return@width':413:419:425:443:459|) 0)
                          (= (+ (- |phi_param0@width:427:446:462|)
                                  |param0@width':414:420:426:445:461|) 0))
                     (and (or (and (= havoc 0)
                                     (= (+ (- |phi___retres3:92:447:463|) 1) 0))
                                (and (not (= havoc 0)) (= (+ havoc -1) 0)
                                       (= (- |phi___retres3:92:447:463|) 0)))
                            (= (+ |phi___retres3:92:447:463|
                                    (- |phi___retres3:433:436:452|)) 0)
                            (= (+ return (- |phi_return:432:437:453|)) 0)
                            (= (+ (- |phi_param0:431:438:454|) havoc) 0)
                            (= (+ return@pos (- |phi_return@pos:430:440:456|)) 0)
                            (= (+ |type_err:71:72:74|
                                    (- |phi_param0@pos:429:442:458|)) 0)
                            (= (+ return@width
                                    (- |phi_return@width:428:444:460|)) 0)
                            (= (+ |type_err:70:73:75|
                                    (- |phi_param0@width:427:446:462|)) 0)))
               (<= (- |phi___retres3:433:436:452|) 0)
               (not (= (+ (- (mod havoc 2)) |phi___retres3:433:436:452|) 0))))
(check-sat)
