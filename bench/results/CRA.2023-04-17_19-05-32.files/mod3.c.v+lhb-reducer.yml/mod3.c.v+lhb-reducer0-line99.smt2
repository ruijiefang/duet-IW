(declare-const |phi_main__y:163:202| Int)
(declare-const |phi_main____CPAchecker_TMP_0:148:188| Int)
(declare-const |main__x':102:140:177| Int)
(declare-const |__tmp_88_0':324| Int)
(declare-const |__tmp_94_0':101| Int)
(declare-const |phi___tmp_112_0:150:186| Int)
(declare-const |main__y':103:143:180| Int)
(declare-const havoc Int)
(declare-const |main__y':103| Int)
(declare-const __tmp_91_0 Int)
(declare-const |main____CPAchecker_TMP_0':104:145:182| Int)
(declare-const |phi_main__x:149:187| Int)
(declare-const |phi___tmp_94_0:166:199| Int)
(declare-const |__tmp_93_0':100:156:193| Int)
(declare-const |K:341| Int)
(declare-const main____CPAchecker_TMP_0 Int)
(declare-const |main____CPAchecker_TMP_0___0':105:170:207| Int)
(declare-const |main__x':102| Int)
(declare-const |havoc:2:213| Int)
(declare-const |K:138:153:190| Int)
(declare-const |main__x':102:169:206| Int)
(declare-const |__tmp_91_1':321| Int)
(declare-const __tmp_93_0 Int)
(declare-const |__tmp_93_0':100:171:208| Int)
(declare-const |phi___tmp_112_0:165:200| Int)
(declare-const |__tmp_88_1':323| Int)
(declare-const |__tmp_112_0':125| Int)
(declare-const |K:116:139:176| Int)
(declare-const |main____CPAchecker_TMP_0___0':105:159:196| Int)
(declare-const main____CPAchecker_TMP_0___0 Int)
(declare-const |__tmp_91_0':322| Int)
(declare-const |main____CPAchecker_TMP_0___0':105| Int)
(declare-const __tmp_94_0 Int)
(declare-const |__tmp_93_0':100:142:179| Int)
(declare-const |havoc:10:29:99:175:212| Int)
(declare-const |__tmp_93_0':100| Int)
(declare-const |main____CPAchecker_TMP_1':325| Int)
(declare-const |__tmp_112_0':125:158:195| Int)
(declare-const __tmp_88_0 Int)
(declare-const main____CPAchecker_TMP_1___0 Int)
(declare-const |phi___tmp_93_0:167:198| Int)
(declare-const __tmp_91_1 Int)
(declare-const |phi_main__x:164:201| Int)
(declare-const |phi_main____CPAchecker_TMP_0___0:147:189| Int)
(declare-const __tmp_112_0 Int)
(declare-const |main__y':103:160:197| Int)
(declare-const |__tmp_94_0':101:155:192| Int)
(declare-const |main____CPAchecker_TMP_0':104:154:191| Int)
(declare-const |__tmp_94_0':101:144:181| Int)
(declare-const |phi_main____CPAchecker_TMP_0:162:203| Int)
(declare-const |main____CPAchecker_TMP_0':104| Int)
(declare-const |main____CPAchecker_TMP_1___0':326| Int)
(declare-const |main__y':103:172:209| Int)
(declare-const |main__x':102:157:194| Int)
(declare-const |phi___tmp_94_0:151:185| Int)
(declare-const |phi___tmp_93_0:152:184| Int)
(declare-const |main____CPAchecker_TMP_0___0':105:141:178| Int)
(declare-const |havoc:10:29:99:146:183| Int)
(declare-const |__tmp_94_0':101:173:210| Int)
(declare-const main____CPAchecker_TMP_1 Int)
(declare-const |main____CPAchecker_TMP_0':104:174:211| Int)
(declare-const __tmp_88_1 Int)
(declare-const |phi_main____CPAchecker_TMP_0___0:161:204| Int)
(declare-const |K:116:168:205| Int)
(assert (and (or (not (and (<= (- |K:341|) 0) (<= |K:341| 0)))
                   (= (+ |main__y':103| -1) 0))
               (or (not (<= (+ (- |K:341|) 1) 0)) (= (+ |main__y':103| -1) 0))
               (or (not (<= (- |K:341|) 0))
                     (<= (+ (- havoc) |main__x':102| (* -7 |K:341|)) 0))
               (or (not (<= (- |K:341|) 0))
                     (<= (+ havoc (- |main__x':102|) (* 4 |K:341|)) 0))
               (or (and (= |K:341| 0)
                          (= (+ (- |main____CPAchecker_TMP_1___0':326|)
                                  main____CPAchecker_TMP_1___0) 0)
                          (= (+ (- |main____CPAchecker_TMP_1':325|)
                                  main____CPAchecker_TMP_1) 0)
                          (= (+ (- |main____CPAchecker_TMP_0___0':105|)
                                  main____CPAchecker_TMP_0___0) 0)
                          (= (+ (- |main____CPAchecker_TMP_0':104|)
                                  main____CPAchecker_TMP_0) 0)
                          (= (+ (- |main__y':103|) 1) 0)
                          (= (+ havoc (- |main__x':102|)) 0)
                          (= (+ (- |__tmp_112_0':125|) __tmp_112_0) 0)
                          (= (+ (- |__tmp_94_0':101|) __tmp_94_0) 0)
                          (= (+ (- |__tmp_93_0':100|) __tmp_93_0) 0)
                          (= (+ (- |__tmp_88_0':324|) __tmp_88_0) 0)
                          (= (+ (- |__tmp_88_1':323|) __tmp_88_1) 0)
                          (= (+ (- |__tmp_91_0':322|) __tmp_91_0) 0)
                          (= (+ (- |__tmp_91_1':321|) __tmp_91_1) 0))
                     (and (<= (+ (- |K:341|) 1) 0)
                            (<= (+ (mod (+ havoc 2) 3)
                                     (* 2 (mod (+ havoc 1) 3))
                                     (* 2 (mod havoc 3)) -6) 0)
                            (<= (+ (mod (+ havoc 1) 3) (* 2 (mod havoc 3)) -4) 0)
                            (<= (+ (mod (+ havoc 1) 3) -2) 0)
                            (<= (+ (mod (+ havoc 2) 3) -2) 0)
                            (<= (- (mod (+ havoc 2) 3)) 0)
                            (<= (- (mod (+ havoc 1) 3)) 0)
                            (<= (- (mod havoc 3)) 0)
                            (= (+ |main__y':103| -1) 0))) (<= (- |K:341|) 0)
               (< (- |main__y':103|) 0) (= (+ |main__y':103| -1) 0)
               (not (= |havoc:2:213| 0))
               (or (and (or (and (not (= (+ (mod |main__x':102| 3) -1) 0))
                                   (= (+ (mod |main__x':102| 3) -2) 0)
                                   (or (not (<= (- |K:116:139:176|) 0))
                                         (= (+ |main__x':102:140:177|
                                                 (- |K:116:139:176|)
                                                 (- |main__x':102|) -1) 0))
                                   (or (not (and (<= (- |K:116:139:176|) 0)
                                                   (<= |K:116:139:176| 0)))
                                         (= (+ (- |__tmp_93_0':100:142:179|)
                                                 |main____CPAchecker_TMP_0___0':105:141:178|) 0))
                                   (or (not (<= (+ (- |K:116:139:176|) 1) 0))
                                         (= (+ (- |__tmp_93_0':100:142:179|)
                                                 |main____CPAchecker_TMP_0___0':105:141:178|) 0))
                                   (or (not (and (<= (- |K:116:139:176|) 0)
                                                   (<= |K:116:139:176| 0)))
                                         (= |main__y':103:143:180| 0))
                                   (or (not (<= (+ (- |K:116:139:176|) 1) 0))
                                         (= |main__y':103:143:180| 0))
                                   (or (not (and (<= (- |K:116:139:176|) 0)
                                                   (<= |K:116:139:176| 0)))
                                         (= (+ |__tmp_94_0':101:144:181|
                                                 (- |__tmp_93_0':100:142:179|)) 0))
                                   (or (not (<= (+ (- |K:116:139:176|) 1) 0))
                                         (= (+ |__tmp_94_0':101:144:181|
                                                 (- |__tmp_93_0':100:142:179|)) 0))
                                   (or (and (= |K:116:139:176| 0)
                                              (= (+ (- |main____CPAchecker_TMP_0___0':105:141:178|)
                                                      |havoc:2:213|) 0)
                                              (= (+ (- |main____CPAchecker_TMP_0':104:145:182|)
                                                      |havoc:2:213|) 0)
                                              (= (- |main__y':103:143:180|) 0)
                                              (= (+ (- |main__x':102:140:177|)
                                                      |main__x':102| 1) 0)
                                              (= (+ (- |__tmp_94_0':101:144:181|)
                                                      |havoc:2:213|) 0)
                                              (= (+ (- |__tmp_93_0':100:142:179|)
                                                      |havoc:2:213|) 0))
                                         (and (<= (+ (- |K:116:139:176|) 1) 0)
                                                (= (+ (mod (+ |main__x':102|
                                                                1)
                                                           3) -2) 0)
                                                (= (+ |__tmp_93_0':100:142:179|
                                                        (- |main____CPAchecker_TMP_0___0':105:141:178|)) 0)
                                                (= (+ |__tmp_94_0':101:144:181|
                                                        (- |main____CPAchecker_TMP_0___0':105:141:178|)) 0)
                                                (= (+ (mod (+ |main__x':102:140:177|
                                                                -1)
                                                           3) -2) 0)
                                                (= |main__y':103:143:180| 0)))
                                   (<= (- |K:116:139:176|) 0)
                                   (= |main__y':103:143:180| 0)
                                   (= |main__y':103:143:180| 0)
                                   (not (= |havoc:10:29:99:146:183| 0))
                                   (= (+ (mod |main__x':102:140:177| 3) -1) 0)
                                   (= (+ (- |phi___tmp_93_0:152:184|)
                                           |__tmp_93_0':100:142:179|) 0)
                                   (= (+ (- |phi___tmp_94_0:151:185|)
                                           |__tmp_94_0':101:144:181|) 0)
                                   (= (+ (- |phi___tmp_112_0:150:186|)
                                           |havoc:10:29:99:146:183|) 0)
                                   (= (+ (- |phi_main__x:149:187|)
                                           |main__x':102:140:177| 2) 0)
                                   (= (+ (- |phi_main____CPAchecker_TMP_0:148:188|)
                                           |__tmp_94_0':101:144:181|) 0)
                                   (= (+ (- |phi_main____CPAchecker_TMP_0___0:147:189|)
                                           |havoc:10:29:99:146:183|) 0))
                              (and (= (+ (mod |main__x':102| 3) -1) 0)
                                     (= (+ (- |phi___tmp_93_0:152:184|)
                                             |__tmp_93_0':100|) 0)
                                     (= (+ (- |phi___tmp_94_0:151:185|)
                                             |__tmp_94_0':101|) 0)
                                     (= (+ (- |phi___tmp_112_0:150:186|)
                                             |havoc:2:213|) 0)
                                     (= (+ (- |phi_main__x:149:187|)
                                             |main__x':102| 2) 0)
                                     (= (+ (- |phi_main____CPAchecker_TMP_0:148:188|)
                                             |havoc:2:213|) 0)
                                     (= (+ (- |phi_main____CPAchecker_TMP_0___0:147:189|)
                                             |main____CPAchecker_TMP_0___0':105|) 0)))
                          (or (not (and (<= (- |K:138:153:190|) 0)
                                          (<= |K:138:153:190| 0)))
                                (= (+ (- |__tmp_94_0':101:155:192|)
                                        |main____CPAchecker_TMP_0':104:154:191|
                                        (- |phi_main____CPAchecker_TMP_0:148:188|)
                                        |phi___tmp_94_0:151:185|) 0))
                          (or (not (<= (+ (- |K:138:153:190|) 1) 0))
                                (= (+ (- |__tmp_94_0':101:155:192|)
                                        |main____CPAchecker_TMP_0':104:154:191|) 0))
                          (or (not (<= (- |K:138:153:190|) 0))
                                (= (+ |__tmp_93_0':100:156:193|
                                        (- |phi___tmp_93_0:152:184|)) 0))
                          (or (not (<= (- |K:138:153:190|) 0))
                                (= (+ |main__x':102:157:194|
                                        (* -2 |K:138:153:190|)
                                        (- |phi_main__x:149:187|)) 0))
                          (or (not (and (<= (- |K:138:153:190|) 0)
                                          (<= |K:138:153:190| 0)))
                                (= (+ (- |main____CPAchecker_TMP_0___0':105:159:196|)
                                        |__tmp_112_0':125:158:195|
                                        |phi_main____CPAchecker_TMP_0___0:147:189|
                                        (- |phi___tmp_112_0:150:186|)) 0))
                          (or (not (<= (+ (- |K:138:153:190|) 1) 0))
                                (= (+ (- |main____CPAchecker_TMP_0___0':105:159:196|)
                                        |__tmp_112_0':125:158:195|) 0))
                          (or (not (and (<= (- |K:138:153:190|) 0)
                                          (<= |K:138:153:190| 0)))
                                (= |main__y':103:160:197| 0))
                          (or (not (<= (+ (- |K:138:153:190|) 1) 0))
                                (= |main__y':103:160:197| 0))
                          (or (and (= |K:138:153:190| 0)
                                     (= (+ (- |main____CPAchecker_TMP_0___0':105:159:196|)
                                             |phi_main____CPAchecker_TMP_0___0:147:189|) 0)
                                     (= (+ (- |main____CPAchecker_TMP_0':104:154:191|)
                                             |phi_main____CPAchecker_TMP_0:148:188|) 0)
                                     (= (- |main__y':103:160:197|) 0)
                                     (= (+ (- |main__x':102:157:194|)
                                             |phi_main__x:149:187|) 0)
                                     (= (+ (- |__tmp_112_0':125:158:195|)
                                             |phi___tmp_112_0:150:186|) 0)
                                     (= (+ (- |__tmp_94_0':101:155:192|)
                                             |phi___tmp_94_0:151:185|) 0)
                                     (= (+ (- |__tmp_93_0':100:156:193|)
                                             |phi___tmp_93_0:152:184|) 0))
                                (and (<= (+ (- |K:138:153:190|) 1) 0)
                                       (= (+ (mod |phi_main__x:149:187| 3) -1) 0)
                                       (= (+ (- |main____CPAchecker_TMP_0___0':105:159:196|)
                                               |__tmp_112_0':125:158:195|) 0)
                                       (= (+ (- |__tmp_94_0':101:155:192|)
                                               |main____CPAchecker_TMP_0':104:154:191|) 0)
                                       (= |main__y':103:160:197| 0)
                                       (= (+ (mod (+ |main__x':102:157:194|
                                                       -2)
                                                  3) -1) 0)))
                          (<= (- |K:138:153:190|) 0)
                          (= |main__y':103:160:197| 0)
                          (= |main__y':103:160:197| 0)
                          (= (+ (- |phi___tmp_93_0:167:198|)
                                  |__tmp_93_0':100:156:193|) 0)
                          (= (+ (- |phi___tmp_94_0:166:199|)
                                  |__tmp_112_0':125:158:195|) 0)
                          (= (+ (- |phi___tmp_112_0:165:200|)
                                  |__tmp_112_0':125:158:195|) 0)
                          (= (+ (- |phi_main__x:164:201|)
                                  |main__x':102:157:194|) 0)
                          (= (+ (- |phi_main__y:163:202|)
                                  |main__y':103:160:197|) 0)
                          (= (+ (- |phi_main____CPAchecker_TMP_0:162:203|)
                                  |__tmp_112_0':125:158:195|) 0)
                          (= (+ (- |phi_main____CPAchecker_TMP_0___0:161:204|)
                                  |main____CPAchecker_TMP_0___0':105:159:196|) 0))
                     (and (not (= (+ (mod |main__x':102| 3) -1) 0))
                            (= (+ (mod |main__x':102| 3) -2) 0)
                            (= (+ (- |phi___tmp_93_0:167:198|) |havoc:2:213|) 0)
                            (= (+ (- |phi___tmp_94_0:166:199|) |havoc:2:213|) 0)
                            (= (+ (- |phi___tmp_112_0:165:200|)
                                    |__tmp_112_0':125|) 0)
                            (= (+ (- |phi_main__x:164:201|) |main__x':102| 1) 0)
                            (= (- |phi_main__y:163:202|) 0)
                            (= (+ (- |phi_main____CPAchecker_TMP_0:162:203|)
                                    |havoc:2:213|) 0)
                            (= (+ (- |phi_main____CPAchecker_TMP_0___0:161:204|)
                                    |havoc:2:213|) 0)))
               (or (not (<= (- |K:116:168:205|) 0))
                     (= (+ |main__x':102:169:206| (- |K:116:168:205|)
                             (- |phi_main__x:164:201|)) 0))
               (or (not (and (<= (- |K:116:168:205|) 0)
                               (<= |K:116:168:205| 0)))
                     (= (+ (- |__tmp_93_0':100:171:208|)
                             |main____CPAchecker_TMP_0___0':105:170:207|
                             (- |phi_main____CPAchecker_TMP_0___0:161:204|)
                             |phi___tmp_93_0:167:198|) 0))
               (or (not (<= (+ (- |K:116:168:205|) 1) 0))
                     (= (+ (- |__tmp_93_0':100:171:208|)
                             |main____CPAchecker_TMP_0___0':105:170:207|) 0))
               (or (not (and (<= (- |K:116:168:205|) 0)
                               (<= |K:116:168:205| 0)))
                     (= (+ |main__y':103:172:209| (- |phi_main__y:163:202|)) 0))
               (or (not (<= (+ (- |K:116:168:205|) 1) 0))
                     (= |main__y':103:172:209| 0))
               (or (not (and (<= (- |K:116:168:205|) 0)
                               (<= |K:116:168:205| 0)))
                     (= (+ |__tmp_94_0':101:173:210|
                             (- |__tmp_93_0':100:171:208|)
                             (- |phi___tmp_94_0:166:199|)
                             |phi___tmp_93_0:167:198|) 0))
               (or (not (<= (+ (- |K:116:168:205|) 1) 0))
                     (= (+ |__tmp_94_0':101:173:210|
                             (- |__tmp_93_0':100:171:208|)) 0))
               (or (and (= |K:116:168:205| 0)
                          (= (+ (- |main____CPAchecker_TMP_0___0':105:170:207|)
                                  |phi_main____CPAchecker_TMP_0___0:161:204|) 0)
                          (= (+ (- |main____CPAchecker_TMP_0':104:174:211|)
                                  |phi_main____CPAchecker_TMP_0:162:203|) 0)
                          (= (+ (- |main__y':103:172:209|)
                                  |phi_main__y:163:202|) 0)
                          (= (+ (- |main__x':102:169:206|)
                                  |phi_main__x:164:201|) 0)
                          (= (+ (- |__tmp_94_0':101:173:210|)
                                  |phi___tmp_94_0:166:199|) 0)
                          (= (+ (- |__tmp_93_0':100:171:208|)
                                  |phi___tmp_93_0:167:198|) 0))
                     (and (<= (+ (- |K:116:168:205|) 1) 0)
                            (= (+ (mod |phi_main__x:164:201| 3) -2) 0)
                            (= |phi_main__y:163:202| 0)
                            (= (+ |__tmp_93_0':100:171:208|
                                    (- |main____CPAchecker_TMP_0___0':105:170:207|)) 0)
                            (= (+ |__tmp_94_0':101:173:210|
                                    (- |main____CPAchecker_TMP_0___0':105:170:207|)) 0)
                            (= (+ (mod (+ |main__x':102:169:206| -1) 3) -2) 0)
                            (= |main__y':103:172:209| 0)))
               (<= (- |K:116:168:205|) 0) (= |main__y':103:172:209| 0)
               (= |main__y':103:172:209| 0) (= |havoc:10:29:99:175:212| 0)
               (= |main__y':103:172:209| 0)
               (= (ite (= (mod |main__x':102:169:206| 3) 0) 1 0) 0)))
(check-sat)
