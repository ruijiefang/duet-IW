(declare-const |havoc:62:91:108:121:149| Int)
(declare-const |phi_y:64:66:94:101:136:163| Int)
(declare-const |phi_return:107:138:165| Int)
(declare-const |havoc:61:93:100:135:162| Int)
(declare-const |phi_x:22:24:144:172| Int)
(declare-const |havoc:61:93:110:123:151| Int)
(declare-const |havoc:17:118:146| Int)
(declare-const |type_err:58:59:68:96:113:127:155| Int)
(declare-const |type_err:58:59:68:96:103:139:166| Int)
(declare-const |havoc:56:67:95:112:125:153| Int)
(declare-const |phi_y:63:65:92:99:134:161| Int)
(declare-const |havoc:0| Int)
(declare-const |havoc:14:131:159| Int)
(declare-const |phi_d:20:143:171| Int)
(declare-const |phi_return:117:126:154| Int)
(declare-const return Int)
(declare-const |havoc:16:132:170| Int)
(declare-const return@pos Int)
(declare-const |phi_return@width:105:142:169| Int)
(declare-const |havoc:8:21:25:145:173| Int)
(declare-const |phi_return@pos:116:128:156| Int)
(declare-const |havoc:56:67:95:102:137:164| Int)
(declare-const |phi_return@pos:106:140:167| Int)
(declare-const |phi_y:64:66:94:111:124:152| Int)
(declare-const return@width Int)
(declare-const |phi_y:63:65:92:109:122:150| Int)
(declare-const |type_err:57:60:69:97:104:141:168| Int)
(declare-const |type_err:57:60:69:97:114:129:157| Int)
(declare-const |phi_d:19:23:119:147| Int)
(declare-const |phi_return@width:115:130:158| Int)
(declare-const |havoc:15:120:148| Int)
(declare-const |havoc:62:91:98:133:160| Int)
(assert (and (<= (+ |havoc:0| -1000000) 0) (<= (+ (- |havoc:0|) -1000000) 0)
               (or (and (= |havoc:17:118:146| 0)
                          (= (+ (- |phi_d:19:23:119:147|) 1) 0))
                     (and (not (= |havoc:17:118:146| 0))
                            (= (- |phi_d:19:23:119:147|) 0)))
               (or (and (not (= |havoc:15:120:148| 0))
                          (or (and (= |havoc:62:91:108:121:149| 0)
                                     (= (- |phi_y:63:65:92:109:122:150|) 0))
                                (and (not (= |havoc:62:91:108:121:149| 0))
                                       (= (+ (- |phi_y:63:65:92:109:122:150|)
                                               1) 0)))
                          (or (and (= |havoc:61:93:110:123:151| 0)
                                     (= (+ (- |phi_y:64:66:94:111:124:152|)
                                             |phi_y:63:65:92:109:122:150| 10) 0))
                                (and (not (= |havoc:61:93:110:123:151| 0))
                                       (= (+ (- |phi_y:64:66:94:111:124:152|)
                                               |phi_y:63:65:92:109:122:150|
                                               -1) 0)))
                          (= (+ (- |phi_return:117:126:154|)
                                  |havoc:56:67:95:112:125:153|) 0)
                          (= (+ (- |phi_return@pos:116:128:156|)
                                  |type_err:58:59:68:96:113:127:155|) 0)
                          (= (+ (- |phi_return@width:115:130:158|)
                                  |type_err:57:60:69:97:114:129:157|) 0))
                     (and (= |havoc:15:120:148| 0)
                            (= (+ return (- |phi_return:117:126:154|)) 0)
                            (= (+ return@pos (- |phi_return@pos:116:128:156|)) 0)
                            (= (+ return@width
                                    (- |phi_return@width:115:130:158|)) 0)))
               (or (and (not (= |havoc:14:131:159| 0))
                          (or (and (= |havoc:62:91:98:133:160| 0)
                                     (= (- |phi_y:63:65:92:99:134:161|) 0))
                                (and (not (= |havoc:62:91:98:133:160| 0))
                                       (= (+ (- |phi_y:63:65:92:99:134:161|)
                                               1) 0)))
                          (or (and (= |havoc:61:93:100:135:162| 0)
                                     (= (+ (- |phi_y:64:66:94:101:136:163|)
                                             |phi_y:63:65:92:99:134:161| 10) 0))
                                (and (not (= |havoc:61:93:100:135:162| 0))
                                       (= (+ (- |phi_y:64:66:94:101:136:163|)
                                               |phi_y:63:65:92:99:134:161| -1) 0)))
                          (= (+ (- |phi_return:107:138:165|)
                                  |havoc:56:67:95:102:137:164|) 0)
                          (= (+ (- |phi_return@pos:106:140:167|)
                                  |type_err:58:59:68:96:103:139:166|) 0)
                          (= (+ (- |phi_return@width:105:142:169|)
                                  |type_err:57:60:69:97:104:141:168|) 0))
                     (and (= |havoc:14:131:159| 0)
                            (= (+ (- |phi_return:107:138:165|)
                                    |phi_return:117:126:154|) 0)
                            (= (+ (- |phi_return@pos:106:140:167|)
                                    |phi_return@pos:116:128:156|) 0)
                            (= (+ (- |phi_return@width:105:142:169|)
                                    |phi_return@width:115:130:158|) 0)))
               (or (and (= |havoc:16:132:170| 0)
                          (= (+ (- |phi_d:20:143:171|) |phi_d:19:23:119:147|) 0))
                     (and (not (= |havoc:16:132:170| 0))
                            (= (+ (- |phi_d:20:143:171|)
                                    |phi_d:19:23:119:147| -1) 0)))
               (or (and (<= |havoc:0| 0)
                          (= (+ (- |phi_x:22:24:144:172|) |havoc:0|) 0))
                     (and (< (- |havoc:0|) 0)
                            (= (+ |havoc:8:21:25:145:173|
                                    (- |phi_x:22:24:144:172|)) 0)))
               (<= |phi_x:22:24:144:172| 0)
               (not (<= |phi_x:22:24:144:172| 0))))
(check-sat)
