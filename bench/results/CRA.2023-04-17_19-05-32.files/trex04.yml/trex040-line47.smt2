(declare-const |phi_d:18:20:121:149| Int)
(declare-const return Int)
(declare-const |phi_y:58:60:87:101:136:163| Int)
(declare-const |phi_y:59:61:89:103:138:165| Int)
(declare-const |havoc:57:86:100:135:162| Int)
(declare-const |x':93:99:147:175| Int)
(declare-const |havoc:15:134:172| Int)
(declare-const |havoc:57:86:110:123:151| Int)
(declare-const |havoc:51:62:90:114:127:155| Int)
(declare-const |havoc:51:62:90:104:139:166| Int)
(declare-const |havoc:56:88:112:125:153| Int)
(declare-const |havoc:13:133:161| Int)
(declare-const |type_err:52:55:64:92:116:131:159| Int)
(declare-const |phi_return@width:107:144:171| Int)
(declare-const |phi_y:59:61:89:113:126:154| Int)
(declare-const return@pos Int)
(declare-const |type_err:52:55:64:92:106:143:170| Int)
(declare-const |K:97:98:146:174| Int)
(declare-const |phi_return@pos:108:142:169| Int)
(declare-const return@width Int)
(declare-const |phi_d:19:145:173| Int)
(declare-const |phi_return:119:128:156| Int)
(declare-const |havoc:56:88:102:137:164| Int)
(declare-const |phi_return:109:140:167| Int)
(declare-const |phi_y:58:60:87:111:124:152| Int)
(declare-const |havoc:14:122:150| Int)
(declare-const |type_err:53:54:63:91:105:141:168| Int)
(declare-const |type_err:53:54:63:91:115:129:157| Int)
(declare-const |havoc:0| Int)
(declare-const |phi_return@pos:118:130:158| Int)
(declare-const |havoc:16:120:148| Int)
(declare-const |phi_return@width:117:132:160| Int)
(assert (and (<= (+ |havoc:0| -1000000) 0) (<= (+ (- |havoc:0|) -1000000) 0)
               (or (and (= |havoc:16:120:148| 0)
                          (= (+ (- |phi_d:18:20:121:149|) 1) 0))
                     (and (not (= |havoc:16:120:148| 0))
                            (= (- |phi_d:18:20:121:149|) 0)))
               (or (and (not (= |havoc:14:122:150| 0))
                          (or (and (= |havoc:57:86:110:123:151| 0)
                                     (= (- |phi_y:58:60:87:111:124:152|) 0))
                                (and (not (= |havoc:57:86:110:123:151| 0))
                                       (= (+ (- |phi_y:58:60:87:111:124:152|)
                                               1) 0)))
                          (or (and (= |havoc:56:88:112:125:153| 0)
                                     (= (+ (- |phi_y:59:61:89:113:126:154|)
                                             |phi_y:58:60:87:111:124:152| 10) 0))
                                (and (not (= |havoc:56:88:112:125:153| 0))
                                       (= (+ (- |phi_y:59:61:89:113:126:154|)
                                               |phi_y:58:60:87:111:124:152|
                                               -1) 0)))
                          (= (+ (- |phi_return:119:128:156|)
                                  |havoc:51:62:90:114:127:155|) 0)
                          (= (+ (- |phi_return@pos:118:130:158|)
                                  |type_err:53:54:63:91:115:129:157|) 0)
                          (= (+ (- |phi_return@width:117:132:160|)
                                  |type_err:52:55:64:92:116:131:159|) 0))
                     (and (= |havoc:14:122:150| 0)
                            (= (+ return (- |phi_return:119:128:156|)) 0)
                            (= (+ return@pos (- |phi_return@pos:118:130:158|)) 0)
                            (= (+ return@width
                                    (- |phi_return@width:117:132:160|)) 0)))
               (or (and (not (= |havoc:13:133:161| 0))
                          (or (and (= |havoc:57:86:100:135:162| 0)
                                     (= (- |phi_y:58:60:87:101:136:163|) 0))
                                (and (not (= |havoc:57:86:100:135:162| 0))
                                       (= (+ (- |phi_y:58:60:87:101:136:163|)
                                               1) 0)))
                          (or (and (= |havoc:56:88:102:137:164| 0)
                                     (= (+ (- |phi_y:59:61:89:103:138:165|)
                                             |phi_y:58:60:87:101:136:163| 10) 0))
                                (and (not (= |havoc:56:88:102:137:164| 0))
                                       (= (+ (- |phi_y:59:61:89:103:138:165|)
                                               |phi_y:58:60:87:101:136:163|
                                               -1) 0)))
                          (= (+ (- |phi_return:109:140:167|)
                                  |havoc:51:62:90:104:139:166|) 0)
                          (= (+ (- |phi_return@pos:108:142:169|)
                                  |type_err:53:54:63:91:105:141:168|) 0)
                          (= (+ (- |phi_return@width:107:144:171|)
                                  |type_err:52:55:64:92:106:143:170|) 0))
                     (and (= |havoc:13:133:161| 0)
                            (= (+ (- |phi_return:109:140:167|)
                                    |phi_return:119:128:156|) 0)
                            (= (+ (- |phi_return@pos:108:142:169|)
                                    |phi_return@pos:118:130:158|) 0)
                            (= (+ (- |phi_return@width:107:144:171|)
                                    |phi_return@width:117:132:160|) 0)))
               (or (and (= |havoc:15:134:172| 0)
                          (= (+ (- |phi_d:19:145:173|) |phi_d:18:20:121:149|) 0))
                     (and (not (= |havoc:15:134:172| 0))
                            (= (+ (- |phi_d:19:145:173|)
                                    |phi_d:18:20:121:149| -1) 0)))
               (or (not (<= (- |K:97:98:146:174|) 0))
                     (= (+ |x':93:99:147:175|
                             (* |K:97:98:146:174| |phi_d:19:145:173|)
                             (- |havoc:0|)) 0))
               (or (and (= |K:97:98:146:174| 0)
                          (= (+ (- |x':93:99:147:175|) |havoc:0|) 0))
                     (and (<= (+ (- |K:97:98:146:174|) 1) 0)
                            (<= (+ (- |havoc:0|) 1) 0)
                            (<= (+ (- |x':93:99:147:175|)
                                     (- |phi_d:19:145:173|) 1) 0)))
               (<= (- |K:97:98:146:174|) 0) (<= |x':93:99:147:175| 0)
               (not (<= |x':93:99:147:175| 0))))
(check-sat)
