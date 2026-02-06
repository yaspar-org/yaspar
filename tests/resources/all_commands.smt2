;; This test input file contains all smt-lib commands
(assert (= 0 0))
(check-sat)
(check-sat-assuming (a b c))