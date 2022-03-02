(set-logic QF_BV) 
(set-option :produce-models true)

(declare-const x (_ BitVec 32))
(declare-const v_0 (_ BitVec 32))
(declare-const ret_1 (_ BitVec 32))
(declare-const v_1 (_ BitVec 32))
(declare-const v_2 (_ BitVec 32))
(declare-const ret_2 (_ BitVec 32))

(assert (ite (bvsgt x (_ bv0 32)) (= v_0 (bvneg x)) (= v_0 x)))
(assert (= ret_1 v_0))
(assert (= v_1 (bvashr x (_ bv31 32))))
(assert (= v_2 (bvxor x v_1)))
(assert (= ret_2 (bvsub v_2 v_1)))
(assert (not (= ret_1 ret_2)))

(check-sat)
(get-model)
; unsat
(exit)