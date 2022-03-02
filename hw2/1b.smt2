(set-logic QF_BV) 
(set-option :produce-models true)

(declare-const x (_ BitVec 32))
(declare-const y (_ BitVec 32))
(declare-const v_0 (_ BitVec 32))
(declare-const ret_1 (_ BitVec 32))
(declare-const v_1 (_ BitVec 32))
(declare-const v_2 (_ BitVec 32))
(declare-const v_3 (_ BitVec 32))
(declare-const ret_2 (_ BitVec 32))

(assert (ite (bvsge x y) (= v_0 x) (= v_0 y)))
(assert (= v_1 (bvxor x y)))
(assert (= v_2 (bvneg (ite (bvsge x y) (_ bv1 32) (_ bv0 32)))))
(assert (= v_3 (bvand v_1 v_2)))
(assert (= ret_2 (bvxor v_3 y)))
(assert (not (= ret_1 ret_2)))

(check-sat)
; unsat
(exit)