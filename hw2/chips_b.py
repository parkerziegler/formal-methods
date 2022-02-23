import z3

NONE   = z3.BitVecVal(0, 2)
YELLOW = z3.BitVecVal(1, 2)
BLUE   = z3.BitVecVal(2, 2)
RED    = z3.BitVecVal(3, 2)

id_cnt = 0
def newb():
    global id_cnt
    id_cnt += 1
    return z3.Bool('choice%d' % id_cnt)

def get_chip(state):
    (ycnt, bcnt, rcnt) = state
    color = NONE
    color = z3.If(ycnt > 0, YELLOW, color)
    color = z3.If(z3.And(bcnt > 0, z3.Or(newb(), color == NONE)), BLUE, color)
    color = z3.If(z3.And(rcnt > 0, z3.Or(newb(), color == NONE)), RED, color)
    
    ycntp = z3.If(color == YELLOW, ycnt - 1, ycnt)
    bcntp = z3.If(color == BLUE,   bcnt - 1, bcnt)
    rcntp = z3.If(color == RED,    rcnt - 1, rcnt)

    statep = (ycntp, bcntp, rcntp)
    return (color, statep)

def transition_fx(state):
    (color1, statep) = get_chip(state)
    (color2, statep) = get_chip(statep)
    statep = case1(color1, color2, statep)
    statep = case2(color1, color2, statep)
    statep = case3(color1, color2, statep)
    return statep

def valid(p):
    return z3.And(p[0] >= 0, p[1] >= 0, p[2] >= 0)

def terminated(p):
    return z3.And(p[0] == 0, p[1] == 0, p[2] == 0)

def is_anti_reflexive_relation():
    "Prove that relation(x, x) is always false."
    S = z3.Solver()
    state = z3.Int('ycnt'), z3.Int('bcnt'), z3.Int('rcnt')
    S.add(relation(state, state))
    return S.check() == z3.unsat
    
def is_transitive_relation():
    "Prove that relation(x, y) and relation(y, z) implies relation(x, z)."
    S = z3.Solver()
    state1 = z3.Int('ycnt1'), z3.Int('bcnt1'), z3.Int('rcnt1')
    state2 = z3.Int('ycnt2'), z3.Int('bcnt2'), z3.Int('rcnt2')
    state3 = z3.Int('ycnt3'), z3.Int('bcnt3'), z3.Int('rcnt3')
    S.add(relation(state1, state2))
    S.add(relation(state2, state3))
    S.add(z3.Not(relation(state1, state3)))
    return S.check() == z3.unsat

def is_total_relation():
    "Prove that if x != y then x < y or y < x."
    S = z3.Solver()
    state1 = z3.Int('ycnt1'), z3.Int('bcnt1'), z3.Int('rcnt1')
    state2 = z3.Int('ycnt2'), z3.Int('bcnt2'), z3.Int('rcnt2')
    eq = z3.And((state1[0] == state2[0]), 
                (state1[1] == state2[1]), 
                (state1[2] == state2[2]))
    S.add(z3.Not(z3.Or(eq, relation(state1, state2), relation(state2, state1))))
    r = S.check() 
    if r == z3.sat:
        m = S.model()
        print (m.eval(state1[0]), m.eval(state1[1]), m.eval(state1[2]))
        print (m.eval(state2[0]), m.eval(state2[1]), m.eval(state2[2]))
    return r== z3.unsat

def is_well_founded():
    """Prove that forall x y, if x != y and x is not the halt state 
       then relation(x, y) holds"""
    S = z3.Solver()
    state1 = z3.Int('ycnt1'), z3.Int('bcnt1'), z3.Int('rcnt1')
    state2 = z3.Int('ycnt2'), z3.Int('bcnt2'), z3.Int('rcnt2')
    S.add(valid(state1))
    S.add(valid(state2))

    S.add(z3.Not(terminated(state1)))
    S.add(terminated(state2))

    S.add(z3.Not(relation(state1, state2)))
    r = S.check()
    return r == z3.unsat

def check_termination():
    ycnt = z3.Int('yellow_cnt')
    bcnt = z3.Int('blue_cnt')
    rcnt = z3.Int('red_cnt')
    state = (ycnt, bcnt, rcnt)

    S = z3.Solver()

    S.add(valid(state))
    statep = transition_fx(state)
    rel = relation(state, statep)
    trm = terminated(state)

    S.add(z3.Not(z3.Or(rel, trm)))
    return S.check() == z3.unsat

def case1(color1, color2, state):
    raise NotImplementedError("FIXME")

def case2(color1, color2, state):
    raise NotImplementedError("FIXME")

def case3(color1, color2, state):
    raise NotImplementedError("FIXME")

def relation(p, q):
    raise NotImplementedError("FIXME")

if __name__ == '__main__':
    assert is_anti_reflexive_relation()
    assert is_transitive_relation()
    assert is_total_relation()
    assert check_termination()
    assert is_well_founded()
    print ('All good!')
