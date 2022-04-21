#!/usr/bin/env python3

class TermConstant:
    def __init__(self, fsym, *args):
        self.fsym = fsym
        self.args = list(args)

    def __repr__(self):
        rep = '('
        for i in range(0, len(self.args)):
            rep += (", " if i else "") + self.args[i]
        rep += ')'
        return rep

    def unify(self, term):
        return term.unifyCons(self)

    def unifyCons(self, cons):
        if not ((self.fsym == cons.fsym) and (len(self.args) == len(cons.args))):
            return False
        for i in range(self.args):
            if not args.unify(cons.args[i]):
                return false
        return True

    def copy(self):
        pass


_tvtimestamp = 0


class TermVar:
    def __init__(self, instance=0):
        global _tvtimestamp
        self.instance = self if not instance else instance
        self.timestamp = _tvtimestamp = _tvtimestamp + 1

    def __repr__(self):
        return repr(self.instance) if self.instance == self else "TermVar(" + self.timestamp + ")"

    def unify(self, term):
        if (self.instance != self):
            return instance.unify(term)
        instance = term
        # Push self to trail
        trail_push(self)
        self.instance = term
        return True

    def unifyCons(self, cons):
        return self.unify(cons)

    def copy(self):
        trail_push(self)
        return TermVar(self.instance)


class Goal:
    def __init__(self, car, cdr):
        self.car = car
        self.cdr = cdr
        pass

    def __repr__(self):
        return repr(self.car) + "" if not cdr else ('; ' + repr(cdr))

    def copy(self):
        return Goal(self.car, 0 if self.cdr else cdr.copy())

    def solve(self, prog, level, tvmap):
        pass


class Clause:
    def __init__(self, head, body):
        self.head = head
        self.body = body

    def __repr__(self):
        return repr(self.head) + " :- " + (repr(self.body) if self.body else 'true')


class TermVarMapping:
    pass


class Trail:
    def __init__(self, head, body):
        self.tcar = head
        self.tcdr = body
        pass

trail = Trail()

def trail_push(tv):
    global trail
    trail = Trail(tv, trail)

def trail_undo(to):
    global trail
    while trail != to:
        trail.tcar.instance = trail.tcar
        trail = trail.tcdr


class Program:
    def __init__(self, pcar, pcdr):
        self.pcar = pcar
        self.pcdr = pcdr


at_app = "app"
at_cons = "cons"
f_nil = TermConstant("nil")
f_1 = TermConstant("1")
f_2 = TermConstant("2")
f_3 = TermConstant("3")

v_x = TermVar()
lhs1 = TermConstant(at_app, f_nil, v_x, v_x)
c1 = Clause(lhs1, 0)

v_l = TermVar()
v_m = TermVar()
v_n = TermVar()
rhs2 = TermConstant(at_app, v_l, v_m, v_n)
lhs2 = TermConstant(at_app, TermConstant(at_cons,
                                 v_x, v_l), v_m,
                TermConstant(at_cons, v_x, v_n))
c2 = Clause(lhs2,  Goal(rhs2, 0))

v_i = TermVar()
v_j = TermVar()
rhs3 = TermConstant(at_app, v_i, v_j,
                TermConstant(at_cons, f_1,
                         TermConstant(at_cons, f_2,
                                  TermConstant(at_cons, f_3, f_nil))))

g1 = Goal(rhs3, 0)

test_p = Program(c1,  Program(c2, 0))
test_p2 = Program(c2,  Program(c1, 0))

varvar = [v_i, v_j]
varname = ["I", "J"]
var_name_map = TermVarMapping(varvar, varname, 2)
