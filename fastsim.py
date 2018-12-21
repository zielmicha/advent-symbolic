import z3, sys, random
from collections import defaultdict

rand = random.Random(42)
simple_instrs = ['addi', 'muli', 'bani', 'bori', 'seti', 'addr', 'mulr', 'banr', 'borr', 'setr']
x_vars = tuple( z3.Int('x%d' % i) for i in range(6) )

def sim_helper(name, a, b):
    if name == 'add': return a + b
    if name == 'mul': return a * b
    if name == 'ban': return a & b
    if name == 'bor': return a | b
    if name == 'set': return a
    assert False

def sim_value(name, data, a, b):
    if name in simple_instrs:
        if name == 'seti':
            return a
        elif name == 'setr':
            return data[a]

        if name.endswith('i'):
            return sim_helper(name[:-1], data[a], b)
        else:
            return sim_helper(name[:-1], data[a], data[b])

    if name[0:2] in ['eq', 'gt']:
        if name[2] == 'i': A = a
        else: A = data[a]
        if name[3] == 'i': B = b
        else: B = data[b]

        if name[0:2] == 'eq':
            p = A==B
        else:
            p = A>B

        if type(p) == bool:
            return 1 if p else 0
        else:
            return z3.If(p, 1, 0)

def sim_instr(name, data, a, b, c):
    data[c] = sim_value(name, data, a, b)
    if type(data[c]) != int:
        assert type(data[c]) != tuple, name
        data[c] = z3.simplify(data[c])

def simulate(line, data):
    instr = line.split()
    assert(type(data[ip]) == int)
    sim_instr(instr[0], data, *map(int, instr[1:]))
    data[ip] += 1

def run(lines, limit):
    data = [0] * 6
    counter = 0

    for i in range(limit):
        pc = data[ip]

        simulate(lines[pc], data)
        print(lines[pc], data)

        if data[ip] >= len(lines): break

def minimize(func, l=0, u=10**9):
    k = z3.Int('k')

    while l + 1 != u:
        m = (l + u) // 2
        s = z3.Solver()
        func(s, k)
        s.add(k <= m)
        if s.check() == z3.sat:
            u = m
        else:
            l = m

    return u

def subs(pattern, new_vars):
    s = z3.Solver()
    s.add([ x==val for x, val in zip(x_vars, new_vars) ])
    s.check()
    m = s.model()
    return [ p if type(p) == int else m.evaluate(p).as_long() for p in pattern ]

class Pattern:
    def __init__(self, start, conds, shift):
        self.start = start
        self.conds = conds
        self.shift = shift

    def matches(self, data):
        s = z3.Solver()
        s.add(self.conds)
        for p, v in zip(self.start, data):
            s.add(p == v)

        if s.check() == z3.sat:
            m = s.model()
            #print(data, self.start, '->', m, tuple( m[v] for v in x_vars ))
            return tuple( m[v] for v in x_vars )

    def use(self, data):
        vars = self.matches(data)
        vars = [ (666 if v is None else v) for v in vars ]
        print(data, vars, self.start)

        def end_cond(s, k):
            new_vars = [ v + k*s for v, s in zip(vars, self.shift) ]
            s.add([ x==val for x, val in zip(x_vars, new_vars) ])
            s.add(z3.Not(self.conds))

        k = minimize(end_cond) - 1
        if k == 0: return None
        print('jumped over', k, 'steps')

        new_vars = [ v + k*s for v, s in zip(vars, self.shift) ]
        new_data = subs(self.start, new_vars)

        return new_data

    def __hash__(self):
        return hash(repr(self))

    def __eq__(self, o):
        return repr(self) == repr(o)

    def __repr__(self):
        return 'Pattern(%s, %s, %s)' % (self.start, self.conds, self.shift)

def find_shifted(conds, states):
    for s1, r1 in states:
        for s2, r2 in states:
            if r1 == r2 or r1[ip] != r2[ip]: continue
            s = z3.Solver()
            s.add(conds)
            #print(s1, s2)
            r = [
                (s1[i] - s2[i]) == (r1[i] - r2[i])
                for i in range(len(s1))
            ]
            s.add(z3.Not(z3.And(r)))
            if s.check() == z3.unsat:
                return Pattern(s1,
                               z3.simplify(z3.And(*conds)),
                               tuple( a2-a1 for (a1,a2) in zip(r1,r2) ))

patterns = set()#defaultdict(set)

def symbolic_run(lines, data):
    data = list(data)
    sym_data = list(x_vars)
    sym_data[ip] = data[ip]

    conds = []

    states = []

    for i in range(12):
        pc = data[ip]

        if pc >= len(lines): break

        print(lines[pc], sym_data)
        simulate(lines[pc], data)
        simulate(lines[pc], sym_data)

        states.append((tuple(sym_data), tuple(data)))

        if type(sym_data[ip]) != int:
            conds.append( z3.simplify(sym_data[ip] == data[ip]) )
            #print('cond', conds[-1])
            sym_data[ip] = data[ip]

        r = find_shifted(conds, states)
        if r:
            patterns.add(r)
            break

        if data[ip] >= len(lines): break

def fast_run(lines, data, limit):
    counter = 0

    for i in range(limit):
        pc = data[ip]

        if pc >= len(lines): break

        matched = None
        if random.randrange(1) == 0:
            matched = [ p for p in patterns if p.matches(data) ]
        if matched:
            p = matched[0]
            res = p.use(data)
            #print(data, '->', res)
            if res:
                data = res
                continue

        simulate(lines[pc], data)
        #print(lines[pc], data)

        if data[ip] >= len(lines): break

    return data

ip = int(input().split()[1])
lines = sys.stdin.read().splitlines()
#run(lines)

def execute():
    data = [0]*6
    data[0] = 0
    for i in range(2000):
        symbolic_run(lines, data)
        print(data)
        print('patterns (%d):' % len(patterns))
        for p in patterns: print(p)
        data = fast_run(lines, data, limit=200)

    print(data)

execute()
