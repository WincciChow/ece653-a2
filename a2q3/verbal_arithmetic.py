import z3
## See https://en.wikipedia.org/wiki/Verbal_arithmetic
## cute: http://mathforum.org/library/drmath/view/60417.html

vars = dict()
def _mk_int_var (x):
    if x not in vars:
        vars[x] = z3.Int (str(x))
    return vars[x]

def mk_var (x):
    return _mk_int_var (x)

def get_vars ():
    return vars.values ()


def solve (s1, s2, s3):
    global vars
    vars = dict()
    s = set()
    X1 = sep(s,s1)
    X2 = sep(s,s2)
    X3 = sep(s,s3)
    X = [ z3.Int('%s' % i) for i in s]
    solver = z3.Solver ()
    for i in X:
        solver.add(i>=0,i<=9)
    t1 = z3.Int('t1')
    t1 = 0
    t2 = z3.Int('t2')
    t2 = 0
    t3 = z3.Int('t3')
    t3 = 0
    t1 = Ath(t1,X1)
    t2 = Ath(t2,X2)
    t3 = Ath(t3,X3)
    solver.add(t1+t2==t3)
    solver.add(z3.Distinct(X))
    res = solver.check ()
    if res == z3.sat:
        m = solver.model()
    	return  (Num(m,X1),Num(m,X2),Num(m,X3))
    elif res == z3.unsat:
        print 'unsat'
    else:
        print 'unknown'

def sep(s,x):
    X = [ '%s' % i for i in list(x)]
    for i in X:
        s.add(i)
    return X
def Ath(t,x):
    for i in x:
        t = z3.Int(i)+t*10
    return t
def Num(m,x):
    t = 0
    for i in x:
        t = m[z3.Int(i)]+t*10
    return z3.simplify(t)


def print_sum (s1, s2, s3):
    s1 = str(s1)
    s2 = str(s2)
    s3 = str(s3)
    print s1.rjust (len(s3) + 1)
    print '+'
    print s2.rjust (len(s3) + 1)
    print ' ' + ('-'*(len(s3)))
    print s3.rjust (len(s3) + 1)

def puzzle (s1, s2, s3):
    print_sum (s1, s2, s3)
    res = solve (s1, s2, s3)
    if res is None:
        print 'No solution'
    else:
        print 'Solution:'
        print_sum (res[0], res[1], res[2])

if __name__ == '__main__':
    puzzle ('SEND', 'MORE', 'MONEY')
