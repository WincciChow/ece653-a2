# The MIT License (MIT)
# Copyright (c) 2016 Arie Gurfinkel

# Permission is hereby granted, free of charge, to any person obtaining
# a copy of this software and associated documentation files (the
# "Software"), to deal in the Software without restriction, including
# without limitation the rights to use, copy, modify, merge, publish,
# distribute, sublicense, and/or sell copies of the Software, and to
# permit persons to whom the Software is furnished to do so, subject to
# the following conditions:

# The above copyright notice and this permission notice shall be
# included in all copies or substantial portions of the Software.

# THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
# EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
# MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
# NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE
# LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION
# OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION
# WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.

from __future__ import print_function

import wlang.ast
import cStringIO
import sys

import z3

class SymState(object):
    def __init__(self, solver = None):
        # environment mapping variables to symbolic constants
        self.env = dict()
        # path condition
        self.path = list ()
        self._solver = solver
        if self._solver is None:
            self._solver = z3.Solver ()

        # true if this is an error state
        self._is_error = False

    def add_pc (self, *exp):
        """Add constraints to the path condition"""
        self.path.extend (exp)
        self._solver.append (exp)
        
    def is_error (self):
        return self._is_error
    def mk_error (self):
        self._is_error = True
        
    def is_empty (self):
        """Check whether the current symbolic state has any concrete states"""
        res = self._solver.check ()
        return res == z3.sat

    def pick_concerete (self):
        """Pick a concrete state consistent with the symbolic state.
           Return None if no such state exists"""
        res = self._solver.check ()
        if res <> z3.sat:
            return None
        model = self._solver.model ()
        st = dict()
        for d in model.decls():
	   # print (st[k])
            st [d.name()] = model[d]
	   # print (model.eval(v))
        return st
        
    def fork(self):
        """Fork the current state into two identical states that can evolve separately"""
        child = SymState ()
        child.env = dict(self.env)
        child.add_pc (*self.path)
        
        return (self, child)
    
    def __repr__ (self):
        return str(self)
        
    def to_smt2 (self):
        """Returns the current state as an SMT-LIB2 benchmark"""
        return self._solver.to_smt2 ()
    
        
    def __str__ (self):
        buf = cStringIO.StringIO ()
        for k, v in self.env.iteritems():
            buf.write (str (k))
            buf.write (': ')
            buf.write (str (v))
            buf.write ('\n')
        buf.write ('pc: ')
        buf.write (str (self.path))
        buf.write ('\n')
            
        return buf.getvalue ()
                   
class SymExec (wlang.ast.AstVisitor):
    def __init__(self):
        self.states = list()

    def run (self, ast,state,index=0):
        ## set things up andi
        s = self.visit_StmtList (ast,index,state=state)
	self.states.append(s)
        return self.states

    def visit_IntVar (self, node, *args, **kwargs):
        return kwargs['state'].env [node.name]
    
    def visit_BoolConst(self, node, *args, **kwargs):
        return z3.BoolVal (node.val)

    def visit_IntConst (self, node, *args, **kwargs):
        return z3.IntVal (node.val)
    
    def visit_RelExp (self, node, *args, **kwargs):
#	print ("compare")
        lhs = self.visit (node.arg (0), *args, **kwargs)
        rhs = self.visit (node.arg (1), *args, **kwargs)
        if node.op == '<=': return lhs <= rhs
        if node.op == '<': return lhs < rhs
        if node.op == '=': return lhs == rhs
        if node.op == '>=': return lhs >= rhs
        if node.op == '>': return lhs > rhs
        
        assert False

    def visit_BExp (self, node, *args, **kwargs):
        kids = [self.visit (a, *args, **kwargs) for a in node.args]
#	print ("BOLL")
        if node.op == 'not':
            assert node.is_unary ()
            assert len (kids) == 1
            return z3.Not(kids[0])

        fn = None
        base = None
        if node.op == 'and':
            return z3.And(kids)
        elif node.op == 'or':
            return z3.Or(kids)

        assert fn is not None
        
    def visit_AExp (self, node, *args, **kwargs):
        kids = [self.visit (a, *args, **kwargs) for a in node.args]

        fn = None
        base = None

        if node.op == '+':
            fn = lambda x, y: x + y
            
        elif node.op == '-':
            fn = lambda x, y: x - y

        elif node.op == '*':
            fn = lambda x, y: x * y

        elif node.op == '/':
            fn = lambda x, y : x / y
            
        
        assert fn is not None
        return z3.simplify(reduce (fn, kids))
        
    def visit_SkipStmt (self, node, *args, **kwargs):
        pass
    
    def visit_PrintStateStmt (self, node, *args, **kwargs):
        print (kwargs['state'])
	return kwargs['state']

    def visit_AsgnStmt (self, node, *args, **kwargs):
        st = kwargs['state']
        st.env [node.lhs.name] = self.visit (node.rhs, *args, **kwargs)
        return st

    def visit_IfStmt (self, node, *args, **kwargs):
        cond = self.visit (node.cond, *args, **kwargs)
        st = kwargs['state']
        (parent,child) = st.fork()
        parent.add_pc(cond)
        child.add_pc(z3.Not(cond))
        if (parent.is_empty()):
	   # parent.env.update(res_par.env)
           self.visit(node.then_stmt,state = parent)
        if (child.is_empty()):
	   if node.has_else():
	   # print (res_child.env)
	   # child.env.update(res_child.env)
	    	self.visit(node.else_stmt,state = child)
	   self.run(args[0],child,args[1])
        return st
            
    def visit_WhileStmt (self, node, *args, **kwargs):
	if(len(args)!=3):
	    rd = 0;
	else:
	    rd = args[2]
	cond = self.visit(node.cond,*args,**kwargs)
	st = kwargs['state']
	if(rd==10):
		st.add_pc(z3.Not(cond))
		return kwargs['state']
	else:
       		(parent,child) = st.fork()
       		parent.add_pc(cond)
       		child.add_pc(z3.Not(cond))
       		if (parent.is_empty()):
            # execute the body
           		st = self.visit (node.body, state = parent)
            # execute the loop again
            		kwargs['state'] = st
           		self.visit (node, args[0],args[1],rd+1, **kwargs)    
       		if (child.is_empty()):
           # print (res_child.env)
           # child.env.update(res_child.env)
           		self.run(args[0],child,args[1])
            # loop condition is false, don't execute the body
        return kwargs['state']

    def visit_AssertStmt (self, node, *args, **kwargs):
        cond = self.visit (node.cond, *args, **kwargs)
        st = kwargs['state']
        (parent,child) = st.fork()
	parent.add_pc(cond)
        child.add_pc(z3.Not(cond))
	max = args[1]
        if  child.is_empty():
	    print ('Error State:')
	    print (child)
	    st = parent
	    #self.run(args[0],child,max)
	if not parent.is_empty():
            print ('Error State:')
            print (parent)
	    st = child
            #self.run(args[0],child,max)	    
        return st
	     
    def visit_AssumeStmt (self, node, *args, **kwargs):
        cond = self.visit (node.cond, *args, **kwargs)
        st = kwargs['state']
	st.add_pc(cond)
        if not st.is_empty():
            print ("Infeasible path")
	return kwargs['state']

    def visit_HavocStmt (self, node, *args, **kwargs):
        st = kwargs['state']
        for v in node.vars:
            ### assign 0 as the default value
            st.env [v.name] = z3.Int(v.name)
        return st

    def visit_StmtList (self, node, *args, **kwargs):
	if node.stmts is None or len (node.stmts) == 0:
            return self.visit (node, *args, **kwargs)
        st = kwargs['state']
	l = len(args)
	if(l==1):
	    index = args[0]
	else:
	    index = 0
	nodes = node.stmts[index::]
#	print ("len:")
#	print (len(node.stmts))
        nkwargs = dict (kwargs)
        for stmt in nodes:
	    index = index + 1
            nkwargs ['state'] = st
            st = self.visit (stmt, node,index, **nkwargs)
        return st
        
def _parse_args ():
    import argparse
    ap = argparse.ArgumentParser (prog='sym',
                                  description='WLang Interpreter')
    ap.add_argument ('in_file', metavar='FILE', help='WLang program to interpret')
    args = ap.parse_args ()
    return args
    
def main ():
    args = _parse_args ()
    ast = wlang.ast.parse_file (args.in_file)
    st = SymState ()
    sym = SymExec ()
    
    states = sym.run (ast, st)
    print ("size:")
    print (len(states))
    if states is None:
        print ('[symexec]: no output states')
    else:
        count = 0
        for out in states:
	    if out.is_empty():
	#	print (out.pick_concerete())
	    	out.env.update(out.pick_concerete())
            count = count + 1
            print ('[symexec]: symbolic state reached')
            print (out)
        print ('[symexec]: found', count, 'symbolic states')
    return 0

if __name__ == '__main__':
    sys.exit (main ())
                    

