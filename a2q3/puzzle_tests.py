import unittest
from a2q3.verbal_arithmetic import solve

class PuzzleTests (unittest.TestCase):

    def setUp (self):
        """Reset Z3 context between tests"""
        import z3
        z3._main_ctx = None
    def tearDown (self):
        """Reset Z3 context after test"""
        import z3
        z3._main_ctx = None
        
    def test_1 (self):
        """NEED + YOUR = MONEY"""
        res = solve ('SEND', 'MORE', 'MONEY')
        self.assertEquals (res, (9567, 1085, 10652))
    def test_2 (self):
        """LIKE + YOUR = MONEY"""
#	self.tearDown()
        res = solve ('LIKE', 'YOUR', 'MONEY')
        self.assertEquals  (res,(2693, 8045, 10738))

    def test_3 (self):
        """NEED + YOUR = MONEY"""
	res = solve ('NEED', 'YOUR', 'MONEY')
        self.assertEquals (res, (7668, 3095, 10763))

    def test_4 (self):
        """NO ANSWER"""
        res  = solve('HATE','YOUR','MONKEY')
	self.assertEquals (res,None)
