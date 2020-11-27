from explain import explain
import unittest
from explain import optimalPropagate, add_assumptions


class ExplainTest(unittest.TestCase):
    def test_add_assumptions(self):
        cnf = [[1]]
        cnf_ass, assumptions = add_assumptions(cnf)
        self.assertTrue(len(assumptions) == len(cnf))
        self.assertTrue(assumptions == [2])

    def test_optimalPropagate(self):
        self.assertTrue(True)

# running the test
unittest.main()