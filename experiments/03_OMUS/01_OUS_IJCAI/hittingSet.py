
# gurobi imports
import gurobipy as gp
from gurobipy import GRB


class OptHS(object):
    def __init__(self, f, F, A):
        # Iend + -Iexpl
        # print(F)
        # print("I=", [l for l in F if -l not in F])
        # print("Iend/Iexpl=", [l for l in F if -l in F])
        self.allLits = list(F)
        self.nAllLits = len(self.allLits)

        # optimisation model
        self.opt_model = gp.Model('OptHittingSet')

        # VARIABLE -- OBJECTIVE
        x = self.opt_model.addMVar(
            shape=self.nAllLits,
            vtype=GRB.BINARY,
            obj=[f(l) if l in A else GRB.INFINITY for l in self.allLits],
            name="x")

        self.opt_model.update()

    def addCorrectionSet(self, C: set):
        """Add new constraint of the form to the optimization model,
        mapped back to decision variable lit => x[i].

            sum x[j] * hij >= 1

        Args:
            C (set): set of assumption literals.
        """
        x = self.opt_model.getVars()

        Ci = [self.allLits.index(lit) for lit in C]

        # add new constraint sum x[j] * hij >= 1
        self.opt_model.addConstr(gp.quicksum(x[i] for i in Ci) >= 1)

    def OptHittingSet(self):
        """Compute conditional Optimal hitting set.

        Returns:
            set: Conditional optimal hitting mapped to assumption literals.
        """
        self.opt_model.optimize()

        x = self.opt_model.getVars()
        hs = set(lit for i, lit in enumerate(self.allLits) if x[i].x == 1)

        return hs

    def dispose(self):
        self.opt_model.dispose()


class CondOptHS(object):
    def __init__(self, U: set, Iend: set, I: set):
        """
        # Optimisation model:

        The constrained optimal hitting set is described by:

        - x_l={0,1} is a boolean decision variable if the literal is selected
                    or not.

        - w_l=f(l) is the cost assigned to having the literal in the hitting
                   set (INF otherwise).

        - c_lj={0,1} is 1 (0) if the literal l is (not) present in hitting set j.

        Objective:

             min sum(x_l * w_l) over all l in Iend + (-Iend \ -I)

        Subject to:

            (1) sum x_l * c_lj >= 1 for all hitting sets j.

                = Hitting set must hit all sets-to-hit.

            (2) sum x_l == 1 for l in (-Iend \ -I)

        Args:

            U (set): User variables over a vocabulary V

            Iend (set): Cautious consequence, the set of literals that hold in
                        all models.

            I (set): partial interpretation subset of Iend.

        """
        Iexpl = Iend - I
        notIexpl = set(-lit for lit in Iexpl)

        self.allLits = list(Iend) + list(notIexpl)
        self.nAllLits = len(self.allLits)

        # optimisation model
        self.opt_model = gp.Model('CondOptHittingSet')

        # VARIABLE -- OBJECTIVE
        x = self.opt_model.addMVar(
            shape=self.nAllLits,
            vtype=GRB.BINARY,
            obj=[GRB.INFINITY] * self.nAllLits,
            name="x")

        # CONSTRAINTS
        # every explanation contains 1 neg Lit.
        posnegIexpl = range(len(Iend), self.nAllLits)

        self.opt_model.addConstr(
            x[posnegIexpl].sum() == 1
        )

        # update model
        self.opt_model.update()

    def addCorrectionSet(self, C: set):
        """Add new constraint of the form to the optimization model,
        mapped back to decision variable lit => x[i].

            sum x[j] * hij >= 1

        Args:
            C (set): set of assumption literals.
        """
        x = self.opt_model.getVars()
        Ci = [self.allLits.index(lit) for lit in C]

        # add new constraint sum x[j] * hij >= 1
        self.opt_model.addConstr(gp.quicksum(x[i] for i in Ci) >= 1)

    def CondOptHittingSet(self):
        """Compute conditional Optimal hitting set.

        Returns:
            set: Conditional optimal hitting mapped to assumption literals.
        """
        self.opt_model.optimize()

        x = self.opt_model.getVars()
        hs = set(lit for i, lit in enumerate(self.allLits) if x[i].x == 1)

        return hs

    def updateObjective(self, f, A: set):
        """Update objective of subset A {I + (-Iend\-I )}, a set of assumption
        literals s.t C u A is unsatisfiable.

        Costs of literals in A should be set to f(lit) and others not in A,
        should be set to INF.

        Args:
            f (func): A cost function mapping literal to a int cost (> 0).
            A (set): A set of assumption literals.
        """
        x = self.opt_model.getVars()

        # update the objective weights
        for xi, lit in zip(x, self.allLits):
            if lit in A:
                xi.setAttr(GRB.Attr.Obj, f(lit))
            else:
                xi.setAttr(GRB.Attr.Obj, GRB.INFINITY)

        self.opt_model.update()

    def __del__(self):
        self.opt_model.dispose()