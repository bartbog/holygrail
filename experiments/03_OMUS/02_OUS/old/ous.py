
class Clauses(object):
    def __init__(self, wcnf: WCNF, user_vars: list, user_vars_cost: list, initial_interpretation: list, constrainedOUS=True):
        self.constrainedOUS = constrainedOUS
        self._hard = wcnf.hard
        self._soft = wcnf.soft
        self._soft_wght = wcnf.wght
        self._user_vars = user_vars
        self._user_vars_cost = user_vars_cost

        # initialize sat solver with hard clauses
        self.satsolver = Solver(bootstrap_with=wcnf.hard)

        # propagate and find end model (interpretation) from initial
        # interpretation and clues
        self.model = self.optProp(I=initial_interpretation, expl=wcnf.soft)
        self.facts = set(fact if fact in self.model else -fact for fact in user_vars)

        self.nc = len(wcnf.soft) + 2 * len(user_vars)
        self.all_soft_ids = frozenset(range(self.nc))
        self.lit_cnt = Counter(wcnf.unweighted().clauses)

        # soft_wght
        self._obj_weights = []
        # self.all_soft = []
        # self.all_lits = set()
        # self.soft_flat = []
        # self.all_soft_flat = []
        # self.lits = set()
        # self._derived = set()

    def checkSat(self, fprime: set = set()):
        # Preferred values for the lits not in the assumption literals
        polarities = self.model
        self.satsolver.set_phases(literals=polarities)

        # list with assumption literals
        # TODO implement all_soft_flat + make faster
        assumptions = [self.clauses.all_soft_flat[i] for i in fprime]

        solved = self.satsolver.solve(assumptions=assumptions)

        if solved:
            model = self.satsolver.get_model()
            return solved, model
        else:
            return solved, None

    # def add_hard(self, added_clauses):
    #     self._hard += added_clauses
    #     for clause in added_clauses:
    #         self.all_lits |= set(clause)
    #         self.lits |= set(abs(lit) for lit in clause)

    # def add_assumptions(self, assumptions, cost_assumptions=None, f=None):
    #     self._soft += assumptions

    #     for clause in assumptions:
    #         self.all_lits |= set(clause)
    #         self.lits |= set(abs(lit) for lit in clause)

    #     if assumptions is not None:
    #         assert len(assumptions) == len(cost_assumptions), f"Weights ({len(cost_assumptions)}) and clauses ({len(assumptions)}) must be  of same length"
    #         self._soft_weights += cost_assumptions
    #     elif f is not None:
    #         self._soft_weights += [f(cl) for cl in assumptions]
    #     else:
    #         raise "Weights/mapping f not provided"

    #     self.all_soft = self._soft + self._Icnf + self._notIcnf
    #     self.all_soft_ids = set(i for i in range(len(self.all_soft)))
    #     self.soft_flat = [l[0] for l in self._soft]
    #     self.all_soft_flat = [l[0] for l in self._soft + self._Icnf + self._notIcnf]

    # def add_indicators(self, weights=None):
    #     self.lit_counter = Counter()
    #     indHard = []
    #     max_lit = max(self.lits)
    #     indVars = set(i for i in range(max_lit + 1, max_lit + self.nHard + 1))

    #     # update hard clauses with indicator variables
    #     for clause, i in zip(self._hard, indVars):
    #         new_clause = clause + [-i]
    #         indHard.append(new_clause)
    #         self.lit_counter.update(new_clause)
    #         self.lit_counter.update([-i])

    #     self._hard = indHard

    #     # add indicator variables to soft clauses
    #     soft_inds = [[i] for i in indVars]

    #     if weights is None:
    #         self.add_soft(added_clauses=soft_inds, added_weights=[1 for _ in indVars])
    #     else:
    #         self.add_soft(added_clauses=soft_inds, added_weights=weights)

    #     self.all_soft = self._soft + self._Icnf + self._notIcnf
    #     self.all_soft_ids = set(i for i in range(len(self.all_soft)))
    #     self.soft_flat = [l[0] for l in self._soft]
    #     self.all_soft_flat = [l[0] for l in self._soft + self._Icnf + self._notIcnf]
        # return indVars

    def add_I(self, added_I):
        for i in added_I:
            self._Icnf.append([i])
            self._notIcnf.append([-i])

        if self.constrainedOUS:
            # INFINITY because the knowledge is not derived yet
            self._obj_weights += [GRB.INFINITY for _ in added_I]
            # 0 because we want to choose 1 of the neg lits for explanations
            self._obj_weights += [0 for _ in added_I]

        # self.all_soft = self._soft + self._Icnf + self._notIcnf
        # self.all_soft_ids = set(i for i in range(len(self.all_soft)))
        # self.soft_flat = [l[0] for l in self._soft]
        # self.all_soft_flat = [l[0] for l in self._soft + self._Icnf + self._notIcnf]

    def add_derived_Icnf(self, addedI):
        for i in addedI:
            fi = [i]
            fnoti = [-i]

            posi = self._Icnf.index(fi)
            posnoti = self._notIcnf.index(fnoti)

            self._derived.add(posi)
            if self.constrainedOUS:
                self._obj_weights[posi] = 1
                self._obj_weights[len(self._Icnf) + posnoti] = GRB.INFINITY

    # def get_assumption_lit(self):
    #     max_lit = max(self.lits)
    #     self.lits.add(max_lit+1)
    #     return max_lit+1

    # def set_lits(self, Iend):
    #     self.model = set(Iend)

    @property
    def fact_lits(self):
        return [cl[0] for cl in self._Icnf]

    @property
    def hard(self):
        return list(self._hard)

    @property
    def soft(self): 
        return list(self._soft)

    @property
    def nLits(self):
        return len(self.lits)

    @property
    def nHard(self):
        return len(self._hard)

    @property
    def nIndi(self):
        return len(self._soft)

    @property
    def nSoftI(self):
        return len(self._soft) + len(self._obj_weights)

    @property
    def nDerived(self):
        return len(self._derived)

    @property
    def derived_idxs(self):
        return set(self.nIndi + i for i in range(self.derived_idxs))

    @property
    def all_soft_weights(self):
        return self._soft_weights + [1 if i == 0 else i for i in self._obj_weights]

    @property
    def I_idxs(self):
        return set(i for i in range(self.nIndi, self.nIndi + self.nCNFLits))

    @property
    def not_I_idxs(self):
        return list(i for i in range(self.nIndi + self.nCNFLits, self.nSoftI))

    @property
    def obj_weights(self):
        return self._soft_weights + self._obj_weights

    @property
    def nCNFLits(self):
        return len(self._Icnf)


    @property
    def weights(self):
        return [GRB.INFINITY] * len(self._hard) + self._soft_weights

    @property
    def all_clauses(self):
        return self._hard + self._soft

    def __str__(self):
        return f"""
        Clauses:
        \t  hard={[list(cl) for cl in self._hard]},
        \t  soft={[list(cl) for cl in self._soft]},
        \t  Icnf={[list(cl) for cl in self._Icnf]},
        \t -Icnf={[list(cl) for cl in self._notIcnf]},
        \tw_soft={self._soft_weights},
        \t w_obj={self._obj_weights}
        \t  lits={self.lits},
        \t cnter={self.lit_counter}
        \t
        """

    def __del__(self):
        del self._hard
        del self._soft
        del self._soft_weights
        del self.all_soft
        del self.all_soft_ids
        del self.all_lits
        del self.lits
        del self._Icnf
        del self._notIcnf
        del self._derived
        del self._obj_weights
        del self.lit_counter
