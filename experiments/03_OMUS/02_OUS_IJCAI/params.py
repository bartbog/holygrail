
class BestStepParams(object):
    """
    docstring
    """
    def __init__(self):
        # polarity of sat solver
        self.polarity = False
        self.polarity_initial = False

        # MAXSAT growing
        self.maxsat_polarities = False

        # sat - grow
        self.grow = False
        self.grow_sat = False
        self.grow_subset_maximal = False
        self.subset_maximal_I0 = False
        self.grow_maxsat = False
        self.grow_subset_maximal_actual = False

        # MAXSAT growing
        self.grow_maxsat_full_pos = False
        self.grow_maxsat_full_inv = False
        self.grow_maxsat_full_unif = False
        self.grow_maxsat_initial_pos = False
        self.grow_maxsat_initial_inv = False
        self.grow_maxsat_initial_unif = False
        self.grow_maxsat_actual_pos = False
        self.grow_maxsat_actual_unif = False
        self.grow_maxsat_actual_inv = False

    def checkParams(self):
        if self.grow:
            assert self.grow_sat ^ \
                   self.grow_subset_maximal ^ \
                   self.grow_subset_maximal_actual ^ \
                   self.grow_maxsat, \
                   "Exactly 1 grow mechanism"

        if self.grow_maxsat:
            assert self.grow_maxsat_full_pos ^ \
                    self.grow_maxsat_full_inv ^ \
                    self.grow_maxsat_full_unif ^ \
                    self.grow_maxsat_initial_pos ^ \
                    self.grow_maxsat_initial_inv ^ \
                    self.grow_maxsat_initial_unif ^ \
                    self.grow_maxsat_actual_pos ^ \
                    self.grow_maxsat_actual_unif ^ \
                    self.grow_maxsat_actual_inv, \
                   "Only 1 type of maxsat grow."


class COusParams(BestStepParams):
    """
    docstring
    """
    def __init__(self):
        # reinitialising the HS solver at every OUS call
        super().__init__()
        self.disableConstrained = False


class OusParams(BestStepParams):
    def __init__(self):
        super().__init__()
        self.reuse_SSes = False
        self.sort_literals = False
