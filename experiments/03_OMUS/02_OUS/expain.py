
def optimalPropagate(cnf, I=None, focus=None):
    # focus: a set of literals to filter, only keep those of the model
    # SET A FOCUS if many auxiliaries...
    with Solver(bootstrap_with=cnf) as s:
        if I is None or len(I) == 0:
            s.solve()
        elif len(I) > 0:
            s.solve(assumptions=list(I))

        model = set(s.get_model())
        if focus:
            model &= focus
        #print("oP",0,model,time.time()-ts)
        while(True):
            s.add_clause(list(-lit for lit in model))
            solved = s.solve()
            if solved:
                new_model = set(s.get_model())
                if focus:
                    new_model &= focus
                model = model.intersection(new_model)
                #print("oP",c,model,time.time()-ts,new_model)
            else:
                return model

def explain_csp(C, f):
    E = []
    Iend = optimalPropagate(C)
    I = set()
