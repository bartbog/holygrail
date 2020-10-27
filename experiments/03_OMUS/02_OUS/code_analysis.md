# Pseudocode - Implementation Analysis

ACTIVE FOLDER = "experiments/03_OMUS/02_OUS/"

## 0. Setup phase [**experiments/03_OMUS/02_OUS/explain.py**  (lines: 68 -> 97)]

Input:

- :params = Execution parameters
- :cnf = list of hard clauses
- :factsToExplain = set of facts to explain
- :weights = indicator variables weights
- :i_0 = initial interpretation (lits in factsToExplain)
- :indicatorVars = list of indicator variables.
  - *constrained*: indicator variables contains the soft clauses to enable or disable clue (trans/bij/clue) clauses
  - *not-constrained*: indicator variables considered empty, and indicator variables are added to every hard clause and added as unit literal soft clauses:
    - indicator vars = [max(lits in hard) + 1, max(lits in hard) + n_hard + 1]

Output:

- clauses = Clause object to manipulate clauses
- sat solver = initialise sat solver bootstrapped hard clauses
- opt solver = initialisation Gurobi opt solver
- grow extension = set extension when growing
- (C)OUS object = central object linked to different components (sat/opt solvers+clauses+grower)

### Execution parameters   [**experiments/03_OMUS/02_OUS/ous_utils.py**  (lines: 263 -> 293)]

***Common parameters possible***

    constrained          [True/False]

    warm_start           [True/False]
    - warm start the OUS explanation loop

    sort_lits ?          [True/False] (don't remember impact of lit sorting)

    post_opt             [True/False]
    - Enable postponing optimization

    post_opt_incremental [True/False]
    - Enable incremental HS computation

    post_opt_greedy      [True/False]
    - Enable Greedy HS computation

    benchmark            [True/False]
    - keep track of execution times

    ispuzzle             [True=puzzle/False=CNF file]

    outputFile           [filename]
    - file to write the explanations sequence for ex: .json

    timeout              [time in secs]
    - explanation generation timeout

    extension            ['default', 'maxsat']

***cOUS specific parameters:***

    -

***OUS parameters:***

    bounded              [True/False]

## 1. Initialization: Warm-up phase

### 1.1 c-OUS warm-up  [**experiments/03_OMUS/02_OUS/ous.py**  (lines: 26 -> 45)]

*Pre-seeding of the constrained OUS.*

1. For every literal:

   1. Grow literal to satisfiable subset (SS).
   2. Add  complement to *H* collection of SS, gurobi solver as constraint

2. Grow set with all derivable facts (+/- lits) to satisfiable subset (SS) + add complement to *H* + constraint to gurobi solver

### 1.2 OUS warm-up

*Not implemented yet.*

    SSOfF ← ∅
    for S ∈ SSs do
        S F ← S ∩ F
        if ¬ ∃ S' ∈ SSOfF : S_F ⊆ S' then
            S_F ← GROW (S_F , F)
            H ← H ∪ {F \ S_F }
            SSOfF ← SSOfF ∪ {S_F }
        end
    end

## 2. Explanation Loop  [**experiments/03_OMUS/02_OUS/explain.py**  (lines: 99 -> 130)]

 1. Compute explanation
 2. Find derived lits used in explanation
 3. Find indicator variable used in explanation
 4. Derived new info:
    - using constraint only, 
    - using derived lits, 
    - focus on all unknown literals (lits of facts to derive), 
    - explanation = E_i (clauses with derived lit used in explanation) + S_i (all constraints used in explanation)
 5. Find N_best [N_i], add to I and clause object
 6. Update Objective weights of satsolver
 7. Add explanation to explanation sequence


Pseudocode:

    E ← hi;
    I end ← OptPropagate(C);
    I ← ∅;
    while I != I_end do
        X ← BestStepC-OUS(C, f, I, I end )
        I best ← I ∩ X;
        C best ← C ∩ X;
        N best ← {I end \ I} ∩ OptPropagate(X);
        add {I best ∧ C best =⇒ N best } to E;
        I ← I ∪ N best ;
    end
    return E;

## 3. c-OUS algorithm


    algorithm BestStepC-OUS(C, f, I, I end ):

    // set p such that exactly one of I end in the hitting set
    // and none of {I end \ I} and none of I  ̄ can be in the
    // hitting set;

    while true do

        // post-poning optimization
        while true do

            // incremental hitting set
            while |H| > 0 do
                F' ← F' + min f element of last MCS in H;
                if ¬ SAT (F' ) then
                    break
                end
                H ← H ∪ {F \ Grow(F' , F)} ;
            end

            // greedy hitting set
            F' ← GreedyHS(H, f);
            if ¬ SAT (F') then
                break
            end
            H ← H ∪ {F \ GROW (F' , F)} ;

        // optimization call
        F' ← CondOptHSOPT(H, f, p)
        if ¬ SAT (F') then
            return F'
        end
        F'' ← GROW (F' , F)
        H ← H ∪ {F \ F''}
    end

### 3.1 Postponing Optimization call [**experiments/03_OMUS/02_OUS/ous.py** (lines: 108 -> 153)]

#### 3.1.1 Incremental Hitting set [**experiments/03_OMUS/02_OUS/ous.py** (lines: 116 -> 140)]

*Add additional constraints to the optimizer*

Two cases possible:

1. If no clause from the indicator variables + derived lits, then add that clause.
2. Else: add clause with least weight to the hitting set.

#### 3.1.2 Greedy Hitting set [**experiments/03_OMUS/02_OUS/ous.py** (lines: 51 -> 106)]

**Needs to be adapted to hard + soft seperation.**

<span style="color:red">

Ideas:
- build vertical set on intialisation of the COUS to skip computation.

</span>

### 3.2 CondOptHSOPT: Optimization Call [**experiments/03_OMUS/02_OUS/ous_utils.py** (lines: 75 -> 142)]

<span style="color:red">
TODO

- Add implementation of @journal cost function.

</span>

**Model initialisation**

    # model parameters
    Threads = 8

Constraints added:

**exactlyOne(-fact for fact in facts)**  [**experiments/03_OMUS/02_OUS/ous_utils.py** line 103]

- only 1 fact explained

**sum(indicator vars + derived lits) >= 1** [**experiments/03_OMUS/02_OUS/ous_utils.py** line 106]

- At least 1 indicator var (at least one constraint used in explanation) + derived literal

**Add complement of Satisfiable set**  [**experiments/03_OMUS/02_OUS/ous_utils.py** line 122]

    add new constraint sum x[j] * hij >= 1

**Compute optimized hs**  [**experiments/03_OMUS/02_OUS/ous_utils.py** line 128]

<span style="color:red">

Ideas:

- Add a Solution Pool to the optimizer? https://www.gurobi.com/documentation/9.0/examples/poolsearch_py.html#subsubsection:poolsearch.py

</span>

**Objective update** [**experiments/03_OMUS/02_OUS/ous_utils.py** line 135]

Attribute (objective coefficients) of variables set to new objective weights

### 3.3 Sat Solver Call [**experiments/03_OMUS/02_OUS/ous_utils.py** line 206]

**Initialization**

    sat solver bootstrapped with hard clauses

**SAT call**  [**experiments/03_OMUS/02_OUS/ous_utils.py** (lines: 215 -> 228)]

    Sat solver uses:
    - assumptions: set as assumptions soft clauses of current hitting set
    - polarities (set_phases): suggest the solver a set of literal truth values based on the full solution model 

**Optimal Propagate**   [**experiments/03_OMUS/02_OUS/ous_utils.py** (lines: 230 -> 257)]

        Solver created because need to add additional clauses to the solver which impacts future calls to the sat solver during (c)OUS solving.

    focus: a set of literals to filter, only keep those of the mode, set a focus if many auxiliaries literals (vars)

<span style="color:red">

    Q: Should we keep assumptions in line 249 or not?

</span>

### 3.4 Grower   [**experiments/03_OMUS/02_OUS/ous_utils.py** (lines: 145 -> 203)]

input:

- :fprime hitting set
- :model model given by sat solver

output:

*grow set of clauses of hitting set **Fprime** into satisfiable set*

**default-grow:**   [**experiments/03_OMUS/02_OUS/ous_utils.py** (lines: 150 -> 151)]

    do nothing

**maxsat:**  [**experiments/03_OMUS/02_OUS/ous_utils.py** (lines: 153 -> 175)]

    - hard clauses: base hard clauses + soft clauses(indicator vars+ Icnf + -Icnf) from hitting set
    - soft clauses: remaining soft clauses
    - weights: weights of inidicator vars + list(1 if literal in derived else Math.INFINTY for literal) + list(1 for literal in -Icnf)

<span style="color:red">

Ideas:

- Greedy grow Maxsat with better growing based on h_counter or H + weights + other puzzle knowledge
  - warm use of sat solver if model is used to grow => less expensive from closer neighborhood
- RC2 stratified what's the diff ?
- other options in PySAT
- set phases?

</span>
