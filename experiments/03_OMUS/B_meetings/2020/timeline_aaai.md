# Meeting Notes 07/12/2020



# Meeting Notes 20/07/2020

- Orthogonaal incrementaliteit van Davies, en SMUS
- QMaxSat
- Explaining Visual sudoku solving

## Experiments: Experimental questions to explore

1. OMUS Experiments

	- Execution time  speed-up before and after incremental:
		- (% of the time optimal hitting set solving, % of the time incremental solving, % of the time greedy hitting set solving)
		(- Number of steps optimal before vs #steps optimal/greedy/incremental after)
		(- @Bart : other ideas ?)

2. CSP experiments:

   - Execution time incremental explain vs non-incremental

     - OMUS eplanation vs previous version:
       - Explanation cost OMUS vs previous journal explanation algon 
       - Encodering must be the same !! 

     - Nice to have : Total runtime Performance idp vs python workflow)
     - Include nested explanations ?

     - Reusing MSSes (w/o or w/ models)? (smart structure):
     - Performance evaluation:
       - How much faster/overhead (not much for small problems, but expensive for big problems) created?
       - How expensive is the first call
       - Plot: call naar OMUS doorheen de sequence met en zonder re-use (x/y steps vs time)

     - Sequence differences:
       - What are there a differences with the generated explanation order (cost) with the MSSes?
         - Cost zal hetzelfde zijn of betere
     - other things ? @Bart

Optimalisatie:

- Kunnen we literals verwijderen die altijd true zijn..?
- Andere optimalisaties? abstract cores? 
- check evolution of cost of MCSes for OMUS increasing ? (=> LB from here?)

<!-- ### Related works: -->

<!-- - @Bart SMUS (only QMaxsat?) problem
	- How would you implement it ? Programming Language ? -->

## Timeline

### Status implementatie:

- preseeding actief

- OUS code traag na +- 6 stappen
  - checksat heel goedkoop
  - aan passing checksat => veel sneller voor de 13 eerste stappen (zoekt expl met 2 constraints => traag)
  - postponing optimimsatie ?

### Status Experimenten

- Finishing cppy to cnf translation
- Encoding idp problems into cppy:
  - only origin puzzle (p5)
  - ***Zo dicht mogelijk bij de originele encodering blijven***

### Week 07- 11 Dec

- Functional implementation of cOUS, ready to run on instances.
- Contributions
- Initial experiments:
  - Check for bugs/performance increases/better ways to compute parts of the workflow

Research note:

- Design of experiments: Bencharmk data sets,  Selection of parameters, ...
- Pseudocode:
  - Resterende algorithme toevoegen + uitleg input/output.
  - Uitleg.
- Optmisatie model afwerken.
  - description + cost function.
- Structure of the paper

Week 07 Dec - 11 Dec

Objectives End of week:
- Experimental stack ready to run on HPC

Week 14 Dec - 18 Dec
- Running/analyzing/tweaking the experiments
- Related works section
- Increase efficiency of parts of the algorithm

Week 21 Dec - 25 Dec
- Experimenten klaar, interpretatie van de resultaten.
- Abstract ready
- First rough draft

Week 28 Dec - 1 Jan
- Holiday ?

Week 4 Jan  - 8 Jan
- Polishing of the paper.
- Send to collegues for proofreading

Objectives:
- Abstract ready for submission

Week 11 Jan - 18 Jan
- Incorporate comments paper