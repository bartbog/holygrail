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
			- @Tias+Bart: make sure encoding the same idp problems to cppy
			(Nice to have : Total runtime Performance idp vs python workflow)
		(- Include nested explanations ? @Bart)

	- Reusing MSSes (w/o or w/ models)? (smart structure):
		- Performance evaluation: 
			- How much faster/overhead (not much for small problems, but expensive for big problems) created?
				- How expensive is the first call
				- Plot: call naar OMUS doorheen de sequence met en zonder re-use (x/y steps vs time)

		- Sequence differences: 
			(- What are there a differences with the generated explanation order (cost) with the MSSes?
				- Cost zal hetzelfde zijn, betere )
			- other things ? @Bart

Optimalisatie:

- Kunnen we literals verwijderen die altijd true zijn..?
- Andere optimalisaties? abstract cores? 

## Paper 

- Incrementeel maken
- De workflow maken die fatsoenlijk werkt

### Related works:

- @Bart SMUS (only QMaxsat?) problem
	- How would you implement it ? Programming Language ?
- check evolution of cost of MCSes for OMUS increasing ? (=> LB from here?)
- abstract cores : MaxSAt htting-based potentieel nuttig voor OMUS

## Timeline

T-5 weeks 27/07 - 31/07
Status:

- Finishing cppy to cnf translation
- Encoding started of idp problems into cppy
---- Zo dicht mogelijk bij de originele encodering blijven
- Presentation almost finished

Objectives:

- Preparation full experimental stack ready to run
- Exploring related works OMUS (qmaxsat implementation?)
- Submit presentation to ECAI

Questions:

- integration of the csp-explain algorithm (use additional variables for solving?)
  -  already included in the IDP files: 
     -  (bi) => !....

T-4 weeks 10/08 - 14/08

- Evaluate Master's thesis

Objectives:

- Debugging/finishing integration of the csp-explain algorithm
- Debugging/Finishing experimental stack ready to run
- Writing parts of the paper
- Further Related works exploration

T-3 weeks 17/08 - 21/08

- Running/analyzing/tweaking the experiments
- End of week:
	- First draft ready on paper
		- Incrementaliteit duidelijk in de paper, ...
- Check for bugs/performance increases/better ways to compute parts of the workflow

Bonus:

- Qmaxsat implementation?
---- niet direct (+bonus/nice to have/
---- workflow incrementaliteit

Objectives:

- Abstract ready for submission

T-2 weeks 24/08 - 28/08

- Final experiments run => interpretation of the results
- Increase efficiency of grow algorithm
- writing of the paper

T-1 weeks 31/08 - 04/09

- Polishing of the paper.
- Send to collegues for proofreading

T-4 days  07/09 - 10/09 13:00
