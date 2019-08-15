# Holygrail

This repo is forked from [Jens Claes' Master Thesis](https://github.com/entropitor/thesis).


## Directory Structure
```
.
├── bos                                  This is the main source directory for the final thesis (using framework Blackburn & Bos)
│   └── output                           This directory contains the IDP files used to solve the puzzles
├── deliverables                         The final PDF deliverables for the thesis
├── diary                                A diary including what I did + questions for the Thesis Advisors (Laurent Janssens and Bart Bogaerts)
├── idp                                  Some manual constructed IDP files as investigation in how a translation would look like
├── latex                                The latex files for the different reports
│   ├── paper                              - Paper (english) describing the thesis (Final)
│   ├── thesis                             - Final Thesis (Dutch)
├── poster                               The files for the poster describing the thesis work
│   └── graphviz                           The graphviz files used for the poster
└── src                                  The source code used up until december (not using Blackburn & Bos)
```

## Installing Dependencies
To be able to run the code from Bos, one would need:
  - docker (to run [IDP](https://dtai.cs.kuleuven.be/software/idp), the constraint solver solving the puzzle)
  - NodeJS
  - SWI Prolog
  - jq (command line json handler)

On a debian-like system: sudo apt-get install docker.io nodejs swi-prolog jq

Then, corresponding to the IDP readme: https://dtai.cs.kuleuven.be/krr/files/releases/idp/README-DOCKER.md
```
/etc/init.d/docker start # make sure docker is running on the machine
docker pull krrkul/idp3:latest;```

if you 'Got permission denied' then sudo adduser docker <your user> and restart

## Running the code
### Setup
Move into the `bos/` directory. If you don't want to answers any questions, use the example `cachedAnswers.pl` provided
```sh
cd bos
cp output/cachedAnswers.pl.example output/cachedAnswers.pl
```

### Run
*Be sure to be in the `bos/` directory!*

To actually run a problem such as 'p1' (this will parse everything and try to solve the puzzle as well):
```sh
swipl -g "solvep(p1)" -g halt main.pl
```

To do this for all puzzles:
```sh
swipl -g "solveAll" -g halt main.pl
```

The above commands do not output anything. Remove the '-g halt' from the command line to see the output. Write 'halt.' in the swipl command line to exit afterwards.

E.g. to just test the parsing of a puzzle:
```sh
swipl -g "testAll([p1])" main.pl
```
(then write 'halt.')

## Adding a problem
One can add a problem by adding a fact in `problems.pl`, `problemPosterEvaluation.pl` or `problemsHolyGrail.pl` (last one is preferred).

```prolog
problem(problem_name, problem(NbTypes, NbEntitiesPerType, Sentences, Lexicon)).
```
