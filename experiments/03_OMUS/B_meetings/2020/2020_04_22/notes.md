# Notes

## Next steps

AIJournal :

- Didn't see any author contributions in the submission process.
- Check bart comments and incorporate comments from today's meeting and review notes.

OMUS

- Continue OMUS and apply it on CNF problems

## OMUS

- Initial proof it works for SMUS example
- For more complex CNF formulas it loops for a very long time => hitting set is always not finding a solution
- Optimization:
  - instead of using the MSS and taking the complement of that one, we just take the complement of F'
  - Can we select the lowest cost clauses (top-x clauses) to generate OMUS ?
    - Problem: we don't have any guarantee about the clauses that will be used...
- Questions:
  - Can it happen that there is no optimal hitting set ? (No.)

## IJCAI-PRICAI Review

### Demo

- slide bar to navigate together with/instead of prev-next
- abstract a bit too long
- Be able to specify new puzzles ?
- The presentation of the demo should be about presenting the whole pipeline, but emphasize the explanation generation aspect with further explanations using nested explanations.

### AIJournal

- Verify XAI motivates zebra puzzles enough :
---- The introduction should motivate more zebra puzzles.
---- Why Zebra puzzles? What is a Zebra puzzle?
---- Is your approach limited to zebra puzzles?
- Demo:
---- Make sure to emphasize that explanations can be natural language explanations, but since the puzzle is usually solved by solving the grid, we chose to use visual explanations in the logic grid to explain inference steps/decisions.
- Make sure figures are easy enough to read : 
---- Figures are very difficult to read because some texts they contain are too small.

### Reviewer comments

Reviewer #1:

- Reviewer didn't understand that the learning is for the users and not the system (future work ?)

Reviewer #2:

- ok, not very technical.

Reviewer #3:

- Reviewer doesn't understand that the natural language explanation is only a matching to the clues, with boxes filled in the grid as written in the introduction : ... we use this grid, in combination with the original .... 
- is there a way to generate the MUS that has the better plain text explanation? OMUS
---- Yes if we find the OMUS then we can generate a better explanation for some steps.
---- Text explanation is a text matching to the clue used.
- WTF : The contribution is nice but there are some questions
