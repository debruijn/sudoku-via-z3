# sudoku-via-z3
This repository contains code and examples to use Z3 for solving (variant) Sudoku's. It contains two core scripts:
- sudoku_solver_legacy.py, which can solve classic sudoku and variants that restrict based on index only
    - It is heavily based on https://www.gcardone.net/2020-06-03-solving-the-miracle-sudoku-in-z3/ with some minor 
  adjustments to align it with my personal coding habits, and adding windoku/diagonal constraints as an option
- sudoku_solver.py, which extends the above with sandwich constraints
  - This requires to look at the dual problem formulation: instead of "what is on loc i,j", it looks at 
  "where is num N in row i", to find the 1s and 9s. 
  - Instead of using an array of z3.Int's, we need to instead use an z3.Array definition that allows us to use the 
  z3_sum_between function, which otherwise would not be possible

## Future ideas

- Graphically show puzzles: start and solution
- Allow user to graphically enter (and partially solve) a puzzle, and then let this package do the rest
- Use image detection to convert an image to a sudoku that the user can adjust/solve
- More variants (thermo, arrow, etc) and stuff like differently sized sudoku (e.g. 16x16)
