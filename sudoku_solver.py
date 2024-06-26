import itertools
import sys
import z3

import sudoku_solver_legacy
from sudoku_solver_legacy import rows, cols, sudoku_from_string
from collections import defaultdict


def read_sudoku(file):
    """Reads a sudoku from a file-like object.

    Args:
        file: file object.

    Returns: dictionary (int, int) -> int. See sudoku_from_string for details.
    """
    input = [line.strip() for line in file]
    puzzle = sudoku_from_string("".join(input[0:9]))

    extra = defaultdict(lambda: defaultdict(dict))
    for row in input[9:]:
        if row.startswith('sw_row'):
            row_clean = row.lstrip('sw_row: ').replace(' ', '').split(',')
            extra['sandwich']['row'] = {i: int(row_clean[i]) for i in range(len(row_clean)) if row_clean[i] != '.'}
        if row.startswith('sw_col'):
            row_clean = row.lstrip('sw_col: ').replace(' ', '').split(',')
            extra['sandwich']['col'] = {i: int(row_clean[i]) for i in range(len(row_clean)) if row_clean[i] != '.'}

    return puzzle, extra


def solve_sudoku(known_values, variant=None, extra_input=None):
    """Solves a sudoku and prints its solution.

    Args:
      known_values: a dictionary of (int, int) -> int representing the known
                    values in a sudoku instance (i.e.: hints). The first int in
                    the tuple of the keys is the row (0-indexed), the second
                    one is the column (0-indexed).
      variant:      a list of strings containing variants, out of:
                    - classic (or empty)
                    - knight
                    - king
                    - consecutive
                    - miracle (= knight + king + consecutive)
                    - diagonal
                    - queen
                    - windoku
      extra_input:  Extra input needed for some variants, such as sandwich sudoku sums
    """
    if extra_input is None:
        extra_input = {}

    # Create a Z3 solver
    s = z3.Solver()
    # Create an array which contains our sudoku.
    cells = z3.Array('cells', z3.IntSort(), z3.ArraySort(z3.IntSort(), z3.IntSort()))
    for r in rows():
        for c in cols():
            # If this cell contains a hint, then add a constraint that force
            # the current variable to be equal to the hint.
            if (r, c) in known_values:
                s.add(cells[r][c] == known_values[(r, c)])

    # This function adds all the constraints of a classic sudoku
    add_constraints(s, cells, variant=variant, extra_input=extra_input)

    if s.check() == z3.sat:
        # Retrieve the model from the solver. In this model all the variables
        # are grounded (i.e.: they have a value)
        m = s.model()
        solution = []
        for r in rows():
            row_solution = []
            for c in cols():
                # Retrieve the grounded value and print it.
                v = m.evaluate(cells[r][c])
                row_solution.append(v)
                print(v, end=' ')
                # Add vertical spacing for a subgrid
                if (c + 1) % 3 == 0:
                    print('  ', end='')
            print()
            solution.append(row_solution)
            # Add horizontal spacing for a subgrid
            if (r + 1) % 3 == 0:
                print()
        print()

        return solution
    else:
        return None


def add_constraints(s, cells, variant=None, extra_input=None):
    if extra_input is None:
        extra_input = {}
    if variant is None:
        variant = []
    classic_constraints(s, cells)
    sudoku_solver_legacy.add_constraints(s, cells, variant)
    if 'sandwich' in variant:
        sandwich_constraints(s, cells, extra_input)


def z3_sum_between(vec, ind_1, ind_9):
    return z3.If(ind_1 < ind_9,
                 z3.Sum([z3.If(z3.And(i > ind_1, i < ind_9), vec[i], 0) for i in cols()]),
                 z3.Sum([z3.If(z3.And(i > ind_9, i < ind_1), vec[i], 0) for i in cols()]))


def sandwich_constraints(s, cells, extra_input):
    for r in rows():
        if r in extra_input['sandwich']['row']:
            ind_1 = z3.Int(f'sw1_r_{r}')
            ind_9 = z3.Int(f'sw9_r_{r}')
            s.add(ind_1 >= 0, ind_9 >= 0)
            s.add(ind_1 < 9, ind_9 < 9)
            s.add(cells[r][ind_1] == 1)
            s.add(cells[r][ind_9] == 9)
            s.add(z3_sum_between(cells[r], ind_1, ind_9) == extra_input['sandwich']['row'][r])
    for c in cols():
        if c in extra_input['sandwich']['col']:
            ind_1 = z3.Int(f'sw1_c_{c}')
            ind_9 = z3.Int(f'sw9_c_{c}')
            s.add(ind_1 >= 0, ind_9 >= 0)
            s.add(ind_1 < 9, ind_9 < 9)
            s.add(cells[ind_1][c] == 1)
            s.add(cells[ind_9][c] == 9)
            col = [cells[r][c] for r in rows()]
            s.add(z3_sum_between(col, ind_1, ind_9) == extra_input['sandwich']['col'][c])


def classic_constraints(s, cells):
    """Adds the classic sudoku constraints to a z3 solver.

    Args:
        s: z3.Solver instance.
        cells: a 9x9 list of lists, where each element is a z3.Int instance.
    """
    # All values must be 1 <= x <= 9.
    for r in rows():
        for c in cols():
            v = cells[r][c]
            s.add(v >= 1)
            s.add(v <= 9)

    # All cells on the same row must be distinct.
    for r in rows():
        row = [cells[r][c] for c in cols()]
        s.add(z3.Distinct(row))

    # All cells on the same column must be distinct.
    for c in cols():
        col = [cells[r][c] for r in rows()]
        s.add(z3.Distinct(col))

    # All cells in a 3x3 subgrid must be distinct: for each top left cell of
    # each subgrid select all the other cells in the same subgrid.
    offsets = list(itertools.product(range(0, 3), range(0, 3)))
    for r in range(0, 9, 3):
        for c in range(0, 9, 3):
            group_cells = []
            for dy, dx in offsets:
                group_cells.append(cells[r + dy][c + dx])
            s.add(z3.Distinct(group_cells))


# Main: read a sudoku from a file or stdin
if __name__ == '__main__':
    # Use: python3 sudoku_solver.py puzzles/classic.pzl classic

    if len(sys.argv) >= 2:
        with open(sys.argv[1]) as f:
            input_values, extra_input = read_sudoku(f)
    else:
        input_values, extra_input = read_sudoku(sys.stdin)
    variant_input = sys.argv[2:] if len(sys.argv) >= 3 else ['classic']
    solve_sudoku(input_values, variant_input, extra_input)
