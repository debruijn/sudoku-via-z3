import itertools
import sys
import z3


def rows():
    """Returns the indexes of rows."""
    return range(0, 9)


def cols():
    """Returns the indexes of columns."""
    return range(0, 9)


def numbers():
    """Returns the numbers."""
    return range(0, 9)


def sudoku_from_string(s):
    """Builds a sudoku from a string.

    Args:
        s: string representing a sudoku cell by cell from the top row to the
        bottom road. Admissible characters are 0-9 for known values, '.' for
        unknown values, and \n (ignored).

    Returns:
      A dictionary (int, int) -> int representing the known values of the
      puzzle. The first int in the tuple is the row (i.e.: y coordinate),
      the second int is the column (i.e.: x coordinate).
    """
    valid_chars = set([str(x) for x in range(1, 10)])
    valid_chars.add('.')
    sudoku = {}
    if len(s) != 81:
        raise ValueError('wrong input size')
    invalid_chars = set(s).difference(valid_chars)
    if invalid_chars:
        err_str = ', '.join(invalid_chars)
        raise ValueError('unexpected character(s): %s' % err_str)
    for r in rows():
        for c in cols():
            char = s[0]
            if char != '.':
                sudoku[(r, c)] = s[0]
            s = s[1:]
    return sudoku


def read_sudoku(file):
    """Reads a sudoku from a file-like object.

    Args:
        file: file object.

    Returns: dictionary (int, int) -> int. See sudoku_from_string for details.
    """
    invar = ''
    valid_chars = set([str(x) for x in range(1, 10)])
    valid_chars.add('.')
    for line in file:
        line = line.strip()
        invar = invar + line
    return sudoku_from_string(invar)


def solve_sudoku(known_values, variant=None):
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
    """
    # Create a Z3 solver
    s = z3.Solver()
    # Create a matrix of None, which will be replaced by Z3 variables. This
    # is our sudoku.
    cells = [[None for _ in cols()] for _ in rows()]
    for r in rows():
        for c in cols():
            # Z3 variables have a name
            v = z3.Int('c_%d_%d' % (r, c))
            # Keep a reference to the Z3 variable in our sudoku.
            cells[r][c] = v
            # If this cell contains a hint, then add a constraint that force
            # the current variable to be equal to the hint.
            if (r, c) in known_values:
                s.add(v == known_values[(r, c)])

    # This function adds all the constraints of a classic sudoku
    add_constraints(s, cells, variant=variant)

    if s.check() == z3.sat:
        # Retrieve the model from the solver. In this model all the variables
        # are grounded (i.e.: they have a value)
        m = s.model()
        for r in rows():
            for c in cols():
                # Retrieve the grounded value and print it.
                v = m.evaluate(cells[r][c])
                print(v, end=' ')
                # Add vertical spacing for a subgrid
                if (c + 1) % 3 == 0:
                    print('  ', end='')
            print()
            # Add horizontal spacing for a subgrid
            if (r + 1) % 3 == 0:
                print()
        print()


def add_constraints(s, cells, variant=None):
    if variant is None:
        variant = []
    classic_constraints(s, cells)
    if 'miracle' in variant:
        miracle_constraints(s, cells)
    if 'king' in variant:
        king_constraints(s, cells)
    if 'knight' in variant:
        knight_constraints(s, cells)
    if 'consecutive' in variant:
        consecutive_constraints(s, cells)
    if 'diagonal' in variant:
        diagonal_constraints(s, cells)
    if 'windoku' in variant:
        windoku_constraints(s, cells)
    if 'sandwich' in variant:
        sandwich_constraints(s, cells)


def valid_coordinates(c, r):
    """Checks if a column and a row index are within the puzzle bounds.

    Args:
        c: int, column index.
        r: int, row index.

    Returns:
        True if c and r are valid sudoku indexes.
    """
    return (0 <= c <= 8) and (0 <= r <= 8)


def apply_constraints(cells, offsets, symmetrical):
    """Yields all the pairs of cells at a given offset from each other.

    Args:
        cells: a 9x9 list of lists, where each element is a z3.Int instance.
        offsets: a list of relative offsets. Each offset is a (dy, dx) tuple.
                 dy is the row offset, dx is the column offset.
        symmetrical: if true, each pair of cells is yielded only once,
                     otherwise both (cell_a, cell_b) and (cell_b, cell_a) are
                     yielded.

        Yields:
            Two z3.Int references.
    """
    pairs = set()
    for r in rows():
        for c in cols():
            v = cells[r][c]
            for dy, dx in offsets:
                # Get the coordinates of a candidate cell.
                y = r + dy
                x = c + dx
                if not valid_coordinates(y, x):
                    continue
                pair = tuple(sorted([(r, c), (y, x)]))
                if symmetrical and (pair in pairs):
                    continue
                pairs.add(pair)
                t = cells[y][x]
                yield v, t


def miracle_constraints(s, cells):
    """Adds the miracle sudoku constraints to a z3 solver.

    Args:
        s: z3.Solver instance.
        cells: a 9x9 list of lists, where each element is a z3.Int instance.
    """
    king_constraints(s, cells)
    knight_constraints(s, cells)
    consecutive_constraints(s, cells)


def king_constraints(s, cells):
    """Adds the king sudoku constraints to a z3 solver:
        all cells that are separated by a chess king's move
        must be different. The list below does not include vertical and
        horizontal offsets because they are already enforced by the classical
        sudoku constraints.

    Args:
        s: z3.Solver instance.
        cells: a 9x9 list of lists, where each element is a z3.Int instance.
    """
    offsets = list(itertools.product((-1, 1), (-1, 1)))
    for v, t in apply_constraints(cells, offsets, True):
        s.add(v != t)


def knight_constraints(s, cells):
    """Adds the knight sudoku constraints to a z3 solver:
        all cells that are separated by a chess
        knight's move must be different. A knight moves following an L shape,
        where the long bit is 2 cells long and the short bit is 1 cell long.
        The list below includes all the possible orientations.

    Args:
        s: z3.Solver instance.
        cells: a 9x9 list of lists, where each element is a z3.Int instance.
    """
    offsets = ((1, -2), (2, -1), (2, 1), (1, 2), (-1, 2), (-2, 1), (-2, -1),
               (-1, -2))
    for v, t in apply_constraints(cells, offsets, True):
        s.add(v != t)


def consecutive_constraints(s, cells):
    """Adds the consecutive sudoku constraints to a z3 solver:
        two orthogonally adjacent cell cannot contain
        consecutive digits. Note that this relationship is not symmetrical,
        so we ask apply_constraint to return both (cell_a, cell_b) and
        (cell_b, cell_a).

    Args:
        s: z3.Solver instance.
        cells: a 9x9 list of lists, where each element is a z3.Int instance.
    """
    offsets = ((0, -1), (1, 0), (0, 1), (-1, 0))
    for v, t in apply_constraints(cells, offsets, False):
        s.add(t - v != 1)


def diagonal_constraints(s, cells):
    """Adds the diagonal sudoku constraints to a z3 solver.

    Args:
        s: z3.Solver instance.
        cells: a 9x9 list of lists, where each element is a z3.Int instance.
    """
    # All cells on the main diagonal must be distinct.
    diagonal = [cells[r][r] for r in rows()]
    s.add(z3.Distinct(diagonal))

    # All cells on the antidiagonal must be distinct.
    alt_diagonal = [cells[9-r][r] for r in rows()]
    s.add(z3.Distinct(alt_diagonal))


def windoku_constraints(s, cells):
    """Adds the windoku sudoku constraints to a z3 solver.

    Args:
        s: z3.Solver instance.
        cells: a 9x9 list of lists, where each element is a z3.Int instance.
    """
    # All cells in the 3x3 windoku subgrids must be distinct: for each top left cell of
    # each subgrid select all the other cells in the same subgrid.
    offsets = list(itertools.product(range(0, 3), range(0, 3)))
    for r in [1, 5]:
        for c in [1, 5]:
            group_cells = []
            for dy, dx in offsets:
                group_cells.append(cells[r + dy][c + dx])
            s.add(z3.Distinct(group_cells))


def sandwich_constraints(s, cells):

    cells_hor = [[None for _ in numbers()] for _ in rows()]  # Interpretation: y[r][i] is where i is in row r
    for r in rows():
        for i in numbers():
            # Z3 variables have a name
            v = z3.Int('y_%d_%d' % (r, i))
            # Keep a reference to the Z3 variable in our sudoku.
            cells_hor[r][i] = v
            s.add(z3.eq(i, cells[r][cells_hor[r][i]]))
            #  https://stackoverflow.com/questions/49474310/how-to-use-z3-bitvec-or-int-as-an-array-index
            # use z3.Select and replace cells with actual z3 Array


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
        s.add(z3.Distinct(cells[r]))

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
    if len(sys.argv) >= 2:
        with open(sys.argv[1]) as f:
            input_values = read_sudoku(f)
    else:
        input_values = read_sudoku(sys.stdin)
    variant_input = sys.argv[2:] if len(sys.argv) >= 3 else ['classic']
    solve_sudoku(input_values, variant_input)
