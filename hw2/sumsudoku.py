import itertools
import z3
from math import ceil, log

# Parameters for Sum-Sudoku
n = 3
m = 5


def flatten(grid):
    return [item for sublist in grid for item in sublist]


# This function creates the variables.
def gridvars(names, n, m):
    rowsums = [var("%s%d" % (names[0], i)) for i in range(n)]
    colsums = [var("%s%d" % (names[1], i)) for i in range(n)]
    grid = [[var("%s_%d_%d" % (names[2], i, j)) for j in range(n)] for i in range(n)]

    return (rowsums, colsums, grid, flatten(grid))


# ----------------------------------------
# Part (a): Valid solutions to Sum-Sudoku
# ------ IMPLEMENT YOUR CODE HERE --------
def var(name):
    "Create a variable of the appropriate type here."
    return z3.Int(name)


def val(v):
    """Create an SMT literal of the appropriate type that corresponds to the
    Python integer 'v' here."""
    # If you are using integers to represent the grid variables, you can just
    # return v, but if you are using bit-vectors, you will need to use
    # z3.BitVecVal(v, <width>) to construct a bit-vector literal.
    return v


def valid(g):
    """Given the variables 'g' create a formula that encodes validity of the
    sum-sudoku instance for these variables."""
    print(g)

    (rs, cs, vars, _) = g

    # Each cell contains a value in the range 1..m, inclusive.
    cells = [
        z3.And(1 <= vars[i][j], vars[i][j] <= m) for i in range(n) for j in range(n)
    ]

    # Each row contains distinct integers.
    rows = [z3.Distinct(vars[i]) for i in range(n)]

    # Each column contains distinct integers.
    cols = [z3.Distinct([vars[i][j] for i in range(n)]) for j in range(n)]

    # Each row sums to its assigned sum.
    row_sums = [z3.Sum(vars[i]) == rs[i] for i in range(n)]

    # Each column sums to its assigned sum.
    col_sums = [z3.Sum([vars[i][j] for i in range(n)]) == cs[j] for j in range(n)]

    # Conjunct all constraints.
    return z3.And(*(cells + rows + cols + row_sums + col_sums))


# ---- DON'T CHANGE THE CODE BELOW -------
def extract_model(m, g):
    rows = [m.eval(rsi).as_long() for rsi in g[0]]
    cols = [m.eval(csi).as_long() for csi in g[1]]
    grid = [[m.eval(gij).as_long() for gij in gi] for gi in g[2]]
    return (rows, cols, grid)


def pretty_print(g, flags=None):
    (rows, cols, grid) = g
    header = " | ".join(["%3s" % ""] + ["%3d" % ci for ci in cols])
    separator = "-" * len(header)
    print(header)
    print(separator)

    def to_str(v, fi):
        return "%3d" % v if fi else "%3s" % "-"

    for i, gr in enumerate(grid):
        int_values = [rows[i]] + gr
        if flags:
            flags_plus = [True] + flags[i * n : (i + 1) * n]
            zipped_values = itertools.izip(flags_plus, int_values)
            str_values = [to_str(vi, fi) for fi, vi in zipped_values]
        else:
            str_values = ["%3d" % v for v in int_values]

        row = " | ".join(str_values)
        print(row)
    print(separator)


def solve_sum_sudoku():
    g = gridvars(("r", "c", "x"), n, m)
    rs, cs = g[0], g[1]

    S = z3.Solver()
    S.add(valid(g))
    S.add(z3.And(rs[0] == val(8), rs[1] == val(10), rs[2] == val(10)))
    S.add(z3.And(cs[0] == val(8), cs[1] == val(8), cs[2] == val(12)))

    if S.check() == z3.sat:
        model = S.model()
        row_vals = [model.eval(rs_i) for rs_i in g[0]]
        col_vals = [model.eval(cs_i) for cs_i in g[1]]
        grid_vals = [model.eval(gs_i) for gs_i in g[3]]
        pretty_print(extract_model(model, g))
        return (row_vals, col_vals, grid_vals)
    else:
        # should never get here.
        assert False


if __name__ == "__main__":
    solve_sum_sudoku()
