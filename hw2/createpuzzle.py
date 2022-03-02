import z3
import itertools

from sumsudoku import *

# ----------------------------------------
# Part (b): Unique solutions to Sum-Sudoku
# ----------------------------------------
def pairwise_equal(xs, ys):
    return z3.And(*([y == xs[i] for i, y in enumerate(ys)]))


def create_puzzle():
    g1 = gridvars(("r", "c", "x"), n, m)
    # ------ IMPLEMENT YOUR CODE HERE --------

    # Destructure variables.
    (rs, cs, grid, vars) = g1

    # Instantiate the solver.
    S = z3.Solver()

    # Add the constraint that this is _the only_ valid solution.
    # Our approach will apply uniqueness quantification from FOL.
    # To show a unique assignment, we must show the following:
    # 1. There exists an x such that P(x).
    # 2. For all y, P(y) implies y = x

    # Define variables to represent y in the above FOL statement.
    g2 = gridvars(("ry", "cy", "xy"), n, m)
    (rs_y, cs_y, grid_y, vars_y) = g2

    # State that there exists an assignment to all variables
    # such that the puzzle has _at least one_ solution.
    unique = (
        z3.ForAll(
            rs_y + cs_y + flatten(grid_y),
            z3.Implies(
                valid((rs_y, cs_y, grid_y, vars_y)),
                pairwise_equal(rs + cs + flatten(grid), rs_y + cs_y + flatten(grid_y)),
            ),
        ),
    )

    # P(x)
    S.add(valid(g1))
    # For all y, P(y) implies y = x
    S.add(unique)

    # ---- DON'T CHANGE THE CODE BELOW -------
    print(S.check())
    print(S.model())
    pretty_print(extract_model(S.model(), g1))


if __name__ == "__main__":
    create_puzzle()
