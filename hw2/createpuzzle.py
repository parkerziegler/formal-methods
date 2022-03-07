import z3
from sumsudoku import *
from timeit import default_timer as timer

# ----------------------------------------
# Part (b): Unique solutions to Sum-Sudoku
# ----------------------------------------
# A helper function to verify that x = y for all pairs in xs, ys.
def pairwise_equal(xs, ys):
    return z3.And(*([xs[i] == y for i, y in enumerate(ys)]))


def create_puzzle():
    start = timer()
    g1 = gridvars(("r", "c", "x"), n, m)
    # ------ IMPLEMENT YOUR CODE HERE --------

    # Destructure the row sum, column sum, and cell variables.
    (rs, cs, _, vs) = g1

    # Instantiate the solver.
    S = z3.Solver()

    # Our approach to create a unique puzzle will apply uniqueness quantification from FOL.
    # To show a unique assignment, we must show the following:
    # 1. There exists an x such that P(x).
    # 2. For all y, P(y) implies y = x.
    #
    # P(x) in this case is valid(x), where x represents the 4-tuple
    # of variables.

    # P(x)
    S.add(valid(g1))

    # Define variables to represent y in the above FOL statement.
    g2 = gridvars(("ry", "cy", "xy"), n, m)
    (rs_y, cs_y, grid_y, vs_y) = g2

    # State that for all assignments ry_0, ry_1, ry_2, cy_0, cy_1, cy_2,
    # if the assignment is valid then all puzzle variables rs_y, cs_, vs_y
    # are equal to their counterparts rs, cs, and vs. Therefore, this
    # is the only solution for the generated puzzle.
    unique = (
        z3.ForAll(
            rs_y + cs_y,
            z3.Implies(
                valid((rs_y, cs_y, grid_y, vs_y)),
                pairwise_equal(rs + cs + vs, rs_y + cs_y + vs_y),
            ),
        ),
    )

    # For all y, P(y) implies y = x
    S.add(unique)

    # ---- DON'T CHANGE THE CODE BELOW -------
    print(S.check())
    pretty_print(extract_model(S.model(), g1))
    end = timer()
    print(f"Completed in: {(end - start) * 1000}ms.")


if __name__ == "__main__":
    create_puzzle()
