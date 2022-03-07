from random import shuffle
import z3

from sumsudoku import *

# ----------------------------------------
# Part (c): Unique solutions to Sum-Sudoku
# ----------------------------------------

# A helper function to choose a remaining unemptied cell in the
# Sum-Sudoku grid to empty.
def choose_cell_to_empty(cells_emptied):
    # Find the cells that are not emptied using set difference between
    # all grid cells and those are already empty.
    remaining_cells = list(
        set([i for i in range(0, n * n)]).difference(set(cells_emptied))
    )

    # Shuffle remaining cells.
    shuffle(remaining_cells)

    # Return the first in the shuffled list.
    return remaining_cells[0]


# A helper function to get all models for a given logical formula.
def get_models(formula, max_models):
    result = []
    s = z3.Solver()
    s.add(formula)

    while len(result) < max_models and s.check() == z3.sat:
        m = s.model()
        result.append(m)
        # Create a new constraint that blocks the current model.
        block = []
        for d in m:
            c = d()
            block.append(c != m[d])
        s.add(z3.Or(block))
    return result


# A predicate to determine if a logical formula has exactly one model,
# meaning it must be unique.
def exactly_one_model(formula):
    return len(get_models(formula, 2)) == 1


def make_puzzle_unique(initial_grid):
    (row_vals, col_vals, grid_vals) = initial_grid
    g1 = gridvars(("r", "c", "x1"), n, m)
    (rs, cs, _, vs) = g1

    # ------ IMPLEMENT YOUR CODE HERE --------

    solution_unique = True
    flags = []
    cells_emptied = []
    last_unique_model = False

    while solution_unique:
        # Define equality constraints for row and column sums.
        rs_constraints = [rs[i] == row_vals[i] for i in range(n)]
        cs_constraints = [cs[i] == col_vals[i] for i in range(n)]

        # Define constraints for all cells that have not been emptied.
        vs_constraints = [
            vs[i] == grid_vals[i] for i in range(n * n) if i not in cells_emptied
        ]

        constraints = rs_constraints + cs_constraints + vs_constraints + [valid(g1)]

        if exactly_one_model(constraints):
            # Pick an arbitrary next cell to remove.
            cell_to_empty = choose_cell_to_empty(cells_emptied)
            cells_emptied.append(cell_to_empty)

            last_unique_model = get_models(constraints, 2)[0]
            flags = [i in cells_emptied for i in range(n * n)]
        else:
            solution_unique = False

        # ---- DON'T CHANGE THE CODE BELOW -------
        pretty_print(extract_model(last_unique_model, g1), flags)


if __name__ == "__main__":
    init_puzzle = solve_sum_sudoku()
    make_puzzle_unique(init_puzzle)
