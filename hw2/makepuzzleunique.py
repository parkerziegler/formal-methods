#! /usr/bin/python2.7
import z3

from sumsudoku import *

# ----------------------------------------
# Part (c): Unique solutions to Sum-Sudoku
# ----------------------------------------
def make_puzzle_unique(initial_grid):
    (row_vals, col_vals, grid_vals) = initial_grid
    g1 = gridvars(('r', 'c', 'x1'), n, m)

    S = z3.Solver()
# ------ IMPLEMENT YOUR CODE HERE --------

    raise NotImplementedError, "FIXME"
# Your "result" should be stored in the variable flags. flags should be a
# boolean array of length n*n in row-major order. flags[n*i + j] = false iff 
# row i, column j of the puzzle is "empty."

# ---- DON'T CHANGE THE CODE BELOW -------
    r = S.solve()
    if r == z3.sat:
        pretty_print(extract_model(S.model(), g1), flags)
    else:
        assert False

if __name__ == '__main__':
    init_puzzle = solve_sum_sudoku()
    make_puzzle_unique(init_puzzle)
    
