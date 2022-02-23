import z3
import itertools

from sumsudoku import *

# ----------------------------------------
# Part (b): Unique solutions to Sum-Sudoku
# ----------------------------------------
def create_puzzle():
    g1 = gridvars(('r', 'c', 'x'), n, m)
# ------ IMPLEMENT YOUR CODE HERE --------
    raise NotImplementedError("Formulate a (quantified) SMT instance here.")

# ---- DON'T CHANGE THE CODE BELOW -------
    print (S.check())
    pretty_print(extract_model(S.model(), g1))

if __name__ == '__main__':
    create_puzzle()
