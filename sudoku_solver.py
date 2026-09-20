"""IT5005 Assignment 1: student implementation file.

Implement the functions marked below. Do not modify utils.py or logic_.py.
"""

from utils import *
from logic_ import *


# Do not change this function; it is used to create atomic propositions.
def atom(prefix, r, c, v):
    """prefix is 'Is' or 'Not'. Returns the Expr for e.g. Is3_2_4."""
    return expr(f'{prefix}{r}_{c}_{v}')


def build_general_kb(n, box_h, box_w, givens):
    """Return a PropKB encoding this n x n Sudoku's constraints plus the given
    cells, as general clauses.

    Parameters
    ----------
    n, box_h, box_w : int
    givens : dict[(int, int), int]

    Returns
    -------
    PropKB
    """
    kb = PropKB()

    # Comment the below piece of code if none of the queries reference 'Not' symbol
    for r in range(1, n + 1):
        for c in range(1, n + 1):
            for v in range(1, n + 1):
                kb.tell(atom('Is', r, c, v) |'<=>'| ~atom('Not', r, c, v))

    # Every cell has at least one value from {1, . . . , n}
    for r in range(1, n + 1):
        for c in range(1, n + 1):
            clause = atom('Is', r, c, 1)
            for v in range(2, n + 1):
                clause |= atom('Is', r, c, v)
            kb.tell(clause)

    # Every cell has at most one value from {1, . . . , n}
    for r in range(1, n + 1):
        for c in range(1, n + 1):
            for v1 in range(1, n):
                for v2 in range(v1 + 1, n + 1):
                    clause = atom('Is', r, c, v1) | '==>' | ~atom('Is', r, c, v2)
                    kb.tell(clause)

    # No two cells in the same row hold the same value
    for r in range(1, n + 1):
        for v in range(1, n + 1):
            for c1 in range(1, n):
                for c2 in range(c1 + 1, n + 1):
                    clause = atom('Is', r, c1, v) | '==>' | ~atom('Is', r, c2, v)
                    kb.tell(clause)

    # No two cells in the same column hold the same value
    for c in range(1, n + 1):
        for v in range(1, n + 1):
            for r1 in range(1, n):
                for r2 in range(r1 + 1, n + 1):
                    clause = atom('Is', r1, c, v) | '==>' | ~atom('Is', r2, c, v)
                    kb.tell(clause)

    # No two cells in the same box hold the same value
    for box_r in range(1, n + 1, box_h):
        for box_c in range(1, n + 1, box_w):
            cells = [
                (r, c)
                for r in range(box_r, box_r + box_h)
                for c in range(box_c, box_c + box_w)
            ]

            for v in range(1, n + 1):
                for cell1 in range(len(cells) - 1):
                    for cell2 in range(cell1 + 1, len(cells)):
                        r1, c1 = cells[cell1]
                        r2, c2 = cells[cell2]
                        clause = atom('Is', r1, c1, v) | '==>' | ~atom('Is', r2, c2, v)
                        kb.tell(clause)

    # The givens cells hold their stated values.
    for (row, col), val in givens.items():
        kb.tell(atom('Is', row, col, val))

    return kb


def build_definite_kb(n, box_h, box_w, givens):
    """Return a PropDefiniteKB encoding this n x n Sudoku's constraints plus
    the given cells, using elimination + last-candidate reasoning.

    Parameters
    ----------
    n, box_h, box_w : int
    givens : dict[(int, int), int] -- {(row, col): value}, 1-indexed

    Returns
    -------
    PropDefiniteKB
    """
    raise NotImplementedError(
        'build_definite_kb: encode the puzzle as definite clauses'
    )


def solve_full_grid_fc(n, box_h, box_w, givens):
    """Solve the whole puzzle using build_definite_kb + pl_fc_entails.

    Returns
    -------
    dict[(int, int), int] -- {(row, col): value} for every cell
    """
    raise NotImplementedError(
        'solve_full_grid_fc: solve every cell with forward chaining'
    )


def pl_bc_entails(kb, query):
    """Your own backward-chaining implementation.

    Parameters
    ----------
    kb : PropDefiniteKB
    query : Expr

    Returns
    -------
    bool
    """
    raise NotImplementedError(
        'pl_bc_entails: implement backward chaining, soundly'
    )


def solve_full_grid_bc(n, box_h, box_w, givens):
    """Solve the whole puzzle using build_definite_kb + your own pl_bc_entails.

    For each cell, try each candidate value until pl_bc_entails confirms one
    -- the same per-cell strategy as solve_full_grid_fc, but backed by
    backward chaining instead of a single shared forward-chaining pass.

    Returns
    -------
    dict[(int, int), int] -- {(row, col): value} for every cell
    """
    raise NotImplementedError(
        'solve_full_grid_bc: solve every cell with backward chaining'
    )
