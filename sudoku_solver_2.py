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
    raise NotImplementedError(
        'build_general_kb: encode the puzzle as general clauses'
    )


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


    newKB = PropDefiniteKB()

    for r in range(1,n+1):
        for c in range(1,n+1):
            if (r,c) in givens:
                newKB.tell(atom('Is', r, c, givens[(r,c)]))

            
            boxBaseCol = (c-1)//box_w * box_w + 1
            boxBaseRow = (r-1)//box_h * box_h + 1
            
            for num in range(1,n+1):
                current = atom('Is', r, c, num)

                rowClauses = []
                colClauses = []
                boxClauses = []
                otherClauses = []
                for n2 in range(1,n+1):
                    if c != n2:
                        rowClauses.append(atom('Not', r, n2, num))
                        newKB.tell(Expr('==>', current, atom('Not', r, n2, num)))
                    if r != n2:
                        colClauses.append(atom('Not', n2, c, num))
                        newKB.tell(Expr('==>', current, atom('Not', n2, c, num)))
                    if num != n2:
                        otherClauses.append(atom('Not', r, c, n2))
                        newKB.tell(Expr('==>', current, atom('Not', r, c, n2)))

                for currRow in range(boxBaseRow, boxBaseRow + box_h):
                    for currCol in range(boxBaseCol, boxBaseCol + box_w):
                        if currRow == r and currCol == c:
                            continue
                        boxClauses.append(atom('Not', currRow, currCol, num))

                        if currRow != r and currCol != c:
                            newKB.tell(Expr('==>', current, atom('Not', currRow, currCol, num)))


                newRowClause = associate('&', rowClauses)
                newKB.tell(Expr('==>', newRowClause, atom('Is', r, c, num)))

                newColClause = associate('&', colClauses)
                newKB.tell(Expr('==>', newColClause, atom('Is', r, c, num)))

                newBoxClause = associate('&', boxClauses)
                newKB.tell(Expr('==>', newBoxClause, atom('Is', r, c, num)))

                newOtherClause = associate('&', otherClauses)
                newKB.tell(Expr('==>', newOtherClause, atom('Is', r, c, num)))

    return newKB


    # raise NotImplementedError(
    #     'build_definite_kb: encode the puzzle as definite clauses'
    # )


def solve_full_grid_fc(n, box_h, box_w, givens):
    """Solve the whole puzzle using build_definite_kb + pl_fc_entails.

    Returns
    -------
    dict[(int, int), int] -- {(row, col): value} for every cell
    """
    givens = dict(givens)
    defKB = build_definite_kb(n, box_h, box_w, givens)


    ## naive method without guessing/PQ
    ## runs very slowly

    # while len(givens) < n**2:
    #     print(len(givens))
    #     for r in range(1, n + 1):
    #         # print("r")
    #         for c in range(1, n + 1):
    #             # print("c")
    #             if (r, c) in givens:
    #                 continue
    #             for num in range(1, n + 1):
    #                 if pl_fc_entails(defKB, atom('Is', r, c, num)):
    #                     givens[(r,c)] = num
    #                     break
    # return givens


    ####
    # adding in heuristics

    # create sets to know what values not to check for
    notRow = [set() for _ in range(n)]
    notCol = [set() for _ in range(n)]
    notBox = [set() for _ in range(n)]
    solved = [[False] * n for _ in range(n)]


    for k,v in givens.items():
        r, c = k
        notRow[r-1].add(v)
        notCol[c-1].add(v)
        notBox[((r-1)//box_h)*box_h + (c-1)//box_w].add(v)
        solved[r-1][c-1] = True

    allSet = set(range(1, n+1))

    # create min priority queue based on number of available choices
    PQ = PriorityQueue('min', lambda x: x[2])
    numChoices = [[None] * n for _ in range(n)]

    for r in range(1,n+1):
        for c in range(1,n+1):
            numChoices[r-1][c-1] = len(allSet-(notRow[r-1]|notCol[c-1]|notBox[((r-1)//box_h)*box_h + (c-1)//box_w]))
            PQ.append((r,c,numChoices[r-1][c-1]))
    
    while len(PQ) > 0:
        if len(givens) >= n**2:
            break
        r,c,num = PQ.pop()
        if solved[r-1][c-1]:
            continue

        if num != numChoices[r - 1][c - 1]:
            continue

        for v in allSet-(notRow[r-1]|notCol[c-1]|notBox[((r-1)//box_h)*box_h + (c-1)//box_w]):
            if pl_fc_entails(defKB, atom('Is', r, c, v)):
                defKB.tell(atom('Is', r, c, v))
                givens[(r,c)] = v

                notRow[r-1].add(v)
                notCol[c-1].add(v)
                notBox[((r-1)//box_h)*box_h + (c-1)//box_w].add(v)
                solved[r-1][c-1] = True

                for n2 in range(1, n+1):
                    newSet = allSet-(notRow[r-1]|notCol[n2-1]|notBox[((r-1)//box_h)*box_h + (n2-1)//box_w])
                    if numChoices[r-1][n2-1] > len(newSet) and n2 != c:
                        numChoices[r-1][n2-1] = len(newSet)
                        PQ.append((r,n2,len(newSet)))

                    newSet = allSet-(notRow[n2-1]|notCol[c-1]|notBox[((n2-1)//box_h)*box_h + (c-1)//box_w])
                    if numChoices[n2-1][c-1] > len(newSet) and n2 != r:
                        numChoices[n2-1][c-1] = len(newSet)
                        PQ.append((n2,c,len(newSet)))

                boxBaseCol = (c-1)//box_w * box_w + 1
                boxBaseRow = (r-1)//box_h * box_h + 1
                for newRow in range(boxBaseRow, boxBaseRow + box_h):
                    for newCol in range(boxBaseCol, boxBaseCol + box_w):
                        if (newRow, newCol) == (r, c):
                            continue
                        newSet = allSet-(notRow[newRow-1]|notCol[newCol-1]|notBox[((newRow-1)//box_h)*box_h + (newCol-1)//box_w])
                        if numChoices[newRow-1][newCol-1] > len(newSet):
                            numChoices[newRow-1][newCol-1] = len(newSet)
                            PQ.append((newRow,newCol,len(newSet)))

                break

    if len(givens) != n**2:
        raise ValueError(f"Could only determine {len(givens)} of {n**2} cells")

    return givens

    # raise NotImplementedError(
    #     'solve_full_grid_fc: solve every cell with forward chaining'
    # )


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
