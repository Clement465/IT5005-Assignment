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

    # Every cell has at least one value from {1, . . . , n}
    # Is111 | Is112 | Is113 ... Is118 | Is119
    # Is121 | Is122 | Is123 ... Is128 | Is129
    # .
    # .
    # for every cell
    for r in range(1, n + 1):
        for c in range(1, n + 1):
            clause = atom('Is', r, c, 1)
            for v in range(2, n + 1):
                clause |= atom('Is', r, c, v)
            kb.tell(clause)

    # Every cell has at most one value from {1, . . . , n}
    # Is111 => ~Is112, Is111 => ~Is113 ... Is111 => ~Is119
    # Is112 => ~Is113, Is112 => ~Is114 ... Is112 => ~Is119
    # .
    # .
    # Is118 => ~Is119
    # for every cell and value combination
    for r in range(1, n + 1):
        for c in range(1, n + 1):
            for v1 in range(1, n):
                for v2 in range(v1 + 1, n + 1):
                    clause = atom('Is', r, c, v1) | '==>' | ~atom('Is', r, c, v2)
                    kb.tell(clause)

    # No two cells in the same row hold the same value
    # Is111 => ~Is121, Is111 => ~Is131 ... Is111 => ~Is191
    # Is112 => ~Is122, Is112 => ~Is132 ... Is112 => ~Is192
    # .
    # .
    # Is119 => ~Is129, Is119 => ~Is139 ... Is119 => ~Is199
    # for every row and value combination
    for r in range(1, n + 1):
        for v in range(1, n + 1):
            for c1 in range(1, n):
                for c2 in range(c1 + 1, n + 1):
                    clause = atom('Is', r, c1, v) | '==>' | ~atom('Is', r, c2, v)
                    kb.tell(clause)

    # No two cells in the same column hold the same value
    # Is111 => ~Is211, Is111 => ~Is311 ... Is111 => ~Is911
    # Is112 => ~Is212, Is112 => ~Is312 ... Is112 => ~Is912
    # .
    # .
    # Is119 => ~Is219, Is119 => ~Is319 ... Is119 => ~Is919
    # for every col and value combination
    for c in range(1, n + 1):
        for v in range(1, n + 1):
            for r1 in range(1, n):
                for r2 in range(r1 + 1, n + 1):
                    clause = atom('Is', r1, c, v) | '==>' | ~atom('Is', r2, c, v)
                    kb.tell(clause)

    # No two cells in the same box hold the same value
    # Is111 => ~Is221 ... with every cell within its box
    # for every box and value combination
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
    # If (2, 3) is given as 7 then tell Is237
    # for every given
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


    newKB = PropDefiniteKB()

    # Loop through each cell on sudoku board
    for r in range(1,n+1):
        for c in range(1,n+1):
            # "The givens cells hold their stated value"
            if (r,c) in givens:
                newKB.tell(atom('Is', r, c, givens[(r,c)]))

            # Defining coordinates of top left cell of each box
            boxBaseCol = (c-1)//box_w * box_w + 1
            boxBaseRow = (r-1)//box_h * box_h + 1
            
            # Looping through each possible number
            for num in range(1,n+1):
                current = atom('Is', r, c, num)     # current cell of interest

                # Define empty list to hold conjunction of clauses to add into premise. 
                rowClauses = []     # Holds premise for "No two cells in the same row hold the same value."
                colClauses = []     # Holds premise for "No two cells in the same column hold the same value."
                boxClauses = []     # Holds premise for "No two cells in the same box hold the same value."
                otherClauses = []   # Holds premise for "Every cell has at least one value from {1, . . . , n}"

                # Loop through each possible number
                for n2 in range(1,n+1):
                    if c != n2:
                        rowClauses.append(atom('Not', r, n2, num))                  
                        newKB.tell(Expr('==>', current, atom('Not', r, n2, num)))   # current cell is num -> other cells in same row not num
                    if r != n2:
                        colClauses.append(atom('Not', n2, c, num))
                        newKB.tell(Expr('==>', current, atom('Not', n2, c, num)))   # current cell is num -> other cells in same col not num
                    if num != n2:
                        otherClauses.append(atom('Not', r, c, n2))
                        newKB.tell(Expr('==>', current, atom('Not', r, c, n2)))     # current cell is num -> current cell is not other nums

                for currRow in range(boxBaseRow, boxBaseRow + box_h):
                    for currCol in range(boxBaseCol, boxBaseCol + box_w):
                        if currRow == r and currCol == c:
                            continue
                        boxClauses.append(atom('Not', currRow, currCol, num))

                        if currRow != r and currCol != c:
                            newKB.tell(Expr('==>', current, atom('Not', currRow, currCol, num)))    # current cell is num -> other cells in same box not num

                # combine literals using conjunctions and tells KB: conjoined literals -> is num
                newRowClause = associate('&', rowClauses)
                newKB.tell(Expr('==>', newRowClause, atom('Is', r, c, num)))        # other cells in same row not num -> current cell is num

                newColClause = associate('&', colClauses)
                newKB.tell(Expr('==>', newColClause, atom('Is', r, c, num)))        # other cells is same col not num -> current cell is num

                newBoxClause = associate('&', boxClauses)
                newKB.tell(Expr('==>', newBoxClause, atom('Is', r, c, num)))        # other cells in same box not num -> current cell is num

                if (r,c) not in givens:
                    newOtherClause = associate('&', otherClauses)
                    newKB.tell(Expr('==>', newOtherClause, atom('Is', r, c, num)))      # current cell is not all other nums -> current cell is num

    for (r,c), v in givens.items():
        kb_cleanup(newKB, atom('Is',r,c,v),n)
    return newKB


def fact_to_cell(fact):
    name = fact.op.removeprefix('Is')
    r, c, v = map(int, name.split('_'))
    return {(r, c): v}

def pl_fc_entails_all(kb):
    """
    Edited pl_fc_entails to keep running until all possible facts are determined and return a dictionary of all values for all deducible cells

    Arguments
    kb: definite knowledge base

    Returns
    dict[(int, int), int] -- {(row, col): value}, 1-indexed
    """
    count = {c: len(conjuncts(c.args[0])) for c in kb.clauses if c.op == '==>'}
    inferred = defaultdict(bool)
    agenda = [s for s in kb.clauses if is_prop_symbol(s.op)]
    is_facts = [s for s in agenda if s.op.startswith('Is')]
    while agenda:
        p = agenda.pop()
        if not inferred[p]:
            inferred[p] = True
            for c in kb.clauses_with_premise(p):
                count[c] -= 1
                if count[c] == 0:
                    agenda.append(c.args[1])
                    if c.args[1].op.startswith('Is'):
                        is_facts.append(c.args[1])
    results = {}

    for fact in is_facts:
        for k, v in fact_to_cell(fact).items():
            if k in results and results[k] != v:
                raise ValueError(f"Conflicting values for cell {k}: {results[k]} vs {v}")
            results[k] = v

    return results


def solve_full_grid_fc_one_pass(n, box_h, box_w, givens):
    """Solve the whole puzzle using build_definite_kb + pl_fc_entails_all.

    Returns
    -------
    dict[(int, int), int] -- {(row, col): value} for every cell
    """
    givens = dict(givens)
    defKB = build_definite_kb(n, box_h, box_w, givens)      # Build definite knowledge base

    results = pl_fc_entails_all(defKB)

    if len(results) != n**2:
        raise ValueError(f"Could only determine {len(results)} of {n**2} cells")

    return results


def pl_fc_entails_optimized(kb, q):
    """
    [Figure 7.15]
    Use forward chaining to see if a PropDefiniteKB entails symbol q.
    Update kb as new symbols are derived.
    >>> pl_fc_entails(horn_clauses_KB, expr('Q'))
    True
    """
    count = {c: len(conjuncts(c.args[0])) for c in kb.clauses if c.op == '==>'}
    inferred = defaultdict(bool)
    agenda = [s for s in kb.clauses if is_prop_symbol(s.op)]
    while agenda:
        p = agenda.pop()
        if p == q:
            return True
        if not inferred[p]:
            inferred[p] = True
            for c in kb.clauses_with_premise(p):
                count[c] -= 1
                if count[c] == 0:
                    derived_fact = c.args[1]
                    kb.tell(derived_fact)
                    kb.retract(c)
                    agenda.append(derived_fact)
    return False


def solve_full_grid_fc(n, box_h, box_w, givens, print_state=False):
    """Solve the whole puzzle using build_definite_kb + pl_fc_entails.
    
    Returns
    -------
    dict[(int, int), int] -- {(row, col): value} for every cell
    """
    kb = build_definite_kb(n,box_h,box_w,givens)
    ans = dict(givens)

    if print_state:
        print("--- Initial Board State ---")
        print_sudoku_grid(kb,n)
    
    changed = True
    while changed:
        changed = False
        for r in range(1,n+1):
            for c in range(1,n+1):
                if (r,c) in ans:
                    continue

                solved = False
                for v in range(1,n+1):
                    if atom('Is',r,c,v) in kb.clauses:
                        ans[(r,c)] = v
                        solved = True
                        changed = True
                        break
                if solved: continue

                for v in range(1,n+1):
                    if atom('Not',r,c,v) in kb.clauses:
                        continue
                    q = atom('Is',r,c,v)
                    if print_state:
                        print(f"Testing Cell {(r,c)} = {v} ... ", end="")
                    if pl_fc_entails_optimized(kb,q):
                        ans[(r,c)] = v
                        changed = True
                        if print_state: 
                            print(f"SUCESS\n --- Curr Board State ---")
                            print_sudoku_grid(kb,n)
                        break
                    elif print_state:
                        print("FAILED")

    expected_cells = n**2

    if len(ans) != expected_cells:
        raise ValueError(
            f"Inference stopped with {len(ans)}/{expected_cells} cells solved. "
            "The current rules could not establish the remaining values."
        )

    return ans


def solve_full_grid_fc_original(n, box_h, box_w, givens):
    """Solve the whole puzzle using build_definite_kb + pl_fc_entails.

    Returns
    -------
    dict[(int, int), int] -- {(row, col): value} for every cell
    """
    givens = dict(givens)
    defKB = build_definite_kb(n, box_h, box_w, givens)      # Build definite knowledge base


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

    # create sets to know what values not to check for. Stores set of values present in each row/col/box
    usedInRow = [set() for _ in range(n)]
    usedInCol = [set() for _ in range(n)]
    usedInBox = [set() for _ in range(n)]
    solved = [[False] * n for _ in range(n)]    # n * n array to store if cell is solved
    visited = [[False] * n for _ in range(n)]

    # Fill usedInRow/usedInCol/usedInBox/solved based on initial given values
    for k,v in givens.items():
        r, c = k
        usedInRow[r-1].add(v)
        usedInCol[c-1].add(v)
        usedInBox[((r-1)//box_h)*box_h + (c-1)//box_w].add(v)
        solved[r-1][c-1] = True
        visited[r-1][c-1] = True

    allSet = set(range(1, n+1)) # Set with numbers 1-9

    # Init min priority queue based on number of available choices per cell
    PQ = PriorityQueue('min', lambda x: x[2])
    numChoices = [[None] * n for _ in range(n)]

    # Fill up PQ
    for r in range(1,n+1):
        for c in range(1,n+1):
            numChoices[r-1][c-1] = len(allSet-(usedInRow[r-1]|usedInCol[c-1]|usedInBox[((r-1)//box_h)*box_h + (c-1)//box_w]))
            if not solved[r-1][c-1]:
                PQ.append((r,c,numChoices[r-1][c-1]))
    
    # Loop through while PQ still has items/agenda
    while len(PQ) > 0:
        # Break if puzzle is solved
        if len(givens) >= n**2:
            break

        r,c,num = PQ.pop()

        # Skip item/agenda if cell is already solved
        if solved[r-1][c-1]:
            continue

        # Skip item/agenda if cell has already been visited 
        if visited[r-1][c-1]:
            continue

        visited[r-1][c-1] = True

        # for each possible number for cell at r, c
        for v in allSet-(usedInRow[r-1]|usedInCol[c-1]|usedInBox[((r-1)//box_h)*box_h + (c-1)//box_w]):
            # check if KB entails number v using FC
            if pl_fc_entails(defKB, atom('Is', r, c, v)):
                defKB.tell(atom('Is', r, c, v))
                givens[(r,c)] = v

                # update not sets and solved with new value
                usedInRow[r-1].add(v)
                usedInCol[c-1].add(v)
                usedInBox[((r-1)//box_h)*box_h + (c-1)//box_w].add(v)
                solved[r-1][c-1] = True

                # check affected cells in same row/col/box and if the number of possible numbers has decreased,
                # add a new entry to the priority queue
                for n2 in range(1, n+1):
                    newSet = allSet-(usedInRow[r-1]|usedInCol[n2-1]|usedInBox[((r-1)//box_h)*box_h + (n2-1)//box_w])
                    if not visited[r-1][n2-1] and numChoices[r-1][n2-1] > len(newSet) and n2 != c:
                        
                        numChoices[r-1][n2-1] = len(newSet)
                        PQ.append((r,n2,len(newSet)))

                    newSet = allSet-(usedInRow[n2-1]|usedInCol[c-1]|usedInBox[((n2-1)//box_h)*box_h + (c-1)//box_w])
                    if not visited[n2-1][c-1] and numChoices[n2-1][c-1] > len(newSet) and n2 != r:
                        numChoices[n2-1][c-1] = len(newSet)
                        PQ.append((n2,c,len(newSet)))

                boxBaseCol = (c-1)//box_w * box_w + 1
                boxBaseRow = (r-1)//box_h * box_h + 1
                for newRow in range(boxBaseRow, boxBaseRow + box_h):
                    for newCol in range(boxBaseCol, boxBaseCol + box_w):
                        if (newRow, newCol) == (r, c):
                            continue
                        newSet = allSet-(usedInRow[newRow-1]|usedInCol[newCol-1]|usedInBox[((newRow-1)//box_h)*box_h + (newCol-1)//box_w])
                        if not visited[newRow-1][newCol-1] and numChoices[newRow-1][newCol-1] > len(newSet):
                            numChoices[newRow-1][newCol-1] = len(newSet)
                            PQ.append((newRow,newCol,len(newSet)))

                break

    if len(givens) != n**2:
        raise ValueError(f"Could only determine {len(givens)} of {n**2} cells")

    return givens

    # raise NotImplementedError(
    #     'solve_full_grid_fc: solve every cell with forward chaining'
    # )

def pl_bc_entails(kb: PropDefiniteKB, q: Expr, n: int = None, visited=None,failed=None) -> bool:
    """Your own backward-chaining implementation.
    Parameters
    ----------
    kb : PropDefiniteKB
    query : Expr

    Returns
    -------
    bool
    """
    if n is None:
        n = extract_n(kb)
    if visited is None: 
        visited = set()
    if failed is None:
        failed = set()

    if q in kb.clauses: 
        return True
    if q in failed or q in visited: 
        return False #recursive and failure cycle prevention

    q_str = str(q.op)
    is_not = q_str.startswith('Not')
    prefix_len = 3 if is_not else 2
    opp_prefix = 'Is' if is_not else 'Not'
    if atom(opp_prefix, *q_str[prefix_len:].split('_')) in kb.clauses:
        failed.add(q)
        return False

    visited.add(q)

    clauses_with_q = [a_c for c in kb.clauses if (a_c:=parse_definite_clause(c))[1] == q]
    if not clauses_with_q:
        visited.remove(q)
        failed.add(q)
        return False
    for a, _ in clauses_with_q:
        count = len(a)
        for p in a:
            if pl_bc_entails(kb, p, n, visited,failed):
                count -= 1
            else:
                break
        
        if count == 0:
            if q not in kb.clauses:
                kb.tell(q)
                kb_cleanup(kb, q, n)
                failed.clear() #New facts may be able to prove past unprovable facts
            visited.remove(q)
            return True

    visited.remove(q)
    failed.add(q)
    return False


def solve_full_grid_bc(n, box_h, box_w, givens,print_state=False) -> dict[tuple[int,int], int]:
    """Solve the whole puzzle using build_definite_kb + your own pl_bc_entails.

    For each cell, try each candidate value until pl_bc_entails confirms one
    -- the same per-cell strategy as solve_full_grid_fc, but backed by
    backward chaining instead of a single shared forward-chaining pass.

    Returns
    -------
    dict[(int, int), int] -- {(row, col): value} for every cell
    """
    kb = build_definite_kb(n,box_h,box_w,givens)
    ans = dict(givens)

    if print_state:
        print("--- Initial Board State ---")
        print_sudoku_grid(kb,n)

    changed = True
    while changed:
        changed = False
        for r in range(1,n+1):
            for c in range(1,n+1):
                if (r,c) in ans:
                    continue

                solved = False
                for v in range(1,n+1):
                    if atom('Is',r,c,v) in kb.clauses:
                        ans[(r,c)] = v
                        solved = True
                        changed = True
                        break
                if solved: continue

                for v in range(1,n+1):
                    if atom('Not',r,c,v) in kb.clauses:
                        continue
                    q = atom('Is',r,c,v)
                    if print_state:
                        print(f"Testing Cell {(r,c)} = {v} ... ", end="")
                    if pl_bc_entails(kb,q,n):
                        ans[(r,c)] = v
                        changed = True
                        if print_state: 
                            print(f"SUCESS\n --- Curr Board State ---")
                            print_sudoku_grid(kb,n)
                        break
                    elif print_state:
                        print("FAILED")


    expected_cells = n * n

    if len(ans) != expected_cells:
        raise ValueError(
            f"Inference stopped with {len(ans)}/{expected_cells} cells solved. "
            "The current rules could not establish the remaining values."
        )
    
    return ans

def kb_cleanup(kb: PropDefiniteKB,q: Expr,n: int) -> None:
    """
    Cleans the kb up given a fact 'Is/Not'+'r_c_v'
    """
    q_str = str(q.op)
    is_not = q_str.startswith("Not")
    prefix_len = 3 if is_not else 2
    r,c,v = map(int,q_str[prefix_len:].split('_'))

    tbd_literals,new_facts,tbd_facts = set(),[],[]
    tbd_literals.add(atom('Is' if is_not else 'Not',r,c,v))

    if not is_not:
        for i in range(1,n+1):
            if i !=v:
                tbd_literals.add(atom('Is',r,c,i))

    for clause in kb.clauses:
        a,c = parse_definite_clause(clause)
        if c in tbd_literals or any(s in tbd_literals for s in a):
            tbd_facts.append(clause)
        elif(len(a) == 1 and q in a):
            if c not in kb.clauses and c not in new_facts:
                new_facts.append(c)
            tbd_facts.append(clause)
    for clause in tbd_facts:
        kb.retract(clause)
    for fact in new_facts:
        kb.tell(fact)

def extract_n(kb) -> int:
    """Iteratively probe diagonal symbols (k, k, k) to determine the exact grid size n."""
    symbols = {str(s.op) for clause in kb.clauses for s in prop_symbols(clause)}
    k = 1
    while f'Is{k}_{k}_{k}' in symbols or f'Not{k}_{k}_{k}' in symbols:
        k += 1
    return k - 1

def print_sudoku_grid(kb: PropDefiniteKB, n: int) -> None:
    """Reconstruct and print the n x n Sudoku grid from facts in kb.clauses."""
    grid = [['.' for _ in range(n)] for _ in range(n)]
    for c in kb.clauses:
        op_str = str(c.op)
        if is_prop_symbol(c.op) and op_str.startswith('Is'):
            parts = op_str[2:].split('_')
            if len(parts) == 3:
                r, col, val = map(int, parts)
                grid[r - 1][col - 1] = str(val)

    print("-" * (2 * n + 1))
    for row in grid:
        print("| " + " ".join(row) + " |")
    print("-" * (2 * n + 1))


