import json
import re
import threading
import time
from collections import defaultdict
from pathlib import Path

import streamlit as st
try:
    # Lets the warm-up thread use st.cache_resource without log warnings. It's an
    # internal module, so if a later Streamlit moves it the app still runs.
    from streamlit.runtime.scriptrunner import add_script_run_ctx, get_script_run_ctx
except ImportError:
    add_script_run_ctx = get_script_run_ctx = None
from utils import *
from logic_ import *
from sudoku_solver import (
    atom,
    build_definite_kb,
    build_general_kb,
    solve_full_grid_fc,
    solve_full_grid_bc,
    pl_bc_entails,
    solve_full_grid_fc_one_pass,
)

st.set_page_config(page_title='Sudoku Solver')
st.title('Sudoku Solver')
st.caption('IT5005 Assignment 1, Group 1. Propositional logic on Sudoku: forward and backward chaining '
           'over a definite (Horn) knowledge base.')


# ---------------------------------------------------------------------------
# Helpers for the interface
# ---------------------------------------------------------------------------

@st.cache_data
def load_pool():
    # Same format as load_pool() in the notebook. The path is relative to this
    # file, so the app works whichever folder streamlit is started from.
    with open(Path(__file__).parent / 'puzzles.json') as f:
        raw = json.load(f)
    puzzles = []
    for p in raw['puzzles']:
        givens = {tuple(int(x) for x in k.split('_')): v for k, v in p['givens'].items()}
        solution = {tuple(int(x) for x in k.split('_')): v for k, v in p['solution'].items()}
        puzzles.append({'givens': givens, 'solution': solution, 'given_count': p['given_count']})
    return raw['n'], raw['box_h'], raw['box_w'], puzzles


n, box_h, box_w, pool = load_pool()

GIVEN_STYLE = 'font-weight:700;color:#202124;background:#e8eaed'
SOLVED_STYLE = 'color:#1a73e8;background:#ffffff'
ASKED_STYLE = 'background:#fde7c8'
MARKED_STYLE = 'background:#f8d7d3'


def board_html(givens, filled=None, asked=None, marked=(), size=40):
    # Givens are bold on grey, cells a solver worked out are blue, and the
    # cell asked about in section 3/4 is shaded orange. Tutor mode shades the
    # cells behind a step red.
    filled = filled or {}
    rows = []
    for r in range(1, n + 1):
        cells = []
        for c in range(1, n + 1):
            style = [f'width:{size}px', f'height:{size}px', 'padding:0', 'text-align:center',
                     f'font-size:{size // 2}px', 'border:1px solid #9aa0a6', SOLVED_STYLE]
            # thicker lines around each box
            if (r - 1) % box_h == 0:
                style.append('border-top:3px solid #202124')
            if r % box_h == 0:
                style.append('border-bottom:3px solid #202124')
            if (c - 1) % box_w == 0:
                style.append('border-left:3px solid #202124')
            if c % box_w == 0:
                style.append('border-right:3px solid #202124')
            if (r, c) in givens:
                style.append(GIVEN_STYLE)
                text = givens[(r, c)]
            else:
                text = filled.get((r, c), '')
            if (r, c) in marked:
                style.append(MARKED_STYLE)
            if (r, c) == asked:
                style.append(ASKED_STYLE)
            cells.append(f'<td style="{";".join(style)}">{text}</td>')
        rows.append('<tr>' + ''.join(cells) + '</tr>')
    return '<table style="border-collapse:collapse;margin:0 0 6px 0">' + ''.join(rows) + '</table>'


@st.cache_resource(show_spinner=False)
def definite_kb(puzzle_index):
    # Building the definite KB takes ~15-20 s (kb_cleanup runs inside it), so it
    # is built once per puzzle and shared. Nothing should modify this copy.
    return build_definite_kb(n, box_h, box_w, pool[puzzle_index]['givens'])


def bc_kb(puzzle_index):
    # pl_bc_entails adds every fact it proves to the KB it is given. Like the
    # notebook's verify loop and solve_full_grid_bc, we keep one KB per puzzle
    # (per browser session) so later questions reuse what earlier ones proved.
    # It starts as a copy, so the shared cached KB is never modified.
    kbs = st.session_state.bc_kbs
    if puzzle_index not in kbs:
        kbs[puzzle_index] = PropDefiniteKB()
        kbs[puzzle_index].clauses = list(definite_kb(puzzle_index).clauses)
    return kbs[puzzle_index]


# ---------------------------------------------------------------------------
# Helpers for the reasoning trace (tutor mode)
# ---------------------------------------------------------------------------

SYMBOL = re.compile(r'^(Is|Not)(\d+)_(\d+)_(\d+)$')


def read_symbol(fact):
    # 'Is3_2_4' -> ('Is', 3, 2, 4)
    kind, r, c, v = SYMBOL.match(fact.op).groups()
    return kind, int(r), int(c), int(v)


def forward_chain_with_reasons(kb):
    # Forward chaining as in pl_fc_entails (logic_.py, Figure 7.15), with two
    # changes for tutor mode: it keeps going until nothing new can be derived,
    # and it remembers which rule produced each fact. Rules are indexed by
    # premise once, instead of scanning the whole KB for every fact.
    count = {}
    by_premise = defaultdict(list)
    for rule in dict.fromkeys(kb.clauses):
        if rule.op == '==>':
            premises = conjuncts(rule.args[0])
            count[rule] = len(premises)
            for p in premises:
                by_premise[p].append(rule)
    agenda = [s for s in kb.clauses if is_prop_symbol(s.op)]
    reason = {s: None for s in agenda}      # None: the KB started with this fact
    order = {s: i for i, s in enumerate(agenda)}
    inferred = set()
    while agenda:
        p = agenda.pop()
        if p in inferred:
            continue
        inferred.add(p)
        for rule in by_premise[p]:
            count[rule] -= 1
            if count[rule] == 0:
                q = rule.args[1]
                if q not in reason:
                    reason[q] = rule
                    order[q] = len(order)
                agenda.append(q)
    return reason, order


@st.cache_resource(show_spinner=False)
def fc_trace(puzzle_index):
    return forward_chain_with_reasons(definite_kb(puzzle_index))


def facts_behind(fact, reason, order):
    # Every fact that `fact` depends on (itself included), in the order forward
    # chaining derived them, so premises always come before conclusions.
    needed, stack = set(), [fact]
    while stack:
        f = stack.pop()
        if f in needed:
            continue
        needed.add(f)
        rule = reason.get(f)
        if rule is not None:
            stack.extend(conjuncts(rule.args[0]))
    return sorted(needed, key=order.get)


def same_box(r1, c1, r2, c2):
    return (r1 - 1) // box_h == (r2 - 1) // box_h and (c1 - 1) // box_w == (c2 - 1) // box_w


def given_behind(r, c, v, givens):
    # kb_cleanup applies the givens while the KB is built, so the KB already
    # starts with eliminations like Not1_2_3. Find the given that explains one.
    if (r, c) in givens:
        return r, c, givens[(r, c)]
    for check in (lambda r2, c2: r2 == r, lambda r2, c2: c2 == c, lambda r2, c2: same_box(r, c, r2, c2)):
        for (r2, c2), v2 in givens.items():
            if v2 == v and check(r2, c2):
                return r2, c2, v2
    return None


def clash(r, c, v, cause):
    # Why cell (r,c) can't be v, when cause = (r2, c2, v2) is a known value.
    r2, c2, v2 = cause
    if (r2, c2) == (r, c):
        return f'the cell is already {v2}'
    if r2 == r:
        return f'row {r} already has a {v} at ({r2},{c2})'
    if c2 == c:
        return f'column {c} already has a {v} at ({r2},{c2})'
    return f'its box already has a {v} at ({r2},{c2})'


def cause_of(fact, reason, givens):
    # The known value (r2, c2, v2) that rules out Not_r_c_v, or None if there isn't one.
    _, r, c, v = read_symbol(fact)
    rule = reason.get(fact)
    if rule is None:
        return given_behind(r, c, v, givens)
    premises = conjuncts(rule.args[0])
    if len(premises) != 1 or read_symbol(premises[0])[0] != 'Is':
        return None
    return read_symbol(premises[0])[1:]


def why_not(fact, reason, givens, step_no):
    # Plain-English reason for an elimination fact Not_r_c_v.
    _, r, c, v = read_symbol(fact)
    rule = reason.get(fact)
    cause = cause_of(fact, reason, givens)
    if cause is None:
        if rule is None:
            return f'({r},{c}) is not {v} (known from the start)'
        return f'({r},{c}) is not {v} (from the rule {rule})'
    if rule is None or givens.get(cause[:2]) == cause[2]:
        where = ' (given)'
    else:
        premise = conjuncts(rule.args[0])[0]
        where = f' (step {step_no[premise]})' if premise in step_no else ''
    return f'({r},{c}) is not {v}: {clash(r, c, v, cause)}{where}'


def why_is(fact, premises):
    # Which kind of last-candidate rule produced Is_r_c_v.
    _, r, c, v = read_symbol(fact)
    cells = [read_symbol(p)[1:] for p in premises]
    if all((ri, ci) == (r, c) for ri, ci, _ in cells):
        return 'the only value left for this cell'
    if all(vi == v for _, _, vi in cells):
        if all(ri == r for ri, _, _ in cells):
            return f'the only place left for {v} in row {r}'
        if all(ci == c for _, ci, _ in cells):
            return f'the only place left for {v} in column {c}'
        return f'the only place left for {v} in its box'
    return 'from the rule below'


def show_steps(target, reason, order, givens):
    # One expander per cell forward chaining had to work out on the way to target.
    # Each has a small board of the cells found so far: this step's cell is orange,
    # and the cells whose values rule out its other options are red.
    steps = [f for f in facts_behind(target, reason, order)
             if reason[f] is not None and read_symbol(f)[0] == 'Is']
    step_no = {f: i for i, f in enumerate(steps, start=1)}
    if len(steps) > 1:
        st.write(f'Forward chaining worked out {len(steps)} cells to get there, in this order. '
                 'Open a step to see the eliminations behind it.')
    st.caption('On each small board, orange is the cell worked out in that step, red cells hold the values '
               'that rule out its other options, and blue cells were worked out in earlier steps.')
    found = {}
    for i, fact in enumerate(steps, start=1):
        _, r, c, v = read_symbol(fact)
        found[(r, c)] = v
        premises = conjuncts(reason[fact].args[0])
        causes = {cause[:2] for cause in (cause_of(p, reason, givens) for p in premises) if cause}
        with st.expander(f'Step {i}: ({r},{c}) = {v}, {why_is(fact, premises)}', expanded=(i == len(steps))):
            board, reasons = st.columns([2, 3])
            board.markdown(board_html(givens, dict(found), asked=(r, c), marked=causes, size=26),
                           unsafe_allow_html=True)
            reasons.markdown('\n'.join(f'- `{p}`: {why_not(p, reason, givens, step_no)}' for p in premises))
            st.caption('Rule fired: ' + ' ∧ '.join(str(p) for p in premises) + f' ⟹ {fact}')


def explain(puzzle_index, r, c, v):
    reason, order = fc_trace(puzzle_index)
    givens = pool[puzzle_index]['givens']
    target, ruled_out = atom('Is', r, c, v), atom('Not', r, c, v)
    if givens.get((r, c)) == v:
        st.info(f'({r},{c}) = {v} is one of the givens, so there is nothing to prove.')
    elif target in reason:
        st.success(f'Forward chaining derives `{target}`: ({r},{c}) = {v} is entailed.')
        show_steps(target, reason, order, givens)
    elif ruled_out in reason:
        st.error(f'Forward chaining derives `{ruled_out}` instead: ({r},{c}) = {v} is not entailed.')
        cause = cause_of(ruled_out, reason, givens)
        board, why = st.columns([2, 3])
        board.markdown(board_html(givens, asked=(r, c), marked={cause[:2]} if cause else (), size=26),
                       unsafe_allow_html=True)
        why.markdown(f'- `{ruled_out}`: {why_not(ruled_out, reason, givens, {})}')
        rule = reason[ruled_out]
        if rule is not None:
            cause = conjuncts(rule.args[0])[0]
            if reason.get(cause) is not None:
                st.write(f'Here is how forward chaining found `{cause}`:')
                show_steps(cause, reason, order, givens)
    else:
        st.warning(f'Forward chaining stops without deciding whether ({r},{c}) = {v}.')


@st.cache_resource(show_spinner=False)
def warm_up():
    # Start building puzzle 1's KB and tutor trace as soon as the app starts, so
    # it's usually ready by the time anyone clicks. Only puzzle 1, the one shown
    # first: building the others in the background would slow down whatever solve
    # someone runs meanwhile and make its timing wrong. Streamlit locks a cached
    # value while it's computed, so a click during the build just waits for it.
    worker = threading.Thread(target=fc_trace, args=(0,), daemon=True)
    if add_script_run_ctx:
        add_script_run_ctx(worker, get_script_run_ctx())
    worker.start()
    return worker


warm_worker = warm_up()


def finish_warm_up():
    # Timings shown in the app shouldn't include a build running alongside them.
    if warm_worker.is_alive():
        with st.spinner('Finishing the start-up build of puzzle 1 first, so the timing is fair ...'):
            warm_worker.join()

if 'solves' not in st.session_state:
    st.session_state.solves = {}      # (puzzle, algorithm) -> (solved grid, seconds)
    st.session_state.on_board = {}    # puzzle -> algorithm whose grid is drawn
    st.session_state.bc_kbs = {}      # puzzle -> the KB pl_bc_entails works on
    st.session_state.bc_answers = {}  # (puzzle, r, c, v) -> (answer, seconds)
    st.session_state.bc_answer = None
    st.session_state.bc_repeat = False
    st.session_state.explained = None
    st.session_state.asked = None


# --- 1. Puzzle selection & visual board display ---
st.header('1. Pick a puzzle')
idx = st.selectbox('Puzzle', range(len(pool)), key='puzzle',
                   format_func=lambda i: f'Puzzle {i + 1}  ({pool[i]["given_count"]} givens)')
puzzle = pool[idx]
givens = puzzle['givens']
board_slot = st.empty()     # drawn at the end of the script, once we know what goes on it
st.markdown(f'<span style="{GIVEN_STYLE};padding:1px 7px">5</span> given &nbsp;&nbsp; '
            f'<span style="{SOLVED_STYLE};padding:1px 7px;border:1px solid #9aa0a6">5</span> worked out by a solver &nbsp;&nbsp; '
            f'<span style="{ASKED_STYLE};padding:1px 7px">&nbsp;&nbsp;</span> cell you asked about',
            unsafe_allow_html=True)


# --- 2. Full-grid auto-solver, with algorithm selection ---
st.header('2. Solve the whole grid')
SOLVERS = {
    'Forward chaining': solve_full_grid_fc,
    'Backward chaining': solve_full_grid_bc,
    'Forward chaining, one pass': solve_full_grid_fc_one_pass,
}
algorithm = st.radio('Algorithm', list(SOLVERS), horizontal=True, key='algorithm',
                     captions=['pl_fc_entails, one cell at a time',
                               'pl_bc_entails, one cell at a time',
                               'one forward pass for the whole grid'])
if st.button('Solve', type='primary', key='solve'):
    solver = SOLVERS[algorithm]
    finish_warm_up()
    with st.spinner(f'Running {solver.__name__} (this can take a minute or two) ...'):
        start = time.perf_counter()
        try:
            grid, error = solver(n, box_h, box_w, dict(givens)), None
        except Exception as e:
            grid, error = None, f'{type(e).__name__}: {e}'
        seconds = time.perf_counter() - start
    if error:
        st.error(f'{solver.__name__} failed after {seconds:.1f} s: {error}')
    else:
        st.session_state.solves[(idx, algorithm)] = (grid, seconds)
        st.session_state.on_board[idx] = algorithm

shown = st.session_state.on_board.get(idx)
if shown:
    grid, seconds = st.session_state.solves[(idx, shown)]
    name = SOLVERS[shown].__name__
    if grid == puzzle['solution']:
        st.success(f'{name} solved all {n * n} cells in {seconds:.2f} s. The grid matches the known solution.')
    else:
        st.warning(f'{name} finished in {seconds:.2f} s, but the grid does not match the known solution '
                   f'({n * n - len(grid)} cells left empty).')
    runs = [{'Algorithm': a, 'Function': SOLVERS[a].__name__, 'Time (s)': round(s, 2)}
            for (i, a), (_, s) in st.session_state.solves.items() if i == idx]
    st.caption('Solve times for this puzzle so far. Run the other algorithms to compare them.')
    st.dataframe(runs, hide_index=True)


# --- 3. Targeted cell entailment query ---
st.header('3. Ask about one cell')
st.write('Is "cell (row, column) has this value" entailed by the puzzle\'s definite KB?')
col_r, col_c, col_v = st.columns(3)
r = col_r.number_input('Row', min_value=1, max_value=n, value=1, step=1, key='row')
c = col_c.number_input('Column', min_value=1, max_value=n, value=1, step=1, key='col')
v = col_v.number_input('Value', min_value=1, max_value=n, value=1, step=1, key='val')
query = atom('Is', r, c, v)
st.caption('A question about an empty cell can be slow the first time: backward chaining has to prove '
           'everything that cell depends on, which can take a few minutes. It keeps what it proves, so later '
           'questions on the same puzzle are much quicker. Tutor mode below explains any cell straight away.')

if st.button(f'Check {query} with pl_bc_entails', key='check'):
    key = (idx, r, c, v)
    st.session_state.bc_repeat = key in st.session_state.bc_answers
    if not st.session_state.bc_repeat:
        with st.spinner('Building the definite KB for this puzzle (first time only, about 20 s) ...'):
            kb = bc_kb(idx)
        finish_warm_up()
        with st.spinner(f'Running pl_bc_entails({query}) ...'):
            start = time.perf_counter()
            answer = pl_bc_entails(kb, query)
            st.session_state.bc_answers[key] = (answer, time.perf_counter() - start)
    st.session_state.bc_answer = key
    st.session_state.asked = (idx, (r, c))

if st.session_state.bc_answer and st.session_state.bc_answer[0] == idx:
    _, qr, qc, qv = st.session_state.bc_answer
    answer, seconds = st.session_state.bc_answers[st.session_state.bc_answer]
    asked_query = atom('Is', qr, qc, qv)
    took = f'pl_bc_entails took {seconds:.2f} s' + (' when you first asked' if st.session_state.bc_repeat else '')
    if answer:
        st.success(f'**True**: `{asked_query}` is entailed, so ({qr},{qc}) = {qv}. ({took})')
    else:
        st.warning(f'**False**: `{asked_query}` is not entailed by this KB. ' f'({took})')

# --- 4. Reasoning trace ("tutor mode") ---
st.header('4. Tutor mode')
st.write('Explains the same cell step by step. This uses forward chaining, instrumented to remember '
         'which rule produced each fact, then keeps only the steps your cell actually depends on.')

if st.button(f'Explain {query}', key='explain'):
    with st.spinner('Building the definite KB for this puzzle (first time only, about 20 s) ...'):
        fc_trace(idx)
    st.session_state.explained = (idx, (r, c, v))
    st.session_state.asked = (idx, (r, c))

if st.session_state.explained and st.session_state.explained[0] == idx:
    explain(idx, *st.session_state.explained[1])


# Draw the board last, so it shows this run's solve result and highlighted cell.
filled = st.session_state.solves[(idx, shown)][0] if shown else {}
asked = st.session_state.asked[1] if st.session_state.asked and st.session_state.asked[0] == idx else None
board_slot.markdown(board_html(givens, filled, asked), unsafe_allow_html=True)

# Keep the core solver functions in sudoku_solver.py; do not duplicate them here.
