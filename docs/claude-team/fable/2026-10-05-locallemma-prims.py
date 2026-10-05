"""2026-10-05-locallemma-prims.py (Fable, LW-10c): the six primitive moves, the decomposition of the 17 terms into primitives
(verified symbolically), and the abstract local-lemma enumeration for each primitive (local cost c = ord + #elem).
Imports the enumeration machinery of 2026-10-05-locallemma-enum.py (same directory)."""
import sys, os, importlib.util, time
from collections import Counter
here = os.path.dirname(os.path.abspath(__file__))
spec = importlib.util.spec_from_file_location('enum6', os.path.join(here, '2026-10-05-locallemma-enum.py'))
EN = importlib.util.module_from_spec(spec); spec.loader.exec_module(EN)
B, R, lw, E, DE = EN.B, EN.R, EN.lw, EN.E, EN.DE

# a "move" is (removed edges, added edges, number of new waved edges, new vertices); composition = concatenation with cancellation
def compose(*moves):
    rem, add, nw, news = [], [], 0, []
    for (r, a, w, n) in moves:
        for e in r:
            if e in add: add.remove(e)      # removing an edge added by an earlier move
            else: rem.append(e)
        add += a; nw += w; news += n
    return rem, add, nw, news

def net(move):
    """the net effect: an edge removed and re-added is cancelled (the final graph is the same)."""
    rem, add, nw, news = move
    r, a = Counter(rem), Counter(add); com = r & a
    return (r - com, a - com, nw, sorted(news))

# ---- the primitives (new vertex `al`; `attach` = the end of the new waved edge, irrelevant for c) --------------------
def Loop(z, al, col=B):                 # T1 / Oe1xOwx / R3: a fresh light-weight hanging from z
    return ([], [lw(al, col)], 1, [al])
def AddLoop(z, col):                    # P5, P6, R5: a light-weight at an existing vertex (no new vertex, no waved edge)
    return ([], [lw(z, col)], 0, [])
def MoveLoop(z, al, col=B):             # T2, T4: the light-weight of z moved to a fresh al (waved z - al)
    return ([lw(z, col)], [lw(al, col)], 1, [al])
def MoveSC(z, u, v, al, col=B):         # P4/P6, R4/R5/R6/R8 core: the pair u -> z -> v moved to al (waved z - al)
    return ([E(col, u, z), E(col, z, v)], [E(col, u, al), E(col, al, v)], 1, [al])
def MoveOut(z, v, d, al):               # P3/P5 core: the two out-edges z -> v (blue), z -> d (red) moved to al
    return ([E(B, z, v), E(R, z, d)], [E(B, al, v), E(R, al, d)], 1, [al])
def Dmove(z, p, q, al):                 # D / T3 / R7 and (at al) T4 / R8: remove p = (blue, z -> v) and q; add DE(al, z, q), al -> v
    assert p[0] == B and p[1] == z
    v = p[2]
    return ([p, q], DE(al, z, q) + [E(B, al, v)], 1, [al])
def Contract(z, u, v, col=B):           # R2
    return ([E(col, u, z), E(col, z, v)], [E(col, u, v)], 1, [])

def check_decompositions():
    ok = True
    def cmp(name, term, comp):
        nonlocal ok
        t, c_ = net(term), net(comp)
        good = (t == c_)
        ok &= good
        print(f'  {name:8s} {"OK " if good else "MISMATCH"} term={t[0]}|{t[1]}|{t[2]}|{t[3]}  composite={c_[0]}|{c_[1]}|{c_[2]}|{c_[3]}' if not good else f'  {name:8s} OK')
    print('decomposition of the 17 term formulas into primitives (symbolic, in the frame):')
    for (kind, (name, syms, qvars, f)) in EN.ALL_TERMS:
        for q in qvars:
            term = f(q)
            if name == 'T1': comp = Loop('w', 'al')
            elif name == 'T2': comp = compose(MoveLoop('w', 'al'), Loop('al', 'be'))
            elif name == 'T3': comp = Dmove('w', lw('w', B), q, 'al')
            elif name == 'T4': comp = compose(MoveLoop('w', 'al'), Dmove('al', lw('al', B), q, 'be'))
            elif name == 'Oe1xOwx': comp = Loop('x', 'al')
            elif name == 'D': comp = Dmove('x', E(B, 'x', 'v'), q, 'al')
            elif name == 'P5': comp = compose(MoveOut('x', 'v', 'd', 'al'), AddLoop('x', R))
            elif name == 'P3': comp = MoveOut('x', 'v', 'd', 'al')
            elif name == 'P6': comp = compose(MoveSC('x', 's', 'v', 'al'), AddLoop('x', B))
            elif name == 'P4': comp = MoveSC('x', 's', 'v', 'al')
            elif name == 'R2': comp = Contract('x', 'yp', 'y')
            elif name == 'R3': comp = Loop('x', 'al')
            elif name == 'R4': comp = compose(MoveSC('x', 'yp', 'y', 'al'), Loop('al', 'be'))
            elif name == 'R5': comp = compose(MoveSC('x', 'yp', 'y', 'al'), AddLoop('x', B))
            elif name == 'R6': comp = compose(Loop('x', 'al'), MoveSC('x', 'yp', 'y', 'be'))
            elif name == 'R7': comp = Dmove('x', E(B, 'x', 'y'), q, 'al')
            elif name == 'R8': comp = compose(MoveSC('x', 'yp', 'y', 'al'), Dmove('al', E(B, 'al', 'y'), q, 'be'))
            cmp(f'{name}{"" if q is None else "/" + str(q)}', term, comp)
    print('all decompositions verified:', ok)
    return ok

# ---- the primitives as "terms" for the abstract enumeration -----------------------------------------------------------
def Dprim_variants():
    # p: the blue out-edge z -> v (an edge of Q; absent in G0 iff [v] = [z]) or the light-weight of z (always present);
    # q: blue / red, a non-loop edge or a light-weight (a = b)
    out = []
    ps = [('edge', E(B, 'z', 'v')), ('lw', lw('z', B))]
    qs = [E(B, 'a', 'b'), E(R, 'a', 'b'), lw('a', B), lw('a', R)]
    for pk, p in ps:
        for q in qs:
            out.append((pk, p, q))
    return out

PRIMS = [
    ('Loop', ['z'], [None], lambda q: Loop('z', 'al')),
    ('AddLoop', ['z'], [B, R], lambda q: AddLoop('z', q)),
    ('MoveLoop', ['z'], [None], lambda q: MoveLoop('z', 'al')),
    ('MoveSC', ['z', 'u', 'v'], [None], lambda q: MoveSC('z', 'u', 'v', 'al')),
    ('MoveOut', ['z', 'v', 'd'], [None], lambda q: MoveOut('z', 'v', 'd', 'al')),
    ('Dmove', ['z', 'v', 'a', 'b'], Dprim_variants(), lambda pq: Dmove('z', pq[1], pq[2], 'al')),
    ('Contract', ['z', 'u', 'v'], [None], lambda q: Contract('z', 'u', 'v')),
]

def main():
    ok = check_decompositions()
    print()
    grand = Counter(); t0 = time.time()
    for prim in PRIMS:
        name = prim[0]
        per = Counter(); mins = {}; shapes = Counter(); other = []; coll = []
        for cfg in EN.configs(prim):
            if any(cfg[6]): continue      # all classes internal (dominant case)
            q = cfg[0]
            dord, delem, total, cls, isext, isfresh, Rpat, Apat = EN.analyse_config(*cfg)
            per['configs'] += 1
            key = str(q); mins[key] = min(mins.get(key, 99), total)
            if total < 0:
                per['naive_fail'] += 1
                k = EN.collapse_kind(cfg)
                shapes[(f'{k}-cycle' if k else 'OTHER', total)] += 1
                (coll if k else other).append(cfg)
        print(f'[{name}] abstract configurations (all internal) {per["configs"]}, min Delta c by variant: {mins}; naive failures {per["naive_fail"]}: {dict(shapes)}')
        for cfg in coll: print('    collapse:', cfg[0], EN.describe(cfg[5], cfg[6], cfg[7]))
        for cfg in other[:5]: print('    NON-COLLAPSE FAILURE:', cfg[0], EN.describe(cfg[5], cfg[6], cfg[7]), EN.shape(cfg))
        grand['configs'] += per['configs']; grand['fail'] += per['naive_fail']; grand['other'] += len(other)
    print('GRAND (primitives):', dict(grand), f't={time.time()-t0:.1f}s')

if __name__ == '__main__' and '--tables' not in sys.argv:
    main()


def tables():
    """Per-primitive tables: for every coincidence pattern of the named vertices and every placement class of the new vertex
    (fresh / a named class / an unnamed class), the minimum of Delta c over the residual patterns (all classes internal), and k =
    the number of the new vertex's non-loop edges whose far end lies in its class."""
    for prim in PRIMS:
        name, syms, qvars, f = prim
        print(f'=== {name}')
        for cfg in EN.configs(prim):
            q, removed, added, nwav, news, part, ext, plc = cfg
            if any(ext): continue
            dord, delem, total, cls, isext, isfresh, Rpat, Apat = EN.analyse_config(*cfg)
            if news:
                al = news[0]; o = plc[al]
                k = sum(1 for (col, s, d, circ) in added if not circ and al in (s, d) and cls[s] == cls[d])
                place = 'fresh' if o == 'fresh' else ('C' if o[0] == 'unn' else 'in{' + ','.join(part[o[1]]) + '}')
            else:
                k = '-'; place = '-'
            pat = ' '.join('{' + ','.join(c) + '}' for c in part)
            qs = '' if q is None else (f' q={q}' if name != 'Dmove' else f' p={q[0]} q=({q[2][0]},{q[2][1]}->{q[2][2]}{",lw" if q[2][3] else ""})')
            print(f'  {pat:22s} alpha->{place:10s} k={k} Delta ord={dord:+d} min Delta c={total:+d}{"  COLLAPSE" if total < 0 else ""}{qs}')

if __name__ == '__main__' and '--tables' in sys.argv:
    tables()
