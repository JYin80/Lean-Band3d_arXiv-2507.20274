"""2026-10-05-locallemma-enum.py  (Fable, LW-10c: the local lemma for the LOCAL cost c = ord + #elem)

c(G) := ord(G) + #{internal vertices v : H(v) = {c-in, c-out} for one colour c}   (H(v) = half-edge multiset, a loop = c-in + c-out)
Phi(Q) := min over partitions pi of V(Q) (x, y apart for the far version) of c(M_pi Q)   (M_pi: merge, keep circled loops, drop other in-class edges)

Local lemma to check: for every generalized term application on a merged graph G0 (named vertices = classes, arbitrary
coincidences, each class external or internal, the new vertices alpha/beta fresh or placed into any class), with all new
in-class edges dropped,  c(G1) >= c(G0)   (naive), and otherwise a repair: a single merge mu of two classes of G0 with
c(mu G0) <= c(G1).

The check is exhaustive over the abstract local data: Delta c = Delta ord + sum_v Delta elem(v), where Delta elem(v) depends only on
the residual pattern X_v (half-edge counts not touched by the term, each in {0,1,2+}) and the removed/added half-edges at v.
Usage: python3 2026-10-05-locallemma-enum.py [--ext] [--full-repair]   (see the __main__ block; report section 6).
"""
from itertools import product, combinations
from collections import Counter, defaultdict
import sys, time
sys.stdout.reconfigure(line_buffering=True)

B, R = 'b', 'r'
HALF = [('b','i'),('b','o'),('r','i'),('r','o')]   # half-edge types: (colour, in/out)

def pat_add(p, q):
    return tuple(a + b for a, b in zip(p, q))

def elem(p):
    """p = (bi, bo, ri, ro) counts (2 = '2 or more')."""
    return p in ((1,1,0,0), (0,0,1,1))

def half_edges(edges, cls):
    """edges: list of (colour, src, dst, circ). Returns dict class -> pattern (bi,bo,ri,ro) of the edges that EXIST
    (a circled loop always exists; an uncircled edge exists iff its ends are in different classes), and the number of existing edges."""
    pat = defaultdict(lambda: [0,0,0,0]); n = 0
    for (col, s, d, circ) in edges:
        cs, cd = cls[s], cls[d]
        if cs == cd and not circ:
            continue
        n += 1
        ib = 0 if col == B else 2
        pat[cd][ib] += 1      # in at dst
        pat[cs][ib + 1] += 1  # out at src
    return {k: tuple(v) for k, v in pat.items()}, n

def set_partitions(items):
    items = list(items)
    if not items:
        yield []
        return
    first, rest = items[0], items[1:]
    for p in set_partitions(rest):
        for i in range(len(p)):
            yield p[:i] + [[first] + p[i]] + p[i+1:]
        yield [[first]] + p

def lw(v, col): return (col, v, v, True)
def E(col, s, d): return (col, s, d, False)

def DE(a, w, q):
    """owxDE: G_{s d} -> G_{s a} G_{w d};  Gbar_{s d} -> Gbar_{s w} Gbar_{a d}  (circle dropped)."""
    col, s, d, _ = q
    if col == B:
        return [E(B, s, a), E(B, w, d)]
    return [E(R, s, w), E(R, a, d)]

# ------------------------------------------------------------------------------------------------------------------
# the 17 term formulas, in the frame (blue = the colour of the expanded loop / edge).  Each: (name, named symbols with
# forced-equal symbols already identified, q-variants, function(q) -> (removed, added, n_waved, new vertices))
def weight_terms():
    out = []
    out.append(('T1', ['w'], [None], lambda q: ([], [lw('al', B)], 1, ['al'])))
    out.append(('T2', ['w'], [None], lambda q: ([lw('w', B)], [lw('al', B), lw('be', B)], 2, ['al', 'be'])))
    qvars = [E(B, 'a', 'b'), E(R, 'a', 'b'), lw('a', B), lw('a', R)]   # q: same/opp colour, non-loop or a light-weight
    out.append(('T3', ['w', 'a', 'b'], qvars, lambda q: ([lw('w', B), q], DE('al', 'w', q) + [E(B, 'al', 'w')], 1, ['al'])))
    out.append(('T4', ['w', 'a', 'b'], qvars, lambda q: ([lw('w', B), q], DE('be', 'al', q) + [E(B, 'be', 'al')], 2, ['al', 'be'])))
    return out

def edge_terms():
    out = []
    out.append(('Oe1xOwx', ['x', 'v'], [None], lambda q: ([], [lw('al', B)], 1, ['al'])))
    # D: q any other non-loop edge, not a red out-edge of x and not a blue in-edge of x (in Q); all class coincidences allowed anyway
    qvars = [E(B, 'a', 'b'), E(R, 'a', 'b'), E(B, 'x', 'b'), E(R, 'a', 'x')]
    out.append(('D', ['x', 'v', 'a', 'b'], qvars, lambda q: ([E(B, 'x', 'v'), q], DE('al', 'x', q) + [E(B, 'al', 'v')], 1, ['al'])))
    out.append(('P5', ['x', 'v', 'd'], [None], lambda q: ([E(B, 'x', 'v'), E(R, 'x', 'd')], [lw('x', R), E(R, 'al', 'd'), E(B, 'al', 'v')], 1, ['al'])))
    out.append(('P3', ['x', 'v', 'd'], [None], lambda q: ([E(B, 'x', 'v'), E(R, 'x', 'd')], [E(R, 'al', 'd'), E(B, 'al', 'v')], 1, ['al'])))
    out.append(('P6', ['x', 'v', 's'], [None], lambda q: ([E(B, 'x', 'v'), E(B, 's', 'x')], [E(B, 's', 'al'), lw('x', B), E(B, 'al', 'v')], 1, ['al'])))
    out.append(('P4', ['x', 'v', 's'], [None], lambda q: ([E(B, 'x', 'v'), E(B, 's', 'x')], [E(B, 's', 'al'), E(B, 'al', 'v')], 1, ['al'])))
    return out

def gg_terms():
    out = []
    P1, Q1 = E(B, 'x', 'y'), E(B, 'yp', 'x')
    out.append(('R2', ['x', 'y', 'yp'], [None], lambda q: ([P1, Q1], [E(B, 'yp', 'y')], 1, [])))
    out.append(('R3', ['x', 'y', 'yp'], [None], lambda q: ([], [lw('al', B)], 1, ['al'])))
    out.append(('R4', ['x', 'y', 'yp'], [None], lambda q: ([P1, Q1], [E(B, 'al', 'y'), E(B, 'yp', 'al'), lw('be', B)], 2, ['al', 'be'])))
    out.append(('R5', ['x', 'y', 'yp'], [None], lambda q: ([P1, Q1], [lw('x', B), E(B, 'al', 'y'), E(B, 'yp', 'al')], 1, ['al'])))
    out.append(('R6', ['x', 'y', 'yp'], [None], lambda q: ([P1, Q1], [lw('al', B), E(B, 'be', 'y'), E(B, 'yp', 'be')], 2, ['al', 'be'])))
    qvars = [E(B, 'a', 'b'), E(R, 'a', 'b'), E(B, 'x', 'b'), E(B, 'a', 'x'), E(R, 'x', 'b'), E(R, 'a', 'x')]
    out.append(('R7', ['x', 'y', 'yp', 'a', 'b'], qvars, lambda q: ([P1, Q1, q], [E(B, 'yp', 'x')] + DE('al', 'x', q) + [E(B, 'al', 'y')], 1, ['al'])))
    out.append(('R8', ['x', 'y', 'yp', 'a', 'b'], qvars, lambda q: ([P1, Q1, q], [E(B, 'be', 'y'), E(B, 'yp', 'al')] + DE('be', 'al', q), 2, ['al', 'be'])))
    return out

ALL_TERMS = [('weight', t) for t in weight_terms()] + [('edge', t) for t in edge_terms()] + [('gg', t) for t in gg_terms()]

# ------------------------------------------------------------------------------------------------------------------
PATS = list(product(range(3), repeat=4))   # residual patterns (2 = "2 or more")

_MEMO = {}
def min_delta_elem(Rv, Av, fresh):
    """min over residual X of elem(X + A) - elem(X + R); for a fresh class X = 0."""
    k = (Rv, Av, fresh)
    if k in _MEMO: return _MEMO[k]
    r = _min_delta_elem(Rv, Av, fresh); _MEMO[k] = r; return r

def _min_delta_elem(Rv, Av, fresh):
    if fresh:
        return elem(Av) - elem(Rv), [(0,0,0,0)]
    best, arg = 9, []
    for X in PATS:
        d = elem(pat_add(X, Av)) - elem(pat_add(X, Rv))
        if d < best: best, arg = d, [X]
        elif d == best: arg.append(X)
    return best, arg

def placements(named_classes, news):
    """every way to place the new vertices: each alone in a fresh class, together in one fresh class, into a named class,
    or into an unnamed class C1/C2 (internal or external)."""
    opts = ['fresh'] + [('named', i) for i in range(len(named_classes))] + [('unn', 'C1', 'int'), ('unn', 'C1', 'ext'), ('unn', 'C2', 'int'), ('unn', 'C2', 'ext')]
    if not news:
        yield {}
        return
    if len(news) == 1:
        for o in opts:
            yield {news[0]: o}
        return
    for o1 in opts:
        for o2 in opts:
            yield {news[0]: o1, news[1]: o2}
    yield {news[0]: 'fresh_shared', news[1]: 'fresh_shared'}

def configs(term):
    name, syms, qvars, f = term
    for q in qvars:
        removed, added, nwav, news = f(q)
        syms_q = list(dict.fromkeys(syms + [v for e in (removed + added) for v in (e[1], e[2]) if v not in news]))
        for part in set_partitions(syms_q):
            # every class external or internal
            for ext in product((False, True), repeat=len(part)):
                for plc in placements(part, news):
                    yield q, removed, added, nwav, news, part, ext, plc

def build_classes(part, ext, plc, news):
    cls = {}; isext = {}; isfresh = {}
    for i, cl in enumerate(part):
        for v in cl: cls[v] = ('N', i)
        isext[('N', i)] = ext[i]; isfresh[('N', i)] = False
    nfresh = 0
    for nv in news:
        o = plc[nv]
        if o == 'fresh':
            cls[nv] = ('F', nv); isext[cls[nv]] = False; isfresh[cls[nv]] = True; nfresh += 1
        elif o == 'fresh_shared':
            cls[nv] = ('F', 'shared'); isext[cls[nv]] = False; isfresh[cls[nv]] = True
        elif o[0] == 'named':
            cls[nv] = ('N', o[1])
        else:
            cls[nv] = ('U', o[1]); isext[cls[nv]] = (o[2] == 'ext'); isfresh[cls[nv]] = False
    if any(plc[nv] == 'fresh_shared' for nv in news): nfresh = 1
    return cls, isext, isfresh, nfresh

def analyse_config(q, removed, added, nwav, news, part, ext, plc):
    cls, isext, isfresh, nfresh = build_classes(part, ext, plc, news)
    Rpat, nR = half_edges(removed, cls)
    Apat, nA = half_edges(added, cls)
    dord = nA - nR + 2 * nwav - 2 * nfresh
    classes = set(cls.values())
    delem = {}; total = dord
    for c in classes:
        if isext[c]:
            delem[c] = (0, None); continue
        Rv = Rpat.get(c, (0,0,0,0)); Av = Apat.get(c, (0,0,0,0))
        d, arg = min_delta_elem(Rv, Av, isfresh[c])
        delem[c] = (d, arg); total += d
    return dord, delem, total, cls, isext, isfresh, Rpat, Apat

def describe(part, ext, plc):
    s = ' '.join('{' + ','.join(cl) + '}' + ('E' if e else 'I') for cl, e in zip(part, ext))
    s += ' ' + ' '.join(f'{k}->{v}' for k, v in plc.items())
    return s

# ------------------------------------------------------------------------------------------------------------------
# repair analysis for failing configurations: concrete enumeration of residual patterns X for the classes of the term,
# residual edges between pairs of named classes included (r in {0,1,2} per ordered pair and colour), then test every single merge.
def c_of(nS, nW, nV, pats, isext):
    return nS + 2 * (nW - nV) + sum(1 for c, p in pats.items() if not isext[c] and elem(p))

def repair_search(q, removed, added, nwav, news, part, ext, plc, far, max_cases=None):
    """Returns (n_cases_failing, n_repaired, n_unrepaired, examples)."""
    cls, isext, isfresh, nfresh = build_classes(part, ext, plc, news)
    classes = sorted(set(cls.values()), key=str)
    nonfresh = [c for c in classes if not isfresh[c]]
    Rpat, nR = half_edges(removed, cls); Apat, nA = half_edges(added, cls)
    # residual: per non-fresh class a pattern X (counts 0..2 per type, meaning exact counts here), realised by edges to dummies,
    # plus explicit residual edges between pairs of non-fresh classes (0..1 per ordered pair and colour) that are subtracted from X
    # -- we enumerate X per class and between-edges, requiring consistency (between-edges' half-edges <= X).
    stats = Counter(); examples = []
    pairs = [(u, v) for u in nonfresh for v in nonfresh if u != v]
    # to keep it finite: between-edges only for pairs that could be merged in a repair (all pairs), 0 or 1 of each (colour, direction)
    between_opts = [()] + [((u, v, col),) for (u, v) in pairs for col in (B, R)] + \
        [((u, v, c1), (u2, v2, c2)) for ((u, v), c1), ((u2, v2), c2) in combinations([(p, c) for p in pairs for c in (B, R)], 2)]
    for Xs in product(PATS, repeat=len(nonfresh)):
        X = dict(zip(nonfresh, Xs))
        for btw in between_opts:
            # consistency: between edges' half edges must be contained in X
            need = defaultdict(lambda: [0,0,0,0])
            for (u, v, col) in btw:
                ib = 0 if col == B else 2
                need[v][ib] += 1; need[u][ib+1] += 1
            if any(any(need[c][i] > X[c][i] for i in range(4)) for c in nonfresh): continue
            # G0: patterns = X + R ; counts: nS0 = nR + (residual edges) ; residual edges = (sum of X half-edges - between half-edges)/... we only need differences
            before = {c: pat_add(X.get(c, (0,0,0,0)), Rpat.get(c, (0,0,0,0))) for c in classes}
            after = {c: pat_add(X.get(c, (0,0,0,0)), Apat.get(c, (0,0,0,0))) for c in classes}
            # ord differences relative to G0: G1: dord ; mu G0 (merge u,v): -(#G0 edges between u,v) + 2*[an internal class disappears]
            c0 = sum(1 for c in classes if not isext[c] and not isfresh[c] and elem(before[c]))
            c1 = (nA - nR + 2 * nwav - 2 * nfresh) + sum(1 for c in classes if not isext[c] and elem(after[c]))
            if c1 >= c0: continue
            stats['fail'] += 1
            repaired = None
            for u, v in combinations(nonfresh, 2):
                if far and isext[u] and isext[v]: continue
                # edges between u and v in G0: removed edges between them (existing) + between residual edges
                j = sum(1 for e in removed if {cls[e[1]], cls[e[2]]} == {u, v} and cls[e[1]] != cls[e[2]]) + sum(1 for (a_, b_, _) in btw if {a_, b_} == {u, v})
                # merged pattern: before[u] + before[v] minus the half-edges of the j edges
                sub = [0,0,0,0]
                for e in removed:
                    if {cls[e[1]], cls[e[2]]} == {u, v} and cls[e[1]] != cls[e[2]]:
                        ib = 0 if e[0] == B else 2; sub[ib] += 1; sub[ib+1] += 1
                for (a_, b_, col) in btw:
                    if {a_, b_} == {u, v}:
                        ib = 0 if col == B else 2; sub[ib] += 1; sub[ib+1] += 1
                merged = tuple(before[u][i] + before[v][i] - sub[i] for i in range(4))
                mext = isext[u] or isext[v]
                dnV = 0 if (isext[u] and isext[v]) else -1
                cmu = (-j - 2 * dnV) + sum(1 for c in classes if c not in (u, v) and not isext[c] and not isfresh[c] and elem(before[c])) + (0 if mext else int(elem(merged)))
                if cmu <= c1:
                    repaired = (u, v); break
            if repaired: stats['repaired'] += 1
            else:
                stats['UNREPAIRED'] += 1
                if len(examples) < 5: examples.append((X, btw, c0, c1))
            if max_cases and stats['fail'] >= max_cases: return stats, examples
    return stats, examples

def main():
    far = '--all' not in sys.argv
    grand = Counter()
    for kind, term in ALL_TERMS:
        name = term[0]
        per = Counter(); mins = {}
        fails = []
        for cfg in configs(term):
            q, removed, added, nwav, news, part, ext, plc = cfg
            dord, delem, total, cls, isext, isfresh, Rpat, Apat = analyse_config(*cfg)
            per['configs'] += 1
            key = str(q)
            mins[key] = min(mins.get(key, 99), total)
            if total < 0:
                per['naive_fail'] += 1
                fails.append((cfg, dord, delem, total))
        print(f'[{kind}/{name}] configs {per["configs"]}, min Delta c by q-variant: {mins}; naive failures (min over residuals < 0): {per["naive_fail"]}')
        grand['configs'] += per['configs']; grand['naive_fail'] += per['naive_fail']
        # repair analysis
        rep = Counter(); shown = 0
        for cfg, dord, delem, total in fails:
            q, removed, added, nwav, news, part, ext, plc = cfg
            st, ex = repair_search(*cfg, far=far)
            rep.update(st)
            if shown < 6:
                shown += 1
                print(f'    FAIL q={q} {describe(part, ext, plc)}: Delta ord={dord}, min Delta c={total}; residual cases failing {st["fail"]}, repaired {st["repaired"]}, UNREPAIRED {st["UNREPAIRED"]}')
            if st['UNREPAIRED']:
                for e in ex[:3]: print('      unrepaired example X, between, c0-c0, c1-c0:', e)
        if fails:
            print(f'    repair summary for {name}: {dict(rep)}')
        grand.update({('rep', k): v for k, v in rep.items()})
    print('GRAND:', dict(grand), '(far =', far, ')')


# ------------------------------------------------------------------------------------------------------------------
def shape(cfg):
    """existing removed / added edges as (colour, src class, dst class, circ), Delta ord, #fresh classes, #new waved edges."""
    q, removed, added, nwav, news, part, ext, plc = cfg
    cls, isext, isfresh, nfresh = build_classes(part, ext, plc, news)
    def ex(edges):
        return [(col, cls[s], cls[d], circ) for (col, s, d, circ) in edges if circ or cls[s] != cls[d]]
    rem, add = ex(removed), ex(added)
    dord = len(add) - len(rem) + 2 * nwav - 2 * nfresh
    return rem, add, dord, nfresh, nwav


def cancel(rem, add):
    rem, add = list(rem), list(add)
    for e in list(add):
        if e in rem:
            rem.remove(e); add.remove(e)
    return rem, add

def collapse_kind(cfg):
    """k-cycle collapse (k = 2, 3): after cancelling edges removed and re-added, the removed edges form a directed cycle of one colour
    on k distinct classes, nothing is added, no fresh vertex, k - 1 new waved edges, Delta ord = k - 2.  Returns k or None."""
    rem, add, dord, nfresh, nwav = shape(cfg)
    rem, add = cancel(rem, add)
    if add or nfresh: return None
    k = len(rem)
    if k not in (2, 3) or nwav != k - 1 or dord != k - 2: return None
    cols = {e[0] for e in rem}
    if len(cols) != 1: return None
    nxt = {e[1]: e[2] for e in rem}
    if len(nxt) != k or set(nxt.values()) != set(nxt.keys()): return None
    v = rem[0][1]; seen = []
    for _ in range(k):
        seen.append(v); v = nxt[v]
    return k if v == seen[0] and len(set(seen)) == k else None

def main_shapes():
    grand = Counter(); t0 = time.time(); collapses = []
    for kind, term in ALL_TERMS:
        name = term[0]
        per = Counter(); mins = {}; shapes = Counter(); other = []
        for cfg in configs(term):
            if any(cfg[6]) and '--ext' not in sys.argv: continue   # external flags: the all-internal case dominates (ext gives Delta elem = 0 >= min over X)
            q = cfg[0]
            dord, delem, total, cls, isext, isfresh, Rpat, Apat = analyse_config(*cfg)
            per['configs'] += 1
            key = str(q); mins[key] = min(mins.get(key, 99), total)
            if total < 0:
                per['naive_fail'] += 1
                k = collapse_kind(cfg)
                shapes[(f'{k}-cycle' if k else 'OTHER', total)] += 1
                if k: collapses.append((kind, name, cfg, k, total))
                else: other.append(cfg)
        print(f'[{kind}/{name}] configs (all classes internal) {per["configs"]}, min Delta c by q-variant: {mins}; naive failures: {per["naive_fail"]}; failing shapes: {dict(shapes)}')
        for cfg in other[:5]:
            print('    NON-COLLAPSE FAILURE:', cfg[0], describe(cfg[5], cfg[6], cfg[7]), shape(cfg))
        grand['configs'] += per['configs']; grand['naive_fail'] += per['naive_fail']; grand['other'] += len(other)
    print('GRAND:', dict(grand), f't={time.time()-t0:.0f}s')
    print('collapse configurations (term, q, classes, placement, k, min Delta c):')
    for kind, name, cfg, k, total in collapses:
        print(f'   {kind}/{name} q={cfg[0]} {describe(cfg[5], cfg[6], cfg[7])} k={k} min Delta c={total}')

def check_cycle_repair(k):
    """The repair for a k-cycle collapse on classes C_1..C_k (the removed edges C_i -> C_{i+1} of one colour; nothing added;
    k - 1 new waved edges), exhaustively over the residual patterns of the k classes (exact counts 0..2 per type), the residual
    edges among the k classes (0..2, consistent with the patterns) and the external flags: whenever c(G1) < c(G0), the classes
    contain at most one external class and merging all k classes gives c(mu G0) <= c(G1)."""
    bad = 0; tested = 0; fails = 0; two_ext = 0
    cls = list(range(k))
    pairs = [(u, v) for u in cls for v in cls if u != v]
    btw_opts = [()] + [((u, v, col),) for (u, v) in pairs for col in (B, R)] + \
        [(a, b) for a, b in combinations([(u, v, col) for (u, v) in pairs for col in (B, R)], 2)]
    for ext in product((False, True), repeat=k):
        for Xs in product(PATS, repeat=k):
            cyc = (1,1,0,0)
            c0 = sum(0 if ext[c] else elem(pat_add(Xs[c], cyc)) for c in cls)
            c1 = (k - 2) + sum(0 if ext[c] else elem(Xs[c]) for c in cls)
            tested += 1
            if c1 >= c0: continue
            for btw in btw_opts:
                need = [[0,0,0,0] for _ in cls]
                for (u, v, col) in btw:
                    ib = 0 if col == B else 2
                    need[u][ib+1] += 1; need[v][ib] += 1
                if any(need[c][i] > Xs[c][i] for c in cls for i in range(4)): continue
                fails += 1
                ne = sum(ext)
                if ne >= 2: two_ext += 1; continue
                r = len(btw)
                merged = tuple(sum(Xs[c][i] for c in cls) - sum(need[c][i] for c in cls) for i in range(4))
                dnV = -(k - 1)
                cmu = -k - r - 2 * dnV + (0 if ne else elem(merged))
                if cmu > c1: bad += 1
    print(f'{k}-cycle collapse repair: tested {tested} residual patterns (x ext flags); failing (pattern, residual-edge) cases {fails}; >= 2 external classes among them: {two_ext}; repair (merge the k classes) fails: {bad}')

if __name__ == '__main__':
    # default (also `--shapes`): classify every configuration of the 17 terms, then verify the k-cycle repairs (seconds);
    # `--ext`: include the external/internal flags of the named classes; `--full-repair`: the slow per-configuration repair search.
    if '--full-repair' in sys.argv:
        main()
    else:
        main_shapes(); check_cycle_repair(2); check_cycle_repair(3)
