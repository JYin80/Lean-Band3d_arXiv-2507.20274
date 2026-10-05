"""2026-10-04-localreg6-model.py  (Fable, LW-10c preflight)
Python model of the merged Lean `LocStep` (RBM3D/Graph/LWLvl1.lean:3260-3275) with the dotted-edge partition
(LWVocab.lean:1303), and the candidate potentials for property (6) of lem:localregular:
  Psi    = ord + |L| + sum_chains (k - 2[cycle] - [closed via one vertex])          (exact R2-resolution cost)
  PsiLoc = ord + |L| + max |DV| over local markings (independent set in the chain graph, 2-cycles excluded)
  Psi3   = Psi - sum_{pairs {a,b}} (m(a,b) - 2)_+                                   (parallel chains discounted)
See 2026-10-04-localreg6.md.  Run 2026-10-04-localreg6-verify.py for the checks.
"""

from itertools import product
from collections import Counter

EXT = ('x', 'y', 'xy')


def is_ext(v):
    return isinstance(v, str)


class Graph:
    __slots__ = ('n', 'solid', 'waved', 'dotted', '_mol', 'ext')

    def __init__(self, n, solid, waved, dotted=None, ext=('x', 'y')):
        self.n = n
        self.ext = tuple(ext)
        self.solid = tuple(solid)
        self.waved = tuple(waved)
        if dotted is None:
            dotted = frozenset(frozenset((s, d)) for (_, _, s, d) in self.solid if s != d)
        self.dotted = dotted
        self._mol = None

    # ---- vertices -------------------------------------------------------------------------
    def vertices(self):
        vs = set(range(self.n)) | set(self.ext)
        for (_, _, s, d) in self.solid:
            vs.add(s); vs.add(d)
        for (u, v) in self.waved:
            vs.add(u); vs.add(v)
        return vs

    def externals(self):
        return sorted(self.ext)

    # ---- molecules (components of the waved graph; a normal graph has no =-dotted edge) -------
    def molecules(self):
        if self._mol is not None:
            return self._mol
        parent = {}
        verts = self.vertices()
        for v in verts:
            parent[v] = v

        def find(a):
            while parent[a] != a:
                parent[a] = parent[parent[a]]
                a = parent[a]
            return a
        for (u, v) in self.waved:
            ru, rv = find(u), find(v)
            if ru != rv:
                parent[ru] = rv
        mol = {v: find(v) for v in verts}
        self._mol = mol
        return mol

    def far(self):
        """M_x != M_y (false once x and y are merged into 'xy')."""
        mol = self.molecules()
        if 'xy' in mol:
            return False
        return mol['x'] != mol['y']

    # ---- counters, (eq:ordG) -------------------------------------------------------------------
    def nS(self):
        return len(self.solid)

    def nW(self):
        return len(self.waved)

    def nV(self):
        return self.n

    def nM(self):
        mol = self.molecules()
        ext_mols = {mol[v] for v in mol if is_ext(v)}
        return len({mol[v] for v in mol if not is_ext(v)} - ext_mols)

    def ord(self):
        return self.nS() + 2 * (self.nW() - self.nV())

    # ---- degree / charge (LWLvl1.lean:1528-1546) ------------------------------------------------
    def inc(self, v):
        return [e for e in self.solid if e[2] != e[3] and (e[2] == v or e[3] == v)]

    def deg(self, v):
        return len(self.inc(v))

    def charge(self, v):
        c = 0
        for (sig, _, s, d) in self.inc(v):
            if s == v:
                c += -1 if sig else 1
            else:
                c += 1 if sig else -1
        return c

    def loops(self):
        return [e for e in self.solid if e[2] == e[3]]

    def std_neutral(self, v):
        inc = self.inc(v)
        return len(inc) == 2 and self.charge(v) == 0 and inc[0][0] != inc[1][0]

    def locstd(self):
        """LGraph.LocStd (LWLvl1.lean:3204): normal, no loops, every internal vertex standard neutral or isolated."""
        if self.loops():
            return False
        for v in range(self.n):
            if self.deg(v) != 0 and not self.std_neutral(v):
                return False
        return True

    def hbad(self, v):
        d = self.deg(v)
        return d != 0 and (d != 2 or self.charge(v) != 0)

    def hnb(self):
        for v in range(self.n):
            d = self.deg(v)
            if not (d == 0 or (d == 2 and self.charge(v) == 0)):
                return False
        return True

    # ---- canonical key (complete up to isomorphism via individualisation-refinement) -----------
    def key(self):
        return canon(self)

    def __repr__(self):
        return f"Graph(n={self.n}, solid={list(self.solid)}, waved={list(self.waved)})"


# ---------------------------------------------------------------------------------------------
# twists
def twist_edges(solid, c, t):
    out = []
    for (sig, circ, s, d) in solid:
        if c:
            sig = not sig
        if t:
            s, d = d, s
        out.append((sig, circ, s, d))
    return out


def DE(alpha, w, e):
    """owxDE (LWWeightExp.lean:468): G_{ab} -> G_{a alpha} G_{w b};  Gbar_{ab} -> Gbar_{a w} Gbar_{alpha b}."""
    sig, _, s, d = e
    if sig:
        return [(True, False, s, alpha), (True, False, w, d)]
    return [(False, False, s, w), (False, False, alpha, d)]


# ---------------------------------------------------------------------------------------------
# the three steps: each yields (label, term) with term = (solid, waved, n_new) in the ORIGINAL orientation
def weight_steps(G):
    """LocStep.weight: for every light-weight p.1 (circled loop) at a vertex w (external or internal),
    both transposes t; c is forced (the loop must be blue in the frame)."""
    for i, e in enumerate(G.solid):
        sig, circ, s, d = e
        if not (s == d and circ):
            continue
        w = s
        c = not sig
        for t in (False, True):
            fr = twist_edges(G.solid, c, t)
            p1 = fr[i]
            others = fr[:i] + fr[i + 1:]
            a, b = G.n, G.n + 1
            terms = []
            terms.append(('T1', fr + [(True, True, a, a)], list(G.waved) + [(w, a)], 1))
            terms.append(('T2', others + [(True, True, a, a), (True, True, b, b)], list(G.waved) + [(w, a), (a, b)], 2))
            for j, q in enumerate(others):
                rest = others[:j] + others[j + 1:]
                terms.append(('T3', rest + DE(a, w, q) + [(True, False, a, w)], list(G.waved) + [(w, a)], 1))
                terms.append(('T4', rest + DE(b, a, q) + [(True, False, b, a)], list(G.waved) + [(w, a), (a, b)], 2))
            for (lab, sol, wav, k) in terms:
                yield (lab, (twist_edges(sol, c, t), wav, k))


def edge_steps(G):
    """LocStep.edge: no loops (hwf), x internal with hbad, p.1 any non-loop edge at x (made the blue out-edge)."""
    if G.loops():
        return
    for i, e in enumerate(G.solid):
        sig, circ, s, d = e
        if s == d:
            continue
        for x in (s, d):
            if is_ext(x) or not G.hbad(x):
                continue
            t = (d == x)  # transpose so that the edge is x -> v in the frame
            c = not sig
            fr = twist_edges(G.solid, c, t)
            p1 = fr[i]
            assert p1[0] and p1[2] == x
            v = p1[3]
            others = fr[:i] + fr[i + 1:]
            a = G.n
            terms = []
            terms.append(('Oe1xOwx', fr + [(True, True, a, a)], list(G.waved) + [(x, a)], 1))
            for j, q in enumerate(others):
                rest = others[:j] + others[j + 1:]
                qs, qc, qsrc, qdst = q
                if (not qs) and qsrc == x:
                    terms.append(('P5', rest + [(False, True, x, x), (False, False, a, qdst), (True, False, a, v)], list(G.waved) + [(x, a)], 1))
                    terms.append(('P3', rest + [(False, False, a, qdst), (True, False, a, v)], list(G.waved) + [(x, a)], 1))
                elif qs and qdst == x:
                    terms.append(('P6', rest + [(True, False, qsrc, a), (True, True, x, x), (True, False, a, v)], list(G.waved) + [(x, a)], 1))
                    terms.append(('P4', rest + [(True, False, qsrc, a), (True, False, a, v)], list(G.waved) + [(x, a)], 1))
                else:
                    terms.append(('D', rest + DE(a, x, q) + [(True, False, a, v)], list(G.waved) + [(x, a)], 1))
            for (lab, sol, wav, k) in terms:
                yield (lab, (twist_edges(sol, c, t), wav, k))


def gg_steps(G):
    """LocStep.gg: no loops, hnb for all internal vertices, x internal with p.1 = G_{xy}, q.1 = G_{y'x} (same colour,
    one out one in; both orders of the pair are allowed, the transpose t makes p.1 the out-edge)."""
    if G.loops() or not G.hnb():
        return
    for x in range(G.n):
        inc = [(i, e) for i, e in enumerate(G.solid) if e[2] != e[3] and (e[2] == x or e[3] == x)]
        if len(inc) != 2 or G.charge(x) != 0:
            continue
        (i1, e1), (i2, e2) = inc
        if e1[0] != e2[0]:
            continue  # standard neutral, not a GG vertex
        for (ip, ep), (iq, eq) in (((i1, e1), (i2, e2)), ((i2, e2), (i1, e1))):
            t = (ep[3] == x)  # transpose so that p.1 is x -> y
            c = not ep[0]
            fr = twist_edges(G.solid, c, t)
            p1, q1 = fr[ip], fr[iq]
            assert p1[0] and p1[2] == x and q1[0] and q1[3] == x, (p1, q1, x)
            y, yp = p1[3], q1[2]
            f = [e for k, e in enumerate(fr) if k not in (ip, iq)]
            a, b = G.n, G.n + 1
            W = list(G.waved)
            terms = []
            terms.append(('R2', f + [(True, False, yp, y)], W + [(x, y)], 0))
            terms.append(('R3', fr + [(True, True, a, a)], W + [(x, a)], 1))
            terms.append(('R4', f + [(True, False, a, y), (True, False, yp, a), (True, True, b, b)], W + [(x, a), (a, b)], 2))
            terms.append(('R5', f + [(True, True, x, x), (True, False, a, y), (True, False, yp, a)], W + [(x, a)], 1))
            terms.append(('R6', f + [(True, True, a, a), (True, False, b, y), (True, False, yp, b)], W + [(x, a), (a, b)], 2))
            for j, qp in enumerate(f):
                rest = f[:j] + f[j + 1:]
                terms.append(('R7', rest + [(True, False, yp, x)] + DE(a, x, qp) + [(True, False, a, y)], W + [(x, a)], 1))
                terms.append(('R8', rest + [(True, False, b, y), (True, False, yp, a)] + DE(b, a, qp), W + [(x, a), (a, b)], 2))
            for (lab, sol, wav, k) in terms:
                yield (lab, (twist_edges(sol, c, t), wav, k))


# ---------------------------------------------------------------------------------------------
# the dotted-edge partition of a term (LWVocab.lean:1061-1305)
def partition(G, term):
    solid, waved, k = term
    n = G.n + k
    dotted = G.dotted  # the parent's x-dotted edges, mapped by emb (identity)
    pairs_solid = {frozenset((s, d)) for (_, _, s, d) in solid if s != d}
    a_pairs = sorted(pairs_solid - dotted, key=lambda p: sorted(map(str, p)))
    b_pairs = sorted(dotted - pairs_solid, key=lambda p: sorted(map(str, p)))
    base = dotted & pairs_solid  # dotBase: x-dotted edges that still have a solid edge
    verts = set(range(n)) | {v for e in solid for v in (e[2], e[3])} | {v for e in waved for v in e}
    verts |= set(G.externals())
    verts = sorted(verts, key=str)
    outs = []
    for ca in product((True, False), repeat=len(a_pairs)):  # True: '=' ; False: '!='
        for cb in product((False, True), repeat=len(b_pairs)):  # False: drop ; True: '=' (coefficient -1)
            eqs = [p for p, c in zip(a_pairs, ca) if c] + [p for p, c in zip(b_pairs, cb) if c]
            neqs = list(base) + [p for p, c in zip(a_pairs, ca) if not c]
            # classes
            par = {v: v for v in verts}

            def find(u):
                while par[u] != u:
                    par[u] = par[par[u]]
                    u = par[u]
                return u
            for p in eqs:
                u, v = tuple(p)
                ru, rv = find(u), find(v)
                if ru != rv:
                    par[ru] = rv
            ok = True
            for p in neqs:
                u, v = tuple(p)
                if find(u) == find(v):
                    ok = False
                    break
            if not ok:
                continue
            # merge: name the classes
            classes = {}
            for v in verts:
                classes.setdefault(find(v), []).append(v)
            name = {}
            nxt = 0
            for r, mem in classes.items():
                exts = [v for v in mem if is_ext(v)]
                if exts:
                    s = ''.join(sorted(set(''.join(exts))))
                    nm = 'xy' if 'x' in s and 'y' in s else s
                else:
                    nm = nxt
                    nxt += 1
                for v in mem:
                    name[v] = nm
            msolid = [(sig, circ, name[s], name[d]) for (sig, circ, s, d) in solid]
            mwaved = [(name[u], name[v]) for (u, v) in waved]
            # splitWeights: every uncircled loop -> circled (light-weight) or dropped (constant m)
            wl = [i for i, e in enumerate(msolid) if e[2] == e[3] and not e[1]]
            for choice in product((True, False), repeat=len(wl)):
                sol2 = []
                for i, e in enumerate(msolid):
                    if i in wl:
                        if choice[wl.index(i)]:
                            sol2.append((e[0], True, e[2], e[3]))
                        # else dropped
                    else:
                        sol2.append(e)
                H = Graph(nxt, sol2, mwaved, ext=tuple(sorted({nm for nm in name.values() if is_ext(nm)})))
                outs.append(H)
    return outs


def all_steps(G):
    """All (kind, label, child) for every LocStep from G (every choice of p, q, c, t)."""
    for lab, term in weight_steps(G):
        for H in partition(G, term):
            yield ('weight', lab, H)
    for lab, term in edge_steps(G):
        for H in partition(G, term):
            yield ('edge', lab, H)
    for lab, term in gg_steps(G):
        for H in partition(G, term):
            yield ('gg', lab, H)


# ---------------------------------------------------------------------------------------------
def fxyPow(p):
    """fxyPowGraph p (LocalRegular.lean): alpha_i = 2i, beta_i = 2i+1, blue iff i < p/2."""
    solid, waved = [], []
    for i in range(p):
        sig = i < p // 2
        a, b = 2 * i, 2 * i + 1
        solid += [(sig, True, b, b), (sig, False, 'x', a), (sig, False, a, 'y')]
        waved.append((a, b))
    return Graph(2 * p, solid, waved)


# ---------------------------------------------------------------------------------------------
# canonical form (individualisation / refinement)
def canon(G):
    verts = sorted(G.vertices(), key=str)
    idx = {v: i for i, v in enumerate(verts)}
    N = len(verts)
    # initial colours: external name, internal 0
    col = [(('E', v) if is_ext(v) else ('I',)) for v in verts]
    S = [(sig, circ, idx[s], idx[d]) for (sig, circ, s, d) in G.solid]
    W = [(idx[u], idx[v]) for (u, v) in G.waved]

    def refine(col):
        col = list(col)
        while True:
            sig_ = [[] for _ in range(N)]
            for (sg, cc, s, d) in S:
                sig_[s].append(('so', sg, cc, col[d]))
                sig_[d].append(('si', sg, cc, col[s]))
            for (u, v) in W:
                sig_[u].append(('w', col[v]))
                sig_[v].append(('w', col[u]))
            new = [(col[i], tuple(sorted(map(repr, sig_[i])))) for i in range(N)]
            ranks = {c: r for r, c in enumerate(sorted(set(new)))}
            new2 = [ranks[c] for c in new]
            old_ranks = {c: r for r, c in enumerate(sorted(set(map(repr, col))))}
            if len(set(new2)) == len(set(map(repr, col))):
                # stable
                return new2
            col = new2

    def encode(col):
        # col discrete: order vertices by colour
        order = sorted(range(N), key=lambda i: col[i])
        pos = {i: r for r, i in enumerate(order)}
        s = tuple(sorted((sg, cc, pos[a], pos[b]) for (sg, cc, a, b) in S))
        w = tuple(sorted(tuple(sorted((pos[a], pos[b]))) for (a, b) in W))
        e = tuple((pos[idx[v]], v) for v in verts if is_ext(v))
        return (N, s, w, e)

    best = [None]

    def search(col):
        col = refine(col)
        cells = {}
        for i, c in enumerate(col):
            cells.setdefault(c, []).append(i)
        nons = [c for c in sorted(cells) if len(cells[c]) > 1]
        if not nons:
            enc = encode(col)
            if best[0] is None or enc < best[0]:
                best[0] = enc
            return
        c = nons[0]
        for i in cells[c]:
            col2 = list(col)
            col2 = [(cc, 0) if j != i else (cc, 1) for j, cc in enumerate(col2)]
            # re-rank
            ranks = {k: r for r, k in enumerate(sorted(set(col2)))}
            search([ranks[k] for k in col2])
    search([0 if c == ('I',) else (1 + EXT.index(c[1])) for c in col])
    return best[0]


# ===== potentials (pot.py) =====



def half_pattern(G, v):
    bi = bo = ri = ro = 0
    for (sig, _, s, d) in G.solid:
        if s == v and d == v:
            if sig: bi += 1; bo += 1
            else: ri += 1; ro += 1
        elif s == v:
            if sig: bo += 1
            else: ro += 1
        elif d == v:
            if sig: bi += 1
            else: ri += 1
    return (bi, bo, ri, ro)


def analyse(G):
    """returns (E_sc: set of SC vertices, E_lw: set of lone-lw vertices, chains: list of (kind, length))"""
    sc = set(); lw = set()
    nxt = {}; pred = {}
    for v in range(G.n):
        pat = half_pattern(G, v)
        if pat in ((1, 1, 0, 0), (0, 0, 1, 1)):
            if any(s == d == v for (_, _, s, d) in G.solid):
                lw.add(v)
            else:
                sc.add(v)
                for (sig, _, s, d) in G.solid:
                    if s == v: nxt[v] = d
                    elif d == v: pred[v] = s
    chains = []
    seen = set()
    for v0 in sorted(sc):
        if v0 in seen:
            continue
        u = v0; back = [v0]
        while pred[u] in sc and pred[u] not in back:
            u = pred[u]; back.append(u)
        if pred[u] in back:
            chains.append(('cyc', len(back)))
            seen |= set(back)
            continue
        entry = pred[u]
        chain = [u]; v = nxt[u]
        while v in sc:
            chain.append(v); v = nxt[v]
        seen |= set(chain)
        if entry == v:
            chains.append(('cyc1_ext' if is_ext(v) else 'cyc1_int', len(chain)))
        else:
            chains.append(('open', len(chain)))
    return sc, lw, chains


def D(G):
    sc, lw, chains = analyse(G)
    d = len(lw)
    for kind, k in chains:
        d += k - (2 if kind == 'cyc' else (1 if kind.startswith('cyc1') else 0))
    return d


def Psi(G):
    return G.ord() + D(G)


def describe(G):
    sc, lw, chains = analyse(G)
    return f'ord={G.ord()} D={D(G)} sc={sorted(sc)} lonelw={sorted(lw)} chains={chains}'


def max_parallel(G):
    """max over unordered pairs {a,b} of non-SC vertices of (#SC chains connecting a and b) + (#solid edges between a and b)."""
    from collections import Counter
    sc, lw, chains = analyse(G)
    # recompute chains with endpoints
    nxt = {}; pred = {}
    for v in sc:
        for (sig, _, s, d) in G.inc(v):
            if s == v: nxt[v] = d
            else: pred[v] = s
    cnt = Counter()
    seen = set()
    for v0 in sorted(sc):
        if v0 in seen: continue
        u = v0; back = [v0]
        while pred[u] in sc and pred[u] not in back:
            u = pred[u]; back.append(u)
        if pred[u] in back:
            seen |= set(back); continue
        entry = pred[u]; chain = [u]; v = nxt[u]
        while v in sc:
            chain.append(v); v = nxt[v]
        seen |= set(chain)
        cnt[frozenset((str(entry), str(v)))] += 1
    for (sig, _, s, d) in G.solid:
        if s != d and s not in sc and d not in sc:
            cnt[frozenset((str(s), str(d)))] += 1
    best = max(cnt.values()) if cnt else 0
    return best

# ===== PsiLoc (pot2.py) =====



def Dloc(G):
    sc, lw, chains = analyse(G)
    d = len(lw)
    for kind, k in chains:
        if kind == 'cyc':
            d += 0 if k == 2 else k // 2
        elif kind.startswith('cyc1'):
            d += 0 if k == 1 else (k + 1) // 2
        else:
            d += (k + 1) // 2
    return d


def PsiLoc(G):
    return G.ord() + Dloc(G)

# ===== Psi3 (pot3.py) =====



def analyse3(G):
    sc = set(); lw = set(); nxt = {}; pred = {}
    for v in range(G.n):
        pat = half_pattern(G, v)
        if pat in ((1, 1, 0, 0), (0, 0, 1, 1)):
            if any(s == d == v for (_, _, s, d) in G.solid):
                lw.add(v)
            else:
                sc.add(v)
                for (sig, _, s, d) in G.solid:
                    if s == v: nxt[v] = d
                    elif d == v: pred[v] = s
    chains = []   # (kind, k, entry, exit)
    seen = set()
    for v0 in sorted(sc):
        if v0 in seen: continue
        u = v0; back = [v0]
        while pred[u] in sc and pred[u] not in back:
            u = pred[u]; back.append(u)
        if pred[u] in back:
            chains.append(('cyc', len(back), None, None)); seen |= set(back); continue
        entry = pred[u]; chain = [u]; v = nxt[u]
        while v in sc:
            chain.append(v); v = nxt[v]
        seen |= set(chain)
        chains.append(('cyc1' if entry == v else 'open', len(chain), entry, v))
    return sc, lw, chains


def D3(G):
    sc, lw, chains = analyse3(G)
    d = len(lw)
    pairs = Counter()
    for kind, k, e, f in chains:
        d += k - (2 if kind == 'cyc' else (1 if kind == 'cyc1' else 0))
        if kind == 'open':
            pairs[frozenset((e, f))] += 1
    for pr, m in pairs.items():
        d -= max(0, m - 2)
    return d


def Psi3(G):
    return G.ord() + D3(G)


def describe3(G):
    sc, lw, chains = analyse3(G)
    return f'ord={G.ord()} D3={D3(G)} sc={sorted(sc)} lonelw={sorted(lw)} chains={[(k, n, str(e), str(f)) for k, n, e, f in chains]}'