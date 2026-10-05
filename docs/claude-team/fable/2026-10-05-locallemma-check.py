"""2026-10-05-locallemma-check.py  (Fable, LW-10c): concrete cross-checks of the local cost c = ord + #elem and of
Phi = min over partitions of c(M_pi .), on the Python model of LocStep (2026-10-04-localreg6-model.py, same directory).

  python3 2026-10-05-locallemma-check.py premerge p ndesc seed maxdepth npart far|xy     local lemma on real (Q, pi0, T, placement)
  python3 2026-10-05-locallemma-check.py phi p ORDMAX nkids seed                          Phi(Q') >= Phi(Q) by brute force over partitions
  python3 2026-10-05-locallemma-check.py init pmax                                        Phi^far(Gamma_p), Phi^all(Gamma_p)
  python3 2026-10-05-locallemma-check.py cexpath file                                     Phi along the recorded path on which Psi decreased
  python3 2026-10-05-locallemma-check.py lemmaA p ndesc seed maxdepth                     dropping a loop never increases c
"""
import sys, os, time, random, importlib.util
from collections import Counter, deque
from itertools import product

here = os.path.dirname(os.path.abspath(__file__))
spec = importlib.util.spec_from_file_location('lr6model', os.path.join(here, '2026-10-04-localreg6-model.py'))
M = importlib.util.module_from_spec(spec); spec.loader.exec_module(M)
Graph, fxyPow, all_steps, is_ext = M.Graph, M.fxyPow, M.all_steps, M.is_ext

ELEM = ((1, 1, 0, 0), (0, 0, 1, 1))


def nelem(G):
    return sum(1 for v in range(G.n) if M.half_pattern(G, v) in ELEM)


def c(G):
    return G.ord() + nelem(G)


def merge_classes(n, ext, solid, waved, classes):
    """M_pi: merge the classes (dict vertex -> class id; a class containing an external vertex is named by the externals it
    contains), keep circled loops, drop every other solid edge inside a class."""
    ids = sorted({cl for cl in classes.values() if not is_ext(cl)})
    ren = {cl: i for i, cl in enumerate(ids)}
    nm = lambda v: classes[v] if is_ext(classes[v]) else ren[classes[v]]
    sol = [(sig, circ, nm(s_), nm(d)) for (sig, circ, s_, d) in solid if (s_ == d and circ) or nm(s_) != nm(d)]
    wav = [(nm(u), nm(v)) for (u, v) in waved]
    return Graph(len(ids), sol, wav, ext=tuple(sorted({nm(v) for v in ext})))


def class_name(members):
    exts = sorted({v for v in members if is_ext(v)})
    if not exts:
        return None
    s = ''.join(sorted(set(''.join(exts))))
    return 'xy' if ('x' in s and 'y' in s) else s


def set_partitions(items):
    items = list(items)
    if not items:
        yield []
        return
    first, rest = items[0], items[1:]
    for p in set_partitions(rest):
        for i in range(len(p)):
            yield p[:i] + [[first] + p[i]] + p[i + 1:]
        yield [[first]] + p


def all_merges(G, far):
    verts = sorted(G.vertices(), key=str)
    for part in set_partitions(verts):
        cls = {}
        ok = True
        for i, mem in enumerate(part):
            nm = class_name(mem)
            if nm == 'xy' and far:
                ok = False; break
            for v in mem:
                cls[v] = nm if nm is not None else ('c', i)
        if not ok:
            continue
        yield cls, merge_classes(G.n, G.ext, G.solid, G.waved, cls)


def Phi(G, far):
    return min(c(H) for _, H in all_merges(G, far))


# ----------------------------------------------------------------------------------------------------------------
def collapse_classes(Q, cl0, solid_T, cl):
    """If the term, read on the merged graph, is a k-cycle collapse (k = 2, 3): returns the set of collapsed classes, else None.
    Removed edges = edges of Q not in T (by multiset), added = edges of T not in Q; both read in classes; cancel; test."""
    rem = Counter(Q.solid); add = Counter(solid_T)
    common = rem & add
    rem -= common; add -= common
    def kept(e, cls):
        sig, circ, s, d = e
        return circ or cls[s] != cls[d]
    R = [(sig, cl0[s], cl0[d]) for (sig, circ, s, d), k in rem.items() for _ in range(k) if kept((sig, circ, s, d), cl0)]
    A = [(sig, cl[s], cl[d]) for (sig, circ, s, d), k in add.items() for _ in range(k) if kept((sig, circ, s, d), cl)]
    # cancel equal class-edges
    Rc, Ac = Counter(R), Counter(A)
    com = Rc & Ac; Rc -= com; Ac -= com
    if sum(Ac.values()):
        return None
    R = list(Rc.elements())
    k = len(R)
    if k not in (2, 3) or len({e[0] for e in R}) != 1:
        return None
    nxt = {s: d for (_, s, d) in R}
    if len(nxt) != k or set(nxt.values()) != set(nxt):
        return None
    v = R[0][1]; seen = []
    for _ in range(k):
        seen.append(v); v = nxt[v]
    if v != seen[0] or len(set(seen)) != k:
        return None
    return set(seen)


def run_premerge(p, ND, seed, MAXD, NPART, allow_xy):
    random.seed(seed)
    stats = Counter(); t0 = time.time(); shown = 0
    gens = (M.weight_steps, M.edge_steps, M.gg_steps)
    for di in range(ND):
        G = fxyPow(p); depth = 0
        while depth < MAXD and not G.locstd():
            verts = sorted(G.vertices(), key=str)
            for _ in range(NPART):
                cl0 = {v: v for v in verts}
                for _m in range(random.choice([0, 1, 1, 2, 2, 3, 4])):
                    u, v = random.sample(verts, 2); cu, cv = cl0[u], cl0[v]
                    if cu == cv:
                        continue
                    if is_ext(cu) and is_ext(cv):
                        if not allow_xy:
                            continue
                        tgt = 'xy'; src = None
                        for w in verts:
                            if cl0[w] in (cu, cv): cl0[w] = tgt
                        continue
                    tgt = cu if is_ext(cu) else (cv if is_ext(cv) else cu); src = cv if tgt == cu else cu
                    for w in verts:
                        if cl0[w] == src: cl0[w] = tgt
                G0 = merge_classes(G.n, G.ext, G.solid, G.waved, cl0); c0 = c(G0)
                class_ids = sorted(set(cl0.values()), key=str)
                for gen in gens:
                    for lab, (solid, waved, k) in gen(G):
                        news = list(range(G.n, G.n + k))
                        opts = ['fresh'] + class_ids
                        if k == 2:
                            opts_pairs = [(o1, o2) for o1 in opts for o2 in opts] + [('shared', 'shared')]
                        else:
                            opts_pairs = [(o,) for o in opts] if k == 1 else [()]
                        for plc in opts_pairs:
                            cl = dict(cl0)
                            for nv, o in zip(news, plc):
                                cl[nv] = nv if o == 'fresh' else ('shared' if o == 'shared' else o)
                            T = merge_classes(G.n + k, G.ext, solid, waved, cl)
                            if not allow_xy and 'xy' in T.ext:
                                continue
                            c1 = c(T)
                            real = all(o == 'fresh' or o == 'shared' or any(cl0.get(u) == o for e in solid if nv in (e[2], e[3]) and e[2] != e[3] for u in (e[2], e[3]) if u != nv) for nv, o in zip(news, plc))
                            key = 'realizable' if real else 'unrealizable'
                            stats[(key, 'tests')] += 1
                            if c1 >= c0:
                                continue
                            stats[(key, 'naive_fail')] += 1
                            coll = collapse_classes(G, cl0, solid, cl)
                            if coll is None:
                                stats[(key, 'FAIL_NOT_COLLAPSE')] += 1
                                if shown < 3:
                                    shown += 1
                                    print(f'NOT A COLLAPSE: {lab} plc={plc} c {c0} -> {c1}\n  Q {G}\n  cl0 {cl0}\n  T {T}', flush=True)
                                continue
                            stats[(key, f'collapse{len(coll)}')] += 1
                            cl2 = dict(cl0)
                            tgt = next((cc for cc in coll if is_ext(cc)), None) or min(coll, key=str)
                            for w in verts:
                                if cl2[w] in coll: cl2[w] = tgt
                            G2 = merge_classes(G.n, G.ext, G.solid, G.waved, cl2)
                            if c(G2) <= c1:
                                stats[(key, 'repaired')] += 1
                            else:
                                stats[(key, 'FAIL_REPAIR')] += 1
                                if shown < 3:
                                    shown += 1
                                    print(f'REPAIR FAILS: {lab} plc={plc} c0 {c0} c1 {c1} c(mu G0) {c(G2)}\n  Q {G}\n  cl0 {cl0}\n  T {T}', flush=True)
            kids = [H for kind, lab, H in all_steps(G) if allow_xy or H.far()]
            if not kids:
                break
            kids.sort(key=lambda H: H.ord()); G = random.choice(kids[:max(1, len(kids) // 3)]); depth += 1
    print(f'DONE premerge(c) p={p} seed={seed} allow_xy={allow_xy} descents={ND} depth<={MAXD}: {dict(sorted(stats.items()))}; t={time.time()-t0:.0f}s')


def run_phi(p, ORDMAX, NKIDS, seed):
    random.seed(seed)
    t0 = time.time()
    G0 = fxyPow(p); frontier = {G0.key(): G0}; queue = deque([G0.key()])
    nstates = 0; nchecked = Counter(); viol = Counter(); minphi = {'far': 99, 'all': 99}; locstd_min = {}
    while queue:
        k = queue.popleft(); G = frontier[k]
        if len(G.vertices()) > 8:
            continue
        nstates += 1
        phi = {'all': Phi(G, False)}
        if 'xy' not in G.ext:
            phi['far'] = Phi(G, True)
        for key in phi:
            minphi[key] = min(minphi[key], phi[key])
        if G.locstd():
            continue
        kids = list(all_steps(G))
        random.shuffle(kids)
        taken = 0
        for kind, lab, H in kids:
            if H.ord() <= ORDMAX:
                hk = H.key()
                if hk not in frontier:
                    frontier[hk] = H; queue.append(hk)
            if taken >= NKIDS or len(H.vertices()) > 8:
                continue
            taken += 1
            far = H.far() and 'far' in phi
            for key in (('far', 'all') if far else ('all',)):
                ph = Phi(H, key == 'far')
                nchecked[key] += 1
                if ph < phi[key]:
                    viol[(key, kind, lab)] += 1
                    print(f'VIOLATION[Phi^{key}] {kind}/{lab}: {phi[key]} -> {ph}\n  parent {G}\n  child {H}', flush=True)
            if H.locstd():
                for key in (('far', 'all') if far else ('all',)):
                    locstd_min[key] = min(locstd_min.get(key, 99), H.ord())
    print(f'DONE phi p={p} ORDMAX={ORDMAX}: states {nstates} (|V| <= 8), children checked {dict(nchecked)}, violations {dict(viol)}, min Phi over states {minphi}, min ord of loc. std. children {locstd_min}; t={time.time()-t0:.0f}s')


def run_init(pmax):
    for p in range(1, pmax + 1):
        G = fxyPow(p)
        t0 = time.time()
        print(f'Gamma_{p}: ord={G.ord()} c={c(G)} Phi^far={Phi(G, True)} (3p={3*p}) Phi^all={Phi(G, False)} (2p={2*p}); t={time.time()-t0:.0f}s', flush=True)


def parse_state(line):
    n = int(line.split('n=')[1].split(' ')[0])
    solid = eval(line.split('solid=')[1].split(' waved=')[0])
    waved = eval(line.split('waved=')[1])
    return Graph(n, [tuple(e) for e in solid], [tuple(w) for w in waved])


def run_cexpath(fn):
    lines = open(fn).read().splitlines()
    states = [parse_state(l) for l in lines if l.startswith('state ')]
    child = [parse_state(l.replace('child:', 'child: ')) for l in lines if l.startswith('child:')][0]
    prev = None
    for i, S in enumerate(states + [child]):
        ph = Phi(S, True); pa = Phi(S, False)
        tag = '' if prev is None else ('  (non-decreasing)' if ph >= prev[0] and pa >= prev[1] else '  DECREASE')
        print(f'{"child" if i == len(states) else f"state {i}"}: |V|={len(S.vertices())} ord={S.ord()} Psi={M.Psi(S)} c={c(S)} Phi^far={ph} Phi^all={pa}{tag}', flush=True)
        prev = (ph, pa)


def run_lemmaA(p, ND, seed, MAXD):
    random.seed(seed); tests = 0; bad = 0
    for di in range(ND):
        G = fxyPow(p); depth = 0
        while depth < MAXD and not G.locstd():
            for i, e in enumerate(G.solid):
                if e[2] == e[3]:
                    H = Graph(G.n, G.solid[:i] + G.solid[i + 1:], G.waved, ext=G.ext)
                    tests += 1
                    if c(H) > c(G):
                        bad += 1
            kids = [H for kind, lab, H in all_steps(G)]
            if not kids:
                break
            G = random.choice(kids); depth += 1
    print(f'lemma A for c: {tests} loop removals on reachable states (p={p}), c increased in {bad}')


def run_placement(p, ND, seed, MAXD, NPART):
    """Placement lemma: T a one-new-vertex term of a reachable Q, pi' a random partition of V(T) with alpha alone, C a class of pi',
    k = number of alpha's non-loop edges whose far end lies in C.  Claim: k <= 1  ==>  c(M_pi T) >= c(M_pi' T) where pi merges alpha into C."""
    random.seed(seed); stats = Counter(); t0 = time.time()
    gens = (M.weight_steps, M.edge_steps, M.gg_steps)
    for di in range(ND):
        G = fxyPow(p); depth = 0
        while depth < MAXD and not G.locstd():
            for gen in gens:
                for lab, (solid, waved, k) in gen(G):
                    if k != 1: continue
                    al = G.n
                    verts = sorted(G.vertices(), key=str)
                    for _ in range(NPART):
                        cl = {v: v for v in verts}
                        for _m in range(random.choice([0, 1, 2, 3])):
                            u, v = random.sample(verts, 2); cu, cv = cl[u], cl[v]
                            if cu == cv or (is_ext(cu) and is_ext(cv)): continue
                            tgt = cu if is_ext(cu) else (cv if is_ext(cv) else cu); src = cv if tgt == cu else cu
                            for w in verts:
                                if cl[w] == src: cl[w] = tgt
                        cl_alone = dict(cl); cl_alone[al] = al
                        T0 = merge_classes(G.n + 1, G.ext, solid, waved, cl_alone); c_alone = c(T0)
                        for C in sorted(set(cl.values()), key=str):
                            cl_pl = dict(cl); cl_pl[al] = C
                            T1 = merge_classes(G.n + 1, G.ext, solid, waved, cl_pl); c_pl = c(T1)
                            kk = sum(1 for e in solid if e[2] != e[3] and al in (e[2], e[3]) and cl[e[2] if e[3] == al else e[3]] == C)
                            stats[('k', kk)] += 1
                            if kk <= 1 and c_pl < c_alone:
                                stats['VIOLATION'] += 1
                                if stats['VIOLATION'] <= 3: print('placement violation', lab, kk, c_alone, c_pl, G, cl, C)
            kids = [H for kind, lab, H in all_steps(G)]
            if not kids: break
            G = random.choice(kids); depth += 1
    print(f'placement lemma: {dict(sorted(stats.items(), key=str))}; t={time.time()-t0:.0f}s')


if __name__ == '__main__':
    a = sys.argv[1:]
    if not a: print(__doc__); sys.exit(0)
    if a[0] == 'premerge': run_premerge(int(a[1]), int(a[2]), int(a[3]), int(a[4]), int(a[5]), a[6] == 'xy')
    elif a[0] == 'phi': run_phi(int(a[1]), int(a[2]), int(a[3]), int(a[4]))
    elif a[0] == 'init': run_init(int(a[1]))
    elif a[0] == 'cexpath': run_cexpath(a[1])
    elif a[0] == 'placement': run_placement(int(a[1]), int(a[2]), int(a[3]), int(a[4]), int(a[5]))
    elif a[0] == 'lemmaA': run_lemmaA(int(a[1]), int(a[2]), int(a[3]), int(a[4]))
    else: print(__doc__)
