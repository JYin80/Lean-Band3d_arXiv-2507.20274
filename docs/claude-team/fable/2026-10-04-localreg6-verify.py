"""2026-10-04-localreg6-verify.py  (Fable, LW-10c preflight)
Checks of the candidate potentials on the Python model of `LocStep` (2026-10-04-localreg6-model.py, same directory).
  python3 2026-10-04-localreg6-verify.py exh p ORDMAX [state.pkl tlimit]   every far child of every far state with
                                                   ord <= ORDMAX (resumable in slices of tlimit seconds)
  python3 2026-10-04-localreg6-verify.py desc p ndesc seed PR maxdepth mode [tlimit]   random descents (low|strat|rand)
  python3 2026-10-04-localreg6-verify.py danger p ndesc seed maxdepth [tlimit]  adversarial search for parallel SC chains
  python3 2026-10-04-localreg6-verify.py cexpath p seed maxdepth out.txt      record a reachable path on which Psi decreases
  python3 2026-10-04-localreg6-verify.py checkpath file.txt                   re-verify a recorded path step by step
  python3 2026-10-04-localreg6-verify.py premerge p ndesc seed maxdepth npart far|xy [tlimit]   local lemma of Psi_true
All checks are on far outputs only (M_x != M_y), as (6) is stated under (eq:far_ab).
"""
import sys, os, time, random, importlib.util
from collections import Counter, deque

here = os.path.dirname(os.path.abspath(__file__))
spec = importlib.util.spec_from_file_location('lr6model', os.path.join(here, '2026-10-04-localreg6-model.py'))
M = importlib.util.module_from_spec(spec); spec.loader.exec_module(M)
Graph, fxyPow, all_steps, is_ext = M.Graph, M.fxyPow, M.all_steps, M.is_ext
POTS = {'Psi': M.Psi, 'PsiLoc': M.PsiLoc, 'Psi3': M.Psi3}


def info(G):
    return f'ord={G.ord()} Psi={M.Psi(G)} PsiLoc={M.PsiLoc(G)} Psi3={M.Psi3(G)} | {M.describe3(G)}'


def check_children(G, viol, mindelta, locstd, nout, shown, tag=''):
    PG = {k: f(G) for k, f in POTS.items()}
    kids = []
    for kind, lab, H in all_steps(G):
        if not H.far():
            nout['notfar'] += 1
            continue
        nout[(kind, lab)] += 1
        for k, f in POTS.items():
            dl = f(H) - PG[k]
            key = (k, kind, lab)
            if key not in mindelta or dl < mindelta[key]:
                mindelta[key] = dl
            if dl < 0:
                viol[(k, kind, lab)] += 1
                if shown[k] < 2:
                    shown[k] += 1
                    print(f'VIOLATION[{k}] {kind}/{lab} d={dl}{tag}\n  parent {G}\n    {info(G)}\n  child  {H}\n    {info(H)}', flush=True)
        if H.locstd():
            locstd[H.ord()] += 1
        kids.append((kind, lab, H))
    return kids


def summary(p, viol, mindelta, locstd, nout, t0, what):
    far = sum(v for k, v in nout.items() if k != 'notfar')
    print(f'DONE {what} p={p}: far outputs {far} (by term {dict(sorted((str(k), v) for k, v in nout.items() if k != "notfar"))}); M_x = M_y outputs skipped {nout["notfar"]}; t={time.time()-t0:.0f}s')
    for k in POTS:
        print(f'  {k}: violating outputs {sum(v for (kk, _, _), v in viol.items() if kk == k)} by term {dict(sorted(((kind, lab), v) for (kk, kind, lab), v in viol.items() if kk == k))}; min delta by term {dict(sorted(((kind, lab), d) for (kk, kind, lab), d in mindelta.items() if kk == k))}')
    print(f'  LocStd far children by ord: {sorted(locstd.items())}')


def run_exh(p, ORDMAX, state=None, tlimit=None):
    """resumable: with `state` (a pickle path) the search state is loaded/saved and the run stops after `tlimit` seconds."""
    import pickle
    t0 = time.time()
    if state and os.path.exists(state):
        fr_raw, queue, viol, mindelta, locstd, nout, expanded, minpot, t_prev = pickle.load(open(state, 'rb'))
        frontier = {k: Graph(n, solid, waved, ext=ext) for k, (n, ext, solid, waved) in fr_raw.items()}
        queue = deque(queue)
        print(f'resumed: expanded {expanded}, queue {len(queue)}, elapsed so far {t_prev:.0f}s')
    else:
        G0 = fxyPow(p); frontier = {G0.key(): G0}; queue = deque([G0.key()])
        viol = Counter(); mindelta = {}; locstd = Counter(); nout = Counter(); expanded = 0; t_prev = 0.0
        minpot = {k: 10**9 for k in POTS}
    shown = Counter()
    while queue:
        if tlimit is not None and time.time() - t0 > tlimit:
            fr_raw = {k: (G.n, G.ext, G.solid, G.waved) for k, G in frontier.items()}
            pickle.dump((fr_raw, list(queue), viol, mindelta, locstd, nout, expanded, minpot, t_prev + time.time() - t0), open(state, 'wb'))
            print(f'paused: expanded {expanded}, frontier {len(frontier)}, queue {len(queue)}, far outputs so far {sum(v for k, v in nout.items() if k != "notfar")}, violations so far {dict(viol)}; state saved to {state}')
            return
        k = queue.popleft(); G = frontier[k]
        for kk, f in POTS.items():
            minpot[kk] = min(minpot[kk], f(G))
        if G.locstd():
            continue
        expanded += 1
        for kind, lab, H in check_children(G, viol, mindelta, locstd, nout, shown):
            if H.ord() <= ORDMAX:
                hk = H.key()
                if hk not in frontier:
                    frontier[hk] = H; queue.append(hk)
    t0 -= t_prev
    print(f'exhaustive: far states with ord <= {ORDMAX}: {len(frontier)} (by ord {sorted(Counter(G.ord() for G in frontier.values()).items())}), expanded {expanded}; min of the potentials over these states {minpot} (3p = {3*p}, 2p+2 = {2*p+2})')
    summary(p, viol, mindelta, locstd, nout, t0, f'exhaustive ord<={ORDMAX}')
    if state and os.path.exists(state):
        os.remove(state)


def run_desc(p, ND, seed, PR, MAXD, mode, tlimit=None):
    random.seed(seed)
    viol = Counter(); mindelta = {}; locstd = Counter(); nout = Counter(); shown = Counter(); t0 = time.time()
    for di in range(ND):
        if tlimit is not None and time.time() - t0 > tlimit:
            ND = di; break
        G = fxyPow(p); depth = 0
        while depth < MAXD and not G.locstd():
            kids = check_children(G, viol, mindelta, locstd, nout, shown)
            if not kids: break
            if mode == 'strat':
                for kd in ('weight', 'edge', 'gg'):
                    c2 = [k for k in kids if k[0] == kd]
                    if c2: kids = c2; break
            if mode != 'rand' and random.random() < PR:
                mo = min(k[2].ord() for k in kids)
                kids = [k for k in kids if k[2].ord() <= mo + (0 if random.random() < 0.6 else 1)]
            G = random.choice(kids)[2]; depth += 1
    summary(p, viol, mindelta, locstd, nout, t0, f'descents n={ND} seed={seed} PR={PR} depth<={MAXD} mode={mode}')


def pair_conn(G):
    sc, lw, chains = M.analyse3(G)
    ch = Counter(); ed = Counter()
    for kind, k, e, f in chains:
        if kind == 'open' and k == 1: ch[frozenset((e, f))] += 1
    for (sig, _, s, d) in G.solid:
        if s != d and s not in sc and d not in sc: ed[frozenset((s, d))] += 1
    return ch, ed


def danger(G):
    ch, ed = pair_conn(G)
    return max([ch[pr] for pr, e in ed.items() if e == 1 and not all(is_ext(v) for v in pr)] + [0])


def run_danger(p, ND, seed, MAXD, tlimit=None):
    random.seed(seed)
    viol = Counter(); mindelta = {}; locstd = Counter(); nout = Counter(); shown = Counter(); t0 = time.time(); maxd = 0
    for di in range(ND):
        if tlimit is not None and time.time() - t0 > tlimit:
            ND = di; break
        G = fxyPow(p); depth = 0
        while depth < MAXD and not G.locstd():
            kids = check_children(G, viol, mindelta, locstd, nout, shown, tag=' (adversarial)')
            if not kids: break
            dg = [(danger(H), random.random(), H) for _, _, H in kids]
            m = max(d for d, _, _ in dg); maxd = max(maxd, m)
            top = [H for d, r, H in dg if d >= m - (0 if random.random() < 0.7 else 1)]
            G = random.choice(top); depth += 1
    print(f'adversarial objective (single-SC chains parallel to one direct edge between a mergeable pair): max reached {maxd}')
    summary(p, viol, mindelta, locstd, nout, t0, f'adversarial descents n={ND} seed={seed} depth<={MAXD}')


def run_cexpath(p, seed, MAXD, out):
    random.seed(seed); t0 = time.time()
    for attempt in range(300):
        G = fxyPow(p); path = [G]; labels = []; found = None
        while len(labels) < MAXD and not G.locstd():
            PG = M.Psi(G); kids = []
            for kind, lab, H in all_steps(G):
                if not H.far(): continue
                if M.Psi(H) < PG and found is None: found = (kind, lab, H)
                kids.append((kind, lab, H))
            if found or not kids: break
            dg = [(danger(H), random.random(), kind, lab, H) for kind, lab, H in kids]
            m = max(d for d, *_ in dg)
            top = [t for t in dg if t[0] >= m - (0 if random.random() < 0.7 else 1)]
            d, r, kind, lab, H = random.choice(top); labels.append(f'{kind}/{lab}'); G = H; path.append(G)
        if found:
            kind, lab, H = found
            with open(out, 'w') as f:
                f.write(f'# reachable far path from fxyPow({p}); each state is a LocStep output of the previous one (M_x != M_y throughout)\n')
                f.write('# x, y external; internal vertices 0..n-1; solid edge = (blue?, circled?, src, dst); waved edge = (u, v)\n')
                for i, S in enumerate(path):
                    f.write(f'state {i}' + (f' (via {labels[i-1]})' if i > 0 else '') + f': n={S.n} solid={list(S.solid)} waved={list(S.waved)}\n   {info(S)}\n')
                f.write(f'violating step: {kind}/{lab}\nchild: n={H.n} solid={list(H.solid)} waved={list(H.waved)}\n   {info(H)}\n')
                f.write(f'Psi {M.Psi(G)}->{M.Psi(H)}  PsiLoc {M.PsiLoc(G)}->{M.PsiLoc(H)}  Psi3 {M.Psi3(G)}->{M.Psi3(H)}  ord {G.ord()}->{H.ord()}\n')
            print(f'cexpath: found at attempt {attempt}, depth {len(labels)}, labels {labels}, Psi {M.Psi(G)}->{M.Psi(H)}, written to {out}, t={time.time()-t0:.0f}s')
            return
    print('cexpath: no decrease of Psi found')


def merge_classes(n, ext, solid, waved, classes):
    """M_pi: merge the classes (dict vertex -> class id, external ids are 'x'/'y'), keep circled loops, drop every other
    solid edge inside a class (the worst case by Lemma A)."""
    ids = sorted({c for c in classes.values() if not is_ext(c)})
    ren = {c: i for i, c in enumerate(ids)}
    nm = lambda v: classes[v] if is_ext(classes[v]) else ren[classes[v]]
    sol = [(sig, circ, nm(s_), nm(d)) for (sig, circ, s_, d) in solid if (s_ == d and circ) or nm(s_) != nm(d)]
    wav = [(nm(u), nm(v)) for (u, v) in waved]
    return Graph(len(ids), sol, wav, ext=tuple(sorted({nm(v) for v in ext})))


def run_premerge(p, ND, seed, MAXD, NPART, allow_xy, tlimit=None):
    """Local lemma behind Psi_true = min_pi [ord + rescost](M_pi Q): for a far state Q, a random partition pi0 of V(Q)
    (x, y kept apart unless allow_xy), a term T of Q and a placement of the new vertices (alone, or into a class):
    naive claim  cost(M_pi T) >= cost(M_pi0 Q);  when it fails, existential repair: some pi0' = pi0 + one more merge
    with cost(M_pi0' Q) <= cost(M_pi T).  'realizable' = every new vertex is put into a class containing one of its
    neighbours along a new edge (the only merges the dotted-edge partition can produce)."""
    random.seed(seed)
    cost = lambda G: G.ord() + M.D(G)
    stats = Counter(); t0 = time.time(); shown = 0; done = 0
    gens = (M.weight_steps, M.edge_steps, M.gg_steps)
    for di in range(ND):
        if tlimit is not None and time.time() - t0 > tlimit: break
        done += 1
        G = fxyPow(p); depth = 0
        while depth < MAXD and not G.locstd():
            verts = sorted(G.vertices(), key=str)
            for _ in range(NPART):
                cl0 = {v: v for v in verts}
                for _m in range(random.choice([0, 1, 1, 2, 3])):
                    u, v = random.sample(verts, 2); cu, cv = cl0[u], cl0[v]
                    if cu == cv or (not allow_xy and {cu, cv} == {'x', 'y'}): continue
                    tgt = cu if is_ext(cu) else (cv if is_ext(cv) else cu); src = cv if tgt == cu else cu
                    for w in verts:
                        if cl0[w] == src: cl0[w] = tgt
                G0 = merge_classes(G.n, G.ext, G.solid, G.waved, cl0); c0 = cost(G0)
                for gen in gens:
                    for lab, (solid, waved, k) in gen(G):
                        news = list(range(G.n, G.n + k))
                        nbrs = {nv: {e[2] if e[3] == nv else e[3] for e in solid if nv in (e[2], e[3]) and e[2] != e[3]} for nv in news}
                        for opt in [None] + random.sample(verts, min(3, len(verts))):
                            cl = dict(cl0)
                            for nv in news: cl[nv] = cl0[opt] if opt is not None else nv
                            T = merge_classes(G.n + k, G.ext, solid, waved, cl)
                            if not allow_xy and not T.far(): continue
                            c1 = cost(T)
                            real = opt is None or all(any(cl0.get(u) == cl0[opt] for u in nbrs[nv]) for nv in news)
                            key = 'realizable' if real else 'unrealizable'
                            stats[(key, 'tests')] += 1
                            if c1 < c0:
                                stats[(key, 'naive_fail')] += 1
                                ok = False
                                for u in verts:
                                    for v in verts:
                                        if str(u) >= str(v) or ok: continue
                                        cu, cv = cl0[u], cl0[v]
                                        if cu == cv or (not allow_xy and {cu, cv} == {'x', 'y'}): continue
                                        cl2 = dict(cl0); tgt = cu if is_ext(cu) else (cv if is_ext(cv) else cu); src = cv if tgt == cu else cu
                                        for w in verts:
                                            if cl2[w] == src: cl2[w] = tgt
                                        if cost(merge_classes(G.n, G.ext, G.solid, G.waved, cl2)) <= c1: ok = True
                                stats[(key, 'repaired' if ok else 'UNREPAIRED')] += 1
                                if not ok and shown < 3:
                                    shown += 1
                                    print(f'UNREPAIRED {lab} opt={opt} cost {c0} -> {c1}\n  Q {G}\n  G0 {M.describe3(G0)}\n  T {T}\n    {M.describe3(T)}', flush=True)
            kids = [H for kind, lab, H in all_steps(G) if allow_xy or H.far()]
            if not kids: break
            kids.sort(key=lambda H: H.ord()); G = random.choice(kids[:max(1, len(kids) // 4)]); depth += 1
    print(f'DONE premerge p={p} seed={seed} allow_xy={allow_xy} descents={done}: {dict(sorted(stats.items()))}; t={time.time()-t0:.0f}s')


def parse_state(line):
    n = int(line.split('n=')[1].split(' ')[0])
    solid = eval(line.split('solid=')[1].split(' waved=')[0])
    waved = eval(line.split('waved=')[1])
    return Graph(n, [tuple(e) for e in solid], [tuple(w) for w in waved])


def run_checkpath(fn):
    lines = open(fn).read().splitlines()
    states = [parse_state(l) for l in lines if l.startswith('state ')]
    child = [parse_state(l.replace('child:', 'child: ')) for l in lines if l.startswith('child:')][0]
    ok = True
    for i in range(1, len(states)):
        keys = {H.key() for kind, lab, H in all_steps(states[i - 1]) if H.far()}
        hit = states[i].key() in keys
        ok &= hit
        print(f'state {i}: is a far LocStep output of state {i-1}: {hit}; {info(states[i])}')
    G = states[-1]
    keys = {H.key() for kind, lab, H in all_steps(G) if H.far()}
    hit = child.key() in keys
    print(f'child: is a far LocStep output of the last state: {hit}; parent {info(G)}; child {info(child)}')
    print(f'checkpath: all steps verified: {ok and hit}; Psi {M.Psi(G)} -> {M.Psi(child)} (decrease {M.Psi(G) - M.Psi(child)}), PsiLoc {M.PsiLoc(G)} -> {M.PsiLoc(child)}, Psi3 {M.Psi3(G)} -> {M.Psi3(child)}, ord {G.ord()} -> {child.ord()}')


if __name__ == '__main__':
    a = sys.argv[1:]
    if not a: print(__doc__); sys.exit(0)
    if a[0] == 'exh': run_exh(int(a[1]), int(a[2]), a[3] if len(a) > 3 else None, float(a[4]) if len(a) > 4 else None)
    elif a[0] == 'desc': run_desc(int(a[1]), int(a[2]), int(a[3]), float(a[4]), int(a[5]), a[6], float(a[7]) if len(a) > 7 else None)
    elif a[0] == 'danger': run_danger(int(a[1]), int(a[2]), int(a[3]), int(a[4]), float(a[5]) if len(a) > 5 else None)
    elif a[0] == 'cexpath': run_cexpath(int(a[1]), int(a[2]), int(a[3]), a[4])
    elif a[0] == 'checkpath': run_checkpath(a[1])
    elif a[0] == 'premerge': run_premerge(int(a[1]), int(a[2]), int(a[3]), int(a[4]), int(a[5]), a[6] == 'xy', float(a[7]) if len(a) > 7 else None)
    else: print(__doc__)
