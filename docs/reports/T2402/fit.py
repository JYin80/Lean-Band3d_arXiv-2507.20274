"""fit.py (T2402 1a): log-log slopes in W of ||Delta||_max, RMS|R_uu| and RMS|<R>_a| from the output files of ravg.py.  Usage: python3 fit.py ravg_d1.out ..."""
import re, sys, math
import numpy as np
for fn in sys.argv[1:]:
    rows = {}
    for l in open(fn):
        m = re.match(r"g=(\S+)\s+d=(\d+) L=(\d+) W=(\d+)\s+N=(\d+)\s+.*\|\|Delta\|\|_max=(\S+)\s+W\^-d=(\S+)\s+RMS\|R_uu\|/W\^-d = (\S+)\s+RMS\|<R>_a\|/W\^-d = (\S+)", l)
        if not m: continue
        g, d, L, W, N, dm, Wd, r, ra = m.groups(); g = float(g); d = int(d); W = int(W)
        rows.setdefault((g, d), []).append((W, float(dm), float(r) * float(Wd), float(ra) * float(Wd)))
    for (g, d), v in rows.items():
        v = np.array(v); lw = np.log(v[:, 0])
        def slope(col, lo=0): return np.polyfit(lw[lo:], np.log(v[lo:, col]), 1)[0]
        print(f"{fn}: g={g:<8.4g} d={d} W in {int(v[0,0])}..{int(v[-1,0])}:  slope of ||Delta||_max = {slope(1):+.2f} (Psi: -d/2 = {-d/2:+.2f});  RMS|R_uu| = {slope(2):+.2f} (Psi: {-d/2:+.2f});  RMS|<R>_a| = {slope(3):+.2f} (Psi^2: {-d:+.2f});  ||Delta||_max W^(d/2) in [{(v[:,1] * v[:,0] ** (d / 2)).min():.2f}, {(v[:,1] * v[:,0] ** (d / 2)).max():.2f}];  last-3-points slopes: {slope(1, -3):+.2f} {slope(2, -3):+.2f} {slope(3, -3):+.2f}")
