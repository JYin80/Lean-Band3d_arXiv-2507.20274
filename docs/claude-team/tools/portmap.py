# Usage (run from $HOME/mnt, i.e. the parent of RBM2D/ and RBM3D/): python3 RBM3D/docs/claude-team/tools/portmap.py RBM2D/RBM2D/<path>.lean
# Lists every RBM2D name used by the source file: OK (RBM3D public twin: full name, file:line) or MISS (no public RBM3D declaration of that last name; [RBM3D private] if only a private one). Matches by last name only: field projections (s1, push, zero, trans, ...) are noise.
import re, os, sys, subprocess
src = sys.argv[1]; r2 = 'RBM2D/RBM2D'; r3 = 'RBM3D/RBM3D'
txt = open(src, encoding='utf-8').read()
# strip comments
t = re.sub(r'/-.*?-/', ' ', txt, flags=re.S); t = re.sub(r'--[^\n]*', ' ', t)
ids = set(re.findall(r"[A-Za-z_][A-Za-z0-9_'.]*", t))
decl = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+)?(?:noncomputable\s+)?(?:theorem|lemma|def|abbrev|structure|instance|class|inductive)\s+([^\s:({\[]+)", re.M)
def decls(root):
    out = {}
    for dp,_,fs in os.walk(root):
        if '/Probe' in dp: continue
        for f in fs:
            if not f.endswith('.lean'): continue
            p = os.path.join(dp,f); s = open(p,encoding='utf-8').read()
            ns=[]; 
            for i,line in enumerate(s.split('\n'),1):
                m=re.match(r'^namespace\s+(\S+)',line)
                if m: ns.append(m.group(1)); continue
                m=re.match(r'^end\s+(\S+)',line)
                if m and ns and ns[-1]==m.group(1): ns.pop(); continue
                m=decl.match(line)
                if m:
                    nm=m.group(1); priv='private' in line.split(nm)[0]
                    full='.'.join(ns+[nm])
                    out.setdefault(nm.split('.')[-1],[]).append((full,p,i,priv))
    return out
own = set(m.group(1).split('.')[-1] for m in decl.finditer(txt))
D2 = decls(r2); D3 = decls(r3)
rows=[]
for x in sorted(ids):
    last = x.split('.')[-1]
    if last in own or last not in D2: continue
    if all(src.endswith(p.split('RBM2D/RBM2D/')[-1]) for _,p,_,_ in D2[last]): continue
    f2 = D2[last][0]
    if f2[1].endswith('/Mathlib') : continue
    h3 = [d for d in D3.get(last,[]) if not d[3]]
    if h3:
        rows.append(f"OK   {last:40s} {h3[0][0]}  {h3[0][1].replace('RBM3D/RBM3D/','')}:{h3[0][2]}")
    else:
        pv = D3.get(last,[])
        rows.append(f"MISS {last:40s} (RBM2D {f2[0]} {f2[1].replace('RBM2D/RBM2D/','')}:{f2[2]}){' [RBM3D private]' if pv else ''}")
print('\n'.join(rows)); print(len(rows),'names;', sum(r.startswith('MISS') for r in rows),'missing')
