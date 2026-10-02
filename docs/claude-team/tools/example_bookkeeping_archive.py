import re,os,subprocess
from collections import Counter
R=os.path.expanduser('~/mnt/RBM3D/')
TS=subprocess.check_output(['date','-u','+%Y-%m-%d %H:%M UTC']).decode().strip()
p=R+'docs/queue/CONTROL.md'; pa=R+'docs/queue/CONTROL-archive.md'
m0=os.stat(p).st_mtime; s=open(p).read()
# released list
old='1. T2272 — `docs/tickets/T2272.md`'
i=s.index(old); j=s.index('\n',i)
s=s[:i]+'(none: T2272, the last ticket, merged ece23e7 at 13:53 UTC; DECISIONS §241)'+s[j:]
s=re.sub(r'^updated: .*$',f'updated: {TS} (dispatcher V2: T2272 merged; CONTROL archived; H313)',s,count=1,flags=re.M)
s=re.sub(r'^reason: .*$',"reason: RUN (Jun, DECISIONS §146). Project closed (DECISIONS §239, §240, §241). No released ticket; no workflow running.",s,count=1,flags=re.M)
L=s.split('\n')
iPre=L.index('## Pre-release checks (the hub compiles; the dispatcher releases — CLAUDE.md §4 step 0)')
iApp=L.index('## Approved instructions')
iLog=L.index('## Merge log (the hub appends one `done:` line per merge)')
head=L[:iPre]; pre=L[iPre:iApp]; app=L[iApp:iLog]; log=L[iLog:]
def merged(t):
    f=R+f'docs/queue/{t}.state'
    return os.path.exists(f) and open(f).read().startswith('state: merged')
arch_pre=[]; keep_pre=[]
for k,l in enumerate(pre):
    if k<2: keep_pre.append(l); continue
    m=re.match(r'^- (T\d+) \(',l)
    if m and merged(m.group(1)): arch_pre.append(l); continue
    if l.startswith('done:') or l.startswith('  docs/tickets/checks/'): arch_pre.append(l); continue
    keep_pre.append(l)
keep_app=[app[0]]; arch_app=[]; blocks=[]; cur=None
for l in app[1:]:
    if re.match(r'^- H\d+ \(',l) or l.startswith('- hub note') or l.startswith('(H1 done'):
        if cur: blocks.append(cur)
        cur=[l]
    else:
        if cur is None: cur=[l]
        else: cur.append(l)
if cur: blocks.append(cur)
STAND={'H299','H298','H147','H110','H109','H108','H93','H26'}
def fully_done(b):
    txt='\n'.join(b); dl=[x for x in b if x.strip().startswith('done:')]
    if not dl: return False
    parts=set(re.findall(r'^  \((\d+)\) ',txt,flags=re.M))
    for k in parts:
        if not any(re.search(r'— \('+k+r'\)\s*(?!pending)',x) for x in dl): return False
    return True
nd=[]
for b in blocks:
    m=re.match(r'^- (H\d+) \(',b[0])
    if m and m.group(1) not in STAND:
        if fully_done(b): arch_app.extend(b)
        else: keep_app.extend(b); nd.append(m.group(1))
    else: keep_app.extend(b)
logdone=[k for k,l in enumerate(log) if l.startswith('- done:')]
cut=set(logdone[:-6])
arch_log=[log[k] for k in sorted(cut)]; keep_log=[l for k,l in enumerate(log) if k not in cut]
newC='\n'.join(head+keep_pre+keep_app+keep_log)
h=f"""- H313 (dispatcher V2, {TS}). **T2272 merged ece23e7 (bookkeeping); CONTROL archived (TEAM §5: it had grown to 43KB).** Completed instructions H300–H312 (except the standing H299, H298, H147, H110, H109, H108, H93, H26), the Pre-release lines of merged tickets with all old `done:` and error lines, and all but the last six merge-log lines were moved verbatim to the end of `docs/queue/CONTROL-archive.md` (append only, section "Archived {TS} by dispatcher V2"). Nothing in force was removed. No released ticket; no workflow running; the dispatcher heartbeat stops after this round.
  (1) Commit, staging by name only, with message `Dispatcher V2: bookkeeping (T2272 merged), archive CONTROL (H300-H312 done items), HANDOVER, worklog`, and `git push origin main` (no force; if rejected, stop and report): `docs/queue/CONTROL.md`, `docs/queue/CONTROL-archive.md`, `docs/claude-team/HANDOVER.md`, `docs/claude-team/WORKLOG.md`. Write one `done:` line.
"""
a=newC.index('- H299 (dispatcher V2,')
newC=newC[:a]+h+newC[a:]
archived='\n'.join(arch_pre+arch_app+arch_log)
c_old=Counter(L); c_new=Counter(newC.split('\n'))+Counter(archived.split('\n'))
missing=[x for x in c_old if c_old[x]>c_new[x]]
assert not missing, missing[:3]
assert os.stat(p).st_mtime==m0
A=open(pa).read().rstrip('\n')+f'\n\n## Archived {TS} by dispatcher V2\n\n'+archived+'\n'
open(pa,'w').write(A); open(p,'w').write(newC)
# HANDOVER
ph=R+'docs/claude-team/HANDOVER.md'; t=open(ph).read()
o='  - 下一编号：H313、DECISIONS §242、paper-delta #142、票 T2273（T2272 = `L32` 文档串改引 v4，§241）。'
assert t.count(o)==1
t=t.replace(o,'  - 下一编号：H314、DECISIONS §242、paper-delta #142、票 T2273。T2272（`L32` 文档串改引 v4，§241）已合并 ece23e7（10-02 13:53 UTC），陈述未变；心跳已再次停止。')
open(ph,'w').write(t)
open(R+'docs/claude-team/WORKLOG.md','a').write(f"- {TS} T2272 合并 ece23e7（`L32` 文档串改引 [32] v4，5+/3-，陈述不变，全量构建、公理审计通过）。审核员注：未对照外部 PDF 核对 v4 的说法；这一步总调度已在 §241 做过（对照 Project 文档 `1609.09011v4.pdf` 与 T2123 (a.3) 的 v3 摘录）。CONTROL 归档（43KB → 见 H313）。发 H313 提交；心跳停止。\n")
print(TS,'kept not-done:',nd,'archived:',len(arch_pre),len(arch_app),len(arch_log),'size',len(newC.encode()))
