import re,os,subprocess
R=os.path.expanduser('~/mnt/RBM3D/')
TS=subprocess.check_output(['date','-u','+%Y-%m-%d %H:%M UTC']).decode().strip()
TSL=subprocess.check_output(['date','-u','+%a %b %e %H:%M UTC %Y']).decode().strip()
open(R+'docs/tickets/T2274.md','w').write(f'''Ticket: T2274 (dispatcher V2, {TS}; DECISIONS §244, §245)
Group / type: **Publication clean-up, step 2 — delete every unreachable declaration, every whole-dead module, and all check clutter. Deletions only (plus the import fixes they force). No statement changes.**
**Start condition: after T2273 has merged** (its tool `docs/claude-team/tools/DeadDecls.lean` and report `docs/reports/T2273-dead.md` are the input).
Role: `prover-hard`. Rework rate (last 10): 1/10 (T2273).
Process: CLAUDE.md §4. Stage 1a `preflight` is **short** (no mathematics): "(i) no exponents; (ii) not applicable", verdict PASS after confirming that T2273 is merged. Then stage 1b `prover-hard`, stage 2 `auditor`.
One ticket on purpose (DECISIONS §245): dead declarations in one directory are used by dead declarations in others, so per-directory deletions would not build separately.

**What to delete.**
1. **The 82 whole-dead modules** of `docs/reports/T2273-dead.md` (c): delete the files, remove their `import` lines from `RBM2D.lean` and from every importing module. Where a live module loses something it needed through that import (typically a Mathlib import), add the direct import it needs.
2. **Every unreached declaration** listed in (b) of the report, with its doc comment, attributes and any `@[…]`/`set_option … in` prefix that belongs only to it. Do this by a script over the report's line ranges (paste the script in the report), bottom-up within each file so that line numbers stay valid; then fix what the build shows.
3. **Check clutter, library-wide:** every `#print`, `#check`, `#eval`, `#guard_msgs` command, and every `example`, **except** in `RBM2D/Endpoints.lean`, `RBM2D/Main/Endpoints.lean`, `RBM2D/Main/BUnivHolds.lean`. Keep `#assert_rbm_axioms` as the last line of `RBM2D.lean`. In `RBM2D/Main/Endpoints.lean` and `RBM2D/Main/BUnivHolds.lean`, keep only the five endpoint theorems, `stoAll_holds`, `locSC_holds_instance` and the one `example` of `BUnivHolds.lean` (the compiled nonempty instance of `bUniv_holds`); delete their `#print axioms` lines and the namespace `BUnivHoldsCheck` except that `example` (move it out of the namespace if needed, statement and proof unchanged).
4. Afterwards remove namespaces/sections left empty and `variable` lines left unused by the deletions. Do **not** reword comments (that is the next ticket), do not rename anything, do not reformat.

**Must not change.**
- `RBM2D/Endpoints.lean`: byte-identical except deletions of unreached declarations that (b) lists for it (if any) — paste `git diff main...t/T2274 -- RBM2D/Endpoints.lean`.
- The statements of the five endpoint theorems, `L32`, `admissible_witnessSizes`, `locSC_holds_instance`, `mSC_eq_msc`: `docs/tickets/checks/T2274-check.lean` must compile on the branch unchanged.
- No new declaration, no edited proof except where a deletion forces it (an `example`-only helper, an import); list every non-deletion line change in the report as `file:line  old → new`.

**Acceptance (CLAUDE.md §4, §6).**
- Full `lake build` OK (it runs `#assert_rbm_axioms`); `#print axioms` of the five endpoint theorems run once in a scratch file (not committed): only `propext`, `Classical.choice`, `Quot.sound`.
- Rerun `lake env lean docs/claude-team/tools/DeadDecls.lean` on the branch: **0 unreached non-meta declarations** and 0 whole-dead modules (the notation `≺` in `Defs/Domination.lean` may stay in the meta list); the number of reached constants equals the T2273 figure (15018) or the report explains the difference.
- `git diff --shortstat main...t/T2274` pasted; insertions ≤ 200 lines (imports and forced fixes only).
- `docs/tickets/checks/T2274-check.lean` compiles against the branch.
- Prove report ≤ 120 lines apart from the deletion script and the tool's summary; line 1 `Prover model: <id>`.

Sole writable files: every file under `RBM2D/` (deletions and the forced fixes above) and `RBM2D.lean`. Branch t/T2274.
Required reading (only these): `CLAUDE.md` §3–§6; this ticket; `docs/tickets/checks/T2274-check.lean`; `docs/DECISIONS.md` §244–§245; `docs/reports/T2273-dead.md`; `docs/claude-team/tools/DeadDecls.lean`.
Merge (rule (A)): the branch deletes files; bring the deletions in with `git rm`, then the full `lake build` of step 5.
''')
open(R+'docs/tickets/checks/T2274-check.lean','w').write(f'''/-
Release check for T2274 (dispatcher V2, {TSL}; CLAUDE.md §4 step 0, DECISIONS §245).
Statements and `#check` only: no proofs, no `sorry`.  Never imported or merged.
The endpoint statements below must elaborate unchanged before and after the deletions.
Run from the main worktree: `lake env lean docs/tickets/checks/T2274-check.lean`.
-/
import RBM2D

#check (RBM.Endpoints.locSC_holds : RBM.Endpoints.locSC)
#check (RBM.Endpoints.QDiff_holds : RBM.Endpoints.QDiff)
#check (RBM.Endpoints.decol_holds : RBM.Endpoints.decol)
#check (RBM.Endpoints.QUE_holds : RBM.Endpoints.QUE)
#check (RBM.Endpoints.bUniv_holds : RBM.Univ.L32 → RBM.Endpoints.BUniv)
#check (RBM.Endpoints.admissible_witnessSizes : RBM.Endpoints.Admissible (1 / 3) RBM.Endpoints.witnessSizes)
#check @RBM.Endpoints.locSC_holds_instance
#check @RBM.Endpoints.mSC_eq_msc
#check @RBM.Univ.L32
#print RBM.Endpoints.locSC
#print RBM.Endpoints.QDiff
#print RBM.Endpoints.decol
#print RBM.Endpoints.QUE
#print RBM.Endpoints.BUniv
''')
p=R+'docs/DECISIONS.md'; s=open(p).read()
tail='（安装于 2026-09-28 08:18 UTC，由 RBM1D 的总调度写入。）'
new=f'''## §245 发布清理第 2 步：一张票删全部死代码（T2274）；论文编译与勘误安排（总调度 V2，{TS}）

- **T2273 的结果**（c763046，审核中）：13531 个声明单元里 3754 个从五条终点不可达，约 4.2 万行；82 个模块整体不可达。核对预期写错一处（`p7Out_holds`/`p7ExpOut_holds` 其实被 `bUniv_of_g1Row` 用到），T2273-amend-1 已改；算返工。
- **为什么只开一张删除票**：不可达声明之间会跨目录互相引用，按目录分开删的话，单张票各自构建不了。所以 T2274 用脚本按报告的行区间一次删完，再修构建。§3「不为凑单拆」优先于并行 4。
- **顺带删掉**：库里的 `#print`/`#check`/`#eval` 约 3775 条、`example` 约 761 个，都是逐票留下的检查痕迹。只保留三个终点文件里的定理与非退化实例。
- **验收**：用 T2273 的工具复跑，结果须为 0 个不可达。
- **注释清理**：T2274 合并之后开（按目录并行，只动注释）。
- **论文**：编译用的 `main.bib` 与 imsart 模板在 `paper/aop-submission/`（Jun 放入）。设备虚拟机缺 `stmaryrd`，所以论文在总调度的云端编译：用现有 `paper/tex/` 编出 68 页，只有字体警告。
  - 勘误分类与改写由 Fable 子代理起草（只读、不写 Lean），总调度复核后给 Jun 看改动；Jun 认可后才进发布版。

'''
assert s.count(tail)==1 and '## §245 ' not in s
s=s.replace(tail,new+tail); open(p,'w').write(s)
p=R+'docs/queue/CONTROL.md'; m0=os.stat(p).st_mtime; s=open(p).read()
s=re.sub(r'^updated: .*$',f'updated: {TS} (dispatcher V2: T2274 written (dead-code deletion, starts after T2273 merges); H317)',s,count=1,flags=re.M)
a=s.index('Pass every listed file (ticket + amends) to every stage.')
s=s[:a]+"2. T2274 — `docs/tickets/T2274.md` (publication clean-up step 2: delete all dead code per `docs/reports/T2273-dead.md`; role `prover-hard`; DECISIONS §245). Start: **only after T2273 has merged** and the compile of H317 (1) is clean; then from stage 1a (short preflight).\n"+s[a:]
o2='## Pre-release checks (the hub compiles; the dispatcher releases — CLAUDE.md §4 step 0)\n'
i=s.index(o2)+len(o2); j=s.index('\n',i)+1
s=s[:j]+"- T2274 (publication clean-up step 2, DECISIONS §245): `docs/tickets/checks/T2274-check.lean` — released if the compile is clean (H317); starts after T2273 merges\n"+s[j:]
h=f"""- H317 (dispatcher V2, {TS}). **T2274: delete all dead code (one ticket on purpose, DECISIONS §245). It starts only after T2273 has merged.**
  (1) Compile `docs/tickets/checks/T2274-check.lean` per H110 (1) and write its `done:` line. If clean, T2274 is released (Released item 2) and starts as soon as T2273 has merged.
  (2) Commit, staging by name only, with message `Dispatcher V2: DECISIONS 245, T2273 amend, T2274 and its check file`, and `git push origin main` (no force; if rejected, stop and report): `docs/DECISIONS.md`, `docs/claude-team/WORKLOG.md`, `docs/queue/CONTROL.md`, `docs/tickets/T2273-amend-1.md`, `docs/tickets/T2274.md`, `docs/tickets/checks/T2274-check.lean`.
  Write one `done:` line per part.
"""
a=s.index('- H316 (dispatcher V2,')
s=s[:a]+h+s[a:]
assert os.stat(p).st_mtime==m0
open(p,'w').write(s)
open(R+'docs/claude-team/WORKLOG.md','a').write(f"- {TS} 写 T2274（一张票删全部死代码与检查痕迹，T2273 合并后开工；§245）。发 H317。论文找到编译文件（paper/aop-submission/），云端编译通过（68 页）。\n")
print(TS)
