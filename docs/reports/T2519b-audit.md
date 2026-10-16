Auditor model: claude-opus-5-5
# T2519 row b audit (round 1) — `t/T2519b` at 8f4c89c3, row diff `19df37e2...t/T2519b`
Written Fri Oct 16 14:39 UTC 2026 (`date -u`). Worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2519b-audit1` (detached at 8f4c89c3). Inputs: ticket T2519 + Amends 1–3, prove report `docs/reports/T2519b-prove.md`.
Row b targets (ticket "Row b" 6, 8; Amend 2 item 1): `Duhamel_drift_remainder_aeBA`, `Duhamel_step_decompBA`, the Azuma lines (`Duhamel_azuma_ZBA`, `Duhamel_azuma_YBA`), endpoint **`gueGrid_loop_duhamelBA`**; target 8 = their instances. None has a `T2519_*` pin (acceptance pins only targets 1, 7, 15, 16), so each is checked against its band twin under the ticket's BA dictionary (C1/X1-C4).

## 1. Statement (band twin → BA, script diff)
`sdiff.py` (scratch): extracts `theorem <name> … :=` from the band file and the BA file, applies the dictionary `gueH sz → gueHBA sz g`, `zt e → ztOf m E`, `etaT (E n) → etaOf (m n)`, `genMatGUE → genMatGUEOf … m`, `gueScale sz E n u → N · etaOf (m n) u`, `gueLmax → loopMax (gueHBA …)`, `envConst … e k v → 16 (k+3)^4 N^4 (1+η_v⁻¹)^(k+4)` (its definition, `Path/OneStep.lean:78`), `Pgue/gueUnit/Duhamel* sz → … (sz.withLam 0)`, process names `Duhamel* → GUEDuhamelBA_*`; the BA loop length `ℓ` is renamed back to the band's `m`. Token diff (all non-equal opcodes):
```
$ python3 -I sdiff.py
== gueGrid_loop_duhamel -> gueGrid_loop_duhamelBA: 616 vs 628 tokens
  delete  band[κ] -> BA[]
  delete  band[( h κ : 0 < κ )] -> BA[]
  insert  band[] -> BA[g]
  insert  band[] -> BA[} { m : ℕ → ℂ]
  replace band[hE] -> BA[hm]
  replace band[| E] -> BA[0 < ( m]
  replace band[|] -> BA[) . im ) ( hm1 : ∀ n , ‖ m n ‖]
  replace band[2 - κ] -> BA[1]
== Duhamel_drift_remainder_ae -> Duhamel_drift_remainder_aeBA: 366 vs 379 tokens
  insert  band[] -> BA[g]
  replace band[e] -> BA[E]
  replace band[he] -> BA[m]
  replace band[| e |] -> BA[ℂ ) ( hm : 0]
  replace band[2] -> BA[m.im ) ( hm1 : ‖ m ‖ ≤ 1]
== Duhamel_step_decomp -> Duhamel_step_decompBA: 361 vs 352 tokens
  replace band[{ d : ℕ } {] -> BA[(]
  replace band[} {] -> BA[) ( g]
  replace band[} {] -> BA[) (]
  replace band[} {] -> BA[) (]
  replace band[} { e] -> BA[) ( E]
  replace band[}] -> BA[) ( m : ℂ )]
  replace band[he] -> BA[hm]
  replace band[| e |] -> BA[0]
  replace band[2] -> BA[m.im]
  delete  band[) ( ht1 : 0 ≤ t1 n] -> BA[]
== Duhamel_azuma_Z -> Duhamel_azuma_ZBA: 157 vs 158 tokens
  replace band[{ d : ℕ } {] -> BA[(]
  replace band[} {] -> BA[) ( g]
  replace band[} {] -> BA[) (]
  replace band[} {] -> BA[) (]
  replace band[} { e] -> BA[) ( E]
  replace band[}] -> BA[) ( m : ℂ )]
== Duhamel_azuma_Y -> Duhamel_azuma_YBA: 235 vs 236 tokens
  replace band[{ d : ℕ } {] -> BA[(]
  replace band[} {] -> BA[) ( g]
  replace band[} {] -> BA[) (]
  replace band[} {] -> BA[) (]
  replace band[} { e] -> BA[) ( E]
  replace band[}] -> BA[) ( m : ℂ )]
```
Reading: the only differences are (i) the band energy window `|E n| ≤ 2 − κ` (resp. `|e| < 2`), under which `m = mE E` has `Im m > 0`, `‖m‖ = 1`, is replaced by a free profile `m` with `0 < Im m`, `‖m‖ ≤ 1` (the BA flow datum; `BAReal` gives both, `BAm_norm_le_one`), and `κ` disappears with it; (ii) the BA shift `g` (no hypothesis: `g Ψ_I` is deterministic Hermitian); (iii) `Duhamel_step_decompBA` drops `0 ≤ t1 n` (weaker premise); (iv) implicit → explicit binders. Quantifier order (fixed `sz, τU, n0`, families, then `∀ᶠ` inside `StochDomAt`), the loss `√(u−t₁)·sup_j √(N⁻¹η_j⁻²L^{(2ℓ)}_j) + (Nη_u)^{−ℓ}`, the range `1 ≤ ℓ ≤ 2 n₀`, grid `gueGridK sz n0`, the `Δ^{3/2}` envelope and the Azuma tails are unchanged. No special case: every statement is at general `d, sz, g, E, m, t1, t0` (`K` general except the endpoint's `gueGridK sz n0`, as in the band). The inline `loopMax (gueHBA …)` of the endpoint is literally the body of row a's `gueLmaxBA` (`main:RBM3D/BA/GUEProcBA.lean:127-129`), so row c reads it by unfolding.

## 2. Vacuity, hidden hypotheses, cycles
```
$ grep -nE "^\s*(structure|class)\b" RBM3D/BA/GUEDuhamelBA*.lean | wc -l        -> 0
$ grep -nE "\bsorry\b|\badmit\b|native_decide|^\s*axiom\b" RBM3D/BA/GUEDuhamelBA*.lean | wc -l  -> 0
$ grep -nE "^import RBM3D.BA.(MainInd|TwistPins|Step6|TwistStep|TwistAvg)" RBM3D/BA/GUEDuhamelBA*.lean | wc -l -> 0
imports: GUEDuhamelBA: BA.GUEEq729BA, Universality.GUEPhase.DuhamelC, Chain.StepDecompGen; GUEDuhamelBA2: BA.GUEDuhamelBA
$ for m in GUEEq729BA DuhamelC StepDecompGen: git cat-file -e main:<file>  -> main has all three
$ git diff --name-status 19df37e2 main -- 'RBM3D/*.lean'
A RBM3D/BA/GUEEntryGridBA.lean | A RBM3D/BA/GUEHypABA.lean | M RBM3D/BA/GUEProcBA.lean | D RBM3D/Probe/T2519Pins.lean
```
No new structure/Prop field; the only upstream fact with a probabilistic content, `condExp_loop_drift_gueBA` (`BA/GUEEq729BA.lean:488`, merged C4 b), has only deterministic premises (`0 < Im m`, `‖m‖ ≤ 1`, `I.WF`, time order, `K n ≠ 0`, `k < K n`, `u_{k+1} < 1`). No external hypothesis, so no limit check is owed. No row-b file imports any file changed between 19df37e2 and `main` (row a's `GUEProcBA` is not imported), so the base drift does not touch row b's closure. No cycle (row b imports nothing of rows a, b′, c, d).

## 3. Compiled nonempty instances (target 8)
| target | instance (`RBM.BA.GUEDuhamelBAInst`) | data |
|---|---|---|
| `Duhamel_step_decompBA` | `Duhamel_step_decompBA_check` (`GUEDuhamelBA.lean:848`) | `d=3`, `sz0` (`L₀=4`, `W₀=32`), BA flow datum `(gI,EI,mI)` via `BAflow_real … flow_sz0`, `t₁=17/20<t₀=9/10<1`, `K=131072`, `j=0`, 2-loop `(+,−;0,1)`, `ω=0 ∈ DuhamelGood` (`DuhamelA2Inst.zero_mem_good`) |
| `Duhamel_drift_remainder_aeBA` | `_check` (`:867`) | same, `k=0`; `im_pos_I`, `norm_le_I` from `BAReal` |
| `Duhamel_azuma_ZBA` | `_check` (`:897`) | `lam=1`, `k=3`, `ε=1`, `hv_I` proved |
| `Duhamel_azuma_YBA` | `_check` (`:938`) | `K=1`, `k=1`, `ε=1`, `b=bI`; `hb` discharged by `GUEDuhamelBA_bddC2C_Phi` + `Duhamel_norm_T_le` |
| **`gueGrid_loop_duhamelBA`** | `_check` (`GUEDuhamelBA2.lean:1033`) | `τU=1/2`, `n₀=1`, `ℓ=2`, `K=gueGridK sz0 1`; `hsize` = merged `MarkovInst.sz0_size_tendsto_nat`; `hscale_I` proved (`η_{t₀} ≥ 1/20`, `N ≥ 400`) |
Every hypothesis is discharged in each instance; none is left as a premise. Nondegeneracy, re-checked in an uncommitted scratch file (`ax.lean`, below), compiles silently:
```
example : sz0.L 0 = 4 ∧ sz0.W 0 = 32 := by decide
example : (17/20 : ℝ) < 9/10 ∧ (9/10 : ℝ) < 1 := by norm_num
example : loop2 4 0 1 ≠ loop2 4 0 0 := by decide
```
The `K = gueGridK sz0 1 = (N+1)^96` grid is the ticket's own grid (band `DuhamelC:1485`), not a witness chosen large to satisfy a hypothesis; `hscale` holds from `N ≥ 400` while `N₀ = 2^21`.

## 4. Build and axioms
```
$ lake build RBM3D.BA.GUEDuhamelBA RBM3D.BA.GUEDuhamelBA2     # audit worktree, oleans written 14:36 UTC
Build completed successfully (3953 jobs).     (0 error lines; no warning line in GUEDuhamelBA*)
$ lake env lean ax.lean
'RBM.BA.gueGrid_loop_duhamelBA' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.Duhamel_step_decompBA' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.Duhamel_drift_remainder_aeBA' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.Duhamel_azuma_ZBA' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.Duhamel_azuma_YBA' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.GUEDuhamelBAInst.gueGrid_loop_duhamelBA_check' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.GUEDuhamelBAInst.Duhamel_step_decompBA_check' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.GUEDuhamelBAInst.Duhamel_drift_remainder_aeBA_check' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.GUEDuhamelBAInst.Duhamel_azuma_ZBA_check' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.GUEDuhamelBAInst.Duhamel_azuma_YBA_check' depends on axioms: [propext, Classical.choice, Quot.sound]
$ git diff --name-status 19df37e2...t/T2519b
M RBM3D.lean | A RBM3D/BA/GUEDuhamelBA.lean | A RBM3D/BA/GUEDuhamelBA2.lean
$ git diff 19df37e2...t/T2519b -- RBM3D.lean   -> +import RBM3D.BA.GUEDuhamelBA, +import RBM3D.BA.GUEDuhamelBA2 (after the last import; #assert_rbm_axioms stays last)
$ wc -l RBM3D/BA/GUEDuhamelBA*.lean   -> 948, 1058, total 2006
```
All three files are sole writable files of row b (ticket Sole writable files; Layout "reserve `GUEDuhamelBA2` past 1,500"). No band or merged file edited; `open private … from` only (`GUEDuhamelBA.lean:52-54`, `GUEDuhamelBA2.lean:29-33`), no `private` deleted. Each file < 2,000 (binding); row sum 2,006 < landing line 2,245 (Amend 2 item 5). Name clash: `git grep -w` of the 13 new public names / namespace on `main`, `t/T2519`, `t/T2519b2` (row-b files excluded): all 0. Public names are pinned (target 6 names, "the Azuma lines") or stem-prefixed `GUEDuhamelBA_*` (rule E). Full `lake build` is the hub's at merge.

## 5. Paper deltas
The prove report (d) proposes `T2519ba1` (BA grid path `gΨ_I + H_k`, `z_t = E + (1−t)m`, `0 < Im m ∧ ‖m‖ ≤ 1` in place of `|E| ≤ 2−κ`), `T2519ba2` (`‖z_{j+1}−z_j‖ ≤ Δ‖m‖`), `T2519ba3` (`Duhamel_step_decompBA` without `0 ≤ t1 n`). These cover every difference of §1 (i)–(iii); (iv) is not a mathematical difference. Tags follow Decision (14) (`T2519ba…`). `grep T2519ba docs/paper-deltas.md` → 0 (not yet appended; dispatcher's).

## 6. Verdicts
| target | verdict |
|---|---|
| 6 `Duhamel_drift_remainder_aeBA` | PASS |
| 6 `Duhamel_step_decompBA` | PASS |
| 6 `Duhamel_azuma_ZBA`, `Duhamel_azuma_YBA` | PASS |
| 6 **`gueGrid_loop_duhamelBA`** | PASS |
| 8 instances | PASS |
**Row b: PASS.** No dispatcher sign-off needed.

## 7. Observations (no RETURN)
1. The reserve `GUEDuhamelBA2` is used with the main file at 948 < 1,500; the layout reads "past 1,500" for the row, and the unsplit row (2,006) would pass it. Not a statement/instance/build issue.
2. The endpoint states `loopMax (gueHBA …)` inline instead of row a's `gueLmaxBA`; definitionally equal (§1). Row c must bridge by `unfold`/`rfl`.
3. The report (b2) lists 13+21+15 `open private` names; not re-audited name by name (process, not statement).
4. Row b reads no `BA/TwistAvg*` name (report (b5) grep 0; my import grep 0), consistent with Amend 3 item 3.
