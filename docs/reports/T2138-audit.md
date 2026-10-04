Auditor model: claude-opus-5-5

# T2138 audit, round 1 (S5-01: Step 5 pins into `Induction/Step5Pins.lean`, `tailTD` into `Defs/Tail.lean`, registry)

Time: Sun Oct  4 16:31:27 UTC 2026 (`date -u`). Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2138-audit1`, detached at `t/T2138` = `c9f5c46`; main tip `f22c63c`.
Scratch files: `<scratchpad>/T2138/` (probe copy, diff, build log, `AuditCheck.lean`).

**Verdict: PASS** (every target). Observations O1-O4 below change no statement, instance, build, axiom or paper-delta coverage.

## 1. Files touched

```
$ git diff --stat main...t/T2138
 RBM3D/Defs/Tail.lean           |   13 +
 RBM3D/Induction/Step5Pins.lean | 1042 ++++++++++++++++++++++++++++++++++++++++
 RBM3D/Test/Axioms.lean         |   27 +-
$ git diff main...t/T2138 -- RBM3D/Defs/Tail.lean | grep '^-[^-]' | wc -l
       0
$ git diff main...t/T2138 -- RBM3D/Test/Axioms.lean | grep '^-[^-]'     # only the closing `]` of two lists becomes `,`
-   `RBM.Green.FlucGainUpTo'] -- gain interface ...
-   `RBM.Path.UkerFar] -- the far-kernel condition ...
$ git diff --stat t/T2138...main -- RBM3D/Defs/Tail.lean RBM3D/Test/Axioms.lean RBM3D/Induction/Step5Pins.lean
(empty: main has not touched the three files since the merge-base 7f82dd6)
```
Only the three sole writable files; `Tail.lean` is append-only (no line removed, no frozen signature touched); `Axioms.lean` changes are registry lines only. Imports of `Step5Pins.lean`: `RBM3D.Induction.KDecay`, `NewKLK`, `GridDuhamelN` (not `RBM3D`).

## 2. Statements: copied text against the pin (probe `7b2b789:RBM3D/Probe/T2134Pins.lean`)

The ticket pins the statements as a verbatim copy of the probe (DECISIONS §40 accepted them). Script diff:

```
$ git show 7b2b789:RBM3D/Probe/T2134Pins.lean > probe.lean; wc -l probe.lean
    2434 probe.lean
$ diff <(sed -n '1,476p;1704,1818p;1856,2254p;2275,2331p' probe.lean) RBM3D/Induction/Step5Pins.lean | grep -c '^[<>]'
51
$ diff ... | grep -E '^[0-9]'
11c11   12a13   17,23c18,24      (module docstring header)
34,46d34                         (section 1 `tailTD`: moved to Defs/Tail.lean)
474a463,471                      (`st5_reg5I_mid` added, see below)
476a474  591a590  990a990        (blank lines)
492c490                          (< namespace RBM.Gauss.T2134Inst  > namespace RBM.Gauss.Step5Inst)
993,998d992                      (`tailTD_nonneg`: moved to Defs/Tail.lean)
1047a1042                        (> end RBM.Gauss.Step5Inst)
$ diff <(sed -n '732,739p' probe.lean) <(sed -n '464,471p' RBM3D/Induction/Step5Pins.lean) && echo SAME_st5_reg5I_mid
SAME_st5_reg5I_mid
```
`tailTD`/`tailTD_nonneg` in `Defs/Tail.lean` (diff of the branch):
```
+noncomputable def tailTD (d : ℕ) (W u D r : ℝ) : ℝ :=
+  ((W ^ d * |1 - u|)⁻¹) ^ 2 * Real.exp (-Real.sqrt r) + W ^ (-D)
+theorem tailTD_nonneg {d : ℕ} {W u D r : ℝ} (hW : 0 ≤ W) : 0 ≤ tailTD d W u D r := by
```
Probe text: `def tailTD (d : ℕ) (W u D r : ℝ) : ℝ := ((W ^ d * |1 - u|)⁻¹) ^ 2 * Real.exp (-Real.sqrt r) + W ^ (-D)`; only `noncomputable` added. Body = `(W^d|1-u|)^{-2} e^{-√r} + W^{-D}` = ticket item 2 (`def_WTuD`, `3_5:2297`).

No pin statement differs from the probe; every non-docstring difference is a move (item 2), the namespace rename (ticket), or the verbatim probe lemma `st5_reg5I_mid` (deterministic `STReg5I → STReg5Mid` for `2 ≤ d`; needed by `inst_etermsMid`, `inst_duhamelI`).

Per pin (statement = probe = §40): `STReg5I/II/III/IV/Mid`, `STIngR5`, `STStep5R`, `STStep5Concl`, `STDecayStrongU`, `STStep5I/II/III/IV`, `STStep5`, `STEtermsMid`, `STDuhamelConcl`, `STDuhamelI/II`, `STIniTermI/II`, `STWardII`, `STNewKLKL(At)`, `STCltFar`, `STCltIso`, `STExpInv`, `STLemDecCalE`, `STPfStep5`, `STTailtoTail`: **PASS**. Parameter order kept (`3 ≤ d →`, constants `κ ε 𝔡 Cd` before `∃ 𝔠d ≤ 1/100`, before the size sequence); `0 ≤ s`, `s < t`, `t ≤ lemT z` present in `STIngR5`; `STTailtoTail` has `0 ≤ s ≤ t < 1`, `g² ≤ 1-t`, every `σ`, `zdistInf`.

## 3. Hidden hypotheses, vacuity, cycles

- No new `structure`/`class`; all pins are `def … : Prop` (hypotheses visible in the signatures, b.4 of the prove report and P.2b of T2134).
- No cycle: the file imports only merged modules; no pin is defined through a theorem of this file.
- Registry (DECISIONS §16, §20, §40): owed `STStep5I/II/III`, `STStep5`, `STEtermsMid`, `STDuhamelI/II`, `STIniTermI/II`, `STWardII`, `STNewKLKL`, `STCltFar`, `STCltIso`, `STExpInv`, `STTailtoTail`, `STLemDecCalE`, `STPfStep5` (17 = the ticket's list, with the §40 override borrowed → owed); structural `STReg5I/II/Mid/III/IV`, `STIngR5`. No new borrowed entry. See O2.

## 4. Compiled nonempty instances

Instances in the file (all compiled in the module build of §5): `inst_ing5`, `inst_ing5_I..IV` (generic in `Concl`), `inst_lemDecCalE`, `inst_pfStep5` at `(sz0, z0, 0, 1/16)`; `inst_etermsMid`, `inst_duhamelI`, `inst_iniTermI` at `(szB, zB, 7/8, 15/16)`; `inst_duhamelII`, `inst_iniTermII`, `inst_wardII` at `(szB, zB, 15/16, 31/32)`; `inst_cltFar`, `inst_cltIso` at `(szCL, zCL, 0, 1-L_n^{-2})` with `szCL_cltFar_index_nonempty (n)` (an explicit element `σ=(+,-)`, `a=(x_n,0)` for every `n`) and `szCL_cltIso_witness (n)` (explicit `b`, isolated label, every `n`); `inst_tailtoTail` (`L=5, g=1/2, W=25, D=2, s=1/2, t=3/4`, `A_b = T_{s,D}(|b₁-b₂|)`, `a=(0,e₁)`); `inst_newKLKL` (`sz0`, `n=0`, `E=1/2`, `u=0`, `H=0`, `‖G_0-M‖=0` via merged `STGMM_zero`); `inst_expInv` (`sz0`, `n=0`, `E=1/2`, `u=1/2`).
Each applies the pin at concrete data; flow, time range, `t ≤ lemT`, regime, `(con_st_ind)` for every `𝔠d > 0`, window and index sets are discharged by proof terms (read in the file: e.g. `inst_ing5 … flow_zCL sCL tCL (fun _ => le_rfl) szCL_hst lemT_zCL szCL_reg5I (fun _ h𝔠 => szCL_con h𝔠)`). What stays a hypothesis: the pin itself and the Step 1-4 stochastic premises (`STKbound`, `STKward`, `STLK`, `STDecay`, `STDecayStrong`, `STStep1Loop`, `STStep2Concl`, `STLmaxU`, `STLKU`): other gates' pins, allowed. No `N = 0` (`L ≥ 4`, `W ≥ 4`), no empty index set, no `False` premise; `szCL` (`W = 2^{n+24}`) is large but only to make the `(log W)^5 ≤ L` window nonempty, and the witnesses hold for every `n` (not "astronomically large only").

Pins `STStep5I/II/III/STStep5` have no named `inst_step5*` in this file (probe 1819-1855, portmap P.5 assigns them to S5-02). Auditor check (scratch file, not a source edit) that the generic instances discharge them at the same data:
```
$ cat AuditCheck.lean   (excerpt; opens copied from Step5Pins.lean:490-492)
example (h : STStep5I 3) (Cd : ℝ) (hCd : 0 < Cd) :
    InstIng5Concl (fun sz E s t => STStep5Concl sz E s t) szB zB (fun _ => 7 / 8) (fun _ => 15 / 16) Cd :=
  inst_ing5_I STReg5I _ h szB_reg5I Cd hCd
example (h : STStep5II 3) … := inst_ing5_II STReg5II _ h szB_reg5II Cd hCd
example (h : STStep5III 3) … sz0 z0 sInst tInst Cd := inst_ing5_III STReg5III _ h sz0_reg5III Cd hCd
example (h : STStep5 3) … sz0 z0 sInst tInst Cd := inst_ing5_III STAny _ h trivial Cd hCd
$ lake env lean AuditCheck.lean; echo exit=$?
exit=0
```
**PASS** for every endpoint (see O1).

## 5. Build and axioms (audit worktree)

```
$ lake build RBM3D.Defs.Tail RBM3D.Induction.Step5Pins 2>&1 | grep -E '^error|Build completed|Step5Pins'
✔ [3774/3774] Built RBM3D.Induction.Step5Pins (4.4s)
Build completed successfully (3774 jobs).
exit=0
(warnings: only `linter.style.longLine`; none other in Tail.lean / Step5Pins.lean)
$ grep -nE '\bsorry\b|\badmit\b|^\s*axiom |native_decide' RBM3D/Induction/Step5Pins.lean RBM3D/Defs/Tail.lean; echo $?
1
$ lake env lean AuditCheck.lean | grep -c 'depends on axioms: \[propext, Classical.choice, Quot.sound\]'
18
$ lake env lean AuditCheck.lean | grep -v 'depends on axioms: \[propext, Classical.choice, Quot.sound\]'
(empty)
```
The 18 `#print axioms`: `tailTD_nonneg`, `inst_tailtoTail`, `inst_newKLKL`, `inst_expInv`, `inst_cltFar`, `inst_cltIso`, `szCL_cltFar_index_nonempty`, `szCL_cltIso_witness`, `inst_etermsMid`, `inst_duhamelI`, `inst_iniTermI`, `inst_duhamelII`, `inst_iniTermII`, `inst_wardII`, `inst_lemDecCalE`, `inst_pfStep5`, `inst_ing5_IV`, `st5_reg5I_mid`. (Prove report b.2: `STSigSame/Mixed` depend on `[propext]`, `STSigAll` on none: subsets of the three.) The full `lake build` with the registry is the hub's at merge (prove report b.1 shows it passing with the root import added temporarily).

Name clash against main tip `f22c63c` (108 declaration names of `Step5Pins.lean`, `git grep` on `main`): only `RBM3D/Green/FlucIterGain.lean:977:private def szG : Sizes 3` (private, namespace `RBM.Green`); no clash.

## 6. Paper deltas

```
$ grep -n 'D315–D324' docs/paper-deltas.md
1271:## D315–D324 · Step 5 钉文（2026-10-04，T2134a–j；ST-D4 设计，3668596；签字 §40）
```
D315 (`STNewKLKL` sharp), D316 (`STTailtoTail`, `T_{u,D}`), D317-D318 (`STLemDecCalE`, `STPfStep5`), D319 (`STCltIso`), D320 (`STCltFar`), D321 (case (ii) pins), D322 (`STIniTermI`), D323 (`STExpInv`, `STDecayStrongU` index set), D324 (`STDuhamelConcl`). The copied statements equal the probe's, so no Lean/paper difference is new; the report proposes none. **PASS**.

## 7. Observations (no verdict impact)

- O1. `inst_step5I/II/III/IV`, `inst_step5` (probe 1819-1855) are not in this file although `STStep5I/II/III/IV`, `STStep5` are defined here; ticket item 3 ("instances of the copied pins") and the portmap ranges (S5-02) disagree. The four registered pins are discharged by the existing generic instances (§4 check). S5-02 should copy those instances.
- O2. `STIngR5` is registered **structural**, while its Step 3-4 analogue `STIngR` is registered **owed** (`Test/Axioms.lean:110`). The ticket allows "the other regime/shape predicates" as structural, and only the generic `inst_ing5*` take it as a hypothesis; the named pins (`STStep5I`, …) are owed by name. The dispatcher may want the two shapes classed the same way.
- O3. `st5_reg5I_mid` (probe 732, S5-02 range) is now public in `RBM.Gauss.Sizes`. S5-02 must not copy it again (prove report (d) N1). The name has the probe's `st5_` prefix, not the file stem (§3 (E)), but it is verbatim probe text.
- O4. `STStep5IV` is defined but not registered; no theorem here takes it as a hypothesis (the full build passes), and S5-02 proves it (`stStep5IV_holds`).
