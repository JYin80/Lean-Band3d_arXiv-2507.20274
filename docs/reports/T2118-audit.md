Auditor model: claude-opus-5-5

# T2118 audit, round 2 (ST2-11, `Induction/EMn2Exp2`), Sun Oct  4 10:33:33 UTC 2026

Branch `t/T2118` at `e9983a2` (merge base `471b643`, `main` = `dd1748c`). Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2118-audit2`
(detached). Scripts are in `scratchpad/T2118/`. This round checks against Amend 2 (DECISIONS §36): the targets are
`emn2Exp_far3 (d : ℕ) (hd : 3 ≤ d) : …` (the `h3` of `emn2Exp_of_far3` at `3 ≤ d`) and
`stEMn2Exp_holds (d : ℕ) (hd : 3 ≤ d) : STEMn2Exp d`. The pins are unchanged.

**Verdict: PASS (both targets).** No dispatcher sign-off is needed: Amend 2 / DECISIONS §36 already signed off on `hd`.

## 1. Statement against the amended pin

```
$ python3 scratchpad/T2118/stmt.py
target1 header: theorem emn2Exp_far3 (d : ℕ) (hd : 3 ≤ d) :
target1 body == h3 body (whitespace removed): True
target2: theorem stEMn2Exp_holds (d : ℕ) (hd : 3 ≤ d) : STEMn2Exp d := emn2Exp_of_far3 d (emn2Exp_far3 d hd)
$ grep -n "def STEMn2Exp" RBM3D/Induction/Step2Defs.lean ; sed -n 1715p RBM3D/Induction/EMn2Exp1.lean
456:def STEMn2Exp (d : ℕ) : Prop :=
1715:theorem emn2Exp_of_far3 (d : ℕ)
$ git diff --stat 471b643 main -- RBM3D/Test/Axioms.lean RBM3D/Induction/EMn2Exp2.lean      # main untouched on the writable files
(empty)
```
- Target 1: the body is token-for-token the `h3` premise of the merged `emn2Exp_of_far3` (same quantifier order, `∀ D > 0`,
  `Ψ` window `∀ᶠ`, `Prec` eventual, `0 ≤ t ≤ lemT`, no `L^d ≤ W^K`). The only extra premise is `(hd : 3 ≤ d)`, which Amend 2 allows.
- Target 2: the signature is exactly the Amend 2 form. `STEMn2Exp` and `emn2Exp_of_far3` are not in the diff, so they are unchanged.

The three DECISIONS §36 conditions:
```
$ sed -n 523p RBM3D/Evolution/PropTInf.lean ; sed -n 55p RBM3D/Path/KellStar.lean          # (i) inputs stated for d ≥ 3 only
  3 ≤ d →
  ∀ (sz : Sizes d) (𝔠 Λ τ δ D : ℝ) (t : ℕ → ℝ), 3 ≤ d → 0 < 𝔠 → 0 < Λ → 0 < τ → 0 < δ →
$ grep -n "^def STStep2 " -A1 RBM3D/Induction/Step2Defs.lean                               # (ii) endpoint consumer
599:def STStep2 (d : ℕ) : Prop :=
600:  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
$ grep -rn "STEMn2Exp d" RBM3D | grep -v "EMn2Exp[12].lean\|Step2Defs" | cut -c1-80
RBM3D/Induction/Step2Iterate.lean:284:theorem ST_selfImprove_section (hLWT : STLWT d) (hEMe : STEMn
RBM3D/Induction/Step2Iterate.lean:700:theorem ST_selfImprove (hLWT : STLWT d) (hEMe : STEMn2Exp d)
RBM3D/Induction/Step2Iterate.lean:1393:theorem ST_step2_of_pins (hNew : STNewKLK d) (hLWT : STLWT d)
RBM3D/Induction/Step2Iterate.lean:1756:theorem ST_step2_of_pinsN {d : ℕ} (hNew : STNewKLK d) (hLWT
RBM3D/Induction/Step2Iterate.lean:1779:theorem ST_step2_of_pins' {d : ℕ} (hNew : STNewKLK d) (hLWT
RBM3D/Induction/Step2Iterate.lean:1786:theorem ST_step2_of_pinsN' {d : ℕ} (hNew : STNewKLK d) (hLWT
RBM3D/Induction/Step2Iterate.lean:1794:    (hEMe : STEMn2Exp d) (hRep : STGridRepN d) (hOpt : STOptL2 d) (hClo
RBM3D/Induction/Step2Events.lean:348:theorem ST_LW_sections (hLWT : STLWT d) (hEMe : STEMn2Exp d) (hd
RBM3D/Induction/Step2Events.lean:637:theorem ST_event_lw (hLWT : STLWT d) (hEMe : STEMn2Exp d) (hd : 0
RBM3D/Induction/Step2Events.lean:710:theorem ST_event_mg (hLWT : STLWT d) (hEMe : STEMn2Exp d) (hd : 0
```
- (i) holds: `EKPropTInf` (the `(TTT2)` input) and `KellStarEv` (the far field in `(eq_L2-J)`) are stated only for `3 ≤ d`.
- (ii) holds. All the consumers above take `STEMn2Exp d` as a hypothesis and pass it on. The `0 < d` lemmas (`ST_selfImprove*`,
  `ST_LW_sections`, `ST_event_*`) feed `ST_step2_of_pins*`. These conclude `STStep2 d`, which is `3 ≤ d → …` (Step2Defs:600).
  No consumer discharges the pin at a `d` without `3 ≤ d`.
- (iii) holds. The prove report lists the consumers (round 1 §1), and the file's last example compiles the chain to a `3 ≤ d` endpoint:
  `example … : STStep2 d := fun hd3 => ST_step2_of_pins' hNew hLWT (stEMn2Exp_holds d hd3) hMart hOpt hClos hd3` (EMn2Exp2.lean:1291–1293).

Result: PASS.

## 2. Hidden hypotheses, vacuity, cycles (round-1 findings re-checked)

```
$ grep -n "^import\|^open private" RBM3D/Induction/EMn2Exp2.lean | cut -c1-70
6:import RBM3D.Induction.EMn2Exp1
7:import RBM3D.Evolution.PropTInf
47:open private emn2Exp_zdistInf_zero emn2Exp_zdistInf_tri emn2Exp_zdistInf_sub_comm
50:open private hs hs_nonneg trace_mul_conjTranspose_eq Gres_conjTranspose Pm Eblk_eq_smul_Pm
52:open private card_ball_le from RBM3D.Induction.ContractPt
53:open private pti_sum_radial from RBM3D.Evolution.PropTInf
54:open private KLWard_mSigma_mul from RBM3D.Loop.KLWard
```
- Target 1 has exactly the premises of the merged `h3` (`STFlow`, `STInitialGT2`, `∀ D, STLWassmExp`) plus `hd`. It adds no structure and no new
  external hypothesis. All imports are merged modules, so there is no cycle. The round-1 grep for `GbEXPij|GijGEX` found docstrings only.
  The branch has not changed since round 1 (same commit `e9983a2`), so the findings stand.

## 3. Compiled nonempty instances (EMn2Exp2.lean:1113–1295, `namespace RBM.Gauss.EMn2Exp2Inst`)

| endpoint | example | data | open hypotheses |
|---|---|---|---|
| `emn2Exp_far3` | l.1252 | `d=3` (`hd` by `norm_num`), `sz0`, `κ=ε=𝔡=1/10`, `𝔠=1/6`, `z0`, `t≡1/16`, `ε₀=1/20`, `Ψ=W^{-1}`, `ℓ=ℓ_t`, any `D>0` | `STInitialGT2`, `∀D, STLWassmExp` (other gates' pins) |
| `stEMn2Exp_holds` | l.1273 | same | same |
| downstream fit | l.1291 | `ST_step2_of_pins'` with `stEMn2Exp_holds d hd3` | the five other Step-2 pins |
| `emn2Exp2_S3_le`, `emn2Exp2_loop6_le`, `emn2Exp2_loop2_far_le` | l.1141, 1183, 1227 | `d=3,L=3,W=2` Hermitian `H`, `z=1/2+i/4`, labels with `|a−b|>ℓ*`; `sz0` | none |

The deterministic hypotheses (`STFlow` via `flow_z0`, `t ≤ lemT` via `sixteenth_le_lemT`, the `Ψ` window `Ψ1_window`, and the `ℓ` range
`ℓ_range_inst`) are discharged at the concrete data. Round 1 showed the far set `{|a−b|_∞ > ℓ†_t}` is nonempty for `n+1 ≥ 189`.
None of the instances is degenerate. PASS.

## 4. Build, axioms, hygiene, scope

```
$ lake build RBM3D.Induction.EMn2Exp2 > build.log 2>&1; echo exit $?; tail -2 build.log
exit 0
✔ [3769/3769] Built RBM3D.Induction.EMn2Exp2 (11s)
Build completed successfully (3769 jobs).
$ grep "EMn2Exp2.lean" build.log | grep -ciE "warning|error"
0
$ lake env lean scratchpad/T2118/ax.lean
'RBM.Gauss.Sizes.emn2Exp_far3' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.stEMn2Exp_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.emn2Exp2_S3_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.emn2Exp2_loop6_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.emn2Exp2_loop2_far_le' depends on axioms: [propext, Classical.choice, Quot.sound]
$ grep -nEw "sorry|admit|axiom|native_decide|sorryAx" RBM3D/Induction/EMn2Exp2.lean | wc -l
       0
$ git diff --stat main...t/T2118
 RBM3D/Induction/EMn2Exp2.lean | 1295 +++++++++++++++++++++++++++++++++++++++++
 RBM3D/Test/Axioms.lean        |    1 -
 2 files changed, 1295 insertions(+), 1 deletion(-)
$ git diff main...t/T2118 -- RBM3D/Test/Axioms.lean | grep '^[-+][^-+]'
-   `RBM.Gauss.Sizes.STEMn2Exp, -- `lem: EMn2_N`, `(eq:MG_conclusion3)` (`3_5:437-440`): ST2-10, ST2-11 (T2066, DECISIONS §28)
```
- Only the two sole writable files change. No frozen signature is touched. The registry line removal is accepted by Amend 2 / DECISIONS §36.
- The full `lake build` was not rerun here; the hub runs it at merge. Prove report (b.3), line 235, shows the registry removal builds only
  together with the root import `import RBM3D.Induction.EMn2Exp2`, so the hub must add both in the same merge.

Result: PASS.

## 5. Paper deltas

```
$ sed -n 260p docs/reports/T2118-prove.md | grep -o "T2118b[^;]*" | cut -c1-60
T2118b** `3 ≤ d` hypothesis of the two theorems (above).
```
The candidates `T2118a` (split route, `∀ D > 0`), `T2118b` (`3 ≤ d`), `T2118c` (HS 2-loops instead of `(GijGEX)`), `T2118d` (`W^{-d}` term
in `(eq_L2-J)`) and `T2118e` (`(1−t)⁻¹ ≤ η_t⁻¹`) are in prove report (d) 4. DECISIONS §36 names `T2118b` as the record of the `3 ≤ d`
condition. `docs/paper-deltas.md` has no T2118 entry yet: the dispatcher appends and numbers the candidates. Coverage is complete. PASS.

## 6. Per-target verdict

- **Target 1 `emn2Exp_far3 (d) (hd : 3 ≤ d)`: PASS.** It is the `h3` of `emn2Exp_of_far3` at `3 ≤ d`, as amended.
- **Target 2 `stEMn2Exp_holds (d) (hd : 3 ≤ d) : STEMn2Exp d`: PASS.** The statement is as amended, and the registry removal is accepted.

## 7. Observations (no effect on the verdict)

- O1 (from round 1, stands): `open private … from` reaches private names in five merged files (lines 47–54). A rename there breaks this build.
- O2: the docstring of `stEMn2Exp_holds` (l.1084–1087) names the condition: "**`3 ≤ d` is a hypothesis** (the pin has none …)". This is
  the docstring condition of DECISIONS §36.
