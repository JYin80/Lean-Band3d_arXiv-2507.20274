Auditor model: claude-opus-5-5

# T2153 audit (round 1) — ST2-31 `Induction/GridEnvelopeN`

Written Sun Oct  4 18:53:52 UTC 2026 (`date -u`). Branch `t/T2153` at `bab80fd`; audit worktree
`/Users/junyin/Lean_proof/RBM3D-wt/T2153-audit1` (detached). Source pin: RBM2D
`RBM2D/Induction/GridEnvelopeN.lean` at `c9a24cf` (`gen2d.lean`, 713 lines).

## 1. Diff scope, hygiene, names

```
$ git diff --name-only main...t/T2153
RBM3D/Induction/GridEnvelopeN.lean
$ grep -nE "sorry|admit|native_decide|^\s*axiom|set_option" RBM3D/Induction/GridEnvelopeN.lean
48:set_option linter.style.longLine false
49:set_option linter.unusedSectionVars false
50:set_option linter.unusedVariables false
$ for n in gridDriftN_envelope sum_gridStep_div_etaT_le SumWeightedStepErrN_Stmt sum_weighted_stepErrN_le GridEnvelopeNCheck; do printf "%s: " $n; git grep -n "\(theorem\|def\|lemma\|namespace\) $n\b" main -- RBM3D | wc -l; done
gridDriftN_envelope:        0
sum_gridStep_div_etaT_le:        0
SumWeightedStepErrN_Stmt:        0
sum_weighted_stepErrN_le:        0
GridEnvelopeNCheck:        0
```
Public declarations: the four targets; instance data/checks inside `RBM.Ind.GridEnvelopeNCheck`
(layout of merged `GridDriftNCheck`); private helpers `gridEnv_*`. New file only; no frozen signature touched.

## 2. Build and axioms (audit worktree)

```
$ lake build RBM3D.Induction.GridEnvelopeN   (exit=0; error/warning lines naming the module: 0)
ℹ [3792/3792] Built RBM3D.Induction.GridEnvelopeN (6.4s)
info: RBM3D/Induction/GridEnvelopeN.lean:786:0: 'RBM.Ind.gridDriftN_envelope' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM3D/Induction/GridEnvelopeN.lean:787:0: 'RBM.Ind.sum_gridStep_div_etaT_le' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM3D/Induction/GridEnvelopeN.lean:788:0: 'RBM.Ind.SumWeightedStepErrN_Stmt' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM3D/Induction/GridEnvelopeN.lean:789:0: 'RBM.Ind.sum_weighted_stepErrN_le' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM3D/Induction/GridEnvelopeN.lean:790:0: 'RBM.Ind.GridEnvelopeNCheck.sum_weighted_stepErrN_instance' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM3D/Induction/GridEnvelopeN.lean:791:0: 'RBM.Ind.GridEnvelopeNCheck.sum_gridStep_instance' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM3D/Induction/GridEnvelopeN.lean:792:0: 'RBM.Ind.GridEnvelopeNCheck.gridDriftN_envelope_instance' depends on axioms: [propext, Classical.choice, Quot.sound]
Build completed successfully (3792 jobs).
```

## 3. Statements against the pin (RBM2D `c9a24cf` through the T2111 dictionary)

Script: extract each statement from `theorem|def <name>` to `:= by`, apply the dictionary
`dict.sed`, token-diff against the RBM3D file.
```
$ cat dict.sed | tr '\n' ';'
s/(d : Sizes)/(d : ℕ) (sz : Sizes d)/g;s/SizeTendsto d/sz.SizeTendsto/g;s/RangeCond d τ' t/sz.RangeCond τ' t/g;s/pathP d/pathP sz/g;s/predIncN d /predIncN sz /g;s/pathH d /pathH sz /g;s/Z2 (d\.L n)/Zd d (sz.L n)/g;s/d\.size/sz.size/g;s/stepErrN (d\.L n) (d\.W n)/stepErrN d (sz.L n) (sz.W n)/g;s/ksimLK (d\.L n) (d\.W n) /sz.STksimLKM n /g;s/elklkN (d\.L n) (d\.W n) /sz.STelklkM n /g;s/egtN (d\.L n) (d\.W n) /sz.STegtM n /g;s/spectralM/mE/g;s/ \[NeZero k\]//g;
$ for f in gridDriftN_envelope sum_gridStep_div_etaT_le SumWeightedStepErrN_Stmt; do ... diff a.$f b.$f; done
== gridDriftN_envelope:      263 vs      271 tokens
2a3,6 > (sz > : > Sizes > d) 41a46,49 > (hKb > : > sz.STKbound > E)
== sum_gridStep_div_etaT_le:      110 vs      114 tokens
2a3,6 > (sz > : > Sizes > d)
== SumWeightedStepErrN_Stmt:      279 vs      279 tokens
```
(`(sz : Sizes d)` is the RBM2D section variable `d : Sizes` made explicit.) `sum_weighted_stepErrN_le`
is `: SumWeightedStepErrN_Stmt` in both files. So, modulo the dictionary:
- `SumWeightedStepErrN_Stmt`: identical (all four exponent inequalities `8+(4k+8)(1-τ')+2D_t < C_K`,
  `3+4τK+5k(1-τ')+D_t < C_K`, `2(1-τ')+τK+2k(1-τ')+D_t < C_K`, `1-τ' < C_K`, the hypothesis
  `N^{C_K} ≤ K n` eventually, the conclusion `≤ N^{-D_t}` for all `m ≤ K n`); `[NeZero k]` dropped
  (stronger). No `d`-dependent exponent: `stepErrN d …` carries `W^d`, `N = (WL)^d` internally.
- `sum_gridStep_div_etaT_le`: identical; conclusion `Σ_{j<K n} Δ/η_{u_j} ≤ (Im m(E))⁻¹ log N`,
  as the ticket's mathematics. `RangeCond` is `∀ᶠ n, N^(-1+δ) ≤ 1 - t n` (`Green/Pins.lean:55`).
- `gridDriftN_envelope`: identical plus one hypothesis `hKb : sz.STKbound E`; `[NeZero k]` dropped.
  The quantifier order (fixed `κ k τK E s t K`, then `∀ᶠ n`, `∀ᵐ ω`, `∀ j < K n`, `∀ a`) and the
  envelope `B_k = N^{τK} η_{u_{j+1}}^{-k}` uniform in `j` are as pinned.

The extra hypothesis is forced by the merged dependency:
```
$ sed -n 1098,1104p RBM3D/Induction/GridDriftN.lean
theorem exists_norm_Kcal_le_win (hsz : sz.SizeTendsto) (E : ℕ → ℝ) (hKb : sz.STKbound E)
    (hE : ∀ n, |E n| < 2) (v : ℕ → ℝ) (hv0 : ∀ n, 0 ≤ v n) (hv1 : ∀ n, v n < 1) (m : ℕ)
    (τ : ℝ) (hτ : 0 < τ) :
    ∀ᶠ n in atTop, ∀ w ∈ Set.Icc (0 : ℝ) (v n), ∀ J : LoopIdx (Zd d (sz.L n)), J.WF →
      2 ≤ J.length → J.length ≤ m →
        ‖KLK d (sz.L n) (sz.lam n) (sz.W n) (E n) w J‖ ≤
          ((sz.size n : ℕ) : ℝ) ^ τ * ((etaT (E n) (v n))⁻¹) ^ m := by
$ sed -n 939,941p docs/paper-deltas.md   (main worktree)
## D232 · `exists_norm_Kcal_le_win` 沿尺寸序列、以欠下的 `STKbound` 为前提（2026-10-04，T2111a；…）
RBM2D 由已证的 `Kbound_prec_uncond` 对 `(L,W,E,u,v)` 一致地证；本库沿尺寸序列陈述，前提为欠下的 `STKbound sz E` 与 `SizeTendsto`，对一切 `w ∈ [0, v_n]`。总调度 06:20 照准（票末注）；消费者 ST2-31 须用此形式；…
$ grep -n "STKbound" docs/DECISIONS.md | sed -n 2p | cut -c1-60
167:- **公理登记（§16）**：`STKbound` 记 owed（KL7 证），…
```
`STKbound` is an explicit, dispatcher-signed owed gate pin (DECISIONS §167, D232), not a structure
field. The per-`n` fixed sequence `v` of the merged lemma is turned into the uniform-in-`j` envelope
inside the proof (worst-index choice); Lean checks it.

## 4. Vacuity, hidden hypotheses, cycles

- No new structure; all hypotheses in the signatures (`Sizes d`, `STKbound`, `RangeCond`, `SizeTendsto`
  are merged). Imports (lines 6–7): only merged `Induction.GridGoodN`, `Induction.GridDriftN`; no cycle.
- External hypothesis `STKbound` (owed gate pin, KL7/KL14): no limit computation is required of this
  ticket beyond being an authorized owed pin (same treatment as merged `exists_norm_Kcal_le_win_instance`,
  `GridDriftN.lean:1236`).

## 5. Compiled nonempty instances (all at `d = 3`, merged `sz0`: `L_n=4(n+1)`, `W_n=(2(n+1))^5`)

```
$ sed -n 716,722p RBM3D/Induction/GridEnvelopeN.lean
  sum_weighted_stepErrN_le 3 sz0 (κ := 1) (τ' := 1 / 2) (τK := 1 / 2) (C_K := 21) (D_t := 1)
    (E := E1) (s := fun _ => 0) (t := fun _ => 1 / 2) (K := Kc) 3 one_pos (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) sz0_tendsto
    (fun _ => by norm_num) (fun _ => le_rfl) (fun _ => by norm_num) (fun _ => by norm_num)
    Kc_ne_zero rangeCond_half (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (Eventually.of_forall rpow_21_le_Kc)
$ sed -n 750,752p RBM3D/Induction/GridEnvelopeN.lean
  sum_gridStep_div_etaT_le sz0 (τ' := 2 / 3) (by norm_num) (E := E1) (s := fun _ => 0) (t := tBd)
    (K := fun _ => 4) (fun _ => by norm_num) (fun _ => le_rfl) (fun n => zero_le_tBd n) tBd_lt_one
    (fun _ => by norm_num) rangeCond_tBd
$ sed -n 756p;777,779p RBM3D/Induction/GridEnvelopeN.lean
theorem gridDriftN_envelope_instance (hKb : sz0.STKbound E1) (σ : Fin 3 → Bool) :
  gridDriftN_envelope sz0 1 one_pos 3 (by norm_num) (1 / 2) (by norm_num) sz0_tendsto hKb
    (fun _ => by norm_num) (fun _ => by norm_num) (fun _ => by norm_num) (fun _ => by norm_num)
    (fun _ => by norm_num) σ
```
- `sum_weighted_stepErrN_instance`: every hypothesis discharged; `k=3`, `τ'=τK=1/2`, `D_t=1`,
  `C_K=21` (inequalities `20<21`, `13.5<21`, `5.5<21`, `0.5<21`), `t ≡ 1/2 < 1`, `RangeCond` proved
  (`rangeCond_half`), `K n = N_n^21`. The size of `K` is forced by the hypothesis `N^{C_K} ≤ K n`
  (minimal admissible `C_K` > 8 at `τ'=1, D_t=0`); not a degenerate witness.
- `sum_gridStep_instance`: every hypothesis discharged; `t_n = 1 - N_n^{-1/3}` sits exactly on the
  `RangeCond(2/3)` boundary (`rangeCond_tBd` by `ring`), `K ≡ 4`, nonempty sum.
- `gridDriftN_envelope_instance`: every deterministic hypothesis discharged (`s ≡ 1/10 ≤ t ≡ 1/2 < 1`,
  `K ≡ 4`, `k = 3`, `|E| = 0 ≤ 1`); only the owed gate pin `STKbound sz0 E1` stays a hypothesis
  (allowed by CLAUDE.md §4 step 2).
No `N = 0`, empty index, collapsed window, or `False` premise.

## 6. Paper deltas

Lean/pin differences: (i) `hKb : sz.STKbound E` in `gridDriftN_envelope` — proposed `T2153a`, and the
underlying change is already numbered D232; (ii) `[NeZero k]` dropped from `gridDriftN_envelope` and
`SumWeightedStepErrN_Stmt` (stronger) — proposed `T2153b` (cf. D233 for `GridDriftN`). The remaining
differences are the dictionary (`Sizes d`, `Zd d`, `W^d`, `N=(WL)^d`, merged `ST*M` names). Coverage
complete.

## 7. Observations (no effect on verdict)

- O1. `STKbound` is not in `owedProps` of `RBM3D/Test/Axioms.lean` (`grep -c STKbound` → 0), though
  DECISIONS §167 classes it owed; pre-existing on `main`, not in this ticket's scope.
- O2. The prove report states the full `lake build` was not run by stage 1b (ticket acceptance lists
  it); the hub's merge build covers it.
- O3. `T2153c` (instance keeps `STKbound`) is not a statement delta. O4. `κ`, `hκ` unused in the
  proof of `gridDriftN_envelope` (kept as pinned).

## Verdict

`gridDriftN_envelope` PASS (signed owed pin `STKbound`, D232); `sum_gridStep_div_etaT_le` PASS;
`SumWeightedStepErrN_Stmt` PASS; `sum_weighted_stepErrN_le` PASS.

Overall: **PASS**. No dispatcher sign-off needed.
