Auditor model: claude-opus-5-5

# T2209 (S5-10, `Induction/PfStep5Alg`) audit, round 1. Mon Oct  5 21:17:56 UTC 2026
Inputs: ticket `docs/tickets/T2209.md`, `docs/tickets/T2209-amend-1.md` (targets 2′ and 4′ adopted, target 7 split off to S5-10a),
check file `docs/tickets/checks/T2209-check.lean`, prove report `docs/reports/T2209-prove.md`, branch `t/T2209` at 4bdfc12,
audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2209-audit1` (detached).
Scope after Amend 1: targets 1, 2′ (+2), 3, 4′ (+4), 5, 6. Target 7 is not in this ticket (Amend 1); its absence is not a defect.

## 1. Diff scope, frozen files, hygiene
```
$ git diff --name-only main...t/T2209
RBM3D/Induction/PfStep5Alg.lean
$ git diff main...t/T2209 -- RBM3D/Test/Axioms.lean RBM3D.lean | wc -l
       0
$ grep -nE "sorry|admit|native_decide|^axiom|set_option maxHeartbeats" RBM3D/Induction/PfStep5Alg.lean; echo "exit $?"
hygiene grep exit 1
```
(`pfStep5Alg_instA_dist` uses kernel `decide`, not `native_decide`.) No sorry/admit/axiom/native_decide; the only file touched is the sole writable file.

## 2. Statements against the pins (script `pindiff.py`: body of every `def PfStep5Alg_*_pin` in the check file vs the branch file)
```
$ python3 pindiff.py
PfStep5Alg_closure_pin identical
PfStep5Alg_goodProb_pin identical
PfStep5Alg_goodStop_pin identical
PfStep5Alg_riemann_pin identical
PfStep5Alg_tailAnti_pin identical
PfStep5Alg_ugenSum_pin identical
new in branch: ["PfStep5Alg_goodStop'_pin", "PfStep5Alg_ugenSum'_pin"]
```
Theorem headers (grep):
```
154:theorem pfStep5Alg_tailAnti {d : ℕ} (sz : Sizes d) : PfStep5Alg_tailAnti_pin sz := by
236:theorem pfStep5Alg_ugenSum' (d : ℕ) : PfStep5Alg_ugenSum'_pin d := by
265:theorem pfStep5Alg_ugenSum (d : ℕ) : PfStep5Alg_ugenSum_pin d := by
343:theorem pfStep5Alg_riemann : PfStep5Alg_riemann_pin := by
388:theorem pfStep5Alg_goodStop' {d : ℕ} (sz : Sizes d) : PfStep5Alg_goodStop'_pin sz := by
405:theorem pfStep5Alg_goodStop {d : ℕ} (sz : Sizes d) : PfStep5Alg_goodStop_pin sz := by
418:theorem pfStep5Alg_goodProb {d : ℕ} (sz : Sizes d) : PfStep5Alg_goodProb_pin sz := by
447:theorem pfStep5Alg_closure {d : ℕ} (sz : Sizes d) : PfStep5Alg_closure_pin sz := by
```
New pins against Amend 1 (read in the file, lines 86-95 and 120-125):
- 2′ = pin 2 with `D : ℕ → ℝ` (binder moved after `E`), hypothesis `‖ℰ j b‖ ≤ p j * tailTD d W (u j) (D j) …`,
  conclusion `Σ c j * p j * (C * tailTD d W (u k) (D j) … + ((1-u j)/(1-u k))^2 * W^(-(D j)))`. Matches Amend 1 verbatim in mathematics;
  same `∃ C` before `∀ L` (uniform in `L, g, W, D, E, σ, k, u, c, p, ℰ`), same ranges `0 ≤ u 0`, monotone, `u k < 1`, `g² ≤ 1-u k`.
- 4′ = pin 4 with the good event at a level `D₁` separate from the conclusion level `D`. Matches Amend 1.
- Pins 2, 4 are proved as the corollaries `D_j ≡ D`, `D₁ = D` (lines 265-270, 405-407), as Amend 1 requires.
Statement verdicts: all six check-file pins identical; 2′, 4′ as amended. No hypothesis weakened or added.

## 3. Vacuity, hidden hypotheses, cycles
- No structure carries a hypothesis: all pins are plain `def … : Prop` used only as theorem conclusions; no new `Prop` is assumed.
- Target 4′: the good event `lemDecCalEPrec_good` (`LemDecCalEPrec.lean:670`) conjunct 1 is
  `STLK2 ≤ N^τ' * (Jst n u D * STtailTD …)`; `LemDecCalELip_Jsharp` (`LemDecCalELip.lean:925`) is `max 1 (sup' over a nonempty
  Finset of STLK2/T)`, so the stopping hypothesis `J♯ ≤ W^ε` is a genuine finite condition, not vacuous.
- Target 5 hypotheses: `SizeTendsto`, eventual `Bctl ≤ 1`, and the five pins `STLKU, STLocalEntryU, STAvgU, STLmaxU, GijGEXPTSwap`
  (other gates' pins, unproved upstream; allowed). The control `Jst n u D = W^D` does not use the conclusion: no circularity (F1 of the ticket).
- Target 6: `Admissible 𝔠 𝔡` is the merged structure of `Defs/Sizes.lean`; it is discharged at `sz0` by `sz0_admissible`.
- Dependencies: `stTailtoTail_holds`, `lemDecCalEPrec_prob`, `lemDecCalEPrec_tail_ge`, `LemDecCalELip_Jsharp_basic`,
  `LemDecCalELip_tail_pos`, `st5_prec_mono`, `st5_Bctl_le_one`, `norm_mE`, `lam_sq_mul_pow_ge`: all merged on `main` (module builds against them).
- External-hypothesis limit check: no new external hypothesis is introduced.

## 4. Compiled nonempty instances (file lines 529-783)
| target | instance | data | hypotheses left open |
|---|---|---|---|
| 1 | `pfStep5Alg_inst_tailAnti`, `_strict` | `sz0`, `n=0`, `u=1/16`, `D=1<48=D'`, `a` with `zdistInf = 1` (`pfStep5Alg_instA_dist`, by `decide`) | none |
| 2′ | `pfStep5Alg_inst_ugenSum'_zero`, `pfStep5Alg_inst_ugenSum'_extremal` | `d=3, L=4, g=1/64, W=32, E=0, σ=![true,false], k=3, u_j=j/48, c_j=1/48, p_j=D_j=j+1`; ℰ ≡ 0 and nonzero ℰ_j = p_j T | none |
| 2 | `pfStep5Alg_inst_ugenSum_zero` | same, `D = 1`, ℰ ≡ 0 (ticket's instance) | none |
| 3 | `pfStep5Alg_inst_riemann`, `_sum` | `u_j = 1-2^{-(j+1)}`, `k = 3`; first sum `= 7` | none |
| 4′ / 4 | `pfStep5Alg_inst_goodStop'` / `_goodStop` | `sz0`, `n=0`, `u=1/16`, `ε=1/4`, `τ'=1/100`, `D=1`, `D₁=55` / `D₁=D=1` | the sample events `hstop`, `hgood` (random, not deterministic) |
| 4′ (joint satisfiability) | `pfStep5Alg_inst_goodStop'_nonvac` (+ `_one`, `_55`) | `sz0`, given the five pins: ∃ n ω in both events | the five stochastic pins |
| 5 | `pfStep5Alg_inst_goodProb` | `sz0`, `E = STflowE z0`, `s≡0`, `t≡1/16`, `D=1`, `τ'=1/100`, `D₁=1`; `SizeTendsto`, `Bctl ≤ 1` discharged | the five stochastic pins (other gates) |
| 6 | `pfStep5Alg_inst_closure` | `sz0`, `Admissible (1/6) (1/10)` via `sz0_admissible`, `ε=1/50<1/40`, `C=6000` | none |
Every deterministic hypothesis is discharged by `norm_num`/merged lemmas; no `N = 0`, empty index, collapsed window or `False` premise.
All compile (section 5). Every endpoint theorem (1, 2′, 2, 3, 4′, 4, 5, 6) has an instance.

## 5. Build and axioms (audit worktree)
```
$ lake build RBM3D.Induction.PfStep5Alg 2>&1 | grep -E "PfStep5Alg|error|Build completed"; echo "exit $?"
✔ [3846/3846] Built RBM3D.Induction.PfStep5Alg (7.6s)
Build completed successfully (3846 jobs).
exit 0
```
(Warnings in the log are only in pre-existing merged files: `Defs/Tail.lean`, `Propagator/*`, `Step34Pins.lean`, `Loop/KLFinal.lean`; none in `PfStep5Alg`.)
```
$ lake env lean ax.lean     # `import RBM3D.Induction.PfStep5Alg`, one `#print axioms` per target and instance
RBM.Gauss.Sizes.pfStep5Alg_tailAnti: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.pfStep5Alg_ugenSum'' depends on axioms: [propext, Classical.choice, Quot.sound]
RBM.Gauss.Sizes.pfStep5Alg_ugenSum: [propext, Classical.choice, Quot.sound]
RBM.Gauss.Sizes.pfStep5Alg_riemann: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.pfStep5Alg_goodStop'' depends on axioms: [propext, Classical.choice, Quot.sound]
RBM.Gauss.Sizes.pfStep5Alg_goodStop: [propext, Classical.choice, Quot.sound]
RBM.Gauss.Sizes.pfStep5Alg_goodProb: [propext, Classical.choice, Quot.sound]
RBM.Gauss.Sizes.pfStep5Alg_closure: [propext, Classical.choice, Quot.sound]
RBM.Gauss.Sizes.pfStep5Alg_inst_tailAnti: [propext, Classical.choice, Quot.sound]
RBM.Gauss.Sizes.pfStep5Alg_inst_tailAnti_strict: [propext, Classical.choice, Quot.sound]
RBM.Gauss.Sizes.pfStep5Alg_instA_dist: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.pfStep5Alg_inst_ugenSum'_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.pfStep5Alg_inst_ugenSum'_extremal' depends on axioms: [propext, Classical.choice, Quot.sound]
RBM.Gauss.Sizes.pfStep5Alg_inst_ugenSum_zero: [propext, Classical.choice, Quot.sound]
RBM.Gauss.Sizes.pfStep5Alg_inst_riemann: [propext, Classical.choice, Quot.sound]
RBM.Gauss.Sizes.pfStep5Alg_inst_riemann_sum: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.pfStep5Alg_inst_goodStop'' depends on axioms: [propext, Classical.choice, Quot.sound]
RBM.Gauss.Sizes.pfStep5Alg_inst_goodStop: [propext, Classical.choice, Quot.sound]
RBM.Gauss.Sizes.pfStep5Alg_inst_goodProb: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.pfStep5Alg_inst_goodStop'_nonvac' depends on axioms: [propext, Classical.choice, Quot.sound]
RBM.Gauss.Sizes.pfStep5Alg_inst_goodStop_nonvac_one: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.pfStep5Alg_inst_goodStop'_nonvac_55' depends on axioms: [propext, Classical.choice, Quot.sound]
RBM.Gauss.Sizes.pfStep5Alg_inst_closure: [propext, Classical.choice, Quot.sound]
```
Unpinned helpers are `private` with prefix `pfStep5Alg_`; public instance names carry the file-stem prefix (§3 (E)).

## 6. Paper-delta coverage
Lean/paper differences and their candidates in the prove report (d): per-time application of `lem_dec_calE` at the realized control
(T2209a, targets 4′/4); left Riemann sums instead of time integrals (T2209b, target 3); time-dependent level `D_u` and the
sequence-level 2′ / two-level 4′ (T2209d, Amend 1, DECISIONS §70); explicit closure `ε < 𝔡/4`, `τ = 𝔠ε/2` (T2209e, target 6);
crude control `W^D` for the probability of the good event (T2209f, target 5). T2209c (squared-profile TailtoTail) is correctly
withdrawn here and belongs to S5-10a. Every statement difference is covered.

## 7. Verdicts
| target | verdict |
|---|---|
| 1 `pfStep5Alg_tailAnti` | PASS |
| 2′ `pfStep5Alg_ugenSum'` | PASS |
| 2 `pfStep5Alg_ugenSum` | PASS |
| 3 `pfStep5Alg_riemann` | PASS |
| 4′ `pfStep5Alg_goodStop'` | PASS |
| 4 `pfStep5Alg_goodStop` | PASS |
| 5 `pfStep5Alg_goodProb` | PASS |
| 6 `pfStep5Alg_closure` | PASS |
| 7 | not in scope (Amend 1: S5-10a) |
**Ticket verdict: PASS.** No dispatcher sign-off needed.

## 8. Observations (no RETURN)
1. Instances of 4′/4 keep the sample events at `ε = 1/4` as hypotheses; joint satisfiability is compiled only at the large
   `ε = D₁ + 6/100` (given the five pins). The events are random, not deterministic hypotheses, so this meets §4 step 2; it is
   stated openly in the prove report (d) 2.
2. Target 6 is `∀ᶠ n` with a large threshold (`W ≥ e^{439}` at `𝔡 = 1/10, ε = 1/50, C = 1`, prove report (a)); a consumer
   must not instantiate it at a finite `n`.
3. `RBM3D.lean` does not import the new module on the branch (hub adds it at merge, then the full `lake build`).
