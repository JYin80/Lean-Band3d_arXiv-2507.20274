Auditor model: claude-opus-5-5
# T2043 audit (round 1): KL7a, `RBM3D/Loop/KLSumZero.lean` at `629f1f3`

Worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2043-audit1` (detached at `t/T2043` = `629f1f3`), started Sat Oct 3 08:44 UTC 2026.
Scratch: `scratchpad/T2043/audit/` (`ax.lean`, `precheck.lean`, `sdiff.py`, `SZ2.lean` = RBM2D `Loop/SumZero.lean` at `c9a24cf`).

## 1. Build, axioms, hygiene, diff scope

```
$ lake build RBM3D.Loop.KLSumZero 2>&1 | grep -E "error|warning|Build|sorry"
Build completed successfully (3237 jobs).        # olean timestamp 01:44 local = 08:44 UTC, rebuilt here
$ lake build RBM3D 2>&1 | grep -E "error|Build" | tail -3
Build completed successfully (3741 jobs).
$ lake env lean precheck.lean   # import RBM3D; import RBM3D.Loop.KLSumZero; #assert_rbm_axioms
lean exit: 0
axiom audit: 1476 theorems, 542 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded). All within [propext,  Classical.choice,  Quot.sound]
$ lake env lean ax.lean   (#print axioms, all identical)
sum_out treeZ_peel treeZ_eq sum_selfW SumZero_sum_Theta_col sum_Theta_sub_one_col sum_Theta_sub_one_row
SumZero_sum_Kpi_eq sum_SigmaPi sum_Kpi_closed SumZero_SigmaPi_add_const SumZero_sum_slice gapK_le_norm
SumZero_sum_slice_alt SigmaPi_alt_sumZero_le_of_Qlayer_one KLSumZero_inst_Kpi_closed KLSumZero_inst_bound
KLSumZero_inst_slice_alt KLSumZero_inst_Qlayer_one : depends on axioms: [propext, Classical.choice, Quot.sound]
$ grep -nE 'sorry|admit|native_decide|^\s*axiom|set_option|opaque|implemented_by|extern' RBM3D/Loop/KLSumZero.lean
45:set_option linter.style.longLine false
$ grep -nE ': Prop|structure|class ' RBM3D/Loop/KLSumZero.lean ; grep -n '^import' RBM3D/Loop/KLSumZero.lean
6:import RBM3D.Loop.KLTree
$ git diff --name-only main...t/T2043 ; git diff main...t/T2043 -- RBM3D.lean RBM3D/Test/Axioms.lean | wc -l
RBM3D/Loop/KLSumZero.lean
       0
```
Only the sole writable file; no merged file or frozen signature touched; imports only merged `KLTree` (no cycle).
Name clashes: each of the 20 ported names grepped as a declaration on `main` and on every other `t/T20*` branch: 0 hits.

## 2. Statements (script diff against RBM2D `c9a24cf` after the ticket's renaming)

```
$ python3 sdiff.py SZ2.lean RBM3D/Loop/KLSumZero.lean <names>    # renaming Z2 L→Zd d L, L^2→L^d, Kpi/SigmaPi/Theta/TSPlong/sigAlt/mSig/etaT→KL…/Gauss.etaT
SAME SumZero_sum_Kpi_eq   SAME sum_Kpi_closed   SAME SumZero_SigmaPi_add_const   SAME Qlayer   SAME edgeR   SAME Alayer (signature)
DIFF treeZ_eq / sum_selfW / SumZero_sum_slice_alt / SigmaPi_alt_sumZero_le_of_Qlayer_one: bound-variable names only (d→J, d→δ)
DIFF sum_SigmaPi
  2D> ... ∑ δ : Fin n → Zd d L, KLSigmaPi d L g m t σ π δ = (L : ℂ) ^ d * Qlayer m t σ π
  3D> ... ∑ δ : Fin n → Zd d L, KLSigmaPi d L g m t σ π δ = (L : ℂ) ^ d * ((∏ i, m (σ i)) * Qlayer m t σ π)
DIFF SumZero_sum_slice
  2D> ... KLSigmaPi d L g m t σ π δ = Qlayer m t σ π
  3D> ... KLSigmaPi d L g m t σ π δ = (∏ j, m (σ j)) * Qlayer m t σ π
$ #print RBM.Loop.Alayer
fun {n} [NeZero n] m t σ π => (∏ i, m (σ i)) * ((∏ v, (1 - ↑t * (m (σ v) * m (σ (v + 1))))⁻¹) * Qlayer m t σ π)
   (RBM2D body: (∏ v, (1 - (t : ℂ) * (m (σ v) * m (σ (v + 1))))⁻¹) * Qlayer m t σ π)
```
Endpoint signatures as elaborated (`#check`):
```
@sum_Kpi_closed : ∀ {n} [NeZero n] (d L : ℕ) [NeZero L] (g : ℝ) (m : Bool → ℂ) {t : ℝ},
  (∀ s s', ‖↑t * (m s * m s')‖ < 1) → 3 ≤ L → ∀ σ π, ∑ a, KLKpi d L g m t σ a π = ↑L ^ d * Alayer m t σ π
SigmaPi_alt_sumZero_le_of_Qlayer_one : ∀ (d : ℕ) (g κ : ℝ), 0 < κ → ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ E, |E| ≤ 2 - κ →
  ∀ t ∈ Set.Ico 0 1, ∀ (n : ℕ) [NeZero n] (hn : 4 ≤ n), Even n → Qlayer (mSigma E) 1 (KLsigAlt n) ∅ = 0 →
  ∀ d₁ : Zd d L, ‖∑ δ with δ ⟨0, ⋯⟩ = d₁, KLSigmaPi d L g (mSigma E) t (KLsigAlt n) ∅ δ‖ ≤
    2 ^ n ^ 2 * ↑n * (gapK κ)⁻¹ ^ n * (2 / √(κ * (4 - κ))) * Gauss.etaT E t
@gapK_le_norm : 0 < κ → |E| ≤ 2 - κ → 0 ≤ t → ∀ s, gapK κ ≤ ‖1 - ↑t * (mSigma E s * mSigma E s)‖
def gapK := fun κ => min 1 √(κ * (4 - κ) / 2)                      (= RBM2D Kcal.lean:311, d-free)
```
Renamed objects checked equal: `KLsigAlt` (KLTree.lean:345) = RBM2D `sigAlt` (Kcal:372) textually; `mSigma` (Semicircle:85) = RBM2D `mSig` (Kcal:159);
`Gauss.etaT E t = (1 - t) * (mE E).im` (GLoop.lean:75) = RBM2D `etaT E t = (spectralZ E t).im`, `spectralZ_im : = (1 - u) * (spectralM E).im`.

Source of the `∏ m` differences (verified):
```
RBM3D KLTree.lean:353  KLKpi … := (∏ i, m (σ i)) * ∑ F ∈ KLTSPlong n σ π, KLtreeValG d L g m t σ a F
RBM3D KLTree.lean:368  KLSigmaPi … := (∏ i, m (σ i)) * ∑ F ∈ KLTSPlong n σ π, …
paper A_deterministic_estimates.tex:357  \Gamma^{(n)}_{t,\bsig,\ba} := \p{\prod_{i=1}^n m(\sig_i)} \cdot \sum_{\mathbf b} \prod_{e} f_{t,\bsig}\p{e}
paper A:611  \cK^{\p{\pi}}\p{t,\bsig,\ba} := \sum_{\Gamma \in \TSP(...)} \Gamma^{\p{n}}_{M;t,\bsig,\ba}
```
The merged (frozen) `KLKpi`/`KLSigmaPi` carry the paper's `∏ m(σ_i)`, RBM2D's do not; the RBM2D form of `sum_Kpi_closed` is false
for the merged `KLKpi` (`KLSumZero_neg_Kpi_closed_2Dform`, compiled: pure triangle, `-8i ≠ 8`). So the three changes
(R1 `Alayer` body, R2 `sum_SigmaPi`/`SumZero_sum_slice` right sides) are forced and agree with the paper.
`SumZero_sum_slice_alt` and the endpoint bound keep RBM2D's statement because `∏ m(σ^alt_i) = 1` (n even, `‖m‖ = 1`,
private `KLSumZero_prod_mSigma_alt` :687); this is why `Even n` is now used (RBM2D: hypothesis present, unused).

Against the ticket's mathematics:
- `sum_Kpi_closed`: `∑_a K^{(π)} = L^d · A(σ,π)` as pinned; `L^d` is the volume (`L² → L^d`); `3 ≤ L` and `‖ξ‖ < 1` as RBM2D; `d`, `g` free. Correct.
- `SigmaPi_alt_sumZero_le_of_Qlayer_one`: quantifier order, `4 ≤ n`, `Even n`, `|E| ≤ 2-κ`, `t ∈ [0,1)`, `Q(1) = 0`, constant `2^{n²} n gapK^{-n} (2/√(κ(4-κ)))` identical to RBM2D :802.
  The ticket's "`W²η_t → W^dη_t`" does not apply: RBM2D :802 ends in `etaT E t` (no `W`), and the paper's `(eq:Sigma-empty-sum-zero)` (A:731) is `O(|1-t|)`. Observation, not a defect.
- This target is a **conditional adapter** (`Q(σ^alt,∅)(1) = 0` assumed), not the general first estimate of `(eq:Sigma-empty-sum-zero)`; the ticket pins it as such ("the conditional sum-zero bound"), and the prove report (d) says so. It does not pass for the general statement (KL7c's job).
- Coverage: all 18 public RBM2D declarations + `gapK` present under RBM2D names; `gapK_le_norm` made public (private in RBM2D). Nothing reused from merged files is copied (KLTree API used).

## 3. Hidden hypotheses, vacuity, cycles
No `structure`/`class`/`Prop` definition in the file (grep above); every hypothesis is in the signature (`hm`, `hL`, `hκ`, `hE`, `t ∈ Ico`, `hn`, `Even n`, `Q(1)=0`).
No external hypothesis (`norm_SB`, `Theta_*_of_three_le` are merged theorems), so no limit check is needed. Only import: `RBM3D.Loop.KLTree` (merged).
The only non-deterministic-looking hypothesis `Q(1)=0` is discharged at the instance (below), so the bound is not vacuous.

## 4. Compiled nonempty instances (same file, all in the 3741-job build above, axioms as in §1)
```
KLSumZero.lean:933 theorem KLSumZero_inst_Kpi_closed :
    ∑ a : Fin 4 → Zd 3 3, KLKpi 3 3 (1 / 2) (mSigma 0) (1 / 2) (KLsigAlt 4) a ∅ = (3 : ℂ) ^ 3 * Alayer (mSigma 0) (1 / 2) (KLsigAlt 4) ∅
KLSumZero.lean:955 theorem KLSumZero_inst_Kpi_closed_val : … = 144          (chk_Alayer :940: A = 16/3; 27·16/3 = 144)
KLSumZero.lean:881 theorem KLSumZero_inst_Qlayer_one : Qlayer (mSigma 0) 1 (KLsigAlt 4) ∅ = 0
KLSumZero.lean:900 theorem KLSumZero_inst_bound (d₁ : Zd 3 3) : ‖∑ δ ∈ … δ ⟨0, _⟩ = d₁, KLSigmaPi 3 3 (1/2) (mSigma 0) (1/2) (KLsigAlt 4) ∅ δ‖
      ≤ 2 ^ (4 ^ 2) * ((4 : ℕ) : ℝ) * (gapK 1)⁻¹ ^ 4 * (2 / Real.sqrt (1 * (4 - 1))) * Gauss.etaT 0 (1 / 2) :=
  SigmaPi_alt_sumZero_le_of_Qlayer_one 3 (1 / 2) 1 one_pos 3 le_rfl 0 (by norm_num) (1 / 2)
    ⟨by norm_num, by norm_num⟩ 4 le_rfl (by decide) KLSumZero_inst_Qlayer_one d₁
KLSumZero.lean:891 theorem KLSumZero_inst_slice_alt (d₁ : Zd 3 3) : … = 1 / 3          (RBM2D Check 1 in d = 3)
```
Data: `d = 3, L = 3, n = 4, E = 0, t = 1/2, κ = 1, g = 1/2`, as the ticket requires; every deterministic hypothesis
(`3 ≤ L`, `0 < κ`, `|0| ≤ 1`, `1/2 ∈ [0,1)`, `4 ≤ 4`, `Even 4`, `Q(1) = 0`, `‖ξ‖ < 1` via `chk_hm`) is discharged; no hypothesis is left
on the instances. Not degenerate: 27 sites, `n = 4`, `t` interior, slice value `1/3 ≠ 0`, `KLTSPlong 4 σ^alt ∅ = {∅, {(0,2)}, {(1,3)}}` (`chk_TSPlong_four`).
One further instance for every other public statement (`inst_Kpi_eq`, `inst_sum_SigmaPi` = 9, `inst_slice`, `inst_add_const`, `inst_treeZ_eq`, `inst_treeZ_peel`,
`inst_sum_selfW`, `inst_col`, `inst_Theta_sums`, `inst_gap`, `inst_sum_out`). PASS.

## 5. Paper deltas
- R1/R2 (`∏ m`): Lean agrees with the paper (A:357, A:611); difference is RBM2D→RBM3D only. No paper delta needed.
- Explicit constant and bulk `|E| ≤ 2-κ` of the bound: RBM2D T2004a-11 type; the ticket says cite, do not re-propose; report (d) cites. Covered.
- Conditional form (`Q(1) = 0`, `n ≥ 4` even): an intermediate lemma pinned conditional by the ticket, stated as such in report (d); the paper-level
  statement `(eq:Sigma-empty-sum-zero)` is not claimed here. No delta needed now; KL7c must carry any delta for the general statement.

## 6. Observations (no RBM3D statement, instance, build, axiom or delta affected)
- O1. Ticket line "`W^2 η_t → W^d η_t`" is inapplicable (no `W` in RBM2D :802 or in the paper's estimate); the port correctly has none.
- O2. `RBM.Loop.KLSigmaPi.congr_simp` is a public tactic-generated name; KL7b/KL7c may regenerate it (prover reports a scratch test with no clash).
- O3. Downstream: `Alayer` now includes `∏ m(σ_i)`; RBM2D `Alayer_cut` (SumZeroWard) will need its prefactor adapted in KL7c.

## 7. Verdict
Targets `sum_Kpi_closed`, `SigmaPi_alt_sumZero_le_of_Qlayer_one` and the other ported declarations: **PASS** on statement
(correct w.r.t. the paper and the merged definitions), non-vacuity, compiled instances, build and axioms.
**Needs dispatcher sign-off**: the ticket says "If a ported statement must change beyond the renaming and the exponents, stop and
report". Three ported items changed beyond renaming (R1 `Alayer` body; R2 `sum_SigmaPi`, `SumZero_sum_slice` gain `∏_i m(σ_i)`).
The change is forced by the frozen `KLKpi`/`KLSigmaPi` (RBM2D's form is provably false here) and is the paper's, but the
ticket reserved this decision for the dispatcher; the prover proceeded instead of stopping. No repair is requested; the
dispatcher only needs to accept R1/R2 (and note O3 for KL7c).
