Prover model: claude-sonnet-5-5

## (a) Math preflight — Sat Oct 10 22:25:05 UTC 2026

Data fixed throughout: `d ≥ 3`, `Λ > 0`, `κ > 0`; family index `i = (L, g, E, m, t)` with `3 ≤ L`, `0 < g ≤ Λ`, `BAReal d L g κ E m`, `0 ≤ t < 1`
(`KWardIneq_Data d Λ κ`, `BA/KWardIneq.lean:141`). `B = Bparam d L g t 0 = (g²+|1-t|)⁻¹ + (L^d |1-t|)⁻¹` (`Defs/Params.lean:36`, `K = 0`).

### (i) Exponent table

Step at `n ≥ 3`, `π ≠ ∅`, innermost `J ∈ π` (`KLArcLe e J → e = J`), `w = KLwIn J = J.2 - J.1`. BA cut `baKpi_cut_abs` (`BA/KInduct.lean:734`):
`K^{(π)}_n = Σ_u t · A(u) · K^{(π')}_{n''}(u)`, `A(u)` = the `IndStepAbs` summand on the inner polygon (`k = w+1` vertices, root `Fin.last`).
No `S^{(B)}`, no `ξ_J`: the prefactor is the real `t`, and `u` is summed once (the band had `Σ_{u,w} ξ S_{uw}`, `Loop/KLInduct.lean:958`).

| quantity | value | constraint | slack |
|---|---|---|---|
| `w` | `2 ≤ w ≤ n-2` | `IsDiag n i j` (`j ≠ i+1`, not `(0,n-1)`, `Loop/Partition.lean:65`) | exact range; `n ≥ 4` is forced when `π ≠ ∅` |
| inner `k = w+1` | `3 ≤ k ≤ n-1` | inner `IndStepAbs` at `k ≥ 3`, strong induction needs `k < n` for the hypothesis list | 0 at both ends |
| outer `n'' = n-w+1` | `3 ≤ n'' ≤ n-1` | outer induction hypothesis needs `3 ≤ n'' < n` | 0 at both ends |
| exponent of `B` | `(k-2)+(n''-1) = (w-1)+(n-w) = n-1` | must equal `n-1` | exactly 0 (checked, 282912 triples, script below) |
| loss `L^τ` | `L^{τ/2} L^{τ/2} = L^τ` | inner at `τ/2`, outer at `τ/2`; `L ≥ 3 > 0` for `rpow_add` | exactly 0 |
| `‖t‖` | `≤ 1` | `0 ≤ t < 1` | `1 - t`; no `(1-t)` loss is spent in the step |
| step constant | `C(n,τ) = C₀ + Σ_{w<n} Ci(w+1)·Co(n-w+1)` | `Ci(k)` from `IndStepAbs` at `(k, τ/2)`, `Co(k)` from the hypothesis at `(k, τ/2)`, `C₀` from the layer `∅` | depends on `(d, n, Λ, κ, τ)` only (C1) |
| `B ≥ (1+Λ²)⁻¹` | `(g²+|1-t|)⁻¹ ≤ B` (`KLlat_inv_le_Bparam`, `Loop/KLIndStepA.lean:116`) | `g² + |1-t| ≤ Λ²+1` as `g ≤ Λ`, `t ∈ [0,1)` | grid min of `(1+Λ²)B` is 1.000808 ≥ 1 (script) |
| D3, all leaves short (`σ_v = σ_{v+1}` for all `v`) | `‖K^{(∅)}‖ ≤ C_Σ S^n ≤ C_Σ S^n (1+Λ²)^{n-1} B^{n-1}` | `C_Σ` from `baWardMol_holds` (K07 decay, `exp ≤ 1`); `S` from property 5' (`BAProp5s`) | `B^{n-1}` exponent exact; loss `L^τ ≥ 1` unused |
| D3, some leaf long (root `r`, `σ_r ≠ σ_{r+1}`) | `‖Θ_r‖_sup ≤ C_d B` (property 5 + translation) times root sum `≤ C_i L^τ B^{n-2}` | `1 + (n-2) = n-1` | exactly 0 |
| `IndStepTH` bridge, loss | `BAProp6/7/8` (no loss) `≤` `IndStepTH` fields with `L^τ` | `1 ≤ L^τ` for `L ≥ 3`, `τ > 0` | factor `L^τ ≥ 3^τ > 1` |
| `IndStepTH` window | `c = 1/2` | `BAProp6/7 d Λ κ (1/2)`: `0 < 1/2 < 1`; `|r| ≤ (1/2)|a|` is the field's window verbatim | exact |
| `IndStepTH.rowSum` | `Σ_b ‖Θ^{(s,s')}(a,b)‖ ≤ (1-t)⁻¹`, `s ≠ s'` | right resolvent identity `Θ = 1 + tΘQ` and `Σ_b |M^{(s,s')}_{cb}| = Σ_b K_{cb} = 1` | the complex row sum of `Θ^{(+,-)}` equals `(1-t)⁻¹` (`BATheta_row_sum_pm`, `BA/KBase.lean:381`) |

Findings that change the target list (mathematics only):

* **F1 (a fourth hypothesis of the abstract step).** The band step uses `KLKpi_cut` only when some tree `F₀` has `KLFlong F₀ σ = π`; otherwise it uses
  `K^{(π)} = 0` (`Loop/KLInduct.lean`, the `hemp` branch of `KLKpi_step`). With `Kp` abstract this needs the hypothesis
  `KLTSPlong n σ π = ∅ → Kp i n σ a π = 0` (BA: `BAKpi` is the sum over `KLTSPlong n σ π`, `BA/KMolecule.lean:53-55`). The ticket lists three.
* **F2 (the leaf bundle).** `indStepAbs_of` (`Loop/KLIndStepB.lean:879`) takes `hTH : IndStepTH d L g t TH` (`Loop/KLIndStepA.lean:1058`) besides
  `hD` (K07 `baSig_decay`) and `hS` (K08b `baSig_sumZeroAbs`). `KPure.lean:1001` leaves it as a hypothesis ("K12"). The mathematics for it is merged:
  `baProp5to8_holds` (`BA/Prop6Path.lean:1049`) gives fields `decay, short, diffOne, diffTwo, zeroMode` (`BAThetaOf (BAMsigma ..) = BATheta` by `rfl`, `BATheta0` is the
  zero-mode expression of `IndStepTH.zeroMode` by unfolding, `BA/MFixedPoint.lean:519`). Fields `transl` and `rowSum` have only private copies
  (`KInduct_theta_shift`, `KWardIneq_theta_row_le`), so they are re-proved in `KStep.lean`. Without `hTH`, target 3 would be conditional, not the stated unconditional theorem.
* **F3 (Ward is not an input of the step).** `KLInduct.lean` contains no `KLWardIneq`; §7 (`KLKpi_step`, `:984`) uses `KLindStepPin_holds`, the cut and `KLInduct_Kpi_empty_bound` only.
  `baWardIneq_holds` (`BA/KWardIneq.lean:1183`) has the premise `∀ k ∈ [3,n], KWardIneq_IndAt d k Λ κ`; it is a consumer. `KWardIneq_IndAt_of_abs`
  (`:376`) turns the `IndStepAbs` of the step into that premise, so K09b's `IndStepAbs` at family `KWardIneq_Data` also discharges it (K12). No Ward input enters `baKpiBoundAt_holds`.
* **F4 (the step needs no private band helper).** The band's `KLInduct_norm_sum_SB_mul_le`, `KLInduct_norm_cut_le` (`:948, :958`) bound `Σ_{u,w} ξ A(u) S_{uw} B(w)`; at BA the cut has
  one sum, `‖Σ_u t A(u) K(u)‖ ≤ |t| (Σ_u ‖A(u)‖) sup_u ‖K(u)‖` (triangle inequality). The merged private helpers of §7 are not needed; the in-place fallback is not triggered.
* **F5 (D3 is not a one-line reduction).** `‖K^{(∅)}‖ ≤ C_Σ S^n` with `S` the `ℓ¹` row norm of a leaf: short leaves have `S = O(1)` (`BAProp5s`), but a long leaf has `ℓ¹` norm `≤ (1-t)⁻¹` only
  (`IndStepTH.rowSum`), and `(1-t)⁻¹ ≥ B`-scale can exceed `B` by the factor `(g²+|1-t|)/(1-t)`, so `S^n` with long leaves is not `≲ B^{n-1}` uniformly in `g, t`. D3 follows the band proof `KLInduct_Kpi_empty_bound` (`:833`): case all-short as above; otherwise sup norm of
  one long leaf `C_d B` times the root sum (`IndStepAbs` at `k = n`).
* **F6 (target 5 as written is degenerate).** `σ = KLsigAlt 4 = (+,-,+,-)` has both chords `(0,2)`, `(1,3)` short, so every layer `π ≠ ∅` has no tree and `K^{(π)} = 0`
  (script, line 2 of the output). The nondegenerate instance below uses `σ = (+,+,-,+)`, `π = {(0,2)}` (the cut, `n = 4`, inner `k = 3`, outer `n'' = 3`) and `σ = KLsigAlt 4`, `π = ∅` (3 trees).

### (ii) One concrete nondegenerate instance

`d = 3`, `L = 4`, `Λ = 10`, `κ = Im m₀ > 0`, `(g, E, m) = (P.g0, P.E, P.m0)` the flow point of `(L, g) = (4, 10)` (`BA/MFixedPoint.lean:893`: `0 < P.g0 ≤ 10`, `P.real : BAReal 3 4 P.g0 (Im m₀) P.E P.m₀`),
`t = 1/2`, `τ = 1`, `n = 4`. Every hypothesis of targets 1-3 at this data:

| hypothesis | at the instance |
|---|---|
| `3 ≤ d`, `0 < Λ`, `0 < κ`, `3 ≤ n` | `3 ≤ 3`, `10 > 0`, `Im m₀ > 0`, `3 ≤ 4` |
| `3 ≤ L`, `0 < g ≤ Λ`, `BAReal`, `0 ≤ t < 1` | `4`, `P.g0 ∈ (0,10]`, `P.real`, `1/2` |
| cut hypotheses `F₀ ∈ TSP 4`, `KLFlong F₀ σ = π`, `J ∈ π`, innermost | `F₀ = {(0,2)}`, `σ = (+,+,-,+)`, `π = {(0,2)}`, `J = (0,2)`, `w = 2` |
| inner / outer sizes (hypothesis list of the step) | `k = 3 ∈ [3,3]`, `n'' = 3 ∈ [3,3]`: induction hypothesis at `n'' = 3` is the base case of the strong induction |
| `IndStepAbs` at `k = 3, 4` | `indStepAbs_of` with `baSig_decay` (`BA/KPure.lean:632`), `baSig_sumZeroAbs` (`BA/KSumZeroB.lean:610`, needs `3 ≤ n`, `t < 1`: `3 ≤ 4`, `1/2 < 1`), `hTH` from F2 |
| root long (`σ_r ≠ σ_{r+1}`) | `σin_last = σ_2 = -`, `σin_0 = σ_0 = +` |
| external hypothesis | none: every hypothesis is a merged theorem or an internal pin; no DECISIONS-authorised external input is used, so no limit computation applies |

`g0 = P.g0` is an existential witness (`FlowPt` field), so the script uses `g = 7.5` as a stand-in only for the numeric lines; the structural lines do not depend on `g`.

Command (script in the scratchpad, `python3 -I`; enumerates `TSP n` as `CrossingFree` subsets of `diagonals n`, `KLFlong`, innermost `J`, per `Loop/Partition.lean:65-92`, `Loop/KLTree.lean:50, 336`):

```
python3 -I /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/60e5425b-ae97-4201-b2dc-fc981af93073/scratchpad/T2396/inst.py
TSP(4) = [[], [(0, 2)], [(1, 3)]]
n=4 sigma KLsigAlt 4 layers (pi -> #trees): {(): 3}
n=4 sigma (+,+,-,+) layers (pi -> #trees): {(): 2, ((0, 2),): 1}
cut triples checked (n=4..8): 282912 violations of 3<=k<n, 3<=n''<n, (k-2)+(n''-1)=n-1, root long: 0
min over grid of (1+Lam^2)*B_{t,0} = 1.000808 >= 1: True
L^(tau/2)*L^(tau/2) = 4.0 = L^tau = 4.0
instance L=4,g=7.5(placeholder for P.g0 in (0,10]),t=1/2: B_{t,0} = 0.04887114537444934 (1+Lam^2)^-1 = 0.009900990099009901 B^(n-1),n=4: 0.00011672329870935422
```

Reading: the layer `{(0,2)}` of `σ = (+,+,-,+)` has one tree, the inner triangle and the outer triangle (`k = n'' = 3`); layers `∅` have 2 resp. 3 trees. The instance is not collapsed:
`TSP 4` is nonempty, the layer `π ≠ ∅` has a tree, the window `2 ≤ w ≤ n-2` is the single value `w = 2`.

### Plan items (iii)-(v) and registry

* (iii) D3 resolved by the band route (F5), constants uniform in `(L, g ≤ Λ, BAReal, t)`: inputs `baWardMol_holds` (`KWardIneq.lean:363`), `BAProp5`, `BAProp5s`, `IndStepAbs`, `(1+Λ²)⁻¹ ≤ B`, `baKpi_empty_slice`, `baKpi_empty_short` (`BA/KInduct.lean:758, 776`).
* (iv) above. (v) omitted: section (a) carries no size estimates (CLAUDE.md §4 step 1).
* Target 6: `BAKpiBoundAt`, `BAKBoundAt`, `KWardIneq_IndAt` do not occur in `RBM3D/Test/Axioms.lean` (`grep` exit 1): no registry change.

### Verdicts

* Target 1 (abstract step): **PASS**, with the extra hypothesis F1 (`KLTSPlong n σ π = ∅ → Kp = 0`) and `Sig`, `Kp` polymorphic in the polygon size `k` (the cut changes `n` to `k = w+1` and `n''`).
* Target 2 (D3): **PASS** (band route, F5); no one-line reduction exists.
* Target 3 (`baKpiBoundAt_holds`): **PASS**, scope includes the `IndStepTH` bridge (F2); Ward is not an input (F3).
* Target 4 (C1): **PASS**, constants in `(d, n, Λ, κ, τ)` only (table row `C(n,τ)`).
* Target 5 (instances): **PASS** with the corrected data of F6 (`σ = (+,+,-,+)`, `π = {(0,2)}`, plus `σ = KLsigAlt 4`, `π = ∅`); `σ = KLsigAlt 4` with `π ≠ ∅` is vacuous.
* Target 6 (registry): **PASS** (no change needed).

## (b) Script output — Sat Oct 10 22:41:40 UTC 2026
```
$ wc -l RBM3D/BA/KStep.lean            # against the stop line 1,300 (ticket estimate 450/650/950)
     746 RBM3D/BA/KStep.lean
$ lake build RBM3D.BA.KStep (error-line count, last line); git log --oneline -4
0
Build completed successfully (3776 jobs).
27b48e4 T2396: BA/KStep section 6, compiled instances; import in RBM3D.lean
d4054ca T2396: BA/KStep sections 4-5, D3 baKpi_empty_bound and baKpiBoundAt_holds
1e2871d T2396: BA/KStep sections 2-3, Theta calculus copies, IndStepTH bundle, baIndStepAbs_holds
34f1d3d T2396: BA/KStep section 1, the abstract induction step (kStep_step, kStep_all)
$ lake build   (full; RBM3D.lean carries the import line RBM3D.BA.KStep, line 438)
build exit status 0; error lines: 0
info: RBM3D.lean:441:0: axiom audit: 11239 theorems, 3377 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
Build completed successfully (4209 jobs).
$ #print axioms (ax2.lean)
KStep_step: [propext, Classical.choice, Quot.sound]
KStep_all: [propext, Classical.choice, Quot.sound]
KStep_baIndStepAbs_holds: [propext, Classical.choice, Quot.sound]
baKpi_empty_bound: [propext, Classical.choice, Quot.sound]
baKpiBoundAt_holds: [propext, Classical.choice, Quot.sound]
$ lake env lean docs/tickets/checks/T2396-check.lean   (main worktree file, run in the branch worktree)
exit 0; error lines: 0; output lines: 113
$ #check of the 26 Mathlib names used (chk.lean)
exit 0; error lines: 0
$ grep -n "sorry\|admit\|native_decide\|^axiom" KStep.lean
exit 1 (no match)
$ name-clash grep: files other than KStep.lean containing each new public name (KStepAt KStep_step KStep_all KStep_baIndStepAbs_holds baKpi_empty_bound baKpiBoundAt_holds KStepInst)
total over main worktree and branch: 0
$ grep -n "BAKpiBoundAt\|BAKBoundAt\|KWardIneq_IndAt\|KStep" RBM3D/Test/Axioms.lean; grep -c KLWardIneq RBM3D/Loop/KLInduct.lean
exit 1 (registry: no line, no change)
0
$ git diff --stat main...t/T2396; import cone of KStep (cone.py): module count, LWExpCert*/Loop.KLInduct members
 RBM3D.lean          |   1 +
 RBM3D/BA/KStep.lean | 746 ++++++++++++++++++++++++++++++++++++++++++++++++++++
 2 files changed, 747 insertions(+)
103 [] 
$ port from RBM1D/RBM2D: none (the step is adapted from RBM3D Loop/KLInduct.lean:833-1131; the Theta copies from the private lemmas of BA/KInduct.lean, BA/KWardIneq.lean)
$ stmt2.py KStep.lean <targets>   (declaration heads, whitespace folded at 250 columns; line numbers in brackets)
[76] theorem KStep_step {ι : Type} (d : ℕ) (L : ι → ℕ) [∀ i, NeZero (L i)] (Bp t : ι → ℝ) (Sig : ∀ (k : ℕ) [NeZero k] (i : ι), (Fin k → Bool) → (Fin k → Zd d (L i)) → ℂ) (TH : ∀ i, Bool → Bool → Matrix (Zd d (L i)) (Zd d (L i)) ℂ) (Kp : ∀ (k : ℕ)
  [NeZero k] (i : ι), (Fin k → Bool) → (Fin k → Zd d (L i)) → Finset (Fin k × Fin k) → ℂ) (n : ℕ) [NeZero n] (hn : 3 ≤ n) (hBp : ∀ i, 0 ≤ Bp i) (ht : ∀ i, ‖((t i : ℝ) : ℂ)‖ ≤ 1) (hempty : ∀ τ : ℝ, 0 < τ → ∃ C : ℝ, 0 < C ∧ ∀ (i : ι) (σ : Fin n → Bool)
  (a : Fin n → Zd d (L i)), ‖Kp n i σ a ∅‖ ≤ C * (L i : ℝ) ^ τ * (Bp i) ^ (n - 1)) (hzero : ∀ (i : ι) (σ : Fin n → Bool) (π : Finset (Fin n × Fin n)) (a : Fin n → Zd d (L i)), KLTSPlong n σ π = ∅ → Kp n i σ a π = 0) (hcut : ∀ (i : ι) (σ : Fin n →
  Bool) {F₀ : Finset (Fin n × Fin n)}, F₀ ∈ TSP n → ∀ {π : Finset (Fin n × Fin n)}, KLFlong F₀ σ = π → ∀ {J : Fin n × Fin n}, J ∈ π → (∀ e ∈ π, KLArcLe e J → e = J) → ∀ a : Fin n → Zd d (L i), Kp n i σ a π = ∑ u : Zd d (L i), (t i : ℂ) * (∑ δ ∈
  Finset.univ.filter (fun δ : Fin (KLwIn J + 1) → Zd d (L i) => δ (Fin.last _) = u), Sig (KLwIn J + 1) i (sigmaIn σ J) δ * ∏ k ∈ Finset.univ.erase (Fin.last (KLwIn J)), TH i (sigmaIn σ J k) (sigmaIn σ J (k + 1)) (a (BAinVinv J k)) (δ k)) * Kp (n -
  KLwIn J + 1) i (sigmaOut σ J) (BAdeltaOut J a u) ((π.erase J).image (KLshiftOut J))) (hind : ∀ (k : ℕ) [NeZero k], 3 ≤ k → k < n → IndStepAbs d k L Bp (Sig k) TH) (hout : ∀ (k : ℕ) [NeZero k], 3 ≤ k → k < n → KStepAt d L Bp Kp k) : KStepAt d L Bp
  Kp n
[212] theorem KStep_all {ι : Type} (d : ℕ) (L : ι → ℕ) [∀ i, NeZero (L i)] (Bp t : ι → ℝ) (Sig : ∀ (k : ℕ) [NeZero k] (i : ι), (Fin k → Bool) → (Fin k → Zd d (L i)) → ℂ) (TH : ∀ i, Bool → Bool → Matrix (Zd d (L i)) (Zd d (L i)) ℂ) (Kp : ∀ (k : ℕ)
  [NeZero k] (i : ι), (Fin k → Bool) → (Fin k → Zd d (L i)) → Finset (Fin k × Fin k) → ℂ) (hBp : ∀ i, 0 ≤ Bp i) (ht : ∀ i, ‖((t i : ℝ) : ℂ)‖ ≤ 1) (hempty : ∀ (n : ℕ) [NeZero n], 3 ≤ n → ∀ τ : ℝ, 0 < τ → ∃ C : ℝ, 0 < C ∧ ∀ (i : ι) (σ : Fin n → Bool)
  (a : Fin n → Zd d (L i)), ‖Kp n i σ a ∅‖ ≤ C * (L i : ℝ) ^ τ * (Bp i) ^ (n - 1)) (hzero : ∀ (n : ℕ) [NeZero n], 3 ≤ n → ∀ (i : ι) (σ : Fin n → Bool) (π : Finset (Fin n × Fin n)) (a : Fin n → Zd d (L i)), KLTSPlong n σ π = ∅ → Kp n i σ a π = 0)
  (hcut : ∀ (n : ℕ) [NeZero n], 3 ≤ n → ∀ (i : ι) (σ : Fin n → Bool) {F₀ : Finset (Fin n × Fin n)}, F₀ ∈ TSP n → ∀ {π : Finset (Fin n × Fin n)}, KLFlong F₀ σ = π → ∀ {J : Fin n × Fin n}, J ∈ π → (∀ e ∈ π, KLArcLe e J → e = J) → ∀ a : Fin n → Zd d (L
  i), Kp n i σ a π = ∑ u : Zd d (L i), (t i : ℂ) * (∑ δ ∈ Finset.univ.filter (fun δ : Fin (KLwIn J + 1) → Zd d (L i) => δ (Fin.last _) = u), Sig (KLwIn J + 1) i (sigmaIn σ J) δ * ∏ k ∈ Finset.univ.erase (Fin.last (KLwIn J)), TH i (sigmaIn σ J k)
  (sigmaIn σ J (k + 1)) (a (BAinVinv J k)) (δ k)) * Kp (n - KLwIn J + 1) i (sigmaOut σ J) (BAdeltaOut J a u) ((π.erase J).image (KLshiftOut J))) (hind : ∀ (k : ℕ) [NeZero k], 3 ≤ k → IndStepAbs d k L Bp (Sig k) TH) : ∀ (n : ℕ) [NeZero n], 3 ≤ n →
  KStepAt d L Bp Kp n
[442] theorem KStep_baIndStepAbs_holds {d : ℕ} (k : ℕ) [NeZero k] (hd : 3 ≤ d) (hk : 3 ≤ k) {Λ κ : ℝ} (hΛ : 0 < Λ) (hκ : 0 < κ) : IndStepAbs (ι := KWardIneq_Data d Λ κ) d k (fun i => i.L) (fun i => Bparam d i.L i.g i.t 0) (BASig (ι := KWardIneq_Data
  d Λ κ) d k (fun i => i.L) (fun i => i.g) (fun i => i.E) (fun i => i.m) (fun i => i.t)) (fun i s s' => BAThetaOf (BAMsigma d i.L (BAMB d i.L i.g (i.E : ℂ) i.m)) i.t s s')
[479] theorem baKpi_empty_bound {d : ℕ} (n : ℕ) [NeZero n] (hd : 3 ≤ d) (hn : 3 ≤ n) {Λ κ : ℝ} (hΛ : 0 < Λ) (hκ : 0 < κ) (τ : ℝ) (hτ : 0 < τ) : ∃ C : ℝ, 0 < C ∧ ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → g ≤ Λ → ∀ (E : ℝ) (m : ℂ), haveI : NeZero L :=
  ⟨by omega⟩ BAReal d L g κ E m → ∀ t : ℝ, 0 ≤ t → t < 1 → ∀ (σ : Fin n → Bool) (a : Fin n → Zd d L), ‖BAKpi d L n (BAMsigma d L (BAMB d L g (E : ℂ) m)) t σ a ∅‖ ≤ C * (L : ℝ) ^ τ * (Bparam d L g t 0) ^ (n - 1)
[597] theorem baKpiBoundAt_holds (d n : ℕ) [NeZero n] {Λ κ : ℝ} (hd : 3 ≤ d) (hn : 3 ≤ n) (hΛ : 0 < Λ) (hκ : 0 < κ) : BAKpiBoundAt d n Λ κ
$ inst2.py KStep.lean   (the compiled `example`s of module KStepInst, elaborated by the builds above; the key one: nonempty layer, one tree, n = 4)
10 examples, at lines: 630 634 644 654 666 676 685 694 709 740
644: example : (KLTSPlong 4 ![true, true, false, true] {((0 : Fin 4), (2 : Fin 4))}).Nonempty ∧ ∃ C : ℝ, 0 < C ∧
645:     ‖BAKpi 3 4 4 (BAMsigma 3 4 (BAMB 3 4 P.g0 (P.E : ℂ) P.m0)) (1 / 2) ![true, true, false, true]
646:         ![![0, 0, 0], ![1, 0, 0], ![2, 0, 0], ![3, 0, 0]] {((0 : Fin 4), (2 : Fin 4))}‖
647:       ≤ C * (4 : ℝ) ^ (1 : ℝ) * (Bparam 3 4 P.g0 (1 / 2) 0) ^ (4 - 1) := by
648:   refine ⟨⟨_, KStep_layer4⟩, ?_⟩
649:   obtain ⟨C, hC, H⟩ := baKpiBoundAt_holds 3 4 (Λ := 10) (κ := P.m0.im) le_rfl (by norm_num) (by norm_num)
650:     P.real.1.1 1 one_pos
651:   exact ⟨C, hC, H 4 (by norm_num) P.g0 P.g0_pos P.g0_le P.E P.m0 P.real (1 / 2) (by norm_num) (by norm_num) _ _ _⟩
```

Narrative (facts from the output above and the files):
* All targets are in `RBM3D/BA/KStep.lean` (746 lines, stop line 1,300), branch `t/T2396` (log above); `Loop/KLInduct.lean` is not edited and the cone of `KStep` has no `LWExpCert*` member.
* Target 1: `KStep_step` (one step) and `KStep_all` (strong induction) over `(Sig, TH, Kp)`, `Sig` and `Kp` polymorphic in the polygon size, bound `KStepAt`. Besides the empty-layer bound, the cut identity (shape of `baKpi_cut_abs`), the inner `IndStepAbs` and the outer bound, the statement carries `hzero` (a layer without a tree is 0; preflight F1) and `hBp`, `ht` (`0 ≤ Bp`, `‖t‖ ≤ 1`); all three are discharged at BA.
* Target 2: `baKpi_empty_bound` follows the band route of `KLInduct_Kpi_empty_bound` (all leaves short: `baKpi_empty_short` with `(1+Λ²)B ≥ 1`; else a long root leaf in sup norm times the root sum, `baKpi_empty_slice`); no one-line reduction (preflight F5).
* Target 3: `baKpiBoundAt_holds` is `KStep_all` at `KWardIneq_Data d Λ κ`, `BAKpi`, `BASig`, `Θ` (private `KStep_BA_all`). The leaf bundle `IndStepTH` (preflight F2) is proved in the file: decay, short, diffOne, diffTwo, zeroMode from `baProp5_holds`..`baProp8_holds` (6, 7 at `c = 1/2`, the loss `L^τ ≥ 1` of the fields spent), translation `KStep_theta_shift`, row sum `KStep_theta_row_le`; it gives `KStep_baIndStepAbs_holds` (an extra public name, stem-prefixed).
* The Ward inequality is not an input of the step (`grep -c KLWardIneq` on `KLInduct.lean` is 0, preflight F3). The last example feeds `KWardIneq_IndAt_of_abs (KStep_baIndStepAbs_holds ..)` to `baWardIneq_holds` and obtains `BAWardIneqAt 3 4 10 P.m0.im`, the premise of `baWardIneq_holds` discharged, no hypothesis left.
* Target 4: in every statement `∃ C` precedes `∀ L g E m t σ π a`, so `C` depends on `(d, n, Λ, κ, τ)` only.
* Target 5 (preflight F6): the first example shows by `decide` that `σ = KLsigAlt 4` has 3 trees in the layer `∅` and none in `{(0,2)}`; the nonempty layer `{(0,2)}` is at `σ = (+,+,-,+)` (key example above), also `n = 5` with `{(0,2),(2,4)}` and `n = 3`. No example has a hypothesis of another gate.
* Target 6: the registry grep has no match, so `Test/Axioms.lean` is unchanged. `RBM3D.lean` gets one import line (after the last import) and the full `lake build` ran with it.

## (c) Verified Mathlib names (all `#check`ed in chk.lean, exit 0, no error line)
`norm_sum_le Finset.sum_le_sum Finset.sum_mul Finset.mul_sum Finset.single_le_sum Finset.mem_range Nat.strong_induction_on Real.rpow_nonneg Real.rpow_add add_halves`
`Real.one_le_rpow Real.exp_le_one_iff inv_anti₀ mul_inv_cancel₀ one_le_pow₀ pow_le_pow_left₀ le_div_iff₀ Matrix.inv_submatrix_equiv Matrix.nonsing_inv_eq_ringInverse`
`Fintype.sum_equiv Finset.eq_empty_or_nonempty Finset.nonempty_iff_ne_empty Finset.card_pos Complex.norm_real Real.norm_of_nonneg Fin.last_add_one`. Names verified absent: none searched.

## (d) Open issues and paper-delta candidates
* T2396a (Lean structure, no paper statement differs): `KStep_step` takes `hzero` as a hypothesis (preflight F1); at BA it holds by the definition of `BAKpi`.
* T2396b: `IndStepTH` fields 6-8 carry the loss `L^τ`, `BAProp6/7/8` carry none; the bundle is the weaker statement (`1 ≤ L^τ`), no change to the paper.
* Six private copies (`KStep_theta_perm`, `KStep_theta_shift`, `KStep_row_of_resolvent`, `KStep_theta_row_le`, `KStep_theta_sup`, `KStep_theta_l1`) duplicate private lemmas of `BA/KInduct.lean`, `BA/KWardIneq.lean`; making them public is outside this ticket's files.
* K12 can use `KStep_baIndStepAbs_holds` and `baKpiBoundAt_holds` directly; the design's K12 row item "bundle `BAProp5to8` to the interface" is done here.
