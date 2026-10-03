Prover model: claude-sonnet-5-5

## (a) Math preflight — Sat Oct  3 04:05:55 UTC 2026

### (i) Exponent table

Sources: `git -C ../RBM2D --no-optional-locks show c9a24cf:RBM2D/Path/{Azuma,Stop,Markov}.lean` (statements read),
merged `RBM3D/Gauss/{FineModel,LinearForm}.lean`, `RBM3D/Path/Walk.lean`, `RBM3D/Defs/Sizes.lean`.
In `azuma_*`, `c : ℕ → ℝ≥0` is the **variance proxy** (`E e^{tY} ≤ e^{c t²/2}`), so "Σ c_k²" of the ticket is `Σ c_k` here.

| Quantity | Value (as stated in RBM2D `c9a24cf`) | Constraint | Slack / remark |
|---|---|---|---|
| `azuma_two_sided` (Azuma.lean:46) | `P(ε ≤ |Σ_{i<n} Y_i|) ≤ 2 exp(−ε²/(2 Σ_{i<n} c_i))`, `0 ≤ ε` | `Y` adapted; `Y 0` sub-G with `c 0` (unconditional); `Y(i+1)` cond. sub-G given `ℱ i`, `c(i+1)`, for `i < n−1` | prefactor 2 = two one-sided Mathlib bounds (`Y`, `−Y`); no loss |
| `azuma_complex` (Azuma.lean:84) | `P(ε ≤ ‖Σ Z_i‖) ≤ 4 exp(−ε²/(4 Σ c_i))` | Re and Im parts each as above, same `c` | `(ε/√2)²/(2Σc) = ε²/(4Σc)`: exact, no slack lost |
| `doob_L2_max` (Azuma.lean:212) | `P(x ≤ max_{k≤K} |M_k|) ≤ E[M_K²]/x²`, `0 < x` | `M` martingale, `M_k ∈ L²`; `M 0 = 0` is an unused (`_hM0`) hypothesis | **Weak-type** (Kolmogorov/Doob) form, NOT the strong `E max|M_k|² ≤ 4 E M_n²` of the ticket text; the port is verbatim (ticket: "verbatim"), strong form is not a target |
| `martingale_sq_eq_sum`, `stopped_martingale` | `E M_n² = Σ E(ΔM_k)²`; stopped martingale is a martingale | `M 0 = 0`, `M_k ∈ L²`; `τ` an `ℕ`-valued stopping time | none |
| `firstHit J θ K` (Stop.lean:41) | `hittingBtwn J (Ici θ) 0 K`, value in `[0,K]` | `J` adapted (grid: `J j ω = F j (pathH sz s t K n j ω)`, each `F j` measurable) | no numeric hypothesis; `θ`, `K'` free |
| `linTr n A X` | `Re tr(AX)` | `A, X` matrices on `Idx d (sz.L n) (sz.W n)` | R1–R4 renaming only |
| `linTrVar n A` (Markov.lean:236) | `Σ_c a_c² gvarF(c)`, `a_c = Re tr(A X(e_c))`, over `c ∈ coordFinset n` | `≥ 0` | closed form below |
| closed form of `linTrVar` | `Σ_i (Re A_ii)² S_ii + ½ Σ_{i<j} S_ij |A_ij + conj A_ji|²`; for Hermitian `A` equals `Σ_{i,j} |A_ij|² S_ij` | `S_xy = W^{-d} S^{(B)}_{ab}(g)` (`svarF`, FineModel.lean:47) | for non-Hermitian `A` the ticket's `Σ|A_ij|²S_ij` is NOT the value (checked in (ii)); the Lean def is the coefficient sum, unaffected |
| `S` normalisation | `S_xx = W^{-d}/(1+2dg²)`; row sums `Σ_y S_xy = 1` (block `S^{(B)}` stochastic, `W^d` sites per block) | `d=3`: `W^{-3}` replaces RBM2D's `W^{-2}` | `linTrVar(A) ≤ (max S)‖A‖_F² = W^{-d}(1+2dg²)^{-1}‖A‖_F²` for Hermitian `A` |
| `hasCondSubgaussianMGF_linear` (Markov.lean:628) | `√Δ·linTr n (A ω)(seqXmat (ω(k+1)))·1_E` cond. sub-G given `filt k`, param `c` | `A` `filt k`-measurable, `E ∈ filt k`, `0 ≤ c`, `Δ·linTrVar n (A ω) ≤ c` on `E`, `Δ = gridStep s t K n = (t−s)/K` | tightness: the proxy is exactly `Δ·linTrVar` (Gaussian) |
| Azuma sum at the use | `Σ_{k<K} c_k ≤ K·Δ·V = (t−s)·V`, `V = sup_E linTrVar` | grid `K Δ = t−s` | tail `2exp(−x²/(2(t−s)V))` |

Replacement of BDG (DECISIONS §7; BDG used at `3_5_Loop_Hierarchy.tex:216` (Lemma `lem:DIfREP`, (aaswtghh)) and `:2040`):
on the grid the martingale term is `Σ_k √Δ linTr(A_k, X_{k+1}) 1_{k<τ}` with `A_k ∈ filt k`; `hasCondSubgaussianMGF_linear` gives
conditional proxy `c_k = Δ·V` on the stopped event `E = {k < τ}` (`τ` from `firstHit`, `E ∈ filt k` by `lt_firstHit_grid_measurableSet`);
`azuma_two_sided` gives `P(|M| ≥ x) ≤ 2exp(−x²/(2(t−s)V))`, i.e. `|M| ≺ √((t−s)V)` with all-polynomial-moment strength (the content of BDG `2p`-moment
bounds used in `≺` form); `doob_L2_max` gives `P(max_k|M_k| ≥ x) ≤ E M_K²/x²` for the running maximum. The weak Doob form gives probability, not `L²`, bounds on the max;
this suffices for `≺` statements (DECISIONS §7), not for an `E max²` bound. Flag to dispatcher (not a FAIL: ticket pins "verbatim").
`Stop.lean` ports 15 grid/generic declarations incl. `lt_min_firstHit_grid_measurableSet` (not named in the ticket, in the source file).

### (ii) Concrete nondegenerate instance

Lean instances (ticket): `sz0` of `RBM3D/Defs/Sizes.lean` (`d=3`, `L_0=4`, `W_0=32`, `lam_0=1/64`, `N_0=2097152`), grid `s=1/10, t=1, K=4, Δ=9/40`, `n=0`.
(1) `isStoppingTime_firstHit_grid`: `F j = ‖M 0 0‖` (measurable), any `θ`, `K'`: no numeric hypothesis.
(2) `hasCondSubgaussianMGF_linear`: `A = (1/4)·1`, `E = univ`, `c = 1` (admissible: `Δ·linTrVar = 0.8987 ≤ 1`).
(3) `azuma_two_sided`, `c_k = 1`: `Y_0 = 0`, `Y_{k+1} = linTr(A, seqXmat(ω(k+1)))√Δ` from (2): `n = 100`, `Σ c = 100`.
Reason `linTrVar(1) = Σ_i S_ii = N_sites S_xx = L^d/(1+2dg²)`: only the `N_sites` diagonal coordinates have `a_c = 1`; off-diagonal have `a_c = Re(A_ij + A_ji) = 0` for `A = 1`.

Command 1: `python3 /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/d787b0e7-ec73-431d-9968-a805c3e11390/scratchpad/t2021_inst.py`
```
size N = 2097152 ; Delta = 9/40 ; S_xx = 3.047294002925402e-05 ; linTrVar(1) = L^d/(1+2dg^2) = 63.90638712823013 check True
Delta*linTrVar(1) = 14.37893710385178
A=(1/4)*1: Delta*linTrVar = 0.8986835689907362 <= c_k = 1 : True
n=100 steps, sum_{i<n} c_i = 100 ; Azuma bound at eps=20: 0.2706705664732254
positivity (nondegenerate): True True True True
```

Command 2 (Azuma/Doob at n = 100, adaptive increments `|Y_k| ≤ 1` so `c_k = 1`; `linTrVar` Monte Carlo at `d=3, W=2, L=3, g=1/2`, 216 sites; MC draws the real
coordinates with variance `gvarF` and builds `X` exactly as `Xentry`/`Xmat` (upper triangle `T + iF`, Hermitian completion, real diagonal)):
`python3 /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/d787b0e7-ec73-431d-9968-a805c3e11390/scratchpad/t2021_pre.py`
```
Azuma real, n=100, sum c=100, adaptive increments (|Y_k|<=1)
 eps=10: MC P=0.16073 <= bound 2exp(-eps^2/(2*100))=1.21306
 eps=15: MC P=0.05441 <= bound 2exp(-eps^2/(2*100))=0.64930
 eps=20: MC P=0.01951 <= bound 2exp(-eps^2/(2*100))=0.27067
 eps=25: MC P=0.00502 <= bound 2exp(-eps^2/(2*100))=0.08787
 Doob weak form P(max_{k<=n}|M_k|>=x) <= E M_n^2/x^2 ; E M_n^2 = 53.89
 x=15: MC P=0.10146 <= 0.23951
 x=20: MC P=0.03407 <= 0.13473
 x=25: MC P=0.00918 <= 0.08622
 strong L2 form check E max^2 = 93.779 <= 4 E M_n^2 = 215.56
 exact Rademacher P(|S_100|>=10)=0.36820 <= 1.21306
 exact Rademacher P(|S_100|>=20)=0.05689 <= 0.27067
 complex eps=20: MC P=0.14270 <= 4exp(-eps^2/400)=1.47152
 complex eps=30: MC P=0.01170 <= 4exp(-eps^2/400)=0.42160
N = 216 row sums of S (should be 1): 1.0 1.0  S_xx = 0.05  max S = 0.05  W^-d = 0.125
Hermitian A=True: sum a_c^2 gvarF = 214.699485; closed form = 214.699485; sum|A_ij|^2 S_ij = 214.699485; MC var (40000 samples) = 214.637335 (mean 0.0526); std err ~ 1.5182
   W^-d ||A||_F^2 upper bound: 5776.434262022245  (W^-2 would be 11552.86852404449 )
Hermitian A=False: sum a_c^2 gvarF = 215.792531; closed form = 215.792531; sum|A_ij|^2 S_ij = 434.627756; MC var (40000 samples) = 215.483650 (mean 0.0135); std err ~ 1.5259
   W^-d ||A||_F^2 upper bound: 11662.67009968768  (W^-2 would be 23325.34019937536 )
```
(The label "Hermitian A=False" is a general complex `A`; there `Σ|A_ij|²S_ij = 434.6` differs from the MC variance `215.5`, the closed form `215.79` matches. The `W^-d ‖A‖_F²`
line is a loose bound only; the sharper `max S·‖A‖_F² = 0.05·46211 = 2310 ≥ 214.7`.)

Reading: Azuma/Doob hold at all tested points (MC ≤ bound; Azuma bound is vacuous (>1) at `ε=10`, as expected at `ε²/(2Σc) = 0.5`);
`linTrVar` (coefficient sum, = Lean def) equals the Hermitian closed form `Σ|A_ij|² S_ij` exactly and the Monte Carlo variance within 1 std err (`|214.637−214.699| = 0.06`).
No external hypothesis occurs in the targets (no limit computation needed): the only inputs are the merged MD-1/MD-4 declarations (`seqXmat`, `seqGvar`, `PathΩ`, `pathP`, `filt`, `pathH`).

### Verdicts
- `Azuma.lean` (`azuma_two_sided`, `azuma_complex`, `doob_L2_max`, `martingale_sq_eq_sum`, `stopped_martingale`): PASS (note: `doob_L2_max` is the weak-type bound, see (i)).
- `Stop.lean` (`firstHit` lemmas, grid versions): PASS (hypotheses are measurability only; instance at `sz0` exists).
- `Markov.lean` (`condExp_freeze` … `hasCondSubgaussianMGF_linear`): PASS (variance identity verified at `d=3`, `W^{-d}` normalisation; instance (2)).

Overall: PASS.

## (a′) Preflight corrections — Sat Oct  3 04:14:24 UTC 2026

- (a)(ii) planned `A = (1/4)·1`, `c = 1` for `hasCondSubgaussianMGF_linear`. Proving `Δ·linTrVar(1/4·1) ≤ 1` in Lean needs the closed form of `linTrVar`, which is not a target. Compiled instead: (1) `hasCondSubgaussianMGF_linear` at `A = 1`, `E = univ`, `c = Δ·linTrVar 0 1` (`markov_hasCondSubgaussianMGF_linear_sz0`, `c > 0` by `markov_instance_c_pos`); (2) `A = markov_instA = (1/(1+Δ V))·1` (`V = linTrVar 0 1`), for which `0 < Δ·linTrVar ≤ 1` is proved (`markov_instA_bound`), hence `c_k = 1` for `azuma_two_sided` (instance in Azuma.lean, `n = 100`, `ε = 20`). The mathematics of (a) is unchanged; no verdict changes.
- Azuma.lean imports `RBM3D.Path.Markov` only for that instance (the instance must sit in the same file as the theorem; Markov.lean does not import Azuma.lean).

## (b) Script output

Prover model line 1. Worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2021`, branch `t/T2021`, commit `23e5021`.

### Build
```
$ lake build RBM3D.Path.Markov RBM3D.Path.Stop RBM3D.Path.Azuma 2>&1 | tail -3   (style warnings omitted: lines > 100 chars, Walk.lean unused hK)
⚠ [3313/3315] Replayed RBM3D.Path.Stop

Build completed successfully (3315 jobs).
$ (temporary imports of the three modules added to RBM3D.lean, not committed; reverted by git checkout) lake build 2>&1 | tail -1
Build completed successfully (3722 jobs).   [tool log of this session; `#assert_rbm_axioms` ran; no unclassified premise reported; only the pre-existing ledger lines]
$ git diff --stat main...t/T2021
 RBM3D/Path/Azuma.lean  | 382 ++++++++++++++++++++++
 RBM3D/Path/Markov.lean | 836 +++++++++++++++++++++++++++++++++++++++++++++++++
 RBM3D/Path/Stop.lean   | 238 ++++++++++++++
 3 files changed, 1456 insertions(+)
$ grep -n "sorry\|admit\|native_decide\|^axiom" RBM3D/Path/{Markov,Stop,Azuma}.lean   -> (no output)
```

### Axioms (`lake env lean ax.lean`: `#print axioms RBM.Path.<n>` for each public declaration below)
```
$ lake env lean ax.lean | sed 's/.*depends on axioms: //' | sort | uniq -c
     39 [propext, Classical.choice, Quot.sound]
declarations: azuma_two_sided azuma_complex doob_L2_max martingale_sq_eq_sum stopped_martingale firstHit isStoppingTime_firstHit firstHit_le lt_firstHit_measurableSet lt_firstHit_imp isStoppingTime_min_firstHit lt_min_firstHit_measurableSet lt_min_firstHit_imp sum_stopped pathH_measurable_filt adapted_of_measurable_pathH isStoppingTime_firstHit_grid lt_firstHit_grid_measurableSet isStoppingTime_min_firstHit_grid lt_min_firstHit_grid_measurableSet condExp_freeze linTr coordFinset linTr_seqXmat_eq_sum linTrVar linTrVar_nonneg map_linTr_seqXmat integral_linTr_seqXmat condExp_linear_eq_zero hasCondSubgaussianMGF_linear markov_linTrVar_one_pos markov_hasCondSubgaussianMGF_linear_sz0 markov_instance_c_pos markov_instOne markov_instScale markov_instA markov_instA_bound markov_cond_subgaussian_unit_sz0 markov_measurable_linTr_seqXmat_sz0
```
The two `example`s (Stop.lean, Azuma.lean) compile in the same build.

### Ported statements against RBM2D c9a24cf (script: rename R1-R4, normalise whitespace, compare statement text up to `:=`)
```
RBM2D lines at c9a24cf: Azuma.lean:46 azuma_two_sided; :84 azuma_complex; :212 doob_L2_max; :282 martingale_sq_eq_sum; :307 stopped_martingale.
Stop.lean:41 firstHit; :50 isStoppingTime_firstHit; :55 firstHit_le; :61 lt_firstHit_measurableSet; :74 lt_firstHit_imp; :90 isStoppingTime_min_firstHit;
 :104 lt_min_firstHit_measurableSet; :123 lt_min_firstHit_imp; :134 sum_stopped; :158 pathH_measurable_filt; :166 adapted_of_measurable_pathH;
 :174 isStoppingTime_firstHit_grid; :184 lt_firstHit_grid_measurableSet; :194 isStoppingTime_min_firstHit_grid; :206 lt_min_firstHit_grid_measurableSet.
Markov.lean:55 condExp_freeze; :132 linTr; :137 coordFinset; :222 linTr_seqXmat_eq_sum; :236 linTrVar; :240 linTrVar_nonneg; :248 map_linTr_seqXmat;
 :307 integral_linTr_seqXmat; :327 condExp_linear_eq_zero; :628 hasCondSubgaussianMGF_linear.
Result (script): 54 of 59 declarations of the three RBM2D files (targets and private helpers) are IDENTICAL after the renaming; the 5 others are the RBM2D-only checks
 (stopCheckSizes, markovSizes, markov_check_hasCondSubgaussianMGF_linear, markov_check_linTrVar_pos), replaced by the sz0 instances below, and markov_linTrVar_one_pos (RBM2D private helper), public here, restated at
 `{d} (sz : Sizes d)` and used by the instance. Proofs: Azuma.lean unchanged apart from the header and the instance; Stop.lean and Markov.lean renamed
 (R1: `d : Sizes` -> `{d : ℕ} (sz : Sizes d)`; R2: `Idx (d.L n) (d.W n)` -> `Idx d (sz.L n) (sz.W n)`; R3: `Coord` -> `CoordF d`, `Xmat_add/Xmat_smul/measurable_Xentry` take `d`;
 R4: `Sizes.X d` -> `Sizes.X sz`, `filt/pathP/PathΩ/pathH/map_incr/indep_incr d` -> `sz`). One proof-level addition: a private instance `StandardBorelSpace (PathΩ sz)` (instance search fails at generic `sz`).
$ git -C ../RBM2D --no-optional-locks diff --stat c9a24cf HEAD -- RBM2D/Path/{Azuma,Stop,Markov}.lean   (RBM2D HEAD 9e0f275 differs from the pinned c9a24cf; ports use c9a24cf)
 RBM2D/Path/Azuma.lean  | 124 ++--------------------------------------
 RBM2D/Path/Markov.lean | 151 ++++++++-----------------------------------------
 RBM2D/Path/Stop.lean   |  91 ++++-------------------------
 3 files changed, 43 insertions(+), 323 deletions(-)
```

### Target statements (extracted from the files by script; remaining targets are in the IDENTICAL list above)
```lean
theorem azuma_two_sided {Y : ℕ → Ω' → ℝ} {c : ℕ → ℝ≥0} (h_adapted : StronglyAdapted ℱ Y) (n : ℕ)
  (h0 : HasSubgaussianMGF (Y 0) (c 0) μ)
  (h_subG : ∀ i < n - 1, HasCondSubgaussianMGF (ℱ i) (ℱ.le i) (Y (i + 1)) (c (i + 1)) μ)
  {ε : ℝ} (hε : 0 ≤ ε) :
  μ.real {ω | ε ≤ |∑ i ∈ range n, Y i ω|} ≤
  2 * Real.exp (-ε ^ 2 / (2 * ∑ i ∈ range n, c i)) :=

theorem azuma_complex {Z : ℕ → Ω' → ℂ} {c : ℕ → ℝ≥0}
  (hZR : StronglyAdapted ℱ (fun i ω => (Z i ω).re))
  (hZI : StronglyAdapted ℱ (fun i ω => (Z i ω).im)) (n : ℕ)
  (h0R : HasSubgaussianMGF (fun ω => (Z 0 ω).re) (c 0) μ)
  (h0I : HasSubgaussianMGF (fun ω => (Z 0 ω).im) (c 0) μ)
  (hCR : ∀ i < n - 1,
  HasCondSubgaussianMGF (ℱ i) (ℱ.le i) (fun ω => (Z (i + 1) ω).re) (c (i + 1)) μ)
  (hCI : ∀ i < n - 1,
  HasCondSubgaussianMGF (ℱ i) (ℱ.le i) (fun ω => (Z (i + 1) ω).im) (c (i + 1)) μ)
  {ε : ℝ} (hε : 0 ≤ ε) :
  μ.real {ω | ε ≤ ‖∑ i ∈ range n, Z i ω‖} ≤
  4 * Real.exp (-ε ^ 2 / (4 * ∑ i ∈ range n, c i)) :=

theorem doob_L2_max (hM : Martingale M ℱ μ) (_hM0 : M 0 = 0) (hM2 : ∀ k, MemLp (M k) 2 μ)
  (K : ℕ) {x : ℝ} (hx : 0 < x) :
  μ.real {ω | x ≤ (range (K + 1)).sup' nonempty_range_add_one fun k => |M k ω|} ≤
  (∫ ω, (M K ω) ^ 2 ∂μ) / x ^ 2 :=

noncomputable def firstHit (J : ℕ → Ω' → ℝ) (θ : ℝ) (K : ℕ) : Ω' → ℕ :=

theorem isStoppingTime_firstHit_grid
  {F : ℕ → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ → ℝ}
  (hF : ∀ j, Measurable (F j)) (θ : ℝ) (K' : ℕ) :
  IsStoppingTime (filt sz)
  (fun ω => (firstHit (fun j (ω : PathΩ sz) => F j (pathH sz s t K n j ω)) θ K' ω : ℕ)) :=

theorem condExp_freeze {β : Type*} [MeasurableSpace β] [StandardBorelSpace β]
  (k : ℕ) {Y : PathΩ sz → β} (hY : Measurable[filt sz k] Y)
  {F : β → Sizes.SeqΩ sz → ℝ} (hF : Measurable (fun p : β × Sizes.SeqΩ sz => F p.1 p.2))
  (hInt : Integrable (fun ω => F (Y ω) (ω (k + 1))) (pathP sz)) :
  (pathP sz)[fun ω => F (Y ω) (ω (k + 1)) | filt sz k]
  =ᵐ[pathP sz] fun ω => ∫ x, F (Y ω) x ∂(Sizes.seqP sz) :=

def linTrVar (n : ℕ) (A : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) : ℝ :=

theorem hasCondSubgaussianMGF_linear (n k : ℕ)
  {A : PathΩ sz → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ}
  (hA : Measurable[filt sz k] A) (E : Set (PathΩ sz)) (hE : MeasurableSet[filt sz k] E)
  (c : ℝ) (hc : 0 ≤ c) (hbound : ∀ ω ∈ E, gridStep s t K n * linTrVar n (A ω) ≤ c) :
  HasCondSubgaussianMGF (filt sz k) ((filt sz).le k)
  (fun ω => E.indicator
  (fun ω => Real.sqrt (gridStep s t K n) * linTr n (A ω) (Sizes.seqXmat sz n (ω (k + 1))))
  ω)
  ⟨c, hc⟩ (pathP sz) :=
```

### Compiled nonempty instances (extracted from the files; all deterministic hypotheses discharged, `sz0`: d = 3, L_0 = 4, W_0 = 32)
```lean
-- Stop.lean:222  (s = 1/10, t = 1, K = 4, n = 0, F j M = ‖M 0 0‖, θ = 1/2, K' = 4)
example :
    IsStoppingTime (filt SizesInst.sz0)
      (fun ω => (firstHit (fun j (ω : PathΩ SizesInst.sz0) =>
        (fun (_k : ℕ) (M : Matrix (Idx 3 (SizesInst.sz0.L 0) (SizesInst.sz0.W 0))
          (Idx 3 (SizesInst.sz0.L 0) (SizesInst.sz0.W 0)) ℂ) => ‖M 0 0‖) j
          (pathH SizesInst.sz0 (fun _ => (1 / 10 : ℝ)) (fun _ => 1) (fun _ => 4) 0 j ω))
        (1 / 2) 4 ω : ℕ)) :=
  isStoppingTime_firstHit_grid SizesInst.sz0 (fun _ => (1 / 10 : ℝ)) (fun _ => 1) (fun _ => 4) 0
    (F := fun (_k : ℕ) (M : Matrix (Idx 3 (SizesInst.sz0.L 0) (SizesInst.sz0.W 0))
      (Idx 3 (SizesInst.sz0.L 0) (SizesInst.sz0.W 0)) ℂ) => ‖M 0 0‖)
    (fun _ => (measurable_norm).comp (Matrix.measurable_apply (i := 0) (j := 0))) (1 / 2) 4

-- Markov.lean:752  (A = 1, E = univ, c = Δ·linTrVar 0 1 > 0 by markov_instance_c_pos, Δ = 9/40)
theorem markov_hasCondSubgaussianMGF_linear_sz0 (k : ℕ) :
    HasCondSubgaussianMGF (filt sz0 k) ((filt sz0).le k)
      (fun ω => (Set.univ : Set (PathΩ sz0)).indicator
        (fun ω => Real.sqrt (gridStep (fun _ => (1 / 10 : ℝ)) (fun _ => 1) (fun _ => 4) 0)
          * linTr 0 markov_instOne (Sizes.seqXmat sz0 0 (ω (k + 1)))) ω)
      ⟨gridStep (fun _ => (1 / 10 : ℝ)) (fun _ => 1) (fun _ => 4) 0 * linTrVar 0 markov_instOne,
        mul_nonneg (by rw [instGridStep]; norm_num) (linTrVar_nonneg _ _)⟩
      (pathP sz0) :=
  hasCondSubgaussianMGF_linear (fun _ => (1 / 10 : ℝ)) (fun _ => 1) (fun _ => 4) 0 k
    measurable_const Set.univ MeasurableSet.univ _
    (mul_nonneg (by rw [instGridStep]; norm_num) (linTrVar_nonneg _ _)) (fun _ _ => le_rfl)

-- Markov.lean:815  (A = markov_instA = (1/(1+ΔV))•1, 0 < Δ·linTrVar ≤ 1 by markov_instA_bound, c = 1)
theorem markov_cond_subgaussian_unit_sz0 (k : ℕ) :
    HasCondSubgaussianMGF (filt sz0 k) ((filt sz0).le k)
      (fun ω => Real.sqrt (9 / 40 : ℝ)
        * linTr 0 markov_instA (Sizes.seqXmat sz0 0 (ω (k + 1)))) 1 (pathP sz0) := by
  have h := hasCondSubgaussianMGF_linear (fun _ => (1 / 10 : ℝ)) (fun _ => 1) (fun _ => 4) 0 k
-- Azuma.lean:372  (n = 100, c_k = 1, ε = 20; Y 0 = 0, Y (k+1) = √Δ·linTr 0 A (X (ω (k+1))); adapted, h0, h_subG all proved)
example :
    (pathP sz0).real {ω | (20 : ℝ) ≤ |∑ i ∈ range 100, azumaInstY i ω|} ≤
      2 * Real.exp (-(20 : ℝ) ^ 2 / (2 * ∑ i ∈ range 100, ((fun _ => (1 : ℝ≥0)) i))) :=
  azuma_two_sided (c := fun _ => (1 : ℝ≥0)) azumaInstY_adapted 100
    ⟨fun t => by simp [azumaInstY],
      fun t => by simpa [azumaInstY, mgf] using Real.one_le_exp (by positivity)⟩
    (fun i _ => markov_cond_subgaussian_unit_sz0 i) (by norm_num)

end Instance
```

### Name-clash grep
```
$ git grep -nw <name> cf8e79e -- RBM3D/*.lean RBM3D.lean   for each of the 39 public names in the axiom list
every count is 0 (script loop output, tool log). Helper names added by this ticket: markov_* (file-stem prefix), plus the private lemmas of the RBM2D files.
```

### Narrative
- Azuma.lean, Stop.lean, Markov.lean are ports of RBM2D c9a24cf under the renaming R1-R4; the statement comparison above is a script result, not a reading.
- `linTrVar` is defined with the merged `Sizes.seqGvar` (`gvarF`, hence `svarF`: `W^{-d}` normalisation); the definition text is the RBM2D one, so the d = 3 normalisation enters only through the merged `FineModel.lean`. The positivity helper (`markov_linTrVar_one_pos`) uses the merged `svarF_diag` (`S_xx = W^{-d}(1+2dg²)^{-1}`).
- `doob_L2_max` is the weak-type bound `P(x ≤ max_{k≤K}|M_k|) ≤ E M_K²/x²` as in RBM2D (see (a) (i)); the strong `E max|M_k|² ≤ 4 E M_n²` is not a target here.
- Azuma.lean now imports Markov.lean (instance only). Downstream importers of Azuma.lean pull Markov.lean transitively.
- No new hypothesis `Prop`; `RBM3D/Test/Axioms.lean` untouched; the full build with temporary root imports reported no unclassified premise.

## (c) Verified Mathlib names used (compiled in the build above)
ProbabilityTheory.measure_sum_ge_le_of_hasCondSubgaussianMGF; Kernel.HasSubgaussianMGF.neg/of_rat; HasSubgaussianMGF (structure fields integrable_exp_mul, mgf_le); HasCondSubgaussianMGF;
MeasureTheory.maximal_ineq; Submartingale.stoppedProcess; MeasureTheory.hittingBtwn, hittingBtwn_le; Adapted.isStoppingTime_hittingBtwn; Matrix.measurable_iff, Matrix.measurable_apply;
StandardBorelSpace.pi_countable; MeasureTheory.Filtration.piLE; Preorder.restrictLe; condExpKernel_comp_trim; condExp_ae_eq_trim_integral_condExpKernel; ae_eq_condExp_of_forall_setIntegral_eq;
condExp_mul_of_stronglyMeasurable_left; Set.indicator_univ; Real.one_le_exp. Verified absent: a Mathlib lemma deriving `HasCondSubgaussianMGF` from independence (grep of Probability/Moments/SubGaussian.lean).

## (d) Open issues and paper-delta candidates
- T2021a (Lean/paper): `doob_L2_max` gives the weak-type tail bound, while DECISIONS §7 / the ticket text speak of "Doob L² maximal inequality" `E max|M_k|² ≤ 4E|M_n|²`; the weak form suffices for `≺` statements, an `E max²` bound would need a new lemma (not a target). Dispatcher to decide whether ST-2 needs the strong form.
- T2021b (instance): the sz0 instance of `hasCondSubgaussianMGF_linear` has `c = Δ·linTrVar 0 1` (not a numeric `c = 1`); the numeric `c_k = 1` instance is the Azuma one with a rescaled direction. See (a′).
- Style: 58 lines > 100 chars over the three files (`awk 'length($0)>100' ... | wc -l`) (inherited from the renaming, `Idx d (sz.L n) (sz.W n)` is longer); warnings only.
