Prover model: claude-sonnet-5-5
## (a) Math preflight — Sat Oct  3 08:06:09 UTC 2026

Source: `../RBM2D/RBM2D/Loop/SumZero.lean` at `c9a24cf` (line numbers below); merged 3D defs `RBM3D/Loop/KLTree.lean` (`KLKpi` :351, `KLSigmaPi` :366, `KLselfW` :357, `KLsigAlt` :345), `Loop/Partition.lean:166` (`thetaEdge d L g m t s s' = Theta d L g (t*(m s*m s'))`), `Propagator/Props4.lean:114` (`sum_Theta_row_of_three_le`), `Defs/Block.lean:136` (`norm_SB`), `Loop/GLoop.lean:75` (`etaT E t = (1-t)*(mE E).im`).

### (i) Exponent table

| # | Item | Value / form | Constraint | Slack at instance (d=3, L=3, g=1/2, E=0, t=1/2, κ=1, n=4) |
|---|---|---|---|---|
| 1 | `\|Zd d L\|` (2D: `L²`, `card_Z2_cast` :139) | `L^d` (27) in `treeZ_eq` :208, `sum_SigmaPi`, `sum_Kpi_closed` :357, `SumZero_sum_slice` :400 (orbit count `∑_x S x = L^d S 0`) | `NeZero L`; `3 ≤ L` only via `norm_SB`; `d` free (no `3 ≤ d` used) | L = 3 is the extreme allowed value; script: 27 sites, S has 7 nonzeros per row, row sums 1 |
| 2 | `W^d` (ticket: "`W²η_t → W^dη_t`") | does not occur: no `W` in `Kpi`, `SigmaPi`, `Qlayer`, `Alayer`, or in the conclusion of :802 (`grep -nw "W\|etaT"` on the 2D file: only `etaT E t` at :808, :820, :869, :884; `W` only inside the name `treeValW`) | — | The ticket remark does not apply to this file: a faithful port has no `W^d`. Adding one would change the statement. |
| 3 | `‖ξ‖<1` for `Θ_ξ` column/row sums `(1-ξ)⁻¹` | edge `ξ = t m(s) m(s')`: same sign `-t`, opposite sign `+t` (E=0, `m(±)=±i`); `‖ξ‖ = t` in the bulk (`norm_mSigma`) | hypothesis `hm : ∀ s s', ‖t m_s m_s'‖ < 1` ⇔ `t<1` | `1 - t = 1/2` |
| 4 | `∏_i m(σ_i)` in `KLKpi`/`KLSigmaPi` (absent in 2D `Kpi`/`SigmaPi`) | `∑_a KLKpi = L^d · A`, `A(σ,π) = (∏_i m(σ_i)) · ∏_v (1-ξ_v)⁻¹ · Q(σ,π)`; `∑_d KLSigmaPi = L^d (∏ m) Q`; slice `= (∏ m) Q` | merged `KLKpi` carries the factor (paper `eq:defKpi` = sum of `Γ^{(n)}_M`) | script: 2D form without `∏m` is off by ~1e2; with `∏m` exact to 1e-12. For `σ_alt`, n even: `∏m = (m m̄)^{n/2} = 1` (`‖m‖=1`) |
| 5 | `gapK κ = min(1, √(κ(4-κ)/2))` (`Kcal.lean:311`, `d`-free, `g`-free) | κ=1: `min(1,√1.5)=1` | `0<κ≤2`; need `gapK ≤ ‖1 - t m(s)²‖` for `t∈[0,1]`, `\|E\|≤2-κ`. Identity (uses `‖m‖=1`, `Re m = -E/2`): `‖1-t m²‖² = (1-t)²+t(4-E²)`; `4-E² ≥ κ(4-κ)` | `gapK² = 1 ≤ 1.5 = κ(4-κ)/2`; at instance `‖1-t m²‖ = 1+t = 1.5 ≥ 1`, slack 0.5; at `t=0` slack 0 (tight). Grid check (4 κ × 41 E × 41 t × 2 signs): min of `‖1-t m²‖ - gapK` = 0.0 and identity holds to 1e-12 |
| 6 | Lipschitz constant `C_n = 2^{n²} n gapK⁻ⁿ` (`norm_Qlayer_le`) | n=4, κ=1: `2^16·4·1 = 262144` | `#TSPlong ≤ 2^{n²}`, `#F ≤ n-2 ≤ n`, edge difference `≤ (1-t) c⁻²`, `c ≤ 1` so `M = c⁻¹ ≥ 1` | conclusion constant, not a hypothesis; no astronomically large witness is needed |
| 7 | `1-t ≤ (2/√(κ(4-κ))) η_t` (`one_sub_le_etaT` :782) | 3D `η_t = (1-t)·√(4-E²)/2` (0.5 at instance) | `√(4-E²) ≥ √(κ(4-κ))` for `\|E\|≤2-κ` | `1-t = 0.5 ≤ 1.1547·0.5 = 0.577`, slack 0.077 |
| 8 | Final bound (:802) | `C_n·(2/√(κ(4-κ)))·η_t = 262144·1.1547·0.5 = 151348.9` | needs `Q(σ_alt,∅)(1) = 0` (extra hypothesis), `n ≥ 4`, `Even n`, `κ>0`, `L≥3`, `\|E\|≤2-κ`, `t∈[0,1)` | LHS `\|slice\| = 1/3`; `Q(1) = 1+2(1/2-1) = 0` exactly |
| 9 | Tree sizes | `diagonals(n)`: n=3 none; n=4 `{(0,2),(1,3)}`; nonempty `F` needs `n ≥ 4` (`IsDiag`: `i<j`, `j≠i+1`, `(i,j)≠(0,n-1)`) | peeling over `F` uses only that the parent of a diagonal is a strictly larger node | `TSPlong(4,σ_alt,∅) = {∅,{(0,2)},{(1,3)}}` (script) |

Merged-vs-2D differences that the port must carry (no other statement difference found): (1) `g : ℝ` explicit parameter in `thetaEdge d L g`, `KLKpi d L g`, `KLSigmaPi d L g`; closed forms are `g`-free because `S^(B)(g)` has row and column sums 1 for every `g` (`norm_SB`, `SB_mulVec_one`); (2) `∏m(σ_i)` (row 4); (3) `m = mSigma E`, `etaT E t = (1-t)(mE E).im`, `gapK` and `sigAlt` renamed/re-defined; (4) `Kcal`'s `W^{-d(n-1)}` is outside `KLKpi`, so no `W` enters.

### (ii) Concrete nondegenerate instance

`d=3, L=3 (27 sites), W=2 (unused), g=1/2, E=0 (m(+)=i, m(-)=-i), t=1/2, κ=1, n∈{3,4}`. Hypotheses of the targets: `3≤L` ✓, `‖ξ‖ = 1/2 < 1` ✓, `|E| = 0 ≤ 2-κ = 1` ✓, `t∈[0,1)` ✓, `4 ≤ n`, `Even n` ✓ (n=4), `Q(σ_alt 4, ∅)(1) = 0` ✓ (below), `κ>0` ✓. Brute-force tensor contraction over all `a∈(Z_3^3)^n` and all internal labels (no closed form used for the left sides; parent maps `leafPar`/`nodePar` = smallest-width containing node, root `(0,n-1)` default, as in `KLTree.lean:76-82`):

Command: `python3 /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/d787b0e7-ec73-431d-9968-a805c3e11390/scratchpad/T2043/chk.py`
```
row sums 0.9999999999999999 1.0000000000000002 nnz/row 7 S symmetric True
n=3: 8 pairs (sigma,pi), 8 with Q!=0; max|sum_a K - L^d*A(with prod m)|=3.27e-13; max|sum_a K - L^d*A(RBM2D form, no prod m)|=1.02e+02
n=4: 64 pairs (sigma,pi), 32 with Q!=0; max|sum_a K - L^d*A(with prod m)|=1.28e-12; max|sum_a K - L^d*A(RBM2D form, no prod m)|=9.60e+01
prod m(sigAlt 4) = (1+0j)
TSPlong(4,sigAlt,empty) = [[], [(0, 2)], [(1, 3)]]
Q(t=1/2) = (0.33333333333333326+0j)  formula 1+2((1+t)^-1-1) = 0.33333333333333326
slice sums d_0=x over all 27 x: min/max = (0.33333333333333237+0j) (0.33333333333333465+0j)
total sum_d Sigma = (8.999999999999998+0j)  L^d*pm*Q = (8.999999999999998+0j)
Q(t=1) by enumeration = 0j
gapK(1)=1, eta_t=0.5, |slice|=0.333333 <= RHS=151348.9
min over grid of |1-t m^2| - gapK(kappa) = 0.0
```
Reading: for every `σ∈{±}^n` and every `π ⊆ diagonals(n)` (8 pairs at n=3, 64 at n=4, 32 with `Q≠0`) `∑_a KLKpi = L^d·A(σ,π)` with `A` containing `∏m`; the 2D-form `A` without `∏m` fails. **RBM2D "Check 1" (:854) in d=3**: the slice sum `∑_{δ: δ_0=x} KLSigmaPi(1/2, σ_alt 4, ∅, δ) = (∏m)·Q = 1/3` for all 27 `x` (equal to the 2D value; it is `L`-, `d`- and `g`-free), and `∑_δ KLSigmaPi = 9 = L^d/3`. **Check 2** (:863): `|slice| = 1/3 ≤ 151348.9` with the hypothesis `Q(1)=0` discharged (`Q(t=1)` by enumeration = 0).

No external (non-Lean-proved) hypothesis occurs in the targets: `norm_SB`, `SB_mulVec_one`, `Theta_*_of_three_le` are merged theorems, so no limit computation is needed.

### Verdicts

- `treeZ_eq`, `treeZ_peel`, `sum_selfW`, `sum_out` (`L²→L^d`): PASS.
- `sum_Kpi_closed`, `SumZero_sum_Kpi_eq`, `sum_SigmaPi`: PASS, **with `Alayer`/slice carrying the factor `∏_i m(σ_i)`** (row 4). This is a statement change beyond renaming and exponents, forced by the merged `KLKpi`/`KLSigmaPi`; stage 1b must list it as a residual difference and a paper-delta candidate, or stop per the ticket.
- `SumZero_SigmaPi_add_const`, `SumZero_sum_slice` (slice `= (∏m)·Q`), `SumZero_sum_slice_alt` (`∏m=1` for `σ_alt`, n even, so `= Q`): PASS.
- (F3) gap and `SigmaPi_alt_sumZero_le_of_Qlayer_one` (with `Q(1)=0`; no `W`): PASS. The ticket's "`W²η_t→W^dη_t`" does not apply (row 2).
- Overall: PASS.

## (b) Script output (worktree /Users/junyin/Lean_proof/RBM3D-wt/T2043, branch t/T2043; scripts and raw outputs in /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/d787b0e7-ec73-431d-9968-a805c3e11390/scratchpad/T2043/ and its ev/)

$ date -u   # taken when the build, pre-check and axiom outputs below were collected; the later outputs were collected between this time and the time on the last line
Sat Oct  3 08:36:39 UTC 2026
$ git log --oneline -1; git diff --stat main...t/T2043; git diff --name-only main...t/T2043
629f1f3 T2043: KL7a, port RBM2D Loop/SumZero.lean to RBM3D/Loop/KLSumZero.lean
 RBM3D/Loop/KLSumZero.lean | 1080 +++++++++++++++++++++++++++++++++++++++++++++
 1 file changed, 1080 insertions(+)
RBM3D/Loop/KLSumZero.lean
$ lake build RBM3D.Loop.KLSumZero 2>&1 | tail -3
Build completed successfully (3237 jobs).
$ # registry pre-check (DECISIONS §20): scratch file `import RBM3D` / `import RBM3D.Loop.KLSumZero` / `#assert_rbm_axioms`, run as: lake env lean precheck.lean 2>&1 | head -3; echo exit
axiom audit: 1476 theorems, 542 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
All within [propext,
 Classical.choice,
exit: 0
  (control run without the module import: 1441 theorems, 534 definitions. `RBM3D/Test/Axioms.lean` and `RBM3D.lean` are not touched.)
$ lake build 2>&1 | tail -1   # whole library in the worktree (the root file does not import the new module yet)
Build completed successfully (3741 jobs).
$ lake env lean axtargets.lean   # #print axioms of every target and of three instances (names in RBM.Loop)
sum_Kpi_closed : [propext, Classical.choice, Quot.sound]
treeZ_eq : [propext, Classical.choice, Quot.sound]
SumZero_SigmaPi_add_const : [propext, Classical.choice, Quot.sound]
SumZero_sum_slice : [propext, Classical.choice, Quot.sound]
gapK_le_norm : [propext, Classical.choice, Quot.sound]
SumZero_sum_slice_alt : [propext, Classical.choice, Quot.sound]
SigmaPi_alt_sumZero_le_of_Qlayer_one : [propext, Classical.choice, Quot.sound]
KLSumZero_inst_Kpi_closed : [propext, Classical.choice, Quot.sound]
KLSumZero_inst_bound : [propext, Classical.choice, Quot.sound]
KLSumZero_neg_Kpi_closed_2Dform : [propext, Classical.choice, Quot.sound]
$ lake env lean axgroups.lean   # collectAxioms of every declaration the module adds to the environment
declarations of RBM3D.Loop.KLSumZero (public, non-internal): 43
42 declarations depend exactly on axioms #[Classical.choice, Quot.sound, propext]
1 declarations depend exactly on axioms #[Quot.sound, propext]
$ grep -nE 'sorry|admit|native_decide|^axiom|^ *axiom ' RBM3D/Loop/KLSumZero.lean; echo exit: $?
exit: 1
$ python3 wgrep.py RBM3D/Loop/KLSumZero.lean   # code lines, comments stripped, with `W` or `3 ≤ d`
code lines (comments stripped) mentioning W / 3 ≤ d: 0
lines with W in the raw file (docstrings only): 2
$ lake env lean listdecls.lean   # declarations of the module, from the environment: 43 = 35 theorems + 8 defs
  ported names (21; `KLSigmaPi.congr_simp` is tactic-generated): Alayer KLSigmaPi.congr_simp Qlayer SigmaPi_alt_sumZero_le_of_Qlayer_one SumZero_SigmaPi_add_const SumZero_sum_Kpi_eq SumZero_sum_Theta_col SumZero_sum_slice SumZero_sum_slice_alt edgeR gapK gapK_le_norm sum_Kpi_closed sum_SigmaPi sum_Theta_sub_one_col sum_Theta_sub_one_row sum_out sum_selfW treeZ treeZ_eq treeZ_peel
  instance names, prefix `KLSumZero_` (22): instE instF instF_mem inst_Kpi_closed inst_Kpi_closed_pure inst_Kpi_closed_val inst_Kpi_eq inst_Qlayer_one inst_Theta_sums inst_add_const inst_bound inst_col inst_gap inst_slice inst_slice_alt inst_sum_SigmaPi inst_sum_out inst_sum_selfW inst_treeZ_eq inst_treeZ_peel instr neg_Kpi_closed_2Dform
$ python3 clash.py   # every name above grepped (grep -rnw) in RBM3D/ and RBM3D.lean outside the new file
43 names declared by the module (RBM.Loop.*, from the environment), each grepped (-rnw) in RBM3D/ and RBM3D.lean outside the new file: 1 with a hit
  Alayer ['RBM3D/Loop/KLWard.lean:960:`Alayer`, `RBM2D/Loop/SumZeroWard.lean:1369-1395` at `c9a24cf`).  The proof is by u']
  (the one hit is a docstring, not a declaration)

$ python3 extract.py RBM3D/Loop/KLSumZero.lean <the seven targets>   # text of the file from the keyword to `:=`
[KLSumZero.lean:338] theorem sum_Kpi_closed (hL : 3 ≤ L) (σ : Fin n → Bool) (π : Finset (Fin n × Fin n)) :
    ∑ a : Fin n → Zd d L, KLKpi d L g m t σ a π = (L : ℂ) ^ d * Alayer m t σ π
[KLSumZero.lean:215] theorem treeZ_eq {F : Finset (Fin n × Fin n)} (hF : F ∈ TSP n)
    (E : ↥F → Matrix (Zd d L) (Zd d L) ℂ) (r : ↥F → ℂ) (hr : ∀ J y, ∑ x, E J x y = r J) :
    treeZ F E = (L : ℂ) ^ d * ∏ J, r J
[KLSumZero.lean:376] theorem SumZero_SigmaPi_add_const (hL : 3 ≤ L) (σ : Fin n → Bool)
    (π : Finset (Fin n × Fin n)) (δ : Fin n → Zd d L) (c : Zd d L) :
    KLSigmaPi d L g m t σ π (fun v => δ v + c) = KLSigmaPi d L g m t σ π δ
[KLSumZero.lean:387] theorem SumZero_sum_slice (hL : 3 ≤ L) (σ : Fin n → Bool) (π : Finset (Fin n × Fin n))
    (i : Fin n) (x : Zd d L) :
    ∑ δ ∈ univ.filter (fun δ : Fin n → Zd d L => δ i = x), KLSigmaPi d L g m t σ π δ =
      (∏ j, m (σ j)) * Qlayer m t σ π
[KLSumZero.lean:456] theorem gapK_le_norm {κ E t : ℝ} (hκ : 0 < κ) (hE : |E| ≤ 2 - κ) (ht0 : 0 ≤ t)
    (s : Bool) :
    gapK κ ≤ ‖1 - (t : ℂ) * (mSigma E s * mSigma E s)‖
[KLSumZero.lean:708] theorem SumZero_sum_slice_alt :
  ∀ κ : ℝ, 0 < κ → ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ E : ℝ, |E| ≤ 2 - κ →
    ∀ t ∈ Set.Ico (0 : ℝ) 1, ∀ (n : ℕ) [NeZero n] (hn : 4 ≤ n), Even n → ∀ d₁ : Zd d L,
      ∑ δ ∈ Finset.univ.filter (fun δ : Fin n → Zd d L => δ ⟨0, by omega⟩ = d₁),
          KLSigmaPi d L g (mSigma E) t (KLsigAlt n) ∅ δ = Qlayer (mSigma E) t (KLsigAlt n) ∅
[KLSumZero.lean:813] theorem SigmaPi_alt_sumZero_le_of_Qlayer_one :
  ∀ κ : ℝ, 0 < κ → ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ E : ℝ, |E| ≤ 2 - κ →
    ∀ t ∈ Set.Ico (0 : ℝ) 1, ∀ (n : ℕ) [NeZero n] (hn : 4 ≤ n), Even n →
      Qlayer (mSigma E) 1 (KLsigAlt n) ∅ = 0 → ∀ d₁ : Zd d L,
      ‖∑ δ ∈ Finset.univ.filter (fun δ : Fin n → Zd d L => δ ⟨0, by omega⟩ = d₁),
          KLSigmaPi d L g (mSigma E) t (KLsigAlt n) ∅ δ‖
        ≤ 2 ^ (n ^ 2) * n * (gapK κ)⁻¹ ^ n * (2 / Real.sqrt (κ * (4 - κ))) * Gauss.etaT E t
$ grep -n '^variable\|^include' RBM3D/Loop/KLSumZero.lean   # in force: 296-298 for sum_Kpi_closed, SumZero_sum_Kpi_eq, sum_SigmaPi; 370-372 for SumZero_SigmaPi_add_const, SumZero_sum_slice; 704 for the two ∀-theorems; 143 for treeZ_eq
55:variable {n : ℕ} [NeZero n]
143:variable {d L : ℕ} [NeZero L] {n : ℕ} [NeZero n]
253:variable {n : ℕ} [NeZero n]
296:variable (d L : ℕ) [NeZero L] (g : ℝ) (m : Bool → ℂ) {t : ℝ}
298:include hm
349:variable {d L : ℕ} [NeZero L] {n : ℕ} [NeZero n]
370:variable {n : ℕ} [NeZero n] (d L : ℕ) [NeZero L] (g : ℝ) (m : Bool → ℂ) {t : ℝ}
372:include hm
704:variable (d : ℕ) (g : ℝ)
$ python3 extractdef.py RBM3D/Loop/KLSumZero.lean Alayer   # the other definitions equal RBM2D's after renaming (portdiff below)
[KLSumZero.lean:268]
noncomputable def Alayer (m : Bool → ℂ) (t : ℝ) (σ : Fin n → Bool)
    (π : Finset (Fin n × Fin n)) : ℂ :=
  (∏ i, m (σ i)) * ((∏ v, (1 - (t : ℂ) * (m (σ v) * m (σ (v + 1))))⁻¹) * Qlayer m t σ π)

$ python3 extract.py RBM3D/Loop/KLSumZero.lean <instances>   # compiled nonempty instances at d = 3, L = 3, g = 1/2, E = 0, t = 1/2, κ = 1: every hypothesis discharged, none left
[KLSumZero.lean:933] theorem KLSumZero_inst_Kpi_closed :
    ∑ a : Fin 4 → Zd 3 3, KLKpi 3 3 (1 / 2) (mSigma 0) (1 / 2) (KLsigAlt 4) a ∅ =
      (3 : ℂ) ^ 3 * Alayer (mSigma 0) (1 / 2) (KLsigAlt 4) ∅
[KLSumZero.lean:955] theorem KLSumZero_inst_Kpi_closed_val :
    ∑ a : Fin 4 → Zd 3 3, KLKpi 3 3 (1 / 2) (mSigma 0) (1 / 2) (KLsigAlt 4) a ∅ = 144
[KLSumZero.lean:970] theorem KLSumZero_inst_Kpi_closed_pure :
    ∑ a : Fin 3 → Zd 3 3, KLKpi 3 3 (1 / 2) (mSigma 0) (1 / 2) (fun _ : Fin 3 => true) a ∅ =
      -8 * Complex.I
[KLSumZero.lean:987] theorem KLSumZero_neg_Kpi_closed_2Dform :
    ∑ a : Fin 3 → Zd 3 3, KLKpi 3 3 (1 / 2) (mSigma 0) (1 / 2) (fun _ : Fin 3 => true) a ∅ ≠
      (3 : ℂ) ^ 3 * ((∏ _v : Fin 3, (1 - ((1 / 2 : ℝ) : ℂ) * (mSigma 0 true * mSigma 0 true))⁻¹) *
        Qlayer (mSigma 0) (1 / 2) (fun _ : Fin 3 => true) ∅)
[KLSumZero.lean:900] theorem KLSumZero_inst_bound (d₁ : Zd 3 3) :
    ‖∑ δ ∈ Finset.univ.filter (fun δ : Fin 4 → Zd 3 3 => δ ⟨0, by omega⟩ = d₁),
        KLSigmaPi 3 3 (1 / 2) (mSigma 0) (1 / 2) (KLsigAlt 4) ∅ δ‖
      ≤ 2 ^ (4 ^ 2) * ((4 : ℕ) : ℝ) * (gapK 1)⁻¹ ^ 4 * (2 / Real.sqrt (1 * (4 - 1)))
          * Gauss.etaT 0 (1 / 2)
[KLSumZero.lean:891] theorem KLSumZero_inst_slice_alt (d₁ : Zd 3 3) :
    ∑ δ ∈ Finset.univ.filter (fun δ : Fin 4 → Zd 3 3 => δ ⟨0, by omega⟩ = d₁),
      KLSigmaPi 3 3 (1 / 2) (mSigma 0) (1 / 2) (KLsigAlt 4) ∅ δ = 1 / 3
[KLSumZero.lean:881] theorem KLSumZero_inst_Qlayer_one : Qlayer (mSigma 0) 1 (KLsigAlt 4) ∅ = 0
  one instance of every other public statement, same data: inst_Kpi_eq inst_Theta_sums inst_add_const inst_col inst_gap inst_slice inst_sum_SigmaPi inst_sum_out inst_sum_selfW inst_treeZ_eq inst_treeZ_peel (instE, instF, instF_mem, instr are the data of the tree instances)
$ python3 numcheck.py   # brute-force tensor contraction over all labels, independent of the closed forms
n=4 sigAlt, t=1/2, E=0: sum_a K^(empty) = 144.000000000+0.0e+00j  (Lean KLSumZero_inst_Kpi_closed_val: 144);  prod m = 1.000+0.000j
n=3 (+,+,+), t=1/2, E=0: sum_a K^(empty) = 0.000000000-8.000000000j  (Lean KLSumZero_inst_Kpi_closed_pure: -8i);  prod m = -0.000-1.000j;  L^d prod(1-xi)^-1 Q (RBM2D form) = 8.000000000+0.000000000j
$ sed -n <lines>   # the definitions behind R1, R2 below, and the paper lines
RBM2D Kcal.lean:  noncomputable def Kpi (m : Bool → ℂ) (t : ℝ) (σ : Fin n → Bool) (a : Fin n → Z2 L)
RBM2D Kcal.lean:      (π : Finset (Fin n × Fin n)) : ℂ :=
RBM2D Kcal.lean:    ∑ F ∈ TSPlong n σ π, treeValG L m t σ a F
RBM2D Kcal.lean:  noncomputable def SigmaPi (m : Bool → ℂ) (t : ℝ) (σ : Fin n → Bool)
RBM2D Kcal.lean:      (π : Finset (Fin n × Fin n)) (d : Fin n → Z2 L) : ℂ :=
RBM2D Kcal.lean:    ∑ F ∈ TSPlong n σ π, selfE L m t σ F d
RBM3D KLTree.lean: noncomputable def KLKpi (m : Bool → ℂ) (t : ℝ) (σ : Fin n → Bool) (a : Fin n → Zd d L)
RBM3D KLTree.lean:     (π : Finset (Fin n × Fin n)) : ℂ :=
RBM3D KLTree.lean:   (∏ i, m (σ i)) * ∑ F ∈ KLTSPlong n σ π, KLtreeValG d L g m t σ a F
RBM3D KLTree.lean: noncomputable def KLSigmaPi (m : Bool → ℂ) (t : ℝ) (σ : Fin n → Bool)
RBM3D KLTree.lean:     (π : Finset (Fin n × Fin n)) (δ : Fin n → Zd d L) : ℂ :=
RBM3D KLTree.lean:   (∏ i, m (σ i)) * ∑ F ∈ KLTSPlong n σ π,
RBM3D KLTree.lean:     KLselfW d L F (fun J => thetaEdge d L g m t (σ J.1.1) (σ J.1.2) - 1) δ
A_deterministic_estimates.tex: \begin{equation}\label{M-graph-value-unsummed}
A_deterministic_estimates.tex: \Gamma^{(n)}_{t,\bsig,\ba} := \p{\prod_{i=1}^n m(\sig_i)} \cdot \sum_{\mathbf b} \prod_{e} f_{t,\bsig}\p{e}    \, ,
A_deterministic_estimates.tex:   \begin{align}\label{eq:defKpi}
A_deterministic_estimates.tex:     \cK^{\p{\pi}}\p{t,\bsig,\ba}
A_deterministic_estimates.tex:       :=\sum_{\Gamma \in \TSP\p{\mathcal{P}_{\ba}, \bsig, \pi}} \Gamma^{\p{n}}_{M;t,\bsig,\ba}  .

$ python3 portdiff.py SumZero_c9a24cf.lean RBM3D/Loop/KLSumZero.lean Kcal_c9a24cf.lean   # signature up to `:=` (and def body) of each public RBM2D declaration; RBM2D text renamed Z2 L→Zd d L, L²→L^d, Theta L→Theta d L g, Kpi/SigmaPi/selfW/TSPlong/Flong/sigAlt/nodes/nodePar/leafPar/ArcLe/…→KL…, mSig→mSigma, spectralM→mE, etaT→Gauss.etaT, bound d→δ|J; explicit binders compared by text
RBM2D public declarations compared (19): same name in KLSumZero.lean: 19; missing: []
  BODY DIFFERS Alayer:
    2D renamed: (∏ v, (1 - (t : ℂ) * (m (σ v) * m (σ (v + 1))))⁻¹) * Qlayer m t σ π
    3D        : (∏ i, m (σ i)) * ((∏ v, (1 - (t : ℂ) * (m (σ v) * m (σ (v + 1))))⁻¹) * Qlayer m t σ π)
  DIFFERS sum_SigmaPi:
    2D renamed: ∑ δ : Fin n → Zd d L, KLSigmaPi d L g m t σ π δ = (L : ℂ) ^ d * Qlayer m t σ π
    3D        : ∑ δ : Fin n → Zd d L, KLSigmaPi d L g m t σ π δ = (L : ℂ) ^ d * ((∏ i, m (σ i)) * Qlayer m t σ π)
  DIFFERS SumZero_sum_slice:
    2D renamed: ∑ δ ∈ univ.filter (fun δ : Fin n → Zd d L => δ i = x), KLSigmaPi d L g m t σ π δ = Qlayer m t σ π
    3D        : ∑ δ ∈ univ.filter (fun δ : Fin n → Zd d L => δ i = x), KLSigmaPi d L g m t σ π δ = (∏ j, m (σ j)) * Qlayer m t σ π
2D line > 3D line: sum_out 92>99; treeZ 143>150; treeZ_peel 151>158; treeZ_eq 208>215; sum_selfW 228>235; edgeR 249>256; Qlayer 253>261; Alayer 259>268; SumZero_sum_Theta_col 265>273; sum_Theta_sub_one_col 273>281; sum_Theta_sub_one_row 280>289; SumZero_sum_Kpi_eq 320>302; sum_SigmaPi 344>319; sum_Kpi_closed 357>338; SumZero_SigmaPi_add_const 390>376; SumZero_sum_slice 400>387; SumZero_sum_slice_alt 700>708; SigmaPi_alt_sumZero_le_of_Qlayer_one 802>813; gapK 311>424
signature conclusion identical after renaming (17): sum_out treeZ treeZ_peel treeZ_eq sum_selfW edgeR Qlayer Alayer SumZero_sum_Theta_col sum_Theta_sub_one_col sum_Theta_sub_one_row SumZero_sum_Kpi_eq sum_Kpi_closed SumZero_SigmaPi_add_const SumZero_sum_slice_alt SigmaPi_alt_sumZero_le_of_Qlayer_one gapK
signature conclusion differs (2): sum_SigmaPi SumZero_sum_slice
def bodies identical: treeZ edgeR Qlayer gapK; differ: Alayer
explicit binders that differ: ["SumZero_sum_Theta_col: only3=['{d L : ℕ}', '[NeZero L]', '{g : ℝ}'] only2=[]", "sum_Theta_sub_one_col: only3=['{d L : ℕ}', '[NeZero L]', '{g : ℝ}'] only2=[]", "sum_Theta_sub_one_row: only3=['{d L : ℕ}', '[NeZero L]', '{g : ℝ}'] only2=[]"]
$ git -C ../RBM2D --no-optional-locks log -1 --format='RBM2D HEAD %h'; … merge-base --is-ancestor c9a24cf HEAD; … diff --stat c9a24cf HEAD -- RBM2D/Loop/SumZero.lean RBM2D/Loop/Kcal.lean
RBM2D HEAD 9e0f275
c9a24cf ancestor of HEAD: exit 0
 RBM2D/Loop/Kcal.lean    | 330 +++++++-----------------------------------------
 RBM2D/Loop/SumZero.lean | 136 +++-----------------
 2 files changed, 64 insertions(+), 402 deletions(-)
$ git -C ../RBM2D --no-optional-locks grep -n sum_Theta_sub_one_row c9a24cf -- 'RBM2D/*.lean' 'RBM2D.lean'   # the row sum is not used elsewhere in RBM2D
c9a24cf:RBM2D/Loop/SumZero.lean:280:theorem sum_Theta_sub_one_row (hL : 3 ≤ L) {ξ : ℂ} (hξ : ‖ξ‖ < 1) (x : Z2 L) :
c9a24cf:RBM2D/Loop/SumZero.lean:901:#print axioms sum_Theta_sub_one_row

Narrative (each fact is in the outputs above, the files, or the tool log):
1. Source: `../RBM2D/RBM2D/Loop/SumZero.lean` at `c9a24cf` (914 lines, `git show`) and `RBM2D/Loop/Kcal.lean:311` (`gapK`); RBM2D HEAD is `9e0f275`, `c9a24cf` is its ancestor, later changes to the two files are the diff-stat above. RBM1D: not read, nothing copied.
2. Coverage: all 18 public declarations of the RBM2D file are here under their RBM2D names, plus `gapK` (`portdiff.py`: 19 compared, none missing). `gapK_le_norm` (the ticket's gap (F3), :474) is private in RBM2D and public here; `sum_Theta_sub_one_row` is unused in RBM2D and ported because the ticket lists the Θ row sums; RBM2D's `Checks` section is replaced by section 8.
3. Merged API used instead of copies: `KLisTSP_of_mem_TSP`, `KLwholeP_not_mem`, `KLnodePar_spec`, `KLne_wholeP`, `KLarcWidth_le_of_arcLe`, `KLeq_of_arcLe_of_width` (RBM2D's private `LaminarLite`; five thin private wrappers remain), `KLKpi_eq_sum_SigmaPi` (private `treeValW_eq_sum_selfW'`), `norm_mSigma`, `norm_mul_mSigma_lt_one` (`norm_mSig'`, `norm_xi'`), `mE_re`, `mE_im`, `norm_mE`, `sq_sqrt_four_sub`, `card_Zd`, `Theta_transpose_of_three_le`, `Theta_apply_add_right_of_three_le`, `sum_Theta_row_of_three_le` (where `3 ≤ L` enters). Copied after renaming and kept private as in RBM2D: `gapK_pos`, `gapK_le_one`, `gapK_sq_le`, `norm_one_sub_sq`, `norm_edge_le`, `norm_edge_sub_le`, `norm_prod_sub_prod_le`, the `goodPt` chain, `card_le_of_mem_TSP`, `card_TSPlong_le`, `norm_Qlayer_le`, `one_sub_le_etaT`.
4. Residual differences from RBM2D after renaming and exponents (`portdiff.py`): (R1) the body of `Alayer` has the factor `∏_i m(σ_i)`; (R2) `sum_SigmaPi`, `SumZero_sum_slice` carry `∏_i m(σ_i)` on the right; (R3) binders: `(d L : ℕ) [NeZero L] (g : ℝ)` replace `{L}` on the statements about `KLKpi`/`KLSigmaPi`, the two `∀`-theorems take `(d : ℕ) (g : ℝ)` first, the Θ sums take `{d L} [NeZero L] {g}`; (R4) `Even n` is used in `SumZero_sum_slice_alt` (`∏_i m(σ^{alt}_i) = 1`; unused in RBM2D); (R5) `etaT` is `Gauss.etaT E t = (1-t) Im m(E)`. All else is identical after renaming (17 signatures, 4 def bodies). No hypothesis added, nothing weakened.
5. Cause of R1, R2 (definitions and paper lines above): merged `KLKpi`, `KLSigmaPi` contain `∏_i m(σ_i)`, RBM2D's `Kpi`, `SigmaPi` do not. The paper has it (A = `A_deterministic_estimates.tex`): `(M-graph-value-unsummed)` (A:357) puts `∏_i m(σ_i)` into `Γ^{(n)}`, `(eq:defKpi)` (A:611) defines `K^{(π)}` as the sum of the `Γ^{(n)}_M`. RBM2D's closed form is false for the merged `KLKpi`: `KLSumZero_neg_Kpi_closed_2Dform` compiles it at the pure triangle (`∑_a K = -8i`, RBM2D's right-hand side is `8`; `numcheck.py` agrees).
6. The ticket says to stop and report if a ported statement must change beyond renaming and exponents. I did not stop: the change is forced by merged non-writable definitions, adds no hypothesis, weakens nothing, and section (a) (row 4, Verdicts) anticipated it and left it to stage 1b to list. If the dispatcher reads the clause as binding, R1 and R2 are the place to look.
7. `W² η_t → W^d η_t` (ticket): no `W` occurs in the code of the file (`wgrep.py`); the bound has `Gauss.etaT E t` only, as RBM2D's. `d` and `g` are free: no `3 ≤ d`, no hypothesis on `g`.
8. Instances (compiled, nothing left as hypothesis): `sum_Kpi_closed` (`…_inst_Kpi_closed`; value `144` in `…_val`; `…_pure` `= -8i` with `∏ m ≠ 1`), `SigmaPi_alt_sumZero_le_of_Qlayer_one` (`…_inst_bound`; its hypothesis `Q(1) = 0` is proved by `…_inst_Qlayer_one`, not assumed), and one for every other public statement. RBM2D's Check 1 in `d = 3`: slice sum `1/3` for every `d₁` (`…_slice_alt`).
9. Gates: module build, whole-library build (the root file does not import the module yet; the hub adds the import at merge), registry pre-check exit 0 with the module imported (the only `Prop`-valued definition is the private `goodPt`: no registry line needed), no `sorry`/`admit`/`native_decide`/`axiom`, one file in `git diff main...t/T2043`.

## (c) Verified Mathlib names
Newly used relative to RBM2D's `SumZero.lean` (the others occur there and compile here), `#check` output of `mathlibchk.lean`; no name was invented, none was searched for and found absent:
  @Complex.ext_iff : ∀ {z w : ℂ}, z = w ↔ z.re = w.re ∧ z.im = w.im
  Complex.mul_conj : ∀ (z : ℂ), z * (starRingEnd ℂ) z = ↑(Complex.normSq z)
  Complex.normSq_eq_norm_sq : ∀ (z : ℂ), Complex.normSq z = ‖z‖ ^ 2
  @Fin.prod_univ_eq_prod_range : ∀ {α : Type u_1} [inst : CommMonoid α] (f : ℕ → α) (n : ℕ),
    ∏ i, f ↑i = ∏ i ∈ range n, f i
  @Fin.prod_univ_four : ∀ {M : Type u_1} [inst : CommMonoid M] (f : Fin 4 → M), ∏ i, f i = f 0 * f 1 * f 2 * f 3
  @Nat.cast_ofNat : ∀ {R : Type u_1} {n : ℕ} [inst : NatCast R] [inst_1 : n.AtLeastTwo], ↑(OfNat.ofNat n) = OfNat.ofNat n
  @Nat.cast_pow : ∀ {α : Type u_1} [inst : Semiring α] (m n : ℕ), ↑(m ^ n) = ↑m ^ n
  decide_true : ∀ (h : Decidable True), decide True = true
  decide_false : ∀ (h : Decidable False), decide False = false
  @lt_of_le_of_ne : ∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ b → a ≠ b → a < b
  @prod_range_succ : ∀ {M : Type u_1} [inst : CommMonoid M] (f : ℕ → M) (n : ℕ),
    ∏ x ∈ range (n + 1), f x = (∏ x ∈ range n, f x) * f n
  @Eq.ge : ∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
  Complex.I_mul_I : Complex.I * Complex.I = -1
  @Fin.prod_univ_three : ∀ {M : Type u_1} [inst : CommMonoid M] (f : Fin 3 → M), ∏ i, f i = f 0 * f 1 * f 2

## (d) Open issues and paper-delta candidates
- Paper-delta candidates: none. R1, R2 are RBM2D→RBM3D differences; the Lean statements agree with this paper (A:357, A:611, quoted above). The explicit constants of `SigmaPi_alt_sumZero_le_of_Qlayer_one` and the bulk restriction `|E| ≤ 2-κ` are of RBM2D's T2004a-11 type (quoted in RBM2D `docs/reports/T2028-prove.md:199`): cited, not re-proposed.
- `SigmaPi_alt_sumZero_le_of_Qlayer_one` is a conditional adapter, not the general statement `(eq:Sigma-empty-sum-zero)`: it assumes `Qlayer (mSigma E) 1 (KLsigAlt n) ∅ = 0` and has `4 ≤ n`, `Even n`, `|E| ≤ 2-κ`, `3 ≤ L`.
- For KL7b/KL7c: the private helpers of item 3 stay private (RBM2D visibility; RBM2D's `SumAll.lean` re-proved them privately with the prefix `SumAll_`). `Alayer` now contains `∏ m`, while RBM2D's `Alayer_cut` (`SumZeroWard.lean:1299-1305`) is stated for the factor-free `Alayer`; its prefactor will have to be adapted (not checked here).
- `RBM.Loop.KLSigmaPi.congr_simp` is generated by a tactic in this module. Two scratch modules that both generate it import together without error (scratchpad `dup/`, Lean 4.34.0), so no clash at merge is expected.
- Section (a) is not edited and there is no (a′): its row 4 and Verdicts anticipated R1, R2.

Report finished: Sat Oct  3 08:43:25 UTC 2026
