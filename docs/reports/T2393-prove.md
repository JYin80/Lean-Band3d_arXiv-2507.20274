Prover model: claude-sonnet-5-5

## (a) Math preflight — Sat Oct 10 21:34:50 UTC 2026

### (i) Exponent table and statement

**`STContractM d`** (matrix form; shape of `STContractPt`, `Step2Defs.lean:391-404`).  Binders
`∀ (L W : ℕ) [NeZero L] [NeZero W] (H : Matrix (Idx d L W) (Idx d L W) ℂ) (z : ℂ), H.IsHermitian → 0 < z.im →`.
Write `Mx k := Finset.univ.sup' _ (fun p : (Fin k → Bool) × (Fin k → Zd d L) => ‖loopFine d L W H z p.1 p.2‖)`
(the same `sup'` as `STmaxL`, `Step34Pins.lean:51`; a public `def Contract_maxLoopM` is proposed so the statement is readable) and
`LI I := loopL d L W (blockMat d L W H) z I`.  The conclusion is `(1) ∧ (2)` of `STContract` (`Step34Pins.lean:307-323`) with
`STLI sz n E τ ω ↦ LI`, `STmaxL sz n E τ k ω ↦ Mx k`, `sz.L n, sz.W n ↦ L, W`, `(W^d * etaT E τ)⁻¹ ↦ (W^d * z.im)⁻¹`:
 (1) `∀ m k, 1 ≤ k → k+1 ≤ m → ∀ σ : Fin m → Bool, a : Fin (m-1) → Zd d L,
      Σ_x ‖LI ⟨ofFn σ, ofFn a ++ [x]⟩‖ ≤ (W^d z.im)⁻¹ (Mx(2k-1) Mx(2m-2k-1))^{1/2}`;
 (2) `∀ m k l p j C, 4 ≤ m → 1 ≤ p → 1 ≤ k → k < j+1 → j+1 < l → l+1 ≤ m → 0 ≤ C → ∀ 𝒜, (∀ x, |𝒜 x| ≤ C) → ∀ σ a,
      Σ_x Σ_{y∈𝒜 x} ‖LI ⟨ofFn σ, ofFn (update a j y) ++ [x]⟩‖ ≤ C (W^d z.im)⁻¹ (Mx(2k-1) Mx(2m-2l-1))^{1/2} Mx(2(l-k)p)^{1/(2p)}`
 (`j : Fin (m-1)`, `𝒜 : Zd d L → Finset (Zd d L)`).

**Ticket typo to correct in 1b.**  `loopL` takes a `Vtx`-matrix (`GLoopFlow.lean:123`, `loopL (H : Matrix (Vtx d L W) …)`), so
`loopL d L W H z` with `H : Matrix (Idx ..)` is ill-typed: the statement uses `loopL d L W (blockMat d L W H) z`
(`= loopM d L W (blockMat d L W H) z`, `loopFine` def.).  The band instance is `H := seqHflow sz n τ ω` (a fine-lattice matrix),
not `blockMat (seqHflow …)`; then `STLI sz n E τ ω I` and `STmaxL sz n E τ k ω` are definitionally `LI I`, `Mx k` at `z := zt E τ`
(`Step34Pins.lean:51,107`; `Lloop` at `GLoopFlow.lean:158`, `loopFine` at `GLoopFlow.lean:110`).

| quantity | value / constraint | slack |
|---|---|---|
| `W^d` power, part (1): `‖w‖² = W^{-2d}` (`E_a = w P_a`, `w = W^{-d}`) times `√(W^d M₁/η)√(W^d M₂/η) = (W^d/η)√(M₁M₂)` | `W^{-2d}·W^d/η = (W^d η)⁻¹` (`arith_part1`) | exact, 0 loss |
| `W^d` power, part (2): `‖w‖³`, `√(T^{1/p}) = W^d Mp^{1/(2p)}` (`T = W^{2dp} Mp`), two Ward factors `W^d/η` | `W^{-3d}·W^d·W^d/η = (W^d η)⁻¹` | exact, 0 loss |
| Ward constant `‖(2iη)⁻¹‖ = (2η)⁻¹`, `‖t₁-t₂‖ ≤ 2M` | `‖c(t₁-t₂)‖ ≤ M/η` (`norm_ward_trace_le`) | exact |
| exponent `1/2` (Cauchy–Schwarz, `core1`) and `1/(2p)` (`hs`/power-trace, `rowbound_of_pow`) | `√μ`, `μ = T^{1/p}` | exact |
| word lengths, part (1): `|l| = k-1`, `|r| = m-k-1` | `2|l|+1 = 2k-1`, `2|r|+1 = 2m-2k-1`; needs `1 ≤ k ≤ m-1` (so `m ≥ 2`) | 0 |
| word lengths, part (2): `|l₁| = k-1`, `|r₃| = m-l-1`, `|r₂ y| = l-k-1` | `2k-1`, `2m-2l-1`, `2(l-k-1+1)p = 2(l-k)p`; needs `1 ≤ k < j+1 < l ≤ m-1`, `m ≥ 4`, `p ≥ 1` | 0 |
| where `|E| < 2` enters | only in the corollary: `etaT_pos : |E| < 2 → τ < 1 → 0 < etaT E τ` (`GLoop.lean:83`), `etaT_eq_zt_im : (zt E τ).im = etaT E τ`; gives `0 < Im(zt E τ)`.  `0 ≤ τ` is not used | `STContractM` has no `E`, `τ` |
| `3 ≤ d`, `3 ≤ L` | not used (file docstring; no use in §1-§6) | — |

**Band objects.**  Lines 1-993 of `Contract.lean` (§1-§6) contain none (grep for `sz.|seqH|etaT|STLI|STmax|zt|Lloop|SeqΩ` finds only the docstring line 31).
Band objects in §7 (all to be replaced/generalised in the corollary, none beyond `Im z > 0`): `blockMat_flow_isHermitian`
(from `seqHflow_isHermitian`, `FineModel.lean:531`; matrix form: `hH.submatrix _` of the hypothesis `H.IsHermitian`),
`STLI_eq_trace_wd` (matrix form `loopL .. = trace (wd ..)`, by `unfold loopL; rw [foldr_eq_wd]`), `norm_trace_wd_le_STmaxL`
(matrix form: same `Finset.le_sup'` proof with `loopFine`), `STmaxL_nonneg` (same), `etaT_pos`/`etaT_eq_zt_im`.

**Private lemmas reused unchanged** (§1-§6, all band-free): `hs, hs_nonneg, trace_mul_conjTranspose_eq, norm_trace_mul_le,
sum_mul_pow_le, psd_quad_pow_le, sum_norm_sq_vecMul, rowbound_of_pow, hs_mul_le, norm_trace_mul_mul_le, Gres_conjTranspose, Gres_sub,
sub_conj_eq, Gres_ward_left, Gres_ward_right, wd, wd_append, Ref, Ref_length, wd_Ref, trace_reflect_X, trace_reflect_Y, wd_pow,
length_replicate_flatten, hs_proj, sum_hs_proj_left, sum_hs_proj_right, trace_proj_sandwich, trace_pow_proj, core1, core2, list_split1,
split_set, ofFn_update_eq_set, zip_set_right, list_split2, Pm, Eblk_eq_smul_Pm, Pm_eq_smul_Eblk, Pm_conjTranspose, Pm_mul_self, sum_Pm,
norm_ward_trace_le, norm_Ward_const, alpha_bound, beta_bound, sqrt_mul_sqrt_eq, arith_part1, arith_sqrt_rpow, part1_matrix, part2_matrix`.
`part1_matrix`/`part2_matrix` take `hH : H.IsHermitian` (on `Vtx`), `hz : 0 < z.im`, `Mx`, `hM0`, `hM` and give exactly the sums above.

**Reduction `STContract ⇐ STContractM`.**  `stContract_holds d sz n E τ hE h0 h1 ω := stContractM_holds d (sz.L n) (sz.W n) (seqHflow sz n τ ω)
(zt E τ) (seqHflow_isHermitian sz n τ ω) (by rw [etaT_eq_zt_im.symm]; exact etaT_pos hE h1)`, then rewrite `(zt E τ).im = etaT E τ`
(`etaT_eq_zt_im`) in the bound; the rest is `Iff.rfl`/`id` by the definitional equalities above.  `NeZero (sz.L n)`, `NeZero (sz.W n)`:
`Defs/Sizes.lean:152-153`.  Consumers (`SEforLn1/2`, `Step34Pins`, `Step2Defs`, `ContractPt`) see the unchanged name and statement (G1).

**Plan against stop line 600** (file now 1143 lines; the proof body of §7 moves, it is not duplicated): new `Contract_maxLoopM` + `STContractM`
≈ 30 lines; three matrix-level helpers (`Contract_STLI`-type trace lemma, `Contract_norm_trace_wd_le`, `Contract_maxLoopM_nonneg`) ≈ 30;
`stContractM_holds` (the current proof with `hH hz hM0 hM` as local facts, `STLI_eq_trace_wd` → `loopL` unfold) ≈ 55 net moved;
corollary ≈ 20; the non-band `example`s ≈ 40; net diff estimate +150 to +250, far below 600.

### (ii) One concrete nondegenerate instance

`d = 3, L = 3, W = 2` (`Idx 3 3 2 = Zd 3 6`, `N = (WL)^d = 216` sites, `27` blocks, `W^d = 8`), `z = i` (`Im z = η = 1`, `NeZero 3`, `NeZero 2`).
Hermitian non-band matrices: `H_A` = symmetric 0/1 matrix with one off-diagonal pair (sites `(0,0,0)`,`(0,0,1)`; non-scalar, the analogue of `LoopGenN_M0`,
`LoopGenN.lean:683`, used in the Lean example), `H_B` = random complex Hermitian `(X+X*)/(2√N)`.  Instances of the targets:
part (1) `m=2,k=1` and `m=4,k=2`; part (2) `m=4,k=1,l=3,p=1,j=1` (`k<2<3`, `l+1=4≤4`), `C=1,𝒜 x={x}` and `C=3, 𝒜 x={x,x+e₀,x+e₁}`;
all maxima `Mx k` are taken over every `σ ∈ {±}^k`, `a ∈ Z_3^{3k}` (not just the tested loop).  No external hypothesis (the statement is deterministic:
Hermitian + `Im z>0`), so no limit computation is owed.

Command (numpy installed in a scratch venv; script in the scratchpad, Python, no Lean):
`./v/bin/python3 check.py` (cwd `…/scratchpad/T2393`).  The script asserts: `H` Hermitian; its block-trace `loop()` equals the dense `tr ∏ G(σ_i)E_{a_i}`
(`E_a = W^{-d}P_a`) on two test loops; every inequality `LHS ≤ RHS + 1e-12`.
```
N= 216 blocks= 27 W^d= 8 eta= 1.0
H_A(coordinate, non-scalar) M1..M4= [1.0, 0.125, 0.01562, 0.00195]
 part1 ratios (lhs/rhs) max: 1.0 0.0  part2 (lhs,rhs): [(0.0015869140625, 0.005524271728019903), (0.0015869140625, 0.01657281518405971)]
H_B(random Hermitian, non-band) M1..M4= [0.62856, 0.05035, 0.004, 0.00032]
 part1 ratios (lhs/rhs) max: 0.9999139835192451 0.021821880212048648  part2 (lhs,rhs): [(0.00032981528929920033, 0.0014066998214026741), (0.00036206215823013306, 0.0042200994642080224)]
```
(exit 0, all asserts passed; ratio `0.9999` at `m=2` shows the constant `(W^d η)⁻¹` is sharp, so no slack is hidden in the instance.)
The instance is nondegenerate: `N=216`, all `Mx k > 0`, `L ≥ 3`, no empty index, no collapsed window.

### Verdicts
- Target 1 (`STContractM d`): **PASS** (statement well-formed once `loopL` is applied to `blockMat d L W H`).
- Target 2 (`stContractM_holds`): **PASS** (§1-§6 band-free; proof of §7 transfers verbatim).
- Target 3 (`stContract_holds` as corollary, old name and statement): **PASS** (`|E|<2` enters only via `etaT_pos`).
- Target 4 (G1): **PASS** (definitional equalities above; consumers untouched).
- Target 5 (non-band instance at `d=3`): **PASS** (numerics above; Lean `example` at `Idx 3 3 2`, `z = Complex.I`).

## (a′) Preflight corrections — Sat Oct 10 21:41 UTC 2026

None. (a) already notes that the ticket's `loopL d L W H z` needs `blockMat d L W H`; the statement uses that.

## (b) Script output — Sat Oct 10 21:41 UTC 2026

Stop line: net diff of `Contract.lean` is 130 insertions, 53 deletions = +77 lines (stop line 600); file 1143 -> 1220 lines.
Commit `915114c` on `t/T2393`; `git diff --numstat main...HEAD`: `130 53 RBM3D/Induction/Contract.lean` (only file).

Build: `lake build RBM3D.Induction.Contract` -> `✔ [3706/3706] Built RBM3D.Induction.Contract`, `Build completed successfully`.
Consumers: `lake build RBM3D.Induction.{SEforLn1,SEforLn2,ContractPt,EMn2Poly,EMn2Exp1,EMn2Exp2}` -> `Build completed successfully (3814 jobs)`.
Full `lake build` (includes `#assert_rbm_axioms`) -> `Build completed successfully (4204 jobs)`.
Check file: `lake env lean docs/tickets/checks/T2393-check.lean` -> exit 0 (all `#check`s elaborate).

G1 + axioms (scratch file `lake env lean g1.lean`, exit 0):
```
example : STContract d := stContract_holds d
example : STContractPt d := stContractPt_holds d
example : STContractM d := stContractM_holds d
'RBM.Gauss.Sizes.stContractM_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.stContract_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.Contract_maxLoopM' depends on axioms: [propext, Classical.choice, Quot.sound]
```
`grep -n "sorry\|admit\|native_decide\|^axiom" Contract.lean` -> no matches.
Name clash: `grep -rn "STContractM\|Contract_maxLoopM" RBM3D RBM3D.lean` outside `Induction/Contract.lean` -> 0 matches.

Targets (extracted lines of `RBM3D/Induction/Contract.lean`): `def Contract_maxLoopM` `:1003`, `def STContractM` `:1011`, `theorem stContractM_holds` `:1069`,
`theorem stContract_holds` `:1123` (old name, old statement `STContract d`, untouched in `Step34Pins.lean`).
`STContractM d` (`:1011-1032`): `∀ L W [NeZero L] [NeZero W] (H : Matrix (Idx d L W) (Idx d L W) ℂ) (z : ℂ), H.IsHermitian → 0 < z.im →`
parts (1) and (2) of `STContract` with `STLI ↦ loopL d L W (blockMat d L W H) z`, `STmaxL ↦ Contract_maxLoopM d L W H z`, `(W^d * etaT E τ)⁻¹ ↦ (W^d * z.im)⁻¹`.

Nonempty instances (compiled in the file, §8): the two band examples are kept unchanged; two new examples apply `stContractM_holds 3 3 2` at
`H = coordinateMatrix 3 3 2 (0,1,true) + coordinateMatrix 3 3 2 (1,0,true)` (non-scalar Hermitian on `Idx 3 3 2`, 216 sites; hypotheses `H.IsHermitian` by
`coordinateMatrix_isHermitian`, `0 < Complex.I.im` by `simp`): part (1) at `m=2,k=1`, `σ=(+,-)`, `a=(0)`; part (2) at `m=4,k=1,l=3,p=1,j=1`, `C=1`, `𝒜 x={x}`.
No hypothesis left open.  The corollary `stContract_holds` is applied by the two retained band examples.

Narrative:
- The §7 proof body moved unchanged into `stContractM_holds`, with `STLI_eq_trace_wd`, `norm_trace_wd_le_STmaxL`, `STmaxL_nonneg` replaced by matrix-level private lemmas
  `Contract_loopL_eq_trace_wd`, `Contract_norm_trace_wd_le`, `Contract_maxLoopM_nonneg`; `blockMat_flow_isHermitian` replaced by `hHerm.submatrix _`.
- `stContract_holds` is `stContractM_holds` at `seqHflow sz n τ ω`, `zt E τ`, then `rw [etaT_eq_zt_im]`; `|E| < 2` enters only through `etaT_pos`.
- `Contract_maxLoopM` is public (used in the statement of `STContractM`), prefixed with the file stem.
- §1-§6 untouched.  `3 ≤ d`, `3 ≤ L`, `0 ≤ τ` unused.

## (c) Verified Mathlib / project names

`Matrix.IsHermitian.submatrix` (used as `hHerm.submatrix _`), `Finset.le_sup'`, `Real.sqrt_eq_rpow`, `Complex.I`: all compile in the build above.
Project: `coordinateMatrix`, `coordinateMatrix_isHermitian` (`Gauss/FineModel.lean:384,388`), `etaT_pos`, `etaT_eq_zt_im`, `seqHflow_isHermitian`.

## (d) Open issues and paper-delta candidates

None.  `STContractM` is the matrix form requested by the ticket; ticket typo (`loopL d L W H z` needs `blockMat d L W H`) handled as in (a).
