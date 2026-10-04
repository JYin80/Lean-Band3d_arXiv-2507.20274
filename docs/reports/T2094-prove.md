Prover model: claude-sonnet-5-5

## (a) Math preflight — Sun Oct  4 00:55:29 UTC 2026

Notation (matches `RBM3D/Loop/GLoopFlow.lean:110` `loopFine`, `RBM3D/Loop/GLoop.lean:55` `Eblk`): `E_x = W^{-d} P_x`
(`P_x` = diagonal projection onto block `x`), `𝓛^{(k)}_{σ,a} = tr ∏_i G(σ_i) E_{a_i}`, `G(+) = (H-z)⁻¹`,
`G(-) = (H-z̄)⁻¹ = G(+)^*`, `η = Im z > 0`, `H` Hermitian (so both resolvents exist).
Fix `σ = (σ₁,σ₂)` (Lean `σ 0, σ 1`), `a, b`, `𝒜`, `M`. Write `G₁ = G(σ₁)`, `G₂ = G(σ₂)`, `Ḡ = G(-·)`.

### (i) Exponent table

Proof (paper `3_5:751–797`, `(eq_sym_loop_bound)`, `(eq_sym_loop_bound_old)`; each line re-derived here in the
`E = W^{-d}P` normalization of the Lean `loopFine`, since the paper's displayed `W^{-3d}`, `W^{2d}` factors are written loosely):

1. `𝓛^{(6)}_{c,c'} := 𝓛^{(6)}_{(σ₁,σ₂,σ₁,-σ₁,-σ₂,-σ₁),(a,b,c',b,a,c)} = W^{-6d} tr(Ψ_c A_{c'} Ψ_c^*)`, with
   `Ψ_c = P_c G₁ P_a G₂ P_b` and `A_{c'} = P_b G₁ P_{c'} Ḡ₁ P_b` (cyclicity; `Ψ_c^* = P_b Ḡ₂ P_a Ḡ₁ P_c`).
   `A_{c'}` is Hermitian PSD (`G₁ P Ḡ₁ = (G₁P)(G₁P)^*`).
2. Cauchy–Schwarz / HS: `|tr(Ψ A Ψ^*)| ≤ ‖A‖_op ‖Ψ‖²_HS ≤ ‖A‖_HS ‖Ψ‖²_HS`
   (`|tr(ΨAΨ^*)| = |tr(A Ψ^*Ψ)| ≤ ‖A‖_HS ‖Ψ^*Ψ‖_HS ≤ ‖A‖_HS ‖Ψ‖²_HS`; any of these forms is enough).
3. `𝓛^{(4)}_{(σ₁,-σ₁,σ₁,-σ₁),(c',b,c',b)} = W^{-4d} tr(A_{c'}²) = W^{-4d} ‖A_{c'}‖²_HS ≥ 0` (A Hermitian), so
   `‖A_{c'}‖_HS = W^{2d} ‖𝓛^{(4)}‖^{1/2} ≤ W^{2d} M` for `c' ∈ 𝒜` (this is the hypothesis on `M`).
4. Ward matrix identity `G(+)G(-) = G(-)G(+) = (G(+) - G(-))/(2iη)` (from `G(+) - G(-) = G(+)((H-z̄)-(H-z))G(-)`).
   `Σ_{all c} P_c = I` gives
   `Σ_c ‖Ψ_c‖²_HS = tr(Ψ̃)`, `Ψ̃ = P_b Ḡ₂ P_a Ḡ₁ G₁ P_a G₂ P_b`; equivalently
   `Σ_c 𝓛^{(4)}_{(σ₁,σ₂,-σ₂,-σ₁),(a,b,a,c)} = W^{-d} tr(G₁ E_a G₂ E_b Ḡ₂ E_a Ḡ₁) = W^{-d}(Ĺ_+ - Ĺ_-)/(2iη)` for `σ₁ = +`, where
   `Ĺ_± = 𝓛^{(3)}_{(±,σ₂,-σ₂),(a,b,a)}`; hence `Σ_c ‖Ψ_c‖²_HS = W^{4d}·W^{-d}|Ĺ_+ - Ĺ_-|/(2η) ≤ W^{3d} max(|Ĺ_+|,|Ĺ_-|)/η`.
   (`Σ_c E_c = W^{-d} I`; `|Ĺ_+ - Ĺ_-| ≤ 2 max`.) For `σ₁ = -` the last-label Ward sum has first sign `-`, last sign `+`:
   same identity with `Ĺ_+ ↔ Ĺ_-`, absolute value unchanged (T2063's `sum_gloop_ward_last_div` covers only first `+`, last `-`, D105;
   the other order must be proved in this ticket, or by cyclic rotation, or directly from the matrix identity above).
5. Neighbour multiplicity (Fubini, no symmetry needed): `Σ_{c'∈𝒜} Σ_{c: zdistInf(c-c')≤1} f(c) = Σ_c f(c)·#{c'∈𝒜 : zdistInf(c-c')≤1}`
   for `f ≥ 0`; the map `c' ↦ c - c'` is injective into `{u : zdistInf u ≤ 1}`. Since `zdist L u = min(u.val, L - u.val)`
   (`RBM3D/Defs/Lattice.lean:25`), `zdist L u ≤ 1` ⇔ `u.val ∈ {0,1,L-1}` (≤ 3 values for every `L ≥ 1`), so the count is `≤ 3^d`
   (`= 3^d` for `L ≥ 3`, `≤ L^d ≤ 3^d` for `L ≤ 2`). **This is the only place `3^d` enters.**
6. Assemble: `Σ_{c'∈𝒜}Σ_{c∼c'} ‖𝓛^{(6)}‖ ≤ W^{-6d}·W^{2d} M · 3^d · Σ_c ‖Ψ_c‖²_HS ≤ W^{-4d} M 3^d W^{3d} max/η = 3^d/(W^d η) · M · max_{σ'}‖𝓛^{(3)}‖`.

| quantity | value | constraint / source | slack |
|---|---|---|---|
| prefactor of `𝓛^{(6)}` | `W^{-6d}` | `E_x = W^{-d}P_x`, six `E`'s | exact |
| `‖A_{c'}‖_HS` | `W^{2d}‖𝓛^{(4)}‖^{1/2} ≤ W^{2d} M` | step 3 (identity, then hypothesis `‖𝓛^{(4)}‖^{1/2} ≤ M`) | none (equality in step 3) |
| `Σ_c ‖Ψ_c‖²_HS` | `W^{3d}|Ĺ_+-Ĺ_-|/(2η) ≤ W^{3d} max/η` | step 4 (Ward) | factor `|Ĺ_+-Ĺ_-|/(2 max) ≤ 1`; constant `2η` vs `η`: none after `|a-b| ≤ 2max` |
| neighbour multiplicity | `3^d` | step 5 | none for `L ≥ 3`; `L^d ≤ 3^d` for `L ≤ 2` |
| total power of `W` | `-6d + 2d + 3d = -d` | pin has `1/(W^d η)` | exact |
| total constant | `3^d · 1/η` | pin: `3^d/(W^d η)` | exact, no loss; no `d ≥ 3` use |
| `Im z` | `η > 0` | pin hyp. `0 < z.im`; Ward needs `η ≠ 0`; resolvents exist by Hermitian + `η ≠ 0` | — |
| `M` | `M ≥ 0` | pin hyp. (follows from `‖·‖^{1/2} ≤ M` on nonempty `𝒜`; for `𝒜 = ∅` LHS `= 0`) | — |
| `L, W` | `NeZero` only | `3 ≤ L`, `3 ≤ d` not needed | — |

The pin (`RBM3D/Induction/Step2Defs.lean:391`) as written matches steps 1–6 (labels `![a,b,c',b,a,c]`, signs `![σ0,σ1,σ0,!σ0,!σ1,!σ0]`,
alternating loop `![σ0,!σ0,σ0,!σ0]` at `![c',b,c',b]`, `max` over `true/false` of `𝓛^{(3)}_{(·,σ1,!σ1),(a,b,a)}`):
the statement is true; the ratio `0.39` of T2039 is `< 1`, and the check below gives ratios `≤ 0.105`.

### (ii) Concrete nondegenerate instance and numerical check

`d = 3`, `L = 4`, `W = 2` (`N = (WL)^d = 512`, 64 blocks of size 8, each block has exactly `3^3 = 27` neighbours), one random
complex Hermitian `H` (seed 1, scale `‖H‖ ≈ 2`), `z = 0.3 + 0.1i`, `a = (0,0,0)`, `b = (2,3,1)`, all four `σ ∈ {±}²`, and three `𝒜`:
all 64 blocks; 12 random blocks; the 27-block neighbourhood of `(0,0,0)`. `M = max_{c'∈𝒜} ‖𝓛^{(4)}_{alt,(c',b,c',b)}‖^{1/2}`
(so `M > 0`, `𝒜` nonempty). Loops are computed literally as `tr ∏ G(σ_i) E_{a_i}` with `E_x = W^{-d}P_x`.
Scripts (Python/numpy, no Lean): `scratchpad/T2094/ratio.py`, `scratchpad/T2094/steps.py`
(`/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/e2e8bc03-a5c7-4581-b49e-f30bd123d3b2/scratchpad/T2094/`).

```
$ python3 ratio.py
direct vs fast: 6.617444900424222e-24
A=all          sigma=(+,+) lhs=8.193449e-05 rhs=1.485476e-03 ratio=0.0552
A=all          sigma=(+,-) lhs=7.470807e-05 rhs=1.340880e-03 ratio=0.0557
A=all          sigma=(-,+) lhs=8.161973e-05 rhs=1.485476e-03 ratio=0.0549
A=all          sigma=(-,-) lhs=7.406546e-05 rhs=1.340880e-03 ratio=0.0552
A=random12     sigma=(+,+) lhs=1.279848e-05 rhs=3.453667e-04 ratio=0.0371
A=random12     sigma=(+,-) lhs=1.327722e-05 rhs=3.117488e-04 ratio=0.0426
A=random12     sigma=(-,+) lhs=1.472654e-05 rhs=4.031583e-04 ratio=0.0365
A=random12     sigma=(-,-) lhs=1.281608e-05 rhs=3.639149e-04 ratio=0.0352
A=nbhd(0,0,0)  sigma=(+,+) lhs=3.525221e-05 rhs=3.547560e-04 ratio=0.0994
A=nbhd(0,0,0)  sigma=(+,-) lhs=3.354198e-05 rhs=3.202241e-04 ratio=0.1047
A=nbhd(0,0,0)  sigma=(-,+) lhs=3.658290e-05 rhs=4.031583e-04 ratio=0.0907
A=nbhd(0,0,0)  sigma=(-,-) lhs=3.315002e-05 rhs=3.639149e-04 ratio=0.0911
$ python3 steps.py     # (a,b,c') = ((0,0,0),(2,3,1),(1,1,0)), sigma = (+,-)
Ward matrix id err: 1.4242292162688902e-13
||A||_HS vs W^2d sqrt|L4|: 0.4400576361429182 0.4400576361429182  L4 imag: -7.533332361867436e-19
sum_c||Psi_c||^2 vs W^3d/(2eta)|L3+-L3-|: 5.892318803127723 5.89231880312775
max over c~c' of |L6|/(W^-6d ||A|| ||Psi_c||^2): 0.29080480805899
```

(`direct vs fast` compares the literal six-fold matrix product with the factored `tr(Y P_c)` evaluation used for the table; the
`steps.py` lines confirm items 3, 4 and the pairwise bound of steps 1–3 numerically, ratio `0.29 ≤ 1`.)
All 12 ratios `< 1`; every hypothesis of the pin (`H` Hermitian, `Im z = 0.1 > 0`, `M ≥ 0`, `‖𝓛^{(4)}‖^{1/2} ≤ M` on `𝒜`) holds with
`N = 512`, `W^d = 8`, nonempty `𝒜`, nonzero loops. The pin is deterministic; there is no external hypothesis, so no limit computation
applies.

### Verdict
- `stContractPt_holds` (`STContractPt d`, all `d`, `L`, `W` with `NeZero`): **PASS**. The statement is true as written, with exact constants
  (`3^d/(W^d η)`, no loss), proved by steps 1–6. Only extra task beyond reuse: Ward with first sign `-` (D105), and the neighbour count `≤ 3^d` for all `L ≥ 1`.

## (b) Script output — Sun Oct  4 01:13:10 UTC 2026

Commit `f271fb0` on `t/T2094` (one new file). Worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2094`.

```
$ git log -1 --format="%h %an <%ae> %s"; git diff --name-only main...t/T2094
f271fb0 Jun Yin <321276894+JYin80@users.noreply.github.com> T2094: ST2-08 Induction/ContractPt (proves STContractPt)
RBM3D/Induction/ContractPt.lean

$ lake build RBM3D.Induction.ContractPt 2>&1 | grep -E "ContractPt|Build completed|error"
Build completed successfully (3721 jobs).

$ lake env lean axioms.lean   # import RBM3D.Induction.ContractPt; #print axioms ...; #check @...
'RBM.Gauss.Sizes.stContractPt_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
RBM.Gauss.Sizes.stContractPt_holds : ∀ (d : ℕ), RBM.Gauss.Sizes.STContractPt d

$ sed -n 459,463p RBM3D/Induction/ContractPt.lean   # the target, as stated in the file
/-- **`STContractPt`** (`ygdhmsgq0`, `(eq_sym_loop_bound)`, `3_5:751-797`): the pointwise
contraction inequality of Step 2 holds for every `d`, `L`, `W`, every Hermitian `H` on the fine
lattice and every `z` with `Im z > 0`: deterministic, no hypothesis beyond those of the pin; the
constant `3^d / (W^d Im z)` is exact. -/
theorem stContractPt_holds (d : ℕ) : STContractPt d := by

$ sed -n 391,400p RBM3D/Induction/Step2Defs.lean   # the pin (merged; branch base 0fc2597)
def STContractPt (d : ℕ) : Prop :=
  ∀ (L W : ℕ) [NeZero L] [NeZero W] (H : Matrix (Idx d L W) (Idx d L W) ℂ) (z : ℂ),
    H.IsHermitian → 0 < z.im → ∀ (σ : Fin 2 → Bool) (a b : Zd d L) (𝒜 : Finset (Zd d L)) (M : ℝ),
      0 ≤ M →
      (∀ c' ∈ 𝒜, ‖loopFine d L W H z ![σ 0, !(σ 0), σ 0, !(σ 0)] ![c', b, c', b]‖ ^ (1 / 2 : ℝ) ≤ M) →
        ∑ c' ∈ 𝒜, ∑ c ∈ Finset.univ.filter (fun c : Zd d L => zdistInf d L (c - c') ≤ 1),
            ‖loopFine d L W H z ![σ 0, σ 1, σ 0, !(σ 0), !(σ 1), !(σ 0)] ![a, b, c', b, a, c]‖ ≤
          3 ^ d / (((W : ℕ) : ℝ) ^ d * z.im) * M *
            max ‖loopFine d L W H z ![true, σ 1, !(σ 1)] ![a, b, a]‖
              ‖loopFine d L W H z ![false, σ 1, !(σ 1)] ![a, b, a]‖

$ grep -n "sorry\|admit\|native_decide\|^axiom" RBM3D/Induction/ContractPt.lean; echo "grep exit: $? (1 = no match)"
grep exit: 1 (1 = no match)

$ grep -nE "^(noncomputable )?(theorem|lemma|def|abbrev|instance|structure)" RBM3D/Induction/ContractPt.lean   # public declarations
463:theorem stContractPt_holds (d : ℕ) : STContractPt d := by

$ grep -rln "stContractPt_holds" RBM3D ../../RBM2D/RBM2D ../../RBM1D/RBM1D
RBM3D/Induction/ContractPt.lean
```

Registry pre-check (DECISIONS §20 rule 2): temporary uncommitted file `scratchpad/T2094/precheck.lean`
= `import RBM3D` + `import RBM3D.Induction.ContractPt` + `#print axioms …` + `#assert_rbm_axioms`:

```
$ lake env lean precheck.lean > precheck.out 2>&1; echo "exit: $?"
exit: 0
$ grep -E "^'RBM.Gauss|^axiom audit|^registry:" precheck.out
'RBM.Gauss.Sizes.stContractPt_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
axiom audit: 2948 theorems, 1136 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
registry: 5 borrowed + 92 owed + 37 structural; 55 registered premise(s) carry nothing yet: [RBM.ThetaDiffOne,
```

`RBM3D/Test/Axioms.lean` and `RBM3D.lean` are unchanged on the branch (`git diff --name-only main...t/T2094` above).
The full `lake build` in the worktree (root as committed, without the new import) ended `Build completed successfully
(3834 jobs)`.

### The compiled nonempty instances (extracted: `sed -n 579,634p RBM3D/Induction/ContractPt.lean`)

```lean
private noncomputable def ptH : Matrix (Idx 3 3 2) (Idx 3 3 2) ℂ :=
  Matrix.of fun i j => (((i 0).val + (j 0).val : ℕ) : ℂ)

private theorem ptH_herm : ptH.IsHermitian := by
  ext i j
  simp only [Matrix.conjTranspose_apply, ptH, Matrix.of_apply]
  rw [add_comm (j 0).val, star_natCast]

private def ptZ : ℂ := ⟨1 / 2, 1 / 4⟩

private theorem ptZ_im : 0 < ptZ.im := by
  change (0 : ℝ) < 1 / 4
  norm_num

private def ptB : Zd 3 3 := fun _ => 1

private noncomputable def ptM (σ0 : Bool) (𝒜 : Finset (Zd 3 3)) : ℝ :=
  ∑ c' ∈ 𝒜, ‖loopFine 3 3 2 ptH ptZ ![σ0, !σ0, σ0, !σ0] ![c', ptB, c', ptB]‖ ^ (1 / 2 : ℝ)

private theorem ptM_nonneg (σ0 : Bool) (𝒜 : Finset (Zd 3 3)) : 0 ≤ ptM σ0 𝒜 :=
  Finset.sum_nonneg fun _ _ => by positivity

private theorem ptM_bound (σ0 : Bool) (𝒜 : Finset (Zd 3 3)) :
    ∀ c' ∈ 𝒜, ‖loopFine 3 3 2 ptH ptZ ![σ0, !σ0, σ0, !σ0] ![c', ptB, c', ptB]‖ ^ (1 / 2 : ℝ) ≤
      ptM σ0 𝒜 := fun c' hc' =>
  Finset.single_le_sum (f := fun c' => ‖loopFine 3 3 2 ptH ptZ ![σ0, !σ0, σ0, !σ0]
    ![c', ptB, c', ptB]‖ ^ (1 / 2 : ℝ)) (fun _ _ => by positivity) hc'

/-- The instance matrix has `N = 216` sites. -/
example : Fintype.card (Idx 3 3 2) = 216 := by
  rw [RBM.Gauss.card_Idx]; norm_num

/-- `stContractPt_holds` at `d = 3`, `L = 3`, `W = 2`, `σ = (+,-)`, `a = 0`, `b = (1,1,1)`,
`𝒜 = {0, b}`, `z = 1/2 + i/4`. -/
example :
    ∑ c' ∈ ({0, ptB} : Finset (Zd 3 3)),
        ∑ c ∈ Finset.univ.filter (fun c : Zd 3 3 => zdistInf 3 3 (c - c') ≤ 1),
          ‖loopFine 3 3 2 ptH ptZ ![true, false, true, false, true, false]
            ![0, ptB, c', ptB, 0, c]‖ ≤
      3 ^ 3 / ((((2 : ℕ) : ℝ)) ^ 3 * ptZ.im) * ptM true {0, ptB} *
        max ‖loopFine 3 3 2 ptH ptZ ![true, false, true] ![0, ptB, 0]‖
          ‖loopFine 3 3 2 ptH ptZ ![false, false, true] ![0, ptB, 0]‖ :=
  stContractPt_holds 3 3 2 ptH ptZ ptH_herm ptZ_im ![true, false] 0 ptB {0, ptB}
    (ptM true {0, ptB}) (ptM_nonneg _ _) (ptM_bound true {0, ptB})

/-- `stContractPt_holds` at the same data with `σ = (-,+)` (first sign `-`) and `𝒜 = Z_L^d`. -/
example :
    ∑ c' ∈ (Finset.univ : Finset (Zd 3 3)),
        ∑ c ∈ Finset.univ.filter (fun c : Zd 3 3 => zdistInf 3 3 (c - c') ≤ 1),
          ‖loopFine 3 3 2 ptH ptZ ![false, true, false, true, false, true]
            ![0, ptB, c', ptB, 0, c]‖ ≤
      3 ^ 3 / ((((2 : ℕ) : ℝ)) ^ 3 * ptZ.im) * ptM false Finset.univ *
        max ‖loopFine 3 3 2 ptH ptZ ![true, true, false] ![0, ptB, 0]‖
          ‖loopFine 3 3 2 ptH ptZ ![false, true, false] ![0, ptB, 0]‖ :=
  stContractPt_holds 3 3 2 ptH ptZ ptH_herm ptZ_im ![false, true] 0 ptB Finset.univ
    (ptM false Finset.univ) (ptM_nonneg _ _) (ptM_bound false Finset.univ)
```

Data: `d = 3`, `L = 3`, `W = 2`, `N = (W L)^d = 216` (the first `example`, proved by `rw [RBM.Gauss.card_Idx]; norm_num`), 27 blocks
of `W^d = 8` sites, `H_{ij} = (i)_0 + (j)_0` (real symmetric, so Hermitian; not block diagonal; not a multiple of `1`),
`z = 1/2 + i/4`, `a = 0`, `b = (1,1,1)`, `𝒜 = {0, b}` resp. all 27 blocks (nonempty), both orders of `σ`. Hypotheses
discharged in Lean: `H.IsHermitian` (`ptH_herm`), `0 < Im z` (`ptZ_im`), `0 ≤ M` (`ptM_nonneg`), the bound on `M`
(`ptM_bound`, `M = Σ_{c'∈𝒜} ‖𝓛^{(4)}‖^{1/2}` dominates each term). The pin has no other hypothesis.

Independent numerical sanity check of the same data (numpy, not part of the Lean proof; `scratchpad/T2094/inst.py`,
loops computed literally as `tr ∏ G(σ_i) E_{a_i}`, `E_x = W^{-d} P_x`, block of a site `= site // W` per coordinate as in
`RBM3D/Defs/Sizes.lean` `blk`): both sides are nonzero.

```
$ python3 inst.py
ex1 A={0,b} sigma=(+,-) M=1.401415e-01 max|L3|=1.567880e-05 lhs=1.640449e-07 rhs=2.966287e-05 ratio=0.0055
ex2 A=all sigma=(-,+) M=1.419933e-01 max|L3|=1.567880e-05 lhs=1.693973e-07 rhs=3.005484e-05 ratio=0.0056
```

### Narrative

- `stContractPt_holds (d : ℕ) : STContractPt d` is the only public declaration of the file (grep above); its type is the merged pin
  `RBM3D/Induction/Step2Defs.lean:391` verbatim (`#check` above). All other declarations are `private`.
- Proof, in the notation of (a), `P_x = W^d E_x` (`Pm`), `G = Gres (blockMat H) z`, `Ψ_c = P_c G₁ P_a G₂ P_b` (`Psi`),
  `A_{c'} = P_b G₁ P_{c'} Ḡ₁ P_b` (`Amat`), `K = G₁ P_a G₂ P_b Ḡ₂ P_a Ḡ₁` (`Kmat`):
  1. `loop6_eq`: `𝓛^{(6)}_{c,c'} = (W^d)^{-6} tr(Ψ_c A_{c'} Ψ_c^*)` (via `Psi_mul_Amat_mul_conj`, `P_b P_b = P_b`, `trace_Pm_sandwich`).
  2. `norm_trace_mul_mul_conjTranspose_le`: `‖tr(Ψ A Ψ^*)‖ ≤ √(hs A) · hs Ψ`, by Cauchy-Schwarz over the index pair of `A`
     (`sum_pair_le`; no operator norm is needed).
  3. `loop4_eq`, `hs_Amat`: `𝓛^{(4)}_{alt} = (W^d)^{-4} hs(A_{c'})` (`A_{c'}` Hermitian, `Amat_conjTranspose`); with the hypothesis
     `‖𝓛^{(4)}‖^{1/2} ≤ M` this gives `√(hs A_{c'}) ≤ W^{2d} M`. Hence `hpt`: `‖𝓛^{(6)}‖ ≤ W^{-4d} M hs(Ψ_c)`.
  4. `sum_hs_Psi`, `trace_Kmat`, `loop3_eq`: `Σ_c hs(Ψ_c) = tr K = (2iη)⁻¹ (tr(G(+)Y) - tr(G(-)Y))`, `Y = P_a G₂ P_b Ḡ₂ P_a`,
     and `tr(G(s)Y) = W^{3d} 𝓛^{(3)}_{(s,σ₂,-σ₂),(a,b,a)}`; so `Σ_c hs(Ψ_c) ≤ W^{3d} max_s ‖𝓛^{(3)}_s‖ / Im z`.
  5. `sum_neighbours_le`, `card_ball_le`, `zdist_le_one`: `Σ_{c'∈𝒜} Σ_{c∼c'} q(c) ≤ 3^d Σ_c q(c)` for `q ≥ 0`
     (`#{u : zdistInf u ≤ 1} ≤ 3^d` for every `L ≥ 1`, from `zdist L u ≤ 1 ⇒ u ∈ {0, 1, -1}`).
  6. Assembly (last `calc` of `stContractPt_holds`): `W^{-4d} · M · 3^d · W^{3d} max/η = 3^d/(W^d η) · M · max`, exactly the pin.
- Ward's identity is used in the matrix form `G(-σ) G(σ) = (2iη)⁻¹ (G(+) - G(-))` (`Gres_ward_left`), which holds for either charge
  `σ`; the case `σ₁ = -` (D105: T2063's `sum_gloop_ward_last_div` covers only first sign `+`) therefore needs no separate argument, and
  T2063's lemma is not used. The second instance has `σ = (-,+)`.
- No port from RBM1D/RBM2D (the ticket has none); `git -C ../RBM2D --no-optional-locks diff --stat` does not apply. The generic
  helpers `hs`, `hs_nonneg`, `trace_mul_conjTranspose_eq`, `Gres_conjTranspose`, `Gres_sub`, `sub_conj_eq`, `Gres_ward_left`, `Pm`,
  `Eblk_eq_smul_Pm`, `Pm_conjTranspose`, `Pm_mul_self`, `sum_Pm` are copied from the merged `RBM3D/Induction/Contract.lean` (T2054, last
  commit of that file `86368fa`; file:line in each docstring), where they are `private`; `Gres_sub` is kept whole, `Psi`, `Amat`, `Kmat`,
  `norm_trace_mul_mul_conjTranspose_le`, the loop and neighbour lemmas and the pin are new. `Contract.lean` is not imported (nothing from it is
  public); the file imports `Step2Defs` and `ConArgDet` only.
- `3 ≤ d` and `3 ≤ L` are not used; `L`, `W` need only `NeZero`. The constant `3^d/(W^d Im z)` is exact (no loss).
- Registry: `RBM3D/Test/Axioms.lean` is not edited. Its `owedProps` line for `RBM.Gauss.Sizes.STContractPt` (line 132 on this branch)
  can go once this merges (the pre-check above passes with it present); DECISIONS §20 rule 1 says registry edits only append, so the
  removal is left to the dispatcher.
- No (a′): no statement of (a) was found wrong while proving (the Ward identity for first sign `-` and the neighbour count were its two flagged extras).

## (c) Verified Mathlib / project names (`env.find?` hit, defining module in brackets, `M.` = `Mathlib.`; script `scratchpad/T2094/names.lean`)

```
Real.sum_mul_le_sqrt_mul_sqrt (M.Analysis.Real.Sqrt)  Real.sqrt_sq (M.Analysis.Real.Sqrt)
Real.sqrt_le_iff (M.Analysis.Real.Sqrt)  Real.sqrt_le_left (M.Analysis.Real.Sqrt)
Real.sqrt_eq_rpow (M.Analysis.SpecialFunctions.Pow.Real)  Matrix.trace_mul_comm (M.LinearAlgebra.Matrix.Trace)
Matrix.trace_sum (M.LinearAlgebra.Matrix.Trace)  Matrix.trace_smul (M.LinearAlgebra.Matrix.Trace)
Matrix.trace_sub (M.LinearAlgebra.Matrix.Trace)  Matrix.conjTranspose_mul (M.LinearAlgebra.Matrix.ConjTranspose)
Matrix.isHermitian_diagonal_iff (M.LinearAlgebra.Matrix.Hermitian)  Matrix.IsHermitian.submatrix (M.LinearAlgebra.Matrix.Hermitian)
Finset.card_le_three (M.Data.Finset.Card)  Finset.card_le_card_of_injOn (M.Data.Finset.Card)
Fintype.card_piFinset (M.Data.Fintype.BigOperators)  Fintype.mem_piFinset (M.Data.Fintype.Pi)
ZMod.natCast_zmod_val (M.Data.ZMod.Basic)  ZMod.natCast_self (M.Data.ZMod.Basic)
Finset.single_le_sum (M.Algebra.Order.BigOperators.Group.Finset)  star_natCast (M.Algebra.Star.Basic)
Complex.ofReal_sum (M.Basic.Complex.BigOperators)  Complex.norm_real (M.Analysis.Complex.Norm)
Complex.norm_natCast (M.Analysis.Complex.Norm)  eq_neg_of_add_eq_zero_left (M.Algebra.Group.DivInvMonoid)
Nat.pow_le_pow_left (Init.Data.Nat.Basic)  Finset.sum_comm (M.Algebra.BigOperators.Group.Finset.Sigma)
Complex.sub_conj (M.Basic.Complex.Basic)  Matrix.conjTranspose_nonsing_inv (M.LinearAlgebra.Matrix.NonsingularInverse)
Matrix.nonsing_inv_eq_ringInverse (M.LinearAlgebra.Matrix.NonsingularInverse)  RBM.isUnit_sub_smul_of_isHermitian (RBM3D.Analysis.Resolvent)
```
Names verified absent: none searched.

## (d) Open issues and paper-delta candidates

- T2094a (statement form, already in the merged pin): the paper's `≲` in `(eq_sym_loop_bound)` is the explicit constant `3^d/(W^d η_t)`
  (sharp), and the left side is `Σ ‖𝓛^{(6)}‖` and the maximum is `max_{σ'} ‖𝓛^{(3)}‖` (norms; the paper's `𝓛^{(4)}_{alt}` is real and
  nonnegative: `= W^{-4d} hs(A_{c'})`, `loop4_eq`/`hs_Amat`). `max_{c'∈𝒜} (𝓛^{(4)}_{alt})^{1/2}` is the hypothesis `‖𝓛^{(4)}‖^{1/2} ≤ M` on `𝒜`.
- T2094b (observation, docstring of the pin `Step2Defs.lean:380-390`): it quotes the T2039 ratio `0.39`; the (a) check gives ratios `≤ 0.105`
  at its data and `0.0055`, `0.0056` at the instance data above. The statement is true as written; only the quoted number is a different sample.
- The statement is the pointwise inequality `(eq_sym_loop_bound)` only; the symmetric partner `(eq_sym_loop_bound2)` (`3_5:758`) is not
  a target of this ticket and is not proved here.
- A full `lake build` with the module temporarily imported in `RBM3D.lean` and the `STContractPt` registry line temporarily deleted (both
  reverted before the commit) also ended `Build completed successfully (3835 jobs)`.
