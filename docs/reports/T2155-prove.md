Prover model: claude-sonnet-5-5
## (a) Math preflight — Sun Oct  4 18:58:13 UTC 2026

Target (`stExpInv_holds d : STExpInv d`, `RBM3D/Induction/Step5Pins.lean:441-446`): for `sz : Sizes d`, `n`, `|E|<2`, `0≤u<1`, `σ : Fin 2 → Bool`, `a : Fin 2 → Zd d (L_n)`, `c`:
`∫ Lloop sz n E u σ (a+c) d seqP = ∫ Lloop … a d seqP` and `∫ Lloop … (-a) d seqP = ∫ Lloop … a d seqP`.  Instances `stExpInv_holds 3`, and both identities at `sz0`, `n=0`, `E=0`, `u=1/2` (`sz0`: `Defs/Sizes.lean:260`, `L_0=4`, `W_0=32`, `lam_0=1/64`).

### (i) Exponent table (no exponents occur; the parameters and constants the target depends on)

| item | value / range | constraint | slack |
|---|---|---|---|
| `d` | any `ℕ` (instance `d=3`) | none: `Zd d L = Fin d → ZMod L`, `3 ≤ d` not used | unlimited |
| `L_n`, `W_n` | `L_n ≥ 3` (`Sizes.three_le_L`), `W_n ≥ 1` | only `NeZero L_n`, `NeZero W_n` (`Sizes.neZeroL/neZeroW`) are used; `3 ≤ L` is not needed (no `Θ`, no `𝒦`) | `L_0=4` vs 3; `W_0=32` vs 1 |
| `lam_n = g` | any real (`sz0`: `1/64`) | `S^{(B)}` enters only through `SBR d L g` (`Propagator/Props4.lean:48`), the kernel `sbKernelR` (`Defs/Block.lean:74`); `sbKernelR_neg` (`Block.lean:84`) holds for every real `g` | unlimited |
| `\|E\|<2`, `0≤u<1` | `E=0`, `u=1/2` at the instance | **not used** by the proof: `Lloop = loopFine (seqHflow) (zt E u)` (`Loop/GLoopFlow.lean:158-160`) is the trace of a product of `Gres H z σ = Ring.inverse (H - z̄^{[σ=false]}·1)` (`GLoopFlow.lean:74`) and `Eblk`; the relabelling identity holds for every `H`, `z` (equivariance of the inverse), so the RBM2D `Kcal_two`/`Theta` step (`MLExpInv.lean` §1 second half, lines 66-128 of c9a24cf) is not ported | the two hypotheses are slack (statement is true without them) |
| translation `c`, label `a` | `c ∈ Zd d L_n`, `a : Fin 2 → Zd d L_n` | block automorphism `T = (·+c)` or `T = (-·)`: `SBR (T a)(T b) = SBR a b` | exact |
| `idxKey` | `Fintype.equivFin` (`FineModel.lean:73`) | only injectivity (`idxKey_injective`, `FineModel.lean:75`) is used; the script uses a random key | exact |
| time `u`, `√u` | `(√u : ℂ)` scalar in `seqHflow` (`FineModel.lean:225-227`) | the same scalar on both sides: `seqHflow (Φω) = (seqHflow ω)_{φ,φ}` is linear in `Xmat` | exact |

Ticket/merged-name discrepancies found (for the prover; mathematics unchanged):
- The ticket's route (i) names `SB_apply`, `sbKernel_neg`; the merged `svarF` is defined through `SBR`/`sbKernelR` (`FineModel.lean:47-48`: `svarF i j = (W^d)⁻¹ * SBR d L g (split i).1 (split j).1`), so the kernel steps are `sbKernelR_neg` (`Defs/Block.lean:84`) and `add_sub_add_right_eq_sub`, not `SB_apply`/`sbKernel_neg`.
- The merged model has the single-time flow `seqHflow` and `Lloop` depends on `ω` only through `slice sz n ω`; the pin integrates against `seqP` (all sizes), so step (v) needs a measure-preserving `Φ` of `SeqΩ sz` acting on the size-`n` coordinates only (RBM2D `MLExpInv_seq`, c9a24cf:451 with a family `φ m` equal to the identity for `m ≠ n`, as in `MLExpInv_integral_eq`, c9a24cf:534).  `seqP_map_slice` alone gives the law of the slice but integrating an arbitrary (not shown measurable) `F ∘ slice` over it would need measurability of `F`.
- Source version: the ticket cites `c9a24cf` (878 lines); `git -C ../RBM2D log -1` is now `9e0f275` and the file at that HEAD has 815 lines, so the prover must read `git -C ../RBM2D show c9a24cf:RBM2D/Evolution/MLExpInv.lean`.

### Route (i)-(v) with the merged statements used (one line per step)

Let `T : Zd d L ≃ Zd d L` be `Equiv.addRight c` or `Equiv.neg _`.
1. (i) `SBR d L g (T a)(T b) = SBR d L g a b`: translation by `(a+c)-(b+c) = a-b`; negation by `sbKernelR_neg` (`Block.lean:84`) on `(-a)-(-b) = -(a-b)`.  Hypothesis form `∀ a b, SBR (T a)(T b) = SBR a b` replaces RBM2D `MLExpInv_Aut`.
2. (ii) `φ := splitEquiv.trans (Equiv.prodCongr T (Equiv.refl _)) |>.trans splitEquiv.symm` on `Idx d L W` (`splitEquiv`, `Defs/Sizes.lean:87`; block label moved by `T`, offset kept; for `T = neg` this is not the group negation of `Z_{WL}^d`).  Then `(split (φ i)).1 = T (split i).1`, hence `svarF (φ i)(φ j) = svarF i j` (`svarF` unfolds at `FineModel.lean:47-48`), and `gvarF ∘ π = gvarF` (`gvarF`, `FineModel.lean:89`): diagonal `S_ii` equal, off-diagonal `S_ij/2` equal, reversed pair uses `svarF_comm` (`FineModel.lean:54`).
3. (iii) coordinate bijection `π(i,j,b) = (φi,φj,b)` if `idxKey i < idxKey j ↔ idxKey (φi) < idxKey (φj)` else `(φj,φi,b)` (bijection: injective on a finite type); `Φω(c) = −ω(π c)` for `c = (i,j,false)` with reversed orientation, `ω(π c)` otherwise.  Then `Xentry (Φω) i j = Xentry ω (φ i)(φ j)` (case split by `idxKey`, `Xentry` at `FineModel.lean:105`), i.e. `Xmat (Φω) = (Xmat ω).submatrix φ φ`; and `Φ_* PF = PF` (see (ii) below).
4. (iv) `blockMat (M.submatrix φ φ) = (blockMat M).submatrix ψ ψ` with `ψ = T × id` on `Vtx d L W = Zd d L × Fin (W^d)` (`blockMat`, `GLoopFlow.lean:105`); `Gres (H.submatrix ψ ψ) z σ = (Gres H z σ).submatrix ψ ψ` (`Gres` is `Ring.inverse`, `GLoopFlow.lean:74`; `ψ` an equivalence); `(Eblk (T a)).submatrix ψ ψ = Eblk a` (`Loop/GLoop.lean:55`: diagonal, weight `W^{-d}·1[x.1 = a]`); trace invariant under `ψ`; so `loopM (H.submatrix ψ ψ) z σ a = loopM H z σ (T∘a)` and `loopFine (M_{φ,φ}) z σ a = loopFine M z σ (T∘a)` (`loopFine`, `GLoopFlow.lean:110`).  With `H = seqHflow ω`: `seqHflow (Φω) = (seqHflow ω)_{φ,φ}` (`seqHflow = √u • Xmat (slice ω)`), so `Lloop (a)(Φω) = Lloop (T∘a)(ω)`.
5. (v) `Φ` lifts to a measurable equivalence of `SeqΩ sz` preserving `seqP` (`seqP = infinitePi` of Gaussians, `FineModel.lean:169`; reindexing of coordinates by `π`, sign flips of the `false`-coordinates in the reversed pairs; `gaussianReal 0 v` is symmetric; `seqGvar` at size `n` is `gvarF … (sz.lam n)`, `FineModel.lean:164`), so `∫ Lloop(a) d seqP = ∫ Lloop(a)(Φω) d seqP = ∫ Lloop(T∘a) d seqP` for arbitrary integrands (`MeasurePreserving.integral_comp'`, no measurability needed).  Both identities of the pin follow: `T = addRight c` and `T = neg`; `T∘(a) = fun i => a i + c`, `fun i => -a i`.  Consistency with the paper: `3_5:2196-2200` ("by the translation invariance and symmetry of our model on the block level") — the pin is exactly the `𝔼𝓛^{(2)}` form of the two stated properties.

### (ii) Negation: which pairs reverse, and why `PF` is preserved

- `φ` is a bijection of the fine lattice, not order-preserving for `idxKey`.  Pair `(i,j)` is *reversed* iff `idxKey i < idxKey j` and `idxKey(φj) < idxKey(φi)` (or the converse).  For `T = neg` and `T = (·+c)` both kinds occur: the script counts the reversed real-pairs `(i,j,true)`, `i≠j`: 364 (translation) and 338 (negation) at `d=3,L=3,W=1` (of `N(N-1)=702` ordered pairs).
- For a preserved pair `Φω(i,j,b) = ω(φi,φj,b)`; for a reversed pair `Φω(i,j,true) = ω(φj,φi,true)`, `Φω(i,j,false) = −ω(φj,φi,false)`: reversing the orientation conjugates the entry (`X_{φi,φj}` is read from the pair `(φj,φi)` as `ω_true − i ω_false`), so the imaginary coordinate changes sign.  Without the sign the identity `X(Φω) = X(ω)_{φ,φ}` fails (script column "without sign flip", `≈ 1`).
- `PF = infinitePi (gaussianReal 0 (gvarF c))` is preserved: `Φ = (sign flips) ∘ (reindexing by π)`; reindexing a product measure by a bijection `π` with `gvarF ∘ π = gvarF` (step 2) gives the same product, and `x ↦ −x` preserves `gaussianReal 0 v`.  On the diagonal (`i=j`) the orientation is trivially preserved and only the real coordinate is used.

### (iii) Concrete nondegenerate instance, by script (Python/numpy, not Lean; `d=3`, `L=3`, `W=1` and also `W=2`)

Data: `g=0.5`, `E=0.5`, `u=0.5`, `σ=(+,−)`, `a=((1,0,2),(2,1,1))`, `c=(1,2,1)`; sampled `ω ~ PF` with `S_xy = W^{-d} SB(g)_{blk x,blk y}`, `idxKey` a random permutation, `H = √u X`, `z = E+(1-u) m(E)`, `Lloop = tr(G(+) E_{a₀} G(−) E_{a₁})`.  Every hypothesis holds: `L=3 ≥ 3`, `W ≥ 1`, `|E|<2`, `0≤u<1`, `N = 27` (resp. `216`) nonempty, nonzero `L`-values (`|L(ω;Ta) − L(ω;a)| ≈ 9e-5 … 4e-3`, so the relabelling is not a trivial one).  Commands: `python3 inst.py 3 3 1; python3 inst.py 3 3 2` (scratch `scratchpad/T2155/inst.py`).  Asserted in the script: `π` bijective, `gvarF∘π = gvarF`, `S_{φi,φj} = S_{ij}`.  Output (verbatim):

```
d=3 L=3 W=1 N=27 g=0.5 E=0.5 u=0.5; z=0.3750+0.4841j
translation c=(1, 2, 1): reversed real-pairs=364; |X(Phi w)-X(w)_phi,phi|max=0.00e+00; without sign flip=9.84e-01
   L(Phi w; a)=0.0017279658-0.0000000000j  L(w; T a)=0.0017279658-0.0000000000j  diff=3.25e-18;  L(w; a)=0.0011177261-0.0000000000j  (|L(w;Ta)-L(w;a)|=6.10e-04)
negation: reversed real-pairs=338; |X(Phi w)-X(w)_phi,phi|max=0.00e+00; without sign flip=9.84e-01
   L(Phi w; a)=0.0051763542-0.0000000000j  L(w; T a)=0.0051763542+0.0000000000j  diff=3.16e-18;  L(w; a)=0.0011177261-0.0000000000j  (|L(w;Ta)-L(w;a)|=4.06e-03)
d=3 L=3 W=2 N=216 g=0.5 E=0.5 u=0.5; z=0.3750+0.4841j
translation c=(1, 2, 1): reversed real-pairs=24524; |X(Phi w)-X(w)_phi,phi|max=0.00e+00; without sign flip=9.56e-01
   L(Phi w; a)=0.0003213071+0.0000000000j  L(w; T a)=0.0003213071-0.0000000000j  diff=3.24e-19;  L(w; a)=0.0004091846+0.0000000000j  (|L(w;Ta)-L(w;a)|=8.79e-05)
negation: reversed real-pairs=24160; |X(Phi w)-X(w)_phi,phi|max=0.00e+00; without sign flip=9.56e-01
   L(Phi w; a)=0.0005181882-0.0000000000j  L(w; T a)=0.0005181882-0.0000000000j  diff=8.89e-20;  L(w; a)=0.0004091846+0.0000000000j  (|L(w;Ta)-L(w;a)|=1.09e-04)
```

Reading: `X(Φω) = X(ω)_{φ,φ}` to machine zero; `L(Φω; a) = L(ω; T a)` pointwise in `ω` (diff `≤ 3e-18`), for both `T`; therefore (step 5) `∫ L(a+c) = ∫ L(a) = ∫ L(−a)`.  Merged `Lloop`/`seqHflow` (single-time flow `√u X`, `Xmat` oriented by `idxKey`) is equivariant as stated: no stop condition of the ticket is triggered.  The target is a statement about expectations, which the script does not sample; it checks the pointwise identity that, with the measure-preserving `Φ`, gives it.  External hypotheses: none (no `Θ`, no `𝒦`, no cited input).

Verdict: target 1 (`stExpInv_holds`) PASS (hypothesis set consistent at `d=3`, `sz0`; route closes; no exponent).  Registry line deletion (`Test/Axioms.lean:177`) is a build matter, not mathematics.  Instances `stExpInv_holds 3` and the identities at `sz0`, `n=0`, `E=0`, `u=1/2`: PASS (`sz0.L 0 = 4`, `W 0 = 32`; nothing degenerate).  Overall: PASS.

## (b) Script output — Sun Oct  4 19:03:27 UTC 2026

```
$ git log -1 --format=%h t/T2155; git diff --stat main...t/T2155
4fa82bf
 RBM3D/Evolution/ExpInv.lean | 544 ++++++++++++++++++++++++++++++++++++++++++++
 RBM3D/Test/Axioms.lean      |   1 -
 2 files changed, 544 insertions(+), 1 deletion(-)

$ lake build RBM3D.Evolution.ExpInv 2>&1 | grep -v "^trace" | tail -4
warning: RBM3D/Evolution/ExpInv.lean:21:100: This line exceeds the 100 character limit, please shorten it!

Note: This linter can be disabled with `set_option linter.style.longLine false`
Build completed successfully (3775 jobs).

$ lake env lean ax.lean   (import RBM3D.Evolution.ExpInv; #print axioms RBM.Gauss.Sizes.stExpInv_holds)
'RBM.Gauss.Sizes.stExpInv_holds' depends on axioms: [propext, Classical.choice, Quot.sound]

$ grep -n "sorry\|admit\|native_decide\|^axiom" RBM3D/Evolution/ExpInv.lean ; echo "exit=$?"
exit=1

$ grep -rn "stExpInv_holds" RBM3D/ | grep -v "Evolution/ExpInv.lean:"   (name clash; public names of the file: stExpInv_holds only)
exit=1 (1 = no clash)

$ grep -n "^theorem\|^def\|^example\|^abbrev\|^instance" RBM3D/Evolution/ExpInv.lean
510:theorem stExpInv_holds (d : ℕ) : STExpInv d := by
530:example : STExpInv 3 := stExpInv_holds 3
534:example :

$ sed -n 441,446p RBM3D/Induction/Step5Pins.lean   (the merged pin, unchanged)
def STExpInv (d : ℕ) : Prop :=
  ∀ (sz : Sizes d) (n : ℕ) (E u : ℝ), |E| < 2 → 0 ≤ u → u < 1 →
    ∀ (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) (c : Zd d (sz.L n)),
      (∫ ω, Lloop sz n E u σ (fun i => a i + c) ω ∂(sz.seqP) = ∫ ω, Lloop sz n E u σ a ω ∂(sz.seqP)) ∧
      (∫ ω, Lloop sz n E u σ (fun i => -a i) ω ∂(sz.seqP) = ∫ ω, Lloop sz n E u σ a ω ∂(sz.seqP))


$ sed -n 510,511p RBM3D/Evolution/ExpInv.lean   (target 1)
theorem stExpInv_holds (d : ℕ) : STExpInv d := by
  intro sz n E u _ _ _ σ a c

$ sed -n 527,544p RBM3D/Evolution/ExpInv.lean   (compiled instances; both compiled in the module build above)
open RBM RBM.Gauss RBM.Gauss.Sizes

/-- The pin at `d = 3`. -/
example : STExpInv 3 := stExpInv_holds 3

/-- Both identities at the merged `sz0` (`L_0 = 4`, `W_0 = 32`, `λ_0 = 1/64`), `n = 0`, `E = 0`,
`u = 1/2`, `σ = (+,-)`, labels `a = (0, (0,1,2))` and shift `c = (1,1,1)` on `Z_4^3`. -/
example :
    let a : Fin 2 → Zd 3 (sz0.L 0) := ![fun _ => 0, fun k => ((k : ℕ) : ZMod (sz0.L 0))]
    let c : Zd 3 (sz0.L 0) := fun _ => 1
    (∫ ω, Lloop sz0 0 0 (1 / 2) ![true, false] (fun i => a i + c) ω ∂(sz0.seqP) =
        ∫ ω, Lloop sz0 0 0 (1 / 2) ![true, false] a ω ∂(sz0.seqP)) ∧
      (∫ ω, Lloop sz0 0 0 (1 / 2) ![true, false] (fun i => -a i) ω ∂(sz0.seqP) =
        ∫ ω, Lloop sz0 0 0 (1 / 2) ![true, false] a ω ∂(sz0.seqP)) :=
  stExpInv_holds 3 sz0 0 0 (1 / 2) (by norm_num) (by norm_num) (by norm_num) ![true, false]
    ![fun _ => 0, fun k => ((k : ℕ) : ZMod (sz0.L 0))] (fun _ => 1)

end RBM.Gauss.SizesInst

$ git diff main...t/T2155 -- RBM3D/Test/Axioms.lean | grep "^[-+] "
-   `RBM.Gauss.Sizes.STExpInv, -- translation and reflection invariance of `𝔼 𝓛^{(2)}`; S5-01 (T2138, DECISIONS §40: owed)

$ lake build   (worktree, root RBM3D.lean not touched: hub-only)
  [RBM.Gauss.Sizes.STExpInv]
Classify each of them: borrowed from the literature, owed by this formalization, or a predicate that defines the objects under study.
Some required targets logged failures:
- RBM3D
error: build failed
lake build  5.58s user 6.03s system 110% cpu 10.534 total

$ registry pre-check: copy of RBM3D.lean + "import RBM3D.Evolution.ExpInv" (after the last import) + #assert_rbm_axioms; lake env lean Precheck.lean; echo exit
exit=0  lines with error: 0
96:registry: 1 borrowed + 87 owed + 49 structural; 52 registered premise(s) carry nothing yet: [RBM.Loop.KLPT,

$ git -C ../RBM2D --no-optional-locks diff --stat c9a24cf HEAD -- RBM2D/Evolution/MLExpInv.lean ; log -1 --format=%h
 RBM2D/Evolution/MLExpInv.lean | 107 +++++++++---------------------------------
 1 file changed, 22 insertions(+), 85 deletions(-)
9e0f275
$ git -C ../RBM1D: no port from RBM1D
```

### Narrative (the ticket's targets; facts from the logs above)
- Target 1 `stExpInv_holds (d : ℕ) : STExpInv d` is proved in the new file `RBM3D/Evolution/ExpInv.lean` (544 lines, namespace `RBM.Gauss.Sizes`); the merged pin statement is unchanged (the `sed` extract above).  Only the three standard axioms.
- Route: the preflight route (i)-(v), as ported from RBM2D `Evolution/MLExpInv.lean` §1-§4 at `c9a24cf` (file header lists it).  Differences from RBM2D: `Z2 L` is `Zd d L`; `svar/gvar/P` are `svarF/gvarF/PF` with `g = sz.lam m` at size `m`; the kernel invariance is stated on `SBR` (`Props4.lean:48`, `sbKernelR_neg` `Block.lean:84`), as the merged `svarF` is defined through `SBR`; the loop is `loopFine`/`loopM` with the merged `Gres` (`Ring.inverse`, handled by `Matrix.nonsing_inv_eq_ringInverse`); `Hflow` is the merged `seqHflow = √u • seqXmat`; the ported `Θ`/`𝒦` step (`MLExpInv_Kcal_two`) and the drift tensors are not ported (ticket).
- `|E| < 2` and `0 ≤ u < 1` are not used in the proof (`intro sz n E u _ _ _ σ a c`); the identity holds for every `E`, `u` (paper-delta candidate T2155a below).
- The coordinate bijection `π`, its sign flips and the measure-preserving `Φ` of `SeqΩ sz` (identity on sizes `m ≠ n`) are the RBM2D constructions with the size-`m` data `(sz.L m, sz.W m, sz.lam m)`.
- Registry: the line `RBM.Gauss.Sizes.STExpInv` was deleted from `Test/Axioms.lean`.  The registry pre-check (copy of `RBM3D.lean` with `import RBM3D.Evolution.ExpInv` added, `#assert_rbm_axioms` last) exits 0 with no `error` line (output above).  The plain `lake build` in this worktree fails at the root `RBM3D.lean:201` with "`[RBM.Gauss.Sizes.STExpInv]` ... not registered", because the root import of the new module is added by the hub at merge (CLAUDE.md §1, §3 (A)4) and without it `inst_expInv` (`Step5Pins.lean:1035`) takes `STExpInv 3` as a hypothesis that no imported theorem proves; with the import added (the pre-check) the audit passes.  The hub's merge-time full `lake build` is the remaining check.
- Instances: `example : STExpInv 3` and the two identities at `sz0`, `n = 0`, `E = 0`, `u = 1/2`, `σ = (+,-)`, labels `a = (0,(0,1,2))`, shift `c = (1,1,1)`; both are `example`s compiled in the module build.  The instance data is nondegenerate (`L_0 = 4`, `W_0 = 32`, `N = 2097152`; `Sizes.card_Idx` / `sz0_values`), not a collapsed window.
- Hypothesis count: no hypothesis added; no external input; the file imports `Induction.Step5Pins` and `Gauss.FineModel`, not `RBM3D`.

## (c) Verified Mathlib names (each used in the file, which compiles)
`Matrix.submatrix_mul_equiv`, `Matrix.submatrix_submatrix`, `Matrix.submatrix_diagonal_equiv`, `Matrix.submatrix_sub`, `Matrix.submatrix_smul`, `Matrix.inv_submatrix_equiv`, `Matrix.nonsing_inv_eq_ringInverse`, `Matrix.trace`/`Matrix.diag_apply`, `Equiv.sum_comp`, `Equiv.prodCongr`, `Equiv.sigmaCongrRight`, `Equiv.addRight`, `Equiv.neg`, `Function.update_self`, `Function.update_of_ne`, `Finite.injective_iff_bijective`, `MeasurableEquiv.piCongrLeft`, `MeasurableEquiv.piCongrLeft_apply_apply`, `MeasurableEquiv.piCongrRight`, `MeasurableEquiv.neg`, `MeasureTheory.Measure.infinitePi_map_piCongrLeft`, `MeasureTheory.Measure.infinitePi_map_pi`, `ProbabilityTheory.gaussianReal_map_neg`, `MeasureTheory.MeasurePreserving.integral_comp'`, `add_sub_add_right_eq_sub`, `neg_sub_neg`, `neg_sub`.  Names verified absent: none searched.

## (d) Open issues and paper-delta candidates
- Section (a) needed no correction (no (a′)); one note, not an error: `sz0` lives in `RBM.Gauss.SizesInst` (`Defs/Sizes.lean:257,260`), so the instance block opens that namespace.
- T2155a: the merged pin `STExpInv` carries `|E| < 2`, `0 ≤ u < 1`, which the proof does not use (the statement holds for every real `E`, `u`); the paper (`3_5:2196-2200`) states the invariance without them.  Not a defect of the pin (a weaker form); no change proposed beyond recording it.
- T2155b: `STExpInv` is proved for the single-time flow `H_u = √u X` (merged `seqHflow`), the model of the merged ticket T2006 (DECISIONS §7), not the matrix Brownian motion (`Gauss/FineModel.lean`, docstring of `seqHflow`); nothing is claimed for the Brownian flow.
- Hub notes: add `import RBM3D.Evolution.ExpInv` after the last import of `RBM3D.lean`; the registry deletion is already in the branch.
