Prover model: claude-sonnet-5-5

## (a) Math preflight — Mon Oct  5 21:52:11 UTC 2026

### (i) Exponent table

No exponent or scaling threshold enters (deterministic, one size, no `≺`, no `∀ᶠ`). The constants and ranges the targets depend on:

| item | value / form | constraint | slack |
|---|---|---|---|
| `3 ≤ d` (pin premise) | unused by the proof | none | none needed; instance `d = 3` |
| `3 ≤ L` (`sz.three_le_L n`) | `‖SB d L g‖ = 1` (`norm_SB`, `Defs/Block.lean:136`), any real `g` | `hasDerivAt_kTwo` `hS`; `sz0`: `L = 4` | 1 |
| `W ≥ 1` (`sz.W_pos`) | `(W:ℂ)^d ≠ 0` | `hW` of `hasDerivAt_kTwo` | `W = 32` |
| `\|E\| < 2` | `‖mSigma E s‖ = 1` (`norm_mSigma`, needs `≤ 2`); `Im mE = √(4-E²)/2 > 0` | strict for `Im > 0` | `E = 1/2`: `Im m = 0.968` |
| time `u` for 𝒦 ODE | `‖u mSigma σ₀ mSigma σ₁‖ = u < 1` (`norm_mul_mSigma_lt_one`, `Defs/Semicircle.lean:91`, every pair of signs) | `0 ≤ u < 1` | `u = 1/2`: 1/2 |
| time for drift identity | `0 < u < 1` (`H_u = √u X`; `samplewise_loop_generator_eq_cuts` needs `u ≠ 0`) | open window | pin states `Ioo 0 1` |
| time for continuity | `[0,1) = ⋃_{b<1} [0,b]`, `u = 0` included | window `η = (1-b) Im m > 0` | `b = 0.9`: `η = 0.0968` |
| bound on `[0,b]` | `‖𝓛‖ ≤ card(Vtx)·(η⁻¹ W^{-d})^k` (`norm_gloop_any_window_le`), `card Vtx = (WL)^d` | `η > 0`, `k` = list length (1, 2, 3 occur) | `(WL)^d = 2097152` at `sz0` |
| Hessian factor | `genMat`: `(1/2) Σ_c gvarF(c) F_c''(0)`, `F_c(y)=𝓛(H_u+yX_c)`; coordinate line `t ↦ H_u + √u(t-ω_c)X_c` (`HflowBlock_update`) gives `∂_t² = u F_c''`; `samplewise_loop_generator_eq_cuts` has `1/(2u) Σ_γ gvarF(γ) tr(…second…)` | `(1/2)F'' = (1/(2u))(∂_t²)` | exact identity, `u > 0`; same `g` in `gvarF d L W g` on both sides; along the sequence `g = sz.lam n` (`seqP_map_slice`) |
| `Σ_{l ∈ Icc 3 2}` | empty (`3 > 2`) | `k = 2` | exact |
| `g = lam n` | arbitrary real (no `WO`, no `lam → 0`) | `SB`, `PF`, `HierarchyN` hold for every real `g` | `sz0`: `1/64` |

### (i') Route table (RBM2D source read at the pinned commit `c9a24cf`, 731 lines, via `git show`)

| target | RBM2D `c9a24cf` `MLExpHier.lean` | merged RBM3D inputs | RBM3D change |
|---|---|---|---|
| 1a `expHier_continuousOn_integral_loopL` | class `Good` `:63-158`, `_continuousOn_Ico` `:488`, `_Lexp` `:499` | `continuousOn_gloop_any_window` `LoopGenerator:696`, `norm_gloop_any_window_le` `:725`, `continuous_gloop_HflowBlock_sample`, `zt_im`/`mE_im_pos` | `Ω d L W`, `PF d L W g`, `loopL`, `zt`; bound `(WL)^d (η⁻¹W^{-d})^k` |
| 1b `expHier_genMat_eq_cuts` | `_blockMat_line` `:305`, `_second_deriv` `:313` (factor `u⁻¹`, confirmed), `_hasDerivAt_Gsig` `:372`, `_deriv_spec` `:415`, `_genMat_eq_cuts` `:436` | `HflowBlock_update`, `hasDerivAt_deriv_gloop_update`, `samplewise_loop_generator_eq_cuts`, `hasDerivAt_green_moving`, `hasDerivAt_spectralZ`; `spectralWordDeriv` is the spectral part only (`LoopFlowStein:185`, `gsigSpectralFlowDeriv` `:168`), matching `genMat`'s fixed-`M` time derivative | `g` argument; `W^d`; `Gres` at both signs |
| 1c `expHier_Kloop_hasDerivAt` | `isPrimitive_Kcal` `:228,:542` | `hasDerivAt_kTwo`, `KLK_two_eq_kTwo`, `norm_mul_mSigma_lt_one`, `norm_SB` | all four sign pairs (`kpmODE` `DriftAlgebra:111` is `(+,-)`); `‖u m(σ₀)m(σ₁)‖ = u` for each pair; `List.ofFn σ = [σ 0, σ 1]` |
| 1d `expHier_hierarchy_two` | `hierarchyN_two` `MLExpVocab:239` | `hierarchyN_holds d` at `k=2`; private reductions `HierarchyN.lean:81-140` (all stated for every `σ : Fin 2 → Bool`: `_STLIM_loopOf`, `_STLKIM_loopOf`, `_ThetaN_two`, `_length_two`, `_STelklkM_two`, `_STegtM_two`) | copy as `expHier_*`; only `hierarchyN_two` (l. 159) fixes `σ = (+,-)` |
| 1e `expHier_hasDerivAt_fixed` | `_integral_LKf` `:464`, `_integral_thetaSig` `:476`, `_hasDerivAt` `:515` | `hasDerivAt_integral_gloop_HflowBlock_spectralZ` `LoopFlowStein:810` (derivative = `∫ deriv_v 𝓛`, full flow, not only spectral), `deriv_integral_…_samplewiseLoopGeneratorCuts` `:312`, `integrable_samplewiseLoopGeneratorCuts` `:275`, `Hflow_isHermitian` | drift = two integrals (`STELKLKM`, `STEGtM`); `STavgM = STLM - STmsig` by definition, so `_avgErr_eq`, `_elklkN_two`, `_egtN_two` are not needed |
| 2a–c, 3 | §5 `:601-667` (`_integral_slice` `:601`) | `seqP_map_slice`, `measurable_slice`, `STLM_seqHflow` (`rfl`), `loopM_eq_loopL` | three transfers (`STExpErr`, `STExpELKLK`, `STExpEGt`); no `f_0 = 0` conjunct |

Dependency check of the integrand classes: `STExpErr` uses `Lloop` (length 2) and `STKloop` (length 2); `STELKLKM` uses `STLKM` at length 2 only; `STEGtM` uses `STLM` at lengths 1 and 3, with no `𝒦`. So continuity of `𝒦` on `[0,1)` is needed only at length 2, and follows from the 𝒦 ODE (1c) at each `t ∈ [0,1)`.

### (ii) One concrete nondegenerate instance

`d = 3`, `sz0` at `n = 0` (`L = 4`, `W = 32`, `lam = 1/64`, `SizesInst.sz0`, `Defs/Sizes.lean:260`), `E = 1/2`, `u = 1/2`, window `b = 0.9`, `σ ∈ {+,-}²` (all four), `a = (0, e₁)`. All hypotheses hold at once: `|E| < 2`, `0 < u < 1`, `3 ≤ L`, `W ≥ 1`, `3 ≤ d`. The script (a) prints the hypotheses, `|m|`, `Im z_t`, `η`, `card Vtx`, and `‖SB‖_∞ = 1` for the `64 × 64` `SB` built from `sbKernel`; (b) checks `∂_t 𝒦 = W^d 𝒦 S 𝒦` by central differences for all four sign pairs, with `𝒦 = W^{-d} μ (1 - tμ SB)⁻¹`, `μ = m(σ₀)m(σ₁)`; (c) checks the Hessian factor on a random Hermitian `6×6` matrix, a coordinate matrix `X_c = E₀₁ + E₁₀`, `u = 1/2`, `σ = (-,-)`: `∂_t²` of the line `t ↦ 𝓛(H + √u t X_c)` equals `u` times `F''(0)`, so `(1/2)F'' = (1/(2u)) ∂_t²`.

Command and output:

```
$ python3 <scratchpad>/T2218/pre.py
hyp: |E|<2 True 0<u<1 True 3<=d True 3<=L True W>0 True
|mE|= 1.0  Im mE= 0.9682458365518543  Im zt(E,u)= 0.4841229182759271
window [0,b], b= 0.9  eta=(1-b)Im m= 0.0968245836551854  card(Vtx)=(WL)^d= 2097152
row sums SB (min,max): 0.9999999999999999 0.9999999999999999 ; ||SB||_inf-op = 0.9999999999999999
every sign: |t m(s1) m(s2)|=u<1, d/dt kTwo (FD) vs W^d sum K S K at (0,e1)
(True, True) |t m m|=0.500 max|FD-rhs|/max|rhs| over all 64x64 entries = 7.14e-10
(True, False) |t m m|=0.500 max|FD-rhs|/max|rhs| over all 64x64 entries = 1.40e-10
(False, True) |t m m|=0.500 max|FD-rhs|/max|rhs| over all 64x64 entries = 1.40e-10
(False, False) |t m m|=0.500 max|FD-rhs|/max|rhs| over all 64x64 entries = 7.14e-10
sign (-,-): line Hessian f''(0)=(-0.581449+0.045537j) ; t-line Hessian=(-0.290724+0.022769j) ; ratio t/line = 0.500000 (u=0.50, 1/u=2.00)
genMat factor: (1/2)*f'' = (1/(2u))*(t-line'') : True
```

Hierarchy at `M = 1` (Hermitian), `σ = (-,-)`, `a = (0,0)`, `u = 1/2`: the identity is `hierarchyN_holds` at `k = 2` (merged, `LoopGenN.lean:621`), so it holds at this data; the instance statements are those of check section 3 (compiled, exit 0 per CONTROL).

External hypothesis: none (the pin and all intermediates are unconditional deterministic statements); no limit computation applies.

### Checklist (§29 / §45 O2) and consumer check

```
$ cd /Users/junyin/Lean_proof/RBM3D; grep -c STExpHier RBM3D/Induction/Step6Kit.lean
0
$ grep -rn "ExpHier.lean\|Induction.ExpHier\|expHier_\|stExpHier_holds\|T2218" RBM3D RBM3D.lean | grep -v Step6Pins.lean | wc -l
       0
$ grep -n "STExpHier" RBM3D/Test/Axioms.lean
229:   `RBM.Gauss.Sizes.STExpHier, -- `3_5:73` at n = 2, `6:90` expected hierarchy: S6-04; S6-01 (T2204, DECISIONS §67: owed)
$ git -C /Users/junyin/Lean_proof/RBM2D --no-optional-locks show c9a24cf:RBM2D/Evolution/MLExpHier.lean | wc -l
     731
$ git -C /Users/junyin/Lean_proof/RBM2D --no-optional-locks show c9a24cf:RBM2D/Evolution/MLExpHier.lean | grep -n "theorem expHierPin"
643:theorem expHierPin : ExpHierPin d := by
$ wc -l RBM2D/RBM2D/Evolution/MLExpHier.lean (checked-out HEAD 9e0f275)
     670
$ git log -1 --format=%h main   (worktree HEAD: 5d313ca)
5d313ca
```

1. Time: continuity on `[0,1)` including `u = 0` (window `[0,b]`, `b < 1`); drift identity on `(0,1)` only. As the pin.
2. No regime, no window. 3. No `L`–`W` relation: `3 ≤ L`, `W ≥ 1` only. 4. No `∀ᶠ`. 5. Pointwise in `u`, no `Prec`, no grid lift. 6. `lam n` arbitrary real. 7. No scale `N` (only `card Vtx = (WL)^d` inside a bound).
- Consumer (§45 O2): `stExpHier_holds 3` is the argument `h : STExpHier 3` of the merged `inst_expHier` (`Step6Pins.lean:659-666`, `h (by norm_num) sz0 0 (1/2) …`); the pin's binder order is `3 ≤ d → ∀ sz n E, |E| < 2 → ∀ σ a`. S6-05 (from-`s` Duhamel, `STExpDuhamelZ`/`Q`) uses continuity of `STExpErr`, `STExpDrift` on `[s,t] ⊂ [0,1)` and `∂_u STExpErr = STthetaOp … + STExpDrift` on `(s,t) ⊂ (0,1)`: the three conjuncts, no `f_0 = 0`. No skeleton in `Step6Kit.lean` mentions `STExpHier` (count above).
- Registry plan: delete the single `owedProps` line carrying `STExpHier`; the file defines no public `Prop` (the class is a `private structure … : Prop`). Expected pre-check: `STExpHier` absent from the owed list, owed count one less than on the branch base, `inst_expHier` still carries `STExpHier` as a hypothesis (counted as proved by `stExpHier_holds`, conclusion head `STExpHier`).

### Observations for stage 1b (no statement is affected)
- O1: the RBM2D checkout at `../RBM2D` is at HEAD (file `MLExpHier.lean` last changed by `ec26147`, 670 lines, refactored); the ticket's source is the pinned commit `c9a24cf` (731 lines, `expHierPin` at `:643`, verified above). Read the source with `git show c9a24cf:RBM2D/Evolution/MLExpHier.lean`; cite `c9a24cf`.
- O2: `main` and the worktree are at `5d313ca`, not `14513ee` (merges of T2213, T2214, T2215 in between; none touches a file the ticket lists as merged input except `Test/Axioms.lean`). The `STExpHier` registry line is now at `Axioms.lean:229` (ticket: `:230`); delete it by content, not by line number.
- O3: for `‖t m(σ₀)m(σ₁)‖ < 1` at every sign pair, the merged `norm_mul_mSigma_lt_one` (`Semicircle.lean:91`, `|E| ≤ 2`, `0 ≤ t < 1`) applies directly; `DriftAlgebra`'s private `mSigma true * mSigma false = 1` is not needed.

### Verdict
- Targets 1a, 1b, 1c, 1d, 1e, 2a, 2b, 2c, 3 (the pin `STExpHier`), 4 (five instances): PASS. Every hypothesis set is satisfiable at the instance above; no exponent constraint exists to close; no statement is false; no missing input.


## (b) Script output — Mon Oct  5 22:03:32 UTC 2026

```
$ git log -1 --format=%h; git diff --stat main...t/T2218
71de123
 RBM3D/Induction/ExpHier.lean | 891 +++++++++++++++++++++++++++++++++++++++++++
 RBM3D/Test/Axioms.lean       |   1 -
 2 files changed, 891 insertions(+), 1 deletion(-)
$ lake build RBM3D.Induction.ExpHier 2>&1 | tail -2
info: RBM3D/Induction/ExpHier.lean:891:0: 'RBM.Gauss.Step6Inst.inst_expHier_hierarchy_two' depends on axioms: [propext, Classical.choice, Quot.sound]
Build completed successfully (3853 jobs).
$ (full build, root RBM3D.lean temporarily with `import RBM3D.Induction.ExpHier` after the last import line, as the hub adds it; reverted, not committed) lake build | tail -2
Build completed successfully (4022 jobs).
lake build  32.08s user 4.77s system 103% cpu 35.480 total
$ lake env lean RBM3D/Induction/ExpHier.lean | grep axioms
Sizes.expHier_continuousOn_integral_loopL' depends on axioms: [propext, Classical.choice, Quot.sound]
Sizes.expHier_genMat_eq_cuts' depends on axioms: [propext, Classical.choice, Quot.sound]
Sizes.expHier_Kloop_hasDerivAt' depends on axioms: [propext, Classical.choice, Quot.sound]
Sizes.expHier_hierarchy_two' depends on axioms: [propext, Classical.choice, Quot.sound]
Sizes.expHier_hasDerivAt_fixed' depends on axioms: [propext, Classical.choice, Quot.sound]
Sizes.expHier_continuousOn_err' depends on axioms: [propext, Classical.choice, Quot.sound]
Sizes.expHier_continuousOn_drift' depends on axioms: [propext, Classical.choice, Quot.sound]
Sizes.expHier_hasDerivAt' depends on axioms: [propext, Classical.choice, Quot.sound]
Sizes.stExpHier_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
Step6Inst.inst_expHier_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
Step6Inst.inst_expHier_pp' depends on axioms: [propext, Classical.choice, Quot.sound]
Step6Inst.inst_expHier_half' depends on axioms: [propext, Classical.choice, Quot.sound]
Step6Inst.inst_expHier_Kloop' depends on axioms: [propext, Classical.choice, Quot.sound]
Step6Inst.inst_expHier_hierarchy_two' depends on axioms: [propext, Classical.choice, Quot.sound]
$ grep -n "sorry\|admit\|native_decide\|^axiom" RBM3D/Induction/ExpHier.lean | wc -l
       0
$ git diff main -- RBM3D/Induction/Step6Pins.lean | wc -l
       0
```

Target statements extracted from the file by script (`<scratchpad>/T2218/stmts.py`; public theorems, namespace `RBM.Gauss.Sizes`):
```
theorem expHier_continuousOn_integral_loopL {d : ℕ} (L W : ℕ) [NeZero L] [NeZero W] (g : ℝ)
    {E : ℝ} (hE : |E| < 2) (I : LoopIdx (Zd d L)) :
    ContinuousOn (fun u : ℝ => ∫ ω : Ω d L W, loopL d L W (HflowBlock d L W u ω) (zt E u) I
      ∂(PF d L W g)) (Set.Ico 0 1) :=

theorem expHier_genMat_eq_cuts {d : ℕ} (L W : ℕ) [NeZero L] [NeZero W] (g : ℝ) {E u : ℝ}
    (hE : |E| < 2) (hu : 0 < u) (hu1 : u < 1) (ω : Ω d L W) (I : LoopIdx (Zd d L)) (hI : I.WF) :
    genMat d L W g E u (Hflow d L W u ω) I = samplewiseLoopGeneratorCuts d L W g ω E u I

theorem expHier_Kloop_hasDerivAt {d : ℕ} (sz : Sizes d) (n : ℕ) {E : ℝ} (hE : |E| < 2) (u : ℝ)
    (hu0 : 0 ≤ u) (hu1 : u < 1) (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) :
    HasDerivAt (fun v : ℝ => sz.STKloop n E v σ a)
      ((((sz.W n : ℕ) : ℂ) ^ d) * ∑ c : Zd d (sz.L n), ∑ e : Zd d (sz.L n),
        sz.STKloop n E u σ ![a 0, c] * SB d (sz.L n) (sz.lam n) c e *
          sz.STKloop n E u σ ![e, a 1]) u

theorem expHier_hierarchy_two {d : ℕ} (sz : Sizes d) (n : ℕ) {E : ℝ} (hE : |E| < 2) (u : ℝ)
    (hu0 : 0 ≤ u) (hu1 : u < 1)
    (M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (hM : M.IsHermitian)
    (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) :
    genMat d (sz.L n) (sz.W n) (sz.lam n) E u M (loopOf σ a) -
        deriv (fun v : ℝ => sz.STKloop n E v σ a) u =
      sz.STthetaOp n E u σ (sz.STLKM n E u M σ) a + sz.STELKLKM n E u M σ a +
        sz.STEGtM n E u M σ a

theorem expHier_hasDerivAt_fixed {d : ℕ} (sz : Sizes d) (n : ℕ) {E : ℝ} (hE : |E| < 2) (u : ℝ)
    (hu0 : 0 < u) (hu1 : u < 1) (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) :
    HasDerivAt (fun v : ℝ =>
        (∫ ω, loopL d (sz.L n) (sz.W n) (HflowBlock d (sz.L n) (sz.W n) v ω) (zt E v) (loopOf σ a)
          ∂(PF d (sz.L n) (sz.W n) (sz.lam n))) - sz.STKloop n E v σ a)
      (sz.STthetaOp n E u σ (fun b =>
          (∫ ω, loopL d (sz.L n) (sz.W n) (HflowBlock d (sz.L n) (sz.W n) u ω) (zt E u) (loopOf σ b)
            ∂(PF d (sz.L n) (sz.W n) (sz.lam n))) - sz.STKloop n E u σ b) a +
        ((∫ ω, sz.STELKLKM n E u (Hflow d (sz.L n) (sz.W n) u ω) σ a
            ∂(PF d (sz.L n) (sz.W n) (sz.lam n))) +
          ∫ ω, sz.STEGtM n E u (Hflow d (sz.L n) (sz.W n) u ω) σ a
            ∂(PF d (sz.L n) (sz.W n) (sz.lam n)))) u

theorem expHier_continuousOn_err {d : ℕ} (sz : Sizes d) (n : ℕ) {E : ℝ} (hE : |E| < 2)
    (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) :
    ContinuousOn (fun u => sz.STExpErr n E u σ a) (Set.Ico 0 1)

theorem expHier_continuousOn_drift {d : ℕ} (sz : Sizes d) (n : ℕ) {E : ℝ} (hE : |E| < 2)
    (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) :
    ContinuousOn (fun u => sz.STExpDrift n E u σ a) (Set.Ico 0 1)

theorem expHier_hasDerivAt {d : ℕ} (sz : Sizes d) (n : ℕ) {E : ℝ} (hE : |E| < 2)
    (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) :
    ∀ u ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt (fun v => sz.STExpErr n E v σ a)
      (sz.STthetaOp n E u σ (fun b => sz.STExpErr n E u σ b) a + sz.STExpDrift n E u σ a) u

theorem stExpHier_holds (d : ℕ) : STExpHier d :=

```
Compiled nonempty instances (namespace `RBM.Gauss.Step6Inst`, `d = 3`, `sz0`, `n = 0`, `E = 1/2`; `<scratchpad>/T2218/inst.py`: proof terms; the five named theorems carry the statements of check section 3, the five `example`s are targets 1a, 1b, 1e, 2a, 2b; no hypothesis left):
```
theorem inst_expHier_holds   ... := inst_expHier (stExpHier_holds 3)
theorem inst_expHier_pp   ... := stExpHier_holds 3 (by norm_num) sz0 0 (1 / 2) (by norm_num [abs_of_pos]) ![true, true]     ![0, Pi.single 0 1]
theorem inst_expHier_half   ... := (stExpHier_holds 3 (by norm_num) sz0 0 (1 / 2) (by norm_num [abs_of_pos]) ![false, false]     ![0, Pi.single 0 1]).2.2 (1 / 2) ⟨by norm_num, by norm_num⟩
theorem inst_expHier_Kloop   ... := expHier_Kloop_hasDerivAt sz0 0 (by norm_num [abs_of_pos]) (1 / 2) (by norm_num) (by norm_num)     ![true, true] ![0, Pi.single 0 1]
theorem inst_expHier_hierarchy_two   ... := expHier_hierarchy_two sz0 0 (by norm_num [abs_of_pos]) (1 / 2) (by norm_num) (by norm_num) 1     Matrix.isHermitian_one ![false, false] ![0, 0]
example   ... := expHier_continuousOn_integral_loopL (sz0.L 0) (sz0.W 0) (sz0.lam 0) (by norm_num [abs_of_pos]) _
example   ... := expHier_genMat_eq_cuts (sz0.L 0) (sz0.W 0) (sz0.lam 0) (by norm_num [abs_of_pos]) (by norm_num)     (by norm_num) (fun _ => 1) _ (by simp [LoopIdx.WF, loopOf])
example   ... := expHier_hasDerivAt_fixed sz0 0 (E := 1 / 2) (by norm_num [abs_of_pos]) (1 / 2) (by norm_num)     (by norm_num) ![true, false] ![0, Pi.single 0 1]
example   ... := expHier_continuousOn_err sz0 0 (E := 1 / 2) (by norm_num [abs_of_pos]) ![true, false]     ![0, Pi.single 0 1]
example   ... := expHier_continuousOn_drift sz0 0 (E := 1 / 2) (by norm_num [abs_of_pos]) ![true, false]     ![0, Pi.single 0 1]
```
Check-file equality (scratch `<scratchpad>/T2218/eq.lean` = check imports + `import RBM3D.Induction.ExpHier` + sections 1-2 + 9 `example : T2218Check.X := @X` + `example (d : ℕ) : STExpHier d := stExpHier_holds d` + 5 instance statements as `example : <stmt> := @inst_*`):
```
$ lake env lean <scratchpad>/T2218/eq.lean > eq.out; echo "exit $?"
exit 0
$ grep -c "error" eq.out
0
$ grep -c "^example" eq.lean   (9 target examples + 1 pin example + 5 instance examples)
15
```
Registry pre-check (§20 (2)): temporary uncommitted file (`<scratchpad>/T2218/pre.lean`: `import RBM3D`, `import RBM3D.Induction.ExpHier`, `#assert_rbm_axioms`), after `RBM3D.lean` temporarily carried `import RBM3D.Induction.ExpHier` (reverted):
```
$ lake env lean pre.lean > pre.out; echo "exit $?"
exit 0
$ grep -c "STExpHier" pre.out    (owed ledger and carry-nothing list)
0
$ grep -n "premises found by scanning\|^registry:" pre.out | cut -c1-140
155:premises found by scanning: 127 (borrowed 1, owed 95, structural 25, refuted 6).
156:registry: 2 borrowed + 146 owed + 80 structural + 7 refuted; 108 registered premise(s) carry nothing yet: [RBM.Loop.KLPT,
$ owed entries of owedProps: main (git show main:RBM3D/Test/Axioms.lean) / branch (cat)
147
146
$ git diff main...t/T2218 -- RBM3D/Test/Axioms.lean | grep "^[-+][^-+]"
-   `RBM.Gauss.Sizes.STExpHier, -- `3_5:73` at n = 2, `6:90` expected hierarchy: S6-04; S6-01 (T2204, DECISIONS §67: owed)
$ (without the root import, the full lake build fails: "1 premise(s) ... [RBM.Gauss.Sizes.STExpHier]"; the hub adds the import at merge, §3 (A) step 4)
```
Name-clash grep of new public names and of the file stem (outside the new file):
```
$ grep -rn "expHier_\|stExpHier_holds\|inst_expHier_\|Induction.ExpHier\|T2218" RBM3D RBM3D.lean --include="*.lean" | grep -v "^RBM3D/Induction/ExpHier.lean" | wc -l
       0
$ grep -n '^theorem\|^def\|^structure\|^abbrev\|^instance\|^example' RBM3D/Induction/ExpHier.lean | cut -c1-90   (non-private top-level declarations; every private helper is `private theorem expHier_*` or `private structure expHier_Good`)
176:theorem expHier_continuousOn_integral_loopL {d : ℕ} (L W : ℕ) [NeZero L] [NeZero W] (g
331:theorem expHier_genMat_eq_cuts {d : ℕ} (L W : ℕ) [NeZero L] [NeZero W] (g : ℝ) {E u : 
427:theorem expHier_Kloop_hasDerivAt {d : ℕ} (sz : Sizes d) (n : ℕ) {E : ℝ} (hE : |E| < 2)
449:theorem expHier_hierarchy_two {d : ℕ} (sz : Sizes d) (n : ℕ) {E : ℝ} (hE : |E| < 2) (u
547:theorem expHier_hasDerivAt_fixed {d : ℕ} (sz : Sizes d) (n : ℕ) {E : ℝ} (hE : |E| < 2)
722:theorem expHier_continuousOn_err {d : ℕ} (sz : Sizes d) (n : ℕ) {E : ℝ} (hE : |E| < 2)
731:theorem expHier_continuousOn_drift {d : ℕ} (sz : Sizes d) (n : ℕ) {E : ℝ} (hE : |E| < 
748:theorem expHier_hasDerivAt {d : ℕ} (sz : Sizes d) (n : ℕ) {E : ℝ} (hE : |E| < 2)
770:theorem stExpHier_holds (d : ℕ) : STExpHier d :=
790:theorem inst_expHier_holds :
799:theorem inst_expHier_pp :
809:theorem inst_expHier_half :
817:theorem inst_expHier_Kloop :
826:theorem inst_expHier_hierarchy_two :
842:example :
850:example :
860:example :=
865:example :=
870:example :=
```
Port citations (RBM2D `Evolution/MLExpHier.lean` at `c9a24cf`, 731 lines, read with `git show`; `../RBM2D` HEAD is a later refactor):
```
$ git -C ../RBM2D --no-optional-locks log -1 --format=%h c9a24cf
c9a24cf
$ git -C ../RBM2D --no-optional-locks diff --stat c9a24cf HEAD -- RBM2D/Evolution/MLExpHier.lean
 RBM2D/Evolution/MLExpHier.lean | 95 ++++++++----------------------------------
 1 file changed, 17 insertions(+), 78 deletions(-)
$ git status --short (worktree)
```

### Narrative (≤ 40 lines)
- Port of RBM2D `Evolution/MLExpHier.lean` at `c9a24cf`: `MLExpHier:55-160` (class `Good`, `Good_gloop`, integrable, continuousOn) is §1 of the file (`expHier_Good*`, bound `card (Vtx) (η⁻¹ W^{-d})^k`); `:305-453` (bridge, `u⁻¹` factor, `_deriv_spec`) is §2; `:457-592` (fixed size) is §4; `:594-667` (transfer, pin) is §5.
- Not ported: `MLExpHier_elklkN_two`, `_egtN_two`, `_avgErr_eq`, `_sbSum` (the merged `STELKLKM`, `STEGtM`, `STavgM` are already the `n = 2` double sums); `MLExpHier_Good_drift` is replaced by `expHier_Good_STELKLKM`, `expHier_Good_STEGtM` (the drift is two integrals); `expErrT_zero` (no `f_0 = 0` in the merged pin).
- New for `d ≥ 3` and every sign: `expHier_Kloop_hasDerivAt` (`hasDerivAt_kTwo` + `KLK_two_eq_kTwo` + `norm_mul_mSigma_lt_one` + `norm_SB`; replaces `isPrimitive_Kcal`; the merged `KpmODE` is `σ = (+,-)` only) and `expHier_hierarchy_two` (`hierarchyN_holds d … 2 le_rfl σ a`, the private reductions of `HierarchyN.lean:81-140` copied as `expHier_*`, `Finset.Icc 3 2` empty).
- `expHier_genMat_eq_cuts`: the factor of the second derivative is `u⁻¹` as in RBM2D (`expHier_second_deriv`), `genMat`'s `1/2` meets `1/(2u)` of `samplewise_loop_generator_eq_cuts`; the spectral part is `trace (spectralWordDeriv …)` (`expHier_hasDerivAt_Gsig` is a copy of the private `LoopGenN_hasDerivAt_Gsig_spec`, `LoopGenN.lean:147`).
- `stExpHier_holds d` uses neither `3 ≤ d` nor any hypothesis; `3 ≤ L` enters through `sz.three_le_L n` (`norm_SB`, `NeZero`), `W ≥ 1` through `NeZero (sz.W n)`. The merged pin file is unchanged (`git diff main -- Step6Pins.lean` is empty).
- Without the root import the full `lake build` fails on `STExpHier` (unregistered premise); with `import RBM3D.Induction.ExpHier` after the last import line (the hub's step, CLAUDE.md §3 (A) 4) the full build passes. `RBM3D.lean` is not committed.
- `Axioms.lean`: one line deleted, by content (it is at `:229` on this base `5d313ca`, not `:230`; the ticket assumed `14513ee`). Merge note: T2217 deletes the adjacent line (ticket text); keep both lines deleted.
- Obstruction: none; section (a) needed no correction (no section (a′)).

## (c) Verified Mathlib names (each used by the compiled file; located by `grep -rn` in `.lake/packages/mathlib/Mathlib`)
- `MeasureTheory.continuousOn_of_dominated` (`VectorMeasure/Integral.lean:758`); `MeasureTheory.Integrable.of_bound` (`Integral/IntegrableOn.lean:171`); `MeasureTheory.integral_map` (`VectorMeasure/Integral.lean:829`); `MeasureTheory.integral_finsetSum` (`:417` same file).
- `MeasureTheory.probReal_univ` (`Measure/Typeclasses/Probability.lean:118`); `IsCompact.exists_bound_of_continuousOn` (`Analysis/Normed/Group/Bounded.lean`); `HasDerivAt.congr_of_eventuallyEq` (`Deriv/Basic.lean:604`), `HasDerivAt.congr_deriv` (`:597`), `HasDerivAt.scomp` (`Deriv/Comp.lean:100`).
- Verified absent: `MeasureTheory.measureReal_univ_eq_one` (unknown identifier at compile).

## (d) Open issues and paper-delta candidates
- Open issues: none. Instances for 1a, 1b, 1e, 2a, 2b are unnamed `example`s with inferred types (the statements of 1b: sample `ω ≡ 1`, nonzero).
- Paper-delta candidates: none (the ported statements are those of the merged pin; no hypothesis was added, no statement weakened).
