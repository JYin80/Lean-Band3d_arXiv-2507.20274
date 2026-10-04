Prover model: claude-sonnet-5-5
## (a) Math preflight — Sun Oct  4 01:32:05 UTC 2026

Sources: RBM2D at `c9a24cf` (`git show c9a24cf:RBM2D/Induction/HierAlgebra.lean` = 787 lines, `HierarchyN.lean` = 76 lines; "HA:n" / "HN:n" below are lines there); paper `paper/tex/3_5_Loop_Hierarchy.tex` (`eq_L-Keee` 73, `DefKsimLK` 89, `def_ELKLK` 97, `DefTHUST`/`def:op_thn` 109-115). Merged: `Induction/Step34Pins` (`STLI..STee`), `Path/DriftAlgebra` (`LoopGenN2`, `HierarchyN2`), `Loop/KLTreeDeriv.lean:1049` `KLK_isKLoop`, `Kernel/Evolution.lean:60` `ThetaN`.

### (i) Exponent table

Targets (math): for Hermitian `M`, `k ≥ 2`, `I = (σ,a)`, `|E|<2`, `0≤u<1`, `3 ≤ L`, `g = lam n`:
`genMat(𝓛_I) − ∂_u 𝒦_I = Θ^{(k)}_{u,σ}∘(𝓛−𝒦) (a) + Σ_{l=3}^k [𝒦^{(l)}∼(𝓛−𝒦)]^{(k)} + 𝓔^{LK×LK} + 𝓔^{G̃}` (`eq_L-Keee`), with `genMat(𝓛_I) = W^d Σ_{k<l}Σ_{a,b} 𝓛 S^{(B)} 𝓛 + 𝓔^{G̃}` (general-`n` `LoopGenN`).
No hypothesis needs `3 ≤ d` (`KLK_isKLoop` is stated for all `d`, needs `3 ≤ L`, `1 ≤ W`, `|E|<2`); the algebra is `d`-free apart from the rows below.

| # | RBM2D token (c9a24cf) | location | `d ≥ 3` replacement | constraint / slack |
|---|---|---|---|---|
| 1 | `(W:ℂ)^2` prefactor of `primBil`, `primBilLen`, `primBilLenR` | HA:46, 86, 92 | `(W:ℂ)^d` = `STksimLK`/`STelklk`/`treeEqRhs` prefactor | equal to the merged definitions' prefactor, exact |
| 2 | `(W:ℂ)^2` in `primBilLen_two_eq`, `primBilLenR_two_eq`, `thetaR_term`, `thetaL_term`, `couplingLen_two_eq_sum` (also `pow_ne_zero 2`, `((W:ℂ)^2)⁻¹` = `W^{-d}` of `Kn2sol`) | HA:400, 426, 473, 480, 485, 492, 509, 517, 531, 554 | `(W:ℂ)^d`, `pow_ne_zero d`, `((W:ℂ)^d)⁻¹` | `W ≠ 0` (`NeZero W`); exact |
| 3 | `(W:ℝ)^2` in `norm_primBil_le` | HA:256, 257, 294, 299, 305 | `(W:ℝ)^d` | `‖W^d‖ = W^d` |
| 4 | `(L:ℝ)^2` = `card (Z2 L)` in `norm_primBil_le` | HA:256, 260, 288, 294, 299, 305 | `(L:ℝ)^d` = `card (Zd d L)` (`card_Zd`, `Defs/Lattice.lean:62`) | bound `W^d n² L^d B_F B_G`; d=3,W=2,n=3,L=3: 1944 (d=2 form would be 324) |
| 5 | `(I.length:ℝ)^2` in `norm_primBil_le` | HA:256, 299, 305 | unchanged (number of pairs `k<l` ≤ `n²`) | dimension-free |
| 6 | `∑ b, ‖SB L a b‖ = 1` (`HA:243`, from `sum_nnnorm_SB_row`) | HA:243-248 | `sum_nnnorm_SB_row d L g hL a` (`Defs/Block.lean:124`) | row sum `a₀(1+2d g²) = 1`; d=3,g=1/2: 0.4+6·0.1 = 1.0 (below) |
| 7 | `Z2 L` (80 lines HA, 2 lines HN) | whole files | `Zd d L`; `Idx L W` → `Idx d L W` | R2 |
| 8 | `Theta_commute_SB L hL`, `thetaGenMat` (defined in RBM2D `Path/UBounds.lean:48`, not in these files) | HA:639, 642 | `Theta_commute_SB_of_three_le (g := g) hL` (`Propagator/Props4.lean:105`), `thetaKer` (`Kernel/Evolution.lean:52`) | needs `3 ≤ L`, `‖t μ‖<1`: `μ = m(σ_i)m(σ_{i+1})`, `‖μ‖=1` (`norm_cycProd`), `u<1` |
| 9 | docstring/check tokens `d = 2`, `W² n² L²`, compile checks at `L=3, W=3` | HA:21, 26, 249, 251, 714, 723, 704-771 | restated at `d=3`; compile checks redone at `sz0` | none are statements |
| 10 | `W^2 L^2 = N`, `ellT`, `scaleM`, `tailT`, `∀ᶠ`, `atTop` | `grep -c` finds none in code of either file (one docstring mention of `∀ᶠ N`, HA:12) | n/a | the two files carry no scale/threshold: no `∀ᶠ N`, no `𝔠`, no `δ` |

Statements false at `d ≥ 3` as ported: none (rows 1-8 are mechanical; the `Θ`-based `ϑ`/`vartheta` of RBM2D, flagged in portmap F-B, is not in these two files).

Vocabulary map (RBM2D → merged), generic `n = k`:
| RBM2D | merged | note |
|---|---|---|
| `Z2 L`, `Idx L W`, `W^2`, `SB L` | `Zd d L`, `Idx d L W`, `W^d`, `SB d L (sz.lam n)` | R1-R3 |
| `LLf L W E u M I` | `loopL d L W (blockMat d L W M) (zt E u) I` = `STLM … M σ a` at `I = loopOf σ a` (`loopM_eq_loopL`) | `STLI` is the same at `M = seqHflow sz n τ ω` |
| `KLoop.Kcal L W E u I` | `KLK d L g W E u I` = `sz.STKloop n E u σ a` | primitive eq. = `KLK_isKLoop` (`IsKLoop`, `treeEqRhs`) |
| `LKf`, `ksimLK`, `elklkN`, `egtN`, `llPairN` | `STLKI`, `STksimLK`, `STelklk`, `STegt` of `Step34Pins` are stated at `M = seqHflow … ω` only; the identity needs arbitrary Hermitian `M` (as `STLKM`, `STELKLKM`, `STEGtM` of `HierarchyN2`): new `M`-level definitions in `HierAlgebra`, bridged to `ST*` by `rfl` at `M = seqHflow` | needed, not a restatement of `ST*` |
| `thetaSig L E σ u A a` | `ThetaN d L g (fun i => STmsig E (σ i)) u A a` (`cycProd`, `thetaKer`) | at `k=2` equals `STthetaOp` (`μ₀ = μ₁ = m₁m₂`) |
| `genMat E u M I` | `genMat d L W g E u M I` (`Path/OneStep.lean:68`) | `g` explicit |
| `primBil`, `couplingLen`, `primRhs` | `treeEqRhs d L W g`-shaped sums with `cutGlueL/R` (`Loop/TreeRep.lean:84-142`) | `primRhs_sub`/`primRhs_split` need only bilinearity |
| `HierarchyN` (RBM2D pin `HierVocab:206`) | `HierarchyN d : Prop := ∀ sz n E, … ∀ k σ a, genMat … (loopOf σ a) − deriv (fun v => sz.STKloop n E v σ a) u = ThetaN… + Σ_{l∈Icc 3 k} … + … + …` in the `HierarchyN2` shape | `n=2`, `σ=(+,−)`: RHS terms = `STthetaOp`, `STELKLKM`, `STEGtM` (`Σ_{Icc 3 2} = 0`) |
| `loopGenN : LoopGenN` (`HN:33`, imported `RBM2D.Induction.LoopGenN`, `HN:8`) | **not in `main`** (`grep -rn "loopGenN\b\|LoopGenN\b" RBM3D` finds only `loopGenN2`/`LoopGenN2`); it is row ST2-28 (`Induction/LoopGenN`, 536 kept), not a dependency of T2095 (T2039-portmap:295-296) | see verdicts |

### (ii) One concrete nondegenerate instance
Data: `d=3, L=3, W=2 (W^d=8, N=(WL)^d=216), g=1/2, E=0 (m=i), u=1/2, n=k=3, σ=(+,−,+)`, `M` a fixed random Hermitian 216×216 matrix (seed 1; the identity is deterministic in `M`), four label triples `a`. Hypotheses: `3≤L`, `|E|<2`, `0≤u<1`, `M` Hermitian, `k≥2`, `1≤W`, `‖u μ_i‖ = 1/2 < 1` (`μ = (1,1,−1)`). `genMat` is computed exactly from its Lean definition: coordinates `(i,j,b)` with `gvarF` and `coordinateMatrix`, which contract to `½Σ_{ij} s_ij D²f[E_ij,E_ji]`, `s = W^{-d}SB`; `∂_u` along `zt E u`; `𝒦^{(2)}, 𝒦^{(3)}` from the primitive equation (`IsKLoop`) by RK4 (400 steps) with `MLoop` initial data; cut/glue on lists exactly as `cutGlueL/R`, `cutGlue`. Self-checks: the Hessian contraction against brute-force coordinate finite differences (`validate`), `K2` against `Kn2sol`, block-reduced loop against dense. Merged Lean instance for stage 1b: `sz0` at `n=0` (`L=4, W=32, lam=1/64`, `Defs/Sizes.lean:260-270`), `E=0`, `u=1/2`, `M=1`, `k=3`, `σ=(+,−,+)` (the Props are `∀ sz n`; every hypothesis holds there).
```
$ python3 scratchpad/T2095/hier_check.py validate
validate d=1,L=3,W=2 sigma=(True, False, True) a=[0, 1, 2]: fast=0.0512492373 brute(coordinates,fin.diff)=0.0512491264 |err|=1.20e-07
validate d=1,L=3,W=2 sigma=(True, False) a=[0, 1]: fast=-0.0656536579 brute(coordinates,fin.diff)=-0.0656536513 |err|=6.60e-09
validate d=1,L=3,W=2 sigma=(True, False, True, False) a=[0, 1, 1, 2]: fast=0.0261947083 brute(coordinates,fin.diff)=0.0261946776 |err|=3.12e-08
zder analytic -0.0490760022 vs finite diff -0.0490760022
$ python3 scratchpad/T2095/hier_check.py     # d=3 L=3 W=2 g=1/2 E=0 u=1/2 n=3 sigma=(+,-,+)
K2(+,-) vs W^-d Theta_u (Kn2sol, |m|^2=1): max err 6.6058269965196814e-15
loopL block-reduced vs dense: 0.0
loopL tensor einsum vs list : 1.0714213466115421e-20
a=(0, 1, 2): genMat=-0.0000102912+0.0000316229j  llPairN+egtN=-0.0000102912+0.0000316229j  |diff|=9.58e-21
      d_uK=0.0000000000+0.0000348554j  LHS=genMat-d_uK=-0.0000102912-0.0000032325j
      couplingLen l_K=2 vs ThetaN(L-K): |ksim2-ThetaN|=2.97e-17  (|ThetaN|=5.23e-05)
      ThetaN=0.00000240+0.00005226j ksim3=-0.00000985-0.00008368j elklk=0.00000581+0.00002197j egt=-0.00000865+0.00000621j
      RHS=-0.0000102912-0.0000032325j  |LHS-RHS|=2.93e-17  (|LHS|=1.079e-05)
a=(4, 4, 4): genMat=0.0000805846+0.0093209937j  llPairN+egtN=0.0000805846+0.0093209937j  |diff|=2.08e-17
      d_uK=0.0000000000+0.0212187363j  LHS=genMat-d_uK=0.0000805846-0.0118977426j
      couplingLen l_K=2 vs ThetaN(L-K): |ksim2-ThetaN|=6.29e-16  (|ThetaN|=8.50e-03)
      ThetaN=-0.00038023-0.00849444j ksim3=0.00037418-0.00929385j elklk=0.00002006+0.00401306j egt=0.00006657+0.00187749j
      RHS=0.0000805846-0.0118977426j  |LHS-RHS|=6.79e-16  (|LHS|=1.190e-02)
a=(7, 13, 20): genMat=-0.0000119057+0.0000292227j  llPairN+egtN=-0.0000119057+0.0000292227j  |diff|=1.45e-20
      d_uK=0.0000000000-0.0000000976j  LHS=genMat-d_uK=-0.0000119057+0.0000293203j
      couplingLen l_K=2 vs ThetaN(L-K): |ksim2-ThetaN|=2.34e-17  (|ThetaN|=2.00e-05)
      ThetaN=-0.00001662-0.00001104j ksim3=0.00000087+0.00000944j elklk=0.00000715+0.00003922j egt=-0.00000331-0.00000830j
      RHS=-0.0000119057+0.0000293203j  |LHS-RHS|=2.34e-17  (|LHS|=3.165e-05)
a=(26, 0, 5): genMat=0.0000040046+0.0000477416j  llPairN+egtN=0.0000040046+0.0000477416j  |diff|=4.21e-20
      d_uK=0.0000000000+0.0000161745j  LHS=genMat-d_uK=0.0000040046+0.0000315670j
      couplingLen l_K=2 vs ThetaN(L-K): |ksim2-ThetaN|=1.35e-17  (|ThetaN|=1.99e-05)
      ThetaN=0.00000478+0.00001929j ksim3=-0.00000008+0.00000503j elklk=-0.00000144+0.00000411j egt=0.00000075+0.00000314j
      RHS=0.0000040046+0.0000315670j  |LHS-RHS|=1.36e-17  (|LHS|=3.182e-05)
norm_primBil_le: |primBil F G I| = 5.4736  <=  W^d n^2 L^d = 8*9*27 = 1944
$ python3 <<EOF   # a=1/(1+2dg^2); a+2d g^2 a ; W^d n^2 L^d
SB row sum d=3,g=1/2: a + 2d g^2 a = 1.0  (a=0.400, g^2 a=0.100); L=3: +-e_i distinct
norm_primBil_le constant W^d n^2 L^d at d=3,W=2,n=3,L=3: 1944 ; d=2 form W^2 n^2 L^2 = 324
```
Reading: at all four `a`, `genMat = llPairN + egtN` (general-`n` `LoopGenN`, residual ≤ 4.2e-17) and `LHS = RHS` (residual ≤ 6.8e-16) with every term nonzero (`|ThetaN|`, `|ksim3|`, `|elklk|`, `|egt|` up to 8.5e-3, 9.3e-3, 4.0e-3, 1.9e-3 at `a=(4,4,4)`); `[𝒦^{(2)}∼(𝓛−𝒦)] = Θ∘(𝓛−𝒦)` (`couplingLen_two_Kval_eq_thetaOp`) to 6.3e-16.

### Verdicts
- `HierAlgebra` (`primBil`, `couplingLen`, `primRhs_sub/split`, `norm_primBil_le`, `couplingLen_two_Kval_eq_thetaOp`, matrix-level `loopDrift_sub_K_deriv_n`): PASS (exponents rows 1-8 close; instance above).
- `HierarchyN` Prop and the `n=2`, `σ=(+,−)` reduction to `HierarchyN2`: PASS.
- `hierarchyN : HierarchyN d` unconditional: BLOCKED. Its RBM2D proof (`HN:31-34`) is `rw [loopGenN …]` then `loopDrift_sub_K_deriv_n`; the general-`n` `LoopGenN` (`genMat 𝓛 = llPairN + egtN`, ST2-28, 536 kept lines) is not merged and not a dependency of T2095. Question for the dispatcher: authorize `hierarchyN` in the conditional form `(LoopGenN-form d) → HierarchyN d` with the general-`n` loop-generator `Prop` as an explicit hypothesis (stated in the `LoopGenN2` shape; the numeric check above verifies it at `d=3`), or add ST2-28 as a dependency. Name-clash note: ST2-28 will later need the same `LoopGenN d` name.
Overall verdict: BLOCKED.

## (a′) Preflight corrections — Sun Oct  4 01:56:27 UTC 2026
- The BLOCKED verdict of (a) (`hierarchyN` unconditional) is resolved by the ticket's Amend 1 (dispatcher V1, 2026-10-04 01:41 UTC): `STLoopGenNForm d` is defined here and `hierarchyN_of_loopGenN` is proved; no mathematical change.
- (a) vocabulary row "`LKf`, `ksimLK`, `elklkN`, `egtN`: new M-level definitions in HierAlgebra" is wrong for `main`: `STLIM`, `STLKIM`, `STksimLKM`, `STelklkM`, `STegtM` general-`n` forms already exist in merged `Induction/Step2Defs.lean` (imported through `Path/DriftAlgebra`); only `STllPairN` is new (see (b)).

## (b) Script output
```
$ lake build RBM3D.Induction.HierAlgebra RBM3D.Induction.HierarchyN   # worktree RBM3D-wt/T2095, branch t/T2095, tip 5f3813e
ℹ [3750/3751] Built RBM3D.Induction.HierAlgebra (3.9s)
ℹ [3751/3751] Built RBM3D.Induction.HierarchyN (2.9s)
Build completed successfully (3751 jobs).
$ #print axioms: 13 targets in the two files (build output) + 10 more declarations (scratch axchk.lean): distinct axiom sets
  23 [propext, Classical.choice, Quot.sound]
  targets printed: primBil_add_add primRhs_sub sum_primBilLen sum_primBilLenR sum_couplingLen couplingLen_eq_zero_outside primRhs_split norm_primBil_le couplingLen_two_Kval_eq_thetaOp loopDrift_sub_K_deriv_n hierarchyN_of_loopGenN hierarchyN_two loopGenNForm_two_of_loopGenN2 
$ lake build   # full library; the root does not import the new modules (the hub adds them at merge)
Build completed successfully (3836 jobs).
$ lake env lean precheck.lean   # import RBM3D + both new modules, #assert_rbm_axioms (registry pre-check)
axiom audit: 3017 theorems, 1145 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
105:  RBM.Ind.STLoopGenNForm: 2 [no certificate]
Sun Oct  4 01:58:24 UTC 2026;modules build exit=0;full lake build exit=0;precheck exit=0;axchk exit=0;Sun Oct  4 01:58:52 UTC 2026;
$ git diff --stat main...t/T2095 ; sorry/admit/native_decide/axiom count ; line counts
 RBM3D/Induction/HierAlgebra.lean | 902 +++++++++++++++++++++++++++++++++++++++
 RBM3D/Induction/HierarchyN.lean  | 253 +++++++++++
 RBM3D/Test/Axioms.lean           |   1 +
 3 files changed, 1156 insertions(+)
sorry-admit-native_decide-axiom hits: 0;  lines:      902 +      253
$ extract.py: target statements as in the files (proofs elided); primBil, primRhs_sub, couplingLen: see ports line
theorem primRhs_split (K D : LoopIdx (Zd d L) → ℂ) (I : LoopIdx (Zd d L))
    (hn : 2 ≤ I.length) :
    treeEqRhs d L W g (K + D) I - treeEqRhs d L W g K I
      = couplingLen d L W g 2 K D I
        + (∑ lK ∈ Finset.Icc 3 I.length, couplingLen d L W g lK K D I)
        + primBil d L W g D D I := by

theorem norm_primBil_le (hL : 3 ≤ L) (F G : LoopIdx (Zd d L) → ℂ)
    (I : LoopIdx (Zd d L)) (hI : I.WF) {BF BG : ℝ} (hBF0 : 0 ≤ BF) (hBG0 : 0 ≤ BG)
    (hBF : ∀ J : LoopIdx (Zd d L), J.WF → 2 ≤ J.length → J.length ≤ I.length → ‖F J‖ ≤ BF)
    (hBG : ∀ J : LoopIdx (Zd d L), J.WF → 2 ≤ J.length → J.length ≤ I.length → ‖G J‖ ≤ BG) :
    ‖primBil d L W g F G I‖ ≤ (W : ℝ) ^ d * (I.length : ℝ) ^ 2 * (L : ℝ) ^ d * BF * BG := by

theorem couplingLen_two_Kval_eq_thetaOp (d L W : ℕ) [NeZero L] [NeZero W] (g : ℝ) (hL : 3 ≤ L)
    (E : ℝ) (hE : |E| ≤ 2) (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u < 1)
    (D : LoopIdx (Zd d L) → ℂ) {k : ℕ} (hk : 2 ≤ k) (σ : Fin k → Bool) (a : Fin k → Zd d L) :
    couplingLen d L W g 2 (KLK d L g W E u) D (loopOf σ a)
      = ThetaN d L g (fun i => mSigma E (σ i)) u (fun v => D (loopOf σ v)) a := by

def STllPairN (n : ℕ) (E u : ℝ)
    (M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    (I : LoopIdx (Zd d (sz.L n))) : ℂ :=
  (((sz.W n : ℕ) : ℂ) ^ d) * ∑ k ∈ Finset.Icc 1 I.length, ∑ l' ∈ Finset.Ioc k I.length,
    ∑ a : Zd d (sz.L n), ∑ b : Zd d (sz.L n),
      STLIM sz n E u M (I.cutGlueL k l' a) * SB d (sz.L n) (sz.lam n) a b *
        STLIM sz n E u M (I.cutGlueR k l' b)

theorem loopDrift_sub_K_deriv_n {d : ℕ} (sz : Sizes d) (n : ℕ) (E : ℝ) (hE : |E| < 2) (u : ℝ)
    (hu0 : 0 ≤ u) (hu1 : u < 1)
    (M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    {k : ℕ} (hk : 2 ≤ k) (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)) :
    (sz.STllPairN n E u M (loopOf σ a) + sz.STegtM n E u M (loopOf σ a))
        - deriv (fun v : ℝ => sz.STKloop n E v σ a) u
      = ThetaN d (sz.L n) (sz.lam n) (fun i => mSigma E (σ i)) u
            (fun b => sz.STLKIM n E u M (loopOf σ b)) a
          + ∑ l ∈ Finset.Icc 3 k, sz.STksimLKM n E u M l (loopOf σ a)
          + sz.STelklkM n E u M (loopOf σ a) + sz.STegtM n E u M (loopOf σ a) := by

def STLoopGenNForm (d : ℕ) : Prop :=
  ∀ (sz : Sizes d) (n : ℕ) (E : ℝ), |E| < 2 → ∀ u : ℝ, 0 ≤ u → u < 1 →
    ∀ M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ, M.IsHermitian →
      ∀ (k : ℕ), 2 ≤ k → ∀ (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)),
        genMat d (sz.L n) (sz.W n) (sz.lam n) E u M (loopOf σ a) =
          sz.STllPairN n E u M (loopOf σ a) + sz.STegtM n E u M (loopOf σ a)

def HierarchyN (d : ℕ) : Prop :=
  ∀ (sz : Sizes d) (n : ℕ) (E : ℝ), |E| < 2 → ∀ u : ℝ, 0 ≤ u → u < 1 →
    ∀ M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ, M.IsHermitian →
      ∀ (k : ℕ), 2 ≤ k → ∀ (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)),
        genMat d (sz.L n) (sz.W n) (sz.lam n) E u M (loopOf σ a) -
            deriv (fun v : ℝ => sz.STKloop n E v σ a) u =
          ThetaN d (sz.L n) (sz.lam n) (fun i => mSigma E (σ i)) u
              (fun b => sz.STLKIM n E u M (loopOf σ b)) a +
            ∑ l ∈ Finset.Icc 3 k, sz.STksimLKM n E u M l (loopOf σ a) +
            sz.STelklkM n E u M (loopOf σ a) + sz.STegtM n E u M (loopOf σ a)

theorem hierarchyN_of_loopGenN (d : ℕ) : STLoopGenNForm d → HierarchyN d := by

theorem hierarchyN_two (d : ℕ) : HierarchyN d → HierarchyN2 d := by

theorem loopGenNForm_two_of_loopGenN2 (d : ℕ) (h : LoopGenN2 d) (sz : Sizes d) (n : ℕ) (E : ℝ)
    (hE : |E| < 2) (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u < 1)
    (M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (hM : M.IsHermitian)
    (a₁ a₂ : Zd d (sz.L n)) :
    genMat d (sz.L n) (sz.W n) (sz.lam n) E u M (loopOf ![true, false] ![a₁, a₂]) =
      sz.STllPairN n E u M (loopOf ![true, false] ![a₁, a₂]) +
        sz.STegtM n E u M (loopOf ![true, false] ![a₁, a₂]) := by

$ compiled nonempty instances (name, statement lines, applying term); d = 3, sz0 (L_0=4, W_0=32, lam_0=1/64), n=0, E=0, u=1/2, M=1, k=3 or 2
theorem HierAlgebra_check_norm_primBil_le :
    ‖primBil 3 3 2 (1 / 2) (fun _ => (1 : ℂ)) (fun _ => (1 : ℂ)) HierAlgebra_I0‖ ≤ 864 := by
  ... (tactic proof)

theorem HierAlgebra_check_primBil_value :
    primBil 3 3 2 (1 / 2) (fun _ => (1 : ℂ)) (fun _ => (1 : ℂ)) HierAlgebra_I0 = 216 := by
  ... (tactic proof)

theorem HierAlgebra_check_primRhs_split (K D : LoopIdx (Zd 3 3) → ℂ) :
  ... (statement: HierAlgebra.lean:814-818)
  primRhs_split 3 3 2 (1 / 2) K D HierAlgebra_I0 (by rw [HierAlgebra_I0_length])

theorem HierAlgebra_check_couplingLen_two (D : LoopIdx (Zd 3 3) → ℂ) :
  ... (statement: HierAlgebra.lean:823-827)
  couplingLen_two_Kval_eq_thetaOp 3 3 2 (1 / 2) (le_refl 3) 0 (by norm_num) (1 / 2)
    (by norm_num) (by norm_num) D (k := 3) (by norm_num) _ _

theorem HierAlgebra_check_algebra (K K' D : LoopIdx (Zd 3 3) → ℂ) :
  ... (statement: HierAlgebra.lean:834-852)
  ⟨primBil_add_left 3 3 2 (1 / 2) K K' D _, primBil_add_right 3 3 2 (1 / 2) D K K' _,
    primBil_add_add 3 3 2 (1 / 2) K D _, primRhs_sub 3 3 2 (1 / 2) K D _,
    sum_primBilLen 3 3 2 (1 / 2) K D _ (by decide), sum_primBilLenR 3 3 2 (1 / 2) K D _ (by decide),
    sum_couplingLen 3 3 2 (1 / 2) K D _ (by decide),
    couplingLen_eq_zero_outside 3 3 2 (1 / 2) K D _ (by decide)⟩

theorem HierAlgebra_check_loopDrift_sz0 :
  ... (statement: HierAlgebra.lean:862-883)
  loopDrift_sub_K_deriv_n sz0 0 0 (by norm_num) (1 / 2) (by norm_num) (by norm_num) 1
    (k := 3) (by norm_num) _ _

theorem HierarchyN_check_sz0 (h : STLoopGenNForm 3) :
  ... (statement: HierarchyN.lean:197-210)
  hierarchyN_of_loopGenN 3 h sz0 0 0 (by norm_num) (1 / 2) (by norm_num) (by norm_num) 1
    Matrix.isHermitian_one 3 (by norm_num) _ _

theorem HierarchyN_check_two_sz0 (h : HierarchyN 3) :
  ... (statement: HierarchyN.lean:216-225)
  hierarchyN_two 3 h sz0 0 0 (by norm_num) (1 / 2) (by norm_num) (by norm_num) 1
    Matrix.isHermitian_one 0 1

theorem HierarchyN_check_loopGenNForm_two_sz0 :
  ... (statement: HierarchyN.lean:231-237)
  loopGenNForm_two_of_loopGenN2 3 (loopGenN2 3) sz0 0 0 (by norm_num) (1 / 2) (by norm_num)
    (by norm_num) 1 Matrix.isHermitian_one 0 1
$ name clash: git grep -n -w -e NAME main -- RBM3D/*.lean, hits outside the two new files, 24 new public names
total hits: 0 (control: hierarchyN2 has 5 hits)
$ grep -nF -e "Z2" -e ") ^ 2" (remaining d = 2 tokens; the two ^2 are n^2 pairs)
RBM3D/Induction/HierAlgebra.lean:14:there), renaming rules R1-R4 of `docs/tickets/ST1-COMMON.md`: `Z2 L → Zd d
RBM3D/Induction/HierAlgebra.lean:258:    ‖primBil d L W g F G I‖ ≤ (W : ℝ) ^ d * (I.length : ℝ) ^ 2 * (L : ℝ) 
RBM3D/Induction/HierAlgebra.lean:307:    _ = (W : ℝ) ^ d * (I.length : ℝ) ^ 2 * (L : ℝ) ^ d * BF * BG := by
$ ports at c9a24cf (RBM2D HierAlgebra.lean:line -> RBM3D HierAlgebra.lean:line)
 primBil 45->49; primBil_self 49->53; primBil_add_left 52->56; primBil_add_right 56->60; primBil_add_add 60->64; primRhs_sub 70->75; primBilLen 
85->90; primBilLenR 91->96; couplingLen 98->103; sum_primBilLen 131->130; sum_primBilLenR 148->147; sum_couplingLen 171->170; 
couplingLen_eq_zero_outside 178->178; primRhs_split 214->214; norm_primBil_le 252->254; couplingLen_two_Kval_eq_thetaOp 602->620; 
loopDrift_sub_K_deriv_n 663->729;
HierarchyN.lean: hierarchyN HN:31 -> hierarchyN_of_loopGenN :69; HierVocab.lean:206 HierarchyN -> :56; HierVocab:548 LoopGenN -> STLoopGenNForm :42; 
HierVocab:539 llPairN -> STllPairN (HierAlgebra):693
$ git -C ../RBM2D --no-optional-locks log -1 --format=%h; ... diff --stat c9a24cf HEAD -- Induction/{HierAlgebra,HierarchyN,HierVocab}.lean
9e0f275
 RBM2D/Induction/HierAlgebra.lean | 129 +++----------
 RBM2D/Induction/HierVocab.lean   | 392 ++++++++-------------------------------
 RBM2D/Induction/HierarchyN.lean  |  51 +----
 3 files changed, 104 insertions(+), 468 deletions(-)
```

**Narrative (written Sun Oct  4 02:00:21 UTC 2026).**
- Ported: all 17 public declarations of RBM2D `HierAlgebra` (ports line above; nothing dropped) into `RBM3D/Induction/HierAlgebra.lean`, and the pin `HierarchyN` of `HierVocab` into `HierarchyN.lean`; RBM2D's unconditional `hierarchyN` is replaced by `hierarchyN_of_loopGenN : STLoopGenNForm d → HierarchyN d` (Amend 1); `STLoopGenNForm` (RBM2D `LoopGenN`) is defined and not proved here.
- d = 3 replacements, all rows 1-8 of (a)(i): `(W:ℂ)^2 → (W:ℂ)^d` (`primBil`, `primBilLen`, `primBilLenR`, the `_two_eq` lemmas); `(W:ℝ)^2 → (W:ℝ)^d` and `(L:ℝ)^2 → (L:ℝ)^d` (`card_Zd`) in `norm_primBil_le`: constant `W^d n² L^d B_F B_G` (`n²` counts the cut pairs, dimension free); `sum_nnnorm_SB_row d L g hL a`; `Theta_commute_SB_of_three_le`, `Theta_transpose_of_three_le`; `thetaSig` (RBM2D) becomes `ThetaN` (`cycProd`, `thetaKer`). No statement was false at d = 3 as ported.
- Residual differences from RBM2D statements: argument order `d L W g` first (`primBil d L W g K K' I`); `KLoop.primRhs`, `KLoop.Kcal` are `treeEqRhs d L W g`, `KLK d L g W E u`; `couplingLen_two_Kval_eq_thetaOp` has no `[NeZero k]` (only `2 ≤ k`) and concludes with `ThetaN … (mSigma E ∘ σ)`; `loopDrift_sub_K_deriv_n` is stated `∀ sz n` at `g = sz.lam n` in the merged `STLIM, STLKIM, STksimLKM, STelklkM, STegtM` and the new `STllPairN` (= `treeEqRhs` of `STLIM`, `rfl`) instead of RBM2D `LLf, LKf, ksimLK, elklkN, egtN, llPairN` at `(L W E u M)`.
- `HierarchyN d` has the shape of `HierarchyN2` (and of `STgDriftN` at `H = M`); `hierarchyN_two : HierarchyN d → HierarchyN2 d` and `loopGenNForm_two_of_loopGenN2` (unconditional, from `LoopGenN2 d`) are the two `n = 2`, `σ = (+,-)` reductions.
- Registry: one owed line `RBM.Ind.STLoopGenNForm` (Test/Axioms.lean, "ST2-28", DECISIONS §32); the pre-check above exits 0 with `STLoopGenNForm: 2` theorems resting on it (`hierarchyN_of_loopGenN`, `HierarchyN_check_sz0`). `HierarchyN` needs no line (`hierarchyN_of_loopGenN` concludes it).
- Instances: every public theorem except the two `rfl` lemmas `primBil_self`, `STllPairN_eq_treeEqRhs` has a compiled instance at d = 3 (`HierAlgebra_check_*`, `HierarchyN_check_*`); `HierarchyN_check_sz0` (k = 3, σ = (+,-,+), a = (0,1,2), at `sz0`) keeps `STLoopGenNForm 3` as hypothesis (ST2-28's pin; its value at d = 3, k = 3 is the numeric check of (a)(ii), not a Lean fact); `HierarchyN_check_two_sz0` keeps `HierarchyN 3`; everything else is discharged. `loopDrift_sub_K_deriv_n` is applied unconditionally at k = 3. The root import is the hub's (not done here).

## (c) Verified names (`#check` in scratch names.lean, exit 0, no error lines)
Mathlib/core: `Finset.sum_eq_single_of_mem, sum_ite_mem, sum_Ico_eq_sum_range, Ico_add_one_right_eq_Icc, add_sum_erase, sum_subset, sum_ite_eq, sum_pair, sum_range, Icc_eq_empty`; `Nat.card_Icc, Nat.card_Ioc`; `List.drop_eq_getElem_cons, getD_eq_getElem, set_eq_take_cons_drop, ext_getElem, getElem_set, getElem_ofFn`; `coe_finRotate`; `Matrix.smul_mul, Matrix.isHermitian_one`; `Complex.norm_natCast`.
RBM3D: `LoopIdx.wf_cutGlueL`, `LoopIdx.length_cutGlueL_le` (Loop/TreeRep.lean), `loopM_eq_loopL` (Loop/GLoopFlow.lean:127), `KLK_isKLoop` (Loop/KLTreeDeriv.lean:1049), `KLK_two_eq_kTwo` (Loop/KLTree.lean:239), `sum_nnnorm_SB_row` (Defs/Block.lean:124), `sum_SB_row` (Defs/Block.lean:108), `SB_transpose` (Defs/Block.lean:58), `card_Zd` (Defs/Lattice.lean:67), `norm_mul_mSigma_lt_one` (Defs/Semicircle.lean:91), `Theta_commute_SB_of_three_le` (Propagator/Props4.lean:105), `Theta_transpose_of_three_le` (Props4.lean:95). Names verified absent: none searched.

## (d) Open issues and paper-delta candidates
- T2095a: `hierarchyN` is conditional here (`STLoopGenNForm d → HierarchyN d`); RBM2D proves it unconditionally with `loopGenN`. ST2-28 must prove `STLoopGenNForm d` to remove the hypothesis (ticket Amend 1, DECISIONS §32). No paper statement changes.
- T2095b: the operator of `DefTHUST` (`3_5:109`) is the merged `ThetaN` (`thetaKer = μ S Θ_{tμ}`, `cycProd`); at k = 2 it equals `STthetaOp` (proved inside `hierarchyN_two`). No change of mathematics.
- Open (a)-vs-main discrepancy recorded in (a′): the general-`n` M-level vocabulary already existed in `Step2Defs`.
- `STLoopGenNForm` for k ≥ 3 is not proved or refuted in Lean; (a)(ii) checks it numerically at d = 3, L = 3, W = 2, g = 1/2, n = 3.
