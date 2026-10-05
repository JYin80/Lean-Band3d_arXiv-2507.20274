/-
Release check for T2222 (dispatcher V1, Mon Oct  5 2026; CLAUDE.md §4 step 0; DECISIONS §16, §17, §20, §29,
§45 O2, §64 (4), §67, §68).
S6-06 (stochastic layer ST-5, Step 6): proves the merged pin `STExpLKLKHi` (`(eq:Exp(L-K)1)` `6:58-62`;
`RBM3D/Induction/Step6Pins.lean:301`, unchanged) in the new file `RBM3D/Induction/ExpEtermsA.lean`; deletes its owed
registry line (`RBM3D/Test/Axioms.lean:232`).
Section 1: the merged names the proof uses (exact namespaces, from the enclosing `namespace … end` blocks; file and
last commit on `main` 63d62b4).
Section 2: the statements of the public theorems of `ExpEtermsA.lean` as closed `Prop`s, in the temporary namespace
`RBM.Gauss.Sizes.T2222Check` (T2222 proves each, same name, in `RBM.Gauss.Sizes`; `{d : ℕ}` first).
Section 3: the statements of the instances T2222 compiles (`RBM.Gauss.Step6Inst`; the merged Step-6 instance data), as
`Prop`-valued `example`s (no proof obligation).
Statement and `#check` only: no theorem, no proof, no `sorry`.  Never imported or merged.
Imports: merged modules only, not `RBM3D`.  No Mathlib lemma is `#check`ed.
Run from the main worktree: `lake env lean docs/tickets/checks/T2222-check.lean`.
-/
import RBM3D.Induction.Step6Kit
import RBM3D.Induction.KDecay
import RBM3D.Induction.ScaleFacts3
import RBM3D.Induction.ScaleFacts
import RBM3D.Induction.Step2Iterate
import RBM3D.Induction.Step5Kit
import RBM3D.Induction.AzumaProxyN2
import RBM3D.Loop.KLTree
import RBM3D.Loop.Primitive
import RBM3D.Loop.GLoopFlow
import RBM3D.Defs.Tail
import RBM3D.Gauss.DominationAt

set_option linter.style.longLine false

/-! ## 1. Merged names -/

-- `RBM3D/Induction/Step6Pins.lean` (cda3bb2; S6-01 = T2204): the pin, its conclusion, the window, the shape
#check @RBM.Gauss.Sizes.STExpLKLKHi
#check @RBM.Gauss.Sizes.STExpLKLKHiConcl
#check @RBM.Gauss.Sizes.STExpELKLK
#check @RBM.Gauss.Sizes.STDriftHi
#check @RBM.Gauss.Sizes.STIngR6
#check @RBM.Gauss.Sizes.STStep6Concl
#check @RBM.Gauss.Sizes.STExpDuhamelZ
#check @RBM.Gauss.Sizes.STExpIntIII
#check @RBM.Gauss.Step6Inst.InstIng6Concl
-- `RBM3D/Induction/Step6Kit.lean` (9e0d6a7; S6-02 = T2211): helpers, the three consumers, the merged instances
#check @RBM.Gauss.Sizes.st6_prec_det_iff
#check @RBM.Gauss.Sizes.st6_lam_pos
#check @RBM.Gauss.Sizes.st6_flowE_lt_two
#check @RBM.Gauss.Sizes.st6_flowE_le
#check @RBM.Gauss.Sizes.st6_mE_im_ge
#check @RBM.Gauss.Sizes.ST_step6_caseIII_of_pins
#check @RBM.Gauss.Sizes.ST_step6_caseII_of_pins
#check @RBM.Gauss.Sizes.ST_step6_caseI_of_pins
#check @RBM.Gauss.Step6Inst.inst_expLKLK_I
#check @RBM.Gauss.Step6Inst.inst_expLKLK_II
#check @RBM.Gauss.Step6Inst.inst_expLKLK_III
#check @RBM.Gauss.Step6Inst.inst_skeleton6I
#check @RBM.Gauss.Step6Inst.inst_skeleton6II
#check @RBM.Gauss.Step6Inst.inst_skeleton6III
-- `RBM3D/Induction/Step5Pins.lean` (d7da51e), `Induction/Step2Defs.lean` (86124dc): the random drift term
#check @RBM.Gauss.Sizes.STELKLK
#check @RBM.Gauss.Sizes.STIdx2
#check @RBM.Gauss.Sizes.STELKLKM
#check @RBM.Gauss.Sizes.STLKM
#check @RBM.Gauss.Sizes.STLM
#check @RBM.Gauss.Sizes.STLM_seqHflow
-- `RBM3D/Induction/Step34Pins.lean` (fc76526): Step 4 maximum bound, Step 5 decay (premises of `STIngR6`)
#check @RBM.Gauss.Sizes.STLKU
#check @RBM.Gauss.Sizes.STGdecayW
-- `RBM3D/Induction/Defs.lean` (64bdfd3)
#check @RBM.Gauss.Sizes.STKloop
#check @RBM.Gauss.Sizes.STWB
#check @RBM.Gauss.Sizes.STFlow
#check @RBM.Gauss.Sizes.STflowE
-- `RBM3D/Defs/Sizes.lean` (0a873f1)
#check @RBM.Gauss.Sizes
#check @RBM.Gauss.Sizes.neZeroL
#check @RBM.Gauss.Idx
#check @RBM.Gauss.zdistInf
#check @RBM.Gauss.Sizes.Bctl
#check @RBM.Gauss.Sizes.size
#check @RBM.Gauss.Sizes.SizeTendsto
#check @RBM.Gauss.Sizes.Bandwidth
#check @RBM.Gauss.Sizes.Admissible
#check @RBM.Gauss.Sizes.WO
#check @RBM.Gauss.Sizes.locDomain
-- `RBM3D/Defs/Params.lean` (c3f3d5d), `Defs/Tail.lean` (c8e4f17)
#check @RBM.ellT
#check @RBM.Bparam
#check @RBM.one_le_ellT
#check @RBM.BparamR
#check @RBM.tailT
#check @RBM.BparamR_natCast
-- `RBM3D/Induction/KDecay.lean` (dab074c; S3-06 = T2129): the lattice sum of the tail (already merged)
#check @RBM.Loop.KDecay_sum_tailT_le
#check @RBM.Loop.KDecay_tailC
#check @RBM.Loop.KDecay_one_le_tailC
-- `RBM3D/Defs/Block.lean` (a722f63)
#check @RBM.SB
#check @RBM.SB_transpose
#check @RBM.sum_norm_SB_row
-- `RBM3D/Loop/GLoopFlow.lean` (868b3b4), `Gauss/FineModel.lean` (0a873f1), `Loop/GLoop.lean` (e0c58e6): the envelope
#check @RBM.Gauss.Sizes.Lloop
#check @RBM.Gauss.Sizes.norm_Lloop_le
#check @RBM.Gauss.Sizes.SeqΩ
#check @RBM.Gauss.Sizes.seqP
#check @RBM.Gauss.etaT
#check @RBM.Gauss.etaT_pos
-- `RBM3D/Loop/Primitive.lean` (58329b9), `Loop/KLTree.lean` (b06ff9b): `𝒦^{(2)} = kTwo`, `‖kTwo‖ ≤ W^{-d}(1-u)⁻¹`
#check @RBM.Loop.kTwo
#check @RBM.Loop.norm_kTwo_le
#check @RBM.Loop.KLK
#check @RBM.Loop.KLloopOf
#check @RBM.Loop.KLK_two_eq_kTwo
-- `RBM3D/Defs/Semicircle.lean` (fbc9870)
#check @RBM.mE
#check @RBM.mSigma
#check @RBM.norm_mSigma
#check @RBM.lemT
-- `RBM3D/Defs/StochDomAt.lean` (9e2b00f): the one `≺`, the union of two failure events
#check @RBM.Path.TimeIcc
#check @RBM.badSetAt
#check @RBM.StochDomAt
#check @RBM.Gauss.Sizes.Prec
#check @RBM.Gauss.Sizes.tendsto_size
#check @RBM.StochDomAt.of_subset_union
#check @RBM.StochDomAt.of_le_left
#check @RBM.StochDomAt.highProb
-- `RBM3D/Gauss/DominationAt.lean` (9e2b00f): the portmap's `≺ → 𝔼` bridge (alternative route)
#check @RBM.Gauss.momentDomAt_of_stochDomAt
-- scale facts: `Induction/ScaleFacts.lean` (5d1e6b1), `ScaleFacts3.lean` (7c3072a), `Step2Iterate.lean` (c5bbae7),
-- `Step5Kit.lean` (85e43db), `AzumaProxyN2.lean` (88183f4)
#check @RBM.Gauss.Sizes.STBctl_pos
#check @RBM.Gauss.Sizes.st_Bctl_ge
#check @RBM.Gauss.Sizes.ST_one_sub_lemT
#check @RBM.Gauss.Sizes.st5_t_lt_one
#check @RBM.Ind.AzumaProxyN_etaT_inv_le_pub
#check @RBM.Ind.AzumaProxyN_inv_one_sub_le_pub
-- instance data: `Defs/Sizes.lean`, `Induction/Defs.lean`, `Induction/Step34Pins.lean`
#check @RBM.Gauss.SizesInst.sz0
#check @RBM.Gauss.InductionDefsInst.z0
#check @RBM.Gauss.InductionDefsInst.sInst
#check @RBM.Gauss.InductionDefsInst.tInst
#check @RBM.Gauss.Step34Inst.szB
#check @RBM.Gauss.Step34Inst.zB
#check @RBM.Gauss.Sizes.LWtermEXP

/-! ## 2. Statements of the public theorems of `ExpEtermsA.lean` (closed `Prop`s) -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal

namespace RBM.Gauss.Sizes.T2222Check

open RBM RBM.Loop RBM.Path RBM.Gauss

/-! ### Deterministic steps (one matrix, one size) -/

-- (window) `𝓔^{LK×LK} = W^d Σ_{x,y} (𝓛-𝒦)_{σ,(x,a₂)} S_{xy} (𝓛-𝒦)_{σ,(a₁,y)}` with the first factor at most a maximum
-- `M` and the second at most a profile `f(y)`: `Σ_x |S_{xy}| = 1` (`SB_transpose`, `sum_norm_SB_row`, `3 ≤ L`).
-- RBM2D pattern: `MLExpDrift_norm_sbSum_le` (`MLExpDrift.lean:141`, private), without the window `R`.
def expLK_window_le : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (n : ℕ) (E u : ℝ)
    (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) (M : ℝ) (f : Zd d (sz.L n) → ℝ),
    (∀ x, ‖sz.STLKM n E u H σ ![x, a 1]‖ ≤ M) → (∀ y, ‖sz.STLKM n E u H σ ![a 0, y]‖ ≤ f y) →
      ‖sz.STELKLKM n E u H σ a‖ ≤ ((sz.W n : ℕ) : ℝ) ^ d * M * ∑ y : Zd d (sz.L n), f y

-- (lattice sum) `Σ_b B_{u,|a-b|} e^{-(|a-b|/ℓ_u)^{1/2}} ≲ (1-u)⁻¹` of `6:61`, in the form of the right side of
-- `STGdecayW` (`W^d · STWB = Bparam`): the merged `KDecay_sum_tailT_le` (`KDecay.lean:1241`) after `y ↦ a - y`,
-- `BparamR_natCast`, `√x = x^{1/2}`.
def expLK_latticeSum : Prop :=
  ∀ {d : ℕ} (sz : Sizes d), 2 ≤ d → ∀ (n : ℕ) {u : ℝ}, 0 ≤ sz.lam n → u < 1 → ∀ a : Zd d (sz.L n),
    ((sz.W n : ℕ) : ℝ) ^ d * ∑ y : Zd d (sz.L n),
        sz.STWB n u (zdistInf d (sz.L n) (a - y)) *
          Real.exp (-(((zdistInf d (sz.L n) (a - y) : ℕ) : ℝ) / ellT (sz.L n) (sz.lam n) u) ^ (1 / 2 : ℝ)) ≤
      KDecay_tailC d / (1 - u)

-- (envelope) `|𝓔^{LK×LK}| ≤ W^d L^d (η_u^{-2} + (1-u)⁻¹)²` for every sample (`norm_Lloop_le`, `KLK_two_eq_kTwo`,
-- `norm_kTwo_le`, `norm_mSigma`).  RBM2D pattern: `MLExpDrift_env_X` (`MLExpDrift.lean:610`, private).
def expLK_env : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (n : ℕ) {E u : ℝ}, |E| < 2 → 0 ≤ u → u < 1 →
    ∀ (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) (ω : sz.SeqΩ),
      ‖sz.STELKLK n E u σ a ω‖ ≤
        ((sz.W n : ℕ) : ℝ) ^ d * ((sz.L n : ℕ) : ℝ) ^ d * ((etaT E u)⁻¹ ^ 2 + (1 - u)⁻¹) ^ 2

/-! ### Along the sequence -/

-- (envelope is polynomial) on the flow, at the right end `t ≤ lemT z`: `1 - t ≥ Im z/(1+|z|) ≥ N^{-1+ε}/4`
-- (`ST_one_sub_lemT`, `locDomain`), `Im m ≥ √(2κ)/2` (`st6_mE_im_ge`, `st6_flowE_le`); `W^d L^d = N`.
def expLK_env_poly : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) {κ ε 𝔠 𝔡 : ℝ}, 0 < κ → 0 < ε → ∀ {z : ℕ → ℂ}, STFlow sz κ ε 𝔠 𝔡 z →
    ∀ {t : ℕ → ℝ}, (∀ n, t n ≤ lemT (z n)) →
      ∀ᶠ n in atTop, ((sz.W n : ℕ) : ℝ) ^ d * ((sz.L n : ℕ) : ℝ) ^ d *
          ((etaT (STflowE z n) (t n))⁻¹ ^ 2 + (1 - t n)⁻¹) ^ 2 ≤ ((sz.size n : ℕ) : ℝ) ^ (6 : ℝ)

-- (decay step, random) `𝓔^{LK×LK}_{u,σ,a} ≺ (1-u)⁻¹ (W^{-d}B_{u,0})^{11/5}` uniformly in `u ∈ [s,t]`: on the
-- complement of the two failure events of `STLKU` (`k = 2`, factor `(x,a₂)`) and `STGdecayW … 0` (factor `(a₁,y)`,
-- at `D = 2/𝔠`) every bound holds for every index at once (`badSetAt` is the union over the index), so
-- `expLK_window_le` + `expLK_latticeSum` give `N^{2τ'}(C_d (1-u)⁻¹ B^{11/5} + N B² W^{-D})`; `W^{-D} ≤ N^{-2}` from
-- `Bandwidth`, `B ≥ N^{-1}` (`0 ≤ u < 1`); `StochDomAt.of_subset_union`.  No grid lift (both inputs are uniform in
-- `u`, §64 (4)).
def expLK_prec : Prop :=
  ∀ {d : ℕ} (sz : Sizes d), 2 ≤ d → ∀ {𝔠 : ℝ}, 0 < 𝔠 → sz.SizeTendsto → sz.Bandwidth 𝔠 →
    (∀ᶠ n in atTop, 0 ≤ sz.lam n) → ∀ {E s t : ℕ → ℝ}, (∀ n, 0 ≤ s n) → (∀ n, t n < 1) →
      STLKU sz E s t → STGdecayW sz E s t 0 →
        sz.Prec (U := STIdx2 sz s t)
          (fun n p ω => ‖sz.STELKLK n (E n) (p.1 : ℝ) p.2.1 p.2.2 ω‖)
          (fun n p _ => (1 - (p.1 : ℝ))⁻¹ * (sz.Bctl n (p.1 : ℝ)) ^ (11 / 5 : ℝ))

-- (`≺ → 𝔼`) the first moment outside the failure event (RBM2D `MLExpDrift_first_moment` `MLExpDrift.lean:717`,
-- private; no measurability needed) with the polynomial envelope at `t`, and the floor
-- `(1-u)⁻¹ B^{11/5} ≥ N^{-11/5}`; the deterministic `Prec` via `st6_prec_det_iff`.
def expLK_expect : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) {E s t : ℕ → ℝ} {Kenv : ℝ}, sz.SizeTendsto → (∀ n, |E n| < 2) →
    (∀ n, 0 ≤ s n) → (∀ n, t n < 1) →
    (∀ᶠ n in atTop, ((sz.W n : ℕ) : ℝ) ^ d * ((sz.L n : ℕ) : ℝ) ^ d *
        ((etaT (E n) (t n))⁻¹ ^ 2 + (1 - t n)⁻¹) ^ 2 ≤ ((sz.size n : ℕ) : ℝ) ^ Kenv) →
    sz.Prec (U := STIdx2 sz s t)
        (fun n p ω => ‖sz.STELKLK n (E n) (p.1 : ℝ) p.2.1 p.2.2 ω‖)
        (fun n p _ => (1 - (p.1 : ℝ))⁻¹ * (sz.Bctl n (p.1 : ℝ)) ^ (11 / 5 : ℝ)) →
      STExpLKLKHiConcl sz E s t

-- (the conclusion from the premises it uses) `STFlow`, `0 ≤ s`, `t ≤ lemT z`, `STLKU`, `STGdecayW … 0`.
def STExpLKLKHiConcl_of_LKU : Prop :=
  ∀ {d : ℕ} (sz : Sizes d), 3 ≤ d → ∀ {κ ε 𝔠 𝔡 : ℝ}, 0 < κ → 0 < ε → ∀ {z : ℕ → ℂ},
    STFlow sz κ ε 𝔠 𝔡 z → ∀ {s t : ℕ → ℝ}, (∀ n, 0 ≤ s n) → (∀ n, t n ≤ lemT (z n)) →
      STLKU sz (STflowE z) s t → STGdecayW sz (STflowE z) s t 0 → STExpLKLKHiConcl sz (STflowE z) s t

-- The merged pin `STExpLKLKHi` (`Step6Pins.lean:301`), proved (`𝔠_d = 1/100`; the window `STDriftHi` and the premises
-- `STLK`, `STDecay`, `STExp2` at `s`, `STConStInd`, `STStep2Core`, `STLmaxU` are not used).
def stExpLKLKHi_holds : Prop := ∀ d : ℕ, STExpLKLKHi d

end RBM.Gauss.Sizes.T2222Check

/-! ## 3. The statements of the instances T2222 compiles -/

namespace RBM.Gauss.Step6Inst.T2222Check

open RBM RBM.Gauss RBM.Gauss.Sizes RBM.Gauss.SizesInst RBM.Gauss.InductionDefsInst RBM.Gauss.Step34Inst
  RBM.Gauss.Step5Inst RBM.Path RBM.Loop Filter

-- statement of `inst_expLKLK_I_holds` (the merged `inst_expLKLK_I` with `h := stExpLKLKHi_holds 3`; regime (i) data)
example : Prop :=
  InstIng6Concl (fun sz E s t => STExpLKLKHiConcl sz E s t) szB zB (fun _ => 7 / 8) (fun _ => 15 / 16)

-- statement of `inst_expLKLK_II_holds` (regime (ii) data)
example : Prop :=
  InstIng6Concl (fun sz E s t => STExpLKLKHiConcl sz E s t) szB zB (fun _ => 15 / 16) (fun _ => 31 / 32)

-- statement of `inst_expLKLK_III_holds` (regime (iii) data)
example : Prop :=
  InstIng6Concl (fun sz E s t => STExpLKLKHiConcl sz E s t) sz0 z0 sInst tInst

-- statement of `inst_skeleton6III_LK` (the merged `inst_skeleton6III` with `hLK := stExpLKLKHi_holds 3`)
example : Prop :=
  LWtermEXP 3 → STExpDuhamelZ 3 → STExpIntIII 3 →
    InstIng6Concl (fun sz E s t => STStep6Concl sz E s t) sz0 z0 sInst tInst

-- statement of `inst_expLK_latticeSum` (`expLK_latticeSum` at `sz0`, `n = 0`, `u = 1/2`, `a = 0`)
example : Prop :=
  ((sz0.W 0 : ℕ) : ℝ) ^ 3 * ∑ y : Zd 3 (sz0.L 0),
      sz0.STWB 0 (1 / 2) (zdistInf 3 (sz0.L 0) ((0 : Zd 3 (sz0.L 0)) - y)) *
        Real.exp (-(((zdistInf 3 (sz0.L 0) ((0 : Zd 3 (sz0.L 0)) - y) : ℕ) : ℝ) /
          ellT (sz0.L 0) (sz0.lam 0) (1 / 2)) ^ (1 / 2 : ℝ)) ≤
    KDecay_tailC 3 / (1 - 1 / 2)

-- statement of `inst_expLK_env` (`expLK_env` at `sz0`, `n = 0`, `E = u = 1/2`, `σ = (+,-)`, `a = (0,0)`)
example : Prop :=
  ∀ ω : sz0.SeqΩ,
    ‖sz0.STELKLK 0 (1 / 2) (1 / 2) ![true, false] ![(0 : Zd 3 (sz0.L 0)), 0] ω‖ ≤
      ((sz0.W 0 : ℕ) : ℝ) ^ 3 * ((sz0.L 0 : ℕ) : ℝ) ^ 3 *
        ((etaT (1 / 2) (1 / 2))⁻¹ ^ 2 + (1 - (1 / 2 : ℝ))⁻¹) ^ 2

end RBM.Gauss.Step6Inst.T2222Check
