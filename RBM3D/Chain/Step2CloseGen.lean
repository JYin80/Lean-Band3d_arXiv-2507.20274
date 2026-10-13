/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Chain.Step2IterGen2
import RBM3D.Chain.OptL2Gen
import RBM3D.Induction.LocalAvg2
import RBM3D.Evolution.FarEntry

/-!
# Step 2 over the carrier: the `STGijDecgL` reader, section 12.2, band corollary (BA-T row T1b)

Ticket T2478.  Design `docs/reports/T2379-design.md` row T1, check file
`docs/tickets/checks/T2478-check.lean`.  The band files `Induction/Step2Iterate.lean`,
`Induction/LocalAvg2.lean` are **not** edited.  No `BA/` import, no kernel is defined.

* **Target 9 (GMN-C1).**  `stStep2LocalPT_of_L2decayDecG`, `stLocalAvgOfL2_holdsDecG`: the generic
  reader of `(Gt_bound_flow)` per time and the closing pin `STLocalAvgOfL2gL`, with the window input
  `STGijGEXgL` replaced by `STGijDecgL` (`Chain/CltGen.lean:94`; band source
  `bandFM_STGijDecgL_of_three_le`, `Evolution/FarEntry.lean:1724`).  The loop premise of
  `STGijDecgL` is `(eq:L2_decay)` for both mixed charges (`L_swap`) at
  `Φ_n(a,b)² = N^{τ/4} W^{-d} B_{u,|a-b|}`, `Ψ_n = W^{-d/2}`.  The right side `R` of `STGijDecgL`
  is `≤ C₂ N^{τ/8} (W^{-d} B_{u,r})^{1/2}`, `r = |[x]-[y]|`: the profile sum by the shift lemma
  `B_{u,K'} ≤ (j+1)^{d-2} B_{u,K}` for `K ≤ K'+j` and the lattice sum
  `Σ_a e^{-γ|a-c|_∞} ≤ (2/(1-e^{-γ/d}))^d`; the `Ψ` term by
  `W^{-d} ≤ cB⁻¹ (r+1)^{d-2} W^{-d}B_{u,r}` (`cB W^{-d} ≤ W^{-d} B_{u,0}`); the floor `W^{-D}` by
  `cB W^{-d} (L+1)^{-(d-2)} ≥ W^{-2D}` (`D = (d + (d-2)/𝔠 + 1)/2`, `L ≤ N ≤ W^{1/𝔠}`).  The
  shift lemma on the explicit `B` replaces the regularity `(eq:Psirelations)` (`7_8:2033-2050`).
* **Target 10.**  The class `Step2IterGen_ListLink` (`𝓛 = 𝓛_I` at `KLloopOf`; `𝒦_I` at `KLloopOf`
  is `𝒦`), its band discharge, and the generic list identities of section 12.2:
  `STthetaOpg_eq_ThetaN`, `STLKMg_eq_STLKIMg`, `STLMg_eq_STLIMg`, `STELKLKMg_eq_STelklkMg`,
  `STEGtMg_eq_STegtMg`, `STEEMg_eq_STeeMg`, `STgAg_eq_STgANg`, `STgDriftg_eq_STgDriftNg`.  The
  consistency theorem from the all-`m` grid pin to `STGridMart` is not restated (TN-C4: the only
  grid input is `STGridMartgL`).
* **Target 11.**  The band corollary `step2CloseGen_step2_of_pinsLW'` (`STStep2 d` for `3 ≤ d`
  through `ST_step2_of_pinsg`, with `stOptL2_of_pinsg` and `stLocalAvgOfL2_holdsDecG` as the
  producers of `STOptL2`, `STLocalAvgOfL2`), compiled nonempty instances of targets 9-11 at
  `d = 3`, and the band re-derivation of `stLocalAvgOfL2_holds` from target 9.
-/

set_option linter.style.longLine false

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.setOption false

open private la2_zdistInf_add_le la2_zdistInf_neg la2_zdistInf_zero from RBM3D.Induction.LocalAvg2

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal

noncomputable section

namespace RBM.BA

open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes

/-! ## 1. Target 10: section 12.2 over the carrier (`Step2Iterate:1586-1728`) -/

/-- **Target 10, the list-index link of section 12.2** (`Step2IterGen_ListLink`, `Step2Iterate.lean:1586-1700`): `𝓛^{(k)}_{σ,a}` of a fine matrix is
`𝓛_I` at the list index `KLloopOf σ a` (band `STLM_eq_STLIM`, model-free through `loopM_eq_loopL`), and `𝒦_I` at `KLloopOf σ a` is `𝒦^{(k)}_{σ,a}`
(band: definitional; BA `baStep2Mat_KI`). -/
def Step2IterGen_ListLink {d : ℕ} {sz : Sizes d} (Cm : Step2Mat sz) : Prop :=
  (∀ (n : ℕ) (u : ℝ) (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (k : ℕ)
      (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)),
      Cm.LM n u H σ a = Cm.LIM n u H (KLloopOf d (sz.L n) σ a)) ∧
    ∀ (n : ℕ) (u : ℝ) (k : ℕ) (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)),
      Cm.KI n u (KLloopOf d (sz.L n) σ a) = Cm.K n u σ a

/-- **Band discharge of `Step2IterGen_ListLink`** (`STLM_eq_STLIM`, `Step2Iterate.lean:1594`; `𝒦_I` at `KLloopOf` is `STKloop` by definition). -/
theorem step2IterGen_listLink_band {d : ℕ} (sz : Sizes d) (E : ℕ → ℝ) :
    Step2IterGen_ListLink (bandStep2Mat sz E) :=
  ⟨fun n u H k σ a => STLM_eq_STLIM sz n (E n) u H σ a, fun n u k σ a => rfl⟩

section Ident

variable {d : ℕ} {sz : Sizes d} (Cm : Step2Mat sz)

/-- `Θ^{(2)}` of `Step2Defs` §1 is the `ThetaN` of `Chain/Step2Gen` at `m = 2` (band `STthetaOp_eq_ThetaN`, `Step2Iterate.lean:1608`); definitional. -/
theorem STthetaOpg_eq_ThetaN (n : ℕ) (u : ℝ) (σ : Fin 2 → Bool) (A : (Fin 2 → Zd d (sz.L n)) → ℂ)
    (a : Fin 2 → Zd d (sz.L n)) :
    STthetaOpg Cm n u σ A a = Step2Gen_ThetaN Cm.toFlowFM n σ u A a := rfl

variable (hL : Step2IterGen_ListLink Cm)
include hL

/-- `STLMg = STLIMg ∘ KLloopOf` (band `STLM_eq_STLIM`, `Step2Iterate.lean:1594`), from the class. -/
theorem STLMg_eq_STLIMg (n : ℕ) (u : ℝ) (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    {m : ℕ} (σ : Fin m → Bool) (a : Fin m → Zd d (sz.L n)) :
    STLMg Cm n u H σ a = STLIMg Cm n u H (KLloopOf d (sz.L n) σ a) := hL.1 n u H m σ a

/-- `STLKMg = STLKIMg ∘ KLloopOf` (band `STLKM_eq_STLKIM`, `Step2Iterate.lean:1586`). -/
theorem STLKMg_eq_STLKIMg (n : ℕ) (u : ℝ) (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    {m : ℕ} (σ : Fin m → Bool) (a : Fin m → Zd d (sz.L n)) :
    STLKMg Cm n u H σ a = STLKIMg Cm n u H (KLloopOf d (sz.L n) σ a) := by
  unfold STLKMg STLKIMg
  rw [STLMg_eq_STLIMg Cm hL, hL.2 n u m σ a]

/-- `ℰ^{(𝓛-𝒦)×(𝓛-𝒦),(2)}` is the general-`n` term at the loop length `2` (band `STELKLKM_eq_STelklkM`, `Step2Iterate.lean:1638`). -/
theorem STELKLKMg_eq_STelklkMg (n : ℕ) (u : ℝ) (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) :
    STELKLKMg Cm n u H σ a = STelklkMg Cm n u H (KLloopOf d (sz.L n) σ a) := by
  unfold STELKLKMg STelklkMg
  rw [KLloopOf_length2]
  have h1 : Finset.Icc 1 2 = {1, 2} := by decide
  have h2 : Finset.Ioc 1 2 = {2} := by decide
  have h3 : Finset.Ioc 2 2 = ∅ := by decide
  rw [h1, Finset.sum_pair (by norm_num : (1 : ℕ) ≠ 2), h2, h3]
  simp only [Finset.sum_singleton, Finset.sum_empty, add_zero, KLloopOf_cutL, KLloopOf_cutR,
    STLKMg_eq_STLKIMg Cm hL]


private theorem Step2CloseGen_STavgMg_eq (n : ℕ) (u : ℝ)
    (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (σ : Bool) (x : Zd d (sz.L n)) :
    STavgMg Cm n u H σ x = STavgErrMg Cm n u H σ x := by
  unfold STavgMg STavgErrMg
  rw [STLMg_eq_STLIMg Cm hL]
  have : KLloopOf d (sz.L n) (fun _ : Fin 1 => σ) (fun _ => x) = ⟨[σ], [x]⟩ := by
    simp [KLloopOf, List.ofFn_succ]
  rw [this]

/-- `ℰ^{G̃,(2)}` is the general-`n` term at the loop length `2` (band `STEGtM_eq_STegtM`, `Step2Iterate.lean:1674`). -/
theorem STEGtMg_eq_STegtMg (n : ℕ) (u : ℝ) (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) :
    STEGtMg Cm n u H σ a = STegtMg Cm n u H (KLloopOf d (sz.L n) σ a) := by
  unfold STEGtMg STegtMg
  rw [KLloopOf_length2]
  have h1 : Finset.Icc 1 2 = {1, 2} := by decide
  rw [h1, Finset.sum_pair (by norm_num : (1 : ℕ) ≠ 2)]
  simp only [Finset.sum_add_distrib, KLloopOf_cutGlue1, KLloopOf_cutGlue2, Step2CloseGen_STavgMg_eq Cm hL,
    STLMg_eq_STLIMg Cm hL]
  congr 1

/-- `(ℰ⊗ℰ)^{M,(2)}` is the general-`n` quadratic-variation loop at the loop length `2`, `a' = a` (band `STEEM_eq_STeeM`, `Step2Iterate.lean:1698`). -/
theorem STEEMg_eq_STeeMg (n : ℕ) (u : ℝ) (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) :
    STEEMg Cm n u H σ a = STeeMg Cm n u H σ a a := by
  unfold STEEMg STEEkMg STeeMg
  have h1 : Finset.Icc 1 2 = {1, 2} := by decide
  rw [h1, Finset.sum_pair (by norm_num : (1 : ℕ) ≠ 2), mul_add]
  simp only [STeeLoop_one, STeeLoop_two, STLMg_eq_STLIMg Cm hL]
  rfl

/-- The observable of the grid walk at the loop length `2` (band `STgA_eq_STgAN`, `Step2Iterate.lean:1602`). -/
theorem STgAg_eq_STgANg (s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) (k : ℕ)
    (ω : PathΩ sz) : STgAg Cm s t K n σ a k ω = STgANg Cm s t K n σ a k ω :=
  STLKMg_eq_STLKIMg Cm hL n _ _ σ a

/-- The drift of §2.3 is the general-`n` drift at the loop length `2` (`Σ_{l=3}^{2}` is empty; band `STgDrift_eq_STgDriftN`, `Step2Iterate.lean:1709`). -/
theorem STgDriftg_eq_STgDriftNg (s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) (σ : Fin 2 → Bool)
    (a : Fin 2 → Zd d (sz.L n)) (k : ℕ) (ω : PathΩ sz) :
    STgDriftg Cm s t K n σ a k ω = STgDriftNg Cm s t K n σ a k ω := by
  unfold STgDriftg STgDriftNg
  rw [STthetaOpg_eq_ThetaN Cm, STELKLKMg_eq_STelklkMg Cm hL, STEGtMg_eq_STegtMg Cm hL]
  have h3 : Finset.Icc 3 2 = (∅ : Finset ℕ) := by decide
  rw [h3, Finset.sum_empty, add_zero]
  have hf : (STLKMg Cm n (gridTime s t K n k) (Cm.Hpath s t K n k ω) σ) =
      fun a' => STLKIMg Cm n (gridTime s t K n k) (Cm.Hpath s t K n k ω) (KLloopOf d (sz.L n) σ a') :=
    funext fun a' => STLKMg_eq_STLKIMg Cm hL n _ _ σ a'
  rw [hf]

end Ident

/-! ## 2. Target 9 (GMN-C1): the local bound from `STGijDecgL` (`LocalAvg2:367-500`) -/

/-- One-dimensional shell sum: `Σ_{z ∈ Z_L} e^{-δ |z|} ≤ 2/(1 - e^{-δ})` (`|z| = min(val z, L - val z)`). -/
private theorem Step2CloseGen_sum1d {L : ℕ} [NeZero L] {δ : ℝ} (hδ : 0 < δ) :
    ∑ z : ZMod L, Real.exp (-δ * (zdist L z : ℝ)) ≤ 2 / (1 - Real.exp (-δ)) := by
  set q : ℝ := Real.exp (-δ) with hq
  have hq0 : 0 < q := Real.exp_pos _
  have hq1 : q < 1 := by rw [hq]; exact Real.exp_lt_one_iff.2 (by linarith)
  have h1q : 0 < 1 - q := by linarith
  -- pointwise: `e^{-δ zdist z} ≤ q^{val} + q^{L - val}`
  have hpt : ∀ z : ZMod L, Real.exp (-δ * (zdist L z : ℝ)) ≤ q ^ z.val + q ^ (L - z.val) := by
    intro z
    have hv : z.val < L := ZMod.val_lt z
    unfold zdist
    have hcast : Real.exp (-δ * ((min z.val (L - z.val) : ℕ) : ℝ)) = q ^ (min z.val (L - z.val)) := by
      rw [hq, ← Real.exp_nat_mul]; congr 1; ring
    rw [hcast]
    rcases le_total z.val (L - z.val) with h | h
    · rw [min_eq_left h]; have : 0 ≤ q ^ (L - z.val) := by positivity
      linarith
    · rw [min_eq_right h]; have : 0 ≤ q ^ z.val := by positivity
      linarith
  have hsum_val : ∀ f : ℕ → ℝ, ∑ z : ZMod L, f z.val = ∑ v ∈ Finset.range L, f v := by
    intro f
    refine Finset.sum_bij (fun z _ => z.val) (fun z _ => Finset.mem_range.2 (ZMod.val_lt z))
      (fun a _ b _ h => ZMod.val_injective L h) (fun v hv => ?_) (fun z _ => rfl)
    refine ⟨((v : ℕ) : ZMod L), Finset.mem_univ _, ?_⟩
    exact ZMod.val_natCast_of_lt (Finset.mem_range.1 hv)
  calc ∑ z : ZMod L, Real.exp (-δ * (zdist L z : ℝ)) ≤ ∑ z : ZMod L, (q ^ z.val + q ^ (L - z.val)) :=
        Finset.sum_le_sum fun z _ => hpt z
    _ = ∑ v ∈ Finset.range L, (q ^ v + q ^ (L - v)) := hsum_val (fun v => q ^ v + q ^ (L - v))
    _ = ∑ v ∈ Finset.range L, q ^ v + ∑ v ∈ Finset.range L, q ^ (L - v) := Finset.sum_add_distrib
    _ ≤ 1 / (1 - q) + q / (1 - q) := by
        have hg : ∑ v ∈ Finset.range L, q ^ v ≤ 1 / (1 - q) := by
          rw [le_div_iff₀ h1q, geom_sum_mul_neg]
          have : 0 ≤ q ^ L := by positivity
          linarith
        have hr : ∑ v ∈ Finset.range L, q ^ (L - v) = q * ∑ v ∈ Finset.range L, q ^ v := by
          rw [← Finset.sum_range_reflect (fun v => q ^ v) L, Finset.mul_sum]
          refine Finset.sum_congr rfl fun v hv => ?_
          have hv' : v < L := Finset.mem_range.1 hv
          have : L - v = (L - 1 - v) + 1 := by omega
          rw [this, pow_succ]; ring
        rw [hr]
        have h2 : q * ∑ v ∈ Finset.range L, q ^ v ≤ q / (1 - q) := by
          rw [div_eq_mul_one_div]; exact mul_le_mul_of_nonneg_left hg hq0.le
        linarith
    _ ≤ 2 / (1 - q) := by
        rw [← add_div]; exact div_le_div_of_nonneg_right (by linarith) h1q.le


/-- The `d`-dimensional lattice sum `Σ_a e^{-γ |a - c|_∞} ≤ (2/(1 - e^{-γ/d}))^d`, by `max ≥ (1/d) Σ` and the product structure. -/
private theorem Step2CloseGen_latsum {d L : ℕ} [NeZero L] (hd : 0 < d) {γ : ℝ} (hγ : 0 < γ) (c : Zd d L) :
    ∑ a : Zd d L, Real.exp (-γ * (zdistInf d L (a - c) : ℝ)) ≤ (2 / (1 - Real.exp (-(γ / d)))) ^ d := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  set δ : ℝ := γ / d with hδdef
  have hδ : 0 < δ := by positivity
  have hγδ : γ = δ * d := by rw [hδdef]; field_simp
  have hpt : ∀ a : Zd d L, Real.exp (-γ * (zdistInf d L (a - c) : ℝ)) ≤
      ∏ i, Real.exp (-δ * (zdist L (a i - c i) : ℝ)) := by
    intro a
    rw [← Real.exp_sum]
    refine Real.exp_le_exp.2 ?_
    have hle : ∀ i, (zdist L (a i - c i) : ℝ) ≤ (zdistInf d L (a - c) : ℝ) := fun i => by
      have : zdist L ((a - c) i) ≤ zdistInf d L (a - c) :=
        Finset.le_sup (f := fun j => zdist L ((a - c) j)) (Finset.mem_univ i)
      exact_mod_cast this
    have hsum : (∑ i, (zdist L (a i - c i) : ℝ)) ≤ d * (zdistInf d L (a - c) : ℝ) := by
      calc ∑ i, (zdist L (a i - c i) : ℝ) ≤ ∑ _i : Fin d, (zdistInf d L (a - c) : ℝ) :=
            Finset.sum_le_sum fun i _ => hle i
        _ = d * (zdistInf d L (a - c) : ℝ) := by simp
    rw [← Finset.mul_sum]
    have := mul_le_mul_of_nonneg_left hsum hδ.le
    rw [hγδ]
    nlinarith
  have h1d : ∀ i : Fin d, ∑ z : ZMod L, Real.exp (-δ * (zdist L (z - c i) : ℝ)) ≤ 2 / (1 - Real.exp (-δ)) := by
    intro i
    have := Equiv.sum_comp (Equiv.subRight (c i)) (fun z : ZMod L => Real.exp (-δ * (zdist L z : ℝ)))
    simp only [Equiv.subRight_apply] at this
    rw [this]
    exact Step2CloseGen_sum1d hδ
  calc ∑ a : Zd d L, Real.exp (-γ * (zdistInf d L (a - c) : ℝ))
      ≤ ∑ a : Zd d L, ∏ i, Real.exp (-δ * (zdist L (a i - c i) : ℝ)) := Finset.sum_le_sum fun a _ => hpt a
    _ = ∏ i : Fin d, ∑ z : ZMod L, Real.exp (-δ * (zdist L (z - c i) : ℝ)) :=
        (Fintype.prod_sum (fun (i : Fin d) (z : ZMod L) => Real.exp (-δ * (zdist L (z - c i) : ℝ)))).symm
    _ ≤ ∏ _i : Fin d, 2 / (1 - Real.exp (-δ)) :=
        Finset.prod_le_prod₀ (fun i _ => Finset.sum_nonneg fun z _ => (Real.exp_pos _).le) fun i _ => h1d i
    _ = (2 / (1 - Real.exp (-δ))) ^ d := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]


/-- The shift lemma `W^{-d} B_{u,K'} ≤ (j+1)^{d-2} W^{-d} B_{u,K}` for `K ≤ K' + j` (`localAvg1_STWB_comp` is the case `j = 2`). -/
private theorem Step2CloseGen_STWB_shift {d : ℕ} (sz : Sizes d) (n : ℕ) (u : ℝ) {K K' j : ℕ} (h : K ≤ K' + j) :
    STWB sz n u K' ≤ ((j : ℝ) + 1) ^ (d - 2) * STWB sz n u K := by
  unfold STWB Bparam
  have hA : 0 ≤ (sz.lam n ^ 2 + |1 - u|)⁻¹ := by positivity
  have hC : 0 ≤ (((sz.L n : ℕ) : ℝ) ^ d * |1 - u|)⁻¹ := by positivity
  have hW : 0 ≤ (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ := by positivity
  have hx : (0 : ℝ) < (K' : ℝ) + 1 := by positivity
  have hy : (0 : ℝ) < (K : ℝ) + 1 := by positivity
  have hj0 : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
  have hyx : (K : ℝ) + 1 ≤ ((j : ℝ) + 1) * ((K' : ℝ) + 1) := by
    have : (K : ℝ) ≤ (K' : ℝ) + j := by exact_mod_cast h
    nlinarith [mul_nonneg hj0 (Nat.cast_nonneg K' : (0 : ℝ) ≤ K')]
  have hpow : ((K : ℝ) + 1) ^ (d - 2) ≤ ((j : ℝ) + 1) ^ (d - 2) * ((K' : ℝ) + 1) ^ (d - 2) := by
    rw [← mul_pow]; exact pow_le_pow_left₀ hy.le hyx _
  have hT0 : (0 : ℝ) < ((j : ℝ) + 1) ^ (d - 2) := by positivity
  have hf : (((K' : ℝ) + 1) ^ (d - 2))⁻¹ ≤ ((j : ℝ) + 1) ^ (d - 2) * (((K : ℝ) + 1) ^ (d - 2))⁻¹ := by
    calc (((K' : ℝ) + 1) ^ (d - 2))⁻¹
        = ((j : ℝ) + 1) ^ (d - 2) * (((j : ℝ) + 1) ^ (d - 2) * ((K' : ℝ) + 1) ^ (d - 2))⁻¹ := by
          field_simp
      _ ≤ ((j : ℝ) + 1) ^ (d - 2) * (((K : ℝ) + 1) ^ (d - 2))⁻¹ :=
          mul_le_mul_of_nonneg_left (inv_anti₀ (by positivity) hpow) hT0.le
  have h31 : (1 : ℝ) ≤ ((j : ℝ) + 1) ^ (d - 2) := one_le_pow₀ (by linarith)
  set f' := (((K' : ℝ) + 1) ^ (d - 2))⁻¹
  set f := (((K : ℝ) + 1) ^ (d - 2))⁻¹
  set A := (sz.lam n ^ 2 + |1 - u|)⁻¹
  set Cc := (((sz.L n : ℕ) : ℝ) ^ d * |1 - u|)⁻¹
  set w := (((sz.W n : ℕ) : ℝ) ^ d)⁻¹
  set T := ((j : ℝ) + 1) ^ (d - 2)
  have : T * (w * (A * f + Cc)) = w * (T * (A * f) + T * Cc) := by ring
  rw [this]
  refine mul_le_mul_of_nonneg_left ?_ hW
  nlinarith [mul_le_mul_of_nonneg_left hf hA, mul_le_mul_of_nonneg_right h31 hC]

/-- A polynomial factor is absorbed by half of the exponential: `(x+1)^e e^{-2γx} ≤ (e! e^γ/γ^e) e^{-γx}`. -/
private theorem Step2CloseGen_poly_exp {γ : ℝ} (hγ : 0 < γ) (e : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    (x + 1) ^ e * Real.exp (-(2 * γ) * x) ≤ ((Nat.factorial e : ℝ) * Real.exp γ / γ ^ e) * Real.exp (-γ * x) := by
  have h1 := Real.pow_div_factorial_le_exp (x := γ * (x + 1)) (by positivity) e
  have hf : (0 : ℝ) < (Nat.factorial e : ℝ) := by exact_mod_cast Nat.factorial_pos e
  have hge : (0 : ℝ) < γ ^ e := by positivity
  rw [div_le_iff₀ hf, mul_pow] at h1
  have h2 : γ ^ e * (x + 1) ^ e * Real.exp (-(2 * γ) * x) ≤
      Real.exp (γ * (x + 1)) * (Nat.factorial e : ℝ) * Real.exp (-(2 * γ) * x) :=
    mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
  have h3 : Real.exp (γ * (x + 1)) * Real.exp (-(2 * γ) * x) = Real.exp γ * Real.exp (-γ * x) := by
    rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  rw [div_mul_eq_mul_div, le_div_iff₀ hge]
  calc (x + 1) ^ e * Real.exp (-(2 * γ) * x) * γ ^ e
      = γ ^ e * (x + 1) ^ e * Real.exp (-(2 * γ) * x) := by ring
    _ ≤ Real.exp (γ * (x + 1)) * (Nat.factorial e : ℝ) * Real.exp (-(2 * γ) * x) := h2
    _ = (Nat.factorial e : ℝ) * Real.exp γ * Real.exp (-γ * x) := by
        rw [mul_right_comm, h3]; ring


/-- The floor `W^{-(d + (d-2)/𝔠 + 1)} ≤ cB W^{-d} ((r+1)^{d-2})⁻¹` for `r ≤ L`, eventually (`L ≤ N ≤ W^{1/𝔠}`). -/
private theorem Step2CloseGen_floor {d : ℕ} (sz : Sizes d) (hd : 0 < d) {𝔠 : ℝ} (h𝔠 : 0 < 𝔠) (hband : sz.Bandwidth 𝔠)
    (hWt : Tendsto (fun n => ((sz.W n : ℕ) : ℝ)) atTop atTop) {cB : ℝ} (hcB : 0 < cB) :
    ∀ᶠ n in atTop, ∀ r : ℕ, (r : ℝ) ≤ ((sz.L n : ℕ) : ℝ) →
      ((sz.W n : ℕ) : ℝ) ^ (-((d : ℝ) + ((d - 2 : ℕ) : ℝ) / 𝔠 + 1)) ≤
        cB * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * ((((r : ℕ) : ℝ) + 1) ^ (d - 2))⁻¹ := by
  filter_upwards [hband, hWt.eventually (eventually_ge_atTop (2 ^ (d - 2) / cB)),
    hWt.eventually (eventually_ge_atTop 1)] with n hn hWb hW1 r hr
  set W : ℝ := ((sz.W n : ℕ) : ℝ) with hWdef
  set N : ℝ := ((sz.size n : ℕ) : ℝ) with hNdef
  set e : ℕ := d - 2 with hedef
  have hW0 : 0 < W := by linarith
  have hN1 : (1 : ℝ) ≤ N := Nat.one_le_cast.2 (sz.one_le_size n)
  have hN0 : 0 < N := by linarith
  have hL3 : (3 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) := by exact_mod_cast sz.three_le_L n
  have hLN : ((sz.L n : ℕ) : ℝ) ≤ N := by
    have h1 : sz.L n ≤ sz.size n := by
      unfold Sizes.size
      calc sz.L n ≤ sz.W n * sz.L n := Nat.le_mul_of_pos_left _ (sz.W_pos n)
        _ ≤ (sz.W n * sz.L n) ^ d := Nat.le_self_pow (by omega) _
    rw [hNdef]; exact_mod_cast h1
  have hr1 : (r : ℝ) + 1 ≤ 2 * N := by linarith
  have hpow1 : ((r : ℝ) + 1) ^ e ≤ 2 ^ e * N ^ e := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) hr1 e
  -- `N ≤ W^{1/𝔠}`
  have hNW : N ≤ W ^ (1 / 𝔠) := by
    calc N = (N ^ 𝔠) ^ (1 / 𝔠) := by
          rw [← Real.rpow_mul hN0.le, mul_one_div_cancel h𝔠.ne', Real.rpow_one]
      _ ≤ W ^ (1 / 𝔠) := Real.rpow_le_rpow (Real.rpow_nonneg hN0.le _) hn (by positivity)
  have hNe : N ^ e ≤ W ^ ((e : ℝ) / 𝔠) := by
    calc N ^ e ≤ (W ^ (1 / 𝔠)) ^ e := pow_le_pow_left₀ hN0.le hNW e
      _ = W ^ ((e : ℝ) / 𝔠) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hW0.le]; congr 1; ring
  have hpow2 : ((r : ℝ) + 1) ^ e ≤ 2 ^ e * W ^ ((e : ℝ) / 𝔠) :=
    hpow1.trans (mul_le_mul_of_nonneg_left hNe (by positivity))
  have hWe : 0 < W ^ ((e : ℝ) / 𝔠) := Real.rpow_pos_of_pos hW0 _
  have hinv : (2 ^ e * W ^ ((e : ℝ) / 𝔠))⁻¹ ≤ (((r : ℝ) + 1) ^ e)⁻¹ :=
    inv_anti₀ (by positivity) hpow2
  have hsplit : W ^ (-((d : ℝ) + (e : ℝ) / 𝔠 + 1)) = (W ^ d)⁻¹ * (W ^ ((e : ℝ) / 𝔠))⁻¹ * W⁻¹ := by
    rw [Real.rpow_neg hW0.le, Real.rpow_add (by positivity), Real.rpow_add hW0, Real.rpow_natCast, Real.rpow_one,
      mul_inv, mul_inv]
  have hWinv : W⁻¹ ≤ cB * (2 ^ e)⁻¹ := by
    have h2e : (0 : ℝ) < 2 ^ e := by positivity
    rw [inv_eq_one_div, div_le_iff₀ hW0]
    have : 2 ^ e / cB ≤ W := hWb
    rw [div_le_iff₀ hcB] at this
    have h3 : (1 : ℝ) ≤ (W * cB) / 2 ^ e := by rw [le_div_iff₀ h2e]; linarith
    calc (1 : ℝ) ≤ (W * cB) / 2 ^ e := h3
      _ = cB * (2 ^ e)⁻¹ * W := by field_simp
  rw [hsplit]
  have hWd0 : 0 < (W ^ d)⁻¹ := by positivity
  calc (W ^ d)⁻¹ * (W ^ ((e : ℝ) / 𝔠))⁻¹ * W⁻¹
      ≤ (W ^ d)⁻¹ * (W ^ ((e : ℝ) / 𝔠))⁻¹ * (cB * (2 ^ e)⁻¹) :=
        mul_le_mul_of_nonneg_left hWinv (by positivity)
    _ = cB * (W ^ d)⁻¹ * (2 ^ e * W ^ ((e : ℝ) / 𝔠))⁻¹ := by rw [mul_inv]; ring
    _ ≤ cB * (W ^ d)⁻¹ * (((r : ℝ) + 1) ^ e)⁻¹ :=
        mul_le_mul_of_nonneg_left hinv (by positivity)


/-- constants of the reader of target 9 -/
private def Step2CloseGen_K1 (d : ℕ) (c' : ℝ) : ℝ :=
  (Nat.factorial (d - 2) : ℝ) * Real.exp (c' / 2) / (c' / 2) ^ (d - 2)

private def Step2CloseGen_K2 (d : ℕ) (c' : ℝ) : ℝ :=
  (Nat.factorial (d - 2) : ℝ) * Real.exp c' / c' ^ (d - 2)

private def Step2CloseGen_S (d : ℕ) (c' : ℝ) : ℝ :=
  (2 / (1 - Real.exp (-((c' / 2) / d)))) ^ d

private def Step2CloseGen_C2 (d : ℕ) (cB c' : ℝ) : ℝ :=
  Step2CloseGen_K1 d c' * Step2CloseGen_S d c' ^ 2 + Real.sqrt (cB⁻¹ * Step2CloseGen_K2 d c') + 1

/-- `T1`: the double sum of the profile term of `STGijDecgL` -/
private theorem Step2CloseGen_T1 {d : ℕ} (hd : 0 < d) (sz : Sizes d) (n : ℕ) (u : ℝ) {c' X : ℝ} (hc' : 0 < c')
    (hX : 1 ≤ X) (a b : Zd d (sz.L n)) :
    (∑ a' : Zd d (sz.L n), ∑ b' : Zd d (sz.L n),
        (X * Real.sqrt (STWB sz n u (zdistInf d (sz.L n) (a' - b')))) *
          Real.exp (-c' * ((zdistInf d (sz.L n) (a' - a) : ℝ) + (zdistInf d (sz.L n) (b' - b) : ℝ)))) ≤
      (X * Step2CloseGen_K1 d c' * Real.sqrt (STWB sz n u (zdistInf d (sz.L n) (a - b)))) *
        (Step2CloseGen_S d c' * Step2CloseGen_S d c') := by
  classical
  have hγ : 0 < c' / 2 := by positivity
  have hK₁0 : 0 ≤ Step2CloseGen_K1 d c' := by unfold Step2CloseGen_K1; positivity
  have hsq0 : 0 ≤ Real.sqrt (STWB sz n u (zdistInf d (sz.L n) (a - b))) := Real.sqrt_nonneg _
  have hlatA : ∑ a' : Zd d (sz.L n), Real.exp (-(c' / 2) * (zdistInf d (sz.L n) (a' - a) : ℝ)) ≤
      Step2CloseGen_S d c' := Step2CloseGen_latsum hd hγ a
  have hlatB : ∑ b' : Zd d (sz.L n), Real.exp (-(c' / 2) * (zdistInf d (sz.L n) (b' - b) : ℝ)) ≤
      Step2CloseGen_S d c' := Step2CloseGen_latsum hd hγ b
  have hS0 : 0 ≤ Step2CloseGen_S d c' := le_trans (Finset.sum_nonneg fun _ _ => (Real.exp_pos _).le) hlatA
  have hterm : ∀ a' b' : Zd d (sz.L n),
      (X * Real.sqrt (STWB sz n u (zdistInf d (sz.L n) (a' - b')))) *
          Real.exp (-c' * ((zdistInf d (sz.L n) (a' - a) : ℝ) + (zdistInf d (sz.L n) (b' - b) : ℝ))) ≤
        (X * Step2CloseGen_K1 d c' * Real.sqrt (STWB sz n u (zdistInf d (sz.L n) (a - b)))) *
          (Real.exp (-(c' / 2) * (zdistInf d (sz.L n) (a' - a) : ℝ)) *
            Real.exp (-(c' / 2) * (zdistInf d (sz.L n) (b' - b) : ℝ))) := by
    intro a' b'
    have hr : zdistInf d (sz.L n) (a - b) ≤ zdistInf d (sz.L n) (a' - b') +
        (zdistInf d (sz.L n) (a' - a) + zdistInf d (sz.L n) (b' - b)) := by
      have e1 : a - b = (a' - b') + (-(a' - a)) + (b' - b) := by abel
      have h1 := la2_zdistInf_add_le (a' - b' + -(a' - a)) (b' - b)
      have h2 := la2_zdistInf_add_le (a' - b') (-(a' - a))
      rw [la2_zdistInf_neg] at h2
      rw [e1]
      omega
    have hsh := Step2CloseGen_STWB_shift sz n u hr
    generalize zdistInf d (sz.L n) (a' - a) = m₁ at *
    generalize zdistInf d (sz.L n) (b' - b) = m₂ at *
    generalize zdistInf d (sz.L n) (a' - b') = k at *
    generalize zdistInf d (sz.L n) (a - b) = r at *
    have hj1 : (1 : ℝ) ≤ (((m₁ + m₂ : ℕ) : ℝ) + 1) ^ (d - 2) :=
      one_le_pow₀ (by have := Nat.cast_nonneg (α := ℝ) (m₁ + m₂); linarith)
    have hsk : Real.sqrt (STWB sz n u k) ≤ (((m₁ + m₂ : ℕ) : ℝ) + 1) ^ (d - 2) * Real.sqrt (STWB sz n u r) := by
      calc Real.sqrt (STWB sz n u k)
          ≤ Real.sqrt ((((m₁ + m₂ : ℕ) : ℝ) + 1) ^ (d - 2) * STWB sz n u r) := Real.sqrt_le_sqrt hsh
        _ = Real.sqrt ((((m₁ + m₂ : ℕ) : ℝ) + 1) ^ (d - 2)) * Real.sqrt (STWB sz n u r) :=
            Real.sqrt_mul (by positivity) _
        _ ≤ (((m₁ + m₂ : ℕ) : ℝ) + 1) ^ (d - 2) * Real.sqrt (STWB sz n u r) := by
            refine mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _)
            rw [Real.sqrt_le_iff]
            exact ⟨by positivity, by nlinarith⟩
    have hpoly := Step2CloseGen_poly_exp hγ (d - 2) (x := ((m₁ + m₂ : ℕ) : ℝ)) (Nat.cast_nonneg _)
    have hexp : Real.exp (-c' * ((m₁ : ℝ) + (m₂ : ℝ))) =
        Real.exp (-(2 * (c' / 2)) * ((m₁ + m₂ : ℕ) : ℝ)) := by
      congr 1; push_cast; ring
    have hexp2 : Real.exp (-(c' / 2) * ((m₁ + m₂ : ℕ) : ℝ)) =
        Real.exp (-(c' / 2) * (m₁ : ℝ)) * Real.exp (-(c' / 2) * (m₂ : ℝ)) := by
      rw [← Real.exp_add]; congr 1; push_cast; ring
    rw [hexp, ← hexp2]
    calc (X * Real.sqrt (STWB sz n u k)) * Real.exp (-(2 * (c' / 2)) * ((m₁ + m₂ : ℕ) : ℝ))
        ≤ (X * ((((m₁ + m₂ : ℕ) : ℝ) + 1) ^ (d - 2) * Real.sqrt (STWB sz n u r))) *
            Real.exp (-(2 * (c' / 2)) * ((m₁ + m₂ : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsk (by linarith)) (Real.exp_pos _).le
      _ = (X * Real.sqrt (STWB sz n u r)) * ((((m₁ + m₂ : ℕ) : ℝ) + 1) ^ (d - 2) *
            Real.exp (-(2 * (c' / 2)) * ((m₁ + m₂ : ℕ) : ℝ))) := by ring
      _ ≤ (X * Real.sqrt (STWB sz n u r)) * (Step2CloseGen_K1 d c' * Real.exp (-(c' / 2) * ((m₁ + m₂ : ℕ) : ℝ))) :=
          mul_le_mul_of_nonneg_left hpoly (mul_nonneg (by linarith) (Real.sqrt_nonneg _))
      _ = (X * Step2CloseGen_K1 d c' * Real.sqrt (STWB sz n u r)) * Real.exp (-(c' / 2) * ((m₁ + m₂ : ℕ) : ℝ)) := by
          ring
  calc _ ≤ ∑ a' : Zd d (sz.L n), ∑ b' : Zd d (sz.L n),
        (X * Step2CloseGen_K1 d c' * Real.sqrt (STWB sz n u (zdistInf d (sz.L n) (a - b)))) *
          (Real.exp (-(c' / 2) * (zdistInf d (sz.L n) (a' - a) : ℝ)) *
            Real.exp (-(c' / 2) * (zdistInf d (sz.L n) (b' - b) : ℝ))) :=
        Finset.sum_le_sum fun a' _ => Finset.sum_le_sum fun b' _ => hterm a' b'
    _ = (X * Step2CloseGen_K1 d c' * Real.sqrt (STWB sz n u (zdistInf d (sz.L n) (a - b)))) *
        ((∑ a' : Zd d (sz.L n), Real.exp (-(c' / 2) * (zdistInf d (sz.L n) (a' - a) : ℝ))) *
          (∑ b' : Zd d (sz.L n), Real.exp (-(c' / 2) * (zdistInf d (sz.L n) (b' - b) : ℝ)))) := by
        rw [Finset.sum_mul_sum, Finset.mul_sum]
        exact Finset.sum_congr rfl fun a' _ => by rw [Finset.mul_sum]
    _ ≤ _ := by
        refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (mul_nonneg (by linarith) hK₁0) hsq0)
        exact mul_le_mul hlatA hlatB (Finset.sum_nonneg fun _ _ => (Real.exp_pos _).le) hS0


/-- `T2`: the `Ψ` term -/
private theorem Step2CloseGen_T2 {d : ℕ} (sz : Sizes d) (n : ℕ) (u : ℝ) {cB c' : ℝ} (hcB : 0 < cB) (hc' : 0 < c')
    (hlow : cB * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ sz.Bctl n u) (r : ℕ) :
    ((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2) * Real.exp (-c' * (r : ℝ)) ≤
      Real.sqrt (cB⁻¹ * Step2CloseGen_K2 d c') * Real.sqrt (STWB sz n u r) := by
  have hW0 : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hWd : (0 : ℝ) < (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ := by positivity
  have hK₂0 : 0 ≤ Step2CloseGen_K2 d c' := by unfold Step2CloseGen_K2; positivity
  have hSnn : 0 ≤ STWB sz n u r := by unfold STWB Bparam; positivity
  have hBle : sz.Bctl n u ≤ (((r : ℝ) + 1) ^ (d - 2)) * STWB sz n u r := by
    have h := localAvg1_STWB_ge sz n u r
    have hp : (0 : ℝ) < ((r : ℝ) + 1) ^ (d - 2) := by positivity
    rw [inv_mul_le_iff₀ hp] at h
    exact h
  have hsqW : (((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2)) ^ 2 = (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ := by
    rw [ST_rpow_neg_half hW0.le, localAvg1_rpow_half_sq hWd.le]
  have hWB : (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ cB⁻¹ * sz.Bctl n u := by
    rw [le_inv_mul_iff₀ hcB]; linarith
  have hpoly := Step2CloseGen_poly_exp hc' (d - 2) (x := (r : ℝ)) (Nat.cast_nonneg _)
  have hex : Real.exp (-c' * (r : ℝ)) ≤ 1 :=
    Real.exp_le_one_iff.2 (by nlinarith [(Nat.cast_nonneg r : (0 : ℝ) ≤ r)])
  have hpoly' : ((r : ℝ) + 1) ^ (d - 2) * Real.exp (-(2 * c') * (r : ℝ)) ≤ Step2CloseGen_K2 d c' := by
    refine hpoly.trans ?_
    have := mul_le_mul_of_nonneg_left hex hK₂0
    unfold Step2CloseGen_K2 at this ⊢
    linarith
  have he2 : Real.exp (-c' * (r : ℝ)) ^ 2 = Real.exp (-(2 * c') * (r : ℝ)) := by
    rw [sq, ← Real.exp_add]; congr 1; ring
  have hsq : (((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2) * Real.exp (-c' * (r : ℝ))) ^ 2 ≤
      (cB⁻¹ * Step2CloseGen_K2 d c') * STWB sz n u r := by
    rw [mul_pow, hsqW, he2]
    calc (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * Real.exp (-(2 * c') * (r : ℝ))
        ≤ (cB⁻¹ * sz.Bctl n u) * Real.exp (-(2 * c') * (r : ℝ)) :=
          mul_le_mul_of_nonneg_right hWB (Real.exp_pos _).le
      _ ≤ (cB⁻¹ * ((((r : ℝ) + 1) ^ (d - 2)) * STWB sz n u r)) * Real.exp (-(2 * c') * (r : ℝ)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hBle (by positivity)) (Real.exp_pos _).le
      _ = (cB⁻¹ * (((r : ℝ) + 1) ^ (d - 2) * Real.exp (-(2 * c') * (r : ℝ)))) * STWB sz n u r := by ring
      _ ≤ (cB⁻¹ * Step2CloseGen_K2 d c') * STWB sz n u r :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpoly' (by positivity)) hSnn
  rw [← Real.sqrt_mul (by positivity)]
  exact Real.le_sqrt_of_sq_le hsq

/-- `T3`: the floor term -/
private theorem Step2CloseGen_T3 {d : ℕ} (sz : Sizes d) (n : ℕ) (u : ℝ) {cB D : ℝ}
    (hlow : cB * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ sz.Bctl n u) (x y : Zd d (sz.L n))
    (hfloor : ∀ r : ℕ, (r : ℝ) ≤ ((sz.L n : ℕ) : ℝ) →
      (((sz.W n : ℕ) : ℝ) ^ (-D)) ^ 2 ≤ cB * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * ((((r : ℕ) : ℝ) + 1) ^ (d - 2))⁻¹) :
    ((sz.W n : ℕ) : ℝ) ^ (-D) ≤ Real.sqrt (STWB sz n u (zdistInf d (sz.L n) (x - y))) := by
  have hrL : ((zdistInf d (sz.L n) (x - y) : ℕ) : ℝ) ≤ ((sz.L n : ℕ) : ℝ) := ST_zdistInf_le sz n (x - y)
  have h1 := hfloor _ hrL
  have h2 : cB * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * ((((zdistInf d (sz.L n) (x - y) : ℕ) : ℝ) + 1) ^ (d - 2))⁻¹ ≤
      STWB sz n u (zdistInf d (sz.L n) (x - y)) := by
    have := localAvg1_STWB_ge sz n u (zdistInf d (sz.L n) (x - y))
    calc cB * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * ((((zdistInf d (sz.L n) (x - y) : ℕ) : ℝ) + 1) ^ (d - 2))⁻¹
        = ((((zdistInf d (sz.L n) (x - y) : ℕ) : ℝ) + 1) ^ (d - 2))⁻¹ * (cB * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹) := by
          ring
      _ ≤ ((((zdistInf d (sz.L n) (x - y) : ℕ) : ℝ) + 1) ^ (d - 2))⁻¹ * sz.Bctl n u :=
        mul_le_mul_of_nonneg_left hlow (by positivity)
      _ ≤ _ := this
  exact Real.le_sqrt_of_sq_le (h1.trans h2)

/-- the right side of `STGijDecgL` at `Φ_n(a,b) = X √STWB(|a-b|)`, `Ψ_n = W^{-d/2}` is `≤ C₂ X √STWB(r)` -/
private theorem Step2CloseGen_R_le {d : ℕ} (hd : 0 < d) (sz : Sizes d) (n : ℕ) (u : ℝ)
    {cB c' X D : ℝ} (hcB : 0 < cB) (hc' : 0 < c') (hX : 1 ≤ X)
    (hlow : cB * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ sz.Bctl n u)
    (hfloor : ∀ r : ℕ, (r : ℝ) ≤ ((sz.L n : ℕ) : ℝ) →
      (((sz.W n : ℕ) : ℝ) ^ (-D)) ^ 2 ≤ cB * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * ((((r : ℕ) : ℝ) + 1) ^ (d - 2))⁻¹)
    (x y : Idx d (sz.L n) (sz.W n)) :
    (∑ a' : Zd d (sz.L n), ∑ b' : Zd d (sz.L n),
        (X * Real.sqrt (STWB sz n u (zdistInf d (sz.L n) (a' - b')))) *
          Real.exp (-c' * ((zdistInf d (sz.L n) (a' - STblk sz n x) : ℝ) +
            (zdistInf d (sz.L n) (b' - STblk sz n y) : ℝ)))) +
      ((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2) *
        Real.exp (-c' * (zdistInf d (sz.L n) (STblk sz n x - STblk sz n y) : ℝ)) +
      ((sz.W n : ℕ) : ℝ) ^ (-D) ≤
    Step2CloseGen_C2 d cB c' * X * Real.sqrt (STWB sz n u (zdistInf d (sz.L n) (STblk sz n x - STblk sz n y))) := by
  have h1 := Step2CloseGen_T1 hd sz n u hc' hX (STblk sz n x) (STblk sz n y)
  have h2 := Step2CloseGen_T2 sz n u hcB hc' hlow (zdistInf d (sz.L n) (STblk sz n x - STblk sz n y))
  have h3 := Step2CloseGen_T3 sz n u hlow (STblk sz n x) (STblk sz n y) hfloor
  have hK₁0 : 0 ≤ Step2CloseGen_K1 d c' := by unfold Step2CloseGen_K1; positivity
  have hsq0 := Real.sqrt_nonneg (STWB sz n u (zdistInf d (sz.L n) (STblk sz n x - STblk sz n y)))
  have hsq2 : 0 ≤ Real.sqrt (cB⁻¹ * Step2CloseGen_K2 d c') := Real.sqrt_nonneg _
  have hXnn : 0 ≤ X := by linarith
  unfold Step2CloseGen_C2
  set sr := Real.sqrt (STWB sz n u (zdistInf d (sz.L n) (STblk sz n x - STblk sz n y)))
  set K₁ := Step2CloseGen_K1 d c'
  set S := Step2CloseGen_S d c'
  set Q := Real.sqrt (cB⁻¹ * Step2CloseGen_K2 d c')
  have hSS : S * S = S ^ 2 := by ring
  rw [hSS] at h1
  have e1 : Q * sr ≤ Q * sr * X := by nlinarith [mul_nonneg hsq2 hsq0]
  have e2 : sr ≤ sr * X := by nlinarith
  calc _ ≤ (X * K₁ * sr) * S ^ 2 + Q * sr + sr := by linarith
    _ ≤ (K₁ * S ^ 2 + Q + 1) * X * sr := by nlinarith


/-- the arithmetic of the off-diagonal case -/
private theorem Step2CloseGen_arith {G C2 P S : ℝ} (hP : 1 ≤ P) (hS : 0 ≤ S) (hC2 : 0 ≤ C2) (hC2P : C2 ^ 2 ≤ P ^ 2)
    (hG0 : 0 ≤ G) (hG : G ≤ P ^ 2 * (C2 * P * Real.sqrt S)) : G ^ 2 ≤ P ^ 8 * S := by
  have hP0 : 0 ≤ P := by linarith
  have hsq : Real.sqrt S ^ 2 = S := Real.sq_sqrt hS
  have h1 : G ^ 2 ≤ (P ^ 2 * (C2 * P * Real.sqrt S)) ^ 2 := pow_le_pow_left₀ hG0 hG 2
  have h2 : (P ^ 2 * (C2 * P * Real.sqrt S)) ^ 2 = P ^ 6 * C2 ^ 2 * S := by
    have : (P ^ 2 * (C2 * P * Real.sqrt S)) ^ 2 = P ^ 6 * C2 ^ 2 * Real.sqrt S ^ 2 := by ring
    rw [this, hsq]
  have h3 : P ^ 6 * C2 ^ 2 * S ≤ P ^ 6 * P ^ 2 * S := by
    have : 0 ≤ P ^ 6 := by positivity
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hC2P this) hS
  calc G ^ 2 ≤ P ^ 6 * C2 ^ 2 * S := h1.trans (le_of_eq h2)
    _ ≤ P ^ 6 * P ^ 2 * S := h3
    _ = P ^ 8 * S := by ring


private theorem Step2CloseGen_cases (σ : Fin 2 → Bool) (h : σ 0 ≠ σ 1) : σ = ![true, false] ∨ σ = ![false, true] := by
  cases h0 : σ 0 <;> cases h1 : σ 1
  · exact absurd (h0.trans h1.symm) h
  · right; funext i; fin_cases i <;> simp [h0, h1]
  · left; funext i; fin_cases i <;> simp [h0, h1]
  · exact absurd (h0.trans h1.symm) h

/-- **Target 9 (GMN-C1), `stStep2LocalPT_of_L2decayDecG`** -/
theorem stStep2LocalPT_of_L2decayDecG {d : ℕ} {sz : Sizes d} (Cm : Step2Data sz) (μ : Measure sz.SeqΩ) (hd : 0 < d)
    {κ ε 𝔠 𝔡 : ℝ} (hflow : Cm.flowOK κ ε 𝔠 𝔡) {s t : ℕ → ℝ} (hs : ∀ n, 0 ≤ s n) (hst : ∀ n, s n ≤ t n)
    (htl : ∀ n, t n ≤ Cm.T0 n)
    (hdat : ∃ cB c : ℝ, 0 < cB ∧ 0 < c ∧ ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ Cm.T0 n) →
      ∀ᶠ n in atTop, ∀ u : ℝ, 0 ≤ u → u ≤ t n →
        cB * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ sz.Bctl n u ∧ sz.Bctl n u ≤ ((sz.size n : ℕ) : ℝ) ^ (-c))
    (hGii : ∀ u : ℕ → ℝ, (∀ n, 0 ≤ u n) → (∀ n, u n ≤ Cm.T0 n) → ∀ ε₀ : ℝ, 0 < ε₀ →
      STGiiGEXgL Cm.toFlowFM μ u ε₀)
    (hGij : ∀ u : ℕ → ℝ, (∀ n, 0 ≤ u n) → (∀ n, u n ≤ Cm.T0 n) → STGijDecgL Cm.toFlowFM μ u)
    (hweak : STStep1WeakgL Cm.toFlowFM μ s t) (hL2 : STL2decayPTgL Cm.toFlowFM μ s t) :
    STStep2LocalPTgL Cm.toFlowFM μ s t := by
  classical
  obtain ⟨cB, c, hcB, hc, hdat'⟩ := hdat
  have hev := hdat' t (fun n => (hs n).trans (hst n)) htl
  have hadm := Cm.flowOK_adm hflow
  have hsize : Tendsto sz.size atTop atTop := tendsto_size sz hadm.2.2.1
  have h𝔠 : 0 < 𝔠 := hadm.1
  have hband : sz.Bandwidth 𝔠 := hadm.2.2.2.1
  have hWt := ST_W_tendsto sz hadm.2.2.1 h𝔠 hband
  have hdR : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hε₀pos : 0 < min (1 / 2 : ℝ) (d * c / 8) := lt_min (by norm_num) (by positivity)
  set ε₀ := min (1 / 2 : ℝ) (d * c / 8) with hε₀
  have hε₀1 : ε₀ ≤ 1 / 2 := min_le_left _ _
  refine Green.perTime_timeIcc_of_forall_seq μ sz.size hst
    (V := fun n => Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n)) (fun n => ⟨(0, 0)⟩)
    (fun n v q ω => ‖Cm.GM n v ω q.1 q.2‖ ^ 2)
    (fun n v q _ => STWB sz n v (zdistInf d (sz.L n) (STblk sz n q.1 - STblk sz n q.2))) ?_
  intro u hu
  have hu0 : ∀ n, 0 ≤ u n := fun n => (hs n).trans (hu n).1
  have hul : ∀ n, u n ≤ Cm.T0 n := fun n => (hu n).2.trans (htl n)
  have hΩev : ∀ᶠ n in atTop, ((sz.size n : ℕ) : ℝ) ^ (c / 8) * (sz.Bctl n (u n)) ^ (1 / 4 : ℝ) ≤
      ((sz.W n : ℕ) : ℝ) ^ (-ε₀) := by
    filter_upwards [hev] with n hn
    obtain ⟨h1, h2⟩ := hn (u n) (hu0 n) (hu n).2
    exact (localAvg1_det sz n hd hcB hc (min_le_left _ _) (min_le_right _ _) h1 h2).1
  have hGii' := hGii u hu0 hul ε₀ hε₀pos
  obtain ⟨c', hc', hGijc⟩ := hGij u hu0 hul
  obtain ⟨D₀, hD₀def⟩ : ∃ D₀ : ℝ, D₀ = ((d : ℝ) + ((d - 2 : ℕ) : ℝ) / 𝔠 + 1) / 2 := ⟨_, rfl⟩
  have hD₀ : 0 < D₀ := by rw [hD₀def]; positivity
  have hfloor := Step2CloseGen_floor sz hd h𝔠 hband hWt hcB
  have hPrec : StochDomAt μ sz.size
      (U := fun n => Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n))
      (fun n q ω => ‖Cm.GM n (u n) ω q.1 q.2‖ ^ 2)
      (fun n q _ => STWB sz n (u n) (zdistInf d (sz.L n) (STblk sz n q.1 - STblk sz n q.2))) := by
    refine localAvg1_stochDomAt_of_whp fun τ hτ => ?_
    obtain ⟨τ', hτ'def⟩ : ∃ τ' : ℝ, τ' = min τ c := ⟨_, rfl⟩
    have hτ'pos : 0 < τ' := by rw [hτ'def]; exact lt_min hτ hc
    have hτ'τ : τ' ≤ τ := by rw [hτ'def]; exact min_le_left _ _
    have hτ'c : τ' ≤ c := by rw [hτ'def]; exact min_le_right _ _
    have hτ4 : 0 < τ' / 4 := by positivity
    obtain ⟨Φ, hΦ⟩ : ∃ Φ : ∀ n, Zd d (sz.L n) → Zd d (sz.L n) → ℝ, ∀ n a b, Φ n a b =
        ((sz.size n : ℕ) : ℝ) ^ (τ' / 8) * Real.sqrt (STWB sz n (u n) (zdistInf d (sz.L n) (a - b))) :=
      ⟨fun n a b => ((sz.size n : ℕ) : ℝ) ^ (τ' / 8) * Real.sqrt (STWB sz n (u n) (zdistInf d (sz.L n) (a - b))),
        fun _ _ _ => rfl⟩
    obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : ℕ → ℝ, ∀ n, Ψ n = ((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2) :=
      ⟨fun n => ((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2), fun _ => rfl⟩
    have hΦr : ∀ᶠ n in atTop, ∀ a b : Zd d (sz.L n), 0 < Φ n a b ∧ Φ n a b ≤ ((sz.W n : ℕ) : ℝ) ^ (-ε₀) := by
      filter_upwards [hev, hΩev] with n hn hΩn
      obtain ⟨h1, h2⟩ := hn (u n) (hu0 n) (hu n).2
      have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
      have hWd : (0 : ℝ) < (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ := by
        have : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
        positivity
      have hBpos : 0 < sz.Bctl n (u n) := lt_of_lt_of_le (mul_pos hcB hWd) h1
      have hB1 : sz.Bctl n (u n) ≤ 1 := h2.trans (Real.rpow_le_one_of_one_le_of_nonpos hN1 (by linarith))
      intro a b
      rw [hΦ]
      have hSle := localAvg1_STWB_le sz n (u n) (zdistInf d (sz.L n) (a - b))
      have hSpos : 0 < STWB sz n (u n) (zdistInf d (sz.L n) (a - b)) :=
        lt_of_lt_of_le (by positivity) (localAvg1_STWB_ge sz n (u n) (zdistInf d (sz.L n) (a - b)))
      refine ⟨mul_pos (Real.rpow_pos_of_pos (by linarith) _) (Real.sqrt_pos.2 hSpos), ?_⟩
      calc ((sz.size n : ℕ) : ℝ) ^ (τ' / 8) * Real.sqrt (STWB sz n (u n) (zdistInf d (sz.L n) (a - b)))
          ≤ ((sz.size n : ℕ) : ℝ) ^ (c / 8) * (sz.Bctl n (u n)) ^ (1 / 4 : ℝ) := by
            refine mul_le_mul (Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)) ?_ (Real.sqrt_nonneg _)
              (Real.rpow_nonneg (by linarith) _)
            calc Real.sqrt (STWB sz n (u n) (zdistInf d (sz.L n) (a - b))) ≤ Real.sqrt (sz.Bctl n (u n)) :=
                  Real.sqrt_le_sqrt hSle
              _ = (sz.Bctl n (u n)) ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow _
              _ ≤ (sz.Bctl n (u n)) ^ (1 / 4 : ℝ) :=
                  Real.rpow_le_rpow_of_exponent_ge hBpos hB1 (by norm_num)
        _ ≤ _ := hΩn
    have hΨ1 : ∀ᶠ n in atTop, ((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2) ≤ Ψ n :=
      Eventually.of_forall fun n => (hΨ n).symm.le
    have hΨ2 : ∀ᶠ n in atTop, Ψ n ≤ ((sz.W n : ℕ) : ℝ) ^ (-ε₀) :=
      Eventually.of_forall fun n => by
        rw [hΨ]
        exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast sz.W_pos n) (by linarith)
    have hLoop : PrecL sz μ (U := fun n => {σ : Fin 2 → Bool // σ 0 ≠ σ 1} × Zd d (sz.L n) × Zd d (sz.L n))
        (fun n p ω => STindMaxg Cm.toFlowFM n (u n) (((sz.W n : ℕ) : ℝ) ^ (-ε₀)) ω *
          ‖Cm.L n (u n) p.1.1 ![p.2.1, p.2.2] ω‖)
        (fun n p _ => Φ n p.2.1 p.2.2 ^ 2) := by
      refine localAvg1_stochDomAt_of_whp fun τ'' hτ'' => ?_
      refine ⟨_, localAvg1_whp_L2G Cm.toFlowFM μ hL2 hu hτ4, ?_⟩
      refine Eventually.of_forall fun n ω hω p => ?_
      have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
      have hLle : ‖Cm.L n (u n) p.1.1 ![p.2.1, p.2.2] ω‖ ≤
          ((sz.size n : ℕ) : ℝ) ^ (τ' / 4) * STWB sz n (u n) (zdistInf d (sz.L n) (p.2.1 - p.2.2)) := by
        rcases Step2CloseGen_cases p.1.1 p.1.2 with h | h
        · rw [h, Cm.L_swap]
          have := hω p.2.2 p.2.1
          rwa [← neg_sub p.2.1 p.2.2, la2_zdistInf_neg] at this
        · rw [h]; exact hω p.2.1 p.2.2
      have hΦsq : Φ n p.2.1 p.2.2 ^ 2 =
          ((sz.size n : ℕ) : ℝ) ^ (τ' / 4) * STWB sz n (u n) (zdistInf d (sz.L n) (p.2.1 - p.2.2)) := by
        rw [hΦ, mul_pow, Real.sq_sqrt (by unfold STWB Bparam; positivity), ← Real.rpow_natCast,
          ← Real.rpow_mul (by linarith)]
        congr 2; push_cast; ring
      have hind1 : STindMaxg Cm.toFlowFM n (u n) (((sz.W n : ℕ) : ℝ) ^ (-ε₀)) ω ≤ 1 := by
        unfold STindMaxg; split_ifs <;> norm_num
      have hind0 : 0 ≤ STindMaxg Cm.toFlowFM n (u n) (((sz.W n : ℕ) : ℝ) ^ (-ε₀)) ω := by
        unfold STindMaxg; split_ifs <;> norm_num
      have hLn := norm_nonneg (Cm.L n (u n) p.1.1 ![p.2.1, p.2.2] ω)
      have hΦnn : 0 ≤ Φ n p.2.1 p.2.2 ^ 2 := sq_nonneg _
      calc STindMaxg Cm.toFlowFM n (u n) (((sz.W n : ℕ) : ℝ) ^ (-ε₀)) ω * ‖Cm.L n (u n) p.1.1 ![p.2.1, p.2.2] ω‖
          ≤ 1 * ‖Cm.L n (u n) p.1.1 ![p.2.1, p.2.2] ω‖ := mul_le_mul_of_nonneg_right hind1 hLn
        _ ≤ Φ n p.2.1 p.2.2 ^ 2 := by rw [one_mul, hΦsq]; exact hLle
        _ ≤ ((sz.size n : ℕ) : ℝ) ^ τ'' * Φ n p.2.1 p.2.2 ^ 2 :=
            le_mul_of_one_le_left hΦnn (Real.one_le_rpow hN1 hτ''.le)
    have hconc := hGijc ε₀ hε₀pos D₀ hD₀ Φ Ψ hΦr hΨ1 hΨ2 hLoop
    have E1 := StochDomAt.highProb hconc (τ := τ' / 4) hτ4
    have E2 := StochDomAt.highProb hGii' (τ := τ' / 4) hτ4
    have E3 := localAvg1_whp_omegaG Cm.toFlowFM μ hweak hu hc hΩev
    have E4 := localAvg1_whp_L2G Cm.toFlowFM μ hL2 hu hτ4
    refine ⟨_, (((E3.inter hsize E1).inter hsize E2).inter hsize E4), ?_⟩
    filter_upwards [hev, hfloor, hsize.eventually (eventually_le_rpow (Step2CloseGen_C2 d cB c' ^ 2) hτ4)] with
      n hn hfl hC ω hω q
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hω
    obtain ⟨hlow, hup⟩ := hn (u n) (hu0 n) (hu n).2
    have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
    have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
    have hW0 : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
    obtain ⟨P, hPdef⟩ : ∃ P : ℝ, P = ((sz.size n : ℕ) : ℝ) ^ (τ' / 8) := ⟨_, rfl⟩
    have hP1 : 1 ≤ P := by rw [hPdef]; exact Real.one_le_rpow hN1 (by positivity)
    have hP2 : ((sz.size n : ℕ) : ℝ) ^ (τ' / 4) = P ^ 2 := by
      rw [hPdef, ← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; congr 1; push_cast; ring
    have hP8 : ((sz.size n : ℕ) : ℝ) ^ τ' = P ^ 8 := by
      rw [hPdef, ← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; congr 1; push_cast; ring
    have hind : STindMaxg Cm.toFlowFM n (u n) (((sz.W n : ℕ) : ℝ) ^ (-ε₀)) ω = 1 := by
      have hΩ : ∀ x y : Idx d (sz.L n) (sz.W n), ‖Cm.GM n (u n) ω x y‖ ≤ ((sz.W n : ℕ) : ℝ) ^ (-ε₀) := h1
      unfold STindMaxg; simp [hΩ]
    have hτN : ((sz.size n : ℕ) : ℝ) ^ τ' ≤ ((sz.size n : ℕ) : ℝ) ^ τ :=
      Real.rpow_le_rpow_of_exponent_le hN1 hτ'τ
    have hS0 : ∀ K : ℕ, 0 ≤ STWB sz n (u n) K := fun K => by unfold STWB Bparam; positivity
    have hfl' : ∀ r : ℕ, (r : ℝ) ≤ ((sz.L n : ℕ) : ℝ) →
        (((sz.W n : ℕ) : ℝ) ^ (-D₀)) ^ 2 ≤
          cB * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * ((((r : ℕ) : ℝ) + 1) ^ (d - 2))⁻¹ := by
      intro r hr
      have e : (((sz.W n : ℕ) : ℝ) ^ (-D₀)) ^ 2 =
          ((sz.W n : ℕ) : ℝ) ^ (-((d : ℝ) + ((d - 2 : ℕ) : ℝ) / 𝔠 + 1)) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hW0.le, hD₀def]; congr 1; push_cast; ring
      rw [e]; exact hfl r hr
    rcases eq_or_ne q.1 q.2 with hxy | hxy
    · -- the diagonal, from `(GiiGEX)` and `max ‖𝓛^{(2)}‖`
      have h5 := h3 q
      rw [hind, one_mul, hP2] at h5
      have hmax := localAvg1_maxLoop2_leG Cm.toFlowFM n (u n) ω
        (X := ((sz.size n : ℕ) : ℝ) ^ (τ' / 4)) (by positivity) h4
      rw [hP2] at hmax
      have hz : zdistInf d (sz.L n) (STblk sz n q.1 - STblk sz n q.2) = 0 := by
        rw [hxy, sub_self, la2_zdistInf_zero]
      rw [hz]
      have hB : sz.Bctl n (u n) = STWB sz n (u n) 0 := rfl
      have hB0 : 0 ≤ sz.Bctl n (u n) := by rw [hB]; exact hS0 0
      have hP0 : (0 : ℝ) ≤ P := by linarith
      calc ‖Cm.GM n (u n) ω q.1 q.2‖ ^ 2 ≤ P ^ 2 * STmaxLoop2g Cm.toFlowFM n (u n) ω := h5
        _ ≤ P ^ 2 * (P ^ 2 * sz.Bctl n (u n)) := mul_le_mul_of_nonneg_left hmax (by positivity)
        _ ≤ P ^ 8 * sz.Bctl n (u n) := by
            have : P ^ 4 ≤ P ^ 8 := pow_le_pow_right₀ hP1 (by norm_num)
            nlinarith [mul_le_mul_of_nonneg_right this hB0]
        _ ≤ ((sz.size n : ℕ) : ℝ) ^ τ * STWB sz n (u n) 0 := by
            rw [← hB, ← hP8]
            exact mul_le_mul_of_nonneg_right hτN hB0
    · -- off the diagonal, from `STGijDecgL`
      have h5 := h2 ⟨(q.1, q.2), hxy⟩
      rw [hind, one_mul, hP2] at h5
      simp only [hΦ, hΨ] at h5
      have hR := Step2CloseGen_R_le hd sz n (u n) (X := ((sz.size n : ℕ) : ℝ) ^ (τ' / 8)) hcB hc'
        (by rw [← hPdef]; exact hP1) hlow hfl' q.1 q.2
      rw [← hPdef] at hR
      have hC2nn : 0 ≤ Step2CloseGen_C2 d cB c' := by
        unfold Step2CloseGen_C2 Step2CloseGen_K1; positivity
      have hG : ‖Cm.GM n (u n) ω q.1 q.2‖ ≤ P ^ 2 * (Step2CloseGen_C2 d cB c' * P *
          Real.sqrt (STWB sz n (u n) (zdistInf d (sz.L n) (STblk sz n q.1 - STblk sz n q.2)))) := by
        refine h5.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
        rw [← hPdef] at *
        exact hR
      have hbd := Step2CloseGen_arith hP1 (hS0 _) hC2nn (by rw [← hP2]; exact hC) (norm_nonneg _) hG
      calc ‖Cm.GM n (u n) ω q.1 q.2‖ ^ 2
          ≤ P ^ 8 * STWB sz n (u n) (zdistInf d (sz.L n) (STblk sz n q.1 - STblk sz n q.2)) := hbd
        _ ≤ _ := by rw [← hP8]; exact mul_le_mul_of_nonneg_right hτN (hS0 _)
  exact localAvg1_perTime_of_stoch (hPrec.precomp_param
    (V := fun n => Unit × (Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n))) (fun n p => p.2))

/-- **Target 9 (GMN-C1), `stLocalAvgOfL2_holdsDecG`** (`LocalAvg2:467`; `3_5:455–465`): the pin `STLocalAvgOfL2gL` over a carrier family from the
inputs of other blocks as `∀`-flow arguments (`hdat`: the size data; `hGii`, `hGav`: `(GiiGEX)`, `(GavLGEX)` of `lem_GbEXP`; `hGij`: `STGijDecgL`, in
place of `STGijGEXgL`) and `hF` (the setting `Flow` gives `flowOK`).  The local bound is `stStep2LocalPT_of_L2decayDecG`, the average bound is the
merged `stStep2AvgPT_of_L2decayG`. -/
theorem stLocalAvgOfL2_holdsDecG {d : ℕ} (hd : 0 < d) (law : ∀ sz : Sizes d, Measure sz.SeqΩ)
    (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop) (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), Step2Data sz)
    (hF : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Flow sz κ ε 𝔠 𝔡 z → (mk sz z).flowOK κ ε 𝔠 𝔡)
    (hdat : ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), Flow sz κ ε 𝔠 𝔡 z →
      ∃ cB c : ℝ, 0 < cB ∧ 0 < c ∧ ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ (mk sz z).T0 n) →
        ∀ᶠ n in atTop, ∀ u : ℝ, 0 ≤ u → u ≤ t n →
          cB * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ sz.Bctl n u ∧ sz.Bctl n u ≤ ((sz.size n : ℕ) : ℝ) ^ (-c))
    (hGii : ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), Flow sz κ ε 𝔠 𝔡 z →
      ∀ u : ℕ → ℝ, (∀ n, 0 ≤ u n) → (∀ n, u n ≤ (mk sz z).T0 n) → ∀ ε₀ : ℝ, 0 < ε₀ →
        STGiiGEXgL (mk sz z).toFlowFM (law sz) u ε₀)
    (hGij : ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), Flow sz κ ε 𝔠 𝔡 z →
      ∀ u : ℕ → ℝ, (∀ n, 0 ≤ u n) → (∀ n, u n ≤ (mk sz z).T0 n) →
        STGijDecgL (mk sz z).toFlowFM (law sz) u)
    (hGav : ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), Flow sz κ ε 𝔠 𝔡 z →
      ∀ u : ℕ → ℝ, (∀ n, 0 ≤ u n) → (∀ n, u n ≤ (mk sz z).T0 n) → ∀ ε₀ : ℝ, 0 < ε₀ →
        STGavLGEXgL (mk sz z).toFlowFM (law sz) u ε₀) :
    STLocalAvgOfL2gL d law Flow (fun sz z => (mk sz z).toFlowFM) (fun sz z => (mk sz z).T0) := by
  intro κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow s t hs hst htl hweak hL2
  exact ⟨stStep2LocalPT_of_L2decayDecG (mk sz z) (law sz) hd (hF sz κ ε 𝔠 𝔡 z hflow) hs hst htl
      (hdat κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow) (hGii κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow)
      (hGij κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow) hweak hL2,
    stStep2AvgPT_of_L2decayG (mk sz z) (law sz) hd hκ (hF sz κ ε 𝔠 𝔡 z hflow) hs hst htl
      (hdat κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow) (hGav κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow) hweak hL2⟩

/-! ## 3. Target 11: the band corollary, the band re-derivation of target 9 and compiled nonempty instances -/

/-- **Band re-derivation of target 9** (`3 ≤ d`): the merged `stLocalAvgOfL2_holds` (`LocalAvg2:482`) from `stLocalAvgOfL2_holdsDecG` at the band
family `(seqP, STFlow, bandStep2Data, ·)`; the Green input is `bandFM_STGijDecgL_of_three_le` (`Evolution/FarEntry.lean:1724`), `(GiiGEX)` and
`(GavLGEX)` are the merged `stGbEXP_holds`, the size data `localAvg1_data`. -/
theorem step2CloseGen_stLocalAvgOfL2_band {d : ℕ} (hd : 3 ≤ d) : STLocalAvgOfL2 d := by
  have hd0 : 0 < d := by omega
  exact stLocalAvgOfL2_holdsDecG hd0 (fun sz => sz.seqP) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
    (fun sz z => bandStep2Data sz z) (fun _ _ _ _ _ _ h => h)
    (fun κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow => by
      obtain ⟨cB, c, hcB, hc, hdat⟩ := localAvg1_data hd0 hκ hε h𝔡 𝔠
      exact ⟨cB, c, hcB, hc, hdat sz z hflow⟩)
    (fun κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow u hu0 hul ε₀ hε₀ =>
      (Green.stGbEXP_holds hd).1 κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow u hu0 hul ε₀ hε₀)
    (fun κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow u hu0 hul =>
      bandFM_STGijDecgL_of_three_le hd hκ hε h𝔡 hflow hu0 hul)
    (fun κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow u hu0 hul ε₀ hε₀ =>
      (Green.stGbEXP_holds hd).2.2 κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow u hu0 hul ε₀ hε₀)

example : type_of% @RBM.Gauss.Sizes.stLocalAvgOfL2_holds := by
  intro d hd
  exact step2CloseGen_stLocalAvgOfL2_band hd

/-- **Target 11, the band corollary** (the statement of `STStep2 d` for `3 ≤ d`; the band `ST_step2_of_pinsLW'`, `Step2Iterate.lean:1793`, read through
`ST_step2_of_pinsg`): every pin of `step2IterGen_step2_of_pins_band` is discharged by a producer inside the cone of this file, namely `STNewKLK`
(`stNewKLK_holds`), `STK2decay`, `STNetLift2`, `STScaleExists`, `ST_Bdata_holds`, `STOptL2` (by `stOptL2_of_pinsg`, through
`optL2Gen_stOptL2_of_pins_band`, from `STLWB` of `LWterm`) and `STLocalAvgOfL2` (by `stLocalAvgOfL2_holdsDecG`, through
`step2CloseGen_stLocalAvgOfL2_band`).  What remains are the two light-weight inputs `LWterm d`, `LWtermExp d` (no `Graph/LWTermHolds` import) and two
pins whose merged producers are not imported here: `STEMn2Exp d` (`stEMn2Exp_holds`, `Induction/EMn2Exp2`: its import cone contains `RBM3D.BA.FlowPins`
and `RBM3D.BA.MFixedPoint`) and `STGridMart d` (`stGridMart_holds`, `Path/DifREP2`: a BA-free cone, but 22 further modules, among them `StepDecompN`,
`LoopC2N`, `HierarchyN`, `GridDriftN`, `AzumaProxyN`, which the ticket keeps out of this row).  The band terminal (`Induction/MainIndHolds`) plugs in all four producers. -/
theorem step2CloseGen_step2_of_pinsLW' {d : ℕ} (hd : 3 ≤ d) (hLW : LWterm d) (hLWE : LWtermExp d)
    (hEMe : STEMn2Exp d) (hMart : STGridMart d) : STStep2 d :=
  step2IterGen_step2_of_pins_band d (STLWT_of_LWtermExp hd hLWE) hEMe hMart
    (optL2Gen_stOptL2_of_pins_band hd (STLWB_of_LWterm hd hLW) hMart) (step2CloseGen_stLocalAvgOfL2_band hd)

/-! ### Compiled nonempty instances (targets 9-11; CLAUDE.md §4 step 2)

Data: the band carrier `bandStep2Data sz0 z0` (`d = 3`, `sz0`: `L_n = 4(n+1)`, `W_n = (2(n+1))^5`, `lam_n = (2(n+1))^{-6}`; flow `z0`,
`κ = ε = 𝔡 = 1/10`, `𝔠 = 1/6`), the law `seqP sz0`, the window `[0, 1/16]`.  Discharged: the setting `flowOK`, the size data, `(GiiGEX)`, `(GavLGEX)`,
`STGijDecgL` (`bandFM_STGijDecgL_of_three_le`), the time ranges.  What stays a hypothesis is a stochastic premise (the weak law of Step 1 and
`(eq:L2_decay)`) or a pin of another gate (`LWterm`, `LWtermExp`, `STEMn2Exp`, `STGridMart`). -/

section Instances

open RBM.Gauss.SizesInst RBM.Gauss.InductionDefsInst RBM.Gauss.Step2DefsInst RBM.Gauss.Step2IterateInst

/-- **Target 9 at the data**: `(Gt_bound_flow)` per time on `[0, 1/16]` over `bandStep2Data sz0 z0` from `STGijDecgL`. -/
example (hweak : STStep1WeakgL (bandStep2Data sz0 z0).toFlowFM sz0.seqP sInst tInst)
    (hL2 : STL2decayPTgL (bandStep2Data sz0 z0).toFlowFM sz0.seqP sInst tInst) :
    STStep2LocalPTgL (bandStep2Data sz0 z0).toFlowFM sz0.seqP sInst tInst :=
  stStep2LocalPT_of_L2decayDecG (bandStep2Data sz0 z0) sz0.seqP (by norm_num : 0 < 3) flow_z0 hs0 hst htT
    RBM.Gauss.LocalAvg1Inst.localAvg1_inst_hdat
    (fun u hu0 hul ε₀ hε₀ => (Green.stGbEXP_holds (by norm_num : 3 ≤ 3)).1 (1 / 10) (1 / 10) (1 / 10)
      (by norm_num) (by norm_num) (by norm_num) (1 / 6) sz0 z0 flow_z0 u hu0 hul ε₀ hε₀)
    (fun u hu0 hul => bandFM_STGijDecgL_of_three_le (by norm_num : 3 ≤ 3) (by norm_num : (0 : ℝ) < 1 / 10)
      (by norm_num : (0 : ℝ) < 1 / 10) (by norm_num : (0 : ℝ) < 1 / 10) flow_z0 hu0 hul)
    hweak hL2

/-- **Target 9, the closing pin at the data**: `stLocalAvgOfL2_holdsDecG` at the band carrier, applied at `(sz0, z0, s ≡ 0, t ≡ 1/16)`. -/
example (hweak : STStep1WeakgL (bandStep2Data sz0 z0).toFlowFM sz0.seqP sInst tInst)
    (hL2 : STL2decayPTgL (bandStep2Data sz0 z0).toFlowFM sz0.seqP sInst tInst) :
    STStep2LocalPTgL (bandStep2Data sz0 z0).toFlowFM sz0.seqP sInst tInst ∧
      STStep2AvgPTgL (bandStep2Data sz0 z0).toFlowFM sz0.seqP sInst tInst :=
  stLocalAvgOfL2_holdsDecG (by norm_num : 0 < 3) (fun sz => sz.seqP) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
    (fun sz z => bandStep2Data sz z) (fun _ _ _ _ _ _ h => h)
    (fun κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow => by
      obtain ⟨cB, c, hcB, hc, hdat⟩ := localAvg1_data (by norm_num : 0 < 3) hκ hε h𝔡 𝔠
      exact ⟨cB, c, hcB, hc, hdat sz z hflow⟩)
    (fun κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow u hu0 hul ε₀ hε₀ =>
      (Green.stGbEXP_holds (by norm_num : 3 ≤ 3)).1 κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow u hu0 hul ε₀ hε₀)
    (fun κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow u hu0 hul =>
      bandFM_STGijDecgL_of_three_le (by norm_num : 3 ≤ 3) hκ hε h𝔡 hflow hu0 hul)
    (fun κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow u hu0 hul ε₀ hε₀ =>
      (Green.stGbEXP_holds (by norm_num : 3 ≤ 3)).2.2 κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow u hu0 hul ε₀ hε₀)
    (1 / 10) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 6) sz0 z0 flow_z0 sInst tInst hs0 hst htT
    hweak hL2

/-- **Target 10 at the data**: the class at the band carrier of `(sz0, z0)` and the identities of section 12.2 at `n = 100`, `u = 1/32`. -/
example : Step2IterGen_ListLink (bandStep2Mat sz0 (STflowE z0)) := step2IterGen_listLink_band sz0 _

example (H : Matrix (Idx 3 (sz0.L 100) (sz0.W 100)) (Idx 3 (sz0.L 100) (sz0.W 100)) ℂ) (σ : Fin 2 → Bool)
    (a : Fin 2 → Zd 3 (sz0.L 100)) :
    STEGtMg (bandStep2Mat sz0 (STflowE z0)) 100 (1 / 32) H σ a =
        STegtMg (bandStep2Mat sz0 (STflowE z0)) 100 (1 / 32) H (KLloopOf 3 (sz0.L 100) σ a) ∧
      STEEMg (bandStep2Mat sz0 (STflowE z0)) 100 (1 / 32) H σ a =
        STeeMg (bandStep2Mat sz0 (STflowE z0)) 100 (1 / 32) H σ a a ∧
      STELKLKMg (bandStep2Mat sz0 (STflowE z0)) 100 (1 / 32) H σ a =
        STelklkMg (bandStep2Mat sz0 (STflowE z0)) 100 (1 / 32) H (KLloopOf 3 (sz0.L 100) σ a) ∧
      STLKMg (bandStep2Mat sz0 (STflowE z0)) 100 (1 / 32) H σ a =
        STLKIMg (bandStep2Mat sz0 (STflowE z0)) 100 (1 / 32) H (KLloopOf 3 (sz0.L 100) σ a) :=
  have hL := step2IterGen_listLink_band sz0 (STflowE z0)
  ⟨STEGtMg_eq_STegtMg _ hL 100 _ H σ a, STEEMg_eq_STeeMg _ hL 100 _ H σ a, STELKLKMg_eq_STelklkMg _ hL 100 _ H σ a,
    STLKMg_eq_STLKIMg _ hL 100 _ H σ a⟩

example (s t : ℕ → ℝ) (K : ℕ → ℕ) (σ : Fin 2 → Bool) (a : Fin 2 → Zd 3 (sz0.L 100)) (k : ℕ) (ω : PathΩ sz0) :
    STgDriftg (bandStep2Mat sz0 (STflowE z0)) s t K 100 σ a k ω =
        STgDriftNg (bandStep2Mat sz0 (STflowE z0)) s t K 100 σ a k ω ∧
      STgAg (bandStep2Mat sz0 (STflowE z0)) s t K 100 σ a k ω =
        STgANg (bandStep2Mat sz0 (STflowE z0)) s t K 100 σ a k ω :=
  have hL := step2IterGen_listLink_band sz0 (STflowE z0)
  ⟨STgDriftg_eq_STgDriftNg _ hL s t K 100 σ a k ω, STgAg_eq_STgANg _ hL s t K 100 σ a k ω⟩

/-- **Target 11 at the data**: the band corollary at `d = 3`, read through `inst_step2` (the premises `STLKgL`, `STDecaygL` at `s` and Step 1's
conclusions stay hypotheses; the four pins stay hypotheses). -/
example (hLW : LWterm 3) (hLWE : LWtermExp 3) (hEMe : STEMn2Exp 3) (hMart : STGridMart 3) :
    ∃ Cd : ℝ, 0 < Cd ∧ ∃ 𝔠d : ℝ, 0 < 𝔠d ∧ 𝔠d ≤ 1 / 100 ∧
      (STLK sz0 (STflowE z0) sInst → STDecay sz0 (STflowE z0) sInst →
        STStep1Loop sz0 (STflowE z0) sInst tInst → STStep1Weak sz0 (STflowE z0) sInst tInst →
        STStep2Concl sz0 (STflowE z0) sInst tInst Cd) :=
  inst_step2 (step2CloseGen_step2_of_pinsLW' (by norm_num : 3 ≤ 3) hLW hLWE hEMe hMart)

end Instances

end RBM.BA

end
