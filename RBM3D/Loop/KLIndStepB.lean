/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Loop.KLIndStepA

/-!
# The `K`-loop layer, KL10b: case (ii) of `(eq:ind-step-bound)` and `KLindStepPin`

Ticket T2106 (`A_deterministic_estimates.tex:703-790`).  Names are in `RBM.Loop`; every helper the
ticket does not pin is `private` and carries the file stem `KLIndStepB`.  Everything of
`Loop/KLIndStepA.lean` is reused (no `open private` is added).

* §1 the pins `KLindStepAt`, `KLindStepPin` (verbatim: the probe pins
  `64b58eb:RBM3D/Probe/T2004Pins.lean:845-863`), the abstract pin `IndStepAbs` (probe
  `t/T2360:RBM3D/Probe/T2360Pins.lean:261`) and `KLindStepAt_iff` (`KLindStepAt` is `IndStepAbs` at the
  band data, `Iff.rfl`).
* §2 the expansion `∏_{j≠r} (f₀ + f₁ + f₂)` in the positions `V` of `f₂` and `U` of `f₁`
  (`Finset.prod_add` twice) and the bounds of the groups, for abstract data: (G0) `V = U = ∅`,
  (G2) `V ≠ ∅` (one distinguished `f₂`, every other factor `≤ 2 K B_{t,0}`), (G3) `V = ∅`,
  `|U| ≥ 2` (two distinguished `f₁`); (G1) `V = ∅`, `|U| = 1` vanishes (`KLIndStepA_slice_vanish`).
* §3 the two sums over `b` and the slice of (G2), (G3): `SigSumZeroAbs` with `Q = d`, `Q = 2d - 2`,
  then `KLlat_pow_dim_rpow`, `KLlat_pair_rpow`.
* §4 the three parts of a leaf (`f₀`, `f₁`, `f₂` of `s ↦ TH(a, b + s)`) and the real bookkeeping.
* §5 `KLIndStepB_alt_abs`: the pin's inequality for every alternating `σ` and every root, over the
  bundles; `KLindStep_alt` is its band instance.
* §6 `indStepAbs_of` (T2365, K09a: the step over the abstract bundles `IndStepTH`, `SigDecayAbs`,
  `SigSumZeroAbs` of `KLIndStepA.lean` §5b), `KLindStepAt_holds` (its band instance) and
  `KLindStepPin_holds`.  §2-§5 below are stated over the bundles; the band statement `KLindStep_alt`
  is their instance.
* §7 the compiled instances at `d = 3`, `L = 5`, `g = 1/2`, `E = 0`, `t = 9/10`.

Groups.  A pattern `ξ ∈ {0,1,2}^{n-1}` is the pair `(V, U)` with `V = {ξ = 2}`, `U = {ξ = 1}`;
(G0) `V = U = ∅`, (G1) `V = ∅`, `|U| = 1`, (G2) `V ≠ ∅`, (G3) `V = ∅`, `|U| ≥ 2` are disjoint and
exhaust the patterns.  For `V ≠ ∅` the factors outside `V` are not expanded further (the crude
bound `‖f₀ + f₁‖ ≤ 2 K B_{t,0}` suffices), so `Finset.prod_add` is used once on
`f₂ + (f₁ + f₀)` and, for the term `V = ∅`, once more on `f₁ + f₀`.  The loss is split as
`L^τ = (L^{τ/3})³`: (G2) uses one `(eq:f12)` loss `L^{τ/3}` and one lattice-sum loss `L^{τ/3}`,
(G3) two `(eq:f12)` losses and one lattice-sum loss; (G0) has none.  The constant is
`C = 2^{n-1} (C_s (2K)^{n-2} + K₁₂² (2K)^{n-3} C₃ + K₁₂ (2K)^{n-2} C₂)` with `K = KLf_crude_bound`,
`K₁₂ = KLf12_bound` at `τ/3`, `C_s` the signed slice constant and `C₂`, `C₃` the constants of the
sums of §3: it depends on `d, n, κ, gmax, τ` only.
-/

set_option linter.style.longLine false

namespace RBM.Loop

open Finset

/-! ## 1. The pins -/

/-- **Route pin `(eq:ind-step-bound)`** (the new `d ≥ 3` estimate; properties 5, 5', 6, 7, 8 and
the two estimates of `KLsumZeroAt`), in the form the cut at an innermost long edge uses
(`RBM2D/Loop/KBoundCut.lean:1954` `Kpi_cut`, `innerId`): the root leaf `p` is long
(`σ_p ≠ σ_{p+1}`) and the other leaves carry `Θ^{(σ_i,σ_{i+1})}_t`;
`∑_{b} |∑_{δ_p = b} Σ^{(∅)}(t,σ,δ) ∏_{i≠p} Θ_{t,a_i δ_i}| ≺ B_{t,0}^{n-2}`.  (The paper's
`Θ̃_t ∈ {Θ_t, tS^{(B)}Θ_t^{(+,-)}}` is not needed: `tSΘ^{(+,-)} = Θ^{(+,-)} - I`, and the glued
edge is `ξ_J S_{uw}` times a standard leaf of the outer polygon.) -/
def KLindStepAt (d n : ℕ) [NeZero n] (κ gmax : ℝ) : Prop :=
  ∀ τ : ℝ, 0 < τ → ∃ C : ℝ, 0 < C ∧ ∀ (p : KLPar κ gmax) (σ : Fin n → Bool) (r : Fin n),
    σ r ≠ σ (r + 1) → ∀ a : Fin n → Zd d p.L,
      ∑ b : Zd d p.L, ‖∑ δ ∈ Finset.univ.filter (fun δ : Fin n → Zd d p.L => δ r = b),
          KLSigmaPi d p.L p.g (mSigma p.E) p.t σ ∅ δ *
            ∏ i ∈ Finset.univ.erase r,
              thetaEdge d p.L p.g (mSigma p.E) p.t (σ i) (σ (i + 1)) (a i) (δ i)‖
        ≤ C * (p.L : ℝ) ^ τ * (Bparam d p.L p.g p.t 0) ^ (n - 2)

def KLindStepPin : Prop :=
  ∀ (d n : ℕ) [NeZero n] (κ gmax : ℝ), 3 ≤ d → 3 ≤ n → 0 < κ → 0 < gmax → KLPT d κ gmax →
    KLindStepAt d n κ gmax

/-- **`IndStepAbs`** (verbatim: the probe pin `t/T2360:RBM3D/Probe/T2360Pins.lean:261`): `(eq:ind-step-bound)`
over abstract data, an index family `ι` with sizes `L`, weight `Bp = B_{t,0}`, molecule weight `Sig` and
leaf edges `TH`. -/
def IndStepAbs {ι : Type} (d n : ℕ) [NeZero n] (L : ι → ℕ) [∀ i, NeZero (L i)] (Bp : ι → ℝ)
    (Sig : ∀ i, (Fin n → Bool) → (Fin n → Zd d (L i)) → ℂ)
    (TH : ∀ i, Bool → Bool → Matrix (Zd d (L i)) (Zd d (L i)) ℂ) : Prop :=
  ∀ τ : ℝ, 0 < τ → ∃ C : ℝ, 0 < C ∧ ∀ (i : ι) (σ : Fin n → Bool) (r : Fin n), σ r ≠ σ (r + 1) →
    ∀ a : Fin n → Zd d (L i),
      ∑ b : Zd d (L i), ‖∑ δ ∈ Finset.univ.filter (fun δ : Fin n → Zd d (L i) => δ r = b),
          Sig i σ δ * ∏ j ∈ Finset.univ.erase r, TH i (σ j) (σ (j + 1)) (a j) (δ j)‖
        ≤ C * (L i : ℝ) ^ τ * (Bp i) ^ (n - 2)

/-- The band pin `KLindStepAt` is `IndStepAbs` at `ι = KLPar κ gmax`, `Sig = Σ^{(∅)}`, `TH = thetaEdge`. -/
theorem KLindStepAt_iff (d n : ℕ) [NeZero n] (κ gmax : ℝ) :
    KLindStepAt d n κ gmax ↔
      IndStepAbs (ι := KLPar κ gmax) d n (fun p => p.L) (fun p => Bparam d p.L p.g p.t 0)
        (fun p σ δ => KLSigmaPi d p.L p.g (mSigma p.E) p.t σ ∅ δ)
        (fun p s s' => thetaEdge d p.L p.g (mSigma p.E) p.t s s') := Iff.rfl


/-! ## 2. The expansion and the bounds of the groups, for abstract data -/

section Abstract

/-- `‖∏_{j ∈ s} x_j‖ ≤ M^{|s|}`. -/
private theorem KLIndStepB_prod_bound {ι : Type*} (s : Finset ι) (x : ι → ℂ) {M : ℝ}
    (hx : ∀ j ∈ s, ‖x j‖ ≤ M) : ‖∏ j ∈ s, x j‖ ≤ M ^ s.card := by
  rw [norm_prod]
  calc ∏ j ∈ s, ‖x j‖ ≤ ∏ _j ∈ s, M := prod_le_prod₀ (fun _ _ => norm_nonneg _) hx
    _ = M ^ s.card := prod_const M

/-- One distinguished factor `x_i`, `i ∈ V ⊆ J`; the other factors of `V` and of `J \ V` are `≤ M`. -/
private theorem KLIndStepB_prodV_le {ι : Type*} [DecidableEq ι] {J V : Finset ι} (hV : V ⊆ J)
    {i : ι} (hi : i ∈ V) (x y : ι → ℂ) {M : ℝ}
    (hx : ∀ j ∈ J, ‖x j‖ ≤ M) (hy : ∀ j ∈ J, ‖y j‖ ≤ M) :
    ‖∏ j ∈ V, x j‖ * ‖∏ j ∈ J \ V, y j‖ ≤ ‖x i‖ * M ^ (J.card - 1) := by
  have hM : 0 ≤ M := (norm_nonneg _).trans (hx i (hV hi))
  have h1 : ‖∏ j ∈ V, x j‖ = ‖x i‖ * ‖∏ j ∈ V.erase i, x j‖ := by
    rw [← mul_prod_erase V x hi, norm_mul]
  have h2 : ‖∏ j ∈ V.erase i, x j‖ ≤ M ^ (V.erase i).card :=
    KLIndStepB_prod_bound _ _ (fun j hj => hx j (hV (mem_of_mem_erase hj)))
  have h3 : ‖∏ j ∈ J \ V, y j‖ ≤ M ^ (J \ V).card :=
    KLIndStepB_prod_bound _ _ (fun j hj => hy j (mem_sdiff.1 hj).1)
  have hc : (V.erase i).card + (J \ V).card = J.card - 1 := by
    rw [card_erase_of_mem hi, card_sdiff_of_subset hV]
    have := card_le_card hV
    have := card_pos.2 ⟨i, hi⟩
    omega
  rw [h1]
  calc ‖x i‖ * ‖∏ j ∈ V.erase i, x j‖ * ‖∏ j ∈ J \ V, y j‖
      ≤ ‖x i‖ * M ^ (V.erase i).card * M ^ (J \ V).card := by gcongr
    _ = ‖x i‖ * M ^ (J.card - 1) := by rw [mul_assoc, ← pow_add, hc]

/-- Two distinguished factors `x_i`, `x_l`, `i ≠ l ∈ U ⊆ J`. -/
private theorem KLIndStepB_prodU_le {ι : Type*} [DecidableEq ι] {J U : Finset ι} (hU : U ⊆ J)
    {i l : ι} (hi : i ∈ U) (hl : l ∈ U) (hil : i ≠ l) (x y : ι → ℂ) {M : ℝ}
    (hx : ∀ j ∈ J, ‖x j‖ ≤ M) (hy : ∀ j ∈ J, ‖y j‖ ≤ M) :
    ‖∏ j ∈ J \ U, y j‖ * ‖∏ j ∈ U, x j‖ ≤ ‖x i‖ * ‖x l‖ * M ^ (J.card - 2) := by
  have hM : 0 ≤ M := (norm_nonneg _).trans (hx i (hU hi))
  have hl' : l ∈ U.erase i := mem_erase.2 ⟨hil.symm, hl⟩
  have h1 : ‖∏ j ∈ U, x j‖ = ‖x i‖ * (‖x l‖ * ‖∏ j ∈ (U.erase i).erase l, x j‖) := by
    rw [← mul_prod_erase U x hi, ← mul_prod_erase (U.erase i) x hl', norm_mul, norm_mul]
  have h2 : ‖∏ j ∈ (U.erase i).erase l, x j‖ ≤ M ^ ((U.erase i).erase l).card :=
    KLIndStepB_prod_bound _ _ (fun j hj =>
      hx j (hU (mem_of_mem_erase (mem_of_mem_erase hj))))
  have h3 : ‖∏ j ∈ J \ U, y j‖ ≤ M ^ (J \ U).card :=
    KLIndStepB_prod_bound _ _ (fun j hj => hy j (mem_sdiff.1 hj).1)
  have hc : ((U.erase i).erase l).card + (J \ U).card = J.card - 2 := by
    rw [card_erase_of_mem hl', card_erase_of_mem hi, card_sdiff_of_subset hU]
    have h4 := card_le_card hU
    have h5 : 1 < U.card := one_lt_card.2 ⟨i, hi, l, hl, hil⟩
    omega
  rw [h1]
  calc ‖∏ j ∈ J \ U, y j‖ * (‖x i‖ * (‖x l‖ * ‖∏ j ∈ (U.erase i).erase l, x j‖))
      ≤ M ^ (J \ U).card * (‖x i‖ * (‖x l‖ * M ^ ((U.erase i).erase l).card)) := by gcongr
    _ = ‖x i‖ * ‖x l‖ * M ^ (J.card - 2) := by
        rw [← hc, pow_add]; ring

/-- The expansion of `∏_{j ∈ J} (φ₀ + φ₁ + φ₂)`: `V` = the `φ₂` positions of the pattern; the
terms with `V = ∅` are expanded once more in `U` = the `φ₁` positions. -/
private theorem KLIndStepB_expand {ι X : Type*} [DecidableEq ι] (J : Finset ι) (S : Finset X)
    (Sg : X → ℂ) (φ0 : ι → ℂ) (φ1 φ2 : ι → X → ℂ) :
    ∑ δ ∈ S, Sg δ * ∏ j ∈ J, (φ0 j + φ1 j δ + φ2 j δ)
      = ∑ U ∈ J.powerset, (∏ j ∈ J \ U, φ0 j) * ∑ δ ∈ S, Sg δ * ∏ j ∈ U, φ1 j δ
        + ∑ V ∈ J.powerset.erase ∅, ∑ δ ∈ S,
            Sg δ * ((∏ j ∈ V, φ2 j δ) * ∏ j ∈ J \ V, (φ1 j δ + φ0 j)) := by
  have hpt : ∀ δ, ∏ j ∈ J, (φ0 j + φ1 j δ + φ2 j δ)
      = ∏ j ∈ J, (φ1 j δ + φ0 j)
        + ∑ V ∈ J.powerset.erase ∅, (∏ j ∈ V, φ2 j δ) * ∏ j ∈ J \ V, (φ1 j δ + φ0 j) := by
    intro δ
    have h1 : ∏ j ∈ J, (φ0 j + φ1 j δ + φ2 j δ) = ∏ j ∈ J, (φ2 j δ + (φ1 j δ + φ0 j)) :=
      prod_congr rfl fun j _ => by ring
    rw [h1, prod_add (fun j => φ2 j δ) (fun j => φ1 j δ + φ0 j) J,
      ← add_sum_erase J.powerset _ (empty_mem_powerset J)]
    simp
  have hpt2 : ∀ δ, ∏ j ∈ J, (φ1 j δ + φ0 j)
      = ∑ U ∈ J.powerset, (∏ j ∈ U, φ1 j δ) * ∏ j ∈ J \ U, φ0 j :=
    fun δ => prod_add (fun j => φ1 j δ) φ0 J
  have hA : ∑ δ ∈ S, Sg δ * ∏ j ∈ J, (φ1 j δ + φ0 j)
      = ∑ U ∈ J.powerset, (∏ j ∈ J \ U, φ0 j) * ∑ δ ∈ S, Sg δ * ∏ j ∈ U, φ1 j δ := by
    simp_rw [hpt2, mul_sum]
    rw [sum_comm]
    refine sum_congr rfl fun U _ => ?_
    refine sum_congr rfl fun δ _ => ?_
    ring
  have hB : ∑ δ ∈ S, Sg δ * ∑ V ∈ J.powerset.erase ∅,
        (∏ j ∈ V, φ2 j δ) * ∏ j ∈ J \ V, (φ1 j δ + φ0 j)
      = ∑ V ∈ J.powerset.erase ∅, ∑ δ ∈ S,
          Sg δ * ((∏ j ∈ V, φ2 j δ) * ∏ j ∈ J \ V, (φ1 j δ + φ0 j)) := by
    simp_rw [mul_sum]
    rw [sum_comm]
  calc ∑ δ ∈ S, Sg δ * ∏ j ∈ J, (φ0 j + φ1 j δ + φ2 j δ)
      = ∑ δ ∈ S, (Sg δ * ∏ j ∈ J, (φ1 j δ + φ0 j)
          + Sg δ * ∑ V ∈ J.powerset.erase ∅,
            (∏ j ∈ V, φ2 j δ) * ∏ j ∈ J \ V, (φ1 j δ + φ0 j)) := by
        refine sum_congr rfl fun δ _ => ?_
        rw [hpt δ, mul_add]
    _ = _ := by rw [sum_add_distrib, hA, hB]

/-- The norm form of `KLIndStepB_expand`. -/
private theorem KLIndStepB_expand_norm {ι X : Type*} [DecidableEq ι] (J : Finset ι) (S : Finset X)
    (Sg : X → ℂ) (φ0 : ι → ℂ) (φ1 φ2 : ι → X → ℂ) :
    ‖∑ δ ∈ S, Sg δ * ∏ j ∈ J, (φ0 j + φ1 j δ + φ2 j δ)‖
      ≤ ∑ U ∈ J.powerset, ‖∏ j ∈ J \ U, φ0 j‖ * ‖∑ δ ∈ S, Sg δ * ∏ j ∈ U, φ1 j δ‖
        + ∑ V ∈ J.powerset.erase ∅, ∑ δ ∈ S,
            ‖Sg δ‖ * (‖∏ j ∈ V, φ2 j δ‖ * ‖∏ j ∈ J \ V, (φ1 j δ + φ0 j)‖) := by
  rw [KLIndStepB_expand]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · refine (norm_sum_le _ _).trans (sum_le_sum fun U _ => ?_)
    rw [norm_mul]
  · refine (norm_sum_le _ _).trans (sum_le_sum fun V _ => ?_)
    refine (norm_sum_le _ _).trans (sum_le_sum fun δ _ => ?_)
    rw [norm_mul, norm_mul]


/-- (G0), abstract: all factors `f₀`; one row sum and the signed slice bound. -/
private theorem KLIndStepB_G0 {ι X D : Type*} [Fintype D] {J : Finset ι} {j0 : ι}
    (hj0 : j0 ∈ J) (S : D → Finset X) (Sg : X → ℂ) (φ0 : D → ι → ℂ) {M Cs τ0 : ℝ}
    (hM : 0 ≤ M) (hCs : 0 ≤ Cs) (hτ0 : 0 < τ0) (hφ0 : ∀ b, ∀ j ∈ J, ‖φ0 b j‖ ≤ M)
    (hsl : ∀ b, ‖∑ δ ∈ S b, Sg δ‖ ≤ Cs * τ0) (hrow : ∑ b, ‖φ0 b j0‖ ≤ τ0⁻¹) :
    ∑ b, ‖∏ j ∈ J, φ0 b j‖ * ‖∑ δ ∈ S b, Sg δ‖ ≤ Cs * M ^ (J.card - 1) := by
  classical
  have hMp : 0 ≤ M ^ (J.card - 1) := pow_nonneg hM _
  calc ∑ b, ‖∏ j ∈ J, φ0 b j‖ * ‖∑ δ ∈ S b, Sg δ‖
      ≤ ∑ b, (‖φ0 b j0‖ * M ^ (J.card - 1)) * (Cs * τ0) := by
        refine sum_le_sum fun b _ => ?_
        have h1 : ‖∏ j ∈ J, φ0 b j‖ ≤ ‖φ0 b j0‖ * M ^ (J.card - 1) := by
          rw [← mul_prod_erase J (φ0 b) hj0, norm_mul]
          have := KLIndStepB_prod_bound (J.erase j0) (φ0 b)
            (fun j hj => hφ0 b j (mem_of_mem_erase hj))
          rw [card_erase_of_mem hj0] at this
          gcongr
        calc ‖∏ j ∈ J, φ0 b j‖ * ‖∑ δ ∈ S b, Sg δ‖
            ≤ (‖φ0 b j0‖ * M ^ (J.card - 1)) * ‖∑ δ ∈ S b, Sg δ‖ := by gcongr
          _ ≤ (‖φ0 b j0‖ * M ^ (J.card - 1)) * (Cs * τ0) := by
              gcongr; exact hsl b
    _ = (Cs * τ0 * M ^ (J.card - 1)) * ∑ b, ‖φ0 b j0‖ := by
        rw [mul_sum]
        exact sum_congr rfl fun b _ => by ring
    _ ≤ (Cs * τ0 * M ^ (J.card - 1)) * τ0⁻¹ := by gcongr
    _ = Cs * M ^ (J.card - 1) := by field_simp

/-- (G2), abstract: `i ∈ V` distinguished; every other factor is bounded by `M`. -/
private theorem KLIndStepB_G2 {ι X D : Type*} [DecidableEq ι] [Fintype D] {J V : Finset ι}
    (hV : V ⊆ J) {i : ι} (hi : i ∈ V) (S : D → Finset X) (Sg : X → ℂ)
    (φ0 : D → ι → ℂ) (φ1 φ2 : D → ι → X → ℂ) {M c : ℝ} (hM : 0 ≤ M) (w : D → X → ℝ)
    (h2 : ∀ b, ∀ δ ∈ S b, ∀ j ∈ J, ‖φ2 b j δ‖ ≤ M)
    (h1 : ∀ b, ∀ δ ∈ S b, ∀ j ∈ J, ‖φ1 b j δ + φ0 b j‖ ≤ M)
    (hw : ∀ b, ∀ δ ∈ S b, ‖φ2 b i δ‖ ≤ c * w b δ) :
    ∑ b, ∑ δ ∈ S b, ‖Sg δ‖ * (‖∏ j ∈ V, φ2 b j δ‖ * ‖∏ j ∈ J \ V, (φ1 b j δ + φ0 b j)‖)
      ≤ c * M ^ (J.card - 1) * ∑ b, ∑ δ ∈ S b, ‖Sg δ‖ * w b δ := by
  have hMp : 0 ≤ M ^ (J.card - 1) := pow_nonneg hM _
  rw [mul_sum]
  refine sum_le_sum fun b _ => ?_
  rw [mul_sum]
  refine sum_le_sum fun δ hδ => ?_
  have hp := KLIndStepB_prodV_le hV hi (φ2 b · δ) (fun j => φ1 b j δ + φ0 b j)
    (h2 b δ hδ) (h1 b δ hδ)
  calc ‖Sg δ‖ * (‖∏ j ∈ V, φ2 b j δ‖ * ‖∏ j ∈ J \ V, (φ1 b j δ + φ0 b j)‖)
      ≤ ‖Sg δ‖ * (‖φ2 b i δ‖ * M ^ (J.card - 1)) := by gcongr
    _ ≤ ‖Sg δ‖ * ((c * w b δ) * M ^ (J.card - 1)) := by gcongr; exact hw b δ hδ
    _ = c * M ^ (J.card - 1) * (‖Sg δ‖ * w b δ) := by ring

/-- (G3), abstract: `i ≠ l ∈ U` distinguished; every other factor is bounded by `M`. -/
private theorem KLIndStepB_G3 {ι X D : Type*} [DecidableEq ι] [Fintype D] {J U : Finset ι}
    (hU : U ⊆ J) {i l : ι} (hi : i ∈ U) (hl : l ∈ U) (hil : i ≠ l) (S : D → Finset X)
    (Sg : X → ℂ) (φ0 : D → ι → ℂ) (φ1 : D → ι → X → ℂ) {M c : ℝ} (hM : 0 ≤ M) (w : D → X → ℝ)
    (h0 : ∀ b, ∀ j ∈ J, ‖φ0 b j‖ ≤ M)
    (h1 : ∀ b, ∀ δ ∈ S b, ∀ j ∈ J, ‖φ1 b j δ‖ ≤ M)
    (hw : ∀ b, ∀ δ ∈ S b, ‖φ1 b i δ‖ * ‖φ1 b l δ‖ ≤ c * w b δ) :
    ∑ b, ‖∏ j ∈ J \ U, φ0 b j‖ * ‖∑ δ ∈ S b, Sg δ * ∏ j ∈ U, φ1 b j δ‖
      ≤ c * M ^ (J.card - 2) * ∑ b, ∑ δ ∈ S b, ‖Sg δ‖ * w b δ := by
  have hMp : 0 ≤ M ^ (J.card - 2) := pow_nonneg hM _
  rw [mul_sum]
  refine sum_le_sum fun b _ => ?_
  rw [mul_sum]
  calc ‖∏ j ∈ J \ U, φ0 b j‖ * ‖∑ δ ∈ S b, Sg δ * ∏ j ∈ U, φ1 b j δ‖
      ≤ ‖∏ j ∈ J \ U, φ0 b j‖ * ∑ δ ∈ S b, ‖Sg δ‖ * ‖∏ j ∈ U, φ1 b j δ‖ := by
        gcongr
        refine (norm_sum_le _ _).trans (sum_le_sum fun δ _ => ?_)
        rw [norm_mul]
    _ = ∑ δ ∈ S b, ‖Sg δ‖ * (‖∏ j ∈ J \ U, φ0 b j‖ * ‖∏ j ∈ U, φ1 b j δ‖) := by
        rw [mul_sum]
        exact sum_congr rfl fun δ _ => by ring
    _ ≤ ∑ δ ∈ S b, c * M ^ (J.card - 2) * (‖Sg δ‖ * w b δ) := by
        refine sum_le_sum fun δ hδ => ?_
        have hp := KLIndStepB_prodU_le hU hi hl hil (φ1 b · δ) (φ0 b) (h1 b δ hδ) (h0 b)
        calc ‖Sg δ‖ * (‖∏ j ∈ J \ U, φ0 b j‖ * ‖∏ j ∈ U, φ1 b j δ‖)
            ≤ ‖Sg δ‖ * (‖φ1 b i δ‖ * ‖φ1 b l δ‖ * M ^ (J.card - 2)) := by gcongr
          _ ≤ ‖Sg δ‖ * ((c * w b δ) * M ^ (J.card - 2)) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hw b δ hδ) hMp)
                (norm_nonneg _)
          _ = c * M ^ (J.card - 2) * (‖Sg δ‖ * w b δ) := by ring

end Abstract


/-! ## 3. The two sums over `b` and the slice of (G2), (G3) -/

section Sums

/-- (G2): `Σ_b Σ_{δ_r = b} |Σ^{(∅)}(δ)| (|δ_i - b|+1)^d (|a_i - b|+1)^{-d} ≤ C (g²+(1-t)) L^τ`:
the weighted sum-zero estimate (`Q = d`) on every slice, then `KLlat_pow_dim_rpow`. -/
private theorem KLIndStepB_G2sum {ι : Type} (n : ℕ) [NeZero n] (k : ℕ) {L : ι → ℕ}
    [∀ i, NeZero (L i)] {g t : ι → ℝ} {Sig : ∀ i, (Fin n → Bool) → (Fin n → Zd (k + 2) (L i)) → ℂ}
    (ht1 : ∀ i, t i < 1) (hS : SigSumZeroAbs (k + 2) n L g t Sig) {τ : ℝ} (hτ : 0 < τ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : ι) (σ : Fin n → Bool), (∀ j, σ j ≠ σ (j + 1)) →
      ∀ (r i : Fin n) (ai : Zd (k + 2) (L p)),
      ∑ b : Zd (k + 2) (L p), ∑ δ ∈ univ.filter (fun δ : Fin n → Zd (k + 2) (L p) => δ r = b),
          ‖Sig p σ δ‖
            * ((((zdistD (k + 2) (L p) (δ i - b) : ℝ) + 1) ^ (k + 2))
              * ((((zdistD (k + 2) (L p) (ai - b) : ℝ) + 1) ^ (k + 2))⁻¹))
        ≤ C * ((g p) ^ 2 + (1 - (t p))) * ((L p) : ℝ) ^ τ := by
  obtain ⟨-, -, hQ⟩ := hS
  obtain ⟨Cw, hCw, hw⟩ := hQ (k + 2) (by omega)
  refine ⟨Cw * (2 ^ (k + 2) * (1 + (((k : ℝ) + 2) + 1) ^ τ / τ)), by positivity,
    fun p σ hσ r i ai => ?_⟩
  have hLτ : 0 ≤ ((L p) : ℝ) ^ τ := Real.rpow_nonneg (Nat.cast_nonneg _) τ
  have hlat := KLlat_pow_dim_rpow (L := (L p)) k hτ ai
  have hA : 0 ≤ (g p) ^ 2 + (1 - (t p)) := by nlinarith [ht1 p, sq_nonneg (g p)]
  calc ∑ b : Zd (k + 2) (L p), ∑ δ ∈ univ.filter (fun δ : Fin n → Zd (k + 2) (L p) => δ r = b),
          ‖Sig p σ δ‖
            * ((((zdistD (k + 2) (L p) (δ i - b) : ℝ) + 1) ^ (k + 2))
              * ((((zdistD (k + 2) (L p) (ai - b) : ℝ) + 1) ^ (k + 2))⁻¹))
      ≤ ∑ b : Zd (k + 2) (L p), (Cw * ((g p) ^ 2 + (1 - (t p))))
          * ((((zdistD (k + 2) (L p) (ai - b) : ℝ) + 1) ^ (k + 2))⁻¹) := by
        refine sum_le_sum fun b _ => ?_
        have hb := (hw p σ hσ r b).2
        have hc : 0 ≤ ((((zdistD (k + 2) (L p) (ai - b) : ℝ) + 1) ^ (k + 2))⁻¹) := by positivity
        calc ∑ δ ∈ univ.filter (fun δ : Fin n → Zd (k + 2) (L p) => δ r = b),
              ‖Sig p σ δ‖
                * ((((zdistD (k + 2) (L p) (δ i - b) : ℝ) + 1) ^ (k + 2))
                  * ((((zdistD (k + 2) (L p) (ai - b) : ℝ) + 1) ^ (k + 2))⁻¹))
            ≤ ∑ δ ∈ univ.filter (fun δ : Fin n → Zd (k + 2) (L p) => δ r = b),
              (‖Sig p σ δ‖
                * ((KLmaxDist (k + 2) (L p) δ : ℝ) + 1) ^ (k + 2))
                * ((((zdistD (k + 2) (L p) (ai - b) : ℝ) + 1) ^ (k + 2))⁻¹) := by
              refine sum_le_sum fun δ hδ => ?_
              have hδr : δ r = b := (mem_filter.1 hδ).2
              have hd : (zdistD (k + 2) (L p) (δ i - b) : ℝ) ≤ KLmaxDist (k + 2) (L p) δ := by
                have := KLIndStepA_dist_le_maxDist δ i r
                rw [hδr] at this
                exact_mod_cast this
              have hpow : (((zdistD (k + 2) (L p) (δ i - b) : ℝ) + 1) ^ (k + 2))
                  ≤ ((KLmaxDist (k + 2) (L p) δ : ℝ) + 1) ^ (k + 2) := by gcongr
              calc ‖Sig p σ δ‖
                    * ((((zdistD (k + 2) (L p) (δ i - b) : ℝ) + 1) ^ (k + 2))
                      * ((((zdistD (k + 2) (L p) (ai - b) : ℝ) + 1) ^ (k + 2))⁻¹))
                  = (‖Sig p σ δ‖
                    * (((zdistD (k + 2) (L p) (δ i - b) : ℝ) + 1) ^ (k + 2)))
                    * ((((zdistD (k + 2) (L p) (ai - b) : ℝ) + 1) ^ (k + 2))⁻¹) := by ring
                _ ≤ _ := by gcongr
          _ = (∑ δ ∈ univ.filter (fun δ : Fin n → Zd (k + 2) (L p) => δ r = b),
              ‖Sig p σ δ‖
                * ((KLmaxDist (k + 2) (L p) δ : ℝ) + 1) ^ (k + 2))
                * ((((zdistD (k + 2) (L p) (ai - b) : ℝ) + 1) ^ (k + 2))⁻¹) := by rw [sum_mul]
          _ ≤ (Cw * ((g p) ^ 2 + (1 - (t p))))
                * ((((zdistD (k + 2) (L p) (ai - b) : ℝ) + 1) ^ (k + 2))⁻¹) :=
              mul_le_mul_of_nonneg_right hb hc
    _ = (Cw * ((g p) ^ 2 + (1 - (t p))))
          * ∑ b : Zd (k + 2) (L p), ((((zdistD (k + 2) (L p) (ai - b) : ℝ) + 1) ^ (k + 2))⁻¹) := by
        rw [← mul_sum]
    _ ≤ (Cw * ((g p) ^ 2 + (1 - (t p))))
          * (2 ^ (k + 2) * (1 + (((k : ℝ) + 2) + 1) ^ τ / τ) * ((L p) : ℝ) ^ τ) := by
        gcongr
    _ = _ := by ring

/-- (G3): the same with two decaying leaves, `Q = 2(d-1)` and `KLlat_pair_rpow`. -/
private theorem KLIndStepB_G3sum {ι : Type} (n : ℕ) [NeZero n] (k : ℕ) {L : ι → ℕ}
    [∀ i, NeZero (L i)] {g t : ι → ℝ} {Sig : ∀ i, (Fin n → Bool) → (Fin n → Zd (k + 2) (L i)) → ℂ}
    (ht1 : ∀ i, t i < 1) (hS : SigSumZeroAbs (k + 2) n L g t Sig) {τ : ℝ} (hτ : 0 < τ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : ι) (σ : Fin n → Bool), (∀ j, σ j ≠ σ (j + 1)) →
      ∀ (r i l : Fin n) (ai al : Zd (k + 2) (L p)),
      ∑ b : Zd (k + 2) (L p), ∑ δ ∈ univ.filter (fun δ : Fin n → Zd (k + 2) (L p) => δ r = b),
          ‖Sig p σ δ‖
            * ((((zdistD (k + 2) (L p) (δ i - b) : ℝ) + 1) ^ (k + 1)
                * (((zdistD (k + 2) (L p) (δ l - b) : ℝ) + 1) ^ (k + 1)))
              * ((((zdistD (k + 2) (L p) (ai - b) : ℝ) + 1) ^ (k + 1)
                * (((zdistD (k + 2) (L p) (al - b) : ℝ) + 1) ^ (k + 1)))⁻¹))
        ≤ C * ((g p) ^ 2 + (1 - (t p))) * ((L p) : ℝ) ^ τ := by
  obtain ⟨-, -, hQ⟩ := hS
  obtain ⟨Cw, hCw, hw⟩ := hQ (2 * (k + 1)) (by omega)
  refine ⟨Cw * (2 ^ (2 * k + 6) * (1 + (((k : ℝ) + 2) + 1) ^ τ / τ)), by positivity,
    fun p σ hσ r i l ai al => ?_⟩
  have hLτ : 0 ≤ ((L p) : ℝ) ^ τ := Real.rpow_nonneg (Nat.cast_nonneg _) τ
  have hlat := KLlat_pair_rpow (L := (L p)) k hτ ai al
  have hA : 0 ≤ (g p) ^ 2 + (1 - (t p)) := by nlinarith [ht1 p, sq_nonneg (g p)]
  calc ∑ b : Zd (k + 2) (L p), ∑ δ ∈ univ.filter (fun δ : Fin n → Zd (k + 2) (L p) => δ r = b),
          ‖Sig p σ δ‖
            * ((((zdistD (k + 2) (L p) (δ i - b) : ℝ) + 1) ^ (k + 1)
                * (((zdistD (k + 2) (L p) (δ l - b) : ℝ) + 1) ^ (k + 1)))
              * ((((zdistD (k + 2) (L p) (ai - b) : ℝ) + 1) ^ (k + 1)
                * (((zdistD (k + 2) (L p) (al - b) : ℝ) + 1) ^ (k + 1)))⁻¹))
      ≤ ∑ b : Zd (k + 2) (L p), (Cw * ((g p) ^ 2 + (1 - (t p))))
          * ((((zdistD (k + 2) (L p) (ai - b) : ℝ) + 1) ^ (k + 1)
                * (((zdistD (k + 2) (L p) (al - b) : ℝ) + 1) ^ (k + 1)))⁻¹) := by
        refine sum_le_sum fun b _ => ?_
        have hb := (hw p σ hσ r b).2
        have hc : 0 ≤ ((((zdistD (k + 2) (L p) (ai - b) : ℝ) + 1) ^ (k + 1)
                * (((zdistD (k + 2) (L p) (al - b) : ℝ) + 1) ^ (k + 1)))⁻¹) := by positivity
        calc ∑ δ ∈ univ.filter (fun δ : Fin n → Zd (k + 2) (L p) => δ r = b),
              ‖Sig p σ δ‖
                * ((((zdistD (k + 2) (L p) (δ i - b) : ℝ) + 1) ^ (k + 1)
                    * (((zdistD (k + 2) (L p) (δ l - b) : ℝ) + 1) ^ (k + 1)))
                  * ((((zdistD (k + 2) (L p) (ai - b) : ℝ) + 1) ^ (k + 1)
                    * (((zdistD (k + 2) (L p) (al - b) : ℝ) + 1) ^ (k + 1)))⁻¹))
            ≤ ∑ δ ∈ univ.filter (fun δ : Fin n → Zd (k + 2) (L p) => δ r = b),
              (‖Sig p σ δ‖
                * ((KLmaxDist (k + 2) (L p) δ : ℝ) + 1) ^ (2 * (k + 1)))
                * ((((zdistD (k + 2) (L p) (ai - b) : ℝ) + 1) ^ (k + 1)
                    * (((zdistD (k + 2) (L p) (al - b) : ℝ) + 1) ^ (k + 1)))⁻¹) := by
              refine sum_le_sum fun δ hδ => ?_
              have hδr : δ r = b := (mem_filter.1 hδ).2
              have hd1 : (zdistD (k + 2) (L p) (δ i - b) : ℝ) ≤ KLmaxDist (k + 2) (L p) δ := by
                have := KLIndStepA_dist_le_maxDist δ i r
                rw [hδr] at this
                exact_mod_cast this
              have hd2 : (zdistD (k + 2) (L p) (δ l - b) : ℝ) ≤ KLmaxDist (k + 2) (L p) δ := by
                have := KLIndStepA_dist_le_maxDist δ l r
                rw [hδr] at this
                exact_mod_cast this
              have hpow : (((zdistD (k + 2) (L p) (δ i - b) : ℝ) + 1) ^ (k + 1)
                    * (((zdistD (k + 2) (L p) (δ l - b) : ℝ) + 1) ^ (k + 1)))
                  ≤ ((KLmaxDist (k + 2) (L p) δ : ℝ) + 1) ^ (2 * (k + 1)) := by
                have h2 : ((KLmaxDist (k + 2) (L p) δ : ℝ) + 1) ^ (2 * (k + 1))
                    = ((KLmaxDist (k + 2) (L p) δ : ℝ) + 1) ^ (k + 1)
                      * ((KLmaxDist (k + 2) (L p) δ : ℝ) + 1) ^ (k + 1) := by
                  rw [← pow_add]; congr 1; ring
                rw [h2]; gcongr
              calc ‖Sig p σ δ‖
                    * ((((zdistD (k + 2) (L p) (δ i - b) : ℝ) + 1) ^ (k + 1)
                    * (((zdistD (k + 2) (L p) (δ l - b) : ℝ) + 1) ^ (k + 1)))
                  * ((((zdistD (k + 2) (L p) (ai - b) : ℝ) + 1) ^ (k + 1)
                    * (((zdistD (k + 2) (L p) (al - b) : ℝ) + 1) ^ (k + 1)))⁻¹))
                  = (‖Sig p σ δ‖
                    * ((((zdistD (k + 2) (L p) (δ i - b) : ℝ) + 1) ^ (k + 1)
                    * (((zdistD (k + 2) (L p) (δ l - b) : ℝ) + 1) ^ (k + 1)))))
                  * ((((zdistD (k + 2) (L p) (ai - b) : ℝ) + 1) ^ (k + 1)
                    * (((zdistD (k + 2) (L p) (al - b) : ℝ) + 1) ^ (k + 1)))⁻¹) := by ring
                _ ≤ _ := by gcongr
          _ = (∑ δ ∈ univ.filter (fun δ : Fin n → Zd (k + 2) (L p) => δ r = b),
              ‖Sig p σ δ‖
                * ((KLmaxDist (k + 2) (L p) δ : ℝ) + 1) ^ (2 * (k + 1)))
                * ((((zdistD (k + 2) (L p) (ai - b) : ℝ) + 1) ^ (k + 1)
                    * (((zdistD (k + 2) (L p) (al - b) : ℝ) + 1) ^ (k + 1)))⁻¹) := by rw [sum_mul]
          _ ≤ _ := mul_le_mul_of_nonneg_right hb hc
    _ = (Cw * ((g p) ^ 2 + (1 - (t p))))
          * ∑ b : Zd (k + 2) (L p), ((((zdistD (k + 2) (L p) (ai - b) : ℝ) + 1) ^ (k + 1)
                * (((zdistD (k + 2) (L p) (al - b) : ℝ) + 1) ^ (k + 1)))⁻¹) := by
        rw [← mul_sum]
    _ ≤ (Cw * ((g p) ^ 2 + (1 - (t p))))
          * (2 ^ (2 * k + 6) * (1 + (((k : ℝ) + 2) + 1) ^ τ / τ) * ((L p) : ℝ) ^ τ) := by
        gcongr
    _ = _ := by ring

end Sums


/-! ## 4. The three parts of a leaf, and the real-number bookkeeping -/

section Parts

/-- `f₀` of the leaf `s ↦ T(a, b + s)`. -/
private noncomputable def KLIndStepB_phi0 {d L : ℕ} (T : Matrix (Zd d L) (Zd d L) ℂ) (a b : Zd d L) : ℂ :=
  KLf0 (fun s => T a (b + s))

/-- `f₁(x - b)` of the leaf `s ↦ T(a, b + s)`, at the position `x = b + s`. -/
private noncomputable def KLIndStepB_phi1 {d L : ℕ} (T : Matrix (Zd d L) (Zd d L) ℂ) (a b x : Zd d L) : ℂ :=
  KLf1 (fun s => T a (b + s)) (x - b)

/-- `f₂(x - b)` of the leaf `s ↦ T(a, b + s)`, at the position `x = b + s`. -/
private noncomputable def KLIndStepB_phi2 {d L : ℕ} (T : Matrix (Zd d L) (Zd d L) ℂ) (a b x : Zd d L) : ℂ :=
  KLf2 (fun s => T a (b + s)) (x - b)

/-- `T(a, x) = f₀ + f₁ + f₂` at `x = b + s`. -/
private theorem KLIndStepB_phi_split {d L : ℕ} (T : Matrix (Zd d L) (Zd d L) ℂ) (a b x : Zd d L) :
    KLIndStepB_phi0 T a b + KLIndStepB_phi1 T a b x + KLIndStepB_phi2 T a b x = T a x := by
  have h := KLf_split (fun s => T a (b + s)) (x - b)
  simp only [add_sub_cancel] at h
  exact h

/-- The crude bound `K B_{t,0}` for each of the three parts (`KLIndStepA_crude_abs`). -/
private theorem KLIndStepB_phi_crude {ι : Type} {d : ℕ} {gmax : ℝ} {L : ι → ℕ} [∀ i, NeZero (L i)]
    {g t : ι → ℝ} {TH : ∀ i, Bool → Bool → Matrix (Zd d (L i)) (Zd d (L i)) ℂ}
    (hr : ∀ i, 3 ≤ L i ∧ 0 < g i ∧ g i ≤ gmax ∧ 0 ≤ t i ∧ t i < 1) (hTH : IndStepTH d L g t TH) :
    ∃ K : ℝ, 0 < K ∧ ∀ (p : ι) (s s' : Bool) (a b x : Zd d (L p)),
      ‖KLIndStepB_phi0 (TH p s s') a b‖ ≤ K * Bparam d (L p) (g p) (t p) 0 ∧
      ‖KLIndStepB_phi1 (TH p s s') a b x‖ ≤ K * Bparam d (L p) (g p) (t p) 0 ∧
      ‖KLIndStepB_phi2 (TH p s s') a b x‖ ≤ K * Bparam d (L p) (g p) (t p) 0 := by
  obtain ⟨K, hK, H⟩ := KLIndStepA_crude_abs hr hTH
  exact ⟨K, hK, fun p s s' a b x => H p s s' a b (x - b)⟩

/-- `(eq:f12)` for `f₁`, `f₂` at the position `x`, `d = k + 2`, loss `L^τ` (`KLIndStepA_f12_abs`). -/
private theorem KLIndStepB_phi_f12 {ι : Type} (k : ℕ) (hk : 1 ≤ k) {L : ι → ℕ} [∀ i, NeZero (L i)] {g t : ι → ℝ}
    {TH : ∀ i, Bool → Bool → Matrix (Zd (k + 2) (L i)) (Zd (k + 2) (L i)) ℂ}
    (hTH : IndStepTH (k + 2) L g t TH) (τ : ℝ) (hτ : 0 < τ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : ι) (s s' : Bool), s ≠ s' → ∀ (a b x : Zd (k + 2) (L p)),
      ‖KLIndStepB_phi1 (TH p s s') a b x‖
        ≤ C * (L p : ℝ) ^ τ * (g p ^ 2 + |1 - t p|)⁻¹
            * (((zdistD (k + 2) (L p) (x - b) : ℝ) + 1) ^ (k + 1))
            * ((((zdistD (k + 2) (L p) (a - b) : ℝ) + 1) ^ (k + 1))⁻¹) ∧
      ‖KLIndStepB_phi2 (TH p s s') a b x‖
        ≤ C * (L p : ℝ) ^ τ * (g p ^ 2 + |1 - t p|)⁻¹
            * (((zdistD (k + 2) (L p) (x - b) : ℝ) + 1) ^ (k + 2))
            * ((((zdistD (k + 2) (L p) (a - b) : ℝ) + 1) ^ (k + 2))⁻¹) := by
  obtain ⟨C, hC, H⟩ := KLIndStepA_f12_abs (by omega : 3 ≤ k + 2) hTH τ hτ
  exact ⟨C, hC, fun p s s' hss a b x => H p s s' hss a b (x - b)⟩

/-- (G2) bookkeeping: `(K₁₂ L^{τ'} A⁻¹)(2KB)^m (C₂ A L^{τ'}) ≤ C_{G2} (L^{τ'})³ B^m`. -/
private theorem KLIndStepB_arith2 {K₁₂ K C2 Ai A B Lt : ℝ} (m : ℕ) (hK₁₂ : 0 ≤ K₁₂) (hK : 0 ≤ K)
    (hC2 : 0 ≤ C2) (hB : 0 ≤ B) (hAA : Ai * A = 1) (hLt : 1 ≤ Lt) :
    (K₁₂ * Lt * Ai) * (2 * K * B) ^ m * (C2 * A * Lt)
      ≤ (K₁₂ * (2 * K) ^ m * C2) * Lt ^ 3 * B ^ m := by
  have h23 : Lt ^ 2 ≤ Lt ^ 3 := pow_le_pow_right₀ hLt (by norm_num)
  have hc : 0 ≤ K₁₂ * (2 * K) ^ m * C2 :=
    mul_nonneg (mul_nonneg hK₁₂ (pow_nonneg (by linarith) m)) hC2
  calc (K₁₂ * Lt * Ai) * (2 * K * B) ^ m * (C2 * A * Lt)
      = (K₁₂ * (2 * K) ^ m * C2) * (Ai * A) * Lt ^ 2 * B ^ m := by rw [mul_pow]; ring
    _ = (K₁₂ * (2 * K) ^ m * C2) * Lt ^ 2 * B ^ m := by rw [hAA]; ring
    _ ≤ (K₁₂ * (2 * K) ^ m * C2) * Lt ^ 3 * B ^ m := by gcongr

/-- (G3) bookkeeping: `(K₁₂ L^{τ'} A⁻¹)² (2KB)^m (C₃ A L^{τ'}) ≤ C_{G3} (L^{τ'})³ B^{m+1}`
(`A⁻¹ ≤ B`). -/
private theorem KLIndStepB_arith3 {K₁₂ K C3 Ai A B Lt : ℝ} (m : ℕ) (hK : 0 ≤ K)
    (hC3 : 0 ≤ C3) (hB : 0 ≤ B) (hLt : 0 ≤ Lt) (hAA : Ai * A = 1) (hAiB : Ai ≤ B) :
    (K₁₂ * Lt * Ai) ^ 2 * (2 * K * B) ^ m * (C3 * A * Lt)
      ≤ (K₁₂ ^ 2 * (2 * K) ^ m * C3) * Lt ^ 3 * B ^ (m + 1) := by
  calc (K₁₂ * Lt * Ai) ^ 2 * (2 * K * B) ^ m * (C3 * A * Lt)
      = (K₁₂ ^ 2 * (2 * K) ^ m * C3) * Lt ^ 3 * (Ai * A) * Ai * B ^ m := by
        rw [mul_pow, mul_pow]; ring
    _ = (K₁₂ ^ 2 * (2 * K) ^ m * C3) * Lt ^ 3 * Ai * B ^ m := by rw [hAA]; ring
    _ ≤ (K₁₂ ^ 2 * (2 * K) ^ m * C3) * Lt ^ 3 * B * B ^ m := by gcongr
    _ = (K₁₂ ^ 2 * (2 * K) ^ m * C3) * Lt ^ 3 * B ^ (m + 1) := by ring

end Parts


/-! ## 5. Case (ii) of `(eq:ind-step-bound)`: the alternating case -/

section Main

/-- The final summation: `Σ_b (Σ_{U∈T} P_U(b) + Σ_{V∈T'} Q_V(b))`. -/
private theorem KLIndStepB_combine {ι D : Type*} [Fintype D] (T T' : Finset ι) (P Q : ι → D → ℝ)
    (cP cQ : ℝ) (hP : ∀ U ∈ T, ∑ b, P U b ≤ cP) (hQ : ∀ V ∈ T', ∑ b, Q V b ≤ cQ) :
    ∑ b, (∑ U ∈ T, P U b + ∑ V ∈ T', Q V b) ≤ T.card * cP + T'.card * cQ := by
  rw [sum_add_distrib]
  have e1 : ∑ b, ∑ U ∈ T, P U b = ∑ U ∈ T, ∑ b, P U b := sum_comm
  have e2 : ∑ b, ∑ V ∈ T', Q V b = ∑ V ∈ T', ∑ b, Q V b := sum_comm
  rw [e1, e2]
  refine add_le_add ?_ ?_
  · calc ∑ U ∈ T, ∑ b, P U b ≤ ∑ _U ∈ T, cP := sum_le_sum hP
      _ = T.card * cP := by rw [sum_const, nsmul_eq_mul]
  · calc ∑ V ∈ T', ∑ b, Q V b ≤ ∑ _V ∈ T', cQ := sum_le_sum hQ
      _ = T'.card * cQ := by rw [sum_const, nsmul_eq_mul]


/-- **Case (ii) of `(eq:ind-step-bound)` over abstract data** (every alternating `σ`, every root `r`; the
pin's inequality `IndStepAbs` with `σ_r ≠ σ_{r+1}` automatic).  With `b = δ_r`, `s_j = δ_j - b` and
`f_j(s) = TH(a_j, b + s) = f₀ + f₁ + f₂`, the product `∏_{j≠r} f_j` is expanded in the positions `V`
of `f₂` and `U` of `f₁` (`Finset.prod_add`).  (G0) `V = U = ∅`: the signed slice estimate times one row
sum, no loss; (G1) `V = ∅`, `|U| = 1`: exactly `0` (`KLIndStepA_slice_vanish`, the reflection of
`SigSumZeroAbs`); (G2) `V ≠ ∅`: one `f₂` factor with `(eq:f12)`, the other factors crude,
`SigSumZeroAbs` with `Q = d`, `KLlat_pow_dim_rpow`; (G3) `V = ∅`, `|U| ≥ 2`: two `f₁` factors,
`Q = 2d - 2`, `KLlat_pair_rpow`, `(g²+|1-t|)⁻¹ ≤ B_{t,0}`.  The loss `L^τ` is `(L^{τ/3})³`;
`C = C(d, n, τ)` and the constants of the bundles. -/
private theorem KLIndStepB_alt_abs {ι : Type} {d : ℕ} {gmax : ℝ} (n : ℕ) [NeZero n] (hd : 3 ≤ d)
    (hn : 3 ≤ n) {L : ι → ℕ} [∀ i, NeZero (L i)] {g t : ι → ℝ}
    {Sig : ∀ i, (Fin n → Bool) → (Fin n → Zd d (L i)) → ℂ}
    {TH : ∀ i, Bool → Bool → Matrix (Zd d (L i)) (Zd d (L i)) ℂ}
    (hr : ∀ i, 3 ≤ L i ∧ 0 < g i ∧ g i ≤ gmax ∧ 0 ≤ t i ∧ t i < 1) (hTH : IndStepTH d L g t TH)
    (hS : SigSumZeroAbs d n L g t Sig) :
    ∀ τ : ℝ, 0 < τ → ∃ C : ℝ, 0 < C ∧ ∀ (p : ι) (σ : Fin n → Bool) (r : Fin n),
      (∀ j, σ j ≠ σ (j + 1)) → ∀ a : Fin n → Zd d (L p),
      ∑ b : Zd d (L p), ‖∑ δ ∈ univ.filter (fun δ : Fin n → Zd d (L p) => δ r = b),
          Sig p σ δ * ∏ i ∈ univ.erase r, TH p (σ i) (σ (i + 1)) (a i) (δ i)‖
        ≤ C * (L p : ℝ) ^ τ * (Bparam d (L p) (g p) (t p) 0) ^ (n - 2) := by
  intro τ hτ
  obtain ⟨k, rfl⟩ : ∃ k, d = k + 2 := ⟨d - 2, by omega⟩
  have hk : 1 ≤ k := by omega
  have hτ' : 0 < τ / 3 := by positivity
  obtain ⟨K, hK, hcr⟩ := KLIndStepB_phi_crude hr hTH
  obtain ⟨K₁₂, hK₁₂, h12⟩ := KLIndStepB_phi_f12 k hk hTH (τ / 3) hτ'
  obtain ⟨hrefl, -, hQ⟩ := id hS
  obtain ⟨Cs, hCs, hsig⟩ := hQ 0 (Nat.zero_le _)
  have ht1 : ∀ i, t i < 1 := fun i => (hr i).2.2.2.2
  obtain ⟨C2, hC2, hG2⟩ := KLIndStepB_G2sum n k ht1 hS hτ'
  obtain ⟨C3, hC3, hG3⟩ := KLIndStepB_G3sum n k ht1 hS hτ'
  obtain ⟨Cg0, hCg0⟩ : ∃ x : ℝ, x = Cs * (2 * K) ^ (n - 2) := ⟨_, rfl⟩
  obtain ⟨Cg3, hCg3⟩ : ∃ x : ℝ, x = K₁₂ ^ 2 * (2 * K) ^ (n - 3) * C3 := ⟨_, rfl⟩
  obtain ⟨Cg2, hCg2⟩ : ∃ x : ℝ, x = K₁₂ * (2 * K) ^ (n - 2) * C2 := ⟨_, rfl⟩
  have hCg0' : 0 < Cg0 := by rw [hCg0]; positivity
  have hCg3' : 0 < Cg3 := by rw [hCg3]; positivity
  have hCg2' : 0 < Cg2 := by rw [hCg2]; positivity
  refine ⟨2 ^ (n - 1) * (Cg0 + Cg3 + Cg2), by positivity, fun p σ r hσ a => ?_⟩
  obtain ⟨hL3, hg0, hg1, ht0, ht1p⟩ := hr p
  have h1t : 0 < 1 - (t p) := by linarith
  have hApos : 0 < (g p) ^ 2 + (1 - (t p)) := by positivity
  have habs : |1 - (t p)| = 1 - (t p) := abs_of_pos h1t
  have hAA : ((g p) ^ 2 + |1 - (t p)|)⁻¹ * ((g p) ^ 2 + (1 - (t p))) = 1 := by
    rw [habs]; exact inv_mul_cancel₀ hApos.ne'
  have hAiB : ((g p) ^ 2 + |1 - (t p)|)⁻¹ ≤ Bparam (k + 2) (L p) (g p) (t p) 0 := KLlat_inv_le_Bparam (t p)
  have hB0 : 0 ≤ Bparam (k + 2) (L p) (g p) (t p) 0 := KLIndStepA_Bparam_nonneg _ _
  have hL1 : (1 : ℝ) ≤ (L p) := by
    exact_mod_cast (by omega : 1 ≤ (L p))
  have hLt1 : 1 ≤ ((L p) : ℝ) ^ (τ / 3) := Real.one_le_rpow hL1 hτ'.le
  have hLτ : 1 ≤ ((L p) : ℝ) ^ τ := Real.one_le_rpow hL1 hτ.le
  have hLt3 : (((L p) : ℝ) ^ (τ / 3)) ^ 3 = ((L p) : ℝ) ^ τ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
    congr 1
    push_cast
    ring
  have hJc : (univ.erase r).card = n - 1 := by
    rw [card_erase_of_mem (mem_univ r), card_univ, Fintype.card_fin]
  -- the three parts replace the leaves
  set T : Fin n → Matrix (Zd (k + 2) (L p)) (Zd (k + 2) (L p)) ℂ := fun j => TH p (σ j) (σ (j + 1)) with hT
  have hrew : ∀ (b : Zd (k + 2) (L p)) (δ : Fin n → Zd (k + 2) (L p)),
      ∏ i ∈ univ.erase r,
          TH p (σ i) (σ (i + 1)) (a i) (δ i)
        = ∏ j ∈ univ.erase r, (KLIndStepB_phi0 (T j) (a j) b + KLIndStepB_phi1 (T j) (a j) b (δ j)
            + KLIndStepB_phi2 (T j) (a j) b (δ j)) := by
    intro b δ
    refine prod_congr rfl fun j _ => ?_
    exact (KLIndStepB_phi_split (T j) (a j) b (δ j)).symm
  have hslice : ∀ b : Zd (k + 2) (L p),
      ‖∑ δ ∈ univ.filter (fun δ : Fin n → Zd (k + 2) (L p) => δ r = b),
          Sig p σ δ *
            ∏ i ∈ univ.erase r,
              TH p (σ i) (σ (i + 1)) (a i) (δ i)‖
        ≤ ∑ U ∈ (univ.erase r).powerset,
            (‖∏ j ∈ univ.erase r \ U, KLIndStepB_phi0 (T j) (a j) b‖ *
              ‖∑ δ ∈ univ.filter (fun δ : Fin n → Zd (k + 2) (L p) => δ r = b),
                Sig p σ δ *
                  ∏ j ∈ U, KLIndStepB_phi1 (T j) (a j) b (δ j)‖)
          + ∑ V ∈ (univ.erase r).powerset.erase ∅,
            ∑ δ ∈ univ.filter (fun δ : Fin n → Zd (k + 2) (L p) => δ r = b),
              ‖Sig p σ δ‖ *
                (‖∏ j ∈ V, KLIndStepB_phi2 (T j) (a j) b (δ j)‖ *
                  ‖∏ j ∈ univ.erase r \ V,
                    (KLIndStepB_phi1 (T j) (a j) b (δ j) + KLIndStepB_phi0 (T j) (a j) b)‖) := by
    intro b
    have h := KLIndStepB_expand_norm (univ.erase r)
      (univ.filter (fun δ : Fin n → Zd (k + 2) (L p) => δ r = b))
      (fun δ => Sig p σ δ)
      (fun j => KLIndStepB_phi0 (T j) (a j) b) (fun j δ => KLIndStepB_phi1 (T j) (a j) b (δ j))
      (fun j δ => KLIndStepB_phi2 (T j) (a j) b (δ j))
    refine le_trans (le_of_eq ?_) h
    congr 1
    refine sum_congr rfl fun δ _ => ?_
    rw [hrew b δ]
  have hKB : 0 ≤ K * Bparam (k + 2) (L p) (g p) (t p) 0 := by positivity
  have hMge : K * Bparam (k + 2) (L p) (g p) (t p) 0 ≤ 2 * K * Bparam (k + 2) (L p) (g p) (t p) 0 := by
    nlinarith
  have hM : 0 ≤ 2 * K * Bparam (k + 2) (L p) (g p) (t p) 0 := by positivity
  have hJpos : 0 < (univ.erase r).card := by rw [hJc]; omega
  -- every factor of every pattern is `≤ 2 K B_{t,0}` (`KLf_crude_bound`)
  have b0 : ∀ b : Zd (k + 2) (L p), ∀ j ∈ univ.erase r,
      ‖KLIndStepB_phi0 (T j) (a j) b‖ ≤ 2 * K * Bparam (k + 2) (L p) (g p) (t p) 0 :=
    fun b j _ => ((hcr p (σ j) (σ (j + 1)) (a j) b 0).1).trans hMge
  have b1 : ∀ b : Zd (k + 2) (L p),
      ∀ δ ∈ univ.filter (fun δ : Fin n → Zd (k + 2) (L p) => δ r = b), ∀ j ∈ univ.erase r,
      ‖KLIndStepB_phi1 (T j) (a j) b (δ j)‖ ≤ 2 * K * Bparam (k + 2) (L p) (g p) (t p) 0 :=
    fun b δ _ j _ => ((hcr p (σ j) (σ (j + 1)) (a j) b (δ j)).2.1).trans hMge
  have b2 : ∀ b : Zd (k + 2) (L p),
      ∀ δ ∈ univ.filter (fun δ : Fin n → Zd (k + 2) (L p) => δ r = b), ∀ j ∈ univ.erase r,
      ‖KLIndStepB_phi2 (T j) (a j) b (δ j)‖ ≤ 2 * K * Bparam (k + 2) (L p) (g p) (t p) 0 :=
    fun b δ _ j _ => ((hcr p (σ j) (σ (j + 1)) (a j) b (δ j)).2.2).trans hMge
  have bρ : ∀ b : Zd (k + 2) (L p),
      ∀ δ ∈ univ.filter (fun δ : Fin n → Zd (k + 2) (L p) => δ r = b), ∀ j ∈ univ.erase r,
      ‖KLIndStepB_phi1 (T j) (a j) b (δ j) + KLIndStepB_phi0 (T j) (a j) b‖
        ≤ 2 * K * Bparam (k + 2) (L p) (g p) (t p) 0 := by
    intro b δ _ j _
    refine (norm_add_le _ _).trans ?_
    have e1 := (hcr p (σ j) (σ (j + 1)) (a j) b (δ j)).2.1
    have e0 := (hcr p (σ j) (σ (j + 1)) (a j) b (δ j)).1
    linarith
  -- the groups with at least one `f₂` (G2)
  have hQV : ∀ V ∈ (univ.erase r).powerset.erase ∅,
      ∑ b : Zd (k + 2) (L p),
        ∑ δ ∈ univ.filter (fun δ : Fin n → Zd (k + 2) (L p) => δ r = b),
          ‖Sig p σ δ‖ *
            (‖∏ j ∈ V, KLIndStepB_phi2 (T j) (a j) b (δ j)‖ *
              ‖∏ j ∈ univ.erase r \ V,
                (KLIndStepB_phi1 (T j) (a j) b (δ j) + KLIndStepB_phi0 (T j) (a j) b)‖)
        ≤ Cg2 * ((L p) : ℝ) ^ τ * (Bparam (k + 2) (L p) (g p) (t p) 0) ^ (n - 2) := by
    intro V hV
    obtain ⟨hVne, hVp⟩ := mem_erase.1 hV
    have hVJ : V ⊆ univ.erase r := mem_powerset.1 hVp
    obtain ⟨i, hi⟩ : V.Nonempty := nonempty_iff_ne_empty.2 hVne
    have hw : ∀ b : Zd (k + 2) (L p),
        ∀ δ ∈ univ.filter (fun δ : Fin n → Zd (k + 2) (L p) => δ r = b),
        ‖KLIndStepB_phi2 (T i) (a i) b (δ i)‖
          ≤ (K₁₂ * ((L p) : ℝ) ^ (τ / 3) * ((g p) ^ 2 + |1 - (t p)|)⁻¹)
            * ((((zdistD (k + 2) (L p) (δ i - b) : ℝ) + 1) ^ (k + 2))
              * ((((zdistD (k + 2) (L p) (a i - b) : ℝ) + 1) ^ (k + 2))⁻¹)) := by
      intro b δ _
      refine ((h12 p (σ i) (σ (i + 1)) (hσ i) (a i) b (δ i)).2).trans (le_of_eq ?_)
      ring
    have hG := KLIndStepB_G2 hVJ hi
      (fun b => univ.filter (fun δ : Fin n → Zd (k + 2) (L p) => δ r = b))
      (fun δ => Sig p σ δ)
      (fun b j => KLIndStepB_phi0 (T j) (a j) b) (fun b j δ => KLIndStepB_phi1 (T j) (a j) b (δ j))
      (fun b j δ => KLIndStepB_phi2 (T j) (a j) b (δ j))
      (M := 2 * K * Bparam (k + 2) (L p) (g p) (t p) 0)
      (c := K₁₂ * ((L p) : ℝ) ^ (τ / 3) * ((g p) ^ 2 + |1 - (t p)|)⁻¹) hM
      (fun b δ => (((zdistD (k + 2) (L p) (δ i - b) : ℝ) + 1) ^ (k + 2))
        * ((((zdistD (k + 2) (L p) (a i - b) : ℝ) + 1) ^ (k + 2))⁻¹)) b2 bρ hw
    have hm : (univ.erase r).card - 1 = n - 2 := by rw [hJc]; omega
    rw [hm] at hG
    refine hG.trans ?_
    calc K₁₂ * ((L p) : ℝ) ^ (τ / 3) * ((g p) ^ 2 + |1 - (t p)|)⁻¹
          * (2 * K * Bparam (k + 2) (L p) (g p) (t p) 0) ^ (n - 2)
          * ∑ b : Zd (k + 2) (L p),
            ∑ δ ∈ univ.filter (fun δ : Fin n → Zd (k + 2) (L p) => δ r = b),
              ‖Sig p σ δ‖
                * ((((zdistD (k + 2) (L p) (δ i - b) : ℝ) + 1) ^ (k + 2))
                  * ((((zdistD (k + 2) (L p) (a i - b) : ℝ) + 1) ^ (k + 2))⁻¹))
        ≤ K₁₂ * ((L p) : ℝ) ^ (τ / 3) * ((g p) ^ 2 + |1 - (t p)|)⁻¹
            * (2 * K * Bparam (k + 2) (L p) (g p) (t p) 0) ^ (n - 2)
            * (C2 * ((g p) ^ 2 + (1 - (t p))) * ((L p) : ℝ) ^ (τ / 3)) := by
          gcongr
          exact hG2 p σ hσ r i (a i)
      _ ≤ (K₁₂ * (2 * K) ^ (n - 2) * C2) * (((L p) : ℝ) ^ (τ / 3)) ^ 3
            * (Bparam (k + 2) (L p) (g p) (t p) 0) ^ (n - 2) :=
          KLIndStepB_arith2 (n - 2) hK₁₂.le hK.le hC2.le hB0 hAA hLt1
      _ = Cg2 * ((L p) : ℝ) ^ τ * (Bparam (k + 2) (L p) (g p) (t p) 0) ^ (n - 2) := by
          rw [hCg2, hLt3]
  -- the groups with no `f₂`: (G0) all `f₀`, (G1) one `f₁`, (G3) at least two `f₁`
  have hPU : ∀ U ∈ (univ.erase r).powerset,
      ∑ b : Zd (k + 2) (L p),
        (‖∏ j ∈ univ.erase r \ U, KLIndStepB_phi0 (T j) (a j) b‖ *
          ‖∑ δ ∈ univ.filter (fun δ : Fin n → Zd (k + 2) (L p) => δ r = b),
            Sig p σ δ *
              ∏ j ∈ U, KLIndStepB_phi1 (T j) (a j) b (δ j)‖)
        ≤ (Cg0 + Cg3) * ((L p) : ℝ) ^ τ * (Bparam (k + 2) (L p) (g p) (t p) 0) ^ (n - 2) := by
    intro U hU
    have hUJ : U ⊆ univ.erase r := mem_powerset.1 hU
    rcases U.eq_empty_or_nonempty with hU0 | hUne
    · -- (G0)
      subst hU0
      obtain ⟨j0, hj0⟩ := card_pos.1 hJpos
      have hrow : ∑ b : Zd (k + 2) (L p), ‖KLIndStepB_phi0 (T j0) (a j0) b‖ ≤ (1 - (t p))⁻¹ := by
        have := hTH.rowSum p (σ j0) (σ (j0 + 1)) (hσ j0) (a j0)
        refine le_of_eq_of_le (sum_congr rfl fun b _ => ?_) this
        change ‖TH p (σ j0) (σ (j0 + 1)) (a j0) (b + 0)‖ = _
        rw [add_zero]
      have hG := KLIndStepB_G0 hj0
        (fun b => univ.filter (fun δ : Fin n → Zd (k + 2) (L p) => δ r = b))
        (fun δ => Sig p σ δ)
        (fun b j => KLIndStepB_phi0 (T j) (a j) b) (M := 2 * K * Bparam (k + 2) (L p) (g p) (t p) 0)
        (Cs := Cs) (τ0 := 1 - (t p)) hM hCs.le h1t b0 (fun b => (hsig p σ hσ r b).1) hrow
      have hm : (univ.erase r).card - 1 = n - 2 := by rw [hJc]; omega
      rw [hm] at hG
      simp only [sdiff_empty, prod_empty, mul_one]
      refine hG.trans ?_
      calc Cs * (2 * K * Bparam (k + 2) (L p) (g p) (t p) 0) ^ (n - 2)
          = Cg0 * (Bparam (k + 2) (L p) (g p) (t p) 0) ^ (n - 2) := by rw [hCg0, mul_pow]; ring
        _ ≤ (Cg0 + Cg3) * ((L p) : ℝ) ^ τ * (Bparam (k + 2) (L p) (g p) (t p) 0) ^ (n - 2) := by
            have : Cg0 ≤ (Cg0 + Cg3) * ((L p) : ℝ) ^ τ := by
              nlinarith [mul_le_mul_of_nonneg_left hLτ (by positivity : 0 ≤ Cg0 + Cg3)]
            gcongr
    · by_cases hU1 : U.card = 1
      · -- (G1)
        obtain ⟨i, rfl⟩ := card_eq_one.1 hU1
        have hz : ∀ b : Zd (k + 2) (L p),
            ∑ δ ∈ univ.filter (fun δ : Fin n → Zd (k + 2) (L p) => δ r = b),
              Sig p σ δ *
                ∏ j ∈ {i}, KLIndStepB_phi1 (T j) (a j) b (δ j) = 0 := by
          intro b
          simp only [prod_singleton]
          exact KLIndStepA_slice_vanish (fun δ => Sig p σ δ) (fun c δ => hrefl p σ hσ c δ) r i b
            (fun s => TH p (σ i) (σ (i + 1)) (a i) (b + s))
        simp only [hz, norm_zero, mul_zero, sum_const_zero]
        positivity
      · -- (G3)
        have h2 : 1 < U.card := by
          have := hUne.card_pos
          omega
        obtain ⟨i, hi, l, hl, hil⟩ := one_lt_card.1 h2
        have hw : ∀ b : Zd (k + 2) (L p),
            ∀ δ ∈ univ.filter (fun δ : Fin n → Zd (k + 2) (L p) => δ r = b),
            ‖KLIndStepB_phi1 (T i) (a i) b (δ i)‖ * ‖KLIndStepB_phi1 (T l) (a l) b (δ l)‖
              ≤ (K₁₂ * ((L p) : ℝ) ^ (τ / 3) * ((g p) ^ 2 + |1 - (t p)|)⁻¹) ^ 2
                * ((((zdistD (k + 2) (L p) (δ i - b) : ℝ) + 1) ^ (k + 1)
                    * (((zdistD (k + 2) (L p) (δ l - b) : ℝ) + 1) ^ (k + 1)))
                  * ((((zdistD (k + 2) (L p) (a i - b) : ℝ) + 1) ^ (k + 1)
                    * (((zdistD (k + 2) (L p) (a l - b) : ℝ) + 1) ^ (k + 1)))⁻¹)) := by
          intro b δ _
          have e1 := (h12 p (σ i) (σ (i + 1)) (hσ i) (a i) b (δ i)).1
          have e2 := (h12 p (σ l) (σ (l + 1)) (hσ l) (a l) b (δ l)).1
          calc ‖KLIndStepB_phi1 (T i) (a i) b (δ i)‖ * ‖KLIndStepB_phi1 (T l) (a l) b (δ l)‖
              ≤ (K₁₂ * ((L p) : ℝ) ^ (τ / 3) * ((g p) ^ 2 + |1 - (t p)|)⁻¹
                  * (((zdistD (k + 2) (L p) (δ i - b) : ℝ) + 1) ^ (k + 1))
                  * ((((zdistD (k + 2) (L p) (a i - b) : ℝ) + 1) ^ (k + 1))⁻¹))
                * (K₁₂ * ((L p) : ℝ) ^ (τ / 3) * ((g p) ^ 2 + |1 - (t p)|)⁻¹
                  * (((zdistD (k + 2) (L p) (δ l - b) : ℝ) + 1) ^ (k + 1))
                  * ((((zdistD (k + 2) (L p) (a l - b) : ℝ) + 1) ^ (k + 1))⁻¹)) :=
                mul_le_mul e1 e2 (norm_nonneg _) (by positivity)
            _ = _ := by rw [mul_inv]; ring
        have hG := KLIndStepB_G3 hUJ hi hl hil
          (fun b => univ.filter (fun δ : Fin n → Zd (k + 2) (L p) => δ r = b))
          (fun δ => Sig p σ δ)
          (fun b j => KLIndStepB_phi0 (T j) (a j) b) (fun b j δ => KLIndStepB_phi1 (T j) (a j) b (δ j))
          (M := 2 * K * Bparam (k + 2) (L p) (g p) (t p) 0)
          (c := (K₁₂ * ((L p) : ℝ) ^ (τ / 3) * ((g p) ^ 2 + |1 - (t p)|)⁻¹) ^ 2) hM
          (fun b δ => ((((zdistD (k + 2) (L p) (δ i - b) : ℝ) + 1) ^ (k + 1)
                    * (((zdistD (k + 2) (L p) (δ l - b) : ℝ) + 1) ^ (k + 1)))
                  * ((((zdistD (k + 2) (L p) (a i - b) : ℝ) + 1) ^ (k + 1)
                    * (((zdistD (k + 2) (L p) (a l - b) : ℝ) + 1) ^ (k + 1)))⁻¹))) b0 b1 hw
        have hm : (univ.erase r).card - 2 = n - 3 := by rw [hJc]; omega
        rw [hm] at hG
        refine hG.trans ?_
        have hn2 : n - 3 + 1 = n - 2 := by omega
        calc (K₁₂ * ((L p) : ℝ) ^ (τ / 3) * ((g p) ^ 2 + |1 - (t p)|)⁻¹) ^ 2
              * (2 * K * Bparam (k + 2) (L p) (g p) (t p) 0) ^ (n - 3)
              * ∑ b : Zd (k + 2) (L p),
                ∑ δ ∈ univ.filter (fun δ : Fin n → Zd (k + 2) (L p) => δ r = b),
                  ‖Sig p σ δ‖
                    * ((((zdistD (k + 2) (L p) (δ i - b) : ℝ) + 1) ^ (k + 1)
                        * (((zdistD (k + 2) (L p) (δ l - b) : ℝ) + 1) ^ (k + 1)))
                      * ((((zdistD (k + 2) (L p) (a i - b) : ℝ) + 1) ^ (k + 1)
                        * (((zdistD (k + 2) (L p) (a l - b) : ℝ) + 1) ^ (k + 1)))⁻¹))
            ≤ (K₁₂ * ((L p) : ℝ) ^ (τ / 3) * ((g p) ^ 2 + |1 - (t p)|)⁻¹) ^ 2
                * (2 * K * Bparam (k + 2) (L p) (g p) (t p) 0) ^ (n - 3)
                * (C3 * ((g p) ^ 2 + (1 - (t p))) * ((L p) : ℝ) ^ (τ / 3)) := by
              gcongr
              exact hG3 p σ hσ r i l (a i) (a l)
          _ ≤ (K₁₂ ^ 2 * (2 * K) ^ (n - 3) * C3) * (((L p) : ℝ) ^ (τ / 3)) ^ 3
                * (Bparam (k + 2) (L p) (g p) (t p) 0) ^ (n - 3 + 1) :=
              KLIndStepB_arith3 (n - 3) hK.le hC3.le hB0 (by positivity) hAA hAiB
          _ = Cg3 * ((L p) : ℝ) ^ τ * (Bparam (k + 2) (L p) (g p) (t p) 0) ^ (n - 2) := by
              rw [hCg3, hLt3, hn2]
          _ ≤ (Cg0 + Cg3) * ((L p) : ℝ) ^ τ * (Bparam (k + 2) (L p) (g p) (t p) 0) ^ (n - 2) := by
              gcongr
              linarith
  -- the sum over the patterns
  have hfin := KLIndStepB_combine (univ.erase r).powerset ((univ.erase r).powerset.erase ∅) _ _
    ((Cg0 + Cg3) * ((L p) : ℝ) ^ τ * (Bparam (k + 2) (L p) (g p) (t p) 0) ^ (n - 2))
    (Cg2 * ((L p) : ℝ) ^ τ * (Bparam (k + 2) (L p) (g p) (t p) 0) ^ (n - 2)) hPU hQV
  refine (sum_le_sum fun b _ => hslice b).trans (hfin.trans ?_)
  have hTc : (((univ.erase r).powerset.card : ℕ) : ℝ) = 2 ^ (n - 1) := by
    rw [card_powerset, hJc]; push_cast; ring
  have hTc' : ((((univ.erase r).powerset.erase ∅).card : ℕ) : ℝ) ≤ 2 ^ (n - 1) := by
    have := card_erase_le (s := (univ.erase r).powerset) (a := ∅)
    rw [card_powerset, hJc] at this
    exact_mod_cast this
  rw [hTc]
  have hX : 0 ≤ Cg2 * ((L p) : ℝ) ^ τ * (Bparam (k + 2) (L p) (g p) (t p) 0) ^ (n - 2) := by positivity
  calc 2 ^ (n - 1) * ((Cg0 + Cg3) * ((L p) : ℝ) ^ τ * (Bparam (k + 2) (L p) (g p) (t p) 0) ^ (n - 2))
        + (((univ.erase r).powerset.erase ∅).card : ℝ)
          * (Cg2 * ((L p) : ℝ) ^ τ * (Bparam (k + 2) (L p) (g p) (t p) 0) ^ (n - 2))
      ≤ 2 ^ (n - 1) * ((Cg0 + Cg3) * ((L p) : ℝ) ^ τ * (Bparam (k + 2) (L p) (g p) (t p) 0) ^ (n - 2))
        + 2 ^ (n - 1) * (Cg2 * ((L p) : ℝ) ^ τ * (Bparam (k + 2) (L p) (g p) (t p) 0) ^ (n - 2)) := by
        gcongr
    _ = 2 ^ (n - 1) * (Cg0 + Cg3 + Cg2) * ((L p) : ℝ) ^ τ
          * (Bparam (k + 2) (L p) (g p) (t p) 0) ^ (n - 2) := by ring


variable {d : ℕ} {κ gmax : ℝ}

/-- **`KLindStep_alt`**: the pin's inequality (`KLindStepAt`, with its quantifier order
`∀ τ, ∃ C, ∀ p σ r, … → ∀ a`) for every alternating `σ` and every root `r` (`σ_r ≠ σ_{r+1}` is
automatic): the band instance of case (ii) over the bundles (`indStepTH_band`, `sigSumZeroAbs_band`). -/
theorem KLindStep_alt (n : ℕ) [NeZero n] (hd : 3 ≤ d) (hn : 3 ≤ n) (hκ : 0 < κ)
    (hg : 0 < gmax) (hPT : KLPT d κ gmax) :
    ∀ τ : ℝ, 0 < τ → ∃ C : ℝ, 0 < C ∧ ∀ (p : KLPar κ gmax) (σ : Fin n → Bool) (r : Fin n),
      (∀ j, σ j ≠ σ (j + 1)) → ∀ a : Fin n → Zd d p.L,
      ∑ b : Zd d p.L, ‖∑ δ ∈ univ.filter (fun δ : Fin n → Zd d p.L => δ r = b),
          KLSigmaPi d p.L p.g (mSigma p.E) p.t σ ∅ δ *
            ∏ i ∈ univ.erase r,
              thetaEdge d p.L p.g (mSigma p.E) p.t (σ i) (σ (i + 1)) (a i) (δ i)‖
        ≤ C * (p.L : ℝ) ^ τ * (Bparam d p.L p.g p.t 0) ^ (n - 2) :=
  KLIndStepB_alt_abs n hd hn (fun p : KLPar κ gmax => ⟨p.hL, p.hg0, p.hg1, p.ht0, p.ht1⟩)
    (indStepTH_band hκ hPT) (sigSumZeroAbs_band n hd hn hκ hg)

end Main

/-! ## 6. The pin `KLindStepPin` -/

section Glue

/-- **`indStepAbs_of`** (T2365, K09a): the induction step `(eq:ind-step-bound)` over abstract data.
From the leaf bundle `IndStepTH` (properties 5, 5', 6, 7, 8, translation, row sum), the molecule decay
`SigDecayAbs` and the sum-zero interface `SigSumZeroAbs`, with the parameter range of `KLPar`.  The
case split is on `σ` alternating (`KLIndStepB_alt_abs`, case (ii)) or not
(`KLIndStepA_nonAlt_abs`, case (i), no loss needed); `C = C_alt + C_nonAlt`. -/
theorem indStepAbs_of (d n : ℕ) [NeZero n] (gmax : ℝ) {ι : Type} (L : ι → ℕ) [∀ i, NeZero (L i)]
    (g t : ι → ℝ) (Sig : ∀ i, (Fin n → Bool) → (Fin n → Zd d (L i)) → ℂ)
    (TH : ∀ i, Bool → Bool → Matrix (Zd d (L i)) (Zd d (L i)) ℂ) (hd : 3 ≤ d) (hn : 3 ≤ n)
    (hr : ∀ i, 3 ≤ L i ∧ 0 < g i ∧ g i ≤ gmax ∧ 0 ≤ t i ∧ t i < 1) (hTH : IndStepTH d L g t TH)
    (hD : SigDecayAbs d n L Sig) (hS : SigSumZeroAbs d n L g t Sig) :
    IndStepAbs d n L (fun i => Bparam d (L i) (g i) (t i) 0) Sig TH := by
  intro τ hτ
  obtain ⟨C₁, hC₁, H₁⟩ := KLIndStepB_alt_abs n hd hn hr hTH hS τ hτ
  obtain ⟨C₂, hC₂, H₂⟩ := KLIndStepA_nonAlt_abs n hd hr hTH hD
  refine ⟨C₁ + C₂, by positivity, fun p σ r hrσ a => ?_⟩
  have hB : 0 ≤ (Bparam d (L p) (g p) (t p) 0) ^ (n - 2) :=
    pow_nonneg (KLIndStepA_Bparam_nonneg _ _) _
  have hLτ : 1 ≤ (L p : ℝ) ^ τ :=
    Real.one_le_rpow (by exact_mod_cast (by have := (hr p).1; omega : 1 ≤ L p)) hτ.le
  by_cases hσ : ∀ j, σ j ≠ σ (j + 1)
  · refine (H₁ p σ r hσ a).trans ?_
    nlinarith [mul_nonneg (mul_nonneg hC₂.le (zero_le_one.trans hLτ)) hB]
  · push Not at hσ
    obtain ⟨j, hj⟩ := hσ
    refine (H₂ p σ j r (fun h => hrσ (h ▸ hj)) hj a).trans ?_
    nlinarith [mul_nonneg hC₂.le hB, mul_nonneg hC₁.le hB, mul_nonneg (mul_nonneg hC₁.le hB) (sub_nonneg.2 hLτ),
      mul_nonneg (mul_nonneg hC₂.le hB) (sub_nonneg.2 hLτ)]

/-- **`KLindStepAt_holds`** (target 3): the route pin `(eq:ind-step-bound)` at `(d, n, κ, gmax)`,
`3 ≤ d`, `3 ≤ n`, from the local propagator shapes `KLPT d κ gmax` (`KLShort` is `KLShort_holds`):
`indStepAbs_of` at the band bundles (`indStepTH_band`, `sigDecayAbs_band`, `sigSumZeroAbs_band`);
`C` depends on `d, n, κ, gmax, τ` only. -/
theorem KLindStepAt_holds (d n : ℕ) [NeZero n] (κ gmax : ℝ) (hd : 3 ≤ d) (hn : 3 ≤ n)
    (hκ : 0 < κ) (hg : 0 < gmax) (hPT : KLPT d κ gmax) : KLindStepAt d n κ gmax :=
  (KLindStepAt_iff d n κ gmax).2
    (indStepAbs_of d n gmax (fun p : KLPar κ gmax => p.L) (fun p => p.g) (fun p => p.t)
      (fun p σ δ => KLSigmaPi d p.L p.g (mSigma p.E) p.t σ ∅ δ)
      (fun p s s' => thetaEdge d p.L p.g (mSigma p.E) p.t s s') hd hn
      (fun p => ⟨p.hL, p.hg0, p.hg1, p.ht0, p.ht1⟩) (indStepTH_band hκ hPT)
      (sigDecayAbs_band n hd hn hκ hg) (sigSumZeroAbs_band n hd hn hκ hg))

/-- **`KLindStepPin_holds`** (target 3): the route pin `KLindStepPin` is proved; its only
hypothesis is the local propagator shapes `KLPT d κ gmax` of the statement. -/
theorem KLindStepPin_holds : KLindStepPin :=
  fun d n _ κ gmax hd hn hκ hg hPT => KLindStepAt_holds d n κ gmax hd hn hκ hg hPT

end Glue


/-! ## 7. The compiled instances: `d = 3`, `L = 5`, `g = 1/2`, `E = 0`, `t = 9/10` -/

section Instances

/-- Target 2, `KLindStep_alt`: `n = 4`, `σ = σ^{(alt)} = (+,-,+,-)`, root `r = 1`,
`a = (0, 1, 2, 3)`; `KLPT 3 1 1` is the only hypothesis left (`3 ≤ d`, `3 ≤ n`, `0 < κ`,
`0 < gmax`, the parameter point `KLinstPar` and the alternating `σ` are discharged). -/
example (hPT : KLPT 3 1 1) :
    ∃ C : ℝ, 0 < C ∧
      ∑ b : Zd 3 5, ‖∑ δ ∈ Finset.univ.filter (fun δ : Fin 4 → Zd 3 5 => δ 1 = b),
          KLSigmaPi 3 5 (1 / 2) (mSigma 0) (9 / 10) (KLsigAlt 4) ∅ δ *
            ∏ i ∈ Finset.univ.erase (1 : Fin 4),
              thetaEdge 3 5 (1 / 2) (mSigma 0) (9 / 10) (KLsigAlt 4 i) (KLsigAlt 4 (i + 1))
                (![0, 1, 2, 3] i) (δ i)‖
        ≤ C * ((5 : ℕ) : ℝ) ^ (1 : ℝ) * (Bparam 3 5 (1 / 2) (9 / 10) 0) ^ (4 - 2) := by
  obtain ⟨C, hC, H⟩ := KLindStep_alt 4 (by norm_num) (by norm_num) one_pos one_pos hPT 1 one_pos
  exact ⟨C, hC, H KLinstPar (KLsigAlt 4) 1 (by decide) ![0, 1, 2, 3]⟩

/-- Target 2, the complement `¬σ^{(alt)} = (-,+,-,+)` (also alternating), root `r = 2`, a spread
labelling `a = ((0,0,0), (1,0,0), (0,1,2), (2,2,2))`. -/
example (hPT : KLPT 3 1 1) :
    ∃ C : ℝ, 0 < C ∧
      ∑ b : Zd 3 5, ‖∑ δ ∈ Finset.univ.filter (fun δ : Fin 4 → Zd 3 5 => δ 2 = b),
          KLSigmaPi 3 5 (1 / 2) (mSigma 0) (9 / 10) (fun k => !KLsigAlt 4 k) ∅ δ *
            ∏ i ∈ Finset.univ.erase (2 : Fin 4),
              thetaEdge 3 5 (1 / 2) (mSigma 0) (9 / 10) (!KLsigAlt 4 i) (!KLsigAlt 4 (i + 1))
                (![![0, 0, 0], ![1, 0, 0], ![0, 1, 2], ![2, 2, 2]] i) (δ i)‖
        ≤ C * ((5 : ℕ) : ℝ) ^ (1 : ℝ) * (Bparam 3 5 (1 / 2) (9 / 10) 0) ^ (4 - 2) := by
  obtain ⟨C, hC, H⟩ := KLindStep_alt 4 (by norm_num) (by norm_num) one_pos one_pos hPT 1 one_pos
  exact ⟨C, hC, H KLinstPar (fun k => !KLsigAlt 4 k) 2 (by decide)
    ![![0, 0, 0], ![1, 0, 0], ![0, 1, 2], ![2, 2, 2]]⟩

/-- Target 2 at `n = 6` (`|{j ≠ r}| = 5`): `σ^{(alt)}`, root `r = 3`, `a = (0, 1, 2, 3, 4, 0)`. -/
example (hPT : KLPT 3 1 1) :
    ∃ C : ℝ, 0 < C ∧
      ∑ b : Zd 3 5, ‖∑ δ ∈ Finset.univ.filter (fun δ : Fin 6 → Zd 3 5 => δ 3 = b),
          KLSigmaPi 3 5 (1 / 2) (mSigma 0) (9 / 10) (KLsigAlt 6) ∅ δ *
            ∏ i ∈ Finset.univ.erase (3 : Fin 6),
              thetaEdge 3 5 (1 / 2) (mSigma 0) (9 / 10) (KLsigAlt 6 i) (KLsigAlt 6 (i + 1))
                (![0, 1, 2, 3, 4, 0] i) (δ i)‖
        ≤ C * ((5 : ℕ) : ℝ) ^ (1 : ℝ) * (Bparam 3 5 (1 / 2) (9 / 10) 0) ^ (6 - 2) := by
  obtain ⟨C, hC, H⟩ := KLindStep_alt 6 (by norm_num) (by norm_num) one_pos one_pos hPT 1 one_pos
  exact ⟨C, hC, H KLinstPar (KLsigAlt 6) 3 (by decide) ![0, 1, 2, 3, 4, 0]⟩

/-- Target 3, `KLindStepAt_holds` at `(d, n, κ, gmax) = (3, 4, 1, 1)`, unfolded at the data: one
constant `C` serves an alternating `σ` (root `1`, `KLindStep_alt`), the complement (root `2`) and
the non-alternating `σ = (+,+,+,-)` (long root `2`, `KLindStep_nonAlt`). -/
example (hPT : KLPT 3 1 1) :
    ∃ C : ℝ, 0 < C ∧
      (∑ b : Zd 3 5, ‖∑ δ ∈ Finset.univ.filter (fun δ : Fin 4 → Zd 3 5 => δ 1 = b),
          KLSigmaPi 3 5 (1 / 2) (mSigma 0) (9 / 10) (KLsigAlt 4) ∅ δ *
            ∏ i ∈ Finset.univ.erase (1 : Fin 4),
              thetaEdge 3 5 (1 / 2) (mSigma 0) (9 / 10) (KLsigAlt 4 i) (KLsigAlt 4 (i + 1))
                (![0, 1, 2, 3] i) (δ i)‖
        ≤ C * ((5 : ℕ) : ℝ) ^ (1 : ℝ) * (Bparam 3 5 (1 / 2) (9 / 10) 0) ^ (4 - 2)) ∧
      (∑ b : Zd 3 5, ‖∑ δ ∈ Finset.univ.filter (fun δ : Fin 4 → Zd 3 5 => δ 2 = b),
          KLSigmaPi 3 5 (1 / 2) (mSigma 0) (9 / 10) (fun k => !KLsigAlt 4 k) ∅ δ *
            ∏ i ∈ Finset.univ.erase (2 : Fin 4),
              thetaEdge 3 5 (1 / 2) (mSigma 0) (9 / 10) (!KLsigAlt 4 i) (!KLsigAlt 4 (i + 1))
                (![0, 1, 2, 3] i) (δ i)‖
        ≤ C * ((5 : ℕ) : ℝ) ^ (1 : ℝ) * (Bparam 3 5 (1 / 2) (9 / 10) 0) ^ (4 - 2)) ∧
      (∑ b : Zd 3 5, ‖∑ δ ∈ Finset.univ.filter (fun δ : Fin 4 → Zd 3 5 => δ 2 = b),
          KLSigmaPi 3 5 (1 / 2) (mSigma 0) (9 / 10) ![true, true, true, false] ∅ δ *
            ∏ i ∈ Finset.univ.erase (2 : Fin 4),
              thetaEdge 3 5 (1 / 2) (mSigma 0) (9 / 10) (![true, true, true, false] i)
                (![true, true, true, false] (i + 1)) (![0, 1, 2, 3] i) (δ i)‖
        ≤ C * ((5 : ℕ) : ℝ) ^ (1 : ℝ) * (Bparam 3 5 (1 / 2) (9 / 10) 0) ^ (4 - 2)) := by
  obtain ⟨C, hC, H⟩ := KLindStepAt_holds 3 4 1 1 (by norm_num) (by norm_num) one_pos one_pos hPT
    1 one_pos
  exact ⟨C, hC, H KLinstPar (KLsigAlt 4) 1 (by decide) ![0, 1, 2, 3],
    H KLinstPar (fun k => !KLsigAlt 4 k) 2 (by decide) ![0, 1, 2, 3],
    H KLinstPar ![true, true, true, false] 2 (by decide) ![0, 1, 2, 3]⟩

/-- Target 3, `KLindStepPin_holds` applied at `(d, n, κ, gmax) = (3, 4, 1, 1)` and `(3, 3, 1, 1)`,
and unfolded at `n = 3` (never alternating), `σ = (+,-,+)`, root `r = 0`, `a = (0, 1, 2)`. -/
example (hPT : KLPT 3 1 1) :
    KLindStepAt 3 4 1 1 ∧
    ∃ C : ℝ, 0 < C ∧
      ∑ b : Zd 3 5, ‖∑ δ ∈ Finset.univ.filter (fun δ : Fin 3 → Zd 3 5 => δ 0 = b),
          KLSigmaPi 3 5 (1 / 2) (mSigma 0) (9 / 10) KLinstσ ∅ δ *
            ∏ i ∈ Finset.univ.erase (0 : Fin 3),
              thetaEdge 3 5 (1 / 2) (mSigma 0) (9 / 10) (KLinstσ i) (KLinstσ (i + 1))
                (KLinsta i) (δ i)‖
        ≤ C * ((5 : ℕ) : ℝ) ^ (1 : ℝ) * (Bparam 3 5 (1 / 2) (9 / 10) 0) ^ (3 - 2) := by
  refine ⟨KLindStepPin_holds 3 4 1 1 (by norm_num) (by norm_num) one_pos one_pos hPT, ?_⟩
  obtain ⟨C, hC, H⟩ := KLindStepPin_holds 3 3 1 1 (by norm_num) (by norm_num) one_pos one_pos hPT
    1 one_pos
  exact ⟨C, hC, H KLinstPar KLinstσ 0 (by decide) KLinsta⟩

/-- T2365, `indStepAbs_of` (target 3) applied to the three band bundles at `ι = KLPar 1 1`, `d = 3`,
`n = 4`, `gmax = 1` (`indStepTH_band`, `sigDecayAbs_band`, `sigSumZeroAbs_band`), then evaluated at the
§7 point `KLinstPar` (`L = 5`, `g = 1/2`, `E = 0`, `t = 9/10`): an alternating `σ` (root `1`, case (ii))
and `σ = (+,+,+,-)` (root `2`, case (i)).  `KLPT 3 1 1` is the only hypothesis left; the parameter
range, `3 ≤ d`, `3 ≤ n` and the bundles' band hypotheses are discharged. -/
example (hPT : KLPT 3 1 1) :
    ∃ C : ℝ, 0 < C ∧
      (∑ b : Zd 3 5, ‖∑ δ ∈ Finset.univ.filter (fun δ : Fin 4 → Zd 3 5 => δ 1 = b),
          KLSigmaPi 3 5 (1 / 2) (mSigma 0) (9 / 10) (KLsigAlt 4) ∅ δ *
            ∏ i ∈ Finset.univ.erase (1 : Fin 4),
              thetaEdge 3 5 (1 / 2) (mSigma 0) (9 / 10) (KLsigAlt 4 i) (KLsigAlt 4 (i + 1))
                (![0, 1, 2, 3] i) (δ i)‖
        ≤ C * ((5 : ℕ) : ℝ) ^ (1 : ℝ) * (Bparam 3 5 (1 / 2) (9 / 10) 0) ^ (4 - 2)) ∧
      (∑ b : Zd 3 5, ‖∑ δ ∈ Finset.univ.filter (fun δ : Fin 4 → Zd 3 5 => δ 2 = b),
          KLSigmaPi 3 5 (1 / 2) (mSigma 0) (9 / 10) ![true, true, true, false] ∅ δ *
            ∏ i ∈ Finset.univ.erase (2 : Fin 4),
              thetaEdge 3 5 (1 / 2) (mSigma 0) (9 / 10) (![true, true, true, false] i)
                (![true, true, true, false] (i + 1)) (![0, 1, 2, 3] i) (δ i)‖
        ≤ C * ((5 : ℕ) : ℝ) ^ (1 : ℝ) * (Bparam 3 5 (1 / 2) (9 / 10) 0) ^ (4 - 2)) := by
  obtain ⟨C, hC, H⟩ := indStepAbs_of 3 4 1 (fun p : KLPar 1 1 => p.L) (fun p => p.g) (fun p => p.t)
    (fun p σ δ => KLSigmaPi 3 p.L p.g (mSigma p.E) p.t σ ∅ δ)
    (fun p s s' => thetaEdge 3 p.L p.g (mSigma p.E) p.t s s') (by norm_num) (by norm_num)
    (fun p => ⟨p.hL, p.hg0, p.hg1, p.ht0, p.ht1⟩) (indStepTH_band one_pos hPT)
    (sigDecayAbs_band 4 (by norm_num) (by norm_num) one_pos one_pos)
    (sigSumZeroAbs_band 4 (by norm_num) (by norm_num) one_pos one_pos) 1 one_pos
  exact ⟨C, hC, H KLinstPar (KLsigAlt 4) 1 (by decide) ![0, 1, 2, 3],
    H KLinstPar ![true, true, true, false] 2 (by decide) ![0, 1, 2, 3]⟩

end Instances


end RBM.Loop
