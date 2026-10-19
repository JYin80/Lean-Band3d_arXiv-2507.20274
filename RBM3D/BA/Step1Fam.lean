/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.BA.Step1

/-!
# The `BAStep1` family assembly

Paper: Step 1 of the proof of Theorem 8.2 (`lem:main_ind_BA`), with Lemma 8.5 (`lem_ConArg_BA`).  Namespace `RBM.BA`.

* section 1 (the ConArg source member):
  `BAm_self_of_im_pos`, `BAtauS`, `BAzSrc`, `BAzSrc_spec` and `BAFamZ_closed`, for the
  ConArg time range `u ≤ max(t₀, s)`; `BAFamZ_mono_max`;
* section 2 (tail congruence): `FlowFM.EqAt`, `FlowFM.EvEq`, the congruence lemmas (`BAflowT0_congr`, `STLKgL_congr`, ...),
  `PrecL_ite`, `STLmaxgL_max`, and `BAConArgLoop''_congr`;
* section 3 (the statements `BAStep1` and `BALmaxFromLK`, and the chain helpers);
* section 4 (`BAStep1_of_parts'`; `baStep1_holds'` in `BA/Step1Prime` completes it);
* section 5 (`BAFlowMember_holds`, `BALmaxFromLK_holds`).
-/

set_option linter.style.longLine false

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal Topology Kronecker

noncomputable section

namespace RBM.BA

open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes

/-! ## 1. The ConArg source member of a family member -/

section Source

variable {d : ℕ}

/-- `BAm` is a solution when its imaginary part is positive (`BAm = 0` is the junk value). -/
theorem BAm_self_of_im_pos {d L : ℕ} [NeZero L] {g : ℝ} {z : ℂ} (h : 0 < (BAm d L g z).im) :
    BASelf d L g z (BAm d L g z) := by
  by_contra hno
  have hne : ¬ ∃ m, BASelf d L g z m := fun ⟨m, hm⟩ => hno (BAm_spec ⟨m, hm⟩)
  have h0 : BAm d L g z = 0 := by
    unfold BAm
    split_ifs
    rfl
  rw [h0] at h
  simp at h

/-- `τ'' = t₀(z') s/u`, the horizon of the ConArg source of the member `z'`. -/
def BAtauS (sz : Sizes d) (z' : ℕ → ℂ) (s u : ℕ → ℝ) (n : ℕ) : ℝ := BAflowT0 sz z' n * (s n / u n)

/-- The ConArg source member. -/
def BAzSrc (sz : Sizes d) (z' : ℕ → ℂ) (s u : ℕ → ℝ) : ℕ → ℂ := fun n =>
  ztOf (BAm d (sz.L n) (Real.sqrt (BAtauS sz z' s u n) * sz.lam n) (BAflowEs sz z' n : ℂ)) (BAflowEs sz z' n)
      (BAtauS sz z' s u n) / (Real.sqrt (BAtauS sz z' s u n) : ℂ)

/-- `g_s = √(s/u) g₀(z') = √(τ'') g`. -/
theorem BAlamS_eq (sz : Sizes d) (z' : ℕ → ℂ) (s u : ℕ → ℝ) (n : ℕ) (h0 : 0 ≤ BAflowT0 sz z' n) :
    BAlamS sz z' s u n = Real.sqrt (BAtauS sz z' s u n) * sz.lam n := by
  unfold BAlamS BAtauS BAflowLam0
  rw [Real.sqrt_mul h0]
  ring

theorem BAflowT0_congr (sz : Sizes d) {z₁ z₂ : ℕ → ℂ} {n : ℕ} (h : z₁ n = z₂ n) : BAflowT0 sz z₁ n = BAflowT0 sz z₂ n := by
  unfold BAflowT0; rw [h]

theorem BAflowEs_congr (sz : Sizes d) {z₁ z₂ : ℕ → ℂ} {n : ℕ} (h : z₁ n = z₂ n) : BAflowEs sz z₁ n = BAflowEs sz z₂ n := by
  unfold BAflowEs; rw [h]

/-- The ConArg source of a member, at one size index: for a member `z'`
of `Fam(u)`, a source time `s ∈ [1 - c₁, u]` with `u ≤ max(t₀(z), s)` and `0 < t₀(z) < 1`, `0 ≤ lam n`: the source horizon
`τ''` satisfies `min(t₀, s) ≤ τ'' ≤ t₀`; the energy is in the κ-bulk at the source coupling `g_s`; the source parameter
`BAzSrc` has horizon `τ''`, energy `E`, and the carrier coupling `g_s`.  (If `t₀(z) < u` then `u = s`, `s/u = 1` and
`τ'' = t₀(z)`.) -/
theorem BAzSrc_spec (sz : Sizes d) (z z' : ℕ → ℂ) (c₁ κ : ℝ) (hκ : 0 < κ) (hc₁ : 0 < c₁) (hc₁' : c₁ ≤ 1 / 2)
    (hwin : BAWinBulk sz z c₁ κ) (s u : ℕ → ℝ) (n : ℕ) (hlam : 0 ≤ sz.lam n)
    (hT0 : 0 < BAflowT0 sz z n) (hT1 : BAflowT0 sz z n < 1) (hs : 1 - c₁ ≤ s n) (hsu : s n ≤ u n)
    (hu : u n ≤ max (BAflowT0 sz z n) (s n)) (hE : BAflowEs sz z' n = BAflowEs sz z n)
    (hlo : min (BAflowT0 sz z n) (max (u n) (1 - c₁)) ≤ BAflowT0 sz z' n) (hhi : BAflowT0 sz z' n ≤ BAflowT0 sz z n) :
    min (BAflowT0 sz z n) (s n) ≤ BAtauS sz z' s u n ∧ BAtauS sz z' s u n ≤ BAflowT0 sz z n ∧
      κ ≤ (BAm d (sz.L n) (BAlamS sz z' s u n) (BAflowEs sz z' n : ℂ)).im ∧
      BAflowT0 sz (BAzSrc sz z' s u) n = BAtauS sz z' s u n ∧
      BAflowEs sz (BAzSrc sz z' s u) n = BAflowEs sz z' n ∧
      BAflowLam0 sz (BAzSrc sz z' s u) n = BAlamS sz z' s u n := by
  have hs0 : 0 < s n := by linarith
  have hu0 : 0 < u n := lt_of_lt_of_le hs0 hsu
  have hmaxu : max (u n) (1 - c₁) = u n := max_eq_left (by linarith)
  rw [hmaxu] at hlo
  have hτ'0 : 0 < BAflowT0 sz z' n := lt_of_lt_of_le (lt_min hT0 hu0) hlo
  have hsu1 : s n / u n ≤ 1 := (div_le_one hu0).mpr hsu
  have hsu0 : 0 ≤ s n / u n := div_nonneg hs0.le hu0.le
  have hτs : min (BAflowT0 sz z n) (s n) ≤ BAtauS sz z' s u n := by
    unfold BAtauS
    rcases le_or_gt (u n) (BAflowT0 sz z n) with h | h
    · have h1 : u n ≤ BAflowT0 sz z' n := le_trans (le_min h le_rfl) hlo
      calc min (BAflowT0 sz z n) (s n) ≤ s n := min_le_right _ _
        _ = u n * (s n / u n) := by field_simp
        _ ≤ BAflowT0 sz z' n * (s n / u n) := mul_le_mul_of_nonneg_right h1 hsu0
    · have hus : u n = s n := by
        rcases le_total (BAflowT0 sz z n) (s n) with h2 | h2
        · rw [max_eq_right h2] at hu; exact le_antisymm hu hsu
        · rw [max_eq_left h2] at hu; exact absurd hu (not_le.mpr h)
      have h1 : BAflowT0 sz z' n = BAflowT0 sz z n := by
        have : BAflowT0 sz z n ≤ BAflowT0 sz z' n := le_trans (le_min le_rfl h.le) hlo
        exact le_antisymm hhi this
      have h2 : s n / u n = 1 := by rw [hus]; exact div_self hs0.ne'
      rw [h1, h2, mul_one]
      exact min_le_left _ _
  have hτ₀ : BAtauS sz z' s u n ≤ BAflowT0 sz z n := by
    unfold BAtauS
    calc BAflowT0 sz z' n * (s n / u n) ≤ BAflowT0 sz z' n * 1 := mul_le_mul_of_nonneg_left hsu1 hτ'0.le
      _ ≤ BAflowT0 sz z n := by linarith
  have hτ''pos : 0 < BAtauS sz z' s u n := lt_of_lt_of_le (lt_min hT0 hs0) hτs
  have hlamS : BAlamS sz z' s u n = Real.sqrt (BAtauS sz z' s u n) * sz.lam n := BAlamS_eq sz z' s u n hτ'0.le
  have hlo' : Real.sqrt (1 - c₁) * BAflowLam0 sz z n ≤ BAlamS sz z' s u n := by
    rw [hlamS]
    unfold BAflowLam0
    rw [← mul_assoc, ← Real.sqrt_mul (by linarith)]
    refine mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt ?_) hlam
    refine le_trans (le_min ?_ ?_) hτs
    · nlinarith
    · nlinarith
  have hhi' : BAlamS sz z' s u n ≤ BAflowLam0 sz z n := by
    rw [hlamS]
    exact mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hτ₀) hlam
  have hbulk : κ ≤ (BAm d (sz.L n) (BAlamS sz z' s u n) (BAflowEs sz z' n : ℂ)).im := by
    rw [hE]; exact hwin n _ hlo' hhi'
  refine ⟨hτs, hτ₀, hbulk, ?_⟩
  have hself := BAm_self_of_im_pos (d := d) (L := sz.L n) (g := BAlamS sz z' s u n)
    (z := (BAflowEs sz z' n : ℂ)) (lt_of_lt_of_le hκ hbulk)
  rw [hlamS] at hself
  obtain ⟨h1, h2, h3⟩ := BAzztE_inv_core d (sz.L n) (sz.lam n) (BAtauS sz z' s u n) (BAflowEs sz z' n) _ hτ''pos
    (lt_of_le_of_lt hτ₀ hT1) hself
  have hz : BAzSrc sz z' s u n = ztOf (BAm d (sz.L n) (Real.sqrt (BAtauS sz z' s u n) * sz.lam n)
      (BAflowEs sz z' n : ℂ)) (BAflowEs sz z' n) (BAtauS sz z' s u n) /
      (Real.sqrt (BAtauS sz z' s u n) : ℂ) := rfl
  have hT : BAflowT0 sz (BAzSrc sz z' s u) n = BAtauS sz z' s u n := by
    unfold BAflowT0
    rw [hz, h1]; exact h2
  refine ⟨hT, ?_, ?_⟩
  · unfold BAflowEs
    rw [hz, h1]; exact h3
  · unfold BAflowLam0
    rw [hT, hlamS]

/-- Closure of the horizon cone under the ConArg map (see `BAzSrc_spec`).  If `z'` is a member
of `Fam(u)`, `s ∈ [1 - c₁, u]` with `u ≤ max(t₀(z), s)`, then its ConArg source `BAzSrc sz z' s u` is a member of `Fam(s)`. -/
theorem BAFamZ_closed (sz : Sizes d) (z : ℕ → ℂ) (c₁ κ : ℝ) (hκ : 0 < κ) (hc₁ : 0 < c₁) (hc₁' : c₁ ≤ 1 / 2)
    (hlam : ∀ n, 0 ≤ sz.lam n) (hwin : BAWinBulk sz z c₁ κ) (hT0 : ∀ n, 0 < BAflowT0 sz z n)
    (hT1 : ∀ n, BAflowT0 sz z n < 1) (s u : ℕ → ℝ)
    (hs : ∀ n, 1 - c₁ ≤ s n) (hsu : ∀ n, s n ≤ u n) (hu : ∀ n, u n ≤ max (BAflowT0 sz z n) (s n))
    (z' : ℕ → ℂ) (hz' : BAFamZ sz z c₁ u z') : BAFamZ sz z c₁ s (BAzSrc sz z' s u) := by
  intro n
  obtain ⟨h1, h2, -, h4, h5, -⟩ := BAzSrc_spec sz z z' c₁ κ hκ hc₁ hc₁' hwin s u n (hlam n) (hT0 n) (hT1 n) (hs n)
    (hsu n) (hu n) (hz' n).1 (hz' n).2.1 (hz' n).2.2
  refine ⟨?_, ?_, ?_⟩
  · rw [h5]; exact (hz' n).1
  · rw [h4, max_eq_left (hs n)]; exact h1
  · rw [h4]; exact h2

/-- `Fam(t) ⊆ Fam(u)` as soon as `max(u, 1 - c₁) ≤ max(t, 1 - c₁)` (as `BAFamZ_mono`, `BA/Step1Boot`). -/
theorem BAFamZ_mono_max (sz : Sizes d) (z : ℕ → ℂ) (c₁ : ℝ) (u t : ℕ → ℝ) (z' : ℕ → ℂ)
    (hut : ∀ n, max (u n) (1 - c₁) ≤ max (t n) (1 - c₁)) (h : BAFamZ sz z c₁ t z') : BAFamZ sz z c₁ u z' := fun n =>
  ⟨(h n).1, le_trans (min_le_min le_rfl (hut n)) (h n).2.1, (h n).2.2⟩

end Source

/-! ## 2. Tail congruence (members satisfy `BAFlow` only for `n ≥ n₀`)

`PrecL_congr` is in `BA/Step1Boot`. -/

section Congr

variable {d : ℕ} {sz : Sizes d}

/-- The model objects of two carriers agree at the size index `n`. -/
structure FlowFM.EqAt (C C' : FlowFM sz) (n : ℕ) : Prop where
  L : C.L n = C'.L n
  K : C.K n = C'.K n
  G : C.G n = C'.G n
  M : C.M n = C'.M n
  S : C.S n = C'.S n
  eta : C.eta n = C'.eta n
  m : C.m n = C'.m n

/-- Two carriers agree for all large `n`. -/
def FlowFM.EvEq (C C' : FlowFM sz) : Prop := ∀ᶠ n in atTop, FlowFM.EqAt C C' n

theorem FlowFM.EqAt.GM {C C' : FlowFM sz} {n : ℕ} (h : FlowFM.EqAt C C' n) : C.GM n = C'.GM n := by
  funext t ω x y
  simp only [FlowFM.GM, h.G, h.M]

variable {C C' : FlowFM sz} (μ : Measure sz.SeqΩ)

theorem STLKgL_congr (h : C.EvEq C') (τ : ℕ → ℝ) : STLKgL C μ τ ↔ STLKgL C' μ τ := by
  unfold STLKgL
  refine forall_congr' fun k => forall_congr' fun hk => PrecL_congr ?_
  filter_upwards [h] with n hn
  exact ⟨by funext p ω; simp only [hn.L, hn.K], rfl⟩

theorem STLmaxgL_congr (h : C.EvEq C') (τ : ℕ → ℝ) : STLmaxgL C μ τ ↔ STLmaxgL C' μ τ := by
  unfold STLmaxgL
  refine forall_congr' fun k => forall_congr' fun hk => PrecL_congr ?_
  filter_upwards [h] with n hn
  exact ⟨by funext p ω; simp only [hn.L], rfl⟩

theorem STDecaygL_congr (h : C.EvEq C') (τ : ℕ → ℝ) : STDecaygL C μ τ ↔ STDecaygL C' μ τ := by
  unfold STDecaygL
  refine forall_congr' fun D => forall_congr' fun hD => PrecL_congr ?_
  filter_upwards [h] with n hn
  exact ⟨by funext p ω; simp only [hn.L, hn.K], rfl⟩

theorem STDecayStronggL_congr (h : C.EvEq C') (τ : ℕ → ℝ) : STDecayStronggL C μ τ ↔ STDecayStronggL C' μ τ := by
  unfold STDecayStronggL
  refine forall_congr' fun D => forall_congr' fun hD => PrecL_congr ?_
  filter_upwards [h] with n hn
  exact ⟨by funext p ω; simp only [hn.L, hn.K], rfl⟩

theorem STLocalMaxgL_congr (h : C.EvEq C') (τ : ℕ → ℝ) : STLocalMaxgL C μ τ ↔ STLocalMaxgL C' μ τ := by
  unfold STLocalMaxgL
  refine PrecL_congr ?_
  filter_upwards [h] with n hn
  exact ⟨by funext p ω; simp only [hn.GM], rfl⟩

theorem STLocalEntrygL_congr (h : C.EvEq C') (τ : ℕ → ℝ) : STLocalEntrygL C μ τ ↔ STLocalEntrygL C' μ τ := by
  unfold STLocalEntrygL
  refine PrecL_congr ?_
  filter_upwards [h] with n hn
  exact ⟨by funext p ω; simp only [hn.GM], rfl⟩

theorem STExp2gL_congr (h : C.EvEq C') (τ : ℕ → ℝ) : STExp2gL C μ τ ↔ STExp2gL C' μ τ := by
  unfold STExp2gL
  refine PrecL_congr ?_
  filter_upwards [h] with n hn
  exact ⟨by funext p ω; simp only [hn.L, hn.K], rfl⟩

theorem STKboundgL_congr (h : C.EvEq C') : STKboundgL C μ ↔ STKboundgL C' μ := by
  unfold STKboundgL
  refine forall_congr' fun τ => forall_congr' fun h0 => forall_congr' fun h1 => forall_congr' fun k =>
    forall_congr' fun hk => PrecL_congr ?_
  filter_upwards [h] with n hn
  exact ⟨by funext p ω; simp only [hn.K], rfl⟩

theorem STStep1LoopgL_congr (h : C.EvEq C') (s t : ℕ → ℝ) : STStep1LoopgL C μ s t ↔ STStep1LoopgL C' μ s t := by
  unfold STStep1LoopgL
  refine forall_congr' fun k => forall_congr' fun hk => PrecL_congr ?_
  filter_upwards [h] with n hn
  exact ⟨by funext p ω; simp only [hn.L], rfl⟩

theorem STStep1WeakgL_congr (h : C.EvEq C') (s t : ℕ → ℝ) : STStep1WeakgL C μ s t ↔ STStep1WeakgL C' μ s t := by
  unfold STStep1WeakgL
  refine PrecL_congr ?_
  filter_upwards [h] with n hn
  exact ⟨by funext p ω; simp only [hn.GM], rfl⟩

/-- The carrier `baFM` at the index `n` depends on `(lam0 n, E n)` only. -/
theorem baFM_eqAt (sz : Sizes d) {lam0 lam0' E E' : ℕ → ℝ} {n : ℕ} (hl : lam0 n = lam0' n) (hE : E n = E' n) :
    FlowFM.EqAt (baFM sz lam0 E) (baFM sz lam0' E') n := by
  refine ⟨?_, ?_, ?_, ?_, rfl, ?_, ?_⟩ <;>
    simp only [baFM, BALloop, BAKloop, BAGt, BAMfine, BAmF, Sizes.seqHflowBA, hl, hE]

/-- The carrier of a member at the index `n` depends on `z' n` only. -/
theorem baFMz_eqAt (sz : Sizes d) {z₁ z₂ : ℕ → ℂ} {n : ℕ} (h : z₁ n = z₂ n) :
    FlowFM.EqAt (baFMz sz z₁) (baFMz sz z₂) n :=
  baFM_eqAt sz (by unfold BAflowLam0; rw [BAflowT0_congr sz h]) (BAflowEs_congr sz h)

end Congr

section Congr2

variable {d : ℕ} {sz : Sizes d}

theorem BAlamS_congr (sz : Sizes d) {z₁ z₂ : ℕ → ℂ} {n : ℕ} (h : z₁ n = z₂ n) (s t : ℕ → ℝ) :
    BAlamS sz z₁ s t n = BAlamS sz z₂ s t n := by
  unfold BAlamS BAflowLam0 BAflowT0; rw [h]

/-- `HighProbAt` depends only on the tail. -/
theorem HighProbAt_congr {P : Measure sz.SeqΩ} {Ξ Ξ' : ℕ → Set sz.SeqΩ} (h : ∀ᶠ n in atTop, Ξ n = Ξ' n) :
    HighProbAt P sz.size Ξ ↔ HighProbAt P sz.size Ξ' := by
  unfold HighProbAt
  refine forall_congr' fun D => forall_congr' fun hD => eventually_congr ?_
  filter_upwards [h] with n hn
  rw [hn]

/-- The loop part of `lem_ConArg_BA`, event form, is tail-local in the spectral parameter. -/
theorem BAConArgLoop''_congr (sz : Sizes d) (z₁ z₂ : ℕ → ℂ) (h : ∀ᶠ n in atTop, z₁ n = z₂ n)
    (s t : ℕ → ℝ) (k : ℕ) (C₀ : ℝ) : (BAConArgLoop'' sz z₁ s t k C₀ ↔ BAConArgLoop'' sz z₂ s t k C₀) := by
  unfold BAConArgLoop''
  refine PrecL_congr ?_
  filter_upwards [h] with n hn
  have hE := baFMz_eqAt sz hn
  constructor
  · funext p ω
    simp only [FlowFM.omegaC, hE.G, hE.L]
  · funext p ω
    simp only [hE.eta, BAmF, BAlamS_congr sz hn, BAflowEs_congr sz hn]

/-- The vector part of `lem_ConArg_BA` is tail-local in the spectral parameter. -/
theorem BAConArgVec_congr (sz : Sizes d) (z₁ z₂ : ℕ → ℂ) (h : ∀ᶠ n in atTop, z₁ n = z₂ n)
    (s t : ℕ → ℝ) : (BAConArgVec sz z₁ s t ↔ BAConArgVec sz z₂ s t) := by
  unfold BAConArgVec
  refine forall_congr' fun v => forall_congr' fun w => forall_congr' fun hv => forall_congr' fun hw => ?_
  refine imp_congr (exists_congr fun C₀ => and_congr_right fun _ => HighProbAt_congr ?_)
    (exists_congr fun C₁ => and_congr_right fun _ => HighProbAt_congr ?_) <;>
  · filter_upwards [h] with n hn
    have hE := baFMz_eqAt sz hn
    ext ω
    simp only [Set.mem_ofPred_eq, BAGt, Sizes.seqHflowBA, BAmF, BAlamS_congr sz hn, BAflowEs_congr sz hn,
      hE.eta, BAflowLam0, BAflowT0_congr sz hn]

/-- A pointwise-in-`n` case split of two dominations is a domination. -/
theorem PrecL_ite {μ : Measure sz.SeqΩ} {U : ℕ → Type*} {ξ₁ ζ₁ ξ₂ ζ₂ : ∀ n, U n → sz.SeqΩ → ℝ} (A : ℕ → Prop)
    [DecidablePred A] (h₁ : PrecL sz μ ξ₁ ζ₁) (h₂ : PrecL sz μ ξ₂ ζ₂) :
    PrecL sz μ (fun n u ω => if A n then ξ₁ n u ω else ξ₂ n u ω)
      (fun n u ω => if A n then ζ₁ n u ω else ζ₂ n u ω) := by
  unfold PrecL StochDomAt at *
  intro τ hτ D hD
  filter_upwards [h₁ τ hτ D hD, h₂ τ hτ D hD] with n hn1 hn2
  by_cases hA : A n
  · simpa [badSetAt, hA] using hn1
  · simpa [badSetAt, hA] using hn2

/-- The loop bound at the time `max(s, c)`: the loop bound at `s` and at the constant time `c`. -/
theorem STLmaxgL_max (sz : Sizes d) (C : FlowFM sz) (μ : Measure sz.SeqΩ) (s : ℕ → ℝ) (c : ℝ) (h₁ : STLmaxgL C μ s)
    (h₂ : STLmaxgL C μ (fun _ => c)) : STLmaxgL C μ (fun n => max (s n) c) := by
  intro k hk
  classical
  refine (PrecL_congr ?_).mp (PrecL_ite (fun n => c ≤ s n) (h₁ k hk) (h₂ k hk))
  refine Eventually.of_forall fun n => ?_
  by_cases hA : c ≤ s n
  · simp [hA]
  · simp [hA, max_eq_right (not_le.mp hA).le]

end Congr2

/-! ## 3. The statements `BALmaxFromLK`, `BAStep1` and the chain helpers -/

/-- `(eq:loopbound_s)` from `(Eq:L-KGt)` and `ML:Kbound` for any carrier: `|𝓛| ≤ |𝓛 - 𝒦| + |𝒦| ≺
B^k + B^{k-1} ≤ 2 B^{k-1}` when `Bctl ≤ 1` (the band's `s1_h55` at `s ≥ 1/2`, `Induction/Step1Setup`).  It is proved as
`BALmaxFromLK_holds`. -/
def BALmaxFromLK (d : ℕ) : Prop :=
  ∀ (sz : Sizes d) (C : FlowFM sz) (τ : ℕ → ℝ), sz.SizeTendsto → (∀ n, 0 ≤ τ n) → (∀ n, τ n < 1) →
    (∀ᶠ n in atTop, sz.Bctl n (τ n) ≤ 1) → STKboundgL C (Sizes.seqP (sz.withLam 0)) →
      STLKgL C (Sizes.seqP (sz.withLam 0)) τ → STLmaxgL C (Sizes.seqP (sz.withLam 0)) τ

/-- Step 1 of Theorem 8.2 (`lem:main_ind_BA`), family form (with `lem_ConArg_BA`, `lem_GbEXP_BA`): from `(a)`, `(c)`, `ML:Kbound` of every member of the family at `s`
and `(con_st_ind)`, the conclusions
`(lRB1)`, `(Gtmwc)` uniformly in `u ∈ [s,t]` for every member of the family at `t`.  It is proved from `BAGbEXPii`, `BAGbEXPij'`
(`baStep1_holds'`, `BA/Step1Prime`). -/
def BAStep1 (d : ℕ) : Prop :=
  ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ 𝔠d : ℝ, 0 < 𝔠d → 𝔠d ≤ 1 / 100 →
      ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z → (∀ n, 0 < sz.lam n) →
        ∀ c₁ : ℝ, 0 < c₁ → c₁ ≤ 1 / 2 → BAWinBulk sz z c₁ κ →
          ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n ≤ BAflowT0 sz z n) → (∀ n, s n < t n) →
            (∀ n, t n ≤ BAflowT0 sz z n) →
            (∀ z' : ℕ → ℂ, BAFamZ sz z c₁ s z' →
              STKboundgL (baFMz sz z') (Sizes.seqP (sz.withLam 0)) ∧
                STLKgL (baFMz sz z') (Sizes.seqP (sz.withLam 0)) s ∧
                STLocalMaxgL (baFMz sz z') (Sizes.seqP (sz.withLam 0)) s) →
            STConStInd sz 𝔠d s t →
              ∀ z' : ℕ → ℂ, BAFamZ sz z c₁ t z' →
                STStep1LoopgL (baFMz sz z') (Sizes.seqP (sz.withLam 0)) s t ∧
                  STStep1WeakgL (baFMz sz z') (Sizes.seqP (sz.withLam 0)) s t

section Chain

variable {d : ℕ}

/-- `(con_st_ind)` gives `Bctl_{t} < 1` eventually, hence `Bctl_{s} ≤ Bctl_{t} < 1`. -/
theorem Bctl_le_one_of_conStInd (sz : Sizes d) {𝔠d : ℝ} (h𝔠d : 0 < 𝔠d) {s t : ℕ → ℝ} (hst : ∀ n, s n ≤ t n)
    (ht1 : ∀ n, t n < 1) (hcon : STConStInd sz 𝔠d s t) : ∀ᶠ n in atTop, sz.Bctl n (s n) ≤ 1 := by
  filter_upwards [hcon] with n hn
  obtain ⟨h1, h2⟩ := hn
  have hlt : sz.Bctl n (t n) < 1 := by
    by_contra hge
    push Not at hge
    have := Real.one_le_rpow hge h𝔠d.le
    linarith
  exact (sz.STBctl_mono n (hst n) (ht1 n)).trans hlt.le

/-- Pointwise modification of a member by another member stays a member. -/
theorem BAFamZ_ite {sz : Sizes d} {z : ℕ → ℂ} {c₁ : ℝ} {u : ℕ → ℝ} {z₁ z₂ : ℕ → ℂ} (h₁ : BAFamZ sz z c₁ u z₁)
    (h₂ : BAFamZ sz z c₁ u z₂) (n₀ : ℕ) : BAFamZ sz z c₁ u (fun n => if n < n₀ then z₁ n else z₂ n) := by
  intro n
  by_cases hn : n < n₀
  · have e : (fun n => if n < n₀ then z₁ n else z₂ n) n = z₁ n := by simp [hn]
    have e1 := BAflowEs_congr sz (z₁ := fun n => if n < n₀ then z₁ n else z₂ n) (z₂ := z₁) (n := n) e
    have e2 := BAflowT0_congr sz (z₁ := fun n => if n < n₀ then z₁ n else z₂ n) (z₂ := z₁) (n := n) e
    exact ⟨by rw [e1]; exact (h₁ n).1, by rw [e2]; exact (h₁ n).2.1, by rw [e2]; exact (h₁ n).2.2⟩
  · have e : (fun n => if n < n₀ then z₁ n else z₂ n) n = z₂ n := by simp [hn]
    have e1 := BAflowEs_congr sz (z₁ := fun n => if n < n₀ then z₁ n else z₂ n) (z₂ := z₂) (n := n) e
    have e2 := BAflowT0_congr sz (z₁ := fun n => if n < n₀ then z₁ n else z₂ n) (z₂ := z₂) (n := n) e
    exact ⟨by rw [e1]; exact (h₂ n).1, by rw [e2]; exact (h₂ n).2.1, by rw [e2]; exact (h₂ n).2.2⟩

end Chain

/-! ## 4. The assembly of `BAStep1` (in the event form) -/

section Assembly

/-- `BAStep1` from the parts `hC : BAConArg'' d`,
`hB : BABootstrap' d`.  `BABootstrap'` supplies the conclusions for the member `z'` of `Fam(t)` from its own
`STKboundgL`, `STLKgL`, `STLocalMaxgL` at `s` (the family premise at `z' ∈ Fam(s)`) and the ConArg outputs for every
`u ∈ [s₁, max(t, 1 - c₁)]`, `s₁ = max(s, 1 - c₁)`.  These are obtained from `BAConArg''` applied to the finite modification
`z3` of `z'` (`BAFlowMember`) at `(s₁, u)` with source `BAzSrc sz z3 s₁ u ∈ Fam(s₁)` (`BAFamZ_closed`), whose loop bound at
`s₁` is `STLmaxgL_max` of `BALmaxFromLK` (at `s`, from the family premise at the source member) and `BATrivialLmax` (at
`1 - c₁`), moved to the carrier of `BAConArg''` by `STLmaxgL_congr`; the outputs move from `z3` to `z'` by the tail
congruences. -/
theorem BAStep1_of_parts' (d : ℕ) (hmem : BAFlowMember d) (hL : BALmaxFromLK d) (hT : BATrivialLmax d)
    (hC : BAConArg'' d) (hB : BABootstrap' d) : BAStep1 d := by
  intro κ ε 𝔡 hκ hε h𝔡 𝔠d h𝔠d0 h𝔠d1 𝔠 sz z hflow hlam c₁ hc₁ hc₁' hwin s t hs0 hsT hst htT hmemb hcon z' hz't
  have hts : ∀ n, s n ≤ t n := fun n => (hst n).le
  have hz's : BAFamZ sz z c₁ s z' := BAFamZ_mono hts hz't
  obtain ⟨hK, hLK, hLM⟩ := hmemb z' hz's
  refine hB κ ε 𝔡 hκ hε h𝔡 𝔠d h𝔠d0 h𝔠d1 𝔠 sz z hflow hlam c₁ hc₁ hc₁' hwin s t hs0 hsT hst htT z' hz't hK hLK hLM
    hcon ?_
  intro u hu1 hu2
  have hT0 : ∀ n, 0 < BAflowT0 sz z n := fun n => (BAflow_T0_bounds hκ hflow n).2.2.1
  have hT1 : ∀ n, BAflowT0 sz z n < 1 := fun n => (BAflow_T0_bounds hκ hflow n).2.2.2
  have hs₁ge : ∀ n, 1 - c₁ ≤ max (s n) (1 - c₁) := fun n => le_max_right _ _
  have hε₁ : ∀ n, 1 / 2 ≤ max (s n) (1 - c₁) := fun n => by linarith [hs₁ge n]
  have huT : ∀ n, u n ≤ max (BAflowT0 sz z n) (max (s n) (1 - c₁)) := fun n =>
    (hu2 n).trans (max_le ((htT n).trans (le_max_left _ _)) (hs₁ge n |>.trans (le_max_right _ _)))
  have hu1' : ∀ n, u n < 1 := fun n =>
    lt_of_le_of_lt (hu2 n) (max_lt ((htT n).trans_lt (hT1 n)) (by linarith))
  have hlam' : ∀ n, 0 ≤ sz.lam n := fun n => (hlam n).le
  -- the finite modification of the member
  obtain ⟨κ', ε', hκ'0, hκ'κ, hε'0, hε'ε, H⟩ := hmem κ ε 𝔡 hκ hε h𝔡
  have hz'0 : BAFamZ sz z c₁ (fun _ => 0) z' :=
    BAFamZ_mono (fun n => (hs0 n).trans (hts n)) hz't
  obtain ⟨n₀, hflow'⟩ := H 𝔠 sz z hflow hlam c₁ hc₁ hc₁' hwin z' hz'0
  set z3 : ℕ → ℂ := fun n => if n < n₀ then z n else z' n with hz3
  have hz3u : BAFamZ sz z c₁ u z3 :=
    BAFamZ_ite (BAFamZ_main sz z c₁ u)
      (BAFamZ_mono_max sz z c₁ u t z' (fun n => max_le (hu2 n) (le_max_right _ _)) hz't) n₀
  have hz3z' : ∀ᶠ n in atTop, z3 n = z' n :=
    Filter.eventually_atTop.mpr ⟨n₀, fun n hn => by simp [hz3, not_lt.mpr hn]⟩
  -- the source member and its carrier
  set zs : ℕ → ℂ := BAzSrc sz z3 (fun n => max (s n) (1 - c₁)) u with hzs
  have hspec := fun n => BAzSrc_spec sz z z3 c₁ κ hκ hc₁ hc₁' hwin (fun n => max (s n) (1 - c₁)) u n (hlam' n)
    (hT0 n) (hT1 n) (hs₁ge n) (hu1 n) (huT n) (hz3u n).1 (hz3u n).2.1 (hz3u n).2.2
  have hzsFam : BAFamZ sz z c₁ (fun n => max (s n) (1 - c₁)) zs :=
    BAFamZ_closed sz z c₁ κ hκ hc₁ hc₁' hlam' hwin hT0 hT1 _ u hs₁ge hu1 huT z3 hz3u
  have hcarr : (baFMz sz zs).EvEq (baFM sz (BAlamS sz z3 (fun n => max (s n) (1 - c₁)) u) (BAflowEs sz z3)) :=
    Eventually.of_forall fun n => baFM_eqAt sz (hspec n).2.2.2.2.2 (hspec n).2.2.2.2.1
  -- the loop bound of the source at `s₁ = max(s, 1 - c₁)`
  have hsizeT : sz.SizeTendsto := hflow.1.2.2.1
  have hs1 : ∀ n, s n < 1 := fun n => lt_of_lt_of_le (hst n) ((htT n).trans (hT1 n).le)
  have hB1 := Bctl_le_one_of_conStInd sz h𝔠d0 hts (fun n => lt_of_le_of_lt (htT n) (hT1 n)) hcon
  have hzsFams : BAFamZ sz z c₁ s zs := BAFamZ_mono (fun n => le_max_left _ _) hzsFam
  obtain ⟨hKs, hLKs, -⟩ := hmemb zs hzsFams
  have hLs : STLmaxgL (baFMz sz zs) (Sizes.seqP (sz.withLam 0)) s := hL sz _ s hsizeT hs0 hs1 hB1 hKs hLKs
  have hL0 : STLmaxgL (baFMz sz zs) (Sizes.seqP (sz.withLam 0)) (fun _ => 1 - c₁) :=
    hT κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow hlam c₁ hc₁ hc₁' hwin zs (BAFamZ_mono (fun n => by
      have := hs0 n; exact this.trans (le_max_left _ _)) hzsFam)
  have hLmax : STLmaxgL (baFM sz (BAlamS sz z3 (fun n => max (s n) (1 - c₁)) u) (BAflowEs sz z3))
      (Sizes.seqP (sz.withLam 0)) (fun n => max (s n) (1 - c₁)) :=
    (STLmaxgL_congr _ hcarr _).mp (STLmaxgL_max sz _ _ s (1 - c₁) hLs hL0)
  -- the added premise of `BAConArg''` and the application
  have hbulk : ∀ n, κ' ≤ (BAmF sz (BAlamS sz z3 (fun n => max (s n) (1 - c₁)) u) (BAflowEs sz z3) n).im :=
    fun n => hκ'κ.trans (hspec n).2.2.1
  have key := fun (C₀ : ℝ) (hC₀ : 0 < C₀) => hC κ' ε' 𝔡 (1 / 2) hκ'0 hε'0 h𝔡 (by norm_num) 𝔠 sz z3 hflow' _ u hε₁
    hu1 hu1' hbulk hLmax C₀ hC₀
  exact ⟨fun C₀ hC₀ k hk => (BAConArgLoop''_congr sz z3 z' hz3z' _ u k C₀).mp ((key C₀ hC₀).1 k hk),
    (BAConArgVec_congr sz z3 z' hz3z' _ u).mp (key 1 one_pos).2⟩

end Assembly

/-! ## 5. The finite modification of a member and `BALmaxFromLK` -/

section Member

variable {d : ℕ}

/-- The constant `c_κ = √min(κ/(κ+1), 1/2)`. -/
def cκ (κ : ℝ) : ℝ := Real.sqrt (min (κ / (κ + 1)) (1 / 2))

theorem cκ_pos {κ : ℝ} (hκ : 0 < κ) : 0 < cκ κ :=
  Real.sqrt_pos.mpr (lt_min (by positivity) (by norm_num))

theorem cκ_le_one (κ : ℝ) : cκ κ ≤ 1 :=
  Real.sqrt_le_one.mpr ((min_le_right _ _).trans (by norm_num))

/-- A member of the family at one size index is in the chain domain at `(c_κ κ, ·)`: the facts of `BAFlowMember`. -/
theorem BAmember_dom_at {d L : ℕ} [NeZero L] {g c₁ κ : ℝ} (hκ : 0 < κ) (hc₁ : 0 < c₁) (hc₁' : c₁ ≤ 1 / 2) (hg : 0 ≤ g)
    {z z' : ℂ} (hz : 0 < z.im) (hz1 : z.im ≤ 1) (hκm : κ ≤ (BAm d L g z).im)
    (hwin : ∀ g' : ℝ, Real.sqrt (1 - c₁) * (Real.sqrt (BAt0 z (BAm d L g z)) * g) ≤ g' →
      g' ≤ Real.sqrt (BAt0 z (BAm d L g z)) * g → κ ≤ (BAm d L g' (BAflowE z (BAm d L g z) : ℂ)).im)
    (hE : BAflowE z' (BAm d L g z') = BAflowE z (BAm d L g z))
    (hlo : min (BAt0 z (BAm d L g z)) (1 - c₁) ≤ BAt0 z' (BAm d L g z'))
    (hhi : BAt0 z' (BAm d L g z') ≤ BAt0 z (BAm d L g z)) :
    0 < z'.im ∧ cκ κ * κ ≤ (BAm d L g z').im ∧ z'.im ≤ 1 ∧ (cκ κ * κ) * z.im ≤ z'.im := by
  set m := BAm d L g z with hm
  set m' := BAm d L g z' with hm'
  set τ₀ := BAt0 z m with hτ₀
  set τ' := BAt0 z' m' with hτ'
  have hmpos : 0 < m.im := lt_of_lt_of_le hκ hκm
  have hτ₀pos : 0 < τ₀ := BAt0_pos hz hmpos
  have hτ₀lt : τ₀ < 1 := BAt0_lt_one hz hmpos
  have hmself : BASelf d L g z m := BAm_self d L g z hz
  have hκ1 : 0 < κ + 1 := by linarith
  have hτ₀lb : κ / (κ + 1) ≤ τ₀ := by
    rw [hτ₀]; unfold BAt0
    rw [div_le_div_iff₀ hκ1 (by linarith)]
    nlinarith
  have hc1 : (1 : ℝ) / 2 ≤ 1 - c₁ := by linarith
  have hcmin : min (κ / (κ + 1)) (1 / 2) ≤ τ' :=
    le_trans (le_min ((min_le_left _ _).trans hτ₀lb) ((min_le_right _ _).trans hc1)) hlo
  have hτ'pos : 0 < τ' := lt_of_lt_of_le (lt_min (by positivity) (by norm_num)) hcmin
  have hτ'lt : τ' < 1 := lt_of_le_of_lt hhi hτ₀lt
  have hm'nonneg : 0 ≤ m'.im := BAm_im_nonneg
  have hm'pos : 0 < m'.im := by
    rcases hm'nonneg.eq_or_lt with h0 | h0
    · exfalso
      have : τ' = 0 := by rw [hτ']; unfold BAt0; rw [← h0]; simp
      linarith
    · exact h0
  have hz'pos : 0 < z'.im := by
    rcases le_or_gt (m'.im + z'.im) 0 with h | h
    · exfalso
      have : τ' ≤ 0 := by
        rw [hτ']; unfold BAt0
        exact div_nonpos_of_nonneg_of_nonpos hm'pos.le h
      linarith
    · have : τ' < 1 := hτ'lt
      rw [hτ'] at this; unfold BAt0 at this
      have := (div_lt_one h).mp this
      linarith
  have hself' : BASelf d L g z' m' := BAm_self_of_im_pos hm'pos
  obtain ⟨-, -, hself0, -, -⟩ := BAzztE_data d L g hz'pos hself'
  rw [hE] at hself0
  have hsq : 0 < Real.sqrt τ' := Real.sqrt_pos.mpr hτ'pos
  have hτ₀' : (1 - c₁) * τ₀ ≤ τ' := by
    refine le_trans (le_min ?_ ?_) hlo
    · nlinarith
    · nlinarith
  have hwin' : κ ≤ (BAm d L (Real.sqrt τ' * g) (BAflowE z m : ℂ)).im := by
    refine hwin _ ?_ ?_
    · rw [← mul_assoc, ← Real.sqrt_mul (by linarith)]
      exact mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hτ₀') hg
    · exact mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hhi) hg
  have hm0eq : BAm d L (Real.sqrt τ' * g) (BAflowE z m : ℂ) = m' / (Real.sqrt τ' : ℂ) :=
    BAm_real_eq_of_self d L _ _ _ hself0
  rw [hm0eq] at hwin'
  simp only [Complex.div_ofReal_im] at hwin'
  have hm'ge : Real.sqrt τ' * κ ≤ m'.im := by
    rw [le_div_iff₀ hsq] at hwin'; linarith
  have hcκ : cκ κ ≤ Real.sqrt τ' := Real.sqrt_le_sqrt hcmin
  have hm'ge2 : cκ κ * κ ≤ m'.im := le_trans (mul_le_mul_of_nonneg_right hcκ hκ.le) hm'ge
  have hm1 : m.im ≤ 1 := BAself_im_le_one hz.le hmself
  have hm0le : m'.im / Real.sqrt τ' ≤ 1 := by
    have := BAself_im_le_one (z := (BAflowE z m : ℂ)) (by simp) hself0
    simpa only [Complex.div_ofReal_im] using this
  have hm'le : m'.im ≤ Real.sqrt τ' := by rwa [div_le_one hsq] at hm0le
  have hrel₀ := BAt0_mul hz hmpos
  have hrel' := BAt0_mul hz'pos hm'pos
  have hτ'τ₀ : τ' ≤ τ₀ := hhi
  refine ⟨hz'pos, hm'ge2, ?_, ?_⟩
  · -- `Im z' ≤ 1`
    rcases hτ'τ₀.lt_or_eq with hlt | heq
    · have h12 : 1 / 2 ≤ τ' := by
        have : τ₀ ≤ τ' ∨ 1 - c₁ ≤ τ' := min_le_iff.mp hlo
        rcases this with h | h
        · linarith
        · linarith
      have hsq2 : (1 / 2 : ℝ) ≤ Real.sqrt τ' := Real.le_sqrt_of_sq_le (by nlinarith)
      have hss : Real.sqrt τ' * Real.sqrt τ' = τ' := Real.mul_self_sqrt hτ'pos.le
      nlinarith [mul_le_mul_of_nonneg_left hm'le (by linarith : 0 ≤ 1 - τ')]
    · -- `τ' = τ₀`: the real-axis solutions agree
      have hmain := (BAzztE_data d L g hz hmself).2.2.1
      have hself0' : BASelf d L (Real.sqrt τ₀ * g) (BAflowE z m : ℂ) (m' / (Real.sqrt τ₀ : ℂ)) := by
        rw [← heq]; exact hself0
      have hsame := BASelf_unique d L (Real.sqrt τ₀ * g) (BAflowE z m : ℂ) _ _ (by simp) hmain hself0'
      have hsc : (Real.sqrt τ₀ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hτ₀pos).ne'
      have hmm : m = m' := (div_left_inj' hsc).mp hsame
      have : z'.im = z.im := by
        have h1 : τ' * z'.im = (1 - τ') * m'.im := hrel'
        have h2 : τ₀ * z.im = (1 - τ₀) * m.im := hrel₀
        rw [← heq] at h2
        rw [← hmm] at h1
        exact mul_left_cancel₀ hτ'pos.ne' (h1.trans h2.symm)
      rw [this]; exact hz1
  · -- `Im z' ≥ c_κ κ Im z`
    have hc0 : 0 ≤ cκ κ * κ := mul_nonneg (cκ_pos hκ).le hκ.le
    have h1 : τ' * z'.im = (1 - τ') * m'.im := hrel'
    have h2 : τ₀ * z.im = (1 - τ₀) * m.im := hrel₀
    have hmul : (cκ κ * κ) * z.im * (τ₀ * τ') ≤ z'.im * (τ₀ * τ') := by
      have e1 : (cκ κ * κ) * z.im * (τ₀ * τ') = (cκ κ * κ) * ((1 - τ₀) * m.im) * τ' := by
        rw [← h2]; ring
      have e2 : z'.im * (τ₀ * τ') = (1 - τ') * m'.im * τ₀ := by
        rw [← h1]; ring
      rw [e1, e2]
      have a1 : (cκ κ * κ) * ((1 - τ₀) * m.im) * τ' ≤ (cκ κ * κ) * (1 - τ₀) * τ' := by
        have h3 : (1 - τ₀) * m.im ≤ (1 - τ₀) * 1 := mul_le_mul_of_nonneg_left hm1 (by linarith)
        calc (cκ κ * κ) * ((1 - τ₀) * m.im) * τ' = ((cκ κ * κ) * τ') * ((1 - τ₀) * m.im) := by ring
          _ ≤ ((cκ κ * κ) * τ') * ((1 - τ₀) * 1) := mul_le_mul_of_nonneg_left h3 (mul_nonneg hc0 hτ'pos.le)
          _ = (cκ κ * κ) * (1 - τ₀) * τ' := by ring
      have a2 : (cκ κ * κ) * (1 - τ') * τ₀ ≤ (1 - τ') * m'.im * τ₀ := by
        calc (cκ κ * κ) * (1 - τ') * τ₀ = ((1 - τ') * τ₀) * (cκ κ * κ) := by ring
          _ ≤ ((1 - τ') * τ₀) * m'.im := mul_le_mul_of_nonneg_left hm'ge2 (mul_nonneg (by linarith) hτ₀pos.le)
          _ = (1 - τ') * m'.im * τ₀ := by ring
      have a3 : (cκ κ * κ) * (1 - τ₀) * τ' ≤ (cκ κ * κ) * (1 - τ') * τ₀ := by
        have h4 : (1 - τ₀) * τ' ≤ (1 - τ') * τ₀ := by nlinarith
        calc (cκ κ * κ) * (1 - τ₀) * τ' = (cκ κ * κ) * ((1 - τ₀) * τ') := by ring
          _ ≤ (cκ κ * κ) * ((1 - τ') * τ₀) := mul_le_mul_of_nonneg_left h4 hc0
          _ = (cκ κ * κ) * (1 - τ') * τ₀ := by ring
      linarith
    exact le_of_mul_le_mul_right hmul (mul_pos hτ₀pos hτ'pos)


/-- `BAFlowMember` is proved: the finite modification of a member satisfies `BAFlow` at `(c_κ κ, ε/2)`. -/
theorem BAFlowMember_holds (d : ℕ) : BAFlowMember d := by
  intro κ ε 𝔡 hκ hε h𝔡
  refine ⟨cκ κ * κ, ε / 2, mul_pos (cκ_pos hκ) hκ, ?_, by positivity, by linarith, ?_⟩
  · calc cκ κ * κ ≤ 1 * κ := mul_le_mul_of_nonneg_right (cκ_le_one κ) hκ.le
      _ = κ := one_mul _
  intro 𝔠 sz z hflow hlam c₁ hc₁ hc₁' hwin z' hz'
  have hNtend : Tendsto (fun n => ((sz.size n : ℕ) : ℝ)) atTop atTop := hflow.1.2.2.1
  have hlim : Tendsto (fun n => ((sz.size n : ℕ) : ℝ) ^ (-(ε / 2))) atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop (by positivity)).comp hNtend
  have hev : ∀ᶠ n in atTop, ((sz.size n : ℕ) : ℝ) ^ (-(ε / 2)) < cκ κ * κ :=
    (tendsto_order.1 hlim).2 _ (mul_pos (cκ_pos hκ) hκ)
  obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.mp hev
  refine ⟨n₀, hflow.1, fun n => ?_⟩
  have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
  have hNpos : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
  obtain ⟨h1, h2, h3⟩ := hflow.2 n
  by_cases hn : n < n₀
  · change BAdom d (sz.L n) (sz.size n) (sz.lam n) (cκ κ * κ) (ε / 2) (if n < n₀ then z n else z' n)
    simp only [hn, ↓reduceIte]
    refine ⟨le_trans (mul_le_of_le_one_left hκ.le (cκ_le_one κ)) h1, ?_, h3⟩
    exact le_trans (Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)) h2
  · change BAdom d (sz.L n) (sz.size n) (sz.lam n) (cκ κ * κ) (ε / 2) (if n < n₀ then z n else z' n)
    simp only [hn, ↓reduceIte]
    obtain ⟨hz0, -, -, -⟩ := BAflow_T0_bounds hκ hflow n
    have hdom := BAmember_dom_at (d := d) (L := sz.L n) (g := sz.lam n) (c₁ := c₁) (κ := κ) hκ hc₁ hc₁' (hlam n).le hz0 h3 h1
      (fun g' hlo hhi => hwin n g' hlo hhi) (hz' n).1
      (by have := (hz' n).2.1; rwa [max_eq_right (by linarith : (0 : ℝ) ≤ 1 - c₁)] at this) (hz' n).2.2
    obtain ⟨hz'0, hm', hz'1, hz'im⟩ := hdom
    refine ⟨hm', ?_, hz'1⟩
    have hge : ((sz.size n : ℕ) : ℝ) ^ (-1 + ε / 2) ≤ cκ κ * κ * ((sz.size n : ℕ) : ℝ) ^ (-1 + ε) := by
      have e : ((sz.size n : ℕ) : ℝ) ^ (-1 + ε / 2) =
          ((sz.size n : ℕ) : ℝ) ^ (-1 + ε) * ((sz.size n : ℕ) : ℝ) ^ (-(ε / 2)) := by
        rw [← Real.rpow_add hNpos]; congr 1; ring
      rw [e, mul_comm]
      exact mul_le_mul_of_nonneg_right (hn₀ n (not_lt.mp hn)).le (Real.rpow_nonneg hNpos.le _)
    calc ((sz.size n : ℕ) : ℝ) ^ (-1 + ε / 2) ≤ cκ κ * κ * ((sz.size n : ℕ) : ℝ) ^ (-1 + ε) := hge
      _ ≤ cκ κ * κ * (z n).im := mul_le_mul_of_nonneg_left h2 (mul_nonneg (cκ_pos hκ).le hκ.le)
      _ ≤ (z' n).im := hz'im

/-- `BALmaxFromLK` is a theorem: `|𝓛| ≤ |𝓛 - 𝒦| + |𝒦| ≺ B^k + B^{k-1} ≤ 2 B^{k-1} ≤ N^τ B^{k-1}` (`StochDomAt.add`, `of_le_left`, `trans`;
the band's `s1_h55` at `s ≥ 1/2`), for any carrier. -/
theorem BALmaxFromLK_holds (d : ℕ) : BALmaxFromLK d := by
  intro sz C τ hN hτ0 hτ1 hB hK hLK k hk
  have hsize : Tendsto sz.size atTop atTop := sz.tendsto_size hN
  have h₁ : StochDomAt (Sizes.seqP (sz.withLam 0)) sz.size
      (fun n (p : (Fin k → Bool) × (Fin k → Zd d (sz.L n))) ω => ‖C.L n (τ n) p.1 p.2 ω - C.K n (τ n) p.1 p.2‖)
      (fun n _ _ => (sz.Bctl n (τ n)) ^ k) := hLK k hk
  have h₂ : StochDomAt (Sizes.seqP (sz.withLam 0)) sz.size
      (fun n (p : (Fin k → Bool) × (Fin k → Zd d (sz.L n))) _ => ‖C.K n (τ n) p.1 p.2‖)
      (fun n _ _ => (sz.Bctl n (τ n)) ^ (k - 1)) := hK τ hτ0 hτ1 k hk
  have h₃ := StochDomAt.of_le_left (ξ := fun n (p : (Fin k → Bool) × (Fin k → Zd d (sz.L n))) ω => ‖C.L n (τ n) p.1 p.2 ω‖)
    (fun n p ω => norm_le_norm_sub_add _ _) (StochDomAt.add hsize h₁ h₂)
  refine StochDomAt.trans hsize h₃ ?_
  refine StochDomAt.of_eventually_empty fun ε hε => ?_
  have hN2 : ∀ᶠ n in atTop, (2 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ ε :=
    ((tendsto_rpow_atTop hε).comp hN).eventually (eventually_ge_atTop 2)
  filter_upwards [hB, hN2] with n hBn hNn
  ext ω
  simp only [badSetAt, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_exists, not_lt]
  intro p
  have hB0 : 0 ≤ sz.Bctl n (τ n) := (sz.STBctl_pos n (hτ1 n)).le
  have h1 : (sz.Bctl n (τ n)) ^ k ≤ (sz.Bctl n (τ n)) ^ (k - 1) := pow_le_pow_of_le_one hB0 hBn (Nat.sub_le k 1)
  have h2 : 0 ≤ (sz.Bctl n (τ n)) ^ (k - 1) := pow_nonneg hB0 _
  change (sz.Bctl n (τ n)) ^ k + (sz.Bctl n (τ n)) ^ (k - 1) ≤ ((sz.size n : ℕ) : ℝ) ^ ε * (sz.Bctl n (τ n)) ^ (k - 1)
  nlinarith

end Member

end RBM.BA

end
