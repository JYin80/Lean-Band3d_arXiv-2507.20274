/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.BA.ConArg
import RBM3D.BA.Step1Trivial
import RBM3D.BA.CouplingWindow
import RBM3D.BA.FlowPins
import RBM3D.Induction.Step1Setup

/-!
# Event forms of `lem_GbEXP_BA`, `BABootstrap'` and the Step 1 bridging

Paper: Lemma 8.4 (`lem_GbEXP_BA`), Lemma 8.5 (`lem_ConArg_BA`), and Step 1 of the proof of Theorem 8.2 (`lem:main_ind_BA`), which is the same as in
[RBSO1D, Section 7.1] (Truong-Yang-Yin, arXiv:2503.11382); band source: Lemma 3.1 (`lem_GbEXP`) with `(GiiGEX)` (3.2), `(GijGEX)` (3.3),
`(GavLGEX)` (3.5).  Namespace `RBM.BA`.

* section 0: the vocabulary `FlowFM.indMax`, `FlowFM.gexRHS`; the sequence forms `BAGiiGEX`,
  `BAGavLGEX`; the statements `BAGbEXPii`, `BAGbEXPav` (proved as `baGbEXPii_holds` in `BA/GreenLocal` and `baGbEXPav_holds` in `BA/GbEXPav`),
  `BAFlowMember` (proved as `BAFlowMember_holds` in `BA/Step1Fam`) and `BABootstrap'` (derived from `BAFlowMember`, `BAGbEXPii` and `BAGbEXPij'` by `baBootstrap'_of_ij'` in `BA/Step1Prime`);
* section 1: `BAFamZ_mono`, `BAFamZ_horizon`, `PrecL_congr`;
* section 2: the member transfer `baGii_member` (the event forms are
  stated per `BAFlow` sequence, a member of `Fam(t)` is not one; `BAFlowMember` and the tail
  congruence of `≺`);
* section 3: `baM_entry_le` (`‖M_xy‖ ≤ (Im m)⁻¹`) and the bounds for the event `Ω_u`;
* section 4: `baBoot_LI`, the block Anderson form of `s1_LI` (`Induction/Step1Setup`).
-/

set_option linter.style.longLine false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.style.setOption false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal

namespace RBM.BA

open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes

/-! ## 0. Vocabulary and statements -/

/-- The indicator of `{‖G_t - M‖_{max} ≤ A}` over a flow carrier (the band's `STindMax`, `Induction/Defs`, is
the case `bandFM`).  `A = W^{-ε₀}`: the event `Ω(t, ε₀)` of `lem_GbEXP_BA`. -/
def FlowFM.indMax {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (n : ℕ) (t A : ℝ) (ω : sz.SeqΩ) : ℝ :=
  if ∀ x y : Idx d (sz.L n) (sz.W n), ‖C.GM n t ω x y‖ ≤ A then 1 else 0

/-- `(GiiGEX)` (3.2) for the block Anderson flow `z` at the time sequence `t` (band `STGiiGEX`, `Induction/Defs`):
`1(Ω(t, ε₀)) ‖G_t - M‖²_max ≺ max_{a,b} 𝓛^{(2)}_{t,(-,+),(a,b)}`, `Ω = {‖G_t - M‖_{max} ≤ W^{-ε₀}}`. -/
def BAGiiGEX {d : ℕ} (sz : Sizes d) (z : ℕ → ℂ) (t : ℕ → ℝ) (ε₀ : ℝ) : Prop :=
  PrecL sz (Sizes.seqP (sz.withLam 0)) (U := fun n => Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n))
    (fun n p ω => (baFMz sz z).indMax n (t n) (((sz.W n : ℕ) : ℝ) ^ (-ε₀)) ω *
      ‖(baFMz sz z).GM n (t n) ω p.1 p.2‖ ^ 2)
    (fun n _ ω => STmaxLoop2g (baFMz sz z) n (t n) ω)

/-- `(GavLGEX)` (3.5) for the block Anderson flow under `(initialGT2)` (band `STGavLGEX`, `Induction/Defs`;
no event, as the band's). -/
def BAGavLGEX {d : ℕ} (sz : Sizes d) (z : ℕ → ℂ) (t : ℕ → ℝ) (ε₀ : ℝ) : Prop :=
  ∀ Ψ : ℕ → ℝ, (∀ᶠ n in atTop, ((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2) ≤ Ψ n) →
    (∀ᶠ n in atTop, Ψ n ≤ ((sz.W n : ℕ) : ℝ) ^ (-ε₀)) →
    STInitialGT2gL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) t ε₀ Ψ →
    PrecL sz (Sizes.seqP (sz.withLam 0)) (U := fun n => Zd d (sz.L n))
      (fun n a ω => ‖(baFMz sz z).L n (t n) (fun _ : Fin 1 => true) (fun _ => a) ω - (baFMz sz z).m n‖)
      (fun n _ _ => Ψ n ^ 2)

/-- `lem_GbEXP_BA` (Lemma 8.4), `(GiiGEX)`, event form (the printed
global form is a corollary).  The band statement `STGbEXPii` (`Induction/Defs`) with `BAFlow`, `BAflowT0`, the
carrier `baFMz sz z` and the law `seqP (sz.withLam 0)`.  It is proved as `baGbEXPii_holds` (`BA/GreenLocal`). -/
def BAGbEXPii (d : ℕ) : Prop :=
  ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z →
      ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ BAflowT0 sz z n) →
        ∀ ε₀ : ℝ, 0 < ε₀ → BAGiiGEX sz z t ε₀

/-- `lem_GbEXP_BA` (Lemma 8.4), `(GavLGEX)` (band statement `STGbEXPav`, `Induction/Defs`).  It is proved as `baGbEXPav_holds` (`BA/GbEXPav`). -/
def BAGbEXPav (d : ℕ) : Prop :=
  ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z →
      ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ BAflowT0 sz z n) →
        ∀ ε₀ : ℝ, 0 < ε₀ → BAGavLGEX sz z t ε₀

/-- The finite modification of a member: `Im z' ≥ c(κ) Im z` for a member of `Fam(0)`, so `BAFlow` holds for
`z'` at `(κ', ε')` for all `n ≥ n₀`; put the main flow `z` back at `n < n₀`.  It is proved as `BAFlowMember_holds` (`BA/Step1Fam`). -/
def BAFlowMember (d : ℕ) : Prop :=
  ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∃ κ' ε' : ℝ, 0 < κ' ∧ κ' ≤ κ ∧ 0 < ε' ∧ ε' ≤ ε ∧
      ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z → (∀ n, 0 < sz.lam n) →
        ∀ c₁ : ℝ, 0 < c₁ → c₁ ≤ 1 / 2 → BAWinBulk sz z c₁ κ →
          ∀ z' : ℕ → ℂ, BAFamZ sz z c₁ (fun _ => 0) z' →
            ∃ n₀ : ℕ, BAFlow sz κ' ε' 𝔠 𝔡 (fun n => if n < n₀ then z n else z' n)

/-- The BA bootstrap (the content of "same as [RBSO1D, Section 7.1]" for Step 1; band
`step1TargetV3_holds`, `Induction/Step1`): Step 1 for one member `z'` of `Fam(t)` from its own
`ML:Kbound`, `(a)`, `(c)` at `s`, `(con_st_ind)`, and the ConArg outputs of `lem_ConArg_BA` for the member at every
time sequence `u ∈ [s₁, max(t, 1 - c₁)]`, `s₁ = max(s, 1 - c₁)` (the range `[s₁, t]` is empty as soon as
`t n < 1 - c₁` at one `n`; below `1 - c₁` the loop bound is deterministic, `BATrivialLmax`).  The ConArg output is in the event form
(`BAConArgLoop''` for every `C₀ > 0`). -/
def BABootstrap' (d : ℕ) : Prop :=
  ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ 𝔠d : ℝ, 0 < 𝔠d → 𝔠d ≤ 1 / 100 →
      ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z → (∀ n, 0 < sz.lam n) →
        ∀ c₁ : ℝ, 0 < c₁ → c₁ ≤ 1 / 2 → BAWinBulk sz z c₁ κ →
          ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n ≤ BAflowT0 sz z n) → (∀ n, s n < t n) →
            (∀ n, t n ≤ BAflowT0 sz z n) →
            ∀ z' : ℕ → ℂ, BAFamZ sz z c₁ t z' →
              STKboundgL (baFMz sz z') (Sizes.seqP (sz.withLam 0)) →
              STLKgL (baFMz sz z') (Sizes.seqP (sz.withLam 0)) s →
              STLocalMaxgL (baFMz sz z') (Sizes.seqP (sz.withLam 0)) s → STConStInd sz 𝔠d s t →
              (∀ u : ℕ → ℝ, (∀ n, max (s n) (1 - c₁) ≤ u n) → (∀ n, u n ≤ max (t n) (1 - c₁)) →
                (∀ C₀ : ℝ, 0 < C₀ → ∀ k : ℕ, 2 ≤ k →
                    BAConArgLoop'' sz z' (fun n => max (s n) (1 - c₁)) u k C₀) ∧
                  BAConArgVec sz z' (fun n => max (s n) (1 - c₁)) u) →
              STStep1LoopgL (baFMz sz z') (Sizes.seqP (sz.withLam 0)) s t ∧
                STStep1WeakgL (baFMz sz z') (Sizes.seqP (sz.withLam 0)) s t

/-! ## 1. Elementary facts about the families -/

section Family

variable {d : ℕ}

/-- The families decrease in time: `Fam(t) ⊆ Fam(s)` for `s ≤ t`. -/
theorem BAFamZ_mono {sz : Sizes d} {z : ℕ → ℂ} {c₁ : ℝ} {s t : ℕ → ℝ} {z' : ℕ → ℂ} (hst : ∀ n, s n ≤ t n)
    (h : BAFamZ sz z c₁ t z') : BAFamZ sz z c₁ s z' := fun n =>
  ⟨(h n).1, le_trans (min_le_min le_rfl (max_le_max (hst n) le_rfl)) (h n).2.1, (h n).2.2⟩

/-- Every member of `Fam(u)` has the horizon `t₀(z') ≥ u` (when
`u ≤ t₀(z)`): the member runs up to the time `u`. -/
theorem BAFamZ_horizon {sz : Sizes d} {z : ℕ → ℂ} {c₁ : ℝ} {u : ℕ → ℝ} {z' : ℕ → ℂ}
    (hu : ∀ n, u n ≤ BAflowT0 sz z n) (h : BAFamZ sz z c₁ u z') (n : ℕ) : u n ≤ BAflowT0 sz z' n :=
  le_trans (le_min (hu n) (le_max_left _ _)) (h n).2.1

/-- `≺` depends only on the tail: `ξ, ζ` and `ξ', ζ'` equal for `n ≥ n₀`
give the same `PrecL`. -/
theorem PrecL_congr {sz : Sizes d} {μ : Measure sz.SeqΩ} {U : ℕ → Type*} {ξ ζ ξ' ζ' : ∀ n, U n → sz.SeqΩ → ℝ}
    (h : ∀ᶠ n in atTop, ξ n = ξ' n ∧ ζ n = ζ' n) : PrecL sz μ ξ ζ ↔ PrecL sz μ ξ' ζ' := by
  unfold PrecL StochDomAt
  refine forall_congr' fun τ => forall_congr' fun hτ => forall_congr' fun D => forall_congr' fun hD => ?_
  refine eventually_congr ?_
  filter_upwards [h] with n hn
  obtain ⟨h1, h2⟩ := hn
  simp only [badSetAt, h1, h2]

end Family

/-! ## 2. The member transfer -/

section Member

variable {d : ℕ}

private theorem Boot_BAflowT0_congr (sz : Sizes d) {z₁ z₂ : ℕ → ℂ} {n : ℕ} (h : z₁ n = z₂ n) :
    BAflowT0 sz z₁ n = BAflowT0 sz z₂ n := by
  unfold BAflowT0; rw [h]

private theorem Boot_BAflowEs_congr (sz : Sizes d) {z₁ z₂ : ℕ → ℂ} {n : ℕ} (h : z₁ n = z₂ n) :
    BAflowEs sz z₁ n = BAflowEs sz z₂ n := by
  unfold BAflowEs; rw [h]

private theorem Boot_BAflowLam0_congr (sz : Sizes d) {z₁ z₂ : ℕ → ℂ} {n : ℕ} (h : z₁ n = z₂ n) :
    BAflowLam0 sz z₁ n = BAflowLam0 sz z₂ n := by
  unfold BAflowLam0; rw [Boot_BAflowT0_congr sz h]

/-- The carrier `baFM` at the index `n` depends on `(lam0 n, E n)` only (restricted to the
fields used here). -/
private theorem Boot_baFM_eqAt (sz : Sizes d) {lam0 lam0' E E' : ℕ → ℝ} {n : ℕ} (hl : lam0 n = lam0' n)
    (hE : E n = E' n) :
    (baFM sz lam0 E).L n = (baFM sz lam0' E').L n ∧ (baFM sz lam0 E).G n = (baFM sz lam0' E').G n ∧
      (baFM sz lam0 E).M n = (baFM sz lam0' E').M n := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp only [baFM, BALloop, BAGt, BAMfine, BAmF, Sizes.seqHflowBA, hl, hE]

/-- The carrier of a spectral sequence at the index `n` depends on `z n` only. -/
private theorem Boot_baFMz_eqAt (sz : Sizes d) {z₁ z₂ : ℕ → ℂ} {n : ℕ} (h : z₁ n = z₂ n) :
    (baFMz sz z₁).L n = (baFMz sz z₂).L n ∧ (baFMz sz z₁).G n = (baFMz sz z₂).G n ∧
      (baFMz sz z₁).M n = (baFMz sz z₂).M n :=
  Boot_baFM_eqAt sz (Boot_BAflowLam0_congr sz h) (Boot_BAflowEs_congr sz h)

/-- The finite modification of a member of `Fam(t)` (`BAFlowMember` and `BAFamZ_mono`): for `0 ≤ u ≤ t ≤ t₀(z)`
there are `κ', ε' > 0` and a sequence `z''` with `BAFlow sz κ' ε' 𝔠 𝔡 z''`, `u ≤ t₀(z'')` and `z'' n = z' n` for all
`n ≥ n₀`. -/
private theorem Boot_member {d : ℕ} (hmem : BAFlowMember d) {κ ε 𝔡 : ℝ} (hκ : 0 < κ) (hε : 0 < ε) (h𝔡 : 0 < 𝔡)
    {𝔠 : ℝ} {sz : Sizes d} {z : ℕ → ℂ} (hflow : BAFlow sz κ ε 𝔠 𝔡 z) (hlam : ∀ n, 0 < sz.lam n)
    {c₁ : ℝ} (hc₁ : 0 < c₁) (hc₁' : c₁ ≤ 1 / 2) (hwin : BAWinBulk sz z c₁ κ)
    {t : ℕ → ℝ} (htT : ∀ n, t n ≤ BAflowT0 sz z n) {z' : ℕ → ℂ} (hfam : BAFamZ sz z c₁ t z')
    {u : ℕ → ℝ} (hu0 : ∀ n, 0 ≤ u n) (hut : ∀ n, u n ≤ t n) :
    ∃ (κ' ε' : ℝ) (z'' : ℕ → ℂ), 0 < κ' ∧ 0 < ε' ∧ BAFlow sz κ' ε' 𝔠 𝔡 z'' ∧
      (∀ n, u n ≤ BAflowT0 sz z'' n) ∧ (∀ᶠ n in atTop, z'' n = z' n) := by
  obtain ⟨κ', ε', hκ'0, -, hε'0, -, H⟩ := hmem κ ε 𝔡 hκ hε h𝔡
  have hfam0 : BAFamZ sz z c₁ (fun _ => 0) z' :=
    BAFamZ_mono (fun n => (hu0 n).trans (hut n)) hfam
  obtain ⟨n₀, hflow'⟩ := H 𝔠 sz z hflow hlam c₁ hc₁ hc₁' hwin z' hfam0
  refine ⟨κ', ε', fun n => if n < n₀ then z n else z' n, hκ'0, hε'0, hflow', ?_, ?_⟩
  · intro n
    by_cases hn : n < n₀
    · have h1 : BAflowT0 sz (fun n => if n < n₀ then z n else z' n) n = BAflowT0 sz z n := by
        unfold BAflowT0; simp only [hn, ↓reduceIte]
      rw [h1]
      exact (hut n).trans (htT n)
    · have h1 : BAflowT0 sz (fun n => if n < n₀ then z n else z' n) n = BAflowT0 sz z' n := by
        unfold BAflowT0; simp only [hn, ↓reduceIte]
      rw [h1]
      exact BAFamZ_horizon (fun n => (hut n).trans (htT n)) (BAFamZ_mono hut hfam) n
  · exact Filter.eventually_atTop.mpr ⟨n₀, fun n hn => by simp [not_lt.mpr hn]⟩

/-- `baGii_member`: the event form `(GiiGEX)` at every member `z'` of `Fam(t)` and every
`0 ≤ u ≤ t`.  `BAFamZ_mono` and `BAFlowMember` give `n₀` and `BAFlow sz κ' ε' 𝔠 𝔡 z''`, `z'' = z` below `n₀` and `z'`
from `n₀` on; `u ≤ t₀(z'')` (`BAFamZ_horizon` from `n₀` on); the statement `BAGbEXPii` at `z''`; back to `z'` by `PrecL_congr`
(the carriers of `z''` and `z'` agree for `n ≥ n₀`). -/
theorem baGii_member (d : ℕ) :
    BAGbEXPii d → BAFlowMember d →
    ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
      ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z → (∀ n, 0 < sz.lam n) →
        ∀ c₁ : ℝ, 0 < c₁ → c₁ ≤ 1 / 2 → BAWinBulk sz z c₁ κ →
          ∀ t : ℕ → ℝ, (∀ n, t n ≤ BAflowT0 sz z n) → ∀ z' : ℕ → ℂ, BAFamZ sz z c₁ t z' →
            ∀ u : ℕ → ℝ, (∀ n, 0 ≤ u n) → (∀ n, u n ≤ t n) → ∀ ε₀ : ℝ, 0 < ε₀ → BAGiiGEX sz z' u ε₀ := by
  intro hii hmem κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow hlam c₁ hc₁ hc₁' hwin t htT z' hfam u hu0 hut ε₀ hε₀
  obtain ⟨κ', ε', z'', hκ', hε', hfl', hhor, hev⟩ :=
    Boot_member hmem hκ hε h𝔡 hflow hlam hc₁ hc₁' hwin htT hfam hu0 hut
  have h := hii κ' ε' 𝔡 hκ' hε' h𝔡 𝔠 sz z'' hfl' u hu0 hhor ε₀ hε₀
  unfold BAGiiGEX at h ⊢
  refine (PrecL_congr ?_).mp h
  filter_upwards [hev] with n hn
  obtain ⟨hL, hG, hM⟩ := Boot_baFMz_eqAt sz hn
  refine ⟨?_, ?_⟩
  · funext p ω
    simp only [FlowFM.indMax, FlowFM.GM, hG, hM]
    rfl
  · funext p ω
    simp only [STmaxLoop2g, hL]

end Member

/-! ## 3. `‖M_xy‖ ≤ (Im m)⁻¹` and the event `Ω_u` -/

section MEntry

variable {d : ℕ}

private theorem Boot_PsiI_herm (sz : Sizes d) (lam0 : ℕ → ℝ) (n : ℕ) :
    (((lam0 n : ℝ) : ℂ) • PsiI d (sz.L n) (sz.W n)).IsHermitian := by
  unfold IsHermitian
  rw [conjTranspose_smul, (PsiI_isHermitian d _ _).eq,
    show star ((lam0 n : ℝ) : ℂ) = ((lam0 n : ℝ) : ℂ) from Complex.conj_ofReal _]

/-- `baM_entry_le`: the entries of `M = Mres(g₀ Ψ, E, m)` are at most `(Im m)⁻¹`: `g₀ Ψ` is
Hermitian (`g₀` real), `Im(E + m) = Im m > 0`, and the entries of the resolvent of a Hermitian matrix at a point of
imaginary part `η` are at most `|η|⁻¹` (`norm_inverse_entry_le`, `Analysis/Resolvent`). -/
theorem baM_entry_le (d : ℕ) :
    ∀ (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ), 0 < (BAmF sz lam0 E n).im →
      ∀ x y : Idx d (sz.L n) (sz.W n), ‖(baFM sz lam0 E).M n x y‖ ≤ ((BAmF sz lam0 E n).im)⁻¹ := by
  intro sz lam0 E n hm x y
  have him : ((E n : ℂ) + BAmF sz lam0 E n).im ≠ 0 := by
    simp only [Complex.add_im, Complex.ofReal_im, zero_add]
    exact hm.ne'
  have h := norm_inverse_entry_le (Boot_PsiI_herm sz lam0 n) him x y
  have habs : |((E n : ℂ) + BAmF sz lam0 E n).im| = (BAmF sz lam0 E n).im := by
    simp only [Complex.add_im, Complex.ofReal_im, zero_add]
    exact abs_of_pos hm
  rw [habs] at h
  change ‖BAMfine sz lam0 E n x y‖ ≤ _
  unfold BAMfine Mres
  simpa using h

/-- At `t = 0` the flow is `H_0 = g₀ Ψ` and `z_0 = E + m`, so `G_0 = M`. -/
private theorem Boot_GM_zero (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ) (ω : sz.SeqΩ)
    (x y : Idx d (sz.L n) (sz.W n)) : (baFM sz lam0 E).GM n 0 ω x y = 0 := by
  have hH : sz.seqHflowBA lam0 n 0 ω = ((lam0 n : ℝ) : ℂ) • PsiI d (sz.L n) (sz.W n) := by
    ext i j
    have h : (sz.withLam 0).seqHflow n 0 ω i j = 0 := by
      have h0 : (sz.withLam 0).seqHflow n 0 ω = 0 := by simp [Sizes.seqHflow]
      rw [h0]
      rfl
    simp [Sizes.seqHflowBA, h]
  change BAGt sz lam0 E n 0 ω x y - BAMfine sz lam0 E n x y = 0
  unfold BAGt BAMfine Mres
  rw [hH]
  have hz : ztOf (BAmF sz lam0 E n) (E n) 0 = (E n : ℂ) + BAmF sz lam0 E n := by simp [ztOf]
  rw [hz]
  simp [Gres]

end MEntry

/-! ## 4. `baBoot_LI`: the block Anderson form of `s1_LI` (`Induction/Step1Setup`) -/

section Calculus

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {size : ℕ → ℕ} {U : ℕ → Type*}
  {ξ ζ ξ' ζ₁ : ∀ l, U l → Ω → ℝ}

/-- A pointwise bound `ξ ≤ K ζ` (eventually in `l`) gives `ξ ≺ ζ` (constants are absorbed). -/
private theorem Boot_prec_of_ev_le (hsize : Tendsto size atTop atTop) {K : ℝ} (hK : 0 ≤ K)
    (hζ : ∀ l u ω, 0 ≤ ζ l u ω) (h : ∀ᶠ l in atTop, ∀ u ω, ξ l u ω ≤ K * ζ l u ω) :
    StochDomAt P size ξ ζ := by
  refine StochDomAt.of_subset (StochDomAt.const_mul_left hsize hK hζ (StochDomAt.refl hsize hζ))
    fun τ hτ => ⟨τ, hτ, ?_⟩
  filter_upwards [h] with l hl
  rintro ω ⟨u, hu⟩
  exact ⟨u, lt_of_lt_of_le hu (hl u ω)⟩

/-- The glue of two index sets per `n` (the shape of `s1_pt_of_ev_or` in the band proof): for each large `n`, either
`ξ ≤ ξ'` and `ζ₁ ≤ Ka ζ` (`ξ'` dominated by `ζ₁`), or `ξ ≤ Kb ζ` surely. -/
private theorem Boot_prec_cases (hsize : Tendsto size atTop atTop) {Ka Kb : ℝ}
    (hζ : ∀ l u ω, 0 ≤ ζ l u ω) (h : StochDomAt P size ξ' ζ₁)
    (hc : ∀ᶠ l in atTop, (∀ u ω, ξ l u ω ≤ ξ' l u ω ∧ ζ₁ l u ω ≤ Ka * ζ l u ω) ∨
      (∀ u ω, ξ l u ω ≤ Kb * ζ l u ω)) :
    StochDomAt P size ξ ζ := by
  refine StochDomAt.of_subset h fun τ hτ => ⟨τ / 2, half_pos hτ, ?_⟩
  filter_upwards [hc, hsize.eventually (eventually_le_rpow Ka (half_pos hτ)),
    hsize.eventually (eventually_le_rpow Kb hτ)] with l hcl hKa hKb
  rintro ω ⟨u, hu⟩
  rcases hcl with hA | hB
  · obtain ⟨h1, h2⟩ := hA u ω
    refine ⟨u, ?_⟩
    have hpos : 0 ≤ (size l : ℝ) ^ (τ / 2) := Real.rpow_nonneg (Nat.cast_nonneg _) _
    have hz := hζ l u ω
    calc (size l : ℝ) ^ (τ / 2) * ζ₁ l u ω
        ≤ (size l : ℝ) ^ (τ / 2) * (Ka * ζ l u ω) := mul_le_mul_of_nonneg_left h2 hpos
      _ ≤ (size l : ℝ) ^ (τ / 2) * ((size l : ℝ) ^ (τ / 2) * ζ l u ω) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hKa hz) hpos
      _ = (size l : ℝ) ^ τ * ζ l u ω := by
          rw [← mul_assoc, UnifDetDom.rpow_half_mul_rpow_half (size l) hτ]
      _ < ξ l u ω := hu
      _ ≤ ξ' l u ω := h1
  · exfalso
    have h3 : ξ l u ω ≤ (size l : ℝ) ^ τ * ζ l u ω :=
      (hB u ω).trans (mul_le_mul_of_nonneg_right hKb (hζ l u ω))
    exact absurd hu (not_lt.2 h3)

end Calculus

section LI

variable {d : ℕ}

private theorem Boot_BAm_im_bounds (d L : ℕ) [NeZero L] (g : ℝ) (z : ℂ) (hz : 0 ≤ z.im) :
    0 ≤ (BAm d L g z).im ∧ (BAm d L g z).im ≤ 1 := by
  by_cases h : ∃ m, BASelf d L g z m
  · have hs := BAm_spec h
    exact ⟨hs.1.le, (Complex.im_le_norm _).trans (BAself_norm_le_one d L g z _ hz hs)⟩
  · have h0 : BAm d L g z = 0 := by
      unfold BAm
      simp [h]
    rw [h0]
    simp

private theorem Boot_omegaC_bounds {sz : Sizes d} (C : FlowFM sz) (n : ℕ) (t C₀ : ℝ) (ω : sz.SeqΩ) :
    0 ≤ C.omegaC n t C₀ ω ∧ C.omegaC n t C₀ ω ≤ 1 := by
  unfold FlowFM.omegaC
  split_ifs <;> norm_num

private theorem Boot_seqHflowBA_herm (sz : Sizes d) (lam0 : ℕ → ℝ) (n : ℕ) (u : ℝ) (ω : sz.SeqΩ) :
    (sz.seqHflowBA lam0 n u ω).IsHermitian := by
  unfold Sizes.seqHflowBA
  refine IsHermitian.add ?_ (Sizes.seqHflow_isHermitian (sz.withLam 0) n u ω)
  unfold IsHermitian
  rw [conjTranspose_smul, (PsiI_isHermitian d _ _).eq,
    show star (lam0 n : ℂ) = (lam0 n : ℂ) from Complex.conj_ofReal _]

section BaseCase

variable {L W : ℕ} [NeZero L] [NeZero W]

/-- `|⟨M E_b⟩| ≤ K` if every diagonal entry of `M` has modulus `≤ K` (copy of the private
`ConArg_norm_trace_mul_Eblk_le_of_diag`, `BA/ConArg`). -/
private theorem Boot_norm_trace_mul_Eblk_le_of_diag
    (M : Matrix (Vtx d L W) (Vtx d L W) ℂ) (b : Zd d L) {K : ℝ}
    (hM : ∀ p, ‖M p p‖ ≤ K) : ‖trace (M * Eblk d L W b)‖ ≤ K := by
  rw [Ind.Eblk_eq_diagonal_bw, trace]
  simp only [diag_apply, mul_diagonal]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ p, ‖M p p * ((Ind.bw b p : ℝ) : ℂ)‖ ≤ ∑ p, K * Ind.bw b p := by
        refine Finset.sum_le_sum fun p _ => ?_
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Ind.bw_nonneg b p)]
        exact mul_le_mul_of_nonneg_right (hM p) (Ind.bw_nonneg b p)
    _ = K := by rw [← Finset.mul_sum, Ind.sum_bw, mul_one]

omit [NeZero W] in
/-- `G(-) = G(+)ᴴ` for Hermitian `H` (copy of the private `ConArg_Gres_false`, `BA/ConArg`). -/
private theorem Boot_Gres_false {H : Matrix (Vtx d L W) (Vtx d L W) ℂ} (hH : H.IsHermitian)
    (z : ℂ) : Gres H z false = (Gres H z true)ᴴ := by
  unfold Gres
  simp only [Bool.false_eq_true, ite_false, ite_true]
  rw [← Matrix.nonsing_inv_eq_ringInverse, ← Matrix.nonsing_inv_eq_ringInverse,
    Matrix.conjTranspose_nonsing_inv]
  congr 1
  rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, Matrix.conjTranspose_one, hH.eq]
  rfl

/-- The diagonal of the block-indexed Green function is the diagonal of the fine one (copy of the private
`ConArg_gres_blockMat_true`, `BA/ConArg`). -/
private theorem Boot_gres_blockMat_true (H : Matrix (Idx d L W) (Idx d L W) ℂ)
    (z : ℂ) (x y : Vtx d L W) :
    Gres (blockMat d L W H) z true x y =
      Gres H z true ((splitEquiv d L W).symm x) ((splitEquiv d L W).symm y) := by
  unfold Gres blockMat
  simp only [ite_true]
  have e1 : H.submatrix (splitEquiv d L W).symm (splitEquiv d L W).symm -
        z • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ) =
      (H - z • (1 : Matrix (Idx d L W) (Idx d L W) ℂ)).submatrix (splitEquiv d L W).symm
        (splitEquiv d L W).symm := by
    ext i j
    simp [Matrix.submatrix_apply, Matrix.one_apply]
  rw [e1, ← Matrix.nonsing_inv_eq_ringInverse, ← Matrix.nonsing_inv_eq_ringInverse,
    Matrix.inv_submatrix_equiv]
  rfl

end BaseCase

/-- `k = 1`: `|𝓛^{(1)}_{t,σ,a}| = |tr(G E_a)| ≤ max_x |G_{xx}|` (`E_a` has total weight `1`). -/
private theorem Boot_L_one_le (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ) (t : ℝ) (σ : Fin 1 → Bool)
    (a : Fin 1 → Zd d (sz.L n)) (ω : sz.SeqΩ) {K : ℝ}
    (hK : ∀ x : Idx d (sz.L n) (sz.W n),
      ‖Gres (sz.seqHflowBA lam0 n t ω) (ztOf (BAmF sz lam0 E n) (E n) t) true x x‖ ≤ K) :
    ‖(baFM sz lam0 E).L n t σ a ω‖ ≤ K := by
  change ‖loopFine d (sz.L n) (sz.W n) (sz.seqHflowBA lam0 n t ω) (ztOf (BAmF sz lam0 E n) (E n) t) σ a‖ ≤ K
  unfold loopFine
  rw [loopM_eq_loopL]
  have e : loopOf σ a = ⟨[σ 0], [a 0]⟩ := by
    unfold loopOf
    simp [List.ofFn_succ]
  rw [e]
  have e2 : loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (sz.seqHflowBA lam0 n t ω))
      (ztOf (BAmF sz lam0 E n) (E n) t) ⟨[σ 0], [a 0]⟩ =
      trace (Gres (blockMat d (sz.L n) (sz.W n) (sz.seqHflowBA lam0 n t ω))
        (ztOf (BAmF sz lam0 E n) (E n) t) (σ 0) * Eblk d (sz.L n) (sz.W n) (a 0)) := by
    simp [loopL]
  rw [e2]
  have hH : (blockMat d (sz.L n) (sz.W n) (sz.seqHflowBA lam0 n t ω)).IsHermitian :=
    (Boot_seqHflowBA_herm sz lam0 n t ω).submatrix _
  refine Boot_norm_trace_mul_Eblk_le_of_diag _ (a 0) fun p => ?_
  have hp : ‖Gres (blockMat d (sz.L n) (sz.W n) (sz.seqHflowBA lam0 n t ω))
      (ztOf (BAmF sz lam0 E n) (E n) t) true p p‖ ≤ K := by
    rw [Boot_gres_blockMat_true]
    exact hK _
  generalize σ 0 = s
  cases s
  · rw [Boot_Gres_false hH, conjTranspose_apply, norm_star]
    exact hp
  · exact hp

/-- `1(Ω_t) |𝓛^{(1)}_{t,σ,a}| ≤ C₀` surely (`Ω_t = {‖G_t‖_{max} ≤ C₀}`). -/
private theorem Boot_omegaC_L_one_le (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ) (t C₀ : ℝ) (hC₀ : 0 ≤ C₀)
    (σ : Fin 1 → Bool) (a : Fin 1 → Zd d (sz.L n)) (ω : sz.SeqΩ) :
    (baFM sz lam0 E).omegaC n t C₀ ω * ‖(baFM sz lam0 E).L n t σ a ω‖ ≤ C₀ := by
  unfold FlowFM.omegaC
  split_ifs with h
  · rw [one_mul]
    exact Boot_L_one_le sz lam0 E n t σ a ω fun x => h x x
  · rw [zero_mul]
    exact hC₀

/-- The arithmetic of case (a): `(1 - s₁) Im m_s / ((1 - u) Im m') · B_{s₁} ≤ κ⁻¹ ((1 - s)/(1 - u)) B_s` from
`Im m_s ≤ 1`, `Im m' ≥ κ` and `(1 - s₁) B_{s₁} ≤ (1 - s) B_s`. -/
private theorem Boot_arith_a {x₀ x₁ y B₀ B₁ im₁ im₂ κ : ℝ} (hκ : 0 < κ) (hy : 0 < y) (hx₁ : 0 ≤ x₁)
    (him₁ : 0 ≤ im₁) (him₁' : im₁ ≤ 1) (him₂ : κ ≤ im₂) (hB₁ : 0 ≤ B₁) (hmono : x₁ * B₁ ≤ x₀ * B₀) :
    ((x₁ * im₁) / (y * im₂)) * B₁ ≤ κ⁻¹ * ((x₀ / y) * B₀) ∧ 0 ≤ ((x₁ * im₁) / (y * im₂)) * B₁ := by
  have him₂0 : 0 < im₂ := lt_of_lt_of_le hκ him₂
  have hden : 0 < y * im₂ := mul_pos hy him₂0
  refine ⟨?_, by positivity⟩
  rw [div_mul_eq_mul_div, div_le_iff₀ hden]
  have h1 : x₁ * im₁ * B₁ ≤ x₁ * B₁ := by
    have := mul_le_mul_of_nonneg_right him₁' (mul_nonneg hx₁ hB₁)
    nlinarith
  have h2 : x₀ * B₀ ≤ κ⁻¹ * (x₀ / y * B₀) * (y * im₂) := by
    have hx0B0 : 0 ≤ x₀ * B₀ := le_trans (mul_nonneg hx₁ hB₁) hmono
    have e : κ⁻¹ * (x₀ / y * B₀) * (y * im₂) = (x₀ * B₀) * (κ⁻¹ * im₂) := by
      field_simp
    rw [e]
    have : 1 ≤ κ⁻¹ * im₂ := by
      rw [← div_eq_inv_mul, one_le_div hκ]
      exact him₂
    nlinarith
  linarith

/-- `baBoot_LI` (the block Anderson form of `s1_LI`, `Induction/Step1Setup`): the
event-form loop bound of a member `z'` of `Fam(t)` at every time sequence `u ∈ [s, t]`, every `C₀ > 0`, every `k ≥ 1`,
from the ConArg output on `[s₁, max(t, 1 - c₁)]`, `s₁ = max(s, 1 - c₁)` (applied at `u' = max(u, s₁)`), and the
deterministic bound below `s₁` (`baFM_loop_det`, `BAFamZ_im_m_ge`).
Per `n`: (a) `u n ≥ s₁ n`: the premise at `u' n = u n`, with `η_{s₁} = (1 - s₁) Im m(E, g_{s₁}) ≤ 1 - s₁`
(`BAself_norm_le_one`), `η_u ≥ (1 - u) κ` (`BAFamZ_im_m_ge`) and `(1 - s₁) B_{s₁} ≤ (1 - s) B_s` (`STBctl_xmono`);
the constant is `κ^{-(k-1)}`.  (b) `u n < s₁ n`, so `u n < 1 - c₁`: `η_u ≥ c₁ κ`, `baFM_loop_det`, `W^{-d} ≤ (𝔡⁻² + 1) B_s`
(`s1_Wd_le_Bctl`) and `(1 - s)/(1 - u) ≥ 1`.  (c) `k = 1`: `Ω_u |𝓛^{(1)}| ≤ C₀` surely.  The two index sets are glued
per `n` (`Boot_prec_cases`). -/
theorem baBoot_LI (d : ℕ) :
    ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
      ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z → (∀ n, 0 < sz.lam n) →
        ∀ c₁ : ℝ, 0 < c₁ → c₁ ≤ 1 / 2 → BAWinBulk sz z c₁ κ →
          ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n ≤ t n) → (∀ n, t n ≤ BAflowT0 sz z n) →
            ∀ z' : ℕ → ℂ, BAFamZ sz z c₁ t z' →
              (∀ u : ℕ → ℝ, (∀ n, max (s n) (1 - c₁) ≤ u n) → (∀ n, u n ≤ max (t n) (1 - c₁)) →
                ∀ C₀ : ℝ, 0 < C₀ → ∀ k : ℕ, 2 ≤ k →
                  BAConArgLoop'' sz z' (fun n => max (s n) (1 - c₁)) u k C₀) →
              ∀ C₀ : ℝ, 0 < C₀ → ∀ u : ℕ → ℝ, (∀ n, u n ∈ Set.Icc (s n) (t n)) → ∀ k : ℕ, 1 ≤ k →
                PrecL sz (Sizes.seqP (sz.withLam 0)) (U := fun n => (Fin k → Bool) × (Fin k → Zd d (sz.L n)))
                  (fun n p ω => (baFMz sz z').omegaC n (u n) C₀ ω * ‖(baFMz sz z').L n (u n) p.1 p.2 ω‖)
                  (fun n _ _ => ((1 - s n) / (1 - u n)) ^ (k - 1) * (sz.Bctl n (s n)) ^ (k - 1)) := by
  intro κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow hlam c₁ hc₁ hc₁' hwin s t hs0 hst htT z' hfam hcon C₀ hC₀ u hu k hk
  have hsize : Tendsto sz.size atTop atTop := Ind.s1_hsize sz hflow.1.2.2.1
  have hT1 : ∀ n, BAflowT0 sz z n < 1 := fun n => (BAflow_T0_bounds hκ hflow n).2.2.2
  have ht1 : ∀ n, t n < 1 := fun n => lt_of_le_of_lt (htT n) (hT1 n)
  have hs1 : ∀ n, s n < 1 := fun n => lt_of_le_of_lt (hst n) (ht1 n)
  have hu1 : ∀ n, u n < 1 := fun n => lt_of_le_of_lt (hu n).2 (ht1 n)
  have hBpos : ∀ n, 0 < sz.Bctl n (s n) := fun n => sz.STBctl_pos n (hs1 n)
  have hratio : ∀ n, 1 ≤ (1 - s n) / (1 - u n) := fun n => by
    rw [one_le_div (by linarith [hu1 n])]
    linarith [(hu n).1]
  have hζ0 : ∀ (n : ℕ) (_ : (Fin k → Bool) × (Fin k → Zd d (sz.L n))) (_ : sz.SeqΩ),
      0 ≤ ((1 - s n) / (1 - u n)) ^ (k - 1) * (sz.Bctl n (s n)) ^ (k - 1) := fun n _ _ =>
    mul_nonneg (pow_nonneg (le_trans zero_le_one (hratio n)) _) (pow_nonneg (hBpos n).le _)
  by_cases hk1 : k = 1
  · subst hk1
    refine Boot_prec_of_ev_le hsize hC₀.le hζ0 (Eventually.of_forall fun n p ω => ?_)
    have h := Boot_omegaC_L_one_le sz (BAflowLam0 sz z') (BAflowEs sz z') n (u n) C₀ hC₀.le p.1 p.2 ω
    have e : ((1 - s n) / (1 - u n)) ^ (1 - 1) * (sz.Bctl n (s n)) ^ (1 - 1) = 1 := by simp
    change (baFMz sz z').omegaC n (u n) C₀ ω * ‖(baFMz sz z').L n (u n) p.1 p.2 ω‖ ≤
      C₀ * (((1 - s n) / (1 - u n)) ^ (1 - 1) * (sz.Bctl n (s n)) ^ (1 - 1))
    rw [e, mul_one]
    exact h
  have hk2 : 2 ≤ k := by omega
  have hfam0 : BAFamZ sz z c₁ (fun _ => 0) z' :=
    BAFamZ_mono (fun n => (hs0 n).trans (hst n)) hfam
  have him : ∀ n, κ ≤ (BAmF sz (BAflowLam0 sz z') (BAflowEs sz z') n).im :=
    BAFamZ_im_m_ge hκ hflow hlam hc₁ hc₁' hwin hfam0
  set s₁ : ℕ → ℝ := fun n => max (s n) (1 - c₁) with hs₁def
  set u' : ℕ → ℝ := fun n => max (u n) (s₁ n) with hu'def
  have hs₁1 : ∀ n, s₁ n < 1 := fun n => max_lt (hs1 n) (by linarith)
  have hs₁s : ∀ n, s n ≤ s₁ n := fun n => le_max_left _ _
  have hP := hcon u' (fun n => le_max_right _ _)
    (fun n => max_le ((hu n).2.trans (le_max_left _ _)) (max_le_max (hst n) le_rfl)) C₀ hC₀ k hk2
  unfold BAConArgLoop'' at hP
  refine Boot_prec_cases hsize (Ka := (κ⁻¹) ^ (k - 1))
    (Kb := (c₁ * κ)⁻¹ ^ k * ((𝔡⁻¹) ^ 2 + 1) ^ (k - 1)) hζ0 hP ?_
  filter_upwards [hflow.1.2.2.2.2] with n hWO
  by_cases hA : s₁ n ≤ u n
  · left
    intro p ω
    have hu'n : u' n = u n := max_eq_left hA
    refine ⟨?_, ?_⟩
    · show (baFMz sz z').omegaC n (u n) C₀ ω * ‖(baFMz sz z').L n (u n) p.1 p.2 ω‖ ≤
        (baFMz sz z').omegaC n (u' n) C₀ ω * ‖(baFMz sz z').L n (u' n) p.1 p.2 ω‖
      rw [hu'n]
    · show (((etaOf (BAmF sz (BAlamS sz z' s₁ u') (BAflowEs sz z') n) (s₁ n)) /
          (baFMz sz z').eta n (u' n)) * sz.Bctl n (s₁ n)) ^ (k - 1) ≤
        (κ⁻¹) ^ (k - 1) * (((1 - s n) / (1 - u n)) ^ (k - 1) * (sz.Bctl n (s n)) ^ (k - 1))
      have hm : 0 ≤ (BAmF sz (BAlamS sz z' s₁ u') (BAflowEs sz z') n).im ∧
          (BAmF sz (BAlamS sz z' s₁ u') (BAflowEs sz z') n).im ≤ 1 :=
        Boot_BAm_im_bounds d (sz.L n) (BAlamS sz z' s₁ u' n) ((BAflowEs sz z' n : ℝ) : ℂ) (by simp)
      have hηs : etaOf (BAmF sz (BAlamS sz z' s₁ u') (BAflowEs sz z') n) (s₁ n) =
          (1 - s₁ n) * (BAmF sz (BAlamS sz z' s₁ u') (BAflowEs sz z') n).im := rfl
      have hηu : (baFMz sz z').eta n (u' n) =
          (1 - u n) * (BAmF sz (BAflowLam0 sz z') (BAflowEs sz z') n).im := by
        rw [hu'n]; rfl
      rw [hηs, hηu]
      have hy : 0 < 1 - u n := by linarith [hu1 n]
      have hx₁ : 0 ≤ 1 - s₁ n := by linarith [hs₁1 n]
      obtain ⟨key1, key2⟩ := Boot_arith_a hκ hy hx₁ hm.1 hm.2 (him n) (sz.STBctl_pos n (hs₁1 n)).le
        (sz.STBctl_xmono n (hs₁s n) (hs₁1 n))
      calc _ ≤ (κ⁻¹ * ((1 - s n) / (1 - u n) * sz.Bctl n (s n))) ^ (k - 1) := pow_le_pow_left₀ key2 key1 _
        _ = _ := by rw [mul_pow, mul_pow]
  · right
    intro p ω
    have hlt : u n < s₁ n := not_le.1 hA
    have hu1c : u n < 1 - c₁ := by
      rcases lt_max_iff.1 hlt with h | h
      · exact absurd h (not_lt.2 (hu n).1)
      · exact h
    have hη : c₁ * κ ≤
        (ztOf (BAmF sz (BAflowLam0 sz z') (BAflowEs sz z') n) (BAflowEs sz z' n) (u n)).im := by
      rw [ztOf_im]
      unfold etaOf
      exact mul_le_mul (by linarith) (him n) hκ.le (by linarith [hu1 n])
    have hdet := baFM_loop_det sz (BAflowLam0 sz z') (BAflowEs sz z') n (u n) (c₁ * κ)
      (by positivity) hη k hk p.1 p.2 ω
    have hlam2 : sz.lam n ^ 2 ≤ (𝔡⁻¹) ^ 2 := pow_le_pow_left₀ (hlam n).le hWO.2 2
    have hW := Ind.s1_Wd_le_Bctl sz n (hs0 n) (hs1 n)
    have hW' : (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ ((𝔡⁻¹) ^ 2 + 1) * sz.Bctl n (s n) :=
      hW.trans (mul_le_mul_of_nonneg_right (by linarith) (hBpos n).le)
    have h5 : ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹) ^ (k - 1) ≤
        (((𝔡⁻¹) ^ 2 + 1) * sz.Bctl n (s n)) ^ (k - 1) :=
      pow_le_pow_left₀ (by positivity) hW' _
    rw [mul_pow] at h5
    have hR : (sz.Bctl n (s n)) ^ (k - 1) ≤
        ((1 - s n) / (1 - u n)) ^ (k - 1) * (sz.Bctl n (s n)) ^ (k - 1) :=
      le_mul_of_one_le_left (pow_nonneg (hBpos n).le _) (one_le_pow₀ (hratio n))
    obtain ⟨-, hind1⟩ := Boot_omegaC_bounds (baFMz sz z') n (u n) C₀ ω
    change (baFMz sz z').omegaC n (u n) C₀ ω * ‖(baFMz sz z').L n (u n) p.1 p.2 ω‖ ≤
      (c₁ * κ)⁻¹ ^ k * ((𝔡⁻¹) ^ 2 + 1) ^ (k - 1) *
        (((1 - s n) / (1 - u n)) ^ (k - 1) * (sz.Bctl n (s n)) ^ (k - 1))
    calc (baFMz sz z').omegaC n (u n) C₀ ω * ‖(baFMz sz z').L n (u n) p.1 p.2 ω‖
        ≤ ‖(baFMz sz z').L n (u n) p.1 p.2 ω‖ := mul_le_of_le_one_left (norm_nonneg _) hind1
      _ ≤ (c₁ * κ)⁻¹ ^ k * ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹) ^ (k - 1) := hdet
      _ ≤ (c₁ * κ)⁻¹ ^ k * (((𝔡⁻¹) ^ 2 + 1) ^ (k - 1) * sz.Bctl n (s n) ^ (k - 1)) :=
          mul_le_mul_of_nonneg_left h5 (by positivity)
      _ ≤ (c₁ * κ)⁻¹ ^ k * (((𝔡⁻¹) ^ 2 + 1) ^ (k - 1) *
            (((1 - s n) / (1 - u n)) ^ (k - 1) * (sz.Bctl n (s n)) ^ (k - 1))) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact mul_le_mul_of_nonneg_left hR (by positivity)
      _ = _ := by ring

end LI

end RBM.BA
