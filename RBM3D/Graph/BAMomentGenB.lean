/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Graph.BAMomentGen

/-!
# The near pairs and `lem:LW_moment` at BA (part B)

Paper: the max bound (7.9) `eq:boundfxyGinf`, Lemma 7.1 (`lem:LW_moment`) and its proof.  This is
the BA counterpart of `Graph/LWMoment.lean` (Sections 9-10); part A is `Graph/BAMomentGen.lean`.

## Contents (namespace `RBM.BA`; private helpers carry the stem `BAMomentGen_`)

1. The near pairs, deterministic part: the max bound `|f_{xy}| ≤ (A/η) max_c |𝓛^{(1)}_c - m|` at
   the BA carrier (`X_c = 𝓛^{(1)}_c - m`, `BAExp14a_X_eq`; Ward and Cauchy-Schwarz,
   `lwMoment_CS`).
2. The near pairs, stochastic part: (3.4) `GavLGEX` at `Ψ'` (`baGbEXPav_holds`),
   `|f_{xy}|^p ≤ (2/η N^{τ₁} Ψ'²)^p`, `≺ → 𝔼`.
3. The statement def `BALWMomentOfAnp` and `baLWMoment_of_anp`, the BA `lem:LW_moment` from
   `lem:Anp` at the BA carrier (`BAAnpAuxG`, only as the antecedent of the statement def) and the
   path binder of `baLocReg15_holds`.
-/

set_option linter.style.longLine false
set_option linter.style.setOption false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.flexible false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedSimpArgs false

open MeasureTheory Filter Matrix

noncomputable section

namespace RBM.BA

open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes RBM.Graph

/-! ## 1. The near pairs, deterministic part -/

section Near

variable {d : ℕ} {sz : Sizes d} {z : ℕ → ℂ} {κ ε 𝔡 𝔠 : ℝ}

/-- `Σ_β (W^{-d} S^{(B)}_{[α][β]}) Ǧ_{ββ} = X_{[α]}` at the BA carrier (`S^{(B)} = I`; `BAExp14a_sumS_GM` without `t`). -/
theorem BAMomentGen_sumS (n : ℕ) (t : ℝ) (ω : sz.SeqΩ) (α : Idx d (sz.L n) (sz.W n)) :
    ∑ β, ((((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * (baFMz sz z).S n (STblk sz n α) (STblk sz n β)) * (baFMz sz z).GM n t ω β β =
      BAExp14a_X sz z n t ω (STblk sz n α) := by
  unfold BAExp14a_X
  have h : ∀ β : Idx d (sz.L n) (sz.W n),
      ((((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * (baFMz sz z).S n (STblk sz n α) (STblk sz n β)) * (baFMz sz z).GM n t ω β β =
      (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * (if β ∈ Iblk d (sz.L n) (sz.W n) (STblk sz n α) then (baFMz sz z).GM n t ω β β else 0) := by
    intro β
    have hmem : β ∈ Iblk d (sz.L n) (sz.W n) (STblk sz n α) ↔ STblk sz n α = STblk sz n β := by
      simp [Iblk, STblk, eq_comm]
    by_cases hb : β ∈ Iblk d (sz.L n) (sz.W n) (STblk sz n α)
    · have e1 : (baFMz sz z).S n (STblk sz n α) (STblk sz n β) = 1 := by
        change (1 : Matrix (Zd d (sz.L n)) (Zd d (sz.L n)) ℂ) (STblk sz n α) (STblk sz n β) = 1
        rw [← hmem.1 hb, Matrix.one_apply_eq]
      rw [e1]; simp only [hb, ↓reduceIte]; ring
    · have hnm : ¬ STblk sz n α = STblk sz n β := fun h' => hb (hmem.2 h')
      have e1 : (baFMz sz z).S n (STblk sz n α) (STblk sz n β) = 0 := by
        change (1 : Matrix (Zd d (sz.L n)) (Zd d (sz.L n)) ℂ) (STblk sz n α) (STblk sz n β) = 0
        exact Matrix.one_apply_ne hnm
      rw [e1]; simp only [hb, ↓reduceIte]; ring
  simp only [h, ← Finset.mul_sum]
  rw [Finset.sum_ite_mem, Finset.univ_inter]

/-- **The max bound, pathwise** ((7.9) `eq:boundfxyGinf`; as `lwMoment_f_le` in `Graph/LWMoment.lean`):
`‖f_{xy}‖ ≤ (A/η) μ` when `‖G_{aa}‖ ≤ A` and `‖𝓛^{(1)}_{+,b} - m‖ ≤ μ` for every block `b` (`X_b = 𝓛^{(1)}_b - m`, `BAExp14a_X_eq`; Ward
and Cauchy-Schwarz for the resolvent of `g₀ Ψ + H_t`, `lwMoment_CS`, `BAExp14a_G_green`). -/
theorem BAMomentGen_f_le (hκ : 0 < κ) (hflow : BAFlow sz κ ε 𝔠 𝔡 z) (n : ℕ) {t : ℝ} (ht0 : 0 ≤ t)
    (ht : t ≤ BAflowT0 sz z n) (ω : sz.SeqΩ) {A μ : ℝ}
    (hμ : ∀ b : Zd d (sz.L n), ‖(baFMz sz z).L n t (fun _ : Fin 1 => true) (fun _ => b) ω - (baFMz sz z).m n‖ ≤ μ)
    (hA : ∀ x : Idx d (sz.L n) (sz.W n), ‖(baFMz sz z).G n t ω x x‖ ≤ A) (x y : Idx d (sz.L n) (sz.W n)) :
    ‖LWfg (baFMz sz z) n t ω x y‖ ≤ A / (baFMz sz z).eta n t * μ := by
  obtain ⟨-, -, hmi, hzi, -⟩ := ba_G_data hκ sz hflow n ht0 ht
  have hSelf := (BAflow_real κ ε 𝔠 𝔡 sz z hflow n).1
  have hH := BAExpand_Hm_isHermitian sz n (BAflowLam0 sz z n) t ω
  have hμ0 : 0 ≤ μ := (norm_nonneg _).trans (hμ 0)
  have hX : ∀ c, ‖BAExp14a_X sz z n t ω c‖ ≤ μ := fun c => by
    rw [BAExp14a_X_eq n t ω hSelf c]; exact hμ c
  have hG : ∀ a b, (baFMz sz z).G n t ω a b =
      green (BAExpand_Hm sz n (BAflowLam0 sz z n) t ω) (ztOf (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) (BAflowEs sz z n) t) a b :=
    fun a b => by rw [BAExp14a_G_green]; rfl
  have hη : (baFMz sz z).eta n t = (ztOf (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) (BAflowEs sz z n) t).im := by
    rw [ztOf_im]; rfl
  have hCS := lwMoment_CS hH hzi (A := A) x y (by rw [← hG]; exact hA x) (by rw [← hG]; exact hA y)
  have hL : LWfg (baFMz sz z) n t ω x y = ∑ α, if α = x ∨ α = y then (0 : ℂ) else
      BAExp14a_X sz z n t ω (STblk sz n α) * (baFMz sz z).G n t ω x α * (baFMz sz z).G n t ω α y := by
    unfold LWfg
    refine Finset.sum_congr rfl fun α _ => ?_
    split_ifs
    · rfl
    · rw [← BAMomentGen_sumS (z := z) n t ω α, Finset.sum_mul, Finset.sum_mul]
  rw [hL, hη]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ α, ‖if α = x ∨ α = y then (0 : ℂ) else
        BAExp14a_X sz z n t ω (STblk sz n α) * (baFMz sz z).G n t ω x α * (baFMz sz z).G n t ω α y‖
      ≤ ∑ α, μ * (‖green (BAExpand_Hm sz n (BAflowLam0 sz z n) t ω) (ztOf (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) (BAflowEs sz z n) t) x α‖ *
          ‖green (BAExpand_Hm sz n (BAflowLam0 sz z n) t ω) (ztOf (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) (BAflowEs sz z n) t) α y‖) := by
        refine Finset.sum_le_sum fun α _ => ?_
        split_ifs
        · simp only [norm_zero]; positivity
        · rw [norm_mul, norm_mul, hG, hG, mul_assoc]
          exact mul_le_mul_of_nonneg_right (hX _) (by positivity)
    _ = μ * ∑ α, ‖green (BAExpand_Hm sz n (BAflowLam0 sz z n) t ω) (ztOf (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) (BAflowEs sz z n) t) x α‖ *
          ‖green (BAExpand_Hm sz n (BAflowLam0 sz z n) t ω) (ztOf (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) (BAflowEs sz z n) t) α y‖ := by
        rw [Finset.mul_sum]
    _ ≤ μ * (A / (ztOf (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) (BAflowEs sz z n) t).im) := mul_le_mul_of_nonneg_left hCS hμ0
    _ = A / (ztOf (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) (BAflowEs sz z n) t).im * μ := by ring

end Near

/-! ## 2. The near pairs, stochastic part -/

section NearStoch

variable {d : ℕ} {sz : Sizes d} {z : ℕ → ℂ} {κ ε 𝔡 𝔠 : ℝ} {t : ℕ → ℝ} {ε₀ C₁ C₂ C₃ : ℝ} {Cc : ℝ → ℝ} {Ψ : ℕ → ℝ}
  {Φ : ℕ → ℝ → ℝ}

/-- The near pairs: block distance `≤ K (log W)²` (as `LWMomNear` in `Graph/LWMoment.lean`). -/
def BAMomentGen_Near (sz : Sizes d) (K : ℕ) (n : ℕ) : Type :=
  {q : Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n) //
    (lwBdist d (sz.L n) (sz.W n) q.1 q.2 : ℝ) ≤ (K : ℝ) * Real.log ((sz.W n : ℕ) : ℝ) ^ 2}

/-- The entry scale for the near pairs `Ψ' = max(Φ(0), W^{-d/2})` (as `lwMoment_Psi'`). -/
def BAMomentGen_Psi' (sz : Sizes d) (Φ : ℕ → ℝ → ℝ) (n : ℕ) : ℝ :=
  max (Φ n 0) (((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2))

/-- `|X_c| ≤ η⁻¹ + 1` (`X_c` is the block average of `Ǧ_{vv}`, `|G| ≤ η⁻¹`, `|M| ≤ 1`; as `BAExp14a_X_le` without the facts record). -/
theorem BAMomentGen_X_le (hκ : 0 < κ) (hflow : BAFlow sz κ ε 𝔠 𝔡 z) (n : ℕ) {t : ℝ} (ht0 : 0 ≤ t)
    (ht : t ≤ BAflowT0 sz z n) (ω : sz.SeqΩ) (c : Zd d (sz.L n)) :
    ‖BAExp14a_X sz z n t ω c‖ ≤ ((baFMz sz z).eta n t)⁻¹ + 1 := by
  obtain ⟨-, -, -, -, -, hM1⟩ := ba_G_data hκ sz hflow n ht0 ht
  have hGM : ∀ v, ‖(baFMz sz z).GM n t ω v v‖ ≤ ((baFMz sz z).eta n t)⁻¹ + 1 := fun v => by
    unfold FlowFM.GM
    exact (norm_sub_le _ _).trans (add_le_add (BAExp14a_G_le hκ hflow n ht0 ht ω v v) (hM1 v v))
  unfold BAExp14a_X
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) ^ d := by
    have : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
    positivity
  rw [norm_mul, norm_inv, norm_pow, Complex.norm_natCast]
  calc (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * ‖∑ v ∈ Iblk d (sz.L n) (sz.W n) c, (baFMz sz z).GM n t ω v v‖
      ≤ (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * ∑ v ∈ Iblk d (sz.L n) (sz.W n) c, (((baFMz sz z).eta n t)⁻¹ + 1) :=
        mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (Finset.sum_le_sum fun v _ => hGM v)) (by positivity)
    _ = ((baFMz sz z).eta n t)⁻¹ + 1 := by
        rw [Finset.sum_const, card_Iblk, nsmul_eq_mul]
        push_cast
        field_simp

variable (hd : 3 ≤ d) (hκ : 0 < κ) (hε : 0 < ε) (h𝔡 : 0 < 𝔡) (hflow : BAFlow sz κ ε 𝔠 𝔡 z) (ht0 : ∀ n, 0 ≤ t n)
  (ht1 : ∀ n, t n ≤ BAflowT0 sz z n)
  (hassm : 0 < ε₀ ∧ LWWindow sz ε₀ Ψ ∧ STInitialGT2gL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) t ε₀ Ψ ∧
    LWClass sz ε₀ C₃ Φ ∧ LWPsiRel C₁ C₂ Cc Φ ∧
    PrecL sz (Sizes.seqP (sz.withLam 0)) (U := fun n => Bool × Zd d (sz.L n) × Zd d (sz.L n))
      (fun n p ω => ‖(baFMz sz z).L n (t n) ![p.1, !p.1] ![p.2.1, p.2.2] ω‖)
      (fun n p _ => Φ n ((zdistInf d (sz.L n) (p.2.1 - p.2.2) : ℕ) : ℝ) ^ 2))
include hd hκ hε h𝔡 hflow ht0 ht1 hassm

theorem BAMomentGen_Psi'_facts :
    ∀ᶠ n in atTop, 0 < Φ n 0 ∧ ((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2) ≤ BAMomentGen_Psi' sz Φ n ∧
      BAMomentGen_Psi' sz Φ n ≤ ((sz.W n : ℕ) : ℝ) ^ (-ε₀) ∧ BAMomentGen_Psi' sz Φ n ≤ max 1 C₃ * Φ n 0 := by
  have hcls := hassm.2.2.2.1
  filter_upwards [hcls.1, hcls.2.2, hassm.2.1] with n hpos hwin hW
  have h0 := hpos 0 le_rfl
  refine ⟨h0.1, le_max_right _ _, max_le h0.2 (hW.1.trans hW.2), max_le ?_ ?_⟩
  · calc Φ n 0 = 1 * Φ n 0 := (one_mul _).symm
      _ ≤ max 1 C₃ * Φ n 0 := mul_le_mul_of_nonneg_right (le_max_left _ _) h0.1.le
  · exact hwin.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) h0.1.le)

/-- `STmaxLoop2g ≺ Ψ'²` from `LWLoop2gL` (`Φ(r) ≤ Φ(0) ≤ Ψ'`; as `lwMoment_maxLoop2_prec`). -/
theorem BAMomentGen_maxLoop2_prec :
    PrecL sz (Sizes.seqP (sz.withLam 0)) (U := fun _ => Unit)
      (fun n _ ω => STmaxLoop2g (baFMz sz z) n (t n) ω) (fun n _ _ => BAMomentGen_Psi' sz Φ n ^ 2) := by
  apply BAMomentGen_prec_of_whp
  intro τ hτ
  refine ⟨_, BAMomentGen_whp_of_prec sz hassm.2.2.2.2.2 hτ, ?_⟩
  have hrel := hassm.2.2.2.2.1
  filter_upwards [hassm.2.2.2.1.1, BAMomentGen_Psi'_facts hd hκ hε h𝔡 hflow ht0 ht1 hassm] with n hpos hP
  intro ω hω u
  unfold STmaxLoop2g
  refine Finset.sup'_le _ _ fun q _ => ?_
  have h1 := hω (false, q.1, q.2)
  refine h1.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  have hr : (0 : ℝ) ≤ ((zdistInf d (sz.L n) (q.1 - q.2) : ℕ) : ℝ) := Nat.cast_nonneg _
  have e1 : Φ n ((zdistInf d (sz.L n) (q.1 - q.2) : ℕ) : ℝ) ≤ Φ n 0 :=
    hrel.1 n (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hr) hr
  have e2 : Φ n 0 ≤ BAMomentGen_Psi' sz Φ n := le_max_left _ _
  exact pow_le_pow_left₀ (hpos _ hr).1.le (e1.trans e2) 2

/-- `max_a |𝓛^{(1)}_{+,a} - m| ≤ N^{τ₁} Ψ'²` w.h.p. ((3.4) `GavLGEX` at `Ψ'`, `baGbEXPav_holds`; as `lwMoment_avg_whp`). -/
theorem BAMomentGen_avg_whp {τ₁ : ℝ} (hτ₁ : 0 < τ₁) :
    HighProbAt (Sizes.seqP (sz.withLam 0)) sz.size (fun n => {ω | ∀ a : Zd d (sz.L n),
      ‖(baFMz sz z).L n (t n) (fun _ : Fin 1 => true) (fun _ => a) ω - (baFMz sz z).m n‖ ≤
        ((sz.size n : ℕ) : ℝ) ^ τ₁ * BAMomentGen_Psi' sz Φ n ^ 2}) := by
  have hGav := baGbEXPav_holds d (by omega) κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow t ht0 ht1 ε₀ hassm.1
  have h := hGav (BAMomentGen_Psi' sz Φ)
    ((BAMomentGen_Psi'_facts hd hκ hε h𝔡 hflow ht0 ht1 hassm).mono fun n h => h.2.1)
    ((BAMomentGen_Psi'_facts hd hκ hε h𝔡 hflow ht0 ht1 hassm).mono fun n h => h.2.2.1)
    ⟨hassm.2.2.1.1, BAMomentGen_maxLoop2_prec hd hκ hε h𝔡 hflow ht0 ht1 hassm⟩
  exact BAMomentGen_whp_of_prec sz h hτ₁

/-- **The near pairs, in probability** ((7.9) `eq:boundfxyGinf`, the max bound; as `lwMoment_prec_near_pre` in `Graph/LWMoment.lean`): for the pairs
with block distance `≤ K (log W)²`, `|f_{xy}|^p ≤ (2/η · N^{τ₁} Ψ'²)^p` on the good event, and `Ψ'² ≤ polylog · Φ(0) Φ(|a-b|)`. -/
theorem BAMomentGen_prec_near_pre {p : ℕ} (hp0 : 0 < p) (K : ℕ) :
    PrecL sz (Sizes.seqP (sz.withLam 0)) (U := BAMomentGen_Near sz K)
      (fun n q ω => ‖(((‖LWfg (baFMz sz z) n (t n) ω q.1.1 q.1.2‖ ^ p : ℝ)) : ℂ)‖)
      (fun n q _ => BAMomentGen_R sz z t Φ p n q.1.1 q.1.2) := by
  classical
  have hε₀ := hassm.1
  have hsz : sz.SizeTendsto := hflow.1.2.2.1
  have h𝔠 : 0 < 𝔠 := hflow.1.1
  have hcls := hassm.2.2.2.1
  have hC₂ : 1 < C₂ := hassm.2.2.2.2.1.2.2.1
  have hC₁ : 1 < C₁ := hassm.2.2.2.2.1.2.1
  apply BAMomentGen_prec_of_whp
  intro τ hτ
  have hp0' : (0 : ℝ) < p := by exact_mod_cast hp0
  set τ₁ : ℝ := min (τ / (3 * p)) (𝔠 * ε₀ / 4) with hτ₁def
  have hτ₁ : 0 < τ₁ := lt_min (by positivity) (by positivity)
  refine ⟨_, HighProbAt.inter (Sizes.tendsto_size sz hsz) (BAMomentGen_entry_whp hd hκ hε h𝔡 hflow ht0 ht1 hassm hτ₁)
    (BAMomentGen_avg_whp hd hκ hε h𝔡 hflow ht0 ht1 hassm hτ₁), ?_⟩
  set M : ℝ := max 1 C₃ with hMdef
  have hM1 : 1 ≤ M := le_max_left _ _
  filter_upwards [BAMomentGen_Psi_facts hd hκ hε h𝔡 hflow ht0 ht1 hassm hτ₁.le (min_le_right _ _),
    BAMomentGen_Psi'_facts hd hκ hε h𝔡 hflow ht0 ht1 hassm, lwMoment_phi_facts hcls hassm.2.2.2.2.1,
    lwMoment_rad sz hsz K (C₂ := C₂) (by linarith) hτ₁, hsz.eventually_ge_atTop 1,
    ((tendsto_rpow_atTop hτ₁).comp hsz).eventually_ge_atTop (2 * M ^ 2 * (Cc 2 * C₁))]
    with n hPsi hPs' hph hrad hN1 hbig
  intro ω hω v
  obtain ⟨hω1, hω2⟩ := hω
  obtain ⟨hΦ0, hwin, hup⟩ := hPsi
  obtain ⟨-, -, -, hΨ'M⟩ := hPs'
  obtain ⟨hCc, hP, hcmp, -⟩ := hph
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
  set X : ℝ := ((sz.size n : ℕ) : ℝ) ^ τ₁ with hXdef
  have hX1 : 1 ≤ X := Real.one_le_rpow hN1 hτ₁.le
  have hW1 : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  obtain ⟨hη0, hη1, ht1'⟩ := BAMomentGen_eta_facts hd hκ hε h𝔡 hflow ht0 ht1 hassm n
  have hηi : 1 ≤ ((baFMz sz z).eta n (t n))⁻¹ := one_le_inv_iff₀.2 ⟨hη0, hη1⟩
  obtain ⟨-, -, -, -, -, hMle⟩ := ba_G_data hκ sz hflow n (ht0 n) (ht1 n)
  have hΨ1 : M * X * Φ n 0 ≤ 1 := hup.trans (Real.rpow_le_one_of_one_le_of_nonpos hW1 (by linarith))
  have hMX : 1 ≤ M * X := by nlinarith
  have hGa : ∀ a : Idx d (sz.L n) (sz.W n), ‖(baFMz sz z).G n (t n) ω a a‖ ≤ 2 := by
    intro a
    have h1 : ‖(baFMz sz z).GM n (t n) ω a a‖ ≤ 1 := by
      refine (hω1 (a, a)).trans ?_
      calc X * Φ n 0 = 1 * (X * Φ n 0) := (one_mul _).symm
        _ ≤ M * (X * Φ n 0) := mul_le_mul_of_nonneg_right hM1 (by positivity)
        _ = M * X * Φ n 0 := by ring
        _ ≤ 1 := hΨ1
    have h3 : (baFMz sz z).G n (t n) ω a a = (baFMz sz z).GM n (t n) ω a a + (baFMz sz z).M n a a := by
      unfold FlowFM.GM; ring
    rw [h3]
    exact (norm_add_le _ _).trans (by have := hMle a a; change ‖(baFMz sz z).M n a a‖ ≤ 1 at this; linarith)
  have hf := BAMomentGen_f_le hκ hflow n (ht0 n) (ht1 n) ω (A := 2) (μ := X * BAMomentGen_Psi' sz Φ n ^ 2)
    (fun b => hω2 b) hGa v.1.1 v.1.2
  set s : ℝ := ((zdistInf d (sz.L n) (STblk sz n v.1.1 - STblk sz n v.1.2) : ℕ) : ℝ) with hs
  have hs0 : 0 ≤ s := Nat.cast_nonneg _
  have hsK : s ≤ (K : ℝ) * Real.log ((sz.W n : ℕ) : ℝ) ^ 2 := by
    refine le_trans ?_ v.2
    have : zdistInf d (sz.L n) (STblk sz n v.1.1 - STblk sz n v.1.2) ≤ lwBdist d (sz.L n) (sz.W n) v.1.1 v.1.2 :=
      zdistInf_le_zdistD d (sz.L n) _
    rw [hs]
    exact_mod_cast this
  have hY : (max 1 s) ^ C₂ ≤ X :=
    (Real.rpow_le_rpow (by positivity) (max_le_max le_rfl hsK) (by linarith)).trans hrad
  have hfB : Φ n 0 ≤ (Cc 2 * C₁) * (max 1 s) ^ C₂ * Φ n s := hcmp s hs0
  have hB : 0 ≤ Cc 2 * C₁ := by positivity
  have hmain : 2 / (baFMz sz z).eta n (t n) * (X * BAMomentGen_Psi' sz Φ n ^ 2) ≤
      X ^ 3 * (((baFMz sz z).eta n (t n))⁻¹ * Φ n 0 * Φ n s) := by
    have := lwMoment_near_arith (X := X) (M := M) (H := ((baFMz sz z).eta n (t n))⁻¹) (f0 := Φ n 0)
      (fs := Φ n s) (Ψp := BAMomentGen_Psi' sz Φ n) (B := Cc 2 * C₁) (Y := (max 1 s) ^ C₂) hX1 (by linarith)
      hΦ0.le (hP s hs0).le (le_trans hΦ0.le (le_max_left _ _)) hΨ'M (by linarith) hB hfB hY hbig
    rwa [div_eq_mul_inv]
  have hR : BAMomentGen_R sz z t Φ p n v.1.1 v.1.2 = (((baFMz sz z).eta n (t n))⁻¹ * Φ n 0 * Φ n s) ^ p := by
    unfold BAMomentGen_R; rw [one_mul]
  have hXp : (X ^ 3) ^ p ≤ ((sz.size n : ℕ) : ℝ) ^ τ := by
    rw [← pow_mul, hXdef, ← Real.rpow_natCast, ← Real.rpow_mul hN0.le]
    refine Real.rpow_le_rpow_of_exponent_le hN1 ?_
    have : τ₁ ≤ τ / (3 * p) := min_le_left _ _
    calc τ₁ * ((3 * p : ℕ) : ℝ) ≤ τ / (3 * p) * ((3 * p : ℕ) : ℝ) :=
          mul_le_mul_of_nonneg_right this (by positivity)
      _ = τ := by push_cast; field_simp
  rw [Complex.norm_real, Real.norm_of_nonneg (by positivity), hR]
  have h1 := pow_le_pow_left₀ (norm_nonneg _) (hf.trans hmain) p
  have hR0 : 0 ≤ (((baFMz sz z).eta n (t n))⁻¹ * Φ n 0 * Φ n s) ^ p := by
    have := (hP s hs0).le
    positivity
  calc _ ≤ _ := h1
    _ = (X ^ 3) ^ p * (((baFMz sz z).eta n (t n))⁻¹ * Φ n 0 * Φ n s) ^ p := mul_pow _ _ _
    _ ≤ _ := mul_le_mul_of_nonneg_right hXp hR0

/-- The polynomial envelope of the carrier `f_{xy}`: `|f_{xy}|^p ≤ N^{7p}` (`|f| ≤ η⁻² (η⁻¹ + 1) ≤ N⁷`, `η⁻¹ ≤ N²`, `N ≥ 2`). -/
theorem BAMomentGen_LWfg_env (p : ℕ) :
    ∀ᶠ n in atTop, ∀ (x y : Idx d (sz.L n) (sz.W n)) (ω : sz.SeqΩ),
      ‖LWfg (baFMz sz z) n (t n) ω x y‖ ^ p ≤ ((sz.size n : ℕ) : ℝ) ^ ((7 * p : ℕ) : ℝ) := by
  filter_upwards [BAExp14a_eventual_scalars hκ hε h𝔡 hflow ht0 ht1] with n hev x y ω
  obtain ⟨-, h4, hηN, -, -⟩ := hev
  set N : ℝ := ((sz.size n : ℕ) : ℝ) with hN
  have hN0 : 0 < N := by linarith
  obtain ⟨hη0, hη1, -⟩ := BAMomentGen_eta_facts hd hκ hε h𝔡 hflow ht0 ht1 hassm n
  have hηi : 1 ≤ ((baFMz sz z).eta n (t n))⁻¹ := one_le_inv_iff₀.2 ⟨hη0, hη1⟩
  have hf := BAMomentGen_f_le hκ hflow n (ht0 n) (ht1 n) ω (A := ((baFMz sz z).eta n (t n))⁻¹)
    (μ := ((baFMz sz z).eta n (t n))⁻¹ + 1)
    (fun b => by
      rw [← BAExp14a_X_eq n (t n) ω (BAflow_real κ ε 𝔠 𝔡 sz z hflow n).1 b]
      exact BAMomentGen_X_le hκ hflow n (ht0 n) (ht1 n) ω b)
    (fun v => BAExp14a_G_le hκ hflow n (ht0 n) (ht1 n) ω v v) x y
  have hA : ((baFMz sz z).eta n (t n))⁻¹ / (baFMz sz z).eta n (t n) * (((baFMz sz z).eta n (t n))⁻¹ + 1) ≤ N ^ 7 := by
    set a := ((baFMz sz z).eta n (t n))⁻¹ with ha
    have e : a / (baFMz sz z).eta n (t n) = a * a := by rw [div_eq_mul_inv]
    rw [e]
    have ha2 : a ≤ N ^ 2 := hηN
    calc a * a * (a + 1) ≤ N ^ 2 * N ^ 2 * (2 * N ^ 2) := by
          have : a + 1 ≤ 2 * N ^ 2 := by nlinarith [sq_nonneg N]
          have h0 : 0 ≤ a := by linarith
          exact mul_le_mul (mul_le_mul ha2 ha2 h0 (by positivity)) this (by linarith) (by positivity)
      _ ≤ N ^ 2 * N ^ 2 * (N * N ^ 2) := by
          have h2N : 2 ≤ N := by linarith
          have : 2 * N ^ 2 ≤ N * N ^ 2 := mul_le_mul_of_nonneg_right h2N (by positivity)
          exact mul_le_mul_of_nonneg_left this (by positivity)
      _ = N ^ 7 := by ring
  have h0 : ‖LWfg (baFMz sz z) n (t n) ω x y‖ ≤ N ^ 7 := hf.trans hA
  calc ‖LWfg (baFMz sz z) n (t n) ω x y‖ ^ p ≤ (N ^ 7) ^ p := pow_le_pow_left₀ (norm_nonneg _) h0 p
    _ = N ^ ((7 * p : ℕ) : ℝ) := by rw [Real.rpow_natCast, ← pow_mul]

/-- **The near pairs** ((7.9) `eq:boundfxyGinf`; as `lwMoment_prec_near` in `Graph/LWMoment.lean`): `𝔼 |f_{xy}|^p ≺ R` for the pairs at block
distance `≤ K (log W)²`, from the max bound and `≺ → 𝔼` (`BAExp14a_prec_integral`; envelope `BAMomentGen_LWfg_env`, floor `BAMomentGen_floor`). -/
theorem BAMomentGen_prec_near {p : ℕ} (hp0 : 0 < p) (K : ℕ) :
    PrecL sz (Sizes.seqP (sz.withLam 0)) (U := BAMomentGen_Near sz K)
      (fun n q _ => ∫ ω, ‖LWfg (baFMz sz z) n (t n) ω q.1.1 q.1.2‖ ^ p ∂(BAExp14a_μ sz))
      (fun n q _ => BAMomentGen_R sz z t Φ p n q.1.1 q.1.2) := by
  classical
  have hsz : sz.SizeTendsto := hflow.1.2.2.1
  have key := BAExp14a_prec_integral (P := BAExp14a_μ sz) (Sizes.tendsto_size sz hsz) (V := BAMomentGen_Near sz K)
    (fun n q ω => (((‖LWfg (baFMz sz z) n (t n) ω q.1.1 q.1.2‖ ^ p : ℝ)) : ℂ))
    (fun n q => BAMomentGen_R sz z t Φ p n q.1.1 q.1.2) (Kenv := ((7 * p : ℕ) : ℝ)) (Kf := (p : ℝ) * (2 + C₂))
    ((BAMomentGen_LWfg_env hd hκ hε h𝔡 hflow ht0 ht1 hassm p).mono fun n h v ω => by
      rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      exact h _ _ ω)
    ((BAMomentGen_floor hd hκ hε h𝔡 hflow ht0 ht1 hassm p).mono fun n h v => h _ _)
    (BAMomentGen_prec_near_pre hd hκ hε h𝔡 hflow ht0 ht1 hassm hp0 K)
  refine (BAExp14a_det_iff (P := BAExp14a_μ sz) (Sizes.tendsto_size sz hsz) _ _).2 fun τ hτ => ?_
  filter_upwards [(BAExp14a_det_iff (P := BAExp14a_μ sz) (Sizes.tendsto_size sz hsz) _ _).1 key τ hτ] with n h v
  have := h v
  rwa [integral_complex_ofReal, Complex.norm_real,
    Real.norm_of_nonneg (integral_nonneg fun ω => by positivity)] at this

end NearStoch

/-! ## 3. `lem:LW_moment` at BA from `lem:Anp` at the BA carrier -/

/-- **The statement def**: `lem:LW_moment` at the block Anderson data (`BALWMoment`) from `lem:Anp` at the BA carrier
(`BAAnpAuxG`, `Graph/BAAuxGraph2B.lean`).  `BAAnpAuxG` occurs only here, as the antecedent of a statement def. -/
def BALWMomentOfAnp (d : ℕ) : Prop := BAAnpAuxG d → BALWMoment d

/-- **`lem:LW_moment` at BA** (Lemma 7.1; as `lwMoment_holds` in `Graph/LWMoment.lean`; `c = 1`): the first hypothesis is
the path binder of `baLocReg15_holds` (`Graph/BALocReg1B.lean`), verbatim; it is concluded by `baPathBinder_holds` (`Graph/BALocReg2B.lean`).
The pairs at block distance `> K (log W)²` are bounded through the engine lists
(`ba_localregularX_holds`: `GtoAG` at the rescaled kernels + `lem:Anp` for the outputs with `𝓜_x ≠ 𝓜_y`, the scale-mole tail for those
with `𝓜_x = 𝓜_y`, the size bound for the errors; the contract (1)-(5) along `BAReach` from the path binder), the others by the max bound
(7.9) `eq:boundfxyGinf`; both upgraded from `≺` to `𝔼` by `BAExp14a_prec_integral`. -/
theorem baLWMoment_of_anp
    (hb : ∀ sh, sh = BAShape.e2 ∨ sh = BAShape.macroA ∨ sh = BAShape.macroB → BAShapePath sh BAFrameStepTN) :
    ∀ d : ℕ, BALWMomentOfAnp d := by
  intro d hAnp hd κ ε 𝔡 hκ hε h𝔡 p hp2 ε₀ C₁ C₂ C₃ Cc
  refine ⟨1, one_pos, ?_⟩
  intro 𝔠 sz z hflow t ht0 ht1 Ψ Φ hassm
  have hp : Even p := even_iff_two_dvd.2 hp2
  have hsz : sz.SizeTendsto := hflow.1.2.2.1
  have h𝔠 : 0 < 𝔠 := hflow.1.1
  rcases Nat.eq_zero_or_pos p with hp0 | hp0
  · subst hp0
    refine (BAExp14a_det_iff (P := BAExp14a_μ sz) (Sizes.tendsto_size sz hsz) _ _).2 fun τ hτ => ?_
    filter_upwards [hsz.eventually_ge_atTop 1] with n hN1 v
    have hX : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ τ := Real.one_le_rpow hN1 hτ.le
    have hI : ∫ ω : sz.SeqΩ, ‖LWfg (baFMz sz z) n (t n) ω v.1 v.2‖ ^ 0 ∂(BAExp14a_μ sz) = 1 := by
      simp only [pow_zero, integral_const, smul_eq_mul, mul_one]
      simp
    rw [hI]
    simpa using hX
  · set K0 : ℕ := ⌈1 / 𝔠⌉₊ with hK0def
    have hK0 : 1 / 𝔠 ≤ K0 := Nat.le_ceil _
    obtain ⟨outs, errs, hX, hw⟩ :=
      ba_localregularX_holds p (ε₀ / 2) (half_pos hassm.1) K0 d (((p : ℝ) * (2 + C₂) + 1) / 𝔠)
    set K : ℕ := ((outs ++ errs).map fun Q => Fintype.card (Q.E' ⊕ Q.I')).sum with hKdef
    have hK : ∀ Q ∈ outs ++ errs, Fintype.card (Q.E' ⊕ Q.I') ≤ K := fun Q hQ =>
      List.le_sum_of_mem (List.mem_map_of_mem (f := fun Q : BAPGraph (Fin 2) => Fintype.card (Q.E' ⊕ Q.I')) hQ)
    -- the contract (1)-(5) at the outputs: the composition of `BALocRegConcl` (a), (c) with `BALocReg15`
    have h15 : ∀ Q ∈ outs, Q.g.nM ≤ p ∧ (BAShadowPG Q).LocReg345 p := by
      intro Q hQ
      obtain ⟨hLS, -⟩ := hX.1 Q hQ
      obtain ⟨P0, hP0, hreach, -⟩ := hX.2.2.1 Q (List.mem_append_left _ hQ)
      obtain ⟨-, hnM, -, h5⟩ := baLocReg15_holds hb p P0 hP0 _ Q hreach
      exact ⟨hnM, (h5 hLS).2.2⟩
    have hpsi : sz.LWPsiAll ε₀ C₁ C₂ C₃ Cc Φ := ⟨hassm.1, hassm.2.2.2.1, hassm.2.2.2.2.1⟩
    -- `lem:Anp` at the BA carrier, instantiated at the data and at every graph
    have hAnpL : ∀ Q : BAPGraph (Fin 2), Q.g.nM ≤ p → (BAShadowPG Q).LocReg345 p →
        Q.g.mol (Sum.inl (Q.ext 0)) ≠ Q.g.mol (Sum.inl (Q.ext 1)) →
        ∃ cG : ℝ, 0 < cG ∧ ∀ ξ : (n : ℕ) → Zd d (sz.L n) → Zd d (sz.L n) → sz.SeqΩ → ℝ,
          ((∀ n α β ω, 0 ≤ ξ n α β ω ∧ ξ n α β ω = ξ n β α ω) ∧
            PrecL sz (Sizes.seqP (sz.withLam 0)) (U := fun n => Zd d (sz.L n) × Zd d (sz.L n))
              (fun n p ω => ξ n p.1 p.2 ω) (fun n p _ => Φ n ((zdistInf d (sz.L n) (p.1 - p.2) : ℕ) : ℝ)) ∧
            PrecL sz (Sizes.seqP (sz.withLam 0)) (U := fun n => Zd d (sz.L n)) (fun n α ω => ∑ β, ξ n α β ω ^ 2)
              (fun n _ _ => ((((sz.W n : ℕ) : ℝ) ^ d) * (baFMz sz z).eta n (t n))⁻¹)) →
          PrecL sz (Sizes.seqP (sz.withLam 0)) (U := fun n => Zd d (sz.L n) × Zd d (sz.L n))
            (fun n ab ω => Q.g.auxVal (fun α β => ξ n α β ω) fun e => if e = Q.ext 0 then ab.1 else ab.2)
            fun n ab _ => ((((sz.W n : ℕ) : ℝ) ^ d) * (baFMz sz z).eta n (t n))⁻¹ ^ Q.g.nM *
              Φ n (cG * ((zdistInf d (sz.L n) (ab.1 - ab.2) : ℕ) : ℝ)) ^ p * Φ n 0 ^ (Q.g.auxOrd - (p : ℤ)) := by
      intro Q hnM h345 hxy
      obtain ⟨cG, hcG, H⟩ := hAnp hd κ ε 𝔡 hκ hε h𝔡 p Q hp0 hnM h345 hxy ε₀ C₁ C₂ C₃ Cc
      exact ⟨cG, hcG, fun ξ hξ => H 𝔠 sz z hflow t ht0 ht1 Φ hpsi ξ hξ⟩
    have hfar := BAMomentGen_prec_far hd hκ hε h𝔡 hflow ht0 ht1 hassm hAnpL hp hp0 hK0 le_rfl hX hw h15 hK
    have hnear := BAMomentGen_prec_near hd hκ hε h𝔡 hflow ht0 ht1 hassm hp0 K
    refine (BAExp14a_det_iff (P := BAExp14a_μ sz) (Sizes.tendsto_size sz hsz) _ _).2 fun τ hτ => ?_
    filter_upwards [(BAExp14a_det_iff (P := BAExp14a_μ sz) (Sizes.tendsto_size sz hsz) _ _).1 hfar τ hτ,
      (BAExp14a_det_iff (P := BAExp14a_μ sz) (Sizes.tendsto_size sz hsz) _ _).1 hnear τ hτ] with n h1 h2 q
    by_cases hq : (K : ℝ) * Real.log ((sz.W n : ℕ) : ℝ) ^ 2 < (lwBdist d (sz.L n) (sz.W n) q.1 q.2 : ℝ)
    · exact h1 ⟨q, hq⟩
    · exact h2 ⟨q, le_of_not_gt hq⟩

end RBM.BA

end
