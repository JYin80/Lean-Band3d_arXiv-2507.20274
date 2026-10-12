/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Graph.BAMomentGen

/-!
# BA-L L3d2a (T2470), part B: the near pairs and `lem:LW_moment` at BA (target 4)

Paper: arXiv:2507.20274, `paper/tex/7_8_light_weight.tex` (cited `7_8:line`): the max bound `(eq:boundfxyGinf)` (`7_8:61-66`),
`lem:LW_moment` (`7_8:72-77`), proof (`7_8:943-950`).  Twin of `Graph/LWMoment.lean` §9-§10 (`:1345-1814`); part A is
`Graph/BAMomentGen.lean`.

## Contents (namespace `RBM.BA`; private helpers carry the stem `BAMomentGen_`)

1. The near pairs, deterministic part: the max bound `|f_{xy}| ≤ (A/η) max_c |𝓛^{(1)}_c - m|` at the BA carrier (`X_c = 𝓛^{(1)}_c - m`,
   `BAExp14a_X_eq`; Ward and Cauchy-Schwarz, `lwMoment_CS`).
2. The near pairs, stochastic part: `(GavLGEX)` at `Ψ'` (`baGbEXPav_holds`), `|f_{xy}|^p ≤ (2/η N^{τ₁} Ψ'²)^p`, `≺ → 𝔼`.
3. **Target 4**: the statement def `BALWMomentOfAnp` and `baLWMoment_of_anp`, the BA `lem:LW_moment` from `lem:Anp` at the BA carrier
   (`BAAnpAuxG`, only as the antecedent of the statement def) and the path binder of `baLocReg15_holds` (T2469 is not merged at the
   start of this ticket).
4. **Target 5**: compiled instances (the instance of target 4; the strengthened instance of target 3).
5. Non-vacuity of the engine lists at `p = 2` (`BAMomentGen_lists_nonempty`: preflight F5).
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

/-- **The max bound, pathwise** (`(eq:boundfxyGinf)`, `7_8:61-66`; twin of `lwMoment_f_le`, `Graph/LWMoment.lean:1492`):
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

/-- The near pairs: block distance `≤ K (log W)²` (twin of `LWMomNear`, `Graph/LWMoment.lean:1546`). -/
def BAMomentGen_Near (sz : Sizes d) (K : ℕ) (n : ℕ) : Type :=
  {q : Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n) //
    (lwBdist d (sz.L n) (sz.W n) q.1 q.2 : ℝ) ≤ (K : ℝ) * Real.log ((sz.W n : ℕ) : ℝ) ^ 2}

/-- The entry scale for the near pairs `Ψ' = max(Φ(0), W^{-d/2})` (`7_8:62-66`; twin of `lwMoment_Psi'`). -/
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

/-- `STmaxLoop2g ≺ Ψ'²` from `LWLoop2gL` (`Φ(r) ≤ Φ(0) ≤ Ψ'`; twin of `lwMoment_maxLoop2_prec`). -/
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

/-- `max_a |𝓛^{(1)}_{+,a} - m| ≤ N^{τ₁} Ψ'²` w.h.p. (`(GavLGEX)` at `Ψ'`, `baGbEXPav_holds`; twin of `lwMoment_avg_whp`). -/
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

/-- **The near pairs, in probability** (`7_8:61-66`, the max bound; twin of `lwMoment_prec_near_pre`, `Graph/LWMoment.lean:1652`): for the pairs
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

/-- **The near pairs** (`7_8:61-66`; twin of `lwMoment_prec_near`, `Graph/LWMoment.lean:1759`): `𝔼 |f_{xy}|^p ≺ R` for the pairs at block
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

/-! ## 3. Target 4: `lem:LW_moment` at BA from `lem:Anp` at the BA carrier -/

/-- **Target 4, the statement def**: `lem:LW_moment` at the block Anderson data (`BALWMoment`) from `lem:Anp` at the BA carrier
(`BAAnpAuxG`, `Graph/BAAuxGraph2B.lean:865`, the pin of L3d1).  `BAAnpAuxG` occurs only here, as the antecedent of a statement def. -/
def BALWMomentOfAnp (d : ℕ) : Prop := BAAnpAuxG d → BALWMoment d

/-- **Target 4** (`lem:LW_moment` at BA, `7_8:72-77`; twin of `lwMoment_holds`, `Graph/LWMoment.lean:1785`; `c = 1`): the first hypothesis is
the path binder of `baLocReg15_holds` (`Graph/BALocReg1B.lean:264`), verbatim; it is concluded by T2469 (L3b2, not merged at the start of this
ticket, DECISIONS §269 (7), O2R-C3 pattern).  The pairs at block distance `> K (log W)²` are bounded through the engine lists
(`ba_localregularX_holds`: `GtoAG` at the rescaled kernels + `lem:Anp` for the outputs with `𝓜_x ≠ 𝓜_y`, the scale-mole tail for those
with `𝓜_x = 𝓜_y`, the size bound for the errors; the contract (1)-(5) along `BAReach` from the path binder), the others by the max bound
`(eq:boundfxyGinf)`; both upgraded from `≺` to `𝔼` by `BAExp14a_prec_integral`. -/
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

/-! ## 4. Compiled nonempty instances (target 5)

Data (`BA/LWPinsBA.lean` §3, `Graph/BAAuxGraph2B.lean` §7): `d = 3`, `sz0` (`n = 0`: `L = 4`, `W = 32`, `N = 2097152`, `λ = 1/64`), the flow
`flow_sz0` (`κ = 1/2`, `ε = 𝔡 = 1/10`, `𝔠 = 1/6`), `z = zSeq`, `t ≡ 1/2 ≤ BAflowT0` (`half_lt_t0`), `ε₀ = 1/10`, `Ψ_n = Φ_n ≡ W_n^{-1/2}`,
`C₁ = C₂ = 2`, `C₃ = 1`, `Cc ≡ 1`.  The hypotheses left are the pins of other gates: `BAAnpAuxG 3` (L3d1), the path binder (T2469),
`STInitialGT2gL` and `LWLoop2gL` (inside `LWAssmgL`). -/

section Inst

open RBM.Gauss.SizesInst RBM.BA.FlowPinsInst

local notation "μ0" => Sizes.seqP (sz0.withLam 0)

/-- The class `Φ ≡ W^{-1/2}` of the instances. -/
private def BAMomentGen_Φ0 : ℕ → ℝ → ℝ := fun n _ => ((sz0.W n : ℕ) : ℝ) ^ (-(1 / 2 : ℝ))

/-- The entry scale `Ψ_n = W_n^{-1/2}` of the instances. -/
private def BAMomentGen_Ψ0 : ℕ → ℝ := fun n => ((sz0.W n : ℕ) : ℝ) ^ (-(1 / 2 : ℝ))

/-- The window of the instances: `W^{-3/2} ≤ Ψ ≤ W^{-1/10}`. -/
private theorem BAMomentGen_Ψ0_window : LWWindow sz0 (1 / 10) BAMomentGen_Ψ0 :=
  Eventually.of_forall fun n => ⟨Real.rpow_le_rpow_of_exponent_le (RBM.Gauss.LWInst.one_le_W n) (by norm_num),
    Real.rpow_le_rpow_of_exponent_le (RBM.Gauss.LWInst.one_le_W n) (by norm_num)⟩

/-- The class and its relation `(eq:Psi)` at `(ε₀, C₁, C₂, C₃, Cc) = (1/10, 2, 2, 1, 1)`. -/
private theorem BAMomentGen_psiAll0 : LWPsiAll sz0 (1 / 10) 2 2 1 (fun _ => 1) BAMomentGen_Φ0 := by
  have hW1 := RBM.Gauss.LWInst.one_le_W
  refine ⟨by norm_num, ⟨Eventually.of_forall fun n r _ => ⟨Real.rpow_pos_of_pos (by linarith [hW1 n]) _,
    Real.rpow_le_rpow_of_exponent_le (hW1 n) (by norm_num)⟩, one_pos, Eventually.of_forall fun n => ?_⟩,
    fun n a _ b _ _ => le_rfl, by norm_num, by norm_num,
    fun C _ => Eventually.of_forall fun n ℓ _ _ => by simp [BAMomentGen_Φ0], Eventually.of_forall fun n ℓ₁ ℓ₂ h1 h12 => ?_⟩
  · simp only [BAMomentGen_Φ0, one_mul]
    exact Real.rpow_le_rpow_of_exponent_le (hW1 n) (by norm_num)
  · simp only [BAMomentGen_Φ0]
    have hW : 0 < ((sz0.W n : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos (by linarith [hW1 n]) _
    have hr : 1 ≤ ℓ₂ / ℓ₁ := (one_le_div (by linarith)).mpr h12
    have : (1 : ℝ) ≤ (ℓ₂ / ℓ₁) ^ (2 : ℝ) := Real.one_le_rpow hr (by norm_num)
    nlinarith

/-- **Instance (iii) of target 4**: `baLWMoment_of_anp` at the data above, `p = 2`: the moment bound
`𝔼 |f_{xy}|² ≺ (η⁻¹ Φ(0) Φ(c|a-b|))²` for some `c > 0`.  The deterministic hypotheses (`d = 3`, `κ`, `ε`, `𝔡 > 0`, `2 ∣ p`,
the flow `flow_sz0`, `0 ≤ t ≤ T₀`, the window, the class, `(eq:Psi)`) are discharged; the pins of other gates stay hypotheses. -/
example
    (hb : ∀ sh, sh = BAShape.e2 ∨ sh = BAShape.macroA ∨ sh = BAShape.macroB → BAShapePath sh BAFrameStepTN)
    (hAnp : BAAnpAuxG 3) (hI : STInitialGT2gL (baFMz sz0 zSeq) μ0 (fun _ => 1 / 2) (1 / 10) BAMomentGen_Ψ0)
    (hL : LWLoop2gL (baFMz sz0 zSeq) μ0 (fun _ => 1 / 2) BAMomentGen_Φ0) :
    ∃ c : ℝ, 0 < c ∧ PrecL sz0 μ0 (U := fun n => Idx 3 (sz0.L n) (sz0.W n) × Idx 3 (sz0.L n) (sz0.W n))
      (fun n q _ => ∫ ω, ‖LWfg (baFMz sz0 zSeq) n ((fun _ => (1 / 2 : ℝ)) n) ω q.1 q.2‖ ^ 2 ∂μ0)
      (fun n q _ => (((baFMz sz0 zSeq).eta n ((fun _ => (1 / 2 : ℝ)) n))⁻¹ * BAMomentGen_Φ0 n 0 *
        BAMomentGen_Φ0 n (c * ((zdistInf 3 (sz0.L n) (STblk sz0 n q.1 - STblk sz0 n q.2) : ℕ) : ℝ))) ^ 2) := by
  obtain ⟨c, hc, H⟩ := baLWMoment_of_anp hb 3 hAnp le_rfl (1 / 2) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num)
    2 (dvd_refl 2) (1 / 10) 2 2 1 (fun _ => 1)
  exact ⟨c, hc, H (1 / 6) sz0 zSeq flow_sz0 (fun _ => 1 / 2) (fun _ => by norm_num) (fun n => (half_lt_t0 n).le)
    BAMomentGen_Ψ0 BAMomentGen_Φ0 ⟨by norm_num, BAMomentGen_Ψ0_window, hI, BAMomentGen_psiAll0.2.1, BAMomentGen_psiAll0.2.2, hL⟩⟩

end Inst

/-! ## 5. Non-vacuity of the engine lists at `p = 2` (preflight F5)

`BALocRegConcl` (d) forces `outs ++ errs ≠ []`: with empty lists it gives `𝔼 |f_{xx}|² = 0` at the datum `d = 3`, `L = 3`, `W = 2`, `g₀ = 0`, `E = 0`,
`t = 1/4`, `m = i`; but at the point `ω₀ = 2 P_σ` of the sample space (`σ` pairs the sites of each block, `Fin.rev` on the offset) the resolvent is
`G = a + b P_σ` and `f_{xx}(ω₀) = t (a - i) b² ≠ 0`, `f_{xx}` is continuous, and every neighbourhood of `ω₀` has positive probability under `PF`. -/

section Nonempty

variable {d L W : ℕ} [NeZero L] [NeZero W]

/-- The point `ω₀`: the coordinate `(i, σ i, true)` of an oriented pair `idxKey i < idxKey (σ i)` is `s`, the others are `0`. -/
def BAMomentGen_pt (σ : Idx d L W → Idx d L W) (s : ℝ) : Ω d L W :=
  fun c => if c.2.2 = true ∧ c.2.1 = σ c.1 ∧ idxKey d L W c.1 < idxKey d L W c.2.1 then s else 0

/-- The permutation matrix of `σ`. -/
def BAMomentGen_P (σ : Idx d L W → Idx d L W) : Matrix (Idx d L W) (Idx d L W) ℂ :=
  Matrix.of fun i j => if j = σ i then 1 else 0

theorem BAMomentGen_pt_Xmat (σ : Idx d L W → Idx d L W) (hσσ : ∀ i, σ (σ i) = i) (hne : ∀ i, σ i ≠ i) (s : ℝ) :
    Xmat d L W (BAMomentGen_pt σ s) = (s : ℂ) • BAMomentGen_P σ := by
  ext i j
  simp only [Xmat, Matrix.of_apply, Matrix.smul_apply, BAMomentGen_P, smul_eq_mul]
  unfold Xentry BAMomentGen_pt
  have hiff : i = σ j ↔ j = σ i := ⟨fun h => by rw [h, hσσ], fun h => by rw [h, hσσ]⟩
  rcases idxKey_lt_or_eq_or_lt d L W i j with h | h | h
  · simp [h]
    split_ifs <;> simp
  · subst h
    have := hne i
    simp [this.symm]
  · have h' : ¬ idxKey d L W i < idxKey d L W j := not_lt.mpr h.le
    simp [h', h, hiff]
    split_ifs <;> simp

theorem BAMomentGen_P_mul (σ : Idx d L W → Idx d L W) (hσσ : ∀ i, σ (σ i) = i) :
    BAMomentGen_P σ * BAMomentGen_P σ = 1 := by
  ext i k
  simp only [BAMomentGen_P, Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply]
  rw [Finset.sum_eq_single (σ i)]
  · simp [hσσ, eq_comm]
  · intro j _ hj; simp [hj]
  · simp


/-- The resolvent of `c P`: `(c P - z)⁻¹ = (-z 1 - c P)/(z² - c²)` (`P² = 1`). -/
theorem BAMomentGen_resolvent (σ : Idx d L W → Idx d L W) (hσσ : ∀ i, σ (σ i) = i) (z c : ℂ) (hz : z ^ 2 ≠ c ^ 2) :
    Gres (c • BAMomentGen_P σ) z true = (-z / (z ^ 2 - c ^ 2)) • (1 : Matrix (Idx d L W) (Idx d L W) ℂ) +
      (-c / (z ^ 2 - c ^ 2)) • BAMomentGen_P σ := by
  have hPP := BAMomentGen_P_mul σ hσσ
  have hz' : z ^ 2 - c ^ 2 ≠ 0 := sub_ne_zero.2 hz
  unfold Gres
  simp only [ite_true]
  rw [← Matrix.nonsing_inv_eq_ringInverse]
  apply Matrix.inv_eq_right_inv
  have key : (c • BAMomentGen_P σ - z • (1 : Matrix (Idx d L W) (Idx d L W) ℂ)) *
      ((-z / (z ^ 2 - c ^ 2)) • (1 : Matrix (Idx d L W) (Idx d L W) ℂ) + (-c / (z ^ 2 - c ^ 2)) • BAMomentGen_P σ) =
      (c * (-c / (z ^ 2 - c ^ 2)) - z * (-z / (z ^ 2 - c ^ 2))) • (1 : Matrix (Idx d L W) (Idx d L W) ℂ) +
      (c * (-z / (z ^ 2 - c ^ 2)) - z * (-c / (z ^ 2 - c ^ 2))) • BAMomentGen_P σ := by
    simp only [Matrix.sub_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, hPP,
      smul_smul]
    module
  rw [key]
  have e1 : c * (-c / (z ^ 2 - c ^ 2)) - z * (-z / (z ^ 2 - c ^ 2)) = 1 := by field_simp; ring
  have e2 : c * (-z / (z ^ 2 - c ^ 2)) - z * (-c / (z ^ 2 - c ^ 2)) = 0 := by field_simp; ring
  rw [e1, e2, one_smul, zero_smul, add_zero]


/-- `M = (0 Ψ - 0 - i)⁻¹ = i · 1`. -/
theorem BAMomentGen_M0 : BAlwM d L W 0 0 Complex.I = (Complex.I : ℂ) • (1 : Matrix (Idx d L W) (Idx d L W) ℂ) := by
  unfold BAlwM Mres
  simp only [Complex.ofReal_zero, zero_smul, zero_sub, zero_add]
  rw [← Matrix.nonsing_inv_eq_ringInverse]
  apply Matrix.inv_eq_right_inv
  rw [neg_mul, Matrix.smul_mul, Matrix.one_mul, smul_smul]
  simp

/-- The flow resolvent at the point: `G = a · 1 + b P`. -/
theorem BAMomentGen_pt_G (σ : Idx d L W → Idx d L W) (hσσ : ∀ i, σ (σ i) = i) (hne : ∀ i, σ i ≠ i) (t s : ℝ)
    (hz : (ztOf Complex.I 0 t) ^ 2 ≠ ((Real.sqrt t : ℂ) * s) ^ 2) (u v : Idx d L W) :
    BAlwG d L W 0 0 t Complex.I (BAMomentGen_pt σ s) u v =
      (if u = v then -(ztOf Complex.I 0 t) / ((ztOf Complex.I 0 t) ^ 2 - ((Real.sqrt t : ℂ) * s) ^ 2) else 0) +
      (if v = σ u then -((Real.sqrt t : ℂ) * s) / ((ztOf Complex.I 0 t) ^ 2 - ((Real.sqrt t : ℂ) * s) ^ 2) else 0) := by
  unfold BAlwG BAlwH
  have hH : (((0 : ℝ) : ℂ) • PsiI d L W + Hflow d L W t (BAMomentGen_pt σ s)) =
      ((Real.sqrt t : ℂ) * s) • BAMomentGen_P σ := by
    simp only [Complex.ofReal_zero, zero_smul, zero_add, Hflow, BAMomentGen_pt_Xmat σ hσσ hne, smul_smul]
  rw [hH, BAMomentGen_resolvent σ hσσ _ _ hz]
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, BAMomentGen_P, Matrix.of_apply, smul_eq_mul]
  split_ifs <;> simp


/-- `Σ_β S_{αβ} = t` (`S_{αβ} = t W^{-d} 1([α] = [β])`, `W^d` points in a block). -/
theorem BAMomentGen_S_sum (t : ℝ) (α : Idx d L W) : ∑ β, BAlwS d L W t α β = (t : ℂ) := by
  have hW : ((W : ℂ) ^ d) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (NeZero.ne W))
  simp only [BAExp14a_S_apply, ← Finset.mul_sum]
  rw [Finset.sum_boole]
  have hc : (Finset.univ.filter fun β : Idx d L W => (split d L W α).1 = (split d L W β).1) =
      Iblk d L W (split d L W α).1 := by
    ext β; simp [Iblk, eq_comm]
  rw [hc, card_Iblk]
  push_cast
  field_simp

/-- The value of `f_{xx}` at the point `ω₀`: `t (a - i) b²`. -/
theorem BAMomentGen_pt_fxy (σ : Idx d L W → Idx d L W) (hσσ : ∀ i, σ (σ i) = i) (hne : ∀ i, σ i ≠ i) (t s : ℝ)
    (hz : (ztOf Complex.I 0 t) ^ 2 ≠ ((Real.sqrt t : ℂ) * s) ^ 2) (x : Idx d L W) :
    fxyVal (BAlwData d L W 0 0 t Complex.I (BAMomentGen_pt σ s)).toLData x x =
      (t : ℂ) * (-(ztOf Complex.I 0 t) / ((ztOf Complex.I 0 t) ^ 2 - ((Real.sqrt t : ℂ) * s) ^ 2) - Complex.I) *
        (-((Real.sqrt t : ℂ) * s) / ((ztOf Complex.I 0 t) ^ 2 - ((Real.sqrt t : ℂ) * s) ^ 2)) ^ 2 := by
  set a : ℂ := -(ztOf Complex.I 0 t) / ((ztOf Complex.I 0 t) ^ 2 - ((Real.sqrt t : ℂ) * s) ^ 2) with ha
  set b : ℂ := -((Real.sqrt t : ℂ) * s) / ((ztOf Complex.I 0 t) ^ 2 - ((Real.sqrt t : ℂ) * s) ^ 2) with hb
  have hG := BAMomentGen_pt_G σ hσσ hne t s hz
  have hGd : ∀ β : Idx d L W, (BAlwData d L W 0 0 t Complex.I (BAMomentGen_pt σ s)).toLData.G β β -
      (BAlwData d L W 0 0 t Complex.I (BAMomentGen_pt σ s)).toLData.M β β = a - Complex.I := by
    intro β
    change BAlwG d L W 0 0 t Complex.I (BAMomentGen_pt σ s) β β - BAlwM d L W 0 0 Complex.I β β = a - Complex.I
    rw [hG β β, BAMomentGen_M0]
    simp [(hne β).symm, ← ha]
  unfold fxyVal
  rw [Finset.sum_eq_single (σ x)]
  · have hno : ¬ (σ x = x ∨ σ x = x) := by simp [hne x]
    simp only [hno, ite_false]
    have h1 : (BAlwData d L W 0 0 t Complex.I (BAMomentGen_pt σ s)).toLData.G x (σ x) = b := by
      change BAlwG d L W 0 0 t Complex.I (BAMomentGen_pt σ s) x (σ x) = b
      rw [hG x (σ x)]; simp [(hne x).symm, ← hb]
    have h2 : (BAlwData d L W 0 0 t Complex.I (BAMomentGen_pt σ s)).toLData.G (σ x) x = b := by
      change BAlwG d L W 0 0 t Complex.I (BAMomentGen_pt σ s) (σ x) x = b
      rw [hG (σ x) x]; simp [hne x, hσσ, ← hb]
    simp only [hGd, h1, h2]
    have : ∀ β : Idx d L W, (BAlwData d L W 0 0 t Complex.I (BAMomentGen_pt σ s)).toLData.S (σ x) β * (a - Complex.I) * b * b =
        BAlwS d L W t (σ x) β * ((a - Complex.I) * b * b) := fun β => by
      change BAlwS d L W t (σ x) β * (a - Complex.I) * b * b = _
      ring
    simp only [this, ← Finset.sum_mul, BAMomentGen_S_sum]
    ring
  · intro α _ hα
    split_ifs with h
    · rfl
    · have hxα : (BAlwData d L W 0 0 t Complex.I (BAMomentGen_pt σ s)).toLData.G x α = 0 := by
        change BAlwG d L W 0 0 t Complex.I (BAMomentGen_pt σ s) x α = 0
        rw [hG x α]
        have h1 : ¬ x = α := fun e => h (Or.inl e.symm)
        have h2 : ¬ α = σ x := hα
        simp [h1, h2]
      simp [hxα]
  · simp


/-- Open sets around a point with the variance-zero coordinates at `0` have positive probability for the Gaussian law `PF`. -/
theorem BAMomentGen_PF_pos (g : ℝ) (ω₀ : Ω d L W) (h0 : ∀ c, gvarF d L W g c = 0 → ω₀ c = 0) {U : Set (Ω d L W)}
    (hU : IsOpen U) (hω : ω₀ ∈ U) : 0 < PF d L W g U := by
  obtain ⟨I, u, hu, hsub⟩ := isOpen_pi_iff.1 hU ω₀ hω
  have hmeas : ∀ i ∈ I, MeasurableSet (u i) := fun i hi => (hu i hi).1.measurableSet
  have hpi : PF d L W g (Set.pi (I : Set (CoordF d L W)) u) =
      ∏ i ∈ I, ProbabilityTheory.gaussianReal 0 (gvarF d L W g i) (u i) := by
    unfold PF
    exact Measure.infinitePi_pi _ hmeas
  refine lt_of_lt_of_le ?_ (measure_mono hsub)
  rw [hpi, pos_iff_ne_zero, Finset.prod_ne_zero_iff]
  intro i hi
  by_cases hv : gvarF d L W g i = 0
  · rw [hv, ProbabilityTheory.gaussianReal_zero_var, Measure.dirac_apply' _ (hmeas i hi),
      Set.indicator_of_mem (by simpa [h0 i hv] using (hu i hi).2)]
    simp
  · intro hzero
    have h1 := (ProbabilityTheory.gaussianReal_absolutelyContinuous' 0 hv) hzero
    have h2 := (hu i hi).1.measure_pos MeasureTheory.volume ⟨ω₀ i, (hu i hi).2⟩
    exact absurd h1 h2.ne'


/-- A fixed-point free involution of the fine lattice that preserves the blocks (`Fin.rev` on the offset, `W^d` even). -/
def BAMomentGen_sigma (d L W : ℕ) [NeZero L] [NeZero W] (i : Idx d L W) : Idx d L W :=
  (splitEquiv d L W).symm ((splitEquiv d L W i).1, Fin.rev (splitEquiv d L W i).2)

theorem BAMomentGen_sigma_sigma (i : Idx d L W) : BAMomentGen_sigma d L W (BAMomentGen_sigma d L W i) = i := by
  unfold BAMomentGen_sigma
  simp [Fin.rev_rev]

theorem BAMomentGen_sigma_ne (hev : Even (W ^ d)) (i : Idx d L W) : BAMomentGen_sigma d L W i ≠ i := by
  intro h
  have h2 := congrArg (splitEquiv d L W) h
  unfold BAMomentGen_sigma at h2
  rw [Equiv.apply_symm_apply] at h2
  have h3 := congrArg Prod.snd h2
  simp only at h3
  obtain ⟨k, hk⟩ := hev
  have h4 := congrArg Fin.val h3
  simp only [Fin.val_rev] at h4
  omega

theorem BAMomentGen_sigma_blk (i : Idx d L W) :
    (split d L W (BAMomentGen_sigma d L W i)).1 = (split d L W i).1 := by
  unfold BAMomentGen_sigma
  have := Equiv.apply_symm_apply (splitEquiv d L W) ((splitEquiv d L W i).1, Fin.rev (splitEquiv d L W i).2)
  have h1 := congrArg Prod.fst this
  exact h1


/-- The coordinates with `ω₀ c ≠ 0` have a non-zero variance (they join two points of one block, `S^{(B)}(0) = I`). -/
theorem BAMomentGen_pt_var (hev : Even (W ^ d)) (s : ℝ) (c : CoordF d L W)
    (hc : BAMomentGen_pt (BAMomentGen_sigma d L W) s c ≠ 0) : gvarF d L W 0 c ≠ 0 := by
  unfold BAMomentGen_pt at hc
  by_cases hcond : c.2.2 = true ∧ c.2.1 = BAMomentGen_sigma d L W c.1 ∧ idxKey d L W c.1 < idxKey d L W c.2.1
  · have hne : c.1 ≠ c.2.1 := by
      rw [hcond.2.1]; exact (BAMomentGen_sigma_ne hev c.1).symm
    have h1 : (gvarF d L W 0 c : ℝ) = svarF d L W 0 c.1 c.2.1 / 2 := by
      simp only [gvarF, hne, ite_false]; rfl
    have h2 : svarF d L W 0 c.1 c.2.1 = svarF d L W 0 c.1 c.1 := by
      unfold svarF; rw [hcond.2.1, BAMomentGen_sigma_blk]
    have h3 : 0 < svarF d L W 0 c.1 c.1 := by
      rw [svarF_diag]
      have : (0 : ℝ) < (W : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne W)
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, add_zero, inv_one, mul_one]
      positivity
    intro h
    have : (gvarF d L W 0 c : ℝ) = 0 := by rw [h]; rfl
    rw [h1, h2] at this
    linarith
  · exact absurd (by simp [hcond]) hc

/-- `BASelf` at `(g, z, m) = (0, 0, i)`: `m = L^{-d} tr (-i)⁻¹ = i`. -/
theorem BAMomentGen_selfI (d L : ℕ) [NeZero L] : BASelf d L 0 (((0 : ℝ) : ℂ)) Complex.I := by
  unfold BASelf BAMB Mres
  refine ⟨by simp, ?_⟩
  have h : Ring.inverse (((0 : ℝ) : ℂ) • PsiB d L - (((0 : ℝ) : ℂ) + Complex.I) • (1 : Matrix (Zd d L) (Zd d L) ℂ)) =
      Complex.I • (1 : Matrix (Zd d L) (Zd d L) ℂ) := by
    simp only [Complex.ofReal_zero, zero_smul, zero_sub, zero_add]
    rw [← Matrix.nonsing_inv_eq_ringInverse]
    apply Matrix.inv_eq_right_inv
    rw [neg_mul, Matrix.smul_mul, Matrix.one_mul, smul_smul]
    simp
  rw [h, Matrix.trace_smul, Matrix.trace_one, BAcard_Zd]
  have : ((L ^ d : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (pow_ne_zero _ (NeZero.ne L))
  simp only [smul_eq_mul]
  field_simp


/-- The value of the BA reading of the start graph at the data `BAlwData` is `f_{xy}^{p/2} \overline{f_{xy}}^{p/2}`, pointwise
(the pointwise half of `ba_fxyPow_integral_eq`, `Graph/BALocReg1B.lean:294`). -/
theorem BAMomentGen_fxyPow_pt (g0 Em t : ℝ) (m : ℂ) (p : ℕ) (hp : Even p) (ℓe : Fin 2 → Idx d L W) (ω : Ω d L W) :
    (BAGraph.ofLGraph (fxyPowGraph p)).val (BAlwData d L W g0 Em t m ω) ℓe =
      fxyVal (BAlwData d L W g0 Em t m ω).toLData (ℓe 0) (ℓe 1) ^ (p / 2) *
        star (fxyVal (BAlwData d L W g0 Em t m ω).toLData (ℓe 0) (ℓe 1)) ^ (p / 2) := by
  rw [BAGraph.val_ofLGraph]
  have hℓ : ℓe = ![ℓe 0, ℓe 1] := by
    funext i; fin_cases i <;> rfl
  have hS : ∀ i j, star ((BAlwData d L W g0 Em t m ω).toLData.S i j) = (BAlwData d L W g0 Em t m ω).toLData.S i j := by
    intro i j
    change star (BAlwS d L W t i j) = BAlwS d L W t i j
    simp [BAlwS, star_mul', Complex.star_def, Complex.conj_ofReal]
  have := fxyPowGraph_val_eq (BAlwData d L W g0 Em t m ω).toLData hS p hp (ℓe 0) (ℓe 1)
  rwa [← hℓ] at this


theorem BAMomentGen_sqrt_quarter : Real.sqrt (1 / 4) = 1 / 2 := by
  rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num]
  exact Real.sqrt_sq (by norm_num)

theorem BAMomentGen_num_z : (ztOf Complex.I 0 (1 / 4)) ^ 2 ≠ ((Real.sqrt (1 / 4) : ℂ) * ((2 : ℝ) : ℂ)) ^ 2 := by
  rw [BAMomentGen_sqrt_quarter]
  unfold ztOf
  intro h
  have := congrArg Complex.re h
  norm_num [pow_two] at this

theorem BAMomentGen_num_F :
    ((1 / 4 : ℝ) : ℂ) * (-(ztOf Complex.I 0 (1 / 4)) / ((ztOf Complex.I 0 (1 / 4)) ^ 2 - ((Real.sqrt (1 / 4) : ℂ) * ((2 : ℝ) : ℂ)) ^ 2) - Complex.I) *
        (-((Real.sqrt (1 / 4) : ℂ) * ((2 : ℝ) : ℂ)) / ((ztOf Complex.I 0 (1 / 4)) ^ 2 - ((Real.sqrt (1 / 4) : ℂ) * ((2 : ℝ) : ℂ)) ^ 2)) ^ 2 ≠ 0 := by
  have hz1 : ztOf Complex.I 0 (1 / 4) = (3 / 4 : ℂ) * Complex.I := by
    unfold ztOf; push_cast; ring
  have hc1 : (Real.sqrt (1 / 4) : ℂ) * ((2 : ℝ) : ℂ) = 1 := by
    rw [BAMomentGen_sqrt_quarter]; push_cast; ring
  have hden : ((3 / 4 : ℂ) * Complex.I) ^ 2 - (1 : ℂ) ^ 2 = -25 / 16 := by
    rw [mul_pow, Complex.I_sq]; norm_num
  rw [hz1, hc1, hden]
  have e1 : -((3 / 4 : ℂ) * Complex.I) / (-25 / 16) - Complex.I = -(13 / 25 : ℂ) * Complex.I := by
    ring
  have e2 : -(1 : ℂ) / (-25 / 16) = 16 / 25 := by norm_num
  rw [e1, e2]
  refine mul_ne_zero (mul_ne_zero (by norm_num) (mul_ne_zero (by norm_num) Complex.I_ne_zero)) (pow_ne_zero _ (by norm_num))


section Final

/-- **The engine lists are not empty at `p = 2`** (non-vacuity of `ba_localregularX_holds`, preflight F5): by `BALocRegConcl` (d) at
the datum `d = 3`, `L = 3`, `W = 2`, `g₀ = 0`, `E = 0`, `t = 1/4`, `m = i` (`BASelf`), empty lists would give `𝔼 |f_{xx}|² = 0`; but `f_{xx}` is continuous,
non-zero at the point `ω₀ = 2 P_σ` (`σ` pairs the sites of each block; there `G = a + b P_σ` is explicit, `f_{xx}(ω₀) = t (a - i) b² ≠ 0`)
and every neighbourhood of `ω₀` has positive probability. -/
theorem BAMomentGen_lists_nonempty {c : ℝ} {K0 : ℕ} {D : ℝ} {outs errs : List (BAPGraph (Fin 2))}
    (h : BALocRegConcl 2 c K0 3 D outs errs) : outs ++ errs ≠ [] := by
  classical
  intro hnil
  have hev : Even ((2 : ℕ) ^ 3) := by decide
  have hσσ := BAMomentGen_sigma_sigma (d := 3) (L := 3) (W := 2)
  have hne := BAMomentGen_sigma_ne (d := 3) (L := 3) (W := 2) hev
  have hSelf := BAMomentGen_selfI 3 3
  let x : Idx 3 3 2 := fun _ => 0
  have hd := h.2.2.2 3 2 (by norm_num) 0 0 (1 / 4) Complex.I hSelf (by norm_num) (by norm_num) ![x, x]
  rw [hnil] at hd
  let DD : Ω 3 3 2 → BALData (Idx 3 3 2) := fun ω => BAlwData 3 3 2 0 0 (1 / 4) Complex.I ω
  let F : Ω 3 3 2 → ℂ := fun ω => fxyVal (DD ω).toLData x x
  have hpt : ∀ ω, (BAGraph.ofLGraph (fxyPowGraph 2)).val (BAlwData 3 3 2 0 0 (1 / 4) Complex.I ω) ![x, x] =
      ((‖F ω‖ ^ 2 : ℝ) : ℂ) := by
    intro ω
    rw [BAMomentGen_fxyPow_pt 0 0 (1 / 4) Complex.I 2 (by decide) ![x, x] ω]
    change F ω ^ (2 / 2) * star (F ω) ^ (2 / 2) = _
    rw [show (2 : ℕ) / 2 = 1 by norm_num, pow_one, pow_one, Complex.star_def, Complex.mul_conj']
    push_cast
    ring
  have hint : Integrable (fun ω => ‖F ω‖ ^ 2) (PF 3 3 2 0) := by
    have h1 := BALvl1A_integrable_val (d := 3) (L := 3) (W := 2) (by norm_num) 0 0 (1 / 4) Complex.I hSelf (by norm_num)
      (by norm_num) (BAGraph.ofLGraph (fxyPowGraph 2)) ![x, x]
    simp_rw [hpt] at h1
    refine h1.norm.congr (Filter.Eventually.of_forall fun ω => ?_)
    simp [norm_pow, Complex.norm_real]
  have hzero : ∫ ω, ‖F ω‖ ^ 2 ∂(PF 3 3 2 0) = 0 := by
    have h1 := hd
    simp_rw [hpt] at h1
    simp only [BAComb.val, List.append_nil, List.map_nil, List.sum_nil, integral_zero] at h1
    rw [integral_complex_ofReal] at h1
    exact_mod_cast h1
  have hae : (fun ω => ‖F ω‖ ^ 2) =ᵐ[PF 3 3 2 0] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun ω => by positivity) hint).1 hzero
  have hz : (ztOf Complex.I 0 (1 / 4)).im ≠ 0 := by norm_num [ztOf]
  have hGc : ∀ a b, Continuous fun ω : Ω 3 3 2 => (DD ω).G a b := fun a b => BAExp14a_cont_lwG hz a b
  have hFc : Continuous F := BAMomentGen_cont_fxyVal DD (DD 0) hGc (fun _ => rfl) (fun _ => rfl) x x
  let ω₀ : Ω 3 3 2 := BAMomentGen_pt (BAMomentGen_sigma 3 3 2) 2
  have hF0 : F ω₀ ≠ 0 := by
    change fxyVal (BAlwData 3 3 2 0 0 (1 / 4) Complex.I ω₀).toLData x x ≠ 0
    rw [BAMomentGen_pt_fxy (BAMomentGen_sigma 3 3 2) hσσ hne (1 / 4) 2 BAMomentGen_num_z x]
    exact BAMomentGen_num_F
  have hU : IsOpen {ω : Ω 3 3 2 | ‖F ω₀‖ ^ 2 / 2 < ‖F ω‖ ^ 2} :=
    isOpen_lt continuous_const (hFc.norm.pow 2)
  have hω₀ : ω₀ ∈ {ω : Ω 3 3 2 | ‖F ω₀‖ ^ 2 / 2 < ‖F ω‖ ^ 2} := by
    have : 0 < ‖F ω₀‖ ^ 2 := by positivity
    change ‖F ω₀‖ ^ 2 / 2 < ‖F ω₀‖ ^ 2
    linarith
  have hpos := BAMomentGen_PF_pos 0 ω₀
    (fun c hc => by by_contra hne'; exact BAMomentGen_pt_var hev 2 c hne' hc) hU hω₀
  have hnull : PF 3 3 2 0 {ω : Ω 3 3 2 | ‖F ω₀‖ ^ 2 / 2 < ‖F ω‖ ^ 2} = 0 := by
    refine measure_mono_null ?_ (ae_iff.1 hae)
    intro ω hω
    have : 0 < ‖F ω₀‖ ^ 2 := by positivity
    simp only [Set.mem_ofPred_eq, Pi.zero_apply] at hω ⊢
    intro h0
    linarith
  exact hpos.ne' hnull

end Final

end Nonempty

/-- **Instance (i) of target 3, lists nonempty**: `ba_localregularX_holds` at `p = 2`, `c = 1/4`, `K0 = 2`, `d = 3`, `D = 10` with `outs ++ errs ≠ []`
(`BAMomentGen_lists_nonempty`). -/
example : ∃ outs errs : List (BAPGraph (Fin 2)), BALocRegConcl 2 (1 / 4) 2 3 10 outs errs ∧ outs ++ errs ≠ [] ∧
    ∀ Q ∈ outs ++ errs, 2 ≤ Q.g.waved.countP (fun e => !e.col) := by
  obtain ⟨outs, errs, h, hw⟩ := ba_localregularX_holds 2 (1 / 4) (by norm_num) 2 3 10
  exact ⟨outs, errs, h, BAMomentGen_lists_nonempty h, hw⟩

end RBM.BA

end
