/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Graph.LocalRegular6d
import RBM3D.Graph.AnpKey6
import RBM3D.Graph.AuxGraph2
import RBM3D.Graph.LWExpTerm2
import RBM3D.Graph.LWEngine

/-!
# LW-02: `lem:LW_moment` (T2297)

Paper: arXiv:2507.20274, `paper/tex/7_8_light_weight.tex` (cited `7_8:line`): `lem:LW_moment` (`7_8:72-77`),
the max bound `(eq:boundfxyGinf)` (`7_8:61-63`), `(eq:far_ab)` (`7_8:95-98`), `lem:localregular`
(`7_8:786-821`), `GtoAG` (`7_8:857-930`), `lem:Anp` (`7_8:933-939`), proof of `lem:LW_moment` (`7_8:943-950`).
-/

set_option linter.style.longLine false
set_option linter.style.setOption false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.flexible false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false

noncomputable section

open MeasureTheory ProbabilityTheory Matrix Filter

namespace RBM.Graph

/-! ## 1. Homogeneity in the black waved edges and the bridge `fxyVal D_t = t · LWf` -/

section Hom

variable {ι : Type} [Fintype ι] [DecidableEq ι]

private theorem lwMoment_waved_prod (D : LData ι) (s : ℂ) {V : Type} (ℓ : V → ι) (l : List (WEdge V)) :
    (l.map (WEdge.val { D with S := s • D.S } ℓ)).prod =
      s ^ (l.countP (fun e => !e.col)) * (l.map (WEdge.val D ℓ)).prod := by
  induction l with
  | nil => simp
  | cons e l ih =>
    simp only [List.map_cons, List.prod_cons, ih]
    by_cases h : e.col
    · simp only [WEdge.val, h, ite_true, List.countP_cons, Bool.not_true, Bool.false_eq_true, ite_false,
        add_zero]
      split_ifs <;> ring
    · simp [WEdge.val, h, pow_succ, Matrix.smul_apply, List.countP_cons]
      ring

/-- **Target `lwMoment_val_smul`** (`LWMomHomPin`): the value of a graph is homogeneous of degree
`n_{W,black}` in the variance matrix `S` (the coloured `S^±` edges, `M` and `G` are untouched). -/
theorem lwMoment_val_smul :
    ∀ {E I ι : Type} [Fintype I] [DecidableEq I] [Fintype ι] [DecidableEq ι]
      (Γ : LGraph E I) (D : LData ι) (s : ℂ) (ℓe : E → ι),
      Γ.val { D with S := s • D.S } ℓe = s ^ (Γ.waved.countP (fun e => !e.col)) * Γ.val D ℓe := by
  intro E I ι _ _ _ _ Γ D s ℓe
  unfold LGraph.val
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun ℓi _ => ?_
  unfold LGraph.term
  rw [lwMoment_waved_prod]
  have : (Γ.solid.map (SEdge.val { D with S := s • D.S } (Sum.elim ℓe ℓi))) =
      (Γ.solid.map (SEdge.val D (Sum.elim ℓe ℓi))) := rfl
  rw [this]; ring

end Hom

section Bridge

open RBM.Gauss RBM.Gauss.Sizes

/-- **Target `lwMoment_fxy_bridge`** (`LWfBridgePin`): the graph `f_{xy}` at the flow data (variance
`S^{(t)} = t · svarF`) is `t` times the pinned `LWf` (variance `svarF`). -/
theorem lwMoment_fxy_bridge :
    ∀ {d : ℕ} (sz : Sizes d) (n : ℕ) (E t : ℝ)
      (Sp : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (ω : sz.SeqΩ)
      (x y : Idx d (sz.L n) (sz.W n)),
      fxyVal (lwSampleData sz n (zt E t) t (Matrix.diagonal fun _ => mE E) (lwS sz n t) Sp ω) x y =
        (t : ℂ) * RBM.Gauss.Sizes.LWf sz n E t ω x y := by
  intro d sz n E t Sp ω x y
  unfold fxyVal RBM.Gauss.Sizes.LWf
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  split_ifs
  · simp
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun β _ => ?_
    simp only [lwSampleData, lwS, Matrix.of_apply, Matrix.diagonal_apply_eq, STGM, ite_true, RBM.Gauss.Sizes.LWS]
    change ((t * svarF d (sz.L n) (sz.W n) (sz.lam n) α β : ℝ) : ℂ) *
        (Gt sz n E t true ω β β - mE E) * Gt sz n E t true ω x α * Gt sz n E t true ω α y = _
    push_cast
    ring

end Bridge

end RBM.Graph

/-! ## 2. Generic `≺` tools -/

namespace RBM.Gauss.Sizes

open RBM RBM.Gauss RBM.Graph

variable {d : ℕ} (sz : Sizes d)

/-- `≺` from a w.h.p. event on which the pathwise bound holds (for every `τ`). -/
theorem lwMoment_prec_of_whp {U : ℕ → Type*} {ξ ζ : ∀ n, U n → sz.SeqΩ → ℝ}
    (h : ∀ τ : ℝ, 0 < τ → ∃ Ξ : ℕ → Set sz.SeqΩ, sz.Whp Ξ ∧
      ∀ᶠ n in atTop, ∀ ω ∈ Ξ n, ∀ u, ξ n u ω ≤ ((sz.size n : ℕ) : ℝ) ^ τ * ζ n u ω) :
    sz.Prec ξ ζ := by
  intro τ hτ D hD
  obtain ⟨Ξ, hΞ, hev⟩ := h τ hτ
  filter_upwards [hΞ D hD, hev] with n h1 h2
  refine le_trans (measure_mono ?_) h1
  intro ω hω
  obtain ⟨u, hu⟩ := hω
  by_contra hΩ
  exact absurd (h2 ω (not_not.1 hΩ) u) (not_le.2 hu)

/-- A finite sum of `≺`-bounds (deterministic, per element of a list) is a `≺`-bound. -/
theorem lwMoment_sum_det (hsz : sz.SizeTendsto) {V : ℕ → Type} {ι : Type*} (l : List ι) (F : ι → ∀ n, V n → ℝ)
    (G : ∀ n, V n → ℝ) (hG : ∀ n v, 0 ≤ G n v)
    (h : ∀ r ∈ l, ∀ τ : ℝ, 0 < τ → ∀ᶠ n in atTop, ∀ v, F r n v ≤ ((sz.size n : ℕ) : ℝ) ^ τ * G n v) :
    ∀ τ : ℝ, 0 < τ → ∀ᶠ n in atTop, ∀ v, (l.map fun r => F r n v).sum ≤ ((sz.size n : ℕ) : ℝ) ^ τ * G n v := by
  have key : ∀ τ : ℝ, 0 < τ → ∀ᶠ n in atTop, ∀ v, (l.map fun r => F r n v).sum ≤
      (l.length : ℝ) * (((sz.size n : ℕ) : ℝ) ^ (τ / 2) * G n v) := by
    induction l with
    | nil => intro τ hτ; exact Eventually.of_forall fun n v => by simp
    | cons a l ih =>
      intro τ hτ
      filter_upwards [h a (List.mem_cons_self ..) (τ / 2) (half_pos hτ),
        ih (fun r hr => h r (List.mem_cons_of_mem _ hr)) τ hτ] with n h1 h2 v
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      have := h1 v
      have := h2 v
      push_cast
      nlinarith
  intro τ hτ
  filter_upwards [key τ hτ, (tendsto_size sz hsz).eventually (eventually_le_rpow (l.length : ℝ) (half_pos hτ))]
    with n h1 h2 v
  refine (h1 v).trans ?_
  have hN : (0 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hg := hG n v
  calc (l.length : ℝ) * (((sz.size n : ℕ) : ℝ) ^ (τ / 2) * G n v)
      ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * (((sz.size n : ℕ) : ℝ) ^ (τ / 2) * G n v) :=
        mul_le_mul_of_nonneg_right h2 (mul_nonneg hN hg)
    _ = ((sz.size n : ℕ) : ℝ) ^ τ * G n v := by
        rw [← mul_assoc, ← Real.rpow_add (by exact_mod_cast (Nat.zero_lt_of_lt (sz.one_le_size n) : 0 < sz.size n))]
        congr 2; ring

/-! ## 3. The setting, the flow facts and the data -/

/-- The standing hypotheses of `LWMoment` for one choice of the constants and the sequences (an internal
bundle: the fields are the hypotheses of the pin, nothing else). -/
structure LWMomentCtx {d : ℕ} (sz : Sizes d) (κ ε 𝔡 𝔠 : ℝ) (z : ℕ → ℂ) (t : ℕ → ℝ)
    (ε₀ C₁ C₂ C₃ : ℝ) (Cc : ℝ → ℝ) (Ψ : ℕ → ℝ) (Φ : ℕ → ℝ → ℝ) : Prop where
  hd : 3 ≤ d
  hκ : 0 < κ
  hε : 0 < ε
  h𝔡 : 0 < 𝔡
  flow : STFlow sz κ ε 𝔠 𝔡 z
  t0 : ∀ n, 0 ≤ t n
  t1 : ∀ n, t n ≤ lemT (z n)
  assm : LWAssm sz (STflowE z) t ε₀ Ψ Φ C₁ C₂ C₃ Cc

variable {sz} {κ ε 𝔡 𝔠 : ℝ} {z : ℕ → ℂ} {t : ℕ → ℝ} {ε₀ C₁ C₂ C₃ : ℝ} {Cc : ℝ → ℝ} {Ψ : ℕ → ℝ}
  {Φ : ℕ → ℝ → ℝ}

/-- `|E_n| < 2 - κ/2`, `t_n < 1`, admissibility and `1 - t ≥ N^{-1+ε/2}` (`v3_premises_of_stFlow`). -/
theorem lwMoment_flow_facts (S : LWMomentCtx sz κ ε 𝔡 𝔠 z t ε₀ C₁ C₂ C₃ Cc Ψ Φ) :
    sz.Admissible 𝔠 𝔡 ∧ (∀ n, |STflowE z n| < 2 - κ / 2) ∧ (∀ n, t n < 1) ∧ sz.RangeCond (ε / 2) t :=
  RBM.Green.v3_premises_of_stFlow sz S.hκ S.hε S.flow S.t1

theorem lwMoment_size_tendsto (S : LWMomentCtx sz κ ε 𝔡 𝔠 z t ε₀ C₁ C₂ C₃ Cc Ψ Φ) : sz.SizeTendsto :=
  (lwMoment_flow_facts S).1.2.2.1

/-- `η_t ≥ N^{-1}` eventually (`eta_lower_of_rangeCond`). -/
theorem lwMoment_eta_lower (S : LWMomentCtx sz κ ε 𝔡 𝔠 z t ε₀ C₁ C₂ C₃ Cc Ψ Φ) :
    ∀ᶠ n in atTop, ((sz.size n : ℕ) : ℝ) ^ (-1 : ℝ) ≤ etaT (STflowE z n) (t n) := by
  obtain ⟨-, hE, -, hR⟩ := lwMoment_flow_facts S
  have := RBM.Green.eta_lower_of_rangeCond sz (half_pos S.hκ) (half_pos S.hε) (lwMoment_size_tendsto S) hE hR
  filter_upwards [this] with n hn
  rwa [etaT_eq_zt_im]

theorem lwMoment_etaT_le_one {E t : ℝ} (hE : |E| < 2) (h0 : 0 ≤ t) (ht : t < 1) : etaT E t ≤ 1 := by
  have h1 : (mE E).im ≤ 1 := by
    rw [mE_im]
    have : Real.sqrt (4 - E ^ 2) ≤ 2 :=
      Real.sqrt_le_iff.mpr ⟨by norm_num, by nlinarith [sq_nonneg E]⟩
    linarith
  have h2 : 0 < (mE E).im := mE_im_pos hE
  unfold etaT
  nlinarith

/-! ## 4. The expansion identity: `E |f_{xy}|^p ≤ Σ_r ‖E r.2.val D₁‖` -/

section Expand

variable (sz)

/-- The graph data of `f_{xy}` at the flow time, with the variance matrix `svarF` (`S := lwS 1`, so that the
data at time `t` is `{D₁ with S := t • D₁.S}`), `M = m I`, `S⁺ = lwSplus` at `t`. -/
def lwMoment_D (n : ℕ) (E t : ℝ) (ω : sz.SeqΩ) : LData (Idx d (sz.L n) (sz.W n)) :=
  lwSampleData sz n (zt E t) t (Matrix.diagonal fun _ => mE E) (lwS sz n 1) (lwSplus sz n t (mE E)) ω

theorem lwMoment_Dt_eq (n : ℕ) (E t : ℝ) (ω : sz.SeqΩ) :
    lwSampleData sz n (zt E t) t (Matrix.diagonal fun _ => mE E) (lwS sz n t) (lwSplus sz n t (mE E)) ω =
      { lwMoment_D sz n E t ω with S := (t : ℂ) • (lwMoment_D sz n E t ω).S } := by
  unfold lwMoment_D lwSampleData
  congr 1
  ext i j
  simp [lwS]

theorem lwMoment_pval_smul {ι E0 : Type} [Fintype ι] [DecidableEq ι] (P : PGraph E0) (D : LData ι) (s : ℂ)
    (ℓe : E0 → ι) :
    P.val { D with S := s • D.S } ℓe = s ^ (P.g.waved.countP fun e => !e.col) * P.val D ℓe := by
  classical
  by_cases h : ∃ ℓ' : P.E' → ι, ℓe = ℓ' ∘ P.ext
  · obtain ⟨ℓ', hℓ'⟩ := h
    rw [P.val_of_factor _ hℓ', P.val_of_factor _ hℓ']
    exact lwMoment_val_smul P.g D s ℓ'
  · rw [P.val_of_not _ h, P.val_of_not _ h]; simp

theorem lwMoment_pval_evX {ι : Type} [Fintype ι] [DecidableEq ι] (m : ℂ) (r : (ℕ × ℕ) × PGraph (Fin 2))
    (D : LData ι) (ℓe : Fin 2 → ι) :
    (lwEvX m r).val D ℓe = (m ^ r.1.1 * star m ^ r.1.2) * r.2.val D ℓe := by
  classical
  by_cases h : ∃ ℓ' : r.2.E' → ι, ℓe = ℓ' ∘ r.2.ext
  · obtain ⟨ℓ', hℓ'⟩ := h
    rw [r.2.val_of_factor D hℓ', (lwEvX m r).val_of_factor D (ℓ' := ℓ') hℓ']
    change LGraph.val { r.2.g with coeff := m ^ r.1.1 * star m ^ r.1.2 * r.2.g.coeff } D ℓ' = _
    unfold LGraph.val
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun ℓi _ => ?_
    unfold LGraph.term
    ring
  · rw [r.2.val_of_not D h, (lwEvX m r).val_of_not D h]; simp

theorem lwMoment_norm_list_sum_le {α : Type*} (l : List α) (f : α → ℂ) :
    ‖(l.map f).sum‖ ≤ (l.map fun x => ‖f x‖).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (norm_add_le _ _).trans (add_le_add le_rfl ih)

theorem lwMoment_pow_conj (z : ℂ) (k : ℕ) : z ^ k * star z ^ k = ((‖z‖ ^ (2 * k) : ℝ) : ℂ) := by
  rw [← mul_pow, Complex.star_def, Complex.mul_conj', pow_mul]
  push_cast; ring

/-- **The expansion identity** (`7_8:943-945`): from the engine lists, `E |f_{xy}|^p ≤ Σ_r ‖E r.2.val D₁‖`
(the homogeneity, `n_{W,black} ≥ p`, `t ≤ 1`, and `t > 0`). -/
theorem lwMoment_expand {p : ℕ} (hp : Even p) (n : ℕ) {E t : ℝ} (hE : |E| < 2) (ht0 : 0 < t) (ht1 : t < 1)
    {c : ℝ} {K0 : ℕ} {D : ℝ} {outsX errsX : List ((ℕ × ℕ) × PGraph (Fin 2))}
    (h : LWLocRegConcl p (mE E) c K0 d D (outsX.map (lwEvX (mE E))) (errsX.map (lwEvX (mE E))))
    (hw : ∀ r ∈ outsX ++ errsX, p ≤ r.2.g.waved.countP (fun e => !e.col))
    (x y : Idx d (sz.L n) (sz.W n)) :
    ∫ ω, ‖LWf sz n E t ω x y‖ ^ p ∂sz.seqP ≤
      ((outsX ++ errsX).map fun r => ‖∫ ω, r.2.val (lwMoment_D sz n E t ω) ![x, y] ∂sz.seqP‖).sum := by
  classical
  have hm0 : mE E ≠ 0 := lwWx_mE_ne E hE
  have hnorm : ‖mE E‖ = 1 := norm_mE hE.le
  have hflow := lwWx_flow E t hE
  have him : 0 < (zt E t).im := lwWx_im_pos E t hE ht1
  have hmt : ‖mE E‖ ^ 2 * t < 1 := by rw [hnorm]; simpa using ht1
  have hSp := fun i j => lwSplus_spec (sz := sz) (n := n) ht0.le hmt i j
  have hSpT := lwSymm_lwSplus_symm (sz := sz) (n := n) ht0.le hmt
  have hid := h.2.2.2.1 (sz := sz) (n := n) (z := zt E t) (u := t) (lwSplus sz n t (mE E))
    (Matrix.diagonal fun _ => mE E) (RBM.Green.gaussIBP sz) him ht0 hm0 hflow hSp hSpT
    (fun a => by simp) (fun a b hab => by simp [Matrix.diagonal_apply_ne _ hab]) ![x, y]
  -- the left side
  have hL : ∀ ω : sz.SeqΩ, (fxyPowGraph p).pack.val
      (lwSampleData sz n (zt E t) t (Matrix.diagonal fun _ => mE E) (lwS sz n t) (lwSplus sz n t (mE E)) ω)
        ![x, y] = ((t ^ p * ‖LWf sz n E t ω x y‖ ^ p : ℝ) : ℂ) := by
    intro ω
    rw [LGraph.pack_val, fxyPowGraph_val_eq _ (fun i j => by simp [lwSampleData, lwS]) p hp x y,
      lwMoment_fxy_bridge sz n E t (lwSplus sz n t (mE E)) ω x y]
    obtain ⟨k, hk⟩ := hp
    have hk2 : p / 2 = k := by omega
    rw [hk2, show (star ((t : ℂ) * LWf sz n E t ω x y)) = (t : ℂ) * star (LWf sz n E t ω x y) by
      simp [star_mul'], mul_pow, mul_pow]
    have h1 := lwMoment_pow_conj (LWf sz n E t ω x y) k
    calc _ = (t : ℂ) ^ k * (t : ℂ) ^ k * (LWf sz n E t ω x y ^ k * star (LWf sz n E t ω x y) ^ k) := by ring
      _ = _ := by rw [h1, hk]; push_cast; ring
  -- the right side
  have hR : ∀ r : (ℕ × ℕ) × PGraph (Fin 2),
      ∫ ω, (lwEvX (mE E) r).val (lwSampleData sz n (zt E t) t (Matrix.diagonal fun _ => mE E) (lwS sz n t)
        (lwSplus sz n t (mE E)) ω) ![x, y] ∂sz.seqP =
      (mE E ^ r.1.1 * star (mE E) ^ r.1.2) * ((t : ℂ) ^ (r.2.g.waved.countP fun e => !e.col) *
        ∫ ω, r.2.val (lwMoment_D sz n E t ω) ![x, y] ∂sz.seqP) := by
    intro r
    simp only [lwMoment_Dt_eq, lwMoment_pval_evX, lwMoment_pval_smul]
    rw [integral_const_mul, integral_const_mul]
    have hcnt : (lwEvX (mE E) r).g.waved.countP (fun e => !e.col) = r.2.g.waved.countP (fun e => !e.col) := rfl
    rw [hcnt]
    ring
  have hI0 : 0 ≤ ∫ ω, ‖LWf sz n E t ω x y‖ ^ p ∂sz.seqP := integral_nonneg fun ω => by positivity
  have hLHS : (∫ ω, (fxyPowGraph p).pack.val (lwSampleData sz n (zt E t) t (Matrix.diagonal fun _ => mE E)
        (lwS sz n t) (lwSplus sz n t (mE E)) ω) ![x, y] ∂sz.seqP) =
      ((t ^ p * ∫ ω, ‖LWf sz n E t ω x y‖ ^ p ∂sz.seqP : ℝ) : ℂ) := by
    simp only [hL]
    rw [integral_complex_ofReal, integral_const_mul]
  rw [hLHS] at hid
  have hid' : ((t ^ p * ∫ ω, ‖LWf sz n E t ω x y‖ ^ p ∂sz.seqP : ℝ) : ℂ) =
      ((outsX ++ errsX).map fun r => (mE E ^ r.1.1 * star (mE E) ^ r.1.2) *
        ((t : ℂ) ^ (r.2.g.waved.countP fun e => !e.col) *
          ∫ ω, r.2.val (lwMoment_D sz n E t ω) ![x, y] ∂sz.seqP)).sum := by
    rw [hid, List.map_append, List.sum_append]
    simp only [List.map_map]
    congr 2 <;> exact List.map_congr_left (fun r _ => hR r)
  have hnn : 0 ≤ t ^ p * ∫ ω, ‖LWf sz n E t ω x y‖ ^ p ∂sz.seqP := mul_nonneg (by positivity) hI0
  have h1 : t ^ p * ∫ ω, ‖LWf sz n E t ω x y‖ ^ p ∂sz.seqP ≤
      ((outsX ++ errsX).map fun r => t ^ p * ‖∫ ω, r.2.val (lwMoment_D sz n E t ω) ![x, y] ∂sz.seqP‖).sum := by
    have h2 := congrArg norm hid'
    rw [Complex.norm_real, Real.norm_of_nonneg hnn] at h2
    rw [h2]
    refine (lwMoment_norm_list_sum_le _ _).trans ?_
    refine List.sum_le_sum fun r hr => ?_
    simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0]
    have hn1 : ‖mE E‖ ^ r.1.1 * ‖star (mE E)‖ ^ r.1.2 = 1 := by
      rw [norm_star, hnorm]; simp
    rw [hn1, one_mul]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one ht0.le ht1.le (hw r hr)) (norm_nonneg _)
  rw [List.sum_map_mul_left] at h1
  exact le_of_mul_le_mul_left h1 (by positivity)

end Expand

/-! ## 5. Decay of `S`, `S⁺`; the envelope and the floors -/

section Decay

variable {sz : Sizes d} {κ ε 𝔡 𝔠 : ℝ} {z : ℕ → ℂ} {t : ℕ → ℝ} {ε₀ C₁ C₂ C₃ : ℝ} {Cc : ℝ → ℝ} {Ψ : ℕ → ℝ}
  {Φ : ℕ → ℝ → ℝ}

/-- `(eq:estSpm-W)` for the data `D₁`: `S = svarF` and `S⁺` at time `t_n` decay at the block distance, with
constants independent of `n`. -/
theorem lwMoment_decay (S : LWMomentCtx sz κ ε 𝔡 𝔠 z t ε₀ C₁ C₂ C₃ Cc Ψ Φ) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ᶠ n in atTop,
      (∀ x y : Idx d (sz.L n) (sz.W n), ‖lwS sz n 1 x y‖ ≤
        C * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * Real.exp (-(c * (lwBdist d (sz.L n) (sz.W n) x y : ℝ)))) ∧
      (∀ x y : Idx d (sz.L n) (sz.W n), ‖lwSplus sz n (t n) (mE (STflowE z n)) x y‖ ≤
        C * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * Real.exp (-(c * (lwBdist d (sz.L n) (sz.W n) x y : ℝ)))) := by
  obtain ⟨hadm, hE, ht1', -⟩ := lwMoment_flow_facts S
  obtain ⟨C, c, hC, hc, h⟩ := lwSpOf_decay_E d S.hd 𝔡⁻¹ (κ / 2) (inv_pos.2 S.h𝔡) (half_pos S.hκ)
  refine ⟨2 * C, c, by positivity, hc, ?_⟩
  filter_upwards [hadm.2.2.2.2] with n hn
  have hg : 0 < sz.lam n :=
    lt_of_lt_of_le (Real.rpow_pos_of_pos (by exact_mod_cast sz.W_pos n) _) hn.1
  have hEn : |STflowE z n| ≤ 2 - κ / 2 := (hE n).le
  obtain ⟨h1, -⟩ := h (sz.L n) (sz.W n) (sz.three_le_L n) (sz.lam n) (1 / 2) (STflowE z n) hg hn.2
    (by norm_num) (by norm_num) hEn
  obtain ⟨-, h2⟩ := h (sz.L n) (sz.W n) (sz.three_le_L n) (sz.lam n) (t n) (STflowE z n) hg hn.2 (S.t0 n)
    (ht1' n) hEn
  have hW : (0 : ℝ) ≤ (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * Real.exp (-(c * 0)) := by positivity
  refine ⟨fun x y => ?_, fun x y => ?_⟩
  · have e : lwS sz n 1 x y = 2 * lwSmat d (sz.L n) (sz.W n) (sz.lam n) (1 / 2) x y := by
      simp [lwS, lwSmat]
    rw [e, norm_mul]
    have := h1 x y
    simp only [Complex.norm_ofNat]
    linarith
  · rw [lwSplus_eq]
    have := h2 x y
    have hn0 : 0 ≤ (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * Real.exp (-(c * (lwBdist d (sz.L n) (sz.W n) x y : ℝ))) := by
      positivity
    nlinarith

end Decay

section Numerics

/-- `size(Γ) ≤ N^{n_M + n_V} B^{n_S}` for `0 < Ψ ≤ B`, `B ≥ 1` (`N = (W L)^d`): `(L^d)^{n_M} ≤ N^{n_M}`,
`Ψ^{n_S} ≤ B^{n_S}`, `W^{-d(n_W - n_V)} ≤ (W^d)^{n_V} ≤ N^{n_V}`. -/
theorem lwMoment_scalingSize_le {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]
    (Γ : LGraph E I) {Ψ B : ℝ} (hΨ0 : 0 < Ψ) (hΨB : Ψ ≤ B) (hB : 1 ≤ B) (W L d : ℕ) (hW : 1 ≤ W) (hL : 1 ≤ L) :
    Γ.scalingSize Ψ W d L ≤ (((W * L) ^ d : ℕ) : ℝ) ^ (Γ.nM + Γ.nV) * B ^ Γ.nS := by
  unfold LGraph.scalingSize Counters.scalingSize
  simp only [LGraph.counters]
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hN1 : ((W : ℝ) ^ d) ≤ (((W * L) ^ d : ℕ) : ℝ) := by
    push_cast; exact pow_le_pow_left₀ (by linarith) (by nlinarith) d
  have hN2 : ((L : ℝ) ^ d) ≤ (((W * L) ^ d : ℕ) : ℝ) := by
    push_cast; exact pow_le_pow_left₀ (by linarith) (by nlinarith) d
  have h1 : ((L : ℝ) ^ d) ^ Γ.nM ≤ (((W * L) ^ d : ℕ) : ℝ) ^ Γ.nM := pow_le_pow_left₀ (by positivity) hN2 _
  have h2 : Ψ ^ Γ.nS ≤ B ^ Γ.nS := pow_le_pow_left₀ hΨ0.le hΨB _
  have h3 : (W : ℝ) ^ (-(d : ℤ) * ((Γ.nW : ℤ) - (Γ.nV : ℤ))) ≤ (((W * L) ^ d : ℕ) : ℝ) ^ Γ.nV := by
    have hex : -(d : ℤ) * ((Γ.nW : ℤ) - (Γ.nV : ℤ)) ≤ ((d * Γ.nV : ℕ) : ℤ) := by
      have h0 : (0 : ℤ) ≤ (d : ℤ) * (Γ.nW : ℤ) := by positivity
      push_cast; nlinarith
    calc (W : ℝ) ^ (-(d : ℤ) * ((Γ.nW : ℤ) - (Γ.nV : ℤ))) ≤ (W : ℝ) ^ ((d * Γ.nV : ℕ) : ℤ) :=
          zpow_le_zpow_right₀ hW1 hex
      _ = ((W : ℝ) ^ d) ^ Γ.nV := by rw [zpow_natCast, pow_mul]
      _ ≤ _ := pow_le_pow_left₀ (by positivity) hN1 _
  have hN0 : (0 : ℝ) ≤ (((W * L) ^ d : ℕ) : ℝ) := Nat.cast_nonneg _
  calc ((L : ℝ) ^ d) ^ Γ.nM * Ψ ^ Γ.nS * (W : ℝ) ^ (-(d : ℤ) * ((Γ.nW : ℤ) - (Γ.nV : ℤ)))
      ≤ ((((W * L) ^ d : ℕ) : ℝ) ^ Γ.nM * B ^ Γ.nS) * (((W * L) ^ d : ℕ) : ℝ) ^ Γ.nV := by
        refine mul_le_mul (mul_le_mul h1 h2 (by positivity) (by positivity)) h3 (by positivity) (by positivity)
    _ = _ := by ring

/-- The deterministic facts on the class `Φ` used below, eventually in `n`: positivity, `Φ(0) ≤ K(r) Φ(r)` with the
polynomial loss `K(r) = Cc(2) C₁ max(1, r)^{C₂}` (`(eq:Psi)`), and `Φ(c r) ≤ K_c Φ(r)` for `0 < c ≤ 1`. -/
theorem lwMoment_phi_facts {ε₀ C₁ C₂ C₃ : ℝ} {Cc : ℝ → ℝ} {Φ : ℕ → ℝ → ℝ} (hcls : LWClass sz ε₀ C₃ Φ)
    (hrel : LWPsiRel C₁ C₂ Cc Φ) :
    ∀ᶠ n in atTop, 0 < Cc 2 ∧ (∀ r : ℝ, 0 ≤ r → 0 < Φ n r) ∧
      (∀ r : ℝ, 0 ≤ r → Φ n 0 ≤ Cc 2 * C₁ * (max 1 r) ^ C₂ * Φ n r) ∧
      ∀ cG : ℝ, 0 < cG → cG ≤ 1 → ∀ r : ℝ, 0 ≤ r →
        Φ n (cG * r) ≤ (max 1 (Cc 2) * C₁ * (cG⁻¹) ^ C₂) * Φ n r := by
  obtain ⟨hanti, hC₁, hC₂, hrel1, hrel2⟩ := hrel
  filter_upwards [hcls.1, hrel1 2 (by norm_num), hrel2] with n hpos h1 h2
  have hP : ∀ r : ℝ, 0 ≤ r → 0 < Φ n r := fun r hr => (hpos r hr).1
  have hCc : 0 < Cc 2 := by
    by_contra hcon
    push Not at hcon
    have := h1 1 zero_le_one (by norm_num)
    nlinarith [hP 0 le_rfl, hP 1 zero_le_one]
  have hcmp : ∀ r : ℝ, 0 ≤ r → Φ n 0 ≤ Cc 2 * C₁ * (max 1 r) ^ C₂ * Φ n r := by
    intro r hr
    by_cases hr1 : r ≤ 1
    · rw [max_eq_left hr1, Real.one_rpow, mul_one]
      have := h1 r hr (by linarith)
      nlinarith [mul_nonneg (mul_nonneg hCc.le (sub_nonneg.2 hC₁.le)) (hP r hr).le]
    · push Not at hr1
      rw [max_eq_right hr1.le]
      have e1 := h1 1 zero_le_one (by norm_num)
      have e2 := h2 1 r le_rfl hr1.le
      rw [div_one] at e2
      calc Φ n 0 ≤ Cc 2 * Φ n 1 := e1
        _ ≤ Cc 2 * (C₁ * r ^ C₂ * Φ n r) := mul_le_mul_of_nonneg_left e2 hCc.le
        _ = _ := by ring
  refine ⟨hCc, hP, hcmp, ?_⟩
  intro cG hcG hcG1 r hr
  have hinv : 1 ≤ cG⁻¹ := one_le_inv_iff₀.2 ⟨hcG, hcG1⟩
  have hKp : 1 ≤ cG⁻¹ ^ C₂ := Real.one_le_rpow hinv (by linarith)
  have hmax : 0 ≤ max 1 (Cc 2) := by positivity
  have hmax1 : 1 ≤ max 1 (Cc 2) := le_max_left _ _
  have hPr := hP r hr
  by_cases hx : 1 ≤ cG * r
  · have hrpos : 0 < r := by
      by_contra h0; push Not at h0; nlinarith
    have e := h2 (cG * r) r hx (by nlinarith)
    have e' : r / (cG * r) = cG⁻¹ := by field_simp
    rw [e'] at e
    calc Φ n (cG * r) ≤ C₁ * cG⁻¹ ^ C₂ * Φ n r := e
      _ ≤ (max 1 (Cc 2) * C₁ * (cG⁻¹) ^ C₂) * Φ n r := by
        refine mul_le_mul_of_nonneg_right ?_ hPr.le
        nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.2 hmax1) (by linarith : (0 : ℝ) ≤ C₁)) (by linarith : (0 : ℝ) ≤ cG⁻¹ ^ C₂)]
  · push Not at hx
    have e1 : Φ n (cG * r) ≤ Φ n 0 :=
      hanti n (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 (by positivity)) (by positivity)
    have hmx : max 1 r ≤ cG⁻¹ := by
      refine max_le hinv ?_
      have : r < cG⁻¹ := by
        rw [← one_div, lt_div_iff₀ hcG]; linarith [mul_comm r cG]
      exact this.le
    have e3 : (max 1 r) ^ C₂ ≤ cG⁻¹ ^ C₂ := Real.rpow_le_rpow (by positivity) hmx (by linarith)
    calc Φ n (cG * r) ≤ Φ n 0 := e1
      _ ≤ Cc 2 * C₁ * (max 1 r) ^ C₂ * Φ n r := hcmp r hr
      _ ≤ Cc 2 * C₁ * cG⁻¹ ^ C₂ * Φ n r := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left e3 (by positivity)) hPr.le
      _ ≤ _ := by
        refine mul_le_mul_of_nonneg_right ?_ hPr.le
        nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.2 (le_max_right 1 (Cc 2))) (by linarith : (0 : ℝ) ≤ C₁)) (by linarith : (0 : ℝ) ≤ cG⁻¹ ^ C₂)]

/-- **The tail `e^{-c (log W)²/2}` beats every power of `N`** (`r = (log W)²` of `(eq:far_ab)`, `7_8:955-958`):
`W ≥ N^𝔠` and `log W → ∞`. -/
theorem lwMoment_tail (S : LWMomentCtx sz κ ε 𝔡 𝔠 z t ε₀ C₁ C₂ C₃ Cc Ψ Φ) {c : ℝ} (hc : 0 < c) (a b : ℝ) :
    ∀ᶠ n in atTop, Real.exp (-(c * Real.log ((sz.W n : ℕ) : ℝ) ^ 2 / 2)) * ((sz.size n : ℕ) : ℝ) ^ a ≤
      ((sz.size n : ℕ) : ℝ) ^ (-b) := by
  obtain ⟨h𝔠, -, hsz, hband, -⟩ := (lwMoment_flow_facts S).1
  set A : ℝ := |a| + |b| with hA
  set M : ℝ := 2 * A / (𝔠 * c) with hM
  have hA0 : 0 ≤ A := by positivity
  filter_upwards [hband, ((tendsto_rpow_atTop h𝔠).comp hsz).eventually_ge_atTop (Real.exp M),
    hsz.eventually_ge_atTop 1] with n hb hbig hN1
  set N : ℝ := ((sz.size n : ℕ) : ℝ) with hN
  have hN0 : 0 < N := by linarith
  have hW0 : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hbig' : Real.exp M ≤ ((sz.W n : ℕ) : ℝ) := le_trans hbig hb
  have hLg : M ≤ Real.log ((sz.W n : ℕ) : ℝ) := (Real.le_log_iff_exp_le hW0).2 hbig'
  set Lg : ℝ := Real.log ((sz.W n : ℕ) : ℝ) with hLgdef
  have hM0 : 0 ≤ M := by positivity
  have h1 : N ^ (a + b) ≤ N ^ A :=
    Real.rpow_le_rpow_of_exponent_le hN1 (by linarith [le_abs_self a, le_abs_self b])
  have h2 : N ^ A ≤ ((sz.W n : ℕ) : ℝ) ^ (A / 𝔠) := Sizes.size_rpow_le_W_rpow sz h𝔠 n hb hA0
  have h3 : ((sz.W n : ℕ) : ℝ) ^ (A / 𝔠) = Real.exp (Lg * (A / 𝔠)) := by
    rw [Real.rpow_def_of_pos hW0]
  have h4 : Lg * (A / 𝔠) ≤ c * Lg ^ 2 / 2 := by
    have : A / 𝔠 = c * M / 2 := by rw [hM]; field_simp
    rw [this]
    have hL0 : 0 ≤ Lg := le_trans hM0 hLg
    nlinarith [mul_le_mul_of_nonneg_left hLg (by positivity : 0 ≤ c * Lg / 2)]
  have h5 : N ^ (a + b) ≤ Real.exp (c * Lg ^ 2 / 2) :=
    h1.trans (h2.trans (h3 ▸ Real.exp_le_exp.2 h4))
  have hNb : 0 < N ^ b := Real.rpow_pos_of_pos hN0 b
  refine le_of_mul_le_mul_right ?_ hNb
  rw [← Real.rpow_add hN0 (-b) b, neg_add_cancel, Real.rpow_zero, mul_assoc, ← Real.rpow_add hN0]
  calc Real.exp (-(c * Lg ^ 2 / 2)) * N ^ (a + b) ≤ Real.exp (-(c * Lg ^ 2 / 2)) * Real.exp (c * Lg ^ 2 / 2) :=
        mul_le_mul_of_nonneg_left h5 (Real.exp_pos _).le
    _ = 1 := by rw [← Real.exp_add]; simp

theorem lwMoment_zdistInf_le (L : ℕ) (x : Zd d L) : zdistInf d L x ≤ L := by
  unfold zdistInf
  exact Finset.sup_le fun i _ => (min_le_right _ _).trans (Nat.sub_le _ _)

/-- **The polynomial floor of the control** (row 11 of the preflight): `R ≥ N^{-p(2+C₂)}` for
`R = (η⁻¹ Φ(0) Φ(|a-b|))^p`, from `W^{-d/2} ≤ C₃ Φ(0)`, `Φ(0) ≤ Cc(2) C₁ max(1,r)^{C₂} Φ(r)`, `η ≤ 1`. -/
theorem lwMoment_floor (S : LWMomentCtx sz κ ε 𝔡 𝔠 z t ε₀ C₁ C₂ C₃ Cc Ψ Φ) (p : ℕ) :
    ∀ᶠ n in atTop, ∀ x y : Idx d (sz.L n) (sz.W n),
      ((sz.size n : ℕ) : ℝ) ^ (-((p : ℝ) * (2 + C₂))) ≤
        ((etaT (STflowE z n) (t n))⁻¹ * Φ n 0 *
          Φ n (1 * ((zdistInf d (sz.L n) (STblk sz n x - STblk sz n y) : ℕ) : ℝ))) ^ p := by
  obtain ⟨-, hE, ht1', -⟩ := lwMoment_flow_facts S
  have hsz := lwMoment_size_tendsto S
  have hcls := S.assm.2.2.2.1
  have hC3 : 0 < C₃ := hcls.2.1
  filter_upwards [lwMoment_phi_facts hcls S.assm.2.2.2.2.1, hcls.2.2, hsz.eventually_ge_atTop 1,
    hsz.eventually_ge_atTop (C₃ ^ 2 * Cc 2 * C₁)] with n hph hwin hN1 hNbig
  obtain ⟨hCc, hP, hcmp, -⟩ := hph
  intro x y
  set N : ℝ := ((sz.size n : ℕ) : ℝ) with hN
  have hN0 : 0 < N := by linarith
  have hEn : |STflowE z n| < 2 := by linarith [hE n, S.hκ]
  have hη0 : 0 < etaT (STflowE z n) (t n) := etaT_pos hEn (ht1' n)
  have hη1 : etaT (STflowE z n) (t n) ≤ 1 := lwMoment_etaT_le_one hEn (S.t0 n) (ht1' n)
  have hηinv : 1 ≤ (etaT (STflowE z n) (t n))⁻¹ := one_le_inv_iff₀.2 ⟨hη0, hη1⟩
  set r : ℝ := 1 * ((zdistInf d (sz.L n) (STblk sz n x - STblk sz n y) : ℕ) : ℝ) with hr
  have hr0 : 0 ≤ r := by positivity
  have hLN : (sz.L n : ℝ) ≤ N := by
    have hd0 : 1 ≤ d := by have := S.hd; omega
    have h1 : sz.L n ≤ sz.size n := by
      unfold Sizes.size
      calc sz.L n = (sz.L n) ^ 1 := (pow_one _).symm
        _ ≤ (sz.L n) ^ d := Nat.pow_le_pow_right (by have := sz.three_le_L n; omega) hd0
        _ ≤ (sz.W n * sz.L n) ^ d := Nat.pow_le_pow_left (Nat.le_mul_of_pos_left _ (sz.W_pos n)) d
    rw [hN]; exact_mod_cast h1
  have hr1 : max 1 r ≤ N := by
    refine max_le hN1 ?_
    rw [hr, one_mul]
    have h6 : ((zdistInf d (sz.L n) (STblk sz n x - STblk sz n y) : ℕ) : ℝ) ≤ (sz.L n : ℝ) := by
      exact_mod_cast lwMoment_zdistInf_le (sz.L n) _
    linarith
  have hmaxN : (max 1 r) ^ C₂ ≤ N ^ C₂ :=
    Real.rpow_le_rpow (by positivity) hr1 (by linarith [S.assm.2.2.2.2.1.2.2.1])
  have hΦr := hP r hr0
  have hΦ0 := hP 0 le_rfl
  have h1 : Φ n 0 ≤ Cc 2 * C₁ * N ^ C₂ * Φ n r := by
    refine (hcmp r hr0).trans (mul_le_mul_of_nonneg_right ?_ hΦr.le)
    exact mul_le_mul_of_nonneg_left hmaxN (by have := S.assm.2.2.2.2.1.2.1; positivity)
  -- `Φ(0) ≥ N^{-1/2} / C₃`
  have hW0 : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hWN : ((sz.W n : ℕ) : ℝ) ^ d ≤ N := by
    have h : (sz.W n) ^ d ≤ sz.size n := by
      unfold Sizes.size
      exact Nat.pow_le_pow_left (Nat.le_mul_of_pos_right _ (by have := sz.three_le_L n; omega)) d
    rw [hN]; exact_mod_cast h
  have hNh : N ^ (-(1 : ℝ) / 2) ≤ ((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2) := by
    have e : ((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2) = (((sz.W n : ℕ) : ℝ) ^ d) ^ (-(1 : ℝ) / 2) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hW0.le]; congr 1; ring
    rw [e]
    exact Real.rpow_le_rpow_of_nonpos (by positivity) hWN (by norm_num)
  have hΦ0lb : N ^ (-(1 : ℝ) / 2) ≤ C₃ * Φ n 0 := hNh.trans hwin
  have hNh2 : N ^ (-(1 : ℝ) / 2) * N ^ (-(1 : ℝ) / 2) = N ^ (-(1 : ℝ)) := by
    rw [← Real.rpow_add hN0]; congr 1; ring
  -- `η⁻¹ Φ(0) Φ(r) ≥ Φ(0)² / (Cc(2) C₁ N^{C₂}) ≥ N^{-(2 + C₂)}`
  have hCK : 0 < Cc 2 * C₁ * N ^ C₂ := by have := S.assm.2.2.2.2.1.2.1; positivity
  have h2 : Φ n 0 * Φ n 0 ≤ Cc 2 * C₁ * N ^ C₂ * (Φ n 0 * Φ n r) := by nlinarith
  have h3 : N ^ (-(1 : ℝ)) ≤ C₃ ^ 2 * (Φ n 0 * Φ n 0) := by
    have := mul_le_mul hΦ0lb hΦ0lb (by positivity) (by positivity)
    rw [hNh2] at this; nlinarith
  have h4 : N ^ (-(2 + C₂)) ≤ Φ n 0 * Φ n r := by
    have hC3N : C₃ ^ 2 * (Cc 2 * C₁ * N ^ C₂) ≤ N ^ (1 + C₂) := by
      rw [Real.rpow_add hN0, Real.rpow_one]
      have := mul_le_mul_of_nonneg_right hNbig (by positivity : (0 : ℝ) ≤ N ^ C₂)
      nlinarith
    have e1 : N ^ (-(2 + C₂)) * N ^ (1 + C₂) = N ^ (-(1 : ℝ)) := by
      rw [← Real.rpow_add hN0]; congr 1; ring
    have : N ^ (-(2 + C₂)) * (C₃ ^ 2 * (Cc 2 * C₁ * N ^ C₂)) ≤ C₃ ^ 2 * (Cc 2 * C₁ * N ^ C₂) * (Φ n 0 * Φ n r) := by
      calc N ^ (-(2 + C₂)) * (C₃ ^ 2 * (Cc 2 * C₁ * N ^ C₂)) ≤ N ^ (-(2 + C₂)) * N ^ (1 + C₂) :=
            mul_le_mul_of_nonneg_left hC3N (by positivity)
        _ = N ^ (-(1 : ℝ)) := e1
        _ ≤ C₃ ^ 2 * (Φ n 0 * Φ n 0) := h3
        _ ≤ C₃ ^ 2 * (Cc 2 * C₁ * N ^ C₂ * (Φ n 0 * Φ n r)) := mul_le_mul_of_nonneg_left h2 (by positivity)
        _ = _ := by ring
    have hpos : 0 < C₃ ^ 2 * (Cc 2 * C₁ * N ^ C₂) := by positivity
    nlinarith
  have h5 : N ^ (-(2 + C₂)) ≤ (etaT (STflowE z n) (t n))⁻¹ * Φ n 0 * Φ n r := by
    calc N ^ (-(2 + C₂)) ≤ Φ n 0 * Φ n r := h4
      _ = 1 * (Φ n 0 * Φ n r) := (one_mul _).symm
      _ ≤ (etaT (STflowE z n) (t n))⁻¹ * (Φ n 0 * Φ n r) :=
          mul_le_mul_of_nonneg_right hηinv (by positivity)
      _ = _ := by ring
  calc N ^ (-((p : ℝ) * (2 + C₂))) = (N ^ (-(2 + C₂))) ^ p := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; congr 1; ring
    _ ≤ _ := pow_le_pow_left₀ (Real.rpow_nonneg hN0.le _) h5 p

end Numerics

/-! ## 6. The deterministic envelope `‖Q.val D₁‖ ≤ N^K` -/

section Envelope

variable {sz : Sizes d} {κ ε 𝔡 𝔠 : ℝ} {z : ℕ → ℂ} {t : ℕ → ℝ} {ε₀ C₁ C₂ C₃ : ℝ} {Cc : ℝ → ℝ} {Ψ : ℕ → ℝ}
  {Φ : ℕ → ℝ → ℝ}

theorem lwMoment_expC_nonneg (k : ℕ) {c : ℝ} (hc : 0 < c) : 0 ≤ expC k c := by
  unfold expC; positivity

theorem lwMoment_Gt_true_eq (n : ℕ) (E t : ℝ) (ω : sz.SeqΩ) :
    Gt sz n E t true ω = RBM.green (sz.seqHflow n t ω) (zt E t) := by
  simp [Gt, Gres, RBM.green, Matrix.nonsing_inv_eq_ringInverse]

/-- `‖G_{xy}‖ ≤ η_t⁻¹` for every sample. -/
theorem lwMoment_norm_Gt_le {E t : ℝ} (hE : |E| < 2) (ht : t < 1) (n : ℕ) (ω : sz.SeqΩ)
    (x y : Idx d (sz.L n) (sz.W n)) : ‖Gt sz n E t true ω x y‖ ≤ (etaT E t)⁻¹ := by
  have := RBM.Green.norm_green_apply_le_etaT (sz := sz) (n := n) hE ht t x y ω
  rw [← etaT_eq_zt_im] at this
  rw [lwMoment_Gt_true_eq]
  exact this

/-- The entries of `G` on the good event: `‖G_{xy}‖ ≤ A`, `‖G_{xx} - m‖ ≤ A` for the data `D₁`. -/
theorem lwMoment_entries {n : ℕ} {E t : ℝ} {ω : sz.SeqΩ} {A : ℝ}
    (hA : ∀ x y : Idx d (sz.L n) (sz.W n), ‖STGM sz n E t ω x y‖ ≤ A) :
    (∀ x y : Idx d (sz.L n) (sz.W n), x ≠ y → ‖(lwMoment_D sz n E t ω).G x y‖ ≤ A) ∧
      ∀ x : Idx d (sz.L n) (sz.W n), ‖(lwMoment_D sz n E t ω).G x x - mE E‖ ≤ A := by
  have hG : ∀ x y : Idx d (sz.L n) (sz.W n), (lwMoment_D sz n E t ω).G x y = Gt sz n E t true ω x y :=
    fun _ _ => rfl
  refine ⟨fun x y hxy => ?_, fun x => ?_⟩
  · have := hA x y
    rw [hG]
    simpa [STGM, hxy] using this
  · have := hA x x
    rw [hG]
    simpa [STGM] using this

/-- **`claim:size` at the data `D₁` on the good event**: `‖Q.val D₁‖ ≤ C_Q · size_A(Q)` when
`‖G_t - M‖_max ≤ A`. -/
theorem lwMoment_pval_claim (S : LWMomentCtx sz κ ε 𝔡 𝔠 z t ε₀ C₁ C₂ C₃ Cc Ψ Φ) {C c : ℝ} (hC : 0 < C) (hc : 0 < c)
    {n : ℕ} (hdec : (∀ x y : Idx d (sz.L n) (sz.W n), ‖lwS sz n 1 x y‖ ≤
        C * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * Real.exp (-(c * (lwBdist d (sz.L n) (sz.W n) x y : ℝ)))) ∧
      (∀ x y : Idx d (sz.L n) (sz.W n), ‖lwSplus sz n (t n) (mE (STflowE z n)) x y‖ ≤
        C * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * Real.exp (-(c * (lwBdist d (sz.L n) (sz.W n) x y : ℝ)))))
    {ω : sz.SeqΩ} {A : ℝ} (hA : ∀ x y : Idx d (sz.L n) (sz.W n),
      ‖STGM sz n (STflowE z n) (t n) ω x y‖ ≤ A) (Q : PGraph (Fin 2)) (hQ : Q.g.Normal)
    (x y : Idx d (sz.L n) (sz.W n)) :
    ‖Q.val (lwMoment_D sz n (STflowE z n) (t n) ω) ![x, y]‖ ≤
      Q.g.sizeConst C (C * expC (d - 2) c) * Q.g.scalingSize A ((sz.W n : ℕ)) d (sz.L n) := by
  classical
  have hKS := lwKBound_of_decay S.hd hC.le hc hdec.1
  have hKSp := lwKBound_of_decay S.hd hC.le hc hdec.2
  have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA x y)
  obtain ⟨hG, hGd⟩ := lwMoment_entries (E := STflowE z n) (t := t n) hA
  by_cases hf : ∃ ℓ' : Q.E' → Idx d (sz.L n) (sz.W n), ![x, y] = ℓ' ∘ Q.ext
  · obtain ⟨ℓ', hℓ'⟩ := hf
    rw [Q.val_of_factor _ hℓ']
    exact lwClaimSize Q.g hQ (lwMoment_D sz n (STflowE z n) (t n) ω) (m := mE (STflowE z n)) (Ψ := A)
      (K₀ := C) (K₁ := C * expC (d - 2) c) (fun a b => by simp [lwMoment_D, lwSampleData, Matrix.diagonal_apply])
      hG hGd hKS hKSp ℓ'
  · rw [Q.val_of_not _ hf, norm_zero]
    refine mul_nonneg (Q.g.sizeConst_nonneg hC.le (by have := lwMoment_expC_nonneg (d - 2) hc; positivity)) ?_
    unfold LGraph.scalingSize Counters.scalingSize
    have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
    have hL : (0 : ℝ) < ((sz.L n : ℕ) : ℝ) := by exact_mod_cast (by have := sz.three_le_L n; omega : 0 < sz.L n)
    positivity

/-- **The polynomial envelope** `‖Q.val D₁‖ ≤ N^{K}`, every sample, with `K` depending on the graph only. -/
theorem lwMoment_env (S : LWMomentCtx sz κ ε 𝔡 𝔠 z t ε₀ C₁ C₂ C₃ Cc Ψ Φ) (Q : PGraph (Fin 2)) (hQ : Q.g.Normal) :
    ∃ Kenv : ℝ, ∀ᶠ n in atTop, ∀ (x y : Idx d (sz.L n) (sz.W n)) (ω : sz.SeqΩ),
      ‖Q.val (lwMoment_D sz n (STflowE z n) (t n) ω) ![x, y]‖ ≤ ((sz.size n : ℕ) : ℝ) ^ Kenv := by
  obtain ⟨hadm, hE, ht1', -⟩ := lwMoment_flow_facts S
  obtain ⟨C, c, hC, hc, hdec⟩ := lwMoment_decay S
  have hsz := lwMoment_size_tendsto S
  refine ⟨((Q.g.nM + Q.g.nV + 2 * Q.g.nS + 1 : ℕ) : ℝ), ?_⟩
  filter_upwards [hdec, lwMoment_eta_lower S, hsz.eventually_ge_atTop 2,
    hsz.eventually_ge_atTop (Q.g.sizeConst C (C * expC (d - 2) c))] with n hn hη hN2 hNc x y ω
  set N : ℝ := ((sz.size n : ℕ) : ℝ) with hN
  have hN0 : 0 < N := by linarith
  have hEn : |STflowE z n| < 2 := by linarith [hE n, S.hκ]
  have hη0 : 0 < etaT (STflowE z n) (t n) := etaT_pos hEn (ht1' n)
  have hη1 : etaT (STflowE z n) (t n) ≤ 1 := lwMoment_etaT_le_one hEn (S.t0 n) (ht1' n)
  have hηN : (etaT (STflowE z n) (t n))⁻¹ ≤ N :=
    calc (etaT (STflowE z n) (t n))⁻¹ ≤ (N ^ (-(1 : ℝ)))⁻¹ := inv_anti₀ (Real.rpow_pos_of_pos hN0 _) hη
      _ = N := by rw [Real.rpow_neg_one, inv_inv]
  have hηi : 1 ≤ (etaT (STflowE z n) (t n))⁻¹ := one_le_inv_iff₀.2 ⟨hη0, hη1⟩
  have hA : ∀ a b : Idx d (sz.L n) (sz.W n), ‖STGM sz n (STflowE z n) (t n) ω a b‖ ≤
      2 * (etaT (STflowE z n) (t n))⁻¹ := by
    intro a b
    have h1 := lwMoment_norm_Gt_le (sz := sz) hEn (ht1' n) n ω a b
    have h2 : ‖mE (STflowE z n)‖ = 1 := norm_mE hEn.le
    unfold STGM
    split_ifs
    · exact (norm_sub_le _ _).trans (by linarith)
    · rw [sub_zero]; linarith
  have h1 := lwMoment_pval_claim S hC hc hn hA Q hQ x y
  have h2 := lwMoment_scalingSize_le Q.g (Ψ := 2 * (etaT (STflowE z n) (t n))⁻¹) (B := 2 * N) (by positivity)
    (by linarith) (by linarith) (sz.W n) (sz.L n) d (sz.W_pos n) (by have := sz.three_le_L n; omega)
  have hK : 0 ≤ Q.g.sizeConst C (C * expC (d - 2) c) :=
    Q.g.sizeConst_nonneg hC.le (by have := lwMoment_expC_nonneg (d - 2) hc; positivity)
  have h3 : (2 * N) ^ Q.g.nS ≤ (N ^ 2) ^ Q.g.nS := pow_le_pow_left₀ (by positivity) (by nlinarith) _
  have e : ((((sz.W n) * (sz.L n)) ^ d : ℕ) : ℝ) = N := rfl
  rw [e] at h2
  calc ‖Q.val (lwMoment_D sz n (STflowE z n) (t n) ω) ![x, y]‖
      ≤ Q.g.sizeConst C (C * expC (d - 2) c) * (N ^ (Q.g.nM + Q.g.nV) * (N ^ 2) ^ Q.g.nS) :=
        h1.trans (mul_le_mul_of_nonneg_left (h2.trans (mul_le_mul_of_nonneg_left h3 (by positivity))) hK)
    _ ≤ N * (N ^ (Q.g.nM + Q.g.nV) * (N ^ 2) ^ Q.g.nS) :=
        mul_le_mul_of_nonneg_right hNc (by positivity)
    _ = N ^ ((Q.g.nM + Q.g.nV + 2 * Q.g.nS + 1 : ℕ) : ℝ) := by rw [Real.rpow_natCast, ← pow_mul]; ring

end Envelope

/-! ## 7. The far pairs: the entry scale `Ψ' = max(1, C₃) N^{τ₁} Φ(0)` -/

section Far

variable {sz : Sizes d} {κ ε 𝔡 𝔠 : ℝ} {z : ℕ → ℂ} {t : ℕ → ℝ} {ε₀ C₁ C₂ C₃ : ℝ} {Cc : ℝ → ℝ} {Ψ : ℕ → ℝ}
  {Φ : ℕ → ℝ → ℝ}

/-- The pin's control `(η_t⁻¹ Ψ_t(0) Ψ_t(1 · |a - b|))^p`, `c = 1`. -/
def lwMoment_R (sz : Sizes d) (E t : ℕ → ℝ) (Φ : ℕ → ℝ → ℝ) (p n : ℕ) (x y : Idx d (sz.L n) (sz.W n)) : ℝ :=
  ((etaT (E n) (t n))⁻¹ * Φ n 0 *
    Φ n (1 * ((zdistInf d (sz.L n) (STblk sz n x - STblk sz n y) : ℕ) : ℝ))) ^ p

/-- The scale `Ψ' = max(1, C₃) N^{τ₁} Φ(0)` of the entry bounds on the good event satisfies the window
`W^{-d/2} ≤ Ψ'` and `Ψ' ≤ W^{-ε₀/2}` (so `Ψ' ≤ 1`), for `τ₁ ≤ 𝔠 ε₀/4`. -/
theorem lwMoment_Psi_facts (S : LWMomentCtx sz κ ε 𝔡 𝔠 z t ε₀ C₁ C₂ C₃ Cc Ψ Φ) {τ₁ : ℝ} (hτ₁ : 0 ≤ τ₁)
    (hτ₁' : τ₁ ≤ 𝔠 * ε₀ / 4) :
    ∀ᶠ n in atTop, 0 < Φ n 0 ∧ ((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2) ≤
        max 1 C₃ * ((sz.size n : ℕ) : ℝ) ^ τ₁ * Φ n 0 ∧
      max 1 C₃ * ((sz.size n : ℕ) : ℝ) ^ τ₁ * Φ n 0 ≤ ((sz.W n : ℕ) : ℝ) ^ (-(ε₀ / 2)) := by
  obtain ⟨h𝔠, -, hsz, hband, -⟩ := (lwMoment_flow_facts S).1
  have hε₀ := S.assm.1
  have hcls := S.assm.2.2.2.1
  have hτpos : 0 < 𝔠 * ε₀ / 4 := by positivity
  filter_upwards [hcls.1, hcls.2.2, hband, hsz.eventually_ge_atTop 1,
    ((tendsto_rpow_atTop hτpos).comp hsz).eventually_ge_atTop (max 1 C₃)] with n hpos hwin hb hN1 hM
  have hW0 : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hΦ0 := (hpos 0 le_rfl).1
  have hΦε := (hpos 0 le_rfl).2
  have hM1 : 1 ≤ max 1 C₃ := le_max_left _ _
  have hNτ1 : 1 ≤ ((sz.size n : ℕ) : ℝ) ^ τ₁ := Real.one_le_rpow hN1 hτ₁
  refine ⟨hΦ0, ?_, ?_⟩
  · calc ((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2) ≤ C₃ * Φ n 0 := hwin
      _ ≤ max 1 C₃ * 1 * Φ n 0 := by
        rw [mul_one]; exact mul_le_mul_of_nonneg_right (le_max_right _ _) hΦ0.le
      _ ≤ _ := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hNτ1 (by positivity)) hΦ0.le
  · have e1 : ((sz.size n : ℕ) : ℝ) ^ τ₁ ≤ ((sz.W n : ℕ) : ℝ) ^ (ε₀ / 4) := by
      have := Real.rpow_le_rpow_of_exponent_le hN1 hτ₁'
      refine this.trans ?_
      have h2 := Sizes.size_rpow_le_W_rpow sz h𝔠 n hb (τ := 𝔠 * ε₀ / 4) hτpos.le
      have e : 𝔠 * ε₀ / 4 / 𝔠 = ε₀ / 4 := by field_simp
      rwa [e] at h2
    have e2 : max 1 C₃ ≤ ((sz.W n : ℕ) : ℝ) ^ (ε₀ / 4) := by
      refine hM.trans ?_
      have h2 := Sizes.size_rpow_le_W_rpow sz h𝔠 n hb (τ := 𝔠 * ε₀ / 4) hτpos.le
      have e : 𝔠 * ε₀ / 4 / 𝔠 = ε₀ / 4 := by field_simp
      rwa [e] at h2
    calc max 1 C₃ * ((sz.size n : ℕ) : ℝ) ^ τ₁ * Φ n 0
        ≤ ((sz.W n : ℕ) : ℝ) ^ (ε₀ / 4) * ((sz.W n : ℕ) : ℝ) ^ (ε₀ / 4) * ((sz.W n : ℕ) : ℝ) ^ (-ε₀) :=
          mul_le_mul (mul_le_mul e2 e1 (by positivity) (by positivity)) hΦε hΦ0.le (by positivity)
      _ = ((sz.W n : ℕ) : ℝ) ^ (-(ε₀ / 2)) := by
          rw [← Real.rpow_add hW0, ← Real.rpow_add hW0]; congr 1; ring

theorem lwMoment_psiAll (S : LWMomentCtx sz κ ε 𝔡 𝔠 z t ε₀ C₁ C₂ C₃ Cc Ψ Φ) :
    LWPsiAll sz ε₀ C₁ C₂ C₃ Cc Φ := ⟨S.assm.1, S.assm.2.2.2.1, S.assm.2.2.2.2.1⟩

/-- The event `‖G_t - M‖_max ≤ N^{τ₁} Φ(0)` holds w.h.p. (`(eq:Gbyxi)` entrywise, `lwEntryPsi_holds`). -/
theorem lwMoment_entry_whp (S : LWMomentCtx sz κ ε 𝔡 𝔠 z t ε₀ C₁ C₂ C₃ Cc Ψ Φ) {τ₁ : ℝ} (hτ₁ : 0 < τ₁) :
    sz.Whp (fun n => {ω | ∀ u : Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n),
      ‖STGM sz n (STflowE z n) (t n) ω u.1 u.2‖ ≤ ((sz.size n : ℕ) : ℝ) ^ τ₁ * Φ n 0}) :=
  Sizes.Prec.whp sz (RBM.Graph.lwEntryPsi_holds d S.hd κ ε 𝔡 S.hκ S.hε S.h𝔡 𝔠 sz z S.flow t S.t0 S.t1 ε₀ C₁ C₂ C₃ Cc Φ
    (lwMoment_psiAll S) S.assm.2.2.2.2.2 ε₀ S.assm.1 S.assm.2.2.1.1) hτ₁

/-- `K' W^{-D} ≤ N^{-K_f}` for `K' ≤ N`, `D ≥ (K_f + 1)/𝔠` (`W ≥ N^𝔠`). -/
theorem lwMoment_Wneg_le (S : LWMomentCtx sz κ ε 𝔡 𝔠 z t ε₀ C₁ C₂ C₃ Cc Ψ Φ) {Kf D : ℝ} (hKf : 0 ≤ Kf)
    (hD : (Kf + 1) / 𝔠 ≤ D) :
    ∀ᶠ n in atTop, ∀ K' : ℝ, K' ≤ ((sz.size n : ℕ) : ℝ) →
      K' * ((sz.W n : ℕ) : ℝ) ^ (-D) ≤ ((sz.size n : ℕ) : ℝ) ^ (-Kf) := by
  obtain ⟨h𝔠, -, hsz, hband, -⟩ := (lwMoment_flow_facts S).1
  filter_upwards [hband, hsz.eventually_ge_atTop 1] with n hb hN1
  intro K' hK'
  have hN0 : 0 < ((sz.size n : ℕ) : ℝ) := by linarith
  have hW0 : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hD0 : 0 ≤ D := le_trans (by positivity) hD
  have h1 : ((sz.W n : ℕ) : ℝ) ^ (-D) ≤ (((sz.size n : ℕ) : ℝ) ^ 𝔠) ^ (-D) :=
    Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hN0 _) hb (by linarith)
  have h2 : (((sz.size n : ℕ) : ℝ) ^ 𝔠) ^ (-D) = ((sz.size n : ℕ) : ℝ) ^ (-(𝔠 * D)) := by
    rw [← Real.rpow_mul hN0.le]; congr 1; ring
  have h3 : ((sz.size n : ℕ) : ℝ) ^ (-(𝔠 * D)) ≤ ((sz.size n : ℕ) : ℝ) ^ (-(Kf + 1)) := by
    refine Real.rpow_le_rpow_of_exponent_le hN1 ?_
    have : Kf + 1 ≤ 𝔠 * D := by rwa [div_le_iff₀ h𝔠, mul_comm] at hD
    linarith
  calc K' * ((sz.W n : ℕ) : ℝ) ^ (-D) ≤ ((sz.size n : ℕ) : ℝ) * ((sz.W n : ℕ) : ℝ) ^ (-D) :=
        mul_le_mul_of_nonneg_right hK' (Real.rpow_nonneg hW0.le _)
    _ ≤ ((sz.size n : ℕ) : ℝ) * ((sz.size n : ℕ) : ℝ) ^ (-(Kf + 1)) :=
        mul_le_mul_of_nonneg_left (h1.trans (h2.le.trans h3)) hN0.le
    _ = ((sz.size n : ℕ) : ℝ) ^ (-Kf) := by
        calc ((sz.size n : ℕ) : ℝ) * ((sz.size n : ℕ) : ℝ) ^ (-(Kf + 1))
            = ((sz.size n : ℕ) : ℝ) ^ (1 : ℝ) * ((sz.size n : ℕ) : ℝ) ^ (-(Kf + 1)) := by rw [Real.rpow_one]
          _ = ((sz.size n : ℕ) : ℝ) ^ (1 + -(Kf + 1)) := (Real.rpow_add hN0 _ _).symm
          _ = _ := by congr 1; ring

/-- `L^d ≤ W^{K0}` for `K0 ≥ 1/𝔠` (`L^d ≤ N ≤ W^{1/𝔠}`). -/
theorem lwMoment_L_le_W (S : LWMomentCtx sz κ ε 𝔡 𝔠 z t ε₀ C₁ C₂ C₃ Cc Ψ Φ) {K0 : ℕ} (hK0 : 1 / 𝔠 ≤ K0) :
    ∀ᶠ n in atTop, ((sz.L n : ℕ) : ℝ) ^ d ≤ ((sz.W n : ℕ) : ℝ) ^ K0 := by
  obtain ⟨h𝔠, -, hsz, hband, -⟩ := (lwMoment_flow_facts S).1
  filter_upwards [hband, hsz.eventually_ge_atTop 1] with n hb hN1
  have h1 : (sz.L n) ^ d ≤ sz.size n := by
    unfold Sizes.size
    exact Nat.pow_le_pow_left (Nat.le_mul_of_pos_left _ (sz.W_pos n)) d
  have h1' : ((sz.L n : ℕ) : ℝ) ^ d ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast h1
  have h2 := Sizes.size_rpow_le_W_rpow sz h𝔠 n hb (τ := 1) zero_le_one
  rw [Real.rpow_one] at h2
  have hW1 : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  calc ((sz.L n : ℕ) : ℝ) ^ d ≤ ((sz.size n : ℕ) : ℝ) := h1'
    _ ≤ ((sz.W n : ℕ) : ℝ) ^ (1 / 𝔠) := by simpa using h2
    _ ≤ ((sz.W n : ℕ) : ℝ) ^ (K0 : ℝ) := Real.rpow_le_rpow_of_exponent_le hW1 hK0
    _ = _ := Real.rpow_natCast _ _

/-- **errs** (and any output with a `W^{-D}` size bound): the size bound at the entry scale `Ψ'` gives `≤ N^{-K_f} ≤ R`. -/
theorem lwMoment_prec_err (S : LWMomentCtx sz κ ε 𝔡 𝔠 z t ε₀ C₁ C₂ C₃ Cc Ψ Φ) (p : ℕ) {K0 : ℕ} {D : ℝ}
    (hK0 : 1 / 𝔠 ≤ K0) (hD : ((p : ℝ) * (2 + C₂) + 1) / 𝔠 ≤ D) {V : ℕ → Type}
    (pr : ∀ n, V n → Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n)) {Q : PGraph (Fin 2)}
    (hQ : Q.g.Normal)
    (herr : ∀ (W L : ℕ) (Ψ : ℝ), 1 ≤ W → 1 ≤ L → (L : ℝ) ^ d ≤ (W : ℝ) ^ K0 →
      (W : ℝ) ^ (-(d : ℝ) / 2) ≤ Ψ → Ψ ≤ (W : ℝ) ^ (-(ε₀ / 2)) → Q.g.scalingSize Ψ W d L ≤ (W : ℝ) ^ (-D)) :
    sz.Prec (U := V) (fun n v ω => ‖Q.val (lwMoment_D sz n (STflowE z n) (t n) ω) ![(pr n v).1, (pr n v).2]‖)
      (fun n v _ => lwMoment_R sz (STflowE z) t Φ p n (pr n v).1 (pr n v).2) := by
  have hε₀ := S.assm.1
  have hsz := lwMoment_size_tendsto S
  have h𝔠 := (lwMoment_flow_facts S).1.1
  apply lwMoment_prec_of_whp
  intro τ hτ
  refine ⟨_, lwMoment_entry_whp S (τ₁ := 𝔠 * ε₀ / 4) (by positivity), ?_⟩
  obtain ⟨C, c, hC, hc, hdec⟩ := lwMoment_decay S
  have hKf : 0 ≤ (p : ℝ) * (2 + C₂) := by
    have := S.assm.2.2.2.2.1.2.2.1; positivity
  filter_upwards [hdec, lwMoment_Psi_facts S (τ₁ := 𝔠 * ε₀ / 4) (by positivity) le_rfl,
    lwMoment_floor S p, lwMoment_Wneg_le S hKf hD, lwMoment_L_le_W S hK0,
    hsz.eventually_ge_atTop 1, hsz.eventually_ge_atTop (Q.g.sizeConst C (C * expC (d - 2) c))]
    with n hdn hPsi hfl hWn hLW hN1 hNc
  intro ω hω v
  obtain ⟨hΦ0, hwin, hup⟩ := hPsi
  have hM1 : 1 ≤ max 1 C₃ := le_max_left _ _
  have hNτ : 1 ≤ ((sz.size n : ℕ) : ℝ) ^ τ := Real.one_le_rpow hN1 hτ.le
  have hA : ∀ a b : Idx d (sz.L n) (sz.W n), ‖STGM sz n (STflowE z n) (t n) ω a b‖ ≤
      max 1 C₃ * ((sz.size n : ℕ) : ℝ) ^ (𝔠 * ε₀ / 4) * Φ n 0 := by
    intro a b
    refine (hω (a, b)).trans ?_
    have h1 : 1 ≤ ((sz.size n : ℕ) : ℝ) ^ (𝔠 * ε₀ / 4) := Real.one_le_rpow hN1 (by positivity)
    have h2 : 0 ≤ ((sz.size n : ℕ) : ℝ) ^ (𝔠 * ε₀ / 4) * Φ n 0 := by positivity
    nlinarith
  have h1 := lwMoment_pval_claim S hC hc hdn hA Q hQ (pr n v).1 (pr n v).2
  have h2 := herr (sz.W n) (sz.L n) _ (sz.W_pos n) (by have := sz.three_le_L n; omega) hLW hwin hup
  have hK0 : 0 ≤ Q.g.sizeConst C (C * expC (d - 2) c) :=
    Q.g.sizeConst_nonneg hC.le (by have := lwMoment_expC_nonneg (d - 2) hc; positivity)
  have h3 := h1.trans (mul_le_mul_of_nonneg_left h2 hK0)
  have h4 := hWn _ hNc
  have h5 := hfl (pr n v).1 (pr n v).2
  have hR0 : 0 ≤ lwMoment_R sz (STflowE z) t Φ p n (pr n v).1 (pr n v).2 :=
    (Real.rpow_nonneg (by positivity) _).trans h5
  calc _ ≤ _ := h3.trans h4
    _ ≤ lwMoment_R sz (STflowE z) t Φ p n (pr n v).1 (pr n v).2 := h5
    _ ≤ ((sz.size n : ℕ) : ℝ) ^ τ * lwMoment_R sz (STflowE z) t Φ p n (pr n v).1 (pr n v).2 :=
        le_mul_of_one_le_left hR0 hNτ

/-- The tail of `scalemole`/`GtoAG`: `e^{-c r/2} K₂ size_{Ψ'}(Γ) ≤ N^{-b}` for `Ψ' ≤ 1`, `K₂ ≤ N`, when
`e^{-c r/2} N^{n_M + n_V + 1} ≤ N^{-b}`. -/
theorem lwMoment_tail_le {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I] (Γ : LGraph E I)
    {Ψ' c r K2 b : ℝ} (W L d : ℕ) (hW : 1 ≤ W) (hL : 1 ≤ L) (hΨ0 : 0 < Ψ') (hΨ1 : Ψ' ≤ 1)
    (hK2 : K2 ≤ (((W * L) ^ d : ℕ) : ℝ)) (hK20 : 0 ≤ K2)
    (htail : Real.exp (-(c * r / 2)) * (((W * L) ^ d : ℕ) : ℝ) ^ ((Γ.nM + Γ.nV + 1 : ℕ) : ℝ) ≤
      (((W * L) ^ d : ℕ) : ℝ) ^ (-b)) :
    Real.exp (-(c * r / 2)) * K2 * Γ.scalingSize Ψ' W d L ≤ (((W * L) ^ d : ℕ) : ℝ) ^ (-b) := by
  have hss := lwMoment_scalingSize_le Γ hΨ0 hΨ1 le_rfl W L d hW hL
  rw [one_pow, mul_one] at hss
  have hscal0 : 0 ≤ Γ.scalingSize Ψ' W d L := by
    unfold LGraph.scalingSize Counters.scalingSize
    have hL' : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL
    have hW' : (0 : ℝ) < (W : ℝ) := by exact_mod_cast hW
    positivity
  have hex := Real.exp_pos (-(c * r / 2))
  have hN0 : (0 : ℝ) ≤ (((W * L) ^ d : ℕ) : ℝ) := Nat.cast_nonneg _
  refine le_trans ?_ htail
  calc Real.exp (-(c * r / 2)) * K2 * Γ.scalingSize Ψ' W d L
      ≤ Real.exp (-(c * r / 2)) * (((W * L) ^ d : ℕ) : ℝ) * ((((W * L) ^ d : ℕ) : ℝ) ^ (Γ.nM + Γ.nV)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hK2 hex.le) hss hscal0 (by positivity)
    _ = _ := by rw [Real.rpow_natCast, pow_succ]; ring

theorem lwMoment_auxVal_smul {κ : Type} [Fintype κ] {E I : Type} [Fintype E] [DecidableEq E] [Fintype I]
    [DecidableEq I] (Γ : LGraph E I) (ξ : κ → κ → ℝ) (s : ℝ)
    (be : E → κ) : Γ.auxVal (fun a b => s * ξ a b) be = s ^ Γ.molSolid.length * Γ.auxVal ξ be := by
  have key : ∀ {α : Type} (l : List α) (f : α → ℝ),
      (l.map fun e => s * f e).prod = s ^ l.length * (l.map f).prod := by
    intro α l f
    induction l with
    | nil => simp
    | cons a l ih => simp only [List.map_cons, List.prod_cons, ih, List.length_cons, pow_succ]; ring
  unfold LGraph.auxVal
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp only [List.map_map, Function.comp_def]
  exact key _ _

theorem lwMoment_ext_mol {Q : PGraph (Fin 2)}
    (hxy : Q.g.molOf (Sum.inl (Q.ext 0)) ≠ Q.g.molOf (Sum.inl (Q.ext 1))) :
    ∀ a b : Q.E', Q.g.molOf (Sum.inl a) = Q.g.molOf (Sum.inl b) → a = b := by
  intro a b hab
  obtain ⟨i, rfl⟩ := Q.ext_surj a
  obtain ⟨j, rfl⟩ := Q.ext_surj b
  fin_cases i <;> fin_cases j
  · rfl
  · exact absurd hab hxy
  · exact absurd hab.symm hxy
  · rfl

/-- **Outputs with `𝓜_x = 𝓜_y` at far pairs** (`(eq:far_ab)`, `7_8:955-958`; `lwScalemole_holds`): the value is at most
the tail `e^{-c r/2} C' size(Γ)` with `r = (log W)²`, which is `≤ N^{-K_f} ≤ R`. -/
theorem lwMoment_prec_scale (S : LWMomentCtx sz κ ε 𝔡 𝔠 z t ε₀ C₁ C₂ C₃ Cc Ψ Φ) (p : ℕ) {V : ℕ → Type}
    (pr : ∀ n, V n → Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n)) {Q : PGraph (Fin 2)}
    (hQ : Q.g.Normal) (hmol : Q.g.molOf (Sum.inl (Q.ext 0)) = Q.g.molOf (Sum.inl (Q.ext 1))) {K : ℕ}
    (hK : Fintype.card (Q.E' ⊕ Q.I') ≤ K)
    (hfar : ∀ n v, (K : ℝ) * Real.log ((sz.W n : ℕ) : ℝ) ^ 2 <
      (lwBdist d (sz.L n) (sz.W n) (pr n v).1 (pr n v).2 : ℝ)) :
    sz.Prec (U := V) (fun n v ω => ‖Q.val (lwMoment_D sz n (STflowE z n) (t n) ω) ![(pr n v).1, (pr n v).2]‖)
      (fun n v _ => lwMoment_R sz (STflowE z) t Φ p n (pr n v).1 (pr n v).2) := by
  classical
  have hε₀ := S.assm.1
  have hsz := lwMoment_size_tendsto S
  have h𝔠 := (lwMoment_flow_facts S).1.1
  apply lwMoment_prec_of_whp
  intro τ hτ
  refine ⟨_, lwMoment_entry_whp S (τ₁ := 𝔠 * ε₀ / 4) (by positivity), ?_⟩
  obtain ⟨C, c, hC, hc, hdec⟩ := lwMoment_decay S
  have hKf : 0 ≤ (p : ℝ) * (2 + C₂) := by
    have := S.assm.2.2.2.2.1.2.2.1; positivity
  have hE : ∀ n, |STflowE z n| < 2 := fun n => by linarith [(lwMoment_flow_facts S).2.1 n, S.hκ]
  filter_upwards [hdec, lwMoment_Psi_facts S (τ₁ := 𝔠 * ε₀ / 4) (by positivity) le_rfl,
    lwMoment_floor S p, lwMoment_tail S hc ((Q.g.nM + Q.g.nV + 1 : ℕ) : ℝ) ((p : ℝ) * (2 + C₂)),
    hsz.eventually_ge_atTop 1,
    hsz.eventually_ge_atTop (Q.g.sizeConst C (C * expC (d - 2) (c / 2)))]
    with n hdn hPsi hfl htail hN1 hNc
  intro ω hω v
  obtain ⟨hΦ0, hwin, hup⟩ := hPsi
  have hM1 : 1 ≤ max 1 C₃ := le_max_left _ _
  have hNτ : 1 ≤ ((sz.size n : ℕ) : ℝ) ^ τ := Real.one_le_rpow hN1 hτ.le
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
  have hW1 : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hA : ∀ a b : Idx d (sz.L n) (sz.W n), ‖STGM sz n (STflowE z n) (t n) ω a b‖ ≤
      max 1 C₃ * ((sz.size n : ℕ) : ℝ) ^ (𝔠 * ε₀ / 4) * Φ n 0 := by
    intro a b
    refine (hω (a, b)).trans ?_
    have h1 : 1 ≤ ((sz.size n : ℕ) : ℝ) ^ (𝔠 * ε₀ / 4) := Real.one_le_rpow hN1 (by positivity)
    have h2 : 0 ≤ ((sz.size n : ℕ) : ℝ) ^ (𝔠 * ε₀ / 4) * Φ n 0 := by positivity
    nlinarith
  have h5 := hfl (pr n v).1 (pr n v).2
  have hR0 : 0 ≤ lwMoment_R sz (STflowE z) t Φ p n (pr n v).1 (pr n v).2 :=
    (Real.rpow_nonneg (by positivity) _).trans h5
  have hfin : ∀ u : ℝ, u ≤ ((sz.size n : ℕ) : ℝ) ^ (-((p : ℝ) * (2 + C₂))) →
      u ≤ ((sz.size n : ℕ) : ℝ) ^ τ * lwMoment_R sz (STflowE z) t Φ p n (pr n v).1 (pr n v).2 :=
    fun u hu => hu.trans (h5.trans (le_mul_of_one_le_left hR0 hNτ))
  refine hfin _ ?_
  by_cases hf : ∃ ℓ' : Q.E' → Idx d (sz.L n) (sz.W n), ![(pr n v).1, (pr n v).2] = ℓ' ∘ Q.ext
  · obtain ⟨ℓ', hℓ'⟩ := hf
    rw [Q.val_of_factor _ hℓ']
    have e0 : ℓ' (Q.ext 0) = (pr n v).1 := (congrFun hℓ' 0).symm
    have e1 : ℓ' (Q.ext 1) = (pr n v).2 := (congrFun hℓ' 1).symm
    have hr0 : 0 ≤ Real.log ((sz.W n : ℕ) : ℝ) ^ 2 := by positivity
    have hfar' : (Fintype.card (Q.E' ⊕ Q.I') : ℝ) * Real.log ((sz.W n : ℕ) : ℝ) ^ 2 <
        (lwBdist d (sz.L n) (sz.W n) (ℓ' (Q.ext 0)) (ℓ' (Q.ext 1)) : ℝ) := by
      rw [e0, e1]
      exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right (Nat.cast_le.2 hK) hr0) (hfar n v)
    obtain ⟨hG, hGd⟩ := lwMoment_entries (E := STflowE z n) (t := t n) hA
    have hsc := lwScalemole_holds d S.hd (sz.L n) (sz.W n) Q.g hQ (lwMoment_D sz n (STflowE z n) (t n) ω)
      (mE (STflowE z n)) (max 1 C₃ * ((sz.size n : ℕ) : ℝ) ^ (𝔠 * ε₀ / 4) * Φ n 0) C c
      (Real.log ((sz.W n : ℕ) : ℝ) ^ 2) (fun a b => by simp [lwMoment_D, lwSampleData, Matrix.diagonal_apply])
      hG hGd hC.le hc hdn.1 hdn.2 hr0 ℓ' (Q.ext 0) (Q.ext 1) hmol hfar'
    have hΨ0 : 0 < max 1 C₃ * ((sz.size n : ℕ) : ℝ) ^ (𝔠 * ε₀ / 4) * Φ n 0 := by
      have : 0 < max 1 C₃ := lt_of_lt_of_le one_pos hM1
      positivity
    have hΨ1 : max 1 C₃ * ((sz.size n : ℕ) : ℝ) ^ (𝔠 * ε₀ / 4) * Φ n 0 ≤ 1 :=
      hup.trans (Real.rpow_le_one_of_one_le_of_nonpos hW1 (by linarith))
    have hK2 : 0 ≤ Q.g.sizeConst C (C * expC (d - 2) (c / 2)) :=
      Q.g.sizeConst_nonneg hC.le (by have := lwMoment_expC_nonneg (d - 2) (half_pos hc); positivity)
    exact hsc.trans (lwMoment_tail_le Q.g (sz.W n) (sz.L n) d (sz.W_pos n)
      (by have := sz.three_le_L n; omega) hΨ0 hΨ1 hNc hK2 htail)
  · rw [Q.val_of_not _ hf, norm_zero]
    exact Real.rpow_nonneg hN0.le _

/-- The exponent arithmetic of the `𝓜_x ≠ 𝓜_y` outputs (rows 7-9 of the preflight): `η^{-n_M} Φ(0)^{ord-p} ≤ η^{-p} Φ(0)^p`
for `n_M ≤ p`, `ord ≥ 2p`, `η ≤ 1`, `Φ(0) ≤ 1`, and the `N^{τ₁}` losses collected in `X^{e₁+k+1}`. -/
theorem lwMoment_anp_arith {X M f0 η w Pc Φs K1 KG : ℝ} {nM p e1 k : ℕ} {ao o : ℤ}
    (hX : 1 ≤ X) (hM : 1 ≤ M) (hf0 : 0 < f0) (hf1 : f0 ≤ 1) (hη0 : 0 < η) (hη1 : η ≤ 1)
    (hw : 0 < w) (hPc : 0 ≤ Pc) (hΦs : 0 ≤ Φs) (hPcK : Pc ≤ KG * Φs) (hK1 : 0 ≤ K1) (hKG : 0 ≤ KG)
    (hnM : nM ≤ p) (hord : 2 * (p : ℤ) ≤ o) (ho : o = (e1 : ℤ) + ao) :
    K1 * (M * X * f0) ^ (e1 : ℤ) * (w ^ nM * (X ^ k * (X * ((w * η)⁻¹ ^ nM * Pc ^ p * f0 ^ (ao - p))))) ≤
      X ^ (e1 + k + 1) * (K1 * M ^ e1 * KG ^ p) * (η⁻¹ * f0 * Φs) ^ p := by
  have hX0 : 0 < X := by linarith
  have hηi : 1 ≤ η⁻¹ := one_le_inv_iff₀.2 ⟨hη0, hη1⟩
  have hwη : w ^ nM * (w * η)⁻¹ ^ nM = (η⁻¹) ^ nM := by
    rw [← mul_pow, mul_inv, ← mul_assoc, mul_inv_cancel₀ hw.ne', one_mul]
  have hfz : f0 ^ (e1 : ℤ) * f0 ^ (ao - p) = f0 ^ (o - p) := by
    rw [← zpow_add₀ hf0.ne']; congr 1; omega
  have hf2 : f0 ^ (o - p) ≤ f0 ^ (p : ℤ) :=
    zpow_le_zpow_right_of_le_one₀ hf0 hf1 (by omega)
  have hη2 : (η⁻¹) ^ nM ≤ (η⁻¹) ^ p := pow_le_pow_right₀ hηi hnM
  have hP : Pc ^ p ≤ (KG * Φs) ^ p := pow_le_pow_left₀ hPc hPcK p
  have e1' : (M * X * f0) ^ (e1 : ℤ) = M ^ e1 * X ^ e1 * f0 ^ (e1 : ℤ) := by
    rw [zpow_natCast, mul_pow, mul_pow, zpow_natCast]
  have hL : K1 * (M * X * f0) ^ (e1 : ℤ) * (w ^ nM * (X ^ k * (X * ((w * η)⁻¹ ^ nM * Pc ^ p * f0 ^ (ao - p))))) =
      (K1 * M ^ e1 * X ^ (e1 + k + 1)) * ((η⁻¹) ^ nM * f0 ^ (o - p) * Pc ^ p) := by
    rw [e1', ← hwη, ← hfz]; ring
  rw [hL]
  have hpf : (η⁻¹ * f0 * Φs) ^ p = (η⁻¹) ^ p * f0 ^ (p : ℤ) * Φs ^ p := by
    rw [zpow_natCast, mul_pow, mul_pow]
  have hKM : 0 ≤ K1 * M ^ e1 * X ^ (e1 + k + 1) := by positivity
  calc (K1 * M ^ e1 * X ^ (e1 + k + 1)) * ((η⁻¹) ^ nM * f0 ^ (o - p) * Pc ^ p)
      ≤ (K1 * M ^ e1 * X ^ (e1 + k + 1)) * ((η⁻¹) ^ p * f0 ^ (p : ℤ) * (KG * Φs) ^ p) := by
        refine mul_le_mul_of_nonneg_left ?_ hKM
        refine mul_le_mul (mul_le_mul hη2 hf2 (zpow_nonneg hf0.le _) (by positivity)) hP (by positivity)
          (by positivity)
    _ = X ^ (e1 + k + 1) * (K1 * M ^ e1 * KG ^ p) * (η⁻¹ * f0 * Φs) ^ p := by
        rw [hpf, mul_pow]; ring

/-- **Outputs with `𝓜_x ≠ 𝓜_y`** (`7_8:907-950`): `GtoAG` (`lwGtoAG_holds`) against the edge variables `N^{τ₁} ξ`,
the nested form of `Γ^{aux}` (`lwAuxNested_holds`) and `lem:Anp` (`lwAnp_holds`), `n_M ≤ p`, `ord ≥ 2p`, and `Φ(c r) ≲ Φ(r)`
(`(eq:Psi)`); the tail is `≤ N^{-K_f} ≤ R`. -/
theorem lwMoment_prec_anp (S : LWMomentCtx sz κ ε 𝔡 𝔠 z t ε₀ C₁ C₂ C₃ Cc Ψ Φ) {p : ℕ} (hp : 0 < p) {V : ℕ → Type}
    (pr : ∀ n, V n → Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n)) {Q : PGraph (Fin 2)}
    (hQ : Q.g.Normal) (h345 : Q.LocReg345 p)
    (hxy : Q.g.molOf (Sum.inl (Q.ext 0)) ≠ Q.g.molOf (Sum.inl (Q.ext 1))) (hnM : Q.g.nM ≤ p)
    (hord : (2 * p : ℤ) ≤ Q.g.scalingOrder) {K : ℕ} (hK : Fintype.card (Q.E' ⊕ Q.I') ≤ K) :
    sz.Prec (U := V) (fun n v ω => ‖Q.val (lwMoment_D sz n (STflowE z n) (t n) ω) ![(pr n v).1, (pr n v).2]‖)
      (fun n v _ => lwMoment_R sz (STflowE z) t Φ p n (pr n v).1 (pr n v).2) := by
  classical
  have hε₀ := S.assm.1
  have hsz := lwMoment_size_tendsto S
  have h𝔠 := (lwMoment_flow_facts S).1.1
  have hcls := S.assm.2.2.2.1
  obtain ⟨Γa, hnog, hnest, hordN, hval⟩ := lwAuxNested_holds p Q hp h345 hxy
  obtain ⟨cG, hcG, hAnp⟩ := lwAnp_holds d S.hd κ ε 𝔡 S.hκ S.hε S.h𝔡 p Q.g.nM hnM Γa hnog hnest ε₀ C₁ C₂ C₃ Cc
  let Rb : ℕ → ℝ := fun n => (K : ℝ) * Real.log ((sz.W n : ℕ) : ℝ) ^ 2
  let ρ : ℕ → ℝ := fun n => 2 * Rb n + 1
  have hRb0 : ∀ n, 0 ≤ Rb n := fun n => by positivity
  have hρ0 : ∀ n, 0 ≤ ρ n := fun n => by have := hRb0 n; simp only [ρ]; linarith
  have hρrad : ∀ τ : ℝ, 0 < τ → ∀ᶠ n in atTop, ρ n + 1 ≤ ((sz.size n : ℕ) : ℝ) ^ τ := by
    intro τ hτ
    filter_upwards [lwXiRad_holds sz hsz (2 * (K : ℝ)) 1 2 (by positivity) zero_le_one zero_le_two τ hτ] with n hn
    simp only [ρ, Rb]; rw [Real.rpow_two] at hn; linarith
  have hξ := lwXiClaim_holds d S.hd κ ε 𝔡 S.hκ S.hε S.h𝔡 𝔠 sz z S.flow t S.t0 S.t1 ε₀ C₁ C₂ C₃ Cc Φ
    (lwMoment_psiAll S) S.assm.2.2.2.2.2 ε₀ S.assm.1 S.assm.2.2.1.1 ρ hρ0 hρrad
  have hA3 := hAnp 𝔠 sz z S.flow t S.t0 S.t1 Φ (lwMoment_psiAll S) _ hξ
  have hE2 := lwGbyXi_holds d S.hd κ ε 𝔡 S.hκ S.hε S.h𝔡 𝔠 sz z S.flow t S.t0 S.t1 ε₀ S.assm.1
    S.assm.2.2.1.1 ρ Rb hRb0 (fun n => le_rfl)
  obtain ⟨C, c, hC, hc, hdec⟩ := lwMoment_decay S
  have hKf : 0 ≤ (p : ℝ) * (2 + C₂) := by
    have := S.assm.2.2.2.2.1.2.2.1; positivity
  -- the exponents
  have hAe : ((Q.g.scalingOrder - LGraph.auxOrd Q.g).toNat : ℤ) = Q.g.scalingOrder - LGraph.auxOrd Q.g :=
    Int.toNat_of_nonneg (sub_nonneg.2 (Q.g.auxOrd_le_scalingOrder hQ))
  set e1 : ℕ := (Q.g.scalingOrder - LGraph.auxOrd Q.g).toNat with he1
  set k : ℕ := Q.g.molSolid.length with hk
  set A : ℕ := e1 + k + 1 with hAdef
  have hA1 : (1 : ℝ) ≤ A := by
    rw [hAdef]; push_cast; linarith [Nat.cast_nonneg (α := ℝ) e1, Nat.cast_nonneg (α := ℝ) k]
  have hApos : (0 : ℝ) < A := by linarith
  set cG' : ℝ := min cG 1 with hcG'
  have hcG'0 : 0 < cG' := lt_min hcG one_pos
  have hcG'1 : cG' ≤ 1 := min_le_right _ _
  set M : ℝ := max 1 C₃ with hMdef
  have hM1 : 1 ≤ M := le_max_left _ _
  set KG : ℝ := max 1 (Cc 2) * C₁ * (cG'⁻¹) ^ C₂ with hKG
  set K1 : ℝ := Q.g.sizeConst C (C * expC (d - 2) c) with hK1
  set K2 : ℝ := Q.g.sizeConst C (C * expC (d - 2) (c / 2)) with hK2
  have hK10 : 0 ≤ K1 := Q.g.sizeConst_nonneg hC.le (by have := lwMoment_expC_nonneg (d - 2) hc; positivity)
  have hK20 : 0 ≤ K2 :=
    Q.g.sizeConst_nonneg hC.le (by have := lwMoment_expC_nonneg (d - 2) (half_pos hc); positivity)
  have hC₁ : 1 < C₁ := S.assm.2.2.2.2.1.2.1
  have hC₂ : 1 < C₂ := S.assm.2.2.2.2.1.2.2.1
  have hKG0 : 0 ≤ KG := by
    have : 0 < max 1 (Cc 2) := lt_of_lt_of_le one_pos (le_max_left _ _)
    rw [hKG]; positivity
  set Kbig : ℝ := K1 * M ^ e1 * KG ^ p with hKbig
  apply lwMoment_prec_of_whp
  intro τ hτ
  set τ₁ : ℝ := min (τ / (2 * A)) (𝔠 * ε₀ / 4) with hτ₁def
  have hτ₁ : 0 < τ₁ := lt_min (by positivity) (by positivity)
  refine ⟨_, HighProbAt.inter (Sizes.tendsto_size sz hsz) (HighProbAt.inter (Sizes.tendsto_size sz hsz) (lwMoment_entry_whp S hτ₁)
    (Sizes.Prec.whp sz hE2 hτ₁)) (Sizes.Prec.whp sz hA3 hτ₁), ?_⟩
  have hE : ∀ n, |STflowE z n| < 2 := fun n => by linarith [(lwMoment_flow_facts S).2.1 n, S.hκ]
  filter_upwards [hdec, lwMoment_Psi_facts S hτ₁.le (min_le_right _ _),
    lwMoment_phi_facts hcls S.assm.2.2.2.2.1, lwMoment_floor S p,
    lwMoment_tail S hc ((Q.g.nM + Q.g.nV + 1 : ℕ) : ℝ) ((p : ℝ) * (2 + C₂)), hsz.eventually_ge_atTop 1,
    hsz.eventually_ge_atTop K2,
    ((tendsto_rpow_atTop (half_pos hτ)).comp hsz).eventually_ge_atTop (Kbig + 1)]
    with n hdn hPsi hph hfl htail hN1 hNc hNb
  intro ω hω v
  obtain ⟨⟨hω1, hω2⟩, hω3⟩ := hω
  obtain ⟨hΦ0, hwin, hup⟩ := hPsi
  obtain ⟨hCc, hP, hcmp, hcGf⟩ := hph
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
  have hX1 : 1 ≤ ((sz.size n : ℕ) : ℝ) ^ τ₁ := Real.one_le_rpow hN1 hτ₁.le
  have hX0 : 0 ≤ ((sz.size n : ℕ) : ℝ) ^ τ₁ := by linarith
  have hW1 : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hEn := hE n
  have hη0 : 0 < etaT (STflowE z n) (t n) := etaT_pos hEn ((lwMoment_flow_facts S).2.2.1 n)
  have hη1 : etaT (STflowE z n) (t n) ≤ 1 :=
    lwMoment_etaT_le_one hEn (S.t0 n) ((lwMoment_flow_facts S).2.2.1 n)
  have hΨ0 : 0 < M * ((sz.size n : ℕ) : ℝ) ^ τ₁ * Φ n 0 := by positivity
  have hΨ1 : M * ((sz.size n : ℕ) : ℝ) ^ τ₁ * Φ n 0 ≤ 1 :=
    hup.trans (Real.rpow_le_one_of_one_le_of_nonpos hW1 (by linarith))
  have hMX : 1 ≤ M * ((sz.size n : ℕ) : ℝ) ^ τ₁ := by nlinarith
  have hf1 : Φ n 0 ≤ 1 := by
    refine le_trans ?_ hΨ1
    calc Φ n 0 = 1 * Φ n 0 := (one_mul _).symm
      _ ≤ M * ((sz.size n : ℕ) : ℝ) ^ τ₁ * Φ n 0 := mul_le_mul_of_nonneg_right hMX hΦ0.le
  have hRf := hfl (pr n v).1 (pr n v).2
  have hR0 : 0 ≤ lwMoment_R sz (STflowE z) t Φ p n (pr n v).1 (pr n v).2 :=
    (Real.rpow_nonneg hN0.le _).trans hRf
  have hNτ : 1 ≤ ((sz.size n : ℕ) : ℝ) ^ τ := Real.one_le_rpow hN1 hτ.le
  -- `X^A ≤ N^{τ/2}`, `(X^A K + 1) ≤ N^τ`
  have hXA : (((sz.size n : ℕ) : ℝ) ^ τ₁) ^ A ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]
    refine Real.rpow_le_rpow_of_exponent_le hN1 ?_
    have : τ₁ ≤ τ / (2 * A) := min_le_left _ _
    calc τ₁ * (A : ℝ) ≤ τ / (2 * A) * A := mul_le_mul_of_nonneg_right this hApos.le
      _ = τ / 2 := by field_simp
  have hfinal : (((sz.size n : ℕ) : ℝ) ^ τ₁) ^ A * Kbig + 1 ≤ ((sz.size n : ℕ) : ℝ) ^ τ := by
    have hh : ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * ((sz.size n : ℕ) : ℝ) ^ (τ / 2) = ((sz.size n : ℕ) : ℝ) ^ τ := by
      rw [← Real.rpow_add hN0]; congr 1; ring
    have h1 : 1 ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) := Real.one_le_rpow hN1 (half_pos hτ).le
    have hKb : 0 ≤ Kbig := by rw [hKbig]; positivity
    calc (((sz.size n : ℕ) : ℝ) ^ τ₁) ^ A * Kbig + 1
        ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * Kbig + ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * 1 := by
          rw [mul_one]; exact add_le_add (mul_le_mul_of_nonneg_right hXA hKb) h1
      _ = ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * (Kbig + 1) := by ring
      _ ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * ((sz.size n : ℕ) : ℝ) ^ (τ / 2) :=
          mul_le_mul_of_nonneg_left hNb (by positivity)
      _ = _ := hh
  suffices h : ‖Q.val (lwMoment_D sz n (STflowE z n) (t n) ω) ![(pr n v).1, (pr n v).2]‖ ≤
      ((((sz.size n : ℕ) : ℝ) ^ τ₁) ^ A * Kbig + 1) * lwMoment_R sz (STflowE z) t Φ p n (pr n v).1 (pr n v).2 by
    exact h.trans (mul_le_mul_of_nonneg_right hfinal hR0)
  by_cases hf : ∃ ℓ' : Q.E' → Idx d (sz.L n) (sz.W n), ![(pr n v).1, (pr n v).2] = ℓ' ∘ Q.ext
  · obtain ⟨ℓ', hℓ'⟩ := hf
    rw [Q.val_of_factor _ hℓ']
    have e0 : ℓ' (Q.ext 0) = (pr n v).1 := (congrFun hℓ' 0).symm
    have e1' : ℓ' (Q.ext 1) = (pr n v).2 := (congrFun hℓ' 1).symm
    have hr0 : 0 ≤ Real.log ((sz.W n : ℕ) : ℝ) ^ 2 := by positivity
    have hA : ∀ a b : Idx d (sz.L n) (sz.W n), ‖STGM sz n (STflowE z n) (t n) ω a b‖ ≤
        M * ((sz.size n : ℕ) : ℝ) ^ τ₁ * Φ n 0 := by
      intro a b
      refine (hω1 (a, b)).trans ?_
      calc ((sz.size n : ℕ) : ℝ) ^ τ₁ * Φ n 0 = 1 * (((sz.size n : ℕ) : ℝ) ^ τ₁ * Φ n 0) := (one_mul _).symm
        _ ≤ M * (((sz.size n : ℕ) : ℝ) ^ τ₁ * Φ n 0) := mul_le_mul_of_nonneg_right hM1 (by positivity)
        _ = _ := by ring
    obtain ⟨hG, hGd⟩ := lwMoment_entries (E := STflowE z n) (t := t n) hA
    obtain ⟨hξ0, hξG⟩ := lwGbyXi_hxi sz (STflowE z) t ρ Rb n (Matrix.diagonal fun _ => mE (STflowE z n))
      (lwS sz n 1) (lwSplus sz n (t n) (mE (STflowE z n))) ω hX0
      (fun a b a' b' hab h1 h2 => hω2 ⟨((a, b), (a', b')), hab, h1, h2⟩)
    have hgt := lwGtoAG_holds d S.hd (sz.L n) (sz.W n) Q.g hQ (lwMoment_ext_mol hxy)
      (lwMoment_D sz n (STflowE z n) (t n) ω) (mE (STflowE z n)) (M * ((sz.size n : ℕ) : ℝ) ^ τ₁ * Φ n 0) C c
      (Real.log ((sz.W n : ℕ) : ℝ) ^ 2) (Rb n)
      (fun a b => ((sz.size n : ℕ) : ℝ) ^ τ₁ * lwXiVar sz (STflowE z) t ρ n a b ω)
      (fun a b => by simp [lwMoment_D, lwSampleData, Matrix.diagonal_apply]) hG hGd hC.le hc hdn.1 hdn.2 hwin
      hr0 (mul_le_mul_of_nonneg_right (Nat.cast_le.2 hK) hr0) hξ0 hξG ℓ'
    have hsymm : ∀ a b, lwXiVar sz (STflowE z) t ρ n a b ω = lwXiVar sz (STflowE z) t ρ n b a ω :=
      fun a b => (hξ.1 n a b ω).2
    have hav : LGraph.auxVal Q.g (fun a b => ((sz.size n : ℕ) : ℝ) ^ τ₁ * lwXiVar sz (STflowE z) t ρ n a b ω)
        (fun a => (split d (sz.L n) (sz.W n) (ℓ' a)).1) =
        (((sz.size n : ℕ) : ℝ) ^ τ₁) ^ k * Γa.val (fun α β => lwXiVar sz (STflowE z) t ρ n α β ω)
          (fun _ => STblk sz n (pr n v).1) (fun _ => STblk sz n (pr n v).2) := by
      rw [lwMoment_auxVal_smul]
      congr 1
      rw [← hval (fun α β => lwXiVar sz (STflowE z) t ρ n α β ω) hsymm
        (fun a => (split d (sz.L n) (sz.W n) (ℓ' a)).1), e0, e1']
      rfl
    have h3 := hω3 (STblk sz n (pr n v).1, STblk sz n (pr n v).2)
    have hs0 : (0 : ℝ) ≤ 1 * ((zdistInf d (sz.L n) (STblk sz n (pr n v).1 - STblk sz n (pr n v).2) : ℕ) : ℝ) := by
      positivity
    -- `Φ(c_G s) ≤ K_G Φ(s)`
    have hPcK : Φ n (cG * ((zdistInf d (sz.L n) (STblk sz n (pr n v).1 - STblk sz n (pr n v).2) : ℕ) : ℝ)) ≤
        KG * Φ n (1 * ((zdistInf d (sz.L n) (STblk sz n (pr n v).1 - STblk sz n (pr n v).2) : ℕ) : ℝ)) := by
      rw [one_mul]
      have hs : (0 : ℝ) ≤ ((zdistInf d (sz.L n) (STblk sz n (pr n v).1 - STblk sz n (pr n v).2) : ℕ) : ℝ) :=
        Nat.cast_nonneg _
      refine le_trans ?_ (hcGf cG' hcG'0 hcG'1 _ hs)
      exact S.assm.2.2.2.2.1.1 n (Set.mem_Ici.2 (by positivity)) (Set.mem_Ici.2 (by positivity))
        (mul_le_mul_of_nonneg_right (min_le_left _ _) hs)
    have hord' : Q.g.scalingOrder = (e1 : ℤ) + Γa.ordN := by rw [hAe, hordN]; ring
    have harith := lwMoment_anp_arith (X := ((sz.size n : ℕ) : ℝ) ^ τ₁) (M := M) (f0 := Φ n 0)
      (η := etaT (STflowE z n) (t n)) (w := ((sz.W n : ℕ) : ℝ) ^ d)
      (Pc := Φ n (cG * ((zdistInf d (sz.L n) (STblk sz n (pr n v).1 - STblk sz n (pr n v).2) : ℕ) : ℝ)))
      (Φs := Φ n (1 * ((zdistInf d (sz.L n) (STblk sz n (pr n v).1 - STblk sz n (pr n v).2) : ℕ) : ℝ)))
      (K1 := K1) (KG := KG) (nM := Q.g.nM) (p := p) (e1 := e1) (k := k) (ao := Γa.ordN)
      (o := Q.g.scalingOrder) hX1 hM1 hΦ0 hf1 hη0 hη1 (by have := sz.W_pos n; positivity) (hP _ (by positivity)).le
      (hP _ hs0).le hPcK hK10 hKG0 hnM hord hord'
    have hX0' : (0 : ℝ) ≤ (((sz.size n : ℕ) : ℝ) ^ τ₁) ^ k := by positivity
    have hterm1 : K1 * (M * ((sz.size n : ℕ) : ℝ) ^ τ₁ * Φ n 0) ^ (Q.g.scalingOrder - LGraph.auxOrd Q.g) *
        ((((sz.W n : ℕ) : ℝ) ^ d) ^ Q.g.nM *
        LGraph.auxVal Q.g (fun a b => ((sz.size n : ℕ) : ℝ) ^ τ₁ * lwXiVar sz (STflowE z) t ρ n a b ω)
          (fun a => (split d (sz.L n) (sz.W n) (ℓ' a)).1)) ≤
        (((sz.size n : ℕ) : ℝ) ^ τ₁) ^ A * Kbig * lwMoment_R sz (STflowE z) t Φ p n (pr n v).1 (pr n v).2 := by
      rw [hav, ← hAe]
      refine le_trans ?_ harith
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h3 hX0')
        (by positivity)) (mul_nonneg hK10 (zpow_nonneg hΨ0.le _))
    have hsc := lwMoment_tail_le Q.g (sz.W n) (sz.L n) d (sz.W_pos n) (by have := sz.three_le_L n; omega)
      hΨ0 hΨ1 hNc hK20 htail
    calc _ ≤ _ := hgt
      _ ≤ (((sz.size n : ℕ) : ℝ) ^ τ₁) ^ A * Kbig * lwMoment_R sz (STflowE z) t Φ p n (pr n v).1 (pr n v).2 +
          lwMoment_R sz (STflowE z) t Φ p n (pr n v).1 (pr n v).2 := add_le_add hterm1 (hsc.trans hRf)
      _ = _ := by ring
  · rw [Q.val_of_not _ hf, norm_zero]
    have hKb : 0 ≤ Kbig := by rw [hKbig]; positivity
    exact mul_nonneg (add_nonneg (mul_nonneg (by positivity) hKb) zero_le_one) hR0

end Far

/-! ## 8. The far pairs: assembly of the expansion -/

section FarAssembly

variable {sz : Sizes d} {κ ε 𝔡 𝔠 : ℝ} {z : ℕ → ℂ} {t : ℕ → ℝ} {ε₀ C₁ C₂ C₃ : ℝ} {Cc : ℝ → ℝ} {Ψ : ℕ → ℝ}
  {Φ : ℕ → ℝ → ℝ}

/-- The far pairs `(x, y)`: block distance `> K (log W)²`. -/
def LWMomFar (sz : Sizes d) (K : ℕ) (n : ℕ) : Type :=
  {q : Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n) //
    (K : ℝ) * Real.log ((sz.W n : ℕ) : ℝ) ^ 2 < (lwBdist d (sz.L n) (sz.W n) q.1 q.2 : ℝ)}

theorem lwMoment_evX_one (r : (ℕ × ℕ) × PGraph (Fin 2)) : lwEvX 1 r = r.2 := by
  unfold lwEvX
  simp

theorem lwMoment_LWf_zero {E : ℝ} (hE : |E| < 2) (n : ℕ) (ω : sz.SeqΩ) (x y : Idx d (sz.L n) (sz.W n)) :
    LWf sz n E 0 ω x y = 0 := by
  unfold LWf
  refine Finset.sum_eq_zero fun α _ => ?_
  split_ifs
  · rfl
  refine Finset.sum_eq_zero fun β _ => ?_
  have : STGM sz n E 0 ω β β = 0 := by simp [STGM, lwExpTerm3_Gt_zero sz n hE]
  rw [this]; simp

/-- From `≺` of `‖Q.val D₁‖` to `≺` of `‖𝔼 Q.val D₁‖` (`lwExpTerm_prec_integral`: polynomial envelope and floor). -/
theorem lwMoment_prec_int (S : LWMomentCtx sz κ ε 𝔡 𝔠 z t ε₀ C₁ C₂ C₃ Cc Ψ Φ) (p : ℕ) {V : ℕ → Type}
    (pr : ∀ n, V n → Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n)) {Q : PGraph (Fin 2)} (hQ : Q.g.Normal)
    (hprec : sz.Prec (U := V) (fun n v ω => ‖Q.val (lwMoment_D sz n (STflowE z n) (t n) ω) ![(pr n v).1, (pr n v).2]‖)
      (fun n v _ => lwMoment_R sz (STflowE z) t Φ p n (pr n v).1 (pr n v).2)) :
    sz.Prec (U := V) (fun n v _ => ‖∫ ω, Q.val (lwMoment_D sz n (STflowE z n) (t n) ω) ![(pr n v).1, (pr n v).2]
        ∂sz.seqP‖) (fun n v _ => lwMoment_R sz (STflowE z) t Φ p n (pr n v).1 (pr n v).2) := by
  obtain ⟨Kenv, henv⟩ := lwMoment_env S Q hQ
  exact lwExpTerm_prec_integral sz (fun n v ω => Q.val (lwMoment_D sz n (STflowE z n) (t n) ω) ![(pr n v).1, (pr n v).2])
    (fun n v => lwMoment_R sz (STflowE z) t Φ p n (pr n v).1 (pr n v).2) (Kenv := Kenv)
    (Kf := (p : ℝ) * (2 + C₂)) (lwMoment_size_tendsto S)
    (henv.mono fun n h v ω => h _ _ ω)
    ((lwMoment_floor S p).mono fun n h v => h _ _) hprec

/-- Every graph `r.2` of the engine lists has `‖𝔼 r.2.val D₁‖ ≺ R` at the far pairs. -/
theorem lwMoment_prec_far_r (S : LWMomentCtx sz κ ε 𝔡 𝔠 z t ε₀ C₁ C₂ C₃ Cc Ψ Φ) {p : ℕ} (hp0 : 0 < p)
    {K0 : ℕ} {D : ℝ} (hK0 : 1 / 𝔠 ≤ K0) (hD : ((p : ℝ) * (2 + C₂) + 1) / 𝔠 ≤ D)
    {outsX errsX : List ((ℕ × ℕ) × PGraph (Fin 2))}
    (hc : LWLocRegConcl p 1 (ε₀ / 2) K0 d D (outsX.map (lwEvX 1)) (errsX.map (lwEvX 1)))
    {K : ℕ} {r : (ℕ × ℕ) × PGraph (Fin 2)} (hr : r ∈ outsX ++ errsX) (hK : Fintype.card (r.2.E' ⊕ r.2.I') ≤ K) :
    sz.Prec (U := LWMomFar sz K)
      (fun n v _ => ‖∫ ω, r.2.val (lwMoment_D sz n (STflowE z n) (t n) ω) ![v.1.1, v.1.2] ∂sz.seqP‖)
      (fun n v _ => lwMoment_R sz (STflowE z) t Φ p n v.1.1 v.1.2) := by
  classical
  obtain ⟨-, hc2, hc3, -, hc5⟩ := hc
  have hnM : (fxyPowGraph p).pack.g.nM = p := fxyPowGraph_nM p
  have hrm : lwEvX 1 r ∈ outsX.map (lwEvX 1) ++ errsX.map (lwEvX 1) := by
    rcases List.mem_append.1 hr with h | h
    · exact List.mem_append_left _ (List.mem_map_of_mem h)
    · exact List.mem_append_right _ (List.mem_map_of_mem h)
  obtain ⟨-, hQ, -, hnM', -⟩ := hc3 _ hrm
  rw [lwMoment_evX_one] at hQ hnM'
  have key : sz.Prec (U := LWMomFar sz K)
      (fun n v ω => ‖r.2.val (lwMoment_D sz n (STflowE z n) (t n) ω) ![v.1.1, v.1.2]‖)
      (fun n v _ => lwMoment_R sz (STflowE z) t Φ p n v.1.1 v.1.2) := by
    rcases List.mem_append.1 hr with h | h
    · have hq : lwEvX 1 r ∈ outsX.map (lwEvX 1) := List.mem_map_of_mem h
      obtain ⟨-, -, h345, h6, -⟩ := hc5 _ hq
      rw [lwMoment_evX_one] at h345 h6
      by_cases hmol : r.2.g.molOf (Sum.inl (r.2.ext 0)) = r.2.g.molOf (Sum.inl (r.2.ext 1))
      · exact lwMoment_prec_scale S p (V := LWMomFar sz K) (fun n v => v.1) hQ hmol hK (fun n v => v.2)
      · exact lwMoment_prec_anp S hp0 (V := LWMomFar sz K) (fun n v => v.1) hQ h345 hmol (hnM'.trans_eq hnM) h6 hK
    · have hq : lwEvX 1 r ∈ errsX.map (lwEvX 1) := List.mem_map_of_mem h
      have := hc2 _ hq
      rw [lwMoment_evX_one] at this
      exact lwMoment_prec_err S p hK0 hD (V := LWMomFar sz K) (fun n v => v.1) hQ this
  exact lwMoment_prec_int S p (V := LWMomFar sz K) (fun n v => v.1) hQ key

/-- **The far pairs** (`7_8:943-950`): from the engine lists (`lw_localregularX`, lists before `m`), `𝔼 |f_{xy}|^p ≺ R` for
the pairs at block distance `> K (log W)²`, `K ≥` the number of vertices of every graph of the lists.  The `n`-th
expansion is evaluated at `m = m(E_n)`, `‖m‖ = 1`; the outputs with `𝓜_x ≠ 𝓜_y` use `lem:Anp`, those with `𝓜_x = 𝓜_y`
use `(eq:far_ab)`, the errors use the size bound. -/
theorem lwMoment_prec_far (S : LWMomentCtx sz κ ε 𝔡 𝔠 z t ε₀ C₁ C₂ C₃ Cc Ψ Φ) {p : ℕ} (hp : Even p) (hp0 : 0 < p)
    {K0 : ℕ} {D : ℝ} (hK0 : 1 / 𝔠 ≤ K0) (hD : ((p : ℝ) * (2 + C₂) + 1) / 𝔠 ≤ D)
    {outsX errsX : List ((ℕ × ℕ) × PGraph (Fin 2))}
    (hX : ∀ m : ℂ, m ≠ 0 → LWLocRegConcl p m (ε₀ / 2) K0 d D (outsX.map (lwEvX m)) (errsX.map (lwEvX m)) ∧
      ∀ Q ∈ outsX.map (lwEvX m) ++ errsX.map (lwEvX m), p ≤ Q.g.waved.countP (fun e => !e.col))
    {K : ℕ} (hK : ∀ r ∈ outsX ++ errsX, Fintype.card (r.2.E' ⊕ r.2.I') ≤ K) :
    sz.Prec (U := LWMomFar sz K) (fun n q _ => ∫ ω, ‖LWf sz n (STflowE z n) (t n) ω q.1.1 q.1.2‖ ^ p ∂sz.seqP)
      (fun n q _ => lwMoment_R sz (STflowE z) t Φ p n q.1.1 q.1.2) := by
  classical
  have hsz := lwMoment_size_tendsto S
  let F : (ℕ × ℕ) × PGraph (Fin 2) → ∀ n, LWMomFar sz K n → ℝ := fun r n v =>
    ‖∫ ω, r.2.val (lwMoment_D sz n (STflowE z n) (t n) ω) ![v.1.1, v.1.2] ∂sz.seqP‖
  let G : ∀ n, LWMomFar sz K n → ℝ := fun n v => lwMoment_R sz (STflowE z) t Φ p n v.1.1 v.1.2
  refine (st6_prec_det_iff sz hsz (fun n (v : LWMomFar sz K n) => ∫ ω, ‖LWf sz n (STflowE z n) (t n) ω v.1.1 v.1.2‖ ^ p ∂sz.seqP)
    G).2 ?_
  intro τ hτ
  have hper : ∀ r ∈ outsX ++ errsX, sz.Prec (U := LWMomFar sz K) (fun n v _ => F r n v) (fun n v _ => G n v) :=
    fun r hr => lwMoment_prec_far_r S hp0 hK0 hD (hX 1 one_ne_zero).1 hr (hK r hr)
  have hG : ∀ n (v : LWMomFar sz K n), 0 ≤ G n v := fun n v => hp.pow_nonneg _
  have hsum := lwMoment_sum_det sz hsz (V := LWMomFar sz K) (outsX ++ errsX) F G hG
    (fun r hr => (st6_prec_det_iff sz hsz (F r) G).1 (hper r hr)) τ hτ
  obtain ⟨-, hE, ht1', -⟩ := lwMoment_flow_facts S
  filter_upwards [hsum] with n hn
  intro v
  have hEn : |STflowE z n| < 2 := by linarith [hE n, S.hκ]
  by_cases ht0 : t n = 0
  · have : ∀ ω, ‖LWf sz n (STflowE z n) (t n) ω v.1.1 v.1.2‖ ^ p = 0 := fun ω => by
      rw [ht0, lwMoment_LWf_zero hEn n ω]; simp [hp0.ne']
    simp only [this, integral_zero]
    exact mul_nonneg (Real.rpow_nonneg (by positivity) _) (hG n v)
  · have ht0' : 0 < t n := lt_of_le_of_ne (S.t0 n) (Ne.symm ht0)
    obtain ⟨hcn, hw⟩ := hX (mE (STflowE z n)) (lwWx_mE_ne _ hEn)
    refine le_trans (lwMoment_expand sz hp n hEn ht0' (ht1' n) hcn (fun r hr => ?_) v.1.1 v.1.2) (hn v)
    have hmem : lwEvX (mE (STflowE z n)) r ∈ outsX.map (lwEvX (mE (STflowE z n))) ++
        errsX.map (lwEvX (mE (STflowE z n))) := by
      rcases List.mem_append.1 hr with h | h
      · exact List.mem_append_left _ (List.mem_map_of_mem h)
      · exact List.mem_append_right _ (List.mem_map_of_mem h)
    exact hw (lwEvX (mE (STflowE z n)) r) hmem

end FarAssembly

/-! ## 9. The near pairs, deterministic part: the max bound `|f_{xy}| ≲ η⁻¹ max_a |𝓛^{(1)}_a - m|` (`7_8:61-66`) -/

section Near

open RBM.Green RBM.Loop

variable {d L W : ℕ} [NeZero L] [NeZero W]

private theorem lwMoment_gres_blockMat (H : Matrix (Idx d L W) (Idx d L W) ℂ) (z : ℂ) (x y : Vtx d L W) :
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

/-- `𝓛^{(1)}_{+,a} - m = Σ_{β ∈ [a]} W^{-d} (G_{ββ} - m)` (`tr E_a = 1`). -/
theorem lwMoment_avgErr_sum (H : Matrix (Idx d L W) (Idx d L W) ℂ) (z m : ℂ) (a : Zd d L) :
    loopFine d L W H z (fun _ : Fin 1 => true) (fun _ => a) - m =
      ∑ β : Idx d L W, if (split d L W β).1 = a then (((W : ℂ) ^ d)⁻¹) * (Gres H z true β β - m) else 0 := by
  have h1 : loopFine d L W H z (fun _ : Fin 1 => true) (fun _ => a) =
      Matrix.trace (Gres (blockMat d L W H) z true * Eblk d L W a) := by
    simp [loopFine, loopM, List.ofFn_succ]
  have h2 : Matrix.trace (Gres (blockMat d L W H) z true * Eblk d L W a) - m =
      Matrix.trace ((Gres (blockMat d L W H) z true - m • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) *
        Eblk d L W a) := by
    rw [Matrix.sub_mul, Matrix.trace_sub, Matrix.smul_mul, Matrix.trace_smul, Matrix.one_mul,
      trace_Eblk]
    simp
  rw [h1, h2]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Eblk, Matrix.diagonal_apply]
  have h3 : ∀ i : Vtx d L W, (∑ j, (Gres (blockMat d L W H) z true - m • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) i j *
      if j = i then (if j.1 = a then ((W : ℂ) ^ d)⁻¹ else 0) else 0) =
      if i.1 = a then ((W : ℂ) ^ d)⁻¹ * (Gres (blockMat d L W H) z true i i - m) else 0 := by
    intro i
    rw [Finset.sum_eq_single i]
    · by_cases hi : i.1 = a <;> simp [hi, Matrix.sub_apply, Matrix.one_apply]
      ring
    · intro j _ hj; simp [hj]
    · simp
  simp only [h3]
  rw [← Equiv.sum_comp (splitEquiv d L W)]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [lwMoment_gres_blockMat]
  simp only [Equiv.symm_apply_apply]
  rfl

/-- **The row average is bounded by the block averages**: `|Σ_β S_{αβ} Ǧ_{ββ}| ≤ max_b |tr(Ǧ E_b)|`, because `S_{αβ} =
W^{-d} S^{(B)}_{[α][β]}` and the row `S^{(B)}_{[α]·}` is a probability vector (`(eq:boundfxyGinf)`, `7_8:62-66`). -/
theorem lwMoment_row_le (hL : 3 ≤ L) (g : ℝ) (G : Matrix (Idx d L W) (Idx d L W) ℂ) (m : ℂ) (α : Idx d L W) {μ : ℝ}
    (hμ : ∀ b : Zd d L, ‖∑ β : Idx d L W, if (split d L W β).1 = b then (((W : ℂ) ^ d)⁻¹) * (G β β - m) else 0‖ ≤ μ) :
    ‖∑ β, (svarF d L W g α β : ℂ) * (G β β - m)‖ ≤ μ := by
  have e : ∑ β, (svarF d L W g α β : ℂ) * (G β β - m) =
      ∑ b, (SBR d L g (split d L W α).1 b : ℂ) *
        ∑ β, (if (split d L W β).1 = b then (((W : ℂ) ^ d)⁻¹) * (G β β - m) else 0) := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun β _ => ?_
    rw [Finset.sum_eq_single (split d L W β).1]
    · simp only [svarF, ite_true]
      push_cast
      ring
    · intro b _ hb; simp [Ne.symm hb]
    · simp
  rw [e]
  have hnn : ∀ b, 0 ≤ SBR d L g (split d L W α).1 b := fun b => by
    simpa [SBR] using sbKernelR_nonneg d L g ((split d L W α).1 - b)
  refine (norm_sum_le _ _).trans ?_
  calc ∑ b, ‖(SBR d L g (split d L W α).1 b : ℂ) *
        ∑ β, (if (split d L W β).1 = b then (((W : ℂ) ^ d)⁻¹) * (G β β - m) else 0)‖
      ≤ ∑ b, SBR d L g (split d L W α).1 b * μ := by
        refine Finset.sum_le_sum fun b _ => ?_
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hnn b)]
        exact mul_le_mul_of_nonneg_left (hμ b) (hnn b)
    _ = μ := by rw [← Finset.sum_mul, sum_SBR_row hL, one_mul]

end Near

section Ward

open RBM.Green

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Ward's identity, column**: `Σ_α |G_{αy}|² = Im G_{yy} / Im z` (`im_green_diag`). -/
theorem lwMoment_ward_col {H : Matrix ι ι ℂ} (hH : H.IsHermitian) {z : ℂ} (hz : z.im ≠ 0) (y : ι) :
    ∑ α, ‖green H z α y‖ ^ 2 = (green H z y y).im / z.im := by
  rw [eq_div_iff hz, mul_comm, im_green_diag hH hz y]
  congr 1
  simp only [dotProduct, Matrix.mulVec_single_one, Pi.star_apply, RCLike.star_def, Complex.re_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [Matrix.col_apply, Complex.conj_mul']
  rw [← Complex.ofReal_pow, Complex.ofReal_re]

/-- **Ward's identity, row**: `Σ_α |G_{xα}|² = Im G_{xx} / Im z` (apply the column identity at `z̄`). -/
theorem lwMoment_ward_row {H : Matrix ι ι ℂ} (hH : H.IsHermitian) {z : ℂ} (hz : z.im ≠ 0) (x : ι) :
    ∑ α, ‖green H z x α‖ ^ 2 = (green H z x x).im / z.im := by
  have hz' : ((starRingEnd ℂ) z).im ≠ 0 := by simpa using hz
  have h := lwMoment_ward_col hH hz' x
  have e1 : ∀ a b, green H ((starRingEnd ℂ) z) a b = star (green H z b a) := fun a b => by
    have := lwWx_Gres_false hH z a b
    simp only [green, Gres, ite_true, Bool.false_eq_true, ite_false, Matrix.nonsing_inv_eq_ringInverse] at this ⊢
    exact this
  simp only [e1, norm_star] at h
  rw [h]
  simp [Complex.conj_im, neg_div_neg_eq]

/-- **Cauchy-Schwarz and Ward**: `Σ_α |G_{xα}| |G_{αy}| ≤ A/η` when `|G_{xx}|, |G_{yy}| ≤ A`
(`7_8:62-66`, `Σ_α |G_{xα}|² = Im G_{xx}/η`). -/
theorem lwMoment_CS {H : Matrix ι ι ℂ} (hH : H.IsHermitian) {z : ℂ} (hz : 0 < z.im) {A : ℝ} (x y : ι)
    (hx : ‖green H z x x‖ ≤ A) (hy : ‖green H z y y‖ ≤ A) :
    ∑ α, ‖green H z x α‖ * ‖green H z α y‖ ≤ A / z.im := by
  have hz0 : z.im ≠ 0 := hz.ne'
  have hr := lwMoment_ward_row hH hz0 x
  have hc := lwMoment_ward_col hH hz0 y
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun α => ‖green H z x α‖) (fun α => ‖green H z α y‖)
  rw [hr, hc] at hcs
  have hS0 : 0 ≤ ∑ α, ‖green H z x α‖ * ‖green H z α y‖ := Finset.sum_nonneg fun _ _ => by positivity
  have hxi : (green H z x x).im ≤ A := (Complex.im_le_norm _).trans hx
  have hyi : (green H z y y).im ≤ A := (Complex.im_le_norm _).trans hy
  have hxi0 : 0 ≤ (green H z x x).im / z.im := by rw [← hr]; positivity
  have hyi0 : 0 ≤ (green H z y y).im / z.im := by rw [← hc]; positivity
  have hA0 : 0 ≤ A := (norm_nonneg _).trans hx
  have h1 : (green H z x x).im / z.im ≤ A / z.im := div_le_div_of_nonneg_right hxi hz.le
  have h2 : (green H z y y).im / z.im ≤ A / z.im := div_le_div_of_nonneg_right hyi hz.le
  have h3 : (∑ α, ‖green H z x α‖ * ‖green H z α y‖) ^ 2 ≤ (A / z.im) ^ 2 :=
    hcs.trans (by rw [sq]; exact mul_le_mul h1 h2 hyi0 (by positivity))
  by_contra hcon
  push Not at hcon
  nlinarith [div_nonneg hA0 hz.le]

end Ward

section NearBound

variable {sz : Sizes d} {κ ε 𝔡 𝔠 : ℝ} {z : ℕ → ℂ} {t : ℕ → ℝ} {ε₀ C₁ C₂ C₃ : ℝ} {Cc : ℝ → ℝ} {Ψ : ℕ → ℝ}
  {Φ : ℕ → ℝ → ℝ}

/-- **The max bound, pathwise** (`(eq:boundfxyGinf)`, `7_8:61-66`): `‖f_{xy}‖ ≤ (A/η) μ` when `‖G_{aa}‖ ≤ A` and
`‖𝓛^{(1)}_{+,b} - m‖ ≤ μ` for every block `b`. -/
theorem lwMoment_f_le (n : ℕ) {E t : ℝ} (hE : |E| < 2) (ht : t < 1) (ω : sz.SeqΩ) {A μ : ℝ}
    (hμ : ∀ b : Zd d (sz.L n), ‖Lloop sz n E t (fun _ : Fin 1 => true) (fun _ => b) ω - mE E‖ ≤ μ)
    (hA : ∀ x : Idx d (sz.L n) (sz.W n), ‖Gt sz n E t true ω x x‖ ≤ A) (x y : Idx d (sz.L n) (sz.W n)) :
    ‖LWf sz n E t ω x y‖ ≤ A / etaT E t * μ := by
  have hG : ∀ a b, Gt sz n E t true ω a b = green (sz.seqHflow n t ω) (zt E t) a b := fun a b => by
    rw [lwMoment_Gt_true_eq]
  have hH := sz.seqHflow_isHermitian n t ω
  have him : 0 < (zt E t).im := lwWx_im_pos E t hE ht
  have hμ0 : 0 ≤ μ := (norm_nonneg _).trans (hμ 0)
  -- the row average
  have hrow : ∀ α : Idx d (sz.L n) (sz.W n),
      ‖∑ β, (LWS sz n α β : ℂ) * STGM sz n E t ω β β‖ ≤ μ := by
    intro α
    have := lwMoment_row_le (sz.three_le_L n) (sz.lam n) (Gt sz n E t true ω) (mE E) α (μ := μ) (fun b => by
      have h := lwMoment_avgErr_sum (sz.seqHflow n t ω) (zt E t) (mE E) b
      have e : ∀ β, Gres (sz.seqHflow n t ω) (zt E t) true β β = Gt sz n E t true ω β β := fun β => by
        rw [hG]; simp [green, Gres, Matrix.nonsing_inv_eq_ringInverse]
      simp only [e] at h
      rw [← h]
      exact hμ b)
    convert this using 2
    refine Finset.sum_congr rfl fun β _ => ?_
    simp [STGM, LWS]
  have hCS := lwMoment_CS hH him (A := A) x y (by rw [← hG]; exact hA x) (by rw [← hG]; exact hA y)
  unfold LWf
  refine (norm_sum_le _ _).trans ?_
  rw [etaT_eq_zt_im]
  calc ∑ α, ‖if α = x ∨ α = y then (0 : ℂ) else
        ∑ β, (LWS sz n α β : ℂ) * STGM sz n E t ω β β * Gt sz n E t true ω x α * Gt sz n E t true ω α y‖
      ≤ ∑ α, μ * (‖green (sz.seqHflow n t ω) (zt E t) x α‖ * ‖green (sz.seqHflow n t ω) (zt E t) α y‖) := by
        refine Finset.sum_le_sum fun α _ => ?_
        split_ifs
        · simp only [norm_zero]; positivity
        · have e : ∑ β, (LWS sz n α β : ℂ) * STGM sz n E t ω β β * Gt sz n E t true ω x α * Gt sz n E t true ω α y =
            (∑ β, (LWS sz n α β : ℂ) * STGM sz n E t ω β β) * Gt sz n E t true ω x α * Gt sz n E t true ω α y := by
            rw [Finset.sum_mul, Finset.sum_mul]
          rw [e, norm_mul, norm_mul, hG, hG]
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_right (hrow α) (by positivity)
    _ = μ * ∑ α, ‖green (sz.seqHflow n t ω) (zt E t) x α‖ * ‖green (sz.seqHflow n t ω) (zt E t) α y‖ := by
        rw [Finset.mul_sum]
    _ ≤ μ * (A / (zt E t).im) := mul_le_mul_of_nonneg_left hCS hμ0
    _ = A / (zt E t).im * μ := by ring

end NearBound

/-! ## 10. The near pairs, stochastic part, and the target `lwMoment_holds` -/

section NearStoch

variable {sz : Sizes d} {κ ε 𝔡 𝔠 : ℝ} {z : ℕ → ℂ} {t : ℕ → ℝ} {ε₀ C₁ C₂ C₃ : ℝ} {Cc : ℝ → ℝ} {Ψ : ℕ → ℝ}
  {Φ : ℕ → ℝ → ℝ}

/-- The near pairs: block distance `≤ K (log W)²`. -/
def LWMomNear (sz : Sizes d) (K : ℕ) (n : ℕ) : Type :=
  {q : Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n) //
    (lwBdist d (sz.L n) (sz.W n) q.1 q.2 : ℝ) ≤ (K : ℝ) * Real.log ((sz.W n : ℕ) : ℝ) ^ 2}

/-- The entry scale for the near pairs `Ψ' = max(Φ(0), W^{-d/2})` (`7_8:62-66`). -/
def lwMoment_Psi' (sz : Sizes d) (Φ : ℕ → ℝ → ℝ) (n : ℕ) : ℝ :=
  max (Φ n 0) (((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2))

theorem lwMoment_Psi'_facts (S : LWMomentCtx sz κ ε 𝔡 𝔠 z t ε₀ C₁ C₂ C₃ Cc Ψ Φ) :
    ∀ᶠ n in atTop, 0 < Φ n 0 ∧ ((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2) ≤ lwMoment_Psi' sz Φ n ∧
      lwMoment_Psi' sz Φ n ≤ ((sz.W n : ℕ) : ℝ) ^ (-ε₀) ∧ lwMoment_Psi' sz Φ n ≤ max 1 C₃ * Φ n 0 := by
  have hcls := S.assm.2.2.2.1
  filter_upwards [hcls.1, hcls.2.2, S.assm.2.1] with n hpos hwin hW
  have h0 := hpos 0 le_rfl
  refine ⟨h0.1, le_max_right _ _, max_le h0.2 (hW.1.trans hW.2), max_le ?_ ?_⟩
  · calc Φ n 0 = 1 * Φ n 0 := (one_mul _).symm
      _ ≤ max 1 C₃ * Φ n 0 := mul_le_mul_of_nonneg_right (le_max_left _ _) h0.1.le
  · exact hwin.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) h0.1.le)

/-- `STmaxLoop2 ≺ Ψ'²` from `LWLoop2` (`Φ(r) ≤ Φ(0) ≤ Ψ'`; the `≺` over the pairs `(a, b)` already is a supremum). -/
theorem lwMoment_maxLoop2_prec (S : LWMomentCtx sz κ ε 𝔡 𝔠 z t ε₀ C₁ C₂ C₃ Cc Ψ Φ) :
    sz.Prec (U := fun _ => Unit) (fun n _ ω => STmaxLoop2 sz n (STflowE z n) (t n) ω)
      (fun n _ _ => lwMoment_Psi' sz Φ n ^ 2) := by
  apply lwMoment_prec_of_whp
  intro τ hτ
  refine ⟨_, Sizes.Prec.whp sz S.assm.2.2.2.2.2 hτ, ?_⟩
  have hrel := S.assm.2.2.2.2.1
  filter_upwards [S.assm.2.2.2.1.1, lwMoment_Psi'_facts S] with n hpos hP
  intro ω hω u
  unfold STmaxLoop2
  refine Finset.sup'_le _ _ fun q _ => ?_
  have h1 := hω (false, q.1, q.2)
  refine h1.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  have hr : (0 : ℝ) ≤ ((zdistInf d (sz.L n) (q.1 - q.2) : ℕ) : ℝ) := Nat.cast_nonneg _
  have e1 : Φ n ((zdistInf d (sz.L n) (q.1 - q.2) : ℕ) : ℝ) ≤ Φ n 0 :=
    hrel.1 n (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hr) hr
  have e2 : Φ n 0 ≤ lwMoment_Psi' sz Φ n := le_max_left _ _
  exact pow_le_pow_left₀ (hpos _ hr).1.le (e1.trans e2) 2

/-- `max_a |𝓛^{(1)}_{+,a} - m| ≤ N^{τ₁} Ψ'²` w.h.p. (`STGavLGEX` at `Ψ'`, `7_8:62-66`). -/
theorem lwMoment_avg_whp (S : LWMomentCtx sz κ ε 𝔡 𝔠 z t ε₀ C₁ C₂ C₃ Cc Ψ Φ) {τ₁ : ℝ} (hτ₁ : 0 < τ₁) :
    sz.Whp (fun n => {ω | ∀ a : Zd d (sz.L n),
      ‖Lloop sz n (STflowE z n) (t n) (fun _ : Fin 1 => true) (fun _ => a) ω - mE (STflowE z n)‖ ≤
        ((sz.size n : ℕ) : ℝ) ^ τ₁ * lwMoment_Psi' sz Φ n ^ 2}) := by
  have hGav := (RBM.Green.stGbEXP_holds S.hd).2.2 κ ε 𝔡 S.hκ S.hε S.h𝔡 𝔠 sz z S.flow t S.t0 S.t1 ε₀ S.assm.1
  have h := hGav (lwMoment_Psi' sz Φ) ((lwMoment_Psi'_facts S).mono fun n h => h.2.1)
    ((lwMoment_Psi'_facts S).mono fun n h => h.2.2.1) S.assm.2.2.1.1 (lwMoment_maxLoop2_prec S)
  exact Sizes.Prec.whp sz h hτ₁

theorem lwMoment_fxyVal_D (n : ℕ) (E t : ℝ) (ω : sz.SeqΩ) (x y : Idx d (sz.L n) (sz.W n)) :
    fxyVal (lwMoment_D sz n E t ω) x y = LWf sz n E t ω x y := by
  unfold fxyVal RBM.Gauss.Sizes.LWf
  refine Finset.sum_congr rfl fun α _ => ?_
  split_ifs
  · rfl
  · refine Finset.sum_congr rfl fun β _ => ?_
    simp only [lwMoment_D, lwSampleData, lwS, Matrix.of_apply, Matrix.diagonal_apply_eq, STGM, ite_true,
      RBM.Gauss.Sizes.LWS]
    change ((1 * svarF d (sz.L n) (sz.W n) (sz.lam n) α β : ℝ) : ℂ) *
        (Gt sz n E t true ω β β - mE E) * Gt sz n E t true ω x α * Gt sz n E t true ω α y = _
    push_cast
    ring


theorem lwMoment_near_arith {X M H f0 fs Ψp B Y : ℝ} (hX : 1 ≤ X) (hH : 0 ≤ H) (hf0 : 0 ≤ f0) (hfs : 0 ≤ fs)
    (hΨ0 : 0 ≤ Ψp) (hΨ : Ψp ≤ M * f0) (hM : 0 ≤ M) (hB : 0 ≤ B) (hfB : f0 ≤ B * Y * fs) (hYX : Y ≤ X)
    (hc : 2 * M ^ 2 * B ≤ X) :
    2 * H * (X * Ψp ^ 2) ≤ X ^ 3 * (H * f0 * fs) := by
  have hX0 : 0 ≤ X := by linarith
  have h1 : Ψp ^ 2 ≤ M ^ 2 * f0 ^ 2 := by rw [← mul_pow]; exact pow_le_pow_left₀ hΨ0 hΨ 2
  have h2 : f0 ^ 2 ≤ f0 * (B * X * fs) := by
    rw [sq]
    exact mul_le_mul_of_nonneg_left (hfB.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hYX hB) hfs)) hf0
  have h3 : Ψp ^ 2 ≤ M ^ 2 * (f0 * (B * X * fs)) :=
    h1.trans (mul_le_mul_of_nonneg_left h2 (by positivity))
  have h4 : 0 ≤ H * f0 * fs * X := by positivity
  calc 2 * H * (X * Ψp ^ 2) ≤ 2 * H * (X * (M ^ 2 * (f0 * (B * X * fs)))) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h3 hX0) (by positivity)
    _ = (2 * M ^ 2 * B) * (X * (X * (H * f0 * fs))) := by ring
    _ ≤ X * (X * (X * (H * f0 * fs))) :=
        mul_le_mul_of_nonneg_right hc (by positivity)
    _ = X ^ 3 * (H * f0 * fs) := by ring

/-- `(max 1 (K (log W)²))^{C₂} ≤ N^{τ₁}` eventually. -/
theorem lwMoment_rad (sz : Sizes d) (hsz : sz.SizeTendsto) (K : ℕ) {C₂ : ℝ} (hC₂ : 0 ≤ C₂) {τ₁ : ℝ} (hτ₁ : 0 < τ₁) :
    ∀ᶠ n in atTop, (max 1 ((K : ℝ) * Real.log ((sz.W n : ℕ) : ℝ) ^ 2)) ^ C₂ ≤ ((sz.size n : ℕ) : ℝ) ^ τ₁ := by
  filter_upwards [lwXiRad_holds sz hsz ((K : ℝ) ^ C₂) 0 (2 * C₂) (by positivity) le_rfl (by linarith) τ₁ hτ₁] with n hn
  have hlog : 0 ≤ Real.log ((sz.W n : ℕ) : ℝ) :=
    Real.log_nonneg (by exact_mod_cast sz.W_pos n)
  have hy : 0 ≤ (K : ℝ) * Real.log ((sz.W n : ℕ) : ℝ) ^ 2 := by positivity
  have e : ((K : ℝ) * Real.log ((sz.W n : ℕ) : ℝ) ^ 2) ^ C₂ =
      (K : ℝ) ^ C₂ * Real.log ((sz.W n : ℕ) : ℝ) ^ (2 * C₂) := by
    rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_natCast (Real.log _) 2, ← Real.rpow_mul hlog]
    norm_num
  have hmax : (max 1 ((K : ℝ) * Real.log ((sz.W n : ℕ) : ℝ) ^ 2)) ^ C₂ ≤
      1 + ((K : ℝ) * Real.log ((sz.W n : ℕ) : ℝ) ^ 2) ^ C₂ := by
    rcases le_total 1 ((K : ℝ) * Real.log ((sz.W n : ℕ) : ℝ) ^ 2) with h | h
    · rw [max_eq_right h]; linarith [Real.rpow_nonneg hy C₂]
    · rw [max_eq_left h, Real.one_rpow]; linarith [Real.rpow_nonneg hy C₂]
  rw [e] at hmax
  linarith



/-- **The near pairs, in probability** (`7_8:61-66`, the max bound): for the pairs with block distance `≤ K (log W)²`,
`|f_{xy}|^p ≤ (2/η · N^{τ₁} Ψ'²)^p` on the good event, and `Ψ'² ≤ polylog · Φ(0) Φ(|a-b|)`. -/
theorem lwMoment_prec_near_pre (S : LWMomentCtx sz κ ε 𝔡 𝔠 z t ε₀ C₁ C₂ C₃ Cc Ψ Φ) {p : ℕ} (hp0 : 0 < p) (K : ℕ) :
    sz.Prec (U := LWMomNear sz K)
      (fun n q ω => ‖(((‖LWf sz n (STflowE z n) (t n) ω q.1.1 q.1.2‖ ^ p : ℝ)) : ℂ)‖)
      (fun n q _ => lwMoment_R sz (STflowE z) t Φ p n q.1.1 q.1.2) := by
  classical
  have hε₀ := S.assm.1
  have hsz := lwMoment_size_tendsto S
  have h𝔠 := (lwMoment_flow_facts S).1.1
  have hcls := S.assm.2.2.2.1
  have hC₂ : 1 < C₂ := S.assm.2.2.2.2.1.2.2.1
  have hC₁ : 1 < C₁ := S.assm.2.2.2.2.1.2.1
  apply lwMoment_prec_of_whp
  intro τ hτ
  have hp0' : (0 : ℝ) < p := by exact_mod_cast hp0
  set τ₁ : ℝ := min (τ / (3 * p)) (𝔠 * ε₀ / 4) with hτ₁def
  have hτ₁ : 0 < τ₁ := lt_min (by positivity) (by positivity)
  refine ⟨_, HighProbAt.inter (Sizes.tendsto_size sz hsz) (lwMoment_entry_whp S hτ₁) (lwMoment_avg_whp S hτ₁), ?_⟩
  have hE : ∀ n, |STflowE z n| < 2 := fun n => by linarith [(lwMoment_flow_facts S).2.1 n, S.hκ]
  set M : ℝ := max 1 C₃ with hMdef
  have hM1 : 1 ≤ M := le_max_left _ _
  filter_upwards [lwMoment_Psi_facts S hτ₁.le (min_le_right _ _), lwMoment_Psi'_facts S,
    lwMoment_phi_facts hcls S.assm.2.2.2.2.1, lwMoment_rad sz hsz K (C₂ := C₂) (by linarith) hτ₁,
    hsz.eventually_ge_atTop 1,
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
  have hEn := hE n
  have ht1 := (lwMoment_flow_facts S).2.2.1 n
  have hη0 : 0 < etaT (STflowE z n) (t n) := etaT_pos hEn ht1
  have hη1 : etaT (STflowE z n) (t n) ≤ 1 := lwMoment_etaT_le_one hEn (S.t0 n) ht1
  have hηi : 1 ≤ (etaT (STflowE z n) (t n))⁻¹ := one_le_inv_iff₀.2 ⟨hη0, hη1⟩
  -- the entries: `‖G_{aa}‖ ≤ 2`
  have hΨ1 : M * X * Φ n 0 ≤ 1 := hup.trans (Real.rpow_le_one_of_one_le_of_nonpos hW1 (by linarith))
  have hMX : 1 ≤ M * X := by nlinarith
  have hGa : ∀ a : Idx d (sz.L n) (sz.W n), ‖Gt sz n (STflowE z n) (t n) true ω a a‖ ≤ 2 := by
    intro a
    have h1 : ‖STGM sz n (STflowE z n) (t n) ω a a‖ ≤ 1 := by
      refine (hω1 (a, a)).trans ?_
      calc X * Φ n 0 = 1 * (X * Φ n 0) := (one_mul _).symm
        _ ≤ M * (X * Φ n 0) := mul_le_mul_of_nonneg_right hM1 (by positivity)
        _ = M * X * Φ n 0 := by ring
        _ ≤ 1 := hΨ1
    have h2 : ‖mE (STflowE z n)‖ = 1 := norm_mE (hE n).le
    have h3 : Gt sz n (STflowE z n) (t n) true ω a a = STGM sz n (STflowE z n) (t n) ω a a + mE (STflowE z n) := by
      simp [STGM]
    rw [h3]
    exact (norm_add_le _ _).trans (by linarith)
  have hf := lwMoment_f_le (sz := sz) n (hE n) ht1 ω (A := 2) (μ := X * lwMoment_Psi' sz Φ n ^ 2)
    (fun b => hω2 b) hGa v.1.1 v.1.2
  -- the distance `s = |a - b|` of the blocks and `Φ(0) ≤ polylog · Φ(s)`
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
  have hmain : 2 / etaT (STflowE z n) (t n) * (X * lwMoment_Psi' sz Φ n ^ 2) ≤
      X ^ 3 * ((etaT (STflowE z n) (t n))⁻¹ * Φ n 0 * Φ n s) := by
    have := lwMoment_near_arith (X := X) (M := M) (H := (etaT (STflowE z n) (t n))⁻¹) (f0 := Φ n 0)
      (fs := Φ n s) (Ψp := lwMoment_Psi' sz Φ n) (B := Cc 2 * C₁) (Y := (max 1 s) ^ C₂) hX1 (by linarith)
      hΦ0.le (hP s hs0).le (le_trans hΦ0.le (le_max_left _ _)) hΨ'M (by linarith) hB hfB hY hbig
    rwa [div_eq_mul_inv]
  have hR : lwMoment_R sz (STflowE z) t Φ p n v.1.1 v.1.2 =
      ((etaT (STflowE z n) (t n))⁻¹ * Φ n 0 * Φ n s) ^ p := by
    unfold lwMoment_R; rw [one_mul]
  have hXp : (X ^ 3) ^ p ≤ ((sz.size n : ℕ) : ℝ) ^ τ := by
    rw [← pow_mul, hXdef, ← Real.rpow_natCast, ← Real.rpow_mul hN0.le]
    refine Real.rpow_le_rpow_of_exponent_le hN1 ?_
    have : τ₁ ≤ τ / (3 * p) := min_le_left _ _
    calc τ₁ * ((3 * p : ℕ) : ℝ) ≤ τ / (3 * p) * ((3 * p : ℕ) : ℝ) :=
          mul_le_mul_of_nonneg_right this (by positivity)
      _ = τ := by push_cast; field_simp
  rw [Complex.norm_real, Real.norm_of_nonneg (by positivity), hR]
  have h1 := pow_le_pow_left₀ (norm_nonneg _) (hf.trans hmain) p
  have hR0 : 0 ≤ ((etaT (STflowE z n) (t n))⁻¹ * Φ n 0 * Φ n s) ^ p := by
    have := (hP s hs0).le
    positivity
  calc _ ≤ _ := h1
    _ = (X ^ 3) ^ p * ((etaT (STflowE z n) (t n))⁻¹ * Φ n 0 * Φ n s) ^ p := mul_pow _ _ _
    _ ≤ _ := mul_le_mul_of_nonneg_right hXp hR0


theorem lwMoment_fxyPow_val {p : ℕ} (hp : Even p) (n : ℕ) (E t : ℝ) (ω : sz.SeqΩ) (x y : Idx d (sz.L n) (sz.W n)) :
    (fxyPowGraph p).pack.val (lwMoment_D sz n E t ω) ![x, y] = ((‖LWf sz n E t ω x y‖ ^ p : ℝ) : ℂ) := by
  rw [LGraph.pack_val, fxyPowGraph_val_eq _ (fun i j => by simp [lwMoment_D, lwSampleData, lwS]) p hp x y,
    lwMoment_fxyVal_D]
  obtain ⟨k, hk⟩ := hp
  have hk2 : p / 2 = k := by omega
  have hk3 : 2 * k = p := by omega
  rw [hk2, lwMoment_pow_conj, hk3]

/-- **The near pairs** (`7_8:61-66`): `𝔼 |f_{xy}|^p ≺ R` for the pairs at block distance `≤ K (log W)²`, from the max bound
and the upgrade `lwExpTerm_prec_integral` (envelope `lwMoment_env` at `fxyPowGraph p`, floor `lwMoment_floor`). -/
theorem lwMoment_prec_near (S : LWMomentCtx sz κ ε 𝔡 𝔠 z t ε₀ C₁ C₂ C₃ Cc Ψ Φ) {p : ℕ} (hp : Even p) (hp0 : 0 < p)
    (K : ℕ) :
    sz.Prec (U := LWMomNear sz K)
      (fun n q _ => ∫ ω, ‖LWf sz n (STflowE z n) (t n) ω q.1.1 q.1.2‖ ^ p ∂sz.seqP)
      (fun n q _ => lwMoment_R sz (STflowE z) t Φ p n q.1.1 q.1.2) := by
  classical
  have hsz := lwMoment_size_tendsto S
  obtain ⟨Kenv, henv⟩ := lwMoment_env S (fxyPowGraph p).pack (fxyPowGraph_normal p)
  have key := lwExpTerm_prec_integral sz (V := LWMomNear sz K)
    (fun n q ω => (((‖LWf sz n (STflowE z n) (t n) ω q.1.1 q.1.2‖ ^ p : ℝ)) : ℂ))
    (fun n q => lwMoment_R sz (STflowE z) t Φ p n q.1.1 q.1.2) (Kenv := Kenv) (Kf := (p : ℝ) * (2 + C₂)) hsz
    (henv.mono fun n h v ω => by
      have := h v.1.1 v.1.2 ω
      rwa [lwMoment_fxyPow_val hp] at this)
    ((lwMoment_floor S p).mono fun n h v => h _ _) (lwMoment_prec_near_pre S hp0 K)
  refine (st6_prec_det_iff sz hsz _ _).2 fun τ hτ => ?_
  filter_upwards [(st6_prec_det_iff sz hsz _ _).1 key τ hτ] with n h v
  have := h v
  rwa [integral_complex_ofReal, Complex.norm_real,
    Real.norm_of_nonneg (integral_nonneg fun ω => by positivity)] at this


/-- **`lem:LW_moment`** (`7_8:72-77`): for every fixed `p ∈ 2ℕ` there is `c > 0` (here `c = 1`) with
`𝔼 |f_{xy}(G)|^p ≺ η_t^{-p} [Ψ_t(0)]^p [Ψ_t(c|a-b|)]^p`.  The pairs at block distance `> K (log W)²` are bounded through the
expansion `lw_localregularX` (`GtoAG`, `(eq:far_ab)`, `lem:Anp`), the others by the max bound `(eq:boundfxyGinf)`; both
upgraded from `≺` to `𝔼` by `lwExpTerm_prec_integral`. -/
theorem lwMoment_holds : ∀ d : ℕ, LWMoment d := by
  intro d hd κ ε 𝔡 hκ hε h𝔡 p hp2 ε₀ C₁ C₂ C₃ Cc
  refine ⟨1, one_pos, ?_⟩
  intro 𝔠 sz z hflow t ht0 ht1 Ψ Φ hassm
  have hp : Even p := even_iff_two_dvd.2 hp2
  let S : LWMomentCtx sz κ ε 𝔡 𝔠 z t ε₀ C₁ C₂ C₃ Cc Ψ Φ := ⟨hd, hκ, hε, h𝔡, hflow, ht0, ht1, hassm⟩
  have hsz := lwMoment_size_tendsto S
  have h𝔠 := (lwMoment_flow_facts S).1.1
  rcases Nat.eq_zero_or_pos p with hp0 | hp0
  · subst hp0
    refine (st6_prec_det_iff sz hsz _ _).2 fun τ hτ => ?_
    filter_upwards [hsz.eventually_ge_atTop 1] with n hN1 v
    have hX : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ τ := Real.one_le_rpow hN1 hτ.le
    simpa using hX
  · set K0 : ℕ := ⌈1 / 𝔠⌉₊ with hK0def
    have hK0 : 1 / 𝔠 ≤ K0 := Nat.le_ceil _
    obtain ⟨outsX, errsX, hX⟩ := lw_localregularX p (ε₀ / 2) (half_pos hassm.1) K0 d (((p : ℝ) * (2 + C₂) + 1) / 𝔠)
    set K : ℕ := ((outsX ++ errsX).map fun r => Fintype.card (r.2.E' ⊕ r.2.I')).sum with hKdef
    have hK : ∀ r ∈ outsX ++ errsX, Fintype.card (r.2.E' ⊕ r.2.I') ≤ K := fun r hr =>
      List.le_sum_of_mem (List.mem_map_of_mem (f := fun r : (ℕ × ℕ) × PGraph (Fin 2) => Fintype.card (r.2.E' ⊕ r.2.I')) hr)
    have hfar := lwMoment_prec_far S hp hp0 hK0 le_rfl hX hK
    have hnear := lwMoment_prec_near S hp hp0 K
    refine (st6_prec_det_iff sz hsz _ _).2 fun τ hτ => ?_
    filter_upwards [(st6_prec_det_iff sz hsz _ _).1 hfar τ hτ, (st6_prec_det_iff sz hsz _ _).1 hnear τ hτ]
      with n h1 h2 q
    by_cases hq : (K : ℝ) * Real.log ((sz.W n : ℕ) : ℝ) ^ 2 < (lwBdist d (sz.L n) (sz.W n) q.1 q.2 : ℝ)
    · exact h1 ⟨q, hq⟩
    · exact h2 ⟨q, le_of_not_gt hq⟩

end NearStoch

end RBM.Gauss.Sizes

/-! ## 11. Compiled nonempty instances of the targets -/

namespace RBM.Graph

/-- **Instance of `lwMoment_val_smul`** at `fxyPowGraph 2` (two black waved edges) and the concrete data `auxGraph_instD`
(`Z_8^3`, `S = lwSmat 3 4 2 (1/2) (1/2)`), `s = 1/2`: the value is multiplied by `(1/2)^2`. -/
example : (fxyPowGraph 2).val { auxGraph_instD with S := (1 / 2 : ℂ) • auxGraph_instD.S } ![0, 1] =
    (1 / 4 : ℂ) * (fxyPowGraph 2).val auxGraph_instD ![0, 1] := by
  have h := lwMoment_val_smul (fxyPowGraph 2) auxGraph_instD (1 / 2) ![0, 1]
  have hn : (fxyPowGraph 2).waved.countP (fun e => !e.col) = 2 := lwEngine_fxy_nWS 2
  rw [h, hn]; norm_num

end RBM.Graph

namespace RBM.Gauss.Sizes

open RBM.Gauss.SizesInst RBM.Graph in
/-- **Instance of `lwMoment_fxy_bridge`** at `sz0` (`d = 3`, `L = 4`, `W = 32`), `n = 0`, `E = 0`, `t = 1/2`, `x = 0`, `y = 1`. -/
example (ω : sz0.SeqΩ) :
    fxyVal (lwSampleData sz0 0 (zt 0 (1 / 2)) (1 / 2) (Matrix.diagonal fun _ => mE 0) (lwS sz0 0 (1 / 2))
      (lwSplus sz0 0 (1 / 2) (mE 0)) ω) 0 1 = ((1 / 2 : ℝ) : ℂ) * LWf sz0 0 0 (1 / 2) ω 0 1 :=
  lwMoment_fxy_bridge sz0 0 0 (1 / 2) (lwSplus sz0 0 (1 / 2) (mE 0)) ω 0 1

end RBM.Gauss.Sizes

namespace RBM.Gauss.LWInst

open RBM RBM.Gauss RBM.Gauss.Sizes RBM.Gauss.SizesInst RBM.Gauss.InductionDefsInst Filter

/-- **Instance of `lwMoment_holds`** (target 3) at the preflight data of `LWPins.lean` (`d = 3`, `sz0`, `z0`, `t ≡ 1/16`,
`Ψ0`, `Φ0`), `p = 2`: the moment bound `𝔼 |f_{xy}|² ≺ (η⁻¹ Φ(0) Φ(c|a-b|))²` for some `c > 0`.  The two hypotheses
`LWInit`, `LWLoop2` (the initial local law and the loop bound: other gates' pins, owed at their registry lines) stay
hypotheses; every deterministic hypothesis of `lwMoment_holds` is discharged by `inst_LWMoment`. -/
theorem lwMoment_inst_moment (hI : LWInit sz0 (STflowE z0) tInst (1 / 20) Ψ0)
    (hL : LWLoop2 sz0 (STflowE z0) tInst Φ0) :
    ∃ c : ℝ, 0 < c ∧
      Prec sz0 (U := fun n => Idx 3 (sz0.L n) (sz0.W n) × Idx 3 (sz0.L n) (sz0.W n))
        (fun n q _ => ∫ ω, ‖LWf sz0 n (STflowE z0 n) (tInst n) ω q.1 q.2‖ ^ 2 ∂(sz0.seqP))
        (fun n q _ => ((etaT (STflowE z0 n) (tInst n))⁻¹ * Φ0 n 0 *
          Φ0 n (c * ((zdistInf 3 (sz0.L n) (STblk sz0 n q.1 - STblk sz0 n q.2) : ℕ) : ℝ))) ^ 2) :=
  inst_LWMoment (lwMoment_holds 3) 2 (dvd_refl 2) hI hL

/-- **Instance of `lwMoment_holds`** at the end time `tEnd` of the preflight flow (`inst_LWMoment_endT`), `p = 2`. -/
theorem lwMoment_inst_moment_endT (hI : LWInit sz0 (STflowE z0) tEnd (1 / 20) Ψ0)
    (hL : LWLoop2 sz0 (STflowE z0) tEnd Φ0) :
    ∃ c : ℝ, 0 < c ∧
      Prec sz0 (U := fun n => Idx 3 (sz0.L n) (sz0.W n) × Idx 3 (sz0.L n) (sz0.W n))
        (fun n q _ => ∫ ω, ‖LWf sz0 n (STflowE z0 n) (tEnd n) ω q.1 q.2‖ ^ 2 ∂(sz0.seqP))
        (fun n q _ => ((etaT (STflowE z0 n) (tEnd n))⁻¹ * Φ0 n 0 *
          Φ0 n (c * ((zdistInf 3 (sz0.L n) (STblk sz0 n q.1 - STblk sz0 n q.2) : ℕ) : ℝ))) ^ 2) :=
  inst_LWMoment_endT (lwMoment_holds 3) 2 (dvd_refl 2) hI hL

end RBM.Gauss.LWInst

end
