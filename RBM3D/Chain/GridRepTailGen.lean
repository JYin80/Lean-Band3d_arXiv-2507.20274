/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Chain.GridDuhamelGen
import RBM3D.Path.DifREP3

/-!
# The two-slot weighted martingale tail over a carrier, part 1

Paper: Lemma 3.6 (`lem:DIfREP`), (3.18) `alu9_STime`.  The carrier-generic form, at loop length `m = 2`
and `Q = ∅`, of the band tail `gridRepWTailQN_holds` (`Path/DifREP3`) over `Step2Gen_UN` / `STeeUMg` /
`martIncNg`.

* §1 the hypothesis classes `GridRepTailGen_Ker`, `GridRepTailGen_Window`, `GridRepTailGen_Inc`,
  `GridRepTailGen_Hyp`; the statement `STGridWTail2gL`.
* §2 the kernel layer (row sums, transfer, near-identity, differences), §3 the proxy `STeeUMg` (quadratic form,
  crude bound, proxy transfer), §4 the `Y` tail (Doob), §5 the `Z` part (switched weights, peeling).
* `Chain/GridRepTailGen2`: the pathwise inclusion, the core, the tail at one size index,
  `stGridWTail2gL_of`, and the band discharge `gridRepTailGen_ker_band`.

The model-free band lemmas of `Path/DifREP3` (`difRep3_sum_*`, `gridTime`, coarse grid, Doob, budgets,
asymptotics) are reused by `open private`; the lemmas that read `uKerQ`, `UN`, `STeeUQM`, `etaT`,
`zt E u` or `pathH` are copied and adapted on the classes `Ker` and `Inc`.  No `BA/*` import, no
spectral hypothesis.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

open private difRep3_sum_norm_prod_le difRep3_norm_double_sum_le difRep3_sum_prod_sub_prod difRep3_tensorKer_one
  difRep3_gridTime_nonneg difRep3_gridTime_le difRep3_gridTime_succ difRep3_gridTime_mono difRep3_K_mul_step
  difRep3_card_label_le difRep3_vc difRep3_vc_ge difRep3_vc_le difRep3_coarse difRep3_memLp_two_of_pow4
  difRep3_doob_tail difRep3_Mee difRep3_VQ difRep3_c3 from RBM3D.Path.DifREP3

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal

noncomputable section

namespace RBM.BA

open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes

/-! ## 1. The hypothesis classes; the statement `STGridWTail2gL` -/

/-- **The kernel class** (`GridRepTailGen_Ker C n`): the semigroup window of `Step2Gen_uKer` (the semigroup conjunct, `Step2Gen_USemigroup`), the row
sums `Σ_b ‖uKer_{v,w}(a,b)‖ ≤ (1 - v)/(1 - w)` (the row-sum conjunct), the near-identity `Σ_b ‖uKer_{s,t}(a,b) - δ_{ab}‖ ≤ |t - s| (1 - t)⁻¹` (the near-identity conjunct)
and the conjugation `uKer(!σ, !σ') = conj uKer(σ, σ')` (the conjugation conjunct; `difRep3_STeeUQM_eq` reads it).  Band: `step2Gen_USemigroup_band`,
`norm_uKer_le`, `difRep3_sum_norm_uKer_sub_one`, `difRep3_conj_uKer`; block Anderson: `BAuKerSemigroup_holds`. -/
def GridRepTailGen_Ker {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (n : ℕ) : Prop :=
  Step2Gen_USemigroup C n ∧
  (∀ (σ σ' : Bool) (v w : ℝ), 0 ≤ v → v ≤ w → w < 1 → ∀ a : Zd d (sz.L n),
    ∑ b, ‖Step2Gen_uKer C n σ σ' v w a b‖ ≤ (1 - v) / (1 - w)) ∧
  (∀ (σ σ' : Bool) (s t : ℝ), 0 ≤ t → t < 1 → ∀ a : Zd d (sz.L n),
    ∑ b, ‖Step2Gen_uKer C n σ σ' s t a b - (1 : Matrix (Zd d (sz.L n)) (Zd d (sz.L n)) ℂ) a b‖ ≤ |t - s| * (1 - t)⁻¹) ∧
  (∀ (σ σ' : Bool) (v w : ℝ), 0 ≤ w → w < 1 → ∀ a b : Zd d (sz.L n),
    Step2Gen_uKer C n (!σ) (!σ') v w a b = starRingEnd ℂ (Step2Gen_uKer C n σ σ' v w a b))

/-- **The window**: `t_n < 1` and `(1 - u)⁻¹ ≤ 16 N` for `0 ≤ u ≤ t_n` (band: `η_u ≥ 1/(16 N)` and `η_u ≤ 1 - u`,
`difRep3_inv_le`; constants). -/
def GridRepTailGen_Window {d : ℕ} {sz : Sizes d} (Cm : Step2Mat sz) (t : ℕ → ℝ) (n : ℕ) : Prop :=
  t n < 1 ∧ ∀ u : ℝ, 0 ≤ u → u ≤ t n → (1 - u)⁻¹ ≤ 16 * ((sz.size n : ℕ) : ℝ)

/-- The `Z` fields (m = 2): `Σ_b κ_b Z_{j,σ,b}` is `ℱ_{j+1}`-measurable with the conditional exponential moments of the real and
imaginary parts bounded by `exp (r² Δ · 2 Re Σ κκ̄ STeeMg_{u_{j+1}}(H_j) / 2)` (band: `difRepTail_condMGF_Z`). -/
def GridRepTailGen_Zfields {d : ℕ} {sz : Sizes d} (Cm : Step2Mat sz) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ)
    (Z : ℕ → (Fin 2 → Bool) → PathΩ sz → (Fin 2 → Zd d (sz.L n)) → ℂ) : Prop :=
  ∀ j, j + 1 ≤ K n → ∀ (σ : Fin 2 → Bool) (κ : (Fin 2 → Zd d (sz.L n)) → ℂ) (r : ℝ),
    Measurable[filt sz (j + 1)] (fun ω => ∑ b, κ b * Z j σ ω b) ∧
    Integrable (fun ω => Real.exp (r * (∑ b, κ b * Z j σ ω b).re)) Cm.Pp ∧
    Integrable (fun ω => Real.exp (r * (∑ b, κ b * Z j σ ω b).im)) Cm.Pp ∧
    Cm.Pp[fun ω => Real.exp (r * (∑ b, κ b * Z j σ ω b).re) | filt sz j] ≤ᵐ[Cm.Pp]
      (fun ω => Real.exp (r ^ 2 * (gridStep s t K n * (2 *
        (∑ b, ∑ b', κ b * starRingEnd ℂ (κ b') *
          STeeMg Cm n (gridTime s t K n (j + 1)) (Cm.Hpath s t K n j ω) σ b b').re)) / 2)) ∧
    Cm.Pp[fun ω => Real.exp (r * (∑ b, κ b * Z j σ ω b).im) | filt sz j] ≤ᵐ[Cm.Pp]
      (fun ω => Real.exp (r ^ 2 * (gridStep s t K n * (2 *
        (∑ b, ∑ b', κ b * starRingEnd ℂ (κ b') *
          STeeMg Cm n (gridTime s t K n (j + 1)) (Cm.Hpath s t K n j ω) σ b b').re)) / 2))

/-- The `Y` fields (m = 2): `Σ_b κ_b Y_{j,σ,b}` is `ℱ_{j+1}`-measurable, conditionally centred, in `L²`, with the second
moment `≤ Δ² · 2000 ((Σ|κ|) C₂)² N⁸`, `C₂ = 6 N (16 N)^4` (band: `AzumaProxyN_YfieldsW`, `P = 2000 (S C₂)² N⁸`;
BA: TL's `TwistGridWTail_Y_fields` has `4 ((Σ|κ|) C₂/2)² · 768 N⁸ ≤` this). -/
def GridRepTailGen_Yfields {d : ℕ} {sz : Sizes d} (Cm : Step2Mat sz) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ)
    (Y : ℕ → (Fin 2 → Bool) → PathΩ sz → (Fin 2 → Zd d (sz.L n)) → ℂ) : Prop :=
  ∀ j, j + 1 ≤ K n → ∀ (σ : Fin 2 → Bool) (κ : (Fin 2 → Zd d (sz.L n)) → ℂ),
    Measurable[filt sz (j + 1)] (fun ω => ∑ b, κ b * Y j σ ω b) ∧
    Cm.Pp[fun ω => (∑ b, κ b * Y j σ ω b).re | filt sz j] =ᵐ[Cm.Pp] 0 ∧
    Cm.Pp[fun ω => (∑ b, κ b * Y j σ ω b).im | filt sz j] =ᵐ[Cm.Pp] 0 ∧
    MemLp (fun ω => (∑ b, κ b * Y j σ ω b).re) 2 Cm.Pp ∧ MemLp (fun ω => (∑ b, κ b * Y j σ ω b).im) 2 Cm.Pp ∧
    ∫ ω, (∑ b, κ b * Y j σ ω b).re ^ 2 ∂Cm.Pp ≤
      gridStep s t K n ^ 2 * (2000 * ((∑ b, ‖κ b‖) * (6 * ((sz.size n : ℕ) : ℝ) * (16 * ((sz.size n : ℕ) : ℝ)) ^ 4)) ^ 2 *
        ((sz.size n : ℕ) : ℝ) ^ 8) ∧
    ∫ ω, (∑ b, κ b * Y j σ ω b).im ^ 2 ∂Cm.Pp ≤
      gridStep s t K n ^ 2 * (2000 * ((∑ b, ‖κ b‖) * (6 * ((sz.size n : ℕ) : ℝ) * (16 * ((sz.size n : ℕ) : ℝ)) ^ 4)) ^ 2 *
        ((sz.size n : ℕ) : ℝ) ^ 8)

/-- **`GridRepTailGen_Inc`** (`m = 2`): the grid walk is a probability space with a Hermitian, adapted walk and a measurable
`STeeMg` (the facts of the band `pathP`, `pathH`); a split `martIncNg = Z + Y` (almost surely) with the `Z` and `Y` fields; the
crude bound and the `u`-shift of `STeeMg` (band: `difRep2_norm_STeeM_le_N`).  Fields are in band
`N`-form (`M_ee = 2 N (16 N)^6`, shift constant `12 · 16^7 N^8`). -/
def GridRepTailGen_Inc {d : ℕ} {sz : Sizes d} (Cm : Step2Mat sz) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) : Prop :=
  IsProbabilityMeasure Cm.Pp ∧
  (∀ j, Measurable[filt sz j] (Cm.Hpath s t K n j) ∧ ∀ ω, (Cm.Hpath s t K n j ω).IsHermitian) ∧
  (∀ (u : ℝ) (σ : Fin 2 → Bool) (b b' : Fin 2 → Zd d (sz.L n)),
    Measurable (fun M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ => STeeMg Cm n u M σ b b')) ∧
  (∃ Z Y : ℕ → (Fin 2 → Bool) → PathΩ sz → (Fin 2 → Zd d (sz.L n)) → ℂ,
    (∀ j σ, ∀ᵐ ω ∂Cm.Pp, ∀ b, martIncNg Cm s t K n j σ ω b = Z j σ ω b + Y j σ ω b) ∧
    GridRepTailGen_Zfields Cm s t K n Z ∧ GridRepTailGen_Yfields Cm s t K n Y) ∧
  (∀ u : ℝ, 0 ≤ u → u ≤ t n → ∀ H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ, H.IsHermitian →
    ∀ (σ : Fin 2 → Bool) (a a' : Fin 2 → Zd d (sz.L n)),
      ‖STeeMg Cm n u H σ a a'‖ ≤ 2 * ((sz.size n : ℕ) : ℝ) * (16 * ((sz.size n : ℕ) : ℝ)) ^ 6) ∧
  (∀ u u' : ℝ, 0 ≤ u → u ≤ u' → u' ≤ t n → ∀ H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ,
    H.IsHermitian → ∀ (σ : Fin 2 → Bool) (a a' : Fin 2 → Zd d (sz.L n)),
      ‖STeeMg Cm n u' H σ a a' - STeeMg Cm n u H σ a a'‖ ≤ 12 * 16 ^ 7 * ((sz.size n : ℕ) : ℝ) ^ 8 * (u' - u))

/-- **`GridRepTailGen_Hyp`**: along the flow datum, eventually in `n`, `Ker`, the window and (for every `K`, `K n ≠ 0`; `CK`
stays before `K`) `Inc`. -/
def GridRepTailGen_Hyp (d : ℕ) (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop)
    (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), Step2Mat sz) (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) : Prop :=
  ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), Flow sz κ ε 𝔠 𝔡 z →
      ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n ≤ t n) → (∀ n, t n ≤ T0 sz z n) →
        sz.SizeTendsto ∧ ∀ᶠ n in atTop, GridRepTailGen_Ker (mk sz z).toFlowFM n ∧
          GridRepTailGen_Window (mk sz z) t n ∧ ∀ K : ℕ → ℕ, K n ≠ 0 → GridRepTailGen_Inc (mk sz z) s t K n

/-- **The statement**: clause 4 of `STGridRepNAtgL d 2`
over a carrier, for the canonical martingale `Σ_{j<k} martIncNg`; the generic form of `GridRepWTailNAt d 2`. -/
def STGridWTail2gL (d : ℕ) (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop)
    (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), Step2Mat sz) (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) : Prop :=
  ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), Flow sz κ ε 𝔠 𝔡 z →
      ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n ≤ t n) → (∀ n, t n ≤ T0 sz z n) →
        ∀ D : ℝ, 0 < D → ∃ CK : ℝ, 0 ≤ CK ∧
          ∀ K : ℕ → ℕ, (∀ n, K n ≠ 0) → (∀ᶠ n in atTop, ((sz.size n : ℕ) : ℝ) ^ CK ≤ K n) →
            ∀ ε' : ℝ, 0 < ε' → ∀ᶠ n in atTop, ∀ i : (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)),
              (mk sz z).Pp {ω | ∃ k, k ≤ K n ∧
                ((sz.size n : ℕ) : ℝ) ^ ε' *
                    (∑ j ∈ Finset.range k, gridStep s t K n *
                      ‖STeeUMg (mk sz z) n (gridTime s t K n j) (gridTime s t K n k)
                        ((mk sz z).Hpath s t K n j ω) i.1 i.2‖ + ((sz.size n : ℕ) : ℝ) ^ (-D)) ^
                        (1 / 2 : ℝ) <
                  ‖∑ j ∈ Finset.range k,
                    Step2Gen_UN (mk sz z).toFlowFM n i.1
                      (gridTime s t K n j) (gridTime s t K n k)
                      (fun b => (∑ j' ∈ Finset.range (j + 1), martIncNg (mk sz z) s t K n j' i.1 ω b) -
                        ∑ j' ∈ Finset.range j, martIncNg (mk sz z) s t K n j' i.1 ω b) i.2‖} ≤
                ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-D))

/-! ## 2. The kernel layer (row sums, transfer, near-identity, differences) from `GridRepTailGen_Ker` -/

section KernelLayer

variable {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (n : ℕ)

/-- The slot-kernel product `∏_i uKer_{σ_i σ_{i+1}}(v, w)(a_i, b_i)` (the kernel of `Step2Gen_UN`). -/
def GridRepTailGen_kp (σ : Fin 2 → Bool) (v w : ℝ) (a b : Fin 2 → Zd d (sz.L n)) : ℂ :=
  ∏ i, Step2Gen_uKer C n (σ i) (σ (finRotate 2 i)) v w (a i) (b i)

/-- One row: `Σ_b |uKer_{v,w}(a,b)| ≤ 16 N` when `(1 - w)⁻¹ ≤ 16 N`, `0 ≤ v ≤ w < 1` (row-sum conjunct). -/
theorem GridRepTailGen_row_le {C : FlowFM sz} {n : ℕ} (hK : GridRepTailGen_Ker C n) {v w : ℝ} (hv : 0 ≤ v)
    (hvw : v ≤ w) (hw : w < 1) {N : ℝ} (hN : (1 - w)⁻¹ ≤ 16 * N) (σ σ' : Bool) (a : Zd d (sz.L n)) :
    ∑ b, ‖Step2Gen_uKer C n σ σ' v w a b‖ ≤ 16 * N := by
  refine (hK.2.1 σ σ' v w hv hvw hw a).trans ?_
  have h1w : 0 < 1 - w := by linarith
  have : (1 - v) / (1 - w) ≤ (1 - w)⁻¹ := by
    rw [div_eq_mul_inv]
    exact mul_le_of_le_one_left (inv_nonneg.2 h1w.le) (by linarith)
  exact this.trans hN

/-- The sum of the kernel rows is at most `(32 N)^2` when `(1 - w)⁻¹ ≤ 16 N`, `0 ≤ v ≤ w < 1`. -/
theorem GridRepTailGen_kp_sum_le {C : FlowFM sz} {n : ℕ} (hK : GridRepTailGen_Ker C n) {v w : ℝ} (hv : 0 ≤ v)
    (hvw : v ≤ w) (hw : w < 1) {N : ℝ} (hN : (1 - w)⁻¹ ≤ 16 * N) (σ : Fin 2 → Bool)
    (a : Fin 2 → Zd d (sz.L n)) :
    ∑ b : Fin 2 → Zd d (sz.L n), ‖GridRepTailGen_kp C n σ v w a b‖ ≤ (32 * N) ^ 2 := by
  have h1w : 0 < 1 - w := by linarith
  have hN0 : 0 ≤ N := by
    have : 0 < (1 - w)⁻¹ := inv_pos.2 h1w
    linarith
  exact difRep3_sum_norm_prod_le (fun i y => Step2Gen_uKer C n (σ i) (σ (finRotate 2 i)) v w (a i) y)
    (R := 32 * N) fun i => (GridRepTailGen_row_le hK hv hvw hw hN _ _ _).trans (by linarith)

/-- Row sums of the difference of two kernels at times `w₁ ≤ w₂`: `≤ 4 (16 N)² (w₂ - w₁)` (the semigroup conjunct gives
`uKer_{u,w₂} - uKer_{u,w₁} = (uKer_{w₁,w₂} - 1) uKer_{u,w₁}`, the near-identity conjunct bounds the first factor, the row-sum conjunct the second). -/
theorem GridRepTailGen_sub_le {C : FlowFM sz} {n : ℕ} (hK : GridRepTailGen_Ker C n) {u w₁ w₂ : ℝ} (hu0 : 0 ≤ u)
    (hu : u ≤ w₁) (hw12 : w₁ ≤ w₂) (hw2 : w₂ < 1) {N : ℝ} (h16₁ : (1 - w₁)⁻¹ ≤ 16 * N)
    (h16₂ : (1 - w₂)⁻¹ ≤ 16 * N) (σ σ' : Bool) (x : Zd d (sz.L n)) :
    ∑ y, ‖Step2Gen_uKer C n σ σ' u w₂ x y - Step2Gen_uKer C n σ σ' u w₁ x y‖ ≤
      4 * (16 * N) ^ 2 * (w₂ - w₁) := by
  have hw1 : w₁ < 1 := hw12.trans_lt hw2
  have hw10 : 0 ≤ w₁ := hu0.trans hu
  have hw20 : 0 ≤ w₂ := hw10.trans hw12
  have hN0 : 0 ≤ 16 * N := (inv_nonneg.2 (by linarith : (0 : ℝ) ≤ 1 - w₁)).trans h16₁
  have hsg := (hK.1 σ σ' u w₁ w₂ hw10 hw1 hw20 hw2).2
  set A := Step2Gen_uKer C n σ σ' w₁ w₂ with hA
  set B := Step2Gen_uKer C n σ σ' u w₁ with hB
  have hentry : ∀ y, Step2Gen_uKer C n σ σ' u w₂ x y - Step2Gen_uKer C n σ σ' u w₁ x y =
      ∑ z, (A x z - (1 : Matrix (Zd d (sz.L n)) (Zd d (sz.L n)) ℂ) x z) * B z y := by
    intro y
    have h : (A * B - B) x y = ∑ z, (A x z - (1 : Matrix (Zd d (sz.L n)) (Zd d (sz.L n)) ℂ) x z) * B z y := by
      rw [show A * B - B = (A - 1) * B by rw [sub_mul, one_mul]]
      simp only [Matrix.mul_apply, Matrix.sub_apply]
    rw [← hsg]
    exact h
  have hrowB : ∀ z, ∑ y, ‖B z y‖ ≤ 16 * N := fun z =>
    GridRepTailGen_row_le hK hu0 hu hw1 h16₁ σ σ' z
  have hrowA : ∑ z, ‖A x z - (1 : Matrix (Zd d (sz.L n)) (Zd d (sz.L n)) ℂ) x z‖ ≤
      (w₂ - w₁) * (16 * N) := by
    refine (hK.2.2.1 σ σ' w₁ w₂ hw20 hw2 x).trans ?_
    rw [abs_of_nonneg (by linarith)]
    exact mul_le_mul_of_nonneg_left h16₂ (by linarith)
  refine le_of_eq_of_le (Finset.sum_congr rfl fun y _ => by rw [hentry y]) ?_
  calc ∑ y, ‖∑ z, (A x z - (1 : Matrix (Zd d (sz.L n)) (Zd d (sz.L n)) ℂ) x z) * B z y‖
      ≤ ∑ y, ∑ z, ‖A x z - (1 : Matrix (Zd d (sz.L n)) (Zd d (sz.L n)) ℂ) x z‖ * ‖B z y‖ := by
        refine Finset.sum_le_sum fun y _ => (norm_sum_le _ _).trans ?_
        exact Finset.sum_le_sum fun z _ => (norm_mul _ _).le
    _ = ∑ z, ‖A x z - (1 : Matrix (Zd d (sz.L n)) (Zd d (sz.L n)) ℂ) x z‖ * ∑ y, ‖B z y‖ := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun z _ => by rw [Finset.mul_sum]
    _ ≤ ∑ z, ‖A x z - (1 : Matrix (Zd d (sz.L n)) (Zd d (sz.L n)) ℂ) x z‖ * (16 * N) :=
        Finset.sum_le_sum fun z _ => mul_le_mul_of_nonneg_left (hrowB z) (norm_nonneg _)
    _ = (∑ z, ‖A x z - (1 : Matrix (Zd d (sz.L n)) (Zd d (sz.L n)) ℂ) x z‖) * (16 * N) := by
        rw [Finset.sum_mul]
    _ ≤ (w₂ - w₁) * (16 * N) * (16 * N) := mul_le_mul_of_nonneg_right hrowA hN0
    _ ≤ 4 * (16 * N) ^ 2 * (w₂ - w₁) := by
        have : 0 ≤ (w₂ - w₁) * (16 * N) ^ 2 := mul_nonneg (by linarith) (by positivity)
        nlinarith

/-- **The transfer identity** (semigroup of `𝒰` from the semigroup conjunct): `Σ_{j<k} 𝒰_{u_j,w} A_j = 𝒰_{v,w} (Σ_{j<k} 𝒰_{u_j,v} A_j)` for
`0 ≤ v, w < 1`, the `u_j` arbitrary (band: `difRep3_UN_transfer` at `Q = ∅`). -/
theorem GridRepTailGen_UN_transfer {C : FlowFM sz} {n : ℕ} (hS : Step2Gen_USemigroup C n)
    (σ : Fin 2 → Bool) {v w : ℝ} (hv0 : 0 ≤ v) (hv1 : v < 1) (hw0 : 0 ≤ w) (hw1 : w < 1) (k : ℕ) (u : ℕ → ℝ)
    (A : ℕ → (Fin 2 → Zd d (sz.L n)) → ℂ) :
    ∑ j ∈ Finset.range k, Step2Gen_UN C n σ (u j) w (A j) =
      Step2Gen_UN C n σ v w (∑ j ∈ Finset.range k, Step2Gen_UN C n σ (u j) v (A j)) := by
  have hsum := map_sum (Step2Gen_UNHom C n σ v w) (fun j => Step2Gen_UN C n σ (u j) v (A j)) (Finset.range k)
  simp only [Step2Gen_UNHom_apply] at hsum
  rw [hsum]
  exact Finset.sum_congr rfl fun j _ =>
    (Step2Gen_UN_comp C n hS σ (u := u j) hv0 hv1 hw0 hw1 (A j)).symm

/-- **The kernel transfer** `𝒰_{v,w} A ≈ A`: for `0 ≤ w < 1` and `|w - v| (1 - w)⁻¹ ≤ ε₀`,
`|(𝒰_{v,w} A)_a - A_a| ≤ 2 ε₀ (1 + ε₀) ‖A‖_∞` (near-identity conjunct; band `difRep3_norm_UN_sub_le`). -/
theorem GridRepTailGen_UN_sub_le {C : FlowFM sz} {n : ℕ} (hK : GridRepTailGen_Ker C n)
    (σ : Fin 2 → Bool) {v w : ℝ} (hw0 : 0 ≤ w) (hw1 : w < 1) {ε₀ : ℝ}
    (hε : |w - v| * (1 - w)⁻¹ ≤ ε₀) (A : (Fin 2 → Zd d (sz.L n)) → ℂ) (a : Fin 2 → Zd d (sz.L n)) :
    ‖Step2Gen_UN C n σ v w A a - A a‖ ≤ ((2 : ℕ) : ℝ) * ε₀ * (1 + ε₀) ^ (2 - 1) * ‖A‖ := by
  have h1w : 0 < 1 - w := by linarith
  have hε0 : 0 ≤ ε₀ := (mul_nonneg (abs_nonneg _) (inv_nonneg.2 h1w.le)).trans hε
  set G : Fin 2 → Zd d (sz.L n) → ℂ := fun i y =>
    Step2Gen_uKer C n (σ i) (σ (finRotate 2 i)) v w (a i) y with hGdef
  set G' : Fin 2 → Zd d (sz.L n) → ℂ := fun i y => (1 : Matrix (Zd d (sz.L n)) (Zd d (sz.L n)) ℂ) (a i) y
    with hG'def
  have hD : ∀ i, ∑ y, ‖G i y - G' i y‖ ≤ ε₀ := fun i =>
    (hK.2.2.1 (σ i) (σ (finRotate 2 i)) v w hw0 hw1 (a i)).trans hε
  have hG'sum : ∀ i, ∑ y, ‖G' i y‖ = 1 := by
    intro i
    simp only [hG'def, Matrix.one_apply]
    rw [Finset.sum_eq_single (a i)]
    · simp
    · intro b _ hb
      simp [Ne.symm hb]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hG' : ∀ i, ∑ y, ‖G' i y‖ ≤ 1 + ε₀ := fun i => by rw [hG'sum i]; linarith
  have hG : ∀ i, ∑ y, ‖G i y‖ ≤ 1 + ε₀ := fun i => by
    calc ∑ y, ‖G i y‖ ≤ ∑ y, (‖G' i y‖ + ‖G i y - G' i y‖) :=
          Finset.sum_le_sum fun y _ => by
            have := norm_add_le (G' i y) (G i y - G' i y)
            simpa using this
      _ = ∑ y, ‖G' i y‖ + ∑ y, ‖G i y - G' i y‖ := Finset.sum_add_distrib
      _ ≤ 1 + ε₀ := by rw [hG'sum i]; exact add_le_add le_rfl (hD i)
  have hmain := difRep3_sum_prod_sub_prod (1 + ε₀) ε₀ (by linarith) hε0 2 G G' hG hG' hD
  have hid : Step2Gen_UN C n σ v w A a - A a =
      ∑ b : Fin 2 → Zd d (sz.L n), (∏ i, G i (b i) - ∏ i, G' i (b i)) * A b := by
    have h1 : tensorKer d (sz.L n) (fun _ => (1 : Matrix (Zd d (sz.L n)) (Zd d (sz.L n)) ℂ)) A a = A a :=
      congrFun (difRep3_tensorKer_one A) a
    have h2 : Step2Gen_UN C n σ v w A a = ∑ b : Fin 2 → Zd d (sz.L n), (∏ i, G i (b i)) * A b := rfl
    have h3 : tensorKer d (sz.L n) (fun _ => (1 : Matrix (Zd d (sz.L n)) (Zd d (sz.L n)) ℂ)) A a =
        ∑ b : Fin 2 → Zd d (sz.L n), (∏ i, G' i (b i)) * A b := rfl
    rw [h2, ← h1, h3, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun b _ => by ring
  rw [hid]
  calc ‖∑ b : Fin 2 → Zd d (sz.L n), (∏ i, G i (b i) - ∏ i, G' i (b i)) * A b‖
      ≤ ∑ b : Fin 2 → Zd d (sz.L n), ‖(∏ i, G i (b i) - ∏ i, G' i (b i)) * A b‖ := norm_sum_le _ _
    _ ≤ ∑ b : Fin 2 → Zd d (sz.L n), ‖∏ i, G i (b i) - ∏ i, G' i (b i)‖ * ‖A‖ := by
        refine Finset.sum_le_sum fun b _ => ?_
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (norm_le_pi_norm A b) (norm_nonneg _)
    _ = (∑ b : Fin 2 → Zd d (sz.L n), ‖∏ i, G i (b i) - ∏ i, G' i (b i)‖) * ‖A‖ := by rw [Finset.sum_mul]
    _ ≤ ((2 : ℕ) : ℝ) * ε₀ * (1 + ε₀) ^ (2 - 1) * ‖A‖ :=
        mul_le_mul_of_nonneg_right hmain (norm_nonneg _)

end KernelLayer

/-! ## 3. The proxy `STeeUMg`: quadratic form, crude bound, proxy transfer -/

section STeeLayer

variable {d : ℕ} {sz : Sizes d} (Cm : Step2Mat sz) (n : ℕ)

/-- **The proxy is the weighted quadratic form**: for `0 ≤ w < 1`,
`STeeUMg_{v,w}(H)_{σ,a} = Σ_{b,b'} κ_b conj(κ_{b'}) STeeMg_v(H)_{σ,b,b'}` with `κ_b = ∏_i uKer_{σ_i σ_{i+1}}(v, w)(a_i, b_i)`
(conjugation conjunct; band `difRep3_STeeUQM_eq`). -/
theorem GridRepTailGen_STeeUMg_eq (hK : GridRepTailGen_Ker Cm.toFlowFM n) (v : ℝ) {w : ℝ} (hw0 : 0 ≤ w)
    (hw1 : w < 1) (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (σ : Fin 2 → Bool)
    (a : Fin 2 → Zd d (sz.L n)) :
    STeeUMg Cm n v w H σ a =
      ∑ b, ∑ b', GridRepTailGen_kp Cm.toFlowFM n σ v w a b *
        starRingEnd ℂ (GridRepTailGen_kp Cm.toFlowFM n σ v w a b') * STeeMg Cm n v H σ b b' := by
  unfold STeeUMg
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun b' _ => ?_
  have h : starRingEnd ℂ (GridRepTailGen_kp Cm.toFlowFM n σ v w a b') =
      ∏ i, Step2Gen_uKer Cm.toFlowFM n (!σ i) (!σ (finRotate 2 i)) v w (a i) (b' i) := by
    unfold GridRepTailGen_kp
    rw [map_prod]
    exact Finset.prod_congr rfl fun i _ => (hK.2.2.2 _ _ v w hw0 hw1 (a i) (b' i)).symm
  rw [h]
  rfl

/-- The same sum in the form of the definition (`!σ` kernel in the second factor). -/
theorem GridRepTailGen_STeeUMg_def (v w : ℝ) (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) :
    STeeUMg Cm n v w H σ a =
      ∑ b, ∑ b', GridRepTailGen_kp Cm.toFlowFM n σ v w a b *
        GridRepTailGen_kp Cm.toFlowFM n (fun i => !σ i) v w a b' * STeeMg Cm n v H σ b b' := rfl

/-- **The crude bound of the proxy**: `|STeeUMg_{u,w}(H)| ≤ V_Q = (32 N)^4 M_ee` for `0 ≤ u ≤ w < 1`,
`(1 - w)⁻¹ ≤ 16 N` and the crude bound of `STeeMg_u`. -/
theorem GridRepTailGen_norm_STeeUMg_le (hK : GridRepTailGen_Ker Cm.toFlowFM n) {u w : ℝ} (hu0 : 0 ≤ u) (huw : u ≤ w)
    (hw1 : w < 1) (hw16 : (1 - w)⁻¹ ≤ 16 * ((sz.size n : ℕ) : ℝ))
    {H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ}
    (hQ1 : ∀ (σ : Fin 2 → Bool) (a a' : Fin 2 → Zd d (sz.L n)),
      ‖STeeMg Cm n u H σ a a'‖ ≤ 2 * ((sz.size n : ℕ) : ℝ) * (16 * ((sz.size n : ℕ) : ℝ)) ^ 6)
    (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) :
    ‖STeeUMg Cm n u w H σ a‖ ≤ difRep3_VQ ((sz.size n : ℕ) : ℝ) 2 := by
  have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
  rw [GridRepTailGen_STeeUMg_def]
  have h := difRep3_norm_double_sum_le (GridRepTailGen_kp Cm.toFlowFM n σ u w a)
    (GridRepTailGen_kp Cm.toFlowFM n (fun i => !σ i) u w a) (fun b b' => STeeMg Cm n u H σ b b')
    (by positivity) (GridRepTailGen_kp_sum_le hK hu0 huw hw1 hw16 σ a)
    (GridRepTailGen_kp_sum_le hK hu0 huw hw1 hw16 (fun i => !σ i) a) fun b b' => hQ1 σ b b'
  refine h.trans (le_of_eq ?_)
  unfold difRep3_VQ difRep3_Mee
  norm_num

/-- **The proxy transfer** `v_p → u_k`: for `0 ≤ u ≤ w₁ ≤ w₂ < 1`, `(1 - w_i)⁻¹ ≤ 16 N` and the crude bound for `STeeMg_u`,
`|STeeUMg_{u,w₂}(H) - STeeUMg_{u,w₁}(H)| ≤ c₃(N, 2) (w₂ - w₁)` (band `difRep3_norm_STeeUQM_sub_le`). -/
theorem GridRepTailGen_norm_STeeUMg_sub_le (hK : GridRepTailGen_Ker Cm.toFlowFM n) {u w₁ w₂ : ℝ} (hu0 : 0 ≤ u)
    (hu : u ≤ w₁) (hw12 : w₁ ≤ w₂) (hw2 : w₂ < 1)
    (h16₁ : (1 - w₁)⁻¹ ≤ 16 * ((sz.size n : ℕ) : ℝ)) (h16₂ : (1 - w₂)⁻¹ ≤ 16 * ((sz.size n : ℕ) : ℝ))
    {H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ}
    (hQ1 : ∀ (σ : Fin 2 → Bool) (a a' : Fin 2 → Zd d (sz.L n)),
      ‖STeeMg Cm n u H σ a a'‖ ≤ 2 * ((sz.size n : ℕ) : ℝ) * (16 * ((sz.size n : ℕ) : ℝ)) ^ 6)
    (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) :
    ‖STeeUMg Cm n u w₂ H σ a - STeeUMg Cm n u w₁ H σ a‖ ≤
      difRep3_c3 ((sz.size n : ℕ) : ℝ) 2 * (w₂ - w₁) := by
  set N : ℝ := ((sz.size n : ℕ) : ℝ) with hN
  have hN1 : (1 : ℝ) ≤ N := by rw [hN]; exact_mod_cast sz.one_le_size n
  have hw1 : w₁ < 1 := hw12.trans_lt hw2
  set Mee : ℝ := 2 * N * (16 * N) ^ 6 with hMee
  have hMee0 : 0 ≤ Mee := by positivity
  have hθ0 : 0 ≤ 4 * (16 * N) ^ 2 * (w₂ - w₁) := mul_nonneg (by positivity) (by linarith)
  set θ : ℝ := 4 * (16 * N) ^ 2 * (w₂ - w₁) with hθ
  set R : ℝ := 32 * N with hR
  have hR0 : 0 ≤ R := by positivity
  set T : (Fin 2 → Zd d (sz.L n)) → (Fin 2 → Zd d (sz.L n)) → ℂ := fun b b' => STeeMg Cm n u H σ b b' with hT
  have hT' : ∀ b b', ‖T b b'‖ ≤ Mee := fun b b' => hQ1 σ b b'
  set P₂ : (Fin 2 → Zd d (sz.L n)) → ℂ := GridRepTailGen_kp Cm.toFlowFM n σ u w₂ a with hP₂
  set P₁ : (Fin 2 → Zd d (sz.L n)) → ℂ := GridRepTailGen_kp Cm.toFlowFM n σ u w₁ a with hP₁
  set Q₂ : (Fin 2 → Zd d (sz.L n)) → ℂ := GridRepTailGen_kp Cm.toFlowFM n (fun i => !σ i) u w₂ a with hQ₂
  set Q₁ : (Fin 2 → Zd d (sz.L n)) → ℂ := GridRepTailGen_kp Cm.toFlowFM n (fun i => !σ i) u w₁ a with hQ₁
  have hS : ∀ (σ' : Fin 2 → Bool) {w : ℝ}, u ≤ w → w < 1 → (1 - w)⁻¹ ≤ 16 * N →
      ∑ b, ‖GridRepTailGen_kp Cm.toFlowFM n σ' u w a b‖ ≤ R ^ 2 := fun σ' w huw hw1 hw16 =>
    GridRepTailGen_kp_sum_le hK hu0 huw hw1 hw16 σ' a
  have hdiff : ∀ (σ' : Fin 2 → Bool),
      ∑ b, ‖GridRepTailGen_kp Cm.toFlowFM n σ' u w₂ a b - GridRepTailGen_kp Cm.toFlowFM n σ' u w₁ a b‖ ≤
        ((2 : ℕ) : ℝ) * θ * R ^ (2 - 1) := fun σ' =>
    difRep3_sum_prod_sub_prod R θ hR0 hθ0 2
      (fun i y => Step2Gen_uKer Cm.toFlowFM n (σ' i) (σ' (finRotate 2 i)) u w₂ (a i) y)
      (fun i y => Step2Gen_uKer Cm.toFlowFM n (σ' i) (σ' (finRotate 2 i)) u w₁ (a i) y)
      (fun i => (GridRepTailGen_row_le hK hu0 (hu.trans hw12) hw2 h16₂ _ _ _).trans (by linarith))
      (fun i => (GridRepTailGen_row_le hK hu0 hu hw1 h16₁ _ _ _).trans (by linarith))
      (fun i => GridRepTailGen_sub_le hK hu0 hu hw12 hw2 h16₁ h16₂ _ _ _)
  have hsplit : STeeUMg Cm n u w₂ H σ a - STeeUMg Cm n u w₁ H σ a =
      ∑ b, ∑ b', (P₂ b - P₁ b) * Q₂ b' * T b b' + ∑ b, ∑ b', P₁ b * (Q₂ b' - Q₁ b') * T b b' := by
    rw [GridRepTailGen_STeeUMg_def, GridRepTailGen_STeeUMg_def, ← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b' _ => ?_
    simp only [hP₂, hP₁, hQ₂, hQ₁, hT]
    ring
  rw [hsplit]
  refine (norm_add_le _ _).trans ?_
  have h1 := difRep3_norm_double_sum_le (fun b => P₂ b - P₁ b) Q₂ T hMee0 (hdiff σ)
    (hS (fun i => !σ i) (hu.trans hw12) hw2 h16₂) hT'
  have h2 := difRep3_norm_double_sum_le P₁ (fun b => Q₂ b - Q₁ b) T hMee0 (hS σ hu hw1 h16₁)
    (hdiff (fun i => !σ i)) hT'
  refine (add_le_add h1 h2).trans (le_of_eq ?_)
  unfold difRep3_c3
  simp only [hθ, hR, hMee]
  norm_num
  ring

end STeeLayer

/-! ## 4. The `Y` part of the tail (Doob, `j`-dependent weights) -/

section YTail

variable {d : ℕ} {sz : Sizes d} (Cm : Step2Mat sz)

/-- **The `Y` part of the tail, weighted**: for deterministic `j`-dependent weights `κ_j` with `Σ_c |κ_j(c)| ≤ S` and any
`P ≥ 2000 (S C₂)² N⁸` (`C₂ = 6 N (16 N)^4`),
`μ (∃ k ≤ K, x ≤ |Σ_{j<k} Σ_c κ_j(c) Y_{j,c}|) ≤ 4 K Δ² P / x²` (the `Y` fields and Doob's inequality for the real and imaginary parts;
band `difRep3_Y_tail`). -/
theorem GridRepTailGen_Y_tail {s t : ℕ → ℝ} {K : ℕ → ℕ} {n : ℕ} (hProb : IsProbabilityMeasure Cm.Pp)
    {Y : ℕ → (Fin 2 → Bool) → PathΩ sz → (Fin 2 → Zd d (sz.L n)) → ℂ}
    (hY : GridRepTailGen_Yfields Cm s t K n Y) (σ : Fin 2 → Bool)
    (κ : ℕ → (Fin 2 → Zd d (sz.L n)) → ℂ) {S : ℝ} (hS0 : 0 ≤ S) (hrow : ∀ j, ∑ c, ‖κ j c‖ ≤ S)
    {P : ℝ} (hP : 2000 * (S * (6 * ((sz.size n : ℕ) : ℝ) * (16 * ((sz.size n : ℕ) : ℝ)) ^ 4)) ^ 2 *
      ((sz.size n : ℕ) : ℝ) ^ 8 ≤ P) {x : ℝ} (hx : 0 < x) :
    Cm.Pp.real {ω | ∃ k, k ≤ K n ∧
        x ≤ ‖∑ j ∈ Finset.range k, ∑ c, κ j c * Y j σ ω c‖} ≤
      4 * ((K n : ℝ) * (gridStep s t K n ^ 2 * P)) / x ^ 2 := by
  set N : ℝ := ((sz.size n : ℕ) : ℝ) with hN
  have hN1 : 1 ≤ N := by rw [hN]; exact_mod_cast sz.one_le_size n
  set c0 : ℝ := 6 * N * (16 * N) ^ 4 with hc0def
  have hc0 : 0 ≤ c0 := by positivity
  have hbound : ∀ j, gridStep s t K n ^ 2 * (2000 * ((∑ c, ‖κ j c‖) * c0) ^ 2 * N ^ 8) ≤
      gridStep s t K n ^ 2 * P := by
    intro j
    have h1 : (∑ c, ‖κ j c‖) * c0 ≤ S * c0 := mul_le_mul_of_nonneg_right (hrow j) hc0
    have h2 : ((∑ c, ‖κ j c‖) * c0) ^ 2 ≤ (S * c0) ^ 2 :=
      pow_le_pow_left₀ (mul_nonneg (Finset.sum_nonneg fun c _ => norm_nonneg _) hc0) h1 2
    refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
    refine le_trans ?_ hP
    gcongr
  have hxs : 0 < x / Real.sqrt 2 := div_pos hx (Real.sqrt_pos.2 (by norm_num))
  have hRe := difRep3_doob_tail Cm.Pp (filt sz)
    (fun j ω => (∑ c, κ j c * Y j σ ω c).re)
    (K n) (gridStep s t K n ^ 2 * P) (x / Real.sqrt 2)
    (fun j hj => Complex.continuous_re.comp_stronglyMeasurable (hY j hj σ (κ j)).1.stronglyMeasurable)
    (fun j hj => (hY j hj σ (κ j)).2.2.2.1)
    (fun j hj => (hY j hj σ (κ j)).2.1)
    (fun j hj => ((hY j hj σ (κ j)).2.2.2.2.2.1).trans (hbound j)) hxs
  have hIm := difRep3_doob_tail Cm.Pp (filt sz)
    (fun j ω => (∑ c, κ j c * Y j σ ω c).im)
    (K n) (gridStep s t K n ^ 2 * P) (x / Real.sqrt 2)
    (fun j hj => Complex.continuous_im.comp_stronglyMeasurable (hY j hj σ (κ j)).1.stronglyMeasurable)
    (fun j hj => (hY j hj σ (κ j)).2.2.2.2.1)
    (fun j hj => (hY j hj σ (κ j)).2.2.1)
    (fun j hj => ((hY j hj σ (κ j)).2.2.2.2.2.2).trans (hbound j)) hxs
  have hsub : {ω | ∃ k, k ≤ K n ∧
      x ≤ ‖∑ j ∈ Finset.range k, ∑ c, κ j c * Y j σ ω c‖} ⊆
      {ω | ∃ k, k ≤ K n ∧ x / Real.sqrt 2 ≤
        |∑ j ∈ Finset.range k, (∑ c, κ j c * Y j σ ω c).re|} ∪
      {ω | ∃ k, k ≤ K n ∧ x / Real.sqrt 2 ≤
        |∑ j ∈ Finset.range k, (∑ c, κ j c * Y j σ ω c).im|} := by
    intro ω hω
    obtain ⟨k, hk, hxk⟩ := hω
    have h1 := Complex.norm_le_sqrt_two_mul_max (∑ j ∈ Finset.range k, ∑ c, κ j c * Y j σ ω c)
    have hs2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
    have h2 : x / Real.sqrt 2 ≤
        max |(∑ j ∈ Finset.range k, ∑ c, κ j c * Y j σ ω c).re|
          |(∑ j ∈ Finset.range k, ∑ c, κ j c * Y j σ ω c).im| := by
      rw [div_le_iff₀ hs2]
      linarith
    rw [Complex.re_sum, Complex.im_sum] at h2
    rcases le_max_iff.1 h2 with h | h
    · exact Or.inl ⟨k, hk, h⟩
    · exact Or.inr ⟨k, hk, h⟩
  calc Cm.Pp.real {ω | ∃ k, k ≤ K n ∧ x ≤ ‖∑ j ∈ Finset.range k, ∑ c, κ j c * Y j σ ω c‖}
      ≤ Cm.Pp.real ({ω | ∃ k, k ≤ K n ∧ x / Real.sqrt 2 ≤
          |∑ j ∈ Finset.range k, (∑ c, κ j c * Y j σ ω c).re|} ∪
        {ω | ∃ k, k ≤ K n ∧ x / Real.sqrt 2 ≤
          |∑ j ∈ Finset.range k, (∑ c, κ j c * Y j σ ω c).im|}) :=
        measureReal_mono hsub
    _ ≤ _ := measureReal_union_le _ _
    _ ≤ (K n : ℝ) * (gridStep s t K n ^ 2 * P) / (x / Real.sqrt 2) ^ 2 +
        (K n : ℝ) * (gridStep s t K n ^ 2 * P) / (x / Real.sqrt 2) ^ 2 := add_le_add hRe hIm
    _ = 4 * ((K n : ℝ) * (gridStep s t K n ^ 2 * P)) / x ^ 2 := by
        rw [div_pow, Real.sq_sqrt (by norm_num)]
        field_simp
        ring

end YTail

/-! ## 5. The `Z` part at a coarse level `v_p` and a label `a'`: the weights, the proxy, the threshold

For a coarse time `v_p` and a label `a'`, `κ^{p,a'}_j := ∏_i uKer_{σ_i σ_{i+1}} (u_j, v_p)(a'_i, ·_i)` if `u_j ≤ v_p` and `0`
otherwise (a deterministic switch), `ζ_j := Σ_b κ_{j,b} Z_{j,b}`, `a_j := 1[u_j ≤ v_p] Δ ‖STeeUMg_{u_j,v_p}(H_j)‖`,
`v_j := max(0, 2 Δ Re Σ κ κ̄ STeeMg_{u_{j+1}}(H_j))` and `e_j := Δ S² · 12 · 16^7 N^8 Δ`. -/

section ZPart

variable {d : ℕ} {sz : Sizes d} (Cm : Step2Mat sz) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ)

/-- The switched weights of the coarse level `vp` at the label `a`. -/
def GridRepTailGen_kap (σ : Fin 2 → Bool) (vp : ℝ) (a : Fin 2 → Zd d (sz.L n)) (j : ℕ) :
    (Fin 2 → Zd d (sz.L n)) → ℂ :=
  fun b => if gridTime s t K n j ≤ vp then
    GridRepTailGen_kp Cm.toFlowFM n σ (gridTime s t K n j) vp a b else 0

/-- The first-chaos increment `ζ_j = Σ_b κ_{j,b} Z_{j,b}` at the coarse level `vp`. -/
def GridRepTailGen_zeta (Z : ℕ → (Fin 2 → Bool) → PathΩ sz → (Fin 2 → Zd d (sz.L n)) → ℂ)
    (σ : Fin 2 → Bool) (vp : ℝ) (a : Fin 2 → Zd d (sz.L n)) (j : ℕ) (ω : PathΩ sz) : ℂ :=
  ∑ b, GridRepTailGen_kap Cm s t K n σ vp a j b * Z j σ ω b

/-- The second-order increment `Σ_b κ_{j,b} Y_{j,b}` at the coarse level `vp`. -/
def GridRepTailGen_yinc (Y : ℕ → (Fin 2 → Bool) → PathΩ sz → (Fin 2 → Zd d (sz.L n)) → ℂ)
    (σ : Fin 2 → Bool) (vp : ℝ) (a : Fin 2 → Zd d (sz.L n)) (j : ℕ) (ω : PathΩ sz) : ℂ :=
  ∑ b, GridRepTailGen_kap Cm s t K n σ vp a j b * Y j σ ω b

/-- The threshold increment `a_j = 1[u_j ≤ vp] Δ ‖STeeUMg_{u_j,vp}(H_j)_{σ,a}‖`. -/
def GridRepTailGen_aSeq (σ : Fin 2 → Bool) (vp : ℝ) (a : Fin 2 → Zd d (sz.L n)) (j : ℕ) (ω : PathΩ sz) : ℝ :=
  if gridTime s t K n j ≤ vp then
    gridStep s t K n * ‖STeeUMg Cm n (gridTime s t K n j) vp (Cm.Hpath s t K n j ω) σ a‖
  else 0

/-- The quadratic variation `Re Σ_{b,b'} κ_b conj κ_{b'} STeeMg_{u_{j+1}}(H_j)_{σ,b,b'}`. -/
def GridRepTailGen_qv (σ : Fin 2 → Bool) (vp : ℝ) (a : Fin 2 → Zd d (sz.L n)) (j : ℕ) (ω : PathΩ sz) : ℝ :=
  (∑ b, ∑ b', GridRepTailGen_kap Cm s t K n σ vp a j b * starRingEnd ℂ (GridRepTailGen_kap Cm s t K n σ vp a j b') *
    STeeMg Cm n (gridTime s t K n (j + 1)) (Cm.Hpath s t K n j ω) σ b b').re

/-- The proxy `v_j = max(0, 2 Δ Re Σ κ κ̄ STeeMg_{u_{j+1}}(H_j))`. -/
def GridRepTailGen_vSeq (σ : Fin 2 → Bool) (vp : ℝ) (a : Fin 2 → Zd d (sz.L n)) (j : ℕ) (ω : PathΩ sz) : ℝ :=
  max 0 (gridStep s t K n * (2 * GridRepTailGen_qv Cm s t K n σ vp a j ω))

/-- The deterministic shift slack `e_j = Δ S² · 12 · 16^7 N^8 Δ`, `S = (32 N)^2`. -/
def GridRepTailGen_eSeq (j : ℕ) : ℝ :=
  gridStep s t K n * (((32 * ((sz.size n : ℕ) : ℝ)) ^ 2) ^ 2 *
    (12 * 16 ^ 7 * ((sz.size n : ℕ) : ℝ) ^ 8 * gridStep s t K n))

variable {Cm s t K n}

/-- The switched weights have `Σ_b |κ_{j,b}| ≤ (32 N)^2`. -/
theorem GridRepTailGen_kap_sum_le (hK : GridRepTailGen_Ker Cm.toFlowFM n) (hs0 : 0 ≤ s n) (hst : s n ≤ t n)
    (σ : Fin 2 → Bool) {vp : ℝ} (hvp1 : vp < 1) (hvp16 : (1 - vp)⁻¹ ≤ 16 * ((sz.size n : ℕ) : ℝ))
    (a : Fin 2 → Zd d (sz.L n)) (j : ℕ) :
    ∑ b, ‖GridRepTailGen_kap Cm s t K n σ vp a j b‖ ≤ (32 * ((sz.size n : ℕ) : ℝ)) ^ 2 := by
  unfold GridRepTailGen_kap
  by_cases h : gridTime s t K n j ≤ vp
  · simp only [h, ↓reduceIte]
    exact GridRepTailGen_kp_sum_le hK (difRep3_gridTime_nonneg hs0 hst j) h hvp1 hvp16 σ a
  · simp only [h, ↓reduceIte, norm_zero, Finset.sum_const_zero]
    positivity

theorem GridRepTailGen_aSeq_nonneg (hst : s n ≤ t n) (σ : Fin 2 → Bool) (vp : ℝ) (a : Fin 2 → Zd d (sz.L n))
    (j : ℕ) (ω : PathΩ sz) : 0 ≤ GridRepTailGen_aSeq Cm s t K n σ vp a j ω := by
  unfold GridRepTailGen_aSeq
  split_ifs
  · exact mul_nonneg (ST_gridStep_nonneg s t K n hst) (norm_nonneg _)
  · exact le_rfl

theorem GridRepTailGen_vSeq_nonneg (σ : Fin 2 → Bool) (vp : ℝ) (a : Fin 2 → Zd d (sz.L n)) (j : ℕ)
    (ω : PathΩ sz) : 0 ≤ GridRepTailGen_vSeq Cm s t K n σ vp a j ω :=
  le_max_left _ _

theorem GridRepTailGen_eSeq_nonneg (hst : s n ≤ t n) (j : ℕ) : 0 ≤ GridRepTailGen_eSeq (sz := sz) s t K n j := by
  have hΔ := ST_gridStep_nonneg s t K n hst
  unfold GridRepTailGen_eSeq
  positivity

/-- **The proxy is dominated by `2 (a_j + e_j)`**: the switched weights give `Σ κ κ̄ STeeMg_{u_j} = STeeUMg_{u_j,vp}`
(`GridRepTailGen_STeeUMg_eq`) and the shift `u_j → u_{j+1}` costs `S² · 12 · 16^7 N^8 Δ` (the shift bound of `GridRepTailGen_Inc`; band `difRep3_vSeq_le`). -/
theorem GridRepTailGen_vSeq_le (hK : GridRepTailGen_Ker Cm.toFlowFM n) (hs0 : 0 ≤ s n) (hst : s n ≤ t n)
    (hK0 : K n ≠ 0) {j : ℕ} (hj : j + 1 ≤ K n)
    (hHerm : ∀ ω, (Cm.Hpath s t K n j ω).IsHermitian)
    (hQ2 : ∀ u u' : ℝ, 0 ≤ u → u ≤ u' → u' ≤ t n →
      ∀ H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ, H.IsHermitian →
        ∀ (σ : Fin 2 → Bool) (a a' : Fin 2 → Zd d (sz.L n)),
          ‖STeeMg Cm n u' H σ a a' - STeeMg Cm n u H σ a a'‖ ≤
            12 * 16 ^ 7 * ((sz.size n : ℕ) : ℝ) ^ 8 * (u' - u))
    (σ : Fin 2 → Bool) {vp : ℝ} (hvp0 : 0 ≤ vp) (hvp1 : vp < 1)
    (hvp16 : (1 - vp)⁻¹ ≤ 16 * ((sz.size n : ℕ) : ℝ)) (a : Fin 2 → Zd d (sz.L n)) (ω : PathΩ sz) :
    GridRepTailGen_vSeq Cm s t K n σ vp a j ω ≤
      2 * (GridRepTailGen_aSeq Cm s t K n σ vp a j ω + GridRepTailGen_eSeq (sz := sz) s t K n j) := by
  have hsucc := difRep3_gridTime_succ s t K n j
  have hΔ := ST_gridStep_nonneg s t K n hst
  have hu0 := difRep3_gridTime_nonneg (K := K) hs0 hst j
  have hu1t : gridTime s t K n (j + 1) ≤ t n := difRep3_gridTime_le hst hK0 hj
  have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
  have he0 := GridRepTailGen_eSeq_nonneg (sz := sz) (K := K) (n := n) hst j
  have ha0 := GridRepTailGen_aSeq_nonneg (Cm := Cm) (K := K) hst σ vp a j ω
  unfold GridRepTailGen_vSeq
  refine max_le (mul_nonneg (by norm_num) (add_nonneg ha0 he0)) ?_
  by_cases h : gridTime s t K n j ≤ vp
  · have hS := GridRepTailGen_kap_sum_le hK hs0 hst σ hvp1 hvp16 a (K := K) j
    have herr0 : 0 ≤ 12 * 16 ^ 7 * ((sz.size n : ℕ) : ℝ) ^ 8 * gridStep s t K n := by positivity
    have hkap : ∀ b, GridRepTailGen_kap Cm s t K n σ vp a j b =
        GridRepTailGen_kp Cm.toFlowFM n σ (gridTime s t K n j) vp a b := by
      intro b; simp only [GridRepTailGen_kap, h, ↓reduceIte]
    have hX : (∑ b, ∑ b', GridRepTailGen_kap Cm s t K n σ vp a j b *
          starRingEnd ℂ (GridRepTailGen_kap Cm s t K n σ vp a j b') *
          STeeMg Cm n (gridTime s t K n (j + 1)) (Cm.Hpath s t K n j ω) σ b b') =
        STeeUMg Cm n (gridTime s t K n j) vp (Cm.Hpath s t K n j ω) σ a +
          ∑ b, ∑ b', GridRepTailGen_kap Cm s t K n σ vp a j b *
            starRingEnd ℂ (GridRepTailGen_kap Cm s t K n σ vp a j b') *
            (STeeMg Cm n (gridTime s t K n (j + 1)) (Cm.Hpath s t K n j ω) σ b b' -
              STeeMg Cm n (gridTime s t K n j) (Cm.Hpath s t K n j ω) σ b b') := by
      rw [GridRepTailGen_STeeUMg_eq Cm n hK (gridTime s t K n j) hvp0 hvp1]
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun b' _ => ?_
      simp only [hkap]
      ring
    have hshift : ∀ b b', ‖STeeMg Cm n (gridTime s t K n (j + 1)) (Cm.Hpath s t K n j ω) σ b b' -
        STeeMg Cm n (gridTime s t K n j) (Cm.Hpath s t K n j ω) σ b b'‖ ≤
        12 * 16 ^ 7 * ((sz.size n : ℕ) : ℝ) ^ 8 * gridStep s t K n := by
      intro b b'
      have := hQ2 (gridTime s t K n j) (gridTime s t K n (j + 1)) hu0 (by rw [hsucc]; linarith) hu1t
        _ (hHerm ω) σ b b'
      have h2 : gridTime s t K n (j + 1) - gridTime s t K n j = gridStep s t K n := by rw [hsucc]; ring
      rwa [h2] at this
    have hdiff : ‖∑ b, ∑ b', GridRepTailGen_kap Cm s t K n σ vp a j b *
          starRingEnd ℂ (GridRepTailGen_kap Cm s t K n σ vp a j b') *
          (STeeMg Cm n (gridTime s t K n (j + 1)) (Cm.Hpath s t K n j ω) σ b b' -
            STeeMg Cm n (gridTime s t K n j) (Cm.Hpath s t K n j ω) σ b b')‖ ≤
        (32 * ((sz.size n : ℕ) : ℝ)) ^ 2 * (32 * ((sz.size n : ℕ) : ℝ)) ^ 2 *
          (12 * 16 ^ 7 * ((sz.size n : ℕ) : ℝ) ^ 8 * gridStep s t K n) :=
      difRep3_norm_double_sum_le _ (fun b' => starRingEnd ℂ (GridRepTailGen_kap Cm s t K n σ vp a j b'))
        _ herr0 hS (by simpa only [Complex.norm_conj] using hS) hshift
    have hqv : GridRepTailGen_qv Cm s t K n σ vp a j ω ≤
        ‖STeeUMg Cm n (gridTime s t K n j) vp (Cm.Hpath s t K n j ω) σ a‖ +
          (32 * ((sz.size n : ℕ) : ℝ)) ^ 2 * (32 * ((sz.size n : ℕ) : ℝ)) ^ 2 *
            (12 * 16 ^ 7 * ((sz.size n : ℕ) : ℝ) ^ 8 * gridStep s t K n) := by
      unfold GridRepTailGen_qv
      rw [hX]
      refine (Complex.re_le_norm _).trans ((norm_add_le _ _).trans ?_)
      exact add_le_add le_rfl hdiff
    unfold GridRepTailGen_aSeq GridRepTailGen_eSeq
    simp only [h, ↓reduceIte]
    calc gridStep s t K n * (2 * GridRepTailGen_qv Cm s t K n σ vp a j ω)
        ≤ gridStep s t K n * (2 * (‖STeeUMg Cm n (gridTime s t K n j) vp (Cm.Hpath s t K n j ω) σ a‖ +
          (32 * ((sz.size n : ℕ) : ℝ)) ^ 2 * (32 * ((sz.size n : ℕ) : ℝ)) ^ 2 *
            (12 * 16 ^ 7 * ((sz.size n : ℕ) : ℝ) ^ 8 * gridStep s t K n))) := by gcongr
      _ = 2 * (gridStep s t K n * ‖STeeUMg Cm n (gridTime s t K n j) vp (Cm.Hpath s t K n j ω) σ a‖ +
          gridStep s t K n * (((32 * ((sz.size n : ℕ) : ℝ)) ^ 2) ^ 2 *
            (12 * 16 ^ 7 * ((sz.size n : ℕ) : ℝ) ^ 8 * gridStep s t K n))) := by ring
  · have hk : ∀ b, GridRepTailGen_kap Cm s t K n σ vp a j b = 0 := fun b => by
      simp only [GridRepTailGen_kap, h, ↓reduceIte]
    have hq : GridRepTailGen_qv Cm s t K n σ vp a j ω = 0 := by
      unfold GridRepTailGen_qv
      simp only [hk, zero_mul, Finset.sum_const_zero, Complex.zero_re]
    rw [hq, mul_zero, mul_zero]
    exact mul_nonneg (by norm_num) (add_nonneg ha0 he0)

/-- `STeeUMg` is measurable in the matrix argument (from the measurability of `STeeMg`). -/
theorem GridRepTailGen_measurable_STeeUMg
    (hM : ∀ (u : ℝ) (σ : Fin 2 → Bool) (b b' : Fin 2 → Zd d (sz.L n)),
      Measurable (fun M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ => STeeMg Cm n u M σ b b'))
    (v w : ℝ) (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) :
    Measurable (fun M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ => STeeUMg Cm n v w M σ a) := by
  unfold STeeUMg
  exact Finset.measurable_sum _ fun b _ => Finset.measurable_sum _ fun b' _ =>
    measurable_const.mul (hM v σ b b')

/-- `ω ↦ a_j(ω)` is `filt sz j`-strongly measurable. -/
theorem GridRepTailGen_aSeq_sm {j : ℕ} (hH : Measurable[filt sz j] (Cm.Hpath s t K n j))
    (hM : ∀ (u : ℝ) (σ : Fin 2 → Bool) (b b' : Fin 2 → Zd d (sz.L n)),
      Measurable (fun M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ => STeeMg Cm n u M σ b b'))
    (σ : Fin 2 → Bool) (vp : ℝ) (a : Fin 2 → Zd d (sz.L n)) :
    StronglyMeasurable[filt sz j] (GridRepTailGen_aSeq Cm s t K n σ vp a j) := by
  by_cases h : gridTime s t K n j ≤ vp
  · have e : GridRepTailGen_aSeq Cm s t K n σ vp a j = fun ω => gridStep s t K n *
        ‖STeeUMg Cm n (gridTime s t K n j) vp (Cm.Hpath s t K n j ω) σ a‖ :=
      funext fun ω => by simp only [GridRepTailGen_aSeq, h, ↓reduceIte]
    rw [e]
    have hS : Measurable[filt sz j] (fun ω => STeeUMg Cm n (gridTime s t K n j) vp (Cm.Hpath s t K n j ω) σ a) :=
      (GridRepTailGen_measurable_STeeUMg hM _ vp σ a).comp hH
    exact hS.stronglyMeasurable.norm.const_mul _
  · have e : GridRepTailGen_aSeq Cm s t K n σ vp a j = fun _ => 0 :=
      funext fun ω => by simp only [GridRepTailGen_aSeq, h, ↓reduceIte]
    rw [e]
    exact stronglyMeasurable_const

/-- `ω ↦ v_j(ω)` is `filt sz j`-strongly measurable. -/
theorem GridRepTailGen_vSeq_sm {j : ℕ} (hH : Measurable[filt sz j] (Cm.Hpath s t K n j))
    (hM : ∀ (u : ℝ) (σ : Fin 2 → Bool) (b b' : Fin 2 → Zd d (sz.L n)),
      Measurable (fun M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ => STeeMg Cm n u M σ b b'))
    (σ : Fin 2 → Bool) (vp : ℝ) (a : Fin 2 → Zd d (sz.L n)) :
    StronglyMeasurable[filt sz j] (GridRepTailGen_vSeq Cm s t K n σ vp a j) := by
  have hf : Measurable (fun M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ =>
      (∑ b, ∑ b', GridRepTailGen_kap Cm s t K n σ vp a j b *
        starRingEnd ℂ (GridRepTailGen_kap Cm s t K n σ vp a j b') *
        STeeMg Cm n (gridTime s t K n (j + 1)) M σ b b').re) :=
    Complex.measurable_re.comp (Finset.measurable_sum _ fun b _ => Finset.measurable_sum _
      fun b' _ => measurable_const.mul (hM _ σ b b'))
  have hqv : Measurable[filt sz j] (GridRepTailGen_qv Cm s t K n σ vp a j) := hf.comp hH
  have : Measurable[filt sz j] (GridRepTailGen_vSeq Cm s t K n σ vp a j) :=
    measurable_const.max ((hqv.const_mul _).const_mul _)
  exact this.stronglyMeasurable

/-- **The mgf facts of `Re ζ_j`, `Im ζ_j` with the proxy `v_j`** (the `Z` fields at the weights `κ_j`; `exp` is monotone and
`v_j = max(0, ·)`; band `difRep3_zeta_mgf`). -/
theorem GridRepTailGen_zeta_mgf {Z : ℕ → (Fin 2 → Bool) → PathΩ sz → (Fin 2 → Zd d (sz.L n)) → ℂ}
    (hZ : GridRepTailGen_Zfields Cm s t K n Z) {j : ℕ} (hj : j + 1 ≤ K n) (σ : Fin 2 → Bool) (vp : ℝ)
    (a : Fin 2 → Zd d (sz.L n)) (r : ℝ) :
    StronglyMeasurable[filt sz (j + 1)] (fun ω => (GridRepTailGen_zeta Cm s t K n Z σ vp a j ω).re) ∧
    StronglyMeasurable[filt sz (j + 1)] (fun ω => (GridRepTailGen_zeta Cm s t K n Z σ vp a j ω).im) ∧
    Integrable (fun ω => Real.exp (r * (GridRepTailGen_zeta Cm s t K n Z σ vp a j ω).re)) Cm.Pp ∧
    Integrable (fun ω => Real.exp (r * (GridRepTailGen_zeta Cm s t K n Z σ vp a j ω).im)) Cm.Pp ∧
    Cm.Pp[fun ω => Real.exp (r * (GridRepTailGen_zeta Cm s t K n Z σ vp a j ω).re) | filt sz j]
      ≤ᵐ[Cm.Pp] (fun ω => Real.exp (r ^ 2 * GridRepTailGen_vSeq Cm s t K n σ vp a j ω / 2)) ∧
    Cm.Pp[fun ω => Real.exp (r * (GridRepTailGen_zeta Cm s t K n Z σ vp a j ω).im) | filt sz j]
      ≤ᵐ[Cm.Pp] (fun ω => Real.exp (r ^ 2 * GridRepTailGen_vSeq Cm s t K n σ vp a j ω / 2)) := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := hZ j hj σ (GridRepTailGen_kap Cm s t K n σ vp a j) r
  have hz : (fun ω => GridRepTailGen_zeta Cm s t K n Z σ vp a j ω) =
      fun ω => ∑ b, GridRepTailGen_kap Cm s t K n σ vp a j b * Z j σ ω b := rfl
  have hle : ∀ ω : PathΩ sz, r ^ 2 * (gridStep s t K n * (2 * GridRepTailGen_qv Cm s t K n σ vp a j ω)) / 2 ≤
      r ^ 2 * GridRepTailGen_vSeq Cm s t K n σ vp a j ω / 2 := by
    intro ω
    unfold GridRepTailGen_vSeq
    have := le_max_right 0 (gridStep s t K n * (2 * GridRepTailGen_qv Cm s t K n σ vp a j ω))
    have h0 : 0 ≤ r ^ 2 := sq_nonneg r
    nlinarith
  refine ⟨Complex.continuous_re.comp_stronglyMeasurable h0.stronglyMeasurable,
    Complex.continuous_im.comp_stronglyMeasurable h0.stronglyMeasurable, h1, h2,
    h3.trans (Eventually.of_forall fun ω => ?_), h4.trans (Eventually.of_forall fun ω => ?_)⟩
  · exact Real.exp_le_exp.2 (hle ω)
  · exact Real.exp_le_exp.2 (hle ω)

/-- The threshold increment is at most `Δ V_Q` (the crude bound `GridRepTailGen_norm_STeeUMg_le`). -/
theorem GridRepTailGen_aSeq_le (hK : GridRepTailGen_Ker Cm.toFlowFM n) (hs0 : 0 ≤ s n) (hst : s n ≤ t n)
    (hK0 : K n ≠ 0) {j : ℕ} (hj : j ≤ K n)
    (hHerm : ∀ ω, (Cm.Hpath s t K n j ω).IsHermitian)
    (hQ1 : ∀ u : ℝ, 0 ≤ u → u ≤ t n → ∀ H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ,
      H.IsHermitian → ∀ (σ : Fin 2 → Bool) (a a' : Fin 2 → Zd d (sz.L n)),
        ‖STeeMg Cm n u H σ a a'‖ ≤ 2 * ((sz.size n : ℕ) : ℝ) * (16 * ((sz.size n : ℕ) : ℝ)) ^ 6)
    (σ : Fin 2 → Bool) {vp : ℝ} (hvp1 : vp < 1) (hvp16 : (1 - vp)⁻¹ ≤ 16 * ((sz.size n : ℕ) : ℝ))
    (a : Fin 2 → Zd d (sz.L n)) (ω : PathΩ sz) :
    GridRepTailGen_aSeq Cm s t K n σ vp a j ω ≤
      gridStep s t K n * difRep3_VQ ((sz.size n : ℕ) : ℝ) 2 := by
  have hΔ := ST_gridStep_nonneg s t K n hst
  have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
  unfold GridRepTailGen_aSeq
  split_ifs with h
  · exact mul_le_mul_of_nonneg_left
      (GridRepTailGen_norm_STeeUMg_le Cm n hK (difRep3_gridTime_nonneg hs0 hst j) h hvp1 hvp16
        (fun σ a a' => hQ1 _ (difRep3_gridTime_nonneg hs0 hst j) (difRep3_gridTime_le hst hK0 hj) _ (hHerm ω) σ a a')
        σ a) hΔ
  · have : 0 ≤ difRep3_VQ ((sz.size n : ℕ) : ℝ) 2 := by unfold difRep3_VQ difRep3_Mee; positivity
    positivity

/-- **The `Z` part of the tail**, through the peeling lemma `difRep2_peel` (`ζ_j`, `a_j`, `v_j`, `e_j`, `c = 2`; band
`difRep3_Z_tail`). -/
theorem GridRepTailGen_Z_tail {Z : ℕ → (Fin 2 → Bool) → PathΩ sz → (Fin 2 → Zd d (sz.L n)) → ℂ}
    (hProb : IsProbabilityMeasure Cm.Pp) (hZ : GridRepTailGen_Zfields Cm s t K n Z)
    (hK : GridRepTailGen_Ker Cm.toFlowFM n) (hs0 : 0 ≤ s n) (hst : s n ≤ t n) (hK0 : K n ≠ 0)
    (hH : ∀ j, Measurable[filt sz j] (Cm.Hpath s t K n j) ∧ ∀ ω, (Cm.Hpath s t K n j ω).IsHermitian)
    (hM : ∀ (u : ℝ) (σ : Fin 2 → Bool) (b b' : Fin 2 → Zd d (sz.L n)),
      Measurable (fun M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ => STeeMg Cm n u M σ b b'))
    (hQ2 : ∀ u u' : ℝ, 0 ≤ u → u ≤ u' → u' ≤ t n →
      ∀ H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ, H.IsHermitian →
        ∀ (σ : Fin 2 → Bool) (a a' : Fin 2 → Zd d (sz.L n)),
          ‖STeeMg Cm n u' H σ a a' - STeeMg Cm n u H σ a a'‖ ≤
            12 * 16 ^ 7 * ((sz.size n : ℕ) : ℝ) ^ 8 * (u' - u))
    (σ : Fin 2 → Bool) {vp : ℝ} (hvp0 : 0 ≤ vp) (hvp1 : vp < 1)
    (hvp16 : (1 - vp)⁻¹ ≤ 16 * ((sz.size n : ℕ) : ℝ)) (a : Fin 2 → Zd d (sz.L n)) (Lmax : ℕ)
    {δ ρ : ℝ} (hδ : 0 < δ) (hρ : 0 ≤ ρ)
    (hesum : ∑ j ∈ Finset.range (K n), GridRepTailGen_eSeq (sz := sz) s t K n j ≤ δ)
    (haL : ∀ ω, ∑ j ∈ Finset.range (K n), GridRepTailGen_aSeq Cm s t K n σ vp a j ω ≤ 2 ^ Lmax * δ) :
    Cm.Pp.real {ω | ∃ k, k ≤ K n ∧
        ρ * (∑ j ∈ Finset.range k, GridRepTailGen_aSeq Cm s t K n σ vp a j ω + δ) ^ (1 / 2 : ℝ) <
          ‖∑ j ∈ Finset.range k, GridRepTailGen_zeta Cm s t K n Z σ vp a j ω‖} ≤
      ((Lmax : ℝ) + 1) * (4 * Real.exp (-ρ ^ 2 / (16 * 2))) := by
  have := RBM.Ind.difRep2_peel Cm.Pp (filt sz) (fun j ω => GridRepTailGen_zeta Cm s t K n Z σ vp a j ω)
    (fun j => GridRepTailGen_aSeq Cm s t K n σ vp a j) (fun j => GridRepTailGen_vSeq Cm s t K n σ vp a j)
    (fun j => GridRepTailGen_eSeq (sz := sz) s t K n j) (K n) Lmax 2 δ ρ (by norm_num) hδ hρ
    (fun j hj => (GridRepTailGen_zeta_mgf hZ hj σ vp a 0).1)
    (fun j hj => (GridRepTailGen_zeta_mgf hZ hj σ vp a 0).2.1)
    (fun j _ => GridRepTailGen_aSeq_sm (hH j).1 hM σ vp a)
    (fun j _ => GridRepTailGen_vSeq_sm (hH j).1 hM σ vp a)
    (fun j _ ω => GridRepTailGen_aSeq_nonneg hst σ vp a j ω)
    (fun j _ ω => GridRepTailGen_vSeq_nonneg σ vp a j ω)
    (fun j _ => GridRepTailGen_eSeq_nonneg hst j)
    (fun j hj ω => GridRepTailGen_vSeq_le hK hs0 hst hK0 hj (hH j).2 hQ2 σ hvp0 hvp1 hvp16 a ω)
    hesum haL
    (fun j hj r => (GridRepTailGen_zeta_mgf hZ hj σ vp a r).2.2.1)
    (fun j hj r => (GridRepTailGen_zeta_mgf hZ hj σ vp a r).2.2.2.1)
    (fun j hj r => (GridRepTailGen_zeta_mgf hZ hj σ vp a r).2.2.2.2.1)
    (fun j hj r => (GridRepTailGen_zeta_mgf hZ hj σ vp a r).2.2.2.2.2)
  exact this

end ZPart

end RBM.BA

end
