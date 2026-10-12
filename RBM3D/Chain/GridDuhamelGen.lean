/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Chain.Step2Gen
import RBM3D.Induction.GridDuhamelN

/-!
# The stopped grid Duhamel and Azuma layer over the carrier (BA-T row T4s1, ticket T2453)

Additive restatement of `Induction/GridDuhamelN.lean` (not edited) over `Step2Mat`, on the one
kernel `Step2Gen_UN` of `Chain/Step2Gen.lean` (supervisor 1152 U-C4: `Ugen = Step2Gen_UN`, no
third kernel).

* **Window.** `Step2Gen_USemigroup C n` (the semigroup law of `(def_Ustz)`, `3_5:116`, for the
  carrier kernel `Step2Gen_uKer`) replaces `3 ≤ L`, `|E| ≤ 2` / `|E n| < 2` of the band statements;
  `step2Gen_USemigroup_band` proves it at `bandFM`.
* **Algebra.** `Step2Gen_UN_add`, `_self`, `_comp`, `Step2Gen_UNHom`, `_duhamel_telescope`.
* **Vocabulary.** `AvecNg`, `martIncNg`, `predIncNg` and the bridges `bandStep2_*`.
* **Pins.** `StoppedDuhamelNg` (G1) and `StoppedAzumaNg` (G3) with `_at` forms and the `∀ n` forms.
* **Bridge.** `bandStep2_Ugen`: `RBM.Ind.Ugen … = Step2Gen_UN (bandFM sz E) …`, the merged
  `Step2Kern_UN_band` read through the definition of `Ugen`.

Band source: `RBM3D/Induction/GridDuhamelN.lean` (ticket T2104).  Private band helpers are reused by
`open private`; the ones that mention `Ugen`, `AvecN`, `martIncN` are copied under the stem
`GridDuhamelGen_`.
-/

set_option linter.style.longLine false

open private GridDuhamelN_gridTime_nonneg GridDuhamelN_gridTime_lt_one GridDuhamelN_azuma_step
  from RBM3D.Induction.GridDuhamelN

noncomputable section

namespace RBM.BA

open MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes
open scoped NNReal ENNReal

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

/-! ### 1. The window of the kernel and the band theorem -/

/-- **The window of the kernel as a carrier fact** (`T2453_USemigroup`): the semigroup law of `(def_Ustz)`
(`3_5:116`) for `Step2Gen_uKer C n` at every charge pair, `0 ≤ v, w < 1`, `u` arbitrary.  It replaces the
band premises `3 ≤ L`, `|E| ≤ 2` of `GridDuhamelN_Ugen_self`/`_comp`. -/
def Step2Gen_USemigroup {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (n : ℕ) : Prop :=
  ∀ (σ σ' : Bool) (u v w : ℝ), 0 ≤ v → v < 1 → 0 ≤ w → w < 1 →
    Step2Gen_uKer C n σ σ' v v = 1 ∧
      Step2Gen_uKer C n σ σ' v w * Step2Gen_uKer C n σ σ' u v = Step2Gen_uKer C n σ σ' u w

/-- The band theorem: `|E n| ≤ 2` gives the semigroup law at `bandFM` (`Step2Kern_uKer_band`, then `ukerMat_self`,
`ukerMat_mul`, with `‖v m(σ) m(σ')‖ = v < 1`, `norm_mul_mSigma_lt_one`). -/
theorem step2Gen_USemigroup_band {d : ℕ} (sz : Sizes d) (E : ℕ → ℝ) (n : ℕ) (hE : |E n| ≤ 2) :
    Step2Gen_USemigroup (bandFM sz E) n := by
  intro σ σ' u v w hv0 hv1 hw0 hw1
  have hv := norm_mul_mSigma_lt_one hE hv0 hv1 σ σ'
  have hw := norm_mul_mSigma_lt_one hE hw0 hw1 σ σ'
  simp only [Step2Kern_uKer_band]
  exact ⟨ukerMat_self d (sz.L n) (sz.lam n) (sz.three_le_L n) hv,
    ukerMat_mul d (sz.L n) (sz.lam n) (sz.three_le_L n) hv hw⟩

/-! ### 2. The kernel `Step2Gen_UN`: additivity, identity and semigroup laws -/

section UNAlgebra

variable {d : ℕ} {sz : Sizes d}

/-- `Step2Gen_UN` is additive (`GridDuhamelN_Ugen_add`). -/
theorem Step2Gen_UN_add (C : FlowFM sz) (n : ℕ) {k : ℕ} (σ : Fin k → Bool) (v w : ℝ)
    (A B : (Fin k → Zd d (sz.L n)) → ℂ) :
    Step2Gen_UN C n σ v w (A + B) = Step2Gen_UN C n σ v w A + Step2Gen_UN C n σ v w B := by
  funext a
  simp only [Step2Gen_UN, Pi.add_apply, mul_add]
  rw [Finset.sum_add_distrib]

/-- `Step2Gen_UN` at equal times is the identity, under the semigroup law (`GridDuhamelN_Ugen_self`). -/
theorem Step2Gen_UN_self (C : FlowFM sz) (n : ℕ) (h : Step2Gen_USemigroup C n) {k : ℕ}
    (σ : Fin k → Bool) {v : ℝ} (hv0 : 0 ≤ v) (hv1 : v < 1) (A : (Fin k → Zd d (sz.L n)) → ℂ) :
    Step2Gen_UN C n σ v v A = A := by
  funext a
  have h1 : ∀ i : Fin k,
      Step2Gen_uKer C n (σ i) (σ (finRotate k i)) v v = 1 := fun i =>
    (h (σ i) (σ (finRotate k i)) 0 v v hv0 hv1 hv0 hv1).1
  simp only [Step2Gen_UN, h1, Matrix.one_apply]
  rw [Finset.sum_eq_single a]
  · simp
  · intro b _ hb
    have : ¬ ∀ i, a i = b i := fun h => hb (funext h).symm
    simp [Fintype.prod_boole, this]
  · intro h; exact absurd (Finset.mem_univ a) h

/-- **Semigroup law** `U_{v,w} ∘ U_{u,v} = U_{u,w}` of `Step2Gen_UN` for `0 ≤ v, w < 1`, slot by slot
from `Step2Gen_USemigroup` (`GridDuhamelN_Ugen_comp`). -/
theorem Step2Gen_UN_comp (C : FlowFM sz) (n : ℕ) (h : Step2Gen_USemigroup C n) {k : ℕ}
    (σ : Fin k → Bool) {u v w : ℝ} (hv0 : 0 ≤ v) (hv1 : v < 1) (hw0 : 0 ≤ w) (hw1 : w < 1)
    (A : (Fin k → Zd d (sz.L n)) → ℂ) :
    Step2Gen_UN C n σ v w (Step2Gen_UN C n σ u v A) = Step2Gen_UN C n σ u w A := by
  funext a
  set ξ : Fin k → ℝ → ℝ → Matrix (Zd d (sz.L n)) (Zd d (sz.L n)) ℂ :=
    fun i s t => Step2Gen_uKer C n (σ i) (σ (finRotate k i)) s t with hξ
  have hm : ∀ (i : Fin k) (x y : Zd d (sz.L n)),
      ∑ c : Zd d (sz.L n), ξ i v w x c * ξ i u v c y = ξ i u w x y := fun i x y => by
    have h' := congrFun (congrFun
      (h (σ i) (σ (finRotate k i)) u v w hv0 hv1 hw0 hw1).2 x) y
    rwa [Matrix.mul_apply] at h'
  calc Step2Gen_UN C n σ v w (Step2Gen_UN C n σ u v A) a
      = ∑ c : Fin k → Zd d (sz.L n), (∏ i, ξ i v w (a i) (c i)) *
          ∑ b : Fin k → Zd d (sz.L n), (∏ i, ξ i u v (c i) (b i)) * A b := rfl
    _ = ∑ c : Fin k → Zd d (sz.L n), ∑ b : Fin k → Zd d (sz.L n),
          (∏ i, ξ i v w (a i) (c i) * ξ i u v (c i) (b i)) * A b := by
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [Finset.prod_mul_distrib]; ring
    _ = ∑ b : Fin k → Zd d (sz.L n), ∑ c : Fin k → Zd d (sz.L n),
          (∏ i, ξ i v w (a i) (c i) * ξ i u v (c i) (b i)) * A b :=
        Finset.sum_comm
    _ = ∑ b : Fin k → Zd d (sz.L n), (∏ i, ξ i u w (a i) (b i)) * A b := by
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [← Finset.sum_mul]
        congr 1
        rw [← Fintype.prod_sum (fun i x => ξ i v w (a i) x * ξ i u v x (b i))]
        exact Finset.prod_congr rfl fun i _ => hm i (a i) (b i)
    _ = Step2Gen_UN C n σ u w A a := rfl

/-- `Step2Gen_UN` bundled as an `AddMonoidHom` (`GridDuhamelN_UgenHom`). -/
def Step2Gen_UNHom (C : FlowFM sz) (n : ℕ) {k : ℕ} (σ : Fin k → Bool) (v w : ℝ) :
    ((Fin k → Zd d (sz.L n)) → ℂ) →+ ((Fin k → Zd d (sz.L n)) → ℂ) :=
  AddMonoidHom.mk' (Step2Gen_UN C n σ v w) (Step2Gen_UN_add C n σ v w)

@[simp] theorem Step2Gen_UNHom_apply (C : FlowFM sz) (n : ℕ) {k : ℕ} (σ : Fin k → Bool)
    (v w : ℝ) (A : (Fin k → Zd d (sz.L n)) → ℂ) :
    Step2Gen_UNHom C n σ v w A = Step2Gen_UN C n σ v w A := rfl

/-- **The algebraic part of `int_K-L_ST` for `Step2Gen_UN`** (`T2453_UNTelescope`;
`GridDuhamelN_Ugen_duhamel_telescope`): `A_m = U_{u_0,u_m} A_0 + Σ_{j<m} U_{u_{j+1},u_m}
(A_{j+1} - U_{u_j,u_{j+1}} A_j)` for `0 ≤ u_j < 1`, `j ≤ m`, under the semigroup law. -/
theorem Step2Gen_UN_duhamel_telescope (C : FlowFM sz) (n : ℕ) (hS : Step2Gen_USemigroup C n) {k : ℕ}
    (σ : Fin k → Bool) (u : ℕ → ℝ) (m : ℕ) (hu0 : ∀ j ≤ m, 0 ≤ u j) (hu1 : ∀ j ≤ m, u j < 1)
    (A : ℕ → ((Fin k → Zd d (sz.L n)) → ℂ)) :
    A m = Step2Gen_UN C n σ (u 0) (u m) (A 0) +
      ∑ j ∈ Finset.range m, Step2Gen_UN C n σ (u (j + 1)) (u m)
        (A (j + 1) - Step2Gen_UN C n σ (u j) (u (j + 1)) (A j)) := by
  set uc : ℕ → ℝ := fun j => u (min j m) with huc
  have hc0 : ∀ j, 0 ≤ uc j := fun j => hu0 _ (min_le_right j m)
  have hc1 : ∀ j, uc j < 1 := fun j => hu1 _ (min_le_right j m)
  have hself : ∀ j, Step2Gen_UNHom C n σ (uc j) (uc j)
      = AddMonoidHom.id ((Fin k → Zd d (sz.L n)) → ℂ) := fun j => by
    apply AddMonoidHom.ext
    intro B
    rw [AddMonoidHom.id_apply, Step2Gen_UNHom_apply]
    exact Step2Gen_UN_self C n hS σ (hc0 j) (hc1 j) B
  have hcomp : ∀ i j l, i ≤ j → j ≤ l →
      (Step2Gen_UNHom C n σ (uc j) (uc l)).comp (Step2Gen_UNHom C n σ (uc i) (uc j))
        = Step2Gen_UNHom C n σ (uc i) (uc l) := fun i j l _ _ => by
    apply AddMonoidHom.ext
    intro B
    rw [AddMonoidHom.comp_apply, Step2Gen_UNHom_apply, Step2Gen_UNHom_apply,
      Step2Gen_UNHom_apply]
    exact Step2Gen_UN_comp C n hS σ (hc0 j) (hc1 j) (hc0 l) (hc1 l) B
  have htel := duhamel_telescope (fun i j => Step2Gen_UNHom C n σ (uc i) (uc j))
    hself hcomp A m
  simp only [Step2Gen_UNHom_apply, huc] at htel
  rw [Nat.zero_min, min_self, sub_eq_iff_eq_add'] at htel
  rw [htel, add_right_inj]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj1 : j + 1 ≤ m := Finset.mem_range.mp hj
  rw [min_eq_left hj1, min_eq_left (Nat.le_of_succ_le hj1)]

end UNAlgebra

/-! ### 3. The bridge `Ugen = Step2Gen_UN` (U-C4) -/

/-- **`Ugen` is `Step2Gen_UN` at `bandFM`** (U-C4, no third kernel): the merged `Step2Kern_UN_band` read through the
definition of `RBM.Ind.Ugen` (`GridDuhamelN:65-67`, `Ugen … = UN … (fun i => mSigma E (σ i))`). -/
theorem bandStep2_Ugen {d : ℕ} (sz : Sizes d) (E : ℕ → ℝ) (n : ℕ) {k : ℕ} (σ : Fin k → Bool) (v w : ℝ)
    (A : (Fin k → Zd d (sz.L n)) → ℂ) :
    RBM.Ind.Ugen d (sz.L n) (sz.lam n) (E n) σ v w A = Step2Gen_UN (bandFM sz E) n σ v w A :=
  (Step2Kern_UN_band sz E n k σ v w A).symm

/-! ### 4. The vocabulary `AvecNg`, `martIncNg`, `predIncNg` -/

section Vocab

variable {d : ℕ} {sz : Sizes d} (Cm : Step2Mat sz)

/-- `A_j = (𝓛 - 𝒦)_{u_j,σ}` of the grid walk, a `k`-tensor (`AvecN`); at `k = 2` it is `STgAg` (`AvecNg_two`). -/
def AvecNg (s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ) {k : ℕ} (σ : Fin k → Bool) (ω : PathΩ sz) :
    (Fin k → Zd d (sz.L n)) → ℂ :=
  fun a => STLKMg Cm n (gridTime s t K n j) (Cm.Hpath s t K n j ω) σ a

/-- `ξ_{j+1} = A_{j+1} - 𝔼[A_{j+1} | F_j]` (`martIncN`). -/
def martIncNg (s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ) {k : ℕ} (σ : Fin k → Bool) (ω : PathΩ sz) :
    (Fin k → Zd d (sz.L n)) → ℂ :=
  fun a => AvecNg Cm s t K n (j + 1) σ ω a -
    MeasureTheory.condExp (filt sz j) Cm.Pp (fun ω' => AvecNg Cm s t K n (j + 1) σ ω' a) ω

/-- `P_j = 𝔼[A_{j+1} | F_j] - U_{u_j,u_{j+1},σ} A_j` (`predIncN`), the kernel being `Step2Gen_UN`. -/
def predIncNg (s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ) {k : ℕ} (σ : Fin k → Bool) (ω : PathΩ sz) :
    (Fin k → Zd d (sz.L n)) → ℂ :=
  fun a => MeasureTheory.condExp (filt sz j) Cm.Pp (fun ω' => AvecNg Cm s t K n (j + 1) σ ω' a) ω -
    Step2Gen_UN Cm.toFlowFM n σ (gridTime s t K n j) (gridTime s t K n (j + 1))
      (AvecNg Cm s t K n j σ ω) a

/-- At `k = 2` the observable is `STgAg` (the observable of `STGridMartAtgL`). -/
theorem AvecNg_two (s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ) (σ : Fin 2 → Bool) (ω : PathΩ sz)
    (a : Fin 2 → Zd d (sz.L n)) : AvecNg Cm s t K n j σ ω a = STgAg Cm s t K n σ a j ω := rfl

end Vocab

section VocabBridge

variable {d : ℕ} (sz : Sizes d) (E : ℕ → ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ)

theorem bandStep2_AvecN {k : ℕ} (σ : Fin k → Bool) (ω : PathΩ sz) :
    RBM.Ind.AvecN sz E s t K n j σ ω = AvecNg (bandStep2Mat sz E) s t K n j σ ω := rfl

theorem bandStep2_martIncN {k : ℕ} (σ : Fin k → Bool) (ω : PathΩ sz) :
    RBM.Ind.martIncN sz E s t K n j σ ω = martIncNg (bandStep2Mat sz E) s t K n j σ ω := rfl

theorem bandStep2_predIncN {k : ℕ} (σ : Fin k → Bool) (ω : PathΩ sz) :
    RBM.Ind.predIncN sz E s t K n j σ ω = predIncNg (bandStep2Mat sz E) s t K n j σ ω := by
  funext a
  unfold RBM.Ind.predIncN predIncNg
  rw [bandStep2_Ugen]
  rfl

end VocabBridge

/-! ### 5. Pin G1 over the carrier -/

section PinG1

variable {d : ℕ} {sz : Sizes d}

/-- **Pin G1 (`int_K-L_ST`, `3_5:134`) over `Step2Mat`** (`T2453_StoppedDuhamelNg`): the stopped grid Duhamel identity,
pathwise.  The `let`s are `AvecNg` (`A`) and the conditional mean (`Y`); the summand is `predIncNg + martIncNg`. -/
def StoppedDuhamelNg (Cm : Step2Mat sz) (s t : ℕ → ℝ) (K : ℕ → ℕ) : Prop :=
  (∀ n, Step2Gen_USemigroup Cm.toFlowFM n) → (∀ n, 0 ≤ s n) → (∀ n, s n ≤ t n) → (∀ n, t n < 1) →
    (∀ n, K n ≠ 0) →
    ∀ (n k : ℕ) (σ : Fin k → Bool) (τ : PathΩ sz → ℕ) (j : ℕ) (ω : PathΩ sz), min j (τ ω) ≤ K n →
      let A : ℕ → PathΩ sz → (Fin k → Zd d (sz.L n)) → ℂ := fun i ω' a =>
        STLKMg Cm n (gridTime s t K n i) (Cm.Hpath s t K n i ω') σ a
      let Y : ℕ → PathΩ sz → (Fin k → Zd d (sz.L n)) → ℂ := fun i ω' a =>
        MeasureTheory.condExp (filt sz i) Cm.Pp (fun ω'' => A (i + 1) ω'' a) ω'
      A (min j (τ ω)) ω =
        Step2Gen_UN Cm.toFlowFM n σ (gridTime s t K n 0) (gridTime s t K n (min j (τ ω))) (A 0 ω) +
          ∑ i ∈ Finset.range (min j (τ ω)),
            Step2Gen_UN Cm.toFlowFM n σ (gridTime s t K n (i + 1)) (gridTime s t K n (min j (τ ω)))
              (fun a : Fin k → Zd d (sz.L n) =>
                (Y i ω a - Step2Gen_UN Cm.toFlowFM n σ (gridTime s t K n i) (gridTime s t K n (i + 1)) (A i ω) a) +
                  (A (i + 1) ω a - Y i ω a))

/-- **Pin G1 at one size index** (DECISIONS §29 (4): hypotheses at `n` only): from `Step2Gen_UN_duhamel_telescope` at
`u = gridTime s t K n`, `A_i = AvecNg … i σ ω`; `A_{i+1} - U A_i = predIncNg_i + martIncNg_i` label by label. -/
theorem stoppedDuhamelNg_at (Cm : Step2Mat sz) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ)
    (hS : Step2Gen_USemigroup Cm.toFlowFM n)
    (hs0 : 0 ≤ s n) (hst : s n ≤ t n) (ht1 : t n < 1) (hK : K n ≠ 0) {k : ℕ}
    (σ : Fin k → Bool) (τ : PathΩ sz → ℕ) (j : ℕ) (ω : PathΩ sz) (hjτ : min j (τ ω) ≤ K n) :
    AvecNg Cm s t K n (min j (τ ω)) σ ω =
      Step2Gen_UN Cm.toFlowFM n σ (gridTime s t K n 0) (gridTime s t K n (min j (τ ω)))
          (AvecNg Cm s t K n 0 σ ω) +
        ∑ i ∈ Finset.range (min j (τ ω)),
          Step2Gen_UN Cm.toFlowFM n σ (gridTime s t K n (i + 1)) (gridTime s t K n (min j (τ ω)))
            (predIncNg Cm s t K n i σ ω + martIncNg Cm s t K n i σ ω) := by
  have h := Step2Gen_UN_duhamel_telescope Cm.toFlowFM n hS σ (gridTime s t K n) (min j (τ ω))
    (fun i _ => GridDuhamelN_gridTime_nonneg s t K n hs0 hst i)
    (fun i hi => GridDuhamelN_gridTime_lt_one s t K n hst hK ht1 (hi.trans hjτ))
    (fun i => AvecNg Cm s t K n i σ ω)
  refine h.trans ?_
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  funext a
  simp only [predIncNg, martIncNg, Pi.add_apply, Pi.sub_apply]
  ring

/-- **Pin G1 proved**: `StoppedDuhamelNg Cm s t K`. -/
theorem stoppedDuhamelNg (Cm : Step2Mat sz) (s t : ℕ → ℝ) (K : ℕ → ℕ) : StoppedDuhamelNg Cm s t K :=
  fun hS hs0 hst ht1 hK n _ σ τ j ω hjτ =>
    stoppedDuhamelNg_at Cm s t K n (hS n) (hs0 n) (hst n) (ht1 n) (hK n) σ τ j ω hjτ

end PinG1

/-! ### 6. Measurability along the walk (copied under the stem) -/

section Measurability

variable {d : ℕ} {sz : Sizes d} (Cm : Step2Mat sz) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ)

/-- The martingale difference `ξ_{j+1}` is `filt sz (j+1)`-strongly measurable as a tensor, given the
`filt sz (j+1)`-measurability of every label of `A_{j+1}` (`GridDuhamelN_stronglyMeasurable_martIncN`). -/
private theorem GridDuhamelGen_stronglyMeasurable_martIncNg {k : ℕ} (σ : Fin k → Bool) (j : ℕ)
    (hmeas : ∀ b : Fin k → Zd d (sz.L n),
      Measurable[filt sz (j + 1)] (fun ω => STLKMg Cm n (gridTime s t K n (j + 1))
        (Cm.Hpath s t K n (j + 1) ω) σ b)) :
    StronglyMeasurable[filt sz (j + 1)] (martIncNg Cm s t K n j σ) := by
  have hme : Measurable[filt sz (j + 1)] (martIncNg Cm s t K n j σ) := by
    refine @measurable_pi_iff _ _ _ (filt sz (j + 1)) _ _ |>.mpr fun a => ?_
    have h1 : Measurable[filt sz (j + 1)] (fun ω => AvecNg Cm s t K n (j + 1) σ ω a) := hmeas a
    have h2 : StronglyMeasurable[filt sz (j + 1)]
        (fun ω => MeasureTheory.condExp (filt sz j) Cm.Pp
          (fun ω' => AvecNg Cm s t K n (j + 1) σ ω' a) ω) :=
      stronglyMeasurable_condExp.mono ((filt sz).mono (Nat.le_succ j))
    exact h1.sub h2.measurable
  exact hme.stronglyMeasurable

/-- `A ↦ (U_{v,w,σ} A)_a` is continuous, so it preserves strong measurability
(`GridDuhamelN_stronglyMeasurable_Ugen_apply`). -/
private theorem GridDuhamelGen_stronglyMeasurable_UN_apply {Ω' : Type*} {m : MeasurableSpace Ω'}
    (C : FlowFM sz) {k : ℕ} (σ : Fin k → Bool) (v w : ℝ)
    {W : Ω' → (Fin k → Zd d (sz.L n)) → ℂ} (hW : StronglyMeasurable[m] W)
    (a : Fin k → Zd d (sz.L n)) :
    StronglyMeasurable[m] (fun ω => Step2Gen_UN C n σ v w (W ω) a) := by
  have hcont : Continuous (fun A : (Fin k → Zd d (sz.L n)) → ℂ => Step2Gen_UN C n σ v w A a) := by
    unfold Step2Gen_UN
    exact continuous_finsetSum _ (fun c _ => continuous_const.mul (continuous_apply c))
  exact hcont.comp_stronglyMeasurable hW

end Measurability

/-! ### 7. Pin G3 over the carrier -/

section PinG3

variable {d : ℕ} {sz : Sizes d}

/-- **Pin G3 (`alu9_STime`-type Azuma) over `Step2Mat`** (`T2453_StoppedAzumaNg`): the premise is the
`filt sz j`-measurability of `AvecNg … j`; the band's five window premises are unused (`GridDuhamelN:553`) and
dropped; the sub-Gaussian bound of the weighted increments is an input.  `ξ` is `martIncNg`. -/
def StoppedAzumaNg (Cm : Step2Mat sz) [IsProbabilityMeasure Cm.Pp]
    (s t : ℕ → ℝ) (K : ℕ → ℕ) : Prop :=
  ∀ (n k : ℕ) (σ : Fin k → Bool),
    (∀ (j : ℕ) (b : Fin k → Zd d (sz.L n)),
      Measurable[filt sz j] (fun ω => STLKMg Cm n (gridTime s t K n j) (Cm.Hpath s t K n j ω) σ b)) →
    ∀ τ : PathΩ sz → ℕ, (∀ j, MeasurableSet[filt sz j] {ω | j < τ ω}) →
    ∀ m : ℕ, m ≤ K n → ∀ (a : Fin k → Zd d (sz.L n)) (c : ℕ → ℝ≥0),
      let ξ : ℕ → PathΩ sz → (Fin k → Zd d (sz.L n)) → ℂ := fun i ω' b =>
        STLKMg Cm n (gridTime s t K n (i + 1)) (Cm.Hpath s t K n (i + 1) ω') σ b -
          MeasureTheory.condExp (filt sz i) Cm.Pp
            (fun ω'' => STLKMg Cm n (gridTime s t K n (i + 1)) (Cm.Hpath s t K n (i + 1) ω'') σ b) ω'
      (∀ j < m,
        HasCondSubgaussianMGF (filt sz j) ((filt sz).le j)
          (fun ω => ({ω' | j < τ ω'}.indicator (fun ω' =>
            Step2Gen_UN Cm.toFlowFM n σ (gridTime s t K n (j + 1)) (gridTime s t K n m) (ξ j ω') a) ω).re)
          (c j) Cm.Pp ∧
        HasCondSubgaussianMGF (filt sz j) ((filt sz).le j)
          (fun ω => ({ω' | j < τ ω'}.indicator (fun ω' =>
            Step2Gen_UN Cm.toFlowFM n σ (gridTime s t K n (j + 1)) (gridTime s t K n m) (ξ j ω') a) ω).im)
          (c j) Cm.Pp) →
      ∀ x : ℝ, 0 ≤ x →
        (Cm.Pp).real {ω | x ≤ ‖∑ j ∈ Finset.range (min m (τ ω)),
            Step2Gen_UN Cm.toFlowFM n σ (gridTime s t K n (j + 1)) (gridTime s t K n m) (ξ j ω) a‖} ≤
          4 * Real.exp (-x ^ 2 / (4 * ∑ j ∈ Finset.range m, (c j : ℝ)))

/-- **Pin G3 at one size index** (DECISIONS §29 (4)): `sum_stopped` rewrites the stopped sum as
`Σ_{j<m} 1{j<τ} (U_{u_{j+1},u_m,σ} ξ_{j+1})_a`, each term is `filt sz (j+1)`-strongly measurable (by the premise
`hmeas`), and `azuma_complex` gives the tail.  No window hypothesis (`GridDuhamelN:553`); the sub-Gaussian
hypothesis is an input. -/
theorem stoppedAzumaNg_at (Cm : Step2Mat sz) [IsProbabilityMeasure Cm.Pp]
    (s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) {k : ℕ} (σ : Fin k → Bool)
    (hmeas : ∀ (j : ℕ) (b : Fin k → Zd d (sz.L n)),
      Measurable[filt sz j] (fun ω => STLKMg Cm n (gridTime s t K n j) (Cm.Hpath s t K n j ω) σ b))
    (τ : PathΩ sz → ℕ) (hτ : ∀ j, MeasurableSet[filt sz j] {ω | j < τ ω})
    (m : ℕ) (a : Fin k → Zd d (sz.L n)) (c : ℕ → ℝ≥0)
    (hsubG : ∀ j < m,
      HasCondSubgaussianMGF (filt sz j) ((filt sz).le j)
        (fun ω => ({ω' | j < τ ω'}.indicator (fun ω' =>
          Step2Gen_UN Cm.toFlowFM n σ (gridTime s t K n (j + 1)) (gridTime s t K n m)
            (martIncNg Cm s t K n j σ ω') a) ω).re) (c j) Cm.Pp ∧
      HasCondSubgaussianMGF (filt sz j) ((filt sz).le j)
        (fun ω => ({ω' | j < τ ω'}.indicator (fun ω' =>
          Step2Gen_UN Cm.toFlowFM n σ (gridTime s t K n (j + 1)) (gridTime s t K n m)
            (martIncNg Cm s t K n j σ ω') a) ω).im) (c j) Cm.Pp)
    {x : ℝ} (hx : 0 ≤ x) :
    (Cm.Pp).real {ω | x ≤ ‖∑ j ∈ Finset.range (min m (τ ω)),
        Step2Gen_UN Cm.toFlowFM n σ (gridTime s t K n (j + 1)) (gridTime s t K n m)
          (martIncNg Cm s t K n j σ ω) a‖} ≤
      4 * Real.exp (-x ^ 2 / (4 * ∑ j ∈ Finset.range m, (c j : ℝ))) := by
  set X : ℕ → PathΩ sz → ℂ := fun j => {ω' | j < τ ω'}.indicator (fun ω' =>
    Step2Gen_UN Cm.toFlowFM n σ (gridTime s t K n (j + 1)) (gridTime s t K n m)
      (martIncNg Cm s t K n j σ ω') a) with hXdef
  have hX : ∀ j < m, StronglyMeasurable[filt sz (j + 1)] (X j) := by
    intro j _
    have hset : MeasurableSet[filt sz (j + 1)] {ω | j < τ ω} :=
      ((filt sz).mono (Nat.le_succ j)) _ (hτ j)
    exact (GridDuhamelGen_stronglyMeasurable_UN_apply n Cm.toFlowFM σ _ _
      (GridDuhamelGen_stronglyMeasurable_martIncNg Cm s t K n σ j (hmeas (j + 1))) a).indicator hset
  have hset : {ω | x ≤ ‖∑ j ∈ Finset.range (min m (τ ω)),
        Step2Gen_UN Cm.toFlowFM n σ (gridTime s t K n (j + 1)) (gridTime s t K n m)
          (martIncNg Cm s t K n j σ ω) a‖}
      = {ω | x ≤ ‖∑ j ∈ Finset.range m, X j ω‖} := by
    ext ω
    rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq]
    have h := sum_stopped (Ω' := PathΩ sz) (M := ℂ)
      (fun i ω' => Step2Gen_UN Cm.toFlowFM n σ (gridTime s t K n i) (gridTime s t K n m)
        (martIncNg Cm s t K n (i - 1) σ ω') a) τ m ω
    simp only [Nat.add_sub_cancel] at h
    rw [h]
  rw [hset]
  exact GridDuhamelN_azuma_step (μ := Cm.Pp) (ℱ := filt sz) hX hsubG hx

/-- **Pin G3 proved**: `StoppedAzumaNg Cm s t K`. -/
theorem stoppedAzumaNg (Cm : Step2Mat sz) [IsProbabilityMeasure Cm.Pp] (s t : ℕ → ℝ) (K : ℕ → ℕ) :
    StoppedAzumaNg Cm s t K :=
  fun n _ σ hmeas τ hτ m _ a c hsubG _ hx =>
    stoppedAzumaNg_at Cm s t K n σ hmeas τ hτ m a c hsubG hx

end PinG3

/-! ### 8. Band corollaries: the merged band pins from targets 5-6 at `bandStep2Mat` -/

section BandCorollaries

variable {d : ℕ} (sz : Sizes d)

/-- Every label of `A_j` at the band carrier is `filt sz j`-measurable: `loopFine` of the walk minus a constant
(`walk_measurable_loopFine`, `pathH_measurable_filt`; `GridDuhamelN_measurable_AvecN`). -/
private theorem GridDuhamelGen_band_measurable (E s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ) {k : ℕ}
    (σ : Fin k → Bool) (b : Fin k → Zd d (sz.L n)) :
    Measurable[filt sz j] (fun ω => STLKMg (bandStep2Mat sz E) n (gridTime s t K n j)
      ((bandStep2Mat sz E).Hpath s t K n j ω) σ b) :=
  ((walk_measurable_loopFine d (sz.L n) (sz.W n) (zt (E n) (gridTime s t K n j)) σ b).comp
    (pathH_measurable_filt sz s t K n j)).sub measurable_const

/-- The band law is a probability measure, in the syntactic form `(bandStep2Mat sz E).Pp` of the pin G3. -/
private instance GridDuhamelGen_bandPp_isProbabilityMeasure (E : ℕ → ℝ) :
    IsProbabilityMeasure (bandStep2Mat sz E).Pp := isProbabilityMeasure_pathP sz

/-- The merged `stoppedDuhamelN_at` from target 5 at `bandStep2Mat` with targets 2-3. -/
example (E : ℕ → ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) (hE : |E n| < 2)
    (hs0 : 0 ≤ s n) (hst : s n ≤ t n) (ht1 : t n < 1) (hK : K n ≠ 0) {k : ℕ}
    (σ : Fin k → Bool) (τ : PathΩ sz → ℕ) (j : ℕ) (ω : PathΩ sz) (hjτ : min j (τ ω) ≤ K n) :
    RBM.Ind.AvecN sz E s t K n (min j (τ ω)) σ ω =
      RBM.Ind.Ugen d (sz.L n) (sz.lam n) (E n) σ (gridTime s t K n 0) (gridTime s t K n (min j (τ ω)))
          (RBM.Ind.AvecN sz E s t K n 0 σ ω) +
        ∑ i ∈ Finset.range (min j (τ ω)),
          RBM.Ind.Ugen d (sz.L n) (sz.lam n) (E n) σ (gridTime s t K n (i + 1))
            (gridTime s t K n (min j (τ ω)))
            (RBM.Ind.predIncN sz E s t K n i σ ω + RBM.Ind.martIncN sz E s t K n i σ ω) := by
  have h := stoppedDuhamelNg_at (bandStep2Mat sz E) s t K n (step2Gen_USemigroup_band sz E n hE.le)
    hs0 hst ht1 hK σ τ j ω hjτ
  simp only [bandStep2_Ugen, bandStep2_predIncN, bandStep2_martIncN, bandStep2_AvecN]
  exact h

/-- The merged pin `StoppedDuhamelN` from the generic pin `StoppedDuhamelNg` at `bandStep2Mat`. -/
example (E s t : ℕ → ℝ) (K : ℕ → ℕ) (h : StoppedDuhamelNg (bandStep2Mat sz E) s t K) :
    RBM.Ind.StoppedDuhamelN sz E s t K := by
  intro hE hs0 hst ht1 hK n k σ τ j ω hjτ
  have h' := h (fun n => step2Gen_USemigroup_band sz E n (hE n).le) hs0 hst ht1 hK n k σ τ j ω hjτ
  simp only [bandStep2_Ugen, bandStep2_predIncN, bandStep2_martIncN, bandStep2_AvecN]
  exact h'

/-- The merged `stoppedAzumaN_at` from target 6 at `bandStep2Mat` (the measurability premise is the band's, the
hypotheses are rewritten along `bandStep2_Ugen`, `bandStep2_martIncN`). -/
example (E s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) {k : ℕ}
    (σ : Fin k → Bool) (τ : PathΩ sz → ℕ) (hτ : ∀ j, MeasurableSet[filt sz j] {ω | j < τ ω})
    (m : ℕ) (a : Fin k → Zd d (sz.L n)) (c : ℕ → ℝ≥0)
    (hsubG : ∀ j < m,
      HasCondSubgaussianMGF (filt sz j) ((filt sz).le j)
        (fun ω => ({ω' | j < τ ω'}.indicator (fun ω' =>
          RBM.Ind.Ugen d (sz.L n) (sz.lam n) (E n) σ (gridTime s t K n (j + 1)) (gridTime s t K n m)
            (RBM.Ind.martIncN sz E s t K n j σ ω') a) ω).re) (c j) (pathP sz) ∧
      HasCondSubgaussianMGF (filt sz j) ((filt sz).le j)
        (fun ω => ({ω' | j < τ ω'}.indicator (fun ω' =>
          RBM.Ind.Ugen d (sz.L n) (sz.lam n) (E n) σ (gridTime s t K n (j + 1)) (gridTime s t K n m)
            (RBM.Ind.martIncN sz E s t K n j σ ω') a) ω).im) (c j) (pathP sz))
    {x : ℝ} (hx : 0 ≤ x) :
    (pathP sz).real {ω | x ≤ ‖∑ j ∈ Finset.range (min m (τ ω)),
        RBM.Ind.Ugen d (sz.L n) (sz.lam n) (E n) σ (gridTime s t K n (j + 1)) (gridTime s t K n m)
          (RBM.Ind.martIncN sz E s t K n j σ ω) a‖} ≤
      4 * Real.exp (-x ^ 2 / (4 * ∑ j ∈ Finset.range m, (c j : ℝ))) := by
  simp only [bandStep2_Ugen, bandStep2_martIncN] at hsubG ⊢
  exact stoppedAzumaNg_at (bandStep2Mat sz E) s t K n σ (fun j b => GridDuhamelGen_band_measurable sz E s t K n j σ b)
    τ hτ m a c hsubG hx

end BandCorollaries

/-! ### 9. Compiled nonempty instances (`d = 3`)

At the non-constant sign vector `σ = (+,+,-)` (`k = 3`).  Algebra of `Step2Gen_UN` at `bandFM sz0 (fun _ => 0)`,
`n = 0` (`d = 3`, `L_0 = 4`, `W_0 = 32`, `lam_0 = 1/64`); pins at `bandStep2Mat sz0 (fun _ => 0)`, `n = 0`,
`s ≡ 1/10`, `t ≡ 1/2`, `K ≡ 4`, `τ ≡ 3`.  The conditional sub-Gaussian input of `stoppedAzumaNg` stays a
hypothesis of the first Azuma example (another gate's pin); the second example (`τ ≡ 0`, `c ≡ 0`) discharges it. -/

section Instances

open RBM.Gauss.SizesInst

private def GridDuhamelGen_instSigma : Fin 3 → Bool := ![true, true, false]

private theorem GridDuhamelGen_instSigma_nonconst :
    GridDuhamelGen_instSigma 0 ≠ GridDuhamelGen_instSigma 2 := by decide

private def GridDuhamelGen_instE : ℕ → ℝ := fun _ => 0
private def GridDuhamelGen_instS : ℕ → ℝ := fun _ => 1 / 10
private def GridDuhamelGen_instT : ℕ → ℝ := fun _ => 1 / 2
private def GridDuhamelGen_instK : ℕ → ℕ := fun _ => 4

private theorem GridDuhamelGen_inst_semigroup :
    ∀ n, Step2Gen_USemigroup (bandStep2Mat sz0 GridDuhamelGen_instE).toFlowFM n := fun n =>
  step2Gen_USemigroup_band sz0 GridDuhamelGen_instE n (by norm_num [GridDuhamelGen_instE])

private theorem GridDuhamelGen_inst_s0 : ∀ n, 0 ≤ GridDuhamelGen_instS n := fun _ => by
  norm_num [GridDuhamelGen_instS]

private theorem GridDuhamelGen_inst_st : ∀ n, GridDuhamelGen_instS n ≤ GridDuhamelGen_instT n :=
  fun _ => by norm_num [GridDuhamelGen_instS, GridDuhamelGen_instT]

private theorem GridDuhamelGen_inst_t1 : ∀ n, GridDuhamelGen_instT n < 1 := fun _ => by
  norm_num [GridDuhamelGen_instT]

private theorem GridDuhamelGen_inst_K : ∀ n, GridDuhamelGen_instK n ≠ 0 := fun _ => by
  norm_num [GridDuhamelGen_instK]

/-- `step2Gen_USemigroup_band` at `sz0`, `E ≡ 0`, `n = 0`. -/
example : Step2Gen_USemigroup (bandFM sz0 GridDuhamelGen_instE) 0 :=
  step2Gen_USemigroup_band sz0 GridDuhamelGen_instE 0 (by norm_num [GridDuhamelGen_instE])

/-- `bandStep2_Ugen` at `sz0`. -/
example (A : (Fin 3 → Zd 3 (sz0.L 0)) → ℂ) :
    RBM.Ind.Ugen 3 (sz0.L 0) (sz0.lam 0) (GridDuhamelGen_instE 0) GridDuhamelGen_instSigma (1 / 4) (1 / 2) A =
      Step2Gen_UN (bandFM sz0 GridDuhamelGen_instE) 0 GridDuhamelGen_instSigma (1 / 4) (1 / 2) A :=
  bandStep2_Ugen sz0 GridDuhamelGen_instE 0 GridDuhamelGen_instSigma (1 / 4) (1 / 2) A

/-- `Step2Gen_UN_add` at `sz0`. -/
example (A B : (Fin 3 → Zd 3 (sz0.L 0)) → ℂ) :
    Step2Gen_UN (bandFM sz0 GridDuhamelGen_instE) 0 GridDuhamelGen_instSigma (1 / 4) (1 / 2) (A + B) =
      Step2Gen_UN (bandFM sz0 GridDuhamelGen_instE) 0 GridDuhamelGen_instSigma (1 / 4) (1 / 2) A +
        Step2Gen_UN (bandFM sz0 GridDuhamelGen_instE) 0 GridDuhamelGen_instSigma (1 / 4) (1 / 2) B :=
  Step2Gen_UN_add (bandFM sz0 GridDuhamelGen_instE) 0 GridDuhamelGen_instSigma (1 / 4) (1 / 2) A B

/-- `Step2Gen_UN_self` at `v = 1/4`. -/
example (A : (Fin 3 → Zd 3 (sz0.L 0)) → ℂ) :
    Step2Gen_UN (bandFM sz0 GridDuhamelGen_instE) 0 GridDuhamelGen_instSigma (1 / 4) (1 / 4) A = A :=
  Step2Gen_UN_self (bandFM sz0 GridDuhamelGen_instE) 0 (GridDuhamelGen_inst_semigroup 0)
    GridDuhamelGen_instSigma (by norm_num) (by norm_num) A

/-- `Step2Gen_UN_comp` at `(u, v, w) = (1/4, 1/2, 3/4)`. -/
example (A : (Fin 3 → Zd 3 (sz0.L 0)) → ℂ) :
    Step2Gen_UN (bandFM sz0 GridDuhamelGen_instE) 0 GridDuhamelGen_instSigma (1 / 2) (3 / 4)
        (Step2Gen_UN (bandFM sz0 GridDuhamelGen_instE) 0 GridDuhamelGen_instSigma (1 / 4) (1 / 2) A) =
      Step2Gen_UN (bandFM sz0 GridDuhamelGen_instE) 0 GridDuhamelGen_instSigma (1 / 4) (3 / 4) A :=
  Step2Gen_UN_comp (bandFM sz0 GridDuhamelGen_instE) 0 (GridDuhamelGen_inst_semigroup 0)
    GridDuhamelGen_instSigma (u := 1 / 4) (by norm_num) (by norm_num) (by norm_num) (by norm_num) A

/-- `Step2Gen_UNHom` applied. -/
example (A : (Fin 3 → Zd 3 (sz0.L 0)) → ℂ) :
    Step2Gen_UNHom (bandFM sz0 GridDuhamelGen_instE) 0 GridDuhamelGen_instSigma (1 / 4) (1 / 2) A =
      Step2Gen_UN (bandFM sz0 GridDuhamelGen_instE) 0 GridDuhamelGen_instSigma (1 / 4) (1 / 2) A :=
  Step2Gen_UNHom_apply (bandFM sz0 GridDuhamelGen_instE) 0 GridDuhamelGen_instSigma (1 / 4) (1 / 2) A

/-- `Step2Gen_UN_duhamel_telescope` at `u j = j / 10`, `m = 3`, for an arbitrary family of `3`-tensors. -/
example (A : ℕ → ((Fin 3 → Zd 3 (sz0.L 0)) → ℂ)) :
    A 3 = Step2Gen_UN (bandFM sz0 GridDuhamelGen_instE) 0 GridDuhamelGen_instSigma
        ((fun j : ℕ => (j : ℝ) / 10) 0) ((fun j : ℕ => (j : ℝ) / 10) 3) (A 0) +
      ∑ j ∈ Finset.range 3, Step2Gen_UN (bandFM sz0 GridDuhamelGen_instE) 0 GridDuhamelGen_instSigma
        ((fun j : ℕ => (j : ℝ) / 10) (j + 1)) ((fun j : ℕ => (j : ℝ) / 10) 3)
        (A (j + 1) - Step2Gen_UN (bandFM sz0 GridDuhamelGen_instE) 0 GridDuhamelGen_instSigma
          ((fun j : ℕ => (j : ℝ) / 10) j) ((fun j : ℕ => (j : ℝ) / 10) (j + 1)) (A j)) :=
  Step2Gen_UN_duhamel_telescope (bandFM sz0 GridDuhamelGen_instE) 0 (GridDuhamelGen_inst_semigroup 0)
    GridDuhamelGen_instSigma (fun j : ℕ => (j : ℝ) / 10) 3
    (fun j _ => by positivity)
    (fun j hj => by
      have : (j : ℝ) ≤ 3 := by exact_mod_cast hj
      change (j : ℝ) / 10 < 1
      linarith) A

/-- `AvecNg_two` at `sz0`. -/
example (j : ℕ) (σ : Fin 2 → Bool) (a : Fin 2 → Zd 3 (sz0.L 0)) (ω : PathΩ sz0) :
    AvecNg (bandStep2Mat sz0 GridDuhamelGen_instE) GridDuhamelGen_instS GridDuhamelGen_instT
        GridDuhamelGen_instK 0 j σ ω a =
      STgAg (bandStep2Mat sz0 GridDuhamelGen_instE) GridDuhamelGen_instS GridDuhamelGen_instT
        GridDuhamelGen_instK 0 σ a j ω :=
  AvecNg_two _ _ _ _ _ _ _ _ _

/-- **`stoppedDuhamelNg_at` at `sz0`**: `τ ≡ 3`, `j = 4` (so `min j τ = 3 ≤ K = 4`), `σ = (+,+,-)`, every
sample `ω`, every hypothesis discharged. -/
example (ω : PathΩ sz0) :
    AvecNg (bandStep2Mat sz0 GridDuhamelGen_instE) GridDuhamelGen_instS GridDuhamelGen_instT
        GridDuhamelGen_instK 0 (min 4 ((fun _ : PathΩ sz0 => 3) ω)) GridDuhamelGen_instSigma ω =
      Step2Gen_UN (bandStep2Mat sz0 GridDuhamelGen_instE).toFlowFM 0 GridDuhamelGen_instSigma
          (gridTime GridDuhamelGen_instS GridDuhamelGen_instT GridDuhamelGen_instK 0 0)
          (gridTime GridDuhamelGen_instS GridDuhamelGen_instT GridDuhamelGen_instK 0
            (min 4 ((fun _ : PathΩ sz0 => 3) ω)))
          (AvecNg (bandStep2Mat sz0 GridDuhamelGen_instE) GridDuhamelGen_instS GridDuhamelGen_instT
            GridDuhamelGen_instK 0 0 GridDuhamelGen_instSigma ω) +
        ∑ i ∈ Finset.range (min 4 ((fun _ : PathΩ sz0 => 3) ω)),
          Step2Gen_UN (bandStep2Mat sz0 GridDuhamelGen_instE).toFlowFM 0 GridDuhamelGen_instSigma
            (gridTime GridDuhamelGen_instS GridDuhamelGen_instT GridDuhamelGen_instK 0 (i + 1))
            (gridTime GridDuhamelGen_instS GridDuhamelGen_instT GridDuhamelGen_instK 0
              (min 4 ((fun _ : PathΩ sz0 => 3) ω)))
            (predIncNg (bandStep2Mat sz0 GridDuhamelGen_instE) GridDuhamelGen_instS
                GridDuhamelGen_instT GridDuhamelGen_instK 0 i GridDuhamelGen_instSigma ω +
              martIncNg (bandStep2Mat sz0 GridDuhamelGen_instE) GridDuhamelGen_instS
                GridDuhamelGen_instT GridDuhamelGen_instK 0 i GridDuhamelGen_instSigma ω) :=
  stoppedDuhamelNg_at (bandStep2Mat sz0 GridDuhamelGen_instE) GridDuhamelGen_instS GridDuhamelGen_instT
    GridDuhamelGen_instK 0 (GridDuhamelGen_inst_semigroup 0) (GridDuhamelGen_inst_s0 0)
    (GridDuhamelGen_inst_st 0) (GridDuhamelGen_inst_t1 0) (GridDuhamelGen_inst_K 0)
    GridDuhamelGen_instSigma (fun _ => 3) 4 ω (by norm_num [GridDuhamelGen_instK])

/-- **`stoppedDuhamelNg` (the `∀ n` pin) at `sz0`**. -/
example : StoppedDuhamelNg (bandStep2Mat sz0 GridDuhamelGen_instE) GridDuhamelGen_instS
    GridDuhamelGen_instT GridDuhamelGen_instK :=
  stoppedDuhamelNg _ _ _ _

/-- **`stoppedAzumaNg_at` at `sz0`**, `τ ≡ 3`, `m = 2`, `σ = (+,+,-)`; the measurability premise is discharged by
`walk_measurable_loopFine` ∘ `pathH_measurable_filt`, the sub-Gaussian input `hsubG` stays a hypothesis. -/
example (a : Fin 3 → Zd 3 (sz0.L 0)) (c : ℕ → ℝ≥0)
    (hsubG : ∀ j < 2,
      HasCondSubgaussianMGF (filt sz0 j) ((filt sz0).le j)
        (fun ω => ({ω' | j < (fun _ : PathΩ sz0 => 3) ω'}.indicator (fun ω' =>
          Step2Gen_UN (bandStep2Mat sz0 GridDuhamelGen_instE).toFlowFM 0 GridDuhamelGen_instSigma
            (gridTime GridDuhamelGen_instS GridDuhamelGen_instT GridDuhamelGen_instK 0 (j + 1))
            (gridTime GridDuhamelGen_instS GridDuhamelGen_instT GridDuhamelGen_instK 0 2)
            (martIncNg (bandStep2Mat sz0 GridDuhamelGen_instE) GridDuhamelGen_instS
              GridDuhamelGen_instT GridDuhamelGen_instK 0 j GridDuhamelGen_instSigma ω') a) ω).re)
        (c j) (bandStep2Mat sz0 GridDuhamelGen_instE).Pp ∧
      HasCondSubgaussianMGF (filt sz0 j) ((filt sz0).le j)
        (fun ω => ({ω' | j < (fun _ : PathΩ sz0 => 3) ω'}.indicator (fun ω' =>
          Step2Gen_UN (bandStep2Mat sz0 GridDuhamelGen_instE).toFlowFM 0 GridDuhamelGen_instSigma
            (gridTime GridDuhamelGen_instS GridDuhamelGen_instT GridDuhamelGen_instK 0 (j + 1))
            (gridTime GridDuhamelGen_instS GridDuhamelGen_instT GridDuhamelGen_instK 0 2)
            (martIncNg (bandStep2Mat sz0 GridDuhamelGen_instE) GridDuhamelGen_instS
              GridDuhamelGen_instT GridDuhamelGen_instK 0 j GridDuhamelGen_instSigma ω') a) ω).im)
        (c j) (bandStep2Mat sz0 GridDuhamelGen_instE).Pp)
    (x : ℝ) (hx : 0 ≤ x) :
    (bandStep2Mat sz0 GridDuhamelGen_instE).Pp.real
        {ω | x ≤ ‖∑ j ∈ Finset.range (min 2 ((fun _ : PathΩ sz0 => 3) ω)),
          Step2Gen_UN (bandStep2Mat sz0 GridDuhamelGen_instE).toFlowFM 0 GridDuhamelGen_instSigma
            (gridTime GridDuhamelGen_instS GridDuhamelGen_instT GridDuhamelGen_instK 0 (j + 1))
            (gridTime GridDuhamelGen_instS GridDuhamelGen_instT GridDuhamelGen_instK 0 2)
            (martIncNg (bandStep2Mat sz0 GridDuhamelGen_instE) GridDuhamelGen_instS
              GridDuhamelGen_instT GridDuhamelGen_instK 0 j GridDuhamelGen_instSigma ω) a‖} ≤
      4 * Real.exp (-x ^ 2 / (4 * ∑ j ∈ Finset.range 2, (c j : ℝ))) := by
  exact stoppedAzumaNg_at (bandStep2Mat sz0 GridDuhamelGen_instE) GridDuhamelGen_instS
    GridDuhamelGen_instT GridDuhamelGen_instK 0 GridDuhamelGen_instSigma
    (fun j b => GridDuhamelGen_band_measurable sz0 GridDuhamelGen_instE GridDuhamelGen_instS
      GridDuhamelGen_instT GridDuhamelGen_instK 0 j GridDuhamelGen_instSigma b)
    (fun _ => 3) (fun _ => MeasurableSet.const _) 2 a c hsubG hx

/-- Fully discharged companion at `τ ≡ 0`, `c ≡ 0` (the stopped increments vanish, so the sub-Gaussian
hypothesis holds by `HasCondSubgaussianMGF.fun_zero`), through the `∀ n` pin `stoppedAzumaNg`. -/
example (a : Fin 3 → Zd 3 (sz0.L 0)) (x : ℝ) (hx : 0 ≤ x) :
    (bandStep2Mat sz0 GridDuhamelGen_instE).Pp.real
        {ω | x ≤ ‖∑ j ∈ Finset.range (min 2 ((fun _ : PathΩ sz0 => 0) ω)),
          Step2Gen_UN (bandStep2Mat sz0 GridDuhamelGen_instE).toFlowFM 0 GridDuhamelGen_instSigma
            (gridTime GridDuhamelGen_instS GridDuhamelGen_instT GridDuhamelGen_instK 0 (j + 1))
            (gridTime GridDuhamelGen_instS GridDuhamelGen_instT GridDuhamelGen_instK 0 2)
            (martIncNg (bandStep2Mat sz0 GridDuhamelGen_instE) GridDuhamelGen_instS
              GridDuhamelGen_instT GridDuhamelGen_instK 0 j GridDuhamelGen_instSigma ω) a‖} ≤
      4 * Real.exp (-x ^ 2 / (4 * ∑ j ∈ Finset.range 2, (((fun _ => 0 : ℕ → ℝ≥0) j : ℝ≥0) : ℝ))) := by
  refine stoppedAzumaNg_at (bandStep2Mat sz0 GridDuhamelGen_instE) GridDuhamelGen_instS
    GridDuhamelGen_instT GridDuhamelGen_instK 0 GridDuhamelGen_instSigma
    (fun j b => GridDuhamelGen_band_measurable sz0 GridDuhamelGen_instE GridDuhamelGen_instS
      GridDuhamelGen_instT GridDuhamelGen_instK 0 j GridDuhamelGen_instSigma b)
    (fun _ => 0) (fun _ => MeasurableSet.const _) 2 a (fun _ => 0) ?_ hx
  intro j _
  have h0 : ∀ f : PathΩ sz0 → ℂ,
      (fun ω => ({ω' | j < (fun _ : PathΩ sz0 => 0) ω'}.indicator f ω).re) = fun _ => (0 : ℝ) := by
    intro f; funext ω; simp
  have h1 : ∀ f : PathΩ sz0 → ℂ,
      (fun ω => ({ω' | j < (fun _ : PathΩ sz0 => 0) ω'}.indicator f ω).im) = fun _ => (0 : ℝ) := by
    intro f; funext ω; simp
  refine ⟨?_, ?_⟩
  · rw [h0]; exact HasCondSubgaussianMGF.fun_zero
  · rw [h1]; exact HasCondSubgaussianMGF.fun_zero

/-- `stoppedAzumaNg` (the `∀ n` pin) at `sz0`, used as a term. -/
example : StoppedAzumaNg (bandStep2Mat sz0 GridDuhamelGen_instE) GridDuhamelGen_instS
    GridDuhamelGen_instT GridDuhamelGen_instK :=
  stoppedAzumaNg _ _ _ _

end Instances

end RBM.BA

end
