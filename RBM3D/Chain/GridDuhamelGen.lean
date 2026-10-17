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

open private GridDuhamelN_gridTime_nonneg GridDuhamelN_gridTime_lt_one
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

end Vocab

/-! ### 5. Pin G1 over the carrier -/

section PinG1

variable {d : ℕ} {sz : Sizes d}

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

end PinG1

/-! ### 6. Measurability along the walk (copied under the stem) -/

/-! ### 7. Pin G3 over the carrier -/

/-! ### 8. Band corollaries: the merged band pins from targets 5-6 at `bandStep2Mat` -/

/-! ### 9. Compiled nonempty instances (`d = 3`)

At the non-constant sign vector `σ = (+,+,-)` (`k = 3`).  Algebra of `Step2Gen_UN` at `bandFM sz0 (fun _ => 0)`,
`n = 0` (`d = 3`, `L_0 = 4`, `W_0 = 32`, `lam_0 = 1/64`); pins at `bandStep2Mat sz0 (fun _ => 0)`, `n = 0`,
`s ≡ 1/10`, `t ≡ 1/2`, `K ≡ 4`, `τ ≡ 3`.  The conditional sub-Gaussian input of `stoppedAzumaNg` stays a
hypothesis of the first Azuma example (another gate's pin); the second example (`τ ≡ 0`, `c ≡ 0`) discharges it. -/

end RBM.BA

end
