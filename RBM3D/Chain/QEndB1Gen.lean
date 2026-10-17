/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Induction.QEndB1
import RBM3D.Chain.QEndGridGen
import RBM3D.Chain.NQEndFlowGen
import RBM3D.Chain.NQLinGen
import RBM3D.Chain.GridGoodGen
import RBM3D.Chain.DecayGen

/-!
# The alternating per-time round over the carrier family (U3s3c, ticket T2498)

Generic form of `Induction/QEndB1.lean` (`STXiRoundPT''`, `STOeqQtRoundPT''`, `stOeqQtRoundPT''_holds`; not edited) over a carrier family
`(law, Flow, mkM, T0)`, namespace `RBM.BA`, no `BA/*` import.  Paper: arXiv:2507.20274, `lem:STOeq_Qt` (`3_5:1362-1378`), its proof, the
alternating case `(eq:alternatecase1)` `3_5:1676-1714`; the non-alternating signs are `lem:STOeq_NQ` (`3_5:1679`).  Composition, no new mathematics.

* **Target 11** `STXiRoundPTgL''`, `STOeqQtRoundPTgL''` (= `T2498_XiRoundPTgL''`, `T2498_OeqQtRoundPTgL''`, binding) and their band bridges
  (`bandFM_STIngR`).
* **Target 12** `stOeqQtRoundPTgL''_of` (conclusion `T2498_OeqQtRoundPTgL''`, binding): the initial loops (`QEndB1Gen_initQ`, `startLevelQNg` and the far
  decay `stDecayLoopUgL_of_step2`), the alternating endpoint at one section (`QEndB1Gen_core`, `altGridEndQNg` of row b, the good events
  `gridGoodNgL_of`, `nqLinGoodgL_of`, `altYGridNg`), the non-alternating half (`stOeqNQPTgL''_of`, U3s2c) and the collapsed section
  (`QEndB1Gen_section`).  The hypotheses are the family-premise table of the ticket: the 22 premises of `stOeqNQPTgL''_of`, D1
  `QProxyG_KerEK4Fam`, the `Θ`-decay class with `∃ C₆` after `κ` (Amend 1) and `B45Gen_Facts`.
* **Target 13** the band re-derivation `stOeqQtRoundPTgL''_band` (every `d ≥ 3`; no open hypothesis), `stOeqQtRoundPT''_holds_of_gen`, and compiled
  nonempty instances at `d = 3` (namespace `RBM.BA.QEndB1GenCheck`).

The model-free private helpers of `QEndB1` (§0-§1, §5') and of `NQEndFlowGen`, `GridGoodGen` are used by `open private`.
-/

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

open private altQFlow_conStInd_exp_mono altQFlow_level_le altQFlow_phi_nonneg altQFlow_phiC_ge altQFlow_phiC_one_le altQFlow_K altQFlow_K_ne_zero
  altQFlow_K_low altQFlow_K_up altQFlow_K_card altQFlow_union2 altQFlow_two_pow_le altQFlow_bootRHS_one_le altQFlow_bootRHS_two_le_one
  altQFlow0_Ylow_le_bootRHS altQFlow_W_le_size altQFlow_Zd_le_size altQFlow_card_Zd from RBM3D.Induction.QEndB1

open private NQEndFlowGen_prec_of_le_right NQEndFlowGen_hQ NQEndFlowGen_restrict_pair NQEndFlowGen_step2_restrict NQEndFlowGen_isProb
  from RBM3D.Chain.NQEndFlowGen

open private GridGoodGen_precL_whp GridGoodGen_one_le_STXiLg from RBM3D.Chain.GridGoodGen

open private nqEnd_rangeCond_mono from RBM3D.Induction.NQEndLin

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal

noncomputable section

namespace RBM.BA

open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes
open RBM.Ind (QProxyG_KerEK4 QProxyG_KerEK4Fam altYGridNg startLevelQNg qProxy4C qProxy4C_pos qProxyG_kerEK4_band_at)

/-! ## 1. Target 11: the round texts -/

section Texts

/-- **Target 11, `STXiRoundPTgL''`** (= `T2498_XiRoundPTgL''`, binding; band `STXiRoundPT''`, `Induction/QEndB1.lean:100`): the per-time round of
`(am;asoi222)` at `n_ ≥ 2` over a flow carrier: `Prec sz` is `PrecL sz μ`, `PrecPT sz` is `PrecPTL sz μ`, `STXiL`/`STXiLK` are U3s1's
`STXiLg`/`STXiLKg`; `sz.Bctl` and `STbootRHS` stay (size level, model-free). -/
def STXiRoundPTgL'' {d : ℕ} {sz : Sizes d} (Cf : FlowFM sz) (μ : Measure sz.SeqΩ) (s t : ℕ → ℝ) : Prop :=
  ∀ n_ p : ℕ, 2 ≤ n_ → 1 ≤ p → ∀ XL XLK : ℕ → ℕ → ℝ → ℝ,
    (∀ m n u, 1 ≤ XL m n u) → (∀ m n u, 1 ≤ XLK m n u) →
    (∀ m, 1 ≤ m → STlenL n_ p m →
      PrecL sz μ (U := STPair s t) (fun n q ω => STXiLg Cf n q.1.1 m ω) (fun n q _ => XL m n q.1.2)) →
    (∀ m, 1 ≤ m → m ≤ n_ →
      PrecL sz μ (U := STPair s t) (fun n q ω => STXiLKg Cf n q.1.1 m ω) (fun n q _ => XLK m n q.1.2)) →
    PrecPTL sz μ (U := STPair s t) (fun n q ω => STXiLKg Cf n q.1.1 n_ ω)
      (fun n q _ => sz.Bctl n q.1.2 ^ (1 / 6 : ℝ) * XLK n_ n q.1.2 +
        STbootRHS 1 (fun m => XL m n q.1.2) (fun m => XLK m n q.1.2) (sz.Bctl n (s n)) n_ p)

/-- **Target 11, `STOeqQtRoundPTgL''`** (= `T2498_OeqQtRoundPTgL''`, binding; band `STOeqQtRoundPT''`, `QEndB1.lean:121`): the round in the setting
`STIngRgL d STCaseI` of a carrier family. -/
def STOeqQtRoundPTgL'' (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ)
    (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop) (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz)
    (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) : Prop :=
  STIngRgL d STCaseI law Flow mk T0 (fun sz z s t => STXiRoundPTgL'' (mk sz z) (law sz) s t)

end Texts

/-! ## 2. Helpers over a carrier (generic forms of `QEndB1` §0-§5, private) -/

section Helpers

variable {d : ℕ}

/-- `(𝓛 - 𝒦)^{(k)}_{u,σ,a}(H)` is measurable in the matrix `H` (band `altQFlow_meas_STLKM`; `LoopForm`). -/
private theorem QEndB1Gen_meas_STLKMg {sz : Sizes d} {Cm : Step2Mat sz} {E : ℕ → ℝ} (hL : StepDecompGen_LoopForm Cm E) (n : ℕ) (u : ℝ) {k : ℕ}
    (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)) :
    Measurable fun H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ => STLKMg Cm n u H σ a := by
  unfold STLKMg STLMg
  exact ((GridGoodGen_meas_of_loopForm hL n u).1 k σ a).sub_const _

/-- `H ↦ ‖(𝒬_t (𝓛-𝒦)^{(k)}_{u,σ}(H))_a‖` is measurable (band `altQFlow_meas_STQop`). -/
private theorem QEndB1Gen_meas_STQop {sz : Sizes d} {Cm : Step2Mat sz} {E : ℕ → ℝ} (hL : StepDecompGen_LoopForm Cm E) (n : ℕ) (u : ℝ) {k : ℕ}
    (σ : Fin (k + 1) → Bool) (ϑ : ℝ → (Fin (k + 1) → Zd d (sz.L n)) → ℂ) (t : ℝ) (a : Fin (k + 1) → Zd d (sz.L n)) :
    Measurable fun H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ =>
      ‖STQop (d := d) ϑ t (fun b => STLKMg Cm n u H σ b) a‖ := by
  unfold STQop STPsum
  refine Measurable.norm ?_
  refine (QEndB1Gen_meas_STLKMg hL n u σ a).sub ?_
  refine Measurable.mul_const ?_ _
  exact Finset.measurable_sum _ (fun b _ => QEndB1Gen_meas_STLKMg hL n u σ b)

/-- The set of matrices that are Hermitian and satisfy the projected initial bound at every alternating sign and label is measurable; the form
`Hermitian → bound` used for the transfer of the initial event (band `altQFlow_meas_initSet`). -/
private theorem QEndB1Gen_meas_initSet {sz : Sizes d} {Cm : Step2Mat sz} {E : ℕ → ℝ} (hL : StepDecompGen_LoopForm Cm E) (n : ℕ) (u t c : ℝ) {k : ℕ}
    (ϑ : ℝ → (Fin (k + 1) → Zd d (sz.L n)) → ℂ) :
    MeasurableSet {M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ |
      ∀ x : (Fin (k + 1) → Bool) × (Fin (k + 1) → Zd d (sz.L n)), x.1 (Fin.last k) = !x.1 0 →
        ‖STQop (d := d) ϑ t (fun b => STLKMg Cm n u M x.1 b) x.2‖ ≤ c} := by
  have e : {M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ |
      ∀ x : (Fin (k + 1) → Bool) × (Fin (k + 1) → Zd d (sz.L n)), x.1 (Fin.last k) = !x.1 0 →
        ‖STQop (d := d) ϑ t (fun b => STLKMg Cm n u M x.1 b) x.2‖ ≤ c} =
      ⋂ x : (Fin (k + 1) → Bool) × (Fin (k + 1) → Zd d (sz.L n)),
        {M | x.1 (Fin.last k) = !x.1 0 →
          ‖STQop (d := d) ϑ t (fun b => STLKMg Cm n u M x.1 b) x.2‖ ≤ c} := by
    ext M; simp
  rw [e]
  refine MeasurableSet.iInter fun x => ?_
  by_cases hx : x.1 (Fin.last k) = !x.1 0
  · simp only [hx, true_imp_iff]
    exact measurableSet_le (QEndB1Gen_meas_STQop hL n u x.1 ϑ t x.2) measurable_const
  · have hu : {M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ |
        x.1 (Fin.last k) = !x.1 0 →
          ‖STQop (d := d) ϑ t (fun b => STLKMg Cm n u M x.1 b) x.2‖ ≤ c} = Set.univ := by
      ext M; simp [hx]
    rw [hu]
    exact MeasurableSet.univ

/-- The grid walk of a `WalkForm` carrier is Hermitian at every index and sample (`Ψ n` Hermitian plus `pathH`). -/
private theorem QEndB1Gen_Hpath_herm {sz : Sizes d} {Cm : Step2Mat sz} {lam' : ℕ → ℝ}
    {Ψ : ∀ n : ℕ, Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ} (hW : StepDecompGen_WalkForm Cm lam' Ψ)
    (s t : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ) (ω : PathΩ sz) : (Cm.Hpath s t K n k ω).IsHermitian := by
  rw [StepDecompGen_Hpath_eq hW]
  exact (hW.1 n).add (pathH_isHermitian _ s t K n k ω)

/-- `Ξ̂^{(𝓛-𝒦)}_{v,k} ≤ 1 + x` as soon as every entry `‖(𝓛-𝒦)^{(k)}_{v,σ,a}‖ / B_v^k` is at most `x` (band `altQFlow_xi_le`). -/
private theorem QEndB1Gen_xi_le {sz : Sizes d} (Cf : FlowFM sz) {n : ℕ} {v : ℝ} {k : ℕ} (hB : 0 < sz.Bctl n v) {ω : sz.SeqΩ} {x : ℝ}
    (h : ∀ p' : (Fin k → Bool) × (Fin k → Zd d (sz.L n)),
      ‖Cf.L n v p'.1 p'.2 ω - Cf.K n v p'.1 p'.2‖ / (sz.Bctl n v) ^ k ≤ x) :
    STXiLKg Cf n v k ω ≤ 1 + x := by
  unfold STXiLKg STmaxLKg
  have hBk : 0 < (sz.Bctl n v) ^ k := pow_pos hB k
  have h1 : (Finset.univ.sup' ⟨((fun _ => true), (fun _ => (0 : Zd d (sz.L n)))), Finset.mem_univ _⟩
      (fun p : (Fin k → Bool) × (Fin k → Zd d (sz.L n)) =>
        ‖Cf.L n v p.1 p.2 ω - Cf.K n v p.1 p.2‖)) / (sz.Bctl n v) ^ k ≤ x := by
    rw [div_le_iff₀ hBk]
    exact Finset.sup'_le _ _ fun p' _ => (div_le_iff₀ hBk).1 (h p')
  linarith

/-- **The collapsed section** `w_n = s_n`: `STLKgL s` at the length `k` gives `‖(𝓛-𝒦)^{(k)}_{s,σ,a}‖ / B_s^k ≺ 1`, uniformly in `(σ, a)`
(band `altQFlow_collapsed`). -/
private theorem QEndB1Gen_collapsed {sz : Sizes d} {Cf : FlowFM sz} {μ : Measure sz.SeqΩ} {s : ℕ → ℝ} (hLK : STLKgL Cf μ s) {k : ℕ}
    (hk : 1 ≤ k) (hBs : ∀ n, 0 < sz.Bctl n (s n)) :
    PrecL sz μ (U := fun n => (Fin k → Bool) × (Fin k → Zd d (sz.L n)))
      (fun n x ω => ‖Cf.L n (s n) x.1 x.2 ω - Cf.K n (s n) x.1 x.2‖ / (sz.Bctl n (s n)) ^ k)
      (fun n _ _ => (1 : ℝ)) := by
  refine StochDomAt.of_subset (hLK k hk) fun τ hτ => ⟨τ, hτ, Eventually.of_forall fun n ω hω => ?_⟩
  obtain ⟨x, hx⟩ := hω
  refine ⟨x, ?_⟩
  have hBk : 0 < (sz.Bctl n (s n)) ^ k := pow_pos (hBs n) _
  have h := (lt_div_iff₀ hBk).1 hx
  simpa using h

/-- **The non-alternating half at a section time, uniformly in the signs and labels** (band `altQFlow_nq_half`): the merged per-time pin
`STNQConclPTgL''` on the window `[s, uu]` with the controls frozen at `uu_n`, at the time `w_n ∈ [s_n, uu_n]`, with the union over `(σ, a)` moved
inside `μ` by `stochDomAt_of_perTimeDomAt`. -/
private theorem QEndB1Gen_nq_half {sz : Sizes d} (Cf : FlowFM sz) (μ : Measure sz.SeqΩ) (hsize : sz.SizeTendsto) {s t uu w : ℕ → ℝ} {n_ p : ℕ}
    (hn : 2 ≤ n_) (hp : 1 ≤ p) {XL XLK : ℕ → ℕ → ℝ → ℝ} (hXL : ∀ i n u, 1 ≤ XL i n u)
    (hXLK : ∀ i n u, 1 ≤ XLK i n u)
    (hXLp : ∀ i, 1 ≤ i → STlenL n_ p i →
      PrecL sz μ (U := STPair s t) (fun n q ω => STXiLg Cf n q.1.1 i ω) (fun n q _ => XL i n q.1.2))
    (hXLKp : ∀ i, 1 ≤ i → i ≤ n_ →
      PrecL sz μ (U := STPair s t) (fun n q ω => STXiLKg Cf n q.1.1 i ω) (fun n q _ => XLK i n q.1.2))
    (hsw : ∀ n, s n ≤ w n) (hwu : ∀ n, w n ≤ uu n) (hut : ∀ n, uu n ≤ t n)
    (hNQ : STNQConclPTgL'' Cf μ s uu) :
    PrecL sz μ (U := fun n => {σ : Fin n_ → Bool // ∃ k, σ k = σ (finRotate n_ k)} × (Fin n_ → Zd d (sz.L n)))
      (fun n x ω => ‖Cf.L n (w n) x.1.1 x.2 ω - Cf.K n (w n) x.1.1 x.2‖ / (sz.Bctl n (w n)) ^ n_)
      (fun n _ _ => (sz.Bctl n (w n)) ^ (1 / 6 : ℝ) * XLK n_ n (uu n) +
        STbootRHS 2 (fun i => XL i n (uu n)) (fun i => XLK i n (uu n)) (sz.Bctl n (s n)) n_ p) := by
  have hX' : ∀ i, 1 ≤ i → STlenL n_ p i →
      PrecL sz μ (U := STPair s uu) (fun n q ω => STXiLg Cf n q.1.1 i ω) (fun n q _ => XL i n (uu n)) :=
    fun i hi hl => StochDomAt.precomp_param (V := STPair s uu) (hXLp i hi hl)
      (fun n q => ⟨(q.1.1, uu n), q.2.1, q.2.2.1.trans q.2.2.2, hut n⟩)
  have hY' : ∀ i, 1 ≤ i → i ≤ n_ →
      PrecL sz μ (U := STPair s uu) (fun n q ω => STXiLKg Cf n q.1.1 i ω) (fun n q _ => XLK i n (uu n)) :=
    fun i hi hl => StochDomAt.precomp_param (V := STPair s uu) (hXLKp i hi hl)
      (fun n q => ⟨(q.1.1, uu n), q.2.1, q.2.2.1.trans q.2.2.2, hut n⟩)
  have h := hNQ n_ p hn hp (fun i n _ => XL i n (uu n)) (fun i n _ => XLK i n (uu n))
    (fun i n _ => hXL i n _) (fun i n _ => hXLK i n _) hX' hY'
  have hper : Path.PerTimeDomAt μ sz.size
      (U := fun n => {σ : Fin n_ → Bool // ∃ k, σ k = σ (finRotate n_ k)} × (Fin n_ → Zd d (sz.L n)))
      (fun n x ω => ‖Cf.L n (w n) x.1.1 x.2 ω - Cf.K n (w n) x.1.1 x.2‖ / (sz.Bctl n (w n)) ^ n_)
      (fun n _ _ => (sz.Bctl n (w n)) ^ (1 / 6 : ℝ) * XLK n_ n (uu n) +
        STbootRHS 2 (fun i => XL i n (uu n)) (fun i => XLK i n (uu n)) (sz.Bctl n (s n)) n_ p) := by
    intro τ hτ D hD
    filter_upwards [h τ hτ D hD] with n hn' x
    exact hn' (⟨(w n), hsw n, hwu n⟩, x.1, x.2)
  refine Path.stochDomAt_of_perTimeDomAt μ sz.size (C := ((2 * n_ : ℕ) : ℝ)) (by positivity) ?_ hper
  filter_upwards [hsize.eventually_ge_atTop 2] with n hN2
  have hN2' : 2 ≤ sz.size n := by exact_mod_cast hN2
  have h1 : Fintype.card {σ : Fin n_ → Bool // ∃ k, σ k = σ (finRotate n_ k)} ≤ 2 ^ n_ := by
    calc _ ≤ Fintype.card (Fin n_ → Bool) := Fintype.card_subtype_le _
      _ = 2 ^ n_ := by simp
  have h2 : Fintype.card (Fin n_ → Zd d (sz.L n)) = ((sz.L n) ^ d) ^ n_ := by
    rw [Fintype.card_fun, altQFlow_card_Zd, Fintype.card_fin]
  have h3 : 2 ^ n_ ≤ (sz.size n) ^ n_ := Nat.pow_le_pow_left hN2' n_
  have h4 : ((sz.L n) ^ d) ^ n_ ≤ (sz.size n) ^ n_ := Nat.pow_le_pow_left (altQFlow_Zd_le_size sz n) n_
  rw [Real.rpow_natCast, Fintype.card_prod, h2]
  have h5 : Fintype.card {σ : Fin n_ → Bool // ∃ k, σ k = σ (finRotate n_ k)} * ((sz.L n) ^ d) ^ n_ ≤
      (sz.size n) ^ (2 * n_) := by
    calc _ ≤ 2 ^ n_ * ((sz.L n) ^ d) ^ n_ := Nat.mul_le_mul_right _ h1
      _ ≤ (sz.size n) ^ n_ * (sz.size n) ^ n_ := Nat.mul_le_mul h3 h4
      _ = (sz.size n) ^ (2 * n_) := by rw [← pow_add]; congr 1; ring
  exact_mod_cast h5

end Helpers

section CoreProof

variable {d : ℕ}

/-- The carrier facts of one flow `(sz, z)` that the endpoint `altGridEndQNg` and the initial loops read (rows 3-9, 11 of the family-premise table, plus the
law and `LCompat` of the flow matrix `Hf`); a private bundle, so that no public statement has an unproved `Prop` premise of this name. -/
private structure QEndB1Gen_Facts {sz : Sizes d} (Cm : Step2Mat sz) (μ : Measure sz.SeqΩ)
    (Hf : ∀ n : ℕ, ℝ → sz.SeqΩ → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    (E lam' gK : ℕ → ℝ) (Ψ : ∀ n : ℕ, Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (κm A C₆ K₆ 𝔡 : ℝ) : Prop where
  hL : StepDecompGen_LoopForm Cm E
  hW : StepDecompGen_WalkForm Cm lam' Ψ
  hspec : DecayGen_Spec Cm.toFlowFM κm
  hm : ∀ n, ‖Cm.m n‖ ≤ 1
  hSeq : ∀ n, Cm.S n = SB d (sz.L n) (lam' n)
  hS : ∀ (n : ℕ) (a : Zd d (sz.L n)), ∑ b : Zd d (sz.L n), ‖Cm.S n a b‖ ≤ 1
  hRow : ∀ n, GridRepTailGen_Ker Cm.toFlowFM n
  hKK : ∀ (n : ℕ) (w : ℝ) (k : ℕ) (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)),
    Cm.KI n w (KLloopOf d (sz.L n) σ a) = Cm.K n w σ a
  hExp : ∀ᶠ n : ℕ in atTop, ∀ (s' t' : ℕ → ℝ) (K' : ℕ → ℕ), HierDriftGen_Expand Cm s' t' K' n
  hKL : ∀ᶠ n : ℕ in atTop, HierDriftGen_KLoop Cm n
  hKT : ∀ᶠ n : ℕ in atTop, HierDriftGen_KTwo Cm n
  hU : ∀ᶠ n : ℕ in atTop, HierDriftGen_UStep Cm.toFlowFM n
  hLaw : Step2EventsGen_Law Cm μ Hf
  hC : Step34Gen_LCompat Cm Hf
  hcmp : ∀ n, 0 ≤ gK n * sz.lam n ∧ gK n ^ 2 ≤ sz.lam n ^ 2 ∧ sz.lam n ^ 2 ≤ A * gK n ^ 2
  hA : 1 ≤ A
  hward : ZeroModeGen_WardCls sz Cm.toFlowFM
  hker : ∀ n, ZeroModeGen_KerSums Cm.toFlowFM n
  hK₆ : 1 ≤ K₆
  hrow : ∀ (n : ℕ) (σ σ' : Bool) (t : ℝ), 0 ≤ t → t < 1 → ∀ a : Zd d (sz.L n),
    ∑ b : Zd d (sz.L n), ‖Step2Gen_thetaKer Cm.toFlowFM n σ σ' t a b‖ ≤ K₆ / (1 - t)
  hcol : ∀ (n : ℕ) (σ σ' : Bool) (t : ℝ), 0 ≤ t → t < 1 → ∀ b : Zd d (sz.L n),
    ‖∑ a : Zd d (sz.L n), Step2Gen_thetaKer Cm.toFlowFM n σ σ' t a b‖ ≤ K₆ / (1 - t)
  hTh : Step5KerGen_ThDecay Cm.toFlowFM gK 𝔡⁻¹ C₆
  hC₆ : 0 ≤ C₆

/-- **The projected initial loops** (`3_5:1676-1690`, the "start term" of the alternating case; band `altQFlow0_initQ`, `QEndB1:1204`): for every `ε > 0`, with
high probability the projected initial loops `𝒬_s (𝓛-𝒦)^{(m+2)}_{s,σ}` of the flow matrix `Hf n (s n)` at every alternating sign are at most `N^ε B_s^{m+2}`
(for a Hermitian matrix; the carrier walk is Hermitian, `QEndB1Gen_Hpath_herm`).  Proof: `startLevelQNg` per matrix at `u = s_n`, `X ≡ 1`, `ν = N^{e/8}`,
`τ_N = e/2`, `e = min ε 1`, with `hY` (`STLKgL s` at length `m+1`), `hYtop` (`STLKgL s` at `m+2`) and `hF` (`stDecayLoopUgL_of_step2` at the far labels,
window `ωf = W^{e/(8d(m+1))}`, decay `D_F = (2m+5)/𝔠`); the spectral data are `DecayGen_Spec` (`Γ = κm⁻¹`) and `‖m‖ ≤ 1`. -/
private theorem QEndB1Gen_initQ {sz : Sizes d} (Cm : Step2Mat sz) (μ : Measure sz.SeqΩ)
    {Hf : ∀ n : ℕ, ℝ → sz.SeqΩ → Matrix (Idx d (sz.L n)  (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ}
    {E lam' gK : ℕ → ℝ} {Ψ : ∀ n : ℕ, Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ} {κm A C₆ K₆ 𝔠 τR 𝔡 : ℝ}
    (F : QEndB1Gen_Facts Cm μ Hf E lam' gK Ψ κm A C₆ K₆ 𝔡) {s t : ℕ → ℝ} (hd : 3 ≤ d) (h𝔠 : 0 < 𝔠)
    (hsize : sz.SizeTendsto) (hband : sz.Bandwidth 𝔠) (hWO : sz.WO 𝔡) (hs0 : ∀ n, 0 ≤ s n) (hst : ∀ n, s n ≤ t n) (ht1 : ∀ n, t n < 1)
    (hrange : sz.RangeCond τR t) (hτR : 0 < τR) (hLK : STLKgL Cm.toFlowFM μ s) (hDecay : STDecayLoopUgL Cm.toFlowFM μ s t)
    {m : ℕ} {ε : ℝ} (hε : 0 < ε) :
    HighProbAt μ sz.size (fun n => {ω | (Hf n (s n) ω).IsHermitian →
      ∀ x : (Fin (m + 1 + 1) → Bool) × (Fin (m + 1 + 1) → Zd d (sz.L n)),
      x.1 (Fin.last (m + 1)) = !x.1 0 →
        ‖STQop (d := d) (QopAlgebra_mollifier d (sz.L n) (m + 1) (sz.lam n)) (s n)
          (fun b => STLKMg Cm n (s n) (Hf n (s n) ω) x.1 b) x.2‖ ≤
        ((sz.size n : ℕ) : ℝ) ^ ε * (sz.Bctl n (s n)) ^ (m + 1 + 1)}) := by
  classical
  have hd1 : 1 ≤ d := by omega
  have hsz := tendsto_size sz hsize
  obtain ⟨e, he⟩ : ∃ e : ℝ, e = min ε 1 := ⟨_, rfl⟩
  have he0 : 0 < e := by rw [he]; exact lt_min hε one_pos
  have he1 : e ≤ 1 := by rw [he]; exact min_le_right _ _
  have heε : e ≤ ε := by rw [he]; exact min_le_left _ _
  have hdm : (0 : ℝ) < ((d * (m + 1) : ℕ) : ℝ) := by
    have : 0 < d * (m + 1) := Nat.mul_pos (by omega) (by omega)
    exact_mod_cast this
  obtain ⟨τ'', hτ''⟩ : ∃ τ'' : ℝ, τ'' = e / (8 * ((d * (m + 1) : ℕ) : ℝ)) := ⟨_, rfl⟩
  have hτ''0 : 0 < τ'' := by rw [hτ'']; positivity
  obtain ⟨DF, hDF⟩ : ∃ DF : ℝ, DF = (2 * (m : ℝ) + 5) / 𝔠 := ⟨_, rfl⟩
  have hDF0 : 0 < DF := by rw [hDF]; positivity
  obtain ⟨C, hC⟩ : ∃ C : ℝ, C = (1 + 40 * ((d * (m + 1) : ℕ) : ℝ)) * 6 ^ (d * (m + 1)) := ⟨_, rfl⟩
  have hC0 : 0 < C := by rw [hC]; positivity
  have hκm : 0 < κm := F.hspec.1
  obtain ⟨c₀, hc₀⟩ : ∃ c₀ : ℝ,
      c₀ = (2 * (m : ℝ) + 5) * K₆ * (3 * 4 ^ (d * m) * κm⁻¹ * C) := ⟨_, rfl⟩
  have hA1 := GridGoodGen_precL_whp (hLK (m + 1) (by omega)) (τ := e / 8) (by positivity)
  have hA2 := GridGoodGen_precL_whp (hLK (m + 1 + 1) (by omega)) (τ := e / 8) (by positivity)
  have hA3 := GridGoodGen_precL_whp (hDecay (m + 1) (by omega) τ'' DF hτ''0 hDF0) (τ := 1) one_pos
  refine HighProbAt.mono (HighProbAt.inter hsz (HighProbAt.inter hsz hA1 hA2) hA3) ?_
  have hc₀ev : ∀ᶠ n in atTop, c₀ ≤ ((sz.size n : ℕ) : ℝ) ^ (e / 4) :=
    ((tendsto_rpow_atTop (by positivity : (0 : ℝ) < e / 4)).comp hsize).eventually_ge_atTop c₀
  have h2ev : ∀ᶠ n in atTop, (2 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ (e / 2) :=
    ((tendsto_rpow_atTop (by positivity : (0 : ℝ) < e / 2)).comp hsize).eventually_ge_atTop 2
  filter_upwards [hWO, hband, hrange, hc₀ev, h2ev] with n hwo hbd hrg hc hN2
  rintro ω ⟨⟨hY1, hYtop'⟩, hFar⟩ hHerm x hx
  -- the scalar facts at the size index `n`
  have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
  have hW1 : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hW0 : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by linarith
  have hWN := altQFlow_W_le_size sz hd1 n
  have hlam : 0 < sz.lam n := lt_of_lt_of_le (Real.rpow_pos_of_pos hW0 _) hwo.1
  have hu1 : s n < 1 := (hst n).trans_lt (ht1 n)
  have hBs : 0 < sz.Bctl n (s n) := st_Bctl_pos sz hu1
  have hNu : (((sz.size n : ℕ) : ℝ))⁻¹ ≤ 1 - s n := by
    have h1 : ((sz.size n : ℕ) : ℝ) ^ (-1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ (-1 + τR) :=
      Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
    rw [Real.rpow_neg_one] at h1
    linarith [hst n]
  obtain ⟨ν, hν⟩ : ∃ ν : ℝ, ν = ((sz.size n : ℕ) : ℝ) ^ (e / 8) := ⟨_, rfl⟩
  have hν1 : 1 ≤ ν := by rw [hν]; exact Real.one_le_rpow hN1 (by positivity)
  have hνN : ν ≤ ((sz.size n : ℕ) : ℝ) := by
    rw [hν]
    calc ((sz.size n : ℕ) : ℝ) ^ (e / 8) ≤ ((sz.size n : ℕ) : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
      _ = _ := Real.rpow_one _
  have hν2 : ν ^ 2 = ((sz.size n : ℕ) : ℝ) ^ (e / 4) := by
    rw [hν, sq, ← Real.rpow_add hN0]; congr 1; ring
  -- the window `ωf = W^{τ''}`
  obtain ⟨ωf, hωfdef⟩ : ∃ ωf : ℝ, ωf = ((sz.W n : ℕ) : ℝ) ^ τ'' := ⟨_, rfl⟩
  have hωf : 1 ≤ ωf := by rw [hωfdef]; exact Real.one_le_rpow hW1 hτ''0.le
  have hωd : ωf ^ (d * m) ≤ ν := by
    have e1 : ωf ^ (d * m) = ((sz.W n : ℕ) : ℝ) ^ (τ'' * ((d * m : ℕ) : ℝ)) := by
      rw [hωfdef, ← Real.rpow_natCast, ← Real.rpow_mul hW0.le]
    have hle : τ'' * ((d * m : ℕ) : ℝ) ≤ e / 8 := by
      have h1 : ((d * m : ℕ) : ℝ) ≤ ((d * (m + 1) : ℕ) : ℝ) := by
        exact_mod_cast Nat.mul_le_mul_left d (Nat.le_succ m)
      rw [hτ'']
      calc e / (8 * ((d * (m + 1) : ℕ) : ℝ)) * ((d * m : ℕ) : ℝ)
          ≤ e / (8 * ((d * (m + 1) : ℕ) : ℝ)) * ((d * (m + 1) : ℕ) : ℝ) :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = e / 8 := by field_simp
    rw [e1, hν]
    calc ((sz.W n : ℕ) : ℝ) ^ (τ'' * ((d * m : ℕ) : ℝ)) ≤ ((sz.W n : ℕ) : ℝ) ^ (e / 8) :=
          Real.rpow_le_rpow_of_exponent_le hW1 hle
      _ ≤ ((sz.size n : ℕ) : ℝ) ^ (e / 8) := Real.rpow_le_rpow hW0.le hWN (by positivity)
  -- the far decay level
  obtain ⟨Fv, hFvdef⟩ : ∃ Fv : ℝ, Fv = ((sz.size n : ℕ) : ℝ) * ((sz.W n : ℕ) : ℝ) ^ (-DF) := ⟨_, rfl⟩
  have hFv0 : 0 ≤ Fv := by rw [hFvdef]; positivity
  have hFv : Fv ≤ ν * (((sz.size n : ℕ) : ℝ) ^ (2 * m + 4))⁻¹ := by
    have hWD : ((sz.size n : ℕ) : ℝ) ^ (2 * m + 5) ≤ ((sz.W n : ℕ) : ℝ) ^ DF := by
      calc ((sz.size n : ℕ) : ℝ) ^ (2 * m + 5) = (((sz.size n : ℕ) : ℝ) ^ 𝔠) ^ DF := by
            rw [← Real.rpow_mul hN0.le, show 𝔠 * DF = ((2 * m + 5 : ℕ) : ℝ) by
              rw [hDF]; push_cast; field_simp, Real.rpow_natCast]
        _ ≤ ((sz.W n : ℕ) : ℝ) ^ DF := Real.rpow_le_rpow (Real.rpow_nonneg hN0.le _) hbd hDF0.le
    have hWneg : ((sz.W n : ℕ) : ℝ) ^ (-DF) ≤ (((sz.size n : ℕ) : ℝ) ^ (2 * m + 5))⁻¹ := by
      rw [Real.rpow_neg hW0.le]
      exact inv_anti₀ (by positivity) hWD
    have h1 : ((sz.size n : ℕ) : ℝ) * (((sz.size n : ℕ) : ℝ) ^ (2 * m + 5))⁻¹ =
        (((sz.size n : ℕ) : ℝ) ^ (2 * m + 4))⁻¹ := by
      rw [show 2 * m + 5 = (2 * m + 4) + 1 by ring, pow_succ]
      field_simp
    have h2 : (((sz.size n : ℕ) : ℝ) ^ (2 * m + 4))⁻¹ ≤ ν * (((sz.size n : ℕ) : ℝ) ^ (2 * m + 4))⁻¹ :=
      le_mul_of_one_le_left (by positivity) hν1
    rw [hFvdef]
    calc ((sz.size n : ℕ) : ℝ) * ((sz.W n : ℕ) : ℝ) ^ (-DF)
        ≤ ((sz.size n : ℕ) : ℝ) * (((sz.size n : ℕ) : ℝ) ^ (2 * m + 5))⁻¹ :=
          mul_le_mul_of_nonneg_left hWneg hN0.le
      _ = _ := h1
      _ ≤ _ := h2
  -- `hMΛ`
  have hMΛ : ((2 * (m : ℝ) + 5) * K₆) * (3 * 4 ^ (d * m) * κm⁻¹ * C * ν ^ 2) ≤ ((sz.size n : ℕ) : ℝ) ^ (e / 2) := by
    have hsq : ((sz.size n : ℕ) : ℝ) ^ (e / 2) = ((sz.size n : ℕ) : ℝ) ^ (e / 4) * ((sz.size n : ℕ) : ℝ) ^ (e / 4) := by
      rw [← Real.rpow_add hN0]; congr 1; ring
    have hp : 0 ≤ ν ^ 2 := by positivity
    calc ((2 * (m : ℝ) + 5) * K₆) * (3 * 4 ^ (d * m) * κm⁻¹ * C * ν ^ 2)
        = c₀ * ν ^ 2 := by rw [hc₀]; ring
      _ ≤ ((sz.size n : ℕ) : ℝ) ^ (e / 4) * ν ^ 2 := mul_le_mul_of_nonneg_right hc hp
      _ = _ := by rw [hsq, hν2]
  -- the levels read off the three events
  have hLMe : ∀ {k : ℕ} (σ' : Fin k → Bool) (a' : Fin k → Zd d (sz.L n)),
      STLKMg Cm n (s n) (Hf n (s n) ω) σ' a' = Cm.L n (s n) σ' a' ω - Cm.K n (s n) σ' a' := by
    intro k σ' a'
    unfold STLKMg STLMg
    rw [GridGoodGen_LM_eq_L F.hL F.hC n (s n) σ' a' ω]
  have hY : ∀ (σ' : Fin (m + 1) → Bool) (a' : Fin (m + 1) → Zd d (sz.L n)),
      ‖STLKMg Cm n (s n) (Hf n (s n) ω) σ' a'‖ ≤ ν * 1 * sz.Bctl n (s n) ^ (m + 1) := by
    intro σ' a'
    have h := hY1 (σ', a')
    rw [hLMe, mul_one, hν]
    exact h
  have hF : ∀ (σ' : Fin (m + 1) → Bool) (a' : Fin (m + 1) → Zd d (sz.L n)),
      ellT (sz.L n) (sz.lam n) (s n) * ωf ≤ (STdiamInf a' : ℝ) → ‖STLKMg Cm n (s n) (Hf n (s n) ω) σ' a'‖ ≤ Fv := by
    intro σ' a' hfar
    have h := hFar (⟨s n, le_rfl, hst n⟩, σ', a')
    simp only [Real.rpow_one] at h
    rw [← hωfdef] at h
    simp only [hfar, ↓reduceIte, mul_one] at h
    rw [hLMe, hFvdef]
    exact le_trans (le_add_of_nonneg_left (norm_nonneg _)) h
  have hYtop : ∀ b : Fin (m + 1 + 1) → Zd d (sz.L n),
      ‖STLKMg Cm n (s n) (Hf n (s n) ω) x.1 b‖ ≤ ν * sz.Bctl n (s n) ^ (m + 1 + 1) := by
    intro b
    have h := hYtop' (x.1, b)
    rw [hLMe, hν]
    exact h
  -- the mollifier bound
  have hϑ : STMollifierProps (d := d) (sz.lam n) C (1 / 2)
      (QopAlgebra_mollifier d (sz.L n) (m + 1) (sz.lam n)) := by
    rw [hC]; exact QopAlgebra_mollifier_props d (sz.L n) (m + 1) (sz.three_le_L n) hlam
  have hexp : ∀ a : Fin (m + 1 + 1) → Zd d (sz.L n),
      ‖QopAlgebra_mollifier d (sz.L n) (m + 1) (sz.lam n) (s n) a‖ ≤
        C * (((ellT (sz.L n) (sz.lam n) (s n) ^ d)⁻¹) ^ (m + 1)) := by
    intro a
    refine (hϑ.2.1 (s n) (hs0 n) hu1 a).trans ?_
    have hl : 0 < ellT (sz.L n) (sz.lam n) (s n) := ellT_pos (by
      exact_mod_cast (by have := sz.three_le_L n; omega : 1 ≤ sz.L n))
    have hS : 0 ≤ ∑ i ∈ Finset.univ.erase (0 : Fin (m + 1 + 1)),
        (zdistD d (sz.L n) (a i - a 0) : ℝ) := Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)
    have hex : Real.exp (-(1 / 2 : ℝ) * (∑ i ∈ Finset.univ.erase (0 : Fin (m + 1 + 1)),
        (zdistD d (sz.L n) (a i - a 0) : ℝ)) / ellT (sz.L n) (sz.lam n) (s n)) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      exact div_nonpos_of_nonpos_of_nonneg (by nlinarith [hS]) hl.le
    have hC1 : 0 ≤ C * (((ellT (sz.L n) (sz.lam n) (s n) ^ d)⁻¹) ^ (m + 1)) := by positivity
    calc _ ≤ C * (((ellT (sz.L n) (sz.lam n) (s n) ^ d)⁻¹) ^ (m + 1)) * 1 :=
          mul_le_mul_of_nonneg_left hex hC1
      _ = _ := by rw [mul_one]
  have key := startLevelQNg (by omega : 2 ≤ d) Cm F.hL n hκm (F.hspec.2.1 n) ((Complex.im_le_norm _).trans (F.hm n)) (F.hspec.2.2 n) F.hward (F.hker n)
    F.hK₆ (F.hrow n) (F.hcol n) (hs0 n) hu1 hlam hNu hHerm (m := m) (Γ := κm⁻¹) (ν := ν) (X := 1) (ωf := ωf) (Fv := Fv)
    (Λ := C) (τ := e / 2) (Y := ν * sz.Bctl n (s n) ^ (m + 1 + 1)) rfl hν1 le_rfl hωf hωd hνN hFv hFv0 hC0.le hMΛ hY hF _ hexp x.1 hx hYtop x.2
  -- `ν + N^{e/2} ≤ N^ε`
  have hsq : ((sz.size n : ℕ) : ℝ) ^ e = ((sz.size n : ℕ) : ℝ) ^ (e / 2) * ((sz.size n : ℕ) : ℝ) ^ (e / 2) :=
    (UnifDetDom.rpow_half_mul_rpow_half _ he0).symm
  have hle1 : ν ≤ ((sz.size n : ℕ) : ℝ) ^ (e / 2) := by
    rw [hν]; exact Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  have hle2 : ((sz.size n : ℕ) : ℝ) ^ e ≤ ((sz.size n : ℕ) : ℝ) ^ ε :=
    Real.rpow_le_rpow_of_exponent_le hN1 heε
  have hsum : ν + ((sz.size n : ℕ) : ℝ) ^ (e / 2) ≤ ((sz.size n : ℕ) : ℝ) ^ ε := by
    have : (2 : ℝ) * ((sz.size n : ℕ) : ℝ) ^ (e / 2) ≤
        ((sz.size n : ℕ) : ℝ) ^ (e / 2) * ((sz.size n : ℕ) : ℝ) ^ (e / 2) :=
      mul_le_mul_of_nonneg_right hN2 (Real.rpow_nonneg hN0.le _)
    linarith
  have hBp : 0 ≤ sz.Bctl n (s n) ^ (m + 2) := (pow_pos hBs _).le
  calc _ ≤ ν * sz.Bctl n (s n) ^ (m + 1 + 1) + ((sz.size n : ℕ) : ℝ) ^ (e / 2) * (sz.Bctl n (s n) ^ (m + 2) * 1) := key
    _ = (ν + ((sz.size n : ℕ) : ℝ) ^ (e / 2)) * sz.Bctl n (s n) ^ (m + 2) := by ring
    _ ≤ ((sz.size n : ℕ) : ℝ) ^ ε * sz.Bctl n (s n) ^ (m + 1 + 1) :=
        mul_le_mul_of_nonneg_right hsum hBp

/-- **The alternating endpoint at one non-collapsed section** (`s_n < v_n ≤ t_n`; band `altQFlow0_core`, `QEndB1:1409`, with `altGridEndQNg` of row b in place of
`altGridEndQN'`; the shape of `NQEndFlowGen_core`): for deterministic controls `X i n`, `Y i n ≥ 1` with `Ξ̂^{(𝓛)}_{w,i} ≺ X i` (`STlenL (m+2) p i`) and
`Ξ̂^{(𝓛-𝒦)}_{w,i} ≺ Y i` (`i ≤ m+2`) uniformly in `w ∈ [s_n, v_n]`, the alternating `(𝓛-𝒦)^{(m+2)}_{v,σ,a}/B_v^{m+2}`, uniformly in `(σ, a)`, is
`≺ B_v^{1/6} Y (m+2) + STbootRHS 1 X Y B_s (m+2) p`.  The failure event is inside the union of `(W_n)ᶜ`, the walk leaving `GoodSetNg ∩ GoodLinNg ∩ altYSetNg` or the
projected initial bound failing (`QEndB1Gen_initQ`, transferred by the law at `j = 0`), of probability `≤ N^{-(D+2)}`, and the exceptional event `Gᶜ` of `altGridEndQNg`
at `ε₀ = τ/2`, `D₁ = D + 2`; outside it `altGridEndQNg` bounds the terminal loop, transferred to the flow matrix `Hf` at `v_n` by the law at `j = K_n`.  The vocabulary
constant is `Cv = C4 + 1` at the consumer; here `C4 ≤ Cv` and `C4 < Cv ∨ A = 1` are hypotheses. -/
private theorem QEndB1Gen_core {sz : Sizes d} (Cm : Step2Mat sz) (μ : Measure sz.SeqΩ)
    {Hf : ∀ n : ℕ, ℝ → sz.SeqΩ → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ}
    {E lam' gK : ℕ → ℝ} {Ψ : ∀ n : ℕ, Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ} {κm A C₆ K₆ 𝔠 τR 𝔡 : ℝ}
    (F : QEndB1Gen_Facts Cm μ Hf E lam' gK Ψ κm A C₆ K₆ 𝔡) {s t v : ℕ → ℝ} (hd : 3 ≤ d) (h𝔠 : 0 < 𝔠) (hτR : 0 < τR) (h𝔡 : 0 < 𝔡)
    (hKb : STKboundgL Cm.toFlowFM μ) (hsize : sz.SizeTendsto) (hband : sz.Bandwidth 𝔠) (hWO : sz.WO 𝔡)
    (hs0 : ∀ n, 0 ≤ s n) (hst : ∀ n, s n ≤ t n) (ht1 : ∀ n, t n < 1) (hcase : sz.STCaseI s t) (hrange : sz.RangeCond τR t)
    (hWt : ∀ᶠ n : ℕ in atTop, (((sz.W n : ℕ) : ℝ))⁻¹ ≤ (1 - t n) / (1 - s n))
    (hsv : ∀ n, s n < v n) (hvt : ∀ n, v n ≤ t n) (hLK : STLKgL Cm.toFlowFM μ s) (hDecay : STDecayLoopUgL Cm.toFlowFM μ s t)
    (hGrid : GridGoodNConclg Cm μ s v) (hLin : NQLinConclg Cm μ s t) {m p : ℕ} (hp : 1 ≤ p)
    {C4 Cv : ℝ} (hC4 : 0 < C4) (hC4Cv : C4 ≤ Cv) (hAk0 : C4 < Cv ∨ A = 1)
    (hKer : ∀ᶠ n : ℕ in atTop, QProxyG_KerEK4 Cm.toFlowFM gK (m + 1 + 1) (1 / 𝔠) C4 n)
    {X Y : ℕ → ℕ → ℝ} (hX1 : ∀ i n, 1 ≤ X i n) (hY1 : ∀ i n, 1 ≤ Y i n)
    (hX : ∀ i : ℕ, 1 ≤ i → STlenL (m + 1 + 1) p i →
      PrecL sz μ (U := fun n => TimeIcc s v n) (fun n u ω => STXiLg Cm.toFlowFM n (u : ℝ) i ω) (fun n _ _ => X i n))
    (hY : ∀ i : ℕ, 1 ≤ i → i ≤ m + 1 + 1 →
      PrecL sz μ (U := fun n => TimeIcc s v n) (fun n u ω => STXiLKg Cm.toFlowFM n (u : ℝ) i ω) (fun n _ _ => Y i n)) :
    StochDomAt μ sz.size
      (fun n (x : {σ : Fin (m + 1 + 1) → Bool // σ (Fin.last (m + 1)) = !σ 0} × (Fin (m + 1 + 1) → Zd d (sz.L n))) ω =>
        ‖Cm.L n (v n) x.1.1 x.2 ω - Cm.K n (v n) x.1.1 x.2‖ / (sz.Bctl n (v n)) ^ (m + 1 + 1))
      (fun n _ _ => (sz.Bctl n (v n)) ^ (1 / 6 : ℝ) * Y (m + 1 + 1) n +
        STbootRHS 1 (fun i => X i n) (fun i => Y i n) (sz.Bctl n (s n)) (m + 1 + 1) p) := by
  classical
  have : IsProbabilityMeasure Cm.Pp := by rw [F.hW.2.1]; exact isProbabilityMeasure_pathP _
  have := NQEndFlowGen_isProb F.hLaw
  intro τ hτ D hD
  have hsz := tendsto_size sz hsize
  have hv1 : ∀ n, v n < 1 := fun n => (hvt n).trans_lt (ht1 n)
  have hBv : ∀ n, 0 < sz.Bctl n (v n) := fun n => st_Bctl_pos sz (hv1 n)
  have hBs : ∀ n, 0 < sz.Bctl n (s n) := fun n => st_Bctl_pos sz ((hsv n).le.trans_lt (hv1 n))
  -- the levels
  set Λ : ℕ → ℝ := fun n => max 1 (RBM.Ind.nqFlowLam (fun i => X i n) (sz.Bctl n (s n)) (m + 1 + 1) p) with hΛdef
  set Φ₁ : ℕ → ℝ := fun n => nqLinPhi1 (fun i => Y i n) (m + 1 + 1) with hΦ₁def
  set Φ₂ : ℕ → ℝ := fun n =>
    nqLinPhi2 (fun i => X i n) (fun i => Y i n) (sz.Bctl n (v n)) (m + 1 + 1) (Y (m + 1 + 1) n) with hΦ₂def
  set Φ₃ : ℕ → ℝ := fun n => nqLinPhi3 (fun i => X i n) (m + 1 + 1) with hΦ₃def
  set Φc : ℕ → ℝ := fun n => RBM.Ind.nqFlowPhiC (fun i => X i n) (fun i => Y i n) (m + 1 + 1) with hΦcdef
  set Xl : ℕ → ℝ := fun n => Y (m + 1) n with hXldef
  have hΛ1 : ∀ n, 1 ≤ Λ n := fun n => le_max_left _ _
  have hΛ0 : ∀ n, 0 ≤ Λ n := fun n => zero_le_one.trans (hΛ1 n)
  have hΦ : ∀ n, 0 ≤ Φ₁ n ∧ 0 ≤ Φ₂ n ∧ 0 ≤ Φ₃ n := fun n =>
    altQFlow_phi_nonneg (fun i => hX1 i n) (fun i => hY1 i n) (hBv n).le
  have hΦc1 : ∀ n, 1 ≤ Φc n := fun n => altQFlow_phiC_one_le (fun i => hX1 i n) (fun i => hY1 i n)
  have hXl1 : ∀ n, 1 ≤ Xl n := fun n => hY1 _ n
  -- the endpoint of the grid walk at `ε₀ = τ/2`, `D₁ = D + 2`
  obtain ⟨ε₁, τ', D', C_K, hε₁, hτ', hD', hCK, hend⟩ := altGridEndQNg Cm μ s t hd h𝔠 hτR h𝔡 F.hL F.hW F.hspec F.hm F.hSeq F.hS
    F.hRow F.hKK hKb F.hExp F.hKL F.hKT F.hU F.hward F.hker F.hK₆ F.hrow F.hcol F.hTh F.hC₆ hsize hband hWO hs0 hst ht1 hcase hrange hWt
    F.hcmp F.hA m C4 Cv hC4 hC4Cv hAk0 hKer Λ Φ₁ Φ₂ Φ₃ Xl hΛ0 (Eventually.of_forall hΛ1) (fun n => (hΦ n).1) (fun n => (hΦ n).2.1)
    (fun n => (hΦ n).2.2) hXl1 v (fun n => (hsv n).le) hvt (τ / 2) (half_pos hτ) (D + 2) (by linarith)
  -- the grid
  set K : ℕ → ℕ := altQFlow_K sz C_K with hKdef
  have hK0 : ∀ n, K n ≠ 0 := altQFlow_K_ne_zero sz C_K
  have hKcard := altQFlow_K_card sz hsize hCK
  have hpin := hend Φc K hK0 (Eventually.of_forall (altQFlow_K_low sz C_K)) (Eventually.of_forall (altQFlow_K_up sz C_K))
  -- the hypotheses of the good-event lemma on `[s, v]` at the crude level `Φc` and the level `Λ_s`
  have hXg : ∀ i : ℕ, 1 ≤ i → i ≤ m + 1 + 1 + 1 →
      PrecL sz μ (U := fun n => TimeIcc s v n) (fun n u ω => STXiLg Cm.toFlowFM n (u : ℝ) i ω) (fun n _ _ => Φc n) :=
    fun i hi hi' => NQEndFlowGen_prec_of_le_right (hX i hi (Or.inl hi')) fun n u ω =>
      (altQFlow_phiC_ge (fun i => hX1 i n) (fun i => hY1 i n) (Finset.mem_Icc.2 ⟨hi, hi'⟩)).1
  have hYg : ∀ i : ℕ, 1 ≤ i → i ≤ m + 1 + 1 →
      PrecL sz μ (U := fun n => TimeIcc s v n) (fun n u ω => STXiLKg Cm.toFlowFM n (u : ℝ) i ω) (fun n _ _ => Φc n) :=
    fun i hi hi' => NQEndFlowGen_prec_of_le_right (hY i hi hi') fun n u ω =>
      (altQFlow_phiC_ge (fun i => hX1 i n) (fun i => hY1 i n) (Finset.mem_Icc.2 ⟨hi, by omega⟩)).2
  have hQ : PrecL sz μ (U := fun n => TimeIcc s v n)
      (fun n u ω => STXiLg Cm.toFlowFM n (u : ℝ) (2 * (m + 1 + 1) - 1) ω *
        (STXiLg Cm.toFlowFM n (u : ℝ) (4 * p) ω / sz.Bctl n (u : ℝ)) ^ (1 / (2 * (p : ℝ))))
      (fun n _ _ => Λ n) :=
    NQEndFlowGen_hQ Cm.toFlowFM μ hsize (fun n => (hsv n).le) hv1 (a := 2 * (m + 1 + 1) - 1) (b := 4 * p) hp
      (Xa := fun n => X (2 * (m + 1 + 1) - 1) n) (Xb := fun n => X (4 * p) n)
      (fun n => zero_le_one.trans (hX1 _ n)) (fun n => zero_le_one.trans (hX1 _ n))
      (hX (2 * (m + 1 + 1) - 1) (by omega) (Or.inr (Or.inl rfl))) (hX (4 * p) (by omega) (Or.inr (Or.inr rfl)))
  have hgood := hGrid v (fun n => (hsv n).le) (fun n => le_rfl) K hK0 (m + 1 + 1) (by omega) Λ Φc hΛ1 hΦc1 hXg hYg
    p hp hQ (C_K + 2) hKcard ε₁ hε₁ τ' hτ' D' hD'
  have hlin := hLin v (fun n => (hsv n).le) hvt K hK0 (m + 1 + 1) (by omega) X Y hX1 hY1
    (fun i hi hi' => hX i hi (Or.inl hi')) hY (C_K + 2) hKcard ε₁ hε₁
  have hyg := altYGridNg Cm μ Hf F.hL F.hC F.hLaw s v K (m + 1) Xl hs0 (fun n => (hsv n).le) hv1 hK0
    (hY (m + 1) (by omega) (by omega)) (C := C_K + 2) hKcard (ε := ε₁) hε₁
  have hinit := QEndB1Gen_initQ Cm μ F hd h𝔠 hsize hband hWO hs0 hst ht1 hrange hτR hLK hDecay (m := m) hε₁
  -- the initial event on the path space at the grid index `0` (the law at `j = 0`)
  let initGood : ∀ n, Set (Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) := fun n =>
    {M | ∀ x : (Fin (m + 1 + 1) → Bool) × (Fin (m + 1 + 1) → Zd d (sz.L n)),
      x.1 (Fin.last (m + 1)) = !x.1 0 →
        ‖STQop (d := d) (QopAlgebra_mollifier d (sz.L n) (m + 1) (sz.lam n)) (s n)
          (fun b => STLKMg Cm n (s n) M x.1 b) x.2‖ ≤
        ((sz.size n : ℕ) : ℝ) ^ ε₁ * (sz.Bctl n (s n)) ^ (m + 1 + 1)}
  have hinitP : HighProbAt Cm.Pp sz.size (fun n => Cm.Hpath s v K n 0 ⁻¹' initGood n) := by
    intro D'' hD''
    filter_upwards [hinit D'' hD''] with n hn
    have hS : MeasurableSet (initGood n) :=
      QEndB1Gen_meas_initSet F.hL n (s n) (s n)
        (((sz.size n : ℕ) : ℝ) ^ ε₁ * (sz.Bctl n (s n)) ^ (m + 1 + 1))
        (QopAlgebra_mollifier d (sz.L n) (m + 1) (sz.lam n))
    have hHm : MeasurableSet {M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ | M.IsHermitian} :=
      (isClosed_eq continuous_id.matrix_conjTranspose continuous_id).measurableSet
    have hT : MeasurableSet {M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ | M.IsHermitian → M ∈ initGood n} := by
      have e : {M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ | M.IsHermitian → M ∈ initGood n} =
          {M | M.IsHermitian}ᶜ ∪ initGood n := by
        ext M; simp [imp_iff_not_or]
      rw [e]
      exact hHm.compl.union hS
    have htr := F.hLaw s v K n 0 (hs0 n) (hsv n).le (hK0 n) _ hT.compl
    rw [ST_gridTime_zero] at htr
    have e1 : (Cm.Hpath s v K n 0 ⁻¹' initGood n)ᶜ =
        {ω | Cm.Hpath s v K n 0 ω ∈ ({M | M.IsHermitian → M ∈ initGood n} : Set (Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ))ᶜ} := by
      ext ω
      have hh := QEndB1Gen_Hpath_herm F.hW s v K n 0 ω
      simp only [Set.mem_compl_iff, Set.mem_preimage, Set.mem_ofPred_eq, not_imp, hh, true_and]
    rw [e1, htr]
    refine le_trans (le_of_eq ?_) hn
    congr 1
  have hW := HighProbAt.inter hsz (HighProbAt.inter hsz (HighProbAt.inter hsz hgood hlin) hyg) hinitP
  have h2ev : ∀ᶠ n in atTop, (2 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) :=
    ((tendsto_rpow_atTop (half_pos hτ)).comp hsize).eventually_ge_atTop 2
  filter_upwards [hpin, hW (D + 2) (by linarith), hsize.eventually_ge_atTop 2, h2ev] with n hG hWn hN2 hhalf
  obtain ⟨G, hGP, hGb⟩ := hG
  have hNn1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by linarith
  have hx0 : (0 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ (-(D + 2)) := Real.rpow_nonneg (by linarith) _
  obtain ⟨ζ₂, hζ₂⟩ : ∃ ζ₂ : ℝ, ζ₂ = (sz.Bctl n (v n)) ^ (1 / 6 : ℝ) * Y (m + 1 + 1) n +
      STbootRHS 1 (fun i => X i n) (fun i => Y i n) (sz.Bctl n (s n)) (m + 1 + 1) p := ⟨_, rfl⟩
  -- the terminal event
  set Sterm : Set (Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) :=
    {M | ∃ x : {σ : Fin (m + 1 + 1) → Bool // σ (Fin.last (m + 1)) = !σ 0} ×
        (Fin (m + 1 + 1) → Zd d (sz.L n)),
      ((sz.size n : ℕ) : ℝ) ^ τ * ζ₂ <
        ‖STLKMg Cm n (v n) M x.1.1 x.2‖ / (sz.Bctl n (v n)) ^ (m + 1 + 1)} with hStermdef
  have hSterm : MeasurableSet Sterm := by
    have heq : Sterm = ⋃ x : {σ : Fin (m + 1 + 1) → Bool // σ (Fin.last (m + 1)) = !σ 0} ×
        (Fin (m + 1 + 1) → Zd d (sz.L n)),
        {M | ((sz.size n : ℕ) : ℝ) ^ τ * ζ₂ <
          ‖STLKMg Cm n (v n) M x.1.1 x.2‖ / (sz.Bctl n (v n)) ^ (m + 1 + 1)} := by
      ext M; simp [hStermdef]
    rw [heq]
    exact MeasurableSet.iUnion fun x =>
      measurableSet_lt measurable_const
        ((QEndB1Gen_meas_STLKMg F.hL n (v n) x.1.1 x.2).norm.div_const _)
  have e1 : μ {ω | Hf n (v n) ω ∈ Sterm} = Cm.Pp (Cm.Hpath s v K n (K n) ⁻¹' Sterm) := by
    have := F.hLaw s v K n (K n) (hs0 n) (hsv n).le (hK0 n) Sterm hSterm
    rw [gridTime_last s v K n (hK0 n)] at this
    exact this.symm
  have hmain : Cm.Pp (Cm.Hpath s v K n (K n) ⁻¹' Sterm) ≤ ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-D)) := by
    refine altQFlow_union2 (B := Gᶜ) hx0 hWn ?_ ?_ (altQFlow_two_pow_le hN2 (by norm_num))
    · rw [← ofReal_measureReal (measure_ne_top Cm.Pp _)]
      exact ENNReal.ofReal_le_ofReal hGP
    · intro ω hω
      by_contra hno
      simp only [Set.mem_union, Set.mem_compl_iff, Set.mem_inter_iff, Set.mem_preimage, Set.mem_ofPred_eq, not_or,
        not_not] at hno
      obtain ⟨⟨⟨⟨hA, hB⟩, hC⟩, hI⟩, hGω⟩ := hno
      obtain ⟨x, hx⟩ := hω
      have hb := hGb ω hGω (fun j hj => ⟨⟨hA j hj, hB j hj⟩, hC j hj⟩) (fun σ hσ a => hI (σ, a) hσ)
        x.1.1 x.1.2 x.2
      have hlev : Λ n ^ ((1 : ℝ) / 2) + Φ₁ n + Φ₂ n + Φ₃ n ≤ ζ₂ := by
        have h1 : Λ n ^ ((1 : ℝ) / 2) + Φ₁ n + Φ₂ n + Φ₃ n ≤ (sz.Bctl n (v n)) ^ (1 / 6 : ℝ) * Y (m + 1 + 1) n +
            STbootRHS 2 (fun i => X i n) (fun i => Y i n) (sz.Bctl n (s n)) (m + 1 + 1) p :=
          altQFlow_level_le (by omega) hp (fun i => hX1 i n) (fun i => hY1 i n) (hBs n)
        have h2 := altQFlow_bootRHS_two_le_one (XL := fun i => X i n) (XLK := fun i => Y i n)
          (B := sz.Bctl n (s n)) (k := m + 1 + 1) (p := p) (fun i => zero_le_one.trans (hY1 i n))
        rw [hζ₂]
        linarith
      have hXl : Xl n ≤ STbootRHS 1 (fun i => X i n) (fun i => Y i n) (sz.Bctl n (s n)) (m + 1 + 1) p :=
        altQFlow0_Ylow_le_bootRHS (XL := fun i => X i n) (XLK := fun i => Y i n) (B := sz.Bctl n (s n))
          (k := m + 1 + 1) (p := p) (by omega) (fun i => zero_le_one.trans (hX1 i n))
          (fun i => zero_le_one.trans (hY1 i n)) (hBs n).le
      have hBY : 0 ≤ (sz.Bctl n (v n)) ^ (1 / 6 : ℝ) * Y (m + 1 + 1) n :=
        mul_nonneg (Real.rpow_nonneg (hBv n).le _) (zero_le_one.trans (hY1 _ n))
      have hXlζ : Xl n ≤ ζ₂ := by rw [hζ₂]; linarith
      have hL0 : 0 ≤ Λ n ^ ((1 : ℝ) / 2) + Φ₁ n + Φ₂ n + Φ₃ n := by
        have h1 := Real.rpow_nonneg (hΛ0 n) ((1 : ℝ) / 2)
        have h2 := hΦ n
        linarith [h2.1, h2.2.1, h2.2.2]
      have hζ0 : 0 ≤ ζ₂ := hL0.trans hlev
      have hBk : 0 < (sz.Bctl n (v n)) ^ (m + 1 + 1) := pow_pos (hBv n) _
      have hdiv : ‖STLKMg Cm n (v n) (Cm.Hpath s v K n (K n) ω) x.1.1 x.2‖ /
          (sz.Bctl n (v n)) ^ (m + 1 + 1) ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) *
            (Λ n ^ ((1 : ℝ) / 2) + Φ₁ n + Φ₂ n + Φ₃ n + Xl n) := (div_le_iff₀ hBk).2 hb
      have hpos : 0 ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) := Real.rpow_nonneg (by linarith) _
      have hsq : ((sz.size n : ℕ) : ℝ) ^ τ =
          ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * ((sz.size n : ℕ) : ℝ) ^ (τ / 2) :=
        (UnifDetDom.rpow_half_mul_rpow_half _ hτ).symm
      have hfin : ((sz.size n : ℕ) : ℝ) ^ (τ / 2) *
          (Λ n ^ ((1 : ℝ) / 2) + Φ₁ n + Φ₂ n + Φ₃ n + Xl n) ≤ ((sz.size n : ℕ) : ℝ) ^ τ * ζ₂ := by
        have h2z : 2 * ζ₂ ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * ζ₂ := mul_le_mul_of_nonneg_right hhalf hζ0
        calc ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * (Λ n ^ ((1 : ℝ) / 2) + Φ₁ n + Φ₂ n + Φ₃ n + Xl n)
            ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * (2 * ζ₂) :=
              mul_le_mul_of_nonneg_left (by linarith) hpos
          _ ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * (((sz.size n : ℕ) : ℝ) ^ (τ / 2) * ζ₂) :=
              mul_le_mul_of_nonneg_left h2z hpos
          _ = _ := by rw [hsq]; ring
      exact absurd hx (not_lt.2 (hdiv.trans hfin))
  have hLMv : ∀ (ω : sz.SeqΩ) {k : ℕ} (σ' : Fin k → Bool) (a' : Fin k → Zd d (sz.L n)),
      STLKMg Cm n (v n) (Hf n (v n) ω) σ' a' = Cm.L n (v n) σ' a' ω - Cm.K n (v n) σ' a' := by
    intro ω k σ' a'
    unfold STLKMg STLMg
    rw [GridGoodGen_LM_eq_L F.hL F.hC n (v n) σ' a' ω]
  calc μ (badSetAt sz.size _ _ τ n) = μ {ω | Hf n (v n) ω ∈ Sterm} := by
        congr 1
        ext ω
        simp only [badSetAt, Set.mem_ofPred_eq, hStermdef, hζ₂, hLMv]
    _ = Cm.Pp (Cm.Hpath s v K n (K n) ⁻¹' Sterm) := e1
    _ ≤ _ := hmain

end CoreProof

section SectionProof

variable {d : ℕ}

/-- **The endpoint at an arbitrary pair** `q n = ((w_n, u_n), _)` of the parameter set `STPair s t` (band `altQFlow0_section`, `QEndB1:1594`;
`perTimeDomAt_iff_forall_section`): `Ξ̂^{(𝓛-𝒦)}_{w_n, m+2} ≺ B_{u_n}^{1/6} XLK (m+2) u_n + STbootRHS 1 … B_s (m+2) p`.  The window of the endpoint is `[s, v]` with
`v_n = w_n` where `s_n < w_n` and `v_n = t_n` elsewhere, the controls are frozen at `uu_n` (`u_n` resp. `t_n`); at a non-collapsed index the alternating part is
`QEndB1Gen_core` and the non-alternating part `QEndB1Gen_nq_half` (bound with `STbootRHS 2 ≤ STbootRHS 1`), at a collapsed index `w_n = s_n` it is `STLKgL s`. -/
private theorem QEndB1Gen_section {sz : Sizes d} (Cm : Step2Mat sz) (μ : Measure sz.SeqΩ)
    {Hf : ∀ n : ℕ, ℝ → sz.SeqΩ → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ}
    {E lam' gK : ℕ → ℝ} {Ψ : ∀ n : ℕ, Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ} {κm A C₆ K₆ 𝔠 τR 𝔡 : ℝ}
    (F : QEndB1Gen_Facts Cm μ Hf E lam' gK Ψ κm A C₆ K₆ 𝔡) {s t : ℕ → ℝ} (hd : 3 ≤ d) (h𝔠 : 0 < 𝔠) (hτR : 0 < τR) (h𝔡 : 0 < 𝔡)
    (hKb : STKboundgL Cm.toFlowFM μ) (hsize : sz.SizeTendsto) (hband : sz.Bandwidth 𝔠) (hWO : sz.WO 𝔡)
    (hs0 : ∀ n, 0 ≤ s n) (hst : ∀ n, s n < t n) (ht1 : ∀ n, t n < 1) (hcase : sz.STCaseI s t) (hrange : sz.RangeCond τR t)
    (hWt : ∀ᶠ n : ℕ in atTop, (((sz.W n : ℕ) : ℝ))⁻¹ ≤ (1 - t n) / (1 - s n))
    (hLK : STLKgL Cm.toFlowFM μ s) (hDecay : STDecayLoopUgL Cm.toFlowFM μ s t)
    (hGrid : ∀ v : ℕ → ℝ, (∀ n, s n < v n) → (∀ n, v n ≤ t n) → GridGoodNConclg Cm μ s v) (hLin : NQLinConclg Cm μ s t)
    (hNQ : ∀ t' : ℕ → ℝ, (∀ n, s n < t' n) → (∀ n, t' n ≤ t n) → STNQConclPTgL'' Cm.toFlowFM μ s t')
    {m p : ℕ} (hp : 1 ≤ p) {C4 Cv : ℝ} (hC4 : 0 < C4) (hC4Cv : C4 ≤ Cv) (hAk0 : C4 < Cv ∨ A = 1)
    (hKer : ∀ᶠ n : ℕ in atTop, QProxyG_KerEK4 Cm.toFlowFM gK (m + 1 + 1) (1 / 𝔠) C4 n)
    {XL XLK : ℕ → ℕ → ℝ → ℝ} (hXL : ∀ i n u, 1 ≤ XL i n u) (hXLK : ∀ i n u, 1 ≤ XLK i n u)
    (hXLp : ∀ i, 1 ≤ i → STlenL (m + 1 + 1) p i →
      PrecL sz μ (U := STPair s t) (fun n q ω => STXiLg Cm.toFlowFM n q.1.1 i ω) (fun n q _ => XL i n q.1.2))
    (hXLKp : ∀ i, 1 ≤ i → i ≤ m + 1 + 1 →
      PrecL sz μ (U := STPair s t) (fun n q ω => STXiLKg Cm.toFlowFM n q.1.1 i ω) (fun n q _ => XLK i n q.1.2))
    (q : ∀ n, STPair s t n) :
    StochDomAt μ sz.size
      (fun n (_ : Unit) ω => STXiLKg Cm.toFlowFM n (q n).1.1 (m + 1 + 1) ω)
      (fun n (_ : Unit) _ => (sz.Bctl n (q n).1.2) ^ (1 / 6 : ℝ) * XLK (m + 1 + 1) n (q n).1.2 +
        STbootRHS 1 (fun i => XL i n (q n).1.2) (fun i => XLK i n (q n).1.2) (sz.Bctl n (s n))
          (m + 1 + 1) p) := by
  classical
  -- the window `v`, the frozen controls `uu`
  obtain ⟨v, hvdef⟩ : ∃ v : ℕ → ℝ, v = fun n => if s n < (q n).1.1 then (q n).1.1 else t n := ⟨_, rfl⟩
  obtain ⟨uu, huudef⟩ : ∃ uu : ℕ → ℝ, uu = fun n => if s n < (q n).1.1 then (q n).1.2 else t n := ⟨_, rfl⟩
  have hv_pos : ∀ n, s n < (q n).1.1 → v n = (q n).1.1 := fun n h => by simp only [hvdef, h, ↓reduceIte]
  have hv_neg : ∀ n, ¬ s n < (q n).1.1 → v n = t n := fun n h => by simp only [hvdef, h, ↓reduceIte]
  have hu_pos : ∀ n, s n < (q n).1.1 → uu n = (q n).1.2 := fun n h => by simp only [huudef, h, ↓reduceIte]
  have hu_neg : ∀ n, ¬ s n < (q n).1.1 → uu n = t n := fun n h => by simp only [huudef, h, ↓reduceIte]
  have hsv : ∀ n, s n < v n := fun n => by
    by_cases h : s n < (q n).1.1
    · rw [hv_pos n h]; exact h
    · rw [hv_neg n h]; exact hst n
  have hvu : ∀ n, v n ≤ uu n := fun n => by
    by_cases h : s n < (q n).1.1
    · rw [hv_pos n h, hu_pos n h]; exact (q n).2.2.1
    · rw [hv_neg n h, hu_neg n h]
  have hut : ∀ n, uu n ≤ t n := fun n => by
    by_cases h : s n < (q n).1.1
    · rw [hu_pos n h]; exact (q n).2.2.2
    · rw [hu_neg n h]
  have hvt : ∀ n, v n ≤ t n := fun n => (hvu n).trans (hut n)
  have hsu : ∀ n, s n < uu n := fun n => (hsv n).trans_le (hvu n)
  have hwu : ∀ n, (q n).1.1 ≤ uu n := fun n => by
    by_cases h : s n < (q n).1.1
    · rw [hu_pos n h]; exact (q n).2.2.1
    · have : (q n).1.1 = s n := le_antisymm (not_lt.1 h) (q n).2.1
      rw [hu_neg n h, this]; exact (hst n).le
  have hBs : ∀ n, 0 < sz.Bctl n (s n) := fun n => st_Bctl_pos sz ((hst n).trans (ht1 n))
  -- the restricted pair hypotheses on `[s, v]` with the controls at `uu`
  have hX : ∀ i : ℕ, 1 ≤ i → STlenL (m + 1 + 1) p i →
      PrecL sz μ (U := fun n => TimeIcc s v n) (fun n u ω => STXiLg Cm.toFlowFM n (u : ℝ) i ω)
        (fun n _ _ => XL i n (uu n)) := fun i hi hl =>
    StochDomAt.precomp_param (V := fun n => TimeIcc s v n) (hXLp i hi hl)
      (fun n w' => (⟨((w' : ℝ), uu n), w'.2.1, w'.2.2.trans (hvu n), hut n⟩ : STPair s t n))
  have hY : ∀ i : ℕ, 1 ≤ i → i ≤ m + 1 + 1 →
      PrecL sz μ (U := fun n => TimeIcc s v n) (fun n u ω => STXiLKg Cm.toFlowFM n (u : ℝ) i ω)
        (fun n _ _ => XLK i n (uu n)) := fun i hi hl =>
    StochDomAt.precomp_param (V := fun n => TimeIcc s v n) (hXLKp i hi hl)
      (fun n w' => (⟨((w' : ℝ), uu n), w'.2.1, w'.2.2.trans (hvu n), hut n⟩ : STPair s t n))
  have hAlt := QEndB1Gen_core Cm μ F hd h𝔠 hτR h𝔡 hKb hsize hband hWO hs0 (fun n => (hst n).le) ht1 hcase hrange hWt
    hsv hvt hLK hDecay (hGrid v hsv hvt) hLin hp hC4 hC4Cv hAk0 hKer (X := fun i n => XL i n (uu n))
    (Y := fun i n => XLK i n (uu n)) (fun i n => hXL i n _) (fun i n => hXLK i n _) hX hY
  have hNQh := QEndB1Gen_nq_half Cm.toFlowFM μ hsize (w := fun n => (q n).1.1) (n_ := m + 1 + 1) (by omega) hp hXL hXLK hXLp
    hXLKp (fun n => (q n).2.1) hwu hut (hNQ uu hsu hut)
  have hcoll := QEndB1Gen_collapsed hLK (k := m + 1 + 1) (by omega) hBs
  have h2ev : ∀ τ : ℝ, 0 < τ → ∀ᶠ n in atTop, (2 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) := fun τ hτ =>
    ((tendsto_rpow_atTop (half_pos hτ)).comp hsize).eventually_ge_atTop 2
  intro τ hτ D hD
  filter_upwards [hAlt (τ / 2) (half_pos hτ) (D + 1) (by linarith), hNQh (τ / 2) (half_pos hτ) (D + 1) (by linarith),
    hcoll (τ / 2) (half_pos hτ) (D + 1) (by linarith), hsize.eventually_ge_atTop 2, h2ev τ hτ] with n h1 h2 h3 hN2 hhalf
  have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by linarith
  have hN0 : (0 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ (-(D + 1)) := Real.rpow_nonneg (by linarith) _
  have hu1 : (q n).1.2 < 1 := ((q n).2.2.2).trans_lt (ht1 n)
  have hw1 : (q n).1.1 < 1 := ((q n).2.2.1).trans_lt hu1
  have hBw : 0 < sz.Bctl n (q n).1.1 := st_Bctl_pos sz hw1
  have hBu : 0 < sz.Bctl n (q n).1.2 := st_Bctl_pos sz hu1
  have hBwu : sz.Bctl n (q n).1.1 ≤ sz.Bctl n (q n).1.2 := STBctl_mono sz n (q n).2.2.1 hu1
  have hNτ : 0 ≤ ((sz.size n : ℕ) : ℝ) ^ τ := Real.rpow_nonneg (by linarith) _
  have hpos : 0 ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) := Real.rpow_nonneg (by linarith) _
  have hsq : ((sz.size n : ℕ) : ℝ) ^ τ =
      ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * ((sz.size n : ℕ) : ℝ) ^ (τ / 2) :=
    (UnifDetDom.rpow_half_mul_rpow_half _ hτ).symm
  -- the right side `ζ` of the pin at the pair, and its lower bound `1 ≤ ζ`
  obtain ⟨ζ, hζ⟩ : ∃ ζ : ℝ, ζ = (sz.Bctl n (q n).1.2) ^ (1 / 6 : ℝ) * XLK (m + 1 + 1) n (q n).1.2 +
      STbootRHS 1 (fun i => XL i n (q n).1.2) (fun i => XLK i n (q n).1.2) (sz.Bctl n (s n)) (m + 1 + 1) p :=
    ⟨_, rfl⟩
  have hζ1 : 1 ≤ ζ := by
    have h0 : 0 ≤ (sz.Bctl n (q n).1.2) ^ (1 / 6 : ℝ) * XLK (m + 1 + 1) n (q n).1.2 :=
      mul_nonneg (Real.rpow_nonneg hBu.le _) (zero_le_one.trans (hXLK _ _ _))
    have := altQFlow_bootRHS_one_le (lo := 1) (XL := fun i => XL i n (q n).1.2)
      (XLK := fun i => XLK i n (q n).1.2) (B := sz.Bctl n (s n)) (k := m + 1 + 1) (p := p) (by omega)
      (fun i => hXL _ _ _) (fun i => zero_le_one.trans (hXLK _ _ _)) (hBs n).le
    rw [hζ]; linarith
  by_cases hn' : s n < (q n).1.1
  · -- non-collapsed: `v n = w_n`, `uu n = u_n`; the union of the alternating and non-alternating parts
    have hv : v n = (q n).1.1 := hv_pos n hn'
    have hu : uu n = (q n).1.2 := hu_pos n hn'
    refine altQFlow_union2 hN0 h1 h2 ?_ (altQFlow_two_pow_le hN2 (by norm_num))
    intro ω hω
    by_contra hno
    simp only [Set.mem_union, badSetAt, Set.mem_ofPred_eq, not_or, not_exists, not_lt] at hno
    obtain ⟨hnoA, hnoB⟩ := hno
    rw [hv, hu] at hnoA
    rw [hu] at hnoB
    simp only [badSetAt, Set.mem_ofPred_eq] at hω
    obtain ⟨_, hω⟩ := hω
    obtain ⟨ζA, hζA⟩ : ∃ ζA : ℝ, ζA = (sz.Bctl n (q n).1.1) ^ (1 / 6 : ℝ) * XLK (m + 1 + 1) n (q n).1.2 +
        STbootRHS 1 (fun i => XL i n (q n).1.2) (fun i => XLK i n (q n).1.2) (sz.Bctl n (s n)) (m + 1 + 1) p :=
      ⟨_, rfl⟩
    have hmax : ∀ x : (Fin (m + 1 + 1) → Bool) × (Fin (m + 1 + 1) → Zd d (sz.L n)),
        ‖Cm.L n (q n).1.1 x.1 x.2 ω - Cm.K n (q n).1.1 x.1 x.2‖ /
          (sz.Bctl n (q n).1.1) ^ (m + 1 + 1) ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * ζA := by
      intro x
      by_cases hσ : x.1 (Fin.last (m + 1)) = !x.1 0
      · rw [hζA]; exact hnoA (⟨x.1, hσ⟩, x.2)
      · have hσ0 : x.1 (Fin.last (m + 1)) = x.1 0 := by
          revert hσ
          generalize x.1 (Fin.last (m + 1)) = b
          generalize x.1 0 = c
          cases b <;> cases c <;> simp
        have hσ' : ∃ k, x.1 k = x.1 (finRotate (m + 1 + 1) k) :=
          ⟨Fin.last (m + 1), by rw [finRotate_last]; exact hσ0⟩
        have hB2 := altQFlow_bootRHS_two_le_one (XL := fun i => XL i n (q n).1.2)
          (XLK := fun i => XLK i n (q n).1.2) (B := sz.Bctl n (s n)) (k := m + 1 + 1) (p := p)
          (fun i => zero_le_one.trans (hXLK _ _ _))
        refine (hnoB (⟨x.1, hσ'⟩, x.2)).trans (mul_le_mul_of_nonneg_left ?_ hpos)
        rw [hζA]; linarith
    have hXi := QEndB1Gen_xi_le Cm.toFlowFM hBw hmax
    have hζA1 : 1 ≤ ζA := by
      have h0 : 0 ≤ (sz.Bctl n (q n).1.1) ^ (1 / 6 : ℝ) * XLK (m + 1 + 1) n (q n).1.2 :=
        mul_nonneg (Real.rpow_nonneg hBw.le _) (zero_le_one.trans (hXLK _ _ _))
      have := altQFlow_bootRHS_one_le (lo := 1) (XL := fun i => XL i n (q n).1.2)
        (XLK := fun i => XLK i n (q n).1.2) (B := sz.Bctl n (s n)) (k := m + 1 + 1) (p := p) (by omega)
        (fun i => hXL _ _ _) (fun i => zero_le_one.trans (hXLK _ _ _)) (hBs n).le
      rw [hζA]; linarith
    have hζAle : ζA ≤ ζ := by
      have e1 : (sz.Bctl n (q n).1.1) ^ (1 / 6 : ℝ) ≤ (sz.Bctl n (q n).1.2) ^ (1 / 6 : ℝ) :=
        Real.rpow_le_rpow hBw.le hBwu (by norm_num)
      have e3 := mul_le_mul_of_nonneg_right e1 (zero_le_one.trans (hXLK (m + 1 + 1) n (q n).1.2))
      rw [hζA, hζ]; linarith
    have hfin : 1 + ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * ζA ≤ ((sz.size n : ℕ) : ℝ) ^ τ * ζ := by
      have hN1' : 1 ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) := by linarith
      calc 1 + ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * ζA
          ≤ ζA + ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * ζA := by linarith
        _ ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * ζA + ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * ζA := by
            have := mul_le_mul_of_nonneg_right hN1' (by linarith : (0 : ℝ) ≤ ζA)
            linarith
        _ = 2 * (((sz.size n : ℕ) : ℝ) ^ (τ / 2) * ζA) := by ring
        _ ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * (((sz.size n : ℕ) : ℝ) ^ (τ / 2) * ζA) :=
            mul_le_mul_of_nonneg_right hhalf (mul_nonneg hpos (by linarith))
        _ = ((sz.size n : ℕ) : ℝ) ^ τ * ζA := by rw [hsq]; ring
        _ ≤ ((sz.size n : ℕ) : ℝ) ^ τ * ζ := mul_le_mul_of_nonneg_left hζAle hNτ
    rw [← hζ] at hω
    exact absurd hω (not_lt.2 (hXi.trans hfin))
  · -- collapsed: `w_n = s_n`, `STLKgL s`
    have hw : (q n).1.1 = s n := le_antisymm (not_lt.1 hn') (q n).2.1
    refine le_trans (measure_mono ?_) (h3.trans (ENNReal.ofReal_le_ofReal
      (Real.rpow_le_rpow_of_exponent_le hN1 (by linarith))))
    intro ω hω
    simp only [badSetAt, Set.mem_ofPred_eq] at hω ⊢
    obtain ⟨_, hω⟩ := hω
    by_contra hno
    push Not at hno
    have hmax : ∀ x : (Fin (m + 1 + 1) → Bool) × (Fin (m + 1 + 1) → Zd d (sz.L n)),
        ‖Cm.L n (q n).1.1 x.1 x.2 ω - Cm.K n (q n).1.1 x.1 x.2‖ /
          (sz.Bctl n (q n).1.1) ^ (m + 1 + 1) ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) := by
      intro x
      rw [hw]
      simpa using hno x
    have hXi := QEndB1Gen_xi_le Cm.toFlowFM hBw hmax
    have hN1' : 1 ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) := by linarith
    rw [← hζ] at hω
    have : 1 + ((sz.size n : ℕ) : ℝ) ^ (τ / 2) ≤ ((sz.size n : ℕ) : ℝ) ^ τ * ζ := by
      calc 1 + ((sz.size n : ℕ) : ℝ) ^ (τ / 2) ≤ 2 * ((sz.size n : ℕ) : ℝ) ^ (τ / 2) := by linarith
        _ ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * ((sz.size n : ℕ) : ℝ) ^ (τ / 2) :=
            mul_le_mul_of_nonneg_right hhalf hpos
        _ = ((sz.size n : ℕ) : ℝ) ^ τ := hsq.symm
        _ = ((sz.size n : ℕ) : ℝ) ^ τ * 1 := (mul_one _).symm
        _ ≤ ((sz.size n : ℕ) : ℝ) ^ τ * ζ := mul_le_mul_of_nonneg_left hζ1 hNτ
    exact absurd hω (not_lt.2 (hXi.trans this))

end SectionProof

/-! ## 3. Target 12: the per-time round `stOeqQtRoundPTgL''_of`

The family-premise table of the ticket (rows as numbered there): 1 `hSE`; 2 `hFlow`; 3 `hL`, `hm` (inline `‖m‖ ≤ 1`); 4 `hW`; 5 `hLaw`, `hC`; 6 `hSpec`, `hWard`, `hKcal`, `hEK`;
7 `hRow` (and the walk's variance law `hSeq`, `hS`); 8 D1 `hEK4 : QProxyG_KerEK4Fam` (`∃ C4` after `(k, κ, ε, 𝔡, KL)`, before `(sz, z)`; used at `KL = 1/𝔠` after the flow's
`𝔠` is introduced) and `hKerFam` of the non-alternating half; 9 `hTh` (the `Θ`-decay class, `∃ C₆` after `(𝔡, κ)`: Amend 1) and `hB45` (`B45Gen_Facts`, constant `K₆ = max C₆' 1`);
10 `hR1` (R1 with the pinned `Aof κ`); 11 D2: `hExp hKL hKT hU` (eventual in `n`) and the all-`w` link `hKK`; 12 `hT0`.  Rows 1-7 and 10-12 and `hKerFam` are the premises of
`stOeqNQPTgL''_of` unchanged (row 13); rows 8 (`hEK4`) and 9 (`hTh`, `hB45`) are new. -/

section Public

/-- **Target 12, `stOeqQtRoundPTgL''_of`** (conclusion = `T2498_OeqQtRoundPTgL''`, binding; band `stOeqQtRoundPT''_holds`, `QEndB1:1841`): the per-time round of
`lem:STOeq_Qt` over a carrier family from the family-premise table.  `𝔠_d = min (min (min 𝔠G 𝔠L) 𝔠N) (1/(2d))` with `𝔠G`, `𝔠L`, `𝔠N` the constants of `gridGoodNgL_of`,
`nqLinGoodgL_of` and `stOeqNQPTgL''_of` at the same `(κ, ε, 𝔡, C_d)`: `d 𝔠_d ≤ 1/2 < 1` for `st_window`, and `STConStInd` passes to the larger exponents; the good events
are re-instantiated on every window `[s, v]` (`st_conStInd_sub`, the restriction of `STStep2ConclgL`), the decay `STDecayLoopUgL` is `stDecayLoopUgL_of_step2`, the
non-alternating half is `stOeqNQPTgL''_of` on every window `[s, t']`; then `perTimeDomAt_iff_forall_section` and `QEndB1Gen_section`.  The kernel constant `C4` is
D1 at `k = n_ = m + 2`, `KL = 1/𝔠`; the vocabulary constant is `Cv = C4 + 1` (R1: `A = Aof κ`). -/
theorem stOeqQtRoundPTgL''_of (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ)
    (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop) (mkM : ∀ (sz : Sizes d) (z : ℕ → ℂ), Step2Mat sz)
    (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ)
    (Hf : ∀ (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ), ℝ → sz.SeqΩ → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    (E lam' gK : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ)
    (Ψ : ∀ (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ), Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    (Aof : ℝ → ℝ)
    -- ticket rows 1-6: the premises of `gridGoodNgL_of` and `nqLinGoodgL_of`
    (hSE : STSEforLngL d STAny law Flow mkM Hf T0) (hFlow : Step2EventsGen_Flow d Flow T0)
    (hSpec : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z →
      ∃ κm, DecayGen_Spec (mkM sz z).toFlowFM κm)
    (hL : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z →
      StepDecompGen_LoopForm (mkM sz z) (E sz z))
    (hW : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z →
      StepDecompGen_WalkForm (mkM sz z) (lam' sz z) (Ψ sz z))
    (hLaw : ∀ (sz : Sizes d) (z : ℕ → ℂ), Step2EventsGen_Law (mkM sz z) (law sz) (Hf sz z))
    (hC : ∀ (sz : Sizes d) (z : ℕ → ℂ), Step34Gen_LCompat (mkM sz z) (Hf sz z))
    (hWard : ∀ (sz : Sizes d) (z : ℕ → ℂ), DecayGen_WardPair (mkM sz z).toFlowFM)
    (hKcal : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z →
      STKcalDecaygL (mkM sz z).toFlowFM)
    (hEK : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z → ∀ s t : ℕ → ℝ,
      (∀ n, 0 ≤ s n) → (∀ n, s n ≤ t n) → (∀ n, t n < 1) → STDecayLoopUgL (mkM sz z).toFlowFM (law sz) s t →
      ∀ k : ℕ, 2 ≤ k → ∀ σ : Fin k → Bool,
        STEKDecaygL (law sz) s t (m := k) (fun n v ω (a : Fin k → Zd d (sz.L n)) =>
          STegtg (mkM sz z) (Hf sz z) n (v : ℝ) ω ⟨List.ofFn σ, List.ofFn a⟩) ∧
        (∀ l : ℕ, STEKDecaygL (law sz) s t (m := k) (fun n v ω (a : Fin k → Zd d (sz.L n)) =>
          STksimLKg (mkM sz z) (Hf sz z) n (v : ℝ) ω l ⟨List.ofFn σ, List.ofFn a⟩)) ∧
        STEKDecaygL (law sz) s t (m := k) (fun n v ω (a : Fin k → Zd d (sz.L n)) =>
          STelklkg (mkM sz z) (Hf sz z) n (v : ℝ) ω ⟨List.ofFn σ, List.ofFn a⟩) ∧
        STEKDecaygL (law sz) s t (m := k + k) (fun n v ω (b : Fin (k + k) → Zd d (sz.L n)) =>
          STeeg (mkM sz z) (Hf sz z) n (v : ℝ) ω σ (fun i => b (Fin.castAdd k i)) (fun i => b (Fin.natAdd k i))))
    -- ticket rows 3, 4, 7, 11: the spectral data, the walk's variance law, the kernel class, the drift classes
    (hm : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z → ∀ n, ‖(mkM sz z).m n‖ ≤ 1)
    (hSeq : ∀ (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ), (mkM sz z).S n = SB d (sz.L n) (lam' sz z n))
    (hS : ∀ (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ) (a : Zd d (sz.L n)), ∑ b : Zd d (sz.L n), ‖(mkM sz z).S n a b‖ ≤ 1)
    (hRow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z →
      ∀ n, GridRepTailGen_Ker (mkM sz z).toFlowFM n)
    (hKK : ∀ (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ) (w : ℝ) (k : ℕ) (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)),
      (mkM sz z).KI n w (KLloopOf d (sz.L n) σ a) = (mkM sz z).K n w σ a)
    (hExp : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z →
      ∀ᶠ n : ℕ in atTop, ∀ (s' t' : ℕ → ℝ) (K' : ℕ → ℕ), HierDriftGen_Expand (mkM sz z) s' t' K' n)
    (hKL : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z →
      ∀ᶠ n : ℕ in atTop, HierDriftGen_KLoop (mkM sz z) n)
    (hKT : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z →
      ∀ᶠ n : ℕ in atTop, HierDriftGen_KTwo (mkM sz z) n)
    (hU : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z →
      ∀ᶠ n : ℕ in atTop, HierDriftGen_UStep (mkM sz z).toFlowFM n)
    -- ticket row 8 (D1 of the non-alternating half, `∃ Ck` before `(sz, z)`), row 10 (R1, the pinned `Aof κ`), row 12 (the flow window)
    (hKerFam : NQGoodGen_KerNALFam d Flow (fun sz z => (mkM sz z).toFlowFM) gK)
    (hR1 : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z →
      1 ≤ Aof κ ∧ ∀ n, 0 ≤ gK sz z n * sz.lam n ∧ gK sz z n ^ 2 ≤ sz.lam n ^ 2 ∧ sz.lam n ^ 2 ≤ Aof κ * gK sz z n ^ 2)
    (hT0 : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → 0 < ε → Flow sz κ ε 𝔠 𝔡 z →
      ∃ τ : ℝ, 0 < τ ∧ sz.RangeCond τ (T0 sz z))
    -- ticket row 8 (D1 of the alternating endpoint, `∃ C4` before `(sz, z)`) and row 9 (the `Θ`-decay class, `∃ C₆` after `(𝔡, κ)`, Amend 1; `B45Gen_Facts`)
    (hEK4 : QProxyG_KerEK4Fam d Flow (fun sz z => (mkM sz z).toFlowFM) gK)
    (hTh : ∀ 𝔡 : ℝ, 0 < 𝔡 → ∀ κ : ℝ, 0 < κ → ∃ C₆ : ℝ, 0 < C₆ ∧ ∀ (sz : Sizes d) (ε 𝔠 : ℝ) (z : ℕ → ℂ),
      Flow sz κ ε 𝔠 𝔡 z → Step5KerGen_ThDecay (mkM sz z).toFlowFM (gK sz z) 𝔡⁻¹ C₆)
    (hB45 : B45Gen_Facts d Flow (fun sz z => (mkM sz z).toFlowFM)) :
    STOeqQtRoundPTgL'' d law Flow (fun sz z => (mkM sz z).toFlowFM) T0 := by
  have hGG := gridGoodNgL_of d law Flow mkM T0 Hf E lam' Ψ hSE hFlow hSpec hL hW hLaw hC hWard hKcal hEK
  have hNL := nqLinGoodgL_of d law Flow mkM T0 Hf E lam' Ψ hSE hFlow hL hW hLaw hC
  have hNN := stOeqNQPTgL''_of d law Flow mkM T0 Hf E lam' gK Ψ Aof hSE hFlow hSpec hL hW hLaw hC hWard hKcal hEK hm hSeq hS hRow hKK
    hExp hKL hKT hU hKerFam hR1 hT0
  intro hd κ ε 𝔡 hκ hε h𝔡 Cd hCd
  obtain ⟨𝔠G, hG0, hG1, HG⟩ := hGG hd κ ε 𝔡 hκ hε h𝔡 Cd hCd
  obtain ⟨𝔠L, hL0, hL1, HL⟩ := hNL hd κ ε 𝔡 hκ hε h𝔡 Cd hCd
  obtain ⟨𝔠N, hN0, hN1, HN⟩ := hNN hd κ ε 𝔡 hκ hε h𝔡 Cd hCd
  obtain ⟨C₆, hC₆, hThAll⟩ := hTh 𝔡 h𝔡 κ hκ
  obtain ⟨K₆', hK₆', hB45All⟩ := hB45 κ hκ
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hd2 : (0 : ℝ) < 1 / (2 * d) := by positivity
  obtain ⟨𝔠d, h𝔠d⟩ : ∃ 𝔠d : ℝ, 𝔠d = min (min (min 𝔠G 𝔠L) 𝔠N) (1 / (2 * d)) := ⟨_, rfl⟩
  have h𝔠d0 : 0 < 𝔠d := by rw [h𝔠d]; exact lt_min (lt_min (lt_min hG0 hL0) hN0) hd2
  have h𝔠dG : 𝔠d ≤ 𝔠G := by
    rw [h𝔠d]; exact (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_left _ _))
  have h𝔠dL : 𝔠d ≤ 𝔠L := by
    rw [h𝔠d]; exact (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_right _ _))
  have h𝔠dN : 𝔠d ≤ 𝔠N := by rw [h𝔠d]; exact (min_le_left _ _).trans (min_le_right _ _)
  have h𝔠dd : 𝔠d ≤ 1 / (2 * d) := by rw [h𝔠d]; exact min_le_right _ _
  refine ⟨𝔠d, h𝔠d0, h𝔠dG.trans hG1, ?_⟩
  intro 𝔠 sz z hflow s t hs hst ht hR hK hKw hLK hcon hStep2
  have hA := hFlow.1 sz κ ε 𝔠 𝔡 z hflow
  have ht1 : ∀ n, t n < 1 := fun n => (ht n).trans_lt (hFlow.2 sz κ ε 𝔠 𝔡 z hκ hflow n)
  obtain ⟨τ0, hτ0, hrange0⟩ := hT0 sz κ ε 𝔠 𝔡 z hκ hε hflow
  have hrange : sz.RangeCond τ0 t := nqEnd_rangeCond_mono sz le_rfl ht hrange0
  have hconG : sz.STConStInd 𝔠G s t := altQFlow_conStInd_exp_mono sz h𝔠d0 h𝔠dG ht1 hcon
  have hconL : sz.STConStInd 𝔠L s t := altQFlow_conStInd_exp_mono sz h𝔠d0 h𝔠dL ht1 hcon
  have hconN : sz.STConStInd 𝔠N s t := altQFlow_conStInd_exp_mono sz h𝔠d0 h𝔠dN ht1 hcon
  have hdc : (d : ℝ) * 𝔠d < 1 := by
    calc (d : ℝ) * 𝔠d ≤ d * (1 / (2 * d)) := mul_le_mul_of_nonneg_left h𝔠dd hd0.le
      _ = 1 / 2 := by field_simp
      _ < 1 := by norm_num
  have hWt := st_window sz h𝔠d0 hdc hcon hA.2.2.2.2 (scaleFacts3_W_tendsto sz hA) hs ht1
  have hGrid : ∀ v : ℕ → ℝ, (∀ n, s n < v n) → (∀ n, v n ≤ t n) → GridGoodNConclg (mkM sz z) (law sz) s v :=
    fun v hsv hvt => HG 𝔠 sz z hflow s v hs hsv (fun n => (hvt n).trans (ht n)) trivial hK hKw hLK
      (st_conStInd_sub sz hG0 hconG (fun n => le_rfl) hsv hvt ht1) (NQEndFlowGen_step2_restrict hvt hStep2)
  have hLin : NQLinConclg (mkM sz z) (law sz) s t :=
    HL 𝔠 sz z hflow s t hs hst ht trivial hK hKw hLK hconL hStep2
  obtain ⟨κm, hspec⟩ := hSpec sz κ ε 𝔠 𝔡 z hκ hflow
  have hDecay : STDecayLoopUgL (mkM sz z).toFlowFM (law sz) s t :=
    stDecayLoopUgL_of_step2 hd sz (mkM sz z).toFlowFM (law sz) κm 𝔠 𝔡 s t Cd hspec hA hs ht1 (hWard sz z)
      (hKcal sz κ ε 𝔠 𝔡 z hκ hflow) hStep2.2.2
  have hNQ : ∀ t' : ℕ → ℝ, (∀ n, s n < t' n) → (∀ n, t' n ≤ t n) → STNQConclPTgL'' (mkM sz z).toFlowFM (law sz) s t' :=
    fun t' hst' ht't =>
      HN 𝔠 sz z hflow s t' hs hst' (fun n => (ht't n).trans (ht n)) (fun n => (hR n).trans (by linarith [ht't n]))
        hK hKw hLK (st_conStInd_sub sz hN0 hconN (fun n => le_rfl) hst' ht't ht1)
        (NQEndFlowGen_step2_restrict ht't hStep2)
  have hr1 := hR1 sz κ ε 𝔠 𝔡 z hκ hflow
  obtain ⟨hward, -, -, hker, hrc⟩ := hB45All sz ε 𝔠 𝔡 z hflow
  have F : QEndB1Gen_Facts (mkM sz z) (law sz) (Hf sz z) (E sz z) (lam' sz z) (gK sz z) (Ψ sz z) κm (Aof κ) C₆ (max K₆' 1) 𝔡 :=
    ⟨hL sz κ ε 𝔠 𝔡 z hκ hflow, hW sz κ ε 𝔠 𝔡 z hκ hflow, hspec, hm sz κ ε 𝔠 𝔡 z hκ hflow, hSeq sz z, hS sz z,
      hRow sz κ ε 𝔠 𝔡 z hκ hflow, hKK sz z, hExp sz κ ε 𝔠 𝔡 z hκ hflow, hKL sz κ ε 𝔠 𝔡 z hκ hflow,
      hKT sz κ ε 𝔠 𝔡 z hκ hflow, hU sz κ ε 𝔠 𝔡 z hκ hflow, hLaw sz z, hC sz z, hr1.2, hr1.1, hward, hker, le_max_right _ _,
      fun n σ σ' t ht0 ht1 a => ((hrc n σ σ' t ht0 ht1).1 a).trans
        (div_le_div_of_nonneg_right (le_max_left _ _) (by linarith)),
      fun n σ σ' t ht0 ht1 b => ((hrc n σ σ' t ht0 ht1).2 b).trans
        (div_le_div_of_nonneg_right (le_max_left _ _) (by linarith)),
      hThAll sz ε 𝔠 z hflow, hC₆.le⟩
  intro n_ p hn hp XL XLK hXL hXLK hXLp hXLKp
  obtain ⟨m, rfl⟩ : ∃ m, n_ = m + 1 + 1 := ⟨n_ - 2, by omega⟩
  obtain ⟨C4, hC4, hKerAll⟩ := hEK4 hd (m + 1 + 1) (by omega) κ ε 𝔡 (1 / 𝔠) hκ hε h𝔡 (by have := hA.1; positivity)
  have hKer := hKerAll sz 𝔠 z hflow
  refine (perTimeDomAt_iff_forall_section (law sz) sz.size
    (fun n => ⟨(s n, s n), le_rfl, le_rfl, (hst n).le⟩) _ _).2 ?_
  intro q
  exact QEndB1Gen_section (mkM sz z) (law sz) F hd hA.1 hτ0 hA.2.1 hK hA.2.2.1 hA.2.2.2.1 hA.2.2.2.2 hs hst ht1 hR hrange hWt hLK
    hDecay hGrid hLin hNQ hp (C4 := C4) (Cv := C4 + 1) hC4 (by linarith) (Or.inl (by linarith)) hKer hXL hXLK hXLp hXLKp q

end Public

/-! ## 4. The band re-derivation of `stOeqQtRoundPT''_holds` (every `d`)

The band family `(seqP, STFlow, bandStep2Mat · (STflowE ·), lemT)`, `Hf = seqHflow`, `E = STflowE`, `lam' = sz.lam`, `Ψ = 0`, `gK = sz.lam`, `Aof = 1`: rows 1-12 are the
discharges of `stOeqNQPTgL''_band` (`Chain/NQEndFlowGen.lean`); row 8 (D1) is `qProxyG_kerEK4_band`; row 9 is `step5KerGen_thDecay_band` (the constant does not depend on
`κ`, so the `∃ C₆` after `κ` is the same one) and `b45Gen_facts_band`.  No hypothesis is left open: the pin is a theorem at every `d ≥ 3`. -/

/-! ## 5. Compiled nonempty instances (`d = 3`)

Data of the merged band instances (`Induction/Step34PinsP.lean:170-215`, `Induction/Defs.lean:435`): `sz0` (`L = 4(n+1)`, `W = (2(n+1))^5`, `lam = (2(n+1))^{-6}`; `n = 0`:
`L = 4`, `W = 32`, `N = 2^21`), the flow `z0` (`z_n = 1/2 + i N_n^{-4/5}`, `flow_z0` at `(κ, ε, 𝔠, 𝔡) = (1/10, 1/10, 1/6, 1/10)`), `s ≡ 0`, `t ≡ 1/16`
(`t ≤ lemT z0`, `STCaseI`: `sz0_caseI`; `(con_st_ind)` for every `𝔠_d > 0`: `sz0_con`), `C_d = 1`.  What stays a hypothesis of an example is a stochastic premise that is
another gate's pin (`STKboundgL`, `STKwardgL`, `STLKgL s`, `STStep2ConclgL`): they are the premises of `STIngRgL`. -/

end RBM.BA

end
