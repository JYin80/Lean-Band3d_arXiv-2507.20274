/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Chain.QtNonzeroEndGen
import RBM3D.Chain.QtXiRoundLiftGen
import RBM3D.Chain.GridGoodGen
import RBM3D.Chain.NQLinGen
import RBM3D.Chain.B45Gen
import RBM3D.Chain.NQEndFlowGen
import RBM3D.Induction.QtNonzeroFlow
import RBM3D.Induction.QtNonzeroFlowLift
import RBM3D.Induction.LemDecCalELip

/-!
# The case-(ii) endpoint over the carrier family, per time and uniformly in the time (U3s4 row c, file 1; ticket T2505)

Generic forms of `Induction/QtNonzeroFlow.lean` and `Induction/QtNonzeroFlowLift.lean` (not edited) over a carrier family `(law, Flow, mkM, T0)`, namespace
`RBM.BA`, no `BA/*` import.  Paper: arXiv:2507.20274, `lem:STOeq_Qt_nonzero` (`3_5:1561-1572`), proof `3_5:1889-1933` (`(eq:expandQAempty)` `3_5:1893`,
`(am;asoiuw_smalleta)` `3_5:1916`, "the same argument applies to each fixed `u`" `3_5:1931`), `(normQA2)` (`3_5:1466`).  Composition, no new mathematics (`7_8:1841`).

* **Target 10** the four R2* texts `STNZConclPTgL''`, `STOeqNZPTgL''`, `STNZConclgL''`, `STOeqNZgL''` (= `T2505_NZConclPTgL''`, `T2505_OeqNZPTgL''`,
  `T2505_NZConclgL''`, `T2505_OeqNZgL''`, binding) and their band bridges through `bandFM_STIngR`.
* **Target 11** `stOeqNZPTgL''_of` (conclusion `T2505_OeqNZPTgL''`, binding): the per-section endpoint `QtNZFlowGen_core`, `QtNZFlowGen_section` (`nzGridEndNg` of row b on
  `[s, v]`, the good events `gridGoodNgL_of` on every window and `nqLinGoodgL_of`, the projected initial event from `STLKgL s` at half the exponent and `(normQA2)`, the
  collapsed sections).  The kernel window is `STCaseII` (`1 - s ≤ lam²/L²`) with R1 in the A-form `lam² ≤ Aof κ gK²`.
* **Target 12** `stOeqNZgL''_of` (conclusion `T2505_OeqNZgL''`): the lift at the envelope controls with the `𝓛` modulus `LemDecCalELipG_FlowMod` (family row 16), the `𝒦`
  modulus `NQEndFlowGen_KLipFam` (family row 15) and the factor `2^{n_}` of `(normQA2)` in the mesh `δ ≤ N^{-(6 n_ + 18 + 2c)}`.
* **Target 15 (part)** the band re-derivations `stOeqNZPTgL''_band`, `stOeqNZgL''_band`, `stOeqNZPT''_holds_of_gen`, `stOeqNZ''_holds_of_gen` and compiled nonempty instances
  at `d = 3`.

The model-free privates of `QtNonzeroFlow`, `QtNonzeroFlowLift` and `NQEndFlowGen` are reused by `open private`.
-/

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

open private nzFlow_level_le nzFlow_phi_nonneg nzFlow_phiC_ge nzFlow_phiC_one_le nzFlow_K nzFlow_K_ne_zero nzFlow_K_low nzFlow_K_up
  nzFlow_K_card nzFlow_four_pow_le nzFlow_union4 nzFlow_bootRHS_one_le nzFlow_conStInd_exp_mono nzFlow_proj_le from RBM3D.Induction.QtNonzeroFlow

open private NQEndFlowGen_prec_of_le_right NQEndFlowGen_hQ NQEndFlowGen_restrict_pair NQEndFlowGen_step2_restrict NQEndFlowGen_isProb from RBM3D.Chain.NQEndFlowGen

open private nqEnd_rangeCond_mono from RBM3D.Induction.NQEndLin

open private nzLift_sharp_one_le nzLift_sharp_le nzLift_sharp_mono nzLift_zeta_mono nzLift_zeta_le nzLift_zeta_one_le nzLift_core_below nzLift_card_V
  from RBM3D.Induction.QtNonzeroFlowLift

open private QtLiftGen_sharp_prec QtLiftGen_htN from RBM3D.Chain.QtXiRoundLiftGen

open private QtBootGen_flow_abs_le from RBM3D.Chain.QtBootGen

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal

noncomputable section

namespace RBM.BA

open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes
open RBM.Ind (nqFlowSharp)

/-! ## 1. Target 10: the R2* texts (case (ii), `Q^{(A)}`; `STbootRHS` at the window start `B_s`, DECISIONS §80 (1)) -/

section Texts

/-- **Target 10, `STNZConclPTgL''`** (= `T2505_NZConclPTgL''`, binding; band `STNZConclPT''`, `QtNonzeroFlow.lean:75`): the merged `STNQConclPTgL''` with the
index set "every `σ`, every `A ⊇ I_diff(σ)`" and the quantity `‖(Q^{(A)}(𝓛 - 𝒦)^{(n_)})_{u,σ,a}‖`. -/
def STNZConclPTgL'' {d : ℕ} {sz : Sizes d} (Cf : FlowFM sz) (μ : Measure sz.SeqΩ) (s t : ℕ → ℝ) : Prop :=
  ∀ n_ p : ℕ, 2 ≤ n_ → 1 ≤ p → ∀ XL XLK : ℕ → ℕ → ℝ → ℝ,
    (∀ m n u, 1 ≤ XL m n u) → (∀ m n u, 1 ≤ XLK m n u) →
    (∀ m, 1 ≤ m → STlenL n_ p m →
      PrecL sz μ (U := STPair s t) (fun n q ω => STXiLg Cf n q.1.1 m ω) (fun n q _ => XL m n q.1.2)) →
    (∀ m, 1 ≤ m → m ≤ n_ →
      PrecL sz μ (U := STPair s t) (fun n q ω => STXiLKg Cf n q.1.1 m ω) (fun n q _ => XLK m n q.1.2)) →
    PrecPTL sz μ (U := fun n => TimeIcc s t n × {σA : (Fin n_ → Bool) × Finset (Fin n_) // STIdiff σA.1 ⊆ σA.2} ×
        (Fin n_ → Zd d (sz.L n)))
      (fun n q ω => ‖zeroModeSet d (sz.L n) q.2.1.1.2
          (fun b : Fin n_ → Zd d (sz.L n) => Cf.L n (q.1 : ℝ) q.2.1.1.1 b ω - Cf.K n (q.1 : ℝ) q.2.1.1.1 b) q.2.2‖ /
        (sz.Bctl n (q.1 : ℝ)) ^ n_)
      (fun n q _ => (sz.Bctl n (q.1 : ℝ)) ^ (1 / 6 : ℝ) * XLK n_ n (q.1 : ℝ) +
        STbootRHS 2 (fun m => XL m n (q.1 : ℝ)) (fun m => XLK m n (q.1 : ℝ)) (sz.Bctl n (s n)) n_ p)

/-- **Target 10, `STOeqNZPTgL''`** (= `T2505_OeqNZPTgL''`, binding; band `STOeqNZPT''`, `QtNonzeroFlow.lean:95`): case (ii) setting of a carrier family. -/
def STOeqNZPTgL'' (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ)
    (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop) (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz)
    (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) : Prop :=
  STIngRgL d STCaseII law Flow mk T0 (fun sz z s t => STNZConclPTgL'' (mk sz z) (law sz) s t)

/-- **Target 10, `STNZConclgL''`** (= `T2505_NZConclgL''`, binding; band `STNZConcl''`, `QtNonzeroFlowLift.lean:68`): `STNZConclPTgL''` with `PrecL`. -/
def STNZConclgL'' {d : ℕ} {sz : Sizes d} (Cf : FlowFM sz) (μ : Measure sz.SeqΩ) (s t : ℕ → ℝ) : Prop :=
  ∀ n_ p : ℕ, 2 ≤ n_ → 1 ≤ p → ∀ XL XLK : ℕ → ℕ → ℝ → ℝ,
    (∀ m n u, 1 ≤ XL m n u) → (∀ m n u, 1 ≤ XLK m n u) →
    (∀ m, 1 ≤ m → STlenL n_ p m →
      PrecL sz μ (U := STPair s t) (fun n q ω => STXiLg Cf n q.1.1 m ω) (fun n q _ => XL m n q.1.2)) →
    (∀ m, 1 ≤ m → m ≤ n_ →
      PrecL sz μ (U := STPair s t) (fun n q ω => STXiLKg Cf n q.1.1 m ω) (fun n q _ => XLK m n q.1.2)) →
    PrecL sz μ (U := fun n => TimeIcc s t n × {σA : (Fin n_ → Bool) × Finset (Fin n_) // STIdiff σA.1 ⊆ σA.2} ×
        (Fin n_ → Zd d (sz.L n)))
      (fun n q ω => ‖zeroModeSet d (sz.L n) q.2.1.1.2
          (fun b : Fin n_ → Zd d (sz.L n) => Cf.L n (q.1 : ℝ) q.2.1.1.1 b ω - Cf.K n (q.1 : ℝ) q.2.1.1.1 b) q.2.2‖ /
        (sz.Bctl n (q.1 : ℝ)) ^ n_)
      (fun n q _ => (sz.Bctl n (q.1 : ℝ)) ^ (1 / 6 : ℝ) * XLK n_ n (q.1 : ℝ) +
        STbootRHS 2 (fun m => XL m n (q.1 : ℝ)) (fun m => XLK m n (q.1 : ℝ)) (sz.Bctl n (s n)) n_ p)

/-- **Target 10, `STOeqNZgL''`** (= `T2505_OeqNZgL''`, binding; band `STOeqNZ''`, `QtNonzeroFlowLift.lean:88`). -/
def STOeqNZgL'' (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ)
    (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop) (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz)
    (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) : Prop :=
  STIngRgL d STCaseII law Flow mk T0 (fun sz z s t => STNZConclgL'' (mk sz z) (law sz) s t)

end Texts

section TextBridges

variable {d : ℕ} (sz : Sizes d) (E s t : ℕ → ℝ)

theorem bandFM_STNZConclPT'' : STNZConclPT'' sz E s t ↔ STNZConclPTgL'' (bandFM sz E) (Sizes.seqP sz) s t := Iff.rfl
theorem bandFM_STNZConcl'' : STNZConcl'' sz E s t ↔ STNZConclgL'' (bandFM sz E) (Sizes.seqP sz) s t := Iff.rfl

end TextBridges

section FamilyBridges

theorem bandFM_STOeqNZPT'' (d : ℕ) :
    STOeqNZPT'' d ↔ STOeqNZPTgL'' d (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
      (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n)) :=
  bandFM_STIngR d STCaseII (fun sz E s t => STNZConclPT'' sz E s t)

theorem bandFM_STOeqNZ'' (d : ℕ) :
    STOeqNZ'' d ↔ STOeqNZgL'' d (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
      (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n)) :=
  bandFM_STIngR d STCaseII (fun sz E s t => STNZConcl'' sz E s t)

end FamilyBridges

/-! ## 2. The projected initial event and the collapsed sections (generic forms of `QtNonzeroFlow` §4, private) -/

section QProj

variable {d : ℕ}

/-- **Measurability of the projected matrix functional** (band `nzFlow_meas_proj`): `H ↦ ‖(Q^{(A)}(𝓛-𝒦)^{(k)}_{u,σ,·}(H))_a‖` is measurable
(`GridGoodGen_meas_of_loopForm`, then the continuous linear functional `T ↦ (Q^{(A)} T)_a`, `zeroModeSetLin`). -/
private theorem QtNZFlowGen_meas_proj {sz : Sizes d} (Cm : Step2Mat sz) {E : ℕ → ℝ} (hL : StepDecompGen_LoopForm Cm E) (n : ℕ) (u : ℝ)
    {k : ℕ} (σ : Fin k → Bool) (A : Finset (Fin k)) (a : Fin k → Zd d (sz.L n)) :
    Measurable fun H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ =>
      ‖zeroModeSet d (sz.L n) A (fun b => STLKMg Cm n u H σ b) a‖ := by
  have hmeas := (GridGoodGen_meas_of_loopForm hL n u).1
  have h1 : Measurable fun H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ =>
      (fun b : Fin k → Zd d (sz.L n) => STLKMg Cm n u H σ b) :=
    Measurable.of_eval fun b => (hmeas k σ b).sub_const _
  have h2 : Continuous fun T : (Fin k → Zd d (sz.L n)) → ℂ => zeroModeSet d (sz.L n) A T a :=
    LinearMap.continuous_of_finiteDimensional
      ((LinearMap.proj a).comp (zeroModeSetLin (d := d) (L := sz.L n) A))
  exact (h2.measurable.comp h1).norm

/-- **The projected initial event** (band `nzFlow_initQ`; DECISIONS §94 (2); `3_5:1902`, `(normQA2)` `3_5:1466`): from `STLKgL s` at the length `k ≥ 1` and the half
exponent `ε/2`, for every `ε, D > 0`, eventually `P(∃ σ, A, a: N^ε B_s^k < ‖(Q^{(A)}(𝓛-𝒦)^{(k)}_{s,σ,·})_a‖) ≤ N^{-D}`: `‖(Q^{(A)} T)_a‖ ≤ 2^{|A|} sup_b ‖T_b‖ ≤
2^k N^{ε/2} B_s^k ≤ N^ε B_s^k` once `2^k ≤ N^{ε/2}`. -/
private theorem QtNZFlowGen_initQ {sz : Sizes d} (Cf : FlowFM sz) (μ : Measure sz.SeqΩ) (hsize : sz.SizeTendsto) {s : ℕ → ℝ}
    (hLK : STLKgL Cf μ s) {k : ℕ} (hk : 1 ≤ k) {ε : ℝ} (hε : 0 < ε) {D : ℝ} (hD : 0 < D) :
    ∀ᶠ n in atTop, μ {ω | ∃ (σ : Fin k → Bool) (A : Finset (Fin k))
        (a : Fin k → Zd d (sz.L n)), ((sz.size n : ℕ) : ℝ) ^ ε * (sz.Bctl n (s n)) ^ k <
          ‖zeroModeSet d (sz.L n) A (fun b => Cf.L n (s n) σ b ω - Cf.K n (s n) σ b) a‖} ≤
      ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-D)) := by
  have h2k : ∀ᶠ n in atTop, (2 : ℝ) ^ k ≤ ((sz.size n : ℕ) : ℝ) ^ (ε / 2) :=
    ((tendsto_rpow_atTop (half_pos hε)).comp hsize).eventually_ge_atTop _
  filter_upwards [hLK k hk (ε / 2) (half_pos hε) D hD, h2k] with n h1 h2
  refine le_trans (measure_mono ?_) h1
  intro ω hω
  obtain ⟨σ, A, a, hlt⟩ := hω
  by_contra hno
  have hall : ∀ b : Fin k → Zd d (sz.L n),
      ‖Cf.L n (s n) σ b ω - Cf.K n (s n) σ b‖ ≤ ((sz.size n : ℕ) : ℝ) ^ (ε / 2) * (sz.Bctl n (s n)) ^ k := by
    intro b
    by_contra hb
    exact hno ⟨(σ, b), not_le.1 hb⟩
  have hx0 : 0 ≤ ((sz.size n : ℕ) : ℝ) ^ (ε / 2) * (sz.Bctl n (s n)) ^ k := (norm_nonneg _).trans (hall fun _ => 0)
  have hproj := nzFlow_proj_le A (fun b => Cf.L n (s n) σ b ω - Cf.K n (s n) σ b) hx0 hall a
  have hsq : ((sz.size n : ℕ) : ℝ) ^ ε = ((sz.size n : ℕ) : ℝ) ^ (ε / 2) * ((sz.size n : ℕ) : ℝ) ^ (ε / 2) :=
    (UnifDetDom.rpow_half_mul_rpow_half _ hε).symm
  have hfin : (2 : ℝ) ^ k * (((sz.size n : ℕ) : ℝ) ^ (ε / 2) * (sz.Bctl n (s n)) ^ k) ≤
      ((sz.size n : ℕ) : ℝ) ^ ε * (sz.Bctl n (s n)) ^ k := by
    rw [hsq, mul_assoc]
    exact mul_le_mul_of_nonneg_right h2 hx0
  linarith

/-- **The collapsed section** `u_n = s_n` (band `nzFlow_collapsed`; paper-delta D597, candidate `T2292d`): for every deterministic `ζ_n ≥ 1` and every choice `σ_n`, `A_n`,
`a_n` (no relation between `A_n` and `I_diff(σ_n)` is needed), `‖(Q^{(A_n)}(𝓛-𝒦)^{(k)}_{s,σ_n,·})_{a_n}‖ / B_s^k ≺ ζ`: `STLKgL s` at the exponent `τ`, `(normQA2)` through
`QtNZFlowGen_initQ`, `B_s^k > 0` and `ζ ≥ 1`. -/
private theorem QtNZFlowGen_collapsed {sz : Sizes d} (Cf : FlowFM sz) (μ : Measure sz.SeqΩ) (hsize : sz.SizeTendsto) {s : ℕ → ℝ}
    (hLK : STLKgL Cf μ s) {k : ℕ} (hk : 1 ≤ k) (hBs : ∀ n, 0 < sz.Bctl n (s n)) {ζ : ℕ → ℝ} (hζ : ∀ n, 1 ≤ ζ n)
    (σ : ∀ n, Fin k → Bool) (A : ∀ n, Finset (Fin k)) (a : ∀ n, Fin k → Zd d (sz.L n)) :
    StochDomAt μ sz.size
      (fun n (_ : Unit) ω => ‖zeroModeSet d (sz.L n) (A n)
          (fun b => Cf.L n (s n) (σ n) b ω - Cf.K n (s n) (σ n) b) (a n)‖ / (sz.Bctl n (s n)) ^ k)
      (fun n (_ : Unit) _ => ζ n) := by
  intro τ hτ D hD
  filter_upwards [QtNZFlowGen_initQ Cf μ hsize hLK hk hτ hD] with n h2
  refine le_trans (measure_mono ?_) h2
  intro ω hω
  simp only [badSetAt, Set.mem_ofPred_eq] at hω ⊢
  obtain ⟨_, hω⟩ := hω
  refine ⟨σ n, A n, a n, ?_⟩
  have hBk : 0 < (sz.Bctl n (s n)) ^ k := pow_pos (hBs n) _
  have hN0 : 0 ≤ ((sz.size n : ℕ) : ℝ) ^ τ := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hlt := (lt_div_iff₀ hBk).1 hω
  calc ((sz.size n : ℕ) : ℝ) ^ τ * (sz.Bctl n (s n)) ^ k
      ≤ ((sz.size n : ℕ) : ℝ) ^ τ * ζ n * (sz.Bctl n (s n)) ^ k := by
        have := mul_le_mul_of_nonneg_left (hζ n) hN0
        nlinarith
    _ < _ := hlt

end QProj

/-! ## 3. The per-section endpoint (generic form of `QtNonzeroFlow` §5, private) -/

section CoreProof

variable {d : ℕ}

/-- The carrier facts of one flow `(sz, z)` that the endpoint `nzGridEndNg` reads (the premises of `nzGridEndNg`, the law and `LCompat` of the flow matrix `Hf`, and R1 in
the A-form `lam² ≤ A gK²`); a private bundle, so that no public statement has an unproved `Prop` premise of this name. -/
private structure QtNZFlowGen_Facts {sz : Sizes d} (Cm : Step2Mat sz) (μ : Measure sz.SeqΩ)
    (Hf : ∀ n : ℕ, ℝ → sz.SeqΩ → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    (E lam' gK : ℕ → ℝ) (Ψ : ∀ n : ℕ, Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (κm A : ℝ) : Prop where
  hL : StepDecompGen_LoopForm Cm E
  hW : StepDecompGen_WalkForm Cm lam' Ψ
  hspec : DecayGen_Spec Cm.toFlowFM κm
  hm : ∀ n, ‖Cm.m n‖ ≤ 1
  hSeq : ∀ n, Cm.S n = SB d (sz.L n) (lam' n)
  hS : ∀ (n : ℕ) (a : Zd d (sz.L n)), ∑ b : Zd d (sz.L n), ‖Cm.S n a b‖ ≤ 1
  hRow : ∀ n, GridRepTailGen_Ker Cm.toFlowFM n
  hKS : ∀ n, ZeroModeGen_KerSums Cm.toFlowFM n
  hKK : ∀ (n : ℕ) (w : ℝ) (k : ℕ) (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)),
    Cm.KI n w (KLloopOf d (sz.L n) σ a) = Cm.K n w σ a
  hExp : ∀ᶠ n : ℕ in atTop, ∀ (s' t' : ℕ → ℝ) (K' : ℕ → ℕ), HierDriftGen_Expand Cm s' t' K' n
  hKL : ∀ᶠ n : ℕ in atTop, HierDriftGen_KLoop Cm n
  hKT : ∀ᶠ n : ℕ in atTop, HierDriftGen_KTwo Cm n
  hU : ∀ᶠ n : ℕ in atTop, HierDriftGen_UStep Cm.toFlowFM n
  hLaw : Step2EventsGen_Law Cm μ Hf
  hC : Step34Gen_LCompat Cm Hf
  hR1 : ∀ n, sz.lam n ^ 2 ≤ A * gK n ^ 2

/-- **The endpoint at one non-collapsed section** (band `nzFlow_core`, `QtNonzeroFlow:577`; the shape of `NQEndFlowGen_core` with `nzGridEndNg` in place of `nqGridEndLinNg`): for
deterministic controls `X m n`, `Y m n ≥ 1` with `Ξ̂^{(𝓛)}_{w,m} ≺ X m` (`STlenL n_ p m`) and `Ξ̂^{(𝓛-𝒦)}_{w,m} ≺ Y m` (`m ≤ n_`) uniformly in `w ∈ [s_n, v_n]`, the zero-mode-removed
`(Q^{(A_n)}(𝓛-𝒦)^{(n_)})_{v,σ_n,a_n}/B_v^{n_}` (`A_n ⊇ I_diff(σ_n)`) is `≺ B_v^{1/6} Y n_ + STbootRHS 2 X Y B_s n_ p`.  The failure event is inside the union of four events of
probability `≤ N^{-(D+2)}`: the carrier walk leaving `GoodSetNg` (`hGrid`, the good event on `[s, v]` at the crude level `Φc` and the level `Λ_s`) or `GoodLinNg` (`hLin`), the
projected initial loops (`QtNZFlowGen_initQ`, the law at `j = 0`) and the exceptional event `Gᶜ` of `nzGridEndNg` at `ε₀ = τ/2`, `D₁ = D + 2` (D1 at `k = n_`, the constant `C5`);
outside it, `nzGridEndNg` bounds the terminal projected loop by `N^{τ/2}(Λ_s^{1/2} + Φ₁ + Φ₂ + Φ₃) B_v^{n_} ≤ N^τ ζ B_v^{n_}`, transferred to the flow matrix `Hf` at `v_n` by the
law at `j = K_n` (`gridTime_last`). -/
private theorem QtNZFlowGen_core {sz : Sizes d} (Cm : Step2Mat sz) (μ : Measure sz.SeqΩ)
    {Hf : ∀ n : ℕ, ℝ → sz.SeqΩ → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ}
    {E lam' gK : ℕ → ℝ} {Ψ : ∀ n : ℕ, Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ} {κm A 𝔠 τR : ℝ}
    (F : QtNZFlowGen_Facts Cm μ Hf E lam' gK Ψ κm A) {s t v : ℕ → ℝ} (hd : 3 ≤ d) (h𝔠 : 0 < 𝔠) (hτR : 0 < τR)
    (hKb : STKboundgL Cm.toFlowFM μ) (hsize : sz.SizeTendsto) (hband : sz.Bandwidth 𝔠)
    (hs0 : ∀ n, 0 ≤ s n) (hst : ∀ n, s n ≤ t n) (ht1 : ∀ n, t n < 1) (hcase : sz.STCaseII s t) (hrange : sz.RangeCond τR t)
    (hsv : ∀ n, s n < v n) (hvt : ∀ n, v n ≤ t n) (hLK : STLKgL Cm.toFlowFM μ s)
    (hGrid : GridGoodNConclg Cm μ s v) (hLin : NQLinConclg Cm μ s t) {n_ p : ℕ} (hn : 2 ≤ n_) (hp : 1 ≤ p)
    {C5 : ℝ} (hC5 : 0 < C5) (hKer : ∀ᶠ n : ℕ in atTop, QtNZGen_KerNZ Cm.toFlowFM gK n_ A C5 n)
    {X Y : ℕ → ℕ → ℝ} (hX1 : ∀ m n, 1 ≤ X m n) (hY1 : ∀ m n, 1 ≤ Y m n)
    (hX : ∀ m : ℕ, 1 ≤ m → STlenL n_ p m →
      PrecL sz μ (U := fun n => TimeIcc s v n) (fun n u ω => STXiLg Cm.toFlowFM n (u : ℝ) m ω) (fun n _ _ => X m n))
    (hY : ∀ m : ℕ, 1 ≤ m → m ≤ n_ →
      PrecL sz μ (U := fun n => TimeIcc s v n) (fun n u ω => STXiLKg Cm.toFlowFM n (u : ℝ) m ω) (fun n _ _ => Y m n))
    (σ : ∀ n, Fin n_ → Bool) (A' : ∀ n, Finset (Fin n_)) (hA : ∀ n, STIdiff (σ n) ⊆ A' n) (a : ∀ n, Fin n_ → Zd d (sz.L n)) :
    StochDomAt μ sz.size
      (fun n (_ : Unit) ω => ‖zeroModeSet d (sz.L n) (A' n)
          (fun b => Cm.L n (v n) (σ n) b ω - Cm.K n (v n) (σ n) b) (a n)‖ / (sz.Bctl n (v n)) ^ n_)
      (fun n (_ : Unit) _ => (sz.Bctl n (v n)) ^ (1 / 6 : ℝ) * Y n_ n +
        STbootRHS 2 (fun m => X m n) (fun m => Y m n) (sz.Bctl n (s n)) n_ p) := by
  have : IsProbabilityMeasure Cm.Pp := by rw [F.hW.2.1]; exact isProbabilityMeasure_pathP _
  have := NQEndFlowGen_isProb F.hLaw
  intro τ hτ D hD
  have hv1 : ∀ n, v n < 1 := fun n => (hvt n).trans_lt (ht1 n)
  have hBv : ∀ n, 0 < sz.Bctl n (v n) := fun n => st_Bctl_pos sz (hv1 n)
  have hBs : ∀ n, 0 < sz.Bctl n (s n) := fun n => st_Bctl_pos sz ((hsv n).le.trans_lt (hv1 n))
  -- the levels
  set Λ : ℕ → ℝ := fun n => max 1 (RBM.Ind.nqFlowLam (fun m => X m n) (sz.Bctl n (s n)) n_ p) with hΛdef
  set Φ₁ : ℕ → ℝ := fun n => nqLinPhi1 (fun m => Y m n) n_ with hΦ₁def
  set Φ₂ : ℕ → ℝ := fun n =>
    nqLinPhi2 (fun m => X m n) (fun m => Y m n) (sz.Bctl n (v n)) n_ (Y n_ n) with hΦ₂def
  set Φ₃ : ℕ → ℝ := fun n => nqLinPhi3 (fun m => X m n) n_ with hΦ₃def
  set Φc : ℕ → ℝ := fun n => RBM.Ind.nqFlowPhiC (fun m => X m n) (fun m => Y m n) n_ with hΦcdef
  have hΛ1 : ∀ n, 1 ≤ Λ n := fun n => le_max_left _ _
  have hΛ0 : ∀ n, 0 ≤ Λ n := fun n => zero_le_one.trans (hΛ1 n)
  have hΦ : ∀ n, 0 ≤ Φ₁ n ∧ 0 ≤ Φ₂ n ∧ 0 ≤ Φ₃ n := fun n =>
    nzFlow_phi_nonneg (fun m => hX1 m n) (fun m => hY1 m n) (hBv n).le
  have hΦc1 : ∀ n, 1 ≤ Φc n := fun n => nzFlow_phiC_one_le (fun m => hX1 m n) (fun m => hY1 m n)
  -- the endpoint of the grid walk at `ε₀ = τ/2`, `D₁ = D + 2`
  obtain ⟨ε₁, τ', D', C_K, hε₁, hτ', hD', hCK, hend⟩ := nzGridEndNg Cm μ s t hd h𝔠 hτR F.hL F.hW F.hspec F.hm F.hSeq F.hS
    F.hRow F.hKS F.hKK hKb F.hExp F.hKL F.hKT F.hU hsize hband hs0 hst ht1 hcase hrange F.hR1 n_ hn C5 hC5 hKer Λ Φ₁ Φ₂ Φ₃ hΛ0
    (Eventually.of_forall hΛ1) (fun n => (hΦ n).1) (fun n => (hΦ n).2.1) (fun n => (hΦ n).2.2) v
    (fun n => (hsv n).le) hvt (τ / 2) (half_pos hτ) (D + 2) (by linarith)
  -- the grid
  set K : ℕ → ℕ := nzFlow_K sz C_K with hKdef
  have hK0 : ∀ n, K n ≠ 0 := nzFlow_K_ne_zero sz C_K
  have hKcard := nzFlow_K_card sz hsize hCK
  have hpin := hend Φc K hK0 (Eventually.of_forall (nzFlow_K_low sz C_K)) (Eventually.of_forall (nzFlow_K_up sz C_K))
  -- the hypotheses of the good-event lemma on `[s, v]` at the crude level `Φc` and the level `Λ_s`
  have hXg : ∀ m : ℕ, 1 ≤ m → m ≤ n_ + 1 →
      PrecL sz μ (U := fun n => TimeIcc s v n) (fun n u ω => STXiLg Cm.toFlowFM n (u : ℝ) m ω) (fun n _ _ => Φc n) :=
    fun m hm hm' => NQEndFlowGen_prec_of_le_right (hX m hm (Or.inl hm')) fun n u ω =>
      (nzFlow_phiC_ge (fun m => hX1 m n) (fun m => hY1 m n) (Finset.mem_Icc.2 ⟨hm, hm'⟩)).1
  have hYg : ∀ m : ℕ, 1 ≤ m → m ≤ n_ →
      PrecL sz μ (U := fun n => TimeIcc s v n) (fun n u ω => STXiLKg Cm.toFlowFM n (u : ℝ) m ω) (fun n _ _ => Φc n) :=
    fun m hm hm' => NQEndFlowGen_prec_of_le_right (hY m hm hm') fun n u ω =>
      (nzFlow_phiC_ge (fun m => hX1 m n) (fun m => hY1 m n) (Finset.mem_Icc.2 ⟨hm, by omega⟩)).2
  have hQ : PrecL sz μ (U := fun n => TimeIcc s v n)
      (fun n u ω => STXiLg Cm.toFlowFM n (u : ℝ) (2 * n_ - 1) ω *
        (STXiLg Cm.toFlowFM n (u : ℝ) (4 * p) ω / sz.Bctl n (u : ℝ)) ^ (1 / (2 * (p : ℝ))))
      (fun n _ _ => Λ n) :=
    NQEndFlowGen_hQ Cm.toFlowFM μ hsize (fun n => (hsv n).le) hv1 (a := 2 * n_ - 1) (b := 4 * p) hp
      (Xa := fun n => X (2 * n_ - 1) n) (Xb := fun n => X (4 * p) n)
      (fun n => zero_le_one.trans (hX1 _ n)) (fun n => zero_le_one.trans (hX1 _ n))
      (hX (2 * n_ - 1) (by omega) (Or.inr (Or.inl rfl))) (hX (4 * p) (by omega) (Or.inr (Or.inr rfl)))
  have hgood := hGrid v (fun n => (hsv n).le) (fun n => le_rfl) K hK0 n_ hn Λ Φc hΛ1 hΦc1 hXg hYg p hp hQ
    (C_K + 2) hKcard ε₁ hε₁ τ' hτ' D' hD'
  have hlin := hLin v (fun n => (hsv n).le) hvt K hK0 n_ hn X Y hX1 hY1
    (fun m hm hm' => hX m hm (Or.inl hm')) hY (C_K + 2) hKcard ε₁ hε₁
  have hinit := QtNZFlowGen_initQ Cm.toFlowFM μ hsize hLK (k := n_) (by omega) hε₁ (D := D + 2) (by linarith)
  filter_upwards [hpin, hgood (D + 2) (by linarith), hlin (D + 2) (by linarith), hinit,
    hsize.eventually_ge_atTop 2] with n hG hGood hLinn hInit hN2
  obtain ⟨G, hGP, hGb⟩ := hG
  have hNn1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by linarith
  have hx0 : (0 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ (-(D + 2)) := Real.rpow_nonneg (by linarith) _
  -- the two matrix events: the terminal projected bound fails / an initial projected loop is large
  set Sterm : Set (Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) :=
    {M | ((sz.size n : ℕ) : ℝ) ^ τ * ((sz.Bctl n (v n)) ^ (1 / 6 : ℝ) * Y n_ n +
        STbootRHS 2 (fun m => X m n) (fun m => Y m n) (sz.Bctl n (s n)) n_ p) <
      ‖zeroModeSet d (sz.L n) (A' n) (fun b => STLKMg Cm n (v n) M (σ n) b) (a n)‖ / (sz.Bctl n (v n)) ^ n_} with hStermdef
  set Sinit : Set (Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) :=
    {M | ∃ (σ' : Fin n_ → Bool) (A'' : Finset (Fin n_)) (a' : Fin n_ → Zd d (sz.L n)),
      ((sz.size n : ℕ) : ℝ) ^ ε₁ * (sz.Bctl n (s n)) ^ n_ <
        ‖zeroModeSet d (sz.L n) A'' (fun b => STLKMg Cm n (s n) M σ' b) a'‖} with hSinitdef
  have hSterm : MeasurableSet Sterm :=
    measurableSet_lt measurable_const ((QtNZFlowGen_meas_proj Cm F.hL n (v n) (σ n) (A' n) (a n)).div_const _)
  have hSinit : MeasurableSet Sinit := by
    have heq : Sinit = ⋃ x : (Fin n_ → Bool) × Finset (Fin n_) × (Fin n_ → Zd d (sz.L n)),
        {M | ((sz.size n : ℕ) : ℝ) ^ ε₁ * (sz.Bctl n (s n)) ^ n_ <
          ‖zeroModeSet d (sz.L n) x.2.1 (fun b => STLKMg Cm n (s n) M x.1 b) x.2.2‖} := by
      ext M; simp [hSinitdef]
    rw [heq]
    exact MeasurableSet.iUnion fun x =>
      measurableSet_lt measurable_const (QtNZFlowGen_meas_proj Cm F.hL n (s n) x.1 x.2.1 x.2.2)
  -- the transfers at the terminal grid index and at index `0` (the law of the grid state)
  have e1 : μ {ω | Hf n (v n) ω ∈ Sterm} = Cm.Pp (Cm.Hpath s v K n (K n) ⁻¹' Sterm) := by
    have := F.hLaw s v K n (K n) (hs0 n) (hsv n).le (hK0 n) Sterm hSterm
    rw [gridTime_last s v K n (hK0 n)] at this
    exact this.symm
  have e0 : Cm.Pp (Cm.Hpath s v K n 0 ⁻¹' Sinit) = μ {ω | Hf n (s n) ω ∈ Sinit} := by
    have := F.hLaw s v K n 0 (hs0 n) (hsv n).le (hK0 n) Sinit hSinit
    rw [ST_gridTime_zero] at this
    exact this
  have hLM0 : ∀ (ω : sz.SeqΩ) (σ' : Fin n_ → Bool) (a' : Fin n_ → Zd d (sz.L n)),
      Cm.LM n (s n) (Hf n (s n) ω) σ' a' = Cm.L n (s n) σ' a' ω := fun ω σ' a' =>
    GridGoodGen_LM_eq_L F.hL F.hC n (s n) σ' a' ω
  -- the failure event of the terminal bound is inside the union of four events
  have hmain : Cm.Pp (Cm.Hpath s v K n (K n) ⁻¹' Sterm) ≤ ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-D)) := by
    refine nzFlow_union4 (C := Cm.Hpath s v K n 0 ⁻¹' Sinit) (D' := Gᶜ) hx0 hGood hLinn ?_ ?_ ?_
      (nzFlow_four_pow_le hN2)
    · rw [e0]
      refine le_trans (le_of_eq ?_) hInit
      congr 1
      ext ω
      simp only [Set.mem_ofPred_eq, hSinitdef, STLKMg, STLMg, hLM0]
    · rw [← ofReal_measureReal (measure_ne_top Cm.Pp _)]
      exact ENNReal.ofReal_le_ofReal hGP
    · intro ω hω
      by_contra hno
      simp only [Set.mem_union, Set.mem_compl_iff, Set.mem_preimage, Set.mem_ofPred_eq, not_or,
        not_not] at hno
      obtain ⟨⟨⟨hgoodω, hlinω⟩, hinitω⟩, hGω⟩ := hno
      have hinit' : ∀ (σ' : Fin n_ → Bool) (A'' : Finset (Fin n_)), STIdiff σ' ⊆ A'' → ∀ a' : Fin n_ → Zd d (sz.L n),
            ‖zeroModeSet d (sz.L n) A'' (fun b => STLKMg Cm n (s n) (Cm.Hpath s v K n 0 ω) σ' b) a'‖ ≤
              ((sz.size n : ℕ) : ℝ) ^ ε₁ * (sz.Bctl n (s n)) ^ n_ := by
        intro σ' A'' _ a'
        by_contra hcon
        exact hinitω ⟨σ', A'', a', not_le.1 hcon⟩
      have hb := hGb ω hGω (fun j hj => ⟨hgoodω j hj, hlinω j hj⟩) hinit' (σ n) (A' n) (hA n) (a n)
      have hlev : Λ n ^ ((1 : ℝ) / 2) + Φ₁ n + Φ₂ n + Φ₃ n ≤
          (sz.Bctl n (v n)) ^ (1 / 6 : ℝ) * Y n_ n +
            STbootRHS 2 (fun m => X m n) (fun m => Y m n) (sz.Bctl n (s n)) n_ p :=
        nzFlow_level_le hn hp (fun m => hX1 m n) (fun m => hY1 m n) (hBs n)
      have hBk : 0 < (sz.Bctl n (v n)) ^ n_ := pow_pos (hBv n) _
      have hL0 : 0 ≤ Λ n ^ ((1 : ℝ) / 2) + Φ₁ n + Φ₂ n + Φ₃ n := by
        have := Real.rpow_nonneg (hΛ0 n) ((1 : ℝ) / 2)
        have := hΦ n
        linarith [this]
      have hdiv : ‖zeroModeSet d (sz.L n) (A' n) (fun b => STLKMg Cm n (v n) (Cm.Hpath s v K n (K n) ω) (σ n) b) (a n)‖ /
          (sz.Bctl n (v n)) ^ n_ ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) *
            (Λ n ^ ((1 : ℝ) / 2) + Φ₁ n + Φ₂ n + Φ₃ n) := (div_le_iff₀ hBk).2 hb
      have hhalf : ((sz.size n : ℕ) : ℝ) ^ (τ / 2) ≤ ((sz.size n : ℕ) : ℝ) ^ τ :=
        Real.rpow_le_rpow_of_exponent_le hNn1 (by linarith)
      have hpos : 0 ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) := Real.rpow_nonneg (by linarith) _
      have hz0 : 0 ≤ (sz.Bctl n (v n)) ^ (1 / 6 : ℝ) * Y n_ n +
          STbootRHS 2 (fun m => X m n) (fun m => Y m n) (sz.Bctl n (s n)) n_ p := hL0.trans hlev
      have hfin : ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * (Λ n ^ ((1 : ℝ) / 2) + Φ₁ n + Φ₂ n + Φ₃ n) ≤
          ((sz.size n : ℕ) : ℝ) ^ τ * ((sz.Bctl n (v n)) ^ (1 / 6 : ℝ) * Y n_ n +
            STbootRHS 2 (fun m => X m n) (fun m => Y m n) (sz.Bctl n (s n)) n_ p) :=
        calc _ ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * ((sz.Bctl n (v n)) ^ (1 / 6 : ℝ) * Y n_ n +
              STbootRHS 2 (fun m => X m n) (fun m => Y m n) (sz.Bctl n (s n)) n_ p) :=
              mul_le_mul_of_nonneg_left hlev hpos
          _ ≤ _ := mul_le_mul_of_nonneg_right hhalf hz0
      exact absurd hω (not_lt.2 (hdiv.trans hfin))
  have hLMv : ∀ (ω : sz.SeqΩ) (σ' : Fin n_ → Bool) (a' : Fin n_ → Zd d (sz.L n)),
      Cm.LM n (v n) (Hf n (v n) ω) σ' a' = Cm.L n (v n) σ' a' ω := fun ω σ' a' =>
    GridGoodGen_LM_eq_L F.hL F.hC n (v n) σ' a' ω
  calc μ (badSetAt sz.size _ _ τ n) = μ {ω | Hf n (v n) ω ∈ Sterm} := by
        congr 1
        ext ω
        simp only [badSetAt, Set.mem_ofPred_eq, hStermdef, STLKMg, STLMg, hLMv ω]
        exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨(), h⟩⟩
    _ = Cm.Pp (Cm.Hpath s v K n (K n) ⁻¹' Sterm) := e1
    _ ≤ _ := hmain

end CoreProof

section SectionProof

variable {d : ℕ}

/-- **The endpoint at an arbitrary section** `q n = (u_n, ⟨(σ_n, A_n), h_n⟩, a_n)` of the parameter set of `STNZConclPTgL''` (band `nzFlow_section`, `QtNonzeroFlow:~760`;
`perTimeDomAt_iff_forall_section`): `v_n = u_n` where `s_n < u_n`, `v_n = t_n` elsewhere (so `s < v ≤ t`), the controls are the numbers `XL m n (v n)`, `XLK m n (v n)` on the
window `[s, v]` (`NQEndFlowGen_restrict_pair`; `STCaseII s t` concerns `s` only, so it holds on every window `[s, v]` unchanged), and `QtNZFlowGen_core` gives the bound at the
indices with `s_n < u_n`; at the collapsed indices `u_n = s_n` the section is bounded by `QtNZFlowGen_collapsed` (`STLKgL s` and `(normQA2)`). -/
private theorem QtNZFlowGen_section {sz : Sizes d} (Cm : Step2Mat sz) (μ : Measure sz.SeqΩ)
    {Hf : ∀ n : ℕ, ℝ → sz.SeqΩ → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ}
    {E lam' gK : ℕ → ℝ} {Ψ : ∀ n : ℕ, Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ} {κm A 𝔠 τR : ℝ}
    (F : QtNZFlowGen_Facts Cm μ Hf E lam' gK Ψ κm A) {s t : ℕ → ℝ} (hd : 3 ≤ d) (h𝔠 : 0 < 𝔠) (hτR : 0 < τR)
    (hKb : STKboundgL Cm.toFlowFM μ) (hsize : sz.SizeTendsto) (hband : sz.Bandwidth 𝔠)
    (hs0 : ∀ n, 0 ≤ s n) (hst : ∀ n, s n < t n) (ht1 : ∀ n, t n < 1) (hcase : sz.STCaseII s t) (hrange : sz.RangeCond τR t)
    (hLK : STLKgL Cm.toFlowFM μ s)
    (hGrid : ∀ v : ℕ → ℝ, (∀ n, s n < v n) → (∀ n, v n ≤ t n) → GridGoodNConclg Cm μ s v) (hLin : NQLinConclg Cm μ s t)
    {n_ p : ℕ} (hn : 2 ≤ n_) (hp : 1 ≤ p) {C5 : ℝ} (hC5 : 0 < C5) (hKer : ∀ᶠ n : ℕ in atTop, QtNZGen_KerNZ Cm.toFlowFM gK n_ A C5 n)
    {XL XLK : ℕ → ℕ → ℝ → ℝ} (hXL : ∀ m n u, 1 ≤ XL m n u) (hXLK : ∀ m n u, 1 ≤ XLK m n u)
    (hXLp : ∀ m, 1 ≤ m → STlenL n_ p m →
      PrecL sz μ (U := STPair s t) (fun n q ω => STXiLg Cm.toFlowFM n q.1.1 m ω) (fun n q _ => XL m n q.1.2))
    (hXLKp : ∀ m, 1 ≤ m → m ≤ n_ →
      PrecL sz μ (U := STPair s t) (fun n q ω => STXiLKg Cm.toFlowFM n q.1.1 m ω) (fun n q _ => XLK m n q.1.2))
    (q : ∀ n, TimeIcc s t n × {σA : (Fin n_ → Bool) × Finset (Fin n_) // STIdiff σA.1 ⊆ σA.2} × (Fin n_ → Zd d (sz.L n))) :
    StochDomAt μ sz.size
      (fun n (_ : Unit) ω => ‖zeroModeSet d (sz.L n) (q n).2.1.1.2
          (fun b => Cm.L n ((q n).1 : ℝ) (q n).2.1.1.1 b ω - Cm.K n ((q n).1 : ℝ) (q n).2.1.1.1 b) (q n).2.2‖ /
        (sz.Bctl n ((q n).1 : ℝ)) ^ n_)
      (fun n (_ : Unit) _ => (sz.Bctl n ((q n).1 : ℝ)) ^ (1 / 6 : ℝ) * XLK n_ n ((q n).1 : ℝ) +
        STbootRHS 2 (fun m => XL m n ((q n).1 : ℝ)) (fun m => XLK m n ((q n).1 : ℝ)) (sz.Bctl n (s n)) n_ p) := by
  classical
  -- the end `v` of the window of the endpoint
  obtain ⟨v, hvdef⟩ : ∃ v : ℕ → ℝ, v = fun n => if s n < ((q n).1 : ℝ) then ((q n).1 : ℝ) else t n :=
    ⟨_, rfl⟩
  have hsv : ∀ n, s n < v n := fun n => by
    by_cases h : s n < ((q n).1 : ℝ)
    · simp only [hvdef, h, ↓reduceIte]
    · simp only [hvdef, h, ↓reduceIte]; exact hst n
  have hvt : ∀ n, v n ≤ t n := fun n => by
    by_cases h : s n < ((q n).1 : ℝ)
    · simp only [hvdef, h, ↓reduceIte]; exact (q n).1.2.2
    · simp only [hvdef, h, ↓reduceIte]; exact le_rfl
  have hX : ∀ m : ℕ, 1 ≤ m → STlenL n_ p m →
      PrecL sz μ (U := fun n => TimeIcc s v n) (fun n u ω => STXiLg Cm.toFlowFM n (u : ℝ) m ω)
        (fun n _ _ => XL m n (v n)) := fun m hm hl =>
    NQEndFlowGen_restrict_pair (s := s) (t := t) (v := v) hvt
      (F := fun n w ω => STXiLg Cm.toFlowFM n w m ω) (Z := fun n u => XL m n u) (hXLp m hm hl)
  have hY : ∀ m : ℕ, 1 ≤ m → m ≤ n_ →
      PrecL sz μ (U := fun n => TimeIcc s v n) (fun n u ω => STXiLKg Cm.toFlowFM n (u : ℝ) m ω)
        (fun n _ _ => XLK m n (v n)) := fun m hm hm' =>
    NQEndFlowGen_restrict_pair (s := s) (t := t) (v := v) hvt
      (F := fun n w ω => STXiLKg Cm.toFlowFM n w m ω) (Z := fun n u => XLK m n u) (hXLKp m hm hm')
  have hcore := QtNZFlowGen_core Cm μ F hd h𝔠 hτR hKb hsize hband hs0 (fun n => (hst n).le) ht1 hcase hrange hsv hvt hLK
    (hGrid v hsv hvt) hLin hn hp hC5 hKer (X := fun m n => XL m n (v n)) (Y := fun m n => XLK m n (v n))
    (fun m n => hXL m n _) (fun m n => hXLK m n _) hX hY
    (fun n => (q n).2.1.1.1) (fun n => (q n).2.1.1.2) (fun n => (q n).2.1.2) (fun n => (q n).2.2)
  have hBs : ∀ n, 0 < sz.Bctl n (s n) := fun n => st_Bctl_pos sz ((hst n).trans (ht1 n))
  have hζ1 : ∀ n, 1 ≤ (sz.Bctl n (s n)) ^ (1 / 6 : ℝ) * XLK n_ n (s n) +
      STbootRHS 2 (fun m => XL m n (s n)) (fun m => XLK m n (s n)) (sz.Bctl n (s n)) n_ p := by
    intro n
    have h0 : 0 ≤ (sz.Bctl n (s n)) ^ (1 / 6 : ℝ) * XLK n_ n (s n) :=
      mul_nonneg (Real.rpow_nonneg (hBs n).le _) (zero_le_one.trans (hXLK _ _ _))
    have := nzFlow_bootRHS_one_le (lo := 2) (XL := fun m => XL m n (s n)) (XLK := fun m => XLK m n (s n))
      (B := sz.Bctl n (s n)) (k := n_) (p := p) (by omega) (fun m => hXL _ _ _)
      (fun m => zero_le_one.trans (hXLK _ _ _)) (hBs n).le
    linarith
  have hcoll := QtNZFlowGen_collapsed Cm.toFlowFM μ hsize hLK (k := n_) (by omega) hBs hζ1
    (fun n => (q n).2.1.1.1) (fun n => (q n).2.1.1.2) (fun n => (q n).2.2)
  intro τ hτ D hD
  filter_upwards [hcore τ hτ D hD, hcoll τ hτ D hD] with n h1 h2
  by_cases hn' : s n < ((q n).1 : ℝ)
  · -- the section is not collapsed: `v n = u_n`
    have hv : v n = ((q n).1 : ℝ) := by simp only [hvdef, hn', ↓reduceIte]
    simp only [badSetAt] at h1 ⊢
    rw [hv] at h1
    exact h1
  · -- collapsed: `u_n = s_n`
    have hu : ((q n).1 : ℝ) = s n := le_antisymm (not_lt.1 hn') (q n).1.2.1
    refine le_trans (measure_mono ?_) h2
    intro ω hω
    simp only [badSetAt, Set.mem_ofPred_eq] at hω ⊢
    obtain ⟨_, hω⟩ := hω
    rw [hu] at hω
    exact ⟨(), hω⟩

end SectionProof

/-! ## 4. Target 11: the per-time pin `stOeqNZPTgL''_of`

The family-premise table (ticket T2505): rows 1-6 are the premises of `gridGoodNgL_of` and `nqLinGoodgL_of`; row 3 the spectral data (`DecayGen_Spec`) and the inline `‖m‖ ≤ 1`; row 4 the
variance law of the walk (`S n = SB d (L n) (lam' n)`, the row sums); row 7 `GridRepTailGen_Ker`; row 9 `B45Gen_Facts` (its fields `ZeroModeGen_KerSums` are read here, `ZeroModeGen_WardCls` by
`stXiRoundNZgL_of`); row 11 the drift classes (eventual in `n`); row 12 the flow window `∃ τ > 0, RangeCond τ (T0 sz z)`; row 14 D1 `QtNZGen_KerNZFam` (`∃ C5` after `(k, κ, 𝔡)`, before `(sz, z)`) and
R1 in the A-form (`lam² ≤ Aof κ gK²`, a premise of `nzGridEndNg`, per flow, per index).  No D1 of the non-alternating half, no `Θ`-decay class, no `∀ n` drift premise.  The exponents `ε₁ τ' D' C_K`
of the endpoint are chosen after `(sz, z)` inside `nzGridEndNg`; the pinned `∃`: `𝔠d`, `C5`, `Aof κ`. -/

section Public

/-- **Target 11, `stOeqNZPTgL''_of`** (conclusion = `T2505_OeqNZPTgL''`; band `stOeqNZPT''_holds`, `QtNonzeroFlow:837`): the per-time case-(ii) R2* pin over a carrier family from the
family-premise table.  `𝔠_d = min 𝔠G 𝔠L` with `𝔠G`, `𝔠L` the constants of `gridGoodNgL_of` and `nqLinGoodgL_of` at the same `(κ, ε, 𝔡, C_d)`; `STConStInd` passes to the larger exponents
(`nzFlow_conStInd_exp_mono`), the good event `gridGoodNgL_of` is re-instantiated on every window `[s, v]` (`st_conStInd_sub`, the restriction of `STStep2ConclgL`); then
`perTimeDomAt_iff_forall_section` and `QtNZFlowGen_section`.  There is no `1/(2d)` in `𝔠_d` (case (ii) uses no `st_window`); the kernel constant is `C5` of D1 at `k = n_`. -/
theorem stOeqNZPTgL''_of (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ)
    (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop) (mkM : ∀ (sz : Sizes d) (z : ℕ → ℂ), Step2Mat sz)
    (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ)
    (Hf : ∀ (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ), ℝ → sz.SeqΩ → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    (E lam' gK : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ)
    (Ψ : ∀ (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ), Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    (Aof : ℝ → ℝ)
    -- rows 1-6 (the premises of `gridGoodNgL_of` and `nqLinGoodgL_of`)
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
    -- rows 3, 4, 7, 11: the spectral data, the walk's variance law, the kernel class, the drift classes
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
    -- row 9: the carrier facts `ZeroModeGen_KerSums` (a field of `B45Gen_Facts`)
    (hB45 : B45Gen_Facts d Flow (fun sz z => (mkM sz z).toFlowFM))
    -- row 14: D1 (the `∃ C5` before `(sz, z)`) and R1 in the A-form (the pinned `Aof κ`); row 12: the flow window
    (hKerFam : QtNZGen_KerNZFam d Flow (fun sz z => (mkM sz z).toFlowFM) gK Aof)
    (hR1 : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z → ∀ n, sz.lam n ^ 2 ≤ Aof κ * gK sz z n ^ 2)
    (hT0 : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → 0 < ε → Flow sz κ ε 𝔠 𝔡 z →
      ∃ τ : ℝ, 0 < τ ∧ sz.RangeCond τ (T0 sz z)) :
    STOeqNZPTgL'' d law Flow (fun sz z => (mkM sz z).toFlowFM) T0 := by
  have hGG := gridGoodNgL_of d law Flow mkM T0 Hf E lam' Ψ hSE hFlow hSpec hL hW hLaw hC hWard hKcal hEK
  have hNL := nqLinGoodgL_of d law Flow mkM T0 Hf E lam' Ψ hSE hFlow hL hW hLaw hC
  intro hd κ ε 𝔡 hκ hε h𝔡 Cd hCd
  obtain ⟨𝔠G, hG0, hG1, HG⟩ := hGG hd κ ε 𝔡 hκ hε h𝔡 Cd hCd
  obtain ⟨𝔠L, hL0, hL1, HL⟩ := hNL hd κ ε 𝔡 hκ hε h𝔡 Cd hCd
  obtain ⟨𝔠d, h𝔠d⟩ : ∃ 𝔠d : ℝ, 𝔠d = min 𝔠G 𝔠L := ⟨_, rfl⟩
  have h𝔠d0 : 0 < 𝔠d := by rw [h𝔠d]; exact lt_min hG0 hL0
  have h𝔠dG : 𝔠d ≤ 𝔠G := by rw [h𝔠d]; exact min_le_left _ _
  have h𝔠dL : 𝔠d ≤ 𝔠L := by rw [h𝔠d]; exact min_le_right _ _
  refine ⟨𝔠d, h𝔠d0, h𝔠dG.trans hG1, ?_⟩
  intro 𝔠 sz z hflow s t hs hst ht hR hK hKw hLK hcon hStep2
  have hA := hFlow.1 sz κ ε 𝔠 𝔡 z hflow
  have ht1 : ∀ n, t n < 1 := fun n => (ht n).trans_lt (hFlow.2 sz κ ε 𝔠 𝔡 z hκ hflow n)
  obtain ⟨τ0, hτ0, hrange0⟩ := hT0 sz κ ε 𝔠 𝔡 z hκ hε hflow
  have hrange : sz.RangeCond τ0 t := nqEnd_rangeCond_mono sz le_rfl ht hrange0
  have hconG : sz.STConStInd 𝔠G s t := nzFlow_conStInd_exp_mono sz h𝔠d0 h𝔠dG ht1 hcon
  have hconL : sz.STConStInd 𝔠L s t := nzFlow_conStInd_exp_mono sz h𝔠d0 h𝔠dL ht1 hcon
  have hGrid : ∀ v : ℕ → ℝ, (∀ n, s n < v n) → (∀ n, v n ≤ t n) → GridGoodNConclg (mkM sz z) (law sz) s v :=
    fun v hsv hvt => HG 𝔠 sz z hflow s v hs hsv (fun n => (hvt n).trans (ht n)) trivial hK hKw hLK
      (st_conStInd_sub sz hG0 hconG (fun n => le_rfl) hsv hvt ht1) (NQEndFlowGen_step2_restrict hvt hStep2)
  have hLin : NQLinConclg (mkM sz z) (law sz) s t :=
    HL 𝔠 sz z hflow s t hs hst ht trivial hK hKw hLK hconL hStep2
  obtain ⟨κm, hspec⟩ := hSpec sz κ ε 𝔠 𝔡 z hκ hflow
  obtain ⟨C₆, -, hB⟩ := hB45 κ hκ
  have hKS : ∀ n : ℕ, ZeroModeGen_KerSums (mkM sz z).toFlowFM n := (hB sz ε 𝔠 𝔡 z hflow).2.2.2.1
  have F : QtNZFlowGen_Facts (mkM sz z) (law sz) (Hf sz z) (E sz z) (lam' sz z) (gK sz z) (Ψ sz z) κm (Aof κ) :=
    ⟨hL sz κ ε 𝔠 𝔡 z hκ hflow, hW sz κ ε 𝔠 𝔡 z hκ hflow, hspec, hm sz κ ε 𝔠 𝔡 z hκ hflow, hSeq sz z, hS sz z,
      hRow sz κ ε 𝔠 𝔡 z hκ hflow, hKS, hKK sz z, hExp sz κ ε 𝔠 𝔡 z hκ hflow, hKL sz κ ε 𝔠 𝔡 z hκ hflow,
      hKT sz κ ε 𝔠 𝔡 z hκ hflow, hU sz κ ε 𝔠 𝔡 z hκ hflow, hLaw sz z, hC sz z, hR1 sz κ ε 𝔠 𝔡 z hκ hflow⟩
  intro n_ p hn hp XL XLK hXL hXLK hXLp hXLKp
  obtain ⟨C5, hC5, hKerAll⟩ := hKerFam hd n_ hn κ 𝔡 hκ h𝔡
  have hKer := hKerAll sz ε 𝔠 z hflow
  refine (perTimeDomAt_iff_forall_section (law sz) sz.size
    (fun n => ⟨(⟨s n, le_rfl, (hst n).le⟩, ⟨((fun _ => true), Finset.univ), Finset.subset_univ _⟩, fun _ => 0)⟩) _ _).2 ?_
  intro q
  exact QtNZFlowGen_section (mkM sz z) (law sz) F hd hA.1 hτ0 hK hA.2.2.1 hA.2.2.2.1 hs hst ht1 hR hrange hLK hGrid hLin hn hp hC5
    hKer hXL hXLK hXLp hXLKp q

end Public

/-! ## 5. Target 12: the lift `STNZConclPTgL'' → STNZConclgL''` and `stOeqNZgL''_of` -/

section Lift

variable {d : ℕ}

/-- **The mesh arithmetic with the factor `2^{n_}` of `(normQA2)`** (band `nzLift_arith`, `QtNonzeroFlowLift:450`, with the Hölder exponent `c` of `LemDecCalELipG_FlowMod`; paper-delta
candidate `T2505c`): for `δ ≤ N^{-(6 n_ + 18 + 2c)}`, `c ≥ 0` and `2^{n_}(3 n_ + 1) ≤ N`, `2^{n_} N^{n_} (3 n_ N^{2n_+6} N^c √δ + N^{2n_+2} δ) ≤ 1` (the two summands of the bracket times `N^{n_}`
are `≤ 3 n_ N^{-3}` and `≤ N^{-3}`; then `2^{n_}(3 n_ + 1) N^{-3} ≤ N · N^{-3} ≤ 1`).  The band value is `c = 1`, `6 n_ + 20`. -/
private theorem QtNZLiftGen_arith {N δ c : ℝ} {n_ : ℕ} (hN : (2 ^ n_ * (3 * n_ + 1) : ℝ) ≤ N) (hc : 0 ≤ c) (hδ0 : 0 ≤ δ)
    (hδ : δ ≤ N ^ (-(((6 * n_ + 18 : ℕ) : ℝ) + 2 * c))) :
    2 ^ n_ * (N ^ n_ * (3 * n_ * N ^ (2 * n_ + 6) * N ^ c * Real.sqrt δ + N ^ (2 * n_ + 2) * δ)) ≤ 1 := by
  have hn0 : (0 : ℝ) ≤ n_ := Nat.cast_nonneg _
  have h2n : (1 : ℝ) ≤ 2 ^ n_ := one_le_pow₀ (by norm_num)
  have h3n : (1 : ℝ) ≤ 3 * n_ + 1 := by linarith
  have hprod1 : (1 : ℝ) ≤ 2 ^ n_ * (3 * n_ + 1) := by nlinarith
  have hN1 : (1 : ℝ) ≤ N := hprod1.trans hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hC1 : (1 : ℝ) ≤ N ^ c := Real.one_le_rpow hN1 hc
  have hC0 : (0 : ℝ) < N ^ c := by linarith
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = N ^ (3 * n_ + 9) * N ^ c := ⟨_, rfl⟩
  have hM0 : 0 < M := by rw [hM]; positivity
  have h2c : N ^ (2 * c) = (N ^ c) ^ 2 := by
    rw [show 2 * c = c + c by ring, Real.rpow_add hN0, sq]
  have hMsq : N ^ (6 * n_ + 18) * (N ^ c) ^ 2 = M ^ 2 := by
    rw [hM, mul_pow, ← pow_mul]; congr 2; omega
  have hδM : δ ≤ (M ^ 2)⁻¹ := by
    refine hδ.trans (le_of_eq ?_)
    rw [Real.rpow_neg hN0.le, Real.rpow_add hN0, Real.rpow_natCast, h2c, hMsq]
  have hsqrt : Real.sqrt δ ≤ M⁻¹ := by
    have h2 : Real.sqrt δ ≤ Real.sqrt ((M ^ 2)⁻¹) := Real.sqrt_le_sqrt hδM
    rwa [← inv_pow, Real.sqrt_sq (by positivity)] at h2
  have hA : N ^ n_ * (N ^ (2 * n_ + 6)) = N ^ (3 * n_ + 6) := by rw [← pow_add]; congr 1; ring
  have hM3 : N ^ (3 * n_ + 9) = N ^ (3 * n_ + 6) * N ^ 3 := by rw [← pow_add]
  have t1 : N ^ n_ * (3 * n_ * N ^ (2 * n_ + 6) * N ^ c * Real.sqrt δ) ≤ 3 * n_ * (N ^ 3)⁻¹ := by
    calc N ^ n_ * (3 * n_ * N ^ (2 * n_ + 6) * N ^ c * Real.sqrt δ)
        = 3 * n_ * (N ^ n_ * N ^ (2 * n_ + 6)) * N ^ c * Real.sqrt δ := by ring
      _ = 3 * n_ * N ^ (3 * n_ + 6) * N ^ c * Real.sqrt δ := by rw [hA]
      _ ≤ 3 * n_ * N ^ (3 * n_ + 6) * N ^ c * M⁻¹ := by gcongr
      _ = 3 * n_ * (N ^ 3)⁻¹ := by
          rw [hM, hM3]; field_simp
  have hB : N ^ n_ * N ^ (2 * n_ + 2) = N ^ (3 * n_ + 2) := by rw [← pow_add]; congr 1; ring
  have hMM : N ^ (3 * n_ + 2) * N ^ 3 ≤ M ^ 2 := by
    rw [← hMsq, ← pow_add]
    have h6 : N ^ (3 * n_ + 2 + 3) ≤ N ^ (6 * n_ + 18) := pow_le_pow_right₀ hN1 (by omega)
    have h7 : N ^ (6 * n_ + 18) ≤ N ^ (6 * n_ + 18) * (N ^ c) ^ 2 := by
      have : 1 ≤ (N ^ c) ^ 2 := one_le_pow₀ hC1
      nlinarith [pow_pos hN0 (6 * n_ + 18)]
    exact h6.trans h7
  have t2 : N ^ n_ * (N ^ (2 * n_ + 2) * δ) ≤ (N ^ 3)⁻¹ := by
    calc N ^ n_ * (N ^ (2 * n_ + 2) * δ) = N ^ (3 * n_ + 2) * δ := by rw [← hB]; ring
      _ ≤ N ^ (3 * n_ + 2) * (M ^ 2)⁻¹ := by gcongr
      _ ≤ N ^ (3 * n_ + 2) * (N ^ (3 * n_ + 2) * N ^ 3)⁻¹ := by gcongr
      _ = (N ^ 3)⁻¹ := by field_simp
  have hmid : N ^ n_ * (3 * n_ * N ^ (2 * n_ + 6) * N ^ c * Real.sqrt δ + N ^ (2 * n_ + 2) * δ) ≤
      (3 * n_ + 1) * (N ^ 3)⁻¹ := by
    calc N ^ n_ * (3 * n_ * N ^ (2 * n_ + 6) * N ^ c * Real.sqrt δ + N ^ (2 * n_ + 2) * δ)
        = N ^ n_ * (3 * n_ * N ^ (2 * n_ + 6) * N ^ c * Real.sqrt δ) + N ^ n_ * (N ^ (2 * n_ + 2) * δ) := by ring
      _ ≤ 3 * n_ * (N ^ 3)⁻¹ + (N ^ 3)⁻¹ := add_le_add t1 t2
      _ = (3 * n_ + 1) * (N ^ 3)⁻¹ := by ring
  have hN3 : 2 ^ n_ * ((3 * n_ + 1 : ℝ) * (N ^ 3)⁻¹) ≤ 1 := by
    have hN3pos : 0 < N ^ 3 := by positivity
    have e : 2 ^ n_ * ((3 * n_ + 1 : ℝ) * (N ^ 3)⁻¹) = (2 ^ n_ * (3 * n_ + 1)) / N ^ 3 := by
      field_simp
    rw [e, div_le_one hN3pos]
    have : N ≤ N ^ 3 := le_self_pow₀ hN1 (by norm_num)
    linarith
  exact (mul_le_mul_of_nonneg_left hmid (by positivity)).trans hN3

/-- **The `ξ` closeness of the projected tensor on the good event** (band `nzLift_xi_close`, `QtNonzeroFlowLift:526`; one-sided, for `s ≤ u' ≤ u ≤ t`, `u - u' ≤ N^{-(6 n_ + 18 + 2c)}`, paper-delta
candidate `T2505c`): `‖(Q^{(A)}(𝓛-𝒦)_u)_a‖ / B_u^{n_} ≤ ‖(Q^{(A)}(𝓛-𝒦)_{u'})_a‖ / B_{u'}^{n_} + 1`.  `Q^{(A)}` is linear (`zeroModeSet_sub`), so `Q^{(A)}(𝓛-𝒦)_u = Q^{(A)}(𝓛-𝒦)_{u'} + Q^{(A)}Δ`
with `Δ_b = (𝓛_u - 𝓛_{u'})_b - (𝒦_u - 𝒦_{u'})_b`; `‖(Q^{(A)}Δ)_a‖ ≤ 2^{n_} sup_b ‖Δ_b‖` (`nzFlow_proj_le`) and `‖Δ_b‖ ≤ 3 n_ N^{2n_+6} N^c √δ + N^{2n_+2} δ` (the `𝓛` modulus `hL` of
`lemDecCalELipG_loops`, the `𝒦` modulus `hK` of `NQEndFlowGen_KLip`, uniformly in `b`); `2^{n_} N^{n_} (…) ≤ 1` (`QtNZLiftGen_arith`), `N⁻¹ ≤ B_u` (`cont_inv_size_le_Bctl`); the ratio term has the
favourable sign (`B_{u'} ≤ B_u`, `STBctl_mono`) and is dropped. -/
private theorem QtNZLiftGen_xi_close (sz : Sizes d) (Cf : FlowFM sz) (n : ℕ) {c : ℝ} (hc : 0 ≤ c) {n_ : ℕ} {s t u u' N : ℝ} (ω : sz.SeqΩ)
    (hs0 : 0 ≤ s) (hsu' : s ≤ u') (hu'u : u' ≤ u) (hut : u ≤ t) (ht1 : t < 1)
    (hN : N = ((sz.size n : ℕ) : ℝ)) (hM : (2 ^ n_ * (3 * n_ + 1) : ℝ) ≤ N)
    (hΔ : u - u' ≤ N ^ (-(((6 * n_ + 18 : ℕ) : ℝ) + 2 * c)))
    (A : Finset (Fin n_)) (σ : Fin n_ → Bool) (a : Fin n_ → Zd d (sz.L n))
    (hL : ∀ b : Fin n_ → Zd d (sz.L n),
      ‖Cf.L n u σ b ω - Cf.L n u' σ b ω‖ ≤ 3 * (n_ : ℝ) * N ^ (2 * n_ + 6) * N ^ c * Real.sqrt |u - u'|)
    (hK : ∀ b : Fin n_ → Zd d (sz.L n), ‖Cf.K n u σ b - Cf.K n u' σ b‖ ≤ N ^ (2 * n_ + 2) * |u - u'|) :
    ‖zeroModeSet d (sz.L n) A (fun b => Cf.L n u σ b ω - Cf.K n u σ b) a‖ / (sz.Bctl n u) ^ n_ ≤
      ‖zeroModeSet d (sz.L n) A (fun b => Cf.L n u' σ b ω - Cf.K n u' σ b) a‖ / (sz.Bctl n u') ^ n_ + 1 := by
  have hu1 : u < 1 := hut.trans_lt ht1
  have hu'1 : u' < 1 := hu'u.trans_lt hu1
  have hu'0 : 0 ≤ u' := hs0.trans hsu'
  have hu0 : 0 ≤ u := hu'0.trans hu'u
  have hn0 : (0 : ℝ) ≤ n_ := Nat.cast_nonneg _
  have h2n : (1 : ℝ) ≤ 2 ^ n_ := one_le_pow₀ (by norm_num)
  have h3n : (1 : ℝ) ≤ 3 * n_ + 1 := by linarith
  have hprod1 : (1 : ℝ) ≤ 2 ^ n_ * (3 * n_ + 1) := by nlinarith
  have hN1 : 1 ≤ N := hprod1.trans hM
  have hN0 : 0 < N := by linarith
  have hBu : 0 < sz.Bctl n u := st_Bctl_pos sz hu1
  have hBu' : 0 < sz.Bctl n u' := st_Bctl_pos sz hu'1
  have hBle : sz.Bctl n u' ≤ sz.Bctl n u := STBctl_mono sz n hu'u hu1
  have hBinv : N⁻¹ ≤ sz.Bctl n u := by
    rw [hN]; exact RBM.Ind.ContinuityNet.cont_inv_size_le_Bctl sz n hu0 hu1
  have hδ0 : 0 ≤ u - u' := sub_nonneg.2 hu'u
  have hK' := hK
  have hL' := hL
  simp only [abs_of_nonneg hδ0] at hK' hL'
  have harith := QtNZLiftGen_arith hM hc hδ0 hΔ
  have hNn : 0 < N ^ n_ := pow_pos hN0 _
  -- the entrywise bound of `Δ`
  obtain ⟨x, hx⟩ : ∃ x : ℝ, x = 3 * (n_ : ℝ) * N ^ (2 * n_ + 6) * N ^ c * Real.sqrt (u - u') +
      N ^ (2 * n_ + 2) * (u - u') := ⟨_, rfl⟩
  have hx0 : 0 ≤ x := by rw [hx]; positivity
  have hent : ∀ b : Fin n_ → Zd d (sz.L n),
      ‖(Cf.L n u σ b ω - Cf.K n u σ b) - (Cf.L n u' σ b ω - Cf.K n u' σ b)‖ ≤ x := by
    intro b
    have e : (Cf.L n u σ b ω - Cf.K n u σ b) - (Cf.L n u' σ b ω - Cf.K n u' σ b) =
        (Cf.L n u σ b ω - Cf.L n u' σ b ω) - (Cf.K n u σ b - Cf.K n u' σ b) := by ring
    rw [e, hx]
    calc _ ≤ ‖Cf.L n u σ b ω - Cf.L n u' σ b ω‖ + ‖Cf.K n u σ b - Cf.K n u' σ b‖ := norm_sub_le _ _
      _ ≤ _ := add_le_add (hL' b) (hK' b)
  have hproj := nzFlow_proj_le A
    (fun b => (Cf.L n u σ b ω - Cf.K n u σ b) - (Cf.L n u' σ b ω - Cf.K n u' σ b)) hx0 hent a
  -- `2^{n_} x ≤ B_u^{n_}`
  have hsmall : 2 ^ n_ * x ≤ (sz.Bctl n u) ^ n_ := by
    have h1 : (N ^ n_)⁻¹ ≤ (sz.Bctl n u) ^ n_ := by
      rw [← inv_pow]; exact pow_le_pow_left₀ (inv_nonneg.2 hN0.le) hBinv n_
    refine le_trans ?_ h1
    have harith' : 2 ^ n_ * (N ^ n_ * x) ≤ 1 := by rw [hx]; exact harith
    calc 2 ^ n_ * x = (N ^ n_)⁻¹ * (2 ^ n_ * (N ^ n_ * x)) := by field_simp
      _ ≤ (N ^ n_)⁻¹ * 1 := mul_le_mul_of_nonneg_left harith' (inv_nonneg.2 hNn.le)
      _ = (N ^ n_)⁻¹ := mul_one _
  -- linearity of `Q^{(A)}`
  have hlin : zeroModeSet d (sz.L n) A (fun b => Cf.L n u σ b ω - Cf.K n u σ b) a =
      zeroModeSet d (sz.L n) A (fun b => Cf.L n u' σ b ω - Cf.K n u' σ b) a +
        zeroModeSet d (sz.L n) A
          (fun b => (Cf.L n u σ b ω - Cf.K n u σ b) - (Cf.L n u' σ b ω - Cf.K n u' σ b)) a := by
    have h := zeroModeSet_sub (d := d) (L := sz.L n) A
      (fun b => Cf.L n u σ b ω - Cf.K n u σ b) (fun b => Cf.L n u' σ b ω - Cf.K n u' σ b)
    have h2 := congrFun h a
    change zeroModeSet d (sz.L n) A (fun b => (Cf.L n u σ b ω - Cf.K n u σ b) -
        (Cf.L n u' σ b ω - Cf.K n u' σ b)) a =
      zeroModeSet d (sz.L n) A (fun b => Cf.L n u σ b ω - Cf.K n u σ b) a -
        zeroModeSet d (sz.L n) A (fun b => Cf.L n u' σ b ω - Cf.K n u' σ b) a at h2
    rw [h2]; ring
  have htri : ‖zeroModeSet d (sz.L n) A (fun b => Cf.L n u σ b ω - Cf.K n u σ b) a‖ ≤
      ‖zeroModeSet d (sz.L n) A (fun b => Cf.L n u' σ b ω - Cf.K n u' σ b) a‖ + (sz.Bctl n u) ^ n_ := by
    rw [hlin]
    refine (norm_add_le _ _).trans (add_le_add le_rfl (hproj.trans hsmall))
  have hBpow : 0 < (sz.Bctl n u) ^ n_ := pow_pos hBu _
  calc ‖zeroModeSet d (sz.L n) A (fun b => Cf.L n u σ b ω - Cf.K n u σ b) a‖ / (sz.Bctl n u) ^ n_
      ≤ (‖zeroModeSet d (sz.L n) A (fun b => Cf.L n u' σ b ω - Cf.K n u' σ b) a‖ + (sz.Bctl n u) ^ n_) /
          (sz.Bctl n u) ^ n_ := div_le_div_of_nonneg_right htri hBpow.le
    _ = ‖zeroModeSet d (sz.L n) A (fun b => Cf.L n u' σ b ω - Cf.K n u' σ b) a‖ / (sz.Bctl n u) ^ n_ + 1 := by
        rw [add_div, div_self hBpow.ne']
    _ ≤ ‖zeroModeSet d (sz.L n) A (fun b => Cf.L n u' σ b ω - Cf.K n u' σ b) a‖ / (sz.Bctl n u') ^ n_ + 1 := by
        refine add_le_add ?_ le_rfl
        exact div_le_div_of_nonneg_left (norm_nonneg _) (pow_pos hBu' _) (pow_le_pow_left₀ hBu'.le hBle _)

/-- **The lift `STNZConclPTgL'' → STNZConclgL''` at one carrier** (private as the band `nzLift_lift`, `QtNonzeroFlowLift:692`: its binder is the per-time pin; public at the family level:
`stOeqNZgL''_of`; the net remark `3_5:1931`).  At the envelope controls `(XL♯, XLK♯)` the per-time pin gives `PrecPTL (ξ ≺ ζ♯)`; the one-sided net core (`nzLift_core_below`, `P = μ`, `Ξ = G` the good
event of `LemDecCalELipG_FlowMod`, `ε = 1`, `A = 6 n_ + 18 + 2c`, `Cv = 2 n_`) gives `PrecL (ξ ≺ ζ♯)`, and `ζ♯ ≤ ζ` gives `PrecL (ξ ≺ ζ)`.  Only the label set `V_n`, the `ξ`-modulus
(`QtNZLiftGen_xi_close`: the `𝓛` modulus `lemDecCalELipG_loops`, the `𝒦` modulus `hKLip`, `M = 2^{n_}(3 n_ + 1)` in `LemDecCalELip_envg`) and the cardinality (`nzLift_card_V`) differ from
the case-(i) lift `QtLiftGen_lift`. -/
private theorem QtNZLiftGen_lift {sz : Sizes d} (Cm : Step2Mat sz) (μ : Measure sz.SeqΩ) {E : ℕ → ℝ} (hL : StepDecompGen_LoopForm Cm E)
    (hm : ∀ n, ‖Cm.m n‖ ≤ 1) {κm : ℝ} (hspec : DecayGen_Spec Cm.toFlowFM κm) {c : ℝ} (hc : 0 ≤ c)
    (hFM : LemDecCalELipG_FlowMod Cm μ c) (hsize : sz.SizeTendsto) {s t : ℕ → ℝ} (hs0 : ∀ n, 0 ≤ s n) (hst : ∀ n, s n < t n)
    (ht1 : ∀ n, t n < 1) (htN : ∀ᶠ n in atTop, (1 - t n)⁻¹ ≤ ((sz.size n : ℕ) : ℝ))
    (hKLip : ∀ k : ℕ, 2 ≤ k → NQEndFlowGen_KLip Cm.toFlowFM t k) (hPT : STNZConclPTgL'' Cm.toFlowFM μ s t) :
    STNZConclgL'' Cm.toFlowFM μ s t := by
  obtain ⟨hκm, hIm, hηeq⟩ := hspec
  obtain ⟨Hm, G, hLM, hG, hmod⟩ := lemDecCalELipG_flowMod_base hFM
  intro n_ p hn hp XL XLK hXL hXLK hXLp hXLKp
  have hsizeN : Tendsto sz.size atTop atTop := sz.tendsto_size hsize
  have hXL' : ∀ m n u, 1 ≤ nqFlowSharp t XL m n u := fun m n u => nzLift_sharp_one_le t XL m n u
  have hXLK' : ∀ m n u, 1 ≤ nqFlowSharp t XLK m n u := fun m n u => nzLift_sharp_one_le t XLK m n u
  have hXLp' : ∀ m, 1 ≤ m → STlenL n_ p m →
      PrecL sz μ (U := STPair s t) (fun n q ω => STXiLg Cm.toFlowFM n q.1.1 m ω)
        (fun n q _ => nqFlowSharp t XL m n q.1.2) := fun m hm1 hl =>
    QtLiftGen_sharp_prec sz μ s t (fun n w ω => STXiLg Cm.toFlowFM n w m ω) XL m hXL (hXLp m hm1 hl)
  have hXLKp' : ∀ m, 1 ≤ m → m ≤ n_ →
      PrecL sz μ (U := STPair s t) (fun n q ω => STXiLKg Cm.toFlowFM n q.1.1 m ω)
        (fun n q _ => nqFlowSharp t XLK m n q.1.2) := fun m hm1 hm' =>
    QtLiftGen_sharp_prec sz μ s t (fun n w ω => STXiLKg Cm.toFlowFM n w m ω) XLK m hXLK (hXLKp m hm1 hm')
  have hPT' := hPT n_ p hn hp (fun m n u => nqFlowSharp t XL m n u) (fun m n u => nqFlowSharp t XLK m n u)
    hXL' hXLK' hXLp' hXLKp'
  have hmain : PrecL sz μ
      (U := fun n => TimeIcc s t n × {σA : (Fin n_ → Bool) × Finset (Fin n_) // STIdiff σA.1 ⊆ σA.2} ×
        (Fin n_ → Zd d (sz.L n)))
      (fun n q ω => ‖zeroModeSet d (sz.L n) q.2.1.1.2
          (fun b : Fin n_ → Zd d (sz.L n) => Cm.L n (q.1 : ℝ) q.2.1.1.1 b ω - Cm.K n (q.1 : ℝ) q.2.1.1.1 b) q.2.2‖ /
        (sz.Bctl n (q.1 : ℝ)) ^ n_)
      (fun n q _ => (sz.Bctl n (q.1 : ℝ)) ^ (1 / 6 : ℝ) * nqFlowSharp t XLK n_ n (q.1 : ℝ) +
        STbootRHS 2 (fun m => nqFlowSharp t XL m n (q.1 : ℝ)) (fun m => nqFlowSharp t XLK m n (q.1 : ℝ))
          (sz.Bctl n (s n)) n_ p) := by
    refine nzLift_core_below (Ω := sz.SeqΩ) μ sz.size hsizeN s t (fun n => (hst n).le)
      (fun n => by linarith [hs0 n, ht1 n])
      (fun n => {σA : (Fin n_ → Bool) × Finset (Fin n_) // STIdiff σA.1 ⊆ σA.2} × (Fin n_ → Zd d (sz.L n)))
      _ _ (((6 * n_ + 18 : ℕ) : ℝ) + 2 * c) ((2 * n_ : ℕ) : ℝ) (by positivity) (Nat.cast_nonneg _) ?_ hPT'
      G hG (fun _ => 1) (fun _ => zero_le_one) ?_ ?_
    · -- `hcard`
      filter_upwards [hsizeN.eventually_ge_atTop 4] with n hn4 using nzLift_card_V sz n_ n hn4
    · -- `hlow`: `ζ♯ ≥ 1`
      exact Eventually.of_forall fun n q ω =>
        nzLift_zeta_one_le sz ht1 n_ p n (by omega) q.1.2.1 q.1.2.2
    · -- `hclose`
      have hQev := LemDecCalELip_envg (Cm := Cm) hκm hIm hηeq hsize htN (2 ^ n_ * (3 * (n_ : ℝ) + 1))
      have hQ : ∀ᶠ n in atTop, (Cm.eta n (t n))⁻¹ ≤ ((sz.size n : ℕ) : ℝ) ^ 2 := hQev.mono fun n h => h.2.2.1
      filter_upwards [hQev, lemDecCalELipG_loops hL hLM hc hmod hm ht1 hQ, hKLip n_ hn] with n hnum hloop hK
      obtain ⟨hM, hN1, hQn, -⟩ := hnum
      intro ω hω u u' hle hΔ v
      obtain ⟨⟨⟨σ, A⟩, hσA⟩, a⟩ := v
      refine ⟨?_, ?_⟩
      · exact QtNZLiftGen_xi_close sz Cm.toFlowFM n hc ω (hs0 n) u'.2.1 hle u.2.2 (ht1 n) rfl hM hΔ A σ a
          (fun b => (hloop ω hω).1 u u' ((hs0 n).trans u.2.1) u.2.2 ((hs0 n).trans u'.2.1) u'.2.2 σ b)
          (fun b => hK u u' ((hs0 n).trans u.2.1) u.2.2 ((hs0 n).trans u'.2.1) u'.2.2 σ b)
      · have h1 := nzLift_zeta_mono sz ht1 hXL hXLK n_ p n u'.2.1 hle u.2.2
        have h2 := nzLift_zeta_one_le sz ht1 (XL := XL) (XLK := XLK) n_ p n (by omega) u.2.1 u.2.2
        change (sz.Bctl n (u' : ℝ)) ^ (1 / 6 : ℝ) * nqFlowSharp t XLK n_ n (u' : ℝ) +
            STbootRHS 2 (fun m => nqFlowSharp t XL m n (u' : ℝ)) (fun m => nqFlowSharp t XLK m n (u' : ℝ))
              (sz.Bctl n (s n)) n_ p ≤
          2 * ((sz.Bctl n (u : ℝ)) ^ (1 / 6 : ℝ) * nqFlowSharp t XLK n_ n (u : ℝ) +
            STbootRHS 2 (fun m => nqFlowSharp t XL m n (u : ℝ)) (fun m => nqFlowSharp t XLK m n (u : ℝ))
              (sz.Bctl n (s n)) n_ p)
        linarith
  exact NQEndFlowGen_prec_of_le_right hmain fun n q ω =>
    nzLift_zeta_le sz ht1 hXL hXLK n_ p n q.1.2.1 q.1.2.2

/-- **Target 12, `stOeqNZgL''_of`** (conclusion = `T2505_OeqNZgL''`; band `stOeqNZ''_holds`, `QtNonzeroFlowLift:763`; paper-delta candidate `T2505d`): the uniform case-(ii) R2* pin over a carrier
family, with the constant `𝔠_d` of `stOeqNZPTgL''_of`.  The uniform conclusion follows from the per-time pin by `QtNZLiftGen_lift`; the flow premises beyond those of `stOeqNZPTgL''_of` are the `𝒦`
modulus (family row 15, `hKLip`, `NQEndFlowGen_KLipFam`) and the `𝓛` modulus (family row 16, `hFM`, `∃ c` after `(κ, ε, 𝔡)`, band `c = 1`); the same eventual regime facts as row a
(`QtLiftGen_htN`). -/
theorem stOeqNZgL''_of (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ)
    (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop) (mkM : ∀ (sz : Sizes d) (z : ℕ → ℂ), Step2Mat sz)
    (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ)
    (Hf : ∀ (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ), ℝ → sz.SeqΩ → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    (E lam' gK : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ)
    (Ψ : ∀ (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ), Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    (Aof : ℝ → ℝ)
    -- rows 1-6 (the premises of `gridGoodNgL_of` and `nqLinGoodgL_of`)
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
    -- rows 3, 4, 7, 11: the spectral data, the walk's variance law, the kernel class, the drift classes
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
    -- row 9: the carrier facts `ZeroModeGen_KerSums` (a field of `B45Gen_Facts`)
    (hB45 : B45Gen_Facts d Flow (fun sz z => (mkM sz z).toFlowFM))
    -- row 14: D1 (the `∃ C5` before `(sz, z)`) and R1 in the A-form (the pinned `Aof κ`); row 12: the flow window
    (hKerFam : QtNZGen_KerNZFam d Flow (fun sz z => (mkM sz z).toFlowFM) gK Aof)
    (hR1 : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z → ∀ n, sz.lam n ^ 2 ≤ Aof κ * gK sz z n ^ 2)
    (hT0 : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → 0 < ε → Flow sz κ ε 𝔠 𝔡 z →
      ∃ τ : ℝ, 0 < τ ∧ sz.RangeCond τ (T0 sz z))
    -- rows 15, 16: the `𝒦` modulus (U3s2c, `NQEndFlowGen_KLipFam`) and the `𝓛` modulus (U4s3, family row 16)
    (hKLip : NQEndFlowGen_KLipFam d Flow (fun sz z => (mkM sz z).toFlowFM) T0) (hFM : QtBootGen_FlowModFam d law Flow mkM) :
    STOeqNZgL'' d law Flow (fun sz z => (mkM sz z).toFlowFM) T0 := by
  have hPT := stOeqNZPTgL''_of d law Flow mkM T0 Hf E lam' gK Ψ Aof hSE hFlow hSpec hL hW hLaw hC hWard hKcal hEK hm hSeq hS hRow hKK
    hExp hKL hKT hU hB45 hKerFam hR1 hT0
  intro hd κ ε 𝔡 hκ hε h𝔡 Cd hCd
  obtain ⟨𝔠d, h0, h1, H⟩ := hPT hd κ ε 𝔡 hκ hε h𝔡 Cd hCd
  obtain ⟨cH, hcH, hFMall⟩ := hFM κ ε 𝔡 hκ hε h𝔡
  refine ⟨𝔠d, h0, h1, ?_⟩
  intro 𝔠 sz z hflow s t hs hst ht hR hK hKw hLK hcon hStep2
  have hPT' := H 𝔠 sz z hflow s t hs hst ht hR hK hKw hLK hcon hStep2
  have hA := hFlow.1 sz κ ε 𝔠 𝔡 z hflow
  have ht1 : ∀ n, t n < 1 := fun n => (ht n).trans_lt (hFlow.2 sz κ ε 𝔠 𝔡 z hκ hflow n)
  obtain ⟨κm, hspec⟩ := hSpec sz κ ε 𝔠 𝔡 z hκ hflow
  obtain ⟨τ0, hτ0, hrange0⟩ := hT0 sz κ ε 𝔠 𝔡 z hκ hε hflow
  have hrange : sz.RangeCond τ0 t := nqEnd_rangeCond_mono sz le_rfl ht hrange0
  exact QtNZLiftGen_lift (mkM sz z) (law sz) (hL sz κ ε 𝔠 𝔡 z hκ hflow) (hm sz κ ε 𝔠 𝔡 z hκ hflow) hspec hcH
    (hFMall sz 𝔠 z hflow) hA.2.2.1 hs hst ht1 (QtLiftGen_htN sz hτ0.le hrange)
    (fun k hk => hKLip hd sz κ ε 𝔠 𝔡 z hκ hε hflow t ht k hk) hPT'

end Lift

/-! ## 6. The band re-derivations (every `d ≥ 3`)

The band family `(seqP, STFlow, bandStep2Mat · (STflowE ·), lemT)`, `Hf = seqHflow`, `E = STflowE`, `lam' = sz.lam`, `Ψ = 0`, `gK = sz.lam`, `Aof = 1`: rows 1-6 are the band discharges of
`gridGoodNgL_of` and `nqLinGoodgL_of` (as in `stOeqNQPTgL''_band`); row 3 is `DecayGen_bandSpec` (`κm = √κ/2`) and `‖mE‖ = 1`; row 4 is `rfl` and `hierDriftGen_SB_row`; row 7
`gridRepTailGen_ker_band`; row 11 the four `hierDriftGen_*_band` and the link `rfl`; row 9 `b45Gen_facts_band`; row 14 D1 `qtNZGen_kerNZ_band` with R1 `lam² ≤ 1 · lam²`; row 12
`v3_premises_of_stFlow`; row 15 `nqEndFlowGen_kLip_band`; row 16 `qtBootGen_flowModFam_band`.  No hypothesis is left open: the pins are theorems at every `d ≥ 3`. -/

section BandReDerivation

namespace QtNonzeroFlowGenCheck

open RBM.Gauss.SizesInst RBM.Gauss.InductionDefsInst RBM.Gauss.Step34Inst

/-- **The band re-derivation of `stOeqNZPT''_holds` at every `d ≥ 3`** through `stOeqNZPTgL''_of`: every row of the family-premise table is discharged at the band family; the generic
per-time pin `STOeqNZPTgL''` holds with no open hypothesis. -/
theorem stOeqNZPTgL''_band (d : ℕ) (hd : 3 ≤ d) : STOeqNZPTgL'' d (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
    (fun sz z => (bandStep2Mat sz (STflowE z)).toFlowFM) (fun _ z n => lemT (z n)) :=
  stOeqNZPTgL''_of d (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
    (fun sz z => bandStep2Mat sz (STflowE z)) (fun _ z n => lemT (z n)) (fun sz z => seqHflow sz) (fun _ z => STflowE z)
    (fun sz _ => sz.lam) (fun sz _ => sz.lam) (fun _ _ _ => 0) (fun _ => 1)
    ((bandFM_STSEforLn d).1 (stSEforLn_holds d)) (Step2EventsGen_bandFlow d)
    (fun sz κ ε 𝔠 𝔡 z hκ hz => ⟨Real.sqrt κ / 2, DecayGen_bandSpec sz hκ (QtBootGen_flow_abs_le hz)⟩)
    (fun sz κ ε 𝔠 𝔡 z hκ hz => stepDecompGen_loopForm_band sz _ fun n => (QtBootGen_flow_abs_le hz n).trans_lt (by linarith))
    (fun sz κ ε 𝔠 𝔡 z _ _ => stepDecompGen_walkForm_band sz _)
    (fun sz z => Step2EventsGen_bandLaw sz _) (fun sz z => bandStep34_LCompat sz _)
    (fun sz z => DecayGen_bandWardPair sz _)
    (fun sz κ ε 𝔠 𝔡 z hκ hz => bandFM_STKcalDecay hd sz hκ hz.1 (QtBootGen_flow_abs_le hz))
    (fun sz κ ε 𝔠 𝔡 z hκ hz s t hs hst ht1 hU k hk σ =>
      stEtermDecay hd sz hκ (QtBootGen_flow_abs_le hz) hz.1 hs hst ht1 ((bandFM_STDecayLoopU sz _ s t).2 hU) k hk σ)
    (fun sz κ ε 𝔠 𝔡 z hκ hz n => (norm_mE (by linarith [QtBootGen_flow_abs_le hz n])).le)
    (fun sz z n => rfl) (fun sz z n a => hierDriftGen_SB_row sz n a)
    (fun sz κ ε 𝔠 𝔡 z hκ hz n => gridRepTailGen_ker_band sz _ n (by linarith [QtBootGen_flow_abs_le hz n]))
    (fun sz z n w k σ a => rfl)
    (fun sz κ ε 𝔠 𝔡 z hκ hz => Eventually.of_forall fun n s' t' K' =>
      hierDriftGen_expand_band sz _ (fun n => (QtBootGen_flow_abs_le hz n).trans_lt (by linarith)) s' t' K' n)
    (fun sz κ ε 𝔠 𝔡 z hκ hz => Eventually.of_forall
      (hierDriftGen_kLoop_band sz _ (fun n => (QtBootGen_flow_abs_le hz n).trans_lt (by linarith))))
    (fun sz κ ε 𝔠 𝔡 z hκ hz => Eventually.of_forall
      (hierDriftGen_kTwo_band sz _ (fun n => (QtBootGen_flow_abs_le hz n).trans_lt (by linarith))))
    (fun sz κ ε 𝔠 𝔡 z hκ hz => Eventually.of_forall
      (hierDriftGen_uStep_band sz _ (fun n => (QtBootGen_flow_abs_le hz n).trans_lt (by linarith))))
    (b45Gen_facts_band d) (qtNZGen_kerNZ_band d)
    (fun sz κ ε 𝔠 𝔡 z hκ hz n => (one_mul _).ge)
    (fun sz κ ε 𝔠 𝔡 z hκ hε hz => ⟨ε / 2, half_pos hε, (Green.v3_premises_of_stFlow sz hκ hε hz (fun n => le_rfl)).2.2.2⟩)

/-- **The band re-derivation of `stOeqNZ''_holds` at every `d ≥ 3`** through `stOeqNZgL''_of`: the uniform pin `STOeqNZgL''` holds at the band family with no open hypothesis (rows 15, 16 are
`nqEndFlowGen_kLip_band` and `qtBootGen_flowModFam_band`, `c = 1`). -/
theorem stOeqNZgL''_band (d : ℕ) (hd : 3 ≤ d) : STOeqNZgL'' d (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
    (fun sz z => (bandStep2Mat sz (STflowE z)).toFlowFM) (fun _ z n => lemT (z n)) :=
  stOeqNZgL''_of d (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
    (fun sz z => bandStep2Mat sz (STflowE z)) (fun _ z n => lemT (z n)) (fun sz z => seqHflow sz) (fun _ z => STflowE z)
    (fun sz _ => sz.lam) (fun sz _ => sz.lam) (fun _ _ _ => 0) (fun _ => 1)
    ((bandFM_STSEforLn d).1 (stSEforLn_holds d)) (Step2EventsGen_bandFlow d)
    (fun sz κ ε 𝔠 𝔡 z hκ hz => ⟨Real.sqrt κ / 2, DecayGen_bandSpec sz hκ (QtBootGen_flow_abs_le hz)⟩)
    (fun sz κ ε 𝔠 𝔡 z hκ hz => stepDecompGen_loopForm_band sz _ fun n => (QtBootGen_flow_abs_le hz n).trans_lt (by linarith))
    (fun sz κ ε 𝔠 𝔡 z _ _ => stepDecompGen_walkForm_band sz _)
    (fun sz z => Step2EventsGen_bandLaw sz _) (fun sz z => bandStep34_LCompat sz _)
    (fun sz z => DecayGen_bandWardPair sz _)
    (fun sz κ ε 𝔠 𝔡 z hκ hz => bandFM_STKcalDecay hd sz hκ hz.1 (QtBootGen_flow_abs_le hz))
    (fun sz κ ε 𝔠 𝔡 z hκ hz s t hs hst ht1 hU k hk σ =>
      stEtermDecay hd sz hκ (QtBootGen_flow_abs_le hz) hz.1 hs hst ht1 ((bandFM_STDecayLoopU sz _ s t).2 hU) k hk σ)
    (fun sz κ ε 𝔠 𝔡 z hκ hz n => (norm_mE (by linarith [QtBootGen_flow_abs_le hz n])).le)
    (fun sz z n => rfl) (fun sz z n a => hierDriftGen_SB_row sz n a)
    (fun sz κ ε 𝔠 𝔡 z hκ hz n => gridRepTailGen_ker_band sz _ n (by linarith [QtBootGen_flow_abs_le hz n]))
    (fun sz z n w k σ a => rfl)
    (fun sz κ ε 𝔠 𝔡 z hκ hz => Eventually.of_forall fun n s' t' K' =>
      hierDriftGen_expand_band sz _ (fun n => (QtBootGen_flow_abs_le hz n).trans_lt (by linarith)) s' t' K' n)
    (fun sz κ ε 𝔠 𝔡 z hκ hz => Eventually.of_forall
      (hierDriftGen_kLoop_band sz _ (fun n => (QtBootGen_flow_abs_le hz n).trans_lt (by linarith))))
    (fun sz κ ε 𝔠 𝔡 z hκ hz => Eventually.of_forall
      (hierDriftGen_kTwo_band sz _ (fun n => (QtBootGen_flow_abs_le hz n).trans_lt (by linarith))))
    (fun sz κ ε 𝔠 𝔡 z hκ hz => Eventually.of_forall
      (hierDriftGen_uStep_band sz _ (fun n => (QtBootGen_flow_abs_le hz n).trans_lt (by linarith))))
    (b45Gen_facts_band d) (qtNZGen_kerNZ_band d)
    (fun sz κ ε 𝔠 𝔡 z hκ hz n => (one_mul _).ge)
    (fun sz κ ε 𝔠 𝔡 z hκ hε hz => ⟨ε / 2, half_pos hε, (Green.v3_premises_of_stFlow sz hκ hε hz (fun n => le_rfl)).2.2.2⟩)
    (nqEndFlowGen_kLip_band d) (qtBootGen_flowModFam_band d)

/-- `stOeqNZPTgL''_band` at `d = 3` (used by the instances of §7). -/
theorem stOeqNZPTgL''_band3 : STOeqNZPTgL'' 3 (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
    (fun sz z => (bandStep2Mat sz (STflowE z)).toFlowFM) (fun _ z n => lemT (z n)) :=
  stOeqNZPTgL''_band 3 le_rfl

/-- `stOeqNZgL''_band` at `d = 3` (used by the instances of §7). -/
theorem stOeqNZgL''_band3 : STOeqNZgL'' 3 (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
    (fun sz z => (bandStep2Mat sz (STflowE z)).toFlowFM) (fun _ z n => lemT (z n)) :=
  stOeqNZgL''_band 3 le_rfl

end QtNonzeroFlowGenCheck

/-- **Band re-derivation of `stOeqNZPT''_holds`** (`QtNonzeroFlow:837`, the same statement `∀ d, STOeqNZPT'' d`): for `3 ≤ d` the merged band pin from the generic one (`stOeqNZPTgL''_band`)
through `bandFM_STOeqNZPT''`; for `d < 3` the pin is vacuous (`STIngRgL` starts with `3 ≤ d →`). -/
theorem stOeqNZPT''_holds_of_gen (d : ℕ) : STOeqNZPT'' d := by
  by_cases hd : 3 ≤ d
  · exact (bandFM_STOeqNZPT'' d).2 (QtNonzeroFlowGenCheck.stOeqNZPTgL''_band d hd)
  · exact fun h => absurd h hd

/-- **Band re-derivation of `stOeqNZ''_holds`** (`QtNonzeroFlowLift:763`, the same statement `∀ d, STOeqNZ'' d`) through `stOeqNZgL''_band` and `bandFM_STOeqNZ''`. -/
theorem stOeqNZ''_holds_of_gen (d : ℕ) : STOeqNZ'' d := by
  by_cases hd : 3 ≤ d
  · exact (bandFM_STOeqNZ'' d).2 (QtNonzeroFlowGenCheck.stOeqNZgL''_band d hd)
  · exact fun h => absurd h hd

end BandReDerivation

/-! ## 7. Compiled nonempty instances (`d = 3`)

Data of the merged band instances (`Induction/Step34Pins.lean:717-946`, `Induction/QtNonzeroFlow.lean:872-987`): `szB` (`L = 4`, `W = n + 4`, `lam ≡ 1`, `N = (4(n+4))^3`), the flow `zB`
(`z_n = 1/2 + i/64`, `flow_zB` at `(κ, ε, 𝔠, 𝔡) = (1/10, 1/10, 1/6, 1/10)`), `s ≡ 15/16`, `t ≡ 31/32` (`szB_flow_ht`; `szB_caseII`: `1 - s = 1/16 = lam²/L²`, the boundary of case (ii);
`conStInd_const`: `(con_st_ind)` for every `𝔠_d > 0`), `C_d = 1`.  `STKboundgL`, `STKwardgL` are theorems of the flow (`stKbound_of_flow`, `bandFM_STKward`); what stays a hypothesis of
an example is a stochastic premise that is another gate's pin: `STLKgL s` and `STStep2ConclgL` (premises of `STIngRgL`), and the pair hypotheses `Ξ̂ ≺ 1` of the pin. -/

section Instances

namespace QtNonzeroFlowGenCheck

open RBM.Gauss.SizesInst RBM.Gauss.InductionDefsInst RBM.Gauss.Step34Inst RBM.Ind.AzumaProxyNInst RBM.Ind.QtNonzeroEndInst

/-- **Target 11 at the data**: the generic per-time pin `STOeqNZPTgL''` (no open hypothesis, `stOeqNZPTgL''_band3`, i.e. `stOeqNZPTgL''_of` with every row discharged) evaluated at
`(szB, zB)`, window `[15/16, 31/32]`, `C_d = 1`: the constant `𝔠_d ∈ (0, 1/100]` and, given the stochastic pins `STLKgL s`, `STStep2ConclgL`, the per-time conclusion `STNZConclPTgL''` of the
band carrier (`STKboundgL`, `STKwardgL`, the flow, the regime `STCaseII` and `(con_st_ind)` are discharged). -/
theorem inst_OeqNZPTgL'' (hLK : STLKgL (bandFM szB (STflowE zB)) (Sizes.seqP szB) (fun _ => 15 / 16))
    (hStep2 : STStep2ConclgL (bandFM szB (STflowE zB)) (Sizes.seqP szB) (fun _ => 15 / 16) (fun _ => 31 / 32) 1) :
    ∃ 𝔠d : ℝ, 0 < 𝔠d ∧ 𝔠d ≤ 1 / 100 ∧
      STNZConclPTgL'' (bandFM szB (STflowE zB)) (Sizes.seqP szB) (fun _ => 15 / 16) (fun _ => 31 / 32) := by
  obtain ⟨𝔠d, h0, h1, hC⟩ := stOeqNZPTgL''_band3 (by norm_num) (1 / 10) (1 / 10) (1 / 10) (by norm_num) (by norm_num)
    (by norm_num) 1 one_pos
  exact ⟨𝔠d, h0, h1, hC (1 / 6) szB zB flow_zB (fun _ => 15 / 16) (fun _ => 31 / 32) (fun _ => by norm_num) (fun _ => by norm_num)
    (szB_flow_ht (by norm_num)) szB_caseII (stKbound_of_flow szB (by norm_num) (by norm_num) flow_zB)
    ((bandFM_STKward szB (STflowE zB)).1 (stKward_of_flow szB (by norm_num) (by norm_num) flow_zB)) hLK
    (conStInd_const szB szB_W_tendsto (by norm_num) (by norm_num) h0) hStep2⟩

/-- **Target 12 at the data**: the uniform pin `STOeqNZgL''` (`stOeqNZgL''_band3`) at the same data; the conclusion is the uniform-in-the-time `STNZConclgL''`. -/
theorem inst_OeqNZgL'' (hLK : STLKgL (bandFM szB (STflowE zB)) (Sizes.seqP szB) (fun _ => 15 / 16))
    (hStep2 : STStep2ConclgL (bandFM szB (STflowE zB)) (Sizes.seqP szB) (fun _ => 15 / 16) (fun _ => 31 / 32) 1) :
    ∃ 𝔠d : ℝ, 0 < 𝔠d ∧ 𝔠d ≤ 1 / 100 ∧
      STNZConclgL'' (bandFM szB (STflowE zB)) (Sizes.seqP szB) (fun _ => 15 / 16) (fun _ => 31 / 32) := by
  obtain ⟨𝔠d, h0, h1, hC⟩ := stOeqNZgL''_band3 (by norm_num) (1 / 10) (1 / 10) (1 / 10) (by norm_num) (by norm_num)
    (by norm_num) 1 one_pos
  exact ⟨𝔠d, h0, h1, hC (1 / 6) szB zB flow_zB (fun _ => 15 / 16) (fun _ => 31 / 32) (fun _ => by norm_num) (fun _ => by norm_num)
    (szB_flow_ht (by norm_num)) szB_caseII (stKbound_of_flow szB (by norm_num) (by norm_num) flow_zB)
    ((bandFM_STKward szB (STflowE zB)).1 (stKward_of_flow szB (by norm_num) (by norm_num) flow_zB)) hLK
    (conStInd_const szB szB_W_tendsto (by norm_num) (by norm_num) h0) hStep2⟩

/-- **Targets 11, 12, band corollaries at the data**: the merged pins `STOeqNZPT'' 3`, `STOeqNZ'' 3` (`stOeqNZPT''_holds_of_gen`, `stOeqNZ''_holds_of_gen`) evaluated at `(szB, zB)` by the merged
`inst_ing`. -/
example : InstIngConcl (fun sz E s t => STNZConclPT'' sz E s t) szB zB (fun _ => 15 / 16) (fun _ => 31 / 32) 1 :=
  inst_ing STCaseII (fun sz E s t => STNZConclPT'' sz E s t) (stOeqNZPT''_holds_of_gen 3) szB zB flow_zB (fun _ => 15 / 16)
    (fun _ => 31 / 32) (fun _ => by norm_num) (fun _ => by norm_num) (szB_flow_ht (by norm_num)) szB_caseII
    (fun _ h𝔠 => conStInd_const szB szB_W_tendsto (by norm_num) (by norm_num) h𝔠) 1 one_pos

example : InstIngConcl (fun sz E s t => STNZConcl'' sz E s t) szB zB (fun _ => 15 / 16) (fun _ => 31 / 32) 1 :=
  inst_ing STCaseII (fun sz E s t => STNZConcl'' sz E s t) (stOeqNZ''_holds_of_gen 3) szB zB flow_zB (fun _ => 15 / 16)
    (fun _ => 31 / 32) (fun _ => by norm_num) (fun _ => by norm_num) (szB_flow_ht (by norm_num)) szB_caseII
    (fun _ h𝔠 => conStInd_const szB szB_W_tendsto (by norm_num) (by norm_num) h𝔠) 1 one_pos

/-- **The projected initial event at the data** (`QtNZFlowGen_initQ`, `k = 3`, exponent `ε = 1/160`, `D = 3`): over all `σ`, `A`, `a` the event has probability at most `N^{-3}`
eventually; `STLKgL s` is the hypothesis, `SizeTendsto` is discharged (`szB_tendsto`). -/
example (hLK : STLKgL (bandFM szB (STflowE zB)) (Sizes.seqP szB) (fun _ => 15 / 16)) :
    ∀ᶠ n in atTop, Sizes.seqP szB {ω | ∃ (σ : Fin 3 → Bool) (A : Finset (Fin 3)) (a : Fin 3 → Zd 3 (szB.L n)),
        ((szB.size n : ℕ) : ℝ) ^ (1 / 160 : ℝ) * (szB.Bctl n (15 / 16)) ^ 3 <
          ‖zeroModeSet 3 (szB.L n) A (fun b => (bandFM szB (STflowE zB)).L n (15 / 16) σ b ω -
            (bandFM szB (STflowE zB)).K n (15 / 16) σ b) a‖} ≤
      ENNReal.ofReal (((szB.size n : ℕ) : ℝ) ^ (-(3 : ℝ))) :=
  QtNZFlowGen_initQ (bandFM szB (STflowE zB)) (Sizes.seqP szB) szB_tendsto hLK (k := 3) (by norm_num) (ε := 1 / 160) (by norm_num)
    (D := 3) (by norm_num)

/-- **The initial event at one size index**: the eventual statement is unfolded at a size index (`Filter.Eventually.exists`), so it is not vacuous in `n`. -/
example (hLK : STLKgL (bandFM szB (STflowE zB)) (Sizes.seqP szB) (fun _ => 15 / 16)) :
    ∃ n : ℕ, Sizes.seqP szB {ω | ∃ (σ : Fin 3 → Bool) (A : Finset (Fin 3)) (a : Fin 3 → Zd 3 (szB.L n)),
        ((szB.size n : ℕ) : ℝ) ^ (1 / 160 : ℝ) * (szB.Bctl n (15 / 16)) ^ 3 <
          ‖zeroModeSet 3 (szB.L n) A (fun b => (bandFM szB (STflowE zB)).L n (15 / 16) σ b ω -
            (bandFM szB (STflowE zB)).K n (15 / 16) σ b) a‖} ≤
      ENNReal.ofReal (((szB.size n : ℕ) : ℝ) ^ (-(3 : ℝ))) :=
  (QtNZFlowGen_initQ (bandFM szB (STflowE zB)) (Sizes.seqP szB) szB_tendsto hLK (k := 3) (by norm_num) (ε := 1 / 160) (by norm_num)
    (D := 3) (by norm_num)).exists

/-- **The collapsed section at the data** (`u_n = s_n ≡ 15/16`, `QtNZFlowGen_collapsed`): `STLKgL s` and `(normQA2)` give `(Q^{(A)}(𝓛-𝒦)^{(3)})_{s,σ,a}/B_s³ ≺ 1` for `σ = sig3`,
`A = I_diff(σ) = {0, 1}`, `a ≡ 0`; `B_s > 0` is discharged (`st_Bctl_pos`, `s = 15/16 < 1`). -/
example (hLK : STLKgL (bandFM szB (STflowE zB)) (Sizes.seqP szB) (fun _ => 15 / 16)) :
    StochDomAt (Sizes.seqP szB) szB.size
      (fun n (_ : Unit) ω => ‖zeroModeSet 3 (szB.L n) ({0, 1} : Finset (Fin 3))
          (fun b => (bandFM szB (STflowE zB)).L n (15 / 16) sig3 b ω - (bandFM szB (STflowE zB)).K n (15 / 16) sig3 b)
          (fun _ => 0)‖ / (szB.Bctl n (15 / 16)) ^ 3)
      (fun n (_ : Unit) _ => (1 : ℝ)) :=
  QtNZFlowGen_collapsed (bandFM szB (STflowE zB)) (Sizes.seqP szB) szB_tendsto hLK (k := 3) (by norm_num)
    (fun n => st_Bctl_pos szB (by norm_num)) (ζ := fun _ => 1) (fun _ => le_rfl) (fun _ => sig3) (fun _ => {0, 1}) (fun _ _ => 0)

/-- **Measurability at the data**: the projected matrix functional of `QtNZFlowGen_meas_proj` at the band carrier of `szB`, size index `0`, `σ = sig3`, `A = I_diff(σ) = {0, 1}`; the
loop form is the band lemma `stepDecompGen_loopForm_band` at `E = Einst`. -/
example (a : Fin 3 → Zd 3 (szB.L 0)) :
    Measurable fun H : Matrix (Idx 3 (szB.L 0) (szB.W 0)) (Idx 3 (szB.L 0) (szB.W 0)) ℂ =>
      ‖zeroModeSet 3 (szB.L 0) ({0, 1} : Finset (Fin 3)) (fun b => STLKMg (bandStep2Mat szB Einst) 0 (15 / 16) H sig3 b) a‖ :=
  QtNZFlowGen_meas_proj (bandStep2Mat szB Einst) (stepDecompGen_loopForm_band szB Einst Einst_abs_lt) 0 (15 / 16) sig3 {0, 1} a

/-- **The index set of the pins is nonempty and has the intended members**: `σ = sig3 = (+,-,+)` with `A = {0, 1}` (`I_diff(sig3) = {0, 1}`, `σ3_idiff`), the constant `σ ≡ +` with `A = ∅`
(`I_diff = ∅`), and any `A` containing `I_diff(σ)`; the parameter type of `STNZConclPTgL''` at `szB` is nonempty at every size index. -/
example (n : ℕ) : Nonempty (TimeIcc (fun _ : ℕ => (15 / 16 : ℝ)) (fun _ : ℕ => (31 / 32 : ℝ)) n ×
    {σA : (Fin 3 → Bool) × Finset (Fin 3) // STIdiff σA.1 ⊆ σA.2} × (Fin 3 → Zd 3 (szB.L n))) :=
  ⟨(⟨15 / 16, le_rfl, by norm_num⟩, ⟨(sig3, {0, 1}), by rw [σ3_idiff]⟩, fun _ => 0)⟩

example : ∃ x : {σA : (Fin 3 → Bool) × Finset (Fin 3) // STIdiff σA.1 ⊆ σA.2}, x.1 = ((fun _ => true), (∅ : Finset (Fin 3))) :=
  ⟨⟨((fun _ => true), ∅), by decide⟩, rfl⟩

/-- **The mesh arithmetic of the lift at numbers** (`QtNZLiftGen_arith` at `N = 4096 = N_0` of `szB`, `n_ = 3`, `c = 1`, `δ = N^{-(6 n_ + 18 + 2c)} = N^{-38}`): the hypothesis
`2^{n_}(3 n_ + 1) = 80 ≤ N` and the conclusion `2^{n_} N^{n_}(…) ≤ 1`. -/
example : (2 : ℝ) ^ 3 * ((4096 : ℝ) ^ 3 * (3 * ((3 : ℕ) : ℝ) * (4096 : ℝ) ^ (2 * 3 + 6) * (4096 : ℝ) ^ (1 : ℝ) *
    Real.sqrt ((4096 : ℝ) ^ (-(((6 * 3 + 18 : ℕ) : ℝ) + 2 * 1))) + (4096 : ℝ) ^ (2 * 3 + 2) * (4096 : ℝ) ^ (-(((6 * 3 + 18 : ℕ) : ℝ) + 2 * 1)))) ≤ 1 :=
  QtNZLiftGen_arith (n_ := 3) (c := 1) (by norm_num) zero_le_one (by positivity) le_rfl

/-- **Targets 10, band bridges at `d = 3`** (`bandFM_STIngR`): the band pins are the generic ones; the two bridged pins that are theorems here. -/
example : STOeqNZPT'' 3 ↔ STOeqNZPTgL'' 3 (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
    (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n)) := bandFM_STOeqNZPT'' 3

example : STOeqNZ'' 3 ↔ STOeqNZgL'' 3 (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
    (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n)) := bandFM_STOeqNZ'' 3

end QtNonzeroFlowGenCheck

end Instances

end RBM.BA

end
