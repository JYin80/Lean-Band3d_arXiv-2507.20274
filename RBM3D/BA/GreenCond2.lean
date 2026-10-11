/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.BA.GreenCond

/-!
# The block Anderson family moment bound (R6), `BAFamGain` and `BAFAav` (BA-G5b, file 2 of 2)

Ticket T2411.  Paper: `paper/tex/7_8_light_weight.tex` (`lem_GbEXP_BA`, `7_8:1916-1948`), band `paper/tex/3_5_Loop_Hierarchy.tex`.

* §1 **R6**: the graded iteration and the moment bound for the family average `Σ_k T_k Q_k Y_k` over the rows `k ∈ A` of one block
  (the twin of `Green/FlucIterGain.lean:566-895`, with `GreenMinor_famGain`, whose words have rows in `A`, as the interface;
  `FlucGainUpTo'` is not a special case, T2401b).
-/

set_option linter.style.longLine false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.setOption false
set_option linter.flexible false

noncomputable section
open Filter Matrix Finset MeasureTheory
open scoped Kronecker ENNReal
open RBM RBM.Green RBM.Gauss

namespace RBM.BA

/-! ## 1. R6: the graded iteration and the family moment bound -/

section R6
variable {d : ℕ} {sz : Sizes d} {n : ℕ}

section Graded
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The iteration, with the gain assumed only for words whose rows are rows of the slots** (the twin of
`norm_integral_prod_applyOps_le_graded`, `Green/FlucIterGain.lean:566`, whose `hgain` is asked for *all* admissible words): the base case
of the induction applies `hgain` to words with `OpsOkOut`, whose rows are all of the form `k j`. -/
theorem GreenCond2_graded {k : ι → Idx d (sz.L n) (sz.W n)} {X : ι → sz.SeqΩ → ℂ} (hX : ∀ i, BddMeas sz (X i))
    (hXd : ∀ i, FinDep sz (X i)) {B ρ : ℝ} (hB : 0 ≤ B) (hρ : 0 ≤ ρ)
    (hgain : ∀ L : ι → List (Bool × Idx d (sz.L n) (sz.W n)), (∀ i, OpsOk k i (L i)) →
      (∀ i, ∀ x ∈ L i, ∃ j, x.2 = k j) → (∀ i, (L i).length ≤ Fintype.card ι) →
      ∫ ω, ∏ i, ‖applyOps sz n (L i) (qRow sz n (k i) (X i)) ω‖ ∂(Sizes.seqP sz)
        ≤ B ^ Fintype.card ι * ρ ^ ∑ i, numQ (L i)) :
    ∀ (r : ℕ) (R : Finset ι) (L : ι → List (Bool × Idx d (sz.L n) (sz.W n))), R.card = r →
      (∀ i₀ ∈ R, ∀ j, j ≠ i₀ → k j ≠ k i₀) →
      (∀ i, OpsOkOut k i R (L i)) →
      ‖∫ ω, ∏ i, applyOps sz n (L i) (qRow sz n (k i) (X i)) ω ∂(Sizes.seqP sz)‖
        ≤ (2 * max 1 ρ) ^ ((Fintype.card ι - 1) * r) * ρ ^ r
          * (B ^ Fintype.card ι * ρ ^ ∑ i, numQ (L i)) := by
  classical
  intro r
  induction r with
  | zero =>
      intro R L _ _ hL
      simp only [Nat.mul_zero, pow_zero, one_mul]
      refine le_trans (norm_integral_le_integral_norm _) ?_
      refine le_trans (le_of_eq ?_)
        (hgain L (fun i => (hL i).opsOk)
          (fun i x hx => let ⟨⟨j, _, hj⟩, _⟩ := (hL i).2 x hx; ⟨j, hj⟩)
          (fun i => le_trans (Nat.le_add_right _ _) (hL i).length_le))
      exact integral_congr_ae (Filter.Eventually.of_forall fun ω => norm_prod _ _)
  | succ r ih =>
      intro R L hR hlone hL
      obtain ⟨i₀, hi₀⟩ : R.Nonempty := Finset.card_pos.1 (by omega)
      have hFb : ∀ i, BddMeas sz (applyOps sz n (L i) (qRow sz n (k i) (X i))) :=
        fun i => ((hX i).qRow (k i)).applyOps (L i)
      have hFd : ∀ i, FinDep sz (applyOps sz n (L i) (qRow sz n (k i) (X i))) :=
        fun i => finDep_applyOps (L i) (finDep_qRow (k i) (hXd i))
      have h0 : condRow sz n (k i₀) (applyOps sz n (L i₀) (qRow sz n (k i₀) (X i₀))) = 0 :=
        condRow_applyOps_qRow sz n (k i₀) (L i₀) (hX i₀)
      have htcard : (Finset.univ.erase i₀).card = Fintype.card ι - 1 := by
        rw [Finset.card_erase_of_mem (Finset.mem_univ i₀), Finset.card_univ]
      have hM1 : (1 : ℝ) ≤ max 1 ρ := le_max_left _ _
      have hM0 : (0 : ℝ) ≤ max 1 ρ := le_trans zero_le_one hM1
      have hA0 : (0 : ℝ) ≤ (2 * max 1 ρ) ^ ((Fintype.card ι - 1) * r) * ρ ^ r
          * B ^ Fintype.card ι := by positivity
      have hexp : ∫ ω, ∏ i, applyOps sz n (L i) (qRow sz n (k i) (X i)) ω ∂(Sizes.seqP sz)
          = ∑ S ∈ (Finset.univ.erase i₀).powerset,
              ∫ ω, ∏ i, pivotFam sz n (k i₀) i₀ S
                (fun j => applyOps sz n (L j) (qRow sz n (k j) (X j))) i ω ∂(Sizes.seqP sz) := by
        rw [← integral_finsetSum _ fun S _ =>
          (bddMeas_prod _ fun i _ => bddMeas_pivotFam sz n (k i₀) i₀ S hFb i).integrable]
        exact integral_congr_ae (Filter.Eventually.of_forall fun ω =>
          prod_eq_sum_pivotFam sz n (k i₀) i₀
            (fun j => applyOps sz n (L j) (qRow sz n (k j) (X j))) ω)
      have hterm : ∀ S ∈ (Finset.univ.erase i₀).powerset,
          ‖∫ ω, ∏ i, pivotFam sz n (k i₀) i₀ S
              (fun j => applyOps sz n (L j) (qRow sz n (k j) (X j))) i ω ∂(Sizes.seqP sz)‖
            ≤ ((2 * max 1 ρ) ^ ((Fintype.card ι - 1) * r) * ρ ^ r * B ^ Fintype.card ι)
                * ρ ^ (∑ i, numQ (L i)) * (ρ * max 1 ρ ^ (Fintype.card ι - 1)) := by
        intro S hSmem
        have hSt : S ⊆ Finset.univ.erase i₀ := Finset.mem_powerset.1 hSmem
        by_cases hSe : S = ∅
        · subst hSe
          rw [integral_prod_pivotFam_empty sz n hFb hFd h0, norm_zero]
          positivity
        · have hc1 : 1 ≤ S.card := Finset.card_pos.2 (Finset.nonempty_of_ne_empty hSe)
          have hc2 : S.card ≤ Fintype.card ι - 1 := htcard ▸ Finset.card_le_card hSt
          have hrw : ∀ ω : sz.SeqΩ, ∏ i, pivotFam sz n (k i₀) i₀ S
              (fun j => applyOps sz n (L j) (qRow sz n (k j) (X j))) i ω
              = ∏ i, applyOps sz n (pivotWords k i₀ S L i) (qRow sz n (k i) (X i)) ω :=
            fun ω => Finset.prod_congr rfl fun i _ => by
              rw [pivotFam_eq_applyOps sz n (X := X) L i]
          have hL' : ∀ i, OpsOkOut k i (R.erase i₀) (pivotWords k i₀ S L i) := by
            intro i
            by_cases h : i = i₀
            · have hw : pivotWords k i₀ S L i = L i₀ := by simp [pivotWords, h]
              rw [hw, h]
              exact (hL i₀).mono (Finset.erase_subset _ _)
            · by_cases hi : i ∈ S
              · have hw : pivotWords k i₀ S L i = (true, k i₀) :: L i := by
                  simp [pivotWords, h, hi]
                rw [hw]; exact (hL i).cons (hlone i₀ hi₀) hi₀ h true
              · have hw : pivotWords k i₀ S L i = (false, k i₀) :: L i := by
                  simp [pivotWords, h, hi]
                rw [hw]; exact (hL i).cons (hlone i₀ hi₀) hi₀ h false
          have hstep := ih (R.erase i₀) (pivotWords k i₀ S L)
            (by rw [Finset.card_erase_of_mem hi₀, hR]; omega)
            (fun i₁ hi₁ => hlone i₁ (Finset.mem_of_mem_erase hi₁)) hL'
          rw [sum_numQ_pivotWords hSt L] at hstep
          rw [integral_congr_ae (Filter.Eventually.of_forall hrw)]
          refine le_trans hstep ?_
          have hpow : ρ ^ S.card ≤ ρ * max 1 ρ ^ (Fintype.card ι - 1) := by
            obtain ⟨c, hc⟩ : ∃ c, S.card = c + 1 := ⟨S.card - 1, by omega⟩
            rw [hc, pow_succ]
            have h1 : ρ ^ c ≤ max 1 ρ ^ c := pow_le_pow_left₀ hρ (le_max_right 1 ρ) c
            have h2 : max 1 ρ ^ c ≤ max 1 ρ ^ (Fintype.card ι - 1) :=
              pow_le_pow_right₀ hM1 (by omega)
            calc ρ ^ c * ρ ≤ max 1 ρ ^ (Fintype.card ι - 1) * ρ := by
                  exact mul_le_mul_of_nonneg_right (le_trans h1 h2) hρ
              _ = ρ * max 1 ρ ^ (Fintype.card ι - 1) := by ring
          have hexpand : (2 * max 1 ρ) ^ ((Fintype.card ι - 1) * r) * ρ ^ r
              * (B ^ Fintype.card ι * ρ ^ ((∑ i, numQ (L i)) + S.card))
              = ((2 * max 1 ρ) ^ ((Fintype.card ι - 1) * r) * ρ ^ r * B ^ Fintype.card ι)
                * ρ ^ (∑ i, numQ (L i)) * ρ ^ S.card := by
            rw [pow_add]; ring
          rw [hexpand]
          exact mul_le_mul_of_nonneg_left hpow (by positivity)
      calc ‖∫ ω, ∏ i, applyOps sz n (L i) (qRow sz n (k i) (X i)) ω ∂(Sizes.seqP sz)‖
          = ‖∑ S ∈ (Finset.univ.erase i₀).powerset,
              ∫ ω, ∏ i, pivotFam sz n (k i₀) i₀ S
                (fun j => applyOps sz n (L j) (qRow sz n (k j) (X j))) i ω ∂(Sizes.seqP sz)‖ := by
            rw [hexp]
        _ ≤ ∑ S ∈ (Finset.univ.erase i₀).powerset,
              ‖∫ ω, ∏ i, pivotFam sz n (k i₀) i₀ S
                (fun j => applyOps sz n (L j) (qRow sz n (k j) (X j))) i ω ∂(Sizes.seqP sz)‖ :=
            norm_sum_le _ _
        _ ≤ ∑ _S ∈ (Finset.univ.erase i₀).powerset,
              (((2 * max 1 ρ) ^ ((Fintype.card ι - 1) * r) * ρ ^ r * B ^ Fintype.card ι)
                * ρ ^ (∑ i, numQ (L i)) * (ρ * max 1 ρ ^ (Fintype.card ι - 1))) :=
            Finset.sum_le_sum hterm
        _ = (2 : ℝ) ^ (Fintype.card ι - 1)
              * (((2 * max 1 ρ) ^ ((Fintype.card ι - 1) * r) * ρ ^ r * B ^ Fintype.card ι)
                * ρ ^ (∑ i, numQ (L i)) * (ρ * max 1 ρ ^ (Fintype.card ι - 1))) := by
            rw [Finset.sum_const, Finset.card_powerset, htcard, nsmul_eq_mul]
            norm_num
        _ = (2 * max 1 ρ) ^ ((Fintype.card ι - 1) * (r + 1)) * ρ ^ (r + 1)
              * (B ^ Fintype.card ι * ρ ^ ∑ i, numQ (L i)) := by
            rw [Nat.mul_succ, pow_add, mul_pow, pow_succ]
            ring

/-- The iteration from empty words (`GreenCond2_graded` with every word empty and `r = #R`). -/
theorem GreenCond2_qRow_graded {k : ι → Idx d (sz.L n) (sz.W n)} (R : Finset ι)
    (hlone : ∀ i₀ ∈ R, ∀ j, j ≠ i₀ → k j ≠ k i₀) {X : ι → sz.SeqΩ → ℂ} (hX : ∀ i, BddMeas sz (X i))
    (hXd : ∀ i, FinDep sz (X i)) {B ρ : ℝ} (hB : 0 ≤ B) (hρ : 0 ≤ ρ)
    (hgain : ∀ L : ι → List (Bool × Idx d (sz.L n) (sz.W n)), (∀ i, OpsOk k i (L i)) →
      (∀ i, ∀ x ∈ L i, ∃ j, x.2 = k j) → (∀ i, (L i).length ≤ Fintype.card ι) →
      ∫ ω, ∏ i, ‖applyOps sz n (L i) (qRow sz n (k i) (X i)) ω‖ ∂(Sizes.seqP sz)
        ≤ B ^ Fintype.card ι * ρ ^ ∑ i, numQ (L i)) :
    ‖∫ ω, ∏ i, qRow sz n (k i) (X i) ω ∂(Sizes.seqP sz)‖
      ≤ (2 * max 1 ρ) ^ ((Fintype.card ι - 1) * R.card) * ρ ^ R.card * B ^ Fintype.card ι := by
  classical
  have h := GreenCond2_graded hX hXd hB hρ hgain R.card R (fun _ => []) rfl hlone (fun i => opsOkOut_nil k i R)
  simpa only [applyOps_nil, numQ_nil, Finset.sum_const, smul_eq_mul, mul_zero, pow_zero, mul_one] using h

end Graded

section Budget
variable {p : ℕ}

/-- **The iteration at order `2p`, for a family**: for slots `v : (Fin p ⊕ Fin p) → Idx` with every row in `A` and a set `R` of lone slots,
`‖∫ ∏_i ε_i Z_{v i}‖ ≤ (2 max(1,ρ))^{(2p-1) #R} ρ^{#R} B^{2p}`, `Z_k = Q_k Y_k`, `ε_i` the identity (`i = inl _`) or the conjugation
(`i = inr _`), under the family gain interface (words whose rows are in `A`). -/
theorem GreenCond2_epsHom_budget {A : Finset (Idx d (sz.L n) (sz.W n))} {Y : Idx d (sz.L n) (sz.W n) → sz.SeqΩ → ℂ}
    (hY : ∀ k, BddMeas sz (Y k)) (hYd : ∀ k, FinDep sz (Y k)) {B ρ : ℝ} {M K : ℕ} (hg : GreenMinor_famGain sz n A Y B ρ M K)
    (hM : 2 * p ≤ M) (hK : 2 * p ≤ K) (v : (Fin p ⊕ Fin p) → Idx d (sz.L n) (sz.W n)) (hvA : ∀ i, v i ∈ A)
    (R : Finset (Fin p ⊕ Fin p)) (hlone : ∀ i₀ ∈ R, ∀ j, j ≠ i₀ → v j ≠ v i₀) :
    ‖∫ ω, ∏ i, epsHom p i (qRow sz n (v i) (Y (v i)) ω) ∂(Sizes.seqP sz)‖
      ≤ (2 * max 1 ρ) ^ ((2 * p - 1) * R.card) * ρ ^ R.card * B ^ (2 * p) := by
  classical
  have hcard : Fintype.card (Fin p ⊕ Fin p) = 2 * p := by simp [Fintype.card_sum, two_mul]
  set X : (Fin p ⊕ Fin p) → sz.SeqΩ → ℂ := fun i ω => epsHom p i (Y (v i) ω) with hXdef
  have hXb : ∀ i, BddMeas sz (X i) := by
    intro i
    obtain ⟨C, hC⟩ := (hY (v i)).bdd
    exact ⟨(measurable_epsHom p i).comp (hY (v i)).meas, C, fun ω => by rw [hXdef]; simpa only [norm_epsHom] using hC ω⟩
  have hXd : ∀ i, FinDep sz (X i) :=
    fun i => (hYd (v i)).imp (fun _ h ω ω' hω => by rw [hXdef]; exact congrArg (epsHom p i) (h ω ω' hω))
  have hq : ∀ i, qRow sz n (v i) (X i) = fun ω => epsHom p i (qRow sz n (v i) (Y (v i)) ω) := by
    intro i
    cases i with
    | inl j => simp only [hXdef, epsHom_inl]
    | inr j =>
        simp only [hXdef, epsHom_inr]
        exact qRow_conj sz n (v (Sum.inr j)) (Y _)
  have hgain : ∀ L : (Fin p ⊕ Fin p) → List (Bool × Idx d (sz.L n) (sz.W n)), (∀ i, OpsOk v i (L i)) →
      (∀ i, ∀ x ∈ L i, ∃ j, x.2 = v j) → (∀ i, (L i).length ≤ Fintype.card (Fin p ⊕ Fin p)) →
      ∫ ω, ∏ i, ‖applyOps sz n (L i) (qRow sz n (v i) (X i)) ω‖ ∂(Sizes.seqP sz)
        ≤ B ^ Fintype.card (Fin p ⊕ Fin p) * ρ ^ ∑ i, numQ (L i) := by
    intro L hL hLj hlen
    have hrw : ∀ ω : sz.SeqΩ, ∏ i, ‖applyOps sz n (L i) (qRow sz n (v i) (X i)) ω‖
        = ∏ i, ‖applyOps sz n (L i) (qRow sz n (v i) (Y (v i))) ω‖ := by
      intro ω
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [hq i, applyOps_epsHom sz n p i (L i) (qRow sz n (v i) (Y (v i))), norm_epsHom]
    rw [integral_congr_ae (Filter.Eventually.of_forall hrw)]
    exact hg.2.2 (Fin p ⊕ Fin p) v L hvA (fun i => (hL i).1)
      (fun i x hx => ⟨(hL i).2 x hx, by obtain ⟨j, hj⟩ := hLj i x hx; rw [hj]; exact hvA j⟩)
      (fun i => le_trans (hlen i) (by rw [hcard]; exact hM)) (by rw [hcard]; exact hK)
  have h := GreenCond2_qRow_graded (k := v) R hlone hXb hXd hg.1 hg.2.1 hgain
  rw [hcard] at h
  simpa only [hq] using h

/-- **The moment bound for the family average** (the twin of `integral_norm_flucAvg_pow_le_iter_budget`, `Green/FlucIterGain.lean:823`): for a
bounded weight `T` (`0 ≤ T ≤ c ≤ ρ²` on `A` with `2p ≤ #A`, `Σ T ≤ 1`), `ρ ≤ 1`, and the family gain interface `famGain(B, ρ, M, K)` of
`Y` on `A` (`M, K ≥ 2p`),
`E|Σ_k T_k Q_k Y_k|^{2p} ≤ (2p+1)(2p)^{2p} (2^{2p-1} ρ B)^{2p}`. -/
theorem GreenCond2_famAvg_moment {A : Finset (Idx d (sz.L n) (sz.W n))} {Y : Idx d (sz.L n) (sz.W n) → sz.SeqΩ → ℂ}
    (hY : ∀ k, BddMeas sz (Y k)) (hYd : ∀ k, FinDep sz (Y k)) {B ρ c : ℝ} {M K : ℕ}
    {T : Idx d (sz.L n) (sz.W n) → ℝ} (hg : GreenMinor_famGain sz n A Y B ρ M K) (hM : 2 * p ≤ M) (hK : 2 * p ≤ K)
    (hρ1 : ρ ≤ 1) (hcρ : c ≤ ρ ^ 2) (hw : BoundedWeight T c A) (hp : 2 * p ≤ A.card) :
    ∫ ω, ‖∑ k, (T k : ℂ) * qRow sz n k (Y k) ω‖ ^ (2 * p) ∂(Sizes.seqP sz)
      ≤ ((2 * p : ℝ) + 1) * (2 * p : ℝ) ^ (2 * p) * ((2 : ℝ) ^ (2 * p - 1) * ρ * B) ^ (2 * p) := by
  classical
  have hcardι : Fintype.card (Fin p ⊕ Fin p) = 2 * p := by simp [Fintype.card_sum, two_mul]
  have hB := hg.1
  have hρ0 := hg.2.1
  have hbm : ∀ (v : (Fin p ⊕ Fin p) → Idx d (sz.L n) (sz.W n)),
      BddMeas sz fun ω => ∏ i, epsHom p i (qRow sz n (v i) (Y (v i)) ω) := by
    intro v
    refine bddMeas_prod _ fun i _ => ?_
    obtain ⟨C, hC⟩ := ((hY (v i)).qRow (v i)).bdd
    exact ⟨(measurable_epsHom p i).comp ((hY (v i)).qRow (v i)).meas, C, fun ω => by simpa only [norm_epsHom] using hC ω⟩
  have hI : ∫ ω, ((‖∑ k, (T k : ℂ) * qRow sz n k (Y k) ω‖ ^ (2 * p) : ℝ) : ℂ) ∂(Sizes.seqP sz)
      = ∑ v : (Fin p ⊕ Fin p) → Idx d (sz.L n) (sz.W n), (∏ i, (T (v i) : ℂ))
          * ∫ ω, ∏ i, epsHom p i (qRow sz n (v i) (Y (v i)) ω) ∂(Sizes.seqP sz) := by
    have hexp : ∀ ω : sz.SeqΩ, ((‖∑ k, (T k : ℂ) * qRow sz n k (Y k) ω‖ ^ (2 * p) : ℝ) : ℂ)
        = ∑ v : (Fin p ⊕ Fin p) → Idx d (sz.L n) (sz.W n), (∏ i, (T (v i) : ℂ))
            * ∏ i, epsHom p i (qRow sz n (v i) (Y (v i)) ω) :=
      fun ω => prod_epsHom_sum_eq p T fun k => qRow sz n k (Y k) ω
    simp_rw [hexp]
    rw [integral_finsetSum _ fun v _ => ((bddMeas_const sz (∏ i, (T (v i) : ℂ))).mul (hbm v)).integrable]
    exact Finset.sum_congr rfl fun v _ => integral_const_mul _ _
  -- the expansion only sees multi-indices in `A^ι`: the other terms carry a zero weight
  set f : ((Fin p ⊕ Fin p) → Idx d (sz.L n) (sz.W n)) → ℝ := fun v =>
    if ∀ i, v i ∈ A then ‖∫ ω, ∏ i, epsHom p i (qRow sz n (v i) (Y (v i)) ω) ∂(Sizes.seqP sz)‖ else 0 with hfdef
  have hf : ∀ v : (Fin p ⊕ Fin p) → Idx d (sz.L n) (sz.W n),
      f v ≤ ((2 : ℝ) ^ (2 * p - 1)) ^ (loneSlots v).card * ρ ^ (loneSlots v).card * B ^ (2 * p) := by
    intro v
    by_cases hv : ∀ i, v i ∈ A
    · rw [hfdef]
      simp only [hv, implies_true, ↓reduceIte]
      have hlone : ∀ i₀ ∈ loneSlots v, ∀ j, j ≠ i₀ → v j ≠ v i₀ := fun i₀ hi₀ => mem_loneSlots.1 hi₀
      have key := GreenCond2_epsHom_budget hY hYd hg hM hK v hv (loneSlots v) hlone
      rwa [max_eq_left hρ1, mul_one, pow_mul] at key
    · rw [hfdef]
      simp only [hv, ↓reduceIte]
      positivity
  have hK1 : (1 : ℝ) ≤ (2 : ℝ) ^ (2 * p - 1) := one_le_pow₀ (by norm_num)
  have hsum := sum_weighted_le (ι := Fin p ⊕ Fin p) hw hcardι hp hρ0 hρ1 hK1 hB hcρ hf
  have hofR : (∫ ω, ((‖∑ k, (T k : ℂ) * qRow sz n k (Y k) ω‖ ^ (2 * p) : ℝ) : ℂ) ∂(Sizes.seqP sz))
      = ((∫ ω, ‖∑ k, (T k : ℂ) * qRow sz n k (Y k) ω‖ ^ (2 * p) ∂(Sizes.seqP sz) : ℝ) : ℂ) := integral_complex_ofReal
  have hreal : ∫ ω, ‖∑ k, (T k : ℂ) * qRow sz n k (Y k) ω‖ ^ (2 * p) ∂(Sizes.seqP sz)
      = ‖∫ ω, ((‖∑ k, (T k : ℂ) * qRow sz n k (Y k) ω‖ ^ (2 * p) : ℝ) : ℂ) ∂(Sizes.seqP sz)‖ := by
    rw [hofR, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun ω => by positivity)]
  rw [hreal, hI]
  refine le_trans (norm_sum_le _ _) ?_
  have hterm : ∀ v : (Fin p ⊕ Fin p) → Idx d (sz.L n) (sz.W n),
      ‖(∏ i, (T (v i) : ℂ)) * ∫ ω, ∏ i, epsHom p i (qRow sz n (v i) (Y (v i)) ω) ∂(Sizes.seqP sz)‖
        = (∏ i, |T (v i)|) * f v := by
    intro v
    rw [norm_mul, norm_prod]
    by_cases hv : ∀ i, v i ∈ A
    · rw [hfdef]; simp only [hv, implies_true, ↓reduceIte]
      congr 1
      exact Finset.prod_congr rfl fun i _ => by rw [Complex.norm_real, Real.norm_eq_abs]
    · push Not at hv
      obtain ⟨i, hi⟩ := hv
      have h0 : T (v i) = 0 := hw.not_mem _ hi
      have h1 : ∏ i, |T (v i)| = 0 := Finset.prod_eq_zero (Finset.mem_univ i) (by rw [h0]; simp)
      have h2 : ∏ i, ‖(T (v i) : ℂ)‖ = 0 := Finset.prod_eq_zero (Finset.mem_univ i) (by rw [h0]; simp)
      rw [h1, h2]; simp
  simp_rw [hterm]
  exact le_trans hsum (le_of_eq (by push_cast; ring))

end Budget



end R6

end RBM.BA
