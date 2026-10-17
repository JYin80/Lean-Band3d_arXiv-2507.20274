/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.BA.GreenCond

/-!
# The block Anderson family moment bound (R6), `BAFamGain` and `BAFAav`

BA-G5b, file 2 of 2.  Ticket T2411.  Paper: `paper/tex/7_8_light_weight.tex` (`lem_GbEXP_BA`,
`7_8:1916-1948`), band `paper/tex/3_5_Loop_Hierarchy.tex`.

* §1 **R6**: the graded iteration and the moment bound for the family average `Σ_k T_k Q_k Y_k`
  over the rows `k ∈ A` of one block (the twin of `Green/FlucIterGain.lean:566-895`, with
  `GreenMinor_famGain`, whose words have rows in `A`, as the interface; `FlucGainUpTo'` is not a
  special case, T2401b).
* §2-§4 the BA data (`η_t`, `‖s‖`, the local law `‖G_t - M‖_max ≺ Ψ`, `P(badBase) ≤ N^{-D}`), the
  exponent bookkeeping, `baFamGain_holds`.
* §5-§9 the decompositions (E) of `𝒜'`, `𝔛` and their remainders, the `ℓ¹` row bound of `M^{(B)}`
  for every `d ≥ 1`, Markov for the family average, the exceptional set of `BAFAav`, the numerics,
  `baFAav_holds`; §10 the nonempty instances (`d = 3`, `sz0`, `flow_sz0`; `BAGiiGEX` and
  `(initialGT2)` are hypotheses).
-/

set_option linter.style.longLine false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.setOption false
set_option linter.flexible false
set_option linter.unusedDecidableInType false

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

/-! ## 2. The BA data: `η_t`, `‖s‖`, the base event -/

section Data
variable {d : ℕ}

/-- **`η_t ≥ (κ/2) N^{-1+ε}`** along the flow: `η_t = (1 - t) Im m_F`, `Im m_F ≥ κ` and `1 - t ≥ 1 - T₀ = Im z/(Im m + Im z) ≥ Im z/2`
(`Im m ≤ ‖m‖ ≤ 1`, `Im z ≤ 1`), `Im z ≥ N^{-1+ε}` (`BAdom`). -/
theorem GreenCond2_eta_lower {κ ε 𝔠 𝔡 : ℝ} (hκ : 0 < κ) (sz : Sizes d) {z : ℕ → ℂ} (h : BAFlow sz κ ε 𝔠 𝔡 z) (n : ℕ) {t : ℝ}
    (ht0 : 0 ≤ t) (ht : t ≤ BAflowT0 sz z n) :
    κ / 2 * ((sz.size n : ℕ) : ℝ) ^ (-1 + ε) ≤ (GreenCond_zt sz z n t).im := by
  obtain ⟨hz0, hm0, -, -⟩ := BAflow_T0_bounds hκ h n
  obtain ⟨hκm, hzlo, hz1⟩ := h.2 n
  have hmself := BAm_self d (sz.L n) (sz.lam n) (z n) hz0
  have hm1 : (BAm d (sz.L n) (sz.lam n) (z n)).im ≤ 1 :=
    ((le_abs_self _).trans (Complex.abs_im_le_norm _)).trans (BAm_norm_le_one (d := d) (L := sz.L n) _ _ _ hz0.le hmself)
  have hMF : κ ≤ (GreenCond_m sz z n).im := (BAflow_real κ ε 𝔠 𝔡 sz z h n).2
  have hsum : (BAm d (sz.L n) (sz.lam n) (z n)).im + (z n).im ≤ 2 := by linarith
  have hT : BAflowT0 sz z n = (BAm d (sz.L n) (sz.lam n) (z n)).im / ((BAm d (sz.L n) (sz.lam n) (z n)).im + (z n).im) := rfl
  have h1t : (z n).im / 2 ≤ 1 - t := by
    have : 1 - BAflowT0 sz z n = (z n).im / ((BAm d (sz.L n) (sz.lam n) (z n)).im + (z n).im) := by
      rw [hT]; field_simp; ring
    have h2 : (z n).im / 2 ≤ (z n).im / ((BAm d (sz.L n) (sz.lam n) (z n)).im + (z n).im) :=
      div_le_div_of_nonneg_left hz0.le (by linarith) hsum
    linarith
  have hN : (0 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ (-1 + ε) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have e : (GreenCond_zt sz z n t).im = (1 - t) * (GreenCond_m sz z n).im := by
    unfold GreenCond_zt
    rw [ztOf_im]; rfl
  rw [e]
  calc κ / 2 * ((sz.size n : ℕ) : ℝ) ^ (-1 + ε) = κ * (((sz.size n : ℕ) : ℝ) ^ (-1 + ε) / 2) := by ring
    _ ≤ (GreenCond_m sz z n).im * (1 - t) := by
        refine mul_le_mul hMF ?_ (by positivity) (hκ.le.trans hMF)
        linarith
    _ = (1 - t) * (GreenCond_m sz z n).im := mul_comm _ _

/-- `η_t⁻¹ ≤ (2/κ) N`. -/
theorem GreenCond2_inv_eta_le {κ ε 𝔠 𝔡 : ℝ} (hκ : 0 < κ) (hε : 0 < ε) (sz : Sizes d) {z : ℕ → ℂ} (h : BAFlow sz κ ε 𝔠 𝔡 z) (n : ℕ)
    {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ BAflowT0 sz z n) :
    |(GreenCond_zt sz z n t).im|⁻¹ ≤ 2 / κ * ((sz.size n : ℕ) : ℝ) := by
  have hl := GreenCond2_eta_lower hκ sz h n ht0 ht
  have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
  have hNpos : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
  have hpow : ((sz.size n : ℕ) : ℝ) ^ (-1 + ε) = ((sz.size n : ℕ) : ℝ) ^ (-1 : ℝ) * ((sz.size n : ℕ) : ℝ) ^ ε := by
    rw [← Real.rpow_add hNpos]
  have hpos : 0 < κ / 2 * ((sz.size n : ℕ) : ℝ) ^ (-1 + ε) := by positivity
  have hη : 0 < (GreenCond_zt sz z n t).im := hpos.trans_le hl
  rw [abs_of_pos hη]
  have h1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ ε := Real.one_le_rpow hN1 hε.le
  have h2 : ((sz.size n : ℕ) : ℝ) ^ (-1 : ℝ) = (((sz.size n : ℕ) : ℝ))⁻¹ := Real.rpow_neg_one _
  have h3 : κ / 2 * (((sz.size n : ℕ) : ℝ))⁻¹ ≤ (GreenCond_zt sz z n t).im := by
    refine le_trans ?_ hl
    rw [hpow, h2]
    have : (((sz.size n : ℕ) : ℝ))⁻¹ ≤ (((sz.size n : ℕ) : ℝ))⁻¹ * ((sz.size n : ℕ) : ℝ) ^ ε :=
      le_mul_of_one_le_right (by positivity) h1
    nlinarith [hκ]
  calc ((GreenCond_zt sz z n t).im)⁻¹ ≤ (κ / 2 * (((sz.size n : ℕ) : ℝ))⁻¹)⁻¹ := inv_anti₀ (by positivity) h3
    _ = 2 / κ * ((sz.size n : ℕ) : ℝ) := by field_simp

/-- `‖s‖ ≤ (1 + 2 d g₀)/κ`: from `(D - s) M = 1` at the entry `(u, u)`, `s m = Σ_l D_{ul} M_{lu} - 1`. -/
theorem GreenCond2_norm_s_le {κ ε 𝔠 𝔡 : ℝ} (hκ : 0 < κ) (sz : Sizes d) {z : ℕ → ℂ} (h : BAFlow sz κ ε 𝔠 𝔡 z) (n : ℕ) {t : ℝ}
    (ht0 : 0 ≤ t) (ht : t ≤ BAflowT0 sz z n) (hg0 : 0 ≤ BAflowLam0 sz z n) :
    ‖GreenCond_s sz z n‖ ≤ (1 + 2 * d * BAflowLam0 sz z n) / κ := by
  have dat := GreenCond_data hκ sz h n ht0 ht hg0
  rw [le_div_iff₀ hκ]
  calc ‖GreenCond_s sz z n‖ * κ ≤ ‖GreenCond_s sz z n‖ * ‖GreenCond_m sz z n‖ :=
        mul_le_mul_of_nonneg_left dat.hκm (norm_nonneg _)
    _ ≤ 1 + 2 * d * BAflowLam0 sz z n := dat.hs

private theorem GreenCond2_prec_of_whp {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {size : ℕ → ℕ} {U : ℕ → Type*}
    {ξ ζ : ∀ l, U l → Ω → ℝ}
    (h : ∀ τ > (0 : ℝ), HighProbAt P size (fun l => {ω | ∀ u, ξ l u ω ≤ (size l : ℝ) ^ τ * ζ l u ω})) :
    StochDomAt P size ξ ζ := by
  intro τ hτ D hD
  filter_upwards [h τ hτ D hD] with l hl
  refine le_trans (le_of_eq ?_) hl
  congr 1
  ext ω
  simp [badSetAt]

private theorem GreenCond2_le_of_sq_le {a b : ℝ} (hb : 0 ≤ b) (h : a ^ 2 ≤ b ^ 2) : a ≤ b := by
  by_contra hab
  push Not at hab
  nlinarith

/-- `N^{ζ} W^{-ε₀} ≤ W^{-ε₀/2}` eventually, for `ζ = 𝔠 ε₀/2` (`W ≥ N^𝔠`). -/
private theorem GreenCond2_ev_incl (sz : Sizes d) {𝔠 𝔡 : ℝ} (hA : sz.Admissible 𝔠 𝔡) {ε₀ : ℝ} (hε₀ : 0 < ε₀) :
    ∀ᶠ n in atTop, ((sz.size n : ℕ) : ℝ) ^ (𝔠 * ε₀ / 2) * ((sz.W n : ℕ) : ℝ) ^ (-ε₀) ≤ ((sz.W n : ℕ) : ℝ) ^ (-(ε₀ / 2)) := by
  filter_upwards [hA.2.2.2.1] with n hn
  have hW0 : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hN0 : (0 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := Nat.cast_nonneg _
  have h1 : ((sz.size n : ℕ) : ℝ) ^ (𝔠 * ε₀ / 2) ≤ ((sz.W n : ℕ) : ℝ) ^ (ε₀ / 2) := by
    calc ((sz.size n : ℕ) : ℝ) ^ (𝔠 * ε₀ / 2) = (((sz.size n : ℕ) : ℝ) ^ 𝔠) ^ (ε₀ / 2) := by
          rw [← Real.rpow_mul hN0]; congr 1; ring
      _ ≤ ((sz.W n : ℕ) : ℝ) ^ (ε₀ / 2) := Real.rpow_le_rpow (Real.rpow_nonneg hN0 _) hn (by linarith)
  calc ((sz.size n : ℕ) : ℝ) ^ (𝔠 * ε₀ / 2) * ((sz.W n : ℕ) : ℝ) ^ (-ε₀)
      ≤ ((sz.W n : ℕ) : ℝ) ^ (ε₀ / 2) * ((sz.W n : ℕ) : ℝ) ^ (-ε₀) :=
        mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hW0.le _)
    _ = ((sz.W n : ℕ) : ℝ) ^ (-(ε₀ / 2)) := by rw [← Real.rpow_add hW0]; congr 1; ring

/-- **The local law at a deterministic control, for the BA carrier** (the argument of `greenLocal_localLaw`, `BA/GreenLocal.lean`, with
`BAGiiGEX` at `ε₀/2` a hypothesis, as in the pins `BAFamGain`, `BAFAav`, and no guard on `d`): `(initialGT2)` gives `‖G_t - M‖_max ≺ Ψ`. -/
theorem GreenCond2_localLaw {κ ε 𝔡 𝔠 : ℝ} (hκ : 0 < κ) (hε : 0 < ε) (h𝔡 : 0 < 𝔡) (sz : Sizes d) {z : ℕ → ℂ}
    (hflow : BAFlow sz κ ε 𝔠 𝔡 z) {t : ℕ → ℝ} (ht0 : ∀ n, 0 ≤ t n) (htT : ∀ n, t n ≤ BAflowT0 sz z n) {ε₀ : ℝ} (hε₀ : 0 < ε₀)
    (hii : BAGiiGEX sz z t (ε₀ / 2)) {Ψ : ℕ → ℝ} (hΨ : ∀ᶠ n in atTop, 0 ≤ Ψ n)
    (hinit : STInitialGT2gL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) t ε₀ Ψ) :
    PrecL sz (Sizes.seqP (sz.withLam 0)) (U := fun n => Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n))
      (fun n p ω => ‖(baFMz sz z).GM n (t n) ω p.1 p.2‖) (fun n _ _ => Ψ n) := by
  have h𝔠 : 0 < 𝔠 := hflow.1.1
  have hsz' : Tendsto sz.size atTop atTop := Sizes.tendsto_size sz hflow.1.2.2.1
  have hζ : 0 < 𝔠 * ε₀ / 2 := by positivity
  have hΩ : HighProbAt (Sizes.seqP (sz.withLam 0)) sz.size (fun n => {ω | ∀ x y : Idx d (sz.L n) (sz.W n),
      ‖(baFMz sz z).GM n (t n) ω x y‖ ≤ ((sz.size n : ℕ) : ℝ) ^ (𝔠 * ε₀ / 2) * ((sz.W n : ℕ) : ℝ) ^ (-ε₀)}) :=
    (StochDomAt.highProb hinit.1 hζ).mono (Eventually.of_forall fun n ω hω x y => hω (x, y))
  refine GreenCond2_prec_of_whp fun τ hτ => ?_
  have hB := StochDomAt.highProb hinit.2 hτ
  have hC := StochDomAt.highProb hii hτ
  refine (HighProbAt.inter hsz' hΩ (HighProbAt.inter hsz' hB hC)).mono ?_
  filter_upwards [GreenCond2_ev_incl sz hflow.1 hε₀, hΨ] with n hincl hΨn
  rintro ω ⟨h1, h2, h3⟩ ⟨x, y⟩
  have hN0 : (0 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := Nat.cast_nonneg _
  have hOm : ∀ x y : Idx d (sz.L n) (sz.W n), ‖(baFMz sz z).GM n (t n) ω x y‖ ≤ ((sz.W n : ℕ) : ℝ) ^ (-(ε₀ / 2)) :=
    fun x y => (h1 x y).trans hincl
  have hi : (baFMz sz z).indMax n (t n) (((sz.W n : ℕ) : ℝ) ^ (-(ε₀ / 2))) ω = 1 := by simp [FlowFM.indMax, hOm]
  have h3' := h3 (x, y)
  simp only [hi, one_mul] at h3'
  have h2' := h2 ()
  have hNτ0 : 0 ≤ ((sz.size n : ℕ) : ℝ) ^ τ := Real.rpow_nonneg hN0 _
  refine GreenCond2_le_of_sq_le (mul_nonneg hNτ0 hΨn) ?_
  calc ‖(baFMz sz z).GM n (t n) ω x y‖ ^ 2 ≤ ((sz.size n : ℕ) : ℝ) ^ τ * STmaxLoop2g (baFMz sz z) n (t n) ω := h3'
    _ ≤ ((sz.size n : ℕ) : ℝ) ^ τ * (((sz.size n : ℕ) : ℝ) ^ τ * Ψ n ^ 2) := mul_le_mul_of_nonneg_left h2' hNτ0
    _ = (((sz.size n : ℕ) : ℝ) ^ τ * Ψ n) ^ 2 := by ring

/-- **`P(S_n) ≤ N^{-D}`**: the hull of the complement of `{‖G_t - M‖_max ≤ W^τ Ψ_n}` is small, for every `τ, D > 0`
(from `‖G_t - M‖_max ≺ Ψ` and `N^{𝔠τ} ≤ W^τ`). -/
theorem GreenCond2_prob_badBase {κ ε 𝔡 𝔠 : ℝ} (hκ : 0 < κ) (hε : 0 < ε) (h𝔡 : 0 < 𝔡) (sz : Sizes d) {z : ℕ → ℂ}
    (hflow : BAFlow sz κ ε 𝔠 𝔡 z) {t : ℕ → ℝ} (ht0 : ∀ n, 0 ≤ t n) (htT : ∀ n, t n ≤ BAflowT0 sz z n) {ε₀ : ℝ} (hε₀ : 0 < ε₀)
    (hii : BAGiiGEX sz z t (ε₀ / 2)) {Ψ : ℕ → ℝ} (hΨ : ∀ᶠ n in atTop, 0 ≤ Ψ n)
    (hinit : STInitialGT2gL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) t ε₀ Ψ) {τ : ℝ} (hτ : 0 < τ) {D : ℝ} (hD : 0 < D) :
    ∀ᶠ n in atTop, (Sizes.seqP (sz.withLam 0)) (GreenCond_badBase sz z n (t n) (((sz.W n : ℕ) : ℝ) ^ τ * Ψ n)) ≤
      ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-D)) := by
  have hLL := GreenCond2_localLaw hκ hε h𝔡 sz hflow ht0 htT hε₀ hii hΨ hinit
  have h𝔠 : 0 < 𝔠 := hflow.1.1
  filter_upwards [hLL (𝔠 * τ) (by positivity) D hD, hflow.1.2.2.2.1, hΨ] with n hn hband hΨn
  rw [GreenCond_meas_badBase]
  refine le_trans (measure_mono ?_) hn
  intro ω hω
  simp only [not_forall, not_le] at hω
  obtain ⟨x, y, hxy⟩ := hω
  have hN0 : (0 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := Nat.cast_nonneg _
  have hNW : ((sz.size n : ℕ) : ℝ) ^ (𝔠 * τ) ≤ ((sz.W n : ℕ) : ℝ) ^ τ := by
    calc ((sz.size n : ℕ) : ℝ) ^ (𝔠 * τ) = (((sz.size n : ℕ) : ℝ) ^ 𝔠) ^ τ := by rw [← Real.rpow_mul hN0]
      _ ≤ ((sz.W n : ℕ) : ℝ) ^ τ := Real.rpow_le_rpow (Real.rpow_nonneg hN0 _) hband hτ.le
  refine ⟨((splitEquiv d (sz.L n) (sz.W n)).symm x, (splitEquiv d (sz.L n) (sz.W n)).symm y), ?_⟩
  have e : ‖(baFMz sz z).GM n (t n) ω ((splitEquiv d (sz.L n) (sz.W n)).symm x) ((splitEquiv d (sz.L n) (sz.W n)).symm y)‖ =
      ‖GreenCore_Gc sz z n (t n) ω x y - GreenCore_Mc sz z n x y‖ := rfl
  change ((sz.size n : ℕ) : ℝ) ^ (𝔠 * τ) * Ψ n < ‖(baFMz sz z).GM n (t n) ω ((splitEquiv d (sz.L n) (sz.W n)).symm x)
    ((splitEquiv d (sz.L n) (sz.W n)).symm y)‖
  rw [e]
  exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right hNW hΨn) hxy

end Data

/-! ## 3. The exponent bookkeeping: `hB1` and `hsmall` eventually -/

section Arith

/-- **The two numerical conditions of `GreenCond_famGain_slice`, from polynomial bounds in `N`** (`N = (WL)^d`): with `δ ≥ N^{-d}`, the
envelope `Env ≤ C_E N²`, the tower measure `P(Bad_{M+1}) ≤ (2 N^{c₁+1})^{M+1} P(S)`, `P(S) ≤ N^{-D'}`, `c₁ = d(M+1) + 3`,
`D' = 2K + (c₁+1)(M+1) + dK(M+1) + 1`, and `N` large: the price of conditionalising is `≤ 2δ` at the threshold `ε' = N^{-c₁}`, and `hsmall` holds. -/
theorem GreenCond2_arith {d M K : ℕ} {N δ Env cM CE Pbad PS : ℝ}
    (hN1 : 1 ≤ N) (hδ0 : 0 < δ) (hδN : 1 ≤ N ^ d * δ) (hEnv1 : 1 ≤ Env) (hEnv : Env ≤ CE * N ^ 2) (hCE : 1 ≤ CE) (hcM : 1 ≤ cM)
    (hPb0 : 0 ≤ Pbad) (hPS0 : 0 ≤ PS)
    (hPbad : Pbad ≤ (2 * N ^ (d * (M + 1) + 4)) ^ (M + 1) * PS)
    (hPS : PS * N ^ (2 * K + (d * (M + 1) + 4) * (M + 1) + d * K * (M + 1) + 1) ≤ 1)
    (hN₁ : (M + 1) * 2 ^ (2 * M + 1) * CE ≤ N)
    (hN₂ : (2 ^ (2 * M + 1) * CE) ^ K * 2 ^ (M + 1) ≤ N) :
    GreenCond_cost Env M (2 * δ) (1 / N ^ (d * (M + 1) + 3)) ≤ 2 * δ ∧
      GreenCond_genv Env M ^ K * Pbad ≤
        (2 * cM * (2 * δ) + GreenCond_cost Env M (2 * δ) (1 / N ^ (d * (M + 1) + 3))) ^ K * (2 * (2 * δ)) ^ (K * M) := by
  have hN0 : 0 < N := by linarith only [hN1]
  have hu : ∀ j : ℕ, 1 ≤ (N ^ d * δ) ^ j := fun j => one_le_pow₀ hδN
  have hcost : GreenCond_cost Env M (2 * δ) (1 / N ^ (d * (M + 1) + 3)) ≤ 2 * δ := by
    unfold GreenCond_cost GreenCond_genv
    have hq0 : 0 < (2 * (2 * δ)) ^ M := by positivity
    have hq : δ ^ M ≤ (2 * (2 * δ)) ^ M := pow_le_pow_left₀ hδ0.le (by linarith) M
    have hdelta : 1 ≤ δ ^ (M + 1) * N ^ (d * (M + 1)) := by
      have := hu (M + 1)
      calc (1 : ℝ) ≤ (N ^ d * δ) ^ (M + 1) := this
        _ = δ ^ (M + 1) * N ^ (d * (M + 1)) := by rw [mul_pow, ← pow_mul, mul_comm]
    have hlow : 2 * N ^ 3 ≤ 2 * δ * N ^ (d * (M + 1) + 3) * (2 * (2 * δ)) ^ M := by
      calc 2 * N ^ 3 ≤ 2 * N ^ 3 * (δ ^ (M + 1) * N ^ (d * (M + 1))) := le_mul_of_one_le_right (by positivity) hdelta
        _ = 2 * δ * N ^ (d * (M + 1) + 3) * δ ^ M := by rw [pow_add, pow_succ]; ring
        _ ≤ 2 * δ * N ^ (d * (M + 1) + 3) * (2 * (2 * δ)) ^ M := mul_le_mul_of_nonneg_left hq (by positivity)
    have hup : ((M : ℝ) + 1) * (2 ^ (2 * M + 1) * Env) ≤ 2 * N ^ 3 := by
      calc ((M : ℝ) + 1) * (2 ^ (2 * M + 1) * Env) ≤ ((M : ℝ) + 1) * (2 ^ (2 * M + 1) * (CE * N ^ 2)) := by gcongr
        _ = ((M + 1) * 2 ^ (2 * M + 1) * CE) * N ^ 2 := by ring
        _ ≤ N * N ^ 2 := by gcongr
        _ ≤ 2 * N ^ 3 := by nlinarith [pow_pos hN0 3]
    have e : ((M : ℝ) + 1) * (2 ^ (2 * M + 1) * Env) * (1 / N ^ (d * (M + 1) + 3)) * ((2 * (2 * δ)) ^ M)⁻¹
        = ((M : ℝ) + 1) * (2 ^ (2 * M + 1) * Env) / (N ^ (d * (M + 1) + 3) * (2 * (2 * δ)) ^ M) := by
      field_simp
    rw [e, div_le_iff₀ (by positivity)]
    nlinarith [hup, hlow]
  refine ⟨hcost, ?_⟩
  set cost := GreenCond_cost Env M (2 * δ) (1 / N ^ (d * (M + 1) + 3)) with hcostdef
  have hcost0 : 0 ≤ cost := by
    rw [hcostdef]; unfold GreenCond_cost GreenCond_genv; positivity
  have hB : δ ≤ 2 * cM * (2 * δ) + cost := by nlinarith
  have hrhs : δ ^ (K * (M + 1)) ≤ (2 * cM * (2 * δ) + cost) ^ K * (2 * (2 * δ)) ^ (K * M) := by
    calc δ ^ (K * (M + 1)) = δ ^ K * δ ^ (K * M) := by rw [← pow_add]; congr 1; ring
      _ ≤ (2 * cM * (2 * δ) + cost) ^ K * (2 * (2 * δ)) ^ (K * M) := by
          gcongr
          linarith
  refine le_trans ?_ hrhs
  -- the left side times `N^{dK(M+1)}` is at most `1`
  set E : ℕ := 2 * K + (d * (M + 1) + 4) * (M + 1) + d * K * (M + 1) with hE
  have hLHS : GreenCond_genv Env M ^ K * Pbad ≤ (2 ^ (2 * M + 1) * CE) ^ K * 2 ^ (M + 1) * (N ^ (2 * K + (d * (M + 1) + 4) * (M + 1)) * PS) := by
    unfold GreenCond_genv
    calc (2 ^ (2 * M + 1) * Env) ^ K * Pbad ≤ (2 ^ (2 * M + 1) * (CE * N ^ 2)) ^ K * ((2 * N ^ (d * (M + 1) + 4)) ^ (M + 1) * PS) := by
          have h1 : 0 ≤ 2 ^ (2 * M + 1) * Env := by positivity
          gcongr
      _ = (2 ^ (2 * M + 1) * CE) ^ K * 2 ^ (M + 1) * (N ^ (2 * K + (d * (M + 1) + 4) * (M + 1)) * PS) := by
          rw [mul_pow, mul_pow, mul_pow, ← pow_mul, ← pow_mul, pow_add]; ring
  have hmain : GreenCond_genv Env M ^ K * Pbad * N ^ (d * K * (M + 1)) ≤ 1 := by
    calc GreenCond_genv Env M ^ K * Pbad * N ^ (d * K * (M + 1))
        ≤ (2 ^ (2 * M + 1) * CE) ^ K * 2 ^ (M + 1) * (N ^ (2 * K + (d * (M + 1) + 4) * (M + 1)) * PS) * N ^ (d * K * (M + 1)) :=
          mul_le_mul_of_nonneg_right hLHS (by positivity)
      _ ≤ N * (N ^ (2 * K + (d * (M + 1) + 4) * (M + 1)) * PS) * N ^ (d * K * (M + 1)) := by gcongr
      _ = PS * N ^ (2 * K + (d * (M + 1) + 4) * (M + 1) + d * K * (M + 1) + 1) := by
          rw [pow_succ, pow_add]; ring
      _ ≤ 1 := hPS
  have hpow : 1 ≤ δ ^ (K * (M + 1)) * N ^ (d * K * (M + 1)) := by
    calc (1 : ℝ) ≤ (N ^ d * δ) ^ (K * (M + 1)) := hu _
      _ = δ ^ (K * (M + 1)) * N ^ (d * K * (M + 1)) := by rw [mul_pow, ← pow_mul, mul_comm]; ring_nf
  have hL0 : 0 ≤ GreenCond_genv Env M ^ K * Pbad := by unfold GreenCond_genv; positivity
  calc GreenCond_genv Env M ^ K * Pbad ≤ GreenCond_genv Env M ^ K * Pbad * (δ ^ (K * (M + 1)) * N ^ (d * K * (M + 1))) :=
        le_mul_of_one_le_right hL0 hpow
    _ = (GreenCond_genv Env M ^ K * Pbad * N ^ (d * K * (M + 1))) * δ ^ (K * (M + 1)) := by ring
    _ ≤ 1 * δ ^ (K * (M + 1)) := mul_le_mul_of_nonneg_right hmain (by positivity)
    _ = δ ^ (K * (M + 1)) := one_mul _

/-- **The tower measure in real numbers**: `ε^j P(Bad_j) ≤ (ε + N)^j P(S)`. -/
theorem GreenCond2_Pbad_le {d : ℕ} (sz : Sizes d) (n : ℕ) {ε : ℝ} (hε : 0 < ε) {S : Set sz.SeqΩ} (hS : MeasurableSet S) (j : ℕ) :
    ε ^ j * (Sizes.seqP sz).real (badTower sz n ε S j) ≤ (ε + (sz.size n : ℝ)) ^ j * (Sizes.seqP sz).real S := by
  have h := minorDiffCond_meas_badTower_le_size sz n (ε := ε) hS j
  have hfin : (ENNReal.ofReal ε + (sz.size n : ℝ≥0∞)) ^ j * (Sizes.seqP sz) S ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.pow_ne_top (ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top, ENNReal.natCast_ne_top _⟩)) (measure_ne_top _ _)
  have h2 := ENNReal.toReal_mono hfin h
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_pow, ENNReal.toReal_add ENNReal.ofReal_ne_top
    (ENNReal.natCast_ne_top _), ENNReal.toReal_ofReal hε.le, ENNReal.toReal_natCast] at h2
  exact h2

/-- `P(Bad_j) ≤ (2 N^{c+1})^j P(S)` for the threshold `ε = N^{-c}` (`N = sz.size n ≥ 1`). -/
theorem GreenCond2_Pbad_le' {d : ℕ} (sz : Sizes d) (n : ℕ) {S : Set sz.SeqΩ} (hS : MeasurableSet S) (c j : ℕ) :
    (Sizes.seqP sz).real (badTower sz n (1 / (sz.size n : ℝ) ^ c) S j) ≤
      (2 * (sz.size n : ℝ) ^ (c + 1)) ^ j * (Sizes.seqP sz).real S := by
  have hN1 : (1 : ℝ) ≤ (sz.size n : ℝ) := by exact_mod_cast sz.one_le_size n
  set N : ℝ := (sz.size n : ℝ) with hN
  have hN0 : 0 < N := by linarith only [hN1]
  have hε : 0 < 1 / N ^ c := by positivity
  have h := GreenCond2_Pbad_le sz n hε hS j
  rw [← hN] at h
  have hP0 : 0 ≤ (Sizes.seqP sz).real S := measureReal_nonneg
  have he : (1 / N ^ c + N) = (1 + N ^ (c + 1)) * (1 / N ^ c) := by
    field_simp
    ring
  rw [he, mul_pow] at h
  have hεj : 0 < (1 / N ^ c) ^ j := by positivity
  have h1 : (Sizes.seqP sz).real (badTower sz n (1 / N ^ c) S j) ≤ (1 + N ^ (c + 1)) ^ j * (Sizes.seqP sz).real S := by
    have := h
    rw [mul_assoc] at this
    nlinarith [mul_pos hεj hεj, mul_nonneg (pow_nonneg (by positivity : (0 : ℝ) ≤ 1 + N ^ (c + 1)) j) hP0]
  refine h1.trans ?_
  refine mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) ?_ j) hP0
  have : (1 : ℝ) ≤ N ^ (c + 1) := one_le_pow₀ hN1
  linarith

end Arith

/-! ## 4. `BAFamGain` -/

section FamGain
variable {d : ℕ}

theorem GreenCond2_one_le_d (sz : Sizes d) (h : sz.SizeTendsto) : 1 ≤ d := by
  by_contra h0
  have hd : d = 0 := by omega
  subst hd
  have := (h.eventually_ge_atTop 2).exists
  obtain ⟨n, hn⟩ := this
  have h1 : ((sz.size n : ℕ) : ℝ) = 1 := by simp [Sizes.size]
  rw [h1] at hn
  norm_num at hn

/-- `W ≤ N` (`d ≥ 1`). -/
theorem GreenCond2_W_le_size (sz : Sizes d) (hd : 1 ≤ d) (n : ℕ) : (sz.W n : ℝ) ≤ (sz.size n : ℝ) := by
  have h1 : sz.W n ≤ sz.W n * sz.L n := Nat.le_mul_of_pos_right _ (by have := sz.three_le_L n; omega)
  have h2 : sz.W n * sz.L n ≤ (sz.W n * sz.L n) ^ d := Nat.le_self_pow (by omega) _
  exact_mod_cast h1.trans h2

theorem GreenCond2_delta_small (sz : Sizes d) {𝔠 𝔡 : ℝ} (hA : sz.Admissible 𝔠 𝔡) {ε₀ τ : ℝ} (hε₀ : 0 < ε₀) (hτε : τ ≤ ε₀ / 2)
    {Ψ : ℕ → ℝ} (hΨ0 : ∀ᶠ n in atTop, 0 ≤ Ψ n) (hΨhi : ∀ᶠ n in atTop, Ψ n ≤ ((sz.W n : ℕ) : ℝ) ^ (-ε₀)) {δ₀ : ℝ}
    (hδ₀ : 0 < δ₀) : ∀ᶠ n in atTop, ((sz.W n : ℕ) : ℝ) ^ τ * Ψ n ≤ δ₀ := by
  have hW := tendsto_W sz hA.1 hA.2.2.1 hA.2.2.2.1
  have hlim := (tendsto_rpow_neg_atTop (show 0 < ε₀ / 2 by positivity)).comp hW
  filter_upwards [hΨ0, hΨhi, (tendsto_order.1 hlim).2 δ₀ hδ₀, hW.eventually_ge_atTop 1] with n h0 hhi hsm hW1
  have hW0 : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by linarith only [hW1]
  have hsm' : ((sz.W n : ℕ) : ℝ) ^ (-(ε₀ / 2)) < δ₀ := hsm
  calc ((sz.W n : ℕ) : ℝ) ^ τ * Ψ n ≤ ((sz.W n : ℕ) : ℝ) ^ τ * ((sz.W n : ℕ) : ℝ) ^ (-ε₀) :=
        mul_le_mul_of_nonneg_left hhi (Real.rpow_nonneg hW0.le _)
    _ = ((sz.W n : ℕ) : ℝ) ^ (τ + -ε₀) := (Real.rpow_add hW0 _ _).symm
    _ ≤ ((sz.W n : ℕ) : ℝ) ^ (-(ε₀ / 2)) := Real.rpow_le_rpow_of_exponent_le hW1 (by linarith)
    _ ≤ δ₀ := hsm'.le

/-- `δ_n = W^τ Ψ_n ≥ Ψ_n ≥ W^{-d/2}` gives `1 ≤ N^d δ_n`. -/
theorem GreenCond2_delta_lower (sz : Sizes d) (hd : 1 ≤ d) (n : ℕ) {τ Ψn : ℝ} (hτ : 0 ≤ τ)
    (hΨ : ((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2) ≤ Ψn) :
    1 ≤ ((sz.size n : ℕ) : ℝ) ^ d * (((sz.W n : ℕ) : ℝ) ^ τ * Ψn) := by
  have hW1 : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hW0 : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by linarith only [hW1]
  have hWN := GreenCond2_W_le_size sz hd n
  have hΨ0 : 0 ≤ Ψn := le_trans (Real.rpow_nonneg hW0.le _) hΨ
  have hWτ : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) ^ τ := Real.one_le_rpow hW1 hτ
  have h1 : ((sz.W n : ℕ) : ℝ) ^ d ≤ ((sz.size n : ℕ) : ℝ) ^ d := pow_le_pow_left₀ hW0.le hWN d
  have h2 : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) ^ d * ((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hW0]
    exact Real.one_le_rpow hW1 (by have : (0 : ℝ) ≤ d := Nat.cast_nonneg d; linarith)
  calc (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) ^ d * ((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2) := h2
    _ ≤ ((sz.size n : ℕ) : ℝ) ^ d * Ψn := mul_le_mul h1 hΨ (by positivity) (by positivity)
    _ ≤ ((sz.size n : ℕ) : ℝ) ^ d * (((sz.W n : ℕ) : ℝ) ^ τ * Ψn) :=
        mul_le_mul_of_nonneg_left (le_mul_of_one_le_left hΨ0 hWτ) (by positivity)

/-- The envelope bound: `Env(g₀, ‖s‖, e) ≤ ((sbd + 2dΛ)(1/κ + 1) + 4dΛ/κ) e²` for `g₀ ≤ Λ`, `‖s‖ ≤ sbd`, `e ≥ 1`. -/
theorem GreenCond2_Env_le {κ g₀ Λ s sbd e : ℝ} (hκ : 0 < κ) (hg : 0 ≤ g₀) (hgΛ : g₀ ≤ Λ) (hs0 : 0 ≤ s) (hs : s ≤ sbd)
    (he1 : 1 ≤ e) : GreenCond_Env d κ g₀ s e ≤ ((sbd + 2 * d * Λ) * (1 / κ + 1) + 4 * d * Λ / κ) * e ^ 2 := by
  unfold GreenCond_Env
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hΛ : 0 ≤ Λ := hg.trans hgΛ
  have he0 : 0 ≤ e := by linarith
  have hee : e ≤ e ^ 2 := by nlinarith
  have hκ' : 0 ≤ 1 / κ + 1 := by positivity
  calc ((s + 2 * d * g₀) * (1 / κ + 1) + 4 * d * g₀ * e / κ) * e
      ≤ ((sbd + 2 * d * Λ) * (1 / κ + 1) + 4 * d * Λ * e / κ) * e := by
        gcongr
    _ = (sbd + 2 * d * Λ) * (1 / κ + 1) * e + 4 * d * Λ / κ * e ^ 2 := by ring
    _ ≤ (sbd + 2 * d * Λ) * (1 / κ + 1) * e ^ 2 + 4 * d * Λ / κ * e ^ 2 := by
        have : 0 ≤ (sbd + 2 * d * Λ) * (1 / κ + 1) := by
          have : 0 ≤ sbd := hs0.trans hs
          positivity
        nlinarith
    _ = ((sbd + 2 * d * Λ) * (1 / κ + 1) + 4 * d * Λ / κ) * e ^ 2 := by ring

/-- The gain interface is monotone in the constant `B`. -/
theorem GreenCond2_famGain_mono {n : ℕ} {sz : Sizes d} {A : Finset (Idx d (sz.L n) (sz.W n))} {Y : Idx d (sz.L n) (sz.W n) → sz.SeqΩ → ℂ}
    {B B' ρ : ℝ} {M K : ℕ} (h : GreenMinor_famGain sz n A Y B ρ M K) (hB : B ≤ B') : GreenMinor_famGain sz n A Y B' ρ M K := by
  refine ⟨h.1.trans hB, h.2.1, fun ι _ k L h1 h2 h3 h4 h5 => ?_⟩
  refine (h.2.2 ι k L h1 h2 h3 h4 h5).trans ?_
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ h.1 hB _) (by have := h.2.1; positivity)

/-- The envelope bound at `e = η⁻¹ + 1` with `η⁻¹ ≤ (2/κ) N`: `Env ≤ C_E N²`. -/
theorem GreenCond2_Env_aux {κ g₀ Λ s sbd N Einv cE CE : ℝ} (hκ : 0 < κ) (hg : 0 ≤ g₀) (hgΛ : g₀ ≤ Λ) (hs0 : 0 ≤ s) (hs : s ≤ sbd)
    (hE0 : 0 ≤ Einv) (hη : Einv ≤ 2 / κ * N) (hN1 : 1 ≤ N)
    (hcE : cE = (sbd + 2 * d * Λ) * (1 / κ + 1) + 4 * d * Λ / κ) (hCE : CE = 1 + cE * (2 / κ + 1) ^ 2) (hcE0 : 0 ≤ cE) :
    GreenCond_Env d κ g₀ s (Einv + 1) ≤ CE * N ^ 2 := by
  have he1 : (1 : ℝ) ≤ Einv + 1 := by linarith
  have he : Einv + 1 ≤ (2 / κ + 1) * N := by
    have : 0 ≤ 2 / κ := by positivity
    have h2 : 2 / κ * N + 1 ≤ 2 / κ * N + N := by linarith
    calc Einv + 1 ≤ 2 / κ * N + 1 := by linarith
      _ ≤ 2 / κ * N + N := h2
      _ = (2 / κ + 1) * N := by ring
  refine (GreenCond2_Env_le hκ hg hgΛ hs0 hs he1).trans ?_
  rw [← hcE]
  have h2 : (Einv + 1) ^ 2 ≤ ((2 / κ + 1) * N) ^ 2 := pow_le_pow_left₀ (by linarith) he 2
  calc cE * (Einv + 1) ^ 2 ≤ cE * ((2 / κ + 1) * N) ^ 2 := mul_le_mul_of_nonneg_left h2 hcE0
    _ = (cE * (2 / κ + 1) ^ 2) * N ^ 2 := by ring
    _ ≤ CE * N ^ 2 := by rw [hCE]; nlinarith [sq_nonneg N]

/-- **`BAFamGain d`, proved** (the owed pin of the G5b row; consumer: `baFAav_holds`).  Fix the data of the pin, `p` and `τ`.  The constants
`c_M = 1 + c_Y(M)` (at `Λ = 𝔡⁻¹`, `sbd = (1 + 2dΛ)/κ ≥ ‖s‖`) and `C = 8 c_M + 4` depend on `(d, κ, 𝔡, p)` only; for `n` large the slice
theorem `GreenCond_famGain_slice` applies with `δ = W^τ Ψ_n`, the tower threshold `ε' = N^{-c₁}`, `c₁ = d(M+1) + 3`, the envelope
`Env = C_E N²` (`η_t⁻¹ ≤ (2/κ) N`), and `P(S_n) ≤ N^{-D'}` (`GreenCond2_prob_badBase`, `D'` a large integer). -/
theorem baFamGain_holds (d : ℕ) : BAFamGain d := by
  intro κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow t ht0 htT ε₀ hε₀ hii Ψ hΨlo hΨhi hinit τ hτ hτε p
  have hd1 : 1 ≤ d := GreenCond2_one_le_d sz hflow.1.2.2.1
  have hsz : sz.SizeTendsto := hflow.1.2.2.1
  have hκ1 : κ ≤ 1 := by
    have hr := BAflow_real κ ε 𝔠 𝔡 sz z hflow 0
    have hm1 : ‖GreenCond_m sz z 0‖ ≤ 1 :=
      BAm_norm_le_one (d := d) (L := sz.L 0) (BAflowLam0 sz z 0) (BAflowEs sz z 0 : ℂ) (GreenCond_m sz z 0) (by simp) hr.1
    exact hr.2.trans ((le_abs_self _).trans ((Complex.abs_im_le_norm _).trans hm1))
  obtain ⟨Λ, hΛ⟩ : ∃ Λ : ℝ, Λ = 𝔡⁻¹ := ⟨_, rfl⟩
  have hΛ0 : 0 < Λ := by rw [hΛ]; exact inv_pos.2 h𝔡
  obtain ⟨sbd, hsbd⟩ : ∃ sbd : ℝ, sbd = (1 + 2 * d * Λ) / κ := ⟨_, rfl⟩
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hsbd0 : 0 ≤ sbd := by rw [hsbd]; positivity
  set M : ℕ := 2 * p with hM
  obtain ⟨cM, hcM1, hcMgen⟩ : ∃ cM : ℝ, 1 ≤ cM ∧ ∀ g₀ s : ℝ, 0 ≤ g₀ → g₀ ≤ Λ → 0 ≤ s → s ≤ sbd →
      GreenMinor_cY d κ g₀ s M ≤ cM := by
    have hcY0 : 0 ≤ GreenMinor_cY d κ Λ sbd M := by
      have ha := GreenMinor_a_nonneg hκ hκ1 M
      unfold GreenMinor_cY
      positivity
    refine ⟨1 + GreenMinor_cY d κ Λ sbd M, by linarith, fun g₀ s hg hgΛ hs0 hs => ?_⟩
    have := GreenCond_cY_mono (d := d) hκ hκ1 hg hgΛ hs0 hs (le_refl M)
    linarith
  obtain ⟨cE, hcE⟩ : ∃ cE : ℝ, cE = (sbd + 2 * d * Λ) * (1 / κ + 1) + 4 * d * Λ / κ := ⟨_, rfl⟩
  obtain ⟨CE, hCE⟩ : ∃ CE : ℝ, CE = 1 + cE * (2 / κ + 1) ^ 2 := ⟨_, rfl⟩
  obtain ⟨δ₀, hδ₀⟩ : ∃ δ₀ : ℝ, δ₀ = min (κ / (8 * M + 4)) (1 / (4 * cM + 2)) := ⟨_, rfl⟩
  obtain ⟨N₀, hN₀⟩ : ∃ N₀ : ℝ, N₀ = (M + 1) * 2 ^ (2 * M + 1) * CE + (2 ^ (2 * M + 1) * CE) ^ M * 2 ^ (M + 1) := ⟨_, rfl⟩
  have hcE0 : 0 ≤ cE := by rw [hcE]; have := hsbd0; positivity
  have hCE1 : 1 ≤ CE := by
    rw [hCE]
    have : 0 ≤ cE * (2 / κ + 1) ^ 2 := by positivity
    linarith
  have hcM0 : 0 < cM := by linarith
  have hδ₀0 : 0 < δ₀ := by rw [hδ₀]; exact lt_min (by positivity) (by positivity)
  refine ⟨8 * cM + 4, by positivity, ?_⟩
  have hΨ0 : ∀ᶠ n in atTop, 0 ≤ Ψ n := by
    filter_upwards [hΨlo] with n hn
    exact le_trans (Real.rpow_nonneg (Nat.cast_nonneg _) _) hn
  filter_upwards [hΨlo, hΨhi, BAflow_lam0_window κ ε 𝔠 𝔡 sz z hflow, GreenCond2_delta_small sz hflow.1 hε₀ hτε hΨ0 hΨhi hδ₀0,
    hsz.eventually_ge_atTop N₀, GreenCond2_prob_badBase hκ hε h𝔡 sz hflow ht0 htT hε₀ hii hΨ0 hinit hτ (D := ((2 * M + (d * (M + 1) + 4) * (M + 1) + d * M * (M + 1) + 1 : ℕ) : ℝ)) (by positivity)]
    with n hΨlon hΨhin hlam hδsm hNbig hPS
  intro β α hβα
  clear hii hinit hΨ0
  -- the sizes
  obtain ⟨N, hN⟩ : ∃ N : ℝ, N = ((sz.size n : ℕ) : ℝ) := ⟨_, rfl⟩
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = ((sz.W n : ℕ) : ℝ) ^ τ * Ψ n := ⟨_, rfl⟩
  have hN1 : (1 : ℝ) ≤ N := by rw [hN]; exact_mod_cast sz.one_le_size n
  have hN0 : 0 < N := by linarith only [hN1]
  have hW1 : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hW0 : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by linarith only [hW1]
  have hΨpos : 0 < Ψ n := lt_of_lt_of_le (Real.rpow_pos_of_pos hW0 _) hΨlon
  have hδ0 : 0 < δ := by rw [hδ]; positivity
  have hδN : 1 ≤ N ^ d * δ := by rw [hN, hδ]; exact GreenCond2_delta_lower sz hd1 n hτ.le hΨlon
  rw [← hδ, ← hN] at hPS
  obtain ⟨hg0', hgΛ⟩ := hlam
  have hg0 : 0 ≤ BAflowLam0 sz z n := hg0'.le
  have hgΛ' : BAflowLam0 sz z n ≤ Λ := by rw [hΛ]; exact hgΛ
  have hδδ₀ : δ ≤ δ₀ := by rw [hδ]; exact hδsm
  have hMnn : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  have hδ1 : δ * (8 * M + 4) ≤ κ := by
    have h1 : δ ≤ κ / (8 * M + 4) := by rw [hδ₀] at hδδ₀; exact hδδ₀.trans (min_le_left _ _)
    rwa [le_div_iff₀ (by positivity)] at h1
  have hMδ0 : 0 ≤ (M : ℝ) * δ := by positivity
  have hδ4 : 4 * δ ≤ κ := by nlinarith only [hδ1, hMδ0, hδ0]
  have hMδ : 8 * (M : ℝ) * δ ≤ κ := by nlinarith only [hδ1, hMδ0, hδ0]
  have hδ2 : 2 * δ ≤ 1 := by linarith only [hδ4, hκ1]
  have hδc : (4 * cM + 2) * δ ≤ 1 := by
    have h1 : δ ≤ 1 / (4 * cM + 2) := by rw [hδ₀] at hδδ₀; exact hδδ₀.trans (min_le_right _ _)
    rw [le_div_iff₀ (by positivity)] at h1
    linarith only [h1]
  -- the envelope
  have hs0 : 0 ≤ ‖GreenCond_s sz z n‖ := norm_nonneg _
  have hs : ‖GreenCond_s sz z n‖ ≤ sbd := by
    refine (GreenCond2_norm_s_le hκ sz hflow n (ht0 n) (htT n) hg0).trans ?_
    rw [hsbd]
    refine div_le_div_of_nonneg_right ?_ hκ.le
    have := mul_le_mul_of_nonneg_left hgΛ' (show (0 : ℝ) ≤ 2 * d by positivity)
    linarith only [this]
  have hη := GreenCond2_inv_eta_le hκ hε sz hflow n (ht0 n) (htT n)
  rw [← hN] at hη
  have hEnvG : GreenCond_Env d κ (BAflowLam0 sz z n) ‖GreenCond_s sz z n‖ (|(GreenCond_zt sz z n (t n)).im|⁻¹ + 1) ≤ CE * N ^ 2 :=
    GreenCond2_Env_aux hκ hg0 hgΛ' hs0 hs (inv_nonneg.2 (abs_nonneg _)) hη hN1 hcE hCE hcE0
  have hEnv1 : (1 : ℝ) ≤ CE * N ^ 2 := by
    have h1 : (1 : ℝ) ≤ N ^ 2 := one_le_pow₀ hN1
    calc (1 : ℝ) = 1 * 1 := by ring
      _ ≤ CE * N ^ 2 := mul_le_mul hCE1 h1 zero_le_one (by linarith only [hCE1])
  have hcMc : GreenMinor_cY d κ (BAflowLam0 sz z n) ‖GreenCond_s sz z n‖ M ≤ cM := hcMgen _ _ hg0 hgΛ' hs0 hs
  -- the tower
  have hS := GreenCond_measurableSet_badBase sz z n (t n) δ
  obtain ⟨PS, hPSdef⟩ : ∃ PS : ℝ, PS = (Sizes.seqP (sz.withLam 0)).real (GreenCond_badBase sz z n (t n) δ) := ⟨_, rfl⟩
  have hPS0 : 0 ≤ PS := by rw [hPSdef]; exact measureReal_nonneg
  obtain ⟨Dn, hDn⟩ : ∃ Dn : ℕ, Dn = 2 * M + (d * (M + 1) + 4) * (M + 1) + d * M * (M + 1) + 1 := ⟨_, rfl⟩
  rw [← hDn] at hPS
  have hPSle : PS * N ^ (2 * M + (d * (M + 1) + 4) * (M + 1) + d * M * (M + 1) + 1) ≤ 1 := by
    rw [← hDn]
    have h1 : PS ≤ N ^ (-(Dn : ℝ)) := by
      have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hPS
      rw [ENNReal.toReal_ofReal (Real.rpow_nonneg hN0.le _)] at this
      rw [hPSdef]
      exact this
    calc PS * N ^ Dn ≤ N ^ (-(Dn : ℝ)) * N ^ Dn := mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = 1 := by rw [← Real.rpow_natCast N Dn, ← Real.rpow_add hN0, neg_add_cancel, Real.rpow_zero]
  have hPbad : (Sizes.seqP (sz.withLam 0)).real (badTower (sz.withLam 0) n (1 / N ^ (d * (M + 1) + 3)) (GreenCond_badBase sz z n (t n) δ) (M + 1)) ≤
      (2 * N ^ (d * (M + 1) + 4)) ^ (M + 1) * PS := by
    rw [hPSdef, hN]
    exact GreenCond2_Pbad_le' (sz.withLam 0) n hS (d * (M + 1) + 3) (M + 1)
  have hNbig' : N₀ ≤ N := by rw [hN]; exact hNbig
  have hNN₁ : ((M : ℝ) + 1) * 2 ^ (2 * M + 1) * CE ≤ N := by
    have : 0 ≤ (2 ^ (2 * M + 1) * CE) ^ M * 2 ^ (M + 1) := by positivity
    rw [hN₀] at hNbig'
    linarith only [hNbig', this]
  have hNN₂ : (2 ^ (2 * M + 1) * CE) ^ M * 2 ^ (M + 1) ≤ N := by
    have : 0 ≤ ((M : ℝ) + 1) * 2 ^ (2 * M + 1) * CE := by positivity
    rw [hN₀] at hNbig'
    linarith only [hNbig', this]
  obtain ⟨hcost, hsmall⟩ := GreenCond2_arith (d := d) (M := M) (K := M) (N := N) (δ := δ) (Env := CE * N ^ 2) (cM := cM) (CE := CE)
    (Pbad := (Sizes.seqP (sz.withLam 0)).real (badTower (sz.withLam 0) n (1 / N ^ (d * (M + 1) + 3)) (GreenCond_badBase sz z n (t n) δ) (M + 1)))
    (PS := PS) hN1 hδ0 hδN hEnv1 le_rfl hCE1 hcM1 measureReal_nonneg hPS0 hPbad hPSle hNN₁ hNN₂
  have hB1 : 2 * cM * (2 * δ) + GreenCond_cost (CE * N ^ 2) M (2 * δ) (1 / N ^ (d * (M + 1) + 3)) ≤ 1 := by
    nlinarith only [hcost, hδc]
  have hε' : (0 : ℝ) ≤ 1 / N ^ (d * (M + 1) + 3) := by positivity
  have hslice := GreenCond_famGain_slice hκ sz hflow t n (ht0 n) (htT n) hg0 (δ := δ) (ε' := 1 / N ^ (d * (M + 1) + 3))
    (Env := CE * N ^ 2) (cM := cM) (M := M) (K := M) hδ0 hδ4 hMδ hδ2 hε' hEnvG hEnv1 hcMc hB1 hsmall β α hβα
  obtain ⟨hA, hX⟩ := hslice
  have e : 2 * (2 * δ) = 4 * δ := by ring
  have hBle : 2 * (2 * cM * (2 * δ) + GreenCond_cost (CE * N ^ 2) M (2 * δ) (1 / N ^ (d * (M + 1) + 3))) ≤ (8 * cM + 4) * δ := by
    nlinarith only [hcost]
  rw [← hδ]
  rw [e] at hA hX
  exact ⟨GreenCond2_famGain_mono hA hBle, GreenCond2_famGain_mono hX hBle⟩

end FamGain

/-! ## 5. The remainders of (E): `𝒜'_u = Q_u Y^A - Q_u[A_u Δ_{uu}]/m + ε₂`, `𝔛_{uy} = - Q_u Y^X - Q_u[𝔛_{uy} Δ_{uu}]/m`

The two identities are exact at every sample (the Gaussian conditional means `E_u A_u = - t v̄ + ε₂`, `E_u 𝔛_{uy} = 0` and S3
`A_u = Y^A m/G_{uu}`, `𝔛_{uy} = - Y^X m/G_{uu}`); off the bad row slice the remainders are `≤ C₁ δ²` (the pointwise bounds,
`GreenCond_m5_A/X`, and `|ε₂| ≤ 13 δ²/(2κ)`), with `C₁ = C₁(d, κ, g₀, ‖s‖)` monotone, so uniform in `n`. -/

section Decomp
variable {d : ℕ} {sz : Sizes d} {z : ℕ → ℂ} {n : ℕ} {t : ℝ}

/-- **(E) for `𝒜'`, exact**: `A_u + t v̄_{[u]} = Q_u Y^A_u - Q_u[A_u Δ_{uu}]/m + ε₂`, at every sample. -/
theorem GreenCond_E_A {κ ε 𝔠 𝔡 : ℝ} (hκ : 0 < κ) (h : BAFlow sz κ ε 𝔠 𝔡 z) (ht0 : 0 ≤ t) (ht : t ≤ BAflowT0 sz z n)
    (hg0 : 0 ≤ BAflowLam0 sz z n) (ht1 : t ≤ 1) (u : Idx d (sz.L n) (sz.W n)) (ω : (GreenCond_sz0 sz).SeqΩ) :
    GreenCore_Arow (GreenCore_Gc sz z n t ω) (GreenCore_Xc sz n t ω) (GreenCore_Dc sz z n) t (GreenCond_m sz z n) (splitEquiv d (sz.L n) (sz.W n) u) +
        (t : ℂ) * GreenCore_vbar (GreenCore_Gc sz z n t ω) (GreenCore_Mc sz z n) (splitEquiv d (sz.L n) (sz.W n) u).1 =
      qRow (GreenCond_sz0 sz) n u (fun σ => GreenCond_ΦA sz z n u (GreenCore_Gc sz z n t σ)) ω
        - (1 / GreenCond_m sz z n) * qRow (GreenCond_sz0 sz) n u (GreenCond_FA sz z n t u) ω
        + GreenCore_eps2 (GreenCore_Gc sz z n t ω) t (splitEquiv d (sz.L n) (sz.W n) u) := by
  have dat := GreenCond_data hκ sz h n ht0 ht hg0
  have hm0 : GreenCond_m sz z n ≠ 0 := fun h0 => by
    have := dat.hκm; rw [h0, norm_zero] at this; linarith [dat.hκ]
  have hsplit : ∀ σ : (GreenCond_sz0 sz).SeqΩ,
      GreenCore_Arow (GreenCore_Gc sz z n t σ) (GreenCore_Xc sz n t σ) (GreenCore_Dc sz z n) t (GreenCond_m sz z n) (splitEquiv d (sz.L n) (sz.W n) u) =
        GreenCond_ΦA sz z n u (GreenCore_Gc sz z n t σ) - GreenCond_FA sz z n t u σ / GreenCond_m sz z n := by
    intro σ
    have hA := GreenCond_Arow_YA hκ h ht0 ht hg0 σ (splitEquiv d (sz.L n) (sz.W n) u)
    have hG0 := GreenCond_G_diag_ne sz z n t hκ h ht0 ht σ (splitEquiv d (sz.L n) (sz.W n) u)
    unfold GreenCond_FA GreenCond_ΦA
    rw [show split d (sz.L n) (sz.W n) u = splitEquiv d (sz.L n) (sz.W n) u from rfl]
    rw [hA]
    field_simp
    ring
  have hYi : Integrable (fun ω'' => GreenCond_ΦA sz z n u (GreenCore_Gc sz z n t (rowSplit (GreenCond_sz0 sz) n u ω ω''))) (Sizes.seqP (GreenCond_sz0 sz)) := by
    have := (GreenCond_bddMeas_A sz z n hκ h ht0 ht hg0 u ∅).rowIntegrable u ω
    rw [GreenCond_famS_empty sz z n hκ h ht0 ht] at this
    exact this
  have hFi : Integrable (fun ω'' => GreenCond_FA sz z n t u (rowSplit (GreenCond_sz0 sz) n u ω ω'')) (Sizes.seqP (GreenCond_sz0 sz)) :=
    GreenCond_integrable_of_sq ((GreenCond_measurable_FA hκ h ht0 ht hg0 u).comp (measurable_rowSplit_right (GreenCond_sz0 sz) n u ω))
      (GreenCond_FA_moment hκ h ht0 ht hg0 ht1 u ω).1
  have hcA := GreenCond_condRow_Arow sz z n t hκ h ht0 ht hg0 ht1 u ω
  have hlin : condRow (GreenCond_sz0 sz) n u (fun σ => GreenCore_Arow (GreenCore_Gc sz z n t σ) (GreenCore_Xc sz n t σ) (GreenCore_Dc sz z n) t
      (GreenCond_m sz z n) (splitEquiv d (sz.L n) (sz.W n) u)) ω =
      condRow (GreenCond_sz0 sz) n u (fun σ => GreenCond_ΦA sz z n u (GreenCore_Gc sz z n t σ)) ω -
        condRow (GreenCond_sz0 sz) n u (GreenCond_FA sz z n t u) ω / GreenCond_m sz z n := by
    simp only [condRow_apply, hsplit]
    rw [integral_sub hYi (hFi.div_const _), integral_div]
  rw [hlin] at hcA
  have hs := hsplit ω
  simp only [qRow_apply]
  linear_combination hs + hcA

/-- **(E) for `𝔛`, exact**: `𝔛_{uy} = - Q_u Y^X_{uy} - Q_u[𝔛_{uy} Δ_{uu}]/m`, `y = (α, o(u))`, `α ≠ [u]`, at every sample. -/
theorem GreenCond_E_X {κ ε 𝔠 𝔡 : ℝ} (hκ : 0 < κ) (h : BAFlow sz κ ε 𝔠 𝔡 z) (ht0 : 0 ≤ t) (ht : t ≤ BAflowT0 sz z n)
    (hg0 : 0 ≤ BAflowLam0 sz z n) (ht1 : t ≤ 1) (u : Idx d (sz.L n) (sz.W n)) {α : Zd d (sz.L n)} (hα : α ≠ (splitEquiv d (sz.L n) (sz.W n) u).1)
    (ω : (GreenCond_sz0 sz).SeqΩ) :
    GreenCore_Xrow (GreenCore_Gc sz z n t ω) (GreenCore_Xc sz n t ω) (splitEquiv d (sz.L n) (sz.W n) u) (α, (splitEquiv d (sz.L n) (sz.W n) u).2) =
      - qRow (GreenCond_sz0 sz) n u (fun σ => GreenCond_ΦX sz z n α u (GreenCore_Gc sz z n t σ)) ω
        - (1 / GreenCond_m sz z n) * qRow (GreenCond_sz0 sz) n u (GreenCond_FX sz z n t u α) ω := by
  have dat := GreenCond_data hκ sz h n ht0 ht hg0
  have hm0 : GreenCond_m sz z n ≠ 0 := fun h0 => by
    have := dat.hκm; rw [h0, norm_zero] at this; linarith [dat.hκ]
  have hyw : ((α, (splitEquiv d (sz.L n) (sz.W n) u).2) : Vtx d (sz.L n) (sz.W n)) ≠ splitEquiv d (sz.L n) (sz.W n) u :=
    fun h' => hα (congrArg Prod.fst h')
  have hsplit : ∀ σ : (GreenCond_sz0 sz).SeqΩ,
      GreenCore_Xrow (GreenCore_Gc sz z n t σ) (GreenCore_Xc sz n t σ) (splitEquiv d (sz.L n) (sz.W n) u) (α, (splitEquiv d (sz.L n) (sz.W n) u).2) =
        - GreenCond_ΦX sz z n α u (GreenCore_Gc sz z n t σ) - GreenCond_FX sz z n t u α σ / GreenCond_m sz z n := by
    intro σ
    have hX := GreenCond_Xrow_YX hκ h ht0 ht hg0 σ hyw
    have hG0 := GreenCond_G_diag_ne sz z n t hκ h ht0 ht σ (splitEquiv d (sz.L n) (sz.W n) u)
    unfold GreenCond_FX GreenCond_ΦX
    rw [show split d (sz.L n) (sz.W n) u = splitEquiv d (sz.L n) (sz.W n) u from rfl]
    rw [hX]
    field_simp
    ring
  have hYi : Integrable (fun ω'' => GreenCond_ΦX sz z n α u (GreenCore_Gc sz z n t (rowSplit (GreenCond_sz0 sz) n u ω ω''))) (Sizes.seqP (GreenCond_sz0 sz)) := by
    have := (GreenCond_bddMeas_X sz z n hκ h ht0 ht hg0 α u ∅).rowIntegrable u ω
    rw [GreenCond_famS_empty sz z n hκ h ht0 ht] at this
    exact this
  have hFi : Integrable (fun ω'' => GreenCond_FX sz z n t u α (rowSplit (GreenCond_sz0 sz) n u ω ω'')) (Sizes.seqP (GreenCond_sz0 sz)) :=
    GreenCond_integrable_of_sq ((GreenCond_measurable_FX hκ h ht0 ht hg0 u hα).comp (measurable_rowSplit_right (GreenCond_sz0 sz) n u ω))
      (GreenCond_FX_moment hκ h ht0 ht hg0 ht1 u hα ω).1
  have hc0 := (GreenCond_Xrow_cond sz z n t hκ h ht0 ht hg0 ht1 u (α, (splitEquiv d (sz.L n) (sz.W n) u).2) ω).1
  have hlin : condRow (GreenCond_sz0 sz) n u (fun σ => GreenCore_Xrow (GreenCore_Gc sz z n t σ) (GreenCore_Xc sz n t σ)
      (splitEquiv d (sz.L n) (sz.W n) u) (α, (splitEquiv d (sz.L n) (sz.W n) u).2)) ω =
      - condRow (GreenCond_sz0 sz) n u (fun σ => GreenCond_ΦX sz z n α u (GreenCore_Gc sz z n t σ)) ω -
        condRow (GreenCond_sz0 sz) n u (GreenCond_FX sz z n t u α) ω / GreenCond_m sz z n := by
    simp only [condRow_apply, hsplit]
    rw [integral_sub (f := fun ω' => - GreenCond_ΦX sz z n α u (GreenCore_Gc sz z n t (rowSplit (GreenCond_sz0 sz) n u ω ω')))
      (g := fun ω' => GreenCond_FX sz z n t u α (rowSplit (GreenCond_sz0 sz) n u ω ω') / GreenCond_m sz z n) hYi.neg (hFi.div_const _),
      integral_div, integral_neg]
  rw [hlin] at hc0
  have hs := hsplit ω
  simp only [qRow_apply]
  linear_combination hs + hc0

/-- The constants of the two pointwise bounds. -/
def GreenCond_cA (d : ℕ) (κ g₀ s : ℝ) : ℝ := 2 * (s + 2 * d * g₀) / κ ^ 2

def GreenCond_cX (d : ℕ) (κ g₀ s : ℝ) : ℝ := 2 / κ * ((s + 2 * d * g₀) * (1 / κ + 1) + 2 * d * g₀)

/-- `C₁ = (2 (c_A + c_X) + 15/2) / κ`: the constant of the two remainders of (E). -/
def GreenCond_C1 (d : ℕ) (κ g₀ s : ℝ) : ℝ := (2 * (GreenCond_cA d κ g₀ s + GreenCond_cX d κ g₀ s) + 15 / 2) / κ

theorem GreenCond_cA_nonneg {κ g₀ s : ℝ} (hg : 0 ≤ g₀) (hs : 0 ≤ s) : 0 ≤ GreenCond_cA d κ g₀ s := by
  unfold GreenCond_cA; positivity

theorem GreenCond_cX_nonneg {κ g₀ s : ℝ} (hκ : 0 < κ) (hg : 0 ≤ g₀) (hs : 0 ≤ s) : 0 ≤ GreenCond_cX d κ g₀ s := by
  unfold GreenCond_cX; positivity

/-- **`|ε₂| ≤ (13/(2κ)) δ²`** on the good event (`GreenCore_apriori`, `GreenCore_eps2_loc`; `W^{-d} ≤ δ²`). -/
theorem GreenCond_eps2_le {κ ε 𝔠 𝔡 : ℝ} (hκ : 0 < κ) (h : BAFlow sz κ ε 𝔠 𝔡 z) (ht0 : 0 ≤ t) (ht : t ≤ BAflowT0 sz z n)
    (hg0 : 0 ≤ BAflowLam0 sz z n) (ht1 : t ≤ 1) {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ2 : δ ≤ κ / 2) (σ : sz.SeqΩ)
    (hG : ∀ x y, ‖GreenCore_Gc sz z n t σ x y - GreenCore_Mc sz z n x y‖ ≤ δ) (hwd : (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ δ ^ 2)
    (w : Vtx d (sz.L n) (sz.W n)) : ‖GreenCore_eps2 (GreenCore_Gc sz z n t σ) t w‖ ≤ 13 / (2 * κ) * δ ^ 2 := by
  have dat := GreenCond_data hκ sz h n ht0 ht hg0
  have hMuu : ∀ w : Vtx d (sz.L n) (sz.W n), GreenCore_Mc sz z n w w = GreenCond_m sz z n := fun w => by
    rw [dat.hM w w]; simpa using dat.hMd w.1
  have hGuu : ∀ w : Vtx d (sz.L n) (sz.W n), κ / 2 ≤ ‖GreenCore_Gc sz z n t σ w w‖ := fun w => by
    have h1 : ‖GreenCond_m sz z n‖ - ‖GreenCore_Gc sz z n t σ w w‖ ≤ ‖GreenCore_Gc sz z n t σ w w - GreenCond_m sz z n‖ := by
      rw [norm_sub_rev]; exact norm_sub_norm_le _ _
    have := hG w w
    rw [hMuu w] at this
    linarith [dat.hκm]
  have hG32 : ∀ u v : Vtx d (sz.L n) (sz.W n), ‖GreenCore_Gc sz z n t σ u v‖ ≤ 3 / 2 := fun u v => by
    have h1 := hG u v
    have h2 := dat.hMle u v
    calc ‖GreenCore_Gc sz z n t σ u v‖ = ‖(GreenCore_Gc sz z n t σ u v - GreenCore_Mc sz z n u v) + GreenCore_Mc sz z n u v‖ := by ring_nf
      _ ≤ ‖GreenCore_Gc sz z n t σ u v - GreenCore_Mc sz z n u v‖ + ‖GreenCore_Mc sz z n u v‖ := norm_add_le _ _
      _ ≤ 3 / 2 := by linarith [dat.hκ1]
  have hGoff : ∀ u v : Vtx d (sz.L n) (sz.W n), u.2 ≠ v.2 → ‖GreenCore_Gc sz z n t σ u v‖ ≤ δ := fun u v huv => by
    have := hG u v
    simpa [dat.hM u v, huv] using this
  obtain ⟨hR, hRr⟩ := GreenCore_apriori (G := GreenCore_Gc sz z n t σ) hG32 hGoff hδ0 hwd
  have h2 := GreenCore_eps2_loc (G := GreenCore_Gc sz z n t σ) ht0 ht1 hκ hGuu w
  have hR0 : 0 ≤ GreenCore_R (GreenCore_Gc sz z n t σ) w.1 w := by unfold GreenCore_R; positivity
  have hRr0 : 0 ≤ GreenCore_Rrow (GreenCore_Gc sz z n t σ) w w.1 := by unfold GreenCore_Rrow; positivity
  refine le_of_pow_le_pow_left₀ two_ne_zero (by positivity) (h2.trans ?_)
  calc 4 / κ ^ 2 * GreenCore_R (GreenCore_Gc sz z n t σ) w.1 w * GreenCore_Rrow (GreenCore_Gc sz z n t σ) w w.1
      ≤ 4 / κ ^ 2 * (13 / 4 * δ ^ 2) * (13 / 4 * δ ^ 2) := by
        gcongr
        · exact hR _ _
        · exact hRr _ _
    _ = (13 / (2 * κ) * δ ^ 2) ^ 2 := by field_simp; ring

/-- **The remainder of (E) for `𝒜'`**: off a bad row slice, `‖A_u + t v̄_{[u]} - Q_u Y^A_u‖ ≤ C₁ δ²`. -/
theorem GreenCond_E_A_le {κ ε 𝔠 𝔡 : ℝ} (hκ : 0 < κ) (h : BAFlow sz κ ε 𝔠 𝔡 z) (ht0 : 0 ≤ t) (ht : t ≤ BAflowT0 sz z n)
    (hg0 : 0 ≤ BAflowLam0 sz z n) (ht1 : t ≤ 1) {δ ε' : ℝ} (hδ0 : 0 ≤ δ) (hδ2 : δ ≤ κ / 2) (hε' : 0 < ε')
    (u : Idx d (sz.L n) (sz.W n)) (ω : (GreenCond_sz0 sz).SeqΩ)
    (hG : ∀ x y, ‖GreenCore_Gc sz z n t ω x y - GreenCore_Mc sz z n x y‖ ≤ δ) (hwd : (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ δ ^ 2)
    (hslice : (Sizes.seqP (GreenCond_sz0 sz)).real (rowSlice (GreenCond_sz0 sz) n u (GreenCond_badBase sz z n t δ) ω) ≤ ε')
    (hsq : Real.sqrt (ε' * GreenCond_QA sz z n t) ≤ δ ^ 2) :
    ‖GreenCore_Arow (GreenCore_Gc sz z n t ω) (GreenCore_Xc sz n t ω) (GreenCore_Dc sz z n) t (GreenCond_m sz z n) (splitEquiv d (sz.L n) (sz.W n) u) +
        (t : ℂ) * GreenCore_vbar (GreenCore_Gc sz z n t ω) (GreenCore_Mc sz z n) (splitEquiv d (sz.L n) (sz.W n) u).1 -
        qRow (GreenCond_sz0 sz) n u (fun σ => GreenCond_ΦA sz z n u (GreenCore_Gc sz z n t σ)) ω‖ ≤
      GreenCond_C1 d κ (BAflowLam0 sz z n) ‖GreenCond_s sz z n‖ * δ ^ 2 := by
  have dat := GreenCond_data hκ sz h n ht0 ht hg0
  have hs0 := norm_nonneg (GreenCond_s sz z n)
  have e := GreenCond_E_A hκ h ht0 ht hg0 ht1 u ω
  have e' : GreenCore_Arow (GreenCore_Gc sz z n t ω) (GreenCore_Xc sz n t ω) (GreenCore_Dc sz z n) t (GreenCond_m sz z n) (splitEquiv d (sz.L n) (sz.W n) u) +
        (t : ℂ) * GreenCore_vbar (GreenCore_Gc sz z n t ω) (GreenCore_Mc sz z n) (splitEquiv d (sz.L n) (sz.W n) u).1 -
        qRow (GreenCond_sz0 sz) n u (fun σ => GreenCond_ΦA sz z n u (GreenCore_Gc sz z n t σ)) ω =
      -((1 / GreenCond_m sz z n) * qRow (GreenCond_sz0 sz) n u (GreenCond_FA sz z n t u) ω) +
        GreenCore_eps2 (GreenCore_Gc sz z n t ω) t (splitEquiv d (sz.L n) (sz.W n) u) := by rw [e]; ring
  rw [e']
  have h1 : ‖GreenCond_FA sz z n t u ω‖ ≤ GreenCond_cA d κ (BAflowLam0 sz z n) ‖GreenCond_s sz z n‖ * δ ^ 2 :=
    (GreenCond_pointwise_A sz z n t hκ h ht0 ht hg0 hδ0 hδ2 ω hG _).2
  have h2 := GreenCond_m5_A hκ h ht0 ht hg0 ht1 hδ0 hδ2 hε' u ω hslice
  have h3 := GreenCond_eps2_le hκ h ht0 ht hg0 ht1 hδ0 hδ2 ω hG hwd (splitEquiv d (sz.L n) (sz.W n) u)
  have hq : ‖qRow (GreenCond_sz0 sz) n u (GreenCond_FA sz z n t u) ω‖ ≤ (2 * GreenCond_cA d κ (BAflowLam0 sz z n) ‖GreenCond_s sz z n‖ + 1) * δ ^ 2 := by
    rw [qRow_apply]
    refine (norm_sub_le _ _).trans ?_
    have h2' : ‖condRow (GreenCond_sz0 sz) n u (GreenCond_FA sz z n t u) ω‖ ≤ GreenCond_cA d κ (BAflowLam0 sz z n) ‖GreenCond_s sz z n‖ * δ ^ 2 + δ ^ 2 := by
      refine h2.trans ?_
      unfold GreenCond_cA
      linarith [hsq]
    nlinarith [h1, h2']
  have hm : ‖1 / GreenCond_m sz z n‖ ≤ 1 / κ := by
    rw [norm_div, norm_one]
    exact one_div_le_one_div_of_le hκ dat.hκm
  refine (norm_add_le _ _).trans ?_
  rw [norm_neg, norm_mul]
  have hq0 : 0 ≤ (2 * GreenCond_cA d κ (BAflowLam0 sz z n) ‖GreenCond_s sz z n‖ + 1) * δ ^ 2 := by
    have := GreenCond_cA_nonneg (d := d) (κ := κ) hg0 hs0
    positivity
  calc ‖1 / GreenCond_m sz z n‖ * ‖qRow (GreenCond_sz0 sz) n u (GreenCond_FA sz z n t u) ω‖ + ‖GreenCore_eps2 (GreenCore_Gc sz z n t ω) t (splitEquiv d (sz.L n) (sz.W n) u)‖
      ≤ 1 / κ * ((2 * GreenCond_cA d κ (BAflowLam0 sz z n) ‖GreenCond_s sz z n‖ + 1) * δ ^ 2) + 13 / (2 * κ) * δ ^ 2 :=
        add_le_add (mul_le_mul hm hq (norm_nonneg _) (by positivity)) h3
    _ ≤ GreenCond_C1 d κ (BAflowLam0 sz z n) ‖GreenCond_s sz z n‖ * δ ^ 2 := by
        unfold GreenCond_C1
        have := GreenCond_cX_nonneg (d := d) hκ hg0 hs0 (s := ‖GreenCond_s sz z n‖)
        have hδ : 0 ≤ δ ^ 2 := sq_nonneg δ
        have e2 : 1 / κ * ((2 * GreenCond_cA d κ (BAflowLam0 sz z n) ‖GreenCond_s sz z n‖ + 1) * δ ^ 2) + 13 / (2 * κ) * δ ^ 2 =
            (2 * GreenCond_cA d κ (BAflowLam0 sz z n) ‖GreenCond_s sz z n‖ + 15 / 2) / κ * δ ^ 2 := by
          field_simp; ring
        rw [e2]
        refine mul_le_mul_of_nonneg_right ?_ hδ
        refine div_le_div_of_nonneg_right ?_ hκ.le
        linarith

/-- `4 d g₀ δ/κ ≤ 2 d g₀` for `δ ≤ κ/2`: the pointwise constant of `𝔛` is at most `c_X`. -/
theorem GreenCond_cX_ge {κ g₀ s δ : ℝ} (hκ : 0 < κ) (hg : 0 ≤ g₀) (hs : 0 ≤ s) (hδ0 : 0 ≤ δ) (hδ2 : δ ≤ κ / 2) :
    2 / κ * ((s + 2 * d * g₀) * (1 / κ + 1) + 4 * d * g₀ * δ / κ) ≤ GreenCond_cX d κ g₀ s := by
  unfold GreenCond_cX
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have h1 : 4 * d * g₀ * δ / κ ≤ 2 * d * g₀ := by
    rw [div_le_iff₀ hκ]
    have : 0 ≤ (d : ℝ) * g₀ := mul_nonneg hd hg
    nlinarith
  gcongr

/-- **The remainder of (E) for `𝔛`**: off a bad row slice, `‖𝔛_{uy} + Q_u Y^X_{uy}‖ ≤ C₁ δ²`, `y = (α, o(u))`, `α ≠ [u]`. -/
theorem GreenCond_E_X_le {κ ε 𝔠 𝔡 : ℝ} (hκ : 0 < κ) (h : BAFlow sz κ ε 𝔠 𝔡 z) (ht0 : 0 ≤ t) (ht : t ≤ BAflowT0 sz z n)
    (hg0 : 0 ≤ BAflowLam0 sz z n) (ht1 : t ≤ 1) {δ ε' : ℝ} (hδ0 : 0 ≤ δ) (hδ2 : δ ≤ κ / 2) (hε' : 0 < ε')
    (u : Idx d (sz.L n) (sz.W n)) {α : Zd d (sz.L n)} (hα : α ≠ (splitEquiv d (sz.L n) (sz.W n) u).1) (ω : (GreenCond_sz0 sz).SeqΩ)
    (hG : ∀ x y, ‖GreenCore_Gc sz z n t ω x y - GreenCore_Mc sz z n x y‖ ≤ δ)
    (hslice : (Sizes.seqP (GreenCond_sz0 sz)).real (rowSlice (GreenCond_sz0 sz) n u (GreenCond_badBase sz z n t δ) ω) ≤ ε')
    (hsq : Real.sqrt (ε' * GreenCond_QX sz z n t) ≤ δ ^ 2) :
    ‖GreenCore_Xrow (GreenCore_Gc sz z n t ω) (GreenCore_Xc sz n t ω) (splitEquiv d (sz.L n) (sz.W n) u) (α, (splitEquiv d (sz.L n) (sz.W n) u).2) +
        qRow (GreenCond_sz0 sz) n u (fun σ => GreenCond_ΦX sz z n α u (GreenCore_Gc sz z n t σ)) ω‖ ≤
      GreenCond_C1 d κ (BAflowLam0 sz z n) ‖GreenCond_s sz z n‖ * δ ^ 2 := by
  have dat := GreenCond_data hκ sz h n ht0 ht hg0
  have hs0 := norm_nonneg (GreenCond_s sz z n)
  have e := GreenCond_E_X hκ h ht0 ht hg0 ht1 u hα ω
  have e' : GreenCore_Xrow (GreenCore_Gc sz z n t ω) (GreenCore_Xc sz n t ω) (splitEquiv d (sz.L n) (sz.W n) u) (α, (splitEquiv d (sz.L n) (sz.W n) u).2) +
        qRow (GreenCond_sz0 sz) n u (fun σ => GreenCond_ΦX sz z n α u (GreenCore_Gc sz z n t σ)) ω =
      -((1 / GreenCond_m sz z n) * qRow (GreenCond_sz0 sz) n u (GreenCond_FX sz z n t u α) ω) := by rw [e]; ring
  rw [e', norm_neg, norm_mul]
  have hcX := GreenCond_cX_ge (d := d) hκ hg0 hs0 hδ0 hδ2 (s := ‖GreenCond_s sz z n‖)
  have h1 : ‖GreenCond_FX sz z n t u α ω‖ ≤ GreenCond_cX d κ (BAflowLam0 sz z n) ‖GreenCond_s sz z n‖ * δ ^ 2 :=
    ((GreenCond_pointwise_X sz z n t hκ h ht0 ht hg0 hδ0 hδ2 ω hG _ _ (fun h' => hα (congrArg Prod.fst h'))).2).trans
      (mul_le_mul_of_nonneg_right hcX (sq_nonneg δ))
  have h2 := GreenCond_m5_X hκ h ht0 ht hg0 ht1 hδ0 hδ2 hε' u hα ω hslice
  have hq : ‖qRow (GreenCond_sz0 sz) n u (GreenCond_FX sz z n t u α) ω‖ ≤ (2 * GreenCond_cX d κ (BAflowLam0 sz z n) ‖GreenCond_s sz z n‖ + 1) * δ ^ 2 := by
    rw [qRow_apply]
    refine (norm_sub_le _ _).trans ?_
    have h2' : ‖condRow (GreenCond_sz0 sz) n u (GreenCond_FX sz z n t u α) ω‖ ≤ GreenCond_cX d κ (BAflowLam0 sz z n) ‖GreenCond_s sz z n‖ * δ ^ 2 + δ ^ 2 := by
      refine h2.trans ?_
      have := mul_le_mul_of_nonneg_right hcX (sq_nonneg δ)
      linarith [hsq]
    nlinarith [h1, h2']
  have hm : ‖1 / GreenCond_m sz z n‖ ≤ 1 / κ := by
    rw [norm_div, norm_one]
    exact one_div_le_one_div_of_le hκ dat.hκm
  have hcX0 := GreenCond_cX_nonneg (d := d) hκ hg0 hs0 (s := ‖GreenCond_s sz z n‖)
  have hcA0 := GreenCond_cA_nonneg (d := d) (κ := κ) hg0 hs0
  calc ‖1 / GreenCond_m sz z n‖ * ‖qRow (GreenCond_sz0 sz) n u (GreenCond_FX sz z n t u α) ω‖
      ≤ 1 / κ * ((2 * GreenCond_cX d κ (BAflowLam0 sz z n) ‖GreenCond_s sz z n‖ + 1) * δ ^ 2) :=
        mul_le_mul hm hq (norm_nonneg _) (by positivity)
    _ ≤ GreenCond_C1 d κ (BAflowLam0 sz z n) ‖GreenCond_s sz z n‖ * δ ^ 2 := by
        unfold GreenCond_C1
        have e2 : 1 / κ * ((2 * GreenCond_cX d κ (BAflowLam0 sz z n) ‖GreenCond_s sz z n‖ + 1) * δ ^ 2) =
            (2 * GreenCond_cX d κ (BAflowLam0 sz z n) ‖GreenCond_s sz z n‖ + 1) / κ * δ ^ 2 := by
          field_simp
        rw [e2]
        refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg δ)
        refine div_le_div_of_nonneg_right ?_ hκ.le
        linarith

end Decomp

/-! ## 6. The offset averages: the row `ℓ¹` bound of `M^{(B)}` for every `d ≥ 1`, the Markov bound for the family average, `⟨M𝒦⟩_a`

`GreenCond2_row_l1` is `baM_row_l1` (`BA/GreenStab.lean:116`, `2 ≤ d`) for every `d ≥ 1`: the decay `BAMB_decay_large` (`0 < d`) and the product
bound `Σ_{b ∈ Z_L^d} e^{-c|a - b|₁} ≤ ((1 + e^{-c})/(1 - e^{-c}))^d` (uniform in `L`).  `GreenCond2_prob_famAvg` is Markov for the moment bound
`GreenCond2_famAvg_moment`.  `GreenCond2_avgK_le` bounds `⟨M𝒦⟩_a` from the offset averages of `𝒜'` and `𝔛` through the exact identity
`GreenMinor_avg_split`; `GreenCond2_avgA_le`, `GreenCond2_avgX_le` bound these averages by the family averages and `C₁ δ²` (§5). -/

section RowL1

/-- The one-dimensional torus sum: `Σ_{j ∈ Z_L} e^{-c|j|} ≤ (1 + e^{-c})/(1 - e^{-c})`, uniformly in `L`. -/
theorem GreenCond2_sum_zmod_exp (L : ℕ) [NeZero L] {c : ℝ} (hc : 0 < c) :
    ∑ j : ZMod L, Real.exp (-c * (zdist L j : ℝ)) ≤ (1 + Real.exp (-c)) / (1 - Real.exp (-c)) := by
  set r : ℝ := Real.exp (-c) with hr
  have hr0 : 0 < r := Real.exp_pos _
  have hr1 : r < 1 := by
    calc r < Real.exp 0 := Real.exp_lt_exp.2 (by linarith)
      _ = 1 := Real.exp_zero
  have h1r : 0 < 1 - r := by linarith
  have hpow : ∀ v : ℕ, Real.exp (-c * (v : ℝ)) = r ^ v := fun v => by
    rw [hr, ← Real.exp_nat_mul]; ring_nf
  have hpt : ∀ j : ZMod L, Real.exp (-c * (zdist L j : ℝ)) ≤ r ^ j.val + r ^ (L - j.val) := by
    intro j
    rw [hpow]
    unfold zdist
    rcases le_total j.val (L - j.val) with h | h
    · rw [min_eq_left h]; exact le_add_of_nonneg_right (pow_nonneg hr0.le _)
    · rw [min_eq_right h]; exact le_add_of_nonneg_left (pow_nonneg hr0.le _)
  have hinj : Function.Injective (fun j : ZMod L => j.val) := ZMod.val_injective L
  have h1 : ∑ j : ZMod L, (r ^ j.val + r ^ (L - j.val)) ≤ ∑ v ∈ Finset.range L, (r ^ v + r ^ (L - v)) := by
    have e : ∑ j : ZMod L, (r ^ j.val + r ^ (L - j.val)) = ∑ v ∈ Finset.univ.image (fun j : ZMod L => j.val), (r ^ v + r ^ (L - v)) :=
      (Finset.sum_image (f := fun v : ℕ => r ^ v + r ^ (L - v)) (s := (Finset.univ : Finset (ZMod L))) (g := fun j : ZMod L => j.val)
        (fun a _ b _ h => hinj h)).symm
    rw [e]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => by positivity)
    intro v hv
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hv
    exact Finset.mem_range.2 (ZMod.val_lt j)
  have hg : ∑ v ∈ Finset.range L, r ^ v ≤ 1 / (1 - r) := by
    rw [geom_sum_eq hr1.ne]
    have e : (r ^ L - 1) / (r - 1) = (1 - r ^ L) / (1 - r) := by
      rw [div_eq_div_iff (by linarith) (by linarith)]; ring
    rw [e]
    exact div_le_div_of_nonneg_right (by linarith [pow_nonneg hr0.le L]) h1r.le
  have hg2 : ∑ v ∈ Finset.range L, r ^ (L - v) = r * ∑ v ∈ Finset.range L, r ^ v := by
    have e : ∑ v ∈ Finset.range L, r ^ (L - v) = ∑ v ∈ Finset.range L, (fun w : ℕ => r ^ (w + 1)) (L - 1 - v) := by
      refine Finset.sum_congr rfl fun v hv => ?_
      have := Finset.mem_range.1 hv
      simp only
      congr 1
      omega
    rw [e, Finset.sum_range_reflect (fun w : ℕ => r ^ (w + 1)) L, Finset.mul_sum]
    exact Finset.sum_congr rfl fun v _ => by ring
  calc ∑ j : ZMod L, Real.exp (-c * (zdist L j : ℝ)) ≤ ∑ j : ZMod L, (r ^ j.val + r ^ (L - j.val)) := Finset.sum_le_sum fun j _ => hpt j
    _ ≤ ∑ v ∈ Finset.range L, (r ^ v + r ^ (L - v)) := h1
    _ = ∑ v ∈ Finset.range L, r ^ v + r * ∑ v ∈ Finset.range L, r ^ v := by rw [Finset.sum_add_distrib, hg2]
    _ ≤ 1 / (1 - r) + r * (1 / (1 - r)) := add_le_add hg (mul_le_mul_of_nonneg_left hg hr0.le)
    _ = (1 + r) / (1 - r) := by field_simp

/-- The torus sum `Σ_b e^{-c|a - b|₁} ≤ ((1 + e^{-c})/(1 - e^{-c}))^d`, for every `d`, uniformly in `L`. -/
theorem GreenCond2_sum_exp_le (d L : ℕ) [NeZero L] {c : ℝ} (hc : 0 < c) (a : Zd d L) :
    ∑ b : Zd d L, Real.exp (-c * (zdistD d L (a - b) : ℝ)) ≤ ((1 + Real.exp (-c)) / (1 - Real.exp (-c))) ^ d := by
  have e1 : ∑ b : Zd d L, Real.exp (-c * (zdistD d L (a - b) : ℝ)) = ∑ x : Zd d L, Real.exp (-c * (zdistD d L x : ℝ)) :=
    Equiv.sum_comp (Equiv.subLeft a) (fun x : Zd d L => Real.exp (-c * (zdistD d L x : ℝ)))
  have e2 : ∀ x : Zd d L, Real.exp (-c * (zdistD d L x : ℝ)) = ∏ i, Real.exp (-c * (zdist L (x i) : ℝ)) := by
    intro x
    rw [← Real.exp_sum]
    congr 1
    unfold zdistD
    push_cast
    rw [Finset.mul_sum]
  have e3 : ∑ x : Zd d L, ∏ i, Real.exp (-c * (zdist L (x i) : ℝ)) = ∏ i : Fin d, ∑ j : ZMod L, Real.exp (-c * (zdist L j : ℝ)) := by
    rw [Finset.prod_univ_sum (fun _ : Fin d => (Finset.univ : Finset (ZMod L))) (fun _ j => Real.exp (-c * (zdist L j : ℝ)))]
    rw [Fintype.piFinset_univ]
  rw [e1]
  simp only [e2]
  rw [e3, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  exact pow_le_pow_left₀ (Finset.sum_nonneg fun _ _ => (Real.exp_pos _).le) (GreenCond2_sum_zmod_exp L hc) d

/-- **The `ℓ¹` row of `M^{(B)}` for every `d ≥ 1`** (the decay `BAMB_decay_large`, `0 < d`, and the product bound on the torus; the merged
`baM_row_l1` is for `2 ≤ d`): `Σ_b |M_ab| ≤ c₀⁻¹ ((1 + e^{-c₀})/(1 - e^{-c₀}))^d`. -/
theorem GreenCond2_row_l1 (d L : ℕ) [NeZero L] (hL : 3 ≤ L) (hd : 0 < d) (Λ g κ E : ℝ) (m : ℂ) (hΛ : 0 < Λ) (hg : 0 < g)
    (hgΛ : g ≤ Λ) (hκ : 0 < κ) (hr : BAReal d L g κ E m) (a : Zd d L) :
    ∑ b, ‖BAMB d L g (E : ℂ) m a b‖ ≤
      (BAct_rate d Λ κ)⁻¹ * ((1 + Real.exp (-BAct_rate d Λ κ)) / (1 - Real.exp (-BAct_rate d Λ κ))) ^ d := by
  have hc := BAct_rate_pos d Λ κ hd hΛ hκ
  calc ∑ b, ‖BAMB d L g (E : ℂ) m a b‖ ≤ ∑ b : Zd d L, (BAct_rate d Λ κ)⁻¹ * Real.exp (-BAct_rate d Λ κ * (zdistD d L (a - b) : ℝ)) :=
        Finset.sum_le_sum fun b _ => BAMB_decay_large d L hL hd Λ g κ E m hΛ hg hgΛ hκ hr a b
    _ = (BAct_rate d Λ κ)⁻¹ * ∑ b : Zd d L, Real.exp (-BAct_rate d Λ κ * (zdistD d L (a - b) : ℝ)) := by rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (GreenCond2_sum_exp_le d L hc a) (inv_nonneg.2 hc.le)

end RowL1

section FamProb

/-- An offset average of `c`-bounded values is `c`-bounded. -/
theorem GreenCond2_norm_avg_le {d W : ℕ} [NeZero W] {f : Fin (W ^ d) → ℂ} {c : ℝ} (hc : ∀ o, ‖f o‖ ≤ c) : ‖GreenMinor_avg f‖ ≤ c := by
  unfold GreenMinor_avg
  have hW : (0 : ℝ) < ((W : ℝ) ^ d) := pow_pos (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne W)) d
  have hc0 : 0 ≤ c := (norm_nonneg _).trans (hc ⟨0, pow_pos (Nat.pos_of_ne_zero (NeZero.ne W)) d⟩)
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.2 hW.le)]
  calc ((W : ℝ) ^ d)⁻¹ * ‖∑ o, f o‖ ≤ ((W : ℝ) ^ d)⁻¹ * ∑ o : Fin (W ^ d), c :=
        mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (Finset.sum_le_sum fun o _ => hc o)) (inv_nonneg.2 hW.le)
    _ = c := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        field_simp

/-- The block weight turns a sum over the fine index into the offset average of the block. -/
theorem GreenCond2_sum_block {d L W : ℕ} [NeZero L] [NeZero W] (β : Zd d L) (f : Idx d L W → ℂ) :
    ∑ k : Idx d L W, (((if (split d L W k).1 = β then ((W : ℝ) ^ d)⁻¹ else 0 : ℝ) : ℂ)) * f k =
      (((W : ℝ) ^ d)⁻¹ : ℝ) * ∑ o : Fin (W ^ d), f ((splitEquiv d L W).symm (β, o)) := by
  rw [← Equiv.sum_comp (splitEquiv d L W).symm, Fintype.sum_prod_type]
  have h : ∀ (b : Zd d L) (o : Fin (W ^ d)), (split d L W ((splitEquiv d L W).symm (b, o))).1 = b := fun b o => by
    have := (splitEquiv d L W).apply_symm_apply (b, o)
    exact congrArg Prod.fst this
  simp only [h]
  rw [Finset.sum_eq_single β]
  · simp only [ite_true, Complex.ofReal_inv, Finset.mul_sum]
  · intro b _ hb
    simp [hb]
  · intro h; exact absurd (Finset.mem_univ β) h

/-- A finite sum of bounded measurable functions is bounded measurable. -/
theorem GreenCond2_bddMeas_sum {sz : Sizes d} {ι : Type*} (s : Finset ι) {f : ι → Sizes.SeqΩ sz → ℂ} (hf : ∀ i, BddMeas sz (f i)) :
    BddMeas sz fun ω => ∑ i ∈ s, f i ω := by
  classical
  choose C hC using fun i => (hf i).bdd
  exact ⟨Finset.measurable_sum _ fun i _ => (hf i).meas, ∑ i ∈ s, C i,
    fun ω => (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => hC i ω)⟩

/-- **Markov for the family average** (`GreenCond2_famAvg_moment`): with `μ = 2 (2p) (2^{2p-1} ρ B)`,
`P(|Σ_k T_k Q_k Y_k| ≥ W_τ μ) ≤ W_τ^{-2p}`, for `W_τ ≥ 1`, `p ≥ 1`. -/
theorem GreenCond2_prob_famAvg {d : ℕ} {sz : Sizes d} {n : ℕ} {A : Finset (Idx d (sz.L n) (sz.W n))} {Y : Idx d (sz.L n) (sz.W n) → sz.SeqΩ → ℂ}
    (hY : ∀ k, BddMeas sz (Y k)) (hYd : ∀ k, FinDep sz (Y k)) {B ρ c : ℝ} {M K p : ℕ} {T : Idx d (sz.L n) (sz.W n) → ℝ}
    (hg : GreenMinor_famGain sz n A Y B ρ M K) (hM : 2 * p ≤ M) (hK : 2 * p ≤ K) (hρ1 : ρ ≤ 1) (hcρ : c ≤ ρ ^ 2)
    (hw : BoundedWeight T c A) (hp : 2 * p ≤ A.card) (hp1 : 1 ≤ p) {Wτ : ℝ} (hWτ : 1 ≤ Wτ) (hρB : 0 < ρ * B) :
    (Sizes.seqP sz).real {ω | Wτ * (2 * (2 * p) * (2 ^ (2 * p - 1) * ρ * B)) ≤ ‖∑ k, (T k : ℂ) * qRow sz n k (Y k) ω‖} ≤ (1 / Wτ) ^ (2 * p) := by
  have hmom := GreenCond2_famAvg_moment (p := p) hY hYd hg hM hK hρ1 hcρ hw hp
  have hS : BddMeas sz fun ω => ∑ k, (T k : ℂ) * qRow sz n k (Y k) ω :=
    GreenCond2_bddMeas_sum _ fun k => (bddMeas_const sz (T k : ℂ)).mul ((hY k).qRow k)
  obtain ⟨C, hC⟩ := hS.bdd
  set S : sz.SeqΩ → ℂ := fun ω => ∑ k, (T k : ℂ) * qRow sz n k (Y k) ω with hSdef
  have hf : Integrable (fun ω => ‖S ω‖ ^ (2 * p)) (Sizes.seqP sz) := by
    refine Integrable.of_bound ((hS.meas.norm.pow_const _).aestronglyMeasurable) (C ^ (2 * p)) (Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact pow_le_pow_left₀ (norm_nonneg _) (hC ω) _
  set μ : ℝ := 2 * (2 * p) * (2 ^ (2 * p - 1) * ρ * B) with hμ
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp1
  have hbase : 0 < (2 : ℝ) ^ (2 * p - 1) * ρ * B := by rw [mul_assoc]; exact mul_pos (by positivity) hρB
  have hμ0 : 0 < μ := by
    rw [hμ]; exact mul_pos (by positivity) hbase
  have hlam0 : 0 < Wτ * μ := by positivity
  have hmark := mul_meas_ge_le_integral_of_nonneg (μ := Sizes.seqP sz) (f := fun ω => ‖S ω‖ ^ (2 * p))
    (Eventually.of_forall fun ω => by positivity) hf ((Wτ * μ) ^ (2 * p))
  have hsub : {ω | Wτ * μ ≤ ‖S ω‖} ⊆ {ω | (Wτ * μ) ^ (2 * p) ≤ ‖S ω‖ ^ (2 * p)} :=
    fun ω hω => pow_le_pow_left₀ hlam0.le hω _
  have hmono := measureReal_mono (μ := Sizes.seqP sz) hsub (measure_ne_top _ _)
  have hF : ∫ ω, ‖S ω‖ ^ (2 * p) ∂(Sizes.seqP sz) ≤ ((2 * p : ℝ) + 1) * (2 * p : ℝ) ^ (2 * p) * ((2 : ℝ) ^ (2 * p - 1) * ρ * B) ^ (2 * p) := by
    refine hmom.trans (le_of_eq ?_)
    rw [mul_assoc (2 ^ (2 * p - 1)) ρ B]
  have hpos : 0 < (Wτ * μ) ^ (2 * p) := by positivity
  have h2p : ((2 * p : ℝ) + 1) ≤ (2 : ℝ) ^ (2 * p) := by
    have := Nat.lt_two_pow_self (n := 2 * p)
    have h' : 2 * p + 1 ≤ 2 ^ (2 * p) := this
    exact_mod_cast h'
  have hkey : (Sizes.seqP sz).real {ω | Wτ * μ ≤ ‖S ω‖} ≤ (1 / Wτ) ^ (2 * p) := by
    have h1 : (Sizes.seqP sz).real {ω | Wτ * μ ≤ ‖S ω‖} ≤ ((2 * p : ℝ) + 1) * (2 * p : ℝ) ^ (2 * p) * ((2 : ℝ) ^ (2 * p - 1) * ρ * B) ^ (2 * p) / (Wτ * μ) ^ (2 * p) := by
      rw [le_div_iff₀ hpos]
      calc (Sizes.seqP sz).real {ω | Wτ * μ ≤ ‖S ω‖} * (Wτ * μ) ^ (2 * p) ≤ (Sizes.seqP sz).real {ω | (Wτ * μ) ^ (2 * p) ≤ ‖S ω‖ ^ (2 * p)} * (Wτ * μ) ^ (2 * p) :=
            mul_le_mul_of_nonneg_right hmono hpos.le
        _ = (Wτ * μ) ^ (2 * p) * (Sizes.seqP sz).real {ω | (Wτ * μ) ^ (2 * p) ≤ ‖S ω‖ ^ (2 * p)} := by ring
        _ ≤ _ := hmark.trans hF
    refine h1.trans ?_
    rw [div_le_iff₀ hpos]
    have e : (Wτ * μ) ^ (2 * p) = Wτ ^ (2 * p) * (2 ^ (2 * p) * (2 * p : ℝ) ^ (2 * p) * ((2 : ℝ) ^ (2 * p - 1) * ρ * B) ^ (2 * p)) := by
      rw [hμ, mul_pow, mul_pow, mul_pow]
    rw [e, one_div, inv_pow]
    have hW2 : 0 < Wτ ^ (2 * p) := by positivity
    have hX : 0 < (2 * p : ℝ) ^ (2 * p) * ((2 : ℝ) ^ (2 * p - 1) * ρ * B) ^ (2 * p) :=
      mul_pos (by positivity) (pow_pos hbase _)
    calc ((2 * p : ℝ) + 1) * (2 * p : ℝ) ^ (2 * p) * ((2 : ℝ) ^ (2 * p - 1) * ρ * B) ^ (2 * p)
        = ((2 * p : ℝ) + 1) * ((2 * p : ℝ) ^ (2 * p) * ((2 : ℝ) ^ (2 * p - 1) * ρ * B) ^ (2 * p)) := by ring
      _ ≤ 2 ^ (2 * p) * ((2 * p : ℝ) ^ (2 * p) * ((2 : ℝ) ^ (2 * p - 1) * ρ * B) ^ (2 * p)) := mul_le_mul_of_nonneg_right h2p hX.le
      _ = (Wτ ^ (2 * p))⁻¹ * (Wτ ^ (2 * p) * (2 ^ (2 * p) * (2 * p : ℝ) ^ (2 * p) * ((2 : ℝ) ^ (2 * p - 1) * ρ * B) ^ (2 * p))) := by
          field_simp
  exact hkey

end FamProb

section AvgBounds
variable {d : ℕ} {sz : Sizes d} {z : ℕ → ℂ} {n : ℕ} {t : ℝ}

/-- **The deterministic bound of `⟨M𝒦⟩_a` from the offset averages of `𝒜'` and `𝔛`**: with `Θ = (2 + c_A) δ² + Λ_A + Λ_X`,
`‖⟨M𝒦⟩_a‖ ≤ ρ_row Θ`, where the first term is `≤ δ²`, the third `≤ (c_A + 1) δ²` (the pointwise bound `‖A_u‖ ≤ c_A δ`, `|t v̄| ≤ δ`),
the second `≤ Λ_A` (`|M_{b'a}| ≤ 1`) and the fourth `≤ Λ_X` (`𝔛_{uu} = 0`). -/
theorem GreenCond2_avgK_le {κ ε 𝔠 𝔡 : ℝ} (hκ : 0 < κ) (h : BAFlow sz κ ε 𝔠 𝔡 z) (ht0 : 0 ≤ t) (ht : t ≤ BAflowT0 sz z n)
    (hg0 : 0 ≤ BAflowLam0 sz z n) (ht1 : t ≤ 1) {δ ΛA ΛX ρr : ℝ} (hδ0 : 0 ≤ δ) (hδ2 : δ ≤ κ / 2) (hΛA : 0 ≤ ΛA) (hΛX : 0 ≤ ΛX)
    (ω : sz.SeqΩ) (hG : ∀ x y, ‖GreenCore_Gc sz z n t ω x y - GreenCore_Mc sz z n x y‖ ≤ δ) (hρ0 : 0 ≤ ρr)
    (hρ : ∑ b, ‖BAMB d (sz.L n) (BAflowLam0 sz z n) (BAflowEs sz z n : ℂ) (GreenCond_m sz z n) a b‖ ≤ ρr)
    (hA : ∀ b' : Zd d (sz.L n), ‖GreenMinor_avg (fun o : Fin (sz.W n ^ d) =>
      GreenCore_Arow (GreenCore_Gc sz z n t ω) (GreenCore_Xc sz n t ω) (GreenCore_Dc sz z n) t (GreenCond_m sz z n) (b', o) +
        (t : ℂ) * GreenCore_vbar (GreenCore_Gc sz z n t ω) (GreenCore_Mc sz z n) b')‖ ≤ ΛA)
    (hX : ∀ b' : Zd d (sz.L n), b' ≠ a → ‖GreenMinor_avg (fun o : Fin (sz.W n ^ d) =>
      GreenCore_Xrow (GreenCore_Gc sz z n t ω) (GreenCore_Xc sz n t ω) (b', o) (a, o))‖ ≤ ΛX) :
    ‖GreenMinor_avgK (GreenCore_Gc sz z n t ω) (GreenCore_Mc sz z n) (GreenCore_Xc sz n t ω) (GreenCore_Dc sz z n)
        (BAMB d (sz.L n) (BAflowLam0 sz z n) (BAflowEs sz z n : ℂ) (GreenCond_m sz z n)) t (GreenCond_m sz z n) a‖ ≤
      ρr * ((2 + GreenCond_cA d κ (BAflowLam0 sz z n) ‖GreenCond_s sz z n‖) * δ ^ 2 + ΛA + ΛX) := by
  have dat := GreenCond_data hκ sz h n ht0 ht hg0
  have hcA0 := GreenCond_cA_nonneg (d := d) (κ := κ) hg0 (norm_nonneg (GreenCond_s sz z n))
  have hMb1 : ∀ b' a' : Zd d (sz.L n), ‖BAMB d (sz.L n) (BAflowLam0 sz z n) (BAflowEs sz z n : ℂ) (GreenCond_m sz z n) b' a'‖ ≤ 1 := by
    intro b' a'
    have := dat.hMle (b', ⟨0, pow_pos (sz.W_pos n) d⟩) (a', ⟨0, pow_pos (sz.W_pos n) d⟩)
    rw [dat.hM] at this
    simpa using this
  have hsplit := GreenMinor_avg_split (G := GreenCore_Gc sz z n t ω) (X := GreenCore_Xc sz n t ω) (D := GreenCore_Dc sz z n) (t := t)
    (m := GreenCond_m sz z n) dat.hM a
  rw [hsplit]
  set Θ : ℝ := (2 + GreenCond_cA d κ (BAflowLam0 sz z n) ‖GreenCond_s sz z n‖) * δ ^ 2 + ΛA + ΛX with hΘ
  have hΘ0 : 0 ≤ Θ := by rw [hΘ]; positivity
  refine (norm_sum_le _ _).trans ?_
  refine le_trans (Finset.sum_le_sum fun b' _ => ?_) (?_ : ∑ b', ‖BAMB d (sz.L n) (BAflowLam0 sz z n) (BAflowEs sz z n : ℂ) (GreenCond_m sz z n) a b'‖ * Θ ≤ ρr * Θ)
  · rw [norm_mul]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    -- the four terms
    have hv : ‖GreenCore_vbar (GreenCore_Gc sz z n t ω) (GreenCore_Mc sz z n) b'‖ ≤ δ := by
      unfold GreenCore_vbar
      refine GreenCond2_norm_avg_le (f := fun o : Fin (sz.W n ^ d) => GreenCore_Gc sz z n t ω (b', o) (b', o) - GreenCore_Mc sz z n (b', o) (b', o)) (fun o => hG _ _)
    have hΔ : ‖GreenMinor_avg (fun o : Fin (sz.W n ^ d) => GreenCore_Gc sz z n t ω (b', o) (a, o) - GreenCore_Mc sz z n (b', o) (a, o))‖ ≤ δ :=
      GreenCond2_norm_avg_le (fun o => hG _ _)
    have hAp : ∀ o : Fin (sz.W n ^ d), ‖GreenCore_Arow (GreenCore_Gc sz z n t ω) (GreenCore_Xc sz n t ω) (GreenCore_Dc sz z n) t (GreenCond_m sz z n) (b', o)‖ ≤
        GreenCond_cA d κ (BAflowLam0 sz z n) ‖GreenCond_s sz z n‖ * δ :=
      fun o => (GreenCond_pointwise_A sz z n t hκ h ht0 ht hg0 hδ0 hδ2 ω hG (b', o)).1
    have hAp' : ∀ o : Fin (sz.W n ^ d), ‖GreenCore_Arow (GreenCore_Gc sz z n t ω) (GreenCore_Xc sz n t ω) (GreenCore_Dc sz z n) t (GreenCond_m sz z n) (b', o) +
        (t : ℂ) * GreenCore_vbar (GreenCore_Gc sz z n t ω) (GreenCore_Mc sz z n) b'‖ ≤ (GreenCond_cA d κ (BAflowLam0 sz z n) ‖GreenCond_s sz z n‖ + 1) * δ := by
      intro o
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ht0]
      have h1 := hAp o
      have h2 : t * ‖GreenCore_vbar (GreenCore_Gc sz z n t ω) (GreenCore_Mc sz z n) b'‖ ≤ 1 * δ :=
        mul_le_mul ht1 hv (norm_nonneg _) zero_le_one
      nlinarith
    have t1 : ‖(t : ℂ) * GreenCore_vbar (GreenCore_Gc sz z n t ω) (GreenCore_Mc sz z n) b' *
        GreenMinor_avg (fun o : Fin (sz.W n ^ d) => GreenCore_Gc sz z n t ω (b', o) (a, o) - GreenCore_Mc sz z n (b', o) (a, o))‖ ≤ δ ^ 2 := by
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg ht0]
      calc t * ‖GreenCore_vbar (GreenCore_Gc sz z n t ω) (GreenCore_Mc sz z n) b'‖ * ‖GreenMinor_avg _‖ ≤ 1 * δ * δ :=
            mul_le_mul (mul_le_mul ht1 hv (norm_nonneg _) zero_le_one) hΔ (norm_nonneg _) (by positivity)
        _ = δ ^ 2 := by ring
    have t2 : ‖BAMB d (sz.L n) (BAflowLam0 sz z n) (BAflowEs sz z n : ℂ) (GreenCond_m sz z n) b' a *
        GreenMinor_avg (fun o : Fin (sz.W n ^ d) => GreenCore_Arow (GreenCore_Gc sz z n t ω) (GreenCore_Xc sz n t ω) (GreenCore_Dc sz z n) t (GreenCond_m sz z n) (b', o) +
          (t : ℂ) * GreenCore_vbar (GreenCore_Gc sz z n t ω) (GreenCore_Mc sz z n) b')‖ ≤ ΛA := by
      rw [norm_mul]
      calc _ ≤ 1 * ΛA := mul_le_mul (hMb1 _ _) (hA b') (norm_nonneg _) zero_le_one
        _ = ΛA := one_mul _
    have t3 : ‖GreenMinor_avg (fun o : Fin (sz.W n ^ d) => (GreenCore_Arow (GreenCore_Gc sz z n t ω) (GreenCore_Xc sz n t ω) (GreenCore_Dc sz z n) t (GreenCond_m sz z n) (b', o) +
        (t : ℂ) * GreenCore_vbar (GreenCore_Gc sz z n t ω) (GreenCore_Mc sz z n) b') *
          (GreenCore_Gc sz z n t ω (b', o) (a, o) - GreenCore_Mc sz z n (b', o) (a, o)))‖ ≤ (GreenCond_cA d κ (BAflowLam0 sz z n) ‖GreenCond_s sz z n‖ + 1) * δ ^ 2 := by
      refine (GreenCond2_norm_avg_le (c := (GreenCond_cA d κ (BAflowLam0 sz z n) ‖GreenCond_s sz z n‖ + 1) * δ * δ) fun o => ?_).trans (le_of_eq (by ring))
      rw [norm_mul]
      exact mul_le_mul (hAp' o) (hG _ _) (norm_nonneg _) (by positivity)
    have t4 : ‖GreenMinor_avg (fun o : Fin (sz.W n ^ d) => GreenCore_Xrow (GreenCore_Gc sz z n t ω) (GreenCore_Xc sz n t ω) (b', o) (a, o))‖ ≤ ΛX := by
      by_cases hba : b' = a
      · subst hba
        have h0 : ∀ o : Fin (sz.W n ^ d), GreenCore_Xrow (GreenCore_Gc sz z n t ω) (GreenCore_Xc sz n t ω) (b', o) (b', o) = 0 := by
          intro o
          unfold GreenCore_Xrow
          refine Finset.sum_eq_zero fun v _ => ?_
          rw [GreenCore_minor_right (GreenCond_G_diag_ne sz z n t hκ h ht0 ht ω _), mul_zero]
        simp only [h0]
        unfold GreenMinor_avg
        simp [hΛX]
      · exact hX b' hba
    have e : ‖(t : ℂ) * GreenCore_vbar (GreenCore_Gc sz z n t ω) (GreenCore_Mc sz z n) b' *
          GreenMinor_avg (fun o : Fin (sz.W n ^ d) => GreenCore_Gc sz z n t ω (b', o) (a, o) - GreenCore_Mc sz z n (b', o) (a, o)) -
        BAMB d (sz.L n) (BAflowLam0 sz z n) (BAflowEs sz z n : ℂ) (GreenCond_m sz z n) b' a *
          GreenMinor_avg (fun o : Fin (sz.W n ^ d) => GreenCore_Arow (GreenCore_Gc sz z n t ω) (GreenCore_Xc sz n t ω) (GreenCore_Dc sz z n) t (GreenCond_m sz z n) (b', o) +
            (t : ℂ) * GreenCore_vbar (GreenCore_Gc sz z n t ω) (GreenCore_Mc sz z n) b') -
        GreenMinor_avg (fun o : Fin (sz.W n ^ d) => (GreenCore_Arow (GreenCore_Gc sz z n t ω) (GreenCore_Xc sz n t ω) (GreenCore_Dc sz z n) t (GreenCond_m sz z n) (b', o) +
          (t : ℂ) * GreenCore_vbar (GreenCore_Gc sz z n t ω) (GreenCore_Mc sz z n) b') *
            (GreenCore_Gc sz z n t ω (b', o) (a, o) - GreenCore_Mc sz z n (b', o) (a, o))) -
        GreenMinor_avg (fun o : Fin (sz.W n ^ d) => GreenCore_Xrow (GreenCore_Gc sz z n t ω) (GreenCore_Xc sz n t ω) (b', o) (a, o))‖ ≤ Θ := by
      refine (norm_sub_le _ _).trans ?_
      refine (add_le_add ((norm_sub_le _ _).trans (add_le_add ((norm_sub_le _ _).trans (add_le_add t1 t2)) t3)) t4).trans ?_
      rw [hΘ]; nlinarith
    exact e
  · exact mul_le_mul_of_nonneg_right hρ hΘ0 |>.trans' (by rw [← Finset.sum_mul])

/-- **The offset average of `𝒜'` against the family average of `Q_u Y^A_u`**: off the bad row slices, the difference is `≤ C₁ δ²`. -/
theorem GreenCond2_avgA_le {κ ε 𝔠 𝔡 : ℝ} (hκ : 0 < κ) (h : BAFlow sz κ ε 𝔠 𝔡 z) (ht0 : 0 ≤ t) (ht : t ≤ BAflowT0 sz z n)
    (hg0 : 0 ≤ BAflowLam0 sz z n) (ht1 : t ≤ 1) {δ ε' : ℝ} (hδ0 : 0 ≤ δ) (hδ2 : δ ≤ κ / 2) (hε' : 0 < ε')
    (ω : (GreenCond_sz0 sz).SeqΩ) (hG : ∀ x y, ‖GreenCore_Gc sz z n t ω x y - GreenCore_Mc sz z n x y‖ ≤ δ)
    (hwd : (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ δ ^ 2)
    (hslice : ∀ u : Idx d (sz.L n) (sz.W n), (Sizes.seqP (GreenCond_sz0 sz)).real (rowSlice (GreenCond_sz0 sz) n u (GreenCond_badBase sz z n t δ) ω) ≤ ε')
    (hsq : Real.sqrt (ε' * GreenCond_QA sz z n t) ≤ δ ^ 2) (b' : Zd d (sz.L n)) :
    ‖GreenMinor_avg (fun o : Fin (sz.W n ^ d) =>
        GreenCore_Arow (GreenCore_Gc sz z n t ω) (GreenCore_Xc sz n t ω) (GreenCore_Dc sz z n) t (GreenCond_m sz z n) (b', o) +
          (t : ℂ) * GreenCore_vbar (GreenCore_Gc sz z n t ω) (GreenCore_Mc sz z n) b')‖ ≤
      ‖∑ k : Idx d (sz.L n) (sz.W n), (((if (split d (sz.L n) (sz.W n) k).1 = b' then (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ else 0 : ℝ) : ℂ)) *
          qRow (GreenCond_sz0 sz) n k (fun σ => GreenCond_ΦA sz z n k (GreenCore_Gc sz z n t σ)) ω‖ +
        GreenCond_C1 d κ (BAflowLam0 sz z n) ‖GreenCond_s sz z n‖ * δ ^ 2 := by
  rw [GreenCond2_sum_block b' (fun k => qRow (GreenCond_sz0 sz) n k (fun σ => GreenCond_ΦA sz z n k (GreenCore_Gc sz z n t σ)) ω)]
  set e := splitEquiv d (sz.L n) (sz.W n) with he
  set q : Fin (sz.W n ^ d) → ℂ := fun o => qRow (GreenCond_sz0 sz) n (e.symm (b', o))
    (fun σ => GreenCond_ΦA sz z n (e.symm (b', o)) (GreenCore_Gc sz z n t σ)) ω with hq
  set f : Fin (sz.W n ^ d) → ℂ := fun o => GreenCore_Arow (GreenCore_Gc sz z n t ω) (GreenCore_Xc sz n t ω) (GreenCore_Dc sz z n) t (GreenCond_m sz z n) (b', o) +
          (t : ℂ) * GreenCore_vbar (GreenCore_Gc sz z n t ω) (GreenCore_Mc sz z n) b' with hf
  have hr : ‖GreenMinor_avg (fun o => f o - q o)‖ ≤ GreenCond_C1 d κ (BAflowLam0 sz z n) ‖GreenCond_s sz z n‖ * δ ^ 2 := by
    refine GreenCond2_norm_avg_le fun o => ?_
    have := GreenCond_E_A_le hκ h ht0 ht hg0 ht1 hδ0 hδ2 hε' (e.symm (b', o)) ω hG hwd (hslice _) hsq
    simpa only [he, Equiv.apply_symm_apply] using this
  have hsub : GreenMinor_avg f = GreenMinor_avg (fun o => f o - q o) + GreenMinor_avg q := by
    rw [GreenMinor_avg_sub]; ring
  rw [hsub]
  refine (norm_add_le _ _).trans ?_
  rw [add_comm]
  exact add_le_add le_rfl hr

/-- **The offset average of `𝔛_{(b',o),(a,o)}` against the family average of `-Q_u Y^X_u`** (`b' ≠ a`): off the bad row slices the difference
is `≤ C₁ δ²`. -/
theorem GreenCond2_avgX_le {κ ε 𝔠 𝔡 : ℝ} (hκ : 0 < κ) (h : BAFlow sz κ ε 𝔠 𝔡 z) (ht0 : 0 ≤ t) (ht : t ≤ BAflowT0 sz z n)
    (hg0 : 0 ≤ BAflowLam0 sz z n) (ht1 : t ≤ 1) {δ ε' : ℝ} (hδ0 : 0 ≤ δ) (hδ2 : δ ≤ κ / 2) (hε' : 0 < ε')
    (ω : (GreenCond_sz0 sz).SeqΩ) (hG : ∀ x y, ‖GreenCore_Gc sz z n t ω x y - GreenCore_Mc sz z n x y‖ ≤ δ)
    (hslice : ∀ u : Idx d (sz.L n) (sz.W n), (Sizes.seqP (GreenCond_sz0 sz)).real (rowSlice (GreenCond_sz0 sz) n u (GreenCond_badBase sz z n t δ) ω) ≤ ε')
    (hsq : Real.sqrt (ε' * GreenCond_QX sz z n t) ≤ δ ^ 2) (a b' : Zd d (sz.L n)) (hba : b' ≠ a) :
    ‖GreenMinor_avg (fun o : Fin (sz.W n ^ d) =>
        GreenCore_Xrow (GreenCore_Gc sz z n t ω) (GreenCore_Xc sz n t ω) (b', o) (a, o))‖ ≤
      ‖∑ k : Idx d (sz.L n) (sz.W n), (((if (split d (sz.L n) (sz.W n) k).1 = b' then (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ else 0 : ℝ) : ℂ)) *
          qRow (GreenCond_sz0 sz) n k (fun σ => GreenCond_ΦX sz z n a k (GreenCore_Gc sz z n t σ)) ω‖ +
        GreenCond_C1 d κ (BAflowLam0 sz z n) ‖GreenCond_s sz z n‖ * δ ^ 2 := by
  rw [GreenCond2_sum_block b' (fun k => qRow (GreenCond_sz0 sz) n k (fun σ => GreenCond_ΦX sz z n a k (GreenCore_Gc sz z n t σ)) ω)]
  set e := splitEquiv d (sz.L n) (sz.W n) with he
  set q : Fin (sz.W n ^ d) → ℂ := fun o => qRow (GreenCond_sz0 sz) n (e.symm (b', o))
    (fun σ => GreenCond_ΦX sz z n a (e.symm (b', o)) (GreenCore_Gc sz z n t σ)) ω with hq
  set f : Fin (sz.W n ^ d) → ℂ := fun o => GreenCore_Xrow (GreenCore_Gc sz z n t ω) (GreenCore_Xc sz n t ω) (b', o) (a, o) with hf
  have hr : ‖GreenMinor_avg (fun o => f o + q o)‖ ≤ GreenCond_C1 d κ (BAflowLam0 sz z n) ‖GreenCond_s sz z n‖ * δ ^ 2 := by
    refine GreenCond2_norm_avg_le fun o => ?_
    have hα : a ≠ (e (e.symm (b', o))).1 := by rw [Equiv.apply_symm_apply]; exact hba.symm
    have := GreenCond_E_X_le hκ h ht0 ht hg0 ht1 hδ0 hδ2 hε' (e.symm (b', o)) hα ω hG (hslice _) hsq
    simpa only [he, Equiv.apply_symm_apply] using this
  have hsub : GreenMinor_avg f = GreenMinor_avg (fun o => f o + q o) - GreenMinor_avg q := by
    rw [← GreenMinor_avg_sub]
    congr 1
    funext o; ring
  rw [hsub]
  refine (norm_sub_le _ _).trans ?_
  rw [add_comm]
  exact add_le_add le_rfl hr

end AvgBounds

/-! ## 7. The exceptional set of `BAFAav` and the bounds off and on it

`GreenCond2_Bad`: the base step `badStep` of the tower over the complement of `{‖G_t - M‖_max ≤ δ}`, together with the family averages
`Σ_k W^{-d} 1_{k ∈ [β]} Q_k Y_k` of size `≥ lam`.  Off it (`GreenCond2_FAav_det`) `‖⟨M𝒦⟩_a‖ ≤ ρ_row ((2 + c_A + 2 C₁) δ² + 2 lam)`; on it
(`GreenCond2_FAav_prob`) `P ≤ P(badStep) + (N + N²) W_τ^{-2p}` (Markov for the moment bound, the union over the blocks `β` and the pairs
`β ≠ α`, `#Z_L^d ≤ N`). -/

section FAav
variable {d : ℕ} {sz : Sizes d} {z : ℕ → ℂ} {n : ℕ} {t : ℝ}

/-- The family average `Σ_k W^{-d} 1_{k ∈ [β]} Q_k Y^A_k` of the block `β`. -/
def GreenCond2_SA (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ) (t : ℝ) (β : Zd d (sz.L n)) (ω : (sz.withLam 0).SeqΩ) : ℂ :=
  ∑ k : Idx d (sz.L n) (sz.W n), (((if (split d (sz.L n) (sz.W n) k).1 = β then (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ else 0 : ℝ)) : ℂ) *
    qRow (sz.withLam 0) n k (fun σ => GreenCond_ΦA sz z n k (GreenCore_Gc sz z n t σ)) ω

/-- The family average `Σ_k W^{-d} 1_{k ∈ [β]} Q_k Y^X_{k,(α,o(k))}` of the block `β` against the block `α`. -/
def GreenCond2_SX (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ) (t : ℝ) (β α : Zd d (sz.L n)) (ω : (sz.withLam 0).SeqΩ) : ℂ :=
  ∑ k : Idx d (sz.L n) (sz.W n), (((if (split d (sz.L n) (sz.W n) k).1 = β then (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ else 0 : ℝ)) : ℂ) *
    qRow (sz.withLam 0) n k (fun σ => GreenCond_ΦX sz z n α k (GreenCore_Gc sz z n t σ)) ω

/-- **The exceptional set of the averaged law**: the tower base step `badStep` over the complement of `{‖G_t - M‖_max ≤ δ}`, and the
family averages of size `≥ lam`. -/
def GreenCond2_Bad (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ) (t : ℝ) (ε' δ lam : ℝ) : Set (sz.withLam 0).SeqΩ :=
  badStep (sz.withLam 0) n ε' (GreenCond_badBase sz z n t δ) ∪ (⋃ β : Zd d (sz.L n), {ω | lam ≤ ‖GreenCond2_SA sz z n t β ω‖}) ∪
    ⋃ p : {p : Zd d (sz.L n) × Zd d (sz.L n) // p.1 ≠ p.2}, {ω | lam ≤ ‖GreenCond2_SX sz z n t p.1.1 p.1.2 ω‖}

/-- **The deterministic bound of `⟨M𝒦⟩_a` off the exceptional set**: `‖⟨M𝒦⟩_a‖ ≤ ρ_row ((2 + c_A + 2 C₁) δ² + 2 lam)`. -/
theorem GreenCond2_FAav_det {κ ε 𝔠 𝔡 : ℝ} (hκ : 0 < κ) (h : BAFlow sz κ ε 𝔠 𝔡 z) (ht0 : 0 ≤ t) (ht : t ≤ BAflowT0 sz z n)
    (hg0 : 0 ≤ BAflowLam0 sz z n) (ht1 : t ≤ 1) {δ ε' lam ρr : ℝ} (hδ0 : 0 ≤ δ) (hδ2 : δ ≤ κ / 2) (hε' : 0 < ε')
    (hwd : (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ δ ^ 2) (hsqA : Real.sqrt (ε' * GreenCond_QA sz z n t) ≤ δ ^ 2)
    (hsqX : Real.sqrt (ε' * GreenCond_QX sz z n t) ≤ δ ^ 2) (hlam : 0 ≤ lam) (hρ0 : 0 ≤ ρr)
    (hρ : ∀ a, ∑ b, ‖BAMB d (sz.L n) (BAflowLam0 sz z n) (BAflowEs sz z n : ℂ) (GreenCond_m sz z n) a b‖ ≤ ρr)
    (ω : (sz.withLam 0).SeqΩ) (hω : ω ∉ GreenCond2_Bad sz z n t ε' δ lam) (a : Zd d (sz.L n)) :
    ‖GreenMinor_avgK (GreenCore_Gc sz z n t ω) (GreenCore_Mc sz z n) (GreenCore_Xc sz n t ω) (GreenCore_Dc sz z n)
        (BAMB d (sz.L n) (BAflowLam0 sz z n) (BAflowEs sz z n : ℂ) (GreenCond_m sz z n)) t (GreenCond_m sz z n) a‖ ≤
      ρr * ((2 + GreenCond_cA d κ (BAflowLam0 sz z n) ‖GreenCond_s sz z n‖) * δ ^ 2 +
        (lam + GreenCond_C1 d κ (BAflowLam0 sz z n) ‖GreenCond_s sz z n‖ * δ ^ 2) +
        (lam + GreenCond_C1 d κ (BAflowLam0 sz z n) ‖GreenCond_s sz z n‖ * δ ^ 2)) := by
  have hs0 := norm_nonneg (GreenCond_s sz z n)
  have hC1 : 0 ≤ GreenCond_C1 d κ (BAflowLam0 sz z n) ‖GreenCond_s sz z n‖ := by
    unfold GreenCond_C1
    have := GreenCond_cA_nonneg (d := d) (κ := κ) hg0 hs0
    have := GreenCond_cX_nonneg (d := d) hκ hg0 hs0 (s := ‖GreenCond_s sz z n‖)
    positivity
  simp only [GreenCond2_Bad, Set.mem_union, Set.mem_iUnion, Set.mem_ofPred_eq, not_or, not_exists, not_le] at hω
  obtain ⟨⟨hstep, hA⟩, hX⟩ := hω
  have hbase : ω ∉ GreenCond_badBase sz z n t δ := fun h' => hstep (subset_badStep _ _ _ _ h')
  have hG := GreenCond_good_of_notMem_badBase sz z n t δ hbase
  have hslice : ∀ u : Idx d (sz.L n) (sz.W n), (Sizes.seqP (GreenCond_sz0 sz)).real (rowSlice (GreenCond_sz0 sz) n u (GreenCond_badBase sz z n t δ) ω) ≤ ε' :=
    fun u => measureReal_rowSlice_le_of_notMem_badStep (sz := sz.withLam 0) (n := n) u hstep
  refine GreenCond2_avgK_le hκ h ht0 ht hg0 ht1 hδ0 hδ2 (by positivity) (by positivity) ω hG hρ0 (hρ a) ?_ ?_
  · intro b'
    exact (GreenCond2_avgA_le hκ h ht0 ht hg0 ht1 hδ0 hδ2 hε' ω hG hwd hslice hsqA b').trans (add_le_add (hA b').le le_rfl)
  · intro b' hba
    exact (GreenCond2_avgX_le hκ h ht0 ht hg0 ht1 hδ0 hδ2 hε' ω hG hslice hsqX a b' hba).trans
      (add_le_add (hX ⟨(b', a), hba⟩).le le_rfl)

theorem GreenCond2_exists_ne {L : ℕ} (hd : 1 ≤ d) (hL : 2 ≤ L) (β : Zd d L) : ∃ α : Zd d L, α ≠ β := by
  refine ⟨β + fun _ => 1, fun h => ?_⟩
  have h1 := congrFun h ⟨0, hd⟩
  simp only [Pi.add_apply, add_eq_left] at h1
  have h2 : ((1 : ℕ) : ZMod L) = 0 := by exact_mod_cast h1
  rw [ZMod.natCast_eq_zero_iff] at h2
  have := Nat.le_of_dvd one_pos h2
  omega

theorem GreenCond2_card_Zd_le (sz : Sizes d) (n : ℕ) : (Fintype.card (Zd d (sz.L n)) : ℝ) ≤ (sz.size n : ℝ) := by
  have h1 : Fintype.card (Zd d (sz.L n)) = (sz.L n) ^ d := by simp [Zd, ZMod.card]
  rw [h1]
  have h2 : (sz.L n) ^ d ≤ (sz.W n * sz.L n) ^ d :=
    Nat.pow_le_pow_left (Nat.le_mul_of_pos_left _ (sz.W_pos n)) d
  exact_mod_cast h2

theorem GreenCond2_finDep {κ ε 𝔠 𝔡 : ℝ} (hκ : 0 < κ) (h : BAFlow sz κ ε 𝔠 𝔡 z) (ht0 : 0 ≤ t) (ht : t ≤ BAflowT0 sz z n)
    (Φ : Matrix (Vtx d (sz.L n) (sz.W n)) (Vtx d (sz.L n) (sz.W n)) ℂ → ℂ) :
    FinDep (sz.withLam 0) (fun ω => Φ (GreenCore_Gc sz z n t ω)) := by
  obtain ⟨I, -, hI⟩ := GreenCond_finDepOffRows sz z n t ∅ Φ
  refine ⟨I, fun ω ω' hω => ?_⟩
  have e : ∀ ω : (sz.withLam 0).SeqΩ, GreenCond_Gs sz z n t ∅ ω = GreenCore_Gc sz z n t ω := fun ω => GreenCond_Gs_empty hκ sz h n ht0 ht ω
  have h1 := hI ω ω' hω
  simp only [e] at h1
  exact h1

theorem GreenCond2_bddMeas_famA {κ ε 𝔠 𝔡 : ℝ} (hκ : 0 < κ) (h : BAFlow sz κ ε 𝔠 𝔡 z) (ht0 : 0 ≤ t) (ht : t ≤ BAflowT0 sz z n)
    (hg0 : 0 ≤ BAflowLam0 sz z n) (k : Idx d (sz.L n) (sz.W n)) :
    BddMeas (sz.withLam 0) (fun σ => GreenCond_ΦA sz z n k (GreenCore_Gc sz z n t σ)) := by
  have := GreenCond_bddMeas_A sz z n hκ h ht0 ht hg0 k ∅
  rwa [GreenCond_famS_empty sz z n hκ h ht0 ht] at this

theorem GreenCond2_bddMeas_famX {κ ε 𝔠 𝔡 : ℝ} (hκ : 0 < κ) (h : BAFlow sz κ ε 𝔠 𝔡 z) (ht0 : 0 ≤ t) (ht : t ≤ BAflowT0 sz z n)
    (hg0 : 0 ≤ BAflowLam0 sz z n) (α : Zd d (sz.L n)) (k : Idx d (sz.L n) (sz.W n)) :
    BddMeas (sz.withLam 0) (fun σ => GreenCond_ΦX sz z n α k (GreenCore_Gc sz z n t σ)) := by
  have := GreenCond_bddMeas_X sz z n hκ h ht0 ht hg0 α k ∅
  rwa [GreenCond_famS_empty sz z n hκ h ht0 ht] at this

/-- **The probability of the exceptional set**: `P(Bad) ≤ P(badStep) + (N + N²) W_τ^{-2p}`, from the family gains of the pin (`GreenCond2_prob_famAvg`). -/
theorem GreenCond2_FAav_prob {κ ε 𝔠 𝔡 : ℝ} (hκ : 0 < κ) (h : BAFlow sz κ ε 𝔠 𝔡 z) (ht0 : 0 ≤ t) (ht : t ≤ BAflowT0 sz z n)
    (hg0 : 0 ≤ BAflowLam0 sz z n) {δ ε' C Wτ : ℝ} {p : ℕ} (hp1 : 1 ≤ p) (hd : 1 ≤ d) (hδ0 : 0 < δ) (hδ4 : 4 * δ ≤ 1) (hC1 : 1 ≤ C)
    (hwd : (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ δ ^ 2) (hp : 2 * p ≤ sz.W n ^ d) (hWτ : 1 ≤ Wτ)
    (hfam : ∀ β α : Zd d (sz.L n), β ≠ α →
      GreenMinor_famGain (sz.withLam 0) n (Iblk d (sz.L n) (sz.W n) β) (fun k σ => GreenCond_ΦA sz z n k (GreenCore_Gc sz z n t σ)) (C * δ) (4 * δ) (2 * p) (2 * p) ∧
      GreenMinor_famGain (sz.withLam 0) n (Iblk d (sz.L n) (sz.W n) β) (fun k σ => GreenCond_ΦX sz z n α k (GreenCore_Gc sz z n t σ)) (C * δ) (4 * δ) (2 * p) (2 * p)) :
    (Sizes.seqP (sz.withLam 0)).real (GreenCond2_Bad sz z n t ε' δ (Wτ * (2 * (2 * p) * (2 ^ (2 * p - 1) * (4 * δ) * (C * δ))))) ≤
      (Sizes.seqP (sz.withLam 0)).real (badStep (sz.withLam 0) n ε' (GreenCond_badBase sz z n t δ)) +
        ((sz.size n : ℝ) + (sz.size n : ℝ) ^ 2) * (1 / Wτ) ^ (2 * p) := by
  have hL2 : 2 ≤ sz.L n := by have := sz.three_le_L n; omega
  have hρB : 0 < 4 * δ * (C * δ) := by positivity
  have hWd : (0 : ℝ) ≤ (1 / Wτ) ^ (2 * p) := by positivity
  have hN0 : (0 : ℝ) ≤ (sz.size n : ℝ) := Nat.cast_nonneg _
  have hcρ : (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ (4 * δ) ^ 2 := hwd.trans (by nlinarith [sq_nonneg δ])
  have hcard : (Fintype.card (Zd d (sz.L n)) : ℝ) ≤ (sz.size n : ℝ) := GreenCond2_card_Zd_le sz n
  -- one block average
  have hA : ∀ β : Zd d (sz.L n), (Sizes.seqP (sz.withLam 0)).real {ω | Wτ * (2 * (2 * p) * (2 ^ (2 * p - 1) * (4 * δ) * (C * δ))) ≤ ‖GreenCond2_SA sz z n t β ω‖} ≤ (1 / Wτ) ^ (2 * p) := by
    intro β
    obtain ⟨α, hα⟩ := GreenCond2_exists_ne hd hL2 β
    have := GreenCond2_prob_famAvg (sz := sz.withLam 0) (n := n) (A := Iblk d (sz.L n) (sz.W n) β)
      (Y := fun k σ => GreenCond_ΦA sz z n k (GreenCore_Gc sz z n t σ)) (fun k => ?_) (fun k => ?_) (ρ := 4 * δ) (B := C * δ) (c := (((sz.W n : ℕ) : ℝ) ^ d)⁻¹)
      (M := 2 * p) (K := 2 * p) (p := p) (T := fun k => if (split d (sz.L n) (sz.W n) k).1 = β then (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ else 0)
      (hfam β α hα.symm).1 le_rfl le_rfl hδ4 hcρ (uniformWeight_blockAvg2 d (sz.L n) (sz.W n) β).toBoundedWeight
      (hp.trans (card_Iblk d (sz.L n) (sz.W n) β).ge) hp1 hWτ hρB
    · exact this
    · exact GreenCond2_bddMeas_famA hκ h ht0 ht hg0 k
    · exact GreenCond2_finDep hκ h ht0 ht _
  have hX : ∀ q : {q : Zd d (sz.L n) × Zd d (sz.L n) // q.1 ≠ q.2}, (Sizes.seqP (sz.withLam 0)).real
      {ω | Wτ * (2 * (2 * p) * (2 ^ (2 * p - 1) * (4 * δ) * (C * δ))) ≤ ‖GreenCond2_SX sz z n t q.1.1 q.1.2 ω‖} ≤ (1 / Wτ) ^ (2 * p) := by
    intro q
    have := GreenCond2_prob_famAvg (sz := sz.withLam 0) (n := n) (A := Iblk d (sz.L n) (sz.W n) q.1.1)
      (Y := fun k σ => GreenCond_ΦX sz z n q.1.2 k (GreenCore_Gc sz z n t σ)) (fun k => ?_) (fun k => ?_) (ρ := 4 * δ) (B := C * δ) (c := (((sz.W n : ℕ) : ℝ) ^ d)⁻¹)
      (M := 2 * p) (K := 2 * p) (p := p) (T := fun k => if (split d (sz.L n) (sz.W n) k).1 = q.1.1 then (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ else 0)
      (hfam q.1.1 q.1.2 q.2).2 le_rfl le_rfl hδ4 hcρ (uniformWeight_blockAvg2 d (sz.L n) (sz.W n) q.1.1).toBoundedWeight
      (hp.trans (card_Iblk d (sz.L n) (sz.W n) q.1.1).ge) hp1 hWτ hρB
    · exact this
    · exact GreenCond2_bddMeas_famX hκ h ht0 ht hg0 _ k
    · exact GreenCond2_finDep hκ h ht0 ht _
  unfold GreenCond2_Bad
  refine (measureReal_union_le _ _).trans ?_
  refine (add_le_add (measureReal_union_le _ _) le_rfl).trans ?_
  have hUA : (Sizes.seqP (sz.withLam 0)).real (⋃ β : Zd d (sz.L n), {ω | Wτ * (2 * (2 * p) * (2 ^ (2 * p - 1) * (4 * δ) * (C * δ))) ≤ ‖GreenCond2_SA sz z n t β ω‖}) ≤
      (sz.size n : ℝ) * (1 / Wτ) ^ (2 * p) := by
    refine (measureReal_iUnion_fintype_le _).trans ?_
    refine (Finset.sum_le_sum fun β _ => hA β).trans ?_
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right hcard hWd
  have hUX : (Sizes.seqP (sz.withLam 0)).real (⋃ q : {q : Zd d (sz.L n) × Zd d (sz.L n) // q.1 ≠ q.2}, {ω | Wτ * (2 * (2 * p) * (2 ^ (2 * p - 1) * (4 * δ) * (C * δ))) ≤ ‖GreenCond2_SX sz z n t q.1.1 q.1.2 ω‖}) ≤
      (sz.size n : ℝ) ^ 2 * (1 / Wτ) ^ (2 * p) := by
    refine (measureReal_iUnion_fintype_le _).trans ?_
    refine (Finset.sum_le_sum fun q _ => hX q).trans ?_
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    refine mul_le_mul_of_nonneg_right ?_ hWd
    have h1 : Fintype.card {q : Zd d (sz.L n) × Zd d (sz.L n) // q.1 ≠ q.2} ≤ Fintype.card (Zd d (sz.L n) × Zd d (sz.L n)) := Fintype.card_subtype_le _
    rw [Fintype.card_prod] at h1
    have h2 : (Fintype.card {q : Zd d (sz.L n) × Zd d (sz.L n) // q.1 ≠ q.2} : ℝ) ≤ (Fintype.card (Zd d (sz.L n)) : ℝ) * Fintype.card (Zd d (sz.L n)) := by
      exact_mod_cast h1
    calc (Fintype.card {q : Zd d (sz.L n) × Zd d (sz.L n) // q.1 ≠ q.2} : ℝ) ≤ (Fintype.card (Zd d (sz.L n)) : ℝ) * Fintype.card (Zd d (sz.L n)) := h2
      _ ≤ (sz.size n : ℝ) * (sz.size n : ℝ) := mul_le_mul hcard hcard (Nat.cast_nonneg _) hN0
      _ = (sz.size n : ℝ) ^ 2 := by ring
  linarith [hUA, hUX]

end FAav

/-! ## 8. Numerical bookkeeping of `BAFAav` -/

section FAarith
variable {d : ℕ}

theorem GreenCond2_cA_mono {κ g₀ g₀' s s' : ℝ} (hκ : 0 < κ) (hg : 0 ≤ g₀) (hgg : g₀ ≤ g₀') (hs : 0 ≤ s) (hss : s ≤ s') :
    GreenCond_cA d κ g₀ s ≤ GreenCond_cA d κ g₀' s' := by
  unfold GreenCond_cA
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  gcongr

theorem GreenCond2_cX_mono {κ g₀ g₀' s s' : ℝ} (hκ : 0 < κ) (hg : 0 ≤ g₀) (hgg : g₀ ≤ g₀') (hs : 0 ≤ s) (hss : s ≤ s') :
    GreenCond_cX d κ g₀ s ≤ GreenCond_cX d κ g₀' s' := by
  unfold GreenCond_cX
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  gcongr

theorem GreenCond2_C1_mono {κ g₀ g₀' s s' : ℝ} (hκ : 0 < κ) (hg : 0 ≤ g₀) (hgg : g₀ ≤ g₀') (hs : 0 ≤ s) (hss : s ≤ s') :
    GreenCond_C1 d κ g₀ s ≤ GreenCond_C1 d κ g₀' s' := by
  unfold GreenCond_C1
  have := GreenCond2_cA_mono (d := d) hκ hg hgg hs hss
  have := GreenCond2_cX_mono (d := d) hκ hg hgg hs hss
  gcongr

/-- `Q_A, Q_X ≤ C_Q N⁸` from `η_t⁻¹ ≤ (2/κ) N`, `0 ≤ g₀ ≤ Λ`, `N ≥ 1`, with `C_Q = 3 c² (2 + 2 c² (2dΛ)² + 12 c²) + c⁴`, `c = 2/κ + 1`. -/
theorem GreenCond2_Q_le {κ g₀ Λ N γ : ℝ} (hκ : 0 < κ) (hg : 0 ≤ g₀) (hgΛ : g₀ ≤ Λ) (hN : 1 ≤ N) (hγ0 : 0 ≤ γ) (hγ : γ ≤ 2 / κ * N) :
    (γ + 1) ^ 2 * (3 * (2 + 2 * γ ^ 2 * (2 * d * g₀) ^ 2 * N ^ 2 + 12 * γ ^ 2 * N ^ 4)) ≤
        (3 * (2 / κ + 1) ^ 2 * (2 + 2 * (2 / κ + 1) ^ 2 * (2 * d * Λ) ^ 2 + 12 * (2 / κ + 1) ^ 2) + (2 / κ + 1) ^ 4) * N ^ 8 ∧
      (γ + 1) ^ 2 * (γ ^ 2 * N ^ 2) ≤
        (3 * (2 / κ + 1) ^ 2 * (2 + 2 * (2 / κ + 1) ^ 2 * (2 * d * Λ) ^ 2 + 12 * (2 / κ + 1) ^ 2) + (2 / κ + 1) ^ 4) * N ^ 8 := by
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hΛ0 : 0 ≤ Λ := hg.trans hgΛ
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = 2 / κ + 1 := ⟨_, rfl⟩
  have hc1 : 1 ≤ c := by rw [hc]; have : 0 ≤ 2 / κ := by positivity
                         linarith
  have hN0 : 0 ≤ N := by linarith
  have hγc : γ ≤ c * N := by
    rw [hc]; nlinarith
  have hγ1 : γ + 1 ≤ c * N := by
    rw [hc]; nlinarith
  have hN2 : N ^ 2 ≤ N ^ 6 := pow_le_pow_right₀ hN (by norm_num)
  have hN4 : N ^ 4 ≤ N ^ 6 := pow_le_pow_right₀ hN (by norm_num)
  have hN1 : (1 : ℝ) ≤ N ^ 6 := one_le_pow₀ hN
  have h2g : (2 * d * g₀) ^ 2 ≤ (2 * d * Λ) ^ 2 := pow_le_pow_left₀ (by positivity) (by gcongr) 2
  have hγ2 : γ ^ 2 ≤ c ^ 2 * N ^ 2 := by
    calc γ ^ 2 ≤ (c * N) ^ 2 := pow_le_pow_left₀ hγ0 hγc 2
      _ = c ^ 2 * N ^ 2 := by ring
  have hγ12 : (γ + 1) ^ 2 ≤ c ^ 2 * N ^ 2 := by
    calc (γ + 1) ^ 2 ≤ (c * N) ^ 2 := pow_le_pow_left₀ (by positivity) hγ1 2
      _ = c ^ 2 * N ^ 2 := by ring
  have hIn : 2 + 2 * γ ^ 2 * (2 * d * g₀) ^ 2 * N ^ 2 + 12 * γ ^ 2 * N ^ 4 ≤ (2 + 2 * c ^ 2 * (2 * d * Λ) ^ 2 + 12 * c ^ 2) * N ^ 6 := by
    have t1 : 2 * γ ^ 2 * (2 * d * g₀) ^ 2 * N ^ 2 ≤ 2 * c ^ 2 * (2 * d * Λ) ^ 2 * N ^ 6 := by
      calc 2 * γ ^ 2 * (2 * d * g₀) ^ 2 * N ^ 2 ≤ 2 * (c ^ 2 * N ^ 2) * (2 * d * Λ) ^ 2 * N ^ 2 := by gcongr
        _ = 2 * c ^ 2 * (2 * d * Λ) ^ 2 * N ^ 4 := by ring
        _ ≤ 2 * c ^ 2 * (2 * d * Λ) ^ 2 * N ^ 6 := by gcongr
    have t2 : 12 * γ ^ 2 * N ^ 4 ≤ 12 * c ^ 2 * N ^ 6 := by
      calc 12 * γ ^ 2 * N ^ 4 ≤ 12 * (c ^ 2 * N ^ 2) * N ^ 4 := by gcongr
        _ = 12 * c ^ 2 * N ^ 6 := by ring
    nlinarith
  constructor
  · calc (γ + 1) ^ 2 * (3 * (2 + 2 * γ ^ 2 * (2 * d * g₀) ^ 2 * N ^ 2 + 12 * γ ^ 2 * N ^ 4))
        ≤ (c ^ 2 * N ^ 2) * (3 * ((2 + 2 * c ^ 2 * (2 * d * Λ) ^ 2 + 12 * c ^ 2) * N ^ 6)) := by gcongr
      _ = (3 * c ^ 2 * (2 + 2 * c ^ 2 * (2 * d * Λ) ^ 2 + 12 * c ^ 2)) * N ^ 8 := by ring
      _ ≤ (3 * c ^ 2 * (2 + 2 * c ^ 2 * (2 * d * Λ) ^ 2 + 12 * c ^ 2) + c ^ 4) * N ^ 8 := by
          have : 0 ≤ c ^ 4 * N ^ 8 := by positivity
          nlinarith
      _ = _ := by rw [hc]
  · calc (γ + 1) ^ 2 * (γ ^ 2 * N ^ 2) ≤ (c ^ 2 * N ^ 2) * ((c ^ 2 * N ^ 2) * N ^ 2) := by gcongr
      _ = c ^ 4 * N ^ 6 := by ring
      _ ≤ c ^ 4 * N ^ 8 := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hN (by norm_num)) (by positivity)
      _ ≤ (3 * c ^ 2 * (2 + 2 * c ^ 2 * (2 * d * Λ) ^ 2 + 12 * c ^ 2) + c ^ 4) * N ^ 8 := by
          have : 0 ≤ 3 * c ^ 2 * (2 + 2 * c ^ 2 * (2 * d * Λ) ^ 2 + 12 * c ^ 2) * N ^ 8 := by positivity
          nlinarith
      _ = _ := by rw [hc]

/-- **`√(ε' Q) ≤ δ²`** at the threshold `ε' = N^{-(2d+9)}`: `Q ≤ C_Q N⁸`, `C_Q ≤ N`, `1 ≤ N^d δ²`. -/
theorem GreenCond2_hsq_arith {N δ Q CQ : ℝ} (hN1 : 1 ≤ N) (hδN : 1 ≤ N ^ d * δ ^ 2) (hQ : Q ≤ CQ * N ^ 8)
    (hCQ : CQ ≤ N) : Real.sqrt (1 / N ^ (2 * d + 9) * Q) ≤ δ ^ 2 := by
  have hN0 : 0 < N := by linarith
  have h1 : 1 / N ^ (2 * d + 9) * Q ≤ (δ ^ 2) ^ 2 := by
    have hpos : 0 < N ^ (2 * d + 9) := by positivity
    rw [one_div, inv_mul_le_iff₀ hpos]
    calc Q ≤ CQ * N ^ 8 := hQ
      _ ≤ N * N ^ 8 := by gcongr
      _ = N ^ 9 := by ring
      _ ≤ N ^ (2 * d + 9) * (δ ^ 2) ^ 2 := by
          have h2 : 1 ≤ (N ^ d * δ ^ 2) ^ 2 := one_le_pow₀ hδN
          have : N ^ (2 * d + 9) * (δ ^ 2) ^ 2 = N ^ 9 * (N ^ d * δ ^ 2) ^ 2 := by ring
          rw [this]
          nlinarith [pow_pos hN0 9]
  calc Real.sqrt (1 / N ^ (2 * d + 9) * Q) ≤ Real.sqrt ((δ ^ 2) ^ 2) := Real.sqrt_le_sqrt h1
    _ = δ ^ 2 := Real.sqrt_sq (sq_nonneg δ)

/-- The probability arithmetic: `P(badStep) ≤ 2 N^{c+1} P(S)`, `P(S) ≤ X/N^{c+3}`, `W_τ^{-2p} ≤ X/N³`, `N ≥ 4` give `P(Bad) ≤ X`, `X = N^{-D}`. -/
theorem GreenCond2_prob_arith {N X Pstep PS W2p : ℝ} (c : ℕ) (hN4 : 4 ≤ N) (hX : 0 ≤ X) (hPS : PS ≤ X / N ^ (c + 3))
    (hPstep : Pstep ≤ 2 * N ^ (c + 1) * PS) (hW : W2p ≤ X / N ^ 3) : Pstep + (N + N ^ 2) * W2p ≤ X := by
  have hN0 : 0 < N := by linarith
  have h1 : Pstep ≤ 2 * X / N ^ 2 := by
    refine hPstep.trans ?_
    calc 2 * N ^ (c + 1) * PS ≤ 2 * N ^ (c + 1) * (X / N ^ (c + 3)) := by gcongr
      _ = 2 * X / N ^ 2 := by field_simp; ring
  have h2 : (N + N ^ 2) * W2p ≤ 2 * X / N := by
    have hN1 : N ≤ N ^ 2 := by nlinarith
    calc (N + N ^ 2) * W2p ≤ (2 * N ^ 2) * (X / N ^ 3) := by
          have hW0 : 0 ≤ X / N ^ 3 := by positivity
          have hW2 : 0 ≤ W2p ∨ W2p < 0 := le_or_gt 0 W2p
          rcases hW2 with h0 | h0
          · exact mul_le_mul (by linarith) hW h0 (by positivity)
          · nlinarith
      _ = 2 * X / N := by field_simp
  have h3 : 2 * X / N ^ 2 + 2 * X / N ≤ X := by
    have hN2 : 16 ≤ N ^ 2 := by nlinarith
    have e1 : 2 * X / N ^ 2 ≤ X / 8 := by
      rw [div_le_iff₀ (by positivity)]; nlinarith [mul_nonneg hX (sub_nonneg.2 hN2)]
    have e2 : 2 * X / N ≤ X / 2 := by
      rw [div_le_iff₀ hN0]; nlinarith
    linarith
  linarith

/-- `N^{-(D + k)} = N^{-D} / N^k`. -/
theorem GreenCond2_rpow_neg_add {N : ℝ} (hN : 0 < N) (D : ℝ) (k : ℕ) : N ^ (-(D + k)) = N ^ (-D) / N ^ k := by
  rw [show -(D + (k : ℝ)) = -D - (k : ℝ) by ring, Real.rpow_sub hN, Real.rpow_natCast]

end FAarith

/-! ## 9. `BAFAav`, proved -/

/-- **`BAFAav d`, proved** (the owed pin of the G5b row; consumer BA-G6b), for every `d` (the `ℓ¹` row bound of `M^{(B)}` is `GreenCond2_row_l1`,
`d ≥ 1`).  Fix `τ' , D`; `τ = min (τ'/6) (ε₀/2)`, `p` with `2 p 𝔠 τ ≥ D + 3`; `δ = W^τ Ψ_n`, `C ≥ 1` from `baFamGain_holds`.  Off the exceptional set
`GreenCond2_Bad` (the tower step at the threshold `ε' = N^{-(2d+9)}` over `{‖G_t - M‖_max ≤ δ}`, and the family averages `≥ lam = W^τ · 2 (2p) 2^{2p-1} ρ B`)
the exact identity `GreenMinor_avg_split`, the decompositions (E) and the bounds of §5-§6 give `‖⟨M𝒦⟩_a‖ ≤ K₀ W^{3τ} Ψ_n² ≤ N^{τ'} Ψ_n²` (`K₀` depends on
`(d, κ, 𝔡, p, C)` only); the probability is `≤ N^{-D}` (`P(badBase) ≤ N^{-(D + 2d + 12)}` from `BAGiiGEX` at `ε₀/2` and `(initialGT2)`, Markov, `W ≥ N^𝔠`). -/
theorem baFAav_holds (d : ℕ) : BAFAav d := by
  intro κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow t ht0 htT ε₀ hε₀ hii Ψ hΨlo hΨhi hinit
  have hd1 : 1 ≤ d := GreenCond2_one_le_d sz hflow.1.2.2.1
  have hsz : Tendsto (fun n => ((sz.size n : ℕ) : ℝ)) atTop atTop := hflow.1.2.2.1
  have h𝔠 : 0 < 𝔠 := hflow.1.1
  have hκ1 : κ ≤ 1 := by
    have hr := BAflow_real κ ε 𝔠 𝔡 sz z hflow 0
    have hm1 : ‖GreenCond_m sz z 0‖ ≤ 1 :=
      BAm_norm_le_one (d := d) (L := sz.L 0) (BAflowLam0 sz z 0) (BAflowEs sz z 0 : ℂ) (GreenCond_m sz z 0) (by simp) hr.1
    exact hr.2.trans ((le_abs_self _).trans ((Complex.abs_im_le_norm _).trans hm1))
  have hΨ0 : ∀ᶠ n in atTop, 0 ≤ Ψ n := by
    filter_upwards [hΨlo] with n hn
    exact le_trans (Real.rpow_nonneg (Nat.cast_nonneg _) _) hn
  unfold PrecL
  intro τ' hτ' D hD
  obtain ⟨Λ, hΛ⟩ : ∃ Λ : ℝ, Λ = 𝔡⁻¹ := ⟨_, rfl⟩
  have hΛ0 : 0 < Λ := by rw [hΛ]; exact inv_pos.2 h𝔡
  obtain ⟨sbd, hsbd⟩ : ∃ sbd : ℝ, sbd = (1 + 2 * d * Λ) / κ := ⟨_, rfl⟩
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hsbd0 : 0 ≤ sbd := by rw [hsbd]; positivity
  obtain ⟨τ, hτ⟩ : ∃ τ : ℝ, τ = min (τ' / 6) (ε₀ / 2) := ⟨_, rfl⟩
  have hτ0 : 0 < τ := by rw [hτ]; exact lt_min (by positivity) (by positivity)
  have hτε : τ ≤ ε₀ / 2 := by rw [hτ]; exact min_le_right _ _
  have hτ6 : 6 * τ ≤ τ' := by have := min_le_left (τ' / 6) (ε₀ / 2); rw [← hτ] at this; linarith
  obtain ⟨p, hp1, hpD⟩ : ∃ p : ℕ, 1 ≤ p ∧ D + 3 ≤ 2 * p * (𝔠 * τ) := by
    refine ⟨⌈(D + 3) / (2 * (𝔠 * τ))⌉₊ + 1, by omega, ?_⟩
    have hpos : 0 < 2 * (𝔠 * τ) := by positivity
    have := Nat.le_ceil ((D + 3) / (2 * (𝔠 * τ)))
    rw [div_le_iff₀ hpos] at this
    push_cast
    nlinarith
  obtain ⟨C₀, hC₀, hfam⟩ := baFamGain_holds d κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow t ht0 htT ε₀ hε₀ hii Ψ hΨlo hΨhi hinit τ hτ0 hτε p
  obtain ⟨C, hC⟩ : ∃ C : ℝ, C = max C₀ 1 := ⟨_, rfl⟩
  have hC1 : 1 ≤ C := by rw [hC]; exact le_max_right _ _
  have hCC : C₀ ≤ C := by rw [hC]; exact le_max_left _ _
  obtain ⟨c₀, hc₀⟩ : ∃ c₀ : ℝ, c₀ = BAct_rate d Λ κ := ⟨_, rfl⟩
  have hc₀0 : 0 < c₀ := by rw [hc₀]; exact BAct_rate_pos d Λ κ (by omega) hΛ0 hκ
  have hexp1 : Real.exp (-c₀) < 1 := by
    calc Real.exp (-c₀) < Real.exp 0 := Real.exp_lt_exp.2 (by linarith)
      _ = 1 := Real.exp_zero
  have hexp0 : 0 < Real.exp (-c₀) := Real.exp_pos _
  obtain ⟨ρr, hρr⟩ : ∃ ρr : ℝ, ρr = c₀⁻¹ * ((1 + Real.exp (-c₀)) / (1 - Real.exp (-c₀))) ^ d := ⟨_, rfl⟩
  have hρr0 : 0 ≤ ρr := by
    rw [hρr]; have : 0 < 1 - Real.exp (-c₀) := by linarith
    positivity
  obtain ⟨Kl, hKl⟩ : ∃ Kl : ℝ, Kl = 2 * (2 * p) * 2 ^ (2 * p) * 4 * C := ⟨_, rfl⟩
  obtain ⟨K₀, hK₀⟩ : ∃ K₀ : ℝ, K₀ = ρr * (2 + GreenCond_cA d κ Λ sbd + 2 * GreenCond_C1 d κ Λ sbd + 2 * Kl) := ⟨_, rfl⟩
  obtain ⟨CQ, hCQ⟩ : ∃ CQ : ℝ, CQ = 3 * (2 / κ + 1) ^ 2 * (2 + 2 * (2 / κ + 1) ^ 2 * (2 * d * Λ) ^ 2 + 12 * (2 / κ + 1) ^ 2) + (2 / κ + 1) ^ 4 := ⟨_, rfl⟩
  obtain ⟨δ₀, hδ₀⟩ : ∃ δ₀ : ℝ, δ₀ = min (κ / 2) (1 / 4) := ⟨_, rfl⟩
  have hδ₀0 : 0 < δ₀ := by rw [hδ₀]; exact lt_min (by positivity) (by norm_num)
  have hW := tendsto_W sz hflow.1.1 hflow.1.2.2.1 hflow.1.2.2.2.1
  filter_upwards [hΨlo, hΨhi, BAflow_lam0_window κ ε 𝔠 𝔡 sz z hflow, GreenCond2_delta_small sz hflow.1 hε₀ hτε hΨ0 hΨhi hδ₀0, hfam,
    GreenCond2_prob_badBase hκ hε h𝔡 sz hflow ht0 htT hε₀ hii hΨ0 hinit hτ0 (D := D + ((2 * d + 9 : ℕ) : ℝ) + 3) (by positivity),
    hsz.eventually_ge_atTop (max 4 CQ), ((tendsto_rpow_atTop (half_pos hτ')).comp hsz).eventually_ge_atTop K₀, hflow.1.2.2.2.1,
    hW.eventually_ge_atTop (2 * p : ℝ)] with n hΨlon hΨhin hlam hδsm hfamn hPS hNbig hKbig hband hWbig
  obtain ⟨hg0', hgΛ⟩ := hlam
  have hg0 : 0 ≤ BAflowLam0 sz z n := hg0'.le
  have hgΛ' : BAflowLam0 sz z n ≤ Λ := by rw [hΛ]; exact hgΛ
  set N : ℝ := (sz.size n : ℝ) with hN
  obtain ⟨w, hw⟩ : ∃ w : ℝ, w = (sz.W n : ℝ) ^ τ := ⟨_, rfl⟩
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = w * Ψ n := ⟨_, rfl⟩
  have hN4 : 4 ≤ N := (le_max_left _ _).trans hNbig
  have hCQN : CQ ≤ N := (le_max_right _ _).trans hNbig
  have hN1 : 1 ≤ N := by linarith
  have hN0 : 0 < N := by linarith
  have hW1 : (1 : ℝ) ≤ (sz.W n : ℝ) := by exact_mod_cast sz.W_pos n
  have hW0 : (0 : ℝ) < (sz.W n : ℝ) := by linarith
  have hw1 : 1 ≤ w := by rw [hw]; exact Real.one_le_rpow hW1 hτ0.le
  have hΨpos : 0 < Ψ n := lt_of_lt_of_le (Real.rpow_pos_of_pos hW0 _) hΨlon
  have hδ0 : 0 < δ := by rw [hδ]; positivity
  have hδδ₀ : δ ≤ δ₀ := by rw [hδ, hw]; exact hδsm
  have hδ2 : δ ≤ κ / 2 := hδδ₀.trans (by rw [hδ₀]; exact min_le_left _ _)
  have hδ4 : 4 * δ ≤ 1 := by
    have : δ ≤ 1 / 4 := hδδ₀.trans (by rw [hδ₀]; exact min_le_right _ _)
    linarith
  have hWN : (sz.W n : ℝ) ≤ N := GreenCond2_W_le_size sz hd1 n
  have hwd : ((sz.W n : ℝ) ^ d)⁻¹ ≤ δ ^ 2 := hδ ▸ GreenCond_hwd hW1 hw1 hΨlon
  have hδN : 1 ≤ N ^ d * δ ^ 2 := by
    have h1 : (1 : ℝ) ≤ (sz.W n : ℝ) ^ d * δ ^ 2 := by
      calc (1 : ℝ) = (sz.W n : ℝ) ^ d * ((sz.W n : ℝ) ^ d)⁻¹ := by field_simp
        _ ≤ (sz.W n : ℝ) ^ d * δ ^ 2 := mul_le_mul_of_nonneg_left hwd (by positivity)
    exact h1.trans (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hW0.le hWN d) (sq_nonneg δ))
  -- the BA data
  have ht1 : t n ≤ 1 := (ba_G_data hκ sz hflow n (ht0 n) (htT n)).1.le
  have hr := (ba_G_data hκ sz hflow n (ht0 n) (htT n)).2.1
  have hs0 : 0 ≤ ‖GreenCond_s sz z n‖ := norm_nonneg _
  have hs : ‖GreenCond_s sz z n‖ ≤ sbd := by
    refine (GreenCond2_norm_s_le hκ sz hflow n (ht0 n) (htT n) hg0).trans ?_
    rw [hsbd]
    refine div_le_div_of_nonneg_right ?_ hκ.le
    have := mul_le_mul_of_nonneg_left hgΛ' (show (0 : ℝ) ≤ 2 * d by positivity)
    linarith only [this]
  have hη := GreenCond2_inv_eta_le hκ hε sz hflow n (ht0 n) (htT n)
  have hQ := GreenCond2_Q_le (d := d) hκ hg0 hgΛ' hN1 (inv_nonneg.2 (abs_nonneg _)) hη
  rw [← hCQ] at hQ
  have hsqA := GreenCond2_hsq_arith (d := d) hN1 hδN hQ.1 hCQN
  have hsqX := GreenCond2_hsq_arith (d := d) hN1 hδN hQ.2 hCQN
  have hρ : ∀ a, ∑ b, ‖BAMB d (sz.L n) (BAflowLam0 sz z n) (BAflowEs sz z n : ℂ) (GreenCond_m sz z n) a b‖ ≤ ρr := fun a => by
    rw [hρr, hc₀]
    exact GreenCond2_row_l1 d (sz.L n) (sz.three_le_L n) (by omega) Λ _ κ _ _ hΛ0 hg0' hgΛ' hκ hr a
  -- the exceptional set
  obtain ⟨lam, hlam⟩ : ∃ lam : ℝ, lam = w * (2 * (2 * p) * (2 ^ (2 * p - 1) * (4 * δ) * (C * δ))) := ⟨_, rfl⟩
  have hlam0 : 0 ≤ lam := by rw [hlam]; positivity
  have hlamK : lam ≤ w * (Kl * δ ^ 2) := by
    rw [hlam, hKl]
    have h2 : (2 : ℝ) ^ (2 * p - 1) ≤ 2 ^ (2 * p) := pow_le_pow_right₀ (by norm_num) (by omega)
    calc w * (2 * (2 * p) * (2 ^ (2 * p - 1) * (4 * δ) * (C * δ))) ≤ w * (2 * (2 * p) * (2 ^ (2 * p) * (4 * δ) * (C * δ))) := by gcongr
      _ = w * (2 * (2 * p) * 2 ^ (2 * p) * 4 * C * δ ^ 2) := by ring
  have hfam' : ∀ β α : Zd d (sz.L n), β ≠ α →
      GreenMinor_famGain (sz.withLam 0) n (Iblk d (sz.L n) (sz.W n) β) (fun k σ => GreenCond_ΦA sz z n k (GreenCore_Gc sz z n (t n) σ)) (C * δ) (4 * δ) (2 * p) (2 * p) ∧
      GreenMinor_famGain (sz.withLam 0) n (Iblk d (sz.L n) (sz.W n) β) (fun k σ => GreenCond_ΦX sz z n α k (GreenCore_Gc sz z n (t n) σ)) (C * δ) (4 * δ) (2 * p) (2 * p) := by
    intro β α hβα
    have hB : C₀ * (w * Ψ n) ≤ C * δ := by rw [hδ]; exact mul_le_mul_of_nonneg_right hCC (by positivity)
    have e : (sz.W n : ℝ) ^ τ * Ψ n = w * Ψ n := by rw [hw]
    obtain ⟨h1, h2⟩ := hfamn β α hβα
    rw [e, ← hδ] at h1 h2
    exact ⟨GreenCond2_famGain_mono h1 (by rw [hδ] at *; exact hB), GreenCond2_famGain_mono h2 (by rw [hδ] at *; exact hB)⟩
  have hp2 : 2 * p ≤ sz.W n ^ d := by
    have h1 : 2 * p ≤ sz.W n := by exact_mod_cast hWbig
    exact h1.trans (Nat.le_self_pow (by omega) _)
  have hprob := GreenCond2_FAav_prob hκ hflow (ht0 n) (htT n) hg0 (δ := δ) (ε' := 1 / N ^ (2 * d + 9)) (C := C) (Wτ := w) (p := p) hp1 hd1 hδ0 hδ4 hC1
    hwd hp2 hw1 hfam'
  rw [← hlam] at hprob
  have hS := GreenCond_measurableSet_badBase sz z n (t n) δ
  have hPstep := GreenCond2_Pbad_le' (sz.withLam 0) n hS (2 * d + 9) 1
  have hPS' : (Sizes.seqP (sz.withLam 0)).real (GreenCond_badBase sz z n (t n) δ) ≤ N ^ (-D) / N ^ (2 * d + 9 + 3) := by
    have h1 := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hδ ▸ hw ▸ hPS)
    rw [ENNReal.toReal_ofReal (Real.rpow_nonneg hN0.le _)] at h1
    refine h1.trans (le_of_eq ?_)
    rw [← GreenCond2_rpow_neg_add hN0 D (2 * d + 9 + 3)]
    congr 1
    push_cast; ring
  have hwN : N ^ (𝔠 * τ) ≤ w := by
    rw [hw]
    calc N ^ (𝔠 * τ) = (N ^ 𝔠) ^ τ := by rw [← Real.rpow_mul hN0.le]
      _ ≤ (sz.W n : ℝ) ^ τ := Real.rpow_le_rpow (Real.rpow_nonneg hN0.le _) hband hτ0.le
  have hW2p : (1 / w) ^ (2 * p) ≤ N ^ (-D) / N ^ 3 := by
    have hNp : 0 < N ^ (𝔠 * τ) := Real.rpow_pos_of_pos hN0 _
    have e : N ^ (-D) / N ^ 3 = N ^ (-(D + 3)) := by
      have := GreenCond2_rpow_neg_add hN0 D 3
      push_cast at this; exact this.symm
    rw [e]
    calc (1 / w) ^ (2 * p) ≤ (1 / N ^ (𝔠 * τ)) ^ (2 * p) := by gcongr
      _ = N ^ (-((2 * p : ℝ) * (𝔠 * τ))) := by
          rw [one_div, inv_pow, ← Real.rpow_natCast, ← Real.rpow_mul hN0.le, ← Real.rpow_neg hN0.le]
          congr 1; push_cast; ring
      _ ≤ N ^ (-(D + 3)) := Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  have hBad : (Sizes.seqP (sz.withLam 0)).real (GreenCond2_Bad sz z n (t n) (1 / N ^ (2 * d + 9)) δ lam) ≤ N ^ (-D) :=
    hprob.trans (GreenCond2_prob_arith (2 * d + 9) hN4 (Real.rpow_nonneg hN0.le _) hPS' (by rw [pow_one] at hPstep; exact hPstep) hW2p)
  -- the deterministic bound
  have hw3 : w ^ 3 ≤ N ^ (τ' / 2) := by
    have h1 : w ≤ N ^ τ := by rw [hw]; exact Real.rpow_le_rpow hW0.le hWN hτ0.le
    calc w ^ 3 ≤ (N ^ τ) ^ 3 := pow_le_pow_left₀ (by linarith) h1 3
      _ = N ^ (τ * 3) := by rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; norm_num
      _ ≤ N ^ (τ' / 2) := Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  have hKbig' : K₀ ≤ N ^ (τ' / 2) := hKbig
  have hDet : ∀ ω : (sz.withLam 0).SeqΩ, ω ∉ GreenCond2_Bad sz z n (t n) (1 / N ^ (2 * d + 9)) δ lam → ∀ a : Zd d (sz.L n),
      ‖GreenMinor_avgK (GreenCore_Gc sz z n (t n) ω) (GreenCore_Mc sz z n) (GreenCore_Xc sz n (t n) ω) (GreenCore_Dc sz z n)
        (BAMB d (sz.L n) (BAflowLam0 sz z n) (BAflowEs sz z n : ℂ) (GreenCond_m sz z n)) (t n) (GreenCond_m sz z n) a‖ ≤ N ^ τ' * Ψ n ^ 2 := by
    intro ω hω a
    refine (GreenCond2_FAav_det hκ hflow (ht0 n) (htT n) hg0 ht1 hδ0.le hδ2 (by positivity) hwd hsqA hsqX hlam0 hρr0 hρ ω hω a).trans ?_
    have hcA := GreenCond2_cA_mono (d := d) hκ hg0 hgΛ' hs0 hs
    have hC1' := GreenCond2_C1_mono (d := d) hκ hg0 hgΛ' hs0 hs
    have hcA0 := GreenCond_cA_nonneg (d := d) (κ := κ) hg0 hs0
    have hcX0 := GreenCond_cX_nonneg (d := d) hκ hg0 hs0 (s := ‖GreenCond_s sz z n‖)
    have hcAΛ0 := GreenCond_cA_nonneg (d := d) (κ := κ) hΛ0.le hsbd0
    have hC1Λ0 : 0 ≤ GreenCond_C1 d κ Λ sbd := by
      unfold GreenCond_C1
      have := GreenCond_cX_nonneg (d := d) hκ hΛ0.le hsbd0
      positivity
    have hKl0 : 0 ≤ Kl := by rw [hKl]; positivity
    obtain ⟨A₀, hA₀⟩ : ∃ A₀ : ℝ, A₀ = 2 + GreenCond_cA d κ Λ sbd + 2 * GreenCond_C1 d κ Λ sbd := ⟨_, rfl⟩
    have hA₀0 : 0 ≤ A₀ := by rw [hA₀]; positivity
    have hX : (2 + GreenCond_cA d κ (BAflowLam0 sz z n) ‖GreenCond_s sz z n‖) * δ ^ 2 +
        (lam + GreenCond_C1 d κ (BAflowLam0 sz z n) ‖GreenCond_s sz z n‖ * δ ^ 2) +
        (lam + GreenCond_C1 d κ (BAflowLam0 sz z n) ‖GreenCond_s sz z n‖ * δ ^ 2) ≤ (A₀ + 2 * Kl) * w * δ ^ 2 := by
      have h1 : (2 + GreenCond_cA d κ (BAflowLam0 sz z n) ‖GreenCond_s sz z n‖ + 2 * GreenCond_C1 d κ (BAflowLam0 sz z n) ‖GreenCond_s sz z n‖) ≤ A₀ := by
        rw [hA₀]; linarith
      have h2 : A₀ * δ ^ 2 ≤ A₀ * w * δ ^ 2 := by
        rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (le_mul_of_one_le_left (sq_nonneg δ) hw1) hA₀0
      have e2 := mul_le_mul_of_nonneg_right h1 (sq_nonneg δ)
      have e5 : (A₀ + 2 * Kl) * w * δ ^ 2 = A₀ * w * δ ^ 2 + 2 * (w * (Kl * δ ^ 2)) := by ring
      linarith only [e2, h2, hlamK, e5]
    calc _ ≤ ρr * ((A₀ + 2 * Kl) * w * δ ^ 2) := mul_le_mul_of_nonneg_left hX hρr0
      _ = K₀ * w ^ 3 * Ψ n ^ 2 := by rw [hK₀, hA₀, hδ]; ring
      _ ≤ N ^ (τ' / 2) * N ^ (τ' / 2) * Ψ n ^ 2 := by
          have hK0 : 0 ≤ K₀ := by rw [hK₀]; positivity
          gcongr
      _ = N ^ τ' * Ψ n ^ 2 := by rw [← Real.rpow_add hN0]; ring_nf
  have hsub : badSetAt sz.size (fun n a ω => ‖(((sz.W n : ℝ) ^ d)⁻¹ : ℝ) * ∑ o, ∑ b',
        BAMB d (sz.L n) (BAflowLam0 sz z n) (BAflowEs sz z n : ℂ) (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) a b' *
          GreenCore_K (GreenCore_Gc sz z n (t n) ω) (GreenCore_Mc sz z n) (GreenCore_Xc sz n (t n) ω)
            (GreenCore_Dc sz z n) (t n) (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) (b', o) (a, o)‖) (fun n _ _ => Ψ n ^ 2) τ' n ⊆
      GreenCond2_Bad sz z n (t n) (1 / N ^ (2 * d + 9)) δ lam := by
    intro ω hω
    by_contra hnot
    obtain ⟨a, ha⟩ := hω
    exact absurd (hDet ω hnot a) (not_le.2 ha)
  calc _ ≤ (Sizes.seqP (sz.withLam 0)) (GreenCond2_Bad sz z n (t n) (1 / N ^ (2 * d + 9)) δ lam) := measure_mono hsub
    _ = ENNReal.ofReal ((Sizes.seqP (sz.withLam 0)).real (GreenCond2_Bad sz z n (t n) (1 / N ^ (2 * d + 9)) δ lam)) :=
        (ofReal_measureReal (measure_ne_top _ _)).symm
    _ ≤ ENNReal.ofReal (N ^ (-D)) := ENNReal.ofReal_le_ofReal hBad

/-! ## 10. Nonempty instances of `baFamGain_holds`, `baFAav_holds`, `GreenCond2_famAvg_moment` -/

-- `baFamGain_holds` at `d = 3`, `sz0`, `zSeq`, `flow_sz0` (`κ = 1/2`, `ε = 𝔡 = 1/10`, `𝔠 = 1/6`), `t ≡ 1/2`, `ε₀ = 1/10`, `Ψ = W^{-1}` (window `W^{-3/2} ≤ Ψ ≤ W^{-1/10}`),
-- `τ = 1/20`, `p = 1`: `BAGiiGEX` (G6's owed `BAGbEXPii`) and `(initialGT2)` stay hypotheses
-- `baFAav_holds` at the same data: the averaged law `|⟨M𝒦⟩_a| ≺ Ψ²`
-- R6 (`GreenCond2_famAvg_moment`) for the BA family `Y^A` of the block `0` at a large `n` of the same data (`p = 1`; the gain interface is `baFamGain_holds`)
end RBM.BA
