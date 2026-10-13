/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Chain.SEforLnGen2
import RBM3D.Chain.DecayGenTw
import RBM3D.Chain.Step2IterGen
import RBM3D.BA.KDecayBA
import RBM3D.BA.KBound
import RBM3D.BA.KInduct
import RBM3D.BA.KWard
import RBM3D.BA.EMn2BA
import RBM3D.BA.Step2IterBA

/-!
# Ticket T2486, targets 2-5: `lem:SEforLn` at the block Anderson carrier (U2-BA, part (a), second file)

The BA readings of the merged generic results of `Chain/SEforLnGen.lean`, `Chain/SEforLnGen2.lean` at the BA tuple
`(law, Flow, mkM, Hf, mk, T0) = (seqP ∘ withLam 0, BAFlow, baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z), seqHflowBA (BAflowLam0 sz z),
baFMz, BAflowT0)`.  No merged file is edited.

* **Target 2 (a)** `baZeroModeGen_wardCls` (UN-C3, the one BA proof of the Ward class, paper `lem_WI_K` `1_2:1034-1046`): `TL` is the
  loop of `blockMat (seqHflowBA ..)` at `ztOf` (`zeroModeGen_loopL_wardFam`, `loopM_eq_loopL`), `TK = BAKsol` through `baKcac_isKLoopS`,
  `baK_unique`, `baK_rotate`, `baK_ward` with `(Kn2sol)` from `BAKcac_spliced`.  This route reads `BAReal` only (no `0 < g₀`).
* **Target 2 (b)** `baKsol_oneLoop`: the first conjunct of `Step2IterGen_OneLoop`, a one-line bridge from T1-BA's `baStep2_oneLoop`.
* **Target 2 (c)** `baStep34_LCompat`, `baStep34_KCompat` (every `sz, lam0, E`), `baStep2Mat_loopForm` (under the flow),
  `baStep2Mat_carrierFacts` (the conjunction), `baStep5CasesGen_flowFacts`.
* **Target 3** `baSEforLnGen_facts`; **target 4** `baSEforLnConclgL_of`, `BASEforLn`, `baSEforLn_holds`; **target 5**
  `baEtermDecaygL` (with the ε-free `STKboundgL`, a private copy of the reduction `BAKbound_of_uniform`).
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

open private KBound_precL_of_loss KBound_B_le from RBM3D.BA.KBound

open MeasureTheory ProbabilityTheory Filter Matrix

noncomputable section

namespace RBM.BA

open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes

/-! ## 1. Target 2 (a): the Ward class at every size index -/

section Ward

variable {d : ℕ}

/-- `BAKsol` solves `IsKLoopS` under `BAReal` alone (existence by `baKcac_isKLoopS`; no `0 < g`, no `BAKsolve`). -/
private theorem SEforLnBA_Ksol_isKLoopS {L W : ℕ} [NeZero L] {g κ E : ℝ} {m : ℂ} (hr : BAReal d L g κ E m) :
    IsKLoopS d L W (1 : Matrix (Zd d L) (Zd d L) ℂ) (PropSpin m)
      (BAMLoop d L W (BAMsigma d L (BAMB d L g (E : ℂ) m))) (Set.Ico (0 : ℝ) 1)
      (BAKsol d L W (BAMsigma d L (BAMB d L g (E : ℂ) m)) (PropSpin m)) := by
  have hex : ∃ K : ℝ → LoopIdx (Zd d L) → ℂ, IsKLoopS d L W (1 : Matrix (Zd d L) (Zd d L) ℂ) (PropSpin m)
      (BAMLoop d L W (BAMsigma d L (BAMB d L g (E : ℂ) m))) (Set.Ico (0 : ℝ) 1) K := ⟨_, baKcac_isKLoopS hr⟩
  simp only [BAKsol, hex, ↓reduceDIte]
  exact hex.choose_spec

/-- **Target 2 (a), `baZeroModeGen_wardCls`** (`T2486_BAWardCls`; UN-C3; `lem_WI_K`, `1_2:1034-1046`): the Ward class at every size
index, along every BA flow.  `TL` is the loop of `blockMat (seqHflowBA ..)` at `z_τ = ztOf m E τ`, whose imaginary part is
`η_τ = etaOf m τ`; `TK = BAKsol`, whose rotation and Ward identity are `baK_rotate`, `baK_ward` (the level-2 clause is
`BAKcac_spliced` through `baK_unique`). -/
theorem baZeroModeGen_wardCls (d : ℕ) :
    ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → BAFlow sz κ ε 𝔠 𝔡 z → ZeroModeGen_WardCls sz (baFMz sz z) := by
  intro sz κ ε 𝔠 𝔡 z hκ hflow n τ hτ0 hτ1 ω
  have hr := BAflow_real κ ε 𝔠 𝔡 sz z hflow n
  have hmd := EMn2BA_mF_data sz hflow n
  have hmpos : 0 < (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n).im := lt_of_lt_of_le hκ hmd.1
  have hη : 0 < etaOf (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) τ := mul_pos (by linarith) hmpos
  have hzim : (ztOf (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) (BAflowEs sz z n) τ).im ≠ 0 := by
    rw [ztOf_im]; exact hη.ne'
  have hHerm : (blockMat d (sz.L n) (sz.W n) (sz.seqHflowBA (BAflowLam0 sz z) n τ ω)).IsHermitian :=
    (EMn2BA_seqHflowBA_herm sz (BAflowLam0 sz z) n τ ω).submatrix _
  have hK := SEforLnBA_Ksol_isKLoopS (W := sz.W n) hr
  have hn2 : ∀ t ∈ Set.Ico (0 : ℝ) 1, ∀ (σ : Bool × Bool) (a₁ a₂ : Zd d (sz.L n)),
      BAKsol d (sz.L n) (sz.W n) (BAMsigma d (sz.L n) (BAMB d (sz.L n) (BAflowLam0 sz z n) (BAflowEs sz z n : ℂ)
          (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n)))
        (PropSpin (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n)) t ⟨[σ.1, σ.2], [a₁, a₂]⟩ =
      (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * (BATheta d (sz.L n) (BAflowLam0 sz z n) (BAflowEs sz z n)
          (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) t σ.1 σ.2 *
        BAMss d (sz.L n) (BAMB d (sz.L n) (BAflowLam0 sz z n) (BAflowEs sz z n : ℂ)
          (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n)) σ.1 σ.2) a₁ a₂ := by
    intro t ht σ a₁ a₂
    rw [baK_unique _ _ hK (baKcac_isKLoopS (W := sz.W n) hr) t ht ⟨[σ.1, σ.2], [a₁, a₂]⟩ (by simp [LoopIdx.WF])
      (by simp [LoopIdx.length])]
    exact (BAKcac_spliced (d := d) (L := sz.L n) (W := sz.W n)).2.1 t σ.1 σ.2 a₁ a₂
  refine ⟨loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (sz.seqHflowBA (BAflowLam0 sz z) n τ ω))
      (ztOf (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) (BAflowEs sz z n) τ),
    BAKsol d (sz.L n) (sz.W n) (BAMsigma d (sz.L n) (BAMB d (sz.L n) (BAflowLam0 sz z n) (BAflowEs sz z n : ℂ)
      (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n))) (PropSpin (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n)) τ,
    fun k σ a => ?_, fun k σ a => rfl, ?_, ?_⟩
  · exact loopM_eq_loopL d (sz.L n) (sz.W n) _ _ σ a
  · have := zeroModeGen_loopL_wardFam (blockMat d (sz.L n) (sz.W n) (sz.seqHflowBA (BAflowLam0 sz z) n τ ω))
      (ztOf (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) (BAflowEs sz z n) τ) hHerm hzim
    rwa [ztOf_im] at this
  · refine ⟨fun s b σ a h => baK_rotate _ _ hK τ ⟨hτ0, hτ1⟩ s b σ a h, fun s μ a ha => ?_⟩
    have := baK_ward d (sz.L n) (sz.W n) (BAflowLam0 sz z n) κ (BAflowEs sz z n) (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) hr
      (sz.three_le_L n) (sz.W_pos n) hK hn2 τ ⟨hτ0, hτ1⟩ s μ a ha
    exact this

end Ward

/-! ## 2. Target 2 (b), (c) and target 3: the carrier facts and `SEforLnGen_Facts` -/

section Facts

/-- **Target 2 (b), `baKsol_oneLoop`** (`T2486_BAOneLoop`; `Def_Ktza`, `1_2:988`): the first conjunct of `Step2IterGen_OneLoop (baFMz sz z)`
verbatim (`Chain/Step2IterGen.lean:81-83`; `STmsigg` unfolds to it).  A bridge from T1-BA's `baStep2_oneLoop` (`BA/Step2IterBA.lean:74`),
which is the one `baKsol_one` proof; this file writes no second proof. -/
theorem baKsol_oneLoop (d : ℕ) :
    ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → BAFlow sz κ ε 𝔠 𝔡 z →
      ∀ᶠ n in atTop, ∀ u : ℝ, 0 ≤ u → u < 1 → ∀ (σ : Bool) (a : Zd d (sz.L n)),
        (baFMz sz z).K n u (fun _ : Fin 1 => σ) (fun _ => a) =
          if σ then (baFMz sz z).m n else (starRingEnd ℂ) ((baFMz sz z).m n) :=
  fun sz κ ε 𝔠 𝔡 z hκ hflow => (baStep2_oneLoop sz κ ε 𝔠 𝔡 z hκ hflow).1

/-- **Target 2 (c), `baStep34_LCompat`** (`T2486_BACarrierFacts`, first half; `loopM_eq_loopL`, `Loop/GLoopFlow.lean:127`, holds for any `H`):
`C.L` is the list-indexed loop at the flow matrix, for every `sz, lam0, E` (unguarded: T5-BA's `hC`, `GridGoodGen:853`). -/
theorem baStep34_LCompat (d : ℕ) :
    ∀ (sz : Sizes d) (lam0 E : ℕ → ℝ), Step34Gen_LCompat (baStep2Mat sz lam0 E) (sz.seqHflowBA lam0) := by
  intro sz lam0 E n t k σ a ω
  exact loopM_eq_loopL d (sz.L n) (sz.W n) _ _ σ a

/-- **Target 2 (c), `baStep34_KCompat`** (`T2486_BACarrierFacts`, first half): `C.K` is the list-indexed `𝒦` (`baStep2Mat_KI` is
definitional), for every `sz, lam0, E`. -/
theorem baStep34_KCompat (d : ℕ) :
    ∀ (sz : Sizes d) (lam0 E : ℕ → ℝ), Step34Gen_KCompat (baStep2Mat sz lam0 E) :=
  fun _ _ _ _ _ _ _ _ => rfl

/-- **Target 2 (c), `baStep2Mat_loopForm`** (`T2486_BACarrierFacts`, second half): the loops of `baStep2Mat` are the loops at `ztOf m E u`
(definitional) and `0 < Im m` (`EMn2BA_mF_data`, so under the flow). -/
theorem baStep2Mat_loopForm (d : ℕ) :
    ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → BAFlow sz κ ε 𝔠 𝔡 z →
      StepDecompGen_LoopForm (baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) (BAflowEs sz z) := by
  intro sz κ ε 𝔠 𝔡 z hκ hflow n
  exact ⟨lt_of_lt_of_le hκ (EMn2BA_mF_data sz hflow n).1, fun u H k σ a => rfl, fun u H I => rfl, fun u => rfl⟩

/-- **Target 2 (c), `baStep2Mat_carrierFacts`**: `T2486_BACarrierFacts` verbatim, the conjunction of `baStep34_LCompat`,
`baStep34_KCompat` and `baStep2Mat_loopForm`. -/
theorem baStep2Mat_carrierFacts (d : ℕ) :
    (∀ (sz : Sizes d) (lam0 E : ℕ → ℝ),
      Step34Gen_LCompat (baStep2Mat sz lam0 E) (sz.seqHflowBA lam0) ∧ Step34Gen_KCompat (baStep2Mat sz lam0 E)) ∧
    (∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → BAFlow sz κ ε 𝔠 𝔡 z →
      StepDecompGen_LoopForm (baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) (BAflowEs sz z)) :=
  ⟨fun sz lam0 E => ⟨baStep34_LCompat d sz lam0 E, baStep34_KCompat d sz lam0 E⟩, baStep2Mat_loopForm d⟩

/-- **Target 2 (c), `baStep5CasesGen_flowFacts`** (`T2486_BAFlowFacts`; `T2462_FlowFacts`): `κm = κ`, `EMn2BA_T0_lt_one`, `EMn2BA_mF_data`, the `eta`
field of `baFM`. -/
theorem baStep5CasesGen_flowFacts (d : ℕ) :
    Step5CasesGen_FlowFacts d (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) (fun sz z => baFMz sz z)
      (fun sz z => BAflowT0 sz z) := by
  intro κ hκ
  refine ⟨κ, hκ, ?_⟩
  intro sz ε 𝔠 𝔡 z hflow
  exact ⟨hflow.1, fun n => EMn2BA_T0_lt_one hκ sz hflow n, fun n => (EMn2BA_mF_data sz hflow n).1, fun n t => rfl⟩

/-- **Target 3, `baSEforLnGen_facts`** (`T2486_BASEforLnFacts`): `SEforLnGen_Facts` at the BA tuple, every `d`.  The loop form, the
compatibilities and the Ward class are target 2; the matrix `S = 1` has row and column sums `1` and the diagonal as support; `Im m ≤ 1`
is `EMn2BA_mF_data`; the one-loop value is target 2 (b). -/
theorem baSEforLnGen_facts (d : ℕ) :
    SEforLnGen_Facts d (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z)
      (fun sz z => baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) (fun sz z => sz.seqHflowBA (BAflowLam0 sz z)) := by
  intro sz κ ε 𝔠 𝔡 z hκ hflow
  have hS : ∀ n, (baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)).S n = (1 : Matrix (Zd d (sz.L n)) (Zd d (sz.L n)) ℂ) :=
    fun n => rfl
  refine ⟨⟨BAflowEs sz z, baStep2Mat_loopForm d sz κ ε 𝔠 𝔡 z hκ hflow⟩,
    fun n τ ω => EMn2BA_seqHflowBA_herm sz (BAflowLam0 sz z) n τ ω, baStep34_LCompat d sz _ _,
    baStep34_KCompat d sz _ _, baZeroModeGen_wardCls d sz κ ε 𝔠 𝔡 z hκ hflow, fun n a => ?_, fun n b => ?_,
    fun n a b hab => ?_, fun n => (EMn2BA_mF_data sz hflow n).2, baKsol_oneLoop d sz κ ε 𝔠 𝔡 z hκ hflow⟩
  · rw [hS n]
    have h : ∀ b, ‖(1 : Matrix (Zd d (sz.L n)) (Zd d (sz.L n)) ℂ) a b‖ = if a = b then (1 : ℝ) else 0 := fun b => by
      by_cases hab : a = b <;> simp [Matrix.one_apply, hab]
    simp [h]
  · rw [hS n]
    have h : ∀ a, ‖(1 : Matrix (Zd d (sz.L n)) (Zd d (sz.L n)) ℂ) a b‖ = if a = b then (1 : ℝ) else 0 := fun a => by
      by_cases hab : a = b <;> simp [Matrix.one_apply, hab]
    simp [h]
  · rw [hS n] at hab
    have hab' : a = b := by
      by_contra h
      exact hab (by simp [Matrix.one_apply, h])
    subst hab'
    rw [sub_self]
    exact ((zdistInf_le_zdistD d _ _).trans_eq (zdistD_zero d _)).trans (Nat.zero_le _)

end Facts

/-! ## 3. Target 4: `lem:SEforLn` at the BA carrier -/

section SEforLn

/-- **Target 4 (a), `baSEforLnConclgL_of`** (conclusion head `STSEforLnConclgL`; paper `lem:SEforLn` `3_5:1017`, `lem:main_ind_BA` `7_8:1825`):
`stSEforLnConclgL_of` at the BA tuple, per carrier.  The carrier facts are `baSEforLnGen_facts`, `STKwardgL` is `baKward_holds`; only the Step 2
conclusions `STStep2ConclgL (baFMz sz z) ..` (T1-BA), `(con_st_ind)` with `𝔠_d C_d ≤ 1/30` and the times stay hypotheses. -/
theorem baSEforLnConclgL_of (d : ℕ) (hd : 3 ≤ d) (sz : Sizes d) (κ ε 𝔠 𝔡 Cd 𝔠d : ℝ) (z : ℕ → ℂ) (s t : ℕ → ℝ)
    (hκ : 0 < κ) (hε : 0 < ε) (hflow : BAFlow sz κ ε 𝔠 𝔡 z) (hCd : 0 < Cd) (h𝔠d : 0 < 𝔠d) (hcc : 𝔠d * Cd ≤ 1 / 30)
    (hs0 : ∀ n, 0 ≤ s n) (hst : ∀ n, s n < t n) (ht1 : ∀ n, t n < 1) (hcon : sz.STConStInd 𝔠d s t)
    (hStep2 : STStep2ConclgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) s t Cd) :
    STSEforLnConclgL (baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) (sz.seqHflowBA (BAflowLam0 sz z))
      (Sizes.seqP (sz.withLam 0)) s t := by
  obtain ⟨κm, hκm, hF⟩ := baStep5CasesGen_flowFacts d κ hκ
  obtain ⟨hA, -, hmκ, hη⟩ := hF sz ε 𝔠 𝔡 z hflow
  obtain ⟨⟨E, hloop⟩, hherm, hL, hK, hward, hrow, hcol, hsupp, him, hone⟩ := baSEforLnGen_facts d sz κ ε 𝔠 𝔡 z hκ hflow
  exact stSEforLnConclgL_of hd sz (baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) (sz.seqHflowBA (BAflowLam0 sz z))
    (Sizes.seqP (sz.withLam 0)) κm 𝔠 𝔡 Cd 𝔠d E s t ⟨hκm, hmκ, hη⟩ hA hloop hherm hL hK hward hrow hcol hsupp him hone hCd h𝔠d
    hcc hs0 hst ht1 hcon (baKward_holds d hd κ ε 𝔡 hκ hε hflow.1.2.1 𝔠 sz z hflow) hStep2

/-- **Target 4 (b), `BASEforLn`** (`T2486_BASEforLn`; the shape of `Chain/Step34GenTw.lean:89`): `lem:SEforLn` as an ingredient pin at the
BA tuple, for every regime `R` (the proof reads none). -/
def BASEforLn (d : ℕ) : Prop :=
  ∀ (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop),
    STSEforLngL d R (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z)
      (fun sz z => baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) (fun sz z => sz.seqHflowBA (BAflowLam0 sz z))
      (fun sz z => BAflowT0 sz z)

/-- **`BASEforLn` is proved, unconditionally** (`stSEforLngL_of` with the flow facts `baStep5CasesGen_flowFacts` and the carrier facts
`baSEforLnGen_facts`; no hypothesis of another gate). -/
theorem baSEforLn_holds (d : ℕ) : BASEforLn d := fun R =>
  stSEforLngL_of d R (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z)
    (fun sz z => baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) (fun sz z => sz.seqHflowBA (BAflowLam0 sz z))
    (fun sz z => BAflowT0 sz z) (fun sz => Sizes.isProbabilityMeasure_seqP (sz.withLam 0))
    (baStep5CasesGen_flowFacts d) (baSEforLnGen_facts d)

end SEforLn

/-! ## 5. Target 5: the label decays of the four `ℰ`-terms at BA -/

section Eterm

/-- `ML:Kbound` at BA without `0 < ε` (the `hEK` shape of `gridGoodNgL_of` has no `ε`): a private copy of the reduction `BAKbound_of_uniform`
(`BA/KBound.lean:213-244`), whose body reads `0 < 𝔡` (`BAFlow` gives it) and never `0 < ε`. -/
private theorem SEforLnBA_Kbound (d : ℕ) (hd : 3 ≤ d) (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ) (hκ : 0 < κ)
    (hflow : BAFlow sz κ ε 𝔠 𝔡 z) : STKboundgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) := by
  have h𝔡 : 0 < 𝔡 := hflow.1.2.1
  intro τ hτ0 hτ1 k hk
  have hB : ∀ n, 0 ≤ sz.Bctl n (τ n) := fun n => by
    unfold Sizes.Bctl Bparam
    positivity
  refine KBound_precL_of_loss sz _ (by omega) hflow.1.2.2.1 (fun n u ω => pow_nonneg (hB n) _) ?_
  intro s hs
  obtain ⟨C, hC, H⟩ := baKBoundAt_holds d hd (inv_pos.2 h𝔡) hκ k hk s hs
  refine ⟨C * ((κ + 1) / κ) ^ (k - 1), by positivity, ?_⟩
  filter_upwards [BAflow_lam0_window κ ε 𝔠 𝔡 sz z hflow] with n hn
  intro u ω
  have : NeZero (sz.L n) := ⟨by have := sz.three_le_L n; omega⟩
  have hreal := BAflow_real κ ε 𝔠 𝔡 sz z hflow n
  have hbd := H (sz.L n) (sz.three_le_L n) (sz.W n) (sz.W_pos n) (BAflowLam0 sz z n) hn.1 hn.2
    (BAflowEs sz z n) _ hreal (τ n) (hτ0 n) (hτ1 n) u.1 u.2
  have hstep := KBound_B_le hκ sz hflow n (hτ1 n)
  have hpow := pow_le_pow_left₀ (by unfold Bparam; positivity) hstep (k - 1)
  have hLs : 0 ≤ ((sz.L n : ℕ) : ℝ) ^ s := Real.rpow_nonneg (Nat.cast_nonneg _) s
  change ‖BAKsol d (sz.L n) (sz.W n)
      (BAMsigma d (sz.L n) (BAMB d (sz.L n) (BAflowLam0 sz z n) (BAflowEs sz z n : ℂ)
        (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n)))
      (PropSpin (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n)) (τ n) (KLloopOf d (sz.L n) u.1 u.2)‖ ≤ _
  refine hbd.trans ?_
  calc C * ((sz.L n : ℕ) : ℝ) ^ s *
        ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * Bparam d (sz.L n) (BAflowLam0 sz z n) (τ n) 0) ^ (k - 1)
      ≤ C * ((sz.L n : ℕ) : ℝ) ^ s * (((κ + 1) / κ) * sz.Bctl n (τ n)) ^ (k - 1) :=
        mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = C * ((κ + 1) / κ) ^ (k - 1) * ((sz.L n : ℕ) : ℝ) ^ s * sz.Bctl n (τ n) ^ (k - 1) := by
        rw [mul_pow]; ring

/-- **Target 5, `baEtermDecaygL`** (`T2486_BAEtermDecay`; paper `3_5:1133`; conclusion the four label decays of `stEtermDecaygL`, the text of
`T2480_EtermDecay`): the `hEK` shape of `gridGoodNgL_of` (`Chain/GridGoodGen.lean:857-868`) at the BA tuple.  `STKcalDecaygL` is
`baKcalDecay_holds` (target 1), `STKboundgL` the ε-free `SEforLnBA_Kbound`, the carrier facts are target 3; `STDecayLoopUgL` is the
consumer's input (T7-BA proves it at BA from `STGdecayWgL` and target 1). -/
theorem baEtermDecaygL (d : ℕ) :
    3 ≤ d → ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → BAFlow sz κ ε 𝔠 𝔡 z → ∀ s t : ℕ → ℝ,
      (∀ n, 0 ≤ s n) → (∀ n, s n ≤ t n) → (∀ n, t n < 1) →
      STDecayLoopUgL (baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)).toFlowFM (Sizes.seqP (sz.withLam 0)) s t →
      ∀ k : ℕ, 2 ≤ k → ∀ σ : Fin k → Bool,
        STEKDecaygL (sz := sz) (Sizes.seqP (sz.withLam 0)) s t (m := k)
            (fun n v ω (a : Fin k → Zd d (sz.L n)) =>
              STegtg (baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) (sz.seqHflowBA (BAflowLam0 sz z)) n (v : ℝ) ω
                ⟨List.ofFn σ, List.ofFn a⟩) ∧
          (∀ l : ℕ, STEKDecaygL (sz := sz) (Sizes.seqP (sz.withLam 0)) s t (m := k)
            (fun n v ω (a : Fin k → Zd d (sz.L n)) =>
              STksimLKg (baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) (sz.seqHflowBA (BAflowLam0 sz z)) n (v : ℝ) ω l
                ⟨List.ofFn σ, List.ofFn a⟩)) ∧
          STEKDecaygL (sz := sz) (Sizes.seqP (sz.withLam 0)) s t (m := k)
            (fun n v ω (a : Fin k → Zd d (sz.L n)) =>
              STelklkg (baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) (sz.seqHflowBA (BAflowLam0 sz z)) n (v : ℝ) ω
                ⟨List.ofFn σ, List.ofFn a⟩) ∧
          STEKDecaygL (sz := sz) (Sizes.seqP (sz.withLam 0)) s t (m := k + k)
            (fun n v ω (b : Fin (k + k) → Zd d (sz.L n)) =>
              STeeg (baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) (sz.seqHflowBA (BAflowLam0 sz z)) n (v : ℝ) ω σ
                (fun i => b (Fin.castAdd k i)) (fun i => b (Fin.natAdd k i))) := by
  intro hd sz κ ε 𝔠 𝔡 z hκ hflow s t hs0 hst ht1 hU
  obtain ⟨κm, hκm, hF⟩ := baStep5CasesGen_flowFacts d κ hκ
  obtain ⟨hA, -, hmκ, hη⟩ := hF sz ε 𝔠 𝔡 z hflow
  obtain ⟨⟨E, hloop⟩, hherm, hL, hK, -, hrow, -, hsupp, -, hone⟩ := baSEforLnGen_facts d sz κ ε 𝔠 𝔡 z hκ hflow
  exact stEtermDecaygL hd sz (baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) (sz.seqHflowBA (BAflowLam0 sz z))
    (Sizes.seqP (sz.withLam 0)) κm 𝔠 𝔡 E s t ⟨hκm, hmκ, hη⟩ hA hloop hherm hs0 hst ht1 hL hK hrow hsupp hone
    (SEforLnBA_Kbound d hd sz κ ε 𝔠 𝔡 z hκ hflow) (baKcalDecay_holds d hd sz κ ε 𝔠 𝔡 z hκ hflow) hU

end Eterm

/-! ## 6. Compiled nonempty instances (targets 2-5)

`d = 3`, the preflight sequence `sz0` (`L = 4(n+1)`, `W = (2(n+1))^5`, `lam = (2(n+1))^{-6}`), the spectral parameters `zSeq` with
`flow_sz0 : BAFlow sz0 (1/2) (1/10) (1/6) (1/10) zSeq` (`BA/FlowPins.lean:1214`), the windows `s ≡ 1/10 < t ≡ 1/2`, `𝔠_d = 1/100`,
`C_d = 1` (`𝔠_d C_d ≤ 1/30`), `(con_st_ind)` from `s1Setup_conStInd_const`.  Every deterministic premise is discharged; the inputs
that stay hypotheses are the Step 2 conclusions `STStep2ConclgL` (T1-BA's pin) and the consumer's `STDecayLoopUgL` (T7-BA). -/

namespace SEforLnBAInst

open RBM.Gauss.SizesInst RBM.BA.FlowPinsInst

/-- **Target 2 (a)** at the data: the Ward class of `baFMz sz0 zSeq`, every size index. -/
theorem inst_wardCls : ZeroModeGen_WardCls sz0 (baFMz sz0 zSeq) :=
  baZeroModeGen_wardCls 3 sz0 (1 / 2) (1 / 10) (1 / 6) (1 / 10) zSeq (by norm_num) flow_sz0

/-- **Target 2 (b)** at the data: the one-loop value of `baFMz sz0 zSeq`, eventually in `n`. -/
theorem inst_oneLoop :
    ∀ᶠ n in atTop, ∀ u : ℝ, 0 ≤ u → u < 1 → ∀ (σ : Bool) (a : Zd 3 (sz0.L n)),
      (baFMz sz0 zSeq).K n u (fun _ : Fin 1 => σ) (fun _ => a) =
        if σ then (baFMz sz0 zSeq).m n else (starRingEnd ℂ) ((baFMz sz0 zSeq).m n) :=
  baKsol_oneLoop 3 sz0 (1 / 2) (1 / 10) (1 / 6) (1 / 10) zSeq (by norm_num) flow_sz0

/-- **Target 2 (c)** at the data: the compatibilities (unguarded) and the loop form (under the flow). -/
theorem inst_carrierFacts :
    (Step34Gen_LCompat (baStep2Mat sz0 (BAflowLam0 sz0 zSeq) (BAflowEs sz0 zSeq)) (sz0.seqHflowBA (BAflowLam0 sz0 zSeq)) ∧
      Step34Gen_KCompat (baStep2Mat sz0 (BAflowLam0 sz0 zSeq) (BAflowEs sz0 zSeq))) ∧
    StepDecompGen_LoopForm (baStep2Mat sz0 (BAflowLam0 sz0 zSeq) (BAflowEs sz0 zSeq)) (BAflowEs sz0 zSeq) :=
  ⟨(baStep2Mat_carrierFacts 3).1 sz0 _ _,
    (baStep2Mat_carrierFacts 3).2 sz0 (1 / 2) (1 / 10) (1 / 6) (1 / 10) zSeq (by norm_num) flow_sz0⟩

/-- **Target 2 (c), flow facts** at the data: some `κm > 0` and the four facts for `sz0`, `zSeq`. -/
theorem inst_flowFacts : ∃ κm : ℝ, 0 < κm ∧ sz0.Admissible (1 / 6) (1 / 10) ∧ (∀ n, BAflowT0 sz0 zSeq n < 1) ∧
    (∀ n, κm ≤ ((baFMz sz0 zSeq).m n).im) ∧
      ∀ (n : ℕ) (t : ℝ), (baFMz sz0 zSeq).eta n t = (1 - t) * ((baFMz sz0 zSeq).m n).im := by
  obtain ⟨κm, hκm, hF⟩ := baStep5CasesGen_flowFacts 3 (1 / 2) (by norm_num)
  exact ⟨κm, hκm, hF sz0 (1 / 10) (1 / 6) (1 / 10) zSeq flow_sz0⟩

/-- **Target 3** at the data: `SEforLnGen_Facts` unfolded at `sz0`, `zSeq`. -/
example := baSEforLnGen_facts 3 sz0 (1 / 2) (1 / 10) (1 / 6) (1 / 10) zSeq (by norm_num) flow_sz0

/-- **Target 4 (a)** at the data: `STSEforLnConclgL` for `sz0`, `zSeq`, `s ≡ 1/10 < t ≡ 1/2`, `𝔠_d = 1/100`, `C_d = 1`; only the Step 2
conclusions stay a hypothesis. -/
theorem inst_seforLnConclgL (hStep2 : STStep2ConclgL (baFMz sz0 zSeq) (Sizes.seqP (sz0.withLam 0))
      (fun _ => 1 / 10) (fun _ => 1 / 2) 1) :
    STSEforLnConclgL (baStep2Mat sz0 (BAflowLam0 sz0 zSeq) (BAflowEs sz0 zSeq)) (sz0.seqHflowBA (BAflowLam0 sz0 zSeq))
      (Sizes.seqP (sz0.withLam 0)) (fun _ => 1 / 10) (fun _ => 1 / 2) :=
  baSEforLnConclgL_of 3 le_rfl sz0 (1 / 2) (1 / 10) (1 / 6) (1 / 10) 1 (1 / 100) zSeq (fun _ => 1 / 10) (fun _ => 1 / 2)
    (by norm_num) (by norm_num) flow_sz0 (by norm_num) (by norm_num) (by norm_num) (fun _ => by norm_num)
    (fun _ => by norm_num) (fun _ => by norm_num)
    (RBM.Ind.Step1SetupInst.s1Setup_conStInd_const (by norm_num) (by norm_num) (by norm_num)) hStep2

/-- **Target 4 (b)** at the data (`d = 3`, the trivial regime `STAny`): unconditional. -/
theorem inst_baSEforLn : STSEforLngL 3 STAny (fun sz => Sizes.seqP (sz.withLam 0))
    (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) (fun sz z => baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z))
    (fun sz z => sz.seqHflowBA (BAflowLam0 sz z)) (fun sz z => BAflowT0 sz z) :=
  baSEforLn_holds 3 STAny

/-- **Target 5** at the data: the four label decays at `k = 3`, `σ = (+,-,+)`, for `sz0`, `zSeq`, `s ≡ 1/10 ≤ t ≡ 1/2`; only the
consumer's `STDecayLoopUgL` stays a hypothesis. -/
example
    (hU : STDecayLoopUgL (baStep2Mat sz0 (BAflowLam0 sz0 zSeq) (BAflowEs sz0 zSeq)).toFlowFM
      (Sizes.seqP (sz0.withLam 0)) (fun _ => 1 / 10) (fun _ => 1 / 2)) :=
  baEtermDecaygL 3 le_rfl sz0 (1 / 2) (1 / 10) (1 / 6) (1 / 10) zSeq (by norm_num) flow_sz0 (fun _ => 1 / 10) (fun _ => 1 / 2)
    (fun _ => by norm_num) (fun _ => by norm_num) (fun _ => by norm_num) hU 3 (by norm_num) ![true, false, true]

end SEforLnBAInst

end RBM.BA

end
