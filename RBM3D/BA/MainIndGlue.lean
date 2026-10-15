/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.BA.MainIndOutBA
import RBM3D.Induction.MainIndRegimes

/-!
# V row V2b (T2512): the regime glue of `lem:main_ind_BA` in family form with TL2

`BAMainIndFamTL d STAny` (`BA/MainIndOutBA.lean:60`) from the four regime steps
`BAMainIndFamTL d R`, `R ∈ {STReg5III, STReg5I, STReg5II, STReg5IV}`, at the BA tuple
`(fun sz => seqP (sz.withLam 0), BAFlow, baFMz, BAflowT0)`.  The family twin of the merged band
glue `ST_mainInd_of_regimes` (`Induction/MainIndRegimes.lean:616`); the pattern layer
(`STPattern`, `STRegChain_of_class`), the subsequence layer (`Induction/SizesComp`) and
`nth_cover` carry no carrier and are used verbatim.

* `baMainIndFamTL_mono`: a smaller regime (`STMainIndR_mono`, `MainIndRegimes:105`).
* `baMainIndFamTL_seq`: two stages `[s, m]`, `[m, t]` (`STRegSeq`; probe `BA_mainInd_compose`,
  `t/T2205:2462`).
* `baMainIndFamTL_chain`: every chain of stages (`STRegChain`).
* `baMainIndFamTL_of_regimes`: the glue along the `Nat.nth` classes of `STPattern`; one constant by
  `Finset.inf'`.
* private `MainIndGlue_extendMember`, `MainIndGlue_down`, `MainIndGlue_up`: a member of the family
  along a class, extended by the main flow; the six hypotheses go down and the seven conclusions
  come back (`stochDomAt_iff_comp_cover`).
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.setOption false
set_option linter.flexible false

open MeasureTheory Filter

noncomputable section

namespace RBM.BA
open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes

/-! ## 1. Smaller regime, two stages, chains of stages -/

/-- **A smaller regime** (twin of `STMainIndR_mono`, `MainIndRegimes:105`): `R' ⊆ R` and `BAMainIndFamTL d R` give `BAMainIndFamTL d R'`. -/
theorem baMainIndFamTL_mono (d : ℕ) (R R' : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop)
    (hRR : ∀ (sz : Sizes d) (s t : ℕ → ℝ), R' sz s t → R sz s t) (h : BAMainIndFamTL d R) : BAMainIndFamTL d R' := by
  intro hd κ ε 𝔡 hκ hε h𝔡
  obtain ⟨c, hc, hc', H⟩ := h hd κ ε 𝔡 hκ hε h𝔡
  exact ⟨c, hc, hc', fun 𝔠 sz z hf hlam c₁ hc₁ hc₁' hwin s t hs0 hsT hst htT hR' hyp hcon =>
    H 𝔠 sz z hf hlam c₁ hc₁ hc₁' hwin s t hs0 hsT hst htT (hRR sz s t hR') hyp hcon⟩

/-- **Two stages** `[s, m]`, `[m, t]` (twin of `ST_mainIndR_seq`, `MainIndRegimes:289`; probe `BA_mainInd_compose`, `t/T2205:2462`, with TL2):
the seven conclusions of stage 1 at `m`, for every member of `Fam(m)`, give the six hypotheses of stage 2
(`STLocalMaxgL_of_STLocalEntrygL`); `(con_st_ind)` passes to both pieces (`st_conStInd_sub`) and to the smaller exponent
(`st5_conStInd_mono`); the constant is `min c₁ c₂`; `t < 1` by `BAflow_T0_bounds`. -/
theorem baMainIndFamTL_seq (d : ℕ) (R₁ R₂ : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop)
    (h₁ : BAMainIndFamTL d R₁) (h₂ : BAMainIndFamTL d R₂) : BAMainIndFamTL d (STRegSeq R₁ R₂) := by
  intro hd κ ε 𝔡 hκ hε h𝔡
  obtain ⟨a₁, ha₁, ha₁', H₁⟩ := h₁ hd κ ε 𝔡 hκ hε h𝔡
  obtain ⟨a₂, ha₂, -, H₂⟩ := h₂ hd κ ε 𝔡 hκ hε h𝔡
  have hapos : 0 < min a₁ a₂ := lt_min ha₁ ha₂
  refine ⟨min a₁ a₂, hapos, (min_le_left _ _).trans ha₁', fun 𝔠 sz z hflow hlam c₁ hc₁ hc₁' hwin s t hs0 hsT hst htT hR hyp hcon => ?_⟩
  obtain ⟨m, hsm, hmt, hR₁, hR₂⟩ := hR
  have ht1 : ∀ n, t n < 1 := fun n => (htT n).trans_lt (BAflow_T0_bounds hκ hflow n).2.2.2
  have hm1 : ∀ n, m n < 1 := fun n => (hmt n).trans (ht1 n)
  have hmT : ∀ n, m n ≤ BAflowT0 sz z n := fun n => (hmt n).le.trans (htT n)
  have hcon₁ : sz.STConStInd (min a₁ a₂) s m :=
    st_conStInd_sub sz hapos hcon (fun n => le_rfl) hsm (fun n => (hmt n).le) ht1
  have hcon₂ : sz.STConStInd (min a₁ a₂) m t :=
    st_conStInd_sub sz hapos hcon (fun n => (hsm n).le) hmt (fun n => le_rfl) ht1
  have stage1 := H₁ 𝔠 sz z hflow hlam c₁ hc₁ hc₁' hwin s m hs0 hsT hsm hmT hR₁ hyp
    (st5_conStInd_mono sz hcon₁ hm1 hapos (min_le_left _ _))
  exact H₂ 𝔠 sz z hflow hlam c₁ hc₁ hc₁' hwin m t (fun n => (hs0 n).trans (hsm n).le) hmT hmt htT hR₂
    (fun z' hz' => by
      obtain ⟨b1, -, b3, b4, b5, b6, b7⟩ := stage1 z' hz'
      exact ⟨b1, b3, b6, STLocalMaxgL_of_STLocalEntrygL _ _ _ b5, b4, b7⟩)
    (st5_conStInd_mono sz hcon₂ ht1 hapos (min_le_right _ _))

/-- **Every chain of stages** `STRegChain i m`, `i + m ≤ 3`, from the four regime steps: induction on `m` by
`baMainIndFamTL_seq` (`STRegChain_succ` is `Iff.rfl`); `STRegK k` is one of the four for `k ≤ 3`. -/
theorem baMainIndFamTL_chain (d : ℕ) (h₃ : BAMainIndFamTL d STReg5III) (h₁ : BAMainIndFamTL d STReg5I)
    (h₂ : BAMainIndFamTL d STReg5II) (h₄ : BAMainIndFamTL d STReg5IV) :
    ∀ m i : ℕ, i + m ≤ 3 → BAMainIndFamTL d (STRegChain i m) := by
  have hk : ∀ k, k ≤ 3 → BAMainIndFamTL d (STRegK k) := by
    intro k hk
    interval_cases k
    exacts [h₃, h₁, h₂, h₄]
  intro m
  induction m with
  | zero => intro i hi; exact hk i (by omega)
  | succ m ih =>
    intro i hi
    exact baMainIndFamTL_seq d (STRegK i) (STRegChain (i + 1) m) (hk i (by omega)) (ih (i + 1) (by omega))

/-! ## 2. A member of the family along a class, extended by the main flow (probe `BAFamZ_extend`, `t/T2205:3086`) -/

/-- **A member of the family along a subsequence, extended by the main flow** (probe `BAFamZ_extend`, `t/T2205:3086`;
`Function.extend` replaces the probe's `BAextend`): on `range φ` the condition is that of `z''` at `j`
(`Function.Injective.extend_apply`), off it that of the main flow (`Function.extend_apply'`, `BAFamZ_main`). -/
private theorem MainIndGlue_extendMember {d : ℕ} (sz : Sizes d) (z : ℕ → ℂ) (c₁ : ℝ) (u : ℕ → ℝ) (φ : ℕ → ℕ)
    (hφ : StrictMono φ) (z'' : ℕ → ℂ) (h : BAFamZ (sz.comp φ) (fun j => z (φ j)) c₁ (fun j => u (φ j)) z'') :
    BAFamZ sz z c₁ u (Function.extend φ z'' z) := by
  intro n
  by_cases hn : n ∈ Set.range φ
  · obtain ⟨j, rfl⟩ := hn
    have e : Function.extend φ z'' z (φ j) = z'' j := hφ.injective.extend_apply z'' z j
    have e2 : BAflowEs sz (Function.extend φ z'' z) (φ j) = BAflowEs (sz.comp φ) z'' j := by
      unfold BAflowEs; rw [e]; rfl
    have e3 : BAflowT0 sz (Function.extend φ z'' z) (φ j) = BAflowT0 (sz.comp φ) z'' j := by
      unfold BAflowT0; rw [e]; rfl
    rw [e2, e3]
    exact h j
  · have e : Function.extend φ z'' z n = z n := Function.extend_apply' _ _ _ (fun ⟨a, ha⟩ => hn ⟨a, ha⟩)
    rw [BAflowEs_congr sz e, BAflowT0_congr sz e]
    exact BAFamZ_main sz z c₁ u n

/-! ## 3. The transports along a finite cover (`stochDomAt_iff_comp_cover`, `SizesComp:536`) -/

/-- `≺` under `seqP (sz.withLam 0)` iff `≺` under every `seqP ((sz.comp (φ k)).withLam 0)` along a finite cover
(`stochDomAt_iff_comp_cover` at `μ = seqP (sz.withLam 0)`, `ν k = seqP ((sz.comp (φ k)).withLam 0)`, `hlaw` by
`seqP_withLam_reindex_preimage`, `SizesComp:239`). -/
private theorem MainIndGlue_precIff {d : ℕ} (sz : Sizes d) {ι : Type} [Finite ι] (φ : ι → ℕ → ℕ) (hφ : ∀ k, StrictMono (φ k))
    (hcov : ∀ᶠ n in atTop, ∃ k, n ∈ Set.range (φ k)) {U : ℕ → Type} (ξ ζ : ∀ n, U n → sz.SeqΩ → ℝ)
    (ξ' ζ' : ∀ k j, U (φ k j) → (sz.comp (φ k)).SeqΩ → ℝ)
    (hξ : ∀ k j u ω, ξ' k j u (reindex sz (φ k) ω) = ξ (φ k j) u ω)
    (hζ : ∀ k j u ω, ζ' k j u (reindex sz (φ k) ω) = ζ (φ k j) u ω) :
    PrecL sz (seqP (sz.withLam 0)) ξ ζ ↔
      ∀ k, PrecL (sz.comp (φ k)) (seqP ((sz.comp (φ k)).withLam 0)) (U := fun j => U (φ k j)) (ξ' k) (ζ' k) :=
  Sizes.stochDomAt_iff_comp_cover sz (seqP (sz.withLam 0)) φ (fun k => seqP ((sz.comp (φ k)).withLam 0)) hφ hcov
    (fun k s => seqP_withLam_reindex_preimage sz (φ k) 0 (hφ k).injective s) ξ ζ ξ' ζ' hξ hζ

/-- The `STExp2gL` left side integrates over the whole law and transfers by `integral_reindex` (`SizesComp:253`; as `baConclShift`,
`MainIndOutBA:172`). -/
private theorem MainIndGlue_exp2_eq {d : ℕ} (sz : Sizes d) (φ : ℕ → ℕ) (hφ : StrictMono φ) (z : ℕ → ℂ) (τ : ℕ → ℝ) (j : ℕ)
    (u : (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L (φ j)))) :
    ‖(∫ ω, (baFMz (sz.comp φ) fun j => z (φ j)).L j (τ (φ j)) u.1 u.2 ω ∂(seqP ((sz.comp φ).withLam 0))) -
        (baFMz (sz.comp φ) fun j => z (φ j)).K j (τ (φ j)) u.1 u.2‖ =
      ‖(∫ ω, (baFMz sz z).L (φ j) (τ (φ j)) u.1 u.2 ω ∂(seqP (sz.withLam 0))) - (baFMz sz z).K (φ j) (τ (φ j)) u.1 u.2‖ :=
  congrArg (fun x : ℂ => ‖x - (baFMz (sz.comp φ) fun j => z (φ j)).K j (τ (φ j)) u.1 u.2‖)
    (Sizes.integral_reindex (sz.withLam 0) φ hφ.injective
      (fun ω₁ => (baFMz (sz.comp φ) fun j => z (φ j)).L j (τ (φ j)) u.1 u.2 ω₁)).symm

/-! Each predicate along the cover: one `stochDomAt_iff_comp_cover` (through `MainIndGlue_precIff`) per predicate; the families
`ξ`, `ζ` are the predicate's own, and every per-`n` object of `baFMz` commutes with `reindex` by `rfl`. -/

private theorem MainIndGlue_LK_iff {d : ℕ} (sz : Sizes d) (z : ℕ → ℂ) (τ : ℕ → ℝ) {ι : Type} [Finite ι] (φ : ι → ℕ → ℕ)
    (hφ : ∀ k, StrictMono (φ k)) (hcov : ∀ᶠ n in atTop, ∃ k, n ∈ Set.range (φ k)) :
    STLKgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) τ ↔
      ∀ k, STLKgL (baFMz (sz.comp (φ k)) fun j => z (φ k j)) (Sizes.seqP ((sz.comp (φ k)).withLam 0)) (fun j => τ (φ k j)) := by
  have P := fun (m : ℕ) => MainIndGlue_precIff sz φ hφ hcov (U := fun n => (Fin m → Bool) × (Fin m → Zd d (sz.L n)))
    (fun n p ω => ‖(baFMz sz z).L n (τ n) p.1 p.2 ω - (baFMz sz z).K n (τ n) p.1 p.2‖) (fun n _ _ => sz.Bctl n (τ n) ^ m)
    (fun k j p ω => ‖(baFMz (sz.comp (φ k)) fun j => z (φ k j)).L j (τ (φ k j)) p.1 p.2 ω -
      (baFMz (sz.comp (φ k)) fun j => z (φ k j)).K j (τ (φ k j)) p.1 p.2‖) (fun k j _ _ => (sz.comp (φ k)).Bctl j (τ (φ k j)) ^ m)
    (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl)
  exact ⟨fun h k m hm => (P m).1 (h m hm) k, fun h m hm => (P m).2 fun k => h k m hm⟩

private theorem MainIndGlue_Lmax_iff {d : ℕ} (sz : Sizes d) (z : ℕ → ℂ) (τ : ℕ → ℝ) {ι : Type} [Finite ι] (φ : ι → ℕ → ℕ)
    (hφ : ∀ k, StrictMono (φ k)) (hcov : ∀ᶠ n in atTop, ∃ k, n ∈ Set.range (φ k)) :
    STLmaxgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) τ ↔
      ∀ k, STLmaxgL (baFMz (sz.comp (φ k)) fun j => z (φ k j)) (Sizes.seqP ((sz.comp (φ k)).withLam 0)) (fun j => τ (φ k j)) := by
  have P := fun (m : ℕ) => MainIndGlue_precIff sz φ hφ hcov (U := fun n => (Fin m → Bool) × (Fin m → Zd d (sz.L n)))
    (fun n p ω => ‖(baFMz sz z).L n (τ n) p.1 p.2 ω‖) (fun n _ _ => sz.Bctl n (τ n) ^ (m - 1))
    (fun k j p ω => ‖(baFMz (sz.comp (φ k)) fun j => z (φ k j)).L j (τ (φ k j)) p.1 p.2 ω‖)
    (fun k j _ _ => (sz.comp (φ k)).Bctl j (τ (φ k j)) ^ (m - 1)) (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl)
  exact ⟨fun h k m hm => (P m).1 (h m hm) k, fun h m hm => (P m).2 fun k => h k m hm⟩

private theorem MainIndGlue_Decay_iff {d : ℕ} (sz : Sizes d) (z : ℕ → ℂ) (τ : ℕ → ℝ) {ι : Type} [Finite ι] (φ : ι → ℕ → ℕ)
    (hφ : ∀ k, StrictMono (φ k)) (hcov : ∀ᶠ n in atTop, ∃ k, n ∈ Set.range (φ k)) :
    STDecaygL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) τ ↔
      ∀ k, STDecaygL (baFMz (sz.comp (φ k)) fun j => z (φ k j)) (Sizes.seqP ((sz.comp (φ k)).withLam 0)) (fun j => τ (φ k j)) := by
  have P := fun (D : ℝ) => MainIndGlue_precIff sz φ hφ hcov (U := fun n => (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)))
    (fun n p ω => ‖(baFMz sz z).L n (τ n) p.1 p.2 ω - (baFMz sz z).K n (τ n) p.1 p.2‖)
    (fun n p _ => (sz.Bctl n (τ n)) ^ (1 / 5 : ℝ) * STWB sz n (τ n) (zdistInf d (sz.L n) (p.2 0 - p.2 1)) *
        Real.exp (-(((zdistInf d (sz.L n) (p.2 0 - p.2 1) : ℕ) : ℝ) / ellT (sz.L n) (sz.lam n) (τ n)) ^ (1 / 2 : ℝ)) +
      ((sz.W n : ℕ) : ℝ) ^ (-D))
    (fun k j p ω => ‖(baFMz (sz.comp (φ k)) fun j => z (φ k j)).L j (τ (φ k j)) p.1 p.2 ω -
      (baFMz (sz.comp (φ k)) fun j => z (φ k j)).K j (τ (φ k j)) p.1 p.2‖)
    (fun k j p _ => ((sz.comp (φ k)).Bctl j (τ (φ k j))) ^ (1 / 5 : ℝ) *
        STWB (sz.comp (φ k)) j (τ (φ k j)) (zdistInf d ((sz.comp (φ k)).L j) (p.2 0 - p.2 1)) *
        Real.exp (-(((zdistInf d ((sz.comp (φ k)).L j) (p.2 0 - p.2 1) : ℕ) : ℝ) /
          ellT ((sz.comp (φ k)).L j) ((sz.comp (φ k)).lam j) (τ (φ k j))) ^ (1 / 2 : ℝ)) +
      (((sz.comp (φ k)).W j : ℕ) : ℝ) ^ (-D))
    (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl)
  exact ⟨fun h k D hD => (P D).1 (h D hD) k, fun h D hD => (P D).2 fun k => h k D hD⟩

private theorem MainIndGlue_DecayStrong_iff {d : ℕ} (sz : Sizes d) (z : ℕ → ℂ) (τ : ℕ → ℝ) {ι : Type} [Finite ι] (φ : ι → ℕ → ℕ)
    (hφ : ∀ k, StrictMono (φ k)) (hcov : ∀ᶠ n in atTop, ∃ k, n ∈ Set.range (φ k)) :
    STDecayStronggL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) τ ↔
      ∀ k, STDecayStronggL (baFMz (sz.comp (φ k)) fun j => z (φ k j)) (Sizes.seqP ((sz.comp (φ k)).withLam 0)) (fun j => τ (φ k j)) := by
  have P := fun (D : ℝ) => MainIndGlue_precIff sz φ hφ hcov
    (U := fun n => {_p : (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)) // sz.lam n ^ 2 ≤ 1 - τ n})
    (fun n p ω => ‖(baFMz sz z).L n (τ n) p.1.1 p.1.2 ω - (baFMz sz z).K n (τ n) p.1.1 p.1.2‖)
    (fun n p _ => (sz.Bctl n (τ n)) ^ 2 * Real.exp (-((zdistInf d (sz.L n) (p.1.2 0 - p.1.2 1) : ℕ) : ℝ) ^ (1 / 2 : ℝ)) +
      ((sz.W n : ℕ) : ℝ) ^ (-D))
    (fun k j p ω => ‖(baFMz (sz.comp (φ k)) fun j => z (φ k j)).L j (τ (φ k j)) p.1.1 p.1.2 ω -
      (baFMz (sz.comp (φ k)) fun j => z (φ k j)).K j (τ (φ k j)) p.1.1 p.1.2‖)
    (fun k j p _ => ((sz.comp (φ k)).Bctl j (τ (φ k j))) ^ 2 *
      Real.exp (-((zdistInf d ((sz.comp (φ k)).L j) (p.1.2 0 - p.1.2 1) : ℕ) : ℝ) ^ (1 / 2 : ℝ)) +
      (((sz.comp (φ k)).W j : ℕ) : ℝ) ^ (-D))
    (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl)
  exact ⟨fun h k D hD => (P D).1 (h D hD) k, fun h D hD => (P D).2 fun k => h k D hD⟩

private theorem MainIndGlue_LocalMax_iff {d : ℕ} (sz : Sizes d) (z : ℕ → ℂ) (τ : ℕ → ℝ) {ι : Type} [Finite ι] (φ : ι → ℕ → ℕ)
    (hφ : ∀ k, StrictMono (φ k)) (hcov : ∀ᶠ n in atTop, ∃ k, n ∈ Set.range (φ k)) :
    STLocalMaxgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) τ ↔
      ∀ k, STLocalMaxgL (baFMz (sz.comp (φ k)) fun j => z (φ k j)) (Sizes.seqP ((sz.comp (φ k)).withLam 0)) (fun j => τ (φ k j)) :=
  MainIndGlue_precIff sz φ hφ hcov (U := fun n => Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n))
    (fun n p ω => ‖(baFMz sz z).GM n (τ n) ω p.1 p.2‖) (fun n _ _ => sz.Bctl n (τ n) ^ (1 / 2 : ℝ))
    (fun k j p ω => ‖(baFMz (sz.comp (φ k)) fun j => z (φ k j)).GM j (τ (φ k j)) ω p.1 p.2‖)
    (fun k j _ _ => (sz.comp (φ k)).Bctl j (τ (φ k j)) ^ (1 / 2 : ℝ)) (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl)

private theorem MainIndGlue_LocalEntry_iff {d : ℕ} (sz : Sizes d) (z : ℕ → ℂ) (τ : ℕ → ℝ) {ι : Type} [Finite ι] (φ : ι → ℕ → ℕ)
    (hφ : ∀ k, StrictMono (φ k)) (hcov : ∀ᶠ n in atTop, ∃ k, n ∈ Set.range (φ k)) :
    STLocalEntrygL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) τ ↔
      ∀ k, STLocalEntrygL (baFMz (sz.comp (φ k)) fun j => z (φ k j)) (Sizes.seqP ((sz.comp (φ k)).withLam 0)) (fun j => τ (φ k j)) :=
  MainIndGlue_precIff sz φ hφ hcov (U := fun n => Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n))
    (fun n p ω => ‖(baFMz sz z).GM n (τ n) ω p.1 p.2‖ ^ 2)
    (fun n p _ => STWB sz n (τ n) (zdistInf d (sz.L n) (STblk sz n p.1 - STblk sz n p.2)))
    (fun k j p ω => ‖(baFMz (sz.comp (φ k)) fun j => z (φ k j)).GM j (τ (φ k j)) ω p.1 p.2‖ ^ 2)
    (fun k j p _ => STWB (sz.comp (φ k)) j (τ (φ k j)) (zdistInf d ((sz.comp (φ k)).L j) (STblk (sz.comp (φ k)) j p.1 - STblk (sz.comp (φ k)) j p.2)))
    (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl)

private theorem MainIndGlue_Exp2_iff {d : ℕ} (sz : Sizes d) (z : ℕ → ℂ) (τ : ℕ → ℝ) {ι : Type} [Finite ι] (φ : ι → ℕ → ℕ)
    (hφ : ∀ k, StrictMono (φ k)) (hcov : ∀ᶠ n in atTop, ∃ k, n ∈ Set.range (φ k)) :
    STExp2gL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) τ ↔
      ∀ k, STExp2gL (baFMz (sz.comp (φ k)) fun j => z (φ k j)) (Sizes.seqP ((sz.comp (φ k)).withLam 0)) (fun j => τ (φ k j)) :=
  MainIndGlue_precIff sz φ hφ hcov (U := fun n => (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)))
    (fun n p _ => ‖(∫ ω, (baFMz sz z).L n (τ n) p.1 p.2 ω ∂(Sizes.seqP (sz.withLam 0))) - (baFMz sz z).K n (τ n) p.1 p.2‖)
    (fun n _ _ => sz.Bctl n (τ n) ^ 2 * ((sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d) ^ (-(1 / 5 : ℝ)) + sz.Bctl n (τ n)))
    (fun k j p _ => ‖(∫ ω, (baFMz (sz.comp (φ k)) fun j => z (φ k j)).L j (τ (φ k j)) p.1 p.2 ω ∂(Sizes.seqP ((sz.comp (φ k)).withLam 0))) -
      (baFMz (sz.comp (φ k)) fun j => z (φ k j)).K j (τ (φ k j)) p.1 p.2‖)
    (fun k j _ _ => (sz.comp (φ k)).Bctl j (τ (φ k j)) ^ 2 *
      (((sz.comp (φ k)).lam j ^ 2 * (((sz.comp (φ k)).W j : ℕ) : ℝ) ^ d) ^ (-(1 / 5 : ℝ)) + (sz.comp (φ k)).Bctl j (τ (φ k j))))
    (fun k j u ω => MainIndGlue_exp2_eq sz (φ k) (hφ k) z τ j u) (fun _ _ _ _ => rfl)

private theorem MainIndGlue_TL2_iff {d : ℕ} (sz : Sizes d) (z : ℕ → ℂ) (τ : ℕ → ℝ) {ι : Type} [Finite ι] (φ : ι → ℕ → ℕ)
    (hφ : ∀ k, StrictMono (φ k)) (hcov : ∀ᶠ n in atTop, ∃ k, n ∈ Set.range (φ k)) :
    BATwistLoopLaw (baFMz sz z) (Sizes.seqP (sz.withLam 0)) τ ↔
      ∀ k, BATwistLoopLaw (baFMz (sz.comp (φ k)) fun j => z (φ k j)) (Sizes.seqP ((sz.comp (φ k)).withLam 0)) (fun j => τ (φ k j)) :=
  MainIndGlue_precIff sz φ hφ hcov (U := fun n => (Fin 2 → Bool) × Zd d (sz.L n) × Zd d (sz.L n) × Zd d (sz.L n))
    (fun n p ω => ‖twL2' (baFMz sz z) n (τ n) ω p.1 p.2.1 p.2.2.1 p.2.2.2 - twK (baFMz sz z) n (τ n) p.1 p.2.1 p.2.2.1 p.2.2.2‖)
    (fun n _ _ => sz.Bctl n (τ n) ^ (3 / 2 : ℝ))
    (fun k j p ω => ‖twL2' (baFMz (sz.comp (φ k)) fun j => z (φ k j)) j (τ (φ k j)) ω p.1 p.2.1 p.2.2.1 p.2.2.2 -
      twK (baFMz (sz.comp (φ k)) fun j => z (φ k j)) j (τ (φ k j)) p.1 p.2.1 p.2.2.1 p.2.2.2‖)
    (fun k j _ _ => (sz.comp (φ k)).Bctl j (τ (φ k j)) ^ (3 / 2 : ℝ)) (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl)

/-- **The six hypotheses go down** (6 uses: `STLKgL`, `STDecaygL`, `STDecayStronggL`, `STLocalMaxgL`, `STExp2gL`, TL2): along every class of a
finite cover. -/
private theorem MainIndGlue_down {d : ℕ} (sz : Sizes d) (z : ℕ → ℂ) (τ : ℕ → ℝ) {ι : Type} [Finite ι] (φ : ι → ℕ → ℕ)
    (hφ : ∀ k, StrictMono (φ k)) (hcov : ∀ᶠ n in atTop, ∃ k, n ∈ Set.range (φ k)) :
    (let C := baFMz sz z; let μ := Sizes.seqP (sz.withLam 0)
      STLKgL C μ τ ∧ STDecaygL C μ τ ∧ STDecayStronggL C μ τ ∧ STLocalMaxgL C μ τ ∧ STExp2gL C μ τ ∧ BATwistLoopLaw C μ τ) →
    ∀ k, let C := baFMz (sz.comp (φ k)) (fun j => z (φ k j)); let μ := Sizes.seqP ((sz.comp (φ k)).withLam 0)
      let τ' : ℕ → ℝ := fun j => τ (φ k j)
      STLKgL C μ τ' ∧ STDecaygL C μ τ' ∧ STDecayStronggL C μ τ' ∧ STLocalMaxgL C μ τ' ∧ STExp2gL C μ τ' ∧ BATwistLoopLaw C μ τ' :=
  fun ⟨h1, h2, h3, h4, h5, h6⟩ k =>
    ⟨(MainIndGlue_LK_iff sz z τ φ hφ hcov).1 h1 k, (MainIndGlue_Decay_iff sz z τ φ hφ hcov).1 h2 k,
      (MainIndGlue_DecayStrong_iff sz z τ φ hφ hcov).1 h3 k, (MainIndGlue_LocalMax_iff sz z τ φ hφ hcov).1 h4 k,
      (MainIndGlue_Exp2_iff sz z τ φ hφ hcov).1 h5 k, (MainIndGlue_TL2_iff sz z τ φ hφ hcov).1 h6 k⟩

/-- **The seven conclusions come back** (7 uses: `STLKgL`, `STLmaxgL`, `STDecaygL`, `STExp2gL`, `STLocalEntrygL`, `STDecayStronggL`, TL2):
the seven along every class give the seven along `sz` (the cover form of `baConclShift`, `MainIndOutBA:155`). -/
private theorem MainIndGlue_up {d : ℕ} (sz : Sizes d) (z : ℕ → ℂ) (τ : ℕ → ℝ) {ι : Type} [Finite ι] (φ : ι → ℕ → ℕ)
    (hφ : ∀ k, StrictMono (φ k)) (hcov : ∀ᶠ n in atTop, ∃ k, n ∈ Set.range (φ k)) :
    (∀ k, let C := baFMz (sz.comp (φ k)) (fun j => z (φ k j)); let μ := Sizes.seqP ((sz.comp (φ k)).withLam 0)
      let τ' : ℕ → ℝ := fun j => τ (φ k j)
      STLKgL C μ τ' ∧ STLmaxgL C μ τ' ∧ STDecaygL C μ τ' ∧ STExp2gL C μ τ' ∧ STLocalEntrygL C μ τ' ∧ STDecayStronggL C μ τ' ∧
        BATwistLoopLaw C μ τ') →
    let C := baFMz sz z; let μ := Sizes.seqP (sz.withLam 0)
    STLKgL C μ τ ∧ STLmaxgL C μ τ ∧ STDecaygL C μ τ ∧ STExp2gL C μ τ ∧ STLocalEntrygL C μ τ ∧ STDecayStronggL C μ τ ∧
      BATwistLoopLaw C μ τ :=
  fun h =>
    ⟨(MainIndGlue_LK_iff sz z τ φ hφ hcov).2 fun k => (h k).1, (MainIndGlue_Lmax_iff sz z τ φ hφ hcov).2 fun k => (h k).2.1,
      (MainIndGlue_Decay_iff sz z τ φ hφ hcov).2 fun k => (h k).2.2.1, (MainIndGlue_Exp2_iff sz z τ φ hφ hcov).2 fun k => (h k).2.2.2.1,
      (MainIndGlue_LocalEntry_iff sz z τ φ hφ hcov).2 fun k => (h k).2.2.2.2.1,
      (MainIndGlue_DecayStrong_iff sz z τ φ hφ hcov).2 fun k => (h k).2.2.2.2.2.1,
      (MainIndGlue_TL2_iff sz z τ φ hφ hcov).2 fun k => (h k).2.2.2.2.2.2⟩

/-! ## 4. The glue along the classes of the stage pattern -/

/-- **`lem:main_ind_BA` in family form from the four regime steps** (twin of `ST_mainInd_of_regimes`, `MainIndRegimes:616`; probe
`BA_mainInd_of_regimes`, `t/T2205:3293`): all `d ≥ 3`.  The constant is the `Finset.inf'` over the 16 pairs `P : Fin 4 × Fin 4` of the
constant of `baMainIndFamTL_chain` at `(P.1, P.2 - P.1)` (`P.1 > P.2` is the chain of length `0`); it is fixed by `(κ, ε, 𝔡)`.
The stage pattern `(i, j)` of `[s_n, t_n]` (`STPattern`) is constant along the `Nat.nth` classes (`nth_cover`); on a class the
regime is the chain of stages `i, …, j` (`STRegChain_of_class`); the six hypotheses go down along the class on the member
extended by the main flow (`MainIndGlue_extendMember`, `MainIndGlue_down`), the seven conclusions come back (`MainIndGlue_up`). -/
theorem baMainIndFamTL_of_regimes (d : ℕ) (h₃ : BAMainIndFamTL d STReg5III) (h₁ : BAMainIndFamTL d STReg5I)
    (h₂ : BAMainIndFamTL d STReg5II) (h₄ : BAMainIndFamTL d STReg5IV) : BAMainIndFamTL d STAny := by
  intro hd κ ε 𝔡 hκ hε h𝔡
  have hch := baMainIndFamTL_chain d h₃ h₁ h₂ h₄
  choose c hc hc' H using fun P : Fin 4 × Fin 4 => hch ((P.2 : ℕ) - P.1) P.1
    (by have := P.1.isLt; have := P.2.isLt; omega) hd κ ε 𝔡 hκ hε h𝔡
  have hinf : ∀ P, (Finset.univ.inf' ⟨((0 : Fin 4), (0 : Fin 4)), Finset.mem_univ _⟩ c) ≤ c P := fun P =>
    Finset.inf'_le c (Finset.mem_univ P)
  refine ⟨Finset.univ.inf' ⟨((0 : Fin 4), (0 : Fin 4)), Finset.mem_univ _⟩ c,
    (Finset.lt_inf'_iff _).2 fun P _ => hc P, (hinf (0, 0)).trans (hc' _), ?_⟩
  intro 𝔠 sz z hflow hlam c₁ hc₁ hc₁' hwin s t hs0 hsT hst htT _ hyp hcon z' hz'
  have hpos : 0 < Finset.univ.inf' ⟨((0 : Fin 4), (0 : Fin 4)), Finset.mem_univ _⟩ c :=
    (Finset.lt_inf'_iff _).2 fun P _ => hc P
  have ht1 : ∀ n, t n < 1 := fun n => (htT n).trans_lt (BAflow_T0_bounds hκ hflow n).2.2.2
  -- the finite cover by the classes of constant pattern
  let ι : Type := {P : Fin 4 × Fin 4 // {m : ℕ | STPattern sz s t m = P}.Infinite}
  let φ : ι → ℕ → ℕ := fun P => Nat.nth (fun m => STPattern sz s t m = P.1)
  have hφ : ∀ P, StrictMono (φ P) := fun P => Nat.nth_strictMono P.2
  have hcov : ∀ᶠ n in atTop, ∃ P, n ∈ Set.range (φ P) := nth_cover (STPattern sz s t)
  refine MainIndGlue_up sz z' t φ hφ hcov fun P => ?_
  have hmem : ∀ j, STPattern sz s t (φ P j) = P.1 := fun j => Nat.nth_mem_of_infinite P.2 j
  obtain ⟨hij, hreg⟩ := STRegChain_of_class hd sz s t hst ht1 (φ P) P.1 hmem
  have htend : Tendsto (φ P) atTop atTop := (hφ P).tendsto_atTop
  refine H P.1 𝔠 (sz.comp (φ P)) (fun j => z (φ P j)) ⟨comp_admissible sz (φ P) 𝔠 𝔡 htend hflow.1, fun j => hflow.2 (φ P j)⟩
    (fun j => hlam (φ P j)) c₁ hc₁ hc₁' (fun j => hwin (φ P j)) (fun j => s (φ P j)) (fun j => t (φ P j))
    (fun j => hs0 _) (fun j => hsT _) (fun j => hst _) (fun j => htT _) hreg ?_
    (st5_conStInd_mono (sz.comp (φ P)) (STConStInd_comp sz (φ P) _ s t htend hcon) (fun j => ht1 _) hpos (hinf P.1))
    (fun j => z' (φ P j)) (fun j => hz' (φ P j))
  intro z'' hz''
  have hext := hyp _ (MainIndGlue_extendMember sz z c₁ s (φ P) (hφ P) z'' hz'')
  have e : (fun j => Function.extend (φ P) z'' z (φ P j)) = z'' :=
    funext fun j => (hφ P).injective.extend_apply z'' z j
  have := MainIndGlue_down sz _ s φ hφ hcov hext P
  simp only [e] at this
  exact this

/-! ## 5. Compiled `d = 3` instances (`sz0`, `zSeq`; the data of `MainIndOutBA:343-351` by `open private`)

Data: `κ = 1/4`, `(ε, 𝔠, 𝔡) = (1/10, 1/6, 1/10)`, `c₁ = 1/3`, `s ≡ 1/10 < t ≡ 1/2 ≤ T₀` (`half_lt_t0`), the member
`BAzSrc sz0 zSeq (2/3) (17/25)` of `Fam(1/2)` (`MainIndOutBA_mem`), `(con_st_ind)` by `s1Setup_conStInd_const`.  The regime steps and
the six family conjuncts on `Fam(1/10)` are the hypotheses (their producers are other gates); the sizes, the flow, the window, the
times, the regime, the pattern and the constants are discharged. -/

section Inst

open RBM.BA.FlowPinsInst RBM.Gauss.SizesInst RBM.BA.Step1FamInst

open private MainIndOutBA_flow MainIndOutBA_win MainIndOutBA_mem from RBM3D.BA.MainIndOutBA

/-- `lam_n² ≤ 1/2` along `sz0`, every `n` (`lam_n = (2 (n+1))⁻⁶ ≤ 1/64`). -/
private theorem MainIndGlue_lam_sq (n : ℕ) : sz0.lam n ^ 2 ≤ 1 / 2 := by
  have hx : (2 : ℝ) ≤ 2 * ((n : ℝ) + 1) := by have := Nat.cast_nonneg (α := ℝ) n; linarith
  have hlam : sz0.lam n ≤ 1 / 64 := by
    change ((2 * ((n : ℝ) + 1)) ^ 6)⁻¹ ≤ 1 / 64
    rw [one_div]
    exact inv_anti₀ (by norm_num) (by nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hx 6])
  have hlam0 : 0 ≤ sz0.lam n := by change 0 ≤ ((2 * ((n : ℝ) + 1)) ^ 6)⁻¹; positivity
  nlinarith [pow_le_pow_left₀ hlam0 hlam 2]

/-- Regime (iii) at `sz0` for every constant `s` and `t ≤ 1/2`. -/
private theorem MainIndGlue_reg (s t : ℝ) (ht : t ≤ 1 / 2) : STReg5III sz0 (fun _ => s) (fun _ => t) := fun n => by
  have := MainIndGlue_lam_sq n
  change sz0.lam n ^ 2 ≤ 1 - t
  linarith

-- The six hypotheses at `s ≡ 1/10` on `Fam(1/10)`, as the hypothesis of the instances.
set_option quotPrecheck false in
local notation "Hyp6" =>
  ∀ z' : ℕ → ℂ, BAFamZ sz0 zSeq (1 / 3) (fun _ => 1 / 10) z' →
    (let C := baFMz sz0 z'; let μ := Sizes.seqP (sz0.withLam 0); let s : ℕ → ℝ := fun _ => 1 / 10
      STLKgL C μ s ∧ STDecaygL C μ s ∧ STDecayStronggL C μ s ∧ STLocalMaxgL C μ s ∧ STExp2gL C μ s ∧ BATwistLoopLaw C μ s)

-- The seven conclusions at `t ≡ 1/2` at the non-main member.
set_option quotPrecheck false in
local notation "Concl7" =>
  (let C := baFMz sz0 (BAzSrc sz0 zSeq (fun _ => 2 / 3) (fun _ => 17 / 25)); let μ := Sizes.seqP (sz0.withLam 0)
    let t : ℕ → ℝ := fun _ => 1 / 2
    STLKgL C μ t ∧ STLmaxgL C μ t ∧ STDecaygL C μ t ∧ STExp2gL C μ t ∧ STLocalEntrygL C μ t ∧ STDecayStronggL C μ t ∧ BATwistLoopLaw C μ t)

-- the regime-(iii) split of `[1/10, 1/2]` at `3/10` (target 2, hypothesis-free)
example : STRegSeq STReg5III STReg5III sz0 (fun _ => 1 / 10) (fun _ => 1 / 2) :=
  ⟨fun _ => 3 / 10, fun _ => by norm_num, fun _ => by norm_num, MainIndGlue_reg _ _ (by norm_num), MainIndGlue_reg _ _ (by norm_num)⟩

-- the stage pattern of `[1/10, 1/2]` along `sz0` is `(0, 0)` at every `n` (one class, regime (iii); hypothesis-free)
example : ∀ n, STPattern sz0 (fun _ => 1 / 10) (fun _ => 1 / 2) n = (0, 0) := fun n => by
  have hl := MainIndGlue_lam_sq n
  have hS : STStageS sz0 (fun _ => (1 / 10 : ℝ)) n = 0 := by
    have h1 : (1 / 10 : ℝ) < STCutK sz0 1 n := by
      change (1 / 10 : ℝ) < 1 - sz0.lam n ^ 2
      linarith
    simp only [STStageS, h1, ↓reduceIte]
  have hT : STStageT sz0 (fun _ => (1 / 2 : ℝ)) n = 0 := by
    have h1 : (1 / 2 : ℝ) ≤ STCutK sz0 1 n := by
      change (1 / 2 : ℝ) ≤ 1 - sz0.lam n ^ 2
      linarith
    simp only [STStageT, h1, ↓reduceIte]
  exact Prod.ext (Fin.ext hS) (Fin.ext hT)

-- target 5 along `φ = (2 ·)`: the member `mem0 ∘ φ` of `Fam(1/2)` along `sz0.comp φ`, extended by the main flow (hypothesis-free)
example : BAFamZ sz0 zSeq (1 / 3) (fun _ => 1 / 2)
    (Function.extend (fun j : ℕ => 2 * j) (fun j => BAzSrc sz0 zSeq (fun _ => 2 / 3) (fun _ => 17 / 25) (2 * j)) zSeq) :=
  MainIndGlue_extendMember sz0 zSeq (1 / 3) (fun _ => 1 / 2) (fun j => 2 * j) (fun a b h => by simpa using h) _
    (fun j => MainIndOutBA_mem (1 / 2) (by norm_num) (2 * j))

-- target 1: `STAny ⊇ STReg5III`; the step at `STReg5III` from the step at `STAny`, applied at the data
example (h : BAMainIndFamTL 3 STAny) (hyp : Hyp6) :
    ∃ 𝔠d : ℝ, 0 < 𝔠d ∧ Concl7 := by
  obtain ⟨𝔠d, h𝔠, -, H⟩ := baMainIndFamTL_mono 3 STAny STReg5III (fun _ _ _ _ => trivial) h le_rfl (1 / 4) (1 / 10) (1 / 10)
    (by norm_num) (by norm_num) (by norm_num)
  exact ⟨𝔠d, h𝔠, H (1 / 6) sz0 zSeq MainIndOutBA_flow sz0_lam_pos (1 / 3) (by norm_num) (by norm_num) MainIndOutBA_win
    (fun _ => 1 / 10) (fun _ => 1 / 2) (fun _ => by norm_num) (fun n => (by norm_num : (1 / 10 : ℝ) ≤ 1 / 2).trans (half_lt_t0 n).le)
    (fun _ => by norm_num) (fun n => (half_lt_t0 n).le) (MainIndGlue_reg _ _ le_rfl) hyp
    (Ind.Step1SetupInst.s1Setup_conStInd_const (by norm_num) (by norm_num) h𝔠) _ (MainIndOutBA_mem (1 / 2) (by norm_num))⟩

-- target 2 at `R₁ = R₂ = STReg5III`, cut at `m ≡ 3/10`, applied at the data
example (h : BAMainIndFamTL 3 STReg5III) (hyp : Hyp6) : ∃ 𝔠d : ℝ, 0 < 𝔠d ∧ Concl7 := by
  obtain ⟨𝔠d, h𝔠, -, H⟩ := baMainIndFamTL_seq 3 STReg5III STReg5III h h le_rfl (1 / 4) (1 / 10) (1 / 10)
    (by norm_num) (by norm_num) (by norm_num)
  exact ⟨𝔠d, h𝔠, H (1 / 6) sz0 zSeq MainIndOutBA_flow sz0_lam_pos (1 / 3) (by norm_num) (by norm_num) MainIndOutBA_win
    (fun _ => 1 / 10) (fun _ => 1 / 2) (fun _ => by norm_num) (fun n => (by norm_num : (1 / 10 : ℝ) ≤ 1 / 2).trans (half_lt_t0 n).le)
    (fun _ => by norm_num) (fun n => (half_lt_t0 n).le)
    ⟨fun _ => 3 / 10, fun _ => by norm_num, fun _ => by norm_num, MainIndGlue_reg _ _ (by norm_num), MainIndGlue_reg _ _ (by norm_num)⟩ hyp
    (Ind.Step1SetupInst.s1Setup_conStInd_const (by norm_num) (by norm_num) h𝔠) _ (MainIndOutBA_mem (1 / 2) (by norm_num))⟩

-- target 3 at `(i, m) = (0, 0)` (`STRegChain 0 0 = STReg5III`), applied at the data
example (h₃ : BAMainIndFamTL 3 STReg5III) (h₁ : BAMainIndFamTL 3 STReg5I) (h₂ : BAMainIndFamTL 3 STReg5II)
    (h₄ : BAMainIndFamTL 3 STReg5IV) (hyp : Hyp6) : ∃ 𝔠d : ℝ, 0 < 𝔠d ∧ Concl7 := by
  obtain ⟨𝔠d, h𝔠, -, H⟩ := baMainIndFamTL_chain 3 h₃ h₁ h₂ h₄ 0 0 (by norm_num) le_rfl (1 / 4) (1 / 10) (1 / 10)
    (by norm_num) (by norm_num) (by norm_num)
  exact ⟨𝔠d, h𝔠, H (1 / 6) sz0 zSeq MainIndOutBA_flow sz0_lam_pos (1 / 3) (by norm_num) (by norm_num) MainIndOutBA_win
    (fun _ => 1 / 10) (fun _ => 1 / 2) (fun _ => by norm_num) (fun n => (by norm_num : (1 / 10 : ℝ) ≤ 1 / 2).trans (half_lt_t0 n).le)
    (fun _ => by norm_num) (fun n => (half_lt_t0 n).le) (MainIndGlue_reg (1 / 10) (1 / 2) le_rfl) hyp
    (Ind.Step1SetupInst.s1Setup_conStInd_const (by norm_num) (by norm_num) h𝔠) _ (MainIndOutBA_mem (1 / 2) (by norm_num))⟩

-- target 4 (`T2512_InstOfRegimes`): the four regime steps and the six conjuncts on `Fam(1/10)` are the hypotheses
example (h₃ : BAMainIndFamTL 3 STReg5III) (h₁ : BAMainIndFamTL 3 STReg5I) (h₂ : BAMainIndFamTL 3 STReg5II)
    (h₄ : BAMainIndFamTL 3 STReg5IV) (hyp : Hyp6) : Concl7 := by
  obtain ⟨𝔠d, h𝔠, -, H⟩ := baMainIndFamTL_of_regimes 3 h₃ h₁ h₂ h₄ le_rfl (1 / 4) (1 / 10) (1 / 10)
    (by norm_num) (by norm_num) (by norm_num)
  exact H (1 / 6) sz0 zSeq MainIndOutBA_flow sz0_lam_pos (1 / 3) (by norm_num) (by norm_num) MainIndOutBA_win
    (fun _ => 1 / 10) (fun _ => 1 / 2) (fun _ => by norm_num) (fun n => (by norm_num : (1 / 10 : ℝ) ≤ 1 / 2).trans (half_lt_t0 n).le)
    (fun _ => by norm_num) (fun n => (half_lt_t0 n).le) trivial hyp
    (Ind.Step1SetupInst.s1Setup_conStInd_const (by norm_num) (by norm_num) h𝔠) _ (MainIndOutBA_mem (1 / 2) (by norm_num))

end Inst

end RBM.BA

end
