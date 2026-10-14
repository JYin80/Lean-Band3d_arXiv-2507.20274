/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.BA.TwistChain
import RBM3D.BA.Step1Fam
import RBM3D.BA.CouplingWindow
import RBM3D.BA.KBound
import RBM3D.Induction.SizesComp
import RBM3D.BA.GridGoodBA
import RBM3D.BA.CltFlowBA
import RBM3D.BA.UNPins

/-!
# V row V3 (T2504): the BA terminal of the main induction in family form

The family twin of `baChainTL_holds` (`BA/TwistChain.lean:240`) and V3's base facts at the BA
tuple `(fun sz => seqP (sz.withLam 0), BAFlow, baFMz, BAflowT0)`.

* `BAMainIndFamTL d R`: the family step (`lem:main_ind_BA` on `Fam(u)`, `7_8:1954-1990`, D536),
  the text of T2503's binding pin; V2a proves it per regime, V2b at `STAny`.
* `BATwistLoopLaw_congr`, `baFamMember_flow`, `baFamMember_base`: TL2 is tail-local; a member of
  `Fam(t)` is a `BAFlow` at `(κ', ε')` after a finite modification; the per-member base case.
* `baTailPassage`, `baConclShift`: the tail `sz.comp (· + n₀)` at `κ/2` (D538) and the shift of
  the seven conclusions.
* `baChainFamTL_holds`: the chain of times over `Fam(p_k)` with the TL2 conjunct, mixed at the
  class `t_n = 0`.
* `baG0M_holds`, `baLK0_holds`, `stBaseG_of_init'`, `baBaseG_holds`, `baHorizonG_holds`:
  `G_0 = M`, `𝓛_0 = 𝒦_0` (`1_2:1240-1243`), the base case and the horizon at BA (uniform over
  `BAFlow`).
* `baMLOutTL_of_famStep`, `unMLOutBA_of_BAMLOutTL`, `unMLOutBA_of_famStep`: the terminal outputs;
  the family step is the one remaining hypothesis.
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

open private TwistChain_LK_mix TwistChain_Lmax_mix TwistChain_Decay_mix TwistChain_Exp2_mix TwistChain_LocalEntry_mix
  TwistChain_TL2_mix from RBM3D.BA.TwistChain
open private Boot_GM_zero from RBM3D.BA.Step1Boot
open private GridGoodBA_loopFine_init GridGoodBA_BAMLoop_one_loop from RBM3D.BA.GridGoodBA
open private CltFlowBA_Ksol_isKLoopS CltFlowBA_one_sub_T0 from RBM3D.BA.CltFlowBA

/-! ## 1. The family step (T2503 D1, binding) -/

/-- **The family step** `BAMainIndFamTL d R` (T2503 binding text, D1): `lem:main_ind_BA` on `Fam(t)` (`7_8:1954-1990`):
the six conclusions at `s` for every member of `Fam(s)` and `(con_st_ind)` give the seven at `t` for every member of `Fam(t)`,
at the main flow `z` with `0 < lam` and the window `c₁` (`∀ c₁`).  V2a proves it per regime `R`, V2b at `STAny`. -/
def BAMainIndFamTL (d : ℕ) (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∃ 𝔠d : ℝ, 0 < 𝔠d ∧ 𝔠d ≤ 1 / 100 ∧
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z → (∀ n, 0 < sz.lam n) →
      ∀ c₁ : ℝ, 0 < c₁ → c₁ ≤ 1 / 2 → BAWinBulk sz z c₁ κ →
      ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n ≤ BAflowT0 sz z n) → (∀ n, s n < t n) →
        (∀ n, t n ≤ BAflowT0 sz z n) → R sz s t →
        (∀ z' : ℕ → ℂ, BAFamZ sz z c₁ s z' →
          let C := baFMz sz z'; let μ := Sizes.seqP (sz.withLam 0)
          STLKgL C μ s ∧ STDecaygL C μ s ∧ STDecayStronggL C μ s ∧ STLocalMaxgL C μ s ∧
            STExp2gL C μ s ∧ BATwistLoopLaw C μ s) →
        sz.STConStInd 𝔠d s t →
        ∀ z' : ℕ → ℂ, BAFamZ sz z c₁ t z' →
          let C := baFMz sz z'; let μ := Sizes.seqP (sz.withLam 0)
          STLKgL C μ t ∧ STLmaxgL C μ t ∧ STDecaygL C μ t ∧ STExp2gL C μ t ∧
            STLocalEntrygL C μ t ∧ STDecayStronggL C μ t ∧ BATwistLoopLaw C μ t

/-! ## 2. TL2 is tail-local; a member of `Fam(t)` as a flow (probe `t/T2503:RBM3D/Probe/T2503Pins.lean:95-123`) -/

/-- **TL2 is tail-local**: `BATwistLoopLaw` depends on the carrier only through `FlowFM.EvEq` (`PrecL_congr`, `Step1Boot:185`). -/
theorem BATwistLoopLaw_congr (d : ℕ) (sz : Sizes d) (C C' : FlowFM sz) (μ : Measure sz.SeqΩ) (τ : ℕ → ℝ)
    (h : FlowFM.EvEq C C') : BATwistLoopLaw C μ τ ↔ BATwistLoopLaw C' μ τ := by
  unfold BATwistLoopLaw
  refine PrecL_congr ?_
  filter_upwards [h] with n hn
  refine ⟨?_, rfl⟩
  funext p ω
  simp only [twL2', twK, twMB, hn.G, hn.M]

/-- **A member of `Fam(t)` as a flow**: after the finite modification below `n₀` it is a `BAFlow` at `(κ', ε')` with
horizon `≥ t` at every `n` and carrier eventually equal (`BAFlowMember_holds`, `Step1Fam:624`). -/
theorem baFamMember_flow (d : ℕ) :
    ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∃ κ' ε' : ℝ, 0 < κ' ∧ κ' ≤ κ ∧ 0 < ε' ∧ ε' ≤ ε ∧
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z → (∀ n, 0 < sz.lam n) →
      ∀ c₁ : ℝ, 0 < c₁ → c₁ ≤ 1 / 2 → BAWinBulk sz z c₁ κ →
      ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ BAflowT0 sz z n) →
      ∀ z' : ℕ → ℂ, BAFamZ sz z c₁ t z' →
        (∀ n, t n ≤ BAflowT0 sz z' n) ∧
          ∃ z'' : ℕ → ℂ, BAFlow sz κ' ε' 𝔠 𝔡 z'' ∧ (∀ n, t n ≤ BAflowT0 sz z'' n) ∧
            FlowFM.EvEq (baFMz sz z'') (baFMz sz z') := by
  intro κ ε 𝔡 hκ hε h𝔡
  obtain ⟨κ', ε', hκ', hκκ, hε', hεε, H⟩ := BAFlowMember_holds d κ ε 𝔡 hκ hε h𝔡
  refine ⟨κ', ε', hκ', hκκ, hε', hεε, fun 𝔠 sz z hflow hlam c₁ hc₁ hc₁' hwin t ht0 htT z' hz' => ⟨BAFamZ_horizon htT hz', ?_⟩⟩
  obtain ⟨n₀, hfl⟩ := H 𝔠 sz z hflow hlam c₁ hc₁ hc₁' hwin z' (BAFamZ_mono (s := fun _ => 0) ht0 hz')
  refine ⟨_, hfl, fun n => ?_, eventually_atTop.mpr ⟨n₀, fun n hn => baFMz_eqAt sz (by simp [not_lt.mpr hn])⟩⟩
  by_cases hn : n < n₀
  · rw [BAflowT0_congr sz (z₂ := z) (by simp [hn])]; exact htT n
  · rw [BAflowT0_congr sz (z₂ := z') (by simp [hn])]; exact BAFamZ_horizon htT hz' n

/-! ## 3. The per-member base; the tail passage; the shift of the conclusions (probe `:142-195`) -/

/-- **The per-member base** at the zero sequence: the member as a flow `z''` at `(κ', ε')` (`baFamMember_flow`), `STBaseG` there,
`baTwistLoopBase_holds` with `STG0M`, back along the congruences `STLKgL_congr … STDecayStronggL_congr`, `BATwistLoopLaw_congr`. -/
theorem baFamMember_base (d : ℕ) (hbase : STBaseG d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) baFMz)
    (hG : ∀ κ ε 𝔠 𝔡 (sz : Sizes d) z, BAFlow sz κ ε 𝔠 𝔡 z → STG0M (baFMz sz z)) :
    3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z → (∀ n, 0 < sz.lam n) →
      ∀ c₁ : ℝ, 0 < c₁ → c₁ ≤ 1 / 2 → BAWinBulk sz z c₁ κ → ∀ z' : ℕ → ℂ, BAFamZ sz z c₁ (fun _ => 0) z' →
        STConclgL (baFMz sz z') (Sizes.seqP (sz.withLam 0)) (fun _ => 0) ∧ BATwistLoopLaw (baFMz sz z') (Sizes.seqP (sz.withLam 0)) (fun _ => 0) := by
  intro hd κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow hlam c₁ hc₁ hc₁' hwin z' hz'
  obtain ⟨κ', ε', hκ', -, hε', -, Hm⟩ := baFamMember_flow d κ ε 𝔡 hκ hε h𝔡
  obtain ⟨-, z'', hfl, -, hev⟩ := Hm 𝔠 sz z hflow hlam c₁ hc₁ hc₁' hwin (fun _ => 0) (fun _ => le_rfl)
    (fun n => (BAflow_T0_bounds hκ hflow n).2.2.1.le) z' hz'
  obtain ⟨b1, b2, b3, b4, b5, b6⟩ := hbase hd κ' ε' 𝔡 𝔠 hκ' hε' h𝔡 sz z'' hfl
  exact ⟨⟨(STLKgL_congr _ hev _).mp b1, (STLmaxgL_congr _ hev _).mp b2, (STDecaygL_congr _ hev _).mp b3,
    (STExp2gL_congr _ hev _).mp b4, (STLocalEntrygL_congr _ hev _).mp b5, (STDecayStronggL_congr _ hev _).mp b6⟩,
    (BATwistLoopLaw_congr d sz _ _ _ _ hev).mp (baTwistLoopBase_holds d hd κ' ε' 𝔡 𝔠 hκ' hε' h𝔡 sz z'' hfl (hG _ _ _ _ sz z'' hfl))⟩

/-- **The tail passage, route (α)** (D538): from `WO` (`hflow.1.2.2.2.2`) a tail `sz.comp (· + n₀)` with `0 < lam`, a `BAFlow` at `κ/2`
and the window at `κ/2` (`BAWinBulk_of_dom_holds`, `CouplingWindow:836`); `c₁` before `(ε, 𝔠, sz, z)`. -/
theorem baTailPassage (d : ℕ) (hd : 3 ≤ d) (κ 𝔡 : ℝ) (hκ : 0 < κ) (h𝔡 : 0 < 𝔡) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ c₁ ≤ 1 / 2 ∧ ∀ (ε 𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z → ∃ n₀ : ℕ,
      BAFlow (sz.comp (· + n₀)) (κ / 2) ε 𝔠 𝔡 (fun j => z (j + n₀)) ∧ (∀ j, 0 < (sz.comp (· + n₀)).lam j) ∧
        BAWinBulk (sz.comp (· + n₀)) (fun j => z (j + n₀)) c₁ (κ / 2) := by
  obtain ⟨c₁, hc₁, hc₁', H⟩ := BAWinBulk_of_dom_holds d hd κ 𝔡⁻¹ hκ (inv_pos.2 h𝔡)
  refine ⟨c₁, hc₁, hc₁', fun ε 𝔠 sz z hflow => ?_⟩
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.1 hflow.1.2.2.2.2
  have hlam : ∀ j, 0 < sz.lam (j + n₀) ∧ sz.lam (j + n₀) ≤ 𝔡⁻¹ := fun j =>
    ⟨lt_of_lt_of_le (Real.rpow_pos_of_pos (by exact_mod_cast sz.W_pos _) _) (hn₀ (j + n₀) (by omega)).1, (hn₀ _ (by omega)).2⟩
  have hf : BAFlow (sz.comp (· + n₀)) κ ε 𝔠 𝔡 (fun j => z (j + n₀)) :=
    ⟨Sizes.comp_admissible sz _ 𝔠 𝔡 (tendsto_add_atTop_nat n₀) hflow.1, fun j => hflow.2 (j + n₀)⟩
  exact ⟨n₀, ⟨hf.1, fun j => ⟨(half_le_self hκ.le).trans (hf.2 j).1, (hf.2 j).2⟩⟩, fun j => (hlam j).1, H ε _ _ hlam hf.2⟩

private theorem MainIndOutBA_shift_mono (n₀ : ℕ) : StrictMono (· + n₀ : ℕ → ℕ) := fun a b h => by simpa using h

/-- `≺` along the tail `sz.comp (· + n₀)` gives `≺` along `sz` (`stochDomAt_iff_comp_cover`, `SizesComp:536`; every carrier object
of `baFMz` commutes with `reindex` by `rfl`). -/
private theorem MainIndOutBA_precL_shift {d : ℕ} (sz : Sizes d) (n₀ : ℕ) {U : ℕ → Type} (ξ ζ : ∀ n, U n → sz.SeqΩ → ℝ)
    (ξ' ζ' : ∀ j, U (j + n₀) → (sz.comp (· + n₀)).SeqΩ → ℝ)
    (hξ : ∀ j u ω, ξ' j u (reindex sz (· + n₀) ω) = ξ (j + n₀) u ω) (hζ : ∀ j u ω, ζ' j u (reindex sz (· + n₀) ω) = ζ (j + n₀) u ω) :
    PrecL (sz.comp (· + n₀)) (seqP ((sz.comp (· + n₀)).withLam 0)) ξ' ζ' → PrecL sz (seqP (sz.withLam 0)) ξ ζ := fun h =>
  (Sizes.stochDomAt_iff_comp_cover sz (seqP (sz.withLam 0)) (fun _ : Unit => (· + n₀)) (fun _ => seqP ((sz.comp (· + n₀)).withLam 0))
    (fun _ => MainIndOutBA_shift_mono n₀) (eventually_atTop.2 ⟨n₀, fun n hn => ⟨(), n - n₀, by simp; omega⟩⟩)
    (fun _ s => seqP_withLam_reindex_preimage sz _ 0 (MainIndOutBA_shift_mono n₀).injective s) ξ ζ (fun _ => ξ') (fun _ => ζ')
    (fun _ => hξ) (fun _ => hζ)).2 (fun _ => h)

/-- **The seven conclusions along the tail give the seven along `sz`** (`MainIndOutBA_precL_shift` for each conjunct). -/
theorem baConclShift {d : ℕ} (sz : Sizes d) (z : ℕ → ℂ) (τ : ℕ → ℝ) (n₀ : ℕ) :
    let C₁ := baFMz (sz.comp (· + n₀)) (fun j => z (j + n₀)); let μ₁ := seqP ((sz.comp (· + n₀)).withLam 0)
    let τ₁ : ℕ → ℝ := fun j => τ (j + n₀)
    (STLKgL C₁ μ₁ τ₁ ∧ STLmaxgL C₁ μ₁ τ₁ ∧ STDecaygL C₁ μ₁ τ₁ ∧ STExp2gL C₁ μ₁ τ₁ ∧ STLocalEntrygL C₁ μ₁ τ₁ ∧
      STDecayStronggL C₁ μ₁ τ₁ ∧ BATwistLoopLaw C₁ μ₁ τ₁) →
    let C := baFMz sz z; let μ := seqP (sz.withLam 0)
    STLKgL C μ τ ∧ STLmaxgL C μ τ ∧ STDecaygL C μ τ ∧ STExp2gL C μ τ ∧ STLocalEntrygL C μ τ ∧ STDecayStronggL C μ τ ∧
      BATwistLoopLaw C μ τ := by
  intro C₁ μ₁ τ₁ ⟨h1, h2, h3, h4, h5, h6, h7⟩ C μ
  refine ⟨fun k hk => MainIndOutBA_precL_shift sz n₀ _ _ _ _ (fun _ _ _ => rfl) (fun _ _ _ => rfl) (h1 k hk),
    fun k hk => MainIndOutBA_precL_shift sz n₀ _ _ _ _ (fun _ _ _ => rfl) (fun _ _ _ => rfl) (h2 k hk),
    fun D hD => MainIndOutBA_precL_shift sz n₀ _ _ _ _ (fun _ _ _ => rfl) (fun _ _ _ => rfl) (h3 D hD),
    MainIndOutBA_precL_shift sz n₀ _ _ _ _ (fun j u _ => ?_) (fun _ _ _ => rfl) h4,
    MainIndOutBA_precL_shift sz n₀ _ _ _ _ (fun _ _ _ => rfl) (fun _ _ _ => rfl) h5,
    fun D hD => MainIndOutBA_precL_shift sz n₀ _ _ _ _ (fun _ _ _ => rfl) (fun _ _ _ => rfl) (h6 D hD),
    MainIndOutBA_precL_shift sz n₀ _ _ _ _ (fun _ _ _ => rfl) (fun _ _ _ => rfl) h7⟩
  exact congrArg (fun x : ℂ => ‖x - C₁.K j (τ₁ j) u.1 u.2‖)
    (Sizes.integral_reindex (sz.withLam 0) (· + n₀) (MainIndOutBA_shift_mono n₀).injective
      (fun ω₁ => (baFMz (sz.comp (· + n₀)) fun j => z (j + n₀)).L j (τ (j + n₀)) u.1 u.2 ω₁)).symm

/-! ## 4. The chain of times over `Fam(p_k)` with the TL2 conjunct (probe `:197-261`) -/

/-- **The conclusions and TL2 at every `0 < t_n ≤ T0`, for every member of `Fam(t)`**: the family twin of `TwistChain_posConcl`
(`BA/TwistChain.lean:134`, private); the motive is "every member of `Fam(p_k)`" over `stChainTime`/`stChainSteps`
(`MainIndChain:51, 80`); base `baFamMember_base`, step `hmain`, the six premises from the seven by `STLocalMaxgL_of_STLocalEntrygL`
(`MainIndChain:126`); the main flow is a member (`BAFamZ_main`, `Step1Trivial:56`). -/
private theorem MainIndOutBA_posConclFam (d : ℕ) (hmain : BAMainIndFamTL d STAny)
    (hhor : STHorizonG d (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) (fun sz z => BAflowT0 sz z))
    (hbase : STBaseG d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) baFMz)
    (hTL : BATwistLoopBase d) (hG : ∀ κ ε 𝔠 𝔡 (sz : Sizes d) z, BAFlow sz κ ε 𝔠 𝔡 z → STG0M (baFMz sz z)) :
    3 ≤ d → ∀ κ ε 𝔡 𝔠 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z → (∀ n, 0 < sz.lam n) →
      ∀ c₁ : ℝ, 0 < c₁ → c₁ ≤ 1 / 2 → BAWinBulk sz z c₁ κ → ∀ t : ℕ → ℝ, (∀ n, 0 < t n) → (∀ n, t n ≤ BAflowT0 sz z n) →
        STConclgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) t ∧ BATwistLoopLaw (baFMz sz z) (Sizes.seqP (sz.withLam 0)) t := by
  intro hd κ ε 𝔡 𝔠 hκ hε h𝔡 sz z hf hlam c₁ hc₁ hc₁' hwin t ht0 htT
  obtain ⟨𝔠d, h𝔠d, -, H⟩ := hmain hd κ ε 𝔡 hκ hε h𝔡
  obtain ⟨⟨h𝔠, -, hsz, hbw, hWO⟩, hT, hr⟩ := hhor κ ε 𝔠 𝔡 sz z hκ hε hf
  have hμ : 0 < 𝔠d * min (2 * 𝔠 * 𝔡) (ε / 2) := mul_pos h𝔠d (lt_min (by have := h𝔡; positivity) (half_pos hε))
  obtain ⟨K, hK⟩ := exists_nat_ge (2 / (𝔠d * min (2 * 𝔠 * 𝔡) (ε / 2)))
  rw [div_le_iff₀ hμ] at hK
  have hK0 : 0 < K := Nat.pos_of_ne_zero fun h0 => by subst h0; norm_num at hK
  have key : ∀ k ≤ K, ∀ z', BAFamZ sz z c₁ (stChainTime t K k) z' → STConclgL (baFMz sz z') (Sizes.seqP (sz.withLam 0)) (stChainTime t K k) ∧
      BATwistLoopLaw (baFMz sz z') (Sizes.seqP (sz.withLam 0)) (stChainTime t K k) := by
    intro k
    induction k with
    | zero => intro _ z' hz'; rw [stChainTime_zero] at hz' ⊢; exact baFamMember_base d hbase hG hd κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hf hlam c₁ hc₁ hc₁' hwin z' hz'
    | succ k ih =>
      intro hk z' hz'
      have hf' := stChainTime_facts ht0 (fun n => (htT n).trans_lt (hT n).2) hK0 (by omega : k < K)
      obtain ⟨o1, o2, o3, o4, o5, o6, o7⟩ := H 𝔠 sz z hf hlam c₁ hc₁ hc₁' hwin _ _ (fun n => (hf' n).1)
        (fun n => ((hf' n).2.1.le.trans (hf' n).2.2).trans (htT n)) (fun n => (hf' n).2.1) (fun n => (hf' n).2.2.trans (htT n)) trivial
        (fun z'' hz'' => let ih' := ih (by omega) z'' hz''
          ⟨ih'.1.1, ih'.1.2.2.1, ih'.1.2.2.2.2.2, STLocalMaxgL_of_STLocalEntrygL _ _ _ ih'.1.2.2.2.2.1, ih'.1.2.2.2.1, ih'.2⟩)
        (stChainSteps sz h𝔠 h𝔡 (half_pos hε) h𝔠d hK hbw hWO hsz (fun n => (hT n).2) hr ht0 htT (by omega)) z' hz'
      exact ⟨⟨o1, o2, o3, o4, o5, o6⟩, o7⟩
  rw [← stChainTime_top t hK0]
  exact key K le_rfl z (BAFamZ_main _ _ _ _)

/-- **The family twin of `baChainTL_holds`** (`BA/TwistChain.lean:240`; target 6): tail `sz.comp (· + n₀)` at `κ/2` (`baTailPassage`);
the family chain at the tail to `t' = t` (`t_n > 0`) or `T₀/2` (`t_n = 0`); back along the shift (`baConclShift`); mix with the base at
`0` at the main flow (merged private `TwistChain_*_mix`).  The hypotheses are the family step `BAMainIndFamTL d STAny` and V3's own
facts (`STHorizonG`, `STBaseG`, `BATwistLoopBase`, `STG0M`). -/
theorem baChainFamTL_holds (d : ℕ) (hmain : BAMainIndFamTL d STAny)
    (hhor : STHorizonG d (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) (fun sz z => BAflowT0 sz z))
    (hbase : STBaseG d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) baFMz)
    (hTL : BATwistLoopBase d) (hG : ∀ κ ε 𝔠 𝔡 (sz : Sizes d) z, BAFlow sz κ ε 𝔠 𝔡 z → STG0M (baFMz sz z)) : BAMLOutTL d := by
  intro hd κ ε 𝔡 𝔠 hκ hε h𝔡 sz z hf t ht0 htT
  obtain ⟨hadm, hT, -⟩ := hhor κ ε 𝔠 𝔡 sz z hκ hε hf
  have hs : Tendsto sz.size atTop atTop := tendsto_natCast_atTop_iff.1 hadm.2.2.1
  set t' : ℕ → ℝ := fun n => if t n = 0 then BAflowT0 sz z n / 2 else t n with ht'
  have hpos : ∀ n, 0 < t' n := fun n => by
    by_cases h : t n = 0
    · simp only [ht', h, ite_true]; linarith [(hT n).1]
    · simp only [ht', h, ite_false]; exact lt_of_le_of_ne (ht0 n) (Ne.symm h)
  have hle : ∀ n, t' n ≤ BAflowT0 sz z n := fun n => by
    by_cases h : t n = 0
    · simp only [ht', h, ite_true]; linarith [(hT n).1]
    · simp only [ht', h, ite_false]; exact htT n
  have hm : ∀ n, t n = 0 ∨ t n = t' n := fun n => by
    by_cases h : t n = 0
    · exact Or.inl h
    · exact Or.inr (by simp only [ht', h, ite_false])
  obtain ⟨c₁, hc₁, hc₁', Ht⟩ := baTailPassage d hd κ 𝔡 hκ h𝔡
  obtain ⟨n₀, hf₁, hlam₁, hwin₁⟩ := Ht ε 𝔠 sz z hf
  have h1 := MainIndOutBA_posConclFam d hmain hhor hbase hTL hG hd (κ / 2) ε 𝔡 𝔠 (half_pos hκ) hε h𝔡 (sz.comp (· + n₀)) _ hf₁ hlam₁ c₁ hc₁ hc₁'
    hwin₁ (fun j => t' (j + n₀)) (fun j => hpos _) (fun j => hle _)
  have h1' := baConclShift sz z t' n₀ ⟨h1.1.1, h1.1.2.1, h1.1.2.2.1, h1.1.2.2.2.1, h1.1.2.2.2.2.1, h1.1.2.2.2.2.2, h1.2⟩
  have h0 := hbase hd κ ε 𝔡 𝔠 hκ hε h𝔡 sz z hf
  have h0TL := hTL hd κ ε 𝔡 𝔠 hκ hε h𝔡 sz z hf (hG κ ε 𝔠 𝔡 sz z hf)
  exact ⟨TwistChain_LK_mix _ _ hs hm h0.1 h1'.1, TwistChain_Lmax_mix _ _ hs hm h0.2.1 h1'.2.1,
    TwistChain_Decay_mix _ _ hs hm h0.2.2.1 h1'.2.2.1, TwistChain_Exp2_mix _ _ hs hm h0.2.2.2.1 h1'.2.2.2.1,
    TwistChain_LocalEntry_mix _ _ hs hm h0.2.2.2.2.1 h1'.2.2.2.2.1, TwistChain_TL2_mix _ _ hs hm h0TL h1'.2.2.2.2.2.2⟩

/-! ## 5. V3's base facts at BA: `G_0 = M`, `𝓛_0 = 𝒦_0`, the base case, the horizon (uniform over `BAFlow`) -/

/-- **`G_0 = M`** (target 7; `1_2:1240`) at the BA carrier, uniform over `BAFlow`: `Boot_GM_zero` (`Step1Boot:358`) at every `(lam0, E)`. -/
theorem baG0M_holds (d : ℕ) :
    ∀ (κ ε 𝔠 𝔡 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z → STG0M (baFMz sz z) := by
  intro κ ε 𝔠 𝔡 sz z _ n ω x y
  exact sub_eq_zero.mp (Boot_GM_zero sz (BAflowLam0 sz z) (BAflowEs sz z) n ω x y)

/-- `H_0 = g₀ Ψ` (copy of the `hH` step of `Boot_GM_zero`, `Step1Boot:360`). -/
private theorem MainIndOutBA_hflow_zero {d : ℕ} (sz : Sizes d) (lam0 : ℕ → ℝ) (n : ℕ) (ω : sz.SeqΩ) :
    sz.seqHflowBA lam0 n 0 ω = ((lam0 n : ℝ) : ℂ) • PsiI d (sz.L n) (sz.W n) := by
  ext i j
  have h : (sz.withLam 0).seqHflow n 0 ω i j = 0 := by
    have h0 : (sz.withLam 0).seqHflow n 0 ω = 0 := by simp [Sizes.seqHflow]
    rw [h0]
    rfl
  simp [Sizes.seqHflowBA, h]

/-- **`𝓛_0 = 𝒦_0`** (target 8; `1_2:1240-1243`) at the BA carrier at **every** `n`, uniform over `BAFlow`.  `𝓛_0 = BAMLoop`
(`GridGoodBA_loopFine_init`, needs `0 < Im m_F` from `BAflow_real`); `𝒦_0 = BAMLoop` from `CltFlowBA_Ksol_isKLoopS` (`BAReal` only,
no `0 < g₀`): the initial clause for length `≥ 2`, the one-loop clause with `GridGoodBA_BAMLoop_one_loop` for length `1`. -/
theorem baLK0_holds (d : ℕ) :
    ∀ (κ ε 𝔠 𝔡 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z → STLK0 (baFMz sz z) := by
  intro κ ε 𝔠 𝔡 sz z hf n k σ a ω hk
  have hr := BAflow_real κ ε 𝔠 𝔡 sz z hf n
  have hm : 0 < (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n).im := hr.1.1
  change BALloop sz (BAflowLam0 sz z) (BAflowEs sz z) n 0 σ a ω = BAKloop sz (BAflowLam0 sz z) (BAflowEs sz z) n 0 σ a
  unfold BALloop BAKloop
  rw [MainIndOutBA_hflow_zero sz _ n ω, GridGoodBA_loopFine_init sz _ _ n hm hk σ a]
  have hK := CltFlowBA_Ksol_isKLoopS (W := sz.W n) hr
  rcases Nat.lt_or_ge 1 k with h2 | h2
  · exact (hK.2.1 (loopOf σ a) (by simp [loopOf, LoopIdx.WF]) (by simp only [loopOf, LoopIdx.length, List.length_ofFn]; omega)).symm
  · obtain rfl : k = 1 := le_antisymm h2 hk
    have e : loopOf σ a = ⟨[σ 0], [a 0]⟩ := by simp [loopOf, List.ofFn_succ]
    rw [e, GridGoodBA_BAMLoop_one_loop hr.1 (σ 0) (a 0)]
    exact (hK.2.2 0 ⟨le_rfl, one_pos⟩ (σ 0) (a 0)).symm

/-- **`stBaseG_of_init`, generic, with `0 < ε → 0 < 𝔡 →` under the `hK` hypothesis** (target 9 (a); K3, supervisor `2026-10-11-0150`
`:87-93`): `stBaseG_of_init` (`MainIndBase:110`) at the setting `0 < ε ∧ 0 < 𝔡 ∧ Flow`; `STBaseG` supplies both. -/
theorem stBaseG_of_init' {d : ℕ} {law : ∀ sz : Sizes d, Measure sz.SeqΩ}
    {Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop} {mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz}
    (hprob : ∀ sz, IsProbabilityMeasure (law sz))
    (hL : ∀ κ ε 𝔠 𝔡 sz z, Flow sz κ ε 𝔠 𝔡 z → STLK0 (mk sz z))
    (hG : ∀ κ ε 𝔠 𝔡 sz z, Flow sz κ ε 𝔠 𝔡 z → STG0M (mk sz z))
    (hK : 3 ≤ d → ∀ κ ε 𝔠 𝔡 sz z, 0 < κ → 0 < ε → 0 < 𝔡 → Flow sz κ ε 𝔠 𝔡 z → STKboundgL (mk sz z) (law sz)) :
    STBaseG d law Flow mk := by
  intro hd κ ε 𝔡 𝔠 hκ hε h𝔡 sz z hf
  exact stBaseG_of_init (Flow := fun sz κ ε 𝔠 𝔡 z => 0 < ε ∧ 0 < 𝔡 ∧ Flow sz κ ε 𝔠 𝔡 z) hprob
    (fun _ _ _ _ sz z h => hL _ _ _ _ sz z h.2.2) (fun _ _ _ _ sz z h => hG _ _ _ _ sz z h.2.2)
    (fun hd κ ε 𝔠 𝔡 sz z hκ h => hK hd κ ε 𝔠 𝔡 sz z hκ h.1 h.2.1 h.2.2) hd κ ε 𝔡 𝔠 hκ hε h𝔡 sz z ⟨hε, h𝔡, hf⟩

/-- **The base case at the BA data** (target 9 (b); registry `Test/Axioms.lean:140`): `stBaseG_of_init'` with `baLK0_holds`, `baG0M_holds`,
`baKbound_holds` (`KBound:245`) and `isProbabilityMeasure_seqP`. -/
theorem baBaseG_holds (d : ℕ) :
    STBaseG d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) baFMz :=
  stBaseG_of_init' (fun sz => Sizes.isProbabilityMeasure_seqP (sz.withLam 0)) (baLK0_holds d) (baG0M_holds d)
    (fun hd κ ε 𝔠 𝔡 sz z hκ hε h𝔡 hf => baKbound_holds d hd κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hf)

/-- **The horizon at the BA data** (target 10; registry `:141`): admissible sizes (`hf.1`), `0 < T0 < 1` (`BAflow_T0_bounds`,
`Step1Trivial:47`), `N^{-1+ε/2} ≤ 1 - T0` eventually (`CltFlowBA_one_sub_T0`: `1 - T0 ≥ Im z/2` from `Im m ≤ 1`, `EMn2BA:111`). -/
theorem baHorizonG_holds (d : ℕ) :
    STHorizonG d (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) (fun sz z => BAflowT0 sz z) := by
  intro κ ε 𝔠 𝔡 sz z hκ hε hf
  exact ⟨hf.1, fun n => ⟨(BAflow_T0_bounds hκ hf n).2.2.1, (BAflow_T0_bounds hκ hf n).2.2.2⟩, CltFlowBA_one_sub_T0 hκ hε hf⟩

/-! ## 6. The terminal outputs (target 11) -/

/-- **The terminal plug-in**: `BAMLOutTL d` from the family step `BAMainIndFamTL d STAny` alone (6 at 10, 9, `baTwistLoopBase_holds`, 7). -/
theorem baMLOutTL_of_famStep (d : ℕ) (hmain : BAMainIndFamTL d STAny) : BAMLOutTL d :=
  baChainFamTL_holds d hmain (baHorizonG_holds d) (baBaseG_holds d) (baTwistLoopBase_holds d) (baG0M_holds d)

/-- **V3 is a projection** (T2449 MN2, probe `t/T2449:RBM3D/Probe/T2449Pins.lean:259`): `BAMLOutTL` drops its sixth conjunct
`BATwistLoopLaw` to `UNMLOutBA` (`BA/UNPins.lean:110`). -/
theorem unMLOutBA_of_BAMLOutTL (d : ℕ) (h : BAMLOutTL d) : Univ.UNMLOutBA d := by
  intro hd κ ε 𝔡 𝔠 hκ hε h𝔡 sz z hf t ht0 ht
  obtain ⟨h1, h2, h3, h4, h5, -⟩ := h hd κ ε 𝔡 𝔠 hκ hε h𝔡 sz z hf t ht0 ht
  exact ⟨h1, h2, h3, h4, h5⟩

/-- **The composite**: `UNMLOutBA d` from the family step `BAMainIndFamTL d STAny` alone. -/
theorem unMLOutBA_of_famStep (d : ℕ) (hmain : BAMainIndFamTL d STAny) : Univ.UNMLOutBA d :=
  unMLOutBA_of_BAMLOutTL d (baMLOutTL_of_famStep d hmain)

/-! ## 7. Compiled `d = 3` instances (target 12)

Data (probe `t/T2503:RBM3D/Probe/T2503Pins.lean:310-391`, re-declared under this stem): `sz0` (`Defs/Sizes.lean:260`), `zSeq`,
`flow_sz0` weakened to `κ = 1/4`, `(ε, 𝔠, 𝔡) = (1/10, 1/6, 1/10)`, `c₁ = 1/3` (`sz0_win_third`), `s ≡ 1/10 < t ≡ 1/2 ≤ T₀`
(`half_lt_t0`); the non-main member is the ConArg source `BAzSrc` (`inst_BAFamZ_closed`).  Targets 7-10 and the per-member base (3) are
hypothesis-free; the family step `BAMainIndFamTL 3 STAny` (V2a, V2b) is the one hypothesis of 6 and 11; the seven tail conclusions are
the hypothesis of 5. -/

section Inst

open RBM.BA.FlowPinsInst RBM.Gauss.SizesInst RBM.BA.Step1FamInst
local notation "μ0" => Sizes.seqP (sz0.withLam 0)
local notation "mem0" => BAzSrc sz0 zSeq (fun _ => 2 / 3) (fun _ => 17 / 25)

private theorem MainIndOutBA_flow : BAFlow sz0 (1 / 4) (1 / 10) (1 / 6) (1 / 10) zSeq :=
  ⟨flow_sz0.1, fun n => ⟨(by norm_num : (1 / 4 : ℝ) ≤ 1 / 2).trans (flow_sz0.2 n).1, (flow_sz0.2 n).2⟩⟩

private theorem MainIndOutBA_win : BAWinBulk sz0 zSeq (1 / 3) (1 / 4) := fun n g h1 h2 =>
  (by norm_num : (1 / 4 : ℝ) ≤ 1 / 2).trans (sz0_win_third n g h1 h2)

private theorem MainIndOutBA_mem (u : ℝ) (hu : max u (1 - 1 / 3) ≤ max (2 / 3) (1 - 1 / 3)) :
    BAFamZ sz0 zSeq (1 / 3) (fun _ => u) mem0 :=
  BAFamZ_mono_max sz0 zSeq (1 / 3) _ (fun _ => 2 / 3) _ (fun _ => hu) inst_BAFamZ_closed

-- targets 7, 8: `G_0 = M` and `𝓛_0 = 𝒦_0` at `zSeq` (hypothesis-free)
example : STG0M (baFMz sz0 zSeq) := baG0M_holds 3 (1 / 4) (1 / 10) (1 / 6) (1 / 10) sz0 zSeq MainIndOutBA_flow
example : STLK0 (baFMz sz0 zSeq) := baLK0_holds 3 (1 / 4) (1 / 10) (1 / 6) (1 / 10) sz0 zSeq MainIndOutBA_flow

-- target 9 (a): the generic `stBaseG_of_init'` at the BA data and at `zSeq`
example : STConclgL (baFMz sz0 zSeq) μ0 (fun _ => 0) :=
  stBaseG_of_init' (law := fun sz => Sizes.seqP (sz.withLam 0)) (Flow := fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) (mk := baFMz)
    (fun sz => Sizes.isProbabilityMeasure_seqP (sz.withLam 0)) (baLK0_holds 3) (baG0M_holds 3)
    (fun hd κ ε 𝔠 𝔡 sz z hκ hε h𝔡 hf => baKbound_holds 3 hd κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hf)
    le_rfl (1 / 4) (1 / 10) (1 / 10) (1 / 6) (by norm_num) (by norm_num) (by norm_num) sz0 zSeq MainIndOutBA_flow

-- target 9 (b): the six conclusions at the zero sequence at `zSeq`
example : STConclgL (baFMz sz0 zSeq) μ0 (fun _ => 0) :=
  baBaseG_holds 3 le_rfl (1 / 4) (1 / 10) (1 / 10) (1 / 6) (by norm_num) (by norm_num) (by norm_num) sz0 zSeq MainIndOutBA_flow

-- target 10: admissible sizes, `0 < T₀ < 1`, `N^{-1+ε/2} ≤ 1 - T₀` eventually, at `zSeq`
example : sz0.Admissible (1 / 6) (1 / 10) ∧ (∀ n, 0 < BAflowT0 sz0 zSeq n ∧ BAflowT0 sz0 zSeq n < 1) ∧
    ∀ᶠ n in atTop, ((sz0.size n : ℕ) : ℝ) ^ (-1 + (1 / 10 : ℝ) / 2) ≤ 1 - BAflowT0 sz0 zSeq n :=
  baHorizonG_holds 3 (1 / 4) (1 / 10) (1 / 6) (1 / 10) sz0 zSeq (by norm_num) (by norm_num) MainIndOutBA_flow

-- target 2 (a): TL2 at `zSeq` and at its finite modification `zMod` (`zMod_ev`: equal for `n ≥ 3`)
example (μ : Measure sz0.SeqΩ) (τ : ℕ → ℝ) :
    BATwistLoopLaw (baFMz sz0 zSeq) μ τ ↔ BATwistLoopLaw (baFMz sz0 zMod) μ τ :=
  BATwistLoopLaw_congr 3 sz0 _ _ μ τ (zMod_ev.mono fun n hn => baFMz_eqAt sz0 hn)

-- target 2 (b): the non-main member of `Fam(1/2)` as a flow at `(κ', ε')` after the finite modification, horizon `≥ 1/2`, `EvEq`
example : ∃ κ' ε' : ℝ, 0 < κ' ∧ κ' ≤ 1 / 4 ∧ 0 < ε' ∧ ε' ≤ 1 / 10 ∧ (∀ n, 1 / 2 ≤ BAflowT0 sz0 mem0 n) ∧
    ∃ z'' : ℕ → ℂ, BAFlow sz0 κ' ε' (1 / 6) (1 / 10) z'' ∧ (∀ n, 1 / 2 ≤ BAflowT0 sz0 z'' n) ∧ (baFMz sz0 z'').EvEq (baFMz sz0 mem0) := by
  obtain ⟨κ', ε', h1, h2, h3, h4, H⟩ := baFamMember_flow 3 (1 / 4) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨κ', ε', h1, h2, h3, h4, H (1 / 6) sz0 zSeq MainIndOutBA_flow sz0_lam_pos (1 / 3) (by norm_num) (by norm_num) MainIndOutBA_win
    (fun _ => 1 / 2) (fun _ => by norm_num) (fun n => (half_lt_t0 n).le) mem0 (MainIndOutBA_mem _ (by norm_num))⟩

-- target 3: the per-member base at the non-main member of `Fam(0)` (hypothesis-free; `baBaseG_holds`, `baG0M_holds` discharge `hbase`, `hG`)
example : STConclgL (baFMz sz0 mem0) μ0 (fun _ => 0) ∧ BATwistLoopLaw (baFMz sz0 mem0) μ0 (fun _ => 0) :=
  baFamMember_base 3 (baBaseG_holds 3) (baG0M_holds 3) le_rfl (1 / 4) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num)
    (1 / 6) sz0 zSeq MainIndOutBA_flow sz0_lam_pos (1 / 3) (by norm_num) (by norm_num) MainIndOutBA_win mem0 (MainIndOutBA_mem 0 (by norm_num))

-- target 4: the tail of `sz0` along `zSeq` at `κ = 1/2` (`flow_sz0`): flow at `κ/2`, window at `κ/2`
example : ∃ c₁ : ℝ, 0 < c₁ ∧ c₁ ≤ 1 / 2 ∧ ∃ n₀ : ℕ, BAFlow (sz0.comp (· + n₀)) (1 / 2 / 2) (1 / 10) (1 / 6) (1 / 10) (fun j => zSeq (j + n₀)) ∧
    (∀ j, 0 < (sz0.comp (· + n₀)).lam j) ∧ BAWinBulk (sz0.comp (· + n₀)) (fun j => zSeq (j + n₀)) c₁ (1 / 2 / 2) := by
  obtain ⟨c₁, h0, h1, H⟩ := baTailPassage 3 le_rfl (1 / 2) (1 / 10) (by norm_num) (by norm_num)
  obtain ⟨n₀, hf, hl, hw⟩ := H (1 / 10) (1 / 6) sz0 zSeq flow_sz0
  exact ⟨c₁, h0, h1, n₀, hf, hl, hw⟩

-- target 5: the seven conclusions along the tail (`n₀ = 3`, `τ ≡ 1/2`) give the seven along `sz0`; the seven at the tail are the hypothesis
example (h : let C₁ := baFMz (sz0.comp (· + 3)) (fun j => zSeq (j + 3)); let μ₁ := Sizes.seqP ((sz0.comp (· + 3)).withLam 0)
    STLKgL C₁ μ₁ (fun _ => 1 / 2) ∧ STLmaxgL C₁ μ₁ (fun _ => 1 / 2) ∧ STDecaygL C₁ μ₁ (fun _ => 1 / 2) ∧ STExp2gL C₁ μ₁ (fun _ => 1 / 2) ∧
      STLocalEntrygL C₁ μ₁ (fun _ => 1 / 2) ∧ STDecayStronggL C₁ μ₁ (fun _ => 1 / 2) ∧ BATwistLoopLaw C₁ μ₁ (fun _ => 1 / 2)) :
    STLKgL (baFMz sz0 zSeq) μ0 (fun _ => 1 / 2) ∧ STLmaxgL (baFMz sz0 zSeq) μ0 (fun _ => 1 / 2) ∧
      STDecaygL (baFMz sz0 zSeq) μ0 (fun _ => 1 / 2) ∧ STExp2gL (baFMz sz0 zSeq) μ0 (fun _ => 1 / 2) ∧
      STLocalEntrygL (baFMz sz0 zSeq) μ0 (fun _ => 1 / 2) ∧ STDecayStronggL (baFMz sz0 zSeq) μ0 (fun _ => 1 / 2) ∧
      BATwistLoopLaw (baFMz sz0 zSeq) μ0 (fun _ => 1 / 2) :=
  baConclShift sz0 zSeq (fun _ => 1 / 2) 3 h

-- target 6: `BAMLOutTL 3` at `t ≡ 1/2` and at `t ≡ 0` (the class mixed with the chain to `T₀/2`); the family step is the one hypothesis
section Chain3
variable (hm : BAMainIndFamTL 3 STAny)
include hm

example := baChainFamTL_holds 3 hm (baHorizonG_holds 3) (baBaseG_holds 3) (baTwistLoopBase_holds 3) (baG0M_holds 3) le_rfl (1 / 4) (1 / 10)
  (1 / 10) (1 / 6) (by norm_num) (by norm_num) (by norm_num) sz0 zSeq MainIndOutBA_flow (fun _ => 1 / 2) (fun _ => by norm_num)
  (fun n => (half_lt_t0 n).le)
example := baChainFamTL_holds 3 hm (baHorizonG_holds 3) (baBaseG_holds 3) (baTwistLoopBase_holds 3) (baG0M_holds 3) le_rfl (1 / 4) (1 / 10)
  (1 / 10) (1 / 6) (by norm_num) (by norm_num) (by norm_num) sz0 zSeq MainIndOutBA_flow (fun _ => 0) (fun _ => le_rfl)
  (fun n => by linarith [half_lt_t0 n])

-- target 11: the terminal plug-in, the projection and the composite at the data
example := baMLOutTL_of_famStep 3 hm le_rfl (1 / 4) (1 / 10) (1 / 10) (1 / 6) (by norm_num) (by norm_num) (by norm_num) sz0 zSeq
  MainIndOutBA_flow (fun _ => 1 / 2) (fun _ => by norm_num) (fun n => (half_lt_t0 n).le)
example := unMLOutBA_of_BAMLOutTL 3 (baMLOutTL_of_famStep 3 hm) le_rfl (1 / 4) (1 / 10) (1 / 10) (1 / 6) (by norm_num) (by norm_num)
  (by norm_num) sz0 zSeq MainIndOutBA_flow (fun _ => 1 / 2) (fun _ => by norm_num) (fun n => (half_lt_t0 n).le)
example := unMLOutBA_of_famStep 3 hm le_rfl (1 / 4) (1 / 10) (1 / 10) (1 / 6) (by norm_num) (by norm_num) (by norm_num) sz0 zSeq
  MainIndOutBA_flow (fun _ => 0) (fun _ => le_rfl) (fun n => by linarith [half_lt_t0 n])
end Chain3

end Inst

end RBM.BA
