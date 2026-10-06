/-
T2256 check file (BA-S2b1, dispatcher V1, Tue Oct  6 04:19 UTC 2026).  Pin texts and the
statements of the proof targets of `RBM3D/BA/Step1Boot.lean`.  Defs, `#check`s and Prop-valued
`example`s only: no proofs.  Compiles on `main` (88183b6) as is.
-/
import RBM3D.BA.ConArg
import RBM3D.BA.Step1Trivial
import RBM3D.Induction.Step1

open MeasureTheory ProbabilityTheory Filter Matrix

/-! ## 0. Merged names used (each `#check` with its full namespace) -/

-- BA carrier and family (T2197 `FlowPins.lean`, T2238 `Step1Trivial.lean`, T2227 `CouplingWindow.lean`)
#check @RBM.BA.PrecL
#check @RBM.BA.FlowFM
#check @RBM.BA.FlowFM.GM
#check @RBM.BA.STmaxLoop2g
#check @RBM.BA.STInitialGT2gL
#check @RBM.BA.STKboundgL
#check @RBM.BA.STLKgL
#check @RBM.BA.STLocalMaxgL
#check @RBM.BA.STStep1LoopgL
#check @RBM.BA.STStep1WeakgL
#check @RBM.BA.baFM
#check @RBM.BA.baFMz
#check @RBM.BA.BAFlow
#check @RBM.BA.BAflowT0
#check @RBM.BA.BAflowEs
#check @RBM.BA.BAflowLam0
#check @RBM.BA.BAmF
#check @RBM.BA.BAMfine
#check @RBM.BA.BAlamS
#check @RBM.BA.BAConArgVec
#check @RBM.BA.BAWinBulk
#check @RBM.BA.BAFamZ
#check @RBM.BA.BAFamZ_main
#check @RBM.BA.BAFamZ_im_m_ge
#check @RBM.BA.BAflow_T0_bounds
#check @RBM.BA.baFM_loop_det
#check @RBM.BA.BATrivialLmax
#check @RBM.BA.BATrivialLmax_holds
-- BA-S1 (T2237 `ConArg.lean`, event form)
#check @RBM.BA.FlowFM.omegaC
#check @RBM.BA.BAConArgLoop''
#check @RBM.BA.BAConArg''
#check @RBM.BA.baConArg''_holds
#check @RBM.BA.bandFM_omegaC
#check @RBM.BA.BAself_norm_le_one
-- band model (T2028 `Induction/Defs.lean`, `Step1Setup.lean`, T2090 `Step1.lean`)
#check @RBM.Gauss.Sizes.STindMax
#check @RBM.Gauss.Sizes.STgexRHS
#check @RBM.Gauss.Sizes.STGiiGEX
#check @RBM.Gauss.Sizes.STGijGEX
#check @RBM.Gauss.Sizes.STGavLGEX
#check @RBM.Gauss.Sizes.STGbEXPii
#check @RBM.Gauss.Sizes.STGbEXPij
#check @RBM.Gauss.Sizes.STGbEXPav
#check @RBM.Gauss.Sizes.STomegaC
#check @RBM.Gauss.Sizes.STConStInd
#check @RBM.Gauss.Sizes.STblk
#check @RBM.Ind.Step1TargetV3
#check @RBM.Ind.step1TargetV3_holds
#check @RBM.Ind.s1_LI
#check @RBM.Ind.s1_loop_det
#check @RBM.Ind.s1_omegaC_eq_one
#check @RBM.Ind.s1_Wd_le_Bctl

namespace RBM.BA.T2256Check

open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes RBM.BA

/-! ## 1. Vocabulary (ℝ-valued; in the new file: `FlowFM.indMax`, `FlowFM.gexRHS`, namespace `RBM.BA`) -/

/-- The indicator of `{‖G_t - M‖_max ≤ A}` over a carrier (the band's `STindMax`, `Defs.lean:197`, at
`bandFM`). -/
noncomputable def indMax {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (n : ℕ) (t A : ℝ) (ω : sz.SeqΩ) : ℝ :=
  if ∀ x y : Idx d (sz.L n) (sz.W n), ‖C.GM n t ω x y‖ ≤ A then 1 else 0

/-- The right side of `(GijGEX)` over a carrier (the band's `STgexRHS`, `Defs.lean:92`, at `bandFM`). -/
noncomputable def gexRHS {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (n : ℕ) (t : ℝ) (ω : sz.SeqΩ)
    (a b : Zd d (sz.L n)) : ℝ :=
  (∑ σ ∈ ({![true, false], ![false, true]} : Finset (Fin 2 → Bool)),
    ∑ a' ∈ Finset.univ.filter (fun a' : Zd d (sz.L n) => zdistInf d (sz.L n) (a' - a) ≤ 1),
      ∑ b' ∈ Finset.univ.filter (fun b' : Zd d (sz.L n) => zdistInf d (sz.L n) (b' - b) ≤ 1),
        ‖C.L n t σ ![a', b'] ω‖) +
    (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (if zdistInf d (sz.L n) (a - b) ≤ 1 then 1 else 0)

/-! ## 2. The event forms of `lem_GbEXP_BA` (supervisor 2252 Q2, DECISIONS §72 (4)) -/

/-- `(GiiGEX)` for the block Anderson flow `z` at the time sequence `t` (band `STGiiGEX`, `Defs.lean:202`). -/
def BAGiiGEX {d : ℕ} (sz : Sizes d) (z : ℕ → ℂ) (t : ℕ → ℝ) (ε₀ : ℝ) : Prop :=
  PrecL sz (Sizes.seqP (sz.withLam 0)) (U := fun n => Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n))
    (fun n p ω => indMax (baFMz sz z) n (t n) (((sz.W n : ℕ) : ℝ) ^ (-ε₀)) ω *
      ‖(baFMz sz z).GM n (t n) ω p.1 p.2‖ ^ 2)
    (fun n _ ω => STmaxLoop2g (baFMz sz z) n (t n) ω)

/-- `(GijGEX)` for the block Anderson flow, on `(G_t - M)_{xy}`, `x ≠ y` (band `STGijGEX`, `Defs.lean:210`, has
`(G_t)_{xy}`: there `M = m I`; here `M = Mres(g₀Ψ, E, m)` is not diagonal; preflight P2). -/
def BAGijGEX {d : ℕ} (sz : Sizes d) (z : ℕ → ℂ) (t : ℕ → ℝ) (ε₀ : ℝ) : Prop :=
  PrecL sz (Sizes.seqP (sz.withLam 0))
    (U := fun n => {p : Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n) // p.1 ≠ p.2})
    (fun n p ω => indMax (baFMz sz z) n (t n) (((sz.W n : ℕ) : ℝ) ^ (-ε₀)) ω *
      ‖(baFMz sz z).GM n (t n) ω p.1.1 p.1.2‖ ^ 2)
    (fun n p ω => gexRHS (baFMz sz z) n (t n) ω (STblk sz n p.1.1) (STblk sz n p.1.2))

/-- `(GavLGEX)` for the block Anderson flow under `(initialGT2)` (band `STGavLGEX`, `Defs.lean:220`; no event,
as the band's). -/
def BAGavLGEX {d : ℕ} (sz : Sizes d) (z : ℕ → ℂ) (t : ℕ → ℝ) (ε₀ : ℝ) : Prop :=
  ∀ Ψ : ℕ → ℝ, (∀ᶠ n in atTop, ((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2) ≤ Ψ n) →
    (∀ᶠ n in atTop, Ψ n ≤ ((sz.W n : ℕ) : ℝ) ^ (-ε₀)) →
    STInitialGT2gL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) t ε₀ Ψ →
    PrecL sz (Sizes.seqP (sz.withLam 0)) (U := fun n => Zd d (sz.L n))
      (fun n a ω => ‖(baFMz sz z).L n (t n) (fun _ : Fin 1 => true) (fun _ => a) ω - (baFMz sz z).m n‖)
      (fun n _ _ => Ψ n ^ 2)

/-- **`lem_GbEXP_BA`, `(GiiGEX)`, event form** (`7_8:1916-1946`; owed, BA-G6). -/
def BAGbEXPii (d : ℕ) : Prop :=
  ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z →
      ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ BAflowT0 sz z n) →
        ∀ ε₀ : ℝ, 0 < ε₀ → BAGiiGEX sz z t ε₀

/-- **`lem_GbEXP_BA`, `(GijGEX)`, event form** (owed, BA-G6). -/
def BAGbEXPij (d : ℕ) : Prop :=
  ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z →
      ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ BAflowT0 sz z n) →
        ∀ ε₀ : ℝ, 0 < ε₀ → BAGijGEX sz z t ε₀

/-- **`lem_GbEXP_BA`, `(GavLGEX)`** (owed, BA-G6). -/
def BAGbEXPav (d : ℕ) : Prop :=
  ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z →
      ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ BAflowT0 sz z n) →
        ∀ ε₀ : ℝ, 0 < ε₀ → BAGavLGEX sz z t ε₀

/-! ## 3. `BAFlowMember` (probe `t/T2205:…T2205Pins.lean:1796-1803`, verbatim; owed, BA-S3) -/

def BAFlowMember (d : ℕ) : Prop :=
  ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∃ κ' ε' : ℝ, 0 < κ' ∧ κ' ≤ κ ∧ 0 < ε' ∧ ε' ≤ ε ∧
      ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z → (∀ n, 0 < sz.lam n) →
        ∀ c₁ : ℝ, 0 < c₁ → c₁ ≤ 1 / 2 → BAWinBulk sz z c₁ κ →
          ∀ z' : ℕ → ℂ, BAFamZ sz z c₁ (fun _ => 0) z' →
            ∃ n₀ : ℕ, BAFlow sz κ' ε' 𝔠 𝔡 (fun n => if n < n₀ then z n else z' n)

/-! ## 4. `BABootstrap'` (probe `:1809-1826` with the ConArg-output premise of supervisor 0255 §1.2;
owed, BA-S2b2) -/

def BABootstrap' (d : ℕ) : Prop :=
  ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ 𝔠d : ℝ, 0 < 𝔠d → 𝔠d ≤ 1 / 100 →
      ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z → (∀ n, 0 < sz.lam n) →
        ∀ c₁ : ℝ, 0 < c₁ → c₁ ≤ 1 / 2 → BAWinBulk sz z c₁ κ →
          ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n ≤ BAflowT0 sz z n) → (∀ n, s n < t n) →
            (∀ n, t n ≤ BAflowT0 sz z n) →
            ∀ z' : ℕ → ℂ, BAFamZ sz z c₁ t z' →
              STKboundgL (baFMz sz z') (Sizes.seqP (sz.withLam 0)) →
              STLKgL (baFMz sz z') (Sizes.seqP (sz.withLam 0)) s →
              STLocalMaxgL (baFMz sz z') (Sizes.seqP (sz.withLam 0)) s → STConStInd sz 𝔠d s t →
              (∀ u : ℕ → ℝ, (∀ n, max (s n) (1 - c₁) ≤ u n) → (∀ n, u n ≤ t n) →
                (∀ C₀ : ℝ, 0 < C₀ → ∀ k : ℕ, 2 ≤ k →
                    BAConArgLoop'' sz z' (fun n => max (s n) (1 - c₁)) u k C₀) ∧
                  BAConArgVec sz z' (fun n => max (s n) (1 - c₁)) u) →
              STStep1LoopgL (baFMz sz z') (Sizes.seqP (sz.withLam 0)) s t ∧
                STStep1WeakgL (baFMz sz z') (Sizes.seqP (sz.withLam 0)) s t

/-! ## 5. Statements of the proof targets (names in the new file without `_stmt`) -/

/-- Target 3a: the event form `(GiiGEX)` at every member `z'` of `Fam(t)` and every `u ≤ t`. -/
def baGii_member_stmt (d : ℕ) : Prop :=
  BAGbEXPii d → BAFlowMember d →
  ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z → (∀ n, 0 < sz.lam n) →
      ∀ c₁ : ℝ, 0 < c₁ → c₁ ≤ 1 / 2 → BAWinBulk sz z c₁ κ →
        ∀ t : ℕ → ℝ, (∀ n, t n ≤ BAflowT0 sz z n) → ∀ z' : ℕ → ℂ, BAFamZ sz z c₁ t z' →
          ∀ u : ℕ → ℝ, (∀ n, 0 ≤ u n) → (∀ n, u n ≤ t n) → ∀ ε₀ : ℝ, 0 < ε₀ → BAGiiGEX sz z' u ε₀

/-- Target 3b: the same for `(GijGEX)`. -/
def baGij_member_stmt (d : ℕ) : Prop :=
  BAGbEXPij d → BAFlowMember d →
  ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z → (∀ n, 0 < sz.lam n) →
      ∀ c₁ : ℝ, 0 < c₁ → c₁ ≤ 1 / 2 → BAWinBulk sz z c₁ κ →
        ∀ t : ℕ → ℝ, (∀ n, t n ≤ BAflowT0 sz z n) → ∀ z' : ℕ → ℂ, BAFamZ sz z c₁ t z' →
          ∀ u : ℕ → ℝ, (∀ n, 0 ≤ u n) → (∀ n, u n ≤ t n) → ∀ ε₀ : ℝ, 0 < ε₀ → BAGijGEX sz z' u ε₀

/-- Target 4a: the entries of `M = Mres(g₀Ψ, E, m)` are at most `(Im m)⁻¹` (deterministic). -/
def baM_entry_le_stmt (d : ℕ) : Prop :=
  ∀ (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ), 0 < (BAmF sz lam0 E n).im →
    ∀ x y : Idx d (sz.L n) (sz.W n), ‖(baFM sz lam0 E).M n x y‖ ≤ ((BAmF sz lam0 E n).im)⁻¹

/-- Target 4b: on `‖G_u - M‖_max ≤ 1` the event `Ω_u` of threshold `1 + (Im m)⁻¹` holds (the band's
`s1_omegaC_eq_one`, `Step1Setup.lean:988`, with `|m| ≤ 1` replaced by target 4a). -/
def baOmegaC_eq_one_stmt (d : ℕ) : Prop :=
  ∀ (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ) (u : ℝ) (ω : sz.SeqΩ), 0 < (BAmF sz lam0 E n).im →
    (∀ x y : Idx d (sz.L n) (sz.W n), ‖(baFM sz lam0 E).GM n u ω x y‖ ≤ 1) →
    (baFM sz lam0 E).omegaC n u (1 + ((BAmF sz lam0 E n).im)⁻¹) ω = 1

/-- Target 5: the BA `s1_LI` (`Step1Setup.lean:774`): the event-form loop bound of a member `z'` of `Fam(t)` at every
time sequence `u ∈ [s, t]`, every `C₀ > 0`, every `k ≥ 1`, from the ConArg output on `[s₁, t]`, `s₁ = max(s, 1 - c₁)`,
and the deterministic bound below `s₁` (`baFM_loop_det`, `BAFamZ_im_m_ge`). -/
def baBoot_LI_stmt (d : ℕ) : Prop :=
  ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z → (∀ n, 0 < sz.lam n) →
      ∀ c₁ : ℝ, 0 < c₁ → c₁ ≤ 1 / 2 → BAWinBulk sz z c₁ κ →
        ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n ≤ t n) → (∀ n, t n ≤ BAflowT0 sz z n) →
          ∀ z' : ℕ → ℂ, BAFamZ sz z c₁ t z' →
            (∀ u : ℕ → ℝ, (∀ n, max (s n) (1 - c₁) ≤ u n) → (∀ n, u n ≤ t n) →
              ∀ C₀ : ℝ, 0 < C₀ → ∀ k : ℕ, 2 ≤ k →
                BAConArgLoop'' sz z' (fun n => max (s n) (1 - c₁)) u k C₀) →
            ∀ C₀ : ℝ, 0 < C₀ → ∀ u : ℕ → ℝ, (∀ n, u n ∈ Set.Icc (s n) (t n)) → ∀ k : ℕ, 1 ≤ k →
              PrecL sz (Sizes.seqP (sz.withLam 0)) (U := fun n => (Fin k → Bool) × (Fin k → Zd d (sz.L n)))
                (fun n p ω => (baFMz sz z').omegaC n (u n) C₀ ω * ‖(baFMz sz z').L n (u n) p.1 p.2 ω‖)
                (fun n _ _ => ((1 - s n) / (1 - u n)) ^ (k - 1) * (sz.Bctl n (s n)) ^ (k - 1))

/-! ## 6. Prop-valued examples (no proof obligations) -/

example : Prop := BAGbEXPii 3 ∧ BAGbEXPij 3 ∧ BAGbEXPav 3
example : Prop := BAFlowMember 3 → BABootstrap' 3
example : Prop := baGii_member_stmt 3 ∧ baGij_member_stmt 3 ∧ baBoot_LI_stmt 3
example : Prop := baM_entry_le_stmt 3 ∧ baOmegaC_eq_one_stmt 3

end RBM.BA.T2256Check
