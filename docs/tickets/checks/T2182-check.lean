/-
Release check for T2182 (dispatcher V1, Mon Oct  5 05:57 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §19, §29, §45 O2).
S5-25: `lem;CLT`, far part (`STCltFar`, `3_5:2173-2249`): the assembly of `f^{far} ≺ A^{-6/5}/(|a₁-a₂|^{d-2}+1)` from
the decomposition `f - 𝔼f = c_n · fluc + off` (S5-24), the mean part (S5-22b), the eventual moment/Markov bound of the
window fluctuation (S5-24 on the isolation bound of S5-21), the off-window bound `(eq:propcalB)` and the per-label tail
`CltMom2.DomHyp`, both from `(Eq:Gdecay_w)` at `u = s`.  Section 1: the merged names it builds on and the downstream
instance.  Section 2: the three pinned intermediate statements, in namespace `RBM.Gauss.Sizes.T2182Check` here; T2182
defines them in `RBM.Gauss.Sizes` verbatim.  The endpoint is the merged pin `STCltFar` itself.
Statement and `#check` only: no proofs, no `sorry`.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2182-check.lean`.
-/
import RBM3D

/-! ## 1. Merged names -/

-- the pin and its objects (S5-01 `Induction/Step5Pins`)
#check @RBM.Gauss.Sizes.STfFar
#check @RBM.Gauss.Sizes.STCltFarConcl
#check @RBM.Gauss.Sizes.STCltFar
#check @RBM.Gauss.Sizes.STcltB
#check @RBM.Gauss.Sizes.STcltX
#check @RBM.Gauss.Sizes.STCltIsoConcl
#check @RBM.Gauss.Sizes.STCltIso
#check @RBM.Gauss.Sizes.STReg5I
#check @RBM.Gauss.Sizes.STIngR5
-- S5-24 (`Evolution/CltMoments2`, T2169 7738afa)
#check @RBM.Evol.CltMom2.Z
#check @RBM.Evol.CltMom2.fluc
#check @RBM.Evol.CltMom2.off
#check @RBM.Evol.CltMom2.BY
#check @RBM.Evol.CltMom2.DomHyp
#check @RBM.Evol.CltMom2.IsoHyp
#check @RBM.Evol.CltMom2.rhs
#check @RBM.Evol.CltMom2.BYStmt
#check @RBM.Evol.CltMom2.DecompStmt
#check @RBM.Evol.CltMom2.MomentStmt
#check @RBM.Evol.CltMom2.TailStmt
#check @RBM.Evol.cltMom2_decomp
#check @RBM.Evol.cltMom2_norm_stcltB_le
#check @RBM.Evol.cltMom2_moment_fixed
#check @RBM.Evol.cltMom2_tail_eventually
#check @RBM.Evol.CltMom1.cs
#check @RBM.Evol.CltMom1.Cd
-- S5-21 (isolation), S5-22b (mean part)
#check @RBM.Gauss.Sizes.stCltIso_holds
#check @RBM.Gauss.Sizes.STMeanFarConcl
#check @RBM.Gauss.Sizes.stMeanFar
#check @RBM.Gauss.Sizes.meanFar_eventually
#check @RBM.Gauss.Sizes.meanFar_T1
-- S5-02 kit (`Induction/Step5Kit`)
#check @RBM.Gauss.Sizes.st5_prec_mono
#check @RBM.Gauss.Sizes.st5_conStInd_mono
#check @RBM.Gauss.Sizes.st5_zdistInf_le
#check @RBM.Gauss.Sizes.st5_t_lt_one
#check @RBM.Gauss.Sizes.st5_eventually_A_ge_one
#check @RBM.Gauss.Sizes.st5_Bctl_le_one
#check @RBM.Gauss.Sizes.ST_step5_caseI_of_pins
-- Step 2 input, sizes, controls
#check @RBM.Gauss.Sizes.STGdecayW
#check @RBM.Gauss.Sizes.STStep2Concl
#check @RBM.Gauss.Sizes.STAI
#check @RBM.Gauss.Sizes.STWB
#check @RBM.Gauss.Sizes.Bctl
#check @RBM.Gauss.Sizes.st_Bctl_pos
#check @RBM.Gauss.Sizes.STConStInd
#check @RBM.Gauss.Sizes.STFlow
#check @RBM.Gauss.Sizes.STflowE
#check @RBM.Gauss.Sizes.Admissible
#check @RBM.Gauss.Sizes.lam_sq_mul_pow_ge
#check @RBM.Gauss.Sizes.STLKM
#check @RBM.Gauss.Sizes.STKloop
#check @RBM.Gauss.Sizes.Lloop
#check @RBM.Gauss.Sizes.norm_Lloop_le
#check @RBM.Gauss.Sizes.walk_measurable_Lloop
#check @RBM.Gauss.Sizes.seqP
#check @RBM.Gauss.Sizes.seqHflow
-- the `≺` calculus (`Defs/StochDomAt`)
#check @RBM.badSetAt
#check @RBM.StochDomAt
#check @RBM.Gauss.Sizes.Prec
#check @RBM.Gauss.Sizes.prec_of_le
#check @RBM.Gauss.Sizes.tendsto_size
#check @RBM.StochDomAt.of_subset
#check @RBM.StochDomAt.precomp_param
#check @RBM.StochDomAt.of_le_left
#check @RBM.StochDomAt.of_subset_union
#check @RBM.StochDomAt.add
#check @RBM.StochDomAt.of_forall_le
-- spectral data, propagator, parameters
#check @RBM.Green.v3_premises_of_stFlow
#check @RBM.abs_lemE_le
#check @RBM.lemT_lt_one
#check @RBM.mE_im
#check @RBM.mE_im_pos
#check @RBM.norm_mE
#check @RBM.Theta
#check @RBM.prop5Decay_holds
#check @RBM.ellT
#check @RBM.one_le_ellT
#check @RBM.Bparam
#check @RBM.Gauss.meas_gt_le_of_moment
-- instance data and the downstream instance (S5-01 `Step5Inst`)
#check @RBM.Gauss.Step5Inst.szCL
#check @RBM.Gauss.Step5Inst.szCL_admissible
#check @RBM.Gauss.Step5Inst.sCL
#check @RBM.Gauss.Step5Inst.tCL
#check @RBM.Gauss.Step5Inst.zCL
#check @RBM.Gauss.Step5Inst.flow_zCL
#check @RBM.Gauss.Step5Inst.lemT_zCL
#check @RBM.Gauss.Step5Inst.szCL_hst
#check @RBM.Gauss.Step5Inst.szCL_reg5I
#check @RBM.Gauss.Step5Inst.szCL_ellT_s
#check @RBM.Gauss.Step5Inst.szCL_con
#check @RBM.Gauss.Step5Inst.xCL
#check @RBM.Gauss.Step5Inst.zdistInf_xCL
#check @RBM.Gauss.Step5Inst.szCL_cltFar_index_nonempty
#check @RBM.Gauss.Step5Inst.InstIng5Concl
#check @RBM.Gauss.Step5Inst.inst_ing5
#check @RBM.Gauss.Step5Inst.inst_cltFar
#check @RBM.Gauss.Step5Inst.inst_cltIso

/-! ## 2. Pinned intermediate statements (T2182 targets 1-3; defined in `RBM.Gauss.Sizes` verbatim) -/

noncomputable section

namespace RBM.Gauss.Sizes.T2182Check

open MeasureTheory Filter
open RBM RBM.Gauss RBM.Gauss.Sizes RBM.Evol

/-- Target 1: the per-label tail `CltMom2.DomHyp` (`(eq:propcalB)`, first half, `3_5:2155`) from `(Eq:Gdecay_w)` at
`u = s`, with `Λ' = N^τ`, `q₁ = N^{-D₁}`, eventually, every `σ`. -/
def CltFar.DomStmt (d : ℕ) : Prop :=
  3 ≤ d → ∀ (sz : Sizes d) (𝔠 𝔡 Cd : ℝ) (E s t : ℕ → ℝ), sz.Admissible 𝔠 𝔡 →
    (∀ n, s n < 1) → (∀ n, s n ≤ t n) → STReg5I sz s t → STGdecayW sz E s t Cd →
    ∀ τ D₁ : ℝ, 0 < τ → 0 < D₁ → ∀ᶠ n in atTop, ∀ σ : Fin 2 → Bool,
      CltMom2.DomHyp sz n (E n) (s n) σ (((sz.size n : ℕ) : ℝ) ^ τ) (((sz.size n : ℕ) : ℝ) ^ (-D₁))

/-- Target 2: the off-window part (`(eq:propcalB)`, second half, `3_5:2155`; the `O(W^{-D})` of `(eq:2p_product)`):
`‖CltMom2.off‖ ≤ W^{-D}` for every `σ, a` at once, off an event of probability `≤ N^{-D'}`, eventually. -/
def CltFar.OffStmt (d : ℕ) : Prop :=
  3 ≤ d → ∀ (sz : Sizes d) (κ 𝔠 𝔡 Cd : ℝ) (E s t : ℕ → ℝ), 0 < κ → sz.Admissible 𝔠 𝔡 →
    (∀ n, |E n| ≤ 2 - κ) → (∀ n, 0 ≤ s n) → (∀ n, s n < t n) → (∀ n, t n < 1) → STReg5I sz s t →
    STGdecayW sz E s t Cd →
    ∀ D D' : ℝ, 0 < D → 0 < D' → ∀ᶠ n in atTop,
      sz.seqP {ω | ∃ (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)),
          ((sz.W n : ℕ) : ℝ) ^ (-D) < ‖CltMom2.off sz n (E n) (s n) (t n) σ a ω‖} ≤
        ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-D'))

/-- Target 3: the window fluctuation `c_n · fluc` (`(eq:main_challenge3)`, `3_5:2213-2249`) at one index `(σ, a)`:
`P(N^τ A^{-6/5}/(|a₁-a₂|^{d-2}+1) < ‖c_n fluc‖) ≤ N^{-D}`, eventually, uniformly in `σ₀ ≠ σ₁` and `a`. -/
def CltFar.FlucStmt (d : ℕ) : Prop :=
  3 ≤ d → ∀ (sz : Sizes d) (κ 𝔠 𝔡 Cd : ℝ) (E s t : ℕ → ℝ), 0 < κ → sz.Admissible 𝔠 𝔡 →
    (∀ n, |E n| ≤ 2 - κ) → (∀ n, 0 ≤ s n) → (∀ n, s n < t n) → (∀ n, t n < 1) → STReg5I sz s t →
    STGdecayW sz E s t Cd → STCltIsoConcl sz E s t →
    ∀ τ D : ℝ, 0 < τ → 0 < D → ∀ᶠ n in atTop, ∀ σ : Fin 2 → Bool, σ 0 ≠ σ 1 →
      ∀ a : Fin 2 → Zd d (sz.L n),
        sz.seqP {ω | ((sz.size n : ℕ) : ℝ) ^ τ * (STAI sz n ^ (-(6 / 5 : ℝ)) /
              (((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) ^ (d - 2) + 1)) <
            ‖(((1 - s n) ^ 2 / (sz.lam n ^ 4 * (sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d) ^ (6 / 5 : ℝ)) : ℝ) : ℂ) *
              CltMom2.fluc sz n (E n) (s n) (t n) σ a ω‖} ≤
          ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-D))

end RBM.Gauss.Sizes.T2182Check

end
