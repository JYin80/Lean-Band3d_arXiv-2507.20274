/-
Release check for T2185 (dispatcher V1, Mon Oct  5 06:49 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §20, §24, §29, §45 O2, §53).
LW-11b: `claim:xi` (`7_8:884-890`, no proof in the paper, D101), the variables `ξ` of `(eq:xia1a2)` (`7_8:882`) and the
bridge `(eq:Gbyxi)` (`7_8:880`) from `lem_GbEXP`: the random layer of `GtoAG` whose deterministic part is LW-11a (T2170,
`Graph/AuxGraph`).  Section 1: the merged names it builds on (LW-11a, LW-P `Graph/LWPins`, LW-15 `Graph/LWPsi`, the ST pins
of `Induction/Defs`, `lem_GbEXP` proved in `Green/GbEXP`, loops, Ward's identity, `≺` calculus, ball count, instance data).
Section 2: the pinned vocabulary (two definitions) and the four pinned statements, in namespace `RBM.Graph.T2185Check`
here; T2185 defines them in `RBM.Graph` verbatim and proves them (`lwXiClaim_holds`, `lwGbyXi_holds`, `lwEntryPsi_holds`,
`lwXiRad_holds`).
Statement and `#check` only: no proofs, no `sorry`.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2185-check.lean`.
-/
import RBM3D

/-! ## 1. Merged names -/

-- LW-11a (`Graph/AuxGraph`, T2170): the deterministic `GtoAG` whose premise `hξ` this ticket discharges
#check @RBM.Graph.LGraph.AuxIMol
#check @RBM.Graph.LGraph.auxLab
#check @RBM.Graph.LGraph.auxVal
#check @RBM.Graph.LGraph.auxOrd
#check @RBM.Graph.LGraph.auxVal_nonneg
#check @RBM.Graph.LWGtoAG
#check @RBM.Graph.lwGtoAG_holds
#check @RBM.Graph.LWScalemole
#check @RBM.Graph.lwScalemole_holds
#check @RBM.Graph.LWAuxNested
#check @RBM.Graph.lwAuxNested_holds
-- LW-04 / LW-09 (`Graph/LWStein`, `Graph/LWSizeClaim`): the sample data of the graphs, block distance, tail
#check @RBM.Graph.lwGm
#check @RBM.Graph.lwSampleData
#check @RBM.Graph.lwBdist
#check @RBM.Graph.lwTail_log32
#check @RBM.Graph.figAux
#check @RBM.Graph.figAux_nested
-- LW-P (`Graph/LWPins`): the premise `LWXi` and its consumers
#check @RBM.Gauss.Sizes.LWInit
#check @RBM.Gauss.Sizes.LWLoop2
#check @RBM.Gauss.Sizes.LWAssm
#check @RBM.Gauss.Sizes.LWXi
#check @RBM.Gauss.Sizes.LWAnpKey
#check @RBM.Gauss.Sizes.LWAnpKeyGh
#check @RBM.Gauss.Sizes.LWAnp
#check @RBM.Gauss.Sizes.LWMoment
#check @RBM.Gauss.Sizes.LWtermEXP
#check @RBM.Gauss.Sizes.LWAvgLaw
-- LW-15 (`Graph/LWPsi`): the class `Ψ_t(·)` and `(eq:Psi)`
#check @RBM.Gauss.Sizes.LWWindow
#check @RBM.Gauss.Sizes.LWClass
#check @RBM.Gauss.Sizes.LWPsiRel
#check @RBM.Gauss.Sizes.LWPsiAll
#check @RBM.Gauss.Sizes.LWWindow_max_Bctl
-- ST pins (`Induction/Defs`) and `lem_GbEXP` (`Green/GbEXP`, S1-30, proved)
#check @RBM.Gauss.Sizes.STFlow
#check @RBM.Gauss.Sizes.STflowE
#check @RBM.Gauss.Sizes.STGM
#check @RBM.Gauss.Sizes.STblk
#check @RBM.Gauss.Sizes.STmaxLoop2
#check @RBM.Gauss.Sizes.STgexRHS
#check @RBM.Gauss.Sizes.STindMax
#check @RBM.Gauss.Sizes.STGiiGEX
#check @RBM.Gauss.Sizes.STGijGEX
#check @RBM.Gauss.Sizes.STGbEXPii
#check @RBM.Gauss.Sizes.STGbEXPij
#check @RBM.Gauss.Sizes.STGbEXP
#check @RBM.Gauss.Sizes.STLmax
#check @RBM.Gauss.Sizes.STLocalEntry
#check @RBM.Green.gbEXPV3
#check @RBM.Green.stGbEXP_holds
-- resolvents, loops, Ward's identity (`Loop/GLoopFlow`, `Loop/GLoop`, `Induction/ConArgDet`)
#check @RBM.Gauss.Gres
#check @RBM.Gauss.Sizes.Gt
#check @RBM.Gauss.Sizes.Lloop
#check @RBM.Gauss.loopFine
#check @RBM.Gauss.blockMat
#check @RBM.Gauss.loopL
#check @RBM.Gauss.Eblk
#check @RBM.Gauss.etaT
#check @RBM.Gauss.etaT_pos
#check @RBM.sum_gloop_two_ward
#check @RBM.sum_gloop_ward_last_div
-- semicircle, flow data
#check @RBM.mE
#check @RBM.norm_mE
#check @RBM.zt
#check @RBM.lemE
#check @RBM.lemT
#check @RBM.lemT_lt_one
#check @RBM.abs_lemE_lt_two
-- sizes, lattice, blocks
#check @RBM.Zd
#check @RBM.zdistD
#check @RBM.Gauss.Idx
#check @RBM.Gauss.split
#check @RBM.Gauss.zdistInf
#check @RBM.Gauss.zdistInf_le_zdistD
#check @RBM.Gauss.Sizes.SizeTendsto
#check @RBM.Gauss.Sizes.Bandwidth
#check @RBM.Gauss.Sizes.Admissible
#check @RBM.Gauss.Sizes.locDomain
#check @RBM.Gauss.Sizes.Bctl
#check @RBM.Gauss.Sizes.W_rpow_le
#check @RBM.Gauss.Sizes.size_rpow_le_W_rpow
#check @RBM.Ind.DecayLoopB_card_ball
-- the `≺` calculus at scale `N` (`Defs/StochDomAt`, `Induction/PerTimeCalc`, `Induction/Step1Setup`)
#check @RBM.badSetAt
#check @RBM.StochDomAt
#check @RBM.Gauss.HighProbAt
#check @RBM.Gauss.HighProbAt.inter
#check @RBM.Gauss.Sizes.Prec
#check @RBM.Gauss.Sizes.Prec.whp
#check @RBM.Gauss.Sizes.prec_of_le
#check @RBM.Gauss.Sizes.tendsto_size
#check @RBM.StochDomAt.of_subset
#check @RBM.StochDomAt.precomp_param
#check @RBM.StochDomAt.of_le_left
#check @RBM.StochDomAt.trans
#check @RBM.StochDomAt.add
#check @RBM.StochDomAt.mul
#check @RBM.Ind.PerTimeCalc.Unif.stochDom_of_indicator
#check @RBM.Ind.s1_indMax_eq_one
-- instance data (`Defs/Sizes`, `Induction/Defs`, `Graph/LWPins` section 8)
#check @RBM.Gauss.SizesInst.sz0
#check @RBM.Gauss.SizesInst.sz0_tendsto
#check @RBM.Gauss.InductionDefsInst.z0
#check @RBM.Gauss.InductionDefsInst.flow_z0
#check @RBM.Gauss.InductionDefsInst.tInst
#check @RBM.Gauss.LWInst.Φ0
#check @RBM.Gauss.LWInst.psiAll0
#check @RBM.Gauss.LWInst.tInst_range
#check @RBM.Gauss.LWInst.inst_Anp

/-! ## 2. Pinned vocabulary and statements (T2185 targets 1, 3-6; defined in `RBM.Graph` verbatim) -/

noncomputable section

namespace RBM.Graph.T2185Check

open RBM RBM.Gauss RBM.Gauss.Sizes RBM.Graph Filter

/-- **`[ξ([a₁],[a₂])]²` of `(eq:xia1a2)`** (`7_8:882`) at the block radius `ρ n` (the paper: `(log W)^{1+2ε₁}`):
the `(+,-)` and `(-,+)` two-loops `𝓛^{(2)}_{t,σ,(b₁,b₂)}` over the `‖·‖_∞`-ball pairs `|b₁ - a₁|, |b₂ - a₂| ≤ ρ`
(summed over the two charges; the paper takes the maximum, at most a factor 2), plus `W^{-d} 1(|a₁ - a₂| ≤ ρ)`.  The
charge set and the summand are those of the merged `STgexRHS` (the right side of `(GijGEX)`). -/
def lwXiSq {d : ℕ} (sz : Sizes d) (E t ρ : ℕ → ℝ) (n : ℕ) (a₁ a₂ : Zd d (sz.L n)) (ω : sz.SeqΩ) : ℝ :=
  (∑ b₁ ∈ Finset.univ.filter (fun b : Zd d (sz.L n) => (zdistInf d (sz.L n) (b - a₁) : ℝ) ≤ ρ n),
    ∑ b₂ ∈ Finset.univ.filter (fun b : Zd d (sz.L n) => (zdistInf d (sz.L n) (b - a₂) : ℝ) ≤ ρ n),
      ∑ σ ∈ ({![true, false], ![false, true]} : Finset (Fin 2 → Bool)),
        ‖Lloop sz n (E n) (t n) σ ![b₁, b₂] ω‖) +
    (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (if (zdistInf d (sz.L n) (a₁ - a₂) : ℝ) ≤ ρ n then 1 else 0)

/-- **The edge variables `ξ([a₁],[a₂])`** of `(eq:xia1a2)`: the square root of `lwXiSq`; the shape of the `ξ` of the merged
`LWXi`, `LWAnp`. -/
def lwXiVar {d : ℕ} (sz : Sizes d) (E t ρ : ℕ → ℝ) (n : ℕ) (a₁ a₂ : Zd d (sz.L n)) (ω : sz.SeqΩ) : ℝ :=
  Real.sqrt (lwXiSq sz E t ρ n a₁ a₂ ω)

/-- **Target 3, `claim:xi`** (`7_8:884-890`, `(eq:Gbyxi2)`): under `(LW_assm)` for a class `Φ` with `(eq:Psi)`, and
`‖G_t - M‖_max ≺ W^{-ε₁}`, the variables `lwXiVar` at a radius `ρ = N^{o(1)}` satisfy the merged `LWXi`: symmetric,
non-negative, `ξ([a₁],[a₂]) ≺ Ψ_t(|a₁ - a₂|)` and `Σ_{a₂} ξ([a₁],[a₂])² ≺ (W^d η_t)⁻¹` (Ward's identity). -/
def LWXiClaim (d : ℕ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z →
      ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ lemT (z n)) →
        ∀ (ε₀ C₁ C₂ C₃ : ℝ) (Cc : ℝ → ℝ) (Φ : ℕ → ℝ → ℝ), LWPsiAll sz ε₀ C₁ C₂ C₃ Cc Φ →
          LWLoop2 sz (STflowE z) t Φ →
          ∀ ε₁ : ℝ, 0 < ε₁ →
          Prec sz (U := fun n => Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n))
            (fun n p ω => ‖STGM sz n (STflowE z n) (t n) ω p.1 p.2‖)
            (fun n _ _ => ((sz.W n : ℕ) : ℝ) ^ (-ε₁)) →
          ∀ ρ : ℕ → ℝ, (∀ n, 0 ≤ ρ n) →
            (∀ τ : ℝ, 0 < τ → ∀ᶠ n in atTop, ρ n + 1 ≤ ((sz.size n : ℕ) : ℝ) ^ τ) →
            LWXi sz (STflowE z) t Φ (lwXiVar sz (STflowE z) t ρ)

/-- **Target 4, `(eq:Gbyxi)` off the diagonal** (`7_8:878-880`, from `(GijGEX)`): uniformly in `x ≠ y` and in the blocks
`a`, `b` at `zdistD`-distance `≤ R` from `[x]`, `[y]` (the premise `hξ` of the merged `LWGtoAG`), `|G_{xy}| ≺ ξ(a, b)`
whenever `2R + 1 ≤ ρ`. -/
def LWGbyXi (d : ℕ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z →
      ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ lemT (z n)) →
        ∀ ε₁ : ℝ, 0 < ε₁ →
        Prec sz (U := fun n => Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n))
          (fun n p ω => ‖STGM sz n (STflowE z n) (t n) ω p.1 p.2‖)
          (fun n _ _ => ((sz.W n : ℕ) : ℝ) ^ (-ε₁)) →
        ∀ ρ R : ℕ → ℝ, (∀ n, 0 ≤ R n) → (∀ n, 2 * R n + 1 ≤ ρ n) →
          Prec sz (U := fun n => {q : (Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n)) ×
              (Zd d (sz.L n) × Zd d (sz.L n)) // q.1.1 ≠ q.1.2 ∧
              (zdistD d (sz.L n) ((split d (sz.L n) (sz.W n) q.1.1).1 - q.2.1) : ℝ) ≤ R n ∧
              (zdistD d (sz.L n) ((split d (sz.L n) (sz.W n) q.1.2).1 - q.2.2) : ℝ) ≤ R n})
            (fun n q ω => ‖Gt sz n (STflowE z n) (t n) true ω q.1.1.1 q.1.1.2‖)
            (fun n q ω => lwXiVar sz (STflowE z) t ρ n q.1.2.1 q.1.2.2 ω)

/-- **Target 5, `(eq:Gbyxi)` entrywise: `|(G - M)_{xy}| ≺ Ψ_t(0)`** (`7_8:880`, the `Ψ_t(0) δ_{xy}` term, from `(GiiGEX)`
and `(LW_assm)`): the premises `|G_{xy}| ≤ Ψ`, `|G_{xx} - m| ≤ Ψ` of the merged `LWGtoAG` at `Ψ = Φ n 0`. -/
def LWEntryPsi (d : ℕ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z →
      ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ lemT (z n)) →
        ∀ (ε₀ C₁ C₂ C₃ : ℝ) (Cc : ℝ → ℝ) (Φ : ℕ → ℝ → ℝ), LWPsiAll sz ε₀ C₁ C₂ C₃ Cc Φ →
          LWLoop2 sz (STflowE z) t Φ →
          ∀ ε₁ : ℝ, 0 < ε₁ →
          Prec sz (U := fun n => Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n))
            (fun n p ω => ‖STGM sz n (STflowE z n) (t n) ω p.1 p.2‖)
            (fun n _ _ => ((sz.W n : ℕ) : ℝ) ^ (-ε₁)) →
          Prec sz (U := fun n => Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n))
            (fun n p ω => ‖STGM sz n (STflowE z n) (t n) ω p.1 p.2‖)
            (fun n _ _ => Φ n 0)

/-- **Target 6, polylogarithmic radii are `N^{o(1)}`**: the radius premise of target 3 for `ρ = C (log W)^K + C'`. -/
def LWXiRad : Prop :=
  ∀ {d : ℕ} (sz : Sizes d), sz.SizeTendsto → ∀ C C' K : ℝ, 0 ≤ C → 0 ≤ C' → 0 ≤ K →
    ∀ τ : ℝ, 0 < τ → ∀ᶠ n in atTop,
      C * Real.log ((sz.W n : ℕ) : ℝ) ^ K + C' + 1 ≤ ((sz.size n : ℕ) : ℝ) ^ τ

end RBM.Graph.T2185Check

end
