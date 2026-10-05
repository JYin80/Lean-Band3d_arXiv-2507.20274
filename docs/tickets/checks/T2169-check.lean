/-
Release check for T2169 (dispatcher V1, Mon Oct  5 03:24 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §19, §29, §45 O2).
S5-24: CLT moment counting part 2: the decomposition of `f^{far} - 𝔼 f^{far}` into the window fluctuation and the
off-window part, the `2p`-th moment expansion `(eq:2p_product)`, the isolated/paired split (`STCltIsoConcl`, merged
`cltMom1_paired_moment_le`), Markov, and the eventual form.  Section 1: the merged names it builds on (S5-23
`Evolution/CltMoments1`, T2165 daa7cc1; S5-21 `Evolution/CltStep`; S5-22b `Evolution/MeanFar`; S5-01 `Induction/Step5Pins`;
loops, measurability, Markov; the instance data) and the downstream pins.  Section 2: the pinned vocabulary (seven
definitions) and statements (six `Prop`s), in namespace `RBM.Evol.T2169Check` here; T2169 defines them in `RBM.Evol`
verbatim.
Statement and `#check` only: no proofs, no `sorry`.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2169-check.lean`.
-/
import RBM3D

/-! ## 1. Merged names -/

-- S5-23 (`Evolution/CltMoments1`)
#check @RBM.Evol.CltMom1.Paired
#check @RBM.Evol.CltMom1.ball
#check @RBM.Evol.CltMom1.clusterSum
#check @RBM.Evol.cltMom1_paired_sum_le
#check @RBM.Evol.cltMom1_not_paired_iff
#check @RBM.Evol.cltMom1_iso_hyp_iff
#check @RBM.Evol.cltMom1_weight_a1
#check @RBM.Evol.cltMom1_weight_a2
#check @RBM.Evol.cltMom1_comparable_weights
#check @RBM.Evol.cltMom1_scale_comparable
#check @RBM.Evol.cltMom1_scale_bd1
#check @RBM.Evol.CltMom1.G
#check @RBM.Evol.CltMom1.cs
#check @RBM.Evol.CltMom1.Cd
#check @RBM.Evol.CltMom1.uw
#check @RBM.Evol.CltMom1.uw_nonneg
#check @RBM.Evol.cltMom1_clusterSum_le
#check @RBM.Evol.cltMom1_paired_moment_le
#check @RBM.Evol.cltMom1_zdistInf_sub_comm
#check @RBM.Evol.cltMom1_cluster_inst
#check @RBM.Evol.cltMom1_b_paired
-- the CLT objects of case (i), the isolation bound, the mean part (S5-01, S5-21, S5-22b)
#check @RBM.Gauss.Sizes.STfFar
#check @RBM.Gauss.Sizes.STcltB
#check @RBM.Gauss.Sizes.STcltX
#check @RBM.Gauss.Sizes.STCltIsoConcl
#check @RBM.Gauss.Sizes.STCltIso
#check @RBM.Gauss.Sizes.stCltIso_holds
#check @RBM.Gauss.Sizes.STMeanFarConcl
#check @RBM.Gauss.Sizes.stMeanFar
#check @RBM.Gauss.Sizes.STReg5I
#check @RBM.Gauss.Sizes.STIngR5
#check @RBM.Gauss.Sizes.STAI
#check @RBM.Gauss.Sizes.STGdecayW
-- loops, propagator, measurability, Markov
#check @RBM.Gauss.Sizes.STLKM
#check @RBM.Gauss.Sizes.STLM_seqHflow
#check @RBM.Gauss.Sizes.STKloop
#check @RBM.Gauss.Sizes.STmsig
#check @RBM.Gauss.Sizes.Lloop
#check @RBM.Gauss.Sizes.norm_Lloop_le
#check @RBM.Gauss.Sizes.walk_measurable_Lloop
#check @RBM.Gauss.Sizes.seqP
#check @RBM.Gauss.Sizes.isProbabilityMeasure_seqP
#check @RBM.Gauss.Sizes.seqHflow
#check @RBM.Gauss.Sizes.neZeroL
#check @RBM.Gauss.etaT
#check @RBM.Gauss.etaT_pos
#check @RBM.Gauss.meas_gt_le_of_moment
#check @RBM.Theta
#check @RBM.PropSpin
#check @RBM.mE
#check @RBM.mE_im
#check @RBM.norm_mE
#check @RBM.ellT
#check @RBM.one_le_ellT
#check @RBM.Ind.nqGood1_mE_im_ge
#check @RBM.Green.v3_premises_of_stFlow
-- instance data (S5-01 `Step5Inst`)
#check @RBM.Gauss.Step5Inst.szCL
#check @RBM.Gauss.Step5Inst.sCL
#check @RBM.Gauss.Step5Inst.tCL
#check @RBM.Gauss.Step5Inst.zCL
#check @RBM.Gauss.Step5Inst.flow_zCL
#check @RBM.Gauss.Step5Inst.lemT_zCL
#check @RBM.Gauss.Step5Inst.szCL_log_W
#check @RBM.Gauss.Step5Inst.szCL_one_le_log_W
#check @RBM.Gauss.Step5Inst.szCL_ellT_s
#check @RBM.Gauss.Step5Inst.szCL_reg5I
#check @RBM.Gauss.Step5Inst.xCL
#check @RBM.Gauss.Step5Inst.zdistInf_xCL
#check @RBM.Gauss.Step5Inst.InstIng5Concl
#check @RBM.Gauss.Step5Inst.inst_cltIso
-- downstream pins (S5-25)
#check @RBM.Gauss.Sizes.STCltFarConcl
#check @RBM.Gauss.Sizes.STCltFar
#check @RBM.Gauss.Step5Inst.inst_cltFar

/-! ## 2. Pinned vocabulary and statements (T2169 target 1; defined in `RBM.Evol` verbatim) -/

noncomputable section

namespace RBM.Evol.T2169Check

open MeasureTheory Filter
open RBM RBM.Gauss RBM.Gauss.Sizes RBM.Evol

/-- **The weight of a two-label index `β = (β₀, β₁)` in `(eq:2p_product)`** (`3_5:2218`):
`ilambda² Θ_t(a₁, β₀) · ilambda² (Θ_t(β₁, a₂) - Θ_t(β₀, a₂))` on the region `(eq:sumregionsforb)` (`3_5:2220`):
`β₀` far from both `a_i` at `(log W)⁴ ℓ_s` in the orientation of `STfFar`, window `|β₀ - β₁| ≤ (log W)³ ℓ_s`;
`0` elsewhere.  The propagator is that of `STfFar`. -/
def CltMom2.Z {d : ℕ} (sz : Sizes d) (n : ℕ) (E s t : ℝ) (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n))
    (β : Fin 2 → Zd d (sz.L n)) : ℂ :=
  if Real.log ((sz.W n : ℕ) : ℝ) ^ 4 * ellT (sz.L n) (sz.lam n) s <
        ((zdistInf d (sz.L n) (β 0 - a 0) : ℕ) : ℝ) ∧
      Real.log ((sz.W n : ℕ) : ℝ) ^ 4 * ellT (sz.L n) (sz.lam n) s <
        ((zdistInf d (sz.L n) (β 0 - a 1) : ℕ) : ℝ) ∧
      ((zdistInf d (sz.L n) (β 0 - β 1) : ℕ) : ℝ) ≤
        Real.log ((sz.W n : ℕ) : ℝ) ^ 3 * ellT (sz.L n) (sz.lam n) s then
    (((sz.lam n ^ 2 : ℝ) : ℂ) *
        Theta d (sz.L n) (sz.lam n) ((t : ℂ) * (STmsig E (σ 0) * STmsig E (σ 1))) (a 0) (β 0)) *
      (((sz.lam n ^ 2 : ℝ) : ℂ) *
        (Theta d (sz.L n) (sz.lam n) ((t : ℂ) * (STmsig E (σ 0) * STmsig E (σ 1))) (β 1) (a 1) -
          Theta d (sz.L n) (sz.lam n) ((t : ℂ) * (STmsig E (σ 0) * STmsig E (σ 1))) (β 0) (a 1)))
  else 0

/-- **The window fluctuation** `ilambda⁴ (1-s)^{-2} (ilambda² W^d)^{6/5} (𝕀𝔼 f^{far})_{window}` (`3_5:2214-2218`):
`Σ_β Z_β (𝗕_β - 𝔼𝗕_β)`, with the centred factor `STcltX … false` of the pin. -/
def CltMom2.fluc {d : ℕ} (sz : Sizes d) (n : ℕ) (E s t : ℝ) (σ : Fin 2 → Bool)
    (a : Fin 2 → Zd d (sz.L n)) (ω : sz.SeqΩ) : ℂ :=
  ∑ β : Fin 2 → Zd d (sz.L n), CltMom2.Z sz n E s t σ a β * STcltX sz n E s σ β false ω

open Classical in
/-- **The off-window part** of `f^{far} - 𝔼 f^{far}` (the `O(W^{-D})` of `(eq:2p_product)`): the sum of `STfFar` with
`𝓑` replaced by `𝓑 - 𝔼𝓑` over `|b₁ - b₂| > (log W)³ ℓ_s`.  S5-25 bounds it with `(eq:propcalB)` (`3_5:2155`). -/
def CltMom2.off {d : ℕ} (sz : Sizes d) (n : ℕ) (E s t : ℝ) (σ : Fin 2 → Bool)
    (a : Fin 2 → Zd d (sz.L n)) (ω : sz.SeqΩ) : ℂ :=
  (((1 - s) ^ 2 : ℝ) : ℂ) * ∑ b₁ ∈ Finset.univ.filter (fun b₁ : Zd d (sz.L n) =>
      Real.log ((sz.W n : ℕ) : ℝ) ^ 4 * ellT (sz.L n) (sz.lam n) s < ((zdistInf d (sz.L n) (b₁ - a 0) : ℕ) : ℝ) ∧
      Real.log ((sz.W n : ℕ) : ℝ) ^ 4 * ellT (sz.L n) (sz.lam n) s < ((zdistInf d (sz.L n) (b₁ - a 1) : ℕ) : ℝ)),
    ∑ b₂ ∈ Finset.univ.filter (fun b₂ : Zd d (sz.L n) =>
      Real.log ((sz.W n : ℕ) : ℝ) ^ 3 * ellT (sz.L n) (sz.lam n) s < ((zdistInf d (sz.L n) (b₁ - b₂) : ℕ) : ℝ)),
      Theta d (sz.L n) (sz.lam n) ((t : ℂ) * (STmsig E (σ 0) * STmsig E (σ 1))) (a 0) b₁ *
        (STLKM sz n E s (sz.seqHflow n s ω) σ ![b₁, b₂] -
          ∫ ω', STLKM sz n E s (sz.seqHflow n s ω') σ ![b₁, b₂] ∂(sz.seqP)) *
        (Theta d (sz.L n) (sz.lam n) ((t : ℂ) * (STmsig E (σ 0) * STmsig E (σ 1))) b₂ (a 1) -
          Theta d (sz.L n) (sz.lam n) ((t : ℂ) * (STmsig E (σ 0) * STmsig E (σ 1))) b₁ (a 1))

/-- **The deterministic envelope of `𝗕`**: `A^{6/5} (η_s^{-2} + Σ_β |𝒦^{(2)}_{s,σ,β}|)`, `A = ilambda² W^d`
(`|𝓛^{(2)}| ≤ η_s^{-2}`, `norm_Lloop_le`). -/
def CltMom2.BY {d : ℕ} (sz : Sizes d) (n : ℕ) (E s : ℝ) (σ : Fin 2 → Bool) : ℝ :=
  (sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d) ^ (6 / 5 : ℝ) *
    ((etaT E s)⁻¹ ^ 2 + ∑ β : Fin 2 → Zd d (sz.L n), ‖STKloop sz n E s σ β‖)

/-- **The per-label tail of the profile-normalised `𝗕` on the window** at one `n` (the `≺` of `(eq:propcalB)`,
`3_5:2155`, in the form used by `(eq:2p_product_pair)`): `P(Λ' < |𝗕_β| (|β₀-β₁|^{d-2}+1)) ≤ q₁` for every window
label `β`.  S5-25 supplies it from `STGdecayW` at `u = s`. -/
def CltMom2.DomHyp {d : ℕ} (sz : Sizes d) (n : ℕ) (E s : ℝ) (σ : Fin 2 → Bool) (Λ' q₁ : ℝ) : Prop :=
  ∀ β : Fin 2 → Zd d (sz.L n),
    ((zdistInf d (sz.L n) (β 0 - β 1) : ℕ) : ℝ) ≤ Real.log ((sz.W n : ℕ) : ℝ) ^ 3 * ellT (sz.L n) (sz.lam n) s →
    sz.seqP {ω | Λ' < ‖STcltB sz n E s σ β ω‖ * (((zdistInf d (sz.L n) (β 0 - β 1) : ℕ) : ℝ) ^ (d - 2) + 1)} ≤
      ENNReal.ofReal q₁

/-- **The isolation bound at one `n`** (`(eq:bound_isolated)`, `3_5:2245`): the inner clause of `STCltIsoConcl`
(`Step5Pins.lean:417-423`) with `(E n), (s n)` replaced by `E, s` and the error `W^{-D}` by `εf`. -/
def CltMom2.IsoHyp {d : ℕ} (sz : Sizes d) (n : ℕ) (E s : ℝ) (σ : Fin 2 → Bool) (p : ℕ) (εf : ℝ) : Prop :=
  ∀ b : Fin (2 * p) → (Fin 2 → Zd d (sz.L n)),
    (∀ k, ((zdistInf d (sz.L n) ((b k) 0 - (b k) 1) : ℕ) : ℝ) ≤
      Real.log ((sz.W n : ℕ) : ℝ) ^ 3 * ellT (sz.L n) (sz.lam n) s) →
    (∃ i, ∀ j, j ≠ i → 10 * Real.log ((sz.W n : ℕ) : ℝ) ^ 3 * ellT (sz.L n) (sz.lam n) s ≤
      ((zdistInf d (sz.L n) ((b i) 0 - (b j) 0) : ℕ) : ℝ)) →
    ‖∫ ω, ∏ k : Fin (2 * p), STcltX sz n E s σ (b k) (decide (p ≤ k.val)) ω ∂(sz.seqP)‖ ≤ εf

/-- **The right side of the `2p`-th moment bound** (`(eq:main_challenge3)` at one `n`): the paired part
(centring `2^{2p}`, the profile-normalised maximum with tail `(Λ', q₁)` and envelope `BY (w^{d-2}+1)` over at most
`|Fin 2 → Zd d L|` window labels, times the cluster bound of `cltMom1_paired_moment_le` at `Mz = M`) plus the
isolated part `εf (Σ_β |Z_β|)^{2p}`. -/
def CltMom2.rhs {d : ℕ} (sz : Sizes d) (n : ℕ) (E s t : ℝ) (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n))
    (p : ℕ) (M Λ' q₁ εf : ℝ) : ℝ :=
  2 ^ (2 * p) * (Λ' ^ (2 * p) +
      (CltMom2.BY sz n E s σ *
          ((Real.log ((sz.W n : ℕ) : ℝ) ^ 3 * ellT (sz.L n) (sz.lam n) s) ^ (d - 2) + 1)) ^ (2 * p) *
        (Fintype.card (Fin 2 → Zd d (sz.L n)) : ℝ) * q₁) *
    (((2 * p : ℕ) : ℝ) ^ (2 * p) * (2 * CltMom1.cs d) ^ p *
      ((CltMom1.Cd d * M * Real.log ((sz.W n : ℕ) : ℝ) ^ 12) ^ (2 * p) *
        (ellT (sz.L n) (sz.lam n) s ^ 4 /
          (((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) ^ (d - 2) + 1)) ^ (2 * p))) +
  εf * (∑ β : Fin 2 → Zd d (sz.L n), ‖CltMom2.Z sz n E s t σ a β‖) ^ (2 * p)

/-- Target 4a: the envelope of `𝗕`. -/
def CltMom2.BYStmt (d : ℕ) : Prop :=
  ∀ (sz : Sizes d) (n : ℕ) (E s : ℝ) (σ : Fin 2 → Bool), |E| < 2 → s < 1 →
    ∀ (β : Fin 2 → Zd d (sz.L n)) (ω : sz.SeqΩ), ‖STcltB sz n E s σ β ω‖ ≤ CltMom2.BY sz n E s σ

/-- Target 3: the decomposition `f^{far} - 𝔼 f^{far} = (1-s)²/(ilambda⁴ A^{6/5}) · fluc + off`. -/
def CltMom2.DecompStmt (d : ℕ) : Prop :=
  ∀ (sz : Sizes d) (n : ℕ) (E s t : ℝ) (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)),
    |E| < 2 → s < 1 → 0 < sz.lam n → ∀ ω : sz.SeqΩ,
      STfFar sz n E s t σ a ω - ∫ ω', STfFar sz n E s t σ a ω' ∂(sz.seqP) =
        (((1 - s) ^ 2 / (sz.lam n ^ 4 * (sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d) ^ (6 / 5 : ℝ)) : ℝ) : ℂ) *
            CltMom2.fluc sz n E s t σ a ω + CltMom2.off sz n E s t σ a ω

/-- Target 4b: the weights of `(eq:2p_product_pair)` (`(prop:ThfadC)`, `(prop:BD1)`): `|Z_β| (|β₀-β₁|^{d-2}+1)^{-1}`
is at most `u(β₀) G_w(β₀ - β₁)` (`CltMom1.uw` with `λ = w`), with a constant `M = M(d, Λ, κ)`. -/
def CltMom2.WeightStmt (d : ℕ) : Prop :=
  3 ≤ d → ∀ Λ κ : ℝ, 0 < Λ → 0 < κ → ∃ M : ℝ, 0 < M ∧
    ∀ (sz : Sizes d) (n : ℕ) (E s t : ℝ) (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)),
      |E| ≤ 2 → κ ≤ (mE E).im → 0 < sz.lam n → sz.lam n ≤ Λ → 0 ≤ t → t < 1 →
      sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 ≤ 1 - t →
      2 * (d : ℝ) ≤ Real.log ((sz.W n : ℕ) : ℝ) →
      ∀ β : Fin 2 → Zd d (sz.L n),
        ‖CltMom2.Z sz n E s t σ a β‖ * (1 / (((zdistInf d (sz.L n) (β 0 - β 1) : ℕ) : ℝ) ^ (d - 2) + 1)) ≤
          CltMom1.uw (a 0) (a 1) (Real.log ((sz.W n : ℕ) : ℝ) ^ 4 * ellT (sz.L n) (sz.lam n) s)
              (Real.log ((sz.W n : ℕ) : ℝ) ^ 3 * ellT (sz.L n) (sz.lam n) s) M (β 0) *
            CltMom1.G d (sz.L n) (Real.log ((sz.W n : ℕ) : ℝ) ^ 3 * ellT (sz.L n) (sz.lam n) s) (β 0 - β 1)

/-- Target 4c: the hypothesis `hzu` of `cltMom1_paired_moment_le` from the pointwise weight bound, at the cluster
radius `2R = 20 w` (comparability, `40 w ≤ ρ`), with the factor `4^d`. -/
def CltMom2.HzuStmt : Prop :=
  ∀ (d L : ℕ) [NeZero L] (a₁ a₂ : Zd d L) (w ρ M : ℝ) (z : (Fin 2 → Zd d L) → ℝ),
    2 ≤ d → 0 ≤ w → 40 * w ≤ ρ → 0 ≤ M → (∀ β, 0 ≤ z β) →
    (∀ β, z β ≤ CltMom1.uw a₁ a₂ ρ w M (β 0) * CltMom1.G d L w (β 0 - β 1)) →
    ∀ β β' : Fin 2 → Zd d L, 0 < z β → ((zdistInf d L (β 0 - β' 0) : ℕ) : ℝ) ≤ 20 * w →
      z β' ≤ CltMom1.uw a₁ a₂ ρ w (4 ^ d * M) (β 0) * CltMom1.G d L w (β' 0 - β' 1)

/-- Target 5: the `2p`-th moment bound `(eq:main_challenge3)` of the window fluctuation at one `n`, and Markov. -/
def CltMom2.MomentStmt (d : ℕ) : Prop :=
  3 ≤ d → ∀ Λ κ : ℝ, 0 < Λ → 0 < κ → ∃ M : ℝ, 0 < M ∧
    ∀ (sz : Sizes d) (n : ℕ) (E s t : ℝ) (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) (p : ℕ)
      (Λ' q₁ εf : ℝ),
      1 ≤ p → |E| < 2 → κ ≤ (mE E).im → 0 < sz.lam n → sz.lam n ≤ Λ → s < 1 → 0 ≤ t → t < 1 →
      sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 ≤ 1 - t →
      (40 : ℝ) ≤ Real.log ((sz.W n : ℕ) : ℝ) → 2 * (d : ℝ) ≤ Real.log ((sz.W n : ℕ) : ℝ) →
      0 ≤ q₁ → 0 ≤ εf →
      CltMom2.DomHyp sz n E s σ Λ' q₁ → CltMom2.IsoHyp sz n E s σ p εf →
      ∫ ω, ‖CltMom2.fluc sz n E s t σ a ω‖ ^ (2 * p) ∂(sz.seqP) ≤ CltMom2.rhs sz n E s t σ a p M Λ' q₁ εf ∧
      ∀ θ : ℝ, 0 < θ → sz.seqP {ω | θ < ‖CltMom2.fluc sz n E s t σ a ω‖} ≤
        ENNReal.ofReal (CltMom2.rhs sz n E s t σ a p M Λ' q₁ εf / θ ^ (2 * p))

/-- Target 6: the eventual form from `STCltIsoConcl` (`εf = W^{-D}`), for `σ₁ ≠ σ₂`; the input of S5-25. -/
def CltMom2.TailStmt (d : ℕ) : Prop :=
  3 ≤ d → ∀ Λ κ : ℝ, 0 < Λ → 0 < κ → ∃ M : ℝ, 0 < M ∧
    ∀ (sz : Sizes d) (E s t : ℕ → ℝ), STCltIsoConcl sz E s t →
      ∀ p : ℕ, 1 ≤ p → ∀ D : ℝ, 0 < D → ∀ᶠ n in atTop,
        ∀ σ : Fin 2 → Bool, σ 0 ≠ σ 1 → ∀ (a : Fin 2 → Zd d (sz.L n)) (Λ' q₁ θ : ℝ),
          |E n| < 2 → κ ≤ (mE (E n)).im → 0 < sz.lam n → sz.lam n ≤ Λ → s n < 1 → 0 ≤ t n → t n < 1 →
          sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 ≤ 1 - t n →
          (40 : ℝ) ≤ Real.log ((sz.W n : ℕ) : ℝ) → 2 * (d : ℝ) ≤ Real.log ((sz.W n : ℕ) : ℝ) →
          0 ≤ q₁ → CltMom2.DomHyp sz n (E n) (s n) σ Λ' q₁ → 0 < θ →
          sz.seqP {ω | θ < ‖CltMom2.fluc sz n (E n) (s n) (t n) σ a ω‖} ≤
            ENNReal.ofReal (CltMom2.rhs sz n (E n) (s n) (t n) σ a p M Λ' q₁ (((sz.W n : ℕ) : ℝ) ^ (-D)) /
              θ ^ (2 * p))

end RBM.Evol.T2169Check

end
