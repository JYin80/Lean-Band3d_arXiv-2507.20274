/-
T2250 check file (S3-15a, `RBM3D/Induction/QDriftA.lean`; dispatcher V1, Tue Oct  6 03:21 UTC 2026).
Pin texts only: imports of merged modules, `#check` of merged names, vocabulary `def`s (copied verbatim
into `QDriftA.lean`, script diff) and the `Prop` texts `T2250_*` (each proved in `QDriftA.lean` with exactly
that statement, as a theorem named without the `T2250_` prefix).  No proofs, no `sorry`, no `by`.
Compiles on `main` (e362f4b): every import below is merged.
-/
import RBM3D.Induction.QGridA
import RBM3D.Induction.QProxy
import RBM3D.Induction.NQGood2
import RBM3D.Induction.ZeroModeCalc

set_option linter.unusedVariables false

noncomputable section

namespace RBM.Ind

open MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.Loop RBM.Gauss RBM.Gauss.Sizes RBM.Path
open scoped NNReal ENNReal

/-! ## 1. Merged names used (full namespaces) -/

-- `Induction/QGridA.lean` (549a62d), namespace `RBM.Ind`
#check @RBM.Ind.aTrueQN            -- :1263
#check @RBM.Ind.dGridQN            -- :1274
#check @RBM.Ind.gridDriftQN        -- :2114
#check @RBM.Ind.stoppedDuhamelQN   -- :2168
-- `Induction/GridDuhamelN.lean` (2ebee73), namespace `RBM.Ind`
#check @RBM.Ind.Ugen               -- :65
#check @RBM.Ind.AvecN              -- :272
-- `Induction/GridAssemblyN.lean`, namespace `RBM.Ind`
#check @RBM.Ind.GridAssemblyHypN   -- :183
-- `Induction/NQGood1.lean` (691566a), `Induction/NQGood2.lean`, namespace `RBM.Ind`
#check @RBM.Ind.hker_of_case1N     -- NQGood1 :310 (pattern of target 5a)
#check @RBM.Ind.nonAltClsN         -- NQGood2 :79  (pattern of `altClsQN`)
#check @RBM.Ind.kappaNonAltN       -- NQGood2 :86
#check @RBM.Ind.epsNonAltN         -- NQGood2 :91
#check @RBM.Ind.nonAlt_hkerN       -- NQGood2 :252 (pattern of target 5b)
#check @RBM.Ind.goodSetN_A0clsN    -- NQGood2 :284 (pattern of target 6)
#check @RBM.Ind.nonAlt_hA0clsN     -- NQGood2 :303
-- `Induction/QProxy.lean` (9a207a1), namespace `RBM.Ind`
#check @RBM.Ind.qProxy4C           -- :444 (the EK-4 constant, shared with S3-14)
#check @RBM.Ind.qProxy4C_pos       -- :465
#check @RBM.Ind.qqTensorN_sumZero  -- :289
-- `Induction/ZeroModeCalc.lean` (d1cb5a6), namespace `RBM.Ind`
#check @RBM.Ind.Ugen_eq_UN_EKsgn   -- :445
-- `Induction/QopAlgebra.lean` (6b2494e), namespace `RBM.Gauss.Sizes`
#check @RBM.Gauss.Sizes.QopAlgebra_mollifier_props          -- :511
#check @RBM.Gauss.Sizes.QopAlgebra_mollifier_differentiableAt -- :581
#check @RBM.Gauss.Sizes.QopAlgebra_Psum_Qop                 -- :601
#check @RBM.Gauss.Sizes.QopAlgebra_Qop_of_sumZero           -- :617
#check @RBM.Gauss.Sizes.QopAlgebra_Psum_deriv               -- :629
#check @RBM.Gauss.Sizes.QopAlgebra_ThetaN_sumZero           -- :786
#check @RBM.Gauss.Sizes.QopAlgebra_commutator_ThetaN        -- :871
-- `Induction/QopNorm.lean` (eb6d67a), namespace `RBM.Gauss.Sizes`
#check @RBM.Gauss.Sizes.stQopNorm_holds       -- :261
#check @RBM.Gauss.Sizes.stQop_sub_fastDecay   -- :378
-- `Induction/Step34Pins.lean` (fc76526), namespace `RBM.Gauss.Sizes`
#check @RBM.Gauss.Sizes.STPsum            -- :87
#check @RBM.Gauss.Sizes.STQop             -- :92
#check @RBM.Gauss.Sizes.STMollifierProps  -- :510
#check @RBM.Gauss.Sizes.STAlternating     -- :543
#check @RBM.Gauss.Sizes.STWardTypeP       -- :549
#check @RBM.Gauss.Sizes.STB45             -- :560
-- `Induction/GridGoodN.lean` (2f246bf), namespace `RBM.Gauss.Sizes`
#check @RBM.Gauss.Sizes.GoodSetN          -- :124
-- `Induction/DecayLoopA.lean` (6179d8c), namespace `RBM.Gauss.Sizes`
#check @RBM.Gauss.Sizes.STdiamInf         -- :71
-- `Induction/Step2Defs.lean` (86124dc), namespace `RBM.Gauss.Sizes`
#check @RBM.Gauss.Sizes.STLKM             -- :68
#check @RBM.Gauss.Sizes.STksimLKM         -- :723
#check @RBM.Gauss.Sizes.STelklkM          -- :737
#check @RBM.Gauss.Sizes.STegtM            -- :750
-- `Evolution/Pins.lean`, `Evolution/SumDecayZero.lean` (d9de66f), namespace `RBM`
#check @RBM.EKsgn                -- Pins :45
#check @RBM.EKFastDecay          -- Pins :51
#check @RBM.EKSumZero            -- Pins :56
#check @RBM.EKSumDecay2          -- Pins :110
#check @RBM.ekSumDecay2_holds    -- SumDecayZero :1411
-- `Kernel/Evolution.lean` (ff8d36d), `Defs/Semicircle.lean` (fbc9870), namespace `RBM`
#check @RBM.ThetaN               -- :60
#check @RBM.UN                   -- :65
#check @RBM.mSigma               -- Semicircle :85
#check @RBM.norm_mSigma          -- Semicircle :87
#check @RBM.norm_mE              -- Semicircle :63

/-! ## 2. Vocabulary (copied verbatim into `QDriftA.lean`) -/

/-- `ℬ₄ = [𝒬_u, Θ^{(m+1)}_{u,σ}](𝓛-𝒦)_{u,σ}(H)` at a fine matrix `H` (`int_K-L+Q`, `3_5:1337-1346`; the
second summand of the merged `dGridQN`, `QGridA.lean:1274`, at a matrix; RBM2D `B4` inside `altB`,
`StoppedEndDefs.lean:88`). -/
def altB4N {d : ℕ} (sz : Sizes d) (n : ℕ) (E u : ℝ) {m : ℕ}
    (ϑ : ℝ → (Fin (m + 1) → Zd d (sz.L n)) → ℂ) (σ : Fin (m + 1) → Bool)
    (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) :
    (Fin (m + 1) → Zd d (sz.L n)) → ℂ :=
  fun a =>
    STQop (d := d) ϑ u
        (ThetaN d (sz.L n) (sz.lam n) (fun i => mSigma E (σ i)) u (fun b => sz.STLKM n E u H σ b)) a -
      ThetaN d (sz.L n) (sz.lam n) (fun i => mSigma E (σ i)) u
        (STQop (d := d) ϑ u (fun b => sz.STLKM n E u H σ b)) a

/-- `ℬ₅ = -[𝒫∘(𝓛-𝒦)_{u,σ}(H)]_{a₁} ∂_uϑ_{u,a}` with the paper's sign inside (`3_5:1345`; the last term of
`dGridQN`). -/
def altB5N {d : ℕ} (sz : Sizes d) (n : ℕ) (E u : ℝ) {m : ℕ}
    (ϑ : ℝ → (Fin (m + 1) → Zd d (sz.L n)) → ℂ) (σ : Fin (m + 1) → Bool)
    (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) :
    (Fin (m + 1) → Zd d (sz.L n)) → ℂ :=
  fun a => -(STPsum (d := d) (fun b => sz.STLKM n E u H σ b) (a 0) * deriv (fun τ => ϑ τ a) u)

/-- **The drift of `int_K-L+Q` at a matrix**: `𝒬_u(ℬ₁ + ℬ₂ + ℬ₃) + ℬ₄ + ℬ₅` (RBM2D `dFlowQ`,
`AltDriftQ.lean:86`; the first summand is the text of `dGridQN` with `H` for `pathH … j ω`). -/
def dFlowQN {d : ℕ} (sz : Sizes d) (n : ℕ) (E u : ℝ) {m : ℕ}
    (ϑ : ℝ → (Fin (m + 1) → Zd d (sz.L n)) → ℂ) (σ : Fin (m + 1) → Bool)
    (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) :
    (Fin (m + 1) → Zd d (sz.L n)) → ℂ :=
  fun a =>
    STQop (d := d) ϑ u
        (fun b => ∑ l ∈ Finset.Icc 3 (m + 1), sz.STksimLKM n E u H l (loopOf σ b) +
            sz.STelklkM n E u H (loopOf σ b) +
            sz.STegtM n E u H (loopOf σ b)) a +
      altB4N sz n E u ϑ σ H a + altB5N sz n E u ϑ σ H a

/-- **The kernel class of the alternating chain** (d ≥ 3 replacement of RBM2D `AltCase4Cls`,
`AltDriftQ.lean:197`; pattern `nonAltClsN`, `NQGood2.lean:79`): `Cls i δ X :⇔` `X` is sum-zero (`EKSumZero`),
`δ ≤ W^{-Dc}`, and `‖X b‖ ≤ δ` when `ℓ_{u_i} W^{τ'} ≤ diam_∞ b`.  No symmetry clause, no alternation. -/
def altClsQN (d L : ℕ) [NeZero L] {k : ℕ} (g W τ' Dc : ℝ) (u : ℕ → ℝ) :
    ℕ → ℝ → ((Fin k → Zd d L) → ℂ) → Prop :=
  fun i δ X => EKSumZero X ∧ δ ≤ W ^ (-Dc) ∧
    ∀ b : Fin k → Zd d L, ellT L g (u i) * W ^ τ' ≤ (STdiamInf b : ℝ) → ‖X b‖ ≤ δ

/-- **The kernel weight `κ_{i,m}` of the alternating chain**: `W^{C₄ε}((g²+|1-u_i|)/(g²+|1-u_m|))^k`,
`C₄ = qProxy4C d k Λg κ' K` (exponent `k`, not `k-1`: `(sum_res_2)`). -/
def kappaAltQN (d k : ℕ) (Λg κ' K g W ε : ℝ) (u : ℕ → ℝ) (i m : ℕ) : ℝ :=
  W ^ (qProxy4C d k Λg κ' K * ε) * ((g ^ 2 + |1 - u i|) / (g ^ 2 + |1 - u m|)) ^ k

/-- **The additive decay-error weight `ε_{i,m}` of the alternating chain**: `W^{C₄}`. -/
def epsAltQN (d k : ℕ) (Λg κ' K W : ℝ) (_i _m : ℕ) : ℝ :=
  W ^ qProxy4C d k Λg κ' K

/-! ## 3. Statements (each proved in `QDriftA.lean` with exactly this statement) -/

/-- Target 2: `dGridQN` along the walk is `dFlowQN` at the grid state (definitional unfolding + `ring`). -/
def T2250_dGridQN_eq_dFlowQN : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (E s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) {m : ℕ}
    (ϑ : ℝ → (Fin (m + 1) → Zd d (sz.L n)) → ℂ) (σ : Fin (m + 1) → Bool) (j : ℕ) (ω : PathΩ sz),
    dGridQN sz E s t K n ϑ σ j ω =
      dFlowQN sz n (E n) (gridTime s t K n j) ϑ σ (pathH sz s t K n j ω)

/-- Target 3: `𝒫ℬ₄ = 𝒫ℬ₅ = 0`, hence `𝒬_uℬ₄ = ℬ₄`, `𝒬_uℬ₅ = ℬ₅`, and the drift is sum-zero in the EK-4
form, for every `σ` (RBM2D `dGridQN_eq_dFlowQ`, `AltDriftQ.lean:119-180`). -/
def T2250_dFlowQN_sumZero : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (n : ℕ) (E u : ℝ) {m : ℕ}
    (ϑ : ℝ → (Fin (m + 1) → Zd d (sz.L n)) → ℂ) (σ : Fin (m + 1) → Bool)
    (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ),
    |E| ≤ 2 → 0 ≤ u → u < 1 →
    (∀ (τ : ℝ) (a₁ : Zd d (sz.L n)),
      ∑ a ∈ Finset.univ.filter (fun a : Fin (m + 1) → Zd d (sz.L n) => a 0 = a₁), ϑ τ a = 1) →
    (∀ a : Fin (m + 1) → Zd d (sz.L n), DifferentiableAt ℝ (fun τ => ϑ τ a) u) →
    (∀ a₁ : Zd d (sz.L n), STPsum (d := d) (altB4N sz n E u ϑ σ H) a₁ = 0) ∧
    (∀ a₁ : Zd d (sz.L n), STPsum (d := d) (altB5N sz n E u ϑ σ H) a₁ = 0) ∧
    STQop (d := d) ϑ u (altB4N sz n E u ϑ σ H) = altB4N sz n E u ϑ σ H ∧
    STQop (d := d) ϑ u (altB5N sz n E u ϑ σ H) = altB5N sz n E u ϑ σ H ∧
    EKSumZero (dFlowQN sz n E u ϑ σ H)

/-- Target 4a: the `𝒬`-process (in particular the initial term `A^Q_0 = 𝒬_{u_0}(𝓛-𝒦)_{u_0}`) is sum-zero
in the EK-4 form. -/
def T2250_aTrueQN_sumZero : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (E s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) {m : ℕ}
    (ϑ : ℝ → (Fin (m + 1) → Zd d (sz.L n)) → ℂ) (σ : Fin (m + 1) → Bool) (j : ℕ) (ω : PathΩ sz),
    (∀ a₁ : Zd d (sz.L n), ∑ a ∈ Finset.univ.filter (fun a : Fin (m + 1) → Zd d (sz.L n) => a 0 = a₁),
      ϑ (gridTime s t K n j) a = 1) →
    EKSumZero (aTrueQN sz E s t K n ϑ σ j ω)

/-- Target 4b: decay survives `𝒬_t` (`𝒬A = A - (A - 𝒬A)`, `stQop_sub_fastDecay`): a `(t, ε', D')`-decaying
tensor with `‖A‖ ≤ W^{C₀}` has `|(𝒬_tA)_a| ≤ 2W^{-D'}` in the window, once `W ≥ W₀(d, m, K, C, c, C₀, ε', D')`. -/
def T2250_Qop_fastDecay : Prop :=
  ∀ (d m : ℕ) (K C c C₀ ε' D' : ℝ), 0 < C → 0 < c → 0 < ε' →
    ∃ W₀ : ℝ, 1 < W₀ ∧ ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ g : ℝ, 0 < g →
      ∀ W : ℝ, W₀ ≤ W → (L : ℝ) ^ d ≤ W ^ K →
      ∀ ϑ : ℝ → (Fin (m + 1) → Zd d L) → ℂ, STMollifierProps (d := d) g C c ϑ →
      ∀ t : ℝ, 0 ≤ t → t < 1 → ∀ A : (Fin (m + 1) → Zd d L) → ℂ, ‖A‖ ≤ W ^ C₀ →
        EKFastDecay g t W ε' D' A →
        ∀ a : Fin (m + 1) → Zd d L, (∃ i j, W ^ ε' * ellT L g t ≤ (zdistD d L (a i - a j) : ℝ)) →
          ‖STQop (d := d) ϑ t A a‖ ≤ 2 * W ^ (-D')

/-- Target 4c: the public form of the private `nqGood1_fast_of_cls` (`NQGood1.lean:278`): the `L^∞` class
of the good set gives the `ℓ¹` window of `EKFastDecay` once `d W^{τ'} ≤ W^ε`. -/
def T2250_fastDecay_of_diamInf : Prop :=
  ∀ {d L k : ℕ}, 0 < d → 1 ≤ (L : ℝ) → ∀ {g s W ε τ' D δ : ℝ},
    (d : ℝ) * W ^ τ' ≤ W ^ ε → δ ≤ W ^ (-D) → ∀ {X : (Fin k → Zd d L) → ℂ},
    (∀ b : Fin k → Zd d L, ellT L g s * W ^ τ' ≤ (STdiamInf b : ℝ) → ‖X b‖ ≤ δ) →
    EKFastDecay g s W ε D X

/-- Target 5a: **`hker` of the alternating chain from EK-4** (`ekSumDecay2_holds`, `(sum_res_2)`), every
`σ`, pattern `hker_of_case1N` (`NQGood1.lean:310`): sum-zero + window decay `≤ δ ≤ W^{-D}` give
`W^{C₄ε} r^k M + W^{C₄} δ`, `C₄ = qProxy4C d k Λg κ' K`. -/
def T2250_hker_altQN : Prop :=
  ∀ {d k : ℕ} (Λg κ' K : ℝ), 3 ≤ d → 2 ≤ k → 0 < Λg → 0 < κ' → 0 < K →
    ∀ {L : ℕ} [NeZero L], 3 ≤ L → ∀ {g : ℝ}, 0 < g → g ≤ Λg →
    ∀ {W ε τ' D : ℝ}, 1 < W → 0 < ε → ε < 1 → 4 ≤ W ^ ε → Real.log L ≤ W ^ ε →
    (L : ℝ) ^ d ≤ W ^ K → (d : ℝ) * W ^ τ' ≤ W ^ ε → 1 < D →
    ∀ {s t : ℝ}, 0 ≤ s → s ≤ t → t ≤ 1 - g ^ 2 / (L : ℝ) ^ 2 → W⁻¹ ≤ (1 - t) / (1 - s) →
    ∀ {E : ℝ}, |E| ≤ 2 → κ' ≤ (mE E).im →
    ∀ (σ : Fin k → Bool) (X : (Fin k → Zd d L) → ℂ) {M δ : ℝ}, 0 ≤ M → 0 ≤ δ → δ ≤ W ^ (-D) →
    (∀ b, ‖X b‖ ≤ M) → EKSumZero X →
    (∀ b : Fin k → Zd d L, ellT L g s * W ^ τ' ≤ (STdiamInf b : ℝ) → ‖X b‖ ≤ δ) →
    ∀ a : Fin k → Zd d L,
      ‖Ugen d L g E σ s t X a‖ ≤
        W ^ (qProxy4C d k Λg κ' K * ε) * ((g ^ 2 + |1 - s|) / (g ^ 2 + |1 - t|)) ^ k * M +
          W ^ qProxy4C d k Λg κ' K * δ

/-- Target 5b: **the field `hker` of `GridAssemblyHypN` for the alternating chain** (pattern `nonAlt_hkerN`,
`NQGood2.lean:252`; RBM2D `altQ_hker`, `AltDriftQ.lean:203`), `Cls = altClsQN`, `κ = kappaAltQN`,
`εK = epsAltQN`; no hypothesis on `σ`. -/
def T2250_alt_hkerQN : Prop :=
  ∀ {d k : ℕ} (Λg κ' K : ℝ), 3 ≤ d → 2 ≤ k → 0 < Λg → 0 < κ' → 0 < K →
    ∀ {L : ℕ} [NeZero L], 3 ≤ L → ∀ {g : ℝ}, 0 < g → g ≤ Λg →
    ∀ {W ε τ' Dc : ℝ}, 1 < W → 0 < ε → ε < 1 → 4 ≤ W ^ ε → Real.log L ≤ W ^ ε →
    (L : ℝ) ^ d ≤ W ^ K → (d : ℝ) * W ^ τ' ≤ W ^ ε → 1 < Dc →
    ∀ {Kg : ℕ} {u : ℕ → ℝ}, (∀ i ≤ Kg, 0 ≤ u i) → (∀ i m, i ≤ m → m ≤ Kg → u i ≤ u m) →
    u Kg ≤ 1 - g ^ 2 / (L : ℝ) ^ 2 → W⁻¹ ≤ (1 - u Kg) / (1 - u 0) →
    ∀ {E : ℝ}, |E| ≤ 2 → κ' ≤ (mE E).im → ∀ σ : Fin k → Bool,
    ∀ i m, i ≤ m → m ≤ Kg → ∀ (X : (Fin k → Zd d L) → ℂ) (M δ : ℝ), 0 ≤ M → 0 ≤ δ →
      (∀ b, ‖X b‖ ≤ M) → altClsQN d L g W τ' Dc u i δ X →
      ∀ a : Fin k → Zd d L,
      ‖Ugen d L g E σ (u i) (u m) X a‖ ≤
        kappaAltQN d k Λg κ' K g W ε u i m * M + epsAltQN d k Λg κ' K W i m * δ

end RBM.Ind

end
