/-
Release check for T2228 (dispatcher V1, Mon Oct  5 2026; CLAUDE.md §4 step 0; DECISIONS §16, §17, §20, §29,
§45 O2, §64 (4), §67, §68, §71).
S6-07 (stochastic layer ST-5, Step 6): proves the merged pins `STExpDriftLo` (`(eq:Exp(L-K)2)`, `(eq:ExpLWn=2_smalleta)`,
`6:63-79`; `RBM3D/Induction/Step6Pins.lean:323`, unchanged) and `STExpDriftDecay` (`(deccA0)` for `D_u`, `3_5:1634`;
`Step6Pins.lean:335`, unchanged) in the new file `RBM3D/Induction/ExpEtermsB.lean`; deletes their owed registry lines
(`RBM3D/Test/Axioms.lean:230-231` on f2766db).
Section 1: the merged names the proof uses (exact namespaces, from the enclosing `namespace … end` blocks; file and
last commit on `main` f2766db).
Section 2: two vocabulary `noncomputable def`s and the statements of the public theorems of `ExpEtermsB.lean` as
closed `Prop`s, in the temporary namespace `RBM.Gauss.Sizes.T2228Check` (T2228 defines / proves each, same name, in
`RBM.Gauss.Sizes`; `{d : ℕ}` first).
Section 3: the statements of the instances T2228 compiles (`RBM.Gauss.Step6Inst`; the merged Step-6 instance data), as
`Prop`-valued `example`s (no proof obligation).
Statement and `#check` only: no theorem, no proof, no `sorry`.  Never imported or merged.
Imports: merged modules only, not `RBM3D`.  No Mathlib lemma is `#check`ed.
Run from the main worktree: `lake env lean docs/tickets/checks/T2228-check.lean`.
-/
import RBM3D.Induction.ExpEtermsA
import RBM3D.Induction.ExpAvg
import RBM3D.Induction.ExpIniI
import RBM3D.Induction.DecayLoopB
import RBM3D.Induction.Step2Iterate
import RBM3D.Induction.KDecay
import RBM3D.Loop.KLFinal
import RBM3D.Path.Walk

set_option linter.style.longLine false

/-! ## 1. Merged names -/

-- `RBM3D/Induction/Step6Pins.lean` (cda3bb2; S6-01 = T2204): the two pins, their conclusions, the drift, the shapes
#check @RBM.Gauss.Sizes.STExpDriftLo
#check @RBM.Gauss.Sizes.STExpDriftLoConcl
#check @RBM.Gauss.Sizes.STExpDriftDecay
#check @RBM.Gauss.Sizes.STExpDriftDecayConcl
#check @RBM.Gauss.Sizes.STExpDrift
#check @RBM.Gauss.Sizes.STExpELKLK
#check @RBM.Gauss.Sizes.STExpEGt
#check @RBM.Gauss.Sizes.STExpAvgU
#check @RBM.Gauss.Sizes.STIngR6
#check @RBM.Gauss.Sizes.STStep6Concl
#check @RBM.Gauss.Sizes.STStep6I
#check @RBM.Gauss.Sizes.STStep6IV
#check @RBM.Gauss.Sizes.STImproveExpAver
#check @RBM.Gauss.Sizes.STExpDuhamelZ
#check @RBM.Gauss.Sizes.STExpDuhamelQ
#check @RBM.Gauss.Sizes.STExpWardI
#check @RBM.Gauss.Sizes.STExpIntIV
#check @RBM.Gauss.Sizes.STExpIntI
#check @RBM.Gauss.Step6Inst.InstIng6Concl
#check @RBM.Gauss.Step6Inst.inst_ing6_I
#check @RBM.Gauss.Step6Inst.inst_ing6_IV
#check @RBM.Gauss.Step6Inst.inst_step6I
#check @RBM.Gauss.Step6Inst.inst_step6IV
#check @RBM.Gauss.Step6Inst.inst_expDriftLo
#check @RBM.Gauss.Step6Inst.inst_expDriftDecay
-- `RBM3D/Induction/Step6Kit.lean` (9e0d6a7; S6-02 = T2211): helpers, the consumers, the merged skeleton instances
#check @RBM.Gauss.Sizes.st6_lam_pos
#check @RBM.Gauss.Sizes.st6_prec_det_iff
#check @RBM.Gauss.Sizes.st6_flowE_lt_two
#check @RBM.Gauss.Sizes.st6_flowE_le
#check @RBM.Gauss.Sizes.st6_mE_im_ge
#check @RBM.Gauss.Sizes.st6_expAvgU_of_pin
#check @RBM.Gauss.Sizes.ST_step6_caseIV_of_pins
#check @RBM.Gauss.Sizes.ST_step6_caseI_of_pins
#check @RBM.Gauss.Step6Inst.inst_skeleton6I
#check @RBM.Gauss.Step6Inst.inst_skeleton6IV
-- `RBM3D/Induction/ExpEtermsA.lean` (cd6fcba; S6-06 = T2222): the sibling's public lemmas and pin
#check @RBM.Gauss.Sizes.expLK_window_le
#check @RBM.Gauss.Sizes.expLK_env
#check @RBM.Gauss.Sizes.expLK_env_poly
#check @RBM.Gauss.Sizes.expLK_prec
#check @RBM.Gauss.Sizes.expLK_expect
#check @RBM.Gauss.Sizes.stExpLKLKHi_holds
-- `RBM3D/Induction/ExpAvg.lean` (d0d79ce; S6-03 = T2217): floor, `η⁻¹ ≤ N`, the `hAvg` pin, the skeleton instances
#check @RBM.Gauss.Sizes.expAvg_Bctl_ge
#check @RBM.Gauss.Sizes.expAvg_eta_inv_le
#check @RBM.Gauss.Sizes.stImproveExpAver_holds
#check @RBM.Gauss.Step6Inst.inst_skeleton6I_avg
#check @RBM.Gauss.Step6Inst.inst_skeleton6IV_avg
-- `RBM3D/Induction/ExpIniI.lean` (f2766db; S6-11 = T2223, route A): the primed regime-(i) skeleton
#check @RBM.Gauss.Sizes.STExpIniI'
#check @RBM.Gauss.Sizes.stExpIniI'_holds
#check @RBM.Gauss.Sizes.ST_step6_caseI_of_pins'
#check @RBM.Gauss.Step6Inst.inst_skeleton6I'
-- `RBM3D/Induction/DecayLoopB.lean` (250a118; S3-07b = T2135): the uniform loop decay and the random `ℰ`-term decay
#check @RBM.Gauss.Sizes.STDecayLoopU
#check @RBM.Gauss.Sizes.stDecayLoopU_of_step2
#check @RBM.Gauss.Sizes.stEtermDecay
-- `RBM3D/Induction/DecayLoopA.lean` (6179d8c)
#check @RBM.Gauss.Sizes.STdiamInf
-- `RBM3D/Induction/Step2Iterate.lean` (c5bbae7): bridges between the `n = 2` terms and the general-`n` terms
#check @RBM.Gauss.Sizes.STelklkM_seqHflow
#check @RBM.Gauss.Sizes.STegtM_seqHflow
#check @RBM.Gauss.Sizes.STELKLKM_eq_STelklkM
#check @RBM.Gauss.Sizes.KLloopOf_cutGlue1
#check @RBM.Gauss.Sizes.KLloopOf_cutGlue2
#check @RBM.Gauss.Sizes.STavgM_eq_STavgErrM
#check @RBM.Gauss.Sizes.STEGtM_eq_STegtM
-- `RBM3D/Induction/Step2Defs.lean` (86124dc): the matrix-level terms
#check @RBM.Gauss.Sizes.STmsig
#check @RBM.Gauss.Sizes.STLM
#check @RBM.Gauss.Sizes.STLM_seqHflow
#check @RBM.Gauss.Sizes.STLKM
#check @RBM.Gauss.Sizes.STavgM
#check @RBM.Gauss.Sizes.STEGtM
#check @RBM.Gauss.Sizes.STELKLKM
#check @RBM.Gauss.Sizes.STEGt
#check @RBM.Gauss.Sizes.STavgErrM
-- `RBM3D/Induction/Step34Pins.lean` (fc76526): general-`n` terms, Step-4/5 premises, `(deccA0)` w.h.p., instance data
#check @RBM.Gauss.Sizes.STLI
#check @RBM.Gauss.Sizes.STKI
#check @RBM.Gauss.Sizes.STLKI
#check @RBM.Gauss.Sizes.STelklk
#check @RBM.Gauss.Sizes.STavgErr
#check @RBM.Gauss.Sizes.STegt
#check @RBM.Gauss.Sizes.STLmaxU
#check @RBM.Gauss.Sizes.STLKU
#check @RBM.Gauss.Sizes.STAvgU
#check @RBM.Gauss.Sizes.STGdecayW
#check @RBM.Gauss.Sizes.STEKDecay
#check @RBM.Gauss.Step34Inst.szB
#check @RBM.Gauss.Step34Inst.zB
#check @RBM.Gauss.Step34Inst.flow_zB
#check @RBM.Gauss.Step34Inst.szB_flow_ht
-- `RBM3D/Induction/Step5Pins.lean` (d7da51e): regimes, the index set, the random `ℰ^{LK×LK}`, instance data
#check @RBM.Gauss.Sizes.STReg5I
#check @RBM.Gauss.Sizes.STReg5IV
#check @RBM.Gauss.Sizes.STIdx2
#check @RBM.Gauss.Sizes.STELKLK
#check @RBM.Gauss.Step5Inst.szG
#check @RBM.Gauss.Step5Inst.flow_zG
#check @RBM.Gauss.Step5Inst.szG_reg4
#check @RBM.Gauss.Step5Inst.szB_reg5I
-- `RBM3D/Induction/Step5Kit.lean` (85e43db)
#check @RBM.Gauss.Sizes.st5_conStInd_mono
#check @RBM.Gauss.Sizes.st5_t_lt_one
-- `RBM3D/Induction/Defs.lean` (64bdfd3)
#check @RBM.Gauss.Sizes.STKloop
#check @RBM.Gauss.Sizes.STKbound
#check @RBM.Gauss.Sizes.STflowE
#check @RBM.Gauss.Sizes.STFlow
#check @RBM.Gauss.InductionDefsInst.z0
#check @RBM.Gauss.InductionDefsInst.sInst
#check @RBM.Gauss.InductionDefsInst.tInst
-- `RBM3D/Induction/KDecay.lean` (dab074c): `(eq:bcal_k)` uniformly in `u ∈ [s,t]`
#check @RBM.Gauss.Sizes.stKbound_timeIcc
-- `RBM3D/Loop/KLFinal.lean` (471b643): the per-time form (portmap; not used)
#check @RBM.Gauss.Sizes.stKbound_of_flow
-- `RBM3D/Loop/GLoopFlow.lean` (868b3b4), `Loop/GLoop.lean` (e0c58e6), `Loop/KLTree.lean` (b06ff9b), `Path/Walk.lean` (ddf5f74)
#check @RBM.Gauss.Sizes.Lloop
#check @RBM.Gauss.Sizes.norm_Lloop_le
#check @RBM.Gauss.etaT
#check @RBM.Gauss.etaT_pos
#check @RBM.Loop.KLK_one
#check @RBM.Loop.KLloopOf
#check @RBM.Gauss.Sizes.walk_measurable_Lloop
-- `RBM3D/Gauss/FineModel.lean` (0a873f1)
#check @RBM.Gauss.Sizes.SeqΩ
#check @RBM.Gauss.Sizes.seqP
#check @RBM.Gauss.Sizes.isProbabilityMeasure_seqP
#check @RBM.Gauss.Sizes.seqHflow
-- `RBM3D/Defs/StochDomAt.lean` (9e2b00f)
#check @RBM.Gauss.HighProbAt
#check @RBM.Path.TimeIcc
#check @RBM.Gauss.Sizes.Prec
#check @RBM.Gauss.Sizes.Whp
#check @RBM.StochDomAt.of_subset
#check @RBM.StochDomAt.of_le_left
#check @RBM.StochDomAt.of_subset_union
#check @RBM.Gauss.Sizes.tendsto_size
-- `RBM3D/Defs/Sizes.lean` (0a873f1), `Defs/Params.lean` (c3f3d5d), `Defs/Lattice.lean` (51f1a17)
#check @RBM.Gauss.zdistInf
#check @RBM.Gauss.zdistInf_le_zdistD
#check @RBM.Gauss.zdistD_le_mul_zdistInf
#check @RBM.Gauss.Sizes.size
#check @RBM.Gauss.Sizes.Bandwidth
#check @RBM.Gauss.Sizes.SizeTendsto
#check @RBM.Gauss.Sizes.Admissible
#check @RBM.Gauss.Sizes.locDomain
#check @RBM.Gauss.Sizes.Bctl
#check @RBM.Gauss.SizesInst.sz0
#check @RBM.ellT
#check @RBM.Bparam
#check @RBM.zdistD
-- `RBM3D/Defs/Semicircle.lean` (fbc9870), `Defs/Block.lean` (a722f63), `Evolution/Pins.lean` (d9de66f), `Graph/LWPins.lean` (975f4ff)
#check @RBM.mSigma
#check @RBM.norm_mSigma
#check @RBM.lemE
#check @RBM.lemT
#check @RBM.lemT_lt_one
#check @RBM.abs_lemE_le
#check @RBM.SB
#check @RBM.SB_transpose
#check @RBM.sum_norm_SB_row
#check @RBM.EKFastDecay
#check @RBM.Gauss.Sizes.LWtermEXP

/-! ## 2. Vocabulary and statements of the public theorems of `ExpEtermsB.lean` (closed `Prop`s) -/

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal

namespace RBM.Gauss.Sizes.T2228Check

open RBM RBM.Loop RBM.Path RBM.Gauss

/-! ### Vocabulary (same bodies in `ExpEtermsB.lean`, namespace `RBM.Gauss.Sizes`) -/

-- The `(𝓛-𝒦)^{(3)}` part of `𝓔^{G̃,(2)}` of a fine matrix `H` (`STEGtM` with `STLM` replaced by `STLKM` in the cut 3-loops).
noncomputable def expDrEGtLKM {d : ℕ} (sz : Sizes d) (n : ℕ) (E u : ℝ)
    (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) : ℂ :=
  (((sz.W n : ℕ) : ℂ) ^ d) * ∑ x : Zd d (sz.L n), ∑ y : Zd d (sz.L n),
    (sz.STavgM n E u H (σ 0) x * SB d (sz.L n) (sz.lam n) x y *
        sz.STLKM n E u H ![σ 0, σ 0, σ 1] ![y, a 0, a 1] +
      sz.STavgM n E u H (σ 1) x * SB d (sz.L n) (sz.lam n) x y *
        sz.STLKM n E u H ![σ 0, σ 1, σ 1] ![a 0, y, a 1])

-- The deterministic part `W^d Σ_k Σ_{x,y} (𝔼 avg_{σ_k}(x)) S_{xy} 𝒦^{(3)}(cut_k y)` of `𝔼𝓔^{G̃,(2)}`.
noncomputable def expDrEGtK {d : ℕ} (sz : Sizes d) (n : ℕ) (E u : ℝ) (σ : Fin 2 → Bool)
    (a : Fin 2 → Zd d (sz.L n)) : ℂ :=
  (((sz.W n : ℕ) : ℂ) ^ d) * ∑ x : Zd d (sz.L n), ∑ y : Zd d (sz.L n),
    ((∫ ω, sz.STavgM n E u (sz.seqHflow n u ω) (σ 0) x ∂(sz.seqP)) * SB d (sz.L n) (sz.lam n) x y *
        sz.STKloop n E u ![σ 0, σ 0, σ 1] ![y, a 0, a 1] +
      (∫ ω, sz.STavgM n E u (sz.seqHflow n u ω) (σ 1) x ∂(sz.seqP)) * SB d (sz.L n) (sz.lam n) x y *
        sz.STKloop n E u ![σ 0, σ 1, σ 1] ![a 0, y, a 1])

/-! ### Deterministic steps (one size) -/

-- (regime bound) regime (iv), `1-u ≤ ilambda²/L^d`: `B_{u,0} ≤ 2 (L^d(1-u))⁻¹`, i.e. `W^{-d}B_{u,0} ≤ 2 (N(1-u))⁻¹`
-- (`(λ²+(1-u))⁻¹ ≤ (L^d(1-u))⁻¹`; `size = W^d L^d`).
def expDr_Bctl_le_IV : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (n : ℕ) {u : ℝ}, u < 1 → 1 - u ≤ sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ d →
    sz.Bctl n u ≤ 2 * (((sz.size n : ℕ) : ℝ) * (1 - u))⁻¹

-- (envelope `𝓔^{G̃}`) every sample: `‖avg‖ ≤ η⁻¹ + 1` (`norm_Lloop_le` at `k = 0`, `norm_mSigma`), `‖𝓛^{(3)}‖ ≤ η⁻³`,
-- column sums of `S` (`SB_transpose`, `sum_norm_SB_row`, `3 ≤ L`), two cuts.
def expDr_envEGt : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (n : ℕ) {E u : ℝ}, |E| < 2 → u < 1 →
    ∀ (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) (ω : sz.SeqΩ),
      ‖sz.STEGt n E u σ a ω‖ ≤
        2 * (((sz.W n : ℕ) : ℝ) ^ d * ((sz.L n : ℕ) : ℝ) ^ d) * (((etaT E u)⁻¹ + 1) * (etaT E u)⁻¹ ^ 3)

-- (split) `𝔼𝓔^{G̃} = (𝔼 avg)·S·𝒦^{(3)} + 𝔼[avg·S·(𝓛-𝒦)^{(3)}]`: `STLM = STKloop + STLKM`, linearity of the integral
-- (every summand bounded and measurable: `norm_Lloop_le`, `walk_measurable_Lloop`; `seqP` is a probability measure).
def expDr_EGt_split : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (n : ℕ) {E u : ℝ}, |E| < 2 → u < 1 →
    ∀ (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)),
      sz.STExpEGt n E u σ a =
        expDrEGtK sz n E u σ a + ∫ ω, expDrEGtLKM sz n E u (sz.seqHflow n u ω) σ a ∂(sz.seqP)

/-! ### Along the sequence -/

-- (envelopes are polynomial) on the flow, uniformly in `u ∈ [s_n,t_n]`: `𝓔^{LK×LK}` (`expLK_env`, monotone in `u ≤ t`,
-- `expLK_env_poly`), `𝓔^{G̃}` (`expDr_envEGt`, `η_u⁻¹ ≤ N` from `expAvg_eta_inv_le`), and its `(𝓛-𝒦)^{(3)}` part
-- (`‖𝒦^{(3)}‖ ≤ N B²` from `stKbound_timeIcc` at `τ = 1`, `B ≤ 2(1-u)⁻¹ ≤ 2η_u⁻¹`).
def expDr_env_poly : Prop :=
  ∀ {d : ℕ} (sz : Sizes d), 3 ≤ d → ∀ {κ ε 𝔠 𝔡 : ℝ}, 0 < κ → 0 < ε → ∀ {z : ℕ → ℂ}, STFlow sz κ ε 𝔠 𝔡 z →
    ∀ {s t : ℕ → ℝ}, (∀ n, 0 ≤ s n) → (∀ n, s n ≤ t n) → (∀ n, t n ≤ lemT (z n)) →
      ∀ᶠ n in atTop, ∀ (p : STIdx2 sz s t n) (ω : sz.SeqΩ),
        ‖sz.STELKLK n (STflowE z n) (p.1 : ℝ) p.2.1 p.2.2 ω‖ ≤ ((sz.size n : ℕ) : ℝ) ^ (6 : ℝ) ∧
        ‖sz.STEGt n (STflowE z n) (p.1 : ℝ) p.2.1 p.2.2 ω‖ ≤ ((sz.size n : ℕ) : ℝ) ^ (6 : ℝ) ∧
        ‖expDrEGtLKM sz n (STflowE z n) (p.1 : ℝ) (sz.seqHflow n (p.1 : ℝ) ω) p.2.1 p.2.2‖ ≤
          ((sz.size n : ℕ) : ℝ) ^ (6 : ℝ)

-- (generic `≺ → 𝔼`) the first moment outside the failure event (private copy of `expLK_first_moment`,
-- `ExpEtermsA.lean:461`; no measurability), a polynomial envelope and a polynomial floor of the deterministic `R`;
-- the deterministic `Prec` through `st6_prec_det_iff`.
def expDr_expect : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) {V : ℕ → Type} (X : ∀ n, V n → sz.SeqΩ → ℂ) (R : ∀ n, V n → ℝ) {Kenv Kf : ℝ},
    sz.SizeTendsto →
    (∀ᶠ n in atTop, ∀ v ω, ‖X n v ω‖ ≤ ((sz.size n : ℕ) : ℝ) ^ Kenv) →
    (∀ᶠ n in atTop, ∀ v, ((sz.size n : ℕ) : ℝ) ^ (-Kf) ≤ R n v) →
    sz.Prec (U := V) (fun n v ω => ‖X n v ω‖) (fun n v _ => R n v) →
      sz.Prec (U := V) (fun n v _ => ‖∫ ω, X n v ω ∂(sz.seqP)‖) (fun n v _ => R n v)

-- (`𝓔^{LK×LK}`, random, no regime) off the failure event of `STLKU … 2` at `τ/2`, both factors `≤ N^{τ/2}B²` for every
-- index: `‖𝓔‖ ≤ W^d L^d N^τ B⁴` (`expLK_window_le` with `M = f = N^{τ/2}B²`).  No grid lift (§64 (4)).
def expDr_LK_prec : Prop :=
  ∀ {d : ℕ} (sz : Sizes d), sz.SizeTendsto → ∀ {E s t : ℕ → ℝ}, STLKU sz E s t →
    sz.Prec (U := STIdx2 sz s t)
      (fun n p ω => ‖sz.STELKLK n (E n) (p.1 : ℝ) p.2.1 p.2.2 ω‖)
      (fun n p _ => ((sz.size n : ℕ) : ℝ) * (sz.Bctl n (p.1 : ℝ)) ^ 4)

-- (`(𝓛-𝒦)^{(3)}` part of `𝓔^{G̃}`, random) `STLKU … 1` (`avg = (𝓛-𝒦)^{(1)}`: `KLK_one`) and `STLKU … 3` at the cut
-- indices, `of_subset_union`, `τ' = τ/3`: `≤ 2 N^{2τ/3} N B⁴`.
def expDr_EGtLK_prec : Prop :=
  ∀ {d : ℕ} (sz : Sizes d), sz.SizeTendsto → ∀ {E s t : ℕ → ℝ}, STLKU sz E s t →
    sz.Prec (U := STIdx2 sz s t)
      (fun n p ω => ‖expDrEGtLKM sz n (E n) (p.1 : ℝ) (sz.seqHflow n (p.1 : ℝ) ω) p.2.1 p.2.2‖)
      (fun n p _ => ((sz.size n : ℕ) : ℝ) * (sz.Bctl n (p.1 : ℝ)) ^ 4)

-- (deterministic part of `𝔼𝓔^{G̃}`) `(res_ELK_n=1)` (`STExpAvgU`) and `(eq:bcal_k)` at `k = 3` uniformly in `u`
-- (`stKbound_timeIcc`), both deterministic (`st6_prec_det_iff`).
def expDr_EGtK_prec : Prop :=
  ∀ {d : ℕ} (sz : Sizes d), 3 ≤ d → ∀ {κ ε 𝔠 𝔡 : ℝ}, 0 < κ → 0 < ε → ∀ {z : ℕ → ℂ}, STFlow sz κ ε 𝔠 𝔡 z →
    ∀ {s t : ℕ → ℝ}, (∀ n, 0 ≤ s n) → (∀ n, s n ≤ t n) → (∀ n, t n ≤ lemT (z n)) →
      STExpAvgU sz (STflowE z) s t →
        sz.Prec (U := STIdx2 sz s t)
          (fun n p _ => ‖expDrEGtK sz n (STflowE z n) (p.1 : ℝ) p.2.1 p.2.2‖)
          (fun n p _ => ((sz.size n : ℕ) : ℝ) * (sz.Bctl n (p.1 : ℝ)) ^ 4)

/-! ### The pins -/

-- ((iv) assembly) `|D_u| ≺ N B⁴ ≤ 16 (1-u)⁻¹(N(1-u))⁻³` (`expDr_expect` twice with `Kenv = 6`, `Kf = 3`,
-- `expDr_EGt_split`, `expDr_EGtK_prec`, `expDr_Bctl_le_IV`).
def STExpDriftLoConcl_of_LKU : Prop :=
  ∀ {d : ℕ} (sz : Sizes d), 3 ≤ d → ∀ {κ ε 𝔠 𝔡 : ℝ}, 0 < κ → 0 < ε → ∀ {z : ℕ → ℂ}, STFlow sz κ ε 𝔠 𝔡 z →
    ∀ {s t : ℕ → ℝ}, (∀ n, 0 ≤ s n) → (∀ n, s n ≤ t n) → (∀ n, t n ≤ lemT (z n)) →
      STReg5IV sz s t → STLKU sz (STflowE z) s t → STExpAvgU sz (STflowE z) s t →
        STExpDriftLoConcl sz (STflowE z) s t

-- the pin `(eq:Exp(L-K)2)`, `(eq:ExpLWn=2_smalleta)` (`Step6Pins.lean:323`), with `𝔠_d = 1/100`
def stExpDriftLo_holds : Prop := ∀ d : ℕ, STExpDriftLo d

-- (decay) `stDecayLoopU_of_step2 … 0`, `stEtermDecay … 2` at `(ε, D+1)`, the first moment off the `Whp` event
-- (`P ≤ N^{-(D+7)}`, envelope `N⁶`, `W ≤ N`, `W ≥ 4` eventually); the conclusion is a `Whp` of an eventually full set.
def STExpDriftDecayConcl_of_GdecayW : Prop :=
  ∀ {d : ℕ} (sz : Sizes d), 3 ≤ d → ∀ {κ ε 𝔠 𝔡 : ℝ}, 0 < κ → 0 < ε → ∀ {z : ℕ → ℂ}, STFlow sz κ ε 𝔠 𝔡 z →
    ∀ {s t : ℕ → ℝ}, (∀ n, 0 ≤ s n) → (∀ n, s n ≤ t n) → (∀ n, t n ≤ lemT (z n)) →
      STGdecayW sz (STflowE z) s t 0 → STExpDriftDecayConcl sz (STflowE z) s t

-- the pin `(deccA0)` for `D_u` (`Step6Pins.lean:335`), with `𝔠_d = 1/100`
def stExpDriftDecay_holds : Prop := ∀ d : ℕ, STExpDriftDecay d

end RBM.Gauss.Sizes.T2228Check

/-! ## 3. The statements of the instances T2228 compiles -/

namespace RBM.Gauss.Step6Inst.T2228Check

open RBM RBM.Gauss RBM.Gauss.Sizes RBM.Gauss.SizesInst RBM.Gauss.InductionDefsInst RBM.Gauss.Step34Inst
  RBM.Gauss.Step5Inst RBM.Path RBM.Loop Filter

-- statement of `inst_expDriftLo_holds` (the merged `inst_expDriftLo` with `h := stExpDriftLo_holds 3`; regime (iv) data)
example : Prop :=
  InstIng6Concl (fun sz E s t => STExpAvgU sz E s t → STExpDriftLoConcl sz E s t) szG zB
    (fun _ => 5 / 8) (fun _ => 3 / 4)

-- statement of `inst_expDriftDecay_holds` (the merged `inst_expDriftDecay` with `h := stExpDriftDecay_holds 3`; regime (i))
example : Prop :=
  InstIng6Concl (fun sz E s t => STExpDriftDecayConcl sz E s t) szB zB (fun _ => 7 / 8) (fun _ => 15 / 16)

-- statement of `inst_skeleton6IV_Lo` (the merged `inst_skeleton6IV_avg` with `hLo := stExpDriftLo_holds 3`)
example : Prop :=
  STExpDuhamelZ 3 → STExpIntIV 3 →
    InstIng6Concl (fun sz E s t => STStep6Concl sz E s t) szG zB (fun _ => 5 / 8) (fun _ => 3 / 4)

-- statement of `inst_skeleton6I_Dec` (the merged `inst_skeleton6I'` with `hLK := stExpLKLKHi_holds 3`,
-- `hAvg := stImproveExpAver_holds 3`, `hDec := stExpDriftDecay_holds 3`)
example : Prop :=
  LWtermEXP 3 → STExpDuhamelZ 3 → STExpDuhamelQ 3 → STExpWardI 3 → STExpIntI 3 →
    InstIng6Concl (fun sz E s t => STStep6Concl sz E s t) szB zB (fun _ => 7 / 8) (fun _ => 15 / 16)

-- statement of `inst_expDr_Bctl_le_IV` (`expDr_Bctl_le_IV` at `szG`, `n = 0`, `u = 3/4`; `1/4 ≤ 25/64`)
example : Prop :=
  szG.Bctl 0 (3 / 4) ≤ 2 * (((szG.size 0 : ℕ) : ℝ) * (1 - 3 / 4))⁻¹

-- statement of `inst_expDr_envEGt` (`expDr_envEGt` at `sz0`, `n = 0`, `E = u = 1/2`, `σ = (+,-)`, `a = (0,0)`)
example : Prop :=
  ∀ ω : sz0.SeqΩ,
    ‖sz0.STEGt 0 (1 / 2) (1 / 2) ![true, false] ![(0 : Zd 3 (sz0.L 0)), 0] ω‖ ≤
      2 * (((sz0.W 0 : ℕ) : ℝ) ^ 3 * ((sz0.L 0 : ℕ) : ℝ) ^ 3) *
        (((etaT (1 / 2) (1 / 2))⁻¹ + 1) * (etaT (1 / 2) (1 / 2))⁻¹ ^ 3)

end RBM.Gauss.Step6Inst.T2228Check
