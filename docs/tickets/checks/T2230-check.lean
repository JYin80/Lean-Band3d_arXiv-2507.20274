/-
Release check for T2230 (dispatcher V1, Mon Oct  5 23:36 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §16, §17, §20,
§29, §45 O2, §64 (4)).
MA-04 (main-theorem assembly, gate MA; fourth proof ticket of the MA split, T2192 portmap P.5 row MA-04 `:417`):
`RBM3D/Main/ZNet.lean`, the `z`-net `[net]` (`1_2:1228`) in the direct parametrization: the pins `MANetLoc`,
`MANetQD` (probe `97d958e:RBM3D/Probe/T2192Pins.lean:2043`, `:2046`; not on `main`), proved from the merged fixed-`z`
statements `locSCFixed`, `QDiffFixed` (MA-03 = T2225, 0d5868e) by a deterministic net of mesh `N^{-7}`, at most
`25 N^{14}` points inside `𝐃_{κ,ε}`, per-point `τ/2`, `D + 15`, and a union bound.
Section 1: the merged names the ticket uses (exact namespaces; file and last commit on `main` 37289f6).
Section 2: the two pins (probe text, docstrings stripped), as `*_pin` in the temporary namespace
`RBM.Endpoints.T2230Check`; T2230 defines each in `RBM.Endpoints` under the probe's name.
Section 3: the intermediate statements T2230 proves (net union, 2D grid, Lipschitz bounds, `𝓑` ratio, the four
deterministic cover lemmas, the count), as `*_pin : Prop`.
Section 4: the statements of the three MA-04 instances, temporary namespace `RBM.Endpoints.Inst.T2230Check`.
Statements and `#check` only: no theorem, no proof.  Never imported or merged.
Imports: `RBM3D.Main.FixedZ` (closure: 56 modules, contains MA-01, MA-02, MA-03, `Green/LDE`, `Propagator/*`,
`Defs/SemicircleIntegral`, `Gauss/FlowCalculus`) and `RBM3D.Induction.ContinuityNet` (for `cont_green_diff`; its own
imports are in that closure apart from `Mathlib.Probability.Moments.SubGaussian`).  No Mathlib lemma is checked.
Run from the main worktree: `lake env lean docs/tickets/checks/T2230-check.lean`.
-/
import RBM3D.Main.FixedZ
import RBM3D.Induction.ContinuityNet

/-! ## 1. Merged names -/

-- `RBM3D/Main/FixedZ.lean` (0d5868e, MA-03 = T2225)
#check @RBM.Endpoints.locSCFixed
#check @RBM.Endpoints.QDiffFixed
#check @RBM.Endpoints.MAFixed
#check @RBM.Endpoints.fixed_of_ML
#check @RBM.Endpoints.locSCFixed_of_ML
#check @RBM.Endpoints.QDiffFixed_of_ML
#check @RBM.Endpoints.prob_union_le
#check @RBM.Endpoints.two_rpow_le
-- `RBM3D/Main/ZTransfer.lean` (afdb81e, MA-02 = T2219)
#check @RBM.Endpoints.im_msc_ge
-- `RBM3D/Endpoints.lean` (8a43715, MA-01 = T2210)
#check @RBM.Endpoints.calB
#check @RBM.Endpoints.distB
#check @RBM.Endpoints.Mband
#check @RBM.Endpoints.avg2
#check @RBM.Endpoints.ThetaPM
#check @RBM.Endpoints.ThetaPP
#check @RBM.Endpoints.profPM
#check @RBM.Endpoints.profPP
#check @RBM.Endpoints.qdBound
#check @RBM.Endpoints.qdBoundExp
#check @RBM.Endpoints.locBad1z
#check @RBM.Endpoints.locBad2z
#check @RBM.Endpoints.qd1Badz
#check @RBM.Endpoints.qd2Badz
#check @RBM.Endpoints.locBad1
#check @RBM.Endpoints.locBad2
#check @RBM.Endpoints.qd1Bad
#check @RBM.Endpoints.qd2Bad
#check @RBM.Endpoints.locSC
#check @RBM.Endpoints.QDiff
#check @RBM.Endpoints.inv_size_mul_le_calB
#check @RBM.Endpoints.calB_antitone
#check @RBM.Endpoints.calB_nonneg
#check @RBM.Endpoints.Nsz_pos
#check @RBM.Endpoints.locDomain_im_pos
#check @RBM.Endpoints.locDomain_nonempty
#check @RBM.Endpoints.locDomain_empty_kappa
#check @RBM.Endpoints.Inst.inst_locSC
#check @RBM.Endpoints.Inst.inst_QDiff
-- `RBM3D/Induction/ContinuityNet.lean` (5b6cbc1)
#check @RBM.Ind.ContinuityNet.cont_green_diff
#check @RBM.Ind.ContinuityNet.cont_Gres_true_eq_green
#check @RBM.Ind.ContinuityNet.cont_norm_green_le
-- `RBM3D/Green/EntryCore.lean` (890a89f)
#check @RBM.green
-- `RBM3D/Green/LDE.lean` (7c7652e)
#check @RBM.Green.tendsto_W
-- `RBM3D/Gauss/FlowCalculus.lean` (6f99812)
#check @RBM.Gauss.norm_Gsig_le_inv_eta
#check @RBM.Gauss.norm_matrix_entry_le_opNorm
-- `RBM3D/Gauss/FineModel.lean` (0a873f1)
#check @RBM.Gauss.Sizes.SeqΩ
#check @RBM.Gauss.Sizes.seqP
#check @RBM.Gauss.Sizes.seqXmat
#check @RBM.Gauss.Sizes.seqXmat_isHermitian
-- `RBM3D/Loop/GLoopFlow.lean` (868b3b4)
#check @RBM.Gauss.Gres
#check @RBM.Gauss.Sizes.Gn
-- `RBM3D/Defs/Sizes.lean` (0a873f1)
#check @RBM.Gauss.Sizes
#check @RBM.Gauss.Sizes.three_le_L
#check @RBM.Gauss.Sizes.size
#check @RBM.Gauss.Sizes.SizeTendsto
#check @RBM.Gauss.Sizes.Admissible
#check @RBM.Gauss.Sizes.locDomain
#check @RBM.Gauss.Iblk
#check @RBM.Gauss.card_Iblk
#check @RBM.Gauss.SizesInst.sz0
#check @RBM.Gauss.SizesInst.sz0_admissible
-- `RBM3D/Defs/StochDomAt.lean` (9e2b00f)
#check @RBM.Gauss.Sizes.one_le_size
-- `RBM3D/Universality/Pins.lean` (f8ad4b4)
#check @RBM.Univ.Nsz
#check @RBM.Univ.UNMLOut
#check @RBM.Univ.UNLocAvgBand
-- `RBM3D/Defs/Semicircle.lean` (fbc9870)
#check @RBM.msc
#check @RBM.msc_mul
#check @RBM.msc_im_pos
#check @RBM.norm_msc_lt_one
#check @RBM.mE
#check @RBM.norm_mE
#check @RBM.lemE
#check @RBM.lemT
#check @RBM.lemT_lt_one
#check @RBM.abs_lemE_lt_two
#check @RBM.msc_eq_sqrt_mul_mE
#check @RBM.msc_add_eq_neg_inv
-- `RBM3D/Defs/SemicircleIntegral.lean` (709c5c7)
#check @RBM.msc_eq_integral
-- `RBM3D/Defs/Block.lean` (a722f63)
#check @RBM.SB
#check @RBM.norm_SB
-- `RBM3D/Propagator/Basic.lean` (020ec7a), `Propagator/Deriv.lean` (2d0baa3), `Propagator/Props4.lean` (892334b)
#check @RBM.Theta
#check @RBM.Theta_sub_Theta
#check @RBM.norm_Theta_le

/-! ## 2. The two pins (probe `:2043`, `:2046`; docstrings stripped) -/

open MeasureTheory ProbabilityTheory Filter Matrix Topology
open RBM RBM.Gauss RBM.Gauss.Sizes RBM.Univ
open scoped NNReal ENNReal

namespace RBM.Endpoints.T2230Check

-- probe `:2043` (`MANetLoc`; Thm 2.2 `1_2:386-395` from its fixed-`z` form, the net `1_2:1228`)
def MANetLoc_pin : Prop := locSCFixed → locSC

-- probe `:2046` (`MANetQD`; Thm 2.5 `1_2:488-511` from its fixed-`z` form; the expectation half is already pointwise)
def MANetQD_pin : Prop := QDiffFixed → QDiff

/-! ## 3. Intermediate statements -/

-- the abstract union over a finite net (explicit form; replaces RBM2D `regionUnif_core`, no `StochDomAt`, no good event)
def net_union_le_pin : Prop :=
  ∀ {Ω ι : Type} [MeasurableSpace Ω] (P : Measure Ω) (S : Finset ι) (A : Set Ω) (B : ι → Set Ω) (p : ℝ≥0∞),
    A ⊆ ⋃ i ∈ S, B i → (∀ i ∈ S, P (B i) ≤ p) → P A ≤ (S.card : ℝ≥0∞) * p

-- the count: `#net ≤ 25 N^{14}` points at `N^{-(D+15)}` each give `N^{-D}` for `N ≥ 25`
def net_count_pin : Prop :=
  ∀ {N D : ℝ} (c : ℕ), 25 ≤ N → (c : ℝ) ≤ 25 * N ^ (14 : ℕ) →
    (c : ℝ≥0∞) * ENNReal.ofReal (N ^ (-(D + 15))) ≤ ENNReal.ofReal (N ^ (-D))

-- the 2D grid of mesh `N^{-7}` inside `𝐃_{κ,ε}` (empty when `𝐃_{κ,ε}` is)
def zNet_exists_pin : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) {κ ε : ℝ}, 0 < κ → ∀ n : ℕ, ∃ S : Finset ℂ,
    (S.card : ℝ) ≤ 25 * Nsz sz n ^ (14 : ℕ) ∧ (∀ w ∈ S, sz.locDomain κ ε n w) ∧
    ∀ z : ℂ, sz.locDomain κ ε n z → ∃ w ∈ S,
      |z.re - w.re| ≤ Nsz sz n ^ (-7 : ℝ) ∧ |z.im - w.im| ≤ Nsz sz n ^ (-7 : ℝ)

-- `𝓑_{η',K} ≤ 2 𝓑_{η,K}` for `|η' - η| ≤ η/2` (relative continuity of the deterministic right side in `η`)
def calB_shift_le_pin : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (n : ℕ) {η η' K : ℝ}, 0 < η → 0 ≤ K → |η' - η| ≤ η / 2 →
    calB sz n η' K ≤ 2 * calB sz n η K

-- `1 - |m|² = Im z / (Im z + Im m) ≥ Im z / (1 + Im z)` (from `msc_mul`)
def one_sub_lemT_ge_pin : Prop :=
  ∀ {z : ℂ}, 0 < z.im → z.im / (1 + z.im) ≤ 1 - lemT z

-- Lipschitz bound of `msc` (Stieltjes form `msc_eq_integral`, or `msc_add_eq_neg_inv`)
def msc_lip_pin : Prop :=
  ∀ {z z' : ℂ} {η : ℝ}, 0 < η → η ≤ z.im → η ≤ z'.im → ‖msc z - msc z'‖ ≤ η⁻¹ * η⁻¹ * ‖z - z'‖

-- the resolvent entries: bound and Lipschitz bound, for every `ω` (`seqXmat` Hermitian; `cont_green_diff` at `H = H'`)
def Gn_entry_le_pin : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (n : ℕ) (ω : sz.SeqΩ) {z : ℂ} {η : ℝ}, 0 < η → η ≤ z.im →
    ∀ x y : Idx d (sz.L n) (sz.W n), ‖sz.Gn n z ω x y‖ ≤ η⁻¹

def Gn_entry_lip_pin : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (n : ℕ) (ω : sz.SeqΩ) {z z' : ℂ} {η : ℝ}, 0 < η → η ≤ z.im → η ≤ z'.im →
    ∀ x y : Idx d (sz.L n) (sz.W n), ‖sz.Gn n z ω x y - sz.Gn n z' ω x y‖ ≤ η⁻¹ * η⁻¹ * ‖z - z'‖

-- the block average does not increase a uniform entrywise bound (`card_Iblk`)
def avg2_lip_pin : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (n : ℕ) (F F' : Idx d (sz.L n) (sz.W n) → Idx d (sz.L n) (sz.W n) → ℂ) {c : ℝ},
    (∀ x y, ‖F x y - F' x y‖ ≤ c) → ∀ a b : Zd d (sz.L n), ‖avg2 sz n F a b - avg2 sz n F' a b‖ ≤ c

-- Lipschitz bounds of the deterministic profiles (`‖Θ‖ ≤ (1 - t)⁻¹ ≤ 2/η`, `Theta_sub_Theta`, `norm_SB`)
def profPM_lip_pin : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (n : ℕ) {z z' : ℂ} {η : ℝ}, 0 < η → η ≤ z.im → z.im ≤ 1 → η ≤ z'.im → z'.im ≤ 1 →
    ∀ a b : Zd d (sz.L n), ‖profPM sz n z a b - profPM sz n z' a b‖ ≤ 12 * η⁻¹ ^ 4 * ‖z - z'‖

def profPP_lip_pin : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (n : ℕ) {z z' : ℂ} {η : ℝ}, 0 < η → η ≤ z.im → z.im ≤ 1 → η ≤ z'.im → z'.im ≤ 1 →
    ∀ a b : Zd d (sz.L n), ‖profPP sz n z a b - profPP sz n z' a b‖ ≤ 12 * η⁻¹ ^ 4 * ‖z - z'‖

-- the four deterministic cover lemmas (§64 (4): only the deterministic, floored right sides `W^τ 𝓑_{η,·}`, `qdBound`
-- are lifted; the random left sides move by a deterministic amount for every `ω`)
def locBad1_net_pin : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (n : ℕ), 3 ≤ d → ∀ {κ ε τ : ℝ}, 0 < ε → 32 ≤ Nsz sz n →
    5 ≤ ((sz.W n : ℕ) : ℝ) ^ (τ / 2) → ∀ S : Finset ℂ, (∀ w ∈ S, sz.locDomain κ ε n w) →
    (∀ z : ℂ, sz.locDomain κ ε n z → ∃ w ∈ S,
      |z.re - w.re| ≤ Nsz sz n ^ (-7 : ℝ) ∧ |z.im - w.im| ≤ Nsz sz n ^ (-7 : ℝ)) →
    ∀ ω : sz.SeqΩ, locBad1 sz κ ε τ n ω → ∃ w ∈ S, locBad1z sz (τ / 2) n w ω

def locBad2_net_pin : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (n : ℕ), 3 ≤ d → ∀ {κ ε τ : ℝ}, 0 < ε → 32 ≤ Nsz sz n →
    5 ≤ ((sz.W n : ℕ) : ℝ) ^ (τ / 2) → ∀ S : Finset ℂ, (∀ w ∈ S, sz.locDomain κ ε n w) →
    (∀ z : ℂ, sz.locDomain κ ε n z → ∃ w ∈ S,
      |z.re - w.re| ≤ Nsz sz n ^ (-7 : ℝ) ∧ |z.im - w.im| ≤ Nsz sz n ^ (-7 : ℝ)) →
    ∀ ω : sz.SeqΩ, locBad2 sz κ ε τ n ω → ∃ w ∈ S, locBad2z sz (τ / 2) n w ω

def qd1Bad_net_pin : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (n : ℕ), 3 ≤ d → ∀ {κ ε τ : ℝ}, 0 < ε → 32 ≤ Nsz sz n →
    5 ≤ ((sz.W n : ℕ) : ℝ) ^ (τ / 2) → ∀ S : Finset ℂ, (∀ w ∈ S, sz.locDomain κ ε n w) →
    (∀ z : ℂ, sz.locDomain κ ε n z → ∃ w ∈ S,
      |z.re - w.re| ≤ Nsz sz n ^ (-7 : ℝ) ∧ |z.im - w.im| ≤ Nsz sz n ^ (-7 : ℝ)) →
    ∀ ω : sz.SeqΩ, qd1Bad sz κ ε τ n ω → ∃ w ∈ S, qd1Badz sz (τ / 2) n w ω

def qd2Bad_net_pin : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (n : ℕ), 3 ≤ d → ∀ {κ ε τ : ℝ}, 0 < ε → 32 ≤ Nsz sz n →
    5 ≤ ((sz.W n : ℕ) : ℝ) ^ (τ / 2) → ∀ S : Finset ℂ, (∀ w ∈ S, sz.locDomain κ ε n w) →
    (∀ z : ℂ, sz.locDomain κ ε n z → ∃ w ∈ S,
      |z.re - w.re| ≤ Nsz sz n ^ (-7 : ℝ) ∧ |z.im - w.im| ≤ Nsz sz n ^ (-7 : ℝ)) →
    ∀ ω : sz.SeqΩ, qd2Bad sz κ ε τ n ω → ∃ w ∈ S, qd2Badz sz (τ / 2) n w ω

-- statements of the two main theorems
def netLoc_pin : Prop := MANetLoc_pin
def netQD_pin : Prop := MANetQD_pin

end RBM.Endpoints.T2230Check

/-! ## 4. The three MA-04 instances (`d = 3`, `sz0`, `(𝔠, 𝔡) = (1/6, 1/10)`, `κ = 1/10`, `ε = 1/20`, `τ = 1/10`, `D = 2`) -/

namespace RBM.Endpoints.Inst.T2230Check

open RBM.Gauss.SizesInst RBM.Univ.UNInst

-- `inst_netLoc`: the conclusion of the merged `inst_locSC` (`Endpoints.lean:567`) from `locSCFixed`
def inst_netLoc_pin : Prop :=
  locSCFixed →
    ∀ᶠ n in atTop, Sizes.seqP sz0 {ω | locBad1 sz0 (1 / 10) (1 / 20) (1 / 10) n ω} ≤
        ENNReal.ofReal (Nsz sz0 n ^ (-(2 : ℝ))) ∧
      Sizes.seqP sz0 {ω | locBad2 sz0 (1 / 10) (1 / 20) (1 / 10) n ω} ≤ ENNReal.ofReal (Nsz sz0 n ^ (-(2 : ℝ)))

-- `inst_netQD`: the conclusion of the merged `inst_QDiff` (`Endpoints.lean:587`) from `QDiffFixed`
def inst_netQD_pin : Prop :=
  QDiffFixed →
    ∀ᶠ n in atTop,
      (Sizes.seqP sz0 {ω | qd1Bad sz0 (1 / 10) (1 / 20) (1 / 10) n ω} ≤ ENNReal.ofReal (Nsz sz0 n ^ (-(2 : ℝ))) ∧
       Sizes.seqP sz0 {ω | qd2Bad sz0 (1 / 10) (1 / 20) (1 / 10) n ω} ≤ ENNReal.ofReal (Nsz sz0 n ^ (-(2 : ℝ)))) ∧
      ∀ z : ℂ, sz0.locDomain (1 / 10) (1 / 20) n z → ∀ a b : Zd 3 (sz0.L n),
        ‖(∫ ω, avg2 sz0 n (fun x y => ((‖sz0.Gn n z ω x y‖ ^ 2 : ℝ) : ℂ)) a b ∂(Sizes.seqP sz0)) -
            profPM sz0 n z a b‖ ≤ qdBoundExp sz0 n (1 / 10) z.im ∧
        ‖(∫ ω, avg2 sz0 n (fun x y => sz0.Gn n z ω x y * sz0.Gn n z ω y x) a b ∂(Sizes.seqP sz0)) -
            profPP sz0 n z a b‖ ≤ qdBoundExp sz0 n (1 / 10) z.im

-- `inst_zNet`: the grid at `n = 0` (`N = 2097152`), no hypothesis
def inst_zNet_pin : Prop :=
  ∃ S : Finset ℂ, (S.card : ℝ) ≤ 25 * Nsz sz0 0 ^ (14 : ℕ) ∧ (∀ w ∈ S, sz0.locDomain (1 / 10) (1 / 20) 0 w) ∧
    ∀ z : ℂ, sz0.locDomain (1 / 10) (1 / 20) 0 z → ∃ w ∈ S,
      |z.re - w.re| ≤ Nsz sz0 0 ^ (-7 : ℝ) ∧ |z.im - w.im| ≤ Nsz sz0 0 ^ (-7 : ℝ)

end RBM.Endpoints.Inst.T2230Check
