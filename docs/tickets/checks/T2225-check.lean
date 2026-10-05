/-
Release check for T2225 (dispatcher V1, Mon Oct  5 22:25 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §16, §17, §20,
§29, §45 O2, §64 (4), §68 (10)).
MA-03 (main-theorem assembly, gate MA; third proof ticket of the MA split, T2192 portmap P.5 row MA-03):
`RBM3D/Main/FixedZ.lean`, the fixed-`z` statements `locSCFixed`, `QDiffFixed` from `UNMLOut` (`locSCFixed_of_ML`,
`QDiffFixed_of_ML`, `fixed_of_ML`) and `decol` from `locSC` (`decol_of_locSC`), moved verbatim from the T2192 probe
(`git show 97d958e:RBM3D/Probe/T2192Pins.lean`, branch `t/T2192`; design merged report-only at 3429d7d) into the
namespace `RBM.Endpoints` (instances: `RBM.Endpoints.Inst`), on top of the merged MA-01 `RBM3D/Endpoints.lean` (8a43715)
and MA-02 `RBM3D/Main/ZTransfer.lean` (afdb81e).
Section 1: the merged names the moved text uses (exact namespaces; file and last commit on `main` afdb81e).
Section 2: the four pins of the moved text (probe `def … : Prop`, docstrings stripped), as `*_pin` in the temporary
namespace `RBM.Endpoints.T2225Check`; T2225 defines each in `RBM.Endpoints` under the probe's name.  `MAFixed_pin`
refers to `locSCFixed_pin`, `QDiffFixed_pin` where the probe has `locSCFixed`, `QDiffFixed` (not merged yet).
Section 3: the statements of the 18 public theorems that are not instances, as `*_pin : Prop`, the probe's binders
turned into `∀` binders (section variable `{d : ℕ}` first where the probe's section adds it), otherwise verbatim
(`zdistInf_neg'` is pinned as `zdistInf_neg_pin`).  The three spectral lemmas and `prob_union_le` are stated for
`Type` (universe 0) where the probe has `Type*`; the equality examples instantiate the probe's universe there.
Section 4: the statements of the four MA-03 instances (probe `:2207`, `:2215`, `:2224`, `:2454`) as `*_pin : Prop` in
the temporary namespace `RBM.Endpoints.Inst.T2225Check`.
Statements and `#check` only: no theorem, no proof.  Never imported or merged.
Imports: `RBM3D.Main.ZTransfer` and `RBM3D.Green.LDE` (the latter for `RBM.Green.tendsto_W`); their joint import closure
(55 modules) is unchanged since the probe's base 76b840e apart from `RBM3D/Endpoints.lean` and
`RBM3D/Main/ZTransfer.lean`; not the probe, not `RBM3D`.  No Mathlib lemma is checked.
Run from the main worktree: `lake env lean docs/tickets/checks/T2225-check.lean`.
-/
import RBM3D.Main.ZTransfer
import RBM3D.Green.LDE

/-! ## 1. Merged names -/

-- `RBM3D/Main/ZTransfer.lean` (afdb81e, MA-02 = T2219)
#check @RBM.Endpoints.zLocal
#check @RBM.Endpoints.btBt
#check @RBM.Endpoints.zAve
#check @RBM.Endpoints.zTrace
#check @RBM.Endpoints.zProfile
-- `RBM3D/Endpoints.lean` (8a43715, MA-01 = T2210)
#check @RBM.Endpoints.calB
#check @RBM.Endpoints.distB
#check @RBM.Endpoints.Mband
#check @RBM.Endpoints.avg2
#check @RBM.Endpoints.profPM
#check @RBM.Endpoints.profPP
#check @RBM.Endpoints.qdBound
#check @RBM.Endpoints.qdBoundExp
#check @RBM.Endpoints.decolBad
#check @RBM.Endpoints.locBad1z
#check @RBM.Endpoints.locBad2z
#check @RBM.Endpoints.qd1Badz
#check @RBM.Endpoints.qd2Badz
#check @RBM.Endpoints.locBad1
#check @RBM.Endpoints.decol
#check @RBM.Endpoints.locSC
#check @RBM.Endpoints.inv_size_mul_le_calB
#check @RBM.Endpoints.calB_nonneg
#check @RBM.Endpoints.explicit_of_prec
#check @RBM.Endpoints.eventually_forall_of_sections
#check @RBM.Endpoints.det_of_prec
#check @RBM.Endpoints.STWB_nonneg
#check @RBM.Endpoints.Nsz_pos
#check @RBM.Endpoints.locDomain_im_pos
#check @RBM.Endpoints.locDomain_nonempty
#check @RBM.Endpoints.locDomain_empty_kappa
#check @RBM.Endpoints.locDomain_empty_eps
-- `RBM3D/Green/LDE.lean` (7c7652e)
#check @RBM.Green.tendsto_W
-- `RBM3D/Universality/Pins.lean` (f8ad4b4)
#check @RBM.Univ.IsOrthoEigenbasis
#check @RBM.Univ.Nsz
#check @RBM.Univ.UNMLOut
-- `RBM3D/Defs/Sizes.lean` (0a873f1)
#check @RBM.Gauss.Idx
#check @RBM.Gauss.Iblk
#check @RBM.Gauss.zdistInf
#check @RBM.Gauss.Sizes
#check @RBM.Gauss.Sizes.size
#check @RBM.Gauss.Sizes.Admissible
#check @RBM.Gauss.Sizes.locDomain
#check @RBM.Gauss.Sizes.lam_sq_mul_pow_ge
#check @RBM.Gauss.Sizes.Bctl
#check @RBM.Gauss.Sizes.size_rpow_le_W_rpow
#check @RBM.Gauss.SizesInst.sz0
#check @RBM.Gauss.SizesInst.sz0_admissible
-- `RBM3D/Defs/StochDomAt.lean` (9e2b00f)
#check @RBM.Gauss.Sizes.one_le_size
-- `RBM3D/Defs/Lattice.lean` (51f1a17)
#check @RBM.zdist
#check @RBM.zdist_neg
#check @RBM.Zd
-- `RBM3D/Defs/Params.lean` (c3f3d5d)
#check @RBM.ellT
#check @RBM.Bparam
-- `RBM3D/Defs/Tail.lean` (c8e4f17)
#check @RBM.ellT_nonneg
-- `RBM3D/Defs/Semicircle.lean` (fbc9870)
#check @RBM.mE
#check @RBM.mSigma
#check @RBM.msc
#check @RBM.norm_msc_lt_one
#check @RBM.lemE
#check @RBM.lemT
#check @RBM.lemT_pos
#check @RBM.lemT_lt_one
#check @RBM.msc_eq_sqrt_mul_mE
-- `RBM3D/Gauss/FineModel.lean` (0a873f1)
#check @RBM.Gauss.Sizes.SeqΩ
#check @RBM.Gauss.Sizes.seqP
#check @RBM.Gauss.Sizes.seqXmat
-- `RBM3D/Loop/GLoopFlow.lean` (868b3b4)
#check @RBM.Gauss.Gres
#check @RBM.Gauss.Sizes.Lloop
#check @RBM.Gauss.Sizes.Gn
-- `RBM3D/Loop/KLTree.lean` (b06ff9b)
#check @RBM.Loop.KLloopOf
#check @RBM.Loop.KLK_one
-- `RBM3D/Loop/TreeRep.lean` (b06ff9b)
#check @RBM.Loop.LoopIdx
-- `RBM3D/Induction/Defs.lean` (64bdfd3)
#check @RBM.Gauss.Sizes.STKloop
#check @RBM.Gauss.Sizes.STWB
#check @RBM.Gauss.Sizes.STblk
#check @RBM.Gauss.Sizes.STGM
#check @RBM.Gauss.Sizes.STflowE
#check @RBM.Gauss.Sizes.STFlow
-- namespaces opened in the moved text
open RBM.Loop in
#check @RBM.Loop.KLK_one
open RBM.Gauss.SizesInst RBM.Univ.UNInst in
#check @RBM.Gauss.SizesInst.sz0_admissible

/-! ## 2. The four pins (probe `:1070`, `:1078`, `:1092`, `:1843`; docstrings stripped) -/

open MeasureTheory ProbabilityTheory Filter Matrix Topology
open RBM RBM.Gauss RBM.Gauss.Sizes RBM.Univ
open scoped NNReal ENNReal

namespace RBM.Endpoints.T2225Check

-- probe `:1070` (`locSCFixed`; `(G_bound)`, `(G_bound_ave)` at each fixed `z`, `1_2:388-391`, `1_2:1228`; D500)
def locSCFixed_pin : Prop :=
  ∀ d : ℕ, 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 →
    ∀ κ ε τ D : ℝ, 0 < κ → 0 < ε → 0 < τ → 0 < D → ∀ᶠ n in atTop, ∀ z : ℂ, sz.locDomain κ ε n z →
      Sizes.seqP sz {ω | locBad1z sz τ n z ω} ≤ ENNReal.ofReal (Nsz sz n ^ (-D)) ∧
      Sizes.seqP sz {ω | locBad2z sz τ n z ω} ≤ ENNReal.ofReal (Nsz sz n ^ (-D))

-- probe `:1078` (`QDiffFixed`; `(eq:diffu1,2)` `1_2:494-498` at each fixed `z`, `(Meq:QdS1,2)` `1_2:504-507`; D500, D503)
def QDiffFixed_pin : Prop :=
  ∀ d : ℕ, 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 →
    ∀ κ ε τ D : ℝ, 0 < κ → 0 < ε → 0 < τ → 0 < D → ∀ᶠ n in atTop, ∀ z : ℂ, sz.locDomain κ ε n z →
      (Sizes.seqP sz {ω | qd1Badz sz τ n z ω} ≤ ENNReal.ofReal (Nsz sz n ^ (-D)) ∧
       Sizes.seqP sz {ω | qd2Badz sz τ n z ω} ≤ ENNReal.ofReal (Nsz sz n ^ (-D))) ∧
      ∀ a b : Zd d (sz.L n),
        ‖(∫ ω, avg2 sz n (fun x y => ((‖sz.Gn n z ω x y‖ ^ 2 : ℝ) : ℂ)) a b ∂(Sizes.seqP sz)) -
            profPM sz n z a b‖ ≤ qdBoundExp sz n τ z.im ∧
        ‖(∫ ω, avg2 sz n (fun x y => sz.Gn n z ω x y * sz.Gn n z ω y x) a b ∂(Sizes.seqP sz)) -
            profPP sz n z a b‖ ≤ qdBoundExp sz n τ z.im

-- probe `:1092` (`MAFixed`; `1_2:1226-1228`, the flow outputs `UNMLOut` as hypothesis)
def MAFixed_pin : Prop := (∀ d : ℕ, UNMLOut d) → locSCFixed_pin ∧ QDiffFixed_pin

-- probe `:1843` (`MADecol`; Thm 2.1 `1_2:357-370` from Thm 2.2 by `(eq:ukx)` `1_2:399`; D502)
def MADecol_pin : Prop := locSC → decol

/-! ## 3. The statements of the 18 public theorems that are not instances -/

-- statement of `Bctl_nonneg` (probe `:1137`)
def Bctl_nonneg_pin : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (n : ℕ) (t : ℝ), 0 ≤ sz.Bctl n t

-- statement of `STKloop_one` (probe `:1143-1144`)
def STKloop_one_pin : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (n : ℕ) (E t : ℝ) (a : Zd d (sz.L n)),
    sz.STKloop n E t (fun _ : Fin 1 => true) (fun _ => a) = mE E

-- statement of `locSCFixed_of_ML` (probe `:1156`)
def locSCFixed_of_ML_pin : Prop := (∀ d : ℕ, UNMLOut d) → locSCFixed_pin

-- statement of `zdistInf_neg'` (probe `:1272`; the probe binds its own `d`)
def zdistInf_neg_pin : Prop :=
  ∀ (d L : ℕ) [NeZero L] (x : Zd d L), zdistInf d L (-x) = zdistInf d L x

-- statement of `floor_X` (probe `:1278-1280`)
def floor_X_pin : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (n : ℕ), 2 ≤ d → ∀ {𝔠 η K : ℝ}, 0 < 𝔠 →
    ((sz.size n : ℕ) : ℝ) ^ 𝔠 ≤ (sz.W n : ℝ) → 0 < η → η ≤ 1 → 0 ≤ K →
    ((sz.W n : ℕ) : ℝ) ^ (-(6 / (5 * 𝔠))) ≤ calB sz n η 0 ^ ((1 : ℝ) / 5) * calB sz n η K

-- statement of `qd_core` (probe `:1315-1323`)
def qd_core_pin : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (n : ℕ), 3 ≤ d → ∀ {𝔠 κ τ e Δ : ℝ}, 0 < 𝔠 → 0 < κ →
    ((sz.size n : ℕ) : ℝ) ^ 𝔠 ≤ (sz.W n : ℝ) → ∀ {z : ℂ}, 0 < z.im → z.im ≤ 1 →
    |z.re| ≤ 2 - κ → 5 ≤ ((sz.W n : ℕ) : ℝ) ^ (τ / 2) → ∀ (a b : Zd d (sz.L n)),
    0 ≤ Δ → 0 ≤ e → e ≤ 1 →
    Δ ≤ ((sz.W n : ℕ) : ℝ) ^ (τ / 2) *
      (sz.Bctl n (lemT z) ^ ((1 : ℝ) / 5) * STWB sz n (lemT z) (zdistInf d (sz.L n) (b - a)) * e +
        ((sz.W n : ℕ) : ℝ) ^ (-(6 / (5 * 𝔠)))) →
    Δ ≤ ((sz.W n : ℕ) : ℝ) ^ (τ / 2) * sz.Bctl n (lemT z) ^ 2 →
    lemT z * Δ ≤ qdBound sz n τ z.im a b

-- statement of `prob_union_le` (probe `:1401-1403`; `Type` for the probe's `Type*`)
def prob_union_le_pin : Prop :=
  ∀ {Ω U : Type} [MeasurableSpace Ω] (P : Measure Ω) (w : ℝ) {ξ ζ₁ ζ₂ : U → Ω → ℝ} {Bad : Set Ω}
    {δ : ENNReal}, P {ω | ∃ u, w * ζ₁ u ω < ξ u ω} ≤ δ → P {ω | ∃ u, w * ζ₂ u ω < ξ u ω} ≤ δ →
    (∀ ω, (∀ u, ξ u ω ≤ w * ζ₁ u ω) → (∀ u, ξ u ω ≤ w * ζ₂ u ω) → ω ∉ Bad) → P Bad ≤ δ + δ

-- statement of `two_rpow_le` (probe `:1414-1415`)
def two_rpow_le_pin : Prop :=
  ∀ {N D : ℝ}, 2 ≤ N →
    ENNReal.ofReal (N ^ (-(D + 1))) + ENNReal.ofReal (N ^ (-(D + 1))) ≤ ENNReal.ofReal (N ^ (-D))

-- statement of `qd_exp_core` (probe `:1429-1433`)
def qd_exp_core_pin : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (n : ℕ), 3 ≤ d → ∀ {κ τ Δ : ℝ}, 0 < κ → ∀ {z : ℂ}, 0 < z.im →
    z.im ≤ 1 → |z.re| ≤ 2 - κ → 8 ≤ ((sz.W n : ℕ) : ℝ) ^ (τ / 2) → 0 ≤ Δ →
    Δ ≤ ((sz.W n : ℕ) : ℝ) ^ (τ / 2) * (sz.Bctl n (lemT z) ^ 2 *
      ((sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d) ^ (-(1 / 5 : ℝ)) + sz.Bctl n (lemT z))) →
    lemT z * Δ ≤ qdBoundExp sz n τ z.im

-- statement of `QDiffFixed_of_ML` (probe `:1475`)
def QDiffFixed_of_ML_pin : Prop := (∀ d : ℕ, UNMLOut d) → QDiffFixed_pin

-- statement of `fixed_of_ML` (probe `:1594`)
def fixed_of_ML_pin : Prop := MAFixed_pin

-- statement of `Gres_apply_self` (probe `:1603-1604` section variables, `:1608-1610`; `Type` for `Type*`)
def Gres_apply_self_pin : Prop :=
  ∀ {ι : Type} [Fintype ι] [DecidableEq ι] {H : Matrix ι ι ℂ} {μ : ι → ℝ} {ψ : ι → ι → ℂ},
    IsOrthoEigenbasis H μ ψ → ∀ {z : ℂ}, (∀ l, (μ l : ℂ) ≠ z) → ∀ x : ι,
    Gres H z true x x = ∑ l, (Complex.normSq (ψ l x) : ℂ) / ((μ l : ℂ) - z)

-- statement of `ukx` (probe `:1603-1604` section variables, `:1652-1653`; `Type` for `Type*`; `(eq:ukx)` `1_2:399`)
def ukx_pin : Prop :=
  ∀ {ι : Type} [Fintype ι] [DecidableEq ι] {H : Matrix ι ι ℂ} {μ : ι → ℝ} {ψ : ι → ι → ℂ},
    IsOrthoEigenbasis H μ ψ → ∀ {η : ℝ}, 0 < η → ∀ (k x : ι),
    ‖ψ k x‖ ^ 2 ≤ η * (Gres H ((μ k : ℂ) + η * Complex.I) true x x).im

-- statement of `zdistInf_zero` (probe `:1689`; the probe binds its own `d`)
def zdistInf_zero_pin : Prop :=
  ∀ (d L : ℕ), zdistInf d L 0 = 0

-- statement of `decol_scalars` (probe `:1695-1699`)
def decol_scalars_pin : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) {𝔠 𝔡 : ℝ}, 2 ≤ d → sz.Admissible 𝔠 𝔡 → ∀ {τ : ℝ}, 0 < τ →
    ∀ᶠ n in atTop,
      ((sz.W n : ℕ) : ℝ) ^ (min 𝔡 ((d : ℝ) * min (τ / 2) (1 / 2) / 2)) *
          calB sz n (Nsz sz n ^ (-1 + min (τ / 2) (1 / 2))) 0 ≤ 1 ∧
        2 * Nsz sz n ^ (-1 + min (τ / 2) (1 / 2)) ≤ Nsz sz n ^ (-1 + τ)

-- statement of `decol_spectral_core` (probe `:1789-1792`; `Type` for `Type*`)
def decol_spectral_core_pin : Prop :=
  ∀ {ι : Type} [Fintype ι] [DecidableEq ι] {H : Matrix ι ι ℂ} {μ : ι → ℝ} {ψ : ι → ι → ℂ},
    IsOrthoEigenbasis H μ ψ → ∀ {η CM B : ℝ}, 0 < η → ∀ {k x : ι} {M : ℂ},
    ‖Gres H ((μ k : ℂ) + η * Complex.I) true x x - M‖ ≤ 1 → M.im ≤ CM →
    η * (CM + 1) ≤ B → ‖ψ k x‖ ^ 2 ≤ B

-- statement of `decol_core` (probe `:1806-1809`; the hypothesis `¬ locBad1 …` is the reason for the registry line)
def decol_core_pin : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) {κ ε τ τL : ℝ} (n : ℕ) (ω : sz.SeqΩ), ε ≤ 1 →
    ¬ locBad1 sz κ ε τL n ω →
    ((sz.W n : ℕ) : ℝ) ^ τL * calB sz n (Nsz sz n ^ (-1 + ε)) 0 ≤ 1 →
    2 * Nsz sz n ^ (-1 + ε) ≤ Nsz sz n ^ (-1 + τ) → ¬ decolBad sz n κ τ ω

-- statement of `decol_of_locSC` (probe `:1845`)
def decol_of_locSC_pin : Prop := MADecol_pin

example : Prop := MAFixed_pin ∧ MADecol_pin

end RBM.Endpoints.T2225Check

/-! ## 4. The four MA-03 instances (probe `:2207`, `:2215`, `:2224`, `:2454`) -/

namespace RBM.Endpoints.Inst.T2225Check

open RBM.Gauss.SizesInst RBM.Univ.UNInst

-- probe `:2207-2209` (`inst_decol_of_locSC`)
def inst_decol_of_locSC_pin : Prop :=
  locSC →
    ∀ᶠ n in atTop, Sizes.seqP sz0 {ω | decolBad sz0 n (1 / 10) (1 / 10) ω} ≤
      ENNReal.ofReal (Nsz sz0 n ^ (-(1 : ℝ)))

-- probe `:2215-2218` (`inst_locSCFixed`)
def inst_locSCFixed_pin : Prop :=
  (∀ d : ℕ, UNMLOut d) →
    ∀ᶠ n in atTop, ∀ z : ℂ, sz0.locDomain (1 / 10) (1 / 20) n z →
      Sizes.seqP sz0 {ω | locBad1z sz0 (1 / 10) n z ω} ≤ ENNReal.ofReal (Nsz sz0 n ^ (-(2 : ℝ))) ∧
      Sizes.seqP sz0 {ω | locBad2z sz0 (1 / 10) n z ω} ≤ ENNReal.ofReal (Nsz sz0 n ^ (-(2 : ℝ)))

-- probe `:2224-2232` (`inst_QDiffFixed`)
def inst_QDiffFixed_pin : Prop :=
  (∀ d : ℕ, UNMLOut d) →
    ∀ᶠ n in atTop, ∀ z : ℂ, sz0.locDomain (1 / 10) (1 / 20) n z →
      (Sizes.seqP sz0 {ω | qd1Badz sz0 (1 / 10) n z ω} ≤ ENNReal.ofReal (Nsz sz0 n ^ (-(2 : ℝ))) ∧
       Sizes.seqP sz0 {ω | qd2Badz sz0 (1 / 10) n z ω} ≤ ENNReal.ofReal (Nsz sz0 n ^ (-(2 : ℝ)))) ∧
      ∀ a b : Zd 3 (sz0.L n),
        ‖(∫ ω, avg2 sz0 n (fun x y => ((‖sz0.Gn n z ω x y‖ ^ 2 : ℝ) : ℂ)) a b ∂(Sizes.seqP sz0)) -
            profPM sz0 n z a b‖ ≤ qdBoundExp sz0 n (1 / 10) z.im ∧
        ‖(∫ ω, avg2 sz0 n (fun x y => sz0.Gn n z ω x y * sz0.Gn n z ω y x) a b ∂(Sizes.seqP sz0)) -
            profPP sz0 n z a b‖ ≤ qdBoundExp sz0 n (1 / 10) z.im

-- probe `:2454-2457` (`inst_decol_scalars`)
def inst_decol_scalars_pin : Prop :=
  ∀ᶠ n in atTop, ((sz0.W n : ℕ) : ℝ) ^ (min (1 / 10 : ℝ) (((3 : ℕ) : ℝ) * min ((1 / 10 : ℝ) / 2) (1 / 2) / 2)) *
      calB sz0 n (Nsz sz0 n ^ (-1 + min ((1 / 10 : ℝ) / 2) (1 / 2))) 0 ≤ 1 ∧
    2 * Nsz sz0 n ^ (-1 + min ((1 / 10 : ℝ) / 2) (1 / 2)) ≤ Nsz sz0 n ^ (-1 + (1 / 10 : ℝ))

end RBM.Endpoints.Inst.T2225Check
