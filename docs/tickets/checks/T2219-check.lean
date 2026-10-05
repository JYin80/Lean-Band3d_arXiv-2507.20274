/-
Release check for T2219 (dispatcher V1, Mon Oct  5 21:40 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §16, §17, §20,
§29, §45 O2, §68 (10)).
MA-02 (main-theorem assembly, gate MA; second proof ticket of the MA split, T2192 portmap P.5 row MA-02):
`RBM3D/Main/ZTransfer.lean`, the `zztE` transfer (`zRange`, `zGreen`, `zLocal`, `zAve`, `zTrace`, `zProfile`) and
`(eq:BtBt)` (`btBt`, scalar core `STWB_compare`), moved verbatim from the T2192 probe
(`git show 97d958e:RBM3D/Probe/T2192Pins.lean`, branch `t/T2192`; design merged report-only at 3429d7d) into the
namespace `RBM.Endpoints` (instances: `RBM.Endpoints.Inst`), on top of the merged MA-01 `RBM3D/Endpoints.lean` (8a43715).
Section 1: the merged names the moved text uses (exact namespaces; file and last commit on `main` 0bc4633).
Section 2: the seven assembly pins of the moved text (probe `def … : Prop`, docstrings stripped), as `*_pin` in the
temporary namespace `RBM.Endpoints.T2219Check`; T2219 defines each in `RBM.Endpoints` under the probe's name.
Section 3: the statements of the seven public lemmas without a pin of their own (`im_identity`, `im_msc_ge`,
`STWB_compare`, `Gres_blockMat'`, `sum_vtx`, `trace_four`, `trace_two`) as `*_pin : Prop`, the probe's binders turned
into `∀` binders, otherwise verbatim (`Gres_blockMat'` is pinned as `Gres_blockMat_pin`).
Section 4: the statements of the six MA-02 instances (probe `:2236-2272`) as `*_pin : Prop` in the temporary namespace
`RBM.Endpoints.Inst.T2219Check`.
Omitted: the private lemmas `inv_le_mul_inv`, `Gres_conjTranspose'` and the re-declared private helpers `W_pos_real`,
`L_pos_real` (the verbatim criterion of the ticket covers them).
Statements and `#check` only: no theorem, no proof.  Never imported or merged.
Imports: `RBM3D.Endpoints` only (its import closure, 40 modules, contains every module of section 1; it equals the
closure of `RBM3D.Universality.Pins` plus `RBM3D.Endpoints`, unchanged since the probe's base 76b840e apart from that
one file); not the probe, not `RBM3D`.  No Mathlib lemma is checked.
Run from the main worktree: `lake env lean docs/tickets/checks/T2219-check.lean`.
-/
import RBM3D.Endpoints

/-! ## 1. Merged names -/

-- `RBM3D/Endpoints.lean` (8a43715, MA-01 = T2210)
#check @RBM.Endpoints.calB
#check @RBM.Endpoints.Mband
#check @RBM.Endpoints.avg2
#check @RBM.Endpoints.ThetaPM
#check @RBM.Endpoints.ThetaPP
#check @RBM.Endpoints.profPM
#check @RBM.Endpoints.profPP
#check @RBM.Endpoints.calB_blk_eq_STWB
#check @RBM.Endpoints.Inst.zI
#check @RBM.Endpoints.Inst.zI_im_pos
#check @RBM.Endpoints.Inst.zI_im_le
#check @RBM.Endpoints.Inst.zI_re_le
-- `RBM3D/Defs/Sizes.lean` (0a873f1)
#check @RBM.Gauss.Sizes
#check @RBM.Gauss.Sizes.L
#check @RBM.Gauss.Sizes.W
#check @RBM.Gauss.Sizes.lam
#check @RBM.Gauss.Sizes.three_le_L
#check @RBM.Gauss.Sizes.W_pos
#check @RBM.Gauss.Idx
#check @RBM.Gauss.split
#check @RBM.Gauss.splitEquiv
#check @RBM.Gauss.Iblk
#check @RBM.Gauss.SizesInst.sz0
-- `RBM3D/Defs/Lattice.lean` (51f1a17)
#check @RBM.Zd
-- `RBM3D/Defs/Params.lean` (c3f3d5d)
#check @RBM.Bparam
-- `RBM3D/Defs/Semicircle.lean` (fbc9870)
#check @RBM.mE
#check @RBM.mE_im
#check @RBM.norm_mE
#check @RBM.mSigma
#check @RBM.msc
#check @RBM.msc_im_pos
#check @RBM.norm_msc_lt_one
#check @RBM.zt
#check @RBM.lemE
#check @RBM.lemT
#check @RBM.norm_msc_pos
#check @RBM.lemT_pos
#check @RBM.lemT_lt_one
#check @RBM.abs_lemE_lt_two
#check @RBM.mE_lemE
#check @RBM.msc_eq_sqrt_mul_mE
#check @RBM.msc_add_eq_neg_inv
#check @RBM.lemma28_quant
-- `RBM3D/Defs/Block.lean` (a722f63)
#check @RBM.SB
#check @RBM.norm_SB
-- `RBM3D/Gauss/Model.lean` (a722f63)
#check @RBM.Gauss.Vtx
-- `RBM3D/Gauss/FineModel.lean` (0a873f1)
#check @RBM.Gauss.Sizes.SeqΩ
#check @RBM.Gauss.Sizes.seqHflow
#check @RBM.Gauss.Sizes.seqHflow_isHermitian
-- `RBM3D/Loop/GLoop.lean` (e0c58e6)
#check @RBM.Gauss.Eblk
-- `RBM3D/Loop/GLoopFlow.lean` (868b3b4)
#check @RBM.Gauss.Gres
#check @RBM.Gauss.loopM
#check @RBM.Gauss.blockMat
#check @RBM.Gauss.loopFine
#check @RBM.Gauss.Sizes.Gt
#check @RBM.Gauss.Sizes.Lloop
#check @RBM.Gauss.Sizes.Gn
#check @RBM.Gauss.Sizes.Gt_lemT
-- `RBM3D/Loop/KLTree.lean` (b06ff9b)
#check @RBM.Loop.KLloopOf
#check @RBM.Loop.KLK_two
-- `RBM3D/Induction/Defs.lean` (64bdfd3)
#check @RBM.Gauss.Sizes.STKloop
#check @RBM.Gauss.Sizes.STWB
#check @RBM.Gauss.Sizes.STGM
-- `RBM3D/Propagator/Basic.lean` (020ec7a)
#check @RBM.Theta
#check @RBM.Theta_transpose
-- namespaces opened in the moved text
open RBM.Loop in
#check @RBM.Loop.KLK_two
open RBM.Gauss.SizesInst RBM.Univ.UNInst in
#check @RBM.Univ.UNInst.bump

/-! ## 2. The seven assembly pins (probe `:492`, `:519`, `:528`, `:582`, `:890`, `:914`, `:993`; docstrings stripped) -/

open MeasureTheory ProbabilityTheory Filter Matrix Topology
open RBM RBM.Gauss RBM.Gauss.Sizes RBM.Univ
open scoped NNReal ENNReal

namespace RBM.Endpoints.T2219Check

-- probe `:492` (`MAZRange`; `zztE`, `1_2:787-795`)
def MAZRange_pin : Prop :=
  ∀ κ : ℝ, 0 < κ → ∀ z : ℂ, 0 < z.im → z.im ≤ 1 → |z.re| ≤ 2 - κ →
    |lemE z| ≤ 2 - κ ∧ (1 / 16 : ℝ) ≤ lemT z ∧ lemT z < 1 ∧
      1 - lemT z = z.im / ((msc z).im + z.im) ∧ z.im / 2 ≤ 1 - lemT z

-- probe `:519` (`MAZGreen`; `(eq:zztE)` third clause, `1_2:792`)
def MAZGreen_pin : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (n : ℕ) (z : ℂ), 0 < z.im → ∀ ω : sz.SeqΩ,
    (Real.sqrt (lemT z) : ℂ) • sz.Gt n (lemE z) (lemT z) true ω = sz.Gn n z ω

-- probe `:528` (`MAZLocal`; `(G_bound)` from `(Gt_bound)`, `1_2:1217`, `1_2:1226`)
def MAZLocal_pin : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (n : ℕ) (z : ℂ), 0 < z.im → ∀ (ω : sz.SeqΩ) (x y : Idx d (sz.L n) (sz.W n)),
    ‖sz.Gn n z ω x y - Mband sz n z x y‖ ^ 2 = lemT z * ‖STGM sz n (lemE z) (lemT z) ω x y‖ ^ 2

-- probe `:582` (`MABtBt`; `(eq:BtBt)`, `1_2:1107-1111`)
def MABtBt_pin : Prop :=
  ∀ {d : ℕ}, 3 ≤ d → ∀ (sz : Sizes d) (n : ℕ) (κ : ℝ), 0 < κ → ∀ z : ℂ, 0 < z.im → z.im ≤ 1 →
    |z.re| ≤ 2 - κ → ∀ k : ℕ,
      STWB sz n (lemT z) k ≤ 2 * calB sz n z.im (((sz.W n : ℕ) : ℝ) * (k : ℝ)) ∧
      (Real.sqrt (κ * (4 - κ)) / 8) * calB sz n z.im (((sz.W n : ℕ) : ℝ) * (k : ℝ)) ≤ STWB sz n (lemT z) k

-- probe `:890` (`MAZAve`; `(G_bound_ave)` from `ML:GLoop` at `n = 1`, `1_2:1226-1229`)
def MAZAve_pin : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (n : ℕ) (z : ℂ), 0 < z.im → ∀ (ω : sz.SeqΩ) (a : Zd d (sz.L n)),
    (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * ∑ x ∈ Iblk d (sz.L n) (sz.W n) a, sz.Gn n z ω x x =
      (Real.sqrt (lemT z) : ℂ) * sz.Lloop n (lemE z) (lemT z) (fun _ : Fin 1 => true) (fun _ => a) ω

-- probe `:914` (`MAZTrace`; `(eq:diffu1)`, `(eq:diffu2)` from `ML:GLoop` at `n = 2`; loop indices `(b, a)`, D506)
def MAZTrace_pin : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (n : ℕ) (z : ℂ), 0 < z.im → ∀ (ω : sz.SeqΩ) (a b : Zd d (sz.L n)),
    avg2 sz n (fun x y => sz.Gn n z ω x y * sz.Gn n z ω y x) a b =
        (lemT z : ℂ) * sz.Lloop n (lemE z) (lemT z) ![true, true] ![b, a] ω ∧
    avg2 sz n (fun x y => ((‖sz.Gn n z ω x y‖ ^ 2 : ℝ) : ℂ)) a b =
        (lemT z : ℂ) * sz.Lloop n (lemE z) (lemT z) ![true, false] ![b, a] ω

-- probe `:988-997` (`MAZProfile`; `(Kn2sol)`, `1_2:1175`)
open scoped Matrix.Norms.Operator in
def MAZProfile_pin : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (n : ℕ) (z : ℂ), 0 < z.im → ∀ a b : Zd d (sz.L n),
    profPM sz n z a b = (lemT z : ℂ) * sz.STKloop n (lemE z) (lemT z) ![true, false] ![b, a] ∧
    profPP sz n z a b = (lemT z : ℂ) * sz.STKloop n (lemE z) (lemT z) ![true, true] ![b, a]

/-! ## 3. The statements of the seven public lemmas without a pin of their own -/

-- statement of `im_identity` (probe `:476`)
def im_identity_pin : Prop :=
  ∀ {z : ℂ}, 0 < z.im →
    z.im * ‖msc z‖ ^ 2 = (msc z).im * (1 - ‖msc z‖ ^ 2)

-- statement of `im_msc_ge` (probe `:548`)
def im_msc_ge_pin : Prop :=
  ∀ {κ : ℝ}, 0 < κ → ∀ {z : ℂ}, 0 < z.im → z.im ≤ 1 →
    |z.re| ≤ 2 - κ → Real.sqrt (κ * (4 - κ)) / 8 ≤ (msc z).im

-- statement of `STWB_compare` (probe `:592`; `d` is auto-bound in the probe, first implicit)
def STWB_compare_pin : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (n : ℕ) {u η C : ℝ}, 0 < η → 0 < u → η ≤ 2 * u →
    1 ≤ C → u ≤ C * η → ∀ k : ℕ,
    STWB sz n (1 - u) k ≤ 2 * STWB sz n (1 - η) k ∧ STWB sz n (1 - η) k ≤ C * STWB sz n (1 - u) k

-- statement of `Gres_blockMat'` (probe `:780`)
def Gres_blockMat_pin : Prop :=
  ∀ {d : ℕ} {L W : ℕ} [NeZero L] [NeZero W]
    (M : Matrix (Idx d L W) (Idx d L W) ℂ) (z : ℂ) (s : Bool),
    Gres (blockMat d L W M) z s =
      (Gres M z s).submatrix (splitEquiv d L W).symm (splitEquiv d L W).symm

-- statement of `sum_vtx` (probe `:792`)
def sum_vtx_pin : Prop :=
  ∀ {d : ℕ} {L W : ℕ} [NeZero L] [NeZero W] (F : Vtx d L W → ℂ),
    ∑ p, F p = ∑ x : Idx d L W, F (splitEquiv d L W x)

-- statement of `trace_four` (probe `:796`)
def trace_four_pin : Prop :=
  ∀ {d : ℕ} {L W : ℕ} [NeZero L] [NeZero W] (P Q : Matrix (Idx d L W) (Idx d L W) ℂ)
    (a b : Zd d L),
    Matrix.trace (P.submatrix (splitEquiv d L W).symm (splitEquiv d L W).symm * Eblk d L W a *
        Q.submatrix (splitEquiv d L W).symm (splitEquiv d L W).symm * Eblk d L W b) =
      (((W : ℂ) ^ d)⁻¹) ^ 2 * ∑ x ∈ Iblk d L W b, ∑ y ∈ Iblk d L W a, P x y * Q y x

-- statement of `trace_two` (probe `:846`)
def trace_two_pin : Prop :=
  ∀ {d : ℕ} {L W : ℕ} [NeZero L] [NeZero W] (P : Matrix (Idx d L W) (Idx d L W) ℂ) (a : Zd d L),
    Matrix.trace (P.submatrix (splitEquiv d L W).symm (splitEquiv d L W).symm * Eblk d L W a) =
      ((W : ℂ) ^ d)⁻¹ * ∑ x ∈ Iblk d L W a, P x x

end RBM.Endpoints.T2219Check

/-! ## 4. The statements of the six MA-02 instances (probe `:2236-2272`; `d = 3`, `sz0`, `n = 0`, `z = zI`) -/

namespace RBM.Endpoints.Inst.T2219Check

open RBM.Gauss.SizesInst RBM.Univ.UNInst

-- statement of `inst_zRange` (probe `:2237`)
def inst_zRange_pin : Prop :=
  |lemE zI| ≤ 2 - 1 / 10 ∧ (1 / 16 : ℝ) ≤ lemT zI ∧ lemT zI < 1 ∧
    1 - lemT zI = zI.im / ((msc zI).im + zI.im) ∧ zI.im / 2 ≤ 1 - lemT zI

-- statement of `inst_btBt` (probe `:2243`)
def inst_btBt_pin : Prop :=
  ∀ k : ℕ,
    STWB sz0 0 (lemT zI) k ≤ 2 * calB sz0 0 zI.im (((sz0.W 0 : ℕ) : ℝ) * (k : ℝ)) ∧
      (Real.sqrt ((1 / 10) * (4 - 1 / 10)) / 8) * calB sz0 0 zI.im (((sz0.W 0 : ℕ) : ℝ) * (k : ℝ)) ≤
        STWB sz0 0 (lemT zI) k

-- statement of `inst_zLocal` (probe `:2250`)
def inst_zLocal_pin : Prop :=
  ∀ (ω : sz0.SeqΩ) (x y : Idx 3 (sz0.L 0) (sz0.W 0)),
    ‖sz0.Gn 0 zI ω x y - Mband sz0 0 zI x y‖ ^ 2 = lemT zI * ‖STGM sz0 0 (lemE zI) (lemT zI) ω x y‖ ^ 2

-- statement of `inst_zAve` (probe `:2255`)
def inst_zAve_pin : Prop :=
  ∀ (ω : sz0.SeqΩ) (a : Zd 3 (sz0.L 0)),
    (((sz0.W 0 : ℕ) : ℂ) ^ 3)⁻¹ * ∑ x ∈ Iblk 3 (sz0.L 0) (sz0.W 0) a, sz0.Gn 0 zI ω x x =
      (Real.sqrt (lemT zI) : ℂ) * sz0.Lloop 0 (lemE zI) (lemT zI) (fun _ : Fin 1 => true) (fun _ => a) ω

-- statement of `inst_zTrace` (probe `:2261`)
def inst_zTrace_pin : Prop :=
  ∀ (ω : sz0.SeqΩ) (a b : Zd 3 (sz0.L 0)),
    avg2 sz0 0 (fun x y => sz0.Gn 0 zI ω x y * sz0.Gn 0 zI ω y x) a b =
        (lemT zI : ℂ) * sz0.Lloop 0 (lemE zI) (lemT zI) ![true, true] ![b, a] ω ∧
    avg2 sz0 0 (fun x y => ((‖sz0.Gn 0 zI ω x y‖ ^ 2 : ℝ) : ℂ)) a b =
        (lemT zI : ℂ) * sz0.Lloop 0 (lemE zI) (lemT zI) ![true, false] ![b, a] ω

-- statement of `inst_zProfile` (probe `:2269`)
def inst_zProfile_pin : Prop :=
  ∀ a b : Zd 3 (sz0.L 0),
    profPM sz0 0 zI a b = (lemT zI : ℂ) * sz0.STKloop 0 (lemE zI) (lemT zI) ![true, false] ![b, a] ∧
    profPP sz0 0 zI a b = (lemT zI : ℂ) * sz0.STKloop 0 (lemE zI) (lemT zI) ![true, true] ![b, a]

end RBM.Endpoints.Inst.T2219Check
