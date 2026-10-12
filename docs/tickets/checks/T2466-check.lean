/-
Release check for T2466 (dispatcher V3, Mon Oct 12 17:08 UTC 2026; DECISIONS §271).  BA-L L4c2 `Graph/BAExp14d`, `BAExp14dB`: the `q ≤ 1` leaf bound for
`n_M = 1` leaves, `BAG5LeafPrec1` = T2464's leaf pin `BAG5LeafPrec` (`T2464-check.lean:338-347`) restricted to `n_M = 1`, which is
`T2465_Q1Need` of L4g's check verbatim up to the name (the `n_M = 1` half of `BAG5LeafPrec`).  Band twin `Graph/LWExpTerm3.lean`
`:384-1228`, `:1426-1661` (the cut of T2464).  Supervisor 0851 Q3 (the pointwise `GtoAG`/`(Gammamuxy)` route for `BAG5Leaf` leaves),
0951 Q3, L4-C8; REQ-0845 `:36`; designs T2398 §5, §7, T2387 §6.
Section 1: merged names only (`main` a1412ad).  Section 2: the targets as Prop pins and shapes.  The rescaled data `DT` (the 1b's
`BAExp14d_dataT`) enters as a variable; its body is pinned in `T2466_dataT_eq` (as `rT0` in T2464-check).  No proofs.
Run: lake env lean docs/tickets/checks/T2466-check.lean
-/
import RBM3D.Graph.BAS3CloseC
import RBM3D.Graph.BAAtom
import RBM3D.Graph.BAAtom2
import RBM3D.Graph.BAAuxGraph2
import RBM3D.Graph.BAAuxGraph2B
import RBM3D.Graph.BASizeClaim2
import RBM3D.Graph.AuxGraph2
import RBM3D.BA.FlowPins
import RBM3D.BA.GreenSchur
import RBM3D.BA.GreenLDE
import RBM3D.BA.Prop5Short
import RBM3D.Graph.LWExpTerm3
import RBM3D.Graph.LWExpTerm6

-- Section 1: merged names
-- L4e-C (T2433, `Graph/BAG5Leaf`): the leaf properties (the hypothesis of the target), the all-`M` leaf (`n_M = 0`, L4g's half)
#check @RBM.Graph.BAG5Tgt
#check @RBM.Graph.BAG5Leaf
#check @RBM.Graph.BAG5Attached
#check @RBM.Graph.BAG5LeafProps
#check @RBM.Graph.BAG5LeafInst.baAllMP
#check @RBM.Graph.BAG5LeafInst.baAllM_leaf
-- L4d2b (T2450): the lists of the leaf census (1a (i)), read only
#check @RBM.Graph.BAS3expandRoot
#check @RBM.Graph.baS3Close_mod
-- vocabulary (`Graph/LWVocab`, `Graph/BAVocab`), graph data of the flow (`Graph/BAExpand`, `Graph/BAExpandW`)
#check @RBM.Graph.WEdge
#check @RBM.Graph.BALData
#check @RBM.Graph.BAGraph
#check @RBM.Graph.BAGraph.val
#check @RBM.Graph.BAGraph.Normal
#check @RBM.Graph.BAGraph.mol
#check @RBM.Graph.BAGraph.atom
#check @RBM.Graph.BAGraph.nM
#check @RBM.Graph.BAGraph.nW
#check @RBM.Graph.BAGraph.nA
#check @RBM.Graph.BAGraph.nS
#check @RBM.Graph.BAGraph.counters
#check @RBM.Graph.BAGraph.scalingOrder
#check @RBM.Graph.BAGraph.scalingSize
#check @RBM.Graph.BAPGraph
#check @RBM.Graph.BAPGraph.val
#check @RBM.Graph.BAPGraph.scalingOrder
#check @RBM.Graph.BAlwData
#check @RBM.Graph.BAlwG
#check @RBM.Graph.BAlwS
#check @RBM.Graph.BAlwW
#check @RBM.Graph.BAlwM
#check @RBM.Graph.lwLift
#check @RBM.Graph.lwBdist
#check @RBM.Graph.LWKBound
#check @RBM.Gauss.svarF
#check @RBM.Gauss.PsiI
#check @RBM.Gauss.Ω
#check @RBM.BA.BATheta
#check @RBM.BA.BAReal
#check @RBM.BA.BASelf
-- L3c2 (T2412, `Graph/BASizeClaim*`): `S W = t · lift(ω)` (target 1), the kernel constants, `C_Γ`, the counters
#check @RBM.Graph.baSp_eq
#check @RBM.Graph.baSpDecay
#check @RBM.Graph.baKBound_E
#check @RBM.Graph.baW_mul
#check @RBM.Graph.BAGraph.sizeConst
#check @RBM.Graph.BAGraph.counters_le
-- `ω = Θ^{(+,+)}`: uniform decay and `ℓ¹` bounds in `t ∈ [0, 1)` (target 2's `S⁺/t`), `S` explicit
#check @RBM.BA.BAProp5s
#check @RBM.BA.baProp5s_holds
#check @RBM.BA.BAExp14a_theta_l1
#check @RBM.BA.BAExp14a_theta_col
#check @RBM.BA.BAExp14a_W_sub_one
#check @RBM.BA.BAExp14a_S_apply
-- L3c1 (T2420, `Graph/BAAtom*`): the auxiliary graph, G3 (`BAGtoAG`, its `hext` unused, `BAAtom2:416`), its public pieces
#check @RBM.Graph.BAGraph.shadow
#check @RBM.Graph.BAGraph.shadow_mol
#check @RBM.Graph.BAGraph.shadow_nM
#check @RBM.Graph.BAGraph.auxVal
#check @RBM.Graph.BAGraph.auxOrd
#check @RBM.Graph.BAGraph.auxVal_nonneg
#check @RBM.Graph.BAGraph.scalingOrder_sub_auxOrd
#check @RBM.Graph.BAGraph.auxOrd_le_scalingOrder
#check @RBM.Graph.BAGraph.molSolid_length_le
#check @RBM.Graph.BAAtom_fJ
#check @RBM.Graph.BAAtom_term_tail
#check @RBM.Graph.BAAtom_main_sum
#check @RBM.Graph.BAAtom_tail_sum
#check @RBM.Graph.BAAtom_decay_E
#check @RBM.Graph.BAGtoAG
#check @RBM.Graph.baGtoAG_holds
#check @RBM.Graph.baGtoAG_E
#check @RBM.Graph.baAtom_offset
#check @RBM.Graph.BAAtom_offdiag_E
-- L3c3a (T2435, `Graph/BAAuxGraph2*`): `ζ`, `(eq:Gbyxi2_BA)` from the entry law alone, its `hξ` form, the Ward row sum
#check @RBM.Graph.baZetaSq
#check @RBM.Graph.baZetaVar
#check @RBM.Graph.baZetaVar_nonneg
#check @RBM.Graph.baZetaVar_symm
#check @RBM.Graph.baZeta_ward_sum
#check @RBM.Graph.BAGbyZetaU
#check @RBM.Graph.BAGbyZeta
#check @RBM.Graph.baGbyZeta_holds
#check @RBM.Graph.baGbyZeta_hxi
#check @RBM.Graph.BAAuxGraph2_whp_entry
#check @RBM.Graph.BAEntryPsi
#check @RBM.Graph.BAAnpAuxG
-- the radii and the tail of the band route (generic)
#check @RBM.Graph.lwTail_log32
#check @RBM.Graph.lwXiRad_holds
#check @RBM.Graph.lwGbyXi_holds
#check @RBM.expC
#check @RBM.zdistD
-- L4a (T2418, `Graph/BAExp14a*`): the slice, `≺ → 𝔼`, the scalars along the flow
#check @RBM.BA.BAExp14a_slc
#check @RBM.BA.BAExp14a_int_slice
#check @RBM.BA.BAExp14a_prec_integral
#check @RBM.BA.BAExp14a_det_iff
#check @RBM.BA.BAExp14a_prec_of_le_ev
#check @RBM.BA.BAExp14a_prec_mono
#check @RBM.BA.BAExp14a_STWB_le
#check @RBM.BA.BAExp14a_eventually
#check @RBM.BA.BAExp14a_eventual_scalars
#check @RBM.BA.BAExp14a_Bctl_le_two
#check @RBM.BA.BAExp14a_Wd_le
#check @RBM.BA.BAExp14a_eta_inv_le
#check @RBM.BA.BAExp14a_eta_pos
#check @RBM.BA.BAExp14a_eta_eq
#check @RBM.BA.BAExp14a_G_le
#check @RBM.BA.BAExp14a_t_lt_one
-- L4d2a (T2445): S3A-C2, S3A-C3 (the arithmetic of target 5)
#check @RBM.BA.twB0_ge_holds
#check @RBM.BA.twEta_ge_holds
-- the carrier, `≺`, the five Step 1/2 pins (inside statement defs only), the flow, the scale facts
#check @RBM.BA.PrecL
#check @RBM.BA.FlowFM.GM
#check @RBM.BA.FlowFM.eta
#check @RBM.BA.STLocalEntrygL
#check @RBM.BA.LWAvgLawgL
#check @RBM.BA.STLmaxgL
#check @RBM.BA.STLKgL
#check @RBM.BA.STDecaygL
#check @RBM.BA.BAFlow
#check @RBM.BA.BAflowT0
#check @RBM.BA.BAflowLam0
#check @RBM.BA.BAflowEs
#check @RBM.BA.baFMz
#check @RBM.BA.ba_G_data
#check @RBM.BA.BAflow_real
#check @RBM.BA.BAflow_lam0_window
#check @RBM.BA.BAflow_T0_bounds
#check @RBM.Gauss.Sizes.Bctl
#check @RBM.Gauss.Sizes.STBctl_pos
#check @RBM.Gauss.Sizes.STBctl_ge
#check @RBM.Gauss.Sizes.expAvg_Bctl_ge
#check @RBM.Gauss.Sizes.lam_sq_mul_pow_ge
#check @RBM.Gauss.Sizes.W_rpow_le
-- the band basis (`Graph/LWExpTerm3` §3 `:384-1228`, `:1426-1661`; the kit `:1229-1425` is L4c1's) and L4g's band pin
#check @RBM.Gauss.Sizes.LWAttached
#check @RBM.Gauss.Sizes.lwExpTerm3_det
#check @RBM.Gauss.Sizes.lwExpTerm3_Sp_decay
#check @RBM.Gauss.Sizes.lwExpTerm3_Data_G
#check @RBM.Gauss.Sizes.lwExpTerm3_Data_M
#check @RBM.Gauss.Sizes.lwExpTerm3_sizeConst_smul
#check @RBM.Gauss.Sizes.lwExpTerm3_entry_whp
#check @RBM.Gauss.Sizes.lwExpTerm3_hent
#check @RBM.Gauss.Sizes.lwExpTerm3_xiSq_nonneg
#check @RBM.Gauss.Sizes.lwExpTerm3_xiVar_sq
#check @RBM.Gauss.Sizes.lwExpTerm3_pathwise
#check @RBM.Gauss.Sizes.lwExpTerm3_Psi_zpow
#check @RBM.Gauss.Sizes.lwExpTerm3_Q_le
#check @RBM.Gauss.Sizes.lwExpTerm3_size_le
#check @RBM.Gauss.Sizes.lwExpTerm3_arith
#check @RBM.Gauss.Sizes.lwExpTerm3_floor
#check @RBM.Gauss.Sizes.lwExpTerm3_etaT_le_one
#check @RBM.Gauss.Sizes.LwGraphPrec1
#check @RBM.Gauss.Sizes.lwGraphPrec1
#check @RBM.Gauss.Sizes.lwExpTerm_prec_integral
#check @RBM.Gauss.Sizes.st6_prec_det_iff
#check @RBM.Gauss.Sizes.LwGraphPrecJoin
-- the `d = 3` instance data (`Defs/Sizes.lean` §Inst, `BA/FlowPins.lean` §Inst)
#check @RBM.Gauss.SizesInst.sz0
#check @RBM.BA.FlowPinsInst.zSeq
#check @RBM.BA.FlowPinsInst.flow_sz0
#check @RBM.BA.FlowPinsInst.half_lt_t0

-- Section 2: the targets (Prop pins) and shapes
noncomputable section

namespace RBM.Graph.T2466Check

open MeasureTheory Filter
open RBM RBM.Loop RBM.Gauss RBM.Gauss.Sizes RBM.Graph RBM.BA

/-! ### Target 1: the rescaled data and the `t`-scaling of a BA graph value -/

section Scale

-- the rescaled data `D'_t` (the 1b's `BAExp14d_dataT`): `S' = S/t`, `S⁺' = S⁺/t`
variable (DT : ∀ (d L W : ℕ) [NeZero L] [NeZero W], ℝ → ℝ → ℝ → ℂ → Ω d L W → BALData (Idx d L W))

/-- Target 1, the rescaled data (`BAExp14d_dataT`, its defining equation `BAExp14d_dataT_eq`): `G`, `M`, `g₀Ψ` of `BAlwData`; `S' = svarF(0)`
(`S = t S'`, `BAlwS`, `BAExpand:75`); `S⁺' = lift(ω_t)`, `ω_t = Θ_t^{(+,+)}` (`S W = t · lift(ω_t)`, `baSp_eq`, `BASizeClaim:180`). -/
def T2466_dataT_eq : Prop :=
  ∀ (d L W : ℕ) [NeZero L] [NeZero W] (g0 E t : ℝ) (m : ℂ) (ω : Ω d L W),
    DT d L W g0 E t m ω =
      ({ G := Matrix.of fun x y => BAlwG d L W g0 E t m ω x y,
         M := BAlwM d L W g0 E m,
         S := Matrix.of fun x y => ((svarF d L W 0 x y : ℝ) : ℂ),
         Sp := lwLift d L W (BATheta d L g0 E m t true true),
         gPsi := (g0 : ℂ) • PsiI d L W } : BALData (Idx d L W))

/-- Target 1, the `t`-scaling (`BAExp14d_val_scale`; the BA form of the `t`-carrying constants of the band, `lwExpTerm3_Sp_decay`,
`lwExpTerm3_sizeConst_smul`, `LWExpTerm3:727, 816`): every waved factor of `BAlwData` at `t` is `t` times that of `D'_t`, so a packed
graph value is `t^{n_W}` times its value at `D'_t`, for all `0 ≤ t < 1` (`t = 0` included). -/
def T2466_val_scale : Prop :=
  ∀ (d L W : ℕ) [NeZero L] [NeZero W], 3 ≤ L → ∀ (g0 κ E t : ℝ) (m : ℂ), BAReal d L g0 κ E m → 0 ≤ t → t < 1 →
    ∀ (ω : Ω d L W) (P : BAPGraph (Fin 2)) (ℓ : Fin 2 → Idx d L W),
      P.val (BAlwData d L W g0 E t m ω) ℓ = (t : ℂ) ^ P.g.nW * P.val (DT d L W g0 E t m ω) ℓ

/-- Target 1, shape. -/
example : Prop := T2466_dataT_eq DT ∧ T2466_val_scale DT

-- Target 7, shape: the `t`-scaling at the `d = 3` data (`sz0`, `zSeq`, `n = 0`, `t = 1/2`).
open RBM.Gauss.SizesInst RBM.BA.FlowPinsInst in
example : Prop :=
  ∀ (ω : sz0.SeqΩ) (P : BAPGraph (Fin 2)) (x y : Idx 3 (sz0.L 0) (sz0.W 0)),
    P.val (BAlwData 3 (sz0.L 0) (sz0.W 0) (BAflowLam0 sz0 zSeq 0) (BAflowEs sz0 zSeq 0) (1 / 2) ((baFMz sz0 zSeq).m 0)
      (BAExp14a_slc sz0 0 ω)) ![x, y] =
    (((1 / 2 : ℝ)) : ℂ) ^ P.g.nW *
      P.val (DT 3 (sz0.L 0) (sz0.W 0) (BAflowLam0 sz0 zSeq 0) (BAflowEs sz0 zSeq 0) (1 / 2) ((baFMz sz0 zSeq).m 0)
        (BAExp14a_slc sz0 0 ω)) ![x, y]

end Scale

/-! ### Target 2: G3 at the rescaled kernels, without `hext` -/

/-- Target 2 (`BAGtoAGT`, `baGtoAGT_holds`; the form of `baGtoAG_E`, `BAAtom2:606`, with `D.S = S'`, `D.S⁺ = lift(ω_t)` and **no
`hext`** (distinct external vertices in distinct molecules): `baGtoAG_holds` does not use it, `BAAtom2:416`).  The constants depend
on `(d, Λ, κ)` only, uniformly in `0 ≤ t < 1`; at these kernels no `t` is lost, target 1 restores `t^{n_W}`. -/
def T2466_BAGtoAGT (d : ℕ) : Prop :=
  3 ≤ d → ∀ Λ κ : ℝ, 0 < Λ → 0 < κ →
    ∃ K₀ K₁ Kd C c : ℝ, 0 < K₀ ∧ 0 < K₁ ∧ 0 ≤ Kd ∧ 0 ≤ C ∧ 0 < c ∧
      ∀ (L W : ℕ) [NeZero L] [NeZero W], 3 ≤ L → ∀ (g0 E t : ℝ) (m : ℂ), 0 < g0 → g0 ≤ Λ →
        BAReal d L g0 κ E m → 0 ≤ t → t < 1 →
        ∀ (E' I' : Type) [Fintype E'] [DecidableEq E'] [Fintype I'] [DecidableEq I'] (Γ : BAGraph E' I'), Γ.Normal →
          ∀ D : BALData (Idx d L W), D.S = Matrix.of (fun x y => ((svarF d L W 0 x y : ℝ) : ℂ)) →
            D.Sp = lwLift d L W (BATheta d L g0 E m t true true) → D.M = BAlwM d L W g0 E m →
            D.gPsi = (g0 : ℂ) • PsiI d L W → ∀ (Ψ A r R : ℝ) (ξ : Zd d L → Zd d L → ℝ),
            (∀ x y, ‖D.G x y - D.M x y‖ ≤ Ψ) → 0 ≤ A → ((W : ℝ) ^ d)⁻¹ ≤ A * Ψ ^ 2 →
            0 ≤ r → (Fintype.card (E' ⊕ I') : ℝ) * r ≤ R → (∀ a b, 0 ≤ ξ a b) →
            (∀ (x y : Idx d L W) (a b : Zd d L), (zdistD d L ((split d L W x).1 - a) : ℝ) ≤ R →
              (zdistD d L ((split d L W y).1 - b) : ℝ) ≤ R → ‖D.G x y - D.M x y‖ ≤ ξ a b) →
            ∀ ℓe : E' → Idx d L W,
              ‖Γ.val D ℓe‖ ≤
                Γ.sizeConst (K₀ * A) K₁ Kd * Ψ ^ (Γ.scalingOrder - Γ.auxOrd) *
                    (((W : ℝ) ^ d) ^ Γ.nM * Γ.auxVal ξ (fun a => (split d L W (ℓe a)).1)) +
                  Real.exp (-(c * r / 2)) * Γ.sizeConst C (C * expC (d - 2) (c / 2)) (C * (1 + expC (d - 2) (c / 2))) *
                    Γ.scalingSize Ψ W d L

/-! ### Target 4: the smallness of `Bctl` along the flow and the entry law -/

/-- Target 4 (`BAExp14d_Bctl_small`; the BA form of the `scaleFacts_R1` input of `lwExpTerm3_hent`, `LWExpTerm3:874`; no BA twin on
`main`, `BAExp14aB:1102`): `W^{-d}B_{t,0} ≤ (λ²W^d)⁻¹ + (N(1-t))⁻¹ ≤ W^{-2𝔡} + 2N^{-ε}` (`lam_sq_mul_pow_ge`, `BAExp14a_one_sub_t`). -/
def T2466_Bctl_small (d : ℕ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z →
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ BAflowT0 sz z n) →
      ∀ᶠ n in atTop, sz.Bctl n (t n) ≤ 2 * ((sz.size n : ℕ) : ℝ) ^ (-c₀)

/-- Target 4 (`BAExp14dEntry`, `baExp14dEntry_holds`; twin of `lwExpTerm3_hent`, `LWExpTerm3:872`): the entry law
`‖G_t - M‖_max ≺ W^{-ε₁}` (the premise of `baGbyZeta_holds`) from `STLocalEntrygL` alone. -/
def T2466_entry (d : ℕ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z →
    ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ BAflowT0 sz z n) →
      STLocalEntrygL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) t →
      ∃ ε₁ : ℝ, 0 < ε₁ ∧
        PrecL sz (Sizes.seqP (sz.withLam 0)) (U := fun n => Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n))
          (fun n p ω => ‖(baFMz sz z).GM n (t n) ω p.1 p.2‖) (fun n _ _ => ((sz.W n : ℕ) : ℝ) ^ (-ε₁))

/-! ### Target 6: the `q ≤ 1` leaf bound for `n_M = 1` leaves (the `n_M = 1` half of T2464's `BAG5LeafPrec`) -/

/-- Target 6 (`BAG5LeafPrec1`, `baG5LeafPrec1_holds`; twin of `LwGraphPrec1`, `LWExpTerm3:1430`): for every `P` with the leaf
properties of `BAG5LeafProps` and `n_M = 1` and every pair `(x, y)`, `‖𝔼 P_{xy}‖ ≺ t^{n_W} η_t⁻¹ Bctl^{ord(P)/2}` at `BAlwData` over the
carrier law, under the five premises of `BAExp14bS3`.  Verbatim up to the name: `T2465_Q1Need` (L4g's check), i.e. `T2464_BAG5LeafPrec`
(`T2464-check.lean:338-347`) with the extra hypothesis `P.g.nM = 1`.  No distinct-molecule hypothesis on `P` (T2465 stop rule S2). -/
def T2466_BAG5LeafPrec1 (d : ℕ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z →
    ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ BAflowT0 sz z n) → let μ := Sizes.seqP (sz.withLam 0)
      STLocalEntrygL (baFMz sz z) μ t → LWAvgLawgL (baFMz sz z) μ t → STLmaxgL (baFMz sz z) μ t → STLKgL (baFMz sz z) μ t →
      STDecaygL (baFMz sz z) μ t →
      ∀ P : BAPGraph (Fin 2), BAG5LeafProps (fun _ _ => [P]) → P.g.nM = 1 →
        PrecL sz μ (U := fun n => Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n))
          (fun n p _ => ‖∫ ω, P.val (BAlwData d (sz.L n) (sz.W n) (BAflowLam0 sz z n) (BAflowEs sz z n) (t n)
            ((baFMz sz z).m n) (BAExp14a_slc sz n ω)) ![p.1, p.2] ∂μ‖)
          (fun n _ _ => (t n) ^ P.g.nW * ((baFMz sz z).eta n (t n))⁻¹ * (sz.Bctl n (t n)) ^ ((P.scalingOrder : ℝ) / 2))

/-- T2464's leaf pin (`T2464_BAG5LeafPrec`, `T2464-check.lean:338-347`), copied verbatim up to the name for the shapes below (an
input of L4g, not a target here). -/
def T2466_BAG5LeafPrec (d : ℕ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z →
    ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ BAflowT0 sz z n) → let μ := Sizes.seqP (sz.withLam 0)
      STLocalEntrygL (baFMz sz z) μ t → LWAvgLawgL (baFMz sz z) μ t → STLmaxgL (baFMz sz z) μ t → STLKgL (baFMz sz z) μ t →
      STDecaygL (baFMz sz z) μ t →
      ∀ P : BAPGraph (Fin 2), BAG5LeafProps (fun _ _ => [P]) →
        PrecL sz μ (U := fun n => Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n))
          (fun n p _ => ‖∫ ω, P.val (BAlwData d (sz.L n) (sz.W n) (BAflowLam0 sz z n) (BAflowEs sz z n) (t n)
            ((baFMz sz z).m n) (BAExp14a_slc sz n ω)) ![p.1, p.2] ∂μ‖)
          (fun n _ _ => (t n) ^ P.g.nW * ((baFMz sz z).eta n (t n))⁻¹ * (sz.Bctl n (t n)) ^ ((P.scalingOrder : ℝ) / 2))

/-! ### Shapes -/

/-- Targets 2, 4, 6 for every `d`. -/
example : Prop :=
  (∀ d : ℕ, T2466_BAGtoAGT d) ∧ (∀ d : ℕ, T2466_Bctl_small d) ∧ (∀ d : ℕ, T2466_entry d) ∧ (∀ d : ℕ, T2466_BAG5LeafPrec1 d)

/-- The split of T2464's pin between L4g and this row: a `BAG5LeafProps` leaf has `n_M = 0` (L4g, `BAGraphPrecJoin`) or `n_M = 1`
(this row).  The pin restricts to this row's target. -/
example : Prop :=
  (∀ P : BAPGraph (Fin 2), BAG5LeafProps (fun _ _ => [P]) → P.g.nM = 0 ∨ P.g.nM = 1) ∧
    ((∀ d : ℕ, T2466_BAG5LeafPrec d) → ∀ d : ℕ, T2466_BAG5LeafPrec1 d)

-- Target 7, shapes: an `n_M = 1` leaf exists (the instance leaf of 1a (i)); target 6 at `d = 3` and the data `sz0`, `zSeq`,
-- `t ≡ 1/2`, with the Step 1/2 pins (other gates') kept as hypotheses.
open RBM.Gauss.SizesInst RBM.BA.FlowPinsInst in
example : Prop :=
  (∃ P : BAPGraph (Fin 2), BAG5LeafProps (fun _ _ => [P]) ∧ P.g.nM = 1) ∧ T2466_BAG5LeafPrec1 3 ∧ T2466_entry 3 ∧
    T2466_BAGtoAGT 3 ∧ STLocalEntrygL (baFMz sz0 zSeq) (Sizes.seqP (sz0.withLam 0)) (fun _ => 1 / 2)

end RBM.Graph.T2466Check

end
