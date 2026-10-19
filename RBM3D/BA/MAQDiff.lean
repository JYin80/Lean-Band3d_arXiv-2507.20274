/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.BA.MAPins
import RBM3D.BA.MALocal
import RBM3D.BA.MainIndTermBA
import RBM3D.BA.KInduct
import RBM3D.BA.KBase
import RBM3D.BA.MReg
import RBM3D.BA.Ward
import RBM3D.BA.RandomLayerBGBA
import RBM3D.BA.ConArg
import RBM3D.Main.FixedZ
import RBM3D.Main.ZTransfer
import RBM3D.Main.ZNet

/-!
# `QDiff` at the block Anderson model from `UNMLOutBA d`

Theorem 2.7 (`MR:decol_BA`): the QDiff statement of Theorem 2.5 (`MR:QuDiff`) at the block Anderson model, that is `(eq:diffu1)`, `(eq:diffu2)` (2.22), (2.23) and
`(Meq:QdS1)`, `(Meq:QdS2)` (2.24), (2.25).  Law `Sizes.seqP (sz.withLam 0)`, matrix `sz.seqHBA`, ρ-bulk `BAbulk`, carrier `baFMz`, profile `BAprof` =
`W^{-d}(ΘM)^{(+,σ)}` at `z`.  The statements `BAEnd_QDiffL`, `BAQDiffFixed`, `BAMANetQD`, `BAMAFixed` and the vocabulary `BAprof`, `BAqdBadz`, `BAendDom`, `BAGz`
are read from `BA/MAPins` by name; this file has no public definition.

* Section 1, `baTrace2`, `baProfile_eq`: the transfer along the block Anderson flow (analogues of `zTrace`, `zProfile` of `Main/ZTransfer`):
  `tr(G E_b G^σ E_a) = t₀ 𝓛^{(2)}_{t₀,(+,σ),(b,a)}` pathwise (`Gt_BA`, `BAzztE_data`, Lemma 8.1 `zztE_BA`), and `BAprof sz n (z n) true σ a b =
  t₀ 𝒦^{(2)}_{t₀,(+,σ),(b,a)}` (`(Kn2sol)` is `baKsol_two` at the `BAReal` datum of `BAdom_real` with `κ := Im m`; `PropThetaQ (Q z) 1 = BATheta λ₀ E m₀ t₀`
  because `Q(z) = t₀ Q₀`; `Θ Q` is symmetric by `BATheta_isSymm`, `BATheta_resolvent`).
* Section 2 (private): the deterministic comparisons `t₀ Δ ≤ qdBound`, `t₀ Δ ≤ qdBoundExp` at a flow time `t₀ ≤ 1` (analogues of `qd_core`, `qd_exp_core` of
  `Main/FixedZ`; the constants of `(eq:BtBt)` are the hypotheses `MALocal_STWB_le`, `MALocal_Bctl_le`), and a deterministic `≺` at the law
  `seqP (sz.withLam 0)` is a deterministic bound (analogue of `det_of_prec`, `Endpoints`).
* Section 3, `baQDiffFixed_of_ML`: `BAQDiffFixed d` from conjuncts 1 (`k = 2`), 3, 4 of `UNMLOutBA d` (analogue of `QDiffFixed_of_ML`, `Main/FixedZ`;
  the sections lemma runs over the chain domain, as in `baLocSCFixed_of_ML`).
* Section 4, `baProf_lip`: `|Δ BAprof| ≤ 12 κ'⁻² (1 + κ'⁻²) η⁻² |z - w| W^{-d}` on the ρ-bulk, every `d`, `sz`, `n`.  Proof outline: Ward rows give
  `‖Q(z)‖_{∞→∞} = t₀ < 1`, Neumann gives `‖Θ‖_{∞→∞} ≤ (1 - t₀)⁻¹ ≤ 2/η`, `ΘQ = Θ - 1`, `Θ - Θ' = Θ (Q - Q') Θ'`, `‖Q - Q'‖_{∞→∞} ≤ 2 ‖M - M'‖_{ℓ²op}`
  (Cauchy-Schwarz on the columns), `‖M - M'‖_{ℓ²op} ≤ κ'⁻² (1 + κ'⁻²) |z - w|`.  This argument gives the constant `8 κ'⁻² (1 + κ'⁻²)`; the statement carries `12`.
* Section 5: the private cover lemma for both `σ` (analogues of `qd1Bad_net`, `qd2Bad_net` of `Main/ZNet`) and `baMANetQD` (analogue of `netQD`), over the net of
  `BA/MALocal` (mesh `N^{-7}`, at most `(4R + 2) N^{14}` points; the extra threshold is `C ≤ N` for the constant `C` of `baProf_lip`).
* Section 6: `baEnd_QDiffL`.

`baEnd_QDiffL` takes `UNMLOutBA d` as a hypothesis.  It is supplied at every `d ≥ 3` by `unMLOutBA_of_famStep` applied to
`baMainIndFamTL_any` and `baStep5III_holds_any`.

Reached by `open private`: `Gres_conjTranspose'` (`Main/ZTransfer`), `ConArg_seqHflowBA_isHermitian` (`BA/ConArg`), `znet_qd_core`, `znet_sq_diff`,
`znet_prod_diff`, `znet_c4` (`Main/ZNet`), `MALocal_kappa_floor`, `MALocal_endDom_dom`, `MALocal_endDom_im_pos`, `MALocal_geom`, `MALocal_thresholds`,
`MALocal_net_exists`, `MALocal_card_le`, `MALocal_net_count`, `MALocal_Gres_lip` (`BA/MALocal`).
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open MeasureTheory Filter Topology
open scoped ENNReal Matrix

noncomputable section

namespace RBM.BA

open RBM RBM.Loop RBM.Gauss RBM.Gauss.Sizes RBM.Univ RBM.Endpoints

/-! ## 1. The transfer `G(z) = √t₀ G_{t₀}` of the two-loop averages and of the profile `BAprof` -/

section Transfer

open private Gres_conjTranspose' from RBM3D.Main.ZTransfer
open private ConArg_seqHflowBA_isHermitian from RBM3D.BA.ConArg

/-- The flow data at `z n` with `Im z_n > 0` (`BAzztE_data`, (8.2) `eq:zztE_BA`): `t₀ ∈ (0, 1)`, `m_F = m(z)/√t₀`, `z_{t₀} = √t₀ z`, `√t₀ M_F = M(z)`. -/
private theorem MAQDiff_flow {d : ℕ} (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ) (hz : 0 < (z n).im) :
    0 < BAflowT0 sz z n ∧ BAflowT0 sz z n < 1 ∧
      BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n =
        BAm d (sz.L n) (sz.lam n) (z n) / (Real.sqrt (BAflowT0 sz z n) : ℂ) ∧
      ztOf (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) (BAflowEs sz z n) (BAflowT0 sz z n) =
        (Real.sqrt (BAflowT0 sz z n) : ℂ) * z n ∧
      (Real.sqrt (BAflowT0 sz z n) : ℂ) • BAMB d (sz.L n) (BAflowLam0 sz z n) ((BAflowEs sz z n : ℝ) : ℂ)
          (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) =
        BAMB d (sz.L n) (sz.lam n) (z n) (BAm d (sz.L n) (sz.lam n) (z n)) := by
  obtain ⟨ht0, ht1, hselfF, hzt, hMB⟩ := BAzztE_data d (sz.L n) (sz.lam n) hz
    (BAm_self d (sz.L n) (sz.lam n) (z n) hz)
  have hmF : BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n =
      BAm d (sz.L n) (sz.lam n) (z n) / (Real.sqrt (BAflowT0 sz z n) : ℂ) :=
    BAm_real_eq_of_self d (sz.L n) _ _ _ hselfF
  refine ⟨ht0, ht1, hmF, ?_, ?_⟩
  · rw [hmF]; exact hzt
  · rw [hmF]; exact hMB

/-- `baTrace2` (analogue of `zTrace`, `Main/ZTransfer`; loop indices `(b, a)`): pathwise, `tr(G E_b G^σ E_a) = t₀ 𝓛^{(2)}_{t₀,(+,σ),(b,a)}`
at `t₀ = BAflowT0`, carrier `baFMz` (`Gt_BA`, `BAzztE_data`, `BASelf_unique`; the unitary-conjugate `G^- = (G^+)^*`). -/
theorem baTrace2 {d : ℕ} (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ) (hz : 0 < (z n).im) (ω : sz.SeqΩ) (a b : Zd d (sz.L n)) :
    avg2 sz n (fun x y => BAGz sz n (z n) ω x y * BAGz sz n (z n) ω y x) a b =
        (BAflowT0 sz z n : ℂ) *
          BALloop sz (BAflowLam0 sz z) (BAflowEs sz z) n (BAflowT0 sz z n) ![true, true] ![b, a] ω ∧
      avg2 sz n (fun x y => ((‖BAGz sz n (z n) ω x y‖ ^ 2 : ℝ) : ℂ)) a b =
        (BAflowT0 sz z n : ℂ) *
          BALloop sz (BAflowLam0 sz z) (BAflowEs sz z) n (BAflowT0 sz z n) ![true, false] ![b, a] ω := by
  obtain ⟨ht0, ht1, hmF, hzt, -⟩ := MAQDiff_flow sz z n hz
  have h1 := Gt_BA sz (BAflowLam0 sz z) n (m0 := BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n)
    (E := BAflowEs sz z n) (t0 := BAflowT0 sz z n) hz ht0 rfl hzt ω
  set t0 := BAflowT0 sz z n with ht0def
  set H := sz.seqHflowBA (BAflowLam0 sz z) n t0 ω with hH
  set zt := ztOf (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) (BAflowEs sz z n) t0 with hztdef
  have hs : (Real.sqrt t0 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (Real.sqrt_pos.2 ht0).ne'
  have hs2 : (Real.sqrt t0 : ℂ) * (Real.sqrt t0 : ℂ) = (t0 : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt ht0.le]
  have hHerm : H.IsHermitian := ConArg_seqHflowBA_isHermitian sz _ n _ ω
  have hGt : ∀ x y : Idx d (sz.L n) (sz.W n), Gres H zt true x y = ((Real.sqrt t0 : ℂ))⁻¹ * BAGz sz n (z n) ω x y := by
    intro x y
    have := congrFun (congrFun h1 x) y
    rw [Matrix.smul_apply, smul_eq_mul] at this
    change _ * Gres H zt true x y = BAGz sz n (z n) ω x y at this
    rw [← this]
    field_simp
  have hGf : ∀ x y : Idx d (sz.L n) (sz.W n), Gres H zt false y x = star (Gres H zt true x y) := by
    intro x y
    have h := congrFun (congrFun (Gres_conjTranspose' hHerm zt true) y) x
    simpa [Matrix.conjTranspose_apply] using h.symm
  have hcore : ∀ (σ : Bool) (F : Idx d (sz.L n) (sz.W n) → Idx d (sz.L n) (sz.W n) → ℂ),
      (∀ x y, Gres H zt true x y * Gres H zt σ y x = ((t0 : ℂ))⁻¹ * F x y) →
      avg2 sz n F a b = (t0 : ℂ) * BALloop sz (BAflowLam0 sz z) (BAflowEs sz z) n t0 ![true, σ] ![b, a] ω := by
    intro σ F hF
    unfold BALloop loopFine loopM
    simp only [List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, mul_one]
    have e0 : (![true, σ] : Fin 2 → Bool) 0 = true := rfl
    have e1 : (![true, σ] : Fin 2 → Bool) (Fin.succ 0) = σ := rfl
    have f0 : (![b, a] : Fin 2 → Zd d (sz.L n)) 0 = b := rfl
    have f1 : (![b, a] : Fin 2 → Zd d (sz.L n)) (Fin.succ 0) = a := rfl
    rw [e0, e1, f0, f1, Gres_blockMat', Gres_blockMat', ← Matrix.mul_assoc, trace_four]
    unfold avg2
    have ht : (t0 : ℂ) ≠ 0 := by exact_mod_cast ht0.ne'
    have hrw : ∀ x y : Idx d (sz.L n) (sz.W n), (Gres H zt true) x y * (Gres H zt σ) y x = (t0 : ℂ)⁻¹ * F x y := hF
    rw [← hH, ← hztdef]
    simp only [hrw]
    simp only [← Finset.mul_sum]
    field_simp
  refine ⟨hcore true _ ?_, hcore false _ ?_⟩
  · intro x y
    rw [hGt x y, hGt y x]
    have : (((Real.sqrt t0 : ℂ))⁻¹ * ((Real.sqrt t0 : ℂ))⁻¹) = (t0 : ℂ)⁻¹ := by
      rw [← mul_inv, hs2]
    calc (((Real.sqrt t0 : ℂ))⁻¹ * BAGz sz n (z n) ω x y) * (((Real.sqrt t0 : ℂ))⁻¹ * BAGz sz n (z n) ω y x)
        = (((Real.sqrt t0 : ℂ))⁻¹ * ((Real.sqrt t0 : ℂ))⁻¹) * (BAGz sz n (z n) ω x y * BAGz sz n (z n) ω y x) := by ring
      _ = (t0 : ℂ)⁻¹ * (BAGz sz n (z n) ω x y * BAGz sz n (z n) ω y x) := by rw [this]
  · intro x y
    rw [hGf x y, hGt x y]
    have hsr : star (((Real.sqrt t0 : ℂ))⁻¹ * BAGz sz n (z n) ω x y) =
        ((Real.sqrt t0 : ℂ))⁻¹ * star (BAGz sz n (z n) ω x y) := by
      rw [star_mul, Complex.star_def, map_inv₀, Complex.conj_ofReal]
      ring
    rw [hsr]
    have : (((Real.sqrt t0 : ℂ))⁻¹ * ((Real.sqrt t0 : ℂ))⁻¹) = (t0 : ℂ)⁻¹ := by
      rw [← mul_inv, hs2]
    have hn : BAGz sz n (z n) ω x y * star (BAGz sz n (z n) ω x y) = ((‖BAGz sz n (z n) ω x y‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    calc (((Real.sqrt t0 : ℂ))⁻¹ * BAGz sz n (z n) ω x y) *
          (((Real.sqrt t0 : ℂ))⁻¹ * star (BAGz sz n (z n) ω x y))
        = (((Real.sqrt t0 : ℂ))⁻¹ * ((Real.sqrt t0 : ℂ))⁻¹) *
            (BAGz sz n (z n) ω x y * star (BAGz sz n (z n) ω x y)) := by ring
      _ = (t0 : ℂ)⁻¹ * ((‖BAGz sz n (z n) ω x y‖ ^ 2 : ℝ) : ℂ) := by rw [this, hn]

/-- A real scalar passes through `M(σ)`. -/
private theorem MAQDiff_Msigma_smul {d L : ℕ} [NeZero L] (s : ℝ) (M : Matrix (Zd d L) (Zd d L) ℂ) (σ : Bool) :
    BAMsigma d L ((s : ℂ) • M) σ = (s : ℂ) • BAMsigma d L M σ := by
  cases σ
  · simp [BAMsigma, Matrix.conjTranspose_smul]
  · simp [BAMsigma]

/-- `M^{(+,σ)}(√t₀ M) = t₀ M^{(+,σ)}(M)` for the flow scalar. -/
private theorem MAQDiff_Mss_smul {d L : ℕ} [NeZero L] (s : ℝ) (M : Matrix (Zd d L) (Zd d L) ℂ) (σ₁ σ₂ : Bool) :
    BAMss d L ((s : ℂ) • M) σ₁ σ₂ = ((s * s : ℝ) : ℂ) • BAMss d L M σ₁ σ₂ := by
  ext a b
  simp only [BAMss, Matrix.of_apply, MAQDiff_Msigma_smul, Matrix.smul_apply, smul_eq_mul, Complex.ofReal_mul]
  ring

/-- `Θ_1(c Q) = Θ_c(Q)`: the propagator at `t = 1` of a scaled matrix. -/
private theorem MAQDiff_Theta_smul {d L : ℕ} [NeZero L] (c : ℝ) (Q : Matrix (Zd d L) (Zd d L) ℂ) :
    PropThetaQ ((c : ℂ) • Q) 1 = PropThetaQ Q c := by
  unfold PropThetaQ
  simp

/-- `baProfile_eq` (analogue of `zProfile`, `Main/ZTransfer`; loop indices `(b, a)`): the end profile `BAprof` at `z_n` is
`t₀ 𝒦^{(2)}_{t₀,(+,σ),(b,a)}` of the block Anderson carrier: `(Kn2sol)` (`baKsol_two`) at the `BAReal` datum of `BAdom_real` with `κ := Im m`, the transfer
`PropThetaQ (Q z) 1 = BATheta λ₀ E m₀ t₀` (`BAzztE_data`, clause 5, `Q(z) = t₀ Q₀`), and the symmetry of `Θ Q` (`BATheta_isSymm`, `BATheta_resolvent`).
`0 < sz.lam n` is eventual from `(eq:WO)`. -/
theorem baProfile_eq {d : ℕ} (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ) (hz : 0 < (z n).im) (hl : 0 < sz.lam n) (σ : Bool)
    (a b : Zd d (sz.L n)) :
    BAprof sz n (z n) true σ a b =
      (BAflowT0 sz z n : ℂ) * BAKloop sz (BAflowLam0 sz z) (BAflowEs sz z) n (BAflowT0 sz z n) ![true, σ] ![b, a] := by
  obtain ⟨ht0, ht1, hmF, -, hMB⟩ := MAQDiff_flow sz z n hz
  have hm := BAm_self d (sz.L n) (sz.lam n) (z n) hz
  have hr : BAReal d (sz.L n) (BAflowLam0 sz z n) (BAm d (sz.L n) (sz.lam n) (z n)).im (BAflowEs sz z n)
      (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) := by
    rw [hmF]; exact BAdom_real hz hm le_rfl
  have hg : 0 < BAflowLam0 sz z n := mul_pos (Real.sqrt_pos.2 ht0) hl
  have hκ : 0 < (BAm d (sz.L n) (sz.lam n) (z n)).im := hm.1
  have hK := baKsol_two d hκ hg (sz.three_le_L n) (sz.W n) hr (t := BAflowT0 sz z n) ⟨ht0.le, ht1⟩ ![true, σ] ![b, a]
  set t0 := BAflowT0 sz z n with ht0def
  set Q0 := BAMss d (sz.L n) (BAMB d (sz.L n) (BAflowLam0 sz z n) ((BAflowEs sz z n : ℝ) : ℂ)
    (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n)) true σ with hQ0
  have hQ : BAMss d (sz.L n) (BAMB d (sz.L n) (sz.lam n) (z n) (BAm d (sz.L n) (sz.lam n) (z n))) true σ =
      (t0 : ℂ) • Q0 := by
    rw [← hMB, MAQDiff_Mss_smul, Real.mul_self_sqrt ht0.le]
  have hres := (BATheta_resolvent d (sz.L n) (BAflowLam0 sz z n) _ (BAflowEs sz z n) _ hr t0 ht0.le ht1 true σ).2
  have hsymm := BATheta_isSymm d (sz.L n) (BAflowLam0 sz z n) _ (BAflowEs sz z n) _ hr t0 ht0.le ht1 true σ
  have hXsym : (BATheta d (sz.L n) (BAflowLam0 sz z n) (BAflowEs sz z n)
        (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) t0 true σ * Q0) b a =
      (BATheta d (sz.L n) (BAflowLam0 sz z n) (BAflowEs sz z n)
        (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) t0 true σ * Q0) a b := by
    have h1 := congrFun (congrFun hres a) b
    have h2 := congrFun (congrFun hres b) a
    have h3 := congrFun (congrFun hsymm a) b
    simp only [Matrix.transpose_apply] at h3
    have e : (1 : Matrix (Zd d (sz.L n)) (Zd d (sz.L n)) ℂ) a b = (1 : Matrix (Zd d (sz.L n)) (Zd d (sz.L n)) ℂ) b a := by
      simp [Matrix.one_apply, eq_comm]
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] at h1 h2
    have htc : (t0 : ℂ) ≠ 0 := by exact_mod_cast ht0.ne'
    refine mul_left_cancel₀ htc ?_
    linear_combination (-1 : ℂ) * h2 + h1 + h3 + e
  have hKl : BAKloop sz (BAflowLam0 sz z) (BAflowEs sz z) n t0 ![true, σ] ![b, a] =
      (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * (BATheta d (sz.L n) (BAflowLam0 sz z n) (BAflowEs sz z n)
        (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) t0 true σ * Q0) b a := hK
  rw [hKl]
  unfold BAprof
  rw [hQ, MAQDiff_Theta_smul, Matrix.mul_smul, Matrix.smul_apply, smul_eq_mul]
  change (t0 : ℂ) * (BATheta d (sz.L n) (BAflowLam0 sz z n) (BAflowEs sz z n)
        (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) t0 true σ * Q0) a b / ((sz.W n : ℕ) : ℂ) ^ d = _
  rw [hXsym]
  ring


end Transfer

/-! ## 2. The deterministic comparisons at `t₀ = BAflowT0`, and a deterministic `≺` is a deterministic bound -/

section Compare

variable {d : ℕ}

/-- The deterministic comparison of the probability halves at a flow time `t₀ ≤ 1` (analogue of `qd_core`, `Main/FixedZ`): if
`Δ = ‖𝓛^{(2)} - 𝒦^{(2)}‖` satisfies the two bounds of `(Eq:Gdecay)` (2.75) (additive `W^{-6/(5𝔠)}`) and of `(Eq:L-KGt)` (2.73) at `k = 2`, both at the scale `W^{τ/2}`,
and the `B`-constants satisfy `(eq:BtBt)` with the constant `2` (`MALocal_STWB_le`, `MALocal_Bctl_le`), then `t₀ Δ ≤ W^τ [𝓑_{η,0}^{1/5} 𝓑_{η,W|a-b|} ∧ 𝓑_{η,0}²]`
(the floor `floor_X`, `min (2 a X, a Y) ≤ 2 a min (X, Y)`). -/
private theorem MAQDiff_qd_core (sz : Sizes d) (n : ℕ) (hd : 3 ≤ d) {𝔠 τ e Δ t₀ : ℝ} (h𝔠 : 0 < 𝔠)
    (hb : ((sz.size n : ℕ) : ℝ) ^ 𝔠 ≤ (sz.W n : ℝ)) {z : ℂ} (hz : 0 < z.im) (hz1 : z.im ≤ 1)
    (hW : 5 ≤ ((sz.W n : ℕ) : ℝ) ^ (τ / 2)) (a b : Zd d (sz.L n))
    (hΔ : 0 ≤ Δ) (he0 : 0 ≤ e) (he1 : e ≤ 1) (ht1 : t₀ ≤ 1)
    (hSB0 : sz.Bctl n t₀ ≤ 2 * calB sz n z.im 0)
    (hSBk : STWB sz n t₀ (zdistInf d (sz.L n) (b - a)) ≤
      2 * calB sz n z.im (((sz.W n : ℕ) : ℝ) * ((zdistInf d (sz.L n) (b - a) : ℕ) : ℝ)))
    (h1 : Δ ≤ ((sz.W n : ℕ) : ℝ) ^ (τ / 2) *
      (sz.Bctl n t₀ ^ ((1 : ℝ) / 5) * STWB sz n t₀ (zdistInf d (sz.L n) (b - a)) * e +
        ((sz.W n : ℕ) : ℝ) ^ (-(6 / (5 * 𝔠)))))
    (h2 : Δ ≤ ((sz.W n : ℕ) : ℝ) ^ (τ / 2) * sz.Bctl n t₀ ^ 2) :
    t₀ * Δ ≤ qdBound sz n τ z.im a b := by
  have hd2 : 2 ≤ d := by omega
  have hW0 : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  set w := ((sz.W n : ℕ) : ℝ) ^ (τ / 2) with hw
  have hwpos : 0 < w := by linarith
  set B0 := calB sz n z.im 0 with hB0
  have hB0n : 0 ≤ B0 := calB_nonneg sz n hz le_rfl
  set k := zdistInf d (sz.L n) (b - a) with hk
  have hkab : zdistInf d (sz.L n) (b - a) = zdistInf d (sz.L n) (a - b) := by
    rw [← neg_sub a b, zdistInf_neg']
  have hdist : distB sz n a b = ((sz.W n : ℕ) : ℝ) * (k : ℝ) := by
    unfold distB
    rw [hk, hkab]
  have hdist0 : 0 ≤ distB sz n a b := by unfold distB; positivity
  set Bk := calB sz n z.im (distB sz n a b) with hBkdef
  have hBk : 0 ≤ Bk := calB_nonneg sz n hz hdist0
  have hSB0 : sz.Bctl n t₀ ≤ 2 * B0 := hSB0
  have hSBk : STWB sz n t₀ k ≤ 2 * Bk := by
    rw [hBkdef, hdist]; exact hSBk
  have hfl := floor_X sz n hd2 h𝔠 hb hz hz1 hdist0
  have hBc : 0 ≤ sz.Bctl n t₀ := Bctl_nonneg sz n _
  have hSTn : 0 ≤ STWB sz n t₀ k := STWB_nonneg sz n _ _
  have hBc15 : sz.Bctl n t₀ ^ ((1 : ℝ) / 5) ≤ 2 * B0 ^ ((1 : ℝ) / 5) := by
    calc sz.Bctl n t₀ ^ ((1 : ℝ) / 5) ≤ (2 * B0) ^ ((1 : ℝ) / 5) :=
          Real.rpow_le_rpow hBc hSB0 (by norm_num)
      _ = (2 : ℝ) ^ ((1 : ℝ) / 5) * B0 ^ ((1 : ℝ) / 5) := Real.mul_rpow (by norm_num) hB0n
      _ ≤ 2 * B0 ^ ((1 : ℝ) / 5) := by
          have h2' : (2 : ℝ) ^ ((1 : ℝ) / 5) ≤ 2 := by
            calc (2 : ℝ) ^ ((1 : ℝ) / 5) ≤ (2 : ℝ) ^ (1 : ℝ) :=
                  Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
              _ = 2 := Real.rpow_one 2
          exact mul_le_mul_of_nonneg_right h2' (Real.rpow_nonneg hB0n _)
  set X := B0 ^ ((1 : ℝ) / 5) * Bk with hX
  have hX0 : 0 ≤ X := mul_nonneg (Real.rpow_nonneg hB0n _) hBk
  have hterm : sz.Bctl n t₀ ^ ((1 : ℝ) / 5) * STWB sz n t₀ k * e ≤ 4 * X := by
    calc sz.Bctl n t₀ ^ ((1 : ℝ) / 5) * STWB sz n t₀ k * e
        ≤ sz.Bctl n t₀ ^ ((1 : ℝ) / 5) * STWB sz n t₀ k * 1 :=
          mul_le_mul_of_nonneg_left he1 (mul_nonneg (Real.rpow_nonneg hBc _) hSTn)
      _ = sz.Bctl n t₀ ^ ((1 : ℝ) / 5) * STWB sz n t₀ k := mul_one _
      _ ≤ (2 * B0 ^ ((1 : ℝ) / 5)) * (2 * Bk) :=
          mul_le_mul hBc15 hSBk hSTn (by positivity)
      _ = 4 * X := by rw [hX]; ring
  have h1' : Δ ≤ w * (5 * X) := by
    calc Δ ≤ w * (sz.Bctl n t₀ ^ ((1 : ℝ) / 5) * STWB sz n t₀ k * e +
          ((sz.W n : ℕ) : ℝ) ^ (-(6 / (5 * 𝔠)))) := h1
      _ ≤ w * (4 * X + X) := mul_le_mul_of_nonneg_left (add_le_add hterm hfl) hwpos.le
      _ = w * (5 * X) := by ring
  have hY : sz.Bctl n t₀ ^ 2 ≤ 4 * B0 ^ 2 := by
    have := pow_le_pow_left₀ hBc hSB0 2
    calc sz.Bctl n t₀ ^ 2 ≤ (2 * B0) ^ 2 := this
      _ = 4 * B0 ^ 2 := by ring
  have h2' : Δ ≤ w * (4 * B0 ^ 2) := h2.trans (mul_le_mul_of_nonneg_left hY hwpos.le)
  have hmin : Δ ≤ w * (5 * min X (B0 ^ 2)) := by
    rcases le_total X (B0 ^ 2) with h | h
    · rw [min_eq_left h]; exact h1'
    · rw [min_eq_right h]
      refine h2'.trans (mul_le_mul_of_nonneg_left ?_ hwpos.le)
      nlinarith [sq_nonneg B0]
  have hm0 : 0 ≤ min X (B0 ^ 2) := le_min hX0 (sq_nonneg _)
  have hWτ : ((sz.W n : ℕ) : ℝ) ^ τ = w * w := by
    rw [hw, ← Real.rpow_add hW0]; congr 1; ring
  calc t₀ * Δ ≤ Δ := mul_le_of_le_one_left hΔ ht1
    _ ≤ w * (5 * min X (B0 ^ 2)) := hmin
    _ ≤ w * (w * min X (B0 ^ 2)) := by
        apply mul_le_mul_of_nonneg_left _ hwpos.le
        exact mul_le_mul_of_nonneg_right hW hm0
    _ = ((sz.W n : ℕ) : ℝ) ^ τ * min X (B0 ^ 2) := by rw [hWτ]; ring
    _ = qdBound sz n τ z.im a b := by
        unfold qdBound
        rfl


/-- The deterministic comparison of the expectation halves at a flow time `t₀ ≤ 1` (analogue of `qd_exp_core`, `Main/FixedZ`): `t₀ Δ ≤ qdBoundExp`
from `Δ ≤ W^{τ/2} 𝓑_{t₀,0}²((λ² W^d)^{-1/5} + 𝓑_{t₀,0})` (`(Eq:Gtlp_exp)` (2.76)) and `(eq:BtBt)` with the constant `2` (`8 ≤ W^{τ/2}`). -/
private theorem MAQDiff_qd_exp_core (sz : Sizes d) (n : ℕ) {τ Δ t₀ : ℝ} {z : ℂ} (hz : 0 < z.im)
    (hW : 8 ≤ ((sz.W n : ℕ) : ℝ) ^ (τ / 2)) (hΔ : 0 ≤ Δ) (ht1 : t₀ ≤ 1)
    (hSB0 : sz.Bctl n t₀ ≤ 2 * calB sz n z.im 0)
    (h : Δ ≤ ((sz.W n : ℕ) : ℝ) ^ (τ / 2) * (sz.Bctl n t₀ ^ 2 *
      ((sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d) ^ (-(1 / 5 : ℝ)) + sz.Bctl n t₀))) :
    t₀ * Δ ≤ qdBoundExp sz n τ z.im := by
  have hW0 : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  set w := ((sz.W n : ℕ) : ℝ) ^ (τ / 2) with hw
  have hwpos : 0 < w := by linarith
  set B0 := calB sz n z.im 0 with hB0
  have hB0n : 0 ≤ B0 := calB_nonneg sz n hz le_rfl
  have hSB0 : sz.Bctl n t₀ ≤ 2 * B0 := hSB0
  have hBc : 0 ≤ sz.Bctl n t₀ := Bctl_nonneg sz n _
  set E := (sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d) ^ (-(1 / 5 : ℝ)) with hE
  have hE0 : 0 ≤ E := Real.rpow_nonneg (by positivity) _
  have hY : sz.Bctl n t₀ ^ 2 ≤ 4 * B0 ^ 2 := by
    have := pow_le_pow_left₀ hBc hSB0 2
    calc sz.Bctl n t₀ ^ 2 ≤ (2 * B0) ^ 2 := this
      _ = 4 * B0 ^ 2 := by ring
  have hZ : sz.Bctl n t₀ ^ 2 * (E + sz.Bctl n t₀) ≤ 8 * (B0 ^ 2 * (E + B0)) := by
    have h1 : sz.Bctl n t₀ ^ 2 * (E + sz.Bctl n t₀) ≤ 4 * B0 ^ 2 * (E + 2 * B0) :=
      mul_le_mul hY (by linarith) (by positivity) (by positivity)
    nlinarith [mul_nonneg (sq_nonneg B0) hE0, mul_nonneg (sq_nonneg B0) hB0n]
  have hm0 : 0 ≤ B0 ^ 2 * (E + B0) := by positivity
  have hWτ : ((sz.W n : ℕ) : ℝ) ^ τ = w * w := by
    rw [hw, ← Real.rpow_add hW0]; congr 1; ring
  have hexp : (-(1 : ℝ) / 5) = -(1 / 5 : ℝ) := by ring
  calc t₀ * Δ ≤ Δ := mul_le_of_le_one_left hΔ ht1
    _ ≤ w * (sz.Bctl n t₀ ^ 2 * (E + sz.Bctl n t₀)) := h
    _ ≤ w * (8 * (B0 ^ 2 * (E + B0))) := mul_le_mul_of_nonneg_left hZ hwpos.le
    _ ≤ w * (w * (B0 ^ 2 * (E + B0))) := by
        apply mul_le_mul_of_nonneg_left _ hwpos.le
        exact mul_le_mul_of_nonneg_right hW hm0
    _ = ((sz.W n : ℕ) : ℝ) ^ τ * B0 ^ 2 * (E + B0) := by rw [hWτ]; ring
    _ = qdBoundExp sz n τ z.im := by
        unfold qdBoundExp
        rw [hexp]


/-- A deterministic `≺` is a deterministic bound at any probability law (analogue of `det_of_prec`, `Endpoints`, which is stated for the band
law `seqP sz`; here `PrecL sz μ` with `μ = seqP (sz.withLam 0)`, a probability measure by `isProbabilityMeasure_seqP`): the expectation half of the
fixed-`z` statement (`STExp2gL` has a left side that does not depend on `ω`): `μ univ = 1 > N^{-1}`, so for `N > 1` the bad set is empty. -/
private theorem MAQDiff_det_of_precL (sz : Sizes d) (μ : Measure sz.SeqΩ) [IsProbabilityMeasure μ] (hsz : sz.SizeTendsto)
    {U : ℕ → Type*} {ξ ζ : ∀ n, U n → sz.SeqΩ → ℝ} (hξ : ∀ n u ω ω', ξ n u ω = ξ n u ω')
    (hζ : ∀ n u ω ω', ζ n u ω = ζ n u ω') (h : PrecL sz μ ξ ζ) {τ : ℝ} (hτ : 0 < τ) :
    ∀ᶠ n in atTop, ∀ u ω, ξ n u ω ≤ ((sz.size n : ℕ) : ℝ) ^ τ * ζ n u ω := by
  filter_upwards [h τ hτ 1 one_pos, hsz.eventually_gt_atTop 1] with n hn hN1
  intro u ω
  by_contra hlt
  push Not at hlt
  have huniv : badSetAt sz.size ξ ζ τ n = Set.univ := by
    ext ω'
    simp only [Set.mem_univ, iff_true]
    exact ⟨u, by rw [hζ n u ω' ω, hξ n u ω' ω]; exact hlt⟩
  rw [huniv, measure_univ] at hn
  have hlt1 : ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-(1 : ℝ))) < 1 := by
    rw [ENNReal.ofReal_lt_one]
    have : ((sz.size n : ℕ) : ℝ) ^ (-(1 : ℝ)) = (((sz.size n : ℕ) : ℝ))⁻¹ := Real.rpow_neg_one _
    rw [this]
    exact inv_lt_one_of_one_lt₀ hN1
  exact absurd hn (not_le.mpr hlt1)

end Compare

/-! ## 3. The fixed-`z` statement of `QDiff` from `UNMLOutBA d` -/

section Fixed

variable {d : ℕ}

open private MALocal_kappa_floor MALocal_endDom_dom MALocal_endDom_im_pos from RBM3D.BA.MALocal

/-- `0 < λ_n` eventually (`(eq:WO)` (2.10): `W^{-d/2 + 𝔡} ≤ λ_n`). -/
private theorem MAQDiff_lam_pos {𝔠 𝔡 : ℝ} (sz : Sizes d) (hA : sz.Admissible 𝔠 𝔡) : ∀ᶠ n in atTop, 0 < sz.lam n := by
  filter_upwards [hA.2.2.2.2] with n h
  exact lt_of_lt_of_le (Real.rpow_pos_of_pos (by exact_mod_cast sz.W_pos n) _) h.1

/-- `baQDiffFixed_of_ML` (analogue of `QDiffFixed_of_ML`, `Main/FixedZ`): the fixed-`z` statements `(eq:diffu1)`, `(eq:diffu2)`, `(Meq:QdS1)`, `(Meq:QdS2)`
at the block Anderson model from conjuncts 1 (`k = 2`), 3, 4 of `UNMLOutBA d` at `t = BAflowT0`: the sections lemma over the chain domain `BAdom κ_f ε` (`κ_f = min κ' c`, as
in `baLocSCFixed_of_ML`), the transfer `baTrace2`, `baProfile_eq` (loop indices `(b, a)`), the comparisons `MAQDiff_qd_core`, `MAQDiff_qd_exp_core`, the form
bridge `explicit_of_stochDomAt` at `τ/2` and `MAQDiff_det_of_precL` at `𝔠 τ/2`, the union bound with `D + 1`. -/
theorem baQDiffFixed_of_ML (d : ℕ) (hML : UNMLOutBA d) : BAQDiffFixed d := by
  intro hd 𝔠 𝔡 sz hA κ ε τ D hκ hε hτ hD
  have hA' := hA
  obtain ⟨h𝔠, h𝔡, hsz, hbw, hWO⟩ := hA'
  by_cases hε1 : ε ≤ 1
  swap
  · filter_upwards [hsz.eventually_gt_atTop 1] with n hn z hz
    exfalso
    have h1 := Real.one_lt_rpow hn (by linarith [not_le.1 hε1] : 0 < -1 + ε)
    have h2 := hz.2.1
    have h3 := hz.2.2
    exact absurd (lt_of_lt_of_le h1 (h2.trans h3)) (lt_irrefl _)
  obtain ⟨c₁, hc₁, hc₁I⟩ := MALocal_kappa_floor hA
  have hκ' : 0 < (Real.pi * κ) ^ 5 / 2048 := by positivity
  set κf : ℝ := min ((Real.pi * κ) ^ 5 / 2048) c₁ with hκfdef
  have hκf : 0 < κf := lt_min hκ' hc₁
  have hne : ∀ n, Nonempty {z : ℂ // BAdom d (sz.L n) (sz.size n) (sz.lam n) κf ε z} := fun n =>
    ⟨⟨Complex.I, (min_le_right _ _).trans (hc₁I n), by
      simp only [Complex.I_im]
      have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
      exact Real.rpow_le_one_of_one_le_of_nonpos hN1 (by linarith), by simp⟩⟩
  have hτ2 : 0 < τ / 2 := half_pos hτ
  have hD1 : 0 < D + 1 := by linarith
  have hD'' : 0 < 6 / (5 * 𝔠) := by positivity
  have hW8 : ∀ᶠ n in atTop, (8 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) ^ (τ / 2) :=
    ((tendsto_rpow_atTop hτ2).comp (RBM.Green.tendsto_W sz h𝔠 hsz hbw)).eventually_ge_atTop 8
  have hN2 : ∀ᶠ n in atTop, (2 : ℝ) ≤ Nsz sz n := hsz.eventually_ge_atTop 2
  have hlam := MAQDiff_lam_pos sz hA
  refine (eventually_forall_of_sections hne (Q := fun n z =>
      (Sizes.seqP (sz.withLam 0) {ω | BAqdBadz sz τ n z.1 ω false} ≤ ENNReal.ofReal (Nsz sz n ^ (-D)) ∧
        Sizes.seqP (sz.withLam 0) {ω | BAqdBadz sz τ n z.1 ω true} ≤ ENNReal.ofReal (Nsz sz n ^ (-D))) ∧
      ∀ a b : Zd d (sz.L n),
        ‖(∫ ω, avg2 sz n (fun x y => ((‖BAGz sz n z.1 ω x y‖ ^ 2 : ℝ) : ℂ)) a b ∂(Sizes.seqP (sz.withLam 0))) -
            BAprof sz n z.1 true false a b‖ ≤ qdBoundExp sz n τ z.1.im ∧
        ‖(∫ ω, avg2 sz n (fun x y => BAGz sz n z.1 ω x y * BAGz sz n z.1 ω y x) a b ∂(Sizes.seqP (sz.withLam 0))) -
            BAprof sz n z.1 true true a b‖ ≤ qdBoundExp sz n τ z.1.im) ?_).mono
    fun n hn z hz => hn ⟨z, ⟨(min_le_left _ _).trans (MALocal_endDom_dom hκ hz), hz.2.1, hz.2.2⟩⟩
  intro s
  set zs : ℕ → ℂ := fun n => (s n).1 with hzs
  have hflow : BAFlow sz κf ε 𝔠 𝔡 zs := ⟨hA, fun n => (s n).2⟩
  have hT0 := fun n => BAflow_T0_bounds hκf hflow n
  obtain ⟨hLK, -, hDec, hExp, -⟩ := hML hd κf ε 𝔡 𝔠 hκf hε h𝔡 sz zs hflow (fun n => BAflowT0 sz zs n)
    (fun n => (hT0 n).2.2.1.le) (fun n => le_rfl)
  have hζ2 : ∀ (n : ℕ) (u : (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n))) (ω : sz.SeqΩ),
      0 ≤ (sz.Bctl n (BAflowT0 sz zs n)) ^ 2 := fun n u ω => pow_nonneg (Bctl_nonneg sz n _) 2
  have hζ1 : ∀ (n : ℕ) (u : (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n))) (ω : sz.SeqΩ),
      0 ≤ (sz.Bctl n (BAflowT0 sz zs n)) ^ (1 / 5 : ℝ) * STWB sz n (BAflowT0 sz zs n) (zdistInf d (sz.L n) (u.2 0 - u.2 1)) *
          Real.exp (-(((zdistInf d (sz.L n) (u.2 0 - u.2 1) : ℕ) : ℝ) / ellT (sz.L n) (sz.lam n) (BAflowT0 sz zs n)) ^
            (1 / 2 : ℝ)) + ((sz.W n : ℕ) : ℝ) ^ (-(6 / (5 * 𝔠))) :=
    fun n u ω => add_nonneg (mul_nonneg (mul_nonneg (Real.rpow_nonneg (Bctl_nonneg sz n _) _)
      (STWB_nonneg sz n _ _)) (Real.exp_nonneg _)) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hE2 := explicit_of_stochDomAt sz (Sizes.seqP (sz.withLam 0)) h𝔠 hζ2 hbw (hLK 2 (by norm_num)) hτ2 hD1
  have hE1 := explicit_of_stochDomAt sz (Sizes.seqP (sz.withLam 0)) h𝔠 hζ1 hbw (hDec (6 / (5 * 𝔠)) hD'') hτ2 hD1
  have hExpDet := MAQDiff_det_of_precL sz (Sizes.seqP (sz.withLam 0)) hsz (by intro _ _ _ _; rfl) (by intro _ _ _ _; rfl)
    hExp (τ := 𝔠 * (τ / 2)) (by positivity)
  filter_upwards [hE1, hE2, hW8, hN2, hExpDet, hbw, hlam] with n hn1 hn2 hn3 hn4 hn5 hbn hln
  have hz := EMn2BA_zim_pos sz hflow n
  have hz1 : (zs n).im ≤ 1 := (s n).2.2.2
  have hWpos : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hW5 : (5 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) ^ (τ / 2) := by linarith
  have ht0 := (hT0 n).2.2.1
  have ht1 := (hT0 n).2.2.2
  have hfin := two_rpow_le (D := D) hn4
  have hSB0 := MALocal_Bctl_le hd hκf hflow n
  have hSBk : ∀ k : ℕ, STWB sz n (BAflowT0 sz zs n) k ≤ 2 * calB sz n (zs n).im (((sz.W n : ℕ) : ℝ) * (k : ℝ)) :=
    fun k => MALocal_STWB_le hd hκf hflow n k
  refine ⟨⟨?_, ?_⟩, fun a b => ?_⟩
  · refine (prob_union_le (Sizes.seqP (sz.withLam 0)) (((sz.W n : ℕ) : ℝ) ^ (τ / 2)) hn1 hn2 ?_).trans hfin
    intro ω h1 h2 hbad
    obtain ⟨a, b, hab⟩ := hbad
    have hab' : qdBound sz n τ (zs n).im a b <
        ‖avg2 sz n (fun x y => ((‖BAGz sz n (zs n) ω x y‖ ^ 2 : ℝ) : ℂ)) a b - BAprof sz n (zs n) true false a b‖ := hab
    have hΔ1 := h1 (![true, false], ![b, a])
    have hΔ2 := h2 (![true, false], ![b, a])
    have htr := (baTrace2 sz zs n hz ω a b).2
    have hpf := baProfile_eq sz zs n hz hln false a b
    have hnorm : ‖avg2 sz n (fun x y => ((‖BAGz sz n (zs n) ω x y‖ ^ 2 : ℝ) : ℂ)) a b - BAprof sz n (zs n) true false a b‖ =
        BAflowT0 sz zs n * ‖BALloop sz (BAflowLam0 sz zs) (BAflowEs sz zs) n (BAflowT0 sz zs n) ![true, false] ![b, a] ω -
          BAKloop sz (BAflowLam0 sz zs) (BAflowEs sz zs) n (BAflowT0 sz zs n) ![true, false] ![b, a]‖ := by
      rw [htr, hpf, ← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht0.le]
    have hcore := MAQDiff_qd_core sz n hd h𝔠 hbn hz hz1 hW5 a b (norm_nonneg _) (Real.exp_nonneg _)
      (Real.exp_le_one_iff.2 (neg_nonpos.2 (Real.rpow_nonneg (div_nonneg (Nat.cast_nonneg _) ellT_nonneg) _)))
      ht1.le hSB0 (hSBk _) hΔ1 hΔ2
    rw [hnorm] at hab'
    exact absurd hab' (not_lt.2 hcore)
  · refine (prob_union_le (Sizes.seqP (sz.withLam 0)) (((sz.W n : ℕ) : ℝ) ^ (τ / 2)) hn1 hn2 ?_).trans hfin
    intro ω h1 h2 hbad
    obtain ⟨a, b, hab⟩ := hbad
    have hab' : qdBound sz n τ (zs n).im a b <
        ‖avg2 sz n (fun x y => BAGz sz n (zs n) ω x y * BAGz sz n (zs n) ω y x) a b - BAprof sz n (zs n) true true a b‖ := hab
    have hΔ1 := h1 (![true, true], ![b, a])
    have hΔ2 := h2 (![true, true], ![b, a])
    have htr := (baTrace2 sz zs n hz ω a b).1
    have hpf := baProfile_eq sz zs n hz hln true a b
    have hnorm : ‖avg2 sz n (fun x y => BAGz sz n (zs n) ω x y * BAGz sz n (zs n) ω y x) a b - BAprof sz n (zs n) true true a b‖ =
        BAflowT0 sz zs n * ‖BALloop sz (BAflowLam0 sz zs) (BAflowEs sz zs) n (BAflowT0 sz zs n) ![true, true] ![b, a] ω -
          BAKloop sz (BAflowLam0 sz zs) (BAflowEs sz zs) n (BAflowT0 sz zs n) ![true, true] ![b, a]‖ := by
      rw [htr, hpf, ← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht0.le]
    have hcore := MAQDiff_qd_core sz n hd h𝔠 hbn hz hz1 hW5 a b (norm_nonneg _) (Real.exp_nonneg _)
      (Real.exp_le_one_iff.2 (neg_nonpos.2 (Real.rpow_nonneg (div_nonneg (Nat.cast_nonneg _) ellT_nonneg) _)))
      ht1.le hSB0 (hSBk _) hΔ1 hΔ2
    rw [hnorm] at hab'
    exact absurd hab' (not_lt.2 hcore)
  · -- the expectation halves
    have hNW : Nsz sz n ^ (𝔠 * (τ / 2)) ≤ ((sz.W n : ℕ) : ℝ) ^ (τ / 2) := by
      rw [Real.rpow_mul (Nat.cast_nonneg _)]
      exact Real.rpow_le_rpow (Real.rpow_nonneg (Nat.cast_nonneg _) _) hbn hτ2.le
    have hbd : ∀ σ : Fin 2 → Bool,
        ‖(∫ ω, BALloop sz (BAflowLam0 sz zs) (BAflowEs sz zs) n (BAflowT0 sz zs n) σ ![b, a] ω ∂(Sizes.seqP (sz.withLam 0))) -
            BAKloop sz (BAflowLam0 sz zs) (BAflowEs sz zs) n (BAflowT0 sz zs n) σ ![b, a]‖ ≤
          ((sz.W n : ℕ) : ℝ) ^ (τ / 2) * (sz.Bctl n (BAflowT0 sz zs n) ^ 2 *
            ((sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d) ^ (-(1 / 5 : ℝ)) + sz.Bctl n (BAflowT0 sz zs n))) := by
      intro σ
      have h := hn5 (σ, ![b, a]) (Classical.arbitrary _)
      refine h.trans ?_
      refine mul_le_mul_of_nonneg_right hNW ?_
      refine mul_nonneg (pow_nonneg (Bctl_nonneg sz n _) 2) (add_nonneg (Real.rpow_nonneg (by positivity) _)
        (Bctl_nonneg sz n _))
    refine ⟨?_, ?_⟩
    · have hint : ∫ ω, avg2 sz n (fun x y => ((‖BAGz sz n (zs n) ω x y‖ ^ 2 : ℝ) : ℂ)) a b ∂(Sizes.seqP (sz.withLam 0)) =
          (BAflowT0 sz zs n : ℂ) * ∫ ω, BALloop sz (BAflowLam0 sz zs) (BAflowEs sz zs) n (BAflowT0 sz zs n) ![true, false] ![b, a] ω
            ∂(Sizes.seqP (sz.withLam 0)) := by
        refine (integral_congr_ae (Filter.Eventually.of_forall fun ω => (baTrace2 sz zs n hz ω a b).2)).trans ?_
        exact integral_const_mul _ _
      have hpf := baProfile_eq sz zs n hz hln false a b
      rw [hint, hpf, ← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht0.le]
      exact MAQDiff_qd_exp_core sz n hz hn3 (norm_nonneg _) ht1.le hSB0 (hbd ![true, false])
    · have hint : ∫ ω, avg2 sz n (fun x y => BAGz sz n (zs n) ω x y * BAGz sz n (zs n) ω y x) a b ∂(Sizes.seqP (sz.withLam 0)) =
          (BAflowT0 sz zs n : ℂ) * ∫ ω, BALloop sz (BAflowLam0 sz zs) (BAflowEs sz zs) n (BAflowT0 sz zs n) ![true, true] ![b, a] ω
            ∂(Sizes.seqP (sz.withLam 0)) := by
        refine (integral_congr_ae (Filter.Eventually.of_forall fun ω => (baTrace2 sz zs n hz ω a b).1)).trans ?_
        exact integral_const_mul _ _
      have hpf := baProfile_eq sz zs n hz hln true a b
      rw [hint, hpf, ← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht0.le]
      exact MAQDiff_qd_exp_core sz n hz hn3 (norm_nonneg _) ht1.le hSB0 (hbd ![true, true])

end Fixed

/-! ## 4. The `z`-Lipschitz bound of `BAprof` -/

section ProfLip

open scoped Matrix.Norms.L2Operator in
/-- The `ℓ²` norm of a column is at most the `ℓ² → ℓ²` operator norm. -/
private theorem MAQDiff_col_sq_le {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ) (a : ι) :
    ∑ b, ‖A b a‖ ^ 2 ≤ ‖A‖ ^ 2 := by
  have h := Matrix.l2_opNorm_mulVec A (EuclideanSpace.single a 1)
  rw [PiLp.norm_single, norm_one, mul_one] at h
  have h2 : ‖(EuclideanSpace.equiv ι ℂ).symm (A *ᵥ (EuclideanSpace.single a (1 : ℂ) : EuclideanSpace ℂ ι))‖ ^ 2 =
      ∑ b, ‖A b a‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp
  rw [← h2]
  exact pow_le_pow_left₀ (norm_nonneg _) h 2

open scoped Matrix.Norms.L2Operator in
/-- `M(z)` is Lipschitz in `z` in `ℓ² → ℓ²` on `Im m ≥ κ'`: `M(z) = (H - (z + m(z)))⁻¹`, `H = gΨ^{(B)}` Hermitian (`cont_green_diff` at `H = H'`,
`BAm_sub_le_of_im`); the consequence used is the `ℓ²` bound of every column of `M(z) - M(w)`. -/
private theorem MAQDiff_M_col_sq {d L : ℕ} [NeZero L] (g κ' : ℝ) (hκ' : 0 < κ') {z w : ℂ} (hz0 : 0 < z.im) (hw0 : 0 < w.im)
    (hmz : κ' ≤ (BAm d L g z).im) (hmw : κ' ≤ (BAm d L g w).im) (a : Zd d L) :
    ∑ b, ‖BAMB d L g z (BAm d L g z) b a - BAMB d L g w (BAm d L g w) b a‖ ^ 2 ≤
      (κ'⁻¹ * κ'⁻¹ * (1 + κ'⁻¹ * κ'⁻¹) * ‖z - w‖) ^ 2 := by
  have hH : ((g : ℂ) • PsiB d L).IsHermitian := BAPsi_isHermitian d L g
  have hMG : ∀ (u m : ℂ), BAMB d L g u m = RBM.green ((g : ℂ) • PsiB d L) (u + m) := fun u m =>
    RBM.Ind.ContinuityNet.cont_Gres_true_eq_green ((g : ℂ) • PsiB d L) (u + m)
  have hqz : κ' ≤ |(z + BAm d L g z).im| := by
    rw [Complex.add_im]; exact le_trans (by linarith) (le_abs_self _)
  have hqw : κ' ≤ |(w + BAm d L g w).im| := by
    rw [Complex.add_im]; exact le_trans (by linarith) (le_abs_self _)
  have h1 := RBM.Ind.ContinuityNet.cont_green_diff hH hH hκ' hqz hqw
  rw [sub_self, norm_zero, zero_add] at h1
  have hdm : ‖BAm d L g z - BAm d L g w‖ ≤ ‖z - w‖ / κ' ^ 2 := BAm_sub_le_of_im d L g κ' z w hκ' hz0 hw0 hmz hmw
  have h2 : ‖(z + BAm d L g z) - (w + BAm d L g w)‖ ≤ ‖z - w‖ + ‖z - w‖ / κ' ^ 2 := by
    calc _ = ‖(z - w) + (BAm d L g z - BAm d L g w)‖ := by congr 1; ring
      _ ≤ ‖z - w‖ + ‖BAm d L g z - BAm d L g w‖ := norm_add_le _ _
      _ ≤ _ := by linarith
  have h3 : ‖BAMB d L g z (BAm d L g z) - BAMB d L g w (BAm d L g w)‖ ≤ κ'⁻¹ * κ'⁻¹ * (1 + κ'⁻¹ * κ'⁻¹) * ‖z - w‖ := by
    rw [hMG, hMG]
    refine h1.trans ?_
    calc κ'⁻¹ * κ'⁻¹ * ‖(z + BAm d L g z) - (w + BAm d L g w)‖
        ≤ κ'⁻¹ * κ'⁻¹ * (‖z - w‖ + ‖z - w‖ / κ' ^ 2) := mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = κ'⁻¹ * κ'⁻¹ * (1 + κ'⁻¹ * κ'⁻¹) * ‖z - w‖ := by field_simp
  refine le_trans ?_ (pow_le_pow_left₀ (norm_nonneg _) h3 2)
  refine le_trans (le_of_eq ?_) (MAQDiff_col_sq_le (BAMB d L g z (BAm d L g z) - BAMB d L g w (BAm d L g w)) a)
  simp [Matrix.sub_apply]

/-- Entrywise bound of the difference of two `M^{(+,σ)}` for symmetric `M, M'` with unit `ℓ²` rows: `Σ_b |Q_{ab} - Q'_{ab}| ≤ 2 B` when every column of `M - M'` has
`ℓ²` norm at most `B` (Cauchy-Schwarz; `|M² - M'²| ≤ |M - M'| (|M| + |M'|)`, `||M|² - |M'|²| ≤ |M - M'| (|M| + |M'|)`). -/
private theorem MAQDiff_Q_row_diff {d L : ℕ} [NeZero L] {M M' : Matrix (Zd d L) (Zd d L) ℂ}
    (hs : ∀ a b, M a b = M b a) (hs' : ∀ a b, M' a b = M' b a)
    (h1 : ∀ a, ∑ b, ‖M a b‖ ^ 2 ≤ 1) (h1' : ∀ a, ∑ b, ‖M' a b‖ ^ 2 ≤ 1) {B : ℝ} (hB : 0 ≤ B)
    (hd : ∀ a, ∑ b, ‖M b a - M' b a‖ ^ 2 ≤ B ^ 2) (σ : Bool) (a : Zd d L) :
    ∑ b, ‖BAMss d L M true σ a b - BAMss d L M' true σ a b‖ ≤ 2 * B := by
  have hent : ∀ b, ‖BAMss d L M true σ a b - BAMss d L M' true σ a b‖ ≤
      ‖M a b - M' a b‖ * (‖M a b‖ + ‖M' a b‖) := by
    intro b
    cases σ
    · simp only [BAMss, Matrix.of_apply, BAMsigma, ite_true, Bool.false_eq_true, ite_false, Matrix.conjTranspose_apply]
      rw [hs b a, hs' b a]
      have hn : ∀ x : ℂ, x * star x = ((‖x‖ ^ 2 : ℝ) : ℂ) := fun x => by
        rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      rw [hn, hn, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      have h1 : ‖M a b‖ ^ 2 - ‖M' a b‖ ^ 2 = (‖M a b‖ - ‖M' a b‖) * (‖M a b‖ + ‖M' a b‖) := by ring
      rw [h1, abs_mul, abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
      exact mul_le_mul_of_nonneg_right ((abs_norm_sub_norm_le _ _)) (add_nonneg (norm_nonneg _) (norm_nonneg _))
    · simp only [BAMss, Matrix.of_apply, BAMsigma, ite_true]
      rw [hs b a, hs' b a]
      have h1 : M a b * M a b - M' a b * M' a b = (M a b - M' a b) * (M a b + M' a b) := by ring
      rw [h1, norm_mul]
      exact mul_le_mul_of_nonneg_left (norm_add_le _ _) (norm_nonneg _)
  refine (Finset.sum_le_sum fun b _ => hent b).trans ?_
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Zd d L)) (fun b => ‖M a b - M' a b‖)
    (fun b => ‖M a b‖ + ‖M' a b‖)
  have hu : ∑ b, ‖M a b - M' a b‖ ^ 2 ≤ B ^ 2 := by
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun b _ => ?_)) (hd a)
    rw [hs a b, hs' a b]
  have hv : ∑ b, (‖M a b‖ + ‖M' a b‖) ^ 2 ≤ 4 := by
    calc ∑ b, (‖M a b‖ + ‖M' a b‖) ^ 2 ≤ ∑ b, (2 * ‖M a b‖ ^ 2 + 2 * ‖M' a b‖ ^ 2) :=
          Finset.sum_le_sum fun b _ => by nlinarith [sq_nonneg (‖M a b‖ - ‖M' a b‖)]
      _ = 2 * ∑ b, ‖M a b‖ ^ 2 + 2 * ∑ b, ‖M' a b‖ ^ 2 := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      _ ≤ 4 := by linarith [h1 a, h1' a]
  have hsq : (∑ b, ‖M a b - M' a b‖ * (‖M a b‖ + ‖M' a b‖)) ^ 2 ≤ (2 * B) ^ 2 := by
    refine hCS.trans ?_
    calc (∑ b, ‖M a b - M' a b‖ ^ 2) * ∑ b, (‖M a b‖ + ‖M' a b‖) ^ 2 ≤ B ^ 2 * 4 :=
          mul_le_mul hu hv (Finset.sum_nonneg fun _ _ => sq_nonneg _) (sq_nonneg _)
      _ = (2 * B) ^ 2 := by ring
  exact (pow_le_pow_iff_left₀ (Finset.sum_nonneg fun _ _ => mul_nonneg (norm_nonneg _)
    (add_nonneg (norm_nonneg _) (norm_nonneg _))) (by positivity) two_ne_zero).1 hsq

open scoped Matrix.Norms.Operator in
/-- Row sums of `|Q|` at most `r` give `‖Q‖_{∞→∞} ≤ max r 0` (`BAKBase_norm_le` with a general `r`). -/
private theorem MAQDiff_normInf_le {ι : Type*} [Fintype ι] [DecidableEq ι] {Q : Matrix ι ι ℂ} {r : ℝ}
    (hQ : ∀ a, ∑ b, ‖Q a b‖ ≤ r) : ‖Q‖ ≤ max r 0 := by
  have h : ‖Q‖₊ ≤ Real.toNNReal r := by
    rw [Matrix.linfty_opNNNorm_def]
    refine Finset.sup_le fun a _ => ?_
    rw [← NNReal.coe_le_coe, NNReal.coe_sum, Real.coe_toNNReal']
    simpa using (hQ a).trans (le_max_left _ _)
  have h' : (‖Q‖₊ : ℝ) ≤ (Real.toNNReal r : ℝ) := by exact_mod_cast h
  simpa [Real.coe_toNNReal', max_comm] using h'

open scoped Matrix.Norms.Operator in
/-- An entry is at most the `∞ → ∞` norm. -/
private theorem MAQDiff_entry_le_normInf {ι : Type*} [Fintype ι] [DecidableEq ι] (Q : Matrix ι ι ℂ) (a b : ι) :
    ‖Q a b‖ ≤ ‖Q‖ := by
  have h : ‖Q a b‖₊ ≤ ‖Q‖₊ := by
    rw [Matrix.linfty_opNNNorm_def]
    refine le_trans ?_ (Finset.le_sup (f := fun i => ∑ j, ‖Q i j‖₊) (Finset.mem_univ a))
    exact Finset.single_le_sum (f := fun j => ‖Q a j‖₊) (fun _ _ => bot_le) (Finset.mem_univ b)
  exact_mod_cast h

open scoped Matrix.Norms.Operator in
/-- Neumann bound (`‖Q‖_{∞→∞} ≤ t < 1`): `1 - Q` is a unit, `‖(1 - Q)⁻¹‖ ≤ (1 - t)⁻¹` and `(1 - Q)⁻¹ Q = (1 - Q)⁻¹ - 1`. -/
private theorem MAQDiff_neumann {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] {Q : Matrix ι ι ℂ} {t : ℝ}
    (hQ : ‖Q‖ ≤ t) (ht : t < 1) :
    IsUnit (1 - Q) ∧ ‖Ring.inverse (1 - Q)‖ ≤ (1 - t)⁻¹ ∧ Ring.inverse (1 - Q) * Q = Ring.inverse (1 - Q) - 1 := by
  have hQ1 : ‖Q‖ < 1 := lt_of_le_of_lt hQ ht
  have hu : IsUnit (1 - Q) := ⟨Units.oneSub Q hQ1, Units.val_oneSub _ _⟩
  have hmul : Ring.inverse (1 - Q) * (1 - Q) = 1 := Ring.inverse_mul_cancel _ hu
  have hid : Ring.inverse (1 - Q) * Q = Ring.inverse (1 - Q) - 1 := by
    have : Ring.inverse (1 - Q) * (1 - Q) = Ring.inverse (1 - Q) - Ring.inverse (1 - Q) * Q := by
      rw [mul_sub, mul_one]
    rw [hmul] at this
    rw [eq_sub_iff_add_eq, add_comm]
    exact (sub_eq_iff_eq_add.mp this.symm).symm
  refine ⟨hu, ?_, hid⟩
  have h1 : ‖Ring.inverse (1 - Q)‖ ≤ 1 + ‖Ring.inverse (1 - Q)‖ * t := by
    calc ‖Ring.inverse (1 - Q)‖ = ‖1 + Ring.inverse (1 - Q) * Q‖ := by rw [hid]; congr 1; abel
      _ ≤ ‖(1 : Matrix ι ι ℂ)‖ + ‖Ring.inverse (1 - Q) * Q‖ := norm_add_le _ _
      _ ≤ 1 + ‖Ring.inverse (1 - Q)‖ * t := by
          rw [norm_one]
          exact add_le_add le_rfl ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left hQ (norm_nonneg _)))
  have h2 : 0 < 1 - t := by linarith
  rw [← one_div, le_div_iff₀ h2]
  linarith

open scoped Matrix.Norms.Operator in
/-- The profile differs by the propagator difference: for `‖Q‖ ≤ t < 1`, `‖Q'‖ ≤ t' < 1`, `‖Q - Q'‖ ≤ B`,
`|((1-Q)⁻¹ Q)_{ab} - ((1-Q')⁻¹ Q')_{ab}| ≤ (1 - t)⁻¹ B (1 - t')⁻¹` (`Θ Q = Θ - 1`, `Θ - Θ' = Θ (Q - Q') Θ'`). -/
private theorem MAQDiff_prof_diff {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] {Q Q' : Matrix ι ι ℂ} {t t' B : ℝ}
    (hQ : ‖Q‖ ≤ t) (hQ' : ‖Q'‖ ≤ t') (ht : t < 1) (ht' : t' < 1) (hB : ‖Q - Q'‖ ≤ B) (a b : ι) :
    ‖(Ring.inverse (1 - Q) * Q) a b - (Ring.inverse (1 - Q') * Q') a b‖ ≤ (1 - t)⁻¹ * B * (1 - t')⁻¹ := by
  obtain ⟨hu, hΘ, hid⟩ := MAQDiff_neumann hQ ht
  obtain ⟨hu', hΘ', hid'⟩ := MAQDiff_neumann hQ' ht'
  set Θ := Ring.inverse (1 - Q) with hΘdef
  set Θ' := Ring.inverse (1 - Q') with hΘ'def
  have hdiff : Θ - Θ' = Θ * (Q - Q') * Θ' := by
    have e1 : Θ * (1 - Q') * Θ' = Θ := by
      rw [mul_assoc, Ring.mul_inverse_cancel _ hu', mul_one]
    have e2 : Θ * (1 - Q) * Θ' = Θ' := by
      rw [hΘdef, Ring.inverse_mul_cancel _ hu, one_mul]
    calc Θ - Θ' = Θ * (1 - Q') * Θ' - Θ * (1 - Q) * Θ' := by rw [e1, e2]
      _ = Θ * (Q - Q') * Θ' := by noncomm_ring
  have h1 : (Θ * Q) a b - (Θ' * Q') a b = (Θ - Θ') a b := by
    rw [hid, hid']
    simp [Matrix.sub_apply]
  rw [h1]
  refine (MAQDiff_entry_le_normInf _ a b).trans ?_
  rw [hdiff]
  have h2 : 0 < 1 - t := by linarith
  have h2' : 0 < 1 - t' := by linarith
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) hB
  calc ‖Θ * (Q - Q') * Θ'‖ ≤ ‖Θ * (Q - Q')‖ * ‖Θ'‖ := norm_mul_le _ _
    _ ≤ ‖Θ‖ * ‖Q - Q'‖ * ‖Θ'‖ := mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
    _ ≤ (1 - t)⁻¹ * B * (1 - t')⁻¹ := by
        refine mul_le_mul (mul_le_mul hΘ hB (norm_nonneg _) (by positivity)) hΘ' (norm_nonneg _) (by positivity)


/-- Ward rows of `M(z)`: `Σ_b |M_{ab}|² = Im m / (Im m + Im z)` for a solution `m` of `(self_m)` and `Im z ≥ 0` (`BAMB_ward_row`). -/
private theorem MAQDiff_M_row_sq {d L : ℕ} [NeZero L] (g : ℝ) {z m : ℂ} (hz : 0 ≤ z.im) (h : BASelf d L g z m) (a : Zd d L) :
    ∑ b, ‖BAMB d L g z m a b‖ ^ 2 = m.im / (m.im + z.im) := by
  have hm := h.1
  have hne : m.im + z.im ≠ 0 := by linarith
  rw [eq_div_iff hne, mul_comm]
  exact BAMB_ward_row d L g z m hz h a

/-- `‖Q(z)‖_{∞→∞} = t₀`: the row sums of `|M^{(+,σ)}_{ab}| = |M_{ab}|²` are `Im m/(Im m + Im z)` (both `σ`; `M` symmetric). -/
private theorem MAQDiff_Q_row_sum {d L : ℕ} [NeZero L] (g : ℝ) {z m : ℂ} (hz : 0 ≤ z.im) (h : BASelf d L g z m) (σ : Bool)
    (a : Zd d L) :
    ∑ b, ‖BAMss d L (BAMB d L g z m) true σ a b‖ = m.im / (m.im + z.im) := by
  rw [← MAQDiff_M_row_sq g hz h a]
  refine Finset.sum_congr rfl fun b _ => ?_
  have hs := BAMB_symm d L g z m a b
  cases σ
  · simp only [BAMss, Matrix.of_apply, BAMsigma, ite_true, Bool.false_eq_true, ite_false, Matrix.conjTranspose_apply]
    rw [norm_mul, norm_star, ← hs, sq]
  · simp only [BAMss, Matrix.of_apply, BAMsigma, ite_true]
    rw [norm_mul, ← hs, sq]

open scoped Matrix.Norms.Operator in
/-- `baProf_lip`: on the ρ-bulk, `|Δ BAprof| ≤ C η⁻² |z - w| W^{-d}`, `C = 12 κ'⁻² (1 + κ'⁻²)`, `κ' = (πκ)^5/2048`, for every `d`, `sz`, `n`.
Proof outline: `‖Q(z)‖_{∞→∞} = t₀ < 1` (Ward rows, `MAQDiff_Q_row_sum`), Neumann `‖Θ‖_{∞→∞} ≤ (1 - t₀)⁻¹ ≤ 2/η` (`MAQDiff_neumann`), `ΘQ = Θ - 1`,
`Θ - Θ' = Θ (Q - Q') Θ'` (`MAQDiff_prof_diff`), `‖Q - Q'‖_{∞→∞} ≤ 2 max_a ‖col_a (M - M')‖₂ ≤ 2 ‖M - M'‖_{ℓ²op}` (`MAQDiff_Q_row_diff`), `‖M - M'‖_{ℓ²op} ≤ κ'⁻² (1 + κ'⁻²) |z - w|`
(`MAQDiff_M_col_sq`: `cont_green_diff`, `BAm_sub_le_of_im`).  This argument gives the constant `8 κ'⁻² (1 + κ'⁻²)`; the statement carries `12`. -/
theorem baProf_lip (κ : ℝ) (hκ : 0 < κ) : ∃ C : ℝ, 0 < C ∧ ∀ (d : ℕ) (sz : Sizes d) (n : ℕ) (η : ℝ) (z w : ℂ), 0 < η → η ≤ z.im →
    η ≤ w.im → z.im ≤ 1 → w.im ≤ 1 → BAbulk d (sz.L n) (sz.lam n) κ z.re → BAbulk d (sz.L n) (sz.lam n) κ w.re →
      ∀ (σ : Bool) (a b : Zd d (sz.L n)),
        ‖BAprof sz n z true σ a b - BAprof sz n w true σ a b‖ ≤ C * (η ^ 2)⁻¹ * ‖z - w‖ / ((sz.W n : ℕ) : ℝ) ^ d := by
  have hκ' : 0 < (Real.pi * κ) ^ 5 / 2048 := by positivity
  set κ' : ℝ := (Real.pi * κ) ^ 5 / 2048 with hκ'def
  set C₀ : ℝ := κ'⁻¹ * κ'⁻¹ * (1 + κ'⁻¹ * κ'⁻¹) with hC₀
  have hC₀0 : 0 < C₀ := by positivity
  refine ⟨12 * C₀, by positivity, ?_⟩
  intro d sz n η z w hη hηz hηw hz1 hw1 hbz hbw σ a b
  have hz0 : 0 < z.im := lt_of_lt_of_le hη hηz
  have hw0 : 0 < w.im := lt_of_lt_of_le hη hηw
  have hmz : κ' ≤ (BAm d (sz.L n) (sz.lam n) z).im := ba_dom_of_bulk d (sz.L n) (sz.lam n) κ hκ hbz hz0 hz1
  have hmw : κ' ≤ (BAm d (sz.L n) (sz.lam n) w).im := ba_dom_of_bulk d (sz.L n) (sz.lam n) κ hκ hbw hw0 hw1
  have hsz := BAm_self d (sz.L n) (sz.lam n) z hz0
  have hsw := BAm_self d (sz.L n) (sz.lam n) w hw0
  have hm1z : (BAm d (sz.L n) (sz.lam n) z).im ≤ 1 :=
    (Complex.im_le_norm _).trans (BAm_norm_le_one d (sz.L n) (sz.lam n) z _ hz0.le hsz)
  have hm1w : (BAm d (sz.L n) (sz.lam n) w).im ≤ 1 :=
    (Complex.im_le_norm _).trans (BAm_norm_le_one d (sz.L n) (sz.lam n) w _ hw0.le hsw)
  set t : ℝ := (BAm d (sz.L n) (sz.lam n) z).im / ((BAm d (sz.L n) (sz.lam n) z).im + z.im) with ht
  set t' : ℝ := (BAm d (sz.L n) (sz.lam n) w).im / ((BAm d (sz.L n) (sz.lam n) w).im + w.im) with ht'
  have hmpz : 0 < (BAm d (sz.L n) (sz.lam n) z).im := lt_of_lt_of_le hκ' hmz
  have hmpw : 0 < (BAm d (sz.L n) (sz.lam n) w).im := lt_of_lt_of_le hκ' hmw
  have ht0 : 0 ≤ t := by positivity
  have ht'0 : 0 ≤ t' := by positivity
  have ht1 : t < 1 := by
    rw [ht, div_lt_one (by linarith)]; linarith
  have ht'1 : t' < 1 := by
    rw [ht', div_lt_one (by linarith)]; linarith
  -- `(1 - t)⁻¹ ≤ 2 η⁻¹`
  have hinv : ∀ {mi zi : ℝ}, 0 < mi → mi ≤ 1 → zi ≤ 1 → η ≤ zi → 0 < zi → (1 - mi / (mi + zi))⁻¹ ≤ 2 * η⁻¹ := by
    intro mi zi hmi hmi1 hzi1 hηzi hzi
    have e : 1 - mi / (mi + zi) = zi / (mi + zi) := by field_simp; ring
    rw [e, inv_div, div_le_iff₀ hzi]
    calc mi + zi ≤ 2 := by linarith
      _ = 2 * η⁻¹ * η := by field_simp
      _ ≤ 2 * η⁻¹ * zi := mul_le_mul_of_nonneg_left hηzi (by positivity)
  have hinvt : (1 - t)⁻¹ ≤ 2 * η⁻¹ := hinv hmpz hm1z hz1 hηz hz0
  have hinvt' : (1 - t')⁻¹ ≤ 2 * η⁻¹ := hinv hmpw hm1w hw1 hηw hw0
  -- the `Q`'s
  set M := BAMB d (sz.L n) (sz.lam n) z (BAm d (sz.L n) (sz.lam n) z) with hM
  set M' := BAMB d (sz.L n) (sz.lam n) w (BAm d (sz.L n) (sz.lam n) w) with hM'
  set Q := BAMss d (sz.L n) M true σ with hQ
  set Q' := BAMss d (sz.L n) M' true σ with hQ'
  have hQn : ‖Q‖ ≤ t := by
    refine (MAQDiff_normInf_le (fun a => (MAQDiff_Q_row_sum (sz.lam n) hz0.le hsz σ a).le)).trans ?_
    rw [max_eq_left ht0]
  have hQn' : ‖Q'‖ ≤ t' := by
    refine (MAQDiff_normInf_le (fun a => (MAQDiff_Q_row_sum (sz.lam n) hw0.le hsw σ a).le)).trans ?_
    rw [max_eq_left ht'0]
  have hB0 : 0 ≤ C₀ * ‖z - w‖ := by positivity
  have hrow1 : ∀ a, ∑ b, ‖M a b‖ ^ 2 ≤ 1 := fun a => by
    rw [MAQDiff_M_row_sq (sz.lam n) hz0.le hsz a, div_le_one (by linarith)]; linarith
  have hrow1' : ∀ a, ∑ b, ‖M' a b‖ ^ 2 ≤ 1 := fun a => by
    rw [MAQDiff_M_row_sq (sz.lam n) hw0.le hsw a, div_le_one (by linarith)]; linarith
  have hQd : ‖Q - Q'‖ ≤ 2 * (C₀ * ‖z - w‖) := by
    refine (MAQDiff_normInf_le (r := 2 * (C₀ * ‖z - w‖)) (fun a => ?_)).trans ?_
    · simpa [Matrix.sub_apply] using MAQDiff_Q_row_diff (BAMB_symm _ _ _ z _) (BAMB_symm _ _ _ w _) hrow1 hrow1' hB0
        (fun a => by
          have := MAQDiff_M_col_sq (sz.lam n) κ' hκ' hz0 hw0 hmz hmw a
          rwa [hC₀] ) σ a
    · rw [max_eq_left (by positivity)]
  have hprof := MAQDiff_prof_diff hQn hQn' ht1 ht'1 hQd a b
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) ^ d := pow_pos (by exact_mod_cast sz.W_pos n) d
  have hnormdiv : ‖BAprof sz n z true σ a b - BAprof sz n w true σ a b‖ =
      ‖(Ring.inverse (1 - Q) * Q) a b - (Ring.inverse (1 - Q') * Q') a b‖ / ((sz.W n : ℕ) : ℝ) ^ d := by
    have e1 : PropThetaQ Q 1 = Ring.inverse (1 - Q) := by unfold PropThetaQ; simp
    have e2 : PropThetaQ Q' 1 = Ring.inverse (1 - Q') := by unfold PropThetaQ; simp
    unfold BAprof
    rw [← sub_div, norm_div, norm_pow, Complex.norm_natCast, e1, e2]
  rw [hnormdiv]
  refine div_le_div_of_nonneg_right ?_ hW.le
  refine hprof.trans ?_
  calc (1 - t)⁻¹ * (2 * (C₀ * ‖z - w‖)) * (1 - t')⁻¹ ≤ (2 * η⁻¹) * (2 * (C₀ * ‖z - w‖)) * (2 * η⁻¹) := by
        refine mul_le_mul (mul_le_mul hinvt le_rfl (by positivity) (by positivity)) hinvt' (by
          have : 0 < 1 - t' := by linarith
          positivity) (by positivity)
    _ = 8 * C₀ * (η ^ 2)⁻¹ * ‖z - w‖ := by field_simp; ring
    _ ≤ 12 * C₀ * (η ^ 2)⁻¹ * ‖z - w‖ := by
        have : 0 ≤ C₀ * (η ^ 2)⁻¹ * ‖z - w‖ := by positivity
        nlinarith


end ProfLip

/-! ## 5. The cover lemmas for `σ = ±` and the `N^{-7}`-net `baMANetQD` -/

section Net

variable {d : ℕ}

open private znet_qd_core znet_sq_diff znet_prod_diff znet_c4 from RBM3D.Main.ZNet
open private MALocal_geom MALocal_thresholds MALocal_net_exists MALocal_card_le MALocal_net_count MALocal_Gres_lip
  MALocal_endDom_im_pos from RBM3D.BA.MALocal

open scoped Matrix.Norms.L2Operator in
/-- `|G(z)_{xy}| ≤ η⁻¹` on `Im z ≥ η`, for every Hermitian `H` (the block Anderson analogue of `Gn_entry_le`, `Main/ZNet`). -/
private theorem MAQDiff_Gres_le {ι : Type*} [Fintype ι] [DecidableEq ι] {H : Matrix ι ι ℂ} (hH : H.IsHermitian) {q : ℂ} {η : ℝ}
    (hη : 0 < η) (hq : η ≤ q.im) (x y : ι) : ‖Gres H q true x y‖ ≤ η⁻¹ := by
  have h1 := RBM.Ind.ContinuityNet.cont_norm_green_le hH hη (le_trans hq (le_abs_self _))
  have h2 := norm_matrix_entry_le_opNorm (RBM.green H q) x y
  rw [RBM.Ind.ContinuityNet.cont_Gres_true_eq_green]
  exact h2.trans h1

/-- The cover lemma for `(eq:diffu1)`, `(eq:diffu2)` at the block Anderson model (analogues of `qd1Bad_net`, `qd2Bad_net`, `Main/ZNet`; both `σ` at once): every `ω` in the bad
event at `τ` over the end domain lies in the per-point bad event at `τ/2` of a net point (`32 ≤ N`, `5 ≤ W^{τ/2}`, `C ≤ N` with `C` the constant of `baProf_lip`);
deterministic, for every `ω`.  The `G`-entries are `η⁻²`-Lipschitz (`MALocal_Gres_lip`), the profile is `baProf_lip`-Lipschitz. -/
private theorem MAQDiff_qdBad_net (sz : Sizes d) (n : ℕ) (hd : 3 ≤ d) {κ ε τ C : ℝ} (σ : Bool) (hε : 0 < ε)
    (h32 : 32 ≤ Nsz sz n) (hC0 : 0 < C) (hCN : C ≤ Nsz sz n)
    (hlip : ∀ (η : ℝ) (z w : ℂ), 0 < η → η ≤ z.im → η ≤ w.im → z.im ≤ 1 → w.im ≤ 1 →
      BAbulk d (sz.L n) (sz.lam n) κ z.re → BAbulk d (sz.L n) (sz.lam n) κ w.re → ∀ (σ : Bool) (a b : Zd d (sz.L n)),
        ‖BAprof sz n z true σ a b - BAprof sz n w true σ a b‖ ≤ C * (η ^ 2)⁻¹ * ‖z - w‖ / ((sz.W n : ℕ) : ℝ) ^ d)
    (h5 : 5 ≤ ((sz.W n : ℕ) : ℝ) ^ (τ / 2)) (S : Finset ℂ) (hS : ∀ w ∈ S, BAendDom sz κ ε n w)
    (hcov : ∀ z : ℂ, BAendDom sz κ ε n z → ∃ w ∈ S,
      |z.re - w.re| ≤ Nsz sz n ^ (-7 : ℝ) ∧ |z.im - w.im| ≤ Nsz sz n ^ (-7 : ℝ))
    (ω : sz.SeqΩ) (hω : ∃ z : ℂ, BAendDom sz κ ε n z ∧ BAqdBadz sz τ n z ω σ) :
    ∃ w ∈ S, BAqdBadz sz (τ / 2) n w ω σ := by
  obtain ⟨z, hz, a, b, hab⟩ := hω
  obtain ⟨w, hwS, hre, him⟩ := hcov z hz
  refine ⟨w, hwS, ?_⟩
  by_contra hnb
  unfold BAqdBadz at hnb
  push Not at hnb
  have hnb' := hnb a b
  have hw := hS w hwS
  obtain ⟨hzu, hwu, hshift, hζ⟩ := MALocal_geom sz n hε h32 hz hw hre him
  have hN1 : (1 : ℝ) ≤ Nsz sz n := by linarith
  have hu0 : 0 < (Nsz sz n)⁻¹ := inv_pos.2 (by linarith)
  have hu32 : (Nsz sz n)⁻¹ ≤ 1 / 32 := by
    have := inv_anti₀ (by norm_num : (0 : ℝ) < 32) h32
    simpa using this
  have hGz : ∀ x y, ‖BAGz sz n z ω x y‖ ≤ ((Nsz sz n)⁻¹)⁻¹ := fun x y =>
    MAQDiff_Gres_le (Sizes.seqHBA_isHermitian sz n ω) hu0 hzu x y
  have hGw : ∀ x y, ‖BAGz sz n w ω x y‖ ≤ ((Nsz sz n)⁻¹)⁻¹ := fun x y =>
    MAQDiff_Gres_le (Sizes.seqHBA_isHermitian sz n ω) hu0 hwu x y
  have hGd : ∀ x y, ‖BAGz sz n z ω x y - BAGz sz n w ω x y‖ ≤ 2 * ((Nsz sz n)⁻¹) ^ 5 := by
    intro x y
    refine (MALocal_Gres_lip (Sizes.seqHBA_isHermitian sz n ω) hu0 hzu hwu x y).trans ?_
    calc ((Nsz sz n)⁻¹)⁻¹ * ((Nsz sz n)⁻¹)⁻¹ * ‖z - w‖ ≤ ((Nsz sz n)⁻¹)⁻¹ * ((Nsz sz n)⁻¹)⁻¹ * (2 * ((Nsz sz n)⁻¹) ^ 7) :=
          mul_le_mul_of_nonneg_left hζ (by positivity)
      _ = 2 * ((Nsz sz n)⁻¹) ^ 5 := by field_simp
  have hF : ∀ x y, ‖(if σ then BAGz sz n z ω x y * BAGz sz n z ω y x else ((‖BAGz sz n z ω x y‖ ^ 2 : ℝ) : ℂ)) -
      (if σ then BAGz sz n w ω x y * BAGz sz n w ω y x else ((‖BAGz sz n w ω x y‖ ^ 2 : ℝ) : ℂ))‖ ≤
      4 * ((Nsz sz n)⁻¹) ^ 4 := by
    intro x y
    cases σ
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact (znet_sq_diff (hGz x y) (hGw x y) (hGd x y)).trans (le_of_eq (znet_c4 hu0))
    · simp only [↓reduceIte]
      exact (znet_prod_diff (hGw x y) (hGz y x) (hGd x y) (hGd y x)).trans (le_of_eq (znet_c4 hu0))
  have havg := avg2_lip sz n (fun x y => if σ then BAGz sz n z ω x y * BAGz sz n z ω y x else ((‖BAGz sz n z ω x y‖ ^ 2 : ℝ) : ℂ))
    (fun x y => if σ then BAGz sz n w ω x y * BAGz sz n w ω y x else ((‖BAGz sz n w ω x y‖ ^ 2 : ℝ) : ℂ))
    (c := 4 * ((Nsz sz n)⁻¹) ^ 4) hF a b
  have hprof := hlip _ z w hu0 hzu hwu hz.2.2 hw.2.2 hz.1 hw.1 σ a b
  have hW1 : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) ^ d := one_le_pow₀ (by exact_mod_cast sz.W_pos n)
  have hprof' : ‖BAprof sz n z true σ a b - BAprof sz n w true σ a b‖ ≤ 2 * ((Nsz sz n)⁻¹) ^ 4 := by
    refine hprof.trans ?_
    have hCu : C * (Nsz sz n)⁻¹ ≤ 1 := by
      rw [← div_eq_mul_inv, div_le_one (by linarith)]; exact hCN
    calc C * (((Nsz sz n)⁻¹) ^ 2)⁻¹ * ‖z - w‖ / ((sz.W n : ℕ) : ℝ) ^ d ≤ C * (((Nsz sz n)⁻¹) ^ 2)⁻¹ * ‖z - w‖ / 1 :=
          div_le_div_of_nonneg_left (by positivity) one_pos hW1
      _ ≤ C * (((Nsz sz n)⁻¹) ^ 2)⁻¹ * (2 * ((Nsz sz n)⁻¹) ^ 7) / 1 :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hζ (by positivity)) zero_le_one
      _ = 2 * ((Nsz sz n)⁻¹) ^ 4 * (C * (Nsz sz n)⁻¹) := by field_simp
      _ ≤ 2 * ((Nsz sz n)⁻¹) ^ 4 * 1 := mul_le_mul_of_nonneg_left hCu (by positivity)
      _ = 2 * ((Nsz sz n)⁻¹) ^ 4 := mul_one _
  have hE : 4 * ((Nsz sz n)⁻¹) ^ 4 + 2 * ((Nsz sz n)⁻¹) ^ 4 ≤ ((Nsz sz n)⁻¹) ^ 2 := by
    have h2 : ((Nsz sz n)⁻¹) ^ 2 ≤ 1 / 1024 := by
      have := pow_le_pow_left₀ hu0.le hu32 2
      norm_num at this ⊢; linarith
    have h4 : ((Nsz sz n)⁻¹) ^ 4 = ((Nsz sz n)⁻¹) ^ 2 * ((Nsz sz n)⁻¹) ^ 2 := by ring
    rw [h4]
    nlinarith [sq_nonneg ((Nsz sz n)⁻¹)]
  have hsplit : avg2 sz n (fun x y => if σ then BAGz sz n z ω x y * BAGz sz n z ω y x else ((‖BAGz sz n z ω x y‖ ^ 2 : ℝ) : ℂ)) a b -
        BAprof sz n z true σ a b =
      (avg2 sz n (fun x y => if σ then BAGz sz n w ω x y * BAGz sz n w ω y x else ((‖BAGz sz n w ω x y‖ ^ 2 : ℝ) : ℂ)) a b -
        BAprof sz n w true σ a b) +
        ((avg2 sz n (fun x y => if σ then BAGz sz n z ω x y * BAGz sz n z ω y x else ((‖BAGz sz n z ω x y‖ ^ 2 : ℝ) : ℂ)) a b -
          avg2 sz n (fun x y => if σ then BAGz sz n w ω x y * BAGz sz n w ω y x else ((‖BAGz sz n w ω x y‖ ^ 2 : ℝ) : ℂ)) a b) -
            (BAprof sz n z true σ a b - BAprof sz n w true σ a b)) := by ring
  have hX : ‖avg2 sz n (fun x y => if σ then BAGz sz n z ω x y * BAGz sz n z ω y x else ((‖BAGz sz n z ω x y‖ ^ 2 : ℝ) : ℂ)) a b -
        BAprof sz n z true σ a b‖ ≤
      ‖avg2 sz n (fun x y => if σ then BAGz sz n w ω x y * BAGz sz n w ω y x else ((‖BAGz sz n w ω x y‖ ^ 2 : ℝ) : ℂ)) a b -
        BAprof sz n w true σ a b‖ + (4 * ((Nsz sz n)⁻¹) ^ 4 + 2 * ((Nsz sz n)⁻¹) ^ 4) := by
    rw [hsplit]
    refine (norm_add_le _ _).trans ?_
    have := norm_sub_le (avg2 sz n (fun x y => if σ then BAGz sz n z ω x y * BAGz sz n z ω y x else ((‖BAGz sz n z ω x y‖ ^ 2 : ℝ) : ℂ)) a b -
          avg2 sz n (fun x y => if σ then BAGz sz n w ω x y * BAGz sz n w ω y x else ((‖BAGz sz n w ω x y‖ ^ 2 : ℝ) : ℂ)) a b)
        (BAprof sz n z true σ a b - BAprof sz n w true σ a b)
    linarith
  have := znet_qd_core sz n (by omega) hz.2.2 hzu hN1 hshift h5 a b hnb' hE hX
  exact absurd hab (not_lt.2 this)

/-- `baMANetQD` (analogue of `netQD`, `Main/ZNet`): the probability halves of `BAEnd_QDiffL` from the fixed-`z` form by the finite net of representatives
`MALocal_net_exists` (mesh `N^{-7}`, real range `2 + 2 d 𝔡⁻¹`), the cover lemmas at `(τ/2, D + 15)`, the union bound and the count `(4R + 2) N^{14} N^{-(D+15)} ≤ N^{-D}`;
the expectation half is the one of `BAQDiffFixed` at `(κ, ε, τ, D)` (already pointwise in `z`, no lift). -/
theorem baMANetQD (d : ℕ) : BAMANetQD d := by
  intro hFix hd 𝔠 𝔡 sz hA κ ε τ D hκ hε hτ hD
  obtain ⟨C, hC, hlip⟩ := baProf_lip κ hκ
  have hF := hFix hd 𝔠 𝔡 sz hA κ ε (τ / 2) (D + 15) hκ hε (by positivity) (by positivity)
  have hF' := hFix hd 𝔠 𝔡 sz hA κ ε τ D hκ hε hτ hD
  have h𝔡 : 0 < 𝔡 := hA.2.1
  set R : ℝ := 2 + 2 * d * 𝔡⁻¹ with hRdef
  have hR0 : 0 ≤ R := by positivity
  filter_upwards [hF, hF', MALocal_thresholds sz hA hτ (max C (4 * R + 2))] with n hn hn' hth
  obtain ⟨h32, hCN, h5, hl0, hl1⟩ := hth
  have hCN1 := le_trans (le_max_left _ _) hCN
  have hCN2 := le_trans (le_max_right _ _) hCN
  have hN1 : (1 : ℝ) ≤ Nsz sz n := by linarith
  have hh0 : 0 < Nsz sz n ^ (-7 : ℝ) := Real.rpow_pos_of_pos (by linarith) _
  have hP : ∀ z, BAendDom sz κ ε n z → |z.re| ≤ R ∧ 0 ≤ z.im ∧ z.im ≤ 1 := by
    intro z hz
    refine ⟨?_, (MALocal_endDom_im_pos hz).le, hz.2.2⟩
    have h1 := MALocal_bulk_abs_le d (sz.L n) (sz.lam n) κ z.re hκ hz.1
    rw [abs_of_nonneg hl0] at h1
    have h2 : 2 * (d : ℝ) * sz.lam n ≤ 2 * (d : ℝ) * 𝔡⁻¹ := mul_le_mul_of_nonneg_left hl1 (by positivity)
    linarith
  obtain ⟨S, hcard, hS, hcov⟩ := MALocal_net_exists (P := BAendDom sz κ ε n) hR0 hh0 hP
  have hcard' : (S.card : ℝ) ≤ (4 * R + 2) * Nsz sz n ^ (14 : ℕ) := hcard.trans (MALocal_card_le hN1 hR0)
  have hnc := MALocal_net_count (D := D) S.card (by linarith) hCN2 hcard'
  refine ⟨⟨?_, ?_⟩, fun z hz a b => (hn' z hz).2 a b⟩
  · refine le_trans (net_union_le (Sizes.seqP (sz.withLam 0)) S {ω | ∃ z : ℂ, BAendDom sz κ ε n z ∧ BAqdBadz sz τ n z ω false}
      (fun w => {ω | BAqdBadz sz (τ / 2) n w ω false}) (ENNReal.ofReal (Nsz sz n ^ (-(D + 15)))) ?_ ?_) hnc
    · intro ω hω
      obtain ⟨w, hw, hbad⟩ := MAQDiff_qdBad_net sz n hd false hε h32 hC hCN1 (hlip d sz n) h5 S hS hcov ω hω
      exact Set.mem_biUnion hw hbad
    · intro w hw
      exact (hn w (hS w hw)).1.1
  · refine le_trans (net_union_le (Sizes.seqP (sz.withLam 0)) S {ω | ∃ z : ℂ, BAendDom sz κ ε n z ∧ BAqdBadz sz τ n z ω true}
      (fun w => {ω | BAqdBadz sz (τ / 2) n w ω true}) (ENNReal.ofReal (Nsz sz n ^ (-(D + 15)))) ?_ ?_) hnc
    · intro ω hω
      obtain ⟨w, hw, hbad⟩ := MAQDiff_qdBad_net sz n hd true hε h32 hC hCN1 (hlip d sz n) h5 S hS hcov ω hω
      exact Set.mem_biUnion hw hbad
    · intro w hw
      exact (hn w (hS w hw)).1.2

end Net

/-! ## 6. `QDiff` at the block Anderson model from `UNMLOutBA d` -/

section Main

/-- `baEnd_QDiffL` (`MR:QuDiff` at the block Anderson model, Theorem 2.7 `MR:decol_BA`; `(eq:diffu1)`, `(eq:diffu2)`, `(Meq:QdS1)`, `(Meq:QdS2)`): `BAEnd_QDiffL d` from `UNMLOutBA d`
(`baMANetQD` composed with `baQDiffFixed_of_ML`). -/
theorem baEnd_QDiffL (d : ℕ) (hML : UNMLOutBA d) : BAEnd_QDiffL d :=
  baMANetQD d (baQDiffFixed_of_ML d hML)

end Main


end RBM.BA

end
