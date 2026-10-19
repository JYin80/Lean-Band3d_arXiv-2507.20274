/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.BA.TwistPins
import RBM3D.Chain.LWGen
import RBM3D.Chain.Carrier
import RBM3D.BA.FlowPins
import RBM3D.Defs.Sizes
import RBM3D.Gauss.FineModel
import RBM3D.Graph.BAExpand
import RBM3D.Graph.BAExp14a
import RBM3D.Graph.BAExp14aB
import RBM3D.Graph.LWStein
import RBM3D.Green.IBPPoly
import RBM3D.BA.GreenSchur
import RBM3D.BA.GreenLDE
import RBM3D.BA.Ward
import RBM3D.BA.MFixedPoint
import RBM3D.BA.CombesThomas

/-!
# The twisted averaged law at the block Anderson model, part A: the moment identity and the regularity facts

Proof of Lemma 8.6 (`lem:TL1_BA`, the twisted averaged law), first part: the identity for the `2p`-th moment of the twisted trace `T = twTr c₁ c₂`, from Gaussian integration by parts,
and the regularity facts.  Part B is `BA/TwistAvgA2` (the recursion for the moment, a Hölder step, and the statement `baTwistAvgRec_holds`).

Proof outline (mirror form).  `lanlw` (Lemma B.6, `baLanlw_holds`, `Graph/BAExpand`) writes
`Ǧ = -M(V + tm)G`.  It is applied with the resolvent polynomial
`f = Φ_p = T^{p-1} conj(T)^p`, `T = twTr c₁ c₂`, at `(x, π_{c₂}x)` for `x ∈ [c₁]`, transported to
`μ = seqP (sz.withLam 0)` as `BAExp14a_lanlw_diag` does for `f = 1`, and summed against the twist.
The identity obtained (`TwistAvgA_moment`) is
`𝔼|T|^{2p} = t Σ_c M_{c₁c} 𝔼[X_c (M_{cc₂} + twTr c c₂) Φ] + t(p-1) 𝔼[𝒮₁ T^{p-2} T̄^p]
+ t p 𝔼[𝒮₂ |T|^{2p-2}]` with `X_c = 𝓛^{(1)}_{+,c} - m`,
`𝒮₁ = Σ S_{αβ} (G P M)_{βα} (G P G)_{αβ}`, `𝒮₂ = Σ S_{αβ} (G P M)_{βα} conj((G P G)_{βα})`
(`twAvgS1`, `twAvgS2`; `S` without the factor `t`),
`(G P M)_{βα} = W^{-d} Σ_{w∈[c₁]} G_{β,π_{c₂}w} M_{wα}`,
`(G P G)_{αβ} = W^{-d} Σ_{w∈[c₁]} G_{α,π_{c₂}w} G_{wβ}` (`twAvgGPM`, `twAvgGPG`):
this is the mirror form, with `twTr c₁ c₂ = T̃_{(c₂,c₁)}`.

Contents: section 1 the vocabulary and the statements `BATwistAvgRec`, `twAvgReg`; section 2 twist
blocks in offset coordinates; section 3 `Φ_p` and `∂_{h_{βα}}Φ_p` at the one-size level; section 4 `lanlw`
with `f = Φ_p` at the BA law; section 5 bounded continuous functions; section 6 `twAvgReg_holds`; section 7 the twist
algebra; section 8 the moment identity `TwistAvgA_moment`.  Helpers carry the stem
`TwistAvgA_`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.setOption false
set_option linter.flexible false
set_option linter.unusedFintypeInType false

open MeasureTheory Filter
open scoped Matrix

noncomputable section

namespace RBM.BA
open RBM RBM.Path RBM.Gauss RBM.Gauss.Sizes RBM.Graph RBM.Green

/-! ## 1. Vocabulary and statements -/

section TwistAvg
variable {d : ℕ} {sz : Sizes d}

/-- `(G P M)_{βα} = W^{-d} Σ_{w ∈ [c₁]} G_{β, Π_{c₂} w} M_{wα}`, `P = P_{c₂c₁}` (so `Tr(Ǧ P) = twTr c₁ c₂`). -/
def twAvgGPM (C : FlowFM sz) (n : ℕ) (t : ℝ) (ω : sz.SeqΩ) (c₁ c₂ : Zd d (sz.L n)) (β α : Idx d (sz.L n) (sz.W n)) : ℂ :=
  (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * ∑ w ∈ twBlk n c₁, C.G n t ω β (twShift n c₂ w) * C.M n w α

/-- `(G P G)_{αβ} = W^{-d} Σ_{w ∈ [c₁]} G_{α, Π_{c₂} w} G_{wβ}`; `∂_{h_{βα}} twTr c₁ c₂ = -(G P G)_{αβ}`. -/
def twAvgGPG (C : FlowFM sz) (n : ℕ) (t : ℝ) (ω : sz.SeqΩ) (c₁ c₂ : Zd d (sz.L n)) (α β : Idx d (sz.L n) (sz.W n)) : ℂ :=
  (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * ∑ w ∈ twBlk n c₁, C.G n t ω α (twShift n c₂ w) * C.G n t ω w β

/-- `𝒮₁ = Σ_{α,β} S_{αβ} (G P M)_{βα} (G P G)_{αβ}` (mirror form), `S_{αβ} = W^{-d} S^{(B)}_{[α][β]}` (no factor `t`; `S^{(B)} = I` at BA). -/
def twAvgS1 (C : FlowFM sz) (n : ℕ) (t : ℝ) (ω : sz.SeqΩ) (c₁ c₂ : Zd d (sz.L n)) : ℂ :=
  ∑ α, ∑ β, (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * C.S n (split d (sz.L n) (sz.W n) α).1 (split d (sz.L n) (sz.W n) β).1 *
    (twAvgGPM C n t ω c₁ c₂ β α * twAvgGPG C n t ω c₁ c₂ α β)

/-- `𝒮₂ = Σ_{α,β} S_{αβ} (G P M)_{βα} conj((G P G)_{βα})` (mirror form). -/
def twAvgS2 (C : FlowFM sz) (n : ℕ) (t : ℝ) (ω : sz.SeqΩ) (c₁ c₂ : Zd d (sz.L n)) : ℂ :=
  ∑ α, ∑ β, (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * C.S n (split d (sz.L n) (sz.W n) α).1 (split d (sz.L n) (sz.W n) β).1 *
    (twAvgGPM C n t ω c₁ c₂ β α * (starRingEnd ℂ) (twAvgGPG C n t ω c₁ c₂ β α))

/-- `X_{c₁c₂} = (𝔼_μ ‖twTr … c₁ c₂‖^{2p})^{1/(2p)}`. -/
def twAvgX (C : FlowFM sz) (μ : Measure sz.SeqΩ) (n : ℕ) (t : ℝ) (p : ℕ) (c₁ c₂ : Zd d (sz.L n)) : ℝ :=
  (∫ ω, ‖twTr C n t ω c₁ c₂‖ ^ (2 * p) ∂μ) ^ ((1 : ℝ) / (2 * (p : ℝ)))

/-- `X = max_{c₁,c₂} X_{c₁c₂}` (a maximum over the `L^{2d}` ordered pairs). -/
def twAvgXmax (C : FlowFM sz) (μ : Measure sz.SeqΩ) (n : ℕ) (t : ℝ) (p : ℕ) : ℝ :=
  Finset.univ.sup' ⟨((0 : Zd d (sz.L n)), (0 : Zd d (sz.L n))), Finset.mem_univ _⟩
    fun q : Zd d (sz.L n) × Zd d (sz.L n) => twAvgX C μ n t p q.1 q.2

/-! ### The moment identity (mirror form) at the BA carrier and the BA law -/

/-! ### Continuity (measurability, integrability) and deterministic envelopes -/

/-- `twAvgReg d`: for `0 ≤ t ≤ T₀` (and `0 < κ`, `0 < ε`, `BAFlow`): `twTr`, `𝒮₁`, `𝒮₂`, `𝓛^{(1)}_c - m` are continuous in `ω` (so measurable),
`‖twTr‖^p` is integrable at `μ`, and the four are bounded by `η_t⁻¹ + 1`, resp. `N (η_t⁻¹ + 1)³` (`‖G_{xy}‖ ≤ η_t⁻¹`, `‖M_{xy}‖ ≤ 1`,
`Σ_{α,β} S_{αβ} = N`); eventually in `n`, uniformly in `t`, `η_t⁻¹ + 1 ≤ N` (`η_t ≥ η_{T₀} = (1 - T₀) Im m₀ ≥ (κ/2) N^{-1+ε}`, so
that `ε > 0` is needed), so that `‖twTr‖, ‖𝓛^{(1)}_c - m‖ ≤ N` (`Kenv = 1` of `twAvgT6`) and `‖𝒮₁‖, ‖𝒮₂‖ ≤ N^4`, `‖𝒮₁‖ + ‖𝒮₂‖ ≤ N^5` for
`N ≥ 2` (`Kenv = 5`), as used in `baTwistAvgRec_holds`. -/
def twAvgReg (d : ℕ) : Prop :=
  ∀ (κ ε 𝔠 𝔡 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), 0 < κ → 0 < ε → BAFlow sz κ ε 𝔠 𝔡 z →
    (∀ (n : ℕ) (t : ℝ), 0 ≤ t → t ≤ BAflowT0 sz z n → ∀ c₁ c₂ : Zd d (sz.L n),
      Continuous (fun ω => twTr (baFMz sz z) n t ω c₁ c₂) ∧ Continuous (fun ω => twAvgS1 (baFMz sz z) n t ω c₁ c₂) ∧
      Continuous (fun ω => twAvgS2 (baFMz sz z) n t ω c₁ c₂) ∧
      Continuous (fun ω => (baFMz sz z).L n t (fun _ : Fin 1 => true) (fun _ => c₁) ω - (baFMz sz z).m n) ∧
      ∀ p : ℕ, Integrable (fun ω => ‖twTr (baFMz sz z) n t ω c₁ c₂‖ ^ p) (Sizes.seqP (sz.withLam 0))) ∧
    (∀ (n : ℕ) (t : ℝ), 0 ≤ t → t ≤ BAflowT0 sz z n → ∀ (ω : sz.SeqΩ) (c₁ c₂ : Zd d (sz.L n)),
      ‖twTr (baFMz sz z) n t ω c₁ c₂‖ ≤ ((baFMz sz z).eta n t)⁻¹ + 1 ∧
      ‖(baFMz sz z).L n t (fun _ : Fin 1 => true) (fun _ => c₁) ω - (baFMz sz z).m n‖ ≤ ((baFMz sz z).eta n t)⁻¹ + 1 ∧
      ‖twAvgS1 (baFMz sz z) n t ω c₁ c₂‖ ≤ ((sz.size n : ℕ) : ℝ) * (((baFMz sz z).eta n t)⁻¹ + 1) ^ 3 ∧
      ‖twAvgS2 (baFMz sz z) n t ω c₁ c₂‖ ≤ ((sz.size n : ℕ) : ℝ) * (((baFMz sz z).eta n t)⁻¹ + 1) ^ 3) ∧
    ∀ᶠ n in atTop, ∀ t : ℝ, 0 ≤ t → t ≤ BAflowT0 sz z n → ((baFMz sz z).eta n t)⁻¹ + 1 ≤ ((sz.size n : ℕ) : ℝ)

/-! ### The statement `BATwistAvgRec` (the `2p`-moment recursion) -/

/-- The recursion at one carrier, law and time sequence, with the constant `K` (`= C_M` of `BAMB_row_l1`, `+ 1`) kept: for every `p ≥ 1`, `ε' > 0`, `D > 0`,
eventually in `n`, for every ordered pair `(c₁, c₂)`, `B = Bctl n (t n)`:
`X_{c₁c₂}^{2p} ≤ K W^{ε'} B (X_{c₁c₂}^{2p-1} + X X_{c₁c₂}^{2p-1}) + 2p K W^{ε'} B² X_{c₁c₂}^{2p-2} + N^{-D}`. -/
def BATwistAvgRecAt (C : FlowFM sz) (μ : Measure sz.SeqΩ) (t : ℕ → ℝ) (K : ℝ) : Prop :=
  ∀ p : ℕ, 1 ≤ p → ∀ ε' D : ℝ, 0 < ε' → 0 < D → ∀ᶠ n in atTop, ∀ c₁ c₂ : Zd d (sz.L n),
    twAvgX C μ n (t n) p c₁ c₂ ^ (2 * p) ≤
      K * (((sz.W n : ℕ) : ℝ) ^ ε' * sz.Bctl n (t n)) * (twAvgX C μ n (t n) p c₁ c₂ ^ (2 * p - 1) + twAvgXmax C μ n (t n) p * twAvgX C μ n (t n) p c₁ c₂ ^ (2 * p - 1)) +
      2 * (p : ℝ) * K * (((sz.W n : ℕ) : ℝ) ^ ε' * sz.Bctl n (t n) ^ 2) * twAvgX C μ n (t n) p c₁ c₂ ^ (2 * p - 2) + ((sz.size n : ℕ) : ℝ) ^ (-D)

/-- `BATwistAvgRec`: frame and premises of `BATwistAvgProd` (`BA/TwistPins`); the constant `K` is fixed before `𝔠, sz, z` (as in `twK_bound`). -/
def BATwistAvgRec (d : ℕ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∃ K : ℝ, 0 < K ∧ ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z →
    ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ BAflowT0 sz z n) → let μ := Sizes.seqP (sz.withLam 0)
      LWAvgLawgL (baFMz sz z) μ t → STLmaxgL (baFMz sz z) μ t → BATwistAvgRecAt (baFMz sz z) μ t K

end TwistAvg

/-! ## 2. Twist blocks in offset coordinates

`Idx d L W ≃ Zd d L × Fin (W^d)` (`splitEquiv`); the point `(c, o)` is `TwistAvgA_pt n c o`; `twShift n c x = (c, o)` with `o` the offset of `x`, `[c] = {(c, o)}`,
and `M_{(a,o),(b,o')} = 1[o = o'] M^{(B)}_{ab}` (`BAMfine_eq`). -/

section Blocks
variable {d : ℕ} {sz : Sizes d} {z : ℕ → ℂ}

/-- The point `(c, o)` of the fine lattice. -/
def TwistAvgA_pt (n : ℕ) (c : Zd d (sz.L n)) (o : Fin (sz.W n ^ d)) : Idx d (sz.L n) (sz.W n) :=
  (splitEquiv d (sz.L n) (sz.W n)).symm (c, o)

theorem TwistAvgA_split_pt (n : ℕ) (c : Zd d (sz.L n)) (o : Fin (sz.W n ^ d)) :
    split d (sz.L n) (sz.W n) (TwistAvgA_pt n c o) = (c, o) :=
  (splitEquiv d (sz.L n) (sz.W n)).apply_symm_apply _

theorem TwistAvgA_shift_eq (n : ℕ) (c : Zd d (sz.L n)) (x : Idx d (sz.L n) (sz.W n)) :
    twShift n c x = TwistAvgA_pt n c (split d (sz.L n) (sz.W n) x).2 := rfl

theorem TwistAvgA_sum_idx {β : Type*} [AddCommMonoid β] (n : ℕ) (F : Idx d (sz.L n) (sz.W n) → β) :
    ∑ x, F x = ∑ c : Zd d (sz.L n), ∑ o : Fin (sz.W n ^ d), F (TwistAvgA_pt n c o) := by
  rw [← Equiv.sum_comp (splitEquiv d (sz.L n) (sz.W n)).symm F, Fintype.sum_prod_type]
  rfl

theorem TwistAvgA_sum_blk {β : Type*} [AddCommMonoid β] (n : ℕ) (c : Zd d (sz.L n)) (F : Idx d (sz.L n) (sz.W n) → β) :
    ∑ x ∈ twBlk n c, F x = ∑ o : Fin (sz.W n ^ d), F (TwistAvgA_pt n c o) := by
  unfold twBlk
  rw [Finset.sum_filter]
  have h := TwistAvgA_sum_idx n (fun x => if (split d (sz.L n) (sz.W n) x).1 = c then F x else 0)
  rw [h]
  simp only [TwistAvgA_split_pt]
  rw [Finset.sum_eq_single c]
  · simp
  · intro c' _ hc'; simp [hc']
  · simp

theorem TwistAvgA_card_blk (n : ℕ) (c : Zd d (sz.L n)) : (twBlk n c).card = sz.W n ^ d := by
  have := card_Iblk d (sz.L n) (sz.W n) c
  exact this

/-- `M_{(a,o),(b,o')} = 1[o = o'] M^{(B)}_{ab}` at the BA carrier (`BAMfine_eq`, `twMB_ba`). -/
theorem TwistAvgA_M_pt {n : ℕ} (hm : 0 < ((baFMz sz z).m n).im) (a b : Zd d (sz.L n)) (o o' : Fin (sz.W n ^ d)) :
    (baFMz sz z).M n (TwistAvgA_pt n a o) (TwistAvgA_pt n b o') = if o = o' then twMB (baFMz sz z) n a b else 0 := by
  have h := BAMfine_eq sz (BAflowLam0 sz z) (BAflowEs sz z) n hm (TwistAvgA_pt n a o) (TwistAvgA_pt n b o')
  have e := congrFun (congrFun (twMB_ba z n hm) a) b
  change BAMfine sz (BAflowLam0 sz z) (BAflowEs sz z) n (TwistAvgA_pt n a o) (TwistAvgA_pt n b o') = _
  rw [h, TwistAvgA_split_pt, TwistAvgA_split_pt, e]

/-- `Σ_α M_{xα} F(α)` for `x = (c₁, o)`: one point of each block `c` (the offset of `x`), weight `M^{(B)}_{c₁c}`. -/
theorem TwistAvgA_sum_M {n : ℕ} (hm : 0 < ((baFMz sz z).m n).im) (c₁ : Zd d (sz.L n)) (o : Fin (sz.W n ^ d))
    (F : Idx d (sz.L n) (sz.W n) → ℂ) :
    ∑ α, (baFMz sz z).M n (TwistAvgA_pt n c₁ o) α * F α = ∑ c, twMB (baFMz sz z) n c₁ c * F (TwistAvgA_pt n c o) := by
  rw [TwistAvgA_sum_idx]
  refine Finset.sum_congr rfl fun c _ => ?_
  simp only [TwistAvgA_M_pt hm, ite_mul, zero_mul]
  rw [Finset.sum_ite_eq]
  simp

end Blocks

/-! ## 3. The resolvent polynomial `Φ_p = T^{p-1} conj(T)^p` and `∂_{h_{βα}} Φ_p` at the one-size level

The objects of `Graph/BAExpand` (`BAlwG`, `BAlwf`, `BAlwdf`, `Ω d L W`) carry no `Sizes`: the polynomial `Φ_p` is a resolvent polynomial over `Idx d L W` and
`∂_{h_{βα}}` is the complex derivative of `LWPins_dH`, computed with `lwWx_hasDerivAt_Gres`. -/

section PF
variable (d L W : ℕ) [NeZero L] [NeZero W]

/-- The offset-preserving shift into the block `c` (`twShift`, at the one-size level). -/
def TwistAvgA_sh (c : Zd d L) (x : Idx d L W) : Idx d L W :=
  (splitEquiv d L W).symm (c, (split d L W x).2)

/-- `T = W^{-d} Σ_{w ∈ [c₁]} Ǧ_{w,Π_{c₂}w}` as a resolvent polynomial. -/
def TwistAvgA_Tpol (Mm : Idx d L W → Idx d L W → ℂ) (c₁ c₂ : Zd d L) : MvPolynomial (Bool × Idx d L W × Idx d L W) ℂ :=
  MvPolynomial.C (((W : ℂ) ^ d)⁻¹) * ∑ w ∈ Iblk d L W c₁,
    (MvPolynomial.X (true, w, TwistAvgA_sh d L W c₂ w) - MvPolynomial.C (Mm w (TwistAvgA_sh d L W c₂ w)))

/-- `conj T` as a resolvent polynomial: the variable `(false, a, b)` is `(G^*)_{ab} = conj G_{ba}`. -/
def TwistAvgA_Tbpol (Mm : Idx d L W → Idx d L W → ℂ) (c₁ c₂ : Zd d L) : MvPolynomial (Bool × Idx d L W × Idx d L W) ℂ :=
  MvPolynomial.C ((starRingEnd ℂ) (((W : ℂ) ^ d)⁻¹)) * ∑ w ∈ Iblk d L W c₁,
    (MvPolynomial.X (false, TwistAvgA_sh d L W c₂ w, w) - MvPolynomial.C ((starRingEnd ℂ) (Mm w (TwistAvgA_sh d L W c₂ w))))

/-- `Φ_p = T^{p-1} conj(T)^p`. -/
def TwistAvgA_Phi (Mm : Idx d L W → Idx d L W → ℂ) (c₁ c₂ : Zd d L) (p : ℕ) : MvPolynomial (Bool × Idx d L W × Idx d L W) ℂ :=
  TwistAvgA_Tpol d L W Mm c₁ c₂ ^ (p - 1) * TwistAvgA_Tbpol d L W Mm c₁ c₂ ^ p

variable (g0 E t : ℝ) (m : ℂ)

/-- `T` at the sample `ω'` of the one-size law. -/
def TwistAvgA_That (c₁ c₂ : Zd d L) (ω' : Ω d L W) : ℂ :=
  (((W : ℂ) ^ d)⁻¹) * ∑ w ∈ Iblk d L W c₁, BAlwGc d L W g0 E t m ω' w (TwistAvgA_sh d L W c₂ w)

/-- `(G P G)_{αβ} = W^{-d} Σ_{w ∈ [c₁]} G_{α,Π_{c₂}w} G_{wβ}` at the one-size level. -/
def TwistAvgA_GPG (c₁ c₂ : Zd d L) (ω' : Ω d L W) (α β : Idx d L W) : ℂ :=
  (((W : ℂ) ^ d)⁻¹) * ∑ w ∈ Iblk d L W c₁, BAlwG d L W g0 E t m ω' α (TwistAvgA_sh d L W c₂ w) * BAlwG d L W g0 E t m ω' w β

theorem TwistAvgA_herm (ω' : Ω d L W) : (BAlwH d L W g0 t ω').IsHermitian := by
  have h1 : ((g0 : ℂ) • PsiI d L W).IsHermitian := by
    unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose_smul, (PsiI_isHermitian d L W).eq, show star (g0 : ℂ) = (g0 : ℂ) from Complex.conj_ofReal _]
  exact h1.add (Hflow_isHermitian d L W t ω')

theorem TwistAvgA_f_T (ω' : Ω d L W) (c₁ c₂ : Zd d L) :
    BAlwf d L W g0 E t m (TwistAvgA_Tpol d L W (BAlwM d L W g0 E m) c₁ c₂) ω' = TwistAvgA_That d L W g0 E t m c₁ c₂ ω' := by
  simp [BAlwf, LWPins_resPoly, TwistAvgA_Tpol, TwistAvgA_That, BAlwGc, BAlwG, Finset.sum_sub_distrib]

theorem TwistAvgA_f_Tb (ω' : Ω d L W) (c₁ c₂ : Zd d L) :
    BAlwf d L W g0 E t m (TwistAvgA_Tbpol d L W (BAlwM d L W g0 E m) c₁ c₂) ω' =
      (starRingEnd ℂ) (TwistAvgA_That d L W g0 E t m c₁ c₂ ω') := by
  have hH := TwistAvgA_herm d L W g0 t ω'
  simp only [BAlwf, LWPins_resPoly, TwistAvgA_Tbpol, TwistAvgA_That, BAlwGc, BAlwG, map_mul, map_sum, map_sub,
    MvPolynomial.eval_C, MvPolynomial.eval_X]
  congr 1
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [lwWx_Gres_false hH]
  rfl


theorem TwistAvgA_f_mul (P Q : MvPolynomial (Bool × Idx d L W × Idx d L W) ℂ) (ω' : Ω d L W) :
    BAlwf d L W g0 E t m (P * Q) ω' = BAlwf d L W g0 E t m P ω' * BAlwf d L W g0 E t m Q ω' := by
  simp [BAlwf, LWPins_resPoly, map_mul]

theorem TwistAvgA_f_pow (P : MvPolynomial (Bool × Idx d L W × Idx d L W) ℂ) (k : ℕ) (ω' : Ω d L W) :
    BAlwf d L W g0 E t m (P ^ k) ω' = BAlwf d L W g0 E t m P ω' ^ k := by
  simp [BAlwf, LWPins_resPoly, map_pow]

theorem TwistAvgA_f_Phi (ω' : Ω d L W) (c₁ c₂ : Zd d L) (p : ℕ) :
    BAlwf d L W g0 E t m (TwistAvgA_Phi d L W (BAlwM d L W g0 E m) c₁ c₂ p) ω' =
      TwistAvgA_That d L W g0 E t m c₁ c₂ ω' ^ (p - 1) * (starRingEnd ℂ) (TwistAvgA_That d L W g0 E t m c₁ c₂ ω') ^ p := by
  unfold TwistAvgA_Phi
  rw [TwistAvgA_f_mul, TwistAvgA_f_pow, TwistAvgA_f_pow, TwistAvgA_f_T, TwistAvgA_f_Tb]

/-- `∂_{h_{βα}} Φ_p` (mirror form): `∂T = -(G P G)_{αβ}`, `∂ T̄ = -conj((G P G)_{βα})`. -/
theorem TwistAvgA_dH_Phi (hz : (ztOf m E t).im ≠ 0) (ω' : Ω d L W) (c₁ c₂ : Zd d L) (p : ℕ) (β α : Idx d L W) :
    BAlwdf d L W g0 E t m (TwistAvgA_Phi d L W (BAlwM d L W g0 E m) c₁ c₂ p) ω' β α =
      ((p - 1 : ℕ) : ℂ) * TwistAvgA_That d L W g0 E t m c₁ c₂ ω' ^ (p - 1 - 1) * (-(TwistAvgA_GPG d L W g0 E t m c₁ c₂ ω' α β)) *
          (starRingEnd ℂ) (TwistAvgA_That d L W g0 E t m c₁ c₂ ω') ^ p +
        TwistAvgA_That d L W g0 E t m c₁ c₂ ω' ^ (p - 1) * ((p : ℂ) * (starRingEnd ℂ) (TwistAvgA_That d L W g0 E t m c₁ c₂ ω') ^ (p - 1) *
          (-((starRingEnd ℂ) (TwistAvgA_GPG d L W g0 E t m c₁ c₂ ω' β α)))) := by
  have hH := TwistAvgA_herm d L W g0 t ω'
  set H := BAlwH d L W g0 t ω' with hHdef
  set zz := ztOf m E t with hzz
  have hd : ∀ (σ : Bool) (a b : Idx d L W), HasDerivAt (fun s : ℂ => Gres (H + s • Matrix.single β α (1 : ℂ)) zz σ a b)
      (-(Gres H zz σ a β * Gres H zz σ α b)) 0 :=
    fun σ a b => lwWx_hasDerivAt_Gres hH hz σ β α a b
  set Ts : ℂ → ℂ := fun s => (((W : ℂ) ^ d)⁻¹) * ∑ w ∈ Iblk d L W c₁, (Gres (H + s • Matrix.single β α (1 : ℂ)) zz true w (TwistAvgA_sh d L W c₂ w) -
          BAlwM d L W g0 E m w (TwistAvgA_sh d L W c₂ w)) with hTsdef
  set Tbs : ℂ → ℂ := fun s => ((starRingEnd ℂ) (((W : ℂ) ^ d)⁻¹)) * ∑ w ∈ Iblk d L W c₁, (Gres (H + s • Matrix.single β α (1 : ℂ)) zz false (TwistAvgA_sh d L W c₂ w) w -
          (starRingEnd ℂ) (BAlwM d L W g0 E m w (TwistAvgA_sh d L W c₂ w))) with hTbsdef
  have hTs : HasDerivAt Ts ((((W : ℂ) ^ d)⁻¹) * ∑ w ∈ Iblk d L W c₁, -(Gres H zz true w β * Gres H zz true α (TwistAvgA_sh d L W c₂ w))) 0 :=
    HasDerivAt.const_mul _ (HasDerivAt.fun_sum (u := Iblk d L W c₁) (fun w _ => (hd true w (TwistAvgA_sh d L W c₂ w)).sub_const _))
  have hTb : HasDerivAt Tbs (((starRingEnd ℂ) (((W : ℂ) ^ d)⁻¹)) * ∑ w ∈ Iblk d L W c₁,
      -(Gres H zz false (TwistAvgA_sh d L W c₂ w) β * Gres H zz false α w)) 0 :=
    HasDerivAt.const_mul _ (HasDerivAt.fun_sum (u := Iblk d L W c₁) (fun w _ => (hd false (TwistAvgA_sh d L W c₂ w) w).sub_const _))
  have hfun : (fun s : ℂ => LWPins_resPoly d L W zz (TwistAvgA_Phi d L W (BAlwM d L W g0 E m) c₁ c₂ p) (H + s • Matrix.single β α (1 : ℂ))) =
      fun s => Ts s ^ (p - 1) * Tbs s ^ p := by
    funext s
    simp only [LWPins_resPoly, TwistAvgA_Phi, TwistAvgA_Tpol, TwistAvgA_Tbpol, map_mul, map_pow, map_sum, map_sub,
      MvPolynomial.eval_C, MvPolynomial.eval_X, hTsdef, hTbsdef]
  have hTs0 : Ts 0 = TwistAvgA_That d L W g0 E t m c₁ c₂ ω' := by
    simp [hTsdef, TwistAvgA_That, BAlwGc, BAlwG, hHdef, hzz, Finset.sum_sub_distrib]
  have hTb0 : Tbs 0 = (starRingEnd ℂ) (TwistAvgA_That d L W g0 E t m c₁ c₂ ω') := by
    rw [← TwistAvgA_f_Tb d L W g0 E t m ω' c₁ c₂]
    simp only [BAlwf, LWPins_resPoly, TwistAvgA_Tbpol, map_mul, map_sum, map_sub, MvPolynomial.eval_C, MvPolynomial.eval_X, hTbsdef,
      zero_smul, add_zero]
    rfl
  have hTs' : (((W : ℂ) ^ d)⁻¹) * ∑ w ∈ Iblk d L W c₁, -(Gres H zz true w β * Gres H zz true α (TwistAvgA_sh d L W c₂ w)) =
      -(TwistAvgA_GPG d L W g0 E t m c₁ c₂ ω' α β) := by
    simp only [TwistAvgA_GPG, BAlwG, Finset.sum_neg_distrib, mul_neg]
    congr 2
    exact Finset.sum_congr rfl fun w _ => mul_comm _ _
  have hTb' : ((starRingEnd ℂ) (((W : ℂ) ^ d)⁻¹)) * ∑ w ∈ Iblk d L W c₁, -(Gres H zz false (TwistAvgA_sh d L W c₂ w) β * Gres H zz false α w) =
      -((starRingEnd ℂ) (TwistAvgA_GPG d L W g0 E t m c₁ c₂ ω' β α)) := by
    simp only [TwistAvgA_GPG, BAlwG, Finset.sum_neg_distrib, mul_neg, map_mul, map_sum]
    congr 2
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [lwWx_Gres_false hH, lwWx_Gres_false hH]
    simp only [Complex.star_def]
    rfl
  unfold BAlwdf LWPins_dH
  rw [hfun]
  have hder := ((hTs.pow (p - 1)).mul (hTb.pow p)).deriv
  refine hder.trans ?_
  simp only [Pi.pow_apply, hTs0, hTb0, hTs', hTb']

end PF

/-! ## 4. `lanlw` with `f = Φ_p`: continuity at the one-size level and the transport to the BA law -/

section PFcont
variable (d L W : ℕ) [NeZero L] [NeZero W] (g0 E t : ℝ) (m : ℂ)

theorem TwistAvgA_cont_That (hz : (ztOf m E t).im ≠ 0) (c₁ c₂ : Zd d L) :
    Continuous (TwistAvgA_That d L W g0 E t m c₁ c₂) := by
  have := fun x y => BAExp14a_cont_lwG (d := d) (L := L) (W := W) (g0 := g0) (E := E) (t := t) (m := m) hz x y
  unfold TwistAvgA_That BAlwGc
  fun_prop

theorem TwistAvgA_cont_GPG (hz : (ztOf m E t).im ≠ 0) (c₁ c₂ : Zd d L) (α β : Idx d L W) :
    Continuous (fun ω' : Ω d L W => TwistAvgA_GPG d L W g0 E t m c₁ c₂ ω' α β) := by
  have := fun x y => BAExp14a_cont_lwG (d := d) (L := L) (W := W) (g0 := g0) (E := E) (t := t) (m := m) hz x y
  unfold TwistAvgA_GPG
  fun_prop

theorem TwistAvgA_cont_f_Phi (hz : (ztOf m E t).im ≠ 0) (c₁ c₂ : Zd d L) (p : ℕ) :
    Continuous (BAlwf d L W g0 E t m (TwistAvgA_Phi d L W (BAlwM d L W g0 E m) c₁ c₂ p)) := by
  have h := TwistAvgA_cont_That d L W g0 E t m hz c₁ c₂
  have e : BAlwf d L W g0 E t m (TwistAvgA_Phi d L W (BAlwM d L W g0 E m) c₁ c₂ p) = fun ω' =>
      TwistAvgA_That d L W g0 E t m c₁ c₂ ω' ^ (p - 1) * (starRingEnd ℂ) (TwistAvgA_That d L W g0 E t m c₁ c₂ ω') ^ p :=
    funext fun ω' => TwistAvgA_f_Phi d L W g0 E t m ω' c₁ c₂ p
  rw [e]
  fun_prop

theorem TwistAvgA_cont_df_Phi (hz : (ztOf m E t).im ≠ 0) (c₁ c₂ : Zd d L) (p : ℕ) (β α : Idx d L W) :
    Continuous (fun ω' : Ω d L W => BAlwdf d L W g0 E t m (TwistAvgA_Phi d L W (BAlwM d L W g0 E m) c₁ c₂ p) ω' β α) := by
  have h := TwistAvgA_cont_That d L W g0 E t m hz c₁ c₂
  have h1 := TwistAvgA_cont_GPG d L W g0 E t m hz c₁ c₂ α β
  have h2 := TwistAvgA_cont_GPG d L W g0 E t m hz c₁ c₂ β α
  have e : (fun ω' : Ω d L W => BAlwdf d L W g0 E t m (TwistAvgA_Phi d L W (BAlwM d L W g0 E m) c₁ c₂ p) ω' β α) = fun ω' =>
      ((p - 1 : ℕ) : ℂ) * TwistAvgA_That d L W g0 E t m c₁ c₂ ω' ^ (p - 1 - 1) * (-(TwistAvgA_GPG d L W g0 E t m c₁ c₂ ω' α β)) *
          (starRingEnd ℂ) (TwistAvgA_That d L W g0 E t m c₁ c₂ ω') ^ p +
        TwistAvgA_That d L W g0 E t m c₁ c₂ ω' ^ (p - 1) * ((p : ℂ) * (starRingEnd ℂ) (TwistAvgA_That d L W g0 E t m c₁ c₂ ω') ^ (p - 1) *
          (-((starRingEnd ℂ) (TwistAvgA_GPG d L W g0 E t m c₁ c₂ ω' β α)))) :=
    funext fun ω' => TwistAvgA_dH_Phi d L W g0 E t m hz ω' c₁ c₂ p β α
  rw [e]
  fun_prop

end PFcont

section Transport
variable {d : ℕ} {sz : Sizes d} {z : ℕ → ℂ} {κ ε 𝔠 𝔡 : ℝ}

/-- `lanlw` with `f = Φ_p` at the BA law: the transport of `baLanlw_holds` (`Graph/BAExpand`) from `PF d L W 0` to
`μ = seqP (sz.withLam 0)`, as `BAExp14a_lanlw_diag` (`Graph/BAExp14aB`) does for `f = 1`. -/
theorem TwistAvgA_lanlw (hκ : 0 < κ) (hflow : BAFlow sz κ ε 𝔠 𝔡 z) (n : ℕ) {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ BAflowT0 sz z n)
    (c₁ c₂ : Zd d (sz.L n)) (p : ℕ) (x y : Idx d (sz.L n) (sz.W n)) :
    ∫ ω, BAlanlwL d (sz.L n) (sz.W n) (BAflowLam0 sz z n) (BAflowEs sz z n) t (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n)
        (TwistAvgA_Phi d (sz.L n) (sz.W n) (BAlwM d (sz.L n) (sz.W n) (BAflowLam0 sz z n) (BAflowEs sz z n) (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n)) c₁ c₂ p)
        x y (BAExp14a_slc sz n ω) ∂(BAExp14a_μ sz) =
      ∫ ω, BAlanlwR d (sz.L n) (sz.W n) (BAflowLam0 sz z n) (BAflowEs sz z n) t (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n)
        (TwistAvgA_Phi d (sz.L n) (sz.W n) (BAlwM d (sz.L n) (sz.W n) (BAflowLam0 sz z n) (BAflowEs sz z n) (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n)) c₁ c₂ p)
        x y (BAExp14a_slc sz n ω) ∂(BAExp14a_μ sz) := by
  obtain ⟨ht1, hr, hmi, hzi, -⟩ := ba_G_data hκ sz hflow n ht0 ht
  have hz : (ztOf (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) (BAflowEs sz z n) t).im ≠ 0 := hzi.ne'
  have hSelf := (BAflow_real κ ε 𝔠 𝔡 sz z hflow n).1
  have key := baLanlw_holds d (sz.L n) (sz.W n) (sz.three_le_L n) (BAflowLam0 sz z n) (BAflowEs sz z n) t
    (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) hSelf ht0 ht1
    (TwistAvgA_Phi d (sz.L n) (sz.W n) (BAlwM d (sz.L n) (sz.W n) (BAflowLam0 sz z n) (BAflowEs sz z n) (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n)) c₁ c₂ p) x y
  have cG := fun α β => BAExp14a_cont_lwG (d := d) (L := sz.L n) (W := sz.W n) (g0 := BAflowLam0 sz z n) (E := BAflowEs sz z n) (t := t)
    (m := BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) hz α β
  have cf := TwistAvgA_cont_f_Phi d (sz.L n) (sz.W n) (BAflowLam0 sz z n) (BAflowEs sz z n) t (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) hz c₁ c₂ p
  have cdf := TwistAvgA_cont_df_Phi d (sz.L n) (sz.W n) (BAflowLam0 sz z n) (BAflowEs sz z n) t (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) hz c₁ c₂ p
  have cL : Continuous fun ω' : Ω d (sz.L n) (sz.W n) => BAlanlwL d (sz.L n) (sz.W n) (BAflowLam0 sz z n) (BAflowEs sz z n) t
      (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n)
      (TwistAvgA_Phi d (sz.L n) (sz.W n) (BAlwM d (sz.L n) (sz.W n) (BAflowLam0 sz z n) (BAflowEs sz z n) (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n)) c₁ c₂ p) x y ω' := by
    unfold BAlanlwL BAlwGc
    exact ((cG x y).sub continuous_const).mul cf
  have cR : Continuous fun ω' : Ω d (sz.L n) (sz.W n) => BAlanlwR d (sz.L n) (sz.W n) (BAflowLam0 sz z n) (BAflowEs sz z n) t
      (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n)
      (TwistAvgA_Phi d (sz.L n) (sz.W n) (BAlwM d (sz.L n) (sz.W n) (BAflowLam0 sz z n) (BAflowEs sz z n) (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n)) c₁ c₂ p) x y ω' := by
    unfold BAlanlwR BAlwGc
    fun_prop
  rw [BAExp14a_int_slice n _ cL, BAExp14a_int_slice n _ cR]
  exact key

end Transport

/-! ## 5. Bounded continuous functions on the sample space (integrability) -/

section BC
variable {d : ℕ} {sz : Sizes d}

/-- Continuous and bounded functions on the sample space. -/
def TwistAvgA_BC (F : sz.SeqΩ → ℂ) : Prop := Continuous F ∧ ∃ C : ℝ, ∀ ω, ‖F ω‖ ≤ C

theorem TwistAvgA_BC.const (c : ℂ) : TwistAvgA_BC (sz := sz) (fun _ => c) := ⟨continuous_const, ‖c‖, fun _ => le_rfl⟩

theorem TwistAvgA_BC.add {f g : sz.SeqΩ → ℂ} (hf : TwistAvgA_BC f) (hg : TwistAvgA_BC g) : TwistAvgA_BC (fun ω => f ω + g ω) := by
  obtain ⟨hf1, Cf, hf2⟩ := hf
  obtain ⟨hg1, Cg, hg2⟩ := hg
  exact ⟨hf1.add hg1, Cf + Cg, fun ω => (norm_add_le _ _).trans (add_le_add (hf2 ω) (hg2 ω))⟩

theorem TwistAvgA_BC.neg {f : sz.SeqΩ → ℂ} (hf : TwistAvgA_BC f) : TwistAvgA_BC (fun ω => -f ω) := by
  obtain ⟨hf1, Cf, hf2⟩ := hf
  exact ⟨hf1.neg, Cf, fun ω => by simpa using hf2 ω⟩

theorem TwistAvgA_BC.sub {f g : sz.SeqΩ → ℂ} (hf : TwistAvgA_BC f) (hg : TwistAvgA_BC g) : TwistAvgA_BC (fun ω => f ω - g ω) := by
  simpa [sub_eq_add_neg] using hf.add hg.neg

theorem TwistAvgA_BC.mul {f g : sz.SeqΩ → ℂ} (hf : TwistAvgA_BC f) (hg : TwistAvgA_BC g) : TwistAvgA_BC (fun ω => f ω * g ω) := by
  obtain ⟨hf1, Cf, hf2⟩ := hf
  obtain ⟨hg1, Cg, hg2⟩ := hg
  refine ⟨hf1.mul hg1, Cf * Cg, fun ω => ?_⟩
  rw [norm_mul]
  exact mul_le_mul (hf2 ω) (hg2 ω) (norm_nonneg _) ((norm_nonneg _).trans (hf2 ω))

theorem TwistAvgA_BC.conj {f : sz.SeqΩ → ℂ} (hf : TwistAvgA_BC f) : TwistAvgA_BC (fun ω => (starRingEnd ℂ) (f ω)) := by
  obtain ⟨hf1, Cf, hf2⟩ := hf
  exact ⟨Complex.continuous_conj.comp hf1, Cf, fun ω => by simpa using hf2 ω⟩

theorem TwistAvgA_BC.pow {f : sz.SeqΩ → ℂ} (hf : TwistAvgA_BC f) (k : ℕ) : TwistAvgA_BC (fun ω => f ω ^ k) := by
  induction k with
  | zero => simpa using TwistAvgA_BC.const (sz := sz) 1
  | succ k ih => simpa [pow_succ] using ih.mul hf

theorem TwistAvgA_BC.sum {ι : Type*} (s : Finset ι) {F : ι → sz.SeqΩ → ℂ} (h : ∀ i ∈ s, TwistAvgA_BC (F i)) :
    TwistAvgA_BC (fun ω => ∑ i ∈ s, F i ω) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using TwistAvgA_BC.const (sz := sz) 0
  | insert i₀ s hi₀ ih =>
    have h₀ := h i₀ (Finset.mem_insert_self _ _)
    have hs := ih fun i hi => h i (Finset.mem_insert_of_mem hi)
    simpa [Finset.sum_insert hi₀] using h₀.add hs

theorem TwistAvgA_BC.integrable {f : sz.SeqΩ → ℂ} (hf : TwistAvgA_BC f) : Integrable f (BAExp14a_μ sz) := by
  obtain ⟨hf1, C, hf2⟩ := hf
  exact BAExp14a_integrable hf1 hf2

end BC

/-! ## 6. Continuity, integrability and the deterministic envelopes -/

section Reg
variable {d : ℕ} {sz : Sizes d} {z : ℕ → ℂ} {κ ε 𝔠 𝔡 : ℝ}

theorem TwistAvgA_M_le_one (hκ : 0 < κ) (hflow : BAFlow sz κ ε 𝔠 𝔡 z) (n : ℕ) {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ BAflowT0 sz z n)
    (x y : Idx d (sz.L n) (sz.W n)) : ‖(baFMz sz z).M n x y‖ ≤ 1 :=
  (ba_G_data hκ sz hflow n ht0 ht).2.2.2.2.2 x y

theorem TwistAvgA_GM_le (hκ : 0 < κ) (hflow : BAFlow sz κ ε 𝔠 𝔡 z) (n : ℕ) {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ BAflowT0 sz z n)
    (ω : sz.SeqΩ) (x y : Idx d (sz.L n) (sz.W n)) : ‖(baFMz sz z).GM n t ω x y‖ ≤ ((baFMz sz z).eta n t)⁻¹ + 1 :=
  (norm_sub_le _ _).trans (add_le_add (BAExp14a_G_le hκ hflow n ht0 ht ω x y) (TwistAvgA_M_le_one hκ hflow n ht0 ht x y))

theorem TwistAvgA_norm_avg {n : ℕ} (c : Zd d (sz.L n)) (F : Idx d (sz.L n) (sz.W n) → ℂ) {B : ℝ} (hF : ∀ w, ‖F w‖ ≤ B) :
    ‖(((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * ∑ w ∈ twBlk n c, F w‖ ≤ B := by
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) ^ d := by have := sz.W_pos n; positivity
  rw [norm_mul, norm_inv, norm_pow, Complex.norm_natCast]
  calc (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * ‖∑ w ∈ twBlk n c, F w‖ ≤ (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * ∑ w ∈ twBlk n c, B :=
        mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (Finset.sum_le_sum fun w _ => hF w)) (by positivity)
    _ = B := by
        rw [Finset.sum_const, TwistAvgA_card_blk, nsmul_eq_mul]; push_cast; field_simp

theorem TwistAvgA_twTr_le (hκ : 0 < κ) (hflow : BAFlow sz κ ε 𝔠 𝔡 z) (n : ℕ) {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ BAflowT0 sz z n)
    (ω : sz.SeqΩ) (c₁ c₂ : Zd d (sz.L n)) : ‖twTr (baFMz sz z) n t ω c₁ c₂‖ ≤ ((baFMz sz z).eta n t)⁻¹ + 1 :=
  TwistAvgA_norm_avg c₁ _ fun w => TwistAvgA_GM_le hκ hflow n ht0 ht ω w _

theorem TwistAvgA_X_le (hκ : 0 < κ) (hflow : BAFlow sz κ ε 𝔠 𝔡 z) (n : ℕ) {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ BAflowT0 sz z n)
    (ω : sz.SeqΩ) (c : Zd d (sz.L n)) : ‖BAExp14a_X sz z n t ω c‖ ≤ ((baFMz sz z).eta n t)⁻¹ + 1 :=
  TwistAvgA_norm_avg c _ fun w => TwistAvgA_GM_le hκ hflow n ht0 ht ω w w

theorem TwistAvgA_GPM_le (hκ : 0 < κ) (hflow : BAFlow sz κ ε 𝔠 𝔡 z) (n : ℕ) {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ BAflowT0 sz z n)
    (ω : sz.SeqΩ) (c₁ c₂ : Zd d (sz.L n)) (β α : Idx d (sz.L n) (sz.W n)) :
    ‖twAvgGPM (baFMz sz z) n t ω c₁ c₂ β α‖ ≤ ((baFMz sz z).eta n t)⁻¹ := by
  have hη := BAExp14a_eta_pos hκ hflow n ht0 ht
  refine TwistAvgA_norm_avg c₁ _ fun w => ?_
  rw [norm_mul]
  calc ‖(baFMz sz z).G n t ω β (twShift n c₂ w)‖ * ‖(baFMz sz z).M n w α‖ ≤ ((baFMz sz z).eta n t)⁻¹ * 1 :=
        mul_le_mul (BAExp14a_G_le hκ hflow n ht0 ht ω _ _) (TwistAvgA_M_le_one hκ hflow n ht0 ht _ _) (norm_nonneg _) (inv_nonneg.2 hη.le)
    _ = _ := mul_one _

theorem TwistAvgA_GPG_le (hκ : 0 < κ) (hflow : BAFlow sz κ ε 𝔠 𝔡 z) (n : ℕ) {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ BAflowT0 sz z n)
    (ω : sz.SeqΩ) (c₁ c₂ : Zd d (sz.L n)) (α β : Idx d (sz.L n) (sz.W n)) :
    ‖twAvgGPG (baFMz sz z) n t ω c₁ c₂ α β‖ ≤ (((baFMz sz z).eta n t)⁻¹) ^ 2 := by
  have hη := BAExp14a_eta_pos hκ hflow n ht0 ht
  refine TwistAvgA_norm_avg c₁ _ fun w => ?_
  rw [norm_mul, sq]
  exact mul_le_mul (BAExp14a_G_le hκ hflow n ht0 ht ω _ _) (BAExp14a_G_le hκ hflow n ht0 ht ω _ _) (norm_nonneg _) (inv_nonneg.2 hη.le)

/-- `Σ_{α,β} ‖W^{-d} S^{(B)}_{[α][β]}‖ = N` at the BA carrier (`S^{(B)} = I`). -/
theorem TwistAvgA_S_sum (n : ℕ) :
    ∑ α : Idx d (sz.L n) (sz.W n), ∑ β : Idx d (sz.L n) (sz.W n),
      ‖(((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * (baFMz sz z).S n (split d (sz.L n) (sz.W n) α).1 (split d (sz.L n) (sz.W n) β).1‖ =
      ((sz.size n : ℕ) : ℝ) := by
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) ^ d := by have := sz.W_pos n; positivity
  have h1 : ∀ α β : Idx d (sz.L n) (sz.W n),
      ‖(((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * (baFMz sz z).S n (split d (sz.L n) (sz.W n) α).1 (split d (sz.L n) (sz.W n) β).1‖ =
        (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (if (split d (sz.L n) (sz.W n) α).1 = (split d (sz.L n) (sz.W n) β).1 then 1 else 0) := by
    intro α β
    change ‖(((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * (1 : Matrix (Zd d (sz.L n)) (Zd d (sz.L n)) ℂ) _ _‖ = _
    rw [Matrix.one_apply, norm_mul, norm_inv, norm_pow, Complex.norm_natCast]
    split_ifs <;> simp
  simp only [h1]
  have h2 : ∀ α : Idx d (sz.L n) (sz.W n), ∑ β : Idx d (sz.L n) (sz.W n),
      (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (if (split d (sz.L n) (sz.W n) α).1 = (split d (sz.L n) (sz.W n) β).1 then (1 : ℝ) else 0) = 1 := by
    intro α
    rw [← Finset.mul_sum, Finset.sum_boole]
    have : (Finset.univ.filter fun β : Idx d (sz.L n) (sz.W n) => (split d (sz.L n) (sz.W n) α).1 = (split d (sz.L n) (sz.W n) β).1) =
        Iblk d (sz.L n) (sz.W n) (split d (sz.L n) (sz.W n) α).1 := by
      ext β; simp [Iblk, eq_comm]
    rw [this, card_Iblk]
    push_cast
    field_simp
  simp only [h2]
  rw [Finset.sum_const, Finset.card_univ, sz.card_Idx n, nsmul_eq_mul, mul_one]

theorem TwistAvgA_S1_le (hκ : 0 < κ) (hflow : BAFlow sz κ ε 𝔠 𝔡 z) (n : ℕ) {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ BAflowT0 sz z n)
    (ω : sz.SeqΩ) (c₁ c₂ : Zd d (sz.L n)) :
    ‖twAvgS1 (baFMz sz z) n t ω c₁ c₂‖ ≤ ((sz.size n : ℕ) : ℝ) * (((baFMz sz z).eta n t)⁻¹ + 1) ^ 3 := by
  have hη := BAExp14a_eta_pos hκ hflow n ht0 ht
  set a := ((baFMz sz z).eta n t)⁻¹ with ha
  have ha0 : 0 ≤ a := inv_nonneg.2 hη.le
  have hterm : ∀ α β : Idx d (sz.L n) (sz.W n),
      ‖(((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * (baFMz sz z).S n (split d (sz.L n) (sz.W n) α).1 (split d (sz.L n) (sz.W n) β).1 *
        (twAvgGPM (baFMz sz z) n t ω c₁ c₂ β α * twAvgGPG (baFMz sz z) n t ω c₁ c₂ α β)‖ ≤
      ‖(((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * (baFMz sz z).S n (split d (sz.L n) (sz.W n) α).1 (split d (sz.L n) (sz.W n) β).1‖ * (a * a ^ 2) := by
    intro α β
    rw [norm_mul (_ * _), norm_mul (twAvgGPM _ _ _ _ _ _ _ _)]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    exact mul_le_mul (TwistAvgA_GPM_le hκ hflow n ht0 ht ω c₁ c₂ β α) (TwistAvgA_GPG_le hκ hflow n ht0 ht ω c₁ c₂ α β) (norm_nonneg _) ha0
  calc ‖twAvgS1 (baFMz sz z) n t ω c₁ c₂‖ ≤ ∑ α : Idx d (sz.L n) (sz.W n), ∑ β : Idx d (sz.L n) (sz.W n),
        ‖(((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * (baFMz sz z).S n (split d (sz.L n) (sz.W n) α).1 (split d (sz.L n) (sz.W n) β).1 *
          (twAvgGPM (baFMz sz z) n t ω c₁ c₂ β α * twAvgGPG (baFMz sz z) n t ω c₁ c₂ α β)‖ :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun α _ => norm_sum_le _ _)
    _ ≤ ∑ α : Idx d (sz.L n) (sz.W n), ∑ β : Idx d (sz.L n) (sz.W n),
        ‖(((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * (baFMz sz z).S n (split d (sz.L n) (sz.W n) α).1 (split d (sz.L n) (sz.W n) β).1‖ * (a * a ^ 2) :=
        Finset.sum_le_sum fun α _ => Finset.sum_le_sum fun β _ => hterm α β
    _ = ((sz.size n : ℕ) : ℝ) * (a * a ^ 2) := by
        simp only [← Finset.sum_mul]
        rw [TwistAvgA_S_sum]
    _ ≤ ((sz.size n : ℕ) : ℝ) * (a + 1) ^ 3 := by
        refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
        nlinarith [sq_nonneg a, mul_nonneg ha0 (sq_nonneg a)]

theorem TwistAvgA_S2_le (hκ : 0 < κ) (hflow : BAFlow sz κ ε 𝔠 𝔡 z) (n : ℕ) {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ BAflowT0 sz z n)
    (ω : sz.SeqΩ) (c₁ c₂ : Zd d (sz.L n)) :
    ‖twAvgS2 (baFMz sz z) n t ω c₁ c₂‖ ≤ ((sz.size n : ℕ) : ℝ) * (((baFMz sz z).eta n t)⁻¹ + 1) ^ 3 := by
  have hη := BAExp14a_eta_pos hκ hflow n ht0 ht
  set a := ((baFMz sz z).eta n t)⁻¹ with ha
  have ha0 : 0 ≤ a := inv_nonneg.2 hη.le
  have hterm : ∀ α β : Idx d (sz.L n) (sz.W n),
      ‖(((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * (baFMz sz z).S n (split d (sz.L n) (sz.W n) α).1 (split d (sz.L n) (sz.W n) β).1 *
        (twAvgGPM (baFMz sz z) n t ω c₁ c₂ β α * (starRingEnd ℂ) (twAvgGPG (baFMz sz z) n t ω c₁ c₂ β α))‖ ≤
      ‖(((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * (baFMz sz z).S n (split d (sz.L n) (sz.W n) α).1 (split d (sz.L n) (sz.W n) β).1‖ * (a * a ^ 2) := by
    intro α β
    rw [norm_mul (_ * _), norm_mul (twAvgGPM _ _ _ _ _ _ _ _), Complex.norm_conj]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    exact mul_le_mul (TwistAvgA_GPM_le hκ hflow n ht0 ht ω c₁ c₂ β α) (TwistAvgA_GPG_le hκ hflow n ht0 ht ω c₁ c₂ β α) (norm_nonneg _) ha0
  calc ‖twAvgS2 (baFMz sz z) n t ω c₁ c₂‖ ≤ ∑ α : Idx d (sz.L n) (sz.W n), ∑ β : Idx d (sz.L n) (sz.W n),
        ‖(((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * (baFMz sz z).S n (split d (sz.L n) (sz.W n) α).1 (split d (sz.L n) (sz.W n) β).1 *
          (twAvgGPM (baFMz sz z) n t ω c₁ c₂ β α * (starRingEnd ℂ) (twAvgGPG (baFMz sz z) n t ω c₁ c₂ β α))‖ :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun α _ => norm_sum_le _ _)
    _ ≤ ∑ α : Idx d (sz.L n) (sz.W n), ∑ β : Idx d (sz.L n) (sz.W n),
        ‖(((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * (baFMz sz z).S n (split d (sz.L n) (sz.W n) α).1 (split d (sz.L n) (sz.W n) β).1‖ * (a * a ^ 2) :=
        Finset.sum_le_sum fun α _ => Finset.sum_le_sum fun β _ => hterm α β
    _ = ((sz.size n : ℕ) : ℝ) * (a * a ^ 2) := by
        simp only [← Finset.sum_mul]
        rw [TwistAvgA_S_sum]
    _ ≤ ((sz.size n : ℕ) : ℝ) * (a + 1) ^ 3 := by
        refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
        nlinarith [sq_nonneg a, mul_nonneg ha0 (sq_nonneg a)]

end Reg

/-- `twAvgReg_holds`: continuity, integrability, the pathwise envelopes and the eventual `η_t⁻¹ + 1 ≤ N`. -/
theorem twAvgReg_holds (d : ℕ) : twAvgReg d := by
  intro κ ε 𝔠 𝔡 sz z hκ hε hflow
  refine ⟨?_, ?_, ?_⟩
  · intro n t ht0 ht c₁ c₂
    have cG := BAExp14a_cont_G hκ hflow n ht0 ht
    have hSelf := (BAflow_real κ ε 𝔠 𝔡 sz z hflow n).1
    have hT : Continuous fun ω => twTr (baFMz sz z) n t ω c₁ c₂ := by
      unfold twTr FlowFM.GM
      fun_prop
    refine ⟨hT, ?_, ?_, ?_, ?_⟩
    · unfold twAvgS1 twAvgGPM twAvgGPG
      fun_prop
    · unfold twAvgS2 twAvgGPM twAvgGPG
      fun_prop
    · have e : (fun ω : sz.SeqΩ => (baFMz sz z).L n t (fun _ : Fin 1 => true) (fun _ => c₁) ω - (baFMz sz z).m n) =
          fun ω => BAExp14a_X sz z n t ω c₁ := funext fun ω => (BAExp14a_X_eq n t ω hSelf c₁).symm
      rw [e]
      exact BAExp14a_cont_X hκ hflow n ht0 ht c₁
    · intro p
      change Integrable (fun ω : sz.SeqΩ => ‖twTr (baFMz sz z) n t ω c₁ c₂‖ ^ p) (BAExp14a_μ sz)
      refine Integrable.of_bound ((continuous_norm.comp hT).pow p).aestronglyMeasurable ((((baFMz sz z).eta n t)⁻¹ + 1) ^ p)
        (Eventually.of_forall fun ω => ?_)
      rw [Real.norm_of_nonneg (pow_nonneg (norm_nonneg _) _)]
      exact pow_le_pow_left₀ (norm_nonneg _) (TwistAvgA_twTr_le hκ hflow n ht0 ht ω c₁ c₂) p
  · intro n t ht0 ht ω c₁ c₂
    have hSelf := (BAflow_real κ ε 𝔠 𝔡 sz z hflow n).1
    refine ⟨TwistAvgA_twTr_le hκ hflow n ht0 ht ω c₁ c₂, ?_,
      TwistAvgA_S1_le hκ hflow n ht0 ht ω c₁ c₂, TwistAvgA_S2_le hκ hflow n ht0 ht ω c₁ c₂⟩
    rw [← BAExp14a_X_eq n t ω hSelf c₁]
    exact TwistAvgA_X_le hκ hflow n ht0 ht ω c₁
  · have hsz : sz.SizeTendsto := hflow.1.2.2.1
    have hN2 : ∀ᶠ n in atTop, (2 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := hsz.eventually (eventually_ge_atTop 2)
    have hNε : ∀ᶠ n in atTop, 4 / κ ≤ ((sz.size n : ℕ) : ℝ) ^ ε :=
      ((tendsto_rpow_atTop hε).comp hsz).eventually (eventually_ge_atTop (4 / κ))
    filter_upwards [hN2, hNε] with n h2 hε4 t ht0 ht
    have hη := BAExp14a_eta_pos hκ hflow n ht0 ht
    have hr := BAflow_real κ ε 𝔠 𝔡 sz z hflow n
    have h1 := BAExp14a_one_sub_t hκ hflow n ht
    have hz := (hflow.2 n).2.1
    set N : ℝ := ((sz.size n : ℕ) : ℝ) with hN
    have hN0 : 0 < N := by linarith
    have hzpos : 0 < (z n).im := lt_of_lt_of_le (Real.rpow_pos_of_pos hN0 _) hz
    have e : (baFMz sz z).eta n t = (1 - t) * (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n).im := rfl
    have hηlow : (z n).im / 2 * κ ≤ (baFMz sz z).eta n t := by
      rw [e]
      exact mul_le_mul h1 hr.2 hκ.le (by linarith)
    have h3 : N * N ^ (-1 + ε) = N ^ ε := by
      rw [← Real.rpow_one_add' hN0.le (by linarith)]
      congr 1; ring
    have hNη : 2 ≤ N * (baFMz sz z).eta n t := by
      have h4 : N * (N ^ (-1 + ε) / 2 * κ) ≤ N * (baFMz sz z).eta n t := by
        refine mul_le_mul_of_nonneg_left (le_trans ?_ hηlow) hN0.le
        have : N ^ (-1 + ε) / 2 * κ ≤ (z n).im / 2 * κ := by gcongr
        exact this
      have h5 : N * (N ^ (-1 + ε) / 2 * κ) = N ^ ε * κ / 2 := by rw [← h3]; ring
      have h6 : 2 ≤ N ^ ε * κ / 2 := by
        have : 4 ≤ N ^ ε * κ := by
          have := mul_le_mul_of_nonneg_right hε4 hκ.le
          rwa [div_mul_cancel₀ _ hκ.ne'] at this
        linarith
      linarith
    have hinv : ((baFMz sz z).eta n t)⁻¹ ≤ N / 2 := by
      rw [inv_eq_one_div, div_le_div_iff₀ hη (by norm_num)]
      linarith
    linarith



/-! ## 7. The twist algebra and `lanlw` at `(x, Π_{c₂}x)` -/

section Alg
variable {d : ℕ} {sz : Sizes d} {z : ℕ → ℂ} {κ ε 𝔠 𝔡 : ℝ}

theorem TwistAvgA_STblk_pt (n : ℕ) (c : Zd d (sz.L n)) (o : Fin (sz.W n ^ d)) : STblk sz n (TwistAvgA_pt n c o) = c := by
  unfold STblk
  rw [TwistAvgA_split_pt]

theorem TwistAvgA_shift_pt (n : ℕ) (c₂ c₁ : Zd d (sz.L n)) (o : Fin (sz.W n ^ d)) :
    twShift n c₂ (TwistAvgA_pt n c₁ o) = TwistAvgA_pt n c₂ o := by
  rw [TwistAvgA_shift_eq, TwistAvgA_split_pt]

/-- `W^{-d} Σ_o G_{(c,o),(c₂,o)} = twTr c c₂ + M^{(B)}_{cc₂}` (`G = Ǧ + M`; the sum of `M_{(c,o),(c₂,o)} = M^{(B)}_{cc₂}` over the `W^d` offsets). -/
theorem TwistAvgA_avg_G {n : ℕ} (hm : 0 < ((baFMz sz z).m n).im) (t : ℝ) (ω : sz.SeqΩ) (c c₂ : Zd d (sz.L n)) :
    (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * ∑ o : Fin (sz.W n ^ d), (baFMz sz z).G n t ω (TwistAvgA_pt n c o) (TwistAvgA_pt n c₂ o) =
      twTr (baFMz sz z) n t ω c c₂ + twMB (baFMz sz z) n c c₂ := by
  have hW : (((sz.W n : ℕ) : ℂ) ^ d) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (sz.W_pos n).ne')
  have e : twTr (baFMz sz z) n t ω c c₂ = (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * ∑ o : Fin (sz.W n ^ d),
      ((baFMz sz z).G n t ω (TwistAvgA_pt n c o) (TwistAvgA_pt n c₂ o) - twMB (baFMz sz z) n c c₂) := by
    unfold twTr
    rw [TwistAvgA_sum_blk]
    congr 1
    refine Finset.sum_congr rfl fun o _ => ?_
    unfold FlowFM.GM
    rw [TwistAvgA_shift_pt, TwistAvgA_M_pt hm]
    simp
  rw [e, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_sub]
  have : (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * (((sz.W n ^ d : ℕ) : ℂ) * twMB (baFMz sz z) n c c₂) = twMB (baFMz sz z) n c c₂ := by
    push_cast
    field_simp
  rw [this]
  ring


/-- The non-derivative term (mirror form): `W^{-d} Σ_{x∈[c₁]} Σ_{α,β} M_{xα} S_{αβ} Ǧ_{ββ} G_{α,Π_{c₂}x} Φ
= t Σ_c M^{(B)}_{c₁c} X_c (M^{(B)}_{cc₂} + twTr c c₂) Φ`; `Σ_β S_{αβ} Ǧ_{ββ} = t X_{[α]}` (`BAExp14a_sumS_GM`) and the block algebra of section 2. -/
theorem TwistAvgA_algA {n : ℕ} (hm : 0 < ((baFMz sz z).m n).im) (t : ℝ) (ω : sz.SeqΩ) (c₁ c₂ : Zd d (sz.L n)) (Φ : ℂ) :
    (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * ∑ x ∈ twBlk n c₁, ∑ α, ∑ β, (baFMz sz z).M n x α * BAlwS d (sz.L n) (sz.W n) t α β *
        (baFMz sz z).GM n t ω β β * (baFMz sz z).G n t ω α (twShift n c₂ x) * Φ =
      (t : ℂ) * (∑ c, twMB (baFMz sz z) n c₁ c * BAExp14a_X sz z n t ω c *
        (twMB (baFMz sz z) n c c₂ + twTr (baFMz sz z) n t ω c c₂)) * Φ := by
  have e1 : ∀ x α : Idx d (sz.L n) (sz.W n), ∑ β, (baFMz sz z).M n x α * BAlwS d (sz.L n) (sz.W n) t α β *
        (baFMz sz z).GM n t ω β β * (baFMz sz z).G n t ω α (twShift n c₂ x) * Φ =
      (baFMz sz z).M n x α * ((t : ℂ) * BAExp14a_X sz z n t ω (STblk sz n α)) * (baFMz sz z).G n t ω α (twShift n c₂ x) * Φ := by
    intro x α
    rw [← BAExp14a_sumS_GM n t ω α]
    simp only [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun β _ => by ring
  simp only [e1]
  rw [TwistAvgA_sum_blk]
  have e2 : ∀ o : Fin (sz.W n ^ d), ∑ α, (baFMz sz z).M n (TwistAvgA_pt n c₁ o) α * ((t : ℂ) * BAExp14a_X sz z n t ω (STblk sz n α)) *
      (baFMz sz z).G n t ω α (twShift n c₂ (TwistAvgA_pt n c₁ o)) * Φ =
      ∑ c, twMB (baFMz sz z) n c₁ c * ((t : ℂ) * BAExp14a_X sz z n t ω c * (baFMz sz z).G n t ω (TwistAvgA_pt n c o) (TwistAvgA_pt n c₂ o) * Φ) := by
    intro o
    have h := TwistAvgA_sum_M hm c₁ o (fun α => (t : ℂ) * BAExp14a_X sz z n t ω (STblk sz n α) *
      (baFMz sz z).G n t ω α (twShift n c₂ (TwistAvgA_pt n c₁ o)) * Φ)
    simp only [TwistAvgA_STblk_pt, TwistAvgA_shift_pt] at h ⊢
    rw [← h]
    exact Finset.sum_congr rfl fun α _ => by ring
  simp only [e2]
  rw [Finset.sum_comm, Finset.mul_sum, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun c _ => ?_
  have h3 := TwistAvgA_avg_G hm t ω c c₂
  have e3 : (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * ∑ o, twMB (baFMz sz z) n c₁ c * ((t : ℂ) * BAExp14a_X sz z n t ω c *
      (baFMz sz z).G n t ω (TwistAvgA_pt n c o) (TwistAvgA_pt n c₂ o) * Φ) =
      twMB (baFMz sz z) n c₁ c * ((t : ℂ) * BAExp14a_X sz z n t ω c * Φ) *
        ((((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * ∑ o, (baFMz sz z).G n t ω (TwistAvgA_pt n c o) (TwistAvgA_pt n c₂ o)) := by
    simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl fun o _ => by ring
  rw [e3, h3]
  ring


theorem TwistAvgA_S_eq (n : ℕ) (t : ℝ) (α β : Idx d (sz.L n) (sz.W n)) :
    BAlwS d (sz.L n) (sz.W n) t α β =
      (t : ℂ) * ((((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * (baFMz sz (z := z)).S n (split d (sz.L n) (sz.W n) α).1 (split d (sz.L n) (sz.W n) β).1) := by
  rw [BAExp14a_S_apply]
  change _ = (t : ℂ) * ((((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * (1 : Matrix (Zd d (sz.L n)) (Zd d (sz.L n)) ℂ) _ _)
  rw [Matrix.one_apply]

/-- The `M`-twisted derivative sum: `Σ_{x∈[c₁]} Σ_{α,β} M_{xα} S_{αβ} G_{β,Π_{c₂}x} F_{βα} = Σ_{α,β} S_{αβ} (G P M)_{βα} F_{βα}`. -/
theorem TwistAvgA_algB (n : ℕ) (t : ℝ) (ω : sz.SeqΩ) (c₁ c₂ : Zd d (sz.L n)) (F : Idx d (sz.L n) (sz.W n) → Idx d (sz.L n) (sz.W n) → ℂ) :
    (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * ∑ x ∈ twBlk n c₁, ∑ α, ∑ β, (baFMz sz z).M n x α * BAlwS d (sz.L n) (sz.W n) t α β *
        (baFMz sz z).G n t ω β (twShift n c₂ x) * F β α =
      ∑ α, ∑ β, BAlwS d (sz.L n) (sz.W n) t α β * twAvgGPM (baFMz sz z) n t ω c₁ c₂ β α * F β α := by
  have key : ∀ α β : Idx d (sz.L n) (sz.W n), (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * ∑ x ∈ twBlk n c₁, (baFMz sz z).M n x α *
      BAlwS d (sz.L n) (sz.W n) t α β * (baFMz sz z).G n t ω β (twShift n c₂ x) * F β α =
      BAlwS d (sz.L n) (sz.W n) t α β * twAvgGPM (baFMz sz z) n t ω c₁ c₂ β α * F β α := by
    intro α β
    unfold twAvgGPM
    simp only [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun w _ => by ring
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [Finset.sum_comm, Finset.mul_sum]
  exact Finset.sum_congr rfl fun β _ => key α β

/-- The derivative term: with `∂Φ_{βα}` of `TwistAvgA_dH_Phi`,
`Σ_{α,β} S_{αβ} (G P M)_{βα} ∂Φ_{βα} = -t (p-1) 𝒮₁ T^{p-2} T̄^p - t p 𝒮₂ T^{p-1} T̄^{p-1}`. -/
theorem TwistAvgA_algB2 (n : ℕ) (t : ℝ) (ω : sz.SeqΩ) (c₁ c₂ : Zd d (sz.L n)) (p : ℕ) :
    ∑ α, ∑ β, BAlwS d (sz.L n) (sz.W n) t α β * twAvgGPM (baFMz sz z) n t ω c₁ c₂ β α *
        (((p - 1 : ℕ) : ℂ) * twTr (baFMz sz z) n t ω c₁ c₂ ^ (p - 1 - 1) * (-(twAvgGPG (baFMz sz z) n t ω c₁ c₂ α β)) *
            (starRingEnd ℂ) (twTr (baFMz sz z) n t ω c₁ c₂) ^ p +
          twTr (baFMz sz z) n t ω c₁ c₂ ^ (p - 1) * ((p : ℂ) * (starRingEnd ℂ) (twTr (baFMz sz z) n t ω c₁ c₂) ^ (p - 1) *
            (-((starRingEnd ℂ) (twAvgGPG (baFMz sz z) n t ω c₁ c₂ β α))))) =
      -((t : ℂ) * ((p - 1 : ℕ) : ℂ) * (twAvgS1 (baFMz sz z) n t ω c₁ c₂ * twTr (baFMz sz z) n t ω c₁ c₂ ^ (p - 1 - 1) *
          (starRingEnd ℂ) (twTr (baFMz sz z) n t ω c₁ c₂) ^ p)) -
        (t : ℂ) * (p : ℂ) * (twAvgS2 (baFMz sz z) n t ω c₁ c₂ *
          (twTr (baFMz sz z) n t ω c₁ c₂ ^ (p - 1) * (starRingEnd ℂ) (twTr (baFMz sz z) n t ω c₁ c₂) ^ (p - 1))) := by
  unfold twAvgS1 twAvgS2
  simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ => ?_
  rw [TwistAvgA_S_eq (z := z)]
  ring

end Alg

section Assembly
variable {d : ℕ} {sz : Sizes d} {z : ℕ → ℂ} {κ ε 𝔠 𝔡 : ℝ}

/-- `∂_{h_{βα}} Φ_p` at the carrier (the value of `BAlwdf` of `Φ_p`, `TwistAvgA_dH_Phi`): `∂T = -(G P G)_{αβ}`, `∂T̄ = -conj((G P G)_{βα})`. -/
def TwistAvgA_dPhi (C : FlowFM sz) (n : ℕ) (t : ℝ) (ω : sz.SeqΩ) (c₁ c₂ : Zd d (sz.L n)) (p : ℕ) (β α : Idx d (sz.L n) (sz.W n)) : ℂ :=
  ((p - 1 : ℕ) : ℂ) * twTr C n t ω c₁ c₂ ^ (p - 1 - 1) * (-(twAvgGPG C n t ω c₁ c₂ α β)) * (starRingEnd ℂ) (twTr C n t ω c₁ c₂) ^ p +
    twTr C n t ω c₁ c₂ ^ (p - 1) * ((p : ℂ) * (starRingEnd ℂ) (twTr C n t ω c₁ c₂) ^ (p - 1) *
      (-((starRingEnd ℂ) (twAvgGPG C n t ω c₁ c₂ β α))))

/-- **`lanlw` at the carrier, `f = Φ_p`, at `(x, y)`**: `𝔼[Ǧ_{xy} Φ] = 𝔼[Σ_{α,β} M_{xα} S_{αβ} Ǧ_{ββ} G_{αy} Φ - Σ_{α,β} M_{xα} S_{αβ} G_{βy} ∂Φ_{βα}]`. -/
theorem TwistAvgA_lanlw_carrier (hκ : 0 < κ) (hflow : BAFlow sz κ ε 𝔠 𝔡 z) (n : ℕ) {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ BAflowT0 sz z n)
    (c₁ c₂ : Zd d (sz.L n)) (p : ℕ) (x y : Idx d (sz.L n) (sz.W n)) :
    ∫ ω, (baFMz sz z).GM n t ω x y * (twTr (baFMz sz z) n t ω c₁ c₂ ^ (p - 1) * (starRingEnd ℂ) (twTr (baFMz sz z) n t ω c₁ c₂) ^ p)
        ∂(BAExp14a_μ sz) =
      ∫ ω, (∑ α, ∑ β, (baFMz sz z).M n x α * BAlwS d (sz.L n) (sz.W n) t α β * (baFMz sz z).GM n t ω β β * (baFMz sz z).G n t ω α y *
            (twTr (baFMz sz z) n t ω c₁ c₂ ^ (p - 1) * (starRingEnd ℂ) (twTr (baFMz sz z) n t ω c₁ c₂) ^ p) -
          ∑ α, ∑ β, (baFMz sz z).M n x α * BAlwS d (sz.L n) (sz.W n) t α β * (baFMz sz z).G n t ω β y *
            TwistAvgA_dPhi (baFMz sz z) n t ω c₁ c₂ p β α) ∂(BAExp14a_μ sz) := by
  have h := TwistAvgA_lanlw hκ hflow n ht0 ht c₁ c₂ p x y
  obtain ⟨-, -, -, hzi, -⟩ := ba_G_data hκ sz hflow n ht0 ht
  have hz := hzi.ne'
  refine (integral_congr_ae (Eventually.of_forall fun ω => ?_)).trans (h.trans (integral_congr_ae (Eventually.of_forall fun ω => ?_)))
  · unfold BAlanlwL
    rw [TwistAvgA_f_Phi]
    rfl
  · change BAlanlwR d (sz.L n) (sz.W n) _ _ _ _ _ x y (BAExp14a_slc sz n ω) = _
    unfold BAlanlwR
    rw [TwistAvgA_f_Phi]
    simp only [TwistAvgA_dH_Phi _ _ _ _ _ _ _ hz]
    rfl

end Assembly

/-! ## 8. The moment identity -/

section Moment
variable {d : ℕ} {sz : Sizes d} {z : ℕ → ℂ} {κ ε 𝔠 𝔡 : ℝ}

section Leaves
variable (hκ : 0 < κ) (hflow : BAFlow sz κ ε 𝔠 𝔡 z) (n : ℕ) {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ BAflowT0 sz z n)
include hκ hflow ht0 ht

theorem TwistAvgA_BC_G (x y : Idx d (sz.L n) (sz.W n)) : TwistAvgA_BC (fun ω : sz.SeqΩ => (baFMz sz z).G n t ω x y) :=
  ⟨BAExp14a_cont_G hκ hflow n ht0 ht x y, ((baFMz sz z).eta n t)⁻¹, fun ω => BAExp14a_G_le hκ hflow n ht0 ht ω x y⟩

theorem TwistAvgA_BC_GM (x y : Idx d (sz.L n) (sz.W n)) : TwistAvgA_BC (fun ω : sz.SeqΩ => (baFMz sz z).GM n t ω x y) :=
  (TwistAvgA_BC_G hκ hflow n ht0 ht x y).sub (TwistAvgA_BC.const ((baFMz sz z).M n x y))

theorem TwistAvgA_BC_twTr (c₁ c₂ : Zd d (sz.L n)) : TwistAvgA_BC (fun ω : sz.SeqΩ => twTr (baFMz sz z) n t ω c₁ c₂) := by
  unfold twTr
  exact (TwistAvgA_BC.const _).mul (TwistAvgA_BC.sum _ fun w _ => TwistAvgA_BC_GM hκ hflow n ht0 ht _ _)

theorem TwistAvgA_BC_X (c : Zd d (sz.L n)) : TwistAvgA_BC (fun ω : sz.SeqΩ => BAExp14a_X sz z n t ω c) := by
  unfold BAExp14a_X
  exact (TwistAvgA_BC.const _).mul (TwistAvgA_BC.sum _ fun w _ => TwistAvgA_BC_GM hκ hflow n ht0 ht _ _)

theorem TwistAvgA_BC_GPM (c₁ c₂ : Zd d (sz.L n)) (β α : Idx d (sz.L n) (sz.W n)) :
    TwistAvgA_BC (fun ω : sz.SeqΩ => twAvgGPM (baFMz sz z) n t ω c₁ c₂ β α) := by
  unfold twAvgGPM
  exact (TwistAvgA_BC.const _).mul (TwistAvgA_BC.sum _ fun w _ => (TwistAvgA_BC_G hκ hflow n ht0 ht _ _).mul (TwistAvgA_BC.const _))

theorem TwistAvgA_BC_GPG (c₁ c₂ : Zd d (sz.L n)) (α β : Idx d (sz.L n) (sz.W n)) :
    TwistAvgA_BC (fun ω : sz.SeqΩ => twAvgGPG (baFMz sz z) n t ω c₁ c₂ α β) := by
  unfold twAvgGPG
  exact (TwistAvgA_BC.const _).mul (TwistAvgA_BC.sum _ fun w _ => (TwistAvgA_BC_G hκ hflow n ht0 ht _ _).mul (TwistAvgA_BC_G hκ hflow n ht0 ht _ _))

theorem TwistAvgA_BC_S1 (c₁ c₂ : Zd d (sz.L n)) : TwistAvgA_BC (fun ω : sz.SeqΩ => twAvgS1 (baFMz sz z) n t ω c₁ c₂) := by
  unfold twAvgS1
  exact TwistAvgA_BC.sum _ fun α _ => TwistAvgA_BC.sum _ fun β _ =>
    (TwistAvgA_BC.const _).mul ((TwistAvgA_BC_GPM hκ hflow n ht0 ht _ _ _ _).mul (TwistAvgA_BC_GPG hκ hflow n ht0 ht _ _ _ _))

theorem TwistAvgA_BC_S2 (c₁ c₂ : Zd d (sz.L n)) : TwistAvgA_BC (fun ω : sz.SeqΩ => twAvgS2 (baFMz sz z) n t ω c₁ c₂) := by
  unfold twAvgS2
  exact TwistAvgA_BC.sum _ fun α _ => TwistAvgA_BC.sum _ fun β _ =>
    (TwistAvgA_BC.const _).mul ((TwistAvgA_BC_GPM hκ hflow n ht0 ht _ _ _ _).mul (TwistAvgA_BC_GPG hκ hflow n ht0 ht _ _ _ _).conj)


theorem TwistAvgA_BC_dPhi (c₁ c₂ : Zd d (sz.L n)) (p : ℕ) (β α : Idx d (sz.L n) (sz.W n)) :
    TwistAvgA_BC (fun ω : sz.SeqΩ => TwistAvgA_dPhi (baFMz sz z) n t ω c₁ c₂ p β α) := by
  have hT := TwistAvgA_BC_twTr hκ hflow n ht0 ht c₁ c₂
  have h1 := TwistAvgA_BC_GPG hκ hflow n ht0 ht c₁ c₂ α β
  have h2 := TwistAvgA_BC_GPG hκ hflow n ht0 ht c₁ c₂ β α
  unfold TwistAvgA_dPhi
  exact (((((TwistAvgA_BC.const _).mul (hT.pow _)).mul h1.neg).mul (hT.conj.pow _))).add
    ((hT.pow _).mul (((TwistAvgA_BC.const _).mul (hT.conj.pow _)).mul h2.conj.neg))

theorem TwistAvgA_BC_Phic (c₁ c₂ : Zd d (sz.L n)) (p : ℕ) :
    TwistAvgA_BC (fun ω : sz.SeqΩ => twTr (baFMz sz z) n t ω c₁ c₂ ^ (p - 1) * (starRingEnd ℂ) (twTr (baFMz sz z) n t ω c₁ c₂) ^ p) :=
  ((TwistAvgA_BC_twTr hκ hflow n ht0 ht c₁ c₂).pow _).mul ((TwistAvgA_BC_twTr hκ hflow n ht0 ht c₁ c₂).conj.pow _)

end Leaves

/-- `T · T^{p-1} conj(T)^p = |T|^{2p}` (`p ≥ 1`). -/
theorem TwistAvgA_pow_eq (T : ℂ) (p : ℕ) (hp : 1 ≤ p) : ((‖T‖ ^ (2 * p) : ℝ) : ℂ) = T * (T ^ (p - 1) * (starRingEnd ℂ) T ^ p) := by
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  have e : T * (T ^ q * (starRingEnd ℂ) T ^ (q + 1)) = (T * (starRingEnd ℂ) T) ^ (q + 1) := by ring
  rw [Nat.add_sub_cancel, e, Complex.mul_conj', ← pow_mul]
  push_cast
  ring_nf

/-- `|T|^{2p-2} = T^{p-1} conj(T)^{p-1}`. -/
theorem TwistAvgA_pow_eq' (T : ℂ) (p : ℕ) (hp : 1 ≤ p) : ((‖T‖ ^ (2 * p - 2) : ℝ) : ℂ) = T ^ (p - 1) * (starRingEnd ℂ) T ^ (p - 1) := by
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  have e : T ^ q * (starRingEnd ℂ) T ^ q = (T * (starRingEnd ℂ) T) ^ q := by ring
  rw [Nat.add_sub_cancel, e, Complex.mul_conj', ← pow_mul, show 2 * (q + 1) - 2 = 2 * q by omega]
  push_cast
  ring_nf


/-- The right-hand side integrand of `lanlw` at the carrier with `f = Φ_p` (`TwistAvgA_lanlw_carrier`). -/
def TwistAvgA_Rint (C : FlowFM sz) (n : ℕ) (t : ℝ) (ω : sz.SeqΩ) (c₁ c₂ : Zd d (sz.L n)) (p : ℕ) (x y : Idx d (sz.L n) (sz.W n)) : ℂ :=
  ∑ α, ∑ β, C.M n x α * BAlwS d (sz.L n) (sz.W n) t α β * C.GM n t ω β β * C.G n t ω α y *
      (twTr C n t ω c₁ c₂ ^ (p - 1) * (starRingEnd ℂ) (twTr C n t ω c₁ c₂) ^ p) -
    ∑ α, ∑ β, C.M n x α * BAlwS d (sz.L n) (sz.W n) t α β * C.G n t ω β y * TwistAvgA_dPhi C n t ω c₁ c₂ p β α

section Leaves2
variable (hκ : 0 < κ) (hflow : BAFlow sz κ ε 𝔠 𝔡 z) (n : ℕ) {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ BAflowT0 sz z n)
include hκ hflow ht0 ht

theorem TwistAvgA_BC_Rint (c₁ c₂ : Zd d (sz.L n)) (p : ℕ) (x y : Idx d (sz.L n) (sz.W n)) :
    TwistAvgA_BC (fun ω : sz.SeqΩ => TwistAvgA_Rint (baFMz sz z) n t ω c₁ c₂ p x y) := by
  unfold TwistAvgA_Rint
  refine (TwistAvgA_BC.sum _ fun α _ => TwistAvgA_BC.sum _ fun β _ => ?_).sub (TwistAvgA_BC.sum _ fun α _ => TwistAvgA_BC.sum _ fun β _ => ?_)
  · exact ((((TwistAvgA_BC.const _).mul (TwistAvgA_BC.const _)).mul (TwistAvgA_BC_GM hκ hflow n ht0 ht _ _)).mul
      (TwistAvgA_BC_G hκ hflow n ht0 ht _ _)).mul (TwistAvgA_BC_Phic hκ hflow n ht0 ht c₁ c₂ p)
  · exact (((TwistAvgA_BC.const _).mul (TwistAvgA_BC.const _)).mul (TwistAvgA_BC_G hκ hflow n ht0 ht _ _)).mul
      (TwistAvgA_BC_dPhi hκ hflow n ht0 ht c₁ c₂ p _ _)

end Leaves2

/-- The moment identity at the carrier and the law `BAExp14a_μ sz = seqP (sz.withLam 0)`. -/
theorem TwistAvgA_moment (hκ : 0 < κ) (hflow : BAFlow sz κ ε 𝔠 𝔡 z) (n : ℕ) {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ BAflowT0 sz z n)
    (p : ℕ) (hp : 1 ≤ p) (c₁ c₂ : Zd d (sz.L n)) :
    ((∫ ω : sz.SeqΩ, ‖twTr (baFMz sz z) n t ω c₁ c₂‖ ^ (2 * p) ∂(BAExp14a_μ sz) : ℝ) : ℂ) =
      (t : ℂ) * ∑ c, twMB (baFMz sz z) n c₁ c * ∫ ω : sz.SeqΩ, ((baFMz sz z).L n t (fun _ : Fin 1 => true) (fun _ => c) ω - (baFMz sz z).m n) *
          (twMB (baFMz sz z) n c c₂ + twTr (baFMz sz z) n t ω c c₂) * twTr (baFMz sz z) n t ω c₁ c₂ ^ (p - 1) *
            (starRingEnd ℂ) (twTr (baFMz sz z) n t ω c₁ c₂) ^ p ∂(BAExp14a_μ sz) +
      (t : ℂ) * ((p : ℂ) - 1) * ∫ ω : sz.SeqΩ, twAvgS1 (baFMz sz z) n t ω c₁ c₂ * twTr (baFMz sz z) n t ω c₁ c₂ ^ (p - 2) *
          (starRingEnd ℂ) (twTr (baFMz sz z) n t ω c₁ c₂) ^ p ∂(BAExp14a_μ sz) +
      (t : ℂ) * (p : ℂ) * ∫ ω : sz.SeqΩ, twAvgS2 (baFMz sz z) n t ω c₁ c₂ * ((‖twTr (baFMz sz z) n t ω c₁ c₂‖ ^ (2 * p - 2) : ℝ) : ℂ)
          ∂(BAExp14a_μ sz) := by
  have hm : 0 < ((baFMz sz z).m n).im := (ba_G_data hκ sz hflow n ht0 ht).2.2.1
  have hSelf := (BAflow_real κ ε 𝔠 𝔡 sz z hflow n).1
  have hW : (((sz.W n : ℕ) : ℂ) ^ d) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (sz.W_pos n).ne')
  have bT := TwistAvgA_BC_twTr hκ hflow n ht0 ht c₁ c₂
  have bPhi := TwistAvgA_BC_Phic hκ hflow n ht0 ht c₁ c₂ p
  -- the three pieces of the right-hand side
  set fA : sz.SeqΩ → ℂ := fun ω => (t : ℂ) * ∑ c, twMB (baFMz sz z) n c₁ c * (((baFMz sz z).L n t (fun _ : Fin 1 => true) (fun _ => c) ω -
      (baFMz sz z).m n) * (twMB (baFMz sz z) n c c₂ + twTr (baFMz sz z) n t ω c c₂) * twTr (baFMz sz z) n t ω c₁ c₂ ^ (p - 1) *
        (starRingEnd ℂ) (twTr (baFMz sz z) n t ω c₁ c₂) ^ p) with hfA
  set fB : sz.SeqΩ → ℂ := fun ω => (t : ℂ) * ((p : ℂ) - 1) * (twAvgS1 (baFMz sz z) n t ω c₁ c₂ * twTr (baFMz sz z) n t ω c₁ c₂ ^ (p - 2) *
      (starRingEnd ℂ) (twTr (baFMz sz z) n t ω c₁ c₂) ^ p) with hfB
  set fC : sz.SeqΩ → ℂ := fun ω => (t : ℂ) * (p : ℂ) * (twAvgS2 (baFMz sz z) n t ω c₁ c₂ *
      ((‖twTr (baFMz sz z) n t ω c₁ c₂‖ ^ (2 * p - 2) : ℝ) : ℂ)) with hfC
  -- integrability of the leaves
  have bX : ∀ c, TwistAvgA_BC (fun ω : sz.SeqΩ => (baFMz sz z).L n t (fun _ : Fin 1 => true) (fun _ => c) ω - (baFMz sz z).m n) := fun c => by
    have e : (fun ω : sz.SeqΩ => (baFMz sz z).L n t (fun _ : Fin 1 => true) (fun _ => c) ω - (baFMz sz z).m n) =
        fun ω => BAExp14a_X sz z n t ω c := funext fun ω => (BAExp14a_X_eq n t ω hSelf c).symm
    rw [e]
    exact TwistAvgA_BC_X hκ hflow n ht0 ht c
  have bI1 : ∀ c, TwistAvgA_BC (fun ω : sz.SeqΩ => ((baFMz sz z).L n t (fun _ : Fin 1 => true) (fun _ => c) ω - (baFMz sz z).m n) *
      (twMB (baFMz sz z) n c c₂ + twTr (baFMz sz z) n t ω c c₂) * twTr (baFMz sz z) n t ω c₁ c₂ ^ (p - 1) *
        (starRingEnd ℂ) (twTr (baFMz sz z) n t ω c₁ c₂) ^ p) := fun c =>
    (((bX c).mul ((TwistAvgA_BC.const _).add (TwistAvgA_BC_twTr hκ hflow n ht0 ht c c₂))).mul (bT.pow _)).mul (bT.conj.pow _)
  have bI2 : TwistAvgA_BC (fun ω : sz.SeqΩ => twAvgS1 (baFMz sz z) n t ω c₁ c₂ * twTr (baFMz sz z) n t ω c₁ c₂ ^ (p - 2) *
      (starRingEnd ℂ) (twTr (baFMz sz z) n t ω c₁ c₂) ^ p) :=
    ((TwistAvgA_BC_S1 hκ hflow n ht0 ht c₁ c₂).mul (bT.pow _)).mul (bT.conj.pow _)
  have bI3 : TwistAvgA_BC (fun ω : sz.SeqΩ => twAvgS2 (baFMz sz z) n t ω c₁ c₂ *
      ((‖twTr (baFMz sz z) n t ω c₁ c₂‖ ^ (2 * p - 2) : ℝ) : ℂ)) := by
    have e : (fun ω : sz.SeqΩ => twAvgS2 (baFMz sz z) n t ω c₁ c₂ * ((‖twTr (baFMz sz z) n t ω c₁ c₂‖ ^ (2 * p - 2) : ℝ) : ℂ)) =
        fun ω => twAvgS2 (baFMz sz z) n t ω c₁ c₂ * (twTr (baFMz sz z) n t ω c₁ c₂ ^ (p - 1) * (starRingEnd ℂ) (twTr (baFMz sz z) n t ω c₁ c₂) ^ (p - 1)) :=
      funext fun ω => by rw [TwistAvgA_pow_eq' _ p hp]
    rw [e]
    exact (TwistAvgA_BC_S2 hκ hflow n ht0 ht c₁ c₂).mul ((bT.pow _).mul (bT.conj.pow _))
  have hA : Integrable fA (BAExp14a_μ sz) :=
    ((TwistAvgA_BC.const _).mul (TwistAvgA_BC.sum _ fun c _ => (TwistAvgA_BC.const _).mul (bI1 c))).integrable
  have hB : Integrable fB (BAExp14a_μ sz) := ((TwistAvgA_BC.const _).mul bI2).integrable
  have hC : Integrable fC (BAExp14a_μ sz) := ((TwistAvgA_BC.const _).mul bI3).integrable
  -- Step 1
  have step1 : ((∫ ω : sz.SeqΩ, ‖twTr (baFMz sz z) n t ω c₁ c₂‖ ^ (2 * p) ∂(BAExp14a_μ sz) : ℝ) : ℂ) =
      ∫ ω : sz.SeqΩ, twTr (baFMz sz z) n t ω c₁ c₂ * (twTr (baFMz sz z) n t ω c₁ c₂ ^ (p - 1) *
        (starRingEnd ℂ) (twTr (baFMz sz z) n t ω c₁ c₂) ^ p) ∂(BAExp14a_μ sz) := by
    rw [← integral_complex_ofReal]
    exact integral_congr_ae (Eventually.of_forall fun ω => TwistAvgA_pow_eq _ p hp)
  -- Step 2
  have step2 : ∫ ω : sz.SeqΩ, twTr (baFMz sz z) n t ω c₁ c₂ * (twTr (baFMz sz z) n t ω c₁ c₂ ^ (p - 1) *
        (starRingEnd ℂ) (twTr (baFMz sz z) n t ω c₁ c₂) ^ p) ∂(BAExp14a_μ sz) =
      ∑ x ∈ twBlk n c₁, (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * ∫ ω : sz.SeqΩ, (baFMz sz z).GM n t ω x (twShift n c₂ x) *
        (twTr (baFMz sz z) n t ω c₁ c₂ ^ (p - 1) * (starRingEnd ℂ) (twTr (baFMz sz z) n t ω c₁ c₂) ^ p) ∂(BAExp14a_μ sz) := by
    have hpt : ∀ ω : sz.SeqΩ, twTr (baFMz sz z) n t ω c₁ c₂ * (twTr (baFMz sz z) n t ω c₁ c₂ ^ (p - 1) *
        (starRingEnd ℂ) (twTr (baFMz sz z) n t ω c₁ c₂) ^ p) =
        ∑ x ∈ twBlk n c₁, (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * ((baFMz sz z).GM n t ω x (twShift n c₂ x) *
          (twTr (baFMz sz z) n t ω c₁ c₂ ^ (p - 1) * (starRingEnd ℂ) (twTr (baFMz sz z) n t ω c₁ c₂) ^ p)) := fun ω => by
      unfold twTr
      rw [Finset.mul_sum, Finset.sum_mul]
      exact Finset.sum_congr rfl fun x _ => mul_assoc _ _ _
    rw [integral_congr_ae (Eventually.of_forall hpt), integral_finsetSum _ (fun x _ =>
      ((TwistAvgA_BC.const _).mul ((TwistAvgA_BC_GM hκ hflow n ht0 ht _ _).mul bPhi)).integrable)]
    exact Finset.sum_congr rfl fun x _ => integral_const_mul _ _
  -- Step 4
  have step4 : ∫ ω : sz.SeqΩ, (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * ∑ x ∈ twBlk n c₁, TwistAvgA_Rint (baFMz sz z) n t ω c₁ c₂ p x (twShift n c₂ x) ∂(BAExp14a_μ sz) =
      ∑ x ∈ twBlk n c₁, (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * ∫ ω : sz.SeqΩ, TwistAvgA_Rint (baFMz sz z) n t ω c₁ c₂ p x (twShift n c₂ x) ∂(BAExp14a_μ sz) := by
    rw [integral_const_mul, integral_finsetSum _ (fun x _ => (TwistAvgA_BC_Rint hκ hflow n ht0 ht c₁ c₂ p x _).integrable), Finset.mul_sum]
  -- Step 5 (pointwise)
  have step5 : ∀ ω : sz.SeqΩ, (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * ∑ x ∈ twBlk n c₁, TwistAvgA_Rint (baFMz sz z) n t ω c₁ c₂ p x (twShift n c₂ x) =
      fA ω + fB ω + fC ω := by
    intro ω
    unfold TwistAvgA_Rint
    rw [Finset.sum_sub_distrib, mul_sub, TwistAvgA_algA hm t ω c₁ c₂ _,
      TwistAvgA_algB n t ω c₁ c₂ (fun β α => TwistAvgA_dPhi (baFMz sz z) n t ω c₁ c₂ p β α)]
    unfold TwistAvgA_dPhi
    rw [TwistAvgA_algB2 n t ω c₁ c₂ p]
    simp only [hfA, hfB, hfC, BAExp14a_X_eq n t ω hSelf, TwistAvgA_pow_eq' _ p hp]
    rw [Nat.cast_pred hp, show p - 1 - 1 = p - 2 by omega]
    rw [mul_assoc (t : ℂ), Finset.sum_mul]
    have e : ∀ c : Zd d (sz.L n), twMB (baFMz sz z) n c₁ c * ((baFMz sz z).L n t (fun _ : Fin 1 => true) (fun _ => c) ω - (baFMz sz z).m n) *
        (twMB (baFMz sz z) n c c₂ + twTr (baFMz sz z) n t ω c c₂) * (twTr (baFMz sz z) n t ω c₁ c₂ ^ (p - 1) * (starRingEnd ℂ) (twTr (baFMz sz z) n t ω c₁ c₂) ^ p) =
        twMB (baFMz sz z) n c₁ c * (((baFMz sz z).L n t (fun _ : Fin 1 => true) (fun _ => c) ω - (baFMz sz z).m n) *
          (twMB (baFMz sz z) n c c₂ + twTr (baFMz sz z) n t ω c c₂) * twTr (baFMz sz z) n t ω c₁ c₂ ^ (p - 1) *
            (starRingEnd ℂ) (twTr (baFMz sz z) n t ω c₁ c₂) ^ p) := fun c => by ring
    simp only [e]
    ring
  -- the chain of equalities
  have hI1 : ∫ ω : sz.SeqΩ, fA ω ∂(BAExp14a_μ sz) = (t : ℂ) * ∑ c, twMB (baFMz sz z) n c₁ c * ∫ ω : sz.SeqΩ,
      ((baFMz sz z).L n t (fun _ : Fin 1 => true) (fun _ => c) ω - (baFMz sz z).m n) *
        (twMB (baFMz sz z) n c c₂ + twTr (baFMz sz z) n t ω c c₂) * twTr (baFMz sz z) n t ω c₁ c₂ ^ (p - 1) *
          (starRingEnd ℂ) (twTr (baFMz sz z) n t ω c₁ c₂) ^ p ∂(BAExp14a_μ sz) := by
    rw [hfA]
    simp only []
    rw [integral_const_mul, integral_finsetSum _ (fun c _ => ((TwistAvgA_BC.const _).mul (bI1 c)).integrable)]
    congr 1
    exact Finset.sum_congr rfl fun c _ => integral_const_mul _ _
  calc ((∫ ω : sz.SeqΩ, ‖twTr (baFMz sz z) n t ω c₁ c₂‖ ^ (2 * p) ∂(BAExp14a_μ sz) : ℝ) : ℂ)
      = ∫ ω : sz.SeqΩ, twTr (baFMz sz z) n t ω c₁ c₂ * (twTr (baFMz sz z) n t ω c₁ c₂ ^ (p - 1) *
        (starRingEnd ℂ) (twTr (baFMz sz z) n t ω c₁ c₂) ^ p) ∂(BAExp14a_μ sz) := step1
    _ = ∑ x ∈ twBlk n c₁, (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * ∫ ω : sz.SeqΩ, (baFMz sz z).GM n t ω x (twShift n c₂ x) *
        (twTr (baFMz sz z) n t ω c₁ c₂ ^ (p - 1) * (starRingEnd ℂ) (twTr (baFMz sz z) n t ω c₁ c₂) ^ p) ∂(BAExp14a_μ sz) := step2
    _ = ∑ x ∈ twBlk n c₁, (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * ∫ ω : sz.SeqΩ, TwistAvgA_Rint (baFMz sz z) n t ω c₁ c₂ p x (twShift n c₂ x) ∂(BAExp14a_μ sz) :=
        Finset.sum_congr rfl fun x _ => by rw [TwistAvgA_lanlw_carrier hκ hflow n ht0 ht c₁ c₂ p x (twShift n c₂ x)]; rfl
    _ = ∫ ω : sz.SeqΩ, (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * ∑ x ∈ twBlk n c₁, TwistAvgA_Rint (baFMz sz z) n t ω c₁ c₂ p x (twShift n c₂ x) ∂(BAExp14a_μ sz) := step4.symm
    _ = ∫ ω : sz.SeqΩ, (fA ω + fB ω + fC ω) ∂(BAExp14a_μ sz) := integral_congr_ae (Eventually.of_forall step5)
    _ = ∫ ω : sz.SeqΩ, fA ω ∂(BAExp14a_μ sz) + ∫ ω : sz.SeqΩ, fB ω ∂(BAExp14a_μ sz) + ∫ ω : sz.SeqΩ, fC ω ∂(BAExp14a_μ sz) := by
        rw [integral_add (f := fun ω => fA ω + fB ω) (g := fC) (hA.add hB) hC, integral_add hA hB]
    _ = _ := by
        rw [hI1, hfB, hfC]
        simp only []
        rw [integral_const_mul, integral_const_mul]

end Moment

end RBM.BA

end
