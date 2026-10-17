/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Graph.BAMomentExpGen
import RBM3D.Graph.BAZetaExp
import RBM3D.Graph.BAExp14dB
import RBM3D.Graph.LWMomentExpA

set_option linter.style.header false
set_option linter.style.longLine false
set_option linter.style.setOption false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.flexible false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedSimpArgs false

/-!
# BA-L L3d2b-2 (T2483), part B: regime (A), the weighted expansion, the far and near pins and `lem:LW_moment_exp` at BA

Paper: arXiv:2507.20274, `paper/tex/7_8_light_weight.tex` (cited `7_8:line`): `lem:LW_moment_exp` (`7_8:78-83`), its proof (`7_8:1595-1660`: the case distinction
`7_8:1602-1611`, the far pin `7_8:1620-1643`, the near pins `7_8:1648-1660`); `paper/tex/B_graphical_lemmas.tex:486-497` (G3, G4).  Twin of `Graph/LWMomentExpA.lean`
(`:1-460`) and of `Graph/LWMomentExp.lean` §4-§12 (`:375-1509`) in a new file (namespace `RBM.BA`, private stem `BAMomentExpGenB_`); additive, no merged file is edited.
Part A (targets 1-5) is `Graph/BAMomentExpGen.lean` (merged).

## Contents

1. The context: `LWAssmgL` for the B class `Φ_B = LWPhiB` from `LWAssmExpgL` (twin of `lwMomentExp_assm`, `lwMEA_assm`), at the BA data.
2. Regime (A) (target 6): the statement `BAMomExpNoExp`, its wrapper `BAMomExpNoExpOfMoment` and `baMomExpNoExp_of_moment` from `BALWMoment` (twin of `lwMomExpNoExp_holds`).
3. The weighted expansion (target 7): continuity and integrability of the values, `BAMomentExp_expand`, `t = 0`.
4. The outputs of the engine with provenance (target 8): the control `R`, errors, `𝓜_x = 𝓜_y` (the weighted scale-mole tail), `𝓜_x ≠ 𝓜_y` (the BA rooted G3, the nested
   form at the shadow, the model-free pins), the polynomial envelope.
5. The three pins (target 8): `BAMomentExpOn`, `BAMomentExp_pin_gen`, the far and near pins for every `K > 0`.
6. The assembly (target 9): `BAMomentExpOfParts`, `baMomentExp_of_parts`, `BALWMomentExpOfAnp`, `baLWMomentExp_of_anp`.
7. Compiled nonempty instances of targets 6-9 (instance (i) of target 10) and of the index sets; instances (ii), (iii) of target 10 are in part A.

Ports (merged RBM3D files, text copied and adapted): `Graph/LWMomentExpA.lean:127-406`, `Graph/LWMomentExp.lean:118-1432`, `Graph/BAMomentGen.lean:1127-1374`, `Graph/BAMomentGenB.lean:370-427`;
RBM1D and RBM2D have no light-weight graph layer.

**Premise scan** (`Test/Axioms.lean`): `BAAnpAuxG` occurs only inside the statement def `BALWMomentExpOfAnp`, `BALWMoment` only inside the statement def
`BAMomExpNoExpOfMoment` (the pinned shape `∀ d, BALWMoment d → ∀ K, 0 < K → BAMomExpNoExp d K` as a theorem hypothesis would put the unproved `BALWMoment` into the scan: the
wrapper is definitionally that statement); `LWAssmExpgL`, `LWAssmgL` occur only in private helpers and inside statement defs.
-/

open private lwMEA_prec_mono lwMEA_phiB_sq_le lwMEA_loss lwMEA_phi_zero lwMEA_phi_sq lwMEA_zdistInf_le lwMEA_wneg
  from RBM3D.Graph.LWMomentExpA
open private BASizeClaim_sizeConst_nonneg from RBM3D.Graph.BASizeClaim2
open private lwMomentExp_comb from RBM3D.Graph.LWMomentExp

open MeasureTheory Filter Matrix

noncomputable section

namespace RBM.BA

open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes RBM.Graph

/-! ## 1. The context: `LWAssmgL` for the B class from `LWAssmExpgL` -/

section Context

variable {d : ℕ}

/-- **`LWAssmgL` for the B class** (twin of `lwMomentExp_assm`, `Graph/LWMomentExp.lean:482`, and of `lwMEA_assm`, `Graph/LWMomentExpA.lean:127`; the band input `lwN_Bctl_le` is
`BAExp14d_Bctl_small`, `Graph/BAExp14dB.lean:74`, with the factor `2`, absorbed by the quarter of the exponent): from `LWAssmExpgL` the class `Φ_B = LWPhiB sz d K t`,
`K n = ⌊ℓ n⌋ ∧ L n`, `c₀ = d`, satisfies `LWAssmgL` at the window `ε₁ = min (ε₀, d c₀/4)` with the constants `(2^d, d, (1 + 𝔡⁻²)^{1/2}, C ↦ ((C+1)^{d-2})^{1/2})`;
`LWLoop2gL` for `Φ_B` is `(LW_assm_exp)` at `D' = 1/𝔠`. -/
private theorem BAMomentExpGenB_assm (hd : 3 ≤ d) {κ ε 𝔡 𝔠 : ℝ} (hκ : 0 < κ) (hε : 0 < ε) (h𝔡 : 0 < 𝔡) {sz : Sizes d} {z : ℕ → ℂ}
    (hflow : BAFlow sz κ ε 𝔠 𝔡 z) {t : ℕ → ℝ} (ht0 : ∀ n, 0 ≤ t n) (ht1 : ∀ n, t n ≤ BAflowT0 sz z n) {ε₀ : ℝ} {Ψ ℓ : ℕ → ℝ}
    (hA : LWAssmExpgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) t ε₀ Ψ ℓ) :
    ∃ ε₁ : ℝ, 0 < ε₁ ∧ LWAssmgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) t ε₁ Ψ
      (LWPhiB sz (d : ℝ) (fun n => min ⌊ℓ n⌋₊ (sz.L n)) t) ((2 : ℝ) ^ d) (d : ℝ) (Real.sqrt (1 + (𝔡⁻¹) ^ 2))
      (fun C => Real.sqrt ((C + 1) ^ (d - 2))) := by
  obtain ⟨hε₀, hwin, hinit, hℓ0, hℓt, hloop⟩ := hA
  have hd2 : 2 ≤ d := by omega
  have h𝔠 : 0 < 𝔠 := hflow.1.1
  have hsz : sz.SizeTendsto := hflow.1.2.2.1
  have hband : sz.Bandwidth 𝔠 := hflow.1.2.2.2.1
  have hWO : sz.WO 𝔡 := hflow.1.2.2.2.2
  have hsize := tendsto_size sz hsz
  have htl1 : ∀ n, t n < 1 := fun n => (ba_G_data hκ sz hflow n (ht0 n) (ht1 n)).1
  obtain ⟨c₀, hc₀, hB⟩ := BAExp14d_Bctl_small d hd κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow
  have hdR : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  obtain ⟨ε₁, hε₁def⟩ : ∃ ε₁ : ℝ, ε₁ = min ε₀ ((d : ℝ) * c₀ / 4) := ⟨_, rfl⟩
  have hε₁pos : 0 < ε₁ := by rw [hε₁def]; exact lt_min hε₀ (by positivity)
  have hε₁a : ε₁ ≤ ε₀ := by rw [hε₁def]; exact min_le_left _ _
  have hε₁b : 4 * ε₁ ≤ (d : ℝ) * c₀ := by
    have : ε₁ ≤ (d : ℝ) * c₀ / 4 := by rw [hε₁def]; exact min_le_right _ _
    linarith
  have hW1 : ∀ n, (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := fun n => Nat.one_le_cast.2 (sz.W_pos n)
  have hWpos : ∀ n, (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := fun n => lt_of_lt_of_le one_pos (hW1 n)
  have hg : ∀ᶠ n in atTop, 0 < sz.lam n ∧ sz.lam n ≤ 𝔡⁻¹ := by
    filter_upwards [hWO] with n hn
    exact ⟨lt_of_lt_of_le (Real.rpow_pos_of_pos (hWpos n) _) hn.1, hn.2⟩
  have ht : ∀ᶠ n in atTop, 0 ≤ t n ∧ t n ≤ 1 := Eventually.of_forall fun n => ⟨ht0 n, (htl1 n).le⟩
  have hWinf : Tendsto (fun n => ((sz.W n : ℕ) : ℝ)) atTop atTop :=
    tendsto_atTop_mono' atTop hband ((tendsto_rpow_atTop h𝔠).comp hsz)
  have hbig : ∀ᶠ n in atTop, (2 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) ^ ((d : ℝ) * c₀ / 2) :=
    ((tendsto_rpow_atTop (by positivity : 0 < (d : ℝ) * c₀ / 2)).comp hWinf).eventually_ge_atTop 2
  have hup : ∀ᶠ n in atTop, ((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ)) * Bparam d (sz.L n) (sz.lam n) (t n) 0 ≤
      ((sz.W n : ℕ) : ℝ) ^ (-2 * ε₁) := by
    filter_upwards [hB t ht0 ht1, hbig] with n hn hb2
    have h2 := lwN_size_rpow_neg_le sz n hc₀.le
    rw [lwMEA_wneg _ (Nat.cast_nonneg _)]
    have hN0 : (0 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) ^ (-((d : ℝ) * c₀)) := Real.rpow_nonneg (Nat.cast_nonneg _) _
    calc ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * Bparam d (sz.L n) (sz.lam n) (t n) 0)
        ≤ 2 * ((sz.size n : ℕ) : ℝ) ^ (-c₀) := hn
      _ ≤ 2 * ((sz.W n : ℕ) : ℝ) ^ (-((d : ℝ) * c₀)) := mul_le_mul_of_nonneg_left h2 two_pos.le
      _ ≤ ((sz.W n : ℕ) : ℝ) ^ ((d : ℝ) * c₀ / 2) * ((sz.W n : ℕ) : ℝ) ^ (-((d : ℝ) * c₀)) :=
          mul_le_mul_of_nonneg_right hb2 hN0
      _ = ((sz.W n : ℕ) : ℝ) ^ (-((d : ℝ) * c₀ / 2)) := by
          rw [← Real.rpow_add (hWpos n)]; congr 1; ring
      _ ≤ ((sz.W n : ℕ) : ℝ) ^ (-2 * ε₁) := Real.rpow_le_rpow_of_exponent_le (hW1 n) (by linarith)
  set K : ℕ → ℕ := fun n => min ⌊ℓ n⌋₊ (sz.L n) with hKdef
  obtain ⟨-, hcls, hrel⟩ := LWPhiB_psiAll sz hd2 (ε₀ := ε₁) (c₀ := (d : ℝ)) K t hε₁pos le_rfl hg ht hup
  have hwin' : LWWindow sz ε₁ Ψ := by
    filter_upwards [hwin] with n hn
    exact ⟨hn.1, hn.2.trans (Real.rpow_le_rpow_of_exponent_le (hW1 n) (by linarith))⟩
  have hinit' : STInitialGT2gL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) t ε₁ Ψ := by
    refine ⟨?_, hinit.2⟩
    refine lwN_prec_mono hsize (c := 1) ?_ hinit.1
    exact Eventually.of_forall fun n u ω => ⟨Real.rpow_nonneg (Nat.cast_nonneg _) _,
      by rw [one_mul]; exact Real.rpow_le_rpow_of_exponent_le (hW1 n) (by linarith)⟩
  have hL2 : LWLoop2gL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) t (LWPhiB sz (d : ℝ) K t) := by
    refine lwN_prec_mono hsize (c := 1) ?_ (hloop (1 / 𝔠) (by positivity))
    filter_upwards [lwN_Wneg_le sz h𝔠 hband] with n hn
    rintro ⟨σ, a, b⟩ ω
    simp only
    have hLn : (zdistInf d (sz.L n) (a - b) : ℕ) ≤ sz.L n := lwMEA_zdistInf_le _ _
    rw [lwMEA_phi_sq, Nat.floor_natCast, one_mul]
    refine ⟨mul_nonneg (inv_nonneg.mpr (by positivity)) ?_, ?_⟩
    · unfold Bparam; positivity
    · refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr (by positivity))
      exact lwN_tailW_le (L := sz.L n) _ hLn (by have := sz.three_le_L n; omega) rfl (hℓ0 n) (ht0 n) (htl1 n) hn
  exact ⟨ε₁, hε₁pos, hε₁pos, hwin', hinit', hcls, hrel, hL2⟩

end Context

/-! ## 2. Regime (A) (target 6) -/

/-- **(A), `lem:LW_moment_exp` in the regime `regA d K` at BA** (the target `LWMomentExpG` at the `baPin` data on the pairs of `regA`, for every `K > 0`; twin of `LWMomExpNoExpF`,
`Graph/LWMomentExpA.lean:56`, with the carrier `LWfg (baFMz sz z)`; `regA` is imported, model-free in `sz`). -/
def BAMomExpNoExp (d : ℕ) (K : ℝ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ (p : ℕ), 2 ∣ p → ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z →
    ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ BAflowT0 sz z n) →
      ∀ (ε₀ : ℝ) (Ψ ℓ : ℕ → ℝ), LWAssmExpgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) t ε₀ Ψ ℓ → ∀ D : ℝ, 0 < D →
        PrecL sz (Sizes.seqP (sz.withLam 0)) (U := fun n => {q : Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n) //
            sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 < 1 - t n ∧ regA d K sz n (t n) (ℓ n) q})
          (fun n q _ => ∫ ω, ‖LWfg (baFMz sz z) n (t n) ω q.1.1 q.1.2‖ ^ p ∂(Sizes.seqP (sz.withLam 0)))
          (fun n q _ => (((baFMz sz z).eta n (t n))⁻¹ * (sz.Bctl n (t n)) ^ (1 / 2 : ℝ) *
            sfT d (sz.L n) ((sz.W n : ℕ) : ℝ) (sz.lam n) (t n)
              (min ((zdistInf d (sz.L n) (STblk sz n q.1.1 - STblk sz n q.1.2) : ℕ) : ℝ) (ℓ n))) ^ p + ((sz.W n : ℕ) : ℝ) ^ (-D))

/-- **Target 6, the statement def**: `lem:LW_moment` at the block Anderson data (`BALWMoment`) gives (A) for every `K > 0` (`∀ d, BALWMoment d → ∀ K, 0 < K → BAMomExpNoExp d K`; the
unfolding is the pinned shape; as `BALWMomentOfAnp`, `Graph/BAMomentGenB.lean:362`, the unproved pin occurs only inside a statement def, so that the premise scan of `Test/Axioms.lean`
does not see it as a hypothesis of a theorem). -/
def BAMomExpNoExpOfMoment (d : ℕ) : Prop := BALWMoment d → ∀ K : ℝ, 0 < K → BAMomExpNoExp d K

/-- **Target 6** (`lwMomExpNoExp_holds`, `Graph/LWMomentExpA.lean:334`; `7_8:1602-1611`): from `lem:LW_moment` at BA (`BALWMoment`) for the B class at the window `ε₁` of
`BAMomentExpGenB_assm`, `𝔼 |f|^p ≺ (η⁻¹ Φ_B(0) Φ_B(c |a-b|))^p`; on `regA`, `Φ_B(c r)² ≤ C_c e^{√(K (log W)^{3/2})} 𝖳_t(r ∧ ℓ)²` (`lwMEA_phiB_sq_le`) and the loss
`(C_c e^{√(K (log W)^{3/2})})^{q'} ≤ N^σ` for every `σ` (`lwMEA_loss`); `Φ_B(0) = B_{ctl}^{1/2}` (`lwMEA_phi_zero`). -/
theorem baMomExpNoExp_of_moment : ∀ d : ℕ, BAMomExpNoExpOfMoment d := by
  intro d hM K hK hd κ ε 𝔡 hκ hε h𝔡 p hp2 𝔠 sz z hflow t ht0 htT ε₀ Ψ ℓ hA D hD
  obtain ⟨q', hq'⟩ := hp2
  have h𝔠 : 0 < 𝔠 := hflow.1.1
  have hsz : sz.SizeTendsto := hflow.1.2.2.1
  have hband : sz.Bandwidth 𝔠 := hflow.1.2.2.2.1
  have hsize := tendsto_size sz hsz
  have ht1 : ∀ n, t n < 1 := fun n => (ba_G_data hκ sz hflow n (ht0 n) (htT n)).1
  have hℓ0 : ∀ n, 0 ≤ ℓ n := hA.2.2.2.1
  obtain ⟨ε₁, hε₁, hassm⟩ := BAMomentExpGenB_assm hd hκ hε h𝔡 hflow ht0 htT hA
  obtain ⟨c, hc, H⟩ := hM hd κ ε 𝔡 hκ hε h𝔡 p ⟨q', hq'⟩ ε₁ ((2 : ℝ) ^ d) (d : ℝ)
    (Real.sqrt (1 + (𝔡⁻¹) ^ 2)) (fun C => Real.sqrt ((C + 1) ^ (d - 2)))
  have hmain := H 𝔠 sz z hflow t ht0 htT Ψ _ hassm
  have h1 := StochDomAt.precomp_param hmain
    (fun n (v : {q : Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n) //
      sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 < 1 - t n ∧ regA d K sz n (t n) (ℓ n) q}) => v.1)
  refine lwMEA_prec_mono ?_ h1
  intro σ hσ
  have hloss := lwMEA_loss sz (by omega) h𝔠 hsz hband hK q' (C := (2 / min c 1) ^ (d - 2) * (1 + 2 ^ (d - 1))) hσ
  filter_upwards [hloss, hsize.eventually_ge_atTop 1] with n hl hN1
  rintro ⟨q, hq1, hq2⟩ ω
  dsimp only
  subst hq'
  set W : ℝ := ((sz.W n : ℕ) : ℝ) with hWdef
  have hW0 : 0 < W := Nat.cast_pos.2 (sz.W_pos n)
  have hL1 : (1 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) := Nat.one_le_cast.2 (by have := sz.three_le_L n; omega)
  set r : ℕ := zdistInf d (sz.L n) (STblk sz n q.1 - STblk sz n q.2) with hr
  have hrL : r ≤ sz.L n := lwMEA_zdistInf_le _ _
  set m : ℝ := min (r : ℝ) (ℓ n) with hm
  set s : ℝ := Real.sqrt (m / ellT (sz.L n) (sz.lam n) (t n)) with hs
  set Xn : ℝ := Real.sqrt (K * Real.log W ^ (3 / 2 : ℝ)) with hXn
  have hsX : s ≤ Xn := by
    refine Real.sqrt_le_sqrt ?_
    rw [div_le_iff₀ (ellT_pos hL1)]
    rcases hq2 with h | h
    · exact (min_le_left _ _).trans h
    · exact (min_le_right _ _).trans h
  have h2 := lwMEA_phiB_sq_le (d := d) (L := sz.L n) (W := W) (g := sz.lam n) (t := t n) (ℓ := ℓ n) (c := c)
    (by omega) hL1 (ht1 n) hW0 hq1.le (hℓ0 n) hc hrL
  have hΦ2 : LWPhiB sz (d : ℝ) (fun n => min ⌊ℓ n⌋₊ (sz.L n)) t n (c * (r : ℝ)) ^ 2 ≤
      ((2 / min c 1) ^ (d - 2) * (1 + 2 ^ (d - 1)) * Real.exp Xn) * sfT d (sz.L n) W (sz.lam n) (t n) m ^ 2 := by
    rw [lwMEA_phi_sq]
    calc _ ≤ _ := h2
      _ ≤ _ := by
        refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
        exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 hsX)
          (by positivity : (0 : ℝ) ≤ (2 / min c 1) ^ (d - 2) * (1 + 2 ^ (d - 1)))
  have hη0 := BAExp14a_eta_pos hκ hflow n (ht0 n) (htT n)
  have hη : 0 ≤ ((baFMz sz z).eta n (t n))⁻¹ := inv_nonneg.mpr hη0.le
  have hB0 : 0 ≤ (sz.Bctl n (t n)) ^ (1 / 2 : ℝ) :=
    Real.rpow_nonneg (by unfold Sizes.Bctl Bparam; positivity) _
  have hsf : 0 ≤ sfT d (sz.L n) W (sz.lam n) (t n) m := sfT_nonneg _
  have hY : 0 ≤ ((baFMz sz z).eta n (t n))⁻¹ * (sz.Bctl n (t n)) ^ (1 / 2 : ℝ) * sfT d (sz.L n) W (sz.lam n) (t n) m :=
    mul_nonneg (mul_nonneg hη hB0) hsf
  have hWD : 0 ≤ W ^ (-D) := Real.rpow_nonneg hW0.le _
  refine ⟨add_nonneg (pow_nonneg hY _) hWD, ?_⟩
  rw [lwMEA_phi_zero]
  set x : ℝ := ((baFMz sz z).eta n (t n))⁻¹ * (sz.Bctl n (t n)) ^ (1 / 2 : ℝ) with hx
  set Φ : ℝ := LWPhiB sz (d : ℝ) (fun n => min ⌊ℓ n⌋₊ (sz.L n)) t n (c * (r : ℝ)) with hΦ
  set C : ℝ := (2 / min c 1) ^ (d - 2) * (1 + 2 ^ (d - 1)) * Real.exp Xn with hC
  have hx0 : 0 ≤ x := mul_nonneg hη hB0
  calc (x * Φ) ^ (2 * q') = x ^ (2 * q') * (Φ ^ 2) ^ q' := by rw [mul_pow, pow_mul Φ 2 q']
    _ ≤ x ^ (2 * q') * (C * sfT d (sz.L n) W (sz.lam n) (t n) m ^ 2) ^ q' :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (sq_nonneg _) hΦ2 q') (by positivity)
    _ = C ^ q' * (x * sfT d (sz.L n) W (sz.lam n) (t n) m) ^ (2 * q') := by
        rw [mul_pow C, ← pow_mul (sfT d (sz.L n) W (sz.lam n) (t n) m) 2 q', mul_pow x _ (2 * q')]
        ring
    _ ≤ ((sz.size n : ℕ) : ℝ) ^ σ * (x * sfT d (sz.L n) W (sz.lam n) (t n) m) ^ (2 * q') :=
        mul_le_mul_of_nonneg_right hl (pow_nonneg (mul_nonneg hx0 hsf) _)
    _ ≤ ((sz.size n : ℕ) : ℝ) ^ σ * ((x * sfT d (sz.L n) W (sz.lam n) (t n) m) ^ (2 * q') + W ^ (-D)) :=
        mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hWD) (Real.rpow_nonneg (Nat.cast_nonneg _) _)

/-! ## 3. The weighted expansion (target 7) -/

section Expand

variable {d : ℕ} {sz : Sizes d} {z : ℕ → ℂ} {κ ε 𝔡 𝔠 : ℝ}

/-- The weighted value of a packed graph is continuous in the sample when only `G` varies (the weight is a constant of the sample; twin of `BAMomentGen_cont_val`,
`Graph/BAMomentGen.lean:1221`). -/
private theorem BAMomentExpGenB_cont_valW {ι : Type} [Fintype ι] [DecidableEq ι] {Ω' : Type*} [TopologicalSpace Ω']
    (D : Ω' → BALData ι) (D0 : BALData ι)
    (hG : ∀ x y, Continuous fun ω => (D ω).G x y) (hS : ∀ ω, (D ω).S = D0.S) (hSp : ∀ ω, (D ω).Sp = D0.Sp)
    (hM : ∀ ω, (D ω).M = D0.M) (hP : ∀ ω, (D ω).gPsi = D0.gPsi) (Q : BAPGraph (Fin 2)) (Wt : (Q.E' ⊕ Q.I' → ι) → ℝ) (ℓe : Fin 2 → ι) :
    Continuous fun ω => Q.valW (D ω) Wt ℓe := by
  classical
  by_cases hf : ∃ ℓ' : Q.E' → ι, ℓe = ℓ' ∘ Q.ext
  · obtain ⟨ℓ', hℓ'⟩ := hf
    have : (fun ω => Q.valW (D ω) Wt ℓe) = fun ω => Q.g.valW (D ω) Wt ℓ' :=
      funext fun ω => BAPGraph.valW_of_factor Q (D ω) Wt hℓ'
    rw [this]
    unfold BAGraph.valW
    exact continuous_finsetSum _ fun ℓi _ => continuous_const.mul (BAMomentGen_cont_term Q.g D D0 hG hS hSp hM hP _)
  · have : (fun ω => Q.valW (D ω) Wt ℓe) = fun _ => 0 := funext fun ω => BAPGraph.valW_of_not Q (D ω) Wt hf
    rw [this]; exact continuous_const

/-- `|f^D|^p` is integrable (bounded by `η⁻¹`-powers, continuous): the pointwise step of the three-way split needs it (twin of `lwMomentExp_integrable`,
`Graph/LWMomentExp.lean:118`). -/
theorem BAMomentExp_integrable (hκ : 0 < κ) (hflow : BAFlow sz κ ε 𝔠 𝔡 z) (n : ℕ) {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ BAflowT0 sz z n) (p : ℕ)
    (Dm : Finset (Zd d (sz.L n))) (x y : Idx d (sz.L n) (sz.W n)) :
    Integrable (fun ω => ‖LWfgD (baFMz sz z) n t ω Dm x y‖ ^ p) (BAExp14a_μ sz) := by
  have hGc : ∀ a b, Continuous fun ω : sz.SeqΩ => (baFMz sz z).G n t ω a b := fun a b => BAExp14a_cont_G hκ hflow n ht0 ht a b
  have hGMc : ∀ a b, Continuous fun ω : sz.SeqΩ => (baFMz sz z).GM n t ω a b := fun a b => BAExp14a_cont_GM hκ hflow n ht0 ht a b
  have hcont : Continuous fun ω : sz.SeqΩ => LWfgD (baFMz sz z) n t ω Dm x y := by
    unfold LWfgD
    refine continuous_finsetSum _ fun α _ => ?_
    by_cases hα : α = x ∨ α = y
    · simp only [hα, ite_true]; exact continuous_const
    · simp only [hα, ite_false]
      refine continuous_finsetSum _ fun β _ => ?_
      by_cases hβ : STblk sz n β ∈ Dm
      · simp only [hβ, ite_true]
        exact ((continuous_const.mul (hGMc β β)).mul (hGc x α)).mul (hGc α y)
      · simp only [hβ, ite_false]; exact continuous_const
  obtain ⟨-, -, -, -, -, hM1⟩ := ba_G_data hκ sz hflow n ht0 ht
  set H : ℝ := ((baFMz sz z).eta n t)⁻¹ with hH
  have hH0 : 0 ≤ H := inv_nonneg.2 (BAExp14a_eta_pos hκ hflow n ht0 ht).le
  have hGb : ∀ (ω : sz.SeqΩ) (a b : Idx d (sz.L n) (sz.W n)), ‖(baFMz sz z).G n t ω a b‖ ≤ H :=
    fun ω a b => BAExp14a_G_le hκ hflow n ht0 ht ω a b
  have hGMb : ∀ (ω : sz.SeqΩ) (a b : Idx d (sz.L n) (sz.W n)), ‖(baFMz sz z).GM n t ω a b‖ ≤ H + 1 := by
    intro ω a b
    refine (norm_sub_le _ _).trans ?_
    change ‖(baFMz sz z).G n t ω a b‖ + ‖BAMfine sz (BAflowLam0 sz z) (BAflowEs sz z) n a b‖ ≤ _
    linarith [hGb ω a b, hM1 a b]
  have hb : ∀ ω : sz.SeqΩ, ‖LWfgD (baFMz sz z) n t ω Dm x y‖ ≤ ∑ α : Idx d (sz.L n) (sz.W n), ∑ β : Idx d (sz.L n) (sz.W n),
      ‖(((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * (baFMz sz z).S n (STblk sz n α) (STblk sz n β)‖ * ((H + 1) * (H * H)) := by
    intro ω
    unfold LWfgD
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun α _ => ?_)
    by_cases hα : α = x ∨ α = y
    · simp only [hα, ite_true, norm_zero]
      exact Finset.sum_nonneg fun β _ => by positivity
    · simp only [hα, ite_false]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun β _ => ?_)
      by_cases hβ : STblk sz n β ∈ Dm
      · simp only [hβ, ite_true]
        have hc0 : 0 ≤ ‖(((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * (baFMz sz z).S n (STblk sz n α) (STblk sz n β)‖ := norm_nonneg _
        have hH1 : 0 ≤ H + 1 := by linarith
        have := mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left (hGMb ω β β) hc0)
          (hGb ω x α) (norm_nonneg _) (mul_nonneg hc0 hH1)) (hGb ω α y) (norm_nonneg _) (mul_nonneg (mul_nonneg hc0 hH1) hH0)
        have hterm : ∀ a b c d' : ℂ, ‖a * b * c * d'‖ = ‖a‖ * ‖b‖ * ‖c‖ * ‖d'‖ := fun a b c d' => by simp only [norm_mul]
        rw [hterm]
        calc _ ≤ _ := this
          _ = _ := by ring
      · simp only [hβ, ite_false, norm_zero]
        exact mul_nonneg (norm_nonneg _) (mul_nonneg (by linarith) (mul_nonneg hH0 hH0))
  refine Integrable.of_bound ((hcont.norm.pow p).aestronglyMeasurable)
    ((∑ α : Idx d (sz.L n) (sz.W n), ∑ β : Idx d (sz.L n) (sz.W n),
      ‖(((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * (baFMz sz z).S n (STblk sz n α) (STblk sz n β)‖ * ((H + 1) * (H * H))) ^ p)
    (Eventually.of_forall fun ω => ?_)
  rw [Real.norm_of_nonneg (by positivity)]
  exact pow_le_pow_left₀ (norm_nonneg _) (hb ω) p

/-- `t = 0`: `f^D = 0` (twin of `lwMomentExp_LWfD_zero`, `Graph/LWMomentExp.lean:1289`, and of `BAMomentGen_LWfg_zero`, `Graph/BAMomentGen.lean:1391`: `Ǧ = 0`). -/
theorem BAMomentExp_LWfgD_zero (hκ : 0 < κ) (hflow : BAFlow sz κ ε 𝔠 𝔡 z) (n : ℕ) (h1 : (0 : ℝ) ≤ BAflowT0 sz z n)
    (Dm : Finset (Zd d (sz.L n))) (ω : sz.SeqΩ) (x y : Idx d (sz.L n) (sz.W n)) : LWfgD (baFMz sz z) n 0 ω Dm x y = 0 := by
  obtain ⟨-, -, -, -, hGM, -⟩ := ba_G_data hκ sz hflow n (le_refl 0) h1
  have hP : BAflowPert sz (BAflowLam0 sz z) (BAflowEs sz z) n 0 ω = 0 := by
    unfold BAflowPert
    ext i j
    simp [Sizes.seqHflow]
    rfl
  have hz : ∀ a b, (baFMz sz z).GM n 0 ω a b = 0 := by
    intro a b
    have := congrFun (congrFun (hGM ω) a) b
    rw [hP] at this
    simpa [FlowFM.GM, baFMz, baFM] using this
  unfold LWfgD
  refine Finset.sum_eq_zero fun α _ => ?_
  split_ifs
  · rfl
  refine Finset.sum_eq_zero fun β _ => ?_
  split_ifs
  · rw [hz β β]; simp
  · rfl

variable {t : ℕ → ℝ} (hκ : 0 < κ) (hflow : BAFlow sz κ ε 𝔠 𝔡 z) (ht0 : ∀ n, 0 ≤ t n) (ht1 : ∀ n, t n ≤ BAflowT0 sz z n)
include hκ hflow ht0 ht1

/-- **Target 7, the weighted expansion** (`7_8:943-945` with the weight of `7_8:1607-1611`; twin of `lwMomentExp_expand`, `Graph/LWMomentExp.lean:390`, of `BAMomentGen_expand`,
`Graph/BAMomentGen.lean:1287`): from the engine lists with provenance (`BAWExp`, `ba_localregularXP`), at a sample size with `0 < t < 1`,
`𝔼 |f^{Dm}_{xy}|^p ≤ Σ_o ‖𝔼 𝒱_o^{π_o^*𝟙_{Dm}}‖` (`BAWExp.prod`, the bridge `baProv_bridge` and target 1 (d) on the left, the homogeneity target 4 (a) on the right, the slice transport
`BAExp14a_int_slice` of continuous integrands).  No integrability hypothesis: the identity is a sum of integrals. -/
theorem BAMomentExp_expand {p : ℕ} (hp : Even p) (n : ℕ) {outs : List (BAProvOut (baPG (BAGraph.ofLGraph (fxyPowGraph p))))}
    (hW : ∀ o ∈ outs, p ≤ o.Q.g.waved.countP (fun e => !e.col))
    (hX : BAWExp d (baPG (BAGraph.ofLGraph (fxyPowGraph p))) outs) (Dm : Finset (Zd d (sz.L n))) (x y : Idx d (sz.L n) (sz.W n))
    (htp : 0 < t n) :
    ∫ ω, ‖LWfgD (baFMz sz z) n (t n) ω Dm x y‖ ^ p ∂(BAExp14a_μ sz) ≤
      (outs.map fun o => ‖∫ ω, o.Q.valW (BAMomentGen_D sz z n (t n) ω) (BAMomentExp_wt sz n Dm o) ![x, y] ∂(BAExp14a_μ sz)‖).sum := by
  classical
  obtain ⟨ht1', hr, hmi, hzi, -⟩ := ba_G_data hκ sz hflow n (ht0 n) (ht1 n)
  have hSelf := hr.1
  have hz : (ztOf (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) (BAflowEs sz z n) (t n)).im ≠ 0 := hzi.ne'
  let Dω : Ω d (sz.L n) (sz.W n) → BALData (Idx d (sz.L n) (sz.W n)) := fun ω' =>
    BAlwData d (sz.L n) (sz.W n) (BAflowLam0 sz z n) (BAflowEs sz z n) (t n)
      (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) ω'
  have hGc : ∀ a b, Continuous fun ω' => (Dω ω').G a b := fun a b => BAExp14a_cont_lwG hz a b
  have hS : ∀ ω', (Dω ω').S = (Dω (fun _ => 0)).S := fun _ => rfl
  have hSp : ∀ ω', (Dω ω').Sp = (Dω (fun _ => 0)).Sp := fun _ => rfl
  have hM : ∀ ω', (Dω ω').M = (Dω (fun _ => 0)).M := fun _ => rfl
  have hP : ∀ ω', (Dω ω').gPsi = (Dω (fun _ => 0)).gPsi := fun _ => rfl
  have hid := BAWExp.prod hX (sz.three_le_L n) hSelf (ht0 n) ht1' (fun _ x' => if STblk sz n x' ∈ Dm then (1 : ℝ) else 0) ![x, y]
  -- the sample space version of both sides
  have hΦ₁ : Continuous fun ω' : Ω d (sz.L n) (sz.W n) =>
      (baPG (BAGraph.ofLGraph (fxyPowGraph p))).valW (Dω ω')
        (fun ℓ => ∏ k : Fin p, if STblk sz n (ℓ (Sum.inr (localReg_fxyBeta k))) ∈ Dm then (1 : ℝ) else 0) ![x, y] :=
    BAMomentExpGenB_cont_valW Dω (Dω fun _ => 0) hGc hS hSp hM hP _ _ _
  have hΦo : ∀ o ∈ outs, Continuous fun ω' : Ω d (sz.L n) (sz.W n) => o.Q.valW (Dω ω') (BAMomentExp_wt sz n Dm o) ![x, y] :=
    fun o _ => BAMomentExpGenB_cont_valW Dω (Dω fun _ => 0) hGc hS hSp hM hP _ _ _
  have h1 := BAExp14a_int_slice (sz := sz) n _ hΦ₁
  have h2 : ∀ o ∈ outs, ∫ ω, o.Q.valW (Dω (BAExp14a_slc sz n ω)) (BAMomentExp_wt sz n Dm o) ![x, y] ∂(BAExp14a_μ sz) =
      ∫ ω', o.Q.valW (Dω ω') (BAMomentExp_wt sz n Dm o) ![x, y] ∂(PF d (sz.L n) (sz.W n) 0) :=
    fun o ho => BAExp14a_int_slice (sz := sz) n _ (hΦo o ho)
  have hμeq : ∫ ω, (baPG (BAGraph.ofLGraph (fxyPowGraph p))).valW (Dω (BAExp14a_slc sz n ω))
        (fun ℓ => ∏ k : Fin p, if STblk sz n (ℓ (Sum.inr (localReg_fxyBeta k))) ∈ Dm then (1 : ℝ) else 0) ![x, y] ∂(BAExp14a_μ sz) =
      (outs.map fun o => ∫ ω, o.Q.valW (Dω (BAExp14a_slc sz n ω)) (BAMomentExp_wt sz n Dm o) ![x, y] ∂(BAExp14a_μ sz)).sum := by
    rw [h1, hid]
    congr 1
    refine List.map_congr_left fun o ho => ?_
    exact (h2 o ho).symm
  -- the left side, pointwise
  have hL : ∀ ω : sz.SeqΩ, (baPG (BAGraph.ofLGraph (fxyPowGraph p))).valW (Dω (BAExp14a_slc sz n ω))
        (fun ℓ => ∏ k : Fin p, if STblk sz n (ℓ (Sum.inr (localReg_fxyBeta k))) ∈ Dm then (1 : ℝ) else 0) ![x, y] =
      ((t n ^ p * ‖LWfgD (baFMz sz z) n (t n) ω Dm x y‖ ^ p : ℝ) : ℂ) := by
    intro ω
    have h0 : (baPG (BAGraph.ofLGraph (fxyPowGraph p))).valW (Dω (BAExp14a_slc sz n ω))
        (fun ℓ => ∏ k : Fin p, if STblk sz n (ℓ (Sum.inr (localReg_fxyBeta k))) ∈ Dm then (1 : ℝ) else 0) ![x, y] =
        ((‖fxyValD (Dω (BAExp14a_slc sz n ω)).toLData Dm x y‖ ^ p : ℝ) : ℂ) := by
      rw [BAPGraph.valW_of_factor (baPG (BAGraph.ofLGraph (fxyPowGraph p))) _ _ (ℓe := ![x, y]) (ℓ' := ![x, y]) rfl]
      exact baProv_bridge d (sz.L n) (sz.W n) _ _ _ _ _ p hp Dm ![x, y]
    rw [h0, ← LWfgD_baFMz sz z n (t n) ω Dm x y, norm_mul, mul_pow, Complex.norm_real, Real.norm_of_nonneg (ht0 n)]
  -- the right side, pointwise
  have hR : ∀ o ∈ outs, ∀ ω : sz.SeqΩ, o.Q.valW (Dω (BAExp14a_slc sz n ω)) (BAMomentExp_wt sz n Dm o) ![x, y] =
      (t n : ℂ) ^ o.Q.g.nW * o.Q.valW (BAMomentGen_D sz z n (t n) ω) (BAMomentExp_wt sz n Dm o) ![x, y] := fun o _ ω =>
    BAMomentExp_valW_scale d (sz.L n) (sz.W n) (sz.three_le_L n) _ κ _ (t n) _ hr (ht0 n) ht1' (BAExp14a_slc sz n ω) o.Q _ _
  simp only [hL] at hμeq
  have hI0 : 0 ≤ ∫ ω, ‖LWfgD (baFMz sz z) n (t n) ω Dm x y‖ ^ p ∂(BAExp14a_μ sz) := integral_nonneg fun ω => by positivity
  have hLHS : ∫ ω, ((t n ^ p * ‖LWfgD (baFMz sz z) n (t n) ω Dm x y‖ ^ p : ℝ) : ℂ) ∂(BAExp14a_μ sz) =
      ((t n ^ p * ∫ ω, ‖LWfgD (baFMz sz z) n (t n) ω Dm x y‖ ^ p ∂(BAExp14a_μ sz) : ℝ) : ℂ) := by
    rw [integral_complex_ofReal, integral_const_mul]
  have hid' : ((t n ^ p * ∫ ω, ‖LWfgD (baFMz sz z) n (t n) ω Dm x y‖ ^ p ∂(BAExp14a_μ sz) : ℝ) : ℂ) =
      (outs.map fun o => (t n : ℂ) ^ o.Q.g.nW *
        ∫ ω, o.Q.valW (BAMomentGen_D sz z n (t n) ω) (BAMomentExp_wt sz n Dm o) ![x, y] ∂(BAExp14a_μ sz)).sum := by
    rw [← hLHS, hμeq]
    congr 1
    refine List.map_congr_left fun o ho => ?_
    rw [← integral_const_mul]
    exact integral_congr_ae (Eventually.of_forall fun ω => hR o ho ω)
  have hnn : 0 ≤ t n ^ p * ∫ ω, ‖LWfgD (baFMz sz z) n (t n) ω Dm x y‖ ^ p ∂(BAExp14a_μ sz) :=
    mul_nonneg (by have := ht0 n; positivity) hI0
  have hle : t n ^ p * ∫ ω, ‖LWfgD (baFMz sz z) n (t n) ω Dm x y‖ ^ p ∂(BAExp14a_μ sz) ≤
      (outs.map fun o => t n ^ p *
        ‖∫ ω, o.Q.valW (BAMomentGen_D sz z n (t n) ω) (BAMomentExp_wt sz n Dm o) ![x, y] ∂(BAExp14a_μ sz)‖).sum := by
    have h2 := congrArg norm hid'
    rw [Complex.norm_real, Real.norm_of_nonneg hnn] at h2
    rw [h2]
    refine (lwMoment_norm_list_sum_le _ _).trans ?_
    refine List.sum_le_sum fun o ho => ?_
    simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos htp]
    refine mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one htp.le ht1'.le ?_) (norm_nonneg _)
    exact (hW o ho).trans List.countP_le_length
  rw [List.sum_map_mul_left] at hle
  exact le_of_mul_le_mul_left hle (by positivity)

end Expand

/-! ## 4. The outputs of the engine with provenance: the control, errors, `𝓜_x = 𝓜_y`, the envelope -/

section Outputs

variable {d : ℕ} {sz : Sizes d} {z : ℕ → ℂ} {κ ε 𝔡 𝔠 : ℝ} {t : ℕ → ℝ} {ε₀ ε₁ : ℝ} {Ψ ℓ : ℕ → ℝ}

/-- the right side of `LWMomentExpG` at BA (twin of `lwMomentExp_R`, `Graph/LWMomentExp.lean:807`, with `η_t = (baFMz sz z).eta`) -/
private def BAMomentExpGenB_R (sz : Sizes d) (z : ℕ → ℂ) (t ℓ : ℕ → ℝ) (p : ℕ) (D : ℝ) (n : ℕ) (x y : Idx d (sz.L n) (sz.W n)) : ℝ :=
  (((baFMz sz z).eta n (t n))⁻¹ * (sz.Bctl n (t n)) ^ (1 / 2 : ℝ) * sfT d (sz.L n) ((sz.W n : ℕ) : ℝ) (sz.lam n) (t n)
    (min ((zdistInf d (sz.L n) (STblk sz n x - STblk sz n y) : ℕ) : ℝ) (ℓ n))) ^ p + ((sz.W n : ℕ) : ℝ) ^ (-D)

private theorem BAMomentExpGenB_R_ge (n : ℕ) (p : ℕ) (D : ℝ) (x y : Idx d (sz.L n) (sz.W n)) (hη : 0 < (baFMz sz z).eta n (t n)) :
    ((sz.W n : ℕ) : ℝ) ^ (-D) ≤ BAMomentExpGenB_R sz z t ℓ p D n x y := by
  have h1 := inv_nonneg.2 hη.le
  have h2 : 0 ≤ (sz.Bctl n (t n)) ^ (1 / 2 : ℝ) := Real.rpow_nonneg (by unfold Sizes.Bctl Bparam; positivity) _
  have h3 := sfT_nonneg (d := d) (L := sz.L n) (W := ((sz.W n : ℕ) : ℝ)) (g := sz.lam n) (t := t n)
    (min ((zdistInf d (sz.L n) (STblk sz n x - STblk sz n y) : ℕ) : ℝ) (ℓ n))
  exact le_add_of_nonneg_left (pow_nonneg (by positivity) _)

/-- `η_t ≤ 1 - t` at the BA carrier (`η_t = (1 - t) Im m`, `‖m‖ ≤ 1`; the BA form of `lwMomentExp_eta_le`, `Graph/LWMomentExp.lean:1017`). -/
private theorem BAMomentExpGenB_eta_le (hκ : 0 < κ) (hflow : BAFlow sz κ ε 𝔠 𝔡 z) (n : ℕ) {s : ℝ} (hs0 : 0 ≤ s) (hs : s ≤ BAflowT0 sz z n) :
    (baFMz sz z).eta n s ≤ 1 - s := by
  obtain ⟨hs1, hr, hmi, -⟩ := ba_G_data hκ sz hflow n hs0 hs
  have hm1 : ‖(baFMz sz z).m n‖ ≤ 1 := BAm_norm_le_one d (sz.L n) _ _ _ (by simp) hr.1
  have h1 : ((baFMz sz z).m n).im ≤ 1 := (Complex.im_le_norm _).trans hm1
  rw [BAExp14a_eta_eq]
  unfold etaOf
  have h3 : 0 ≤ 1 - s := by linarith
  nlinarith [mul_le_mul_of_nonneg_left h1 h3]

variable (hd : 3 ≤ d) (hκ : 0 < κ) (hε : 0 < ε) (h𝔡 : 0 < 𝔡) (hflow : BAFlow sz κ ε 𝔠 𝔡 z) (ht0 : ∀ n, 0 ≤ t n)
  (ht1 : ∀ n, t n ≤ BAflowT0 sz z n)
  (hassm : LWAssmgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) t ε₁ Ψ (LWPhiB sz (d : ℝ) (fun n => min ⌊ℓ n⌋₊ (sz.L n)) t)
    ((2 : ℝ) ^ d) (d : ℝ) (Real.sqrt (1 + (𝔡⁻¹) ^ 2)) (fun C => Real.sqrt ((C + 1) ^ (d - 2))))
include hd hκ hε h𝔡 hflow ht0 ht1 hassm

/-- **errors** (twin of `lwMomentExp_prec_err`, `Graph/LWMomentExp.lean:901`): the weighted size bound at the entry scale `Ψ'` gives `N^{-D} ≤ W^{-D} ≤ R`. -/
private theorem BAMomentExpGenB_prec_err (p : ℕ) {K0 : ℕ} {D Deng : ℝ} (hD0 : 0 < D) (hK0 : 1 / 𝔠 ≤ K0) (hDe : (D + 1) / 𝔠 ≤ Deng)
    {V : ℕ → Type} (pr : ∀ n, V n → Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n))
    (dom : ∀ (L : ℕ) [NeZero L], Zd d L → Zd d L → ℝ → Finset (Zd d L)) (o : BAProvOut (baPG (BAGraph.ofLGraph (fxyPowGraph p))))
    (hQ : o.Q.g.Normal)
    (herr : ∀ (W L : ℕ) (Ψ' : ℝ), 1 ≤ W → 1 ≤ L → (L : ℝ) ^ d ≤ (W : ℝ) ^ K0 → (W : ℝ) ^ (-(d : ℝ) / 2) ≤ Ψ' →
      Ψ' ≤ (W : ℝ) ^ (-(ε₁ / 2)) → o.Q.g.scalingSize Ψ' W d L ≤ (W : ℝ) ^ (-Deng)) :
    PrecL sz (Sizes.seqP (sz.withLam 0)) (U := V)
      (fun n v ω => ‖o.Q.valW (BAMomentGen_D sz z n (t n) ω)
        (BAMomentExp_wt sz n (dom (sz.L n) (STblk sz n (pr n v).1) (STblk sz n (pr n v).2) (ℓ n)) o) ![(pr n v).1, (pr n v).2]‖)
      (fun n v _ => BAMomentExpGenB_R sz z t ℓ p D n (pr n v).1 (pr n v).2) := by
  have hε₁ := hassm.1
  have hsz : sz.SizeTendsto := hflow.1.2.2.1
  have h𝔠 : 0 < 𝔠 := hflow.1.1
  have hd0 : d ≠ 0 := by omega
  apply BAMomentGen_prec_of_whp
  intro τ hτ
  refine ⟨_, BAMomentGen_entry_whp hd hκ hε h𝔡 hflow ht0 ht1 hassm (τ₁ := 𝔠 * ε₁ / 4) (by positivity), ?_⟩
  obtain ⟨C, c, Kd, hC, hc, hKd, hdec⟩ := BAMomentGen_decay hd hκ hε h𝔡 hflow ht0 ht1 hassm
  have hC0 : 0 ≤ C := by linarith
  have hK1 : 0 ≤ C * expC (d - 2) c := by have := lwMoment_expC_nonneg (d - 2) hc; positivity
  filter_upwards [hdec, BAMomentGen_Psi_facts hd hκ hε h𝔡 hflow ht0 ht1 hassm (τ₁ := 𝔠 * ε₁ / 4) (by positivity) le_rfl,
    BAMomentGen_Wneg_le hflow.1 hD0.le hDe, BAMomentGen_L_le_W hflow.1 hK0, hsz.eventually_ge_atTop 1,
    hsz.eventually_ge_atTop (o.Q.g.sizeConst C (C * expC (d - 2) c) Kd)] with n hdn hPsi hWn hLW hN1 hNc
  intro ω hω v
  obtain ⟨hSd, hSpd, hMPd, hoff, hKS, hKSp, hKM, hKP⟩ := hdn ω
  obtain ⟨hΦ0, hwin, hup⟩ := hPsi
  set M : ℝ := max 1 (Real.sqrt (1 + (𝔡⁻¹) ^ 2)) with hM
  have hM1 : 1 ≤ M := le_max_left _ _
  have hNτ : 1 ≤ ((sz.size n : ℕ) : ℝ) ^ τ := Real.one_le_rpow hN1 hτ.le
  have hA : ∀ a b : Idx d (sz.L n) (sz.W n), ‖(BAMomentGen_D sz z n (t n) ω).G a b - (BAMomentGen_D sz z n (t n) ω).M a b‖ ≤
      M * ((sz.size n : ℕ) : ℝ) ^ (𝔠 * ε₁ / 4) * LWPhiB sz (d : ℝ) (fun n => min ⌊ℓ n⌋₊ (sz.L n)) t n 0 := by
    intro a b
    refine (hω (a, b)).trans ?_
    have h1 : 1 ≤ ((sz.size n : ℕ) : ℝ) ^ (𝔠 * ε₁ / 4) := Real.one_le_rpow hN1 (by positivity)
    have h2 : 0 ≤ ((sz.size n : ℕ) : ℝ) ^ (𝔠 * ε₁ / 4) * LWPhiB sz (d : ℝ) (fun n => min ⌊ℓ n⌋₊ (sz.L n)) t n 0 := by positivity
    nlinarith
  have h1 := BAMomentExp_pvalW_claim o.Q hQ (BAMomentGen_D sz z n (t n) ω) hA hKS hKSp hKM hKP hC0 hK1 hKd
    ![(pr n v).1, (pr n v).2]
    (BAMomentExp_wt sz n (dom (sz.L n) (STblk sz n (pr n v).1) (STblk sz n (pr n v).2) (ℓ n)) o) (BAMomentExp_wt_abs sz n _ o)
  have h2 := herr (sz.W n) (sz.L n) _ (sz.W_pos n) (by have := sz.three_le_L n; omega) hLW hwin hup
  have hK0' : 0 ≤ o.Q.g.sizeConst C (C * expC (d - 2) c) Kd := BASizeClaim_sizeConst_nonneg o.Q.g hC0 hK1 hKd
  have hη0 := BAExp14a_eta_pos hκ hflow n (ht0 n) (ht1 n)
  have hRg := BAMomentExpGenB_R_ge (sz := sz) (z := z) (t := t) (ℓ := ℓ) n p D (pr n v).1 (pr n v).2 hη0
  have hR0 : 0 ≤ BAMomentExpGenB_R sz z t ℓ p D n (pr n v).1 (pr n v).2 := (Real.rpow_nonneg (Nat.cast_nonneg _) _).trans hRg
  calc _ ≤ _ := (h1.trans (mul_le_mul_of_nonneg_left h2 hK0')).trans (hWn _ hNc)
    _ ≤ ((sz.W n : ℕ) : ℝ) ^ (-D) := lwMomentExp_floor_le hd0 n hD0.le
    _ ≤ _ := hRg
    _ ≤ _ := le_mul_of_one_le_left hR0 hNτ

/-- **outputs with `𝓜_x = 𝓜_y` at far pairs** (twin of `lwMomentExp_prec_scale`, `Graph/LWMomentExp.lean:943`, on the route of `BAMomentGen_prec_scale`,
`Graph/BAMomentGen.lean:802`; radius `r = Krad (log W)^{3/2}`, `lwTail32`): the weighted scale-mole tail `BAMomentExp_scalemole` covers every output with
`inr (ext 1) ∈ mol (inr (ext 0))`, every `x ~ y` among them (L4-C4 (b)). -/
private theorem BAMomentExpGenB_prec_scale (p : ℕ) {D Krad : ℝ} (hD0 : 0 < D) (hKr : 0 < Krad)
    {V : ℕ → Type} (pr : ∀ n, V n → Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n))
    (dom : ∀ (L : ℕ) [NeZero L], Zd d L → Zd d L → ℝ → Finset (Zd d L)) (o : BAProvOut (baPG (BAGraph.ofLGraph (fxyPowGraph p))))
    (hQ : o.Q.g.Normal) (hmol : Sum.inl (o.Q.ext 1) ∈ o.Q.g.mol (Sum.inl (o.Q.ext 0)))
    (hfar : ∀ n (v : V n), (Fintype.card (o.Q.E' ⊕ o.Q.I') : ℝ) * (Krad * Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ)) <
      (lwBdist d (sz.L n) (sz.W n) (pr n v).1 (pr n v).2 : ℝ)) :
    PrecL sz (Sizes.seqP (sz.withLam 0)) (U := V)
      (fun n v ω => ‖o.Q.valW (BAMomentGen_D sz z n (t n) ω)
        (BAMomentExp_wt sz n (dom (sz.L n) (STblk sz n (pr n v).1) (STblk sz n (pr n v).2) (ℓ n)) o) ![(pr n v).1, (pr n v).2]‖)
      (fun n v _ => BAMomentExpGenB_R sz z t ℓ p D n (pr n v).1 (pr n v).2) := by
  classical
  have hε₁ := hassm.1
  obtain ⟨h𝔠, -, hsz, hband, -⟩ := hflow.1
  apply BAMomentGen_prec_of_whp
  intro τ hτ
  refine ⟨_, BAMomentGen_entry_whp hd hκ hε h𝔡 hflow ht0 ht1 hassm (τ₁ := 𝔠 * ε₁ / 4) (by positivity), ?_⟩
  obtain ⟨C, c, Kd, hC, hc, hKd, hdec⟩ := BAMomentGen_decay hd hκ hε h𝔡 hflow ht0 ht1 hassm
  have hC0 : 0 ≤ C := by linarith
  filter_upwards [hdec, BAMomentGen_Psi_facts hd hκ hε h𝔡 hflow ht0 ht1 hassm (τ₁ := 𝔠 * ε₁ / 4) (by positivity) le_rfl,
    lwTail32 sz h𝔠 (mul_pos hc hKr) hsz hband ((o.Q.g.nM + o.Q.g.nA + 1 : ℕ) : ℝ) D, BAMomentGen_Wneg_le hflow.1 (le_refl (0 : ℝ)) le_rfl,
    hsz.eventually_ge_atTop 1,
    hsz.eventually_ge_atTop (o.Q.g.sizeConst C (C * expC (d - 2) (c / 2)) (C * (1 + expC (d - 2) (c / 2))))]
    with n hdn hPsi htail _ hN1 hNc
  intro ω hω v
  obtain ⟨hSd, hSpd, hMPd, hoff, -, -, -, -⟩ := hdn ω
  obtain ⟨hΦ0, hwin, hup⟩ := hPsi
  set M : ℝ := max 1 (Real.sqrt (1 + (𝔡⁻¹) ^ 2)) with hM
  have hM1 : 1 ≤ M := le_max_left _ _
  have hW1 : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := Nat.one_le_cast.2 (sz.W_pos n)
  have hA : ∀ a b : Idx d (sz.L n) (sz.W n), ‖(BAMomentGen_D sz z n (t n) ω).G a b - (BAMomentGen_D sz z n (t n) ω).M a b‖ ≤
      M * ((sz.size n : ℕ) : ℝ) ^ (𝔠 * ε₁ / 4) * LWPhiB sz (d : ℝ) (fun n => min ⌊ℓ n⌋₊ (sz.L n)) t n 0 := by
    intro a b
    refine (hω (a, b)).trans ?_
    have h1 : 1 ≤ ((sz.size n : ℕ) : ℝ) ^ (𝔠 * ε₁ / 4) := Real.one_le_rpow hN1 (by positivity)
    have h2 : 0 ≤ ((sz.size n : ℕ) : ℝ) ^ (𝔠 * ε₁ / 4) * LWPhiB sz (d : ℝ) (fun n => min ⌊ℓ n⌋₊ (sz.L n)) t n 0 := by positivity
    nlinarith
  have hη0 := BAExp14a_eta_pos hκ hflow n (ht0 n) (ht1 n)
  have hRg := BAMomentExpGenB_R_ge (sz := sz) (z := z) (t := t) (ℓ := ℓ) n p D (pr n v).1 (pr n v).2 hη0
  have hR0 : 0 ≤ BAMomentExpGenB_R sz z t ℓ p D n (pr n v).1 (pr n v).2 := (Real.rpow_nonneg (Nat.cast_nonneg _) _).trans hRg
  have hNτ : 1 ≤ ((sz.size n : ℕ) : ℝ) ^ τ := Real.one_le_rpow hN1 hτ.le
  refine le_trans ?_ (le_mul_of_one_le_left hR0 hNτ)
  by_cases hf : ∃ ℓ' : o.Q.E' → Idx d (sz.L n) (sz.W n), ![(pr n v).1, (pr n v).2] = ℓ' ∘ o.Q.ext
  · obtain ⟨ℓ', hℓ'⟩ := hf
    rw [BAPGraph.valW_of_factor o.Q _ _ hℓ']
    have hr0 : 0 ≤ Krad * Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ) :=
      mul_nonneg hKr.le (Real.rpow_nonneg (Real.log_nonneg hW1) _)
    have e0 : ℓ' (o.Q.ext 0) = (pr n v).1 := (congrFun hℓ' 0).symm
    have e1 : ℓ' (o.Q.ext 1) = (pr n v).2 := (congrFun hℓ' 1).symm
    have hsc := BAMomentExp_scalemole hd o.Q.g hQ (BAMomentGen_D sz z n (t n) ω) hA hC0 hc hSd hSpd hMPd hoff hr0
      (BAMomentExp_wt sz n (dom (sz.L n) (STblk sz n (pr n v).1) (STblk sz n (pr n v).2) (ℓ n)) o) (BAMomentExp_wt_abs sz n _ o) ℓ'
      (o.Q.ext 0) (o.Q.ext 1) hmol (by rw [e0, e1]; exact hfar n v)
    have hΨ0 : 0 < M * ((sz.size n : ℕ) : ℝ) ^ (𝔠 * ε₁ / 4) * LWPhiB sz (d : ℝ) (fun n => min ⌊ℓ n⌋₊ (sz.L n)) t n 0 := by
      have : 0 < M := lt_of_lt_of_le one_pos hM1
      positivity
    have hΨ1 : M * ((sz.size n : ℕ) : ℝ) ^ (𝔠 * ε₁ / 4) * LWPhiB sz (d : ℝ) (fun n => min ⌊ℓ n⌋₊ (sz.L n)) t n 0 ≤ 1 :=
      hup.trans (Real.rpow_le_one_of_one_le_of_nonpos hW1 (by linarith))
    have hK2 : 0 ≤ o.Q.g.sizeConst C (C * expC (d - 2) (c / 2)) (C * (1 + expC (d - 2) (c / 2))) := by
      have h1 : 0 ≤ expC (d - 2) (c / 2) := lwMoment_expC_nonneg (d - 2) (half_pos hc)
      exact BASizeClaim_sizeConst_nonneg o.Q.g hC0 (by positivity) (by positivity)
    rw [mul_assoc] at htail
    exact hsc.trans ((BAMomentGen_tail_le o.Q.g.counters (sz.W n) (sz.L n) d (sz.W_pos n) (by have := sz.three_le_L n; omega) hΨ0 hΨ1 hNc hK2
      htail).trans ((lwMomentExp_floor_le (by omega) n hD0.le).trans hRg))
  · rw [BAPGraph.valW_of_not o.Q _ _ hf, norm_zero]; exact hR0

/-- **The polynomial envelope** `‖𝔼-integrand‖ ≤ N^{K}`, every sample and every weight `|Wt| ≤ 1`, with `K` depending on the graph only (twin of `lwMomentExp_env`,
`Graph/LWMomentExp.lean:861`, and of `BAMomentGen_env`, `Graph/BAMomentGen.lean:1127`). -/
private theorem BAMomentExpGenB_env (Q : BAPGraph (Fin 2)) (hQ : Q.g.Normal) :
    ∃ Kenv : ℝ, ∀ᶠ n in atTop, ∀ (x y : Idx d (sz.L n) (sz.W n)) (ω : sz.SeqΩ)
      (Wt : (Q.E' ⊕ Q.I' → Idx d (sz.L n) (sz.W n)) → ℝ), (∀ ℓ, |Wt ℓ| ≤ 1) →
      ‖Q.valW (BAMomentGen_D sz z n (t n) ω) Wt ![x, y]‖ ≤ ((sz.size n : ℕ) : ℝ) ^ Kenv := by
  have hsz : sz.SizeTendsto := hflow.1.2.2.1
  obtain ⟨C, c, Kd, hC, hc, hKd, hdec⟩ := BAMomentGen_decay hd hκ hε h𝔡 hflow ht0 ht1 hassm
  have hC0 : 0 ≤ C := by linarith
  have hK1 : 0 ≤ C * expC (d - 2) c := by have := lwMoment_expC_nonneg (d - 2) hc; positivity
  refine ⟨((Q.g.nM + Q.g.nA + 3 * Q.g.nS + 1 : ℕ) : ℝ), ?_⟩
  filter_upwards [hdec, BAExp14a_eventual_scalars hκ hε h𝔡 hflow ht0 ht1,
    hsz.eventually_ge_atTop (Q.g.sizeConst C (C * expC (d - 2) c) Kd)] with n hn hev hNc x y ω Wt hWt
  obtain ⟨hSd, hSpd, hMPd, hoff, hKS, hKSp, hKM, hKP⟩ := hn ω
  obtain ⟨-, h4, hηN, -, -⟩ := hev
  set N : ℝ := ((sz.size n : ℕ) : ℝ) with hN
  have hN0 : 0 < N := by linarith
  have hη0 := BAExp14a_eta_pos hκ hflow n (ht0 n) (ht1 n)
  have hη1 := BAExp14c_eta_le_one hκ hflow n (ht0 n) (ht1 n)
  obtain ⟨-, -, -, -, -, hM1⟩ := ba_G_data hκ sz hflow n (ht0 n) (ht1 n)
  have hηi : 1 ≤ ((baFMz sz z).eta n (t n))⁻¹ := one_le_inv_iff₀.2 ⟨hη0, hη1⟩
  have hA : ∀ a b : Idx d (sz.L n) (sz.W n), ‖(BAMomentGen_D sz z n (t n) ω).G a b - (BAMomentGen_D sz z n (t n) ω).M a b‖ ≤
      2 * ((baFMz sz z).eta n (t n))⁻¹ := by
    intro a b
    have h1 := BAExp14a_G_le hκ hflow n (ht0 n) (ht1 n) ω a b
    have h2 := hM1 a b
    refine (norm_sub_le _ _).trans ?_
    change ‖(baFMz sz z).G n (t n) ω a b‖ + ‖BAMfine sz (BAflowLam0 sz z) (BAflowEs sz z) n a b‖ ≤ _
    linarith
  have h1 := BAMomentExp_pvalW_claim Q hQ (BAMomentGen_D sz z n (t n) ω) hA hKS hKSp hKM hKP hC0 hK1 hKd ![x, y] Wt hWt
  have hΨB : 2 * ((baFMz sz z).eta n (t n))⁻¹ ≤ N ^ 3 := by
    calc 2 * ((baFMz sz z).eta n (t n))⁻¹ ≤ 2 * N ^ 2 := by linarith
      _ ≤ N * N ^ 2 := by nlinarith [sq_nonneg N]
      _ = N ^ 3 := by ring
  have h2 := BAMomentGen_scalingSize_le Q.g.counters (Ψ := 2 * ((baFMz sz z).eta n (t n))⁻¹) (B := N ^ 3) (by positivity)
    hΨB (by nlinarith [sq_nonneg N]) (sz.W n) (sz.L n) d (sz.W_pos n) (by have := sz.three_le_L n; omega)
  have hK : 0 ≤ Q.g.sizeConst C (C * expC (d - 2) c) Kd := BASizeClaim_sizeConst_nonneg Q.g hC0 hK1 hKd
  have e : ((((sz.W n) * (sz.L n)) ^ d : ℕ) : ℝ) = N := rfl
  rw [e] at h2
  have hs : Q.g.scalingSize (2 * ((baFMz sz z).eta n (t n))⁻¹) (sz.W n) d (sz.L n) =
      Q.g.counters.scalingSize (2 * ((baFMz sz z).eta n (t n))⁻¹) (sz.W n) d (sz.L n) := rfl
  rw [hs] at h1
  calc ‖Q.valW (BAMomentGen_D sz z n (t n) ω) Wt ![x, y]‖
      ≤ Q.g.sizeConst C (C * expC (d - 2) c) Kd * (N ^ (Q.g.nM + Q.g.nA) * (N ^ 3) ^ Q.g.nS) :=
        h1.trans (mul_le_mul_of_nonneg_left h2 hK)
    _ ≤ N * (N ^ (Q.g.nM + Q.g.nA) * (N ^ 3) ^ Q.g.nS) :=
        mul_le_mul_of_nonneg_right hNc (by positivity)
    _ = N ^ ((Q.g.nM + Q.g.nA + 3 * Q.g.nS + 1 : ℕ) : ℝ) := by
        rw [Real.rpow_natCast, ← pow_mul]; ring

set_option maxHeartbeats 3200000 in
-- The twin `lwMomentExp_prec_anp` (`Graph/LWMomentExp.lean:1029`) carries the same heartbeat limit.
/-- **the outputs with `𝓜_x ≠ 𝓜_y`** (twin of `lwMomentExp_prec_anp`, `Graph/LWMomentExp.lean:1030`, on the route of `BAMomentGen_prec_anp`, `Graph/BAMomentGen.lean:904`):
the BA rooted G3 `baGtoAGTRooted_holds` (target 5) against the edge variables `N^{τ₁} ζ`, `ζ = baZetaVar` at the radius `ρ = (2K+1)(log W)^{3/2}`, `R = K (log W)^{3/2}`,
`r = (K/Kc)(log W)^{3/2}` (`baZetaExpClaim_holds`, `baGbyZeta_holds`), the nested form of `Γ^aux` at the shadow (`lwAuxNestedOwnOn_holds` at `BAShadowPG`, no twin), the
floor `W^{-D'}` of `ζ ≺ 𝖳 + W^{-D'}` and the model-free pin `hPin`. -/
private theorem BAMomentExpGenB_prec_anp
    (hAss : LWAssmExpgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) t ε₀ Ψ ℓ)
    {p : ℕ} (hp : 0 < p) {K Kc D : ℝ} (hK : 0 < K) (hKc : 0 < Kc) (hD0 : 0 < D)
    {V : ℕ → Type} (pr : ∀ n, V n → Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n))
    (dom : ∀ (L : ℕ) [NeZero L], Zd d L → Zd d L → ℝ → Finset (Zd d L)) (o : BAProvOut (baPG (BAGraph.ofLGraph (fxyPowGraph p))))
    (hPin : ∀ Γ : NGraph p (BAShadowPG o.Q).g.nM, Γ.NoGhost → Γ.IsNested → lwMomExpFar_ownExt Γ → lwMomentExp_PinN d Γ dom)
    (hQ : o.Q.g.Normal) (h345 : (BAShadowPG o.Q).LocReg345 p)
    (hxy : (BAShadowPG o.Q).g.molOf (Sum.inl ((BAShadowPG o.Q).ext 0)) ≠ (BAShadowPG o.Q).g.molOf (Sum.inl ((BAShadowPG o.Q).ext 1)))
    (hnM : o.Q.g.nM ≤ p) (hord : (2 * p : ℤ) ≤ o.Q.g.scalingOrder) (hcard : (Fintype.card (o.Q.E' ⊕ o.Q.I') : ℝ) ≤ Kc)
    (hcov : BACoverBy (P := o.Q) fun k : Fin p => o.π (Sum.inr (localReg_fxyBeta k)))
    (hreg1 : ∀ n (v : V n), sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 < 1 - t n)
    (hreg3 : ∀ n (v : V n), K * Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ) * ellT (sz.L n) (sz.lam n) (t n) < ℓ n) :
    PrecL sz (Sizes.seqP (sz.withLam 0)) (U := V)
      (fun n v ω => ‖o.Q.valW (BAMomentGen_D sz z n (t n) ω)
        (BAMomentExp_wt sz n (dom (sz.L n) (STblk sz n (pr n v).1) (STblk sz n (pr n v).2) (ℓ n)) o) ![(pr n v).1, (pr n v).2]‖)
      (fun n v _ => BAMomentExpGenB_R sz z t ℓ p D n (pr n v).1 (pr n v).2) := by
  classical
  have hε₁ := hassm.1
  obtain ⟨h𝔠, -, hsz, hband, -⟩ := hflow.1
  have hd0 : d ≠ 0 := by omega
  set Φ := LWPhiB sz (d : ℝ) (fun n => min ⌊ℓ n⌋₊ (sz.L n)) t with hΦ
  have hent : PrecL sz (Sizes.seqP (sz.withLam 0)) (U := fun n => Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n))
      (fun n p ω => ‖(baFMz sz z).GM n (t n) ω p.1 p.2‖) (fun n _ _ => ((sz.W n : ℕ) : ℝ) ^ (-ε₁)) := hassm.2.2.1.1
  obtain ⟨Γa, hnog, hnest, hown, hordN, hval⟩ := lwAuxNestedOwnOn_holds p (BAShadowPG o.Q) hp h345 hxy
  obtain ⟨Caux, hCaux, hPinH⟩ := hPin Γa hnog hnest hown
  have hnMeq : (BAShadowPG o.Q).g.nM = o.Q.g.nM := BAGraph.shadow_nM o.Q.g
  have hordN' : Γa.ordN = o.Q.g.auxOrd := hordN
  have hAe : (((o.Q.g.scalingOrder - o.Q.g.auxOrd).toNat : ℕ) : ℤ) = o.Q.g.scalingOrder - o.Q.g.auxOrd :=
    Int.toNat_of_nonneg (sub_nonneg.2 (o.Q.g.auxOrd_le_scalingOrder hQ))
  set e1 : ℕ := (o.Q.g.scalingOrder - o.Q.g.auxOrd).toNat with he1
  set nE : ℕ := Γa.es.length with hnE
  set A : ℕ := e1 + 2 * nE + o.Q.g.nM + 1 with hAdef
  set aN : ℕ := 2 * o.Q.g.nM + 2 * nE with haN
  set D' : ℝ := (D + aN + 1 + 1) / 𝔠 with hD'def
  have hD'0 : 0 < D' := by positivity
  set Rr : ℕ → ℝ := fun n => K * Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ) with hRr
  set ρ : ℕ → ℝ := fun n => (2 * K + 1) * Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ) with hρ
  have hlog : ∀ n, 0 ≤ Real.log ((sz.W n : ℕ) : ℝ) := fun n => Real.log_nonneg (Nat.one_le_cast.2 (sz.W_pos n))
  have hRr0 : ∀ n, 0 ≤ Rr n := fun n => mul_nonneg hK.le (Real.rpow_nonneg (hlog n) _)
  have hρ0 : ∀ n, 0 ≤ ρ n := fun n => mul_nonneg (by positivity) (Real.rpow_nonneg (hlog n) _)
  have hρrad : ∀ τ : ℝ, 0 < τ → ∀ᶠ n in atTop, Real.sqrt (ρ n) ≤ τ * Real.log ((sz.size n : ℕ) : ℝ) := by
    intro τ hτ
    filter_upwards [lwMomentExp_rad sz hd0 h𝔠 hsz hband (K := K + 1 / 2) (by positivity) τ hτ] with n hn
    refine le_trans (Real.sqrt_le_sqrt ?_) hn
    simp only [hρ]
    exact (by ring : (2 * K + 1) * Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ) =
      2 * ((K + 1 / 2) * Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ))).trans_le (le_add_of_nonneg_right zero_le_one)
  have hsep : ∀ K' : ℝ, ∀ᶠ n in atTop, K' * Real.log ((sz.W n : ℕ) : ℝ) ≤ ρ n - 2 * Rr n := by
    intro K'
    filter_upwards [BAMomentGen_logW_ge hflow.1 (max 1 (K' ^ 2))] with n hn
    have hy1 : 1 ≤ Real.log ((sz.W n : ℕ) : ℝ) := (le_max_left _ _).trans hn
    have hy0 : 0 < Real.log ((sz.W n : ℕ) : ℝ) := lt_of_lt_of_le one_pos hy1
    have hsq : |K'| ≤ Real.sqrt (Real.log ((sz.W n : ℕ) : ℝ)) := Real.abs_le_sqrt ((le_max_right _ _).trans hn)
    have h32 : Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ) = Real.log ((sz.W n : ℕ) : ℝ) * Real.sqrt (Real.log ((sz.W n : ℕ) : ℝ)) := by
      rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hy0, Real.rpow_one, Real.sqrt_eq_rpow]
    have hdiff : ρ n - 2 * Rr n = Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ) := by simp only [hρ, hRr]; ring
    rw [hdiff, h32]
    calc K' * Real.log ((sz.W n : ℕ) : ℝ) ≤ |K'| * Real.log ((sz.W n : ℕ) : ℝ) := mul_le_mul_of_nonneg_right (le_abs_self K') hy0.le
      _ ≤ Real.sqrt (Real.log ((sz.W n : ℕ) : ℝ)) * Real.log ((sz.W n : ℕ) : ℝ) := mul_le_mul_of_nonneg_right hsq hy0.le
      _ = _ := mul_comm _ _
  set D₁ : ℝ := max (2 * D') (1 / 𝔠) with hD₁
  have hξ := baZetaExpClaim_holds d hd κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow t ht0 ht1 ε₀ Ψ ℓ hAss ε₁ hε₁ hent D' hD'0 ρ hρ0 hρrad D₁ le_rfl
  have hE2 := baGbyZeta_holds d hd κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow t ht0 ht1 ε₁ hε₁ hent ρ Rr D₁ hRr0 hsep
  obtain ⟨K₀, K₁, Kd, Cg, cg, hK₀, hK₁, hKd, hCg, hcg, hGT⟩ := baGtoAGTRooted_holds d hd 𝔡⁻¹ κ (inv_pos.2 h𝔡) hκ
  set M : ℝ := max 1 (Real.sqrt (1 + (𝔡⁻¹) ^ 2)) with hM
  have hM1 : 1 ≤ M := le_max_left _ _
  set K1 : ℝ := o.Q.g.sizeConst (K₀ * 1) K₁ Kd with hK1
  set K2 : ℝ := o.Q.g.sizeConst Cg (Cg * expC (d - 2) (cg / 2)) (Cg * (1 + expC (d - 2) (cg / 2))) with hK2
  set Kbig : ℝ := K1 * M ^ e1 * Caux with hKbig
  have hK10 : 0 ≤ K1 := BASizeClaim_sizeConst_nonneg o.Q.g (by positivity) hK₁.le hKd
  have hK20 : 0 ≤ K2 := by
    have h1 : 0 ≤ expC (d - 2) (cg / 2) := lwMoment_expC_nonneg (d - 2) (half_pos hcg)
    exact BASizeClaim_sizeConst_nonneg o.Q.g hCg (by positivity) (by positivity)
  apply BAMomentGen_prec_of_whp
  intro τ hτ
  set τ₁ : ℝ := min (min (τ / (2 * A)) (𝔠 * ε₁ / 4)) 1 with hτ₁def
  have hτ₁ : 0 < τ₁ := lt_min (lt_min (by positivity) (by positivity)) one_pos
  refine ⟨_, HighProbAt.inter (tendsto_size sz hsz) (BAMomentGen_entry_whp hd hκ hε h𝔡 hflow ht0 ht1 hassm hτ₁)
    (HighProbAt.inter (tendsto_size sz hsz) (BAMomentGen_whp_of_prec sz hE2 hτ₁)
      (HighProbAt.inter (tendsto_size sz hsz) (BAMomentGen_whp_of_prec sz hξ.2.1 hτ₁) (BAMomentGen_whp_of_prec sz hξ.2.2 hτ₁))), ?_⟩
  filter_upwards [BAMomentGen_Psi_facts hd hκ hε h𝔡 hflow ht0 ht1 hassm hτ₁.le ((min_le_left _ _).trans (min_le_right _ _)),
    lwTail32 sz h𝔠 (mul_pos hcg (div_pos hK hKc)) hsz hband ((o.Q.g.nM + o.Q.g.nA + 1 : ℕ) : ℝ) D,
    hsz.eventually_ge_atTop 1, hsz.eventually_ge_atTop K2, hsz.eventually_ge_atTop (K1 * 2 ^ nE),
    ((tendsto_rpow_atTop (half_pos hτ)).comp hsz).eventually_ge_atTop (Kbig + 2),
    lwXiRad_holds sz hsz 1 0 20 zero_le_one le_rfl (by norm_num) τ₁ hτ₁, lwMomentExp_logW sz h𝔠 hsz hband (max 1 (1 / K)),
    BAMomentGen_Wneg_le hflow.1 (Kf := D + aN + 1) (by positivity) le_rfl, hflow.1.2.2.2.2,
    BAflow_lam0_window κ ε 𝔠 𝔡 sz z hflow]
    with n hPsi htail hN1 hNc hNc1 hNb hrad hlw hWn hWO hn0
  intro ω hω v
  obtain ⟨hω1, hω2, hω3, hω4⟩ := hω
  obtain ⟨hΦ0, hwin, hup⟩ := hPsi
  obtain ⟨hlg1, hlgK⟩ : 1 ≤ Real.log ((sz.W n : ℕ) : ℝ) ∧ 1 / K ≤ Real.log ((sz.W n : ℕ) : ℝ) :=
    ⟨(le_max_left _ _).trans hlw, (le_max_right _ _).trans hlw⟩
  set N : ℝ := ((sz.size n : ℕ) : ℝ) with hN
  set Wn : ℝ := ((sz.W n : ℕ) : ℝ) with hWn'
  set X : ℝ := N ^ τ₁ with hX
  have hN0 : 0 < N := lt_of_lt_of_le one_pos hN1
  have hX1 : 1 ≤ X := Real.one_le_rpow hN1 hτ₁.le
  have hX0 : 0 < X := lt_of_lt_of_le one_pos hX1
  have hXN : X ≤ N := by
    calc X ≤ N ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hN1 (min_le_right _ _)
      _ = N := Real.rpow_one N
  have hW1 : (1 : ℝ) ≤ Wn := Nat.one_le_cast.2 (sz.W_pos n)
  have hW0 : 0 < Wn := lt_of_lt_of_le one_pos hW1
  have hWd : Wn ^ d ≤ N := by
    have : (sz.W n) ^ d ≤ sz.size n := by
      unfold Sizes.size
      exact Nat.pow_le_pow_left (Nat.le_mul_of_pos_right _ (by have := sz.three_le_L n; omega)) d
    rw [hN, hWn']; exact_mod_cast this
  obtain ⟨ht1', hr, -⟩ := ba_G_data hκ sz hflow n (ht0 n) (ht1 n)
  have hη0 := BAExp14a_eta_pos hκ hflow n (ht0 n) (ht1 n)
  have hηt := BAMomentExpGenB_eta_le hκ hflow n (ht0 n) (ht1 n)
  have hη1 := BAExp14c_eta_le_one hκ hflow n (ht0 n) (ht1 n)
  have hΨ0 : 0 < M * X * Φ n 0 := by
    have : 0 < M := lt_of_lt_of_le one_pos hM1
    positivity
  have hΨ1 : M * X * Φ n 0 ≤ 1 := hup.trans (Real.rpow_le_one_of_one_le_of_nonpos hW1 (neg_nonpos.2 (half_pos hε₁).le))
  have hMX : 1 ≤ M * X := one_le_mul_of_one_le_of_one_le hM1 hX1
  have hf0 : Φ n 0 ≤ 1 := le_trans (by simpa using mul_le_mul_of_nonneg_right hMX hΦ0.le) hΨ1
  have hRg := BAMomentExpGenB_R_ge (sz := sz) (z := z) (t := t) (ℓ := ℓ) n p D (pr n v).1 (pr n v).2 hη0
  have hR0 : 0 ≤ BAMomentExpGenB_R sz z t ℓ p D n (pr n v).1 (pr n v).2 :=
    (Real.rpow_nonneg (Nat.cast_nonneg _) _).trans hRg
  have hND : N ^ (-D) ≤ BAMomentExpGenB_R sz z t ℓ p D n (pr n v).1 (pr n v).2 :=
    (lwMomentExp_floor_le hd0 n hD0.le).trans hRg
  have hXA : X ^ A ≤ N ^ (τ / 2) := by
    rw [hX, ← Real.rpow_natCast, ← Real.rpow_mul hN0.le]
    refine Real.rpow_le_rpow_of_exponent_le hN1 ?_
    have hA0 : (0 : ℝ) < A := by positivity
    calc τ₁ * (A : ℝ) ≤ τ / (2 * A) * A :=
          mul_le_mul_of_nonneg_right ((min_le_left _ _).trans (min_le_left _ _)) hA0.le
      _ = τ / 2 := by field_simp
  have hfin : X ^ A * Kbig + 2 ≤ N ^ τ := by
    have hh : N ^ (τ / 2) * N ^ (τ / 2) = N ^ τ := by rw [← Real.rpow_add hN0]; congr 1; ring
    have hKb : 0 ≤ Kbig := by rw [hKbig]; positivity
    have h1' : 1 ≤ N ^ (τ / 2) := Real.one_le_rpow hN1 (half_pos hτ).le
    calc X ^ A * Kbig + 2 ≤ N ^ (τ / 2) * Kbig + N ^ (τ / 2) * 2 :=
          add_le_add (mul_le_mul_of_nonneg_right hXA hKb) (le_mul_of_one_le_left (by norm_num) h1')
      _ = N ^ (τ / 2) * (Kbig + 2) := by ring
      _ ≤ N ^ (τ / 2) * N ^ (τ / 2) := mul_le_mul_of_nonneg_left hNb (by positivity)
      _ = _ := hh
  suffices hmain : ‖o.Q.valW (BAMomentGen_D sz z n (t n) ω)
      (BAMomentExp_wt sz n (dom (sz.L n) (STblk sz n (pr n v).1) (STblk sz n (pr n v).2) (ℓ n)) o) ![(pr n v).1, (pr n v).2]‖ ≤
      (X ^ A * Kbig + 2) * BAMomentExpGenB_R sz z t ℓ p D n (pr n v).1 (pr n v).2 from
    hmain.trans (mul_le_mul_of_nonneg_right hfin hR0)
  by_cases hf : ∃ ℓ' : o.Q.E' → Idx d (sz.L n) (sz.W n), ![(pr n v).1, (pr n v).2] = ℓ' ∘ o.Q.ext
  swap
  · rw [BAPGraph.valW_of_not o.Q _ _ hf, norm_zero]
    have hKb : 0 ≤ Kbig := by rw [hKbig]; positivity
    exact mul_nonneg (by positivity) hR0
  obtain ⟨ℓ', hℓ'⟩ := hf
  rw [BAPGraph.valW_of_factor o.Q _ _ hℓ']
  have e0 : ℓ' (o.Q.ext 0) = (pr n v).1 := (congrFun hℓ' 0).symm
  have e1' : ℓ' (o.Q.ext 1) = (pr n v).2 := (congrFun hℓ' 1).symm
  set Dmv := dom (sz.L n) (STblk sz n (pr n v).1) (STblk sz n (pr n v).2) (ℓ n) with hDmv
  obtain ⟨rep, hrep, hWt0⟩ := BAMomentExpGen_rep sz o hcov n Dmv
  have hA : ∀ a b : Idx d (sz.L n) (sz.W n), ‖(BAMomentGen_D sz z n (t n) ω).G a b - (BAMomentGen_D sz z n (t n) ω).M a b‖ ≤
      M * X * Φ n 0 := fun a b =>
    (hω1 (a, b)).trans (by
      calc X * Φ n 0 = 1 * (X * Φ n 0) := (one_mul _).symm
        _ ≤ M * (X * Φ n 0) := mul_le_mul_of_nonneg_right hM1 (mul_nonneg hX0.le hΦ0.le)
        _ = _ := by ring)
  set L32 : ℝ := Real.log Wn ^ (3 / 2 : ℝ) with hL32
  have hr0 : 0 ≤ K / Kc * L32 := mul_nonneg (div_nonneg hK.le hKc.le) (Real.rpow_nonneg (hlog n) _)
  have hRr' : (Fintype.card (o.Q.E' ⊕ o.Q.I') : ℝ) * (K / Kc * L32) ≤ Rr n :=
    (mul_le_mul_of_nonneg_right hcard hr0).trans (le_of_eq (by have := hKc.ne'; simp only [hRr, hL32]; field_simp; try rfl))
  set ξ : Zd d (sz.L n) → Zd d (sz.L n) → ℝ := fun a b => baZetaVar sz z t ρ D₁ n a b ω with hξdef
  have hξ0 : ∀ a b, 0 ≤ X * ξ a b := fun a b => mul_nonneg hX0.le (hξ.1 n a b ω).1
  have hξG : ∀ (x y : Idx d (sz.L n) (sz.W n)) (a b : Zd d (sz.L n)),
      (zdistD d (sz.L n) ((split d (sz.L n) (sz.W n) x).1 - a) : ℝ) ≤ Rr n →
      (zdistD d (sz.L n) ((split d (sz.L n) (sz.W n) y).1 - b) : ℝ) ≤ Rr n →
      ‖(BAMomentGen_D sz z n (t n) ω).G x y - (BAMomentGen_D sz z n (t n) ω).M x y‖ ≤ X * ξ a b :=
    fun x y a b h1 h2 => hω2 ⟨((x, y), (a, b)), h1, h2⟩
  have hwinv : (Wn ^ d)⁻¹ ≤ 1 * (M * X * Φ n 0) ^ 2 := by
    rw [one_mul, inv_le_iff_one_le_mul₀' (by positivity)]
    exact (one_le_pow_mul_sq_iff (sz.W n) d hW0 hΨ0.le).1 hwin
  have hgt := hGT (sz.L n) (sz.W n) (sz.three_le_L n) (BAflowLam0 sz z n) (BAflowEs sz z n) (t n)
    (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) hn0.1 hn0.2 hr (ht0 n) ht1' o.Q.E' o.Q.I' o.Q.g hQ rep hrep
    (BAMomentGen_D sz z n (t n) ω) rfl rfl rfl rfl (M * X * Φ n 0) 1 (K / Kc * L32) (Rr n)
    (fun a b => X * ξ a b) Dmv hA zero_le_one hwinv hr0 hRr' hξ0 hξG
    (BAMomentExp_wt sz n Dmv o) (BAMomentExp_wt_abs sz n Dmv o) hWt0 ℓ'
  have htl := BAMomentGen_tail_le o.Q.g.counters (sz.W n) (sz.L n) d (sz.W_pos n) (by have := sz.three_le_L n; omega) hΨ0 hΨ1 hNc hK20
    (by rw [mul_assoc] at htail; exact htail)
  -- the auxiliary graph: `Γ^aux_{Dm}(X ξ) = X^{2 nE} Γa.valOn ζ`, floor, pin
  set aa := STblk sz n (pr n v).1 with haa
  set bb := STblk sz n (pr n v).2 with hbb
  set ζ : Zd d (sz.L n) → Zd d (sz.L n) → ℝ := fun a b => ξ a b / X with hζ
  set T : Zd d (sz.L n) → Zd d (sz.L n) → ℝ := fun a b => sfT d (sz.L n) Wn (sz.lam n) (t n)
    (min ((zdistInf d (sz.L n) (a - b) : ℕ) : ℝ) (ℓ n)) with hT
  set ζ' : Zd d (sz.L n) → Zd d (sz.L n) → ℝ := fun a b => min (ζ a b) (T a b) with hζ'
  set S0 := Fintype.piFinset fun _ : Fin (BAShadowPG o.Q).g.nM => Dmv with hS0
  set δ0 : ℝ := Wn ^ (-D') with hδ0
  have hξs : ∀ a b, ξ a b = ξ b a := fun a b => (hξ.1 n a b ω).2
  have hPsiT : PsiT d (sz.L n) Wn (sz.lam n) (t n) = Φ n 0 := by
    rw [hΦ, lwMomentExp_phi_zero]; unfold PsiT Sizes.Bctl; rw [Real.sqrt_eq_rpow]
  have hT1 : ∀ a b, T a b ≤ 1 := fun a b =>
    ((sfT_antitone (le_refl 0) (le_min (Nat.cast_nonneg _) (hAss.2.2.2.1 n))).trans
      ((sfT_zero_le_PsiT hW0).trans (hPsiT ▸ hf0)))
  have hζ0 : ∀ a b, 0 ≤ ζ a b := fun a b => div_nonneg (hξ.1 n a b ω).1 hX0.le
  have hζle : ∀ a b, ζ a b ≤ T a b + δ0 := fun a b => by
    rw [hζ, div_le_iff₀ hX0]; have := hω3 ⟨(a, b), hreg1 n v⟩; simp only [mul_comm] at this ⊢; exact this
  have hζ'0 : ∀ a b, 0 ≤ ζ' a b := fun a b => le_min (hζ0 a b) (sfT_nonneg _)
  have hζ'1 : ∀ a b, ζ' a b ≤ 1 := fun a b => (min_le_right _ _).trans (hT1 a b)
  have hζ'le : ∀ a b, ζ a b ≤ ζ' a b + δ0 := fun a b => by
    by_cases h : ζ a b ≤ T a b
    · change ζ a b ≤ min (ζ a b) (T a b) + δ0
      rw [min_eq_left h]; exact le_add_of_nonneg_right (Real.rpow_nonneg hW0.le _)
    · change ζ a b ≤ min (ζ a b) (T a b) + δ0
      rw [min_eq_right (not_le.1 h).le]; exact hζle a b
  have hTs : ∀ a b, T a b = T b a := fun a b => by simp only [hT]; rw [anpKey_zdistInf_sub_comm]
  have hrow : ∀ α, ∑ β, ζ' α β ^ 2 ≤ ((Wn ^ d) * (baFMz sz z).eta n (t n))⁻¹ := fun α => by
    have hθ : 0 ≤ ((Wn ^ d) * (baFMz sz z).eta n (t n))⁻¹ := by positivity
    calc ∑ β, ζ' α β ^ 2 ≤ ∑ β, (ξ α β / X) ^ 2 := Finset.sum_le_sum fun β _ => pow_le_pow_left₀ (hζ'0 _ _) (min_le_left _ _) 2
      _ = (∑ β, ξ α β ^ 2) / X ^ 2 := by simp [div_pow, Finset.sum_div]
      _ ≤ (X * ((Wn ^ d) * (baFMz sz z).eta n (t n))⁻¹) / X ^ 2 := by gcongr; exact hω4 α
      _ ≤ _ := by rw [div_le_iff₀ (by positivity)]; nlinarith only [mul_nonneg hθ (mul_nonneg hX0.le (sub_nonneg.2 hX1))]
  have hΛ : 1 ≤ Real.log Wn ^ 10 := one_le_pow₀ hlg1
  have hΛX : (Real.log Wn ^ 10) ^ 2 ≤ X := by
    have : (Real.log Wn ^ 10) ^ 2 = Real.log Wn ^ (20 : ℝ) := by rw [← pow_mul, ← Real.rpow_natCast]; norm_num
    rw [this]; linarith only [hrad]
  have hℓ1 : 1 ≤ ℓ n := by
    have h1' := one_le_ellT (L := sz.L n) (g := sz.lam n) (t := t n) (by exact_mod_cast (by have := sz.three_le_L n; omega : 1 ≤ sz.L n))
    have h2' : 1 ≤ K * L32 := by
      have h3 : Real.log Wn ≤ L32 := Real.self_le_rpow_of_one_le hlg1 (by norm_num : (1 : ℝ) ≤ 3 / 2)
      have h4 : 1 ≤ Real.log Wn * K := (div_le_iff₀ hK).1 hlgK
      nlinarith only [mul_le_mul_of_nonneg_left h3 hK.le, h4]
    exact (one_le_mul_of_one_le_of_one_le h2' h1').trans (hreg3 n v).le
  have hgt' : sz.lam n ^ 2 ≤ ((sz.L n : ℕ) : ℝ) ^ 2 * (1 - t n) := by
    have := hreg1 n v
    rw [div_lt_iff₀ (by have := sz.three_le_L n; positivity), mul_comm] at this; exact this.le
  have hpin := hPinH (sz.L n) Wn (sz.lam n) (t n) ((baFMz sz z).eta n (t n)) (ℓ n) (Real.log Wn ^ 10) X hW0
    ((Real.rpow_nonneg hW0.le _).trans hWO.1) ht1' hgt' hη0 hηt hℓ1 (hAss.2.2.2.2.1 n) hΛ hΛX ζ'
    (fun a b => ⟨hζ'0 a b, by simp only [hζ', hζ, hξs a b, hTs a b]⟩) (fun a b => min_le_right _ _) hrow aa bb
  have hexp : ∀ x : ℝ, x ^ (BAShadowPG o.Q).g.nM = x ^ o.Q.g.nM := fun x => by rw [hnMeq]
  rw [hexp (Wn ^ d), hexp X, hexp ((baFMz sz z).eta n (t n))⁻¹] at hpin
  have hval' : Γa.valOn (fun a b => X * ξ a b) (fun _ => aa) (fun _ => bb) S0 =
      auxValOn o.Q.g.shadow (fun a b => X * ξ a b) (fun a => (split d (sz.L n) (sz.W n) (ℓ' a)).1) Dmv := by
    have := hval (κ := Zd d (sz.L n)) (fun a b => X * ξ a b) (fun u v => by rw [hξs u v])
      (fun a => (split d (sz.L n) (sz.W n) (ℓ' a)).1) Dmv
    have e0s : ℓ' ((BAShadowPG o.Q).ext 0) = (pr n v).1 := e0
    have e1s : ℓ' ((BAShadowPG o.Q).ext 1) = (pr n v).2 := e1'
    rw [show (split d (sz.L n) (sz.W n) (ℓ' ((BAShadowPG o.Q).ext 0))).1 = aa by rw [e0s]; rfl,
      show (split d (sz.L n) (sz.W n) (ℓ' ((BAShadowPG o.Q).ext 1))).1 = bb by rw [e1s]; rfl] at this
    exact this
  have hξζ : Γa.valOn (fun a b => X * ξ a b) (fun _ => aa) (fun _ => bb) S0 =
      X ^ nE * (X ^ nE * Γa.valOn ζ (fun _ => aa) (fun _ => bb) S0) := by
    rw [lwMomentExp_valOn_smul Γa hnog ξ X]
    congr 1
    have := lwMomentExp_valOn_smul Γa hnog ζ X (fun _ => aa) (fun _ => bb) S0
    simp only [hζ, mul_div_cancel₀ _ hX0.ne'] at this
    exact this
  have hδ0 : 0 ≤ δ0 := Real.rpow_nonneg hW0.le _
  have hfl := lwMomentExp_valOn_floor Γa ζ ζ' δ0 hδ0 (Real.rpow_le_one_of_one_le_of_nonpos hW1 (neg_nonpos.2 hD'0.le)) hζ0 hζ'0 hζ'1 hζ'le
    (fun _ => aa) (fun _ => bb) S0
  have hΨe : 0 ≤ K1 * (M * X * Φ n 0) ^ e1 := by positivity
  have hWq : 0 ≤ (Wn ^ d) ^ o.Q.g.nM := by positivity
  rw [← hAe, zpow_natCast, ← hval'] at hgt
  rw [hξζ] at hgt
  have hfirst : K1 * (M * X * Φ n 0) ^ e1 * (X ^ (nE + nE) * (X ^ o.Q.g.nM * Caux * ((baFMz sz z).eta n (t n))⁻¹ ^ o.Q.g.nM *
      Φ n 0 ^ (Γa.ordN - (p : ℤ)) * T aa bb ^ p)) ≤ X ^ A * Kbig * BAMomentExpGenB_R sz z t ℓ p D n (pr n v).1 (pr n v).2 := by
    have := lwMomentExp_arith (X := X) (M := M) (f0 := Φ n 0) (η := (baFMz sz z).eta n (t n)) (C := Caux) (K1 := K1) (T := T aa bb)
      (e1 := e1) (k := nE) (len := nE) (q := o.Q.g.nM) (p := p) (a := Γa.ordN) (o := o.Q.g.scalingOrder) hX1 hM1 hΦ0 hf0 hη0 hη1
      (sfT_nonneg _) hCaux.le hK10 hnM hord (by rw [hordN']; omega)
    refine this.trans ?_
    have h5 : ((baFMz sz z).eta n (t n))⁻¹ * Φ n 0 * T aa bb = ((baFMz sz z).eta n (t n))⁻¹ * (sz.Bctl n (t n)) ^ (1 / 2 : ℝ) *
        sfT d (sz.L n) Wn (sz.lam n) (t n) (min ((zdistInf d (sz.L n) (aa - bb) : ℕ) : ℝ) (ℓ n)) := by rw [hΦ, lwMomentExp_phi_zero]
    have hKb : 0 ≤ Kbig := by rw [hKbig]; positivity
    have h6 : X ^ (e1 + nE + nE + o.Q.g.nM) ≤ X ^ A := pow_le_pow_right₀ hX1 (by rw [hAdef]; omega)
    have h7 : (((baFMz sz z).eta n (t n))⁻¹ * Φ n 0 * T aa bb) ^ p ≤ BAMomentExpGenB_R sz z t ℓ p D n (pr n v).1 (pr n v).2 := by
      rw [h5]; exact le_add_of_nonneg_right (Real.rpow_nonneg hW0.le _)
    exact mul_le_mul (mul_le_mul_of_nonneg_right h6 hKb) h7
      (pow_nonneg (mul_nonneg (mul_nonneg (inv_nonneg.2 hη0.le) hΦ0.le) (sfT_nonneg _)) _) (mul_nonneg (pow_nonneg hX0.le _) hKb)
  have hFT : K1 * (M * X * Φ n 0) ^ e1 * ((Wn ^ d) ^ o.Q.g.nM * (X ^ nE * (X ^ nE * (S0.card * (2 ^ nE * δ0))))) ≤ N ^ (-D) := by
    have hc1 : (S0.card : ℝ) ≤ N ^ o.Q.g.nM := by
      rw [hS0, Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      have : Dmv.card ≤ sz.size n := (Finset.card_le_univ Dmv).trans (by
        rw [Fintype.card_fun, ZMod.card, Fintype.card_fin]; unfold Sizes.size
        exact Nat.pow_le_pow_left (Nat.le_mul_of_pos_left _ (sz.W_pos n)) d)
      rw [Nat.cast_pow, hnMeq]; exact pow_le_pow_left₀ (Nat.cast_nonneg _) (Nat.cast_le.2 this) _
    have h2 := hWn 1 hN1
    rw [one_mul] at h2
    have hd2 : δ0 ≤ N ^ (-(D + aN + 1)) := h2
    have e1'' : N ^ (aN : ℝ) * N ^ (-(D + aN + 1)) = N ^ (-D) / N := by
      rw [← Real.rpow_add hN0, eq_div_iff hN0.ne', ← Real.rpow_add_one hN0.ne']; congr 1; ring
    have h8 : (Wn ^ d) ^ o.Q.g.nM * (X ^ nE * (X ^ nE * (S0.card * (2 ^ nE * δ0)))) ≤
        2 ^ nE * (N ^ aN * N ^ (-(D + aN + 1))) := by
      calc _ ≤ N ^ o.Q.g.nM * (N ^ nE * (N ^ nE * (N ^ o.Q.g.nM * (2 ^ nE * N ^ (-(D + aN + 1)))))) := by gcongr
        _ = 2 ^ nE * (N ^ aN * N ^ (-(D + aN + 1))) := by rw [haN]; ring
    have hΨ1' : (M * X * Φ n 0) ^ e1 ≤ 1 := pow_le_one₀ hΨ0.le hΨ1
    calc _ ≤ K1 * 1 * (2 ^ nE * (N ^ (aN : ℝ) * N ^ (-(D + aN + 1)))) := by
          rw [Real.rpow_natCast]; gcongr
      _ = K1 * 2 ^ nE * (N ^ (-D) / N) := by rw [e1'']; ring
      _ ≤ N * (N ^ (-D) / N) := by gcongr
      _ = N ^ (-D) := by field_simp
  rw [hPsiT] at hpin
  have hmain : K1 * (M * X * Φ n 0) ^ e1 * ((Wn ^ d) ^ o.Q.g.nM * (X ^ nE * (X ^ nE * Γa.valOn ζ (fun _ => aa) (fun _ => bb) S0))) ≤
      X ^ A * Kbig * BAMomentExpGenB_R sz z t ℓ p D n (pr n v).1 (pr n v).2 + N ^ (-D) := by
    calc _ ≤ K1 * (M * X * Φ n 0) ^ e1 * ((Wn ^ d) ^ o.Q.g.nM * (X ^ nE * (X ^ nE * (Γa.valOn ζ' (fun _ => aa) (fun _ => bb) S0 +
          S0.card * (2 ^ nE * δ0))))) := by gcongr
      _ = K1 * (M * X * Φ n 0) ^ e1 * (X ^ (nE + nE) * ((Wn ^ d) ^ o.Q.g.nM * Γa.valOn ζ' (fun _ => aa) (fun _ => bb) S0)) +
          K1 * (M * X * Φ n 0) ^ e1 * ((Wn ^ d) ^ o.Q.g.nM * (X ^ nE * (X ^ nE * (S0.card * (2 ^ nE * δ0))))) := by ring
      _ ≤ _ := add_le_add ((mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpin (by positivity)) hΨe).trans hfirst) hFT
  have hfin2 : X ^ A * Kbig * BAMomentExpGenB_R sz z t ℓ p D n (pr n v).1 (pr n v).2 + N ^ (-D) + N ^ (-D) ≤
      (X ^ A * Kbig + 2) * BAMomentExpGenB_R sz z t ℓ p D n (pr n v).1 (pr n v).2 := by nlinarith only [hND]
  exact hgt.trans ((add_le_add hmain htl).trans hfin2)

/-- From `≺` of `‖𝒱_o‖` to `≺` of `‖𝔼 𝒱_o‖` (`BAExp14a_prec_integral`: polynomial envelope `BAMomentExpGenB_env` and the floor `R ≥ N^{-D}`; twin of `lwExpTerm_prec_integral` as used in
`lwMomentExp_pin_gen`, and of `BAMomentGen_prec_int`, `Graph/BAMomentGen.lean:1175`). -/
private theorem BAMomentExpGenB_prec_int (p : ℕ) {D : ℝ} (hD : 0 < D) {V : ℕ → Type}
    (pr : ∀ n, V n → Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n))
    (dom : ∀ (L : ℕ) [NeZero L], Zd d L → Zd d L → ℝ → Finset (Zd d L)) (o : BAProvOut (baPG (BAGraph.ofLGraph (fxyPowGraph p))))
    (hQ : o.Q.g.Normal)
    (hprec : PrecL sz (Sizes.seqP (sz.withLam 0)) (U := V)
      (fun n v ω => ‖o.Q.valW (BAMomentGen_D sz z n (t n) ω)
        (BAMomentExp_wt sz n (dom (sz.L n) (STblk sz n (pr n v).1) (STblk sz n (pr n v).2) (ℓ n)) o) ![(pr n v).1, (pr n v).2]‖)
      (fun n v _ => BAMomentExpGenB_R sz z t ℓ p D n (pr n v).1 (pr n v).2)) :
    PrecL sz (Sizes.seqP (sz.withLam 0)) (U := V)
      (fun n v _ => ‖∫ ω, o.Q.valW (BAMomentGen_D sz z n (t n) ω)
        (BAMomentExp_wt sz n (dom (sz.L n) (STblk sz n (pr n v).1) (STblk sz n (pr n v).2) (ℓ n)) o) ![(pr n v).1, (pr n v).2]
        ∂(BAExp14a_μ sz)‖)
      (fun n v _ => BAMomentExpGenB_R sz z t ℓ p D n (pr n v).1 (pr n v).2) := by
  obtain ⟨Kenv, henv⟩ := BAMomentExpGenB_env hd hκ hε h𝔡 hflow ht0 ht1 hassm o.Q hQ
  exact BAExp14a_prec_integral (P := BAExp14a_μ sz) (Sizes.tendsto_size sz hflow.1.2.2.1)
    (fun n v ω => o.Q.valW (BAMomentGen_D sz z n (t n) ω)
      (BAMomentExp_wt sz n (dom (sz.L n) (STblk sz n (pr n v).1) (STblk sz n (pr n v).2) (ℓ n)) o) ![(pr n v).1, (pr n v).2])
    (fun n v => BAMomentExpGenB_R sz z t ℓ p D n (pr n v).1 (pr n v).2) (Kenv := Kenv) (Kf := D)
    (henv.mono fun n h v ω => h _ _ ω _ (BAMomentExp_wt_abs sz n _ o))
    (Eventually.of_forall fun n v => (lwMomentExp_floor_le (by omega) n hD.le).trans
      (BAMomentExpGenB_R_ge n p D (pr n v).1 (pr n v).2 (BAExp14a_eta_pos hκ hflow n (ht0 n) (ht1 n))))
    hprec

omit hd hκ hε h𝔡 hflow ht0 ht1 hassm

end Outputs

/-! ## 5. The three pins from the engine with provenance (target 8) -/

/-- **`lem:LW_moment_exp` at BA for the domain form** (the target `LWMomentExpG` at the `baPin` data for `f^{dom}` on the pairs/lengths in `reg`; twin of `LWMomentExpOn`,
`Graph/LWMomentExp.lean:86`; `dom ≡ univ`, `reg ≡ True` is `LWMomentExpG`): `E |f^{dom}_{xy}|^p ≺ (η⁻¹ B_{ctl}^{1/2} 𝖳_t(|a-b|∧ℓ))^p + W^{-D}` on `λ²/L² < 1 - t` and `reg`. -/
def BAMomentExpOn (d : ℕ) (dom : ∀ (L : ℕ) [NeZero L], Zd d L → Zd d L → ℝ → Finset (Zd d L))
    (reg : ∀ (sz : Sizes d) (n : ℕ), ℝ → ℝ → Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n) → Prop) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ (p : ℕ), 2 ∣ p → ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z →
    ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ BAflowT0 sz z n) →
      ∀ (ε₀ : ℝ) (Ψ ℓ : ℕ → ℝ), LWAssmExpgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) t ε₀ Ψ ℓ → ∀ D : ℝ, 0 < D →
        PrecL sz (Sizes.seqP (sz.withLam 0)) (U := fun n => {q : Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n) //
            sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 < 1 - t n ∧ reg sz n (t n) (ℓ n) q})
          (fun n q _ => ∫ ω, ‖LWfgD (baFMz sz z) n (t n) ω (dom (sz.L n) (STblk sz n q.1.1) (STblk sz n q.1.2) (ℓ n)) q.1.1 q.1.2‖ ^ p
            ∂(Sizes.seqP (sz.withLam 0)))
          (fun n q _ => (((baFMz sz z).eta n (t n))⁻¹ * (sz.Bctl n (t n)) ^ (1 / 2 : ℝ) *
            sfT d (sz.L n) ((sz.W n : ℕ) : ℝ) (sz.lam n) (t n)
              (min ((zdistInf d (sz.L n) (STblk sz n q.1.1 - STblk sz n q.1.2) : ℕ) : ℝ) (ℓ n))) ^ p + ((sz.W n : ℕ) : ℝ) ^ (-D))

/-- **far pin** (`lem:LW_moment_exp_far`; engine with provenance, rooted `GtoAG`, `lwMomExpFar_and`) in `¬ regA` (twin of `LWMomExpFarPin`, `Graph/LWMomentExp.lean:99`) -/
def BAMomExpFarPin (d : ℕ) (K : ℝ) : Prop :=
  BAMomentExpOn d (fun L _ a b ℓ => domFar d L a b ℓ) fun sz n t ℓ q => ¬ regA d K sz n t ℓ q

/-- **near pins** (`lem:LW_moment_exp_near`, split by the centre; `AnpNearInfAt`) in `¬ regA` (twin of `LWMomExpNearPin`, `Graph/LWMomentExp.lean:102`) -/
def BAMomExpNearPin (d : ℕ) (K : ℝ) : Prop :=
  BAMomentExpOn d (fun L _ a _ ℓ => domNearA d L a ℓ) (fun sz n t ℓ q => ¬ regA d K sz n t ℓ q) ∧
    BAMomentExpOn d (fun L _ a b ℓ => domNearB d L a b ℓ) fun sz n t ℓ q => ¬ regA d K sz n t ℓ q

/-- **a pin from its normalized deterministic bound** (twin of `lwMomentExp_pin_gen`, `Graph/LWMomentExp.lean:1302`; `7_8:1620-1660`): the engine with provenance
`ba_localregularXP`, the weighted expansion, the three kinds of outputs (errors, `𝓜_x = 𝓜_y`, `𝓜_x ≠ 𝓜_y`), the upgrade `≺ → 𝔼`, the sum over the list; every `K > 0`. -/
theorem BAMomentExp_pin_gen {d : ℕ} {K : ℝ} (hK : 0 < K) (dom : ∀ (L : ℕ) [NeZero L], Zd d L → Zd d L → ℝ → Finset (Zd d L))
    (hPin : 3 ≤ d → ∀ {p q : ℕ}, 0 < p → ∀ Γ : NGraph p q, Γ.NoGhost → Γ.IsNested → lwMomExpFar_ownExt Γ → lwMomentExp_PinN d Γ dom) :
    BAMomentExpOn d dom (fun sz n t ℓ q => ¬ regA d K sz n t ℓ q) := by
  classical
  intro hd κ ε 𝔡 hκ hε h𝔡 p hp2 𝔠 sz z hflow t ht0 ht1 ε₀ Ψ ℓ hAss D hD
  have hsz : sz.SizeTendsto := hflow.1.2.2.1
  have h𝔠 : 0 < 𝔠 := hflow.1.1
  have htl1 : ∀ n, t n < 1 := fun n => (ba_G_data hκ sz hflow n (ht0 n) (ht1 n)).1
  have hd0 : d ≠ 0 := by omega
  rcases Nat.eq_zero_or_pos p with rfl | hp0
  · refine (BAExp14a_det_iff (P := BAExp14a_μ sz) (Sizes.tendsto_size sz hsz) _ _).2 fun τ hτ => ?_
    filter_upwards [hsz.eventually_ge_atTop 1] with n hN1 v
    have hX : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ τ := Real.one_le_rpow hN1 hτ.le
    have hW : 0 ≤ ((sz.W n : ℕ) : ℝ) ^ (-D) := Real.rpow_nonneg (Nat.cast_nonneg _) _
    simp only [pow_zero, integral_const, probReal_univ, smul_eq_mul, mul_one]
    nlinarith
  have hpe : Even p := even_iff_two_dvd.2 hp2
  obtain ⟨ε₁, hε₁, hassm⟩ := BAMomentExpGenB_assm hd hκ hε h𝔡 hflow ht0 ht1 hAss
  set K0 : ℕ := ⌈1 / 𝔠⌉₊ with hK0def
  have hK0 : 1 / 𝔠 ≤ K0 := Nat.le_ceil _
  obtain ⟨outs, errs, hcovx, hconcl, hwaved, hX⟩ := ba_localregularXP p (ε₁ / 2) (half_pos hε₁) K0 d ((D + 1) / 𝔠)
  set Kn : ℕ := ((outs ++ errs).map fun o => Fintype.card (o.Q.E' ⊕ o.Q.I')).sum with hKn
  set Kc : ℝ := (Kn : ℝ) + 1 with hKc
  have hKc1 : 1 ≤ Kc := by have : (0 : ℝ) ≤ Kn := Nat.cast_nonneg _; linarith
  have hKc0 : 0 < Kc := lt_of_lt_of_le one_pos hKc1
  have hcard : ∀ o ∈ outs ++ errs, (Fintype.card (o.Q.E' ⊕ o.Q.I') : ℝ) ≤ Kc := by
    intro o ho
    have : Fintype.card (o.Q.E' ⊕ o.Q.I') ≤ Kn :=
      List.le_sum_of_mem (List.mem_map_of_mem (f := fun o : BAProvOut (baPG (BAGraph.ofLGraph (fxyPowGraph p))) =>
        Fintype.card (o.Q.E' ⊕ o.Q.I')) ho)
    have h2 : (Fintype.card (o.Q.E' ⊕ o.Q.I') : ℝ) ≤ Kn := by exact_mod_cast this
    rw [hKc]; linarith
  obtain ⟨hup5a, hup5b⟩ := baLocRegConcl_upto5 p (ε₁ / 2) K0 d ((D + 1) / 𝔠) (outs.map (·.Q)) (errs.map (·.Q)) hconcl
  let V : ℕ → Type := fun n => {q : Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n) //
    sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 < 1 - t n ∧ ¬ regA d K sz n (t n) (ℓ n) q}
  have hper : ∀ o ∈ outs ++ errs, PrecL sz (Sizes.seqP (sz.withLam 0)) (U := V)
      (fun n v ω => ‖o.Q.valW (BAMomentGen_D sz z n (t n) ω)
        (BAMomentExp_wt sz n (dom (sz.L n) (STblk sz n v.1.1) (STblk sz n v.1.2) (ℓ n)) o) ![v.1.1, v.1.2]‖)
      (fun n v _ => BAMomentExpGenB_R sz z t ℓ p D n v.1.1 v.1.2) := by
    intro o ho
    have hmem : o.Q ∈ (outs.map (·.Q)) ++ (errs.map (·.Q)) := by
      rw [← List.map_append]; exact List.mem_map_of_mem ho
    obtain ⟨P0, -, -, hQ, -⟩ := hconcl.2.2.1 o.Q hmem
    obtain ⟨-, hnM, -⟩ := hup5a o.Q hmem
    obtain ⟨-, hcov⟩ := hcovx o ho
    rcases List.mem_append.1 ho with h | h
    · have hmo : o.Q ∈ outs.map (·.Q) := List.mem_map_of_mem h
      obtain ⟨-, h6, -⟩ := hconcl.1 o.Q hmo
      obtain ⟨-, -, h345⟩ := hup5b o.Q hmo
      by_cases hmol : o.Q.g.mol (Sum.inl (o.Q.ext 0)) = o.Q.g.mol (Sum.inl (o.Q.ext 1))
      · refine BAMomentExpGenB_prec_scale hd hκ hε h𝔡 hflow ht0 ht1 hassm p hD (Krad := K / Kc) (div_pos hK hKc0)
          (V := V) (fun n v => v.1) dom o hQ (by rw [hmol]; exact BAMomentGen_mem_mol_self _ _) ?_
        intro n v
        have hreg := not_or.1 v.2.2
        have h1 : (zdistInf d (sz.L n) (STblk sz n v.1.1 - STblk sz n v.1.2) : ℝ) ≤ (lwBdist d (sz.L n) (sz.W n) v.1.1 v.1.2 : ℝ) := by
          exact_mod_cast zdistInf_le_zdistD d (sz.L n) _
        have hL0 : 0 ≤ K * Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ) :=
          mul_nonneg hK.le (Real.rpow_nonneg (Real.log_nonneg (Nat.one_le_cast.2 (sz.W_pos n))) _)
        have hell : (1 : ℝ) ≤ ellT (sz.L n) (sz.lam n) (t n) := one_le_ellT (Nat.one_le_cast.2 (by have := sz.three_le_L n; omega))
        have h2 := not_le.1 hreg.1
        calc (Fintype.card (o.Q.E' ⊕ o.Q.I') : ℝ) * (K / Kc * Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ))
            ≤ Kc * (K / Kc * Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ)) :=
              mul_le_mul_of_nonneg_right (hcard o ho) (by positivity)
          _ = K * Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ) := by field_simp
          _ ≤ K * Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ) * ellT (sz.L n) (sz.lam n) (t n) := le_mul_of_one_le_right hL0 hell
          _ < _ := h2.trans_le h1
      · have hxy : (BAShadowPG o.Q).g.molOf (Sum.inl ((BAShadowPG o.Q).ext 0)) ≠ (BAShadowPG o.Q).g.molOf (Sum.inl ((BAShadowPG o.Q).ext 1)) := by
          intro h'
          apply hmol
          have h'' : o.Q.g.shadow.molOf (Sum.inl (o.Q.ext 0)) = o.Q.g.shadow.molOf (Sum.inl (o.Q.ext 1)) := h'
          exact (BAAtom_mol_eq_of_mem o.Q.g ((BAAtom_shadow_molOf_eq_iff o.Q.g _ _).1 h'')).symm
        exact BAMomentExpGenB_prec_anp hd hκ hε h𝔡 hflow ht0 ht1 hassm hAss hp0 hK hKc0 hD (V := V) (fun n v => v.1) dom o
          (fun Γ hNG hN hO => hPin hd hp0 Γ hNG hN hO) hQ h345 hxy hnM h6 (hcard o ho) hcov (fun n v => v.2.1)
          (fun n v => not_le.1 (not_or.1 v.2.2).2)
    · have hme : o.Q ∈ errs.map (·.Q) := List.mem_map_of_mem h
      exact BAMomentExpGenB_prec_err hd hκ hε h𝔡 hflow ht0 ht1 hassm p hD hK0 le_rfl (V := V) (fun n v => v.1) dom o hQ (hconcl.2.1 o.Q hme)
  have hint : ∀ o ∈ outs ++ errs, PrecL sz (Sizes.seqP (sz.withLam 0)) (U := V)
      (fun n v _ => ‖∫ ω, o.Q.valW (BAMomentGen_D sz z n (t n) ω)
        (BAMomentExp_wt sz n (dom (sz.L n) (STblk sz n v.1.1) (STblk sz n v.1.2) (ℓ n)) o) ![v.1.1, v.1.2] ∂(BAExp14a_μ sz)‖)
      (fun n v _ => BAMomentExpGenB_R sz z t ℓ p D n v.1.1 v.1.2) := by
    intro o ho
    have hmem : o.Q ∈ (outs.map (·.Q)) ++ (errs.map (·.Q)) := by
      rw [← List.map_append]; exact List.mem_map_of_mem ho
    obtain ⟨P0, -, -, hQ, -⟩ := hconcl.2.2.1 o.Q hmem
    exact BAMomentExpGenB_prec_int hd hκ hε h𝔡 hflow ht0 ht1 hassm p hD (V := V) (fun n v => v.1) dom o hQ (hper o ho)
  refine (BAExp14a_det_iff (P := BAExp14a_μ sz) (Sizes.tendsto_size sz hsz) _ _).2 fun τ hτ => ?_
  let F : BAProvOut (baPG (BAGraph.ofLGraph (fxyPowGraph p))) → ∀ n, V n → ℝ := fun o n v =>
    ‖∫ ω, o.Q.valW (BAMomentGen_D sz z n (t n) ω)
      (BAMomentExp_wt sz n (dom (sz.L n) (STblk sz n v.1.1) (STblk sz n v.1.2) (ℓ n)) o) ![v.1.1, v.1.2] ∂(BAExp14a_μ sz)‖
  let G : ∀ n, V n → ℝ := fun n v => BAMomentExpGenB_R sz z t ℓ p D n v.1.1 v.1.2
  have hG : ∀ n v, 0 ≤ G n v := fun n v => (Real.rpow_nonneg (Nat.cast_nonneg _) _).trans
    (BAMomentExpGenB_R_ge n p D v.1.1 v.1.2 (BAExp14a_eta_pos hκ hflow n (ht0 n) (ht1 n)))
  have hsum := lwMoment_sum_det sz hsz (V := V) (outs ++ errs) F G hG
    (fun o ho => (BAExp14a_det_iff (P := BAExp14a_μ sz) (Sizes.tendsto_size sz hsz) (F o) G).1 (hint o ho)) τ hτ
  filter_upwards [hsum] with n hn
  intro v
  by_cases ht0' : t n = 0
  · have h0 : ∀ (Dm : Finset (Zd d (sz.L n))) (x y : Idx d (sz.L n) (sz.W n)) (ω : sz.SeqΩ),
        LWfgD (baFMz sz z) n (t n) ω Dm x y = 0 := by
      intro Dm x y ω
      rw [ht0']
      exact BAMomentExp_LWfgD_zero hκ hflow n (by have := ht1 n; rwa [ht0'] at this) Dm ω x y
    have hz : ∀ ω : sz.SeqΩ, ‖LWfgD (baFMz sz z) n (t n) ω (dom (sz.L n) (STblk sz n v.1.1) (STblk sz n v.1.2) (ℓ n)) v.1.1 v.1.2‖ ^ p = 0 :=
      fun ω => by
        rw [h0]
        simp [hp0.ne']
    have hzero : ∫ ω, ‖LWfgD (baFMz sz z) n (t n) ω (dom (sz.L n) (STblk sz n v.1.1) (STblk sz n v.1.2) (ℓ n)) v.1.1 v.1.2‖ ^ p
        ∂(BAExp14a_μ sz) = 0 := by
      simp only [hz, integral_zero]
    exact hzero.trans_le (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) (hG n v))
  · have htp : 0 < t n := lt_of_le_of_ne (ht0 n) (Ne.symm ht0')
    exact le_trans (BAMomentExp_expand hκ hflow ht0 ht1 hpe n (outs := outs ++ errs) (fun o ho => hwaved o ho) hX _ v.1.1 v.1.2 htp) (hn v)

/-- **the far pin** (`lem:LW_moment_exp_far`, `7_8:1620-1643`) for every `K > 0`: `AnpFarAndAt` (`lwMomExpFar_and`) with the domain `domFar` (twin of `lwMomentExp_farPin_holds`,
`Graph/LWMomentExp.lean:1422`; the model-free normalized pin `lwMomentExp_pinN_far`) -/
theorem baMomExpFarPin_holds (d : ℕ) {K : ℝ} (hK : 0 < K) : BAMomExpFarPin d K :=
  BAMomentExp_pin_gen hK (fun L _ a b ℓ => domFar d L a b ℓ)
    (fun hd p q hp Γ hNG hN hO => lwMomentExp_pinN_far hd hp (lwMomExpFar_and d p q Γ hNG hN hO))

/-- **the near pins** (`lem:LW_moment_exp_near`, `7_8:1648-1660`) for every `K > 0`: `AnpNearInfAt` (`lwMomExp_nearInf`) with the centres `a` and `b` (twin of
`lwMomentExp_nearPin_holds`, `Graph/LWMomentExp.lean:1426`) -/
theorem baMomExpNearPin_holds (d : ℕ) {K : ℝ} (hK : 0 < K) : BAMomExpNearPin d K :=
  ⟨BAMomentExp_pin_gen hK (fun L _ a _ ℓ => domNearA d L a ℓ)
      (fun hd p q hp Γ hNG hN hO => lwMomentExp_pinN_near (lwMomExp_nearInf d hd p q Γ hNG hN) _ (fun L _ a _ => a)
        (fun L _ a b ℓ α hα => (Finset.mem_filter.1 hα).2)),
    BAMomentExp_pin_gen hK (fun L _ a b ℓ => domNearB d L a b ℓ)
      (fun hd p q hp Γ hNG hN hO => lwMomentExp_pinN_near (lwMomExp_nearInf d hd p q Γ hNG hN) _ (fun L _ _ b => b)
        (fun L _ a b ℓ α hα => (Finset.mem_filter.1 hα).2.2))⟩

/-! ## 6. The assembly and the target (target 9) -/

/-- A deterministic `≺` at the block Anderson law is the pointwise bound for large `n` (`BAExp14a_det_iff` at `PrecL`). -/
private theorem BAMomentExpGenB_det {d : ℕ} (sz : Sizes d) (hsz : sz.SizeTendsto) {V : ℕ → Type} (F G : ∀ n, V n → ℝ) :
    PrecL sz (Sizes.seqP (sz.withLam 0)) (U := V) (fun n v _ => F n v) (fun n v _ => G n v) ↔
      ∀ τ : ℝ, 0 < τ → ∀ᶠ n in atTop, ∀ v, F n v ≤ ((sz.size n : ℕ) : ℝ) ^ τ * G n v :=
  BAExp14a_det_iff (P := BAExp14a_μ sz) (Sizes.tendsto_size sz hsz) F G

/-- **the assembly** (twin of `LWMomentExpOfParts`, `Graph/LWMomentExp.lean:106`): (A) in the regime `regA K` (`BAMomExpNoExp`), the far pin and both near pins give the target
`BALWMomentExp d` (`LWMomentExpG` at the `baPin` data). -/
def BAMomentExpOfParts (d : ℕ) : Prop :=
  ∀ K : ℝ, 0 < K → BAMomExpNoExp d K → BAMomExpFarPin d K → BAMomExpNearPin d K → BALWMomentExp d

/-- **`baMomentExp_of_parts`** (`7_8:1595-1611`; twin of `lwMomentExp_of_parts`, `Graph/LWMomentExp.lean:179`): (A) on `regA K`; on `¬ regA K` the exact split
`f = f^> + f^(a) + f^(b)` (`LWfg_split`) with `E|f|^p ≤ 3^{p-1} Σ E|f^•|^p` (`norm_add3_pow_le`, `BAMomentExp_integrable`). -/
theorem baMomentExp_of_parts (d : ℕ) : BAMomentExpOfParts d := by
  intro K hK hA hF hN hd κ ε 𝔡 hκ hε h𝔡 p hp2 𝔠 sz z hflow t ht0 htT ε₀ Ψ ℓ hAss D hD
  have hsz : sz.SizeTendsto := hflow.1.2.2.1
  have hA' := (BAMomentExpGenB_det sz hsz _ _).1 (hA hd κ ε 𝔡 hκ hε h𝔡 p hp2 𝔠 sz z hflow t ht0 htT ε₀ Ψ ℓ hAss D hD)
  have hF' := (BAMomentExpGenB_det sz hsz _ _).1 (hF hd κ ε 𝔡 hκ hε h𝔡 p hp2 𝔠 sz z hflow t ht0 htT ε₀ Ψ ℓ hAss D hD)
  have hN1 := (BAMomentExpGenB_det sz hsz _ _).1 (hN.1 hd κ ε 𝔡 hκ hε h𝔡 p hp2 𝔠 sz z hflow t ht0 htT ε₀ Ψ ℓ hAss D hD)
  have hN2 := (BAMomentExpGenB_det sz hsz _ _).1 (hN.2 hd κ ε 𝔡 hκ hε h𝔡 p hp2 𝔠 sz z hflow t ht0 htT ε₀ Ψ ℓ hAss D hD)
  refine (BAMomentExpGenB_det sz hsz _ _).2 fun τ hτ => ?_
  rcases Nat.eq_zero_or_pos p with hp0 | hp0
  · subst hp0
    filter_upwards [hsz.eventually_ge_atTop 1] with n hN1' q
    have hX : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ τ := Real.one_le_rpow hN1' hτ.le
    have hW : 0 ≤ ((sz.W n : ℕ) : ℝ) ^ (-D) := Real.rpow_nonneg (Nat.cast_nonneg _) _
    have hI : ∫ ω : sz.SeqΩ, ‖LWfg (baFMz sz z) n (t n) ω q.1.1 q.1.2‖ ^ 0 ∂(BAExp14a_μ sz) = 1 := by
      simp only [pow_zero, integral_const, smul_eq_mul, mul_one]; simp
    refine (le_of_eq hI).trans ?_
    simp only [pow_zero]
    nlinarith
  · filter_upwards [hA' τ hτ, hF' (τ / 2) (half_pos hτ), hN1 (τ / 2) (half_pos hτ), hN2 (τ / 2) (half_pos hτ),
      ((tendsto_rpow_atTop (half_pos hτ)).comp hsz).eventually_ge_atTop ((3 : ℝ) ^ p)] with n hA1 hF1 hN11 hN21 h3
    intro q
    by_cases hreg : regA d K sz n (t n) (ℓ n) q.1
    · exact hA1 ⟨q.1, q.2, hreg⟩
    · have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
      have e1 := hF1 ⟨q.1, q.2, hreg⟩
      have e2 := hN11 ⟨q.1, q.2, hreg⟩
      have e3 := hN21 ⟨q.1, q.2, hreg⟩
      have hη0 := BAExp14a_eta_pos hκ hflow n (ht0 n) (htT n)
      have hR0 : 0 ≤ BAMomentExpGenB_R sz z t ℓ p D n q.1.1 q.1.2 :=
        (Real.rpow_nonneg (Nat.cast_nonneg _) _).trans (BAMomentExpGenB_R_ge n p D q.1.1 q.1.2 hη0)
      refine le_trans (lwMomentExp_comb ?_ e1 e2 e3 hp0 h3 hR0) (le_of_eq ?_)
      swap
      · rw [← Real.rpow_add hN0]; congr 2; ring
      set f1 : sz.SeqΩ → ℝ := fun ω => ‖LWfgD (baFMz sz z) n (t n) ω
        (domFar d (sz.L n) (STblk sz n q.1.1) (STblk sz n q.1.2) (ℓ n)) q.1.1 q.1.2‖ ^ p with hf1
      set f2 : sz.SeqΩ → ℝ := fun ω => ‖LWfgD (baFMz sz z) n (t n) ω
        (domNearA d (sz.L n) (STblk sz n q.1.1) (ℓ n)) q.1.1 q.1.2‖ ^ p with hf2
      set f3 : sz.SeqΩ → ℝ := fun ω => ‖LWfgD (baFMz sz z) n (t n) ω
        (domNearB d (sz.L n) (STblk sz n q.1.1) (STblk sz n q.1.2) (ℓ n)) q.1.1 q.1.2‖ ^ p with hf3
      have hpt : ∀ ω : sz.SeqΩ, ‖LWfg (baFMz sz z) n (t n) ω q.1.1 q.1.2‖ ^ p ≤ 3 ^ (p - 1) * (f1 ω + f2 ω + f3 ω) := by
        intro ω
        rw [LWfg_split (baFMz sz z) n (t n) (ℓ n) ω q.1.1 q.1.2]
        exact norm_add3_pow_le _ _ _ hp0
      have i1 : Integrable f1 (BAExp14a_μ sz) := BAMomentExp_integrable hκ hflow n (ht0 n) (htT n) p _ q.1.1 q.1.2
      have i2 : Integrable f2 (BAExp14a_μ sz) := BAMomentExp_integrable hκ hflow n (ht0 n) (htT n) p _ q.1.1 q.1.2
      have i3 : Integrable f3 (BAExp14a_μ sz) := BAMomentExp_integrable hκ hflow n (ht0 n) (htT n) p _ q.1.1 q.1.2
      calc _ ≤ ∫ ω, (3 : ℝ) ^ (p - 1) * (f1 ω + f2 ω + f3 ω) ∂(BAExp14a_μ sz) :=
            integral_mono_of_nonneg (Eventually.of_forall fun ω => by positivity) (((i1.add i2).add i3).const_mul _)
              (Eventually.of_forall hpt)
        _ = (3 : ℝ) ^ (p - 1) * (∫ ω, f1 ω ∂(BAExp14a_μ sz) + ∫ ω, f2 ω ∂(BAExp14a_μ sz) + ∫ ω, f3 ω ∂(BAExp14a_μ sz)) := by
            rw [integral_const_mul]
            congr 1
            rw [integral_add (f := fun a => f1 a + f2 a) (g := f3) (i1.add i2) i3, integral_add i1 i2]

/-- **Target 9, the statement def** (`T2483_MomentExpOfAnp`): `lem:LW_moment_exp` at BA from G4 on the BA carrier (`BAAnpAuxG`, `Graph/BAAuxGraph2B.lean:865`, L3d1's pin), which
enters only through regime (A) (`BALWMoment`, target 3).  `BAAnpAuxG` occurs only here (and in instances). -/
def BALWMomentExpOfAnp (d : ℕ) : Prop := BAAnpAuxG d → BALWMomentExp d

/-- **Target 9** (`T2483_MomentExp`; `lem:LW_moment_exp` at BA, `7_8:78-83`; twin of `lwMomentExp_holds`, `Graph/LWMomentExp.lean:1436`; `K = 1`): no path binder
(`baLWMomentOfAnp_closed`, target 3); the far and near pins are proved for every `K > 0` from the engine with provenance and the model-free NGraph pins; `BAAnpAuxG`
(L3d1) enters only through (A). -/
theorem baLWMomentExp_of_anp : ∀ d : ℕ, BALWMomentExpOfAnp d := fun d hAnp =>
  baMomentExp_of_parts d 1 one_pos (baMomExpNoExp_of_moment d (baLWMomentOfAnp_closed d hAnp) 1 one_pos)
    (baMomExpFarPin_holds d one_pos) (baMomExpNearPin_holds d one_pos)

/-! ## 7. Compiled nonempty instances of targets 6-9 (target 10 (i)-(iii))

Data (`BA/LWPinsBA.lean` §3, `BA/FlowPins.lean` §Inst, `Graph/LWPins.lean` §8): `d = 3`, `sz0` (`n = 0`: `L = 4`, `W = 32`, `N = 2097152`, `λ = 1/64`), the flow `flow_sz0`
(`κ = 1/2`, `ε = 𝔡 = 1/10`, `𝔠 = 1/6`), `z = zSeq`, `t ≡ 1/2 ≤ BAflowT0` (`half_lt_t0`), `ε₀ = 1/20`, `Ψ_n = W_n^{-1}` (`Ψ0`, `window0`), `ℓ_n = ℓ_t` (`ℓT`: `1 ≤ ℓ_n ≤ (log W)^{10} ℓ_t`),
`p = 2`.  What stays a hypothesis is another gate's pin: `STInitialGT2gL`, `LWLoopExpgL` (inside `LWAssmExpgL`) and `BAAnpAuxG 3` (L3d1). -/

end RBM.BA

end
