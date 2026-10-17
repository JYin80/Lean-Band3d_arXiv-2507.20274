/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Graph.LWMoment
import RBM3D.Graph.BAEngine
import RBM3D.Graph.BAShapeO2B
import RBM3D.Graph.BALocReg1B
import RBM3D.Graph.BAAtom2
import RBM3D.Graph.BAAuxGraph2B
import RBM3D.Graph.BASizeClaim2
import RBM3D.Graph.BAExp14aB
import RBM3D.Graph.BAExp14c
import RBM3D.Graph.BAExp14d
import RBM3D.BA.LWPinsBA
import RBM3D.BA.GbEXPav

/-!
# `lem:LW_moment` at BA (part A): the carrier, the statement and the far pairs

Paper: (7.4) `fxyG_sum`; Lemma 7.1 (`lem:LW_moment`) and its proof; (7.9) `eq:boundfxyGinf`;
(7.12) `eq:far_ab`; Subappendix B.3 (the end of the proof of Lemma B.7).  This is the BA counterpart
of `Graph/LWMoment.lean` (the band proof) in new files.

## Contents (namespace `RBM.BA`; helpers carry the stem `BAMomentGen_`)

1. The carrier `f_{xy}` `LWfg` with the BA bridge `LWfg_baFMz`.
2. The generic statement `LWMomentG`, the BA reading `BALWMoment`.
3. `ba_localregularX_holds`: `ba_localregularX` with its shape binder discharged by
   `baShapeLL_e2_tn`, `baShapeLL_macroA_tn`, `baShapeLL_macroB_tn`.
4. The far pairs (as `LWMoment` Sections 1-8): `≺` tools at the BA law, the model-free arithmetic,
   the rescaled data of the slice `BAMomentGen_D` and the constants of its kernels, the floor, the
   three kinds of output (error, `𝓜_x = 𝓜_y` through the scale-mole tail `BAMomentGen_scalemole`,
   `𝓜_x ≠ 𝓜_y` through `baGtoAGT_holds` and `lem:Anp`), the envelope, `≺ → 𝔼`, the continuity of
   graph values, the expansion identity `BAMomentGen_expand`, and the assembly
   `BAMomentGen_prec_far`.

`LWAssmgL`, `LWLoop2gL` and `BAAnpAuxG` occur only inside definitions (`LWMomentG`,
`BALWMomentOfAnp`).  The lemmas of this file take `LWAssmgL` unfolded (`hassm`, with `LWLoop2gL`
unfolded) and `lem:Anp` instantiated at the data and at one graph (`hAnpQ`, `hAnpL`, with `LWXigL`
unfolded); the callers (`baLWMoment_of_anp`) pass the hypotheses of the statement (definitionally
equal) and the instances of `BAAnpAuxG`.

The near pairs and `baLWMoment_of_anp` are in `Graph/BAMomentGenB.lean`.
-/

set_option linter.style.longLine false
set_option linter.style.setOption false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.flexible false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedSimpArgs false

open private BASizeClaim_theta_decay from RBM3D.Graph.BASizeClaim
open private BAVocab_val_of_factor BAVocab_val_of_not from RBM3D.Graph.BAVocab
open private BASizeClaim_sizeConst_nonneg from RBM3D.Graph.BASizeClaim2

open MeasureTheory Filter Matrix

noncomputable section

namespace RBM.BA

open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes RBM.Graph

/-! ## 1. The carrier `f_{xy}` -/

/-- **The carrier `f_{xy}`** of (7.4) `fxyG_sum` over a carrier `C : FlowFM sz`, `σ = +`:
`Σ_{α ∉ {x, y}} Σ_β (W^{-d} S^{(B)}_{[α][β]}) Ǧ_{ββ} G_{xα} G_{αy}` with `S^{(B)} = C.S`, `Ǧ = C.GM`, `G = C.G`
(as `LWf` in `Graph/LWPins.lean`). -/
def LWfg {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (n : ℕ) (t : ℝ) (ω : sz.SeqΩ) (x y : Idx d (sz.L n) (sz.W n)) : ℂ :=
  ∑ α, if α = x ∨ α = y then (0 : ℂ) else
    ∑ β, ((((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * C.S n (STblk sz n α) (STblk sz n β)) * C.GM n t ω β β * C.G n t ω x α * C.G n t ω α y

/-- **The BA bridge** (as `lwMoment_fxy_bridge` in `Graph/LWMoment.lean`): at the block Anderson carrier `S^{(B)}(0) = I`, and
`t` times the carrier `f_{xy}` is the graph quantity `fxyVal` at the data `BAlwData` (`BAlwS = t · svarF(0)`) of the slice of the sample. -/
theorem LWfg_baFMz {d : ℕ} (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ) (t : ℝ) (ω : sz.SeqΩ) (x y : Idx d (sz.L n) (sz.W n)) :
    (t : ℂ) * LWfg (baFMz sz z) n t ω x y =
      fxyVal (BAlwData d (sz.L n) (sz.W n) (BAflowLam0 sz z n) (BAflowEs sz z n) t
        (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) (BAExp14a_slc sz n ω)).toLData x y := by
  unfold LWfg fxyVal
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  split_ifs
  · simp
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun β _ => ?_
  have hS : (BAlwData d (sz.L n) (sz.W n) (BAflowLam0 sz z n) (BAflowEs sz z n) t
        (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) (BAExp14a_slc sz n ω)).toLData.S α β =
      (t : ℂ) * ((((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * (baFMz sz z).S n (STblk sz n α) (STblk sz n β)) := by
    change BAlwS d (sz.L n) (sz.W n) t α β = _
    rw [BAExp14a_S_apply]
    simp only [baFMz, baFM, STblk, Matrix.one_apply]
  rw [hS]
  change (t : ℂ) * ((((((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * (baFMz sz z).S n (STblk sz n α) (STblk sz n β)) * (baFMz sz z).GM n t ω β β *
      (baFMz sz z).G n t ω x α * (baFMz sz z).G n t ω α y)) =
    (t : ℂ) * ((((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * (baFMz sz z).S n (STblk sz n α) (STblk sz n β)) *
      ((baFMz sz z).G n t ω β β - (baFMz sz z).M n β β) * (baFMz sz z).G n t ω x α * (baFMz sz z).G n t ω α y
  unfold FlowFM.GM
  ring

/-! ## 2. The generic statement `LWMomentG` -/

/-- **`lem:LW_moment`** (Lemma 7.1; `Graph/LWPins.lean`) over a carrier family, in the `PinFam` shape of `LWtermG`
(`Chain/LWGen.lean`): `STFlow` becomes `Flow`, `lemT` becomes `T0`, `LWAssm` becomes `LWAssmgL (mk sz z) (law sz)`, `Prec` becomes
`PrecL sz (law sz)`, `LWf` becomes the carrier `f_{xy}` `LWfg (mk sz z)`, `η_t` becomes `(mk sz z).eta`; the rest is as in `LWMoment`
(`∃ c` before `𝔠`). -/
def LWMomentG (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ)
    (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop)
    (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz) (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ (p : ℕ), 2 ∣ p → ∀ (ε₀ C₁ C₂ C₃ : ℝ) (Cc : ℝ → ℝ),
      ∃ c : ℝ, 0 < c ∧
        ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), Flow sz κ ε 𝔠 𝔡 z →
          ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ T0 sz z n) →
            ∀ (Ψ : ℕ → ℝ) (Φ : ℕ → ℝ → ℝ),
              LWAssmgL (mk sz z) (law sz) t ε₀ Ψ Φ C₁ C₂ C₃ Cc →
              PrecL sz (law sz) (U := fun n => Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n))
                (fun n q _ => ∫ ω, ‖LWfg (mk sz z) n (t n) ω q.1 q.2‖ ^ p ∂(law sz))
                (fun n q _ => (((mk sz z).eta n (t n))⁻¹ * Φ n 0 *
                  Φ n (c * ((zdistInf d (sz.L n) (STblk sz n q.1 - STblk sz n q.2) : ℕ) : ℝ))) ^ p)

/-- **The block Anderson reading** (law `seqP (sz.withLam 0)`, `BAFlow`, `baFMz`, `BAflowT0`), beside `BALWterm`. -/
abbrev BALWMoment : ℕ → Prop := baPin LWMomentG

/-! ## 3. `ba_localregularX` with its binder discharged -/

/-- The conclusion of `ba_localregularX` (`Graph/BAEngine.lean`) without its shape binder,
which is discharged by `baShapeLL_e2_tn`, `baShapeLL_macroA_tn`, `baShapeLL_macroB_tn` (`Graph/BAShapeO2B.lean`). -/
theorem ba_localregularX_holds : ∀ (p : ℕ) (c : ℝ), 0 < c → ∀ (K0 d : ℕ) (D : ℝ), ∃ outs errs : List (BAPGraph (Fin 2)),
    BALocRegConcl p c K0 d D outs errs ∧ ∀ Q ∈ outs ++ errs, p ≤ Q.g.waved.countP (fun e => !e.col) :=
  ba_localregularX (fun sh h => by
    rcases h with rfl | rfl | rfl
    exacts [baShapeLL_e2_tn, baShapeLL_macroA_tn, baShapeLL_macroB_tn])

/-! ## 4. `≺` tools at the block Anderson law and the model-free arithmetic -/

section Tools

variable {d : ℕ} (sz : Sizes d)

/-- `≺` at an arbitrary law from a w.h.p. event on which the pathwise bound holds (as `lwMoment_prec_of_whp`). -/
theorem BAMomentGen_prec_of_whp {μ : Measure sz.SeqΩ} {U : ℕ → Type*} {ξ ζ : ∀ n, U n → sz.SeqΩ → ℝ}
    (h : ∀ τ : ℝ, 0 < τ → ∃ Ξ : ℕ → Set sz.SeqΩ, HighProbAt μ sz.size Ξ ∧
      ∀ᶠ n in atTop, ∀ ω ∈ Ξ n, ∀ u, ξ n u ω ≤ ((sz.size n : ℕ) : ℝ) ^ τ * ζ n u ω) :
    PrecL sz μ ξ ζ := by
  intro τ hτ D hD
  obtain ⟨Ξ, hΞ, hev⟩ := h τ hτ
  filter_upwards [hΞ D hD, hev] with n h1 h2
  refine le_trans (measure_mono ?_) h1
  intro ω hω
  obtain ⟨u, hu⟩ := hω
  by_contra hΩ
  exact absurd (h2 ω (not_not.1 hΩ) u) (not_le.2 hu)

/-- `ξ ≺ ζ` gives the w.h.p. event `{∀ u, ξ ≤ N^τ ζ}` (as `Sizes.Prec.whp` in `Defs/StochDomAt.lean`). -/
theorem BAMomentGen_whp_of_prec {μ : Measure sz.SeqΩ} {U : ℕ → Type*} {ξ ζ : ∀ n, U n → sz.SeqΩ → ℝ}
    (h : PrecL sz μ ξ ζ) {τ : ℝ} (hτ : 0 < τ) :
    HighProbAt μ sz.size (fun n => {ω | ∀ u, ξ n u ω ≤ ((sz.size n : ℕ) : ℝ) ^ τ * ζ n u ω}) := by
  intro D hD
  filter_upwards [h τ hτ D hD] with n hn
  refine le_trans (le_of_eq ?_) hn
  congr 1
  ext ω
  simp [badSetAt]

end Tools

section Numerics

/-- `size(Γ) ≤ N^{n_M + n_V} B^{n_S}` for `0 < Ψ ≤ B`, `B ≥ 1` at the level of the counters (as `lwMoment_scalingSize_le`
in `Graph/LWMoment.lean`; the slot `n_V` of a BA graph holds `n_A`). -/
theorem BAMomentGen_scalingSize_le (cs : Counters) {Ψ B : ℝ} (hΨ0 : 0 < Ψ) (hΨB : Ψ ≤ B) (hB : 1 ≤ B) (W L d : ℕ) (hW : 1 ≤ W)
    (hL : 1 ≤ L) :
    cs.scalingSize Ψ W d L ≤ (((W * L) ^ d : ℕ) : ℝ) ^ (cs.nM + cs.nV) * B ^ cs.nS := by
  unfold Counters.scalingSize
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hN1 : ((W : ℝ) ^ d) ≤ (((W * L) ^ d : ℕ) : ℝ) := by
    push_cast; exact pow_le_pow_left₀ (by linarith) (by nlinarith) d
  have hN2 : ((L : ℝ) ^ d) ≤ (((W * L) ^ d : ℕ) : ℝ) := by
    push_cast; exact pow_le_pow_left₀ (by linarith) (by nlinarith) d
  have h1 : ((L : ℝ) ^ d) ^ cs.nM ≤ (((W * L) ^ d : ℕ) : ℝ) ^ cs.nM := pow_le_pow_left₀ (by positivity) hN2 _
  have h2 : Ψ ^ cs.nS ≤ B ^ cs.nS := pow_le_pow_left₀ hΨ0.le hΨB _
  have h3 : (W : ℝ) ^ (-(d : ℤ) * ((cs.nW : ℤ) - (cs.nV : ℤ))) ≤ (((W * L) ^ d : ℕ) : ℝ) ^ cs.nV := by
    have hex : -(d : ℤ) * ((cs.nW : ℤ) - (cs.nV : ℤ)) ≤ ((d * cs.nV : ℕ) : ℤ) := by
      have h0 : (0 : ℤ) ≤ (d : ℤ) * (cs.nW : ℤ) := by positivity
      push_cast; nlinarith
    calc (W : ℝ) ^ (-(d : ℤ) * ((cs.nW : ℤ) - (cs.nV : ℤ))) ≤ (W : ℝ) ^ ((d * cs.nV : ℕ) : ℤ) :=
          zpow_le_zpow_right₀ hW1 hex
      _ = ((W : ℝ) ^ d) ^ cs.nV := by rw [zpow_natCast, pow_mul]
      _ ≤ _ := pow_le_pow_left₀ (by positivity) hN1 _
  have hN0 : (0 : ℝ) ≤ (((W * L) ^ d : ℕ) : ℝ) := Nat.cast_nonneg _
  calc ((L : ℝ) ^ d) ^ cs.nM * Ψ ^ cs.nS * (W : ℝ) ^ (-(d : ℤ) * ((cs.nW : ℤ) - (cs.nV : ℤ)))
      ≤ ((((W * L) ^ d : ℕ) : ℝ) ^ cs.nM * B ^ cs.nS) * (((W * L) ^ d : ℕ) : ℝ) ^ cs.nV := by
        refine mul_le_mul (mul_le_mul h1 h2 (by positivity) (by positivity)) h3 (by positivity) (by positivity)
    _ = _ := by ring

/-- The tail `e^{-c r/2} K₂ size_{Ψ'}(Γ) ≤ N^{-b}` for `Ψ' ≤ 1`, `K₂ ≤ N`, when `e^{-c r/2} N^{n_M + n_V + 1} ≤ N^{-b}`
(as `lwMoment_tail_le` in `Graph/LWMoment.lean`, at the counters). -/
theorem BAMomentGen_tail_le (cs : Counters) {Ψ' c r K2 b : ℝ} (W L d : ℕ) (hW : 1 ≤ W) (hL : 1 ≤ L) (hΨ0 : 0 < Ψ')
    (hΨ1 : Ψ' ≤ 1) (hK2 : K2 ≤ (((W * L) ^ d : ℕ) : ℝ)) (hK20 : 0 ≤ K2)
    (htail : Real.exp (-(c * r / 2)) * (((W * L) ^ d : ℕ) : ℝ) ^ ((cs.nM + cs.nV + 1 : ℕ) : ℝ) ≤
      (((W * L) ^ d : ℕ) : ℝ) ^ (-b)) :
    Real.exp (-(c * r / 2)) * K2 * cs.scalingSize Ψ' W d L ≤ (((W * L) ^ d : ℕ) : ℝ) ^ (-b) := by
  have hss := BAMomentGen_scalingSize_le cs hΨ0 hΨ1 le_rfl W L d hW hL
  rw [one_pow, mul_one] at hss
  have hscal0 : 0 ≤ cs.scalingSize Ψ' W d L := by
    unfold Counters.scalingSize
    have hL' : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL
    have hW' : (0 : ℝ) < (W : ℝ) := by exact_mod_cast hW
    positivity
  have hex := Real.exp_pos (-(c * r / 2))
  have hN0 : (0 : ℝ) ≤ (((W * L) ^ d : ℕ) : ℝ) := Nat.cast_nonneg _
  refine le_trans ?_ htail
  calc Real.exp (-(c * r / 2)) * K2 * cs.scalingSize Ψ' W d L
      ≤ Real.exp (-(c * r / 2)) * (((W * L) ^ d : ℕ) : ℝ) * ((((W * L) ^ d : ℕ) : ℝ) ^ (cs.nM + cs.nV)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hK2 hex.le) hss hscal0 (by positivity)
    _ = _ := by rw [Real.rpow_natCast, pow_succ]; ring

variable {d : ℕ} {sz : Sizes d} {𝔡 𝔠 : ℝ}

/-- **The tail `e^{-c (log W)²/2}` beats every power of `N`** (`r = (log W)²` of (7.12) `eq:far_ab`; as
`lwMoment_tail`): `W ≥ N^𝔠` and `log W → ∞`. -/
theorem BAMomentGen_tail (hadm : sz.Admissible 𝔠 𝔡) {c : ℝ} (hc : 0 < c) (a b : ℝ) :
    ∀ᶠ n in atTop, Real.exp (-(c * Real.log ((sz.W n : ℕ) : ℝ) ^ 2 / 2)) * ((sz.size n : ℕ) : ℝ) ^ a ≤
      ((sz.size n : ℕ) : ℝ) ^ (-b) := by
  obtain ⟨h𝔠, -, hsz, hband, -⟩ := hadm
  set A : ℝ := |a| + |b| with hA
  set M : ℝ := 2 * A / (𝔠 * c) with hM
  have hA0 : 0 ≤ A := by positivity
  filter_upwards [hband, ((tendsto_rpow_atTop h𝔠).comp hsz).eventually_ge_atTop (Real.exp M),
    hsz.eventually_ge_atTop 1] with n hb hbig hN1
  set N : ℝ := ((sz.size n : ℕ) : ℝ) with hN
  have hN0 : 0 < N := by linarith
  have hW0 : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hbig' : Real.exp M ≤ ((sz.W n : ℕ) : ℝ) := le_trans hbig hb
  have hLg : M ≤ Real.log ((sz.W n : ℕ) : ℝ) := (Real.le_log_iff_exp_le hW0).2 hbig'
  set Lg : ℝ := Real.log ((sz.W n : ℕ) : ℝ) with hLgdef
  have hM0 : 0 ≤ M := by positivity
  have h1 : N ^ (a + b) ≤ N ^ A :=
    Real.rpow_le_rpow_of_exponent_le hN1 (by linarith [le_abs_self a, le_abs_self b])
  have h2 : N ^ A ≤ ((sz.W n : ℕ) : ℝ) ^ (A / 𝔠) := Sizes.size_rpow_le_W_rpow sz h𝔠 n hb hA0
  have h3 : ((sz.W n : ℕ) : ℝ) ^ (A / 𝔠) = Real.exp (Lg * (A / 𝔠)) := by
    rw [Real.rpow_def_of_pos hW0]
  have h4 : Lg * (A / 𝔠) ≤ c * Lg ^ 2 / 2 := by
    have : A / 𝔠 = c * M / 2 := by rw [hM]; field_simp
    rw [this]
    have hL0 : 0 ≤ Lg := le_trans hM0 hLg
    nlinarith [mul_le_mul_of_nonneg_left hLg (by positivity : 0 ≤ c * Lg / 2)]
  have h5 : N ^ (a + b) ≤ Real.exp (c * Lg ^ 2 / 2) :=
    h1.trans (h2.trans (h3 ▸ Real.exp_le_exp.2 h4))
  have hNb : 0 < N ^ b := Real.rpow_pos_of_pos hN0 b
  refine le_of_mul_le_mul_right ?_ hNb
  rw [← Real.rpow_add hN0 (-b) b, neg_add_cancel, Real.rpow_zero, mul_assoc, ← Real.rpow_add hN0]
  calc Real.exp (-(c * Lg ^ 2 / 2)) * N ^ (a + b) ≤ Real.exp (-(c * Lg ^ 2 / 2)) * Real.exp (c * Lg ^ 2 / 2) :=
        mul_le_mul_of_nonneg_left h5 (Real.exp_pos _).le
    _ = 1 := by rw [← Real.exp_add]; simp

/-- `K' W^{-D} ≤ N^{-K_f}` for `K' ≤ N`, `D ≥ (K_f + 1)/𝔠` (`W ≥ N^𝔠`; as `lwMoment_Wneg_le`). -/
theorem BAMomentGen_Wneg_le (hadm : sz.Admissible 𝔠 𝔡) {Kf D : ℝ} (hKf : 0 ≤ Kf) (hD : (Kf + 1) / 𝔠 ≤ D) :
    ∀ᶠ n in atTop, ∀ K' : ℝ, K' ≤ ((sz.size n : ℕ) : ℝ) →
      K' * ((sz.W n : ℕ) : ℝ) ^ (-D) ≤ ((sz.size n : ℕ) : ℝ) ^ (-Kf) := by
  obtain ⟨h𝔠, -, hsz, hband, -⟩ := hadm
  filter_upwards [hband, hsz.eventually_ge_atTop 1] with n hb hN1
  intro K' hK'
  have hN0 : 0 < ((sz.size n : ℕ) : ℝ) := by linarith
  have hW0 : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hD0 : 0 ≤ D := le_trans (by positivity) hD
  have h1 : ((sz.W n : ℕ) : ℝ) ^ (-D) ≤ (((sz.size n : ℕ) : ℝ) ^ 𝔠) ^ (-D) :=
    Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hN0 _) hb (by linarith)
  have h2 : (((sz.size n : ℕ) : ℝ) ^ 𝔠) ^ (-D) = ((sz.size n : ℕ) : ℝ) ^ (-(𝔠 * D)) := by
    rw [← Real.rpow_mul hN0.le]; congr 1; ring
  have h3 : ((sz.size n : ℕ) : ℝ) ^ (-(𝔠 * D)) ≤ ((sz.size n : ℕ) : ℝ) ^ (-(Kf + 1)) := by
    refine Real.rpow_le_rpow_of_exponent_le hN1 ?_
    have : Kf + 1 ≤ 𝔠 * D := by rwa [div_le_iff₀ h𝔠, mul_comm] at hD
    linarith
  calc K' * ((sz.W n : ℕ) : ℝ) ^ (-D) ≤ ((sz.size n : ℕ) : ℝ) * ((sz.W n : ℕ) : ℝ) ^ (-D) :=
        mul_le_mul_of_nonneg_right hK' (Real.rpow_nonneg hW0.le _)
    _ ≤ ((sz.size n : ℕ) : ℝ) * ((sz.size n : ℕ) : ℝ) ^ (-(Kf + 1)) :=
        mul_le_mul_of_nonneg_left (h1.trans (h2.le.trans h3)) hN0.le
    _ = ((sz.size n : ℕ) : ℝ) ^ (-Kf) := by
        calc ((sz.size n : ℕ) : ℝ) * ((sz.size n : ℕ) : ℝ) ^ (-(Kf + 1))
            = ((sz.size n : ℕ) : ℝ) ^ (1 : ℝ) * ((sz.size n : ℕ) : ℝ) ^ (-(Kf + 1)) := by rw [Real.rpow_one]
          _ = ((sz.size n : ℕ) : ℝ) ^ (1 + -(Kf + 1)) := (Real.rpow_add hN0 _ _).symm
          _ = _ := by congr 1; ring

/-- `L^d ≤ W^{K0}` for `K0 ≥ 1/𝔠` (`L^d ≤ N ≤ W^{1/𝔠}`; as `lwMoment_L_le_W`). -/
theorem BAMomentGen_L_le_W (hadm : sz.Admissible 𝔠 𝔡) {K0 : ℕ} (hK0 : 1 / 𝔠 ≤ K0) :
    ∀ᶠ n in atTop, ((sz.L n : ℕ) : ℝ) ^ d ≤ ((sz.W n : ℕ) : ℝ) ^ K0 := by
  obtain ⟨h𝔠, -, hsz, hband, -⟩ := hadm
  filter_upwards [hband, hsz.eventually_ge_atTop 1] with n hb hN1
  have h1 : (sz.L n) ^ d ≤ sz.size n := by
    unfold Sizes.size
    exact Nat.pow_le_pow_left (Nat.le_mul_of_pos_left _ (sz.W_pos n)) d
  have h1' : ((sz.L n : ℕ) : ℝ) ^ d ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast h1
  have h2 := Sizes.size_rpow_le_W_rpow sz h𝔠 n hb (τ := 1) zero_le_one
  rw [Real.rpow_one] at h2
  have hW1 : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  calc ((sz.L n : ℕ) : ℝ) ^ d ≤ ((sz.size n : ℕ) : ℝ) := h1'
    _ ≤ ((sz.W n : ℕ) : ℝ) ^ (1 / 𝔠) := by simpa using h2
    _ ≤ ((sz.W n : ℕ) : ℝ) ^ (K0 : ℝ) := Real.rpow_le_rpow_of_exponent_le hW1 hK0
    _ = _ := Real.rpow_natCast _ _

end Numerics

/-! ## 5. The rescaled data of the slice, the constants of its kernels, `claim:size` -/

section Data

/-- **The rescaled data `D₁` of the slice** (as `lwMoment_D` in `Graph/LWMoment.lean`): `BAExp14d_dataT` (`S' = svarF(0)`,
`S⁺' = lift(ω_t)`; `S = t S'`, `S⁺ = t S⁺'`, `BAExp14d_val_scale`) at the flow parameters of `n` and the slice of the sample. -/
def BAMomentGen_D {d : ℕ} (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ) (t : ℝ) (ω : sz.SeqΩ) : BALData (Idx d (sz.L n) (sz.W n)) :=
  BAExp14d_dataT d (sz.L n) (sz.W n) (BAflowLam0 sz z n) (BAflowEs sz z n) t (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n)
    (BAExp14a_slc sz n ω)

/-- `S' = svarF(0)` is `W^{-d}` on a block and `0` elsewhere (as the private `BAExp14d_svar0` in `Graph/BAExp14d.lean`). -/
private theorem BAMomentGen_svar0 {d L W : ℕ} [NeZero L] [NeZero W] (x y : Idx d L W) :
    ((svarF d L W 0 x y : ℝ) : ℂ) = ((W : ℂ) ^ d)⁻¹ * if (split d L W x).1 = (split d L W y).1 then 1 else 0 := by
  have h := BAExp14a_S_apply (d := d) (L := L) (W := W) 1 x y
  simpa [BAlwS] using h

/-- Relaxing the constants of an exponential bound (as the private `BAExp14d_relax`). -/
private theorem BAMomentGen_relax {v w u C' c' C c : ℝ} (hw : 0 ≤ w) (hu : 0 ≤ u) (hC : C' ≤ C) (hc : c ≤ c') (hC0 : 0 ≤ C')
    (h : v ≤ C' * w * Real.exp (-(c' * u))) : v ≤ C * w * Real.exp (-(c * u)) :=
  h.trans (mul_le_mul (mul_le_mul_of_nonneg_right hC hw) (Real.exp_le_exp.2 (by nlinarith)) (Real.exp_pos _).le
    (mul_nonneg (hC0.trans hC) hw))

/-- **The constants of the rescaled kernels** (the first half of the proof of `baGtoAGT_holds` in `Graph/BAExp14d.lean`):
for `d ≥ 3`, `Λ`, `κ > 0` there are constants, depending on `(d, Λ, κ)` only, such that for every `0 < g₀ ≤ Λ`, `0 ≤ t < 1`,
`BAReal d L g₀ κ E m`, the data with `S = svarF(0)`, `S⁺ = lift(ω_t)`, `M = BAlwM`, `gPsi = g₀ Ψ` have the entry decay with `(C, c)`
(`C ≥ 1`), the off-block support of `M`, `g₀ Ψ`, and the kernel bounds of the claim `Γ ≺ size(Γ)` with `(K₀, K₁, Kd) = (C, C e^{c}-sum, Kd)`. -/
theorem BAMomentGen_consts (d : ℕ) (hd : 3 ≤ d) (Λ κ : ℝ) (hΛ : 0 < Λ) (hκ : 0 < κ) :
    ∃ C c Kd : ℝ, 1 ≤ C ∧ 0 < c ∧ 0 ≤ Kd ∧
      ∀ (L W : ℕ) [NeZero L] [NeZero W], 3 ≤ L → ∀ (g0 E t : ℝ) (m : ℂ), 0 < g0 → g0 ≤ Λ → BAReal d L g0 κ E m → 0 ≤ t → t < 1 →
        ∀ D : BALData (Idx d L W), D.S = Matrix.of (fun x y => ((svarF d L W 0 x y : ℝ) : ℂ)) →
          D.Sp = lwLift d L W (BATheta d L g0 E m t true true) → D.M = BAlwM d L W g0 E m →
          D.gPsi = (g0 : ℂ) • PsiI d L W →
          (∀ x y, ‖D.S x y‖ ≤ C * ((W : ℝ) ^ d)⁻¹ * Real.exp (-(c * (lwBdist d L W x y : ℝ)))) ∧
          (∀ x y, ‖D.Sp x y‖ ≤ C * ((W : ℝ) ^ d)⁻¹ * Real.exp (-(c * (lwBdist d L W x y : ℝ)))) ∧
          (∀ x y, ‖D.M x y‖ ≤ C * Real.exp (-(c * (lwBdist d L W x y : ℝ))) ∧
            ‖D.gPsi x y‖ ≤ C * Real.exp (-(c * (lwBdist d L W x y : ℝ)))) ∧
          (∀ x y, (split d L W x).2 ≠ (split d L W y).2 → D.M x y = 0 ∧ D.gPsi x y = 0) ∧
          LWKBound D.S (C * ((W : ℝ) ^ d)⁻¹) (C * expC (d - 2) c) ∧ LWKBound D.Sp (C * ((W : ℝ) ^ d)⁻¹) (C * expC (d - 2) c) ∧
          LWKBound D.M Kd Kd ∧ LWKBound D.gPsi Kd Kd := by
  have hd0 : 0 < d := by omega
  obtain ⟨_K₀, _K₁, Kd, -, -, hKd, hK⟩ := baKBound_E d hd Λ κ hΛ hκ
  obtain ⟨C₁, c₁, hC₁, hc₁, hdec⟩ := BAAtom_decay_E d hd Λ κ hΛ hκ
  have hC5 := BAp5s_C_pos d Λ κ hd0 hΛ hκ
  have hμ := BAp5s_rate_pos d Λ κ hd0 hΛ hκ
  set Cθ : ℝ := (1 + Λ ^ 2) * BAp5s_C d Λ κ with hCθ
  have hCθ0 : 0 < Cθ := by positivity
  set C : ℝ := max (max C₁ 1) Cθ with hCdef
  set c : ℝ := min (min c₁ (BAp5s_rate d Λ κ)) 1 with hcdef
  have hC1 : 1 ≤ C := (le_max_right C₁ 1).trans ((le_max_left _ _))
  have hC0 : 0 ≤ C := by linarith
  have hc0 : 0 < c := lt_min (lt_min hc₁ hμ) one_pos
  have hCC₁ : C₁ ≤ C := (le_max_left C₁ 1).trans (le_max_left _ _)
  have hCCθ : Cθ ≤ C := le_max_right _ _
  have hcc₁ : c ≤ c₁ := (min_le_left _ _).trans (min_le_left _ _)
  have hccθ : c ≤ BAp5s_rate d Λ κ := (min_le_left _ _).trans (min_le_right _ _)
  refine ⟨C, c, Kd, hC1, hc0, hKd, ?_⟩
  intro L W _ _ hL g0 E t m hg hgΛ hr ht0 ht1 D hDS hDSp hDM hDP
  obtain ⟨-, -, hMP, hoff⟩ := hdec L W hL g0 E t m hg hgΛ hr ht0 ht1
  obtain ⟨-, -, hM', hP'⟩ := hK L W hL g0 E t m hg hgΛ hr ht0 ht1
  have hWd : 0 ≤ ((W : ℝ) ^ d)⁻¹ := by positivity
  have hbd : ∀ x y : Idx d L W, 0 ≤ (lwBdist d L W x y : ℝ) := fun x y => Nat.cast_nonneg _
  have hSd : ∀ x y, ‖D.S x y‖ ≤ C * ((W : ℝ) ^ d)⁻¹ * Real.exp (-(c * (lwBdist d L W x y : ℝ))) := by
    intro x y
    rw [hDS, Matrix.of_apply, BAMomentGen_svar0]
    by_cases h : (split d L W x).1 = (split d L W y).1
    · have h0 : (lwBdist d L W x y : ℝ) = 0 := by simp [lwBdist, h]
      rw [h0]
      simp only [h, ite_true, mul_one, mul_zero, neg_zero, Real.exp_zero, norm_inv, norm_pow, Complex.norm_natCast]
      nlinarith
    · simp only [h, ite_false, mul_zero, norm_zero]
      positivity
  have hSpd : ∀ x y, ‖D.Sp x y‖ ≤ C * ((W : ℝ) ^ d)⁻¹ * Real.exp (-(c * (lwBdist d L W x y : ℝ))) := by
    intro x y
    rw [hDSp]
    have hθ := BASizeClaim_theta_decay hL hd Λ g0 κ E t m hΛ hg hgΛ hκ hr ht0 ht1 (split d L W x).1 (split d L W y).1
    have e : ‖lwLift d L W (BATheta d L g0 E m t true true) x y‖ =
        ((W : ℝ) ^ d)⁻¹ * ‖BATheta d L g0 E m t true true (split d L W x).1 (split d L W y).1‖ := by
      simp [lwLift, norm_mul, norm_inv, norm_pow, Complex.norm_natCast]
    rw [e]
    refine BAMomentGen_relax (C' := Cθ) (c' := BAp5s_rate d Λ κ) hWd (hbd x y) hCCθ hccθ hCθ0.le ?_
    calc ((W : ℝ) ^ d)⁻¹ * ‖BATheta d L g0 E m t true true (split d L W x).1 (split d L W y).1‖
        ≤ ((W : ℝ) ^ d)⁻¹ * (Cθ * Real.exp (-(BAp5s_rate d Λ κ * (zdistD d L ((split d L W x).1 - (split d L W y).1) : ℝ)))) :=
          mul_le_mul_of_nonneg_left hθ hWd
      _ = Cθ * ((W : ℝ) ^ d)⁻¹ * Real.exp (-(BAp5s_rate d Λ κ * (lwBdist d L W x y : ℝ))) := by
          unfold lwBdist; ring
  have hMPd : ∀ x y, ‖D.M x y‖ ≤ C * Real.exp (-(c * (lwBdist d L W x y : ℝ))) ∧
      ‖D.gPsi x y‖ ≤ C * Real.exp (-(c * (lwBdist d L W x y : ℝ))) := by
    intro x y
    rw [hDM, hDP]
    obtain ⟨h1, h2⟩ := hMP x y
    refine ⟨?_, ?_⟩
    · have := BAMomentGen_relax (w := 1) (v := ‖BAlwM d L W g0 E m x y‖) (C' := C₁) (c' := c₁) (C := C) (c := c) zero_le_one
        (hbd x y) hCC₁ hcc₁ hC₁ (by simpa using h1)
      simpa using this
    · have := BAMomentGen_relax (w := 1) (v := ‖((g0 : ℂ) • PsiI d L W) x y‖) (C' := C₁) (c' := c₁) (C := C) (c := c) zero_le_one
        (hbd x y) hCC₁ hcc₁ hC₁ (by simpa using h2)
      simpa using this
  have hoff' : ∀ x y, (split d L W x).2 ≠ (split d L W y).2 → D.M x y = 0 ∧ D.gPsi x y = 0 := by
    intro x y hxy
    rw [hDM, hDP]
    exact hoff x y hxy
  exact ⟨hSd, hSpd, hMPd, hoff', lwKBound_of_decay hd hC0 hc0 hSd, lwKBound_of_decay hd hC0 hc0 hSpd, by rw [hDM]; exact hM',
    by rw [hDP]; exact hP'⟩

/-- The claim `Γ ≺ size(Γ)` for a packed graph at data with the kernel bounds of `BAMomentGen_consts` (the BA form of the pathwise estimate of
`lwMoment_pval_claim` in `Graph/LWMoment.lean`): `|Q.val D ℓe| ≤ C_Q size_Ψ(Q)` for `‖G - M‖_max ≤ Ψ`. -/
theorem BAMomentGen_pval_claim {d L W : ℕ} [NeZero L] [NeZero W] {K₀ K₁ Kd Ψ : ℝ} (Q : BAPGraph (Fin 2)) (hQ : Q.g.Normal)
    (D : BALData (Idx d L W)) (hG : ∀ x y, ‖D.G x y - D.M x y‖ ≤ Ψ) (hS : LWKBound D.S (K₀ * ((W : ℝ) ^ d)⁻¹) K₁)
    (hSp : LWKBound D.Sp (K₀ * ((W : ℝ) ^ d)⁻¹) K₁) (hM : LWKBound D.M Kd Kd) (hP : LWKBound D.gPsi Kd Kd)
    (hK₀ : 0 ≤ K₀) (hK₁ : 0 ≤ K₁) (hKd : 0 ≤ Kd) (ℓe : Fin 2 → Idx d L W) :
    ‖Q.val D ℓe‖ ≤ Q.g.sizeConst K₀ K₁ Kd * Q.g.scalingSize Ψ W d L := by
  classical
  by_cases hf : ∃ ℓ' : Q.E' → Idx d L W, ℓe = ℓ' ∘ Q.ext
  · obtain ⟨ℓ', hℓ'⟩ := hf
    rw [BAVocab_val_of_factor Q D hℓ']
    exact baClaimSize Q.g hQ D hG hS hSp hM hP ℓ'
  · rw [BAVocab_val_of_not Q D hf, norm_zero]
    refine mul_nonneg (BASizeClaim_sizeConst_nonneg Q.g hK₀ hK₁ hKd) ?_
    unfold BAGraph.scalingSize Counters.scalingSize
    have hW : (0 : ℝ) < (W : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne W)
    have hL : (0 : ℝ) < (L : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    have hΨ : 0 ≤ Ψ := (norm_nonneg _).trans (hG (fun _ => 0) (fun _ => 0))
    positivity

end Data

/-! ## 6. The standing hypotheses, the entry scale and the events

The standing hypotheses of `LWMomentG` at BA (the BA data) are the eight arguments `hd hκ hε h𝔡 hflow ht0 ht1 hassm` of every
lemma of this section (the BA counterpart of the band bundle `LWMomentCtx` in `Graph/LWMoment.lean`; no new structure).  `hassm` is
`LWAssmgL (baFMz sz z) (seqP (sz.withLam 0)) t ε₀ Ψ Φ C₁ C₂ C₃ Cc` with `LWLoop2gL` unfolded; the callers pass the hypothesis of the statement
(definitionally equal). -/

section Stoch

variable {d : ℕ} {sz : Sizes d} {z : ℕ → ℂ} {κ ε 𝔡 𝔠 : ℝ} {t : ℕ → ℝ} {ε₀ C₁ C₂ C₃ : ℝ} {Cc : ℝ → ℝ} {Ψ : ℕ → ℝ}
  {Φ : ℕ → ℝ → ℝ}
  (hd : 3 ≤ d) (hκ : 0 < κ) (hε : 0 < ε) (h𝔡 : 0 < 𝔡) (hflow : BAFlow sz κ ε 𝔠 𝔡 z) (ht0 : ∀ n, 0 ≤ t n)
  (ht1 : ∀ n, t n ≤ BAflowT0 sz z n)
  (hassm : 0 < ε₀ ∧ LWWindow sz ε₀ Ψ ∧ STInitialGT2gL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) t ε₀ Ψ ∧
    LWClass sz ε₀ C₃ Φ ∧ LWPsiRel C₁ C₂ Cc Φ ∧
    PrecL sz (Sizes.seqP (sz.withLam 0)) (U := fun n => Bool × Zd d (sz.L n) × Zd d (sz.L n))
      (fun n p ω => ‖(baFMz sz z).L n (t n) ![p.1, !p.1] ![p.2.1, p.2.2] ω‖)
      (fun n p _ => Φ n ((zdistInf d (sz.L n) (p.2.1 - p.2.2) : ℕ) : ℝ) ^ 2))
include hd hκ hε h𝔡 hflow ht0 ht1 hassm

omit hd hκ hε h𝔡 hflow ht0 ht1 hassm in
/-- The dominating function of the statement, `c = 1`: `R = (η_t⁻¹ Φ(0) Φ(1 · |a - b|))^p` (as `lwMoment_R` in `Graph/LWMoment.lean`). -/
def BAMomentGen_R (sz : Sizes d) (z : ℕ → ℂ) (t : ℕ → ℝ) (Φ : ℕ → ℝ → ℝ) (p n : ℕ) (x y : Idx d (sz.L n) (sz.W n)) : ℝ :=
  (((baFMz sz z).eta n (t n))⁻¹ * Φ n 0 * Φ n (1 * ((zdistInf d (sz.L n) (STblk sz n x - STblk sz n y) : ℕ) : ℝ))) ^ p

theorem BAMomentGen_psiAll : sz.LWPsiAll ε₀ C₁ C₂ C₃ Cc Φ := ⟨hassm.1, hassm.2.2.2.1, hassm.2.2.2.2.1⟩

/-- `0 < η_t ≤ 1` and `t < 1` at every `n`. -/
theorem BAMomentGen_eta_facts (n : ℕ) :
    0 < (baFMz sz z).eta n (t n) ∧ (baFMz sz z).eta n (t n) ≤ 1 ∧ t n < 1 :=
  ⟨BAExp14a_eta_pos hκ hflow n (ht0 n) (ht1 n), BAExp14c_eta_le_one hκ hflow n (ht0 n) (ht1 n),
    (ba_G_data hκ sz hflow n (ht0 n) (ht1 n)).1⟩

/-- The scale `Ψ' = max(1, C₃) N^{τ₁} Φ(0)` of the entry bounds on the good event satisfies the window `W^{-d/2} ≤ Ψ'` and
`Ψ' ≤ W^{-ε₀/2}` for `τ₁ ≤ 𝔠 ε₀/4` (as `lwMoment_Psi_facts` in `Graph/LWMoment.lean`). -/
theorem BAMomentGen_Psi_facts {τ₁ : ℝ} (hτ₁ : 0 ≤ τ₁) (hτ₁' : τ₁ ≤ 𝔠 * ε₀ / 4) :
    ∀ᶠ n in atTop, 0 < Φ n 0 ∧ ((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2) ≤
        max 1 C₃ * ((sz.size n : ℕ) : ℝ) ^ τ₁ * Φ n 0 ∧
      max 1 C₃ * ((sz.size n : ℕ) : ℝ) ^ τ₁ * Φ n 0 ≤ ((sz.W n : ℕ) : ℝ) ^ (-(ε₀ / 2)) := by
  obtain ⟨h𝔠, -, hsz, hband, -⟩ := hflow.1
  have hε₀ := hassm.1
  have hcls := hassm.2.2.2.1
  have hτpos : 0 < 𝔠 * ε₀ / 4 := by positivity
  filter_upwards [hcls.1, hcls.2.2, hband, hsz.eventually_ge_atTop 1,
    ((tendsto_rpow_atTop hτpos).comp hsz).eventually_ge_atTop (max 1 C₃)] with n hpos hwin hb hN1 hM
  have hW0 : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hΦ0 := (hpos 0 le_rfl).1
  have hΦε := (hpos 0 le_rfl).2
  have hM1 : 1 ≤ max 1 C₃ := le_max_left _ _
  have hNτ1 : 1 ≤ ((sz.size n : ℕ) : ℝ) ^ τ₁ := Real.one_le_rpow hN1 hτ₁
  refine ⟨hΦ0, ?_, ?_⟩
  · calc ((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2) ≤ C₃ * Φ n 0 := hwin
      _ ≤ max 1 C₃ * 1 * Φ n 0 := by
        rw [mul_one]; exact mul_le_mul_of_nonneg_right (le_max_right _ _) hΦ0.le
      _ ≤ _ := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hNτ1 (by positivity)) hΦ0.le
  · have e1 : ((sz.size n : ℕ) : ℝ) ^ τ₁ ≤ ((sz.W n : ℕ) : ℝ) ^ (ε₀ / 4) := by
      have := Real.rpow_le_rpow_of_exponent_le hN1 hτ₁'
      refine this.trans ?_
      have h2 := Sizes.size_rpow_le_W_rpow sz h𝔠 n hb (τ := 𝔠 * ε₀ / 4) hτpos.le
      have e : 𝔠 * ε₀ / 4 / 𝔠 = ε₀ / 4 := by field_simp
      rwa [e] at h2
    have e2 : max 1 C₃ ≤ ((sz.W n : ℕ) : ℝ) ^ (ε₀ / 4) := by
      refine hM.trans ?_
      have h2 := Sizes.size_rpow_le_W_rpow sz h𝔠 n hb (τ := 𝔠 * ε₀ / 4) hτpos.le
      have e : 𝔠 * ε₀ / 4 / 𝔠 = ε₀ / 4 := by field_simp
      rwa [e] at h2
    calc max 1 C₃ * ((sz.size n : ℕ) : ℝ) ^ τ₁ * Φ n 0
        ≤ ((sz.W n : ℕ) : ℝ) ^ (ε₀ / 4) * ((sz.W n : ℕ) : ℝ) ^ (ε₀ / 4) * ((sz.W n : ℕ) : ℝ) ^ (-ε₀) :=
          mul_le_mul (mul_le_mul e2 e1 (by positivity) (by positivity)) hΦε hΦ0.le (by positivity)
      _ = ((sz.W n : ℕ) : ℝ) ^ (-(ε₀ / 2)) := by
          rw [← Real.rpow_add hW0, ← Real.rpow_add hW0]; congr 1; ring

/-- The event `‖G_t - M‖_max ≤ N^{τ₁} Φ(0)` holds w.h.p. ((7.32) `eq:Gbyxi` entrywise, `baEntryPsi_holds`; as
`lwMoment_entry_whp`). -/
theorem BAMomentGen_entry_whp {τ₁ : ℝ} (hτ₁ : 0 < τ₁) :
    HighProbAt (Sizes.seqP (sz.withLam 0)) sz.size (fun n => {ω | ∀ u : Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n),
      ‖(baFMz sz z).GM n (t n) ω u.1 u.2‖ ≤ ((sz.size n : ℕ) : ℝ) ^ τ₁ * Φ n 0}) :=
  BAMomentGen_whp_of_prec sz (baEntryPsi_holds d hd κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow t ht0 ht1 ε₀ C₁ C₂ C₃ Cc Φ
    (BAMomentGen_psiAll hd hκ hε h𝔡 hflow ht0 ht1 hassm) hassm.2.2.2.2.2 ε₀ hassm.1 hassm.2.2.1.1) hτ₁

/-- **The polynomial floor of the dominating function** (as `lwMoment_floor` in `Graph/LWMoment.lean`):
`R ≥ N^{-p(2+C₂)}` for `R = (η⁻¹ Φ(0) Φ(|a-b|))^p`, from `W^{-d/2} ≤ C₃ Φ(0)`, `Φ(0) ≤ Cc(2) C₁ max(1,r)^{C₂} Φ(r)`, `η ≤ 1`. -/
theorem BAMomentGen_floor (p : ℕ) :
    ∀ᶠ n in atTop, ∀ x y : Idx d (sz.L n) (sz.W n),
      ((sz.size n : ℕ) : ℝ) ^ (-((p : ℝ) * (2 + C₂))) ≤ BAMomentGen_R sz z t Φ p n x y := by
  have hsz : sz.SizeTendsto := hflow.1.2.2.1
  have hcls := hassm.2.2.2.1
  have hC3 : 0 < C₃ := hcls.2.1
  filter_upwards [lwMoment_phi_facts hcls hassm.2.2.2.2.1, hcls.2.2, hsz.eventually_ge_atTop 1,
    hsz.eventually_ge_atTop (C₃ ^ 2 * Cc 2 * C₁)] with n hph hwin hN1 hNbig
  obtain ⟨hCc, hP, hcmp, -⟩ := hph
  intro x y
  unfold BAMomentGen_R
  set N : ℝ := ((sz.size n : ℕ) : ℝ) with hN
  have hN0 : 0 < N := by linarith
  obtain ⟨hη0, hη1, -⟩ := BAMomentGen_eta_facts hd hκ hε h𝔡 hflow ht0 ht1 hassm n
  have hηinv : 1 ≤ ((baFMz sz z).eta n (t n))⁻¹ := one_le_inv_iff₀.2 ⟨hη0, hη1⟩
  set r : ℝ := 1 * ((zdistInf d (sz.L n) (STblk sz n x - STblk sz n y) : ℕ) : ℝ) with hr
  have hr0 : 0 ≤ r := by positivity
  have hLN : (sz.L n : ℝ) ≤ N := by
    have hd0 : 1 ≤ d := by omega
    have h1 : sz.L n ≤ sz.size n := by
      unfold Sizes.size
      calc sz.L n = (sz.L n) ^ 1 := (pow_one _).symm
        _ ≤ (sz.L n) ^ d := Nat.pow_le_pow_right (by have := sz.three_le_L n; omega) hd0
        _ ≤ (sz.W n * sz.L n) ^ d := Nat.pow_le_pow_left (Nat.le_mul_of_pos_left _ (sz.W_pos n)) d
    rw [hN]; exact_mod_cast h1
  have hr1 : max 1 r ≤ N := by
    refine max_le hN1 ?_
    rw [hr, one_mul]
    have h6 : ((zdistInf d (sz.L n) (STblk sz n x - STblk sz n y) : ℕ) : ℝ) ≤ (sz.L n : ℝ) := by
      exact_mod_cast lwMoment_zdistInf_le (sz.L n) _
    linarith
  have hmaxN : (max 1 r) ^ C₂ ≤ N ^ C₂ :=
    Real.rpow_le_rpow (by positivity) hr1 (by linarith [hassm.2.2.2.2.1.2.2.1])
  have hΦr := hP r hr0
  have hΦ0 := hP 0 le_rfl
  have h1 : Φ n 0 ≤ Cc 2 * C₁ * N ^ C₂ * Φ n r := by
    refine (hcmp r hr0).trans (mul_le_mul_of_nonneg_right ?_ hΦr.le)
    exact mul_le_mul_of_nonneg_left hmaxN (by have := hassm.2.2.2.2.1.2.1; positivity)
  have hW0 : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hWN : ((sz.W n : ℕ) : ℝ) ^ d ≤ N := by
    have h : (sz.W n) ^ d ≤ sz.size n := by
      unfold Sizes.size
      exact Nat.pow_le_pow_left (Nat.le_mul_of_pos_right _ (by have := sz.three_le_L n; omega)) d
    rw [hN]; exact_mod_cast h
  have hNh : N ^ (-(1 : ℝ) / 2) ≤ ((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2) := by
    have e : ((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2) = (((sz.W n : ℕ) : ℝ) ^ d) ^ (-(1 : ℝ) / 2) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hW0.le]; congr 1; ring
    rw [e]
    exact Real.rpow_le_rpow_of_nonpos (by positivity) hWN (by norm_num)
  have hΦ0lb : N ^ (-(1 : ℝ) / 2) ≤ C₃ * Φ n 0 := hNh.trans hwin
  have hNh2 : N ^ (-(1 : ℝ) / 2) * N ^ (-(1 : ℝ) / 2) = N ^ (-(1 : ℝ)) := by
    rw [← Real.rpow_add hN0]; congr 1; ring
  have hCK : 0 < Cc 2 * C₁ * N ^ C₂ := by have := hassm.2.2.2.2.1.2.1; positivity
  have h2 : Φ n 0 * Φ n 0 ≤ Cc 2 * C₁ * N ^ C₂ * (Φ n 0 * Φ n r) := by nlinarith
  have h3 : N ^ (-(1 : ℝ)) ≤ C₃ ^ 2 * (Φ n 0 * Φ n 0) := by
    have := mul_le_mul hΦ0lb hΦ0lb (by positivity) (by positivity)
    rw [hNh2] at this; nlinarith
  have h4 : N ^ (-(2 + C₂)) ≤ Φ n 0 * Φ n r := by
    have hC3N : C₃ ^ 2 * (Cc 2 * C₁ * N ^ C₂) ≤ N ^ (1 + C₂) := by
      rw [Real.rpow_add hN0, Real.rpow_one]
      have := mul_le_mul_of_nonneg_right hNbig (by positivity : (0 : ℝ) ≤ N ^ C₂)
      nlinarith
    have e1 : N ^ (-(2 + C₂)) * N ^ (1 + C₂) = N ^ (-(1 : ℝ)) := by
      rw [← Real.rpow_add hN0]; congr 1; ring
    have : N ^ (-(2 + C₂)) * (C₃ ^ 2 * (Cc 2 * C₁ * N ^ C₂)) ≤ C₃ ^ 2 * (Cc 2 * C₁ * N ^ C₂) * (Φ n 0 * Φ n r) := by
      calc N ^ (-(2 + C₂)) * (C₃ ^ 2 * (Cc 2 * C₁ * N ^ C₂)) ≤ N ^ (-(2 + C₂)) * N ^ (1 + C₂) :=
            mul_le_mul_of_nonneg_left hC3N (by positivity)
        _ = N ^ (-(1 : ℝ)) := e1
        _ ≤ C₃ ^ 2 * (Φ n 0 * Φ n 0) := h3
        _ ≤ C₃ ^ 2 * (Cc 2 * C₁ * N ^ C₂ * (Φ n 0 * Φ n r)) := mul_le_mul_of_nonneg_left h2 (by positivity)
        _ = _ := by ring
    have hpos : 0 < C₃ ^ 2 * (Cc 2 * C₁ * N ^ C₂) := by positivity
    nlinarith
  have h5 : N ^ (-(2 + C₂)) ≤ ((baFMz sz z).eta n (t n))⁻¹ * Φ n 0 * Φ n r := by
    calc N ^ (-(2 + C₂)) ≤ Φ n 0 * Φ n r := h4
      _ = 1 * (Φ n 0 * Φ n r) := (one_mul _).symm
      _ ≤ ((baFMz sz z).eta n (t n))⁻¹ * (Φ n 0 * Φ n r) :=
          mul_le_mul_of_nonneg_right hηinv (by positivity)
      _ = _ := by ring
  calc N ^ (-((p : ℝ) * (2 + C₂))) = (N ^ (-(2 + C₂))) ^ p := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; congr 1; ring
    _ ≤ _ := pow_le_pow_left₀ (Real.rpow_nonneg hN0.le _) h5 p

end Stoch

/-! ## 7. The kernels along the flow, the outputs with an error bound and with `𝓜_x = 𝓜_y` -/

section Outputs

variable {d : ℕ} {sz : Sizes d} {z : ℕ → ℂ} {κ ε 𝔡 𝔠 : ℝ} {t : ℕ → ℝ} {ε₀ C₁ C₂ C₃ : ℝ} {Cc : ℝ → ℝ} {Ψ : ℕ → ℝ}
  {Φ : ℕ → ℝ → ℝ}
  (hd : 3 ≤ d) (hκ : 0 < κ) (hε : 0 < ε) (h𝔡 : 0 < 𝔡) (hflow : BAFlow sz κ ε 𝔠 𝔡 z) (ht0 : ∀ n, 0 ≤ t n)
  (ht1 : ∀ n, t n ≤ BAflowT0 sz z n)
  (hassm : 0 < ε₀ ∧ LWWindow sz ε₀ Ψ ∧ STInitialGT2gL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) t ε₀ Ψ ∧
    LWClass sz ε₀ C₃ Φ ∧ LWPsiRel C₁ C₂ Cc Φ ∧
    PrecL sz (Sizes.seqP (sz.withLam 0)) (U := fun n => Bool × Zd d (sz.L n) × Zd d (sz.L n))
      (fun n p ω => ‖(baFMz sz z).L n (t n) ![p.1, !p.1] ![p.2.1, p.2.2] ω‖)
      (fun n p _ => Φ n ((zdistInf d (sz.L n) (p.2.1 - p.2.2) : ℕ) : ℝ) ^ 2))
include hd hκ hε h𝔡 hflow ht0 ht1 hassm

/-- **The decay and the kernel bounds of the rescaled data along the flow** (as `lwMoment_decay` in `Graph/LWMoment.lean`):
constants `(C, c, Kd)` depending on `(d, 𝔡, κ)` only, and for large `n` the facts of `BAMomentGen_consts` at the data of every
sample (the flow has `0 < g₀ ≤ 𝔡⁻¹` eventually, `BAflow_lam0_window`; `BAReal` and `t < 1` from `ba_G_data`). -/
theorem BAMomentGen_decay : ∃ C c Kd : ℝ, 1 ≤ C ∧ 0 < c ∧ 0 ≤ Kd ∧ ∀ᶠ n in atTop, ∀ ω : sz.SeqΩ,
    (∀ x y, ‖(BAMomentGen_D sz z n (t n) ω).S x y‖ ≤
      C * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * Real.exp (-(c * (lwBdist d (sz.L n) (sz.W n) x y : ℝ)))) ∧
    (∀ x y, ‖(BAMomentGen_D sz z n (t n) ω).Sp x y‖ ≤
      C * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * Real.exp (-(c * (lwBdist d (sz.L n) (sz.W n) x y : ℝ)))) ∧
    (∀ x y, ‖(BAMomentGen_D sz z n (t n) ω).M x y‖ ≤ C * Real.exp (-(c * (lwBdist d (sz.L n) (sz.W n) x y : ℝ))) ∧
      ‖(BAMomentGen_D sz z n (t n) ω).gPsi x y‖ ≤ C * Real.exp (-(c * (lwBdist d (sz.L n) (sz.W n) x y : ℝ)))) ∧
    (∀ x y, (split d (sz.L n) (sz.W n) x).2 ≠ (split d (sz.L n) (sz.W n) y).2 →
      (BAMomentGen_D sz z n (t n) ω).M x y = 0 ∧ (BAMomentGen_D sz z n (t n) ω).gPsi x y = 0) ∧
    LWKBound (BAMomentGen_D sz z n (t n) ω).S (C * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹) (C * expC (d - 2) c) ∧
    LWKBound (BAMomentGen_D sz z n (t n) ω).Sp (C * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹) (C * expC (d - 2) c) ∧
    LWKBound (BAMomentGen_D sz z n (t n) ω).M Kd Kd ∧ LWKBound (BAMomentGen_D sz z n (t n) ω).gPsi Kd Kd := by
  obtain ⟨C, c, Kd, hC, hc, hKd, h⟩ := BAMomentGen_consts d hd 𝔡⁻¹ κ (inv_pos.2 h𝔡) hκ
  refine ⟨C, c, Kd, hC, hc, hKd, ?_⟩
  filter_upwards [BAflow_lam0_window κ ε 𝔠 𝔡 sz z hflow] with n hn ω
  obtain ⟨ht1', hr, -⟩ := ba_G_data hκ sz hflow n (ht0 n) (ht1 n)
  exact h (sz.L n) (sz.W n) (sz.three_le_L n) (BAflowLam0 sz z n) (BAflowEs sz z n) (t n)
    (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) hn.1 hn.2 hr (ht0 n) ht1' (BAMomentGen_D sz z n (t n) ω) rfl rfl rfl rfl

/-- **errs** (and any output with a `W^{-D}` size bound): the size bound at the entry scale `Ψ'` gives `≤ N^{-K_f} ≤ R`
(as `lwMoment_prec_err` in `Graph/LWMoment.lean`). -/
theorem BAMomentGen_prec_err (p : ℕ) {K0 : ℕ} {D : ℝ} (hK0 : 1 / 𝔠 ≤ K0) (hD : ((p : ℝ) * (2 + C₂) + 1) / 𝔠 ≤ D)
    {V : ℕ → Type} (pr : ∀ n, V n → Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n)) {Q : BAPGraph (Fin 2)}
    (hQ : Q.g.Normal)
    (herr : ∀ (W L : ℕ) (Ψ : ℝ), 1 ≤ W → 1 ≤ L → (L : ℝ) ^ d ≤ (W : ℝ) ^ K0 →
      (W : ℝ) ^ (-(d : ℝ) / 2) ≤ Ψ → Ψ ≤ (W : ℝ) ^ (-(ε₀ / 2)) → Q.g.scalingSize Ψ W d L ≤ (W : ℝ) ^ (-D)) :
    PrecL sz (Sizes.seqP (sz.withLam 0)) (U := V)
      (fun n v ω => ‖Q.val (BAMomentGen_D sz z n (t n) ω) ![(pr n v).1, (pr n v).2]‖)
      (fun n v _ => BAMomentGen_R sz z t Φ p n (pr n v).1 (pr n v).2) := by
  have hε₀ := hassm.1
  have hsz : sz.SizeTendsto := hflow.1.2.2.1
  have h𝔠 : 0 < 𝔠 := hflow.1.1
  apply BAMomentGen_prec_of_whp
  intro τ hτ
  refine ⟨_, BAMomentGen_entry_whp hd hκ hε h𝔡 hflow ht0 ht1 hassm (τ₁ := 𝔠 * ε₀ / 4) (by positivity), ?_⟩
  obtain ⟨C, c, Kd, hC, hc, hKd, hdec⟩ := BAMomentGen_decay hd hκ hε h𝔡 hflow ht0 ht1 hassm
  have hC0 : 0 ≤ C := by linarith
  have hKf : 0 ≤ (p : ℝ) * (2 + C₂) := by
    have := hassm.2.2.2.2.1.2.2.1; positivity
  filter_upwards [hdec, BAMomentGen_Psi_facts hd hκ hε h𝔡 hflow ht0 ht1 hassm (τ₁ := 𝔠 * ε₀ / 4) (by positivity) le_rfl,
    BAMomentGen_floor hd hκ hε h𝔡 hflow ht0 ht1 hassm p, BAMomentGen_Wneg_le hflow.1 hKf hD,
    BAMomentGen_L_le_W hflow.1 hK0, hsz.eventually_ge_atTop 1,
    hsz.eventually_ge_atTop (Q.g.sizeConst C (C * expC (d - 2) c) Kd)]
    with n hdn hPsi hfl hWn hLW hN1 hNc
  intro ω hω v
  obtain ⟨hSd, hSpd, hMPd, hoff, hKS, hKSp, hKM, hKP⟩ := hdn ω
  obtain ⟨hΦ0, hwin, hup⟩ := hPsi
  have hM1 : 1 ≤ max 1 C₃ := le_max_left _ _
  have hNτ : 1 ≤ ((sz.size n : ℕ) : ℝ) ^ τ := Real.one_le_rpow hN1 hτ.le
  have hA : ∀ a b : Idx d (sz.L n) (sz.W n), ‖(BAMomentGen_D sz z n (t n) ω).G a b - (BAMomentGen_D sz z n (t n) ω).M a b‖ ≤
      max 1 C₃ * ((sz.size n : ℕ) : ℝ) ^ (𝔠 * ε₀ / 4) * Φ n 0 := by
    intro a b
    refine (hω (a, b)).trans ?_
    have h1 : 1 ≤ ((sz.size n : ℕ) : ℝ) ^ (𝔠 * ε₀ / 4) := Real.one_le_rpow hN1 (by positivity)
    have h2 : 0 ≤ ((sz.size n : ℕ) : ℝ) ^ (𝔠 * ε₀ / 4) * Φ n 0 := by positivity
    nlinarith
  have hK1 : 0 ≤ C * expC (d - 2) c := by have := lwMoment_expC_nonneg (d - 2) hc; positivity
  have h1 := BAMomentGen_pval_claim Q hQ (BAMomentGen_D sz z n (t n) ω) hA hKS hKSp hKM hKP hC0 hK1 hKd
    ![(pr n v).1, (pr n v).2]
  have h2 := herr (sz.W n) (sz.L n) _ (sz.W_pos n) (by have := sz.three_le_L n; omega) hLW hwin hup
  have hK0' : 0 ≤ Q.g.sizeConst C (C * expC (d - 2) c) Kd := BASizeClaim_sizeConst_nonneg Q.g hC0 hK1 hKd
  have h3 := h1.trans (mul_le_mul_of_nonneg_left h2 hK0')
  have h4 := hWn _ hNc
  have h5 := hfl (pr n v).1 (pr n v).2
  have hR0 : 0 ≤ BAMomentGen_R sz z t Φ p n (pr n v).1 (pr n v).2 :=
    (Real.rpow_nonneg (by positivity) _).trans h5
  calc _ ≤ _ := h3.trans h4
    _ ≤ BAMomentGen_R sz z t Φ p n (pr n v).1 (pr n v).2 := h5
    _ ≤ ((sz.size n : ℕ) : ℝ) ^ τ * BAMomentGen_R sz z t Φ p n (pr n v).1 (pr n v).2 :=
        le_mul_of_one_le_left hR0 hNτ

end Outputs

/-! ## 8. The scale-mole tail: two external vertices in one molecule ((7.12) `eq:far_ab`) -/

section Scalemole

variable {d L W : ℕ} [NeZero L] [NeZero W] {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

/-- A vertex is in its own molecule. -/
theorem BAMomentGen_mem_mol_self (Γ : BAGraph E I) (v : E ⊕ I) : v ∈ Γ.mol v :=
  (BAGraph.mem_mol_iff Γ v v).2 Relation.ReflTransGen.refl

/-- **The BA scale-mole tail** (as `lwScalemole_holds` in `Graph/AuxGraph.lean`): if the labels of two external
vertices of one molecule are at block distance `> |E ⊕ I| r`, no labelling is confined (`BAAtom_shadow_conf` and
`auxGraph_mol_dist` on the shadow, whose molecules are those of `Γ`), so the tail bound `BAAtom_term_tail` applies to every term and
`BAAtom_tail_sum` sums it.  This covers every `x ~ y` (an atom is inside a molecule, `BALocReg1_mol_of_atom`). -/
theorem BAMomentGen_scalemole (hd : 3 ≤ d) (Γ : BAGraph E I) (hN : Γ.Normal) (D : BALData (Idx d L W)) {Ψ C c r : ℝ}
    (hG : ∀ x y, ‖D.G x y - D.M x y‖ ≤ Ψ) (hC : 0 ≤ C) (hc : 0 < c)
    (hSd : ∀ x y, ‖D.S x y‖ ≤ C * ((W : ℝ) ^ d)⁻¹ * Real.exp (-(c * (lwBdist d L W x y : ℝ))))
    (hSpd : ∀ x y, ‖D.Sp x y‖ ≤ C * ((W : ℝ) ^ d)⁻¹ * Real.exp (-(c * (lwBdist d L W x y : ℝ))))
    (hMPd : ∀ x y, ‖D.M x y‖ ≤ C * Real.exp (-(c * (lwBdist d L W x y : ℝ))) ∧
      ‖D.gPsi x y‖ ≤ C * Real.exp (-(c * (lwBdist d L W x y : ℝ))))
    (hoff : ∀ x y, (split d L W x).2 ≠ (split d L W y).2 → D.M x y = 0 ∧ D.gPsi x y = 0) (hr : 0 ≤ r)
    (ℓe : E → Idx d L W) (a b : E) (hab : Sum.inl b ∈ Γ.mol (Sum.inl a))
    (hfar : (Fintype.card (E ⊕ I) : ℝ) * r < (lwBdist d L W (ℓe a) (ℓe b) : ℝ)) :
    ‖Γ.val D ℓe‖ ≤ Real.exp (-(c * r / 2)) * Γ.sizeConst C (C * expC (d - 2) (c / 2)) (C * (1 + expC (d - 2) (c / 2))) *
      Γ.scalingSize Ψ W d L := by
  classical
  have hne : Nonempty (Idx d L W) := ⟨fun _ => 0⟩
  have hΨ : 0 ≤ Ψ := (norm_nonneg _).trans (hG (fun _ => 0) (fun _ => 0))
  have htail := BAAtom_tail_sum (r := r) hd Γ hN D hΨ hC hc hSd hSpd hMPd hoff ℓe
  have hpt : ∀ ℓi : I → Idx d L W, ‖Γ.term D (Sum.elim ℓe ℓi)‖ ≤ ‖Γ.coeff‖ * Ψ ^ Γ.nS *
      (Real.exp (-(c * r / 2)) * ∏ j : Γ.Jx, BAAtom_fJw Γ D c j (Sum.elim ℓe ℓi (Γ.edgeEnds j).1)
        (Sum.elim ℓe ℓi (Γ.edgeEnds j).2)) := by
    intro ℓi
    refine BAAtom_term_tail Γ hN D hG hc _ ?_
    by_contra hcon
    have hconf : ∀ j : Γ.Jx, (lwBdist d L W (Sum.elim ℓe ℓi (Γ.edgeEnds j).1) (Sum.elim ℓe ℓi (Γ.edgeEnds j).2) : ℝ) ≤ r := by
      intro j
      by_contra h
      exact hcon ⟨j, not_le.1 h⟩
    have hsh := BAAtom_shadow_conf Γ (Sum.elim ℓe ℓi) r hconf
    have := auxGraph_mol_dist Γ.shadow hN.1 (Sum.elim ℓe ℓi) hr hsh (u := Sum.inl a) (v := Sum.inl b)
      ((BAAtom_shadow_molOf_eq_iff Γ _ _).2 hab)
    simp only [Sum.elim_inl] at this
    exact absurd hfar (not_lt.2 this)
  unfold BAGraph.val
  calc ‖∑ ℓi : I → Idx d L W, Γ.term D (Sum.elim ℓe ℓi)‖ ≤ ∑ ℓi : I → Idx d L W, ‖Γ.term D (Sum.elim ℓe ℓi)‖ :=
        norm_sum_le _ _
    _ ≤ _ := Finset.sum_le_sum fun ℓi _ => hpt ℓi
    _ ≤ _ := htail

end Scalemole

/-! ## 9. Outputs with `𝓜_x = 𝓜_y`, outputs with `𝓜_x ≠ 𝓜_y` -/

section Outputs2

variable {d : ℕ} {sz : Sizes d} {z : ℕ → ℂ} {κ ε 𝔡 𝔠 : ℝ} {t : ℕ → ℝ} {ε₀ C₁ C₂ C₃ : ℝ} {Cc : ℝ → ℝ} {Ψ : ℕ → ℝ}
  {Φ : ℕ → ℝ → ℝ}

/-- `log W → ∞` along the flow (`W ≥ N^𝔠`). -/
theorem BAMomentGen_logW_ge (hadm : sz.Admissible 𝔠 𝔡) (K' : ℝ) :
    ∀ᶠ n in atTop, K' ≤ Real.log ((sz.W n : ℕ) : ℝ) := by
  obtain ⟨h𝔠, -, hsz, hband, -⟩ := hadm
  filter_upwards [hband, ((tendsto_rpow_atTop h𝔠).comp hsz).eventually_ge_atTop (Real.exp K')] with n hb hbig
  have hW0 : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  exact (Real.le_log_iff_exp_le hW0).2 (le_trans hbig hb)

variable (hd : 3 ≤ d) (hκ : 0 < κ) (hε : 0 < ε) (h𝔡 : 0 < 𝔡) (hflow : BAFlow sz κ ε 𝔠 𝔡 z) (ht0 : ∀ n, 0 ≤ t n)
  (ht1 : ∀ n, t n ≤ BAflowT0 sz z n)
  (hassm : 0 < ε₀ ∧ LWWindow sz ε₀ Ψ ∧ STInitialGT2gL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) t ε₀ Ψ ∧
    LWClass sz ε₀ C₃ Φ ∧ LWPsiRel C₁ C₂ Cc Φ ∧
    PrecL sz (Sizes.seqP (sz.withLam 0)) (U := fun n => Bool × Zd d (sz.L n) × Zd d (sz.L n))
      (fun n p ω => ‖(baFMz sz z).L n (t n) ![p.1, !p.1] ![p.2.1, p.2.2] ω‖)
      (fun n p _ => Φ n ((zdistInf d (sz.L n) (p.2.1 - p.2.2) : ℕ) : ℝ) ^ 2))
include hd hκ hε h𝔡 hflow ht0 ht1 hassm

/-- **Outputs with `𝓜_x = 𝓜_y` at far pairs** ((7.12) `eq:far_ab`; as `lwMoment_prec_scale` in `Graph/LWMoment.lean`):
the value is at most the tail `e^{-c r/2} C' size(Γ)` with `r = (log W)²`, which is `≤ N^{-K_f} ≤ R`. -/
theorem BAMomentGen_prec_scale (p : ℕ) {V : ℕ → Type} (pr : ∀ n, V n → Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n))
    {Q : BAPGraph (Fin 2)} (hQ : Q.g.Normal) (hmol : Q.g.mol (Sum.inl (Q.ext 0)) = Q.g.mol (Sum.inl (Q.ext 1))) {K : ℕ}
    (hK : Fintype.card (Q.E' ⊕ Q.I') ≤ K)
    (hfar : ∀ n v, (K : ℝ) * Real.log ((sz.W n : ℕ) : ℝ) ^ 2 < (lwBdist d (sz.L n) (sz.W n) (pr n v).1 (pr n v).2 : ℝ)) :
    PrecL sz (Sizes.seqP (sz.withLam 0)) (U := V)
      (fun n v ω => ‖Q.val (BAMomentGen_D sz z n (t n) ω) ![(pr n v).1, (pr n v).2]‖)
      (fun n v _ => BAMomentGen_R sz z t Φ p n (pr n v).1 (pr n v).2) := by
  classical
  have hε₀ := hassm.1
  have hsz : sz.SizeTendsto := hflow.1.2.2.1
  have h𝔠 : 0 < 𝔠 := hflow.1.1
  apply BAMomentGen_prec_of_whp
  intro τ hτ
  refine ⟨_, BAMomentGen_entry_whp hd hκ hε h𝔡 hflow ht0 ht1 hassm (τ₁ := 𝔠 * ε₀ / 4) (by positivity), ?_⟩
  obtain ⟨C, c, Kd, hC, hc, hKd, hdec⟩ := BAMomentGen_decay hd hκ hε h𝔡 hflow ht0 ht1 hassm
  have hC0 : 0 ≤ C := by linarith
  have hKf : 0 ≤ (p : ℝ) * (2 + C₂) := by
    have := hassm.2.2.2.2.1.2.2.1; positivity
  filter_upwards [hdec, BAMomentGen_Psi_facts hd hκ hε h𝔡 hflow ht0 ht1 hassm (τ₁ := 𝔠 * ε₀ / 4) (by positivity) le_rfl,
    BAMomentGen_floor hd hκ hε h𝔡 hflow ht0 ht1 hassm p,
    BAMomentGen_tail hflow.1 hc ((Q.g.nM + Q.g.nA + 1 : ℕ) : ℝ) ((p : ℝ) * (2 + C₂)),
    hsz.eventually_ge_atTop 1,
    hsz.eventually_ge_atTop (Q.g.sizeConst C (C * expC (d - 2) (c / 2)) (C * (1 + expC (d - 2) (c / 2))))]
    with n hdn hPsi hfl htail hN1 hNc
  intro ω hω v
  obtain ⟨hSd, hSpd, hMPd, hoff, -, -, -, -⟩ := hdn ω
  obtain ⟨hΦ0, hwin, hup⟩ := hPsi
  have hM1 : 1 ≤ max 1 C₃ := le_max_left _ _
  have hNτ : 1 ≤ ((sz.size n : ℕ) : ℝ) ^ τ := Real.one_le_rpow hN1 hτ.le
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
  have hW1 : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hA : ∀ a b : Idx d (sz.L n) (sz.W n), ‖(BAMomentGen_D sz z n (t n) ω).G a b - (BAMomentGen_D sz z n (t n) ω).M a b‖ ≤
      max 1 C₃ * ((sz.size n : ℕ) : ℝ) ^ (𝔠 * ε₀ / 4) * Φ n 0 := by
    intro a b
    refine (hω (a, b)).trans ?_
    have h1 : 1 ≤ ((sz.size n : ℕ) : ℝ) ^ (𝔠 * ε₀ / 4) := Real.one_le_rpow hN1 (by positivity)
    have h2 : 0 ≤ ((sz.size n : ℕ) : ℝ) ^ (𝔠 * ε₀ / 4) * Φ n 0 := by positivity
    nlinarith
  have h5 := hfl (pr n v).1 (pr n v).2
  have hR0 : 0 ≤ BAMomentGen_R sz z t Φ p n (pr n v).1 (pr n v).2 :=
    (Real.rpow_nonneg (by positivity) _).trans h5
  have hfin : ∀ u : ℝ, u ≤ ((sz.size n : ℕ) : ℝ) ^ (-((p : ℝ) * (2 + C₂))) →
      u ≤ ((sz.size n : ℕ) : ℝ) ^ τ * BAMomentGen_R sz z t Φ p n (pr n v).1 (pr n v).2 :=
    fun u hu => hu.trans (h5.trans (le_mul_of_one_le_left hR0 hNτ))
  refine hfin _ ?_
  by_cases hf : ∃ ℓ' : Q.E' → Idx d (sz.L n) (sz.W n), ![(pr n v).1, (pr n v).2] = ℓ' ∘ Q.ext
  · obtain ⟨ℓ', hℓ'⟩ := hf
    rw [BAVocab_val_of_factor Q _ hℓ']
    have e0 : ℓ' (Q.ext 0) = (pr n v).1 := (congrFun hℓ' 0).symm
    have e1 : ℓ' (Q.ext 1) = (pr n v).2 := (congrFun hℓ' 1).symm
    have hr0 : 0 ≤ Real.log ((sz.W n : ℕ) : ℝ) ^ 2 := by positivity
    have hfar' : (Fintype.card (Q.E' ⊕ Q.I') : ℝ) * Real.log ((sz.W n : ℕ) : ℝ) ^ 2 <
        (lwBdist d (sz.L n) (sz.W n) (ℓ' (Q.ext 0)) (ℓ' (Q.ext 1)) : ℝ) := by
      rw [e0, e1]
      exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right (Nat.cast_le.2 hK) hr0) (hfar n v)
    have hab : Sum.inl (Q.ext 1) ∈ Q.g.mol (Sum.inl (Q.ext 0)) := by
      rw [hmol]; exact BAMomentGen_mem_mol_self _ _
    have hsc := BAMomentGen_scalemole hd Q.g hQ (BAMomentGen_D sz z n (t n) ω) hA hC0 hc hSd hSpd hMPd hoff hr0 ℓ'
      (Q.ext 0) (Q.ext 1) hab hfar'
    have hΨ0 : 0 < max 1 C₃ * ((sz.size n : ℕ) : ℝ) ^ (𝔠 * ε₀ / 4) * Φ n 0 := by
      have : 0 < max 1 C₃ := lt_of_lt_of_le one_pos hM1
      positivity
    have hΨ1 : max 1 C₃ * ((sz.size n : ℕ) : ℝ) ^ (𝔠 * ε₀ / 4) * Φ n 0 ≤ 1 :=
      hup.trans (Real.rpow_le_one_of_one_le_of_nonpos hW1 (by linarith))
    have hK2 : 0 ≤ Q.g.sizeConst C (C * expC (d - 2) (c / 2)) (C * (1 + expC (d - 2) (c / 2))) := by
      have h1 : 0 ≤ expC (d - 2) (c / 2) := lwMoment_expC_nonneg (d - 2) (half_pos hc)
      exact BASizeClaim_sizeConst_nonneg Q.g hC0 (by positivity) (by positivity)
    exact hsc.trans (BAMomentGen_tail_le Q.g.counters (sz.W n) (sz.L n) d (sz.W_pos n)
      (by have := sz.three_le_L n; omega) hΨ0 hΨ1 hNc hK2 htail)
  · rw [BAVocab_val_of_not Q _ hf, norm_zero]
    exact Real.rpow_nonneg hN0.le _

omit hd hκ hε h𝔡 hflow ht0 ht1 hassm in
/-- The scaling of the auxiliary value in the edge variables (as the band `lwMoment_auxVal_smul`, whose statement is for an
`LGraph`; here at the shadow, which is `BAGraph.auxVal`). -/
theorem BAMomentGen_auxVal_smul {κ' : Type} [Fintype κ'] {E I : Type} [Fintype E] [DecidableEq E] [Fintype I]
    [DecidableEq I] (Γ : BAGraph E I) (ξ : κ' → κ' → ℝ) (s : ℝ) (be : E → κ') :
    Γ.auxVal (fun a b => s * ξ a b) be = s ^ Γ.shadow.molSolid.length * Γ.auxVal ξ be :=
  lwMoment_auxVal_smul Γ.shadow ξ s be

omit hd hκ hε h𝔡 hflow ht0 ht1 hassm in
/-- The external labels of a packed graph with two external vertices in distinct molecules: `[ℓ' a]` is the block of `x` at `ext 0`
and of `y` at `ext 1` (every vertex of `E'` is `ext 0` or `ext 1`). -/
theorem BAMomentGen_be_eq {d L W : ℕ} [NeZero L] [NeZero W] (Q : BAPGraph (Fin 2))
    (hxy : Q.g.mol (Sum.inl (Q.ext 0)) ≠ Q.g.mol (Sum.inl (Q.ext 1))) (ℓ' : Q.E' → Idx d L W) (x y : Idx d L W)
    (hℓ' : ![x, y] = ℓ' ∘ Q.ext) :
    (fun a : Q.E' => (split d L W (ℓ' a)).1) =
      fun e => if e = Q.ext 0 then (split d L W x).1 else (split d L W y).1 := by
  funext a
  obtain ⟨i, rfl⟩ := Q.ext_surj a
  have e0 : ℓ' (Q.ext 0) = x := (congrFun hℓ' 0).symm
  have e1 : ℓ' (Q.ext 1) = y := (congrFun hℓ' 1).symm
  fin_cases i
  · simp [e0]
  · have hne : Q.ext 1 ≠ Q.ext 0 := fun h => hxy (by rw [h])
    simp [e1, hne]

/-- **Outputs with `𝓜_x ≠ 𝓜_y`** (Lemmas 7.21 and 7.22; as `lwMoment_prec_anp` in `Graph/LWMoment.lean`): `GtoAG` at the rescaled
kernels (`baGtoAGT_holds`, no `hext`) against the edge variables `N^{τ₁} ζ`, `ζ = baZetaVar` at the radius `ρ = (2K+1)(log W)²` (`baGbyZeta_holds` needs `ρ - 2R ≥ K' log W`),
the claim `LWXigL` (`baZetaClaim_holds`), (B.22) `eq:Gbyxi2_BA`
(`baGbyZeta_holds`) and `lem:Anp` at the BA carrier (`hAnpQ`, `BAAnpAuxG` instantiated at `Q` and at the data); `n_M ≤ p`, `ord ≥ 2p`, `Φ(c r) ≲ Φ(r)` ((3.28) `eq:Psi`);
the tail is `≤ N^{-K_f} ≤ R`. -/
theorem BAMomentGen_prec_anp {p : ℕ} (hp : 0 < p) {V : ℕ → Type}
    (pr : ∀ n, V n → Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n)) {Q : BAPGraph (Fin 2)}
    (hQ : Q.g.Normal) (hxy : Q.g.mol (Sum.inl (Q.ext 0)) ≠ Q.g.mol (Sum.inl (Q.ext 1))) (hnM : Q.g.nM ≤ p)
    (hord : (2 * p : ℤ) ≤ Q.scalingOrder) {K : ℕ} (hK : Fintype.card (Q.E' ⊕ Q.I') ≤ K)
    (hAnpQ : ∃ cG : ℝ, 0 < cG ∧ ∀ ξ : (n : ℕ) → Zd d (sz.L n) → Zd d (sz.L n) → sz.SeqΩ → ℝ,
      ((∀ n α β ω, 0 ≤ ξ n α β ω ∧ ξ n α β ω = ξ n β α ω) ∧
        PrecL sz (Sizes.seqP (sz.withLam 0)) (U := fun n => Zd d (sz.L n) × Zd d (sz.L n))
          (fun n p ω => ξ n p.1 p.2 ω) (fun n p _ => Φ n ((zdistInf d (sz.L n) (p.1 - p.2) : ℕ) : ℝ)) ∧
        PrecL sz (Sizes.seqP (sz.withLam 0)) (U := fun n => Zd d (sz.L n)) (fun n α ω => ∑ β, ξ n α β ω ^ 2)
          (fun n _ _ => ((((sz.W n : ℕ) : ℝ) ^ d) * (baFMz sz z).eta n (t n))⁻¹)) →
      PrecL sz (Sizes.seqP (sz.withLam 0)) (U := fun n => Zd d (sz.L n) × Zd d (sz.L n))
        (fun n ab ω => Q.g.auxVal (fun α β => ξ n α β ω) fun e => if e = Q.ext 0 then ab.1 else ab.2)
        fun n ab _ => ((((sz.W n : ℕ) : ℝ) ^ d) * (baFMz sz z).eta n (t n))⁻¹ ^ Q.g.nM *
          Φ n (cG * ((zdistInf d (sz.L n) (ab.1 - ab.2) : ℕ) : ℝ)) ^ p * Φ n 0 ^ (Q.g.auxOrd - (p : ℤ))) :
    PrecL sz (Sizes.seqP (sz.withLam 0)) (U := V)
      (fun n v ω => ‖Q.val (BAMomentGen_D sz z n (t n) ω) ![(pr n v).1, (pr n v).2]‖)
      (fun n v _ => BAMomentGen_R sz z t Φ p n (pr n v).1 (pr n v).2) := by
  classical
  have hε₀ := hassm.1
  have hsz : sz.SizeTendsto := hflow.1.2.2.1
  have h𝔠 : 0 < 𝔠 := hflow.1.1
  have hcls := hassm.2.2.2.1
  have hpsi := BAMomentGen_psiAll hd hκ hε h𝔡 hflow ht0 ht1 hassm
  obtain ⟨cG, hcG, hAnp'⟩ := hAnpQ
  let Rb : ℕ → ℝ := fun n => (K : ℝ) * Real.log ((sz.W n : ℕ) : ℝ) ^ 2
  let ρ : ℕ → ℝ := fun n => (2 * (K : ℝ) + 1) * Real.log ((sz.W n : ℕ) : ℝ) ^ 2
  have hRb0 : ∀ n, 0 ≤ Rb n := fun n => by positivity
  have hρ0 : ∀ n, 0 ≤ ρ n := fun n => by positivity
  have hρrad : ∀ τ : ℝ, 0 < τ → ∀ᶠ n in atTop, ρ n + 1 ≤ ((sz.size n : ℕ) : ℝ) ^ τ := by
    intro τ hτ
    filter_upwards [lwXiRad_holds sz hsz (2 * (K : ℝ) + 1) 0 2 (by positivity) le_rfl zero_le_two τ hτ] with n hn
    simp only [ρ]; rw [Real.rpow_two] at hn; linarith
  have hsep : ∀ K' : ℝ, ∀ᶠ n in atTop, K' * Real.log ((sz.W n : ℕ) : ℝ) ≤ ρ n - 2 * Rb n := by
    intro K'
    filter_upwards [BAMomentGen_logW_ge hflow.1 K', BAMomentGen_logW_ge hflow.1 0] with n h1 h0
    simp only [ρ, Rb]
    nlinarith [mul_le_mul_of_nonneg_right h1 h0]
  set D₁ : ℝ := max ((d : ℝ) + 2 * C₂ / (𝔠 * d) + 1) (1 / 𝔠) with hD₁
  have hξ := baZetaClaim_holds d hd κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow t ht0 ht1 ε₀ C₁ C₂ C₃ Cc Φ hpsi hassm.2.2.2.2.2 ε₀ hassm.1
    hassm.2.2.1.1 ρ hρ0 hρrad D₁ le_rfl
  have hA3 := hAnp' _ hξ
  have hE2 := baGbyZeta_holds d hd κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow t ht0 ht1 ε₀ hassm.1 hassm.2.2.1.1 ρ Rb D₁ hRb0 hsep
  obtain ⟨K₀, K₁, Kd, Cg, cg, hK₀, hK₁, hKd, hCg, hcg, hGT⟩ := baGtoAGT_holds d hd 𝔡⁻¹ κ (inv_pos.2 h𝔡) hκ
  have hC₁ : 1 < C₁ := hassm.2.2.2.2.1.2.1
  have hC₂ : 1 < C₂ := hassm.2.2.2.2.1.2.2.1
  -- the exponents
  have hAe : ((Q.g.scalingOrder - Q.g.auxOrd).toNat : ℤ) = Q.g.scalingOrder - Q.g.auxOrd :=
    Int.toNat_of_nonneg (sub_nonneg.2 (Q.g.auxOrd_le_scalingOrder hQ))
  set e1 : ℕ := (Q.g.scalingOrder - Q.g.auxOrd).toNat with he1
  set k : ℕ := Q.g.shadow.molSolid.length with hk
  set A : ℕ := e1 + k + 1 with hAdef
  have hA1 : (1 : ℝ) ≤ A := by
    rw [hAdef]; push_cast; linarith [Nat.cast_nonneg (α := ℝ) e1, Nat.cast_nonneg (α := ℝ) k]
  have hApos : (0 : ℝ) < A := by linarith
  set cG' : ℝ := min cG 1 with hcG'
  have hcG'0 : 0 < cG' := lt_min hcG one_pos
  have hcG'1 : cG' ≤ 1 := min_le_right _ _
  set M : ℝ := max 1 C₃ with hMdef
  have hM1 : 1 ≤ M := le_max_left _ _
  set KG : ℝ := max 1 (Cc 2) * C₁ * (cG'⁻¹) ^ C₂ with hKG
  set K1 : ℝ := Q.g.sizeConst (K₀ * 1) K₁ Kd with hK1
  set K2 : ℝ := Q.g.sizeConst Cg (Cg * expC (d - 2) (cg / 2)) (Cg * (1 + expC (d - 2) (cg / 2))) with hK2
  have hK10 : 0 ≤ K1 := BASizeClaim_sizeConst_nonneg Q.g (by positivity) hK₁.le hKd
  have hK20 : 0 ≤ K2 := by
    have h1 : 0 ≤ expC (d - 2) (cg / 2) := lwMoment_expC_nonneg (d - 2) (half_pos hcg)
    exact BASizeClaim_sizeConst_nonneg Q.g hCg (by positivity) (by positivity)
  have hKG0 : 0 ≤ KG := by
    have : 0 < max 1 (Cc 2) := lt_of_lt_of_le one_pos (le_max_left _ _)
    rw [hKG]; positivity
  set Kbig : ℝ := K1 * M ^ e1 * KG ^ p with hKbig
  apply BAMomentGen_prec_of_whp
  intro τ hτ
  set τ₁ : ℝ := min (τ / (2 * A)) (𝔠 * ε₀ / 4) with hτ₁def
  have hτ₁ : 0 < τ₁ := lt_min (by positivity) (by positivity)
  refine ⟨_, HighProbAt.inter (Sizes.tendsto_size sz hsz) (HighProbAt.inter (Sizes.tendsto_size sz hsz)
    (BAMomentGen_entry_whp hd hκ hε h𝔡 hflow ht0 ht1 hassm hτ₁) (BAMomentGen_whp_of_prec sz hE2 hτ₁))
    (BAMomentGen_whp_of_prec sz hA3 hτ₁), ?_⟩
  filter_upwards [BAMomentGen_Psi_facts hd hκ hε h𝔡 hflow ht0 ht1 hassm hτ₁.le (min_le_right _ _),
    lwMoment_phi_facts hcls hassm.2.2.2.2.1, BAMomentGen_floor hd hκ hε h𝔡 hflow ht0 ht1 hassm p,
    BAMomentGen_tail hflow.1 hcg ((Q.g.nM + Q.g.nA + 1 : ℕ) : ℝ) ((p : ℝ) * (2 + C₂)), hsz.eventually_ge_atTop 1,
    hsz.eventually_ge_atTop K2, ((tendsto_rpow_atTop (half_pos hτ)).comp hsz).eventually_ge_atTop (Kbig + 1),
    BAflow_lam0_window κ ε 𝔠 𝔡 sz z hflow]
    with n hPsi hph hfl htail hN1 hNc hNb hn
  intro ω hω v
  obtain ⟨⟨hω1, hω2⟩, hω3⟩ := hω
  obtain ⟨hΦ0, hwin, hup⟩ := hPsi
  obtain ⟨hCc, hP, hcmp, hcGf⟩ := hph
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
  have hX1 : 1 ≤ ((sz.size n : ℕ) : ℝ) ^ τ₁ := Real.one_le_rpow hN1 hτ₁.le
  have hX0 : 0 ≤ ((sz.size n : ℕ) : ℝ) ^ τ₁ := by linarith
  have hW1 : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hW0 : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by linarith
  obtain ⟨hη0, hη1, ht1'⟩ := BAMomentGen_eta_facts hd hκ hε h𝔡 hflow ht0 ht1 hassm n
  obtain ⟨-, hr, -⟩ := ba_G_data hκ sz hflow n (ht0 n) (ht1 n)
  have hΨ0 : 0 < M * ((sz.size n : ℕ) : ℝ) ^ τ₁ * Φ n 0 := by positivity
  have hΨ1 : M * ((sz.size n : ℕ) : ℝ) ^ τ₁ * Φ n 0 ≤ 1 :=
    hup.trans (Real.rpow_le_one_of_one_le_of_nonpos hW1 (by linarith))
  have hMX : 1 ≤ M * ((sz.size n : ℕ) : ℝ) ^ τ₁ := by nlinarith
  have hf1 : Φ n 0 ≤ 1 := by
    refine le_trans ?_ hΨ1
    calc Φ n 0 = 1 * Φ n 0 := (one_mul _).symm
      _ ≤ M * ((sz.size n : ℕ) : ℝ) ^ τ₁ * Φ n 0 := mul_le_mul_of_nonneg_right hMX hΦ0.le
  have hRf := hfl (pr n v).1 (pr n v).2
  have hR0 : 0 ≤ BAMomentGen_R sz z t Φ p n (pr n v).1 (pr n v).2 :=
    (Real.rpow_nonneg hN0.le _).trans hRf
  have hNτ : 1 ≤ ((sz.size n : ℕ) : ℝ) ^ τ := Real.one_le_rpow hN1 hτ.le
  have hXA : (((sz.size n : ℕ) : ℝ) ^ τ₁) ^ A ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]
    refine Real.rpow_le_rpow_of_exponent_le hN1 ?_
    have : τ₁ ≤ τ / (2 * A) := min_le_left _ _
    calc τ₁ * (A : ℝ) ≤ τ / (2 * A) * A := mul_le_mul_of_nonneg_right this hApos.le
      _ = τ / 2 := by field_simp
  have hfinal : (((sz.size n : ℕ) : ℝ) ^ τ₁) ^ A * Kbig + 1 ≤ ((sz.size n : ℕ) : ℝ) ^ τ := by
    have hh : ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * ((sz.size n : ℕ) : ℝ) ^ (τ / 2) = ((sz.size n : ℕ) : ℝ) ^ τ := by
      rw [← Real.rpow_add hN0]; congr 1; ring
    have h1 : 1 ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) := Real.one_le_rpow hN1 (half_pos hτ).le
    have hKb : 0 ≤ Kbig := by rw [hKbig]; positivity
    calc (((sz.size n : ℕ) : ℝ) ^ τ₁) ^ A * Kbig + 1
        ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * Kbig + ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * 1 := by
          rw [mul_one]; exact add_le_add (mul_le_mul_of_nonneg_right hXA hKb) h1
      _ = ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * (Kbig + 1) := by ring
      _ ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * ((sz.size n : ℕ) : ℝ) ^ (τ / 2) :=
          mul_le_mul_of_nonneg_left hNb (by positivity)
      _ = _ := hh
  suffices h : ‖Q.val (BAMomentGen_D sz z n (t n) ω) ![(pr n v).1, (pr n v).2]‖ ≤
      ((((sz.size n : ℕ) : ℝ) ^ τ₁) ^ A * Kbig + 1) * BAMomentGen_R sz z t Φ p n (pr n v).1 (pr n v).2 by
    exact h.trans (mul_le_mul_of_nonneg_right hfinal hR0)
  by_cases hf : ∃ ℓ' : Q.E' → Idx d (sz.L n) (sz.W n), ![(pr n v).1, (pr n v).2] = ℓ' ∘ Q.ext
  · obtain ⟨ℓ', hℓ'⟩ := hf
    rw [BAVocab_val_of_factor Q _ hℓ']
    have hr0 : 0 ≤ Real.log ((sz.W n : ℕ) : ℝ) ^ 2 := by positivity
    have hA : ∀ a b : Idx d (sz.L n) (sz.W n), ‖(BAMomentGen_D sz z n (t n) ω).G a b - (BAMomentGen_D sz z n (t n) ω).M a b‖ ≤
        M * ((sz.size n : ℕ) : ℝ) ^ τ₁ * Φ n 0 := by
      intro a b
      refine (hω1 (a, b)).trans ?_
      calc ((sz.size n : ℕ) : ℝ) ^ τ₁ * Φ n 0 = 1 * (((sz.size n : ℕ) : ℝ) ^ τ₁ * Φ n 0) := (one_mul _).symm
        _ ≤ M * (((sz.size n : ℕ) : ℝ) ^ τ₁ * Φ n 0) := mul_le_mul_of_nonneg_right hM1 (by positivity)
        _ = _ := by ring
    have hξ0 : ∀ a b : Zd d (sz.L n), 0 ≤ ((sz.size n : ℕ) : ℝ) ^ τ₁ * baZetaVar sz z t ρ D₁ n a b ω :=
      fun a b => mul_nonneg hX0 (hξ.1 n a b ω).1
    have hξG : ∀ (x y : Idx d (sz.L n) (sz.W n)) (a b : Zd d (sz.L n)),
        (zdistD d (sz.L n) ((split d (sz.L n) (sz.W n) x).1 - a) : ℝ) ≤ Rb n →
        (zdistD d (sz.L n) ((split d (sz.L n) (sz.W n) y).1 - b) : ℝ) ≤ Rb n →
        ‖(BAMomentGen_D sz z n (t n) ω).G x y - (BAMomentGen_D sz z n (t n) ω).M x y‖ ≤
          ((sz.size n : ℕ) : ℝ) ^ τ₁ * baZetaVar sz z t ρ D₁ n a b ω :=
      fun x y a b h1 h2 => hω2 ⟨((x, y), (a, b)), h1, h2⟩
    have hwinv : (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ 1 * (M * ((sz.size n : ℕ) : ℝ) ^ τ₁ * Φ n 0) ^ 2 := by
      rw [one_mul, inv_le_iff_one_le_mul₀' (by positivity)]
      exact (one_le_pow_mul_sq_iff (sz.W n) d hW0 hΨ0.le).1 hwin
    have hRr : (Fintype.card (Q.E' ⊕ Q.I') : ℝ) * Real.log ((sz.W n : ℕ) : ℝ) ^ 2 ≤ Rb n :=
      mul_le_mul_of_nonneg_right (Nat.cast_le.2 hK) hr0
    have hgt := hGT (sz.L n) (sz.W n) (sz.three_le_L n) (BAflowLam0 sz z n) (BAflowEs sz z n) (t n)
      (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) hn.1 hn.2 hr (ht0 n) ht1' Q.E' Q.I' Q.g hQ
      (BAMomentGen_D sz z n (t n) ω) rfl rfl rfl rfl (M * ((sz.size n : ℕ) : ℝ) ^ τ₁ * Φ n 0) 1
      (Real.log ((sz.W n : ℕ) : ℝ) ^ 2) (Rb n) (fun a b => ((sz.size n : ℕ) : ℝ) ^ τ₁ * baZetaVar sz z t ρ D₁ n a b ω)
      hA zero_le_one hwinv hr0 hRr hξ0 hξG ℓ'
    have hsymm : ∀ a b, baZetaVar sz z t ρ D₁ n a b ω = baZetaVar sz z t ρ D₁ n b a ω :=
      fun a b => (hξ.1 n a b ω).2
    have hav : Q.g.auxVal (fun a b => ((sz.size n : ℕ) : ℝ) ^ τ₁ * baZetaVar sz z t ρ D₁ n a b ω)
        (fun a => (split d (sz.L n) (sz.W n) (ℓ' a)).1) =
        (((sz.size n : ℕ) : ℝ) ^ τ₁) ^ k * Q.g.auxVal (fun α β => baZetaVar sz z t ρ D₁ n α β ω)
          (fun e => if e = Q.ext 0 then STblk sz n (pr n v).1 else STblk sz n (pr n v).2) := by
      rw [BAMomentGen_auxVal_smul, BAMomentGen_be_eq Q hxy ℓ' _ _ hℓ']
      rfl
    have h3 := hω3 (STblk sz n (pr n v).1, STblk sz n (pr n v).2)
    have hs0 : (0 : ℝ) ≤ 1 * ((zdistInf d (sz.L n) (STblk sz n (pr n v).1 - STblk sz n (pr n v).2) : ℕ) : ℝ) := by
      positivity
    have hPcK : Φ n (cG * ((zdistInf d (sz.L n) (STblk sz n (pr n v).1 - STblk sz n (pr n v).2) : ℕ) : ℝ)) ≤
        KG * Φ n (1 * ((zdistInf d (sz.L n) (STblk sz n (pr n v).1 - STblk sz n (pr n v).2) : ℕ) : ℝ)) := by
      rw [one_mul]
      have hs : (0 : ℝ) ≤ ((zdistInf d (sz.L n) (STblk sz n (pr n v).1 - STblk sz n (pr n v).2) : ℕ) : ℝ) :=
        Nat.cast_nonneg _
      refine le_trans ?_ (hcGf cG' hcG'0 hcG'1 _ hs)
      exact hassm.2.2.2.2.1.1 n (Set.mem_Ici.2 (by positivity)) (Set.mem_Ici.2 (by positivity))
        (mul_le_mul_of_nonneg_right (min_le_left _ _) hs)
    have hord' : Q.g.scalingOrder = (e1 : ℤ) + Q.g.auxOrd := by rw [hAe]; ring
    have hord2 : (2 * p : ℤ) ≤ Q.g.scalingOrder := hord
    have harith := lwMoment_anp_arith (X := ((sz.size n : ℕ) : ℝ) ^ τ₁) (M := M) (f0 := Φ n 0)
      (η := (baFMz sz z).eta n (t n)) (w := ((sz.W n : ℕ) : ℝ) ^ d)
      (Pc := Φ n (cG * ((zdistInf d (sz.L n) (STblk sz n (pr n v).1 - STblk sz n (pr n v).2) : ℕ) : ℝ)))
      (Φs := Φ n (1 * ((zdistInf d (sz.L n) (STblk sz n (pr n v).1 - STblk sz n (pr n v).2) : ℕ) : ℝ)))
      (K1 := K1) (KG := KG) (nM := Q.g.nM) (p := p) (e1 := e1) (k := k) (ao := Q.g.auxOrd)
      (o := Q.g.scalingOrder) hX1 hM1 hΦ0 hf1 hη0 hη1 (by have := sz.W_pos n; positivity) (hP _ (by positivity)).le
      (hP _ hs0).le hPcK hK10 hKG0 hnM hord2 hord'
    have hX0' : (0 : ℝ) ≤ (((sz.size n : ℕ) : ℝ) ^ τ₁) ^ k := by positivity
    have hterm1 : K1 * (M * ((sz.size n : ℕ) : ℝ) ^ τ₁ * Φ n 0) ^ (Q.g.scalingOrder - Q.g.auxOrd) *
        ((((sz.W n : ℕ) : ℝ) ^ d) ^ Q.g.nM *
        Q.g.auxVal (fun a b => ((sz.size n : ℕ) : ℝ) ^ τ₁ * baZetaVar sz z t ρ D₁ n a b ω)
          (fun a => (split d (sz.L n) (sz.W n) (ℓ' a)).1)) ≤
        (((sz.size n : ℕ) : ℝ) ^ τ₁) ^ A * Kbig * BAMomentGen_R sz z t Φ p n (pr n v).1 (pr n v).2 := by
      rw [hav, ← hAe]
      refine le_trans ?_ harith
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h3 hX0')
        (by positivity)) (mul_nonneg hK10 (zpow_nonneg hΨ0.le _))
    have hsc := BAMomentGen_tail_le Q.g.counters (sz.W n) (sz.L n) d (sz.W_pos n) (by have := sz.three_le_L n; omega)
      hΨ0 hΨ1 hNc hK20 htail
    calc _ ≤ _ := hgt
      _ ≤ (((sz.size n : ℕ) : ℝ) ^ τ₁) ^ A * Kbig * BAMomentGen_R sz z t Φ p n (pr n v).1 (pr n v).2 +
          BAMomentGen_R sz z t Φ p n (pr n v).1 (pr n v).2 := add_le_add hterm1 (hsc.trans hRf)
      _ = _ := by ring
  · rw [BAVocab_val_of_not Q _ hf, norm_zero]
    have hKb : 0 ≤ Kbig := by rw [hKbig]; positivity
    exact mul_nonneg (add_nonneg (mul_nonneg (by positivity) hKb) zero_le_one) hR0

end Outputs2

/-! ## 10. The envelope and `≺ → 𝔼` -/

section Envelope

variable {d : ℕ} {sz : Sizes d} {z : ℕ → ℂ} {κ ε 𝔡 𝔠 : ℝ} {t : ℕ → ℝ} {ε₀ C₁ C₂ C₃ : ℝ} {Cc : ℝ → ℝ} {Ψ : ℕ → ℝ}
  {Φ : ℕ → ℝ → ℝ}
  (hd : 3 ≤ d) (hκ : 0 < κ) (hε : 0 < ε) (h𝔡 : 0 < 𝔡) (hflow : BAFlow sz κ ε 𝔠 𝔡 z) (ht0 : ∀ n, 0 ≤ t n)
  (ht1 : ∀ n, t n ≤ BAflowT0 sz z n)
  (hassm : 0 < ε₀ ∧ LWWindow sz ε₀ Ψ ∧ STInitialGT2gL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) t ε₀ Ψ ∧
    LWClass sz ε₀ C₃ Φ ∧ LWPsiRel C₁ C₂ Cc Φ ∧
    PrecL sz (Sizes.seqP (sz.withLam 0)) (U := fun n => Bool × Zd d (sz.L n) × Zd d (sz.L n))
      (fun n p ω => ‖(baFMz sz z).L n (t n) ![p.1, !p.1] ![p.2.1, p.2.2] ω‖)
      (fun n p _ => Φ n ((zdistInf d (sz.L n) (p.2.1 - p.2.2) : ℕ) : ℝ) ^ 2))
include hd hκ hε h𝔡 hflow ht0 ht1 hassm

/-- **The polynomial envelope** `‖Q.val D₁‖ ≤ N^{K}`, every sample, with `K` depending on the graph only (as `lwMoment_env`
in `Graph/LWMoment.lean`; `‖G - M‖ ≤ η⁻¹ + 1 ≤ 2 η⁻¹ ≤ 2 N²`). -/
theorem BAMomentGen_env (Q : BAPGraph (Fin 2)) (hQ : Q.g.Normal) :
    ∃ Kenv : ℝ, ∀ᶠ n in atTop, ∀ (x y : Idx d (sz.L n) (sz.W n)) (ω : sz.SeqΩ),
      ‖Q.val (BAMomentGen_D sz z n (t n) ω) ![x, y]‖ ≤ ((sz.size n : ℕ) : ℝ) ^ Kenv := by
  have hsz : sz.SizeTendsto := hflow.1.2.2.1
  obtain ⟨C, c, Kd, hC, hc, hKd, hdec⟩ := BAMomentGen_decay hd hκ hε h𝔡 hflow ht0 ht1 hassm
  have hC0 : 0 ≤ C := by linarith
  have hK1 : 0 ≤ C * expC (d - 2) c := by have := lwMoment_expC_nonneg (d - 2) hc; positivity
  refine ⟨((Q.g.nM + Q.g.nA + 3 * Q.g.nS + 1 : ℕ) : ℝ), ?_⟩
  filter_upwards [hdec, BAExp14a_eventual_scalars hκ hε h𝔡 hflow ht0 ht1,
    hsz.eventually_ge_atTop (Q.g.sizeConst C (C * expC (d - 2) c) Kd)] with n hn hev hNc x y ω
  obtain ⟨hSd, hSpd, hMPd, hoff, hKS, hKSp, hKM, hKP⟩ := hn ω
  obtain ⟨-, h4, hηN, -, -⟩ := hev
  set N : ℝ := ((sz.size n : ℕ) : ℝ) with hN
  have hN0 : 0 < N := by linarith
  obtain ⟨hη0, hη1, -⟩ := BAMomentGen_eta_facts hd hκ hε h𝔡 hflow ht0 ht1 hassm n
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
  have h1 := BAMomentGen_pval_claim Q hQ (BAMomentGen_D sz z n (t n) ω) hA hKS hKSp hKM hKP hC0 hK1 hKd ![x, y]
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
  calc ‖Q.val (BAMomentGen_D sz z n (t n) ω) ![x, y]‖
      ≤ Q.g.sizeConst C (C * expC (d - 2) c) Kd * (N ^ (Q.g.nM + Q.g.nA) * (N ^ 3) ^ Q.g.nS) :=
        h1.trans (mul_le_mul_of_nonneg_left h2 hK)
    _ ≤ N * (N ^ (Q.g.nM + Q.g.nA) * (N ^ 3) ^ Q.g.nS) :=
        mul_le_mul_of_nonneg_right hNc (by positivity)
    _ = N ^ ((Q.g.nM + Q.g.nA + 3 * Q.g.nS + 1 : ℕ) : ℝ) := by
        rw [Real.rpow_natCast, ← pow_mul]; ring

/-- From `≺` of `‖Q.val D₁‖` to `≺` of `‖𝔼 Q.val D₁‖` (`BAExp14a_prec_integral`: polynomial envelope and floor; as
`lwMoment_prec_int` in `Graph/LWMoment.lean`). -/
theorem BAMomentGen_prec_int (p : ℕ) {V : ℕ → Type} (pr : ∀ n, V n → Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n))
    {Q : BAPGraph (Fin 2)} (hQ : Q.g.Normal)
    (hprec : PrecL sz (Sizes.seqP (sz.withLam 0)) (U := V)
      (fun n v ω => ‖Q.val (BAMomentGen_D sz z n (t n) ω) ![(pr n v).1, (pr n v).2]‖)
      (fun n v _ => BAMomentGen_R sz z t Φ p n (pr n v).1 (pr n v).2)) :
    PrecL sz (Sizes.seqP (sz.withLam 0)) (U := V)
      (fun n v _ => ‖∫ ω, Q.val (BAMomentGen_D sz z n (t n) ω) ![(pr n v).1, (pr n v).2] ∂(BAExp14a_μ sz)‖)
      (fun n v _ => BAMomentGen_R sz z t Φ p n (pr n v).1 (pr n v).2) := by
  obtain ⟨Kenv, henv⟩ := BAMomentGen_env hd hκ hε h𝔡 hflow ht0 ht1 hassm Q hQ
  exact BAExp14a_prec_integral (P := BAExp14a_μ sz) (Sizes.tendsto_size sz hflow.1.2.2.1)
    (fun n v ω => Q.val (BAMomentGen_D sz z n (t n) ω) ![(pr n v).1, (pr n v).2])
    (fun n v => BAMomentGen_R sz z t Φ p n (pr n v).1 (pr n v).2) (Kenv := Kenv)
    (Kf := (p : ℝ) * (2 + C₂)) (henv.mono fun n h v ω => h _ _ ω)
    ((BAMomentGen_floor hd hκ hε h𝔡 hflow ht0 ht1 hassm p).mono fun n h v => h _ _) hprec

end Envelope

/-! ## 11. Continuity of graph values and the integral of lists (inputs of the expansion identity) -/

section ExpandTools

theorem BAMomentGen_cont_term {ι E I : Type} [Fintype ι] [DecidableEq ι] [Fintype I] [DecidableEq I] {Ω' : Type*}
    [TopologicalSpace Ω'] (Γ : BAGraph E I) (D : Ω' → BALData ι) (D0 : BALData ι)
    (hG : ∀ x y, Continuous fun ω => (D ω).G x y) (hS : ∀ ω, (D ω).S = D0.S) (hSp : ∀ ω, (D ω).Sp = D0.Sp)
    (hM : ∀ ω, (D ω).M = D0.M) (hP : ∀ ω, (D ω).gPsi = D0.gPsi) (ℓ : E ⊕ I → ι) :
    Continuous fun ω => Γ.term (D ω) ℓ := by
  unfold BAGraph.term LGraph.term
  refine Continuous.mul (Continuous.mul (Continuous.mul (Continuous.mul (continuous_const.mul ?_) ?_) ?_) ?_) ?_
  · refine continuous_list_prod _ fun e _ => ?_
    have hg : Continuous fun ω => (D ω).G (ℓ e.src) (ℓ e.dst) - (if e.circ = true then (D ω).M (ℓ e.src) (ℓ e.dst) else 0) := by
      simp only [hM]; exact (hG _ _).sub continuous_const
    by_cases hσ : e.σ = true
    · simpa [SEdge.val, hσ] using hg
    · simpa [SEdge.val, hσ] using hg.star
  · refine continuous_list_prod _ fun e _ => ?_
    simp only [WEdge.val, hS, hSp]
    exact continuous_const
  · exact continuous_const
  · refine continuous_list_prod _ fun e _ => ?_
    simp only [BAPsiEdge.val, hP]
    exact continuous_const
  · refine continuous_list_prod _ fun e _ => ?_
    simp only [BAMEdge.val, hM]
    exact continuous_const


theorem BAMomentGen_cont_val {ι : Type} [Fintype ι] [DecidableEq ι] {Ω' : Type*} [TopologicalSpace Ω']
    (D : Ω' → BALData ι) (D0 : BALData ι)
    (hG : ∀ x y, Continuous fun ω => (D ω).G x y) (hS : ∀ ω, (D ω).S = D0.S) (hSp : ∀ ω, (D ω).Sp = D0.Sp)
    (hM : ∀ ω, (D ω).M = D0.M) (hP : ∀ ω, (D ω).gPsi = D0.gPsi) (Q : BAPGraph (Fin 2)) (ℓe : Fin 2 → ι) :
    Continuous fun ω => Q.val (D ω) ℓe := by
  classical
  by_cases hf : ∃ ℓ' : Q.E' → ι, ℓe = ℓ' ∘ Q.ext
  · obtain ⟨ℓ', hℓ'⟩ := hf
    have : (fun ω => Q.val (D ω) ℓe) = fun ω => Q.g.val (D ω) ℓ' := funext fun ω => BAVocab_val_of_factor Q (D ω) hℓ'
    rw [this]
    unfold BAGraph.val
    exact continuous_finsetSum _ fun ℓi _ => BAMomentGen_cont_term Q.g D D0 hG hS hSp hM hP _
  · have : (fun ω => Q.val (D ω) ℓe) = fun _ => 0 := funext fun ω => BAVocab_val_of_not Q (D ω) hf
    rw [this]; exact continuous_const

theorem BAMomentGen_cont_comb {ι : Type} [Fintype ι] [DecidableEq ι] {Ω' : Type*} [TopologicalSpace Ω']
    (D : Ω' → BALData ι) (D0 : BALData ι)
    (hG : ∀ x y, Continuous fun ω => (D ω).G x y) (hS : ∀ ω, (D ω).S = D0.S) (hSp : ∀ ω, (D ω).Sp = D0.Sp)
    (hM : ∀ ω, (D ω).M = D0.M) (hP : ∀ ω, (D ω).gPsi = D0.gPsi) (L : List (BAPGraph (Fin 2))) (ℓe : Fin 2 → ι) :
    Continuous fun ω => BAComb.val L (D ω) ℓe := by
  unfold BAComb.val
  exact continuous_list_sum _ fun Q _ => BAMomentGen_cont_val D D0 hG hS hSp hM hP Q ℓe

theorem BAMomentGen_cont_fxyVal {ι : Type} [Fintype ι] [DecidableEq ι] {Ω' : Type*} [TopologicalSpace Ω']
    (D : Ω' → BALData ι) (D0 : BALData ι)
    (hG : ∀ x y, Continuous fun ω => (D ω).G x y) (hS : ∀ ω, (D ω).S = D0.S) (hM : ∀ ω, (D ω).M = D0.M) (x y : ι) :
    Continuous fun ω => fxyVal (D ω).toLData x y := by
  unfold fxyVal
  refine continuous_finsetSum _ fun α _ => ?_
  split_ifs
  · exact continuous_const
  · refine continuous_finsetSum _ fun β _ => ?_
    simp only [hS, hM]
    exact ((continuous_const.mul ((hG β β).sub continuous_const)).mul (hG x α)).mul (hG α y)

/-- The integral of a finite list sum (the sum of the integrals of integrable summands). -/
theorem BAMomentGen_integral_list_sum {Ω' : Type*} [MeasurableSpace Ω'] {μ : Measure Ω'} {ι : Type*} (l : List ι)
    (f : ι → Ω' → ℂ) (hf : ∀ i ∈ l, Integrable (f i) μ) :
    Integrable (fun ω => (l.map fun i => f i ω).sum) μ ∧
      ∫ ω, (l.map fun i => f i ω).sum ∂μ = (l.map fun i => ∫ ω, f i ω ∂μ).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    obtain ⟨ih1, ih2⟩ := ih fun i hi => hf i (List.mem_cons_of_mem _ hi)
    have ha := hf a (List.mem_cons_self ..)
    refine ⟨?_, ?_⟩
    · simp only [List.map_cons, List.sum_cons]
      exact ha.add ih1
    · simp only [List.map_cons, List.sum_cons]
      rw [integral_add ha ih1, ih2]

end ExpandTools

/-! ## 12. The expansion identity -/

section Expand

variable {d : ℕ} {sz : Sizes d} {z : ℕ → ℂ} {κ ε 𝔡 𝔠 : ℝ} {t : ℕ → ℝ}
  (hκ : 0 < κ) (hflow : BAFlow sz κ ε 𝔠 𝔡 z) (ht0 : ∀ n, 0 ≤ t n) (ht1 : ∀ n, t n ≤ BAflowT0 sz z n)
include hκ hflow ht0 ht1

/-- **The expansion identity** (the expansion in the proof of Lemma 7.22; as `lwMoment_expand` in `Graph/LWMoment.lean`): from the engine lists, at a sample size
with `0 < t < 1`, `𝔼 |f_{xy}|^p ≤ Σ_Q ‖𝔼 Q.val D₁‖` (`BALocRegConcl` (d) for the start graph at the data `BAlwData` over the model law,
transported to the sample space through the slice; `LWfg_baFMz`; the homogeneity `BAExp14d_val_scale`: `Q.val (BAlwData) = t^{n_W} Q.val D₁`,
`n_W ≥ p` by the lists' `n_{W,black} ≥ p`, `t < 1`).  The integrability of the summands is a hypothesis (proved for large `n` from the
envelope). -/
theorem BAMomentGen_expand {p : ℕ} (hp : Even p) (n : ℕ) {c : ℝ} {K0 : ℕ} {D : ℝ} {outs errs : List (BAPGraph (Fin 2))}
    (h : BALocRegConcl p c K0 d D outs errs) (hw : ∀ Q ∈ outs ++ errs, p ≤ Q.g.waved.countP (fun e => !e.col))
    (x y : Idx d (sz.L n) (sz.W n)) (htp : 0 < t n)
    (hint : ∀ Q ∈ outs ++ errs,
      Integrable (fun ω => Q.val (BAMomentGen_D sz z n (t n) ω) ![x, y]) (BAExp14a_μ sz)) :
    ∫ ω, ‖LWfg (baFMz sz z) n (t n) ω x y‖ ^ p ∂(BAExp14a_μ sz) ≤
      ((outs ++ errs).map fun Q =>
        ‖∫ ω, Q.val (BAMomentGen_D sz z n (t n) ω) ![x, y] ∂(BAExp14a_μ sz)‖).sum := by
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
  have hid := (ba_fxyPow_integral_eq d (sz.L n) (sz.W n) (BAflowLam0 sz z n) (BAflowEs sz z n) (t n)
    (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) p hp ![x, y]).symm.trans
    (h.2.2.2 (sz.L n) (sz.W n) (sz.three_le_L n) (BAflowLam0 sz z n) (BAflowEs sz z n) (t n)
      (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) hSelf (ht0 n) ht1' ![x, y])
  have hF := BAMomentGen_cont_fxyVal Dω (Dω fun _ => 0) hGc hS hM x y
  have hΦ₁ : Continuous fun ω' : Ω d (sz.L n) (sz.W n) =>
      fxyVal (Dω ω').toLData x y ^ (p / 2) * star (fxyVal (Dω ω').toLData x y) ^ (p / 2) :=
    (hF.pow _).mul (hF.star.pow _)
  have hΨ₂ := BAMomentGen_cont_comb Dω (Dω fun _ => 0) hGc hS hSp hM hP (outs ++ errs) ![x, y]
  have h1 := BAExp14a_int_slice (sz := sz) n _ hΦ₁
  have h2 := BAExp14a_int_slice (sz := sz) n _ hΨ₂
  have hμeq := h1.trans (hid.trans h2.symm)
  -- the left side, pointwise
  have hL : ∀ ω : sz.SeqΩ, fxyVal (Dω (BAExp14a_slc sz n ω)).toLData x y ^ (p / 2) *
      star (fxyVal (Dω (BAExp14a_slc sz n ω)).toLData x y) ^ (p / 2) =
      ((t n ^ p * ‖LWfg (baFMz sz z) n (t n) ω x y‖ ^ p : ℝ) : ℂ) := by
    intro ω
    have hF' : fxyVal (Dω (BAExp14a_slc sz n ω)).toLData x y = (t n : ℂ) * LWfg (baFMz sz z) n (t n) ω x y :=
      (LWfg_baFMz sz z n (t n) ω x y).symm
    obtain ⟨k, hk⟩ := hp
    have hk2 : p / 2 = k := by omega
    have hk3 : 2 * k = p := by omega
    rw [hk2, hF', show (star ((t n : ℂ) * LWfg (baFMz sz z) n (t n) ω x y)) =
        (t n : ℂ) * star (LWfg (baFMz sz z) n (t n) ω x y) by simp [star_mul'], mul_pow, mul_pow]
    have h1 := lwMoment_pow_conj (LWfg (baFMz sz z) n (t n) ω x y) k
    calc _ = (t n : ℂ) ^ k * (t n : ℂ) ^ k * (LWfg (baFMz sz z) n (t n) ω x y ^ k * star (LWfg (baFMz sz z) n (t n) ω x y) ^ k) := by
          ring
      _ = _ := by rw [h1, ← hk3]; push_cast; ring
  -- the right side, pointwise
  have hR : ∀ ω : sz.SeqΩ, BAComb.val (outs ++ errs) (Dω (BAExp14a_slc sz n ω)) ![x, y] =
      ((outs ++ errs).map fun Q => (t n : ℂ) ^ Q.g.nW * Q.val (BAMomentGen_D sz z n (t n) ω) ![x, y]).sum := by
    intro ω
    unfold BAComb.val
    congr 1
    refine List.map_congr_left fun Q _ => ?_
    exact BAExp14d_val_scale d (sz.L n) (sz.W n) (sz.three_le_L n) _ κ _ (t n) _ hr (ht0 n) ht1' (BAExp14a_slc sz n ω) Q ![x, y]
  simp only [hL, hR] at hμeq
  have hI0 : 0 ≤ ∫ ω, ‖LWfg (baFMz sz z) n (t n) ω x y‖ ^ p ∂(BAExp14a_μ sz) :=
    integral_nonneg fun ω => by positivity
  obtain ⟨hsumI, hsum⟩ := BAMomentGen_integral_list_sum (Ω' := sz.SeqΩ) (μ := BAExp14a_μ sz) (outs ++ errs)
    (fun Q ω => (t n : ℂ) ^ Q.g.nW * Q.val (BAMomentGen_D sz z n (t n) ω) ![x, y])
    (fun Q hQ => (hint Q hQ).const_mul _)
  rw [hsum] at hμeq
  have hLHS : ∫ ω, ((t n ^ p * ‖LWfg (baFMz sz z) n (t n) ω x y‖ ^ p : ℝ) : ℂ) ∂(BAExp14a_μ sz) =
      ((t n ^ p * ∫ ω, ‖LWfg (baFMz sz z) n (t n) ω x y‖ ^ p ∂(BAExp14a_μ sz) : ℝ) : ℂ) := by
    rw [integral_complex_ofReal, integral_const_mul]
  have hid' : ((t n ^ p * ∫ ω, ‖LWfg (baFMz sz z) n (t n) ω x y‖ ^ p ∂(BAExp14a_μ sz) : ℝ) : ℂ) =
      ((outs ++ errs).map fun Q => (t n : ℂ) ^ Q.g.nW *
        ∫ ω, Q.val (BAMomentGen_D sz z n (t n) ω) ![x, y] ∂(BAExp14a_μ sz)).sum := by
    rw [← hLHS, hμeq]
    congr 1
    refine List.map_congr_left fun Q _ => ?_
    rw [integral_const_mul]
  have hnn : 0 ≤ t n ^ p * ∫ ω, ‖LWfg (baFMz sz z) n (t n) ω x y‖ ^ p ∂(BAExp14a_μ sz) :=
    mul_nonneg (by have := ht0 n; positivity) hI0
  have hle : t n ^ p * ∫ ω, ‖LWfg (baFMz sz z) n (t n) ω x y‖ ^ p ∂(BAExp14a_μ sz) ≤
      ((outs ++ errs).map fun Q =>
        t n ^ p * ‖∫ ω, Q.val (BAMomentGen_D sz z n (t n) ω) ![x, y] ∂(BAExp14a_μ sz)‖).sum := by
    have h2 := congrArg norm hid'
    rw [Complex.norm_real, Real.norm_of_nonneg hnn] at h2
    rw [h2]
    refine (lwMoment_norm_list_sum_le _ _).trans ?_
    refine List.sum_le_sum fun Q hQ => ?_
    simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos htp]
    refine mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one htp.le ht1'.le ?_) (norm_nonneg _)
    exact (hw Q hQ).trans List.countP_le_length
  rw [List.sum_map_mul_left] at hle
  exact le_of_mul_le_mul_left hle (by positivity)

end Expand

/-! ## 13. The far pairs: the assembly of the expansion -/

section FarAssembly

variable {d : ℕ} {sz : Sizes d} {z : ℕ → ℂ} {κ ε 𝔡 𝔠 : ℝ} {t : ℕ → ℝ} {ε₀ C₁ C₂ C₃ : ℝ} {Cc : ℝ → ℝ} {Ψ : ℕ → ℝ}
  {Φ : ℕ → ℝ → ℝ}

/-- The far pairs `(x, y)`: block distance `> K (log W)²` (as `LWMomFar` in `Graph/LWMoment.lean`). -/
def BAMomentGen_Far (sz : Sizes d) (K : ℕ) (n : ℕ) : Type :=
  {q : Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n) //
    (K : ℝ) * Real.log ((sz.W n : ℕ) : ℝ) ^ 2 < (lwBdist d (sz.L n) (sz.W n) q.1 q.2 : ℝ)}

/-- At `t = 0` the carrier `f_{xy}` vanishes (`Ǧ = 0`: `G - M = -M (√t V + t m) G`; as `lwMoment_LWf_zero`). -/
theorem BAMomentGen_LWfg_zero (hκ : 0 < κ) (hflow : BAFlow sz κ ε 𝔠 𝔡 z) (n : ℕ)
    (h1 : (0 : ℝ) ≤ BAflowT0 sz z n) (ω : sz.SeqΩ) (x y : Idx d (sz.L n) (sz.W n)) :
    LWfg (baFMz sz z) n 0 ω x y = 0 := by
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
  unfold LWfg
  refine Finset.sum_eq_zero fun α _ => ?_
  split_ifs
  · rfl
  refine Finset.sum_eq_zero fun β _ => ?_
  rw [hz β β]
  simp

variable (hd : 3 ≤ d) (hκ : 0 < κ) (hε : 0 < ε) (h𝔡 : 0 < 𝔡) (hflow : BAFlow sz κ ε 𝔠 𝔡 z) (ht0 : ∀ n, 0 ≤ t n)
  (ht1 : ∀ n, t n ≤ BAflowT0 sz z n)
  (hassm : 0 < ε₀ ∧ LWWindow sz ε₀ Ψ ∧ STInitialGT2gL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) t ε₀ Ψ ∧
    LWClass sz ε₀ C₃ Φ ∧ LWPsiRel C₁ C₂ Cc Φ ∧
    PrecL sz (Sizes.seqP (sz.withLam 0)) (U := fun n => Bool × Zd d (sz.L n) × Zd d (sz.L n))
      (fun n p ω => ‖(baFMz sz z).L n (t n) ![p.1, !p.1] ![p.2.1, p.2.2] ω‖)
      (fun n p _ => Φ n ((zdistInf d (sz.L n) (p.2.1 - p.2.2) : ℕ) : ℝ) ^ 2))
variable {p : ℕ}
  (hAnpL : ∀ Q : BAPGraph (Fin 2), Q.g.nM ≤ p → (BAShadowPG Q).LocReg345 p →
    Q.g.mol (Sum.inl (Q.ext 0)) ≠ Q.g.mol (Sum.inl (Q.ext 1)) →
    ∃ cG : ℝ, 0 < cG ∧ ∀ ξ : (n : ℕ) → Zd d (sz.L n) → Zd d (sz.L n) → sz.SeqΩ → ℝ,
      ((∀ n α β ω, 0 ≤ ξ n α β ω ∧ ξ n α β ω = ξ n β α ω) ∧
        PrecL sz (Sizes.seqP (sz.withLam 0)) (U := fun n => Zd d (sz.L n) × Zd d (sz.L n))
          (fun n p ω => ξ n p.1 p.2 ω) (fun n p _ => Φ n ((zdistInf d (sz.L n) (p.1 - p.2) : ℕ) : ℝ)) ∧
        PrecL sz (Sizes.seqP (sz.withLam 0)) (U := fun n => Zd d (sz.L n)) (fun n α ω => ∑ β, ξ n α β ω ^ 2)
          (fun n _ _ => ((((sz.W n : ℕ) : ℝ) ^ d) * (baFMz sz z).eta n (t n))⁻¹)) →
      PrecL sz (Sizes.seqP (sz.withLam 0)) (U := fun n => Zd d (sz.L n) × Zd d (sz.L n))
        (fun n ab ω => Q.g.auxVal (fun α β => ξ n α β ω) fun e => if e = Q.ext 0 then ab.1 else ab.2)
        fun n ab _ => ((((sz.W n : ℕ) : ℝ) ^ d) * (baFMz sz z).eta n (t n))⁻¹ ^ Q.g.nM *
          Φ n (cG * ((zdistInf d (sz.L n) (ab.1 - ab.2) : ℕ) : ℝ)) ^ p * Φ n 0 ^ (Q.g.auxOrd - (p : ℤ)))
include hd hκ hε h𝔡 hflow ht0 ht1 hassm hAnpL

/-- Every graph `Q` of the engine lists has `‖𝔼 Q.val D₁‖ ≺ R` at the far pairs (as `lwMoment_prec_far_r`
in `Graph/LWMoment.lean`).  `h15` is the contract (1)-(5) at the outputs: `n_M ≤ p` and (3)-(5) on the shadow (`BALocReg15`);
(6) `2p ≤ ord` is read from the conjunct (a) of `BALocRegConcl`. -/
theorem BAMomentGen_prec_far_r (hp0 : 0 < p) {K0 : ℕ} {D : ℝ} (hK0 : 1 / 𝔠 ≤ K0)
    (hD : ((p : ℝ) * (2 + C₂) + 1) / 𝔠 ≤ D) {outs errs : List (BAPGraph (Fin 2))}
    (hc : BALocRegConcl p (ε₀ / 2) K0 d D outs errs)
    (h15 : ∀ Q ∈ outs, Q.g.nM ≤ p ∧ (BAShadowPG Q).LocReg345 p)
    {K : ℕ} {Q : BAPGraph (Fin 2)} (hr : Q ∈ outs ++ errs) (hK : Fintype.card (Q.E' ⊕ Q.I') ≤ K) :
    PrecL sz (Sizes.seqP (sz.withLam 0)) (U := BAMomentGen_Far sz K)
      (fun n v _ => ‖∫ ω, Q.val (BAMomentGen_D sz z n (t n) ω) ![v.1.1, v.1.2] ∂(BAExp14a_μ sz)‖)
      (fun n v _ => BAMomentGen_R sz z t Φ p n v.1.1 v.1.2) := by
  classical
  obtain ⟨hc1, hc2, hc3, -⟩ := hc
  obtain ⟨P0, -, -, hQ, -⟩ := hc3 Q hr
  have key : PrecL sz (Sizes.seqP (sz.withLam 0)) (U := BAMomentGen_Far sz K)
      (fun n v ω => ‖Q.val (BAMomentGen_D sz z n (t n) ω) ![v.1.1, v.1.2]‖)
      (fun n v _ => BAMomentGen_R sz z t Φ p n v.1.1 v.1.2) := by
    rcases List.mem_append.1 hr with h | h
    · obtain ⟨-, h6, -⟩ := hc1 Q h
      obtain ⟨hnM, h345⟩ := h15 Q h
      by_cases hmol : Q.g.mol (Sum.inl (Q.ext 0)) = Q.g.mol (Sum.inl (Q.ext 1))
      · exact BAMomentGen_prec_scale hd hκ hε h𝔡 hflow ht0 ht1 hassm p (V := BAMomentGen_Far sz K) (fun n v => v.1) hQ hmol hK
          (fun n v => v.2)
      · exact BAMomentGen_prec_anp hd hκ hε h𝔡 hflow ht0 ht1 hassm hp0 (V := BAMomentGen_Far sz K) (fun n v => v.1) hQ hmol
          hnM h6 hK (hAnpL Q hnM h345 hmol)
    · exact BAMomentGen_prec_err hd hκ hε h𝔡 hflow ht0 ht1 hassm p hK0 hD (V := BAMomentGen_Far sz K) (fun n v => v.1) hQ (hc2 Q h)
  exact BAMomentGen_prec_int hd hκ hε h𝔡 hflow ht0 ht1 hassm p (V := BAMomentGen_Far sz K) (fun n v => v.1) hQ key

/-- **The far pairs** (proof of Lemma 7.1; as `lwMoment_prec_far` in `Graph/LWMoment.lean`): from the engine lists
(`ba_localregularX_holds`), `𝔼 |f_{xy}|^p ≺ R` for the pairs at block distance `> K (log W)²`, `K ≥` the number of vertices of
every graph of the lists.  The `n`-th expansion is at the flow data of `n`; the outputs with `𝓜_x ≠ 𝓜_y` use `lem:Anp` at BA (`hAnpL`),
those with `𝓜_x = 𝓜_y` use (7.12) `eq:far_ab`, the errors use the size bound. -/
theorem BAMomentGen_prec_far (hp : Even p) (hp0 : 0 < p) {K0 : ℕ} {D : ℝ} (hK0 : 1 / 𝔠 ≤ K0)
    (hD : ((p : ℝ) * (2 + C₂) + 1) / 𝔠 ≤ D) {outs errs : List (BAPGraph (Fin 2))}
    (hc : BALocRegConcl p (ε₀ / 2) K0 d D outs errs)
    (hw : ∀ Q ∈ outs ++ errs, p ≤ Q.g.waved.countP (fun e => !e.col))
    (h15 : ∀ Q ∈ outs, Q.g.nM ≤ p ∧ (BAShadowPG Q).LocReg345 p)
    {K : ℕ} (hK : ∀ Q ∈ outs ++ errs, Fintype.card (Q.E' ⊕ Q.I') ≤ K) :
    PrecL sz (Sizes.seqP (sz.withLam 0)) (U := BAMomentGen_Far sz K)
      (fun n q _ => ∫ ω, ‖LWfg (baFMz sz z) n (t n) ω q.1.1 q.1.2‖ ^ p ∂(BAExp14a_μ sz))
      (fun n q _ => BAMomentGen_R sz z t Φ p n q.1.1 q.1.2) := by
  classical
  have hsz : sz.SizeTendsto := hflow.1.2.2.1
  have hnorm : ∀ Q ∈ outs ++ errs, Q.g.Normal := fun Q hQ => by
    obtain ⟨P0, -, -, hN, -⟩ := hc.2.2.1 Q hQ
    exact hN
  let F : BAPGraph (Fin 2) → ∀ n, BAMomentGen_Far sz K n → ℝ := fun Q n v =>
    ‖∫ ω, Q.val (BAMomentGen_D sz z n (t n) ω) ![v.1.1, v.1.2] ∂(BAExp14a_μ sz)‖
  let G : ∀ n, BAMomentGen_Far sz K n → ℝ := fun n v => BAMomentGen_R sz z t Φ p n v.1.1 v.1.2
  refine (BAExp14a_det_iff (P := BAExp14a_μ sz) (Sizes.tendsto_size sz hsz)
    (fun n (v : BAMomentGen_Far sz K n) => ∫ ω, ‖LWfg (baFMz sz z) n (t n) ω v.1.1 v.1.2‖ ^ p ∂(BAExp14a_μ sz)) G).2 ?_
  intro τ hτ
  have hper : ∀ Q ∈ outs ++ errs, PrecL sz (Sizes.seqP (sz.withLam 0)) (U := BAMomentGen_Far sz K) (fun n v _ => F Q n v)
      (fun n v _ => G n v) :=
    fun Q hQ => BAMomentGen_prec_far_r hd hκ hε h𝔡 hflow ht0 ht1 hassm hAnpL hp0 hK0 hD hc h15 hQ (hK Q hQ)
  have hG : ∀ n (v : BAMomentGen_Far sz K n), 0 ≤ G n v := fun n v => hp.pow_nonneg _
  have hsum := lwMoment_sum_det sz hsz (V := BAMomentGen_Far sz K) (outs ++ errs) F G hG
    (fun Q hQ => (BAExp14a_det_iff (P := BAExp14a_μ sz) (Sizes.tendsto_size sz hsz) (F Q) G).1 (hper Q hQ)) τ hτ
  -- the envelopes of the members of the lists
  have henv : ∀ Q ∈ outs ++ errs, ∃ Kenv : ℝ, ∀ᶠ n in atTop, ∀ (x y : Idx d (sz.L n) (sz.W n)) (ω : sz.SeqΩ),
      ‖Q.val (BAMomentGen_D sz z n (t n) ω) ![x, y]‖ ≤ ((sz.size n : ℕ) : ℝ) ^ Kenv :=
    fun Q hQ => BAMomentGen_env hd hκ hε h𝔡 hflow ht0 ht1 hassm Q (hnorm Q hQ)
  choose! Ke hKe using henv
  have hall : ∀ᶠ n in atTop, ∀ Q ∈ outs ++ errs, ∀ (x y : Idx d (sz.L n) (sz.W n)) (ω : sz.SeqΩ),
      ‖Q.val (BAMomentGen_D sz z n (t n) ω) ![x, y]‖ ≤ ((sz.size n : ℕ) : ℝ) ^ Ke Q :=
    (Filter.eventually_all_finite (List.finite_toSet (outs ++ errs))).2 hKe
  filter_upwards [hsum, hall] with n hn hen
  intro v
  by_cases ht0' : t n = 0
  · have : ∀ ω, ‖LWfg (baFMz sz z) n (t n) ω v.1.1 v.1.2‖ ^ p = 0 := fun ω => by
      rw [ht0', BAMomentGen_LWfg_zero hκ hflow n (by have := ht1 n; rwa [ht0'] at this) ω]; simp [hp0.ne']
    simp only [this, integral_zero]
    exact mul_nonneg (Real.rpow_nonneg (by positivity) _) (hG n v)
  · have htp : 0 < t n := lt_of_le_of_ne (ht0 n) (Ne.symm ht0')
    refine le_trans (BAMomentGen_expand hκ hflow ht0 ht1 hp n hc hw v.1.1 v.1.2 htp (fun Q hQ => ?_)) (hn v)
    refine BAExp14a_integrable ?_ (hen Q hQ v.1.1 v.1.2)
    have hGc : ∀ a b, Continuous fun ω : sz.SeqΩ => (BAMomentGen_D sz z n (t n) ω).G a b :=
      fun a b => BAExp14a_cont_G hκ hflow n (ht0 n) (ht1 n) a b
    exact BAMomentGen_cont_val (fun ω : sz.SeqΩ => BAMomentGen_D sz z n (t n) ω) (BAMomentGen_D sz z n (t n) 0) hGc
      (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) Q ![v.1.1, v.1.2]

end FarAssembly

end RBM.BA

end
