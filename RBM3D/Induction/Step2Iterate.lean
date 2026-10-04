/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Induction.Step2Events
import RBM3D.Induction.Step2Scale
import RBM3D.Path.NetLift2
import RBM3D.Induction.Step2K2

/-!
# ST2-04 (ticket T2092): the iteration over scales and the closure of Step 2 from its pins

Moved from the T2039 design probe (`git show 0362cbc:RBM3D/Probe/T2039Pins.lean`): section 10
(probe lines 2243-2525, without `STScaleInv`, `ST_STprof_pos`, `ST_card_lab_le`, which are merged in
`Step2Events.lean`, and without `STScaleOk`, `STScaleAdm`, merged in `Step2Defs.lean`), section 11
`Main` and `Iterate2` (3572-4089), section 12 (4090-4728, without the pins merged in `Step2Defs.lean`),
12.1 (4729-4886, without the bundle `STStep2Concl` and its parts, merged in `Step34Pins.lean`) and
12.2 (4888-5346, without the loop vocabulary `STLI` ... `STGridRepN`, merged).  Paper:
`paper/tex/3_5_Loop_Hierarchy.tex:345-609`.

Differences from the probe text: the namespace `RBM.Probe.T2039` is `RBM.Gauss.Sizes` everywhere, the
`RBM.Probe.T2039` entries of the `open` lines are dropped, and `ST2_Bctl_pos`, `ST2_Bctl_mono` are the
merged `STBctl_pos`, `STBctl_mono` (`Induction/ScaleFacts.lean`).  Adaptation (preflight finding D-1):
the merged `STStep2` concludes the bundle `STStep2Concl`, the probe's concluded the triple
`STStep2Local ∧ STStep2Avg ∧ STStep2Decay`; the probe's statement is `STStep2Parts` (new), the last line
of `ST_step2_of_pins` goes through `ST_concl_of_step2`, and `ST_step2_concl` is stated for
`STStep2Parts`.  The final section `Corollaries` (new) discharges the pins now proved, and the section
`Instances` holds one compiled nonempty `example` per target.
-/

set_option linter.style.longLine false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal

/-! ## 10. The iteration over scales (`3_5:512–577`)

`STScaleInv` is the premise of the light-weight lemmas at the scale family `Kf` (at every time
section); `STSelfImp` is the conclusion of one self-improving step (the Grönwall bound for `Ĵ`);
`STScaleAdm` says that `Kseq` is the iteration `𝒯_u(K_{m+1}) = 𝒯_u(K_m) (W^{-d}B_{u,0})^{1/6}`
(`(eq:def_ell1)`) started at `K_0 = 0`. -/

namespace RBM.Gauss.Sizes

open RBM RBM.Loop RBM.Path

section Iter

variable {d : ℕ} (sz : Sizes d)

/-- The conclusion of one self-improving step (`(eq:Gronwall_dervJuD)`, per time): for every `D > 0`
`|(𝓛-𝒦)^{(2)}_{u,σ,a}| ≺ ((1-s)/(1-u))^{C_d} (W^{-d}B_{u,0})^{1/5} W^{-d} 𝒯̃^{K_u}_{u,D}(|a₁-a₂|)`. -/
def STSelfImp (Cd : ℝ) (E s t : ℕ → ℝ) (Kf : ℕ → ℝ → ℝ) : Prop :=
  ∀ D : ℝ, 0 < D →
    PrecPT sz (U := fun n => TimeIcc s t n × (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)))
      (fun n p ω => ‖Lloop sz n (E n) (p.1 : ℝ) p.2.1 p.2.2 ω -
        STKloop sz n (E n) (p.1 : ℝ) p.2.1 p.2.2‖)
      (fun n p _ => ((1 - s n) / (1 - (p.1 : ℝ))) ^ Cd * (sz.Bctl n (p.1 : ℝ)) ^ (1 / 5 : ℝ) *
        STprof sz n (p.1 : ℝ) D (Kf n (p.1 : ℝ)) (p.2.2 0) (p.2.2 1))

/-- Enlarging the control pointwise (eventually in `n`, for all sample points) preserves `PrecPT`. -/
theorem ST_PT_mono_eventually {U : ℕ → Type*} {ξ ζ ζ' : ∀ n, U n → sz.SeqΩ → ℝ}
    (hle : ∀ᶠ n in atTop, ∀ u ω, ζ n u ω ≤ ζ' n u ω) (h : sz.PrecPT ξ ζ) : sz.PrecPT ξ ζ' := by
  intro τ hτ D hD
  filter_upwards [h τ hτ D hD, hle] with n hn hle' u
  refine le_trans (measure_mono ?_) (hn u)
  intro ω hω
  exact lt_of_le_of_lt
    (mul_le_mul_of_nonneg_left (hle' u ω) (Real.rpow_nonneg (Nat.cast_nonneg _) _)) hω

/-- The `L^∞` distance on the torus is at most `L`. -/
theorem ST_zdistInf_le (n : ℕ) (x : Zd d (sz.L n)) : ((zdistInf d (sz.L n) x : ℕ) : ℝ) ≤ ((sz.L n : ℕ) : ℝ) := by
  have : zdistInf d (sz.L n) x ≤ sz.L n := by
    refine Finset.sup_le fun i _ => ?_
    exact (min_le_left _ _).trans (ZMod.val_lt (x i)).le
  exact_mod_cast this

/-- **From one self-improving step to the next premise** (`(eq:def_ell1)`, `3_5:570–575`, with
`(eq:simpleboundK)`): `𝓛 = 𝒦 + (𝓛-𝒦)`, `|𝒦| ≤ C_K W^{-d} 𝒯̃^L`, `|𝓛-𝒦| ≺ q W^{-d} 𝒯̃^{K}` with
`q ≤ (W^{-d}B_{u,0})^{1/6}`, and the scale step `𝒯_u(K') = (W^{-d}B_{u,0})^{1/6} 𝒯_u(K)` give
`|𝓛| ≺ W^{-d} 𝒯̃^{K'}` at every time section. -/
theorem ST_next (hsz : sz.SizeTendsto) {E s t : ℕ → ℝ} (hst : ∀ n, s n ≤ t n) {Cd C_K : ℝ}
    (hCK : 0 < C_K) (Kf Kf' : ℕ → ℝ → ℝ)
    (hK2 : ∀ᶠ n in atTop, ∀ u D (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)), s n ≤ u →
      u ≤ t n → 0 ≤ D →
      ‖STKloop sz n (E n) u σ a‖ ≤ C_K * STprof sz n u D ((sz.L n : ℕ) : ℝ) (a 0) (a 1))
    (hrange : ∀ᶠ n in atTop, ∀ u, s n ≤ u → u ≤ t n → 0 ≤ Kf n u ∧ Kf n u ≤ Kf' n u)
    (hstep : ∀ᶠ n in atTop, ∀ u, s n ≤ u → u ≤ t n → (sz.Bctl n u) ^ (1 / 6 : ℝ) *
      tailT d (sz.L n) (sz.lam n) u (Kf n u) ≤ tailT d (sz.L n) (sz.lam n) u (Kf' n u))
    (hq : ∀ᶠ n in atTop, ∀ u, s n ≤ u → u ≤ t n →
      ((1 - s n) / (1 - u)) ^ Cd * (sz.Bctl n u) ^ (1 / 5 : ℝ) ≤ (sz.Bctl n u) ^ (1 / 6 : ℝ) ∧
        0 ≤ ((1 - s n) / (1 - u)) ^ Cd * (sz.Bctl n u) ^ (1 / 5 : ℝ) ∧
        (sz.Bctl n u) ^ (1 / 6 : ℝ) ≤ 1)
    (h : STSelfImp sz Cd E s t Kf) : STScaleInv sz E s t Kf' := by
  intro tt D hD
  have hsize := tendsto_size sz hsz
  -- the section form of `h`, restricted to the alternating charges
  have hcard : ∀ᶠ n in atTop, (Fintype.card (STLab sz n) : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ (3 : ℝ) := by
    filter_upwards [hsize.eventually (eventually_ge_atTop 4)] with n hn
    exact ST_card_lab_le sz n hn
  have hsec := ST_sections_of_PT sz (V := STLab sz) (s := s) (t := t)
    (fun n p ω => ‖Lloop sz n (E n) (p.1 : ℝ) p.2.1 p.2.2 ω -
      STKloop sz n (E n) (p.1 : ℝ) p.2.1 p.2.2‖)
    (fun n p _ => ((1 - s n) / (1 - (p.1 : ℝ))) ^ Cd * (sz.Bctl n (p.1 : ℝ)) ^ (1 / 5 : ℝ) *
      STprof sz n (p.1 : ℝ) D (Kf n (p.1 : ℝ)) (p.2.2 0) (p.2.2 1)) (by norm_num) hcard
    (h D hD) tt
  have hsec' : StochDomAt (Sizes.seqP sz) sz.size (U := STLab sz)
      (fun n (p : STLab sz n) ω => ‖Lloop sz n (E n) (tt n : ℝ) p.1 p.2 ω -
        STKloop sz n (E n) (tt n : ℝ) p.1 p.2‖)
      (fun n p _ => ((1 - s n) / (1 - (tt n : ℝ))) ^ Cd * (sz.Bctl n (tt n : ℝ)) ^ (1 / 5 : ℝ) *
        STprof sz n (tt n : ℝ) D (Kf n (tt n : ℝ)) (p.2 0) (p.2 1)) := hsec
  have hres := StochDomAt.precomp_param (V := fun n =>
      {σ : Fin 2 → Bool // σ 0 ≠ σ 1} × (Fin 2 → Zd d (sz.L n))) hsec'
    (fun n p => (p.1.1, p.2))
  have hnonneg : ∀ (n : ℕ) (p : {σ : Fin 2 → Bool // σ 0 ≠ σ 1} × (Fin 2 → Zd d (sz.L n)))
      (ω : sz.SeqΩ), 0 ≤ C_K * STprof sz n (tt n : ℝ) D ((sz.L n : ℕ) : ℝ) (p.2 0) (p.2 1) :=
    fun n p _ => mul_nonneg hCK.le (ST_STprof_pos sz n _ _ _ _ _).le
  have hKp : StochDomAt (Sizes.seqP sz) sz.size
      (U := fun n => {σ : Fin 2 → Bool // σ 0 ≠ σ 1} × (Fin 2 → Zd d (sz.L n)))
      (fun n p ω => ‖STKloop sz n (E n) (tt n : ℝ) p.1.1 p.2‖)
      (fun n p _ => C_K * STprof sz n (tt n : ℝ) D ((sz.L n : ℕ) : ℝ) (p.2 0) (p.2 1)) :=
    ST_prec_of_le_ev sz hnonneg (by
      filter_upwards [hK2] with n hn p ω
      exact hn (tt n : ℝ) D p.1.1 p.2 (tt n).2.1 (tt n).2.2 hD.le)
  have hsum := StochDomAt.add hsize hKp hres
  have hL : StochDomAt (Sizes.seqP sz) sz.size
      (U := fun n => {σ : Fin 2 → Bool // σ 0 ≠ σ 1} × (Fin 2 → Zd d (sz.L n)))
      (fun n p ω => ‖Lloop sz n (E n) (tt n : ℝ) p.1.1 p.2 ω‖)
      (fun n p ω => C_K * STprof sz n (tt n : ℝ) D ((sz.L n : ℕ) : ℝ) (p.2 0) (p.2 1) +
        ((1 - s n) / (1 - (tt n : ℝ))) ^ Cd * (sz.Bctl n (tt n : ℝ)) ^ (1 / 5 : ℝ) *
          STprof sz n (tt n : ℝ) D (Kf n (tt n : ℝ)) (p.2 0) (p.2 1)) := by
    refine StochDomAt.of_le_left (fun n p ω => ?_) hsum
    have := norm_add_le (STKloop sz n (E n) (tt n : ℝ) p.1.1 p.2)
      (Lloop sz n (E n) (tt n : ℝ) p.1.1 p.2 ω - STKloop sz n (E n) (tt n : ℝ) p.1.1 p.2)
    simpa [add_sub_cancel] using this
  -- the deterministic comparison
  have hcmp : ∀ᶠ n in atTop, ∀ (p : {σ : Fin 2 → Bool // σ 0 ≠ σ 1} × (Fin 2 → Zd d (sz.L n)))
      (ω : sz.SeqΩ),
      C_K * STprof sz n (tt n : ℝ) D ((sz.L n : ℕ) : ℝ) (p.2 0) (p.2 1) +
        ((1 - s n) / (1 - (tt n : ℝ))) ^ Cd * (sz.Bctl n (tt n : ℝ)) ^ (1 / 5 : ℝ) *
          STprof sz n (tt n : ℝ) D (Kf n (tt n : ℝ)) (p.2 0) (p.2 1) ≤
      (C_K + 1) * STprof sz n (tt n : ℝ) D (Kf' n (tt n : ℝ)) (p.2 0) (p.2 1) := by
    filter_upwards [hq, hrange, hstep] with n hn hrangen hstepn p ω
    obtain ⟨hq1, hq0, hq2⟩ := hn (tt n : ℝ) (tt n).2.1 (tt n).2.2
    obtain ⟨hK0, hKK⟩ := hrangen (tt n : ℝ) (tt n).2.1 (tt n).2.2
    have hW : (0 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := Nat.cast_nonneg _
    have hρ0 : (0 : ℝ) ≤ ((zdistInf d (sz.L n) (p.2 0 - p.2 1) : ℕ) : ℝ) := Nat.cast_nonneg _
    have hρL := ST_zdistInf_le sz n (p.2 0 - p.2 1)
    have hstep' := hstepn (tt n : ℝ) (tt n).2.1 (tt n).2.2
    have hsc := ST_tailW_scale_step (d := d) (L := sz.L n) (g := sz.lam n) (u := (tt n : ℝ))
      (K := Kf n (tt n : ℝ)) (K' := Kf' n (tt n : ℝ)) (W := ((sz.W n : ℕ) : ℝ)) (D := D)
      (e := (sz.Bctl n (tt n : ℝ)) ^ (1 / 6 : ℝ)) (ρ := ((zdistInf d (sz.L n) (p.2 0 - p.2 1) : ℕ) : ℝ))
      hW hK0 hKK (hq0.trans hq1) hq2 hstep' hρ0
    have hL' := ST_tailW_L_le (d := d) (L := sz.L n) (g := sz.lam n) (u := (tt n : ℝ))
      (ℓ := Kf' n (tt n : ℝ)) (W := ((sz.W n : ℕ) : ℝ)) (D := D)
      (ρ := ((zdistInf d (sz.L n) (p.2 0 - p.2 1) : ℕ) : ℝ)) (hK0.trans hKK) hρ0 hρL
    have hWd : 0 ≤ (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ := inv_nonneg.mpr (pow_nonneg hW d)
    unfold STprof
    have hP1 : 0 ≤ tailW d (sz.L n) (sz.lam n) (tt n : ℝ) (Kf n (tt n : ℝ)) ((sz.W n : ℕ) : ℝ) D
        ((zdistInf d (sz.L n) (p.2 0 - p.2 1) : ℕ) : ℝ) := (tailW_pos (by
          exact_mod_cast sz.W_pos n) _).le
    have e1 : ((1 - s n) / (1 - (tt n : ℝ))) ^ Cd * (sz.Bctl n (tt n : ℝ)) ^ (1 / 5 : ℝ) *
        tailW d (sz.L n) (sz.lam n) (tt n : ℝ) (Kf n (tt n : ℝ)) ((sz.W n : ℕ) : ℝ) D
          ((zdistInf d (sz.L n) (p.2 0 - p.2 1) : ℕ) : ℝ) ≤
        tailW d (sz.L n) (sz.lam n) (tt n : ℝ) (Kf' n (tt n : ℝ)) ((sz.W n : ℕ) : ℝ) D
          ((zdistInf d (sz.L n) (p.2 0 - p.2 1) : ℕ) : ℝ) :=
      (mul_le_mul_of_nonneg_right hq1 hP1).trans hsc
    nlinarith [mul_le_mul_of_nonneg_left hL' (mul_nonneg hCK.le hWd),
      mul_le_mul_of_nonneg_left e1 hWd]
  -- assemble: `ξ ≺ C_K P^L + q P^{Kf} ≤ (C_K + 1) P^{Kf'} ≺ P^{Kf'}`
  have hmono : StochDomAt (Sizes.seqP sz) sz.size
      (U := fun n => {σ : Fin 2 → Bool // σ 0 ≠ σ 1} × (Fin 2 → Zd d (sz.L n)))
      (fun n p ω => ‖Lloop sz n (E n) (tt n : ℝ) p.1.1 p.2 ω‖)
      (fun n p _ => (C_K + 1) * STprof sz n (tt n : ℝ) D (Kf' n (tt n : ℝ)) (p.2 0) (p.2 1)) :=
    StochDomAt.of_subset hL fun τ hτ => ⟨τ, hτ, hcmp.mono fun n hn ω hω => by
      obtain ⟨p, hp⟩ := hω
      exact ⟨p, lt_of_le_of_lt (mul_le_mul_of_nonneg_left (hn p ω)
        (Real.rpow_nonneg (Nat.cast_nonneg _) _)) hp⟩⟩
  have hpos : ∀ (n : ℕ) (p : {σ : Fin 2 → Bool // σ 0 ≠ σ 1} × (Fin 2 → Zd d (sz.L n)))
      (ω : sz.SeqΩ), 0 ≤ STprof sz n (tt n : ℝ) D (Kf' n (tt n : ℝ)) (p.2 0) (p.2 1) :=
    fun n p _ => (ST_STprof_pos sz n _ _ _ _ _).le
  have hcst := StochDomAt.const_mul_left (P := Sizes.seqP sz) hsize (show 0 ≤ C_K + 1 by linarith)
    hpos (StochDomAt.refl (P := Sizes.seqP sz) hsize hpos)
  exact StochDomAt.trans hsize hmono hcst

/-- **The last scale gives `(Eq:Gdecay_w)`** (`3_5:575–577`): if for every `D > 0` the self-improving
bound holds at a family `Kf` with `𝒯_u(K_u) ≤ W^{-D}` (eventually), then `𝒯̃^{K}_{u,D} = max(𝒯_u, W^{-D})`
and `q W^{-d} 𝒯̃ ≤ q W^{-d} 𝒯 + W^{-D}` (`q W^{-d} ≤ 1`): the per-time `STStep2DecayPT`. -/
theorem ST_decay_of_final {E s t : ℕ → ℝ} {Cd : ℝ}
    (h : ∀ D : ℝ, 0 < D → ∃ Kf : ℕ → ℝ → ℝ, STSelfImp sz Cd E s t Kf ∧
      ∀ᶠ n in atTop, ∀ u, s n ≤ u → u ≤ t n → 0 ≤ Kf n u ∧
        (tailT d (sz.L n) (sz.lam n) u (Kf n u) ≤ ((sz.W n : ℕ) : ℝ) ^ (-D) ∨
          ((sz.L n : ℕ) : ℝ) ≤ Kf n u))
    (hqW : ∀ᶠ n in atTop, ∀ u, s n ≤ u → u ≤ t n →
      ((1 - s n) / (1 - u)) ^ Cd * (sz.Bctl n u) ^ (1 / 5 : ℝ) *
        (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ 1)
    (hq0 : ∀ᶠ n in atTop, ∀ u, s n ≤ u → u ≤ t n →
      0 ≤ ((1 - s n) / (1 - u)) ^ Cd * (sz.Bctl n u) ^ (1 / 5 : ℝ)) :
    STStep2DecayPT sz Cd E s t := by
  intro D hD
  obtain ⟨Kf, hself, hfin⟩ := h D hD
  refine ST_PT_mono_eventually sz ?_ (hself D hD)
  filter_upwards [hfin, hqW, hq0] with n hn hqn hq0n
  intro p ω
  obtain ⟨⟨u, hsu, hut⟩, σ, a⟩ := p
  obtain ⟨hK0, hT⟩ := hn u hsu hut
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hρ0 : (0 : ℝ) ≤ ((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) := Nat.cast_nonneg _
  have hfinal : tailW d (sz.L n) (sz.lam n) u (Kf n u) ((sz.W n : ℕ) : ℝ) D
      ((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) =
      max (tailT d (sz.L n) (sz.lam n) u ((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ))
        (((sz.W n : ℕ) : ℝ) ^ (-D)) := by
    rcases hT with hT | hL
    · exact ST_tailW_final (d := d) (L := sz.L n) (g := sz.lam n) (u := u) (K := Kf n u)
        (W := ((sz.W n : ℕ) : ℝ)) (D := D) (ρ := ((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ))
        hK0 hT
    · unfold tailW
      have hρL := ST_zdistInf_le sz n (a 0 - a 1)
      rw [min_eq_left (hρL.trans hL)]
  have hTnn := tailT_nonneg (d := d) (L := sz.L n) (g := sz.lam n) (t := u) hρ0
  have hWD : 0 ≤ ((sz.W n : ℕ) : ℝ) ^ (-D) := Real.rpow_nonneg hW.le _
  have hmax : max (tailT d (sz.L n) (sz.lam n) u ((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ))
      (((sz.W n : ℕ) : ℝ) ^ (-D)) ≤
      tailT d (sz.L n) (sz.lam n) u ((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) +
        ((sz.W n : ℕ) : ℝ) ^ (-D) :=
    max_le (by linarith) (by linarith)
  have hWd : 0 ≤ (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ := inv_nonneg.mpr (pow_nonneg hW.le d)
  -- `T(ρ) = B_{u,ρ} exp(-(ρ/ℓ_u)^{1/2})`
  have hTeq : tailT d (sz.L n) (sz.lam n) u ((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) =
      Bparam d (sz.L n) (sz.lam n) u (zdistInf d (sz.L n) (a 0 - a 1)) *
        Real.exp (-(((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) /
          ellT (sz.L n) (sz.lam n) u) ^ (1 / 2 : ℝ)) := by
    unfold tailT
    rw [BparamR_natCast, Real.sqrt_eq_rpow]
  have hq := hq0n u hsu hut
  have hqW' := hqn u hsu hut
  show ((1 - s n) / (1 - u)) ^ Cd * (sz.Bctl n u) ^ (1 / 5 : ℝ) *
      STprof sz n u D (Kf n u) (a 0) (a 1) ≤
    ((1 - s n) / (1 - u)) ^ Cd * (sz.Bctl n u) ^ (1 / 5 : ℝ) *
        STWB sz n u (zdistInf d (sz.L n) (a 0 - a 1)) *
        Real.exp (-(((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) /
          ellT (sz.L n) (sz.lam n) u) ^ (1 / 2 : ℝ)) + ((sz.W n : ℕ) : ℝ) ^ (-D)
  unfold STprof STWB
  rw [hfinal]
  set q := ((1 - s n) / (1 - u)) ^ Cd * (sz.Bctl n u) ^ (1 / 5 : ℝ) with hqdef
  set Wd := (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ with hWddef
  have e1 : q * (Wd * max (tailT d (sz.L n) (sz.lam n) u
      ((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ)) (((sz.W n : ℕ) : ℝ) ^ (-D))) ≤
      q * (Wd * (tailT d (sz.L n) (sz.lam n) u ((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) +
        ((sz.W n : ℕ) : ℝ) ^ (-D))) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hmax hWd) hq
  have e2 : q * (Wd * (tailT d (sz.L n) (sz.lam n) u
      ((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) + ((sz.W n : ℕ) : ℝ) ^ (-D))) =
      q * (Wd * Bparam d (sz.L n) (sz.lam n) u (zdistInf d (sz.L n) (a 0 - a 1))) *
        Real.exp (-(((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) /
          ellT (sz.L n) (sz.lam n) u) ^ (1 / 2 : ℝ)) + (q * Wd) * ((sz.W n : ℕ) : ℝ) ^ (-D) := by
    rw [hTeq]; ring
  have e3 : (q * Wd) * ((sz.W n : ℕ) : ℝ) ^ (-D) ≤ ((sz.W n : ℕ) : ℝ) ^ (-D) := by
    nlinarith [mul_le_mul_of_nonneg_right hqW' hWD]
  linarith

end Iter

end RBM.Gauss.Sizes

namespace RBM.Gauss.Sizes

open MeasureTheory Filter RBM RBM.Gauss RBM.Gauss.Sizes RBM.Path

section Main

variable {d : ℕ} (sz : Sizes d)

set_option maxHeartbeats 3200000 in
/-- **One self-improving step at a time section** (`(eq:Gronwall_dervJuD)`, `3_5:529`, per time):
from the premise `Inv(Kf)` (`(eq:LW_assm_exp)` at the scale family `Kf`, every time section of
`[s,t]`) and the pins `lem:newKLK`, `lem: EWGn2_N`, `lem: EMn2_N`, `Sol_CalL`+`lem:DIfREP`:
`|(𝓛-𝒦)^{(2)}_{u,σ,a}| ≺ ((1-s)/(1-u))^{C_d} (W^{-d}B_{u,0})^{1/5} W^{-d} 𝒯̃^{K_u}_{u,D}(|a₁-a₂|)`
at `u = tt n`, with `C_d = 3C + 1`.  The proof is the stopped Grönwall bootstrap of
`ST_good_engine` on the good event of `ST_good_prob`, transferred to the model at `t_n`. -/
theorem ST_selfImprove_section (hLWT : STLWT d) (hEMe : STEMn2Exp d) (hd : 0 < d)
    {κ ε 𝔡 𝔠 : ℝ} (hκ : 0 < κ) (hε : 0 < ε) (h𝔡 : 0 < 𝔡) {z : ℕ → ℂ}
    (hflow : STFlow sz κ ε 𝔠 𝔡 z) {s t : ℕ → ℝ} (hs : ∀ n, 0 ≤ s n)
    (htT : ∀ n, t n ≤ lemT (z n))
    {C δ₀ C₀ 𝔠d : ℝ} (hC : 0 < C) (hδ₀ : 0 < δ₀) (hC₀ : 0 ≤ C₀)
    (hnew : STNewKLKAt d κ 𝔡 C δ₀) (hmart : STGridMartAt d C₀)
    (h𝔠d : 0 < 𝔠d) (h3 : (3 * C + 1) * 𝔠d ≤ 1 / 60)
    (hDec : STDecay sz (STflowE z) s) (hCon : STConStInd sz 𝔠d s t)
    (hS1W : STStep1Weak sz (STflowE z) s t) {cB c : ℝ} (hcB : 0 < cB) (hc : 0 < c)
    (hBd : ∀ᶠ n in atTop, ∀ u : ℝ, 0 ≤ u → u ≤ t n →
      cB * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ sz.Bctl n u ∧ sz.Bctl n u ≤ ((sz.size n : ℕ) : ℝ) ^ (-c))
    (Kf : ℕ → ℝ → ℝ) (hKok : STScaleOk sz s t Kf) (hinv : STScaleInv sz (STflowE z) s t Kf)
    (tt : ∀ n, TimeIcc s t n) (D : ℝ) (hD : 0 < D) :
    sz.Prec (U := fun n => STLab sz n)
      (fun n i ω => ‖Lloop sz n (STflowE z n) (tt n : ℝ) i.1 i.2 ω -
        STKloop sz n (STflowE z n) (tt n : ℝ) i.1 i.2‖)
      (fun n i _ => ((1 - s n) / (1 - (tt n : ℝ))) ^ (3 * C + 1) *
        (sz.Bctl n (tt n : ℝ)) ^ (1 / 5 : ℝ) *
        STprof sz n (tt n : ℝ) D (Kf n (tt n : ℝ)) (i.2 0) (i.2 1)) := by
  classical
  intro τ hτ D' hD'
  have hsz : sz.SizeTendsto := hflow.1.2.2.1
  have hsize := tendsto_size sz hsz
  have h𝔠 : 0 < 𝔠 := hflow.1.1
  have hband : sz.Bandwidth 𝔠 := hflow.1.2.2.2.1
  have hWO : sz.WO 𝔡 := hflow.1.2.2.2.2
  -- the end of the grid is the section
  obtain ⟨T, hTdef⟩ : ∃ T : ℕ → ℝ, T = fun n => (tt n : ℝ) := ⟨_, rfl⟩
  have hsT : ∀ n, s n ≤ T n := fun n => by rw [hTdef]; exact (tt n).2.1
  have hTt : ∀ n, T n ≤ t n := fun n => by rw [hTdef]; exact (tt n).2.2
  have hTT : ∀ n, T n ≤ lemT (z n) := fun n => (hTt n).trans (htT n)
  have hT1 : ∀ n, T n < 1 := fun n =>
    lt_of_le_of_lt (hTT n) (lemT_lt_one (ST_flow_im_pos sz hflow n))
  have hT0 : ∀ n, 0 ≤ T n := fun n => (hs n).trans (hsT n)
  have hTD : ∀ n, T n = (tt n : ℝ) := fun n => by rw [hTdef]
  -- the loss `ε₁`, the floors
  obtain ⟨ε₁, hε₁def⟩ : ∃ ε₁ : ℝ, ε₁ = min (τ / 6) (c / 400) := ⟨_, rfl⟩
  have hε₁pos : 0 < ε₁ := by rw [hε₁def]; exact lt_min (by linarith) (by linarith)
  have hε₁τ : ε₁ ≤ τ / 6 := by rw [hε₁def]; exact min_le_left _ _
  have hε₁c : ε₁ ≤ c / 400 := by rw [hε₁def]; exact min_le_right _ _
  obtain ⟨Dm, hDmdef⟩ : ∃ Dm : ℝ, Dm = D' + 2 * D + 10 := ⟨_, rfl⟩
  have hDm1 : D' + 1 + 3 ≤ Dm := by rw [hDmdef]; linarith
  have hDm2 : 2 * D + 6 ≤ Dm := by rw [hDmdef]; linarith
  have hDmpos : 0 < Dm := by rw [hDmdef]; linarith
  -- the grid size and the martingale decomposition from the pin
  obtain ⟨CK, hCK0, hCK⟩ := hmart κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow s T hs hsT hTT Dm hDmpos
  obtain ⟨CK', hCK'def⟩ : ∃ CK' : ℝ, CK' = max CK (2 * (C₀ + D + 3)) := ⟨_, rfl⟩
  have hCK'0 : 0 ≤ CK' := by rw [hCK'def]; exact hCK0.trans (le_max_left _ _)
  have hCK'1 : CK ≤ CK' := by rw [hCK'def]; exact le_max_left _ _
  have hCK'2 : 2 * (C₀ + D + 3) ≤ CK' := by rw [hCK'def]; exact le_max_right _ _
  obtain ⟨K, hKdef⟩ : ∃ K : ℕ → ℕ, K = fun n => ⌈((sz.size n : ℕ) : ℝ) ^ CK'⌉₊ := ⟨_, rfl⟩
  have hKn : ∀ n, K n = ⌈((sz.size n : ℕ) : ℝ) ^ CK'⌉₊ := fun n => by rw [hKdef]
  have hK0 : ∀ n, K n ≠ 0 := fun n => by
    rw [hKn n]
    have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
    exact (Nat.ceil_pos.2 (Real.rpow_pos_of_pos hN0 _)).ne'
  have hKbig' : ∀ n, ((sz.size n : ℕ) : ℝ) ^ CK' ≤ (K n : ℝ) := fun n => by
    rw [hKn n]; exact Nat.le_ceil _
  have hKbig : ∀ᶠ n in atTop, ((sz.size n : ℕ) : ℝ) ^ CK ≤ (K n : ℝ) := by
    filter_upwards [hsize.eventually (eventually_ge_atTop 1)] with n hn
    have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast hn
    exact (Real.rpow_le_rpow_of_exponent_le hN1 hCK'1).trans (hKbig' n)
  obtain ⟨Mart, Rem, hident, hrem0, hmart0⟩ := hCK K hK0 hKbig
  -- the parameters of the good event: `Λ = q = 2 N^{ε₁}`, `a₀ = r₀ = Λ b_s^{1/5}`, `ρ₁ = a₀²`
  obtain ⟨X, hXdef⟩ : ∃ X : ℕ → ℝ, X = fun n => ((sz.size n : ℕ) : ℝ) ^ ε₁ := ⟨_, rfl⟩
  have hX1 : ∀ n, 1 ≤ X n := fun n => by
    rw [hXdef]
    exact Real.one_le_rpow (by exact_mod_cast sz.one_le_size n) hε₁pos.le
  obtain ⟨Λ, hΛdef⟩ : ∃ Λ : ℕ → ℝ, Λ = fun n => 2 * X n := ⟨_, rfl⟩
  have hΛ1 : ∀ n, 1 ≤ Λ n := fun n => by rw [hΛdef]; have := hX1 n; simp only; linarith
  have hΛX : ∀ n, ((sz.size n : ℕ) : ℝ) ^ ε₁ ≤ Λ n := fun n => by
    rw [hΛdef]; have := hX1 n; rw [hXdef] at this ⊢; simp only at this ⊢; linarith
  have hΛX2 : ∀ n, 2 * ((sz.size n : ℕ) : ℝ) ^ ε₁ ≤ Λ n := fun n => by
    rw [hΛdef, hXdef]
  obtain ⟨a₀, ha₀def⟩ : ∃ a₀ : ℕ → ℝ, a₀ = fun n => Λ n * (sz.Bctl n (s n)) ^ (1 / 5 : ℝ) :=
    ⟨_, rfl⟩
  obtain ⟨ρ₁, hρ₁def⟩ : ∃ ρ₁ : ℕ → ℝ,
      ρ₁ = fun n => (Λ n * (sz.Bctl n (s n)) ^ (1 / 5 : ℝ)) ^ 2 := ⟨_, rfl⟩
  -- cardinalities of the label sets
  have hN4 : ∀ᶠ n in atTop, 4 ≤ sz.size n := hsize.eventually (eventually_ge_atTop 4)
  have hcardIdx := ST_hcard sz
    (V := fun n => Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n)) hsize hCK'0 K hKn
    (by filter_upwards [hN4] with n hn
        exact ST_card_idx_prod_le sz n (by omega))
  have hcardLab3 : ∀ᶠ n in atTop,
      (Fintype.card (STLab sz n) : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ (3 : ℝ) := by
    filter_upwards [hN4] with n hn using ST_card_lab_le sz n hn
  have hcardLab := ST_hcard sz (V := fun n => STLab sz n) hsize hCK'0 K hKn (by
    filter_upwards [hcardLab3, hN4] with n hn hN
    refine hn.trans (Real.rpow_le_rpow_of_exponent_le ?_ (by norm_num))
    exact_mod_cast (by omega : 1 ≤ sz.size n))
  have hcardF2 := ST_hcard sz (V := fun n => Fin 2 × STLab sz n) hsize hCK'0 K hKn (by
    filter_upwards [hN4] with n hn using ST_card_fin2_lab_le sz n hn)
  -- polynomial floors
  have hNcB : ∀ᶠ n in atTop, ((sz.size n : ℕ) : ℝ) ^ (-1 : ℝ) ≤ cB ^ (1 / 5 : ℝ) :=
    ST_size_pow_small sz hsize (by norm_num) (Real.rpow_pos_of_pos hcB _)
  have hbP : ∀ᶠ n in atTop, ∀ u, s n ≤ u → u ≤ t n → ∀ (ℓ : ℝ) (a b : Zd d (sz.L n)),
      ((sz.size n : ℕ) : ℝ) ^ (-(D + 3)) ≤ (sz.Bctl n u) ^ (1 / 5 : ℝ) * STprof sz n u D ℓ a b := by
    filter_upwards [hBd, hNcB] with n hn hN u hsu hut ℓ a b
    exact ST_bP_lower sz hd n hcB hD.le (hn u ((hs n).trans hsu) hut).1 hN a b
  -- (E1) the weak law
  have hsmallE1 : ∀ᶠ n in atTop, ∀ u, s n ≤ u → u ≤ t n →
      ((sz.size n : ℕ) : ℝ) ^ ε₁ * (sz.Bctl n u) ^ (1 / 4 : ℝ) ≤ δ₀ := by
    filter_upwards [hBd, ST_size_pow_small sz hsize (a := ε₁ - c / 4) (δ := δ₀)
      (by linarith) hδ₀] with n hn hsm u hsu hut
    have hb := (hn u ((hs n).trans hsu) hut).2
    have hN0 : (0 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := Nat.cast_nonneg _
    have hb0 : 0 ≤ sz.Bctl n u := ((mul_nonneg hcB.le (inv_nonneg.mpr (pow_nonneg
      (Nat.cast_nonneg _) d)))).trans (hn u ((hs n).trans hsu) hut).1
    calc ((sz.size n : ℕ) : ℝ) ^ ε₁ * (sz.Bctl n u) ^ (1 / 4 : ℝ)
        ≤ ((sz.size n : ℕ) : ℝ) ^ ε₁ * (((sz.size n : ℕ) : ℝ) ^ (-c)) ^ (1 / 4 : ℝ) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hb0 hb (by norm_num))
            (Real.rpow_nonneg hN0 _)
      _ = ((sz.size n : ℕ) : ℝ) ^ (ε₁ - c / 4) := by
          rw [← Real.rpow_mul hN0, ← Real.rpow_add' hN0 (by linarith)]; congr 1; ring
      _ ≤ δ₀ := hsm
  have hE1 := ST_event_weak sz (κ := κ) (ε := ε) (𝔡 := 𝔡) (𝔠 := 𝔠) (z := z) (s := s) (t := t)
    (T := T) K hs hsT hTt hK0 (by linarith : (0 : ℝ) ≤ CK' + 5) hcardIdx hS1W hε₁pos hsmallE1
  have hst' : ∀ n, s n ≤ t n := fun n => (hsT n).trans (hTt n)
  have hKcap : ∀ᶠ n in atTop, ∀ u, s n ≤ u → u ≤ t n → 0 ≤ Kf n u ∧
      Kf n u ≤ (Real.log ((sz.W n : ℕ) : ℝ)) ^ 10 * ellT (sz.L n) (sz.lam n) u := by
    filter_upwards [hKok.1] with n hn u h1 h2
    exact ⟨(hn u h1 h2).1, (hn u h1 h2).2.2⟩
  -- (E2) the initial value
  obtain ⟨Di, hDidef⟩ : ∃ Di : ℝ, Di = (D + 3) / 𝔠 := ⟨_, rfl⟩
  have hDipos : 0 < Di := by rw [hDidef]; positivity
  have hWDi : ∀ᶠ n in atTop, ((sz.W n : ℕ) : ℝ) ^ (-Di) ≤ ((sz.size n : ℕ) : ℝ) ^ (-(D + 3)) := by
    filter_upwards [hband] with n hn
    have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
    have hNc : 0 < ((sz.size n : ℕ) : ℝ) ^ 𝔠 := Real.rpow_pos_of_pos hN0 _
    calc ((sz.W n : ℕ) : ℝ) ^ (-Di) ≤ (((sz.size n : ℕ) : ℝ) ^ 𝔠) ^ (-Di) :=
          Real.rpow_le_rpow_of_nonpos hNc hn (by linarith)
      _ = ((sz.size n : ℕ) : ℝ) ^ (-(D + 3)) := by
          rw [← Real.rpow_mul hN0.le]; congr 1; rw [hDidef]; field_simp
  have hcmp : ∀ᶠ n in atTop, ∀ i : STLab sz n, ((sz.size n : ℕ) : ℝ) ^ ε₁ *
      ((sz.Bctl n (s n)) ^ (1 / 5 : ℝ) *
        STWB sz n (s n) (zdistInf d (sz.L n) (i.2 0 - i.2 1)) *
        Real.exp (-(((zdistInf d (sz.L n) (i.2 0 - i.2 1) : ℕ) : ℝ) /
          ellT (sz.L n) (sz.lam n) (s n)) ^ (1 / 2 : ℝ)) +
        ((sz.W n : ℕ) : ℝ) ^ (-Di)) ≤
      a₀ n * STprof sz n (s n) D (Kf n (s n)) (i.2 0) (i.2 1) := by
    filter_upwards [hBd, hbP, hWDi, hKok.1] with n hn hP hW hKc i
    have hKs := (hKc (s n) le_rfl (hst' n)).1
    have hbs0 : 0 ≤ sz.Bctl n (s n) := (mul_nonneg hcB.le (inv_nonneg.mpr (pow_nonneg
      (Nat.cast_nonneg _) d))).trans (hn (s n) (hs n) (hst' n)).1
    have h := ST_init_cmp sz n (u := s n) (D := D) (ℓ := Kf n (s n)) (Di := Di)
      (X := ((sz.size n : ℕ) : ℝ) ^ ε₁) (Real.rpow_nonneg (Nat.cast_nonneg _) _) hKs hbs0 i
      (hW.trans (hP (s n) le_rfl (hst' n) _ _ _))
    rw [ha₀def, hΛdef, hXdef]
    exact h
  have hE2 := ST_event_init sz (z := z) (s := s) (T := T) K hs hsT hK0 hDec (C₁ := 3)
    (by norm_num) hcardLab3 hε₁pos hDipos D Kf (a₀ := a₀) hcmp
  -- (E3), (E4) the light-weight term and the quadratic variation
  have hE3 := ST_event_lw sz hLWT hEMe hd hκ hε h𝔡 hflow K hs hsT hTt hK0 htT hS1W hcB hc hBd Kf
    hKcap hinv (C₁ := CK' + 5) (by linarith) hcardLab hε₁pos hΛX D hD
  have hE4 := ST_event_mg sz hLWT hEMe hd hκ hε h𝔡 hflow K hs hsT hTt hK0 htT hS1W hcB hc hBd Kf
    hKcap hinv (C₁ := CK' + 5) (by linarith) hcardF2 hε₁pos hΛX2 D hD
  -- the floors of the martingale event and of the remainder
  have hρ : ∀ᶠ n in atTop, ∀ i : STLab sz n, ((sz.size n : ℕ) : ℝ) ^ (-Dm) ≤ ρ₁ n *
      STprof sz n (gridTime s T K n 0) D (Kf n (gridTime s T K n 0)) (i.2 0) (i.2 1) ^ 2 := by
    filter_upwards [hbP, hsize.eventually (eventually_ge_atTop 1)] with n hP hN1 i
    have hN1' : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast hN1
    rw [ST_gridTime_zero]
    have h1 := ST_floor_sq (q := Λ n) hN1' (hΛ1 n) (hP (s n) le_rfl (hst' n) (Kf n (s n))
      (i.2 0) (i.2 1)) hDm2
    rw [hρ₁def]
    refine h1.trans (le_of_eq ?_)
    simp only
    ring
  have hrem : ∀ᶠ n in atTop, ∀ i : STLab sz n, ∀ᵐ ω ∂(pathP sz), ∀ k, k ≤ K n →
      ‖Rem n i k ω‖ ≤ a₀ n *
        STprof sz n (gridTime s T K n 0) D (Kf n (gridTime s T K n 0)) (i.2 0) (i.2 1) := by
    filter_upwards [hrem0, hbP, hsize.eventually (eventually_ge_atTop 1)] with n hr hP hN1 i
    have hN1' : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast hN1
    have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
    rw [ST_gridTime_zero]
    refine (hr i).mono fun ω hω k hk => (hω k hk).trans ?_
    have hts : T n - s n ≤ 1 := by have := hT1 n; have := hs n; linarith
    have hsq := ST_sqrt_gridStep_le s T K n hN1' hts (hKbig' n)
    have hP0 := hP (s n) le_rfl (hst' n) (Kf n (s n)) (i.2 0) (i.2 1)
    have hb5 : 0 ≤ (sz.Bctl n (s n)) ^ (1 / 5 : ℝ) * STprof sz n (s n) D (Kf n (s n)) (i.2 0) (i.2 1) :=
      (Real.rpow_nonneg hN0.le _).trans hP0
    calc ((sz.size n : ℕ) : ℝ) ^ C₀ * Real.sqrt (gridStep s T K n)
        ≤ ((sz.size n : ℕ) : ℝ) ^ C₀ * ((sz.size n : ℕ) : ℝ) ^ (-CK' / 2) :=
          mul_le_mul_of_nonneg_left hsq (Real.rpow_nonneg hN0.le _)
      _ = ((sz.size n : ℕ) : ℝ) ^ (C₀ + -CK' / 2) := (Real.rpow_add hN0 _ _).symm
      _ ≤ ((sz.size n : ℕ) : ℝ) ^ (-(D + 3)) :=
          Real.rpow_le_rpow_of_exponent_le hN1' (by linarith)
      _ ≤ (sz.Bctl n (s n)) ^ (1 / 5 : ℝ) * STprof sz n (s n) D (Kf n (s n)) (i.2 0) (i.2 1) := hP0
      _ ≤ Λ n * ((sz.Bctl n (s n)) ^ (1 / 5 : ℝ) *
            STprof sz n (s n) D (Kf n (s n)) (i.2 0) (i.2 1)) :=
          le_mul_of_one_le_left hb5 (hΛ1 n)
      _ = a₀ n * STprof sz n (s n) D (Kf n (s n)) (i.2 0) (i.2 1) := by
          rw [ha₀def]; simp only; ring
  have hgp := ST_good_prob sz hsize s T K (STflowE z) D Kf (δ₀ := δ₀) (Λ := Λ) (a₀ := a₀)
    (r₀ := a₀) (ρ₁ := ρ₁) Mart Rem hE1 hE2 hE3 hE4
    (fun n => ST_gridStep_nonneg s T K n (hsT n)) (D' := D') (Dm := Dm) (ε₁ := ε₁) hD' hDm1
    (hmart0 ε₁ hε₁pos) hΛX hρ hident hrem hcardLab3
  -- the size constants of the closure and of the final comparison
  obtain ⟨cstar, hcstardef⟩ : ∃ cstar : ℝ, cstar = 3 + 3 * (Real.sqrt κ / 2)⁻¹ := ⟨_, rfl⟩
  have hcstar0 : 0 < cstar := by
    rw [hcstardef]; have := Real.sqrt_pos.2 hκ; positivity
  have hP1 : ∀ᶠ n in atTop, 12 * cstar * ((sz.size n : ℕ) : ℝ) ^ (3 * ε₁ - c / 60) < 1 := by
    filter_upwards [ST_size_pow_small sz hsize (a := 3 * ε₁ - c / 60) (δ := 1 / (24 * cstar))
      (by linarith) (by positivity)] with n hn
    calc 12 * cstar * ((sz.size n : ℕ) : ℝ) ^ (3 * ε₁ - c / 60)
        ≤ 12 * cstar * (1 / (24 * cstar)) := mul_le_mul_of_nonneg_left hn (by positivity)
      _ = 1 / 2 := by field_simp; norm_num
      _ < 1 := by norm_num
  have hP2 : ∀ᶠ n in atTop, 12 * cstar * ((sz.size n : ℕ) : ℝ) ^ (3 * ε₁) ≤
      ((sz.size n : ℕ) : ℝ) ^ τ := by
    filter_upwards [ST_size_pow_big sz hsize (a := τ - 3 * ε₁) (M := 12 * cstar)
      (by linarith), hsize.eventually (eventually_ge_atTop 1)] with n hn hN1
    have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by exact_mod_cast hN1
    calc 12 * cstar * ((sz.size n : ℕ) : ℝ) ^ (3 * ε₁)
        ≤ ((sz.size n : ℕ) : ℝ) ^ (τ - 3 * ε₁) * ((sz.size n : ℕ) : ℝ) ^ (3 * ε₁) :=
          mul_le_mul_of_nonneg_right hn (Real.rpow_nonneg hN0.le _)
      _ = ((sz.size n : ℕ) : ℝ) ^ τ := by rw [← Real.rpow_add hN0]; congr 1; ring
  filter_upwards [hgp, hBd, hP1, hP2, hKok.1, hKok.2, hCon, hWO,
    hsize.eventually (eventually_ge_atTop 1)] with n hgpn hbdn hP1n hP2n hKc hKmono hconn hwon hN1
  have hN1' : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast hN1
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
  have him := ST_flow_im_pos sz hflow n
  have hmI : 0 < (mE (STflowE z n)).im := mE_im_pos (abs_lemE_lt_two him)
  have hE : |STflowE z n| ≤ 2 - κ := (abs_lemE_le him).trans (hflow.2 n).1
  have hlam : 0 < sz.lam n :=
    lt_of_lt_of_le (Real.rpow_pos_of_pos (by exact_mod_cast sz.W_pos n) _) hwon.1
  have hlam' : sz.lam n ≤ 𝔡⁻¹ := hwon.2
  have hcstar : 3 + 3 * ((mE (STflowE z n)).im)⁻¹ ≤ cstar := by
    rw [hcstardef]; exact ST_cstar_le hκ hE
  have hc₁0 : 0 ≤ 3 + 3 * ((mE (STflowE z n)).im)⁻¹ := by positivity
  have hlt1 : ∀ u, u ≤ t n → u < 1 := fun u hu =>
    lt_of_le_of_lt (hu.trans (htT n)) (lemT_lt_one him)
  have hbpos : ∀ u, u ≤ t n → 0 < sz.Bctl n u := fun u hu => STBctl_pos sz n (hlt1 u hu)
  have hbtn := hbdn (t n) ((hs n).trans (hst' n)) le_rfl
  have hbt1 : sz.Bctl n (t n) ≤ 1 :=
    hbtn.2.trans (Real.rpow_le_one_of_one_le_of_nonpos hN1' (by linarith))
  have hbT := hbdn (T n) (hT0 n) (hTt n)
  have hb1 : sz.Bctl n (T n) ≤ 1 :=
    hbT.2.trans (Real.rpow_le_one_of_one_le_of_nonpos hN1' (by linarith))
  -- the closure `hΛq`
  have hΛq : (3 + 3 * ((mE (STflowE z n)).im)⁻¹) * (Λ n) ^ 2 * (1 + Λ n) *
      (sz.Bctl n (t n)) ^ (1 / 60 : ℝ) < 1 := by
    have hX := hX1 n
    have hΛe : Λ n = 2 * X n := by rw [hΛdef]
    have h12 : (Λ n) ^ 2 * (1 + Λ n) ≤ 12 * (X n) ^ 3 := by
      rw [hΛe]; nlinarith [mul_nonneg (sub_nonneg.2 hX) (sq_nonneg (X n))]
    have hXe : (X n) ^ 3 = ((sz.size n : ℕ) : ℝ) ^ (3 * ε₁) := by
      rw [hXdef]; simp only
      rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; congr 1; push_cast; ring
    have hbt60 : (sz.Bctl n (t n)) ^ (1 / 60 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ (-c / 60) := by
      calc (sz.Bctl n (t n)) ^ (1 / 60 : ℝ)
          ≤ (((sz.size n : ℕ) : ℝ) ^ (-c)) ^ (1 / 60 : ℝ) :=
            Real.rpow_le_rpow (hbpos _ le_rfl).le hbtn.2 (by norm_num)
        _ = ((sz.size n : ℕ) : ℝ) ^ (-c / 60) := by
            rw [← Real.rpow_mul hN0.le]; congr 1; ring
    have hΛ0 : 0 ≤ (Λ n) ^ 2 * (1 + Λ n) := by have := hΛ1 n; positivity
    calc (3 + 3 * ((mE (STflowE z n)).im)⁻¹) * (Λ n) ^ 2 * (1 + Λ n) *
          (sz.Bctl n (t n)) ^ (1 / 60 : ℝ)
        = (3 + 3 * ((mE (STflowE z n)).im)⁻¹) * ((Λ n) ^ 2 * (1 + Λ n)) *
          (sz.Bctl n (t n)) ^ (1 / 60 : ℝ) := by ring
      _ ≤ cstar * (12 * ((sz.size n : ℕ) : ℝ) ^ (3 * ε₁)) *
          ((sz.size n : ℕ) : ℝ) ^ (-c / 60) := by
          refine mul_le_mul (mul_le_mul hcstar (by rw [← hXe]; exact h12) hΛ0 hcstar0.le)
            hbt60 (Real.rpow_nonneg (hbpos _ le_rfl).le _) (by positivity)
      _ = 12 * cstar * ((sz.size n : ℕ) : ℝ) ^ (3 * ε₁ - c / 60) := by
          have : (3 * ε₁ - c / 60) = 3 * ε₁ + (-c / 60) := by ring
          rw [this, Real.rpow_add hN0]; ring
      _ < 1 := hP1n
  -- the probability transfer
  have hJmeas : ∀ (n : ℕ) (u : ℝ), Measurable (fun H : Matrix (Idx d (sz.L n) (sz.W n))
      (Idx d (sz.L n) (sz.W n)) ℂ => STJhatM sz n (STflowE z n) D (Kf n u) u H) :=
    fun n u => STJhatM_measurable sz n (STflowE z n) u D (Kf n u)
  have hmodel := ST_model_le_path sz s T K hs hsT hK0 n
    (fun n u H => STJhatM sz n (STflowE z n) D (Kf n u) u H)
    (fun n u _ => ((1 - s n) / (1 - u)) ^ (3 * C + 1) * (sz.Bctl n u) ^ (1 / 5 : ℝ))
    hJmeas (fun n u => measurable_const) τ
    {ω | ¬ STGoodAt sz s T K n (STflowE z n) D (fun j => Kf n (gridTime s T K n j)) (Λ n) δ₀
      (a₀ n) (a₀ n) (ρ₁ n) (Mart n) (Rem n) ω} (by
      intro ω hω hg
      -- the engine on the good event
      have hKs : ∀ j, j ≤ K n → s n ≤ gridTime s T K n j ∧ gridTime s T K n j ≤ T n := fun j hj =>
        ST_gridTime_mem s T K n j (hsT n) (hK0 n) hj
      have hKf0 : ∀ j, j ≤ K n → 0 ≤ Kf n (gridTime s T K n j) := fun j hj =>
        (hKc _ (hKs j hj).1 ((hKs j hj).2.trans (hTt n))).1
      have hKfL : ∀ j, j ≤ K n → Kf n (gridTime s T K n j) ≤ ((sz.L n : ℕ) : ℝ) := fun j hj =>
        (hKc _ (hKs j hj).1 ((hKs j hj).2.trans (hTt n))).2.1
      have hTmono : ∀ j k, j ≤ k → k ≤ K n →
          tailT d (sz.L n) (sz.lam n) (gridTime s T K n j) (Kf n (gridTime s T K n j)) ≤
            tailT d (sz.L n) (sz.lam n) (gridTime s T K n k) (Kf n (gridTime s T K n k)) :=
        fun j k hjk hk => hKmono _ _ (hKs j (hjk.trans hk)).1
          (ST_gridTime_mono s T K n (hsT n) hjk) ((hKs k hk).2.trans (hTt n))
      have hsmall : ∀ k, k ≤ K n →
          (3 + 3 * ((mE (STflowE z n)).im)⁻¹) * (Λ n) ^ 2 *
            (1 + Λ n + Real.log ((1 - s n) / (1 - gridTime s T K n k))) *
            ((1 - s n) / (1 - gridTime s T K n k)) ^ (3 * C) *
            (sz.Bctl n (gridTime s T K n k)) ^ (1 / 30 : ℝ) < 1 := by
        intro k hk
        have hu1 := hlt1 (gridTime s T K n k) ((hKs k hk).2.trans (hTt n))
        have hu2 := hKs k hk
        have hs1 : 0 < 1 - s n := by
          have := hlt1 (s n) (hst' n); linarith
        have hr1 : 1 ≤ (1 - s n) / (1 - gridTime s T K n k) := by
          rw [le_div_iff₀ (by linarith)]; linarith [hu2.1]
        have hrb : (1 - s n) / (1 - gridTime s T K n k) ≤ (sz.Bctl n (t n)) ^ (-𝔠d) := by
          have ht1 : 0 < 1 - t n := by have := hlt1 (t n) le_rfl; linarith
          have hcon1 := hconn.1
          have hcon2 := hconn.2
          calc (1 - s n) / (1 - gridTime s T K n k) ≤ (1 - s n) / (1 - t n) :=
                div_le_div_of_nonneg_left hs1.le ht1 (by linarith [(hu2.2).trans (hTt n)])
            _ = ((1 - t n) / (1 - s n))⁻¹ := (inv_div _ _).symm
            _ ≤ ((sz.Bctl n (t n)) ^ 𝔠d)⁻¹ :=
                inv_anti₀ (Real.rpow_pos_of_pos (hbpos _ le_rfl) _) hcon1
            _ = (sz.Bctl n (t n)) ^ (-𝔠d) := (Real.rpow_neg (hbpos _ le_rfl).le _).symm
        exact ST_hsmall_aux (c₁ := 3 + 3 * ((mE (STflowE z n)).im)⁻¹) (Λ := Λ n) (q := Λ n)
          hC.le (by have := hΛ1 n; linarith) hc₁0 hr1 hrb
          (hbpos _ ((hKs k hk).2.trans (hTt n)))
          (STBctl_mono sz n ((hKs k hk).2.trans (hTt n)) (hlt1 (t n) le_rfl)) hbt1 h3 hΛq
      have ha₀0 : 0 ≤ a₀ n := by
        rw [ha₀def]
        exact mul_nonneg (by have := hΛ1 n; linarith) (Real.rpow_nonneg (hbpos _ (hst' n)).le _)
      have hρ₁0 : 0 ≤ ρ₁ n := by rw [hρ₁def]; exact sq_nonneg _
      have hq0 : 0 ≤ Λ n := by have := hΛ1 n; linarith
      have hae : a₀ n ≤ Λ n * (sz.Bctl n (s n)) ^ (1 / 5 : ℝ) := le_of_eq (by rw [ha₀def])
      have hρe : ρ₁ n ≤ (Λ n * (sz.Bctl n (s n)) ^ (1 / 5 : ℝ)) ^ 2 := le_of_eq (by rw [hρ₁def])
      have hb_eng := (ST_good_engine sz s T K n (STflowE z) D Kf (Λ := Λ n) (δ₀ := δ₀) (C := C)
        (a₀ := a₀ n) (r₀ := a₀ n) (ρ₁ := ρ₁ n) (q := Λ n) (κ := κ) (𝔡 := 𝔡) (hK0 n) (hs n)
        (hsT n) (hT1 n) hD.le hmI (hΛ1 n) hC.le ha₀0 ha₀0 hρ₁0 hlam hlam' hE hnew hKf0 hKfL
        hTmono hb1 hq0 hae hae hρe hsmall (Mart n) (Rem n) ω hg).2 (K n) le_rfl
      rw [gridTime_last s T K n (hK0 n)] at hb_eng
      have hr1 : 1 ≤ (1 - s n) / (1 - T n) := by
        rw [le_div_iff₀ (by linarith [hT1 n])]; linarith [hsT n]
      have hfinal := ST_final_cmp (c₁ := 3 + 3 * ((mE (STflowE z n)).im)⁻¹) (Λ := Λ n)
        (q := Λ n) (C := C) (r := (1 - s n) / (1 - T n)) (b := sz.Bctl n (T n))
        (M := ((sz.size n : ℕ) : ℝ) ^ τ) (by have := hΛ1 n; linarith) hc₁0 hr1
        (hbpos _ (hTt n)).le (by
          have hΛe : Λ n = 2 * X n := by rw [hΛdef]
          have hX := hX1 n
          have h12 : (Λ n) ^ 2 * (1 + Λ n) ≤ 12 * (X n) ^ 3 := by
            rw [hΛe]; nlinarith [mul_nonneg (sub_nonneg.2 hX) (sq_nonneg (X n))]
          have hXe : (X n) ^ 3 = ((sz.size n : ℕ) : ℝ) ^ (3 * ε₁) := by
            rw [hXdef]; simp only
            rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; congr 1; push_cast; ring
          have hΛ0 : 0 ≤ (Λ n) ^ 2 * (1 + Λ n) := by have := hΛ1 n; positivity
          calc (3 + 3 * ((mE (STflowE z n)).im)⁻¹) * (Λ n) ^ 2 * (1 + Λ n)
              = (3 + 3 * ((mE (STflowE z n)).im)⁻¹) * ((Λ n) ^ 2 * (1 + Λ n)) := by ring
            _ ≤ cstar * (12 * ((sz.size n : ℕ) : ℝ) ^ (3 * ε₁)) :=
                mul_le_mul hcstar (by rw [← hXe]; exact h12) hΛ0 hcstar0.le
            _ = 12 * cstar * ((sz.size n : ℕ) : ℝ) ^ (3 * ε₁) := by ring
            _ ≤ _ := hP2n)
      -- `hω : N^τ Z < Ĵ`
      have hω' : ((sz.size n : ℕ) : ℝ) ^ τ * (((1 - s n) / (1 - T n)) ^ (3 * C + 1) *
          (sz.Bctl n (T n)) ^ (1 / 5 : ℝ)) <
          STJhatM sz n (STflowE z n) D (Kf n (T n)) (T n) (pathH sz s T K n (K n) ω) := hω
      exact absurd hω' (not_lt.2 (hb_eng.trans hfinal)))
  refine le_trans (measure_mono ?_) (hmodel.trans hgpn)
  intro ω hω
  obtain ⟨i, hi⟩ := hω
  have hPpos := ST_STprof_pos sz n (T n) D (Kf n (T n)) (i.2 0) (i.2 1)
  have hratio : ‖STLKM sz n (STflowE z n) (T n) (sz.seqHflow n (T n) ω) i.1 i.2‖ /
      STprof sz n (T n) D (Kf n (T n)) (i.2 0) (i.2 1) ≤
      STJhatM sz n (STflowE z n) D (Kf n (T n)) (T n) (sz.seqHflow n (T n) ω) := by
    unfold STJhatM
    exact Finset.le_sup' (fun p : (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)) =>
      ‖STLKM sz n (STflowE z n) (T n) (sz.seqHflow n (T n) ω) p.1 p.2‖ /
        STprof sz n (T n) D (Kf n (T n)) (p.2 0) (p.2 1)) (Finset.mem_univ i)
  rw [div_le_iff₀ hPpos] at hratio
  show ((sz.size n : ℕ) : ℝ) ^ τ * (((1 - s n) / (1 - T n)) ^ (3 * C + 1) *
      (sz.Bctl n (T n)) ^ (1 / 5 : ℝ)) <
    STJhatM sz n (STflowE z n) D (Kf n (T n)) (T n) (sz.seqHflow n (T n) ω)
  have hi' : ((sz.size n : ℕ) : ℝ) ^ τ * (((1 - s n) / (1 - T n)) ^ (3 * C + 1) *
      (sz.Bctl n (T n)) ^ (1 / 5 : ℝ) * STprof sz n (T n) D (Kf n (T n)) (i.2 0) (i.2 1)) <
      ‖STLKM sz n (STflowE z n) (T n) (sz.seqHflow n (T n) ω) i.1 i.2‖ := by
    rw [hTD n]; exact hi
  have h2 : ((sz.size n : ℕ) : ℝ) ^ τ * (((1 - s n) / (1 - T n)) ^ (3 * C + 1) *
      (sz.Bctl n (T n)) ^ (1 / 5 : ℝ)) * STprof sz n (T n) D (Kf n (T n)) (i.2 0) (i.2 1) <
      STJhatM sz n (STflowE z n) D (Kf n (T n)) (T n) (sz.seqHflow n (T n) ω) *
        STprof sz n (T n) D (Kf n (T n)) (i.2 0) (i.2 1) := by
    calc _ = ((sz.size n : ℕ) : ℝ) ^ τ * (((1 - s n) / (1 - T n)) ^ (3 * C + 1) *
          (sz.Bctl n (T n)) ^ (1 / 5 : ℝ) * STprof sz n (T n) D (Kf n (T n)) (i.2 0) (i.2 1)) := by
          ring
      _ < _ := hi'
      _ ≤ _ := hratio
  exact lt_of_mul_lt_mul_right h2 hPpos.le

end Main

end RBM.Gauss.Sizes

namespace RBM.Gauss.Sizes

open MeasureTheory Filter RBM RBM.Gauss RBM.Gauss.Sizes RBM.Path

section Iterate2

variable {d : ℕ} (sz : Sizes d)

/-- `r^{C_d} b^{1/5} ≤ b^{1/6}` from `r ≤ b_t^{-𝔠_d}`, `b ≤ b_t ≤ 1`, `C_d 𝔠_d ≤ 1/60`
(`3_5:570`, "`𝔠_d` small"). -/
theorem ST_hq_arith {r b bt 𝔠' Cd : ℝ} (hCd : 0 ≤ Cd) (hr1 : 1 ≤ r) (hrb : r ≤ bt ^ (-𝔠'))
    (h𝔠 : 0 ≤ 𝔠') (hb : 0 < b) (hbt : b ≤ bt) (hbt1 : bt ≤ 1) (h : Cd * 𝔠' ≤ 1 / 60) :
    r ^ Cd * b ^ (1 / 5 : ℝ) ≤ b ^ (1 / 6 : ℝ) := by
  have hbt0 : 0 < bt := hb.trans_le hbt
  have hb1 : b ≤ 1 := hbt.trans hbt1
  have h1 : r ^ Cd ≤ b ^ (-(Cd * 𝔠')) := by
    calc r ^ Cd ≤ (bt ^ (-𝔠')) ^ Cd := Real.rpow_le_rpow (by linarith) hrb hCd
      _ = bt ^ (-(Cd * 𝔠')) := by rw [← Real.rpow_mul hbt0.le]; congr 1; ring
      _ ≤ b ^ (-(Cd * 𝔠')) := Real.rpow_le_rpow_of_nonpos hb hbt (by nlinarith)
  calc r ^ Cd * b ^ (1 / 5 : ℝ) ≤ b ^ (-(Cd * 𝔠')) * b ^ (1 / 5 : ℝ) :=
        mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hb.le _)
    _ = b ^ (-(Cd * 𝔠') + 1 / 5) := (Real.rpow_add hb _ _).symm
    _ ≤ b ^ (1 / 6 : ℝ) := Real.rpow_le_rpow_of_exponent_ge hb hb1 (by linarith)

set_option maxHeartbeats 800000 in
/-- **All time sections**: the self-improving bound of one step holds per time
(`STSelfImp`, `(eq:Gronwall_dervJuD)` for every `u ∈ [s,t]`). -/
theorem ST_selfImprove (hLWT : STLWT d) (hEMe : STEMn2Exp d) (hd : 0 < d)
    {κ ε 𝔡 𝔠 : ℝ} (hκ : 0 < κ) (hε : 0 < ε) (h𝔡 : 0 < 𝔡) {z : ℕ → ℂ}
    (hflow : STFlow sz κ ε 𝔠 𝔡 z) {s t : ℕ → ℝ} (hs : ∀ n, 0 ≤ s n) (hst : ∀ n, s n ≤ t n)
    (htT : ∀ n, t n ≤ lemT (z n))
    {C δ₀ C₀ 𝔠d : ℝ} (hC : 0 < C) (hδ₀ : 0 < δ₀) (hC₀ : 0 ≤ C₀)
    (hnew : STNewKLKAt d κ 𝔡 C δ₀) (hmart : STGridMartAt d C₀)
    (h𝔠d : 0 < 𝔠d) (h3 : (3 * C + 1) * 𝔠d ≤ 1 / 60)
    (hDec : STDecay sz (STflowE z) s) (hCon : STConStInd sz 𝔠d s t)
    (hS1W : STStep1Weak sz (STflowE z) s t) {cB c : ℝ} (hcB : 0 < cB) (hc : 0 < c)
    (hBd : ∀ᶠ n in atTop, ∀ u : ℝ, 0 ≤ u → u ≤ t n →
      cB * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ sz.Bctl n u ∧ sz.Bctl n u ≤ ((sz.size n : ℕ) : ℝ) ^ (-c))
    (Kf : ℕ → ℝ → ℝ) (hKok : STScaleOk sz s t Kf) (hinv : STScaleInv sz (STflowE z) s t Kf) :
    STSelfImp sz (3 * C + 1) (STflowE z) s t Kf := by
  intro D hD
  exact ST_PT_of_sections sz (V := fun n => STLab sz n) hst
    (fun n p ω => ‖Lloop sz n (STflowE z n) (p.1 : ℝ) p.2.1 p.2.2 ω -
      STKloop sz n (STflowE z n) (p.1 : ℝ) p.2.1 p.2.2‖)
    (fun n p _ => ((1 - s n) / (1 - (p.1 : ℝ))) ^ (3 * C + 1) * (sz.Bctl n (p.1 : ℝ)) ^ (1 / 5 : ℝ) *
      STprof sz n (p.1 : ℝ) D (Kf n (p.1 : ℝ)) (p.2.2 0) (p.2.2 1))
    (fun tt => ST_selfImprove_section sz hLWT hEMe hd hκ hε h𝔡 hflow hs htT hC hδ₀ hC₀ hnew hmart
      h𝔠d h3 hDec hCon hS1W hcB hc hBd Kf hKok hinv tt D hD)

/-- **The iteration over the scale family** (`3_5:570–577`): `Inv(K_m) ⇒ SelfImp(K_m) ⇒ Inv(K_{m+1})`
for every level `m` of an admissible family, from the base `Inv(K_0)`, the one-step improvement
`hSelf` and the deterministic `𝒦^{(2)}` bound (`(eq:simpleboundK)`). -/
theorem ST_iterate {E s t : ℕ → ℝ} {Cd C_K : ℝ} (hsz : sz.SizeTendsto) (hst : ∀ n, s n ≤ t n)
    (hCK : 0 < C_K)
    (hSelf : ∀ Kf : ℕ → ℝ → ℝ, STScaleOk sz s t Kf → STScaleInv sz E s t Kf →
      STSelfImp sz Cd E s t Kf)
    (hK2 : ∀ᶠ n in atTop, ∀ u D (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)), s n ≤ u →
      u ≤ t n → 0 ≤ D →
      ‖STKloop sz n (E n) u σ a‖ ≤ C_K * STprof sz n u D ((sz.L n : ℕ) : ℝ) (a 0) (a 1))
    (hq : ∀ᶠ n in atTop, ∀ u, s n ≤ u → u ≤ t n →
      ((1 - s n) / (1 - u)) ^ Cd * (sz.Bctl n u) ^ (1 / 5 : ℝ) ≤ (sz.Bctl n u) ^ (1 / 6 : ℝ) ∧
        0 ≤ ((1 - s n) / (1 - u)) ^ Cd * (sz.Bctl n u) ^ (1 / 5 : ℝ) ∧
        (sz.Bctl n u) ^ (1 / 6 : ℝ) ≤ 1)
    (Kseq : ℕ → ℕ → ℝ → ℝ) (hAdm : STScaleAdm sz s t Kseq)
    (hbase : STScaleInv sz E s t (Kseq 0)) :
    ∀ m, STScaleInv sz E s t (Kseq m) ∧ STSelfImp sz Cd E s t (Kseq m) := by
  intro m
  induction m with
  | zero => exact ⟨hbase, hSelf _ (hAdm.2.1 0) hbase⟩
  | succ m ih =>
    have hinv' : STScaleInv sz E s t (Kseq (m + 1)) :=
      ST_next sz hsz hst hCK (Kseq m) (Kseq (m + 1)) hK2
        (hAdm.2.2.1 m) (hAdm.2.2.2.1 m)
        hq ih.2
    exact ⟨hinv', hSelf _ (hAdm.2.1 (m + 1)) hinv'⟩

/-- **`(Eq:Gdecay_w)` from the iteration** (`3_5:575–577`): after `M(D)` steps the scale family is
at the floor, and `ST_decay_of_final` turns the last self-improving bound into the per-time
`(Eq:Gdecay_w)`. -/
theorem ST_decay_pt {E s t : ℕ → ℝ} {Cd C_K : ℝ} (hsz : sz.SizeTendsto) (hst : ∀ n, s n ≤ t n)
    (hCK : 0 < C_K)
    (hSelf : ∀ Kf : ℕ → ℝ → ℝ, STScaleOk sz s t Kf → STScaleInv sz E s t Kf →
      STSelfImp sz Cd E s t Kf)
    (hK2 : ∀ᶠ n in atTop, ∀ u D (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)), s n ≤ u →
      u ≤ t n → 0 ≤ D →
      ‖STKloop sz n (E n) u σ a‖ ≤ C_K * STprof sz n u D ((sz.L n : ℕ) : ℝ) (a 0) (a 1))
    (hq : ∀ᶠ n in atTop, ∀ u, s n ≤ u → u ≤ t n →
      ((1 - s n) / (1 - u)) ^ Cd * (sz.Bctl n u) ^ (1 / 5 : ℝ) ≤ (sz.Bctl n u) ^ (1 / 6 : ℝ) ∧
        0 ≤ ((1 - s n) / (1 - u)) ^ Cd * (sz.Bctl n u) ^ (1 / 5 : ℝ) ∧
        (sz.Bctl n u) ^ (1 / 6 : ℝ) ≤ 1)
    (Kseq : ℕ → ℕ → ℝ → ℝ) (hAdm : STScaleAdm sz s t Kseq)
    (hbase : STScaleInv sz E s t (Kseq 0)) :
    STStep2DecayPT sz Cd E s t := by
  have hit := ST_iterate sz hsz hst hCK hSelf hK2 hq Kseq hAdm hbase
  refine ST_decay_of_final sz (fun D hD => ?_) ?_ ?_
  · obtain ⟨M, hM⟩ := hAdm.2.2.2.2 D hD
    refine ⟨Kseq M, (hit M).2, ?_⟩
    filter_upwards [hM, hAdm.2.2.1 M] with n hn hr u hsu hut
    exact ⟨(hr u hsu hut).1, hn u hsu hut⟩
  · filter_upwards [hq] with n hn u hsu hut
    obtain ⟨h1, h2, h3⟩ := hn u hsu hut
    have hW : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
    have hWd : (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ 1 :=
      inv_le_one_of_one_le₀ (one_le_pow₀ hW)
    calc ((1 - s n) / (1 - u)) ^ Cd * (sz.Bctl n u) ^ (1 / 5 : ℝ) *
          (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ 1 * 1 :=
          mul_le_mul (h1.trans h3) hWd (inv_nonneg.mpr (pow_nonneg (by linarith) d)) zero_le_one
      _ = 1 := one_mul 1
  · filter_upwards [hq] with n hn u hsu hut using (hn u hsu hut).2.1

end Iterate2

end RBM.Gauss.Sizes
/-! ## 12. The remaining pins of the skeleton and the closure of Step 2

`STScaleExists` (the scale family of `(eq:def_ell1)`), `STOptL2` (`(eq:opt_L2)`, the base of the
iteration) and `STLocalAvgOfL2` (the closing paragraph `3_5:455–465` from `(eq:L2_decay)` and
`lem_GbEXP`) are pins (deterministic or owed to ST-2); everything else of the proof of Step 2 is
compiled in this file (`ST_step2_of_pins`). -/

namespace RBM.Gauss.Sizes

open RBM RBM.Loop RBM.Path

section L2

variable {d : ℕ} (sz : Sizes d)

end L2

end RBM.Gauss.Sizes

namespace RBM.Gauss.Sizes

open MeasureTheory Filter RBM RBM.Gauss RBM.Gauss.Sizes RBM.Path

section Final

variable {d : ℕ} (sz : Sizes d)

/-- `STWB ≥ N⁻¹` for `0 ≤ u < 1` (the zero-mode term `(L^d |1-u|)⁻¹` of `B_{u,K}` alone). -/
theorem ST_STWB_lower (n : ℕ) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) (K : ℕ) :
    ((sz.size n : ℕ) : ℝ)⁻¹ ≤ STWB sz n u K := by
  have hL : (0 : ℝ) < ((sz.L n : ℕ) : ℝ) := by
    exact_mod_cast (by have := sz.three_le_L n; omega : 0 < sz.L n)
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hsz : ((sz.size n : ℕ) : ℝ) = ((sz.W n : ℕ) : ℝ) ^ d * ((sz.L n : ℕ) : ℝ) ^ d := by
    unfold Sizes.size; push_cast; ring
  have habs : |1 - u| = 1 - u := abs_of_pos (by linarith)
  have hLd : (0 : ℝ) < ((sz.L n : ℕ) : ℝ) ^ d := pow_pos hL d
  have hWd : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) ^ d := pow_pos hW d
  have hpos : 0 < ((sz.L n : ℕ) : ℝ) ^ d * |1 - u| := by rw [habs]; exact mul_pos hLd (by linarith)
  have hle : ((sz.L n : ℕ) : ℝ) ^ d * |1 - u| ≤ ((sz.L n : ℕ) : ℝ) ^ d := by
    rw [habs]; nlinarith
  have h1 : (((sz.L n : ℕ) : ℝ) ^ d)⁻¹ ≤ (((sz.L n : ℕ) : ℝ) ^ d * |1 - u|)⁻¹ := inv_anti₀ hpos hle
  have hX : 0 ≤ (sz.lam n ^ 2 + |1 - u|)⁻¹ * ((((K : ℕ) : ℝ) + 1) ^ (d - 2))⁻¹ :=
    mul_nonneg (inv_nonneg.mpr (by positivity)) (inv_nonneg.mpr (by positivity))
  unfold STWB Bparam
  rw [hsz, mul_inv]
  calc (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (((sz.L n : ℕ) : ℝ) ^ d)⁻¹
      ≤ (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (((sz.L n : ℕ) : ℝ) ^ d * |1 - u|)⁻¹ :=
        mul_le_mul_of_nonneg_left h1 (inv_nonneg.mpr hWd.le)
    _ ≤ (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * ((sz.lam n ^ 2 + |1 - u|)⁻¹ *
        ((((K : ℕ) : ℝ) + 1) ^ (d - 2))⁻¹ + (((sz.L n : ℕ) : ℝ) ^ d * |1 - u|)⁻¹) :=
        mul_le_mul_of_nonneg_left (by linarith) (inv_nonneg.mpr hWd.le)

/-- `STprof^{L} ≤ STWB + (W^d)⁻¹ W^{-D}` (`𝒯 ≤ B`, `ρ ≤ L`). -/
theorem ST_prof_L_le (n : ℕ) {u D : ℝ} (a b : Zd d (sz.L n)) :
    STprof sz n u D ((sz.L n : ℕ) : ℝ) a b ≤
      STWB sz n u (zdistInf d (sz.L n) (a - b)) +
        (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * ((sz.W n : ℕ) : ℝ) ^ (-D) := by
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hρL := ST_zdistInf_le sz n (a - b)
  have hρ0 : (0 : ℝ) ≤ ((zdistInf d (sz.L n) (a - b) : ℕ) : ℝ) := Nat.cast_nonneg _
  have hB0 : 0 ≤ Bparam d (sz.L n) (sz.lam n) u (zdistInf d (sz.L n) (a - b)) := by
    rw [← BparamR_natCast]; exact BparamR_nonneg hρ0
  unfold STprof STWB
  rw [← mul_add]
  refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr (pow_nonneg hW.le d))
  unfold tailW
  rw [min_eq_left hρL]
  refine max_le ?_ (by linarith)
  unfold tailT
  rw [BparamR_natCast]
  have hexp : Real.exp (-Real.sqrt (((zdistInf d (sz.L n) (a - b) : ℕ) : ℝ) /
      ellT (sz.L n) (sz.lam n) u)) ≤ 1 :=
    Real.exp_le_one_iff.2 (neg_nonpos.2 (Real.sqrt_nonneg _))
  calc Bparam d (sz.L n) (sz.lam n) u (zdistInf d (sz.L n) (a - b)) *
        Real.exp (-Real.sqrt (((zdistInf d (sz.L n) (a - b) : ℕ) : ℝ) /
          ellT (sz.L n) (sz.lam n) u))
      ≤ Bparam d (sz.L n) (sz.lam n) u (zdistInf d (sz.L n) (a - b)) * 1 :=
        mul_le_mul_of_nonneg_left hexp hB0
    _ ≤ Bparam d (sz.L n) (sz.lam n) u (zdistInf d (sz.L n) (a - b)) +
        ((sz.W n : ℕ) : ℝ) ^ (-D) := by
        have := Real.rpow_nonneg hW.le (-D)
        linarith

end Final

end RBM.Gauss.Sizes

namespace RBM.Gauss.Sizes

open MeasureTheory Filter RBM RBM.Gauss RBM.Gauss.Sizes RBM.Path

section Final2

variable {d : ℕ} (sz : Sizes d)

/-- The deterministic comparison of `(eq:L2_decay)`: `C_K 𝒯̃^L + (q W^{-d}B e^{-..} + W^{-D₁}) ≤
(2 + 2 C_K) W^{-d} B_{u,ρ}` (`q ≤ 1`, `W^{-D₁} ≤ N⁻¹`). -/
theorem ST_L2_cmp (n : ℕ) {u D₁ C_K q : ℝ} (hCK : 0 < C_K) (hu0 : 0 ≤ u) (hu1 : u < 1)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hW : ((sz.W n : ℕ) : ℝ) ^ (-D₁) ≤ ((sz.size n : ℕ) : ℝ)⁻¹) (a : Fin 2 → Zd d (sz.L n)) :
    C_K * STprof sz n u D₁ ((sz.L n : ℕ) : ℝ) (a 0) (a 1) +
      (q * STWB sz n u (zdistInf d (sz.L n) (a 0 - a 1)) *
        Real.exp (-(((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) /
          ellT (sz.L n) (sz.lam n) u) ^ (1 / 2 : ℝ)) + ((sz.W n : ℕ) : ℝ) ^ (-D₁)) ≤
      (2 + 2 * C_K) * STWB sz n u (zdistInf d (sz.L n) (a 0 - a 1)) := by
  have hW1 : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hS := ST_STWB_lower sz n hu0 hu1 (zdistInf d (sz.L n) (a 0 - a 1))
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
  have hS0 : 0 ≤ STWB sz n u (zdistInf d (sz.L n) (a 0 - a 1)) :=
    (inv_nonneg.mpr hN0.le).trans hS
  have hP := ST_prof_L_le sz n (u := u) (D := D₁) (a 0) (a 1)
  have hWd1 : (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * ((sz.W n : ℕ) : ℝ) ^ (-D₁) ≤
      STWB sz n u (zdistInf d (sz.L n) (a 0 - a 1)) := by
    calc (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * ((sz.W n : ℕ) : ℝ) ^ (-D₁)
        ≤ 1 * ((sz.W n : ℕ) : ℝ) ^ (-D₁) :=
          mul_le_mul_of_nonneg_right (inv_le_one_of_one_le₀ (one_le_pow₀ hW1))
            (Real.rpow_nonneg (by linarith) _)
      _ ≤ _ := by rw [one_mul]; exact hW.trans hS
  have hexp : Real.exp (-(((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) /
      ellT (sz.L n) (sz.lam n) u) ^ (1 / 2 : ℝ)) ≤ 1 :=
    Real.exp_le_one_iff.2 (neg_nonpos.2 (Real.rpow_nonneg (div_nonneg (Nat.cast_nonneg _)
      ellT_nonneg) _))
  have hterm : q * STWB sz n u (zdistInf d (sz.L n) (a 0 - a 1)) *
      Real.exp (-(((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) /
        ellT (sz.L n) (sz.lam n) u) ^ (1 / 2 : ℝ)) ≤
      STWB sz n u (zdistInf d (sz.L n) (a 0 - a 1)) := by
    calc _ ≤ 1 * STWB sz n u (zdistInf d (sz.L n) (a 0 - a 1)) * 1 :=
          mul_le_mul (mul_le_mul_of_nonneg_right hq1 hS0) hexp (Real.exp_pos _).le
            (by positivity)
      _ = _ := by ring
  have hW2 : ((sz.W n : ℕ) : ℝ) ^ (-D₁) ≤ STWB sz n u (zdistInf d (sz.L n) (a 0 - a 1)) :=
    hW.trans hS
  nlinarith [mul_le_mul_of_nonneg_left hP hCK.le]

set_option maxHeartbeats 800000 in
/-- **`(eq:L2_decay)`** (`3_5:455–462`) from `(Eq:Gdecay_w)` and the `𝒦^{(2)}` bound
(`(eq:kn2sol_decay)`), per time, at the floor `D₁ = 1/𝔠` (`W^{-D₁} ≤ N⁻¹`). -/
theorem ST_L2_decay_pt {E s t : ℕ → ℝ} {Cd C_K : ℝ} (hsz : sz.SizeTendsto) (hst : ∀ n, s n ≤ t n)
    (hs0 : ∀ n, 0 ≤ s n) (ht1 : ∀ n, t n < 1) (hCK : 0 < C_K) {𝔠 : ℝ} (h𝔠 : 0 < 𝔠)
    (hband : sz.Bandwidth 𝔠) (hdec : STStep2DecayPT sz Cd E s t)
    (hK2 : ∀ᶠ n in atTop, ∀ u D (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)), s n ≤ u →
      u ≤ t n → 0 ≤ D →
      ‖STKloop sz n (E n) u σ a‖ ≤ C_K * STprof sz n u D ((sz.L n : ℕ) : ℝ) (a 0) (a 1))
    (hq : ∀ᶠ n in atTop, ∀ u, s n ≤ u → u ≤ t n →
      ((1 - s n) / (1 - u)) ^ Cd * (sz.Bctl n u) ^ (1 / 5 : ℝ) ≤ (sz.Bctl n u) ^ (1 / 6 : ℝ) ∧
        0 ≤ ((1 - s n) / (1 - u)) ^ Cd * (sz.Bctl n u) ^ (1 / 5 : ℝ) ∧
        (sz.Bctl n u) ^ (1 / 6 : ℝ) ≤ 1) :
    STL2decayPT sz E s t := by
  have hsize := tendsto_size sz hsz
  obtain ⟨D₁, hD₁⟩ : ∃ D₁ : ℝ, D₁ = 1 / 𝔠 := ⟨_, rfl⟩
  have hD₁pos : 0 < D₁ := by rw [hD₁]; positivity
  have hWD : ∀ᶠ n in atTop, ((sz.W n : ℕ) : ℝ) ^ (-D₁) ≤ ((sz.size n : ℕ) : ℝ)⁻¹ := by
    filter_upwards [hband] with n hn
    have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
    have hNc : 0 < ((sz.size n : ℕ) : ℝ) ^ 𝔠 := Real.rpow_pos_of_pos hN0 _
    calc ((sz.W n : ℕ) : ℝ) ^ (-D₁) ≤ (((sz.size n : ℕ) : ℝ) ^ 𝔠) ^ (-D₁) :=
          Real.rpow_le_rpow_of_nonpos hNc hn (by linarith)
      _ = ((sz.size n : ℕ) : ℝ)⁻¹ := by
          rw [← Real.rpow_mul hN0.le, ← Real.rpow_neg_one]; congr 1; rw [hD₁]; field_simp
  have hcard : ∀ᶠ n in atTop,
      (Fintype.card (STLab sz n) : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ (3 : ℝ) := by
    filter_upwards [hsize.eventually (eventually_ge_atTop 4)] with n hn using ST_card_lab_le sz n hn
  refine ST_PT_of_sections sz (V := fun n => Fin 2 → Zd d (sz.L n)) hst
    (fun n p ω => ‖Lloop sz n (E n) (p.1 : ℝ) ![false, true] p.2 ω‖)
    (fun n p _ => STWB sz n (p.1 : ℝ) (zdistInf d (sz.L n) (p.2 0 - p.2 1))) (fun tt => ?_)
  have hsec := ST_sections_of_PT sz (V := STLab sz) (s := s) (t := t)
    (fun n p ω => ‖Lloop sz n (E n) (p.1 : ℝ) p.2.1 p.2.2 ω -
      STKloop sz n (E n) (p.1 : ℝ) p.2.1 p.2.2‖)
    (fun n p _ => ((1 - s n) / (1 - (p.1 : ℝ))) ^ Cd * (sz.Bctl n (p.1 : ℝ)) ^ (1 / 5 : ℝ) *
      STWB sz n (p.1 : ℝ) (zdistInf d (sz.L n) (p.2.2 0 - p.2.2 1)) *
      Real.exp (-(((zdistInf d (sz.L n) (p.2.2 0 - p.2.2 1) : ℕ) : ℝ) /
        ellT (sz.L n) (sz.lam n) (p.1 : ℝ)) ^ (1 / 2 : ℝ)) + ((sz.W n : ℕ) : ℝ) ^ (-D₁))
    (by norm_num) hcard (hdec D₁ hD₁pos) tt
  have h1 := StochDomAt.precomp_param (V := fun n => Fin 2 → Zd d (sz.L n))
    (show StochDomAt (Sizes.seqP sz) sz.size (U := STLab sz) _ _ from hsec)
    (fun n a => (![false, true], a))
  have hKp : StochDomAt (Sizes.seqP sz) sz.size (U := fun n => Fin 2 → Zd d (sz.L n))
      (fun n a ω => ‖STKloop sz n (E n) (tt n : ℝ) ![false, true] a‖)
      (fun n a _ => C_K * STprof sz n (tt n : ℝ) D₁ ((sz.L n : ℕ) : ℝ) (a 0) (a 1)) :=
    ST_prec_of_le_ev sz (fun n a _ => mul_nonneg hCK.le (ST_STprof_pos sz _ _ _ _ _ _).le)
      (by
        filter_upwards [hK2] with n hn a ω
        exact hn (tt n : ℝ) D₁ _ a (tt n).2.1 (tt n).2.2 hD₁pos.le)
  have hsum := StochDomAt.add hsize hKp h1
  have hL : StochDomAt (Sizes.seqP sz) sz.size (U := fun n => Fin 2 → Zd d (sz.L n))
      (fun n a ω => ‖Lloop sz n (E n) (tt n : ℝ) ![false, true] a ω‖)
      (fun n a ω => C_K * STprof sz n (tt n : ℝ) D₁ ((sz.L n : ℕ) : ℝ) (a 0) (a 1) +
        (((1 - s n) / (1 - (tt n : ℝ))) ^ Cd * (sz.Bctl n (tt n : ℝ)) ^ (1 / 5 : ℝ) *
          STWB sz n (tt n : ℝ) (zdistInf d (sz.L n) (a 0 - a 1)) *
          Real.exp (-(((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) /
            ellT (sz.L n) (sz.lam n) (tt n : ℝ)) ^ (1 / 2 : ℝ)) + ((sz.W n : ℕ) : ℝ) ^ (-D₁))) := by
    refine StochDomAt.of_le_left (fun n a ω => ?_) hsum
    have := norm_add_le (STKloop sz n (E n) (tt n : ℝ) ![false, true] a)
      (Lloop sz n (E n) (tt n : ℝ) ![false, true] a ω -
        STKloop sz n (E n) (tt n : ℝ) ![false, true] a)
    simpa [add_sub_cancel] using this
  have hmono : sz.Prec (U := fun n => Fin 2 → Zd d (sz.L n))
      (fun n a ω => ‖Lloop sz n (E n) (tt n : ℝ) ![false, true] a ω‖)
      (fun n a _ => (2 + 2 * C_K) * STWB sz n (tt n : ℝ) (zdistInf d (sz.L n) (a 0 - a 1))) := by
    refine ST_prec_mono_eventually sz ?_ hL
    filter_upwards [hq, hWD] with n hn hW a ω
    obtain ⟨h1, h2, h3⟩ := hn (tt n : ℝ) (tt n).2.1 (tt n).2.2
    exact ST_L2_cmp sz n hCK ((hs0 n).trans (tt n).2.1)
      (lt_of_le_of_lt (tt n).2.2 (ht1 n)) h2 (h1.trans h3) hW a
  have hpos : ∀ (n : ℕ) (a : Fin 2 → Zd d (sz.L n)) (ω : sz.SeqΩ),
      0 ≤ STWB sz n (tt n : ℝ) (zdistInf d (sz.L n) (a 0 - a 1)) := fun n a _ => by
    have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
    exact (inv_nonneg.mpr hN0.le).trans (ST_STWB_lower sz n ((hs0 n).trans (tt n).2.1)
      (lt_of_le_of_lt (tt n).2.2 (ht1 n)) _)
  have hcst := StochDomAt.const_mul_left (P := Sizes.seqP sz) hsize
    (show 0 ≤ 2 + 2 * C_K by linarith) hpos (StochDomAt.refl (P := Sizes.seqP sz) hsize hpos)
  exact StochDomAt.trans hsize hmono hcst

end Final2

end RBM.Gauss.Sizes

namespace RBM.Gauss.Sizes

open MeasureTheory Filter RBM RBM.Gauss RBM.Gauss.Sizes RBM.Path

section Bdata

variable {d : ℕ} (sz : Sizes d)

/-- **`1 - lemT z ≥ Im z/(1+|z|)`**: from `m + z = -m⁻¹` on imaginary parts,
`Im z · |m|² = Im m (1 - |m|²)` with `Im m ≤ |m|`, and `|m| ≥ (1+|z|)⁻¹` (merged `lemT_ge`). -/
theorem ST_one_sub_lemT {z : ℂ} (hz : 0 < z.im) : z.im / (1 + ‖z‖) ≤ 1 - lemT z := by
  set m := msc z with hm
  have hr : 0 < ‖m‖ := norm_msc_pos hz
  have hI : 0 < m.im := msc_im_pos hz
  have hlt : ‖m‖ < 1 := norm_msc_lt_one hz
  have hN : Complex.normSq m = ‖m‖ ^ 2 := by rw [Complex.sq_norm]
  have him : m.im + z.im = m.im / ‖m‖ ^ 2 := by
    have := congrArg Complex.im (msc_add_eq_neg_inv hz)
    simp only [Complex.add_im, Complex.neg_im, Complex.inv_im] at this
    have h' : m.im + z.im = m.im / Complex.normSq m := by rw [← hm] at this; rw [this]; ring
    rwa [hN] at h'
  have hkey : z.im * ‖m‖ ^ 2 = m.im * (1 - ‖m‖ ^ 2) := by
    have h1 : (m.im + z.im) * ‖m‖ ^ 2 = m.im := by
      rw [him]; field_simp
    nlinarith [h1]
  have hIle : m.im ≤ ‖m‖ := Complex.im_le_norm m
  have h1 : z.im * ‖m‖ ^ 2 ≤ ‖m‖ * (1 - ‖m‖ ^ 2) := by
    rw [hkey]
    exact mul_le_mul_of_nonneg_right hIle (by nlinarith)
  have h2 : z.im * ‖m‖ ≤ 1 - ‖m‖ ^ 2 := by
    have : ‖m‖ * (z.im * ‖m‖) ≤ ‖m‖ * (1 - ‖m‖ ^ 2) := by nlinarith [h1]
    exact le_of_mul_le_mul_left this hr
  have h3 : (1 + ‖z‖)⁻¹ ≤ ‖m‖ := by
    have hg := lemT_ge hz
    rw [lemT, ← inv_pow] at hg
    exact (pow_le_pow_iff_left₀ (by positivity) hr.le two_ne_zero).1 hg
  calc z.im / (1 + ‖z‖) = z.im * (1 + ‖z‖)⁻¹ := div_eq_mul_inv _ _
    _ ≤ z.im * ‖m‖ := mul_le_mul_of_nonneg_left h3 hz.le
    _ ≤ 1 - ‖m‖ ^ 2 := h2
    _ = 1 - lemT z := by rw [lemT]

set_option maxHeartbeats 800000 in
/-- **The size data** (`STBdata`) is a theorem: `W^{-d} B_{u,0} ≤ (ilambda² W^d)⁻¹ + (N(1-u))⁻¹ ≤
W^{-2𝔡} + 4 N^{-ε}` (`(eq:WO)`, `Im z ≥ N^{-1+ε}`, `1 - u ≥ 1 - lemT z ≥ Im z/4`) and
`B_{u,0} ≥ (ilambda² + 1)⁻¹ ≥ (𝔡^{-2} + 1)⁻¹`. -/
theorem ST_Bdata_holds (hd : 0 < d) : STBdata d := by
  intro κ ε 𝔡 hκ hε h𝔡
  refine ⟨(𝔡⁻¹ ^ 2 + 1)⁻¹, by positivity, fun 𝔠 => ?_⟩
  rcases le_or_gt 𝔠 0 with h𝔠 | h𝔠
  · exact ⟨1, one_pos, fun sz z hflow => absurd hflow.1.1 (not_lt.2 h𝔠)⟩
  refine ⟨min (2 * 𝔡 * 𝔠) ε / 2, by
    have := lt_min (mul_pos (mul_pos two_pos h𝔡) h𝔠) hε; linarith, ?_⟩
  intro sz z hflow t ht0 htT
  have hsz : sz.SizeTendsto := hflow.1.2.2.1
  have hband : sz.Bandwidth 𝔠 := hflow.1.2.2.2.1
  have hWO : sz.WO 𝔡 := hflow.1.2.2.2.2
  have hsize := tendsto_size sz hsz
  obtain ⟨c, hcdef⟩ : ∃ c : ℝ, c = min (2 * 𝔡 * 𝔠) ε / 2 := ⟨_, rfl⟩
  have hc : 0 < c := by
    rw [hcdef]; have := lt_min (mul_pos (mul_pos two_pos h𝔡) h𝔠) hε; linarith
  have hc1 : 2 * c ≤ 2 * 𝔡 * 𝔠 := by rw [hcdef]; have := min_le_left (2 * 𝔡 * 𝔠) ε; linarith
  have hc2 : 2 * c ≤ ε := by rw [hcdef]; have := min_le_right (2 * 𝔡 * 𝔠) ε; linarith
  rw [← hcdef]
  filter_upwards [hWO, hband, ST_size_pow_big sz hsize (a := c) (M := 5) hc,
    hsize.eventually (eventually_ge_atTop 1)] with n hwo hbn hN5 hN1 u hu0 hut
  have hN1' : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast hN1
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hL : (0 : ℝ) < ((sz.L n : ℕ) : ℝ) := by
    exact_mod_cast (by have := sz.three_le_L n; omega : 0 < sz.L n)
  have him := ST_flow_im_pos sz hflow n
  have hlt1 : u < 1 := lt_of_le_of_lt (hut.trans (htT n)) (lemT_lt_one him)
  have hlam : 0 < sz.lam n :=
    lt_of_lt_of_le (Real.rpow_pos_of_pos hW _) hwo.1
  have hWd : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) ^ d := pow_pos hW d
  have hLd : (0 : ℝ) < ((sz.L n : ℕ) : ℝ) ^ d := pow_pos hL d
  have hz0 : ((0 : ℕ) : ℝ) + 1 = 1 := by norm_num
  have hBp : Bparam d (sz.L n) (sz.lam n) u 0 =
      (sz.lam n ^ 2 + (1 - u))⁻¹ + (((sz.L n : ℕ) : ℝ) ^ d * (1 - u))⁻¹ := by
    unfold Bparam
    rw [abs_of_pos (by linarith : (0 : ℝ) < 1 - u)]
    simp
  have hBc : sz.Bctl n u = (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * Bparam d (sz.L n) (sz.lam n) u 0 := rfl
  constructor
  · -- the lower bound
    rw [hBc, hBp, mul_comm]
    refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr hWd.le)
    have h1 : (sz.lam n ^ 2 + (1 - u))⁻¹ ≥ (𝔡⁻¹ ^ 2 + 1)⁻¹ := by
      refine inv_anti₀ (by positivity) ?_
      have := pow_le_pow_left₀ hlam.le hwo.2 2
      linarith
    have h2 : 0 ≤ (((sz.L n : ℕ) : ℝ) ^ d * (1 - u))⁻¹ :=
      inv_nonneg.mpr (mul_nonneg hLd.le (by linarith))
    linarith
  · -- the upper bound
    have hz3 : ‖z n‖ ≤ 3 := by
      have h1 := Complex.norm_le_abs_re_add_abs_im (z n)
      have h2 := (hflow.2 n).1
      have h3 := (hflow.2 n).2.2
      rw [abs_of_pos him] at h1
      linarith
    have hone := ST_one_sub_lemT him
    have hu1 : (z n).im / 4 ≤ 1 - u := by
      have : (z n).im / 4 ≤ (z n).im / (1 + ‖z n‖) :=
        div_le_div_of_nonneg_left him.le (by positivity) (by linarith)
      have h2 : 1 - lemT (z n) ≤ 1 - u := by linarith [hut.trans (htT n)]
      linarith
    have hNim : ((sz.size n : ℕ) : ℝ) ^ (-1 + ε) ≤ (z n).im := (hflow.2 n).2.1
    have hsz2 : ((sz.size n : ℕ) : ℝ) = ((sz.W n : ℕ) : ℝ) ^ d * ((sz.L n : ℕ) : ℝ) ^ d := by
      unfold Sizes.size; push_cast; ring
    -- `(N(1-u))⁻¹ ≤ 4 N^{-ε}`
    have hA : (((sz.L n : ℕ) : ℝ) ^ d * (1 - u))⁻¹ * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤
        4 * ((sz.size n : ℕ) : ℝ) ^ (-ε) := by
      have h1 : (((sz.L n : ℕ) : ℝ) ^ d * (1 - u))⁻¹ * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ =
          (((sz.size n : ℕ) : ℝ) * (1 - u))⁻¹ := by
        rw [hsz2]; field_simp
      rw [h1]
      have hNε : 0 < ((sz.size n : ℕ) : ℝ) ^ (-1 + ε) := Real.rpow_pos_of_pos hN0 _
      have h2 : ((sz.size n : ℕ) : ℝ) ^ (-1 + ε) / 4 ≤ 1 - u := by linarith
      have h3 : ((sz.size n : ℕ) : ℝ) * (((sz.size n : ℕ) : ℝ) ^ (-1 + ε) / 4) ≤
          ((sz.size n : ℕ) : ℝ) * (1 - u) := mul_le_mul_of_nonneg_left h2 hN0.le
      have h4 : ((sz.size n : ℕ) : ℝ) * (((sz.size n : ℕ) : ℝ) ^ (-1 + ε) / 4) =
          ((sz.size n : ℕ) : ℝ) ^ ε / 4 := by
        have : ((sz.size n : ℕ) : ℝ) ^ ε = ((sz.size n : ℕ) : ℝ) * ((sz.size n : ℕ) : ℝ) ^ (-1 + ε) := by
          conv_lhs => rw [show ε = 1 + (-1 + ε) by ring]
          rw [Real.rpow_add hN0, Real.rpow_one]
        rw [this]; ring
      rw [h4] at h3
      have h5 : 0 < ((sz.size n : ℕ) : ℝ) ^ ε / 4 := by positivity
      calc (((sz.size n : ℕ) : ℝ) * (1 - u))⁻¹ ≤ (((sz.size n : ℕ) : ℝ) ^ ε / 4)⁻¹ :=
            inv_anti₀ h5 h3
        _ = 4 * ((sz.size n : ℕ) : ℝ) ^ (-ε) := by
            rw [Real.rpow_neg hN0.le]; field_simp
    -- `(W^d lam²)⁻¹ ≤ W^{-2𝔡} ≤ N^{-2𝔡𝔠}`
    have hB : (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (sz.lam n ^ 2)⁻¹ ≤ ((sz.size n : ℕ) : ℝ) ^ (-(2 * 𝔡 * 𝔠)) := by
      have h1 := Sizes.lam_sq_mul_pow_ge sz n hwo.1
      have h2 : (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (sz.lam n ^ 2)⁻¹ =
          (sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d)⁻¹ := by rw [mul_comm, mul_inv]
      rw [h2]
      have hNc : 0 < ((sz.size n : ℕ) : ℝ) ^ 𝔠 := Real.rpow_pos_of_pos hN0 _
      calc (sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ (((sz.W n : ℕ) : ℝ) ^ (2 * 𝔡))⁻¹ :=
            inv_anti₀ (Real.rpow_pos_of_pos hW _) h1
        _ = ((sz.W n : ℕ) : ℝ) ^ (-(2 * 𝔡)) := (Real.rpow_neg hW.le _).symm
        _ ≤ (((sz.size n : ℕ) : ℝ) ^ 𝔠) ^ (-(2 * 𝔡)) :=
            Real.rpow_le_rpow_of_nonpos hNc hbn (by linarith)
        _ = ((sz.size n : ℕ) : ℝ) ^ (-(2 * 𝔡 * 𝔠)) := by
            rw [← Real.rpow_mul hN0.le]; congr 1; ring
    rw [hBc, hBp, mul_add]
    have hfirst : (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (sz.lam n ^ 2 + (1 - u))⁻¹ ≤
        (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (sz.lam n ^ 2)⁻¹ :=
      mul_le_mul_of_nonneg_left (inv_anti₀ (by positivity) (by linarith))
        (inv_nonneg.mpr hWd.le)
    have hsecond : (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (((sz.L n : ℕ) : ℝ) ^ d * (1 - u))⁻¹ ≤
        4 * ((sz.size n : ℕ) : ℝ) ^ (-ε) := by rw [mul_comm]; exact hA
    have hN2c : ((sz.size n : ℕ) : ℝ) ^ (-(2 * 𝔡 * 𝔠)) ≤ ((sz.size n : ℕ) : ℝ) ^ (-(2 * c)) :=
      Real.rpow_le_rpow_of_exponent_le hN1' (by linarith)
    have hNe : ((sz.size n : ℕ) : ℝ) ^ (-ε) ≤ ((sz.size n : ℕ) : ℝ) ^ (-(2 * c)) :=
      Real.rpow_le_rpow_of_exponent_le hN1' (by linarith)
    have hsum : 5 * ((sz.size n : ℕ) : ℝ) ^ (-(2 * c)) ≤ ((sz.size n : ℕ) : ℝ) ^ (-c) := by
      have e : ((sz.size n : ℕ) : ℝ) ^ (-(2 * c)) =
          ((sz.size n : ℕ) : ℝ) ^ (-c) * ((sz.size n : ℕ) : ℝ) ^ (-c) := by
        rw [← Real.rpow_add hN0]; congr 1; ring
      have h5 : 5 * ((sz.size n : ℕ) : ℝ) ^ (-c) ≤ 1 := by
        have hNc : 0 < ((sz.size n : ℕ) : ℝ) ^ c := Real.rpow_pos_of_pos hN0 _
        rw [Real.rpow_neg hN0.le, ← div_eq_mul_inv, div_le_one hNc]
        linarith
      have hp : 0 ≤ ((sz.size n : ℕ) : ℝ) ^ (-c) := Real.rpow_nonneg hN0.le _
      rw [e]
      nlinarith [mul_le_mul_of_nonneg_right h5 hp]
    linarith

end Bdata

end RBM.Gauss.Sizes

/-! ## 12.1 The bundle `STStep2Concl` from the three parts of `STStep2Parts`

`STStep2Parts` is the probe's `STStep2` (conclusion `STStep2Local ∧ STStep2Avg ∧ STStep2Decay`);
the merged `STStep2` concludes the bundle `STStep2Concl = STLocalEntryU ∧ STAvgU ∧ STGdecayW` of
`Induction/Step34Pins.lean`.  `STLocalEntryU`, `STGdecayW` are `STStep2Local`, `STStep2Decay` word for
word; `STAvgU` is `max_{σ,a} |𝓛^{(1)}_{u,σ,a} - 𝒦^{(1)}_{u,σ,a}| ≺ W^{-d}B_{u,0}` for **both** charges and
follows from `STStep2Avg` (charge `+`, `𝒦^{(1)}_+ = m(E)`) because `𝓛^{(1)}_- = conj 𝓛^{(1)}_+`
(`ST_Lloop_one_false`) and `𝒦^{(1)}_- = conj m(E)` (`ST_Kloop_one`) (`ST_avgU_of_avg`,
`ST_concl_of_step2`). -/

namespace RBM.Gauss.Sizes

open MeasureTheory Filter Matrix RBM RBM.Loop RBM.Gauss RBM.Gauss.Sizes RBM.Path

section Concl

variable {d : ℕ} (sz : Sizes d)

/-- `G(-) = G(+)^*`: `Gres H z false = (Gres H z true)ᴴ` for Hermitian `H`. -/
theorem ST_Gres_false {ι : Type*} [Fintype ι] [DecidableEq ι] {H : Matrix ι ι ℂ}
    (hH : H.IsHermitian) (z : ℂ) : Gres H z false = (Gres H z true)ᴴ := by
  unfold Gres
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [← Matrix.nonsing_inv_eq_ringInverse, ← Matrix.nonsing_inv_eq_ringInverse,
    Matrix.conjTranspose_nonsing_inv]
  congr 1
  rw [Matrix.conjTranspose_sub, hH.eq, Matrix.conjTranspose_smul, Matrix.conjTranspose_one]
  simp

/-- The block average `E_a` is Hermitian. -/
theorem ST_Eblk_herm (d L W : ℕ) [NeZero L] [NeZero W] (a : Zd d L) :
    (Eblk d L W a)ᴴ = Eblk d L W a := by
  unfold Eblk
  rw [Matrix.diagonal_conjTranspose]
  congr 1
  funext x
  by_cases h : x.1 = a <;> simp [h]

/-- `𝓛^{(1)}_{u,-,a} = conj 𝓛^{(1)}_{u,+,a}` (`G(-) = G(+)^*`, `E_a` Hermitian). -/
theorem ST_Lloop_one_false (n : ℕ) (E u : ℝ) (a : Zd d (sz.L n)) (ω : sz.SeqΩ) :
    Lloop sz n E u (fun _ : Fin 1 => false) (fun _ => a) ω =
      (starRingEnd ℂ) (Lloop sz n E u (fun _ : Fin 1 => true) (fun _ => a) ω) := by
  have hH : (blockMat d (sz.L n) (sz.W n) (sz.seqHflow n u ω)).IsHermitian := by
    unfold blockMat
    exact (sz.seqHflow_isHermitian n u ω).submatrix _
  unfold Lloop loopFine loopM
  simp only [List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, mul_one]
  have hE := ST_Eblk_herm d (sz.L n) (sz.W n) a
  rw [ST_Gres_false hH]
  have hm : (Gres (blockMat d (sz.L n) (sz.W n) (sz.seqHflow n u ω)) (zt E u) true)ᴴ *
      Eblk d (sz.L n) (sz.W n) a =
      (Eblk d (sz.L n) (sz.W n) a *
        Gres (blockMat d (sz.L n) (sz.W n) (sz.seqHflow n u ω)) (zt E u) true)ᴴ := by
    rw [Matrix.conjTranspose_mul, hE]
  rw [hm, Matrix.trace_conjTranspose, Matrix.trace_mul_comm]
  rfl

/-- `𝒦^{(1)}_{u,σ,a} = m(σ)` (`Def_Ktza`, `1_2:988`; merged `KLK_one`) at the labels of `STKloop`. -/
theorem ST_Kloop_one (n : ℕ) (E u : ℝ) (σ : Bool) (a : Zd d (sz.L n)) :
    STKloop sz n E u (fun _ : Fin 1 => σ) (fun _ => a) = mSigma E σ := by
  have : KLloopOf d (sz.L n) (fun _ : Fin 1 => σ) (fun _ => a) = ⟨[σ], [a]⟩ := by
    simp [KLloopOf, List.ofFn_succ]
  unfold STKloop
  rw [this]
  exact KLK_one d (sz.L n) (sz.lam n) (sz.W n) E u σ a

/-- Both charges of the one-loop error have the same modulus: `|𝓛^{(1)}_{σ,a} - 𝒦^{(1)}_{σ,a}| =
|𝓛^{(1)}_{+,a₀} - m(E)|`. -/
theorem ST_avg_pointwise (n : ℕ) (E u : ℝ) (σ : Fin 1 → Bool) (a : Fin 1 → Zd d (sz.L n))
    (ω : sz.SeqΩ) :
    ‖Lloop sz n E u σ a ω - STKloop sz n E u σ a‖ =
      ‖Lloop sz n E u (fun _ : Fin 1 => true) (fun _ => a 0) ω - mE E‖ := by
  obtain ⟨b, rfl⟩ : ∃ b, σ = fun _ => b := ⟨σ 0, funext fun i => by rw [Subsingleton.elim i 0]⟩
  obtain ⟨x, rfl⟩ : ∃ x, a = fun _ => x := ⟨a 0, funext fun i => by rw [Subsingleton.elim i 0]⟩
  rw [ST_Kloop_one sz n E u b x]
  cases b
  · rw [ST_Lloop_one_false sz n E u x ω]
    simp only [mSigma, Bool.false_eq_true, ↓reduceIte]
    rw [← map_sub, Complex.norm_conj]
  · simp [mSigma]

/-- `STAvgU` (both charges, `Lloop - STKloop`) from `STStep2Avg` (charge `+`, `Lloop - m(E)`). -/
theorem ST_avgU_of_avg {E s t : ℕ → ℝ} (h : STStep2Avg sz E s t) : STAvgU sz E s t := by
  unfold STStep2Avg Sizes.Prec at h
  have h1 := StochDomAt.precomp_param
    (V := fun n => TimeIcc s t n × (Fin 1 → Bool) × (Fin 1 → Zd d (sz.L n))) h
    (fun n p => (p.1, p.2.2 0))
  unfold STAvgU Sizes.Prec
  simp only [pow_one]
  refine StochDomAt.of_le_left (fun n p ω => ?_) h1
  exact (ST_avg_pointwise sz n (E n) (p.1 : ℝ) p.2.1 p.2.2 ω).le

/-- **The conclusions of `STStep2` imply the bundle `STStep2Concl` of the merged Steps 3-4 pins** (the
same `C_d`). -/
theorem ST_concl_of_step2 {E s t : ℕ → ℝ} {Cd : ℝ} (hL : STStep2Local sz E s t)
    (hA : STStep2Avg sz E s t) (hD : STStep2Decay sz Cd E s t) : STStep2Concl sz E s t Cd :=
  ⟨hL, ST_avgU_of_avg sz hA, hD⟩

end Concl

end RBM.Gauss.Sizes

namespace RBM.Gauss.Sizes

open MeasureTheory Filter RBM RBM.Gauss RBM.Gauss.Sizes RBM.Path

section Step2

variable {d : ℕ} (sz : Sizes d)

/-- `N ≥ 1` eventually (`N → ∞`). -/
theorem hsize_ev (hsz : sz.SizeTendsto) : ∀ᶠ n in atTop, 1 ≤ sz.size n :=
  (tendsto_size sz hsz).eventually (eventually_ge_atTop 1)

/-- `𝒯̃^{0}`: the profile at the scale `0` dominates `W^{-d}B_{u,0}`. -/
theorem ST_prof_zero_ge (n : ℕ) (u D : ℝ) (a b : Zd d (sz.L n)) :
    sz.Bctl n u ≤ STprof sz n u D 0 a b := by
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hρ0 : (0 : ℝ) ≤ ((zdistInf d (sz.L n) (a - b) : ℕ) : ℝ) := Nat.cast_nonneg _
  unfold STprof Sizes.Bctl
  refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr (pow_nonneg hW.le d))
  unfold tailW
  refine le_trans ?_ (le_max_left _ _)
  rw [min_eq_right hρ0, tailT_zero]

/-- `𝒯̃^{L} ≤ 𝒯̃^{0}`. -/
theorem ST_prof_L_le_zero (n : ℕ) (u D : ℝ) (a b : Zd d (sz.L n)) :
    STprof sz n u D ((sz.L n : ℕ) : ℝ) a b ≤ STprof sz n u D 0 a b := by
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hρ0 : (0 : ℝ) ≤ ((zdistInf d (sz.L n) (a - b) : ℕ) : ℝ) := Nat.cast_nonneg _
  have hρL := ST_zdistInf_le sz n (a - b)
  unfold STprof
  exact mul_le_mul_of_nonneg_left (ST_tailW_L_le (d := d) (L := sz.L n) (le_refl (0 : ℝ)) hρ0 hρL)
    (inv_nonneg.mpr (pow_nonneg hW.le d))

/-- **The base of the iteration** (`(ksjjuw)`, `3_5:512–518`): `(eq:opt_L2)` and `(eq:simpleboundK)`
give `𝓛^{(2)}_{u,σ,(a,b)} ≺ W^{-d} 𝒯̃^{0}_{u,D}(|a-b|)`, i.e. `Inv(K_0 = 0)`. -/
theorem ST_base_inv {E s t : ℕ → ℝ} (hsz : sz.SizeTendsto) (hst : ∀ n, s n ≤ t n) {C_K : ℝ}
    (hCK : 0 < C_K)
    (hK2 : ∀ᶠ n in atTop, ∀ u D (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)), s n ≤ u →
      u ≤ t n → 0 ≤ D →
      ‖STKloop sz n (E n) u σ a‖ ≤ C_K * STprof sz n u D ((sz.L n : ℕ) : ℝ) (a 0) (a 1))
    (hOpt : PrecPT sz (U := fun n => TimeIcc s t n × (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)))
      (fun n p ω => ‖Lloop sz n (E n) (p.1 : ℝ) p.2.1 p.2.2 ω -
        STKloop sz n (E n) (p.1 : ℝ) p.2.1 p.2.2‖)
      (fun n p _ => sz.Bctl n (p.1 : ℝ))) :
    STScaleInv sz E s t (fun n u => 0) := by
  intro tt D hD
  have hsize := tendsto_size sz hsz
  have hcard : ∀ᶠ n in atTop,
      (Fintype.card (STLab sz n) : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ (3 : ℝ) := by
    filter_upwards [hsize.eventually (eventually_ge_atTop 4)] with n hn using ST_card_lab_le sz n hn
  have hsec := ST_sections_of_PT sz (V := STLab sz) (s := s) (t := t)
    (fun n p ω => ‖Lloop sz n (E n) (p.1 : ℝ) p.2.1 p.2.2 ω -
      STKloop sz n (E n) (p.1 : ℝ) p.2.1 p.2.2‖)
    (fun n p _ => sz.Bctl n (p.1 : ℝ)) (by norm_num) hcard hOpt tt
  have hres := StochDomAt.precomp_param
    (V := fun n => {σ : Fin 2 → Bool // σ 0 ≠ σ 1} × (Fin 2 → Zd d (sz.L n)))
    (show StochDomAt (Sizes.seqP sz) sz.size (U := STLab sz) _ _ from hsec)
    (fun n p => (p.1.1, p.2))
  have hnonneg : ∀ (n : ℕ) (p : {σ : Fin 2 → Bool // σ 0 ≠ σ 1} × (Fin 2 → Zd d (sz.L n)))
      (ω : sz.SeqΩ), 0 ≤ C_K * STprof sz n (tt n : ℝ) D ((sz.L n : ℕ) : ℝ) (p.2 0) (p.2 1) :=
    fun n p _ => mul_nonneg hCK.le (ST_STprof_pos sz n _ _ _ _ _).le
  have hKp : StochDomAt (Sizes.seqP sz) sz.size
      (U := fun n => {σ : Fin 2 → Bool // σ 0 ≠ σ 1} × (Fin 2 → Zd d (sz.L n)))
      (fun n p ω => ‖STKloop sz n (E n) (tt n : ℝ) p.1.1 p.2‖)
      (fun n p _ => C_K * STprof sz n (tt n : ℝ) D ((sz.L n : ℕ) : ℝ) (p.2 0) (p.2 1)) :=
    ST_prec_of_le_ev sz hnonneg (by
      filter_upwards [hK2] with n hn p ω
      exact hn (tt n : ℝ) D p.1.1 p.2 (tt n).2.1 (tt n).2.2 hD.le)
  have hsum := StochDomAt.add hsize hKp hres
  have hL : StochDomAt (Sizes.seqP sz) sz.size
      (U := fun n => {σ : Fin 2 → Bool // σ 0 ≠ σ 1} × (Fin 2 → Zd d (sz.L n)))
      (fun n p ω => ‖Lloop sz n (E n) (tt n : ℝ) p.1.1 p.2 ω‖)
      (fun n p ω => C_K * STprof sz n (tt n : ℝ) D ((sz.L n : ℕ) : ℝ) (p.2 0) (p.2 1) +
        sz.Bctl n (tt n : ℝ)) := by
    refine StochDomAt.of_le_left (fun n p ω => ?_) hsum
    have := norm_add_le (STKloop sz n (E n) (tt n : ℝ) p.1.1 p.2)
      (Lloop sz n (E n) (tt n : ℝ) p.1.1 p.2 ω - STKloop sz n (E n) (tt n : ℝ) p.1.1 p.2)
    simpa [add_sub_cancel] using this
  have hmono : sz.Prec
      (U := fun n => {σ : Fin 2 → Bool // σ 0 ≠ σ 1} × (Fin 2 → Zd d (sz.L n)))
      (fun n p ω => ‖Lloop sz n (E n) (tt n : ℝ) p.1.1 p.2 ω‖)
      (fun n p _ => (C_K + 1) * STprof sz n (tt n : ℝ) D 0 (p.2 0) (p.2 1)) := by
    refine ST_prec_mono_eventually sz (Eventually.of_forall fun n p ω => ?_) hL
    have h1 := ST_prof_L_le_zero sz n (tt n : ℝ) D (p.2 0) (p.2 1)
    have h2 := ST_prof_zero_ge sz n (tt n : ℝ) D (p.2 0) (p.2 1)
    nlinarith [mul_le_mul_of_nonneg_left h1 hCK.le]
  have hpos : ∀ (n : ℕ) (p : {σ : Fin 2 → Bool // σ 0 ≠ σ 1} × (Fin 2 → Zd d (sz.L n)))
      (ω : sz.SeqΩ), 0 ≤ STprof sz n (tt n : ℝ) D 0 (p.2 0) (p.2 1) :=
    fun n p _ => (ST_STprof_pos sz n _ _ _ _ _).le
  have hcst := StochDomAt.const_mul_left (P := Sizes.seqP sz) hsize (show 0 ≤ C_K + 1 by linarith)
    hpos (StochDomAt.refl (P := Sizes.seqP sz) hsize hpos)
  exact StochDomAt.trans hsize hmono hcst

/-- `(1-s)/(1-u) ≤ b_t^{-𝔠_d}` from `(con_st_ind)` for `u ∈ [s,t]`. -/
theorem ST_ratio_le {s t u bt 𝔠' : ℝ} (hs1 : 0 < 1 - s) (ht1 : 0 < 1 - t) (hsu : s ≤ u)
    (hut : u ≤ t) (hbt : 0 < bt) (hcon : bt ^ 𝔠' ≤ (1 - t) / (1 - s)) :
    (1 - s) / (1 - u) ≤ bt ^ (-𝔠') := by
  calc (1 - s) / (1 - u) ≤ (1 - s) / (1 - t) :=
        div_le_div_of_nonneg_left hs1.le ht1 (by linarith)
    _ = ((1 - t) / (1 - s))⁻¹ := (inv_div _ _).symm
    _ ≤ (bt ^ 𝔠')⁻¹ := inv_anti₀ (Real.rpow_pos_of_pos hbt _) hcon
    _ = bt ^ (-𝔠') := (Real.rpow_neg hbt.le _).symm

set_option maxHeartbeats 1600000 in
/-- **Step 2 of `lem:main_ind` from its pinned ingredients** (the compiled skeleton of
`3_5:345–609`).  Taken as hypotheses (each a `Prop` of the file, with its registry class in the
report): the light-weight lemmas `STLWT`; the martingale estimate `STEMn2Exp`; `lem:newKLK`
`STNewKLK`; `Sol_CalL` + `lem:DIfREP` `STGridMart`; the deterministic `𝒦^{(2)}` decay `STK2decay`; the
scale family `STScaleExists`; the base `STOptL2`; the closing paragraph `STLocalAvgOfL2`; the net lift
`STNetLift2`.  Proved here: the size data (`ST_Bdata_holds`), the good event of the grid walk, the
stopped Grönwall bootstrap, the iteration over scales, `(Eq:Gdecay_w)` and `(eq:L2_decay)`; the
constants are `C_d = 3C + 1` (`C` of `lem:newKLK`) and `𝔠_d = min(1/100, 1/(60 C_d), 𝔠₀)`. -/
theorem ST_step2_of_pins (hNew : STNewKLK d) (hLWT : STLWT d) (hEMe : STEMn2Exp d)
    (hMart : STGridMart d) (hK2 : STK2decay d) (hNet : STNetLift2 d)
    (hScale : STScaleExists d) (hOpt : STOptL2 d) (hClos : STLocalAvgOfL2 d) : STStep2 d := by
  intro hd3 κ ε 𝔡 hκ hε h𝔡
  have hd : 0 < d := by omega
  obtain ⟨C, δ₀, hC, hδ₀, hnew⟩ := hNew hd3 κ 𝔡 hκ h𝔡
  obtain ⟨C₀, hC₀, hmart⟩ := hMart
  obtain ⟨C_K, hCK, hK2at⟩ := hK2 hd3 κ 𝔡 hκ h𝔡
  obtain ⟨cB, hcB, hBc⟩ := ST_Bdata_holds hd κ ε 𝔡 hκ hε h𝔡
  obtain ⟨𝔠₀, h𝔠₀, hOptat⟩ := hOpt κ ε 𝔡 hκ hε h𝔡
  have hCd : 0 < 3 * C + 1 := by positivity
  obtain ⟨𝔠d, h𝔠d⟩ : ∃ 𝔠d : ℝ, 𝔠d = min (min (1 / 100) (1 / (60 * (3 * C + 1)))) 𝔠₀ :=
    ⟨_, rfl⟩
  have h𝔠dpos : 0 < 𝔠d := by
    rw [h𝔠d]; exact lt_min (lt_min (by norm_num) (by positivity)) h𝔠₀
  have h𝔠d1 : 𝔠d ≤ 1 / 100 := by
    rw [h𝔠d]; exact (min_le_left _ _).trans (min_le_left _ _)
  have h𝔠d3 : 𝔠d ≤ 𝔠₀ := by rw [h𝔠d]; exact min_le_right _ _
  have h𝔠d2 : (3 * C + 1) * 𝔠d ≤ 1 / 60 := by
    have h : 𝔠d ≤ 1 / (60 * (3 * C + 1)) := by
      rw [h𝔠d]; exact (min_le_left _ _).trans (min_le_right _ _)
    calc (3 * C + 1) * 𝔠d ≤ (3 * C + 1) * (1 / (60 * (3 * C + 1))) :=
          mul_le_mul_of_nonneg_left h hCd.le
      _ = 1 / 60 := by field_simp
  refine ⟨3 * C + 1, hCd, 𝔠d, h𝔠dpos, h𝔠d1, ?_⟩
  intro 𝔠 sz z hflow s t hs hsl hst htT hLK hDec hCon hS1L hS1W
  have hst' : ∀ n, s n ≤ t n := fun n => (hst n).le
  have hsz : sz.SizeTendsto := hflow.1.2.2.1
  have h𝔠 : 0 < 𝔠 := hflow.1.1
  have hband : sz.Bandwidth 𝔠 := hflow.1.2.2.2.1
  have hWO : sz.WO 𝔡 := hflow.1.2.2.2.2
  have ht1 : ∀ n, t n < 1 := fun n =>
    lt_of_le_of_lt (htT n) (lemT_lt_one (ST_flow_im_pos sz hflow n))
  obtain ⟨c, hc, hBc'⟩ := hBc 𝔠
  have hBd := hBc' sz z hflow t (fun n => (hs n).trans (hst' n)) htT
  -- the deterministic `𝒦^{(2)}` bound, eventually
  have hK2e : ∀ᶠ n in atTop, ∀ u D (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)), s n ≤ u →
      u ≤ t n → 0 ≤ D →
      ‖STKloop sz n (STflowE z n) u σ a‖ ≤
        C_K * STprof sz n u D ((sz.L n : ℕ) : ℝ) (a 0) (a 1) := by
    filter_upwards [hWO] with n hn u D σ a hsu hut hD
    have him := ST_flow_im_pos sz hflow n
    have hlam : 0 < sz.lam n :=
      lt_of_lt_of_le (Real.rpow_pos_of_pos (by exact_mod_cast sz.W_pos n) _) hn.1
    exact hK2at sz n (STflowE z n) u D hlam hn.2 ((abs_lemE_le him).trans (hflow.2 n).1)
      ((hs n).trans hsu) (lt_of_le_of_lt hut (ht1 n)) hD σ a
  -- the closure arithmetic `r^{C_d} b^{1/5} ≤ b^{1/6}`
  have hq : ∀ᶠ n in atTop, ∀ u, s n ≤ u → u ≤ t n →
      ((1 - s n) / (1 - u)) ^ (3 * C + 1) * (sz.Bctl n u) ^ (1 / 5 : ℝ) ≤
          (sz.Bctl n u) ^ (1 / 6 : ℝ) ∧
        0 ≤ ((1 - s n) / (1 - u)) ^ (3 * C + 1) * (sz.Bctl n u) ^ (1 / 5 : ℝ) ∧
        (sz.Bctl n u) ^ (1 / 6 : ℝ) ≤ 1 := by
    filter_upwards [hBd, hCon, hsize_ev sz hsz] with n hbdn hconn hN1 u hsu hut
    have hN1' : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast hN1
    have hlt1 : ∀ v, v ≤ t n → v < 1 := fun v hv => lt_of_le_of_lt hv (ht1 n)
    have hs1 : 0 < 1 - s n := by have := hlt1 (s n) (hst' n); linarith
    have ht1' : 0 < 1 - t n := by have := hlt1 (t n) le_rfl; linarith
    have hbpos := STBctl_pos sz n (hlt1 u hut)
    have hbt := STBctl_pos sz n (hlt1 (t n) le_rfl)
    have hbtn1 : sz.Bctl n (t n) ≤ 1 :=
      (hbdn (t n) ((hs n).trans (hst' n)) le_rfl).2.trans
        (Real.rpow_le_one_of_one_le_of_nonpos hN1' (by linarith))
    have hr1 : 1 ≤ (1 - s n) / (1 - u) := by
      rw [le_div_iff₀ (by linarith [hlt1 u hut])]; linarith
    have hrb := ST_ratio_le hs1 ht1' hsu hut hbt hconn.1
    have hbu1 : sz.Bctl n u ≤ 1 := (STBctl_mono sz n hut (hlt1 _ le_rfl)).trans hbtn1
    have hb6 : (sz.Bctl n u) ^ (1 / 6 : ℝ) ≤ 1 := Real.rpow_le_one hbpos.le hbu1 (by norm_num)
    refine ⟨ST_hq_arith hCd.le hr1 hrb h𝔠dpos.le hbpos (STBctl_mono sz n hut (hlt1 _ le_rfl))
      hbtn1 h𝔠d2, mul_nonneg (Real.rpow_nonneg (by linarith) _) (Real.rpow_nonneg hbpos.le _),
      hb6⟩
  -- the base of the iteration and the scale family
  have hbase0 := hOptat 𝔠d h𝔠dpos h𝔠d3 𝔠 sz z hflow s t hs hst' htT hLK hCon hS1L hS1W
  have hbase : STScaleInv sz (STflowE z) s t (fun n u => 0) :=
    ST_base_inv sz hsz hst' hCK hK2e hbase0
  obtain ⟨Kseq, hAdm⟩ := hScale κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow s t hs hst' htT
  have hKz : Kseq 0 = fun n u => 0 := funext fun n => funext fun u => hAdm.1 n u
  have hbase' : STScaleInv sz (STflowE z) s t (Kseq 0) := by rw [hKz]; exact hbase
  -- one self-improving step at every level
  have hSelf : ∀ Kf : ℕ → ℝ → ℝ, STScaleOk sz s t Kf → STScaleInv sz (STflowE z) s t Kf →
      STSelfImp sz (3 * C + 1) (STflowE z) s t Kf := fun Kf hKok hinv =>
    ST_selfImprove sz hLWT hEMe hd hκ hε h𝔡 hflow hs hst' htT hC hδ₀ hC₀ hnew hmart h𝔠dpos h𝔠d2
      hDec hCon hS1W hcB hc hBd Kf hKok hinv
  have hdec := ST_decay_pt sz hsz hst' hCK hSelf hK2e hq Kseq hAdm hbase'
  have hL2 := ST_L2_decay_pt sz hsz hst' hs ht1 hCK h𝔠 hband hdec hK2e hq
  obtain ⟨hLocPT, hAvgPT⟩ := hClos κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow s t hs hst' htT hS1W hL2
  obtain ⟨hl, ha, hd'⟩ := hNet κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow s t hs hst' htT (3 * C + 1) hLocPT hAvgPT hdec
  exact ST_concl_of_step2 sz hl ha hd'

end Step2

end RBM.Gauss.Sizes

namespace RBM.Gauss.Sizes

/-- **The probe's form of `STStep2`**: the same statement as the merged `STStep2` with the conclusion
`STStep2Local ∧ STStep2Avg ∧ STStep2Decay` (the three parts, single-charge averaged law). -/
def STStep2Parts (d : ℕ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∃ Cd : ℝ, 0 < Cd ∧ ∃ 𝔠d : ℝ, 0 < 𝔠d ∧ 𝔠d ≤ 1 / 100 ∧
      ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z →
        ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n ≤ lemT (z n)) → (∀ n, s n < t n) →
          (∀ n, t n ≤ lemT (z n)) →
          STLK sz (STflowE z) s → STDecay sz (STflowE z) s → STConStInd sz 𝔠d s t →
          STStep1Loop sz (STflowE z) s t → STStep1Weak sz (STflowE z) s t →
            STStep2Local sz (STflowE z) s t ∧ STStep2Avg sz (STflowE z) s t ∧
              STStep2Decay sz Cd (STflowE z) s t

/-- **`STStep2Parts` gives `STStep2`** (the form consumed by Steps 3-4): the same statement with the conclusion
`STStep2Concl` (the merged bundle of T2049). -/
theorem ST_step2_concl {d : ℕ} (h : STStep2Parts d) :
    3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
      ∃ Cd : ℝ, 0 < Cd ∧ ∃ 𝔠d : ℝ, 0 < 𝔠d ∧ 𝔠d ≤ 1 / 100 ∧
        ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z →
          ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n ≤ lemT (z n)) → (∀ n, s n < t n) →
            (∀ n, t n ≤ lemT (z n)) →
            STLK sz (STflowE z) s → STDecay sz (STflowE z) s → STConStInd sz 𝔠d s t →
            STStep1Loop sz (STflowE z) s t → STStep1Weak sz (STflowE z) s t →
              STStep2Concl sz (STflowE z) s t Cd := by
  intro hd κ ε 𝔡 hκ hε h𝔡
  obtain ⟨Cd, hCd, 𝔠d, h0, h1, hall⟩ := h hd κ ε 𝔡 hκ hε h𝔡
  refine ⟨Cd, hCd, 𝔠d, h0, h1, fun 𝔠 sz z hflow s t hs hsl hst htT hLK hDec hCon hS1L hS1W => ?_⟩
  obtain ⟨hL, hA, hD⟩ := hall 𝔠 sz z hflow s t hs hsl hst htT hLK hDec hCon hS1L hS1W
  exact ST_concl_of_step2 sz hL hA hD

end RBM.Gauss.Sizes

/-! ## 12.2 The general-`n` loop dynamics shared by Steps 2-4: `Sol_CalL` and `lem:DIfREP` on the grid

The paper states `Sol_CalL` (`(int_K-L_ST)`, `3_5:134`) and `lem:DIfREP` (`(aaswtghh)`, `(alu9_STime)`,
`3_5:218`) for every loop length `n`; Step 2 uses `n = 2` (`STGridMart`), Steps 3-4 use every `n`.
`STGridRepN d` (merged, `Step34Pins`/`Step2Defs`) is the grid form for **all** loop lengths `m ≥ 2`.
The model-level terms are written once more for an arbitrary fine matrix `H` (suffix `M`, merged) so that
they can be evaluated on the grid walk `pathH`; `STLIM_seqHflow` etc. are `rfl`.
`ST_gridMart_of_repN` compiles the consistency with the loop-length-`2` pin used by the skeleton. -/

namespace RBM.Gauss.Sizes

open MeasureTheory Filter Matrix RBM RBM.Loop RBM.Gauss RBM.Gauss.Sizes RBM.Path

end RBM.Gauss.Sizes

namespace RBM.Gauss.Sizes

open RBM RBM.Loop RBM.Path

section MatrixN

variable {d : ℕ} (sz : Sizes d)

theorem STLIM_seqHflow (n : ℕ) (E τ : ℝ) (ω : sz.SeqΩ) (I : LoopIdx (Zd d (sz.L n))) :
    STLIM sz n E τ (sz.seqHflow n τ ω) I = STLI sz n E τ ω I := rfl

theorem STLKIM_seqHflow (n : ℕ) (E τ : ℝ) (ω : sz.SeqΩ) (I : LoopIdx (Zd d (sz.L n))) :
    STLKIM sz n E τ (sz.seqHflow n τ ω) I = STLKI sz n E τ ω I := rfl

theorem STksimLKM_seqHflow (n : ℕ) (E τ : ℝ) (ω : sz.SeqΩ) (l : ℕ) (I : LoopIdx (Zd d (sz.L n))) :
    STksimLKM sz n E τ (sz.seqHflow n τ ω) l I = STksimLK sz n E τ ω l I := rfl

theorem STelklkM_seqHflow (n : ℕ) (E τ : ℝ) (ω : sz.SeqΩ) (I : LoopIdx (Zd d (sz.L n))) :
    STelklkM sz n E τ (sz.seqHflow n τ ω) I = STelklk sz n E τ ω I := rfl

theorem STegtM_seqHflow (n : ℕ) (E τ : ℝ) (ω : sz.SeqΩ) (I : LoopIdx (Zd d (sz.L n))) :
    STegtM sz n E τ (sz.seqHflow n τ ω) I = STegt sz n E τ ω I := rfl

theorem STeeM_seqHflow (n : ℕ) (E τ : ℝ) (ω : sz.SeqΩ) {m : ℕ} (σ : Fin m → Bool)
    (a a' : Fin m → Zd d (sz.L n)) :
    STeeM sz n E τ (sz.seqHflow n τ ω) σ a a' = STee sz n E τ ω σ a a' := rfl

end MatrixN

end RBM.Gauss.Sizes

namespace RBM.Gauss.Sizes

open RBM RBM.Loop RBM.Path

section GridN

variable {d : ℕ} (sz : Sizes d)

end GridN

end RBM.Gauss.Sizes

namespace RBM.Gauss.Sizes

open RBM RBM.Loop RBM.Path

section Ident

variable {d : ℕ} (sz : Sizes d)

/-- `STLKM = STLKIM ∘ KLloopOf` (the loop `loopFine` of `(σ, a)` is `loopL` of its list index). -/
theorem STLKM_eq_STLKIM (n : ℕ) (E u : ℝ)
    (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) {m : ℕ}
    (σ : Fin m → Bool) (a : Fin m → Zd d (sz.L n)) :
    STLKM sz n E u H σ a = STLKIM sz n E u H (KLloopOf d (sz.L n) σ a) := by
  unfold STLKM STLKIM STLM STLIM STKloop
  rw [loopFine, loopM_eq_loopL]
  rfl

theorem STLM_eq_STLIM (n : ℕ) (E u : ℝ)
    (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) {m : ℕ}
    (σ : Fin m → Bool) (a : Fin m → Zd d (sz.L n)) :
    STLM sz n E u H σ a = STLIM sz n E u H (KLloopOf d (sz.L n) σ a) := by
  unfold STLM STLIM
  rw [loopFine, loopM_eq_loopL]
  rfl

theorem STgA_eq_STgAN (s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) (E : ℝ) (σ : Fin 2 → Bool)
    (a : Fin 2 → Zd d (sz.L n)) (k : ℕ) (ω : PathΩ sz) :
    STgA sz s t K n E σ a k ω = STgAN sz s t K n E σ a k ω :=
  STLKM_eq_STLKIM sz n E _ _ σ a

/-- `Θ^{(2)}` of §1 is the merged `ThetaN` at `m = 2`. -/
theorem STthetaOp_eq_ThetaN (n : ℕ) (E u : ℝ) (σ : Fin 2 → Bool)
    (A : (Fin 2 → Zd d (sz.L n)) → ℂ) (a : Fin 2 → Zd d (sz.L n)) :
    STthetaOp sz n E u σ A a =
      ThetaN d (sz.L n) (sz.lam n) (fun i => mSigma E (σ i)) u A a := by
  have e0 : finRotate 2 0 = 1 := by decide
  have e1 : finRotate 2 1 = 0 := by decide
  have hcyc : ∀ i : Fin 2, cycProd (fun i => mSigma E (σ i)) i =
      STmsig E (σ 0) * STmsig E (σ 1) := by
    rw [Fin.forall_fin_two]
    refine ⟨?_, ?_⟩
    · simp only [cycProd, e0]; rfl
    · simp only [cycProd, e1]; rw [mul_comm]; rfl
  unfold STthetaOp ThetaN thetaKer
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun b _ => ?_
  rw [hcyc i, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul]

/-- The two pieces of the cut `(k,l) = (1,2)` of a loop of length `2`. -/
theorem KLloopOf_cutL (n : ℕ) (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) (x : Zd d (sz.L n)) :
    (KLloopOf d (sz.L n) σ a).cutGlueL 1 2 x = KLloopOf d (sz.L n) σ ![x, a 1] := by
  simp [KLloopOf, LoopIdx.cutGlueL, List.ofFn_succ]

theorem KLloopOf_cutR (n : ℕ) (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) (y : Zd d (sz.L n)) :
    (KLloopOf d (sz.L n) σ a).cutGlueR 1 2 y = KLloopOf d (sz.L n) σ ![a 0, y] := by
  simp [KLloopOf, LoopIdx.cutGlueR, List.ofFn_succ]

theorem KLloopOf_length2 (n : ℕ) (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) :
    (KLloopOf d (sz.L n) σ a).length = 2 := by
  simp [KLloopOf, LoopIdx.length]

/-- `ℰ^{(𝓛-𝒦)×(𝓛-𝒦),(2)}` of §1 is the general-`n` term at the loop length `2`. -/
theorem STELKLKM_eq_STelklkM (n : ℕ) (E u : ℝ)
    (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (σ : Fin 2 → Bool)
    (a : Fin 2 → Zd d (sz.L n)) :
    STELKLKM sz n E u H σ a = STelklkM sz n E u H (KLloopOf d (sz.L n) σ a) := by
  unfold STELKLKM STelklkM
  rw [KLloopOf_length2]
  have h1 : Finset.Icc 1 2 = {1, 2} := by decide
  have h2 : Finset.Ioc 1 2 = {2} := by decide
  have h3 : Finset.Ioc 2 2 = ∅ := by decide
  rw [h1, Finset.sum_pair (by norm_num : (1 : ℕ) ≠ 2), h2, h3]
  simp only [Finset.sum_singleton, Finset.sum_empty, add_zero]
  congr 1

theorem KLloopOf_cutGlue1 (n : ℕ) (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n))
    (y : Zd d (sz.L n)) :
    (KLloopOf d (sz.L n) σ a).cutGlue 1 y =
      KLloopOf d (sz.L n) ![σ 0, σ 0, σ 1] ![y, a 0, a 1] := by
  simp [KLloopOf, LoopIdx.cutGlue, List.ofFn_succ]

theorem KLloopOf_cutGlue2 (n : ℕ) (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n))
    (y : Zd d (sz.L n)) :
    (KLloopOf d (sz.L n) σ a).cutGlue 2 y =
      KLloopOf d (sz.L n) ![σ 0, σ 1, σ 1] ![a 0, y, a 1] := by
  simp [KLloopOf, LoopIdx.cutGlue, List.ofFn_succ]

theorem STavgM_eq_STavgErrM (n : ℕ) (E u : ℝ)
    (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (σ : Bool)
    (x : Zd d (sz.L n)) : STavgM sz n E u H σ x = STavgErrM sz n E u H σ x := by
  unfold STavgM STavgErrM
  rw [STLM_eq_STLIM]
  have : KLloopOf d (sz.L n) (fun _ : Fin 1 => σ) (fun _ => x) = ⟨[σ], [x]⟩ := by
    simp [KLloopOf, List.ofFn_succ]
  rw [this]
  rfl

/-- `ℰ^{G̃,(2)}` of §1 is the general-`n` term at the loop length `2`. -/
theorem STEGtM_eq_STegtM (n : ℕ) (E u : ℝ)
    (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (σ : Fin 2 → Bool)
    (a : Fin 2 → Zd d (sz.L n)) :
    STEGtM sz n E u H σ a = STegtM sz n E u H (KLloopOf d (sz.L n) σ a) := by
  unfold STEGtM STegtM
  rw [KLloopOf_length2]
  have h1 : Finset.Icc 1 2 = {1, 2} := by decide
  rw [h1, Finset.sum_pair (by norm_num : (1 : ℕ) ≠ 2)]
  simp only [Finset.sum_add_distrib, KLloopOf_cutGlue1, KLloopOf_cutGlue2, STavgM_eq_STavgErrM,
    STLM_eq_STLIM]
  congr 1

theorem STeeLoop_one (n : ℕ) (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) (b b' : Zd d (sz.L n)) :
    STeeLoop (List.ofFn σ) (List.ofFn a) (List.ofFn a) 1 b b' =
      KLloopOf d (sz.L n) ![σ 0, σ 1, σ 0, !(σ 0), !(σ 1), !(σ 0)] ![a 0, a 1, b', a 1, a 0, b] := by
  simp [STeeLoop, KLloopOf, List.ofFn_succ]

theorem STeeLoop_two (n : ℕ) (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) (b b' : Zd d (sz.L n)) :
    STeeLoop (List.ofFn σ) (List.ofFn a) (List.ofFn a) 2 b b' =
      KLloopOf d (sz.L n) ![σ 1, σ 0, σ 1, !(σ 1), !(σ 0), !(σ 1)] ![a 1, a 0, b', a 0, a 1, b] := by
  simp [STeeLoop, KLloopOf, List.ofFn_succ]

/-- `(ℰ⊗ℰ)^{M,(2)}` of §1 is the general-`n` quadratic-variation loop at the loop length `2`
(`a' = a`). -/
theorem STEEM_eq_STeeM (n : ℕ) (E u : ℝ)
    (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (σ : Fin 2 → Bool)
    (a : Fin 2 → Zd d (sz.L n)) :
    STEEM sz n E u H σ a = STeeM sz n E u H σ a a := by
  unfold STEEM STEEkM STeeM
  have h1 : Finset.Icc 1 2 = {1, 2} := by decide
  rw [h1, Finset.sum_pair (by norm_num : (1 : ℕ) ≠ 2), mul_add]
  simp only [STeeLoop_one, STeeLoop_two, STLIM]
  rfl

/-- The drift of §2.3 (`n = 2`) is the general-`n` drift at the loop length `2` (`Σ_{l_K=3}^{2}` is empty). -/
theorem STgDrift_eq_STgDriftN (s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) (E : ℝ) (σ : Fin 2 → Bool)
    (a : Fin 2 → Zd d (sz.L n)) (k : ℕ) (ω : PathΩ sz) :
    STgDrift sz s t K n E σ a k ω = STgDriftN sz s t K n E σ a k ω := by
  unfold STgDrift STgDriftN
  rw [STthetaOp_eq_ThetaN, STELKLKM_eq_STelklkM, STEGtM_eq_STegtM]
  have h3 : Finset.Icc 3 2 = (∅ : Finset ℕ) := by decide
  rw [h3, Finset.sum_empty, add_zero]
  have hf : (STLKM sz n E (gridTime s t K n k) (pathH sz s t K n k ω) σ) =
      fun a' => STLKIM sz n E (gridTime s t K n k) (pathH sz s t K n k ω)
        (KLloopOf d (sz.L n) σ a') := funext fun a' => STLKM_eq_STLKIM sz n E _ _ σ a'
  rw [hf]

end Ident

section Consistency

/-- **The pin `STGridRepN` (every loop length) implies the pin `STGridMart` (loop length `2`) used by the
skeleton**: the first three clauses are the case `m = 2` of the general ones, with the vocabulary of §1
identified with the general-`n` vocabulary at length `2` (`STLKM_eq_STLKIM`, `STthetaOp_eq_ThetaN`,
`STELKLKM_eq_STelklkM`, `STEGtM_eq_STegtM`, `STEEM_eq_STeeM`). -/
theorem ST_gridMart_of_repN {d : ℕ} (h : STGridRepN d) : STGridMart d := by
  obtain ⟨C₀, hC₀, hAt⟩ := h 2 le_rfl
  refine ⟨C₀, hC₀, ?_⟩
  intro κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow s t hs hst htT D hD
  obtain ⟨CK, hCK, hK⟩ := hAt κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow s t hs hst htT D hD
  refine ⟨CK, hCK, fun K hK0 hKN => ?_⟩
  obtain ⟨Mart, Rem, hid, hrem, htail, -⟩ := hK K hK0 hKN
  refine ⟨Mart, Rem, ?_, hrem, ?_⟩
  · intro n i
    filter_upwards [hid n i] with ω hω k hk
    simp only [STgA_eq_STgAN, STgDrift_eq_STgDriftN]
    exact hω k hk
  · intro ε' hε'
    filter_upwards [htail ε' hε'] with n hn i
    simp only [STEEM_eq_STeeM]
    exact hn i

end Consistency

end RBM.Gauss.Sizes

namespace RBM.Gauss.Sizes

open MeasureTheory Filter RBM RBM.Gauss RBM.Gauss.Sizes RBM.Path

/-- **The compiled skeleton with the general-`n` grid pin**: the same theorem as `ST_step2_of_pins`, with
`STGridRepN` (every loop length) instead of `STGridMart` (loop length `2`). -/
theorem ST_step2_of_pinsN {d : ℕ} (hNew : STNewKLK d) (hLWT : STLWT d) (hEMe : STEMn2Exp d)
    (hRep : STGridRepN d) (hK2 : STK2decay d) (hNet : STNetLift2 d) (hScale : STScaleExists d)
    (hOpt : STOptL2 d) (hClos : STLocalAvgOfL2 d) : STStep2 d :=
  ST_step2_of_pins hNew hLWT hEMe (ST_gridMart_of_repN hRep) hK2 hNet hScale hOpt hClos

end RBM.Gauss.Sizes

/-! ## Corollaries (new): the pins now proved are discharged

`stK2decay_holds` (`Induction/Step2K2.lean`, T2093), `stNetLift2_holds` (`Path/NetLift2.lean`) and
`stScaleExists_holds` (`Induction/Step2Scale.lean`, T2081) prove `STK2decay d`, `STNetLift2 d`,
`STScaleExists d` for every `d` (no `3 ≤ d` in the pin statements).  The primed corollaries keep the
six remaining pins `STNewKLK`, `STLWT`, `STEMn2Exp`, `STGridMart` (or `STGridRepN`), `STOptL2`,
`STLocalAvgOfL2` as hypotheses.  `ST_step2_of_pinsLW'` replaces `STLWT` by `LWtermExp` through the bridge
`STLWT_of_LWtermExp`, which needs `3 ≤ d` (DECISIONS section 29). -/

namespace RBM.Gauss.Sizes

open MeasureTheory Filter RBM RBM.Gauss RBM.Gauss.Sizes RBM.Path

/-- `ST_step2_of_pins` with `STK2decay`, `STNetLift2`, `STScaleExists` discharged
(`stK2decay_holds`, `stNetLift2_holds`, `stScaleExists_holds`); the remaining pins are
`STNewKLK`, `STLWT`, `STEMn2Exp`, `STGridMart`, `STOptL2`, `STLocalAvgOfL2`. -/
theorem ST_step2_of_pins' {d : ℕ} (hNew : STNewKLK d) (hLWT : STLWT d) (hEMe : STEMn2Exp d)
    (hMart : STGridMart d) (hOpt : STOptL2 d) (hClos : STLocalAvgOfL2 d) : STStep2 d :=
  ST_step2_of_pins hNew hLWT hEMe hMart (stK2decay_holds d) (stNetLift2_holds d)
    (stScaleExists_holds d) hOpt hClos

/-- `ST_step2_of_pinsN` with `STK2decay`, `STNetLift2`, `STScaleExists` discharged; the remaining
pins are `STNewKLK`, `STLWT`, `STEMn2Exp`, `STGridRepN`, `STOptL2`, `STLocalAvgOfL2`. -/
theorem ST_step2_of_pinsN' {d : ℕ} (hNew : STNewKLK d) (hLWT : STLWT d) (hEMe : STEMn2Exp d)
    (hRep : STGridRepN d) (hOpt : STOptL2 d) (hClos : STLocalAvgOfL2 d) : STStep2 d :=
  ST_step2_of_pinsN hNew hLWT hEMe hRep (stK2decay_holds d) (stNetLift2_holds d)
    (stScaleExists_holds d) hOpt hClos

/-- `ST_step2_of_pinsN'` with `STLWT` obtained from the light-weight pin `LWtermExp` (bridge
`STLWT_of_LWtermExp`, `3 ≤ d`). -/
theorem ST_step2_of_pinsLW' {d : ℕ} (hd : 3 ≤ d) (hNew : STNewKLK d) (hLW : LWtermExp d)
    (hEMe : STEMn2Exp d) (hRep : STGridRepN d) (hOpt : STOptL2 d) (hClos : STLocalAvgOfL2 d) :
    STStep2 d :=
  ST_step2_of_pinsN' hNew (STLWT_of_LWtermExp hd hLW) hEMe hRep hOpt hClos

/-- The deterministic `𝒦^{(2)}` bound of `ST_step2_of_pins` (`hK2e`), eventually in `n`, from the
proved `stK2decay_holds` and the flow: for every `d ≥ 3` and every flow with `0 ≤ s_n`, `t_n < 1`. -/
theorem ST_K2e_of_flow {d : ℕ} (hd3 : 3 ≤ d) {κ ε 𝔠 𝔡 : ℝ} (hκ : 0 < κ) (h𝔡 : 0 < 𝔡)
    {sz : Sizes d} {z : ℕ → ℂ} (hflow : STFlow sz κ ε 𝔠 𝔡 z) {s t : ℕ → ℝ}
    (hs : ∀ n, 0 ≤ s n) (ht1 : ∀ n, t n < 1) :
    ∃ C_K : ℝ, 0 < C_K ∧ ∀ᶠ n in atTop, ∀ u D (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)),
      s n ≤ u → u ≤ t n → 0 ≤ D →
      ‖STKloop sz n (STflowE z n) u σ a‖ ≤ C_K * STprof sz n u D ((sz.L n : ℕ) : ℝ) (a 0) (a 1) := by
  obtain ⟨C_K, hCK, hK2at⟩ := stK2decay_holds d hd3 κ 𝔡 hκ h𝔡
  have hWO : sz.WO 𝔡 := hflow.1.2.2.2.2
  refine ⟨C_K, hCK, ?_⟩
  filter_upwards [hWO] with n hn u D σ a hsu hut hD
  have him := ST_flow_im_pos sz hflow n
  have hlam : 0 < sz.lam n :=
    lt_of_lt_of_le (Real.rpow_pos_of_pos (by exact_mod_cast sz.W_pos n) _) hn.1
  exact hK2at sz n (STflowE z n) u D hlam hn.2 ((abs_lemE_le him).trans (hflow.2 n).1)
    ((hs n).trans hsu) (lt_of_le_of_lt hut (ht1 n)) hD σ a

/-- The closure arithmetic of `ST_step2_of_pins` (`hq`), eventually in `n`, at `C_d = 3C + 1`: from
`(con_st_ind)` and the size data `cB W^{-d} ≤ B_{u,0} ≤ N^{-c}`. -/
theorem ST_hq_of_data {d : ℕ} (sz : Sizes d) (hsz : sz.SizeTendsto) {s t : ℕ → ℝ}
    (hs : ∀ n, 0 ≤ s n) (hst' : ∀ n, s n ≤ t n) (ht1 : ∀ n, t n < 1) {C 𝔠d cB c : ℝ}
    (hC : 0 < C) (h𝔠dpos : 0 < 𝔠d) (h𝔠d2 : (3 * C + 1) * 𝔠d ≤ 1 / 60)
    (hBd : ∀ᶠ n in atTop, ∀ u : ℝ, 0 ≤ u → u ≤ t n →
      cB * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ sz.Bctl n u ∧ sz.Bctl n u ≤ ((sz.size n : ℕ) : ℝ) ^ (-c))
    (hc : 0 < c) (hCon : STConStInd sz 𝔠d s t) :
    ∀ᶠ n in atTop, ∀ u, s n ≤ u → u ≤ t n →
      ((1 - s n) / (1 - u)) ^ (3 * C + 1) * (sz.Bctl n u) ^ (1 / 5 : ℝ) ≤
          (sz.Bctl n u) ^ (1 / 6 : ℝ) ∧
        0 ≤ ((1 - s n) / (1 - u)) ^ (3 * C + 1) * (sz.Bctl n u) ^ (1 / 5 : ℝ) ∧
        (sz.Bctl n u) ^ (1 / 6 : ℝ) ≤ 1 := by
  have hCd : 0 < 3 * C + 1 := by positivity
  filter_upwards [hBd, hCon, hsize_ev sz hsz] with n hbdn hconn hN1 u hsu hut
  have hN1' : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast hN1
  have hlt1 : ∀ v, v ≤ t n → v < 1 := fun v hv => lt_of_le_of_lt hv (ht1 n)
  have hs1 : 0 < 1 - s n := by have := hlt1 (s n) (hst' n); linarith
  have ht1' : 0 < 1 - t n := by have := hlt1 (t n) le_rfl; linarith
  have hbpos := STBctl_pos sz n (hlt1 u hut)
  have hbt := STBctl_pos sz n (hlt1 (t n) le_rfl)
  have hbtn1 : sz.Bctl n (t n) ≤ 1 :=
    (hbdn (t n) ((hs n).trans (hst' n)) le_rfl).2.trans
      (Real.rpow_le_one_of_one_le_of_nonpos hN1' (by linarith))
  have hr1 : 1 ≤ (1 - s n) / (1 - u) := by
    rw [le_div_iff₀ (by linarith [hlt1 u hut])]; linarith
  have hrb := ST_ratio_le hs1 ht1' hsu hut hbt hconn.1
  have hbu1 : sz.Bctl n u ≤ 1 := (STBctl_mono sz n hut (hlt1 _ le_rfl)).trans hbtn1
  have hb6 : (sz.Bctl n u) ^ (1 / 6 : ℝ) ≤ 1 := Real.rpow_le_one hbpos.le hbu1 (by norm_num)
  refine ⟨ST_hq_arith hCd.le hr1 hrb h𝔠dpos.le hbpos (STBctl_mono sz n hut (hlt1 _ le_rfl))
    hbtn1 h𝔠d2, mul_nonneg (Real.rpow_nonneg (by linarith) _) (Real.rpow_nonneg hbpos.le _),
    hb6⟩

end RBM.Gauss.Sizes

/-! ## Instances (new): every target at `d = 3`

The data are the merged `RBM.Gauss.SizesInst.sz0` (`L_n = 4(n+1)`, `W_n = (2(n+1))^5`,
`lam_n = (2(n+1))^{-6}`, `N_n = (W_n L_n)^3`), the flow `z0` (`flow_z0`, `κ = ε = 𝔡 = 1/10`,
`𝔠 = 1/6`, `Im z_n = N_n^{-4/5}`), the times `s ≡ 0`, `t ≡ 1/16 ≤ lemT z_n` and the pin constants
`C = 1`, so `C_d = 3C + 1 = 4`, `𝔠_d = 1/240` with `(3C+1) 𝔠_d = 1/60` (preflight table).  In every example
the deterministic hypotheses are discharged: `SizeTendsto`, `Bandwidth`, `STFlow`, the time ranges,
`STConStInd`, the size data `cB W^{-3} ≤ B ≤ N^{-c}` (`ST_Bdata_holds`), the deterministic `𝒦^{(2)}` bound
(`ST_K2e_of_flow`), the closure arithmetic `hq` (`ST_hq_of_data`), the scale family (`stScaleExists_holds`).
What stays a hypothesis of an example is a pin or a stochastic premise of the statement. -/

namespace RBM.Gauss.Step2IterateInst

open RBM RBM.Gauss RBM.Gauss.Sizes RBM.Gauss.SizesInst RBM.Gauss.InductionDefsInst
  RBM.Gauss.Step2DefsInst RBM.Path Filter

theorem hs0 : ∀ n, 0 ≤ sInst n := fun _ => le_rfl

theorem hst : ∀ n, sInst n ≤ tInst n := fun n => by simp only [sInst, tInst]; norm_num

theorem tInst_nonneg : ∀ n, 0 ≤ tInst n := fun n => by simp only [tInst]; norm_num

theorem ht1 : ∀ n, tInst n < 1 := fun n => by simp only [tInst]; norm_num

theorem htT : ∀ n, tInst n ≤ lemT (z0 n) := fun n => sixteenth_le_lemT n

/-- **`ST_Bdata_holds`, instantiated**: `cB W^{-3} ≤ W^{-3} B_{u,0} ≤ N^{-c}` for `u ∈ [0, 1/16]`,
`d = 3`, `κ = ε = 𝔡 = 1/10`, `𝔠 = 1/6`, the data `(sz0, z0)`. -/
theorem bdata_sz0 :
    ∃ cB c : ℝ, 0 < cB ∧ 0 < c ∧ ∀ᶠ n in atTop, ∀ u : ℝ, 0 ≤ u → u ≤ tInst n →
      cB * (((sz0.W n : ℕ) : ℝ) ^ 3)⁻¹ ≤ sz0.Bctl n u ∧
        sz0.Bctl n u ≤ ((sz0.size n : ℕ) : ℝ) ^ (-c) := by
  obtain ⟨cB, hcB, hall⟩ := ST_Bdata_holds (by norm_num : 0 < 3) (1 / 10) (1 / 10) (1 / 10)
    (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨c, hc, hall'⟩ := hall (1 / 6)
  exact ⟨cB, c, hcB, hc, hall' sz0 z0 flow_z0 tInst tInst_nonneg htT⟩

noncomputable def bdata_cB : ℝ := bdata_sz0.choose
noncomputable def bdata_c : ℝ := bdata_sz0.choose_spec.choose

theorem bdata_spec : 0 < bdata_cB ∧ 0 < bdata_c ∧ ∀ᶠ n in atTop, ∀ u : ℝ, 0 ≤ u → u ≤ tInst n →
    bdata_cB * (((sz0.W n : ℕ) : ℝ) ^ 3)⁻¹ ≤ sz0.Bctl n u ∧
      sz0.Bctl n u ≤ ((sz0.size n : ℕ) : ℝ) ^ (-bdata_c) :=
  bdata_sz0.choose_spec.choose_spec

/-- The deterministic `𝒦^{(2)}` bound at the data. -/
theorem k2_sz0 : ∃ C_K : ℝ, 0 < C_K ∧ ∀ᶠ n in atTop, ∀ u D (σ : Fin 2 → Bool)
    (a : Fin 2 → Zd 3 (sz0.L n)), sInst n ≤ u → u ≤ tInst n → 0 ≤ D →
    ‖STKloop sz0 n (STflowE z0 n) u σ a‖ ≤
      C_K * STprof sz0 n u D ((sz0.L n : ℕ) : ℝ) (a 0) (a 1) :=
  ST_K2e_of_flow (by norm_num) (by norm_num) (by norm_num) flow_z0 hs0 ht1

noncomputable def CK0 : ℝ := k2_sz0.choose
theorem CK0_pos : 0 < CK0 := k2_sz0.choose_spec.1
theorem hK2_sz0 : ∀ᶠ n in atTop, ∀ u D (σ : Fin 2 → Bool)
    (a : Fin 2 → Zd 3 (sz0.L n)), sInst n ≤ u → u ≤ tInst n → 0 ≤ D →
    ‖STKloop sz0 n (STflowE z0 n) u σ a‖ ≤
      CK0 * STprof sz0 n u D ((sz0.L n : ℕ) : ℝ) (a 0) (a 1) :=
  k2_sz0.choose_spec.2

/-- The closure arithmetic `r^{C_d} b^{1/5} ≤ b^{1/6} ≤ 1` at `C_d = 3·1 + 1`, `𝔠_d = 1/240`. -/
theorem hq_sz0 : ∀ᶠ n in atTop, ∀ u, sInst n ≤ u → u ≤ tInst n →
    ((1 - sInst n) / (1 - u)) ^ (3 * (1 : ℝ) + 1) * (sz0.Bctl n u) ^ (1 / 5 : ℝ) ≤
        (sz0.Bctl n u) ^ (1 / 6 : ℝ) ∧
      0 ≤ ((1 - sInst n) / (1 - u)) ^ (3 * (1 : ℝ) + 1) * (sz0.Bctl n u) ^ (1 / 5 : ℝ) ∧
      (sz0.Bctl n u) ^ (1 / 6 : ℝ) ≤ 1 :=
  ST_hq_of_data sz0 sz0_tendsto hs0 hst ht1 (C := 1) (𝔠d := 1 / 240) one_pos (by norm_num)
    (by norm_num) bdata_spec.2.2 bdata_spec.2.1 (conStInd_inst (by norm_num))

/-- The scale family at the data (`stScaleExists_holds`). -/
theorem scale_sz0 : ∃ Kseq : ℕ → ℕ → ℝ → ℝ, STScaleAdm sz0 sInst tInst Kseq :=
  stScaleExists_holds 3 (1 / 10) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num)
    (1 / 6) sz0 z0 flow_z0 sInst tInst hs0 hst htT

noncomputable def Kseq0 : ℕ → ℕ → ℝ → ℝ := scale_sz0.choose
theorem Kseq0_adm : STScaleAdm sz0 sInst tInst Kseq0 := scale_sz0.choose_spec

/-- `ST_Bdata_holds` at the data. -/
example : ∃ cB c : ℝ, 0 < cB ∧ 0 < c ∧ ∀ᶠ n in atTop, ∀ u : ℝ, 0 ≤ u → u ≤ tInst n →
    cB * (((sz0.W n : ℕ) : ℝ) ^ 3)⁻¹ ≤ sz0.Bctl n u ∧
      sz0.Bctl n u ≤ ((sz0.size n : ℕ) : ℝ) ^ (-c) := bdata_sz0

/-- `ST_selfImprove_section` at `(sz0, z0, s ≡ 0, t ≡ 1/16)`, the scale `Kseq0 0`, the time section
`tt ≡ 1/32`, `D = 1`, `C = 1`, `δ₀ = 1/10`, `C₀ = 1`, `𝔠_d = 1/240`.  The pins `STLWT`, `STEMn2Exp`,
`STNewKLKAt`, `STGridMartAt` and the stochastic premises `STDecay`, `STStep1Weak`, `STScaleInv` stay
hypotheses; the rest is discharged. -/
example (hLWT : STLWT 3) (hEMe : STEMn2Exp 3)
    (hnew : STNewKLKAt 3 (1 / 10) (1 / 10) 1 (1 / 10)) (hmart : STGridMartAt 3 1)
    (hDec : STDecay sz0 (STflowE z0) sInst) (hS1W : STStep1Weak sz0 (STflowE z0) sInst tInst)
    (hinv : STScaleInv sz0 (STflowE z0) sInst tInst (Kseq0 0)) :=
  ST_selfImprove_section sz0 hLWT hEMe (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    flow_z0 hs0 htT (C := 1) (δ₀ := 1 / 10) (C₀ := 1) (𝔠d := 1 / 240) one_pos (by norm_num)
    (by norm_num) hnew hmart (by norm_num) (by norm_num) hDec (conStInd_inst (by norm_num)) hS1W
    bdata_spec.1 bdata_spec.2.1 bdata_spec.2.2 (Kseq0 0) (Kseq0_adm.2.1 0) hinv
    (fun n => ⟨1 / 32, by simp only [sInst, tInst, Set.mem_Icc]; norm_num⟩) 1 one_pos

/-- `ST_iterate` at the data: `C_d = 4`; the one-step pin `hSelf` and the base `hbase` stay hypotheses. -/
example (hSelf : ∀ Kf : ℕ → ℝ → ℝ, STScaleOk sz0 sInst tInst Kf →
      STScaleInv sz0 (STflowE z0) sInst tInst Kf →
      STSelfImp sz0 (3 * 1 + 1) (STflowE z0) sInst tInst Kf)
    (hbase : STScaleInv sz0 (STflowE z0) sInst tInst (Kseq0 0)) :
    ∀ m, STScaleInv sz0 (STflowE z0) sInst tInst (Kseq0 m) ∧
      STSelfImp sz0 (3 * 1 + 1) (STflowE z0) sInst tInst (Kseq0 m) :=
  ST_iterate sz0 sz0_tendsto hst CK0_pos hSelf hK2_sz0 hq_sz0 Kseq0 Kseq0_adm hbase

/-- `ST_decay_pt` at the data (`(Eq:Gdecay_w)` per time, `C_d = 4`). -/
example (hSelf : ∀ Kf : ℕ → ℝ → ℝ, STScaleOk sz0 sInst tInst Kf →
      STScaleInv sz0 (STflowE z0) sInst tInst Kf →
      STSelfImp sz0 (3 * 1 + 1) (STflowE z0) sInst tInst Kf)
    (hbase : STScaleInv sz0 (STflowE z0) sInst tInst (Kseq0 0)) :
    STStep2DecayPT sz0 (3 * 1 + 1) (STflowE z0) sInst tInst :=
  ST_decay_pt sz0 sz0_tendsto hst CK0_pos hSelf hK2_sz0 hq_sz0 Kseq0 Kseq0_adm hbase

/-- `ST_L2_decay_pt` at the data (`(eq:L2_decay)` per time); `(Eq:Gdecay_w)` per time stays a
hypothesis. -/
example (hdec : STStep2DecayPT sz0 (3 * 1 + 1) (STflowE z0) sInst tInst) :
    STL2decayPT sz0 (STflowE z0) sInst tInst :=
  ST_L2_decay_pt sz0 sz0_tendsto hst hs0 ht1 CK0_pos (𝔠 := 1 / 6) (by norm_num) sz0_bandwidth
    hdec hK2_sz0 hq_sz0

/-- `ST_base_inv` at the data: the base of the iteration from `(eq:opt_L2)` (the pin `STOptL2`'s
conclusion stays a hypothesis). -/
example (hOpt : PrecPT sz0 (U := fun n => TimeIcc sInst tInst n × (Fin 2 → Bool) ×
        (Fin 2 → Zd 3 (sz0.L n)))
      (fun n p ω => ‖Lloop sz0 n (STflowE z0 n) (p.1 : ℝ) p.2.1 p.2.2 ω -
        STKloop sz0 n (STflowE z0 n) (p.1 : ℝ) p.2.1 p.2.2‖)
      (fun n p _ => sz0.Bctl n (p.1 : ℝ))) :
    STScaleInv sz0 (STflowE z0) sInst tInst (fun n u => 0) :=
  ST_base_inv sz0 sz0_tendsto hst CK0_pos hK2_sz0 hOpt

/-- `ST_avgU_of_avg` at the data. -/
example (h : STStep2Avg sz0 (STflowE z0) sInst tInst) : STAvgU sz0 (STflowE z0) sInst tInst :=
  ST_avgU_of_avg sz0 h

/-- `ST_concl_of_step2` at the data. -/
example {Cd : ℝ} (hL : STStep2Local sz0 (STflowE z0) sInst tInst)
    (hA : STStep2Avg sz0 (STflowE z0) sInst tInst) (hD : STStep2Decay sz0 Cd (STflowE z0) sInst tInst) :
    STStep2Concl sz0 (STflowE z0) sInst tInst Cd :=
  ST_concl_of_step2 sz0 hL hA hD

/-- **`ST_step2_of_pins` at the data** (`STStep2 3` at `(sz0, z0, 0, 1/16)`): the nine pins stay
hypotheses. -/
example (hNew : STNewKLK 3) (hLWT : STLWT 3) (hEMe : STEMn2Exp 3) (hMart : STGridMart 3)
    (hK2 : STK2decay 3) (hNet : STNetLift2 3) (hScale : STScaleExists 3) (hOpt : STOptL2 3)
    (hClos : STLocalAvgOfL2 3) :
    ∃ Cd : ℝ, 0 < Cd ∧ ∃ 𝔠d : ℝ, 0 < 𝔠d ∧ 𝔠d ≤ 1 / 100 ∧
      (STLK sz0 (STflowE z0) sInst → STDecay sz0 (STflowE z0) sInst →
        STStep1Loop sz0 (STflowE z0) sInst tInst → STStep1Weak sz0 (STflowE z0) sInst tInst →
        STStep2Concl sz0 (STflowE z0) sInst tInst Cd) :=
  inst_step2 (ST_step2_of_pins hNew hLWT hEMe hMart hK2 hNet hScale hOpt hClos)

/-- **`ST_step2_of_pins'` at the data**: only the six remaining pins are hypotheses. -/
example (hNew : STNewKLK 3) (hLWT : STLWT 3) (hEMe : STEMn2Exp 3) (hMart : STGridMart 3)
    (hOpt : STOptL2 3) (hClos : STLocalAvgOfL2 3) :
    ∃ Cd : ℝ, 0 < Cd ∧ ∃ 𝔠d : ℝ, 0 < 𝔠d ∧ 𝔠d ≤ 1 / 100 ∧
      (STLK sz0 (STflowE z0) sInst → STDecay sz0 (STflowE z0) sInst →
        STStep1Loop sz0 (STflowE z0) sInst tInst → STStep1Weak sz0 (STflowE z0) sInst tInst →
        STStep2Concl sz0 (STflowE z0) sInst tInst Cd) :=
  inst_step2 (ST_step2_of_pins' hNew hLWT hEMe hMart hOpt hClos)

/-- **`ST_step2_of_pinsLW'` at the data** (`d = 3`; `LWtermExp` instead of `STLWT`). -/
example (hNew : STNewKLK 3) (hLW : LWtermExp 3) (hEMe : STEMn2Exp 3) (hRep : STGridRepN 3)
    (hOpt : STOptL2 3) (hClos : STLocalAvgOfL2 3) :
    ∃ Cd : ℝ, 0 < Cd ∧ ∃ 𝔠d : ℝ, 0 < 𝔠d ∧ 𝔠d ≤ 1 / 100 ∧
      (STLK sz0 (STflowE z0) sInst → STDecay sz0 (STflowE z0) sInst →
        STStep1Loop sz0 (STflowE z0) sInst tInst → STStep1Weak sz0 (STflowE z0) sInst tInst →
        STStep2Concl sz0 (STflowE z0) sInst tInst Cd) :=
  inst_step2 (ST_step2_of_pinsLW' (by norm_num) hNew hLW hEMe hRep hOpt hClos)

/-- **`ST_step2_of_pinsN` at the data**: the general-`n` grid pin `STGridRepN`. -/
example (hNew : STNewKLK 3) (hLWT : STLWT 3) (hEMe : STEMn2Exp 3) (hRep : STGridRepN 3)
    (hK2 : STK2decay 3) (hNet : STNetLift2 3) (hScale : STScaleExists 3) (hOpt : STOptL2 3)
    (hClos : STLocalAvgOfL2 3) :
    ∃ Cd : ℝ, 0 < Cd ∧ ∃ 𝔠d : ℝ, 0 < 𝔠d ∧ 𝔠d ≤ 1 / 100 ∧
      (STLK sz0 (STflowE z0) sInst → STDecay sz0 (STflowE z0) sInst →
        STStep1Loop sz0 (STflowE z0) sInst tInst → STStep1Weak sz0 (STflowE z0) sInst tInst →
        STStep2Concl sz0 (STflowE z0) sInst tInst Cd) :=
  inst_step2 (ST_step2_of_pinsN hNew hLWT hEMe hRep hK2 hNet hScale hOpt hClos)

/-- **`ST_step2_concl` at the data**: the probe form `STStep2Parts` gives the bundle. -/
example (h : STStep2Parts 3) :
    ∃ Cd : ℝ, 0 < Cd ∧ ∃ 𝔠d : ℝ, 0 < 𝔠d ∧ 𝔠d ≤ 1 / 100 ∧
      (STLK sz0 (STflowE z0) sInst → STDecay sz0 (STflowE z0) sInst →
        STStep1Loop sz0 (STflowE z0) sInst tInst → STStep1Weak sz0 (STflowE z0) sInst tInst →
        STStep2Concl sz0 (STflowE z0) sInst tInst Cd) :=
  inst_step2 (ST_step2_concl h)

/-- **`ST_gridMart_of_repN` at the data** (loop length `m = 2` of `STGridRepN 3`, `s ≡ 0`,
`t ≡ 1/16`, `D = 1`): the grid exponent `C_K`, the grid `K_n = ⌈N^{C_K}⌉`, and the decomposition
`A_k = A_0 + Δ Σ Drift_j + Rem_k + Mart_k` a.e. for the grid walk. -/
example (hRep : STGridRepN 3) :
    ∃ C₀ CK : ℝ, 0 ≤ C₀ ∧ 0 ≤ CK ∧ ∃ K : ℕ → ℕ, (∀ n, K n ≠ 0) ∧
      (∀ᶠ n in atTop, ((sz0.size n : ℕ) : ℝ) ^ CK ≤ K n) ∧
      ∃ Mart Rem : ∀ n, ((Fin 2 → Bool) × (Fin 2 → Zd 3 (sz0.L n))) → ℕ → PathΩ sz0 → ℂ,
        ∀ n i, ∀ᵐ ω ∂(pathP sz0), ∀ k, k ≤ K n →
          STgA sz0 sInst tInst K n (STflowE z0 n) i.1 i.2 k ω =
            STgA sz0 sInst tInst K n (STflowE z0 n) i.1 i.2 0 ω +
              ((gridStep sInst tInst K n : ℝ) : ℂ) *
                ∑ j ∈ Finset.range k, STgDrift sz0 sInst tInst K n (STflowE z0 n) i.1 i.2 j ω +
              Rem n i k ω + Mart n i k ω := by
  obtain ⟨C₀, hC₀, hAt⟩ := ST_gridMart_of_repN hRep
  obtain ⟨CK, hCK, hK⟩ := hAt (1 / 10) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num)
    (1 / 6) sz0 z0 flow_z0 sInst tInst hs0 hst htT 1 one_pos
  have hK0 : ∀ n, ⌈((sz0.size n : ℕ) : ℝ) ^ CK⌉₊ ≠ 0 := fun n =>
    (Nat.ceil_pos.2 (Real.rpow_pos_of_pos (lt_of_lt_of_le one_pos (one_le_size_sz0 n)) _)).ne'
  obtain ⟨Mart, Rem, hid, -, -⟩ := hK (fun n => ⌈((sz0.size n : ℕ) : ℝ) ^ CK⌉₊) hK0
    (Eventually.of_forall fun n => Nat.le_ceil _)
  exact ⟨C₀, CK, hC₀, hCK, fun n => ⌈((sz0.size n : ℕ) : ℝ) ^ CK⌉₊, hK0,
    Eventually.of_forall fun n => Nat.le_ceil _, Mart, Rem, hid⟩

end RBM.Gauss.Step2IterateInst
