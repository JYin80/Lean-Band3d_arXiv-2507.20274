/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Graph.BAAuxGraph2
import RBM3D.Graph.AuxGraph2
import RBM3D.Graph.BAAtom2
import RBM3D.BA.LWPinsBA
import RBM3D.BA.GreenOff
import RBM3D.BA.GreenLocal
import RBM3D.BA.Step1Boot
import RBM3D.BA.Prop5Short

/-!
# BA-L L3c3a, part 2: `claim:xi`, `(eq:Gbyxi2_BA)` and the bridge to G3, G4 (T2435)

Paper: arXiv:2507.20274 (`B:line` is `paper/tex/B_graphical_lemmas.tex:line`): `(Gyiyjatom)`
`B:424-426`, `(eq:Gbyxi2_BA)` `B:428-431`, `(G_by_auxG_BA)` `B:486-490`, G4 `B:491-497`;
`paper/tex/7_8_light_weight.tex:870-890` (`(eq:Gbyxi)`, `(eq:xia1a2)`, `claim:xi`) and `:1916-1946`
(`lem_GbEXP_BA`).  Part 1 is `RBM3D/Graph/BAAuxGraph2.lean` (`ζ`, `LWXigL`, the Ward sum, the
helpers); the basis is `RBM3D/Graph/AuxGraph2.lean` `:946-1500`.

* Section 4: `claim:xi` at BA (`BAZetaClaim`, `baZetaClaim_holds`: `LWXigL (baFMz sz z)
  (seqP (sz.withLam 0)) t Φ ζ`), twin of `LWXiClaim`.
* Section 5: `(eq:Gbyxi2_BA)` for all `x, y` (`BAGbyZeta`, `baGbyZeta_holds`, `baGbyZeta_hxi`)
  by the sample-wise route: the deterministic core `GreenOff_carrier_decay`
  (`BA/GreenOff.lean:916`, all `x, y`, `x = y` included) at `φ = ‖𝓛_{(-,+)}‖^{1/2}`,
  `Ψ = W^{-d/2}`, then the kernel `𝔗_γ` against `ζ` (Cauchy-Schwarz inside the `ρ`-window, the
  tail outside).  No unprimed `BAGbEXPij`, no loop premise (paper-delta candidate `T2435c`).
  Also the entrywise `BAEntryPsi`, `baEntryPsi_holds` (via `baGbEXPii_holds`), twin of
  `LWEntryPsi`.
* Section 6: G4 on the BA carrier `BAAnpAuxG` (a pin; owner L3d1).
* Section 7: compiled nonempty instances at the `d = 3` data of `BA/LWPinsBA.lean` §3 (`sz0`,
  `flow_sz0`, `t ≡ 1/2`, `ε₀ = 1/10`).

The floor exponent `D₁` of `ζ²` satisfies `D₁ ≥ max (d + 2 C₂/(𝔠 d) + 1) (1/𝔠)` in `BAZetaClaim`:
the first for `W^{-D₁} ≤ Φ(ℓ)²` on `ℓ ≤ L`, the second for the floor of the Ward sum.
-/

set_option linter.style.setOption false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.flexible false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.style.openClassical false
set_option linter.style.show false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false



noncomputable section

namespace RBM.Graph

open MeasureTheory Filter
open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes RBM.BA
open scoped Matrix

/-! ## 4. `claim:xi` at BA (target 3) -/

/-- **Target 3, `claim:xi` at BA** (`7_8:884-890`, `(eq:Gbyxi2_BA)` `B:428-431`; twin of `LWXiClaim`, `AuxGraph2:951`): at the `baPin` data
(law `seqP (sz.withLam 0)`, setting `BAFlow`, carrier `baFMz`, horizon `BAflowT0`), under `(LW_assm)` for a class `Φ` with `(eq:Psi)`
and `‖G_t - M‖_max ≺ W^{-ε₁}`, the variables `baZetaVar` at a radius `ρ = N^{o(1)}` and a floor exponent
`D₁ ≥ max (d + 2 C₂/(𝔠 d) + 1) (1/𝔠)` satisfy `LWXigL`: symmetric, non-negative, `ζ([a₁],[a₂]) ≺ Ψ_t(|a₁ - a₂|)` and
`Σ_{a₂} ζ([a₁],[a₂])² ≺ (W^d η_t)⁻¹` (Ward's identity, block form `T2435d`). -/
def BAZetaClaim (d : ℕ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z →
      ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ BAflowT0 sz z n) →
        ∀ (ε₀ C₁ C₂ C₃ : ℝ) (Cc : ℝ → ℝ) (Φ : ℕ → ℝ → ℝ), LWPsiAll sz ε₀ C₁ C₂ C₃ Cc Φ →
          LWLoop2gL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) t Φ →
          ∀ ε₁ : ℝ, 0 < ε₁ →
          PrecL sz (Sizes.seqP (sz.withLam 0)) (U := fun n => Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n))
            (fun n p ω => ‖(baFMz sz z).GM n (t n) ω p.1 p.2‖) (fun n _ _ => ((sz.W n : ℕ) : ℝ) ^ (-ε₁)) →
          ∀ ρ : ℕ → ℝ, (∀ n, 0 ≤ ρ n) →
            (∀ τ : ℝ, 0 < τ → ∀ᶠ n in atTop, ρ n + 1 ≤ ((sz.size n : ℕ) : ℝ) ^ τ) →
            ∀ D₁ : ℝ, max ((d : ℝ) + 2 * C₂ / (𝔠 * d) + 1) (1 / 𝔠) ≤ D₁ →
              LWXigL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) t Φ (baZetaVar sz z t ρ D₁)

theorem baZetaClaim_holds (d : ℕ) : BAZetaClaim d := by
  intro hd κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow t ht0 htT ε₀ C₁ C₂ C₃ Cc Φ hΦ hL ε₁ hε₁ hent ρ hρ0 hρ D₁ hD₁
  have hadm := hflow.1
  have hsize : sz.SizeTendsto := hadm.2.2.1
  have h𝔠 : 0 < 𝔠 := hadm.1
  have hd0 : 0 < d := by omega
  have hD₁a : (d : ℝ) + 2 * C₂ / (𝔠 * d) + 1 ≤ D₁ := (le_max_left _ _).trans hD₁
  have hD₁b : 1 / 𝔠 ≤ D₁ := (le_max_right _ _).trans hD₁
  refine ⟨fun n α β ω => ⟨baZetaVar_nonneg sz z t ρ D₁ n α β ω, baZetaVar_symm sz z t ρ D₁ n α β ω⟩, ?_, ?_⟩
  · -- conjunct 2: `ζ ≺ Φ(|a₁ - a₂|)`
    obtain ⟨hcls, hC3, hwin⟩ := hΦ.2.1
    obtain ⟨hanti, hC₁, hC₂, hrel1, hrel2⟩ := hΦ.2.2
    refine BAAuxGraph2_prec_of_imp hL ?_
    intro τ hτ
    refine ⟨τ / 2, half_pos hτ, ?_⟩
    set K₀ : ℝ := C₁ * 2 ^ C₂ + Cc 2 + Cc 2 * C₁ with hK₀
    have p1 := BAAuxGraph2_ev_poly sz hsize hρ0 hρ (a := 2) (b := 1) (c := 2) (e := ((2 * d : ℕ) : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (Nat.cast_nonneg _) (τ := τ / 4) (by positivity)
    have p2 := BAAuxGraph2_ev_poly sz hsize hρ0 hρ (a := 4) (b := 2) (c := |K₀|) (e := C₂)
      (by norm_num) (by norm_num) (abs_nonneg _) (by linarith) (τ := τ / 8) (by positivity)
    have p3 : ∀ᶠ n in atTop, C₃ ^ 2 ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) :=
      ((tendsto_rpow_atTop (half_pos hτ)).comp hsize).eventually_ge_atTop _
    have p4 : ∀ᶠ n in atTop, (3 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ τ :=
      ((tendsto_rpow_atTop hτ).comp hsize).eventually_ge_atTop _
    have p5 := BAAuxGraph2_ev_W_big sz hadm (C₃ * Cc 2 * C₁ * 2 ^ C₂) (s := 1 / 2) (by norm_num)
    filter_upwards [hcls, hwin, hrel1 2 (by norm_num), hrel2, p1, p2, p3, p4, p5, hadm.2.2.2.1,
      hsize.eventually_ge_atTop 1] with n hcl hwn hr1 hr2 q1 q2 q3 q4 q5 hb hX1
    intro ω p hp
    by_contra hno
    push Not at hno
    set X : ℝ := ((sz.size n : ℕ) : ℝ) with hXdef
    have hX0 : 0 < X := by linarith
    set u : ℝ := X ^ (τ / 8) with hu
    have hu1 : 1 ≤ u := Real.one_le_rpow hX1 (by positivity)
    have hpow : ∀ k : ℕ, X ^ (τ / 8 * (k : ℝ)) = u ^ k := fun k =>
      (BAAuxGraph2_rpow_nat X hX0.le _ k).symm
    have hΦn0 : ∀ r : ℝ, 0 ≤ r → 0 < Φ n r := fun r hr => (hcl r hr).1
    have hCc2 : 0 < Cc 2 := by
      by_contra h
      push Not at h
      have := hr1 0 le_rfl (by norm_num)
      have := hΦn0 0 le_rfl
      have := hΦn0 1 zero_le_one
      nlinarith
    have hK₀pos : 0 < K₀ := by
      have : 0 < C₁ * 2 ^ C₂ := by positivity
      have : 0 < Cc 2 * C₁ := by positivity
      rw [hK₀]; linarith
    set P : ℝ := (4 * ρ n + 2) ^ C₂ with hP
    have hP0 : 0 ≤ P := Real.rpow_nonneg (by have := hρ0 n; linarith) _
    set Kn : ℝ := K₀ * P with hKn
    have hKn0 : 0 ≤ Kn := by positivity
    -- the loop bound on the complement of the bad event
    have hloop : ∀ (s : Bool) (b₁ b₂ : Zd d (sz.L n)),
        ‖(baFMz sz z).L n (t n) ![s, !s] ![b₁, b₂] ω‖ ≤
          X ^ (τ / 2) * Φ n ((zdistInf d (sz.L n) (b₁ - b₂) : ℕ) : ℝ) ^ 2 := fun s b₁ b₂ =>
      hno (s, b₁, b₂)
    have hcmp : ∀ ℓ m : ℝ, 0 ≤ ℓ → 0 ≤ m → ℓ ≤ 2 * ρ n + m → Φ n m ≤ Kn * Φ n ℓ := by
      intro ℓ m hℓ hm hlm
      exact BAAuxGraph2_phi_cmp (Φ := Φ n) (hρ0 n) (hanti n) hΦn0 hC₁ hC₂ hCc2 hr1 hr2 hℓ hm hlm
    have hWpos : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := Nat.cast_pos.2 (sz.W_pos n)
    have hW : (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ C₃ ^ 2 * Φ n 0 ^ 2 := by
      have e : (((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2)) ^ 2 = (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ := by
        rw [BAAuxGraph2_rpow_nat _ hWpos.le, show -(d : ℝ) / 2 * ((2 : ℕ) : ℝ) = -(d : ℝ) by push_cast; ring,
          Real.rpow_neg hWpos.le, Real.rpow_natCast]
      calc (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ = (((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2)) ^ 2 := e.symm
        _ ≤ (C₃ * Φ n 0) ^ 2 := pow_le_pow_left₀ (Real.rpow_nonneg hWpos.le _) hwn 2
        _ = C₃ ^ 2 * Φ n 0 ^ 2 := by ring
    have hbound := BAAuxGraph2_zetaSq_le sz z t ρ D₁ n ω (Φ n) (hρ0 n) (B := X ^ (τ / 2)) (K := Kn)
      (C₃ := C₃) (Real.rpow_nonneg hX0.le _) hloop (fun r hr => (hΦn0 r hr).le) hcmp hW p.1 p.2
    set ℓ : ℝ := ((zdistInf d (sz.L n) (p.1 - p.2) : ℕ) : ℝ) with hℓ
    have hℓ0 : 0 ≤ ℓ := Nat.cast_nonneg _
    have hℓL : ℓ ≤ ((sz.L n : ℕ) : ℝ) := by
      rw [hℓ]; exact_mod_cast BAAuxGraph2_zdistInf_le_L d (sz.L n) _
    have hfl := BAAuxGraph2_floor_le sz hd0 n (Φ n) hΦn0 hC₁ hC₂ hCc2 hC3 hr1 hr2 hwn h𝔠 hb hD₁a q5 hℓ0 hℓL
    have hp' : X ^ τ * Φ n ℓ < baZetaVar sz z t ρ D₁ n p.1 p.2 ω := hp
    have e2 : X ^ (τ / 4) = u ^ 2 := by rw [← hpow 2]; congr 1; push_cast; ring
    have e4 : X ^ (τ / 2) = u ^ 4 := by rw [← hpow 4]; congr 1; push_cast; ring
    have e8 : X ^ τ = u ^ 8 := by rw [← hpow 8]; congr 1; push_cast; ring
    have hA1 : 2 * (2 * ρ n + 1) ^ (2 * d) ≤ u ^ 2 := by
      have := q1
      rw [Real.rpow_natCast, e2] at this
      exact this
    have hKn : Kn ^ 2 ≤ u ^ 2 := by
      have h1 : Kn ≤ u := by
        calc Kn = K₀ * P := rfl
          _ ≤ |K₀| * P := mul_le_mul_of_nonneg_right (le_abs_self _) hP0
          _ ≤ u := q2
      exact pow_le_pow_left₀ hKn0 h1 2
    have hnum := BAAuxGraph2_num hu1 hA1 (by rw [← e4]; exact q3) hKn (by rw [← e8]; exact q4)
      (pow_nonneg (by have := hρ0 n; linarith) _) (sq_nonneg _) (sq_nonneg _)
    rw [e4] at hbound
    have hΦℓ := (hΦn0 ℓ (Nat.cast_nonneg _)).le
    have hsq : baZetaSq sz z t ρ D₁ n p.1 p.2 ω ≤ (X ^ τ * Φ n ℓ) ^ 2 := by
      calc _ ≤ ((2 * (2 * ρ n + 1) ^ (2 * d) * u ^ 4 + C₃ ^ 2) * Kn ^ 2) * Φ n ℓ ^ 2 + Φ n ℓ ^ 2 := by
            linarith
        _ = (((2 * (2 * ρ n + 1) ^ (2 * d) * u ^ 4 + C₃ ^ 2) * Kn ^ 2) + 1) * Φ n ℓ ^ 2 := by ring
        _ ≤ (u ^ 8) ^ 2 * Φ n ℓ ^ 2 := mul_le_mul_of_nonneg_right hnum (sq_nonneg _)
        _ = (X ^ τ * Φ n ℓ) ^ 2 := by rw [e8]; ring
    have hle : baZetaVar sz z t ρ D₁ n p.1 p.2 ω ≤ X ^ τ * Φ n ℓ :=
      Real.sqrt_le_iff.2 ⟨by positivity, hsq⟩
    linarith
  · -- conjunct 3: `Σ_β ζ² ≺ (W^d η)⁻¹` (Ward's identity on `‖G - M‖_max ≤ 1`)
    refine BAAuxGraph2_prec_of_imp hent ?_
    intro τ hτ
    refine ⟨𝔠 * ε₁ / 2, by positivity, ?_⟩
    have p1 := BAAuxGraph2_ev_poly sz hsize hρ0 hρ (a := 2) (b := 1) (c := 6) (e := ((2 * d : ℕ) : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (Nat.cast_nonneg _) hτ
    filter_upwards [hadm.2.2.2.1, p1] with n hb q1
    intro ω α hα
    by_contra hno
    push Not at hno
    have hsm := BAAuxGraph2_pow_small sz n h𝔠 hε₁ hb
    have hA : ∀ x y : Idx d (sz.L n) (sz.W n), ‖(baFMz sz z).GM n (t n) ω x y‖ ≤ 1 := fun x y =>
      ((hno (x, y)).trans hsm.1).trans hsm.2
    have hw := baZeta_ward_sum sz z t ρ D₁ n hκ hflow (ht0 n) (htT n) (hρ0 n) ω hA α
    set X : ℝ := ((sz.size n : ℕ) : ℝ) with hXdef
    set Q : ℝ := ((((sz.W n : ℕ) : ℝ) ^ d) * (baFMz sz z).eta n (t n))⁻¹ with hQ
    have hα' : X ^ τ * Q < ∑ β, baZetaVar sz z t ρ D₁ n α β ω ^ 2 := hα
    simp_rw [BAAuxGraph2_zetaVar_sq] at hα'
    obtain ⟨ht1, -, hmi, hzi, -, -⟩ := ba_G_data hκ sz hflow n (ht0 n) (htT n)
    have hη0 : 0 < (baFMz sz z).eta n (t n) := by
      have := hzi
      rw [ztOf_im] at this
      exact this
    have hη1 : (baFMz sz z).eta n (t n) ≤ 1 := BAAuxGraph2_eta_le_one sz z hκ hflow n (ht0 n) (htT n)
    have hWd : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) ^ d := by
      have : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := Nat.cast_pos.2 (sz.W_pos n)
      positivity
    have hQ0 : 0 < Q := inv_pos.2 (mul_pos hWd hη0)
    have hWQ : (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ Q :=
      inv_anti₀ (mul_pos hWd hη0) (by nlinarith)
    have hρ1 : (1 : ℝ) ≤ 2 * ρ n + 1 := by have := hρ0 n; linarith
    have hA01 : (2 * ρ n + 1) ^ d ≤ (2 * ρ n + 1) ^ (2 * d) :=
      pow_le_pow_right₀ hρ1 (by omega)
    have hA1pos : 1 ≤ (2 * ρ n + 1) ^ (2 * d) := one_le_pow₀ hρ1
    have hq : 6 * (2 * ρ n + 1) ^ (2 * d) ≤ X ^ τ := by
      have := q1
      rwa [Real.rpow_natCast] at this
    have hfl := BAAuxGraph2_floorL_le sz h𝔠 n hb hD₁b
    have hsum : ∑ β, baZetaSq sz z t ρ D₁ n α β ω ≤ 6 * (2 * ρ n + 1) ^ (2 * d) * Q := by
      refine hw.trans ?_
      have h1 : (2 * ρ n + 1) ^ d * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ (2 * ρ n + 1) ^ (2 * d) * Q :=
        mul_le_mul hA01 hWQ (by positivity) (by linarith)
      have h2 : ((sz.L n : ℕ) : ℝ) ^ d * ((sz.W n : ℕ) : ℝ) ^ (-D₁) ≤ (2 * ρ n + 1) ^ (2 * d) * Q :=
        hfl.trans (hWQ.trans (le_mul_of_one_le_left hQ0.le hA1pos))
      nlinarith
    have := mul_le_mul_of_nonneg_right hq hQ0.le
    linarith

/-! ## 5. `(eq:Gbyxi2_BA)` and the entrywise bound (targets 4 and 5) -/

section Kernel

variable {d L : ℕ} [NeZero L]

/-- `Σ_{a'} e^{-c |a' - A|} ≤ expC (d - 2) c`, uniformly in `L` and `A` (`d ≥ 2`; `BAsum_exp_decay_le`, with `zdistD (-x) = zdistD x`). -/
private theorem BAAuxGraph2B_sum_exp_le (hd : 2 ≤ d) {c : ℝ} (hc : 0 < c) (A : Zd d L) :
    ∑ a' : Zd d L, Real.exp (-c * (zdistD d L (a' - A) : ℝ)) ≤ expC (d - 2) c := by
  have := BAsum_exp_decay_le d L hd c hc A
  refine le_trans (le_of_eq (Finset.sum_congr rfl fun a' _ => ?_)) this
  have e : zdistD d L (a' - A) = zdistD d L (A - a') := by
    rw [← neg_sub, zdistD_neg]
  rw [e]; congr 1; ring

private theorem BAAuxGraph2B_expC_nonneg (k : ℕ) {c : ℝ} (hc : 0 < c) : 0 ≤ expC k c := by
  unfold expC; positivity

/-- **The kernel `𝔗_γ(φ, Ψ)` against `ζ`** (the lattice part of `(eq:Gbyxi2_BA)`; paper-delta candidate `T2435c`).  `φ ∈ [0, 2]`, `Ψ ∈ [0, 1]`, blocks `A`, `C` within `zdistD`-distance `R`
of `a`, `b`, `s ≤ ρ - 2R`:
`𝔗_γ(A, C) ≤ (S + 1) Z + 2 F`, `S = expC (d-2) (γ/2)`, where `Z² ≥ Σ_{|a'-a|, |b'-b| ≤ ρ} φ²` (Cauchy-Schwarz inside the window),
`Z ≥ Ψ` when `|a - b| ≤ ρ`, and the tails `4 S² e^{-γ s/2} ≤ F`, `Ψ e^{-γ s} ≤ F` (outside the window). -/
theorem BAAuxGraph2B_T_le (hd : 2 ≤ d) {γ Ψ ρ R s Z F : ℝ} (hγ : 0 < γ) (hΨ0 : 0 ≤ Ψ) (hΨ1 : Ψ ≤ 1)
    (hR : 0 ≤ R) (hs : s ≤ ρ - 2 * R) (φ : Zd d L → Zd d L → ℝ) (hφ0 : ∀ a b, 0 ≤ φ a b)
    (hφ2 : ∀ a b, φ a b ≤ 2) (a b A C : Zd d L) (hA : (zdistD d L (A - a) : ℝ) ≤ R)
    (hC : (zdistD d L (C - b) : ℝ) ≤ R) (hZ0 : 0 ≤ Z)
    (h1 : ∑ a' ∈ Finset.univ.filter (fun a' : Zd d L => (zdistInf d L (a' - a) : ℝ) ≤ ρ),
      ∑ b' ∈ Finset.univ.filter (fun b' : Zd d L => (zdistInf d L (b' - b) : ℝ) ≤ ρ), φ a' b' ^ 2 ≤ Z ^ 2)
    (h2 : (zdistInf d L (a - b) : ℝ) ≤ ρ → Ψ ≤ Z)
    (h3 : 4 * expC (d - 2) (γ / 2) ^ 2 * Real.exp (-(γ / 2) * s) ≤ F)
    (h4 : Ψ * Real.exp (-γ * s) ≤ F) :
    GreenOff_T d L γ Ψ φ A C ≤ (expC (d - 2) (γ / 2) + 1) * Z + 2 * F := by
  classical
  set Sh : ℝ := expC (d - 2) (γ / 2) with hSh
  have hSh0 : 0 ≤ Sh := BAAuxGraph2B_expC_nonneg _ (by positivity)
  set u : Zd d L → ℝ := fun a' => Real.exp (-γ * (zdistD d L (a' - A) : ℝ)) with hu
  set v : Zd d L → ℝ := fun b' => Real.exp (-γ * (zdistD d L (b' - C) : ℝ)) with hv
  set u' : Zd d L → ℝ := fun a' => Real.exp (-(γ / 2) * (zdistD d L (a' - A) : ℝ)) with hu'
  set v' : Zd d L → ℝ := fun b' => Real.exp (-(γ / 2) * (zdistD d L (b' - C) : ℝ)) with hv'
  have hu0 : ∀ a', 0 ≤ u a' := fun _ => (Real.exp_pos _).le
  have hv0 : ∀ b', 0 ≤ v b' := fun _ => (Real.exp_pos _).le
  have hu'0 : ∀ a', 0 ≤ u' a' := fun _ => (Real.exp_pos _).le
  have hv'0 : ∀ b', 0 ≤ v' b' := fun _ => (Real.exp_pos _).le
  have hsu' : ∑ a', u' a' ≤ Sh := BAAuxGraph2B_sum_exp_le hd (by positivity) A
  have hsv' : ∑ b', v' b' ≤ Sh := BAAuxGraph2B_sum_exp_le hd (by positivity) C
  have huu' : ∀ a', u a' ≤ u' a' := fun a' =>
    Real.exp_le_exp.2 (by
      have := mul_nonneg hγ.le (Nat.cast_nonneg (zdistD d L (a' - A)) : (0 : ℝ) ≤ _)
      linarith only [this])
  have hvv' : ∀ b', v b' ≤ v' b' := fun b' =>
    Real.exp_le_exp.2 (by
      have := mul_nonneg hγ.le (Nat.cast_nonneg (zdistD d L (b' - C)) : (0 : ℝ) ≤ _)
      linarith only [this])
  have hu1 : ∀ a', u a' ≤ 1 := fun a' => Real.exp_le_one_iff.2 (by
    have := mul_nonneg hγ.le (Nat.cast_nonneg (zdistD d L (a' - A)) : (0 : ℝ) ≤ _)
    linarith only [this])
  have hv1 : ∀ b', v b' ≤ 1 := fun b' => Real.exp_le_one_iff.2 (by
    have := mul_nonneg hγ.le (Nat.cast_nonneg (zdistD d L (b' - C)) : (0 : ℝ) ≤ _)
    linarith only [this])
  have hsu : ∑ a', u a' ≤ Sh := (Finset.sum_le_sum fun a' _ => huu' a').trans hsu'
  have hsv : ∑ b', v b' ≤ Sh := (Finset.sum_le_sum fun b' _ => hvv' b').trans hsv'
  have hsu0 : 0 ≤ ∑ a', u a' := Finset.sum_nonneg fun a' _ => hu0 a'
  have hsv0 : 0 ≤ ∑ b', v b' := Finset.sum_nonneg fun b' _ => hv0 b'
  -- the windows and their complements
  set Ba : Finset (Zd d L) := Finset.univ.filter (fun a' : Zd d L => (zdistInf d L (a' - a) : ℝ) ≤ ρ) with hBa
  set Bb : Finset (Zd d L) := Finset.univ.filter (fun b' : Zd d L => (zdistInf d L (b' - b) : ℝ) ≤ ρ) with hBb
  set Ta : Finset (Zd d L) := Finset.univ.filter (fun a' : Zd d L => ¬ (zdistInf d L (a' - a) : ℝ) ≤ ρ) with hTa
  set Tb : Finset (Zd d L) := Finset.univ.filter (fun b' : Zd d L => ¬ (zdistInf d L (b' - b) : ℝ) ≤ ρ) with hTb
  -- the tails of the weights
  have htail_u : ∑ a' ∈ Ta, u a' ≤ Real.exp (-(γ / 2) * s) * Sh := by
    calc ∑ a' ∈ Ta, u a' ≤ ∑ a' ∈ Ta, Real.exp (-(γ / 2) * s) * u' a' := by
          refine Finset.sum_le_sum fun a' ha' => ?_
          simp only [hTa, Finset.mem_filter, Finset.mem_univ, true_and, not_le] at ha'
          have t1 := BAAuxGraph2_zdistInf_tri_real d L a' A a
          have t2 : (zdistInf d L (A - a) : ℝ) ≤ R :=
            (by exact_mod_cast zdistInf_le_zdistD d L (A - a) : (zdistInf d L (A - a) : ℝ) ≤ zdistD d L (A - a)).trans hA
          have t3 : (zdistInf d L (a' - A) : ℝ) ≤ zdistD d L (a' - A) := by
            exact_mod_cast zdistInf_le_zdistD d L (a' - A)
          have hxs : s ≤ (zdistD d L (a' - A) : ℝ) := by linarith
          have : -γ * (zdistD d L (a' - A) : ℝ) ≤ -(γ / 2) * s + -(γ / 2) * (zdistD d L (a' - A) : ℝ) := by
            have := mul_le_mul_of_nonneg_left hxs hγ.le
            linarith only [this]
          calc u a' = Real.exp (-γ * (zdistD d L (a' - A) : ℝ)) := rfl
            _ ≤ Real.exp (-(γ / 2) * s + -(γ / 2) * (zdistD d L (a' - A) : ℝ)) := Real.exp_le_exp.2 this
            _ = Real.exp (-(γ / 2) * s) * u' a' := by rw [Real.exp_add]
      _ = Real.exp (-(γ / 2) * s) * ∑ a' ∈ Ta, u' a' := by rw [Finset.mul_sum]
      _ ≤ Real.exp (-(γ / 2) * s) * Sh := by
          refine mul_le_mul_of_nonneg_left ((Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            fun a' _ _ => hu'0 a').trans hsu') (Real.exp_pos _).le
  have htail_v : ∑ b' ∈ Tb, v b' ≤ Real.exp (-(γ / 2) * s) * Sh := by
    calc ∑ b' ∈ Tb, v b' ≤ ∑ b' ∈ Tb, Real.exp (-(γ / 2) * s) * v' b' := by
          refine Finset.sum_le_sum fun b' hb' => ?_
          simp only [hTb, Finset.mem_filter, Finset.mem_univ, true_and, not_le] at hb'
          have t1 := BAAuxGraph2_zdistInf_tri_real d L b' C b
          have t2 : (zdistInf d L (C - b) : ℝ) ≤ R :=
            (by exact_mod_cast zdistInf_le_zdistD d L (C - b) : (zdistInf d L (C - b) : ℝ) ≤ zdistD d L (C - b)).trans hC
          have t3 : (zdistInf d L (b' - C) : ℝ) ≤ zdistD d L (b' - C) := by
            exact_mod_cast zdistInf_le_zdistD d L (b' - C)
          have hxs : s ≤ (zdistD d L (b' - C) : ℝ) := by linarith
          have : -γ * (zdistD d L (b' - C) : ℝ) ≤ -(γ / 2) * s + -(γ / 2) * (zdistD d L (b' - C) : ℝ) := by
            have := mul_le_mul_of_nonneg_left hxs hγ.le
            linarith only [this]
          calc v b' = Real.exp (-γ * (zdistD d L (b' - C) : ℝ)) := rfl
            _ ≤ Real.exp (-(γ / 2) * s + -(γ / 2) * (zdistD d L (b' - C) : ℝ)) := Real.exp_le_exp.2 this
            _ = Real.exp (-(γ / 2) * s) * v' b' := by rw [Real.exp_add]
      _ = Real.exp (-(γ / 2) * s) * ∑ b' ∈ Tb, v' b' := by rw [Finset.mul_sum]
      _ ≤ Real.exp (-(γ / 2) * s) * Sh := by
          refine mul_le_mul_of_nonneg_left ((Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            fun b' _ _ => hv'0 b').trans hsv') (Real.exp_pos _).le
  have hF0 : 0 ≤ F := le_trans (by positivity) h3
  -- the three pieces of the double sum
  have hT1 : (∑ a' : Zd d L, ∑ b' : Zd d L, φ a' b' *
      Real.exp (-γ * ((zdistD d L (a' - A) : ℝ) + (zdistD d L (b' - C) : ℝ)))) =
      ∑ a' : Zd d L, ∑ b' : Zd d L, φ a' b' * (u a' * v b') := by
    refine Finset.sum_congr rfl fun a' _ => Finset.sum_congr rfl fun b' _ => ?_
    rw [show -γ * ((zdistD d L (a' - A) : ℝ) + (zdistD d L (b' - C) : ℝ)) =
      -γ * (zdistD d L (a' - A) : ℝ) + -γ * (zdistD d L (b' - C) : ℝ) by ring, Real.exp_add]
  have hdecA : ∀ f : Zd d L → ℝ, ∑ a', f a' = ∑ a' ∈ Ba, f a' + ∑ a' ∈ Ta, f a' := fun f =>
    (Finset.sum_filter_add_sum_filter_not Finset.univ _ f).symm
  have hdecB : ∀ f : Zd d L → ℝ, ∑ b', f b' = ∑ b' ∈ Bb, f b' + ∑ b' ∈ Tb, f b' := fun f =>
    (Finset.sum_filter_add_sum_filter_not Finset.univ _ f).symm
  have hsplit : (∑ a' : Zd d L, ∑ b' : Zd d L, φ a' b' * (u a' * v b')) =
      (∑ a' ∈ Ba, ∑ b' ∈ Bb, φ a' b' * (u a' * v b')) + (∑ a' ∈ Ba, ∑ b' ∈ Tb, φ a' b' * (u a' * v b')) +
        ∑ a' ∈ Ta, ∑ b' : Zd d L, φ a' b' * (u a' * v b') := by
    rw [hdecA (fun a' => ∑ b' : Zd d L, φ a' b' * (u a' * v b'))]
    have : (∑ a' ∈ Ba, ∑ b' : Zd d L, φ a' b' * (u a' * v b')) =
        (∑ a' ∈ Ba, ∑ b' ∈ Bb, φ a' b' * (u a' * v b')) + ∑ a' ∈ Ba, ∑ b' ∈ Tb, φ a' b' * (u a' * v b') := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun a' _ => hdecB (fun b' => φ a' b' * (u a' * v b'))
    rw [this]
  -- mid and out pieces
  have hmid : (∑ a' ∈ Ba, ∑ b' ∈ Tb, φ a' b' * (u a' * v b')) ≤ 2 * (Real.exp (-(γ / 2) * s) * Sh ^ 2) := by
    calc (∑ a' ∈ Ba, ∑ b' ∈ Tb, φ a' b' * (u a' * v b')) ≤ ∑ a' ∈ Ba, ∑ b' ∈ Tb, 2 * (u a' * v b') :=
          Finset.sum_le_sum fun a' _ => Finset.sum_le_sum fun b' _ =>
            mul_le_mul_of_nonneg_right (hφ2 a' b') (mul_nonneg (hu0 a') (hv0 b'))
      _ = 2 * ((∑ a' ∈ Ba, u a') * ∑ b' ∈ Tb, v b') := by
          rw [Finset.sum_mul_sum, Finset.mul_sum]
          exact Finset.sum_congr rfl fun a' _ => by rw [Finset.mul_sum]
      _ ≤ 2 * (Sh * (Real.exp (-(γ / 2) * s) * Sh)) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul ?_ htail_v (Finset.sum_nonneg fun b' _ => hv0 b') hSh0) (by norm_num)
          exact (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun a' _ _ => hu0 a').trans hsu
      _ = _ := by ring
  have hout : (∑ a' ∈ Ta, ∑ b' : Zd d L, φ a' b' * (u a' * v b')) ≤ 2 * (Real.exp (-(γ / 2) * s) * Sh ^ 2) := by
    calc (∑ a' ∈ Ta, ∑ b' : Zd d L, φ a' b' * (u a' * v b')) ≤ ∑ a' ∈ Ta, ∑ b' : Zd d L, 2 * (u a' * v b') :=
          Finset.sum_le_sum fun a' _ => Finset.sum_le_sum fun b' _ =>
            mul_le_mul_of_nonneg_right (hφ2 a' b') (mul_nonneg (hu0 a') (hv0 b'))
      _ = 2 * ((∑ a' ∈ Ta, u a') * ∑ b' : Zd d L, v b') := by
          rw [Finset.sum_mul_sum, Finset.mul_sum]
          exact Finset.sum_congr rfl fun a' _ => by rw [Finset.mul_sum]
      _ ≤ 2 * ((Real.exp (-(γ / 2) * s) * Sh) * Sh) :=
          mul_le_mul_of_nonneg_left (mul_le_mul htail_u hsv hsv0 (mul_nonneg (Real.exp_pos _).le hSh0)) (by norm_num)
      _ = _ := by ring
  -- the window piece: Cauchy-Schwarz
  have hin : (∑ a' ∈ Ba, ∑ b' ∈ Bb, φ a' b' * (u a' * v b')) ≤ Sh * Z := by
    have hprod : ∀ g : Zd d L → Zd d L → ℝ, (∑ a' ∈ Ba, ∑ b' ∈ Bb, g a' b') = ∑ p ∈ Ba ×ˢ Bb, g p.1 p.2 := fun g =>
      (Finset.sum_product Ba Bb (fun p => g p.1 p.2)).symm
    rw [hprod (fun a' b' => φ a' b' * (u a' * v b'))]
    have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul (Ba ×ˢ Bb)
      (r := fun p : Zd d L × Zd d L => φ p.1 p.2 * (u p.1 * v p.2))
      (f := fun p : Zd d L × Zd d L => φ p.1 p.2 ^ 2 * (u p.1 * v p.2))
      (g := fun p : Zd d L × Zd d L => u p.1 * v p.2)
      (fun p _ => mul_nonneg (sq_nonneg _) (mul_nonneg (hu0 _) (hv0 _)))
      (fun p _ => mul_nonneg (hu0 _) (hv0 _)) (fun p _ => le_of_eq (by ring))
    have hf : (∑ p ∈ Ba ×ˢ Bb, φ p.1 p.2 ^ 2 * (u p.1 * v p.2)) ≤ Z ^ 2 := by
      refine le_trans ?_ h1
      rw [hprod (fun a' b' => φ a' b' ^ 2)]
      refine Finset.sum_le_sum fun p _ => ?_
      have h5 : u p.1 * v p.2 ≤ 1 := (mul_le_mul (hu1 p.1) (hv1 p.2) (hv0 p.2) zero_le_one).trans_eq (one_mul 1)
      calc φ p.1 p.2 ^ 2 * (u p.1 * v p.2) ≤ φ p.1 p.2 ^ 2 * 1 := mul_le_mul_of_nonneg_left h5 (sq_nonneg _)
        _ = φ p.1 p.2 ^ 2 := mul_one _
    have hg : (∑ p ∈ Ba ×ˢ Bb, u p.1 * v p.2) ≤ Sh ^ 2 := by
      rw [← hprod (fun a' b' => u a' * v b'), ← Finset.sum_mul_sum]
      rw [sq]
      exact mul_le_mul ((Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun a' _ _ => hu0 a').trans hsu)
        ((Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun a' _ _ => hv0 a').trans hsv)
        (Finset.sum_nonneg fun _ _ => hv0 _) hSh0
    have hsq : (∑ p ∈ Ba ×ˢ Bb, φ p.1 p.2 * (u p.1 * v p.2)) ^ 2 ≤ (Sh * Z) ^ 2 := by
      calc _ ≤ (∑ p ∈ Ba ×ˢ Bb, φ p.1 p.2 ^ 2 * (u p.1 * v p.2)) * ∑ p ∈ Ba ×ˢ Bb, u p.1 * v p.2 := hcs
        _ ≤ Z ^ 2 * Sh ^ 2 := mul_le_mul hf hg (Finset.sum_nonneg fun p _ => mul_nonneg (hu0 _) (hv0 _)) (sq_nonneg _)
        _ = (Sh * Z) ^ 2 := by ring
    exact le_of_sq_le_sq hsq (mul_nonneg hSh0 hZ0)
  -- the `Ψ` term
  have hΨ : Ψ * Real.exp (-γ * (zdistD d L (A - C) : ℝ)) ≤ Z + F := by
    by_cases hab : (zdistInf d L (a - b) : ℝ) ≤ ρ
    · have h5 : Real.exp (-γ * (zdistD d L (A - C) : ℝ)) ≤ 1 :=
        Real.exp_le_one_iff.2 (by
          have := mul_nonneg hγ.le (Nat.cast_nonneg (zdistD d L (A - C)) : (0 : ℝ) ≤ _)
          linarith only [this])
      have := mul_le_of_le_one_right hΨ0 h5
      linarith [h2 hab]
    · push Not at hab
      have t1 := BAAuxGraph2_zdistInf_tri_real d L a C b
      have t2 := BAAuxGraph2_zdistInf_tri_real d L a A C
      have t3 : (zdistInf d L (a - A) : ℝ) ≤ R := by
        rw [BAAuxGraph2_zdistInf_sub_comm]
        exact (by exact_mod_cast zdistInf_le_zdistD d L (A - a) : (zdistInf d L (A - a) : ℝ) ≤ zdistD d L (A - a)).trans hA
      have t4 : (zdistInf d L (C - b) : ℝ) ≤ R :=
        (by exact_mod_cast zdistInf_le_zdistD d L (C - b) : (zdistInf d L (C - b) : ℝ) ≤ zdistD d L (C - b)).trans hC
      have t5 : (zdistInf d L (A - C) : ℝ) ≤ zdistD d L (A - C) := by exact_mod_cast zdistInf_le_zdistD d L (A - C)
      have hxs : s ≤ (zdistD d L (A - C) : ℝ) := by linarith
      have h5 : Real.exp (-γ * (zdistD d L (A - C) : ℝ)) ≤ Real.exp (-γ * s) :=
        Real.exp_le_exp.2 (by
          have := mul_le_mul_of_nonneg_left hxs hγ.le
          linarith only [this])
      have := mul_le_mul_of_nonneg_left h5 hΨ0
      linarith
  unfold GreenOff_T
  rw [hT1, hsplit]
  linarith only [hin, hmid, hout, hΨ, h3]

end Kernel

section Sample

variable {d : ℕ}

/-- `‖𝓛^{(2)}_{(-,+),(a,b)}‖ ≤ g²` when `‖G_{xy}‖ ≤ g` for all `x, y` (`𝓛^{(2)} = W^{-2d} Σ_{x∈a, y∈b} |G_{xy}|²`, `GreenOff_loop_eq`). -/
theorem BAAuxGraph2B_loop_le (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ) (t : ℝ) (ω : sz.SeqΩ) {g : ℝ}
    (hG : ∀ x y : Idx d (sz.L n) (sz.W n), ‖(baFMz sz z).G n t ω x y‖ ≤ g) (a b : Zd d (sz.L n)) :
    ‖(baFMz sz z).L n t ![false, true] ![a, b] ω‖ ≤ g ^ 2 := by
  have hH := BAAuxGraph2_seqHflowBA_herm sz n (BAflowLam0 sz z) t ω
  have e := GreenOff_loop_eq (L := sz.L n) (W := sz.W n) hH
    (ztOf (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) (BAflowEs sz z n) t) a b
  change ‖loopFine d (sz.L n) (sz.W n) (sz.seqHflowBA (BAflowLam0 sz z) n t ω)
      (ztOf (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) (BAflowEs sz z n) t) ![false, true] ![a, b]‖ ≤ g ^ 2
  rw [e]
  unfold GreenCore_loop
  have hWd : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) ^ d := by
    have : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := Nat.cast_pos.2 (sz.W_pos n)
    positivity
  have hterm : ∀ o o' : Fin (sz.W n ^ d), ‖blockMat d (sz.L n) (sz.W n)
      (Gres (sz.seqHflowBA (BAflowLam0 sz z) n t ω)
        (ztOf (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) (BAflowEs sz z n) t) true) (a, o) (b, o')‖ ^ 2 ≤ g ^ 2 :=
    fun o o' => pow_le_pow_left₀ (norm_nonneg _) (hG _ _) 2
  calc (((((sz.W n : ℕ) : ℝ) ^ d)⁻¹) ^ 2 * ∑ o : Fin (sz.W n ^ d), ∑ o' : Fin (sz.W n ^ d), ‖blockMat d (sz.L n) (sz.W n)
      (Gres (sz.seqHflowBA (BAflowLam0 sz z) n t ω)
        (ztOf (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) (BAflowEs sz z n) t) true) (a, o) (b, o')‖ ^ 2)
      ≤ ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹) ^ 2 * ∑ o : Fin (sz.W n ^ d), ∑ o' : Fin (sz.W n ^ d), g ^ 2 :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun o _ => Finset.sum_le_sum fun o' _ => hterm o o')
          (by positivity)
    _ = g ^ 2 := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        field_simp

/-- `W^{-d} ≤ (W^{-ε'})²` for `2 ε' ≤ d`, `W ≥ 1` (private copy of `GreenLocal:wd_le`). -/
theorem BAAuxGraph2B_wd_le {W ε' : ℝ} (hW : 1 ≤ W) (hε' : ε' ≤ (d : ℝ) / 2) : (W ^ d)⁻¹ ≤ (W ^ (-ε')) ^ 2 := by
  have hW0 : 0 < W := by linarith
  rw [← Real.rpow_natCast, ← Real.rpow_neg hW0.le, ← Real.rpow_natCast, ← Real.rpow_mul hW0.le]
  exact Real.rpow_le_rpow_of_exponent_le hW (by push_cast; linarith)

/-- The floor: `W^{-max(D₁,0)/2} ≤ ζ`. -/
theorem BAAuxGraph2B_floor_zeta (sz : Sizes d) (z : ℕ → ℂ) (t ρ : ℕ → ℝ) (D₁ : ℝ) (n : ℕ) (a₁ a₂ : Zd d (sz.L n))
    (ω : sz.SeqΩ) : ((sz.W n : ℕ) : ℝ) ^ (-(max D₁ 0) / 2) ≤ baZetaVar sz z t ρ D₁ n a₁ a₂ ω := by
  have hW1 : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := Nat.one_le_cast.2 (sz.W_pos n)
  have hW0 : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by linarith
  unfold baZetaVar
  refine Real.le_sqrt_of_sq_le ?_
  have h1 : (((sz.W n : ℕ) : ℝ) ^ (-(max D₁ 0) / 2)) ^ 2 = ((sz.W n : ℕ) : ℝ) ^ (-(max D₁ 0)) := by
    rw [BAAuxGraph2_rpow_nat _ hW0.le]; congr 1; push_cast; ring
  have h2 : ((sz.W n : ℕ) : ℝ) ^ (-(max D₁ 0)) ≤ ((sz.W n : ℕ) : ℝ) ^ (-D₁) :=
    Real.rpow_le_rpow_of_exponent_le hW1 (by linarith [le_max_left D₁ 0])
  have h3 : ((sz.W n : ℕ) : ℝ) ^ (-D₁) ≤ baZetaSq sz z t ρ D₁ n a₁ a₂ ω := by
    unfold baZetaSq
    have hS : 0 ≤ ∑ b₁ ∈ Finset.univ.filter (fun b : Zd d (sz.L n) => (zdistInf d (sz.L n) (b - a₁) : ℝ) ≤ ρ n),
        ∑ b₂ ∈ Finset.univ.filter (fun b : Zd d (sz.L n) => (zdistInf d (sz.L n) (b - a₂) : ℝ) ≤ ρ n),
          ∑ σ ∈ ({![true, false], ![false, true]} : Finset (Fin 2 → Bool)),
            ‖(baFMz sz z).L n (t n) σ ![b₁, b₂] ω‖ :=
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
    have hI : 0 ≤ (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (if (zdistInf d (sz.L n) (a₁ - a₂) : ℝ) ≤ ρ n then 1 else 0) := by
      have : (0 : ℝ) ≤ (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ := by positivity
      split_ifs <;> positivity
    linarith
  rw [h1]; exact h2.trans h3

/-- **The lattice step of `(eq:Gbyxi2_BA)`** (sample form): if `‖(G_t - M)_{xy}‖ ≤ C_ℓ 𝔗_γ(φ, Ψ)([x], [y])` for all `x, y` at
`φ = ‖𝓛_{(-,+)}‖^{1/2}`, `Ψ = W^{-d/2}`, and `‖G‖_max ≤ 2`, then `‖(G_t - M)_{xy}‖ ≤ C_ℓ ((S + 1) ζ(a, b) + 2F)` for `x`, `y` within
`R` of `a`, `b`, with `S = expC (d-2) (γ/2)` and the tails `4 S² e^{-γ s/2} ≤ F`, `W^{-d/2} e^{-γ s} ≤ F`, `s ≤ ρ - 2R`. -/
theorem BAAuxGraph2B_zeta_bound (hd : 2 ≤ d) (sz : Sizes d) (z : ℕ → ℂ) (t ρ : ℕ → ℝ) (D₁ : ℝ) (n : ℕ) (ω : sz.SeqΩ)
    {γ Cl R s F : ℝ} (hγ : 0 < γ) (hCl : 0 ≤ Cl)
    (hG : ∀ x y : Idx d (sz.L n) (sz.W n), ‖(baFMz sz z).G n (t n) ω x y‖ ≤ 2)
    (hkey : ∀ x y : Idx d (sz.L n) (sz.W n), ‖(baFMz sz z).GM n (t n) ω x y‖ ≤
      Cl * GreenOff_T d (sz.L n) γ (Real.sqrt ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹))
        (fun a b => Real.sqrt ‖(baFMz sz z).L n (t n) ![false, true] ![a, b] ω‖) (STblk sz n x) (STblk sz n y))
    (hR : 0 ≤ R) (hs : s ≤ ρ n - 2 * R)
    (h3 : 4 * expC (d - 2) (γ / 2) ^ 2 * Real.exp (-(γ / 2) * s) ≤ F)
    (h4 : Real.sqrt ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹) * Real.exp (-γ * s) ≤ F)
    (x y : Idx d (sz.L n) (sz.W n)) (a b : Zd d (sz.L n))
    (hx : (zdistD d (sz.L n) ((split d (sz.L n) (sz.W n) x).1 - a) : ℝ) ≤ R)
    (hy : (zdistD d (sz.L n) ((split d (sz.L n) (sz.W n) y).1 - b) : ℝ) ≤ R) :
    ‖(baFMz sz z).GM n (t n) ω x y‖ ≤ Cl * ((expC (d - 2) (γ / 2) + 1) * baZetaVar sz z t ρ D₁ n a b ω + 2 * F) := by
  classical
  have hW1 : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := Nat.one_le_cast.2 (sz.W_pos n)
  have hWd1 : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) ^ d := one_le_pow₀ hW1
  have hWd0 : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) ^ d := by linarith
  set Ψ : ℝ := Real.sqrt ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹) with hΨ
  have hΨ0 : 0 ≤ Ψ := Real.sqrt_nonneg _
  have hΨ1 : Ψ ≤ 1 := by
    rw [hΨ, Real.sqrt_le_one]
    exact inv_le_one_of_one_le₀ hWd1
  have hZ0 : 0 ≤ baZetaVar sz z t ρ D₁ n a b ω := baZetaVar_nonneg sz z t ρ D₁ n a b ω
  have hφ2 : ∀ a' b' : Zd d (sz.L n),
      Real.sqrt ‖(baFMz sz z).L n (t n) ![false, true] ![a', b'] ω‖ ≤ 2 := fun a' b' =>
    Real.sqrt_le_iff.2 ⟨by norm_num, by
      have := BAAuxGraph2B_loop_le sz z n (t n) ω hG a' b'
      linarith⟩
  have hF : 0 ≤ F := le_trans (by have := BAAuxGraph2B_expC_nonneg (d - 2) (show 0 < γ / 2 by positivity); positivity) h3
  have hT := BAAuxGraph2B_T_le (L := sz.L n) hd (γ := γ) (Ψ := Ψ) (ρ := ρ n) (R := R) (s := s) (Z := baZetaVar sz z t ρ D₁ n a b ω) (F := F)
    hγ hΨ0 hΨ1 hR hs (fun a' b' => Real.sqrt ‖(baFMz sz z).L n (t n) ![false, true] ![a', b'] ω‖)
    (fun _ _ => Real.sqrt_nonneg _) hφ2 a b (STblk sz n x) (STblk sz n y) hx hy hZ0 ?_ ?_ h3 h4
  · exact (hkey x y).trans (mul_le_mul_of_nonneg_left hT hCl)
  · -- the window sum
    have hsq := BAAuxGraph2_zetaVar_sq sz z t ρ D₁ n a b ω
    rw [hsq]
    unfold baZetaSq
    have hI : 0 ≤ (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (if (zdistInf d (sz.L n) (a - b) : ℝ) ≤ ρ n then 1 else 0) := by
      have : (0 : ℝ) ≤ (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ := by positivity
      split_ifs <;> positivity
    have hFl : (0 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) ^ (-D₁) := Real.rpow_nonneg (Nat.cast_nonneg _) _
    refine le_trans ?_ (le_add_of_nonneg_right hFl |>.trans' (le_add_of_nonneg_right hI))
    refine Finset.sum_le_sum fun b₁ _ => Finset.sum_le_sum fun b₂ _ => ?_
    rw [BAAuxGraph2_pair_sum, Real.sq_sqrt (norm_nonneg _)]
    have := norm_nonneg ((baFMz sz z).L n (t n) ![true, false] ![b₁, b₂] ω)
    linarith
  · -- `Ψ ≤ ζ` inside the window
    intro hab
    have hsq := BAAuxGraph2_zetaVar_sq sz z t ρ D₁ n a b ω
    have hS : 0 ≤ ∑ b₁ ∈ Finset.univ.filter (fun b : Zd d (sz.L n) => (zdistInf d (sz.L n) (b - a) : ℝ) ≤ ρ n),
        ∑ b₂ ∈ Finset.univ.filter (fun b' : Zd d (sz.L n) => (zdistInf d (sz.L n) (b' - b) : ℝ) ≤ ρ n),
          ∑ σ ∈ ({![true, false], ![false, true]} : Finset (Fin 2 → Bool)),
            ‖(baFMz sz z).L n (t n) σ ![b₁, b₂] ω‖ :=
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
    have hFl : (0 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) ^ (-D₁) := Real.rpow_nonneg (Nat.cast_nonneg _) _
    have hle : (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ baZetaSq sz z t ρ D₁ n a b ω := by
      unfold baZetaSq
      have hind : (if (zdistInf d (sz.L n) (a - b) : ℝ) ≤ ρ n then (1 : ℝ) else 0) = 1 := by simp [hab]
      rw [hind, mul_one]
      linarith
    rw [hΨ]
    exact Real.sqrt_le_sqrt (hle.trans_eq hsq.symm) |>.trans_eq (Real.sqrt_sq hZ0)

end Sample


/-- The index set of `BAGbyZeta`: all pairs `x, y` (`x = y` included) with blocks `a`, `b` within `zdistD`-distance `R` of `[x]`, `[y]`. -/
abbrev BAGbyZetaU {d : ℕ} (sz : Sizes d) (R : ℕ → ℝ) (n : ℕ) : Type :=
  {q : (Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n)) × (Zd d (sz.L n) × Zd d (sz.L n)) //
    (zdistD d (sz.L n) ((split d (sz.L n) (sz.W n) q.1.1).1 - q.2.1) : ℝ) ≤ R n ∧
    (zdistD d (sz.L n) ((split d (sz.L n) (sz.W n) q.1.2).1 - q.2.2) : ℝ) ≤ R n}

/-- **Target 4, `(eq:Gbyxi2_BA)` (a)** (`B:428-431`; twin of `LWGbyXi`, `AuxGraph2:1106`): `‖(G_t - M)_{xy}‖ ≺ ζ(a, b)` for all `x, y`
(`x = y` included) and the blocks `a`, `b` at `zdistD`-distance `≤ R` from `[x]`, `[y]` (`R ≥ 0`, `ρ - 2R ≥ K log W` eventually for every `K`);
no `LWPsiAll`, no `LWLoop2gL`, no unprimed `BAGbEXPij`.  The floor exponent `D₁` is arbitrary. -/
def BAGbyZeta (d : ℕ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z →
      ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ BAflowT0 sz z n) →
        ∀ ε₁ : ℝ, 0 < ε₁ →
        PrecL sz (Sizes.seqP (sz.withLam 0)) (U := fun n => Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n))
          (fun n p ω => ‖(baFMz sz z).GM n (t n) ω p.1 p.2‖) (fun n _ _ => ((sz.W n : ℕ) : ℝ) ^ (-ε₁)) →
        ∀ (ρ R : ℕ → ℝ) (D₁ : ℝ), (∀ n, 0 ≤ R n) →
          (∀ K : ℝ, ∀ᶠ n in atTop, K * Real.log ((sz.W n : ℕ) : ℝ) ≤ ρ n - 2 * R n) →
          PrecL sz (Sizes.seqP (sz.withLam 0)) (U := BAGbyZetaU sz R)
            (fun n q ω => ‖(baFMz sz z).GM n (t n) ω q.1.1.1 q.1.1.2‖)
            (fun n q ω => baZetaVar sz z t ρ D₁ n q.1.2.1 q.1.2.2 ω)


section Events

variable {d : ℕ} (sz : Sizes d)

private theorem BAAuxGraph2B_card_vtx (n : ℕ) : Fintype.card (Vtx d (sz.L n) (sz.W n)) = sz.size n := by
  rw [Fintype.card_congr (splitEquiv d (sz.L n) (sz.W n)).symm, sz.card_Idx]

private theorem BAAuxGraph2B_card_off (n : ℕ) :
    Fintype.card (Green.OffPair d (sz.L n) (sz.W n)) ≤ sz.size n ^ 2 := by
  calc Fintype.card (Green.OffPair d (sz.L n) (sz.W n))
      ≤ Fintype.card (Vtx d (sz.L n) (sz.W n) × Vtx d (sz.L n) (sz.W n)) := Fintype.card_subtype_le _
    _ = sz.size n ^ 2 := by rw [Fintype.card_prod, BAAuxGraph2B_card_vtx, sq]

/-- A per-time domination over a polynomially small parameter set gives a high probability event (private copy of `GreenOff_whp`). -/
private theorem BAAuxGraph2B_whp {Ω : Type*} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω} {size : ℕ → ℕ}
    {V : ℕ → Type*} [∀ n, Fintype (V n)] {m : ℕ} (hV : ∀ n, Fintype.card (V n) ≤ size n ^ m)
    {ξ ζ : ∀ n, V n → Ω → ℝ} (h : Path.PerTimeDomAt P size ξ ζ) {τ : ℝ} (hτ : 0 < τ) :
    HighProbAt P size (fun n => {ω | ∀ v, ξ n v ω ≤ (size n : ℝ) ^ τ * ζ n v ω}) :=
  StochDomAt.highProb (Path.stochDomAt_of_perTimeDomAt P size (C := (m : ℝ)) (Nat.cast_nonneg m)
    (Eventually.of_forall fun n => by rw [Real.rpow_natCast]; exact_mod_cast hV n) h) hτ

end Events

theorem baGbyZeta_holds (d : ℕ) : BAGbyZeta d := by
  intro hd κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow t ht0 htT ε₁ hε₁ hent ρ R D₁ hR hsep
  have hd2 : 2 ≤ d := by omega
  have hd0 : 0 < d := by omega
  have hΛ : 0 < 𝔡⁻¹ := inv_pos.2 h𝔡
  have hγ0 := GreenStab_clam_pos d 𝔡⁻¹ κ hd0 hΛ hκ
  obtain ⟨ε', Kcl, hε'0, hKcl0, hconst⟩ := GreenOff_pin_consts (d := d) hd2 hκ h𝔡
  have hadm := hflow.1
  have h𝔠 : 0 < 𝔠 := hadm.1
  have hsz : sz.SizeTendsto := hadm.2.2.1
  have hsz' : Tendsto sz.size atTop atTop := Sizes.tendsto_size sz hsz
  obtain ⟨hRow, hCol, hQuad, hDiag⟩ := baLDEin_holds d κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow t ht0 htT
  set γ : ℝ := GreenStab_clam d 𝔡⁻¹ κ with hγ
  set Sh : ℝ := expC (d - 2) (γ / 2) with hSh
  have hSh0 : 0 ≤ Sh := BAAuxGraph2B_expC_nonneg _ (by positivity)
  -- the exponent of the event `Ω`, the floor exponent and the separation constant
  set ε₂ : ℝ := min (ε₁ / 2) ((d : ℝ) / 2) with hε₂
  have hε₂0 : 0 < ε₂ := lt_min (half_pos hε₁) (by positivity)
  have hε₂₁ : ε₂ ≤ ε₁ / 2 := min_le_left _ _
  have hε₂d : ε₂ ≤ (d : ℝ) / 2 := min_le_right _ _
  set E : ℝ := max D₁ 0 with hE
  have hE0 : 0 ≤ E := le_max_right _ _
  set K : ℝ := (E + 1) / γ with hK
  have hΩw := BAAuxGraph2_whp_entry sz (Sizes.seqP (sz.withLam 0)) (baFMz sz z) t h𝔠 hε₁ hadm.2.2.2.1 hent
  intro τ hτ D' hD'
  obtain ⟨τ₀, hτ₀0, hτ₀τ, hτ₀c⟩ : ∃ τ₀ : ℝ, 0 < τ₀ ∧ τ₀ ≤ τ / 2 ∧ τ₀ ≤ 𝔠 * ε₂ :=
    ⟨min (τ / 2) (𝔠 * ε₂), lt_min (by linarith) (mul_pos h𝔠 hε₂0), min_le_left _ _, min_le_right _ _⟩
  have hP1 := BAAuxGraph2B_whp (m := 2) (BAAuxGraph2B_card_off sz) hRow hτ₀0
  have hP2 := BAAuxGraph2B_whp (m := 2) (BAAuxGraph2B_card_off sz) hCol hτ₀0
  have hP3 := BAAuxGraph2B_whp (m := 1) (fun n => by rw [pow_one, BAAuxGraph2B_card_vtx sz]) hQuad hτ₀0
  have hP4 := BAAuxGraph2B_whp (m := 1) (fun n => by rw [pow_one, BAAuxGraph2B_card_vtx sz]) hDiag hτ₀0
  have hEv := HighProbAt.inter hsz' hP1 (HighProbAt.inter hsz' hP2 (HighProbAt.inter hsz' hP3
    (HighProbAt.inter hsz' hP4 hΩw)))
  filter_upwards [hEv D' hD', BAflow_lam0_window κ ε 𝔠 𝔡 sz z hflow, GreenOff_ev_small sz hadm hε₂0 hτ₀c hε'0,
    GreenOff_ev_big sz (Kcl * (Sh + 3)) hsz hτ hτ₀τ hτ₀0.le, hsep K,
    BAAuxGraph2_ev_W_big sz hadm (4 * Sh ^ 2) (s := 1 / 2) (by norm_num)] with n hEn hg hsm hbg hsepn hW4
  refine le_trans (MeasureTheory.measure_mono ?_) hEn
  rintro ω ⟨⟨⟨⟨x, y⟩, ⟨a, b⟩⟩, hx, hy⟩, hq⟩ hωE
  obtain ⟨h1, h2, h3, h4, h5⟩ := hωE
  beta_reduce at hq
  have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
  have hW1 : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hW0 : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by linarith
  have hP1' : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ τ₀ := Real.one_le_rpow hN1 hτ₀0.le
  have hδ0 : 0 ≤ ((sz.W n : ℕ) : ℝ) ^ (-ε₂) := Real.rpow_nonneg hW0.le _
  have hδ1 : ((sz.W n : ℕ) : ℝ) ^ (-ε₂) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hW1 (by linarith)
  obtain ⟨hδκ, hC1, hC2, hCl⟩ := hconst _ _ _ hP1' hδ0 hg.1.le hg.2 hsm
  have hΨpos : 0 < Real.sqrt ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹) := Real.sqrt_pos.2 (by positivity)
  have hwd : (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ (((sz.W n : ℕ) : ℝ) ^ (-ε₂)) ^ 2 := BAAuxGraph2B_wd_le hW1 hε₂d
  have hΩ' : ∀ x y : Idx d (sz.L n) (sz.W n), ‖(baFMz sz z).GM n (t n) ω x y‖ ≤ ((sz.W n : ℕ) : ℝ) ^ (-ε₂) :=
    fun x y => (h5 x y).trans (Real.rpow_le_rpow_of_exponent_le hW1 (by linarith))
  obtain ⟨-, -, -, -, -, hM1⟩ := ba_G_data hκ sz hflow n (ht0 n) (htT n)
  have hGb : ∀ x y : Idx d (sz.L n) (sz.W n), ‖(baFMz sz z).G n (t n) ω x y‖ ≤ 2 := fun x y => by
    have e : (baFMz sz z).G n (t n) ω x y = (baFMz sz z).GM n (t n) ω x y + (baFMz sz z).M n x y := by
      simp [FlowFM.GM]
    rw [e]
    have := norm_add_le ((baFMz sz z).GM n (t n) ω x y) ((baFMz sz z).M n x y)
    have h6 := hΩ' x y
    have h7 : ‖(baFMz sz z).M n x y‖ ≤ 1 := hM1 x y
    linarith
  have hφ : ∀ a b : Zd d (sz.L n), ‖(baFMz sz z).L n (t n) ![false, true] ![a, b] ω‖ ≤
      (Real.sqrt ‖(baFMz sz z).L n (t n) ![false, true] ![a, b] ω‖) ^ 2 := fun a b =>
    (Real.sq_sqrt (norm_nonneg _)).ge
  have key : ∀ x y : Idx d (sz.L n) (sz.W n), ‖(baFMz sz z).GM n (t n) ω x y‖ ≤
      (2 * GreenOff_Cl d κ (BAct_rate d 𝔡⁻¹ κ) (GreenOff_rho d 𝔡⁻¹ κ) (GreenOff_S d 𝔡⁻¹ κ) (((sz.size n : ℕ) : ℝ) ^ τ₀)
        (((sz.W n : ℕ) : ℝ) ^ (-ε₂)) (BAflowLam0 sz z n) (GreenStab_CTheta d 𝔡⁻¹ κ)) *
      GreenOff_T d (sz.L n) γ (Real.sqrt ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹))
        (fun a b => Real.sqrt ‖(baFMz sz z).L n (t n) ![false, true] ![a, b] ω‖) (STblk sz n x) (STblk sz n y) :=
    fun x y => GreenOff_carrier_decay hd2 hκ sz hflow n (ht0 n) (htT n) ω (P := ((sz.size n : ℕ) : ℝ) ^ τ₀)
      (Ψ := Real.sqrt ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹))
      (φ := fun a b => Real.sqrt ‖(baFMz sz z).L n (t n) ![false, true] ![a, b] ω‖) hg.1 hg.2 hP1' hδκ hδ0 hwd hΩ'
      (fun i j hij => h1 ⟨(i, j), hij⟩) (fun i j hij => h2 ⟨(i, j), hij⟩) h3 h4 hC1
      (fun a b => Real.sqrt_nonneg _) hφ hΨpos le_rfl hC2 x y
  have hCl0 : 0 ≤ 2 * GreenOff_Cl d κ (BAct_rate d 𝔡⁻¹ κ) (GreenOff_rho d 𝔡⁻¹ κ) (GreenOff_S d 𝔡⁻¹ κ)
      (((sz.size n : ℕ) : ℝ) ^ τ₀) (((sz.W n : ℕ) : ℝ) ^ (-ε₂)) (BAflowLam0 sz z n) (GreenStab_CTheta d 𝔡⁻¹ κ) := by
    have := GreenOff_T_pos (d := d) (L := sz.L n) (γ := γ) (φ := fun a b => Real.sqrt ‖(baFMz sz z).L n (t n) ![false, true] ![a, b] ω‖)
      (fun a b => Real.sqrt_nonneg _) hΨpos (STblk sz n x) (STblk sz n y)
    exact (mul_nonneg_iff_of_pos_right this).1 ((norm_nonneg _).trans (key x y))
  -- the tails
  have hlogW : Real.log ((sz.W n : ℕ) : ℝ) = Real.log ((sz.W n : ℕ) : ℝ) := rfl
  have hγK : γ / 2 * K = (E + 1) / 2 := by rw [hK]; field_simp
  have hexp1 : Real.exp (-(γ / 2) * (K * Real.log ((sz.W n : ℕ) : ℝ))) = ((sz.W n : ℕ) : ℝ) ^ (-((E + 1) / 2)) := by
    rw [Real.rpow_def_of_pos hW0]; congr 1; rw [← hγK]; ring
  have hexp2 : Real.exp (-γ * (K * Real.log ((sz.W n : ℕ) : ℝ))) = ((sz.W n : ℕ) : ℝ) ^ (-(E + 1)) := by
    rw [Real.rpow_def_of_pos hW0]; congr 1; rw [hK]; field_simp
  have hW2 : (0 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) ^ (-E / 2) := Real.rpow_nonneg hW0.le _
  have hF3 : 4 * Sh ^ 2 * Real.exp (-(γ / 2) * (K * Real.log ((sz.W n : ℕ) : ℝ))) ≤ ((sz.W n : ℕ) : ℝ) ^ (-E / 2) := by
    have e : ((sz.W n : ℕ) : ℝ) ^ (-((E + 1) / 2)) =
        ((sz.W n : ℕ) : ℝ) ^ (-E / 2) * ((sz.W n : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) := by
      rw [← Real.rpow_add hW0]; congr 1; ring
    have hhalf : 4 * Sh ^ 2 * ((sz.W n : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) ≤ 1 := by
      have : ((sz.W n : ℕ) : ℝ) ^ (1 / 2 : ℝ) * ((sz.W n : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) = 1 := by
        rw [← Real.rpow_add hW0]; simp
      calc 4 * Sh ^ 2 * ((sz.W n : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) ≤
            ((sz.W n : ℕ) : ℝ) ^ (1 / 2 : ℝ) * ((sz.W n : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) :=
            mul_le_mul_of_nonneg_right hW4 (Real.rpow_nonneg hW0.le _)
        _ = 1 := this
    rw [hexp1, e]
    calc 4 * Sh ^ 2 * (((sz.W n : ℕ) : ℝ) ^ (-E / 2) * ((sz.W n : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)))
        = (4 * Sh ^ 2 * ((sz.W n : ℕ) : ℝ) ^ (-(1 / 2 : ℝ))) * ((sz.W n : ℕ) : ℝ) ^ (-E / 2) := by ring
      _ ≤ 1 * ((sz.W n : ℕ) : ℝ) ^ (-E / 2) := mul_le_mul_of_nonneg_right hhalf hW2
      _ = _ := one_mul _
  have hF4 : Real.sqrt ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹) * Real.exp (-γ * (K * Real.log ((sz.W n : ℕ) : ℝ))) ≤
      ((sz.W n : ℕ) : ℝ) ^ (-E / 2) := by
    rw [hexp2]
    have hΨ1 : Real.sqrt ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹) ≤ 1 := by
      rw [Real.sqrt_le_one]; exact inv_le_one_of_one_le₀ (one_le_pow₀ hW1)
    have h7 : ((sz.W n : ℕ) : ℝ) ^ (-(E + 1)) ≤ ((sz.W n : ℕ) : ℝ) ^ (-E / 2) :=
      Real.rpow_le_rpow_of_exponent_le hW1 (by linarith)
    calc _ ≤ 1 * ((sz.W n : ℕ) : ℝ) ^ (-(E + 1)) :=
          mul_le_mul hΨ1 le_rfl (Real.rpow_nonneg hW0.le _) zero_le_one
      _ ≤ _ := by rw [one_mul]; exact h7
  have hbound := BAAuxGraph2B_zeta_bound hd2 sz z t ρ D₁ n ω (γ := γ)
    (Cl := 2 * GreenOff_Cl d κ (BAct_rate d 𝔡⁻¹ κ) (GreenOff_rho d 𝔡⁻¹ κ) (GreenOff_S d 𝔡⁻¹ κ)
      (((sz.size n : ℕ) : ℝ) ^ τ₀) (((sz.W n : ℕ) : ℝ) ^ (-ε₂)) (BAflowLam0 sz z n) (GreenStab_CTheta d 𝔡⁻¹ κ))
    (R := R n) (s := K * Real.log ((sz.W n : ℕ) : ℝ)) (F := ((sz.W n : ℕ) : ℝ) ^ (-E / 2)) hγ0 hCl0 hGb key (hR n) hsepn
    hF3 hF4 x y a b hx hy
  have hζ0 : 0 ≤ baZetaVar sz z t ρ D₁ n a b ω := baZetaVar_nonneg sz z t ρ D₁ n a b ω
  have hFζ : ((sz.W n : ℕ) : ℝ) ^ (-E / 2) ≤ baZetaVar sz z t ρ D₁ n a b ω :=
    BAAuxGraph2B_floor_zeta sz z t ρ D₁ n a b ω
  have hs1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ (τ₀ / 2) := Real.one_le_rpow hN1 (by linarith)
  have hP0 : (0 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ τ₀ := by linarith
  have hKS : 0 ≤ Kcl * (Sh + 3) := by positivity
  have step : ‖(baFMz sz z).GM n (t n) ω x y‖ ≤ ((sz.size n : ℕ) : ℝ) ^ τ * baZetaVar sz z t ρ D₁ n a b ω := by
    calc ‖(baFMz sz z).GM n (t n) ω x y‖
        ≤ (2 * GreenOff_Cl d κ (BAct_rate d 𝔡⁻¹ κ) (GreenOff_rho d 𝔡⁻¹ κ) (GreenOff_S d 𝔡⁻¹ κ)
            (((sz.size n : ℕ) : ℝ) ^ τ₀) (((sz.W n : ℕ) : ℝ) ^ (-ε₂)) (BAflowLam0 sz z n) (GreenStab_CTheta d 𝔡⁻¹ κ)) *
          ((Sh + 1) * baZetaVar sz z t ρ D₁ n a b ω + 2 * ((sz.W n : ℕ) : ℝ) ^ (-E / 2)) := hbound
      _ ≤ (2 * GreenOff_Cl d κ (BAct_rate d 𝔡⁻¹ κ) (GreenOff_rho d 𝔡⁻¹ κ) (GreenOff_S d 𝔡⁻¹ κ)
            (((sz.size n : ℕ) : ℝ) ^ τ₀) (((sz.W n : ℕ) : ℝ) ^ (-ε₂)) (BAflowLam0 sz z n) (GreenStab_CTheta d 𝔡⁻¹ κ)) *
          ((Sh + 3) * baZetaVar sz z t ρ D₁ n a b ω) :=
          mul_le_mul_of_nonneg_left (by linarith) hCl0
      _ ≤ (Kcl * ((sz.size n : ℕ) : ℝ) ^ τ₀) * ((Sh + 3) * baZetaVar sz z t ρ D₁ n a b ω) :=
          mul_le_mul_of_nonneg_right hCl (by positivity)
      _ = (Kcl * (Sh + 3) * ((sz.size n : ℕ) : ℝ) ^ τ₀) * baZetaVar sz z t ρ D₁ n a b ω := by ring
      _ ≤ (Kcl * (Sh + 3) * (((sz.size n : ℕ) : ℝ) ^ τ₀ * ((sz.size n : ℕ) : ℝ) ^ (τ₀ / 2))) *
            baZetaVar sz z t ρ D₁ n a b ω := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ hKS) hζ0
          exact le_mul_of_one_le_right hP0 hs1
      _ ≤ ((sz.size n : ℕ) : ℝ) ^ τ * baZetaVar sz z t ρ D₁ n a b ω := mul_le_mul_of_nonneg_right hbg hζ0
  exact absurd hq (not_lt.2 step)

/-- **`hξ` of `baGtoAG_holds` / `baGtoAG_E` from `(eq:Gbyxi2_BA)`** (the type match with L3c1; twin of `lwGbyXi_hxi`, `AuxGraph2:1160`): for
`c ≥ 0`, data `D` with `D.G = C.G`, `D.M = C.M` (`C = baFMz sz z`) and a sample `ω` with `‖(G_t - M)_{xy}‖ ≤ c ζ(a, b)` on the `R`-balls,
the edge variables `ξ = c · baZetaVar` are non-negative and satisfy the premise `hξ` of `baGtoAG_holds` (`BAAtom2:403-406`) and of `baGtoAG_E`
(`BAAtom2:616-618`) verbatim, for all `x, y`, `x = y` included. -/
theorem baGbyZeta_hxi {d : ℕ} (sz : Sizes d) (z : ℕ → ℂ) (t ρ R : ℕ → ℝ) (D₁ : ℝ) (n : ℕ)
    (D : BALData (Idx d (sz.L n) (sz.W n))) (ω : sz.SeqΩ) {c : ℝ} (hc : 0 ≤ c)
    (hG : ∀ x y, D.G x y = (baFMz sz z).G n (t n) ω x y) (hM : ∀ x y, D.M x y = (baFMz sz z).M n x y)
    (h : ∀ (x y : Idx d (sz.L n) (sz.W n)) (a b : Zd d (sz.L n)),
      (zdistD d (sz.L n) ((split d (sz.L n) (sz.W n) x).1 - a) : ℝ) ≤ R n →
      (zdistD d (sz.L n) ((split d (sz.L n) (sz.W n) y).1 - b) : ℝ) ≤ R n →
      ‖(baFMz sz z).GM n (t n) ω x y‖ ≤ c * baZetaVar sz z t ρ D₁ n a b ω) :
    (∀ a b : Zd d (sz.L n), 0 ≤ (fun a b : Zd d (sz.L n) => c * baZetaVar sz z t ρ D₁ n a b ω) a b) ∧
    (∀ (x y : Idx d (sz.L n) (sz.W n)) (a b : Zd d (sz.L n)),
      (zdistD d (sz.L n) ((split d (sz.L n) (sz.W n) x).1 - a) : ℝ) ≤ R n →
      (zdistD d (sz.L n) ((split d (sz.L n) (sz.W n) y).1 - b) : ℝ) ≤ R n →
      ‖D.G x y - D.M x y‖ ≤ (fun a b : Zd d (sz.L n) => c * baZetaVar sz z t ρ D₁ n a b ω) a b) :=
  ⟨fun a b => mul_nonneg hc (baZetaVar_nonneg sz z t ρ D₁ n a b ω), fun x y a b hx hy => by
    rw [hG, hM]; exact h x y a b hx hy⟩

/-- **Removing the indicator of `Ω(t, A)`** (`indMax`) from a domination `1(Ω) ξ ≺ ζ` over a carrier `C` and a law `μ` when `‖G_t - M‖_max ≤ A`
holds w.h.p. (twin of `auxGraph2_remove_indicator`, `AuxGraph2:681`). -/
private theorem BAAuxGraph2B_remove_indicator {d : ℕ} (sz : Sizes d) (μ : Measure sz.SeqΩ) (C : FlowFM sz) (t A : ℕ → ℝ)
    (hsize : sz.SizeTendsto) {U : ℕ → Type*} {ξ ζ : ∀ n, U n → sz.SeqΩ → ℝ}
    (hΩ : HighProbAt μ sz.size (fun n => {ω | ∀ x y : Idx d (sz.L n) (sz.W n), ‖C.GM n (t n) ω x y‖ ≤ A n}))
    (h : PrecL sz μ (fun n u ω => C.indMax n (t n) (A n) ω * ξ n u ω) ζ) : PrecL sz μ ξ ζ := by
  refine RBM.Ind.PerTimeCalc.Unif.stochDom_of_indicator (sz.tendsto_size hsize)
    (Ωs := fun n _ => {ω | ∀ x y : Idx d (sz.L n) (sz.W n), ‖C.GM n (t n) ω x y‖ ≤ A n}) ?_ ?_
  · exact HighProbAt.mono hΩ (Eventually.of_forall fun n ω hω u => hω)
  · have e : (fun n (u : U n) ω => ({ω : sz.SeqΩ | ∀ x y : Idx d (sz.L n) (sz.W n), ‖C.GM n (t n) ω x y‖ ≤ A n}).indicator
        (fun ω => ξ n u ω) ω) = fun n u ω => C.indMax n (t n) (A n) ω * ξ n u ω := by
      funext n u ω
      unfold FlowFM.indMax
      by_cases hω : ∀ x y : Idx d (sz.L n) (sz.W n), ‖C.GM n (t n) ω x y‖ ≤ A n
      · simp [Set.indicator, hω]
      · simp [Set.indicator, hω]
    rw [e]
    exact h

/-- **Target 5, `(eq:Gbyxi)` entrywise** (`B:428-431`, the `Ψ_t(0) δ_{xy}` term; twin of `LWEntryPsi`, `AuxGraph2:1177`): `‖G_t - M‖_max ≺ Ψ_t(0)`
at all pairs (G3's `‖D.G - D.M‖ ≤ Ψ`), from `(GiiGEX)` (`baGbEXPii_holds`) and `(LW_assm)`. -/
def BAEntryPsi (d : ℕ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z →
      ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ BAflowT0 sz z n) →
        ∀ (ε₀ C₁ C₂ C₃ : ℝ) (Cc : ℝ → ℝ) (Φ : ℕ → ℝ → ℝ), LWPsiAll sz ε₀ C₁ C₂ C₃ Cc Φ →
          LWLoop2gL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) t Φ →
          ∀ ε₁ : ℝ, 0 < ε₁ →
          PrecL sz (Sizes.seqP (sz.withLam 0)) (U := fun n => Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n))
            (fun n p ω => ‖(baFMz sz z).GM n (t n) ω p.1 p.2‖) (fun n _ _ => ((sz.W n : ℕ) : ℝ) ^ (-ε₁)) →
          PrecL sz (Sizes.seqP (sz.withLam 0)) (U := fun n => Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n))
            (fun n p ω => ‖(baFMz sz z).GM n (t n) ω p.1 p.2‖) (fun n _ _ => Φ n 0)

theorem baEntryPsi_holds (d : ℕ) : BAEntryPsi d := by
  intro hd κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow t ht0 htT ε₀ C₁ C₂ C₃ Cc Φ hΦ hL ε₁ hε₁ hent
  have hadm := hflow.1
  have hsize : sz.SizeTendsto := hadm.2.2.1
  have hii : BAGiiGEX sz z t (ε₁ / 2) :=
    baGbEXPii_holds d (by omega) κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow t ht0 htT (ε₁ / 2) (half_pos hε₁)
  have hΩ := BAAuxGraph2_whp_entry sz (Sizes.seqP (sz.withLam 0)) (baFMz sz z) t hadm.1 hε₁ hadm.2.2.2.1 hent
  have h1 : PrecL sz (Sizes.seqP (sz.withLam 0)) (U := fun n => Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n))
      (fun n p ω => ‖(baFMz sz z).GM n (t n) ω p.1 p.2‖ ^ 2)
      (fun n _ ω => STmaxLoop2g (baFMz sz z) n (t n) ω) :=
    BAAuxGraph2B_remove_indicator sz _ (baFMz sz z) t (fun n => ((sz.W n : ℕ) : ℝ) ^ (-(ε₁ / 2))) hsize hΩ hii
  refine BAAuxGraph2_prec_of_imp_union (sz.tendsto_size hsize) h1 hL ?_
  intro τ hτ
  refine ⟨τ, hτ, ?_⟩
  filter_upwards [hΦ.2.1.1] with n hcl
  intro ω p hp
  by_contra hno
  push Not at hno
  obtain ⟨hno1, hno2⟩ := hno
  set X : ℝ := ((sz.size n : ℕ) : ℝ) with hXdef
  have hX0 : 0 ≤ X := Nat.cast_nonneg _
  have hXτ : 0 ≤ X ^ τ := Real.rpow_nonneg hX0 _
  have hΦ0 : 0 < Φ n 0 := (hcl 0 le_rfl).1
  have hmax : STmaxLoop2g (baFMz sz z) n (t n) ω ≤ X ^ τ * Φ n 0 ^ 2 := by
    unfold STmaxLoop2g
    refine Finset.sup'_le _ _ fun pr _ => ?_
    have h1 := hno2 (false, pr.1, pr.2)
    have h2 : Φ n ((zdistInf d (sz.L n) (pr.1 - pr.2) : ℕ) : ℝ) ≤ Φ n 0 :=
      hΦ.2.2.1 n (Set.mem_Ici.2 (le_refl (0 : ℝ))) (Set.mem_Ici.2 (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
    have h3 : 0 < Φ n ((zdistInf d (sz.L n) (pr.1 - pr.2) : ℕ) : ℝ) := (hcl _ (Nat.cast_nonneg _)).1
    have h4 : Φ n ((zdistInf d (sz.L n) (pr.1 - pr.2) : ℕ) : ℝ) ^ 2 ≤ Φ n 0 ^ 2 :=
      pow_le_pow_left₀ h3.le h2 2
    exact h1.trans (mul_le_mul_of_nonneg_left h4 hXτ)
  have hG := hno1 p
  have hp' : X ^ τ * Φ n 0 < ‖(baFMz sz z).GM n (t n) ω p.1 p.2‖ := hp
  have hsq := pow_lt_pow_left₀ hp' (mul_nonneg hXτ hΦ0.le) (two_ne_zero)
  have : ‖(baFMz sz z).GM n (t n) ω p.1 p.2‖ ^ 2 ≤ (X ^ τ * Φ n 0) ^ 2 := by
    calc _ ≤ X ^ τ * STmaxLoop2g (baFMz sz z) n (t n) ω := hG
      _ ≤ X ^ τ * (X ^ τ * Φ n 0 ^ 2) := mul_le_mul_of_nonneg_left hmax hXτ
      _ = (X ^ τ * Φ n 0) ^ 2 := by ring
  linarith

/-! ## 6. Target 6: G4 on the BA carrier (a pin; owner L3d1) -/

/-- **G4 on the BA carrier** (`B:491-497`, **the pin of L3d1**): `BAAnpAux` (`BAAtom2:677`) with the BA data (`BAFlow`, `BAflowT0`, carrier
`baFMz`, law `seqP (sz.withLam 0)`, `PrecL`) and the carrier form `LWXigL` of `LWXi` (`η = C.eta`).  Pin only: `lwAnp_holds` is stated for
`Prec sz`, `STFlow`, `etaT`, and the `AnpKey*` chain has no law argument, so the statement at `μ`, `C.eta` needs the chain restated over the
carrier (L3d1). -/
def BAAnpAuxG (d : ℕ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ (p : ℕ) (P : BAPGraph (Fin 2)), 0 < p → P.g.nM ≤ p → (BAShadowPG P).LocReg345 p →
      P.g.mol (Sum.inl (P.ext 0)) ≠ P.g.mol (Sum.inl (P.ext 1)) →
      ∀ (ε₀ C₁ C₂ C₃ : ℝ) (Cc : ℝ → ℝ), ∃ c : ℝ, 0 < c ∧
        ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z →
          ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ BAflowT0 sz z n) →
            ∀ Φ : ℕ → ℝ → ℝ, LWPsiAll sz ε₀ C₁ C₂ C₃ Cc Φ →
              ∀ ξ : ∀ n, Zd d (sz.L n) → Zd d (sz.L n) → sz.SeqΩ → ℝ,
                LWXigL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) t Φ ξ →
                PrecL sz (Sizes.seqP (sz.withLam 0)) (U := fun n => Zd d (sz.L n) × Zd d (sz.L n))
                  (fun n ab ω => P.g.auxVal (fun α β => ξ n α β ω) (fun e => if e = P.ext 0 then ab.1 else ab.2))
                  (fun n ab _ => ((((sz.W n : ℕ) : ℝ) ^ d) * (baFMz sz z).eta n (t n))⁻¹ ^ P.g.nM *
                    Φ n (c * ((zdistInf d (sz.L n) (ab.1 - ab.2) : ℕ) : ℝ)) ^ p * Φ n 0 ^ (P.g.auxOrd - p))

/-! ## 7. Compiled nonempty instances at the `d = 3` data of `BA/LWPinsBA.lean` §3

`d = 3`, `sz0` (`n = 0`: `L = 4`, `W = 32`, `N = 2097152`), the flow `flow_sz0` (`κ = 1/2`, `ε = 𝔡 = 1/10`, `𝔠 = 1/6`, `t ≡ 1/2 ≤ T₀`), the class
`Φ0 ≡ W^{-1/2}` (`LWPsiAll` with `ε₀ = 1/10`, `C₁ = C₂ = 2`, `C₃ = 1`, `Cc ≡ 1`), `ε₁ = 1/20`, `D₁ = 12 = max (d + 2 C₂/(𝔠 d) + 1) (1/𝔠)`,
`R = (log W)^{21/20}`, `ρ = 2R + (log W)^{3/2}`.  What stays a hypothesis is another gate's input: `LWLoop2gL` and the entry law
`‖G_t - M‖_max ≺ W^{-1/20}`, and the pin `BAAnpAuxG 3` (owner L3d1). -/

section Instances

open RBM.Gauss.SizesInst RBM.BA.FlowPinsInst

local notation "μ0" => Sizes.seqP (sz0.withLam 0)

private theorem BAAuxGraph2B_one_le_W : ∀ n, (1 : ℝ) ≤ ((sz0.W n : ℕ) : ℝ) := RBM.Gauss.LWInst.one_le_W

private theorem BAAuxGraph2B_one_le_log : ∀ n, 1 ≤ Real.log ((sz0.W n : ℕ) : ℝ) := fun n => by
  rw [Real.le_log_iff_exp_le (by linarith [BAAuxGraph2B_one_le_W n])]
  linarith [RBM.Gauss.InductionDefsInst.W_ge_32 n, Real.exp_one_lt_d9]

/-- The class `Φ0 ≡ W^{-1/2}`. -/
private def BAAuxGraph2B_Φ0 : ℕ → ℝ → ℝ := fun n _ => ((sz0.W n : ℕ) : ℝ) ^ (-(1 / 2 : ℝ))
/-- The radius `R = (log W)^{21/20}`. -/
private def BAAuxGraph2B_R0 : ℕ → ℝ := fun n => Real.log ((sz0.W n : ℕ) : ℝ) ^ (21 / 20 : ℝ)
/-- The radius `ρ = 2R + (log W)^{3/2}`. -/
private def BAAuxGraph2B_ρ0 : ℕ → ℝ := fun n =>
  2 * BAAuxGraph2B_R0 n + Real.log ((sz0.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ)

private theorem BAAuxGraph2B_psiAll : LWPsiAll sz0 (1 / 10) 2 2 1 (fun _ => 1) BAAuxGraph2B_Φ0 := by
  have hW1 := BAAuxGraph2B_one_le_W
  refine ⟨by norm_num, ⟨Eventually.of_forall fun n r _ => ⟨Real.rpow_pos_of_pos (by linarith [hW1 n]) _,
    Real.rpow_le_rpow_of_exponent_le (hW1 n) (by norm_num)⟩, one_pos, Eventually.of_forall fun n => ?_⟩,
    fun n a _ b _ _ => le_rfl, by norm_num, by norm_num,
    fun C _ => Eventually.of_forall fun n ℓ _ _ => by simp [BAAuxGraph2B_Φ0], Eventually.of_forall fun n ℓ₁ ℓ₂ h1 h12 => ?_⟩
  · simp only [BAAuxGraph2B_Φ0, one_mul]
    exact Real.rpow_le_rpow_of_exponent_le (hW1 n) (by norm_num)
  · simp only [BAAuxGraph2B_Φ0]
    have hW : 0 < ((sz0.W n : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos (by linarith [hW1 n]) _
    have hr : 1 ≤ ℓ₂ / ℓ₁ := (one_le_div (by linarith)).mpr h12
    have : (1 : ℝ) ≤ (ℓ₂ / ℓ₁) ^ (2 : ℝ) := Real.one_le_rpow hr (by norm_num)
    nlinarith

private theorem BAAuxGraph2B_R0_nonneg (n : ℕ) : 0 ≤ BAAuxGraph2B_R0 n :=
  Real.rpow_nonneg (by linarith [BAAuxGraph2B_one_le_log n]) _

private theorem BAAuxGraph2B_ρ0_nonneg (n : ℕ) : 0 ≤ BAAuxGraph2B_ρ0 n := by
  unfold BAAuxGraph2B_ρ0
  linarith [BAAuxGraph2B_R0_nonneg n,
    Real.rpow_nonneg (by linarith [BAAuxGraph2B_one_le_log n] : (0 : ℝ) ≤ Real.log ((sz0.W n : ℕ) : ℝ)) (3 / 2 : ℝ)]

/-- `ρ = N^{o(1)}` (target 6 of the band file, `lwXiRad_holds`). -/
private theorem BAAuxGraph2B_ρ0_rad :
    ∀ τ : ℝ, 0 < τ → ∀ᶠ n in atTop, BAAuxGraph2B_ρ0 n + 1 ≤ ((sz0.size n : ℕ) : ℝ) ^ τ := fun τ hτ => by
  filter_upwards [lwXiRad_holds sz0 sz0_tendsto 3 0 (3 / 2) (by norm_num) le_rfl (by norm_num) τ hτ] with n hn
  have := Real.rpow_le_rpow_of_exponent_le (BAAuxGraph2B_one_le_log n) (by norm_num : (21 / 20 : ℝ) ≤ 3 / 2)
  unfold BAAuxGraph2B_ρ0 BAAuxGraph2B_R0
  linarith

/-- The separation `ρ - 2R ≥ K log W` eventually, for every `K` (`ρ - 2R = (log W)^{3/2}`). -/
private theorem BAAuxGraph2B_sep : ∀ K : ℝ, ∀ᶠ n in atTop,
    K * Real.log ((sz0.W n : ℕ) : ℝ) ≤ BAAuxGraph2B_ρ0 n - 2 * BAAuxGraph2B_R0 n := fun K => by
  have hW : Tendsto (fun n => ((sz0.W n : ℕ) : ℝ)) atTop atTop := by
    refine tendsto_atTop_mono (fun n => ?_) tendsto_natCast_atTop_atTop
    have : n ≤ sz0.W n := by
      change n ≤ (2 * (n + 1)) ^ 5
      exact (by omega : n ≤ 2 * (n + 1)).trans (Nat.le_self_pow (by norm_num) _)
    exact_mod_cast this
  filter_upwards [(Real.tendsto_log_atTop.comp hW).eventually_ge_atTop (K ^ 2),
    (Real.tendsto_log_atTop.comp hW).eventually_ge_atTop 1] with n h1' h2'
  have h1 : K ^ 2 ≤ Real.log ((sz0.W n : ℕ) : ℝ) := h1'
  have h2 : 1 ≤ Real.log ((sz0.W n : ℕ) : ℝ) := h2'
  have e : Real.log ((sz0.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ) =
      Real.log ((sz0.W n : ℕ) : ℝ) * Real.sqrt (Real.log ((sz0.W n : ℕ) : ℝ)) := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add (by linarith), Real.rpow_one, Real.sqrt_eq_rpow]
  have h3 : BAAuxGraph2B_ρ0 n - 2 * BAAuxGraph2B_R0 n =
      Real.log ((sz0.W n : ℕ) : ℝ) * Real.sqrt (Real.log ((sz0.W n : ℕ) : ℝ)) := by
    rw [← e]; unfold BAAuxGraph2B_ρ0; ring
  rw [h3]
  calc K * Real.log ((sz0.W n : ℕ) : ℝ) ≤ |K| * Real.log ((sz0.W n : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_right (le_abs_self K) (by linarith)
    _ ≤ Real.sqrt (Real.log ((sz0.W n : ℕ) : ℝ)) * Real.log ((sz0.W n : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_right (Real.abs_le_sqrt h1) (by linarith)
    _ = _ := mul_comm _ _

/-- **Instance of target 3** (`baZetaClaim_holds`) at `ρ = BAAuxGraph2B_ρ0`, `D₁ = 12`: `LWXigL` for `ζ` under `LWLoop2gL` and the entry law (other
gates' pins); every deterministic hypothesis is discharged (`LWPsiAll`, `ρ ≥ 0`, `ρ + 1 ≤ N^τ`, `D₁ = 12` is tight for `d + 2 C₂/(𝔠 d) + 1`). -/
example (hL : LWLoop2gL (baFMz sz0 zSeq) μ0 (fun _ => 1 / 2) BAAuxGraph2B_Φ0)
    (hent : PrecL sz0 μ0 (U := fun n => Idx 3 (sz0.L n) (sz0.W n) × Idx 3 (sz0.L n) (sz0.W n))
      (fun n p ω => ‖(baFMz sz0 zSeq).GM n (1 / 2) ω p.1 p.2‖) (fun n _ _ => ((sz0.W n : ℕ) : ℝ) ^ (-(1 / 20 : ℝ)))) :
    LWXigL (baFMz sz0 zSeq) μ0 (fun _ => 1 / 2) BAAuxGraph2B_Φ0
      (baZetaVar sz0 zSeq (fun _ => 1 / 2) BAAuxGraph2B_ρ0 12) :=
  baZetaClaim_holds 3 le_rfl (1 / 2) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 6) sz0 zSeq flow_sz0
    (fun _ => 1 / 2) (fun _ => by norm_num) (fun n => (half_lt_t0 n).le) (1 / 10) 2 2 1 (fun _ => 1) BAAuxGraph2B_Φ0
    BAAuxGraph2B_psiAll hL (1 / 20) (by norm_num) hent BAAuxGraph2B_ρ0 BAAuxGraph2B_ρ0_nonneg BAAuxGraph2B_ρ0_rad 12
    (by norm_num)

/-- **Instance of targets 4 and 5** (`baGbyZeta_holds`, `baEntryPsi_holds`) and of target 6's input: at the same data and the radius pair
`(ρ, R) = (BAAuxGraph2B_ρ0, BAAuxGraph2B_R0)` (`ρ - 2R ≥ K log W` eventually, `R ≥ 0`), `‖G - M‖ ≺ ζ(a, b)` on the index set
`BAGbyZetaU` (every diagonal pair `(x, x)` lies in it), `‖G - M‖ ≺ Φ0(0)` under `LWLoop2gL` and the entry law; `BAAnpAuxG 3`
(L3d1's pin) is fed with `ζ` from target 3. -/
example (h6 : BAAnpAuxG 3)
    (hL : LWLoop2gL (baFMz sz0 zSeq) μ0 (fun _ => 1 / 2) BAAuxGraph2B_Φ0)
    (hent : PrecL sz0 μ0 (U := fun n => Idx 3 (sz0.L n) (sz0.W n) × Idx 3 (sz0.L n) (sz0.W n))
      (fun n p ω => ‖(baFMz sz0 zSeq).GM n (1 / 2) ω p.1 p.2‖) (fun n _ _ => ((sz0.W n : ℕ) : ℝ) ^ (-(1 / 20 : ℝ)))) :
    PrecL sz0 μ0 (U := BAGbyZetaU sz0 BAAuxGraph2B_R0)
      (fun n q ω => ‖(baFMz sz0 zSeq).GM n ((fun _ => (1 / 2 : ℝ)) n) ω q.1.1.1 q.1.1.2‖)
      (fun n q ω => baZetaVar sz0 zSeq (fun _ => 1 / 2) BAAuxGraph2B_ρ0 12 n q.1.2.1 q.1.2.2 ω) ∧
    (∀ n (x : Idx 3 (sz0.L n) (sz0.W n)), ∃ q : BAGbyZetaU sz0 BAAuxGraph2B_R0 n, q.1.1 = (x, x)) ∧
    PrecL sz0 μ0 (U := fun n => Idx 3 (sz0.L n) (sz0.W n) × Idx 3 (sz0.L n) (sz0.W n))
      (fun n p ω => ‖(baFMz sz0 zSeq).GM n (1 / 2) ω p.1 p.2‖) (fun n _ _ => BAAuxGraph2B_Φ0 n 0) ∧
    ∃ c : ℝ, 0 < c ∧ PrecL sz0 μ0 (U := fun n => Zd 3 (sz0.L n) × Zd 3 (sz0.L n))
      (fun n ab ω => BAAtomInst2.baPQ.g.auxVal (fun α β => baZetaVar sz0 zSeq (fun _ => 1 / 2) BAAuxGraph2B_ρ0 12 n α β ω)
        (fun e => if e = BAAtomInst2.baPQ.ext 0 then ab.1 else ab.2))
      (fun n ab _ => ((((sz0.W n : ℕ) : ℝ) ^ 3) * (baFMz sz0 zSeq).eta n (1 / 2))⁻¹ ^ BAAtomInst2.baPQ.g.nM *
        BAAuxGraph2B_Φ0 n (c * ((zdistInf 3 (sz0.L n) (ab.1 - ab.2) : ℕ) : ℝ)) ^ 2 *
          BAAuxGraph2B_Φ0 n 0 ^ (BAAtomInst2.baPQ.g.auxOrd - 2)) := by
  have hR0 := BAAuxGraph2B_R0_nonneg
  refine ⟨baGbyZeta_holds 3 le_rfl (1 / 2) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 6) sz0 zSeq flow_sz0
    (fun _ => 1 / 2) (fun _ => by norm_num) (fun n => (half_lt_t0 n).le) (1 / 20) (by norm_num) hent BAAuxGraph2B_ρ0
    BAAuxGraph2B_R0 12 hR0 BAAuxGraph2B_sep, fun n x => ⟨⟨((x, x), ((split 3 (sz0.L n) (sz0.W n) x).1,
      (split 3 (sz0.L n) (sz0.W n) x).1)), by simpa using hR0 n, by simpa using hR0 n⟩, rfl⟩,
    baEntryPsi_holds 3 le_rfl (1 / 2) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 6) sz0 zSeq flow_sz0
      (fun _ => 1 / 2) (fun _ => by norm_num) (fun n => (half_lt_t0 n).le) (1 / 10) 2 2 1 (fun _ => 1) BAAuxGraph2B_Φ0
      BAAuxGraph2B_psiAll hL (1 / 20) (by norm_num) hent, ?_⟩
  have c3 := baZetaClaim_holds 3 le_rfl (1 / 2) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 6) sz0 zSeq flow_sz0
    (fun _ => 1 / 2) (fun _ => by norm_num) (fun n => (half_lt_t0 n).le) (1 / 10) 2 2 1 (fun _ => 1) BAAuxGraph2B_Φ0
    BAAuxGraph2B_psiAll hL (1 / 20) (by norm_num) hent BAAuxGraph2B_ρ0 BAAuxGraph2B_ρ0_nonneg BAAuxGraph2B_ρ0_rad 12 (by norm_num)
  obtain ⟨c, hc, H⟩ := h6 le_rfl (1 / 2) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) 2
    BAAtomInst2.baPQ (by norm_num) (by decide) localReg2_inst_Q_locReg345 (by decide) (1 / 10) 2 2 1 (fun _ => 1)
  exact ⟨c, hc, H (1 / 6) sz0 zSeq flow_sz0 (fun _ => 1 / 2) (fun _ => by norm_num) (fun n => (half_lt_t0 n).le)
    BAAuxGraph2B_Φ0 BAAuxGraph2B_psiAll _ c3⟩

/-- The data `D` of `baGbyZeta_hxi` exists (`D.G = C.G`, `D.M = C.M` at a sample). -/
private theorem BAAuxGraph2B_exists_data (ω : sz0.SeqΩ) : ∃ D : BALData (Idx 3 (sz0.L 0) (sz0.W 0)),
    (∀ x y, D.G x y = (baFMz sz0 zSeq).G 0 (1 / 2) ω x y) ∧ (∀ x y, D.M x y = (baFMz sz0 zSeq).M 0 x y) :=
  ⟨⟨⟨Matrix.of fun x y => (baFMz sz0 zSeq).G 0 (1 / 2) ω x y, Matrix.of fun x y => (baFMz sz0 zSeq).M 0 x y, 0, 0⟩, 0⟩,
    fun _ _ => rfl, fun _ _ => rfl⟩

/-- **Instance of `baGbyZeta_hxi` and the bridge to G3**: the premises `hξ0`, `hξ` of `baGtoAG_holds` from the sample event of target 4, for
`D` with `D.G = C.G`, `D.M = C.M`, `ξ = cξ ζ`, `R = BAAuxGraph2B_R0 0`; the other premises are those of `baGtoAG_holds` (L3c1's hypotheses). -/
example {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I] (Γ : BAGraph E I)
    (hN : Γ.Normal) (hext : ∀ a b : E, Γ.mol (Sum.inl a) = Γ.mol (Sum.inl b) → a = b)
    (D : BALData (Idx 3 (sz0.L 0) (sz0.W 0))) (ω : sz0.SeqΩ)
    (hDG : ∀ x y, D.G x y = (baFMz sz0 zSeq).G 0 (1 / 2) ω x y) (hDM : ∀ x y, D.M x y = (baFMz sz0 zSeq).M 0 x y)
    (Ψ A K₀ K₁ Kd C c r cξ : ℝ) (hcξ : 0 ≤ cξ) (hG : ∀ x y, ‖D.G x y - D.M x y‖ ≤ Ψ) (hA : 0 ≤ A)
    (hwin : (((sz0.W 0 : ℕ) : ℝ) ^ 3)⁻¹ ≤ A * Ψ ^ 2)
    (hS : LWKBound D.S (K₀ * (((sz0.W 0 : ℕ) : ℝ) ^ 3)⁻¹) K₁) (hSp : LWKBound D.Sp (K₀ * (((sz0.W 0 : ℕ) : ℝ) ^ 3)⁻¹) K₁)
    (hM : LWKBound D.M Kd Kd) (hP : LWKBound D.gPsi Kd Kd) (hC : 0 ≤ C) (hc : 0 < c)
    (hSd : ∀ x y, ‖D.S x y‖ ≤ C * (((sz0.W 0 : ℕ) : ℝ) ^ 3)⁻¹ * Real.exp (-(c * (lwBdist 3 (sz0.L 0) (sz0.W 0) x y : ℝ))))
    (hSpd : ∀ x y, ‖D.Sp x y‖ ≤ C * (((sz0.W 0 : ℕ) : ℝ) ^ 3)⁻¹ * Real.exp (-(c * (lwBdist 3 (sz0.L 0) (sz0.W 0) x y : ℝ))))
    (hMPd : ∀ x y, ‖D.M x y‖ ≤ C * Real.exp (-(c * (lwBdist 3 (sz0.L 0) (sz0.W 0) x y : ℝ))) ∧
      ‖D.gPsi x y‖ ≤ C * Real.exp (-(c * (lwBdist 3 (sz0.L 0) (sz0.W 0) x y : ℝ))))
    (hoff : ∀ x y, (split 3 (sz0.L 0) (sz0.W 0) x).2 ≠ (split 3 (sz0.L 0) (sz0.W 0) y).2 → D.M x y = 0 ∧ D.gPsi x y = 0)
    (hr : 0 ≤ r) (hRr : (Fintype.card (E ⊕ I) : ℝ) * r ≤ BAAuxGraph2B_R0 0)
    (h : ∀ (x y : Idx 3 (sz0.L 0) (sz0.W 0)) (a b : Zd 3 (sz0.L 0)),
      (zdistD 3 (sz0.L 0) ((split 3 (sz0.L 0) (sz0.W 0) x).1 - a) : ℝ) ≤ BAAuxGraph2B_R0 0 →
      (zdistD 3 (sz0.L 0) ((split 3 (sz0.L 0) (sz0.W 0) y).1 - b) : ℝ) ≤ BAAuxGraph2B_R0 0 →
      ‖(baFMz sz0 zSeq).GM 0 (1 / 2) ω x y‖ ≤
        cξ * baZetaVar sz0 zSeq (fun _ => 1 / 2) BAAuxGraph2B_ρ0 12 0 a b ω)
    (ℓe : E → Idx 3 (sz0.L 0) (sz0.W 0)) :=
  baGtoAG_holds 3 le_rfl (sz0.L 0) (sz0.W 0) Γ hN hext D Ψ A K₀ K₁ Kd C c r (BAAuxGraph2B_R0 0)
    (fun a b => cξ * baZetaVar sz0 zSeq (fun _ => 1 / 2) BAAuxGraph2B_ρ0 12 0 a b ω) hG hA hwin hS hSp hM hP hC hc hSd hSpd hMPd hoff hr hRr
    (baGbyZeta_hxi sz0 zSeq (fun _ => 1 / 2) BAAuxGraph2B_ρ0 BAAuxGraph2B_R0 12 0 D ω hcξ hDG hDM h).1
    (baGbyZeta_hxi sz0 zSeq (fun _ => 1 / 2) BAAuxGraph2B_ρ0 BAAuxGraph2B_R0 12 0 D ω hcξ hDG hDM h).2 ℓe

/-- The same data for `baGtoAG_E`'s premise `hξ` (`BAAtom2:616-618`) at the BA model: `D.G = C.G`, `D.M = C.M` exist, and the premise
`hξ` of `baGtoAG_E` is the conclusion of `baGbyZeta_hxi` (`diff -w` of `BAAtom2:403-406` and `:616-618` is empty). -/
example (ω : sz0.SeqΩ) (cξ : ℝ) (hcξ : 0 ≤ cξ)
    (h : ∀ (x y : Idx 3 (sz0.L 0) (sz0.W 0)) (a b : Zd 3 (sz0.L 0)),
      (zdistD 3 (sz0.L 0) ((split 3 (sz0.L 0) (sz0.W 0) x).1 - a) : ℝ) ≤ BAAuxGraph2B_R0 0 →
      (zdistD 3 (sz0.L 0) ((split 3 (sz0.L 0) (sz0.W 0) y).1 - b) : ℝ) ≤ BAAuxGraph2B_R0 0 →
      ‖(baFMz sz0 zSeq).GM 0 (1 / 2) ω x y‖ ≤ cξ * baZetaVar sz0 zSeq (fun _ => 1 / 2) BAAuxGraph2B_ρ0 12 0 a b ω) :
    ∃ D : BALData (Idx 3 (sz0.L 0) (sz0.W 0)), (∀ a b, 0 ≤ cξ * baZetaVar sz0 zSeq (fun _ => 1 / 2) BAAuxGraph2B_ρ0 12 0 a b ω) ∧
      ∀ (x y : Idx 3 (sz0.L 0) (sz0.W 0)) (a b : Zd 3 (sz0.L 0)),
        (zdistD 3 (sz0.L 0) ((split 3 (sz0.L 0) (sz0.W 0) x).1 - a) : ℝ) ≤ BAAuxGraph2B_R0 0 →
        (zdistD 3 (sz0.L 0) ((split 3 (sz0.L 0) (sz0.W 0) y).1 - b) : ℝ) ≤ BAAuxGraph2B_R0 0 →
        ‖D.G x y - D.M x y‖ ≤ cξ * baZetaVar sz0 zSeq (fun _ => 1 / 2) BAAuxGraph2B_ρ0 12 0 a b ω := by
  obtain ⟨D, hDG, hDM⟩ := BAAuxGraph2B_exists_data ω
  exact ⟨D, (baGbyZeta_hxi sz0 zSeq (fun _ => 1 / 2) BAAuxGraph2B_ρ0 BAAuxGraph2B_R0 12 0 D ω hcξ hDG hDM h).1,
    (baGbyZeta_hxi sz0 zSeq (fun _ => 1 / 2) BAAuxGraph2B_ρ0 BAAuxGraph2B_R0 12 0 D ω hcξ hDG hDM h).2⟩

end Instances

end RBM.Graph

end
