/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Universality.GUEPhase.Eq729A
import RBM3D.Universality.GUEPhase.OneLoop
import RBM3D.Universality.GUEPhase.KPrim
import RBM3D.Universality.GUEPhase.BootstrapAt
import RBM3D.Universality.GUEPhase.HypA
import RBM3D.Universality.ZeroModeProfile
import RBM3D.Main.ZTransfer
import RBM3D.Main.QUEFromQDiff
import RBM3D.Loop.KLFinal
import RBM3D.Loop.KLTree

/-!
# (7.29) at `t₀` on the GUE-phase grid, second half, and the (7.47) step (UN-47, `d ≥ 3`)

Ticket T2356 (stage 1b).  Port of `RBM2D/Universality/GUEPhase/Eq729B.lean` (1419 lines, RBM2D
commit `9e0f275`, cited `Eq729B:<line>`) onto the merged `d`-general layer, with the statements
designed at stage 1a (`docs/reports/T2356-design.md`; supervisor
`docs/supervisor/2026-10-09-0344.md`, conditions E1-E5 of `docs/tickets/T2356-1b.md`).  Paper:
[YY_25] (7.29), the (7.47) step, and
`(Meq:QdS1)`, `(Meq:QdS2)` (`paper/tex/1_2_Intro_model_result.tex:504-512`) at `η_Q`; the initial
term is `(Eq:Gtlp_exp+IND)` (`1_2:1281`).  Second half of the file `Eq729A.lean` (T2350): the
Grönwall closure of the one-step recursion, the inputs at the QUE scale, the arithmetic,
`gueGrid_eq729`, and the passage from `t₀` to `η_Q`.

## Targets

* `gueGrid_eq729`: (7.29) at `t₀` on the GUE-phase grid, `σ = (+, σ₂)`, in the loss form
  `N^δ ((N η_{t₀})^{-3} + I₀(t₁))` (`Eq729B_Concl`; `I₀` = right side of `STExp2`,
  `Eq729B_initTerm`), `hB := sz.STExp2 E t1`, `hell`, `hKb`, `hKinit` as `Hyp_Kt_detDom` (T2352a),
  `hd : 3 ≤ d`, `hlam`; `GUEPathBounds` stays a hypothesis.
* `Eq729B_eq747_of_eq729`: `Eq729B_Concl` at the flow data `(E', t₀, t₁)` of (7.47) implies the
  body of the merged pin `UNOUEq747` (`Eq729B_OUBody`; `Eq729B_ueq747_iff` is `Iff.rfl`), error
  `qdBoundExp sz n τ η_Q`, `η_Q = ouEtaQ sz 𝔡 n = W^{-𝔡/3} ilambda W^{d/2}/N`.
* `Eq729B_eq747_of_inputs`: the same from the inputs of `gueGrid_eq729`; `h730`, `hscale`, `hell`
  are derived (`Eq729B_derived`) from `τ_U ≤ ouTauMax 𝔠 𝔡`, `hlam` from `(eq:WO)`, `hKb` by
  `Sizes.stKbound_holds`.
* `Eq729B_goodFlow`, `Eq729B_bridge`: data good for every `n` (the formulas of `Eq729B_FlowData`
  hold eventually; `Sizes.lam` has no positivity field) and `STExp2 sz E' t₁` from `UNMLOut d`
  through `STFlow` (UN-51's input).  Both proved, no new pin.

## Renaming (as T2350, T2352, T2353)

`d : Sizes` is `sz : Sizes d`; `d.L n`, `d.W n`, `d.size n` are `sz.L n`, `sz.W n`, `sz.size n`
(`= (W L)^d`); `Z2 L` is `Zd d L`; `gloop L W (blockMat M)` is `loopL d L W (blockMat d L W M)`;
`Gsig` is `Gres`; `spectralZ`, `spectralM` are `zt`, `mE`; `KLoop.mSig` is `mSigma`;
`KLoop.Kcal` is `sz.STKloop`; `MLExpConcl` is `sz.STExp2`; `trGEGEmat`/`profileTilde` are `avg2`
of `Gres`/`profPMTilde`, `profPPTilde`; `Meta`/`scaleM` are `calB`/`Bctl`.
`hell : (d.L n)^2 (1 - t₁) ≤ 1` is `L^d (1 - t₁) ≤ ilambda²`; `N = (W L)^d ≥ 3^d ≥ 27`.

## Public helpers kept for the block Anderson kind (E4: over real data or over `sz`)

`Eq729B_perN`, `Eq729B_arith`, `Eq729B_final_729`, `Eq729B_gronwall_factor` (the Grönwall closure
and the arithmetic), `Eq729B_bctl_le_two_calB`, `Eq729B_Ld_mul_etaQ`, `Eq729B_hell_of_scales`,
`Eq729B_claimA`, `Eq729B_h730_hscale_real`, `Eq729B_qdBoundExp_eq`, `Eq729B_assembly_747` (the
exponent chain of the (7.47) step), `Eq729B_STExp2_congr`, `Eq729B_FlowData.ev_eq`.  Compiled
nonempty instances: namespace `RBM.Univ.GUEPhase.Eq729BInst`.  Every unpinned helper is `private`
or carries the file-stem prefix `Eq729B_`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

namespace RBM.Univ.GUEPhase

open MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.Gauss RBM.Gauss.Sizes RBM.Path RBM.Loop
  RBM.Univ RBM.Endpoints
open scoped NNReal ENNReal

variable {d : ℕ}

/-! ### The vocabulary of the three targets -/

/-- `z_n = E_n + i η_Q`, `η_Q = ouEtaQ sz 𝔡 n = W^{-𝔡/3} ilambda W^{d/2} / N` (`ZeroModeProfile.lean:84`). -/
def Eq729B_zQ (sz : Sizes d) (𝔡 : ℝ) (E : ℕ → ℝ) (n : ℕ) : ℂ :=
  (E n : ℂ) + ((ouEtaQ sz 𝔡 n : ℝ) : ℂ) * Complex.I

/-- The flow data of (7.47) (RBM2D `hE' ht0 ht1`, `Eq729B:1041`), eventually in `n`: `E' = lemE z_n`,
`t₀ = lemT z_n`, `t₁ = (1 - ζ(t_n)) t₀` (the formulas are junk where `ilambda_n ≤ 0`; `Eq729B_goodFlow` gives data
that are good for every `n`). -/
structure Eq729B_FlowData (sz : Sizes d) (𝔡 : ℝ) (E t E' t0 t1 : ℕ → ℝ) : Prop where
  hE' : ∀ᶠ n in atTop, E' n = lemE (Eq729B_zQ sz 𝔡 E n)
  ht0 : ∀ᶠ n in atTop, t0 n = lemT (Eq729B_zQ sz 𝔡 E n)
  ht1 : ∀ᶠ n in atTop, t1 n = (1 - ouZeta (t n)) * t0 n

/-- The right side of `STExp2` (`Induction/Defs.lean:159`): `𝓑² ((ilambda² W^d)^{-1/5} + 𝓑)`, `𝓑 = sz.Bctl n t`. -/
def Eq729B_initTerm (sz : Sizes d) (n : ℕ) (t : ℝ) : ℝ :=
  sz.Bctl n t ^ 2 * ((sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d) ^ (-(1 / 5 : ℝ)) + sz.Bctl n t)

/-- `‖𝔼 𝓛_{t₀,(+,σ₂),(a,b)} - 𝒦̃_{t₀,(+,σ₂),(a,b)}‖` at the last grid step (RBM2D `Eq729B:549-552`). -/
def Eq729B_eqErr (sz : Sizes d) (E t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) (σ₂ : Bool) (a b : Zd d (sz.L n)) : ℝ :=
  ‖(∫ ω, loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (gueH sz t1 t0 K n (K n) ω))
        (zt (E n) (t0 n)) ⟨[true, σ₂], [a, b]⟩ ∂(Pgue sz)) -
    kTwoGUE d (sz.L n) (sz.W n) (sz.lam n) (mSigma (E n)) (t1 n) (t0 n) true σ₂ a b‖

/-- (7.29) at `t₀`, loss form `N^δ ((N η_{t₀})^{-3} + I₀(t₁))`; RBM2D has `N^δ (N η_{t₀})^{-3}`, no `I₀`: the initial term
of `STExp2` is not of the form `Λ³` (the factor `(ilambda² W^d)^{-1/5}`). -/
def Eq729B_Concl (sz : Sizes d) (E t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) : Prop :=
  ∀ δ > (0 : ℝ), ∀ᶠ n in atTop, ∀ (σ₂ : Bool) (a b : Zd d (sz.L n)),
    Eq729B_eqErr sz E t1 t0 K n σ₂ a b ≤ Nsz sz n ^ δ * ((gueScale sz E n (t0 n))⁻¹ ^ 3 + Eq729B_initTerm sz n (t1 n))

/-- The body of `UNOUEq747 sz 𝔡 τU` at one `(κ, E, t)` and loss `τ` (`ZeroModeProfile.lean:107-122`, verbatim). -/
def Eq729B_OUBody (sz : Sizes d) (𝔡 : ℝ) (E t : ℕ → ℝ) (τ : ℝ) : Prop :=
  ∀ᶠ n in atTop, ∀ a b : Zd d (sz.L n),
    ‖(∫ ω, avg2 sz n (fun x y => ((‖Gres (ouMat (UNModel.band sz) n (t n) ω)
          ((E n : ℂ) + ((ouEtaQ sz 𝔡 n : ℝ) : ℂ) * Complex.I) true x y‖ ^ 2 : ℝ) : ℂ)) a b
        ∂(ouP (UNModel.band sz) n)) -
      profPMTilde sz n (ouZeta (t n)) ((E n : ℂ) + ((ouEtaQ sz 𝔡 n : ℝ) : ℂ) * Complex.I) a b‖ ≤
        qdBoundExp sz n τ (ouEtaQ sz 𝔡 n) ∧
    ‖(∫ ω, avg2 sz n (fun x y =>
          Gres (ouMat (UNModel.band sz) n (t n) ω)
            ((E n : ℂ) + ((ouEtaQ sz 𝔡 n : ℝ) : ℂ) * Complex.I) true x y *
          Gres (ouMat (UNModel.band sz) n (t n) ω)
            ((E n : ℂ) + ((ouEtaQ sz 𝔡 n : ℝ) : ℂ) * Complex.I) true y x) a b
        ∂(ouP (UNModel.band sz) n)) -
      profPPTilde sz n (ouZeta (t n)) ((E n : ℂ) + ((ouEtaQ sz 𝔡 n : ℝ) : ℂ) * Complex.I) a b‖ ≤
        qdBoundExp sz n τ (ouEtaQ sz 𝔡 n)

/-- `Eq729B_OUBody` is, by `Iff.rfl`, the body of the merged pin `UNOUEq747` (`ZeroModeProfile.lean:107`). -/
theorem Eq729B_ueq747_iff (sz : Sizes d) (𝔡 τU : ℝ) :
    UNOUEq747 sz 𝔡 τU ↔ ∀ κ : ℝ, 0 < κ → ∀ E : ℕ → ℝ, (∀ n, |E n| ≤ 2 - κ) →
      ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n ∧ t n ≤ ouTStar sz τU n) → ∀ τ : ℝ, 0 < τ → Eq729B_OUBody sz 𝔡 E t τ := Iff.rfl

/-! ### The crude Grönwall bound at a fixed size parameter (RBM2D `Eq729B:63-147`) -/

theorem Eq729B_c_nonneg {N ρ Λ p Δ : ℝ} (hN : 0 ≤ N) (hρ : 0 ≤ ρ) (hΛ : 0 ≤ Λ)
    (hp : 0 ≤ p) (hΔ : 0 ≤ Δ) : 0 ≤ eq729c N ρ Λ p Δ := by
  unfold eq729c
  have : 0 ≤ Δ ^ ((3 : ℝ) / 2) := Real.rpow_nonneg hΔ _
  positivity

/-- **The recursion closed by a discrete Grönwall** (RBM2D `Eq729B_perN`, `Eq729B:75`): at the last grid
step, `‖e_K‖ ≤ exp((t₀ - t₁)·2NρΛ) (B₀ + K c)`, `N = sz.size n`, `B₀` a bound of the initial error `e₀`. -/
theorem Eq729B_perN (sz : Sizes d) {t1 t0 : ℕ → ℝ} (K : ℕ → ℕ) {E : ℕ → ℝ} {n : ℕ}
    (Kt : ∀ n, ℝ → LoopIdx (Zd d (sz.L n)) → ℂ)
    (hE : |E n| < 2) (ht1 : 0 ≤ t1 n) (ht10 : t1 n ≤ t0 n) (ht0 : t0 n < 1) (hKN : K n ≠ 0)
    {Λ ρ p B0 : ℝ}
    (hΛ : Λ = (((sz.size n : ℕ) : ℝ) * etaT (E n) (t0 n))⁻¹) (hΛ1 : Λ ≤ 1)
    (hρ0 : 0 ≤ ρ) (hρΛ : ρ * Λ ≤ 1) (hp0 : 0 ≤ p)
    (hMΔ : ((sz.size n : ℕ) : ℝ) * gridStep t1 t0 K n ≤ 1)
    (hK2b : ∀ s ∈ Set.Icc (t1 n) (t0 n), ∀ s1 s2 x y,
      ‖Kt n s ⟨[s1, s2], [x, y]⟩‖ ≤ ρ * Λ)
    (hK3b : ∀ s ∈ Set.Icc (t1 n) (t0 n), ∀ s1 s2 s3 x y w,
      ‖Kt n s ⟨[s1, s2, s3], [x, y, w]⟩‖ ≤ ρ * Λ ^ 2)
    (hKd : ∀ s ∈ Set.Icc (t1 n) (t0 n), ∀ s1 s2 x y,
      HasDerivWithinAt (fun s => Kt n s ⟨[s1, s2], [x, y]⟩)
        (primRhsGUE d (sz.L n) (sz.W n) (Kt n s) ⟨[s1, s2], [x, y]⟩)
        (Set.Icc (t1 n) (t0 n)) s)
    (hX : ∀ k < K n, ∀ a,
      ‖(∫ ω, eq729F sz t1 t0 K E n k ω ⟨[true], [a]⟩ ∂(Pgue sz)) - mE (E n)‖ ≤ ρ * Λ ^ 2)
    {B : Set (PathΩ sz)} (hB : Pgue sz B ≤ ENNReal.ofReal p)
    (hg1 : ∀ ω ∉ B, ∀ k < K n, ∀ σ a,
      ‖eq729F sz t1 t0 K E n k ω ⟨[σ], [a]⟩ - mSigma (E n) σ‖ ≤ ρ * Λ)
    (hg2 : ∀ ω ∉ B, ∀ k < K n, ∀ s1 s2 x y, ‖eq729F sz t1 t0 K E n k ω ⟨[s1, s2], [x, y]⟩
      - Kt n (gridTime t1 t0 K n k) ⟨[s1, s2], [x, y]⟩‖ ≤ ρ * Λ ^ 2)
    (hg3 : ∀ ω ∉ B, ∀ k < K n, ∀ s1 s2 s3 x y w, ‖eq729F sz t1 t0 K E n k ω ⟨[s1, s2, s3], [x, y, w]⟩
      - Kt n (gridTime t1 t0 K n k) ⟨[s1, s2, s3], [x, y, w]⟩‖ ≤ ρ * Λ ^ 3)
    (hinit : ∀ s1 s2 x y, ‖eq729e sz t1 t0 K E Kt n 0 ⟨[s1, s2], [x, y]⟩‖ ≤ B0)
    (s1 s2 : Bool) (a1 a2 : Zd d (sz.L n)) :
    ‖eq729e sz t1 t0 K E Kt n (K n) ⟨[s1, s2], [a1, a2]⟩‖ ≤
      Real.exp ((t0 n - t1 n) * (2 * ((sz.size n : ℕ) : ℝ) * (ρ * Λ))) *
        (B0 + (K n : ℝ) * eq729c ((sz.size n : ℕ) : ℝ) ρ Λ p (gridStep t1 t0 K n)) := by
  set N : ℝ := ((sz.size n : ℕ) : ℝ) with hN
  set Δ : ℝ := gridStep t1 t0 K n with hΔ
  set r : ℝ := 2 * N * (ρ * Λ) with hr
  set c : ℝ := eq729c N ρ Λ p Δ with hc
  have hN0 : 0 ≤ N := Nat.cast_nonneg _
  have hΔ0 : 0 ≤ Δ := eq729_step_nonneg ht10
  have hΛ0 : 0 ≤ Λ := by
    rw [hΛ]; exact inv_nonneg.2 (mul_nonneg hN0 (eq729_eta_pos hE ht0).le)
  have hr0 : 0 ≤ r := by positivity
  have hc0 : 0 ≤ c := Eq729B_c_nonneg hN0 hρ0 hΛ0 hp0 hΔ0
  have hB00 : 0 ≤ B0 := (norm_nonneg _).trans (hinit true true 0 0)
  have hq1 : 1 ≤ 1 + Δ * r := by nlinarith
  have claim : ∀ k, k ≤ K n → ∀ s1 s2 x y,
      ‖eq729e sz t1 t0 K E Kt n k ⟨[s1, s2], [x, y]⟩‖ ≤ (1 + Δ * r) ^ k * (B0 + k * c) := by
    intro k
    induction k with
    | zero =>
      intro _ s1 s2 x y
      simpa using hinit s1 s2 x y
    | succ k ih =>
      intro hk s1 s2 x y
      have hk' : k < K n := hk
      have hstep := eq729_one_step sz K Kt hE ht1 ht10 ht0 hΛ hΛ1 hρ0 hρΛ hp0 hMΔ hK2b hK3b hKd
        hk' (hX k hk') hB (fun ω hω => hg1 ω hω k hk') (fun ω hω => hg2 ω hω k hk')
        (fun ω hω => hg3 ω hω k hk') (ih hk'.le) s1 s2 x y
      refine hstep.trans ?_
      have hpow : 1 ≤ (1 + Δ * r) ^ (k + 1) := one_le_pow₀ hq1
      have hA : 0 ≤ B0 + k * c := by positivity
      rw [Nat.cast_succ]
      calc (1 + Δ * r) * ((1 + Δ * r) ^ k * (B0 + k * c)) + c
          = (1 + Δ * r) ^ (k + 1) * (B0 + k * c) + c := by ring
        _ ≤ (1 + Δ * r) ^ (k + 1) * (B0 + k * c) + (1 + Δ * r) ^ (k + 1) * c := by
            gcongr; exact le_mul_of_one_le_left hc0 hpow
        _ = (1 + Δ * r) ^ (k + 1) * (B0 + (k + 1) * c) := by ring
  refine (claim (K n) le_rfl s1 s2 a1 a2).trans ?_
  have hexp : (1 + Δ * r) ^ (K n) ≤ Real.exp ((t0 n - t1 n) * r) := by
    have h1 : 1 + Δ * r ≤ Real.exp (Δ * r) := by linarith [Real.add_one_le_exp (Δ * r)]
    calc (1 + Δ * r) ^ (K n) ≤ Real.exp (Δ * r) ^ (K n) := pow_le_pow_left₀ (by linarith) h1 _
      _ = Real.exp ((K n : ℝ) * (Δ * r)) := (Real.exp_nat_mul _ _).symm
      _ = Real.exp ((t0 n - t1 n) * r) := by rw [← mul_assoc, hΔ, eq729_KΔ hKN]
  exact mul_le_mul_of_nonneg_right hexp (by positivity)

/-! ### The final normalisation (RBM2D `Eq729B:353-495`, `N`-only) -/

/-- `exp 2 < 7.4`. -/
theorem Eq729B_exp_two_lt : Real.exp 2 < 7.4 := by
  have h := Real.exp_one_lt_d9
  have h2 : Real.exp 2 = Real.exp 1 ^ 2 := by
    rw [← Real.exp_nat_mul]; norm_num
  rw [h2]
  have h0 : 0 < Real.exp 1 := Real.exp_pos 1
  nlinarith

/-- **The final normalisation**: `exp(E₀·2NρΛ)(ρΛ³ + K c) ≤ 56 ρ Λ³`, `K = (N+1)^{2A}`, `A ≥ 80`,
`p = 3/N¹²`, `N ≥ 9` (verbatim RBM2D `Eq729B_arith`, `Eq729B:368`: a statement in `N`, `ρ`, `Λ` only). -/
theorem Eq729B_arith {N : ℕ} (hN : 9 ≤ N) {ρ Λ E0 Δ Kr : ℝ} (A : ℕ) (hA : 80 ≤ A)
    (hKr : Kr = ((N : ℝ) + 1) ^ (2 * A)) (hρ : 1 ≤ ρ)
    (hΛ0 : 0 < Λ) (hΛN : 1 ≤ (N : ℝ) * Λ) (hE01 : E0 ≤ 1) (hKΔ : Kr * Δ = E0)
    (hΔ0 : 0 ≤ Δ) (hθ : E0 * (N : ℝ) * Λ * ρ ≤ 1) :
    Real.exp (E0 * (2 * (N : ℝ) * (ρ * Λ))) *
        (ρ * Λ ^ 3 + Kr * eq729c (N : ℝ) ρ Λ (3 / (N : ℝ) ^ 12) Δ) ≤ 56 * ρ * Λ ^ 3 := by
  set x : ℝ := (N : ℝ) with hx
  have hx9 : 9 ≤ x := by rw [hx]; exact_mod_cast hN
  have hx4 : 4 ≤ x := by linarith
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x + 1 := by linarith
  have hKr0 : 0 < Kr := by rw [hKr]; positivity
  have hρ0 : 0 ≤ ρ := by linarith
  have hΛ3 : 1 / x ^ 3 ≤ Λ ^ 3 := by
    have h1 : 1 / x ≤ Λ := by rw [div_le_iff₀ hx0]; linarith
    calc 1 / x ^ 3 = (1 / x) ^ 3 := by rw [_root_.one_div_pow]
      _ ≤ Λ ^ 3 := pow_le_pow_left₀ (by positivity) h1 3
  -- the exponential factor
  have hexp : Real.exp (E0 * (2 * x * (ρ * Λ))) ≤ 7.4 := by
    have : E0 * (2 * x * (ρ * Λ)) ≤ 2 := by
      have e : E0 * (2 * x * (ρ * Λ)) = 2 * (E0 * x * Λ * ρ) := by ring
      rw [e]; linarith
    exact ((Real.exp_le_exp.2 this).trans Eq729B_exp_two_lt.le)
  -- the pieces of `K c`
  have hsqrt : Δ ^ ((3 : ℝ) / 2) = Δ * Real.sqrt Δ := by
    rw [Real.sqrt_eq_rpow, show (3 : ℝ) / 2 = 1 + 1 / 2 by norm_num,
      Real.rpow_add' hΔ0 (by norm_num), Real.rpow_one]
  have hΔK : Δ ≤ 1 / Kr := by
    rw [le_div_iff₀ hKr0]; linarith [mul_comm Kr Δ]
  have hsqrtΔ : Real.sqrt Δ ≤ 1 / (x + 1) ^ A := by
    have h1 : Real.sqrt (1 / Kr) = 1 / (x + 1) ^ A := by
      rw [hKr, pow_mul', one_div, Real.sqrt_inv, Real.sqrt_sq (by positivity), one_div]
    rw [← h1]; exact Real.sqrt_le_sqrt hΔK
  have hpow80 : (x + 1) ^ 80 ≤ (x + 1) ^ A := pow_le_pow_right₀ hx1 hA
  -- piece Q2 + Q3 (main)
  have hXeq : eq729c x ρ Λ (3 / x ^ 12) Δ
      = Δ * (5 * x * ρ ^ 2 * Λ ^ 4 + 36 * x ^ 5 / x ^ 12)
        + 10000 * x ^ 4 * (1 + x) ^ 6 * Δ ^ ((3 : ℝ) / 2) + 3 * x ^ 2 * Δ ^ 2 := by
    unfold eq729c; ring
  have hmain : E0 * (5 * x * ρ ^ 2 * Λ ^ 4) ≤ 5 * ρ * Λ ^ 3 := by
    have h : E0 * (5 * x * ρ ^ 2 * Λ ^ 4) = 5 * ρ * Λ ^ 3 * (E0 * x * Λ * ρ) := by ring
    rw [h]
    have : 0 ≤ 5 * ρ * Λ ^ 3 := by positivity
    exact mul_le_of_le_one_right this hθ
  have hbad : E0 * (36 * x ^ 5 / x ^ 12) ≤ 1 / (3 * x ^ 3) := by
    have h1 : E0 * (36 * x ^ 5 / x ^ 12) ≤ 36 * x ^ 5 / x ^ 12 := by
      have : 0 ≤ 36 * x ^ 5 / x ^ 12 := by positivity
      calc E0 * (36 * x ^ 5 / x ^ 12) ≤ 1 * (36 * x ^ 5 / x ^ 12) :=
            mul_le_mul_of_nonneg_right hE01 this
        _ = 36 * x ^ 5 / x ^ 12 := one_mul _
    refine h1.trans ?_
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hx4' : (256 : ℝ) ≤ x ^ 4 := by
      have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 4) hx4 4
      norm_num at this; linarith
    have h8 : 0 < x ^ 8 := by positivity
    calc 36 * x ^ 5 * (3 * x ^ 3) = 108 * x ^ 8 := by ring
      _ ≤ 256 * x ^ 8 := by linarith
      _ ≤ x ^ 4 * x ^ 8 := mul_le_mul_of_nonneg_right hx4' h8.le
      _ = 1 * x ^ 12 := by ring
  -- piece Q4, Taylor
  have htaylor : Kr * (10000 * x ^ 4 * (1 + x) ^ 6 * Δ ^ ((3 : ℝ) / 2))
      ≤ 1 / (3 * x ^ 3) := by
    rw [hsqrt]
    have hsΔ0 : 0 ≤ Real.sqrt Δ := Real.sqrt_nonneg _
    have e : Kr * (10000 * x ^ 4 * (1 + x) ^ 6 * (Δ * Real.sqrt Δ))
        = 10000 * x ^ 4 * (1 + x) ^ 6 * (Kr * Δ) * Real.sqrt Δ := by ring
    rw [e, hKΔ]
    have h1 : 10000 * x ^ 4 * (1 + x) ^ 6 * E0 * Real.sqrt Δ
        ≤ 10000 * x ^ 4 * (1 + x) ^ 6 * 1 * (1 / (x + 1) ^ A) := by
      gcongr
    refine h1.trans ?_
    rw [mul_one, mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
    -- `3 · 10⁴ x⁷ (1+x)⁶ ≤ (x+1)^A`
    have hx7 : x ^ 7 ≤ (x + 1) ^ 7 := pow_le_pow_left₀ hx0.le (by linarith) 7
    have h5 : (30000 : ℝ) ≤ (x + 1) ^ 7 := by
      calc (30000 : ℝ) ≤ 10 ^ 7 := by norm_num
        _ ≤ (x + 1) ^ 7 := pow_le_pow_left₀ (by norm_num) (by linarith) 7
    have hA' : 10000 * x ^ 4 * (1 + x) ^ 6 * (3 * x ^ 3) = 30000 * x ^ 7 * (x + 1) ^ 6 := by ring
    rw [hA']
    calc 30000 * x ^ 7 * (x + 1) ^ 6 ≤ (x + 1) ^ 7 * (x + 1) ^ 7 * (x + 1) ^ 6 := by gcongr
      _ = (x + 1) ^ 20 := by rw [← pow_add, ← pow_add]
      _ ≤ (x + 1) ^ A := pow_le_pow_right₀ hx1 (by omega)
      _ = 1 * (x + 1) ^ A := (one_mul _).symm
  -- piece Q4, primitive side
  have hkdisc : Kr * (3 * x ^ 2 * Δ ^ 2) ≤ 1 / (3 * x ^ 3) := by
    have e : Kr * (3 * x ^ 2 * Δ ^ 2) = 3 * x ^ 2 * (Kr * Δ) * Δ := by ring
    rw [e, hKΔ]
    have h1 : 3 * x ^ 2 * E0 * Δ ≤ 3 * x ^ 2 * 1 * (1 / Kr) := by gcongr
    refine h1.trans ?_
    rw [mul_one, mul_one_div, div_le_div_iff₀ hKr0 (by positivity), hKr]
    have hx5 : x ^ 5 ≤ (x + 1) ^ 5 := pow_le_pow_left₀ hx0.le (by linarith) 5
    have h9 : (9 : ℝ) ≤ (x + 1) ^ 2 := by
      calc (9 : ℝ) ≤ 10 ^ 2 := by norm_num
        _ ≤ (x + 1) ^ 2 := pow_le_pow_left₀ (by norm_num) (by linarith) 2
    have h160 : (x + 1) ^ 7 ≤ (x + 1) ^ (2 * A) := pow_le_pow_right₀ hx1 (by omega)
    calc 3 * x ^ 2 * (3 * x ^ 3) = 9 * x ^ 5 := by ring
      _ ≤ (x + 1) ^ 2 * (x + 1) ^ 5 := by gcongr
      _ = (x + 1) ^ 7 := by rw [← pow_add]
      _ ≤ (x + 1) ^ (2 * A) := h160
      _ = 1 * (x + 1) ^ (2 * A) := (one_mul _).symm
  -- assembly
  have hKc : Kr * eq729c x ρ Λ (3 / x ^ 12) Δ ≤ 5 * ρ * Λ ^ 3 + Λ ^ 3 := by
    rw [hXeq]
    have e : Kr * (Δ * (5 * x * ρ ^ 2 * Λ ^ 4 + 36 * x ^ 5 / x ^ 12)
        + 10000 * x ^ 4 * (1 + x) ^ 6 * Δ ^ ((3 : ℝ) / 2) + 3 * x ^ 2 * Δ ^ 2)
        = (Kr * Δ) * (5 * x * ρ ^ 2 * Λ ^ 4) + (Kr * Δ) * (36 * x ^ 5 / x ^ 12)
          + Kr * (10000 * x ^ 4 * (1 + x) ^ 6 * Δ ^ ((3 : ℝ) / 2))
          + Kr * (3 * x ^ 2 * Δ ^ 2) := by ring
    rw [e, hKΔ]
    have hsum : 1 / (3 * x ^ 3) + 1 / (3 * x ^ 3) + 1 / (3 * x ^ 3) = 1 / x ^ 3 := by
      field_simp; ring
    linarith
  have hin : 0 ≤ ρ * Λ ^ 3 + Kr * eq729c x ρ Λ (3 / x ^ 12) Δ := by
    have := Eq729B_c_nonneg hx0.le hρ0 hΛ0.le (by positivity : (0 : ℝ) ≤ 3 / x ^ 12) hΔ0
    positivity
  have hρΛ3 : Λ ^ 3 ≤ ρ * Λ ^ 3 := le_mul_of_one_le_left (by positivity) hρ
  calc Real.exp (E0 * (2 * x * (ρ * Λ))) * (ρ * Λ ^ 3 + Kr * eq729c x ρ Λ (3 / x ^ 12) Δ)
      ≤ 7.4 * (ρ * Λ ^ 3 + Kr * eq729c x ρ Λ (3 / x ^ 12) Δ) :=
        mul_le_mul_of_nonneg_right hexp hin
    _ ≤ 7.4 * (7 * (ρ * Λ ^ 3)) := by gcongr; linarith
    _ = 51.8 * (ρ * Λ ^ 3) := by ring
    _ ≤ 56 * (ρ * Λ ^ 3) := by
        have : 0 ≤ ρ * Λ ^ 3 := by positivity
        linarith
    _ = 56 * ρ * Λ ^ 3 := by ring

/-! ### The exponent chain as real-variable lemmas (`d = 3, 4` by script in the prove report) -/

/-- (i) `Bctl(t₁) ≤ 2 𝓑_{η_Q,0}` from `η_Q ≤ 2 (1 - t₁)` alone (`zRange`: `1 - t₀ ≥ η_Q/2`): no `hell` (cf. `STWB_compare`, `Main/ZTransfer.lean:174`). -/
theorem Eq729B_bctl_le_two_calB (sz : Sizes d) (n : ℕ) (hd : 2 ≤ d) {t η : ℝ} (hη : 0 < η) (h2 : η ≤ 2 * (1 - t)) :
    sz.Bctl n t ≤ 2 * calB sz n η 0 := by
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hL : (0 : ℝ) < ((sz.L n : ℕ) : ℝ) := by have := sz.three_le_L n; exact_mod_cast (by omega : 0 < sz.L n)
  have hu : 0 < 1 - t := by linarith
  have hN : ((sz.size n : ℕ) : ℝ) = ((sz.W n : ℕ) : ℝ) ^ d * ((sz.L n : ℕ) : ℝ) ^ d := by simp [Sizes.size, mul_pow]
  have hWd : ((sz.W n : ℕ) : ℝ) ^ 2 * (0 + ((sz.W n : ℕ) : ℝ)) ^ (d - 2) = ((sz.W n : ℕ) : ℝ) ^ d := by
    rw [zero_add, ← pow_add]; congr 1; omega
  have h1 : (sz.lam n ^ 2 + (1 - t))⁻¹ ≤ 2 * (sz.lam n ^ 2 + η)⁻¹ := by
    rw [show 2 * (sz.lam n ^ 2 + η)⁻¹ = (2⁻¹ * (sz.lam n ^ 2 + η))⁻¹ by field_simp]
    exact inv_anti₀ (by positivity) (by nlinarith [sq_nonneg (sz.lam n)])
  have h2' : (((sz.L n : ℕ) : ℝ) ^ d * (1 - t))⁻¹ ≤ 2 * (((sz.L n : ℕ) : ℝ) ^ d * η)⁻¹ := by
    rw [show 2 * (((sz.L n : ℕ) : ℝ) ^ d * η)⁻¹ = (2⁻¹ * (((sz.L n : ℕ) : ℝ) ^ d * η))⁻¹ by field_simp]
    exact inv_anti₀ (by positivity) (by nlinarith [pow_pos hL d])
  unfold Sizes.Bctl Bparam calB
  rw [abs_of_pos hu, hWd, hN]
  simp only [Nat.cast_zero, zero_add, one_pow, inv_one, mul_one]
  calc (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * ((sz.lam n ^ 2 + (1 - t))⁻¹ + (((sz.L n : ℕ) : ℝ) ^ d * (1 - t))⁻¹)
      ≤ (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (2 * (sz.lam n ^ 2 + η)⁻¹ + 2 * (((sz.L n : ℕ) : ℝ) ^ d * η)⁻¹) := by gcongr
    _ = 2 * ((sz.lam n ^ 2 + η)⁻¹ / ((sz.W n : ℕ) : ℝ) ^ d + (((sz.W n : ℕ) : ℝ) ^ d * ((sz.L n : ℕ) : ℝ) ^ d * η)⁻¹) := by
        field_simp

/-- `L^d η_Q W^{4𝔡/3} = ilambda W^{-d/2+𝔡}` (`η_Q = W^{-𝔡/3} ilambda W^{d/2} / N`, `N = W^d L^d`). -/
theorem Eq729B_Ld_mul_etaQ (sz : Sizes d) (n : ℕ) (𝔡 : ℝ) :
    ((sz.L n : ℕ) : ℝ) ^ d * ouEtaQ sz 𝔡 n * ((sz.W n : ℕ) : ℝ) ^ (4 * 𝔡 / 3) =
      sz.lam n * ((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2 + 𝔡) := by
  have hw : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hL : (0 : ℝ) < ((sz.L n : ℕ) : ℝ) := by have := sz.three_le_L n; exact_mod_cast (by omega : 0 < sz.L n)
  have hp : ((sz.W n : ℕ) : ℝ) ^ (-(𝔡 / 3)) * ((sz.W n : ℕ) : ℝ) ^ ((d : ℝ) / 2) * ((sz.W n : ℕ) : ℝ) ^ (4 * 𝔡 / 3) =
      ((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2 + 𝔡) * ((sz.W n : ℕ) : ℝ) ^ d := by
    rw [← Real.rpow_add hw, ← Real.rpow_add hw, ← Real.rpow_natCast, ← Real.rpow_add hw]; congr 1; ring
  have hN : Nsz sz n = ((sz.W n : ℕ) : ℝ) ^ d * ((sz.L n : ℕ) : ℝ) ^ d := by simp [Nsz, Sizes.size, mul_pow]
  unfold ouEtaQ; rw [hN]
  generalize ((sz.W n : ℕ) : ℝ) ^ (-(𝔡 / 3)) = A at hp ⊢
  generalize ((sz.W n : ℕ) : ℝ) ^ ((d : ℝ) / 2) = B at hp ⊢
  generalize ((sz.W n : ℕ) : ℝ) ^ (4 * 𝔡 / 3) = R at hp ⊢
  generalize ((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2 + 𝔡) = a at hp ⊢
  have hP : ((sz.W n : ℕ) : ℝ) ^ d ≠ 0 := by positivity
  have hQ : ((sz.L n : ℕ) : ℝ) ^ d ≠ 0 := by positivity
  generalize ((sz.W n : ℕ) : ℝ) ^ d = P at hp hP ⊢
  generalize ((sz.L n : ℕ) : ℝ) ^ d = Q at hQ ⊢
  field_simp
  linear_combination (sz.lam n) * hp

/-- (i) `hell` from the scales: `1 - t₀ ≤ η_Q/c`, `ζ ≤ N^{-1+τ_U}`, `ilambda ≥ W^{-d/2+𝔡}`, `2/c ≤ W^{4𝔡/3}`, `2 N^{τ_U} ≤ W^{2𝔡}`
give `L^d (1 - t₁) ≤ ilambda²` (RBM2D: `L² (1 - t₁) ≤ 1` from `η_Q ≤ L^{-2}`). -/
theorem Eq729B_hell_of_scales (sz : Sizes d) (n : ℕ) {𝔡 c τU ζ t0 : ℝ} (hc : 0 < c)
    (hlo : ((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2 + 𝔡) ≤ sz.lam n)
    (h1t : 1 - t0 ≤ ouEtaQ sz 𝔡 n / c) (hζ : 0 ≤ ζ) (hζN : ζ ≤ Nsz sz n ^ (-1 + τU)) (ht01 : t0 ≤ 1)
    (hc4 : 2 / c ≤ ((sz.W n : ℕ) : ℝ) ^ (4 * 𝔡 / 3)) (hN : 2 * Nsz sz n ^ τU ≤ ((sz.W n : ℕ) : ℝ) ^ (2 * 𝔡)) :
    ((sz.L n : ℕ) : ℝ) ^ d * (1 - (1 - ζ) * t0) ≤ sz.lam n ^ 2 := by
  have hw : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hL : (0 : ℝ) < ((sz.L n : ℕ) : ℝ) := by have := sz.three_le_L n; exact_mod_cast (by omega : 0 < sz.L n)
  have hNpos : 0 < Nsz sz n := by have := sz.one_le_size n; exact_mod_cast (by omega : 0 < sz.size n)
  have hN' : Nsz sz n = ((sz.W n : ℕ) : ℝ) ^ d * ((sz.L n : ℕ) : ℝ) ^ d := by simp [Nsz, Sizes.size, mul_pow]
  have ha0 : 0 < ((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2 + 𝔡) := Real.rpow_pos_of_pos hw _
  have hη0 : 0 < ouEtaQ sz 𝔡 n := by
    unfold ouEtaQ
    have := Real.rpow_pos_of_pos hw (-(𝔡 / 3)); have := Real.rpow_pos_of_pos hw ((d : ℝ) / 2)
    have := lt_of_lt_of_le ha0 hlo; positivity
  have hid := Eq729B_Ld_mul_etaQ sz n 𝔡
  have hLd : 0 < ((sz.L n : ℕ) : ℝ) ^ d := by positivity
  have hWd : 0 < ((sz.W n : ℕ) : ℝ) ^ d := by positivity
  have ha2 : (((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2 + 𝔡)) ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d = ((sz.W n : ℕ) : ℝ) ^ (2 * 𝔡) := by
    rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul hw.le, ← Real.rpow_natCast ((sz.W n : ℕ) : ℝ) d, ← Real.rpow_add hw]
    congr 1; push_cast; ring
  have hρc : 2 ≤ ((sz.W n : ℕ) : ℝ) ^ (4 * 𝔡 / 3) * c := (div_le_iff₀ hc).1 hc4
  generalize ((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2 + 𝔡) = a at *
  generalize ((sz.W n : ℕ) : ℝ) ^ (4 * 𝔡 / 3) = ρ at *
  have hx : ((sz.L n : ℕ) : ℝ) ^ d * (ouEtaQ sz 𝔡 n / c) ≤ sz.lam n * a / 2 := by   -- `L^d η_Q / c ≤ ilambda a / 2`
    have e : ((sz.L n : ℕ) : ℝ) ^ d * (ouEtaQ sz 𝔡 n / c) * (ρ * c) = sz.lam n * a := by rw [← hid]; field_simp
    nlinarith [mul_le_mul_of_nonneg_left hρc (show 0 ≤ ((sz.L n : ℕ) : ℝ) ^ d * (ouEtaQ sz 𝔡 n / c) by positivity)]
  have hy : ((sz.L n : ℕ) : ℝ) ^ d * ζ ≤ a ^ 2 / 2 := by                            -- `L^d ζ ≤ a² / 2`
    have h1 : ((sz.L n : ℕ) : ℝ) ^ d * Nsz sz n ^ (-1 + τU) = Nsz sz n ^ τU / ((sz.W n : ℕ) : ℝ) ^ d := by
      rw [Real.rpow_add hNpos, Real.rpow_neg_one, hN']; field_simp
    have h2 : Nsz sz n ^ τU / ((sz.W n : ℕ) : ℝ) ^ d ≤ a ^ 2 / 2 := by
      rw [div_le_iff₀ hWd, div_mul_eq_mul_div, le_div_iff₀ (by norm_num : (0 : ℝ) < 2), ha2]; linarith
    exact (mul_le_mul_of_nonneg_left hζN hLd.le).trans (h1 ▸ h2)
  have hζt : ζ * t0 ≤ ζ := by nlinarith
  calc ((sz.L n : ℕ) : ℝ) ^ d * (1 - (1 - ζ) * t0) = ((sz.L n : ℕ) : ℝ) ^ d * ((1 - t0) + ζ * t0) := by ring
    _ ≤ ((sz.L n : ℕ) : ℝ) ^ d * (ouEtaQ sz 𝔡 n / c) + ((sz.L n : ℕ) : ℝ) ^ d * ζ := by
        rw [← mul_add]; exact mul_le_mul_of_nonneg_left (by linarith) hLd.le
    _ ≤ sz.lam n * a / 2 + a ^ 2 / 2 := add_le_add hx hy
    _ ≤ sz.lam n ^ 2 := by nlinarith

/-- (ii) Claim A (rows `h730`, `hscale`): `4 N^{2τ_U} ≤ N η_Q = W^{-𝔡/3} ilambda W^{d/2}` for `τ_U ≤ 𝔠𝔡/12`, `W ≥ N^𝔠`,
`ilambda ≥ W^{-d/2+𝔡}`, `W^{𝔡/2} ≥ 4` (RBM2D `Eq729B:1163`: `4 N^{2τ_U} ≤ W^{2/3}` with `η_Q = W^{2/3}/N`). -/
theorem Eq729B_claimA (sz : Sizes d) (n : ℕ) {𝔠 𝔡 τU : ℝ} (h𝔡 : 0 < 𝔡) (hτU : τU ≤ 𝔠 * 𝔡 / 12)
    (hNW : Nsz sz n ^ 𝔠 ≤ ((sz.W n : ℕ) : ℝ)) (h4 : 4 ≤ ((sz.W n : ℕ) : ℝ) ^ (𝔡 / 2))
    (hlo : ((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2 + 𝔡) ≤ sz.lam n) :
    4 * Nsz sz n ^ (2 * τU) ≤ Nsz sz n * ouEtaQ sz 𝔡 n := by
  have hw : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hN1 : 1 ≤ Nsz sz n := by exact_mod_cast sz.one_le_size n
  have hNpos : 0 < Nsz sz n := by linarith
  have h1 : ((sz.W n : ℕ) : ℝ) ^ (2 * 𝔡 / 3) ≤ Nsz sz n * ouEtaQ sz 𝔡 n := by       -- `N η_Q ≥ W^{2𝔡/3}`
    have e : Nsz sz n * ouEtaQ sz 𝔡 n = ((sz.W n : ℕ) : ℝ) ^ (-(𝔡 / 3)) * (sz.lam n * ((sz.W n : ℕ) : ℝ) ^ ((d : ℝ) / 2)) := by
      unfold ouEtaQ; field_simp
    have e2 : ((sz.W n : ℕ) : ℝ) ^ (2 * 𝔡 / 3) =
        ((sz.W n : ℕ) : ℝ) ^ (-(𝔡 / 3)) * (((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2 + 𝔡) * ((sz.W n : ℕ) : ℝ) ^ ((d : ℝ) / 2)) := by
      rw [← Real.rpow_add hw, ← Real.rpow_add hw]; congr 1; ring
    rw [e, e2]; gcongr
  have h2 : Nsz sz n ^ (2 * τU) ≤ ((sz.W n : ℕ) : ℝ) ^ (𝔡 / 6) :=                    -- `N^{2τ_U} ≤ (N^𝔠)^{𝔡/6} ≤ W^{𝔡/6}`
    calc Nsz sz n ^ (2 * τU) ≤ Nsz sz n ^ (𝔠 * (𝔡 / 6)) := Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
      _ = (Nsz sz n ^ 𝔠) ^ (𝔡 / 6) := Real.rpow_mul hNpos.le _ _
      _ ≤ ((sz.W n : ℕ) : ℝ) ^ (𝔡 / 6) := Real.rpow_le_rpow (Real.rpow_nonneg hNpos.le _) hNW (by linarith)
  have h3 : ((sz.W n : ℕ) : ℝ) ^ (2 * 𝔡 / 3) = ((sz.W n : ℕ) : ℝ) ^ (𝔡 / 2) * ((sz.W n : ℕ) : ℝ) ^ (𝔡 / 6) := by
    rw [← Real.rpow_add hw]; congr 1; ring
  have h5 : 0 ≤ ((sz.W n : ℕ) : ℝ) ^ (𝔡 / 6) := Real.rpow_nonneg hw.le _
  calc 4 * Nsz sz n ^ (2 * τU) ≤ 4 * ((sz.W n : ℕ) : ℝ) ^ (𝔡 / 6) := by gcongr
    _ ≤ ((sz.W n : ℕ) : ℝ) ^ (𝔡 / 2) * ((sz.W n : ℕ) : ℝ) ^ (𝔡 / 6) := by gcongr
    _ ≤ Nsz sz n * ouEtaQ sz 𝔡 n := h3 ▸ h1

/-- (ii) `h730` and `hscale` from Claim A: `η_{t₀} = √t₀ η_Q ≥ η_Q/4` (`t₀ ≥ 1/16`), `t₀ - t₁ = ζ t₀ ≤ N^{-1+τ_U}`. -/
theorem Eq729B_h730_hscale_real {N ηQ s ζt τU : ℝ} (hN : 1 ≤ N) (hτ : 0 < τU) (hη : 0 < ηQ) (hs : 1 / 4 ≤ s)
    (hA : 4 * N ^ (2 * τU) ≤ N * ηQ) (hζ : ζt ≤ N ^ (-1 + τU)) :
    ζt ≤ N ^ (-τU) * (s * ηQ) ∧ (N * (s * ηQ))⁻¹ ≤ N ^ (-τU) := by
  have hN0 : 0 < N := by linarith
  have hp : N ^ (2 * τU) = N ^ τU * N ^ τU := by rw [← Real.rpow_add hN0]; ring_nf
  have hq : N ^ (-τU) * N ^ τU = 1 := by rw [← Real.rpow_add hN0]; simp
  have hτ1 : N ^ τU ≤ N ^ (2 * τU) := Real.rpow_le_rpow_of_exponent_le hN (by linarith)
  have hnn : 0 ≤ N ^ (-τU) := Real.rpow_nonneg hN0.le _
  have h1 : 1 / 4 * (N * ηQ) ≤ N * (s * ηQ) := by nlinarith [mul_le_mul_of_nonneg_left hs (mul_pos hN0 hη).le]
  refine ⟨hζ.trans ?_, ?_⟩
  · rw [Real.rpow_add hN0, Real.rpow_neg_one, inv_mul_le_iff₀ hN0]
    have : N ^ τU * N ^ τU ≤ N * (s * ηQ) := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right this hnn]
  · rw [Real.rpow_neg hN0.le]
    exact inv_anti₀ (Real.rpow_pos_of_pos hN0 _) (by nlinarith)

/-- (iii) `qdBoundExp = W^τ 𝓑² (X + 𝓑)`, `X` of `initTerm` (exponents `-(1:ℝ)/5`, `Endpoints.lean:101`, and `-(1/5:ℝ)` agree). -/
theorem Eq729B_qdBoundExp_eq (sz : Sizes d) (n : ℕ) (τ η : ℝ) : qdBoundExp sz n τ η = ((sz.W n : ℕ) : ℝ) ^ τ *
    (calB sz n η 0 ^ 2 * ((sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d) ^ (-(1 / 5 : ℝ)) + calB sz n η 0)) := by
  unfold qdBoundExp; rw [neg_div]; ring

/-- (iii) The (7.47) assembly: `t₀ N^{δ'} ((N η_{t₀})^{-3} + I₀(t₁)) ≤ W^τ 𝓑² (X + 𝓑)`, `𝓑 = 𝓑_{η_Q,0}`, `η_{t₀} = √t₀ η_Q`, `t₀ ∈ [1/16, 1]`,
`𝓑 ≥ (N η_Q)⁻¹`, `𝓑(t₁) ≤ 2 𝓑`, `12 N^{δ'} ≤ W^τ` (`t₀ (N η_{t₀})^{-3} ≤ 4 (N η_Q)^{-3}`; RBM2D `Eq729B_scale_747`). -/
theorem Eq729B_assembly_747 {t0 N ηQ B X Bt M Wt : ℝ} (ht0 : 1 / 16 ≤ t0) (ht01 : t0 ≤ 1) (hN : 0 < N) (hη : 0 < ηQ)
    (hB : (N * ηQ)⁻¹ ≤ B) (hX : 0 ≤ X) (hBt0 : 0 ≤ Bt) (hBt : Bt ≤ 2 * B) (hM : 0 ≤ M) (hW : 12 * M ≤ Wt) :
    t0 * (M * ((N * (Real.sqrt t0 * ηQ))⁻¹ ^ 3 + Bt ^ 2 * (X + Bt))) ≤ Wt * (B ^ 2 * (X + B)) := by
  have ht0' : 0 < t0 := by linarith
  have hs0 : 0 < Real.sqrt t0 := Real.sqrt_pos.2 ht0'
  have hss : Real.sqrt t0 * Real.sqrt t0 = t0 := Real.mul_self_sqrt ht0'.le
  have hs4 : 1 / 4 ≤ Real.sqrt t0 := by
    rw [show (1 : ℝ) / 4 = Real.sqrt (1 / 16) by rw [show (1 : ℝ) / 16 = (1 / 4) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt ht0
  have hB0 : 0 ≤ B := le_trans (inv_nonneg.2 (mul_pos hN hη).le) hB
  have hscale : t0 * (N * (Real.sqrt t0 * ηQ))⁻¹ ^ 3 ≤ 4 * (N * ηQ)⁻¹ ^ 3 := by
    generalize Real.sqrt t0 = r at hs0 hss hs4 ⊢
    have e : t0 * (N * (r * ηQ))⁻¹ ^ 3 = r⁻¹ * (N * ηQ)⁻¹ ^ 3 := by rw [← hss]; field_simp
    rw [e]
    have : r⁻¹ ≤ 4 := by rw [inv_le_comm₀ hs0 (by norm_num)]; linarith
    gcongr
  have hB3 : (N * ηQ)⁻¹ ^ 3 ≤ B ^ 2 * (X + B) :=
    calc (N * ηQ)⁻¹ ^ 3 ≤ B ^ 3 := by gcongr
      _ ≤ B ^ 2 * (X + B) := by nlinarith [mul_nonneg (sq_nonneg B) hX]
  have hI : Bt ^ 2 * (X + Bt) ≤ 8 * (B ^ 2 * (X + B)) :=
    calc Bt ^ 2 * (X + Bt) ≤ (2 * B) ^ 2 * (2 * (X + B)) := by gcongr; nlinarith
      _ = 8 * (B ^ 2 * (X + B)) := by ring
  calc t0 * (M * ((N * (Real.sqrt t0 * ηQ))⁻¹ ^ 3 + Bt ^ 2 * (X + Bt)))
      = M * (t0 * (N * (Real.sqrt t0 * ηQ))⁻¹ ^ 3 + t0 * (Bt ^ 2 * (X + Bt))) := by ring
    _ ≤ M * (4 * (N * ηQ)⁻¹ ^ 3 + 1 * (Bt ^ 2 * (X + Bt))) := by gcongr
    _ ≤ M * (4 * (B ^ 2 * (X + B)) + 8 * (B ^ 2 * (X + B))) :=
        mul_le_mul_of_nonneg_left (add_le_add (by linarith) (by linarith)) hM
    _ = (12 * M) * (B ^ 2 * (X + B)) := by ring
    _ ≤ Wt * (B ^ 2 * (X + B)) := by gcongr

/-- (ii) final normalisation of target 1: `harith` is the ported `Eq729B_arith` (RBM2D `:368`, `N`-only); `I₀` needs `exp E ≤ 7.4`. -/
theorem Eq729B_final_729 {E ρ I0 Λ3 Kc : ℝ} (hρ : 0 ≤ ρ) (hI : 0 ≤ I0) (hΛ : 0 ≤ Λ3) (he : Real.exp E ≤ 7.4)
    (harith : Real.exp E * (ρ * Λ3 + Kc) ≤ 56 * ρ * Λ3) : Real.exp E * (ρ * I0 + Kc) ≤ 56 * ρ * (Λ3 + I0) := by
  nlinarith [mul_nonneg (Real.exp_pos E).le (mul_nonneg hρ hΛ), mul_nonneg hρ hI, mul_le_mul_of_nonneg_right he (mul_nonneg hρ hI)]

/-- (i) evolution factor `(1 + Δ·2NρΛ)^K ≤ exp((t₀ - t₁)·2NρΛ) ≤ e²`: `h730`, `dt = t₀ - t₁ ≤ M η_{t₀}`, `M = N^{-τ_U}`, `ρ M ≤ 1`. -/
theorem Eq729B_gronwall_factor {N η dt M ρ : ℝ} (hN : 0 < N) (hη : 0 < η) (hρ0 : 0 ≤ ρ) (h730 : dt ≤ M * η) (hρ : ρ * M ≤ 1) :
    Real.exp (dt * (2 * N * (ρ * (N * η)⁻¹))) ≤ Real.exp 2 := by
  refine Real.exp_le_exp.2 ?_
  have e : dt * (2 * N * (ρ * (N * η)⁻¹)) = 2 * ρ * (dt / η) := by field_simp
  rw [e]
  have : dt / η ≤ M := by rwa [div_le_iff₀ hη]
  nlinarith [mul_le_mul_of_nonneg_left this hρ0]


/-! ### Inputs at the size parameter `n` (RBM2D `Eq729B:149-351`; `Eq729B_Kt_one`, `_initial`, `_K_bounds` are the merged
`Hyp_Kt_one`, `Hyp_Kt_detDom`, `HypA.lean:690-712`) -/

theorem Eq729B_nine_le_size (sz : Sizes d) (hd : 3 ≤ d) (n : ℕ) : 9 ≤ sz.size n := by
  unfold Sizes.size
  have hW := sz.W_pos n
  have hL := sz.three_le_L n
  have h3 : 3 ≤ sz.W n * sz.L n := by nlinarith
  calc 9 = 3 ^ 2 := by norm_num
    _ ≤ 3 ^ d := Nat.pow_le_pow_right (by norm_num) (by omega)
    _ ≤ (sz.W n * sz.L n) ^ d := Nat.pow_le_pow_left h3 d

theorem Eq729B_gueScale_pos (sz : Sizes d) {E : ℕ → ℝ} {n : ℕ} (hE : |E n| < 2) {t : ℝ} (ht : t < 1) :
    0 < gueScale sz E n t :=
  mul_pos (Nsz_pos sz n) (eq729_eta_pos hE ht)

theorem Eq729B_gueScale_anti (sz : Sizes d) {E : ℕ → ℝ} {n : ℕ} (hE : |E n| < 2) {u t : ℝ} (hut : u ≤ t) :
    gueScale sz E n t ≤ gueScale sz E n u :=
  mul_le_mul_of_nonneg_left (eq729_eta_le hE hut) (Nat.cast_nonneg _)

theorem Eq729B_inv_scale_le (sz : Sizes d) {E : ℕ → ℝ} {n : ℕ} (hE : |E n| < 2) {u t : ℝ}
    (hut : u ≤ t) (ht : t < 1) : (gueScale sz E n u)⁻¹ ≤ (gueScale sz E n t)⁻¹ :=
  inv_anti₀ (Eq729B_gueScale_pos sz hE ht) (Eq729B_gueScale_anti sz hE hut)

theorem Eq729B_gridTime_zero (t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) : gridTime t1 t0 K n 0 = t1 n := by
  unfold gridTime; simp

/-- `0 ≤ I₀(t)` (the initial term of `STExp2`). -/
theorem Eq729B_initTerm_nonneg (sz : Sizes d) (n : ℕ) (t : ℝ) : 0 ≤ Eq729B_initTerm sz n t := by
  have hB : 0 ≤ sz.Bctl n t := by unfold Sizes.Bctl Bparam; positivity
  unfold Eq729B_initTerm
  positivity

/-- **The only transfer between carriers**: the one-time law at step `0` (`map_gueH_zero`; RBM2D `Eq729B_transfer`, `:330`). -/
theorem Eq729B_transfer (sz : Sizes d) (t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) (ht1 : 0 ≤ t1 n) (z : ℂ)
    (I : LoopIdx (Zd d (sz.L n))) :
    ∫ ω, loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (gueH sz t1 t0 K n 0 ω)) z I ∂(Pgue sz)
      = ∫ ω, loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (sz.seqHflow n (t1 n) ω)) z I
          ∂(sz.seqP) := by
  have hc : Measurable fun M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ =>
      loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) M) z I :=
    (RBM.Gauss.walk_measurable_loopL d (sz.L n) (sz.W n) z I).comp
      (RBM.Gauss.walk_measurable_blockMat d (sz.L n) (sz.W n))
  have hHf : Measurable (sz.seqHflow n (t1 n)) :=
    measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun j => Sizes.measurable_seqHflow_entry sz n (t1 n) i j
  calc ∫ ω, loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (gueH sz t1 t0 K n 0 ω)) z I ∂(Pgue sz)
      = ∫ M, loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) M) z I
          ∂((Pgue sz).map (gueH sz t1 t0 K n 0)) :=
        (integral_map (gueH_measurable sz t1 t0 K n 0).aemeasurable hc.aestronglyMeasurable).symm
    _ = ∫ M, loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) M) z I
          ∂((sz.seqP).map (sz.seqHflow n (t1 n))) := by
        rw [map_gueH_zero sz t1 t0 K n ht1]
    _ = ∫ ω, loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (sz.seqHflow n (t1 n) ω)) z I
          ∂(sz.seqP) :=
        integral_map hHf.aemeasurable hc.aestronglyMeasurable

/-! ### The bad events of `GUEPathBounds.lk` (RBM2D `Eq729B:497-524`) -/

/-- The failure event of `hP.lk m` at level `τ`, size index `n`. -/
private def Eq729B_Bad (sz : Sizes d) (E t1 t0 : ℕ → ℝ) (Kt : ∀ n, ℝ → LoopIdx (Zd d (sz.L n)) → ℂ) (n0 m : ℕ)
    (τ : ℝ) (n : ℕ) : Set (PathΩ sz) :=
  {ω | ∃ p : Fin (gueGridK sz n0 n + 1) × (Fin m → Bool) × (Fin m → Zd d (sz.L n)),
    ((sz.size n : ℕ) : ℝ) ^ τ *
        (gueScale sz E n (gridTime t1 t0 (gueGridK sz n0) n p.1))⁻¹ ^ m <
      ‖loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (gueH sz t1 t0 (gueGridK sz n0) n p.1 ω))
          (zt (E n) (gridTime t1 t0 (gueGridK sz n0) n p.1)) (loopOf p.2.1 p.2.2) -
        Kt n (gridTime t1 t0 (gueGridK sz n0) n p.1) (loopOf p.2.1 p.2.2)‖}

private theorem Eq729B_not_bad {sz : Sizes d} {E t1 t0 : ℕ → ℝ} {Kt : ∀ n, ℝ → LoopIdx (Zd d (sz.L n)) → ℂ}
    {n0 m n : ℕ} {τ : ℝ} {ω : PathΩ sz} (hω : ω ∉ Eq729B_Bad sz E t1 t0 Kt n0 m τ n) {k : ℕ}
    (hk : k ≤ gueGridK sz n0 n) (σ : Fin m → Bool) (a : Fin m → Zd d (sz.L n)) :
    ‖loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (gueH sz t1 t0 (gueGridK sz n0) n k ω))
          (zt (E n) (gridTime t1 t0 (gueGridK sz n0) n k)) (loopOf σ a) -
        Kt n (gridTime t1 t0 (gueGridK sz n0) n k) (loopOf σ a)‖
      ≤ ((sz.size n : ℕ) : ℝ) ^ τ *
        (gueScale sz E n (gridTime t1 t0 (gueGridK sz n0) n k))⁻¹ ^ m := by
  by_contra h
  exact hω ⟨(⟨k, Nat.lt_succ_of_le hk⟩, σ, a), lt_of_not_ge h⟩

/-! ### The statement `gueGrid_eq729` -/

/-- **(7.29) at `t₀` on the GUE-phase grid** ([YY_25] §7.2, cited by the paper in the resolvent estimates after `417`),
`σ = (+, σ₂)`, on the size scale `N = sz.size n = (W L)^d`, in the loss form `N^δ ((N η_{t₀})^{-3} + I₀(t₁))`
(`Eq729B_Concl`), with `GUEPathBounds`, `gueGridK` and the initial term `sz.STExp2 E t1` (`ML:exp` at `t₁`, `I₀` = its right
side).  Port of RBM2D `gueGrid_eq729` (`Eq729B:531`) under the port map of T2352/T2353; new: `hd`, `hlam` (for
`gueGrid_expect_oneLoop`), `hell`, `hKb`, `hKinit` as the merged `Hyp_Kt_detDom` (T2352a), `hB := STExp2`, `I₀` in the
conclusion (T2356a).  The `∀ n` hypotheses are those of RBM2D and of `Hyp_Kt_detDom`. -/
theorem gueGrid_eq729 (sz : Sizes d) (hd : 3 ≤ d) {κ τU Λ : ℝ} (hκ : 0 < κ) (hτU : 0 < τU) (n0 : ℕ) (hn0 : 3 ≤ n0)
    {E t1 t0 : ℕ → ℝ} (hsize : Tendsto sz.size atTop atTop) (hlam : ∀ᶠ n in atTop, 0 < sz.lam n ∧ sz.lam n ≤ Λ)
    (hE : ∀ n, |E n| ≤ 2 - κ) (ht1 : ∀ n, 0 ≤ t1 n) (ht10 : ∀ n, t1 n ≤ t0 n) (ht0 : ∀ n, t0 n < 1)
    (h730 : ∀ᶠ n in atTop, t0 n - t1 n ≤ Nsz sz n ^ (-τU) * etaT (E n) (t0 n))
    (hscale : ∀ᶠ n in atTop, (gueScale sz E n (t0 n))⁻¹ ≤ Nsz sz n ^ (-τU))
    (hell : ∀ᶠ n in atTop, ((sz.L n : ℕ) : ℝ) ^ d * (1 - t1 n) ≤ sz.lam n ^ 2) (hKb : sz.STKbound E)
    (Kt : ∀ n, ℝ → LoopIdx (Zd d (sz.L n)) → ℂ)
    (hKinit : ∀ n {k : ℕ} (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)),
      Kt n (t1 n) (loopOf σ a) = sz.STKloop n (E n) (t1 n) σ a)
    (hK : ∀ n, ∀ s ∈ Set.Icc (t1 n) (t0 n), ∀ I : LoopIdx (Zd d (sz.L n)), I.WF → 1 ≤ I.length →
      I.length ≤ 4 * n0 →
      HasDerivWithinAt (fun u => Kt n u I) (primRhsGUE d (sz.L n) (sz.W n) (Kt n s) I) (Set.Icc (t1 n) (t0 n)) s)
    (hK2 : ∀ n, ∀ s ∈ Set.Icc (t1 n) (t0 n), ∀ (σ₁ σ₂ : Bool) (a b : Zd d (sz.L n)),
      Kt n s ⟨[σ₁, σ₂], [a, b]⟩ =
        kTwoGUE d (sz.L n) (sz.W n) (sz.lam n) (mSigma (E n)) (t1 n) s σ₁ σ₂ a b)
    (hB : sz.STExp2 E t1) (hP : GUEPathBounds sz E t1 t0 (gueGridK sz n0) n0 Kt) :
    Eq729B_Concl sz E t1 t0 (gueGridK sz n0) := by
  intro δ hδ
  have hE2 : ∀ n, |E n| < 2 := fun n => by linarith [hE n]
  set τ : ℝ := min (δ / 4) τU with hτdef
  have hτ : 0 < τ := lt_min (by positivity) hτU
  have hττU : τ ≤ τU := min_le_right _ _
  have hτδ : τ ≤ δ / 4 := min_le_left _ _
  have hKne := gueGridK_ne_zero sz n0
  have hKone : ∀ n, ∀ s ∈ Set.Icc (t1 n) (t0 n), ∀ σ a, Kt n s ⟨[σ], [a]⟩ = mSigma (E n) σ :=
    fun n s hs σ a => Hyp_Kt_one sz n0 (by omega) Kt hKinit hK n hs σ a
  have hKmem : ∀ n k, k ≤ gueGridK sz n0 n →
      gridTime t1 t0 (gueGridK sz n0) n k ∈ Set.Icc (t1 n) (t0 n) := fun n k hk =>
    eq729_time_mem (ht10 n) (hKne n) hk
  -- the 1-loop input of Lemma 5.15, from `hP.lk 1` (the `+` 1-loops, `K̃ = m`)
  have h1 : StochDomAt (Pgue sz) sz.size
      (fun n (p : Fin (gueGridK sz n0 n + 1) × Zd d (sz.L n)) ω =>
        ‖loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (gueH sz t1 t0 (gueGridK sz n0) n p.1 ω))
            (zt (E n) (gridTime t1 t0 (gueGridK sz n0) n p.1)) ⟨[true], [p.2]⟩ - mE (E n)‖)
      (fun n p _ => (gueScale sz E n (gridTime t1 t0 (gueGridK sz n0) n p.1))⁻¹) := by
    intro τ' hτ' D hD
    filter_upwards [hP.lk 1 le_rfl (by omega) τ' hτ' D hD] with n hn
    refine le_trans (measure_mono ?_) hn
    rintro ω ⟨⟨k, a⟩, hlt⟩
    refine ⟨(k, (fun _ => true), (fun _ => a)), ?_⟩
    have hk : (k : ℕ) ≤ gueGridK sz n0 n := Nat.lt_succ_iff.1 k.isLt
    have hKt := hKone n _ (hKmem n k hk) true a
    have hloop : (loopOf (fun _ : Fin 1 => true) (fun _ : Fin 1 => a) : LoopIdx (Zd d (sz.L n))) =
        ⟨[true], [a]⟩ := rfl
    have hm : mSigma (E n) true = mE (E n) := by simp [mSigma]
    change ((sz.size n : ℕ) : ℝ) ^ τ' *
        (gueScale sz E n (gridTime t1 t0 (gueGridK sz n0) n k))⁻¹ ^ 1 <
      ‖loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (gueH sz t1 t0 (gueGridK sz n0) n k ω))
          (zt (E n) (gridTime t1 t0 (gueGridK sz n0) n k))
            (loopOf (fun _ : Fin 1 => true) (fun _ : Fin 1 => a)) -
        Kt n (gridTime t1 t0 (gueGridK sz n0) n k)
          (loopOf (fun _ : Fin 1 => true) (fun _ : Fin 1 => a))‖
    rw [hloop, hKt, hm, pow_one]
    exact hlt
  have hX := gueGrid_expect_oneLoop sz hd hκ hsize hlam hE ht1 ht10 ht0 hKne h1 τ hτ
  have hKb' := Hyp_Kt_detDom sz hκ hτU n0 hE ht1 ht10 ht0 hsize h730 hell hKb Kt hKinit hK τ hτ
  have hb1 := hP.lk 1 le_rfl (by omega) τ hτ 12 (by norm_num)
  have hb2 := hP.lk 2 (by norm_num) (by omega) τ hτ 12 (by norm_num)
  have hb3 := hP.lk 3 (by norm_num) hn0 τ hτ 12 (by norm_num)
  have hsz' : sz.SizeTendsto := tendsto_natCast_atTop_iff.mpr hsize
  have hin := det_of_prec sz hsz' (U := fun n => (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)))
    (ξ := fun n p _ => ‖(∫ ω, sz.Lloop n (E n) (t1 n) p.1 p.2 ω ∂(sz.seqP)) -
        sz.STKloop n (E n) (t1 n) p.1 p.2‖)
    (ζ := fun n _ _ => Eq729B_initTerm sz n (t1 n)) (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl) hB hτ
  filter_upwards [h730, hscale, hell, hKb', hX, hb1, hb2, hb3, hin,
    hsize.eventually (eventually_le_rpow 56 hτ)] with n h730n hscalen hellN hKbn hXn hb1n hb2n hb3n
    hinn hN56
  intro σ₂ a b
  change Eq729B_eqErr sz E t1 t0 (gueGridK sz n0) n σ₂ a b ≤
    ((sz.size n : ℕ) : ℝ) ^ δ * ((gueScale sz E n (t0 n))⁻¹ ^ 3 + Eq729B_initTerm sz n (t1 n))
  -- the size parameter `n`: scales
  set N : ℝ := ((sz.size n : ℕ) : ℝ) with hNdef
  have hN9 : (9 : ℝ) ≤ N := by rw [hNdef]; exact_mod_cast Eq729B_nine_le_size sz hd n
  have hN1 : (1 : ℝ) ≤ N := by linarith
  have hN0 : (0 : ℝ) < N := by linarith
  have ht0n0 : 0 ≤ t0 n := (ht1 n).trans (ht10 n)
  set η0 : ℝ := etaT (E n) (t0 n) with hη0
  have hη0pos : 0 < η0 := eq729_eta_pos (hE2 n) (ht0 n)
  have hη01 : η0 ≤ 1 := by
    rw [hη0]; unfold etaT
    have him : (mE (E n)).im ≤ 1 := by
      have := Complex.im_le_norm (mE (E n)); rwa [norm_mE (hE2 n).le] at this
    have h0 : 0 ≤ 1 - t0 n := by linarith [ht0 n]
    have h1' : 1 - t0 n ≤ 1 := by linarith
    have hm0 : 0 ≤ (mE (E n)).im := (mE_im_pos (hE2 n)).le
    calc (1 - t0 n) * (mE (E n)).im ≤ 1 * 1 := mul_le_mul h1' him hm0 zero_le_one
      _ = 1 := one_mul 1
  set Λ : ℝ := (gueScale sz E n (t0 n))⁻¹ with hΛ
  have hΛdef : Λ = (N * η0)⁻¹ := rfl
  have hΛpos : 0 < Λ := by rw [hΛdef]; positivity
  have hΛτ : Λ ≤ N ^ (-τU) := hscalen
  have hΛ1 : Λ ≤ 1 := hΛτ.trans (Real.rpow_le_one_of_one_le_of_nonpos hN1 (by linarith))
  set ρ : ℝ := N ^ τ with hρ
  have hρ1 : 1 ≤ ρ := Real.one_le_rpow hN1 hτ.le
  have hρ0 : 0 ≤ ρ := by linarith
  have hρτ : ρ * N ^ (-τU) ≤ 1 := by
    rw [hρ, ← Real.rpow_add hN0]
    exact Real.rpow_le_one_of_one_le_of_nonpos hN1 (by linarith)
  have hρΛ : ρ * Λ ≤ 1 := (mul_le_mul_of_nonneg_left hΛτ hρ0).trans hρτ
  have hinvs : ∀ s ∈ Set.Icc (t1 n) (t0 n), (gueScale sz E n s)⁻¹ ≤ Λ := fun s hs =>
    Eq729B_inv_scale_le sz (hE2 n) hs.2 (ht0 n)
  have hinvs0 : ∀ s ∈ Set.Icc (t1 n) (t0 n), 0 ≤ (gueScale sz E n s)⁻¹ := fun s hs =>
    (inv_pos.2 (Eq729B_gueScale_pos sz (hE2 n) (lt_of_le_of_lt hs.2 (ht0 n)))).le
  have hinvsn : ∀ s ∈ Set.Icc (t1 n) (t0 n), ∀ m : ℕ, (gueScale sz E n s)⁻¹ ^ m ≤ Λ ^ m :=
    fun s hs m => pow_le_pow_left₀ (hinvs0 s hs) (hinvs s hs) m
  -- `K̃` on 2- and 3-loops
  have hK2b : ∀ s ∈ Set.Icc (t1 n) (t0 n), ∀ s1 s2 x y,
      ‖Kt n s ⟨[s1, s2], [x, y]⟩‖ ≤ ρ * Λ := fun s hs s1 s2 x y => by
    have h := hKbn s hs ⟨[s1, s2], [x, y]⟩ rfl (by simp [LoopIdx.length]) (by simp [LoopIdx.length]; omega)
    have h' : ‖Kt n s ⟨[s1, s2], [x, y]⟩‖ ≤ N ^ τ * (gueScale sz E n s)⁻¹ := by simpa [LoopIdx.length] using h
    exact h'.trans (mul_le_mul_of_nonneg_left (hinvs s hs) hρ0)
  have hK3b : ∀ s ∈ Set.Icc (t1 n) (t0 n), ∀ s1 s2 s3 x y w,
      ‖Kt n s ⟨[s1, s2, s3], [x, y, w]⟩‖ ≤ ρ * Λ ^ 2 := fun s hs s1 s2 s3 x y w => by
    have h := hKbn s hs ⟨[s1, s2, s3], [x, y, w]⟩ rfl (by simp [LoopIdx.length]) (by simp [LoopIdx.length]; omega)
    have h' : ‖Kt n s ⟨[s1, s2, s3], [x, y, w]⟩‖ ≤ N ^ τ * (gueScale sz E n s)⁻¹ ^ 2 := by
      simpa [LoopIdx.length] using h
    exact h'.trans (mul_le_mul_of_nonneg_left (hinvsn s hs 2) hρ0)
  have hKd : ∀ s ∈ Set.Icc (t1 n) (t0 n), ∀ s1 s2 x y,
      HasDerivWithinAt (fun s => Kt n s ⟨[s1, s2], [x, y]⟩)
        (primRhsGUE d (sz.L n) (sz.W n) (Kt n s) ⟨[s1, s2], [x, y]⟩)
        (Set.Icc (t1 n) (t0 n)) s := fun s hs s1 s2 x y =>
    hK n s hs _ rfl (by simp [LoopIdx.length]) (by simp [LoopIdx.length]; omega)
  -- Lemma 5.15 at the grid times
  have hX' : ∀ k < gueGridK sz n0 n, ∀ a,
      ‖(∫ ω, eq729F sz t1 t0 (gueGridK sz n0) E n k ω ⟨[true], [a]⟩ ∂(Pgue sz)) - mE (E n)‖
        ≤ ρ * Λ ^ 2 := by
    intro k hk a
    have := hXn (⟨k, by omega⟩, a)
    exact this.trans (mul_le_mul_of_nonneg_left (hinvsn _ (hKmem n k hk.le) 2) hρ0)
  -- the bad event
  set B : Set (PathΩ sz) := Eq729B_Bad sz E t1 t0 Kt n0 1 τ n ∪ Eq729B_Bad sz E t1 t0 Kt n0 2 τ n
    ∪ Eq729B_Bad sz E t1 t0 Kt n0 3 τ n with hBdef
  have hNrpow : N ^ (-(12 : ℝ)) = 1 / N ^ 12 := by
    rw [Real.rpow_neg hN0.le, show (12 : ℝ) = ((12 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
      one_div]
  have hBm : Pgue sz B ≤ ENNReal.ofReal (3 / N ^ 12) := by
    have hb1' : Pgue sz (Eq729B_Bad sz E t1 t0 Kt n0 1 τ n) ≤ ENNReal.ofReal (N ^ (-(12 : ℝ))) := hb1n
    have hb2' : Pgue sz (Eq729B_Bad sz E t1 t0 Kt n0 2 τ n) ≤ ENNReal.ofReal (N ^ (-(12 : ℝ))) := hb2n
    have hb3' : Pgue sz (Eq729B_Bad sz E t1 t0 Kt n0 3 τ n) ≤ ENNReal.ofReal (N ^ (-(12 : ℝ))) := hb3n
    have h12 : Pgue sz (Eq729B_Bad sz E t1 t0 Kt n0 1 τ n ∪ Eq729B_Bad sz E t1 t0 Kt n0 2 τ n)
        ≤ Pgue sz (Eq729B_Bad sz E t1 t0 Kt n0 1 τ n) + Pgue sz (Eq729B_Bad sz E t1 t0 Kt n0 2 τ n) :=
      measure_union_le _ _
    have h123 : Pgue sz B ≤ Pgue sz (Eq729B_Bad sz E t1 t0 Kt n0 1 τ n ∪ Eq729B_Bad sz E t1 t0 Kt n0 2 τ n)
        + Pgue sz (Eq729B_Bad sz E t1 t0 Kt n0 3 τ n) := measure_union_le _ _
    refine (h123.trans (add_le_add h12 le_rfl)).trans ?_
    refine (add_le_add (add_le_add hb1' hb2') hb3').trans (le_of_eq ?_)
    rw [hNrpow, ← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1; ring
  have hg1 : ∀ ω ∉ B, ∀ k < gueGridK sz n0 n, ∀ σ a,
      ‖eq729F sz t1 t0 (gueGridK sz n0) E n k ω ⟨[σ], [a]⟩ - mSigma (E n) σ‖ ≤ ρ * Λ := by
    intro ω hω k hk σ a
    have hω1 : ω ∉ Eq729B_Bad sz E t1 t0 Kt n0 1 τ n := fun h => hω (Or.inl (Or.inl h))
    have h : ‖eq729F sz t1 t0 (gueGridK sz n0) E n k ω ⟨[σ], [a]⟩
        - Kt n (gridTime t1 t0 (gueGridK sz n0) n k) ⟨[σ], [a]⟩‖
        ≤ N ^ τ * (gueScale sz E n (gridTime t1 t0 (gueGridK sz n0) n k))⁻¹ ^ 1 :=
      Eq729B_not_bad hω1 hk.le (fun _ => σ) (fun _ => a)
    rw [hKone n _ (hKmem n k hk.le) σ a] at h
    refine h.trans ?_
    rw [pow_one]
    exact mul_le_mul_of_nonneg_left (hinvs _ (hKmem n k hk.le)) hρ0
  have hg2 : ∀ ω ∉ B, ∀ k < gueGridK sz n0 n, ∀ s1 s2 x y,
      ‖eq729F sz t1 t0 (gueGridK sz n0) E n k ω ⟨[s1, s2], [x, y]⟩
        - Kt n (gridTime t1 t0 (gueGridK sz n0) n k) ⟨[s1, s2], [x, y]⟩‖ ≤ ρ * Λ ^ 2 := by
    intro ω hω k hk s1 s2 x y
    have hω2 : ω ∉ Eq729B_Bad sz E t1 t0 Kt n0 2 τ n := fun h => hω (Or.inl (Or.inr h))
    have h := Eq729B_not_bad hω2 hk.le ![s1, s2] ![x, y]
    exact h.trans (mul_le_mul_of_nonneg_left (hinvsn _ (hKmem n k hk.le) 2) hρ0)
  have hg3 : ∀ ω ∉ B, ∀ k < gueGridK sz n0 n, ∀ s1 s2 s3 x y w,
      ‖eq729F sz t1 t0 (gueGridK sz n0) E n k ω ⟨[s1, s2, s3], [x, y, w]⟩
        - Kt n (gridTime t1 t0 (gueGridK sz n0) n k) ⟨[s1, s2, s3], [x, y, w]⟩‖
          ≤ ρ * Λ ^ 3 := by
    intro ω hω k hk s1 s2 s3 x y w
    have hω3 : ω ∉ Eq729B_Bad sz E t1 t0 Kt n0 3 τ n := fun h => hω (Or.inr h)
    have h := Eq729B_not_bad hω3 hk.le ![s1, s2, s3] ![x, y, w]
    exact h.trans (mul_le_mul_of_nonneg_left (hinvsn _ (hKmem n k hk.le) 3) hρ0)
  -- the initial term, from `sz.STExp2 E t1`
  have ht1mem : t1 n ∈ Set.Icc (t1 n) (t0 n) := ⟨le_rfl, ht10 n⟩
  have hI0 := Eq729B_initTerm_nonneg sz n (t1 n)
  have hinit : ∀ s1 s2 x y,
      ‖eq729e sz t1 t0 (gueGridK sz n0) E Kt n 0 ⟨[s1, s2], [x, y]⟩‖ ≤ ρ * Eq729B_initTerm sz n (t1 n) := by
    intro s1 s2 x y
    have hl : (loopOf ![s1, s2] ![x, y] : LoopIdx (Zd d (sz.L n))) = ⟨[s1, s2], [x, y]⟩ := by
      simp [loopOf, List.ofFn_succ]
    have he : eq729e sz t1 t0 (gueGridK sz n0) E Kt n 0 ⟨[s1, s2], [x, y]⟩
        = (∫ ω, sz.Lloop n (E n) (t1 n) ![s1, s2] ![x, y] ω ∂(sz.seqP)) -
          sz.STKloop n (E n) (t1 n) ![s1, s2] ![x, y] := by
      unfold eq729e eq729F
      rw [← hl, Eq729B_gridTime_zero, hKinit n ![s1, s2] ![x, y],
        Eq729B_transfer sz t1 t0 (gueGridK sz n0) n (ht1 n) (zt (E n) (t1 n))]
      simp only [Sizes.Lloop, loopFine, loopM_eq_loopL]
    rw [he]
    exact hinn (![s1, s2], ![x, y]) 0
  -- `N Δ ≤ 1`
  have hKge : N + 1 ≤ (gueGridK sz n0 n : ℝ) := by
    unfold gueGridK; push_cast
    exact le_self_pow₀ (by linarith) (by omega)
  have hKpos : (0 : ℝ) < (gueGridK sz n0 n : ℝ) := by linarith
  have hE0 : 0 ≤ t0 n - t1 n := by linarith [ht10 n]
  have hE01 : t0 n - t1 n ≤ 1 := by linarith [ht1 n, ht0 n]
  have hMΔ : N * gridStep t1 t0 (gueGridK sz n0) n ≤ 1 := by
    unfold gridStep
    rw [mul_div_assoc']
    rw [div_le_one hKpos]
    nlinarith
  -- the one-size bound at `n`
  have hper := Eq729B_perN sz (gueGridK sz n0) Kt (hE2 n) (ht1 n) (ht10 n) (ht0 n) (hKne n)
    (Λ := Λ) (ρ := ρ) (p := 3 / N ^ 12) (B0 := ρ * Eq729B_initTerm sz n (t1 n)) hΛdef hΛ1
    hρ0 hρΛ (by positivity) hMΔ hK2b hK3b hKd hX' hBm hg1 hg2 hg3 hinit true σ₂ a b
  have hΛN : 1 ≤ N * Λ := by
    rw [hΛdef, ← div_eq_mul_inv, le_div_iff₀ (by positivity), one_mul]
    calc N * η0 ≤ N * 1 := mul_le_mul_of_nonneg_left hη01 hN0.le
      _ = N := mul_one _
  have hθ : (t0 n - t1 n) * N * Λ * ρ ≤ 1 := by
    have h1 : (t0 n - t1 n) * N * Λ = (t0 n - t1 n) / η0 := by
      rw [hΛdef]; field_simp
    have h2 : (t0 n - t1 n) / η0 ≤ N ^ (-τU) := by
      rw [div_le_iff₀ hη0pos]; exact h730n
    rw [h1]
    calc (t0 n - t1 n) / η0 * ρ ≤ N ^ (-τU) * ρ :=
          mul_le_mul_of_nonneg_right h2 hρ0
      _ = ρ * N ^ (-τU) := mul_comm _ _
      _ ≤ 1 := hρτ
  have hKr : ((gueGridK sz n0 n : ℕ) : ℝ) = (N + 1) ^ (2 * (16 * n0 + 32)) := by
    rw [show 2 * (16 * n0 + 32) = 32 * n0 + 64 by ring]
    unfold gueGridK; push_cast; rfl
  have harith := Eq729B_arith (N := sz.size n) (Eq729B_nine_le_size sz hd n) (ρ := ρ) (Λ := Λ)
    (E0 := t0 n - t1 n) (Δ := gridStep t1 t0 (gueGridK sz n0) n) (Kr := (gueGridK sz n0 n : ℝ))
    (16 * n0 + 32) (by omega) hKr hρ1 hΛpos hΛN hE01 (eq729_KΔ (hKne n))
    (eq729_step_nonneg (ht10 n)) hθ
  have hexp : Real.exp ((t0 n - t1 n) * (2 * N * (ρ * Λ))) ≤ 7.4 :=
    (Eq729B_gronwall_factor hN0 hη0pos hρ0 h730n hρτ).trans Eq729B_exp_two_lt.le   -- chain link (i), `h730`
  have hfin := Eq729B_final_729 hρ0 hI0 (by positivity : 0 ≤ Λ ^ 3) hexp harith
  -- `56 N^τ ≤ N^δ`
  have hW : 56 * ρ ≤ N ^ δ := by
    calc 56 * ρ ≤ N ^ τ * N ^ τ := mul_le_mul_of_nonneg_right hN56 hρ0
      _ = N ^ (τ + τ) := (Real.rpow_add hN0 _ _).symm
      _ ≤ N ^ δ := Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  -- the left side is `e_K`
  have hlhs : Eq729B_eqErr sz E t1 t0 (gueGridK sz n0) n σ₂ a b
      = ‖eq729e sz t1 t0 (gueGridK sz n0) E Kt n (gueGridK sz n0 n) ⟨[true, σ₂], [a, b]⟩‖ := by
    unfold Eq729B_eqErr eq729e eq729F
    rw [gridTime_last t1 t0 (gueGridK sz n0) n (hKne n),
      hK2 n (t0 n) ⟨ht10 n, le_rfl⟩ true σ₂ a b]
  rw [hlhs]
  calc ‖eq729e sz t1 t0 (gueGridK sz n0) E Kt n (gueGridK sz n0 n) ⟨[true, σ₂], [a, b]⟩‖
      ≤ 56 * ρ * (Λ ^ 3 + Eq729B_initTerm sz n (t1 n)) := hper.trans hfin
    _ ≤ N ^ δ * (Λ ^ 3 + Eq729B_initTerm sz n (t1 n)) :=
        mul_le_mul_of_nonneg_right hW (by positivity)

/-! ### The (7.47) step, part 1: the law (7.26) and the main term (RBM2D `Eq729B:784-884`) -/

/-- `gueH` at size `n` depends on `t₁` only through `t₁ n`. -/
theorem Eq729B_gueH_congr (sz : Sizes d) {t1 t1' : ℕ → ℝ} (t0 : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ)
    (h : t1 n = t1' n) : gueH sz t1 t0 K n k = gueH sz t1' t0 K n k := by
  unfold gueH gridStep; rw [h]

theorem Eq729B_avg2_eq_loop (sz : Sizes d) (n : ℕ)
    (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (z : ℂ) (σ : Bool)
    (a b : Zd d (sz.L n)) :
    avg2 sz n (fun x y => Gres H z true x y * Gres H z σ y x) a b =
      loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) H) z ⟨[true, σ], [b, a]⟩ := by
  have hI : (⟨[true, σ], [b, a]⟩ : LoopIdx (Zd d (sz.L n))) = loopOf ![true, σ] ![b, a] := by
    simp [loopOf, List.ofFn_succ]
  rw [hI, ← loopM_eq_loopL]
  unfold loopM
  simp only [List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, mul_one]
  have e0 : (![true, σ] : Fin 2 → Bool) 0 = true := rfl
  have e1 : (![true, σ] : Fin 2 → Bool) (Fin.succ 0) = σ := rfl
  have f0 : (![b, a] : Fin 2 → Zd d (sz.L n)) 0 = b := rfl
  have f1 : (![b, a] : Fin 2 → Zd d (sz.L n)) (Fin.succ 0) = a := rfl
  rw [e0, e1, f0, f1, Gres_blockMat', Gres_blockMat', ← Matrix.mul_assoc, trace_four]
  unfold avg2
  rw [inv_pow]

/-- `(G(σ))ᴴ = G(!σ)` for Hermitian `H` (copy of the private `Gres_conjTranspose'`, `Main/ZTransfer.lean:344`). -/
private theorem Eq729B_Gres_conjTranspose {ι : Type*} [Fintype ι] [DecidableEq ι] {H : Matrix ι ι ℂ}
    (hH : H.IsHermitian) (z : ℂ) (σ : Bool) : (Gres H z σ)ᴴ = Gres H z (!σ) := by
  have hH' : Hᴴ = H := hH
  cases σ with
  | true =>
    simp only [Gres, ↓reduceIte, Bool.not_true, Bool.false_eq_true,
      ← Matrix.nonsing_inv_eq_ringInverse, Matrix.conjTranspose_nonsing_inv,
      Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, Matrix.conjTranspose_one, hH',
      Complex.star_def]
  | false =>
    simp only [Gres, Bool.false_eq_true, ↓reduceIte, Bool.not_false,
      ← Matrix.nonsing_inv_eq_ringInverse, Matrix.conjTranspose_nonsing_inv,
      Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, Matrix.conjTranspose_one, hH',
      Complex.star_def, Complex.conj_conj]

/-- `|G_xy|² = G_xy G^{-}_yx` for Hermitian `H`, block-averaged. -/
theorem Eq729B_avg2_abs_sq (sz : Sizes d) (n : ℕ)
    {H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ} (hH : H.IsHermitian) (z : ℂ)
    (a b : Zd d (sz.L n)) :
    avg2 sz n (fun x y => ((‖Gres H z true x y‖ ^ 2 : ℝ) : ℂ)) a b =
      avg2 sz n (fun x y => Gres H z true x y * Gres H z false y x) a b := by
  unfold avg2
  congr 1
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  have h := congrFun (congrFun (Eq729B_Gres_conjTranspose hH z true) y) x
  simp only [Matrix.conjTranspose_apply, Bool.not_true] at h
  change ((‖Gres H z true x y‖ ^ 2 : ℝ) : ℂ) = Gres H z true x y * Gres H z false y x
  rw [← h, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]

/-- `blockMat` commutes with the scalar action. -/
theorem Eq729B_blockMat_smul {L W : ℕ} [NeZero L] [NeZero W] (c : ℂ) (M : Matrix (Idx d L W) (Idx d L W) ℂ) :
    blockMat d L W (c • M) = c • blockMat d L W M := by
  ext i j; simp [blockMat, Matrix.submatrix_apply, Matrix.smul_apply]

/-- **The law (7.26) in expectation**: at the last grid step, `𝔼 [avg2 G_xy G^σ_yx](z) = t₀ 𝔼 𝓛_{t₀,(+,σ),(b,a)}`,
`t₀ = lemT z`, `t₁ = (1 - ζ(t)) t₀` (`map_gueH_last`, `GUEPhaseGrid_gloop_two_smul_lemT_eq`; RBM2D `Eq729B_law726`, `:822`);
`t₁` need agree with the formula at `n` only. -/
theorem Eq729B_law726 (sz : Sizes d) {t t0 t1 : ℕ → ℝ} (K : ℕ → ℕ) (n : ℕ) {z : ℂ}
    (hz : 0 < z.im) (ht0 : t0 n = lemT z) (ht1 : t1 n = (1 - ouZeta (t n)) * t0 n) (ht : 0 ≤ t n)
    (hK : K n ≠ 0) (σ : Bool) (a b : Zd d (sz.L n)) :
    ∫ ω, avg2 sz n (fun x y => Gres (ouMat (UNModel.band sz) n (t n) ω) z true x y *
        Gres (ouMat (UNModel.band sz) n (t n) ω) z σ y x) a b ∂(ouP (UNModel.band sz) n) =
      (lemT z : ℂ) * ∫ ω, loopL d (sz.L n) (sz.W n)
        (blockMat d (sz.L n) (sz.W n) (gueH sz t1 t0 K n (K n) ω))
        (zt (lemE z) (lemT z)) ⟨[true, σ], [b, a]⟩ ∂(Pgue sz) := by
  have ht0pos : 0 ≤ t0 n := by rw [ht0]; exact (lemT_pos hz).le
  set F : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ → ℂ := fun M =>
    loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) M) (zt (lemE z) (lemT z))
      ⟨[true, σ], [b, a]⟩ with hF
  have hFm : Measurable F :=
    (RBM.Gauss.walk_measurable_loopL d (sz.L n) (sz.W n) _ _).comp
      (RBM.Gauss.walk_measurable_blockMat d (sz.L n) (sz.W n))
  have hg : Measurable (fun ω : Sizes.SeqΩ sz × Ω d (sz.L n) (sz.W n) =>
      ((Real.sqrt (t0 n) : ℝ) : ℂ) • ouMat (UNModel.band sz) n (t n) ω) :=
    (measurable_ouMat (UNModel.band sz) n (t n)).const_smul ((Real.sqrt (t0 n) : ℝ) : ℂ)
  have hgueH : gueH sz t1 t0 K n (K n) = gueH sz (fun n => (1 - ouZeta (t n)) * t0 n) t0 K n (K n) :=
    Eq729B_gueH_congr sz t0 K n (K n) ht1
  have hint : ∫ ω, loopL d (sz.L n) (sz.W n)
        (blockMat d (sz.L n) (sz.W n) (gueH sz t1 t0 K n (K n) ω))
        (zt (lemE z) (lemT z)) ⟨[true, σ], [b, a]⟩ ∂(Pgue sz) =
      ∫ ω, F (((Real.sqrt (t0 n) : ℝ) : ℂ) • ouMat (UNModel.band sz) n (t n) ω)
        ∂(ouP (UNModel.band sz) n) := by
    rw [hgueH]
    calc ∫ ω, F (gueH sz (fun n => (1 - ouZeta (t n)) * t0 n) t0 K n (K n) ω) ∂(Pgue sz)
        = ∫ M, F M ∂((Pgue sz).map (gueH sz (fun n => (1 - ouZeta (t n)) * t0 n) t0 K n (K n))) :=
          (integral_map (gueH_measurable sz _ t0 K n (K n)).aemeasurable hFm.aestronglyMeasurable).symm
      _ = ∫ M, F M ∂((ouP (UNModel.band sz) n).map
            (fun ω => ((Real.sqrt (t0 n) : ℝ) : ℂ) • ouMat (UNModel.band sz) n (t n) ω)) := by
          rw [map_gueH_last sz t0 t K n ht0pos ht hK]
      _ = ∫ ω, F (((Real.sqrt (t0 n) : ℝ) : ℂ) • ouMat (UNModel.band sz) n (t n) ω)
            ∂(ouP (UNModel.band sz) n) :=
          integral_map hg.aemeasurable hFm.aestronglyMeasurable
  rw [hint, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
  change avg2 sz n (fun x y => Gres (ouMat (UNModel.band sz) n (t n) ω) z true x y *
        Gres (ouMat (UNModel.band sz) n (t n) ω) z σ y x) a b =
    (lemT z : ℂ) * loopL d (sz.L n) (sz.W n)
      (blockMat d (sz.L n) (sz.W n) (((Real.sqrt (t0 n) : ℝ) : ℂ) • ouMat (UNModel.band sz) n (t n) ω))
      (zt (lemE z) (lemT z)) ⟨[true, σ], [b, a]⟩
  have hl : (loopOf ![true, σ] ![b, a] : LoopIdx (Zd d (sz.L n))) = ⟨[true, σ], [b, a]⟩ := by
    simp [loopOf, List.ofFn_succ]
  have h := GUEPhaseGrid_gloop_two_smul_lemT_eq (blockMat d (sz.L n) (sz.W n) (ouMat (UNModel.band sz) n (t n) ω)) hz σ b a
  rw [hl] at h
  rw [Eq729B_avg2_eq_loop, h, ht0, Eq729B_blockMat_smul]

/-- `𝓑 = W^{-d} B_{t,0} ≥ 0`. -/
theorem Eq729B_Bctl_nonneg (sz : Sizes d) (n : ℕ) (t : ℝ) : 0 ≤ sz.Bctl n t := by
  unfold Sizes.Bctl Bparam; positivity

/-- `K̃_{(σ₁,σ₂),(a,b)} = K̃_{(σ₁,σ₂),(b,a)}` (`Θ` is symmetric, `Theta_transpose`; the `(b, a)` order of the 2-loops of `zTrace`). -/
theorem Eq729B_kTwoGUE_symm (d L : ℕ) [NeZero L] (W : ℕ) (hL : 3 ≤ L) (g : ℝ) (m : Bool → ℂ) (t1 t : ℝ)
    (σ₁ σ₂ : Bool) (hξ : ‖(t1 : ℂ) * (m σ₁ * m σ₂)‖ < 1) (a b : Zd d L) :
    kTwoGUE d L W g m t1 t σ₁ σ₂ a b = kTwoGUE d L W g m t1 t σ₁ σ₂ b a := by
  have h := congrFun (congrFun (Theta_transpose d L g (norm_SB d L g hL) hξ) a) b
  simp only [Matrix.transpose_apply] at h
  unfold kTwoGUE
  rw [h]

/-- (7.47) at one size index: `‖𝔼 [avg2 G_xy G^σ_yx] - prof‖ ≤ qdBoundExp` from the loss-form (7.29) at `(E', t₁, t₀)` at the
labels `(b, a)`; the main term `prof = t₀ K̃_{t₀}`. -/
theorem Eq729B_core747 (sz : Sizes d) (hd : 3 ≤ d) (𝔡 : ℝ) {κ τ δ : ℝ} (hκ : 0 < κ) {E t E' t0 t1 : ℕ → ℝ}
    {K : ℕ → ℕ} (n : ℕ) (σ : Bool) (a b : Zd d (sz.L n)) (hE : |E n| ≤ 2 - κ) (ht : 0 ≤ t n) (hK : K n ≠ 0)
    (hη : 0 < ouEtaQ sz 𝔡 n) (hη1 : ouEtaQ sz 𝔡 n ≤ 1) (hE' : E' n = lemE (Eq729B_zQ sz 𝔡 E n))
    (ht0 : t0 n = lemT (Eq729B_zQ sz 𝔡 E n)) (ht1 : t1 n = (1 - ouZeta (t n)) * t0 n)
    (hH : Eq729B_eqErr sz E' t1 t0 K n σ b a ≤
      Nsz sz n ^ δ * ((gueScale sz E' n (t0 n))⁻¹ ^ 3 + Eq729B_initTerm sz n (t1 n)))
    (hW : 12 * Nsz sz n ^ δ ≤ ((sz.W n : ℕ) : ℝ) ^ τ) {prof : ℂ}
    (hprof : (lemT (Eq729B_zQ sz 𝔡 E n) : ℂ) * kTwoGUE d (sz.L n) (sz.W n) (sz.lam n)
        (mSigma (lemE (Eq729B_zQ sz 𝔡 E n))) ((1 - ouZeta (t n)) * lemT (Eq729B_zQ sz 𝔡 E n))
        (lemT (Eq729B_zQ sz 𝔡 E n)) true σ b a = prof) :
    ‖(∫ ω, avg2 sz n (fun x y => Gres (ouMat (UNModel.band sz) n (t n) ω) (Eq729B_zQ sz 𝔡 E n) true x y *
        Gres (ouMat (UNModel.band sz) n (t n) ω) (Eq729B_zQ sz 𝔡 E n) σ y x) a b ∂(ouP (UNModel.band sz) n)) - prof‖ ≤
      qdBoundExp sz n τ (ouEtaQ sz 𝔡 n) := by
  set z : ℂ := Eq729B_zQ sz 𝔡 E n with hzdef
  have hzim : z.im = ouEtaQ sz 𝔡 n := by simp [hzdef, Eq729B_zQ]
  have hzre : z.re = E n := by simp [hzdef, Eq729B_zQ]
  have hz : 0 < z.im := by rw [hzim]; exact hη
  have hz1 : z.im ≤ 1 := by rw [hzim]; exact hη1
  have hzκ : |z.re| ≤ 2 - κ := by rw [hzre]; exact hE
  obtain ⟨-, hu16, -, hhalf⟩ := lemma28_quant hκ hz hz1 hzκ
  obtain ⟨-, -, -, -, hhalf⟩ := zRange κ hκ z hz hz1 hzκ
  have hu1 := lemT_lt_one hz
  have hu0 : 0 ≤ lemT z := by linarith
  have hζ0 := ZeroModeProfile_ouZeta_nonneg ht
  have hζ1 := ZeroModeProfile_ouZeta_le_one (t n)
  -- the law (7.26) and the main term
  rw [Eq729B_law726 sz K n hz ht0 ht1 ht hK σ a b, ← hprof, ← mul_sub, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg hu0]
  have heq : Eq729B_eqErr sz E' t1 t0 K n σ b a =
      ‖(∫ ω, loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (gueH sz t1 t0 K n (K n) ω))
          (zt (lemE z) (lemT z)) ⟨[true, σ], [b, a]⟩ ∂(Pgue sz)) -
        kTwoGUE d (sz.L n) (sz.W n) (sz.lam n) (mSigma (lemE z)) ((1 - ouZeta (t n)) * lemT z) (lemT z)
          true σ b a‖ := by
    unfold Eq729B_eqErr
    rw [ht1, ht0, hE']
  rw [← heq]
  -- the scales
  have hsc : gueScale sz E' n (t0 n) = Nsz sz n * (Real.sqrt (lemT z) * ouEtaQ sz 𝔡 n) := by
    unfold gueScale
    rw [hE', ht0, ← eq729_zt_im, zt_im_lemma28 hz, hzim]
  have hu01 : ouEtaQ sz 𝔡 n ≤ 2 * (1 - t1 n) := by
    have : t1 n ≤ lemT z := by rw [ht1, ht0]; nlinarith
    rw [← hzim]; linarith
  have hBt := Eq729B_bctl_le_two_calB sz n (by omega) hη hu01
  have hNpos := Nsz_pos sz n
  have hB : (Nsz sz n * ouEtaQ sz 𝔡 n)⁻¹ ≤ calB sz n (ouEtaQ sz 𝔡 n) 0 := by
    unfold calB
    have : 0 ≤ (sz.lam n ^ 2 + ouEtaQ sz 𝔡 n)⁻¹ / (((sz.W n : ℕ) : ℝ) ^ 2 * (0 + ((sz.W n : ℕ) : ℝ)) ^ (d - 2)) := by
      positivity
    linarith
  have hX : 0 ≤ (sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d) ^ (-(1 / 5 : ℝ)) := Real.rpow_nonneg (by positivity) _
  have hass := Eq729B_assembly_747 hu16 hu1.le hNpos hη hB hX (Eq729B_Bctl_nonneg sz n (t1 n)) hBt
    (Real.rpow_nonneg hNpos.le δ) hW
  rw [hsc] at hH
  rw [Eq729B_qdBoundExp_eq]
  calc lemT z * Eq729B_eqErr sz E' t1 t0 K n σ b a
      ≤ lemT z * (Nsz sz n ^ δ * ((Nsz sz n * (Real.sqrt (lemT z) * ouEtaQ sz 𝔡 n))⁻¹ ^ 3 +
          Eq729B_initTerm sz n (t1 n))) := mul_le_mul_of_nonneg_left hH hu0
    _ ≤ ((sz.W n : ℕ) : ℝ) ^ τ * (calB sz n (ouEtaQ sz 𝔡 n) 0 ^ 2 *
        ((sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d) ^ (-(1 / 5 : ℝ)) + calB sz n (ouEtaQ sz 𝔡 n) 0)) := hass

/-- The loss `12 N^{δ'} ≤ W^τ` for `δ' = 𝔠 τ / 2`, `W ≥ N^𝔠`, `N^{δ'} ≥ 12`. -/
theorem Eq729B_loss_absorb {N W 𝔠 τ : ℝ} (hN : 0 < N) (hτ : 0 < τ) (hNW : N ^ 𝔠 ≤ W)
    (h12 : 12 ≤ N ^ (𝔠 * τ / 2)) : 12 * N ^ (𝔠 * τ / 2) ≤ W ^ τ := by
  have hp : 0 ≤ N ^ (𝔠 * τ / 2) := Real.rpow_nonneg hN.le _
  have hNN : N ^ (𝔠 * τ / 2) * N ^ (𝔠 * τ / 2) = N ^ (𝔠 * τ) := by
    rw [← Real.rpow_add hN]; congr 1; ring
  calc 12 * N ^ (𝔠 * τ / 2) ≤ N ^ (𝔠 * τ / 2) * N ^ (𝔠 * τ / 2) := mul_le_mul_of_nonneg_right h12 hp
    _ = N ^ (𝔠 * τ) := hNN
    _ = (N ^ 𝔠) ^ τ := Real.rpow_mul hN.le _ _
    _ ≤ W ^ τ := Real.rpow_le_rpow (Real.rpow_nonneg hN.le _) hNW hτ.le

/-- **(7.47) from (7.29) and (7.26)** (RBM2D `Eq729B_eq747_of_eq729`, `Eq729B:1041`).  Let `z_n = E_n + i η_Q`,
`η_Q = W^{-𝔡/3} ilambda W^{d/2}/N`, `t₀ = lemT z_n`, `E' = lemE z_n` (Lemma 2.8, `z = t₀^{-1/2} z_{t₀}^{(E')}`),
`t₁ = (1 - ζ(t_n)) t₀` (`Eq729B_FlowData`, eventually).  If (7.29) holds at `t₀` on the GUE-phase grid in the loss form
`N^δ ((N η_{t₀})^{-3} + I₀(t₁))` at `(E', t₁, t₀)` (`Eq729B_Concl`), the one-time law (7.26) at the last grid step
(`map_gueH_last`) and `lemT_mul_kTwoGUE_pm/pp_eq_profPM/PPTilde` give the body of `UNOUEq747` at `(E, t)` (`Eq729B_OUBody`):
`W ≥ N^𝔠` turns the loss `N^{𝔠τ/2}` into `W^τ`, `t₀ (N η_{t₀})^{-3} ≤ 4 (N η_Q)^{-3}`, `𝓑(t₁) ≤ 2 𝓑_{η_Q,0}`
(`Eq729B_assembly_747`).  No `hell` is needed (`Eq729B_bctl_le_two_calB`). -/
theorem Eq729B_eq747_of_eq729 (sz : Sizes d) (hd : 3 ≤ d) {𝔠 𝔡 : ℝ} (hA : sz.Admissible 𝔠 𝔡) {κ : ℝ} (hκ : 0 < κ)
    {E t : ℕ → ℝ} (hE : ∀ n, |E n| ≤ 2 - κ) (ht : ∀ n, 0 ≤ t n) {E' t0 t1 : ℕ → ℝ}
    (hF : Eq729B_FlowData sz 𝔡 E t E' t0 t1) {K : ℕ → ℕ} (hK : ∀ n, K n ≠ 0) (H729 : Eq729B_Concl sz E' t1 t0 K)
    (τ : ℝ) (hτ : 0 < τ) : Eq729B_OUBody sz 𝔡 E t τ := by
  have hδ' : 0 < 𝔠 * τ / 2 := by have := mul_pos hA.1 hτ; linarith
  have hdom := queDomain sz hA (ε₀ := 𝔡 / 3) (κ := κ) (by linarith [hA.2.1]) (by linarith [hA.2.1])
  filter_upwards [H729 (𝔠 * τ / 2) hδ', hF.hE', hF.ht0, hF.ht1, hA.2.2.2.1, hdom,
    (Sizes.tendsto_size sz hA.2.2.1).eventually (eventually_le_rpow 12 hδ')] with n hH hE'n ht0n ht1n hNW hdn h12
  intro a b
  rw [show ((E n : ℂ) + ((ouEtaQ sz 𝔡 n : ℝ) : ℂ) * Complex.I) = Eq729B_zQ sz 𝔡 E n from rfl]
  have hloc : sz.locDomain κ (𝔠 * (𝔡 - 𝔡 / 3)) n (Eq729B_zQ sz 𝔡 E n) := hdn (E n) (hE n)
  have hzim : (Eq729B_zQ sz 𝔡 E n).im = ouEtaQ sz 𝔡 n := by simp [Eq729B_zQ]
  have hz : 0 < (Eq729B_zQ sz 𝔡 E n).im := locDomain_im_pos hloc
  have hη : 0 < ouEtaQ sz 𝔡 n := by rwa [hzim] at hz
  have hη1 : ouEtaQ sz 𝔡 n ≤ 1 := by rw [← hzim]; exact hloc.2.2
  have hW := Eq729B_loss_absorb (Nsz_pos sz n) hτ hNW h12
  have hζ0 := ZeroModeProfile_ouZeta_nonneg (ht n)
  have hζ1 := ZeroModeProfile_ouZeta_le_one (t n)
  set z : ℂ := Eq729B_zQ sz 𝔡 E n with hzdef
  have hzre : z.re = E n := by simp [hzdef, Eq729B_zQ]
  have hz1 : z.im ≤ 1 := by rw [hzim]; exact hη1
  have hzκ : |z.re| ≤ 2 - κ := by rw [hzre]; exact hE n
  obtain ⟨-, hu16, -, -⟩ := lemma28_quant hκ hz hz1 hzκ
  have hu1 := lemT_lt_one hz
  have hξ : ∀ σ : Bool, ‖(((1 - ouZeta (t n)) * lemT z : ℝ) : ℂ) *
      (mSigma (lemE z) true * mSigma (lemE z) σ)‖ < 1 := fun σ =>
    norm_mul_mSigma_lt_one (abs_lemE_lt_two hz).le (mul_nonneg (by linarith) (by linarith))
      (by nlinarith) true σ
  refine ⟨?_, ?_⟩
  · have e1 : (∫ ω, avg2 sz n (fun x y => ((‖Gres (ouMat (UNModel.band sz) n (t n) ω) z true x y‖ ^ 2 : ℝ) : ℂ)) a b
        ∂(ouP (UNModel.band sz) n)) =
        ∫ ω, avg2 sz n (fun x y => Gres (ouMat (UNModel.band sz) n (t n) ω) z true x y *
          Gres (ouMat (UNModel.band sz) n (t n) ω) z false y x) a b ∂(ouP (UNModel.band sz) n) :=
      integral_congr_ae (Filter.Eventually.of_forall fun ω => Eq729B_avg2_abs_sq sz n (ouMat_isHermitian _ _ _ ω) z a b)
    rw [e1]
    refine Eq729B_core747 sz hd 𝔡 hκ n false a b (hE n) (ht n) (hK n) hη hη1 hE'n ht0n ht1n (hH false b a) hW ?_
    rw [Eq729B_kTwoGUE_symm d (sz.L n) (sz.W n) (sz.three_le_L n) (sz.lam n) _ _ _ true false (hξ false) b a]
    exact lemT_mul_kTwoGUE_pm_eq_profPMTilde sz n hz hζ0 hζ1 a b
  · refine Eq729B_core747 sz hd 𝔡 hκ n true a b (hE n) (ht n) (hK n) hη hη1 hE'n ht0n ht1n (hH true b a) hW ?_
    rw [Eq729B_kTwoGUE_symm d (sz.L n) (sz.W n) (sz.three_le_L n) (sz.lam n) _ _ _ true true (hξ true) b a]
    exact lemT_mul_kTwoGUE_pp_eq_profPPTilde sz n hz hζ0 hζ1 a b

/-! ### The three asymptotic hypotheses at the QUE scale, and the target `Eq729B_eq747_of_inputs` -/

/-- **The three asymptotic hypotheses of `gueGrid_eq729` at `(E', t₁, t₀)`** (RBM2D `Eq729B_derived`, `Eq729B:1339`;
`Eq729B_good_pw`, `:1207`): `h730`, `hscale`, `hell`, eventually, from `Admissible 𝔠 𝔡`, `τ_U ≤ ouTauMax 𝔠 𝔡`,
`0 ≤ t_n ≤ N^{-1+τ_U}` at the QUE scale `η_Q = W^{-𝔡/3} ilambda W^{d/2}/N`.  The thresholds are `W`-only (`W → ∞`):
`4 ≤ W^{𝔡/2}`, `2/c ≤ W^{4𝔡/3}`, `2 ≤ W^{23𝔡/12}`, `c = √(κ(4-κ))/8` (`im_msc_ge`). -/
theorem Eq729B_derived (sz : Sizes d) {𝔠 𝔡 : ℝ} (hA : sz.Admissible 𝔠 𝔡) {κ τU : ℝ} (hκ : 0 < κ) (hτU : 0 < τU)
    (hτUm : τU ≤ ouTauMax 𝔠 𝔡) {E t : ℕ → ℝ} (hE : ∀ n, |E n| ≤ 2 - κ)
    (ht : ∀ n, 0 ≤ t n ∧ t n ≤ ouTStar sz τU n) {E' t0 t1 : ℕ → ℝ} (hF : Eq729B_FlowData sz 𝔡 E t E' t0 t1) :
    (∀ᶠ n in atTop, t0 n - t1 n ≤ Nsz sz n ^ (-τU) * etaT (E' n) (t0 n)) ∧
      (∀ᶠ n in atTop, (gueScale sz E' n (t0 n))⁻¹ ≤ Nsz sz n ^ (-τU)) ∧
      (∀ᶠ n in atTop, ((sz.L n : ℕ) : ℝ) ^ d * (1 - t1 n) ≤ sz.lam n ^ 2) := by
  have hτ12 : τU ≤ 𝔠 * 𝔡 / 12 := (hτUm.trans (min_le_left _ _)).trans (min_le_right _ _)
  have hκ2 : κ ≤ 2 := by have := abs_nonneg (E 0); have := hE 0; linarith
  have h𝔠 := hA.1
  have h𝔡 := hA.2.1
  have hc0 : 0 < Real.sqrt (κ * (4 - κ)) / 8 :=
    div_pos (Real.sqrt_pos.2 (mul_pos hκ (by linarith))) (by norm_num)
  have hWtop := RBM.Green.tendsto_W sz h𝔠 hA.2.2.1 hA.2.2.2.1
  have hdom := queDomain sz hA (ε₀ := 𝔡 / 3) (κ := κ) (by linarith) (by linarith)
  have hall : ∀ᶠ n in atTop,
      (t0 n - t1 n ≤ Nsz sz n ^ (-τU) * etaT (E' n) (t0 n)) ∧
      ((gueScale sz E' n (t0 n))⁻¹ ≤ Nsz sz n ^ (-τU)) ∧
      (((sz.L n : ℕ) : ℝ) ^ d * (1 - t1 n) ≤ sz.lam n ^ 2) := by
    filter_upwards [hF.hE', hF.ht0, hF.ht1, hA.2.2.2.1, hA.2.2.2.2, hdom,
      ((tendsto_rpow_atTop (by positivity : 0 < 𝔡 / 2)).comp hWtop).eventually_ge_atTop 4,
      ((tendsto_rpow_atTop (by positivity : 0 < 4 * 𝔡 / 3)).comp hWtop).eventually_ge_atTop
        (2 / (Real.sqrt (κ * (4 - κ)) / 8)),
      ((tendsto_rpow_atTop (by positivity : 0 < 23 * 𝔡 / 12)).comp hWtop).eventually_ge_atTop 2,
      hWtop.eventually_ge_atTop 1]
      with n hE'n ht0n ht1n hNW hWOn hdn h4 hc4 h2' hW1
    have h4' : 4 ≤ ((sz.W n : ℕ) : ℝ) ^ (𝔡 / 2) := h4
    have hc4' : 2 / (Real.sqrt (κ * (4 - κ)) / 8) ≤ ((sz.W n : ℕ) : ℝ) ^ (4 * 𝔡 / 3) := hc4
    have h2'' : 2 ≤ ((sz.W n : ℕ) : ℝ) ^ (23 * 𝔡 / 12) := h2'
    have hNpos := Nsz_pos sz n
    have hN1 : 1 ≤ Nsz sz n := by exact_mod_cast sz.one_le_size n
    have hloc : sz.locDomain κ (𝔠 * (𝔡 - 𝔡 / 3)) n (Eq729B_zQ sz 𝔡 E n) := hdn (E n) (hE n)
    have hzim : (Eq729B_zQ sz 𝔡 E n).im = ouEtaQ sz 𝔡 n := by simp [Eq729B_zQ]
    have hz : 0 < (Eq729B_zQ sz 𝔡 E n).im := locDomain_im_pos hloc
    have hη : 0 < ouEtaQ sz 𝔡 n := by rwa [hzim] at hz
    set z : ℂ := Eq729B_zQ sz 𝔡 E n with hzdef
    have hzre : z.re = E n := by simp [hzdef, Eq729B_zQ]
    have hz1 : z.im ≤ 1 := hloc.2.2
    have hzκ : |z.re| ≤ 2 - κ := by rw [hzre]; exact hE n
    obtain ⟨-, hu16, -, -⟩ := lemma28_quant hκ hz hz1 hzκ
    have hu1 := lemT_lt_one hz
    have hs4 : 1 / 4 ≤ Real.sqrt (lemT z) := by
      rw [show (1 / 4 : ℝ) = Real.sqrt (1 / 16) by
        rw [show (1 / 16 : ℝ) = (1 / 4) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt hu16
    have hζ0 := ZeroModeProfile_ouZeta_nonneg (ht n).1
    have hζ1 := ZeroModeProfile_ouZeta_le_one (t n)
    have hζt : ouZeta (t n) ≤ t n := ZeroModeProfile_ouZeta_le (t n)
    have hζN : ouZeta (t n) ≤ Nsz sz n ^ (-1 + τU) := hζt.trans (ht n).2
    have hdiff : t0 n - t1 n = ouZeta (t n) * lemT z := by rw [ht1n, ht0n]; ring
    have hζt0 : ouZeta (t n) * lemT z ≤ Nsz sz n ^ (-1 + τU) :=
      calc ouZeta (t n) * lemT z ≤ ouZeta (t n) * 1 := mul_le_mul_of_nonneg_left hu1.le hζ0
        _ = ouZeta (t n) := mul_one _
        _ ≤ _ := hζN
    have hclaim := Eq729B_claimA sz n h𝔡 hτ12 hNW h4' hWOn.1
    obtain ⟨hh1, hh2⟩ := Eq729B_h730_hscale_real hN1 hτU hη hs4 hclaim hζt0
    have heta : etaT (E' n) (t0 n) = Real.sqrt (lemT z) * ouEtaQ sz 𝔡 n := by
      rw [hE'n, ht0n, etaT_eq_zt_im, zt_im_lemma28 hz, hzim]
    refine ⟨?_, ?_, ?_⟩
    · rw [hdiff, heta]; exact hh1
    · have : gueScale sz E' n (t0 n) = Nsz sz n * (Real.sqrt (lemT z) * ouEtaQ sz 𝔡 n) := by
        unfold gueScale; rw [heta]
      rw [this]; exact hh2
    · -- `hell`
      have hform := (zRange κ hκ z hz hz1 hzκ).2.2.2.1
      have hmk := im_msc_ge hκ hz hz1 hzκ
      have hma := msc_im_pos hz
      have h1t : 1 - lemT z ≤ ouEtaQ sz 𝔡 n / (Real.sqrt (κ * (4 - κ)) / 8) :=
        calc 1 - lemT z = z.im / ((msc z).im + z.im) := hform
          _ ≤ z.im / (Real.sqrt (κ * (4 - κ)) / 8) := div_le_div_of_nonneg_left hz.le hc0 (by linarith)
          _ = _ := by rw [hzim]
      have hW0 : 0 < ((sz.W n : ℕ) : ℝ) := by linarith
      have hN2 : 2 * Nsz sz n ^ τU ≤ ((sz.W n : ℕ) : ℝ) ^ (2 * 𝔡) := by
        have e1 : Nsz sz n ^ τU ≤ ((sz.W n : ℕ) : ℝ) ^ (τU / 𝔠) :=
          Sizes.size_rpow_le_W_rpow sz h𝔠 n hNW hτU.le
        have e2 : ((sz.W n : ℕ) : ℝ) ^ (τU / 𝔠) ≤ ((sz.W n : ℕ) : ℝ) ^ (𝔡 / 12) :=
          Real.rpow_le_rpow_of_exponent_le hW1 (by rw [div_le_iff₀ h𝔠]; linarith)
        have e3 : ((sz.W n : ℕ) : ℝ) ^ (2 * 𝔡) =
            ((sz.W n : ℕ) : ℝ) ^ (𝔡 / 12) * ((sz.W n : ℕ) : ℝ) ^ (23 * 𝔡 / 12) := by
          rw [← Real.rpow_add hW0]; congr 1; ring
        rw [e3]
        have := Real.rpow_nonneg hW0.le (𝔡 / 12)
        calc 2 * Nsz sz n ^ τU ≤ 2 * ((sz.W n : ℕ) : ℝ) ^ (𝔡 / 12) := by linarith [e1.trans e2]
          _ ≤ ((sz.W n : ℕ) : ℝ) ^ (23 * 𝔡 / 12) * ((sz.W n : ℕ) : ℝ) ^ (𝔡 / 12) :=
              mul_le_mul_of_nonneg_right h2'' this
          _ = _ := mul_comm _ _
      have := Eq729B_hell_of_scales sz n hc0 hWOn.1 h1t hζ0 hζN hu1.le hc4' hN2
      rw [ht1n, ht0n]; exact this
  exact ⟨hall.mono fun n h => h.1, hall.mono fun n h => h.2.1, hall.mono fun n h => h.2.2⟩

/-- **(7.47) from the inputs of `gueGrid_eq729`** (RBM2D `Eq729B_eq747_of_inputs`, `Eq729B:1384`): at `(E', t₁, t₀)`,
`E' = lemE z_n`, `t₀ = lemT z_n`, `t₁ = (1 - ζ(t_n)) t₀`, `z_n = E_n + i η_Q`, `0 ≤ t_n ≤ t*_n = N^{-1+τ_U}`,
`τ_U ≤ ouTauMax 𝔠 𝔡`, `W ≥ N^𝔠`: `h730`, `hscale`, `hell` (`Eq729B_derived`), `Tendsto size`, `hlam` (from `(eq:WO)`) and
`hKb` (`Sizes.stKbound_holds`) of `gueGrid_eq729` are derived, and `gueGrid_eq729` followed by `Eq729B_eq747_of_eq729` is the
body of `UNOUEq747 sz 𝔡 τ_U` at `(E, t)` (`Eq729B_ueq747_iff`).  The remaining inputs are those of `gueGrid_eq729`: `K̃`
(`hKinit`, `hK`, `hK2`), `hB := sz.STExp2 E' t₁` (from `UNMLOut` by `Eq729B_bridge`) and `GUEPathBounds` ((7.28) on the grid);
`hgood` (`|E'| ≤ 2 - κ`, `0 ≤ t₁ ≤ t₀ < 1` at every `n`; `Eq729B_goodFlow`) replaces RBM2D's `Eq729B_pw`. -/
theorem Eq729B_eq747_of_inputs (sz : Sizes d) (hd : 3 ≤ d) {𝔠 𝔡 : ℝ} (hA : sz.Admissible 𝔠 𝔡) {κ τU : ℝ}
    (hκ : 0 < κ) (hτU : 0 < τU) (hτUm : τU ≤ ouTauMax 𝔠 𝔡) (n0 : ℕ) (hn0 : 3 ≤ n0) {E t : ℕ → ℝ}
    (hE : ∀ n, |E n| ≤ 2 - κ) (ht : ∀ n, 0 ≤ t n ∧ t n ≤ ouTStar sz τU n) {E' t0 t1 : ℕ → ℝ}
    (hF : Eq729B_FlowData sz 𝔡 E t E' t0 t1) (hgood : ∀ n, |E' n| ≤ 2 - κ ∧ 0 ≤ t1 n ∧ t1 n ≤ t0 n ∧ t0 n < 1)
    (Kt : ∀ n, ℝ → LoopIdx (Zd d (sz.L n)) → ℂ)
    (hKinit : ∀ n {k : ℕ} (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)),
      Kt n (t1 n) (loopOf σ a) = sz.STKloop n (E' n) (t1 n) σ a)
    (hK : ∀ n, ∀ s ∈ Set.Icc (t1 n) (t0 n), ∀ I : LoopIdx (Zd d (sz.L n)), I.WF → 1 ≤ I.length →
      I.length ≤ 4 * n0 →
      HasDerivWithinAt (fun u => Kt n u I) (primRhsGUE d (sz.L n) (sz.W n) (Kt n s) I) (Set.Icc (t1 n) (t0 n)) s)
    (hK2 : ∀ n, ∀ s ∈ Set.Icc (t1 n) (t0 n), ∀ (σ₁ σ₂ : Bool) (a b : Zd d (sz.L n)),
      Kt n s ⟨[σ₁, σ₂], [a, b]⟩ =
        kTwoGUE d (sz.L n) (sz.W n) (sz.lam n) (mSigma (E' n)) (t1 n) s σ₁ σ₂ a b)
    (hB : sz.STExp2 E' t1) (hP : GUEPathBounds sz E' t1 t0 (gueGridK sz n0) n0 Kt) (τ : ℝ) (hτ : 0 < τ) :
    Eq729B_OUBody sz 𝔡 E t τ := by
  obtain ⟨h730, hscale, hell⟩ := Eq729B_derived sz hA hκ hτU hτUm hE ht hF
  have hlam : ∀ᶠ n in atTop, 0 < sz.lam n ∧ sz.lam n ≤ 𝔡⁻¹ := by
    filter_upwards [hA.2.2.2.2] with n hn
    exact ⟨lt_of_lt_of_le (Real.rpow_pos_of_pos (by exact_mod_cast sz.W_pos n) _) hn.1, hn.2⟩
  have hKb := Sizes.stKbound_holds sz hd hκ (inv_pos.2 hA.2.1) hA.2.2.1
    (Eventually.of_forall fun n => (hgood n).1) hlam
  exact Eq729B_eq747_of_eq729 sz hd hA hκ hE (fun n => (ht n).1) hF (gueGridK_ne_zero sz n0)
    (gueGrid_eq729 sz hd hκ hτU n0 hn0 (Sizes.tendsto_size sz hA.2.2.1) hlam (fun n => (hgood n).1)
      (fun n => (hgood n).2.1) (fun n => (hgood n).2.2.1) (fun n => (hgood n).2.2.2) h730 hscale hell hKb Kt hKinit
      hK hK2 hB hP) τ hτ

/-! ### Good data for every `n` and the bridge `UNMLOut ⟹ STExp2 E' t₁` (RBM3D-specific; both proved, no new pin) -/

/-- `STExp2` depends on `(E, t)` only eventually (it is `∀ τ D, ∀ᶠ n`). -/
theorem Eq729B_STExp2_congr (sz : Sizes d) {E E' t t' : ℕ → ℝ} (hE : ∀ᶠ n in atTop, E n = E' n)
    (ht : ∀ᶠ n in atTop, t n = t' n) (h : sz.STExp2 E t) : sz.STExp2 E' t' := by
  intro τ hτ D hD
  filter_upwards [h τ hτ D hD, hE, ht] with n hn h1 h2
  simpa only [badSetAt, ← h1, ← h2] using hn

/-- The formulas of (7.47) define flow data: `E' = lemE z_n`, `t₀ = lemT z_n`, `t₁ = (1 - ζ(t_n)) t₀` satisfy the three fields of
`Eq729B_FlowData` (for every `n`; the vocabulary structure is not a pin). -/
theorem Eq729B_flowData_formulas (sz : Sizes d) (𝔡 : ℝ) (E t : ℕ → ℝ) :
    Eq729B_FlowData sz 𝔡 E t (fun n => lemE (Eq729B_zQ sz 𝔡 E n)) (fun n => lemT (Eq729B_zQ sz 𝔡 E n))
      (fun n => (1 - ouZeta (t n)) * lemT (Eq729B_zQ sz 𝔡 E n)) :=
  ⟨Filter.Eventually.of_forall fun _ => rfl, Filter.Eventually.of_forall fun _ => rfl,
    Filter.Eventually.of_forall fun _ => rfl⟩

/-- Two flow data of the same `(E, t)` agree eventually. -/
theorem Eq729B_FlowData.ev_eq {sz : Sizes d} {𝔡 : ℝ} {E t E1 t01 t11 E2 t02 t12 : ℕ → ℝ}
    (h1 : Eq729B_FlowData sz 𝔡 E t E1 t01 t11) (h2 : Eq729B_FlowData sz 𝔡 E t E2 t02 t12) :
    (∀ᶠ n in atTop, E1 n = E2 n) ∧ ∀ᶠ n in atTop, t11 n = t12 n :=
  ⟨by filter_upwards [h1.hE', h2.hE'] with n a b; rw [a, b],
   by filter_upwards [h1.ht0, h1.ht1, h2.ht0, h2.ht1] with n a b c e; rw [b, a, e, c]⟩

/-- `z_n` is kept where `z_n ∈ 𝐃_{κ,ε}` (`queDomain`, `ε₀ = 𝔡/3`, `ε = min(𝔠(𝔡 - 𝔡/3), 1)`; eventually), else a fixed point of
`𝐃_{κ,ε}` (`locDomain_nonempty`, `Endpoints.lean:486`): `STFlow` at every `n`, the formulas of `Eq729B_FlowData` eventually,
and `|E'| ≤ 2 - κ`, `0 ≤ t₁ ≤ t₀ < 1` for every `n` (`lemma28_quant`, `lemT_lt_one`). -/
theorem Eq729B_goodFlow_aux (sz : Sizes d) {𝔠 𝔡 : ℝ} (hA : sz.Admissible 𝔠 𝔡) {κ : ℝ} (hκ : 0 < κ) {E t : ℕ → ℝ}
    (hE : ∀ n, |E n| ≤ 2 - κ) (ht : ∀ n, 0 ≤ t n) : ∃ (ε : ℝ) (z' : ℕ → ℂ) (t1 : ℕ → ℝ), 0 < ε ∧
      STFlow sz κ ε 𝔠 𝔡 z' ∧ Eq729B_FlowData sz 𝔡 E t (STflowE z') (fun n => lemT (z' n)) t1 ∧
      ∀ n, |STflowE z' n| ≤ 2 - κ ∧ 0 ≤ t1 n ∧ t1 n ≤ lemT (z' n) ∧ lemT (z' n) < 1 := by
  classical
  have hε : 0 < min (𝔠 * (𝔡 - 𝔡 / 3)) 1 := lt_min (mul_pos hA.1 (by linarith [hA.2.1])) one_pos
  have hdom := queDomain sz hA (ε₀ := 𝔡 / 3) (κ := κ) (by linarith [hA.2.1]) (by linarith [hA.2.1])
  set ε := min (𝔠 * (𝔡 - 𝔡 / 3)) 1 with hεdef
  have hgood : ∀ᶠ n in atTop, sz.locDomain κ ε n (Eq729B_zQ sz 𝔡 E n) := by
    filter_upwards [hdom] with n hn
    obtain ⟨h1, h2, h3⟩ := hn (E n) (hE n)
    exact ⟨h1, le_trans (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast sz.one_le_size n)
      (by linarith [min_le_left (𝔠 * (𝔡 - 𝔡 / 3)) 1])) h2, h3⟩
  have hfb := fun n => locDomain_nonempty sz (show κ ≤ 2 by have := hE 0; linarith [abs_nonneg (E 0)])
    (min_le_right (𝔠 * (𝔡 - 𝔡 / 3)) 1) n
  let z' : ℕ → ℂ := fun n => if sz.locDomain κ ε n (Eq729B_zQ sz 𝔡 E n) then Eq729B_zQ sz 𝔡 E n else (hfb n).choose
  have hz' : ∀ n, sz.locDomain κ ε n (z' n) := fun n => by
    by_cases h : sz.locDomain κ ε n (Eq729B_zQ sz 𝔡 E n)
    · simp [z', h]
    · simpa [z', h] using (hfb n).choose_spec
  have hev : ∀ᶠ n in atTop, z' n = Eq729B_zQ sz 𝔡 E n := hgood.mono fun n h => by simp [z', h]
  refine ⟨ε, z', fun n => (1 - ouZeta (t n)) * lemT (z' n), hε, ⟨hA, hz'⟩,
    ⟨hev.mono fun n h => by simp [STflowE, h], hev.mono fun n h => by simp [h], Eventually.of_forall fun n => rfl⟩,
    fun n => ?_⟩
  have hu := lemT_pos (locDomain_im_pos (hz' n))
  have hζ0 := ZeroModeProfile_ouZeta_nonneg (ht n)
  have hζ1 := ZeroModeProfile_ouZeta_le_one (t n)
  exact ⟨(lemma28_quant hκ (locDomain_im_pos (hz' n)) (hz' n).2.2 (hz' n).1).1, mul_nonneg (by linarith) hu.le,
    by nlinarith, lemT_lt_one (locDomain_im_pos (hz' n))⟩

/-- **Good flow data**: for `(E, t)` with `|E| ≤ 2 - κ`, `t ≥ 0` there are `E', t₀, t₁` with the formulas of
`Eq729B_FlowData` eventually and `|E'| ≤ 2 - κ`, `0 ≤ t₁ ≤ t₀ < 1` at **every** `n` (the formulas are junk at the finitely many
`n` with `ilambda_n ≤ 0`, where `Im z_n ≤ 0`; `Sizes.lam` has no positivity field and `(eq:WO)` is eventual). -/
theorem Eq729B_goodFlow (sz : Sizes d) {𝔠 𝔡 : ℝ} (hA : sz.Admissible 𝔠 𝔡) {κ : ℝ} (hκ : 0 < κ) {E t : ℕ → ℝ}
    (hE : ∀ n, |E n| ≤ 2 - κ) (ht : ∀ n, 0 ≤ t n) :
    ∃ E' t0 t1 : ℕ → ℝ, Eq729B_FlowData sz 𝔡 E t E' t0 t1 ∧ ∀ n, |E' n| ≤ 2 - κ ∧ 0 ≤ t1 n ∧ t1 n ≤ t0 n ∧ t0 n < 1 := by
  obtain ⟨ε, z', t1, -, -, hF, hg⟩ := Eq729B_goodFlow_aux sz hA hκ hE ht
  exact ⟨_, _, t1, hF, fun n => ⟨(hg n).1, (hg n).2.1, (hg n).2.2.1, (hg n).2.2.2⟩⟩

/-- **The bridge UN-51 needs**: `STExp2 sz E' t₁` at the flow data of (7.47) from `UNMLOut d` (`Universality/Pins.lean:432`)
through `STFlow` (`Induction/Defs.lean:286`) at `z_n = E_n + i η_Q` (modified at finitely many `n`) and `t₁ ≤ lemT z_n`.
Of the five conclusions of `UNMLOut` only `STExp2` is consumed. -/
theorem Eq729B_bridge (hML : UNMLOut d) (hd : 3 ≤ d) (sz : Sizes d) {𝔠 𝔡 : ℝ} (hA : sz.Admissible 𝔠 𝔡) {κ : ℝ}
    (hκ : 0 < κ) {E t : ℕ → ℝ} (hE : ∀ n, |E n| ≤ 2 - κ) (ht : ∀ n, 0 ≤ t n) {E' t0 t1 : ℕ → ℝ}
    (hF : Eq729B_FlowData sz 𝔡 E t E' t0 t1) : sz.STExp2 E' t1 := by
  obtain ⟨ε, z', t1', hε, hflow, hF', hg⟩ := Eq729B_goodFlow_aux sz hA hκ hE ht
  obtain ⟨he, hte⟩ := hF'.ev_eq hF
  exact Eq729B_STExp2_congr sz he hte
    (hML hd κ ε 𝔡 𝔠 hκ hε hA.2.1 sz z' hflow t1' (fun n => (hg n).2.1) (fun n => (hg n).2.2.1)).2.2.2.1

/-! ## Compiled nonempty instances (CLAUDE.md §4 step 2)

`Eq729BInst`.  `d = 3` at the merged size sequence `SizesInst.sz0` (`L = 4(n+1)`, `W = (2(n+1))^5`, `ilambda = (2(n+1))^{-6}`,
`N = 8 (2(n+1))^{18} → ∞`; `n = 0`: `L = 4`, `W = 32`, `N = 2097152`), `𝔠 = 1/6`, `𝔡 = 1/10`, `κ = 1/10`, `E = 0`.
* `inst_gueGrid_eq729`: the window `1 - t₀ = y`, `t₀ - t₁ = y/N`, `y = ilambda²/(2 L³)`, `τ_U = 1/30`, `n₀ = 3`; every deterministic
  hypothesis is discharged (`hKb` by `stKbound_holds`, `Kt` by `gueK_exists` at every `n`); `hB : STExp2` and `hP : GUEPathBounds`
  (pins of ST-6 and UN-49/50/51) are the hypotheses of the statement.
* The OU times are `t_n = t*_n = N^{-1+τ_U}` (positive), `τ_U = ouTauMax = 1/720`.  `inst_derived`, `inst_bridge`,
  `inst_eq747_of_eq729` are at the explicit flow data `Ec`, `T0c`, `T1c` (`Eq729B_flowData_formulas`, `t₁ < t₀` as `ζ(t_n) > 0`);
  `inst_goodFlow`, `inst_eq747_of_inputs` at the data of `Eq729B_goodFlow` (`|E'| ≤ 2 - κ`, `0 ≤ t₁ ≤ t₀ < 1` for every `n`).
  `UNMLOut 3`, `GUEPathBounds` and (for `Eq729B_eq747_of_eq729`) the conclusion `Eq729B_Concl` of `gueGrid_eq729` are the
  hypotheses of the statements (pins of ST-6 and UN-49/50/51).
* `inst_claimA`, `inst_hell_of_scales` at `n = 7` (`L = 32`, `W = 2^{20}`, `ilambda = 2^{-24}`, `N = 2^{75}`), `𝔡 = 3/10`; the real-variable
  lemmas at explicit numbers. -/

namespace Eq729BInst

open RBM.Gauss.SizesInst

/-! ### The window of the instance of `gueGrid_eq729`: `E = 0`, `1 - t₀ = y`, `t₀ - t₁ = y/N`, `y = ilambda²/(2 L^d)` -/

private def Ei : ℕ → ℝ := fun _ => 0
private def xx (n : ℕ) : ℝ := 2 * ((n : ℝ) + 1)
private def Nn (n : ℕ) : ℝ := ((sz0.size n : ℕ) : ℝ)
private def yy (n : ℕ) : ℝ := sz0.lam n ^ 2 / (2 * ((sz0.L n : ℕ) : ℝ) ^ 3)
private def tw0 (n : ℕ) : ℝ := 1 - yy n
private def tw1 (n : ℕ) : ℝ := 1 - yy n - yy n / Nn n

private theorem xx_ge (n : ℕ) : 2 ≤ xx n := by unfold xx; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
private theorem lam_eq (n : ℕ) : sz0.lam n = (xx n ^ 6)⁻¹ := rfl
private theorem W_eq (n : ℕ) : ((sz0.W n : ℕ) : ℝ) = xx n ^ 5 := by simp [sz0, xx]
private theorem L_eq (n : ℕ) : ((sz0.L n : ℕ) : ℝ) = 2 * xx n := by simp [sz0, xx]; ring
private theorem Nn_eq (n : ℕ) : Nn n = 8 * xx n ^ 18 := by
  unfold Nn Sizes.size; push_cast; rw [W_eq, L_eq]; ring
private theorem yy_eq (n : ℕ) : yy n = (16 * xx n ^ 15)⁻¹ := by
  have : (0 : ℝ) < xx n := by linarith [xx_ge n]
  unfold yy; rw [lam_eq, L_eq]; field_simp; ring
private theorem yy_pos (n : ℕ) : 0 < yy n := by
  have : (0 : ℝ) < xx n := by linarith [xx_ge n]
  rw [yy_eq]; positivity
private theorem yy_le_half (n : ℕ) : yy n ≤ 1 / 2 := by
  have h1 : (2 : ℝ) ≤ xx n := xx_ge n
  have h2 : (1 : ℝ) ≤ xx n ^ 15 := one_le_pow₀ (by linarith)
  rw [yy_eq]
  calc (16 * xx n ^ 15)⁻¹ ≤ (16 * 1)⁻¹ := inv_anti₀ (by norm_num) (by nlinarith)
    _ ≤ 1 / 2 := by norm_num
private theorem Nn_ge_one (n : ℕ) : 1 ≤ Nn n := by
  have h : (1 : ℝ) ≤ xx n ^ 18 := one_le_pow₀ (by linarith [xx_ge n])
  rw [Nn_eq]; linarith
private theorem Nn_mul_yy (n : ℕ) : Nn n * yy n = xx n ^ 3 / 2 := by
  have : (0 : ℝ) < xx n := by linarith [xx_ge n]
  rw [Nn_eq, yy_eq]; field_simp; ring

private theorem tw1_nonneg (n : ℕ) : 0 ≤ tw1 n := by
  have h1 := yy_pos n
  have h2 := yy_le_half n
  have h3 : yy n / Nn n ≤ yy n := div_le_self h1.le (Nn_ge_one n)
  unfold tw1; linarith
private theorem tw1_le_tw0 (n : ℕ) : tw1 n ≤ tw0 n := by
  have : 0 ≤ yy n / Nn n := div_nonneg (yy_pos n).le (by linarith [Nn_ge_one n])
  unfold tw1 tw0; linarith
private theorem tw0_lt_one (n : ℕ) : tw0 n < 1 := by unfold tw0; linarith [yy_pos n]
private theorem mE_zero_im : (mE 0).im = 1 := by
  rw [mE_im, show (4 : ℝ) - 0 ^ 2 = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]; norm_num

private theorem etaT_tw0 (n : ℕ) : etaT (Ei n) (tw0 n) = yy n := by
  unfold etaT tw0 Ei; rw [mE_zero_im]; ring

private theorem h730_at (n : ℕ) :
    tw0 n - tw1 n ≤ Nsz sz0 n ^ (-(1 / 30 : ℝ)) * etaT (Ei n) (tw0 n) := by
  have hN := Nn_ge_one n
  have hN0 : 0 < Nn n := by linarith
  have h1 : (Nn n)⁻¹ ≤ Nn n ^ (-(1 / 30 : ℝ)) := by
    rw [← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le hN (by norm_num)
  rw [etaT_tw0]
  change _ ≤ Nn n ^ (-(1 / 30 : ℝ)) * _
  have e : tw0 n - tw1 n = yy n * (Nn n)⁻¹ := by unfold tw0 tw1; ring
  rw [e, mul_comm]
  exact mul_le_mul_of_nonneg_right h1 (yy_pos n).le

private theorem hscale_at (n : ℕ) :
    (gueScale sz0 Ei n (tw0 n))⁻¹ ≤ Nsz sz0 n ^ (-(1 / 30 : ℝ)) := by
  have hx : (2 : ℝ) ≤ xx n := xx_ge n
  have hx0 : (0 : ℝ) < xx n := by linarith
  have hN0 : 0 < Nn n := by linarith [Nn_ge_one n]
  have hN30 : Nn n ≤ xx n ^ 30 := by
    rw [Nn_eq]
    have h8 : (8 : ℝ) ≤ xx n ^ 12 := by
      calc (8 : ℝ) ≤ 2 ^ 12 := by norm_num
        _ ≤ xx n ^ 12 := pow_le_pow_left₀ (by norm_num) hx 12
    calc 8 * xx n ^ 18 ≤ xx n ^ 12 * xx n ^ 18 := by gcongr
      _ = xx n ^ 30 := by ring
  have h1 : Nn n ^ (1 / 30 : ℝ) ≤ xx n := by
    calc Nn n ^ (1 / 30 : ℝ) ≤ (xx n ^ 30) ^ (1 / 30 : ℝ) := Real.rpow_le_rpow hN0.le hN30 (by norm_num)
      _ = xx n := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]; norm_num
  have h2 : xx n ≤ xx n ^ 3 / 2 := by nlinarith [mul_nonneg hx0.le hx0.le]
  have hg : gueScale sz0 Ei n (tw0 n) = xx n ^ 3 / 2 := by
    unfold gueScale; rw [etaT_tw0]; exact Nn_mul_yy n
  rw [hg]
  change (xx n ^ 3 / 2)⁻¹ ≤ Nn n ^ (-(1 / 30 : ℝ))
  rw [Real.rpow_neg hN0.le]
  exact inv_anti₀ (Real.rpow_pos_of_pos hN0 _) (h1.trans h2)

private theorem hell_at (n : ℕ) : ((sz0.L n : ℕ) : ℝ) ^ 3 * (1 - tw1 n) ≤ sz0.lam n ^ 2 := by
  have hL : (0 : ℝ) < ((sz0.L n : ℕ) : ℝ) ^ 3 := by
    have : (3 : ℝ) ≤ ((sz0.L n : ℕ) : ℝ) := by exact_mod_cast sz0.three_le_L n
    positivity
  have h1 : yy n / Nn n ≤ yy n := div_le_self (yy_pos n).le (Nn_ge_one n)
  have e : 1 - tw1 n = yy n + yy n / Nn n := by unfold tw1; ring
  have hL' : ((sz0.L n : ℕ) : ℝ) ≠ 0 := by
    have : (3 : ℝ) ≤ ((sz0.L n : ℕ) : ℝ) := by exact_mod_cast sz0.three_le_L n
    linarith
  have h2 : ((sz0.L n : ℕ) : ℝ) ^ 3 * (2 * yy n) = sz0.lam n ^ 2 := by
    unfold yy; field_simp
  rw [e, ← h2]
  exact mul_le_mul_of_nonneg_left (by linarith) hL.le


private theorem hlam1 : ∀ᶠ n in atTop, 0 < sz0.lam n ∧ sz0.lam n ≤ 1 :=
  Eventually.of_forall fun n => by
    have := xx_ge n
    refine ⟨by rw [lam_eq]; positivity, ?_⟩
    rw [lam_eq]; exact inv_le_one_of_one_le₀ (one_le_pow₀ (by linarith))

private theorem hE0 : ∀ n, |Ei n| ≤ 2 - 1 / 10 := fun n => by norm_num [Ei]

/-- `STKbound` at `sz0`, `E = 0` (merged `Sizes.stKbound_holds`, `κ = 1/10`, `gmax = 1`). -/
private theorem hKb0 : sz0.STKbound Ei :=
  Sizes.stKbound_holds sz0 (le_refl 3) (κ := 1 / 10) (gmax := 1) (by norm_num) one_pos sz0_tendsto
    (Eventually.of_forall hE0) hlam1

/-- The primitive family of the instance: the band K-loops (`gueK_exists`, `g = ilambda_n`) on the window `[t₁, t₀]`. -/
private theorem exists_Kt :
    ∃ Kt : (n : ℕ) → ℝ → LoopIdx (Zd 3 (sz0.L n)) → ℂ,
      (∀ n {k : ℕ} (σ : Fin k → Bool) (a : Fin k → Zd 3 (sz0.L n)),
        Kt n (tw1 n) (loopOf σ a) = sz0.STKloop n (Ei n) (tw1 n) σ a) ∧
      (∀ n, ∀ t ∈ Set.Icc (tw1 n) (tw0 n), ∀ I : LoopIdx (Zd 3 (sz0.L n)), I.WF → 1 ≤ I.length →
        I.length ≤ 4 * 3 → HasDerivWithinAt (fun s => Kt n s I) (primRhsGUE 3 (sz0.L n) (sz0.W n) (Kt n t) I)
          (Set.Icc (tw1 n) (tw0 n)) t) ∧
      (∀ n, ∀ t ∈ Set.Icc (tw1 n) (tw0 n), ∀ (σ₁ σ₂ : Bool) (a b : Zd 3 (sz0.L n)),
        Kt n t ⟨[σ₁, σ₂], [a, b]⟩ =
          kTwoGUE 3 (sz0.L n) (sz0.W n) (sz0.lam n) (mSigma (Ei n)) (tw1 n) t σ₁ σ₂ a b) := by
  choose Kt h1 h2 h3 using fun n => gueK_exists 3 (sz0.L n) (sz0.W n) (sz0.three_le_L n) (sz0.lam n)
    (E := Ei n) (by norm_num [Ei]) (tw1_nonneg n) (tw1_le_tw0 n) (tw0_lt_one n) (4 * 3)
  exact ⟨Kt, fun n k σ a => h1 n _, fun n t ht I hI h hl => h2 n t ht I hI h hl, h3⟩

/-- **`gueGrid_eq729`** at `sz0` (`d = 3`, `κ = 1/10`, `E = 0`, `τ_U = 1/30`, `n₀ = 3`, `Λ = 1`, the window `1 - t₀ = y`,
`t₀ - t₁ = y/N`, `y = ilambda²/(2 L³)`, a window of positive length for every `n`): every deterministic hypothesis (`hsize`,
`hlam`, `hE`, `ht1`, `ht10`, `ht0`, `h730`, `hscale`, `hell`, `hKb`, `hKinit`, `hK`, `hK2`) is discharged; `hB : STExp2` and
`hP : GUEPathBounds` (the pins of ST-6 and UN-49/50/51) stay hypotheses of the statement. -/
theorem inst_gueGrid_eq729 :
    ∃ Kt : (n : ℕ) → ℝ → LoopIdx (Zd 3 (sz0.L n)) → ℂ,
      sz0.STExp2 Ei tw1 → GUEPathBounds sz0 Ei tw1 tw0 (gueGridK sz0 3) 3 Kt →
        Eq729B_Concl sz0 Ei tw1 tw0 (gueGridK sz0 3) := by
  obtain ⟨Kt, h1, h2, h3⟩ := exists_Kt
  exact ⟨Kt, fun hB hP => gueGrid_eq729 sz0 (le_refl 3) (κ := 1 / 10) (τU := 1 / 30) (Λ := 1) (by norm_num)
    (by norm_num) 3 (le_refl 3) (Sizes.tendsto_size sz0 sz0_tendsto) hlam1 hE0 tw1_nonneg tw1_le_tw0 tw0_lt_one
    (Eventually.of_forall h730_at) (Eventually.of_forall hscale_at) (Eventually.of_forall hell_at) hKb0 Kt h1 h2 h3
    hB hP⟩

private theorem two_pow_rpow (m : ℕ) (r : ℝ) : ((2 : ℝ) ^ m) ^ r = (2 : ℝ) ^ ((m : ℝ) * r) := by
  rw [← Real.rpow_natCast 2 m, ← Real.rpow_mul (by norm_num)]

private theorem W7 : ((sz0.W 7 : ℕ) : ℝ) = 2 ^ 20 := by norm_num [sz0]
private theorem lam7 : sz0.lam 7 = ((2 : ℝ) ^ 24)⁻¹ := by norm_num [sz0]
private theorem N7 : Nsz sz0 7 = 2 ^ 75 := by
  unfold Nsz Sizes.size; norm_num [sz0]

private theorem h4_7 : (4 : ℝ) ≤ ((sz0.W 7 : ℕ) : ℝ) ^ ((3 / 10 : ℝ) / 2) := by
  rw [W7, two_pow_rpow]
  have : ((20 : ℕ) : ℝ) * ((3 / 10 : ℝ) / 2) = (3 : ℕ) := by norm_num
  rw [this, Real.rpow_natCast]; norm_num

private theorem hlo_7 : ((sz0.W 7 : ℕ) : ℝ) ^ (-((3 : ℕ) : ℝ) / 2 + 3 / 10) ≤ sz0.lam 7 := by
  rw [W7, two_pow_rpow, lam7]
  have : ((20 : ℕ) : ℝ) * (-((3 : ℕ) : ℝ) / 2 + 3 / 10) = -((24 : ℕ) : ℝ) := by norm_num
  rw [this, Real.rpow_neg (by norm_num), Real.rpow_natCast]


private theorem etaQ7_pos : 0 < ouEtaQ sz0 (3 / 10) 7 := by
  unfold ouEtaQ; rw [lam7, W7]
  have : (0 : ℝ) < Nsz sz0 7 := Nsz_pos sz0 7
  positivity

private theorem hc4_7 : (2 : ℝ) / 1 ≤ ((sz0.W 7 : ℕ) : ℝ) ^ (4 * (3 / 10 : ℝ) / 3) := by
  rw [W7, two_pow_rpow]
  have : ((20 : ℕ) : ℝ) * (4 * (3 / 10 : ℝ) / 3) = (8 : ℕ) := by norm_num
  rw [this, Real.rpow_natCast]; norm_num

private theorem hN_7 : 2 * Nsz sz0 7 ^ (1 / 240 : ℝ) ≤ ((sz0.W 7 : ℕ) : ℝ) ^ (2 * (3 / 10 : ℝ)) := by
  have h1 : Nsz sz0 7 ^ (1 / 240 : ℝ) ≤ 2 := by
    rw [N7, two_pow_rpow]
    calc (2 : ℝ) ^ (((75 : ℕ) : ℝ) * (1 / 240 : ℝ)) ≤ 2 ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = 2 := Real.rpow_one 2
  have h2 : ((sz0.W 7 : ℕ) : ℝ) ^ (2 * (3 / 10 : ℝ)) = 4096 := by
    rw [W7, two_pow_rpow]
    have : ((20 : ℕ) : ℝ) * (2 * (3 / 10 : ℝ)) = (12 : ℕ) := by norm_num
    rw [this, Real.rpow_natCast]; norm_num
  rw [h2]; linarith

/-- **`Eq729B_claimA`** at `sz0`, `n = 7` (`L = 32`, `W = 2^{20}`, `ilambda = 2^{-24}`, `N = 2^{75}`), `𝔠 = 1/6`, `𝔡 = 3/10`,
`τ_U = 1/240 = 𝔠𝔡/12`: all five hypotheses discharged. -/
theorem inst_claimA : 4 * Nsz sz0 7 ^ (2 * (1 / 240 : ℝ)) ≤ Nsz sz0 7 * ouEtaQ sz0 (3 / 10) 7 :=
  Eq729B_claimA sz0 7 (𝔠 := 1 / 6) (𝔡 := 3 / 10) (τU := 1 / 240) (by norm_num) (by norm_num)
    (sz0_bandwidth_at 7) h4_7 hlo_7

/-- **`Eq729B_hell_of_scales`** at `sz0`, `n = 7`, `𝔡 = 3/10`, `c = 1`, `τ_U = 1/240`, `ζ = N^{-1+τ_U} > 0` (the OU
correction at `t_n = t*_n`), `t₀ = 1 - η_Q`: all hypotheses discharged. -/
theorem inst_hell_of_scales :
    ((sz0.L 7 : ℕ) : ℝ) ^ 3 * (1 - (1 - Nsz sz0 7 ^ (-1 + 1 / 240 : ℝ)) * (1 - ouEtaQ sz0 (3 / 10) 7)) ≤
      sz0.lam 7 ^ 2 :=
  Eq729B_hell_of_scales sz0 7 (𝔡 := 3 / 10) (c := 1) (τU := 1 / 240) (ζ := Nsz sz0 7 ^ (-1 + 1 / 240 : ℝ))
    (t0 := 1 - ouEtaQ sz0 (3 / 10) 7) one_pos hlo_7 (by norm_num) (Real.rpow_nonneg (Nsz_pos sz0 7).le _) le_rfl
    (by linarith [etaQ7_pos]) hc4_7 hN_7

/-- **`Eq729B_assembly_747`** at explicit real data (`t₀ = 1/2`, `N = 100`, `η_Q = 1/10`, `𝓑 = 1/5`, `X = 1/10`, `𝓑(t₁) = 1/5`,
`M = 1`, `W^τ = 12`). -/
theorem inst_assembly_747 :
    (1 / 2 : ℝ) * (1 * ((100 * (Real.sqrt (1 / 2) * (1 / 10)))⁻¹ ^ 3 + (1 / 5) ^ 2 * (1 / 10 + 1 / 5))) ≤
      12 * ((1 / 5) ^ 2 * (1 / 10 + 1 / 5)) :=
  Eq729B_assembly_747 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)


/-! ### The flow data of (7.47) at `sz0`: `E = 0`, `t_n = t*_n = N^{-1+τ_U}`, `τ_U = ouTauMax = 1/720` -/

private theorem hτUi : 0 < ouTauMax (1 / 6) (1 / 10) := by unfold ouTauMax; norm_num

/-- The OU times `t_n = t*_n = N^{-1+τ_U}` (positive, so that `t₁ < t₀`). -/
private def tU (n : ℕ) : ℝ := ouTStar sz0 (ouTauMax (1 / 6) (1 / 10)) n

private theorem tU_ok : ∀ n, 0 ≤ tU n ∧ tU n ≤ ouTStar sz0 (ouTauMax (1 / 6) (1 / 10)) n :=
  fun _ => ⟨Real.rpow_nonneg (Nat.cast_nonneg _) _, le_rfl⟩

/-- **`Eq729B_goodFlow`** at `sz0` (`𝔠 = 1/6`, `𝔡 = 1/10`, `κ = 1/10`, `E = 0`, `t = t*`). -/
theorem inst_goodFlow :
    ∃ E' t0 t1 : ℕ → ℝ, Eq729B_FlowData sz0 (1 / 10) Ei tU E' t0 t1 ∧
      ∀ n, |E' n| ≤ 2 - 1 / 10 ∧ 0 ≤ t1 n ∧ t1 n ≤ t0 n ∧ t0 n < 1 :=
  Eq729B_goodFlow sz0 sz0_admissible (κ := 1 / 10) (by norm_num) hE0 (fun n => (tU_ok n).1)

/-- The explicit flow data of (7.47) at `sz0` (`E = 0`, `t = t*`): `E' = lemE z_n`, `t₀ = lemT z_n`, `t₁ = (1 - ζ(t_n)) t₀`,
`z_n = i η_Q` (`Eq729B_flowData_formulas`; junk at the finitely many `n` with `Im z_n ≤ 0`, so only the eventual targets use it). -/
private def Ec (n : ℕ) : ℝ := lemE (Eq729B_zQ sz0 (1 / 10) Ei n)
private def T0c (n : ℕ) : ℝ := lemT (Eq729B_zQ sz0 (1 / 10) Ei n)
private def T1c (n : ℕ) : ℝ := (1 - ouZeta (tU n)) * lemT (Eq729B_zQ sz0 (1 / 10) Ei n)

private theorem fdc : Eq729B_FlowData sz0 (1 / 10) Ei tU Ec T0c T1c := Eq729B_flowData_formulas sz0 (1 / 10) Ei tU

/-- **`Eq729B_derived`** at the explicit flow data of `sz0`: `h730`, `hscale`, `hell` hold eventually. -/
theorem inst_derived :
    (∀ᶠ n in atTop, T0c n - T1c n ≤ Nsz sz0 n ^ (-ouTauMax (1 / 6) (1 / 10)) * etaT (Ec n) (T0c n)) ∧
      (∀ᶠ n in atTop, (gueScale sz0 Ec n (T0c n))⁻¹ ≤ Nsz sz0 n ^ (-ouTauMax (1 / 6) (1 / 10))) ∧
      (∀ᶠ n in atTop, ((sz0.L n : ℕ) : ℝ) ^ 3 * (1 - T1c n) ≤ sz0.lam n ^ 2) :=
  Eq729B_derived sz0 sz0_admissible (κ := 1 / 10) (by norm_num) hτUi le_rfl hE0 tU_ok fdc

/-- **`Eq729B_bridge`** at `sz0` and the explicit flow data: `STExp2 sz0 E' t₁` from `UNMLOut 3` (a pin of ST-6, kept as a
hypothesis). -/
theorem inst_bridge (hML : UNMLOut 3) : sz0.STExp2 Ec T1c :=
  Eq729B_bridge hML (le_refl 3) sz0 sz0_admissible (κ := 1 / 10) (by norm_num) hE0 (fun n => (tU_ok n).1) fdc

/-- **`Eq729B_eq747_of_eq729`** at `sz0` and the explicit flow data (`K = gueGridK sz0 3`); `H729` (the conclusion of
`gueGrid_eq729`, a stochastic statement) is the hypothesis of the target. -/
theorem inst_eq747_of_eq729 (H729 : Eq729B_Concl sz0 Ec T1c T0c (gueGridK sz0 3)) (τ : ℝ) (hτ : 0 < τ) :
    Eq729B_OUBody sz0 (1 / 10) Ei tU τ :=
  Eq729B_eq747_of_eq729 sz0 (le_refl 3) sz0_admissible (κ := 1 / 10) (by norm_num) hE0 (fun n => (tU_ok n).1) fdc
    (gueGridK_ne_zero sz0 3) H729 τ hτ

/-- **`Eq729B_eq747_of_inputs`** at `sz0` (`𝔠 = 1/6`, `𝔡 = 1/10`, `κ = 1/10`, `E = 0`, `t = t*`, `τ_U = ouTauMax = 1/720`,
`n₀ = 3`): the good flow data of `Eq729B_goodFlow`, the primitive family `Kt` of `gueK_exists` at every `n`, `hKinit`, `hK`, `hK2`
and `hB` (from `UNMLOut 3` by `Eq729B_bridge`) discharged; `UNMLOut 3` and `GUEPathBounds` (the pins of ST-6 and UN-49/50/51)
stay hypotheses. -/
theorem inst_eq747_of_inputs (hML : UNMLOut 3) :
    ∃ (E' t0 t1 : ℕ → ℝ) (Kt : ∀ n, ℝ → LoopIdx (Zd 3 (sz0.L n)) → ℂ),
      Eq729B_FlowData sz0 (1 / 10) Ei tU E' t0 t1 ∧
      (∀ n, |E' n| ≤ 2 - 1 / 10 ∧ 0 ≤ t1 n ∧ t1 n ≤ t0 n ∧ t0 n < 1) ∧
      (GUEPathBounds sz0 E' t1 t0 (gueGridK sz0 3) 3 Kt → ∀ τ : ℝ, 0 < τ → Eq729B_OUBody sz0 (1 / 10) Ei tU τ) := by
  obtain ⟨E', t0, t1, hF, hgood⟩ := inst_goodFlow
  choose Kt h1 h2 h3 using fun n => gueK_exists 3 (sz0.L n) (sz0.W n) (sz0.three_le_L n) (sz0.lam n)
    (E := E' n) (by linarith [(hgood n).1, abs_nonneg (E' n)] : |E' n| < 2)
    (hgood n).2.1 (hgood n).2.2.1 (hgood n).2.2.2 (4 * 3)
  refine ⟨E', t0, t1, Kt, hF, hgood, fun hP τ hτ => ?_⟩
  exact Eq729B_eq747_of_inputs sz0 (le_refl 3) sz0_admissible (κ := 1 / 10) (τU := ouTauMax (1 / 6) (1 / 10))
    (by norm_num) hτUi le_rfl 3 (le_refl 3) hE0 tU_ok hF hgood Kt (fun n k σ a => h1 n _)
    (fun n t ht I hI h hl => h2 n t ht I hI h hl) h3
    (Eq729B_bridge hML (le_refl 3) sz0 sz0_admissible (κ := 1 / 10) (by norm_num) hE0 (fun n => (tU_ok n).1) hF) hP τ hτ


/-! ### The real-variable lemmas of the chain at explicit data -/

/-- `Eq729B_bctl_le_two_calB` at `sz0`, `n = 0` (`L = 4`, `W = 32`, `ilambda = 1/64`, `N = 2097152`), `η_Q = 1 - t₁ = 2^{-18}`. -/
theorem inst_bctl_le_two_calB : sz0.Bctl 0 (1 - 1 / 262144) ≤ 2 * calB sz0 0 (1 / 262144) 0 :=
  Eq729B_bctl_le_two_calB sz0 0 (by norm_num) (by norm_num) (by norm_num)

/-- `Eq729B_Ld_mul_etaQ` at `sz0`, `n = 7`, `𝔡 = 3/10`. -/
example : ((sz0.L 7 : ℕ) : ℝ) ^ 3 * ouEtaQ sz0 (3 / 10) 7 * ((sz0.W 7 : ℕ) : ℝ) ^ (4 * (3 / 10 : ℝ) / 3) =
    sz0.lam 7 * ((sz0.W 7 : ℕ) : ℝ) ^ (-((3 : ℕ) : ℝ) / 2 + 3 / 10) := Eq729B_Ld_mul_etaQ sz0 7 (3 / 10)

/-- `Eq729B_qdBoundExp_eq` at `sz0`, `n = 7`, `τ = 1/100`, `η = η_Q`. -/
example : qdBoundExp sz0 7 (1 / 100) (ouEtaQ sz0 (3 / 10) 7) = ((sz0.W 7 : ℕ) : ℝ) ^ (1 / 100 : ℝ) *
    (calB sz0 7 (ouEtaQ sz0 (3 / 10) 7) 0 ^ 2 * ((sz0.lam 7 ^ 2 * ((sz0.W 7 : ℕ) : ℝ) ^ 3) ^ (-(1 / 5 : ℝ)) +
      calB sz0 7 (ouEtaQ sz0 (3 / 10) 7) 0)) := Eq729B_qdBoundExp_eq sz0 7 (1 / 100) _

/-- `Eq729B_h730_hscale_real` at `N = 4`, `η_Q = 4`, `s = 1/2`, `τ_U = 1/2`, `ζ_t = 1/4`. -/
example : (1 / 4 : ℝ) ≤ (4 : ℝ) ^ (-(1 / 2 : ℝ)) * (1 / 2 * 4) ∧ (4 * (1 / 2 * 4) : ℝ)⁻¹ ≤ (4 : ℝ) ^ (-(1 / 2 : ℝ)) := by
  have h4 : (4 : ℝ) ^ (-1 + 1 / 2 : ℝ) = 1 / 2 := by
    rw [show (-1 + 1 / 2 : ℝ) = -(1 / 2) by norm_num, Real.rpow_neg (by norm_num), ← Real.sqrt_eq_rpow,
      show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    norm_num
  exact Eq729B_h730_hscale_real (N := 4) (ηQ := 4) (s := 1 / 2) (ζt := 1 / 4) (τU := 1 / 2) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num [Real.rpow_one]) (by rw [h4]; norm_num)

/-- `Eq729B_final_729` at `E = 0`, `ρ = Λ³ = K c = 1`, `I₀ = 1/2`. -/
example : Real.exp 0 * (1 * (1 / 2) + 1) ≤ 56 * 1 * (1 + 1 / 2) :=
  Eq729B_final_729 (E := 0) (ρ := 1) (I0 := 1 / 2) (Λ3 := 1) (Kc := 1) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

/-- `Eq729B_gronwall_factor` at `N = 100`, `η = 1/10`, `Δt = 1/100`, `M = 1/10`, `ρ = 1`. -/
example : Real.exp (1 / 100 * (2 * 100 * (1 * (100 * (1 / 10))⁻¹))) ≤ Real.exp 2 :=
  Eq729B_gronwall_factor (N := 100) (η := 1 / 10) (dt := 1 / 100) (M := 1 / 10) (ρ := 1) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

/-- `Eq729B_loss_absorb` at `N = W = 16`, `𝔠 = 1`, `τ = 2`. -/
example : 12 * (16 : ℝ) ^ ((1 : ℝ) * 2 / 2) ≤ (16 : ℝ) ^ (2 : ℝ) :=
  Eq729B_loss_absorb (N := 16) (W := 16) (𝔠 := 1) (τ := 2) (by norm_num) (by norm_num) (by norm_num [Real.rpow_one])
    (by norm_num [Real.rpow_one])

/-- `Eq729B_arith` at `N = 27 = 3^3` (`d = 3`, the least size), `A = 80`, `ρ = Λ = 1`, `E₀ = 1/100`, `K = 28^{160}`. -/
example : Real.exp (1 / 100 * (2 * ((27 : ℕ) : ℝ) * (1 * 1))) *
    (1 * 1 ^ 3 + (((27 : ℕ) : ℝ) + 1) ^ (2 * 80) * eq729c ((27 : ℕ) : ℝ) 1 1 (3 / ((27 : ℕ) : ℝ) ^ 12)
      ((1 / 100) / ((((27 : ℕ) : ℝ) + 1) ^ (2 * 80)))) ≤ 56 * 1 * 1 ^ 3 :=
  Eq729B_arith (N := 27) (by norm_num) (ρ := 1) (Λ := 1) (E0 := 1 / 100) (Δ := (1 / 100) / ((((27 : ℕ) : ℝ) + 1) ^ (2 * 80)))
    (Kr := (((27 : ℕ) : ℝ) + 1) ^ (2 * 80)) 80 le_rfl rfl le_rfl one_pos (by norm_num) (by norm_num)
    (by field_simp) (by positivity) (by norm_num)

/-- The flow data of `inst_goodFlow` agree with themselves eventually, and `Eq729B_STExp2_congr` at `sz0`. -/
example : ∃ E' t0 t1 : ℕ → ℝ, Eq729B_FlowData sz0 (1 / 10) Ei tU E' t0 t1 ∧
    (∀ᶠ n in atTop, E' n = E' n) ∧ ∀ᶠ n in atTop, t1 n = t1 n := by
  obtain ⟨E', t0, t1, hF, -⟩ := inst_goodFlow
  exact ⟨E', t0, t1, hF, Eq729B_FlowData.ev_eq hF hF⟩

example (hML : UNMLOut 3) : sz0.STExp2 Ec T1c :=
  Eq729B_STExp2_congr sz0 (Eventually.of_forall fun _ => rfl) (Eventually.of_forall fun _ => rfl) (inst_bridge hML)

end Eq729BInst

end RBM.Univ.GUEPhase

end
