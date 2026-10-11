/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.BA.GreenOff
import RBM3D.BA.GreenCore
import RBM3D.BA.GreenStab
import RBM3D.BA.Step1Boot

/-!
# T2408 probe (BA-G6a design gate, probe step of CONTROL H203; never merged, no root import)

The Lean form of the pins GL1-GL6 of `docs/reports/T2408-prove.md`, section (a), (G)(v).  Namespace `RBM.BA`, stem `GreenLocal_`.
The file has definitions, `#check` lines and `example`s only (no theorem, no placeholder proof): the statement of a theorem
`X` of (G)(v) is the `Prop` `X_pin` here (`∀ d, 2 ≤ d → ...`, as `baGbEXPij'_holds`, `BA/GreenOff.lean:1289`, is `∀ d, 2 ≤ d → BAGbEXPij' d`);
stage 1b proves the theorem with `d` and `hd : 2 ≤ d` as arguments.  Compile: `lake env lean RBM3D/Probe/T2408Pins.lean` in the T2408 worktree.

* Section 1: GL1 `GreenLocal_floor_sample_pin`, GL2 `baGbEXPii_holds_pin` (the merged text `BAGbEXPii`, `BA/Step1Boot.lean:108`),
  GL3 `GreenLocal_LocalLaw`, GL4 `GreenLocal_Floor`, GL5 `GreenLocal_omega`, GL6 `GreenLocal_Gav`, and their `_pin`s.
* Section 2: the premises that G5a and G5c take, as their probes state them (text copied: `BAFAav` from `t/T2401` at `aec5a16`,
  `RBM3D/Probe/T2401Pins.lean:337`; `GreenIBP_Omega`, `GreenIBP_hll` from `t/T2402` at `4b5f864`, `RBM3D/Probe/T2402Pins.lean:173,177`).
* Section 3: `#check` lines.
* Section 4: nonemptiness at `d = 3`, `sz0`, `zSeq`, `flow_sz0`: `t ≡ 1/2` (`STInitialGT2gL`, the induction's output, and `BAFAav`,
  owed by G5b, stay hypotheses), the bridges of item (ii) of the ticket (G5a and G6b, G5c), and `t ≡ 0` (`G_0 = M`), where
  `(initialGT2)` is proved and every hypothesis of GL1, GL3, GL4, GL5, GL6 is discharged.
-/

set_option linter.style.longLine false
set_option linter.unusedVariables false
noncomputable section
open MeasureTheory Filter Matrix
open RBM RBM.Green RBM.Gauss RBM.Gauss.Sizes

namespace RBM.BA

/-! ## 1. The pins GL1-GL6 -/

/-- **GL1 `GreenLocal_floor_sample`** (one sample, deterministic; the BA twin of `inv_Wd_le_maxLoopPM`, `Green/EntryDom.lean:386`):
`|M_{uu}| = |m| ≥ κ` and `‖G - M‖_max ≤ δ ≤ κ/2` give `|G_{uu}| ≥ κ/2`, so `𝓛^{(2)}_{(-,+),(a,a)} ≥ W^{-d} κ²/4`. -/
def GreenLocal_floor_sample_pin : Prop :=
  ∀ {d L W : ℕ} [NeZero L] [NeZero W] {G M : Matrix (Vtx d L W) (Vtx d L W) ℂ} {Mb : Matrix (Zd d L) (Zd d L) ℂ} {m : ℂ}
    {κ δ : ℝ}, 0 < κ → (∀ u v, M u v = if u.2 = v.2 then Mb u.1 v.1 else 0) → (∀ a, Mb a a = m) → κ ≤ ‖m‖ → δ ≤ κ / 2 →
    (∀ u v, ‖G u v - M u v‖ ≤ δ) → ∀ a : Zd d L, ((W : ℝ) ^ d)⁻¹ ≤ 4 / κ ^ 2 * GreenCore_loop G a a

/-- **GL2 `baGbEXPii_holds`**: the merged pin `BAGbEXPii` (`BA/Step1Boot.lean:108`, text unchanged) for `2 ≤ d`
(the guard of `baGbEXPij'_holds`, `BA/GreenOff.lean:1289`). -/
def baGbEXPii_holds_pin : Prop := ∀ d : ℕ, 2 ≤ d → BAGbEXPii d

/-- **GL3 `GreenLocal_LocalLaw`**: the BA local law at a deterministic control, per sequence: `(initialGT2)` (`STInitialGT2gL`,
`Chain/Carrier.lean:140`) gives `‖G_t - M‖_max ≺ Ψ` (the band `LocalLawDetThm`, `Green/LocalLaw.lean:166`, with the carrier `baFMz`). -/
def GreenLocal_LocalLaw (d : ℕ) : Prop :=
  ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z →
      ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ BAflowT0 sz z n) →
        ∀ ε₀ : ℝ, 0 < ε₀ → ∀ Ψ : ℕ → ℝ, (∀ᶠ n in atTop, 0 ≤ Ψ n) →
          STInitialGT2gL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) t ε₀ Ψ →
            PrecL sz (Sizes.seqP (sz.withLam 0)) (U := fun n => Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n))
              (fun n p ω => ‖(baFMz sz z).GM n (t n) ω p.1 p.2‖) (fun n _ _ => Ψ n)

/-- **Pin `greenLocal_localLaw`**: `GreenLocal_LocalLaw d` for `2 ≤ d`. -/
def greenLocal_localLaw_pin : Prop := ∀ d : ℕ, 2 ≤ d → GreenLocal_LocalLaw d

/-- **GL4 `GreenLocal_Floor`**: the BA floor along the flow (the band `LoopFloorThm`, `Green/LocalLaw.lean:207`,
`4 N^ε Ψ²` replaced by `(4/κ²) N^ν Ψ²`; `ν` is the exponent of `N`, `ε` is that of `BAFlow`). -/
def GreenLocal_Floor (d : ℕ) : Prop :=
  ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z →
      ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ BAflowT0 sz z n) →
        ∀ ε₀ : ℝ, 0 < ε₀ → ∀ Ψ : ℕ → ℝ,
          STInitialGT2gL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) t ε₀ Ψ →
            ∀ ν : ℝ, 0 < ν → ∀ᶠ n in atTop,
              (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ 4 / κ ^ 2 * ((sz.size n : ℕ) : ℝ) ^ ν * Ψ n ^ 2

/-- **Pin `greenLocal_floor`**: `GreenLocal_Floor d` for `2 ≤ d`. -/
def greenLocal_floor_pin : Prop := ∀ d : ℕ, 2 ≤ d → GreenLocal_Floor d

/-- **GL5 `GreenLocal_omega`**: from (A) of `(initialGT2)` (`‖G_t - M‖_max ≺ W^{-ε₀}`) the event `{‖G_t - M‖_max ≤ N^ζ W^{-ε₀}}` has
high probability, and `N^ζ W^{-ε₀} ≤ κ/2` eventually, for `0 < ζ ≤ 𝔠 ε₀ / 2` (`W ≥ N^𝔠`).  No guard on `d`. -/
def GreenLocal_omega (d : ℕ) : Prop :=
  ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z →
      ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ BAflowT0 sz z n) →
        ∀ ε₀ : ℝ, 0 < ε₀ →
          PrecL sz (Sizes.seqP (sz.withLam 0)) (U := fun n => Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n))
            (fun n p ω => ‖(baFMz sz z).GM n (t n) ω p.1 p.2‖) (fun n _ _ => ((sz.W n : ℕ) : ℝ) ^ (-ε₀)) →
          ∀ ζ : ℝ, 0 < ζ → ζ ≤ 𝔠 * ε₀ / 2 →
            (∀ᶠ n in atTop, ((sz.size n : ℕ) : ℝ) ^ ζ * ((sz.W n : ℕ) : ℝ) ^ (-ε₀) ≤ κ / 2) ∧
            HighProbAt (Sizes.seqP (sz.withLam 0)) sz.size
              (fun n => {ω | ∀ x y : Idx d (sz.L n) (sz.W n),
                ‖(baFMz sz z).GM n (t n) ω x y‖ ≤ ((sz.size n : ℕ) : ℝ) ^ ζ * ((sz.W n : ℕ) : ℝ) ^ (-ε₀)})

/-- **Pin `greenLocal_omega`**: `GreenLocal_omega d` for every `d`. -/
def greenLocal_omega_pin : Prop := ∀ d : ℕ, GreenLocal_omega d

/-- **GL6 `GreenLocal_Gav`** (the averaged wiring): the averaged law of the residual `𝒦` (the conclusion of `BAFAav`, owed by G5b)
gives `‖L^{(1)}_a - m‖ ≺ Ψ²` uniformly in `a` (the conclusion of `BAGavLGEX`, `BA/Step1Boot.lean:97-103`): `L^{(1)}_a - m = v̄_a`,
`v̄ - t M^{(+,+)} v̄ = ⟨M𝒦⟩` (`GreenCore_E3`), `‖v̄‖_max ≤ 16 κ⁻⁴ ‖⟨M𝒦⟩‖_max` (`baStab_holds`). -/
def GreenLocal_Gav (d : ℕ) : Prop :=
  ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z →
      ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ BAflowT0 sz z n) → ∀ Ψ : ℕ → ℝ,
        PrecL sz (Sizes.seqP (sz.withLam 0)) (U := fun n => Zd d (sz.L n))
          (fun n a ω => ‖(((sz.W n : ℝ) ^ d)⁻¹ : ℝ) * ∑ o, ∑ b',
            BAMB d (sz.L n) (BAflowLam0 sz z n) (BAflowEs sz z n : ℂ) (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) a b' *
              GreenCore_K (GreenCore_Gc sz z n (t n) ω) (GreenCore_Mc sz z n) (GreenCore_Xc sz n (t n) ω)
                (GreenCore_Dc sz z n) (t n) (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) (b', o) (a, o)‖)
          (fun n _ _ => Ψ n ^ 2) →
        PrecL sz (Sizes.seqP (sz.withLam 0)) (U := fun n => Zd d (sz.L n))
          (fun n a ω => ‖(baFMz sz z).L n (t n) (fun _ : Fin 1 => true) (fun _ => a) ω - (baFMz sz z).m n‖)
          (fun n _ _ => Ψ n ^ 2)

/-- **Pin `greenLocal_gav_of_fa`**: `GreenLocal_Gav d` for `2 ≤ d`. -/
def greenLocal_gav_of_fa_pin : Prop := ∀ d : ℕ, 2 ≤ d → GreenLocal_Gav d

/-! ## 2. The premises of G5a and G5c (text copied from the probes of T2401 and T2402; never merged) -/

/-- `BAFAav` of G5b (`t/T2401` at `aec5a16`, `RBM3D/Probe/T2401Pins.lean:337-346`, after Amend 1 D1). -/
def BAFAav (d : ℕ) : Prop :=
  ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z →
    ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ BAflowT0 sz z n) → ∀ ε₀ : ℝ, 0 < ε₀ → BAGiiGEX sz z t (ε₀ / 2) →
    ∀ Ψ : ℕ → ℝ, (∀ᶠ n in atTop, ((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2) ≤ Ψ n) →
      (∀ᶠ n in atTop, Ψ n ≤ ((sz.W n : ℕ) : ℝ) ^ (-ε₀)) →
      STInitialGT2gL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) t ε₀ Ψ →
        PrecL sz (Sizes.seqP (sz.withLam 0)) (U := fun n => Zd d (sz.L n))
          (fun n a ω => ‖(((sz.W n : ℝ) ^ d)⁻¹ : ℝ) * ∑ o, ∑ b',
            BAMB d (sz.L n) (BAflowLam0 sz z n) (BAflowEs sz z n : ℂ) (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) a b' *
              GreenCore_K (GreenCore_Gc sz z n (t n) ω) (GreenCore_Mc sz z n) (GreenCore_Xc sz n (t n) ω)
                (GreenCore_Dc sz z n) (t n) (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) (b', o) (a, o)‖)
          (fun n _ _ => Ψ n ^ 2)

/-- `Ω_δ = {‖G_t - M‖_max ≤ δ_n}` (`t/T2402` at `4b5f864`, `RBM3D/Probe/T2402Pins.lean:173`). -/
def GreenIBP_Omega {d : ℕ} (sz : Sizes d) (z : ℕ → ℂ) (t δ : ℕ → ℝ) (n : ℕ) : Set sz.SeqΩ :=
  {ω | ∀ x y : Idx d (sz.L n) (sz.W n), ‖(baFMz sz z).GM n (t n) ω x y‖ ≤ δ n}

/-- `hll` (`t/T2402` at `4b5f864`, `RBM3D/Probe/T2402Pins.lean:177`). -/
def GreenIBP_hll {d : ℕ} (sz : Sizes d) (z : ℕ → ℂ) (t Ψ : ℕ → ℝ) : Prop :=
  PrecL sz (Sizes.seqP (sz.withLam 0)) (U := fun n => Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n))
    (fun n p ω => ‖(baFMz sz z).GM n (t n) ω p.1 p.2‖) (fun n _ _ => Ψ n)

/-! ## 3. `#check` lines -/

#check GreenLocal_floor_sample_pin
#check baGbEXPii_holds_pin
#check GreenLocal_LocalLaw
#check greenLocal_localLaw_pin
#check GreenLocal_Floor
#check greenLocal_floor_pin
#check GreenLocal_omega
#check greenLocal_omega_pin
#check GreenLocal_Gav
#check greenLocal_gav_of_fa_pin
#check BAFAav
#check GreenIBP_Omega
#check GreenIBP_hll


/-! ## 4. Nonemptiness

The data: `d = 3`, `sz0` at `n = 0` (`L = 4`, `W = 32`, `N = 2097152`, `λ = 1/64`), the flow `flow_sz0` (`κ = 1/2`, `ε = 1/10`,
`𝔠 = 1/6`, `𝔡 = 1/10`), `t ≡ 1/2 ≤ T₀` (`half_lt_t0`), `ε₀ = 1/10`, `Ψ = W^{-1}` (`W^{-3/2} ≤ Ψ ≤ W^{-1/10}`), `ζ = 1/120 = 𝔠 ε₀ / 2`.
In the examples at `t ≡ 1/2`, `STInitialGT2gL` (the induction's output) and `BAFAav` (owed by G5b) stay hypotheses. -/

namespace GreenLocalInst

open SizesInst FlowPinsInst

/-- `Ψ = W^{-1}`. -/
abbrev Ψ0 : ℕ → ℝ := fun n => ((sz0.W n : ℕ) : ℝ) ^ (-1 : ℝ)
/-- `δ_n = N^{1/120} W^{-1/10}`. -/
abbrev δ0 : ℕ → ℝ := fun n => ((sz0.size n : ℕ) : ℝ) ^ (1 / 120 : ℝ) * ((sz0.W n : ℕ) : ℝ) ^ (-(1 / 10 : ℝ))

end GreenLocalInst

open SizesInst FlowPinsInst GreenLocalInst

-- GL2 at the instance, no extra hypothesis; and at `ε₀/2` (the premise of `BAFAav`, T2401 Amend 1 D1)
example (h : baGbEXPii_holds_pin) : BAGiiGEX sz0 zSeq (fun _ => 1 / 2) (1 / 10) :=
  h 3 (by norm_num) (1 / 2) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 6) sz0 zSeq flow_sz0
    (fun _ => 1 / 2) (fun _ => by norm_num) (fun n => (half_lt_t0 n).le) (1 / 10) (by norm_num)

example (h : baGbEXPii_holds_pin) : BAGiiGEX sz0 zSeq (fun _ => 1 / 2) (1 / 10 / 2) :=
  h 3 (by norm_num) (1 / 2) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 6) sz0 zSeq flow_sz0
    (fun _ => 1 / 2) (fun _ => by norm_num) (fun n => (half_lt_t0 n).le) (1 / 10 / 2) (by norm_num)

-- GL3 at the instance; its conclusion is `GreenIBP_hll` (T2402), literally
example (h : greenLocal_localLaw_pin)
    (hinit : STInitialGT2gL (baFMz sz0 zSeq) (Sizes.seqP (sz0.withLam 0)) (fun _ => 1 / 2) (1 / 10) Ψ0) :
    GreenIBP_hll sz0 zSeq (fun _ => 1 / 2) Ψ0 :=
  h 3 (by norm_num) (1 / 2) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 6) sz0 zSeq flow_sz0
    (fun _ => 1 / 2) (fun _ => by norm_num) (fun n => (half_lt_t0 n).le) (1 / 10) (by norm_num) Ψ0
    (Eventually.of_forall fun n => Real.rpow_nonneg (Nat.cast_nonneg _) _) hinit

-- GL4 at the instance (`ν` arbitrary)
example (h : greenLocal_floor_pin)
    (hinit : STInitialGT2gL (baFMz sz0 zSeq) (Sizes.seqP (sz0.withLam 0)) (fun _ => 1 / 2) (1 / 10) Ψ0) (ν : ℝ) (hν : 0 < ν) :
    ∀ᶠ n in atTop, (((sz0.W n : ℕ) : ℝ) ^ 3)⁻¹ ≤ 4 / (1 / 2 : ℝ) ^ 2 * ((sz0.size n : ℕ) : ℝ) ^ ν * Ψ0 n ^ 2 :=
  h 3 (by norm_num) (1 / 2) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 6) sz0 zSeq flow_sz0
    (fun _ => 1 / 2) (fun _ => by norm_num) (fun n => (half_lt_t0 n).le) (1 / 10) (by norm_num) Ψ0 hinit ν hν

-- GL5 at the instance, from (A) of `hinit`; the conclusion is the premise pair of `BAIBPDet` (T2402) at `δ = δ0`
example (h : greenLocal_omega_pin)
    (hinit : STInitialGT2gL (baFMz sz0 zSeq) (Sizes.seqP (sz0.withLam 0)) (fun _ => 1 / 2) (1 / 10) Ψ0) :
    (∀ᶠ n in atTop, δ0 n ≤ 1 / 2 / 2) ∧
      HighProbAt (Sizes.seqP (sz0.withLam 0)) sz0.size (GreenIBP_Omega sz0 zSeq (fun _ => 1 / 2) δ0) :=
  h 3 (1 / 2) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 6) sz0 zSeq flow_sz0
    (fun _ => 1 / 2) (fun _ => by norm_num) (fun n => (half_lt_t0 n).le) (1 / 10) (by norm_num) hinit.1 (1 / 120)
    (by norm_num) (by norm_num)

-- GL6 at the instance; the premise is the conclusion of `BAFAav` at `Ψ0`
example (h : greenLocal_gav_of_fa_pin)
    (hFA : PrecL sz0 (Sizes.seqP (sz0.withLam 0)) (U := fun n => Zd 3 (sz0.L n))
      (fun n a ω => ‖(((sz0.W n : ℝ) ^ 3)⁻¹ : ℝ) * ∑ o, ∑ b',
        BAMB 3 (sz0.L n) (BAflowLam0 sz0 zSeq n) (BAflowEs sz0 zSeq n : ℂ) (BAmF sz0 (BAflowLam0 sz0 zSeq) (BAflowEs sz0 zSeq) n) a b' *
          GreenCore_K (GreenCore_Gc sz0 zSeq n (1 / 2) ω) (GreenCore_Mc sz0 zSeq n) (GreenCore_Xc sz0 n (1 / 2) ω)
            (GreenCore_Dc sz0 zSeq n) (1 / 2) (BAmF sz0 (BAflowLam0 sz0 zSeq) (BAflowEs sz0 zSeq) n) (b', o) (a, o)‖)
      (fun n _ _ => Ψ0 n ^ 2)) :
    PrecL sz0 (Sizes.seqP (sz0.withLam 0)) (U := fun n => Zd 3 (sz0.L n))
      (fun n a ω => ‖(baFMz sz0 zSeq).L n (1 / 2) (fun _ : Fin 1 => true) (fun _ => a) ω - (baFMz sz0 zSeq).m n‖)
      (fun n _ _ => Ψ0 n ^ 2) :=
  h 3 (by norm_num) (1 / 2) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 6) sz0 zSeq flow_sz0
    (fun _ => 1 / 2) (fun _ => by norm_num) (fun n => (half_lt_t0 n).le) Ψ0 hFA

-- (ii), G5a and G6b: `BAFAav` (premise `BAGiiGEX` at `ε₀/2` from GL2) and GL6 compose to `BAGbEXPav d`, one `intro`
example (d : ℕ) (hd : 2 ≤ d) (hFA : BAFAav d) (hii : baGbEXPii_holds_pin) (hgav : greenLocal_gav_of_fa_pin) : BAGbEXPav d := by
  intro κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow t ht0 htT ε₀ hε₀ Ψ hlo hhi hinit
  exact hgav d hd κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow t ht0 htT Ψ
    (hFA κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow t ht0 htT ε₀ hε₀
      (hii d hd κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow t ht0 htT (ε₀ / 2) (half_pos hε₀)) Ψ hlo hhi hinit)

-- (ii), G5c: GL3 and GL5 give the premises `hll`, `hΩ`, `δ ≤ κ/2` of `BAIBPDet` (T2402), generic in the data
example (h3 : greenLocal_localLaw_pin) (h5 : greenLocal_omega_pin) (d : ℕ) (hd : 2 ≤ d) (κ ε 𝔡 : ℝ) (hκ : 0 < κ) (hε : 0 < ε)
    (h𝔡 : 0 < 𝔡) (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ) (hflow : BAFlow sz κ ε 𝔠 𝔡 z) (t : ℕ → ℝ) (ht0 : ∀ n, 0 ≤ t n)
    (htT : ∀ n, t n ≤ BAflowT0 sz z n) (ε₀ : ℝ) (hε₀ : 0 < ε₀) (Ψ : ℕ → ℝ) (hΨ : ∀ᶠ n in atTop, 0 ≤ Ψ n)
    (hinit : STInitialGT2gL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) t ε₀ Ψ) (ζ : ℝ) (hζ : 0 < ζ) (hζ' : ζ ≤ 𝔠 * ε₀ / 2) :
    GreenIBP_hll sz z t Ψ ∧ (∀ᶠ n in atTop, ((sz.size n : ℕ) : ℝ) ^ ζ * ((sz.W n : ℕ) : ℝ) ^ (-ε₀) ≤ κ / 2) ∧
      HighProbAt (Sizes.seqP (sz.withLam 0)) sz.size
        (GreenIBP_Omega sz z t (fun n => ((sz.size n : ℕ) : ℝ) ^ ζ * ((sz.W n : ℕ) : ℝ) ^ (-ε₀))) :=
  ⟨h3 d hd κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow t ht0 htT ε₀ hε₀ Ψ hΨ hinit,
    (h5 d κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow t ht0 htT ε₀ hε₀ hinit.1 ζ hζ hζ').1,
    (h5 d κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow t ht0 htT ε₀ hε₀ hinit.1 ζ hζ hζ').2⟩


/-! ### `t ≡ 0`: `G_0 = M`, `X = 0` (`(initialGT2)` is proved, `𝒦 = 0`); every hypothesis of GL1, GL3-GL6 is discharged at `sz0` -/

example (h1 : GreenLocal_floor_sample_pin) (h3 : greenLocal_localLaw_pin) (h4 : greenLocal_floor_pin)
    (h5 : greenLocal_omega_pin) (h6 : greenLocal_gav_of_fa_pin) :
    (∀ (ω : sz0.SeqΩ) (a : Zd 3 (sz0.L 0)),
      (((sz0.W 0 : ℕ) : ℝ) ^ 3)⁻¹ ≤ 4 / (1 / 2 : ℝ) ^ 2 * GreenCore_loop (GreenCore_Gc sz0 zSeq 0 0 ω) a a) ∧
    GreenIBP_hll sz0 zSeq (fun _ => 0) Ψ0 ∧
    (∀ ν : ℝ, 0 < ν → ∀ᶠ n in atTop,
      (((sz0.W n : ℕ) : ℝ) ^ 3)⁻¹ ≤ 4 / (1 / 2 : ℝ) ^ 2 * ((sz0.size n : ℕ) : ℝ) ^ ν * Ψ0 n ^ 2) ∧
    (∀ᶠ n in atTop, δ0 n ≤ 1 / 2 / 2) ∧
      HighProbAt (Sizes.seqP (sz0.withLam 0)) sz0.size (GreenIBP_Omega sz0 zSeq (fun _ => 0) δ0) ∧
    PrecL sz0 (Sizes.seqP (sz0.withLam 0)) (U := fun n => Zd 3 (sz0.L n))
      (fun n a ω => ‖(baFMz sz0 zSeq).L n 0 (fun _ : Fin 1 => true) (fun _ => a) ω - (baFMz sz0 zSeq).m n‖)
      (fun n _ _ => Ψ0 n ^ 2) := by
  have hT : ∀ n, (0 : ℝ) ≤ BAflowT0 sz0 zSeq n := fun n => ((by norm_num : (0 : ℝ) ≤ 1 / 2)).trans (half_lt_t0 n).le
  have hW1 : ∀ n, (1 : ℝ) ≤ ((sz0.W n : ℕ) : ℝ) := fun n => by exact_mod_cast sz0.W_pos n
  -- `X = 0`: `√0 V = 0`
  have hH0 : ∀ (n : ℕ) (ω : sz0.SeqΩ) (i j : Idx 3 (sz0.L n) (sz0.W n)), Sizes.seqHflow (sz0.withLam 0) n 0 ω i j = 0 := by
    intro n ω i j
    change (((Real.sqrt 0 : ℝ) : ℂ) • (sz0.withLam 0).seqXmat n ω) i j = 0
    rw [Real.sqrt_zero, Complex.ofReal_zero, zero_smul]
    rfl
  have hX0 : ∀ (n : ℕ) (ω : sz0.SeqΩ), GreenCore_Xc sz0 n 0 ω = 0 := fun n ω => by
    ext u v
    exact hH0 n ω _ _
  -- `𝒦 = 0` at `t = 0`, `X = 0`
  have hK0 : ∀ (n : ℕ) (ω : sz0.SeqΩ) (m : ℂ) (u y : Vtx 3 (sz0.L n) (sz0.W n)), GreenCore_K (GreenCore_Gc sz0 zSeq n 0 ω)
      (GreenCore_Mc sz0 zSeq n) (GreenCore_Xc sz0 n 0 ω) (GreenCore_Dc sz0 zSeq n) 0 m u y = 0 := by
    intro n ω m u y
    simp [GreenCore_K, GreenCore_Arow, GreenCore_Xrow, hX0]
  -- `G_0 = M`: `G - M = -M (√0 V + 0 · m) G = 0`
  have hZ : ∀ (n : ℕ) (ω : sz0.SeqΩ), BAGt sz0 (BAflowLam0 sz0 zSeq) (BAflowEs sz0 zSeq) n 0 ω =
      BAMfine sz0 (BAflowLam0 sz0 zSeq) (BAflowEs sz0 zSeq) n := by
    intro n ω
    have h := (BAGt_sub_BAMfine sz0 (BAflowLam0 sz0 zSeq) (BAflowEs sz0 zSeq) n 0 ω (by norm_num) (BAmF_sz0_im_pos n)).1
    have hP : BAflowPert sz0 (BAflowLam0 sz0 zSeq) (BAflowEs sz0 zSeq) n 0 ω = 0 := by
      ext i j
      simp only [BAflowPert, Matrix.add_apply, Matrix.of_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.zero_apply]
      rw [hH0 n ω i j]
      simp
    rw [hP, mul_zero, zero_mul, neg_zero] at h
    exact sub_eq_zero.1 h
  have hGM : ∀ (n : ℕ) (ω : sz0.SeqΩ), GreenCore_Gc sz0 zSeq n 0 ω = GreenCore_Mc sz0 zSeq n := fun n ω => by
    ext u v
    simp only [GreenCore_Gc, GreenCore_Mc, blockMat, Matrix.submatrix_apply]
    rw [hZ n ω]
  -- `𝓛^{(2)}(M) = W^{-d} |M^{(B)}_{ab}|² ≤ W^{-d}` (Kronecker structure, `‖M^{(B)}‖_max ≤ 1`)
  have loopM : ∀ (n : ℕ) (a b : Zd 3 (sz0.L n)), GreenCore_loop (GreenCore_Mc sz0 zSeq n) a b ≤ (((sz0.W n : ℕ) : ℝ) ^ 3)⁻¹ := by
    intro n a b
    obtain ⟨-, -, -, -, -, hM, -, -, -⟩ := GreenCore_carrier (by norm_num : (0 : ℝ) < 1 / 2) sz0 flow_sz0 n (t := 0) le_rfl
      (hT n) (fun _ => 0) rfl rfl rfl
    have hr := BAflow_real (1 / 2) (1 / 10) (1 / 6) (1 / 10) sz0 zSeq flow_sz0 n
    have hb : ‖BAMB 3 (sz0.L n) (BAflowLam0 sz0 zSeq n) (BAflowEs sz0 zSeq n : ℂ)
        (BAmF sz0 (BAflowLam0 sz0 zSeq) (BAflowEs sz0 zSeq) n) a b‖ ^ 2 ≤ 1 := by
      have h1 := BAMB_row_sq_real 3 (sz0.L n) (BAflowLam0 sz0 zSeq n) (BAflowEs sz0 zSeq n) _ hr.1 a
      rw [← h1]
      exact Finset.single_le_sum (f := fun b => ‖BAMB 3 (sz0.L n) (BAflowLam0 sz0 zSeq n) (BAflowEs sz0 zSeq n : ℂ)
        (BAmF sz0 (BAflowLam0 sz0 zSeq) (BAflowEs sz0 zSeq) n) a b‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ b)
    have e : ∀ o : Fin (sz0.W n ^ 3), ∑ o' : Fin (sz0.W n ^ 3), ‖GreenCore_Mc sz0 zSeq n (a, o) (b, o')‖ ^ 2 =
        ‖BAMB 3 (sz0.L n) (BAflowLam0 sz0 zSeq n) (BAflowEs sz0 zSeq n : ℂ)
          (BAmF sz0 (BAflowLam0 sz0 zSeq) (BAflowEs sz0 zSeq) n) a b‖ ^ 2 := fun o => by
      rw [Finset.sum_eq_single o]
      · simp [hM]
      · intro o' _ ho'
        simp [hM, Ne.symm ho']
      · simp
    unfold GreenCore_loop
    rw [sq, mul_assoc]
    simp only [e]
    calc (((sz0.W n : ℕ) : ℝ) ^ 3)⁻¹ * ((((sz0.W n : ℕ) : ℝ) ^ 3)⁻¹ * ∑ _o : Fin (sz0.W n ^ 3), ‖BAMB 3 (sz0.L n)
          (BAflowLam0 sz0 zSeq n) (BAflowEs sz0 zSeq n : ℂ) (BAmF sz0 (BAflowLam0 sz0 zSeq) (BAflowEs sz0 zSeq) n) a b‖ ^ 2)
        ≤ (((sz0.W n : ℕ) : ℝ) ^ 3)⁻¹ * 1 :=
          mul_le_mul_of_nonneg_left (GreenCore_avg_le fun _ => hb) GreenCore_w_pos.le
      _ = _ := mul_one _
  -- `ξ ≤ ζ`, `0 ≤ ζ` give `ξ ≺ ζ` (the bad set is empty)
  have det : ∀ {U : ℕ → Type} (ξ ζ : ∀ n, U n → sz0.SeqΩ → ℝ), (∀ n u ω, ξ n u ω ≤ ζ n u ω) →
      (∀ n u ω, 0 ≤ ζ n u ω) → PrecL sz0 (Sizes.seqP (sz0.withLam 0)) ξ ζ := by
    intro U ξ ζ hξ hζ τ hτ D hD
    refine Eventually.of_forall fun n => ?_
    refine (measure_mono_null (t := ∅) (fun ω hω => ?_) measure_empty).trans_le zero_le
    obtain ⟨u, hu⟩ := hω
    have h1 : 1 ≤ ((sz0.size n : ℕ) : ℝ) ^ τ := Real.one_le_rpow (by exact_mod_cast sz0.one_le_size n) hτ.le
    nlinarith [hξ n u ω, hζ n u ω, mul_nonneg (sub_nonneg.2 h1) (hζ n u ω)]
  -- `(initialGT2)` at `t ≡ 0`: (A) `‖G - M‖_max = 0`, (B) `max 𝓛 ≤ W^{-3} ≤ W^{-2} = Ψ²`
  have hinit0 : STInitialGT2gL (baFMz sz0 zSeq) (Sizes.seqP (sz0.withLam 0)) (fun _ => 0) (1 / 10) Ψ0 := by
    refine ⟨det _ _ (fun n p ω => ?_) (fun n _ _ => Real.rpow_nonneg (Nat.cast_nonneg _) _),
      det _ _ (fun n _ ω => ?_) (fun n _ _ => sq_nonneg _)⟩
    · change ‖BAGt sz0 (BAflowLam0 sz0 zSeq) (BAflowEs sz0 zSeq) n 0 ω p.1 p.2 -
        BAMfine sz0 (BAflowLam0 sz0 zSeq) (BAflowEs sz0 zSeq) n p.1 p.2‖ ≤ _
      rw [hZ n ω, sub_self, norm_zero]
      exact Real.rpow_nonneg (Nat.cast_nonneg _) _
    · unfold STmaxLoop2g
      refine Finset.sup'_le _ _ fun p _ => ?_
      have hH : (sz0.seqHflowBA (BAflowLam0 sz0 zSeq) n 0 ω).IsHermitian := by
        unfold Sizes.seqHflowBA
        refine IsHermitian.add ?_ (Sizes.seqHflow_isHermitian (sz0.withLam 0) n 0 ω)
        unfold IsHermitian
        rw [conjTranspose_smul, (PsiI_isHermitian 3 _ _).eq,
          show star (BAflowLam0 sz0 zSeq n : ℂ) = (BAflowLam0 sz0 zSeq n : ℂ) from Complex.conj_ofReal _]
      change ‖loopFine 3 (sz0.L n) (sz0.W n) (sz0.seqHflowBA (BAflowLam0 sz0 zSeq) n 0 ω)
        (ztOf (BAmF sz0 (BAflowLam0 sz0 zSeq) (BAflowEs sz0 zSeq) n) (BAflowEs sz0 zSeq n) 0) ![false, true] ![p.1, p.2]‖ ≤ _
      rw [GreenOff_loop_eq hH]
      change GreenCore_loop (GreenCore_Gc sz0 zSeq n 0 ω) p.1 p.2 ≤ Ψ0 n ^ 2
      rw [hGM n ω]
      refine (loopM n p.1 p.2).trans ?_
      have e : Ψ0 n ^ 2 = ((((sz0.W n : ℕ) : ℝ)) ^ 2)⁻¹ := by simp [Ψ0, Real.rpow_neg_one, inv_pow]
      rw [e]
      exact inv_anti₀ (by have := hW1 n; positivity) (pow_le_pow_right₀ (hW1 n) (by norm_num))
  have hΨ : ∀ᶠ n in atTop, 0 ≤ Ψ0 n := Eventually.of_forall fun n => Real.rpow_nonneg (Nat.cast_nonneg _) _
  refine ⟨fun ω a => ?_, ?_, fun ν hν => ?_, ?_, ?_, ?_⟩
  · obtain ⟨-, -, -, -, -, hM, hMd, -, -⟩ := GreenCore_carrier (by norm_num : (0 : ℝ) < 1 / 2) sz0 flow_sz0 0 (t := 0) le_rfl
      (hT 0) ω rfl rfl rfl
    have hr := BAflow_real (1 / 2) (1 / 10) (1 / 6) (1 / 10) sz0 zSeq flow_sz0 0
    exact h1 (by norm_num) hM hMd (hr.2.trans ((le_abs_self _).trans (Complex.abs_im_le_norm _))) (δ := 0) (by norm_num)
      (fun u v => by rw [hGM 0 ω, sub_self, norm_zero]) a
  · exact h3 3 (by norm_num) (1 / 2) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 6) sz0 zSeq flow_sz0
      (fun _ => 0) (fun _ => le_rfl) hT (1 / 10) (by norm_num) Ψ0 hΨ hinit0
  · exact h4 3 (by norm_num) (1 / 2) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 6) sz0 zSeq flow_sz0
      (fun _ => 0) (fun _ => le_rfl) hT (1 / 10) (by norm_num) Ψ0 hinit0 ν hν
  · exact (h5 3 (1 / 2) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 6) sz0 zSeq flow_sz0
      (fun _ => 0) (fun _ => le_rfl) hT (1 / 10) (by norm_num) hinit0.1 (1 / 120) (by norm_num) (by norm_num)).1
  · exact (h5 3 (1 / 2) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 6) sz0 zSeq flow_sz0
      (fun _ => 0) (fun _ => le_rfl) hT (1 / 10) (by norm_num) hinit0.1 (1 / 120) (by norm_num) (by norm_num)).2
  · exact h6 3 (by norm_num) (1 / 2) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 6) sz0 zSeq flow_sz0
      (fun _ => 0) (fun _ => le_rfl) hT Ψ0 (det _ _ (fun n a ω => by simp only [hK0, mul_zero, Finset.sum_const_zero, norm_zero]; exact sq_nonneg _) (fun _ _ _ => sq_nonneg _))

end RBM.BA
