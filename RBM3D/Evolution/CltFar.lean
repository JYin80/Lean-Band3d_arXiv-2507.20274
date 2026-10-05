/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Evolution.CltMoments2
import RBM3D.Evolution.MeanFar
import RBM3D.Evolution.CltStep
import RBM3D.Induction.Step5Kit

/-!
# S5-25 (ST-4): `lem;CLT`, far part -- the pin `STCltFar` (ticket T2182)

Paper: arXiv:2507.20274, `paper/tex/3_5_Loop_Hierarchy.tex` (`3_5:line`): `lem;CLT`
(`3_5:2173-2176`), its proof `3_5:2182-2249`: the split `f^{far} = 𝔼 f^{far} + (f^{far} - 𝔼
f^{far})` (`3_5:2182-2212`), `(eq:boundEfar)` (`3_5:2211`), the `2p`-th moment
`(eq:main_challenge3)` (`3_5:2213`), and the properties `(eq:propcalB)` (`3_5:2155`) of `𝓑 =
(𝓛-𝒦)^{(2)}_{s,σ}` taken from `(Eq:Gdecay_w)` at `u = s`.  The pin `STCltFar`
(`Induction/Step5Pins.lean:396`, conclusion `STCltFarConcl` `:385`) is proved as stated.

**Targets** (namespace `RBM.Gauss.Sizes`; constants explicit, no hidden `≺`):

1. `cltFar_dom : CltFar.DomStmt d`: the per-label tail `CltMom2.DomHyp` of the profile-normalised
   `𝗕 = A^{6/5} 𝓑` at `Λ' = N^τ`, `q₁ = N^{-D₁}` from `STGdecayW` at `u = s` (event inclusion,
   `A^{6/5} R ζ' ≤ c₀ + 2𝔡^{-4} ≤ N^{τ/2}`).
2. `cltFar_off : CltFar.OffStmt d`: `‖CltMom2.off‖ ≤ W^{-D}` for every `(σ, a)` at once, off one
   event of probability `≤ N^{-D'}` (the single good event of `STGdecayW`, `D_w = D + 3/𝔠 + 1`;
   the mean by the a.s. envelope and the per-entry bad events).
3. `cltFar_fluc : CltFar.FlucStmt d`: `P(N^τ A^{-6/5}/R_a < ‖c_n fluc‖) ≤ N^{-D}` eventually,
   uniformly in `σ₀ ≠ σ₁`, `a`: Markov and the `2p`-th moment `cltMom2_tail_eventually` on
   `STCltIsoConcl`, `p = ⌈(D+2)/τ⌉`, `Λ' = N^{τ/2}`, `q₁ = N^{-D₁}`, `εf = W^{-D'}`.
4. `stCltFar_holds : STCltFar d`: `f = 𝔼 f + c_n fluc + off` (`cltMom2_decomp`), the mean part
   `meanFar_eventually` at `τ/2`, targets 2 and 3 at `(D₀, D+1)` and `(τ/2, D+3)` with
   `D₀ = 6d/5 + (d-2)/𝔠 + 1` (`W^{-D₀} ≤ A^{-6/5}/R_a`), and the union
   over the index set inside `Prec` by the explicit bound `#({σ // σ₀ ≠ σ₁} × (Fin 2 → Z_L^d)) ≤ 4
   N²`.

Ports (read-only sources, RBM3D `main`): private lemmas of `Evolution/MeanFar.lean` (commit
`a21a819`, ticket T2157) copied as `cltFar_*` (section 2, source lines in the list below):
`meanFar_norm_integral_le` `:845`, `meanFar_K_eq` `:885`, `meanFar_Theta_shift` `:991`,
`meanFar_ell_sq` `:1255`, `meanFar_Bparam_le` `:1275`, `meanFar_c3` `:1294`, `meanFar_c0` `:1297`,
`meanFar_c3_pos` `:1299`, `meanFar_BctlSTWB` `:1303`, `meanFar_n_K` `:1495`, `meanFar_polylog`
`:1921`, `meanFar_three_halves` `:1964`; adapted: `meanFar_B_bound`
`:964` (to `∫ STLKM`, `cltFar_B_bound`), `meanFar_bad_le` `:942` (all indices at once,
`cltFar_good_event`), the blocks `hκ'`, `hWdw`, `h5n` of `meanFar_eventually` `:1980`
(`cltFar_mE_im_ge`, `cltFar_W_rpow_le`, `cltFar_H5_at`). No RBM1D/RBM2D file is
read or copied here.

Differences from the paper (paper-delta candidates `T2182a...`, see the prove report): the indices
`(eq:ells_to_ellt)`, `(eq:ells_to_ellt2)` are carried by the index set only; `(eq:propcalB)` is the
event `{N^τ ζ' < |𝓑|}` of `(Eq:Gdecay_w)` at `u = s` with explicit `(Λ', q₁) = (N^τ, N^{-D₁})`, and
the off-window `W^{-D}` is one event for all `(σ, a)`; the choices `p = ⌈(D+2)/τ⌉`,
`D₁ = 18p + ⌈D⌉ + 4`, `D' = (6p + ⌈D⌉ + 3)/𝔠` (target 3), `D_w = D + 3/𝔠 + 1`,
`D₁ = D + 6/𝔠 + 2` (target 2) and `D₀` (target 4); the union over the index set by the explicit
bound `4L^{2d} ≤ 4N²`. -/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal

namespace RBM.Gauss.Sizes

open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Evol

/-! ## 1. The pinned intermediate statements (targets 1-3) -/

/-- Target 1: the per-label tail `CltMom2.DomHyp` (`(eq:propcalB)`, first half, `3_5:2155`) from `(Eq:Gdecay_w)` at
`u = s`, with `Λ' = N^τ`, `q₁ = N^{-D₁}`, eventually, every `σ`. -/
def CltFar.DomStmt (d : ℕ) : Prop :=
  3 ≤ d → ∀ (sz : Sizes d) (𝔠 𝔡 Cd : ℝ) (E s t : ℕ → ℝ), sz.Admissible 𝔠 𝔡 →
    (∀ n, s n < 1) → (∀ n, s n ≤ t n) → STReg5I sz s t → STGdecayW sz E s t Cd →
    ∀ τ D₁ : ℝ, 0 < τ → 0 < D₁ → ∀ᶠ n in atTop, ∀ σ : Fin 2 → Bool,
      CltMom2.DomHyp sz n (E n) (s n) σ (((sz.size n : ℕ) : ℝ) ^ τ) (((sz.size n : ℕ) : ℝ) ^ (-D₁))

/-- Target 2: the off-window part (`(eq:propcalB)`, second half, `3_5:2155`; the `O(W^{-D})` of `(eq:2p_product)`):
`‖CltMom2.off‖ ≤ W^{-D}` for every `σ, a` at once, off an event of probability `≤ N^{-D'}`, eventually. -/
def CltFar.OffStmt (d : ℕ) : Prop :=
  3 ≤ d → ∀ (sz : Sizes d) (κ 𝔠 𝔡 Cd : ℝ) (E s t : ℕ → ℝ), 0 < κ → sz.Admissible 𝔠 𝔡 →
    (∀ n, |E n| ≤ 2 - κ) → (∀ n, 0 ≤ s n) → (∀ n, s n < t n) → (∀ n, t n < 1) → STReg5I sz s t →
    STGdecayW sz E s t Cd →
    ∀ D D' : ℝ, 0 < D → 0 < D' → ∀ᶠ n in atTop,
      sz.seqP {ω | ∃ (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)),
          ((sz.W n : ℕ) : ℝ) ^ (-D) < ‖CltMom2.off sz n (E n) (s n) (t n) σ a ω‖} ≤
        ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-D'))

/-- Target 3: the window fluctuation `c_n · fluc` (`(eq:main_challenge3)`, `3_5:2213-2249`) at one index `(σ, a)`:
`P(N^τ A^{-6/5}/(|a₁-a₂|^{d-2}+1) < ‖c_n fluc‖) ≤ N^{-D}`, eventually, uniformly in `σ₀ ≠ σ₁` and `a`. -/
def CltFar.FlucStmt (d : ℕ) : Prop :=
  3 ≤ d → ∀ (sz : Sizes d) (κ 𝔠 𝔡 Cd : ℝ) (E s t : ℕ → ℝ), 0 < κ → sz.Admissible 𝔠 𝔡 →
    (∀ n, |E n| ≤ 2 - κ) → (∀ n, 0 ≤ s n) → (∀ n, s n < t n) → (∀ n, t n < 1) → STReg5I sz s t →
    STGdecayW sz E s t Cd → STCltIsoConcl sz E s t →
    ∀ τ D : ℝ, 0 < τ → 0 < D → ∀ᶠ n in atTop, ∀ σ : Fin 2 → Bool, σ 0 ≠ σ 1 →
      ∀ a : Fin 2 → Zd d (sz.L n),
        sz.seqP {ω | ((sz.size n : ℕ) : ℝ) ^ τ * (STAI sz n ^ (-(6 / 5 : ℝ)) /
              (((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) ^ (d - 2) + 1)) <
            ‖(((1 - s n) ^ 2 / (sz.lam n ^ 4 * (sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d) ^ (6 / 5 : ℝ)) : ℝ) : ℂ) *
              CltMom2.fluc sz n (E n) (s n) (t n) σ a ω‖} ≤
          ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-D))


/-! ## 2. Copied private helpers

Copies of private lemmas of the merged `RBM3D/Evolution/MeanFar.lean` (commit `a21a819`, ticket T2157), renamed
`meanFar_ ↦ cltFar_`; the source line of each is in its docstring. -/

section Copied

variable {d : ℕ} (sz : Sizes d)

/-- `‖∫ f‖ ≤ M + C · P(‖f‖ > M)` for `‖f‖ ≤ C`: the expectation of a `≺` bound
(a.s. polynomial envelope `C` plus a small bad event).  Copy of `meanFar_norm_integral_le`
(`Evolution/MeanFar.lean:845`, commit `a21a819`). -/
private theorem cltFar_norm_integral_le {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (f : Ω → ℂ) (hf : Measurable f) (M C : ℝ) (hM : 0 ≤ M)
    (hall : ∀ ω, ‖f ω‖ ≤ C) :
    ‖∫ ω, f ω ∂P‖ ≤ M + C * P.real {ω | M < ‖f ω‖} := by
  have hint : Integrable f P :=
    Integrable.of_bound hf.aestronglyMeasurable C (Filter.Eventually.of_forall hall)
  have hS : MeasurableSet {ω | M < ‖f ω‖} := measurableSet_lt measurable_const hf.norm
  set S := {ω | M < ‖f ω‖} with hSdef
  have hpt : ∀ ω, ‖f ω‖ ≤ M + C * S.indicator (1 : Ω → ℝ) ω := by
    intro ω
    by_cases h : ω ∈ S
    · rw [Set.indicator_of_mem h]
      have := hall ω
      simp only [Pi.one_apply]
      linarith
    · rw [Set.indicator_of_notMem h]
      simpa using not_lt.1 h
  have hind : Integrable (S.indicator (1 : Ω → ℝ)) P := (integrable_const (1 : ℝ)).indicator hS
  calc ‖∫ ω, f ω ∂P‖ ≤ ∫ ω, ‖f ω‖ ∂P := norm_integral_le_integral_norm f
    _ ≤ ∫ ω, (M + C * S.indicator (1 : Ω → ℝ) ω) ∂P :=
        integral_mono hint.norm ((integrable_const M).add (hind.const_mul C)) hpt
    _ = M + C * P.real S := by
        rw [integral_add (integrable_const M) (hind.const_mul C), integral_const_mul,
          integral_indicator_one hS, integral_const]
        simp

/-- `𝒦^{(2)}_{s,σ,(a,b)} = W^{-d} m₁ m₂ Θ_{s m₁ m₂}(a,b)` (`(Kn2sol)`).  Copy of `meanFar_K_eq`
(`Evolution/MeanFar.lean:885`). -/
private theorem cltFar_K_eq (n : ℕ) (E s : ℝ) (σ : Fin 2 → Bool) (a b : Zd d (sz.L n)) :
    STKloop sz n E s σ ![a, b] = (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * (mSigma E (σ 0) * mSigma E (σ 1)) *
      Theta d (sz.L n) (sz.lam n) ((s : ℂ) * (mSigma E (σ 0) * mSigma E (σ 1))) a b := by
  unfold STKloop
  have h : KLloopOf d (sz.L n) σ ![a, b] = ⟨[σ 0, σ 1], [a, b]⟩ := by
    simp [KLloopOf, List.ofFn_succ]
  rw [h, KLK_two]

/-- `Θ_{xy} = Θ_{0,y-x}` (property 2).  Copy of `meanFar_Theta_shift` (`Evolution/MeanFar.lean:991`). -/
private theorem cltFar_Theta_shift {L : ℕ} [NeZero L] (hL : 3 ≤ L) {g : ℝ} {ξ : ℂ} (hξ : ‖ξ‖ < 1)
    (x y : Zd d L) : Theta d L g ξ x y = Theta d L g ξ 0 (y - x) := by
  have := Theta_apply_add_right_of_three_le (d := d) (g := g) hL hξ 0 (y - x) x
  rwa [zero_add, sub_add_cancel] at this

/-- `ℓ_s ≤ g/√(1-s)` when `1-s ≤ g²`: `(1-s) ℓ_s² ≤ g²`, i.e. `(1-s)² ℓ_s⁴ ≤ g⁴`.  Copy of
`meanFar_ell_sq` (`Evolution/MeanFar.lean:1255`). -/
private theorem cltFar_ell_sq {L : ℕ} {g s : ℝ} (hg : 0 < g) (hs : s < 1) (h : 1 - s ≤ g ^ 2) :
    (1 - s) * ellT L g s ^ 2 ≤ g ^ 2 := by
  have hv : (0 : ℝ) < 1 - s := by linarith
  have habs : |1 - s| = 1 - s := abs_of_pos hv
  have hsq : 0 < √|1 - s| := Real.sqrt_pos.2 (by rw [habs]; exact hv)
  have h1 : 1 ≤ g / √|1 - s| := by
    rw [le_div_iff₀ hsq, one_mul]
    refine Real.sqrt_le_iff.2 ⟨hg.le, ?_⟩
    rw [habs]; exact h
  have hmin : ellT L g s ≤ g / √|1 - s| := by
    refine (min_le_left _ _).trans ?_
    exact max_le le_rfl h1
  have h0 : 0 ≤ ellT L g s := le_min (le_trans zero_le_one (le_max_right _ _)) (Nat.cast_nonneg L)
  have hsq2 : (g / √|1 - s|) ^ 2 = g ^ 2 / (1 - s) := by
    rw [div_pow, Real.sq_sqrt (abs_nonneg _), habs]
  calc (1 - s) * ellT L g s ^ 2 ≤ (1 - s) * (g / √|1 - s|) ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h0 hmin 2) hv.le
    _ = g ^ 2 := by rw [hsq2]; field_simp

/-- `B_{t,K}` is dominated by `(1 + 2^{d-1}) g^{-2} (K+1)^{-(d-2)}` for `K ≤ L`, `1 - t ≥ g²/L²`.  Copy of
`meanFar_Bparam_le` (`Evolution/MeanFar.lean:1275`). -/
private theorem cltFar_Bparam_le (hd : 3 ≤ d) {L : ℕ} (hL : 3 ≤ L) {g t : ℝ} (hg : 0 < g) (ht : t < 1)
    (hreg : g ^ 2 / (L : ℝ) ^ 2 ≤ 1 - t) (K : ℕ) (hK : K ≤ L) :
    Bparam d L g t K ≤ (1 + 2 ^ (d - 1)) * ((g ^ 2)⁻¹ * ((((K : ℕ) : ℝ) + 1) ^ (d - 2))⁻¹) := by
  have hL1 : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast (by omega : 1 ≤ L)
  have hu : (0 : ℝ) < 1 - t := by linarith
  have habs : |1 - t| = 1 - t := abs_of_pos hu
  have hr0 : (0 : ℝ) ≤ ((K : ℕ) : ℝ) := Nat.cast_nonneg _
  have hrL : ((K : ℕ) : ℝ) ≤ (L : ℝ) := by exact_mod_cast hK
  have hzm := zeroMode_le_of_ge (d := d) (L := L) (g := g) (t := t) (by omega) hL1 ht hr0 hrL hreg
  have hgg : (g ^ 2 + |1 - t|)⁻¹ ≤ (g ^ 2)⁻¹ := inv_anti₀ (by positivity) (by rw [habs]; linarith)
  unfold Bparam
  have e1 : (g ^ 2 + |1 - t|)⁻¹ * ((((K : ℕ) : ℝ) + 1) ^ (d - 2))⁻¹ ≤
      (g ^ 2)⁻¹ * ((((K : ℕ) : ℝ) + 1) ^ (d - 2))⁻¹ := by gcongr
  have e2 : ((L : ℝ) ^ d * |1 - t|)⁻¹ ≤ 2 ^ (d - 1) * ((g ^ 2)⁻¹ * ((((K : ℕ) : ℝ) + 1) ^ (d - 2))⁻¹) := by
    refine hzm.trans ?_
    gcongr
  nlinarith

/-- The constant `1 + 2^{d-1}` of `cltFar_Bparam_le`.  Copy of `meanFar_c3` (`Evolution/MeanFar.lean:1294`). -/
private def cltFar_c3 (d : ℕ) : ℝ := 1 + 2 ^ (d - 1)

/-- The constant `c₃^{1/5} c₃` of `(eq:propcalB)`.  Copy of `meanFar_c0` (`Evolution/MeanFar.lean:1297`). -/
private def cltFar_c0 (d : ℕ) : ℝ := cltFar_c3 d ^ (1 / 5 : ℝ) * cltFar_c3 d

/-- Copy of `meanFar_c3_pos` (`Evolution/MeanFar.lean:1299`). -/
private theorem cltFar_c3_pos (d : ℕ) : 0 < cltFar_c3 d := by unfold cltFar_c3; positivity

/-- `(W^{-d} B_{s,0})^{1/5} (W^{-d} B_{s,K}) ≤ c₀ A^{-6/5} (K+1)^{-(d-2)}`, `A = g² W^d`
(`(eq:propcalB)` with `(Eq:Gdecay_w)`, `3_5:2139-2150`).  Copy of `meanFar_BctlSTWB`
(`Evolution/MeanFar.lean:1303`). -/
private theorem cltFar_BctlSTWB (sz : Sizes d) (n : ℕ) (hd : 3 ≤ d) {s : ℝ} (hs : s < 1)
    (hg : 0 < sz.lam n) (hreg : sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 ≤ 1 - s) (K : ℕ)
    (hK : K ≤ sz.L n) :
    sz.Bctl n s ^ (1 / 5 : ℝ) * STWB sz n s K ≤
      cltFar_c0 d * STAI sz n ^ (-(6 / 5 : ℝ)) / (((K : ℕ) : ℝ) + 1) ^ (d - 2) := by
  have hL := sz.three_le_L n
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hWd : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) ^ d := by positivity
  set A : ℝ := STAI sz n with hAdef
  have hA : 0 < A := by rw [hAdef]; unfold STAI; positivity
  have hAe : A = sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d := rfl
  have hc3 := cltFar_c3_pos d
  have hB0 := cltFar_Bparam_le hd hL hg hs hreg 0 (Nat.zero_le _)
  have hBK := cltFar_Bparam_le hd hL hg hs hreg K hK
  have hBctl : sz.Bctl n s ≤ cltFar_c3 d / A := by
    unfold Sizes.Bctl
    refine (mul_le_mul_of_nonneg_left hB0 (by positivity)).trans ?_
    simp only [Nat.cast_zero, zero_add, one_pow, inv_one, mul_one]
    rw [hAe]; unfold cltFar_c3
    field_simp
    rfl
  have hSTWB : STWB sz n s K ≤ cltFar_c3 d / A / (((K : ℕ) : ℝ) + 1) ^ (d - 2) := by
    unfold STWB
    refine (mul_le_mul_of_nonneg_left hBK (by positivity)).trans ?_
    rw [hAe]; unfold cltFar_c3
    field_simp
    rfl
  have hBctl0 : 0 ≤ sz.Bctl n s := by
    unfold Sizes.Bctl Bparam
    have : 0 < 1 - s := by linarith
    rw [abs_of_pos this]
    positivity
  have h15 : sz.Bctl n s ^ (1 / 5 : ℝ) ≤ (cltFar_c3 d / A) ^ (1 / 5 : ℝ) :=
    Real.rpow_le_rpow hBctl0 hBctl (by norm_num)
  have hrp : (cltFar_c3 d / A) ^ (1 / 5 : ℝ) = cltFar_c3 d ^ (1 / 5 : ℝ) * A ^ (-(1 / 5 : ℝ)) := by
    rw [Real.div_rpow hc3.le hA.le, Real.rpow_neg hA.le, div_eq_mul_inv]
  have hA65 : A ^ (-(6 / 5 : ℝ)) = A ^ (-(1 / 5 : ℝ)) * A⁻¹ := by
    rw [← Real.rpow_neg_one, ← Real.rpow_add hA]; congr 1; norm_num
  have hSW0 : 0 ≤ STWB sz n s K := by
    unfold STWB Bparam
    have : 0 < 1 - s := by linarith
    rw [abs_of_pos this]
    positivity
  calc sz.Bctl n s ^ (1 / 5 : ℝ) * STWB sz n s K
      ≤ (cltFar_c3 d ^ (1 / 5 : ℝ) * A ^ (-(1 / 5 : ℝ))) * (cltFar_c3 d / A / (((K : ℕ) : ℝ) + 1) ^ (d - 2)) := by
        rw [← hrp]
        exact mul_le_mul h15 hSTWB hSW0 (Real.rpow_nonneg (by positivity) _)
    _ = cltFar_c0 d * A ^ (-(6 / 5 : ℝ)) / (((K : ℕ) : ℝ) + 1) ^ (d - 2) := by
        rw [hA65]; unfold cltFar_c0; field_simp

/-- `‖𝒦^{(2)}_{s,σ,(a,b)}‖ ≤ c₁/A` from the decay of `T = Θ(0,·)`: `𝒦^{(2)} = W^{-d} m₁m₂ Θ(a,b)`,
`|m₁ m₂| = 1`, `Θ(a,b) = T(b - a)`.  Copy of `meanFar_n_K` (`Evolution/MeanFar.lean:1495`). -/
private theorem cltFar_n_K (sz : Sizes d) (n : ℕ) {E s : ℝ} (hE : |E| < 2) (hs0 : 0 ≤ s) (hs : s < 1)
    (σ : Fin 2 → Bool) (a b : Zd d (sz.L n)) {K₁ : ℝ}
    (hT : ∀ x : Zd d (sz.L n),
      ‖Theta d (sz.L n) (sz.lam n) ((s : ℂ) * (mSigma E (σ 0) * mSigma E (σ 1))) 0 x‖ ≤ K₁) :
    ‖STKloop sz n E s σ ![a, b]‖ ≤ (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * K₁ := by
  have hL := sz.three_le_L n
  have hξ := norm_mul_mSigma_lt_one hE.le hs0 hs (σ 0) (σ 1)
  rw [cltFar_K_eq, norm_mul, norm_mul, norm_mul, norm_mSigma hE.le, norm_mSigma hE.le, mul_one, mul_one,
    norm_inv, norm_pow, Complex.norm_natCast, cltFar_Theta_shift hL hξ]
  exact mul_le_mul_of_nonneg_left (hT _) (by positivity)

/-- `C (log x)^k ≤ x^ε` eventually (`ε > 0`).  Copy of `meanFar_polylog` (`Evolution/MeanFar.lean:1921`). -/
private theorem cltFar_polylog (C ε : ℝ) (hε : 0 < ε) (k : ℕ) :
    ∀ᶠ x : ℝ in atTop, C * Real.log x ^ k ≤ x ^ ε := by
  have h := (isLittleO_log_rpow_rpow_atTop (k : ℝ) hε).def (c := 1 / (|C| + 1)) (by positivity)
  filter_upwards [h, eventually_ge_atTop (1 : ℝ)] with x hx hx1
  have hl : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hxe : 0 ≤ x ^ ε := Real.rpow_nonneg (by linarith) _
  rw [Real.norm_of_nonneg (Real.rpow_nonneg hl _), Real.norm_of_nonneg hxe, Real.rpow_natCast] at hx
  have h1 : (|C| + 1) * Real.log x ^ k ≤ x ^ ε := by
    have := hx
    rw [one_div, inv_mul_eq_div, le_div_iff₀ (by positivity)] at this
    calc (|C| + 1) * Real.log x ^ k = Real.log x ^ k * (|C| + 1) := mul_comm _ _
      _ ≤ x ^ ε := this
  have h2 : C * Real.log x ^ k ≤ (|C| + 1) * Real.log x ^ k :=
    mul_le_mul_of_nonneg_right (by linarith [le_abs_self C]) (pow_nonneg hl _)
  linarith

/-- `B · lw ≤ lw^{3/2}` when `B² ≤ lw`.  Copy of `meanFar_three_halves` (`Evolution/MeanFar.lean:1964`). -/
private theorem cltFar_three_halves {lw B : ℝ} (hB : 0 < B) (hlw : B ^ 2 ≤ lw) :
    B * lw ≤ lw ^ (3 / 2 : ℝ) := by
  have hlw0 : 0 < lw := lt_of_lt_of_le (by positivity) hlw
  have h1 : lw ^ (3 / 2 : ℝ) = lw * lw ^ (1 / 2 : ℝ) := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hlw0, Real.rpow_one]
  have h2 : B ≤ lw ^ (1 / 2 : ℝ) := by
    have : (B ^ 2) ^ (1 / 2 : ℝ) = B := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hB.le]; norm_num
    calc B = (B ^ 2) ^ (1 / 2 : ℝ) := this.symm
      _ ≤ lw ^ (1 / 2 : ℝ) := Real.rpow_le_rpow (by positivity) hlw (by norm_num)
  rw [h1]
  nlinarith

end Copied

/-! ## 3. The expectation envelope, the single good event and the size facts -/

section Tools

variable {d : ℕ} (sz : Sizes d)

/-- The profile of `(Eq:Gdecay_w)` at `u = s` (the `u = s` case of `STGdecayW`, loss factor `1`):
`ζ'_s(K) = (W^{-d}B_{s,0})^{1/5} (W^{-d}B_{s,K}) e^{-(K/ℓ_s)^{1/2}} + W^{-D_w}`. -/
private def cltFarZ (n : ℕ) (s Dw : ℝ) (K : ℕ) : ℝ :=
  sz.Bctl n s ^ (1 / 5 : ℝ) * STWB sz n s K *
    Real.exp (-(((K : ℕ) : ℝ) / ellT (sz.L n) (sz.lam n) s) ^ (1 / 2 : ℝ)) + ((sz.W n : ℕ) : ℝ) ^ (-Dw)

/-- **`‖𝔼 𝓑_{ab}‖ ≤ N^τ Z + (η_s^{-2} + |𝒦_{ab}|) N^{-D₁}`** from the `≺` bound off an event of probability `≤ N^{-D₁}` and
the a.s. envelope `|𝓛^{(2)}| ≤ η_s^{-2}` (`norm_Lloop_le`).  Copy of `meanFar_B_bound` (`Evolution/MeanFar.lean:964`), stated
for `∫ STLKM` (`meanFar_B` is private there). -/
private theorem cltFar_B_bound (n : ℕ) {E s : ℝ} (hE : |E| < 2) (hs : s < 1) (σ : Fin 2 → Bool)
    (a b : Zd d (sz.L n)) {τ Z D₁ : ℝ} (hZ : 0 ≤ ((sz.size n : ℕ) : ℝ) ^ τ * Z)
    (hP : sz.seqP {ω | ((sz.size n : ℕ) : ℝ) ^ τ * Z <
        ‖STLKM sz n E s (sz.seqHflow n s ω) σ ![a, b]‖} ≤
      ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-D₁))) :
    ‖∫ ω, STLKM sz n E s (sz.seqHflow n s ω) σ ![a, b] ∂(sz.seqP)‖ ≤ ((sz.size n : ℕ) : ℝ) ^ τ * Z +
      ((etaT E s)⁻¹ ^ 2 + ‖STKloop sz n E s σ ![a, b]‖) * ((sz.size n : ℕ) : ℝ) ^ (-D₁) := by
  have hmeas : Measurable fun ω => STLKM sz n E s (sz.seqHflow n s ω) σ ![a, b] :=
    (walk_measurable_Lloop sz n E s σ ![a, b]).sub measurable_const
  have hall : ∀ ω, ‖STLKM sz n E s (sz.seqHflow n s ω) σ ![a, b]‖ ≤
      (etaT E s)⁻¹ ^ 2 + ‖STKloop sz n E s σ ![a, b]‖ := by
    intro ω
    refine (norm_sub_le _ _).trans (add_le_add ?_ le_rfl)
    exact norm_Lloop_le sz n hE hs σ ![a, b] ω
  have h := cltFar_norm_integral_le sz.seqP (fun ω => STLKM sz n E s (sz.seqHflow n s ω) σ ![a, b])
    hmeas _ _ hZ hall
  have hreal : sz.seqP.real {ω | ((sz.size n : ℕ) : ℝ) ^ τ * Z <
        ‖STLKM sz n E s (sz.seqHflow n s ω) σ ![a, b]‖} ≤ ((sz.size n : ℕ) : ℝ) ^ (-D₁) := by
    rw [Measure.real]
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hP
    rwa [ENNReal.toReal_ofReal (Real.rpow_nonneg (Nat.cast_nonneg _) _)] at this
  have hC : 0 ≤ (etaT E s)⁻¹ ^ 2 + ‖STKloop sz n E s σ ![a, b]‖ := by positivity
  refine h.trans ?_
  gcongr

/-- **The single good event of `(Eq:Gdecay_w)` at `u = s`** (`(eq:propcalB)`, `3_5:2155`): the union over `(σ, a, b)` is inside the
probability, by taking the witnesses `u = (s, σ, ![a,b])` in the union of `STGdecayW`.  Port of `meanFar_bad_le`
(`Evolution/MeanFar.lean:942`, one index) to all indices at once. -/
private theorem cltFar_good_event {E s t : ℕ → ℝ} {Cd : ℝ} (hs1 : ∀ n, s n < 1) (hst : ∀ n, s n ≤ t n)
    (hG : STGdecayW sz E s t Cd) {Dw : ℝ} (hDw : 0 < Dw) {τ D₁ : ℝ} (hτ : 0 < τ) (hD₁ : 0 < D₁) :
    ∀ᶠ n in atTop, sz.seqP {ω | ∃ (σ : Fin 2 → Bool) (a b : Zd d (sz.L n)),
      ((sz.size n : ℕ) : ℝ) ^ τ * cltFarZ sz n (s n) Dw (zdistInf d (sz.L n) (a - b)) <
          ‖STLKM sz n (E n) (s n) (sz.seqHflow n (s n) ω) σ ![a, b]‖} ≤
        ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-D₁)) := by
  filter_upwards [hG Dw hDw τ hτ D₁ hD₁] with n hn
  refine le_trans (measure_mono ?_) hn
  intro ω ⟨σ, a, b, hω⟩
  refine ⟨(⟨s n, le_rfl, hst n⟩, σ, ![a, b]), ?_⟩
  have h1 : (1 - s n) ≠ 0 := (sub_pos.2 (hs1 n)).ne'
  simp only [div_self h1, Real.one_rpow, one_mul]
  have e : (![a, b] : Fin 2 → Zd d (sz.L n)) 0 - (![a, b] : Fin 2 → Zd d (sz.L n)) 1 = a - b := by simp
  rw [e]
  exact hω

/-- The single-index form of `cltFar_good_event` (the `≺` bound for one `(σ, a, b)` off an event of probability `≤ N^{-D₁}`). -/
private theorem cltFar_bad_one {E s t : ℕ → ℝ} {Cd : ℝ} (hs1 : ∀ n, s n < 1) (hst : ∀ n, s n ≤ t n)
    (hG : STGdecayW sz E s t Cd) {Dw : ℝ} (hDw : 0 < Dw) {τ D₁ : ℝ} (hτ : 0 < τ) (hD₁ : 0 < D₁) :
    ∀ᶠ n in atTop, ∀ (σ : Fin 2 → Bool) (a b : Zd d (sz.L n)),
      sz.seqP {ω | ((sz.size n : ℕ) : ℝ) ^ τ * cltFarZ sz n (s n) Dw (zdistInf d (sz.L n) (a - b)) <
          ‖STLKM sz n (E n) (s n) (sz.seqHflow n (s n) ω) σ ![a, b]‖} ≤
        ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-D₁)) := by
  filter_upwards [cltFar_good_event sz hs1 hst hG hDw hτ hD₁] with n hn σ a b
  refine le_trans (measure_mono ?_) hn
  intro ω hω
  exact ⟨σ, a, b, hω⟩

/-! ### Size facts at one index -/

private theorem cltFar_size_real (n : ℕ) :
    ((sz.size n : ℕ) : ℝ) = (((sz.W n : ℕ) : ℝ) * ((sz.L n : ℕ) : ℝ)) ^ d := by
  simp [Sizes.size]

private theorem cltFar_one_le_L (n : ℕ) : (1 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) := by
  have := sz.three_le_L n
  exact_mod_cast (by omega : 1 ≤ sz.L n)

private theorem cltFar_one_le_W (n : ℕ) : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := by
  exact_mod_cast sz.W_pos n

private theorem cltFar_Lpow_le (n : ℕ) : ((sz.L n : ℕ) : ℝ) ^ d ≤ ((sz.size n : ℕ) : ℝ) := by
  rw [cltFar_size_real, mul_pow]
  have h1 := one_le_pow₀ (n := d) (cltFar_one_le_W sz n)
  have h2 : (0 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) ^ d := by positivity
  nlinarith

private theorem cltFar_Wpow_le (n : ℕ) : ((sz.W n : ℕ) : ℝ) ^ d ≤ ((sz.size n : ℕ) : ℝ) := by
  rw [cltFar_size_real, mul_pow]
  have h1 := one_le_pow₀ (n := d) (cltFar_one_le_L sz n)
  have h2 : (0 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) ^ d := by positivity
  nlinarith

private theorem cltFar_L_le (hd : 1 ≤ d) (n : ℕ) : ((sz.L n : ℕ) : ℝ) ≤ ((sz.size n : ℕ) : ℝ) :=
  (le_self_pow₀ (cltFar_one_le_L sz n) (by omega)).trans (cltFar_Lpow_le sz n)

private theorem cltFar_W_le (hd : 1 ≤ d) (n : ℕ) : ((sz.W n : ℕ) : ℝ) ≤ ((sz.size n : ℕ) : ℝ) :=
  (le_self_pow₀ (cltFar_one_le_W sz n) (by omega)).trans (cltFar_Wpow_le sz n)

private theorem cltFar_one_le_N (n : ℕ) : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by
  exact_mod_cast sz.one_le_size n

private theorem cltFar_card_Zd (L : ℕ) [NeZero L] : Fintype.card (Zd d L) = L ^ d := by
  simp [Zd, ZMod.card]

/-- `#(Fin 2 → Zd d L) = (L^d)² ≤ N²`. -/
private theorem cltFar_card_pair_le (n : ℕ) :
    ((Fintype.card (Fin 2 → Zd d (sz.L n)) : ℕ) : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ 2 := by
  rw [Fintype.card_fun, cltFar_card_Zd]
  simp only [Fintype.card_fin]
  push_cast
  have h := cltFar_Lpow_le sz n
  have h0 : (0 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) ^ d := by positivity
  nlinarith

/-- `W^{-m/𝔠} ≤ N^{-m}` from `N^𝔠 ≤ W` (`(Main_DEL_COND)`), for a natural `m`: the shape of `hWdw` in `meanFar_eventually`
(`Evolution/MeanFar.lean:2036-2043`). -/
private theorem cltFar_W_rpow_le {N W 𝔠 : ℝ} (hN0 : 0 < N) (h𝔠 : 0 < 𝔠) (hb : N ^ 𝔠 ≤ W) (m : ℕ) :
    W ^ (-((m : ℝ) / 𝔠)) ≤ (N ^ m)⁻¹ := by
  have h𝔠' : 𝔠 ≠ 0 := h𝔠.ne'
  calc W ^ (-((m : ℝ) / 𝔠)) ≤ (N ^ 𝔠) ^ (-((m : ℝ) / 𝔠)) :=
        Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hN0 𝔠) hb (by
          have : (0 : ℝ) ≤ (m : ℝ) / 𝔠 := by positivity
          linarith)
    _ = N ^ (𝔠 * (-((m : ℝ) / 𝔠))) := (Real.rpow_mul hN0.le _ _).symm
    _ = N ^ (-(m : ℝ)) := by congr 1; field_simp
    _ = (N ^ m)⁻¹ := by rw [Real.rpow_neg hN0.le, Real.rpow_natCast]

/-- `min κ (1/2) ≤ Im m(E)` for `|E| ≤ 2 - κ` (the block `hκ'` of `meanFar_eventually`, `Evolution/MeanFar.lean:2046-2057`). -/
private theorem cltFar_mE_im_ge {E κ : ℝ} (hκ : 0 < κ) (hE : |E| ≤ 2 - κ) : min κ (1 / 2) ≤ (mE E).im := by
  rw [mE_im]
  have hκ'0 : 0 < min κ (1 / 2) := lt_min hκ (by norm_num)
  have hE2 : E ^ 2 ≤ (2 - min κ (1 / 2)) ^ 2 := by
    have h1 := abs_le.1 hE
    have h2 : min κ (1 / 2) ≤ κ := min_le_left _ _
    exact sq_le_sq' (by linarith [h1.1]) (by linarith [h1.2])
  have hκ'1 : min κ (1 / 2) ≤ 1 / 2 := min_le_right _ _
  have h4 : (2 * min κ (1 / 2)) ^ 2 ≤ 4 - E ^ 2 := by nlinarith
  have h5 : 2 * min κ (1 / 2) ≤ Real.sqrt (4 - E ^ 2) := by
    calc 2 * min κ (1 / 2) = Real.sqrt ((2 * min κ (1 / 2)) ^ 2) := (Real.sqrt_sq (by linarith)).symm
      _ ≤ _ := Real.sqrt_le_sqrt h4
  linarith

/-- **`(prop:ThfadC)` in the sup form**: `|Θ_u(x,y)| ≤ C₅ (1 + 2^{d-1}) / g²` for `u < 1`, `g²/L² ≤ 1 - u`
(`meanFar_T1`, `Evolution/MeanFar.lean:762`, and `|Θ_{xy}| = |Θ_{0,y-x}|`). -/
private theorem cltFar_Theta_sup (hd : 3 ≤ d) {L : ℕ} [NeZero L] (hL : 3 ≤ L) {g u C₅ c₅ : ℝ} {ξ : ℂ}
    (hξ : ‖ξ‖ < 1) (hg : 0 < g) (hu1 : u < 1) (hreg : g ^ 2 / (L : ℝ) ^ 2 ≤ 1 - u) (hC₅ : 0 ≤ C₅) (hc₅ : 0 < c₅)
    (hdec : ∀ x : Zd d L, ‖Theta d L g ξ 0 x‖ ≤ C₅ * Bparam d L g u (zdistD d L x) *
      Real.exp (-c₅ * (zdistD d L x : ℝ) / ellT L g u)) (x y : Zd d L) :
    ‖Theta d L g ξ x y‖ ≤ C₅ * (1 + 2 ^ (d - 1)) / g ^ 2 := by
  rw [cltFar_Theta_shift hL hξ]
  have h := meanFar_T1 hd hL hg hu1 hreg hC₅ hc₅ (fun x => Theta d L g ξ 0 x) hdec (y - x)
  refine h.trans ?_
  have hr : (1 : ℝ) ≤ (((zdistInf d L (y - x) : ℕ) : ℝ) + 1) ^ (d - 2) :=
    one_le_pow₀ (by have : (0 : ℝ) ≤ ((zdistInf d L (y - x) : ℕ) : ℝ) := Nat.cast_nonneg _; linarith)
  have hc : 0 ≤ C₅ * (1 + 2 ^ (d - 1)) / g ^ 2 := by positivity
  exact div_le_self hc hr

end Tools

/-! ## 4. Target 1: the per-label tail `CltMom2.DomHyp` -/

section Dom

variable {d : ℕ}

/-- **The deterministic core of target 1** (`(eq:propcalB)`, `3_5:2155`): with `A = ilambda² W^d ≥ 1`, `K ≤ L`,
`g²/L² ≤ 1 - s` and `R = K^{d-2} + 1`:
`A^{6/5} R (Bctl^{1/5} STWB(K) e^{-(K/ℓ_s)^{1/2}} + W^{-Dw}) ≤ c₀ + A^{6/5} R W^{-Dw}` with `c₀ = (1 + 2^{d-1})^{6/5}(1 + 2^{d-1})`
(`cltFar_BctlSTWB`: `Bctl^{1/5} STWB(K) ≤ c₀ A^{-6/5} (K+1)^{-(d-2)}`, `K^{d-2} + 1 ≤ (K+1)^{d-2}`, `exp ≤ 1`). -/
private theorem cltFar_dom_key (hd : 3 ≤ d) (sz : Sizes d) (n : ℕ) {s : ℝ} (hs : s < 1) (hg : 0 < sz.lam n)
    (hreg : sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 ≤ 1 - s) (hA1 : 1 ≤ STAI sz n) (K : ℕ) (hK : K ≤ sz.L n)
    (Dw : ℝ) :
    STAI sz n ^ (6 / 5 : ℝ) * (((K : ℕ) : ℝ) ^ (d - 2) + 1) *
        (sz.Bctl n s ^ (1 / 5 : ℝ) * STWB sz n s K *
            Real.exp (-(((K : ℕ) : ℝ) / ellT (sz.L n) (sz.lam n) s) ^ (1 / 2 : ℝ)) + ((sz.W n : ℕ) : ℝ) ^ (-Dw)) ≤
      cltFar_c0 d + STAI sz n ^ (6 / 5 : ℝ) * (((K : ℕ) : ℝ) ^ (d - 2) + 1) * ((sz.W n : ℕ) : ℝ) ^ (-Dw) := by
  have hA0 : 0 < STAI sz n := lt_of_lt_of_le one_pos hA1
  have hBW := cltFar_BctlSTWB sz n hd hs hg hreg K hK
  have hexp : Real.exp (-(((K : ℕ) : ℝ) / ellT (sz.L n) (sz.lam n) s) ^ (1 / 2 : ℝ)) ≤ 1 := by
    rw [Real.exp_le_one_iff, neg_nonpos]
    exact Real.rpow_nonneg (div_nonneg (Nat.cast_nonneg _) (ellT_pos (cltFar_one_le_L sz n)).le) _
  have hBctl0 : 0 ≤ sz.Bctl n s := by
    unfold Sizes.Bctl Bparam
    have : 0 < 1 - s := by linarith
    rw [abs_of_pos this]
    positivity
  have hSTWB0 : 0 ≤ STWB sz n s K := by
    unfold STWB Bparam
    have : 0 < 1 - s := by linarith
    rw [abs_of_pos this]
    positivity
  have hP0 : 0 ≤ sz.Bctl n s ^ (1 / 5 : ℝ) * STWB sz n s K :=
    mul_nonneg (Real.rpow_nonneg hBctl0 _) hSTWB0
  have hK0 : (0 : ℝ) ≤ ((K : ℕ) : ℝ) := Nat.cast_nonneg _
  have hpa : ((K : ℕ) : ℝ) ^ (d - 2) + 1 ≤ (((K : ℕ) : ℝ) + 1) ^ (d - 2) := by
    have := pow_add_pow_le hK0 (zero_le_one' ℝ) (n := d - 2) (by omega)
    simpa using this
  have hR0 : 0 < ((K : ℕ) : ℝ) ^ (d - 2) + 1 := by positivity
  have hY0 : 0 < (((K : ℕ) : ℝ) + 1) ^ (d - 2) := by positivity
  have hAA : STAI sz n ^ (6 / 5 : ℝ) * STAI sz n ^ (-(6 / 5 : ℝ)) = 1 := by
    rw [← Real.rpow_add hA0]; simp
  have hc0 : 0 < cltFar_c0 d := by
    unfold cltFar_c0
    have := cltFar_c3_pos d
    positivity
  have h1 : STAI sz n ^ (6 / 5 : ℝ) * (((K : ℕ) : ℝ) ^ (d - 2) + 1) *
      (sz.Bctl n s ^ (1 / 5 : ℝ) * STWB sz n s K *
        Real.exp (-(((K : ℕ) : ℝ) / ellT (sz.L n) (sz.lam n) s) ^ (1 / 2 : ℝ))) ≤ cltFar_c0 d := by
    calc STAI sz n ^ (6 / 5 : ℝ) * (((K : ℕ) : ℝ) ^ (d - 2) + 1) *
          (sz.Bctl n s ^ (1 / 5 : ℝ) * STWB sz n s K *
            Real.exp (-(((K : ℕ) : ℝ) / ellT (sz.L n) (sz.lam n) s) ^ (1 / 2 : ℝ)))
        ≤ STAI sz n ^ (6 / 5 : ℝ) * (((K : ℕ) : ℝ) ^ (d - 2) + 1) *
          (sz.Bctl n s ^ (1 / 5 : ℝ) * STWB sz n s K) :=
          mul_le_mul_of_nonneg_left (mul_le_of_le_one_right hP0 hexp) (by positivity)
      _ ≤ STAI sz n ^ (6 / 5 : ℝ) * (((K : ℕ) : ℝ) ^ (d - 2) + 1) *
          (cltFar_c0 d * STAI sz n ^ (-(6 / 5 : ℝ)) / (((K : ℕ) : ℝ) + 1) ^ (d - 2)) :=
          mul_le_mul_of_nonneg_left hBW (by positivity)
      _ = cltFar_c0 d * ((((K : ℕ) : ℝ) ^ (d - 2) + 1) / (((K : ℕ) : ℝ) + 1) ^ (d - 2)) := by
          have : STAI sz n ^ (6 / 5 : ℝ) * (((K : ℕ) : ℝ) ^ (d - 2) + 1) *
              (cltFar_c0 d * STAI sz n ^ (-(6 / 5 : ℝ)) / (((K : ℕ) : ℝ) + 1) ^ (d - 2)) =
              (STAI sz n ^ (6 / 5 : ℝ) * STAI sz n ^ (-(6 / 5 : ℝ))) * (cltFar_c0 d *
                ((((K : ℕ) : ℝ) ^ (d - 2) + 1) / (((K : ℕ) : ℝ) + 1) ^ (d - 2))) := by
            field_simp
          rw [this, hAA, one_mul]
      _ ≤ cltFar_c0 d := mul_le_of_le_one_right hc0.le (div_le_one_of_le₀ hpa hY0.le)
  have hsplit : STAI sz n ^ (6 / 5 : ℝ) * (((K : ℕ) : ℝ) ^ (d - 2) + 1) *
      (sz.Bctl n s ^ (1 / 5 : ℝ) * STWB sz n s K *
          Real.exp (-(((K : ℕ) : ℝ) / ellT (sz.L n) (sz.lam n) s) ^ (1 / 2 : ℝ)) + ((sz.W n : ℕ) : ℝ) ^ (-Dw)) =
      STAI sz n ^ (6 / 5 : ℝ) * (((K : ℕ) : ℝ) ^ (d - 2) + 1) *
        (sz.Bctl n s ^ (1 / 5 : ℝ) * STWB sz n s K *
          Real.exp (-(((K : ℕ) : ℝ) / ellT (sz.L n) (sz.lam n) s) ^ (1 / 2 : ℝ))) +
      STAI sz n ^ (6 / 5 : ℝ) * (((K : ℕ) : ℝ) ^ (d - 2) + 1) * ((sz.W n : ℕ) : ℝ) ^ (-Dw) := by ring
  rw [hsplit]
  linarith

/-- `A^{6/5} (K^{d-2} + 1) W^{-3/𝔠} ≤ 2 𝔡^{-4}`: `A ≤ 𝔡^{-2} N`, `K^{d-2} + 1 ≤ 2N` (`K ≤ L`, `L^d ≤ N`) and
`W^{-3/𝔠} ≤ N^{-3}` (`N^𝔠 ≤ W`). -/
private theorem cltFar_dom_tail (sz : Sizes d) (n : ℕ) {𝔠 𝔡 : ℝ} (h𝔠 : 0 < 𝔠)
    (hA1 : 1 ≤ STAI sz n) (hg : 0 < sz.lam n) (hgΛ : sz.lam n ≤ 𝔡⁻¹)
    (hBwn : ((sz.size n : ℕ) : ℝ) ^ 𝔠 ≤ ((sz.W n : ℕ) : ℝ)) (K : ℕ) (hK : K ≤ sz.L n) :
    STAI sz n ^ (6 / 5 : ℝ) * (((K : ℕ) : ℝ) ^ (d - 2) + 1) * ((sz.W n : ℕ) : ℝ) ^ (-(((3 : ℕ) : ℝ) / 𝔠)) ≤
      2 * (𝔡⁻¹) ^ 4 := by
  have hN1 := cltFar_one_le_N sz n
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := lt_of_lt_of_le one_pos hN1
  have hW := cltFar_W_rpow_le hN0 h𝔠 hBwn 3
  have hAN : STAI sz n ≤ (𝔡⁻¹) ^ 2 * ((sz.size n : ℕ) : ℝ) := by
    unfold STAI
    exact mul_le_mul (pow_le_pow_left₀ hg.le hgΛ 2) (cltFar_Wpow_le sz n) (by positivity) (by positivity)
  have hA65 : STAI sz n ^ (6 / 5 : ℝ) ≤ STAI sz n ^ 2 := by
    have := Real.rpow_le_rpow_of_exponent_le hA1 (show (6 / 5 : ℝ) ≤ 2 by norm_num)
    rwa [Real.rpow_two] at this
  have hA2 : STAI sz n ^ 2 ≤ ((𝔡⁻¹) ^ 2 * ((sz.size n : ℕ) : ℝ)) ^ 2 :=
    pow_le_pow_left₀ (by linarith) hAN 2
  have hL1 := cltFar_one_le_L sz n
  have hKL : ((K : ℕ) : ℝ) ≤ ((sz.L n : ℕ) : ℝ) := by exact_mod_cast hK
  have hR : ((K : ℕ) : ℝ) ^ (d - 2) + 1 ≤ 2 * ((sz.size n : ℕ) : ℝ) := by
    have h1 : ((K : ℕ) : ℝ) ^ (d - 2) ≤ ((sz.L n : ℕ) : ℝ) ^ (d - 2) :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) hKL _
    have h2 : ((sz.L n : ℕ) : ℝ) ^ (d - 2) ≤ ((sz.L n : ℕ) : ℝ) ^ d :=
      pow_le_pow_right₀ hL1 (Nat.sub_le d 2)
    have h3 := cltFar_Lpow_le sz n
    linarith
  have hR0 : 0 ≤ ((K : ℕ) : ℝ) ^ (d - 2) + 1 := by positivity
  have hWW0 : 0 ≤ ((sz.W n : ℕ) : ℝ) ^ (-(((3 : ℕ) : ℝ) / 𝔠)) := Real.rpow_nonneg (by linarith [cltFar_one_le_W sz n]) _
  have hN3 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) ^ 3 := by positivity
  calc STAI sz n ^ (6 / 5 : ℝ) * (((K : ℕ) : ℝ) ^ (d - 2) + 1) * ((sz.W n : ℕ) : ℝ) ^ (-(((3 : ℕ) : ℝ) / 𝔠))
      ≤ ((𝔡⁻¹) ^ 2 * ((sz.size n : ℕ) : ℝ)) ^ 2 * (2 * ((sz.size n : ℕ) : ℝ)) * (((sz.size n : ℕ) : ℝ) ^ 3)⁻¹ := by
        refine mul_le_mul (mul_le_mul (hA65.trans hA2) hR hR0 (by positivity)) hW hWW0 (by positivity)
    _ = 2 * (𝔡⁻¹) ^ 4 := by field_simp

/-- **Target 1: the per-label tail `CltMom2.DomHyp`** (`(eq:propcalB)`, `3_5:2155`) from `(Eq:Gdecay_w)` at `u = s` with
`Λ' = N^τ`, `q₁ = N^{-D₁}`, eventually, every `σ`.  The event `{N^τ < |𝗕_β| (r^{d-2} + 1)}`, `𝗕 = A^{6/5}(𝓛-𝒦)^{(2)}_{s,σ,β}`, is
contained in the `≺` event `{N^{τ/2} ζ' < |(𝓛-𝒦)^{(2)}|}` of `(Eq:Gdecay_w)` (`cltFar_bad_one` at `(τ/2, D₁, D_w = 3/𝔠)`) because
`A^{6/5} R ζ' ≤ c₀ + 2𝔡^{-4} ≤ N^{τ/2}` (`cltFar_dom_key`, `cltFar_dom_tail`). -/
theorem cltFar_dom (d : ℕ) : CltFar.DomStmt d := by
  intro hd sz 𝔠 𝔡 Cd E s t hAdm hs1 hst hreg hG τ D₁ hτ hD₁
  obtain ⟨h𝔠, h𝔡, hSz, hBw, hWO⟩ := hAdm
  have hDw : (0 : ℝ) < ((3 : ℕ) : ℝ) / 𝔠 := by positivity
  have hbad := cltFar_bad_one sz hs1 hst hG hDw (τ := τ / 2) (D₁ := D₁) (half_pos hτ) hD₁
  have hev := st5_eventually_A_ge_one sz h𝔡 hWO
  have hbig : ∀ᶠ n in atTop, cltFar_c0 d + 2 * (𝔡⁻¹) ^ 4 ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) :=
    ((tendsto_rpow_atTop (half_pos hτ)).comp hSz).eventually_ge_atTop _
  filter_upwards [hbad, hev, hBw, hWO, hbig] with n hbadn hAn hBwn hWOn hbign
  obtain ⟨hg, hA1⟩ := hAn
  obtain ⟨-, hgΛ⟩ := hWOn
  intro σ β _
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := lt_of_lt_of_le one_pos (cltFar_one_le_N sz n)
  have hreg_s : sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 ≤ 1 - s n := le_trans (hreg n).1 (by linarith [hst n])
  have hrL : zdistInf d (sz.L n) (β 0 - β 1) ≤ sz.L n := st5_zdistInf_le sz n _
  have hkey := cltFar_dom_key hd sz n (hs1 n) hg hreg_s hA1 (zdistInf d (sz.L n) (β 0 - β 1)) hrL
    (((3 : ℕ) : ℝ) / 𝔠)
  have htail := cltFar_dom_tail sz n h𝔠 hA1 hg hgΛ hBwn (zdistInf d (sz.L n) (β 0 - β 1)) hrL
  set N : ℝ := ((sz.size n : ℕ) : ℝ) with hNdef
  set A : ℝ := STAI sz n with hAdef
  set R : ℝ := ((zdistInf d (sz.L n) (β 0 - β 1) : ℕ) : ℝ) ^ (d - 2) + 1 with hRdef
  set ζ' : ℝ := sz.Bctl n (s n) ^ (1 / 5 : ℝ) * STWB sz n (s n) (zdistInf d (sz.L n) (β 0 - β 1)) *
      Real.exp (-(((zdistInf d (sz.L n) (β 0 - β 1) : ℕ) : ℝ) / ellT (sz.L n) (sz.lam n) (s n)) ^ (1 / 2 : ℝ)) +
      ((sz.W n : ℕ) : ℝ) ^ (-(((3 : ℕ) : ℝ) / 𝔠)) with hζ'
  have hA0 : 0 < A := lt_of_lt_of_le one_pos hA1
  have hZ : A ^ (6 / 5 : ℝ) * R * ζ' ≤ N ^ (τ / 2) := by
    have := hkey
    linarith
  have hβ : (![β 0, β 1] : Fin 2 → Zd d (sz.L n)) = β := by
    funext i; fin_cases i <;> rfl
  have hnormB : ∀ ω, ‖STcltB sz n (E n) (s n) σ β ω‖ =
      A ^ (6 / 5 : ℝ) * ‖STLKM sz n (E n) (s n) (sz.seqHflow n (s n) ω) σ ![β 0, β 1]‖ := by
    intro ω
    have hA65 : 0 ≤ (sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d) ^ (6 / 5 : ℝ) := by positivity
    rw [hβ]
    unfold STcltB
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hA65]
    rfl
  refine le_trans (measure_mono ?_) (hbadn σ (β 0) (β 1))
  intro ω hω
  have hω' : N ^ τ < ‖STcltB sz n (E n) (s n) σ β ω‖ * R := hω
  rw [hnormB] at hω'
  change N ^ (τ / 2) * ζ' < ‖STLKM sz n (E n) (s n) (sz.seqHflow n (s n) ω) σ ![β 0, β 1]‖
  by_contra hcon0
  have hcon := not_lt.1 hcon0
  have hA65 : 0 ≤ A ^ (6 / 5 : ℝ) := Real.rpow_nonneg hA0.le _
  have hR0 : 0 ≤ R := by positivity
  have h1 : A ^ (6 / 5 : ℝ) * ‖STLKM sz n (E n) (s n) (sz.seqHflow n (s n) ω) σ ![β 0, β 1]‖ * R ≤
      A ^ (6 / 5 : ℝ) * (N ^ (τ / 2) * ζ') * R := by gcongr
  have h2 : A ^ (6 / 5 : ℝ) * (N ^ (τ / 2) * ζ') * R = N ^ (τ / 2) * (A ^ (6 / 5 : ℝ) * R * ζ') := by ring
  have h3 : N ^ (τ / 2) * (A ^ (6 / 5 : ℝ) * R * ζ') ≤ N ^ (τ / 2) * N ^ (τ / 2) :=
    mul_le_mul_of_nonneg_left hZ (Real.rpow_nonneg hN0.le _)
  have h4 : N ^ (τ / 2) * N ^ (τ / 2) = N ^ τ := by
    rw [← Real.rpow_add hN0]; congr 1; ring
  linarith

end Dom

/-! ## 5. Per-index bounds: the propagator, `𝒦`, the weights `Z`, the envelope `BY` -/

section PerN

variable {d : ℕ}

/-- `(prop:ThfadC)` (`prop5Decay_holds`) at one index `n` and energy `E`, in the shape `h5n` of `meanFar_eventually`
(`Evolution/MeanFar.lean:2058-2063`). -/
private def CltFarH5 (sz : Sizes d) (n : ℕ) (E C₅ c₅ : ℝ) : Prop :=
  ∀ u : ℝ, 0 ≤ u → u < 1 → ∀ (σ : Fin 2 → Bool) (x : Zd d (sz.L n)),
    ‖Theta d (sz.L n) (sz.lam n) ((u : ℂ) * (STmsig E (σ 0) * STmsig E (σ 1))) 0 x‖ ≤
      C₅ * Bparam d (sz.L n) (sz.lam n) u (zdistD d (sz.L n) x) *
        Real.exp (-c₅ * ((zdistD d (sz.L n) x : ℕ) : ℝ) / ellT (sz.L n) (sz.lam n) u)

private theorem cltFar_H5_at (sz : Sizes d) (n : ℕ) {𝔡 C₅ c₅ E : ℝ} (hE : |E| ≤ 2) (hg : 0 < sz.lam n)
    (hgΛ : sz.lam n ≤ 𝔡⁻¹)
    (H5 : ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → g ≤ 𝔡⁻¹ → ∀ t : ℝ, 0 ≤ t → t < 1 → ∀ m : ℂ, ‖m‖ = 1 →
      ∀ σ₁ σ₂ : Bool, ∀ a : Zd d L,
        haveI : NeZero L := ⟨by omega⟩
        ‖Theta d L g ((t : ℂ) * (PropSpin m σ₁ * PropSpin m σ₂)) 0 a‖ ≤ C₅ * Bparam d L g t (zdistD d L a) *
          Real.exp (-c₅ * (zdistD d L a : ℝ) / ellT L g t)) :
    CltFarH5 sz n E C₅ c₅ := by
  intro u hu0 hu1 σ x
  exact H5 (sz.L n) (sz.three_le_L n) (sz.lam n) hg hgΛ u hu0 hu1 (mE E) (norm_mE hE) (σ 0) (σ 1) x

/-- `|Θ_u(x,y)| ≤ c_Θ / g²`, `c_Θ = C₅ (1 + 2^{d-1})`, at one index. -/
private theorem cltFar_Theta_all (hd : 3 ≤ d) (sz : Sizes d) (n : ℕ) {E u C₅ c₅ : ℝ} (hE : |E| < 2) (hu0 : 0 ≤ u)
    (hu1 : u < 1) (hg : 0 < sz.lam n) (hreg : sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 ≤ 1 - u) (hC₅ : 0 ≤ C₅)
    (hc₅ : 0 < c₅) (h5 : CltFarH5 sz n E C₅ c₅) (σ : Fin 2 → Bool) (x y : Zd d (sz.L n)) :
    ‖Theta d (sz.L n) (sz.lam n) ((u : ℂ) * (STmsig E (σ 0) * STmsig E (σ 1))) x y‖ ≤
      C₅ * (1 + 2 ^ (d - 1)) / sz.lam n ^ 2 := by
  have hL := sz.three_le_L n
  have hξ : ‖(u : ℂ) * (STmsig E (σ 0) * STmsig E (σ 1))‖ < 1 :=
    norm_mul_mSigma_lt_one hE.le hu0 hu1 (σ 0) (σ 1)
  exact cltFar_Theta_sup hd hL hξ hg hu1 hreg hC₅ hc₅ (fun x => h5 u hu0 hu1 σ x) x y

/-- `|𝒦^{(2)}_{s,σ,(a,b)}| ≤ W^{-d} c_Θ / g²` (`cltFar_n_K`). -/
private theorem cltFar_K_le (hd : 3 ≤ d) (sz : Sizes d) (n : ℕ) {E s C₅ c₅ : ℝ} (hE : |E| < 2) (hs0 : 0 ≤ s)
    (hs : s < 1) (hg : 0 < sz.lam n) (hreg : sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 ≤ 1 - s) (hC₅ : 0 ≤ C₅)
    (hc₅ : 0 < c₅) (h5 : CltFarH5 sz n E C₅ c₅) (σ : Fin 2 → Bool) (a b : Zd d (sz.L n)) :
    ‖STKloop sz n E s σ ![a, b]‖ ≤ (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (C₅ * (1 + 2 ^ (d - 1)) / sz.lam n ^ 2) :=
  cltFar_n_K sz n hE hs0 hs σ a b (fun x => cltFar_Theta_all hd sz n hE hs0 hs hg hreg hC₅ hc₅ h5 σ 0 x)

/-- `W^{-d} c_Θ / g² = c_Θ / A ≤ c_Θ` for `A ≥ 1`. -/
private theorem cltFar_K_le' (sz : Sizes d) (n : ℕ) {cΘ : ℝ} (hcΘ : 0 ≤ cΘ) (hg : 0 < sz.lam n) (hA1 : 1 ≤ STAI sz n) :
    (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (cΘ / sz.lam n ^ 2) ≤ cΘ := by
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) ^ d := by
    have := cltFar_one_le_W sz n
    positivity
  have hg2 : 0 < sz.lam n ^ 2 := by positivity
  have hA : STAI sz n = sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d := rfl
  have : (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (cΘ / sz.lam n ^ 2) = cΘ / STAI sz n := by
    rw [hA]; field_simp
  rw [this]
  exact div_le_self hcΘ hA1

/-- `|Z_β| ≤ 2 c_Θ²` for every `β` (`g² |Θ| ≤ c_Θ`). -/
private theorem cltFar_Z_le (hd : 3 ≤ d) (sz : Sizes d) (n : ℕ) {E s t C₅ c₅ : ℝ} (hE : |E| < 2) (ht0 : 0 ≤ t)
    (ht : t < 1) (hg : 0 < sz.lam n) (hreg : sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 ≤ 1 - t) (hC₅ : 0 ≤ C₅)
    (hc₅ : 0 < c₅) (h5 : CltFarH5 sz n E C₅ c₅) (σ : Fin 2 → Bool) (a β : Fin 2 → Zd d (sz.L n)) :
    ‖CltMom2.Z sz n E s t σ a β‖ ≤ 2 * (C₅ * (1 + 2 ^ (d - 1))) ^ 2 := by
  have hT := cltFar_Theta_all hd sz n hE ht0 ht hg hreg hC₅ hc₅ h5 σ
  set cΘ : ℝ := C₅ * (1 + 2 ^ (d - 1)) with hcΘ
  have hcΘ0 : 0 ≤ cΘ := by positivity
  have hg2 : 0 < sz.lam n ^ 2 := by positivity
  have hg2T : ∀ x y, sz.lam n ^ 2 * ‖Theta d (sz.L n) (sz.lam n) ((t : ℂ) * (STmsig E (σ 0) * STmsig E (σ 1))) x y‖ ≤ cΘ := by
    intro x y
    calc sz.lam n ^ 2 * ‖Theta d (sz.L n) (sz.lam n) ((t : ℂ) * (STmsig E (σ 0) * STmsig E (σ 1))) x y‖
        ≤ sz.lam n ^ 2 * (cΘ / sz.lam n ^ 2) := mul_le_mul_of_nonneg_left (hT x y) hg2.le
      _ = cΘ := by field_simp
  unfold CltMom2.Z
  split_ifs
  · rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hg2.le]
    have h1 := hg2T (a 0) (β 0)
    have h2 : sz.lam n ^ 2 * ‖Theta d (sz.L n) (sz.lam n) ((t : ℂ) * (STmsig E (σ 0) * STmsig E (σ 1))) (β 1) (a 1) -
        Theta d (sz.L n) (sz.lam n) ((t : ℂ) * (STmsig E (σ 0) * STmsig E (σ 1))) (β 0) (a 1)‖ ≤ 2 * cΘ := by
      calc _ ≤ sz.lam n ^ 2 * (‖Theta d (sz.L n) (sz.lam n) ((t : ℂ) * (STmsig E (σ 0) * STmsig E (σ 1))) (β 1) (a 1)‖ +
            ‖Theta d (sz.L n) (sz.lam n) ((t : ℂ) * (STmsig E (σ 0) * STmsig E (σ 1))) (β 0) (a 1)‖) :=
            mul_le_mul_of_nonneg_left (norm_sub_le _ _) hg2.le
        _ = sz.lam n ^ 2 * ‖Theta d (sz.L n) (sz.lam n) ((t : ℂ) * (STmsig E (σ 0) * STmsig E (σ 1))) (β 1) (a 1)‖ +
            sz.lam n ^ 2 * ‖Theta d (sz.L n) (sz.lam n) ((t : ℂ) * (STmsig E (σ 0) * STmsig E (σ 1))) (β 0) (a 1)‖ := by ring
        _ ≤ cΘ + cΘ := add_le_add (hg2T _ _) (hg2T _ _)
        _ = 2 * cΘ := by ring
    calc sz.lam n ^ 2 * ‖Theta d (sz.L n) (sz.lam n) ((t : ℂ) * (STmsig E (σ 0) * STmsig E (σ 1))) (a 0) (β 0)‖ *
        (sz.lam n ^ 2 * ‖Theta d (sz.L n) (sz.lam n) ((t : ℂ) * (STmsig E (σ 0) * STmsig E (σ 1))) (β 1) (a 1) -
        Theta d (sz.L n) (sz.lam n) ((t : ℂ) * (STmsig E (σ 0) * STmsig E (σ 1))) (β 0) (a 1)‖)
        ≤ cΘ * (2 * cΘ) := mul_le_mul h1 h2 (by positivity) hcΘ0
      _ = 2 * cΘ ^ 2 := by ring
  · rw [norm_zero]; positivity

/-- `Σ_β |Z_β| ≤ N² · 2 c_Θ²`. -/
private theorem cltFar_ZZ_le (hd : 3 ≤ d) (sz : Sizes d) (n : ℕ) {E s t C₅ c₅ : ℝ} (hE : |E| < 2) (ht0 : 0 ≤ t)
    (ht : t < 1) (hg : 0 < sz.lam n) (hreg : sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 ≤ 1 - t) (hC₅ : 0 ≤ C₅)
    (hc₅ : 0 < c₅) (h5 : CltFarH5 sz n E C₅ c₅) (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) :
    ∑ β : Fin 2 → Zd d (sz.L n), ‖CltMom2.Z sz n E s t σ a β‖ ≤
      ((sz.size n : ℕ) : ℝ) ^ 2 * (2 * (C₅ * (1 + 2 ^ (d - 1))) ^ 2) := by
  have h := Finset.sum_le_card_nsmul Finset.univ (fun β : Fin 2 → Zd d (sz.L n) => ‖CltMom2.Z sz n E s t σ a β‖)
    (2 * (C₅ * (1 + 2 ^ (d - 1))) ^ 2) (fun β _ => cltFar_Z_le hd sz n hE ht0 ht hg hreg hC₅ hc₅ h5 σ a β)
  rw [Finset.card_univ, nsmul_eq_mul] at h
  refine h.trans ?_
  exact mul_le_mul_of_nonneg_right (cltFar_card_pair_le sz n) (by positivity)

/-- `(lw³ ℓ_s)^{d-2} + 1 ≤ 2 N²` once `lw^{3(d-2)} ≤ N` (`ℓ_s ≤ L`, `L^d ≤ N`). -/
private theorem cltFar_wpow_le (sz : Sizes d) (n : ℕ) {s : ℝ}
    (hlwN : Real.log ((sz.W n : ℕ) : ℝ) ^ (3 * (d - 2)) ≤ ((sz.size n : ℕ) : ℝ)) :
    (Real.log ((sz.W n : ℕ) : ℝ) ^ 3 * ellT (sz.L n) (sz.lam n) s) ^ (d - 2) + 1 ≤
      2 * ((sz.size n : ℕ) : ℝ) ^ 2 := by
  have hℓ1 : 1 ≤ ellT (sz.L n) (sz.lam n) s := one_le_ellT (cltFar_one_le_L sz n)
  have hℓL : ellT (sz.L n) (sz.lam n) s ≤ ((sz.L n : ℕ) : ℝ) := ellT_le_L
  have h1 : (Real.log ((sz.W n : ℕ) : ℝ) ^ 3 * ellT (sz.L n) (sz.lam n) s) ^ (d - 2) =
      Real.log ((sz.W n : ℕ) : ℝ) ^ (3 * (d - 2)) * ellT (sz.L n) (sz.lam n) s ^ (d - 2) := by
    rw [mul_pow, ← pow_mul]
  have h2 : ellT (sz.L n) (sz.lam n) s ^ (d - 2) ≤ ((sz.L n : ℕ) : ℝ) ^ (d - 2) :=
    pow_le_pow_left₀ (by linarith) hℓL _
  have h3 : ((sz.L n : ℕ) : ℝ) ^ (d - 2) ≤ ((sz.L n : ℕ) : ℝ) ^ d :=
    pow_le_pow_right₀ (cltFar_one_le_L sz n) (Nat.sub_le d 2)
  have h4 := cltFar_Lpow_le sz n
  have hN1 := cltFar_one_le_N sz n
  have h6 : 0 ≤ ellT (sz.L n) (sz.lam n) s ^ (d - 2) := by positivity
  have h5 : Real.log ((sz.W n : ℕ) : ℝ) ^ (3 * (d - 2)) * ellT (sz.L n) (sz.lam n) s ^ (d - 2) ≤
      ((sz.size n : ℕ) : ℝ) * ((sz.size n : ℕ) : ℝ) :=
    mul_le_mul hlwN (h2.trans (h3.trans h4)) h6 (by linarith)
  rw [h1]
  nlinarith

/-- `1/N² ≤ 1 - s` for `g²/L² ≤ 1 - t ≤ 1 - s` and `A ≥ 1` (`g² ≥ W^{-d} ≥ N^{-1}`, `L² ≤ N`). -/
private theorem cltFar_one_sub_ge (sz : Sizes d) (n : ℕ) {s t : ℝ} (hd2 : 2 ≤ d) (hst : s ≤ t)
    (hreg : sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 ≤ 1 - t) (hA1 : 1 ≤ STAI sz n) :
    1 / ((sz.size n : ℕ) : ℝ) ^ 2 ≤ 1 - s := by
  have hN1 := cltFar_one_le_N sz n
  have hL1 := cltFar_one_le_L sz n
  have hLsq : ((sz.L n : ℕ) : ℝ) ^ 2 ≤ ((sz.size n : ℕ) : ℝ) :=
    (pow_le_pow_right₀ hL1 hd2).trans (cltFar_Lpow_le sz n)
  have hWN := cltFar_Wpow_le sz n
  have hg2N : 1 ≤ sz.lam n ^ 2 * ((sz.size n : ℕ) : ℝ) := by
    have : sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d ≤ sz.lam n ^ 2 * ((sz.size n : ℕ) : ℝ) :=
      mul_le_mul_of_nonneg_left hWN (by positivity)
    have hA : STAI sz n = sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d := rfl
    linarith
  have hL0 : 0 < ((sz.L n : ℕ) : ℝ) ^ 2 := by positivity
  have h1 : 1 / ((sz.size n : ℕ) : ℝ) ^ 2 ≤ sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 := by
    rw [div_le_div_iff₀ (by positivity) hL0]
    nlinarith
  linarith

/-- `η_s^{-2} ≤ N⁴/κ'²` (`1 - s ≥ N^{-2}`, `Im m(E) ≥ κ'`). -/
private theorem cltFar_eta_inv_le (sz : Sizes d) (n : ℕ) {E s t κ' : ℝ} (hd2 : 2 ≤ d) (hκ' : κ' ≤ (mE E).im)
    (hκ'0 : 0 < κ') (hst : s ≤ t) (hreg : sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 ≤ 1 - t)
    (hA1 : 1 ≤ STAI sz n) : (etaT E s)⁻¹ ^ 2 ≤ ((sz.size n : ℕ) : ℝ) ^ 4 / κ' ^ 2 := by
  have hN1 := cltFar_one_le_N sz n
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
  have h1s := cltFar_one_sub_ge sz n hd2 hst hreg hA1
  have hη : κ' * (1 / ((sz.size n : ℕ) : ℝ) ^ 2) ≤ etaT E s := by
    unfold etaT
    exact mul_le_mul hκ' h1s (by positivity) (hκ'0.le.trans hκ')  |>.trans_eq (by ring)
  have hη0 : 0 < κ' * (1 / ((sz.size n : ℕ) : ℝ) ^ 2) := by positivity
  have h1 : (etaT E s)⁻¹ ≤ (κ' * (1 / ((sz.size n : ℕ) : ℝ) ^ 2))⁻¹ := inv_anti₀ hη0 hη
  have h2 : (etaT E s)⁻¹ ^ 2 ≤ ((κ' * (1 / ((sz.size n : ℕ) : ℝ) ^ 2))⁻¹) ^ 2 :=
    pow_le_pow_left₀ (inv_nonneg.2 (hη0.le.trans hη)) h1 2
  refine h2.trans (le_of_eq ?_)
  field_simp

/-- **The envelope** `BY ≤ 𝔡^{-4} (κ'^{-2} + c_Θ) N⁶`: `A^{6/5} ≤ A² ≤ 𝔡^{-4}N²`, `η_s^{-2} ≤ N⁴/κ'²`
(`1 - s ≥ N^{-2}`, `Im m(E) ≥ κ'`), `Σ_β |𝒦_β| ≤ N² c_Θ` (`cltFar_K_le`, `cltFar_K_le'`). -/
private theorem cltFar_BY_le (hd : 3 ≤ d) (sz : Sizes d) (n : ℕ) {E s t C₅ c₅ κ' 𝔡 : ℝ} (σ : Fin 2 → Bool)
    (hE : |E| < 2) (hκ' : κ' ≤ (mE E).im) (hκ'0 : 0 < κ') (hs0 : 0 ≤ s) (hst : s ≤ t) (ht : t < 1)
    (hg : 0 < sz.lam n) (hgΛ : sz.lam n ≤ 𝔡⁻¹) (hreg : sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 ≤ 1 - t)
    (hA1 : 1 ≤ STAI sz n) (hC₅ : 0 ≤ C₅) (hc₅ : 0 < c₅) (h5 : CltFarH5 sz n E C₅ c₅) :
    CltMom2.BY sz n E s σ ≤ 𝔡⁻¹ ^ 4 * (1 / κ' ^ 2 + C₅ * (1 + 2 ^ (d - 1))) * ((sz.size n : ℕ) : ℝ) ^ 6 := by
  have hs : s < 1 := lt_of_le_of_lt hst ht
  have hN1 := cltFar_one_le_N sz n
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
  have hcΘ0 : 0 ≤ C₅ * (1 + 2 ^ (d - 1)) := by positivity
  have hreg_s : sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 ≤ 1 - s := le_trans hreg (by linarith)
  have hA0 : 0 < STAI sz n := lt_of_lt_of_le one_pos hA1
  have hAN : STAI sz n ≤ (𝔡⁻¹) ^ 2 * ((sz.size n : ℕ) : ℝ) := by
    unfold STAI
    exact mul_le_mul (pow_le_pow_left₀ hg.le hgΛ 2) (cltFar_Wpow_le sz n) (by positivity) (by positivity)
  have hA65 : STAI sz n ^ (6 / 5 : ℝ) ≤ 𝔡⁻¹ ^ 4 * ((sz.size n : ℕ) : ℝ) ^ 2 := by
    have h1 := Real.rpow_le_rpow_of_exponent_le hA1 (show (6 / 5 : ℝ) ≤ 2 by norm_num)
    rw [Real.rpow_two] at h1
    have h2 : STAI sz n ^ 2 ≤ ((𝔡⁻¹) ^ 2 * ((sz.size n : ℕ) : ℝ)) ^ 2 := pow_le_pow_left₀ hA0.le hAN 2
    calc STAI sz n ^ (6 / 5 : ℝ) ≤ ((𝔡⁻¹) ^ 2 * ((sz.size n : ℕ) : ℝ)) ^ 2 := h1.trans h2
      _ = 𝔡⁻¹ ^ 4 * ((sz.size n : ℕ) : ℝ) ^ 2 := by ring
  have hηinv := cltFar_eta_inv_le sz n (by omega) hκ' hκ'0 hst hreg hA1
  -- `Σ_β |𝒦_β| ≤ N² c_Θ`
  have hKβ : ∀ β : Fin 2 → Zd d (sz.L n), ‖STKloop sz n E s σ β‖ ≤ C₅ * (1 + 2 ^ (d - 1)) := by
    intro β
    have hβ : (![β 0, β 1] : Fin 2 → Zd d (sz.L n)) = β := by funext i; fin_cases i <;> rfl
    have := cltFar_K_le hd sz n hE hs0 hs hg hreg_s hC₅ hc₅ h5 σ (β 0) (β 1)
    rw [hβ] at this
    exact this.trans (cltFar_K_le' sz n hcΘ0 hg hA1)
  have hKsum : ∑ β : Fin 2 → Zd d (sz.L n), ‖STKloop sz n E s σ β‖ ≤
      ((sz.size n : ℕ) : ℝ) ^ 2 * (C₅ * (1 + 2 ^ (d - 1))) := by
    have h := Finset.sum_le_card_nsmul Finset.univ (fun β : Fin 2 → Zd d (sz.L n) => ‖STKloop sz n E s σ β‖)
      (C₅ * (1 + 2 ^ (d - 1))) (fun β _ => hKβ β)
    rw [Finset.card_univ, nsmul_eq_mul] at h
    exact h.trans (mul_le_mul_of_nonneg_right (cltFar_card_pair_le sz n) hcΘ0)
  unfold CltMom2.BY
  have hsum0 : 0 ≤ (etaT E s)⁻¹ ^ 2 + ∑ β : Fin 2 → Zd d (sz.L n), ‖STKloop sz n E s σ β‖ := by positivity
  calc STAI sz n ^ (6 / 5 : ℝ) * ((etaT E s)⁻¹ ^ 2 + ∑ β : Fin 2 → Zd d (sz.L n), ‖STKloop sz n E s σ β‖)
      ≤ (𝔡⁻¹ ^ 4 * ((sz.size n : ℕ) : ℝ) ^ 2) *
          (((sz.size n : ℕ) : ℝ) ^ 4 / κ' ^ 2 + ((sz.size n : ℕ) : ℝ) ^ 2 * (C₅ * (1 + 2 ^ (d - 1)))) :=
        mul_le_mul hA65 (add_le_add hηinv hKsum) hsum0 (by positivity)
    _ ≤ 𝔡⁻¹ ^ 4 * (1 / κ' ^ 2 + C₅ * (1 + 2 ^ (d - 1))) * ((sz.size n : ℕ) : ℝ) ^ 6 := by
        have hN24 : ((sz.size n : ℕ) : ℝ) ^ 4 ≤ ((sz.size n : ℕ) : ℝ) ^ 6 := pow_le_pow_right₀ hN1 (by norm_num)
        have hd4 : 0 ≤ 𝔡⁻¹ ^ 4 := by positivity
        have e : (𝔡⁻¹ ^ 4 * ((sz.size n : ℕ) : ℝ) ^ 2) *
            (((sz.size n : ℕ) : ℝ) ^ 4 / κ' ^ 2 + ((sz.size n : ℕ) : ℝ) ^ 2 * (C₅ * (1 + 2 ^ (d - 1)))) =
            𝔡⁻¹ ^ 4 * (((sz.size n : ℕ) : ℝ) ^ 6 / κ' ^ 2 + ((sz.size n : ℕ) : ℝ) ^ 4 * (C₅ * (1 + 2 ^ (d - 1)))) := by
          field_simp
        rw [e]
        have e2 : 𝔡⁻¹ ^ 4 * (1 / κ' ^ 2 + C₅ * (1 + 2 ^ (d - 1))) * ((sz.size n : ℕ) : ℝ) ^ 6 =
            𝔡⁻¹ ^ 4 * (((sz.size n : ℕ) : ℝ) ^ 6 / κ' ^ 2 + ((sz.size n : ℕ) : ℝ) ^ 6 * (C₅ * (1 + 2 ^ (d - 1)))) := by
          field_simp
        rw [e2]
        exact mul_le_mul_of_nonneg_left (add_le_add le_rfl (mul_le_mul_of_nonneg_right hN24 hcΘ0)) hd4

end PerN

/-! ## 6. Target 2: the off-window part `CltMom2.off` -/

section Off

variable {d : ℕ}

/-- A double sum over two filtered index sets is at most `#ι² M` when every summand of the second filter is at most `M`. -/
private theorem cltFar_double_sum_le {ι : Type*} [Fintype ι] (p₁ : ι → Prop) (p₂ : ι → ι → Prop)
    [DecidablePred p₁] [∀ b, DecidablePred (p₂ b)] (T : ι → ι → ℂ) {M : ℝ} (hM : 0 ≤ M)
    (hT : ∀ b₁ b₂, p₂ b₁ b₂ → ‖T b₁ b₂‖ ≤ M) :
    ‖∑ b₁ ∈ Finset.univ.filter p₁, ∑ b₂ ∈ Finset.univ.filter (p₂ b₁), T b₁ b₂‖ ≤
      (Fintype.card ι : ℝ) * ((Fintype.card ι : ℝ) * M) := by
  have hcard : ∀ (q : ι → Prop) [DecidablePred q], ((Finset.univ.filter q).card : ℝ) ≤ (Fintype.card ι : ℝ) := by
    intro q _
    have := Finset.card_filter_le (Finset.univ : Finset ι) q
    rw [Finset.card_univ] at this
    exact_mod_cast this
  refine (norm_sum_le _ _).trans ?_
  have h1 : ∀ b₁ ∈ Finset.univ.filter p₁, ‖∑ b₂ ∈ Finset.univ.filter (p₂ b₁), T b₁ b₂‖ ≤
      (Fintype.card ι : ℝ) * M := by
    intro b₁ _
    refine (norm_sum_le _ _).trans ?_
    have h := Finset.sum_le_card_nsmul (Finset.univ.filter (p₂ b₁)) (fun b₂ => ‖T b₁ b₂‖) M
      (fun b₂ hb₂ => hT b₁ b₂ (Finset.mem_filter.1 hb₂).2)
    rw [nsmul_eq_mul] at h
    exact h.trans (mul_le_mul_of_nonneg_right (hcard _) hM)
  have h2 := Finset.sum_le_card_nsmul (Finset.univ.filter p₁)
    (fun b₁ => ‖∑ b₂ ∈ Finset.univ.filter (p₂ b₁), T b₁ b₂‖) ((Fintype.card ι : ℝ) * M) h1
  rw [nsmul_eq_mul] at h2
  exact h2.trans (mul_le_mul_of_nonneg_right (hcard _) (by positivity))

/-- **The sum bound for `CltMom2.off`**: `|off| ≤ (1-s)² (L^d)² K_Θ X (2 K_Θ)` when `|Θ_t| ≤ K_Θ` and every off-window
`|𝓑 - 𝔼𝓑|` is at most `X`. -/
private theorem cltFar_off_sum_le (sz : Sizes d) (n : ℕ) {E s t : ℝ} (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n))
    (ω : sz.SeqΩ) {KΘ Xb : ℝ} (hKΘ : 0 ≤ KΘ) (hXb : 0 ≤ Xb)
    (hΘ : ∀ x y : Zd d (sz.L n),
      ‖Theta d (sz.L n) (sz.lam n) ((t : ℂ) * (STmsig E (σ 0) * STmsig E (σ 1))) x y‖ ≤ KΘ)
    (hX : ∀ b₁ b₂ : Zd d (sz.L n),
      Real.log ((sz.W n : ℕ) : ℝ) ^ 3 * ellT (sz.L n) (sz.lam n) s < ((zdistInf d (sz.L n) (b₁ - b₂) : ℕ) : ℝ) →
      ‖STLKM sz n E s (sz.seqHflow n s ω) σ ![b₁, b₂] -
        ∫ ω', STLKM sz n E s (sz.seqHflow n s ω') σ ![b₁, b₂] ∂(sz.seqP)‖ ≤ Xb) :
    ‖CltMom2.off sz n E s t σ a ω‖ ≤
      (1 - s) ^ 2 * (((sz.L n : ℕ) : ℝ) ^ d * (((sz.L n : ℕ) : ℝ) ^ d * (KΘ * Xb * (KΘ + KΘ)))) := by
  unfold CltMom2.off
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (sq_nonneg _)]
  refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
  have hM : 0 ≤ KΘ * Xb * (KΘ + KΘ) := by positivity
  refine (cltFar_double_sum_le (M := KΘ * Xb * (KΘ + KΘ)) _ _ _ hM ?_).trans ?_
  · intro b₁ b₂ hb
    rw [norm_mul, norm_mul]
    refine mul_le_mul (mul_le_mul (hΘ _ _) (hX b₁ b₂ hb) (norm_nonneg _) hKΘ) ?_ (norm_nonneg _) (by positivity)
    exact (norm_sub_le _ _).trans (add_le_add (hΘ _ _) (hΘ _ _))
  · rw [cltFar_card_Zd]
    push_cast
    exact le_rfl

/-- **The off-window profile**: for `K > (log W)³ ℓ_s`, `K ≤ L`, `D_w > 0`, `D_w² ≤ log W`:
`ζ'_s(K) ≤ (c₀ + 1) W^{-D_w}`: `e^{-(K/ℓ_s)^{1/2}} ≤ e^{-(log W)^{3/2}} ≤ e^{-D_w log W} = W^{-D_w}` (`D_w log W ≤ (log W)^{3/2}`),
`(W^{-d}B_{s,0})^{1/5}(W^{-d}B_{s,K}) ≤ c₀` (`A ≥ 1`) (`(eq:propcalB)`, `3_5:2155`). -/
private theorem cltFar_zeta_off (hd : 3 ≤ d) (sz : Sizes d) (n : ℕ) {s Dw : ℝ} (hs : s < 1) (hg : 0 < sz.lam n)
    (hreg : sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 ≤ 1 - s) (hA1 : 1 ≤ STAI sz n) (hDw : 0 < Dw)
    (hlwD : Dw ^ 2 ≤ Real.log ((sz.W n : ℕ) : ℝ)) (K : ℕ) (hK : K ≤ sz.L n)
    (hoff : Real.log ((sz.W n : ℕ) : ℝ) ^ 3 * ellT (sz.L n) (sz.lam n) s < (K : ℝ)) :
    cltFarZ sz n s Dw K ≤ (cltFar_c0 d + 1) * ((sz.W n : ℕ) : ℝ) ^ (-Dw) := by
  unfold cltFarZ
  have hW0 : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by linarith [cltFar_one_le_W sz n]
  have hA0 : 0 < STAI sz n := lt_of_lt_of_le one_pos hA1
  have hBW := cltFar_BctlSTWB sz n hd hs hg hreg K hK
  have hA65 : STAI sz n ^ (-(6 / 5 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hA1 (by norm_num)
  have hY1 : (1 : ℝ) ≤ (((K : ℕ) : ℝ) + 1) ^ (d - 2) :=
    one_le_pow₀ (by have : (0 : ℝ) ≤ ((K : ℕ) : ℝ) := Nat.cast_nonneg _; linarith)
  have hc0 : 0 < cltFar_c0 d := by
    unfold cltFar_c0
    have := cltFar_c3_pos d
    positivity
  have hP : sz.Bctl n s ^ (1 / 5 : ℝ) * STWB sz n s K ≤ cltFar_c0 d := by
    refine hBW.trans ?_
    rw [div_le_iff₀ (by positivity)]
    calc cltFar_c0 d * STAI sz n ^ (-(6 / 5 : ℝ)) ≤ cltFar_c0 d * 1 := mul_le_mul_of_nonneg_left hA65 hc0.le
      _ = cltFar_c0 d := mul_one _
      _ ≤ cltFar_c0 d * (((K : ℕ) : ℝ) + 1) ^ (d - 2) := le_mul_of_one_le_right hc0.le hY1
  have hℓ0 : 0 < ellT (sz.L n) (sz.lam n) s := ellT_pos (cltFar_one_le_L sz n)
  have hlw0 : 0 ≤ Real.log ((sz.W n : ℕ) : ℝ) := le_trans (by positivity) hlwD
  have hxℓ : Real.log ((sz.W n : ℕ) : ℝ) ^ 3 ≤ ((K : ℕ) : ℝ) / ellT (sz.L n) (sz.lam n) s := by
    rw [le_div_iff₀ hℓ0]; exact hoff.le
  have hpow : Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ) ≤
      (((K : ℕ) : ℝ) / ellT (sz.L n) (sz.lam n) s) ^ (1 / 2 : ℝ) := by
    have h1 : (Real.log ((sz.W n : ℕ) : ℝ) ^ 3) ^ (1 / 2 : ℝ) ≤
        (((K : ℕ) : ℝ) / ellT (sz.L n) (sz.lam n) s) ^ (1 / 2 : ℝ) :=
      Real.rpow_le_rpow (pow_nonneg hlw0 3) hxℓ (by norm_num)
    have h2 : (Real.log ((sz.W n : ℕ) : ℝ) ^ 3) ^ (1 / 2 : ℝ) = Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hlw0]; norm_num
    rwa [h2] at h1
  have hexp : Real.exp (-(((K : ℕ) : ℝ) / ellT (sz.L n) (sz.lam n) s) ^ (1 / 2 : ℝ)) ≤
      ((sz.W n : ℕ) : ℝ) ^ (-Dw) := by
    refine (Real.exp_le_exp.2 (neg_le_neg hpow)).trans ?_
    have h3 := cltFar_three_halves hDw hlwD
    rw [Real.rpow_def_of_pos hW0,
      show Real.log ((sz.W n : ℕ) : ℝ) * (-Dw) = -(Dw * Real.log ((sz.W n : ℕ) : ℝ)) by ring]
    exact Real.exp_le_exp.2 (neg_le_neg h3)
  calc sz.Bctl n s ^ (1 / 5 : ℝ) * STWB sz n s K *
        Real.exp (-(((K : ℕ) : ℝ) / ellT (sz.L n) (sz.lam n) s) ^ (1 / 2 : ℝ)) + ((sz.W n : ℕ) : ℝ) ^ (-Dw)
      ≤ cltFar_c0 d * ((sz.W n : ℕ) : ℝ) ^ (-Dw) + ((sz.W n : ℕ) : ℝ) ^ (-Dw) :=
        add_le_add (mul_le_mul hP hexp (Real.exp_pos _).le hc0.le) le_rfl
    _ = (cltFar_c0 d + 1) * ((sz.W n : ℕ) : ℝ) ^ (-Dw) := by ring

/-- The numerics of target 2, in `W`-exponents: with `N³ ≤ W^a`, `N⁶ ≤ W^b` (`N ≤ W^{1/𝔠}`), `D_w = D + a + 1`, `D₁ = D + b + 2` and
`2 c_Θ² (2(c₀+1) + κ'^{-2} + c_Θ) ≤ W`:
`2 c_Θ² N² (2 N (c₀+1) W^{-D_w} + (N⁴/κ'² + c_Θ) N^{-D₁}) ≤ W^{-D}`. -/
private theorem cltFar_off_numeric {N W D a b cΘ c₀ κ' : ℝ} (hW1 : 1 ≤ W) (hWN : W ≤ N) (hD : 0 ≤ D) (hb : 0 ≤ b)
    (hQ3 : N ^ 3 ≤ W ^ a) (hQ6 : N ^ 6 ≤ W ^ b)
    (hcΘ : 0 ≤ cΘ) (hc₀ : 0 ≤ c₀) (hκ' : 0 < κ')
    (hbig : 2 * cΘ ^ 2 * (2 * (c₀ + 1) + 1 / κ' ^ 2 + cΘ) ≤ W) :
    2 * cΘ ^ 2 * N ^ 2 * (2 * (N * ((c₀ + 1) * W ^ (-(D + a + 1)))) +
      (N ^ 4 / κ' ^ 2 + cΘ) * N ^ (-(D + b + 2))) ≤ W ^ (-D) := by
  have hW0 : 0 < W := by linarith
  have hN1 : 1 ≤ N := by linarith
  have hN0 : 0 < N := by linarith
  set x : ℝ := W ^ (-D) with hx
  have hx0 : 0 < x := Real.rpow_pos_of_pos hW0 _
  set y : ℝ := W⁻¹ with hy
  have hy0 : 0 < y := inv_pos.2 hW0
  have hy1 : y ≤ 1 := inv_le_one_of_one_le₀ hW1
  have hWy : W * y = 1 := mul_inv_cancel₀ hW0.ne'
  -- (1) `W^{-(D+a+1)} N³ ≤ x y`
  have h1 : W ^ (-(D + a + 1)) * N ^ 3 ≤ x * y := by
    calc W ^ (-(D + a + 1)) * N ^ 3 ≤ W ^ (-(D + a + 1)) * W ^ a :=
          mul_le_mul_of_nonneg_left hQ3 (Real.rpow_nonneg hW0.le _)
      _ = W ^ (-(D + a + 1) + a) := (Real.rpow_add hW0 _ _).symm
      _ = W ^ (-D + (-1 : ℝ)) := by congr 1; ring
      _ = x * y := by rw [Real.rpow_add hW0, Real.rpow_neg_one]
  -- (2) `N^{-(D+b+2)} N⁶ ≤ x y²`
  have h2 : N ^ (-(D + b + 2)) * N ^ 6 ≤ x * y ^ 2 := by
    have hle : N ^ (-(D + b + 2)) ≤ W ^ (-(D + b + 2)) :=
      Real.rpow_le_rpow_of_nonpos hW0 hWN (by linarith)
    calc N ^ (-(D + b + 2)) * N ^ 6 ≤ W ^ (-(D + b + 2)) * W ^ b :=
          mul_le_mul hle hQ6 (by positivity) (Real.rpow_nonneg hW0.le _)
      _ = W ^ (-(D + b + 2) + b) := (Real.rpow_add hW0 _ _).symm
      _ = W ^ (-D + (-2 : ℝ)) := by congr 1; ring
      _ = x * y ^ 2 := by
          rw [Real.rpow_add hW0, hy, inv_pow]
          congr 1
          rw [show (-2 : ℝ) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg hW0.le, Real.rpow_natCast]
  have hN2 : N ^ 2 ≤ N ^ 6 := pow_le_pow_right₀ hN1 (by norm_num)
  have hq0 : 0 ≤ N ^ (-(D + b + 2)) := Real.rpow_nonneg hN0.le _
  have h3 : N ^ 2 * N ^ (-(D + b + 2)) ≤ x * y ^ 2 :=
    calc N ^ 2 * N ^ (-(D + b + 2)) ≤ N ^ 6 * N ^ (-(D + b + 2)) := mul_le_mul_of_nonneg_right hN2 hq0
      _ = N ^ (-(D + b + 2)) * N ^ 6 := mul_comm _ _
      _ ≤ x * y ^ 2 := h2
  have hexp : 2 * cΘ ^ 2 * N ^ 2 * (2 * (N * ((c₀ + 1) * W ^ (-(D + a + 1)))) +
      (N ^ 4 / κ' ^ 2 + cΘ) * N ^ (-(D + b + 2))) =
      2 * cΘ ^ 2 * (2 * (c₀ + 1) * (W ^ (-(D + a + 1)) * N ^ 3) +
        1 / κ' ^ 2 * (N ^ (-(D + b + 2)) * N ^ 6) + cΘ * (N ^ 2 * N ^ (-(D + b + 2)))) := by
    field_simp
    ring
  rw [hexp]
  have hκ2 : 0 < κ' ^ 2 := by positivity
  have hcc : 0 ≤ 2 * cΘ ^ 2 := by positivity
  have h4 : 2 * cΘ ^ 2 * (2 * (c₀ + 1) * (W ^ (-(D + a + 1)) * N ^ 3) +
        1 / κ' ^ 2 * (N ^ (-(D + b + 2)) * N ^ 6) + cΘ * (N ^ 2 * N ^ (-(D + b + 2)))) ≤
      2 * cΘ ^ 2 * (2 * (c₀ + 1) * (x * y) + 1 / κ' ^ 2 * (x * y ^ 2) + cΘ * (x * y ^ 2)) := by
    gcongr
  refine h4.trans ?_
  have hy2 : y ^ 2 ≤ y := by nlinarith
  have h5 : 2 * cΘ ^ 2 * (2 * (c₀ + 1) * (x * y) + 1 / κ' ^ 2 * (x * y ^ 2) + cΘ * (x * y ^ 2)) ≤
      2 * cΘ ^ 2 * (2 * (c₀ + 1) * (x * y) + 1 / κ' ^ 2 * (x * y) + cΘ * (x * y)) := by
    gcongr
  refine h5.trans ?_
  have h6 : 2 * cΘ ^ 2 * (2 * (c₀ + 1) * (x * y) + 1 / κ' ^ 2 * (x * y) + cΘ * (x * y)) =
      x * y * (2 * cΘ ^ 2 * (2 * (c₀ + 1) + 1 / κ' ^ 2 + cΘ)) := by ring
  rw [h6]
  calc x * y * (2 * cΘ ^ 2 * (2 * (c₀ + 1) + 1 / κ' ^ 2 + cΘ)) ≤ x * y * W :=
        mul_le_mul_of_nonneg_left hbig (by positivity)
    _ = x := by rw [mul_assoc, mul_comm y W, hWy, mul_one]


/-- **The deterministic bound of `‖off‖` on the good event** (`(eq:propcalB)`, `3_5:2155`): if every `|𝓛^{(2)} - 𝒦^{(2)}|_{s,σ',(b₁,b₂)}`
is at most `N ζ'_s(|b₁ - b₂|)` (the single good event of `STGdecayW` at `u = s`) and the per-entry bad events have probability `≤ N^{-D₁}`,
then `|off| ≤ 2 c_Θ² N² (2 N (c₀+1) W^{-D_w} + (N⁴/κ'² + c_Θ) N^{-D₁})`: the sum has `≤ N²` terms, `|Θ_t| ≤ c_Θ/g²`,
`(1-s)² (c_Θ/g²)² ≤ c_Θ²` (`1 - s ≤ g²`), the profile is `≤ (c₀+1) W^{-D_w}` off the window (`cltFar_zeta_off`) and
`|𝔼 𝓑| ≤ N ζ' + (η_s^{-2} + |𝒦|) N^{-D₁}` (`cltFar_B_bound`, `cltFar_eta_inv_le`, `cltFar_K_le`). -/
private theorem cltFar_off_det (hd : 3 ≤ d) (sz : Sizes d) (n : ℕ) {E s t C₅ c₅ κ' Dw D₁ : ℝ}
    (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) (ω : sz.SeqΩ)
    (hE : |E| < 2) (hκ' : κ' ≤ (mE E).im) (hκ'0 : 0 < κ') (hs0 : 0 ≤ s) (hst : s < t) (ht : t < 1)
    (hg : 0 < sz.lam n) (hreg : sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 ≤ 1 - t) (hreg2 : 1 - s ≤ sz.lam n ^ 2)
    (hA1 : 1 ≤ STAI sz n) (hC₅ : 0 ≤ C₅) (hc₅ : 0 < c₅) (h5 : CltFarH5 sz n E C₅ c₅) (hDw : 0 < Dw)
    (hlwD : Dw ^ 2 ≤ Real.log ((sz.W n : ℕ) : ℝ))
    (hω : ∀ (σ' : Fin 2 → Bool) (b₁ b₂ : Zd d (sz.L n)),
      ‖STLKM sz n E s (sz.seqHflow n s ω) σ' ![b₁, b₂]‖ ≤
        ((sz.size n : ℕ) : ℝ) ^ (1 : ℝ) * cltFarZ sz n s Dw (zdistInf d (sz.L n) (b₁ - b₂)))
    (hP1 : ∀ (σ' : Fin 2 → Bool) (b₁ b₂ : Zd d (sz.L n)),
      sz.seqP {ω' | ((sz.size n : ℕ) : ℝ) ^ (1 : ℝ) * cltFarZ sz n s Dw (zdistInf d (sz.L n) (b₁ - b₂)) <
          ‖STLKM sz n E s (sz.seqHflow n s ω') σ' ![b₁, b₂]‖} ≤ ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-D₁))) :
    ‖CltMom2.off sz n E s t σ a ω‖ ≤ 2 * (C₅ * (1 + 2 ^ (d - 1))) ^ 2 * ((sz.size n : ℕ) : ℝ) ^ 2 *
      (2 * (((sz.size n : ℕ) : ℝ) * ((cltFar_c0 d + 1) * ((sz.W n : ℕ) : ℝ) ^ (-Dw))) +
        (((sz.size n : ℕ) : ℝ) ^ 4 / κ' ^ 2 + C₅ * (1 + 2 ^ (d - 1))) * ((sz.size n : ℕ) : ℝ) ^ (-D₁)) := by
  have hs1 : s < 1 := hst.trans ht
  have ht0 : 0 ≤ t := hs0.trans hst.le
  have hreg_s : sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 ≤ 1 - s := le_trans hreg (by linarith)
  have hN1 := cltFar_one_le_N sz n
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
  have hcΘ0 : 0 ≤ C₅ * (1 + 2 ^ (d - 1)) := by positivity
  have hc0 : 0 < cltFar_c0 d := by
    unfold cltFar_c0
    have := cltFar_c3_pos d
    positivity
  have hW1 := cltFar_one_le_W sz n
  set N : ℝ := ((sz.size n : ℕ) : ℝ) with hNdef
  set W : ℝ := ((sz.W n : ℕ) : ℝ) with hWdef
  set cΘ : ℝ := C₅ * (1 + 2 ^ (d - 1)) with hcΘ
  set Xb : ℝ := 2 * (N * ((cltFar_c0 d + 1) * W ^ (-Dw))) + (N ^ 4 / κ' ^ 2 + cΘ) * N ^ (-D₁) with hXb
  have hW0 : 0 < W := by linarith
  have hXb0 : 0 ≤ Xb := by
    have : 0 ≤ N ^ (-D₁) := Real.rpow_nonneg hN0.le _
    have : 0 ≤ W ^ (-Dw) := Real.rpow_nonneg hW0.le _
    positivity
  have hΘ := cltFar_Theta_all hd sz n hE ht0 ht hg hreg hC₅ hc₅ h5 σ
  have hKΘ : 0 ≤ cΘ / sz.lam n ^ 2 := by positivity
  have hη := cltFar_eta_inv_le sz n (E := E) (s := s) (t := t) (by omega) hκ' hκ'0 hst.le hreg hA1
  have hX : ∀ b₁ b₂ : Zd d (sz.L n),
      Real.log W ^ 3 * ellT (sz.L n) (sz.lam n) s < ((zdistInf d (sz.L n) (b₁ - b₂) : ℕ) : ℝ) →
      ‖STLKM sz n E s (sz.seqHflow n s ω) σ ![b₁, b₂] -
        ∫ ω', STLKM sz n E s (sz.seqHflow n s ω') σ ![b₁, b₂] ∂(sz.seqP)‖ ≤ Xb := by
    intro b₁ b₂ hoff
    have hr : zdistInf d (sz.L n) (b₁ - b₂) ≤ sz.L n := st5_zdistInf_le sz n _
    have hζ := cltFar_zeta_off hd sz n hs1 hg hreg_s hA1 hDw hlwD _ hr hoff
    have hZ0 : 0 ≤ cltFarZ sz n s Dw (zdistInf d (sz.L n) (b₁ - b₂)) := by
      unfold cltFarZ
      have hBctl0 : 0 ≤ sz.Bctl n s := by
        unfold Sizes.Bctl Bparam
        have : 0 < 1 - s := by linarith
        rw [abs_of_pos this]
        positivity
      have hSTWB0 : 0 ≤ STWB sz n s (zdistInf d (sz.L n) (b₁ - b₂)) := by
        unfold STWB Bparam
        have : 0 < 1 - s := by linarith
        rw [abs_of_pos this]
        positivity
      positivity
    have hZ0' : 0 ≤ N ^ (1 : ℝ) * cltFarZ sz n s Dw (zdistInf d (sz.L n) (b₁ - b₂)) :=
      mul_nonneg (Real.rpow_nonneg hN0.le _) hZ0
    have hB := cltFar_B_bound sz n hE hs1 σ b₁ b₂ (τ := 1)
      (Z := cltFarZ sz n s Dw (zdistInf d (sz.L n) (b₁ - b₂))) (D₁ := D₁) hZ0' (hP1 σ b₁ b₂)
    have hX1 := hω σ b₁ b₂
    have hK := (cltFar_K_le hd sz n hE hs0 hs1 hg hreg_s hC₅ hc₅ h5 σ b₁ b₂).trans
      (cltFar_K_le' sz n hcΘ0 hg hA1)
    have hND : 0 ≤ N ^ (-D₁) := Real.rpow_nonneg hN0.le _
    have hNZ : N ^ (1 : ℝ) * cltFarZ sz n s Dw (zdistInf d (sz.L n) (b₁ - b₂)) ≤
        N * ((cltFar_c0 d + 1) * W ^ (-Dw)) := by
      rw [Real.rpow_one]
      exact mul_le_mul_of_nonneg_left hζ hN0.le
    have hE2 : ((etaT E s)⁻¹ ^ 2 + ‖STKloop sz n E s σ ![b₁, b₂]‖) * N ^ (-D₁) ≤
        (N ^ 4 / κ' ^ 2 + cΘ) * N ^ (-D₁) :=
      mul_le_mul_of_nonneg_right (add_le_add hη hK) hND
    calc ‖STLKM sz n E s (sz.seqHflow n s ω) σ ![b₁, b₂] -
          ∫ ω', STLKM sz n E s (sz.seqHflow n s ω') σ ![b₁, b₂] ∂(sz.seqP)‖
        ≤ ‖STLKM sz n E s (sz.seqHflow n s ω) σ ![b₁, b₂]‖ +
          ‖∫ ω', STLKM sz n E s (sz.seqHflow n s ω') σ ![b₁, b₂] ∂(sz.seqP)‖ := norm_sub_le _ _
      _ ≤ N ^ (1 : ℝ) * cltFarZ sz n s Dw (zdistInf d (sz.L n) (b₁ - b₂)) +
          (N ^ (1 : ℝ) * cltFarZ sz n s Dw (zdistInf d (sz.L n) (b₁ - b₂)) +
            ((etaT E s)⁻¹ ^ 2 + ‖STKloop sz n E s σ ![b₁, b₂]‖) * N ^ (-D₁)) := add_le_add hX1 hB
      _ ≤ N * ((cltFar_c0 d + 1) * W ^ (-Dw)) + (N * ((cltFar_c0 d + 1) * W ^ (-Dw)) +
            (N ^ 4 / κ' ^ 2 + cΘ) * N ^ (-D₁)) := by
          gcongr
      _ = Xb := by rw [hXb]; ring
  have hsum := cltFar_off_sum_le sz n σ a ω hKΘ hXb0 hΘ hX
  refine hsum.trans ?_
  have hLd := cltFar_Lpow_le sz n
  have hLd0 : (0 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) ^ d := by positivity
  have hg2 : 0 < sz.lam n ^ 2 := by positivity
  have h1 : (1 - s) * (cΘ / sz.lam n ^ 2) ≤ cΘ := by
    calc (1 - s) * (cΘ / sz.lam n ^ 2) = cΘ * ((1 - s) / sz.lam n ^ 2) := by ring
      _ ≤ cΘ * 1 := mul_le_mul_of_nonneg_left (div_le_one_of_le₀ hreg2 hg2.le) hcΘ0
      _ = cΘ := mul_one _
  have h2 : (1 - s) ^ 2 * (((sz.L n : ℕ) : ℝ) ^ d * (((sz.L n : ℕ) : ℝ) ^ d *
      (cΘ / sz.lam n ^ 2 * Xb * (cΘ / sz.lam n ^ 2 + cΘ / sz.lam n ^ 2)))) =
      2 * ((1 - s) * (cΘ / sz.lam n ^ 2)) ^ 2 * (((sz.L n : ℕ) : ℝ) ^ d * ((sz.L n : ℕ) : ℝ) ^ d) * Xb := by ring
  rw [h2]
  have h3 : ((1 - s) * (cΘ / sz.lam n ^ 2)) ^ 2 ≤ cΘ ^ 2 :=
    pow_le_pow_left₀ (mul_nonneg (by linarith) hKΘ) h1 2
  have h4 : ((sz.L n : ℕ) : ℝ) ^ d * ((sz.L n : ℕ) : ℝ) ^ d ≤ N ^ 2 := by nlinarith
  calc 2 * ((1 - s) * (cΘ / sz.lam n ^ 2)) ^ 2 * (((sz.L n : ℕ) : ℝ) ^ d * ((sz.L n : ℕ) : ℝ) ^ d) * Xb
      ≤ 2 * cΘ ^ 2 * N ^ 2 * Xb := by gcongr
    _ = 2 * cΘ ^ 2 * N ^ 2 * Xb := rfl

/-- `N ≤ W^{1/𝔠}` from `N^𝔠 ≤ W` (`(Main_DEL_COND)`). -/
private theorem cltFar_N_le_W {N W 𝔠 : ℝ} (hN0 : 0 < N) (h𝔠 : 0 < 𝔠) (hb : N ^ 𝔠 ≤ W) : N ≤ W ^ (1 / 𝔠) := by
  have h := Real.rpow_le_rpow (Real.rpow_nonneg hN0.le 𝔠) hb (show (0 : ℝ) ≤ 1 / 𝔠 by positivity)
  rwa [← Real.rpow_mul hN0.le, mul_one_div_cancel h𝔠.ne', Real.rpow_one] at h

/-- `N^k ≤ W^{k/𝔠}` for a natural `k`. -/
private theorem cltFar_Npow_le_W {N W 𝔠 : ℝ} (hN0 : 0 < N) (hW0 : 0 < W) (h𝔠 : 0 < 𝔠) (hb : N ^ 𝔠 ≤ W) (k : ℕ) :
    N ^ k ≤ W ^ ((k : ℝ) / 𝔠) := by
  have h := cltFar_N_le_W hN0 h𝔠 hb
  calc N ^ k ≤ (W ^ (1 / 𝔠)) ^ k := pow_le_pow_left₀ hN0.le h k
    _ = W ^ ((k : ℝ) / 𝔠) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hW0.le]
        congr 1; ring

/-- **Target 2: the off-window part** (`(eq:propcalB)`, `3_5:2155`; the `O(W^{-D})` of `(eq:2p_product)`): `‖CltMom2.off‖ ≤ W^{-D}` for
every `σ, a` at once, off an event of probability `≤ N^{-D'}`.  The event is the single good event of `(Eq:Gdecay_w)` at `u = s`
(`cltFar_good_event` at `(D_w, τ, D₁) = (D + 3/𝔠 + 1, 1, D')`, the union over `(σ, a, b)` being inside `STGdecayW`); on it
`cltFar_off_det` bounds `‖off‖` and `cltFar_off_numeric` gives `≤ W^{-D}` (`N³ ≤ W^{3/𝔠}`, `N⁶ ≤ W^{6/𝔠}`, `W → ∞`, `D_w² ≤ log W`). -/
theorem cltFar_off (d : ℕ) : CltFar.OffStmt d := by
  intro hd sz κ 𝔠 𝔡 Cd E s t hκ hAdm hE hs0 hst ht hreg hG D D' hD hD'
  obtain ⟨h𝔠, h𝔡, hSz, hBw, hWO⟩ := hAdm
  have hΛ : 0 < 𝔡⁻¹ := inv_pos.2 h𝔡
  obtain ⟨C₅, hC₅, c₅, hc₅, H5⟩ := prop5Decay_holds d 𝔡⁻¹ hd hΛ
  have hκ'0 : 0 < min κ (1 / 2) := lt_min hκ (by norm_num)
  have hs1 : ∀ n, s n < 1 := fun n => (hst n).trans (ht n)
  have hst' : ∀ n, s n ≤ t n := fun n => (hst n).le
  have hDw : (0 : ℝ) < D + 3 / 𝔠 + 1 := by positivity
  have hD₁ : (0 : ℝ) < D + 6 / 𝔠 + 2 := by positivity
  have hgood := cltFar_good_event sz hs1 hst' hG hDw (τ := 1) (D₁ := D') one_pos hD'
  have hbad := cltFar_bad_one sz hs1 hst' hG hDw (τ := 1) (D₁ := D + 6 / 𝔠 + 2) one_pos hD₁
  have hev := st5_eventually_A_ge_one sz h𝔡 hWO
  have hcΘ0 : 0 ≤ C₅ * (1 + 2 ^ (d - 1)) := by positivity
  have hc0 : 0 < cltFar_c0 d := by
    unfold cltFar_c0
    have := cltFar_c3_pos d
    positivity
  have hWt : Tendsto (fun n => ((sz.W n : ℕ) : ℝ)) atTop atTop :=
    tendsto_atTop_mono' atTop (hBw.mono fun n hn => hn) ((tendsto_rpow_atTop h𝔠).comp hSz)
  have hWev : ∀ᶠ n in atTop, (D + 3 / 𝔠 + 1) ^ 2 ≤ Real.log ((sz.W n : ℕ) : ℝ) ∧
      2 * (C₅ * (1 + 2 ^ (d - 1))) ^ 2 * (2 * (cltFar_c0 d + 1) + 1 / (min κ (1 / 2)) ^ 2 +
        C₅ * (1 + 2 ^ (d - 1))) ≤ ((sz.W n : ℕ) : ℝ) :=
    ((Real.tendsto_log_atTop.comp hWt).eventually_ge_atTop _).and (hWt.eventually_ge_atTop _)
  filter_upwards [hgood, hbad, hev, hBw, hWO, hWev] with n hgn hbn hAn hBwn hWOn hWn
  obtain ⟨hg, hA1⟩ := hAn
  obtain ⟨-, hgΛ⟩ := hWOn
  obtain ⟨hlwD, hbig⟩ := hWn
  have hN1 := cltFar_one_le_N sz n
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
  have hW1 := cltFar_one_le_W sz n
  have hW0 : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by linarith
  have hEn : |E n| < 2 := by have := hE n; linarith
  have hκ' : min κ (1 / 2) ≤ (mE (E n)).im := cltFar_mE_im_ge hκ (hE n)
  have h5 : CltFarH5 sz n (E n) C₅ c₅ := cltFar_H5_at sz n hEn.le hg hgΛ H5
  refine le_trans (measure_mono ?_) hgn
  intro ω hω
  obtain ⟨σ, a, hσa⟩ := hω
  by_contra hno
  have hω' : ∀ (σ' : Fin 2 → Bool) (b₁ b₂ : Zd d (sz.L n)),
      ‖STLKM sz n (E n) (s n) (sz.seqHflow n (s n) ω) σ' ![b₁, b₂]‖ ≤
        ((sz.size n : ℕ) : ℝ) ^ (1 : ℝ) * cltFarZ sz n (s n) (D + 3 / 𝔠 + 1) (zdistInf d (sz.L n) (b₁ - b₂)) := by
    intro σ' b₁ b₂
    by_contra h
    exact hno ⟨σ', b₁, b₂, not_le.1 h⟩
  have hdet := cltFar_off_det hd sz n σ a ω hEn hκ' hκ'0 (hs0 n) (hst n) (ht n) hg (hreg n).1 (hreg n).2 hA1
    hC₅.le hc₅ h5 hDw hlwD hω' (fun σ' b₁ b₂ => hbn σ' b₁ b₂)
  have hQ3 := cltFar_Npow_le_W hN0 hW0 h𝔠 hBwn 3
  have hQ6 := cltFar_Npow_le_W hN0 hW0 h𝔠 hBwn 6
  have hWN := cltFar_W_le sz (by omega) n
  have hnum := cltFar_off_numeric (N := ((sz.size n : ℕ) : ℝ)) (W := ((sz.W n : ℕ) : ℝ)) (D := D)
    (a := 3 / 𝔠) (b := 6 / 𝔠) (cΘ := C₅ * (1 + 2 ^ (d - 1))) (c₀ := cltFar_c0 d) (κ' := min κ (1 / 2)) hW1 hWN
    hD.le (by positivity) (by simpa using hQ3) (by simpa using hQ6) hcΘ0 hc0.le hκ'0 hbig
  have := hdet.trans hnum
  linarith [hσa]

end Off

/-! ## 7. Target 3: the window fluctuation `c_n · fluc` -/

section Fluc

variable {d : ℕ}

/-- `(F P2 + G) / (Y2 P2) ≤ F/Y2 + G R2 / Y2` for `1/P2 ≤ R2`: the factor `(ℓ_s⁴/R_a)^{2p}` of `CltMom2.rhs` cancels exactly against
`θ₀^{2p}` in the first part. -/
private theorem cltFar_div_step {F P2 G Y2 R2 : ℝ} (hP2 : 0 < P2) (hG : 0 ≤ G) (hY2 : 0 < Y2)
    (hR2 : 1 / P2 ≤ R2) : (F * P2 + G) / (Y2 * P2) ≤ F / Y2 + G * R2 / Y2 := by
  have h1 : (F * P2 + G) / (Y2 * P2) = F / Y2 + G * (1 / P2) / Y2 := by
    field_simp
  rw [h1]
  gcongr

/-- The numerics of the Markov step of target 3: `K Lw ≤ N²/4`, `Λp ≤ u Y2`, `B ≤ u`, `ε₂ ≤ u` give `≤ N² u`. -/
private theorem cltFar_fluc_numeric {K Lw Λp B ε2 Y2 u N : ℝ} (hN : 3 ≤ N) (hu : 0 < u) (hY2 : 1 ≤ Y2)
    (hKL : K * Lw ≤ N ^ 2 / 4) (hΛp0 : 0 ≤ Λp) (hΛp : Λp ≤ u * Y2) (hB0 : 0 ≤ B) (hB : B ≤ u)
    (hε0 : 0 ≤ ε2) (hε : ε2 ≤ u) :
    K * Lw * (Λp + B) / Y2 + ε2 / Y2 ≤ N ^ 2 * u := by
  have hY0 : 0 < Y2 := by linarith
  have hN2 : (9 : ℝ) ≤ N ^ 2 := by nlinarith
  have h1 : K * Lw * (Λp + B) ≤ N ^ 2 / 4 * (u * Y2 + u) :=
    mul_le_mul hKL (add_le_add hΛp hB) (by positivity) (by positivity)
  have h2 : K * Lw * (Λp + B) / Y2 ≤ N ^ 2 / 4 * (u * Y2 + u) / Y2 := div_le_div_of_nonneg_right h1 hY0.le
  have h3 : N ^ 2 / 4 * (u * Y2 + u) / Y2 = N ^ 2 / 4 * u + N ^ 2 / 4 * u / Y2 := by field_simp
  have h4 : N ^ 2 / 4 * u / Y2 ≤ N ^ 2 / 4 * u := div_le_self (by positivity) hY2
  have h5 : ε2 / Y2 ≤ u := (div_le_self hε0 hY2).trans hε
  have h6 : 2 * u ≤ N ^ 2 / 4 * u := by nlinarith
  nlinarith

/-- The constant of `CltMom2.rhs` in front of `(log W)^{24p}`: `2^{2p} (2p)^{2p} (2 cs)^p (C_d M)^{2p}`. -/
private def cltFarKp (d : ℕ) (M : ℝ) (p : ℕ) : ℝ :=
  2 ^ (2 * p) * (((2 * p : ℕ) : ℝ) ^ (2 * p) * (2 * CltMom1.cs d) ^ p * (CltMom1.Cd d * M) ^ (2 * p))

private theorem cltFarKp_nonneg (hd : 1 ≤ d) {M : ℝ} (hM : 0 ≤ M) (p : ℕ) : 0 ≤ cltFarKp d M p := by
  unfold cltFarKp
  have := CltMom1.cs_pos hd
  have h2 : 0 ≤ CltMom1.Cd d := by
    unfold CltMom1.Cd
    positivity
  positivity

/-- `Λ'^{2p} ≤ N^{-(D+2)} (N^τ)^{2p}` for `Λ' = N^{τ/2}` and `D + 2 ≤ pτ` (`N^{pτ} ≤ N^{2pτ-D-2}`). -/
private theorem cltFar_Lp_le {N τ D : ℝ} {p : ℕ} (hN1 : 1 ≤ N) (hpτ : D + 2 ≤ (p : ℝ) * τ) :
    (N ^ (τ / 2)) ^ (2 * p) ≤ N ^ (-(D + 2)) * (N ^ τ) ^ (2 * p) := by
  have hN0 : 0 < N := by linarith
  have e1 : (N ^ (τ / 2)) ^ (2 * p) = N ^ (τ / 2 * ((2 * p : ℕ) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]
  have e2 : (N ^ τ) ^ (2 * p) = N ^ (τ * ((2 * p : ℕ) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]
  rw [e1, e2, ← Real.rpow_add hN0]
  apply Real.rpow_le_rpow_of_exponent_le hN1
  push_cast
  nlinarith

/-- `BYw^{2p} · #labels · N^{-D₁} ≤ N^{-(D+2)}` for `BYw ≤ N⁹`, `#labels ≤ N²`, `D₁ ≥ 18p + D + 4`. -/
private theorem cltFar_Bq_le {N D D₁ BYw cd : ℝ} {p : ℕ} (hN1 : 1 ≤ N) (hBYw0 : 0 ≤ BYw) (hBYw : BYw ≤ N ^ 9)
    (hcd0 : 0 ≤ cd) (hcd : cd ≤ N ^ 2) (hD₁ : 18 * (p : ℝ) + D + 4 ≤ D₁) :
    BYw ^ (2 * p) * cd * N ^ (-D₁) ≤ N ^ (-(D + 2)) := by
  have hN0 : 0 < N := by linarith
  calc BYw ^ (2 * p) * cd * N ^ (-D₁) ≤ (N ^ 9) ^ (2 * p) * N ^ 2 * N ^ (-D₁) := by
        gcongr
    _ = N ^ ((9 * (2 * p) + 2 : ℕ) : ℝ) * N ^ (-D₁) := by
        rw [← pow_mul, ← pow_add, Real.rpow_natCast]
    _ = N ^ (((9 * (2 * p) + 2 : ℕ) : ℝ) + (-D₁)) := by rw [← Real.rpow_add hN0]
    _ ≤ N ^ (-(D + 2)) := by
        apply Real.rpow_le_rpow_of_exponent_le hN1
        push_cast
        linarith

/-- `εf (Σ|Z| · R)^{2p} ≤ N^{-(D+2)}` for `εf ≤ N^{-m₃}`, `Σ|Z| ≤ N² · 2c_Θ²`, `R ≤ 2N`, `(4c_Θ²)^{2p} ≤ N`, `m₃ ≥ 6p + D + 3`. -/
private theorem cltFar_Gq_le {N D cΘ SZ R εf : ℝ} {p m₃ : ℕ} (hN1 : 1 ≤ N) (hεf : εf ≤ (N ^ m₃)⁻¹)
    (hSZ0 : 0 ≤ SZ) (hSZ : SZ ≤ N ^ 2 * (2 * cΘ ^ 2)) (hR0 : 0 ≤ R) (hR : R ≤ 2 * N)
    (hcΘp : (4 * cΘ ^ 2) ^ (2 * p) ≤ N) (hm₃ : 6 * (p : ℝ) + D + 3 ≤ (m₃ : ℝ)) :
    εf * (SZ * R) ^ (2 * p) ≤ N ^ (-(D + 2)) := by
  have hN0 : 0 < N := by linarith
  have hSR : SZ * R ≤ 4 * cΘ ^ 2 * N ^ 3 := by
    calc SZ * R ≤ (N ^ 2 * (2 * cΘ ^ 2)) * (2 * N) := mul_le_mul hSZ hR hR0 (by positivity)
      _ = 4 * cΘ ^ 2 * N ^ 3 := by ring
  have hSR' : (SZ * R) ^ (2 * p) ≤ (4 * cΘ ^ 2) ^ (2 * p) * N ^ (6 * p) := by
    calc (SZ * R) ^ (2 * p) ≤ (4 * cΘ ^ 2 * N ^ 3) ^ (2 * p) :=
          pow_le_pow_left₀ (mul_nonneg hSZ0 hR0) hSR _
      _ = (4 * cΘ ^ 2) ^ (2 * p) * N ^ (6 * p) := by
          rw [mul_pow, ← pow_mul]; ring_nf
  calc εf * (SZ * R) ^ (2 * p) ≤ (N ^ m₃)⁻¹ * ((4 * cΘ ^ 2) ^ (2 * p) * N ^ (6 * p)) :=
        mul_le_mul hεf hSR' (by positivity) (by positivity)
    _ ≤ (N ^ m₃)⁻¹ * (N * N ^ (6 * p)) := by gcongr
    _ = N ^ (-(m₃ : ℝ)) * (N ^ (1 : ℝ) * N ^ ((6 * p : ℕ) : ℝ)) := by
        rw [Real.rpow_neg hN0.le, Real.rpow_natCast, Real.rpow_one, Real.rpow_natCast]
    _ = N ^ (-(m₃ : ℝ) + (1 + ((6 * p : ℕ) : ℝ))) := by
        rw [← Real.rpow_add hN0, ← Real.rpow_add hN0]
    _ ≤ N ^ (-(D + 2)) := by
        apply Real.rpow_le_rpow_of_exponent_le hN1
        push_cast
        linarith

/-- `BY (w^{d-2} + 1) ≤ N⁹` at one index (`cltFar_BY_le`, `cltFar_wpow_le`; `2𝔡^{-4}(κ'^{-2} + c_Θ) ≤ N`, `(log W)^{3(d-2)} ≤ N`). -/
private theorem cltFar_BYw_le (hd : 3 ≤ d) (sz : Sizes d) (n : ℕ) {E s t C₅ c₅ κ' 𝔡 : ℝ} (σ : Fin 2 → Bool)
    (hE : |E| < 2) (hκ' : κ' ≤ (mE E).im) (hκ'0 : 0 < κ') (hs0 : 0 ≤ s) (hst : s < t) (ht : t < 1)
    (hg : 0 < sz.lam n) (hgΛ : sz.lam n ≤ 𝔡⁻¹) (hreg : sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 ≤ 1 - t)
    (hA1 : 1 ≤ STAI sz n) (hC₅ : 0 ≤ C₅) (hc₅ : 0 < c₅) (h5 : CltFarH5 sz n E C₅ c₅)
    (hKc : 2 * 𝔡⁻¹ ^ 4 * (1 / κ' ^ 2 + C₅ * (1 + 2 ^ (d - 1))) ≤ ((sz.size n : ℕ) : ℝ))
    (hlwpow : Real.log ((sz.W n : ℕ) : ℝ) ^ (3 * (d - 2)) ≤ ((sz.size n : ℕ) : ℝ)) :
    CltMom2.BY sz n E s σ * ((Real.log ((sz.W n : ℕ) : ℝ) ^ 3 * ellT (sz.L n) (sz.lam n) s) ^ (d - 2) + 1) ≤
      ((sz.size n : ℕ) : ℝ) ^ 9 := by
  have hN1 := cltFar_one_le_N sz n
  have hBY := cltFar_BY_le hd sz n σ hE hκ' hκ'0 hs0 hst.le ht hg hgΛ hreg hA1 hC₅ hc₅ h5
  have hw := cltFar_wpow_le sz n (s := s) hlwpow
  have hBY0 : 0 ≤ CltMom2.BY sz n E s σ := by
    unfold CltMom2.BY
    positivity
  have hcΘ0 : 0 ≤ C₅ * (1 + 2 ^ (d - 1)) := by positivity
  have hlw0 : 0 ≤ Real.log ((sz.W n : ℕ) : ℝ) := Real.log_nonneg (cltFar_one_le_W sz n)
  have hℓ0 : 0 < ellT (sz.L n) (sz.lam n) s := ellT_pos (cltFar_one_le_L sz n)
  have hw0 : 0 ≤ (Real.log ((sz.W n : ℕ) : ℝ) ^ 3 * ellT (sz.L n) (sz.lam n) s) ^ (d - 2) + 1 := by positivity
  calc CltMom2.BY sz n E s σ * ((Real.log ((sz.W n : ℕ) : ℝ) ^ 3 * ellT (sz.L n) (sz.lam n) s) ^ (d - 2) + 1)
      ≤ (𝔡⁻¹ ^ 4 * (1 / κ' ^ 2 + C₅ * (1 + 2 ^ (d - 1))) * ((sz.size n : ℕ) : ℝ) ^ 6) *
          (2 * ((sz.size n : ℕ) : ℝ) ^ 2) :=
        mul_le_mul hBY hw hw0 (by positivity)
    _ = (2 * 𝔡⁻¹ ^ 4 * (1 / κ' ^ 2 + C₅ * (1 + 2 ^ (d - 1)))) * ((sz.size n : ℕ) : ℝ) ^ 8 := by ring
    _ ≤ ((sz.size n : ℕ) : ℝ) * ((sz.size n : ℕ) : ℝ) ^ 8 := mul_le_mul_of_nonneg_right hKc (by positivity)
    _ = ((sz.size n : ℕ) : ℝ) ^ 9 := by ring

/-- `R_a = |a₁-a₂|^{d-2} + 1 ≤ 2N`. -/
private theorem cltFar_R_le (sz : Sizes d) (n : ℕ) (r : ℕ) (hr : r ≤ sz.L n) :
    ((r : ℕ) : ℝ) ^ (d - 2) + 1 ≤ 2 * ((sz.size n : ℕ) : ℝ) := by
  have hL1 := cltFar_one_le_L sz n
  have hrL' : ((r : ℕ) : ℝ) ≤ ((sz.L n : ℕ) : ℝ) := by exact_mod_cast hr
  have h1 : ((r : ℕ) : ℝ) ^ (d - 2) ≤ ((sz.L n : ℕ) : ℝ) ^ (d - 2) := pow_le_pow_left₀ (Nat.cast_nonneg _) hrL' _
  have h2 : ((sz.L n : ℕ) : ℝ) ^ (d - 2) ≤ ((sz.L n : ℕ) : ℝ) ^ d := pow_le_pow_right₀ hL1 (Nat.sub_le d 2)
  have h3 := cltFar_Lpow_le sz n
  have hN1 := cltFar_one_le_N sz n
  linarith

/-- **The assembly of the three terms** (abstract atoms): `((K lw^{24p} (Λp + Bq)) P2 + εf SZ^{2p}) / θ^{2p} ≤ N^{-D}` for
`θ ≥ N^τ ℓ⁴/R`, `P2 = (ℓ⁴/R)^{2p}`, and the three bounds `Λp ≤ N^{-(D+2)} (N^τ)^{2p}`, `Bq ≤ N^{-(D+2)}`,
`εf (SZ R)^{2p} ≤ N^{-(D+2)}`, `K lw^{24p} ≤ N²/4`, `N ≥ 3`. -/
private theorem cltFar_assemble {N τ D Kp lw ℓ R θ Λp Bq εf SZ : ℝ} {p : ℕ} (hN3 : 3 ≤ N) (hτ : 0 < τ)
    (hℓ1 : 1 ≤ ℓ) (hR1 : 1 ≤ R) (hKp0 : 0 ≤ Kp) (hlw0 : 0 ≤ lw) (hKL : Kp * lw ^ (24 * p) ≤ N ^ 2 / 4)
    (hΛp0 : 0 ≤ Λp) (hΛp : Λp ≤ N ^ (-(D + 2)) * (N ^ τ) ^ (2 * p))
    (hBq0 : 0 ≤ Bq) (hBq : Bq ≤ N ^ (-(D + 2)))
    (hεf0 : 0 ≤ εf) (hSZ0 : 0 ≤ SZ) (hG : εf * (SZ * R) ^ (2 * p) ≤ N ^ (-(D + 2)))
    (hθ : N ^ τ * (ℓ ^ 4 / R) ≤ θ) :
    ((Kp * lw ^ (24 * p) * (Λp + Bq)) * (ℓ ^ 4 / R) ^ (2 * p) + εf * SZ ^ (2 * p)) / θ ^ (2 * p) ≤ N ^ (-D) := by
  have hN1 : 1 ≤ N := by linarith
  have hN0 : 0 < N := by linarith
  have hu0 : 0 < N ^ (-(D + 2)) := Real.rpow_pos_of_pos hN0 _
  have hNu : N ^ 2 * N ^ (-(D + 2)) = N ^ (-D) := by
    rw [← Real.rpow_natCast N 2, ← Real.rpow_add hN0]
    congr 1; push_cast; ring
  have hR0 : 0 < R := by linarith
  have hP0 : 0 < ℓ ^ 4 / R := by positivity
  have hθ0' : 0 < N ^ τ * (ℓ ^ 4 / R) := by positivity
  have hY2 : 1 ≤ (N ^ τ) ^ (2 * p) := one_le_pow₀ (Real.one_le_rpow hN1 hτ.le)
  have hP20 : 0 < (ℓ ^ 4 / R) ^ (2 * p) := by positivity
  have hR2 : 1 / (ℓ ^ 4 / R) ^ (2 * p) ≤ R ^ (2 * p) := by
    rw [one_div, ← inv_pow, inv_div]
    refine pow_le_pow_left₀ (by positivity) ?_ _
    rw [div_le_iff₀ (by positivity)]
    have : (1 : ℝ) ≤ ℓ ^ 4 := one_le_pow₀ hℓ1
    nlinarith
  have hG0 : 0 ≤ εf * SZ ^ (2 * p) := by positivity
  have hε : εf * SZ ^ (2 * p) * R ^ (2 * p) ≤ N ^ (-(D + 2)) := by
    have := hG
    rw [mul_pow, ← mul_assoc] at this
    exact this
  have hrhs0 : 0 ≤ (Kp * lw ^ (24 * p) * (Λp + Bq)) * (ℓ ^ 4 / R) ^ (2 * p) + εf * SZ ^ (2 * p) := by
    positivity
  calc ((Kp * lw ^ (24 * p) * (Λp + Bq)) * (ℓ ^ 4 / R) ^ (2 * p) + εf * SZ ^ (2 * p)) / θ ^ (2 * p)
      ≤ ((Kp * lw ^ (24 * p) * (Λp + Bq)) * (ℓ ^ 4 / R) ^ (2 * p) + εf * SZ ^ (2 * p)) /
          (N ^ τ * (ℓ ^ 4 / R)) ^ (2 * p) :=
        div_le_div_of_nonneg_left hrhs0 (pow_pos hθ0' _) (pow_le_pow_left₀ hθ0'.le hθ _)
    _ = ((Kp * lw ^ (24 * p) * (Λp + Bq)) * (ℓ ^ 4 / R) ^ (2 * p) + εf * SZ ^ (2 * p)) /
          ((N ^ τ) ^ (2 * p) * (ℓ ^ 4 / R) ^ (2 * p)) := by rw [mul_pow]
    _ ≤ (Kp * lw ^ (24 * p) * (Λp + Bq)) / (N ^ τ) ^ (2 * p) +
          εf * SZ ^ (2 * p) * R ^ (2 * p) / (N ^ τ) ^ (2 * p) := cltFar_div_step hP20 hG0 (by positivity) hR2
    _ ≤ N ^ 2 * N ^ (-(D + 2)) := cltFar_fluc_numeric hN3 hu0 hY2 hKL hΛp0 hΛp hBq0 hBq (by positivity) hε
    _ = N ^ (-D) := hNu

/-- **The bound of `rhs/θ^{2p}` at one index** (`(eq:main_challenge3)`, `3_5:2213`): with `Λ' = N^{τ/2}`, `q₁ = N^{-D₁}`,
`εf = W^{-m₃/𝔠}`, `θ ≥ θ₀ = N^τ ℓ_s⁴/(|a₁-a₂|^{d-2}+1)`, `D + 2 ≤ pτ`, `D₁ ≥ 18p + D + 4`, `m₃ ≥ 6p + D + 3`:
`CltMom2.rhs/θ^{2p} ≤ N^{-D}`.  The three terms are `N^{-pτ}·K_p(log W)^{24p}`, `BY^{2p}(w^{d-2}+1)^{2p} |labels| N^{-D₁} ≤ N^{18p+2-D₁}`
(`BY (w^{d-2}+1) ≤ N⁹`) and `W^{-m₃/𝔠}(Σ|Z|·R_a)^{2p} ≤ (4c_Θ²)^{2p} N^{6p-m₃}`. -/
private theorem cltFar_rhs_bound (hd : 3 ≤ d) (sz : Sizes d) (n : ℕ)
    {E s t C₅ c₅ κ' 𝔠 𝔡 M τ D D₁ θ : ℝ} {p m₃ : ℕ} (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n))
    (hτ : 0 < τ) (hpτ : D + 2 ≤ (p : ℝ) * τ) (hM : 0 < M)
    (hD₁ : 18 * (p : ℝ) + D + 4 ≤ D₁) (hm₃ : 6 * (p : ℝ) + D + 3 ≤ (m₃ : ℝ))
    (hE : |E| < 2) (hκ' : κ' ≤ (mE E).im) (hκ'0 : 0 < κ') (hs0 : 0 ≤ s) (hst : s < t) (ht : t < 1)
    (hg : 0 < sz.lam n) (hgΛ : sz.lam n ≤ 𝔡⁻¹) (hreg : sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 ≤ 1 - t)
    (hA1 : 1 ≤ STAI sz n) (hC₅ : 0 ≤ C₅) (hc₅ : 0 < c₅) (h5 : CltFarH5 sz n E C₅ c₅) (h𝔠 : 0 < 𝔠)
    (hBwn : ((sz.size n : ℕ) : ℝ) ^ 𝔠 ≤ ((sz.W n : ℕ) : ℝ))
    (hN3 : 3 ≤ ((sz.size n : ℕ) : ℝ))
    (hpoly : 4 * cltFarKp d M p * Real.log ((sz.size n : ℕ) : ℝ) ^ (24 * p) ≤ ((sz.size n : ℕ) : ℝ) ^ 2)
    (hcΘp : (4 * (C₅ * (1 + 2 ^ (d - 1))) ^ 2) ^ (2 * p) ≤ ((sz.size n : ℕ) : ℝ))
    (hKc : 2 * 𝔡⁻¹ ^ 4 * (1 / κ' ^ 2 + C₅ * (1 + 2 ^ (d - 1))) ≤ ((sz.size n : ℕ) : ℝ))
    (hlwpow : Real.log ((sz.W n : ℕ) : ℝ) ^ (3 * (d - 2)) ≤ ((sz.size n : ℕ) : ℝ))
    (hθ : ((sz.size n : ℕ) : ℝ) ^ τ * (ellT (sz.L n) (sz.lam n) s ^ 4 /
      (((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) ^ (d - 2) + 1)) ≤ θ) :
    CltMom2.rhs sz n E s t σ a p M (((sz.size n : ℕ) : ℝ) ^ (τ / 2)) (((sz.size n : ℕ) : ℝ) ^ (-D₁))
        (((sz.W n : ℕ) : ℝ) ^ (-((m₃ : ℝ) / 𝔠))) / θ ^ (2 * p) ≤ ((sz.size n : ℕ) : ℝ) ^ (-D) := by
  have hN1 := cltFar_one_le_N sz n
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
  have ht0 : 0 ≤ t := hs0.trans hst.le
  have hcΘ0 : 0 ≤ C₅ * (1 + 2 ^ (d - 1)) := by positivity
  have hW1 := cltFar_one_le_W sz n
  have hL1 := cltFar_one_le_L sz n
  have hℓ1 : 1 ≤ ellT (sz.L n) (sz.lam n) s := one_le_ellT hL1
  -- the three bounds
  have hLp := cltFar_Lp_le (N := ((sz.size n : ℕ) : ℝ)) (τ := τ) (D := D) (p := p) hN1 hpτ
  have hBYw := cltFar_BYw_le hd sz n σ hE hκ' hκ'0 hs0 hst ht hg hgΛ hreg hA1 hC₅ hc₅ h5 hKc hlwpow
  have hBYw0 : 0 ≤ CltMom2.BY sz n E s σ *
      ((Real.log ((sz.W n : ℕ) : ℝ) ^ 3 * ellT (sz.L n) (sz.lam n) s) ^ (d - 2) + 1) := by
    have : 0 ≤ CltMom2.BY sz n E s σ := by
      unfold CltMom2.BY
      positivity
    positivity
  have hBq := cltFar_Bq_le (N := ((sz.size n : ℕ) : ℝ)) (D := D) (D₁ := D₁) (p := p) hN1 hBYw0 hBYw
    (Nat.cast_nonneg _) (cltFar_card_pair_le sz n) hD₁
  have hZZ := cltFar_ZZ_le hd sz n (s := s) hE ht0 ht hg hreg hC₅ hc₅ h5 σ a
  have hSZ0 : 0 ≤ ∑ β : Fin 2 → Zd d (sz.L n), ‖CltMom2.Z sz n E s t σ a β‖ :=
    Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hR0 : 0 ≤ ((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) ^ (d - 2) + 1 := by positivity
  have hεf := cltFar_W_rpow_le hN0 h𝔠 hBwn m₃
  have hGq := cltFar_Gq_le (N := ((sz.size n : ℕ) : ℝ)) (D := D) (p := p) (m₃ := m₃) hN1
    hεf hSZ0 hZZ hR0
    (cltFar_R_le sz n _ (st5_zdistInf_le sz n _)) hcΘp hm₃
  have hrhs : CltMom2.rhs sz n E s t σ a p M (((sz.size n : ℕ) : ℝ) ^ (τ / 2)) (((sz.size n : ℕ) : ℝ) ^ (-D₁))
        (((sz.W n : ℕ) : ℝ) ^ (-((m₃ : ℝ) / 𝔠))) =
      (cltFarKp d M p * Real.log ((sz.W n : ℕ) : ℝ) ^ (24 * p) *
        ((((sz.size n : ℕ) : ℝ) ^ (τ / 2)) ^ (2 * p) +
          (CltMom2.BY sz n E s σ * ((Real.log ((sz.W n : ℕ) : ℝ) ^ 3 * ellT (sz.L n) (sz.lam n) s) ^ (d - 2) + 1)) ^ (2 * p) *
            (Fintype.card (Fin 2 → Zd d (sz.L n)) : ℝ) * ((sz.size n : ℕ) : ℝ) ^ (-D₁))) *
        (ellT (sz.L n) (sz.lam n) s ^ 4 / (((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) ^ (d - 2) + 1)) ^ (2 * p) +
      ((sz.W n : ℕ) : ℝ) ^ (-((m₃ : ℝ) / 𝔠)) *
        (∑ β : Fin 2 → Zd d (sz.L n), ‖CltMom2.Z sz n E s t σ a β‖) ^ (2 * p) := by
    unfold CltMom2.rhs cltFarKp
    ring
  rw [hrhs]
  have hlw0 : 0 ≤ Real.log ((sz.W n : ℕ) : ℝ) := Real.log_nonneg hW1
  have hKL : cltFarKp d M p * Real.log ((sz.W n : ℕ) : ℝ) ^ (24 * p) ≤ ((sz.size n : ℕ) : ℝ) ^ 2 / 4 := by
    have hlwN : Real.log ((sz.W n : ℕ) : ℝ) ≤ Real.log ((sz.size n : ℕ) : ℝ) :=
      Real.log_le_log (by linarith) (cltFar_W_le sz (by omega) n)
    have : Real.log ((sz.W n : ℕ) : ℝ) ^ (24 * p) ≤ Real.log ((sz.size n : ℕ) : ℝ) ^ (24 * p) :=
      pow_le_pow_left₀ hlw0 hlwN _
    have h1 := mul_le_mul_of_nonneg_left this (cltFarKp_nonneg (d := d) (by omega) hM.le p)
    linarith
  have hR1 : 1 ≤ ((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) ^ (d - 2) + 1 := by
    have : (0 : ℝ) ≤ ((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) ^ (d - 2) := by positivity
    linarith
  exact cltFar_assemble hN3 hτ hℓ1 hR1 (cltFarKp_nonneg (by omega) hM.le p) hlw0 hKL (by positivity) hLp
    (by positivity) hBq (Real.rpow_nonneg (by linarith) _) hSZ0 hGq hθ

/-- `θ = N^τ ζ / c_n` with `ζ = A^{-6/5}/R`, `c_n = (1-s)²/(g⁴ A^{6/5})`: `θ = N^τ g⁴/((1-s)² R)`. -/
private theorem cltFar_theta_eq {Nτ g s A65 R : ℝ} (hA65 : 0 < A65) (hR : 0 < R) (hg : 0 < g) (hs : s < 1) :
    Nτ * (A65⁻¹ / R) / ((1 - s) ^ 2 / (g ^ 4 * A65)) = Nτ * (g ^ 4 / ((1 - s) ^ 2 * R)) := by
  have hs' : (1 - s) ≠ 0 := (sub_pos.2 hs).ne'
  have hg' : g ≠ 0 := hg.ne'
  have hA' : A65 ≠ 0 := hA65.ne'
  have hR' : R ≠ 0 := hR.ne'
  field_simp

/-- `θ₀ ≤ θ`: `N^τ ℓ_s⁴/R ≤ N^τ g⁴/((1-s)² R)` from `(1-s) ℓ_s² ≤ g²` (`cltFar_ell_sq`). -/
private theorem cltFar_theta_ge {Nτ ℓ g s R : ℝ} (hNτ : 0 ≤ Nτ) (hR : 0 < R) (hs : s < 1)
    (h : (1 - s) * ℓ ^ 2 ≤ g ^ 2) :
    Nτ * (ℓ ^ 4 / R) ≤ Nτ * (g ^ 4 / ((1 - s) ^ 2 * R)) := by
  have hv : 0 < 1 - s := sub_pos.2 hs
  have h2 : (1 - s) ^ 2 * ℓ ^ 4 ≤ g ^ 4 := by
    calc (1 - s) ^ 2 * ℓ ^ 4 = ((1 - s) * ℓ ^ 2) ^ 2 := by ring
      _ ≤ (g ^ 2) ^ 2 := pow_le_pow_left₀ (by positivity) h 2
      _ = g ^ 4 := by ring
  refine mul_le_mul_of_nonneg_left ?_ hNτ
  rw [div_le_div_iff₀ hR (by positivity)]
  nlinarith

/-- **Target 3: the window fluctuation** `c_n · fluc` (`(eq:main_challenge3)`, `3_5:2213-2249`) at one index `(σ, a)`:
`P(N^τ A^{-6/5}/(|a₁-a₂|^{d-2}+1) < ‖c_n fluc‖) ≤ N^{-D}`, eventually, uniformly in `σ₀ ≠ σ₁` and `a`.  Route: `cltMom2_tail_eventually`
(Markov, `2p`-th moment, `STCltIsoConcl`) at `Λ' = N^{τ/2}`, `q₁ = N^{-D₁}` (`DomHyp` by target 1), `εf = W^{-m₃/𝔠}`, with
`p = ⌈(D+2)/τ⌉`, `D₁ = 18p + ⌈D⌉ + 4`, `m₃ = 6p + ⌈D⌉ + 3`; the event is `{θ < ‖fluc‖}` with `θ = N^τ g⁴/((1-s)² R_a) ≥ θ₀ =
N^τ ℓ_s⁴/R_a` (`1 - s ≤ g²`, `cltFar_theta_ge`), and `cltFar_rhs_bound` bounds `rhs/θ^{2p} ≤ N^{-D}`. -/
theorem cltFar_fluc (d : ℕ) : CltFar.FlucStmt d := by
  intro hd sz κ 𝔠 𝔡 Cd E s t hκ hAdm hE hs0 hst ht hreg hG hiso τ D hτ hD
  obtain ⟨h𝔠, h𝔡, hSz, hBw, hWO⟩ := hAdm
  have hAdm' : sz.Admissible 𝔠 𝔡 := ⟨h𝔠, h𝔡, hSz, hBw, hWO⟩
  have hΛ : 0 < 𝔡⁻¹ := inv_pos.2 h𝔡
  have hκ'0 : 0 < min κ (1 / 2) := lt_min hκ (by norm_num)
  obtain ⟨M, hM, HT⟩ := cltMom2_tail_eventually d hd 𝔡⁻¹ (min κ (1 / 2)) hΛ hκ'0
  obtain ⟨C₅, hC₅, c₅, hc₅, H5⟩ := prop5Decay_holds d 𝔡⁻¹ hd hΛ
  have hs1 : ∀ n, s n < 1 := fun n => (hst n).trans (ht n)
  have hst' : ∀ n, s n ≤ t n := fun n => (hst n).le
  -- the exponents
  obtain ⟨p, hpdef⟩ : ∃ p : ℕ, p = ⌈(D + 2) / τ⌉₊ := ⟨_, rfl⟩
  have hp1 : 1 ≤ p := by
    rw [hpdef]
    exact Nat.ceil_pos.2 (by positivity)
  have hpτ : D + 2 ≤ (p : ℝ) * τ := by
    have h1 : (D + 2) / τ ≤ (p : ℝ) := by rw [hpdef]; exact Nat.le_ceil _
    calc D + 2 = (D + 2) / τ * τ := by field_simp
      _ ≤ (p : ℝ) * τ := mul_le_mul_of_nonneg_right h1 hτ.le
  obtain ⟨m₃, hm₃def⟩ : ∃ m₃ : ℕ, m₃ = 6 * p + ⌈D⌉₊ + 3 := ⟨_, rfl⟩
  have hm₃ : 6 * (p : ℝ) + D + 3 ≤ (m₃ : ℝ) := by
    have := Nat.le_ceil D
    rw [hm₃def]; push_cast; linarith
  obtain ⟨m₁, hm₁def⟩ : ∃ m₁ : ℕ, m₁ = 18 * p + ⌈D⌉₊ + 4 := ⟨_, rfl⟩
  have hD₁ : 18 * (p : ℝ) + D + 4 ≤ (m₁ : ℝ) := by
    have := Nat.le_ceil D
    rw [hm₁def]; push_cast; linarith
  have hD₁0 : (0 : ℝ) < (m₁ : ℝ) := by linarith [show (0 : ℝ) ≤ p from Nat.cast_nonneg _]
  have hm₃0 : (0 : ℝ) < (m₃ : ℝ) := by linarith [show (0 : ℝ) ≤ p from Nat.cast_nonneg _]
  have hD'0 : (0 : ℝ) < (m₃ : ℝ) / 𝔠 := by positivity
  -- the eventual inputs
  have hdom := cltFar_dom d hd sz 𝔠 𝔡 Cd E s t hAdm' hs1 hst' hreg hG (τ / 2) (m₁ : ℝ) (half_pos hτ) hD₁0
  have hisoN := HT sz E s t hiso p hp1 ((m₃ : ℝ) / 𝔠) hD'0
  have hev := st5_eventually_A_ge_one sz h𝔡 hWO
  have hcΘ0 : 0 ≤ C₅ * (1 + 2 ^ (d - 1)) := by positivity
  have hpure : ∀ᶠ x : ℝ in atTop, 3 ≤ x ∧ 4 * cltFarKp d M p * Real.log x ^ (24 * p) ≤ x ^ 2 ∧
      (4 * (C₅ * (1 + 2 ^ (d - 1))) ^ 2) ^ (2 * p) ≤ x ∧
      2 * 𝔡⁻¹ ^ 4 * (1 / (min κ (1 / 2)) ^ 2 + C₅ * (1 + 2 ^ (d - 1))) ≤ x ∧
      Real.log x ^ (3 * (d - 2)) ≤ x ∧ (40 : ℝ) ≤ 𝔠 * Real.log x ∧ 2 * (d : ℝ) ≤ 𝔠 * Real.log x := by
    have h1 := cltFar_polylog (4 * cltFarKp d M p) 2 two_pos (24 * p)
    have h2 := cltFar_polylog 1 1 one_pos (3 * (d - 2))
    have h3 : ∀ᶠ x : ℝ in atTop, (40 : ℝ) ≤ 𝔠 * Real.log x :=
      (Filter.Tendsto.const_mul_atTop h𝔠 Real.tendsto_log_atTop).eventually_ge_atTop 40
    have h4 : ∀ᶠ x : ℝ in atTop, 2 * (d : ℝ) ≤ 𝔠 * Real.log x :=
      (Filter.Tendsto.const_mul_atTop h𝔠 Real.tendsto_log_atTop).eventually_ge_atTop _
    filter_upwards [eventually_ge_atTop (3 : ℝ), h1, eventually_ge_atTop ((4 * (C₅ * (1 + 2 ^ (d - 1))) ^ 2) ^ (2 * p)),
      eventually_ge_atTop (2 * 𝔡⁻¹ ^ 4 * (1 / (min κ (1 / 2)) ^ 2 + C₅ * (1 + 2 ^ (d - 1)))), h2, h3, h4]
      with x a b c e f g h
    refine ⟨a, ?_, c, e, ?_, g, h⟩
    · simpa [Real.rpow_two] using b
    · simpa [Real.rpow_one] using f
  filter_upwards [hdom, hisoN, hev, hBw, hWO, hSz.eventually hpure] with n hdomn hisoNn hAn hBwn hWOn hpn
  obtain ⟨hg, hA1⟩ := hAn
  obtain ⟨-, hgΛ⟩ := hWOn
  obtain ⟨hN3, hpoly, hcΘp, hKc, hlwpow, h40', h2d'⟩ := hpn
  intro σ hσ a
  have hN1 := cltFar_one_le_N sz n
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
  have hEn : |E n| < 2 := by have := hE n; linarith
  have hκ' : min κ (1 / 2) ≤ (mE (E n)).im := cltFar_mE_im_ge hκ (hE n)
  have h5 : CltFarH5 sz n (E n) C₅ c₅ := cltFar_H5_at sz n hEn.le hg hgΛ H5
  have hlw𝔠 : 𝔠 * Real.log ((sz.size n : ℕ) : ℝ) ≤ Real.log ((sz.W n : ℕ) : ℝ) := by
    have := Real.log_le_log (Real.rpow_pos_of_pos hN0 𝔠) hBwn
    rwa [Real.log_rpow hN0] at this
  have h40 : (40 : ℝ) ≤ Real.log ((sz.W n : ℕ) : ℝ) := h40'.trans hlw𝔠
  have h2d : 2 * (d : ℝ) ≤ Real.log ((sz.W n : ℕ) : ℝ) := h2d'.trans hlw𝔠
  have hlw0 : 0 ≤ Real.log ((sz.W n : ℕ) : ℝ) := Real.log_nonneg (cltFar_one_le_W sz n)
  have hlwN : Real.log ((sz.W n : ℕ) : ℝ) ≤ Real.log ((sz.size n : ℕ) : ℝ) :=
    Real.log_le_log (by linarith [cltFar_one_le_W sz n]) (cltFar_W_le sz (by omega) n)
  have hlwpow' : Real.log ((sz.W n : ℕ) : ℝ) ^ (3 * (d - 2)) ≤ ((sz.size n : ℕ) : ℝ) :=
    (pow_le_pow_left₀ hlw0 hlwN _).trans hlwpow
  have hs1n := hs1 n
  have hv : 0 < 1 - s n := sub_pos.2 hs1n
  have hℓ1 : 1 ≤ ellT (sz.L n) (sz.lam n) (s n) := one_le_ellT (cltFar_one_le_L sz n)
  have hRpos : 0 < ((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) ^ (d - 2) + 1 := by positivity
  have hA0 : 0 < STAI sz n := lt_of_lt_of_le one_pos hA1
  have hA65 : 0 < STAI sz n ^ (6 / 5 : ℝ) := Real.rpow_pos_of_pos hA0 _
  -- `θ`
  obtain ⟨θ, hθdef⟩ : ∃ θ : ℝ, θ = ((sz.size n : ℕ) : ℝ) ^ τ *
      (sz.lam n ^ 4 / ((1 - s n) ^ 2 * (((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) ^ (d - 2) + 1))) := ⟨_, rfl⟩
  have hθ₀ : ((sz.size n : ℕ) : ℝ) ^ τ * (ellT (sz.L n) (sz.lam n) (s n) ^ 4 /
      (((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) ^ (d - 2) + 1)) ≤ θ := by
    rw [hθdef]
    exact cltFar_theta_ge (Real.rpow_nonneg hN0.le _) hRpos hs1n (cltFar_ell_sq hg hs1n (hreg n).2)
  have hθpos : 0 < θ := by
    rw [hθdef]
    have : 0 < ((sz.size n : ℕ) : ℝ) ^ τ := Real.rpow_pos_of_pos hN0 _
    positivity
  -- the event
  have hcn : 0 < (1 - s n) ^ 2 / (sz.lam n ^ 4 * (sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d) ^ (6 / 5 : ℝ)) := by
    have : 0 < (sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d) ^ (6 / 5 : ℝ) := hA65
    positivity
  have hθeq : ((sz.size n : ℕ) : ℝ) ^ τ * (STAI sz n ^ (-(6 / 5 : ℝ)) /
      (((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) ^ (d - 2) + 1)) /
      ((1 - s n) ^ 2 / (sz.lam n ^ 4 * (sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d) ^ (6 / 5 : ℝ))) = θ := by
    rw [hθdef, Real.rpow_neg hA0.le]
    exact cltFar_theta_eq hA65 hRpos hg hs1n
  have hset : {ω | ((sz.size n : ℕ) : ℝ) ^ τ * (STAI sz n ^ (-(6 / 5 : ℝ)) /
          (((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) ^ (d - 2) + 1)) <
        ‖(((1 - s n) ^ 2 / (sz.lam n ^ 4 * (sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d) ^ (6 / 5 : ℝ)) : ℝ) : ℂ) *
          CltMom2.fluc sz n (E n) (s n) (t n) σ a ω‖} =
      {ω | θ < ‖CltMom2.fluc sz n (E n) (s n) (t n) σ a ω‖} := by
    ext ω
    simp only [Set.mem_ofPred_eq]
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hcn.le, ← div_lt_iff₀' hcn, hθeq]
  rw [hset]
  have hmom := hisoNn σ hσ a (((sz.size n : ℕ) : ℝ) ^ (τ / 2)) (((sz.size n : ℕ) : ℝ) ^ (-(m₁ : ℝ))) θ hEn hκ' hg hgΛ
    hs1n (hs0 n |>.trans (hst n).le) (ht n) (hreg n).1 h40 h2d (Real.rpow_nonneg hN0.le _) (hdomn σ) hθpos
  refine hmom.trans ?_
  apply ENNReal.ofReal_le_ofReal
  exact cltFar_rhs_bound hd sz n σ a hτ hpτ hM hD₁ hm₃ hEn hκ' hκ'0 (hs0 n) (hst n) (ht n) hg hgΛ (hreg n).1
    hA1 hC₅.le hc₅ h5 h𝔠 hBwn hN3 hpoly hcΘp hKc hlwpow' hθ₀

end Fluc

/-! ## 8. Target 4: the pin `STCltFar` -/

section Far

variable {d : ℕ}

/-- `W^{-D₀} ≤ ζ = A^{-6/5}/(r^{d-2} + 1)` for `D₀ = 6d/5 + (d-2)/𝔠 + 1` once `2 κ₁ ≤ W`, `κ₁ = (𝔡^{-2})^{6/5}`: `A ≤ 𝔡^{-2} W^d`,
`A^{6/5} ≤ κ₁ W^{6d/5}`, `r^{d-2} + 1 ≤ 2 L^{d-2} ≤ 2 N^{d-2} ≤ 2 W^{(d-2)/𝔠}` (`N ≤ W^{1/𝔠}`).  This is the floor `ζ ≥ W^{-D₀}` of the
bad-event split. -/
private theorem cltFar_zeta_ge (hd : 3 ≤ d) (sz : Sizes d) (n : ℕ) {𝔠 𝔡 : ℝ} (h𝔠 : 0 < 𝔠) (h𝔡 : 0 < 𝔡)
    (hA1 : 1 ≤ STAI sz n) (hg : 0 < sz.lam n) (hgΛ : sz.lam n ≤ 𝔡⁻¹)
    (hBwn : ((sz.size n : ℕ) : ℝ) ^ 𝔠 ≤ ((sz.W n : ℕ) : ℝ)) (r : ℕ) (hr : r ≤ sz.L n)
    (hbig : 2 * ((𝔡⁻¹ ^ 2) ^ (6 / 5 : ℝ)) ≤ ((sz.W n : ℕ) : ℝ)) :
    ((sz.W n : ℕ) : ℝ) ^ (-(6 * (d : ℝ) / 5 + ((d : ℝ) - 2) / 𝔠 + 1)) ≤
      STAI sz n ^ (-(6 / 5 : ℝ)) / (((r : ℕ) : ℝ) ^ (d - 2) + 1) := by
  have hN1 := cltFar_one_le_N sz n
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
  have hW1 := cltFar_one_le_W sz n
  have hW0 : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by linarith
  have hL1 := cltFar_one_le_L sz n
  have hA0 : 0 < STAI sz n := lt_of_lt_of_le one_pos hA1
  have hκ₁0 : 0 < (𝔡⁻¹ ^ 2) ^ (6 / 5 : ℝ) := Real.rpow_pos_of_pos (by positivity) _
  have hAW : STAI sz n ≤ 𝔡⁻¹ ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d := by
    unfold STAI
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hg.le hgΛ 2) (by positivity)
  have hA65 : STAI sz n ^ (6 / 5 : ℝ) ≤ (𝔡⁻¹ ^ 2) ^ (6 / 5 : ℝ) * ((sz.W n : ℕ) : ℝ) ^ (6 * (d : ℝ) / 5) := by
    calc STAI sz n ^ (6 / 5 : ℝ) ≤ (𝔡⁻¹ ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d) ^ (6 / 5 : ℝ) :=
          Real.rpow_le_rpow hA0.le hAW (by norm_num)
      _ = (𝔡⁻¹ ^ 2) ^ (6 / 5 : ℝ) * (((sz.W n : ℕ) : ℝ) ^ d) ^ (6 / 5 : ℝ) :=
          Real.mul_rpow (by positivity) (by positivity)
      _ = (𝔡⁻¹ ^ 2) ^ (6 / 5 : ℝ) * ((sz.W n : ℕ) : ℝ) ^ (6 * (d : ℝ) / 5) := by
          congr 1
          rw [← Real.rpow_natCast ((sz.W n : ℕ) : ℝ) d, ← Real.rpow_mul hW0.le]
          congr 1; ring
  have hR : ((r : ℕ) : ℝ) ^ (d - 2) + 1 ≤ 2 * ((sz.W n : ℕ) : ℝ) ^ (((d : ℝ) - 2) / 𝔠) := by
    have hrL' : ((r : ℕ) : ℝ) ≤ ((sz.L n : ℕ) : ℝ) := by exact_mod_cast hr
    have h1 : ((r : ℕ) : ℝ) ^ (d - 2) ≤ ((sz.L n : ℕ) : ℝ) ^ (d - 2) := pow_le_pow_left₀ (Nat.cast_nonneg _) hrL' _
    have h2 : ((sz.L n : ℕ) : ℝ) ^ (d - 2) ≤ ((sz.size n : ℕ) : ℝ) ^ (d - 2) :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) (cltFar_L_le sz (by omega) n) _
    have h3 := cltFar_Npow_le_W hN0 hW0 h𝔠 hBwn (d - 2)
    have h4 : (((d - 2 : ℕ) : ℝ)) = (d : ℝ) - 2 := by
      rw [Nat.cast_sub (by omega)]; norm_num
    rw [h4] at h3
    have h5 : (1 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) ^ (d - 2) := one_le_pow₀ hL1
    linarith
  have hR0 : 0 < ((r : ℕ) : ℝ) ^ (d - 2) + 1 := by positivity
  have hA65pos : 0 < STAI sz n ^ (6 / 5 : ℝ) := Real.rpow_pos_of_pos hA0 _
  have hden : STAI sz n ^ (6 / 5 : ℝ) * (((r : ℕ) : ℝ) ^ (d - 2) + 1) ≤
      (2 * (𝔡⁻¹ ^ 2) ^ (6 / 5 : ℝ)) * ((sz.W n : ℕ) : ℝ) ^ (6 * (d : ℝ) / 5 + ((d : ℝ) - 2) / 𝔠) := by
    calc STAI sz n ^ (6 / 5 : ℝ) * (((r : ℕ) : ℝ) ^ (d - 2) + 1)
        ≤ ((𝔡⁻¹ ^ 2) ^ (6 / 5 : ℝ) * ((sz.W n : ℕ) : ℝ) ^ (6 * (d : ℝ) / 5)) *
          (2 * ((sz.W n : ℕ) : ℝ) ^ (((d : ℝ) - 2) / 𝔠)) := mul_le_mul hA65 hR hR0.le (by positivity)
      _ = (2 * (𝔡⁻¹ ^ 2) ^ (6 / 5 : ℝ)) * ((sz.W n : ℕ) : ℝ) ^ (6 * (d : ℝ) / 5 + ((d : ℝ) - 2) / 𝔠) := by
          rw [Real.rpow_add hW0]; ring
  have e1 : STAI sz n ^ (-(6 / 5 : ℝ)) / (((r : ℕ) : ℝ) ^ (d - 2) + 1) =
      (STAI sz n ^ (6 / 5 : ℝ) * (((r : ℕ) : ℝ) ^ (d - 2) + 1))⁻¹ := by
    rw [Real.rpow_neg hA0.le]
    field_simp
  have e2 : ((sz.W n : ℕ) : ℝ) ^ (-(6 * (d : ℝ) / 5 + ((d : ℝ) - 2) / 𝔠 + 1)) =
      (((sz.W n : ℕ) : ℝ) ^ (6 * (d : ℝ) / 5 + ((d : ℝ) - 2) / 𝔠) * ((sz.W n : ℕ) : ℝ))⁻¹ := by
    rw [Real.rpow_neg hW0.le, Real.rpow_add hW0, Real.rpow_one]
  rw [e1, e2]
  refine inv_anti₀ (mul_pos hA65pos hR0) ?_
  calc STAI sz n ^ (6 / 5 : ℝ) * (((r : ℕ) : ℝ) ^ (d - 2) + 1)
      ≤ (2 * (𝔡⁻¹ ^ 2) ^ (6 / 5 : ℝ)) * ((sz.W n : ℕ) : ℝ) ^ (6 * (d : ℝ) / 5 + ((d : ℝ) - 2) / 𝔠) := hden
    _ ≤ ((sz.W n : ℕ) : ℝ) * ((sz.W n : ℕ) : ℝ) ^ (6 * (d : ℝ) / 5 + ((d : ℝ) - 2) / 𝔠) :=
        mul_le_mul_of_nonneg_right hbig (Real.rpow_nonneg hW0.le _)
    _ = ((sz.W n : ℕ) : ℝ) ^ (6 * (d : ℝ) / 5 + ((d : ℝ) - 2) / 𝔠) * ((sz.W n : ℕ) : ℝ) := mul_comm _ _

/-- **The deterministic splitting of the far part** (`3_5:2182-2186`): `f = 𝔼 f + c_n fluc + off` (`cltMom2_decomp`), so
`|f| ≤ |𝔼 f| + |c_n fluc| + |off| ≤ (2 N^{τ/2} + 1) ζ ≤ N^τ ζ` for `N^{τ/2} ≥ 3`, `|off| ≤ W^{-D₀} ≤ ζ`. -/
private theorem cltFar_far_le (sz : Sizes d) (n : ℕ) {E s t : ℝ} (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n))
    (ω : sz.SeqΩ) (hE : |E| < 2) (hs : s < 1) (hg : 0 < sz.lam n) {Nh ζ Woff : ℝ}
    (hmean : ‖∫ ω', STfFar sz n E s t σ a ω' ∂(sz.seqP)‖ ≤ Nh * ζ)
    (hfl : ‖(((1 - s) ^ 2 / (sz.lam n ^ 4 * (sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d) ^ (6 / 5 : ℝ)) : ℝ) : ℂ) *
      CltMom2.fluc sz n E s t σ a ω‖ ≤ Nh * ζ)
    (hoff : ‖CltMom2.off sz n E s t σ a ω‖ ≤ Woff) (hWζ : Woff ≤ ζ) (hζ0 : 0 ≤ ζ) (hNh : 3 ≤ Nh) :
    ‖STfFar sz n E s t σ a ω‖ ≤ Nh * Nh * ζ := by
  have hdec := cltMom2_decomp d sz n E s t σ a hE hs hg ω
  have h1 : ‖STfFar sz n E s t σ a ω‖ ≤
      ‖STfFar sz n E s t σ a ω - ∫ ω', STfFar sz n E s t σ a ω' ∂(sz.seqP)‖ +
        ‖∫ ω', STfFar sz n E s t σ a ω' ∂(sz.seqP)‖ := by
    calc ‖STfFar sz n E s t σ a ω‖
        = ‖(STfFar sz n E s t σ a ω - ∫ ω', STfFar sz n E s t σ a ω' ∂(sz.seqP)) +
            ∫ ω', STfFar sz n E s t σ a ω' ∂(sz.seqP)‖ := by rw [sub_add_cancel]
      _ ≤ _ := norm_add_le _ _
  rw [hdec] at h1
  have h2 := norm_add_le
    ((((1 - s) ^ 2 / (sz.lam n ^ 4 * (sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d) ^ (6 / 5 : ℝ)) : ℝ) : ℂ) *
      CltMom2.fluc sz n E s t σ a ω) (CltMom2.off sz n E s t σ a ω)
  have h3 : 2 * Nh * ζ + ζ ≤ Nh * Nh * ζ := by
    nlinarith [mul_nonneg hζ0 (mul_nonneg (sub_nonneg.2 hNh) (by linarith : (0 : ℝ) ≤ Nh + 1))]
  linarith

/-- The union bound over a finite family inside `P`: `B ⊆ E₀ ∪ ⋃ Ef` gives `P(B) ≤ a + #ι b` from `P(E₀) ≤ a`, `P(Ef i) ≤ b`. -/
private theorem cltFar_union_bound {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) {ι : Type*} [Fintype ι]
    (B E₀ : Set Ω) (Ef : ι → Set Ω) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hB : B ⊆ E₀ ∪ ⋃ i, Ef i)
    (h0 : μ E₀ ≤ ENNReal.ofReal a) (hf : ∀ i, μ (Ef i) ≤ ENNReal.ofReal b) :
    μ B ≤ ENNReal.ofReal (a + (Fintype.card ι : ℝ) * b) := by
  have h1 : μ (⋃ i, Ef i) ≤ ∑ i, μ (Ef i) := measure_iUnion_fintype_le μ Ef
  have h2 : ∑ i, μ (Ef i) ≤ ∑ _i : ι, ENNReal.ofReal b := Finset.sum_le_sum fun i _ => hf i
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h2
  calc μ B ≤ μ (E₀ ∪ ⋃ i, Ef i) := measure_mono hB
    _ ≤ μ E₀ + μ (⋃ i, Ef i) := measure_union_le _ _
    _ ≤ ENNReal.ofReal a + (Fintype.card ι : ENNReal) * ENNReal.ofReal b := add_le_add h0 (h1.trans h2)
    _ = ENNReal.ofReal (a + (Fintype.card ι : ℝ) * b) := by
        rw [ENNReal.ofReal_add ha (by positivity), ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]

/-- `N^{-(D+1)} + c N^{-(D+3)} ≤ N^{-D}` for `c ≤ 4 N²`, `N ≥ 5`. -/
private theorem cltFar_union_numeric {N D : ℝ} {c : ℕ} (hN5 : 5 ≤ N) (hc : (c : ℝ) ≤ 4 * N ^ 2) :
    N ^ (-(D + 1)) + (c : ℝ) * N ^ (-(D + 3)) ≤ N ^ (-D) := by
  have hN0 : 0 < N := by linarith
  have h1 : N ^ (-(D + 1)) = N ^ (-D) * N⁻¹ := by
    rw [show -(D + 1) = -D + (-1 : ℝ) by ring, Real.rpow_add hN0, Real.rpow_neg_one]
  have h3 : N ^ (-(D + 3)) = N ^ (-D) * (N ^ 3)⁻¹ := by
    have e : N ^ (-(3 : ℝ)) = (N ^ 3)⁻¹ := by
      rw [Real.rpow_neg hN0.le (3 : ℝ)]
      congr 1
      exact_mod_cast Real.rpow_natCast N 3
    rw [show -(D + 3) = -D + (-(3 : ℝ)) by ring, Real.rpow_add hN0, e]
  have hx : 0 < N ^ (-D) := Real.rpow_pos_of_pos hN0 _
  rw [h1, h3]
  have h4 : (c : ℝ) * (N ^ (-D) * (N ^ 3)⁻¹) ≤ 4 * N ^ 2 * (N ^ (-D) * (N ^ 3)⁻¹) :=
    mul_le_mul_of_nonneg_right hc (by positivity)
  have h5 : 4 * N ^ 2 * (N ^ (-D) * (N ^ 3)⁻¹) = 4 * (N ^ (-D) * N⁻¹) := by
    field_simp
  have h6 : N ^ (-D) * N⁻¹ * 5 ≤ N ^ (-D) := by
    have : 5 * N⁻¹ ≤ 1 := by
      rw [← div_eq_mul_inv, div_le_one hN0]; exact hN5
    nlinarith
  linarith

/-- **`lem;CLT`, far part, case (i)** (`3_5:2173-2176`, proof `3_5:2182-2249`): `f^{far}_{σ,a} ≺ A^{-6/5}/(|a₁-a₂|^{d-2}+1)` on the index set of
`STCltFarConcl`, as stated (`STCltFar`).  `f = 𝔼 f + c_n fluc + off` (`cltMom2_decomp`): the mean part is `meanFar_eventually` at `τ/2`,
the window fluctuation is `cltFar_fluc` at `(τ/2, D+3)` for one `(σ, a)` (the same `𝔠_d` of `stCltIso_holds` feeds `STCltIsoConcl`),
the off-window part is `cltFar_off` at `(6d/5 + (d-2)/𝔠 + 1, D+1)` for every `(σ, a)` at once; the union over the index set is the explicit finite
union over `{σ // σ₀ ≠ σ₁} × (Fin 2 → Z_L^d)` (`≤ 4N²` elements) inside `P`. -/
theorem stCltFar_holds (d : ℕ) : STCltFar d := by
  intro hd κ ε 𝔡 hκ hε h𝔡 Cd hCd
  obtain ⟨c, hc, hc', H⟩ := stCltIso_holds d hd κ ε 𝔡 hκ hε h𝔡 Cd hCd
  refine ⟨c, hc, hc', ?_⟩
  intro 𝔠 sz z hflow s t hs0 hst ht hreg hKb hKw hLK hDec hDecS hCon hS1 hS2 hLmax hLKU
  have hiso := H 𝔠 sz z hflow s t hs0 hst ht hreg hKb hKw hLK hDec hDecS hCon hS1 hS2 hLmax hLKU
  have hAdm : sz.Admissible 𝔠 𝔡 := hflow.1
  obtain ⟨h𝔠, -, hSz, hBw, hWO⟩ := hAdm
  have him : ∀ n, 0 < (z n).im := fun n =>
    lt_of_lt_of_le (Real.rpow_pos_of_pos (by exact_mod_cast sz.one_le_size n) _) (hflow.2 n).2.1
  have hE : ∀ n, |STflowE z n| ≤ 2 - κ := fun n => (abs_lemE_le (him n)).trans (hflow.2 n).1
  have ht1 : ∀ n, t n < 1 := fun n => (ht n).trans_lt (lemT_lt_one (him n))
  have hG := hS2.2.2
  have hs1 : ∀ n, s n < 1 := fun n => (hst n).trans (ht1 n)
  intro τ hτ D hD
  have hD₀ : (0 : ℝ) < 6 * (d : ℝ) / 5 + ((d : ℝ) - 2) / 𝔠 + 1 := by
    have h3 : (3 : ℝ) ≤ d := by exact_mod_cast hd
    have h1 : 0 ≤ ((d : ℝ) - 2) / 𝔠 := div_nonneg (by linarith) h𝔠.le
    linarith
  have hmean := meanFar_eventually hd sz hκ h𝔠 h𝔡 hSz hBw hWO (STflowE z) s t hE hs0 hst ht1 hreg hG (τ / 2)
    (half_pos hτ)
  have hoff := cltFar_off d hd sz κ 𝔠 𝔡 Cd (STflowE z) s t hκ hflow.1 hE hs0 hst ht1 hreg hG
    (6 * (d : ℝ) / 5 + ((d : ℝ) - 2) / 𝔠 + 1) (D + 1) hD₀ (by linarith)
  have hfluc := cltFar_fluc d hd sz κ 𝔠 𝔡 Cd (STflowE z) s t hκ hflow.1 hE hs0 hst ht1 hreg hG hiso (τ / 2) (D + 3)
    (half_pos hτ) (by linarith)
  have hev := st5_eventually_A_ge_one sz h𝔡 hWO
  have hpure : ∀ᶠ x : ℝ in atTop, 5 ≤ x ∧ 3 ≤ x ^ (τ / 2) := by
    have h1 : ∀ᶠ x : ℝ in atTop, 3 ≤ x ^ (τ / 2) :=
      (tendsto_rpow_atTop (half_pos hτ)).eventually_ge_atTop 3
    filter_upwards [eventually_ge_atTop (5 : ℝ), h1] with x a b
    exact ⟨a, b⟩
  have hWt : Tendsto (fun n => ((sz.W n : ℕ) : ℝ)) atTop atTop :=
    tendsto_atTop_mono' atTop (hBw.mono fun n hn => hn) ((tendsto_rpow_atTop h𝔠).comp hSz)
  filter_upwards [hmean, hoff, hfluc, hev, hBw, hWO, hSz.eventually hpure,
    hWt.eventually_ge_atTop (2 * ((𝔡⁻¹ ^ 2) ^ (6 / 5 : ℝ)))] with n hmn hon hfn hAn hBwn hWOn hpn hbig
  obtain ⟨hg, hA1⟩ := hAn
  obtain ⟨-, hgΛ⟩ := hWOn
  obtain ⟨hN5, hNh⟩ := hpn
  have hN1 := cltFar_one_le_N sz n
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
  have hEn : |STflowE z n| < 2 := by have := hE n; linarith
  have hA0 : 0 < STAI sz n := lt_of_lt_of_le one_pos hA1
  change sz.seqP (badSetAt sz.size _ _ τ n) ≤ _
  refine (cltFar_union_bound sz.seqP _
    {ω | ∃ (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)),
      ((sz.W n : ℕ) : ℝ) ^ (-(6 * (d : ℝ) / 5 + ((d : ℝ) - 2) / 𝔠 + 1)) < ‖CltMom2.off sz n (STflowE z n) (s n) (t n) σ a ω‖}
    (fun q : {σ : Fin 2 → Bool // σ 0 ≠ σ 1} × (Fin 2 → Zd d (sz.L n)) =>
      {ω | ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * (STAI sz n ^ (-(6 / 5 : ℝ)) /
          (((zdistInf d (sz.L n) (q.2 0 - q.2 1) : ℕ) : ℝ) ^ (d - 2) + 1)) <
        ‖(((1 - s n) ^ 2 / (sz.lam n ^ 4 * (sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d) ^ (6 / 5 : ℝ)) : ℝ) : ℂ) *
          CltMom2.fluc sz n (STflowE z n) (s n) (t n) q.1.1 q.2 ω‖})
    (Real.rpow_nonneg hN0.le _) (Real.rpow_nonneg hN0.le _) ?_ hon (fun q => hfn q.1.1 q.1.2 q.2)).trans ?_
  · -- the bad event is covered
    intro ω hω
    obtain ⟨u, hu⟩ := hω
    by_contra hcon
    rw [Set.mem_union, not_or] at hcon
    obtain ⟨hc1, hc2⟩ := hcon
    have hoff' : ∀ (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)),
        ‖CltMom2.off sz n (STflowE z n) (s n) (t n) σ a ω‖ ≤ ((sz.W n : ℕ) : ℝ) ^ (-(6 * (d : ℝ) / 5 + ((d : ℝ) - 2) / 𝔠 + 1)) := by
      intro σ a
      by_contra h
      exact hc1 ⟨σ, a, not_le.1 h⟩
    have hfl' : ‖(((1 - s n) ^ 2 / (sz.lam n ^ 4 * (sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d) ^ (6 / 5 : ℝ)) : ℝ) : ℂ) *
        CltMom2.fluc sz n (STflowE z n) (s n) (t n) u.1.1.1 u.1.2 ω‖ ≤
        ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * (STAI sz n ^ (-(6 / 5 : ℝ)) /
          (((zdistInf d (sz.L n) (u.1.2 0 - u.1.2 1) : ℕ) : ℝ) ^ (d - 2) + 1)) := by
      by_contra h
      exact hc2 (Set.mem_iUnion.2 ⟨(u.1.1, u.1.2), not_le.1 h⟩)
    have hr : zdistInf d (sz.L n) (u.1.2 0 - u.1.2 1) ≤ sz.L n := st5_zdistInf_le sz n _
    have hζ := cltFar_zeta_ge hd sz n h𝔠 h𝔡 hA1 hg hgΛ hBwn _ hr hbig
    have hζ0 : 0 ≤ STAI sz n ^ (-(6 / 5 : ℝ)) / (((zdistInf d (sz.L n) (u.1.2 0 - u.1.2 1) : ℕ) : ℝ) ^ (d - 2) + 1) := by
      have : 0 ≤ STAI sz n ^ (-(6 / 5 : ℝ)) := Real.rpow_nonneg hA0.le _
      positivity
    have hfar := cltFar_far_le sz n u.1.1.1 u.1.2 ω hEn (hs1 n) hg (hmn u.1.1.1 u.1.2) hfl' (hoff' u.1.1.1 u.1.2) hζ hζ0 hNh
    have hNN : ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * ((sz.size n : ℕ) : ℝ) ^ (τ / 2) = ((sz.size n : ℕ) : ℝ) ^ τ := by
      rw [← Real.rpow_add hN0]; congr 1; ring
    rw [hNN] at hfar
    have hu' : ((sz.size n : ℕ) : ℝ) ^ τ * (STAI sz n ^ (-(6 / 5 : ℝ)) /
        (((zdistInf d (sz.L n) (u.1.2 0 - u.1.2 1) : ℕ) : ℝ) ^ (d - 2) + 1)) <
        ‖STfFar sz n (STflowE z n) (s n) (t n) u.1.1.1 u.1.2 ω‖ := hu
    linarith
  · -- the numerics
    apply ENNReal.ofReal_le_ofReal
    refine cltFar_union_numeric hN5 ?_
    have h1 : Fintype.card ({σ : Fin 2 → Bool // σ 0 ≠ σ 1} × (Fin 2 → Zd d (sz.L n))) =
        Fintype.card {σ : Fin 2 → Bool // σ 0 ≠ σ 1} * Fintype.card (Fin 2 → Zd d (sz.L n)) :=
      Fintype.card_prod _ _
    have h2 : Fintype.card {σ : Fin 2 → Bool // σ 0 ≠ σ 1} ≤ 4 := by
      have h := Fintype.card_subtype_le (fun σ : Fin 2 → Bool => σ 0 ≠ σ 1)
      have h' : Fintype.card (Fin 2 → Bool) = 4 := by simp
      omega
    rw [h1]
    push_cast
    have h3 := cltFar_card_pair_le sz n
    have h4 : ((Fintype.card {σ : Fin 2 → Bool // σ 0 ≠ σ 1} : ℕ) : ℝ) ≤ 4 := by exact_mod_cast h2
    calc ((Fintype.card {σ : Fin 2 → Bool // σ 0 ≠ σ 1} : ℕ) : ℝ) * ((Fintype.card (Fin 2 → Zd d (sz.L n)) : ℕ) : ℝ)
        ≤ 4 * ((sz.size n : ℕ) : ℝ) ^ 2 := mul_le_mul h4 h3 (Nat.cast_nonneg _) (by norm_num)

end Far

/-! ## 9. Compiled nonempty instances (`d = 3`)

The data is the merged sequence `szCL` of `RBM.Gauss.Step5Inst` (`d = 3`, `L_n = 2 (n+24)^5`, `W_n = 2^{n+24}`, `ilambda ≡ 1`, `s ≡ 0`,
`1 - t_n = L_n^{-2}`, `E_n = lemE z_n`, `𝔠 = 1/6`, `𝔡 = 1/10`); the index sets are nonempty at every `n`
(`szCL_cltFar_index_nonempty`).  The hypotheses that are other gates' unproved pins stay hypotheses of the examples:
`STStep2Concl` (for `STGdecayW`) and, for target 3, the nine stochastic premises of `inst_cltIso`. -/

section Instances

open RBM.Gauss.Step5Inst

private theorem cltFar_zCL_im (n : ℕ) : 0 < (zCL n).im := by
  have hL := szCL_two_le_L n
  change 0 < (((szCL.L n : ℕ) : ℝ) ^ 2)⁻¹ / 2
  positivity

/-- `|E_n| ≤ 1/2` along the flow of `szCL` (`|lemE z| ≤ |Re z|`, `Re zCL = 1/2`). -/
private theorem cltFar_zCL_E (n : ℕ) : |STflowE zCL n| ≤ 1 / 2 :=
  (abs_lemE_le (cltFar_zCL_im n)).trans (by simp [zCL])

private theorem cltFar_tCL_lt (n : ℕ) : tCL n < 1 := by
  have h := szCL_one_sub_t n
  have h2 : 0 < (((szCL.L n : ℕ) : ℝ) ^ 2)⁻¹ := by
    have := szCL_two_le_L n
    positivity
  linarith

private theorem cltFar_sCL_lt (n : ℕ) : sCL n < 1 := by
  change (0 : ℝ) < 1; norm_num

/-- **Instance of target 4** (the pin `STCltFar`) at `(szCL, zCL, sCL, tCL)`, `Cd = 1`: the index set is nonempty at every `n`
(`szCL_cltFar_index_nonempty`); the nine stochastic premises of the pin are inside `InstIng5Concl`. -/
example : InstIng5Concl (fun sz E s t => STCltFarConcl sz E s t) szCL zCL sCL tCL 1 :=
  inst_cltFar (stCltFar_holds 3) 1 one_pos

/-- The index set of `STCltFarConcl` at `(szCL, sCL, tCL)` is nonempty at every `n` (merged `szCL_cltFar_index_nonempty`): the instance
`inst_cltFar` below is not vacuous. -/
example (n : ℕ) := szCL_cltFar_index_nonempty n

/-- **Instance of target 1** (`cltFar_dom`) at `(szCL, 1/6, 1/10, STflowE zCL, sCL, tCL)`, `Cd = 1`, `(τ, D₁) = (1, 1)`, `σ = (+,-)`:
`Admissible` (`szCL_admissible`), `s < 1`, `s ≤ t` (`szCL_hst`), `STReg5I` (`szCL_reg5I`) are discharged; `STGdecayW` is
`(Eq:Gdecay_w)` (`h2.2.2`, another gate's pin).  The window is nonempty at every `n`: `β = (0, 0)` has `|β₀ - β₁| = 0`. -/
example (h2 : STStep2Concl szCL (STflowE zCL) sCL tCL 1) :
    ∀ᶠ n in atTop, CltMom2.DomHyp szCL n (STflowE zCL n) (sCL n) ![true, false]
        (((szCL.size n : ℕ) : ℝ) ^ (1 : ℝ)) (((szCL.size n : ℕ) : ℝ) ^ (-(1 : ℝ))) ∧
      szCL.seqP {ω | ((szCL.size n : ℕ) : ℝ) ^ (1 : ℝ) <
          ‖STcltB szCL n (STflowE zCL n) (sCL n) ![true, false] (![0, 0] : Fin 2 → Zd 3 (szCL.L n)) ω‖ *
            (((zdistInf 3 (szCL.L n) ((![0, 0] : Fin 2 → Zd 3 (szCL.L n)) 0 - (![0, 0] : Fin 2 → Zd 3 (szCL.L n)) 1) : ℕ) : ℝ) ^ (3 - 2) + 1)} ≤
        ENNReal.ofReal (((szCL.size n : ℕ) : ℝ) ^ (-(1 : ℝ))) := by
  filter_upwards [cltFar_dom 3 le_rfl szCL (1 / 6) (1 / 10) 1 (STflowE zCL) sCL tCL szCL_admissible
    cltFar_sCL_lt (fun n => (szCL_hst n).le) szCL_reg5I h2.2.2 1 1 one_pos one_pos] with n hn
  refine ⟨hn ![true, false], hn ![true, false] ![0, 0] ?_⟩
  have h0 : zdistInf 3 (szCL.L n) ((![0, 0] : Fin 2 → Zd 3 (szCL.L n)) 0 - (![0, 0] : Fin 2 → Zd 3 (szCL.L n)) 1) = 0 := by
    simp [zdistInf]
  rw [h0, Nat.cast_zero]
  have hlog : 0 ≤ Real.log ((szCL.W n : ℕ) : ℝ) := Real.log_nonneg (cltFar_one_le_W szCL n)
  have hℓ : 0 < ellT (szCL.L n) (szCL.lam n) (sCL n) := ellT_pos (cltFar_one_le_L szCL n)
  positivity

/-- **Instance of target 2** (`cltFar_off`) at the same data, `κ = 1/10` (`|E_n| ≤ 1/2 ≤ 2 - 1/10`), `0 ≤ s < t < 1`,
`(D, D') = (1, 1)`: `‖off_{σ,a}‖ ≤ W^{-1}` for every `(σ, a)` at once, off an event of probability `≤ N^{-1}`. -/
example (h2 : STStep2Concl szCL (STflowE zCL) sCL tCL 1) :
    ∀ᶠ n in atTop, szCL.seqP {ω | ∃ (σ : Fin 2 → Bool) (a : Fin 2 → Zd 3 (szCL.L n)),
        ((szCL.W n : ℕ) : ℝ) ^ (-(1 : ℝ)) < ‖CltMom2.off szCL n (STflowE zCL n) (sCL n) (tCL n) σ a ω‖} ≤
      ENNReal.ofReal (((szCL.size n : ℕ) : ℝ) ^ (-(1 : ℝ))) :=
  cltFar_off 3 le_rfl szCL (1 / 10) (1 / 6) (1 / 10) 1 (STflowE zCL) sCL tCL (by norm_num) szCL_admissible
    (fun n => (cltFar_zCL_E n).trans (by norm_num)) (fun _ => le_rfl) szCL_hst cltFar_tCL_lt szCL_reg5I h2.2.2
    1 1 one_pos one_pos

/-- **Instance of target 3** (`cltFar_fluc`) at the same data, `(τ, D) = (1/10, 1)`, `σ = (+,-)`, `a = (x_n, 0)`
(`|a₁ - a₂| = L_n/2`; the index `(σ, a)` is in the index set of `STCltFarConcl` by `szCL_cltFar_index_nonempty`): `STCltIsoConcl`
comes from the merged `inst_cltIso (stCltIso_holds 3) 1 one_pos`, whose nine stochastic premises (`STKbound … STLKU`, other gates'
pins) stay hypotheses of the example, as in `CltMoments2.lean:1604-1626`. -/
example (hK : STKbound szCL (STflowE zCL)) (hKw : STKward szCL (STflowE zCL)) (ha : STLK szCL (STflowE zCL) sCL)
    (hD : STDecay szCL (STflowE zCL) sCL) (hDS : STDecayStrong szCL (STflowE zCL) sCL)
    (h1 : STStep1Loop szCL (STflowE zCL) sCL tCL) (h2 : STStep2Concl szCL (STflowE zCL) sCL tCL 1)
    (h3 : STLmaxU szCL (STflowE zCL) sCL tCL) (h4 : STLKU szCL (STflowE zCL) sCL tCL) :
    ∀ᶠ n in atTop, szCL.seqP {ω | ((szCL.size n : ℕ) : ℝ) ^ (1 / 10 : ℝ) *
          (STAI szCL n ^ (-(6 / 5 : ℝ)) /
            (((zdistInf 3 (szCL.L n) ((![xCL n, 0] : Fin 2 → Zd 3 (szCL.L n)) 0 -
              (![xCL n, 0] : Fin 2 → Zd 3 (szCL.L n)) 1) : ℕ) : ℝ) ^ (3 - 2) + 1)) <
        ‖(((1 - sCL n) ^ 2 / (szCL.lam n ^ 4 * (szCL.lam n ^ 2 * ((szCL.W n : ℕ) : ℝ) ^ 3) ^ (6 / 5 : ℝ)) : ℝ) : ℂ) *
          CltMom2.fluc szCL n (STflowE zCL n) (sCL n) (tCL n) ![true, false] ![xCL n, 0] ω‖} ≤
      ENNReal.ofReal (((szCL.size n : ℕ) : ℝ) ^ (-(1 : ℝ))) := by
  obtain ⟨𝔠d, -, -, Hiso⟩ := inst_cltIso (stCltIso_holds 3) 1 one_pos
  have hiso : STCltIsoConcl szCL (STflowE zCL) sCL tCL := Hiso hK hKw ha hD hDS h1 h2 h3 h4
  filter_upwards [cltFar_fluc 3 le_rfl szCL (1 / 10) (1 / 6) (1 / 10) 1 (STflowE zCL) sCL tCL (by norm_num)
    szCL_admissible (fun n => (cltFar_zCL_E n).trans (by norm_num)) (fun _ => le_rfl) szCL_hst cltFar_tCL_lt szCL_reg5I
    h2.2.2 hiso (1 / 10) 1 (by norm_num) one_pos] with n hn
  exact hn ![true, false] (by decide) ![xCL n, 0]

end Instances

#print axioms cltFar_dom
#print axioms cltFar_off
#print axioms cltFar_fluc
#print axioms stCltFar_holds

end RBM.Gauss.Sizes

end
