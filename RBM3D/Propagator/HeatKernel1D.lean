/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# The one-dimensional heat kernel on `ℤ` and on `ℤ_L`

Route H (design `docs/reports/T2003-prove.md` b8 rows S1–S2 and ticket B1; Fable review
`docs/claude-team/fable/2026-10-02-routeH.md` F1–F2).  On `ℤ`,
`e^{-τΔ} = e^{-2τ} e^{τ(T + T⁻¹)}`, so the kernel is the Poisson series
`h_τ(n) = e^{-2τ} Σ_j τ^j N_j(n) / j!`, where `N_j(n)` counts the `±1`-sequences of length `j`
with sum `n`.  There is no contour shift and no Poisson measure: the series is summed against
`z^n` with the binomial theorem and Fubini over `ℕ × ℤ`.

The import of `Mathlib.Analysis.SpecialFunctions.Trigonometric.Series` is not used in this file;
it provides `Real.cosh_le_exp_half_sq` for the bounds file that imports this one (ticket T2009).

## Main definitions

* `RBM.Heat.walkCount`: `N_j(n)`.
* `RBM.Heat.hkZ`: the kernel `h_τ` on `ℤ`.
* `RBM.Heat.hkT`: the kernel `hk(τ, ·)` on `ℤ_L`, as a finite Fourier sum.

## Main results

* `RBM.Heat.hkZ_nonneg`, `RBM.Heat.hkZ_mass`, `RBM.Heat.hkZ_neg`: positivity, summability with total
  mass one, and symmetry.
* `RBM.Heat.hkZ_hasSum_mgf`: `Σ_n h_τ(n) z^n = exp(τ (z + z⁻¹) - 2τ)` for `z ≠ 0`.
* `RBM.Heat.hkZ_tilt`: the tilted inversion formula
  `e^{νn} h_τ(n) = (2π)⁻¹ ∫_{-π}^{π} e^{-ikn} exp(2τ (cosh (ν + ik) - 1)) dk`
  (the MGF at `z = e^{ν + ik}`, orthogonality of `e^{ikm}` on `[-π, π]`, and `∑'`/`∫` exchange).
* `RBM.Heat.hkT_hasSum_images`: `hk(τ, x) = Σ_y h_τ(x.val + L y)` (the MGF on the unit circle and
  finite orthogonality on `ℤ_L`).
* `RBM.Heat.hkT_mass`: `hk(τ, x) ≥ 0` and `Σ_x hk(τ, x) = 1`.

The finite orthogonality `sum_exp_orth` is adapted from `RBM2D/Propagator/Symbol.lean:144-149`
(`inv_mul_sum_stdAddChar`, commit `c9a24cf`).
-/

namespace RBM.Heat

/-- `N_j(n)`: the number of `±1`-sequences of length `j` whose sum is `n`. -/
def walkCount (j : ℕ) (n : ℤ) : ℕ :=
  ((Finset.univ : Finset (Fin j → Bool)).filter
    (fun ε => (∑ i, (if ε i then (1 : ℤ) else -1)) = n)).card

private lemma walkCount_neg (j : ℕ) (n : ℤ) : walkCount j (-n) = walkCount j n := by
  unfold walkCount
  have hneg : ∀ ε : Fin j → Bool,
      (∑ i, (if (fun i => !ε i) i then (1 : ℤ) else -1))
        = -(∑ i, (if ε i then (1 : ℤ) else -1)) := by
    intro ε
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    cases h : ε i <;> simp [h]
  refine Finset.card_nbij' (fun ε i => !ε i) (fun ε i => !ε i) ?_ ?_ ?_ ?_
  · intro ε hε
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hε ⊢
    rw [hneg, hε, neg_neg]
  · intro ε hε
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hε ⊢
    rw [hneg, hε]
  · intro ε _
    funext i
    simp
  · intro ε _
    funext i
    simp

private lemma zpow_sum_aux {K : Type*} [Field K] {ι : Type*} (z : K) (hz : z ≠ 0)
    (s : Finset ι) (a : ι → ℤ) : z ^ (∑ i ∈ s, a i) = ∏ i ∈ s, z ^ (a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.prod_insert hi, zpow_add₀ hz, ih]

private lemma walkCount_hasSum {K : Type*} [Field K] [TopologicalSpace K] (j : ℕ) (z : K)
    (hz : z ≠ 0) :
    HasSum (fun n : ℤ => (walkCount j n : K) * z ^ n) ((z + z⁻¹) ^ j) := by
  obtain ⟨S, hS⟩ : ∃ S : (Fin j → Bool) → ℤ,
      ∀ ε, S ε = ∑ i, (if ε i then (1 : ℤ) else -1) := ⟨_, fun _ => rfl⟩
  have hsupp : ∀ n ∉ Finset.univ.image S, (walkCount j n : K) * z ^ n = 0 := by
    intro n hn
    have h0 : walkCount j n = 0 := by
      unfold walkCount
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro ε _ hε
      exact hn (Finset.mem_image.mpr ⟨ε, Finset.mem_univ _, (hS ε).trans hε⟩)
    simp [h0]
  have h1 : HasSum (fun n : ℤ => (walkCount j n : K) * z ^ n)
      (∑ n ∈ Finset.univ.image S, (walkCount j n : K) * z ^ n) :=
    hasSum_sum_of_ne_finset_zero hsupp
  have h2 : ∑ n ∈ Finset.univ.image S, (walkCount j n : K) * z ^ n = (z + z⁻¹) ^ j := by
    calc ∑ n ∈ Finset.univ.image S, (walkCount j n : K) * z ^ n
        = ∑ n ∈ Finset.univ.image S, ∑ ε ∈ Finset.univ.filter (fun ε => S ε = n), z ^ S ε := by
          refine Finset.sum_congr rfl (fun n _ => ?_)
          have : walkCount j n = (Finset.univ.filter (fun ε : Fin j → Bool => S ε = n)).card := by
            unfold walkCount
            congr 1
            ext ε
            simp [hS]
          rw [Finset.sum_congr rfl (fun ε hε => by rw [(Finset.mem_filter.mp hε).2]),
            Finset.sum_const, nsmul_eq_mul, this]
      _ = ∑ ε, z ^ S ε :=
          Finset.sum_fiberwise_of_maps_to
            (fun ε _ => Finset.mem_image_of_mem S (Finset.mem_univ ε)) _
      _ = ∑ ε : Fin j → Bool, ∏ i, z ^ (if ε i then (1 : ℤ) else -1) := by
          refine Finset.sum_congr rfl (fun ε _ => ?_)
          rw [hS ε]
          exact zpow_sum_aux z hz _ _
      _ = (∑ b : Bool, z ^ (if b then (1 : ℤ) else -1)) ^ j :=
          (Fintype.sum_pow (fun b : Bool => z ^ (if b then (1 : ℤ) else -1)) j).symm
      _ = (z + z⁻¹) ^ j := by simp
  rw [h2] at h1
  exact h1

/-- The heat kernel of the 1D discrete Laplacian on `ℤ`, `h_τ(n) = e^{-2τ} Σ_j τ^j N_j(n) / j!`
(`= e^{-2τ} I_n(2τ)`; route H, step S1). -/
noncomputable def hkZ (τ : ℝ) (n : ℤ) : ℝ :=
  Real.exp (-2 * τ) * ∑' j : ℕ, τ ^ j * (walkCount j n : ℝ) / (Nat.factorial j : ℝ)

/-- The torus kernel `hk(τ, x) = L⁻¹ Σ_{k ∈ ℤ_L} cos(2πkx/L) e^{-2τ(1 - cos(2πk/L))}` (the kernel of
`e^{-τΔ}` on `ℤ_L`; route H, steps S1–S2). -/
noncomputable def hkT (L : ℕ) [NeZero L] (τ : ℝ) (x : ZMod L) : ℝ :=
  (L : ℝ)⁻¹ * ∑ k : ZMod L,
    Real.cos (2 * Real.pi * (k.val : ℝ) * (x.val : ℝ) / L)
      * Real.exp (-2 * τ * (1 - Real.cos (2 * Real.pi * (k.val : ℝ) / L)))

/-- Target 1 (`Nonneg`): positivity. -/
theorem hkZ_nonneg : ∀ τ : ℝ, 0 ≤ τ → ∀ n : ℤ, 0 ≤ hkZ τ n := by
  intro τ hτ n
  unfold hkZ
  exact mul_nonneg (Real.exp_pos _).le (tsum_nonneg fun j => by positivity)

/-- Target 3 (`Symm`): symmetry. -/
theorem hkZ_neg : ∀ τ : ℝ, ∀ n : ℤ, hkZ τ (-n) = hkZ τ n := by
  intro τ n
  simp only [hkZ, walkCount_neg]

/-- Target 4 (`MGF`): the moment generating function (Fable review F2 (i)). -/
theorem hkZ_hasSum_mgf : ∀ τ : ℝ, 0 ≤ τ → ∀ z : ℂ, z ≠ 0 →
    HasSum (fun n : ℤ => (hkZ τ n : ℂ) * z ^ n)
      (Complex.exp ((τ : ℂ) * (z + z⁻¹) - 2 * (τ : ℂ))) := by
  intro τ hτ z hz
  -- the Poisson coefficients
  obtain ⟨a, ha⟩ : ∃ a : ℕ → ℤ → ℝ, ∀ j n, a j n =
      τ ^ j * (walkCount j n : ℝ) / (Nat.factorial j : ℝ) := ⟨_, fun _ _ => rfl⟩
  have ha_nonneg : ∀ j n, 0 ≤ a j n := fun j n => by rw [ha]; positivity
  obtain ⟨F, hF⟩ : ∃ F : ℕ × ℤ → ℂ, ∀ p, F p = (a p.1 p.2 : ℂ) * z ^ p.2 :=
    ⟨_, fun _ => rfl⟩
  have hr : 0 < ‖z‖ := norm_pos_iff.mpr hz
  -- fibres over `j`
  have hfib_j : ∀ j : ℕ, HasSum (fun n : ℤ => F (j, n))
      (((τ : ℂ) ^ j / (Nat.factorial j : ℂ)) * (z + z⁻¹) ^ j) := by
    intro j
    have h := (walkCount_hasSum j z hz).mul_left ((τ : ℂ) ^ j / (Nat.factorial j : ℂ))
    convert h using 1
    funext n
    rw [hF, ha]
    push_cast
    ring
  have hnorm_j : ∀ j : ℕ, HasSum (fun n : ℤ => ‖F (j, n)‖)
      (τ ^ j / (Nat.factorial j : ℝ) * (‖z‖ + ‖z‖⁻¹) ^ j) := by
    intro j
    have h := (walkCount_hasSum j ‖z‖ hr.ne').mul_left (τ ^ j / (Nat.factorial j : ℝ))
    convert h using 1
    funext n
    rw [hF, norm_mul, norm_zpow, Complex.norm_real, Real.norm_of_nonneg (ha_nonneg j n), ha]
    ring
  have hsummable_norm : Summable (fun p : ℕ × ℤ => ‖F p‖) := by
    refine (summable_prod_of_nonneg (fun p => norm_nonneg _)).2 ⟨fun j => (hnorm_j j).summable, ?_⟩
    have h := Real.summable_pow_div_factorial (τ * (‖z‖ + ‖z‖⁻¹))
    refine h.congr (fun j => ?_)
    rw [(hnorm_j j).tsum_eq, mul_pow]
    ring
  have hsummable : Summable F := Summable.of_norm hsummable_norm
  have hS := hsummable.hasSum
  -- the total sum, by the fibres over `j`
  have hexp : HasSum (fun j : ℕ => ((τ : ℂ) ^ j / (Nat.factorial j : ℂ)) * (z + z⁻¹) ^ j)
      (Complex.exp ((τ : ℂ) * (z + z⁻¹))) := by
    have h := NormedSpace.expSeries_div_hasSum_exp ((τ : ℂ) * (z + z⁻¹))
    rw [← Complex.exp_eq_exp_ℂ] at h
    convert h using 1
    funext j
    rw [mul_pow]
    ring
  have hStot : ∑' p, F p = Complex.exp ((τ : ℂ) * (z + z⁻¹)) :=
    (hS.prod_fiberwise hfib_j).unique hexp
  -- the fibres over `n`
  have hS' : HasSum (F ∘ (Equiv.prodComm ℤ ℕ)) (∑' p, F p) := (Equiv.hasSum_iff _).mpr hS
  have hsummable' : Summable (F ∘ (Equiv.prodComm ℤ ℕ)) :=
    (Equiv.summable_iff (Equiv.prodComm ℤ ℕ)).mpr hsummable
  have hfib_n : HasSum (fun n : ℤ => ∑' j : ℕ, F (j, n)) (∑' p, F p) :=
    hS'.prod_fiberwise (fun n => (hsummable'.prod_factor n).hasSum)
  have h2 := hfib_n.mul_left (((Real.exp (-2 * τ) : ℝ)) : ℂ)
  rw [hStot] at h2
  convert h2 using 1
  · funext n
    have hsum_n : ∑' j : ℕ, F (j, n) = ((∑' j : ℕ, a j n : ℝ) : ℂ) * z ^ n := by
      rw [Complex.ofReal_tsum, ← tsum_mul_right]
      exact tsum_congr (fun j => hF (j, n))
    rw [hsum_n]
    simp only [hkZ, ha]
    push_cast
    ring
  · rw [Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    push_cast
    ring

/-- Target 2 (`Mass`): summability and total mass one. -/
theorem hkZ_mass : ∀ τ : ℝ, 0 ≤ τ → Summable (hkZ τ) ∧ ∑' n : ℤ, hkZ τ n = 1 := by
  intro τ hτ
  have h := hkZ_hasSum_mgf τ hτ 1 one_ne_zero
  have h1 : Complex.exp ((τ : ℂ) * (1 + 1⁻¹) - 2 * (τ : ℂ)) = ((1 : ℝ) : ℂ) := by
    have : (τ : ℂ) * (1 + 1⁻¹) - 2 * (τ : ℂ) = 0 := by ring
    rw [this, Complex.exp_zero, Complex.ofReal_one]
  rw [h1] at h
  simp only [one_zpow, mul_one] at h
  have h' : HasSum (hkZ τ) 1 := Complex.hasSum_ofReal.mp h
  exact ⟨h'.summable, h'.tsum_eq⟩

/-- Target 5 (`Tilt`): the tilted inversion formula (Fable review F2 (ii); no contour shift). -/
theorem hkZ_tilt : ∀ τ : ℝ, 0 ≤ τ → ∀ ν : ℝ, ∀ n : ℤ,
    ((Real.exp (ν * n) * hkZ τ n : ℝ) : ℂ) =
      ((2 * Real.pi : ℝ) : ℂ)⁻¹ * ∫ k in (-Real.pi)..Real.pi,
        Complex.exp (-((k : ℂ) * (n : ℂ)) * Complex.I)
          * Complex.exp (2 * (τ : ℂ) * (Complex.cosh ((ν : ℂ) + (k : ℂ) * Complex.I) - 1)) := by
  intro τ hτ ν n
  obtain ⟨G, hG⟩ : ∃ G : ℤ → ℝ → ℂ, ∀ m k, G m k = (hkZ τ m : ℂ) *
      Complex.exp ((m : ℂ) * ((ν : ℂ) + (k : ℂ) * Complex.I) - (k : ℂ) * (n : ℂ) * Complex.I) :=
    ⟨_, fun _ _ => rfl⟩
  -- the pointwise sum over `m` is the integrand (MGF at `z = e^{ν + ik}`)
  have hsum_pt : ∀ k : ℝ, HasSum (fun m : ℤ => G m k)
      (Complex.exp (-((k : ℂ) * (n : ℂ)) * Complex.I)
        * Complex.exp (2 * (τ : ℂ) *
          (Complex.cosh ((ν : ℂ) + (k : ℂ) * Complex.I) - 1))) := by
    intro k
    have hz : Complex.exp ((ν : ℂ) + (k : ℂ) * Complex.I) ≠ 0 := Complex.exp_ne_zero _
    have h := (hkZ_hasSum_mgf τ hτ _ hz).mul_left
      (Complex.exp (-((k : ℂ) * (n : ℂ)) * Complex.I))
    convert h using 1
    · funext m
      rw [hG, ← Complex.exp_int_mul, mul_left_comm, ← Complex.exp_add]
      congr 2
      ring
    · congr 2
      have h2 : Complex.exp ((ν : ℂ) + (k : ℂ) * Complex.I)
          + (Complex.exp ((ν : ℂ) + (k : ℂ) * Complex.I))⁻¹
          = 2 * Complex.cosh ((ν : ℂ) + (k : ℂ) * Complex.I) := by
        rw [Complex.two_cosh, Complex.exp_neg]
      rw [h2]
      ring
  have hG_cont : ∀ m : ℤ, Continuous (G m) := by
    intro m
    rw [show G m = fun k : ℝ => (hkZ τ m : ℂ) *
      Complex.exp ((m : ℂ) * ((ν : ℂ) + (k : ℂ) * Complex.I) - (k : ℂ) * (n : ℂ) * Complex.I)
      from funext (hG m)]
    fun_prop
  have hG_norm : ∀ m k, ‖G m k‖ = hkZ τ m * Real.exp (m * ν) := by
    intro m k
    rw [hG, norm_mul, Complex.norm_real, Real.norm_of_nonneg (hkZ_nonneg τ hτ m),
      Complex.norm_exp]
    congr 2
    simp
  have hsumm : Summable (fun m : ℤ => hkZ τ m * Real.exp (m * ν)) := by
    have h := (hkZ_hasSum_mgf τ hτ (Complex.exp (ν : ℂ)) (Complex.exp_ne_zero _)).summable
    have h' : Summable (fun m : ℤ => ((hkZ τ m * Real.exp (m * ν) : ℝ) : ℂ)) := by
      refine h.congr (fun m => ?_)
      rw [← Complex.exp_int_mul]
      push_cast
      rfl
    exact Complex.summable_ofReal.mp h'
  have hπ : -Real.pi ≤ Real.pi := by linarith [Real.pi_pos]
  have hint : ∀ m : ℤ, MeasureTheory.Integrable (G m)
      (MeasureTheory.volume.restrict (Set.Ioc (-Real.pi) Real.pi)) :=
    fun m => (hG_cont m).integrableOn_Ioc
  have hnormint : ∀ m : ℤ,
      ∫ k, ‖G m k‖ ∂(MeasureTheory.volume.restrict (Set.Ioc (-Real.pi) Real.pi))
        = (2 * Real.pi) * (hkZ τ m * Real.exp (m * ν)) := by
    intro m
    simp only [hG_norm]
    have hvol : (MeasureTheory.volume.restrict (Set.Ioc (-Real.pi) Real.pi)).real Set.univ
        = 2 * Real.pi := by
      rw [MeasureTheory.Measure.real, MeasureTheory.Measure.restrict_apply_univ,
        Real.volume_Ioc, ENNReal.toReal_ofReal (by linarith [Real.pi_pos])]
      ring
    rw [MeasureTheory.integral_const, smul_eq_mul, hvol]
  have hsumnorm : Summable (fun m : ℤ =>
      ∫ k, ‖G m k‖ ∂(MeasureTheory.volume.restrict (Set.Ioc (-Real.pi) Real.pi))) := by
    simp only [hnormint]
    exact hsumm.mul_left _
  have hHS := MeasureTheory.hasSum_integral_of_summable_integral_norm hint hsumnorm
  -- orthogonality of the exponentials on `[-π, π]`
  have hortho : ∀ m : ℤ, ∫ k in (-Real.pi)..Real.pi, G m k =
      if m = n then ((2 * Real.pi : ℝ) : ℂ) *
        ((hkZ τ n : ℂ) * Complex.exp ((n : ℂ) * (ν : ℂ))) else 0 := by
    intro m
    have hform : ∀ k : ℝ, G m k = ((hkZ τ m : ℂ) * Complex.exp ((m : ℂ) * (ν : ℂ))) *
        Complex.exp ((((m : ℂ) - (n : ℂ)) * Complex.I) * (k : ℂ)) := by
      intro k
      have h1 : Complex.exp ((m : ℂ) * ((ν : ℂ) + (k : ℂ) * Complex.I)
            - (k : ℂ) * (n : ℂ) * Complex.I)
          = Complex.exp ((m : ℂ) * (ν : ℂ))
            * Complex.exp ((((m : ℂ) - (n : ℂ)) * Complex.I) * (k : ℂ)) := by
        rw [← Complex.exp_add]
        congr 1
        ring
      rw [hG, h1]
      ring
    simp_rw [hform]
    rw [intervalIntegral.integral_const_mul]
    by_cases hmn : m = n
    · subst hmn
      simp
      ring
    · simp only [hmn, ↓reduceIte]
      have hc : (((m : ℂ) - (n : ℂ)) * Complex.I) ≠ 0 := by
        apply mul_ne_zero
        · rw [sub_ne_zero]; exact_mod_cast hmn
        · exact Complex.I_ne_zero
      rw [integral_exp_mul_complex hc]
      have h2 : Complex.exp ((((m : ℂ) - (n : ℂ)) * Complex.I) * (Real.pi : ℂ))
          = Complex.exp ((((m : ℂ) - (n : ℂ)) * Complex.I) * ((-Real.pi : ℝ) : ℂ)) := by
        have : (((m : ℂ) - (n : ℂ)) * Complex.I) * (Real.pi : ℂ)
            = (((m : ℂ) - (n : ℂ)) * Complex.I) * ((-Real.pi : ℝ) : ℂ)
              + (((m - n : ℤ) : ℂ)) * (2 * Real.pi * Complex.I) := by
          push_cast; ring
        rw [this, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
      rw [h2, sub_self, zero_div, mul_zero]
  have hHS' : HasSum (fun m : ℤ => ∫ k in (-Real.pi)..Real.pi, G m k)
      (∫ k in (-Real.pi)..Real.pi, ∑' m : ℤ, G m k) := by
    simp_rw [intervalIntegral.integral_of_le hπ]
    exact hHS
  have hlim : HasSum (fun m : ℤ => ∫ k in (-Real.pi)..Real.pi, G m k)
      (((2 * Real.pi : ℝ) : ℂ) * ((hkZ τ n : ℂ) * Complex.exp ((n : ℂ) * (ν : ℂ)))) := by
    simp_rw [hortho]
    exact hasSum_ite_eq n _
  have hval := hHS'.unique hlim
  have hpt : ∀ k : ℝ, ∑' m : ℤ, G m k = Complex.exp (-((k : ℂ) * (n : ℂ)) * Complex.I)
        * Complex.exp (2 * (τ : ℂ) * (Complex.cosh ((ν : ℂ) + (k : ℂ) * Complex.I) - 1)) :=
    fun k => (hsum_pt k).tsum_eq
  simp_rw [hpt] at hval
  rw [hval]
  have h2pi : ((2 * Real.pi : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (by positivity : (2 * Real.pi) ≠ 0)
  rw [← mul_assoc, inv_mul_cancel₀ h2pi, one_mul]
  push_cast
  rw [mul_comm (ν : ℂ) (n : ℂ)]
  ring

/-- Finite orthogonality of the exponentials `k ↦ e^{2πi k u / L}` on `ℤ_L` (the last two steps are
adapted from `RBM2D/Propagator/Symbol.lean:144-149` at `c9a24cf`, `inv_mul_sum_stdAddChar`). -/
private lemma sum_exp_orth (L : ℕ) [NeZero L] (u : ℤ) :
    ∑ k : ZMod L, Complex.exp (2 * Real.pi * Complex.I * (((k.val : ℤ) * u : ℤ) : ℂ) / (L : ℂ))
      = if (u : ZMod L) = 0 then (L : ℂ) else 0 := by
  have h1 : ∀ k : ZMod L,
      Complex.exp (2 * Real.pi * Complex.I * (((k.val : ℤ) * u : ℤ) : ℂ) / (L : ℂ))
        = ZMod.stdAddChar (k * (u : ZMod L)) := by
    intro k
    have hk : k * (u : ZMod L) = (((k.val : ℤ) * u : ℤ) : ZMod L) := by
      push_cast
      rw [ZMod.natCast_zmod_val]
    rw [hk, ZMod.stdAddChar_coe]
  simp_rw [h1]
  rw [AddChar.sum_mulShift _ (ZMod.isPrimitive_stdAddChar L), ZMod.card]
  split_ifs <;> simp

/-- The cosine version of the orthogonality, summed over the position variable. -/
private lemma sum_cos_orth (L : ℕ) [NeZero L] (k : ZMod L) :
    ∑ x : ZMod L, Real.cos (2 * Real.pi * (k.val : ℝ) * (x.val : ℝ) / L)
      = if k = 0 then (L : ℝ) else 0 := by
  have h := sum_exp_orth L (k.val : ℤ)
  have hk : (((k.val : ℤ)) : ZMod L) = k := by simp
  rw [hk] at h
  have h2 := congrArg Complex.re h
  rw [Complex.re_sum] at h2
  have h3 : ∀ x : ZMod L,
      (Complex.exp (2 * Real.pi * Complex.I * (((x.val : ℤ) * (k.val : ℤ) : ℤ) : ℂ)
        / (L : ℂ))).re = Real.cos (2 * Real.pi * (k.val : ℝ) * (x.val : ℝ) / L) := by
    intro x
    have : 2 * (Real.pi : ℂ) * Complex.I * (((x.val : ℤ) * (k.val : ℤ) : ℤ) : ℂ) / (L : ℂ)
        = ((2 * Real.pi * (k.val : ℝ) * (x.val : ℝ) / L : ℝ) : ℂ) * Complex.I := by
      push_cast
      ring
    rw [this, Complex.exp_ofReal_mul_I_re]
  simp_rw [h3] at h2
  rw [h2]
  split_ifs <;> simp

/-- The value of the moment generating function on the unit circle. -/
private lemma mgf_unit_circle (τ θ : ℝ) :
    Complex.exp ((τ : ℂ) * (Complex.exp ((θ : ℂ) * Complex.I)
        + (Complex.exp ((θ : ℂ) * Complex.I))⁻¹) - 2 * (τ : ℂ))
      = ((Real.exp (-2 * τ * (1 - Real.cos θ)) : ℝ) : ℂ) := by
  have h : Complex.exp ((θ : ℂ) * Complex.I) + (Complex.exp ((θ : ℂ) * Complex.I))⁻¹
      = 2 * (Real.cos θ : ℂ) := by
    rw [← Complex.exp_neg, Complex.ofReal_cos, Complex.two_cos, neg_mul]
  rw [h, Complex.ofReal_exp]
  congr 1
  push_cast
  ring

/-- The indicator of the residue class of `x` as a Fourier sum. -/
private lemma indicator_eq_sum (L : ℕ) [NeZero L] (x : ZMod L) (m : ℤ) :
    (if (m : ZMod L) = x then (1 : ℂ) else 0) =
      ∑ k : ZMod L, (L : ℂ)⁻¹
        * Complex.exp (((-(2 * Real.pi * (k.val : ℝ) * (x.val : ℝ) / L) : ℝ) : ℂ) * Complex.I)
        * (Complex.exp (((2 * Real.pi * (k.val : ℝ) / L : ℝ) : ℂ) * Complex.I)) ^ m := by
  have h := sum_exp_orth L (m - (x.val : ℤ))
  have hcond : ((m - (x.val : ℤ) : ℤ) : ZMod L) = 0 ↔ (m : ZMod L) = x := by
    push_cast
    rw [ZMod.natCast_zmod_val, sub_eq_zero]
  have hterm : ∀ k : ZMod L,
      (L : ℂ)⁻¹
        * Complex.exp (((-(2 * Real.pi * (k.val : ℝ) * (x.val : ℝ) / L) : ℝ) : ℂ) * Complex.I)
        * (Complex.exp (((2 * Real.pi * (k.val : ℝ) / L : ℝ) : ℂ) * Complex.I)) ^ m
      = (L : ℂ)⁻¹ * Complex.exp (2 * Real.pi * Complex.I
          * (((k.val : ℤ) * (m - (x.val : ℤ)) : ℤ) : ℂ) / (L : ℂ)) := by
    intro k
    rw [mul_assoc, ← Complex.exp_int_mul, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [Finset.sum_congr rfl (fun k _ => hterm k), ← Finset.mul_sum, h]
  have hL : (L : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne L)
  by_cases hmx : (m : ZMod L) = x
  · have h0 : ((m - (x.val : ℤ) : ℤ) : ZMod L) = 0 := hcond.mpr hmx
    simp only [h0, hmx, ↓reduceIte]
    field_simp
  · have h0 : ¬ ((m - (x.val : ℤ) : ℤ) : ZMod L) = 0 := fun h' => hmx (hcond.mp h')
    simp only [h0, hmx, ↓reduceIte, mul_zero]

/-- Target 6 (`Images`): the torus kernel is the periodisation of the `ℤ` kernel (images). -/
theorem hkT_hasSum_images : ∀ (L : ℕ) [NeZero L], ∀ τ : ℝ, 0 ≤ τ → ∀ x : ZMod L,
    HasSum (fun y : ℤ => hkZ τ ((x.val : ℤ) + (L : ℤ) * y)) (hkT L τ x) := by
  intro L _ τ hτ x
  have hL' : (L : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr (NeZero.ne L)
  -- the arithmetic progression `y ↦ x.val + L y`
  obtain ⟨P, hP⟩ : ∃ P : ℤ → ℤ, ∀ y, P y = (x.val : ℤ) + (L : ℤ) * y := ⟨_, fun _ => rfl⟩
  have hPinj : Function.Injective P := by
    intro y₁ y₂ h
    rw [hP, hP] at h
    exact mul_left_cancel₀ hL' (add_left_cancel h)
  have hPcast : ∀ y, ((P y : ℤ) : ZMod L) = x := by
    intro y
    rw [hP]
    push_cast
    rw [ZMod.natCast_self, zero_mul, add_zero, ZMod.natCast_zmod_val]
  have hPrange : ∀ m : ℤ, (m : ZMod L) = x → m ∈ Set.range P := by
    intro m hm
    have h0 : ((m - (x.val : ℤ) : ℤ) : ZMod L) = 0 := by
      push_cast
      rw [ZMod.natCast_zmod_val, hm, sub_self]
    obtain ⟨y, hy⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ L).mp h0
    exact ⟨y, by rw [hP]; linarith⟩
  -- the Fourier weights and the values of the moment generating function
  obtain ⟨w, hw⟩ : ∃ w : ZMod L → ℂ, ∀ k, w k = (L : ℂ)⁻¹
        * Complex.exp (((-(2 * Real.pi * (k.val : ℝ) * (x.val : ℝ) / L) : ℝ) : ℂ) * Complex.I) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨z, hz⟩ : ∃ z : ZMod L → ℂ, ∀ k,
      z k = Complex.exp (((2 * Real.pi * (k.val : ℝ) / L : ℝ) : ℂ) * Complex.I) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨g, hg⟩ : ∃ g : ZMod L → ℝ, ∀ k,
      g k = Real.exp (-2 * τ * (1 - Real.cos (2 * Real.pi * (k.val : ℝ) / L))) :=
    ⟨_, fun _ => rfl⟩
  have hz0 : ∀ k, z k ≠ 0 := fun k => by rw [hz]; exact Complex.exp_ne_zero _
  have hmgf : ∀ k : ZMod L, HasSum (fun m : ℤ => w k * ((hkZ τ m : ℂ) * (z k) ^ m))
      (w k * ((g k : ℝ) : ℂ)) := by
    intro k
    have h := (hkZ_hasSum_mgf τ hτ (z k) (hz0 k)).mul_left (w k)
    rw [hz k, mgf_unit_circle, ← hg k] at h
    rwa [hz k]
  have hsum : HasSum (fun m : ℤ => ∑ k : ZMod L, w k * ((hkZ τ m : ℂ) * (z k) ^ m))
      (∑ k : ZMod L, w k * ((g k : ℝ) : ℂ)) := hasSum_sum (fun k _ => hmgf k)
  -- identify the summand with `h(m) 1_{m ≡ x}`
  have hf : ∀ m : ℤ, ∑ k : ZMod L, w k * ((hkZ τ m : ℂ) * (z k) ^ m)
      = (hkZ τ m : ℂ) * (if (m : ZMod L) = x then (1 : ℂ) else 0) := by
    intro m
    rw [indicator_eq_sum L x m, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [hw, hz]
    ring
  have hsum' : HasSum (fun m : ℤ => (hkZ τ m : ℂ) * (if (m : ZMod L) = x then (1 : ℂ) else 0))
      (∑ k : ZMod L, w k * ((g k : ℝ) : ℂ)) := by
    simpa only [hf] using hsum
  -- restrict to the progression
  have hvanish : ∀ m ∉ Set.range P,
      (hkZ τ m : ℂ) * (if (m : ZMod L) = x then (1 : ℂ) else 0) = 0 := by
    intro m hm
    have : ¬ (m : ZMod L) = x := fun h => hm (hPrange m h)
    simp [this]
  have hcomp := (hPinj.hasSum_iff hvanish).mpr hsum'
  have hcomp' : HasSum (fun y : ℤ => (hkZ τ (P y) : ℂ)) (∑ k : ZMod L, w k * ((g k : ℝ) : ℂ)) := by
    have heq : (fun y : ℤ => (hkZ τ (P y) : ℂ)) =
        ((fun m : ℤ => (hkZ τ m : ℂ) * (if (m : ZMod L) = x then (1 : ℂ) else 0)) ∘ P) := by
      funext y
      simp [Function.comp, hPcast y]
    rw [heq]
    exact hcomp
  -- real part
  have hre := Complex.hasSum_re hcomp'
  simp only [Complex.ofReal_re] at hre
  have hV : (∑ k : ZMod L, w k * ((g k : ℝ) : ℂ)).re = hkT L τ x := by
    rw [Complex.re_sum]
    unfold hkT
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    have h1 : w k * ((g k : ℝ) : ℂ) = (((L : ℝ)⁻¹ * g k : ℝ) : ℂ) *
        Complex.exp (((-(2 * Real.pi * (k.val : ℝ) * (x.val : ℝ) / L) : ℝ) : ℂ) * Complex.I) := by
      rw [hw]
      push_cast
      ring
    rw [h1, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re, Real.cos_neg, hg]
    ring
  rw [hV] at hre
  simpa only [hP] using hre

/-- Target 7 (`TorusMass`): the torus kernel is a probability on `ℤ_L`. -/
theorem hkT_mass : ∀ (L : ℕ) [NeZero L], ∀ τ : ℝ, 0 ≤ τ →
    (∀ x : ZMod L, 0 ≤ hkT L τ x) ∧ ∑ x : ZMod L, hkT L τ x = 1 := by
  intro L _ τ hτ
  refine ⟨fun x => ?_, ?_⟩
  · exact (hkT_hasSum_images L τ hτ x).nonneg (fun y => hkZ_nonneg τ hτ _)
  · have hL : (L : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne L)
    unfold hkT
    rw [← Finset.mul_sum, Finset.sum_comm]
    have h1 : ∀ k : ZMod L, ∑ x : ZMod L, Real.cos (2 * Real.pi * (k.val : ℝ) * (x.val : ℝ) / L)
        * Real.exp (-2 * τ * (1 - Real.cos (2 * Real.pi * (k.val : ℝ) / L)))
        = (if k = 0 then (L : ℝ) else 0)
          * Real.exp (-2 * τ * (1 - Real.cos (2 * Real.pi * (k.val : ℝ) / L))) := by
      intro k
      rw [← Finset.sum_mul, sum_cos_orth]
    simp_rw [h1]
    simp [hL]

/-! ### Compiled instances

Each target theorem applied at concrete nondegenerate data (`τ = 1`, `L = 5`, `x = 2`, `ν = 1/2`,
`n = 3`); every deterministic hypothesis is discharged. -/

-- `hkZ_nonneg` at `τ = 1`, `n = 2`.
example : 0 ≤ hkZ 1 2 := hkZ_nonneg 1 zero_le_one 2

-- `hkZ_mass` at `τ = 1`: `h_1` is summable on `ℤ` with total mass one.
example : Summable (hkZ 1) ∧ ∑' n : ℤ, hkZ 1 n = 1 := hkZ_mass 1 zero_le_one

-- `hkZ_neg` at `τ = 1`, `n = 3`.
example : hkZ 1 (-3) = hkZ 1 3 := hkZ_neg 1 3

-- `hkZ_hasSum_mgf` at `τ = 1`, `z = 2`.
example : HasSum (fun n : ℤ => (hkZ 1 n : ℂ) * (2 : ℂ) ^ n)
    (Complex.exp (((1 : ℝ) : ℂ) * ((2 : ℂ) + (2 : ℂ)⁻¹) - 2 * ((1 : ℝ) : ℂ))) :=
  hkZ_hasSum_mgf 1 zero_le_one 2 two_ne_zero

-- `hkZ_tilt` at `τ = 1`, `ν = 1/2`, `n = 3`.
example : ((Real.exp ((1 / 2 : ℝ) * ((3 : ℤ) : ℝ)) * hkZ 1 3 : ℝ) : ℂ) =
    ((2 * Real.pi : ℝ) : ℂ)⁻¹ * ∫ k in (-Real.pi)..Real.pi,
      Complex.exp (-((k : ℂ) * ((3 : ℤ) : ℂ)) * Complex.I)
        * Complex.exp (2 * ((1 : ℝ) : ℂ) *
          (Complex.cosh (((1 / 2 : ℝ) : ℂ) + (k : ℂ) * Complex.I) - 1)) :=
  hkZ_tilt 1 zero_le_one (1 / 2) 3

-- `hkT_hasSum_images` at `L = 5`, `τ = 1`, `x = 2`.
example : HasSum (fun y : ℤ => hkZ 1 (((2 : ZMod 5).val : ℤ) + ((5 : ℕ) : ℤ) * y))
    (hkT 5 1 2) :=
  hkT_hasSum_images 5 1 zero_le_one 2

-- `hkT_mass` at `L = 5`, `τ = 1`.
example : (∀ x : ZMod 5, 0 ≤ hkT 5 1 x) ∧ ∑ x : ZMod 5, hkT 5 1 x = 1 :=
  hkT_mass 5 1 zero_le_one

end RBM.Heat
