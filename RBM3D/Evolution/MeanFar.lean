/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Evolution.ExpInv
import RBM3D.Propagator.Prop5Hold
import RBM3D.Propagator.Prop6Hold
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# S5-22b (ST-4): the mean part `𝔼 f^{far}` of the CLT step of case (i) (ticket T2157)

Paper: arXiv:2507.20274, `paper/tex/3_5_Loop_Hierarchy.tex` (`3_5:line`): `lem;CLT`
(`3_5:2173-2176`), its proof `3_5:2182-2212`, `(eq:boundEfar)` (`3_5:2211`), `(eq:propcalB)`
(`3_5:2139-2150`).  The propagator pins `(prop:ThfadC)`, `(prop:BD2)` are `Prop5Decay`,
`Prop7Diff2` (proved: `prop5Decay_holds`, `prop7Diff2_holds`).  The fluctuation part
`f^{far} - 𝔼 f^{far}` (`STCltFar`) is S5-25.

**Targets.**
1. `meanFar_core` (section 2), the deterministic core: for a translation-invariant, symmetric
   kernel `B` and a propagator profile `T = Θ_t(0, ·)`,
   `|∑_{b₁∈S} ∑_{b₂} T(b₁-a₁) B_{b₁b₂} (T(a₂-b₂) - T(a₂-b₁))|` is at most
   `C_d K₁ K₂ K (1 + log(L+1)) (w₁+1)⁴ / (|a₁-a₂|_∞+1)^{d-2} + 2 K₁² K' L^{2d}`.
   The first difference is half the second difference (`meanFar_identity`: `b₂ ↦ b₁+b₁-b₂`);
   `(prop:BD2)` is the hypothesis `hT2` on the `ℓ¹`-window `|r|₁ ≤ w₁`, `(prop:ThfadC)` is `hT1`,
   `(eq:propcalB)` is `hB1`/`hB2`.
2. `stMeanFar : STMeanFar d` (section 8): under `STIngR5 d STReg5I`,
   `‖𝔼 f^{far}_{σ,a}‖ ≺ A^{-6/5} / (|a₁-a₂|^{d-2} + 1)`, `A = ilambda² W^d`, on the index set of
   `STCltFarConcl`; the underlying `meanFar_eventually` holds for every `σ` and `a`.
   `B = 𝔼 (𝓛-𝒦)^{(2)}_{s,σ}` is translation invariant and symmetric by `stExpInv_holds` and the
   properties 1, 2 of `Θ`; its decay is `(Eq:Gdecay_w)` at `u = s` (`STGdecayW`) off an event of
   probability `≤ N^{-D₁}`, plus the a.s. envelope `|𝓛^{(2)}_s| ≤ η_s^{-2}` (`norm_Lloop_le`)
   on that event (section 4).

Sections: 1 lattice sums on `Z_L^d` (shells, ball sums, the `b₁`-sum with its logarithm);
2 the core; 3 `meanFar_T1`, `meanFar_T2` (the pins in the shape of `hT1`, `hT2`); 4 `𝔼𝓑`;
5-6 the numerics at one index `n` (`meanFar_numeric_main`, `meanFar_tiny`, `meanFar_at_n`);
7 facts about `N`; 8 `meanFar_eventually`, `stMeanFar`; 9 compiled instances at `d = 3`.
Every helper is `private` or prefixed `meanFar_`.

Differences from the paper (paper-delta candidates `T2157a`-`T2157d`, see the prove report):
(a) the paper's `≺` hides `(log W)^{12}` and a `log L`: the proof gives `(d (log W)³ ℓ_s + 1)⁴`
(the window is `w₁ = d (log W)³ ℓ_s`) and `1 + log(L+1)` (the `b₁`-sum
`∑_b (|b-a₂|+1)^{-d}` is logarithmic); both are absorbed by `N^τ`;
(b) the window of the core is in `ℓ¹` (`(prop:BD2)` is stated in `ℓ¹`), the decay profiles are
in `ℓ^∞`;
(c) the mean part uses neither `σ₁ ≠ σ₂` nor `(eq:ells_to_ellt)`, `(eq:ells_to_ellt2)`;
(d) `≺ ⟹ 𝔼`: the paper applies `(eq:propcalB)` to `𝔼𝓑`; here it is the a.s. envelope plus the
bad event, with `D₁ = 5d+19`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false



noncomputable section

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal

namespace RBM.Gauss.Sizes

open RBM RBM.Loop RBM.Path RBM.Gauss

/-! ## 1. Counting and lattice sums on `Z_L^d` -/

section Lattice

variable {d L : ℕ} [NeZero L]

private theorem meanFar_zdistInf_le (x : Zd d L) : zdistInf d L x ≤ L :=
  Finset.sup_le fun _ _ => (min_le_right _ _).trans (Nat.sub_le _ _)

private theorem meanFar_zdistInf_neg (x : Zd d L) : zdistInf d L (-x) = zdistInf d L x := by
  simp only [zdistInf, Pi.neg_apply, zdist_neg]

private theorem meanFar_zdistInf_add_le (x y : Zd d L) :
    zdistInf d L (x + y) ≤ zdistInf d L x + zdistInf d L y := by
  refine Finset.sup_le fun i _ => ?_
  change zdist L (x i + y i) ≤ _
  refine (zdist_add_le L (x i) (y i)).trans (add_le_add ?_ ?_)
  · exact Finset.le_sup (f := fun j => zdist L (x j)) (Finset.mem_univ i)
  · exact Finset.le_sup (f := fun j => zdist L (y j)) (Finset.mem_univ i)

private theorem meanFar_zdistInf_zero : zdistInf d L (0 : Zd d L) = 0 := by
  simp [zdistInf]

/-- The shell `{x : |x|_∞ = k}` of `Z_L^d` has at most `d · 2 (2k+1)^{d-1}` points. -/
private theorem meanFar_card_shell (hd : 1 ≤ d) (k : ℕ) :
    (Finset.univ.filter fun x : Zd d L => zdistInf d L x = k).card ≤
      d * (2 * (2 * k + 1) ^ (d - 1)) := by
  classical
  set Seq : Finset (ZMod L) := Finset.univ.filter fun u => zdist L u = k with hSeq
  set Sle : Finset (ZMod L) := Finset.univ.filter fun u => zdist L u ≤ k with hSle
  have hSeq_card : Seq.card ≤ 2 := card_zdist_eq_le k
  have hSle_card : Sle.card ≤ 2 * k + 1 := card_zdist_le_le k
  have hcover : (Finset.univ.filter fun x : Zd d L => zdistInf d L x = k) ⊆
      Finset.univ.biUnion (fun i : Fin d =>
        Fintype.piFinset (fun j : Fin d => if j = i then Seq else Sle)) := by
    intro x hx
    have hxk : zdistInf d L x = k := (Finset.mem_filter.1 hx).2
    have hne : (Finset.univ : Finset (Fin d)).Nonempty := ⟨⟨0, hd⟩, Finset.mem_univ _⟩
    obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup Finset.univ hne (fun j => zdist L (x j))
    have hik : zdist L (x i) = k := by
      have : zdistInf d L x = zdist L (x i) := hi
      omega
    refine Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, ?_⟩
    rw [Fintype.mem_piFinset]
    intro j
    by_cases hj : j = i
    · subst hj
      simp [hSeq, hik]
    · have hjle : zdist L (x j) ≤ k := by
        have := Finset.le_sup (f := fun l => zdist L (x l)) (Finset.mem_univ j)
        have h2 : zdistInf d L x = Finset.univ.sup fun l => zdist L (x l) := rfl
        omega
      simp [hj, hSle, hjle]
  have hone : ∀ i : Fin d,
      (Fintype.piFinset (fun j : Fin d => if j = i then Seq else Sle)).card ≤
        2 * (2 * k + 1) ^ (d - 1) := by
    intro i
    rw [Fintype.card_piFinset]
    have hle : ∏ j : Fin d, (if j = i then Seq else Sle).card ≤
        ∏ j : Fin d, (if j = i then 2 else 2 * k + 1) := by
      refine Finset.prod_le_prod₀ (fun _ _ => Nat.zero_le _) fun j _ => ?_
      by_cases hj : j = i
      · simp [hj, hSeq_card]
      · simp [hj, hSle_card]
    refine hle.trans (le_of_eq ?_)
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
    have : ∏ j ∈ Finset.univ.erase i, (if j = i then 2 else 2 * k + 1) =
        ∏ _j ∈ Finset.univ.erase i, (2 * k + 1) :=
      Finset.prod_congr rfl fun j hj => by simp [Finset.ne_of_mem_erase hj]
    rw [this, Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ i)]
    simp
  calc (Finset.univ.filter fun x : Zd d L => zdistInf d L x = k).card
      ≤ (Finset.univ.biUnion (fun i : Fin d =>
        Fintype.piFinset (fun j : Fin d => if j = i then Seq else Sle))).card :=
        Finset.card_le_card hcover
    _ ≤ ∑ i : Fin d, (Fintype.piFinset (fun j : Fin d => if j = i then Seq else Sle)).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ _i : Fin d, 2 * (2 * k + 1) ^ (d - 1) := Finset.sum_le_sum fun i _ => hone i
    _ = d * (2 * (2 * k + 1) ^ (d - 1)) := by simp

/-- The constant of the shell count: `#{x : |x|_∞ = k} ≤ cs (k+1)^{d-1}`, `cs = 2 d 2^{d-1}`. -/
private def meanFar_cs (d : ℕ) : ℝ := 2 * d * 2 ^ (d - 1)

private theorem meanFar_cs_pos (hd : 1 ≤ d) : 0 < meanFar_cs d := by
  unfold meanFar_cs
  have : (0 : ℝ) < d := by exact_mod_cast hd
  positivity

private theorem meanFar_card_shell_real (hd : 1 ≤ d) (k : ℕ) :
    ((Finset.univ.filter fun x : Zd d L => zdistInf d L x = k).card : ℝ) ≤
      meanFar_cs d * ((k : ℝ) + 1) ^ (d - 1) := by
  have h := meanFar_card_shell (d := d) (L := L) hd k
  have h1 : ((Finset.univ.filter fun x : Zd d L => zdistInf d L x = k).card : ℝ) ≤
      ((d * (2 * (2 * k + 1) ^ (d - 1)) : ℕ) : ℝ) := by exact_mod_cast h
  refine h1.trans ?_
  push_cast
  have h2 : (2 * (k : ℝ) + 1) ^ (d - 1) ≤ (2 * ((k : ℝ) + 1)) ^ (d - 1) :=
    pow_le_pow_left₀ (by positivity) (by linarith) _
  rw [mul_pow] at h2
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  unfold meanFar_cs
  calc (d : ℝ) * (2 * (2 * (k : ℝ) + 1) ^ (d - 1))
      = 2 * d * (2 * (k : ℝ) + 1) ^ (d - 1) := by ring
    _ ≤ 2 * d * (2 ^ (d - 1) * ((k : ℝ) + 1) ^ (d - 1)) := by gcongr
    _ = 2 * d * 2 ^ (d - 1) * ((k : ℝ) + 1) ^ (d - 1) := by ring

/-- Sum over the lattice of a function of `|x|_∞`, by shells. -/
private theorem meanFar_sum_shell (hd : 1 ≤ d) (F : ℕ → ℝ) (hF : ∀ k, 0 ≤ F k) :
    ∑ x : Zd d L, F (zdistInf d L x) ≤
      ∑ k ∈ Finset.range (L + 1), meanFar_cs d * ((k : ℝ) + 1) ^ (d - 1) * F k := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.range (L + 1))
    (g := zdistInf d L) (fun x _ => Finset.mem_range.2 (Nat.lt_succ_of_le (meanFar_zdistInf_le x)))]
  refine Finset.sum_le_sum fun k _ => ?_
  have hk : ∑ x ∈ Finset.univ.filter (fun x : Zd d L => zdistInf d L x = k), F (zdistInf d L x) =
      ((Finset.univ.filter fun x : Zd d L => zdistInf d L x = k).card : ℝ) * F k := by
    rw [Finset.sum_congr rfl (fun x hx => by rw [(Finset.mem_filter.1 hx).2])]
    simp
  rw [hk]
  exact mul_le_mul_of_nonneg_right (meanFar_card_shell_real hd k) (hF k)

/-- `∑_x (|x|_∞ + 1)^{-d} ≤ cs (1 + log (L+1))`: the logarithmic lattice sum. -/
private theorem meanFar_sum_inv_pow (hd : 1 ≤ d) :
    ∑ x : Zd d L, 1 / (((zdistInf d L x : ℕ) : ℝ) + 1) ^ d ≤
      meanFar_cs d * (1 + Real.log ((L : ℝ) + 1)) := by
  have h := meanFar_sum_shell (d := d) (L := L) hd (fun k => 1 / ((k : ℝ) + 1) ^ d)
    (fun k => by positivity)
  refine h.trans ?_
  have hterm : ∀ k ∈ Finset.range (L + 1),
      meanFar_cs d * ((k : ℝ) + 1) ^ (d - 1) * (1 / ((k : ℝ) + 1) ^ d) =
        meanFar_cs d * ((k : ℝ) + 1)⁻¹ := by
    intro k _
    have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    have e : ((k : ℝ) + 1) ^ d = ((k : ℝ) + 1) ^ (d - 1) * ((k : ℝ) + 1) := by
      rw [← pow_succ, Nat.sub_add_cancel hd]
    rw [e]
    field_simp
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ (meanFar_cs_pos hd).le
  have hH := harmonic_le_one_add_log (L + 1)
  have hH' : ((harmonic (L + 1) : ℚ) : ℝ) = ∑ k ∈ Finset.range (L + 1), ((k : ℝ) + 1)⁻¹ := by
    simp [harmonic]
  rw [← hH']
  have : ((L + 1 : ℕ) : ℝ) = (L : ℝ) + 1 := by push_cast; ring
  rw [this] at hH
  exact hH

/-- The ball sums: for `R ≥ 0` and a power `j`,
`∑_{|x|_∞ ≤ R} (|x|_∞+1)^j / (|x|_∞+1)^{d-2} ≤ cs (R+1)^{j+2}`. -/
private theorem meanFar_sum_ball (hd : 3 ≤ d) (j : ℕ) {R : ℝ} (hR : 0 ≤ R) :
    ∑ x ∈ Finset.univ.filter (fun x : Zd d L => ((zdistInf d L x : ℕ) : ℝ) ≤ R),
        (((zdistInf d L x : ℕ) : ℝ) + 1) ^ j / (((zdistInf d L x : ℕ) : ℝ) + 1) ^ (d - 2) ≤
      meanFar_cs d * (R + 1) ^ (j + 2) := by
  classical
  set F : ℕ → ℝ := fun k => if (k : ℝ) ≤ R then ((k : ℝ) + 1) ^ j / ((k : ℝ) + 1) ^ (d - 2) else 0
    with hFdef
  have hF0 : ∀ k, 0 ≤ F k := fun k => by
    simp only [hFdef]; split_ifs <;> positivity
  have hle : ∑ x ∈ Finset.univ.filter (fun x : Zd d L => ((zdistInf d L x : ℕ) : ℝ) ≤ R),
        (((zdistInf d L x : ℕ) : ℝ) + 1) ^ j / (((zdistInf d L x : ℕ) : ℝ) + 1) ^ (d - 2) ≤
      ∑ x : Zd d L, F (zdistInf d L x) := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun x : Zd d L => ((zdistInf d L x : ℕ) : ℝ) ≤ R) (fun x => F (zdistInf d L x))]
    have h1 : ∑ x ∈ Finset.univ.filter (fun x : Zd d L => ((zdistInf d L x : ℕ) : ℝ) ≤ R),
        (((zdistInf d L x : ℕ) : ℝ) + 1) ^ j / (((zdistInf d L x : ℕ) : ℝ) + 1) ^ (d - 2) =
      ∑ x ∈ Finset.univ.filter (fun x : Zd d L => ((zdistInf d L x : ℕ) : ℝ) ≤ R),
        F (zdistInf d L x) :=
      Finset.sum_congr rfl fun x hx => by simp [hFdef, (Finset.mem_filter.1 hx).2]
    rw [h1]
    have : 0 ≤ ∑ x ∈ Finset.univ.filter (fun x : Zd d L => ¬ ((zdistInf d L x : ℕ) : ℝ) ≤ R),
        F (zdistInf d L x) := Finset.sum_nonneg fun x _ => hF0 _
    linarith
  refine hle.trans ((meanFar_sum_shell (by omega) F hF0).trans ?_)
  -- the one-dimensional sum
  have hterm : ∀ k ∈ Finset.range (L + 1),
      meanFar_cs d * ((k : ℝ) + 1) ^ (d - 1) * F k ≤
        if (k : ℝ) ≤ R then meanFar_cs d * (R + 1) ^ (j + 1) else 0 := by
    intro k _
    by_cases hk : (k : ℝ) ≤ R
    · simp only [hFdef, hk, ↓reduceIte]
      have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
      have e : ((k : ℝ) + 1) ^ (d - 1) = ((k : ℝ) + 1) ^ (d - 2) * ((k : ℝ) + 1) := by
        rw [← pow_succ, show d - 2 + 1 = d - 1 by omega]
      have e2 : meanFar_cs d * ((k : ℝ) + 1) ^ (d - 1) *
          (((k : ℝ) + 1) ^ j / ((k : ℝ) + 1) ^ (d - 2)) =
          meanFar_cs d * (((k : ℝ) + 1) ^ j * ((k : ℝ) + 1)) := by
        rw [e]; field_simp
      rw [e2]
      have : ((k : ℝ) + 1) ^ j * ((k : ℝ) + 1) ≤ (R + 1) ^ (j + 1) := by
        rw [← pow_succ]
        exact pow_le_pow_left₀ hk1.le (by linarith) _
      exact mul_le_mul_of_nonneg_left this (meanFar_cs_pos (by omega)).le
    · simp [hFdef, hk]
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.sum_filter]
  have hsub : (Finset.range (L + 1)).filter (fun k : ℕ => (k : ℝ) ≤ R) ⊆
      Finset.range (⌊R⌋₊ + 1) := by
    intro k hk
    have hk' : (k : ℝ) ≤ R := (Finset.mem_filter.1 hk).2
    exact Finset.mem_range.2 (Nat.lt_succ_of_le (Nat.le_floor hk'))
  have hcard : (((Finset.range (L + 1)).filter (fun k : ℕ => (k : ℝ) ≤ R)).card : ℝ) ≤ R + 1 := by
    have h1 := Finset.card_le_card hsub
    rw [Finset.card_range] at h1
    have h2 : ((⌊R⌋₊ : ℕ) : ℝ) ≤ R := Nat.floor_le hR
    have h3 : (((⌊R⌋₊ + 1 : ℕ)) : ℝ) ≥ ((Finset.filter (fun k : ℕ => (k : ℝ) ≤ R) (Finset.range (L + 1))).card : ℝ) := by
      exact_mod_cast h1
    push_cast at h3
    linarith
  rw [Finset.sum_const, nsmul_eq_mul]
  calc _ ≤ (R + 1) * (meanFar_cs d * (R + 1) ^ (j + 1)) :=
        mul_le_mul_of_nonneg_right hcard (by have := meanFar_cs_pos (d := d) (by omega); positivity)
    _ = meanFar_cs d * (R + 1) ^ (j + 2) := by ring

/-- Translation of the summation variable. -/
private theorem meanFar_sum_sub {M : Type*} [AddCommMonoid M] (f : Zd d L → M) (x : Zd d L) :
    ∑ b : Zd d L, f (b - x) = ∑ b : Zd d L, f b :=
  Fintype.sum_equiv (Equiv.subRight x) _ _ (fun _ => rfl)

/-- The constant of the pair sum. -/
private def meanFar_Cpair (d : ℕ) : ℝ := 2 ^ (d - 1) * meanFar_cs d

/-- **The `b₁`-sum** (`(eq:boundEfar)`, `3_5:2211`): `∑_b (|b-x|+1)^{-(d-2)} (|b-y|+1)^{-d} ≤
C (1 + log (L+1)) (|x-y|+1)^{-(d-2)}`.  The factor `|b-y|^{-d}` is critical at `b = y`: the log. -/
private theorem meanFar_pair_sum (hd : 3 ≤ d) (x y : Zd d L) :
    ∑ b : Zd d L, 1 / ((((zdistInf d L (b - x) : ℕ) : ℝ) + 1) ^ (d - 2) *
        (((zdistInf d L (b - y) : ℕ) : ℝ) + 1) ^ d) ≤
      meanFar_Cpair d * (1 + Real.log ((L : ℝ) + 1)) /
        (((zdistInf d L (x - y) : ℕ) : ℝ) + 1) ^ (d - 2) := by
  classical
  set D : ℕ := zdistInf d L (x - y) with hD
  set Dr : ℝ := (D : ℝ) with hDr
  have hDr0 : (0 : ℝ) ≤ Dr := Nat.cast_nonneg _
  have hh : (0 : ℝ) < Dr / 2 + 1 := by positivity
  have hcs := meanFar_cs_pos (d := d) (by omega)
  have hlog : 0 ≤ Real.log ((L : ℝ) + 1) :=
    Real.log_nonneg (by have : (0 : ℝ) ≤ L := Nat.cast_nonneg L; linarith)
  have htri : ∀ b : Zd d L, D ≤ zdistInf d L (b - x) + zdistInf d L (b - y) := by
    intro b
    have e : x - y = (b - y) + (-(b - x)) := by abel
    rw [hD, e]
    refine (meanFar_zdistInf_add_le _ _).trans ?_
    rw [meanFar_zdistInf_neg]; omega
  set term : Zd d L → ℝ := fun b => 1 / ((((zdistInf d L (b - x) : ℕ) : ℝ) + 1) ^ (d - 2) *
        (((zdistInf d L (b - y) : ℕ) : ℝ) + 1) ^ d) with hterm
  set t₁ : Zd d L → ℝ := fun b =>
    ((Dr / 2 + 1) ^ (d - 2))⁻¹ * (1 / (((zdistInf d L (b - y) : ℕ) : ℝ) + 1) ^ d) with ht₁
  set t₂ : Zd d L → ℝ := fun b =>
    ((Dr / 2 + 1) ^ d)⁻¹ *
      ((((zdistInf d L (b - x) : ℕ) : ℝ) + 1) ^ 0 / (((zdistInf d L (b - x) : ℕ) : ℝ) + 1) ^ (d - 2))
    with ht₂
  have ht₁0 : ∀ b, 0 ≤ t₁ b := fun b => by simp only [ht₁]; positivity
  have hP : ∀ b, D ≤ 2 * zdistInf d L (b - x) → term b ≤ t₁ b := by
    intro b hb
    have hb' : Dr / 2 ≤ ((zdistInf d L (b - x) : ℕ) : ℝ) := by
      have : (D : ℝ) ≤ 2 * ((zdistInf d L (b - x) : ℕ) : ℝ) := by exact_mod_cast hb
      linarith
    have hpow : (Dr / 2 + 1) ^ (d - 2) ≤ (((zdistInf d L (b - x) : ℕ) : ℝ) + 1) ^ (d - 2) :=
      pow_le_pow_left₀ hh.le (by linarith) _
    simp only [hterm, ht₁]
    have e : 1 / ((((zdistInf d L (b - x) : ℕ) : ℝ) + 1) ^ (d - 2) *
        (((zdistInf d L (b - y) : ℕ) : ℝ) + 1) ^ d) =
        ((((zdistInf d L (b - x) : ℕ) : ℝ) + 1) ^ (d - 2))⁻¹ *
          (1 / (((zdistInf d L (b - y) : ℕ) : ℝ) + 1) ^ d) := by
      rw [one_div, mul_inv, one_div]
    rw [e]
    gcongr
  have hQ : ∀ b, ¬ D ≤ 2 * zdistInf d L (b - x) →
      term b ≤ t₂ b ∧ ((zdistInf d L (b - x) : ℕ) : ℝ) ≤ Dr / 2 := by
    intro b hb
    have h1 := htri b
    have hlt : 2 * zdistInf d L (b - x) < D := by omega
    have hv : Dr / 2 ≤ ((zdistInf d L (b - y) : ℕ) : ℝ) := by
      have : (D : ℝ) ≤ 2 * ((zdistInf d L (b - y) : ℕ) : ℝ) := by exact_mod_cast (by omega : D ≤ 2 * zdistInf d L (b - y))
      linarith
    have hu : ((zdistInf d L (b - x) : ℕ) : ℝ) ≤ Dr / 2 := by
      have : (2 * zdistInf d L (b - x) : ℝ) ≤ D := by exact_mod_cast hlt.le
      linarith
    refine ⟨?_, hu⟩
    have hpow : (Dr / 2 + 1) ^ d ≤ (((zdistInf d L (b - y) : ℕ) : ℝ) + 1) ^ d :=
      pow_le_pow_left₀ hh.le (by linarith) _
    simp only [hterm, ht₂, pow_zero]
    have e : 1 / ((((zdistInf d L (b - x) : ℕ) : ℝ) + 1) ^ (d - 2) *
        (((zdistInf d L (b - y) : ℕ) : ℝ) + 1) ^ d) =
        ((((zdistInf d L (b - y) : ℕ) : ℝ) + 1) ^ d)⁻¹ *
          (1 / (((zdistInf d L (b - x) : ℕ) : ℝ) + 1) ^ (d - 2)) := by
      rw [one_div, mul_inv, one_div, mul_comm]
    rw [e]
    gcongr
  -- split the sum
  have hsplit : ∑ b, term b ≤ ∑ b, t₁ b +
      ∑ b ∈ Finset.univ.filter (fun b : Zd d L => ¬ D ≤ 2 * zdistInf d L (b - x)), t₂ b := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun b : Zd d L => D ≤ 2 * zdistInf d L (b - x)) term]
    refine add_le_add ?_ ?_
    · calc ∑ b ∈ Finset.univ.filter (fun b : Zd d L => D ≤ 2 * zdistInf d L (b - x)), term b
          ≤ ∑ b ∈ Finset.univ.filter (fun b : Zd d L => D ≤ 2 * zdistInf d L (b - x)), t₁ b :=
            Finset.sum_le_sum fun b hb => hP b (Finset.mem_filter.1 hb).2
        _ ≤ ∑ b, t₁ b :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun b _ _ => ht₁0 b
    · exact Finset.sum_le_sum fun b hb => (hQ b (Finset.mem_filter.1 hb).2).1
  -- the first sum
  have hS1 : ∑ b, t₁ b ≤ ((Dr / 2 + 1) ^ (d - 2))⁻¹ * (meanFar_cs d * (1 + Real.log ((L : ℝ) + 1))) := by
    simp only [ht₁]
    rw [← Finset.mul_sum, meanFar_sum_sub (fun b : Zd d L => 1 / (((zdistInf d L b : ℕ) : ℝ) + 1) ^ d) y]
    exact mul_le_mul_of_nonneg_left (meanFar_sum_inv_pow (by omega)) (by positivity)
  -- the second sum
  have hS2 : ∑ b ∈ Finset.univ.filter (fun b : Zd d L => ¬ D ≤ 2 * zdistInf d L (b - x)), t₂ b ≤
      ((Dr / 2 + 1) ^ d)⁻¹ * (meanFar_cs d * (Dr / 2 + 1) ^ (0 + 2)) := by
    simp only [ht₂]
    rw [← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have hsub : ∑ b ∈ Finset.univ.filter (fun b : Zd d L => ¬ D ≤ 2 * zdistInf d L (b - x)),
        (((zdistInf d L (b - x) : ℕ) : ℝ) + 1) ^ 0 / (((zdistInf d L (b - x) : ℕ) : ℝ) + 1) ^ (d - 2) ≤
        ∑ b ∈ Finset.univ.filter (fun b : Zd d L => ((zdistInf d L (b - x) : ℕ) : ℝ) ≤ Dr / 2),
        (((zdistInf d L (b - x) : ℕ) : ℝ) + 1) ^ 0 / (((zdistInf d L (b - x) : ℕ) : ℝ) + 1) ^ (d - 2) := by
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun b _ _ => by positivity
      intro b hb
      exact Finset.mem_filter.2 ⟨Finset.mem_univ _, (hQ b (Finset.mem_filter.1 hb).2).2⟩
    refine hsub.trans ?_
    have heq : ∑ b ∈ Finset.univ.filter (fun b : Zd d L => ((zdistInf d L (b - x) : ℕ) : ℝ) ≤ Dr / 2),
        (((zdistInf d L (b - x) : ℕ) : ℝ) + 1) ^ 0 / (((zdistInf d L (b - x) : ℕ) : ℝ) + 1) ^ (d - 2) =
        ∑ b ∈ Finset.univ.filter (fun b : Zd d L => ((zdistInf d L b : ℕ) : ℝ) ≤ Dr / 2),
        (((zdistInf d L b : ℕ) : ℝ) + 1) ^ 0 / (((zdistInf d L b : ℕ) : ℝ) + 1) ^ (d - 2) := by
      refine Finset.sum_equiv (Equiv.subRight x) (fun b => ?_) (fun b _ => rfl)
      simp
    rw [heq]
    exact meanFar_sum_ball hd 0 (by positivity)
  -- assemble
  have hc12 : ((Dr / 2 + 1) ^ d)⁻¹ * (Dr / 2 + 1) ^ (0 + 2) = ((Dr / 2 + 1) ^ (d - 2))⁻¹ := by
    have e : (Dr / 2 + 1) ^ d = (Dr / 2 + 1) ^ (d - 2) * (Dr / 2 + 1) ^ 2 := by
      rw [← pow_add]; congr 1; omega
    rw [e, mul_inv, zero_add, mul_assoc, inv_mul_cancel₀ (by positivity), mul_one]
  have hfin : ∑ b, term b ≤ 2 * (((Dr / 2 + 1) ^ (d - 2))⁻¹ * (meanFar_cs d * (1 + Real.log ((L : ℝ) + 1)))) := by
    refine hsplit.trans ?_
    have h2' : ((Dr / 2 + 1) ^ d)⁻¹ * (meanFar_cs d * (Dr / 2 + 1) ^ (0 + 2)) =
        ((Dr / 2 + 1) ^ (d - 2))⁻¹ * meanFar_cs d := by
      rw [← hc12]; ring
    have hc1 : (0 : ℝ) ≤ ((Dr / 2 + 1) ^ (d - 2))⁻¹ := by positivity
    have : ((Dr / 2 + 1) ^ (d - 2))⁻¹ * meanFar_cs d ≤
        ((Dr / 2 + 1) ^ (d - 2))⁻¹ * (meanFar_cs d * (1 + Real.log ((L : ℝ) + 1))) := by
      refine mul_le_mul_of_nonneg_left ?_ hc1
      nlinarith
    linarith
  -- `(D/2+1)^{-(d-2)} ≤ 2^{d-2} (D+1)^{-(d-2)}`
  have hc3 : ((Dr / 2 + 1) ^ (d - 2))⁻¹ ≤ 2 ^ (d - 2) / (Dr + 1) ^ (d - 2) := by
    have h1 : (Dr + 1) / 2 ≤ Dr / 2 + 1 := by linarith
    have h2 : ((Dr + 1) / 2) ^ (d - 2) ≤ (Dr / 2 + 1) ^ (d - 2) := pow_le_pow_left₀ (by positivity) h1 _
    have h3 : ((Dr + 1) / 2) ^ (d - 2) = (Dr + 1) ^ (d - 2) / 2 ^ (d - 2) := by rw [div_pow]
    rw [h3] at h2
    calc ((Dr / 2 + 1) ^ (d - 2))⁻¹ ≤ ((Dr + 1) ^ (d - 2) / 2 ^ (d - 2))⁻¹ := inv_anti₀ (by positivity) h2
      _ = 2 ^ (d - 2) / (Dr + 1) ^ (d - 2) := by rw [inv_div]
  have hCp : meanFar_Cpair d = 2 * 2 ^ (d - 2) * meanFar_cs d := by
    unfold meanFar_Cpair
    rw [show d - 1 = (d - 2) + 1 by omega, pow_succ]; ring
  calc ∑ b, term b ≤ 2 * (((Dr / 2 + 1) ^ (d - 2))⁻¹ * (meanFar_cs d * (1 + Real.log ((L : ℝ) + 1)))) := hfin
    _ ≤ 2 * (2 ^ (d - 2) / (Dr + 1) ^ (d - 2) * (meanFar_cs d * (1 + Real.log ((L : ℝ) + 1)))) := by
        gcongr
    _ = meanFar_Cpair d * (1 + Real.log ((L : ℝ) + 1)) / (Dr + 1) ^ (d - 2) := by
        rw [hCp]; ring

/-- The window sum of `|r|_1² / (|r|_∞+1)^{d-2}` over the `ℓ¹`-ball of radius `R` is `≲ R⁴`. -/
private theorem meanFar_window_sum (hd : 3 ≤ d) {R : ℝ} (hR : 0 ≤ R) :
    ∑ x ∈ Finset.univ.filter (fun x : Zd d L => ((zdistD d L x : ℕ) : ℝ) ≤ R),
        ((zdistD d L x : ℕ) : ℝ) ^ 2 / (((zdistInf d L x : ℕ) : ℝ) + 1) ^ (d - 2) ≤
      (d : ℝ) ^ 2 * meanFar_cs d * (R + 1) ^ 4 := by
  classical
  have hsub : ∑ x ∈ Finset.univ.filter (fun x : Zd d L => ((zdistD d L x : ℕ) : ℝ) ≤ R),
        ((zdistD d L x : ℕ) : ℝ) ^ 2 / (((zdistInf d L x : ℕ) : ℝ) + 1) ^ (d - 2) ≤
      ∑ x ∈ Finset.univ.filter (fun x : Zd d L => ((zdistInf d L x : ℕ) : ℝ) ≤ R),
        (d : ℝ) ^ 2 * ((((zdistInf d L x : ℕ) : ℝ) + 1) ^ 2 / (((zdistInf d L x : ℕ) : ℝ) + 1) ^ (d - 2)) := by
    calc _ ≤ ∑ x ∈ Finset.univ.filter (fun x : Zd d L => ((zdistD d L x : ℕ) : ℝ) ≤ R),
          (d : ℝ) ^ 2 * ((((zdistInf d L x : ℕ) : ℝ) + 1) ^ 2 / (((zdistInf d L x : ℕ) : ℝ) + 1) ^ (d - 2)) := by
          refine Finset.sum_le_sum fun x _ => ?_
          have h1 : ((zdistD d L x : ℕ) : ℝ) ≤ (d : ℝ) * (((zdistInf d L x : ℕ) : ℝ) + 1) := by
            have := zdistD_le_mul_zdistInf d L x
            have h2 : ((zdistD d L x : ℕ) : ℝ) ≤ (d : ℝ) * ((zdistInf d L x : ℕ) : ℝ) := by exact_mod_cast this
            have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
            nlinarith
          have h3 : ((zdistD d L x : ℕ) : ℝ) ^ 2 ≤ ((d : ℝ) * (((zdistInf d L x : ℕ) : ℝ) + 1)) ^ 2 :=
            pow_le_pow_left₀ (Nat.cast_nonneg _) h1 2
          rw [mul_pow] at h3
          rw [← mul_div_assoc]
          gcongr
      _ ≤ _ := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun x _ _ => by positivity
          intro x hx
          have hx' : ((zdistD d L x : ℕ) : ℝ) ≤ R := (Finset.mem_filter.1 hx).2
          have : ((zdistInf d L x : ℕ) : ℝ) ≤ ((zdistD d L x : ℕ) : ℝ) := by
            exact_mod_cast zdistInf_le_zdistD d L x
          exact Finset.mem_filter.2 ⟨Finset.mem_univ _, this.trans hx'⟩
  refine hsub.trans ?_
  rw [← Finset.mul_sum]
  have h := meanFar_sum_ball (d := d) (L := L) hd 2 hR
  calc (d : ℝ) ^ 2 * _ ≤ (d : ℝ) ^ 2 * (meanFar_cs d * (R + 1) ^ (2 + 2)) :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ = (d : ℝ) ^ 2 * meanFar_cs d * (R + 1) ^ 4 := by ring

end Lattice

/-! ## 2. The deterministic core -/

section Core

variable {d L : ℕ} [NeZero L]

/-- The constant of the core. -/
def meanFar_Cd (d : ℕ) : ℝ := (d : ℝ) ^ 2 * meanFar_cs d ^ 2 * 2 ^ (d - 2)

/-- The symmetric and translation-invariant kernel is a function of the difference. -/
private theorem meanFar_B0 (B : Zd d L → Zd d L → ℂ)
    (hBtr : ∀ a b c, B (a + c) (b + c) = B a b) (hBsym : ∀ a b, B a b = B b a) (a b : Zd d L) :
    B a b = B 0 (a - b) := by
  have h1 := hBtr 0 (b - a) a
  rw [zero_add, sub_add_cancel] at h1
  rw [h1, hBsym 0 (b - a)]
  have h2 := hBtr (b - a) 0 (a - b)
  have e : (b - a) + (a - b) = 0 := by abel
  rw [e, zero_add] at h2
  exact h2.symm

private theorem meanFar_Bneg (B : Zd d L → Zd d L → ℂ)
    (hBtr : ∀ a b c, B (a + c) (b + c) = B a b) (hBsym : ∀ a b, B a b = B b a) (x : Zd d L) :
    B 0 (-x) = B 0 x := by
  have h := meanFar_B0 B hBtr hBsym 0 x
  rw [zero_sub] at h
  exact h.symm

/-- **The first difference is half the second difference** (`3_5:2199-2206`): by translation
invariance and symmetry of `B`, `B(b₁, b₁+b₁-b₂) = B(b₁, b₂)`, and `b₂ ↦ b₁+b₁-b₂` is an involution of
`Z_L^d`, so `∑_{b₂} B_{b₁b₂}(T(y-b₂) - T(y-b₁)) = ½ ∑_{b₂} B_{b₁b₂}(T(y-b₂) + T(y-(b₁+b₁-b₂)) - 2T(y-b₁))`. -/
private theorem meanFar_identity (T : Zd d L → ℂ) (B : Zd d L → Zd d L → ℂ)
    (hBtr : ∀ a b c, B (a + c) (b + c) = B a b) (hBsym : ∀ a b, B a b = B b a) (y b₁ : Zd d L) :
    ∑ b₂, B b₁ b₂ * (T (y - b₂) - T (y - b₁)) =
      (1 / 2 : ℂ) * ∑ b₂, B b₁ b₂ * (T (y - b₂) + T (y - (b₁ + b₁ - b₂)) - 2 * T (y - b₁)) := by
  have hrefl : ∀ b₂, B b₁ (b₁ + b₁ - b₂) = B b₁ b₂ := by
    intro b₂
    rw [meanFar_B0 B hBtr hBsym b₁ (b₁ + b₁ - b₂), meanFar_B0 B hBtr hBsym b₁ b₂]
    have e : b₁ - (b₁ + b₁ - b₂) = -(b₁ - b₂) := by abel
    rw [e, meanFar_Bneg B hBtr hBsym]
  have hsum : ∑ b₂, B b₁ b₂ * T (y - (b₁ + b₁ - b₂)) = ∑ b₂, B b₁ b₂ * T (y - b₂) := by
    have h := Fintype.sum_equiv (Equiv.subLeft (b₁ + b₁))
      (fun b₂ => B b₁ (b₁ + b₁ - b₂) * T (y - (b₁ + b₁ - b₂)))
      (fun b₂ => B b₁ b₂ * T (y - b₂)) (fun _ => rfl)
    rw [← h]
    exact Finset.sum_congr rfl fun b₂ _ => by rw [hrefl]
  have h2 : ∑ b₂, B b₁ b₂ * (2 * T (y - b₁)) = 2 * ∑ b₂, B b₁ b₂ * T (y - b₁) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring
  have hL : ∑ b₂, B b₁ b₂ * (T (y - b₂) - T (y - b₁)) =
      ∑ b₂, B b₁ b₂ * T (y - b₂) - ∑ b₂, B b₁ b₂ * T (y - b₁) := by
    simp only [mul_sub, Finset.sum_sub_distrib]
  have hR : ∑ b₂, B b₁ b₂ * (T (y - b₂) + T (y - (b₁ + b₁ - b₂)) - 2 * T (y - b₁)) =
      ∑ b₂, B b₁ b₂ * T (y - b₂) + ∑ b₂, B b₁ b₂ * T (y - (b₁ + b₁ - b₂)) -
        ∑ b₂, B b₁ b₂ * (2 * T (y - b₁)) := by
    simp only [mul_sub, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [hL, hR, hsum, h2]
  ring

/-- `‖T x‖ ≤ K₁` from the decay hypothesis. -/
private theorem meanFar_T_le (T : Zd d L → ℂ) {K₁ : ℝ}
    (hT1 : ∀ x, ‖T x‖ ≤ K₁ / (((zdistInf d L x : ℕ) : ℝ) + 1) ^ (d - 2)) (x : Zd d L) :
    ‖T x‖ ≤ K₁ := by
  refine (hT1 x).trans ?_
  have hK₁ : 0 ≤ K₁ := by
    have := hT1 0
    have h0 : 0 ≤ ‖T 0‖ := norm_nonneg _
    have hpos : (0 : ℝ) < (((zdistInf d L (0 : Zd d L) : ℕ) : ℝ) + 1) ^ (d - 2) := by positivity
    have := h0.trans this
    exact (div_nonneg_iff.1 this).elim (fun h => h.1) (fun h => absurd h.2 (not_le.2 hpos))
  have h1 : (1 : ℝ) ≤ (((zdistInf d L x : ℕ) : ℝ) + 1) ^ (d - 2) :=
    one_le_pow₀ (by have : (0 : ℝ) ≤ ((zdistInf d L x : ℕ) : ℝ) := Nat.cast_nonneg _; linarith)
  exact div_le_self hK₁ h1

/-- **The inner `b₂`-sum** for one `b₁` in the far region: `|b₁ - y|_∞ > ρ`.  The window part is the
second-difference bound summed over the `ℓ¹`-ball (`3_5:2207-2210`), the rest costs `K'`. -/
private theorem meanFar_inner_bound (hd : 3 ≤ d)
    (T : Zd d L → ℂ) (B : Zd d L → Zd d L → ℂ)
    (hBtr : ∀ a b c, B (a + c) (b + c) = B a b) (hBsym : ∀ a b, B a b = B b a)
    {ρ w₁ K₁ K₂ K K' : ℝ} (hw₁ : 0 ≤ w₁) (hK₂ : 0 ≤ K₂) (hK' : 0 ≤ K')
    (hT1 : ∀ x, ‖T x‖ ≤ K₁ / (((zdistInf d L x : ℕ) : ℝ) + 1) ^ (d - 2))
    (hT2 : ∀ a r : Zd d L, ((zdistD d L r : ℕ) : ℝ) ≤ w₁ → ρ < ((zdistInf d L a : ℕ) : ℝ) →
      ‖T (a + r) + T (a - r) - 2 * T a‖ ≤
        K₂ * ((zdistD d L r : ℕ) : ℝ) ^ 2 / (((zdistInf d L a : ℕ) : ℝ) + 1) ^ d)
    (hB1 : ∀ x : Zd d L, ((zdistD d L x : ℕ) : ℝ) ≤ w₁ →
      ‖B 0 x‖ ≤ K / (((zdistInf d L x : ℕ) : ℝ) + 1) ^ (d - 2))
    (hB2 : ∀ x : Zd d L, w₁ < ((zdistD d L x : ℕ) : ℝ) → ‖B 0 x‖ ≤ K')
    (y b₁ : Zd d L) (hy : ρ < ((zdistInf d L (b₁ - y) : ℕ) : ℝ)) :
    ‖∑ b₂, B b₁ b₂ * (T (y - b₂) - T (y - b₁))‖ ≤
      (1 / 2 : ℝ) * (K * K₂ * ((d : ℝ) ^ 2 * meanFar_cs d * (w₁ + 1) ^ 4) /
          (((zdistInf d L (b₁ - y) : ℕ) : ℝ) + 1) ^ d + 4 * K₁ * K' * (L : ℝ) ^ d) := by
  classical
  have hK₁ : 0 ≤ K₁ := by
    have := (norm_nonneg (T 0)).trans (hT1 0)
    have hpos : (0 : ℝ) < (((zdistInf d L (0 : Zd d L) : ℕ) : ℝ) + 1) ^ (d - 2) := by positivity
    exact (div_nonneg_iff.1 this).elim (fun h => h.1) (fun h => absurd h.2 (not_le.2 hpos))
  have hK : 0 ≤ K := by
    have h := hB1 0 (by simp [zdistD, hw₁])
    have := (norm_nonneg (B 0 0)).trans h
    have hpos : (0 : ℝ) < (((zdistInf d L (0 : Zd d L) : ℕ) : ℝ) + 1) ^ (d - 2) := by positivity
    exact (div_nonneg_iff.1 this).elim (fun h => h.1) (fun h => absurd h.2 (not_le.2 hpos))
  have hid := meanFar_identity T B hBtr hBsym y b₁
  rw [hid, norm_mul]
  have hhalf : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by simp
  rw [hhalf]
  set v : ℝ := ((zdistInf d L (b₁ - y) : ℕ) : ℝ) with hv
  -- the termwise bound, as a function of `r = b₁ - b₂`
  set G : Zd d L → ℝ := fun r =>
    if ((zdistD d L r : ℕ) : ℝ) ≤ w₁ then
      K * K₂ * ((zdistD d L r : ℕ) : ℝ) ^ 2 / ((((zdistInf d L r : ℕ) : ℝ) + 1) ^ (d - 2) * (v + 1) ^ d)
    else 4 * K₁ * K' with hG
  have hterm : ∀ b₂ : Zd d L, ‖B b₁ b₂ * (T (y - b₂) + T (y - (b₁ + b₁ - b₂)) - 2 * T (y - b₁))‖ ≤
      G (b₁ - b₂) := by
    intro b₂
    set r : Zd d L := b₁ - b₂ with hr
    have e1 : y - b₂ = (y - b₁) + r := by rw [hr]; abel
    have e2 : y - (b₁ + b₁ - b₂) = (y - b₁) - r := by rw [hr]; abel
    have e3 : y - b₁ = -(b₁ - y) := by abel
    have ha : zdistInf d L (y - b₁) = zdistInf d L (b₁ - y) := by
      rw [e3, meanFar_zdistInf_neg]
    rw [norm_mul, e1, e2, meanFar_B0 B hBtr hBsym b₁ b₂]
    by_cases hw : ((zdistD d L r : ℕ) : ℝ) ≤ w₁
    · simp only [hG, hw, ↓reduceIte]
      have hb := hB1 r hw
      have hd2 := hT2 (y - b₁) r hw (by rw [ha]; exact hy)
      rw [ha] at hd2
      calc ‖B 0 r‖ * ‖T (y - b₁ + r) + T (y - b₁ - r) - 2 * T (y - b₁)‖
          ≤ (K / (((zdistInf d L r : ℕ) : ℝ) + 1) ^ (d - 2)) *
              (K₂ * ((zdistD d L r : ℕ) : ℝ) ^ 2 / (v + 1) ^ d) :=
            mul_le_mul hb hd2 (norm_nonneg _) (div_nonneg hK (by positivity))
        _ = _ := by rw [div_mul_div_comm]; ring
    · simp only [hG, hw, ↓reduceIte]
      have hb := hB2 r (not_le.1 hw)
      have h4 : ‖T (y - b₁ + r) + T (y - b₁ - r) - 2 * T (y - b₁)‖ ≤ 4 * K₁ := by
        calc _ ≤ ‖T (y - b₁ + r)‖ + ‖T (y - b₁ - r)‖ + ‖2 * T (y - b₁)‖ := by
              refine (norm_sub_le _ _).trans ?_
              exact add_le_add (norm_add_le _ _) le_rfl
          _ ≤ K₁ + K₁ + 2 * K₁ := by
              refine add_le_add (add_le_add (meanFar_T_le T hT1 _) (meanFar_T_le T hT1 _)) ?_
              rw [norm_mul]; simp only [Complex.norm_ofNat]
              exact mul_le_mul_of_nonneg_left (meanFar_T_le T hT1 _) (by norm_num)
          _ = 4 * K₁ := by ring
      calc ‖B 0 r‖ * ‖T (y - b₁ + r) + T (y - b₁ - r) - 2 * T (y - b₁)‖ ≤ K' * (4 * K₁) :=
            mul_le_mul hb h4 (norm_nonneg _) hK'
        _ = 4 * K₁ * K' := by ring
  have hsumG : ∑ b₂ : Zd d L, G (b₁ - b₂) = ∑ r : Zd d L, G r :=
    Fintype.sum_equiv (Equiv.subLeft b₁) _ _ (fun _ => rfl)
  -- the sum of `G`
  have hG1 : ∑ r : Zd d L, G r ≤ K * K₂ * ((d : ℝ) ^ 2 * meanFar_cs d * (w₁ + 1) ^ 4) / (v + 1) ^ d +
      4 * K₁ * K' * (L : ℝ) ^ d := by
    have hGle : ∀ r : Zd d L, G r ≤
        (if ((zdistD d L r : ℕ) : ℝ) ≤ w₁ then
          K * K₂ / (v + 1) ^ d * (((zdistD d L r : ℕ) : ℝ) ^ 2 / (((zdistInf d L r : ℕ) : ℝ) + 1) ^ (d - 2))
          else 0) + 4 * K₁ * K' := by
      intro r
      by_cases hw : ((zdistD d L r : ℕ) : ℝ) ≤ w₁
      · simp only [hG, hw, ↓reduceIte]
        have : 0 ≤ 4 * K₁ * K' := by positivity
        have e : K * K₂ * ((zdistD d L r : ℕ) : ℝ) ^ 2 /
            ((((zdistInf d L r : ℕ) : ℝ) + 1) ^ (d - 2) * (v + 1) ^ d) =
            K * K₂ / (v + 1) ^ d * (((zdistD d L r : ℕ) : ℝ) ^ 2 / (((zdistInf d L r : ℕ) : ℝ) + 1) ^ (d - 2)) := by
          field_simp
        rw [e]; linarith
      · simp [hG, hw]
    refine (Finset.sum_le_sum fun r _ => hGle r).trans ?_
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, card_Zd, nsmul_eq_mul]
    have hwin : ∑ r : Zd d L, (if ((zdistD d L r : ℕ) : ℝ) ≤ w₁ then
          K * K₂ / (v + 1) ^ d * (((zdistD d L r : ℕ) : ℝ) ^ 2 / (((zdistInf d L r : ℕ) : ℝ) + 1) ^ (d - 2))
          else 0) =
        K * K₂ / (v + 1) ^ d * ∑ r ∈ Finset.univ.filter (fun r : Zd d L => ((zdistD d L r : ℕ) : ℝ) ≤ w₁),
          ((zdistD d L r : ℕ) : ℝ) ^ 2 / (((zdistInf d L r : ℕ) : ℝ) + 1) ^ (d - 2) := by
      rw [Finset.mul_sum, Finset.sum_filter]
    rw [hwin]
    have hw' := meanFar_window_sum (d := d) (L := L) hd hw₁
    have : K * K₂ / (v + 1) ^ d * ∑ r ∈ Finset.univ.filter (fun r : Zd d L => ((zdistD d L r : ℕ) : ℝ) ≤ w₁),
          ((zdistD d L r : ℕ) : ℝ) ^ 2 / (((zdistInf d L r : ℕ) : ℝ) + 1) ^ (d - 2) ≤
        K * K₂ / (v + 1) ^ d * ((d : ℝ) ^ 2 * meanFar_cs d * (w₁ + 1) ^ 4) :=
      mul_le_mul_of_nonneg_left hw' (by positivity)
    have e : K * K₂ / (v + 1) ^ d * ((d : ℝ) ^ 2 * meanFar_cs d * (w₁ + 1) ^ 4) =
        K * K₂ * ((d : ℝ) ^ 2 * meanFar_cs d * (w₁ + 1) ^ 4) / (v + 1) ^ d := by ring
    rw [e] at this
    calc _ ≤ K * K₂ * ((d : ℝ) ^ 2 * meanFar_cs d * (w₁ + 1) ^ 4) / (v + 1) ^ d +
          ((L ^ d : ℕ) : ℝ) * (4 * K₁ * K') := add_le_add this le_rfl
      _ = _ := by push_cast; ring
  have hnorm : ‖∑ b₂, B b₁ b₂ * (T (y - b₂) + T (y - (b₁ + b₁ - b₂)) - 2 * T (y - b₁))‖ ≤
      ∑ r : Zd d L, G r := by
    refine (norm_sum_le _ _).trans ?_
    rw [← hsumG]
    exact Finset.sum_le_sum fun b₂ _ => hterm b₂
  calc 1 / 2 * ‖∑ b₂, B b₁ b₂ * (T (y - b₂) + T (y - (b₁ + b₁ - b₂)) - 2 * T (y - b₁))‖
      ≤ 1 / 2 * ∑ r : Zd d L, G r := by gcongr
    _ ≤ _ := by gcongr

/-- **The deterministic core of `(eq:boundEfar)`** (`3_5:2192-2212`).  For a translation-invariant,
symmetric kernel `B` (`𝔼𝓑`), a propagator profile `T = Θ_t(0, ·)`, and the far set `S ⊆ {b₁ : |b₁-a₁|∧|b₁-a₂| > ρ}`,
`∑_{b₁∈S} ∑_{b₂} T(b₁-a₁) B_{b₁b₂} (T(a₂-b₂) - T(a₂-b₁))` is at most
`C_d K₁ K₂ K (1 + log(L+1)) (w₁+1)⁴ / (|a₁-a₂|+1)^{d-2} + 2 K₁² K' L^{2d}`.
Hypotheses: the decay of `T` (`hT1`, `(prop:ThfadC)`), its second difference (`hT2`, `(prop:BD2)`, on the `ℓ¹`-window
`|r|₁ ≤ w₁` and `|a|_∞ > ρ`), the decay of `B` inside the `ℓ¹`-window `w₁` (`hB1`, `(eq:propcalB)`) and the crude
bound `K'` beyond it (`hB2`). -/
theorem meanFar_core (hd : 3 ≤ d)
    (T : Zd d L → ℂ) (B : Zd d L → Zd d L → ℂ)
    (hBtr : ∀ a b c, B (a + c) (b + c) = B a b) (hBsym : ∀ a b, B a b = B b a)
    (ρ w₁ K₁ K₂ K K' : ℝ) (hw₁ : 0 ≤ w₁) (hK₂ : 0 ≤ K₂) (hK' : 0 ≤ K')
    (hT1 : ∀ x : Zd d L, ‖T x‖ ≤ K₁ / (((zdistInf d L x : ℕ) : ℝ) + 1) ^ (d - 2))
    (hT2 : ∀ a r : Zd d L, ((zdistD d L r : ℕ) : ℝ) ≤ w₁ → ρ < ((zdistInf d L a : ℕ) : ℝ) →
      ‖T (a + r) + T (a - r) - 2 * T a‖ ≤
        K₂ * ((zdistD d L r : ℕ) : ℝ) ^ 2 / (((zdistInf d L a : ℕ) : ℝ) + 1) ^ d)
    (hB1 : ∀ x : Zd d L, ((zdistD d L x : ℕ) : ℝ) ≤ w₁ →
      ‖B 0 x‖ ≤ K / (((zdistInf d L x : ℕ) : ℝ) + 1) ^ (d - 2))
    (hB2 : ∀ x : Zd d L, w₁ < ((zdistD d L x : ℕ) : ℝ) → ‖B 0 x‖ ≤ K')
    (a : Fin 2 → Zd d L) (S : Finset (Zd d L))
    (hS : ∀ b ∈ S, ρ < ((zdistInf d L (b - a 0) : ℕ) : ℝ) ∧ ρ < ((zdistInf d L (b - a 1) : ℕ) : ℝ)) :
    ‖∑ b₁ ∈ S, ∑ b₂ : Zd d L, T (b₁ - a 0) * B b₁ b₂ * (T (a 1 - b₂) - T (a 1 - b₁))‖ ≤
      meanFar_Cd d * K₁ * K₂ * K * (1 + Real.log ((L : ℝ) + 1)) * (w₁ + 1) ^ 4 /
          (((zdistInf d L (a 0 - a 1) : ℕ) : ℝ) + 1) ^ (d - 2) + 2 * K₁ ^ 2 * K' * ((L : ℝ) ^ d) ^ 2 := by
  classical
  have hK₁ : 0 ≤ K₁ := by
    have := (norm_nonneg (T 0)).trans (hT1 0)
    have hpos : (0 : ℝ) < (((zdistInf d L (0 : Zd d L) : ℕ) : ℝ) + 1) ^ (d - 2) := by positivity
    exact (div_nonneg_iff.1 this).elim (fun h => h.1) (fun h => absurd h.2 (not_le.2 hpos))
  have hK : 0 ≤ K := by
    have h := hB1 0 (by simp [zdistD, hw₁])
    have := (norm_nonneg (B 0 0)).trans h
    have hpos : (0 : ℝ) < (((zdistInf d L (0 : Zd d L) : ℕ) : ℝ) + 1) ^ (d - 2) := by positivity
    exact (div_nonneg_iff.1 this).elim (fun h => h.1) (fun h => absurd h.2 (not_le.2 hpos))
  have hcs := meanFar_cs_pos (d := d) (by omega)
  have hlog : 0 ≤ Real.log ((L : ℝ) + 1) :=
    Real.log_nonneg (by have : (0 : ℝ) ≤ L := Nat.cast_nonneg L; linarith)
  set M : ℝ := K * K₂ * ((d : ℝ) ^ 2 * meanFar_cs d * (w₁ + 1) ^ 4) with hM
  set N₀ : ℝ := 4 * K₁ * K' * (L : ℝ) ^ d with hN₀
  have hM0 : 0 ≤ M := by positivity
  have hN₀0 : 0 ≤ N₀ := by positivity
  -- the `b₁`-summand
  have hsum_eq : ∀ b₁ : Zd d L, ∑ b₂ : Zd d L, T (b₁ - a 0) * B b₁ b₂ * (T (a 1 - b₂) - T (a 1 - b₁)) =
      T (b₁ - a 0) * ∑ b₂ : Zd d L, B b₁ b₂ * (T (a 1 - b₂) - T (a 1 - b₁)) := by
    intro b₁
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun b₂ _ => by ring
  have hb₁ : ∀ b₁ ∈ S, ‖∑ b₂ : Zd d L, T (b₁ - a 0) * B b₁ b₂ * (T (a 1 - b₂) - T (a 1 - b₁))‖ ≤
      K₁ / (((zdistInf d L (b₁ - a 0) : ℕ) : ℝ) + 1) ^ (d - 2) *
        ((1 / 2 : ℝ) * (M / (((zdistInf d L (b₁ - a 1) : ℕ) : ℝ) + 1) ^ d + N₀)) := by
    intro b₁ hb
    rw [hsum_eq, norm_mul]
    refine mul_le_mul (hT1 _) ?_ (norm_nonneg _) (by positivity)
    exact meanFar_inner_bound hd T B hBtr hBsym hw₁ hK₂ hK' hT1 hT2 hB1 hB2 (a 1) b₁ (hS b₁ hb).2
  refine (norm_sum_le _ _).trans ((Finset.sum_le_sum hb₁).trans ?_)
  have hnn : ∀ b₁ : Zd d L, 0 ≤ K₁ / (((zdistInf d L (b₁ - a 0) : ℕ) : ℝ) + 1) ^ (d - 2) *
        ((1 / 2 : ℝ) * (M / (((zdistInf d L (b₁ - a 1) : ℕ) : ℝ) + 1) ^ d + N₀)) := fun b₁ => by positivity
  refine (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S) fun b _ _ => hnn b).trans ?_
  -- expand
  have hexp : ∀ b₁ : Zd d L, K₁ / (((zdistInf d L (b₁ - a 0) : ℕ) : ℝ) + 1) ^ (d - 2) *
        ((1 / 2 : ℝ) * (M / (((zdistInf d L (b₁ - a 1) : ℕ) : ℝ) + 1) ^ d + N₀)) =
      (1 / 2 : ℝ) * M * K₁ * (1 / ((((zdistInf d L (b₁ - a 0) : ℕ) : ℝ) + 1) ^ (d - 2) *
          (((zdistInf d L (b₁ - a 1) : ℕ) : ℝ) + 1) ^ d)) +
        (1 / 2 : ℝ) * N₀ * K₁ * (1 / (((zdistInf d L (b₁ - a 0) : ℕ) : ℝ) + 1) ^ (d - 2)) := by
    intro b₁
    field_simp
  rw [Finset.sum_congr rfl fun b₁ _ => hexp b₁, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have hpair := meanFar_pair_sum (d := d) (L := L) hd (a 0) (a 1)
  have hone : ∑ b₁ : Zd d L, 1 / (((zdistInf d L (b₁ - a 0) : ℕ) : ℝ) + 1) ^ (d - 2) ≤ (L : ℝ) ^ d := by
    calc _ ≤ ∑ _b₁ : Zd d L, (1 : ℝ) := by
          refine Finset.sum_le_sum fun b₁ _ => ?_
          have : (1 : ℝ) ≤ (((zdistInf d L (b₁ - a 0) : ℕ) : ℝ) + 1) ^ (d - 2) :=
            one_le_pow₀ (by have : (0 : ℝ) ≤ ((zdistInf d L (b₁ - a 0) : ℕ) : ℝ) := Nat.cast_nonneg _; linarith)
          exact div_le_one_of_le₀ (by linarith) (by linarith)
      _ = (L : ℝ) ^ d := by simp [Finset.card_univ]
  have hCpair : meanFar_Cd d = (1 / 2 : ℝ) * ((d : ℝ) ^ 2 * meanFar_cs d) * meanFar_Cpair d := by
    unfold meanFar_Cd meanFar_Cpair
    rw [show d - 1 = (d - 2) + 1 by omega, pow_succ]; ring
  have h1 : (1 / 2 : ℝ) * M * K₁ * ∑ b₁ : Zd d L, 1 / ((((zdistInf d L (b₁ - a 0) : ℕ) : ℝ) + 1) ^ (d - 2) *
          (((zdistInf d L (b₁ - a 1) : ℕ) : ℝ) + 1) ^ d) ≤
      meanFar_Cd d * K₁ * K₂ * K * (1 + Real.log ((L : ℝ) + 1)) * (w₁ + 1) ^ 4 /
          (((zdistInf d L (a 0 - a 1) : ℕ) : ℝ) + 1) ^ (d - 2) := by
    have h0 : 0 ≤ (1 / 2 : ℝ) * M * K₁ := by positivity
    calc _ ≤ (1 / 2 : ℝ) * M * K₁ * (meanFar_Cpair d * (1 + Real.log ((L : ℝ) + 1)) /
          (((zdistInf d L (a 0 - a 1) : ℕ) : ℝ) + 1) ^ (d - 2)) := mul_le_mul_of_nonneg_left hpair h0
      _ = _ := by rw [hCpair, hM]; ring
  have h2 : (1 / 2 : ℝ) * N₀ * K₁ * ∑ b₁ : Zd d L, 1 / (((zdistInf d L (b₁ - a 0) : ℕ) : ℝ) + 1) ^ (d - 2) ≤
      2 * K₁ ^ 2 * K' * ((L : ℝ) ^ d) ^ 2 := by
    have h0 : 0 ≤ (1 / 2 : ℝ) * N₀ * K₁ := by positivity
    calc _ ≤ (1 / 2 : ℝ) * N₀ * K₁ * (L : ℝ) ^ d := mul_le_mul_of_nonneg_left hone h0
      _ = _ := by rw [hN₀]; ring
  linarith

end Core

/-! ## 3. The propagator bounds in the shape of the core -/

section Theta

variable {d L : ℕ} [NeZero L]

/-- `(prop:ThfadC)` in the shape `hT1` of the core: `|T(x)| ≤ C₅ (1 + 2^{d-1}) g^{-2} (|x|_∞+1)^{-(d-2)}`, from
`|T(x)| ≤ C₅ B_{t,|x|₁}` (`Prop5Decay`), the zero-mode term being dominated by `(1-t) ≥ g²/L²`
(`zeroMode_le_of_ge`). -/
theorem meanFar_T1 (hd : 3 ≤ d) (hL : 3 ≤ L) {g t C₅ c₅ : ℝ} (hg : 0 < g) (ht : t < 1)
    (hreg : g ^ 2 / (L : ℝ) ^ 2 ≤ 1 - t) (hC₅ : 0 ≤ C₅) (hc₅ : 0 < c₅) (T : Zd d L → ℂ)
    (hdec : ∀ x : Zd d L, ‖T x‖ ≤ C₅ * Bparam d L g t (zdistD d L x) *
      Real.exp (-c₅ * (zdistD d L x : ℝ) / ellT L g t)) (x : Zd d L) :
    ‖T x‖ ≤ (C₅ * (1 + 2 ^ (d - 1)) / g ^ 2) / (((zdistInf d L x : ℕ) : ℝ) + 1) ^ (d - 2) := by
  have hL1 : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast (by omega : 1 ≤ L)
  have hu : (0 : ℝ) < 1 - t := by linarith
  have habs : |1 - t| = 1 - t := abs_of_pos hu
  have hex : Real.exp (-c₅ * (zdistD d L x : ℝ) / ellT L g t) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have : 0 < ellT L g t := ellT_pos hL1
    have : 0 ≤ c₅ * (zdistD d L x : ℝ) := by positivity
    rw [neg_mul, neg_div]
    exact neg_nonpos.2 (by positivity)
  have hB0 : 0 ≤ Bparam d L g t (zdistD d L x) := by
    unfold Bparam; positivity
  have h1 : ‖T x‖ ≤ C₅ * Bparam d L g t (zdistD d L x) := by
    refine (hdec x).trans ?_
    calc _ ≤ C₅ * Bparam d L g t (zdistD d L x) * 1 :=
          mul_le_mul_of_nonneg_left hex (by positivity)
      _ = _ := mul_one _
  refine h1.trans ?_
  have hrL : ((zdistInf d L x : ℕ) : ℝ) ≤ (L : ℝ) := by
    have := meanFar_zdistInf_le x
    exact_mod_cast this
  have hrD : ((zdistInf d L x : ℕ) : ℝ) ≤ ((zdistD d L x : ℕ) : ℝ) := by
    have := zdistInf_le_zdistD d L x
    exact_mod_cast this
  set r : ℝ := ((zdistInf d L x : ℕ) : ℝ) with hr
  have hr0 : 0 ≤ r := Nat.cast_nonneg _
  have hzm := zeroMode_le_of_ge (d := d) (L := L) (g := g) (t := t) (by omega) hL1 ht hr0 hrL hreg
  have hpow : (r + 1) ^ (d - 2) ≤ (((zdistD d L x : ℕ) : ℝ) + 1) ^ (d - 2) :=
    pow_le_pow_left₀ (by linarith) (by linarith) _
  have hinv : ((((zdistD d L x : ℕ) : ℝ) + 1) ^ (d - 2))⁻¹ ≤ ((r + 1) ^ (d - 2))⁻¹ :=
    inv_anti₀ (by positivity) hpow
  have hgg : (g ^ 2 + |1 - t|)⁻¹ ≤ (g ^ 2)⁻¹ := inv_anti₀ (by positivity) (by rw [habs]; linarith)
  have hBp : Bparam d L g t (zdistD d L x) ≤ (1 + 2 ^ (d - 1)) * ((g ^ 2)⁻¹ * ((r + 1) ^ (d - 2))⁻¹) := by
    unfold Bparam
    have e1 : (g ^ 2 + |1 - t|)⁻¹ * ((((zdistD d L x : ℕ) : ℝ) + 1) ^ (d - 2))⁻¹ ≤
        (g ^ 2)⁻¹ * ((r + 1) ^ (d - 2))⁻¹ := by gcongr
    have e2 : ((L : ℝ) ^ d * |1 - t|)⁻¹ ≤ 2 ^ (d - 1) * ((g ^ 2)⁻¹ * ((r + 1) ^ (d - 2))⁻¹) := by
      refine hzm.trans ?_
      gcongr
    nlinarith
  calc C₅ * Bparam d L g t (zdistD d L x)
      ≤ C₅ * ((1 + 2 ^ (d - 1)) * ((g ^ 2)⁻¹ * ((r + 1) ^ (d - 2))⁻¹)) :=
        mul_le_mul_of_nonneg_left hBp hC₅
    _ = _ := by field_simp

/-- `(prop:BD2)` in the shape `hT2` of the core: for `|r|₁ ≤ w₁`, `|a|_∞ > ρ` and `2 w₁ ≤ ⌊ρ⌋ + 1`,
`|T(a+r) + T(a-r) - 2T(a)| ≤ (C₇/g²) |r|₁² (|a|_∞+1)^{-d}`.  The condition `|r|₁ ≤ ½ |a|₁` of `Prop7Diff2` holds as
`|a|₁ ≥ |a|_∞ ≥ ⌊ρ⌋ + 1 ≥ 2 w₁`. -/
theorem meanFar_T2 {g t C₇ ρ w₁ : ℝ} (hg : 0 < g) (hC₇ : 0 ≤ C₇) (hρ : 0 ≤ ρ)
    (hwρ : 2 * w₁ ≤ (⌊ρ⌋₊ : ℝ) + 1) (T : Zd d L → ℂ)
    (hdiff : ∀ a r : Zd d L, ((zdistD d L r : ℕ) : ℝ) ≤ 1 / 2 * ((zdistD d L a : ℕ) : ℝ) →
      ‖T (a + r) + T (a - r) - 2 * T a‖ ≤ C₇ * (g ^ 2 + |1 - t|)⁻¹ * ((zdistD d L r : ℕ) : ℝ) ^ 2 *
        ((((zdistD d L a : ℕ) : ℝ) + 1) ^ d)⁻¹)
    (a r : Zd d L) (hr : ((zdistD d L r : ℕ) : ℝ) ≤ w₁)
    (ha : ρ < ((zdistInf d L a : ℕ) : ℝ)) :
    ‖T (a + r) + T (a - r) - 2 * T a‖ ≤
      C₇ / g ^ 2 * ((zdistD d L r : ℕ) : ℝ) ^ 2 / (((zdistInf d L a : ℕ) : ℝ) + 1) ^ d := by
  have hfl : ⌊ρ⌋₊ < zdistInf d L a := (Nat.floor_lt hρ).2 ha
  have hfl' : ((⌊ρ⌋₊ : ℕ) : ℝ) + 1 ≤ ((zdistInf d L a : ℕ) : ℝ) := by exact_mod_cast hfl
  have haD : ((zdistInf d L a : ℕ) : ℝ) ≤ ((zdistD d L a : ℕ) : ℝ) := by
    exact_mod_cast zdistInf_le_zdistD d L a
  have hr' : ((zdistD d L r : ℕ) : ℝ) ≤ 1 / 2 * ((zdistD d L a : ℕ) : ℝ) := by linarith
  refine (hdiff a r hr').trans ?_
  have h1 : (g ^ 2 + |1 - t|)⁻¹ ≤ (g ^ 2)⁻¹ := inv_anti₀ (by positivity) (by linarith [abs_nonneg (1 - t)])
  have h2 : ((((zdistD d L a : ℕ) : ℝ) + 1) ^ d)⁻¹ ≤ ((((zdistInf d L a : ℕ) : ℝ) + 1) ^ d)⁻¹ :=
    inv_anti₀ (by positivity) (pow_le_pow_left₀ (by positivity) (by linarith) _)
  calc C₇ * (g ^ 2 + |1 - t|)⁻¹ * ((zdistD d L r : ℕ) : ℝ) ^ 2 * ((((zdistD d L a : ℕ) : ℝ) + 1) ^ d)⁻¹
      ≤ C₇ * (g ^ 2)⁻¹ * ((zdistD d L r : ℕ) : ℝ) ^ 2 * ((((zdistInf d L a : ℕ) : ℝ) + 1) ^ d)⁻¹ := by
        gcongr
    _ = _ := by field_simp

end Theta

/-! ## 4. The expectation kernel `𝔼 𝓑` and its invariances -/

section Expect

/-- `‖∫ f‖ ≤ M + C · P(‖f‖ > M)` for `‖f‖ ≤ C`: the expectation of a `≺` bound
(a.s. polynomial envelope `C` plus a small bad event). -/
private theorem meanFar_norm_integral_le {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
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

variable {d : ℕ} (sz : Sizes d)

/-- The loops `𝓛^{(2)}_{u,σ,a}` are integrable (measurable and bounded by `η_u^{-2}`). -/
private theorem meanFar_integrable_L (n : ℕ) {E u : ℝ} (hE : |E| < 2) (hu : u < 1)
    (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) :
    Integrable (fun ω => Lloop sz n E u σ a ω) sz.seqP :=
  Integrable.of_bound (walk_measurable_Lloop sz n E u σ a).aestronglyMeasurable
    ((etaT E u)⁻¹ ^ 2) (Filter.Eventually.of_forall fun ω => norm_Lloop_le sz n hE hu σ a ω)

/-- **The mean kernel** `𝔼 𝓑_{ab}`, `𝓑 = (𝓛 - 𝒦)^{(2)}_{s,σ}` (`3_5:2139`). -/
private def meanFar_B (n : ℕ) (E s : ℝ) (σ : Fin 2 → Bool) (a b : Zd d (sz.L n)) : ℂ :=
  ∫ ω, STLKM sz n E s (sz.seqHflow n s ω) σ ![a, b] ∂(sz.seqP)

/-- `𝒦^{(2)}_{s,σ,(a,b)} = W^{-d} m₁ m₂ Θ_{s m₁ m₂}(a,b)` (`(Kn2sol)`). -/
private theorem meanFar_K_eq (n : ℕ) (E s : ℝ) (σ : Fin 2 → Bool) (a b : Zd d (sz.L n)) :
    STKloop sz n E s σ ![a, b] = (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * (mSigma E (σ 0) * mSigma E (σ 1)) *
      Theta d (sz.L n) (sz.lam n) ((s : ℂ) * (mSigma E (σ 0) * mSigma E (σ 1))) a b := by
  unfold STKloop
  have h : KLloopOf d (sz.L n) σ ![a, b] = ⟨[σ 0, σ 1], [a, b]⟩ := by
    simp [KLloopOf, List.ofFn_succ]
  rw [h, KLK_two]

private theorem meanFar_B_eq (n : ℕ) {E s : ℝ} (hE : |E| < 2) (hs : s < 1) (σ : Fin 2 → Bool)
    (a b : Zd d (sz.L n)) :
    meanFar_B sz n E s σ a b =
      (∫ ω, Lloop sz n E s σ ![a, b] ω ∂(sz.seqP)) - STKloop sz n E s σ ![a, b] := by
  unfold meanFar_B
  have h : (fun ω => STLKM sz n E s (sz.seqHflow n s ω) σ ![a, b]) =
      fun ω => Lloop sz n E s σ ![a, b] ω - STKloop sz n E s σ ![a, b] := rfl
  rw [h, integral_sub (meanFar_integrable_L sz n hE hs σ ![a, b]) (integrable_const _),
    integral_const]
  simp

/-- **Translation invariance of `𝔼 𝓑`** (`3_5:2196`): `𝔼𝓛` by `stExpInv_holds`, `𝒦` by `Θ` property 2. -/
private theorem meanFar_B_tr (n : ℕ) {E s : ℝ} (hE : |E| < 2) (hs0 : 0 ≤ s) (hs : s < 1)
    (σ : Fin 2 → Bool) (a b c : Zd d (sz.L n)) :
    meanFar_B sz n E s σ (a + c) (b + c) = meanFar_B sz n E s σ a b := by
  rw [meanFar_B_eq sz n hE hs, meanFar_B_eq sz n hE hs, meanFar_K_eq, meanFar_K_eq]
  have hL := sz.three_le_L n
  have hξ := norm_mul_mSigma_lt_one hE.le hs0 hs (σ 0) (σ 1)
  rw [Theta_apply_add_right_of_three_le hL hξ]
  have h := (stExpInv_holds d sz n E s hE hs0 hs σ ![a, b] c).1
  have e : (fun i => (![a, b] : Fin 2 → Zd d (sz.L n)) i + c) = ![a + c, b + c] := by
    funext i; fin_cases i <;> simp
  rw [e] at h
  rw [h]

/-- **Symmetry of `𝔼 𝓑`** (`3_5:2196`): reflection and the translation by `a + b` give
`𝔼𝓛_{(b,a)} = 𝔼𝓛_{(a,b)}`; `Θ` is symmetric (property 1). -/
private theorem meanFar_B_sym (n : ℕ) {E s : ℝ} (hE : |E| < 2) (hs0 : 0 ≤ s) (hs : s < 1)
    (σ : Fin 2 → Bool) (a b : Zd d (sz.L n)) :
    meanFar_B sz n E s σ a b = meanFar_B sz n E s σ b a := by
  rw [meanFar_B_eq sz n hE hs, meanFar_B_eq sz n hE hs, meanFar_K_eq, meanFar_K_eq]
  have hL := sz.three_le_L n
  have hξ := norm_mul_mSigma_lt_one hE.le hs0 hs (σ 0) (σ 1)
  have hT : Theta d (sz.L n) (sz.lam n) ((s : ℂ) * (mSigma E (σ 0) * mSigma E (σ 1))) b a =
      Theta d (sz.L n) (sz.lam n) ((s : ℂ) * (mSigma E (σ 0) * mSigma E (σ 1))) a b :=
    congr_fun (congr_fun (Theta_transpose_of_three_le (d := d) (L := sz.L n) (g := sz.lam n) hL hξ) a) b
  rw [hT]
  have hr := (stExpInv_holds d sz n E s hE hs0 hs σ ![a, b] 0).2
  have ht := (stExpInv_holds d sz n E s hE hs0 hs σ ![-a, -b] (a + b)).1
  have e1 : (fun i => -((![a, b] : Fin 2 → Zd d (sz.L n)) i)) = ![-a, -b] := by
    funext i; fin_cases i <;> simp
  have e2 : (fun i => (![-a, -b] : Fin 2 → Zd d (sz.L n)) i + (a + b)) = ![b, a] := by
    funext i; fin_cases i <;> simp
  rw [e1] at hr
  rw [e2] at ht
  rw [← hr, ← ht]

/-- The `≺` bound of `(Eq:Gdecay_w)` at `u = s` (`STGdecayW`) for the entry `𝓑_{ab}` holds off an event of
probability `≤ N^{-D₁}`, by taking the witness `u = (s, σ, (a,b))` in the union inside `Prec`. -/
private theorem meanFar_bad_le {E s t : ℕ → ℝ} {Cd : ℝ} (hs1 : ∀ n, s n < 1) (hst : ∀ n, s n ≤ t n)
    (hG : STGdecayW sz E s t Cd) {Dw : ℝ} (hDw : 0 < Dw) {τ D₁ : ℝ} (hτ : 0 < τ) (hD₁ : 0 < D₁) :
    ∀ᶠ n in atTop, ∀ (σ : Fin 2 → Bool) (a b : Zd d (sz.L n)),
      sz.seqP {ω | ((sz.size n : ℕ) : ℝ) ^ τ *
          (sz.Bctl n (s n) ^ (1 / 5 : ℝ) * STWB sz n (s n) (zdistInf d (sz.L n) (a - b)) *
            Real.exp (-(((zdistInf d (sz.L n) (a - b) : ℕ) : ℝ) / ellT (sz.L n) (sz.lam n) (s n)) ^ (1 / 2 : ℝ)) +
            ((sz.W n : ℕ) : ℝ) ^ (-Dw)) <
          ‖STLKM sz n (E n) (s n) (sz.seqHflow n (s n) ω) σ ![a, b]‖} ≤
        ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-D₁)) := by
  filter_upwards [hG Dw hDw τ hτ D₁ hD₁] with n hn σ a b
  refine le_trans (measure_mono ?_) hn
  intro ω hω
  refine ⟨(⟨s n, le_rfl, hst n⟩, σ, ![a, b]), ?_⟩
  have h1 : (1 - s n) ≠ 0 := (sub_pos.2 (hs1 n)).ne'
  simp only [div_self h1, Real.one_rpow, one_mul]
  have e : (![a, b] : Fin 2 → Zd d (sz.L n)) 0 - (![a, b] : Fin 2 → Zd d (sz.L n)) 1 = a - b := by simp
  rw [e]
  exact hω

/-- The pointwise bound of `‖𝔼 𝓑_{ab}‖` from the `≺` bound off an event of probability `≤ N^{-D₁}`:
`‖𝔼𝓑_{ab}‖ ≤ N^τ Z + (η_s^{-2} + |𝒦_{ab}|) N^{-D₁}` (a.s. envelope `|𝓛^{(2)}| ≤ η_s^{-2}`,
`norm_Lloop_le`). -/
private theorem meanFar_B_bound (n : ℕ) {E s : ℝ} (hE : |E| < 2) (hs : s < 1) (σ : Fin 2 → Bool)
    (a b : Zd d (sz.L n)) {τ Z D₁ : ℝ} (hZ : 0 ≤ ((sz.size n : ℕ) : ℝ) ^ τ * Z)
    (hP : sz.seqP {ω | ((sz.size n : ℕ) : ℝ) ^ τ * Z <
        ‖STLKM sz n E s (sz.seqHflow n s ω) σ ![a, b]‖} ≤
      ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-D₁))) :
    ‖meanFar_B sz n E s σ a b‖ ≤ ((sz.size n : ℕ) : ℝ) ^ τ * Z +
      ((etaT E s)⁻¹ ^ 2 + ‖STKloop sz n E s σ ![a, b]‖) * ((sz.size n : ℕ) : ℝ) ^ (-D₁) := by
  have hmeas : Measurable fun ω => STLKM sz n E s (sz.seqHflow n s ω) σ ![a, b] :=
    (walk_measurable_Lloop sz n E s σ ![a, b]).sub measurable_const
  have hall : ∀ ω, ‖STLKM sz n E s (sz.seqHflow n s ω) σ ![a, b]‖ ≤
      (etaT E s)⁻¹ ^ 2 + ‖STKloop sz n E s σ ![a, b]‖ := by
    intro ω
    refine (norm_sub_le _ _).trans (add_le_add ?_ le_rfl)
    exact norm_Lloop_le sz n hE hs σ ![a, b] ω
  have h := meanFar_norm_integral_le sz.seqP (fun ω => STLKM sz n E s (sz.seqHflow n s ω) σ ![a, b])
    hmeas _ _ hZ hall
  have hreal : sz.seqP.real {ω | ((sz.size n : ℕ) : ℝ) ^ τ * Z <
        ‖STLKM sz n E s (sz.seqHflow n s ω) σ ![a, b]‖} ≤ ((sz.size n : ℕ) : ℝ) ^ (-D₁) := by
    rw [Measure.real]
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hP
    rwa [ENNReal.toReal_ofReal (Real.rpow_nonneg (Nat.cast_nonneg _) _)] at this
  have hC : 0 ≤ (etaT E s)⁻¹ ^ 2 + ‖STKloop sz n E s σ ![a, b]‖ := by positivity
  unfold meanFar_B
  refine h.trans ?_
  gcongr

/-- `Θ_{xy} = Θ_{0,y-x}` (property 2). -/
private theorem meanFar_Theta_shift {L : ℕ} [NeZero L] (hL : 3 ≤ L) {g : ℝ} {ξ : ℂ} (hξ : ‖ξ‖ < 1)
    (x y : Zd d L) : Theta d L g ξ x y = Theta d L g ξ 0 (y - x) := by
  have := Theta_apply_add_right_of_three_le (d := d) (g := g) hL hξ 0 (y - x) x
  rwa [zero_add, sub_add_cancel] at this

open Classical in
/-- **The mean of `f^{far}`**: `𝔼 f^{far}_{σ,a}` is `f^{far}` with `𝓑` replaced by `𝔼𝓑`
(`3_5:2192`, "replacing `𝓑` in `f^{far}` with `𝔼𝓑`"). -/
private theorem meanFar_integral_fFar (n : ℕ) {E s t : ℝ} (hE : |E| < 2) (hs : s < 1)
    (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) :
    ∫ ω, STfFar sz n E s t σ a ω ∂(sz.seqP) =
      (((1 - s) ^ 2 : ℝ) : ℂ) * ∑ b₁ ∈ Finset.univ.filter (fun b₁ : Zd d (sz.L n) =>
          Real.log ((sz.W n : ℕ) : ℝ) ^ 4 * ellT (sz.L n) (sz.lam n) s < ((zdistInf d (sz.L n) (b₁ - a 0) : ℕ) : ℝ) ∧
          Real.log ((sz.W n : ℕ) : ℝ) ^ 4 * ellT (sz.L n) (sz.lam n) s < ((zdistInf d (sz.L n) (b₁ - a 1) : ℕ) : ℝ)),
        ∑ b₂ : Zd d (sz.L n),
          Theta d (sz.L n) (sz.lam n) ((t : ℂ) * (STmsig E (σ 0) * STmsig E (σ 1))) (a 0) b₁ *
            meanFar_B sz n E s σ b₁ b₂ *
            (Theta d (sz.L n) (sz.lam n) ((t : ℂ) * (STmsig E (σ 0) * STmsig E (σ 1))) b₂ (a 1) -
              Theta d (sz.L n) (sz.lam n) ((t : ℂ) * (STmsig E (σ 0) * STmsig E (σ 1))) b₁ (a 1)) := by
  unfold STfFar
  have hX : ∀ b₁ b₂ : Zd d (sz.L n), Integrable
      (fun ω => STLKM sz n E s (sz.seqHflow n s ω) σ ![b₁, b₂]) sz.seqP := by
    intro b₁ b₂
    have h : (fun ω => STLKM sz n E s (sz.seqHflow n s ω) σ ![b₁, b₂]) =
        fun ω => Lloop sz n E s σ ![b₁, b₂] ω - STKloop sz n E s σ ![b₁, b₂] := rfl
    rw [h]
    exact (meanFar_integrable_L sz n hE hs σ _).sub (integrable_const _)
  rw [integral_const_mul]
  congr 1
  rw [integral_finsetSum _ (fun b₁ _ => integrable_finsetSum _
    (fun b₂ _ => ((hX b₁ b₂).const_mul _).mul_const _))]
  refine Finset.sum_congr rfl fun b₁ _ => ?_
  rw [integral_finsetSum _ (fun b₂ _ => ((hX b₁ b₂).const_mul _).mul_const _)]
  refine Finset.sum_congr rfl fun b₂ _ => ?_
  rw [integral_mul_const, integral_const_mul]
  rfl

/-- **The assembly at one size index**: `‖𝔼 f^{far}_{σ,a}‖ ≤ (1-s)² [C_d K₁K₂K (1+log(L+1)) (dw+1)⁴ /
(|a₁-a₂|+1)^{d-2} + 2K₁²K' L^{2d}]` from the decay of the propagator (`hT1`, `hT2`) and of the mean kernel
(`hBx` everywhere, `hBy` beyond the window `w`), with `K = P₀ + ε₁ (dw+1)^{d-2}`, `K' = ε₂`. -/
private theorem meanFar_assemble (n : ℕ) {E s t : ℝ} (hd : 3 ≤ d) (hE : |E| < 2) (hs0 : 0 ≤ s)
    (hst : s < t) (ht : t < 1) (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n))
    (w K₁ K₂ P₀ ε₁ ε₂ : ℝ) (hw : 0 ≤ w) (hK₂ : 0 ≤ K₂) (hε₁ : 0 ≤ ε₁) (hε₂ : 0 ≤ ε₂)
    (hT1 : ∀ x : Zd d (sz.L n),
      ‖Theta d (sz.L n) (sz.lam n) ((t : ℂ) * (STmsig E (σ 0) * STmsig E (σ 1))) 0 x‖ ≤
        K₁ / (((zdistInf d (sz.L n) x : ℕ) : ℝ) + 1) ^ (d - 2))
    (hT2 : ∀ a' r : Zd d (sz.L n), ((zdistD d (sz.L n) r : ℕ) : ℝ) ≤ (d : ℝ) * w →
      Real.log ((sz.W n : ℕ) : ℝ) ^ 4 * ellT (sz.L n) (sz.lam n) s < ((zdistInf d (sz.L n) a' : ℕ) : ℝ) →
      ‖Theta d (sz.L n) (sz.lam n) ((t : ℂ) * (STmsig E (σ 0) * STmsig E (σ 1))) 0 (a' + r) +
          Theta d (sz.L n) (sz.lam n) ((t : ℂ) * (STmsig E (σ 0) * STmsig E (σ 1))) 0 (a' - r) -
          2 * Theta d (sz.L n) (sz.lam n) ((t : ℂ) * (STmsig E (σ 0) * STmsig E (σ 1))) 0 a'‖ ≤
        K₂ * ((zdistD d (sz.L n) r : ℕ) : ℝ) ^ 2 / (((zdistInf d (sz.L n) a' : ℕ) : ℝ) + 1) ^ d)
    (hBx : ∀ x : Zd d (sz.L n), ‖meanFar_B sz n E s σ 0 x‖ ≤
      P₀ / (((zdistInf d (sz.L n) x : ℕ) : ℝ) + 1) ^ (d - 2) + ε₁)
    (hBy : ∀ x : Zd d (sz.L n), w < ((zdistInf d (sz.L n) x : ℕ) : ℝ) → ‖meanFar_B sz n E s σ 0 x‖ ≤ ε₂) :
    ‖∫ ω, STfFar sz n E s t σ a ω ∂(sz.seqP)‖ ≤ (1 - s) ^ 2 *
      (meanFar_Cd d * K₁ * K₂ * (P₀ + ε₁ * ((d : ℝ) * w + 1) ^ (d - 2)) *
          (1 + Real.log (((sz.L n : ℕ) : ℝ) + 1)) * ((d : ℝ) * w + 1) ^ 4 /
          (((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) + 1) ^ (d - 2) +
        2 * K₁ ^ 2 * ε₂ * ((((sz.L n : ℕ) : ℝ)) ^ d) ^ 2) := by
  classical
  have hL := sz.three_le_L n
  have hmsig : ∀ b : Bool, STmsig E b = mSigma E b := fun _ => rfl
  have hξ : ‖(t : ℂ) * (STmsig E (σ 0) * STmsig E (σ 1))‖ < 1 := by
    simp only [hmsig]
    exact norm_mul_mSigma_lt_one hE.le (hs0.trans hst.le) ht (σ 0) (σ 1)
  have hs1 : s < 1 := hst.trans ht
  rw [meanFar_integral_fFar sz n hE hs1 σ a, norm_mul, Complex.norm_real, Real.norm_of_nonneg (sq_nonneg _)]
  refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
  set T : Zd d (sz.L n) → ℂ := fun x =>
    Theta d (sz.L n) (sz.lam n) ((t : ℂ) * (STmsig E (σ 0) * STmsig E (σ 1))) 0 x with hT
  have hshift : ∀ x y : Zd d (sz.L n),
      Theta d (sz.L n) (sz.lam n) ((t : ℂ) * (STmsig E (σ 0) * STmsig E (σ 1))) x y = T (y - x) :=
    fun x y => meanFar_Theta_shift hL hξ x y
  have hrw : ∀ b₁ : Zd d (sz.L n), ∑ b₂ : Zd d (sz.L n),
      Theta d (sz.L n) (sz.lam n) ((t : ℂ) * (STmsig E (σ 0) * STmsig E (σ 1))) (a 0) b₁ *
        meanFar_B sz n E s σ b₁ b₂ *
        (Theta d (sz.L n) (sz.lam n) ((t : ℂ) * (STmsig E (σ 0) * STmsig E (σ 1))) b₂ (a 1) -
          Theta d (sz.L n) (sz.lam n) ((t : ℂ) * (STmsig E (σ 0) * STmsig E (σ 1))) b₁ (a 1)) =
      ∑ b₂ : Zd d (sz.L n), T (b₁ - a 0) * meanFar_B sz n E s σ b₁ b₂ * (T (a 1 - b₂) - T (a 1 - b₁)) := by
    intro b₁
    refine Finset.sum_congr rfl fun b₂ _ => ?_
    rw [hshift, hshift, hshift]
  rw [Finset.sum_congr rfl fun b₁ _ => hrw b₁]
  set ρ : ℝ := Real.log ((sz.W n : ℕ) : ℝ) ^ 4 * ellT (sz.L n) (sz.lam n) s with hρ
  have hw₁ : 0 ≤ (d : ℝ) * w := by positivity
  have hcore := meanFar_core (d := d) (L := sz.L n) hd T (meanFar_B sz n E s σ)
    (meanFar_B_tr sz n hE hs0 hs1 σ) (meanFar_B_sym sz n hE hs0 hs1 σ)
    ρ ((d : ℝ) * w) K₁ K₂ (P₀ + ε₁ * ((d : ℝ) * w + 1) ^ (d - 2)) ε₂ hw₁ hK₂ hε₂ hT1 hT2
    (fun x hx => ?_) (fun x hx => ?_) a
    (Finset.univ.filter (fun b₁ : Zd d (sz.L n) =>
      ρ < ((zdistInf d (sz.L n) (b₁ - a 0) : ℕ) : ℝ) ∧ ρ < ((zdistInf d (sz.L n) (b₁ - a 1) : ℕ) : ℝ)))
    (fun b hb => (Finset.mem_filter.1 hb).2)
  · exact hcore
  · -- `hB1`
    have hxinf : ((zdistInf d (sz.L n) x : ℕ) : ℝ) ≤ (d : ℝ) * w := by
      have : ((zdistInf d (sz.L n) x : ℕ) : ℝ) ≤ ((zdistD d (sz.L n) x : ℕ) : ℝ) := by
        exact_mod_cast zdistInf_le_zdistD d (sz.L n) x
      linarith
    have hY : 0 < (((zdistInf d (sz.L n) x : ℕ) : ℝ) + 1) ^ (d - 2) := by positivity
    have hYle : (((zdistInf d (sz.L n) x : ℕ) : ℝ) + 1) ^ (d - 2) ≤ ((d : ℝ) * w + 1) ^ (d - 2) :=
      pow_le_pow_left₀ (by positivity) (by linarith) _
    calc ‖meanFar_B sz n E s σ 0 x‖
        ≤ P₀ / (((zdistInf d (sz.L n) x : ℕ) : ℝ) + 1) ^ (d - 2) + ε₁ := hBx x
      _ ≤ (P₀ + ε₁ * ((d : ℝ) * w + 1) ^ (d - 2)) / (((zdistInf d (sz.L n) x : ℕ) : ℝ) + 1) ^ (d - 2) := by
          rw [add_div]
          gcongr
          rw [le_div_iff₀ hY]
          nlinarith
  · -- `hB2`
    refine hBy x ?_
    by_contra hcon
    push Not at hcon
    have h1 : ((zdistD d (sz.L n) x : ℕ) : ℝ) ≤ (d : ℝ) * ((zdistInf d (sz.L n) x : ℕ) : ℝ) := by
      exact_mod_cast zdistD_le_mul_zdistInf d (sz.L n) x
    have h2 : (d : ℝ) * ((zdistInf d (sz.L n) x : ℕ) : ℝ) ≤ (d : ℝ) * w :=
      mul_le_mul_of_nonneg_left hcon (Nat.cast_nonneg d)
    linarith

end Expect

/-! ## 5. The numerics of `(eq:boundEfar)` -/

section Numeric

private theorem meanFar_Cd_nonneg (d : ℕ) : 0 ≤ meanFar_Cd d := by
  unfold meanFar_Cd meanFar_cs
  positivity

/-- The last step of `(eq:boundEfar)` (`3_5:2211`): from the bound of the assembly, the relation
`(1-s)² ℓ⁴ ≤ g⁴` (`ℓ_s ≤ g/√(1-s)`), the polylogarithmic bound `lw^{12}(1 + log(L+1)) ≲ N^{τ/4}` and the smallness
`htiny` of the terms with `ε₁ ≤ ε₂`, `≤ N^τ A^{-6/5} (|a₁-a₂|+1)^{-(d-2)}`. -/
private theorem meanFar_numeric_main (d : ℕ) (hd : 3 ≤ d)
    {τ Nn g ℓ lw s Dn A Lr Lg c₀ c₁ c₂ ε₁ ε₂ : ℝ}
    (hN2 : 2 ≤ Nn ^ (τ / 2)) (hN1 : 1 ≤ Nn) (hg : 0 < g) (hℓ : 1 ≤ ℓ) (hlw : 1 ≤ lw)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hDn : 0 ≤ Dn) (hA : 0 < A) (hLg : 0 ≤ Lg)
    (hc₀ : 0 ≤ c₀) (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂) (hε₁ : 0 ≤ ε₁) (hε12 : ε₁ ≤ ε₂)
    (hreg : (1 - s) ^ 2 * ℓ ^ 4 ≤ g ^ 4)
    (hpoly : meanFar_Cd d * c₁ * c₂ * c₀ * (16 * (d : ℝ) ^ 4) * (lw ^ 12 * (1 + Lg)) ≤ Nn ^ (τ / 4))
    (htiny : (g ^ 4)⁻¹ * ε₂ * (meanFar_Cd d * c₁ * c₂ * ((d : ℝ) * (lw ^ 3 * ℓ) + 1) ^ (d + 2) * (1 + Lg) +
      2 * c₁ ^ 2 * (Lr ^ d) ^ 2) ≤ A ^ (-(6 / 5 : ℝ)) / (Dn + 1) ^ (d - 2)) :
    (1 - s) ^ 2 * (meanFar_Cd d * (c₁ / g ^ 2) * (c₂ / g ^ 2) *
          (Nn ^ (τ / 4) * (c₀ * A ^ (-(6 / 5 : ℝ))) + ε₁ * ((d : ℝ) * (lw ^ 3 * ℓ) + 1) ^ (d - 2)) *
          (1 + Lg) * ((d : ℝ) * (lw ^ 3 * ℓ) + 1) ^ 4 / (Dn + 1) ^ (d - 2) +
        2 * (c₁ / g ^ 2) ^ 2 * ε₂ * (Lr ^ d) ^ 2) ≤
      Nn ^ τ * (A ^ (-(6 / 5 : ℝ)) / (Dn + 1) ^ (d - 2)) := by
  have hCd := meanFar_Cd_nonneg d
  have hd0 : (3 : ℝ) ≤ d := by exact_mod_cast hd
  set Cd := meanFar_Cd d with hCddef
  set Y : ℝ := (Dn + 1) ^ (d - 2) with hY
  have hY1 : 1 ≤ Y := one_le_pow₀ (by linarith)
  have hY0 : 0 < Y := by linarith
  set A' : ℝ := A ^ (-(6 / 5 : ℝ)) with hA'
  have hA'0 : 0 < A' := Real.rpow_pos_of_pos hA _
  set X : ℝ := A' / Y with hX
  have hX0 : 0 < X := by positivity
  set u : ℝ := (d : ℝ) * (lw ^ 3 * ℓ) + 1 with hu
  have hw1 : 1 ≤ lw ^ 3 * ℓ := by
    have : 1 ≤ lw ^ 3 := one_le_pow₀ hlw
    nlinarith
  have hdw : 3 ≤ (d : ℝ) * (lw ^ 3 * ℓ) := by nlinarith
  have hu1 : 1 ≤ u := by rw [hu]; linarith
  have hu0 : 0 < u := by linarith
  have hu2 : u ≤ 2 * ((d : ℝ) * (lw ^ 3 * ℓ)) := by rw [hu]; linarith
  have hg0 : 0 < g ^ 2 := by positivity
  have hg4 : 0 < g ^ 4 := by positivity
  have hs2 : (1 - s) ^ 2 ≤ 1 := by nlinarith
  have hs2' : 0 ≤ (1 - s) ^ 2 := sq_nonneg _
  have hNt : (1 : ℝ) ≤ Nn ^ (τ / 2) := by linarith
  have hÑ : 0 ≤ Nn ^ (τ / 4) := Real.rpow_nonneg (by linarith) _
  -- Claim A
  have hA_claim : (1 - s) ^ 2 * (Cd * (c₁ / g ^ 2) * (c₂ / g ^ 2) *
      (Nn ^ (τ / 4) * (c₀ * A')) * (1 + Lg) * u ^ 4 / Y) ≤ Nn ^ (τ / 2) * X := by
    have e1 : (1 - s) ^ 2 * (Cd * (c₁ / g ^ 2) * (c₂ / g ^ 2) *
        (Nn ^ (τ / 4) * (c₀ * A')) * (1 + Lg) * u ^ 4 / Y) =
        Nn ^ (τ / 4) * X * ((1 - s) ^ 2 * u ^ 4 / g ^ 4 * (Cd * c₁ * c₂ * c₀ * (1 + Lg))) := by
      rw [hX]; field_simp
    rw [e1]
    have hu4 : u ^ 4 ≤ 16 * (d : ℝ) ^ 4 * lw ^ 12 * ℓ ^ 4 := by
      have h1 : u ^ 4 ≤ (2 * ((d : ℝ) * (lw ^ 3 * ℓ))) ^ 4 := pow_le_pow_left₀ hu0.le hu2 4
      calc u ^ 4 ≤ (2 * ((d : ℝ) * (lw ^ 3 * ℓ))) ^ 4 := h1
        _ = 16 * (d : ℝ) ^ 4 * lw ^ 12 * ℓ ^ 4 := by ring
    have hb : (1 - s) ^ 2 * u ^ 4 / g ^ 4 * (Cd * c₁ * c₂ * c₀ * (1 + Lg)) ≤ Nn ^ (τ / 4) := by
      have h1 : (1 - s) ^ 2 * u ^ 4 / g ^ 4 ≤ 16 * (d : ℝ) ^ 4 * lw ^ 12 := by
        rw [div_le_iff₀ hg4]
        calc (1 - s) ^ 2 * u ^ 4 ≤ (1 - s) ^ 2 * (16 * (d : ℝ) ^ 4 * lw ^ 12 * ℓ ^ 4) :=
              mul_le_mul_of_nonneg_left hu4 hs2'
          _ = 16 * (d : ℝ) ^ 4 * lw ^ 12 * ((1 - s) ^ 2 * ℓ ^ 4) := by ring
          _ ≤ 16 * (d : ℝ) ^ 4 * lw ^ 12 * g ^ 4 := by gcongr
      calc _ ≤ 16 * (d : ℝ) ^ 4 * lw ^ 12 * (Cd * c₁ * c₂ * c₀ * (1 + Lg)) := by
            gcongr
        _ = Cd * c₁ * c₂ * c₀ * (16 * (d : ℝ) ^ 4) * (lw ^ 12 * (1 + Lg)) := by ring
        _ ≤ _ := hpoly
    calc Nn ^ (τ / 4) * X * ((1 - s) ^ 2 * u ^ 4 / g ^ 4 * (Cd * c₁ * c₂ * c₀ * (1 + Lg)))
        ≤ Nn ^ (τ / 4) * X * Nn ^ (τ / 4) := by gcongr
      _ = Nn ^ (τ / 2) * X := by
          have : Nn ^ (τ / 2) = Nn ^ (τ / 4) * Nn ^ (τ / 4) := by
            rw [← Real.rpow_add (by linarith)]; ring_nf
          rw [this]; ring
  -- Claim B
  have hB_claim : (1 - s) ^ 2 * (Cd * (c₁ / g ^ 2) * (c₂ / g ^ 2) * (ε₁ * u ^ (d - 2)) * (1 + Lg) * u ^ 4 / Y) ≤
      (g ^ 4)⁻¹ * ε₂ * (Cd * c₁ * c₂ * u ^ (d + 2) * (1 + Lg)) := by
    have e1 : Cd * (c₁ / g ^ 2) * (c₂ / g ^ 2) * (ε₁ * u ^ (d - 2)) * (1 + Lg) * u ^ 4 / Y =
        (g ^ 4)⁻¹ * ε₁ * (Cd * c₁ * c₂ * u ^ (d + 2) * (1 + Lg)) / Y := by
      have : u ^ (d + 2) = u ^ (d - 2) * u ^ 4 := by rw [← pow_add]; congr 1; omega
      rw [this]; field_simp
    rw [e1]
    have h0 : 0 ≤ (g ^ 4)⁻¹ * (Cd * c₁ * c₂ * u ^ (d + 2) * (1 + Lg)) := by positivity
    calc (1 - s) ^ 2 * ((g ^ 4)⁻¹ * ε₁ * (Cd * c₁ * c₂ * u ^ (d + 2) * (1 + Lg)) / Y)
        ≤ 1 * ((g ^ 4)⁻¹ * ε₁ * (Cd * c₁ * c₂ * u ^ (d + 2) * (1 + Lg)) / 1) := by
          gcongr
      _ = ε₁ * ((g ^ 4)⁻¹ * (Cd * c₁ * c₂ * u ^ (d + 2) * (1 + Lg))) := by ring
      _ ≤ ε₂ * ((g ^ 4)⁻¹ * (Cd * c₁ * c₂ * u ^ (d + 2) * (1 + Lg))) :=
          mul_le_mul_of_nonneg_right hε12 h0
      _ = _ := by ring
  -- Claim C
  have hC_claim : (1 - s) ^ 2 * (2 * (c₁ / g ^ 2) ^ 2 * ε₂ * (Lr ^ d) ^ 2) ≤
      (g ^ 4)⁻¹ * ε₂ * (2 * c₁ ^ 2 * (Lr ^ d) ^ 2) := by
    have e1 : 2 * (c₁ / g ^ 2) ^ 2 * ε₂ * (Lr ^ d) ^ 2 = (g ^ 4)⁻¹ * ε₂ * (2 * c₁ ^ 2 * (Lr ^ d) ^ 2) := by
      field_simp
    rw [e1]
    have h0 : 0 ≤ (g ^ 4)⁻¹ * ε₂ * (2 * c₁ ^ 2 * (Lr ^ d) ^ 2) := by
      have : 0 ≤ ε₂ := hε₁.trans hε12
      positivity
    have h1 := mul_le_mul_of_nonneg_right hs2 h0
    linarith
  -- assemble
  have hsplit : (1 - s) ^ 2 * (Cd * (c₁ / g ^ 2) * (c₂ / g ^ 2) *
          (Nn ^ (τ / 4) * (c₀ * A') + ε₁ * u ^ (d - 2)) * (1 + Lg) * u ^ 4 / Y +
        2 * (c₁ / g ^ 2) ^ 2 * ε₂ * (Lr ^ d) ^ 2) =
      (1 - s) ^ 2 * (Cd * (c₁ / g ^ 2) * (c₂ / g ^ 2) * (Nn ^ (τ / 4) * (c₀ * A')) * (1 + Lg) * u ^ 4 / Y) +
      (1 - s) ^ 2 * (Cd * (c₁ / g ^ 2) * (c₂ / g ^ 2) * (ε₁ * u ^ (d - 2)) * (1 + Lg) * u ^ 4 / Y) +
      (1 - s) ^ 2 * (2 * (c₁ / g ^ 2) ^ 2 * ε₂ * (Lr ^ d) ^ 2) := by ring
  rw [hsplit]
  have hBC : (g ^ 4)⁻¹ * ε₂ * (Cd * c₁ * c₂ * u ^ (d + 2) * (1 + Lg)) +
      (g ^ 4)⁻¹ * ε₂ * (2 * c₁ ^ 2 * (Lr ^ d) ^ 2) ≤ X := by
    have : (g ^ 4)⁻¹ * ε₂ * (Cd * c₁ * c₂ * u ^ (d + 2) * (1 + Lg)) +
        (g ^ 4)⁻¹ * ε₂ * (2 * c₁ ^ 2 * (Lr ^ d) ^ 2) =
        (g ^ 4)⁻¹ * ε₂ * (Cd * c₁ * c₂ * u ^ (d + 2) * (1 + Lg) + 2 * c₁ ^ 2 * (Lr ^ d) ^ 2) := by ring
    rw [this]
    exact htiny
  have hXN : X ≤ Nn ^ (τ / 2) * X := le_mul_of_one_le_left hX0.le hNt
  have hNN : Nn ^ τ = Nn ^ (τ / 2) * Nn ^ (τ / 2) := by
    rw [← Real.rpow_add (by linarith)]; ring_nf
  calc _ ≤ Nn ^ (τ / 2) * X + (g ^ 4)⁻¹ * ε₂ * (Cd * c₁ * c₂ * u ^ (d + 2) * (1 + Lg)) +
        (g ^ 4)⁻¹ * ε₂ * (2 * c₁ ^ 2 * (Lr ^ d) ^ 2) := by gcongr
    _ ≤ Nn ^ (τ / 2) * X + X := by linarith
    _ ≤ Nn ^ (τ / 2) * X + Nn ^ (τ / 2) * X := by linarith
    _ = 2 * Nn ^ (τ / 2) * X := by ring
    _ ≤ Nn ^ (τ / 2) * Nn ^ (τ / 2) * X := by
        have : 2 * Nn ^ (τ / 2) ≤ Nn ^ (τ / 2) * Nn ^ (τ / 2) :=
          mul_le_mul_of_nonneg_right hN2 (by linarith)
        exact mul_le_mul_of_nonneg_right this hX0.le
    _ = Nn ^ τ * X := by rw [hNN]

end Numeric

/-! ## 6. The size-dependent facts at one index `n` -/

section SizeFacts

variable {d : ℕ}

/-- `ℓ_s ≤ g/√(1-s)` when `1-s ≤ g²`: `(1-s) ℓ_s² ≤ g²`, i.e. `(1-s)² ℓ_s⁴ ≤ g⁴`. -/
private theorem meanFar_ell_sq {L : ℕ} {g s : ℝ} (hg : 0 < g) (hs : s < 1) (h : 1 - s ≤ g ^ 2) :
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

/-- `B_{t,K}` is dominated by `(1 + 2^{d-1}) g^{-2} (K+1)^{-(d-2)}` for `K ≤ L`, `1 - t ≥ g²/L²`. -/
private theorem meanFar_Bparam_le (hd : 3 ≤ d) {L : ℕ} (hL : 3 ≤ L) {g t : ℝ} (hg : 0 < g) (ht : t < 1)
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

/-- The constant `1 + 2^{d-1}` of `meanFar_Bparam_le`. -/
private def meanFar_c3 (d : ℕ) : ℝ := 1 + 2 ^ (d - 1)

/-- The constant `c₃^{1/5} c₃` of `(eq:propcalB)`. -/
private def meanFar_c0 (d : ℕ) : ℝ := meanFar_c3 d ^ (1 / 5 : ℝ) * meanFar_c3 d

private theorem meanFar_c3_pos (d : ℕ) : 0 < meanFar_c3 d := by unfold meanFar_c3; positivity

/-- `(W^{-d} B_{s,0})^{1/5} (W^{-d} B_{s,K}) ≤ c₀ A^{-6/5} (K+1)^{-(d-2)}`, `A = g² W^d`
(`(eq:propcalB)` with `(Eq:Gdecay_w)`, `3_5:2139-2150`). -/
private theorem meanFar_BctlSTWB (sz : Sizes d) (n : ℕ) (hd : 3 ≤ d) {s : ℝ} (hs : s < 1)
    (hg : 0 < sz.lam n) (hreg : sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 ≤ 1 - s) (K : ℕ)
    (hK : K ≤ sz.L n) :
    sz.Bctl n s ^ (1 / 5 : ℝ) * STWB sz n s K ≤
      meanFar_c0 d * STAI sz n ^ (-(6 / 5 : ℝ)) / (((K : ℕ) : ℝ) + 1) ^ (d - 2) := by
  have hL := sz.three_le_L n
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hWd : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) ^ d := by positivity
  set A : ℝ := STAI sz n with hAdef
  have hA : 0 < A := by rw [hAdef]; unfold STAI; positivity
  have hAe : A = sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d := rfl
  have hc3 := meanFar_c3_pos d
  have hB0 := meanFar_Bparam_le hd hL hg hs hreg 0 (Nat.zero_le _)
  have hBK := meanFar_Bparam_le hd hL hg hs hreg K hK
  have hBctl : sz.Bctl n s ≤ meanFar_c3 d / A := by
    unfold Sizes.Bctl
    refine (mul_le_mul_of_nonneg_left hB0 (by positivity)).trans ?_
    simp only [Nat.cast_zero, zero_add, one_pow, inv_one, mul_one]
    rw [hAe]; unfold meanFar_c3
    field_simp
    rfl
  have hSTWB : STWB sz n s K ≤ meanFar_c3 d / A / (((K : ℕ) : ℝ) + 1) ^ (d - 2) := by
    unfold STWB
    refine (mul_le_mul_of_nonneg_left hBK (by positivity)).trans ?_
    rw [hAe]; unfold meanFar_c3
    field_simp
    rfl
  have hBctl0 : 0 ≤ sz.Bctl n s := by
    unfold Sizes.Bctl Bparam
    have : 0 < 1 - s := by linarith
    rw [abs_of_pos this]
    positivity
  have h15 : sz.Bctl n s ^ (1 / 5 : ℝ) ≤ (meanFar_c3 d / A) ^ (1 / 5 : ℝ) :=
    Real.rpow_le_rpow hBctl0 hBctl (by norm_num)
  have hrp : (meanFar_c3 d / A) ^ (1 / 5 : ℝ) = meanFar_c3 d ^ (1 / 5 : ℝ) * A ^ (-(1 / 5 : ℝ)) := by
    rw [Real.div_rpow hc3.le hA.le, Real.rpow_neg hA.le, div_eq_mul_inv]
  have hA65 : A ^ (-(6 / 5 : ℝ)) = A ^ (-(1 / 5 : ℝ)) * A⁻¹ := by
    rw [← Real.rpow_neg_one, ← Real.rpow_add hA]; congr 1; norm_num
  have hSW0 : 0 ≤ STWB sz n s K := by
    unfold STWB Bparam
    have : 0 < 1 - s := by linarith
    rw [abs_of_pos this]
    positivity
  calc sz.Bctl n s ^ (1 / 5 : ℝ) * STWB sz n s K
      ≤ (meanFar_c3 d ^ (1 / 5 : ℝ) * A ^ (-(1 / 5 : ℝ))) * (meanFar_c3 d / A / (((K : ℕ) : ℝ) + 1) ^ (d - 2)) := by
        rw [← hrp]
        exact mul_le_mul h15 hSTWB hSW0 (Real.rpow_nonneg (by positivity) _)
    _ = meanFar_c0 d * A ^ (-(6 / 5 : ℝ)) / (((K : ℕ) : ℝ) + 1) ^ (d - 2) := by
        rw [hA65]; unfold meanFar_c0; field_simp

/-- **The decay of `𝔼 𝓑`** (`(eq:propcalB)`, `3_5:2139-2150`, in expectation): from the `≺` bound off an
event of probability `≤ N^{-D₁}` (`hP`) and the a.s. envelope, for every `x`
`‖𝔼𝓑_{0x}‖ ≤ P₀/(|x|+1)^{d-2} + ε₁` and, beyond the window `w = (log W)³ ℓ_s`, `‖𝔼𝓑_{0x}‖ ≤ ε₂`. -/
private theorem meanFar_n_kernel (sz : Sizes d) (n : ℕ) (hd : 3 ≤ d) {E s : ℝ} (hE : |E| < 2) (hs : s < 1)
    (hg : 0 < sz.lam n) (hreg : sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 ≤ 1 - s)
    {τ₁ D₁ Dw Kmax : ℝ}
    (hP : ∀ (σ : Fin 2 → Bool) (a b : Zd d (sz.L n)),
      sz.seqP {ω | ((sz.size n : ℕ) : ℝ) ^ τ₁ *
          (sz.Bctl n s ^ (1 / 5 : ℝ) * STWB sz n s (zdistInf d (sz.L n) (a - b)) *
            Real.exp (-(((zdistInf d (sz.L n) (a - b) : ℕ) : ℝ) / ellT (sz.L n) (sz.lam n) s) ^ (1 / 2 : ℝ)) +
            ((sz.W n : ℕ) : ℝ) ^ (-Dw)) <
          ‖STLKM sz n E s (sz.seqHflow n s ω) σ ![a, b]‖} ≤
        ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-D₁)))
    (hK : ∀ (σ : Fin 2 → Bool) (a b : Zd d (sz.L n)), ‖STKloop sz n E s σ ![a, b]‖ ≤ Kmax)
    (σ : Fin 2 → Bool) :
    (∀ x : Zd d (sz.L n), ‖meanFar_B sz n E s σ 0 x‖ ≤
        (((sz.size n : ℕ) : ℝ) ^ τ₁ * (meanFar_c0 d * STAI sz n ^ (-(6 / 5 : ℝ)))) /
            (((zdistInf d (sz.L n) x : ℕ) : ℝ) + 1) ^ (d - 2) +
          (((sz.size n : ℕ) : ℝ) ^ τ₁ * ((sz.W n : ℕ) : ℝ) ^ (-Dw) +
            ((etaT E s)⁻¹ ^ 2 + Kmax) * ((sz.size n : ℕ) : ℝ) ^ (-D₁))) ∧
    (∀ x : Zd d (sz.L n), Real.log ((sz.W n : ℕ) : ℝ) ^ 3 * ellT (sz.L n) (sz.lam n) s <
        ((zdistInf d (sz.L n) x : ℕ) : ℝ) → ‖meanFar_B sz n E s σ 0 x‖ ≤
        ((sz.size n : ℕ) : ℝ) ^ τ₁ * (meanFar_c0 d * STAI sz n ^ (-(6 / 5 : ℝ)) *
            Real.exp (-(Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ)))) +
          (((sz.size n : ℕ) : ℝ) ^ τ₁ * ((sz.W n : ℕ) : ℝ) ^ (-Dw) +
            ((etaT E s)⁻¹ ^ 2 + Kmax) * ((sz.size n : ℕ) : ℝ) ^ (-D₁))) := by
  have hL := sz.three_le_L n
  have hW1 : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hNn : (0 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := Nat.cast_nonneg _
  have hℓ0 : 0 < ellT (sz.L n) (sz.lam n) s := ellT_pos (by exact_mod_cast (by omega : 1 ≤ sz.L n))
  -- the general pointwise bound for `x`
  have hpt : ∀ x : Zd d (sz.L n), ‖meanFar_B sz n E s σ 0 x‖ ≤
      ((sz.size n : ℕ) : ℝ) ^ τ₁ *
        (sz.Bctl n s ^ (1 / 5 : ℝ) * STWB sz n s (zdistInf d (sz.L n) x) *
          Real.exp (-(((zdistInf d (sz.L n) x : ℕ) : ℝ) / ellT (sz.L n) (sz.lam n) s) ^ (1 / 2 : ℝ)) +
          ((sz.W n : ℕ) : ℝ) ^ (-Dw)) +
        ((etaT E s)⁻¹ ^ 2 + Kmax) * ((sz.size n : ℕ) : ℝ) ^ (-D₁) := by
    intro x
    have hz : zdistInf d (sz.L n) ((0 : Zd d (sz.L n)) - x) = zdistInf d (sz.L n) x := by
      rw [zero_sub, meanFar_zdistInf_neg]
    have hP' := hP σ 0 x
    rw [hz] at hP'
    have hZ : 0 ≤ ((sz.size n : ℕ) : ℝ) ^ τ₁ *
        (sz.Bctl n s ^ (1 / 5 : ℝ) * STWB sz n s (zdistInf d (sz.L n) x) *
          Real.exp (-(((zdistInf d (sz.L n) x : ℕ) : ℝ) / ellT (sz.L n) (sz.lam n) s) ^ (1 / 2 : ℝ)) +
          ((sz.W n : ℕ) : ℝ) ^ (-Dw)) := by
      have hB0 : 0 ≤ sz.Bctl n s := by
        unfold Sizes.Bctl Bparam
        have : 0 < 1 - s := by linarith
        rw [abs_of_pos this]; positivity
      have hS0 : 0 ≤ STWB sz n s (zdistInf d (sz.L n) x) := by
        unfold STWB Bparam
        have : 0 < 1 - s := by linarith
        rw [abs_of_pos this]; positivity
      positivity
    have h := meanFar_B_bound sz n hE hs σ 0 x hZ hP'
    refine h.trans ?_
    have hK' := hK σ 0 x
    have hDD : 0 ≤ ((sz.size n : ℕ) : ℝ) ^ (-D₁) := Real.rpow_nonneg hNn _
    have hη : 0 ≤ (etaT E s)⁻¹ ^ 2 := by positivity
    gcongr
  have hBW : ∀ x : Zd d (sz.L n), sz.Bctl n s ^ (1 / 5 : ℝ) * STWB sz n s (zdistInf d (sz.L n) x) ≤
      meanFar_c0 d * STAI sz n ^ (-(6 / 5 : ℝ)) / (((zdistInf d (sz.L n) x : ℕ) : ℝ) + 1) ^ (d - 2) :=
    fun x => meanFar_BctlSTWB sz n hd hs hg hreg _ (meanFar_zdistInf_le x)
  have hexp1 : ∀ x : Zd d (sz.L n), Real.exp (-(((zdistInf d (sz.L n) x : ℕ) : ℝ) /
      ellT (sz.L n) (sz.lam n) s) ^ (1 / 2 : ℝ)) ≤ 1 := by
    intro x
    rw [Real.exp_le_one_iff, neg_nonpos]
    exact Real.rpow_nonneg (div_nonneg (Nat.cast_nonneg _) hℓ0.le) _
  have hBW0 : ∀ x : Zd d (sz.L n), 0 ≤ sz.Bctl n s ^ (1 / 5 : ℝ) * STWB sz n s (zdistInf d (sz.L n) x) := by
    intro x
    have hB0 : 0 ≤ sz.Bctl n s := by
      unfold Sizes.Bctl Bparam
      have : 0 < 1 - s := by linarith
      rw [abs_of_pos this]; positivity
    have hS0 : 0 ≤ STWB sz n s (zdistInf d (sz.L n) x) := by
      unfold STWB Bparam
      have : 0 < 1 - s := by linarith
      rw [abs_of_pos this]; positivity
    positivity
  refine ⟨fun x => ?_, fun x hx => ?_⟩
  · refine (hpt x).trans ?_
    have h1 : sz.Bctl n s ^ (1 / 5 : ℝ) * STWB sz n s (zdistInf d (sz.L n) x) *
        Real.exp (-(((zdistInf d (sz.L n) x : ℕ) : ℝ) / ellT (sz.L n) (sz.lam n) s) ^ (1 / 2 : ℝ)) ≤
        meanFar_c0 d * STAI sz n ^ (-(6 / 5 : ℝ)) / (((zdistInf d (sz.L n) x : ℕ) : ℝ) + 1) ^ (d - 2) :=
      calc _ ≤ sz.Bctl n s ^ (1 / 5 : ℝ) * STWB sz n s (zdistInf d (sz.L n) x) * 1 :=
            mul_le_mul_of_nonneg_left (hexp1 x) (hBW0 x)
        _ ≤ _ := by rw [mul_one]; exact hBW x
    have h2 := mul_le_mul_of_nonneg_left (add_le_add_left h1 (((sz.W n : ℕ) : ℝ) ^ (-Dw)))
      (Real.rpow_nonneg hNn τ₁)
    have e : ((sz.size n : ℕ) : ℝ) ^ τ₁ * (meanFar_c0 d * STAI sz n ^ (-(6 / 5 : ℝ)) /
        (((zdistInf d (sz.L n) x : ℕ) : ℝ) + 1) ^ (d - 2) + ((sz.W n : ℕ) : ℝ) ^ (-Dw)) =
        ((sz.size n : ℕ) : ℝ) ^ τ₁ * (meanFar_c0 d * STAI sz n ^ (-(6 / 5 : ℝ))) /
            (((zdistInf d (sz.L n) x : ℕ) : ℝ) + 1) ^ (d - 2) +
          ((sz.size n : ℕ) : ℝ) ^ τ₁ * ((sz.W n : ℕ) : ℝ) ^ (-Dw) := by ring
    rw [e] at h2
    linarith
  · refine (hpt x).trans ?_
    -- beyond the window the exponential is `≤ exp(-(log W)^{3/2})`
    have hxℓ : Real.log ((sz.W n : ℕ) : ℝ) ^ 3 ≤
        ((zdistInf d (sz.L n) x : ℕ) : ℝ) / ellT (sz.L n) (sz.lam n) s := by
      rw [le_div_iff₀ hℓ0]; exact hx.le
    have hlw0 : 0 ≤ Real.log ((sz.W n : ℕ) : ℝ) := Real.log_nonneg hW1
    have hpow : Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ) ≤
        (((zdistInf d (sz.L n) x : ℕ) : ℝ) / ellT (sz.L n) (sz.lam n) s) ^ (1 / 2 : ℝ) := by
      have h1 : (Real.log ((sz.W n : ℕ) : ℝ) ^ 3) ^ (1 / 2 : ℝ) ≤
          (((zdistInf d (sz.L n) x : ℕ) : ℝ) / ellT (sz.L n) (sz.lam n) s) ^ (1 / 2 : ℝ) :=
        Real.rpow_le_rpow (pow_nonneg hlw0 3) hxℓ (by norm_num)
      have h2 : (Real.log ((sz.W n : ℕ) : ℝ) ^ 3) ^ (1 / 2 : ℝ) = Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hlw0]; norm_num
      rwa [h2] at h1
    have hexp2 : Real.exp (-(((zdistInf d (sz.L n) x : ℕ) : ℝ) / ellT (sz.L n) (sz.lam n) s) ^ (1 / 2 : ℝ)) ≤
        Real.exp (-(Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ))) :=
      Real.exp_le_exp.2 (neg_le_neg hpow)
    have h1 : sz.Bctl n s ^ (1 / 5 : ℝ) * STWB sz n s (zdistInf d (sz.L n) x) *
        Real.exp (-(((zdistInf d (sz.L n) x : ℕ) : ℝ) / ellT (sz.L n) (sz.lam n) s) ^ (1 / 2 : ℝ)) ≤
        meanFar_c0 d * STAI sz n ^ (-(6 / 5 : ℝ)) * Real.exp (-(Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ))) := by
      have hY : 1 ≤ (((zdistInf d (sz.L n) x : ℕ) : ℝ) + 1) ^ (d - 2) :=
        one_le_pow₀ (by have : (0 : ℝ) ≤ ((zdistInf d (sz.L n) x : ℕ) : ℝ) := Nat.cast_nonneg _; linarith)
      have hc0 : 0 ≤ meanFar_c0 d * STAI sz n ^ (-(6 / 5 : ℝ)) := by
        unfold meanFar_c0
        have := meanFar_c3_pos d
        have hA : 0 < STAI sz n := by unfold STAI; positivity
        positivity
      calc _ ≤ (meanFar_c0 d * STAI sz n ^ (-(6 / 5 : ℝ)) / (((zdistInf d (sz.L n) x : ℕ) : ℝ) + 1) ^ (d - 2)) *
              Real.exp (-(((zdistInf d (sz.L n) x : ℕ) : ℝ) / ellT (sz.L n) (sz.lam n) s) ^ (1 / 2 : ℝ)) :=
            mul_le_mul_of_nonneg_right (hBW x) (Real.exp_pos _).le
        _ ≤ (meanFar_c0 d * STAI sz n ^ (-(6 / 5 : ℝ))) * Real.exp (-(Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ))) := by
            refine mul_le_mul ?_ hexp2 (Real.exp_pos _).le hc0
            exact div_le_self hc0 hY
    have h2 := mul_le_mul_of_nonneg_left (add_le_add_left h1 (((sz.W n : ℕ) : ℝ) ^ (-Dw)))
      (Real.rpow_nonneg hNn τ₁)
    have e : ((sz.size n : ℕ) : ℝ) ^ τ₁ * (meanFar_c0 d * STAI sz n ^ (-(6 / 5 : ℝ)) *
          Real.exp (-(Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ))) + ((sz.W n : ℕ) : ℝ) ^ (-Dw)) =
        ((sz.size n : ℕ) : ℝ) ^ τ₁ * (meanFar_c0 d * STAI sz n ^ (-(6 / 5 : ℝ)) *
            Real.exp (-(Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ)))) +
          ((sz.size n : ℕ) : ℝ) ^ τ₁ * ((sz.W n : ℕ) : ℝ) ^ (-Dw) := by ring
    rw [e] at h2
    linarith

/-- `‖𝒦^{(2)}_{s,σ,(a,b)}‖ ≤ c₁/A` from the decay of `T = Θ(0,·)`: `𝒦^{(2)} = W^{-d} m₁m₂ Θ(a,b)`,
`|m₁ m₂| = 1`, `Θ(a,b) = T(b - a)`. -/
private theorem meanFar_n_K (sz : Sizes d) (n : ℕ) {E s : ℝ} (hE : |E| < 2) (hs0 : 0 ≤ s) (hs : s < 1)
    (σ : Fin 2 → Bool) (a b : Zd d (sz.L n)) {K₁ : ℝ}
    (hT : ∀ x : Zd d (sz.L n),
      ‖Theta d (sz.L n) (sz.lam n) ((s : ℂ) * (mSigma E (σ 0) * mSigma E (σ 1))) 0 x‖ ≤ K₁) :
    ‖STKloop sz n E s σ ![a, b]‖ ≤ (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * K₁ := by
  have hL := sz.three_le_L n
  have hξ := norm_mul_mSigma_lt_one hE.le hs0 hs (σ 0) (σ 1)
  rw [meanFar_K_eq, norm_mul, norm_mul, norm_mul, norm_mSigma hE.le, norm_mSigma hE.le, mul_one, mul_one,
    norm_inv, norm_pow, Complex.norm_natCast, meanFar_Theta_shift hL hξ]
  exact mul_le_mul_of_nonneg_left (hT _) (by positivity)

end SizeFacts

/-- The smallness `htiny` of `meanFar_numeric_main`: polynomial factors in `N` times `ε₂ ≤ (c₀+2) N^{-(5d+12)}`
are `≤ A^{-6/5}(|a₁-a₂|+1)^{-(d-2)}`, which is `≳ N^{-d}`. -/
private theorem meanFar_tiny (d : ℕ) (hd : 3 ≤ d)
    {Nn g ℓ lw A Dn Lr Lg Λ c₀ c₁ c₂ ε₂ : ℝ}
    (hN1 : 1 ≤ Nn) (hg2 : 1 ≤ g ^ 2 * Nn) (hA1 : 1 ≤ A) (hAΛ : A ≤ Λ ^ 2 * Nn) (hΛ : 0 < Λ)
    (hℓ1 : 1 ≤ ℓ) (hℓL : ℓ ≤ Lr) (hLr : Lr ≤ Nn) (hLd : Lr ^ d ≤ Nn) (hlw1 : 1 ≤ lw) (hlwN : lw ≤ Nn)
    (hDn0 : 0 ≤ Dn) (hDnN : Dn ≤ Nn) (hLg : 0 ≤ Lg) (hLg' : 1 + Lg ≤ 3 * Nn)
    (hc₀ : 0 ≤ c₀) (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂) (hε₂0 : 0 ≤ ε₂)
    (hε₂ : ε₂ ≤ (c₀ + 2) * (Nn ^ (5 * d + 12))⁻¹)
    (hbig : (3 * meanFar_Cd d * c₁ * c₂ * ((d : ℝ) + 1) ^ (d + 2) + 2 * c₁ ^ 2) * (c₀ + 2) * Λ ^ 4 * 2 ^ (d - 2) ≤ Nn) :
    (g ^ 4)⁻¹ * ε₂ * (meanFar_Cd d * c₁ * c₂ * ((d : ℝ) * (lw ^ 3 * ℓ) + 1) ^ (d + 2) * (1 + Lg) +
      2 * c₁ ^ 2 * (Lr ^ d) ^ 2) ≤ A ^ (-(6 / 5 : ℝ)) / (Dn + 1) ^ (d - 2) := by
  have hCd := meanFar_Cd_nonneg d
  set Cd := meanFar_Cd d with hCddef
  have hNn0 : 0 < Nn := by linarith
  have hg0 : 0 < g ^ 2 := by
    by_contra h
    push Not at h
    have : g ^ 2 * Nn ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h hNn0.le
    linarith
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  -- the lower bound for the right-hand side
  have hX : (Λ ^ 4 * 2 ^ (d - 2) * Nn ^ d)⁻¹ ≤ A ^ (-(6 / 5 : ℝ)) / (Dn + 1) ^ (d - 2) := by
    have h1 : (A ^ 2)⁻¹ ≤ A ^ (-(6 / 5 : ℝ)) := by
      have : (A ^ 2)⁻¹ = A ^ (-(2 : ℝ)) := by
        rw [Real.rpow_neg (by linarith), Real.rpow_two]
      rw [this]
      exact Real.rpow_le_rpow_of_exponent_le hA1 (by norm_num)
    have h2 : (Λ ^ 4 * Nn ^ 2)⁻¹ ≤ (A ^ 2)⁻¹ := by
      refine inv_anti₀ (by positivity) ?_
      calc A ^ 2 ≤ (Λ ^ 2 * Nn) ^ 2 := pow_le_pow_left₀ (by linarith) hAΛ 2
        _ = Λ ^ 4 * Nn ^ 2 := by ring
    have h3 : (Dn + 1) ^ (d - 2) ≤ (2 * Nn) ^ (d - 2) := pow_le_pow_left₀ (by linarith) (by linarith) _
    have hA0 : 0 ≤ A ^ (-(6 / 5 : ℝ)) := Real.rpow_nonneg (by linarith) _
    have e : (Λ ^ 4 * 2 ^ (d - 2) * Nn ^ d)⁻¹ = (Λ ^ 4 * Nn ^ 2)⁻¹ / (2 * Nn) ^ (d - 2) := by
      have : Nn ^ d = Nn ^ 2 * Nn ^ (d - 2) := by rw [← pow_add]; congr 1; omega
      rw [this, mul_pow]
      field_simp
    rw [e]
    exact div_le_div₀ hA0 (h2.trans h1) (by positivity) h3
  refine le_trans ?_ hX
  -- the polynomial bounds
  have hg4 : (g ^ 4)⁻¹ ≤ Nn ^ 2 := by
    have h1 : (g ^ 2)⁻¹ ≤ Nn := (inv_le_iff_one_le_mul₀' hg0).2 hg2
    have e : (g ^ 4)⁻¹ = ((g ^ 2)⁻¹) ^ 2 := by rw [inv_pow, ← pow_mul]
    rw [e]
    exact pow_le_pow_left₀ (by positivity) h1 2
  have hlwN3 : lw ^ 3 ≤ Nn ^ 3 := pow_le_pow_left₀ (by linarith) hlwN 3
  have hℓN : ℓ ≤ Nn := hℓL.trans hLr
  have hw : lw ^ 3 * ℓ ≤ Nn ^ 4 :=
    calc lw ^ 3 * ℓ ≤ Nn ^ 3 * Nn := mul_le_mul hlwN3 hℓN (by linarith) (by positivity)
      _ = Nn ^ 4 := by ring
  have hu : (d : ℝ) * (lw ^ 3 * ℓ) + 1 ≤ ((d : ℝ) + 1) * Nn ^ 4 := by
    have h1 : 1 ≤ Nn ^ 4 := one_le_pow₀ hN1
    have := mul_le_mul_of_nonneg_left hw hd0
    nlinarith
  have hu2 : ((d : ℝ) * (lw ^ 3 * ℓ) + 1) ^ (d + 2) ≤ ((d : ℝ) + 1) ^ (d + 2) * Nn ^ (4 * d + 8) := by
    calc _ ≤ (((d : ℝ) + 1) * Nn ^ 4) ^ (d + 2) := pow_le_pow_left₀ (by positivity) hu _
      _ = ((d : ℝ) + 1) ^ (d + 2) * Nn ^ (4 * d + 8) := by
          rw [mul_pow, ← pow_mul]; congr 2
  have hLd2 : (Lr ^ d) ^ 2 ≤ Nn ^ (4 * d + 9) := by
    have h1 : (Lr ^ d) ^ 2 ≤ Nn ^ 2 := pow_le_pow_left₀ (by
      have : 0 ≤ Lr := by linarith
      positivity) hLd 2
    exact h1.trans (pow_le_pow_right₀ hN1 (by omega))
  set CB : ℝ := 3 * Cd * c₁ * c₂ * ((d : ℝ) + 1) ^ (d + 2) + 2 * c₁ ^ 2 with hCB
  have hCB0 : 0 ≤ CB := by positivity
  have hBn : Cd * c₁ * c₂ * ((d : ℝ) * (lw ^ 3 * ℓ) + 1) ^ (d + 2) * (1 + Lg) + 2 * c₁ ^ 2 * (Lr ^ d) ^ 2 ≤
      CB * Nn ^ (4 * d + 9) := by
    have h1 : Cd * c₁ * c₂ * ((d : ℝ) * (lw ^ 3 * ℓ) + 1) ^ (d + 2) * (1 + Lg) ≤
        Cd * c₁ * c₂ * (((d : ℝ) + 1) ^ (d + 2) * Nn ^ (4 * d + 8)) * (3 * Nn) := by
      have h0 : 0 ≤ Cd * c₁ * c₂ := by positivity
      calc _ ≤ Cd * c₁ * c₂ * (((d : ℝ) + 1) ^ (d + 2) * Nn ^ (4 * d + 8)) * (1 + Lg) := by
            gcongr
        _ ≤ _ := by gcongr
    have h2 : 2 * c₁ ^ 2 * (Lr ^ d) ^ 2 ≤ 2 * c₁ ^ 2 * Nn ^ (4 * d + 9) := by gcongr
    have e : Cd * c₁ * c₂ * (((d : ℝ) + 1) ^ (d + 2) * Nn ^ (4 * d + 8)) * (3 * Nn) =
        3 * Cd * c₁ * c₂ * ((d : ℝ) + 1) ^ (d + 2) * Nn ^ (4 * d + 9) := by
      rw [pow_succ (n := 4 * d + 8)]; ring
    rw [e] at h1
    rw [hCB]; linarith
  have hε₂' : ε₂ ≤ (c₀ + 2) * (Nn ^ (5 * d + 12))⁻¹ := hε₂
  have hmain : (g ^ 4)⁻¹ * ε₂ * (Cd * c₁ * c₂ * ((d : ℝ) * (lw ^ 3 * ℓ) + 1) ^ (d + 2) * (1 + Lg) +
      2 * c₁ ^ 2 * (Lr ^ d) ^ 2) ≤
      Nn ^ 2 * ((c₀ + 2) * (Nn ^ (5 * d + 12))⁻¹) * (CB * Nn ^ (4 * d + 9)) := by
    have hB0 : 0 ≤ Cd * c₁ * c₂ * ((d : ℝ) * (lw ^ 3 * ℓ) + 1) ^ (d + 2) * (1 + Lg) +
        2 * c₁ ^ 2 * (Lr ^ d) ^ 2 := by positivity
    calc _ ≤ Nn ^ 2 * ε₂ * (Cd * c₁ * c₂ * ((d : ℝ) * (lw ^ 3 * ℓ) + 1) ^ (d + 2) * (1 + Lg) +
          2 * c₁ ^ 2 * (Lr ^ d) ^ 2) := by gcongr
      _ ≤ Nn ^ 2 * ((c₀ + 2) * (Nn ^ (5 * d + 12))⁻¹) * (CB * Nn ^ (4 * d + 9)) := by gcongr
  refine hmain.trans ?_
  -- compare with `(Λ⁴ 2^{d-2} N^d)⁻¹`
  have hap : 0 < Λ ^ 4 * 2 ^ (d - 2) * Nn ^ d := by positivity
  have hba : Nn ^ 2 * ((c₀ + 2) * (Nn ^ (5 * d + 12))⁻¹) * (CB * Nn ^ (4 * d + 9)) *
      (Λ ^ 4 * 2 ^ (d - 2) * Nn ^ d) = CB * (c₀ + 2) * Λ ^ 4 * 2 ^ (d - 2) / Nn := by
    have e1 : Nn ^ (5 * d + 12) = Nn ^ (5 * d + 11) * Nn := pow_succ _ _
    have e2 : Nn ^ 2 * Nn ^ (4 * d + 9) * Nn ^ d = Nn ^ (5 * d + 11) := by
      rw [← pow_add, ← pow_add]; congr 1; omega
    have e3 : Nn ^ 2 * ((c₀ + 2) * (Nn ^ (5 * d + 12))⁻¹) * (CB * Nn ^ (4 * d + 9)) *
        (Λ ^ 4 * 2 ^ (d - 2) * Nn ^ d) =
        (CB * (c₀ + 2) * Λ ^ 4 * 2 ^ (d - 2)) * ((Nn ^ 2 * Nn ^ (4 * d + 9) * Nn ^ d) * (Nn ^ (5 * d + 12))⁻¹) := by
      ring
    rw [e3, e2, e1]
    field_simp
  have hle1 : Nn ^ 2 * ((c₀ + 2) * (Nn ^ (5 * d + 12))⁻¹) * (CB * Nn ^ (4 * d + 9)) *
      (Λ ^ 4 * 2 ^ (d - 2) * Nn ^ d) ≤ 1 := by
    rw [hba, div_le_one hNn0]
    exact hbig
  calc Nn ^ 2 * ((c₀ + 2) * (Nn ^ (5 * d + 12))⁻¹) * (CB * Nn ^ (4 * d + 9))
      = Nn ^ 2 * ((c₀ + 2) * (Nn ^ (5 * d + 12))⁻¹) * (CB * Nn ^ (4 * d + 9)) *
          (Λ ^ 4 * 2 ^ (d - 2) * Nn ^ d) * (Λ ^ 4 * 2 ^ (d - 2) * Nn ^ d)⁻¹ := by
        field_simp
    _ ≤ 1 * (Λ ^ 4 * 2 ^ (d - 2) * Nn ^ d)⁻¹ := by gcongr
    _ = (Λ ^ 4 * 2 ^ (d - 2) * Nn ^ d)⁻¹ := one_mul _

/-- `η_s⁻² + c₁ ≤ N⁷`: `η_s = (1-s) Im m ≥ (g²/L²) κ'`, `g⁻² ≤ N`, `L ≤ N`. -/
private theorem meanFar_eta_bound {Nn g L κ' η c₁ : ℝ} (hN1 : 1 ≤ Nn) (hg : 0 < g)
    (hg2N : 1 ≤ g ^ 2 * Nn) (hL3 : 3 ≤ L) (hLN : L ≤ Nn) (hκ' : 0 < κ')
    (hη : g ^ 2 / L ^ 2 * κ' ≤ η) (hc₁ : 0 ≤ c₁) (hM : 1 / κ' ^ 2 + c₁ ≤ Nn) :
    η⁻¹ ^ 2 + c₁ ≤ Nn ^ 7 := by
  have hNn0 : 0 < Nn := by linarith
  have hL0 : 0 < L := by linarith
  have h2 : 0 < g ^ 2 / L ^ 2 * κ' := by positivity
  have hη0 : 0 < η := lt_of_lt_of_le h2 hη
  have hηinv : η⁻¹ ≤ Nn ^ 3 / κ' := by
    refine (inv_anti₀ h2 hη).trans ?_
    have e : (g ^ 2 / L ^ 2 * κ')⁻¹ = (L ^ 2 * (g ^ 2)⁻¹) / κ' := by
      field_simp
    rw [e]
    have hgN : (g ^ 2)⁻¹ ≤ Nn := (inv_le_iff_one_le_mul₀' (by positivity)).2 hg2N
    have : L ^ 2 * (g ^ 2)⁻¹ ≤ Nn ^ 2 * Nn :=
      mul_le_mul (pow_le_pow_left₀ hL0.le hLN 2) hgN (by positivity) (by positivity)
    calc _ ≤ Nn ^ 2 * Nn / κ' := div_le_div_of_nonneg_right this hκ'.le
      _ = Nn ^ 3 / κ' := by ring
  have h1 : η⁻¹ ^ 2 ≤ (Nn ^ 3 / κ') ^ 2 := pow_le_pow_left₀ (by positivity) hηinv 2
  have e : (Nn ^ 3 / κ') ^ 2 = Nn ^ 6 * (1 / κ' ^ 2) := by field_simp
  have h6 : 1 ≤ Nn ^ 6 := one_le_pow₀ hN1
  have h2' : Nn ^ 6 * (1 / κ' ^ 2) + c₁ ≤ Nn ^ 6 * (1 / κ' ^ 2 + c₁) := by
    have : 0 ≤ 1 / κ' ^ 2 := by positivity
    nlinarith
  calc η⁻¹ ^ 2 + c₁ ≤ Nn ^ 6 * (1 / κ' ^ 2) + c₁ := by rw [e] at h1; linarith
    _ ≤ Nn ^ 6 * (1 / κ' ^ 2 + c₁) := h2'
    _ ≤ Nn ^ 6 * Nn := mul_le_mul_of_nonneg_left hM (by positivity)
    _ = Nn ^ 7 := by ring

/-- `ε₂ ≤ (c₀ + 2) N^{-(5d+12)}`. -/
private theorem meanFar_eps_bound (d : ℕ) {Nn τ Wd ex c₀ A' η2 : ℝ} (hN1 : 1 ≤ Nn) (hτ : τ ≤ 1)
    (hc₀ : 0 ≤ c₀) (hA'0 : 0 ≤ A') (hA'1 : A' ≤ 1) (hex0 : 0 ≤ ex)
    (hexp : ex ≤ (Nn ^ (5 * d + 13))⁻¹) (hWd0 : 0 ≤ Wd) (hWdw : Wd ≤ (Nn ^ (5 * d + 13))⁻¹)
    (hη7 : η2 ≤ Nn ^ 7) :
    Nn ^ (τ / 4) * (c₀ * A' * ex) + (Nn ^ (τ / 4) * Wd + η2 * (Nn ^ (5 * d + 19))⁻¹) ≤
      (c₀ + 2) * (Nn ^ (5 * d + 12))⁻¹ := by
  have hNn0 : 0 < Nn := by linarith
  have hτ4 : Nn ^ (τ / 4) ≤ Nn := by
    calc Nn ^ (τ / 4) ≤ Nn ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
      _ = Nn := Real.rpow_one _
  have hNτ0 : 0 ≤ Nn ^ (τ / 4) := Real.rpow_nonneg hNn0.le _
  have e13 : Nn * (Nn ^ (5 * d + 13))⁻¹ = (Nn ^ (5 * d + 12))⁻¹ := by
    rw [pow_succ]; field_simp
  have e19 : Nn ^ 7 * (Nn ^ (5 * d + 19))⁻¹ = (Nn ^ (5 * d + 12))⁻¹ := by
    have : Nn ^ (5 * d + 19) = Nn ^ 7 * Nn ^ (5 * d + 12) := by rw [← pow_add]; congr 1; omega
    rw [this]; field_simp
  have t1 : Nn ^ (τ / 4) * (c₀ * A' * ex) ≤ c₀ * (Nn ^ (5 * d + 12))⁻¹ := by
    calc _ ≤ Nn * (c₀ * 1 * (Nn ^ (5 * d + 13))⁻¹) := by
          refine mul_le_mul hτ4 ?_ (by positivity) hNn0.le
          exact mul_le_mul (mul_le_mul_of_nonneg_left hA'1 hc₀) hexp hex0 (by positivity)
      _ = c₀ * (Nn * (Nn ^ (5 * d + 13))⁻¹) := by ring
      _ = _ := by rw [e13]
  have t2 : Nn ^ (τ / 4) * Wd ≤ (Nn ^ (5 * d + 12))⁻¹ := by
    calc _ ≤ Nn * (Nn ^ (5 * d + 13))⁻¹ := mul_le_mul hτ4 hWdw hWd0 hNn0.le
      _ = _ := e13
  have t3 : η2 * (Nn ^ (5 * d + 19))⁻¹ ≤ (Nn ^ (5 * d + 12))⁻¹ := by
    calc _ ≤ Nn ^ 7 * (Nn ^ (5 * d + 19))⁻¹ := mul_le_mul_of_nonneg_right hη7 (by positivity)
      _ = _ := e19
  linarith

/-- **`‖𝔼 f^{far}‖` at one index `n`**: every numeric fact about the size sequence is a hypothesis
(`hA1`, `h2d`, `hexp`, `hWdw`, `hP`, the pure facts about `N`), the propagator pins are given through
their instances `h5n`, `h7n` at `Θ_{u m₁m₂}(0, ·)`. -/
private theorem meanFar_at_n {d : ℕ} (sz : Sizes d) (n : ℕ) (hd : 3 ≤ d)
    {E s t τ κ' Λ C₅ c₅ C₇ Dw : ℝ}
    (hE : |E| < 2) (hκ'0 : 0 < κ') (hκ' : κ' ≤ (mE E).im)
    (hs0 : 0 ≤ s) (hst : s < t) (ht : t < 1)
    (hΛ : 0 < Λ) (hg : 0 < sz.lam n) (hgΛ : sz.lam n ≤ Λ)
    (hreg1 : sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 ≤ 1 - t) (hreg2 : 1 - s ≤ sz.lam n ^ 2)
    (hC₅ : 0 < C₅) (hC₇ : 0 < C₇)
    (h5n : ∀ u : ℝ, 0 ≤ u → u < 1 → ∀ (σ : Fin 2 → Bool) (x : Zd d (sz.L n)),
      ‖Theta d (sz.L n) (sz.lam n) ((u : ℂ) * (STmsig E (σ 0) * STmsig E (σ 1))) 0 x‖ ≤
        C₅ * Bparam d (sz.L n) (sz.lam n) u (zdistD d (sz.L n) x) *
          Real.exp (-c₅ * ((zdistD d (sz.L n) x : ℕ) : ℝ) / ellT (sz.L n) (sz.lam n) u))
    (hc₅ : 0 < c₅)
    (h7n : ∀ (σ : Fin 2 → Bool) (a r : Zd d (sz.L n)),
      ((zdistD d (sz.L n) r : ℕ) : ℝ) ≤ 1 / 2 * ((zdistD d (sz.L n) a : ℕ) : ℝ) →
      ‖Theta d (sz.L n) (sz.lam n) ((t : ℂ) * (STmsig E (σ 0) * STmsig E (σ 1))) 0 (a + r) +
          Theta d (sz.L n) (sz.lam n) ((t : ℂ) * (STmsig E (σ 0) * STmsig E (σ 1))) 0 (a - r) -
          2 * Theta d (sz.L n) (sz.lam n) ((t : ℂ) * (STmsig E (σ 0) * STmsig E (σ 1))) 0 a‖ ≤
        C₇ * (sz.lam n ^ 2 + |1 - t|)⁻¹ * ((zdistD d (sz.L n) r : ℕ) : ℝ) ^ 2 *
          ((((zdistD d (sz.L n) a : ℕ) : ℝ) + 1) ^ d)⁻¹)
    (hτ1 : τ ≤ 1)
    (hA1 : 1 ≤ STAI sz n)
    (h2d : 2 * (d : ℝ) ≤ Real.log ((sz.W n : ℕ) : ℝ))
    (hexp : Real.exp (-(Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ))) ≤
      (((sz.size n : ℕ) : ℝ) ^ (5 * d + 13))⁻¹)
    (hWdw : ((sz.W n : ℕ) : ℝ) ^ (-Dw) ≤ (((sz.size n : ℕ) : ℝ) ^ (5 * d + 13))⁻¹)
    (hP : ∀ (σ : Fin 2 → Bool) (a b : Zd d (sz.L n)),
      sz.seqP {ω | ((sz.size n : ℕ) : ℝ) ^ (τ / 4) *
          (sz.Bctl n s ^ (1 / 5 : ℝ) * STWB sz n s (zdistInf d (sz.L n) (a - b)) *
            Real.exp (-(((zdistInf d (sz.L n) (a - b) : ℕ) : ℝ) / ellT (sz.L n) (sz.lam n) s) ^ (1 / 2 : ℝ)) +
            ((sz.W n : ℕ) : ℝ) ^ (-Dw)) <
          ‖STLKM sz n E s (sz.seqHflow n s ω) σ ![a, b]‖} ≤
        ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-((5 * d + 19 : ℕ) : ℝ))))
    (hN1 : 1 ≤ ((sz.size n : ℕ) : ℝ))
    (hN2 : 2 ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2))
    (hlogN : 1 ≤ Real.log ((sz.size n : ℕ) : ℝ))
    (hpolyN : meanFar_Cd d * (C₅ * meanFar_c3 d) * C₇ * meanFar_c0 d * (16 * (d : ℝ) ^ 4) * 3 *
      Real.log ((sz.size n : ℕ) : ℝ) ^ 13 ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 4))
    (hM4 : 1 / κ' ^ 2 + C₅ * meanFar_c3 d ≤ ((sz.size n : ℕ) : ℝ))
    (hM5 : (3 * meanFar_Cd d * (C₅ * meanFar_c3 d) * C₇ * ((d : ℝ) + 1) ^ (d + 2) +
        2 * (C₅ * meanFar_c3 d) ^ 2) * (meanFar_c0 d + 2) * Λ ^ 4 * 2 ^ (d - 2) ≤ ((sz.size n : ℕ) : ℝ))
    (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) :
    ‖∫ ω, STfFar sz n E s t σ a ω ∂(sz.seqP)‖ ≤ ((sz.size n : ℕ) : ℝ) ^ τ *
      (STAI sz n ^ (-(6 / 5 : ℝ)) / (((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) ^ (d - 2) + 1)) := by
  have hL := sz.three_le_L n
  have hs1 : s < 1 := hst.trans ht
  have ht0 : 0 ≤ t := hs0.trans hst.le
  have hregs : sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 ≤ 1 - s := hreg1.trans (by linarith)
  have hmsig : ∀ b : Bool, STmsig E b = mSigma E b := fun _ => rfl
  -- basic real quantities
  have hW1 : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hL3 : (3 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) := by exact_mod_cast hL
  have hWN : ((sz.W n : ℕ) : ℝ) ^ d ≤ ((sz.size n : ℕ) : ℝ) := by
    have h : (sz.W n) ^ d ≤ sz.size n :=
      Nat.pow_le_pow_left (Nat.le_mul_of_pos_right _ (by omega : 0 < sz.L n)) d
    exact_mod_cast h
  have hLN : ((sz.L n : ℕ) : ℝ) ^ d ≤ ((sz.size n : ℕ) : ℝ) := by
    have h : (sz.L n) ^ d ≤ sz.size n :=
      Nat.pow_le_pow_left (Nat.le_mul_of_pos_left _ (sz.W_pos n)) d
    exact_mod_cast h
  have hLNn : ((sz.L n : ℕ) : ℝ) ≤ ((sz.size n : ℕ) : ℝ) :=
    (le_self_pow₀ (by linarith) (by omega : d ≠ 0)).trans hLN
  have hWNn : ((sz.W n : ℕ) : ℝ) ≤ ((sz.size n : ℕ) : ℝ) :=
    (le_self_pow₀ hW1 (by omega : d ≠ 0)).trans hWN
  have hA0 : 0 < STAI sz n := lt_of_lt_of_le one_pos hA1
  have hAe : STAI sz n = sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d := rfl
  have hg2N : 1 ≤ sz.lam n ^ 2 * ((sz.size n : ℕ) : ℝ) := by
    calc (1 : ℝ) ≤ STAI sz n := hA1
      _ = sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d := hAe
      _ ≤ sz.lam n ^ 2 * ((sz.size n : ℕ) : ℝ) := mul_le_mul_of_nonneg_left hWN (by positivity)
  have hAΛ : STAI sz n ≤ Λ ^ 2 * ((sz.size n : ℕ) : ℝ) := by
    rw [hAe]
    exact mul_le_mul (pow_le_pow_left₀ hg.le hgΛ 2) hWN (by positivity) (by positivity)
  have hℓ1 : 1 ≤ ellT (sz.L n) (sz.lam n) s := one_le_ellT (by linarith)
  have hℓL : ellT (sz.L n) (sz.lam n) s ≤ ((sz.L n : ℕ) : ℝ) := ellT_le_L
  have hlw3 : (6 : ℝ) ≤ Real.log ((sz.W n : ℕ) : ℝ) := by
    have : (3 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hlwN : Real.log ((sz.W n : ℕ) : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by
    have := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < ((sz.W n : ℕ) : ℝ))
    linarith
  have hlwlogN : Real.log ((sz.W n : ℕ) : ℝ) ≤ Real.log ((sz.size n : ℕ) : ℝ) :=
    Real.log_le_log (by linarith) hWNn
  -- the constants
  set c₃ : ℝ := meanFar_c3 d with hc₃
  set c₁ : ℝ := C₅ * c₃ with hc₁
  have hc₃0 : 0 < c₃ := meanFar_c3_pos d
  have hc₁0 : 0 < c₁ := by positivity
  have hc₀0 : 0 ≤ meanFar_c0 d := by unfold meanFar_c0; have := meanFar_c3_pos d; positivity
  -- propagator bounds at the time `u`
  have hT1u : ∀ u : ℝ, 0 ≤ u → u < 1 → sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 ≤ 1 - u →
      ∀ (σ' : Fin 2 → Bool) (x : Zd d (sz.L n)),
      ‖Theta d (sz.L n) (sz.lam n) ((u : ℂ) * (STmsig E (σ' 0) * STmsig E (σ' 1))) 0 x‖ ≤
        (c₁ / sz.lam n ^ 2) / (((zdistInf d (sz.L n) x : ℕ) : ℝ) + 1) ^ (d - 2) := by
    intro u hu0 hu1 hru σ' x
    exact meanFar_T1 hd hL hg hu1 hru hC₅.le hc₅
      (fun x => Theta d (sz.L n) (sz.lam n) ((u : ℂ) * (STmsig E (σ' 0) * STmsig E (σ' 1))) 0 x)
      (h5n u hu0 hu1 σ') x
  -- the bound of `𝒦` and the kernel
  have hKbound : ∀ (σ' : Fin 2 → Bool) (a' b' : Zd d (sz.L n)), ‖STKloop sz n E s σ' ![a', b']‖ ≤ c₁ := by
    intro σ' a' b'
    have hTs : ∀ x : Zd d (sz.L n),
        ‖Theta d (sz.L n) (sz.lam n) ((s : ℂ) * (mSigma E (σ' 0) * mSigma E (σ' 1))) 0 x‖ ≤ c₁ / sz.lam n ^ 2 :=
      fun x => meanFar_T_le
        (fun x => Theta d (sz.L n) (sz.lam n) ((s : ℂ) * (mSigma E (σ' 0) * mSigma E (σ' 1))) 0 x)
        (fun x => hT1u s hs0 hs1 hregs σ' x) x
    refine (meanFar_n_K sz n hE hs0 hs1 σ' a' b' hTs).trans ?_
    have hWd : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) ^ d := by positivity
    have : (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (c₁ / sz.lam n ^ 2) = c₁ / STAI sz n := by
      rw [hAe]; field_simp
    rw [this]
    exact div_le_self hc₁0.le hA1
  have hker := meanFar_n_kernel sz n hd hE hs1 hg hregs (τ₁ := τ / 4) (D₁ := ((5 * d + 19 : ℕ) : ℝ))
    (Dw := Dw) (Kmax := c₁) hP hKbound σ
  -- the propagator at the time `t`, the window and the far threshold
  have hT1 : ∀ x : Zd d (sz.L n),
      ‖Theta d (sz.L n) (sz.lam n) ((t : ℂ) * (STmsig E (σ 0) * STmsig E (σ 1))) 0 x‖ ≤
        (c₁ / sz.lam n ^ 2) / (((zdistInf d (sz.L n) x : ℕ) : ℝ) + 1) ^ (d - 2) :=
    fun x => hT1u t ht0 ht hreg1 σ x
  set lw : ℝ := Real.log ((sz.W n : ℕ) : ℝ) with hlw
  set ℓ : ℝ := ellT (sz.L n) (sz.lam n) s with hℓ
  set Nn : ℝ := ((sz.size n : ℕ) : ℝ) with hNn
  have hlw0 : 0 ≤ lw := by linarith
  have hℓ0 : 0 < ℓ := by linarith
  have hρ0 : 0 ≤ lw ^ 4 * ℓ := by positivity
  have hwρ : 2 * ((d : ℝ) * (lw ^ 3 * ℓ)) ≤ ((⌊lw ^ 4 * ℓ⌋₊ : ℕ) : ℝ) + 1 := by
    have h1 : 2 * ((d : ℝ) * (lw ^ 3 * ℓ)) ≤ lw ^ 4 * ℓ := by
      calc 2 * ((d : ℝ) * (lw ^ 3 * ℓ)) = (2 * d) * (lw ^ 3 * ℓ) := by ring
        _ ≤ lw * (lw ^ 3 * ℓ) := mul_le_mul_of_nonneg_right h2d (by positivity)
        _ = lw ^ 4 * ℓ := by ring
    have h2 := Nat.lt_floor_add_one (lw ^ 4 * ℓ)
    linarith
  have hT2 : ∀ a' r : Zd d (sz.L n), ((zdistD d (sz.L n) r : ℕ) : ℝ) ≤ (d : ℝ) * (lw ^ 3 * ℓ) →
      lw ^ 4 * ℓ < ((zdistInf d (sz.L n) a' : ℕ) : ℝ) →
      ‖Theta d (sz.L n) (sz.lam n) ((t : ℂ) * (STmsig E (σ 0) * STmsig E (σ 1))) 0 (a' + r) +
          Theta d (sz.L n) (sz.lam n) ((t : ℂ) * (STmsig E (σ 0) * STmsig E (σ 1))) 0 (a' - r) -
          2 * Theta d (sz.L n) (sz.lam n) ((t : ℂ) * (STmsig E (σ 0) * STmsig E (σ 1))) 0 a'‖ ≤
        (C₇ / sz.lam n ^ 2) * ((zdistD d (sz.L n) r : ℕ) : ℝ) ^ 2 /
          (((zdistInf d (sz.L n) a' : ℕ) : ℝ) + 1) ^ d :=
    fun a' r hr ha => meanFar_T2 hg hC₇.le hρ0 hwρ
      (fun x => Theta d (sz.L n) (sz.lam n) ((t : ℂ) * (STmsig E (σ 0) * STmsig E (σ 1))) 0 x)
      (fun a r h => h7n σ a r h) a' r hr ha
  -- the small quantities
  have hNn0 : 0 < Nn := by linarith
  set A' : ℝ := STAI sz n ^ (-(6 / 5 : ℝ)) with hA'
  have hA'0 : 0 ≤ A' := Real.rpow_nonneg hA0.le _
  have hA'1 : A' ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hA1 (by norm_num)
  set ε₁ : ℝ := Nn ^ (τ / 4) * ((sz.W n : ℕ) : ℝ) ^ (-Dw) +
      ((etaT E s)⁻¹ ^ 2 + c₁) * Nn ^ (-((5 * d + 19 : ℕ) : ℝ)) with hε₁
  set ε₂ : ℝ := Nn ^ (τ / 4) * (meanFar_c0 d * A' * Real.exp (-(lw ^ (3 / 2 : ℝ)))) + ε₁ with hε₂
  have hNτ0 : 0 ≤ Nn ^ (τ / 4) := Real.rpow_nonneg hNn0.le _
  have hε₁0 : 0 ≤ ε₁ := by positivity
  have hε₂0 : 0 ≤ ε₂ := by positivity
  have hε12 : ε₁ ≤ ε₂ := by
    have : 0 ≤ Nn ^ (τ / 4) * (meanFar_c0 d * A' * Real.exp (-(lw ^ (3 / 2 : ℝ)))) := by positivity
    linarith
  have hη7 : (etaT E s)⁻¹ ^ 2 + c₁ ≤ Nn ^ 7 := by
    have h1 : sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 * κ' ≤ etaT E s := by
      have : etaT E s = (1 - s) * (mE E).im := rfl
      rw [this]
      exact mul_le_mul hregs hκ' hκ'0.le (by linarith)
    exact meanFar_eta_bound hN1 hg hg2N hL3 hLNn hκ'0 h1 hc₁0.le hM4
  have hD1 : Nn ^ (-((5 * d + 19 : ℕ) : ℝ)) = (Nn ^ (5 * d + 19))⁻¹ := by
    rw [Real.rpow_neg hNn0.le, Real.rpow_natCast]
  have hε₂bd : ε₂ ≤ (meanFar_c0 d + 2) * (Nn ^ (5 * d + 12))⁻¹ := by
    rw [hε₂, hε₁, hD1]
    exact meanFar_eps_bound d hN1 hτ1 hc₀0 hA'0 hA'1 (Real.exp_pos _).le hexp
      (Real.rpow_nonneg (by linarith) _) hWdw hη7
  -- logarithmic and polynomial facts
  have hLr0 : 0 ≤ ((sz.L n : ℕ) : ℝ) := by linarith
  have hLg0 : 0 ≤ Real.log (((sz.L n : ℕ) : ℝ) + 1) := Real.log_nonneg (by linarith)
  have hLg1 : Real.log (((sz.L n : ℕ) : ℝ) + 1) ≤ 1 + Real.log Nn := by
    have h1 : ((sz.L n : ℕ) : ℝ) + 1 ≤ 2 * Nn := by linarith
    calc Real.log (((sz.L n : ℕ) : ℝ) + 1) ≤ Real.log (2 * Nn) := Real.log_le_log (by linarith) h1
      _ = Real.log 2 + Real.log Nn := Real.log_mul (by norm_num) hNn0.ne'
      _ ≤ 1 + Real.log Nn := by have := Real.log_two_lt_d9; linarith
  have hlogNN : Real.log Nn ≤ Nn := by
    have := Real.log_le_sub_one_of_pos hNn0
    linarith
  have hLg' : 1 + Real.log (((sz.L n : ℕ) : ℝ) + 1) ≤ 3 * Nn := by linarith
  have hpoly : meanFar_Cd d * c₁ * C₇ * meanFar_c0 d * (16 * (d : ℝ) ^ 4) *
      (lw ^ 12 * (1 + Real.log (((sz.L n : ℕ) : ℝ) + 1))) ≤ Nn ^ (τ / 4) := by
    have h1 : lw ^ 12 * (1 + Real.log (((sz.L n : ℕ) : ℝ) + 1)) ≤ 3 * Real.log Nn ^ 13 := by
      have : lw ^ 12 ≤ Real.log Nn ^ 12 := pow_le_pow_left₀ hlw0 hlwlogN 12
      calc _ ≤ Real.log Nn ^ 12 * (3 * Real.log Nn) :=
            mul_le_mul this (by linarith) (by linarith) (by positivity)
        _ = 3 * Real.log Nn ^ 13 := by ring
    have hCd0 := meanFar_Cd_nonneg d
    calc _ ≤ (meanFar_Cd d * c₁ * C₇ * meanFar_c0 d * (16 * (d : ℝ) ^ 4)) * (3 * Real.log Nn ^ 13) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = meanFar_Cd d * c₁ * C₇ * meanFar_c0 d * (16 * (d : ℝ) ^ 4) * 3 * Real.log Nn ^ 13 := by ring
      _ ≤ _ := hpolyN
  have hDn0 : (0 : ℝ) ≤ ((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) := Nat.cast_nonneg _
  have hDnN : ((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) ≤ Nn := by
    have : ((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) ≤ ((sz.L n : ℕ) : ℝ) := by
      exact_mod_cast meanFar_zdistInf_le _
    linarith
  have hlw1 : 1 ≤ lw := by linarith
  have htiny := meanFar_tiny d hd (Nn := Nn) (g := sz.lam n) (ℓ := ℓ) (lw := lw) (A := STAI sz n)
    (Dn := ((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ)) (Lr := ((sz.L n : ℕ) : ℝ))
    (Lg := Real.log (((sz.L n : ℕ) : ℝ) + 1)) (Λ := Λ) (c₀ := meanFar_c0 d) (c₁ := c₁) (c₂ := C₇)
    (ε₂ := ε₂) hN1 hg2N hA1 hAΛ hΛ hℓ1 hℓL hLNn hLN hlw1 hlwN hDn0 hDnN hLg0 hLg' hc₀0 hc₁0.le hC₇.le
    hε₂0 hε₂bd hM5
  have hass := meanFar_assemble sz n hd hE hs0 hst ht σ a (lw ^ 3 * ℓ) (c₁ / sz.lam n ^ 2)
    (C₇ / sz.lam n ^ 2) (Nn ^ (τ / 4) * (meanFar_c0 d * A')) ε₁ ε₂ (by positivity) (by positivity)
    hε₁0 hε₂0 hT1 hT2 hker.1 hker.2
  refine hass.trans ?_
  have hreg' : (1 - s) ^ 2 * ℓ ^ 4 ≤ sz.lam n ^ 4 := by
    have h := meanFar_ell_sq (L := sz.L n) hg hs1 hreg2
    have h0 : 0 ≤ (1 - s) * ℓ ^ 2 := by
      have : 0 < 1 - s := by linarith
      positivity
    calc (1 - s) ^ 2 * ℓ ^ 4 = ((1 - s) * ℓ ^ 2) ^ 2 := by ring
      _ ≤ (sz.lam n ^ 2) ^ 2 := pow_le_pow_left₀ h0 h 2
      _ = sz.lam n ^ 4 := by ring
  have hmain := meanFar_numeric_main d hd (τ := τ) (Nn := Nn) (g := sz.lam n) (ℓ := ℓ) (lw := lw)
    (s := s) (Dn := ((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ)) (A := STAI sz n)
    (Lr := ((sz.L n : ℕ) : ℝ)) (Lg := Real.log (((sz.L n : ℕ) : ℝ) + 1)) (c₀ := meanFar_c0 d)
    (c₁ := c₁) (c₂ := C₇) (ε₁ := ε₁) (ε₂ := ε₂) hN2 hN1 hg hℓ1 hlw1 hs0 hs1.le hDn0 hA0 hLg0
    hc₀0 hc₁0.le hC₇.le hε₁0 hε12 hreg' hpoly htiny
  refine hmain.trans ?_
  have hpa : ((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) ^ (d - 2) + 1 ≤
      (((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) + 1) ^ (d - 2) := by
    have := pow_add_pow_le hDn0 (zero_le_one' ℝ) (n := d - 2) (by omega)
    simpa using this
  have hposD : 0 < ((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) ^ (d - 2) + 1 := by positivity
  have hNτ : 0 ≤ Nn ^ τ := Real.rpow_nonneg hNn0.le _
  refine mul_le_mul_of_nonneg_left ?_ hNτ
  exact div_le_div_of_nonneg_left hA'0 hposD hpa

/-! ## 7. The eventual facts about the scale `N` -/

section PureN

/-- `C (log x)^k ≤ x^ε` eventually (`ε > 0`). -/
private theorem meanFar_polylog (C ε : ℝ) (hε : 0 < ε) (k : ℕ) :
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

/-- The pure facts about `N` used at one index. -/
private theorem meanFar_pureN {τ 𝔠 : ℝ} (hτ : 0 < τ) (h𝔠 : 0 < 𝔠) (Cp M₄ M₅ M₆ : ℝ) :
    ∀ᶠ x : ℝ in atTop, 1 ≤ x ∧ 2 ≤ x ^ (τ / 2) ∧ 1 ≤ Real.log x ∧
      Cp * 3 * Real.log x ^ 13 ≤ x ^ (τ / 4) ∧ M₄ ≤ x ∧ M₅ ≤ x ∧ M₆ ≤ 𝔠 * Real.log x := by
  have h2 : ∀ᶠ x : ℝ in atTop, 2 ≤ x ^ (τ / 2) :=
    (tendsto_rpow_atTop (by positivity)).eventually_ge_atTop 2
  have h3 : ∀ᶠ x : ℝ in atTop, 1 ≤ Real.log x := Real.tendsto_log_atTop.eventually_ge_atTop 1
  have h4 := meanFar_polylog (Cp * 3) (τ / 4) (by positivity) 13
  have h6 : ∀ᶠ x : ℝ in atTop, M₆ ≤ 𝔠 * Real.log x :=
    (Filter.Tendsto.const_mul_atTop h𝔠 Real.tendsto_log_atTop).eventually_ge_atTop M₆
  filter_upwards [eventually_ge_atTop (1 : ℝ), h2, h3, h4, eventually_ge_atTop M₄,
    eventually_ge_atTop M₅, h6] with x a b c d e f g
  exact ⟨a, b, c, d, e, f, g⟩

end PureN


/-! ## 8. The eventual statement and the pin `stMeanFar` -/

section Eventually

/-- `(N^k)⁻¹ = exp(-(k log N))`. -/
private theorem meanFar_inv_pow_eq {N : ℝ} (hN : 0 < N) (k : ℕ) :
    (N ^ k)⁻¹ = Real.exp (-((k : ℝ) * Real.log N)) := by
  rw [Real.exp_neg, Real.exp_nat_mul, Real.exp_log hN]

/-- `B · lw ≤ lw^{3/2}` when `B² ≤ lw`. -/
private theorem meanFar_three_halves {lw B : ℝ} (hB : 0 < B) (hlw : B ^ 2 ≤ lw) :
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

/-- **The mean part of `f^{far}`, eventually in `n`** (`(eq:boundEfar)`, `3_5:2192-2212`): for every
`τ > 0`, eventually in `n`, for every sign pattern `σ` and `a`,
`|𝔼 f^{far}_{σ,a}| ≤ N^τ (ilambda² W^d)^{-6/5} / (|a₁-a₂|^{d-2} + 1)`. -/
theorem meanFar_eventually {d : ℕ} (hd : 3 ≤ d) (sz : Sizes d) {κ 𝔠 𝔡 Cd : ℝ} (hκ : 0 < κ)
    (h𝔠 : 0 < 𝔠) (h𝔡 : 0 < 𝔡) (hSz : sz.SizeTendsto) (hBw : sz.Bandwidth 𝔠) (hWO : sz.WO 𝔡)
    (E s t : ℕ → ℝ) (hE : ∀ n, |E n| ≤ 2 - κ) (hs0 : ∀ n, 0 ≤ s n) (hst : ∀ n, s n < t n)
    (ht : ∀ n, t n < 1) (hreg : STReg5I sz s t) (hG : STGdecayW sz E s t Cd) (τ : ℝ) (hτ : 0 < τ) :
    ∀ᶠ n in atTop, ∀ (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)),
      ‖∫ ω, STfFar sz n (E n) (s n) (t n) σ a ω ∂(sz.seqP)‖ ≤ ((sz.size n : ℕ) : ℝ) ^ τ *
        (STAI sz n ^ (-(6 / 5 : ℝ)) / (((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) ^ (d - 2) + 1)) := by
  -- reduce to `τ ≤ 1`
  obtain ⟨τ', hτ'0, hτ'1, hτ'⟩ : ∃ τ' : ℝ, 0 < τ' ∧ τ' ≤ 1 ∧ τ' ≤ τ :=
    ⟨min τ 1, lt_min hτ one_pos, min_le_right _ _, min_le_left _ _⟩
  set Λ : ℝ := 𝔡⁻¹ with hΛdef
  have hΛ : 0 < Λ := inv_pos.2 h𝔡
  set κ' : ℝ := min κ (1 / 2) with hκ'def
  have hκ'0 : 0 < κ' := lt_min hκ (by norm_num)
  obtain ⟨C₅, hC₅, c₅, hc₅, H5⟩ := prop5Decay_holds d Λ hd hΛ
  obtain ⟨C₇, hC₇, H7⟩ := prop7Diff2_holds d Λ κ' (1 / 2) hd hΛ hκ'0 (by norm_num) (by norm_num)
  set Dw : ℝ := ((5 * d + 13 : ℕ) : ℝ) / 𝔠 with hDw
  have hDw0 : 0 < Dw := by positivity
  have hs1 : ∀ n, s n < 1 := fun n => (hst n).trans (ht n)
  have hbad := meanFar_bad_le sz hs1 (fun n => (hst n).le) hG hDw0 (τ := τ' / 4)
    (D₁ := ((5 * d + 19 : ℕ) : ℝ)) (by positivity) (by positivity)
  have hpure := meanFar_pureN (τ := τ') (𝔠 := 𝔠) hτ'0 h𝔠
    (meanFar_Cd d * (C₅ * meanFar_c3 d) * C₇ * meanFar_c0 d * (16 * (d : ℝ) ^ 4))
    (1 / κ' ^ 2 + C₅ * meanFar_c3 d)
    ((3 * meanFar_Cd d * (C₅ * meanFar_c3 d) * C₇ * ((d : ℝ) + 1) ^ (d + 2) +
        2 * (C₅ * meanFar_c3 d) ^ 2) * (meanFar_c0 d + 2) * Λ ^ 4 * 2 ^ (d - 2))
    (max (2 * (d : ℝ)) ((((5 * d + 13 : ℕ) : ℝ) / 𝔠) ^ 2))
  have hpure' := hSz.eventually hpure
  filter_upwards [hWO, hBw, hbad, hpure'] with n hWOn hBwn hbadn hpn
  obtain ⟨hN1, hN2, hlogN, hpolyN, hM4, hM5, hM6⟩ := hpn
  have hL := sz.three_le_L n
  have hW1 : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := lt_of_lt_of_le one_pos hN1
  obtain ⟨hWO1, hWO2⟩ := hWOn
  have hg : 0 < sz.lam n :=
    lt_of_lt_of_le (Real.rpow_pos_of_pos (by linarith) _) hWO1
  have hA1 : 1 ≤ STAI sz n :=
    le_trans (Real.one_le_rpow hW1 (by positivity)) (sz.lam_sq_mul_pow_ge n hWO1)
  -- the logarithmic lower bound `log W ≥ 𝔠 log N`
  have hlw𝔠 : 𝔠 * Real.log ((sz.size n : ℕ) : ℝ) ≤ Real.log ((sz.W n : ℕ) : ℝ) := by
    have := Real.log_le_log (Real.rpow_pos_of_pos hN0 𝔠) hBwn
    rwa [Real.log_rpow hN0] at this
  have hM6' : max (2 * (d : ℝ)) ((((5 * d + 13 : ℕ) : ℝ) / 𝔠) ^ 2) ≤ Real.log ((sz.W n : ℕ) : ℝ) :=
    hM6.trans hlw𝔠
  have h2d : 2 * (d : ℝ) ≤ Real.log ((sz.W n : ℕ) : ℝ) := (le_max_left _ _).trans hM6'
  have hexp : Real.exp (-(Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ))) ≤
      (((sz.size n : ℕ) : ℝ) ^ (5 * d + 13))⁻¹ := by
    rw [meanFar_inv_pow_eq hN0]
    refine Real.exp_le_exp.2 (neg_le_neg ?_)
    have hB : 0 < (((5 * d + 13 : ℕ) : ℝ) / 𝔠) := by positivity
    have h3 := meanFar_three_halves hB ((le_max_right _ _).trans hM6')
    calc ((5 * d + 13 : ℕ) : ℝ) * Real.log ((sz.size n : ℕ) : ℝ)
        = (((5 * d + 13 : ℕ) : ℝ) / 𝔠) * (𝔠 * Real.log ((sz.size n : ℕ) : ℝ)) := by field_simp
      _ ≤ (((5 * d + 13 : ℕ) : ℝ) / 𝔠) * Real.log ((sz.W n : ℕ) : ℝ) :=
          mul_le_mul_of_nonneg_left hlw𝔠 hB.le
      _ ≤ _ := h3
  have hWdw : ((sz.W n : ℕ) : ℝ) ^ (-Dw) ≤ (((sz.size n : ℕ) : ℝ) ^ (5 * d + 13))⁻¹ := by
    calc ((sz.W n : ℕ) : ℝ) ^ (-Dw) ≤ (((sz.size n : ℕ) : ℝ) ^ 𝔠) ^ (-Dw) :=
          Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hN0 𝔠) hBwn (by linarith)
      _ = ((sz.size n : ℕ) : ℝ) ^ (𝔠 * (-Dw)) := (Real.rpow_mul hN0.le _ _).symm
      _ = ((sz.size n : ℕ) : ℝ) ^ (-((5 * d + 13 : ℕ) : ℝ)) := by
          congr 1; rw [hDw]; field_simp
      _ = (((sz.size n : ℕ) : ℝ) ^ (5 * d + 13))⁻¹ := by
          rw [Real.rpow_neg hN0.le, Real.rpow_natCast]
  -- the energy
  have hEn : |E n| < 2 := by have := hE n; linarith
  have hκ' : κ' ≤ (mE (E n)).im := by
    rw [mE_im]
    have hE2 : (E n) ^ 2 ≤ (2 - κ') ^ 2 := by
      have h1 := abs_le.1 (hE n)
      have h2 : κ' ≤ κ := min_le_left _ _
      exact sq_le_sq' (by linarith [h1.1]) (by linarith [h1.2])
    have hκ'1 : κ' ≤ 1 / 2 := min_le_right _ _
    have h4 : (2 * κ') ^ 2 ≤ 4 - (E n) ^ 2 := by nlinarith
    have h5 : 2 * κ' ≤ Real.sqrt (4 - (E n) ^ 2) := by
      calc 2 * κ' = Real.sqrt ((2 * κ') ^ 2) := (Real.sqrt_sq (by linarith)).symm
        _ ≤ _ := Real.sqrt_le_sqrt h4
    linarith
  have h5n : ∀ u : ℝ, 0 ≤ u → u < 1 → ∀ (σ : Fin 2 → Bool) (x : Zd d (sz.L n)),
      ‖Theta d (sz.L n) (sz.lam n) ((u : ℂ) * (STmsig (E n) (σ 0) * STmsig (E n) (σ 1))) 0 x‖ ≤
        C₅ * Bparam d (sz.L n) (sz.lam n) u (zdistD d (sz.L n) x) *
          Real.exp (-c₅ * ((zdistD d (sz.L n) x : ℕ) : ℝ) / ellT (sz.L n) (sz.lam n) u) := by
    intro u hu0 hu1 σ x
    exact H5 (sz.L n) hL (sz.lam n) hg hWO2 u hu0 hu1 (mE (E n)) (norm_mE hEn.le) (σ 0) (σ 1) x
  have h7n : ∀ (σ : Fin 2 → Bool) (a r : Zd d (sz.L n)),
      ((zdistD d (sz.L n) r : ℕ) : ℝ) ≤ 1 / 2 * ((zdistD d (sz.L n) a : ℕ) : ℝ) →
      ‖Theta d (sz.L n) (sz.lam n) ((t n : ℂ) * (STmsig (E n) (σ 0) * STmsig (E n) (σ 1))) 0 (a + r) +
          Theta d (sz.L n) (sz.lam n) ((t n : ℂ) * (STmsig (E n) (σ 0) * STmsig (E n) (σ 1))) 0 (a - r) -
          2 * Theta d (sz.L n) (sz.lam n) ((t n : ℂ) * (STmsig (E n) (σ 0) * STmsig (E n) (σ 1))) 0 a‖ ≤
        C₇ * (sz.lam n ^ 2 + |1 - t n|)⁻¹ * ((zdistD d (sz.L n) r : ℕ) : ℝ) ^ 2 *
          ((((zdistD d (sz.L n) a : ℕ) : ℝ) + 1) ^ d)⁻¹ := by
    intro σ a r h
    exact H7 (sz.L n) hL (sz.lam n) hg hWO2 (t n) ((hs0 n).trans (hst n).le) (ht n) (mE (E n))
      (norm_mE hEn.le) hκ' (σ 0) (σ 1) a r h
  intro σ a
  have hmain := meanFar_at_n sz n hd (E := E n) (s := s n) (t := t n) (τ := τ') (κ' := κ') (Λ := Λ)
    (C₅ := C₅) (c₅ := c₅) (C₇ := C₇) (Dw := Dw) hEn hκ'0 hκ' (hs0 n) (hst n) (ht n) hΛ hg hWO2
    (hreg n).1 (hreg n).2 hC₅ hC₇ h5n hc₅ h7n hτ'1 hA1 h2d hexp hWdw hbadn hN1 hN2 hlogN hpolyN
    hM4 hM5 σ a
  refine hmain.trans (mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le hN1 hτ') ?_)
  have hA0 : 0 < STAI sz n := lt_of_lt_of_le one_pos hA1
  have : 0 ≤ STAI sz n ^ (-(6 / 5 : ℝ)) := Real.rpow_nonneg hA0.le _
  positivity

/-- **The mean part of `lem;CLT`** (`(eq:boundEfar)`, `3_5:2192-2212`): the conclusion of `STCltFarConcl`
(same index set, same bound) for the deterministic quantity `‖𝔼 f^{far}_{σ,a}‖`: for every `τ > 0`,
eventually, `|𝔼 f^{far}_{σ,a}| ≤ N^τ (ilambda² W^d)^{-6/5} / (|a₁-a₂|^{d-2} + 1)`.  `S5-25` adds it to the
fluctuation bound `|f^{far} - 𝔼 f^{far}|` of `STCltFar`.  Registry class: none (proved here). -/
def STMeanFarConcl {d : ℕ} (sz : Sizes d) (E s t : ℕ → ℝ) : Prop :=
  Prec sz
    (U := fun n => {p : {σ : Fin 2 → Bool // σ 0 ≠ σ 1} × (Fin 2 → Zd d (sz.L n)) //
      Real.log ((sz.W n : ℕ) : ℝ) ^ 5 * ellT (sz.L n) (sz.lam n) (s n) ≤ ellT (sz.L n) (sz.lam n) (t n) ∧
        ((zdistInf d (sz.L n) (p.2 0 - p.2 1) : ℕ) : ℝ) ≤
          (1 / 2 : ℝ) * Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ) * ellT (sz.L n) (sz.lam n) (t n) +
            Real.log ((sz.W n : ℕ) : ℝ) ^ (5 / 2 : ℝ) * ellT (sz.L n) (sz.lam n) (s n)})
    (fun n p _ => ‖∫ ω, STfFar sz n (E n) (s n) (t n) p.1.1.1 p.1.2 ω ∂(sz.seqP)‖)
    (fun n p _ => (STAI sz n) ^ (-(6 / 5) : ℝ) /
      (((zdistInf d (sz.L n) (p.1.2 0 - p.1.2 1) : ℕ) : ℝ) ^ (d - 2) + 1))

/-- `STMeanFarConcl` in regime (i), with the hypotheses of every Step-5 pin (`STIngR5`). -/
def STMeanFar (d : ℕ) : Prop := STIngR5 d STReg5I (fun sz E s t => STMeanFarConcl sz E s t)

/-- **`stMeanFar`: the mean part of `f^{far}` is `≺ A^{-6/5}/(|a₁-a₂|^{d-2}+1)`** (`(eq:boundEfar)`,
`3_5:2192-2212`).  Uses of `STIngR5`: `STFlow` (admissibility, `(eq:WO)`, the spectral domain), the regime
`STReg5I`, `0 ≤ s < t ≤ lemT`, and `(Eq:Gdecay_w)` at `u = s` (`STStep2Concl`, `STGdecayW`); the invariances of
`𝔼𝓛^{(2)}` come from `stExpInv_holds`, the propagator bounds from `prop5Decay_holds`, `prop7Diff2_holds`. -/
theorem stMeanFar (d : ℕ) : STMeanFar d := by
  intro hd κ ε 𝔡 hκ hε h𝔡 Cd hCd
  refine ⟨1 / 100, by norm_num, le_rfl, ?_⟩
  intro 𝔠 sz z hflow s t hs0 hst ht hreg hKb hKw hLK hDec hDecS hCon hStep1 hStep2 hLmax hLKU
  obtain ⟨⟨h𝔠, -, hSz, hBw, hWO⟩, hloc⟩ := hflow
  have him : ∀ n, 0 < (z n).im := fun n =>
    lt_of_lt_of_le (Real.rpow_pos_of_pos (by exact_mod_cast sz.one_le_size n) _) (hloc n).2.1
  have hE : ∀ n, |STflowE z n| ≤ 2 - κ := fun n => (abs_lemE_le (him n)).trans (hloc n).1
  have ht1 : ∀ n, t n < 1 := fun n => (ht n).trans_lt (lemT_lt_one (him n))
  have hG := hStep2.2.2
  intro τ hτ D hD
  filter_upwards [meanFar_eventually hd sz hκ h𝔠 h𝔡 hSz hBw hWO (STflowE z) s t hE hs0 hst ht1 hreg hG τ hτ]
    with n hn
  have hempty : badSetAt sz.size
      (fun n (p : {p : {σ : Fin 2 → Bool // σ 0 ≠ σ 1} × (Fin 2 → Zd d (sz.L n)) //
        Real.log ((sz.W n : ℕ) : ℝ) ^ 5 * ellT (sz.L n) (sz.lam n) (s n) ≤ ellT (sz.L n) (sz.lam n) (t n) ∧
          ((zdistInf d (sz.L n) (p.2 0 - p.2 1) : ℕ) : ℝ) ≤
            (1 / 2 : ℝ) * Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ) * ellT (sz.L n) (sz.lam n) (t n) +
              Real.log ((sz.W n : ℕ) : ℝ) ^ (5 / 2 : ℝ) * ellT (sz.L n) (sz.lam n) (s n)}) (_ : sz.SeqΩ) =>
        ‖∫ ω, STfFar sz n (STflowE z n) (s n) (t n) p.1.1.1 p.1.2 ω ∂(sz.seqP)‖)
      (fun n p _ => (STAI sz n) ^ (-(6 / 5) : ℝ) /
        (((zdistInf d (sz.L n) (p.1.2 0 - p.1.2 1) : ℕ) : ℝ) ^ (d - 2) + 1)) τ n = ∅ := by
    ext ω
    simp only [badSetAt, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_exists, not_lt]
    intro u
    exact hn u.1.1.1 u.1.2
  change sz.seqP (badSetAt sz.size _ _ τ n) ≤ _
  rw [hempty, measure_empty]
  exact zero_le

end Eventually

/-! ## 9. Compiled nonempty instances at `d = 3` -/

section Instances

/-- The propagator profile of the instance: `T(x) = Θ_{t m₁m₂}(0, x)` at `d = 3`, `L = 5`, `g = 1/2`,
`t = 9/10`, `m = i` (`|m| = 1`, `Im m = 1`), `σ = (+,-)` (`m₁ m₂ = 1`): regime (i), `g²/L² = 1/100 ≤ 1 - t = 1/10`. -/
private def meanFar_Tinst (x : Zd 3 5) : ℂ :=
  Theta 3 5 (1 / 2) (((9 / 10 : ℝ) : ℂ) * (PropSpin Complex.I true * PropSpin Complex.I false)) 0 x

/-- The mean kernel of the instance: `B(a,b) = 1/(|a-b|_∞ + 1)` if `|a-b|₁ ≤ 1`, else `0`
(translation invariant, symmetric, and nonzero: `B(0,0) = 1`, `B(0,e₁) = 1/2`). -/
private def meanFar_Binst (a b : Zd 3 5) : ℂ :=
  if ((zdistD 3 5 (a - b) : ℕ) : ℝ) ≤ 1 then
    (((1 : ℝ) / (((zdistInf 3 5 (a - b) : ℕ) : ℝ) + 1) : ℝ) : ℂ) else 0

private theorem meanFar_Binst_tr (a b c : Zd 3 5) :
    meanFar_Binst (a + c) (b + c) = meanFar_Binst a b := by
  unfold meanFar_Binst; rw [add_sub_add_right_eq_sub]

private theorem meanFar_Binst_sym (a b : Zd 3 5) : meanFar_Binst a b = meanFar_Binst b a := by
  unfold meanFar_Binst
  rw [show a - b = -(b - a) by abel, zdistD_neg, meanFar_zdistInf_neg]

private theorem meanFar_Binst_zero (x : Zd 3 5) : meanFar_Binst 0 x =
    if ((zdistD 3 5 x : ℕ) : ℝ) ≤ 1 then
      (((1 : ℝ) / (((zdistInf 3 5 x : ℕ) : ℝ) + 1) : ℝ) : ℂ) else 0 := by
  unfold meanFar_Binst; rw [zero_sub, zdistD_neg, meanFar_zdistInf_neg]

/-- The propagator hypotheses of the core at the instance: `(prop:ThfadC)` and `(prop:BD2)`, from the proved
pins `prop5Decay_holds`, `prop7Diff2_holds` (`Λ = 1`, `κ = c = 1/2`), with the window `w₁ = 1` and `ρ = 1`. -/
private theorem meanFar_inst_T : ∃ K₁ K₂ : ℝ, 0 ≤ K₂ ∧
    (∀ x : Zd 3 5, ‖meanFar_Tinst x‖ ≤ K₁ / (((zdistInf 3 5 x : ℕ) : ℝ) + 1) ^ (3 - 2)) ∧
    (∀ a r : Zd 3 5, ((zdistD 3 5 r : ℕ) : ℝ) ≤ 1 → (1 : ℝ) < ((zdistInf 3 5 a : ℕ) : ℝ) →
      ‖meanFar_Tinst (a + r) + meanFar_Tinst (a - r) - 2 * meanFar_Tinst a‖ ≤
        K₂ * ((zdistD 3 5 r : ℕ) : ℝ) ^ 2 / (((zdistInf 3 5 a : ℕ) : ℝ) + 1) ^ 3) := by
  obtain ⟨C₅, hC₅, c₅, hc₅, H5⟩ := prop5Decay_holds 3 1 (by norm_num) one_pos
  obtain ⟨C₇, hC₇, H7⟩ := prop7Diff2_holds 3 1 (1 / 2) (1 / 2) (by norm_num) one_pos (by norm_num)
    (by norm_num) (by norm_num)
  have hξ : ‖(((9 / 10 : ℝ) : ℂ) * (PropSpin Complex.I true * PropSpin Complex.I false))‖ < 1 := by
    simp [PropSpin]; norm_num
  refine ⟨C₅ * (1 + 2 ^ (3 - 1)) / (1 / 2 : ℝ) ^ 2, C₇ / (1 / 2 : ℝ) ^ 2, by positivity, ?_, ?_⟩
  · intro x
    exact meanFar_T1 (d := 3) (L := 5) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hC₅.le hc₅ meanFar_Tinst
      (fun x => H5 5 (by norm_num) (1 / 2) (by norm_num) (by norm_num) (9 / 10) (by norm_num)
        (by norm_num) Complex.I (by simp) true false x) x
  · intro a r hr ha
    exact meanFar_T2 (d := 3) (L := 5) (g := 1 / 2) (t := 9 / 10) (ρ := 1) (w₁ := 1) (by norm_num)
      hC₇.le (by norm_num) (by norm_num) meanFar_Tinst
      (fun a r h => H7 5 (by norm_num) (1 / 2) (by norm_num) (by norm_num) (9 / 10) (by norm_num)
        (by norm_num) Complex.I (by simp) (by norm_num [Complex.I_im]) true false a r h) a r hr ha

open Classical in
/-- **Instance of `meanFar_core`** at `d = 3`, `L = 5`, `a = (0, e₁)`, `ρ = w₁ = 1`, `T = Θ_{t}(0,·)`
(`meanFar_Tinst`) and the nonzero kernel `B = meanFar_Binst` (`K = 1`, `K' = 0`): every deterministic
hypothesis is discharged (`hT1`, `hT2` from the proved pins `prop5Decay_holds`, `prop7Diff2_holds`). -/
example : ∃ K₁ K₂ : ℝ,
    ‖∑ b₁ ∈ Finset.univ.filter (fun b₁ : Zd 3 5 =>
        (1 : ℝ) < ((zdistInf 3 5 (b₁ - (![0, ![1, 0, 0]] : Fin 2 → Zd 3 5) 0) : ℕ) : ℝ) ∧
        (1 : ℝ) < ((zdistInf 3 5 (b₁ - (![0, ![1, 0, 0]] : Fin 2 → Zd 3 5) 1) : ℕ) : ℝ)),
      ∑ b₂ : Zd 3 5, meanFar_Tinst (b₁ - (![0, ![1, 0, 0]] : Fin 2 → Zd 3 5) 0) * meanFar_Binst b₁ b₂ *
        (meanFar_Tinst ((![0, ![1, 0, 0]] : Fin 2 → Zd 3 5) 1 - b₂) -
          meanFar_Tinst ((![0, ![1, 0, 0]] : Fin 2 → Zd 3 5) 1 - b₁))‖ ≤
      meanFar_Cd 3 * K₁ * K₂ * 1 * (1 + Real.log (((5 : ℕ) : ℝ) + 1)) * ((1 : ℝ) + 1) ^ 4 /
          (((zdistInf 3 5 ((![0, ![1, 0, 0]] : Fin 2 → Zd 3 5) 0 - (![0, ![1, 0, 0]] : Fin 2 → Zd 3 5) 1) : ℕ) : ℝ) + 1) ^ (3 - 2) +
        2 * K₁ ^ 2 * 0 * ((((5 : ℕ) : ℝ)) ^ 3) ^ 2 := by
  obtain ⟨K₁, K₂, hK₂, hT1, hT2⟩ := meanFar_inst_T
  refine ⟨K₁, K₂, ?_⟩
  refine meanFar_core (d := 3) (L := 5) (by norm_num) meanFar_Tinst meanFar_Binst meanFar_Binst_tr
    meanFar_Binst_sym 1 1 K₁ K₂ 1 0 zero_le_one hK₂ le_rfl hT1 hT2 ?_ ?_ _ _ (fun b hb => (Finset.mem_filter.1 hb).2)
  · intro x hx
    rw [meanFar_Binst_zero]
    simp only [hx, ↓reduceIte]
    rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    norm_num
  · intro x hx
    rw [meanFar_Binst_zero]
    simp only [not_le.2 hx, ↓reduceIte]
    simp

open Classical in
/-- The far set of the instance is nonempty (`b₁ = (2,2,2)`), the window is not collapsed and `B ≠ 0`. -/
example : (Finset.univ.filter (fun b₁ : Zd 3 5 =>
        (1 : ℝ) < ((zdistInf 3 5 (b₁ - (![0, ![1, 0, 0]] : Fin 2 → Zd 3 5) 0) : ℕ) : ℝ) ∧
        (1 : ℝ) < ((zdistInf 3 5 (b₁ - (![0, ![1, 0, 0]] : Fin 2 → Zd 3 5) 1) : ℕ) : ℝ))).Nonempty ∧
    meanFar_Binst 0 0 = 1 ∧ meanFar_Binst 0 ![1, 0, 0] = (1 / 2 : ℂ) ∧
    ((zdistD 3 5 (![1, 0, 0] : Zd 3 5) : ℕ) : ℝ) ≤ 1 := by
  refine ⟨⟨![2, 2, 2], Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_, ?_⟩⟩, ?_, ?_, ?_⟩
  · have : (1 : ℕ) < zdistInf 3 5 (![2, 2, 2] - (![0, ![1, 0, 0]] : Fin 2 → Zd 3 5) 0 : Zd 3 5) := by decide
    exact_mod_cast this
  · have : (1 : ℕ) < zdistInf 3 5 (![2, 2, 2] - (![0, ![1, 0, 0]] : Fin 2 → Zd 3 5) 1 : Zd 3 5) := by decide
    exact_mod_cast this
  · rw [meanFar_Binst_zero]
    have h0 : zdistD 3 5 (0 : Zd 3 5) = 0 := by decide
    have h1 : zdistInf 3 5 (0 : Zd 3 5) = 0 := by decide
    simp [h0, h1]
  · rw [meanFar_Binst_zero]
    have h0 : zdistD 3 5 (![1, 0, 0] : Zd 3 5) = 1 := by decide
    have h1 : zdistInf 3 5 (![1, 0, 0] : Zd 3 5) = 1 := by decide
    simp [h0, h1]
    norm_num
  · have h0 : zdistD 3 5 (![1, 0, 0] : Zd 3 5) = 1 := by decide
    simp [h0]

open Classical in
/-- The zero kernel `B = 0` (`K = K' = 0`): the instance of `meanFar_core` at the same data. -/
example : ∃ K₁ K₂ : ℝ,
    ‖∑ b₁ ∈ Finset.univ.filter (fun b₁ : Zd 3 5 =>
        (1 : ℝ) < ((zdistInf 3 5 (b₁ - (![0, ![1, 0, 0]] : Fin 2 → Zd 3 5) 0) : ℕ) : ℝ) ∧
        (1 : ℝ) < ((zdistInf 3 5 (b₁ - (![0, ![1, 0, 0]] : Fin 2 → Zd 3 5) 1) : ℕ) : ℝ)),
      ∑ b₂ : Zd 3 5, meanFar_Tinst (b₁ - (![0, ![1, 0, 0]] : Fin 2 → Zd 3 5) 0) * (0 : ℂ) *
        (meanFar_Tinst ((![0, ![1, 0, 0]] : Fin 2 → Zd 3 5) 1 - b₂) -
          meanFar_Tinst ((![0, ![1, 0, 0]] : Fin 2 → Zd 3 5) 1 - b₁))‖ ≤
      meanFar_Cd 3 * K₁ * K₂ * 0 * (1 + Real.log (((5 : ℕ) : ℝ) + 1)) * ((1 : ℝ) + 1) ^ 4 /
          (((zdistInf 3 5 ((![0, ![1, 0, 0]] : Fin 2 → Zd 3 5) 0 - (![0, ![1, 0, 0]] : Fin 2 → Zd 3 5) 1) : ℕ) : ℝ) + 1) ^ (3 - 2) +
        2 * K₁ ^ 2 * 0 * ((((5 : ℕ) : ℝ)) ^ 3) ^ 2 := by
  obtain ⟨K₁, K₂, hK₂, hT1, hT2⟩ := meanFar_inst_T
  refine ⟨K₁, K₂, ?_⟩
  refine meanFar_core (d := 3) (L := 5) (by norm_num) meanFar_Tinst (fun _ _ => 0) (fun _ _ _ => rfl)
    (fun _ _ => rfl) 1 1 K₁ K₂ 0 0 zero_le_one hK₂ le_rfl hT1 hT2 ?_ ?_ _ _
    (fun b hb => (Finset.mem_filter.1 hb).2)
  · intro x _; simp
  · intro x _; simp

/-- **Instance of `stMeanFar`** at `d = 3` on the merged sequence `szCL` (`L = 2(n+24)^5`, `W = 2^{n+24}`,
`ilambda = 1`, `s = 0`, `1-t = L^{-2}`: regime (i), `(con_st_ind)` for every `𝔠_d`): the flow, the regime and
`(con_st_ind)` are discharged; the stochastic premises of `STIngR5` (`STKbound`, `STLK`, ..., `STStep2Concl`)
stay hypotheses of the implication. -/
example (Cd : ℝ) (hCd : 0 < Cd) :
    Step5Inst.InstIng5Concl (fun sz E s t => STMeanFarConcl sz E s t) Step5Inst.szCL Step5Inst.zCL
      Step5Inst.sCL Step5Inst.tCL Cd :=
  Step5Inst.inst_ing5 STReg5I _ (stMeanFar 3) Step5Inst.szCL Step5Inst.zCL Step5Inst.flow_zCL
    Step5Inst.sCL Step5Inst.tCL (fun _ => le_rfl) Step5Inst.szCL_hst Step5Inst.lemT_zCL
    Step5Inst.szCL_reg5I (fun _ h𝔠 => Step5Inst.szCL_con h𝔠) Cd hCd

/-- The index set of `STMeanFarConcl` at `(szCL, sCL, tCL)` is nonempty for every `n` (it is that of
`STCltFarConcl`: `σ = (+,-)`, `a = (x_n, 0)`, `|a₁-a₂| = L_n/2`). -/
example (n : ℕ) :
    Nonempty {p : {σ : Fin 2 → Bool // σ 0 ≠ σ 1} × (Fin 2 → Zd 3 (Step5Inst.szCL.L n)) //
      Real.log ((Step5Inst.szCL.W n : ℕ) : ℝ) ^ 5 *
          ellT (Step5Inst.szCL.L n) (Step5Inst.szCL.lam n) (Step5Inst.sCL n) ≤
        ellT (Step5Inst.szCL.L n) (Step5Inst.szCL.lam n) (Step5Inst.tCL n) ∧
        ((zdistInf 3 (Step5Inst.szCL.L n) (p.2 0 - p.2 1) : ℕ) : ℝ) ≤
          (1 / 2 : ℝ) * Real.log ((Step5Inst.szCL.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ) *
              ellT (Step5Inst.szCL.L n) (Step5Inst.szCL.lam n) (Step5Inst.tCL n) +
            Real.log ((Step5Inst.szCL.W n : ℕ) : ℝ) ^ (5 / 2 : ℝ) *
              ellT (Step5Inst.szCL.L n) (Step5Inst.szCL.lam n) (Step5Inst.sCL n)} :=
  Step5Inst.szCL_cltFar_index_nonempty n

/-- **Instance of `meanFar_eventually`** at `(szCL, zCL, sCL, tCL)`, `d = 3`, `κ = ε = 1/10`, `𝔠 = 1/6`,
`𝔡 = 1/10`: the deterministic hypotheses (flow, `(eq:WO)`, bandwidth, regime) are discharged, the
pin `STGdecayW` (`(Eq:Gdecay_w)` at `u = s`) is a hypothesis of the instance. -/
example (Cd : ℝ) (hG : STGdecayW Step5Inst.szCL (STflowE Step5Inst.zCL) Step5Inst.sCL Step5Inst.tCL Cd)
    (τ : ℝ) (hτ : 0 < τ) :
    ∀ᶠ n in atTop, ∀ (σ : Fin 2 → Bool) (a : Fin 2 → Zd 3 (Step5Inst.szCL.L n)),
      ‖∫ ω, STfFar Step5Inst.szCL n (STflowE Step5Inst.zCL n) (Step5Inst.sCL n) (Step5Inst.tCL n) σ a ω
          ∂(Step5Inst.szCL.seqP)‖ ≤ ((Step5Inst.szCL.size n : ℕ) : ℝ) ^ τ *
        (STAI Step5Inst.szCL n ^ (-(6 / 5 : ℝ)) /
          (((zdistInf 3 (Step5Inst.szCL.L n) (a 0 - a 1) : ℕ) : ℝ) ^ (3 - 2) + 1)) := by
  have him : ∀ n, 0 < (Step5Inst.zCL n).im := fun n =>
    lt_of_lt_of_le (Real.rpow_pos_of_pos (by exact_mod_cast Step5Inst.szCL.one_le_size n) _)
      (Step5Inst.zCL_locDomain n).2.1
  have hE : ∀ n, |STflowE Step5Inst.zCL n| ≤ 2 - 1 / 10 := fun n =>
    (abs_lemE_le (him n)).trans (Step5Inst.zCL_locDomain n).1
  have ht1 : ∀ n, Step5Inst.tCL n < 1 := fun n => (Step5Inst.lemT_zCL n).trans_lt (lemT_lt_one (him n))
  exact meanFar_eventually (by norm_num) Step5Inst.szCL (κ := 1 / 10) (𝔠 := 1 / 6) (𝔡 := 1 / 10)
    (by norm_num) (by norm_num) (by norm_num) Step5Inst.szCL_tendsto Step5Inst.szCL_bandwidth
    Step5Inst.szCL_WO (STflowE Step5Inst.zCL) Step5Inst.sCL Step5Inst.tCL hE (fun _ => le_rfl)
    Step5Inst.szCL_hst ht1 Step5Inst.szCL_reg5I hG τ hτ


end Instances

end RBM.Gauss.Sizes
