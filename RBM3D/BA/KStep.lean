/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.BA.KInduct
import RBM3D.BA.KSumZeroB
import RBM3D.BA.KWardIneq
import RBM3D.BA.KPure
import RBM3D.BA.Prop6Path
import RBM3D.Loop.KLIndStepB

/-!
# Stage K, row K09b: the induction on molecules at BA, `(eq:K-pi-bound)` for every `n ≥ 3`

Ticket T2396 (design BA-DK, `docs/reports/T2360-design.md` §1 row `KLInduct` §7, §5; DECISIONS §209: a new generic file,
`Loop/KLInduct.lean` is not edited).

1. **The abstract step** (`kStep_step`, `kStep_all`): the induction step of `KLKpi_step` (`Loop/KLInduct.lean:984`) over abstract data
   `(Sig, TH, Kp)` on an index family `ι`, with the layer `∅` bound, the vanishing of an empty layer, the cut identity (the shape of
   `baKpi_cut_abs`), the inner bound `IndStepAbs` and the outer induction hypothesis as hypotheses.  Model-free.
2. **D3** (`baKpi_empty_bound`): `‖K^{(∅)}‖ ≤ C L^τ B_{t,0}^{n-1}` at BA, from `baKpi_empty_slice`, `baKpi_empty_short`, `baWardMol_holds`
   and `baIndStepAbs_holds`.
3. **The bundle** `IndStepTH` of the BA edges (`baIndStepAbs_holds`: `IndStepAbs` at the family `KWardIneq_Data d Λ κ`, from `indStepAbs_of` with
   `baSig_decay`, `baSig_sumZeroAbs` and the leaf bundle: properties 5-8 `baProp5to8_holds`, translation invariance, the row sum).
4. **`baKpiBoundAt_holds`**: `BAKpiBoundAt d n Λ κ` for every `n ≥ 3`, by `kStep_all` at `BAKpi`, `BASig`, `Θ`.
5. Compiled nonempty instances at the flow point `P` of `(d, L) = (3, 4)`.

Public: the declarations above; every other helper is `private` with the stem `KStep_`.
-/

set_option linter.style.longLine false

namespace RBM.BA

open RBM RBM.Loop
open scoped Matrix

/-! ## 1. The abstract step -/

section Abstract

/-- **`(eq:K-pi-bound)` at the polygon size `n` over abstract data**: the family `ι` of parameters, sizes `L`, the weight `Bp = B_{t,0}` and the
layer values `Kp k i σ a π` (polymorphic in the polygon size `k`): for every `τ > 0` one constant `C` with
`|Kp n i σ a π| ≤ C L^τ Bp^{n-1}`, every `i`, `σ`, `π`, `a`.  At BA this is `BAKpiBoundAt` (`BA/KInduct.lean:66`), at the band `KLKpiBoundAt`
(`Loop/KLInduct.lean:105`). -/
def KStepAt {ι : Type} (d : ℕ) (L : ι → ℕ) [∀ i, NeZero (L i)] (Bp : ι → ℝ)
    (Kp : ∀ (k : ℕ) [NeZero k] (i : ι), (Fin k → Bool) → (Fin k → Zd d (L i)) → Finset (Fin k × Fin k) → ℂ)
    (n : ℕ) [NeZero n] : Prop :=
  ∀ τ : ℝ, 0 < τ → ∃ C : ℝ, 0 < C ∧ ∀ (i : ι) (σ : Fin n → Bool) (π : Finset (Fin n × Fin n)) (a : Fin n → Zd d (L i)),
    ‖Kp n i σ a π‖ ≤ C * (L i : ℝ) ^ τ * (Bp i) ^ (n - 1)

/-- `‖∑_u t A(u) B(u)‖ ≤ ‖t‖ (∑_u ‖A u‖) M` when `‖B u‖ ≤ M` (the final chain of the cut: one glue sum, no kernel `S^{(B)}`). -/
private theorem KStep_norm_cut_le {G : Type*} [Fintype G] (t : ℂ) (A B : G → ℂ) {M : ℝ}
    (hB : ∀ u, ‖B u‖ ≤ M) : ‖∑ u, t * A u * B u‖ ≤ ‖t‖ * (∑ u, ‖A u‖) * M := by
  calc ‖∑ u, t * A u * B u‖ ≤ ∑ u, ‖t‖ * ‖A u‖ * ‖B u‖ := by
        refine (norm_sum_le _ _).trans (le_of_eq ?_)
        simp only [norm_mul]
    _ ≤ ∑ u, ‖t‖ * ‖A u‖ * M :=
        Finset.sum_le_sum fun u _ => mul_le_mul_of_nonneg_left (hB u) (by positivity)
    _ = ‖t‖ * (∑ u, ‖A u‖) * M := by rw [← Finset.sum_mul, ← Finset.mul_sum]

/-- **The induction step over abstract data** (strong induction on the number `n` of polygon vertices; the BA/abstract form of `KLKpi_step`,
`Loop/KLInduct.lean:984`): the bound `(eq:K-pi-bound)` at `n ≥ 3` follows from the bound at every `3 ≤ n'' < n` (outer polygons,
`n'' = n - (j - i) + 1`).  Hypotheses, all explicit:
* `hempty`: the layer `π = ∅` at `n`, `|Kp n σ a ∅| ≤ C L^τ Bp^{n-1}` (BA: `baKpi_empty_bound`);
* `hzero`: a layer with no tree vanishes (`KLTSPlong n σ π = ∅ → Kp = 0`; BA: `BAKpi` is the sum over `KLTSPlong`);
* `hcut`: the cut identity at an innermost edge `J ∈ π = KLFlong F₀ σ`, in the shape of `baKpi_cut_abs` (`BA/KInduct.lean:734`):
  `Kp n σ a π = ∑_u t A(u) Kp (n - w + 1) σ_out a_out(u) π'`, where `A(u)` is, verbatim, the summand of the left side of `IndStepAbs` at the
  inner polygon (`w + 1` vertices, root `Fin.last`);
* `hind`: the inner bound `IndStepAbs d k L Bp (Sig k) TH` at every `k ≥ 3` (`(eq:ind-step-bound)`; BA: `baIndStepAbs_holds`);
* `hout`: the bound at every `3 ≤ n'' < n`.
The glue weight `t` has `‖t‖ ≤ 1` (`ht`), `Bp ≥ 0` (`hBp`).  The cut keeps `(k-2) + (n''-1) = n - 1` and splits the loss `L^τ = L^{τ/2} L^{τ/2}`;
the constant depends on `n, τ` and the constants of the hypotheses only. -/
theorem kStep_step {ι : Type} (d : ℕ) (L : ι → ℕ) [∀ i, NeZero (L i)] (Bp t : ι → ℝ)
    (Sig : ∀ (k : ℕ) [NeZero k] (i : ι), (Fin k → Bool) → (Fin k → Zd d (L i)) → ℂ)
    (TH : ∀ i, Bool → Bool → Matrix (Zd d (L i)) (Zd d (L i)) ℂ)
    (Kp : ∀ (k : ℕ) [NeZero k] (i : ι), (Fin k → Bool) → (Fin k → Zd d (L i)) → Finset (Fin k × Fin k) → ℂ)
    (n : ℕ) [NeZero n] (hn : 3 ≤ n) (hBp : ∀ i, 0 ≤ Bp i) (ht : ∀ i, ‖((t i : ℝ) : ℂ)‖ ≤ 1)
    (hempty : ∀ τ : ℝ, 0 < τ → ∃ C : ℝ, 0 < C ∧ ∀ (i : ι) (σ : Fin n → Bool) (a : Fin n → Zd d (L i)),
      ‖Kp n i σ a ∅‖ ≤ C * (L i : ℝ) ^ τ * (Bp i) ^ (n - 1))
    (hzero : ∀ (i : ι) (σ : Fin n → Bool) (π : Finset (Fin n × Fin n)) (a : Fin n → Zd d (L i)),
      KLTSPlong n σ π = ∅ → Kp n i σ a π = 0)
    (hcut : ∀ (i : ι) (σ : Fin n → Bool) {F₀ : Finset (Fin n × Fin n)}, F₀ ∈ TSP n →
      ∀ {π : Finset (Fin n × Fin n)}, KLFlong F₀ σ = π → ∀ {J : Fin n × Fin n}, J ∈ π →
      (∀ e ∈ π, KLArcLe e J → e = J) → ∀ a : Fin n → Zd d (L i),
        Kp n i σ a π = ∑ u : Zd d (L i), (t i : ℂ) *
          (∑ δ ∈ Finset.univ.filter (fun δ : Fin (KLwIn J + 1) → Zd d (L i) => δ (Fin.last _) = u),
            Sig (KLwIn J + 1) i (sigmaIn σ J) δ *
              ∏ k ∈ Finset.univ.erase (Fin.last (KLwIn J)),
                TH i (sigmaIn σ J k) (sigmaIn σ J (k + 1)) (a (BAinVinv J k)) (δ k)) *
          Kp (n - KLwIn J + 1) i (sigmaOut σ J) (BAdeltaOut J a u) ((π.erase J).image (KLshiftOut J)))
    (hind : ∀ (k : ℕ) [NeZero k], 3 ≤ k → k < n → IndStepAbs d k L Bp (Sig k) TH)
    (hout : ∀ (k : ℕ) [NeZero k], 3 ≤ k → k < n → KStepAt d L Bp Kp k) :
    KStepAt d L Bp Kp n := by
  intro τ hτ
  have hτ2 : 0 < τ / 2 := half_pos hτ
  obtain ⟨C₀, hC₀, H₀⟩ := hempty τ hτ
  -- the inner constants (at `τ/2`) and the outer constants (at `τ/2`), one per width
  have hin : ∀ k : ℕ, ∃ C : ℝ, 0 < C ∧ (3 ≤ k → k < n → ∀ [NeZero k], ∀ (i : ι)
      (σ : Fin k → Bool) (r : Fin k), σ r ≠ σ (r + 1) → ∀ a : Fin k → Zd d (L i),
        ∑ b : Zd d (L i), ‖∑ δ ∈ Finset.univ.filter (fun δ : Fin k → Zd d (L i) => δ r = b),
            Sig k i σ δ * ∏ j ∈ Finset.univ.erase r, TH i (σ j) (σ (j + 1)) (a j) (δ j)‖
          ≤ C * (L i : ℝ) ^ (τ / 2) * (Bp i) ^ (k - 2)) := by
    intro k
    by_cases hk : 3 ≤ k ∧ k < n
    · have : NeZero k := ⟨by omega⟩
      obtain ⟨C, hC, H⟩ := hind k hk.1 hk.2 (τ / 2) hτ2
      exact ⟨C, hC, fun _ _ => H⟩
    · exact ⟨1, one_pos, fun h3 hlt => absurd ⟨h3, hlt⟩ hk⟩
  have hout' : ∀ k : ℕ, ∃ C : ℝ, 0 < C ∧ (3 ≤ k → k < n → ∀ [NeZero k], ∀ (i : ι)
      (σ : Fin k → Bool) (π : Finset (Fin k × Fin k)) (a : Fin k → Zd d (L i)),
        ‖Kp k i σ a π‖ ≤ C * (L i : ℝ) ^ (τ / 2) * (Bp i) ^ (k - 1)) := by
    intro k
    by_cases hk : 3 ≤ k ∧ k < n
    · have : NeZero k := ⟨by omega⟩
      obtain ⟨C, hC, H⟩ := hout k hk.1 hk.2 (τ / 2) hτ2
      exact ⟨C, hC, fun _ _ _ => H⟩
    · exact ⟨1, one_pos, fun h3 hlt => absurd ⟨h3, hlt⟩ hk⟩
  choose Ci hCi0 hCi using hin
  choose Co hCo0 hCo using hout'
  have hsum0 : 0 ≤ ∑ w ∈ Finset.range n, Ci (w + 1) * Co (n - w + 1) :=
    Finset.sum_nonneg fun w _ => mul_nonneg (hCi0 _).le (hCo0 _).le
  refine ⟨C₀ + ∑ w ∈ Finset.range n, Ci (w + 1) * Co (n - w + 1), by positivity, ?_⟩
  intro i σ π a
  have hB0 : 0 ≤ Bp i := hBp i
  have hLτ0 : 0 ≤ (L i : ℝ) ^ τ := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hBn : 0 ≤ (Bp i) ^ (n - 1) := pow_nonneg hB0 _
  have hRHS : 0 ≤ (C₀ + ∑ w ∈ Finset.range n, Ci (w + 1) * Co (n - w + 1)) * (L i : ℝ) ^ τ
      * (Bp i) ^ (n - 1) := by positivity
  by_cases hπ0 : π = ∅
  · -- the layer `π = ∅`
    subst hπ0
    refine (H₀ i σ a).trans ?_
    have : 0 ≤ (∑ w ∈ Finset.range n, Ci (w + 1) * Co (n - w + 1)) * (L i : ℝ) ^ τ
        * (Bp i) ^ (n - 1) := by positivity
    nlinarith [this]
  rcases (KLTSPlong n σ π).eq_empty_or_nonempty with hemp | ⟨F₀, hF₀⟩
  · -- no tree has the long edges `π`
    rw [hzero i σ π a hemp, norm_zero]
    exact hRHS
  obtain ⟨hF₀T, hπ⟩ := Finset.mem_filter.1 hF₀
  have hsub : π ⊆ diagonals n := by rw [← hπ]; exact Flong_subset_diagonals hF₀T σ
  obtain ⟨J, hJ, hinner⟩ := exists_innermost hsub (Finset.nonempty_iff_ne_empty.2 hπ0)
  have hJd : IsDiag n J.1 J.2 := (Finset.mem_filter.1 (hsub hJ)).2
  have hJlong : σ J.1 ≠ σ J.2 := by
    have hJ' : J ∈ KLFlong F₀ σ := by rw [hπ]; exact hJ
    exact (Finset.mem_filter.1 hJ').2
  obtain ⟨hJ12, hJadj, hJwhole⟩ := hJd
  rw [Fin.lt_def] at hJ12
  have hJ2n := J.2.isLt
  have hw2 : 2 ≤ KLwIn J := by simp only [KLwIn]; omega
  have hwn : KLwIn J + 2 ≤ n := by
    simp only [KLwIn]
    by_cases h0 : J.1.val = 0
    · have : J.2.val ≠ n - 1 := fun h => hJwhole ⟨h0, h⟩
      omega
    · omega
  rw [hcut i σ hF₀T hπ hJ hinner a]
  -- the outer average
  have hB : ∀ u : Zd d (L i), ‖Kp (n - KLwIn J + 1) i (sigmaOut σ J) (BAdeltaOut J a u)
      ((π.erase J).image (KLshiftOut J))‖
        ≤ Co (n - KLwIn J + 1) * (L i : ℝ) ^ (τ / 2) * (Bp i) ^ (n - KLwIn J + 1 - 1) := fun u =>
    hCo (n - KLwIn J + 1) (by omega) (by omega) i (sigmaOut σ J) _ (BAdeltaOut J a u)
  -- the inner root sum
  have hroot : sigmaIn σ J (Fin.last (KLwIn J)) ≠ sigmaIn σ J (Fin.last (KLwIn J) + 1) := by
    rw [Fin.last_add_one]
    have e1 : sigmaIn σ J (Fin.last (KLwIn J)) = σ J.2 := by
      simp only [sigmaIn, Fin.val_last]
      congr 1
      ext
      simp only [KLwIn]
      omega
    have e2 : sigmaIn σ J 0 = σ J.1 := by
      simp only [sigmaIn, Fin.val_zero, add_zero]
      congr 1
      ext
      simp only
      omega
    rw [e1, e2]
    exact Ne.symm hJlong
  have hA := hCi (KLwIn J + 1) (by omega) (by omega) i (sigmaIn σ J) (Fin.last (KLwIn J)) hroot
    (fun k => a (BAinVinv J k))
  refine (KStep_norm_cut_le _ _ _ hB).trans ?_
  have hM0 : 0 ≤ Co (n - KLwIn J + 1) * (L i : ℝ) ^ (τ / 2) * (Bp i) ^ (n - KLwIn J + 1 - 1) :=
    mul_nonneg (mul_nonneg (hCo0 _).le (Real.rpow_nonneg (Nat.cast_nonneg _) _)) (pow_nonneg hB0 _)
  have hpow : (Bp i) ^ (KLwIn J + 1 - 2) * (Bp i) ^ (n - KLwIn J + 1 - 1) = (Bp i) ^ (n - 1) := by
    rw [← pow_add]; congr 1; omega
  have hLL : (L i : ℝ) ^ (τ / 2) * (L i : ℝ) ^ (τ / 2) = (L i : ℝ) ^ τ := by
    rw [← Real.rpow_add (by exact_mod_cast (NeZero.pos (L i))), add_halves]
  -- the single term of the constant
  have hterm : Ci (KLwIn J + 1) * Co (n - KLwIn J + 1)
      ≤ ∑ w ∈ Finset.range n, Ci (w + 1) * Co (n - w + 1) :=
    Finset.single_le_sum (f := fun w => Ci (w + 1) * Co (n - w + 1))
      (fun w _ => mul_nonneg (hCi0 _).le (hCo0 _).le) (Finset.mem_range.2 (by omega))
  calc _ ≤ 1 * (Ci (KLwIn J + 1) * (L i : ℝ) ^ (τ / 2) * (Bp i) ^ (KLwIn J + 1 - 2)) *
          (Co (n - KLwIn J + 1) * (L i : ℝ) ^ (τ / 2) * (Bp i) ^ (n - KLwIn J + 1 - 1)) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul (ht i) hA (Finset.sum_nonneg fun _ _ => norm_nonneg _) zero_le_one) hM0
    _ = (Ci (KLwIn J + 1) * Co (n - KLwIn J + 1)) * ((L i : ℝ) ^ (τ / 2) * (L i : ℝ) ^ (τ / 2)) *
          ((Bp i) ^ (KLwIn J + 1 - 2) * (Bp i) ^ (n - KLwIn J + 1 - 1)) := by ring
    _ = (Ci (KLwIn J + 1) * Co (n - KLwIn J + 1)) * (L i : ℝ) ^ τ * (Bp i) ^ (n - 1) := by
        rw [hLL, hpow]
    _ ≤ (C₀ + ∑ w ∈ Finset.range n, Ci (w + 1) * Co (n - w + 1)) * (L i : ℝ) ^ τ * (Bp i) ^ (n - 1) := by
        have h1 : Ci (KLwIn J + 1) * Co (n - KLwIn J + 1)
            ≤ C₀ + ∑ w ∈ Finset.range n, Ci (w + 1) * Co (n - w + 1) := by linarith
        gcongr

/-- **The induction for every `n ≥ 3`** (strong induction on `n` with `kStep_step`): the per-`n` hypotheses of `kStep_step` for every `n ≥ 3`
give `KStepAt d L Bp Kp n` for every `n ≥ 3`.  `hind` is the inner bound at every `k ≥ 3`. -/
theorem kStep_all {ι : Type} (d : ℕ) (L : ι → ℕ) [∀ i, NeZero (L i)] (Bp t : ι → ℝ)
    (Sig : ∀ (k : ℕ) [NeZero k] (i : ι), (Fin k → Bool) → (Fin k → Zd d (L i)) → ℂ)
    (TH : ∀ i, Bool → Bool → Matrix (Zd d (L i)) (Zd d (L i)) ℂ)
    (Kp : ∀ (k : ℕ) [NeZero k] (i : ι), (Fin k → Bool) → (Fin k → Zd d (L i)) → Finset (Fin k × Fin k) → ℂ)
    (hBp : ∀ i, 0 ≤ Bp i) (ht : ∀ i, ‖((t i : ℝ) : ℂ)‖ ≤ 1)
    (hempty : ∀ (n : ℕ) [NeZero n], 3 ≤ n → ∀ τ : ℝ, 0 < τ → ∃ C : ℝ, 0 < C ∧
      ∀ (i : ι) (σ : Fin n → Bool) (a : Fin n → Zd d (L i)),
        ‖Kp n i σ a ∅‖ ≤ C * (L i : ℝ) ^ τ * (Bp i) ^ (n - 1))
    (hzero : ∀ (n : ℕ) [NeZero n], 3 ≤ n → ∀ (i : ι) (σ : Fin n → Bool) (π : Finset (Fin n × Fin n))
      (a : Fin n → Zd d (L i)), KLTSPlong n σ π = ∅ → Kp n i σ a π = 0)
    (hcut : ∀ (n : ℕ) [NeZero n], 3 ≤ n → ∀ (i : ι) (σ : Fin n → Bool) {F₀ : Finset (Fin n × Fin n)}, F₀ ∈ TSP n →
      ∀ {π : Finset (Fin n × Fin n)}, KLFlong F₀ σ = π → ∀ {J : Fin n × Fin n}, J ∈ π →
      (∀ e ∈ π, KLArcLe e J → e = J) → ∀ a : Fin n → Zd d (L i),
        Kp n i σ a π = ∑ u : Zd d (L i), (t i : ℂ) *
          (∑ δ ∈ Finset.univ.filter (fun δ : Fin (KLwIn J + 1) → Zd d (L i) => δ (Fin.last _) = u),
            Sig (KLwIn J + 1) i (sigmaIn σ J) δ *
              ∏ k ∈ Finset.univ.erase (Fin.last (KLwIn J)),
                TH i (sigmaIn σ J k) (sigmaIn σ J (k + 1)) (a (BAinVinv J k)) (δ k)) *
          Kp (n - KLwIn J + 1) i (sigmaOut σ J) (BAdeltaOut J a u) ((π.erase J).image (KLshiftOut J)))
    (hind : ∀ (k : ℕ) [NeZero k], 3 ≤ k → IndStepAbs d k L Bp (Sig k) TH) :
    ∀ (n : ℕ) [NeZero n], 3 ≤ n → KStepAt d L Bp Kp n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro _ hn
    exact kStep_step d L Bp t Sig TH Kp n hn hBp ht (hempty n hn) (hzero n hn) (hcut n hn)
      (fun k _ h3 _ => hind k h3) (fun k _ h3 hlt => ih k hlt h3)

end Abstract

end RBM.BA
