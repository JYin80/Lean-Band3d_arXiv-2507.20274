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

1. **The abstract step** (`KStep_step`, `KStep_all`, bound `KStepAt`): the induction step of `KLKpi_step` (`Loop/KLInduct.lean:984`) over abstract data
   `(Sig, TH, Kp)` on an index family `ι` (`Sig`, `Kp` polymorphic in the polygon size).  Hypotheses: the layer `∅` bound, a layer with no tree
   vanishes, the cut identity (the shape of `baKpi_cut_abs`), the inner bound `IndStepAbs`, the outer induction hypothesis; and `‖t‖ ≤ 1`, `Bp ≥ 0`.
   Model-free.
2. **The leaf bundle and `IndStepAbs` at BA** (`KStep_baIndStepAbs_holds`): `indStepAbs_of` at the family `KWardIneq_Data d Λ κ` with `baSig_decay`,
   `baSig_sumZeroAbs` and the bundle `IndStepTH` of the BA edges (properties 5-8 `baProp5to8_holds`, translation invariance, the row sum).
3. **D3** (`baKpi_empty_bound`): `‖K^{(∅)}‖ ≤ C L^τ B_{t,0}^{n-1}` at BA, from `baKpi_empty_slice`, `baKpi_empty_short`, `baWardMol_holds` and
   `KStep_baIndStepAbs_holds`.
4. **`baKpiBoundAt_holds`**: `BAKpiBoundAt d n Λ κ` for every `n ≥ 3`, by `KStep_all` at `BAKpi`, `BASig`, `Θ`.
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
* `hind`: the inner bound `IndStepAbs d k L Bp (Sig k) TH` at every `k ≥ 3` (`(eq:ind-step-bound)`; BA: `KStep_baIndStepAbs_holds`);
* `hout`: the bound at every `3 ≤ n'' < n`.
The glue weight `t` has `‖t‖ ≤ 1` (`ht`), `Bp ≥ 0` (`hBp`).  The cut keeps `(k-2) + (n''-1) = n - 1` and splits the loss `L^τ = L^{τ/2} L^{τ/2}`;
the constant depends on `n, τ` and the constants of the hypotheses only. -/
theorem KStep_step {ι : Type} (d : ℕ) (L : ι → ℕ) [∀ i, NeZero (L i)] (Bp t : ι → ℝ)
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

/-- **The induction for every `n ≥ 3`** (strong induction on `n` with `KStep_step`): the per-`n` hypotheses of `KStep_step` for every `n ≥ 3`
give `KStepAt d L Bp Kp n` for every `n ≥ 3`.  `hind` is the inner bound at every `k ≥ 3`. -/
theorem KStep_all {ι : Type} (d : ℕ) (L : ι → ℕ) [∀ i, NeZero (L i)] (Bp t : ι → ℝ)
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
    exact KStep_step d L Bp t Sig TH Kp n hn hBp ht (hempty n hn) (hzero n hn) (hcut n hn)
      (fun k _ h3 _ => hind k h3) (fun k _ h3 hlt => ih k hlt h3)

end Abstract

/-! ## 2. The `Θ` calculus at the BA data (private copies: the originals in `KInduct`, `KWardIneq` are private) -/

section Calculus

variable {d L : ℕ} [NeZero L]

/-- `Θ^{(s,s')} = (1 - t M^{(s,s')})⁻¹` is invariant under a permutation `e` of the labels fixing every `M(σ)` (a copy of the private
`KInduct_theta_perm`, `BA/KInduct.lean:128`). -/
private theorem KStep_theta_perm (e : Zd d L ≃ Zd d L) (M : Bool → Matrix (Zd d L) (Zd d L) ℂ)
    (hM : ∀ σ x y, M σ (e x) (e y) = M σ x y) (t : ℝ) (s s' : Bool) (x y : Zd d L) :
    BAThetaOf M t s s' (e x) (e y) = BAThetaOf M t s s' x y := by
  have hQ : ∀ x y, BAMssOf M s s' (e x) (e y) = BAMssOf M s s' x y := fun x y => by
    simp only [BAMssOf, Matrix.of_apply, hM]
  have hA : ((1 : Matrix (Zd d L) (Zd d L) ℂ) - (t : ℂ) • BAMssOf M s s').submatrix e e =
      1 - (t : ℂ) • BAMssOf M s s' := by
    ext x y
    simp only [Matrix.submatrix_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
      e.injective.eq_iff, hQ]
  have h2 := Matrix.inv_submatrix_equiv ((1 : Matrix (Zd d L) (Zd d L) ℂ) - (t : ℂ) • BAMssOf M s s') e e
  rw [hA] at h2
  unfold BAThetaOf PropThetaQ
  rw [← Matrix.nonsing_inv_eq_ringInverse]
  have h3 := congrFun (congrFun h2 x) y
  rw [Matrix.submatrix_apply] at h3
  exact h3.symm

/-- Translation invariance of `Θ`: `Θ_t^{(s,s')}(x, y) = Θ_t^{(s,s')}(0, y - x)` (a copy of the private `KInduct_theta_shift`,
`BA/KInduct.lean:147`). -/
private theorem KStep_theta_shift (g E : ℝ) (m : ℂ) (t : ℝ) (s s' : Bool) (x y : Zd d L) :
    BATheta d L g E m t s s' x y = BATheta d L g E m t s s' 0 (y - x) := by
  have h := KStep_theta_perm (Equiv.addRight (-x)) (BAMsigma d L (BAMB d L g (E : ℂ) m))
    (fun σ u v => BAMsigma_shift d L g (E : ℂ) m σ u v (-x)) t s s' x y
  simp only [Equiv.coe_addRight, add_neg_cancel, ← sub_eq_add_neg] at h
  exact h.symm

/-- `Σ_b |Θ(a,b)| ≤ (1-t)⁻¹` from the right resolvent identity `Θ = 1 + t Θ Q` and `Σ_b |Q(c,b)| ≤ 1` (a copy of the private
`KWardIneq_row_of_resolvent`, `BA/KWardIneq.lean:184`). -/
private theorem KStep_row_of_resolvent {G : Type*} [Fintype G] [DecidableEq G] (Θ Q : Matrix G G ℂ)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) (hres : Θ = 1 + (t : ℂ) • (Θ * Q))
    (hQ : ∀ c, ∑ b, ‖Q c b‖ ≤ 1) (a : G) : ∑ b, ‖Θ a b‖ ≤ (1 - t)⁻¹ := by
  set R : ℝ := ∑ b, ‖Θ a b‖ with hR
  have hpt : ∀ b, ‖Θ a b‖ ≤ (if a = b then (1 : ℝ) else 0) + t * ∑ c, ‖Θ a c‖ * ‖Q c b‖ := by
    intro b
    have h := congrFun (congrFun hres a) b
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, Matrix.mul_apply] at h
    rw [h]
    refine (norm_add_le _ _).trans ?_
    have h1 : ‖(if a = b then (1 : ℂ) else 0)‖ = if a = b then (1 : ℝ) else 0 := by split_ifs <;> simp
    have h2 : ‖(t : ℂ) * ∑ c, Θ a c * Q c b‖ ≤ t * ∑ c, ‖Θ a c‖ * ‖Q c b‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ht0]
      refine mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (le_of_eq ?_)) ht0
      exact Finset.sum_congr rfl fun c _ => norm_mul _ _
    rw [h1]
    linarith
  have hsum : R ≤ 1 + t * R := by
    calc R = ∑ b, ‖Θ a b‖ := rfl
      _ ≤ ∑ b, ((if a = b then (1 : ℝ) else 0) + t * ∑ c, ‖Θ a c‖ * ‖Q c b‖) := Finset.sum_le_sum fun b _ => hpt b
      _ = 1 + t * ∑ c, ‖Θ a c‖ * ∑ b, ‖Q c b‖ := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_comm]
          simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true, ← Finset.mul_sum]
      _ ≤ 1 + t * ∑ c, ‖Θ a c‖ * 1 := by
          gcongr with c _
          exact hQ c
      _ = 1 + t * R := by simp [hR]
  have h1t : 0 < 1 - t := by linarith
  rw [← one_div, le_div_iff₀ h1t]
  nlinarith

/-- **`(eq:THETAinftinf)` at BA, rows**: `Σ_b |Θ_t^{(s,s')}(a,b)| ≤ (1-t)⁻¹` for all four charge pairs: the right resolvent identity
(`BATheta_resolvent`) and `Σ_b |M^{(s,s')}_{cb}| = Σ_b K_{cb} = 1` (`BAMss_norm_eq_BAK`, `BAK_row_sum`); a copy of the private
`KWardIneq_theta_row_le`, `BA/KWardIneq.lean:255`. -/
private theorem KStep_theta_row_le {g κ E : ℝ} {m : ℂ} (hr : BAReal d L g κ E m) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1)
    (s s' : Bool) (a : Zd d L) :
    ∑ b, ‖BAThetaOf (BAMsigma d L (BAMB d L g (E : ℂ) m)) t s s' a b‖ ≤ (1 - t)⁻¹ := by
  refine KStep_row_of_resolvent (BATheta d L g E m t s s') (BAMss d L (BAMB d L g (E : ℂ) m) s s') ht0 ht1
    (BATheta_resolvent d L g κ E m hr t ht0 ht1 s s').2 (fun c => ?_) a
  simp only [BAMss_norm_eq_BAK]
  exact (BAK_row_sum d L g E m hr.1 c).le

end Calculus

section Constants

/-- `1 ≤ L^τ` for `L ≥ 3`, `τ > 0`. -/
private theorem KStep_one_le_rpow {L : ℕ} (hL : 3 ≤ L) {τ : ℝ} (hτ : 0 < τ) : (1 : ℝ) ≤ (L : ℝ) ^ τ :=
  Real.one_le_rpow (by exact_mod_cast (by omega : 1 ≤ L)) hτ.le

/-- `C P ≤ C L' P` for `C, P ≥ 0`, `L' ≥ 1` (a loss factor is spent). -/
private theorem KStep_mul_loss {C L' P : ℝ} (hC : 0 ≤ C) (hP : 0 ≤ P) (hL : 1 ≤ L') : C * P ≤ C * L' * P := by
  nlinarith [mul_nonneg (mul_nonneg hC hP) (sub_nonneg.2 hL)]

/-- **Properties 4 + 5** (`BAProp5`): every entry of every `Θ_t^{(σ₁,σ₂)}` is `≤ C_d B_{t,0}` (a copy of the private
`KInduct_theta_sup`, `BA/KInduct.lean:188`). -/
private theorem KStep_theta_sup {d : ℕ} (hd : 3 ≤ d) {Λ κ : ℝ} (hΛ : 0 < Λ) (hκ : 0 < κ) :
    ∃ Cd : ℝ, 0 < Cd ∧ ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → g ≤ Λ → ∀ (E : ℝ) (m : ℂ),
      haveI : NeZero L := ⟨by omega⟩
      BAReal d L g κ E m → ∀ t : ℝ, 0 ≤ t → t < 1 → ∀ (σ₁ σ₂ : Bool) (x y : Zd d L),
        ‖BATheta d L g E m t σ₁ σ₂ x y‖ ≤ Cd * Bparam d L g t 0 := by
  obtain ⟨Cd, hCd, cd, hcd, hbd⟩ := baProp5_holds d Λ κ hd hΛ hκ
  refine ⟨Cd, hCd, fun L hL g hg hgΛ E m => ?_⟩
  have : NeZero L := ⟨by omega⟩
  intro hr t ht0 ht1 σ₁ σ₂ x y
  rw [KStep_theta_shift]
  exact KLIndStepA_decay_le_zero (by omega) hCd.le hcd.le (y - x)
    (hbd L hL g hg hgΛ E m hr t ht0 ht1 σ₁ σ₂ (y - x))

/-- **Property 5'** (`BAProp5s`): `Σ_b |Θ_t^{(σ,σ)}(x, b)| ≤ S`, `S = C_s (1 + Λ² expC k c_s)` (`d = k + 2`; a copy of the private
`KInduct_theta_l1`, `BA/KInduct.lean:203`). -/
private theorem KStep_theta_l1 {k : ℕ} (hd : 3 ≤ k + 2) {Λ κ : ℝ} (hΛ : 0 < Λ) (hκ : 0 < κ) :
    ∃ S : ℝ, 0 < S ∧ ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → g ≤ Λ → ∀ (E : ℝ) (m : ℂ),
      haveI : NeZero L := ⟨by omega⟩
      BAReal (k + 2) L g κ E m → ∀ t : ℝ, 0 ≤ t → t < 1 → ∀ (σ : Bool) (x : Zd (k + 2) L),
        ∑ b : Zd (k + 2) L, ‖BATheta (k + 2) L g E m t σ σ x b‖ ≤ S := by
  obtain ⟨Cs, hCs, cs, hcs, hbd⟩ := baProp5s_holds (k + 2) Λ κ hd hΛ hκ
  have hexpC : 0 ≤ expC k cs := by unfold expC; positivity
  refine ⟨Cs * (1 + Λ ^ 2 * expC k cs), by positivity, fun L hL g hg hgΛ E m => ?_⟩
  have : NeZero L := ⟨by omega⟩
  intro hr t ht0 ht1 σ x
  have hpt : ∀ b : Zd (k + 2) L, ‖BATheta (k + 2) L g E m t σ σ x b‖
      ≤ Cs * ((if b - x = 0 then (1 : ℝ) else 0)
          + g ^ 2 * Real.exp (-(cs * (zdistD (k + 2) L (b - x) : ℝ)))) := by
    intro b
    rw [KStep_theta_shift]
    have := hbd L hL g hg hgΛ E m hr t ht0 ht1 σ (b - x)
    simpa [neg_mul] using this
  have h1 : ∑ b : Zd (k + 2) L, (if b - x = 0 then (1 : ℝ) else 0) = 1 := by
    simp [sub_eq_zero]
  have h2 : ∑ b : Zd (k + 2) L, Real.exp (-(cs * (zdistD (k + 2) L (b - x) : ℝ))) ≤ expC k cs :=
    (le_of_eq (Fintype.sum_equiv (Equiv.subRight x) _
      (fun y : Zd (k + 2) L => Real.exp (-(cs * (zdistD (k + 2) L y : ℝ)))) fun b => rfl)).trans
      (sum_radial_exp_decay_le k hcs)
  calc ∑ b : Zd (k + 2) L, ‖BATheta (k + 2) L g E m t σ σ x b‖
      ≤ ∑ b : Zd (k + 2) L, Cs * ((if b - x = 0 then (1 : ℝ) else 0)
          + g ^ 2 * Real.exp (-(cs * (zdistD (k + 2) L (b - x) : ℝ)))) :=
        Finset.sum_le_sum fun b _ => hpt b
    _ = Cs * (1 + g ^ 2 * ∑ b : Zd (k + 2) L, Real.exp (-(cs * (zdistD (k + 2) L (b - x) : ℝ)))) := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib, h1, ← Finset.mul_sum]
    _ ≤ Cs * (1 + g ^ 2 * expC k cs) := by gcongr
    _ ≤ Cs * (1 + Λ ^ 2 * expC k cs) := by
        have : g ^ 2 ≤ Λ ^ 2 := pow_le_pow_left₀ hg.le hgΛ 2
        gcongr

end Constants

/-! ## 3. The leaf bundle `IndStepTH` at the BA edges, and `IndStepAbs` at BA -/

section Bundle

/-- **The leaf bundle at BA** (the BA twin of `indStepTH_band`, `Loop/KLIndStepA.lean:1100`): `IndStepTH` for the edges `Θ` of the BA data at the
family `KWardIneq_Data d Λ κ`.  Properties 5, 5', 6, 7, 8 are `baProp5to8_holds` (6 and 7 at `c = 1/2`; the loss `L^τ ≥ 1` of the fields is not
needed by the BA statements), the translation field is `KStep_theta_shift`, the row sum `KStep_theta_row_le`
(`BAThetaOf (BAMsigma ..) = BATheta` by `rfl`, `BATheta0` is the zero-mode expression of the field). -/
private theorem KStep_indStepTH {d : ℕ} (hd : 3 ≤ d) {Λ κ : ℝ} (hΛ : 0 < Λ) (hκ : 0 < κ) :
    IndStepTH (ι := KWardIneq_Data d Λ κ) d (fun i => i.L) (fun i => i.g) (fun i => i.t)
      (fun i s s' => BAThetaOf (BAMsigma d i.L (BAMB d i.L i.g (i.E : ℂ) i.m)) i.t s s') := by
  obtain ⟨C5, hC5, c5, hc5, H5⟩ := baProp5_holds d Λ κ hd hΛ hκ
  obtain ⟨Cs, hCs, cs, hcs, Hs⟩ := baProp5s_holds d Λ κ hd hΛ hκ
  refine ⟨fun i s s' a b => KStep_theta_shift i.g i.E i.m i.t s s' a b, ⟨C5, hC5, c5, hc5, ?_⟩,
    ⟨Cs, hCs, cs, hcs, ?_⟩, fun τ hτ => ?_, fun τ hτ => ?_, fun τ hτ => ?_, ?_⟩
  · intro i s s' _ a
    exact H5 i.L i.hL i.g i.hg i.hgΛ i.E i.m i.hr i.t i.ht0 i.ht1 s s' a
  · intro i s a
    exact Hs i.L i.hL i.g i.hg i.hgΛ i.E i.m i.hr i.t i.ht0 i.ht1 s a
  · obtain ⟨C, hC, H⟩ := baProp6_holds d Λ κ (1 / 2) hd hΛ hκ (by norm_num) (by norm_num)
    refine ⟨C, hC, fun i s s' _ a r hr => ?_⟩
    refine (H i.L i.hL i.g i.hg i.hgΛ i.E i.m i.hr i.t i.ht0 i.ht1 s s' a r hr).trans ?_
    have h0 : 0 ≤ (i.g ^ 2 + |1 - i.t|)⁻¹ * (zdistD d i.L r : ℝ) * (((zdistD d i.L a : ℝ) + 1) ^ (d - 1))⁻¹ := by
      positivity
    have key := KStep_mul_loss hC.le h0 (KStep_one_le_rpow i.hL hτ)
    calc _ = C * ((i.g ^ 2 + |1 - i.t|)⁻¹ * (zdistD d i.L r : ℝ) * (((zdistD d i.L a : ℝ) + 1) ^ (d - 1))⁻¹) := by
          ring
      _ ≤ _ := key.trans (le_of_eq (by ring))
  · obtain ⟨C, hC, H⟩ := baProp7_holds d Λ κ (1 / 2) hd hΛ hκ (by norm_num) (by norm_num)
    refine ⟨C, hC, fun i s s' _ a r hr => ?_⟩
    refine (H i.L i.hL i.g i.hg i.hgΛ i.E i.m i.hr i.t i.ht0 i.ht1 s s' a r hr).trans ?_
    have h0 : 0 ≤ (i.g ^ 2 + |1 - i.t|)⁻¹ * (zdistD d i.L r : ℝ) ^ 2 * (((zdistD d i.L a : ℝ) + 1) ^ d)⁻¹ := by
      positivity
    have key := KStep_mul_loss hC.le h0 (KStep_one_le_rpow i.hL hτ)
    calc _ = C * ((i.g ^ 2 + |1 - i.t|)⁻¹ * (zdistD d i.L r : ℝ) ^ 2 * (((zdistD d i.L a : ℝ) + 1) ^ d)⁻¹) := by
          ring
      _ ≤ _ := key.trans (le_of_eq (by ring))
  · obtain ⟨C, hC, H⟩ := baProp8_holds d Λ κ hd hΛ hκ
    refine ⟨C, hC, fun i s s' _ a => ?_⟩
    have h := H i.L i.hL i.g i.hg i.hgΛ i.E i.m i.hr i.t i.ht0 i.ht1 s s' a
    have e : BATheta0 d i.L i.g i.E i.m i.t s s' 0 a
        = BATheta d i.L i.g i.E i.m i.t s s' 0 a
          - ((i.L : ℂ) ^ (2 * d))⁻¹ * ∑ a', ∑ b', BATheta d i.L i.g i.E i.m i.t s s' a' b' := rfl
    rw [e] at h
    have h0 : 0 ≤ (i.g ^ 2 + |1 - i.t|)⁻¹ * (((zdistD d i.L a : ℝ) + 1) ^ (d - 2))⁻¹ := by positivity
    have key := KStep_mul_loss hC.le h0 (KStep_one_le_rpow i.hL hτ)
    refine h.trans ?_
    calc _ = C * ((i.g ^ 2 + |1 - i.t|)⁻¹ * (((zdistD d i.L a : ℝ) + 1) ^ (d - 2))⁻¹) := by ring
      _ ≤ _ := key.trans (le_of_eq (by ring))
  · intro i s s' _ a
    exact KStep_theta_row_le i.hr i.ht0 i.ht1 s s' a

/-- **`(eq:ind-step-bound)` at BA is proved** (K09a's `indStepAbs_of` at the BA data): `IndStepAbs` for the molecule weight `BASig`, the edges
`Θ` of the BA data and `Bp = B_{t,0}`, at the family `KWardIneq_Data d Λ κ` of the real-axis data, every `k ≥ 3`.  The inputs are the
molecule decay `baSig_decay` (K07), the sum-zero interface `baSig_sumZeroAbs` (K08b, `3 ≤ k`, `t < 1`) and the leaf bundle `KStep_indStepTH`.
Its image under `KWardIneq_IndAt_of_abs` is the premise of `baWardIneq_holds` (K11, consumed by K12). -/
theorem KStep_baIndStepAbs_holds {d : ℕ} (k : ℕ) [NeZero k] (hd : 3 ≤ d) (hk : 3 ≤ k) {Λ κ : ℝ} (hΛ : 0 < Λ) (hκ : 0 < κ) :
    IndStepAbs (ι := KWardIneq_Data d Λ κ) d k (fun i => i.L) (fun i => Bparam d i.L i.g i.t 0)
      (BASig (ι := KWardIneq_Data d Λ κ) d k (fun i => i.L) (fun i => i.g) (fun i => i.E) (fun i => i.m)
        (fun i => i.t))
      (fun i s s' => BAThetaOf (BAMsigma d i.L (BAMB d i.L i.g (i.E : ℂ) i.m)) i.t s s') :=
  indStepAbs_of d k Λ (fun i : KWardIneq_Data d Λ κ => i.L) (fun i => i.g) (fun i => i.t) _ _ hd hk
    (fun i => ⟨i.hL, i.hg, i.hgΛ, i.ht0, i.ht1⟩) (KStep_indStepTH hd hΛ hκ)
    (baSig_decay hd hk hΛ hκ (fun i : KWardIneq_Data d Λ κ => i.L) (fun i => i.g) (fun i => i.E) (fun i => i.m)
      (fun i => i.t) (fun i => i.hL) (fun i => i.hg) (fun i => i.hgΛ) (fun i => i.hr) (fun i => i.ht0)
      (fun i => i.ht1.le))
    (baSig_sumZeroAbs hd hk hΛ hκ (fun i : KWardIneq_Data d Λ κ => i.L) (fun i => i.g) (fun i => i.E)
      (fun i => i.m) (fun i => i.t) (fun i => i.hL) (fun i => i.hg) (fun i => i.hgΛ) (fun i => i.hr)
      (fun i => i.ht0) (fun i => i.ht1))

end Bundle

/-! ## 4. The layer `π = ∅` at BA (D3) -/

section Empty

/-- `‖∑_b T(b) X(b)‖ ≤ C_b C_s` when `‖T b‖ ≤ C_b` and `∑_b ‖X b‖ ≤ C_s` (a long root leaf in sup norm times the root sum). -/
private theorem KStep_long_root {G : Type*} [Fintype G] (T X : G → ℂ) {Cb Cs : ℝ} (hCb : 0 ≤ Cb)
    (hT : ∀ b, ‖T b‖ ≤ Cb) (hX : ∑ b, ‖X b‖ ≤ Cs) : ‖∑ b, T b * X b‖ ≤ Cb * Cs := by
  calc ‖∑ b, T b * X b‖ ≤ ∑ b, ‖T b‖ * ‖X b‖ := by
        refine (norm_sum_le _ _).trans (le_of_eq ?_)
        simp only [norm_mul]
    _ ≤ ∑ b, Cb * ‖X b‖ := Finset.sum_le_sum fun b _ => mul_le_mul_of_nonneg_right (hT b) (norm_nonneg _)
    _ = Cb * ∑ b, ‖X b‖ := by rw [Finset.mul_sum]
    _ ≤ Cb * Cs := mul_le_mul_of_nonneg_left hX hCb

/-- **D3: the layer `π = ∅` at BA** (the BA twin of `KLInduct_Kpi_empty_bound`, `Loop/KLInduct.lean:833`): `|K^{(∅)}_{t,σ,a}| ≤ C L^τ B_{t,0}^{n-1}`, for every
`n ≥ 3`, uniformly in `L ≥ 3`, `g ∈ (0, Λ]`, the real-axis data `BAReal d L g κ E m` and `t ∈ [0,1)`; `C` depends on `(d, n, Λ, κ, τ)` only.  The
merged bound `|K^{(∅)}| ≤ C_Σ S^n` (`baKpi_empty_short`) alone does not suffice: a long leaf has `ℓ¹` norm `≤ (1-t)⁻¹` only, which exceeds `B` by the
factor `(g² + |1-t|)/(1-t)`.  If every charge is equal to the next one, `|Σ^{(∅)}| ≤ C_Σ` (`baWardMol_holds`, `(eq:molecule-decay)`) and the `ℓ¹`
bound of property 5' (`KStep_theta_l1`) give `C_Σ S^n ≤ C_Σ S^n (1+Λ²)^{n-1} B^{n-1}` because `(1+Λ²) B ≥ 1`; otherwise a long leaf `Θ_t^{(+,-)}` is
bounded in sup norm by `C_d B` (property 5, `KStep_theta_sup`) and the root sum is `KStep_baIndStepAbs_holds`, `≺ B^{n-2}`
(`baKpi_empty_slice`). -/
theorem baKpi_empty_bound {d : ℕ} (n : ℕ) [NeZero n] (hd : 3 ≤ d) (hn : 3 ≤ n) {Λ κ : ℝ} (hΛ : 0 < Λ) (hκ : 0 < κ)
    (τ : ℝ) (hτ : 0 < τ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → g ≤ Λ → ∀ (E : ℝ) (m : ℂ),
      haveI : NeZero L := ⟨by omega⟩
      BAReal d L g κ E m → ∀ t : ℝ, 0 ≤ t → t < 1 → ∀ (σ : Fin n → Bool) (a : Fin n → Zd d L),
        ‖BAKpi d L n (BAMsigma d L (BAMB d L g (E : ℂ) m)) t σ a ∅‖
          ≤ C * (L : ℝ) ^ τ * (Bparam d L g t 0) ^ (n - 1) := by
  obtain ⟨Cm, hCm, c, hc, hmol⟩ := baWardMol_holds hd hn hΛ hκ
  obtain ⟨Cd, hCd, hTh⟩ := KStep_theta_sup hd hΛ hκ
  obtain ⟨Ci, hCi, hind⟩ := KStep_baIndStepAbs_holds n hd hn hΛ hκ τ hτ
  obtain ⟨k, rfl⟩ : ∃ k, d = k + 2 := ⟨d - 2, by omega⟩
  obtain ⟨S, hS0, hS⟩ := KStep_theta_l1 hd hΛ hκ
  refine ⟨Cm * S ^ n * (1 + Λ ^ 2) ^ (n - 1) + Cd * Ci, by positivity, ?_⟩
  intro L hL g hg hgΛ E m
  have : NeZero L := ⟨by omega⟩
  intro hr t ht0 ht1 σ a
  have hB0 : 0 ≤ Bparam (k + 2) L g t 0 := KLIndStepA_Bparam_nonneg _ _
  have hL1 := KStep_one_le_rpow hL hτ
  have hLτ0 : 0 ≤ (L : ℝ) ^ τ := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hBn : 0 ≤ (Bparam (k + 2) L g t 0) ^ (n - 1) := pow_nonneg hB0 _
  have hextra : 0 ≤ Cd * Ci * (L : ℝ) ^ τ * (Bparam (k + 2) L g t 0) ^ (n - 1) := by positivity
  by_cases hσ : ∀ v, σ v = σ (v + 1)
  · -- equal charges: the molecule is bounded and every leaf is short
    have hcm : ∀ δ, ‖BASigmaPi (k + 2) L n (BAMsigma (k + 2) L (BAMB (k + 2) L g (E : ℂ) m)) t σ ∅ δ‖ ≤ Cm := by
      intro δ
      refine (hmol L hL g hg hgΛ E m hr t ht0 ht1 σ δ).trans ?_
      have h1 : Real.exp (-(c * (KLmaxDist (k + 2) L δ : ℝ))) ≤ 1 :=
        Real.exp_le_one_iff.2 (by
          have : 0 ≤ c * (KLmaxDist (k + 2) L δ : ℝ) := by positivity
          linarith)
      calc Cm * Real.exp (-(c * (KLmaxDist (k + 2) L δ : ℝ))) ≤ Cm * 1 := mul_le_mul_of_nonneg_left h1 hCm.le
        _ = Cm := mul_one _
    have hS' : ∀ (v : Fin n) (x : Zd (k + 2) L),
        ∑ b, ‖BAThetaOf (BAMsigma (k + 2) L (BAMB (k + 2) L g (E : ℂ) m)) t (σ v) (σ (v + 1)) x b‖ ≤ S := by
      intro v x
      rw [← hσ v]
      exact hS L hL g hg hgΛ E m hr t ht0 ht1 (σ v) x
    have h1 := baKpi_empty_short (BAMsigma (k + 2) L (BAMB (k + 2) L g (E : ℂ) m)) t σ a hcm hS'
    -- `(1 + Λ²) B ≥ 1`: `B ≥ (g² + |1-t|)⁻¹ ≥ (1 + Λ²)⁻¹`
    have hden : g ^ 2 + |1 - t| ≤ 1 + Λ ^ 2 := by
      have h1 : g ^ 2 ≤ Λ ^ 2 := pow_le_pow_left₀ hg.le hgΛ 2
      have h2 : |1 - t| ≤ 1 := by
        rw [abs_of_pos (by linarith)]; linarith
      linarith
    have hden0 : 0 < g ^ 2 + |1 - t| := by positivity
    have hinv : (1 + Λ ^ 2)⁻¹ ≤ Bparam (k + 2) L g t 0 :=
      (inv_anti₀ hden0 hden).trans (KLlat_inv_le_Bparam t)
    have hAB : 1 ≤ (1 + Λ ^ 2) * Bparam (k + 2) L g t 0 := by
      have h1pos : (0 : ℝ) < 1 + Λ ^ 2 := by positivity
      calc (1 : ℝ) = (1 + Λ ^ 2) * (1 + Λ ^ 2)⁻¹ := (mul_inv_cancel₀ h1pos.ne').symm
        _ ≤ (1 + Λ ^ 2) * Bparam (k + 2) L g t 0 := mul_le_mul_of_nonneg_left hinv h1pos.le
    have hpow : 1 ≤ (1 + Λ ^ 2) ^ (n - 1) * (Bparam (k + 2) L g t 0) ^ (n - 1) := by
      rw [← mul_pow]; exact one_le_pow₀ hAB
    have hCS : 0 ≤ Cm * S ^ n := by positivity
    calc ‖BAKpi (k + 2) L n (BAMsigma (k + 2) L (BAMB (k + 2) L g (E : ℂ) m)) t σ a ∅‖ ≤ Cm * S ^ n := h1
      _ = (Cm * S ^ n) * 1 * 1 := by ring
      _ ≤ (Cm * S ^ n) * ((1 + Λ ^ 2) ^ (n - 1) * (Bparam (k + 2) L g t 0) ^ (n - 1)) * (L : ℝ) ^ τ := by
          gcongr
      _ = Cm * S ^ n * (1 + Λ ^ 2) ^ (n - 1) * (L : ℝ) ^ τ * (Bparam (k + 2) L g t 0) ^ (n - 1) := by ring
      _ ≤ (Cm * S ^ n * (1 + Λ ^ 2) ^ (n - 1) + Cd * Ci) * (L : ℝ) ^ τ * (Bparam (k + 2) L g t 0) ^ (n - 1) := by
          nlinarith [hextra]
  · -- a long leaf: `Θ_t` in sup norm times the root sum
    obtain ⟨r, hrσ⟩ := not_forall.1 hσ
    have hlong : ∀ b : Zd (k + 2) L,
        ‖BAThetaOf (BAMsigma (k + 2) L (BAMB (k + 2) L g (E : ℂ) m)) t (σ r) (σ (r + 1)) (a r) b‖
          ≤ Cd * Bparam (k + 2) L g t 0 := fun b =>
      hTh L hL g hg hgΛ E m hr t ht0 ht1 (σ r) (σ (r + 1)) (a r) b
    have hroot := hind ⟨L, hL, g, hg, hgΛ, E, m, hr, t, ht0, ht1⟩ σ r hrσ a
    rw [baKpi_empty_slice (BAMsigma (k + 2) L (BAMB (k + 2) L g (E : ℂ) m)) t σ a r]
    calc _ ≤ (Cd * Bparam (k + 2) L g t 0) * (Ci * (L : ℝ) ^ τ * (Bparam (k + 2) L g t 0) ^ (n - 2)) :=
          KStep_long_root _ _ (by positivity) hlong hroot
      _ = Cd * Ci * (L : ℝ) ^ τ * (Bparam (k + 2) L g t 0) ^ (n - 1) := by
          have : n - 1 = (n - 2) + 1 := by omega
          rw [this, pow_succ]; ring
      _ ≤ (Cm * S ^ n * (1 + Λ ^ 2) ^ (n - 1) + Cd * Ci) * (L : ℝ) ^ τ * (Bparam (k + 2) L g t 0) ^ (n - 1) := by
          have : 0 ≤ Cm * S ^ n * (1 + Λ ^ 2) ^ (n - 1) * (L : ℝ) ^ τ * (Bparam (k + 2) L g t 0) ^ (n - 1) := by
            positivity
          nlinarith [this]

end Empty

/-! ## 5. `(eq:K-pi-bound)` at BA for every `n ≥ 3` -/

section Main

/-- **The abstract bound `KStepAt` at the BA data, every `n ≥ 3`**: the abstract induction `KStep_all` at the family `KWardIneq_Data d Λ κ`, the
molecule weight `BASig`, the edges `Θ` of the BA data and `Kp = BAKpi`.  The inputs are the merged theorems:
* layer `∅`: `baKpi_empty_bound` (D3, from K10's `baKpi_empty_slice`, `baKpi_empty_short`);
* the cut: `baKpi_cut_abs` (K10); a layer with no tree is `0` (`BAKpi` is a sum over `KLTSPlong`);
* the inner root sum: `KStep_baIndStepAbs_holds` (K09a `indStepAbs_of` with K08b `baSig_sumZeroAbs`, K07 `baSig_decay`, the leaf bundle);
* the glue weight is the real `t ∈ [0,1)`. -/
private theorem KStep_BA_all (d : ℕ) {Λ κ : ℝ} (hd : 3 ≤ d) (hΛ : 0 < Λ) (hκ : 0 < κ) :
    ∀ (n : ℕ) [NeZero n], 3 ≤ n →
      KStepAt (ι := KWardIneq_Data d Λ κ) d (fun i => i.L) (fun i => Bparam d i.L i.g i.t 0)
        (fun k _ i σ a π => BAKpi d i.L k (BAMsigma d i.L (BAMB d i.L i.g (i.E : ℂ) i.m)) i.t σ a π) n :=
  KStep_all (ι := KWardIneq_Data d Λ κ) d (fun i => i.L) (fun i => Bparam d i.L i.g i.t 0) (fun i => i.t)
    (fun k _ i σ δ => BASig (ι := KWardIneq_Data d Λ κ) d k (fun i => i.L) (fun i => i.g) (fun i => i.E)
      (fun i => i.m) (fun i => i.t) i σ δ)
    (fun i s s' => BAThetaOf (BAMsigma d i.L (BAMB d i.L i.g (i.E : ℂ) i.m)) i.t s s')
    (fun k _ i σ a π => BAKpi d i.L k (BAMsigma d i.L (BAMB d i.L i.g (i.E : ℂ) i.m)) i.t σ a π)
    (fun i => KLIndStepA_Bparam_nonneg _ _)
    (fun i => by rw [Complex.norm_real, Real.norm_of_nonneg i.ht0]; exact i.ht1.le)
    (fun k _ hk τ hτ => by
      obtain ⟨C, hC, H⟩ := baKpi_empty_bound k hd hk hΛ hκ τ hτ
      exact ⟨C, hC, fun i σ a => H i.L i.hL i.g i.hg i.hgΛ i.E i.m i.hr i.t i.ht0 i.ht1 σ a⟩)
    (fun k _ hk i σ π a h => by
      show BAKpi d i.L k _ i.t σ a π = 0
      unfold BAKpi
      rw [h, Finset.sum_empty])
    (fun k _ hk i σ F₀ hF₀ π hπ J hJ hinner a =>
      baKpi_cut_abs (ι := KWardIneq_Data d Λ κ) d (fun i => i.L) (fun i => i.g) (fun i => i.E) (fun i => i.m)
        (fun i => i.t) i hk σ hF₀ hπ hJ hinner a)
    (fun k _ hk => KStep_baIndStepAbs_holds k hd hk hΛ hκ)

/-- **`(eq:K-pi-bound)` is proved at BA** (`BAKpiBoundAt`, `BA/KInduct.lean:66`) for every `n ≥ 3`, every `π`, uniformly in `L ≥ 3`,
`g ∈ (0, Λ]`, the real-axis data `BAReal d L g κ E m` and `t ∈ [0,1)`: `|K^{(π)}_{t,σ,a}| ≤ C L^τ B_{t,0}^{n-1}`, `C` depending on `(d, n, Λ, κ, τ)` only.
The abstract induction `KStep_all` at `BAKpi`, `BASig`, `Θ` (`KStep_BA_all`).  The Ward inequality `baWardIneq_holds` (K11) is not an input of the
step (the band step `KLKpi_step` does not use `KLWardIneq` either): it consumes `IndStepAbs` (`KWardIneq_IndAt_of_abs` of `KStep_baIndStepAbs_holds`). -/
theorem baKpiBoundAt_holds (d n : ℕ) [NeZero n] {Λ κ : ℝ} (hd : 3 ≤ d) (hn : 3 ≤ n) (hΛ : 0 < Λ) (hκ : 0 < κ) :
    BAKpiBoundAt d n Λ κ := by
  intro τ hτ
  obtain ⟨C, hC, H⟩ := KStep_BA_all d hd hΛ hκ n hn τ hτ
  exact ⟨C, hC, fun L hL g hg hgΛ E m hr t ht0 ht1 σ π a =>
    H ⟨L, hL, g, hg, hgΛ, E, m, hr, t, ht0, ht1⟩ σ π a⟩

end Main

/-! ## 6. Compiled nonempty instances

Datum: the merged flow point `P` of `(d, L) = (3, 4)` (`BA/MFixedPoint.lean:893`; `P.real : BAReal 3 4 P.g0 P.m0.im P.E P.m0`,
`0 < P.g0 ≤ 10`), `Λ = 10`, `κ = Im m₀ > 0`, `t = 1/2`, `τ = 1`, distinct labels of `Z_4^3`.  `TSP 4 = {∅, {(0,2)}, {(1,3)}}`.  With the alternating
`σ = KLsigAlt 4 = (+,-,+,-)` both diagonals are short, so every layer `π ≠ ∅` has no tree and `K^{(π)} = 0`: that datum is used for the layer `∅`
(three trees) and the layer `{(0,2)}` is shown empty.  The layer `π = {(0,2)}` with a tree is at `σ = (+,+,-,+)` (the cut: an inner and an outer triangle);
at `n = 5` the layer `{(0,2),(2,4)}` of `σ = (+,+,-,+,+)` (an inner triangle and an outer quadrilateral).  No hypothesis of another gate remains: every
hypothesis of `KStep_step`, `KStep_all`, `baKpi_empty_bound`, `KStep_baIndStepAbs_holds`, `baKpiBoundAt_holds` is discharged at the data. -/

namespace KStepInst

open RBM.BA.MFixedPointInst

/-- The layer `{(0,2)}` of `σ = (+,+,-,+)` has the tree `{(0,2)}` (`n = 4`). -/
private theorem KStep_layer4 :
    ({((0 : Fin 4), (2 : Fin 4))} : Finset (Fin 4 × Fin 4)) ∈
      KLTSPlong 4 ![true, true, false, true] {((0 : Fin 4), (2 : Fin 4))} := by decide

/-- The layer `{(0,2),(2,4)}` of `σ = (+,+,-,+,+)` has the tree `{(0,2),(2,4)}` (`n = 5`). -/
private theorem KStep_layer5 :
    ({((0 : Fin 5), (2 : Fin 5)), ((2 : Fin 5), (4 : Fin 5))} : Finset (Fin 5 × Fin 5)) ∈
      KLTSPlong 5 ![true, true, false, true, true] {((0 : Fin 5), (2 : Fin 5)), ((2 : Fin 5), (4 : Fin 5))} := by decide

/-- **Alternating charges** (`σ = KLsigAlt 4`): three trees in the layer `∅`, none in the layer `{(0,2)}` (both diagonals are short). -/
example : (KLTSPlong 4 (KLsigAlt 4) ∅).card = 3 ∧ KLTSPlong 4 (KLsigAlt 4) {((0 : Fin 4), (2 : Fin 4))} = ∅ := by
  decide

/-- **`baKpiBoundAt_holds`** at the flow point, `n = 4`, `σ = KLsigAlt 4`, `π = ∅` (three trees), `t = 1/2`, `τ = 1`. -/
example : (KLTSPlong 4 (KLsigAlt 4) ∅).Nonempty ∧ ∃ C : ℝ, 0 < C ∧
    ‖BAKpi 3 4 4 (BAMsigma 3 4 (BAMB 3 4 P.g0 (P.E : ℂ) P.m0)) (1 / 2) (KLsigAlt 4)
        ![![0, 0, 0], ![1, 0, 0], ![2, 0, 0], ![3, 0, 0]] ∅‖
      ≤ C * (4 : ℝ) ^ (1 : ℝ) * (Bparam 3 4 P.g0 (1 / 2) 0) ^ (4 - 1) := by
  refine ⟨Finset.card_pos.1 (by decide), ?_⟩
  obtain ⟨C, hC, H⟩ := baKpiBoundAt_holds 3 4 (Λ := 10) (κ := P.m0.im) le_rfl (by norm_num) (by norm_num)
    P.real.1.1 1 one_pos
  exact ⟨C, hC, H 4 (by norm_num) P.g0 P.g0_pos P.g0_le P.E P.m0 P.real (1 / 2) (by norm_num) (by norm_num) _ _ _⟩

/-- **`baKpiBoundAt_holds`** at the flow point, `n = 4`, `σ = (+,+,-,+)`, the layer `π = {(0,2)}` with a tree (the cut), `t = 1/2`, `τ = 1`. -/
example : (KLTSPlong 4 ![true, true, false, true] {((0 : Fin 4), (2 : Fin 4))}).Nonempty ∧ ∃ C : ℝ, 0 < C ∧
    ‖BAKpi 3 4 4 (BAMsigma 3 4 (BAMB 3 4 P.g0 (P.E : ℂ) P.m0)) (1 / 2) ![true, true, false, true]
        ![![0, 0, 0], ![1, 0, 0], ![2, 0, 0], ![3, 0, 0]] {((0 : Fin 4), (2 : Fin 4))}‖
      ≤ C * (4 : ℝ) ^ (1 : ℝ) * (Bparam 3 4 P.g0 (1 / 2) 0) ^ (4 - 1) := by
  refine ⟨⟨_, KStep_layer4⟩, ?_⟩
  obtain ⟨C, hC, H⟩ := baKpiBoundAt_holds 3 4 (Λ := 10) (κ := P.m0.im) le_rfl (by norm_num) (by norm_num)
    P.real.1.1 1 one_pos
  exact ⟨C, hC, H 4 (by norm_num) P.g0 P.g0_pos P.g0_le P.E P.m0 P.real (1 / 2) (by norm_num) (by norm_num) _ _ _⟩

/-- **`baKpiBoundAt_holds`** at the flow point, `n = 5`, `σ = (+,+,-,+,+)`, the two-edge layer `π = {(0,2),(2,4)}`, `t = 1/2`, `τ = 1`. -/
example : (KLTSPlong 5 ![true, true, false, true, true]
      {((0 : Fin 5), (2 : Fin 5)), ((2 : Fin 5), (4 : Fin 5))}).Nonempty ∧ ∃ C : ℝ, 0 < C ∧
    ‖BAKpi 3 4 5 (BAMsigma 3 4 (BAMB 3 4 P.g0 (P.E : ℂ) P.m0)) (1 / 2) ![true, true, false, true, true]
        ![![0, 0, 0], ![1, 0, 0], ![2, 0, 0], ![3, 0, 0], ![0, 1, 0]]
        {((0 : Fin 5), (2 : Fin 5)), ((2 : Fin 5), (4 : Fin 5))}‖
      ≤ C * (4 : ℝ) ^ (1 : ℝ) * (Bparam 3 4 P.g0 (1 / 2) 0) ^ (5 - 1) := by
  refine ⟨⟨_, KStep_layer5⟩, ?_⟩
  obtain ⟨C, hC, H⟩ := baKpiBoundAt_holds 3 5 (Λ := 10) (κ := P.m0.im) le_rfl (by norm_num) (by norm_num)
    P.real.1.1 1 one_pos
  exact ⟨C, hC, H 4 (by norm_num) P.g0 P.g0_pos P.g0_le P.E P.m0 P.real (1 / 2) (by norm_num) (by norm_num) _ _ _⟩

/-- **`baKpiBoundAt_holds`** at the base `n = 3` of the induction: `σ = (+,-,+)`, `π = ∅` (`TSP 3 = {∅}`), `t = 1/2`, `τ = 1`. -/
example : (KLTSPlong 3 ![true, false, true] ∅).Nonempty ∧ ∃ C : ℝ, 0 < C ∧
    ‖BAKpi 3 4 3 (BAMsigma 3 4 (BAMB 3 4 P.g0 (P.E : ℂ) P.m0)) (1 / 2) ![true, false, true]
        ![![0, 0, 0], ![1, 0, 0], ![2, 1, 0]] ∅‖
      ≤ C * (4 : ℝ) ^ (1 : ℝ) * (Bparam 3 4 P.g0 (1 / 2) 0) ^ (3 - 1) := by
  refine ⟨Finset.card_pos.1 (by decide), ?_⟩
  obtain ⟨C, hC, H⟩ := baKpiBoundAt_holds 3 3 (Λ := 10) (κ := P.m0.im) le_rfl (by norm_num) (by norm_num)
    P.real.1.1 1 one_pos
  exact ⟨C, hC, H 4 (by norm_num) P.g0 P.g0_pos P.g0_le P.E P.m0 P.real (1 / 2) (by norm_num) (by norm_num) _ _ _⟩

/-- **D3 `baKpi_empty_bound`** at the flow point, `n = 4`, mixed charges `σ = (+,+,-,+)` (a long root leaf), `t = 1/2`, `τ = 1`. -/
example : ∃ C : ℝ, 0 < C ∧
    ‖BAKpi 3 4 4 (BAMsigma 3 4 (BAMB 3 4 P.g0 (P.E : ℂ) P.m0)) (1 / 2) ![true, true, false, true]
        ![![0, 0, 0], ![1, 0, 0], ![2, 0, 0], ![3, 0, 0]] ∅‖
      ≤ C * (4 : ℝ) ^ (1 : ℝ) * (Bparam 3 4 P.g0 (1 / 2) 0) ^ (4 - 1) := by
  obtain ⟨C, hC, H⟩ := baKpi_empty_bound 4 (d := 3) (Λ := 10) (κ := P.m0.im) le_rfl (by norm_num) (by norm_num)
    P.real.1.1 1 one_pos
  exact ⟨C, hC, H 4 (by norm_num) P.g0 P.g0_pos P.g0_le P.E P.m0 P.real (1 / 2) (by norm_num) (by norm_num) _ _⟩

/-- **D3** at the same data with all charges equal (every leaf short; the branch `C_Σ S^n (1+Λ²)^{n-1} B^{n-1}`). -/
example : ∃ C : ℝ, 0 < C ∧
    ‖BAKpi 3 4 4 (BAMsigma 3 4 (BAMB 3 4 P.g0 (P.E : ℂ) P.m0)) (1 / 2) (fun _ => true)
        ![![0, 0, 0], ![1, 0, 0], ![2, 0, 0], ![3, 0, 0]] ∅‖
      ≤ C * (4 : ℝ) ^ (1 : ℝ) * (Bparam 3 4 P.g0 (1 / 2) 0) ^ (4 - 1) := by
  obtain ⟨C, hC, H⟩ := baKpi_empty_bound 4 (d := 3) (Λ := 10) (κ := P.m0.im) le_rfl (by norm_num) (by norm_num)
    P.real.1.1 1 one_pos
  exact ⟨C, hC, H 4 (by norm_num) P.g0 P.g0_pos P.g0_le P.E P.m0 P.real (1 / 2) (by norm_num) (by norm_num) _ _⟩

/-- **`KStep_baIndStepAbs_holds`** at the family of the flow point (`n = 4`, root `r = 1` of `σ = (+,+,-,+)`: `σ_1 ≠ σ_2`), `τ = 1`. -/
example : ∃ C : ℝ, 0 < C ∧
    ∑ b : Zd 3 4, ‖∑ δ ∈ Finset.univ.filter (fun δ : Fin 4 → Zd 3 4 => δ 1 = b),
        BASigmaPi 3 4 4 (BAMsigma 3 4 (BAMB 3 4 P.g0 (P.E : ℂ) P.m0)) (1 / 2) ![true, true, false, true] ∅ δ *
          ∏ j ∈ Finset.univ.erase (1 : Fin 4),
            BAThetaOf (BAMsigma 3 4 (BAMB 3 4 P.g0 (P.E : ℂ) P.m0)) (1 / 2) (![true, true, false, true] j)
              (![true, true, false, true] (j + 1)) (![![0, 0, 0], ![1, 0, 0], ![2, 0, 0], ![3, 0, 0]] j) (δ j)‖
      ≤ C * (4 : ℝ) ^ (1 : ℝ) * (Bparam 3 4 P.g0 (1 / 2) 0) ^ (4 - 2) := by
  obtain ⟨C, hC, H⟩ := KStep_baIndStepAbs_holds 4 (d := 3) (Λ := 10) (κ := P.m0.im) le_rfl (by norm_num)
    (by norm_num) P.real.1.1 1 one_pos
  exact ⟨C, hC, H ⟨4, by norm_num, P.g0, P.g0_pos, P.g0_le, P.E, P.m0, P.real, 1 / 2, by norm_num, by norm_num⟩
    ![true, true, false, true] 1 (by decide) ![![0, 0, 0], ![1, 0, 0], ![2, 0, 0], ![3, 0, 0]]⟩

/-- **`KStep_step`** (the abstract step) at the BA data of the flow point's family, `n = 4`: every hypothesis is discharged by a merged
theorem (`hempty`: `baKpi_empty_bound`, `hzero`: `BAKpi` is a sum over `KLTSPlong`, `hcut`: `baKpi_cut_abs`, `hind`: `KStep_baIndStepAbs_holds`,
`hout`: the bound at `n'' = 3`, `KStep_BA_all`).  The concrete inequality is at `σ = (+,+,-,+)`, `π = {(0,2)}` (the cut, inner and outer triangles). -/
example : ∃ C : ℝ, 0 < C ∧
    ‖BAKpi 3 4 4 (BAMsigma 3 4 (BAMB 3 4 P.g0 (P.E : ℂ) P.m0)) (1 / 2) ![true, true, false, true]
        ![![0, 0, 0], ![1, 0, 0], ![2, 0, 0], ![3, 0, 0]] {((0 : Fin 4), (2 : Fin 4))}‖
      ≤ C * (4 : ℝ) ^ (1 : ℝ) * (Bparam 3 4 P.g0 (1 / 2) 0) ^ (4 - 1) := by
  have hκ : 0 < P.m0.im := P.real.1.1
  have h := KStep_step (ι := KWardIneq_Data 3 10 P.m0.im) 3 (fun i => i.L) (fun i => Bparam 3 i.L i.g i.t 0) (fun i => i.t)
    (fun k _ i σ δ => BASig (ι := KWardIneq_Data 3 10 P.m0.im) 3 k (fun i => i.L) (fun i => i.g) (fun i => i.E)
      (fun i => i.m) (fun i => i.t) i σ δ)
    (fun i s s' => BAThetaOf (BAMsigma 3 i.L (BAMB 3 i.L i.g (i.E : ℂ) i.m)) i.t s s')
    (fun k _ i σ a π => BAKpi 3 i.L k (BAMsigma 3 i.L (BAMB 3 i.L i.g (i.E : ℂ) i.m)) i.t σ a π)
    4 (by norm_num) (fun i => KLIndStepA_Bparam_nonneg _ _)
    (fun i => by rw [Complex.norm_real, Real.norm_of_nonneg i.ht0]; exact i.ht1.le)
    (fun τ hτ => by
      obtain ⟨C, hC, H⟩ := baKpi_empty_bound 4 (d := 3) (by norm_num) (by norm_num) (by norm_num : (0 : ℝ) < 10) hκ τ hτ
      exact ⟨C, hC, fun i σ a => H i.L i.hL i.g i.hg i.hgΛ i.E i.m i.hr i.t i.ht0 i.ht1 σ a⟩)
    (fun i σ π a h => by
      show BAKpi 3 i.L 4 _ i.t σ a π = 0
      unfold BAKpi
      rw [h, Finset.sum_empty])
    (fun i σ F₀ hF₀ π hπ J hJ hinner a =>
      baKpi_cut_abs (ι := KWardIneq_Data 3 10 P.m0.im) 3 (fun i => i.L) (fun i => i.g) (fun i => i.E) (fun i => i.m)
        (fun i => i.t) i (by norm_num) σ hF₀ hπ hJ hinner a)
    (fun k _ hk _ => KStep_baIndStepAbs_holds k (by norm_num) hk (by norm_num) hκ)
    (fun k _ hk hlt => KStep_BA_all 3 (by norm_num) (by norm_num) hκ k hk)
  obtain ⟨C, hC, H⟩ := h 1 one_pos
  exact ⟨C, hC, H ⟨4, by norm_num, P.g0, P.g0_pos, P.g0_le, P.E, P.m0, P.real, 1 / 2, by norm_num, by norm_num⟩
    ![true, true, false, true] {((0 : Fin 4), (2 : Fin 4))} ![![0, 0, 0], ![1, 0, 0], ![2, 0, 0], ![3, 0, 0]]⟩

/-- **The premise of K11 is discharged**: `baWardIneq_holds` (`BA/KWardIneq.lean:1183`) at the flow point, `n = 4`, with its premises
`KWardIneq_IndAt d k Λ κ` (`k = 3, 4`) from `KStep_baIndStepAbs_holds` through `KWardIneq_IndAt_of_abs`.  The Ward inequality is a consumer of the
induction step, not an input of it. -/
example : BAWardIneqAt 3 4 10 P.m0.im :=
  baWardIneq_holds 3 4 le_rfl (by norm_num) (by norm_num) P.real.1.1
    (fun k hk _ _ => KWardIneq_IndAt_of_abs (KStep_baIndStepAbs_holds k le_rfl hk (by norm_num) P.real.1.1))

end KStepInst

end RBM.BA
