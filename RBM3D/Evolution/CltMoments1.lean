/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Induction.Step5Pins
import RBM3D.Evolution.CltStep
import RBM3D.Evolution.MeanFar
import RBM3D.Defs.Shells
import RBM3D.Defs.RadialSum
import RBM3D.Propagator.Prop5Hold
import RBM3D.Propagator.Prop6Hold

/-!
# S5-23 (ST-4): the deterministic counting half of the CLT moment bound (ticket T2165)

Paper: arXiv:2507.20274, `paper/tex/3_5_Loop_Hierarchy.tex` (`3_5:line`): the cluster decomposition under the pairing
condition `(eq:pairingcond)` (`3_5:2223-2225`), the cluster sums of `(eq:2p_product_pair)` (`3_5:2226-2233`) and
`(eq:simplecalculus)` (`3_5:2234-2241`) of the proof of `lem;CLT`.  Everything here is deterministic at a fixed `n`
(no `Prec`): `S5-24` (`Evolution/CltMoments2`) sums the configurations of `(eq:2p_product)` with the weights below,
splits the sum into the paired part (this file) and the isolated part (`stCltIso_holds`, `Step5Pins.lean:415`), and
`S5-25` (`STCltFar`) assembles.  Notation: `|x| = zdistInf d L x`, `w = (log W)³ ℓ_s` (the window of
`(eq:sumregionsforb)` and of `STCltIsoConcl`, `Step5Pins.lean:418`), `ρ = (log W)⁴ ℓ_s` (the far cutoff of `STfFar`,
`Step5Pins.lean:364`), `R = 10 w` (the pairing radius).  Scales are real parameters; the `lw = log W` form is in section 5.

**Targets** (namespace `RBM.Evol`; constants explicit):
1. Clusters: `CltMom1.Cluster`, `CltMom1.Paired`, `cltMom1_exists_cluster`, `cltMom1_clusters` (every cluster has `≥ 2`
   elements, `r ≤ p` clusters, members within `2R ≤ 2pR` of the representative, `≤ (2p)^{2p}` structures),
   `cltMom1_not_paired_iff`, `cltMom1_iso_hyp_iff` (the complement of `Paired (10 (log W)³ ℓ_s)` is literally the isolation
   hypothesis of `STCltIsoConcl`); the sum machinery `cltMom1_sum_compat`, `cltMom1_paired_sum_le`,
   `cltMom1_clusterSum_le_of_bound` (ports).
2. Weights: `cltMom1_weight_a1` (`g² |Θ_t(a,b)| ≤ C₅(1+2^{d-1})/(|a-b|^{d-2}+1)`, from `prop5Decay_holds` via the public
   `meanFar_T1`; the zero-mode term `(L^d(1-t))⁻¹` is absorbed by the regime `g²/L² ≤ 1-t`), `cltMom1_weight_a2`
   (`g² |Θ_t(b₂,a₂) - Θ_t(b₁,a₂)| ≤ C₆ d w/(|a₂-b₁|^{d-1}+1)`, from `prop6Diff1_holds`, premise `|r| ≤ ½|a|` from `2dw ≤ ρ`).
3. Comparability: `cltMom1_comparable`, `cltMom1_comparable_weights` (factor `2^m ≤ 2^d`, premise `2r ≤ ρ`),
   `cltMom1_scale_comparable` (for `r = 2pR`: `40 p w ≤ ρ` holds when `log W ≥ 40 p`; for `r = 2R`: when `log W ≥ 40`).
4. Per-cluster sum: `cltMom1_cluster_sum`, `cltMom1_cluster_sum_C4` (`≤ (41^d)^m (d 4^d)^{m+1} w^{(d+2)m+2}`),
   `cltMom1_term_le` (the term `∑_β z_β (∑_{β'} z_{β'})^m` of the cluster sum).
5. `(eq:simplecalculus)`: `cltMom1_simplecalculus` (`λ^q ρ^{-((d-1)q-d)}` form, `q ≥ 2`), `cltMom1_simplecalculus_ell`
   (the ticket-literal `ℓ^d/(ℓ^{d-2})^q` form).  `(d-1)q > d` is used exactly in the tail sum
   `∑_{|x|>ρ} (|x|^{d-1}+1)^{-q} ≤ cs 2^{(d-1)q} ρ^{-((d-1)q-d)}` (`cltMom1_tail_sum`); for `q = 1` the exponent is `-1`
   and the sum grows like `L`.
6. Exponent count: `cltMom1_exponent_identity` (`d - (d-2)k + (d+2)(k-1) + 2 = 4k`), `cltMom1_exponent_nat`,
   `cltMom1_exponent_count_eq` / `cltMom1_exponent_count` (the cluster factor is `ℓ^{4k} lw^{d+(13-d)k} ≤ ℓ^{4k} lw^{12k}`),
   `cltMom1_prod_exponent_exact`, and the assembly `cltMom1_clusterSum_le`, `cltMom1_paired_moment_le`:
   `∑_{b paired} ∏_k z(b^{(k)}) ≤ (2p)^{2p} (2cs)^p (C_d M lw^{12})^{2p} (ℓ⁴/(|a₁-a₂|^{d-2}+1))^{2p}`.

**Ports** (read-only source: RBM2D `RBM2D/Evolution/CltMoments.lean` at `c9a24cf`): `CltMoments.Cluster` `:72`,
`cltm_exists_cluster` `:75-148`, `CltMoments.assigned` `:151`, `CltMoments.ball` `:155`, `CltMoments.clusterSum` `:163`,
`cltm_sum_compat` `:168-282`, `cltm_nonfar_sum_le` `:283-328`, `cltm_assigned_pos`, `cltm_sum_assigned`,
`cltm_two_mul_free_le` `:333-377`, `cltm_card_cluster_le` `:379-389`, `cltm_clusterSum_le_of_bound` `:391-410`,
`cltm_clusterSum_nonneg` `:690-694`, with the label `Z2 L` replaced by a two-label index `Fin 2 → Zd d L`, `zdist2`
by `zdistInf` of the first labels, and the separation `3R` by `2R`.  The shell count and the window sum are re-proved
from the private `meanFar_card_shell`, `meanFar_sum_shell` (`Evolution/MeanFar.lean:89-187`; `Defs/Shells` is `ℓ¹`).  The
RBM2D lines `cltm_ball_sum_le`, `cltm_T1`, `cltm_T2`, `cltFw`, `cltm_double_sum` (`d = 2` logarithmic sums) are replaced by
sections 4-7.

**Differences from the paper** (paper-delta candidates, see the prove report): `T2165a` the pairing condition is strict
and the clusters are a `2R`-separated cover with nearest-point assignment, not the components of `|b₁-b₁'| ≤ R`;
`T2165b` the numerator of the weight at `a₂` is the window `w = (log W)³ ℓ_s` (times `C₆ d`), not `ℓ_s`, and
`(eq:simplecalculus)` is proved with the far-cutoff power `ρ^{-((d-1)q-d)}`, which is `≤ ℓ^{-((d-1)q-d)}`;
`T2165c` the powers of `log W` are explicit (`lw^{12 |A|}` per cluster, `lw^{24 p}` in total).
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

namespace RBM.Evol

open RBM RBM.Gauss RBM.Gauss.Sizes

/-! ## 1. Elementary inequalities and lattice sums on `Z_L^d` in the norm `|·|_∞` -/

section Lattice

variable {d L : ℕ} [NeZero L]

private theorem cltMom1_pow_add_one_le {r : ℝ} (hr : 0 ≤ r) (m : ℕ) :
    (r + 1) ^ m ≤ 2 ^ m * (r ^ m + 1) := by
  have h2 : (0 : ℝ) < 2 ^ m := pow_pos two_pos m
  have hrm : 0 ≤ r ^ m := pow_nonneg hr m
  rcases le_total r 1 with h | h
  · calc (r + 1) ^ m ≤ 2 ^ m := pow_le_pow_left₀ (by linarith) (by linarith) m
      _ ≤ 2 ^ m * (r ^ m + 1) := by nlinarith
  · calc (r + 1) ^ m ≤ (2 * r) ^ m := pow_le_pow_left₀ (by linarith) (by linarith) m
      _ = 2 ^ m * r ^ m := mul_pow _ _ _
      _ ≤ 2 ^ m * (r ^ m + 1) := by nlinarith

private theorem cltMom1_pow_add_one_ge {r : ℝ} (hr : 0 ≤ r) {m : ℕ} (hm : m ≠ 0) :
    r ^ m + 1 ≤ (r + 1) ^ m := by
  simpa using pow_add_pow_le hr zero_le_one hm

private theorem cltMom1_zdistInf_le (x : Zd d L) : zdistInf d L x ≤ L :=
  Finset.sup_le fun _ _ => (min_le_right _ _).trans (Nat.sub_le _ _)

private theorem cltMom1_zdistInf_neg (x : Zd d L) : zdistInf d L (-x) = zdistInf d L x := by
  simp only [zdistInf, Pi.neg_apply, zdist_neg]

/-- `|x - y|_∞ = |y - x|_∞` (the far regions of `STfFar` are written `|b₁ - a_i|`, the weights `|a_i - b₁|`). -/
theorem cltMom1_zdistInf_sub_comm (x y : Zd d L) : zdistInf d L (x - y) = zdistInf d L (y - x) := by
  rw [← neg_sub, cltMom1_zdistInf_neg]

private theorem cltMom1_zdistInf_add_le (x y : Zd d L) :
    zdistInf d L (x + y) ≤ zdistInf d L x + zdistInf d L y := by
  refine Finset.sup_le fun i _ => ?_
  change zdist L (x i + y i) ≤ _
  refine (zdist_add_le L (x i) (y i)).trans (add_le_add ?_ ?_)
  · exact Finset.le_sup (f := fun j => zdist L (x j)) (Finset.mem_univ i)
  · exact Finset.le_sup (f := fun j => zdist L (y j)) (Finset.mem_univ i)

/-- The triangle inequality in the form used for the weights: `|x - z|_∞ ≤ |x - y|_∞ + |y - z|_∞`. -/
theorem cltMom1_zdistInf_tri (x y z : Zd d L) :
    zdistInf d L (x - z) ≤ zdistInf d L (x - y) + zdistInf d L (y - z) := by
  have := cltMom1_zdistInf_add_le (x - y) (y - z)
  simpa using this

private theorem cltMom1_zdistInf_zero : zdistInf d L (0 : Zd d L) = 0 := by
  simp [zdistInf]


/-- The shell `{x : |x|_∞ = k}` of `Z_L^d` has at most `d · 2 (2k+1)^{d-1}` points. -/
private theorem cltMom1_card_shell (hd : 1 ≤ d) (k : ℕ) :
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
def CltMom1.cs (d : ℕ) : ℝ := 2 * d * 2 ^ (d - 1)

theorem CltMom1.cs_pos (hd : 1 ≤ d) : 0 < CltMom1.cs d := by
  unfold CltMom1.cs
  have : (0 : ℝ) < d := by exact_mod_cast hd
  positivity

private theorem cltMom1_card_shell_real (hd : 1 ≤ d) (k : ℕ) :
    ((Finset.univ.filter fun x : Zd d L => zdistInf d L x = k).card : ℝ) ≤
      CltMom1.cs d * ((k : ℝ) + 1) ^ (d - 1) := by
  have h := cltMom1_card_shell (d := d) (L := L) hd k
  have h1 : ((Finset.univ.filter fun x : Zd d L => zdistInf d L x = k).card : ℝ) ≤
      ((d * (2 * (2 * k + 1) ^ (d - 1)) : ℕ) : ℝ) := by exact_mod_cast h
  refine h1.trans ?_
  push_cast
  have h2 : (2 * (k : ℝ) + 1) ^ (d - 1) ≤ (2 * ((k : ℝ) + 1)) ^ (d - 1) :=
    pow_le_pow_left₀ (by positivity) (by linarith) _
  rw [mul_pow] at h2
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  unfold CltMom1.cs
  calc (d : ℝ) * (2 * (2 * (k : ℝ) + 1) ^ (d - 1))
      = 2 * d * (2 * (k : ℝ) + 1) ^ (d - 1) := by ring
    _ ≤ 2 * d * (2 ^ (d - 1) * ((k : ℝ) + 1) ^ (d - 1)) := by gcongr
    _ = 2 * d * 2 ^ (d - 1) * ((k : ℝ) + 1) ^ (d - 1) := by ring

/-- Sum over the lattice of a function of `|x|_∞`, by shells. -/
private theorem cltMom1_sum_shell (hd : 1 ≤ d) (F : ℕ → ℝ) (hF : ∀ k, 0 ≤ F k) :
    ∑ x : Zd d L, F (zdistInf d L x) ≤
      ∑ k ∈ Finset.range (L + 1), CltMom1.cs d * ((k : ℝ) + 1) ^ (d - 1) * F k := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.range (L + 1))
    (g := zdistInf d L) (fun x _ => Finset.mem_range.2 (Nat.lt_succ_of_le (cltMom1_zdistInf_le x)))]
  refine Finset.sum_le_sum fun k _ => ?_
  have hk : ∑ x ∈ Finset.univ.filter (fun x : Zd d L => zdistInf d L x = k), F (zdistInf d L x) =
      ((Finset.univ.filter fun x : Zd d L => zdistInf d L x = k).card : ℝ) * F k := by
    rw [Finset.sum_congr rfl (fun x hx => by rw [(Finset.mem_filter.1 hx).2])]
    simp
  rw [hk]
  exact mul_le_mul_of_nonneg_right (cltMom1_card_shell_real hd k) (hF k)


/-- Translation of the summation variable. -/
private theorem cltMom1_sum_sub {M : Type*} [AddCommMonoid M] (f : Zd d L → M) (x : Zd d L) :
    ∑ b : Zd d L, f (b - x) = ∑ b : Zd d L, f b :=
  Fintype.sum_equiv (Equiv.subRight x) _ _ (fun _ => rfl)

/-- Reflection and translation of the summation variable. -/
private theorem cltMom1_sum_sub_left {M : Type*} [AddCommMonoid M] (f : Zd d L → M) (x : Zd d L) :
    ∑ b : Zd d L, f (x - b) = ∑ b : Zd d L, f b :=
  Fintype.sum_equiv (Equiv.subLeft x) _ _ (fun _ => rfl)

/-- The ball `{x : |x|_∞ ≤ R}` has at most `(2R+1)^d` points. -/
private theorem cltMom1_card_ball (R : ℝ) (hR : 0 ≤ R) :
    ((Finset.univ.filter fun x : Zd d L => ((zdistInf d L x : ℕ) : ℝ) ≤ R).card : ℝ) ≤
      (2 * R + 1) ^ d := by
  classical
  set K : ℕ := ⌊R⌋₊ with hK
  set Sle : Finset (ZMod L) := Finset.univ.filter fun u => zdist L u ≤ K with hSle
  have hSle_card : Sle.card ≤ 2 * K + 1 := card_zdist_le_le K
  have hsub : (Finset.univ.filter fun x : Zd d L => ((zdistInf d L x : ℕ) : ℝ) ≤ R) ⊆
      Fintype.piFinset (fun _ : Fin d => Sle) := by
    intro x hx
    have hx' : ((zdistInf d L x : ℕ) : ℝ) ≤ R := (Finset.mem_filter.1 hx).2
    have hxK : zdistInf d L x ≤ K := Nat.le_floor hx'
    rw [Fintype.mem_piFinset]
    intro i
    simp only [hSle, Finset.mem_filter, Finset.mem_univ, true_and]
    exact (Finset.le_sup (f := fun j => zdist L (x j)) (Finset.mem_univ i)).trans hxK
  have h1 : (Finset.univ.filter fun x : Zd d L => ((zdistInf d L x : ℕ) : ℝ) ≤ R).card ≤
      (2 * K + 1) ^ d := by
    refine (Finset.card_le_card hsub).trans ?_
    rw [Fintype.card_piFinset]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    exact Nat.pow_le_pow_left hSle_card d
  have h2 : ((2 * K + 1 : ℕ) : ℝ) ≤ 2 * R + 1 := by
    have : (K : ℝ) ≤ R := Nat.floor_le hR
    push_cast; linarith
  calc ((Finset.univ.filter fun x : Zd d L => ((zdistInf d L x : ℕ) : ℝ) ≤ R).card : ℝ)
      ≤ (((2 * K + 1) ^ d : ℕ) : ℝ) := by exact_mod_cast h1
    _ = ((2 * K + 1 : ℕ) : ℝ) ^ d := by push_cast; ring
    _ ≤ (2 * R + 1) ^ d := pow_le_pow_left₀ (by positivity) h2 d

/-- The profile sum over a window: `∑_{|x|_∞ ≤ w} (|x|_∞^{d-2}+1)^{-1} ≤ cs 2^{d-2} (w+1)²`
(shells `cs (k+1)^{d-1}`, `(k+1)^{d-2} ≤ 2^{d-2} (k^{d-2}+1)`). -/
private theorem cltMom1_window_sum (hd : 3 ≤ d) {w : ℝ} (hw : 0 ≤ w) :
    ∑ x : Zd d L, (if ((zdistInf d L x : ℕ) : ℝ) ≤ w then
        1 / (((zdistInf d L x : ℕ) : ℝ) ^ (d - 2) + 1) else 0) ≤
      CltMom1.cs d * 2 ^ (d - 2) * (w + 1) ^ 2 := by
  classical
  set F : ℕ → ℝ := fun k => if (k : ℝ) ≤ w then 1 / ((k : ℝ) ^ (d - 2) + 1) else 0 with hF
  have hF0 : ∀ k, 0 ≤ F k := fun k => by simp only [hF]; split_ifs <;> positivity
  have hcs := CltMom1.cs_pos (d := d) (by omega)
  refine (cltMom1_sum_shell (d := d) (L := L) (by omega) F hF0).trans ?_
  have hterm : ∀ k ∈ Finset.range (L + 1),
      CltMom1.cs d * ((k : ℝ) + 1) ^ (d - 1) * F k ≤
        if (k : ℝ) ≤ w then CltMom1.cs d * 2 ^ (d - 2) * (w + 1) else 0 := by
    intro k _
    by_cases hk : (k : ℝ) ≤ w
    · simp only [hF, hk, ↓reduceIte]
      have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      have hden : (0 : ℝ) < (k : ℝ) ^ (d - 2) + 1 := by positivity
      have e : ((k : ℝ) + 1) ^ (d - 1) = ((k : ℝ) + 1) ^ (d - 2) * ((k : ℝ) + 1) := by
        rw [← pow_succ, show d - 2 + 1 = d - 1 by omega]
      have hp := cltMom1_pow_add_one_le hk0 (d - 2)
      have h1 : ((k : ℝ) + 1) ^ (d - 1) * (1 / ((k : ℝ) ^ (d - 2) + 1)) ≤
          2 ^ (d - 2) * ((k : ℝ) + 1) := by
        rw [e, mul_one_div, div_le_iff₀ hden]
        calc ((k : ℝ) + 1) ^ (d - 2) * ((k : ℝ) + 1)
            ≤ 2 ^ (d - 2) * ((k : ℝ) ^ (d - 2) + 1) * ((k : ℝ) + 1) :=
              mul_le_mul_of_nonneg_right hp (by positivity)
          _ = 2 ^ (d - 2) * ((k : ℝ) + 1) * ((k : ℝ) ^ (d - 2) + 1) := by ring
      calc CltMom1.cs d * ((k : ℝ) + 1) ^ (d - 1) * (1 / ((k : ℝ) ^ (d - 2) + 1))
          = CltMom1.cs d * (((k : ℝ) + 1) ^ (d - 1) * (1 / ((k : ℝ) ^ (d - 2) + 1))) := by ring
        _ ≤ CltMom1.cs d * (2 ^ (d - 2) * ((k : ℝ) + 1)) := mul_le_mul_of_nonneg_left h1 hcs.le
        _ ≤ CltMom1.cs d * (2 ^ (d - 2) * (w + 1)) := by gcongr
        _ = _ := by ring
    · simp [hF, hk]
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.sum_filter]
  have hsub : (Finset.range (L + 1)).filter (fun k : ℕ => (k : ℝ) ≤ w) ⊆
      Finset.range (⌊w⌋₊ + 1) := by
    intro k hk
    have hk' : (k : ℝ) ≤ w := (Finset.mem_filter.1 hk).2
    exact Finset.mem_range.2 (Nat.lt_succ_of_le (Nat.le_floor hk'))
  have hcard : (((Finset.range (L + 1)).filter (fun k : ℕ => (k : ℝ) ≤ w)).card : ℝ) ≤ w + 1 := by
    have h1 := Finset.card_le_card hsub
    rw [Finset.card_range] at h1
    have h2 : ((⌊w⌋₊ : ℕ) : ℝ) ≤ w := Nat.floor_le hw
    have h3 : (((⌊w⌋₊ + 1 : ℕ)) : ℝ) ≥ ((Finset.filter (fun k : ℕ => (k : ℝ) ≤ w) (Finset.range (L + 1))).card : ℝ) := by
      exact_mod_cast h1
    push_cast at h3
    linarith
  rw [Finset.sum_const, nsmul_eq_mul]
  calc _ ≤ (w + 1) * (CltMom1.cs d * 2 ^ (d - 2) * (w + 1)) :=
        mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = CltMom1.cs d * 2 ^ (d - 2) * (w + 1) ^ 2 := by ring

/-- The tail of `∑ (k+1)^{-2}` over `k > ρ`: telescoping `(k+1)^{-2} ≤ k^{-1} - (k+1)^{-1}`. -/
private theorem cltMom1_tail_inv_sq {ρ : ℝ} (hρ : 0 < ρ) (N : ℕ) :
    ∑ k ∈ Finset.range N, (if ρ < (k : ℝ) then 1 / ((k : ℝ) + 1) ^ 2 else 0) ≤ 1 / ρ := by
  set m : ℕ := ⌊ρ⌋₊ + 1 with hm
  have hmρ : ρ < (m : ℝ) := by rw [hm]; push_cast; exact Nat.lt_floor_add_one ρ
  have hm1 : (1 : ℝ) ≤ m := by rw [hm]; push_cast; linarith [Nat.cast_nonneg (α := ℝ) ⌊ρ⌋₊]
  have hm0 : (0 : ℝ) < m := by linarith
  have key : ∀ N : ℕ, ∑ k ∈ Finset.range N, (if ρ < (k : ℝ) then 1 / ((k : ℝ) + 1) ^ 2 else 0) ≤
      1 / (m : ℝ) - 1 / ((max N m : ℕ) : ℝ) := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.sum_range_succ]
      by_cases h : ρ < (N : ℝ)
      · have hmN : m ≤ N := by
          have : ⌊ρ⌋₊ < N := (Nat.floor_lt hρ.le).2 h
          omega
        have hmaxN : max N m = N := max_eq_left hmN
        have hmax1 : max (N + 1) m = N + 1 := max_eq_left (by omega)
        rw [hmaxN] at ih
        rw [hmax1]
        have hN0 : (0 : ℝ) < N := by
          have : (m : ℝ) ≤ N := by exact_mod_cast hmN
          linarith
        simp only [h, ↓reduceIte]
        push_cast
        have : 1 / ((N : ℝ) + 1) ^ 2 ≤ 1 / (N : ℝ) - 1 / ((N : ℝ) + 1) := by
          rw [div_sub_div _ _ hN0.ne' (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith
        linarith
      · have hNm : N < m := by
          by_contra hc
          push Not at hc
          apply h
          have : ((m : ℕ) : ℝ) ≤ N := by exact_mod_cast hc
          have h2 : ρ < (m : ℝ) := hmρ
          -- N ≥ m > ρ
          linarith
        have hmaxN : max N m = m := max_eq_right hNm.le
        have hmax1 : max (N + 1) m = m := max_eq_right (by omega)
        rw [hmaxN] at ih
        rw [hmax1]
        simp only [h, ↓reduceIte]
        linarith
  refine (key N).trans ?_
  have h1 : 0 ≤ 1 / ((max N m : ℕ) : ℝ) := by positivity
  have h2 : 1 / (m : ℝ) ≤ 1 / ρ := one_div_le_one_div_of_le hρ hmρ.le
  linarith

/-- **The tail sum for `(eq:simplecalculus)`**: for `k ≥ 2`, `d ≥ 3`, `ρ > 0`,
`∑_{|x|_∞ > ρ} (|x|_∞^{d-1}+1)^{-k} ≤ cs 2^{(d-1)k} ρ^{-((d-1)k-d)}`.  The exponent `(d-1)k - d ≥ d - 2 ≥ 1`
is where `(d-1)k > d` is used: the shells contribute `(k'+1)^{d-1}`, the summand decays as
`(k'+1)^{-(d-1)k}`, so the radial sum is `∑ (k'+1)^{-((d-1)(k-1))}` with `(d-1)(k-1) ≥ 2`; at `k = 1`
the exponent is `0` and the sum grows like `L`. -/
private theorem cltMom1_tail_sum (hd : 3 ≤ d) {q : ℕ} (hq : 2 ≤ q) {ρ : ℝ} (hρ : 0 < ρ) :
    ∑ x : Zd d L, (if ρ < ((zdistInf d L x : ℕ) : ℝ) then
        1 / (((zdistInf d L x : ℕ) : ℝ) ^ (d - 1) + 1) ^ q else 0) ≤
      CltMom1.cs d * 2 ^ ((d - 1) * q) / ρ ^ ((d - 1) * q - d) := by
  classical
  set F : ℕ → ℝ := fun k => if ρ < (k : ℝ) then 1 / ((k : ℝ) ^ (d - 1) + 1) ^ q else 0 with hF
  have hF0 : ∀ k, 0 ≤ F k := fun k => by simp only [hF]; split_ifs <;> positivity
  have hcs := CltMom1.cs_pos (d := d) (by omega)
  refine (cltMom1_sum_shell (d := d) (L := L) (by omega) F hF0).trans ?_
  -- the exponent `E = (d-1) q - d ≥ 1`
  obtain ⟨E, hE⟩ : ∃ E : ℕ, (d - 1) * q = d + E ∧ 1 ≤ E := by
    refine ⟨(d - 1) * q - d, ?_, ?_⟩
    · have : d ≤ (d - 1) * q := by nlinarith [Nat.sub_add_cancel (show 1 ≤ d by omega)]
      omega
    · have : d + 1 ≤ (d - 1) * q := by
        calc d + 1 ≤ (d - 1) * 2 := by omega
          _ ≤ (d - 1) * q := Nat.mul_le_mul_left _ hq
      omega
  obtain ⟨hE1, hE2⟩ := hE
  have hexp : (d - 1) * q - d = E := by omega
  rw [hexp]
  -- termwise bound
  have hterm : ∀ k ∈ Finset.range (L + 1),
      CltMom1.cs d * ((k : ℝ) + 1) ^ (d - 1) * F k ≤
        if ρ < (k : ℝ) then CltMom1.cs d * 2 ^ ((d - 1) * q) *
          (1 / ρ ^ (E - 1) * (1 / ((k : ℝ) + 1) ^ 2)) else 0 := by
    intro k _
    by_cases hk : ρ < (k : ℝ)
    · simp only [hF, hk, ↓reduceIte]
      have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
      have hp := cltMom1_pow_add_one_le hk0 (d - 1)
      have hpq : ((k : ℝ) + 1) ^ ((d - 1) * q) ≤ 2 ^ ((d - 1) * q) * ((k : ℝ) ^ (d - 1) + 1) ^ q := by
        have := pow_le_pow_left₀ (by positivity) hp q
        rw [mul_pow, ← pow_mul, ← pow_mul] at this
        exact this
      have hden : (0 : ℝ) < ((k : ℝ) ^ (d - 1) + 1) ^ q := by positivity
      -- (k+1)^{d-1} / (k^{d-1}+1)^q ≤ 2^{(d-1)q} (k+1)^{-(E+1)}
      have hsplit : ((k : ℝ) + 1) ^ ((d - 1) * q) = ((k : ℝ) + 1) ^ (d - 1) * ((k : ℝ) + 1) ^ (E + 1) := by
        rw [← pow_add]; congr 1; omega
      have hE1' : ((k : ℝ) + 1) ^ (E + 1) = ((k : ℝ) + 1) ^ (E - 1) * ((k : ℝ) + 1) ^ 2 := by
        rw [← pow_add]; congr 1; omega
      have hρk : ρ ^ (E - 1) ≤ ((k : ℝ) + 1) ^ (E - 1) :=
        pow_le_pow_left₀ hρ.le (by linarith) _
      have hρpos : 0 < ρ ^ (E - 1) := pow_pos hρ _
      have h1 : ((k : ℝ) + 1) ^ (d - 1) * (1 / ((k : ℝ) ^ (d - 1) + 1) ^ q) ≤
          2 ^ ((d - 1) * q) * (1 / ρ ^ (E - 1) * (1 / ((k : ℝ) + 1) ^ 2)) := by
        rw [mul_one_div, div_le_iff₀ hden]
        have hkE : 0 < ((k : ℝ) + 1) ^ (E + 1) := by positivity
        have h3 : ((k : ℝ) + 1) ^ (d - 1) ≤
            2 ^ ((d - 1) * q) * ((k : ℝ) ^ (d - 1) + 1) ^ q / ((k : ℝ) + 1) ^ (E + 1) := by
          rw [le_div_iff₀ hkE]
          calc ((k : ℝ) + 1) ^ (d - 1) * ((k : ℝ) + 1) ^ (E + 1) = ((k : ℝ) + 1) ^ ((d - 1) * q) := hsplit.symm
            _ ≤ _ := hpq
        have h4 : 2 ^ ((d - 1) * q) * ((k : ℝ) ^ (d - 1) + 1) ^ q / ((k : ℝ) + 1) ^ (E + 1) ≤
            2 ^ ((d - 1) * q) * (1 / ρ ^ (E - 1) * (1 / ((k : ℝ) + 1) ^ 2)) * ((k : ℝ) ^ (d - 1) + 1) ^ q := by
          rw [hE1']
          have : 1 / (((k : ℝ) + 1) ^ (E - 1) * ((k : ℝ) + 1) ^ 2) ≤ 1 / ρ ^ (E - 1) * (1 / ((k : ℝ) + 1) ^ 2) := by
            rw [one_div_mul_one_div]
            apply one_div_le_one_div_of_le (by positivity)
            exact mul_le_mul_of_nonneg_right hρk (by positivity)
          calc 2 ^ ((d - 1) * q) * ((k : ℝ) ^ (d - 1) + 1) ^ q / (((k : ℝ) + 1) ^ (E - 1) * ((k : ℝ) + 1) ^ 2)
              = 2 ^ ((d - 1) * q) * ((k : ℝ) ^ (d - 1) + 1) ^ q * (1 / (((k : ℝ) + 1) ^ (E - 1) * ((k : ℝ) + 1) ^ 2)) := by ring
            _ ≤ 2 ^ ((d - 1) * q) * ((k : ℝ) ^ (d - 1) + 1) ^ q * (1 / ρ ^ (E - 1) * (1 / ((k : ℝ) + 1) ^ 2)) :=
                mul_le_mul_of_nonneg_left this (by positivity)
            _ = _ := by ring
        exact h3.trans h4
      calc CltMom1.cs d * ((k : ℝ) + 1) ^ (d - 1) * (1 / ((k : ℝ) ^ (d - 1) + 1) ^ q)
          = CltMom1.cs d * (((k : ℝ) + 1) ^ (d - 1) * (1 / ((k : ℝ) ^ (d - 1) + 1) ^ q)) := by ring
        _ ≤ CltMom1.cs d * (2 ^ ((d - 1) * q) * (1 / ρ ^ (E - 1) * (1 / ((k : ℝ) + 1) ^ 2))) :=
            mul_le_mul_of_nonneg_left h1 hcs.le
        _ = _ := by ring
    · simp [hF, hk]
  refine (Finset.sum_le_sum hterm).trans ?_
  have hsum : ∑ k ∈ Finset.range (L + 1),
      (if ρ < (k : ℝ) then CltMom1.cs d * 2 ^ ((d - 1) * q) * (1 / ρ ^ (E - 1) * (1 / ((k : ℝ) + 1) ^ 2)) else 0)
      = CltMom1.cs d * 2 ^ ((d - 1) * q) * (1 / ρ ^ (E - 1)) *
        ∑ k ∈ Finset.range (L + 1), (if ρ < (k : ℝ) then 1 / ((k : ℝ) + 1) ^ 2 else 0) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    split_ifs <;> ring
  rw [hsum]
  have hT := cltMom1_tail_inv_sq hρ (L + 1)
  have hc0 : 0 ≤ CltMom1.cs d * 2 ^ ((d - 1) * q) * (1 / ρ ^ (E - 1)) := by positivity
  calc _ ≤ CltMom1.cs d * 2 ^ ((d - 1) * q) * (1 / ρ ^ (E - 1)) * (1 / ρ) :=
        mul_le_mul_of_nonneg_left hT hc0
    _ = CltMom1.cs d * 2 ^ ((d - 1) * q) / ρ ^ E := by
        have : ρ ^ E = ρ ^ (E - 1) * ρ := by rw [← pow_succ]; congr 1; omega
        rw [this]; field_simp

end Lattice

/-! ## 2. Clusters under the pairing condition `(eq:pairingcond)` (target 1) -/

section Clusters

variable {d L : ℕ} [NeZero L]

/-- **Cluster structure** of `3_5:2225` (RBM2D `CltMoments.Cluster`, `CltMoments.lean:72`, commit `c9a24cf`):
a retraction `φ` of `Fin n` (`φ ∘ φ = φ`) whose fixed points (the representatives `k_i`) each carry at least one
further index, `φ k` being the representative that `k` is assigned to.  The clusters are the fibres
`A_i = {k : φ k = k_i}`. -/
def CltMom1.Cluster {n : ℕ} (φ : Fin n → Fin n) : Prop :=
  (∀ i, φ (φ i) = φ i) ∧ ∀ i, φ i = i → ∃ k, k ≠ i ∧ φ k = i

/-- **The pairing condition `(eq:pairingcond)`** (`3_5:2223`) at radius `R` on the first labels of `n` two-label
indices `b k = (b₁^{(k)}, b₂^{(k)})`: every `k` has a partner `l ≠ k` with `|b₁^{(k)} - b₁^{(l)}|_∞ < R`.  The
inequality is strict: with `R = 10 (log W)³ ℓ_s` its complement is *literally* the isolation hypothesis
`10 (log W)³ ℓ_s ≤ |b₁^{(i)} - b₁^{(j)}|` (`j ≠ i`) of `STCltIsoConcl` (`cltMom1_not_paired_iff`); the paper writes
`≤` in `(eq:pairingcond)` and `≥` in `(eq:bound_isolated)`, which overlap at equality (paper-delta candidate `T2165a`). -/
def CltMom1.Paired (R : ℝ) {n : ℕ} (b : Fin n → (Fin 2 → Zd d L)) : Prop :=
  ∀ i, ∃ k, k ≠ i ∧ ((zdistInf d L ((b i) 0 - (b k) 0) : ℕ) : ℝ) < R

/-- The representatives (free indices) of `φ`. -/
abbrev CltMom1.free {n : ℕ} (φ : Fin n → Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun s => φ s = s)

/-- The number of non-free indices assigned to the representative `s`: `|A_i| - 1`. -/
def CltMom1.assigned {n : ℕ} (φ : Fin n → Fin n) (s : Fin n) : ℕ :=
  (Finset.univ.filter fun k => φ k = s ∧ k ≠ s).card

/-- The closed ball `{β' : |β₁ - β₁'|_∞ ≤ R}` of two-label indices, measured on the first labels. -/
def CltMom1.ball (R : ℝ) (β : Fin 2 → Zd d L) : Finset (Fin 2 → Zd d L) :=
  Finset.univ.filter fun β' => ((zdistInf d L (β 0 - β' 0) : ℕ) : ℝ) ≤ R

open Classical in
/-- The cluster sum `∑_{(𝒮,φ)} ∏_{s∈𝒮} ∑_β z_β (∑_{|β₁'-β₁| ≤ R} z_{β'})^{k_s}` over the cluster structures
(port of RBM2D `CltMoments.clusterSum`, `CltMoments.lean:163`, with the label `Z2 L` replaced by the two-label
index `Fin 2 → Zd d L` and the distance `zdist2` by `zdistInf` of the first labels). -/
def CltMom1.clusterSum (n : ℕ) (z : (Fin 2 → Zd d L) → ℝ) (R : ℝ) : ℝ :=
  ∑ φ ∈ (Finset.univ : Finset (Fin n → Fin n)).filter (fun φ => CltMom1.Cluster φ),
    ∏ s ∈ CltMom1.free φ,
      ∑ β : Fin 2 → Zd d L, z β * (∑ β' ∈ CltMom1.ball R β, z β') ^ CltMom1.assigned φ s

/-- **Existence of the cluster decomposition** under the pairing condition (port of RBM2D `cltm_exists_cluster`,
`CltMoments.lean:75-148`; the paper's decomposition into the components of `|b₁^{(k)} - b₁^{(l)}| ≤ R` is replaced by
a maximal `2R`-separated set `S` of indices and `φ k` = a nearest point of `S`; separation `2R` instead of RBM2D's `3R`
suffices because a partner `k₀` of `i ∈ S` has `δ(i,k₀) < R`, so `k₀ ∉ S` and every other `s ∈ S` satisfies
`δ(k₀,s) ≥ 2R - R > δ(k₀,i)`; paper-delta candidate `T2165a`).  Every index lies within `2R` of its
representative's first label. -/
theorem cltMom1_exists_cluster {n : ℕ} (b : Fin n → (Fin 2 → Zd d L)) (R : ℝ)
    (hnf : CltMom1.Paired R b) :
    ∃ φ : Fin n → Fin n, CltMom1.Cluster φ ∧
      ∀ k, ((zdistInf d L ((b (φ k)) 0 - (b k) 0) : ℕ) : ℝ) ≤ 2 * R := by
  classical
  set dd : Fin n → Fin n → ℝ := fun i k => ((zdistInf d L ((b i) 0 - (b k) 0) : ℕ) : ℝ) with hdd
  have dsymm : ∀ i k, dd i k = dd k i := fun i k => by
    simp only [hdd]; rw [cltMom1_zdistInf_sub_comm]
  have dtri : ∀ i k m, dd i m ≤ dd i k + dd k m := fun i k m => by
    simp only [hdd]; exact_mod_cast cltMom1_zdistInf_tri ((b i) 0) ((b k) 0) ((b m) 0)
  have dnn : ∀ i k, 0 ≤ dd i k := fun i k => by simp only [hdd]; positivity
  have dself : ∀ i, dd i i = 0 := fun i => by simp [hdd, cltMom1_zdistInf_zero]
  let Sep : Finset (Fin n) → Prop := fun S => ∀ s ∈ S, ∀ s' ∈ S, s ≠ s' → 2 * R ≤ dd s s'
  obtain ⟨S, hSmem, hSmax⟩ := Finset.exists_max_image (Finset.univ.filter Sep) Finset.card
    ⟨∅, by simp [Sep]⟩
  have hSep : Sep S := (Finset.mem_filter.1 hSmem).2
  have hmax : ∀ k, k ∉ S → ∃ s ∈ S, dd k s < 2 * R := by
    intro k hk
    by_contra hcon
    push Not at hcon
    have hsep' : Sep (insert k S) := by
      intro s hs s' hs' hne
      rcases Finset.mem_insert.1 hs with h1 | h1
      · rcases Finset.mem_insert.1 hs' with h2 | h2
        · exact absurd (h1.trans h2.symm) hne
        · rw [h1]; exact hcon s' h2
      · rcases Finset.mem_insert.1 hs' with h2 | h2
        · rw [h2, dsymm]; exact hcon s h1
        · exact hSep s h1 s' h2 hne
    have := hSmax (insert k S) (Finset.mem_filter.2 ⟨Finset.mem_univ _, hsep'⟩)
    rw [Finset.card_insert_of_notMem hk] at this
    omega
  have hex : ∀ k, ∃ m, m ∈ S ∧ (k ∈ S → m = k) ∧ (k ∉ S → ∀ s' ∈ S, dd k m ≤ dd k s') := by
    intro k
    by_cases hk : k ∈ S
    · exact ⟨k, hk, fun _ => rfl, fun h => absurd hk h⟩
    · obtain ⟨s, hs, _⟩ := hmax k hk
      obtain ⟨m, hm, hmin⟩ := Finset.exists_min_image S (dd k) ⟨s, hs⟩
      exact ⟨m, hm, fun h => absurd h hk, fun _ => hmin⟩
  choose φ hφS hφfix hφmin using hex
  refine ⟨φ, ⟨fun i => hφfix (φ i) (hφS i), ?_⟩, ?_⟩
  · intro i hi
    have hiS : i ∈ S := hi ▸ hφS i
    obtain ⟨k₀, hk₀ne, hk₀d⟩ := hnf i
    have hRpos : 0 < R := lt_of_le_of_lt (dnn i k₀) hk₀d
    have hk₀S : k₀ ∉ S := by
      intro hk₀S
      have := hSep i hiS k₀ hk₀S (Ne.symm hk₀ne)
      change 2 * R ≤ dd i k₀ at this
      change dd i k₀ < R at hk₀d
      linarith
    refine ⟨k₀, hk₀ne, ?_⟩
    by_contra hne
    have h1 : dd k₀ (φ k₀) ≤ dd k₀ i := hφmin k₀ hk₀S i hiS
    have h2 : dd i k₀ < R := hk₀d
    have h3 := hSep i hiS (φ k₀) (hφS k₀) (Ne.symm hne)
    have h4 := dtri i k₀ (φ k₀)
    have := dsymm k₀ i
    linarith
  · intro k
    by_cases hk : k ∈ S
    · have : φ k = k := hφfix k hk
      rw [this]
      have := dself k
      have hRpos : 0 < R := by
        obtain ⟨k₀, _, hk₀d⟩ := hnf k
        exact lt_of_le_of_lt (dnn k k₀) hk₀d
      change dd k k ≤ 2 * R
      linarith
    · obtain ⟨s, hs, hsd⟩ := hmax k hk
      have h1 := hφmin k hk s hs
      have h2 := dsymm (φ k) k
      change dd (φ k) k ≤ 2 * R
      linarith

/-- **The sum over cluster-compatible configurations factorises over the representatives** (port of RBM2D
`cltm_sum_compat`, `CltMoments.lean:168-282`, the label `Z2 L` being the two-label index and the compatibility `|b₁^{(φ k)} - b₁^{(k)}| ≤ R`
being on the first labels): `∑_{b compatible with φ} ∏_k z(b^{(k)}) = ∏_{s ∈ free φ} ∑_β z(β) (∑_{|β₁'-β₁| ≤ R} z(β'))^{assigned φ s}`. -/
theorem cltMom1_sum_compat {n : ℕ} (φ : Fin n → Fin n) (hφ : φ ∘ φ = φ) (z : (Fin 2 → Zd d L) → ℝ)
    (R : ℝ) (hR : 0 ≤ R) :
    ∑ b ∈ Finset.univ.filter (fun b : Fin n → (Fin 2 → Zd d L) =>
        ∀ k, ((zdistInf d L ((b (φ k)) 0 - (b k) 0) : ℕ) : ℝ) ≤ R), ∏ k, z (b k)
      = ∏ s ∈ Finset.univ.filter (fun s => φ s = s),
          ∑ β : (Fin 2 → Zd d L), z β * (∑ β' ∈ CltMom1.ball R β, z β') ^ CltMom1.assigned φ s := by
  classical
  set S : Finset (Fin n) := Finset.univ.filter (fun s => φ s = s) with hS
  have hφS : ∀ k, φ k ∈ S := fun k => by
    simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and]
    exact congrFun hφ k
  let t : Fin n → Finset ((Fin 2 → Zd d L)) := fun k => if k ∈ S then Finset.univ else {0}
  let r : (Fin n → (Fin 2 → Zd d L)) → (Fin n → (Fin 2 → Zd d L)) := fun b k => if k ∈ S then b k else 0
  set C : Finset (Fin n → (Fin 2 → Zd d L)) := Finset.univ.filter (fun b : Fin n → (Fin 2 → Zd d L) =>
        ∀ k, ((zdistInf d L ((b (φ k)) 0 - (b k) 0) : ℕ) : ℝ) ≤ R) with hC
  have hmaps : ∀ b ∈ C, r b ∈ Fintype.piFinset t := by
    intro b _
    rw [Fintype.mem_piFinset]
    intro k
    by_cases hk : k ∈ S
    · simp [r, t, hk]
    · simp [r, t, hk]
  rw [← Finset.sum_fiberwise_of_maps_to (g := r) (t := Fintype.piFinset t) hmaps]
  set Bf : (Fin 2 → Zd d L) → ℝ := fun β => ∑ β' ∈ CltMom1.ball R β, z β' with hBf
  have hfib : ∀ β ∈ Fintype.piFinset t,
      ∑ b ∈ C with r b = β, ∏ k, z (b k)
        = ∏ s ∈ S, z (β s) * Bf (β s) ^ CltMom1.assigned φ s := by
    intro β hβ
    have hβ' : ∀ k, k ∉ S → β k = 0 := by
      intro k hk
      have := Fintype.mem_piFinset.1 hβ k
      simpa [t, hk] using this
    have hset : C.filter (fun b => r b = β) =
        Fintype.piFinset (fun k => if k ∈ S then {β k} else CltMom1.ball R (β (φ k))) := by
      ext b
      simp only [hC, Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset]
      constructor
      · rintro ⟨hcomp, hrb⟩ k
        by_cases hk : k ∈ S
        · have : r b k = β k := congrFun hrb k
          simp only [r, hk, ite_true] at this
          simp [hk, this]
        · have hφk : b (φ k) = β (φ k) := by
            have : r b (φ k) = β (φ k) := congrFun hrb (φ k)
            simpa [r, hφS k] using this
          simp only [hk, ite_false, CltMom1.ball, Finset.mem_filter, Finset.mem_univ, true_and]
          have := hcomp k
          rw [hφk] at this
          exact this
      · intro hb
        refine ⟨?_, ?_⟩
        · intro k
          by_cases hk : k ∈ S
          · have hbk : b k = β k := by simpa [hk] using hb k
            have hφk : φ k = k := (Finset.mem_filter.1 hk).2
            rw [hφk]; simpa [cltMom1_zdistInf_zero] using hR
          · have hbk := hb k
            simp only [hk, ite_false, CltMom1.ball, Finset.mem_filter, Finset.mem_univ, true_and] at hbk
            have hφk : b (φ k) = β (φ k) := by
              have := hb (φ k)
              simpa [hφS k] using this
            rw [hφk]; exact hbk
        · funext k
          by_cases hk : k ∈ S
          · have hbk : b k = β k := by simpa [hk] using hb k
            simp [r, hk, hbk]
          · simp [r, hk, hβ' k hk]
    rw [hset, ← Finset.prod_univ_sum (fun k => if k ∈ S then ({β k} : Finset ((Fin 2 → Zd d L))) else CltMom1.ball R (β (φ k)))
      (fun _ x => z x)]
    have h1 : ∏ k, ∑ x ∈ (if k ∈ S then ({β k} : Finset ((Fin 2 → Zd d L))) else CltMom1.ball R (β (φ k))), z x
        = ∏ k, (if k ∈ S then z (β k) else Bf (β (φ k))) := by
      refine Finset.prod_congr rfl fun k _ => ?_
      by_cases hk : k ∈ S <;> simp [hk, hBf]
    rw [h1, Finset.prod_ite]
    have e1 : (Finset.univ.filter fun k => k ∈ S) = S := by ext; simp
    have e2 : (Finset.univ.filter fun k => k ∉ S) = Sᶜ := by ext; simp
    rw [e1, e2]
    have e3 : ∏ k ∈ Sᶜ, Bf (β (φ k)) = ∏ s ∈ S, Bf (β s) ^ CltMom1.assigned φ s := by
      rw [← Finset.prod_fiberwise_of_maps_to (g := φ) (t := S) (f := fun k => Bf (β (φ k)))
        (fun k _ => hφS k)]
      refine Finset.prod_congr rfl fun y hy => ?_
      have hfil : (Sᶜ.filter fun k => φ k = y) = Finset.univ.filter fun k => φ k = y ∧ k ≠ y := by
        ext k
        simp only [Finset.mem_filter, Finset.mem_compl, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨hk, hky⟩
          exact ⟨hky, fun h => hk (h ▸ hy)⟩
        · rintro ⟨hky, hne⟩
          refine ⟨fun hk => hne ?_, hky⟩
          have : φ k = k := (Finset.mem_filter.1 hk).2
          rw [← this, hky]
      have : ∏ k ∈ Sᶜ.filter (fun k => φ k = y), Bf (β (φ k)) = ∏ k ∈ Sᶜ.filter (fun k => φ k = y), Bf (β y) :=
        Finset.prod_congr rfl fun k hk => by rw [(Finset.mem_filter.1 hk).2]
      rw [this, Finset.prod_const, hfil]
      rfl
    rw [e3, ← Finset.prod_mul_distrib]
  rw [Finset.sum_congr rfl hfib]
  -- now sum over β ∈ piFinset t of ∏_{s ∈ S} h s (β s)
  let h : Fin n → (Fin 2 → Zd d L) → ℝ := fun k x => if k ∈ S then z x * Bf x ^ CltMom1.assigned φ k else 1
  have hsum := Finset.prod_univ_sum t h
  have h2 : ∀ β : Fin n → (Fin 2 → Zd d L), ∏ k, h k (β k) = ∏ s ∈ S, z (β s) * Bf (β s) ^ CltMom1.assigned φ s := by
    intro β
    simp only [h]
    rw [Finset.prod_ite, Finset.prod_const_one, mul_one]
    have e1 : (Finset.univ.filter fun k => k ∈ S) = S := by ext; simp
    rw [e1]
  simp only [h2] at hsum
  rw [← hsum]
  have h3 : ∀ k, ∑ x ∈ t k, h k x = if k ∈ S then ∑ β : (Fin 2 → Zd d L), z β * Bf β ^ CltMom1.assigned φ k else 1 := by
    intro k
    by_cases hk : k ∈ S <;> simp [t, h, hk]
  rw [Finset.prod_congr rfl fun k _ => h3 k, Finset.prod_ite, Finset.prod_const_one, mul_one]
  have e1 : (Finset.univ.filter fun k => k ∈ S) = S := by ext; simp
  rw [e1]


open Classical in
/-- **The paired part of the moment sum is bounded by the cluster sum at radius `2R`** (port of RBM2D
`cltm_nonfar_sum_le`, `CltMoments.lean:283`, with `2R` for `3R`): for `z ≥ 0` the sum over the configurations
satisfying the pairing condition (`CltMom1.Paired R`) of `∏_k z(b^{(k)})` is at most `CltMom1.clusterSum n z (2R)`. -/
theorem cltMom1_paired_sum_le {n : ℕ} (z : (Fin 2 → Zd d L) → ℝ) (hz : ∀ β, 0 ≤ z β) (R : ℝ)
    (hR : 0 ≤ R) :
    ∑ b ∈ Finset.univ.filter (fun b : Fin n → (Fin 2 → Zd d L) => CltMom1.Paired R b), ∏ k, z (b k)
      ≤ CltMom1.clusterSum n z (2 * R) := by
  classical
  have hR2 : 0 ≤ 2 * R := by linarith
  unfold CltMom1.clusterSum
  have hstep : ∀ φ ∈ (Finset.univ : Finset (Fin n → Fin n)).filter (fun φ => CltMom1.Cluster φ),
      ∏ s ∈ Finset.univ.filter (fun s => φ s = s),
        ∑ β : (Fin 2 → Zd d L), z β * (∑ β' ∈ CltMom1.ball (2 * R) β, z β') ^ CltMom1.assigned φ s
      = ∑ b : Fin n → (Fin 2 → Zd d L), if (∀ k, ((zdistInf d L ((b (φ k)) 0 - (b k) 0) : ℕ) : ℝ) ≤ 2 * R)
          then ∏ k, z (b k) else 0 := by
    intro φ hφ
    have hφ' : CltMom1.Cluster φ := (Finset.mem_filter.1 hφ).2
    have hcomp : φ ∘ φ = φ := funext hφ'.1
    rw [← cltMom1_sum_compat φ hcomp z (2 * R) hR2, Finset.sum_filter]
  rw [Finset.sum_congr rfl hstep, Finset.sum_comm]
  set G : (Fin n → (Fin 2 → Zd d L)) → ℝ := fun b => ∑ φ ∈ (Finset.univ : Finset (Fin n → Fin n)).filter
    (fun φ => CltMom1.Cluster φ), if (∀ k, ((zdistInf d L ((b (φ k)) 0 - (b k) 0) : ℕ) : ℝ) ≤ 2 * R)
      then ∏ k, z (b k) else 0 with hG
  have hwnn : ∀ b : Fin n → (Fin 2 → Zd d L), 0 ≤ ∏ k, z (b k) := fun b => Finset.prod_nonneg fun k _ => hz _
  have hG0 : ∀ b, 0 ≤ G b := fun b =>
    Finset.sum_nonneg fun φ _ => by split_ifs; exacts [hwnn b, le_rfl]
  have hG1 : ∀ b : Fin n → (Fin 2 → Zd d L), CltMom1.Paired R b →
      ∏ k, z (b k) ≤ G b := by
    intro b hb
    obtain ⟨φ, hφ, hφd⟩ := cltMom1_exists_cluster b R hb
    have hmem : φ ∈ (Finset.univ : Finset (Fin n → Fin n)).filter (fun φ => CltMom1.Cluster φ) :=
      Finset.mem_filter.2 ⟨Finset.mem_univ _, hφ⟩
    have hsingle := Finset.single_le_sum (f := fun φ : Fin n → Fin n =>
      if (∀ k, ((zdistInf d L ((b (φ k)) 0 - (b k) 0) : ℕ) : ℝ) ≤ 2 * R) then ∏ k, z (b k) else 0)
      (s := (Finset.univ : Finset (Fin n → Fin n)).filter (fun φ => CltMom1.Cluster φ))
      (fun φ _ => by split_ifs; exacts [hwnn b, le_rfl]) hmem
    have hite : (if (∀ k, ((zdistInf d L ((b (φ k)) 0 - (b k) 0) : ℕ) : ℝ) ≤ 2 * R) then ∏ k, z (b k) else 0)
        = ∏ k, z (b k) := by simp [hφd]
    rw [hite] at hsingle
    exact hsingle
  calc ∑ b ∈ Finset.univ.filter (fun b : Fin n → (Fin 2 → Zd d L) => CltMom1.Paired R b), ∏ k, z (b k)
      ≤ ∑ b ∈ Finset.univ.filter (fun b : Fin n → (Fin 2 → Zd d L) => CltMom1.Paired R b), G b :=
        Finset.sum_le_sum fun b hb => hG1 b (Finset.mem_filter.1 hb).2
    _ ≤ ∑ b : Fin n → (Fin 2 → Zd d L), G b :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun b _ _ => hG0 b


/-- Every representative carries at least one further index. -/
theorem cltMom1_assigned_pos {n : ℕ} {φ : Fin n → Fin n} (hφ : CltMom1.Cluster φ) {s : Fin n}
    (hs : φ s = s) : 1 ≤ CltMom1.assigned φ s := by
  obtain ⟨k, hk, hks⟩ := hφ.2 s hs
  unfold CltMom1.assigned
  exact Finset.card_pos.2 ⟨k, Finset.mem_filter.2 ⟨Finset.mem_univ _, hks, hk⟩⟩

/-- `∑_s |assigned s| + #free = n`: the clusters partition the `n` indices (`∑_i |A_i| = 2p`). -/
theorem cltMom1_sum_assigned {n : ℕ} {φ : Fin n → Fin n} (hφ : CltMom1.Cluster φ) :
    ∑ s ∈ CltMom1.free φ, CltMom1.assigned φ s + (CltMom1.free φ).card = n := by
  classical
  have hmaps : Set.MapsTo φ ((CltMom1.free φ)ᶜ : Finset (Fin n)) (CltMom1.free φ : Finset (Fin n)) := by
    intro k _
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq]
    exact hφ.1 k
  have h1 := Finset.card_eq_sum_card_fiberwise hmaps
  have h2 : ∀ y ∈ CltMom1.free φ, ((CltMom1.free φ)ᶜ.filter fun a => φ a = y).card = CltMom1.assigned φ y := by
    intro y hy
    have hyS : φ y = y := (Finset.mem_filter.1 hy).2
    unfold CltMom1.assigned
    congr 1
    ext k
    simp only [Finset.mem_filter, Finset.mem_compl, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hk, hky⟩
      refine ⟨hky, fun h => hk ?_⟩
      rw [h]; exact hyS
    · rintro ⟨hky, hne⟩
      refine ⟨fun hk => hne ?_, hky⟩
      have : φ k = k := hk
      rw [← this, hky]
  rw [Finset.sum_congr rfl h2] at h1
  have h3 := Finset.card_compl (CltMom1.free φ)
  simp only [Fintype.card_fin] at h3
  have : (CltMom1.free φ).card ≤ n := by
    have := Finset.card_le_univ (CltMom1.free φ); simpa using this
  have h1' : ((CltMom1.free φ)ᶜ).card = ∑ s ∈ CltMom1.free φ, CltMom1.assigned φ s := h1
  omega

/-- `2 r ≤ n`: each cluster has at least two elements, so there are at most `p` clusters among `2p` indices. -/
theorem cltMom1_two_mul_free_le {n : ℕ} {φ : Fin n → Fin n} (hφ : CltMom1.Cluster φ) :
    2 * (CltMom1.free φ).card ≤ n := by
  have h := cltMom1_sum_assigned hφ
  have h2 : (CltMom1.free φ).card ≤ ∑ s ∈ CltMom1.free φ, CltMom1.assigned φ s := by
    calc (CltMom1.free φ).card = ∑ _s ∈ CltMom1.free φ, 1 := by simp
      _ ≤ ∑ s ∈ CltMom1.free φ, CltMom1.assigned φ s :=
        Finset.sum_le_sum fun s hs => cltMom1_assigned_pos hφ (Finset.mem_filter.1 hs).2
  omega

open Classical in
/-- **The number of cluster structures is at most `n^n`** (RBM2D `cltm_card_cluster_le`, `CltMoments.lean:380`). -/
theorem cltMom1_card_cluster_le (n : ℕ) :
    (((Finset.univ : Finset (Fin n → Fin n)).filter (fun φ => CltMom1.Cluster φ)).card : ℝ)
      ≤ (n : ℝ) ^ n := by
  classical
  have h1 := Finset.card_filter_le (Finset.univ : Finset (Fin n → Fin n)) (fun φ => CltMom1.Cluster φ)
  have h2 : (Finset.univ : Finset (Fin n → Fin n)).card = n ^ n := by
    simp [Finset.card_univ]
  have : ((Finset.univ : Finset (Fin n → Fin n)).filter (fun φ => CltMom1.Cluster φ)).card ≤ n ^ n := by
    omega
  exact_mod_cast this

/-- General reduction: a bound `g κ` on the per-cluster sums bounds the cluster sum. -/
theorem cltMom1_clusterSum_le_of_bound {n : ℕ} (z : (Fin 2 → Zd d L) → ℝ) (hz0 : ∀ β, 0 ≤ z β) (R : ℝ)
    (g : ℕ → ℝ) (hg : ∀ k, 1 ≤ k → ∑ β, z β * (∑ β' ∈ CltMom1.ball R β, z β') ^ k ≤ g k)
    (Bnd : ℝ) (hBnd0 : 0 ≤ Bnd)
    (hprod : ∀ φ : Fin n → Fin n, CltMom1.Cluster φ → ∏ s ∈ CltMom1.free φ, g (CltMom1.assigned φ s) ≤ Bnd) :
    CltMom1.clusterSum n z R ≤ (n : ℝ) ^ n * Bnd := by
  classical
  unfold CltMom1.clusterSum
  calc ∑ φ ∈ (Finset.univ : Finset (Fin n → Fin n)).filter (fun φ => CltMom1.Cluster φ),
        ∏ s ∈ Finset.univ.filter (fun s => φ s = s),
          ∑ β : (Fin 2 → Zd d L), z β * (∑ β' ∈ CltMom1.ball R β, z β') ^ CltMom1.assigned φ s
      ≤ ∑ _φ ∈ (Finset.univ : Finset (Fin n → Fin n)).filter (fun φ => CltMom1.Cluster φ), Bnd := by
        refine Finset.sum_le_sum fun φ hφ => ?_
        have hφ' : CltMom1.Cluster φ := (Finset.mem_filter.1 hφ).2
        refine le_trans (Finset.prod_le_prod₀ (fun s _ => Finset.sum_nonneg fun β _ =>
          mul_nonneg (hz0 β) (pow_nonneg (Finset.sum_nonneg fun β' _ => hz0 β') _))
          (fun s hs => hg _ (cltMom1_assigned_pos hφ' (Finset.mem_filter.1 hs).2))) (hprod φ hφ')
    _ = (((Finset.univ : Finset (Fin n → Fin n)).filter (fun φ => CltMom1.Cluster φ)).card : ℝ) * Bnd := by
        simp
    _ ≤ (n : ℝ) ^ n * Bnd := mul_le_mul_of_nonneg_right (cltMom1_card_cluster_le n) hBnd0

theorem cltMom1_clusterSum_nonneg {n : ℕ} (z : (Fin 2 → Zd d L) → ℝ) (hz0 : ∀ β, 0 ≤ z β) (R : ℝ) :
    0 ≤ CltMom1.clusterSum n z R := by
  unfold CltMom1.clusterSum
  exact Finset.sum_nonneg fun φ _ => Finset.prod_nonneg fun s _ => Finset.sum_nonneg fun β _ =>
    mul_nonneg (hz0 β) (pow_nonneg (Finset.sum_nonneg fun β' _ => hz0 β') _)


open Classical in
/-- **Target 1 (clusters).**  Let `b : Fin (2p) → (Fin 2 → Zd d L)` be `2p` two-label indices satisfying the pairing
condition at radius `R ≥ 0` (`(eq:pairingcond)`, `3_5:2223`).  Then there is a retraction `φ` of `Fin (2p)` (the cluster
decomposition `⊔_{i=1}^r A_i`, `A_i = {k : φ k = k_i}`, the representatives being the fixed points) such that every
cluster has at least `2` elements, there are `r ≤ p` clusters, every member's first label lies within `2R ≤ 2pR` of its
representative's first label, and the number of cluster structures is at most `(2p)^{2p}`.  Construction: a maximal
`2R`-separated set of indices with nearest-point assignment (the construction of RBM2D `cltm_exists_cluster` with
separation `2R` instead of `3R`), not the components of `|b₁^{(k)} - b₁^{(l)}| ≤ R` used in the paper (`3_5:2225`);
paper-delta candidate `T2165a`.  The equivalence "not paired ⇔ some label isolated as in `STCltIsoConcl`" is
`cltMom1_not_paired_iff` / `cltMom1_iso_hyp_iff`. -/
theorem cltMom1_clusters {p : ℕ} (hp : 1 ≤ p) {R : ℝ} (hR : 0 ≤ R)
    (b : Fin (2 * p) → (Fin 2 → Zd d L)) (hb : CltMom1.Paired R b) :
    ∃ φ : Fin (2 * p) → Fin (2 * p), CltMom1.Cluster φ ∧
      (∀ s, φ s = s → 2 ≤ (Finset.univ.filter fun k => φ k = s).card) ∧
      (CltMom1.free φ).card ≤ p ∧
      (∀ k, ((zdistInf d L ((b (φ k)) 0 - (b k) 0) : ℕ) : ℝ) ≤ 2 * R) ∧
      (∀ k, ((zdistInf d L ((b (φ k)) 0 - (b k) 0) : ℕ) : ℝ) ≤ 2 * (p : ℝ) * R) ∧
      ((((Finset.univ : Finset (Fin (2 * p) → Fin (2 * p))).filter
          (fun φ => CltMom1.Cluster φ)).card : ℝ) ≤ ((2 * p : ℕ) : ℝ) ^ (2 * p)) := by
  classical
  obtain ⟨φ, hφ, hd⟩ := cltMom1_exists_cluster b R hb
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp
  refine ⟨φ, hφ, ?_, ?_, hd, fun k => (hd k).trans ?_, cltMom1_card_cluster_le (2 * p)⟩
  · intro s hs
    obtain ⟨k, hk, hks⟩ := hφ.2 s hs
    have hsub : ({s, k} : Finset (Fin (2 * p))) ⊆ Finset.univ.filter fun k => φ k = s := by
      intro x hx
      rcases Finset.mem_insert.1 hx with rfl | hx
      · simp [hs]
      · rw [Finset.mem_singleton.1 hx]; simp [hks]
    calc 2 = ({s, k} : Finset (Fin (2 * p))).card := by
          rw [Finset.card_pair (Ne.symm hk)]
      _ ≤ _ := Finset.card_le_card hsub
  · have := cltMom1_two_mul_free_le hφ
    omega
  · nlinarith

/-- **Not paired `⇔` some label is isolated** (the hypothesis shape of `STCltIsoConcl`, `Step5Pins.lean:420-421`):
`¬ Paired R b ↔ ∃ i, ∀ j ≠ i, R ≤ |b₁^{(i)} - b₁^{(j)}|_∞`. -/
theorem cltMom1_not_paired_iff {n : ℕ} (R : ℝ) (b : Fin n → (Fin 2 → Zd d L)) :
    ¬ CltMom1.Paired R b ↔
      ∃ i, ∀ j, j ≠ i → R ≤ ((zdistInf d L ((b i) 0 - (b j) 0) : ℕ) : ℝ) := by
  unfold CltMom1.Paired
  push Not
  rfl

/-- The isolation hypothesis of `STCltIsoConcl` (`Step5Pins.lean:420-421`, text copied) is exactly the complement of
the pairing condition at `R = 10 (log W)³ ℓ_s`: the sum over all configurations splits, without a translation
lemma, into the paired part (this file) and the isolated part (`stCltIso_holds`). -/
theorem cltMom1_iso_hyp_iff (sz : Sizes d) (n p : ℕ) (s : ℝ)
    (b : Fin (2 * p) → (Fin 2 → Zd d (sz.L n))) :
    (∃ i, ∀ j, j ≠ i → 10 * Real.log ((sz.W n : ℕ) : ℝ) ^ 3 * ellT (sz.L n) (sz.lam n) s ≤
        ((zdistInf d (sz.L n) ((b i) 0 - (b j) 0) : ℕ) : ℝ)) ↔
      ¬ CltMom1.Paired (10 * Real.log ((sz.W n : ℕ) : ℝ) ^ 3 * ellT (sz.L n) (sz.lam n) s) b :=
  (cltMom1_not_paired_iff _ _).symm


end Clusters

/-! ## 3. The per-label weights from `(prop:ThfadC)` and `(prop:BD1)` (target 2) -/

section Weights

private theorem cltMom1_norm_spin {m : ℂ} (hm : ‖m‖ = 1) (b c : Bool) :
    ‖PropSpin m b * PropSpin m c‖ = 1 := by
  have h1 : ∀ b : Bool, ‖PropSpin m b‖ = 1 := by
    intro b
    unfold PropSpin
    split_ifs
    · exact hm
    · simpa using hm
  rw [norm_mul, h1, h1, one_mul]

private theorem cltMom1_norm_xi {m : ℂ} (hm : ‖m‖ = 1) (σ₁ σ₂ : Bool) {t : ℝ} (ht0 : 0 ≤ t)
    (ht1 : t < 1) : ‖(t : ℂ) * (PropSpin m σ₁ * PropSpin m σ₂)‖ < 1 := by
  rw [norm_mul, cltMom1_norm_spin hm, mul_one, Complex.norm_real, Real.norm_of_nonneg ht0]
  exact ht1

/-- `Θ_{xy} = Θ_{0,y-x}` (property 2 of `lem_propTH`). -/
private theorem cltMom1_Theta_shift {d L : ℕ} [NeZero L] (hL : 3 ≤ L) {g : ℝ} {ξ : ℂ}
    (hξ : ‖ξ‖ < 1) (x y : Zd d L) : Theta d L g ξ x y = Theta d L g ξ 0 (y - x) := by
  have := Theta_apply_add_right_of_three_le (d := d) (g := g) hL hξ 0 (y - x) x
  rwa [zero_add, sub_add_cancel] at this

/-- **Target 2a: the weight at `a₁` from `(prop:ThfadC)`** (`3_5:2218`, `(prop:ThfadC)` = `prop5Decay_holds`
`Propagator/Prop5Hold.lean:784`): there is `C₅ = C₅(d, Λ) > 0` such that, for `3 ≤ L`, `0 < g ≤ Λ`, `0 ≤ t < 1`,
`‖m‖ = 1`, any signs, in regime (i) of `STfFar` (`g²/L² ≤ 1 - t`, `g = ilambda`),
`g² |Θ_t(a, b)| ≤ C₅ (1 + 2^{d-1}) / (|a - b|_∞^{d-2} + 1)`.
Route: `meanFar_T1` (`MeanFar.lean:762`) applied to `T = Θ_t(0, ·)` after `Θ_{ab} = Θ_{0,b-a}`.  The zero-mode term of
`B_{t,|x|₁}` (`Defs/Tail.lean`, `Bparam`) is `(L^d |1-t|)⁻¹`; it is absorbed by the regime `1 - t ≥ g²/L²`
(`zeroMode_le_of_ge`: `(L^d (1-t))⁻¹ ≤ 2^{d-1} (g²+|1-t|)⁻¹ (|x|+1)^{-(d-2)}` for `|x|_∞ ≤ L`), which gives the factor
`1 + 2^{d-1}`.  No far-region restriction is needed for this bound; `(r+1)^{d-2} ≥ r^{d-2} + 1`
converts `(|x|+1)^{-(d-2)}` into the profile `1/(|x|^{d-2}+1)` of `(eq:simplecalculus)`. -/
theorem cltMom1_weight_a1 (d : ℕ) (Λ : ℝ) (hd : 3 ≤ d) (hΛ : 0 < Λ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ g : ℝ, 0 < g → g ≤ Λ →
      ∀ t : ℝ, 0 ≤ t → t < 1 → g ^ 2 / (L : ℝ) ^ 2 ≤ 1 - t →
      ∀ m : ℂ, ‖m‖ = 1 → ∀ σ₁ σ₂ : Bool, ∀ a b : Zd d L,
        g ^ 2 * ‖Theta d L g ((t : ℂ) * (PropSpin m σ₁ * PropSpin m σ₂)) a b‖ ≤
          C * (1 + 2 ^ (d - 1)) / (((zdistInf d L (a - b) : ℕ) : ℝ) ^ (d - 2) + 1) := by
  obtain ⟨C₅, hC₅, c₅, hc₅, H5⟩ := prop5Decay_holds d Λ hd hΛ
  refine ⟨C₅, hC₅, ?_⟩
  intro L _ hL g hg hgΛ t ht0 ht1 hreg m hm σ₁ σ₂ a b
  have hξ := cltMom1_norm_xi hm σ₁ σ₂ ht0 ht1
  have hT1 := meanFar_T1 hd hL hg ht1 hreg hC₅.le hc₅
    (fun x => Theta d L g ((t : ℂ) * (PropSpin m σ₁ * PropSpin m σ₂)) 0 x)
    (fun x => H5 L hL g hg hgΛ t ht0 ht1 m hm σ₁ σ₂ x) (b - a)
  rw [cltMom1_Theta_shift hL hξ a b]
  rw [cltMom1_zdistInf_sub_comm b a] at hT1
  set r : ℝ := ((zdistInf d L (a - b) : ℕ) : ℝ) with hr
  have hr0 : 0 ≤ r := Nat.cast_nonneg _
  have hpow := cltMom1_pow_add_one_ge hr0 (show d - 2 ≠ 0 by omega)
  have hg2 : 0 < g ^ 2 := by positivity
  calc g ^ 2 * ‖Theta d L g ((t : ℂ) * (PropSpin m σ₁ * PropSpin m σ₂)) 0 (b - a)‖
      ≤ g ^ 2 * ((C₅ * (1 + 2 ^ (d - 1)) / g ^ 2) / (r + 1) ^ (d - 2)) :=
        mul_le_mul_of_nonneg_left hT1 hg2.le
    _ = C₅ * (1 + 2 ^ (d - 1)) / (r + 1) ^ (d - 2) := by field_simp
    _ ≤ C₅ * (1 + 2 ^ (d - 1)) / (r ^ (d - 2) + 1) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hpow

/-- **Target 2b: the weight at `a₂` from `(prop:BD1)`** (`3_5:2218`, `prop6Diff1_holds`
`Propagator/Prop6Hold.lean:353`, `c = 1/2`): there is `C₆ = C₆(d, Λ, κ) > 0` such that for `‖m‖ = 1`, `κ ≤ Im m`,
`|b₁ - b₂|_∞ ≤ w`, `2 d w ≤ ρ < |a₂ - b₁|_∞`,
`g² |Θ_t(b₂, a₂) - Θ_t(b₁, a₂)| ≤ C₆ d w / (|a₂ - b₁|_∞^{d-1} + 1)`.
`(prop:BD1)` is applied at `a = a₂ - b₁`, `r = b₁ - b₂` (`a + r = a₂ - b₂`); its premise `|r|₁ ≤ ½ |a|₁` holds as
`|r|₁ ≤ d |r|_∞ ≤ d w ≤ ρ/2 < ½ |a|_∞ ≤ ½ |a|₁`.  `(prop:BD1)` has no zero-mode term (it is stated for
`(g² + |1-t|)⁻¹`), so no regime is used; `g² (g²+|1-t|)⁻¹ ≤ 1`.  With `w = (log W)³ ℓ_s` this is the weight
`C (log W)³ ℓ_s / (|a₂ - b₁|^{d-1} + 1)` of the paper (`3_5:2218` writes `ℓ_s`; the numerator `w` is the window,
paper-delta candidate `T2165b`). -/
theorem cltMom1_weight_a2 (d : ℕ) (Λ κ : ℝ) (hd : 3 ≤ d) (hΛ : 0 < Λ) (hκ : 0 < κ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ g : ℝ, 0 < g → g ≤ Λ →
      ∀ t : ℝ, 0 ≤ t → t < 1 → ∀ m : ℂ, ‖m‖ = 1 → κ ≤ m.im → ∀ σ₁ σ₂ : Bool,
      ∀ a₂ b₁ b₂ : Zd d L, ∀ w ρ : ℝ, 2 * d * w ≤ ρ → ρ < ((zdistInf d L (a₂ - b₁) : ℕ) : ℝ) →
        ((zdistInf d L (b₁ - b₂) : ℕ) : ℝ) ≤ w →
        g ^ 2 * ‖Theta d L g ((t : ℂ) * (PropSpin m σ₁ * PropSpin m σ₂)) b₂ a₂ -
            Theta d L g ((t : ℂ) * (PropSpin m σ₁ * PropSpin m σ₂)) b₁ a₂‖ ≤
          C * d * w / (((zdistInf d L (a₂ - b₁) : ℕ) : ℝ) ^ (d - 1) + 1) := by
  obtain ⟨C₆, hC₆, H6⟩ := prop6Diff1_holds d Λ κ (1 / 2) hd hΛ hκ (by norm_num) (by norm_num)
  refine ⟨C₆, hC₆, ?_⟩
  intro L _ hL g hg hgΛ t ht0 ht1 m hm hκm σ₁ σ₂ a₂ b₁ b₂ w ρ hρw ha hr
  have hξ := cltMom1_norm_xi hm σ₁ σ₂ ht0 ht1
  set a : Zd d L := a₂ - b₁ with hadef
  set r : Zd d L := b₁ - b₂ with hrdef
  have hsum : a + r = a₂ - b₂ := by rw [hadef, hrdef]; exact sub_add_sub_cancel a₂ b₁ b₂
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hrD : (zdistD d L r : ℝ) ≤ d * w := by
    have h1 : ((zdistD d L r : ℕ) : ℝ) ≤ ((d * zdistInf d L r : ℕ) : ℝ) := by
      exact_mod_cast zdistD_le_mul_zdistInf d L r
    push_cast at h1
    exact h1.trans (mul_le_mul_of_nonneg_left hr hd0)
  have haD : ((zdistInf d L a : ℕ) : ℝ) ≤ (zdistD d L a : ℝ) := by
    exact_mod_cast zdistInf_le_zdistD d L a
  have hprem : (zdistD d L r : ℝ) ≤ 1 / 2 * (zdistD d L a : ℝ) := by linarith
  have hBD := H6 L hL g hg hgΛ t ht0 ht1 m hm hκm σ₁ σ₂ a r hprem
  have e1 : Theta d L g ((t : ℂ) * (PropSpin m σ₁ * PropSpin m σ₂)) b₂ a₂ =
      Theta d L g ((t : ℂ) * (PropSpin m σ₁ * PropSpin m σ₂)) 0 (a + r) := by
    rw [cltMom1_Theta_shift hL hξ b₂ a₂, hsum]
  have e2 : Theta d L g ((t : ℂ) * (PropSpin m σ₁ * PropSpin m σ₂)) b₁ a₂ =
      Theta d L g ((t : ℂ) * (PropSpin m σ₁ * PropSpin m σ₂)) 0 a := by
    rw [cltMom1_Theta_shift hL hξ b₁ a₂]
  rw [e1, e2]
  set A : ℝ := ((zdistInf d L a : ℕ) : ℝ) with hA
  have hA0 : 0 ≤ A := Nat.cast_nonneg _
  have hpow := cltMom1_pow_add_one_ge hA0 (show d - 1 ≠ 0 by omega)
  have hpow2 : (A + 1) ^ (d - 1) ≤ ((zdistD d L a : ℝ) + 1) ^ (d - 1) :=
    pow_le_pow_left₀ (by linarith) (by linarith) _
  have hg2 : 0 < g ^ 2 := by positivity
  have hden : 0 < g ^ 2 + |1 - t| := by positivity
  have hfac : g ^ 2 * (g ^ 2 + |1 - t|)⁻¹ ≤ 1 := by
    rw [← div_eq_mul_inv, div_le_one hden]
    linarith [abs_nonneg (1 - t)]
  have hinv : (((zdistD d L a : ℝ) + 1) ^ (d - 1))⁻¹ ≤ 1 / (A ^ (d - 1) + 1) := by
    rw [← one_div]
    exact one_div_le_one_div_of_le (by positivity) (hpow.trans hpow2)
  have hr0 : (0 : ℝ) ≤ zdistD d L r := Nat.cast_nonneg _
  calc g ^ 2 * ‖Theta d L g ((t : ℂ) * (PropSpin m σ₁ * PropSpin m σ₂)) 0 (a + r) -
          Theta d L g ((t : ℂ) * (PropSpin m σ₁ * PropSpin m σ₂)) 0 a‖
      ≤ g ^ 2 * (C₆ * (g ^ 2 + |1 - t|)⁻¹ * (zdistD d L r : ℝ) *
          (((zdistD d L a : ℝ) + 1) ^ (d - 1))⁻¹) := mul_le_mul_of_nonneg_left hBD hg2.le
    _ = C₆ * (g ^ 2 * (g ^ 2 + |1 - t|)⁻¹) * (zdistD d L r : ℝ) *
          (((zdistD d L a : ℝ) + 1) ^ (d - 1))⁻¹ := by ring
    _ ≤ C₆ * 1 * (d * w) * (1 / (A ^ (d - 1) + 1)) := by
        have hw0 : 0 ≤ w := le_trans (Nat.cast_nonneg _) hr
        gcongr
    _ = C₆ * d * w / (A ^ (d - 1) + 1) := by ring

end Weights

/-! ## 4. Comparability of the weights inside a cluster (target 3) -/

section Comparable

variable {d L : ℕ} [NeZero L]

/-- Real form: if `2 r ≤ ρ < X` and `|X - X'| ≤ r`, then `X' > X/2` and `X' < 2X`, hence the profiles
`1/(X^m+1)` and `1/(X'^m+1)` agree up to the factor `2^m` in both directions. -/
theorem cltMom1_comparable_real {r ρ X X' : ℝ} (hρ : 2 * r ≤ ρ) (hX : ρ < X)
    (hXX' : |X - X'| ≤ r) (hr0 : 0 ≤ r) (m : ℕ) :
    1 / (X' ^ m + 1) ≤ 2 ^ m / (X ^ m + 1) ∧ 1 / (X ^ m + 1) ≤ 2 ^ m / (X' ^ m + 1) := by
  have hX0 : 0 < X := by linarith
  have h1 := abs_le.1 hXX'
  have hX'low : X / 2 ≤ X' := by linarith [h1.1, h1.2]
  have hX'up : X' ≤ 2 * X := by linarith [h1.1, h1.2]
  have hX'0 : 0 < X' := by linarith
  have h2m : (0 : ℝ) < 2 ^ m := pow_pos two_pos m
  constructor
  · -- `X'^m + 1 ≥ (X/2)^m + 1 ≥ (X^m+1)/2^m`
    have hp : (X / 2) ^ m ≤ X' ^ m := pow_le_pow_left₀ (by positivity) hX'low m
    have hq : (X ^ m + 1) / 2 ^ m ≤ X' ^ m + 1 := by
      rw [div_le_iff₀ h2m]
      have : X ^ m = 2 ^ m * (X / 2) ^ m := by rw [← mul_pow]; congr 1; ring
      have h3 : (1 : ℝ) ≤ 2 ^ m := one_le_pow₀ (by norm_num)
      nlinarith [pow_nonneg hX0.le m, pow_nonneg (show (0 : ℝ) ≤ X / 2 by positivity) m]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    rw [div_le_iff₀ h2m] at hq
    nlinarith
  · have hp : X' ^ m ≤ (2 * X) ^ m := pow_le_pow_left₀ hX'0.le hX'up m
    have hq : X' ^ m + 1 ≥ 0 := by positivity
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have h3 : (1 : ℝ) ≤ 2 ^ m := one_le_pow₀ (by norm_num)
    have : (2 * X) ^ m = 2 ^ m * X ^ m := mul_pow _ _ _
    nlinarith [pow_nonneg hX0.le m]

/-- **Target 3: comparability of the weights on a cluster.**  Let `ρ < |a - b|_∞` (`b` in the far region of `a`),
`|b - b'|_∞ ≤ r` and `2 r ≤ ρ`.  Then `|a - b'|` is within a factor `2` of `|a - b|`, hence for every exponent `m`
(`m = d-2` for the weight at `a₁`, `m = d-1` for the weight at `a₂`; each `2^m ≤ 2^d`) the profiles
`1/(|a-b|^m+1)` and `1/(|a-b'|^m+1)` agree up to the factor `2^m`, in both directions.  For the cluster radius
`r = 2R`, `R = 10 (log W)³ ℓ_s`, the premise `2 r = 40 (log W)³ ℓ_s ≤ ρ = (log W)⁴ ℓ_s` follows from `log W ≥ 40`
(`cltMom1_scale_comparable`, `p = 1`); for `r = 2pR` it follows from `log W ≥ 40 p` (same lemma). -/
theorem cltMom1_comparable {r ρ : ℝ} (hρ : 2 * r ≤ ρ) (hr0 : 0 ≤ r) (a b b' : Zd d L)
    (hb : ρ < ((zdistInf d L (a - b) : ℕ) : ℝ)) (hbb' : ((zdistInf d L (b - b') : ℕ) : ℝ) ≤ r)
    (m : ℕ) :
    1 / (((zdistInf d L (a - b') : ℕ) : ℝ) ^ m + 1) ≤ 2 ^ m / (((zdistInf d L (a - b) : ℕ) : ℝ) ^ m + 1) ∧
    1 / (((zdistInf d L (a - b) : ℕ) : ℝ) ^ m + 1) ≤ 2 ^ m / (((zdistInf d L (a - b') : ℕ) : ℝ) ^ m + 1) := by
  refine cltMom1_comparable_real hρ hb ?_ hr0 m
  have h1 : zdistInf d L (a - b') ≤ zdistInf d L (a - b) + zdistInf d L (b - b') :=
    cltMom1_zdistInf_tri a b b'
  have h2 : zdistInf d L (a - b) ≤ zdistInf d L (a - b') + zdistInf d L (b' - b) := by
    have := cltMom1_zdistInf_tri a b' b
    exact this
  have h3 : zdistInf d L (b' - b) = zdistInf d L (b - b') := cltMom1_zdistInf_sub_comm _ _
  rw [abs_le]
  have h1' : ((zdistInf d L (a - b') : ℕ) : ℝ) ≤ ((zdistInf d L (a - b) : ℕ) : ℝ) + ((zdistInf d L (b - b') : ℕ) : ℝ) := by
    exact_mod_cast h1
  have h2' : ((zdistInf d L (a - b) : ℕ) : ℝ) ≤ ((zdistInf d L (a - b') : ℕ) : ℝ) + ((zdistInf d L (b - b') : ℕ) : ℝ) := by
    rw [h3] at h2; exact_mod_cast h2
  constructor <;> linarith

/-- **The two weights of a label** (`3_5:2218`): `W₁(b) = 1/(|a₁ - b|^{d-2}+1)` and
`W₂(b) = λ/(|a₂ - b|^{d-1}+1)`, `λ ≥ 0`.  For `b` in the far region (`ρ < |a₁ - b|`, `ρ < |a₂ - b|`) and `b'` with
`|b - b'| ≤ r`, `2 r ≤ ρ`, each weight at `b'` is at most `2^d` times the weight at `b` (in fact `2^{d-2}`, `2^{d-1}`),
and conversely. -/
theorem cltMom1_comparable_weights {r ρ lam : ℝ} (hρ : 2 * r ≤ ρ) (hr0 : 0 ≤ r) (hlam : 0 ≤ lam)
    (a₁ a₂ b b' : Zd d L) (hb₁ : ρ < ((zdistInf d L (a₁ - b) : ℕ) : ℝ))
    (hb₂ : ρ < ((zdistInf d L (a₂ - b) : ℕ) : ℝ)) (hbb' : ((zdistInf d L (b - b') : ℕ) : ℝ) ≤ r)
    (hd : 2 ≤ d) :
    (1 / (((zdistInf d L (a₁ - b') : ℕ) : ℝ) ^ (d - 2) + 1) ≤
        2 ^ d * (1 / (((zdistInf d L (a₁ - b) : ℕ) : ℝ) ^ (d - 2) + 1)) ∧
      1 / (((zdistInf d L (a₁ - b) : ℕ) : ℝ) ^ (d - 2) + 1) ≤
        2 ^ d * (1 / (((zdistInf d L (a₁ - b') : ℕ) : ℝ) ^ (d - 2) + 1))) ∧
    (lam / (((zdistInf d L (a₂ - b') : ℕ) : ℝ) ^ (d - 1) + 1) ≤
        2 ^ d * (lam / (((zdistInf d L (a₂ - b) : ℕ) : ℝ) ^ (d - 1) + 1)) ∧
      lam / (((zdistInf d L (a₂ - b) : ℕ) : ℝ) ^ (d - 1) + 1) ≤
        2 ^ d * (lam / (((zdistInf d L (a₂ - b') : ℕ) : ℝ) ^ (d - 1) + 1))) := by
  have h2d : ∀ m : ℕ, m ≤ d → (2 : ℝ) ^ m ≤ 2 ^ d := fun m hm =>
    pow_le_pow_right₀ (by norm_num) hm
  obtain ⟨c1, c2⟩ := cltMom1_comparable hρ hr0 a₁ b b' hb₁ hbb' (d - 2)
  obtain ⟨e1, e2⟩ := cltMom1_comparable hρ hr0 a₂ b b' hb₂ hbb' (d - 1)
  have f1 := h2d (d - 2) (by omega)
  have f2 := h2d (d - 1) (by omega)
  have g1 : ∀ x y : ℝ, 0 < x → 0 < y → ∀ m : ℕ, m ≤ d → 1 / x ≤ 2 ^ m / y → 1 / x ≤ 2 ^ d * (1 / y) := by
    intro x y hx hy m hm h
    refine h.trans ?_
    rw [← mul_one_div]
    exact mul_le_mul_of_nonneg_right (h2d m hm) (by positivity)
  have hz : ∀ s : ℝ, 0 ≤ s → 0 < s ^ (d - 2) + 1 := fun s hs => by positivity
  have hz' : ∀ s : ℝ, 0 ≤ s → 0 < s ^ (d - 1) + 1 := fun s hs => by positivity
  refine ⟨⟨g1 _ _ (hz _ (Nat.cast_nonneg _)) (hz _ (Nat.cast_nonneg _)) _ (by omega) c1,
    g1 _ _ (hz _ (Nat.cast_nonneg _)) (hz _ (Nat.cast_nonneg _)) _ (by omega) c2⟩, ?_, ?_⟩
  · have := g1 _ _ (hz' _ (Nat.cast_nonneg _)) (hz' _ (Nat.cast_nonneg _)) _ (by omega) e1
    calc lam / (((zdistInf d L (a₂ - b') : ℕ) : ℝ) ^ (d - 1) + 1)
        = lam * (1 / (((zdistInf d L (a₂ - b') : ℕ) : ℝ) ^ (d - 1) + 1)) := by ring
      _ ≤ lam * (2 ^ d * (1 / (((zdistInf d L (a₂ - b) : ℕ) : ℝ) ^ (d - 1) + 1))) :=
          mul_le_mul_of_nonneg_left this hlam
      _ = _ := by ring
  · have := g1 _ _ (hz' _ (Nat.cast_nonneg _)) (hz' _ (Nat.cast_nonneg _)) _ (by omega) e2
    calc lam / (((zdistInf d L (a₂ - b) : ℕ) : ℝ) ^ (d - 1) + 1)
        = lam * (1 / (((zdistInf d L (a₂ - b) : ℕ) : ℝ) ^ (d - 1) + 1)) := by ring
      _ ≤ lam * (2 ^ d * (1 / (((zdistInf d L (a₂ - b') : ℕ) : ℝ) ^ (d - 1) + 1))) :=
          mul_le_mul_of_nonneg_left this hlam
      _ = _ := by ring

end Comparable

/-! ## 5. The scales `w = (log W)³ ℓ_s`, `ρ = (log W)⁴ ℓ_s`, `R = 10 (log W)³ ℓ_s` -/

section Scales

/-- **The premise of the comparability (target 3), exact form.**  With `lw = log W`, `w = lw³ ℓ`, `ρ = lw⁴ ℓ`,
`R = 10 lw³ ℓ`: `2 · (2 p R) = 40 p w ≤ ρ` holds when `lw ≥ 40 p` (`ℓ ≥ 0`; the converse for `ℓ > 0` is
division by `w`, not formalized).  For the cluster radius `2R` of `cltMom1_clusters` (not `2pR`) the premise is `lw ≥ 40` (`p = 1`). -/
theorem cltMom1_scale_comparable {lw ℓ : ℝ} {p : ℕ} (hlw : 40 * (p : ℝ) ≤ lw) (hℓ : 0 ≤ ℓ) :
    2 * (2 * (p : ℝ) * (10 * lw ^ 3 * ℓ)) ≤ lw ^ 4 * ℓ := by
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  have hlw0 : 0 ≤ lw := by linarith
  have h1 : 0 ≤ lw ^ 3 * ℓ := by positivity
  nlinarith [mul_nonneg (sub_nonneg.2 hlw) h1]

/-- The premise of `(prop:BD1)` in the window: `2 d w ≤ ρ` holds when `lw ≥ 2d` (`D368` form). -/
theorem cltMom1_scale_bd1 {lw ℓ : ℝ} {d : ℕ} (hlw : 2 * (d : ℝ) ≤ lw) (hℓ : 0 ≤ ℓ) :
    2 * (d : ℝ) * (lw ^ 3 * ℓ) ≤ lw ^ 4 * ℓ := by
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hlw0 : 0 ≤ lw := by linarith
  have h1 : 0 ≤ lw ^ 3 * ℓ := by positivity
  nlinarith [mul_nonneg (sub_nonneg.2 hlw) h1]

/-- `1 ≤ w = lw³ ℓ` for `lw ≥ 1`, `ℓ ≥ 1`. -/
theorem cltMom1_scale_one_le {lw ℓ : ℝ} (hlw : 1 ≤ lw) (hℓ : 1 ≤ ℓ) : 1 ≤ lw ^ 3 * ℓ := by
  have : 1 ≤ lw ^ 3 := one_le_pow₀ hlw
  nlinarith

/-- `ℓ ≤ ρ = lw⁴ ℓ`. -/
theorem cltMom1_scale_ell_le {lw ℓ : ℝ} (hlw : 1 ≤ lw) (hℓ : 0 ≤ ℓ) : ℓ ≤ lw ^ 4 * ℓ := by
  have : 1 ≤ lw ^ 4 := one_le_pow₀ hlw
  nlinarith

end Scales

/-! ## 6. The per-cluster sum (target 4) -/

section ClusterSum

variable {d L : ℕ} [NeZero L]

/-- The window profile `G_w(x) = 1/(|x|_∞^{d-2}+1)` on `|x|_∞ ≤ w`, `0` outside: the factor
`1/(|b₁^{(k)} - b₂^{(k)}|^{d-2}+1)` of `(eq:2p_product_pair)` together with the window of `(eq:sumregionsforb)`. -/
def CltMom1.G (d L : ℕ) [NeZero L] (w : ℝ) (x : Zd d L) : ℝ :=
  if ((zdistInf d L x : ℕ) : ℝ) ≤ w then 1 / (((zdistInf d L x : ℕ) : ℝ) ^ (d - 2) + 1) else 0

theorem CltMom1.G_nonneg (w : ℝ) (x : Zd d L) : 0 ≤ CltMom1.G d L w x := by
  unfold CltMom1.G; split_ifs <;> positivity

/-- The window constant `Y_w = cs 2^{d-2} (w+1)²`, `cs = 2 d 2^{d-1}` (the shell constant). -/
def CltMom1.Yw (d : ℕ) (w : ℝ) : ℝ := CltMom1.cs d * 2 ^ (d - 2) * (w + 1) ^ 2

theorem CltMom1.Yw_nonneg (hd : 1 ≤ d) (w : ℝ) : 0 ≤ CltMom1.Yw d w := by
  have := CltMom1.cs_pos (d := d) hd
  unfold CltMom1.Yw; positivity

/-- `∑_x G_w(x) ≤ Y_w`. -/
theorem cltMom1_G_sum_le (hd : 3 ≤ d) {w : ℝ} (hw : 0 ≤ w) :
    ∑ x : Zd d L, CltMom1.G d L w x ≤ CltMom1.Yw d w :=
  cltMom1_window_sum hd hw

/-- `∑_y G_w(x - y) ≤ Y_w` for every `x`. -/
theorem cltMom1_G_sum_sub_le (hd : 3 ≤ d) {w : ℝ} (hw : 0 ≤ w) (x : Zd d L) :
    ∑ y : Zd d L, CltMom1.G d L w (x - y) ≤ CltMom1.Yw d w := by
  rw [cltMom1_sum_sub_left (fun y => CltMom1.G d L w y) x]
  exact cltMom1_G_sum_le hd hw

private theorem cltMom1_sum_pair (F : Zd d L → Zd d L → ℝ) :
    ∑ v : Fin 2 → Zd d L, F (v 0) (v 1) = ∑ u₀ : Zd d L, ∑ u₁ : Zd d L, F u₀ u₁ := by
  rw [Fintype.sum_equiv (piFinTwoEquiv fun _ : Fin 2 => Zd d L) (fun v => F (v 0) (v 1))
    (fun p => F p.1 p.2) (fun v => rfl), Fintype.sum_prod_type]

/-- The ball count in the translated form `∑_{u₀} 1[|x - u₀| ≤ R] ≤ (2R+1)^d`. -/
private theorem cltMom1_ball_count (x : Zd d L) {R : ℝ} (hR : 0 ≤ R) :
    ∑ u : Zd d L, (if ((zdistInf d L (x - u) : ℕ) : ℝ) ≤ R then (1 : ℝ) else 0) ≤ (2 * R + 1) ^ d := by
  classical
  rw [cltMom1_sum_sub_left (fun y => if ((zdistInf d L y : ℕ) : ℝ) ≤ R then (1 : ℝ) else 0) x]
  rw [← Finset.sum_filter]
  simpa using cltMom1_card_ball (d := d) (L := L) R hR

/-- **Sum of `G` over a ball of two-label indices**: `∑_{β' ∈ ball R β} G_w(β₁' - β₂') ≤ (2R+1)^d Y_w`. -/
private theorem cltMom1_ball_G_sum (hd : 3 ≤ d) {w R : ℝ} (hw : 0 ≤ w) (hR : 0 ≤ R)
    (β : Fin 2 → Zd d L) :
    ∑ β' ∈ CltMom1.ball R β, CltMom1.G d L w (β' 0 - β' 1) ≤ (2 * R + 1) ^ d * CltMom1.Yw d w := by
  classical
  have hY0 := CltMom1.Yw_nonneg (d := d) (by omega) w
  have h1 : ∑ β' ∈ CltMom1.ball R β, CltMom1.G d L w (β' 0 - β' 1) =
      ∑ u₀ : Zd d L, ∑ u₁ : Zd d L, (if ((zdistInf d L (β 0 - u₀) : ℕ) : ℝ) ≤ R then
        CltMom1.G d L w (u₀ - u₁) else 0) := by
    rw [← cltMom1_sum_pair (fun u₀ u₁ => if ((zdistInf d L (β 0 - u₀) : ℕ) : ℝ) ≤ R then
        CltMom1.G d L w (u₀ - u₁) else 0)]
    unfold CltMom1.ball
    rw [Finset.sum_filter]
  rw [h1]
  have h2 : ∀ u₀ : Zd d L, ∑ u₁ : Zd d L, (if ((zdistInf d L (β 0 - u₀) : ℕ) : ℝ) ≤ R then
        CltMom1.G d L w (u₀ - u₁) else 0) ≤
      (if ((zdistInf d L (β 0 - u₀) : ℕ) : ℝ) ≤ R then (1 : ℝ) else 0) * CltMom1.Yw d w := by
    intro u₀
    by_cases h : ((zdistInf d L (β 0 - u₀) : ℕ) : ℝ) ≤ R
    · simp only [h, ↓reduceIte, one_mul]
      exact cltMom1_G_sum_sub_le hd hw u₀
    · simp [h]
  refine (Finset.sum_le_sum fun u₀ _ => h2 u₀).trans ?_
  rw [← Finset.sum_mul]
  exact mul_le_mul_of_nonneg_right (cltMom1_ball_count (β 0) hR) hY0

/-- **Target 4: the per-cluster sum** (`3_5:2233`, second step of `(eq:2p_product_pair)`).  For a representative with first
label `x`, a cluster with `m = |A| - 1` further indices (first labels within `R_b` of `x`, windows `|b₁ - b₂| ≤ w`) and the
representative's own second label, `∑_{b₂^{rep}} ∑_{(b^{(k)})_{k∈A∖rep}} G_w(x - b₂^{rep}) ∏_k 1[|b₁^{(k)} - x| ≤ R_b] G_w(b₁^{(k)} - b₂^{(k)})
≤ Y_w ((2R_b+1)^d Y_w)^m`, `Y_w = cs 2^{d-2} (w+1)²`. -/
theorem cltMom1_cluster_sum (hd : 3 ≤ d) {w Rb : ℝ} (hw : 0 ≤ w) (hRb : 0 ≤ Rb) (m : ℕ) (x : Zd d L) :
    ∑ b₂ : Zd d L, ∑ β : Fin m → (Fin 2 → Zd d L),
      CltMom1.G d L w (x - b₂) * ∏ k : Fin m,
        (if ((zdistInf d L ((β k) 0 - x) : ℕ) : ℝ) ≤ Rb then
          CltMom1.G d L w ((β k) 0 - (β k) 1) else 0) ≤
      CltMom1.Yw d w * ((2 * Rb + 1) ^ d * CltMom1.Yw d w) ^ m := by
  classical
  have hY0 := CltMom1.Yw_nonneg (d := d) (by omega) w
  set f : (Fin 2 → Zd d L) → ℝ := fun v =>
    if ((zdistInf d L (v 0 - x) : ℕ) : ℝ) ≤ Rb then CltMom1.G d L w (v 0 - v 1) else 0 with hf
  have hf0 : ∀ v, 0 ≤ f v := fun v => by simp only [hf]; split_ifs <;> [exact CltMom1.G_nonneg _ _; exact le_rfl]
  have hprod : ∀ b₂ : Zd d L, ∑ β : Fin m → (Fin 2 → Zd d L),
      CltMom1.G d L w (x - b₂) * ∏ k : Fin m,
        (if ((zdistInf d L ((β k) 0 - x) : ℕ) : ℝ) ≤ Rb then
          CltMom1.G d L w ((β k) 0 - (β k) 1) else 0) =
      CltMom1.G d L w (x - b₂) * (∑ v, f v) ^ m := by
    intro b₂
    rw [← Finset.mul_sum]
    congr 1
    have := Finset.prod_univ_sum (fun _ : Fin m => (Finset.univ : Finset (Fin 2 → Zd d L))) (fun _ v => f v)
    rw [Fintype.piFinset_univ] at this
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at this
    exact this.symm
  simp only [hprod]
  rw [← Finset.sum_mul]
  have hS : ∑ v, f v ≤ (2 * Rb + 1) ^ d * CltMom1.Yw d w := by
    have : ∑ v, f v = ∑ u₀ : Zd d L, ∑ u₁ : Zd d L, (if ((zdistInf d L (u₀ - x) : ℕ) : ℝ) ≤ Rb then
        CltMom1.G d L w (u₀ - u₁) else 0) := cltMom1_sum_pair (fun u₀ u₁ =>
          if ((zdistInf d L (u₀ - x) : ℕ) : ℝ) ≤ Rb then CltMom1.G d L w (u₀ - u₁) else 0)
    rw [this]
    have h2 : ∀ u₀ : Zd d L, ∑ u₁ : Zd d L, (if ((zdistInf d L (u₀ - x) : ℕ) : ℝ) ≤ Rb then
          CltMom1.G d L w (u₀ - u₁) else 0) ≤
        (if ((zdistInf d L (x - u₀) : ℕ) : ℝ) ≤ Rb then (1 : ℝ) else 0) * CltMom1.Yw d w := by
      intro u₀
      rw [cltMom1_zdistInf_sub_comm x u₀]
      by_cases h : ((zdistInf d L (u₀ - x) : ℕ) : ℝ) ≤ Rb
      · simp only [h, ↓reduceIte, one_mul]
        exact cltMom1_G_sum_sub_le hd hw u₀
      · simp [h]
    refine (Finset.sum_le_sum fun u₀ _ => h2 u₀).trans ?_
    rw [← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right (cltMom1_ball_count x hRb) hY0
  have hS0 : 0 ≤ ∑ v, f v := Finset.sum_nonneg fun v _ => hf0 v
  have hG : ∑ b₂ : Zd d L, CltMom1.G d L w (x - b₂) ≤ CltMom1.Yw d w := cltMom1_G_sum_sub_le hd hw x
  calc (∑ b₂ : Zd d L, CltMom1.G d L w (x - b₂)) * (∑ v, f v) ^ m
      ≤ CltMom1.Yw d w * ((2 * Rb + 1) ^ d * CltMom1.Yw d w) ^ m := by
        apply mul_le_mul hG (pow_le_pow_left₀ hS0 hS m) (by positivity) hY0

/-- `Y_w ≤ d 4^d w²` for `w ≥ 1` (`cs 2^{d-2} (w+1)² ≤ cs 2^{d-2} 4 w²`, `cs 2^d = d 4^d`). -/
theorem CltMom1.Yw_le (hd : 3 ≤ d) {w : ℝ} (hw : 1 ≤ w) : CltMom1.Yw d w ≤ (d : ℝ) * 4 ^ d * w ^ 2 := by
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 3 := ⟨d - 3, by omega⟩
  unfold CltMom1.Yw CltMom1.cs
  have h4 : (4 : ℝ) ^ (e + 3) = 2 * 2 ^ (e + 3 - 1) * 2 ^ (e + 3 - 2) * 4 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul]
    simp only [show e + 3 - 1 = e + 2 by omega, show e + 3 - 2 = e + 1 by omega]
    rw [show (2 : ℝ) ^ 2 = 4 by norm_num]
    ring_nf
  have hw2 : (w + 1) ^ 2 ≤ 4 * w ^ 2 := by nlinarith
  have hc : (0 : ℝ) ≤ 2 * ((e + 3 : ℕ) : ℝ) * 2 ^ (e + 3 - 1) * 2 ^ (e + 3 - 2) := by positivity
  calc 2 * ((e + 3 : ℕ) : ℝ) * 2 ^ (e + 3 - 1) * 2 ^ (e + 3 - 2) * (w + 1) ^ 2
      ≤ 2 * ((e + 3 : ℕ) : ℝ) * 2 ^ (e + 3 - 1) * 2 ^ (e + 3 - 2) * (4 * w ^ 2) :=
        mul_le_mul_of_nonneg_left hw2 hc
    _ = ((e + 3 : ℕ) : ℝ) * (2 * 2 ^ (e + 3 - 1) * 2 ^ (e + 3 - 2) * 4) * w ^ 2 := by ring
    _ = ((e + 3 : ℕ) : ℝ) * 4 ^ (e + 3) * w ^ 2 := by rw [h4]

/-- The window constants for the cluster radius `R_b = 20 w`:
`Y_w ((2 R_b + 1)^d Y_w)^m ≤ (41^d)^m (d 4^d)^{m+1} w^{(d+2) m + 2}` for `w ≥ 1`. -/
theorem cltMom1_Yw_bound (hd : 3 ≤ d) {w : ℝ} (hw : 1 ≤ w) (m : ℕ) :
    CltMom1.Yw d w * ((2 * (20 * w) + 1) ^ d * CltMom1.Yw d w) ^ m ≤
      (41 ^ d) ^ m * ((d : ℝ) * 4 ^ d) ^ (m + 1) * w ^ ((d + 2) * m + 2) := by
  have hw0 : 0 ≤ w := by linarith
  have hY := CltMom1.Yw_le hd hw
  have hY0 := CltMom1.Yw_nonneg (d := d) (by omega) w
  have hN : (2 * (20 * w) + 1) ^ d ≤ 41 ^ d * w ^ d := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by linarith) (by linarith) d
  have h1 : (2 * (20 * w) + 1) ^ d * CltMom1.Yw d w ≤ 41 ^ d * w ^ d * ((d : ℝ) * 4 ^ d * w ^ 2) :=
    mul_le_mul hN hY hY0 (by positivity)
  calc CltMom1.Yw d w * ((2 * (20 * w) + 1) ^ d * CltMom1.Yw d w) ^ m
      ≤ ((d : ℝ) * 4 ^ d * w ^ 2) * (41 ^ d * w ^ d * ((d : ℝ) * 4 ^ d * w ^ 2)) ^ m :=
        mul_le_mul hY (pow_le_pow_left₀ (by positivity) h1 m) (by positivity) (by positivity)
    _ = (41 ^ d) ^ m * ((d : ℝ) * 4 ^ d) ^ (m + 1) * w ^ ((d + 2) * m + 2) := by
        have : (w ^ d * w ^ 2) ^ m * w ^ 2 = w ^ ((d + 2) * m + 2) := by
          rw [← pow_add, ← pow_mul, ← pow_add]
        calc ((d : ℝ) * 4 ^ d * w ^ 2) * (41 ^ d * w ^ d * ((d : ℝ) * 4 ^ d * w ^ 2)) ^ m
            = (41 ^ d) ^ m * ((d : ℝ) * 4 ^ d) ^ (m + 1) * ((w ^ d * w ^ 2) ^ m * w ^ 2) := by
              rw [show 41 ^ d * w ^ d * ((d : ℝ) * 4 ^ d * w ^ 2) =
                  (41 ^ d * ((d : ℝ) * 4 ^ d)) * (w ^ d * w ^ 2) by ring, mul_pow, mul_pow]
              ring
          _ = _ := by rw [this]

/-- **Target 4, the explicit constant**: for `w ≥ 1`, the cluster radius `R_b = 20 w = 2R`
(`R = 10 w`, `w = (log W)³ ℓ_s`), a cluster with `m = |A| - 1` further indices contributes at most
`(41^d)^m (d 4^d)^{m+1} w^{(d+2) m + 2}`: this is the factor `(ℓ_s^{d+2})^{|A|-1} ℓ_s²` of `(eq:2p_product_pair)`
(`3_5:2233`) with `ℓ_s` replaced by the window `w = (log W)³ ℓ_s`. -/
theorem cltMom1_cluster_sum_C4 (hd : 3 ≤ d) {w : ℝ} (hw : 1 ≤ w) (m : ℕ) (x : Zd d L) :
    ∑ b₂ : Zd d L, ∑ β : Fin m → (Fin 2 → Zd d L),
      CltMom1.G d L w (x - b₂) * ∏ k : Fin m,
        (if ((zdistInf d L ((β k) 0 - x) : ℕ) : ℝ) ≤ 20 * w then
          CltMom1.G d L w ((β k) 0 - (β k) 1) else 0) ≤
      (41 ^ d) ^ m * ((d : ℝ) * 4 ^ d) ^ (m + 1) * w ^ ((d + 2) * m + 2) :=
  (cltMom1_cluster_sum hd (by linarith : (0 : ℝ) ≤ w) (by linarith : (0 : ℝ) ≤ 20 * w) m x).trans
    (cltMom1_Yw_bound hd hw m)

/-- **The per-cluster term** `∑_β z_β (∑_{β' ∈ ball R_b β} z_{β'})^k` of `cltMom1_clusterSum_le_of_bound`
(`k = |A| - 1` further indices) in terms of a weight `u` at the representative's first label and the window profile
`G_w`: if for every `β` with `z β > 0` and every `β'` with `|β₁ - β₁'| ≤ R_b` one has `z β' ≤ u(β₁) G_w(β₁' - β₂')` (this
contains `β' = β`; it is the output of the weights of target 2 and the comparability of target 3), then the term is at most
`(∑_x u(x)^{k+1}) · Y_w ((2R_b+1)^d Y_w)^k`.  The first factor is the sum of `(eq:simplecalculus)` (`u = ` weight at `a₁` times
weight at `a₂`, on the far region), the second is target 4. -/
theorem cltMom1_term_le (hd : 3 ≤ d) {w Rb : ℝ} (hw : 0 ≤ w) (hRb : 0 ≤ Rb) {u : Zd d L → ℝ}
    (hu0 : ∀ x, 0 ≤ u x) {z : (Fin 2 → Zd d L) → ℝ} (hz0 : ∀ β, 0 ≤ z β)
    (hzu : ∀ β β' : Fin 2 → Zd d L, 0 < z β → ((zdistInf d L (β 0 - β' 0) : ℕ) : ℝ) ≤ Rb →
      z β' ≤ u (β 0) * CltMom1.G d L w (β' 0 - β' 1)) (k : ℕ) :
    ∑ β, z β * (∑ β' ∈ CltMom1.ball Rb β, z β') ^ k ≤
      (∑ x, u x ^ (k + 1)) * (CltMom1.Yw d w * ((2 * Rb + 1) ^ d * CltMom1.Yw d w) ^ k) := by
  classical
  have hY0 := CltMom1.Yw_nonneg (d := d) (by omega) w
  set NY : ℝ := (2 * Rb + 1) ^ d * CltMom1.Yw d w with hNY
  have hNY0 : 0 ≤ NY := by positivity
  have hpt : ∀ β : Fin 2 → Zd d L, z β * (∑ β' ∈ CltMom1.ball Rb β, z β') ^ k ≤
      u (β 0) ^ (k + 1) * CltMom1.G d L w (β 0 - β 1) * NY ^ k := by
    intro β
    by_cases hzb : 0 < z β
    · have hself : ((zdistInf d L (β 0 - β 0) : ℕ) : ℝ) ≤ Rb := by
        rw [sub_self, cltMom1_zdistInf_zero]; simpa using hRb
      have h1 : z β ≤ u (β 0) * CltMom1.G d L w (β 0 - β 1) := hzu β β hzb hself
      have h2 : ∑ β' ∈ CltMom1.ball Rb β, z β' ≤ u (β 0) * NY := by
        calc ∑ β' ∈ CltMom1.ball Rb β, z β'
            ≤ ∑ β' ∈ CltMom1.ball Rb β, u (β 0) * CltMom1.G d L w (β' 0 - β' 1) := by
              refine Finset.sum_le_sum fun β' hβ' => hzu β β' hzb ?_
              exact (Finset.mem_filter.1 hβ').2
          _ = u (β 0) * ∑ β' ∈ CltMom1.ball Rb β, CltMom1.G d L w (β' 0 - β' 1) := by
              rw [Finset.mul_sum]
          _ ≤ u (β 0) * NY := mul_le_mul_of_nonneg_left (cltMom1_ball_G_sum hd hw hRb β) (hu0 _)
      have hS0 : 0 ≤ ∑ β' ∈ CltMom1.ball Rb β, z β' := Finset.sum_nonneg fun β' _ => hz0 β'
      calc z β * (∑ β' ∈ CltMom1.ball Rb β, z β') ^ k
          ≤ (u (β 0) * CltMom1.G d L w (β 0 - β 1)) * (u (β 0) * NY) ^ k :=
            mul_le_mul h1 (pow_le_pow_left₀ hS0 h2 k) (by positivity)
              (mul_nonneg (hu0 _) (CltMom1.G_nonneg _ _))
        _ = u (β 0) ^ (k + 1) * CltMom1.G d L w (β 0 - β 1) * NY ^ k := by
            rw [mul_pow, pow_succ]; ring
    · have : z β = 0 := le_antisymm (not_lt.1 hzb) (hz0 β)
      rw [this, zero_mul]
      have := hu0 (β 0)
      have := CltMom1.G_nonneg w (β 0 - β 1)
      positivity
  calc ∑ β, z β * (∑ β' ∈ CltMom1.ball Rb β, z β') ^ k
      ≤ ∑ β : Fin 2 → Zd d L, u (β 0) ^ (k + 1) * CltMom1.G d L w (β 0 - β 1) * NY ^ k :=
        Finset.sum_le_sum fun β _ => hpt β
    _ = (∑ u₀ : Zd d L, u u₀ ^ (k + 1) * ∑ u₁ : Zd d L, CltMom1.G d L w (u₀ - u₁)) * NY ^ k := by
        rw [← Finset.sum_mul]
        congr 1
        rw [cltMom1_sum_pair (fun u₀ u₁ => u u₀ ^ (k + 1) * CltMom1.G d L w (u₀ - u₁))]
        refine Finset.sum_congr rfl fun u₀ _ => ?_
        rw [Finset.mul_sum]
    _ ≤ (∑ u₀ : Zd d L, u u₀ ^ (k + 1) * CltMom1.Yw d w) * NY ^ k := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        refine Finset.sum_le_sum fun u₀ _ => ?_
        exact mul_le_mul_of_nonneg_left (cltMom1_G_sum_sub_le hd hw u₀) (by have := hu0 u₀; positivity)
    _ = (∑ x, u x ^ (k + 1)) * (CltMom1.Yw d w * NY ^ k) := by
        rw [← Finset.sum_mul]; ring

end ClusterSum

/-! ## 7. `(eq:simplecalculus)` for `k ≥ 2`, `d ≥ 3` (target 5) -/

section SimpleCalculus

variable {d L : ℕ} [NeZero L]

private theorem cltMom1_calc_E1 {m : ℕ} {A D : ℝ} (hA : 0 ≤ A) (hD : 0 ≤ D) (h : D ≤ 2 * A) :
    1 / (A ^ m + 1) ≤ 2 ^ m / (D ^ m + 1) := by
  have h2m : (0 : ℝ) < 2 ^ m := pow_pos two_pos m
  have hp : (D / 2) ^ m ≤ A ^ m := pow_le_pow_left₀ (by positivity) (by linarith) m
  have hDm : D ^ m = 2 ^ m * (D / 2) ^ m := by rw [← mul_pow]; congr 1; ring
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have h1 : (1 : ℝ) ≤ 2 ^ m := one_le_pow₀ (by norm_num)
  have h3 := mul_le_mul_of_nonneg_left hp h2m.le
  nlinarith

private theorem cltMom1_calc_E2 {m : ℕ} (hm : 1 ≤ m) {B : ℝ} (hB : 0 ≤ B) :
    (B ^ m + 1) * (B + 1) ≤ 3 * (B ^ (m + 1) + 1) := by
  have hexp : (B ^ m + 1) * (B + 1) = B ^ (m + 1) + B ^ m + B + 1 := by rw [pow_succ]; ring
  rw [hexp]
  rcases le_total B 1 with h | h
  · have h1 : B ^ m ≤ 1 := pow_le_one₀ hB h
    have h2 : 0 ≤ B ^ (m + 1) := pow_nonneg hB _
    linarith
  · have h1 : B ^ m ≤ B ^ (m + 1) := pow_le_pow_right₀ h (by omega)
    have h2 : B ≤ B ^ (m + 1) := by
      calc B = B ^ 1 := (pow_one B).symm
        _ ≤ B ^ (m + 1) := pow_le_pow_right₀ h (by omega)
    linarith

/-- The pointwise form of `(eq:simplecalculus)`, `m = d - 2`: with `D ≤ A + B` (`D = |a₁-a₂|`, `A = |a₁-b|`,
`B = |a₂-b|`), `(A^m+1)^{-q} (λ/(B^{m+1}+1))^q ≤ (3·2^m)^q (D^m+1)^{-q} λ^q ((A^{m+1}+1)^{-q} + (B^{m+1}+1)^{-q})`.
Case `A ≥ B` (so `D ≤ 2A`): the factor at `a₁` carries the decay in `D`; case `A < B` (`D ≤ 2B`): the decay in `D` is
taken from `B` via `B^{m+1} + 1 ≥ (B^m+1)(B+1)/3` and `B ≥ A`. -/
private theorem cltMom1_calc_point {m : ℕ} (hm : 1 ≤ m) {A B D lam : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hD : 0 ≤ D) (hDAB : D ≤ A + B) (hlam : 0 ≤ lam) (q : ℕ) :
    (1 / (A ^ m + 1)) ^ q * (lam / (B ^ (m + 1) + 1)) ^ q ≤
      (3 * 2 ^ m) ^ q * (1 / (D ^ m + 1)) ^ q * lam ^ q *
        ((1 / (A ^ (m + 1) + 1)) ^ q + (1 / (B ^ (m + 1) + 1)) ^ q) := by
  have hu : 0 ≤ (1 / (D ^ m + 1)) ^ q := by positivity
  have ha : 0 ≤ (1 / (A ^ (m + 1) + 1)) ^ q := by positivity
  have hb : 0 ≤ (1 / (B ^ (m + 1) + 1)) ^ q := by positivity
  have hlq : 0 ≤ lam ^ q := pow_nonneg hlam q
  have h2q : (0 : ℝ) ≤ (2 ^ m) ^ q := by positivity
  have h3q : (1 : ℝ) ≤ 3 ^ q := one_le_pow₀ (by norm_num)
  have hK : (3 * 2 ^ m : ℝ) ^ q = 3 ^ q * (2 ^ m) ^ q := mul_pow _ _ _
  have hlam_split : ∀ x : ℝ, (lam / x) ^ q = lam ^ q * (1 / x) ^ q := fun x => by
    rw [div_eq_mul_one_div, mul_pow]
  rw [hlam_split]
  rcases le_total B A with hBA | hAB
  · -- `A ≥ B`, `D ≤ 2A`
    have h1 := cltMom1_calc_E1 (m := m) hA hD (by linarith)
    have h1q : (1 / (A ^ m + 1)) ^ q ≤ (2 ^ m) ^ q * (1 / (D ^ m + 1)) ^ q := by
      rw [← mul_pow, ← div_eq_mul_one_div]
      exact pow_le_pow_left₀ (by positivity) h1 q
    calc (1 / (A ^ m + 1)) ^ q * (lam ^ q * (1 / (B ^ (m + 1) + 1)) ^ q)
        ≤ ((2 ^ m) ^ q * (1 / (D ^ m + 1)) ^ q) * (lam ^ q * (1 / (B ^ (m + 1) + 1)) ^ q) :=
          mul_le_mul_of_nonneg_right h1q (by positivity)
      _ = (2 ^ m) ^ q * (1 / (D ^ m + 1)) ^ q * lam ^ q * (1 / (B ^ (m + 1) + 1)) ^ q := by ring
      _ ≤ 3 ^ q * (2 ^ m) ^ q * (1 / (D ^ m + 1)) ^ q * lam ^ q *
            ((1 / (A ^ (m + 1) + 1)) ^ q + (1 / (B ^ (m + 1) + 1)) ^ q) := by
          have hc : 0 ≤ (2 ^ m) ^ q * (1 / (D ^ m + 1)) ^ q * lam ^ q := by positivity
          have : (2 ^ m) ^ q * (1 / (D ^ m + 1)) ^ q * lam ^ q * (1 / (B ^ (m + 1) + 1)) ^ q ≤
              (3 ^ q * ((2 ^ m) ^ q * (1 / (D ^ m + 1)) ^ q * lam ^ q)) *
                ((1 / (A ^ (m + 1) + 1)) ^ q + (1 / (B ^ (m + 1) + 1)) ^ q) := by
            calc _ = ((2 ^ m) ^ q * (1 / (D ^ m + 1)) ^ q * lam ^ q) * (1 / (B ^ (m + 1) + 1)) ^ q := rfl
              _ ≤ ((2 ^ m) ^ q * (1 / (D ^ m + 1)) ^ q * lam ^ q) * (1 * ((1 / (A ^ (m + 1) + 1)) ^ q + (1 / (B ^ (m + 1) + 1)) ^ q)) :=
                  mul_le_mul_of_nonneg_left (by linarith) hc
              _ ≤ ((2 ^ m) ^ q * (1 / (D ^ m + 1)) ^ q * lam ^ q) * (3 ^ q * ((1 / (A ^ (m + 1) + 1)) ^ q + (1 / (B ^ (m + 1) + 1)) ^ q)) :=
                  mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h3q (by positivity)) hc
              _ = _ := by ring
          calc _ ≤ _ := this
            _ = _ := by ring
      _ = _ := by rw [hK]
  · -- `A < B`, `D ≤ 2B`
    have hB1 := cltMom1_calc_E1 (m := m) hB hD (by linarith)
    have hE2 := cltMom1_calc_E2 hm hB
    have hB2 : 1 / (B ^ (m + 1) + 1) ≤ 3 * 2 ^ m * (1 / (D ^ m + 1)) * (1 / (A + 1)) := by
      have h1 : 1 / (B ^ (m + 1) + 1) ≤ 3 / ((B ^ m + 1) * (B + 1)) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        linarith
      have h2 : 3 / ((B ^ m + 1) * (B + 1)) = 3 * (1 / (B ^ m + 1)) * (1 / (B + 1)) := by
        field_simp
      have h3 : 1 / (B + 1) ≤ 1 / (A + 1) := one_div_le_one_div_of_le (by positivity) (by linarith)
      have h4 : 1 / (B ^ m + 1) ≤ 2 ^ m / (D ^ m + 1) := hB1
      calc 1 / (B ^ (m + 1) + 1) ≤ 3 * (1 / (B ^ m + 1)) * (1 / (B + 1)) := h1.trans h2.le
        _ ≤ 3 * (2 ^ m / (D ^ m + 1)) * (1 / (A + 1)) := by gcongr
        _ = 3 * 2 ^ m * (1 / (D ^ m + 1)) * (1 / (A + 1)) := by ring
    have hA3 : (1 / (A ^ m + 1)) * (1 / (A + 1)) ≤ 1 / (A ^ (m + 1) + 1) := by
      rw [one_div_mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [pow_nonneg hA m, pow_nonneg hA (m + 1), pow_succ A m]
    have hX : (1 / (A ^ m + 1)) * (1 / (B ^ (m + 1) + 1)) ≤
        3 * 2 ^ m * (1 / (D ^ m + 1)) * (1 / (A ^ (m + 1) + 1)) := by
      calc (1 / (A ^ m + 1)) * (1 / (B ^ (m + 1) + 1))
          ≤ (1 / (A ^ m + 1)) * (3 * 2 ^ m * (1 / (D ^ m + 1)) * (1 / (A + 1))) :=
            mul_le_mul_of_nonneg_left hB2 (by positivity)
        _ = 3 * 2 ^ m * (1 / (D ^ m + 1)) * ((1 / (A ^ m + 1)) * (1 / (A + 1))) := by ring
        _ ≤ 3 * 2 ^ m * (1 / (D ^ m + 1)) * (1 / (A ^ (m + 1) + 1)) :=
            mul_le_mul_of_nonneg_left hA3 (by positivity)
    have hXq := pow_le_pow_left₀ (by positivity) hX q
    have e1 : (1 / (A ^ m + 1)) ^ q * (1 / (B ^ (m + 1) + 1)) ^ q =
        ((1 / (A ^ m + 1)) * (1 / (B ^ (m + 1) + 1))) ^ q := (mul_pow _ _ _).symm
    have e2 : (3 * 2 ^ m * (1 / (D ^ m + 1)) * (1 / (A ^ (m + 1) + 1))) ^ q =
        (3 * 2 ^ m) ^ q * (1 / (D ^ m + 1)) ^ q * (1 / (A ^ (m + 1) + 1)) ^ q := by
      rw [mul_pow, mul_pow]
    rw [e2] at hXq
    rw [← e1] at hXq
    calc (1 / (A ^ m + 1)) ^ q * (lam ^ q * (1 / (B ^ (m + 1) + 1)) ^ q)
        = lam ^ q * ((1 / (A ^ m + 1)) ^ q * (1 / (B ^ (m + 1) + 1)) ^ q) := by ring
      _ ≤ lam ^ q * ((3 * 2 ^ m) ^ q * (1 / (D ^ m + 1)) ^ q * (1 / (A ^ (m + 1) + 1)) ^ q) :=
          mul_le_mul_of_nonneg_left hXq hlq
      _ ≤ (3 * 2 ^ m) ^ q * (1 / (D ^ m + 1)) ^ q * lam ^ q *
            ((1 / (A ^ (m + 1) + 1)) ^ q + (1 / (B ^ (m + 1) + 1)) ^ q) := by
          have : 0 ≤ (3 * 2 ^ m : ℝ) ^ q * (1 / (D ^ m + 1)) ^ q * lam ^ q := by positivity
          nlinarith [mul_nonneg this hb]

/-- **Target 5: `(eq:simplecalculus)`** (`3_5:2234-2241`) for `k = q ≥ 2`, `d ≥ 3`.  For `ρ > 0`, `λ ≥ 0`,
`∑_{b : |a₁-b| ∧ |a₂-b| > ρ} (|a₁-b|^{d-2}+1)^{-q} (λ/(|a₂-b|^{d-1}+1))^q ≤
C(d,q) (|a₁-a₂|^{d-2}+1)^{-q} λ^q / ρ^{(d-1)q-d}`, `C(d,q) = 2 cs (3·2^{2d-3})^q`, `cs = 2 d 2^{d-1}`.
Both cases `|a₁-b| ≷ |a₂-b|` are in `cltMom1_calc_point`.  `(d-1)q > d` is used exactly in the tail
`∑_{|x|>ρ} (|x|^{d-1}+1)^{-q} ≲ ρ^{-((d-1)q-d)}` (`cltMom1_tail_sum`, exponent `(d-1)q - d ≥ d - 2 ≥ 1`); at `q = 1`
the exponent is `-1` and the sum over the far region grows like `L` (preflight script: ratio `121.6, 298.4, 649.3` at
`L = 31, 63, 127`).  The paper's numerator `ℓ_s` is the parameter `λ` (BD1's numerator is `C (log W)³ ℓ_s`, so
`S5-24` takes `λ = w`; paper-delta candidate `T2165b`); the ticket-literal form is `cltMom1_simplecalculus_ell`. -/
theorem cltMom1_simplecalculus (hd : 3 ≤ d) {q : ℕ} (hq : 2 ≤ q) {ρ lam : ℝ} (hρ : 0 < ρ)
    (hlam : 0 ≤ lam) (a₁ a₂ : Zd d L) :
    ∑ b ∈ Finset.univ.filter (fun b : Zd d L =>
        ρ < ((zdistInf d L (a₁ - b) : ℕ) : ℝ) ∧ ρ < ((zdistInf d L (a₂ - b) : ℕ) : ℝ)),
      (1 / (((zdistInf d L (a₁ - b) : ℕ) : ℝ) ^ (d - 2) + 1)) ^ q *
        (lam / (((zdistInf d L (a₂ - b) : ℕ) : ℝ) ^ (d - 1) + 1)) ^ q ≤
      (2 * CltMom1.cs d * (3 * 2 ^ (2 * d - 3)) ^ q) *
        (1 / (((zdistInf d L (a₁ - a₂) : ℕ) : ℝ) ^ (d - 2) + 1)) ^ q * (lam ^ q / ρ ^ ((d - 1) * q - d)) := by
  classical
  have hm : 1 ≤ d - 2 := by omega
  have hdd : d - 2 + 1 = d - 1 := by omega
  set D : ℝ := ((zdistInf d L (a₁ - a₂) : ℕ) : ℝ) with hDdef
  have hD0 : 0 ≤ D := Nat.cast_nonneg _
  set H : ℝ → ℝ := fun r => if ρ < r then 1 / (r ^ (d - 1) + 1) ^ q else 0 with hH
  have hH0 : ∀ r, 0 ≤ H r := fun r => by
    simp only [hH]
    split_ifs with h
    · have hr : 0 < r := lt_trans hρ h
      positivity
    · exact le_rfl
  have hcs := CltMom1.cs_pos (d := d) (by omega)
  have hT := cltMom1_tail_sum (d := d) (L := L) hd hq hρ
  -- the sum of `H(|a - b|)` over all `b`
  have hHa : ∀ a : Zd d L, ∑ b : Zd d L, H ((zdistInf d L (a - b) : ℕ) : ℝ) ≤
      CltMom1.cs d * 2 ^ ((d - 1) * q) / ρ ^ ((d - 1) * q - d) := by
    intro a
    rw [cltMom1_sum_sub_left (fun x : Zd d L => H ((zdistInf d L x : ℕ) : ℝ)) a]
    exact hT
  set K : ℝ := (3 * 2 ^ (d - 2)) ^ q with hK
  set u : ℝ := (1 / (D ^ (d - 2) + 1)) ^ q with hu
  have hu0 : 0 ≤ u := by positivity
  have hK0 : 0 ≤ K := by positivity
  have hlq : 0 ≤ lam ^ q := pow_nonneg hlam q
  have hpt : ∀ b ∈ Finset.univ.filter (fun b : Zd d L =>
        ρ < ((zdistInf d L (a₁ - b) : ℕ) : ℝ) ∧ ρ < ((zdistInf d L (a₂ - b) : ℕ) : ℝ)),
      (1 / (((zdistInf d L (a₁ - b) : ℕ) : ℝ) ^ (d - 2) + 1)) ^ q *
        (lam / (((zdistInf d L (a₂ - b) : ℕ) : ℝ) ^ (d - 1) + 1)) ^ q ≤
      K * u * lam ^ q * (H ((zdistInf d L (a₁ - b) : ℕ) : ℝ) + H ((zdistInf d L (a₂ - b) : ℕ) : ℝ)) := by
    intro b hb
    obtain ⟨hb1, hb2⟩ := (Finset.mem_filter.1 hb).2
    have hDAB : D ≤ ((zdistInf d L (a₁ - b) : ℕ) : ℝ) + ((zdistInf d L (a₂ - b) : ℕ) : ℝ) := by
      have h1 := cltMom1_zdistInf_tri a₁ b a₂
      rw [cltMom1_zdistInf_sub_comm b a₂] at h1
      rw [hDdef]; exact_mod_cast h1
    have hpt := cltMom1_calc_point hm (A := ((zdistInf d L (a₁ - b) : ℕ) : ℝ))
      (B := ((zdistInf d L (a₂ - b) : ℕ) : ℝ)) (D := D) (lam := lam) (Nat.cast_nonneg _)
      (Nat.cast_nonneg _) (Nat.cast_nonneg _) hDAB hlam q
    rw [hdd] at hpt
    have e1 : H ((zdistInf d L (a₁ - b) : ℕ) : ℝ) = (1 / (((zdistInf d L (a₁ - b) : ℕ) : ℝ) ^ (d - 1) + 1)) ^ q := by
      simp only [hH, hb1, ↓reduceIte, one_div_pow]
    have e2 : H ((zdistInf d L (a₂ - b) : ℕ) : ℝ) = (1 / (((zdistInf d L (a₂ - b) : ℕ) : ℝ) ^ (d - 1) + 1)) ^ q := by
      simp only [hH, hb2, ↓reduceIte, one_div_pow]
    rw [e1, e2]
    exact hpt
  have hsub : ∑ b ∈ Finset.univ.filter (fun b : Zd d L =>
        ρ < ((zdistInf d L (a₁ - b) : ℕ) : ℝ) ∧ ρ < ((zdistInf d L (a₂ - b) : ℕ) : ℝ)),
      (H ((zdistInf d L (a₁ - b) : ℕ) : ℝ) + H ((zdistInf d L (a₂ - b) : ℕ) : ℝ)) ≤
      ∑ b : Zd d L, (H ((zdistInf d L (a₁ - b) : ℕ) : ℝ) + H ((zdistInf d L (a₂ - b) : ℕ) : ℝ)) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun b _ _ =>
      add_nonneg (hH0 _) (hH0 _)
  calc _ ≤ ∑ b ∈ Finset.univ.filter (fun b : Zd d L =>
        ρ < ((zdistInf d L (a₁ - b) : ℕ) : ℝ) ∧ ρ < ((zdistInf d L (a₂ - b) : ℕ) : ℝ)),
      K * u * lam ^ q * (H ((zdistInf d L (a₁ - b) : ℕ) : ℝ) + H ((zdistInf d L (a₂ - b) : ℕ) : ℝ)) :=
        Finset.sum_le_sum hpt
    _ = K * u * lam ^ q * ∑ b ∈ Finset.univ.filter (fun b : Zd d L =>
        ρ < ((zdistInf d L (a₁ - b) : ℕ) : ℝ) ∧ ρ < ((zdistInf d L (a₂ - b) : ℕ) : ℝ)),
      (H ((zdistInf d L (a₁ - b) : ℕ) : ℝ) + H ((zdistInf d L (a₂ - b) : ℕ) : ℝ)) := by
        rw [Finset.mul_sum]
    _ ≤ K * u * lam ^ q * ∑ b : Zd d L, (H ((zdistInf d L (a₁ - b) : ℕ) : ℝ) +
          H ((zdistInf d L (a₂ - b) : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_left hsub (by positivity)
    _ ≤ K * u * lam ^ q * (2 * (CltMom1.cs d * 2 ^ ((d - 1) * q) / ρ ^ ((d - 1) * q - d))) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        rw [Finset.sum_add_distrib]
        linarith [hHa a₁, hHa a₂]
    _ = (2 * CltMom1.cs d * (3 * 2 ^ (2 * d - 3)) ^ q) * u * (lam ^ q / ρ ^ ((d - 1) * q - d)) := by
        have e : (3 * 2 ^ (2 * d - 3) : ℝ) ^ q = K * 2 ^ ((d - 1) * q) := by
          have h1 : (3 * 2 ^ (2 * d - 3) : ℝ) = (3 * 2 ^ (d - 2)) * 2 ^ (d - 1) := by
            rw [mul_assoc, ← pow_add]; congr 2; omega
          rw [h1, mul_pow, ← pow_mul, hK]
        rw [e]
        ring

/-- **Target 5, the ticket-literal form**: with `λ = ℓ` and the far cutoff `ρ ≥ ℓ ≥ 1`
(`ρ = (log W)⁴ ℓ_s`, `ℓ ≤ ρ` for `log W ≥ 1`), the sum of `(eq:simplecalculus)` is at most
`C(d,q) (|a₁-a₂|^{d-2}+1)^{-q} ℓ^d / (ℓ^{d-2})^q`. -/
theorem cltMom1_simplecalculus_ell (hd : 3 ≤ d) {q : ℕ} (hq : 2 ≤ q) {ρ ℓ : ℝ} (hℓ : 1 ≤ ℓ)
    (hℓρ : ℓ ≤ ρ) (a₁ a₂ : Zd d L) :
    ∑ b ∈ Finset.univ.filter (fun b : Zd d L =>
        ρ < ((zdistInf d L (a₁ - b) : ℕ) : ℝ) ∧ ρ < ((zdistInf d L (a₂ - b) : ℕ) : ℝ)),
      (1 / (((zdistInf d L (a₁ - b) : ℕ) : ℝ) ^ (d - 2) + 1)) ^ q *
        (ℓ / (((zdistInf d L (a₂ - b) : ℕ) : ℝ) ^ (d - 1) + 1)) ^ q ≤
      (2 * CltMom1.cs d * (3 * 2 ^ (2 * d - 3)) ^ q) *
        (1 / (((zdistInf d L (a₁ - a₂) : ℕ) : ℝ) ^ (d - 2) + 1)) ^ q * (ℓ ^ d / (ℓ ^ (d - 2)) ^ q) := by
  have hρ : 0 < ρ := by linarith
  have hℓ0 : 0 < ℓ := by linarith
  have hcs := CltMom1.cs_pos (d := d) (by omega)
  refine (cltMom1_simplecalculus hd hq hρ hℓ0.le a₁ a₂).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  obtain ⟨E, hE⟩ : ∃ E : ℕ, (d - 1) * q = d + E := by
    refine ⟨(d - 1) * q - d, ?_⟩
    have : d ≤ (d - 1) * q := by
      calc d ≤ (d - 1) * 2 := by omega
        _ ≤ (d - 1) * q := Nat.mul_le_mul_left _ hq
    omega
  have hexp : (d - 1) * q - d = E := by omega
  rw [hexp]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  -- `ℓ^q (ℓ^{d-2})^q ≤ ℓ^d ρ^E`, i.e. `ℓ^{(d-1)q} = ℓ^{d+E} ≤ ℓ^d ρ^E`
  have h1 : ℓ ^ q * (ℓ ^ (d - 2)) ^ q = ℓ ^ d * ℓ ^ E := by
    rw [← pow_mul, ← pow_add, ← pow_add]
    congr 1
    have : q + (d - 2) * q = (d - 1) * q := by
      rw [show d - 1 = (d - 2) + 1 by omega]; ring
    omega
  rw [h1]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hℓ0.le hℓρ E) (by positivity)

end SimpleCalculus

/-! ## 8. The exponent count (target 6) and the assembly -/

section ExponentCount

variable {d L : ℕ} [NeZero L]

/-- **Target 6a: the exponent identity of `(eq:2p_product_pair)`**: for a cluster with `k = |A|` indices the exponents
of `ℓ_s` are `d - (d-2)k` (the sum `(eq:simplecalculus)`), `(d+2)(k-1)` and `2` (target 4), total `4k`, for all `d, k`. -/
theorem cltMom1_exponent_identity (d k : ℕ) :
    (d : ℤ) - ((d : ℤ) - 2) * k + ((d : ℤ) + 2) * ((k : ℤ) - 1) + 2 = 4 * k := by ring

/-- **Target 6b: the exponents in natural numbers.**  For a cluster with `m + 1 = |A|` indices, `m ≥ 1`, `d ≥ 3`: with
`E = (d-1)(m+1) - d` (the power of `ρ` in `(eq:simplecalculus)`; `E ≥ d - 2 ≥ 1` is `(d-1)(m+1) > d`) the power of the window
`w` in the cluster factor (`w^{m+1}` from `λ = w`, `w^{(d+2)m+2}` from target 4) is `(m+1) + ((d+2)m+2) = E + 4(m+1)`. -/
theorem cltMom1_exponent_nat {d m : ℕ} (hd : 3 ≤ d) (hm : 1 ≤ m) :
    ∃ E : ℕ, (d - 1) * (m + 1) - d = E ∧ (d - 1) * (m + 1) = d + E ∧ 1 ≤ E ∧
      (m + 1) + ((d + 2) * m + 2) = E + 4 * (m + 1) := by
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 3 := ⟨d - 3, by omega⟩
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
  have h1 : e + 3 - 1 = e + 2 := by omega
  rw [h1]
  refine ⟨e * j + e + 2 * j + 1, ?_, ?_, ?_, ?_⟩
  · have : (e + 2) * (j + 1 + 1) = (e + 3) + (e * j + e + 2 * j + 1) := by ring
    omega
  · ring
  · omega
  · ring

/-- **Target 6c: the scale count of a cluster.**  With `lw = log W ≥ 1`, `ℓ = ℓ_s > 0`, `w = lw³ ℓ`, `ρ = lw⁴ ℓ`, for a cluster
with `m + 1 = |A|` indices (`m ≥ 1`, `d ≥ 3`):
`w^{(m+1)} w^{(d+2)m+2} / ρ^{(d-1)(m+1)-d} ≤ ℓ^{4(m+1)} lw^{12 (m+1)}`.  The power of `ℓ_s` is exactly `4(m+1) = 4|A|`
(`cltMom1_exponent_identity`); the power of `log W` is `3((d+3)|A|-d) - 4((d-1)|A|-d) = d + (13-d)|A| ≤ 12|A|` (the paper's `≺`
hides it; paper-delta candidate `T2165c`). -/
theorem cltMom1_exponent_count {d m : ℕ} (hd : 3 ≤ d) (hm : 1 ≤ m) {lw ℓ : ℝ} (hlw : 1 ≤ lw) (hℓ : 0 < ℓ) :
    (lw ^ 3 * ℓ) ^ ((m + 1) + ((d + 2) * m + 2)) / (lw ^ 4 * ℓ) ^ ((d - 1) * (m + 1) - d) ≤
      ℓ ^ (4 * (m + 1)) * lw ^ (12 * (m + 1)) := by
  obtain ⟨E, hE, -, -, hN⟩ := cltMom1_exponent_nat hd hm
  rw [hE, hN, pow_add]
  have hlw0 : 0 < lw := by linarith
  have hrat : (lw ^ 3 * ℓ) ^ E / (lw ^ 4 * ℓ) ^ E ≤ 1 := by
    rw [← div_pow]
    apply pow_le_one₀ (by positivity)
    rw [div_le_one (by positivity)]
    have : lw ^ 3 ≤ lw ^ 4 := pow_le_pow_right₀ hlw (by norm_num)
    nlinarith
  calc (lw ^ 3 * ℓ) ^ E * (lw ^ 3 * ℓ) ^ (4 * (m + 1)) / (lw ^ 4 * ℓ) ^ E
      = ((lw ^ 3 * ℓ) ^ E / (lw ^ 4 * ℓ) ^ E) * (lw ^ 3 * ℓ) ^ (4 * (m + 1)) := by ring
    _ ≤ 1 * (lw ^ 3 * ℓ) ^ (4 * (m + 1)) :=
        mul_le_mul_of_nonneg_right hrat (by positivity)
    _ = ℓ ^ (4 * (m + 1)) * lw ^ (12 * (m + 1)) := by
        rw [one_mul, mul_pow, ← pow_mul, show 3 * (4 * (m + 1)) = 12 * (m + 1) by ring]; ring

/-- **Target 6c, exact form**: for `m + 1 = |A|` indices, `d ≥ 3`, `lw, ℓ > 0`,
`w^{(m+1)} w^{(d+2)m+2} / ρ^{(d-1)(m+1)-d} = ℓ^{4|A|} · lw^{d + (13-d)|A|}`, `w = lw³ ℓ`, `ρ = lw⁴ ℓ` (exponent of `lw` an integer,
`3((d+3)|A| - d) - 4((d-1)|A| - d)`; it is `≤ 12|A|`, which is `cltMom1_exponent_count`). -/
theorem cltMom1_exponent_count_eq {d m : ℕ} (hd : 3 ≤ d) (hm : 1 ≤ m) {lw ℓ : ℝ} (hlw : 0 < lw) (hℓ : 0 < ℓ) :
    (lw ^ 3 * ℓ) ^ ((m + 1) + ((d + 2) * m + 2)) / (lw ^ 4 * ℓ) ^ ((d - 1) * (m + 1) - d) =
      ℓ ^ (4 * (m + 1)) * lw ^ ((d : ℤ) + (13 - (d : ℤ)) * ((m : ℤ) + 1)) := by
  obtain ⟨E, hE, hE1, -, hN⟩ := cltMom1_exponent_nat hd hm
  rw [hE, hN]
  have hEz : ((d : ℤ) - 1) * ((m : ℤ) + 1) = d + E := by
    have := congrArg (Nat.cast : ℕ → ℤ) hE1
    push_cast [Nat.cast_sub (show 1 ≤ d by omega)] at this
    exact this
  have key : lw ^ ((d : ℤ) + (13 - (d : ℤ)) * ((m : ℤ) + 1)) = lw ^ (12 * (m + 1)) / lw ^ E := by
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_sub₀ hlw.ne']
    congr 1
    push_cast
    linarith [hEz]
  rw [key]
  field_simp
  ring

/-- The exact product over the clusters of the factors of `cltMom1_exponent_count_eq`:
`∏_{s ∈ free φ} ℓ^{4|A_s|} lw^{d + (13-d)|A_s|} = ℓ^{4n} lw^{d r + (13-d) n}` (`n = 2p`, `r = #free φ`): the `ℓ_s`-power is
`8p` (the paper's `(ℓ_s⁴)^{2p}`), the `log W`-power `d r + (13-d) 2p` (hidden in the paper's `≺`; `≤ 24 p`). -/
theorem cltMom1_prod_exponent_exact {n : ℕ} {φ : Fin n → Fin n} (hφ : CltMom1.Cluster φ) (d : ℕ)
    {lw ℓ : ℝ} (hlw : 0 < lw) :
    ∏ s ∈ CltMom1.free φ, (ℓ ^ (4 * (CltMom1.assigned φ s + 1)) *
        lw ^ ((d : ℤ) + (13 - (d : ℤ)) * ((CltMom1.assigned φ s : ℤ) + 1))) =
      ℓ ^ (4 * n) * lw ^ ((d : ℤ) * (CltMom1.free φ).card + (13 - (d : ℤ)) * n) := by
  have hz : ∀ (s : Finset (Fin n)) (z : Fin n → ℤ), ∏ i ∈ s, lw ^ z i = lw ^ (∑ i ∈ s, z i) := by
    intro s z
    classical
    induction s using Finset.induction_on with
    | empty => simp
    | insert i s hi ih => rw [Finset.prod_insert hi, Finset.sum_insert hi, ih, zpow_add₀ hlw.ne']
  rw [Finset.prod_mul_distrib, hz, Finset.prod_pow_eq_pow_sum]
  have hsum := cltMom1_sum_assigned hφ
  have hs1 : ∑ s ∈ CltMom1.free φ, 4 * (CltMom1.assigned φ s + 1) = 4 * n := by
    rw [← Finset.mul_sum, Finset.sum_add_distrib]
    simp only [Finset.sum_const, smul_eq_mul, mul_one]
    omega
  have hs2 : ∑ s ∈ CltMom1.free φ, ((d : ℤ) + (13 - (d : ℤ)) * ((CltMom1.assigned φ s : ℤ) + 1)) =
      (d : ℤ) * (CltMom1.free φ).card + (13 - (d : ℤ)) * n := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_add_distrib]
    simp only [Finset.sum_const, mul_one, nsmul_eq_mul]
    have : ((∑ s ∈ CltMom1.free φ, CltMom1.assigned φ s : ℕ) : ℤ) + ((CltMom1.free φ).card : ℤ) = n := by
      exact_mod_cast hsum
    push_cast at this
    linear_combination (13 - (d : ℤ)) * this
  rw [hs1, hs2]

/-- The product over the clusters: `∏_{s ∈ free φ} c X^{|A_s|} = c^r X^{n}`, `|A_s| = assigned φ s + 1`,
`∑_s |A_s| = n` (the clusters partition the `n` indices). -/
theorem cltMom1_prod_clusters {n : ℕ} {φ : Fin n → Fin n} (hφ : CltMom1.Cluster φ) (c X : ℝ) :
    ∏ s ∈ CltMom1.free φ, (c * X ^ (CltMom1.assigned φ s + 1)) = c ^ (CltMom1.free φ).card * X ^ n := by
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_pow_eq_pow_sum]
  congr 2
  have := cltMom1_sum_assigned hφ
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_const, smul_eq_mul, mul_one]
  omega

/-- The constant `C_d = 3·2^{2d-3}·41^d·d 4^d` of the cluster bound. -/
def CltMom1.Cd (d : ℕ) : ℝ := 3 * 2 ^ (2 * d - 3) * 41 ^ d * ((d : ℝ) * 4 ^ d)

/-- **The weight at the representative**: `u(x) = M · (|a₁-x|^{d-2}+1)^{-1} · λ/(|a₂-x|^{d-1}+1)` on the far region
`|a₁-x| ∧ |a₂-x| > ρ` of `STfFar`, `0` elsewhere. -/
def CltMom1.uw (a₁ a₂ : Zd d L) (ρ lam M : ℝ) (x : Zd d L) : ℝ :=
  M * (if ρ < ((zdistInf d L (a₁ - x) : ℕ) : ℝ) ∧ ρ < ((zdistInf d L (a₂ - x) : ℕ) : ℝ) then
    (1 / (((zdistInf d L (a₁ - x) : ℕ) : ℝ) ^ (d - 2) + 1)) *
      (lam / (((zdistInf d L (a₂ - x) : ℕ) : ℝ) ^ (d - 1) + 1)) else 0)

theorem CltMom1.uw_nonneg {a₁ a₂ : Zd d L} {ρ lam M : ℝ} (hlam : 0 ≤ lam) (hM : 0 ≤ M) (x : Zd d L) :
    0 ≤ CltMom1.uw a₁ a₂ ρ lam M x := by
  unfold CltMom1.uw
  refine mul_nonneg hM ?_
  split_ifs
  · positivity
  · exact le_rfl

/-- The sum of `u^{m+1}` over the lattice is the sum of `(eq:simplecalculus)` times `M^{m+1}`. -/
theorem cltMom1_uw_sum (hd : 3 ≤ d) {m : ℕ} (hm : 1 ≤ m) {ρ lam M : ℝ} (hρ : 0 < ρ) (hlam : 0 ≤ lam)
    (hM : 0 ≤ M) (a₁ a₂ : Zd d L) :
    ∑ x, CltMom1.uw a₁ a₂ ρ lam M x ^ (m + 1) ≤
      M ^ (m + 1) * ((2 * CltMom1.cs d * (3 * 2 ^ (2 * d - 3)) ^ (m + 1)) *
        (1 / (((zdistInf d L (a₁ - a₂) : ℕ) : ℝ) ^ (d - 2) + 1)) ^ (m + 1) *
          (lam ^ (m + 1) / ρ ^ ((d - 1) * (m + 1) - d))) := by
  classical
  have hsc := cltMom1_simplecalculus hd (q := m + 1) (by omega) hρ hlam a₁ a₂
  have heq : ∀ x : Zd d L, CltMom1.uw a₁ a₂ ρ lam M x ^ (m + 1) =
      M ^ (m + 1) * (if ρ < ((zdistInf d L (a₁ - x) : ℕ) : ℝ) ∧ ρ < ((zdistInf d L (a₂ - x) : ℕ) : ℝ) then
        (1 / (((zdistInf d L (a₁ - x) : ℕ) : ℝ) ^ (d - 2) + 1)) ^ (m + 1) *
          (lam / (((zdistInf d L (a₂ - x) : ℕ) : ℝ) ^ (d - 1) + 1)) ^ (m + 1) else 0) := by
    intro x
    unfold CltMom1.uw
    rw [mul_pow]
    congr 1
    split_ifs
    · rw [mul_pow]
    · simp
  simp only [heq]
  rw [← Finset.mul_sum, ← Finset.sum_filter]
  exact mul_le_mul_of_nonneg_left hsc (by positivity)

/-- **The cluster term at the scales of the paper** (`(eq:2p_product_pair)`, `3_5:2226-2241`): for a cluster with
`m + 1 = |A|` indices, `m ≥ 1`, `d ≥ 3`, `lw = log W ≥ 1`, `ℓ = ℓ_s ≥ 1`, `w = lw³ ℓ` (window), `ρ = lw⁴ ℓ` (far cutoff),
cluster radius `2R = 20 w`, and `z` bounded by the weight `u = CltMom1.uw` at the representative
(`hzu`, produced from targets 2 and 3), the term `∑_β z_β (∑_{β' ∈ ball} z_{β'})^m` is at most
`2 cs · (C_d M lw^{12} ℓ⁴ / (|a₁-a₂|^{d-2}+1))^{|A|}`.  The sum over `b` is target 5 (with `λ = w`), the sum over the cluster
is target 4, and the powers are those of target 6. -/
theorem cltMom1_cluster_term_le (hd : 3 ≤ d) {m : ℕ} (hm : 1 ≤ m) {lw ℓ Mz : ℝ} (hlw : 1 ≤ lw) (hℓ : 1 ≤ ℓ)
    (hMz : 0 ≤ Mz) (a₁ a₂ : Zd d L) {z : (Fin 2 → Zd d L) → ℝ} (hz0 : ∀ β, 0 ≤ z β)
    (hzu : ∀ β β' : Fin 2 → Zd d L, 0 < z β →
      ((zdistInf d L (β 0 - β' 0) : ℕ) : ℝ) ≤ 20 * (lw ^ 3 * ℓ) →
      z β' ≤ CltMom1.uw a₁ a₂ (lw ^ 4 * ℓ) (lw ^ 3 * ℓ) Mz (β 0) *
        CltMom1.G d L (lw ^ 3 * ℓ) (β' 0 - β' 1)) :
    ∑ β, z β * (∑ β' ∈ CltMom1.ball (20 * (lw ^ 3 * ℓ)) β, z β') ^ m ≤
      2 * CltMom1.cs d * (CltMom1.Cd d * Mz * lw ^ 12 *
        (ℓ ^ 4 * (1 / (((zdistInf d L (a₁ - a₂) : ℕ) : ℝ) ^ (d - 2) + 1)))) ^ (m + 1) := by
  have hlw0 : 0 < lw := by linarith
  have hℓ0 : 0 < ℓ := by linarith
  have hw1 : 1 ≤ lw ^ 3 * ℓ := cltMom1_scale_one_le hlw hℓ
  have hw0 : 0 ≤ lw ^ 3 * ℓ := by linarith
  have hρ : 0 < lw ^ 4 * ℓ := by positivity
  have hcs := CltMom1.cs_pos (d := d) (by omega)
  set w : ℝ := lw ^ 3 * ℓ with hw
  set ρ : ℝ := lw ^ 4 * ℓ with hρdef
  set U : ℝ := 1 / (((zdistInf d L (a₁ - a₂) : ℕ) : ℝ) ^ (d - 2) + 1) with hU
  have hU0 : 0 ≤ U := by rw [hU]; positivity
  have h1 := cltMom1_term_le hd hw0 (by linarith : (0 : ℝ) ≤ 20 * w) (u := CltMom1.uw a₁ a₂ ρ w Mz)
    (fun x => CltMom1.uw_nonneg hw0 hMz x) hz0 hzu m
  have h2 := cltMom1_uw_sum hd hm hρ hw0 hMz a₁ a₂
  have h3 := cltMom1_Yw_bound hd hw1 m
  have hY0 := CltMom1.Yw_nonneg (d := d) (by omega) w
  have h4 := cltMom1_exponent_count hd hm hlw hℓ0
  have hsum0 : 0 ≤ ∑ x, CltMom1.uw a₁ a₂ ρ w Mz x ^ (m + 1) :=
    Finset.sum_nonneg fun x _ => pow_nonneg (CltMom1.uw_nonneg hw0 hMz x) _
  have hK2 : (1 : ℝ) ≤ 41 ^ d := one_le_pow₀ (by norm_num)
  have hCd0 : 0 ≤ CltMom1.Cd d := by unfold CltMom1.Cd; positivity
  calc _ ≤ _ := h1
    _ ≤ (Mz ^ (m + 1) * ((2 * CltMom1.cs d * (3 * 2 ^ (2 * d - 3)) ^ (m + 1)) * U ^ (m + 1) *
          (w ^ (m + 1) / ρ ^ ((d - 1) * (m + 1) - d)))) *
        ((41 ^ d) ^ m * ((d : ℝ) * 4 ^ d) ^ (m + 1) * w ^ ((d + 2) * m + 2)) :=
        mul_le_mul h2 h3 (by positivity) (by positivity)
    _ = (2 * CltMom1.cs d * (Mz ^ (m + 1) * (3 * 2 ^ (2 * d - 3)) ^ (m + 1) * U ^ (m + 1) *
          (41 ^ d) ^ m * ((d : ℝ) * 4 ^ d) ^ (m + 1))) *
        (w ^ ((m + 1) + ((d + 2) * m + 2)) / ρ ^ ((d - 1) * (m + 1) - d)) := by
        rw [pow_add]; ring
    _ ≤ (2 * CltMom1.cs d * (Mz ^ (m + 1) * (3 * 2 ^ (2 * d - 3)) ^ (m + 1) * U ^ (m + 1) *
          (41 ^ d) ^ m * ((d : ℝ) * 4 ^ d) ^ (m + 1))) *
        (ℓ ^ (4 * (m + 1)) * lw ^ (12 * (m + 1))) :=
        mul_le_mul_of_nonneg_left h4 (by positivity)
    _ ≤ (2 * CltMom1.cs d * (Mz ^ (m + 1) * (3 * 2 ^ (2 * d - 3)) ^ (m + 1) * U ^ (m + 1) *
          (41 ^ d) ^ (m + 1) * ((d : ℝ) * 4 ^ d) ^ (m + 1))) *
        (ℓ ^ (4 * (m + 1)) * lw ^ (12 * (m + 1))) := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ (by positivity)) (by positivity))
          (by positivity)) (by positivity)
        exact pow_le_pow_right₀ hK2 (Nat.le_succ m)
    _ = 2 * CltMom1.cs d * (CltMom1.Cd d * Mz * lw ^ 12 * (ℓ ^ 4 * U)) ^ (m + 1) := by
        unfold CltMom1.Cd
        rw [show 12 * (m + 1) = 12 * (m + 1) from rfl, pow_mul, pow_mul]
        ring

open Classical in
/-- **The paired part of the `2p`-th moment sum** (`(eq:2p_product_pair)`, `3_5:2226-2241`; the interface for `S5-24`):
let `lw = log W ≥ 1`, `ℓ = ℓ_s ≥ 1`, `R = 10 lw³ ℓ` (the pairing radius of `STCltIsoConcl`), `z ≥ 0` a per-label weight with
`hzu` (target 2 and 3: at a label `β` with `z β > 0`, every `β'` with first label within `2R = 20 lw³ ℓ` of `β`'s has
`z β' ≤ u(β₁) G_w(β₁'-β₂')`).  Then
`∑_{b paired at R} ∏_{k<2p} z(b^{(k)}) ≤ (2p)^{2p} (2 cs)^p (C_d M lw^{12})^{2p} (ℓ⁴/(|a₁-a₂|^{d-2}+1))^{2p}`:
the target of `(eq:main_challenge3)` under the pairing condition, with the explicit log factor `lw^{24p}`. -/
theorem cltMom1_clusterSum_le (hd : 3 ≤ d) (p : ℕ) {lw ℓ Mz : ℝ} (hlw : 1 ≤ lw) (hℓ : 1 ≤ ℓ)
    (hMz : 0 ≤ Mz) (a₁ a₂ : Zd d L) {z : (Fin 2 → Zd d L) → ℝ} (hz0 : ∀ β, 0 ≤ z β)
    (hzu : ∀ β β' : Fin 2 → Zd d L, 0 < z β →
      ((zdistInf d L (β 0 - β' 0) : ℕ) : ℝ) ≤ 20 * (lw ^ 3 * ℓ) →
      z β' ≤ CltMom1.uw a₁ a₂ (lw ^ 4 * ℓ) (lw ^ 3 * ℓ) Mz (β 0) *
        CltMom1.G d L (lw ^ 3 * ℓ) (β' 0 - β' 1)) :
    CltMom1.clusterSum (2 * p) z (20 * (lw ^ 3 * ℓ)) ≤
      ((2 * p : ℕ) : ℝ) ^ (2 * p) * (2 * CltMom1.cs d) ^ p *
        ((CltMom1.Cd d * Mz * lw ^ 12) ^ (2 * p) *
          (ℓ ^ 4 / (((zdistInf d L (a₁ - a₂) : ℕ) : ℝ) ^ (d - 2) + 1)) ^ (2 * p)) := by
  have hlw0 : 0 < lw := by linarith
  have hcs := CltMom1.cs_pos (d := d) (by omega)
  have hCd0 : 0 ≤ CltMom1.Cd d := by unfold CltMom1.Cd; positivity
  set U : ℝ := 1 / (((zdistInf d L (a₁ - a₂) : ℕ) : ℝ) ^ (d - 2) + 1) with hU
  have hU0 : 0 ≤ U := by rw [hU]; positivity
  set X : ℝ := CltMom1.Cd d * Mz * lw ^ 12 * (ℓ ^ 4 * U) with hX
  have hX0 : 0 ≤ X := by positivity
  have hc1 : (1 : ℝ) ≤ 2 * CltMom1.cs d := by
    unfold CltMom1.cs
    have : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast (by omega : 1 ≤ d)
    have h2 : (1 : ℝ) ≤ 2 ^ (d - 1) := one_le_pow₀ (by norm_num)
    nlinarith
  have hmain := cltMom1_clusterSum_le_of_bound (n := 2 * p) z hz0 (20 * (lw ^ 3 * ℓ))
    (fun k => 2 * CltMom1.cs d * X ^ (k + 1))
    (fun k hk => cltMom1_cluster_term_le hd hk hlw hℓ hMz a₁ a₂ hz0 hzu)
    ((2 * CltMom1.cs d) ^ p * X ^ (2 * p)) (by positivity)
    (fun φ hφ => by
      rw [cltMom1_prod_clusters hφ]
      have hr : (CltMom1.free φ).card ≤ p := by
        have := cltMom1_two_mul_free_le hφ
        omega
      exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hc1 hr) (by positivity))
  refine hmain.trans (le_of_eq ?_)
  rw [hX, mul_pow, mul_pow, mul_pow, hU]
  have : (ℓ ^ 4 * (1 / (((zdistInf d L (a₁ - a₂) : ℕ) : ℝ) ^ (d - 2) + 1))) =
      ℓ ^ 4 / (((zdistInf d L (a₁ - a₂) : ℕ) : ℝ) ^ (d - 2) + 1) := by ring
  rw [this]
  ring

open Classical in
/-- **The paired part of the `2p`-th moment sum, over the configurations**: the sum over the `b : Fin (2p) → (Fin 2 → Zd d L)`
satisfying the pairing condition at `R = 10 lw³ ℓ` (`CltMom1.Paired`, the complement of the isolation hypothesis of
`STCltIsoConcl`) of `∏_k z(b^{(k)})` is bounded by the right-hand side of `cltMom1_clusterSum_le`. -/
theorem cltMom1_paired_moment_le (hd : 3 ≤ d) (p : ℕ) {lw ℓ Mz : ℝ} (hlw : 1 ≤ lw) (hℓ : 1 ≤ ℓ)
    (hMz : 0 ≤ Mz) (a₁ a₂ : Zd d L) {z : (Fin 2 → Zd d L) → ℝ} (hz0 : ∀ β, 0 ≤ z β)
    (hzu : ∀ β β' : Fin 2 → Zd d L, 0 < z β →
      ((zdistInf d L (β 0 - β' 0) : ℕ) : ℝ) ≤ 20 * (lw ^ 3 * ℓ) →
      z β' ≤ CltMom1.uw a₁ a₂ (lw ^ 4 * ℓ) (lw ^ 3 * ℓ) Mz (β 0) *
        CltMom1.G d L (lw ^ 3 * ℓ) (β' 0 - β' 1)) :
    ∑ b ∈ Finset.univ.filter (fun b : Fin (2 * p) → (Fin 2 → Zd d L) =>
        CltMom1.Paired (10 * (lw ^ 3 * ℓ)) b), ∏ k, z (b k) ≤
      ((2 * p : ℕ) : ℝ) ^ (2 * p) * (2 * CltMom1.cs d) ^ p *
        ((CltMom1.Cd d * Mz * lw ^ 12) ^ (2 * p) *
          (ℓ ^ 4 / (((zdistInf d L (a₁ - a₂) : ℕ) : ℝ) ^ (d - 2) + 1)) ^ (2 * p)) := by
  have hw0 : 0 ≤ lw ^ 3 * ℓ := by
    have : 0 < lw := by linarith
    positivity
  refine (cltMom1_paired_sum_le z hz0 (10 * (lw ^ 3 * ℓ)) (by positivity)).trans ?_
  rw [show 2 * (10 * (lw ^ 3 * ℓ)) = 20 * (lw ^ 3 * ℓ) by ring]
  exact cltMom1_clusterSum_le hd p hlw hℓ hMz a₁ a₂ hz0 hzu

end ExponentCount

/-! ## 9. Compiled nonempty instances at `d = 3` -/

section Instances

/-- The data of the instances: `d = 3`, `L = 83`, `p = 1`, window `w = 1`, far cutoff `ρ = 40`, pairing radius `R = 10 w = 10`,
`a₁ = 0`, `a₂ = (0,0,1)` (`|a₁ - a₂|_∞ = 1`), two indices `b^{(0)} = ((41,41,41),(41,41,42))`,
`b^{(1)} = ((36,41,41),(36,41,40))`: first labels at distance `5 < R`, both far (`|b₁ - a_i|_∞ = 41 > 40`) and in the
window (`|b₁ - b₂|_∞ = 1`). -/
private def cltMom1_a₂ : Zd 3 83 := ![0, 0, 1]

private def cltMom1_b : Fin (2 * 1) → (Fin 2 → Zd 3 83) :=
  ![![![41, 41, 41], ![41, 41, 42]], ![![36, 41, 41], ![36, 41, 40]]]

private theorem cltMom1_b_dist : zdistInf 3 83 ((cltMom1_b 0 0) - (cltMom1_b 1 0)) = 5 ∧
    zdistInf 3 83 ((cltMom1_b 1 0) - (cltMom1_b 0 0)) = 5 := by
  constructor <;> decide

/-- Non-vacuity of the cluster predicate: the constant retraction of `Fin 2` onto `0` is one cluster `{0, 1}`. -/
theorem cltMom1_cluster_inst : CltMom1.Cluster (fun _ : Fin 2 => (0 : Fin 2)) := by
  refine ⟨fun _ => rfl, fun i hi => ?_⟩
  have h0 : i = 0 := hi.symm
  subst h0
  exact ⟨1, by decide, rfl⟩

/-- A paired configuration exists: `b^{(0)}, b^{(1)}` are paired at `R = 10`. -/
theorem cltMom1_b_paired : CltMom1.Paired (10 : ℝ) cltMom1_b := by
  obtain ⟨h0, h1⟩ := cltMom1_b_dist
  intro i
  fin_cases i
  · refine ⟨1, by decide, ?_⟩
    simp only [Fin.zero_eta, h0]
    norm_num
  · refine ⟨0, by decide, ?_⟩
    simp only [Fin.mk_one, h1]
    norm_num

/-- **Instance of target 1** (`p = 1`, `R = 10`): the paired configuration `cltMom1_b` has a cluster decomposition
(one cluster `{0,1}`, `r = 1 ≤ p`, members within `2R = 20`, at most `2² = 4` structures). -/
example := cltMom1_clusters (d := 3) (L := 83) (p := 1) le_rfl (R := 10) (by norm_num) cltMom1_b cltMom1_b_paired

/-- Target 1, the isolation side: a configuration with first labels `(0,0,0)` and `(41,41,41)` (distance `41 ≥ R`) is
not paired, by `cltMom1_not_paired_iff`. -/
example : ¬ CltMom1.Paired (10 : ℝ)
    (![![![0, 0, 0], ![0, 0, 0]], ![![41, 41, 41], ![41, 41, 41]]] : Fin (2 * 1) → (Fin 2 → Zd 3 83)) := by
  rw [cltMom1_not_paired_iff]
  refine ⟨0, fun j hj => ?_⟩
  fin_cases j
  · exact absurd rfl hj
  · have : zdistInf 3 83 (((![![![0, 0, 0], ![0, 0, 0]], ![![41, 41, 41], ![41, 41, 41]]] :
        Fin (2 * 1) → (Fin 2 → Zd 3 83)) 0) 0 - ((![![![0, 0, 0], ![0, 0, 0]], ![![41, 41, 41], ![41, 41, 41]]] :
        Fin (2 * 1) → (Fin 2 → Zd 3 83)) 1) 0) = 41 := by decide
    simp only [Fin.mk_one, this]
    norm_num

/-- The common (non-stochastic) data of target 2: `ξ = t m(σ₁) m(σ₂)` at `t = 9/10`, `m = i`, `σ = (+,-)` (`m₁ m₂ = 1`),
`g = 1/2 ≤ Λ = 1`, regime (i): `g²/L² = 1/27556 ≤ 1 - t = 1/10`. -/
private abbrev cltMom1_xi : ℂ := (((9 / 10 : ℝ) : ℂ) * (PropSpin Complex.I true * PropSpin Complex.I false))

/-- **Instance of target 2a** (weight at `a₁ = 0`, `b₁ = (41,41,41)`). -/
example : ∃ C : ℝ, 0 < C ∧ (1 / 2 : ℝ) ^ 2 * ‖Theta 3 83 (1 / 2 : ℝ) cltMom1_xi (0 : Zd 3 83) ![41, 41, 41]‖ ≤
    C * (1 + 2 ^ (3 - 1)) / (((zdistInf 3 83 ((0 : Zd 3 83) - ![41, 41, 41]) : ℕ) : ℝ) ^ (3 - 2) + 1) := by
  obtain ⟨C, hC, H⟩ := cltMom1_weight_a1 3 1 le_rfl one_pos
  exact ⟨C, hC, H 83 (by norm_num) (1 / 2) (by norm_num) (by norm_num) (9 / 10) (by norm_num) (by norm_num)
    (by norm_num) Complex.I (by simp) true false 0 ![41, 41, 41]⟩

/-- **Instance of target 2b** (weight at `a₂`, `b₁ = (36,41,41)`, `b₂ = (36,41,40)`, `w = 1`, `ρ = 40`). -/
example : ∃ C : ℝ, 0 < C ∧ (1 / 2 : ℝ) ^ 2 * ‖Theta 3 83 (1 / 2 : ℝ) cltMom1_xi (![36, 41, 40] : Zd 3 83) cltMom1_a₂ -
      Theta 3 83 (1 / 2 : ℝ) cltMom1_xi (![36, 41, 41] : Zd 3 83) cltMom1_a₂‖ ≤
    C * (3 : ℕ) * 1 / (((zdistInf 3 83 (cltMom1_a₂ - ![36, 41, 41]) : ℕ) : ℝ) ^ (3 - 1) + 1) := by
  obtain ⟨C, hC, H⟩ := cltMom1_weight_a2 3 1 (1 / 2) le_rfl one_pos (by norm_num)
  have hfar : (40 : ℝ) < ((zdistInf 3 83 (cltMom1_a₂ - ![36, 41, 41]) : ℕ) : ℝ) := by
    have : zdistInf 3 83 (cltMom1_a₂ - ![36, 41, 41]) = 41 := by decide
    rw [this]; norm_num
  have hwin : ((zdistInf 3 83 ((![36, 41, 41] : Zd 3 83) - ![36, 41, 40]) : ℕ) : ℝ) ≤ 1 := by
    have : zdistInf 3 83 ((![36, 41, 41] : Zd 3 83) - ![36, 41, 40]) = 1 := by decide
    rw [this]; norm_num
  exact ⟨C, hC, H 83 (by norm_num) (1 / 2) (by norm_num) (by norm_num) (9 / 10) (by norm_num) (by norm_num)
    Complex.I (by simp) (by norm_num) true false cltMom1_a₂ ![36, 41, 41] ![36, 41, 40] 1 40 (by norm_num) hfar hwin⟩

/-- **Instance of target 3** (comparability): `b = (41,41,41)`, `b' = (36,41,41)` (`|b - b'|_∞ = 5 ≤ r = 20 = 2R`, `R = 10`),
`2 r = 40 ≤ ρ = 40 < 41 = |a_i - b|_∞`, `λ = 1`. -/
example := cltMom1_comparable_weights (d := 3) (L := 83) (r := 20) (ρ := 40) (lam := 1) (by norm_num) (by norm_num)
  (by norm_num) (0 : Zd 3 83) cltMom1_a₂ ![41, 41, 41] ![36, 41, 41]
  (by
    have : zdistInf 3 83 ((0 : Zd 3 83) - ![41, 41, 41]) = 41 := by decide
    rw [this]; norm_num)
  (by
    have : zdistInf 3 83 (cltMom1_a₂ - ![41, 41, 41]) = 41 := by decide
    rw [this]; norm_num)
  (by
    have : zdistInf 3 83 ((![41, 41, 41] : Zd 3 83) - ![36, 41, 41]) = 5 := by decide
    rw [this]; norm_num)
  (by norm_num)

/-- **Instance of target 4** (`m = |A| - 1 = 1`, `w = 1`, representative first label `x = 0`). -/
example := cltMom1_cluster_sum_C4 (d := 3) (L := 83) (by norm_num) (w := 1) le_rfl 1 (0 : Zd 3 83)

/-- **Instance of target 5** (`q = k = 2`, `ρ = 40`, `λ = 1`, `a₁ = 0`, `a₂ = (0,0,1)`). -/
example := cltMom1_simplecalculus (d := 3) (L := 83) (by norm_num) (q := 2) le_rfl (ρ := 40) (lam := 1)
  (by norm_num) (by norm_num) (0 : Zd 3 83) cltMom1_a₂

/-- **Instance of target 5, ticket-literal form** (`q = k = 2`, `ρ = 40`, `ℓ = 1`, `a₁ = 0`, `a₂ = (0,0,1)`). -/
example := cltMom1_simplecalculus_ell (d := 3) (L := 83) (by norm_num) (q := 2) le_rfl (ρ := 40) (ℓ := 1)
  le_rfl (by norm_num) (0 : Zd 3 83) cltMom1_a₂

/-- The far set of target 5's instance is nonempty (`b = (41,41,41)`). -/
example : (Finset.univ.filter (fun b : Zd 3 83 =>
    (40 : ℝ) < ((zdistInf 3 83 ((0 : Zd 3 83) - b) : ℕ) : ℝ) ∧
      (40 : ℝ) < ((zdistInf 3 83 (cltMom1_a₂ - b) : ℕ) : ℝ))).Nonempty := by
  classical
  refine ⟨![41, 41, 41], ?_⟩
  rw [Finset.mem_filter]
  refine ⟨by simp, ?_, ?_⟩
  · have : zdistInf 3 83 ((0 : Zd 3 83) - ![41, 41, 41]) = 41 := by decide
    rw [this]; norm_num
  · have : zdistInf 3 83 (cltMom1_a₂ - ![41, 41, 41]) = 41 := by decide
    rw [this]; norm_num

/-- **Instance of target 6**: `d = 3`, a cluster with `m + 1 = 2` indices, `lw = 41 ≥ 40`, `ℓ = 1`: the identity, the natural-number
form (`E = (d-1)(m+1) - d = 1`) and the scale count. -/
example := cltMom1_exponent_identity 3 2

example := cltMom1_exponent_nat (d := 3) (m := 1) (by norm_num) le_rfl

example := cltMom1_exponent_count (d := 3) (m := 1) (by norm_num) le_rfl (lw := 41) (ℓ := 1) (by norm_num) one_pos

/-- Instances of the exact forms of target 6 (`d = 3`, `lw = 41`, `ℓ = 1`; the cluster of `cltMom1_cluster_inst`). -/
example := cltMom1_exponent_count_eq (d := 3) (m := 1) (by norm_num) le_rfl (lw := 41) (ℓ := 1) (by norm_num) one_pos

example := cltMom1_prod_exponent_exact cltMom1_cluster_inst 3 (lw := 41) (ℓ := 1) (by norm_num)

example := cltMom1_scale_comparable (lw := 41) (ℓ := 1) (p := 1) (by norm_num) zero_le_one

example := cltMom1_scale_bd1 (d := 3) (lw := 41) (ℓ := 1) (by norm_num) zero_le_one


/-- **The assembly instance** (`lw = ℓ = 1`, `M = 1`, `p = 1`, `w = ρ = 1`): `z` is the point mass at the first index
`b^{(0)} = ((41,41,41),(41,41,42))` of the paired configuration, with value `c = u(b₁) G_w(b₁ - b₂) > 0`, so `z β > 0` only
at `β = b^{(0)}` and `hzu` holds with equality there. -/
private noncomputable def cltMom1_c : ℝ :=
  CltMom1.uw (0 : Zd 3 83) cltMom1_a₂ (1 ^ 4 * 1) (1 ^ 3 * 1) 1 (cltMom1_b 0 0) *
    CltMom1.G 3 83 (1 ^ 3 * 1) (cltMom1_b 0 0 - cltMom1_b 0 1)

private theorem cltMom1_c_pos : 0 < cltMom1_c := by
  have hA : zdistInf 3 83 ((0 : Zd 3 83) - cltMom1_b 0 0) = 41 := by decide
  have hB : zdistInf 3 83 (cltMom1_a₂ - cltMom1_b 0 0) = 41 := by decide
  have hG : zdistInf 3 83 (cltMom1_b 0 0 - cltMom1_b 0 1) = 1 := by decide
  unfold cltMom1_c CltMom1.uw CltMom1.G
  rw [hA, hB, hG]
  norm_num

open Classical in
private noncomputable def cltMom1_z : (Fin 2 → Zd 3 83) → ℝ :=
  fun β => if β = cltMom1_b 0 then cltMom1_c else 0

private theorem cltMom1_z_nonneg (β : Fin 2 → Zd 3 83) : 0 ≤ cltMom1_z β := by
  classical
  unfold cltMom1_z
  split_ifs
  · exact cltMom1_c_pos.le
  · exact le_rfl

private theorem cltMom1_z_hzu (β β' : Fin 2 → Zd 3 83) (hβ : 0 < cltMom1_z β)
    (_ : ((zdistInf 3 83 (β 0 - β' 0) : ℕ) : ℝ) ≤ 20 * (1 ^ 3 * 1)) :
    cltMom1_z β' ≤ CltMom1.uw (0 : Zd 3 83) cltMom1_a₂ (1 ^ 4 * 1) (1 ^ 3 * 1) 1 (β 0) *
      CltMom1.G 3 83 (1 ^ 3 * 1) (β' 0 - β' 1) := by
  classical
  have hβb : β = cltMom1_b 0 := by
    by_contra h
    simp [cltMom1_z, h] at hβ
  have hnn : 0 ≤ CltMom1.uw (0 : Zd 3 83) cltMom1_a₂ (1 ^ 4 * 1) (1 ^ 3 * 1) 1 (β 0) *
      CltMom1.G 3 83 (1 ^ 3 * 1) (β' 0 - β' 1) :=
    mul_nonneg (CltMom1.uw_nonneg (by norm_num) (by norm_num) _) (CltMom1.G_nonneg _ _)
  by_cases hβ' : β' = cltMom1_b 0
  · subst hβb
    simp only [cltMom1_z, hβ', ↓reduceIte, cltMom1_c]
    exact le_rfl
  · simp only [cltMom1_z, hβ', ↓reduceIte]
    exact hnn

/-- **Instance of the assembly** `cltMom1_clusterSum_le` (`d = 3`, `L = 83`, `p = 1`). -/
example := cltMom1_clusterSum_le (d := 3) (L := 83) (by norm_num) 1 (lw := 1) (ℓ := 1) (Mz := 1) le_rfl le_rfl
  zero_le_one (0 : Zd 3 83) cltMom1_a₂ (z := cltMom1_z) cltMom1_z_nonneg cltMom1_z_hzu

/-- **Instance of the paired moment bound** `cltMom1_paired_moment_le` (same data). -/
example := cltMom1_paired_moment_le (d := 3) (L := 83) (by norm_num) 1 (lw := 1) (ℓ := 1) (Mz := 1) le_rfl le_rfl
  zero_le_one (0 : Zd 3 83) cltMom1_a₂ (z := cltMom1_z) cltMom1_z_nonneg cltMom1_z_hzu

end Instances

end RBM.Evol
