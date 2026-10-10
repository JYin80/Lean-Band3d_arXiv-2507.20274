/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.BA.KMolecule
import RBM3D.BA.CombesThomas
import RBM3D.BA.Prop5Short
import RBM3D.BA.KKernel
import RBM3D.Loop.PureLoop
import RBM3D.Loop.KLIndStepA

/-!
# Stage K, row K07: the decay of the BA molecule weight `(eq:molecule-decay)` and pure BA loops

Ticket T2380 (design BA-DK, `docs/reports/T2360-design.md` §3 (b), §4 row K07).  The statements
are those of `docs/reports/T2380-prove.md` section (a), audited in `docs/reports/T2380-1a-audit.md`.
Paper: `(eq:molecule-decay)`, `lem_pureloop`, `(res_pureKes)`
(`A_deterministic_estimates.tex:640-700`).
The BA twin of `Loop/PureLoop.lean` and `Loop/KLMolecule.lean` §2-§5 (star to cactus: one label per
slot, not per node).

1. `baPureB`, `baPureRate`, `baPure_edge`: every edge of a BA molecule, i.e. an `M(σ)`-entry
   (`Mbound_AO`, `Mbound_AO2`) and a short chord `tΘ^{(s,s)}` (`(prop:ThfadC_short)`), is at most
   `B e^{-r |x-y|}`.
2. `baSlot_path_le`: the slot graph of a cactus (chords and `M`-edges) is connected, so two slots
   are at distance at most the total length of the edges.  An abstract spanning-tree argument (a
   tree grown from a base slot, one new slot and one new edge at a time) replaces the laminar path
   bound of the band; it needs only that the sets of slots closed under the edges are trivial,
   proved from the cyclic order of a node (`BAnextSlot_orbit`) and the parent of a node
   (`KLnodePar`).
3. `baSigmaTree_bound` (the core, with a product hypothesis `hprod`), its entrywise corollaries,
   and `baSigmaPi_empty_bound`: `|Σ^{(∅)}(δ)| ≤ C e^{-(r/4) max_{i,j} |δ_i - δ_j|}`.
4. `baSig_decay`: `(eq:molecule-decay)` as `SigDecayAbs d n L (BASig ..)`, every `σ`, uniformly in
   the family.
5. `baK_pure_eq`, `baPure_loop`: the pure loop `σ = (σ₀, …, σ₀)`: `𝒦^{(n)} = W^{-d(n-1)} K^{(∅)}`,
   and `|𝒦^{(n)}| ≤ C W^{-d(n-1)} e^{-c max_{i,j} |a_i - a_j|}`.
6. Compiled instances at the flow point `P` of `(d, L) = (3, 4)`, `n = 3, 4`.

Every helper that is not pinned is `private` and carries the stem `KPure_`.
-/

set_option linter.style.longLine false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace RBM.BA

open RBM RBM.Loop
open scoped Matrix

/-! ## 0. Small helpers -/

section Helpers

variable {d L : ℕ} [NeZero L]

/-- The periodic distance is symmetric. -/
private theorem KPure_zdistD_comm (x y : Zd d L) : zdistD d L (x - y) = zdistD d L (y - x) := by
  rw [← zdistD_neg d L (x - y), neg_sub]

/-- The triangle inequality for the periodic distance. -/
private theorem KPure_zdistD_tri (x y z : Zd d L) :
    zdistD d L (x - z) ≤ zdistD d L (x - y) + zdistD d L (y - z) := by
  have := zdistD_add_le d L (x - y) (y - z)
  rwa [sub_add_sub_cancel] at this

/-- `Θ^{(s,s')}` is invariant under the translation `x ↦ x + c` when every `M(σ)` is (the conjugation of
`Ring.inverse` by a permutation matrix, `Matrix.inv_submatrix_equiv`; no invertibility; a copy of the private
`KMolecule_theta_perm`, `BA/KMolecule.lean:166`, at `e = Equiv.addRight c`). -/
private theorem KPure_theta_shift (M : Bool → Matrix (Zd d L) (Zd d L) ℂ)
    (hM : ∀ (σ : Bool) (x y c : Zd d L), M σ (x + c) (y + c) = M σ x y) (t : ℝ) (s s' : Bool) (x y c : Zd d L) :
    BAThetaOf M t s s' (x + c) (y + c) = BAThetaOf M t s s' x y := by
  have hQ : ∀ x y, BAMssOf M s s' (x + c) (y + c) = BAMssOf M s s' x y := fun x y => by
    simp only [BAMssOf, Matrix.of_apply, hM]
  have hA : ((1 : Matrix (Zd d L) (Zd d L) ℂ) - (t : ℂ) • BAMssOf M s s').submatrix (Equiv.addRight c)
      (Equiv.addRight c) = 1 - (t : ℂ) • BAMssOf M s s' := by
    ext x y
    simp only [Matrix.submatrix_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
      Equiv.coe_addRight, add_left_inj, hQ]
  have h2 := Matrix.inv_submatrix_equiv ((1 : Matrix (Zd d L) (Zd d L) ℂ) - (t : ℂ) • BAMssOf M s s')
    (Equiv.addRight c) (Equiv.addRight c)
  rw [hA] at h2
  unfold BAThetaOf PropThetaQ
  rw [← Matrix.nonsing_inv_eq_ringInverse]
  have h3 := congrFun (congrFun h2 x) y
  rw [Matrix.submatrix_apply] at h3
  exact h3.symm

/-- `(1/2)^k ≤ e^{-r k}` for `r ≤ log 2`. -/
private theorem KPure_half_pow_le {r : ℝ} (hr : r ≤ Real.log 2) (k : ℕ) :
    (1 / 2 : ℝ) ^ k ≤ Real.exp (-(r * (k : ℝ))) := by
  have h1 : (1 / 2 : ℝ) ^ k = Real.exp (-(Real.log 2 * (k : ℝ))) := by
    rw [show -(Real.log 2 * (k : ℝ)) = (k : ℝ) * (-Real.log 2) by ring, Real.exp_nat_mul, Real.exp_neg,
      Real.exp_log (by norm_num), one_div]
  rw [h1]
  exact Real.exp_le_exp.2 (by nlinarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)])

end Helpers

/-! ## 1. The constants and the edge bounds -/

/-- **The prefactor `B`** of the edge bounds: `B = max (max 1 c₀⁻¹) (C₅ (1 + Λ²))`, with `c₀ = BAct_rate d Λ κ`
(`Mbound_AO2`) and `C₅ = BAp5s_C d Λ κ` (`(prop:ThfadC_short)`); `B ≥ 1` (`baPureB_one_le`). -/
noncomputable def baPureB (d : ℕ) (Λ κ : ℝ) : ℝ :=
  max (max 1 (BAct_rate d Λ κ)⁻¹) (BAp5s_C d Λ κ * (1 + Λ ^ 2))

/-- **The rate `r`** of the edge bounds: `r = min (min c₀ (log 2)) c_s`, `c₀ = BAct_rate d Λ κ`,
`c_s = BAp5s_rate d Λ κ`; `r > 0` (`baPureRate_pos`). -/
noncomputable def baPureRate (d : ℕ) (Λ κ : ℝ) : ℝ :=
  min (min (BAct_rate d Λ κ) (Real.log 2)) (BAp5s_rate d Λ κ)

theorem baPureB_one_le (d : ℕ) (Λ κ : ℝ) : 1 ≤ baPureB d Λ κ :=
  (le_max_left _ _).trans' (le_max_left _ _)

theorem baPureRate_pos {d : ℕ} (hd : 0 < d) {Λ κ : ℝ} (hΛ : 0 < Λ) (hκ : 0 < κ) : 0 < baPureRate d Λ κ := by
  unfold baPureRate
  exact lt_min (lt_min (BAct_rate_pos d Λ κ hd hΛ hκ) (Real.log_pos (by norm_num)))
    (BAp5s_rate_pos d Λ κ hd hΛ hκ)

section Edges

variable {d : ℕ} {Λ κ : ℝ} {L : ℕ} [NeZero L] {g : ℝ} {E : ℝ} {m : ℂ}

/-- The entries of `M^{(B)} = BAMB`: `|M_{xy}| ≤ B e^{-r |x-y|}` (`Mbound_AO` when `g < (2C)⁻¹`, `Mbound_AO2`
otherwise). -/
private theorem KPure_MB_entry (hd : 0 < d) (hΛ : 0 < Λ) (hκ : 0 < κ) (hL : 3 ≤ L) (hg : 0 < g) (hgΛ : g ≤ Λ)
    (hr : BAReal d L g κ E m) (x y : Zd d L) :
    ‖BAMB d L g (E : ℂ) m x y‖ ≤ baPureB d Λ κ * Real.exp (-(baPureRate d Λ κ * (zdistD d L (x - y) : ℝ))) := by
  obtain ⟨h1, h2⟩ := BAPropM3_of_real d L hL hd Λ g κ E m hΛ hg hgΛ hκ hr
  have hC := BAct_C_pos d κ hd hκ
  have hc₀ := BAct_rate_pos d Λ κ hd hΛ hκ
  have hB1 := baPureB_one_le d Λ κ
  have hrc : baPureRate d Λ κ ≤ BAct_rate d Λ κ := (min_le_left _ _).trans (min_le_left _ _)
  have hrl : baPureRate d Λ κ ≤ Real.log 2 := (min_le_left _ _).trans (min_le_right _ _)
  by_cases hsm : g < (2 * BAct_C d κ)⁻¹
  · have hb := (h1 hsm x y).2
    have hCg : BAct_C d κ * g ≤ 1 / 2 := by
      have h := hsm
      rw [← one_div, lt_div_iff₀ (by positivity)] at h
      nlinarith
    calc ‖BAMB d L g (E : ℂ) m x y‖ ≤ (BAct_C d κ * g) ^ zdistD d L (x - y) := hb
      _ ≤ (1 / 2 : ℝ) ^ zdistD d L (x - y) := pow_le_pow_left₀ (by positivity) hCg _
      _ ≤ Real.exp (-(baPureRate d Λ κ * (zdistD d L (x - y) : ℝ))) := KPure_half_pow_le hrl _
      _ ≤ baPureB d Λ κ * Real.exp (-(baPureRate d Λ κ * (zdistD d L (x - y) : ℝ))) :=
        le_mul_of_one_le_left (Real.exp_pos _).le hB1
  · push Not at hsm
    have hb := h2 hsm x y
    have hBc : (BAct_rate d Λ κ)⁻¹ ≤ baPureB d Λ κ := (le_max_right _ _).trans (le_max_left _ _)
    have hz : (0 : ℝ) ≤ (zdistD d L (x - y) : ℝ) := Nat.cast_nonneg _
    calc ‖BAMB d L g (E : ℂ) m x y‖
        ≤ (BAct_rate d Λ κ)⁻¹ * Real.exp (-BAct_rate d Λ κ * (zdistD d L (x - y) : ℝ)) := hb
      _ ≤ baPureB d Λ κ * Real.exp (-(baPureRate d Λ κ * (zdistD d L (x - y) : ℝ))) := by
        refine mul_le_mul hBc (Real.exp_le_exp.2 ?_) (Real.exp_pos _).le (by linarith)
        nlinarith

/-- The short propagator `Θ^{(s,s)}` at an arbitrary pair `(x, y)`: translation `x ↦ 0` and `(prop:ThfadC_short)`
(`baProp5s_of_real`), `1_{a=0} ≤ e^{-c_s |a|}`, `g² ≤ Λ²`. -/
private theorem KPure_theta_entry (hd : 2 ≤ d) (hΛ : 0 < Λ) (hκ : 0 < κ) (hL : 3 ≤ L) (hg : 0 < g) (hgΛ : g ≤ Λ)
    (hr : BAReal d L g κ E m) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (s : Bool) (x y : Zd d L) :
    ‖BAThetaOf (BAMsigma d L (BAMB d L g (E : ℂ) m)) t s s x y‖ ≤
      baPureB d Λ κ * Real.exp (-(baPureRate d Λ κ * (zdistD d L (x - y) : ℝ))) := by
  have hd0 : 0 < d := by omega
  have hB1 := baPureB_one_le d Λ κ
  have hrs : baPureRate d Λ κ ≤ BAp5s_rate d Λ κ := min_le_right _ _
  have hBC : BAp5s_C d Λ κ * (1 + Λ ^ 2) ≤ baPureB d Λ κ := le_max_right _ _
  have hC := BAp5s_C_pos d Λ κ hd0 hΛ hκ
  have hshift : BAThetaOf (BAMsigma d L (BAMB d L g (E : ℂ) m)) t s s x y =
      BATheta d L g E m t s s 0 (y - x) := by
    have h := KPure_theta_shift (BAMsigma d L (BAMB d L g (E : ℂ) m))
      (fun σ x y c => BAMsigma_shift d L g (E : ℂ) m σ x y c) t s s 0 (y - x) x
    rw [zero_add, sub_add_cancel] at h
    exact h
  rw [hshift]
  have h5 := baProp5s_of_real d L hL hd Λ g κ E m hΛ hg hgΛ hκ hr t ht0 ht1 s (y - x)
  rw [KPure_zdistD_comm x y]
  set z : ℝ := (zdistD d L (y - x) : ℝ) with hz
  have hz0 : 0 ≤ z := Nat.cast_nonneg _
  have hexp : Real.exp (-(BAp5s_rate d Λ κ * z)) ≤ Real.exp (-(baPureRate d Λ κ * z)) :=
    Real.exp_le_exp.2 (by nlinarith)
  have hind : (if y - x = 0 then (1 : ℝ) else 0) ≤ Real.exp (-(BAp5s_rate d Λ κ * z)) := by
    by_cases h0 : y - x = 0
    · simp [h0, hz, zdistD_zero]
    · simp only [h0, ite_false]
      exact (Real.exp_pos _).le
  have hg2 : g ^ 2 ≤ Λ ^ 2 := pow_le_pow_left₀ hg.le hgΛ 2
  calc ‖BATheta d L g E m t s s 0 (y - x)‖
      ≤ BAp5s_C d Λ κ * ((if y - x = 0 then (1 : ℝ) else 0) + g ^ 2 * Real.exp (-BAp5s_rate d Λ κ * z)) := h5
    _ ≤ BAp5s_C d Λ κ * (1 + Λ ^ 2) * Real.exp (-(baPureRate d Λ κ * z)) := by
      rw [neg_mul]
      calc BAp5s_C d Λ κ * ((if y - x = 0 then (1 : ℝ) else 0) + g ^ 2 * Real.exp (-(BAp5s_rate d Λ κ * z)))
          ≤ BAp5s_C d Λ κ * (Real.exp (-(BAp5s_rate d Λ κ * z)) + Λ ^ 2 * Real.exp (-(BAp5s_rate d Λ κ * z))) := by
            refine mul_le_mul_of_nonneg_left (add_le_add hind ?_) hC.le
            exact mul_le_mul_of_nonneg_right hg2 (Real.exp_pos _).le
        _ = BAp5s_C d Λ κ * (1 + Λ ^ 2) * Real.exp (-(BAp5s_rate d Λ κ * z)) := by ring
        _ ≤ BAp5s_C d Λ κ * (1 + Λ ^ 2) * Real.exp (-(baPureRate d Λ κ * z)) :=
          mul_le_mul_of_nonneg_left hexp (by positivity)
    _ ≤ baPureB d Λ κ * Real.exp (-(baPureRate d Λ κ * z)) :=
      mul_le_mul_of_nonneg_right hBC (Real.exp_pos _).le

/-- **The edge-kernel bounds at the BA data** (`Mbound_AO`, `Mbound_AO2`, `(prop:ThfadC_short)`): every edge of a BA
molecule is `≤ B e^{-r |x-y|}`, with `B = baPureB d Λ κ ≥ 1`, `r = baPureRate d Λ κ > 0`, depending on `(d, Λ, κ)` only.
(a) the entries of `M(σ) = BAMsigma (BAMB ..)`, both charges (`M(-) = Mᴴ`); (b) the short propagator `Θ^{(s,s)}_{xy}`;
(c) the short chord `t Θ^{(s,s)}_{xy}`, `0 ≤ t ≤ 1`. -/
theorem baPure_edge (hd : 3 ≤ d) (hΛ : 0 < Λ) (hκ : 0 < κ) (hL : 3 ≤ L) (hg : 0 < g) (hgΛ : g ≤ Λ)
    (hr : BAReal d L g κ E m) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (∀ (σ : Bool) (x y : Zd d L), ‖BAMsigma d L (BAMB d L g (E : ℂ) m) σ x y‖ ≤
      baPureB d Λ κ * Real.exp (-(baPureRate d Λ κ * (zdistD d L (x - y) : ℝ)))) ∧
    (∀ (s : Bool) (x y : Zd d L), ‖BAThetaOf (BAMsigma d L (BAMB d L g (E : ℂ) m)) t s s x y‖ ≤
      baPureB d Λ κ * Real.exp (-(baPureRate d Λ κ * (zdistD d L (x - y) : ℝ)))) ∧
    (∀ (s : Bool) (x y : Zd d L), ‖(t : ℂ) * BAThetaOf (BAMsigma d L (BAMB d L g (E : ℂ) m)) t s s x y‖ ≤
      baPureB d Λ κ * Real.exp (-(baPureRate d Λ κ * (zdistD d L (x - y) : ℝ)))) := by
  have hd0 : 0 < d := by omega
  refine ⟨fun σ x y => ?_, fun s x y => KPure_theta_entry (by omega) hΛ hκ hL hg hgΛ hr ht0 ht1 s x y,
    fun s x y => ?_⟩
  · cases σ
    · simp only [BAMsigma, Bool.false_eq_true, ite_false, Matrix.conjTranspose_apply, norm_star]
      rw [KPure_zdistD_comm x y]
      exact KPure_MB_entry hd0 hΛ hκ hL hg hgΛ hr y x
    · simp only [BAMsigma, ite_true]
      exact KPure_MB_entry hd0 hΛ hκ hL hg hgΛ hr x y
  · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht0]
    exact (mul_le_of_le_one_left (norm_nonneg _) ht1).trans
      (KPure_theta_entry (by omega) hΛ hκ hL hg hgΛ hr ht0 ht1 s x y)

end Edges

/-! ## 2. The slot graph is connected: the spanning-tree path bound

The band bounds the distance of two nodes by the total length of the internal edges along the laminar path
(`KLMolecule_path_le`, `Loop/KLMolecule.lean:161`).  The slot graph of a cactus has the chords and the `M`-edges
(one cycle per node) as edges, a multigraph.  The abstract fact used is: if every subset of the vertices closed under the
edges is trivial, then the distance (in any pseudo-metric `ρ`) of two vertices of a labelling is at most the sum of the
lengths of all edges.  The proof grows a tree from the base vertex, one new vertex and one new edge at a time. -/

section Span

variable {V Eg X : Type*} [Fintype V] [DecidableEq V] [Fintype Eg] [DecidableEq Eg]

/-- Growing the tree: for a vertex set `S` containing the base `s` and an edge set `A` inside `S` such that every
vertex of `S` is within `ρ`-distance `Σ_A len` of `s`, every vertex is within `Σ_{all} len` (induction on `|V ∖ S|`;
a crossing edge exists as the closed sets are trivial, and it is new). -/
private theorem KPure_span_aux (c q : Eg → V) (ρ : X → X → ℕ) (hsymm : ∀ x y, ρ x y = ρ y x)
    (htri : ∀ x y z, ρ x z ≤ ρ x y + ρ y z) (f : V → X) (s : V)
    (hconn : ∀ S : Finset V, s ∈ S → (∀ e, c e ∈ S ↔ q e ∈ S) → ∀ v, v ∈ S) :
    ∀ k : ℕ, ∀ (S : Finset V) (A : Finset Eg), (Finset.univ \ S).card = k → s ∈ S →
      (∀ e ∈ A, c e ∈ S ∧ q e ∈ S) → (∀ v ∈ S, ρ (f v) (f s) ≤ ∑ e ∈ A, ρ (f (c e)) (f (q e))) →
      ∀ v, ρ (f v) (f s) ≤ ∑ e, ρ (f (c e)) (f (q e)) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro S A hk hs hA hb
    by_cases hall : ∀ v, v ∈ S
    · intro v
      exact (hb v (hall v)).trans (Finset.sum_le_sum_of_subset (Finset.subset_univ A))
    · push Not at hall
      obtain ⟨w0, hw0⟩ := hall
      have hcross : ∃ e, (c e ∈ S ∧ q e ∉ S) ∨ (c e ∉ S ∧ q e ∈ S) := by
        by_contra hno
        push Not at hno
        exact hw0 (hconn S hs (fun e => ⟨(hno e).1, fun h => by
          by_contra h'
          exact (hno e).2 h' h⟩) w0)
      obtain ⟨e, u, w, hu, hw, hep⟩ : ∃ (e : Eg) (u w : V), u ∈ S ∧ w ∉ S ∧
          ((c e = u ∧ q e = w) ∨ (c e = w ∧ q e = u)) := by
        obtain ⟨e, he | he⟩ := hcross
        · exact ⟨e, c e, q e, he.1, he.2, Or.inl ⟨rfl, rfl⟩⟩
        · exact ⟨e, q e, c e, he.2, he.1, Or.inr ⟨rfl, rfl⟩⟩
      have heA : e ∉ A := fun h => by
        have h' := hA e h
        rcases hep with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact hw (h2 ▸ h'.2)
        · exact hw (h1 ▸ h'.1)
      have hρ : ρ (f w) (f u) = ρ (f (c e)) (f (q e)) := by
        rcases hep with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · rw [h1, h2]; exact hsymm _ _
        · rw [h1, h2]
      have hss : Finset.univ \ insert w S ⊂ Finset.univ \ S := by
        rw [Finset.ssubset_iff_of_subset (Finset.sdiff_subset_sdiff (le_refl _) (Finset.subset_insert _ _))]
        exact ⟨w, by simp [hw], by simp⟩
      refine ih _ (hk ▸ Finset.card_lt_card hss) (insert w S) (insert e A) rfl (Finset.mem_insert_of_mem hs) ?_ ?_
      · intro e' he'
        rcases Finset.mem_insert.1 he' with rfl | he'
        · rcases hep with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact ⟨by rw [h1]; exact Finset.mem_insert_of_mem hu, by rw [h2]; exact Finset.mem_insert_self _ _⟩
          · exact ⟨by rw [h1]; exact Finset.mem_insert_self _ _, by rw [h2]; exact Finset.mem_insert_of_mem hu⟩
        · exact ⟨Finset.mem_insert_of_mem (hA e' he').1, Finset.mem_insert_of_mem (hA e' he').2⟩
      · intro v hv
        rw [Finset.sum_insert heA]
        rcases Finset.mem_insert.1 hv with rfl | hv
        · calc ρ (f v) (f s) ≤ ρ (f v) (f u) + ρ (f u) (f s) := htri _ _ _
            _ ≤ ρ (f (c e)) (f (q e)) + ∑ e' ∈ A, ρ (f (c e')) (f (q e')) := by
              rw [← hρ]; exact add_le_add le_rfl (hb u hu)
        · exact (hb v hv).trans (Nat.le_add_left _ _)

/-- **The spanning-tree bound**: if the only subsets of the vertices closed under the edges `c e — q e` are `∅` and
everything, then `ρ (f v) (f s)` is at most the sum of the lengths `ρ (f (c e)) (f (q e))` of all the edges. -/
private theorem KPure_span_le (c q : Eg → V) (ρ : X → X → ℕ) (hsymm : ∀ x y, ρ x y = ρ y x)
    (htri : ∀ x y z, ρ x z ≤ ρ x y + ρ y z) (hself : ∀ x, ρ x x = 0) (f : V → X)
    (hconn : ∀ S : Finset V, (∀ e, c e ∈ S ↔ q e ∈ S) → ∀ s ∈ S, ∀ v, v ∈ S) (s v : V) :
    ρ (f v) (f s) ≤ ∑ e, ρ (f (c e)) (f (q e)) :=
  KPure_span_aux c q ρ hsymm htri f s (fun S hs hS v => hconn S hS s hs v) _ {s} ∅ rfl (by simp) (by simp)
    (by
      intro v hv
      rw [Finset.mem_singleton] at hv
      subst hv
      simp [hself]) v

end Span

section SlotGraph

variable {n : ℕ} [NeZero n]

/-- One step up the tree: the parent `KLnodePar F x` of a non-root node `x` is a node of smaller depth, and `x ∈ F`
(a trimmed copy of the private `KLMolecule_anc_step`, `Loop/KLMolecule.lean:86`). -/
private theorem KPure_anc_step {F : Finset (Fin n × Fin n)} (hF : KLIsTSP F) (hn : 2 ≤ n) {x : Fin n × Fin n}
    (hx : x ∈ KLnodes F) (hxw : x ≠ KLwholeP n) :
    KLnodePar F x ∈ KLnodes F ∧ x ∈ F ∧
      (F.filter (KLArcLe (KLnodePar F x))).card < (F.filter (KLArcLe x)).card := by
  have hxF : x ∈ F := (Finset.mem_insert.1 hx).resolve_left hxw
  obtain ⟨hp, hdp, hne, -⟩ := KLnodePar_spec hF hn hx hxw
  have hpd : ¬KLArcLe (KLnodePar F x) x := fun h => hne (KLArcLe.antisymm hdp h).symm
  have hsub : F.filter (KLArcLe (KLnodePar F x)) ⊆ (F.filter (KLArcLe x)).erase x := by
    intro e he
    obtain ⟨heF, hpe⟩ := Finset.mem_filter.1 he
    refine Finset.mem_erase.2 ⟨?_, Finset.mem_filter.2 ⟨heF, KLArcLe.trans hdp hpe⟩⟩
    rintro rfl
    exact hpd hpe
  have hxmem : x ∈ F.filter (KLArcLe x) := Finset.mem_filter.2 ⟨hxF, ⟨le_refl _, le_refl _⟩⟩
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_erase_of_mem hxmem] at h1
  have := Finset.card_pos.2 ⟨x, hxmem⟩
  exact ⟨hp, hxF, by omega⟩

/-- **The closed sets of the slot graph are trivial**: a set `S` of slots such that both ends of every edge (a chord
`In J — Out J`, an `M`-edge `s — next s`) lie in `S` or both lie outside, and which contains one slot, contains every
slot.  Inside a node the `M`-edges form one cycle (`BAnextSlot_orbit`), the chord of a node `J` joins `In J` to the
slot `Out J` of the parent node, and the root node contains the leaf slot `n - 1` (`KLleafPar_root`). -/
private theorem KPure_slot_conn {F : Finset (Fin n × Fin n)} (hF : KLIsTSP F) (hn : 2 ≤ n) (S : Finset (BAslot F))
    (hS : ∀ e : ↥F ⊕ BAslot F, BACactusValSrc F e ∈ S ↔ BACactusValTgt F e ∈ S) (s : BAslot F) (hs : s ∈ S)
    (v : BAslot F) : v ∈ S := by
  have hnext : ∀ u, u ∈ S ↔ BAnextSlot F u ∈ S := fun u => hS (Sum.inr u)
  have hiter : ∀ (k : ℕ) (u : BAslot F), u ∈ S ↔ (BAnextSlot F)^[k] u ∈ S := by
    intro k
    induction k with
    | zero => intro u; exact Iff.rfl
    | succ k ih =>
      intro u
      rw [Function.iterate_succ_apply']
      exact (ih u).trans (hnext _)
  have hnode : ∀ u u' : BAslot F, BAslotNode F u = BAslotNode F u' → (u ∈ S ↔ u' ∈ S) := by
    intro u u' h
    obtain ⟨k, hk⟩ := (BAnextSlot_orbit hF hn u u').1 h
    rw [← hk]
    exact hiter k u
  have hchord : ∀ J : ↥F, BAslotIn F J ∈ S ↔ BAslotOut F J ∈ S := fun J => hS (Sum.inl J)
  have hn1 : n - 1 < n := by have := NeZero.pos n; omega
  have hr₁node : BAslotNode F (BAslotLeaf F ⟨n - 1, hn1⟩) = KLwholeP n := KLleafPar_root F rfl
  have key : ∀ m : ℕ, ∀ u : BAslot F, (F.filter (KLArcLe (BAslotNode F u))).card = m →
      (u ∈ S ↔ BAslotLeaf F ⟨n - 1, hn1⟩ ∈ S) := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro u hm
      by_cases hroot : BAslotNode F u = KLwholeP n
      · exact hnode u _ (hroot.trans hr₁node.symm)
      · obtain ⟨-, hxF, hcard⟩ := KPure_anc_step hF hn (BAslotNode_mem_nodes F u) hroot
        have h1 : u ∈ S ↔ BAslotIn F ⟨BAslotNode F u, hxF⟩ ∈ S := hnode u _ rfl
        have h3 := ih _ (hm ▸ hcard) (BAslotOut F ⟨BAslotNode F u, hxF⟩) rfl
        exact h1.trans ((hchord ⟨BAslotNode F u, hxF⟩).trans h3)
  exact (key _ v rfl).2 ((key _ s rfl).1 hs)

/-- **The path bound in the slot graph**: any two slots `s, t` of the cactus of `F` (`KLIsTSP F`, `2 ≤ n`) have labels
at distance at most the total length `T(β)` of the edges (chords `In J — Out J` and `M`-edges `s — next s`).  Stronger
than the two forms of the design (`|β s - β r₀| ≤ T`, and `|β s - β t| ≤ 2T`): every pair, factor one. -/
theorem baSlot_path_le {d L : ℕ} [NeZero L] {F : Finset (Fin n × Fin n)} (hF : KLIsTSP F) (hn : 2 ≤ n)
    (β : BAslot F → Zd d L) (s t : BAslot F) :
    zdistD d L (β s - β t) ≤
      ∑ e : ↥F ⊕ BAslot F, zdistD d L (β (BACactusValSrc F e) - β (BACactusValTgt F e)) :=
  KPure_span_le (BACactusValSrc F) (BACactusValTgt F) (fun x y : Zd d L => zdistD d L (x - y))
    KPure_zdistD_comm KPure_zdistD_tri (fun x => by simp) β
    (fun S hS s hs v => KPure_slot_conn hF hn S hS s hs v) t s

end SlotGraph

/-! ## 3. The tree bound

The twin of `KLMolecule_tree_bound` (`Loop/KLMolecule.lean:209`) with one label per slot.  For a labelling `b` of the
slots consistent with `δ` (`b (leaf v) = δ v`) the product of the edge entries is `≤ Γ e^{-r T(b)}`, `T(b)` the total
edge length, and the path bound gives `T(b) ≥ |δ_i - δ_j|` and `T(b) ≥ |δ_i - b s|`; the factor `e^{-(r/4)T}` pays for
the decay in `|δ_i - δ_j|`, the factor `e^{-(r/4)T}` for the sum over the `N ≤ n + 2n²` slot labels. -/

section TreeBound

variable {d L : ℕ} [NeZero L] {n : ℕ} [NeZero n]

omit [NeZero L] [NeZero n] in
private theorem KPure_prod_const_exp {Eg : Type*} [Fintype Eg] (z : Eg → ℕ) (B r : ℝ) :
    ∏ e, (B * Real.exp (-(r * (z e : ℝ)))) =
      B ^ Fintype.card Eg * Real.exp (-(r * ((∑ e, z e : ℕ) : ℝ))) := by
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, ← Real.exp_sum]
  congr 2
  simp only [Nat.cast_sum, Finset.mul_sum, Finset.sum_neg_distrib]

omit [NeZero L] [NeZero n] in
private theorem KPure_card_le (F : Finset (Fin n × Fin n)) : F.card ≤ n * n := by
  simpa using Finset.card_le_univ F

/-- **The tree bound** (core): if the product of the edge entries at every labelling `β` of the slots consistent with
`δ` (`β (leaf v) = δ v`) is at most `Γ e^{-r T(β)}`, `T(β) = Σ_e |β (src e) - β (tgt e)|`, then the self-energy of the
tree `F` satisfies `|Σ_F(δ)| ≤ Γ S₀^{N₀} e^{-(r/4) |δ_i - δ_j|}`, `N₀ = n + 2n²` (the largest number of slots),
`S₀ = expC (d-2) (r / (4 N₀))`.  The twin of `KLMolecule_tree_bound`, `Loop/KLMolecule.lean:209`. -/
theorem baSigmaTree_bound (hd : 2 ≤ d) {F : Finset (Fin n × Fin n)} (hF : KLIsTSP F) (hn : 2 ≤ n)
    (M : Bool → Matrix (Zd d L) (Zd d L) ℂ) (t : ℝ) (σ : Fin n → Bool) (δ : Fin n → Zd d L) {r Γ : ℝ}
    (hr : 0 < r) (hΓ : 0 ≤ Γ)
    (hprod : ∀ β : BAslot F → Zd d L, (∀ v : Fin n, β (BAslotLeaf F v) = δ v) →
      ∏ e : ↥F ⊕ BAslot F, ‖BACactusValEdgeW M t F σ e (β (BACactusValSrc F e)) (β (BACactusValTgt F e))‖ ≤
        Γ * Real.exp (-(r * ((∑ e : ↥F ⊕ BAslot F,
          zdistD d L (β (BACactusValSrc F e) - β (BACactusValTgt F e)) : ℕ) : ℝ))))
    (i j : Fin n) :
    ‖BASigmaTree d L M t F σ δ‖ ≤
      Γ * (expC (d - 2) (r / (4 * ((n + 2 * (n * n) : ℕ) : ℝ)))) ^ (n + 2 * (n * n)) *
        Real.exp (-(r / 4 * (zdistD d L (δ i - δ j) : ℝ))) := by
  have hnpos : 0 < n := NeZero.pos n
  have hN0 : (0 : ℝ) < ((n + 2 * (n * n) : ℕ) : ℝ) := by
    exact_mod_cast (by positivity : 0 < n + 2 * (n * n))
  set N0 : ℕ := n + 2 * (n * n) with hN0def
  set lam : ℝ := r / (4 * (N0 : ℝ)) with hlam_def
  have hlam : 0 < lam := by positivity
  set S : ℝ := expC (d - 2) lam with hS
  set g : Zd d L → ℝ := fun y => Real.exp (-(lam * (zdistD d L (δ i - y) : ℝ))) with hg
  have hgS : ∑ y, g y ≤ S := BAsum_exp_decay_le d L hd lam hlam (δ i)
  have hg0 : 0 ≤ ∑ y, g y := Finset.sum_nonneg fun _ _ => (Real.exp_pos _).le
  have hg1 : 1 ≤ ∑ y, g y := by
    calc (1 : ℝ) = g (δ i) := by simp [hg]
      _ ≤ ∑ y, g y := Finset.single_le_sum (f := g) (fun _ _ => (Real.exp_pos _).le) (Finset.mem_univ _)
  have hS1 : 1 ≤ S := hg1.trans hgS
  set Ns : ℕ := Fintype.card (BAslot F) with hNs
  have hNsle : Ns ≤ N0 := by
    rw [hNs, BAslot_card]
    have := KPure_card_le F
    omega
  set C0 := Γ * Real.exp (-(r / 4 * (zdistD d L (δ i - δ j) : ℝ))) with hC0def
  have hC0 : 0 ≤ C0 := by positivity
  have hpt : ∀ b : BAslot F → Zd d L,
      ‖(∏ ℓ : Fin n, (1 : Matrix (Zd d L) (Zd d L) ℂ) (δ ℓ) (b (BAslotLeaf F ℓ))) *
        ∏ e : ↥F ⊕ BAslot F, BACactusValEdgeW M t F σ e (b (BACactusValSrc F e)) (b (BACactusValTgt F e))‖ ≤
        C0 * ∏ s, g (b s) := by
    intro b
    by_cases hcons : ∀ v : Fin n, b (BAslotLeaf F v) = δ v
    · have h1 : ∏ v : Fin n, (1 : Matrix (Zd d L) (Zd d L) ℂ) (δ v) (b (BAslotLeaf F v)) = 1 :=
        Finset.prod_eq_one fun v _ => by rw [hcons v, Matrix.one_apply_eq]
      rw [h1, one_mul, norm_prod]
      have hE := hprod b hcons
      set T : ℕ := ∑ e : ↥F ⊕ BAslot F, zdistD d L (b (BACactusValSrc F e) - b (BACactusValTgt F e)) with hT
      have hT0 : (0 : ℝ) ≤ (T : ℝ) := Nat.cast_nonneg _
      have hij : (zdistD d L (δ i - δ j) : ℝ) ≤ (T : ℝ) := by
        have h := baSlot_path_le hF hn b (BAslotLeaf F i) (BAslotLeaf F j)
        rw [hcons i, hcons j] at h
        exact_mod_cast h
      have hnode : ∀ s, (zdistD d L (δ i - b s) : ℝ) ≤ (T : ℝ) := by
        intro s
        have h := baSlot_path_le hF hn b (BAslotLeaf F i) s
        rw [hcons i] at h
        exact_mod_cast h
      have hexp : Real.exp (-(r * (T : ℝ))) ≤
          Real.exp (-(r / 4 * (zdistD d L (δ i - δ j) : ℝ))) * ∏ s, g (b s) := by
        simp only [hg, ← Real.exp_sum, ← Real.exp_add]
        apply Real.exp_le_exp.2
        have h2 : ∑ s : BAslot F, (zdistD d L (δ i - b s) : ℝ) ≤ (Ns : ℝ) * (T : ℝ) := by
          calc _ ≤ ∑ _s : BAslot F, (T : ℝ) := Finset.sum_le_sum fun s _ => hnode s
            _ = (Ns : ℝ) * (T : ℝ) := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        have h3 : (Ns : ℝ) ≤ (N0 : ℝ) := by exact_mod_cast hNsle
        have h4 : lam * ∑ s : BAslot F, (zdistD d L (δ i - b s) : ℝ) ≤ r / 4 * (T : ℝ) := by
          calc _ ≤ lam * ((N0 : ℝ) * (T : ℝ)) := by
                gcongr
                exact h2.trans (by gcongr)
            _ = r / 4 * (T : ℝ) := by rw [hlam_def]; field_simp
        have h5 : r / 4 * (zdistD d L (δ i - δ j) : ℝ) ≤ r / 4 * (T : ℝ) :=
          mul_le_mul_of_nonneg_left hij (by positivity)
        have h6 : ∑ s : BAslot F, -(lam * (zdistD d L (δ i - b s) : ℝ)) =
            -(lam * ∑ s : BAslot F, (zdistD d L (δ i - b s) : ℝ)) := by
          rw [Finset.mul_sum, Finset.sum_neg_distrib]
        rw [h6]
        nlinarith [mul_nonneg hr.le hT0]
      calc _ ≤ Γ * Real.exp (-(r * (T : ℝ))) := hE
        _ ≤ Γ * (Real.exp (-(r / 4 * (zdistD d L (δ i - δ j) : ℝ))) * ∏ s, g (b s)) :=
          mul_le_mul_of_nonneg_left hexp hΓ
        _ = C0 * ∏ s, g (b s) := by rw [hC0def]; ring
    · push Not at hcons
      obtain ⟨v, hv⟩ := hcons
      have h0 : ∏ v : Fin n, (1 : Matrix (Zd d L) (Zd d L) ℂ) (δ v) (b (BAslotLeaf F v)) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ v) (Matrix.one_apply_ne (Ne.symm hv))
      rw [h0, zero_mul, norm_zero]
      exact mul_nonneg hC0 (Finset.prod_nonneg fun s _ => (Real.exp_pos _).le)
  have hsum : ∑ b : BAslot F → Zd d L, ∏ s, g (b s) = (∑ y, g y) ^ Ns := by
    have h := Finset.prod_univ_sum (fun _ : BAslot F => (Finset.univ : Finset (Zd d L))) (fun _ x => g x)
    rw [Fintype.piFinset_univ] at h
    rw [← h, Finset.prod_const, Finset.card_univ]
  unfold BASigmaTree KLgval
  calc _ ≤ ∑ b : BAslot F → Zd d L, C0 * ∏ s, g (b s) :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => hpt b)
    _ = C0 * (∑ y, g y) ^ Ns := by rw [← Finset.mul_sum, hsum]
    _ ≤ C0 * S ^ N0 := by
        gcongr
        exact (pow_le_pow_left₀ hg0 hgS Ns).trans (pow_le_pow_right₀ hS1 hNsle)
    _ = Γ * S ^ N0 * Real.exp (-(r / 4 * (zdistD d L (δ i - δ j) : ℝ))) := by rw [hC0def]; ring

/-- The product hypothesis of `baSigmaTree_bound` from entrywise bounds: `∏_e ‖E_e‖ ≤ B^{|ℰ|} e^{-r T} ≤ B^{n+3n²} e^{-r T}`
(the cactus has `|F| + (n + 2|F|) = n + 3|F| ≤ n + 3n²` edges). -/
private theorem KPure_hprod_of_entries {F : Finset (Fin n × Fin n)} (M : Bool → Matrix (Zd d L) (Zd d L) ℂ) (t : ℝ)
    (σ : Fin n → Bool) {B r : ℝ} (hB : 1 ≤ B)
    (hE : ∀ (e : ↥F ⊕ BAslot F) (x y : Zd d L),
      ‖BACactusValEdgeW M t F σ e x y‖ ≤ B * Real.exp (-(r * (zdistD d L (x - y) : ℝ))))
    (β : BAslot F → Zd d L) :
    ∏ e : ↥F ⊕ BAslot F, ‖BACactusValEdgeW M t F σ e (β (BACactusValSrc F e)) (β (BACactusValTgt F e))‖ ≤
      B ^ (n + 3 * (n * n)) * Real.exp (-(r * ((∑ e : ↥F ⊕ BAslot F,
        zdistD d L (β (BACactusValSrc F e) - β (BACactusValTgt F e)) : ℕ) : ℝ))) := by
  have hcard : Fintype.card (↥F ⊕ BAslot F) ≤ n + 3 * (n * n) := by
    rw [Fintype.card_sum, Fintype.card_coe, BAslot_card]
    have := KPure_card_le F
    omega
  calc ∏ e : ↥F ⊕ BAslot F, ‖BACactusValEdgeW M t F σ e (β (BACactusValSrc F e)) (β (BACactusValTgt F e))‖
      ≤ ∏ e : ↥F ⊕ BAslot F, (B * Real.exp (-(r * (zdistD d L (β (BACactusValSrc F e) -
          β (BACactusValTgt F e)) : ℝ)))) :=
        Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun e _ => hE e _ _
    _ = B ^ Fintype.card (↥F ⊕ BAslot F) * Real.exp (-(r * ((∑ e : ↥F ⊕ BAslot F,
          zdistD d L (β (BACactusValSrc F e) - β (BACactusValTgt F e)) : ℕ) : ℝ))) :=
        KPure_prod_const_exp (fun e => zdistD d L (β (BACactusValSrc F e) - β (BACactusValTgt F e))) B r
    _ ≤ B ^ (n + 3 * (n * n)) * Real.exp (-(r * ((∑ e : ↥F ⊕ BAslot F,
          zdistD d L (β (BACactusValSrc F e) - β (BACactusValTgt F e)) : ℕ) : ℝ))) :=
        mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hB hcard) (Real.exp_pos _).le

/-- **The tree bound, entrywise form**: if every edge weight of the cactus of `F` has entries `≤ B e^{-r |x-y|}`,
`B ≥ 1`, then `|Σ_F(δ)| ≤ B^{n+3n²} S₀^{N₀} e^{-(r/4) |δ_i - δ_j|}`. -/
theorem baSigmaTree_bound_of_entries (hd : 2 ≤ d) {F : Finset (Fin n × Fin n)} (hF : KLIsTSP F) (hn : 2 ≤ n)
    (M : Bool → Matrix (Zd d L) (Zd d L) ℂ) (t : ℝ) (σ : Fin n → Bool) (δ : Fin n → Zd d L) {B r : ℝ}
    (hB : 1 ≤ B) (hr : 0 < r)
    (hE : ∀ (e : ↥F ⊕ BAslot F) (x y : Zd d L),
      ‖BACactusValEdgeW M t F σ e x y‖ ≤ B * Real.exp (-(r * (zdistD d L (x - y) : ℝ))))
    (i j : Fin n) :
    ‖BASigmaTree d L M t F σ δ‖ ≤
      B ^ (n + 3 * (n * n)) * (expC (d - 2) (r / (4 * ((n + 2 * (n * n) : ℕ) : ℝ)))) ^ (n + 2 * (n * n)) *
        Real.exp (-(r / 4 * (zdistD d L (δ i - δ j) : ℝ))) :=
  baSigmaTree_bound hd hF hn M t σ δ hr (pow_nonneg (by linarith) _)
    (fun β _ => KPure_hprod_of_entries M t σ hB hE β) i j

/-- **The tree bound in the form of the ticket**: `|Σ_F(δ)| ≤ B^{#edges} S₀^{N₀} e^{-(r/4) max_{i,j} |δ_i - δ_j|}`
(`#edges ≤ n + 3n²`), the pair `(i, j)` of `baSigmaTree_bound_of_entries` realising `KLmaxDist`. -/
theorem baSigmaTree_bound_maxDist (hd : 2 ≤ d) {F : Finset (Fin n × Fin n)} (hF : KLIsTSP F) (hn : 2 ≤ n)
    (M : Bool → Matrix (Zd d L) (Zd d L) ℂ) (t : ℝ) (σ : Fin n → Bool) (δ : Fin n → Zd d L) {B r : ℝ}
    (hB : 1 ≤ B) (hr : 0 < r)
    (hE : ∀ (e : ↥F ⊕ BAslot F) (x y : Zd d L),
      ‖BACactusValEdgeW M t F σ e x y‖ ≤ B * Real.exp (-(r * (zdistD d L (x - y) : ℝ)))) :
    ‖BASigmaTree d L M t F σ δ‖ ≤
      B ^ (n + 3 * (n * n)) * (expC (d - 2) (r / (4 * ((n + 2 * (n * n) : ℕ) : ℝ)))) ^ (n + 2 * (n * n)) *
        Real.exp (-(r / 4 * (KLmaxDist d L δ : ℝ))) := by
  obtain ⟨i, j, hij⟩ := KLMolecule_exists_pair δ
  rw [hij]
  exact baSigmaTree_bound_of_entries hd hF hn M t σ δ hB hr hE i j

/-- The entry bounds of every edge of a tree whose chords are short: `M`-edges by `hM`, a chord `tΘ^{(σ_i,σ_j)}` with
`σ_i = σ_j` by `hΘ`. -/
private theorem KPure_edge_entries {F : Finset (Fin n × Fin n)} (M : Bool → Matrix (Zd d L) (Zd d L) ℂ) (t : ℝ)
    (σ : Fin n → Bool) (hsame : ∀ e ∈ F, σ e.1 = σ e.2) {B r : ℝ}
    (hM : ∀ (s : Bool) (x y : Zd d L), ‖M s x y‖ ≤ B * Real.exp (-(r * (zdistD d L (x - y) : ℝ))))
    (hΘ : ∀ (s : Bool) (x y : Zd d L),
      ‖(t : ℂ) * BAThetaOf M t s s x y‖ ≤ B * Real.exp (-(r * (zdistD d L (x - y) : ℝ)))) :
    ∀ (e : ↥F ⊕ BAslot F) (x y : Zd d L),
      ‖BACactusValEdgeW M t F σ e x y‖ ≤ B * Real.exp (-(r * (zdistD d L (x - y) : ℝ))) := by
  rintro (J | s) x y
  · change ‖((t : ℂ) • BAThetaOf M t (σ J.1.1) (σ J.1.2)) x y‖ ≤ _
    rw [Matrix.smul_apply, smul_eq_mul, ← hsame J.1 J.2]
    exact hΘ _ x y
  · exact hM _ x y

end TreeBound

/-! ## 4. The molecule bound and `(eq:molecule-decay)` -/

section Molecule

variable {d L : ℕ} [NeZero L] {n : ℕ} [NeZero n]

/-- **The molecule bound** `(eq:molecule-decay)` for one charge vector: in the layer `π = ∅` every chord of every tree is
a short edge (`KLMolecule_same_charge`), so the entry bounds (a) of `M(σ)` and (c) of the short chord `tΘ^{(s,s)}` give
`|Σ^{(∅)}(δ)| ≤ |TSP n| B^{n+3n²} S₀^{N₀} e^{-(r/4) max_{i,j} |δ_i - δ_j|}`, for every `σ`. -/
theorem baSigmaPi_empty_bound (hd : 2 ≤ d) (hn : 2 ≤ n) (M : Bool → Matrix (Zd d L) (Zd d L) ℂ) (t : ℝ)
    (σ : Fin n → Bool) {B r : ℝ} (hB : 1 ≤ B) (hr : 0 < r)
    (hM : ∀ (s : Bool) (x y : Zd d L), ‖M s x y‖ ≤ B * Real.exp (-(r * (zdistD d L (x - y) : ℝ))))
    (hΘ : ∀ (s : Bool) (x y : Zd d L),
      ‖(t : ℂ) * BAThetaOf M t s s x y‖ ≤ B * Real.exp (-(r * (zdistD d L (x - y) : ℝ))))
    (δ : Fin n → Zd d L) :
    ‖BASigmaPi d L n M t σ ∅ δ‖ ≤ ((TSP n).card : ℝ) *
      (B ^ (n + 3 * (n * n)) * (expC (d - 2) (r / (4 * ((n + 2 * (n * n) : ℕ) : ℝ)))) ^ (n + 2 * (n * n)) *
        Real.exp (-(r / 4 * (KLmaxDist d L δ : ℝ)))) := by
  have hnn : (0 : ℝ) < ((n + 2 * (n * n) : ℕ) : ℝ) := by
    have := NeZero.pos n
    exact_mod_cast (by positivity : 0 < n + 2 * (n * n))
  have hlam : 0 < r / (4 * ((n + 2 * (n * n) : ℕ) : ℝ)) := by positivity
  have hS0 : 0 < expC (d - 2) (r / (4 * ((n + 2 * (n * n) : ℕ) : ℝ))) := by unfold expC; positivity
  have hB0 : 0 < B := by linarith
  have hX : 0 ≤ B ^ (n + 3 * (n * n)) * (expC (d - 2) (r / (4 * ((n + 2 * (n * n) : ℕ) : ℝ)))) ^
      (n + 2 * (n * n)) * Real.exp (-(r / 4 * (KLmaxDist d L δ : ℝ))) := by positivity
  unfold BASigmaPi
  calc ‖∑ F ∈ KLTSPlong n σ ∅, BASigmaTree d L M t F σ δ‖
      ≤ ∑ F ∈ KLTSPlong n σ ∅, (B ^ (n + 3 * (n * n)) *
          (expC (d - 2) (r / (4 * ((n + 2 * (n * n) : ℕ) : ℝ)))) ^ (n + 2 * (n * n)) *
            Real.exp (-(r / 4 * (KLmaxDist d L δ : ℝ)))) := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun F hF => ?_)
        have hsame := KLMolecule_same_charge hF
        have hFT : F ∈ TSP n := (Finset.mem_filter.1 hF).1
        exact baSigmaTree_bound_maxDist hd (KLisTSP_of_mem_TSP hFT) hn M t σ δ hB hr
          (KPure_edge_entries M t σ hsame hM hΘ)
    _ = ((KLTSPlong n σ ∅).card : ℝ) * (B ^ (n + 3 * (n * n)) *
          (expC (d - 2) (r / (4 * ((n + 2 * (n * n) : ℕ) : ℝ)))) ^ (n + 2 * (n * n)) *
            Real.exp (-(r / 4 * (KLmaxDist d L δ : ℝ)))) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((TSP n).card : ℝ) * (B ^ (n + 3 * (n * n)) *
          (expC (d - 2) (r / (4 * ((n + 2 * (n * n) : ℕ) : ℝ)))) ^ (n + 2 * (n * n)) *
            Real.exp (-(r / 4 * (KLmaxDist d L δ : ℝ)))) := by
        refine mul_le_mul_of_nonneg_right ?_ hX
        exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)

end Molecule

/-- **`(eq:molecule-decay)` for `BASig`** (`A:691`): `|Σ^{(∅)}(t,σ,δ)| ≤ C e^{-c max_{i,j} |δ_i - δ_j|}` for **every**
charge vector `σ`, in the form `SigDecayAbs d n L (BASig ..)` consumed by `indStepAbs_of` (`Loop/KLIndStepB.lean:879`),
uniformly in the family `ι` of `(L, g, E, m, t)`: `3 ≤ L i`, `0 < g i ≤ Λ`, `BAReal d (L i) (g i) κ (E i) (m i)`,
`0 ≤ t i ≤ 1`.  `C = |TSP n| B^{n+3n²} S₀^{N₀}`, `c = r/4` depend on `(d, n, Λ, κ)` only. -/
theorem baSig_decay {ι : Type} {d n : ℕ} [NeZero n] (hd : 3 ≤ d) (hn : 3 ≤ n) {Λ κ : ℝ} (hΛ : 0 < Λ) (hκ : 0 < κ)
    (L : ι → ℕ) [∀ i, NeZero (L i)] (g E : ι → ℝ) (m : ι → ℂ) (t : ι → ℝ) (hL : ∀ i, 3 ≤ L i) (hg : ∀ i, 0 < g i)
    (hgΛ : ∀ i, g i ≤ Λ) (hr : ∀ i, BAReal d (L i) (g i) κ (E i) (m i)) (ht0 : ∀ i, 0 ≤ t i)
    (ht1 : ∀ i, t i ≤ 1) :
    SigDecayAbs d n L (BASig d n L g E m t) := by
  have hd0 : 0 < d := by omega
  have hB1 := baPureB_one_le d Λ κ
  have hr0 := baPureRate_pos hd0 hΛ hκ
  have hnn : (0 : ℝ) < ((n + 2 * (n * n) : ℕ) : ℝ) := by
    have := NeZero.pos n
    exact_mod_cast (by positivity : 0 < n + 2 * (n * n))
  have hlam : 0 < baPureRate d Λ κ / (4 * ((n + 2 * (n * n) : ℕ) : ℝ)) := by positivity
  have hS0 : 0 < expC (d - 2) (baPureRate d Λ κ / (4 * ((n + 2 * (n * n) : ℕ) : ℝ))) := by
    unfold expC; positivity
  have hB0 : 0 < baPureB d Λ κ := by linarith
  have hT : 0 < ((TSP n).card : ℝ) := by exact_mod_cast Finset.card_pos.2 ⟨∅, empty_mem_TSP n⟩
  refine ⟨((TSP n).card : ℝ) * (baPureB d Λ κ ^ (n + 3 * (n * n)) *
    (expC (d - 2) (baPureRate d Λ κ / (4 * ((n + 2 * (n * n) : ℕ) : ℝ)))) ^ (n + 2 * (n * n))), by positivity,
    baPureRate d Λ κ / 4, by positivity, fun i σ δ => ?_⟩
  obtain ⟨hM, -, hΘ⟩ := baPure_edge hd hΛ hκ (hL i) (hg i) (hgΛ i) (hr i) (ht0 i) (ht1 i)
  have h := baSigmaPi_empty_bound (d := d) (L := L i) (by omega) (by omega)
    (BAMsigma d (L i) (BAMB d (L i) (g i) ((E i : ℝ) : ℂ) (m i))) (t i) σ hB1 hr0 hM hΘ δ
  calc ‖BASig d n L g E m t i σ δ‖ ≤ _ := h
    _ = _ := by ring

/-! ## 5. Pure loops

`lem_pureloop` (`A:643-654`): for a constant charge vector `σ = (σ₀, …, σ₀)` every tree of `TSP n` has no long chord,
so `𝒦^{(n)} = W^{-d(n-1)} K^{(∅)}`; `K^{(∅)}(a) = Σ_δ Σ^{(∅)}(δ) ∏_v Θ^{(σ₀,σ₀)}(a_v, δ_v)` (first stage), the molecule
decays in `max |δ_i - δ_j|` (`baSigmaPi_empty_bound`) and the leaves `Θ^{(σ₀,σ₀)}(a_v, ·)` decay in `|a_v - δ_v|`
(`baPure_edge` (b)); the convolution `max |a_i - a_j| ≤ max |δ_i - δ_j| + 2 Σ_v |a_v - δ_v|` and `Σ_x e^{-(r/2)|y-x|} ≤ expC`
finish. -/

section Pure

/-- **The pure loop reduces to `K^{(∅)}`** (`(eq_K-Kpi)` for a constant charge vector, `A:643-654`): with `σ = (σ₀,…,σ₀)`
no tree has a long chord (`KLFlong F σ = ∅`), so only `π = ∅` survives in `baK_eq_sum_Kpi`, and
`𝒦^{(n)} = W^{-d(n-1)} Σ_δ Σ^{(∅)}(δ) ∏_v Θ^{(σ₀,σ₀)}(a_v, δ_v)` (`baKpi_eq_sum_SigmaPi`). -/
theorem baK_pure_eq (d : ℕ) {κ g : ℝ} (hκ : 0 < κ) (hg : 0 < g) {L : ℕ} [NeZero L] (hL : 3 ≤ L) (W : ℕ) {E : ℝ}
    {m : ℂ} (hr : BAReal d L g κ E m) {t : ℝ} (ht : t ∈ Set.Ico (0 : ℝ) 1) {n : ℕ} [NeZero n] (hn : 3 ≤ n)
    (σ₀ : Bool) (a : Fin n → Zd d L) :
    BAKsol d L W (BAMsigma d L (BAMB d L g (E : ℂ) m)) (PropSpin m) t (KLloopOf d L (fun _ => σ₀) a) =
      (((W : ℂ) ^ d)⁻¹) ^ (n - 1) * ∑ δ : Fin n → Zd d L,
        BASigmaPi d L n (BAMsigma d L (BAMB d L g (E : ℂ) m)) t (fun _ => σ₀) ∅ δ *
          ∏ v, BAThetaOf (BAMsigma d L (BAMB d L g (E : ℂ) m)) t σ₀ σ₀ (a v) (δ v) := by
  rw [baK_eq_sum_Kpi d hκ hg hL W hr ht hn (fun _ => σ₀) a]
  congr 1
  rw [Finset.sum_eq_single (∅ : Finset (Fin n × Fin n))]
  · exact baKpi_eq_sum_SigmaPi _ t _ a ∅
  · intro π _ hπ
    simp only [BAKpi]
    refine Finset.sum_eq_zero fun F hF => ?_
    exfalso
    have hFl : KLFlong F (fun _ : Fin n => σ₀) = π := (Finset.mem_filter.1 hF).2
    have h0 : KLFlong F (fun _ : Fin n => σ₀) = ∅ := by simp [KLFlong]
    exact hπ (hFl.symm.trans h0)
  · intro h
    exact absurd (Finset.empty_mem_powerset _) h

variable {d L : ℕ} [NeZero L] {n : ℕ} [NeZero n]

/-- The constant of the molecule bound: `|TSP n| B^{n+3n²} S₀^{N₀}`. -/
private noncomputable def KPure_CSig (d n : ℕ) (B r : ℝ) : ℝ :=
  ((TSP n).card : ℝ) * (B ^ (n + 3 * (n * n)) *
    (expC (d - 2) (r / (4 * ((n + 2 * (n * n) : ℕ) : ℝ)))) ^ (n + 2 * (n * n)))

omit [NeZero n] in
private theorem KPure_CSig_pos (hn : 0 < n) {B r : ℝ} (hB : 1 ≤ B) (hr : 0 < r) : 0 < KPure_CSig d n B r := by
  have hnn : (0 : ℝ) < ((n + 2 * (n * n) : ℕ) : ℝ) := by exact_mod_cast (by positivity : 0 < n + 2 * (n * n))
  have hlam : 0 < r / (4 * ((n + 2 * (n * n) : ℕ) : ℝ)) := by positivity
  have hS0 : 0 < expC (d - 2) (r / (4 * ((n + 2 * (n * n) : ℕ) : ℝ))) := by unfold expC; positivity
  have hB0 : 0 < B := by linarith
  have hT : 0 < ((TSP n).card : ℝ) := by exact_mod_cast Finset.card_pos.2 ⟨∅, empty_mem_TSP n⟩
  unfold KPure_CSig
  positivity

/-- The distance of the labels `a` is at most that of the molecule labels `δ` plus twice the total displacement:
`max |a_i - a_j| ≤ max |δ_i - δ_j| + 2 Σ_v |a_v - δ_v|`. -/
private theorem KPure_maxDist_le (a δ : Fin n → Zd d L) :
    (KLmaxDist d L a : ℝ) ≤ (KLmaxDist d L δ : ℝ) + 2 * ∑ v, (zdistD d L (a v - δ v) : ℝ) := by
  obtain ⟨i, j, hij⟩ := KLMolecule_exists_pair a
  have h1 := KPure_zdistD_tri (a i) (δ i) (a j)
  have h2 := KPure_zdistD_tri (δ i) (δ j) (a j)
  have h3 : zdistD d L (δ i - δ j) ≤ KLmaxDist d L δ :=
    Finset.le_sup (f := fun q : Fin n × Fin n => zdistD d L (δ q.1 - δ q.2)) (Finset.mem_univ (i, j))
  have h4 : zdistD d L (δ j - a j) = zdistD d L (a j - δ j) := KPure_zdistD_comm _ _
  have hs : ∀ v : Fin n, (zdistD d L (a v - δ v) : ℝ) ≤ ∑ w, (zdistD d L (a w - δ w) : ℝ) := fun v =>
    Finset.single_le_sum (f := fun w => (zdistD d L (a w - δ w) : ℝ)) (fun _ _ => Nat.cast_nonneg _)
      (Finset.mem_univ v)
  have h5 : zdistD d L (a i - a j) ≤ KLmaxDist d L δ + zdistD d L (a i - δ i) + zdistD d L (a j - δ j) := by
    omega
  rw [hij]
  have h6 : (zdistD d L (a i - a j) : ℝ) ≤ (KLmaxDist d L δ : ℝ) + (zdistD d L (a i - δ i) : ℝ) +
      (zdistD d L (a j - δ j) : ℝ) := by exact_mod_cast h5
  linarith [hs i, hs j]

/-- **The first-stage bound for the pure loop**: `|Σ_δ Σ^{(∅)}(δ) ∏_v Θ^{(σ₀,σ₀)}(a_v, δ_v)| ≤ C_Σ (B S')^n e^{-(r/4) max|a_i - a_j|}`,
`S' = expC (d-2) (r/2)`. -/
private theorem KPure_K_bound (hd : 2 ≤ d) (hn : 2 ≤ n) (M : Bool → Matrix (Zd d L) (Zd d L) ℂ) (t : ℝ) (σ₀ : Bool)
    {B r : ℝ} (hB : 1 ≤ B) (hr : 0 < r)
    (hM : ∀ (s : Bool) (x y : Zd d L), ‖M s x y‖ ≤ B * Real.exp (-(r * (zdistD d L (x - y) : ℝ))))
    (hΘ0 : ∀ (s : Bool) (x y : Zd d L),
      ‖BAThetaOf M t s s x y‖ ≤ B * Real.exp (-(r * (zdistD d L (x - y) : ℝ))))
    (hΘ : ∀ (s : Bool) (x y : Zd d L),
      ‖(t : ℂ) * BAThetaOf M t s s x y‖ ≤ B * Real.exp (-(r * (zdistD d L (x - y) : ℝ))))
    (a : Fin n → Zd d L) :
    ‖∑ δ : Fin n → Zd d L, BASigmaPi d L n M t (fun _ => σ₀) ∅ δ * ∏ v, BAThetaOf M t σ₀ σ₀ (a v) (δ v)‖ ≤
      KPure_CSig d n B r * (B * expC (d - 2) (r / 2)) ^ n * Real.exp (-(r / 4 * (KLmaxDist d L a : ℝ))) := by
  have hB0 : 0 < B := by linarith
  have hCS : 0 ≤ KPure_CSig d n B r := (KPure_CSig_pos (NeZero.pos n) hB hr).le
  have hSig : ∀ δ : Fin n → Zd d L, ‖BASigmaPi d L n M t (fun _ => σ₀) ∅ δ‖ ≤
      KPure_CSig d n B r * Real.exp (-(r / 4 * (KLmaxDist d L δ : ℝ))) := fun δ => by
    refine (baSigmaPi_empty_bound hd hn M t (fun _ => σ₀) hB hr hM hΘ δ).trans (le_of_eq ?_)
    unfold KPure_CSig
    ring
  set f : Fin n → Zd d L → ℝ := fun v x => B * Real.exp (-(r / 2 * (zdistD d L (a v - x) : ℝ))) with hf
  have hpt : ∀ δ : Fin n → Zd d L,
      ‖BASigmaPi d L n M t (fun _ => σ₀) ∅ δ * ∏ v, BAThetaOf M t σ₀ σ₀ (a v) (δ v)‖ ≤
        KPure_CSig d n B r * Real.exp (-(r / 4 * (KLmaxDist d L a : ℝ))) * ∏ v, f v (δ v) := by
    intro δ
    rw [norm_mul, norm_prod]
    have h1 := hSig δ
    have h2 : ∏ v, ‖BAThetaOf M t σ₀ σ₀ (a v) (δ v)‖ ≤
        ∏ v, (B * Real.exp (-(r * (zdistD d L (a v - δ v) : ℝ)))) :=
      Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun v _ => hΘ0 σ₀ (a v) (δ v)
    have hDa := KPure_maxDist_le a δ
    have hz0 : (0 : ℝ) ≤ ∑ v, (zdistD d L (a v - δ v) : ℝ) := Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
    have h3 : ∏ v, (B * Real.exp (-(r * (zdistD d L (a v - δ v) : ℝ)))) =
        B ^ n * Real.exp (-(r * ∑ v, (zdistD d L (a v - δ v) : ℝ))) := by
      have := KPure_prod_const_exp (fun v => zdistD d L (a v - δ v)) B r
      simpa [Nat.cast_sum] using this
    have h4 : ∏ v, f v (δ v) = B ^ n * Real.exp (-((r / 2) * ∑ v, (zdistD d L (a v - δ v) : ℝ))) := by
      have := KPure_prod_const_exp (fun v => zdistD d L (a v - δ v)) B (r / 2)
      simpa [Nat.cast_sum, hf] using this
    have h5 : Real.exp (-(r / 4 * (KLmaxDist d L δ : ℝ))) * Real.exp (-(r * ∑ v, (zdistD d L (a v - δ v) : ℝ))) ≤
        Real.exp (-(r / 4 * (KLmaxDist d L a : ℝ))) * Real.exp (-((r / 2) * ∑ v, (zdistD d L (a v - δ v) : ℝ))) := by
      rw [← Real.exp_add, ← Real.exp_add]
      apply Real.exp_le_exp.2
      nlinarith [mul_nonneg hr.le hz0]
    calc ‖BASigmaPi d L n M t (fun _ => σ₀) ∅ δ‖ * ∏ v, ‖BAThetaOf M t σ₀ σ₀ (a v) (δ v)‖
        ≤ (KPure_CSig d n B r * Real.exp (-(r / 4 * (KLmaxDist d L δ : ℝ)))) *
            ∏ v, (B * Real.exp (-(r * (zdistD d L (a v - δ v) : ℝ)))) :=
          mul_le_mul h1 h2 (Finset.prod_nonneg fun _ _ => norm_nonneg _) (by positivity)
      _ = KPure_CSig d n B r * B ^ n *
            (Real.exp (-(r / 4 * (KLmaxDist d L δ : ℝ))) * Real.exp (-(r * ∑ v, (zdistD d L (a v - δ v) : ℝ)))) := by
          rw [h3]; ring
      _ ≤ KPure_CSig d n B r * B ^ n *
            (Real.exp (-(r / 4 * (KLmaxDist d L a : ℝ))) *
              Real.exp (-((r / 2) * ∑ v, (zdistD d L (a v - δ v) : ℝ)))) :=
          mul_le_mul_of_nonneg_left h5 (by positivity)
      _ = KPure_CSig d n B r * Real.exp (-(r / 4 * (KLmaxDist d L a : ℝ))) * ∏ v, f v (δ v) := by
          rw [h4]; ring
  have hsum : ∑ δ : Fin n → Zd d L, ∏ v, f v (δ v) = ∏ v, ∑ x, f v x := by
    have h := Finset.prod_univ_sum (fun _ : Fin n => (Finset.univ : Finset (Zd d L))) f
    rw [Fintype.piFinset_univ] at h
    exact h.symm
  have hlam2 : 0 < r / 2 := by positivity
  have hfS : ∀ v, ∑ x, f v x ≤ B * expC (d - 2) (r / 2) := fun v => by
    simp only [hf, ← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (BAsum_exp_decay_le d L hd (r / 2) hlam2 (a v)) hB0.le
  have hfS0 : ∀ v, 0 ≤ ∑ x, f v x := fun v => Finset.sum_nonneg fun x _ => by simp only [hf]; positivity
  calc _ ≤ ∑ δ : Fin n → Zd d L, ‖BASigmaPi d L n M t (fun _ => σ₀) ∅ δ * ∏ v, BAThetaOf M t σ₀ σ₀ (a v) (δ v)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ δ : Fin n → Zd d L, KPure_CSig d n B r * Real.exp (-(r / 4 * (KLmaxDist d L a : ℝ))) * ∏ v, f v (δ v) :=
        Finset.sum_le_sum fun δ _ => hpt δ
    _ = KPure_CSig d n B r * Real.exp (-(r / 4 * (KLmaxDist d L a : ℝ))) * ∏ v, ∑ x, f v x := by
        rw [← Finset.mul_sum, hsum]
    _ ≤ KPure_CSig d n B r * Real.exp (-(r / 4 * (KLmaxDist d L a : ℝ))) * (B * expC (d - 2) (r / 2)) ^ n := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        calc ∏ v, ∑ x, f v x ≤ ∏ _v : Fin n, (B * expC (d - 2) (r / 2)) :=
              Finset.prod_le_prod₀ (fun v _ => hfS0 v) fun v _ => hfS v
          _ = (B * expC (d - 2) (r / 2)) ^ n := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    _ = KPure_CSig d n B r * (B * expC (d - 2) (r / 2)) ^ n * Real.exp (-(r / 4 * (KLmaxDist d L a : ℝ))) := by ring

end Pure

/-- **Pure loops** (`lem_pureloop`, `(res_pureKes)`, `A:643-654`): for a constant charge vector `σ = (σ₀, …, σ₀)`,
`|𝒦^{(n)}_{t,σ,a}| ≤ C W^{-d(n-1)} e^{-c max_{i,j} |a_i - a_j|}`, with `C, c > 0` depending on `(d, n, Λ, κ)` only,
uniformly in `L ≥ 3`, `W`, `g ∈ (0, Λ]`, the real-axis data `BAReal d L g κ E m` and `t ∈ [0, 1)`.  `c = r/4`,
`C = C_Σ (B S')^n` (`C_Σ = |TSP n| B^{n+3n²} S₀^{N₀}`, `S' = expC (d-2) (r/2)`); the quantifier order is that of the
pin `BAKBoundAt` (`t/T2360:RBM3D/Probe/T2360Pins.lean:38`), and no hypothesis `1 ≤ W` is needed. -/
theorem baPure_loop {d n : ℕ} [NeZero n] (hd : 3 ≤ d) (hn : 3 ≤ n) {Λ κ : ℝ} (hΛ : 0 < Λ) (hκ : 0 < κ) :
    ∃ C : ℝ, 0 < C ∧ ∃ c : ℝ, 0 < c ∧ ∀ (L : ℕ) (hL : 3 ≤ L) (W : ℕ) (g : ℝ), 0 < g → g ≤ Λ → ∀ (E : ℝ) (m : ℂ),
      haveI : NeZero L := ⟨by omega⟩
      BAReal d L g κ E m → ∀ t : ℝ, 0 ≤ t → t < 1 → ∀ (σ₀ : Bool) (a : Fin n → Zd d L),
        ‖BAKsol d L W (BAMsigma d L (BAMB d L g (E : ℂ) m)) (PropSpin m) t (KLloopOf d L (fun _ => σ₀) a)‖ ≤
          C * (((W : ℝ) ^ d)⁻¹) ^ (n - 1) * Real.exp (-(c * (KLmaxDist d L a : ℝ))) := by
  have hd0 : 0 < d := by omega
  have hB1 := baPureB_one_le d Λ κ
  have hr0 := baPureRate_pos hd0 hΛ hκ
  have hB0 : 0 < baPureB d Λ κ := by linarith
  have hS' : 0 < expC (d - 2) (baPureRate d Λ κ / 2) := by unfold expC; positivity
  have hCpos := KPure_CSig_pos (d := d) (NeZero.pos n) hB1 hr0
  refine ⟨KPure_CSig d n (baPureB d Λ κ) (baPureRate d Λ κ) *
    (baPureB d Λ κ * expC (d - 2) (baPureRate d Λ κ / 2)) ^ n, by positivity, baPureRate d Λ κ / 4, by positivity,
    fun L hL W g hg hgΛ E m => ?_⟩
  have : NeZero L := ⟨by omega⟩
  intro hreal t ht0 ht1 σ₀ a
  obtain ⟨hM, hΘ0, hΘ⟩ := baPure_edge hd hΛ hκ hL hg hgΛ hreal ht0 ht1.le
  rw [baK_pure_eq d hκ hg hL W hreal ⟨ht0, ht1⟩ hn σ₀ a, norm_mul, norm_pow, norm_inv, norm_pow,
    Complex.norm_natCast]
  have h := KPure_K_bound (d := d) (L := L) (by omega) (by omega) (BAMsigma d L (BAMB d L g (E : ℂ) m)) t σ₀ hB1 hr0 hM
    hΘ0 hΘ a
  calc (((W : ℝ) ^ d)⁻¹) ^ (n - 1) * ‖∑ δ : Fin n → Zd d L,
        BASigmaPi d L n (BAMsigma d L (BAMB d L g (E : ℂ) m)) t (fun _ => σ₀) ∅ δ *
          ∏ v, BAThetaOf (BAMsigma d L (BAMB d L g (E : ℂ) m)) t σ₀ σ₀ (a v) (δ v)‖
      ≤ (((W : ℝ) ^ d)⁻¹) ^ (n - 1) * (KPure_CSig d n (baPureB d Λ κ) (baPureRate d Λ κ) *
          (baPureB d Λ κ * expC (d - 2) (baPureRate d Λ κ / 2)) ^ n *
            Real.exp (-(baPureRate d Λ κ / 4 * (KLmaxDist d L a : ℝ)))) :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ = _ := by ring_nf

/-! ## 6. Compiled nonempty instances

Datum: the merged flow point `P` of `(d, L) = (3, 4)` (`BA/MFixedPoint.lean:893`; `P.real : BAReal 3 4 P.g0 P.m0.im P.E P.m0`,
`0 < P.g0 ≤ 10`), `Λ = 10`, `κ = Im m₀ > 0`, `t = 1/2`, `W = 2`, `n = 3, 4`, distinct labels (`δ3`, `δ4`: points
`(k, 0, 0)` of `Z_4^3`), charges `σ` with a short chord.  Every deterministic hypothesis is discharged; no hypothesis is
left open (no pin of another gate enters).  `F = {(0,2)}` (`TSP_four`) is the tree with one chord: two nodes, six slots,
seven edges. -/

namespace KPureInst

open RBM.BA.MFixedPointInst

/-- `M(σ) = BAMsigma (BAMB ..)` at the flow point. -/
private noncomputable abbrev M0 : Bool → Matrix (Zd 3 4) (Zd 3 4) ℂ := BAMsigma 3 4 (BAMB 3 4 P.g0 (P.E : ℂ) P.m0)

private noncomputable abbrev tP : ℝ := 1 / 2

private abbrev δ3 : Fin 3 → Zd 3 4 := ![![0, 0, 0], ![1, 0, 0], ![2, 0, 0]]

private abbrev δ4 : Fin 4 → Zd 3 4 := ![![0, 0, 0], ![1, 0, 0], ![2, 0, 0], ![3, 0, 0]]

/-- The labels are not collapsed: `max_{i,j} |δ_i - δ_j| = 2` for `δ3` and `δ4`. -/
example : KLmaxDist 3 4 δ3 = 2 := by decide

example : KLmaxDist 3 4 δ4 = 2 := by decide

private abbrev F02 : Finset (Fin 4 × Fin 4) := {((0 : Fin 4), (2 : Fin 4))}

private theorem F02_tsp : KLIsTSP F02 := KLisTSP_of_mem_TSP (by rw [TSP_four]; simp)

private theorem rate_pos : 0 < baPureRate 3 10 P.m0.im := baPureRate_pos (by norm_num) (by norm_num) P.real.1.1

/-- `baPure_edge` at the flow point, `t = 1/2`: the three entry bounds. -/
private theorem edge_P :
    (∀ (σ : Bool) (x y : Zd 3 4), ‖M0 σ x y‖ ≤
      baPureB 3 10 P.m0.im * Real.exp (-(baPureRate 3 10 P.m0.im * (zdistD 3 4 (x - y) : ℝ)))) ∧
    (∀ (s : Bool) (x y : Zd 3 4), ‖BAThetaOf M0 tP s s x y‖ ≤
      baPureB 3 10 P.m0.im * Real.exp (-(baPureRate 3 10 P.m0.im * (zdistD 3 4 (x - y) : ℝ)))) ∧
    (∀ (s : Bool) (x y : Zd 3 4), ‖(tP : ℂ) * BAThetaOf M0 tP s s x y‖ ≤
      baPureB 3 10 P.m0.im * Real.exp (-(baPureRate 3 10 P.m0.im * (zdistD 3 4 (x - y) : ℝ)))) :=
  baPure_edge (d := 3) (Λ := 10) (κ := P.m0.im) (L := 4) (g := P.g0) (E := P.E) (m := P.m0) (by norm_num)
    (by norm_num) P.real.1.1 (by norm_num) P.g0_pos P.g0_le P.real (t := tP) (by norm_num) (by norm_num)

/-- **`baPure_edge`** at the flow point: the entry `(0, (1,0,0))` of `M(+)`, of `Θ^{(-,-)}` and of the chord `tΘ^{(+,+)}`
is at most `B e^{-r |x-y|}`, `B ≥ 1`, `r > 0`. -/
example : ‖M0 true 0 ![1, 0, 0]‖ ≤ baPureB 3 10 P.m0.im *
    Real.exp (-(baPureRate 3 10 P.m0.im * (zdistD 3 4 ((0 : Zd 3 4) - ![1, 0, 0]) : ℝ))) :=
  edge_P.1 true 0 ![1, 0, 0]

example : ‖BAThetaOf M0 tP false false 0 ![1, 0, 0]‖ ≤ baPureB 3 10 P.m0.im *
    Real.exp (-(baPureRate 3 10 P.m0.im * (zdistD 3 4 ((0 : Zd 3 4) - ![1, 0, 0]) : ℝ))) :=
  edge_P.2.1 false 0 ![1, 0, 0]

example : ‖(tP : ℂ) * BAThetaOf M0 tP true true 0 ![1, 0, 0]‖ ≤ baPureB 3 10 P.m0.im *
    Real.exp (-(baPureRate 3 10 P.m0.im * (zdistD 3 4 ((0 : Zd 3 4) - ![1, 0, 0]) : ℝ))) :=
  edge_P.2.2 true 0 ![1, 0, 0]

example : 1 ≤ baPureB 3 10 P.m0.im ∧ 0 < baPureRate 3 10 P.m0.im := ⟨baPureB_one_le 3 10 P.m0.im, rate_pos⟩

/-- **`baSlot_path_le`** for `F = {(0,2)}`, `n = 4` (six slots), the labelling `β s = (start s, 0, 0)` and the slots of the
leaves `0` and `2` (in different nodes): `|β s - β t| ≤ T(β)`. -/
example := baSlot_path_le (d := 3) (L := 4) F02_tsp (by norm_num)
  (fun s : BAslot F02 => (![((BAslotStart F02 s).val : ZMod 4), 0, 0] : Zd 3 4)) (BAslotLeaf F02 0) (BAslotLeaf F02 2)

/-- `baSlot_path_le` for the star `F = ∅`, `n = 3`: the three `M`-edges form one cycle. -/
example := baSlot_path_le (d := 3) (L := 4) (F := (∅ : Finset (Fin 3 × Fin 3)))
  (KLisTSP_of_mem_TSP (empty_mem_TSP 3)) (by norm_num) (fun s => δ3 (BAslotStart _ s)) (BAslotLeaf _ 0) (BAslotLeaf _ 2)

/-- **`baSigmaTree_bound`** (core) for the tree `F = {(0,2)}` with the charges `σ = (+,-,+,+)` (the chord is short,
`σ_0 = σ_2`), `δ = δ4`, the pair `(0, 2)`; the product hypothesis `hprod` is discharged from the entry bounds. -/
example :=
  baSigmaTree_bound (d := 3) (L := 4) (n := 4) (F := F02) (by norm_num) F02_tsp (by norm_num) M0 tP
    ![true, false, true, true] δ4 rate_pos (pow_nonneg (by linarith [baPureB_one_le 3 10 P.m0.im]) _)
    (fun β _ => KPure_hprod_of_entries M0 tP _ (baPureB_one_le 3 10 P.m0.im)
      (KPure_edge_entries M0 tP _ (by decide) edge_P.1 edge_P.2.2) β) 0 2

/-- The edge count of the cactus of `F = {(0,2)}`: `1` chord and `6` `M`-edges, `n + 3|F| = 7`. -/
example : Fintype.card (↥F02 ⊕ BAslot F02) = 7 := by
  rw [Fintype.card_sum, Fintype.card_coe, BAslot_card]
  rfl

/-- **`baSigmaTree_bound_of_entries`** for `F = {(0,2)}`, the pure charges `σ = (+,+,+,+)`, `δ = δ4`, the pair `(1, 3)`. -/
example :=
  baSigmaTree_bound_of_entries (d := 3) (L := 4) (n := 4) (F := F02) (by norm_num) F02_tsp (by norm_num) M0 tP
    ![true, true, true, true] δ4 (baPureB_one_le 3 10 P.m0.im) rate_pos
    (KPure_edge_entries M0 tP _ (by decide) edge_P.1 edge_P.2.2) 1 3

/-- **`baSigmaTree_bound_of_entries`** for the star `F = ∅`, `n = 3`, `σ = (+,+,+)`. -/
example :=
  baSigmaTree_bound_of_entries (d := 3) (L := 4) (n := 3) (F := (∅ : Finset (Fin 3 × Fin 3))) (by norm_num)
    (KLisTSP_of_mem_TSP (empty_mem_TSP 3)) (by norm_num) M0 tP ![true, true, true] δ3
    (baPureB_one_le 3 10 P.m0.im) rate_pos
    (KPure_edge_entries M0 tP _ (by decide) edge_P.1 edge_P.2.2) 0 2

/-- **`baSigmaTree_bound_maxDist`** for the tree `F = {(0,2)}` with `σ = (+,-,+,+)` and `δ = δ4`: `e^{-(r/4) max |δ_i - δ_j|}`. -/
example :=
  baSigmaTree_bound_maxDist (d := 3) (L := 4) (n := 4) (F := F02) (by norm_num) F02_tsp (by norm_num) M0 tP
    ![true, false, true, true] δ4 (baPureB_one_le 3 10 P.m0.im) rate_pos
    (KPure_edge_entries M0 tP _ (by decide) edge_P.1 edge_P.2.2)

/-- **`baSigmaPi_empty_bound`** at `n = 3`, `σ = (+,+,+)` and at `n = 4`, `σ = (+,-,+,-)` (alternating): the molecule
`Σ^{(∅)}` at the flow point decays in `max_{i,j} |δ_i - δ_j|`. -/
example :=
  baSigmaPi_empty_bound (d := 3) (L := 4) (n := 3) (by norm_num) (by norm_num) M0 tP ![true, true, true]
    (baPureB_one_le 3 10 P.m0.im) rate_pos edge_P.1 edge_P.2.2 δ3

example :=
  baSigmaPi_empty_bound (d := 3) (L := 4) (n := 4) (by norm_num) (by norm_num) M0 tP ![true, false, true, false]
    (baPureB_one_le 3 10 P.m0.im) rate_pos edge_P.1 edge_P.2.2 δ4

/-- **`baSig_decay`** at `ι = Unit`, `n = 3` and `n = 4`: `SigDecayAbs d n L (BASig ..)` at the flow point. -/
example : SigDecayAbs 3 3 (fun _ : Unit => 4)
    (BASig 3 3 (fun _ : Unit => 4) (fun _ => P.g0) (fun _ => P.E) (fun _ => P.m0) (fun _ => tP)) :=
  baSig_decay (ι := Unit) (d := 3) (n := 3) (Λ := 10) (κ := P.m0.im) (by norm_num) (by norm_num) (by norm_num)
    P.real.1.1 (fun _ => 4) (fun _ => P.g0) (fun _ => P.E) (fun _ => P.m0) (fun _ => tP) (fun _ => by norm_num)
    (fun _ => P.g0_pos) (fun _ => P.g0_le) (fun _ => P.real) (fun _ => by norm_num) (fun _ => by norm_num)

/-- `baSig_decay` at `n = 4`, applied: for the alternating `σ = (+,-,+,-)` and the labels `δ4` the molecule weight is at
most `C e^{-c max_{i,j} |δ_i - δ_j|}` with `C, c > 0`. -/
example : ∃ C : ℝ, 0 < C ∧ ∃ c : ℝ, 0 < c ∧
    ‖BASig 3 4 (fun _ : Unit => 4) (fun _ => P.g0) (fun _ => P.E) (fun _ => P.m0) (fun _ => tP) ()
      ![true, false, true, false] δ4‖ ≤ C * Real.exp (-(c * (KLmaxDist 3 4 δ4 : ℝ))) :=
  let ⟨C, hC, c, hc, H⟩ := baSig_decay (ι := Unit) (d := 3) (n := 4) (Λ := 10) (κ := P.m0.im) (by norm_num)
    (by norm_num) (by norm_num) P.real.1.1 (fun _ => 4) (fun _ => P.g0) (fun _ => P.E) (fun _ => P.m0)
    (fun _ => tP) (fun _ => by norm_num) (fun _ => P.g0_pos) (fun _ => P.g0_le) (fun _ => P.real)
    (fun _ => by norm_num) (fun _ => by norm_num)
  ⟨C, hC, c, hc, H () _ _⟩

/-- **`baK_pure_eq`** at the flow point, `W = 2`, `σ₀ = +`: `n = 3` and `n = 4`. -/
example :=
  baK_pure_eq 3 P.real.1.1 P.g0_pos (L := 4) (by norm_num) 2 P.real (t := tP) ⟨by norm_num, by norm_num⟩ (n := 3)
    (by norm_num) true δ3

example :=
  baK_pure_eq 3 P.real.1.1 P.g0_pos (L := 4) (by norm_num) 2 P.real (t := tP) ⟨by norm_num, by norm_num⟩ (n := 4)
    (by norm_num) true δ4

/-- **`baPure_loop`** at the flow point, `W = 2`, `σ₀ = +`, labels `δ3` (`n = 3`) and `δ4` (`n = 4`): the pure loop
`𝒦^{(n)}` is at most `C W^{-d(n-1)} e^{-c max_{i,j} |a_i - a_j|}`. -/
example : ∃ C : ℝ, 0 < C ∧ ∃ c : ℝ, 0 < c ∧
    ‖BAKsol 3 4 2 M0 (PropSpin P.m0) tP (KLloopOf 3 4 (fun _ : Fin 3 => true) δ3)‖ ≤
      C * ((((2 : ℕ) : ℝ) ^ 3)⁻¹) ^ (3 - 1) * Real.exp (-(c * (KLmaxDist 3 4 δ3 : ℝ))) :=
  let ⟨C, hC, c, hc, H⟩ := baPure_loop (d := 3) (n := 3) (Λ := 10) (κ := P.m0.im) (by norm_num) (by norm_num)
    (by norm_num) P.real.1.1
  ⟨C, hC, c, hc, H 4 (by norm_num) 2 P.g0 P.g0_pos P.g0_le P.E P.m0 P.real tP (by norm_num) (by norm_num) true δ3⟩

example : ∃ C : ℝ, 0 < C ∧ ∃ c : ℝ, 0 < c ∧
    ‖BAKsol 3 4 2 M0 (PropSpin P.m0) tP (KLloopOf 3 4 (fun _ : Fin 4 => true) δ4)‖ ≤
      C * ((((2 : ℕ) : ℝ) ^ 3)⁻¹) ^ (4 - 1) * Real.exp (-(c * (KLmaxDist 3 4 δ4 : ℝ))) :=
  let ⟨C, hC, c, hc, H⟩ := baPure_loop (d := 3) (n := 4) (Λ := 10) (κ := P.m0.im) (by norm_num) (by norm_num)
    (by norm_num) P.real.1.1
  ⟨C, hC, c, hc, H 4 (by norm_num) 2 P.g0 P.g0_pos P.g0_le P.E P.m0 P.real tP (by norm_num) (by norm_num) true δ4⟩

/-- **The K09b interface**: `baSig_decay` is the molecule-decay hypothesis `hD` of `indStepAbs_of`
(`Loop/KLIndStepB.lean:879`) at `Sig = BASig`, `ι = Unit`; the leaf bundle `hTH` (K12) and the sum-zero interface `hS` (K08)
are other gates' pins and stay hypotheses of the example. -/
example (TH : ∀ _ : Unit, Bool → Bool → Matrix (Zd 3 4) (Zd 3 4) ℂ)
    (hTH : IndStepTH 3 (fun _ : Unit => 4) (fun _ => P.g0) (fun _ => tP) TH)
    (hS : SigSumZeroAbs 3 4 (fun _ : Unit => 4) (fun _ => P.g0) (fun _ => tP)
      (BASig 3 4 (fun _ : Unit => 4) (fun _ => P.g0) (fun _ => P.E) (fun _ => P.m0) (fun _ => tP))) :
    IndStepAbs 3 4 (fun _ : Unit => 4) (fun _ => Bparam 3 4 P.g0 tP 0)
      (BASig 3 4 (fun _ : Unit => 4) (fun _ => P.g0) (fun _ => P.E) (fun _ => P.m0) (fun _ => tP)) TH :=
  indStepAbs_of 3 4 10 (fun _ : Unit => 4) (fun _ => P.g0) (fun _ => tP)
    (BASig 3 4 (fun _ : Unit => 4) (fun _ => P.g0) (fun _ => P.E) (fun _ => P.m0) (fun _ => tP)) TH
    (by norm_num) (by norm_num) (fun _ => ⟨by norm_num, P.g0_pos, P.g0_le, by norm_num, by norm_num⟩) hTH
    (baSig_decay (ι := Unit) (d := 3) (n := 4) (Λ := 10) (κ := P.m0.im) (by norm_num) (by norm_num) (by norm_num)
      P.real.1.1 (fun _ => 4) (fun _ => P.g0) (fun _ => P.E) (fun _ => P.m0) (fun _ => tP) (fun _ => by norm_num)
      (fun _ => P.g0_pos) (fun _ => P.g0_le) (fun _ => P.real) (fun _ => by norm_num) (fun _ => by norm_num))
    hS

end KPureInst

end RBM.BA
