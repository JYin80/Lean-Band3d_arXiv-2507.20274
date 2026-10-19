/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.BA.GreenMinor2
import RBM3D.Green.FlucIterGain
import RBM3D.Green.MinorDiff

/-!
# The block Anderson minors: graded differences, the averaging identity, the family statements

Paper: Lemma 8.4 (`lem_GbEXP_BA`), the block Anderson version of Lemma 3.1 (`lem_GbEXP`).  Everything
is deterministic, for one sample, except the statements `BAFamGain`, `BAFAav` of section 3.

* The graded bound on protected rows.  For `u = (β, o)`, `y` of offset `o` in another
  block, and distinct rows `κ_1, …, κ_r ∈ R_{β,o}`:
  `‖Δ_{κ_1} ⋯ Δ_{κ_r} Y^X_{uy}‖, ‖Δ_{κ_1} ⋯ Δ_{κ_r} Y^A_u‖ ≤ c_Y(r) (2δ)^{r+1}`
  (`GreenMinor_diff`), with `c_Y(r) = (‖s‖ + 2 d g₀)(1/κ + 1) a_r + (4 d g₀/κ) 2^r a_r²`,
  `a_0 = 2/κ`, `a_{r+1} = 16^r a_r⁵`.  It is the analogue of `Green.diffBd_atom`
  (`MinorDiff.lean`) for the centred entries of the protected levels; the sum rule
  (`GreenMinor_DiffBd_add`, `GreenMinor_DiffBd_smul`, `GreenMinor_DiffBd_sum`) is specific to this file.  The hypothesis `κ ≤ 1` is needed
  because `a_0 = 2/κ ≥ 1` (at block Anderson `κ ≤ ‖m‖ ≤ 1`, `BAm_norm_le_one`, `BA/Ward.lean`).
* The exact averaging identity `v̄_a - t Σ_b M^{(B)}_{ab} M^{(B)}_{ba} v̄_b = ⟨M𝒦⟩_a` and its
  split into the offset averages of `Δ`, `𝒜' = A + t v̄` and `𝔛` (`GreenMinor_avgK`,
  `GreenMinor_avg_split`).
* The statements: the gain interface `GreenMinor_famGain`, the carrier families
  `GreenMinor_famA`, `GreenMinor_famX`, and the statements `BAFamGain`, `BAFAav` (proved in `BA/GreenCond2.lean`).
-/

set_option linter.style.longLine false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.setOption false
set_option linter.flexible false

noncomputable section
open MeasureTheory Filter Matrix Finset
open scoped Kronecker
open RBM RBM.Green RBM.Gauss RBM.Gauss.Sizes

namespace RBM.BA

/-! ## 1. The exact averaging identity for `⟨M𝒦⟩_a` -/

section Averaging
variable {d L W : ℕ}

/-- `GreenMinor_avg f = W^{-d} Σ_o f(o)`. -/
def GreenMinor_avg {d W : ℕ} (f : Fin (W ^ d) → ℂ) : ℂ := (((W : ℝ) ^ d)⁻¹ : ℝ) * ∑ o, f o

theorem GreenMinor_avg_sub (f g : Fin (W ^ d) → ℂ) :
    GreenMinor_avg (fun o => f o - g o) = GreenMinor_avg f - GreenMinor_avg g := by
  unfold GreenMinor_avg; rw [Finset.sum_sub_distrib]; ring

theorem GreenMinor_avg_mul_left (c : ℂ) (f : Fin (W ^ d) → ℂ) :
    GreenMinor_avg (fun o => c * f o) = c * GreenMinor_avg f := by
  unfold GreenMinor_avg; rw [← Finset.mul_sum]; ring

variable [NeZero L] [NeZero W]

/-- `⟨M𝒦⟩_a = W^{-d} Σ_o Σ_{b'} M^{(B)}_{ab'} 𝒦_{(b',o),(a,o)}` (`GreenCore_K`). -/
def GreenMinor_avgK {d L W : ℕ} [NeZero L] [NeZero W] (G M X D : Matrix (Vtx d L W) (Vtx d L W) ℂ)
    (Mb : Zd d L → Zd d L → ℂ) (t : ℝ) (m : ℂ) (a : Zd d L) : ℂ :=
  (((W : ℝ) ^ d)⁻¹ : ℝ) * ∑ o : Fin (W ^ d), ∑ b' : Zd d L, Mb a b' * GreenCore_K G M X D t m (b', o) (a, o)

variable {G X D M : Matrix (Vtx d L W) (Vtx d L W) ℂ} {Mb : Zd d L → Zd d L → ℂ} {t : ℝ} {m s z : ℂ}

/-- **The split of `⟨M𝒦⟩_a`** (only `hM`; the sum is over all `b'`, `𝔛_{uu} = 0` is not used):
`⟨M𝒦⟩_a = Σ_{b'} M^{(B)}_{ab'} [t v̄_{b'} avg_o Δ - M^{(B)}_{b'a} avg_o 𝒜' - avg_o (𝒜' Δ) - avg_o 𝔛]`, `𝒜'_u = A_u + t v̄_{[u]}`. -/
theorem GreenMinor_avg_split (hM : ∀ u v, M u v = if u.2 = v.2 then Mb u.1 v.1 else 0) (a : Zd d L) :
    GreenMinor_avgK G M X D Mb t m a =
      ∑ b', Mb a b' * ((t : ℂ) * GreenCore_vbar G M b' * GreenMinor_avg (fun o : Fin (W ^ d) => G (b', o) (a, o) - M (b', o) (a, o))
        - Mb b' a * GreenMinor_avg (fun o : Fin (W ^ d) => GreenCore_Arow G X D t m (b', o) + (t : ℂ) * GreenCore_vbar G M b')
        - GreenMinor_avg (fun o : Fin (W ^ d) => (GreenCore_Arow G X D t m (b', o) + (t : ℂ) * GreenCore_vbar G M b') *
            (G (b', o) (a, o) - M (b', o) (a, o)))
        - GreenMinor_avg (fun o : Fin (W ^ d) => GreenCore_Xrow G X (b', o) (a, o))) := by
  have hM' : ∀ (b' a : Zd d L) (o : Fin (W ^ d)), M (b', o) (a, o) = Mb b' a := fun b' a o => by simp [hM]
  have hK : ∀ b' : Zd d L, GreenMinor_avg (fun o : Fin (W ^ d) => GreenCore_K G M X D t m (b', o) (a, o)) =
      (t : ℂ) * GreenCore_vbar G M b' * GreenMinor_avg (fun o : Fin (W ^ d) => G (b', o) (a, o) - M (b', o) (a, o))
        - Mb b' a * GreenMinor_avg (fun o : Fin (W ^ d) => GreenCore_Arow G X D t m (b', o) + (t : ℂ) * GreenCore_vbar G M b')
        - GreenMinor_avg (fun o : Fin (W ^ d) => (GreenCore_Arow G X D t m (b', o) + (t : ℂ) * GreenCore_vbar G M b') *
            (G (b', o) (a, o) - M (b', o) (a, o)))
        - GreenMinor_avg (fun o : Fin (W ^ d) => GreenCore_Xrow G X (b', o) (a, o)) := by
    intro b'
    have hf : (fun o : Fin (W ^ d) => GreenCore_K G M X D t m (b', o) (a, o)) = fun o =>
        (((t : ℂ) * GreenCore_vbar G M b' * (G (b', o) (a, o) - M (b', o) (a, o))
          - Mb b' a * (GreenCore_Arow G X D t m (b', o) + (t : ℂ) * GreenCore_vbar G M b'))
          - (GreenCore_Arow G X D t m (b', o) + (t : ℂ) * GreenCore_vbar G M b') * (G (b', o) (a, o) - M (b', o) (a, o)))
          - GreenCore_Xrow G X (b', o) (a, o) := by
      funext o
      unfold GreenCore_K
      simp only [hM']
      ring
    rw [hf, GreenMinor_avg_sub, GreenMinor_avg_sub, GreenMinor_avg_sub, GreenMinor_avg_mul_left, GreenMinor_avg_mul_left]
  unfold GreenMinor_avgK
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b' _ => ?_
  rw [← hK b']
  unfold GreenMinor_avg
  rw [← Finset.mul_sum]
  ring

end Averaging

/-! ## 2. The graded bound on protected rows

The calculus of `Green/MinorDiff.lean` (`deltaFam`, `iterDeltaFam`, `DiffBd` with the product rule `DiffBd.mul`, `.delta`, `.shift`,
`.congr`) is generic in the index type.  Here the index type is the type `R_{β,o}` of the protected rows, so that every level
`S : Finset R_{β,o}` is protected and the good event `GreenMinor_good` covers it.  Added: linearity of `iterDeltaFam` and the sum
rule for `DiffBd` (the band calculus has only `.neg`, `.mul`, `.delta`, `.shift`). -/

section Calculus
variable {α : Type*} [DecidableEq α]

theorem GreenMinor_deltaFam_smul (κ : α) (c : ℂ) (Y : Finset α → ℂ) :
    deltaFam κ (fun S => c * Y S) = fun S => c * deltaFam κ Y S := by
  funext S; simp only [deltaFam_apply]; ring

theorem GreenMinor_iterDeltaFam_smul (l : List α) (c : ℂ) (Y : Finset α → ℂ) :
    iterDeltaFam l (fun S => c * Y S) = fun S => c * iterDeltaFam l Y S := by
  induction l generalizing Y with
  | nil => rfl
  | cons κ l ih => rw [iterDeltaFam_cons, GreenMinor_deltaFam_smul, ih, iterDeltaFam_cons]

theorem GreenMinor_deltaFam_zero (κ : α) : deltaFam κ (fun _ : Finset α => (0 : ℂ)) = fun _ => 0 := by
  funext S; simp [deltaFam_apply]

theorem GreenMinor_iterDeltaFam_zero (l : List α) : iterDeltaFam l (fun _ : Finset α => (0 : ℂ)) = fun _ => 0 := by
  induction l with
  | nil => rfl
  | cons κ l ih => rw [iterDeltaFam_cons, GreenMinor_deltaFam_zero, ih]

theorem GreenMinor_DiffBd_zero {Ψ : ℝ} {I : Finset α} {M n : ℕ} {c : ℝ} {p : ℕ} (hc : 0 ≤ c) (hΨ : 0 ≤ Ψ) :
    DiffBd Ψ I M n c p (fun _ : Finset α => (0 : ℂ)) := by
  intro l S _ _ _ _
  rw [GreenMinor_iterDeltaFam_zero, norm_zero]
  positivity

theorem GreenMinor_DiffBd_add {Ψ : ℝ} {I : Finset α} {M n : ℕ} {c₁ c₂ : ℝ} {p : ℕ} {Y Z : Finset α → ℂ}
    (hY : DiffBd Ψ I M n c₁ p Y) (hZ : DiffBd Ψ I M n c₂ p Z) :
    DiffBd Ψ I M n (c₁ + c₂) p (fun S => Y S + Z S) := by
  intro l S hnd hav hlen hcard
  rw [iterDeltaFam_add]
  refine (norm_add_le _ _).trans ?_
  have h1 := hY l S hnd hav hlen hcard
  have h2 := hZ l S hnd hav hlen hcard
  rw [add_mul]
  exact add_le_add h1 h2

theorem GreenMinor_DiffBd_smul {Ψ : ℝ} {I : Finset α} {M n : ℕ} {c' : ℝ} {p : ℕ} {Y : Finset α → ℂ} (c : ℂ)
    (hY : DiffBd Ψ I M n c' p Y) : DiffBd Ψ I M n (‖c‖ * c') p (fun S => c * Y S) := by
  intro l S hnd hav hlen hcard
  rw [GreenMinor_iterDeltaFam_smul, norm_mul]
  calc ‖c‖ * ‖iterDeltaFam l Y S‖ ≤ ‖c‖ * (c' * Ψ ^ (p + l.length)) :=
        mul_le_mul_of_nonneg_left (hY l S hnd hav hlen hcard) (norm_nonneg _)
    _ = ‖c‖ * c' * Ψ ^ (p + l.length) := by ring

theorem GreenMinor_DiffBd_sum {ι : Type*} {Ψ : ℝ} (hΨ : 0 ≤ Ψ) {I : Finset α} {M n : ℕ} {p : ℕ} (s : Finset ι) (c : ι → ℝ)
    (Y : ι → Finset α → ℂ) (h : ∀ i ∈ s, DiffBd Ψ I M n (c i) p (Y i)) :
    DiffBd Ψ I M n (∑ i ∈ s, c i) p (fun S => ∑ i ∈ s, Y i S) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using GreenMinor_DiffBd_zero (I := I) (M := M) (n := n) (p := p) le_rfl hΨ
  | insert j s hj ih =>
      simp only [Finset.sum_insert hj]
      exact GreenMinor_DiffBd_add (h j (Finset.mem_insert_self j s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

end Calculus

section Constants

/-- `a_0 = 2/κ`, `a_{r+1} = 16^r a_r^5` (`a_0 = 2/κ` replaces the band's `2` in `atomC`, `MinorDiff.lean`). -/
def GreenMinor_a (κ : ℝ) : ℕ → ℝ
  | 0 => 2 / κ
  | r + 1 => 16 ^ r * GreenMinor_a κ r ^ 5

/-- `c_Y(r) = (‖s‖ + 2 d g₀)(1/κ + 1) a_r + (4 d g₀/κ) 2^r a_r²`. -/
def GreenMinor_cY (d : ℕ) (κ g₀ s : ℝ) (r : ℕ) : ℝ :=
  (s + 2 * d * g₀) * (1 / κ + 1) * GreenMinor_a κ r + (4 * d * g₀ / κ) * 2 ^ r * GreenMinor_a κ r ^ 2

variable {κ : ℝ}

@[simp] theorem GreenMinor_a_zero : GreenMinor_a κ 0 = 2 / κ := rfl

@[simp] theorem GreenMinor_a_succ (r : ℕ) : GreenMinor_a κ (r + 1) = 16 ^ r * GreenMinor_a κ r ^ 5 := rfl

/-- For `0 < κ ≤ 1`: `a_r ≥ 2/κ ≥ 2`. -/
theorem GreenMinor_two_div_le_a (hκ : 0 < κ) (hκ1 : κ ≤ 1) : ∀ r : ℕ, 2 / κ ≤ GreenMinor_a κ r
  | 0 => le_rfl
  | r + 1 => by
      have h := GreenMinor_two_div_le_a hκ hκ1 r
      have h2 : (2 : ℝ) ≤ 2 / κ := by rw [le_div_iff₀ hκ]; linarith
      have h1 : (1 : ℝ) ≤ GreenMinor_a κ r := by linarith
      have h5 : GreenMinor_a κ r ≤ GreenMinor_a κ r ^ 5 := by
        calc GreenMinor_a κ r = GreenMinor_a κ r ^ 1 := (pow_one _).symm
          _ ≤ GreenMinor_a κ r ^ 5 := pow_le_pow_right₀ h1 (by norm_num)
      have h16 : (1 : ℝ) ≤ 16 ^ r := one_le_pow₀ (by norm_num)
      rw [GreenMinor_a_succ]
      nlinarith

theorem GreenMinor_one_le_a (hκ : 0 < κ) (hκ1 : κ ≤ 1) (r : ℕ) : (1 : ℝ) ≤ GreenMinor_a κ r := by
  have h := GreenMinor_two_div_le_a hκ hκ1 r
  have h2 : (2 : ℝ) ≤ 2 / κ := by rw [le_div_iff₀ hκ]; linarith
  linarith

theorem GreenMinor_a_nonneg (hκ : 0 < κ) (hκ1 : κ ≤ 1) (r : ℕ) : 0 ≤ GreenMinor_a κ r :=
  le_trans zero_le_one (GreenMinor_one_le_a hκ hκ1 r)

end Constants

section Atoms
variable {d L W : ℕ} [NeZero L] [NeZero W]
  (Gs : Finset (Vtx d L W) → Matrix (Vtx d L W) (Vtx d L W) ℂ) (M : Matrix (Vtx d L W) (Vtx d L W) ℂ)

/-- The centred entry atom `Δ^{(U)}_{ab} = G^{(U)}_{ab} - M_{ab}`, extended by `0` to the levels that removed `a` or `b`. -/
def GreenMinor_gE (a b : Vtx d L W) (U : Finset (Vtx d L W)) : ℂ :=
  if a ∈ U ∨ b ∈ U then 0 else Gs U a b - M a b

/-- The inverse diagonal atom `(G^{(U)}_{aa})⁻¹`, extended by `0` to the levels that removed `a`. -/
def GreenMinor_gI (a : Vtx d L W) (U : Finset (Vtx d L W)) : ℂ :=
  if a ∈ U then 0 else (Gs U a a)⁻¹

variable {Gs M}

/-- **The minor identity for a centred entry atom**: `Δ_κ Δ^{(·)}_{ab} = G_{aκ} G_{κb} (G_{κκ})⁻¹`, both factors being centred entries
because `M_{aκ} = M_{κb} = 0`; valid at every level, with the zero padding. -/
theorem GreenMinor_gE_delta {G : Matrix (Vtx d L W) (Vtx d L W) ℂ} (hT : GreenMinor_Tower G Gs) {a b κ : Vtx d L W}
    (U : Finset (Vtx d L W)) (hak : a ≠ κ) (hbk : b ≠ κ) (hMa : M a κ = 0) (hMb : M κ b = 0) :
    GreenMinor_gE Gs M a b U - GreenMinor_gE Gs M a b (insert κ U) =
      GreenMinor_gE Gs M a κ U * GreenMinor_gE Gs M κ b U * GreenMinor_gI Gs κ U := by
  by_cases hκU : κ ∈ U
  · rw [Finset.insert_eq_of_mem hκU, sub_self]
    simp [GreenMinor_gE, hκU]
  by_cases haU : a ∈ U
  · have : a ∈ insert κ U := Finset.mem_insert_of_mem haU
    simp [GreenMinor_gE, haU, this]
  by_cases hbU : b ∈ U
  · have : b ∈ insert κ U := Finset.mem_insert_of_mem hbU
    simp [GreenMinor_gE, hbU, this]
  have ha' : a ∉ insert κ U := by simp [hak, haU]
  have hb' : b ∉ insert κ U := by simp [hbk, hbU]
  simp only [GreenMinor_gE, GreenMinor_gI, haU, hbU, hκU, ha', hb', or_self, ite_false, hMa, hMb, sub_zero]
  rw [hT.step U κ hκU a b, greenMinor]
  ring

/-- **The reciprocal rule for the inverse diagonal atom** (the analogue of `Green.deltaFam_gInvFam_apply`): with the diagonal entries
nonzero at the two levels, `Δ_κ (G_{aa})⁻¹ = -(G_{aκ} G_{κa} (G_{κκ})⁻¹ (G_{aa})⁻¹ (G^{(κ)}_{aa})⁻¹)`. -/
theorem GreenMinor_gI_delta {G : Matrix (Vtx d L W) (Vtx d L W) ℂ} (hT : GreenMinor_Tower G Gs) {a κ : Vtx d L W}
    (U : Finset (Vtx d L W)) (hak : a ≠ κ) (hMa : M a κ = 0) (hMb : M κ a = 0)
    (hne1 : a ∉ U → Gs U a a ≠ 0) (hne2 : a ∉ insert κ U → Gs (insert κ U) a a ≠ 0) :
    GreenMinor_gI Gs a U - GreenMinor_gI Gs a (insert κ U) =
      -(GreenMinor_gE Gs M a κ U * GreenMinor_gE Gs M κ a U * GreenMinor_gI Gs κ U * GreenMinor_gI Gs a U *
        GreenMinor_gI Gs a (insert κ U)) := by
  by_cases hκU : κ ∈ U
  · rw [Finset.insert_eq_of_mem hκU, sub_self]
    simp [GreenMinor_gE, hκU]
  by_cases haU : a ∈ U
  · have : a ∈ insert κ U := Finset.mem_insert_of_mem haU
    simp [GreenMinor_gE, GreenMinor_gI, haU, this]
  have ha' : a ∉ insert κ U := by simp [hak, haU]
  have hx := hne1 haU
  have hy := hne2 ha'
  have hstep : Gs (insert κ U) a a = Gs U a a - Gs U a κ * Gs U κ a / Gs U κ κ := by
    rw [hT.step U κ hκU a a, greenMinor]
  simp only [GreenMinor_gE, GreenMinor_gI, haU, hκU, ha', or_self, ite_false, hMa, hMb, sub_zero]
  rw [hstep] at hy ⊢
  field_simp
  ring

end Atoms

section Rows
variable {d L W : ℕ} [NeZero L] [NeZero W]

/-- The index type of the protected rows `R_{β,o}`: every `Finset` of it is a protected level. -/
abbrev GreenMinor_Rows (β : Zd d L) (o : Fin (W ^ d)) : Type := {x : Vtx d L W // x ∈ GreenMinor_R β o}

variable {β : Zd d L} {o : Fin (W ^ d)}

/-- The sites of a set of protected rows (a level of the tower). -/
def GreenMinor_lev (S : Finset (GreenMinor_Rows β o)) : Finset (Vtx d L W) :=
  S.map (Function.Embedding.subtype _)

@[simp] theorem GreenMinor_lev_empty : GreenMinor_lev (∅ : Finset (GreenMinor_Rows β o)) = ∅ := by
  simp [GreenMinor_lev]

theorem GreenMinor_lev_insert (k : GreenMinor_Rows β o) (S : Finset (GreenMinor_Rows β o)) :
    GreenMinor_lev (insert k S) = insert k.1 (GreenMinor_lev S) := by
  simp [GreenMinor_lev, Finset.map_insert]

theorem GreenMinor_lev_card (S : Finset (GreenMinor_Rows β o)) : (GreenMinor_lev S).card = S.card := by
  simp [GreenMinor_lev]

theorem GreenMinor_lev_subset (S : Finset (GreenMinor_Rows β o)) : ↑(GreenMinor_lev S) ⊆ GreenMinor_R β o := by
  intro x hx
  simp only [GreenMinor_lev, Finset.coe_map, Set.mem_image, Finset.mem_coe, Function.Embedding.coe_subtype] at hx
  obtain ⟨y, -, rfl⟩ := hx
  exact y.2

/-- The sites an atom may mention: of offset `o` (never removed), or one of the protected rows `I`. -/
def GreenMinor_Adm (I : Finset (GreenMinor_Rows β o)) (a : Vtx d L W) : Prop := a.2 = o ∨ ∃ k ∈ I, k.1 = a

theorem GreenMinor_Adm.mem_T {I : Finset (GreenMinor_Rows β o)} {a : Vtx d L W} (h : GreenMinor_Adm I a) :
    a ∈ GreenMinor_T β o := by
  rcases h with h | ⟨k, -, rfl⟩
  · exact Or.inl h
  · exact Or.inr k.2.1

theorem GreenMinor_Adm.mono {I I' : Finset (GreenMinor_Rows β o)} (hII : I ⊆ I') {a : Vtx d L W} (h : GreenMinor_Adm I a) :
    GreenMinor_Adm I' a := by
  rcases h with h | ⟨k, hk, rfl⟩
  · exact Or.inl h
  · exact Or.inr ⟨k, hII hk, rfl⟩

theorem GreenMinor_Adm_row (I : Finset (GreenMinor_Rows β o)) (k : GreenMinor_Rows β o) :
    GreenMinor_Adm (insert k I) k.1 := Or.inr ⟨k, Finset.mem_insert_self k I, rfl⟩

theorem GreenMinor_Adm.ne {I : Finset (GreenMinor_Rows β o)} {k : GreenMinor_Rows β o} (hk : k ∉ I) {a : Vtx d L W}
    (h : GreenMinor_Adm I a) : a ≠ k.1 := by
  rcases h with h | ⟨k', hk', rfl⟩
  · intro h'
    exact k.2.2 (h' ▸ h)
  · intro h'
    exact hk (Subtype.ext h' ▸ hk')

theorem GreenMinor_Adm.cross {M : Matrix (Vtx d L W) (Vtx d L W) ℂ} {Mb : Zd d L → Zd d L → ℂ}
    (hM : ∀ u v, M u v = if u.2 = v.2 then Mb u.1 v.1 else 0) {I : Finset (GreenMinor_Rows β o)}
    {k : GreenMinor_Rows β o} (hk : k ∉ I) {a : Vtx d L W} (h : GreenMinor_Adm I a) :
    M a k.1 = 0 ∧ M k.1 a = 0 := by
  have h2 : a.2 ≠ k.1.2 := GreenMinor_offset_ne k.2 h.mem_T (h.ne hk)
  exact ⟨GreenMinor_cross hM h2, GreenMinor_cross hM (Ne.symm h2)⟩

variable (Gs : Finset (Vtx d L W) → Matrix (Vtx d L W) (Vtx d L W) ℂ) (M : Matrix (Vtx d L W) (Vtx d L W) ℂ)

/-- The atom family `S ↦ Δ^{(S ∪ T)}_{ab}` over the protected rows (`T` the base level: the class of atoms is closed under the
shift `Y ↦ Y^{(κ)}`). -/
def GreenMinor_eFam (a b : Vtx d L W) (T : Finset (GreenMinor_Rows β o)) : Finset (GreenMinor_Rows β o) → ℂ :=
  fun S => GreenMinor_gE Gs M a b (GreenMinor_lev (S ∪ T))

/-- The atom family `S ↦ (G^{(S ∪ T)}_{aa})⁻¹`. -/
def GreenMinor_iFam (a : Vtx d L W) (T : Finset (GreenMinor_Rows β o)) : Finset (GreenMinor_Rows β o) → ℂ :=
  fun S => GreenMinor_gI Gs a (GreenMinor_lev (S ∪ T))

variable {Gs M}

theorem GreenMinor_eFam_delta {G : Matrix (Vtx d L W) (Vtx d L W) ℂ} (hT : GreenMinor_Tower G Gs) (k : GreenMinor_Rows β o)
    {a b : Vtx d L W} (T S : Finset (GreenMinor_Rows β o)) (hak : a ≠ k.1) (hbk : b ≠ k.1) (hMa : M a k.1 = 0)
    (hMb : M k.1 b = 0) :
    deltaFam k (GreenMinor_eFam Gs M a b T) S =
      GreenMinor_eFam Gs M a k.1 T S * GreenMinor_eFam Gs M k.1 b T S * GreenMinor_iFam Gs k.1 T S := by
  have h : GreenMinor_lev (insert k S ∪ T) = insert k.1 (GreenMinor_lev (S ∪ T)) := by
    rw [Finset.insert_union, GreenMinor_lev_insert]
  simp only [deltaFam_apply, GreenMinor_eFam, GreenMinor_iFam, h]
  exact GreenMinor_gE_delta hT _ hak hbk hMa hMb

theorem GreenMinor_iFam_delta {G : Matrix (Vtx d L W) (Vtx d L W) ℂ} (hT : GreenMinor_Tower G Gs) (k : GreenMinor_Rows β o)
    {a : Vtx d L W} (T S : Finset (GreenMinor_Rows β o)) (hak : a ≠ k.1) (hMa : M a k.1 = 0) (hMb : M k.1 a = 0)
    (hne1 : a ∉ GreenMinor_lev (S ∪ T) → Gs (GreenMinor_lev (S ∪ T)) a a ≠ 0)
    (hne2 : a ∉ insert k.1 (GreenMinor_lev (S ∪ T)) → Gs (insert k.1 (GreenMinor_lev (S ∪ T))) a a ≠ 0) :
    deltaFam k (GreenMinor_iFam Gs a T) S =
      -(GreenMinor_eFam Gs M a k.1 T S * GreenMinor_eFam Gs M k.1 a T S * GreenMinor_iFam Gs k.1 T S *
        GreenMinor_iFam Gs a T S * GreenMinor_iFam Gs a (insert k T) S) := by
  have h : GreenMinor_lev (insert k S ∪ T) = insert k.1 (GreenMinor_lev (S ∪ T)) := by
    rw [Finset.insert_union, GreenMinor_lev_insert]
  have h' : GreenMinor_lev (S ∪ insert k T) = insert k.1 (GreenMinor_lev (S ∪ T)) := by
    rw [Finset.union_insert, GreenMinor_lev_insert]
  simp only [deltaFam_apply, GreenMinor_eFam, GreenMinor_iFam, h, h']
  exact GreenMinor_gI_delta hT _ hak hMa hMb hne1 hne2

end Rows

section AtomInduction
variable {d L W : ℕ} [NeZero L] [NeZero W] {G M : Matrix (Vtx d L W) (Vtx d L W) ℂ} {Mb : Zd d L → Zd d L → ℂ}
  {Gs : Finset (Vtx d L W) → Matrix (Vtx d L W) (Vtx d L W) ℂ} {κ δ : ℝ} {m₀ : ℕ} {β : Zd d L} {o : Fin (W ^ d)}

theorem GreenMinor_level_card {S T : Finset (GreenMinor_Rows β o)} {B : ℕ} (hS : S.card ≤ B) (hB : B + T.card ≤ m₀) :
    (GreenMinor_lev (S ∪ T)).card ≤ m₀ := by
  rw [GreenMinor_lev_card]
  exact le_trans (Finset.card_union_le S T) (by omega)

/-- The base bound for the centred entry atoms: `‖Δ^{(S ∪ T)}_{ab}‖ ≤ 2δ` (`0` at the levels that removed `a` or `b`). -/
theorem GreenMinor_eFam_le (hδ0 : 0 ≤ δ) (hgood : GreenMinor_good Gs M κ δ m₀ β o) {I T S : Finset (GreenMinor_Rows β o)}
    (hcard : (GreenMinor_lev (S ∪ T)).card ≤ m₀) {a b : Vtx d L W} (ha : GreenMinor_Adm I a) (hb : GreenMinor_Adm I b) :
    ‖GreenMinor_eFam Gs M a b T S‖ ≤ 2 * δ := by
  unfold GreenMinor_eFam GreenMinor_gE
  split_ifs with h
  · rw [norm_zero]; linarith
  · have h' := not_or.1 h
    exact (hgood _ (GreenMinor_lev_subset _) hcard a b ha.mem_T hb.mem_T h'.1 h'.2).1

/-- The diagonal of the good event is nonzero at the protected levels. -/
theorem GreenMinor_diag_ne (hκ : 0 < κ) (hgood : GreenMinor_good Gs M κ δ m₀ β o) {S : Finset (GreenMinor_Rows β o)}
    (hcard : (GreenMinor_lev S).card ≤ m₀) {a : Vtx d L W} (ha : a ∈ GreenMinor_T β o) (h : a ∉ GreenMinor_lev S) :
    Gs (GreenMinor_lev S) a a ≠ 0 := by
  have h1 := (hgood _ (GreenMinor_lev_subset _) hcard a a ha ha h h).2
  intro h0
  rw [h0, norm_zero] at h1
  linarith [show 0 < κ / 2 by positivity]

/-- The base bound for the inverse diagonal atoms: `‖(G^{(S ∪ T)}_{aa})⁻¹‖ ≤ 2/κ`. -/
theorem GreenMinor_iFam_le (hκ : 0 < κ) (hgood : GreenMinor_good Gs M κ δ m₀ β o) {I T S : Finset (GreenMinor_Rows β o)}
    (hcard : (GreenMinor_lev (S ∪ T)).card ≤ m₀) {a : Vtx d L W} (ha : GreenMinor_Adm I a) :
    ‖GreenMinor_iFam Gs a T S‖ ≤ 2 / κ := by
  unfold GreenMinor_iFam GreenMinor_gI
  split_ifs with h
  · rw [norm_zero]; positivity
  · have h1 := (hgood _ (GreenMinor_lev_subset _) hcard a a ha.mem_T ha.mem_T h h).2
    have h0 : 0 < κ / 2 := by positivity
    rw [norm_inv]
    calc ‖Gs (GreenMinor_lev (S ∪ T)) a a‖⁻¹ ≤ (κ / 2)⁻¹ := inv_anti₀ h0 h1
      _ = 2 / κ := by field_simp

/-- **The `r`-fold difference estimate for the two kinds of atom, proved together** (the analogue of `Green.diffBd_atom`):
for `m ≤ r` protected rows `k_1, …, k_m` distinct from each other and from every row the atom mentions
(`I`), with `c = a_r` and `Ψ = 2δ`,
`‖Δ_{k_1} ⋯ Δ_{k_m} Δ^{(·)}_{ab}‖ ≤ c Ψ^{m+1}` and `‖Δ_{k_1} ⋯ Δ_{k_m} (G^{(·)}_{aa})⁻¹‖ ≤ c Ψ^{m}`.
Each difference gains a power of `Ψ`: the minor identity (`GreenMinor_eFam_delta`, three atoms) and the reciprocal rule
(`GreenMinor_iFam_delta`, five atoms), both products of cross-offset entries, combined by `DiffBd.mul`. -/
theorem GreenMinor_diffBd_atom (hM : ∀ u v, M u v = if u.2 = v.2 then Mb u.1 v.1 else 0) (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    (hδ0 : 0 ≤ δ) (h2δ : 2 * δ ≤ 1) (hT : GreenMinor_Tower G Gs) (hgood : GreenMinor_good Gs M κ δ m₀ β o) :
    ∀ (r : ℕ) (I T : Finset (GreenMinor_Rows β o)) (B : ℕ), B + T.card ≤ m₀ →
      (∀ a b : Vtx d L W, GreenMinor_Adm I a → GreenMinor_Adm I b →
        DiffBd (2 * δ) I B r (GreenMinor_a κ r) 1 (GreenMinor_eFam Gs M a b T)) ∧
      (∀ a : Vtx d L W, GreenMinor_Adm I a → DiffBd (2 * δ) I B r (GreenMinor_a κ r) 0 (GreenMinor_iFam Gs a T)) := by
  have hΨ0 : 0 ≤ 2 * δ := by linarith
  intro r
  induction r with
  | zero =>
      intro I T B hB
      refine ⟨fun a b ha hb => diffBd_zero fun S hS => ?_, fun a ha => diffBd_zero fun S hS => ?_⟩
      · have h := GreenMinor_eFam_le hδ0 hgood (GreenMinor_level_card hS hB) ha hb
        have h1 := GreenMinor_one_le_a hκ hκ1 0
        calc ‖GreenMinor_eFam Gs M a b T S‖ ≤ 2 * δ := h
          _ ≤ GreenMinor_a κ 0 * (2 * δ) ^ 1 := by rw [pow_one]; nlinarith
      · have h := GreenMinor_iFam_le hκ hgood (GreenMinor_level_card hS hB) ha
        simpa using h
  | succ r ih =>
      intro I T B hB
      have hc0 : (0 : ℝ) ≤ GreenMinor_a κ r := GreenMinor_a_nonneg hκ hκ1 r
      have hc1 : (1 : ℝ) ≤ GreenMinor_a κ r := GreenMinor_one_le_a hκ hκ1 r
      have hCsucc : (1 : ℝ) ≤ GreenMinor_a κ (r + 1) := GreenMinor_one_le_a hκ hκ1 (r + 1)
      have hCsucc0 : (0 : ℝ) ≤ GreenMinor_a κ (r + 1) := GreenMinor_a_nonneg hκ hκ1 (r + 1)
      constructor
      · intro a b ha hb l S hnd hav hlen hcard
        match l with
        | [] =>
            have h := GreenMinor_eFam_le hδ0 hgood (GreenMinor_level_card (S := S) (by simpa using hcard) hB) ha hb
            simp only [iterDeltaFam_nil, List.length_nil, Nat.add_zero, pow_one]
            nlinarith
        | k :: l' =>
            have hcardl : S.card + l'.length + 1 ≤ B := by
              simp only [List.length_cons] at hcard; omega
            obtain ⟨B', rfl⟩ : ∃ B', B = B' + 1 := ⟨B - 1, by omega⟩
            have hkI : k ∉ I := hav k List.mem_cons_self
            have hnd' : l'.Nodup := (List.nodup_cons.1 hnd).2
            have hkl' : k ∉ l' := (List.nodup_cons.1 hnd).1
            have hav' : ∀ k' ∈ l', k' ∉ insert k I := by
              intro k' hk' hmem
              rcases Finset.mem_insert.1 hmem with h1 | h1
              · exact hkl' (h1 ▸ hk')
              · exact hav k' (List.mem_cons_of_mem _ hk') h1
            have hlen' : l'.length ≤ r := by
              simp only [List.length_cons] at hlen; omega
            obtain ⟨ihoff, ihinv⟩ := ih (insert k I) T B' (by omega)
            have hak := ha.ne hkI
            have hbk := hb.ne hkI
            have hMa := (ha.cross hM hkI).1
            have hMb := (hb.cross hM hkI).2
            have hA := ihoff a k.1 (ha.mono (Finset.subset_insert k I)) (GreenMinor_Adm_row I k)
            have hB2 := ihoff k.1 b (GreenMinor_Adm_row I k) (hb.mono (Finset.subset_insert k I))
            have hC := ihinv k.1 (GreenMinor_Adm_row I k)
            have hAB := DiffBd.mul hΨ0 r hc0 hc0 hA hB2
            have hABC := DiffBd.mul hΨ0 r (by positivity) hc0 hAB hC
            have hle : (2 : ℝ) ^ r * (2 ^ r * (GreenMinor_a κ r * GreenMinor_a κ r) * GreenMinor_a κ r) ≤
                GreenMinor_a κ (r + 1) := by
              have hexp : (2 : ℝ) ^ r * (2 ^ r * (GreenMinor_a κ r * GreenMinor_a κ r) * GreenMinor_a κ r)
                  = (2 ^ r * 2 ^ r) * GreenMinor_a κ r ^ 3 := by ring
              have h4 : (2 : ℝ) ^ r * 2 ^ r = 4 ^ r := by rw [← mul_pow]; norm_num
              have hc3 : GreenMinor_a κ r ^ 3 ≤ GreenMinor_a κ r ^ 5 := pow_le_pow_right₀ hc1 (by norm_num)
              have h416 : (4 : ℝ) ^ r ≤ 16 ^ r := pow_le_pow_left₀ (by norm_num) (by norm_num) r
              rw [hexp, h4, GreenMinor_a_succ]
              exact mul_le_mul h416 hc3 (pow_nonneg hc0 3) (pow_nonneg (by norm_num) r)
            have hkey : DiffBd (2 * δ) (insert k I) B' r (GreenMinor_a κ (r + 1)) 2
                (deltaFam k (GreenMinor_eFam Gs M a b T)) := by
              refine (hABC.mono_c hΨ0 hle).congr fun U hU => ?_
              exact (GreenMinor_eFam_delta hT k T U hak hbk hMa hMb).symm
            have hres := hkey l' S hnd' hav' hlen' (by omega)
            rw [iterDeltaFam_cons]
            have hexp2 : 2 + l'.length = 1 + (k :: l').length := by
              simp only [List.length_cons]; omega
            rwa [hexp2] at hres
      · intro a ha l S hnd hav hlen hcard
        match l with
        | [] =>
            have h := GreenMinor_iFam_le hκ hgood (GreenMinor_level_card (S := S) (by simpa using hcard) hB) ha
            simp only [iterDeltaFam_nil, List.length_nil, Nat.add_zero, pow_zero, mul_one]
            exact le_trans h (GreenMinor_two_div_le_a hκ hκ1 (r + 1))
        | k :: l' =>
            have hcardl : S.card + l'.length + 1 ≤ B := by
              simp only [List.length_cons] at hcard; omega
            obtain ⟨B', rfl⟩ : ∃ B', B = B' + 1 := ⟨B - 1, by omega⟩
            have hkI : k ∉ I := hav k List.mem_cons_self
            have hnd' : l'.Nodup := (List.nodup_cons.1 hnd).2
            have hkl' : k ∉ l' := (List.nodup_cons.1 hnd).1
            have hav' : ∀ k' ∈ l', k' ∉ insert k I := by
              intro k' hk' hmem
              rcases Finset.mem_insert.1 hmem with h1 | h1
              · exact hkl' (h1 ▸ hk')
              · exact hav k' (List.mem_cons_of_mem _ hk') h1
            have hlen' : l'.length ≤ r := by
              simp only [List.length_cons] at hlen; omega
            obtain ⟨ihoff, ihinv⟩ := ih (insert k I) T B' (by omega)
            have hTk : B' + (insert k T).card ≤ m₀ :=
              le_trans (by have := Finset.card_insert_le k T; omega) hB
            obtain ⟨_, ihinv'⟩ := ih (insert k I) (insert k T) B' hTk
            have hak := ha.ne hkI
            have hMa := (ha.cross hM hkI).1
            have hMb := (ha.cross hM hkI).2
            have hA := ihoff a k.1 (ha.mono (Finset.subset_insert k I)) (GreenMinor_Adm_row I k)
            have hB2 := ihoff k.1 a (GreenMinor_Adm_row I k) (ha.mono (Finset.subset_insert k I))
            have hC := ihinv k.1 (GreenMinor_Adm_row I k)
            have hD := ihinv a (ha.mono (Finset.subset_insert k I))
            have hE := ihinv' a (ha.mono (Finset.subset_insert k I))
            have h1 := DiffBd.mul hΨ0 r hc0 hc0 hA hB2
            have h2 := DiffBd.mul hΨ0 r (by positivity) hc0 h1 hC
            have h3 := DiffBd.mul hΨ0 r (by positivity) hc0 h2 hD
            have h4 := DiffBd.mul hΨ0 r (by positivity) hc0 h3 hE
            have hle : (2 : ℝ) ^ r * (2 ^ r * (2 ^ r * (2 ^ r * (GreenMinor_a κ r * GreenMinor_a κ r) * GreenMinor_a κ r)
                * GreenMinor_a κ r) * GreenMinor_a κ r) ≤ GreenMinor_a κ (r + 1) := by
              have hexp : (2 : ℝ) ^ r * (2 ^ r * (2 ^ r * (2 ^ r * (GreenMinor_a κ r * GreenMinor_a κ r) * GreenMinor_a κ r)
                  * GreenMinor_a κ r) * GreenMinor_a κ r) = (2 ^ r * 2 ^ r * 2 ^ r * 2 ^ r) * GreenMinor_a κ r ^ 5 := by ring
              have h16 : (2 : ℝ) ^ r * 2 ^ r * 2 ^ r * 2 ^ r = 16 ^ r := by
                rw [← mul_pow, ← mul_pow, ← mul_pow]; norm_num
              rw [hexp, h16, GreenMinor_a_succ]
            have hkey : DiffBd (2 * δ) (insert k I) B' r (GreenMinor_a κ (r + 1)) 1
                (deltaFam k (GreenMinor_iFam Gs a T)) := by
              refine (((h4.mono_c hΨ0 hle).neg).mono_p hΨ0 h2δ hCsucc0 (by norm_num)).congr fun U hU => ?_
              have hne1 : a ∉ GreenMinor_lev (U ∪ T) → Gs (GreenMinor_lev (U ∪ T)) a a ≠ 0 := fun h =>
                GreenMinor_diag_ne hκ hgood (by rw [GreenMinor_lev_card]; exact le_trans (Finset.card_union_le U T) (by omega))
                  ha.mem_T h
              have hne2 : a ∉ insert k.1 (GreenMinor_lev (U ∪ T)) → Gs (insert k.1 (GreenMinor_lev (U ∪ T))) a a ≠ 0 := by
                intro h
                rw [← GreenMinor_lev_insert] at h ⊢
                refine GreenMinor_diag_ne hκ hgood ?_ ha.mem_T h
                rw [GreenMinor_lev_card]
                exact le_trans (Finset.card_insert_le k (U ∪ T)) (by have := Finset.card_union_le U T; omega)
              rw [GreenMinor_iFam_delta hT k T U hak hMa hMb hne1 hne2]
            have hres := hkey l' S hnd' hav' hlen' (by omega)
            rw [iterDeltaFam_cons]
            have hexp2 : 1 + l'.length = 0 + (k :: l').length := by
              simp only [List.length_cons]; omega
            rwa [hexp2] at hres

end AtomInduction

section Models
variable {α : Type*} [DecidableEq α]

/-- The polynomial `Y^X_{uy}` in the centred entries (as a family): the linear terms and the quadratic terms, bounded by
`GreenMinor_DiffBd_add`, `GreenMinor_DiffBd_smul`, `DiffBd.mul` (orders `1` and `1 + 1`, lowered by `Ψ ≤ 1`).  `Euu, Euy` are the entries `Δ_{uu}, Δ_{uy}`,
`Sq = Σ_l D_{ul} Δ_{lu}`, `Sp = Σ_l D_{ul} Δ_{ly}` with `‖D_{u·}‖_1 = K`. -/
theorem GreenMinor_DiffBd_modelX {Ψ : ℝ} (hΨ0 : 0 ≤ Ψ) (hΨ1 : Ψ ≤ 1) {I : Finset α} {M : ℕ} (r : ℕ) {a K κ : ℝ} {s m Muy : ℂ}
    (hκ : 0 < κ) (hm : κ ≤ ‖m‖) (hMuy : ‖Muy‖ ≤ 1) (ha : 0 ≤ a) (hK : 0 ≤ K) {Euu Euy Sq Sp : Finset α → ℂ}
    (h1 : DiffBd Ψ I M r a 1 Euu) (h2 : DiffBd Ψ I M r a 1 Euy) (h3 : DiffBd Ψ I M r (K * a) 1 Sq)
    (h4 : DiffBd Ψ I M r (K * a) 1 Sp) :
    DiffBd Ψ I M r ((‖s‖ + K) * (1 / κ + 1) * a + (2 * K / κ) * 2 ^ r * a ^ 2) 1
      (fun S => ((Muy / m) * (s * Euu S + (-1 : ℂ) * Sq S) + (Sp S + (-s) * Euy S)) +
        ((1 / m) * (Euu S * Sp S) + (-(1 / m)) * (Euy S * Sq S))) := by
  have hm0 : 0 < ‖m‖ := lt_of_lt_of_le hκ hm
  have hinv : ‖(1 : ℂ) / m‖ ≤ 1 / κ := by
    rw [norm_div, norm_one]; exact one_div_le_one_div_of_le hκ hm
  have hMinv : ‖Muy / m‖ ≤ 1 / κ := by
    rw [norm_div]
    calc ‖Muy‖ / ‖m‖ ≤ 1 / ‖m‖ := div_le_div_of_nonneg_right hMuy hm0.le
      _ ≤ 1 / κ := one_div_le_one_div_of_le hκ hm
  have hKa : 0 ≤ K * a := mul_nonneg hK ha
  have hT1 := GreenMinor_DiffBd_smul (Muy / m)
    (GreenMinor_DiffBd_add (GreenMinor_DiffBd_smul s h1) (GreenMinor_DiffBd_smul (-1 : ℂ) h3))
  have hT2 := GreenMinor_DiffBd_add h4 (GreenMinor_DiffBd_smul (-s) h2)
  have hT3a := DiffBd.mul hΨ0 r ha hKa h1 h4
  have hT3b := DiffBd.mul hΨ0 r ha hKa h2 h3
  have hT3 := GreenMinor_DiffBd_add (GreenMinor_DiffBd_smul (1 / m) hT3a) (GreenMinor_DiffBd_smul (-(1 / m)) hT3b)
  have hT3' := hT3.mono_p hΨ0 hΨ1 (by positivity) (by norm_num : 1 ≤ 1 + 1)
  have hall := GreenMinor_DiffBd_add (GreenMinor_DiffBd_add hT1 hT2) hT3'
  refine hall.mono_c hΨ0 ?_
  simp only [norm_neg, norm_one]
  have e1 : ‖Muy / m‖ * (‖s‖ * a + 1 * (K * a)) ≤ 1 / κ * (‖s‖ * a + K * a) := by
    rw [one_mul]; gcongr
  have e3 : ‖(1 : ℂ) / m‖ * (2 ^ r * (a * (K * a))) + ‖(1 : ℂ) / m‖ * (2 ^ r * (a * (K * a))) ≤
      2 / κ * (2 ^ r * (a * (K * a))) := by
    have : ‖(1 : ℂ) / m‖ + ‖(1 : ℂ) / m‖ ≤ 2 / κ := by
      have := add_le_add hinv hinv
      calc ‖(1 : ℂ) / m‖ + ‖(1 : ℂ) / m‖ ≤ 1 / κ + 1 / κ := this
        _ = 2 / κ := by ring
    nlinarith [show 0 ≤ (2 : ℝ) ^ r * (a * (K * a)) by positivity]
  calc ‖Muy / m‖ * (‖s‖ * a + 1 * (K * a)) + (K * a + ‖s‖ * a) + (‖(1 : ℂ) / m‖ * (2 ^ r * (a * (K * a))) + ‖(1 : ℂ) / m‖ * (2 ^ r * (a * (K * a))))
      ≤ 1 / κ * (‖s‖ * a + K * a) + (K * a + ‖s‖ * a) + 2 / κ * (2 ^ r * (a * (K * a))) := by linarith
    _ = (‖s‖ + K) * (1 / κ + 1) * a + (2 * K / κ) * 2 ^ r * a ^ 2 := by ring

/-- The polynomial `Y^A_u` in the centred entries (as a family), with the constant of `Y^X` (which is larger). -/
theorem GreenMinor_DiffBd_modelA {Ψ : ℝ} (hΨ0 : 0 ≤ Ψ) {I : Finset α} {M : ℕ} (r : ℕ) {a K κ : ℝ} {s m : ℂ}
    (hκ : 0 < κ) (hm : κ ≤ ‖m‖) (ha : 0 ≤ a) (hK : 0 ≤ K) {Euu Sq : Finset α → ℂ}
    (h1 : DiffBd Ψ I M r a 1 Euu) (h3 : DiffBd Ψ I M r (K * a) 1 Sq) :
    DiffBd Ψ I M r ((‖s‖ + K) * (1 / κ + 1) * a + (2 * K / κ) * 2 ^ r * a ^ 2) 1
      (fun S => (1 / m) * (s * Euu S + (-1 : ℂ) * Sq S)) := by
  have hm0 : 0 < ‖m‖ := lt_of_lt_of_le hκ hm
  have hinv : ‖(1 : ℂ) / m‖ ≤ 1 / κ := by
    rw [norm_div, norm_one]; exact one_div_le_one_div_of_le hκ hm
  have hT1 := GreenMinor_DiffBd_smul (1 / m)
    (GreenMinor_DiffBd_add (GreenMinor_DiffBd_smul s h1) (GreenMinor_DiffBd_smul (-1 : ℂ) h3))
  refine hT1.mono_c hΨ0 ?_
  simp only [norm_neg, norm_one]
  have e1 : ‖(1 : ℂ) / m‖ * (‖s‖ * a + 1 * (K * a)) ≤ 1 / κ * (‖s‖ * a + K * a) := by
    rw [one_mul]; gcongr
  have e2 : 0 ≤ (2 * K / κ) * 2 ^ r * a ^ 2 := by positivity
  nlinarith [show 0 ≤ (‖s‖ + K) * a by positivity]

end Models

section Diff
variable {d L W : ℕ} [NeZero L] [NeZero W]

/-- Levels of protected rows: `Δ_{k_1} ⋯ Δ_{k_m}` along rows `k_i ∈ R_{β,o}` of a family `Y` of `Finset V`, read on `lev S`, is the
iterated difference of the family `S ↦ Y (lev S)` of `Finset R_{β,o}`. -/
theorem GreenMinor_iter_lev {β : Zd d L} {o : Fin (W ^ d)} (Y : Finset (Vtx d L W) → ℂ) :
    ∀ (l : List (Vtx d L W)) (hl : ∀ k ∈ l, k ∈ GreenMinor_R β o) (S : Finset (GreenMinor_Rows β o)),
      iterDeltaFam l Y (GreenMinor_lev S) =
        iterDeltaFam (l.pmap (fun k hk => (⟨k, hk⟩ : GreenMinor_Rows β o)) hl) (fun S' => Y (GreenMinor_lev S')) S := by
  intro l
  induction l generalizing Y with
  | nil => intro hl S; rfl
  | cons k l ih =>
      intro hl S
      have hk : k ∈ GreenMinor_R β o := hl k List.mem_cons_self
      have hl' : ∀ k' ∈ l, k' ∈ GreenMinor_R β o := fun k' hk' => hl k' (List.mem_cons_of_mem _ hk')
      have hF : (fun S' => deltaFam k Y (GreenMinor_lev S')) =
          deltaFam (⟨k, hk⟩ : GreenMinor_Rows β o) (fun S' => Y (GreenMinor_lev S')) := by
        funext S'
        simp [deltaFam_apply, GreenMinor_lev_insert]
      rw [List.pmap_cons, iterDeltaFam_cons, iterDeltaFam_cons, ih (deltaFam k Y) hl' S, hF]

/-- **The graded bound on protected rows.**  For `u = (β, o)`, `y` of offset `o` in another block, and distinct
rows `k_1, …, k_r ∈ R_{β,o}` (`r ≤ m₀`), on the protected good event,
`‖Δ_{k_1} ⋯ Δ_{k_r} Y^X_{uy}‖, ‖Δ_{k_1} ⋯ Δ_{k_r} Y^A_u‖ ≤ c_Y(r) (2δ)^{r+1}`,
`c_Y(r) = (‖s‖ + 2 d g₀)(1/κ + 1) a_r + (4 d g₀/κ) 2^r a_r²`.  The hypothesis `κ ≤ 1` is needed
(`a_0 = 2/κ ≥ 1`; BA: `κ ≤ ‖m‖ ≤ 1`, `BA/Ward.lean`).  The constants depend on `(d, κ, g₀, ‖s‖, r)`
only: no smallness of `g₀`, no `L`, no `W`. -/
theorem GreenMinor_diff {G M D : Matrix (Vtx d L W) (Vtx d L W) ℂ} {Mb : Zd d L → Zd d L → ℂ}
    {Gs : Finset (Vtx d L W) → Matrix (Vtx d L W) (Vtx d L W) ℂ} {s m : ℂ} {κ δ g₀ : ℝ} {m₀ : ℕ}
    {β : Zd d L} {o : Fin (W ^ d)} {u y : Vtx d L W}
    (hL : 3 ≤ L) (hg : 0 ≤ g₀) (hD : ∀ u l, D u l = if u.2 = l.2 ∧ Adj d L u.1 l.1 then (g₀ : ℂ) else 0)
    (hM : ∀ u v, M u v = if u.2 = v.2 then Mb u.1 v.1 else 0) (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hm : κ ≤ ‖m‖)
    (hMuy : ‖M u y‖ ≤ 1) (hT : GreenMinor_Tower G Gs) (hgood : GreenMinor_good Gs M κ δ m₀ β o) (hu : u = (β, o))
    (hy : y.2 = o ∧ y.1 ≠ β) (l : List (Vtx d L W)) (hl : l.Nodup) (hR : ∀ k ∈ l, k ∈ GreenMinor_R β o)
    (hlen : l.length ≤ m₀) (h2δ : 2 * δ ≤ 1) :
    ‖iterDeltaFam l (fun S => GreenMinor_YX (Gs S) M D s m u y) ∅‖ ≤
        GreenMinor_cY d κ g₀ ‖s‖ l.length * (2 * δ) ^ (l.length + 1) ∧
      ‖iterDeltaFam l (fun S => GreenMinor_YA (Gs S) M D s m u) ∅‖ ≤
        GreenMinor_cY d κ g₀ ‖s‖ l.length * (2 * δ) ^ (l.length + 1) := by
  have hu2 : u.2 = o := by rw [hu]
  have hδ0 : 0 ≤ δ := by
    have := (hgood ∅ (by simp) (Nat.zero_le _) u u (Or.inl hu2) (Or.inl hu2) (Finset.notMem_empty _)
      (Finset.notMem_empty _)).1
    linarith [norm_nonneg (Gs ∅ u u - M u u)]
  have hΨ0 : 0 ≤ 2 * δ := by linarith
  set r := l.length with hr
  have hatom := (GreenMinor_diffBd_atom hM hκ hκ1 hδ0 h2δ hT hgood r ∅ ∅ m₀ (by simp)).1
  have hE : ∀ a b : Vtx d L W, a.2 = o → b.2 = o →
      DiffBd (2 * δ) ∅ m₀ r (GreenMinor_a κ r) 1 (GreenMinor_eFam (β := β) (o := o) Gs M a b ∅) :=
    fun a b ha hb => hatom a b (Or.inl ha) (Or.inl hb)
  have hca : 0 ≤ GreenMinor_a κ r := GreenMinor_a_nonneg hκ hκ1 r
  have hDi : ∀ i : Vtx d L W, D u i ≠ 0 → i.2 = o := by
    intro i h0
    by_contra hne
    apply h0
    rw [hD u i]
    simp only [ite_eq_right_iff]
    rintro ⟨h1, -⟩
    exact absurd (h1.symm.trans hu2) hne
  -- the sums over the hopping row
  have hS : ∀ z : Vtx d L W, z.2 = o →
      DiffBd (2 * δ) ∅ m₀ r (2 * d * g₀ * GreenMinor_a κ r) 1 (fun S => ∑ i, D u i * GreenMinor_eFam (β := β) (o := o) Gs M i z ∅ S) := by
    intro z hz
    have h := GreenMinor_DiffBd_sum hΨ0 (Finset.univ : Finset (Vtx d L W)) (fun i => ‖D u i‖ * GreenMinor_a κ r)
      (fun i S => D u i * GreenMinor_eFam (β := β) (o := o) Gs M i z ∅ S) (fun i _ => by
        by_cases h0 : D u i = 0
        · have h1 : (fun S => D u i * GreenMinor_eFam (β := β) (o := o) Gs M i z ∅ S) = fun _ => (0 : ℂ) := by
            funext S; simp [h0]
          change DiffBd (2 * δ) ∅ m₀ r (‖D u i‖ * GreenMinor_a κ r) 1 (fun S => D u i * GreenMinor_eFam (β := β) (o := o) Gs M i z ∅ S)
          rw [h1]
          exact GreenMinor_DiffBd_zero (by positivity) hΨ0
        · exact GreenMinor_DiffBd_smul (D u i) (hE i z (hDi i h0) hz))
    rw [← Finset.sum_mul, GreenCore_Drow hg hL hD u] at h
    exact h
  -- the pointwise identities: the families are polynomials in the centred atoms
  have hlevR : ∀ (S : Finset (GreenMinor_Rows β o)) (a : Vtx d L W), a.2 = o → a ∉ GreenMinor_lev S := by
    intro S a ha hmem
    exact (GreenMinor_lev_subset S hmem).2 ha
  have hEq : ∀ (a b : Vtx d L W), a.2 = o → b.2 = o → ∀ S,
      GreenMinor_eFam (β := β) (o := o) Gs M a b ∅ S = Gs (GreenMinor_lev S) a b - M a b := by
    intro a b ha hb S
    simp only [GreenMinor_eFam, GreenMinor_gE, Finset.union_empty]
    have hn : ¬ (a ∈ GreenMinor_lev S ∨ b ∈ GreenMinor_lev S) := not_or.2 ⟨hlevR S a ha, hlevR S b hb⟩
    simp [hn]
  have hsum : ∀ (z : Vtx d L W), z.2 = o → ∀ S,
      ∑ i, D u i * (Gs (GreenMinor_lev S) i z - M i z) = ∑ i, D u i * GreenMinor_eFam (β := β) (o := o) Gs M i z ∅ S := by
    intro z hz S
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h0 : D u i = 0
    · simp [h0]
    · rw [hEq i z (hDi i h0) hz S]
  have hXmodel : ∀ S, GreenMinor_YX (Gs (GreenMinor_lev S)) M D s m u y =
      ((M u y / m) * (s * GreenMinor_eFam (β := β) (o := o) Gs M u u ∅ S + (-1 : ℂ) * ∑ i, D u i * GreenMinor_eFam (β := β) (o := o) Gs M i u ∅ S) +
        (∑ i, D u i * GreenMinor_eFam (β := β) (o := o) Gs M i y ∅ S + (-s) * GreenMinor_eFam (β := β) (o := o) Gs M u y ∅ S)) +
        ((1 / m) * (GreenMinor_eFam (β := β) (o := o) Gs M u u ∅ S * ∑ i, D u i * GreenMinor_eFam (β := β) (o := o) Gs M i y ∅ S) +
          (-(1 / m)) * (GreenMinor_eFam (β := β) (o := o) Gs M u y ∅ S * ∑ i, D u i * GreenMinor_eFam (β := β) (o := o) Gs M i u ∅ S)) := by
    intro S
    unfold GreenMinor_YX
    rw [hsum u hu2 S, hsum y hy.1 S, hEq u u hu2 hu2 S, hEq u y hu2 hy.1 S]
    ring
  have hAmodel : ∀ S, GreenMinor_YA (Gs (GreenMinor_lev S)) M D s m u =
      (1 / m) * (s * GreenMinor_eFam (β := β) (o := o) Gs M u u ∅ S + (-1 : ℂ) * ∑ i, D u i * GreenMinor_eFam (β := β) (o := o) Gs M i u ∅ S) := by
    intro S
    unfold GreenMinor_YA
    rw [hsum u hu2 S, hEq u u hu2 hu2 S]
    ring
  -- the graded bounds of the two models
  have hK : 0 ≤ 2 * (d : ℝ) * g₀ := by positivity
  have hdX := GreenMinor_DiffBd_modelX (s := s) (m := m) (Muy := M u y) hΨ0 h2δ r hκ hm hMuy hca hK
    (hE u u hu2 hu2) (hE u y hu2 hy.1) (hS u hu2) (hS y hy.1)
  have hdA := GreenMinor_DiffBd_modelA (s := s) (m := m) hΨ0 r hκ hm hca hK (hE u u hu2 hu2) (hS u hu2)
  have hcY : (‖s‖ + 2 * d * g₀) * (1 / κ + 1) * GreenMinor_a κ r + (2 * (2 * d * g₀) / κ) * 2 ^ r * GreenMinor_a κ r ^ 2 =
      GreenMinor_cY d κ g₀ ‖s‖ r := by
    unfold GreenMinor_cY; ring
  rw [hcY] at hdX hdA
  -- back to the sites
  set l' := l.pmap (fun k hk => (⟨k, hk⟩ : GreenMinor_Rows β o)) hR with hl'
  have hl'nd : l'.Nodup := by
    refine List.Nodup.pmap (fun a ha b hb h => ?_) hl
    exact congrArg Subtype.val h
  have hl'len : l'.length = r := List.length_pmap
  have hfinal : ∀ (Yv : Finset (Vtx d L W) → ℂ) (Ym : Finset (GreenMinor_Rows β o) → ℂ) (c : ℝ),
      (∀ S, Yv (GreenMinor_lev S) = Ym S) → DiffBd (2 * δ) ∅ m₀ r c 1 Ym →
      ‖iterDeltaFam l Yv ∅‖ ≤ c * (2 * δ) ^ (r + 1) := by
    intro Yv Ym c hY hDB
    have e := GreenMinor_iter_lev Yv l hR ∅
    rw [GreenMinor_lev_empty] at e
    rw [e]
    have hf : (fun S' => Yv (GreenMinor_lev S')) = Ym := funext hY
    rw [hf]
    have h := hDB l' ∅ hl'nd (fun k _ hk => Finset.notMem_empty _ hk) (by omega) (by simp; omega)
    rwa [hl'len, add_comm 1 r] at h
  exact ⟨hfinal _ _ _ hXmodel hdX, hfinal _ _ _ hAmodel hdA⟩

end Diff

/-! ## 3. The gain interface and the statements `BAFamGain`, `BAFAav`

The family gain interface `GreenMinor_famGain` (the analogue of `FlucGainUpTo'`, `Green/FlucIterGain.lean`, for the family
`k ↦ Q_k Y_k`, words restricted to rows of the block `A`) is only a definition here; its moment bound (the graded iteration)
is in `BA/GreenCond2.lean`, where `BAFamGain` and `BAFAav` are proved. -/

section Registry

/-- The gain interface `GreenMinor_famGain` at `(B, ρ, M, K)` of the family `Y`, for words whose rows are distinct, `≠ k_i` and in `A`:
`E ∏_i ‖applyOps (L_i) (qRow (k_i) (Y_{k_i}))‖ ≤ B^{#ι} ρ^{Σ numQ}` (the analogue of `FlucGainUpTo'` with `qRow (k i) (Y (k i))` for
`flucDiag`). -/
def GreenMinor_famGain {d : ℕ} (sz : Sizes d) (n : ℕ) (A : Finset (Idx d (sz.L n) (sz.W n)))
    (Y : Idx d (sz.L n) (sz.W n) → sz.SeqΩ → ℂ) (B ρ : ℝ) (M K : ℕ) : Prop :=
  0 ≤ B ∧ 0 ≤ ρ ∧ ∀ (ι : Type) [Fintype ι] (k : ι → Idx d (sz.L n) (sz.W n))
    (L : ι → List (Bool × Idx d (sz.L n) (sz.W n))),
    (∀ i, k i ∈ A) → (∀ i, ((L i).map Prod.snd).Nodup) → (∀ i, ∀ x ∈ L i, x.2 ≠ k i ∧ x.2 ∈ A) →
    (∀ i, (L i).length ≤ M) → Fintype.card ι ≤ K →
    ∫ ω, ∏ i, ‖applyOps sz n (L i) (qRow sz n (k i) (Y (k i))) ω‖ ∂(Sizes.seqP sz) ≤
      B ^ Fintype.card ι * ρ ^ ∑ i, numQ (L i)

/-- The carrier family `Y^A` on the fine index at `(n, t_n)`: `k ↦ (ω ↦ Y^A_{split k})`, with `Y^A` of `GreenMinor_YA` at `G = G_{t_n}(ω)`, `M`,
`D = g₀ Ψ`, `m = BAmF`, `s = E_n + m` (the carriers of `GreenCore_Gc`, `GreenCore_Mc`, `GreenCore_Dc`). -/
def GreenMinor_famA {d : ℕ} (sz : Sizes d) (z : ℕ → ℂ) (t : ℕ → ℝ) (n : ℕ) : Idx d (sz.L n) (sz.W n) → sz.SeqΩ → ℂ :=
  fun k ω => GreenMinor_YA (GreenCore_Gc sz z n (t n) ω) (GreenCore_Mc sz z n) (GreenCore_Dc sz z n)
    ((BAflowEs sz z n : ℂ) + BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n)
    (split d (sz.L n) (sz.W n) k)

/-- The carrier family `Y^X_{x,(α, o(x))}` of the pair of blocks `(β, α)` on the fine index at `(n, t_n)`: `k ↦ (ω ↦ Y^X_{u,(α, o(u))})`,
`u = split k` (the slot `x` of block `β` against the site of block `α` with the same offset). -/
def GreenMinor_famX {d : ℕ} (sz : Sizes d) (z : ℕ → ℂ) (t : ℕ → ℝ) (n : ℕ) (α : Zd d (sz.L n)) :
    Idx d (sz.L n) (sz.W n) → sz.SeqΩ → ℂ :=
  fun k ω => GreenMinor_YX (GreenCore_Gc sz z n (t n) ω) (GreenCore_Mc sz z n) (GreenCore_Dc sz z n)
    ((BAflowEs sz z n : ℂ) + BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n)
    (split d (sz.L n) (sz.W n) k) (α, (split d (sz.L n) (sz.W n) k).2)

/-- **`BAFamGain`** (used in the proof of `BAFAav`).  The family gain interface `GreenMinor_famGain` at `(B, ρ, M, K)`
at the carrier, for `Y^A` and `Y^X_{·,(α,o(·))}` on `A = [β]`, `β ≠ α`: `ρ = 4 δ_n`, `B = C δ_n`,
`δ_n = W^τ Ψ_n`, `M = K = 2p`, eventually in `n`.  Event and window hypotheses as in `BAFAav` (`BAGiiGEX` at `ε₀/2`, the window of `Ψ`,
(3.4) `initialGT2`), `0 < τ ≤ ε₀/2`; `C ≥ 0` depends on the data and on `p`, not on `n`, `β`, `α`; no `∃ c` before the flow. -/
def BAFamGain (d : ℕ) : Prop :=
  ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z →
    ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ BAflowT0 sz z n) → ∀ ε₀ : ℝ, 0 < ε₀ → BAGiiGEX sz z t (ε₀ / 2) →
    ∀ Ψ : ℕ → ℝ, (∀ᶠ n in atTop, ((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2) ≤ Ψ n) →
      (∀ᶠ n in atTop, Ψ n ≤ ((sz.W n : ℕ) : ℝ) ^ (-ε₀)) →
      STInitialGT2gL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) t ε₀ Ψ →
      ∀ τ : ℝ, 0 < τ → τ ≤ ε₀ / 2 → ∀ p : ℕ,
        ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n in atTop, ∀ β α : Zd d (sz.L n), β ≠ α →
          GreenMinor_famGain (sz.withLam 0) n (Iblk d (sz.L n) (sz.W n) β) (GreenMinor_famA sz z t n)
            (C * (((sz.W n : ℕ) : ℝ) ^ τ * Ψ n)) (4 * (((sz.W n : ℕ) : ℝ) ^ τ * Ψ n)) (2 * p) (2 * p) ∧
          GreenMinor_famGain (sz.withLam 0) n (Iblk d (sz.L n) (sz.W n) β) (GreenMinor_famX sz z t n α)
            (C * (((sz.W n : ℕ) : ℝ) ^ τ * Ψ n)) (4 * (((sz.W n : ℕ) : ℝ) ^ τ * Ψ n)) (2 * p) (2 * p)

/-- **`BAFAav`**: the averaged law of the offset
average of `𝒦`: `|W^{-d} Σ_o Σ_{b'} M^{(B)}_{ab'} 𝒦_{(b',o),(a,o)}| ≺ Ψ²`, uniformly in `a`, from `BAGiiGEX` and (3.4) `initialGT2`
(`STInitialGT2gL`); no `∃ c` before the flow.  The entrywise law is taken at the smaller exponent `ε₀/2` (`BAGiiGEX sz z t (ε₀ / 2)`),
because `‖Δ‖_max ≺ W^{-ε₀}` does not give `P(Ω(ε₀)ᶜ) ≤ N^{-D}`, whereas `Ω(ε₀/2) ⊇ {‖Δ‖_max ≤ N^{𝔠ε₀/2} W^{-ε₀}}`; the
statement `BAGbEXPii` is `∀ ε₀ > 0`, so it supplies the hypothesis at every `ε₀`. -/
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

end Registry

end RBM.BA
