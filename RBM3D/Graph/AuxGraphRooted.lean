/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Graph.AuxGraph
import RBM3D.Graph.LWMomExpFar
import RBM3D.Graph.LWProv
/-!
# LW-13b R3 (G): `GtoAG` for a weighted sum, rooted at chosen representatives (T2364)
Paper `7_8:857-958` (`GtoAG`; the centre of an internal molecule is any of its vertices, `7_8:860`; the weight sits on the initial `β^{(k)}`, `T2289d`).  `lwGtoAG_holds` (`Graph/AuxGraph.lean:1018`) sums over all
internal labels with `choose`n roots (`:476`); here the roots `rep` are a hypothesis, a real weight `|Wt| ≤ 1` vanishing unless every root block lies in `Dm` multiplies the terms, and `Γ^aux` is summed over the blocks in `Dm` (`auxValOn`).
Sections: 1 `auxValOn`; 2 rooted forest; 3 main sum with the indicator; 4 `LWGtoAGRooted`; 5 `LWAuxNestedOwnOn`; 6 instances.
Ports (merged RBM3D, text copied and adapted): `Graph/AuxGraph.lean:436-452, 459-537, 901-968, 1018-1127, 1526-1593, 1606-1640`, `Graph/LWMomExpFar.lean:96-103, 391-418`; statements = probe `t/T2348:RBM3D/Probe/T2348Pins.lean:189-224`.
-/
set_option linter.style.setOption false set_option linter.style.longLine false set_option linter.unusedSectionVars false set_option linter.flexible false set_option linter.unusedFintypeInType false set_option linter.unusedDecidableInType false
set_option linter.style.openClassical false set_option linter.style.show false set_option linter.unusedSimpArgs false set_option linter.unusedVariables false set_option linter.deprecated false
noncomputable section
namespace RBM.Graph
open RBM RBM.Gauss
/-! ## 1. `auxValOn` -/
open Classical in
/-- `Γ^aux` summed over the blocks of the internal molecules in `Dm` only (`LGraph.auxVal`, `AuxGraph.lean:79`, restricted) -/
def auxValOn {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I] {κ : Type} [Fintype κ]
    (Γ : LGraph E I) (ξ : κ → κ → ℝ) (be : E → κ) (Dm : Finset κ) : ℝ :=
  haveI : Fintype (LGraph.AuxIMol Γ) := Fintype.ofFinite _
  ∑ b ∈ Fintype.piFinset (fun _ : LGraph.AuxIMol Γ => Dm),
    (Γ.molSolid.map fun e => ξ (LGraph.auxLab Γ be b e.src) (LGraph.auxLab Γ be b e.dst)).prod
section Basic
variable {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]
/-- the value of the restricted auxiliary graph for a constant edge variable: `|Dm|^{n_M} c^{|𝒢_ℳ|}` -/
theorem lwAuxRoot_auxValOn_const {κ : Type} [Fintype κ] (Γ : LGraph E I) (c : ℝ) (be : E → κ) (Dm : Finset κ) :
    auxValOn Γ (fun _ _ => c) be Dm = (Dm.card : ℝ) ^ Γ.nM * c ^ Γ.molSolid.length := by
  classical
  unfold auxValOn
  simp only [List.map_const', List.prod_replicate, Finset.sum_const, nsmul_eq_mul]
  rw [@Fintype.card_piFinset _ _ _ (Fintype.ofFinite _), Finset.prod_const,
    @Finset.card_univ _ (Fintype.ofFinite _), auxGraph_card_aux, Nat.cast_pow]
end Basic
/-! ## 2. The rooted molecular forest (`7_8:922-925`, root given) -/
section Forest
/-- a rank function toward a target set (`auxGraph_exists_rank`, `AuxGraph.lean:436`, private there, copied) -/
private theorem lwAuxRoot_exists_rank {V : Type*} (G : SimpleGraph V) (T : V → Prop)
    (hT : ∀ v, ∃ t, T t ∧ G.Reachable v t) :
    ∃ rk : V → ℕ, ∀ v, ¬ T v → ∃ w, G.Adj v w ∧ rk w < rk v := by
  classical
  have hex : ∀ v, ∃ n, ∃ t, T t ∧ ∃ p : G.Walk v t, p.length = n := fun v => by
    obtain ⟨t, ht, ⟨p⟩⟩ := hT v
    exact ⟨p.length, t, ht, p, rfl⟩
  refine ⟨fun v => Nat.find (hex v), fun v hv => ?_⟩
  obtain ⟨t, ht, p, hp⟩ := Nat.find_spec (hex v)
  cases p with
  | nil => exact absurd ht hv
  | @cons _ w _ hadj p' =>
    refine ⟨w, hadj, ?_⟩
    have h1 : Nat.find (hex w) ≤ p'.length := Nat.find_min' (hex w) ⟨t, ht, p', rfl⟩
    rw [SimpleGraph.Walk.length_cons] at hp
    change Nat.find (hex w) < Nat.find (hex v)
    omega
variable {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]
/-- **the molecular forest with prescribed roots** (`auxGraph_exists_forest`, `AuxGraph.lean:459`, for any choice `rep` of one vertex per internal molecule; only `molOf (inr (rep c)) = c` is used) -/
theorem lwAuxRoot_exists_forest (Γ : LGraph E I) (hD : ∀ e ∈ Γ.dotted, e.eq = false)
    (rep : LGraph.AuxIMol Γ → I) (hrep : ∀ c, Γ.molOf (Sum.inr (rep c)) = c.1) :
    ∃ (par : I → E ⊕ I) (edge : {i : I // i ∉ Set.range rep} → Fin Γ.waved.length) (ρ : I → ℕ),
      Function.Injective rep ∧
      (∀ i : {i : I // i ∉ Set.range rep}, ∀ w, par i.1 = Sum.inr w → ρ w < ρ i.1) ∧
      (∀ i : {i : I // i ∉ Set.range rep},
        (((Γ.waved.get (edge i)).x = Sum.inr i.1 ∧ (Γ.waved.get (edge i)).y = par i.1) ∨
         ((Γ.waved.get (edge i)).y = Sum.inr i.1 ∧ (Γ.waved.get (edge i)).x = par i.1))) ∧
      Function.Injective edge := by
  classical
  let Mi := {c : Γ.Mol // ¬ Γ.IsExtMol c}
  let T : E ⊕ I → Prop := fun v => v.isLeft = true ∨ ∃ m : Mi, v = Sum.inr (rep m)
  have hreach : ∀ v, ∃ t, T t ∧ Γ.molGraph.Reachable v t := by
    intro v
    by_cases h : Γ.IsExtMol (Γ.molOf v)
    · obtain ⟨a, ha⟩ := h
      exact ⟨Sum.inl a, Or.inl rfl, SimpleGraph.ConnectedComponent.eq.1 ha.symm⟩
    · refine ⟨Sum.inr (rep ⟨Γ.molOf v, h⟩), Or.inr ⟨_, rfl⟩, ?_⟩
      exact SimpleGraph.ConnectedComponent.eq.1 (hrep ⟨Γ.molOf v, h⟩).symm
  obtain ⟨rk, hrk⟩ := lwAuxRoot_exists_rank Γ.molGraph T hreach
  have hex : ∀ c : I, ¬ T (Sum.inr c) → ∃ (w : E ⊕ I) (j : Fin Γ.waved.length),
      (((Γ.waved.get j).x = Sum.inr c ∧ (Γ.waved.get j).y = w) ∨
        ((Γ.waved.get j).y = Sum.inr c ∧ (Γ.waved.get j).x = w)) ∧ rk w < rk (Sum.inr c) := by
    intro c hc
    obtain ⟨w, hadj, hlt⟩ := hrk _ hc
    refine ⟨w, ?_⟩
    obtain ⟨e, he, h⟩ := auxGraph_adj_waved Γ hD hadj
    obtain ⟨j, rfl⟩ := List.mem_iff_get.1 he
    refine ⟨j, ?_, hlt⟩
    rcases h with h | h
    · exact Or.inl ⟨h.1, h.2⟩
    · exact Or.inr ⟨h.2, h.1⟩
  choose! par' edge' hpe using hex
  have hnT : ∀ i : I, i ∉ Set.range rep → ¬ T (Sum.inr i) := by
    intro i hi hT
    rcases hT with hT | ⟨m, hm⟩
    · simp at hT
    · exact hi ⟨m, (Sum.inr_injective hm).symm⟩
  refine ⟨par', fun i => edge' i.1 (hnT i.1 i.2), fun i => rk (Sum.inr i), ?_, ?_, ?_, ?_⟩
  · intro m m' h
    apply Subtype.ext
    rw [← hrep m, ← hrep m', h]
  · intro i w hw
    have := (hpe i.1 (hnT i.1 i.2)).2
    rw [hw] at this
    exact this
  · intro i
    simpa using (hpe i.1 (hnT i.1 i.2)).1
  · intro i₁ i₂ h
    apply Subtype.ext
    by_contra hne
    obtain ⟨e1, r1⟩ := hpe i₁.1 (hnT i₁.1 i₁.2)
    obtain ⟨e2, r2⟩ := hpe i₂.1 (hnT i₂.1 i₂.2)
    have h' : edge' i₁.1 (hnT i₁.1 i₁.2) = edge' i₂.1 (hnT i₂.1 i₂.2) := h
    rw [h'] at e1
    rcases e1 with ⟨a1, b1⟩ | ⟨a1, b1⟩ <;> rcases e2 with ⟨a2, b2⟩ | ⟨a2, b2⟩
    · exact hne (Sum.inr_injective (a1.symm.trans a2))
    · rw [a1] at b2
      rw [b1] at a2
      rw [a2] at r1
      rw [← b2] at r2
      omega
    · rw [a1] at b2
      rw [b1] at a2
      rw [a2] at r1
      rw [← b2] at r2
      omega
    · exact hne (Sum.inr_injective (a1.symm.trans a2))
end Forest
/-! ## 3. The main sum with the indicator of the root blocks -/
section MainSum
variable {d L W : ℕ} [NeZero L] [NeZero W] {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]
open Classical in
/-- **the main sum with the indicator** (`auxGraph_main_sum`, `AuxGraph.lean:901`, with `Φ` multiplied by `1[every root block ∈ Dm]`) -/
theorem lwAuxRoot_main_sum (hd : 3 ≤ d) (Γ : LGraph E I) (D : LData (Idx d L W)) {C c : ℝ} {ξ : Zd d L → Zd d L → ℝ}
    (hξ0 : ∀ a b, 0 ≤ ξ a b) (hC : 0 ≤ C) (hc : 0 < c)
    (hS : ∀ x y, ‖D.S x y‖ ≤ C * ((W : ℝ) ^ d)⁻¹ * Real.exp (-(c * (lwBdist d L W x y : ℝ))))
    (hSp : ∀ x y, ‖D.Sp x y‖ ≤ C * ((W : ℝ) ^ d)⁻¹ * Real.exp (-(c * (lwBdist d L W x y : ℝ))))
    (ℓe : E → Idx d L W) (Dm : Finset (Zd d L))
    (root : LGraph.AuxIMol Γ → I) (par : I → E ⊕ I) (edge : {i : I // i ∉ Set.range root} → Fin Γ.waved.length)
    (ρ : I → ℕ) (hrootinj : Function.Injective root)
    (hrank : ∀ i : {i : I // i ∉ Set.range root}, ∀ w, par i.1 = Sum.inr w → ρ w < ρ i.1)
    (hedge : ∀ i : {i : I // i ∉ Set.range root},
      (((Γ.waved.get (edge i)).x = Sum.inr i.1 ∧ (Γ.waved.get (edge i)).y = par i.1) ∨
       ((Γ.waved.get (edge i)).y = Sum.inr i.1 ∧ (Γ.waved.get (edge i)).x = par i.1)))
    (hedgeinj : Function.Injective edge) :
    ∑ ℓi : I → Idx d L W, (if ∀ c, (split d L W (ℓi (root c))).1 ∈ Dm then (1 : ℝ) else 0) *
      ((Γ.molSolid.map fun e => ξ
          (LGraph.auxLab Γ (fun a => (split d L W (ℓe a)).1) (fun c => (split d L W (ℓi (root c))).1) e.src)
          (LGraph.auxLab Γ (fun a => (split d L W (ℓe a)).1) (fun c => (split d L W (ℓi (root c))).1) e.dst)).prod *
        (Γ.waved.map fun e => ‖WEdge.val D (Sum.elim ℓe ℓi) e‖).prod) ≤
      ((W : ℝ) ^ d) ^ Γ.nM * auxValOn Γ ξ (fun a => (split d L W (ℓe a)).1) Dm *
        ((C * expC (d - 2) c) ^ (Γ.nV - Γ.nM) * (C * ((W : ℝ) ^ d)⁻¹) ^ (Γ.nW - (Γ.nV - Γ.nM))) := by
  have : Nonempty (Idx d L W) := ⟨fun _ => 0⟩
  have : Fintype (LGraph.AuxIMol Γ) := Fintype.ofFinite _
  have hK1 := lwKBound_of_decay hd hC hc (K := D.S) hS
  have hK2 := lwKBound_of_decay hd hC hc (K := D.Sp) hSp
  have ha : 0 ≤ C * ((W : ℝ) ^ d)⁻¹ := by positivity
  have hK : 0 ≤ C * expC (d - 2) c := by
    have : 0 < expC (d - 2) c := by unfold expC; positivity
    positivity
  set f : Fin Γ.waved.length → Idx d L W → Idx d L W → ℝ :=
    fun j x y => ‖lwWVal D (Γ.waved.get j) x y‖ with hf
  have hsum : ∀ ℓi : I → Idx d L W, (Γ.waved.map fun e => ‖WEdge.val D (Sum.elim ℓe ℓi) e‖).prod =
      ∏ j : Fin Γ.waved.length, f j (Sum.elim ℓe ℓi (Γ.waved.get j).x) (Sum.elim ℓe ℓi (Γ.waved.get j).y) := by
    intro ℓi
    rw [auxGraph_prod_waved Γ (fun e => ‖WEdge.val D (Sum.elim ℓe ℓi) e‖)]
    rfl
  set P : (LGraph.AuxIMol Γ → Zd d L) → ℝ := fun b =>
    (Γ.molSolid.map fun e => ξ
        (LGraph.auxLab Γ (fun a => (split d L W (ℓe a)).1) b e.src)
        (LGraph.auxLab Γ (fun a => (split d L W (ℓe a)).1) b e.dst)).prod with hP
  have hP0 : ∀ b, 0 ≤ P b := fun b => List.prod_nonneg fun y hy => by
    obtain ⟨e, _, rfl⟩ := List.mem_map.1 hy
    exact hξ0 _ _
  set Φ : (LGraph.AuxIMol Γ → Idx d L W) → ℝ := fun x =>
    (if ∀ c, (split d L W (x c)).1 ∈ Dm then (1 : ℝ) else 0) * P (fun c => (split d L W (x c)).1) with hΦ
  have hΦ0 : ∀ x, 0 ≤ Φ x := fun x => mul_nonneg (by split_ifs <;> norm_num) (hP0 _)
  have hmain := auxGraph_forest_roots (ι := Idx d L W) (E := E) (I := I) (Rt := LGraph.AuxIMol Γ)
    (J := Fin Γ.waved.length) ℓe (fun j => (Γ.waved.get j).x) (fun j => (Γ.waved.get j).y) f
    (C * ((W : ℝ) ^ d)⁻¹) (C * expC (d - 2) c) ha hK (fun j x y => norm_nonneg _)
    (fun j x y => (auxGraph_wval_bound hK1 hK2 (Γ.waved.get j)).1 x y)
    (fun j x => (auxGraph_wval_bound hK1 hK2 (Γ.waved.get j)).2.1 x)
    (fun j y => (auxGraph_wval_bound hK1 hK2 (Γ.waved.get j)).2.2 y)
    root hrootinj par edge ρ hedgeinj hedge hrank Φ hΦ0
  have hcardRt : Fintype.card (LGraph.AuxIMol Γ) = Γ.nM := auxGraph_card_aux Γ
  have hcardI : Fintype.card I = Γ.nV := rfl
  have hcardJ : Fintype.card (Fin Γ.waved.length) = Γ.nW := by simp [LGraph.nW]
  rw [hcardRt, hcardI, hcardJ] at hmain
  have hblocks := auxGraph_sum_blocks (d := d) (L := L) (W := W) (Rt := LGraph.AuxIMol Γ)
    (fun b => (if ∀ c, b c ∈ Dm then (1 : ℝ) else 0) * P b)
  rw [hcardRt] at hblocks
  have hind : ∀ b : LGraph.AuxIMol Γ → Zd d L, (if ∀ c, b c ∈ Dm then (1 : ℝ) else 0) * P b =
      if b ∈ Fintype.piFinset (fun _ : LGraph.AuxIMol Γ => Dm) then P b else 0 := by
    intro b
    by_cases h : ∀ c, b c ∈ Dm
    · simp [Fintype.mem_piFinset, h]
    · simp [Fintype.mem_piFinset, h]
  have hΦsum : ∑ x : LGraph.AuxIMol Γ → Idx d L W, Φ x =
      ((W : ℝ) ^ d) ^ Γ.nM * auxValOn Γ ξ (fun a => (split d L W (ℓe a)).1) Dm := by
    have h1 : ∑ b : LGraph.AuxIMol Γ → Zd d L, (if ∀ c, b c ∈ Dm then (1 : ℝ) else 0) * P b =
        auxValOn Γ ξ (fun a => (split d L W (ℓe a)).1) Dm := by
      simp_rw [hind]
      rw [Finset.sum_ite_mem, Finset.univ_inter]
      unfold auxValOn
      congr
      exact Subsingleton.elim _ _
    rw [← h1]
    exact hblocks
  rw [hΦsum] at hmain
  calc _ = ∑ ℓi : I → Idx d L W, Φ (fun t => ℓi (root t)) *
          ∏ j : Fin Γ.waved.length, f j (Sum.elim ℓe ℓi (Γ.waved.get j).x) (Sum.elim ℓe ℓi (Γ.waved.get j).y) := by
        refine Finset.sum_congr rfl fun ℓi _ => ?_
        rw [hsum]
        simp only [hΦ, hP]
        by_cases h : ∀ c, (split d L W (ℓi (root c))).1 ∈ Dm
        · simp only [h, if_true, one_mul]
          ring
        · simp only [h, if_false, zero_mul]
    _ ≤ _ := hmain
end MainSum
/-! ## 4. `GtoAG` for a weighted sum, rooted at the provenance vertices -/
/-- **`GtoAG` for a weighted sum** (`LWGtoAG`, `AuxGraph.lean:979-998`, same hypotheses): `rep c` is the root of the molecule `c` and carries the weight (`T2289d`); `Wt ≠ 0` only where every root block is in `Dm` -/
def LWGtoAGRooted (d : ℕ) : Prop :=
  3 ≤ d → ∀ (L W : ℕ) [NeZero L] [NeZero W] {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]
    (Γ : LGraph E I), Γ.Normal → (∀ a b : E, Γ.molOf (Sum.inl a) = Γ.molOf (Sum.inl b) → a = b) →
    ∀ (rep : LGraph.AuxIMol Γ → I), (∀ c, Γ.molOf (Sum.inr (rep c)) = c.1) →
    ∀ (D : LData (Idx d L W)) (m : ℂ) (Ψ C c r R : ℝ) (ξ : Zd d L → Zd d L → ℝ) (Dm : Finset (Zd d L)),
      (∀ x y, D.M x y = if x = y then m else 0) →
      (∀ x y, x ≠ y → ‖D.G x y‖ ≤ Ψ) → (∀ x, ‖D.G x x - m‖ ≤ Ψ) → 0 ≤ C → 0 < c →
      (∀ x y, ‖D.S x y‖ ≤ C * ((W : ℝ) ^ d)⁻¹ * Real.exp (-(c * (lwBdist d L W x y : ℝ)))) →
      (∀ x y, ‖D.Sp x y‖ ≤ C * ((W : ℝ) ^ d)⁻¹ * Real.exp (-(c * (lwBdist d L W x y : ℝ)))) →
      (W : ℝ) ^ (-(d : ℝ) / 2) ≤ Ψ → 0 ≤ r → (Fintype.card (E ⊕ I) : ℝ) * r ≤ R → (∀ a b, 0 ≤ ξ a b) →
      (∀ (x y : Idx d L W) (a b : Zd d L), x ≠ y → (zdistD d L ((split d L W x).1 - a) : ℝ) ≤ R →
        (zdistD d L ((split d L W y).1 - b) : ℝ) ≤ R → ‖D.G x y‖ ≤ ξ a b) →
      ∀ (Wt : (E ⊕ I → Idx d L W) → ℝ), (∀ ℓ, |Wt ℓ| ≤ 1) →
        (∀ ℓ, Wt ℓ ≠ 0 → ∀ c, (split d L W (ℓ (Sum.inr (rep c)))).1 ∈ Dm) → ∀ ℓe : E → Idx d L W,
          ‖valW Γ D Wt ℓe‖ ≤
            Γ.sizeConst C (C * expC (d - 2) c) * Ψ ^ (Γ.scalingOrder - LGraph.auxOrd Γ) *
                (((W : ℝ) ^ d) ^ Γ.nM * auxValOn Γ ξ (fun a => (split d L W (ℓe a)).1) Dm) +
              Real.exp (-(c * r / 2)) * Γ.sizeConst C (C * expC (d - 2) (c / 2)) * Γ.scalingSize Ψ W d L
/-- **`GtoAG` for a weighted sum rooted at `rep`** (twin of `lwGtoAG_holds`, `AuxGraph.lean:1018-1127`: `|Wt| ≤ 1`, the restricted main sum, the merged tail sum) -/
theorem lwGtoAGRooted_holds (d : ℕ) : LWGtoAGRooted d := by
  intro hd L W _ _ E I _ _ _ _ Γ hN hext rep hrep D m Ψ C c r R ξ Dm hM hG hGd hC hc hS hSp hwin hr hRr hξ0 hξ
    Wt hWt1 hWt0 ℓe
  classical
  have hne : Nonempty (Idx d L W) := ⟨fun _ => 0⟩
  have hΨ : 0 ≤ Ψ := (norm_nonneg _).trans (hGd (fun _ => 0))
  have hWpos : (0 : ℝ) < W := Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne W))
  obtain ⟨par, edge, ρ, hrootinj, hrank, hedge, hedgeinj⟩ := lwAuxRoot_exists_forest Γ hN.1 rep hrep
  obtain ⟨h1, h2⟩ := Γ.counters_le hN.1
  have hmS := Γ.molSolid_length_le
  have hmain := lwAuxRoot_main_sum hd Γ D hξ0 hC hc hS hSp ℓe Dm rep par edge ρ hrootinj hrank hedge hedgeinj
  have htail := auxGraph_tail_sum hd Γ hN D (r := r) hGd hC hc hS hSp ℓe
  have hwin' : 1 ≤ (W : ℝ) ^ d * Ψ ^ 2 := (one_le_pow_mul_sq_iff W d hWpos hΨ).1 hwin
  have hWd : (0 : ℝ) < (W : ℝ) ^ d := pow_pos hWpos d
  have hinv : ((W : ℝ) ^ d)⁻¹ ≤ Ψ ^ 2 := by
    rw [inv_le_iff_one_le_mul₀ hWd]; linarith
  have ha : C * ((W : ℝ) ^ d)⁻¹ ≤ C * Ψ ^ 2 := mul_le_mul_of_nonneg_left hinv hC
  have ha0 : 0 ≤ C * ((W : ℝ) ^ d)⁻¹ := by positivity
  have hapow : (C * ((W : ℝ) ^ d)⁻¹) ^ (Γ.nW - (Γ.nV - Γ.nM)) ≤ C ^ (Γ.nW - (Γ.nV - Γ.nM)) * Ψ ^ (2 * (Γ.nW - (Γ.nV - Γ.nM))) := by
    calc (C * ((W : ℝ) ^ d)⁻¹) ^ (Γ.nW - (Γ.nV - Γ.nM)) ≤ (C * Ψ ^ 2) ^ (Γ.nW - (Γ.nV - Γ.nM)) :=
          pow_le_pow_left₀ ha0 ha _
      _ = _ := by rw [mul_pow, ← pow_mul, mul_comm 2]
  have hexp : Γ.scalingOrder - LGraph.auxOrd Γ =
      (((Γ.nS - Γ.molSolid.length) + 2 * (Γ.nW - (Γ.nV - Γ.nM)) : ℕ) : ℤ) := by
    rw [Γ.scalingOrder_sub_auxOrd]
    unfold LGraph.nV at *
    omega
  rw [hexp, zpow_natCast]
  have hK0 : 0 ≤ C * expC (d - 2) c := by
    have : 0 < expC (d - 2) c := by unfold expC; positivity
    positivity
  set Ind : (I → Idx d L W) → ℝ := fun ℓi => if ∀ c, (split d L W (ℓi (rep c))).1 ∈ Dm then (1 : ℝ) else 0 with hInd
  have hmain' : ∑ ℓi : I → Idx d L W, ‖Γ.coeff‖ * Ψ ^ (Γ.nS - Γ.molSolid.length) *
        (Ind ℓi * ((Γ.molSolid.map fun e => ξ
          (LGraph.auxLab Γ (fun a => (split d L W (ℓe a)).1) (fun c => (split d L W (ℓi (rep c))).1) e.src)
          (LGraph.auxLab Γ (fun a => (split d L W (ℓe a)).1) (fun c => (split d L W (ℓi (rep c))).1) e.dst)).prod *
        (Γ.waved.map fun e => ‖WEdge.val D (Sum.elim ℓe ℓi) e‖).prod)) ≤
      Γ.sizeConst C (C * expC (d - 2) c) * Ψ ^ ((Γ.nS - Γ.molSolid.length) + 2 * (Γ.nW - (Γ.nV - Γ.nM))) *
        (((W : ℝ) ^ d) ^ Γ.nM * auxValOn Γ ξ (fun a => (split d L W (ℓe a)).1) Dm) := by
    rw [← Finset.mul_sum]
    have hcn : 0 ≤ ‖Γ.coeff‖ * Ψ ^ (Γ.nS - Γ.molSolid.length) := by positivity
    have hav0 : 0 ≤ auxValOn Γ ξ (fun a => (split d L W (ℓe a)).1) Dm := by
      unfold auxValOn
      exact Finset.sum_nonneg fun b _ => List.prod_nonneg fun y hy => by
        obtain ⟨e, _, rfl⟩ := List.mem_map.1 hy
        exact hξ0 _ _
    calc ‖Γ.coeff‖ * Ψ ^ (Γ.nS - Γ.molSolid.length) * ∑ ℓi : I → Idx d L W,
          (Ind ℓi * ((Γ.molSolid.map fun e => ξ
            (LGraph.auxLab Γ (fun a => (split d L W (ℓe a)).1) (fun c => (split d L W (ℓi (rep c))).1) e.src)
            (LGraph.auxLab Γ (fun a => (split d L W (ℓe a)).1) (fun c => (split d L W (ℓi (rep c))).1) e.dst)).prod *
          (Γ.waved.map fun e => ‖WEdge.val D (Sum.elim ℓe ℓi) e‖).prod))
        ≤ ‖Γ.coeff‖ * Ψ ^ (Γ.nS - Γ.molSolid.length) *
          (((W : ℝ) ^ d) ^ Γ.nM * auxValOn Γ ξ (fun a => (split d L W (ℓe a)).1) Dm *
            ((C * expC (d - 2) c) ^ (Γ.nV - Γ.nM) * (C * ((W : ℝ) ^ d)⁻¹) ^ (Γ.nW - (Γ.nV - Γ.nM)))) :=
          mul_le_mul_of_nonneg_left hmain hcn
      _ ≤ ‖Γ.coeff‖ * Ψ ^ (Γ.nS - Γ.molSolid.length) *
          (((W : ℝ) ^ d) ^ Γ.nM * auxValOn Γ ξ (fun a => (split d L W (ℓe a)).1) Dm *
            ((C * expC (d - 2) c) ^ (Γ.nV - Γ.nM) *
              (C ^ (Γ.nW - (Γ.nV - Γ.nM)) * Ψ ^ (2 * (Γ.nW - (Γ.nV - Γ.nM)))))) := by
          refine mul_le_mul_of_nonneg_left ?_ hcn
          refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (by positivity) hav0)
          exact mul_le_mul_of_nonneg_left hapow (by positivity)
      _ = _ := by
          unfold LGraph.sizeConst
          rw [pow_add]
          ring
  have hpt : ∀ ℓi : I → Idx d L W, ‖((Wt (Sum.elim ℓe ℓi) : ℝ) : ℂ) * Γ.term D (Sum.elim ℓe ℓi)‖ ≤
      ‖Γ.coeff‖ * Ψ ^ (Γ.nS - Γ.molSolid.length) *
        (Ind ℓi * ((Γ.molSolid.map fun e => ξ
          (LGraph.auxLab Γ (fun a => (split d L W (ℓe a)).1) (fun c => (split d L W (ℓi (rep c))).1) e.src)
          (LGraph.auxLab Γ (fun a => (split d L W (ℓe a)).1) (fun c => (split d L W (ℓi (rep c))).1) e.dst)).prod *
        (Γ.waved.map fun e => ‖WEdge.val D (Sum.elim ℓe ℓi) e‖).prod)) +
      ‖Γ.coeff‖ * Ψ ^ Γ.nS *
        (Real.exp (-(c * r / 2)) * (Γ.waved.map fun e => ‖WEdge.val (auxGraph_wdata D c) (Sum.elim ℓe ℓi) e‖).prod) := by
    intro ℓi
    have hMn0 : 0 ≤ (Γ.molSolid.map fun e => ξ
          (LGraph.auxLab Γ (fun a => (split d L W (ℓe a)).1) (fun c => (split d L W (ℓi (rep c))).1) e.src)
          (LGraph.auxLab Γ (fun a => (split d L W (ℓe a)).1) (fun c => (split d L W (ℓi (rep c))).1) e.dst)).prod :=
      List.prod_nonneg fun y hy => by
        obtain ⟨e, _, rfl⟩ := List.mem_map.1 hy
        exact hξ0 _ _
    have h2' : 0 ≤ (Γ.waved.map fun e => ‖WEdge.val D (Sum.elim ℓe ℓi) e‖).prod :=
      List.prod_nonneg fun y hy => by
        obtain ⟨e, _, rfl⟩ := List.mem_map.1 hy
        exact norm_nonneg _
    have hInd0 : 0 ≤ Ind ℓi := by simp only [hInd]; split_ifs <;> norm_num
    have hMn : 0 ≤ ‖Γ.coeff‖ * Ψ ^ (Γ.nS - Γ.molSolid.length) *
        (Ind ℓi * ((Γ.molSolid.map fun e => ξ
          (LGraph.auxLab Γ (fun a => (split d L W (ℓe a)).1) (fun c => (split d L W (ℓi (rep c))).1) e.src)
          (LGraph.auxLab Γ (fun a => (split d L W (ℓe a)).1) (fun c => (split d L W (ℓi (rep c))).1) e.dst)).prod *
        (Γ.waved.map fun e => ‖WEdge.val D (Sum.elim ℓe ℓi) e‖).prod)) := by positivity
    have hTl : 0 ≤ ‖Γ.coeff‖ * Ψ ^ Γ.nS *
        (Real.exp (-(c * r / 2)) * (Γ.waved.map fun e => ‖WEdge.val (auxGraph_wdata D c) (Sum.elim ℓe ℓi) e‖).prod) := by
      have h2 : 0 ≤ (Γ.waved.map fun e => ‖WEdge.val (auxGraph_wdata D c) (Sum.elim ℓe ℓi) e‖).prod :=
        List.prod_nonneg fun y hy => by
          obtain ⟨e, _, rfl⟩ := List.mem_map.1 hy
          exact norm_nonneg _
      positivity
    by_cases hW0 : Wt (Sum.elim ℓe ℓi) = 0
    · rw [hW0]
      simp only [Complex.ofReal_zero, zero_mul, norm_zero]
      exact add_nonneg hMn hTl
    · have hind : Ind ℓi = 1 := by
        simp only [hInd]
        exact if_pos fun c' => by simpa using hWt0 _ hW0 c'
      have hw1 : ‖((Wt (Sum.elim ℓe ℓi) : ℝ) : ℂ) * Γ.term D (Sum.elim ℓe ℓi)‖ ≤ ‖Γ.term D (Sum.elim ℓe ℓi)‖ := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        exact mul_le_of_le_one_left (norm_nonneg _) (hWt1 _)
      refine hw1.trans ?_
      rw [hind, one_mul]
      by_cases hconf : ∀ e ∈ Γ.waved, (lwBdist d L W (Sum.elim ℓe ℓi e.x) (Sum.elim ℓe ℓi e.y) : ℝ) ≤ r
      · exact (auxGraph_term_conf Γ hN D hM hG hGd hξ0 hξ hr hRr ℓe ℓi rep hrep hconf).trans
          (le_add_of_nonneg_right hTl)
      · push Not at hconf
        have := auxGraph_term_tail Γ hN D hM hG hGd hc _ hconf
        refine this.trans (le_add_of_nonneg_left ?_)
        rw [hind, one_mul] at hMn
        exact hMn
  unfold valW
  calc ‖∑ ℓi : I → Idx d L W, ((Wt (Sum.elim ℓe ℓi) : ℝ) : ℂ) * Γ.term D (Sum.elim ℓe ℓi)‖
      ≤ ∑ ℓi : I → Idx d L W, ‖((Wt (Sum.elim ℓe ℓi) : ℝ) : ℂ) * Γ.term D (Sum.elim ℓe ℓi)‖ := norm_sum_le _ _
    _ ≤ ∑ ℓi : I → Idx d L W, (‖Γ.coeff‖ * Ψ ^ (Γ.nS - Γ.molSolid.length) *
        (Ind ℓi * ((Γ.molSolid.map fun e => ξ
          (LGraph.auxLab Γ (fun a => (split d L W (ℓe a)).1) (fun c => (split d L W (ℓi (rep c))).1) e.src)
          (LGraph.auxLab Γ (fun a => (split d L W (ℓe a)).1) (fun c => (split d L W (ℓi (rep c))).1) e.dst)).prod *
        (Γ.waved.map fun e => ‖WEdge.val D (Sum.elim ℓe ℓi) e‖).prod)) +
      ‖Γ.coeff‖ * Ψ ^ Γ.nS *
        (Real.exp (-(c * r / 2)) * (Γ.waved.map fun e => ‖WEdge.val (auxGraph_wdata D c) (Sum.elim ℓe ℓi) e‖).prod)) :=
        Finset.sum_le_sum fun ℓi _ => hpt ℓi
    _ = _ := Finset.sum_add_distrib
    _ ≤ _ := add_le_add hmain' htail
/-! ## 5. The nested form of `Γ^aux` with the internal labels restricted to `Dm` -/
section Nested
open Classical
variable {Q : PGraph (Fin 2)} {p : ℕ}
/-- **the restricted value of the nested graph** (`auxGraph_val_eq`, `AuxGraph.lean:1526`, over the internal labels in `Dm`) -/
theorem lwAuxRoot_val_eq_on (hxy : Q.g.molOf (Sum.inl (Q.ext 0)) ≠ Q.g.molOf (Sum.inl (Q.ext 1)))
    (Dt : auxGraph_Data Q p) (hM : (∑ i, localReg_stepEdges (Dt.W i)) + (↑(Dt.rest.map fun st => s(st.1, st.2)) : Multiset (Sym2 Q.g.Mol)) = Q.g.localReg_molEdgeMS)
    {κ : Type} [Fintype κ] [DecidableEq κ] (ξ : κ → κ → ℝ) (hsymm : ∀ u v, ξ u v = ξ v u) (be : Q.E' → κ) (Dm : Finset κ) :
    (auxGraph_ngraph Dt).valOn ξ (fun _ => be (Q.ext 0)) (fun _ => be (Q.ext 1))
        (Fintype.piFinset fun _ : Fin Q.g.nM => Dm) = auxValOn Q.g ξ be Dm := by
  unfold auxValOn
  refine Finset.sum_equiv (Dt.e.arrowCongr (Equiv.refl κ)) (fun ℓ => ?_) (fun ℓ _ => ?_)
  · simp only [Fintype.mem_piFinset, Equiv.arrowCongr_apply, Equiv.coe_refl, Function.comp_apply, id_eq]
    exact ⟨fun h c => h _, fun h j => by simpa using h (Dt.e j)⟩
  set bb : LGraph.AuxIMol Q.g → κ := (Dt.e.arrowCongr (Equiv.refl κ)) ℓ with hbb
  have hbbe : ∀ j, bb (Dt.e j) = ℓ j := by
    intro j; simp [hbb, Equiv.arrowCongr]
  -- the labels of the vertices of the nested graph are the blocks of the molecules
  have hlab : ∀ (i : Fin p) (c : Q.g.Mol),
      Sum.elim (Sum.elim (fun _ : Fin p => be (Q.ext 0)) (fun _ : Fin p => be (Q.ext 1))) ℓ (auxGraph_nodeV Dt i c) =
        LGraph.auxLab Q.g be bb c := by
    intro i c
    rcases auxGraph_mol_cls c with rfl | rfl | hc
    · rw [auxGraph_nodeV_x, auxGraph_auxLab_ext Q.g (auxGraph_ext_inj hxy)]
      rfl
    · rw [auxGraph_nodeV_y hxy, auxGraph_auxLab_ext Q.g (auxGraph_ext_inj hxy)]
      rfl
    · rw [auxGraph_nodeV_int Dt i c hc]
      unfold LGraph.auxLab
      rw [dif_neg hc]
      change ℓ (Dt.e.symm ⟨c, hc⟩) = bb ⟨c, hc⟩
      rw [← hbbe, Equiv.apply_symm_apply]
  let Fm : Sym2 Q.g.Mol → ℝ := Sym2.lift ⟨fun c c' => ξ (LGraph.auxLab Q.g be bb c) (LGraph.auxLab Q.g be bb c'),
    fun c c' => hsymm _ _⟩
  have hFm : ∀ c c', Fm s(c, c') = ξ (LGraph.auxLab Q.g be bb c) (LGraph.auxLab Q.g be bb c') := fun c c' => rfl
  set F : NEdge p Q.g.nM → ℝ := fun e => if e.ghost then (1 : ℝ) else
    ξ (Sum.elim (Sum.elim (fun _ : Fin p => be (Q.ext 0)) (fun _ : Fin p => be (Q.ext 1))) ℓ e.u)
      (Sum.elim (Sum.elim (fun _ : Fin p => be (Q.ext 0)) (fun _ : Fin p => be (Q.ext 1))) ℓ e.v) with hF
  have hFslot : ∀ s : auxGraph_Slots Dt, F (auxGraph_edgeOf Dt s) =
      Sum.elim (fun ik : Σ i : Fin p, Fin (Dt.W i).length =>
          Fm s(((Dt.W ik.1).get ik.2).1, ((Dt.W ik.1).get ik.2).2))
        (fun r : Fin Dt.rest.length => Fm s((Dt.rest.get r).1, (Dt.rest.get r).2)) s := by
    intro s
    rcases s with ⟨i, k⟩ | r
    · simp only [hF, auxGraph_edgeOf, Bool.false_eq_true, ite_false, Sum.elim_inl, hFm, hlab]
    · simp only [hF, auxGraph_edgeOf, Bool.false_eq_true, ite_false, Sum.elim_inr, hFm, hlab]
  have h1 : ((auxGraph_ngraph Dt).es.map F).prod = ∏ s : auxGraph_Slots Dt, F (auxGraph_edgeOf Dt s) := by
    change ((List.ofFn _).map F).prod = _
    rw [List.map_ofFn, List.prod_ofFn]
    exact Equiv.prod_comp (Fintype.equivFin (auxGraph_Slots Dt)).symm (fun s => F (auxGraph_edgeOf Dt s))
  have h2 : ∏ s : auxGraph_Slots Dt, F (auxGraph_edgeOf Dt s) =
      (∏ i : Fin p, ((localReg_stepEdges (Dt.W i)).map Fm).prod) *
        (((↑(Dt.rest.map fun st => s(st.1, st.2)) : Multiset (Sym2 Q.g.Mol)).map Fm).prod) := by
    simp only [hFslot]
    rw [Fintype.prod_sum_type, Fintype.prod_sigma]
    simp only [Sum.elim_inl, Sum.elim_inr]
    congr 1
    · refine Finset.prod_congr rfl fun i _ => ?_
      rw [auxGraph_prod_fin_get (Dt.W i) (fun st => Fm s(st.1, st.2))]
      unfold localReg_stepEdges
      rw [Multiset.map_coe, Multiset.prod_coe, List.map_map]
      rfl
    · rw [auxGraph_prod_fin_get Dt.rest (fun st => Fm s(st.1, st.2)), Multiset.map_coe, Multiset.prod_coe, List.map_map]
      rfl
  have h3 : ((Q.g.localReg_molEdgeMS).map Fm).prod =
      (Q.g.molSolid.map fun e => ξ (LGraph.auxLab Q.g be bb e.src) (LGraph.auxLab Q.g be bb e.dst)).prod := by
    unfold LGraph.localReg_molEdgeMS
    rw [Multiset.map_coe, Multiset.prod_coe, List.map_map]
    rfl
  change ((auxGraph_ngraph Dt).es.map F).prod = _
  rw [← h3, ← hM, Multiset.map_add, Multiset.prod_add, auxGraph_prod_map_sum, ← h2, ← h1]
end Nested
open Classical in
/-- `LWAuxNestedOwn` (`LWMomExpFar.lean:96`) with the restricted sum (the bridge to `valOn` with `piFinset Dm`) -/
def LWAuxNestedOwnOn : Prop :=
  ∀ (p : ℕ) (Q : PGraph (Fin 2)), 0 < p → Q.LocReg345 p →
    Q.g.molOf (Sum.inl (Q.ext 0)) ≠ Q.g.molOf (Sum.inl (Q.ext 1)) →
    ∃ Γa : NGraph p Q.g.nM, Γa.NoGhost ∧ Γa.IsNested ∧ lwMomExpFar_ownExt Γa ∧ Γa.ordN = LGraph.auxOrd Q.g ∧
      ∀ {κ : Type} [Fintype κ] [DecidableEq κ] (ξ : κ → κ → ℝ), (∀ u v, ξ u v = ξ v u) → ∀ be : Q.E' → κ,
        ∀ Dm : Finset κ, Γa.valOn ξ (fun _ => be (Q.ext 0)) (fun _ => be (Q.ext 1))
          (Fintype.piFinset fun _ : Fin Q.g.nM => Dm) = auxValOn Q.g ξ be Dm
/-- **The nested form of `Γ^aux` with `ownExt`, restricted** (the proof of `lwMomExpFar_auxOwn`, `LWMomExpFar.lean:391-418`, with `lwAuxRoot_val_eq_on`). -/
theorem lwAuxNestedOwnOn_holds : LWAuxNestedOwnOn := by
  classical
  rintro p Q hp ⟨W, h3, h4, h5⟩ hxy
  have : Fintype (LGraph.AuxIMol Q.g) := Fintype.ofFinite _
  let e : Fin Q.g.nM ≃ LGraph.AuxIMol Q.g := (Fintype.equivFinOfCardEq (auxGraph_card_aux Q.g)).symm
  obtain ⟨R, hR⟩ := Multiset.le_iff_exists_add.1 h3.2
  let Dt : auxGraph_Data Q p := ⟨hp, e, W, R.toList.map fun z => Quot.out z⟩
  have hout : ∀ z : Sym2 Q.g.Mol, s((Quot.out z).1, (Quot.out z).2) = z := fun z => Quot.out_eq z
  have hcover : (∑ i, localReg_stepEdges (Dt.W i)) +
      (↑(Dt.rest.map fun st => s(st.1, st.2)) : Multiset (Sym2 Q.g.Mol)) = Q.g.localReg_molEdgeMS := by
    have : (↑(Dt.rest.map fun st => s(st.1, st.2)) : Multiset (Sym2 Q.g.Mol)) = R := by
      change (↑((R.toList.map fun z => Quot.out z).map fun st => s(st.1, st.2)) : Multiset (Sym2 Q.g.Mol)) = R
      rw [List.map_map]
      have h1 : ((fun st : Q.g.Mol × Q.g.Mol => s(st.1, st.2)) ∘ fun z : Sym2 Q.g.Mol => Quot.out z) = id := by
        funext z; exact hout z
      rw [h1, List.map_id, Multiset.coe_toList]
    rw [this]
    exact hR.symm
  have hnd : ∀ i, ∀ st ∈ Dt.W i, st.1 ≠ st.2 := by
    intro i st hst
    have h1 : s(st.1, st.2) ∈ localReg_stepEdges (W i) := localReg_mem_stepEdges.2 ⟨st, hst, rfl⟩
    have h2 : s(st.1, st.2) ∈ ∑ j, localReg_stepEdges (W j) := Multiset.mem_sum.2 ⟨i, Finset.mem_univ _, h1⟩
    have h3' := auxGraph_molEdgeMS_nd Q.g (Multiset.mem_of_le h3.2 h2)
    rwa [Sym2.mk_isDiag_iff] at h3'
  have hndr : ∀ st ∈ Dt.rest, st.1 ≠ st.2 := by
    intro st hst
    obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hst
    have hzR : z ∈ R := Multiset.mem_toList.1 hz
    have hz' : z ∈ Q.g.localReg_molEdgeMS := by rw [hR]; exact Multiset.mem_add.2 (Or.inr hzR)
    have := auxGraph_molEdgeMS_nd Q.g hz'
    rw [← hout z] at this
    rwa [Sym2.mk_isDiag_iff] at this
  exact ⟨auxGraph_ngraph Dt, auxGraph_noGhost Dt, auxGraph_isNested hxy Dt h3.1 hnd hndr h4 h5,
    lwMomExpFar_auxGraph_ownExt Dt, auxGraph_ordN Dt hcover,
    fun ξ hsymm be Dm => lwAuxRoot_val_eq_on hxy Dt hcover ξ hsymm be Dm⟩
/-! ## 6. Compiled nonempty instances at `d = 3`
The merged data of `AuxGraph.lean` (`Instances`, `Instances3`, `Instances5`): `d = 3`, `L = 4`, `W = 2`, `auxGraph_instD` (`G = m(0) I + (1/2) J`, `Ψ = 1/2`), `figGraph`
(`|E ⊕ I| = 8 = R`, `n_M = 2`, `|𝒢_ℳ| = 6`), `localReg2_inst_Q` (`p = 2`, `n_M = 1`, `|𝒢_ℳ| = 4`).  The block set is `Dm = {0, e₀} ⊂ Z_4^3` (2 of 64 points). -/
section Instances
/-- every graph has a choice of roots (one vertex in each internal molecule) -/
theorem lwAuxRoot_exists_rep {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I] (Γ : LGraph E I) :
    ∃ rep : LGraph.AuxIMol Γ → I, ∀ c, Γ.molOf (Sum.inr (rep c)) = c.1 := by
  have hMi : ∀ c : LGraph.AuxIMol Γ, ∃ i : I, Γ.molOf (Sum.inr i) = c.1 := by
    rintro ⟨c, hc⟩
    induction c using SimpleGraph.ConnectedComponent.ind with | h v => ?_
    rcases v with a | i
    · exact absurd ⟨a, rfl⟩ hc
    · exact ⟨i, rfl⟩
  choose rep hrep using hMi
  exact ⟨rep, hrep⟩
private theorem lwAuxRoot_Dm_card : ({0, Pi.single 0 1} : Finset (Zd 3 4)).card = 2 := by decide +kernel
/-- **Instance of `lwGtoAGRooted_holds`** at `figGraph` (`d = 3`, `L = 4`, `W = 2`, `auxGraph_instD`, `Ψ = 1/2`, `r = 1`, `R = 8`, `ξ ≡ 1/2`), roots `rep`, `Dm = {0, e₀}`, `Wt = 1[every root block ∈ Dm]` (takes the values `1` and `0`); restricted main term `|Dm|^{n_M} (1/2)^{|𝒢_ℳ|} = 1/16` (full sum: `64`) -/
example : ∃ (rep : LGraph.AuxIMol figGraph → Fin 6) (Wt : (Fin 2 ⊕ Fin 6 → Idx 3 4 2) → ℝ) (C c : ℝ), 0 < C ∧ 0 < c ∧
    (∀ c, figGraph.molOf (Sum.inr (rep c)) = c.1) ∧ (∃ ℓ, Wt ℓ = 1) ∧ (∃ ℓ, Wt ℓ = 0) ∧
    auxValOn figGraph (fun _ _ => (1 / 2 : ℝ)) (fun a => (split 3 4 2 (lwSizeEll a)).1) ({0, Pi.single 0 1} : Finset (Zd 3 4)) = 1 / 16 ∧
    ‖valW figGraph auxGraph_instD Wt lwSizeEll‖ ≤
      figGraph.sizeConst C (C * expC (3 - 2) c) * (1 / 2 : ℝ) ^ (figGraph.scalingOrder - figGraph.auxOrd) *
          ((((2 : ℕ) : ℝ) ^ 3) ^ figGraph.nM *
            auxValOn figGraph (fun _ _ => (1 / 2 : ℝ)) (fun a => (split 3 4 2 (lwSizeEll a)).1)
              ({0, Pi.single 0 1} : Finset (Zd 3 4))) +
        Real.exp (-(c * 1 / 2)) * figGraph.sizeConst C (C * expC (3 - 2) (c / 2)) * figGraph.scalingSize (1 / 2) 2 3 4 := by
  classical
  obtain ⟨rep, hrep⟩ := lwAuxRoot_exists_rep figGraph
  obtain ⟨C, c, hC, hc, h⟩ := lwSpOf_decay_E 3 le_rfl 1 (1 / 2) one_pos (by norm_num)
  obtain ⟨h1, h2⟩ := h 4 2 (by norm_num) (1 / 2) (1 / 2) 0 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  set Dm : Finset (Zd 3 4) := {0, Pi.single 0 1} with hDm
  set Wt : (Fin 2 ⊕ Fin 6 → Idx 3 4 2) → ℝ := fun ℓ =>
    if ∀ c, (split 3 4 2 (ℓ (Sum.inr (rep c)))).1 ∈ Dm then 1 else 0 with hWt
  have hWt1 : ∀ ℓ, |Wt ℓ| ≤ 1 := fun ℓ => by simp only [hWt]; split_ifs <;> simp
  have hWt0 : ∀ ℓ, Wt ℓ ≠ 0 → ∀ c, (split 3 4 2 (ℓ (Sum.inr (rep c)))).1 ∈ Dm := fun ℓ hℓ => by
    by_contra hcon
    exact hℓ (by simp only [hWt]; exact if_neg hcon)
  have hcard : Fintype.card (LGraph.AuxIMol figGraph) = 2 := by
    rw [auxGraph_card_aux]; exact figGraph_counters.2.2.2
  obtain ⟨c₀⟩ : Nonempty (LGraph.AuxIMol figGraph) := Fintype.card_pos_iff.1 (by omega)
  refine ⟨rep, Wt, C, c, hC, hc, hrep, ⟨fun _ => fun _ => 0, ?_⟩, ⟨fun _ => fun _ => 2, ?_⟩, ?_, ?_⟩
  · simp only [hWt]
    refine if_pos fun c' => ?_
    have : (split 3 4 2 ((fun _ : Fin 2 ⊕ Fin 6 => (fun _ : Fin 3 => (0 : ZMod 8))) (Sum.inr (rep c')))).1 = 0 := by
      funext k; simp [split, blk]
    rw [this]; exact Finset.mem_insert_self _ _
  · simp only [hWt]
    refine if_neg fun hall => ?_
    have h0 := hall c₀
    have : (split 3 4 2 ((fun _ : Fin 2 ⊕ Fin 6 => (fun _ : Fin 3 => (2 : ZMod 8))) (Sum.inr (rep c₀)))).1 =
        (fun _ : Fin 3 => (1 : ZMod 4)) := by
      funext k; simp [split, blk]; decide +kernel
    rw [this] at h0
    revert h0; decide +kernel
  · rw [lwAuxRoot_auxValOn_const, lwAuxRoot_Dm_card, (figGraph_counters).2.2.2, auxGraph_figGraph_molSolid]; norm_num
  · have hmain := lwGtoAGRooted_holds 3 le_rfl 4 2 figGraph (by decide) auxGraph_figGraph_hext rep hrep auxGraph_instD (mE 0)
      (1 / 2) C c 1 8 (fun _ _ => 1 / 2) Dm auxGraph_instD_hM auxGraph_instD_hG auxGraph_instD_hGd hC.le hc h1 h2
      auxGraph_inst_window (by norm_num) (by simp) (fun _ _ => by norm_num)
      (fun x y a b hxy _ _ => (auxGraph_instD_hG x y hxy)) Wt hWt1 hWt0 lwSizeEll
    exact hmain
/-- **Instance of `lwAuxNestedOwnOn_holds`** at `localReg2_inst_Q.pack` (`p = 2`, `q = n_M = 1`): `NoGhost`, `IsNested`, `ownExt`, `ordN = 2`, value at `ξ ≡ 1/2`, internal labels in `Dm = {0, e₀}`: `|Dm| (1/2)^4 = 1/8` -/
example : ∃ Γa : NGraph 2 localReg2_inst_Q.nM, Γa.NoGhost ∧ Γa.IsNested ∧ lwMomExpFar_ownExt Γa ∧ Γa.ordN = 2 ∧
    Γa.valOn (fun _ _ => (1 / 2 : ℝ)) (fun _ => (0 : Zd 3 4)) (fun _ => 0)
      (Fintype.piFinset fun _ : Fin localReg2_inst_Q.nM => ({0, Pi.single 0 1} : Finset (Zd 3 4))) = 1 / 8 := by
  obtain ⟨Γa, h1, h2, h3, h4, h5⟩ := lwAuxNestedOwnOn_holds 2 localReg2_inst_Q.pack (by norm_num)
    localReg2_inst_Q_locReg345 auxGraph_inst_Q_hxy
  refine ⟨Γa, h1, h2, h3, h4.trans auxGraph_inst_Q_auxOrd, ?_⟩
  have := h5 (κ := Zd 3 4) (fun _ _ => (1 / 2 : ℝ)) (fun _ _ => rfl) (fun _ => (0 : Zd 3 4)) {0, Pi.single 0 1}
  refine this.trans ?_
  rw [lwAuxRoot_auxValOn_const]
  change ((({0, Pi.single 0 1} : Finset (Zd 3 4)).card : ℝ)) ^ localReg2_inst_Q.nM *
    (1 / 2 : ℝ) ^ localReg2_inst_Q.molSolid.length = 1 / 8
  rw [auxGraph_inst_Q_molSolid, auxGraph_inst_Q_counters.2.2.2, lwAuxRoot_Dm_card]
  norm_num
end Instances
end RBM.Graph
end
