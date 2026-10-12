/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Graph.BAScost
import RBM3D.Graph.BAScost2
import RBM3D.Graph.LocalRegular6d
import RBM3D.Graph.BAWeightOp
import RBM3D.Graph.BAGGOp
import RBM3D.Graph.BAExpandW
import RBM3D.Graph.BASim3

set_option linter.style.header false
set_option linter.style.setOption false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.flexible false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false
set_option linter.style.show false
set_option linter.unusedSimpArgs false

/-!
# BA-L L3b4'' `BAShapeO2`, part 1: the stage-1 builder lemmas `BAScostLL Γ X` (T2447)

Paper: arXiv:2507.20274, `paper/tex/B_graphical_lemmas.tex` (`lanlw`, `lem_lweight`, `GGGamma`).  The builder terms of the tagged frame step that carry
`e2` or `macroB` at stage 1 (T2443 `docs/reports/T2443-prove.md:38`) each satisfy the local lemma `BAScostLL Γ X` at a general normal BA graph,
under the hypotheses of their constructor (`weight`, `within`, `edge`, `gg`, `ggSplit` of `BAFrameStepT`, `BASim:138-161`).  Every proof is the
reduction `BAScostLL_of_band` (`BAScost:617`) to a band local lemma on the atomic image `(promoteC Γ).merge`, as `BAScostLL_S1`, `BAScostLL_lanlwT1`,
`BAScostLL_macroA`, `BAScostLL_macroB` (`BAScost`).

## Contents (namespace `RBM.Graph`; helpers carry the stem `BAShapeO2_`)

1. Tools: the comparison of solid lists `BAShapeO2_Up_of_forall2`, the driver `BAShapeO2_driver` (the vertex map `ψ`, the band term `Λ` and the solid-list comparison) with its three
   instances `BAShapeO2_driver1` (`ψ = BAScost_psi1`), `BAShapeO2_driver2` (the four-vertex map `BAShapeO2_psi2`, its kernel `BAShapeO2_ker_psi2`) and `BAShapeO2_driver0`
   (`ψ = vmap ∘ BAScost_rho2`, no fresh band vertex).
2. The weight terms: `lanlwD` (`Dmove`), the `lw2` head and the `within` head (`Loop`), the `lw4` head (`T2`) and tail (`T4`).
3. The `GGGamma` terms: `gg2` heads `A2`, `A3` (`Contract`), `A4` (`Loop`), `A5` (`R5`) and tail `AD` (`R7`), `gg4` heads `B1` (`R4`), `B2` (`R6`) and tail `BD` (`R8`).
4. The `ggSplit` terms `d1` (`R5`), `d2`-`d4` (`Contract`).
5. The term lists `BAShapeO2_lw2`, `_lw4`, `_within`, `_gg2`, `_gg4` (with `A1` = `BAScostLL_S1`).
6. Compiled instances at the R1 witnesses `baPW`, `baPB`, `baPE`, `baPA`, `baPC` (`BASim3:1877-1905`).
-/

noncomputable section

namespace RBM.Graph

/-! ## 1. Tools -/

section Tools

variable {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

/-- a componentwise comparison of two solid lists gives the relation `BAScost_Up` -/
theorem BAShapeO2_Up_of_forall2 {V : Type} (s : Setoid V) {l l' : List (SEdge V)}
    (h : List.Forall₂ (fun e e' => e'.σ = e.σ ∧ e'.src = e.src ∧ e'.dst = e.dst ∧ (e.circ = true → e'.circ = true)) l l') :
    BAScost_Up s l l' := by
  induction h with
  | nil => exact BAScost_Up.refl s []
  | cons h _ ih => exact BAScost_Up.cons s _ _ ih h.1 h.2.1 h.2.2.1 h.2.2.2

/-- **The driver**: `BAScostLL_of_band` for an extension `ext k Γ rest S W md`, the band term `Λ` having, up to a permutation, the solid list of the old edges (read at the
vertex map `kap` of the atomic image) followed by the list `sB`, and `hnew` the comparison of `sB` with the new edges of the extension read at `ψ`. -/
theorem BAShapeO2_driver {k : ℕ} {J : Type} [Fintype J] [DecidableEq J] (Γ : BAGraph E I) (rest : List (SEdge (E ⊕ I)))
    (S : List (SEdge (E ⊕ (I ⊕ Fin k)))) (W : List (WEdge (E ⊕ (I ⊕ Fin k)))) (md : List (BAMEdge (E ⊕ (I ⊕ Fin k))))
    (Λ : LGraph (promoteC Γ).ExtCls J) (hLL : LGraph.ScostLL (promoteC Γ).merge Λ)
    (ψ : E ⊕ (I ⊕ Fin k) → (promoteC Γ).ExtCls ⊕ J) (hψ : Function.Surjective ψ)
    (hψl : ∀ a : E, ψ (Sum.inl a) = Sum.inl ((promoteC Γ).extMap a))
    (hker : ∀ u v, ψ u = ψ v → atomSetoid (BAGraph.ext k Γ rest S W md) u v)
    (kap : (promoteC Γ).ExtCls ⊕ (promoteC Γ).IntCls → (promoteC Γ).ExtCls ⊕ J)
    (hψkap : ∀ v, ψ (owxEmb k v) = kap ((promoteC Γ).vmap v))
    (sB : List (SEdge ((promoteC Γ).ExtCls ⊕ J)))
    (hperm : Λ.solid.Perm ((rest.map (BAScost_imgE Γ)).map (SEdge.map kap) ++ sB))
    (hnew : ∀ s'' : Setoid ((promoteC Γ).ExtCls ⊕ J), (∀ u v, atomSetoid (BAGraph.ext k Γ rest S W md) u v → s'' (ψ u) (ψ v)) → BAScost_Up s'' sB
      (S.map (fun e => (⟨e.σ, e.circ && (BAGraph.ext k Γ rest S W md).sameAtom e.src e.dst, ψ e.src, ψ e.dst⟩ : SEdge _))))
    (hW : Λ.waved.length = Γ.waved.length + W.length) :
    BAScostLL Γ (BAGraph.ext k Γ rest S W md) := by
  set Λ' : LGraph (promoteC Γ).ExtCls J := { Λ with solid := (rest.map (BAScost_imgE Γ)).map (SEdge.map kap) ++ sB } with hΛ'
  have hLL' : LGraph.ScostLL (promoteC Γ).merge Λ' := LGraph.ScostLL.of_perm _ Λ Λ' hperm rfl hLL
  refine BAScostLL_of_band Γ _ Λ' hLL' ψ hψ hψl hker ?_
  intro s'' hadm
  refine BAScost_scost_le_of_Up _ _ s'' ?_ ?_
  · rw [BAScost_ext_relabel_solid]
    change BAScost_Up s'' ((rest.map (BAScost_imgE Γ)).map (SEdge.map kap) ++ sB) _
    rw [List.map_map]
    exact BAScost_Up.append s'' (BAScost_Up_old (k := k) Γ rest S W md ψ kap hψkap s'') (hnew s'' hadm)
  · rw [BAScost_ext_relabel_waved_length]
    exact hW

/-- the driver for the vertex map `ψ = BAScost_psi1 Γ a` (`α ↦` the atom of `a`, `β ↦` the fresh band vertex): the kernel is inside the atoms by `BAScost_ker_psi1` -/
theorem BAShapeO2_driver1 (Γ : BAGraph E I) (a : E ⊕ I) (rest : List (SEdge (E ⊕ I)))
    (S : List (SEdge (E ⊕ (I ⊕ Fin 2)))) (W : List (WEdge (E ⊕ (I ⊕ Fin 2)))) (md : List (BAMEdge (E ⊕ (I ⊕ Fin 2))))
    (hα : atomSetoid (BAGraph.ext 2 Γ rest S W md) (bpv 0) (owxEmb 2 a))
    (Λ : LGraph (promoteC Γ).ExtCls ((promoteC Γ).IntCls ⊕ Fin 1)) (hLL : LGraph.ScostLL (promoteC Γ).merge Λ)
    (sB : List (SEdge ((promoteC Γ).ExtCls ⊕ ((promoteC Γ).IntCls ⊕ Fin 1))))
    (hperm : Λ.solid.Perm ((rest.map (BAScost_imgE Γ)).map (SEdge.map (owxEmb 1)) ++ sB))
    (hnew : ∀ s'' : Setoid ((promoteC Γ).ExtCls ⊕ ((promoteC Γ).IntCls ⊕ Fin 1)),
      (∀ u v, atomSetoid (BAGraph.ext 2 Γ rest S W md) u v → s'' (BAScost_psi1 Γ a u) (BAScost_psi1 Γ a v)) → BAScost_Up s'' sB
      (S.map (fun e => (⟨e.σ, e.circ && (BAGraph.ext 2 Γ rest S W md).sameAtom e.src e.dst, BAScost_psi1 Γ a e.src, BAScost_psi1 Γ a e.dst⟩ : SEdge _))))
    (hW : Λ.waved.length = Γ.waved.length + W.length) :
    BAScostLL Γ (BAGraph.ext 2 Γ rest S W md) :=
  BAShapeO2_driver Γ rest S W md Λ hLL (BAScost_psi1 Γ a) (BAScost_psi1_surj Γ a) (fun e => BAScost_psi1_inl Γ a e)
    (fun u v h => BAScost_ker_psi1 Γ a _ hα (fun u v h => BAScost_atomSetoid_ext Γ rest S W md h) u v h) (owxEmb 1)
    (fun v => BAScost_psi1_emb Γ a v) sB hperm hnew hW

/-- the image of a solid edge of a normal graph is a loop iff it is circled -/
theorem BAShapeO2_imgE_loop (Γ : BAGraph E I) (hN : Γ.Normal) {e : SEdge (E ⊕ I)} (he : e ∈ Γ.solid) :
    ((BAScost_imgE Γ e).src = (BAScost_imgE Γ e).dst ↔ (BAScost_imgE Γ e).circ = true) := by
  have hc := hN.2 e he
  simp only [BAScost_imgE, hc, Bool.true_and]
  exact BAAtomic_promoteC_vmap_eq_sameAtom Γ _ _

/-! ### The four-vertex map -/

/-- **The vertex map of an extension by `u, w, α, β = bpv 0..3`** (`lw4`, `gg4`: `u` carries `M`-dotted edges to the old vertex `a`, `w` to `α`) onto the band vertices of the atomic
image of `Γ` plus two fresh vertices: the old vertices go to their atoms, `u` to the atom of `a`, `w`, `α` to the first fresh vertex, `β` to the second. -/
def BAShapeO2_psi2 (Γ : BAGraph E I) (a : E ⊕ I) :
    E ⊕ (I ⊕ Fin 4) → (promoteC Γ).ExtCls ⊕ ((promoteC Γ).IntCls ⊕ Fin 2)
  | Sum.inl e => Sum.inl ((promoteC Γ).extMap e)
  | Sum.inr (Sum.inl i) => owxEmb 2 ((promoteC Γ).vmap (Sum.inr i))
  | Sum.inr (Sum.inr j) => if j = 0 then owxEmb 2 ((promoteC Γ).vmap a) else if j = 3 then Sum.inr (Sum.inr 1) else Sum.inr (Sum.inr 0)

theorem BAShapeO2_psi2_emb (Γ : BAGraph E I) (a v : E ⊕ I) :
    BAShapeO2_psi2 Γ a (owxEmb 4 v) = owxEmb 2 ((promoteC Γ).vmap v) := by
  rcases v with e | i
  · simp [BAShapeO2_psi2, owxEmb, BAAtomic_vmap_inl]
  · rfl

theorem BAShapeO2_psi2_zero (Γ : BAGraph E I) (a : E ⊕ I) : BAShapeO2_psi2 Γ a (bpv 0) = owxEmb 2 ((promoteC Γ).vmap a) := by
  simp [BAShapeO2_psi2]

theorem BAShapeO2_psi2_one (Γ : BAGraph E I) (a : E ⊕ I) : BAShapeO2_psi2 Γ a (bpv 1) = Sum.inr (Sum.inr 0) := by
  simp [BAShapeO2_psi2]

theorem BAShapeO2_psi2_two (Γ : BAGraph E I) (a : E ⊕ I) : BAShapeO2_psi2 Γ a (bpv 2) = Sum.inr (Sum.inr 0) := by
  simp [BAShapeO2_psi2]

theorem BAShapeO2_psi2_three (Γ : BAGraph E I) (a : E ⊕ I) : BAShapeO2_psi2 Γ a (bpv 3) = Sum.inr (Sum.inr 1) := by
  simp [BAShapeO2_psi2]

theorem BAShapeO2_psi2_inl (Γ : BAGraph E I) (a : E ⊕ I) (e : E) :
    BAShapeO2_psi2 Γ a (Sum.inl e) = Sum.inl ((promoteC Γ).extMap e) := rfl

theorem BAShapeO2_emb2_ne_fresh {Γ : BAGraph E I} (v : (promoteC Γ).ExtCls ⊕ (promoteC Γ).IntCls) (j : Fin 2) :
    (owxEmb 2 v : (promoteC Γ).ExtCls ⊕ ((promoteC Γ).IntCls ⊕ Fin 2)) ≠ Sum.inr (Sum.inr j) := by
  rcases v with a | i <;> simp [owxEmb]

theorem BAShapeO2_psi2_surj (Γ : BAGraph E I) (a : E ⊕ I) : Function.Surjective (BAShapeO2_psi2 Γ a) := by
  intro w
  rcases w with e | i | j
  · obtain ⟨v₀, hv₀⟩ := BAAtomic_vmap_surjective (promoteC Γ) (Sum.inl e)
    exact ⟨owxEmb 4 v₀, by rw [BAShapeO2_psi2_emb, hv₀]; rfl⟩
  · obtain ⟨v₀, hv₀⟩ := BAAtomic_vmap_surjective (promoteC Γ) (Sum.inr i)
    exact ⟨owxEmb 4 v₀, by rw [BAShapeO2_psi2_emb, hv₀]; rfl⟩
  · fin_cases j
    · exact ⟨bpv 1, BAShapeO2_psi2_one Γ a⟩
    · exact ⟨bpv 3, BAShapeO2_psi2_three Γ a⟩

/-- the kernel of `BAShapeO2_psi2` lies inside the atoms of the extension, if `u` lies in the atom of `a` and `w`, `α` in one atom -/
theorem BAShapeO2_ker_psi2 (Γ : BAGraph E I) (a : E ⊕ I) (T : BAGraph E (I ⊕ Fin 4))
    (h0 : atomSetoid T (bpv 0) (owxEmb 4 a)) (h12 : atomSetoid T (bpv 1) (bpv 2))
    (hmono : ∀ u v, atomSetoid Γ u v → atomSetoid T (owxEmb 4 u) (owxEmb 4 v))
    (u v : E ⊕ (I ⊕ Fin 4)) (h : BAShapeO2_psi2 Γ a u = BAShapeO2_psi2 Γ a v) : atomSetoid T u v := by
  let rt : E ⊕ (I ⊕ Fin 4) → E ⊕ (I ⊕ Fin 4) := fun w =>
    match w with
    | Sum.inr (Sum.inr j) => if j = 0 then owxEmb 4 a else if j = 2 then bpv 1 else w
    | _ => w
  have hrt : ∀ w, atomSetoid T w (rt w) := by
    intro w
    rcases w with e | i | j
    · exact (atomSetoid _).refl' _
    · exact (atomSetoid _).refl' _
    · fin_cases j
      · exact h0
      · exact (atomSetoid _).refl' _
      · exact (atomSetoid _).symm h12
      · exact (atomSetoid _).refl' _
  have hψrt : ∀ w, BAShapeO2_psi2 Γ a (rt w) = BAShapeO2_psi2 Γ a w := by
    intro w
    rcases w with e | i | j
    · rfl
    · rfl
    · fin_cases j
      · show BAShapeO2_psi2 Γ a (owxEmb 4 a) = BAShapeO2_psi2 Γ a (bpv 0)
        rw [BAShapeO2_psi2_emb, BAShapeO2_psi2_zero]
      · rfl
      · show BAShapeO2_psi2 Γ a (bpv 1) = BAShapeO2_psi2 Γ a (bpv 2)
        rw [BAShapeO2_psi2_one, BAShapeO2_psi2_two]
      · rfl
  have hold : ∀ w, (∃ v₀, rt w = owxEmb 4 v₀) ∨ rt w = bpv 1 ∨ rt w = bpv 3 := by
    intro w
    rcases w with e | i | j
    · exact Or.inl ⟨Sum.inl e, rfl⟩
    · exact Or.inl ⟨Sum.inr i, rfl⟩
    · fin_cases j
      · exact Or.inl ⟨a, rfl⟩
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr rfl)
  have h' : BAShapeO2_psi2 Γ a (rt u) = BAShapeO2_psi2 Γ a (rt v) := by rw [hψrt, hψrt]; exact h
  refine (atomSetoid _).trans (hrt u) ((atomSetoid _).trans ?_ ((atomSetoid _).symm (hrt v)))
  rcases hold u with ⟨u₀, hu⟩ | hu | hu <;> rcases hold v with ⟨v₀, hv⟩ | hv | hv
  · rw [hu, hv] at h' ⊢
    rw [BAShapeO2_psi2_emb, BAShapeO2_psi2_emb] at h'
    have := BAScost_owxEmb_inj 2 h'
    exact hmono _ _ ((BAAtomic_atomSetoid_iff Γ _ _).2 ((BAAtomic_promoteC_vmap_eq_atom Γ _ _).1 this))
  · rw [hu, hv] at h'
    rw [BAShapeO2_psi2_emb, BAShapeO2_psi2_one] at h'
    exact absurd h' (BAShapeO2_emb2_ne_fresh _ 0)
  · rw [hu, hv] at h'
    rw [BAShapeO2_psi2_emb, BAShapeO2_psi2_three] at h'
    exact absurd h' (BAShapeO2_emb2_ne_fresh _ 1)
  · rw [hu, hv] at h'
    rw [BAShapeO2_psi2_emb, BAShapeO2_psi2_one] at h'
    exact absurd h'.symm (BAShapeO2_emb2_ne_fresh _ 0)
  · rw [hu, hv]
  · rw [hu, hv] at h'
    rw [BAShapeO2_psi2_one, BAShapeO2_psi2_three] at h'
    exact absurd h' (by simp)
  · rw [hu, hv] at h'
    rw [BAShapeO2_psi2_emb, BAShapeO2_psi2_three] at h'
    exact absurd h'.symm (BAShapeO2_emb2_ne_fresh _ 1)
  · rw [hu, hv] at h'
    rw [BAShapeO2_psi2_one, BAShapeO2_psi2_three] at h'
    exact absurd h'.symm (by simp)
  · rw [hu, hv]

/-- the driver for the vertex map `ψ = BAShapeO2_psi2 Γ a` -/
theorem BAShapeO2_driver2 (Γ : BAGraph E I) (a : E ⊕ I) (rest : List (SEdge (E ⊕ I)))
    (S : List (SEdge (E ⊕ (I ⊕ Fin 4)))) (W : List (WEdge (E ⊕ (I ⊕ Fin 4)))) (md : List (BAMEdge (E ⊕ (I ⊕ Fin 4))))
    (h0 : atomSetoid (BAGraph.ext 4 Γ rest S W md) (bpv 0) (owxEmb 4 a))
    (h12 : atomSetoid (BAGraph.ext 4 Γ rest S W md) (bpv 1) (bpv 2))
    (Λ : LGraph (promoteC Γ).ExtCls ((promoteC Γ).IntCls ⊕ Fin 2)) (hLL : LGraph.ScostLL (promoteC Γ).merge Λ)
    (sB : List (SEdge ((promoteC Γ).ExtCls ⊕ ((promoteC Γ).IntCls ⊕ Fin 2))))
    (hperm : Λ.solid.Perm ((rest.map (BAScost_imgE Γ)).map (SEdge.map (owxEmb 2)) ++ sB))
    (hnew : ∀ s'' : Setoid ((promoteC Γ).ExtCls ⊕ ((promoteC Γ).IntCls ⊕ Fin 2)),
      (∀ u v, atomSetoid (BAGraph.ext 4 Γ rest S W md) u v → s'' (BAShapeO2_psi2 Γ a u) (BAShapeO2_psi2 Γ a v)) → BAScost_Up s'' sB
      (S.map (fun e => (⟨e.σ, e.circ && (BAGraph.ext 4 Γ rest S W md).sameAtom e.src e.dst, BAShapeO2_psi2 Γ a e.src, BAShapeO2_psi2 Γ a e.dst⟩ : SEdge _))))
    (hW : Λ.waved.length = Γ.waved.length + W.length) :
    BAScostLL Γ (BAGraph.ext 4 Γ rest S W md) :=
  BAShapeO2_driver Γ rest S W md Λ hLL (BAShapeO2_psi2 Γ a) (BAShapeO2_psi2_surj Γ a) (fun e => BAShapeO2_psi2_inl Γ a e)
    (fun u v h => BAShapeO2_ker_psi2 Γ a _ h0 h12 (fun u v h => BAScost_atomSetoid_ext Γ rest S W md h) u v h) (owxEmb 2)
    (fun v => BAShapeO2_psi2_emb Γ a v) sB hperm hnew hW

/-- the driver for the vertex map `ψ = vmap ∘ rho2` (no fresh band vertex: `Contract`): `α`, `β` go to the atoms of `x₀`, `x₁` -/
theorem BAShapeO2_driver0 (Γ : BAGraph E I) (x₀ x₁ : E ⊕ I) (rest : List (SEdge (E ⊕ I)))
    (S : List (SEdge (E ⊕ (I ⊕ Fin 2)))) (W : List (WEdge (E ⊕ (I ⊕ Fin 2)))) (md : List (BAMEdge (E ⊕ (I ⊕ Fin 2))))
    (h0 : atomSetoid (BAGraph.ext 2 Γ rest S W md) (bpv 0) (owxEmb 2 x₀))
    (h1 : atomSetoid (BAGraph.ext 2 Γ rest S W md) (bpv 1) (owxEmb 2 x₁))
    (Λ : LGraph (promoteC Γ).ExtCls (promoteC Γ).IntCls) (hLL : LGraph.ScostLL (promoteC Γ).merge Λ)
    (sB : List (SEdge ((promoteC Γ).ExtCls ⊕ (promoteC Γ).IntCls)))
    (hperm : Λ.solid.Perm ((rest.map (BAScost_imgE Γ)).map (SEdge.map id) ++ sB))
    (hnew : ∀ s'' : Setoid ((promoteC Γ).ExtCls ⊕ (promoteC Γ).IntCls),
      (∀ u v, atomSetoid (BAGraph.ext 2 Γ rest S W md) u v →
        s'' (((promoteC Γ).vmap ∘ BAScost_rho2 x₀ x₁) u) (((promoteC Γ).vmap ∘ BAScost_rho2 x₀ x₁) v)) → BAScost_Up s'' sB
      (S.map (fun e => (⟨e.σ, e.circ && (BAGraph.ext 2 Γ rest S W md).sameAtom e.src e.dst, ((promoteC Γ).vmap ∘ BAScost_rho2 x₀ x₁) e.src,
        ((promoteC Γ).vmap ∘ BAScost_rho2 x₀ x₁) e.dst⟩ : SEdge _))))
    (hW : Λ.waved.length = Γ.waved.length + W.length) :
    BAScostLL Γ (BAGraph.ext 2 Γ rest S W md) := by
  have hrt : ∀ w, atomSetoid (BAGraph.ext 2 Γ rest S W md) w (owxEmb 2 (BAScost_rho2 x₀ x₁ w)) := by
    intro w
    rcases w with e | i | j
    · exact (atomSetoid _).refl' _
    · exact (atomSetoid _).refl' _
    · fin_cases j
      · exact h0
      · exact h1
  refine BAShapeO2_driver Γ rest S W md Λ hLL ((promoteC Γ).vmap ∘ BAScost_rho2 x₀ x₁)
    ((BAAtomic_vmap_surjective _).comp (fun v => ⟨owxEmb 2 v, BAScost_rho2_emb _ _ v⟩)) (fun a => BAAtomic_vmap_inl (promoteC Γ) a)
    (fun u v h => BAScost_ker_ext Γ rest S W md (BAScost_rho2 x₀ x₁) hrt u v h) id (fun v => by simp [BAScost_rho2_emb]) sB hperm hnew hW

theorem BAShapeO2_rho2_zero (x y : E ⊕ I) : BAScost_rho2 x y (bpv 0) = x := by simp [BAScost_rho2, bpv]

theorem BAShapeO2_rho2_one (x y : E ⊕ I) : BAScost_rho2 x y (bpv 1) = y := by simp [BAScost_rho2, bpv]

/-- from `intAtom` to an internal class -/
theorem BAShapeO2_vmap_inr (Γ : BAGraph E I) {u : E ⊕ I} (h : Γ.intAtom u = true) :
    ∃ x : (promoteC Γ).IntCls, (promoteC Γ).vmap u = Sum.inr x := by
  have := (BAAtomic_promoteC_vmap_isRight Γ u).2 h
  rcases hv : (promoteC Γ).vmap u with a | x
  · rw [hv] at this; simp at this
  · exact ⟨x, rfl⟩

theorem BAShapeO2_map_id {V : Type} (l : List (SEdge V)) : l.map (SEdge.map id) = l := by
  induction l with
  | nil => rfl
  | cons e l ih => rw [List.map_cons, ih]; rfl

/-- the image of a blue circled edge between two distinct atoms of a graph -/
theorem BAShapeO2_imgE_wf (Γ : BAGraph E I) {e : SEdge (E ⊕ I)} (h1 : e.σ = true) (h2 : e.circ = true) (hwf : Γ.sameAtom e.src e.dst = false) :
    BAScost_imgE Γ e = ⟨true, false, (promoteC Γ).vmap e.src, (promoteC Γ).vmap e.dst⟩ := by
  simp [BAScost_imgE, h1, h2, hwf]


/-- rotate a block of the front to the back -/
theorem BAShapeO2_perm_rot {α : Type} (A R T : List α) : ((A ++ R) ++ T).Perm (R ++ (T ++ A)) := by
  rw [List.append_assoc]
  exact (List.perm_append_comm (l₁ := A) (l₂ := R ++ T)).trans (List.Perm.of_eq (by simp))

end Tools

/-! ## 2. The weight terms -/

section Weight

variable {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

/-- **`lanlwD`** (the derivative term of `lanlw`, the tail of `lw2`, of the `within` stage 1, of `edge`, of `ggSplit`; `BAExpandW:133`): the band's `Dmove` (`scostLL_dmove`,
`LocalRegular6c:1431`) at `z = [x]`, `v = [y]`, with `cp = ([x] = [y])`; the vertex map is `BAScost_psi1` at `x`. -/
theorem BAShapeO2_lanlwD (Γ : BAGraph E I) (hN : Γ.Normal) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid)
    (hp1 : p.1.σ = true ∧ p.1.circ = true) (q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hq : q ∈ lwSplit p.2) :
    BAScostLL Γ (BAGraph.lanlwD Γ p q) := by
  classical
  have hD : BAGraph.lanlwD Γ p q = BAGraph.ext 2 Γ q.2 [(owxDE (bpv 1) (bpv 0) (SEdge.map (owxEmb 2) q.1)).1,
      (owxDE (bpv 1) (bpv 0) (SEdge.map (owxEmb 2) q.1)).2, bpS false (bpv 1) (owxEmb 2 p.1.dst)] [bpW false (bpv 0) (bpv 1)]
      [bpM (owxEmb 2 p.1.src) (bpv 0)] := rfl
  rw [hD]
  have hperm0 : Γ.solid.Perm (p.1 :: q.1 :: q.2) := (lwSplit_perm Γ.solid p hp).trans ((lwSplit_perm p.2 q hq).cons p.1)
  have hq1 : q.1 ∈ Γ.solid := hperm0.symm.subset (by simp)
  have hperm : (promoteC Γ).merge.solid.Perm (⟨true, Γ.sameAtom p.1.src p.1.dst, (promoteC Γ).vmap p.1.src, (promoteC Γ).vmap p.1.dst⟩ ::
      BAScost_imgE Γ q.1 :: q.2.map (BAScost_imgE Γ)) := by
    rw [BAScost_img_solid]
    have e1 : BAScost_imgE Γ p.1 = ⟨true, Γ.sameAtom p.1.src p.1.dst, (promoteC Γ).vmap p.1.src, (promoteC Γ).vmap p.1.dst⟩ := by
      simp [BAScost_imgE, hp1.1, hp1.2]
    have h4 := hperm0.map (BAScost_imgE Γ)
    rw [List.map_cons, List.map_cons, e1] at h4
    exact h4
  have hLL := scostLL_dmove (promoteC Γ).merge (q.2.map (BAScost_imgE Γ)) ((promoteC Γ).vmap p.1.src) ((promoteC Γ).vmap p.1.dst)
    (Γ.sameAtom p.1.src p.1.dst) (BAScost_imgE Γ q.1) (BAAtomic_promoteC_vmap_eq_sameAtom Γ _ _) (BAShapeO2_imgE_loop Γ hN hq1) hperm
  have hmdx : atomSetoid (BAGraph.ext 2 Γ q.2 [(owxDE (bpv 1) (bpv 0) (SEdge.map (owxEmb 2) q.1)).1,
      (owxDE (bpv 1) (bpv 0) (SEdge.map (owxEmb 2) q.1)).2, bpS false (bpv 1) (owxEmb 2 p.1.dst)] [bpW false (bpv 0) (bpv 1)]
      [bpM (owxEmb 2 p.1.src) (bpv 0)]) (owxEmb 2 p.1.src) (bpv 0) :=
    BAScost_atomSetoid_ext_md Γ q.2 _ _ _ (bpM (owxEmb 2 p.1.src) (bpv 0)) (by simp)
  refine BAShapeO2_driver1 Γ p.1.src q.2 _ _ _ ((atomSetoid _).symm hmdx) _ hLL
    [(owxDE (Sum.inr (Sum.inr 0)) (owxEmb 1 ((promoteC Γ).vmap p.1.src)) (SEdge.map (owxEmb 1) (BAScost_imgE Γ q.1))).1,
      (owxDE (Sum.inr (Sum.inr 0)) (owxEmb 1 ((promoteC Γ).vmap p.1.src)) (SEdge.map (owxEmb 1) (BAScost_imgE Γ q.1))).2,
      ⟨true, false, Sum.inr (Sum.inr 0), owxEmb 1 ((promoteC Γ).vmap p.1.dst)⟩] (List.Perm.refl _) ?_ ?_
  · intro s'' _
    refine BAShapeO2_Up_of_forall2 s'' ?_
    cases hσ : q.1.σ <;>
      simp [owxDE, SEdge.map, BAScost_imgE, hσ, BAScost_psi1_emb, BAScost_psi1_alpha, BAScost_psi1_beta, bpS, bpv]
  · simp [lwPrimDmove, LGraph.owxExt, BAScost_img_waved_length]

/-- from the atom relation of a graph to its Boolean `sameAtom` -/
theorem BAShapeO2_sameAtom_of_atomSetoid {E' I' : Type} [Fintype E'] [DecidableEq E'] [Fintype I'] [DecidableEq I'] (T : BAGraph E' I') {u v : E' ⊕ I'}
    (h : atomSetoid T u v) : T.sameAtom u v = true :=
  (T.BAAtomic_sameAtom_iff u v).2 ((BAAtomic_atomSetoid_iff T u v).1 h)

/-- **The head loop** (`lw2` head with `p.1` a loop, `within` head with `[x] = [y]`; `BAWeightOp:69`, `BASim:122`): the image of `p.1` is the circled loop at `[x]`, the band's `Loop([x])`
(`scostLL_loop`, `localReg6d_ll_T1`); the extension has the loop `Ǧ_{αy}` at `[x]` (circled in the atomic image) and `Ǧ_{ββ}` at the fresh vertex.  `hsame` replaces `src = dst`. -/
theorem BAShapeO2_withinHead (Γ : BAGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid)
    (hp1 : p.1.σ = true ∧ p.1.circ = true) (hsame : Γ.sameAtom p.1.src p.1.dst = true) :
    BAScostLL Γ (BAGraph.ext 2 Γ p.2 [bpS true (bpv 1) (bpv 1), bpS true (bpv 0) (owxEmb 2 p.1.dst)] [bpW false (bpv 0) (bpv 1)]
      [bpM (owxEmb 2 p.1.src) (bpv 0)]) := by
  classical
  have hvv : (promoteC Γ).vmap p.1.src = (promoteC Γ).vmap p.1.dst := (BAAtomic_promoteC_vmap_eq_sameAtom Γ _ _).2 hsame
  have e1 : BAScost_imgE Γ p.1 = ⟨true, true, (promoteC Γ).vmap p.1.src, (promoteC Γ).vmap p.1.src⟩ := by
    simp [BAScost_imgE, hp1.1, hp1.2, hsame, hvv]
  have hperm0 : Γ.solid.Perm (p.1 :: p.2) := lwSplit_perm Γ.solid p hp
  have hmdx : atomSetoid (BAGraph.ext 2 Γ p.2 [bpS true (bpv 1) (bpv 1), bpS true (bpv 0) (owxEmb 2 p.1.dst)] [bpW false (bpv 0) (bpv 1)]
      [bpM (owxEmb 2 p.1.src) (bpv 0)]) (owxEmb 2 p.1.src) (bpv 0) :=
    BAScost_atomSetoid_ext_md Γ p.2 _ _ _ (bpM (owxEmb 2 p.1.src) (bpv 0)) (by simp)
  have hxy : atomSetoid (BAGraph.ext 2 Γ p.2 [bpS true (bpv 1) (bpv 1), bpS true (bpv 0) (owxEmb 2 p.1.dst)] [bpW false (bpv 0) (bpv 1)]
      [bpM (owxEmb 2 p.1.src) (bpv 0)]) (bpv 0) (owxEmb 2 p.1.dst) :=
    (atomSetoid _).trans ((atomSetoid _).symm hmdx) (BAScost_atomSetoid_ext Γ p.2 _ _ _
      ((BAAtomic_atomSetoid_iff Γ _ _).2 ((Γ.BAAtomic_sameAtom_iff _ _).1 hsame)))
  refine BAShapeO2_driver1 Γ p.1.src p.2 _ _ _ ((atomSetoid _).symm hmdx) (lwPrimLoop (promoteC Γ).merge ((promoteC Γ).vmap p.1.src) true)
    (scostLL_loop (promoteC Γ).merge ((promoteC Γ).vmap p.1.src) true)
    [⟨true, true, Sum.inr (Sum.inr 0), Sum.inr (Sum.inr 0)⟩, ⟨true, true, owxEmb 1 ((promoteC Γ).vmap p.1.src), owxEmb 1 ((promoteC Γ).vmap p.1.src)⟩]
    ?_ ?_ ?_
  · -- the solid lists
    rw [BAScost_lwPrimLoop_solid, BAScost_img_solid, List.map_map, List.map_map]
    refine ((hperm0.map (SEdge.map (owxEmb 1) ∘ BAScost_imgE Γ)).append_right _).trans ?_
    simp only [List.map_cons, Function.comp_apply, e1, SEdge.map]
    exact ((List.perm_append_singleton _ _).symm).trans (List.Perm.of_eq (by simp))
  · intro s'' _
    refine BAShapeO2_Up_of_forall2 s'' ?_
    simp only [List.map_cons, List.map_nil, List.forall₂_cons, List.forall₂_nil_left_iff, and_true]
    refine ⟨⟨rfl, ?_, ?_, fun _ => ?_⟩, rfl, ?_, ?_, fun _ => ?_⟩
    · simp [bpS, BAScost_psi1_beta, bpv]
    · simp [bpS, BAScost_psi1_beta, bpv]
    · simp [bpS, BAScost_sameAtom_self]
    · simp [bpS, BAScost_psi1_alpha]
    · simp [bpS, BAScost_psi1_emb, hvv]
    · exact BAShapeO2_sameAtom_of_atomSetoid _ hxy
  · simp [lwPrimLoop, LGraph.owxExt, BAScost_img_waved_length]

/-- **`lw2` head** (`BAWeightOp:69`; the solid edges of the `within` head in the other order): `p.1` a blue circled loop, so `[x] = [y]` and the term is the band's `Loop([x])` again. -/
theorem BAShapeO2_lw2Head (Γ : BAGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid)
    (hp1 : p.1.σ = true ∧ p.1.circ = true ∧ p.1.src = p.1.dst) :
    BAScostLL Γ (BAGraph.ext 2 Γ p.2 [bpS true (bpv 0) (owxEmb 2 p.1.dst), bpS true (bpv 1) (bpv 1)] [bpW false (bpv 0) (bpv 1)]
      [bpM (owxEmb 2 p.1.src) (bpv 0)]) := by
  classical
  have hsame : Γ.sameAtom p.1.src p.1.dst = true := by rw [hp1.2.2]; exact BAScost_sameAtom_self Γ _
  have hvv : (promoteC Γ).vmap p.1.src = (promoteC Γ).vmap p.1.dst := (BAAtomic_promoteC_vmap_eq_sameAtom Γ _ _).2 hsame
  have e1 : BAScost_imgE Γ p.1 = ⟨true, true, (promoteC Γ).vmap p.1.src, (promoteC Γ).vmap p.1.src⟩ := by
    simp [BAScost_imgE, hp1.1, hp1.2.1, hsame, hvv]
  have hperm0 : Γ.solid.Perm (p.1 :: p.2) := lwSplit_perm Γ.solid p hp
  have hmdx : atomSetoid (BAGraph.ext 2 Γ p.2 [bpS true (bpv 0) (owxEmb 2 p.1.dst), bpS true (bpv 1) (bpv 1)] [bpW false (bpv 0) (bpv 1)]
      [bpM (owxEmb 2 p.1.src) (bpv 0)]) (owxEmb 2 p.1.src) (bpv 0) :=
    BAScost_atomSetoid_ext_md Γ p.2 _ _ _ (bpM (owxEmb 2 p.1.src) (bpv 0)) (by simp)
  have hxy : atomSetoid (BAGraph.ext 2 Γ p.2 [bpS true (bpv 0) (owxEmb 2 p.1.dst), bpS true (bpv 1) (bpv 1)] [bpW false (bpv 0) (bpv 1)]
      [bpM (owxEmb 2 p.1.src) (bpv 0)]) (bpv 0) (owxEmb 2 p.1.dst) :=
    (atomSetoid _).trans ((atomSetoid _).symm hmdx) (BAScost_atomSetoid_ext Γ p.2 _ _ _
      ((BAAtomic_atomSetoid_iff Γ _ _).2 ((Γ.BAAtomic_sameAtom_iff _ _).1 hsame)))
  refine BAShapeO2_driver1 Γ p.1.src p.2 _ _ _ ((atomSetoid _).symm hmdx) (lwPrimLoop (promoteC Γ).merge ((promoteC Γ).vmap p.1.src) true)
    (scostLL_loop (promoteC Γ).merge ((promoteC Γ).vmap p.1.src) true)
    [⟨true, true, owxEmb 1 ((promoteC Γ).vmap p.1.src), owxEmb 1 ((promoteC Γ).vmap p.1.src)⟩, ⟨true, true, Sum.inr (Sum.inr 0), Sum.inr (Sum.inr 0)⟩]
    ?_ ?_ ?_
  · rw [BAScost_lwPrimLoop_solid, BAScost_img_solid, List.map_map, List.map_map]
    refine ((hperm0.map (SEdge.map (owxEmb 1) ∘ BAScost_imgE Γ)).append_right _).trans ?_
    simp only [List.map_cons, Function.comp_apply, e1, SEdge.map]
    exact (((List.perm_append_singleton _ _).symm).append_right _).trans (List.Perm.of_eq (by simp))
  · intro s'' _
    refine BAShapeO2_Up_of_forall2 s'' ?_
    simp only [List.map_cons, List.map_nil, List.forall₂_cons, List.forall₂_nil_left_iff, and_true]
    refine ⟨⟨rfl, ?_, ?_, fun _ => ?_⟩, rfl, ?_, ?_, fun _ => ?_⟩
    · simp [bpS, BAScost_psi1_alpha]
    · simp [bpS, BAScost_psi1_emb, hvv]
    · exact BAShapeO2_sameAtom_of_atomSetoid _ hxy
    · simp [bpS, BAScost_psi1_beta, bpv]
    · simp [bpS, BAScost_psi1_beta, bpv]
    · simp [bpS, BAScost_sameAtom_self]
  · simp [lwPrimLoop, LGraph.owxExt, BAScost_img_waved_length]

/-- **`lw4` head** (`BAWeightOp:74`): `p.1` a blue circled loop; the atoms of the term are `{x, u}`, `{w, α}`, `{β}`, and the image is the band's `T2` = `MoveLoop([x])` then `Loop(α)`
(`localReg6d_ll_T2`, `LocalRegular6d:270`); the vertex map is `BAShapeO2_psi2` at `x`. -/
theorem BAShapeO2_lw4Head (Γ : BAGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid)
    (hp1 : p.1.σ = true ∧ p.1.circ = true ∧ p.1.src = p.1.dst) :
    BAScostLL Γ (BAGraph.ext 4 Γ p.2 [bpS true (bpv 2) (bpv 1), bpS true (bpv 3) (bpv 3)]
      [bpW true (bpv 0) (bpv 1), bpW false (bpv 2) (bpv 3)]
      [bpM (owxEmb 4 p.1.src) (bpv 0), bpM (bpv 0) (owxEmb 4 p.1.src), bpM (bpv 1) (bpv 2)]) := by
  classical
  have hsame : Γ.sameAtom p.1.src p.1.dst = true := by rw [hp1.2.2]; exact BAScost_sameAtom_self Γ _
  have hvv : (promoteC Γ).vmap p.1.src = (promoteC Γ).vmap p.1.dst := (BAAtomic_promoteC_vmap_eq_sameAtom Γ _ _).2 hsame
  have e1 : BAScost_imgE Γ p.1 = ⟨true, true, (promoteC Γ).vmap p.1.src, (promoteC Γ).vmap p.1.src⟩ := by
    simp [BAScost_imgE, hp1.1, hp1.2.1, hsame, hvv]
  have hperm0 : Γ.solid.Perm (p.1 :: p.2) := lwSplit_perm Γ.solid p hp
  have hperm : (promoteC Γ).merge.solid.Perm (⟨true, true, (promoteC Γ).vmap p.1.src, (promoteC Γ).vmap p.1.src⟩ :: p.2.map (BAScost_imgE Γ)) := by
    rw [BAScost_img_solid]
    have h4 := hperm0.map (BAScost_imgE Γ)
    rw [List.map_cons, e1] at h4
    exact h4
  have hLL := localReg6d_ll_T2 1 (promoteC Γ).merge (BAScost_imgE Γ p.1, p.2.map (BAScost_imgE Γ)) ((promoteC Γ).vmap p.1.src) hperm
  have hmd : ∀ m ∈ [bpM (owxEmb 4 p.1.src) (bpv 0), bpM (bpv 0) (owxEmb 4 p.1.src), bpM (bpv 1) (bpv 2)],
      atomSetoid (BAGraph.ext 4 Γ p.2 [bpS true (bpv 2) (bpv 1), bpS true (bpv 3) (bpv 3)]
        [bpW true (bpv 0) (bpv 1), bpW false (bpv 2) (bpv 3)]
        [bpM (owxEmb 4 p.1.src) (bpv 0), bpM (bpv 0) (owxEmb 4 p.1.src), bpM (bpv 1) (bpv 2)]) m.x m.y :=
    fun m hm => BAScost_atomSetoid_ext_md Γ p.2 _ _ _ m hm
  have h12 := hmd (bpM (bpv 1) (bpv 2)) (by simp)
  refine BAShapeO2_driver2 Γ p.1.src p.2 _ _ _ (hmd (bpM (bpv 0) (owxEmb 4 p.1.src)) (by simp)) h12
    (owxET2 1 (promoteC Γ).merge (BAScost_imgE Γ p.1, p.2.map (BAScost_imgE Γ)) ((promoteC Γ).vmap p.1.src)) hLL
    [⟨true, true, Sum.inr (Sum.inr 0), Sum.inr (Sum.inr 0)⟩, ⟨true, true, Sum.inr (Sum.inr 1), Sum.inr (Sum.inr 1)⟩] (List.Perm.refl _) ?_ ?_
  · intro s'' _
    refine BAShapeO2_Up_of_forall2 s'' ?_
    simp only [List.map_cons, List.map_nil, List.forall₂_cons, List.forall₂_nil_left_iff, and_true]
    refine ⟨⟨rfl, ?_, ?_, fun _ => ?_⟩, rfl, ?_, ?_, fun _ => ?_⟩
    · simp [bpS, BAShapeO2_psi2_two]
    · simp [bpS, BAShapeO2_psi2_one]
    · exact BAShapeO2_sameAtom_of_atomSetoid _ ((atomSetoid _).symm h12)
    · simp [bpS, BAShapeO2_psi2_three]
    · simp [bpS, BAShapeO2_psi2_three]
    · simp [bpS, BAScost_sameAtom_self]
  · simp [owxET2, LGraph.owxExt, BAScost_img_waved_length]

/-- **`lw4` tail** (`BAWeightOp:75`, the derivative terms at the solid edges `q.1` of `f`): the band's `T4` = `MoveLoop([x])` then `Dmove(α; q)` (`localReg6d_ll_T4`, `:315`). -/
theorem BAShapeO2_lw4Tail (Γ : BAGraph E I) (hN : Γ.Normal) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid)
    (hp1 : p.1.σ = true ∧ p.1.circ = true ∧ p.1.src = p.1.dst) (q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hq : q ∈ lwSplit p.2) :
    BAScostLL Γ (BAGraph.ext 4 Γ q.2 [(owxDE (bpv 3) (bpv 2) (SEdge.map (owxEmb 4) q.1)).1, (owxDE (bpv 3) (bpv 2) (SEdge.map (owxEmb 4) q.1)).2,
      bpS false (bpv 3) (bpv 1)] [bpW true (bpv 0) (bpv 1), bpW false (bpv 2) (bpv 3)]
      [bpM (owxEmb 4 p.1.src) (bpv 0), bpM (bpv 0) (owxEmb 4 p.1.src), bpM (bpv 1) (bpv 2)]) := by
  classical
  have hsame : Γ.sameAtom p.1.src p.1.dst = true := by rw [hp1.2.2]; exact BAScost_sameAtom_self Γ _
  have hvv : (promoteC Γ).vmap p.1.src = (promoteC Γ).vmap p.1.dst := (BAAtomic_promoteC_vmap_eq_sameAtom Γ _ _).2 hsame
  have e1 : BAScost_imgE Γ p.1 = ⟨true, true, (promoteC Γ).vmap p.1.src, (promoteC Γ).vmap p.1.src⟩ := by
    simp [BAScost_imgE, hp1.1, hp1.2.1, hsame, hvv]
  have hperm0 : Γ.solid.Perm (p.1 :: q.1 :: q.2) := (lwSplit_perm Γ.solid p hp).trans ((lwSplit_perm p.2 q hq).cons p.1)
  have hq1 : q.1 ∈ Γ.solid := hperm0.symm.subset (by simp)
  have hperm : (promoteC Γ).merge.solid.Perm (⟨true, true, (promoteC Γ).vmap p.1.src, (promoteC Γ).vmap p.1.src⟩ ::
      BAScost_imgE Γ q.1 :: q.2.map (BAScost_imgE Γ)) := by
    rw [BAScost_img_solid]
    have h4 := hperm0.map (BAScost_imgE Γ)
    rw [List.map_cons, List.map_cons, e1] at h4
    exact h4
  have hLL := localReg6d_ll_T4 1 (promoteC Γ).merge ((promoteC Γ).vmap p.1.src) (BAScost_imgE Γ q.1, q.2.map (BAScost_imgE Γ))
    (BAShapeO2_imgE_loop Γ hN hq1) hperm
  have hmd : ∀ m ∈ [bpM (owxEmb 4 p.1.src) (bpv 0), bpM (bpv 0) (owxEmb 4 p.1.src), bpM (bpv 1) (bpv 2)],
      atomSetoid (BAGraph.ext 4 Γ q.2 [(owxDE (bpv 3) (bpv 2) (SEdge.map (owxEmb 4) q.1)).1, (owxDE (bpv 3) (bpv 2) (SEdge.map (owxEmb 4) q.1)).2,
        bpS false (bpv 3) (bpv 1)] [bpW true (bpv 0) (bpv 1), bpW false (bpv 2) (bpv 3)]
        [bpM (owxEmb 4 p.1.src) (bpv 0), bpM (bpv 0) (owxEmb 4 p.1.src), bpM (bpv 1) (bpv 2)]) m.x m.y :=
    fun m hm => BAScost_atomSetoid_ext_md Γ q.2 _ _ _ m hm
  refine BAShapeO2_driver2 Γ p.1.src q.2 _ _ _ (hmd (bpM (bpv 0) (owxEmb 4 p.1.src)) (by simp)) (hmd (bpM (bpv 1) (bpv 2)) (by simp))
    (owxET4 1 (promoteC Γ).merge ((promoteC Γ).vmap p.1.src) (BAScost_imgE Γ q.1, q.2.map (BAScost_imgE Γ))) hLL
    [(owxDE (Sum.inr (Sum.inr 1)) (Sum.inr (Sum.inr 0)) (SEdge.map (owxEmb 2) (BAScost_imgE Γ q.1))).1,
      (owxDE (Sum.inr (Sum.inr 1)) (Sum.inr (Sum.inr 0)) (SEdge.map (owxEmb 2) (BAScost_imgE Γ q.1))).2,
      ⟨true, false, Sum.inr (Sum.inr 1), Sum.inr (Sum.inr 0)⟩] (List.Perm.refl _) ?_ ?_
  · intro s'' _
    refine BAShapeO2_Up_of_forall2 s'' ?_
    cases hσ : q.1.σ <;>
      simp [owxDE, SEdge.map, BAScost_imgE, hσ, BAShapeO2_psi2_emb, BAShapeO2_psi2_one, BAShapeO2_psi2_two, BAShapeO2_psi2_three, bpS, bpv]
  · simp [owxET4, LGraph.owxExt, BAScost_img_waved_length]

end Weight

/-! ## 3. The `GGGamma` terms -/

section GG

variable {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

/-- the common data of the terms of `gg2`, `gg4` (and the `ggSplit` pair): `p.1 = Ǧ_{xy}`, `q.1 = Ǧ_{y'x}` blue circled, split off `Γ.solid` -/
theorem BAShapeO2_perm_pq (Γ : BAGraph E I) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid) (hq : q ∈ lwSplit p.2) :
    Γ.solid.Perm (p.1 :: q.1 :: q.2) := (lwSplit_perm Γ.solid p hp).trans ((lwSplit_perm p.2 q hq).cons p.1)

/-- the band side of the `Contract` terms (`A2`, `A3`, `d2`, `d3`, `d4`): the atomic image of the pair `p`, `q` with `[q.dst] = [p.src]` is `[x] → [y]`, `[y'] → [x]`, and `scostLL_contract` applies -/
theorem BAShapeO2_contractLL (Γ : BAGraph E I) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid) (hq : q ∈ lwSplit p.2)
    (hp1 : p.1.σ = true ∧ p.1.circ = true) (hq1 : q.1.σ = true ∧ q.1.circ = true) (hvq : (promoteC Γ).vmap q.1.dst = (promoteC Γ).vmap p.1.src)
    (hwf1 : Γ.sameAtom p.1.src p.1.dst = false) (hwf2 : Γ.sameAtom q.1.src q.1.dst = false) :
    LGraph.ScostLL (promoteC Γ).merge (lwPrimContract (promoteC Γ).merge (q.2.map (BAScost_imgE Γ)) ((promoteC Γ).vmap p.1.src)
      ((promoteC Γ).vmap q.1.src) ((promoteC Γ).vmap p.1.dst)) := by
  have hu : (promoteC Γ).vmap q.1.src ≠ (promoteC Γ).vmap p.1.src := by
    rw [← hvq]
    exact BAScost_vmap_ne_of_sameAtom Γ hwf2
  have hperm : (promoteC Γ).merge.solid.Perm (⟨true, false, (promoteC Γ).vmap p.1.src, (promoteC Γ).vmap p.1.dst⟩ ::
      ⟨true, false, (promoteC Γ).vmap q.1.src, (promoteC Γ).vmap p.1.src⟩ :: q.2.map (BAScost_imgE Γ)) := by
    rw [BAScost_img_solid]
    have h4 := (BAShapeO2_perm_pq Γ p q hp hq).map (BAScost_imgE Γ)
    rw [List.map_cons, List.map_cons, BAShapeO2_imgE_wf Γ hp1.1 hp1.2 hwf1, BAShapeO2_imgE_wf Γ hq1.1 hq1.2 hwf2, hvq] at h4
    exact h4
  exact scostLL_contract (promoteC Γ).merge (q.2.map (BAScost_imgE Γ)) ((promoteC Γ).vmap p.1.src)
    ((promoteC Γ).vmap q.1.src) ((promoteC Γ).vmap p.1.dst) hu (BAScost_vmap_ne_of_sameAtom Γ hwf1) hperm

/-- **`gg2` head `A2`** (`BAGGOp_A2`, `Σ M_{xu} M_{ux} S⁺_{uβ} Ǧ_{βy} M_{y'β} f`): the band's `Contract([x]; [y'], [y])` (`scostLL_contract`), `α ↦ [x]`, `β ↦ [y']`. -/
theorem BAShapeO2_ggA2 (Γ : BAGraph E I) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid) (hq : q ∈ lwSplit p.2)
    (hp1 : p.1.σ = true ∧ p.1.circ = true) (hq1 : q.1.σ = true ∧ q.1.circ = true) (hxy : q.1.dst = p.1.src)
    (hwf1 : Γ.sameAtom p.1.src p.1.dst = false) (hwf2 : Γ.sameAtom q.1.src q.1.dst = false) :
    BAScostLL Γ (BAGGOp_A2 Γ p q) := by
  classical
  have hA : BAGGOp_A2 Γ p q = BAGraph.ext 2 Γ q.2 [bpS true (bpv 1) (owxEmb 2 p.1.dst)] [bpW true (bpv 0) (bpv 1)]
      [bpM (owxEmb 2 p.1.src) (bpv 0), bpM (bpv 0) (owxEmb 2 p.1.src), bpM (owxEmb 2 q.1.src) (bpv 1)] := rfl
  rw [hA]
  have hLL := BAShapeO2_contractLL Γ p q hp hq hp1 hq1 (by rw [hxy]) hwf1 hwf2
  have hmd : ∀ m ∈ [bpM (owxEmb 2 p.1.src) (bpv 0), bpM (bpv 0) (owxEmb 2 p.1.src), bpM (owxEmb 2 q.1.src) (bpv 1)],
      atomSetoid (BAGraph.ext 2 Γ q.2 [bpS true (bpv 1) (owxEmb 2 p.1.dst)] [bpW true (bpv 0) (bpv 1)]
      [bpM (owxEmb 2 p.1.src) (bpv 0), bpM (bpv 0) (owxEmb 2 p.1.src), bpM (owxEmb 2 q.1.src) (bpv 1)]) m.x m.y :=
    fun m hm => BAScost_atomSetoid_ext_md Γ q.2 _ _ _ m hm
  refine BAShapeO2_driver0 Γ p.1.src q.1.src q.2 _ _ _ ((atomSetoid _).symm (hmd (bpM (owxEmb 2 p.1.src) (bpv 0)) (by simp)))
    ((atomSetoid _).symm (hmd (bpM (owxEmb 2 q.1.src) (bpv 1)) (by simp))) _ hLL
    [⟨true, false, (promoteC Γ).vmap q.1.src, (promoteC Γ).vmap p.1.dst⟩] ?_ ?_ ?_
  · rw [BAShapeO2_map_id]
    exact (List.perm_append_singleton _ _).symm
  · intro s'' _
    refine BAShapeO2_Up_of_forall2 s'' ?_
    simp [BAShapeO2_rho2_zero, BAShapeO2_rho2_one, BAScost_rho2_emb, bpS]
  · simp [lwPrimContract, BAScost_img_waved_length]

/-- **`gg2` head `A3`** (`BAGGOp_A3`, `Σ M_{xu} M_{ux} S⁺_{uβ} M_{βy} Ǧ_{y'β} f`): the same `Contract`, `α ↦ [x]`, `β ↦ [y]`. -/
theorem BAShapeO2_ggA3 (Γ : BAGraph E I) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid) (hq : q ∈ lwSplit p.2)
    (hp1 : p.1.σ = true ∧ p.1.circ = true) (hq1 : q.1.σ = true ∧ q.1.circ = true) (hxy : q.1.dst = p.1.src)
    (hwf1 : Γ.sameAtom p.1.src p.1.dst = false) (hwf2 : Γ.sameAtom q.1.src q.1.dst = false) :
    BAScostLL Γ (BAGGOp_A3 Γ p q) := by
  classical
  have hA : BAGGOp_A3 Γ p q = BAGraph.ext 2 Γ q.2 [bpS true (owxEmb 2 q.1.src) (bpv 1)] [bpW true (bpv 0) (bpv 1)]
      [bpM (owxEmb 2 p.1.src) (bpv 0), bpM (bpv 0) (owxEmb 2 p.1.src), bpM (bpv 1) (owxEmb 2 p.1.dst)] := rfl
  rw [hA]
  have hLL := BAShapeO2_contractLL Γ p q hp hq hp1 hq1 (by rw [hxy]) hwf1 hwf2
  have hmd : ∀ m ∈ [bpM (owxEmb 2 p.1.src) (bpv 0), bpM (bpv 0) (owxEmb 2 p.1.src), bpM (bpv 1) (owxEmb 2 p.1.dst)],
      atomSetoid (BAGraph.ext 2 Γ q.2 [bpS true (owxEmb 2 q.1.src) (bpv 1)] [bpW true (bpv 0) (bpv 1)]
      [bpM (owxEmb 2 p.1.src) (bpv 0), bpM (bpv 0) (owxEmb 2 p.1.src), bpM (bpv 1) (owxEmb 2 p.1.dst)]) m.x m.y :=
    fun m hm => BAScost_atomSetoid_ext_md Γ q.2 _ _ _ m hm
  refine BAShapeO2_driver0 Γ p.1.src p.1.dst q.2 _ _ _ ((atomSetoid _).symm (hmd (bpM (owxEmb 2 p.1.src) (bpv 0)) (by simp)))
    (hmd (bpM (bpv 1) (owxEmb 2 p.1.dst)) (by simp)) _ hLL
    [⟨true, false, (promoteC Γ).vmap q.1.src, (promoteC Γ).vmap p.1.dst⟩] ?_ ?_ ?_
  · rw [BAShapeO2_map_id]
    exact (List.perm_append_singleton _ _).symm
  · intro s'' _
    refine BAShapeO2_Up_of_forall2 s'' ?_
    simp [BAShapeO2_rho2_zero, BAShapeO2_rho2_one, BAScost_rho2_emb, bpS]
  · simp [lwPrimContract, BAScost_img_waved_length]

/-- **`gg2` head `A4`** (`BAGGOp_A4`, `Σ M_{xα} S_{αβ} Ǧ_{ββ} G_{αy} Ǧ_{y'x} f`): the band's `Loop([x])` (`scostLL_loop`) with the edges `p`, `q` kept; `α ↦ [x]`, `β ↦` the fresh vertex. -/
theorem BAShapeO2_ggA4 (Γ : BAGraph E I) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid) (hq : q ∈ lwSplit p.2)
    (hp1 : p.1.σ = true ∧ p.1.circ = true) (hq1 : q.1.σ = true ∧ q.1.circ = true) (hxy : q.1.dst = p.1.src)
    (hwf1 : Γ.sameAtom p.1.src p.1.dst = false) (hwf2 : Γ.sameAtom q.1.src q.1.dst = false) :
    BAScostLL Γ (BAGGOp_A4 Γ p q) := by
  classical
  have hA : BAGGOp_A4 Γ p q = BAGraph.ext 2 Γ q.2 [bpS true (bpv 1) (bpv 1), bpS false (bpv 0) (owxEmb 2 p.1.dst),
      bpS true (owxEmb 2 q.1.src) (owxEmb 2 p.1.src)] [bpW false (bpv 0) (bpv 1)] [bpM (owxEmb 2 p.1.src) (bpv 0)] := rfl
  rw [hA]
  have hperm0 := BAShapeO2_perm_pq Γ p q hp hq
  have ep := BAShapeO2_imgE_wf Γ hp1.1 hp1.2 hwf1
  have eq' := BAShapeO2_imgE_wf Γ hq1.1 hq1.2 hwf2
  have hmdx : atomSetoid (BAGraph.ext 2 Γ q.2 [bpS true (bpv 1) (bpv 1), bpS false (bpv 0) (owxEmb 2 p.1.dst),
      bpS true (owxEmb 2 q.1.src) (owxEmb 2 p.1.src)] [bpW false (bpv 0) (bpv 1)] [bpM (owxEmb 2 p.1.src) (bpv 0)])
      (owxEmb 2 p.1.src) (bpv 0) :=
    BAScost_atomSetoid_ext_md Γ q.2 _ _ _ (bpM (owxEmb 2 p.1.src) (bpv 0)) (by simp)
  refine BAShapeO2_driver1 Γ p.1.src q.2 _ _ _ ((atomSetoid _).symm hmdx) (lwPrimLoop (promoteC Γ).merge ((promoteC Γ).vmap p.1.src) true)
    (scostLL_loop (promoteC Γ).merge ((promoteC Γ).vmap p.1.src) true)
    [⟨true, true, Sum.inr (Sum.inr 0), Sum.inr (Sum.inr 0)⟩, SEdge.map (owxEmb 1) (BAScost_imgE Γ p.1), SEdge.map (owxEmb 1) (BAScost_imgE Γ q.1)]
    ?_ ?_ ?_
  · rw [BAScost_lwPrimLoop_solid, BAScost_img_solid, List.map_map, List.map_map]
    refine ((hperm0.map (SEdge.map (owxEmb 1) ∘ BAScost_imgE Γ)).append_right _).trans ?_
    simp only [List.map_cons, Function.comp_apply]
    exact BAShapeO2_perm_rot [SEdge.map (owxEmb 1) (BAScost_imgE Γ p.1), SEdge.map (owxEmb 1) (BAScost_imgE Γ q.1)] _ _
  · intro s'' _
    refine BAShapeO2_Up_of_forall2 s'' ?_
    simp only [List.map_cons, List.map_nil, List.forall₂_cons, List.forall₂_nil_left_iff, and_true]
    rw [ep, eq', hxy]
    refine ⟨⟨rfl, ?_, ?_, fun _ => ?_⟩, ⟨rfl, ?_, ?_, fun h => ?_⟩, rfl, ?_, ?_, fun h => ?_⟩
    · simp [bpS, BAScost_psi1_beta, bpv]
    · simp [bpS, BAScost_psi1_beta, bpv]
    · simp [bpS, BAScost_sameAtom_self]
    · simp [bpS, BAScost_psi1_alpha, SEdge.map]
    · simp [bpS, BAScost_psi1_emb, SEdge.map]
    · simp [SEdge.map] at h
    · simp [bpS, BAScost_psi1_emb, SEdge.map]
    · simp [bpS, BAScost_psi1_emb, SEdge.map]
    · simp [SEdge.map] at h
  · simp [lwPrimLoop, LGraph.owxExt, BAScost_img_waved_length]

/-- **`gg2` head `A5`** (`BAGGOp_A5`, `Σ M_{xα} S_{αβ} Ǧ_{αx} G_{βy} G_{y'β} f`): `[x]` is an internal vertex of the atomic image (`hint`), and the term is the band's `R5` = `MoveSC([x]; [y'], [y])`
then `AddLoop([x])` (`localReg6d_ll_R5`, `LocalRegular6d:361`). -/
theorem BAShapeO2_ggA5 (Γ : BAGraph E I) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid) (hq : q ∈ lwSplit p.2)
    (hp1 : p.1.σ = true ∧ p.1.circ = true) (hq1 : q.1.σ = true ∧ q.1.circ = true) (hxy : q.1.dst = p.1.src)
    (hwf1 : Γ.sameAtom p.1.src p.1.dst = false) (hwf2 : Γ.sameAtom q.1.src q.1.dst = false) (hint : Γ.intAtom p.1.src = true) :
    BAScostLL Γ (BAGGOp_A5 Γ p q) := by
  classical
  have hA : BAGGOp_A5 Γ p q = BAGraph.ext 2 Γ q.2 [bpS true (bpv 0) (owxEmb 2 p.1.src), bpS false (bpv 1) (owxEmb 2 p.1.dst),
      bpS false (owxEmb 2 q.1.src) (bpv 1)] [bpW false (bpv 0) (bpv 1)] [bpM (owxEmb 2 p.1.src) (bpv 0)] := rfl
  rw [hA]
  obtain ⟨x', hx'⟩ := BAShapeO2_vmap_inr Γ hint
  have hwf2' : Γ.sameAtom q.1.src p.1.src = false := hxy ▸ hwf2
  have hperm : (promoteC Γ).merge.solid.Perm (⟨true, false, Sum.inr x', (promoteC Γ).vmap p.1.dst⟩ ::
      ⟨true, false, (promoteC Γ).vmap q.1.src, Sum.inr x'⟩ :: q.2.map (BAScost_imgE Γ)) := by
    rw [BAScost_img_solid]
    have h4 := (BAShapeO2_perm_pq Γ p q hp hq).map (BAScost_imgE Γ)
    rw [List.map_cons, List.map_cons, BAShapeO2_imgE_wf Γ hp1.1 hp1.2 hwf1, BAShapeO2_imgE_wf Γ hq1.1 hq1.2 hwf2, hxy, hx'] at h4
    exact h4
  have hLL := localReg6d_ll_R5 1 (promoteC Γ).merge (BAScost_imgE Γ q.1, q.2.map (BAScost_imgE Γ)) x' ((promoteC Γ).vmap p.1.dst)
    ((promoteC Γ).vmap q.1.src) (by rw [← hx']; exact BAScost_vmap_ne_of_sameAtom Γ hwf2')
    (by rw [← hx']; exact (BAScost_vmap_ne_of_sameAtom Γ hwf1)) hperm
  have hmdx : atomSetoid (BAGraph.ext 2 Γ q.2 [bpS true (bpv 0) (owxEmb 2 p.1.src), bpS false (bpv 1) (owxEmb 2 p.1.dst),
      bpS false (owxEmb 2 q.1.src) (bpv 1)] [bpW false (bpv 0) (bpv 1)] [bpM (owxEmb 2 p.1.src) (bpv 0)])
      (owxEmb 2 p.1.src) (bpv 0) :=
    BAScost_atomSetoid_ext_md Γ q.2 _ _ _ (bpM (owxEmb 2 p.1.src) (bpv 0)) (by simp)
  refine BAShapeO2_driver1 Γ p.1.src q.2 _ _ _ ((atomSetoid _).symm hmdx)
    (oe2xR5 1 (promoteC Γ).merge (BAScost_imgE Γ q.1, q.2.map (BAScost_imgE Γ)) x' ((promoteC Γ).vmap p.1.dst) ((promoteC Γ).vmap q.1.src)) hLL
    [⟨true, true, Sum.inr (Sum.inl x'), Sum.inr (Sum.inl x')⟩, ⟨true, false, Sum.inr (Sum.inr 0), owxEmb 1 ((promoteC Γ).vmap p.1.dst)⟩,
      ⟨true, false, owxEmb 1 ((promoteC Γ).vmap q.1.src), Sum.inr (Sum.inr 0)⟩] (List.Perm.refl _) ?_ ?_
  · intro s'' _
    refine BAShapeO2_Up_of_forall2 s'' ?_
    simp only [List.map_cons, List.map_nil, List.forall₂_cons, List.forall₂_nil_left_iff, and_true]
    refine ⟨⟨rfl, ?_, ?_, fun _ => ?_⟩, ⟨rfl, ?_, ?_, fun h => ?_⟩, rfl, ?_, ?_, fun h => ?_⟩
    · simp [bpS, BAScost_psi1_alpha, hx', owxEmb]
    · simp only [bpS]; rw [BAScost_psi1_emb, hx']; rfl
    · exact BAShapeO2_sameAtom_of_atomSetoid _ ((atomSetoid _).symm hmdx)
    · simp [bpS, BAScost_psi1_beta, bpv]
    · simp [bpS, BAScost_psi1_emb]
    · simp at h
    · simp [bpS, BAScost_psi1_emb]
    · simp [bpS, BAScost_psi1_beta, bpv]
    · simp at h
  · simp [oe2xR5, LGraph.owxExt, BAScost_img_waved_length]

theorem BAShapeO2_perm_pqr (Γ : BAGraph E I) (p q r : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid) (hq : q ∈ lwSplit p.2)
    (hr : r ∈ lwSplit q.2) : Γ.solid.Perm (p.1 :: q.1 :: r.1 :: r.2) :=
  (BAShapeO2_perm_pq Γ p q hp hq).trans (((lwSplit_perm q.2 r hr).cons q.1).cons p.1)

/-- **`gg2` tail `AD`** (`BAGGOp_AD`, the derivative terms at the solid edges `r.1` of `f`): the band's `R7` = `Dmove([x]; [x] → [y], r)` (`localReg6d_ll_R7`, `LocalRegular6d:374`). -/
theorem BAShapeO2_ggAD (Γ : BAGraph E I) (hN : Γ.Normal) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid) (hq : q ∈ lwSplit p.2)
    (hp1 : p.1.σ = true ∧ p.1.circ = true) (hq1 : q.1.σ = true ∧ q.1.circ = true) (hxy : q.1.dst = p.1.src)
    (hwf1 : Γ.sameAtom p.1.src p.1.dst = false) (hwf2 : Γ.sameAtom q.1.src q.1.dst = false) (hint : Γ.intAtom p.1.src = true)
    (r : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hr : r ∈ lwSplit q.2) :
    BAScostLL Γ (BAGGOp_AD Γ p q r) := by
  classical
  have hA : BAGGOp_AD Γ p q r = BAGraph.ext 2 Γ r.2 [(owxDE (bpv 1) (bpv 0) (SEdge.map (owxEmb 2) r.1)).1,
      (owxDE (bpv 1) (bpv 0) (SEdge.map (owxEmb 2) r.1)).2, bpS false (bpv 1) (owxEmb 2 p.1.dst),
      bpS true (owxEmb 2 q.1.src) (owxEmb 2 p.1.src)] [bpW false (bpv 0) (bpv 1)] [bpM (owxEmb 2 p.1.src) (bpv 0)] := rfl
  rw [hA]
  obtain ⟨x', hx'⟩ := BAShapeO2_vmap_inr Γ hint
  have hperm0 := BAShapeO2_perm_pqr Γ p q r hp hq hr
  have hr1 : r.1 ∈ Γ.solid := hperm0.symm.subset (by simp)
  have hperm : (promoteC Γ).merge.solid.Perm (⟨true, false, Sum.inr x', (promoteC Γ).vmap p.1.dst⟩ ::
      ⟨true, false, (promoteC Γ).vmap q.1.src, Sum.inr x'⟩ :: BAScost_imgE Γ r.1 :: r.2.map (BAScost_imgE Γ)) := by
    rw [BAScost_img_solid]
    have h4 := hperm0.map (BAScost_imgE Γ)
    rw [List.map_cons, List.map_cons, List.map_cons, BAShapeO2_imgE_wf Γ hp1.1 hp1.2 hwf1, BAShapeO2_imgE_wf Γ hq1.1 hq1.2 hwf2, hxy, hx'] at h4
    exact h4
  have hLL := localReg6d_ll_R7 1 (promoteC Γ).merge x' ((promoteC Γ).vmap p.1.dst) ((promoteC Γ).vmap q.1.src)
    (BAScost_imgE Γ r.1, r.2.map (BAScost_imgE Γ)) (by rw [← hx']; exact BAScost_vmap_ne_of_sameAtom Γ hwf1)
    (BAShapeO2_imgE_loop Γ hN hr1) hperm
  have hmdx : atomSetoid (BAGraph.ext 2 Γ r.2 [(owxDE (bpv 1) (bpv 0) (SEdge.map (owxEmb 2) r.1)).1,
      (owxDE (bpv 1) (bpv 0) (SEdge.map (owxEmb 2) r.1)).2, bpS false (bpv 1) (owxEmb 2 p.1.dst),
      bpS true (owxEmb 2 q.1.src) (owxEmb 2 p.1.src)] [bpW false (bpv 0) (bpv 1)] [bpM (owxEmb 2 p.1.src) (bpv 0)])
      (owxEmb 2 p.1.src) (bpv 0) :=
    BAScost_atomSetoid_ext_md Γ r.2 _ _ _ (bpM (owxEmb 2 p.1.src) (bpv 0)) (by simp)
  refine BAShapeO2_driver1 Γ p.1.src r.2 _ _ _ ((atomSetoid _).symm hmdx)
    (oe2xR7 1 (promoteC Γ).merge x' ((promoteC Γ).vmap p.1.dst) ((promoteC Γ).vmap q.1.src) (BAScost_imgE Γ r.1, r.2.map (BAScost_imgE Γ))) hLL
    [(owxDE (Sum.inr (Sum.inr 0)) (Sum.inr (Sum.inl x')) (SEdge.map (owxEmb 1) (BAScost_imgE Γ r.1))).1,
      (owxDE (Sum.inr (Sum.inr 0)) (Sum.inr (Sum.inl x')) (SEdge.map (owxEmb 1) (BAScost_imgE Γ r.1))).2,
      ⟨true, false, Sum.inr (Sum.inr 0), owxEmb 1 ((promoteC Γ).vmap p.1.dst)⟩,
      ⟨true, false, owxEmb 1 ((promoteC Γ).vmap q.1.src), Sum.inr (Sum.inl x')⟩] ?_ ?_ ?_
  · simp only [oe2xR7, LGraph.owxExt]
    exact List.Perm.append_left _ (List.perm_append_singleton _ _).symm
  · intro s'' _
    refine BAShapeO2_Up_of_forall2 s'' ?_
    have hα : BAScost_psi1 Γ p.1.src (bpv 0) = Sum.inr (Sum.inl x') := by rw [BAScost_psi1_alpha, hx']; rfl
    have hx2 : BAScost_psi1 Γ p.1.src (owxEmb 2 p.1.src) = Sum.inr (Sum.inl x') := by rw [BAScost_psi1_emb, hx']; rfl
    cases hσ : r.1.σ <;>
      simp [owxDE, SEdge.map, BAScost_imgE, hσ, BAScost_psi1_emb, hα, hx2, BAScost_psi1_beta, bpS, bpv]
  · simp [oe2xR7, LGraph.owxExt, BAScost_img_waved_length]

/-- **`gg4` head `B1`** (`BAGGOp_B1`): the atoms are `{x, u}`, `{w, α}`, `{β}`; the band's `R4` = `MoveSC([x]; [y'], [y])` then `Loop(β)` (`localReg6d_ll_R4`, `LocalRegular6d:388`). -/
theorem BAShapeO2_ggB1 (Γ : BAGraph E I) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid) (hq : q ∈ lwSplit p.2)
    (hp1 : p.1.σ = true ∧ p.1.circ = true) (hq1 : q.1.σ = true ∧ q.1.circ = true) (hxy : q.1.dst = p.1.src)
    (hwf1 : Γ.sameAtom p.1.src p.1.dst = false) (hwf2 : Γ.sameAtom q.1.src q.1.dst = false) (hint : Γ.intAtom p.1.src = true) :
    BAScostLL Γ (BAGGOp_B1 Γ p q) := by
  classical
  have hA : BAGGOp_B1 Γ p q = BAGraph.ext 4 Γ q.2 [bpS true (bpv 3) (bpv 3), bpS false (bpv 2) (owxEmb 4 p.1.dst), bpS true (owxEmb 4 q.1.src) (bpv 1)]
      [bpW true (bpv 0) (bpv 1), bpW false (bpv 2) (bpv 3)]
      [bpM (owxEmb 4 p.1.src) (bpv 0), bpM (bpv 0) (owxEmb 4 p.1.src), bpM (bpv 1) (bpv 2)] := rfl
  rw [hA]
  obtain ⟨x', hx'⟩ := BAShapeO2_vmap_inr Γ hint
  have hwf2' : Γ.sameAtom q.1.src p.1.src = false := hxy ▸ hwf2
  have hperm : (promoteC Γ).merge.solid.Perm (⟨true, false, Sum.inr x', (promoteC Γ).vmap p.1.dst⟩ ::
      ⟨true, false, (promoteC Γ).vmap q.1.src, Sum.inr x'⟩ :: q.2.map (BAScost_imgE Γ)) := by
    rw [BAScost_img_solid]
    have h4 := (BAShapeO2_perm_pq Γ p q hp hq).map (BAScost_imgE Γ)
    rw [List.map_cons, List.map_cons, BAShapeO2_imgE_wf Γ hp1.1 hp1.2 hwf1, BAShapeO2_imgE_wf Γ hq1.1 hq1.2 hwf2, hxy, hx'] at h4
    exact h4
  have hLL := localReg6d_ll_R4 1 (promoteC Γ).merge (BAScost_imgE Γ q.1, q.2.map (BAScost_imgE Γ)) x' ((promoteC Γ).vmap p.1.dst)
    ((promoteC Γ).vmap q.1.src) (by rw [← hx']; exact BAScost_vmap_ne_of_sameAtom Γ hwf2')
    (by rw [← hx']; exact (BAScost_vmap_ne_of_sameAtom Γ hwf1)) hperm
  have hmd : ∀ m ∈ [bpM (owxEmb 4 p.1.src) (bpv 0), bpM (bpv 0) (owxEmb 4 p.1.src), bpM (bpv 1) (bpv 2)],
      atomSetoid (BAGraph.ext 4 Γ q.2 [bpS true (bpv 3) (bpv 3), bpS false (bpv 2) (owxEmb 4 p.1.dst), bpS true (owxEmb 4 q.1.src) (bpv 1)]
        [bpW true (bpv 0) (bpv 1), bpW false (bpv 2) (bpv 3)]
        [bpM (owxEmb 4 p.1.src) (bpv 0), bpM (bpv 0) (owxEmb 4 p.1.src), bpM (bpv 1) (bpv 2)]) m.x m.y :=
    fun m hm => BAScost_atomSetoid_ext_md Γ q.2 _ _ _ m hm
  refine BAShapeO2_driver2 Γ p.1.src q.2 _ _ _ (hmd (bpM (bpv 0) (owxEmb 4 p.1.src)) (by simp)) (hmd (bpM (bpv 1) (bpv 2)) (by simp))
    (oe2xR4 1 (promoteC Γ).merge (BAScost_imgE Γ q.1, q.2.map (BAScost_imgE Γ)) x' ((promoteC Γ).vmap p.1.dst) ((promoteC Γ).vmap q.1.src)) hLL
    [⟨true, true, Sum.inr (Sum.inr 1), Sum.inr (Sum.inr 1)⟩, ⟨true, false, Sum.inr (Sum.inr 0), owxEmb 2 ((promoteC Γ).vmap p.1.dst)⟩,
      ⟨true, false, owxEmb 2 ((promoteC Γ).vmap q.1.src), Sum.inr (Sum.inr 0)⟩] ?_ ?_ ?_
  · simp only [oe2xR4, LGraph.owxExt]
    exact List.Perm.append_left _ (List.perm_append_singleton _ [_, _])
  · intro s'' _
    refine BAShapeO2_Up_of_forall2 s'' ?_
    simp only [List.map_cons, List.map_nil, List.forall₂_cons, List.forall₂_nil_left_iff, and_true]
    refine ⟨⟨rfl, ?_, ?_, fun _ => ?_⟩, ⟨rfl, ?_, ?_, fun h => ?_⟩, rfl, ?_, ?_, fun h => ?_⟩
    · simp [bpS, BAShapeO2_psi2_three, bpv]
    · simp [bpS, BAShapeO2_psi2_three, bpv]
    · simp [bpS, BAScost_sameAtom_self]
    · simp [bpS, BAShapeO2_psi2_two, bpv]
    · simp [bpS, BAShapeO2_psi2_emb]
    · simp at h
    · simp [bpS, BAShapeO2_psi2_emb]
    · simp [bpS, BAShapeO2_psi2_one, bpv]
    · simp at h
  · simp [oe2xR4, LGraph.owxExt, BAScost_img_waved_length]

/-- **`gg4` head `B2`** (`BAGGOp_B2`): the band's `R6` = `Loop([x])` then `MoveSC([x]; [y'], [y])` (`localReg6d_ll_R6`, `:404`). -/
theorem BAShapeO2_ggB2 (Γ : BAGraph E I) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid) (hq : q ∈ lwSplit p.2)
    (hp1 : p.1.σ = true ∧ p.1.circ = true) (hq1 : q.1.σ = true ∧ q.1.circ = true) (hxy : q.1.dst = p.1.src)
    (hwf1 : Γ.sameAtom p.1.src p.1.dst = false) (hwf2 : Γ.sameAtom q.1.src q.1.dst = false) (hint : Γ.intAtom p.1.src = true) :
    BAScostLL Γ (BAGGOp_B2 Γ p q) := by
  classical
  have hA : BAGGOp_B2 Γ p q = BAGraph.ext 4 Γ q.2 [bpS true (bpv 2) (bpv 1), bpS false (bpv 3) (owxEmb 4 p.1.dst), bpS false (owxEmb 4 q.1.src) (bpv 3)]
      [bpW true (bpv 0) (bpv 1), bpW false (bpv 2) (bpv 3)]
      [bpM (owxEmb 4 p.1.src) (bpv 0), bpM (bpv 0) (owxEmb 4 p.1.src), bpM (bpv 1) (bpv 2)] := rfl
  rw [hA]
  obtain ⟨x', hx'⟩ := BAShapeO2_vmap_inr Γ hint
  have hwf2' : Γ.sameAtom q.1.src p.1.src = false := hxy ▸ hwf2
  have hperm : (promoteC Γ).merge.solid.Perm (⟨true, false, Sum.inr x', (promoteC Γ).vmap p.1.dst⟩ ::
      ⟨true, false, (promoteC Γ).vmap q.1.src, Sum.inr x'⟩ :: q.2.map (BAScost_imgE Γ)) := by
    rw [BAScost_img_solid]
    have h4 := (BAShapeO2_perm_pq Γ p q hp hq).map (BAScost_imgE Γ)
    rw [List.map_cons, List.map_cons, BAShapeO2_imgE_wf Γ hp1.1 hp1.2 hwf1, BAShapeO2_imgE_wf Γ hq1.1 hq1.2 hwf2, hxy, hx'] at h4
    exact h4
  have hLL := localReg6d_ll_R6 1 (promoteC Γ).merge (BAScost_imgE Γ q.1, q.2.map (BAScost_imgE Γ)) x' ((promoteC Γ).vmap p.1.dst)
    ((promoteC Γ).vmap q.1.src) (by rw [← hx']; exact BAScost_vmap_ne_of_sameAtom Γ hwf2')
    (by rw [← hx']; exact (BAScost_vmap_ne_of_sameAtom Γ hwf1)) hperm
  have hmd : ∀ m ∈ [bpM (owxEmb 4 p.1.src) (bpv 0), bpM (bpv 0) (owxEmb 4 p.1.src), bpM (bpv 1) (bpv 2)],
      atomSetoid (BAGraph.ext 4 Γ q.2 [bpS true (bpv 2) (bpv 1), bpS false (bpv 3) (owxEmb 4 p.1.dst), bpS false (owxEmb 4 q.1.src) (bpv 3)]
        [bpW true (bpv 0) (bpv 1), bpW false (bpv 2) (bpv 3)]
        [bpM (owxEmb 4 p.1.src) (bpv 0), bpM (bpv 0) (owxEmb 4 p.1.src), bpM (bpv 1) (bpv 2)]) m.x m.y :=
    fun m hm => BAScost_atomSetoid_ext_md Γ q.2 _ _ _ m hm
  have h12 := hmd (bpM (bpv 1) (bpv 2)) (by simp)
  refine BAShapeO2_driver2 Γ p.1.src q.2 _ _ _ (hmd (bpM (bpv 0) (owxEmb 4 p.1.src)) (by simp)) h12
    (oe2xR6 1 (promoteC Γ).merge (BAScost_imgE Γ q.1, q.2.map (BAScost_imgE Γ)) x' ((promoteC Γ).vmap p.1.dst) ((promoteC Γ).vmap q.1.src)) hLL
    [⟨true, true, Sum.inr (Sum.inr 0), Sum.inr (Sum.inr 0)⟩, ⟨true, false, Sum.inr (Sum.inr 1), owxEmb 2 ((promoteC Γ).vmap p.1.dst)⟩,
      ⟨true, false, owxEmb 2 ((promoteC Γ).vmap q.1.src), Sum.inr (Sum.inr 1)⟩] (List.Perm.refl _) ?_ ?_
  · intro s'' _
    refine BAShapeO2_Up_of_forall2 s'' ?_
    simp only [List.map_cons, List.map_nil, List.forall₂_cons, List.forall₂_nil_left_iff, and_true]
    refine ⟨⟨rfl, ?_, ?_, fun _ => ?_⟩, ⟨rfl, ?_, ?_, fun h => ?_⟩, rfl, ?_, ?_, fun h => ?_⟩
    · simp [bpS, BAShapeO2_psi2_two, bpv]
    · simp [bpS, BAShapeO2_psi2_one, bpv]
    · exact BAShapeO2_sameAtom_of_atomSetoid _ ((atomSetoid _).symm h12)
    · simp [bpS, BAShapeO2_psi2_three, bpv]
    · simp [bpS, BAShapeO2_psi2_emb]
    · simp at h
    · simp [bpS, BAShapeO2_psi2_emb]
    · simp [bpS, BAShapeO2_psi2_three, bpv]
    · simp at h
  · simp [oe2xR6, LGraph.owxExt, BAScost_img_waved_length]

/-- **`gg4` tail `BD`** (`BAGGOp_BD`): the band's `R8` = `MoveSC([x]; [y'], [y])` then `Dmove(α; α → y, r)` (`localReg6d_ll_R8`, `:429`). -/
theorem BAShapeO2_ggBD (Γ : BAGraph E I) (hN : Γ.Normal) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid) (hq : q ∈ lwSplit p.2)
    (hp1 : p.1.σ = true ∧ p.1.circ = true) (hq1 : q.1.σ = true ∧ q.1.circ = true) (hxy : q.1.dst = p.1.src)
    (hwf1 : Γ.sameAtom p.1.src p.1.dst = false) (hwf2 : Γ.sameAtom q.1.src q.1.dst = false) (hint : Γ.intAtom p.1.src = true)
    (r : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hr : r ∈ lwSplit q.2) :
    BAScostLL Γ (BAGGOp_BD Γ p q r) := by
  classical
  have hA : BAGGOp_BD Γ p q r = BAGraph.ext 4 Γ r.2 [(owxDE (bpv 3) (bpv 2) (SEdge.map (owxEmb 4) r.1)).1,
      (owxDE (bpv 3) (bpv 2) (SEdge.map (owxEmb 4) r.1)).2, bpS false (bpv 3) (owxEmb 4 p.1.dst), bpS true (owxEmb 4 q.1.src) (bpv 1)]
      [bpW true (bpv 0) (bpv 1), bpW false (bpv 2) (bpv 3)]
      [bpM (owxEmb 4 p.1.src) (bpv 0), bpM (bpv 0) (owxEmb 4 p.1.src), bpM (bpv 1) (bpv 2)] := rfl
  rw [hA]
  obtain ⟨x', hx'⟩ := BAShapeO2_vmap_inr Γ hint
  have hwf2' : Γ.sameAtom q.1.src p.1.src = false := hxy ▸ hwf2
  have hperm0 := BAShapeO2_perm_pqr Γ p q r hp hq hr
  have hr1 : r.1 ∈ Γ.solid := hperm0.symm.subset (by simp)
  have hperm : (promoteC Γ).merge.solid.Perm (⟨true, false, Sum.inr x', (promoteC Γ).vmap p.1.dst⟩ ::
      ⟨true, false, (promoteC Γ).vmap q.1.src, Sum.inr x'⟩ :: BAScost_imgE Γ r.1 :: r.2.map (BAScost_imgE Γ)) := by
    rw [BAScost_img_solid]
    have h4 := hperm0.map (BAScost_imgE Γ)
    rw [List.map_cons, List.map_cons, List.map_cons, BAShapeO2_imgE_wf Γ hp1.1 hp1.2 hwf1, BAShapeO2_imgE_wf Γ hq1.1 hq1.2 hwf2, hxy, hx'] at h4
    exact h4
  have hLL := localReg6d_ll_R8 1 (promoteC Γ).merge x' ((promoteC Γ).vmap p.1.dst) ((promoteC Γ).vmap q.1.src)
    (BAScost_imgE Γ r.1, r.2.map (BAScost_imgE Γ)) (by rw [← hx']; exact BAScost_vmap_ne_of_sameAtom Γ hwf2')
    (by rw [← hx']; exact BAScost_vmap_ne_of_sameAtom Γ hwf1) (BAShapeO2_imgE_loop Γ hN hr1) hperm
  have hmd : ∀ m ∈ [bpM (owxEmb 4 p.1.src) (bpv 0), bpM (bpv 0) (owxEmb 4 p.1.src), bpM (bpv 1) (bpv 2)],
      atomSetoid (BAGraph.ext 4 Γ r.2 [(owxDE (bpv 3) (bpv 2) (SEdge.map (owxEmb 4) r.1)).1,
        (owxDE (bpv 3) (bpv 2) (SEdge.map (owxEmb 4) r.1)).2, bpS false (bpv 3) (owxEmb 4 p.1.dst), bpS true (owxEmb 4 q.1.src) (bpv 1)]
        [bpW true (bpv 0) (bpv 1), bpW false (bpv 2) (bpv 3)]
        [bpM (owxEmb 4 p.1.src) (bpv 0), bpM (bpv 0) (owxEmb 4 p.1.src), bpM (bpv 1) (bpv 2)]) m.x m.y :=
    fun m hm => BAScost_atomSetoid_ext_md Γ r.2 _ _ _ m hm
  refine BAShapeO2_driver2 Γ p.1.src r.2 _ _ _ (hmd (bpM (bpv 0) (owxEmb 4 p.1.src)) (by simp)) (hmd (bpM (bpv 1) (bpv 2)) (by simp))
    (oe2xR8 1 (promoteC Γ).merge x' ((promoteC Γ).vmap p.1.dst) ((promoteC Γ).vmap q.1.src) (BAScost_imgE Γ r.1, r.2.map (BAScost_imgE Γ))) hLL
    [(owxDE (Sum.inr (Sum.inr 1)) (Sum.inr (Sum.inr 0)) (SEdge.map (owxEmb 2) (BAScost_imgE Γ r.1))).1,
      (owxDE (Sum.inr (Sum.inr 1)) (Sum.inr (Sum.inr 0)) (SEdge.map (owxEmb 2) (BAScost_imgE Γ r.1))).2,
      ⟨true, false, Sum.inr (Sum.inr 1), owxEmb 2 ((promoteC Γ).vmap p.1.dst)⟩,
      ⟨true, false, owxEmb 2 ((promoteC Γ).vmap q.1.src), Sum.inr (Sum.inr 0)⟩] ?_ ?_ ?_
  · simp only [oe2xR8, LGraph.owxExt]
    exact List.Perm.append_left _ (List.perm_append_comm (l₁ := [_, _]) (l₂ := [_, _]))
  · intro s'' _
    refine BAShapeO2_Up_of_forall2 s'' ?_
    cases hσ : r.1.σ <;>
      simp [owxDE, SEdge.map, BAScost_imgE, hσ, BAShapeO2_psi2_emb, BAShapeO2_psi2_one, BAShapeO2_psi2_two, BAShapeO2_psi2_three, bpS, bpv]
  · simp [oe2xR8, LGraph.owxExt, BAScost_img_waved_length]

end GG

/-! ## 4. The `ggSplit` terms -/

section GGSplit

variable {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

/-- **`ggSplit` term `d1`** (`BASim:132`, `dq [G_{y'β}, Ǧ_{αa'}, G_{βy}] []`): `[a] = [a']` is internal (`hint`), and the term is the band's `R5` at `x := [a]` (`localReg6d_ll_R5`). -/
theorem BAShapeO2_ggSplitD1 (Γ : BAGraph E I) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid) (hq : q ∈ lwSplit p.2)
    (hp1 : p.1.σ = true ∧ p.1.circ = true) (hq1 : q.1.σ = true ∧ q.1.circ = true) (hsame : Γ.sameAtom p.1.src q.1.dst = true)
    (hwf1 : Γ.sameAtom p.1.src p.1.dst = false) (hwf2 : Γ.sameAtom q.1.src q.1.dst = false) (hint : Γ.intAtom p.1.src = true) :
    BAScostLL Γ (BAGraph.ext 2 Γ q.2 [bpS false (owxEmb 2 q.1.src) (bpv 1), bpS true (bpv 0) (owxEmb 2 q.1.dst), bpS false (bpv 1) (owxEmb 2 p.1.dst)]
      [bpW false (bpv 0) (bpv 1)] [bpM (owxEmb 2 p.1.src) (bpv 0)]) := by
  classical
  obtain ⟨x', hx'⟩ := BAShapeO2_vmap_inr Γ hint
  have hvq : (promoteC Γ).vmap q.1.dst = (promoteC Γ).vmap p.1.src := ((BAAtomic_promoteC_vmap_eq_sameAtom Γ _ _).2 hsame).symm
  have hne2 : (promoteC Γ).vmap q.1.src ≠ (promoteC Γ).vmap p.1.src := by
    rw [← hvq]; exact BAScost_vmap_ne_of_sameAtom Γ hwf2
  have hperm : (promoteC Γ).merge.solid.Perm (⟨true, false, Sum.inr x', (promoteC Γ).vmap p.1.dst⟩ ::
      ⟨true, false, (promoteC Γ).vmap q.1.src, Sum.inr x'⟩ :: q.2.map (BAScost_imgE Γ)) := by
    rw [BAScost_img_solid]
    have h4 := (BAShapeO2_perm_pq Γ p q hp hq).map (BAScost_imgE Γ)
    rw [List.map_cons, List.map_cons, BAShapeO2_imgE_wf Γ hp1.1 hp1.2 hwf1, BAShapeO2_imgE_wf Γ hq1.1 hq1.2 hwf2, hvq, hx'] at h4
    exact h4
  have hLL := localReg6d_ll_R5 1 (promoteC Γ).merge (BAScost_imgE Γ q.1, q.2.map (BAScost_imgE Γ)) x' ((promoteC Γ).vmap p.1.dst)
    ((promoteC Γ).vmap q.1.src) (by rw [← hx']; exact hne2) (by rw [← hx']; exact (BAScost_vmap_ne_of_sameAtom Γ hwf1)) hperm
  have hmdx : atomSetoid (BAGraph.ext 2 Γ q.2 [bpS false (owxEmb 2 q.1.src) (bpv 1), bpS true (bpv 0) (owxEmb 2 q.1.dst), bpS false (bpv 1) (owxEmb 2 p.1.dst)]
      [bpW false (bpv 0) (bpv 1)] [bpM (owxEmb 2 p.1.src) (bpv 0)]) (owxEmb 2 p.1.src) (bpv 0) :=
    BAScost_atomSetoid_ext_md Γ q.2 _ _ _ (bpM (owxEmb 2 p.1.src) (bpv 0)) (by simp)
  have haa : atomSetoid (BAGraph.ext 2 Γ q.2 [bpS false (owxEmb 2 q.1.src) (bpv 1), bpS true (bpv 0) (owxEmb 2 q.1.dst), bpS false (bpv 1) (owxEmb 2 p.1.dst)]
      [bpW false (bpv 0) (bpv 1)] [bpM (owxEmb 2 p.1.src) (bpv 0)]) (bpv 0) (owxEmb 2 q.1.dst) :=
    (atomSetoid _).trans ((atomSetoid _).symm hmdx) (BAScost_atomSetoid_ext Γ q.2 _ _ _
      ((BAAtomic_atomSetoid_iff Γ _ _).2 ((Γ.BAAtomic_sameAtom_iff _ _).1 hsame)))
  refine BAShapeO2_driver1 Γ p.1.src q.2 _ _ _ ((atomSetoid _).symm hmdx)
    (oe2xR5 1 (promoteC Γ).merge (BAScost_imgE Γ q.1, q.2.map (BAScost_imgE Γ)) x' ((promoteC Γ).vmap p.1.dst) ((promoteC Γ).vmap q.1.src)) hLL
    [⟨true, false, owxEmb 1 ((promoteC Γ).vmap q.1.src), Sum.inr (Sum.inr 0)⟩, ⟨true, true, Sum.inr (Sum.inl x'), Sum.inr (Sum.inl x')⟩,
      ⟨true, false, Sum.inr (Sum.inr 0), owxEmb 1 ((promoteC Γ).vmap p.1.dst)⟩] ?_ ?_ ?_
  · simp only [oe2xR5, LGraph.owxExt]
    exact List.Perm.append_left _ (List.perm_append_singleton _ [_, _])
  · intro s'' _
    refine BAShapeO2_Up_of_forall2 s'' ?_
    simp only [List.map_cons, List.map_nil, List.forall₂_cons, List.forall₂_nil_left_iff, and_true]
    refine ⟨⟨rfl, ?_, ?_, fun h => ?_⟩, ⟨rfl, ?_, ?_, fun _ => ?_⟩, rfl, ?_, ?_, fun h => ?_⟩
    · simp [bpS, BAScost_psi1_emb]
    · simp [bpS, BAScost_psi1_beta, bpv]
    · simp at h
    · simp only [bpS]; rw [BAScost_psi1_alpha, hx']; rfl
    · simp only [bpS]; rw [BAScost_psi1_emb, hvq, hx']; rfl
    · exact BAShapeO2_sameAtom_of_atomSetoid _ haa
    · simp [bpS, BAScost_psi1_beta, bpv]
    · simp [bpS, BAScost_psi1_emb]
    · simp at h
  · simp [oe2xR5, LGraph.owxExt, BAScost_img_waved_length]

/-- the data of the `Contract` terms `d2`, `d3`, `d4` -/
private theorem BAShapeO2_ggSplit_vq (Γ : BAGraph E I) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hsame : Γ.sameAtom p.1.src q.1.dst = true) :
    (promoteC Γ).vmap q.1.dst = (promoteC Γ).vmap p.1.src := ((BAAtomic_promoteC_vmap_eq_sameAtom Γ _ _).2 hsame).symm

/-- **`ggSplit` term `d2`** (`dq [Ǧ_{y'β}] [M_{αa'}, M_{βy}]`): `Contract([a]; [y'], [y])` (`scostLL_contract`), `α ↦ [a]`, `β ↦ [y]`. -/
theorem BAShapeO2_ggSplitD2 (Γ : BAGraph E I) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid) (hq : q ∈ lwSplit p.2)
    (hp1 : p.1.σ = true ∧ p.1.circ = true) (hq1 : q.1.σ = true ∧ q.1.circ = true) (hsame : Γ.sameAtom p.1.src q.1.dst = true)
    (hwf1 : Γ.sameAtom p.1.src p.1.dst = false) (hwf2 : Γ.sameAtom q.1.src q.1.dst = false) :
    BAScostLL Γ (BAGraph.ext 2 Γ q.2 [bpS true (owxEmb 2 q.1.src) (bpv 1)] [bpW false (bpv 0) (bpv 1)]
      [bpM (owxEmb 2 p.1.src) (bpv 0), bpM (bpv 0) (owxEmb 2 q.1.dst), bpM (bpv 1) (owxEmb 2 p.1.dst)]) := by
  classical
  have hLL := BAShapeO2_contractLL Γ p q hp hq hp1 hq1 (BAShapeO2_ggSplit_vq Γ p q hsame) hwf1 hwf2
  have hmd : ∀ m ∈ [bpM (owxEmb 2 p.1.src) (bpv 0), bpM (bpv 0) (owxEmb 2 q.1.dst), bpM (bpv 1) (owxEmb 2 p.1.dst)],
      atomSetoid (BAGraph.ext 2 Γ q.2 [bpS true (owxEmb 2 q.1.src) (bpv 1)] [bpW false (bpv 0) (bpv 1)]
      [bpM (owxEmb 2 p.1.src) (bpv 0), bpM (bpv 0) (owxEmb 2 q.1.dst), bpM (bpv 1) (owxEmb 2 p.1.dst)]) m.x m.y :=
    fun m hm => BAScost_atomSetoid_ext_md Γ q.2 _ _ _ m hm
  refine BAShapeO2_driver0 Γ p.1.src p.1.dst q.2 _ _ _ ((atomSetoid _).symm (hmd (bpM (owxEmb 2 p.1.src) (bpv 0)) (by simp)))
    (hmd (bpM (bpv 1) (owxEmb 2 p.1.dst)) (by simp)) _ hLL
    [⟨true, false, (promoteC Γ).vmap q.1.src, (promoteC Γ).vmap p.1.dst⟩] ?_ ?_ ?_
  · rw [BAShapeO2_map_id]
    exact (List.perm_append_singleton _ _).symm
  · intro s'' _
    refine BAShapeO2_Up_of_forall2 s'' ?_
    simp [BAShapeO2_rho2_zero, BAShapeO2_rho2_one, BAScost_rho2_emb, bpS]
  · simp [lwPrimContract, BAScost_img_waved_length]

/-- **`ggSplit` term `d3`** (`dq [Ǧ_{βy}] [M_{αa'}, M_{y'β}]`): the same `Contract`, `α ↦ [a]`, `β ↦ [y']`. -/
theorem BAShapeO2_ggSplitD3 (Γ : BAGraph E I) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid) (hq : q ∈ lwSplit p.2)
    (hp1 : p.1.σ = true ∧ p.1.circ = true) (hq1 : q.1.σ = true ∧ q.1.circ = true) (hsame : Γ.sameAtom p.1.src q.1.dst = true)
    (hwf1 : Γ.sameAtom p.1.src p.1.dst = false) (hwf2 : Γ.sameAtom q.1.src q.1.dst = false) :
    BAScostLL Γ (BAGraph.ext 2 Γ q.2 [bpS true (bpv 1) (owxEmb 2 p.1.dst)] [bpW false (bpv 0) (bpv 1)]
      [bpM (owxEmb 2 p.1.src) (bpv 0), bpM (bpv 0) (owxEmb 2 q.1.dst), bpM (owxEmb 2 q.1.src) (bpv 1)]) := by
  classical
  have hLL := BAShapeO2_contractLL Γ p q hp hq hp1 hq1 (BAShapeO2_ggSplit_vq Γ p q hsame) hwf1 hwf2
  have hmd : ∀ m ∈ [bpM (owxEmb 2 p.1.src) (bpv 0), bpM (bpv 0) (owxEmb 2 q.1.dst), bpM (owxEmb 2 q.1.src) (bpv 1)],
      atomSetoid (BAGraph.ext 2 Γ q.2 [bpS true (bpv 1) (owxEmb 2 p.1.dst)] [bpW false (bpv 0) (bpv 1)]
      [bpM (owxEmb 2 p.1.src) (bpv 0), bpM (bpv 0) (owxEmb 2 q.1.dst), bpM (owxEmb 2 q.1.src) (bpv 1)]) m.x m.y :=
    fun m hm => BAScost_atomSetoid_ext_md Γ q.2 _ _ _ m hm
  refine BAShapeO2_driver0 Γ p.1.src q.1.src q.2 _ _ _ ((atomSetoid _).symm (hmd (bpM (owxEmb 2 p.1.src) (bpv 0)) (by simp)))
    ((atomSetoid _).symm (hmd (bpM (owxEmb 2 q.1.src) (bpv 1)) (by simp))) _ hLL
    [⟨true, false, (promoteC Γ).vmap q.1.src, (promoteC Γ).vmap p.1.dst⟩] ?_ ?_ ?_
  · rw [BAShapeO2_map_id]
    exact (List.perm_append_singleton _ _).symm
  · intro s'' _
    refine BAShapeO2_Up_of_forall2 s'' ?_
    simp [BAShapeO2_rho2_zero, BAShapeO2_rho2_one, BAScost_rho2_emb, bpS]
  · simp [lwPrimContract, BAScost_img_waved_length]

/-- **`ggSplit` term `d4`** (`dq [] [M_{αa'}, M_{y'β}, M_{βy}]`): the same `Contract` with the contracted edge `[y'] → [y]` dropped (`[y'] = [y]` at every merge of the term), as `BAScostLL_S1`. -/
theorem BAShapeO2_ggSplitD4 (Γ : BAGraph E I) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid) (hq : q ∈ lwSplit p.2)
    (hp1 : p.1.σ = true ∧ p.1.circ = true) (hq1 : q.1.σ = true ∧ q.1.circ = true) (hsame : Γ.sameAtom p.1.src q.1.dst = true)
    (hwf1 : Γ.sameAtom p.1.src p.1.dst = false) (hwf2 : Γ.sameAtom q.1.src q.1.dst = false) :
    BAScostLL Γ (BAGraph.ext 2 Γ q.2 [] [bpW false (bpv 0) (bpv 1)]
      [bpM (owxEmb 2 p.1.src) (bpv 0), bpM (bpv 0) (owxEmb 2 q.1.dst), bpM (owxEmb 2 q.1.src) (bpv 1), bpM (bpv 1) (owxEmb 2 p.1.dst)]) := by
  classical
  have hLL := BAShapeO2_contractLL Γ p q hp hq hp1 hq1 (BAShapeO2_ggSplit_vq Γ p q hsame) hwf1 hwf2
  have hmd : ∀ m ∈ [bpM (owxEmb 2 p.1.src) (bpv 0), bpM (bpv 0) (owxEmb 2 q.1.dst), bpM (owxEmb 2 q.1.src) (bpv 1), bpM (bpv 1) (owxEmb 2 p.1.dst)],
      atomSetoid (BAGraph.ext 2 Γ q.2 [] [bpW false (bpv 0) (bpv 1)]
      [bpM (owxEmb 2 p.1.src) (bpv 0), bpM (bpv 0) (owxEmb 2 q.1.dst), bpM (owxEmb 2 q.1.src) (bpv 1), bpM (bpv 1) (owxEmb 2 p.1.dst)]) m.x m.y :=
    fun m hm => BAScost_atomSetoid_ext_md Γ q.2 _ _ _ m hm
  refine BAShapeO2_driver0 Γ p.1.src p.1.dst q.2 _ _ _ ((atomSetoid _).symm (hmd (bpM (owxEmb 2 p.1.src) (bpv 0)) (by simp)))
    (hmd (bpM (bpv 1) (owxEmb 2 p.1.dst)) (by simp)) _ hLL
    [⟨true, false, (promoteC Γ).vmap q.1.src, (promoteC Γ).vmap p.1.dst⟩] ?_ ?_ ?_
  · rw [BAShapeO2_map_id]
    exact (List.perm_append_singleton _ _).symm
  · intro s'' hadm
    have hu : s'' ((promoteC Γ).vmap q.1.src) ((promoteC Γ).vmap p.1.dst) := by
      have h1 := hadm (owxEmb 2 q.1.src) (owxEmb 2 p.1.dst)
        ((atomSetoid _).trans (hmd (bpM (owxEmb 2 q.1.src) (bpv 1)) (by simp)) (hmd (bpM (bpv 1) (owxEmb 2 p.1.dst)) (by simp)))
      simpa [BAScost_rho2_emb] using h1
    exact BAScost_Up.drop s'' _ (BAScost_Up.refl s'' []) rfl hu
  · simp [lwPrimContract, BAScost_img_waved_length]

end GGSplit

/-! ## 5. The term lists -/

section Lists

variable {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

/-- **The `weight` step, `lw2`** (`BASim:139`): every term of `lw2` at a blue circled loop `p.1` has the local lemma -/
theorem BAShapeO2_lw2 (Γ : BAGraph E I) (hN : Γ.Normal) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid)
    (hp1 : p.1.σ = true ∧ p.1.circ = true ∧ p.1.src = p.1.dst) : ∀ X ∈ Γ.lw2 p, BAScostLL Γ X := by
  intro X hX
  rcases List.mem_cons.1 hX with rfl | hX
  · exact BAShapeO2_lw2Head Γ p hp hp1
  · obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hX
    exact BAShapeO2_lanlwD Γ hN p hp ⟨hp1.1, hp1.2.1⟩ q hq

/-- **The `weight` step, `lw4`**: every term of `lw4` at a blue circled loop `p.1` has the local lemma -/
theorem BAShapeO2_lw4 (Γ : BAGraph E I) (hN : Γ.Normal) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid)
    (hp1 : p.1.σ = true ∧ p.1.circ = true ∧ p.1.src = p.1.dst) : ∀ X ∈ Γ.lw4 p, BAScostLL Γ X := by
  intro X hX
  rcases List.mem_cons.1 hX with rfl | hX
  · exact BAShapeO2_lw4Head Γ p hp hp1
  · obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hX
    exact BAShapeO2_lw4Tail Γ hN p hp hp1 q hq

/-- **The `within` step, stage 1** (`BASim:122`): the head and the terms `lanlwD` -/
theorem BAShapeO2_within (Γ : BAGraph E I) (hN : Γ.Normal) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid)
    (hp1 : p.1.σ = true ∧ p.1.circ = true) (hsame : Γ.sameAtom p.1.src p.1.dst = true) :
    ∀ X ∈ BAGraph.ext 2 Γ p.2 [bpS true (bpv 1) (bpv 1), bpS true (bpv 0) (owxEmb 2 p.1.dst)] [bpW false (bpv 0) (bpv 1)]
      [bpM (owxEmb 2 p.1.src) (bpv 0)] :: (lwSplit p.2).map (BAGraph.lanlwD Γ p), BAScostLL Γ X := by
  intro X hX
  rcases List.mem_cons.1 hX with rfl | hX
  · exact BAShapeO2_withinHead Γ p hp hp1 hsame
  · obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hX
    exact BAShapeO2_lanlwD Γ hN p hp hp1 q hq

/-- **The `gg` step, `gg2`** (`BASim:149`): `A1` is `BAScostLL_S1` -/
theorem BAShapeO2_gg2 (Γ : BAGraph E I) (hN : Γ.Normal) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid) (hq : q ∈ lwSplit p.2)
    (hp1 : p.1.σ = true ∧ p.1.circ = true) (hq1 : q.1.σ = true ∧ q.1.circ = true) (hxy : q.1.dst = p.1.src)
    (hwf1 : Γ.sameAtom p.1.src p.1.dst = false) (hwf2 : Γ.sameAtom q.1.src q.1.dst = false) (hint : Γ.intAtom p.1.src = true) :
    ∀ X ∈ Γ.gg2 p q, BAScostLL Γ X := by
  intro X hX
  rw [BAGGOp_gg2_eq] at hX
  rcases List.mem_append.1 hX with hX | hX
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hX
    rcases hX with rfl | rfl | rfl | rfl | rfl
    · exact BAScostLL_S1 Γ p q hp hq hp1 hq1 hxy hwf1 hwf2
    · exact BAShapeO2_ggA2 Γ p q hp hq hp1 hq1 hxy hwf1 hwf2
    · exact BAShapeO2_ggA3 Γ p q hp hq hp1 hq1 hxy hwf1 hwf2
    · exact BAShapeO2_ggA4 Γ p q hp hq hp1 hq1 hxy hwf1 hwf2
    · exact BAShapeO2_ggA5 Γ p q hp hq hp1 hq1 hxy hwf1 hwf2 hint
  · obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hX
    exact BAShapeO2_ggAD Γ hN p q hp hq hp1 hq1 hxy hwf1 hwf2 hint r hr

/-- **The `gg` step, `gg4`** -/
theorem BAShapeO2_gg4 (Γ : BAGraph E I) (hN : Γ.Normal) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid) (hq : q ∈ lwSplit p.2)
    (hp1 : p.1.σ = true ∧ p.1.circ = true) (hq1 : q.1.σ = true ∧ q.1.circ = true) (hxy : q.1.dst = p.1.src)
    (hwf1 : Γ.sameAtom p.1.src p.1.dst = false) (hwf2 : Γ.sameAtom q.1.src q.1.dst = false) (hint : Γ.intAtom p.1.src = true) :
    ∀ X ∈ Γ.gg4 p q, BAScostLL Γ X := by
  intro X hX
  rw [BAGGOp_gg4_eq] at hX
  rcases List.mem_append.1 hX with hX | hX
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hX
    rcases hX with rfl | rfl
    · exact BAShapeO2_ggB1 Γ p q hp hq hp1 hq1 hxy hwf1 hwf2 hint
    · exact BAShapeO2_ggB2 Γ p q hp hq hp1 hq1 hxy hwf1 hwf2 hint
  · obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hX
    exact BAShapeO2_ggBD Γ hN p q hp hq hp1 hq1 hxy hwf1 hwf2 hint r hr

end Lists

/-! ## 6. Nonempty instances: the term lemmas at the R1 witnesses (`BASim3:1877-1905`), every hypothesis discharged -/

section Inst
open BASimInst

/-- `weight` at `P_W` (a blue circled loop at the internal vertex `0`) -/
example : (∀ X ∈ baPW.lw2 pW, BAScostLL baPW X) ∧ (∀ X ∈ baPW.lw4 pW, BAScostLL baPW X) :=
  ⟨BAShapeO2_lw2 baPW (by decide) pW (List.mem_cons_self ..) ⟨rfl, rfl, rfl⟩, BAShapeO2_lw4 baPW (by decide) pW (List.mem_cons_self ..) ⟨rfl, rfl, rfl⟩⟩

/-- `within` at `P_B` (`2 → 3` inside the atom `{2, 3}`): the head and the terms `lanlwD` -/
example : ∀ X ∈ BAGraph.ext 2 baPB pB.2 [bpS true (bpv 1) (bpv 1), bpS true (bpv 0) (owxEmb 2 pB.1.dst)] [bpW false (bpv 0) (bpv 1)]
    [bpM (owxEmb 2 pB.1.src) (bpv 0)] :: (lwSplit pB.2).map (BAGraph.lanlwD baPB pB), BAScostLL baPB X :=
  BAShapeO2_within baPB (by decide) pB (List.mem_cons_self ..) ⟨rfl, rfl⟩ (by decide)

/-- `edge` at `P_E` (a degree-3 internal vertex): the terms `lanlwD` -/
example : ∀ q ∈ lwSplit pE.2, BAScostLL baPE (BAGraph.lanlwD baPE pE q) :=
  fun q hq => BAShapeO2_lanlwD baPE (by decide) pE (List.mem_cons_of_mem _ (List.mem_map.2 ⟨_, List.mem_cons_self .., rfl⟩)) ⟨rfl, rfl⟩ q hq

/-- `gg` at `P_A` (`p = 2 → 1`, `q = 0 → 2`; the internal atom `{2, 3}`): `gg2` (`A1`-`A5`, `AD`) and `gg4` (`B1`, `B2`, `BD`) -/
example : (∀ X ∈ baPA.gg2 pA qA, BAScostLL baPA X) ∧ (∀ X ∈ baPA.gg4 pA qA, BAScostLL baPA X) :=
  ⟨BAShapeO2_gg2 baPA (by decide) pA qA (List.mem_cons_self ..) (List.mem_cons_self ..) ⟨rfl, rfl⟩ ⟨rfl, rfl⟩ rfl (by decide) (by decide) (by decide),
    BAShapeO2_gg4 baPA (by decide) pA qA (List.mem_cons_self ..) (List.mem_cons_self ..) ⟨rfl, rfl⟩ ⟨rfl, rfl⟩ rfl (by decide) (by decide) (by decide)⟩

/-- `ggSplit` at `P_C`, `j = 0` (`a = 2 ≠ a' = 3` in one atom): the terms `d1`-`d4` -/
example : BAScostLL baPC (BAGraph.ext 2 baPC qC.2 [bpS false (owxEmb 2 qC.1.src) (bpv 1), bpS true (bpv 0) (owxEmb 2 qC.1.dst), bpS false (bpv 1) (owxEmb 2 pC.1.dst)]
      [bpW false (bpv 0) (bpv 1)] [bpM (owxEmb 2 pC.1.src) (bpv 0)]) ∧
    BAScostLL baPC (BAGraph.ext 2 baPC qC.2 [bpS true (owxEmb 2 qC.1.src) (bpv 1)] [bpW false (bpv 0) (bpv 1)]
      [bpM (owxEmb 2 pC.1.src) (bpv 0), bpM (bpv 0) (owxEmb 2 qC.1.dst), bpM (bpv 1) (owxEmb 2 pC.1.dst)]) ∧
    BAScostLL baPC (BAGraph.ext 2 baPC qC.2 [bpS true (bpv 1) (owxEmb 2 pC.1.dst)] [bpW false (bpv 0) (bpv 1)]
      [bpM (owxEmb 2 pC.1.src) (bpv 0), bpM (bpv 0) (owxEmb 2 qC.1.dst), bpM (owxEmb 2 qC.1.src) (bpv 1)]) ∧
    BAScostLL baPC (BAGraph.ext 2 baPC qC.2 [] [bpW false (bpv 0) (bpv 1)]
      [bpM (owxEmb 2 pC.1.src) (bpv 0), bpM (bpv 0) (owxEmb 2 qC.1.dst), bpM (owxEmb 2 qC.1.src) (bpv 1), bpM (bpv 1) (owxEmb 2 pC.1.dst)]) :=
  ⟨BAShapeO2_ggSplitD1 baPC pC qC (List.mem_cons_self ..) (List.mem_cons_self ..) ⟨rfl, rfl⟩ ⟨rfl, rfl⟩ (by decide) (by decide) (by decide) (by decide),
    BAShapeO2_ggSplitD2 baPC pC qC (List.mem_cons_self ..) (List.mem_cons_self ..) ⟨rfl, rfl⟩ ⟨rfl, rfl⟩ (by decide) (by decide) (by decide),
    BAShapeO2_ggSplitD3 baPC pC qC (List.mem_cons_self ..) (List.mem_cons_self ..) ⟨rfl, rfl⟩ ⟨rfl, rfl⟩ (by decide) (by decide) (by decide),
    BAShapeO2_ggSplitD4 baPC pC qC (List.mem_cons_self ..) (List.mem_cons_self ..) ⟨rfl, rfl⟩ ⟨rfl, rfl⟩ (by decide) (by decide) (by decide)⟩

end Inst

end RBM.Graph

end
