/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Graph.AuxGraph
import RBM3D.Graph.BASizeClaim2
import RBM3D.Graph.LWPins
import RBM3D.BA.GreenSchur

/-!
# T2420 probe (BA-L3c1, the 1a probe step of the ticket; never merged, no root import)

The Lean form of the pins of `docs/reports/T2420-prove.md`, section (a), block "Pins" (namespace `RBM.Graph`): definitions,
`#check` lines and `example`s only (no theorem); a theorem of that block is a `Prop` (`X_pin`; `BAGtoAG`, `BAAnpAux` after the
band's `LWGtoAG`, `LWAnp`).  Compile: `lake env lean RBM3D/Probe/T2420Pins.lean` in the T2420 worktree.  Sections: 1 vocabulary
(`BAGraph.shadow`: every `M`- and `Ψ`-dotted edge also a waved edge; `auxVal`, `auxOrd` at the molecule centres; `BAShadowPG`);
2 the vocabulary and atom pins (`scaleatom`, `Gyiyjatom`, `Gyiyjatom2`); 3 **G3** `BAGtoAG`, `baGtoAG_E_pin`; 4 the nested
form `baAuxNested_pin` and **G4** `BAAnpAux` (owner L3d1); 5 `#check` lines; 6 nonempty instances.
-/

set_option linter.style.setOption false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option autoImplicit false

noncomputable section

namespace RBM.Graph

open RBM RBM.Gauss RBM.Gauss.Sizes

/-! ## 1. Vocabulary -/

section Vocab

variable {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

/-- `Γ` with every `M`-dotted and every `Ψ`-dotted edge also a waved edge: the molecules of `Γ` (`BAGraph.adj`: waved,
`=`-dotted, `Ψ`-dotted and `M`-dotted edges join) are the molecules of the shadow. -/
def BAGraph.shadow (Γ : BAGraph E I) : LGraph E I where
  solid := Γ.solid
  waved := Γ.waved ++ Γ.mdot.map (fun e => (⟨false, true, e.x, e.y⟩ : WEdge (E ⊕ I))) ++
    Γ.psi.map (fun e => (⟨false, true, e.x, e.y⟩ : WEdge (E ⊕ I)))
  dotted := Γ.dotted
  coeff := Γ.coeff

/-- The value of the auxiliary graph at the molecule centres (the construction of `B:436-449`, retained atoms folded in). -/
def BAGraph.auxVal {κ : Type} [Fintype κ] (Γ : BAGraph E I) (ξ : κ → κ → ℝ) (be : E → κ) : ℝ :=
  Γ.shadow.auxVal ξ be

/-- `ord(Γ^aux)` at the centre level: `#molecular solid edges - 2 n_M`. -/
def BAGraph.auxOrd (Γ : BAGraph E I) : ℤ := Γ.shadow.auxOrd

end Vocab

/-- The packed graph of the shadow (the input of the band's nested form `lwAuxNested_holds`). -/
def BAShadowPG (P : BAPGraph (Fin 2)) : PGraph (Fin 2) := ⟨P.E', P.I', P.ext, P.ext_surj, P.g.shadow⟩

/-! ## 2. The vocabulary pins and the atom pins (`scaleatom`, `Gyiyjatom`, `Gyiyjatom2`) -/

/-- The molecules of `Γ` and of its shadow agree. -/
def BAGraph_shadow_mol_pin : Prop :=
  ∀ {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I] (Γ : BAGraph E I) (v : E ⊕ I),
    Γ.shadow.mol v = Γ.mol v

/-- `n_M` of the shadow is `n_M` of `Γ`. -/
def BAGraph_shadow_nM_pin : Prop :=
  ∀ {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I] (Γ : BAGraph E I), Γ.shadow.nM = Γ.nM

/-- `(eq:ordG_BA)` against the aux order: `ord Γ - ord Γ^aux = (n_S - |𝒢_ℳ|) + 2 (n_W - n_A + n_M)`. -/
def BAGraph_scalingOrder_sub_auxOrd_pin : Prop :=
  ∀ {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I] (Γ : BAGraph E I),
    Γ.scalingOrder - Γ.auxOrd = ((Γ.nS : ℤ) - (Γ.shadow.molSolid.length : ℤ)) + 2 * ((Γ.nW : ℤ) - (Γ.nA : ℤ) + (Γ.nM : ℤ))

/-- `ord Γ^aux ≤ ord Γ` for a normal graph (`BAGraph.counters_le`). -/
def BAGraph_auxOrd_le_scalingOrder_pin : Prop :=
  ∀ {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I] (Γ : BAGraph E I), Γ.Normal →
    Γ.auxOrd ≤ Γ.scalingOrder

/-- **`scaleatom`, first half** (`B:317-318`): atom-mates share one offset (`M`, `g Ψ` are offset-diagonal). -/
def baAtom_offset_pin : Prop :=
  ∀ {d L W : ℕ} [NeZero L] [NeZero W] {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]
    (Γ : BAGraph E I) (D : BALData (Idx d L W)),
    (∀ x y, (split d L W x).2 ≠ (split d L W y).2 → D.M x y = 0 ∧ D.gPsi x y = 0) →
    ∀ ℓ : E ⊕ I → Idx d L W, Γ.term D ℓ ≠ 0 → ∀ u v, v ∈ Γ.atom u →
      (split d L W (ℓ u)).2 = (split d L W (ℓ v)).2

/-- **`scaleatom`, second half** (`B:317-318`): atom-mates are within `|E ⊕ I| r` in block distance when every `M`- and
`Ψ`-dotted edge is within `r` (no `=`-dotted edge: the part (ii) of `BAGraph.Normal`). -/
def baAtom_dist_pin : Prop :=
  ∀ {d L W : ℕ} [NeZero L] [NeZero W] {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]
    (Γ : BAGraph E I) (ℓ : E ⊕ I → Idx d L W) (r : ℝ), 0 ≤ r → (∀ e ∈ Γ.dotted, e.eq = false) →
    (∀ e ∈ Γ.mdot, (lwBdist d L W (ℓ e.x) (ℓ e.y) : ℝ) ≤ r) → (∀ e ∈ Γ.psi, (lwBdist d L W (ℓ e.x) (ℓ e.y) : ℝ) ≤ r) →
    ∀ u v, v ∈ Γ.atom u → (lwBdist d L W (ℓ u) (ℓ v) : ℝ) ≤ (Fintype.card (E ⊕ I) : ℝ) * r

/-- **`Gyiyjatom`** (`B:424`), deterministic: if every label is within `R` of its centre block `lab`, a circled solid edge is
`≤ ξ` of the centre blocks of its ends (the `hξ`-domination on `R`-balls). -/
def baAtom_sedge_xi_pin : Prop :=
  ∀ {d L W : ℕ} [NeZero L] [NeZero W] {V : Type} (D : BALData (Idx d L W)) (ξ : Zd d L → Zd d L → ℝ) (R : ℝ),
    (∀ (x y : Idx d L W) (a b : Zd d L), (zdistD d L ((split d L W x).1 - a) : ℝ) ≤ R →
      (zdistD d L ((split d L W y).1 - b) : ℝ) ≤ R → ‖D.G x y - D.M x y‖ ≤ ξ a b) →
    ∀ (ℓ : V → Idx d L W) (lab : V → Zd d L), (∀ v, (zdistD d L ((split d L W (ℓ v)).1 - lab v) : ℝ) ≤ R) →
      ∀ e : SEdge V, e.circ = true → ‖SEdge.val D.toLData ℓ e‖ ≤ ξ (lab e.src) (lab e.dst)

/-- **`Gyiyjatom2`** (`B:432`), deterministic: the decay of `S`, `S⁺` gives the indicator of `d_B ≤ r` plus the tail. -/
def baAtom_wedge_pin : Prop :=
  ∀ {d L W : ℕ} [NeZero L] [NeZero W] (K : Matrix (Idx d L W) (Idx d L W) ℂ) (C c r : ℝ), 0 ≤ c →
    (∀ x y, ‖K x y‖ ≤ C * ((W : ℝ) ^ d)⁻¹ * Real.exp (-(c * (lwBdist d L W x y : ℝ)))) →
    ∀ x y, ‖K x y‖ ≤ C * ((W : ℝ) ^ d)⁻¹ * ((if (lwBdist d L W x y : ℝ) ≤ r then 1 else 0) + Real.exp (-(c * r)))

/-! ## 3. G3: `(G_by_auxG_BA)` (`B:486-490`) -/

/-- **G3** (`B:486-490`, the twin of `LWGtoAG`, `AuxGraph.lean:979`), deterministic form: a normal BA graph whose distinct
external vertices lie in distinct molecules, data with `‖G - M‖ ≤ Ψ` entrywise (no `hM : M = m I`), the window
`W^{-d} ≤ A Ψ²`, the `LWKBound`s of `S`, `S⁺`, `M`, `g Ψ`, one decay `(C, c)` of the four kernels (`M`, `g Ψ` offset-diagonal),
and `ξ ≥ 0` dominating `‖G - M‖` on the `R`-balls, `R ≥ |E ⊕ I| r`:
`|Γ| ≤ C_Γ(K₀ A, K₁, Kd) Ψ^{ord Γ - ord Γ^aux} (W^d)^{n_M} Γ^aux_{[ℓe]} + e^{-cr/2} C'_Γ size(Γ)`. -/
def BAGtoAG (d : ℕ) : Prop :=
  3 ≤ d → ∀ (L W : ℕ) [NeZero L] [NeZero W] {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]
    (Γ : BAGraph E I), Γ.Normal → (∀ a b : E, Γ.mol (Sum.inl a) = Γ.mol (Sum.inl b) → a = b) →
    ∀ (D : BALData (Idx d L W)) (Ψ A K₀ K₁ Kd C c r R : ℝ) (ξ : Zd d L → Zd d L → ℝ),
      (∀ x y, ‖D.G x y - D.M x y‖ ≤ Ψ) → 0 ≤ A → ((W : ℝ) ^ d)⁻¹ ≤ A * Ψ ^ 2 →
      LWKBound D.S (K₀ * ((W : ℝ) ^ d)⁻¹) K₁ → LWKBound D.Sp (K₀ * ((W : ℝ) ^ d)⁻¹) K₁ →
      LWKBound D.M Kd Kd → LWKBound D.gPsi Kd Kd → 0 ≤ C → 0 < c →
      (∀ x y, ‖D.S x y‖ ≤ C * ((W : ℝ) ^ d)⁻¹ * Real.exp (-(c * (lwBdist d L W x y : ℝ)))) →
      (∀ x y, ‖D.Sp x y‖ ≤ C * ((W : ℝ) ^ d)⁻¹ * Real.exp (-(c * (lwBdist d L W x y : ℝ)))) →
      (∀ x y, ‖D.M x y‖ ≤ C * Real.exp (-(c * (lwBdist d L W x y : ℝ))) ∧
        ‖D.gPsi x y‖ ≤ C * Real.exp (-(c * (lwBdist d L W x y : ℝ)))) →
      (∀ x y, (split d L W x).2 ≠ (split d L W y).2 → D.M x y = 0 ∧ D.gPsi x y = 0) →
      0 ≤ r → (Fintype.card (E ⊕ I) : ℝ) * r ≤ R → (∀ a b, 0 ≤ ξ a b) →
      (∀ (x y : Idx d L W) (a b : Zd d L), (zdistD d L ((split d L W x).1 - a) : ℝ) ≤ R →
        (zdistD d L ((split d L W y).1 - b) : ℝ) ≤ R → ‖D.G x y - D.M x y‖ ≤ ξ a b) →
      ∀ ℓe : E → Idx d L W,
        ‖Γ.val D ℓe‖ ≤
          Γ.sizeConst (K₀ * A) K₁ Kd * Ψ ^ (Γ.scalingOrder - Γ.auxOrd) *
              (((W : ℝ) ^ d) ^ Γ.nM * Γ.auxVal ξ (fun a => (split d L W (ℓe a)).1)) +
            Real.exp (-(c * r / 2)) * Γ.sizeConst C (C * expC (d - 2) (c / 2)) (C * (1 + expC (d - 2) (c / 2))) *
              Γ.scalingSize Ψ W d L

/-- **G3 at the BA model** (constants of `(d, Λ, κ)` only; the form of `baClaimSize_E`, `BASizeClaim2.lean:566`): `D.S`,
`D.Sp`, `D.M`, `D.gPsi` are the BA matrices, `G` is any matrix with `‖G - M‖ ≤ Ψ`. -/
def baGtoAG_E_pin : Prop :=
  ∀ d : ℕ, 3 ≤ d → ∀ Λ κ : ℝ, 0 < Λ → 0 < κ → ∃ K₀ K₁ Kd C c : ℝ, 0 < K₀ ∧ 0 < K₁ ∧ 0 ≤ Kd ∧ 0 ≤ C ∧ 0 < c ∧
    ∀ (L W : ℕ) [NeZero L] [NeZero W], 3 ≤ L → ∀ (g0 E t : ℝ) (m : ℂ), 0 < g0 → g0 ≤ Λ →
      RBM.BA.BAReal d L g0 κ E m → 0 ≤ t → t < 1 →
      ∀ (E' I' : Type) [Fintype E'] [DecidableEq E'] [Fintype I'] [DecidableEq I'] (Γ : BAGraph E' I'), Γ.Normal →
        (∀ a b : E', Γ.mol (Sum.inl a) = Γ.mol (Sum.inl b) → a = b) →
        ∀ D : BALData (Idx d L W), D.S = Matrix.of (BAlwS d L W t) →
          D.Sp = Matrix.of (BAlwS d L W t) * BAlwW d L W g0 E t m → D.M = BAlwM d L W g0 E m →
          D.gPsi = (g0 : ℂ) • PsiI d L W → ∀ (Ψ A r R : ℝ) (ξ : Zd d L → Zd d L → ℝ),
          (∀ x y, ‖D.G x y - D.M x y‖ ≤ Ψ) → 0 ≤ A → ((W : ℝ) ^ d)⁻¹ ≤ A * Ψ ^ 2 →
          0 ≤ r → (Fintype.card (E' ⊕ I') : ℝ) * r ≤ R → (∀ a b, 0 ≤ ξ a b) →
          (∀ (x y : Idx d L W) (a b : Zd d L), (zdistD d L ((split d L W x).1 - a) : ℝ) ≤ R →
            (zdistD d L ((split d L W y).1 - b) : ℝ) ≤ R → ‖D.G x y - D.M x y‖ ≤ ξ a b) →
          ∀ ℓe : E' → Idx d L W,
            ‖Γ.val D ℓe‖ ≤
              Γ.sizeConst (K₀ * A) K₁ Kd * Ψ ^ (Γ.scalingOrder - Γ.auxOrd) *
                  (((W : ℝ) ^ d) ^ Γ.nM * Γ.auxVal ξ (fun a => (split d L W (ℓe a)).1)) +
                Real.exp (-(c * r / 2)) * Γ.sizeConst C (C * expC (d - 2) (c / 2)) (C * (1 + expC (d - 2) (c / 2))) *
                  Γ.scalingSize Ψ W d L

/-! ## 4. The nested form and G4 (`B:491-497`; the owner is L3d1) -/

/-- **The nested form of `Γ^aux`** (the BA twin of `LWAuxNested`, `AuxGraph.lean:1597`): the walks of `lem:localregular`
(3)-(5) of the shadow, the molecules `𝓜_x ≠ 𝓜_y`; an `NGraph` with `p` paths and `n_M` internal vertices, no ghost edge,
of order `ord Γ^aux`, whose value is the value of the aux graph for every symmetric `ξ`. -/
def baAuxNested_pin : Prop :=
  ∀ (p : ℕ) (P : BAPGraph (Fin 2)), 0 < p → (BAShadowPG P).LocReg345 p →
    P.g.mol (Sum.inl (P.ext 0)) ≠ P.g.mol (Sum.inl (P.ext 1)) →
    ∃ Γa : NGraph p P.g.nM, Γa.NoGhost ∧ Γa.IsNested ∧ Γa.ordN = P.g.auxOrd ∧
      ∀ {κ : Type} [Fintype κ] (ξ : κ → κ → ℝ), (∀ u v, ξ u v = ξ v u) → ∀ be : P.E' → κ,
        Γa.val ξ (fun _ => be (P.ext 0)) (fun _ => be (P.ext 1)) = P.g.auxVal ξ be

/-- **G4** (`B:491-497`, the pin of L3d1): the conclusion of `LWAnp` (`LWPins.lean:409`) for the aux graph of a BA graph,
with the hypotheses of `LWAnp` (`STFlow`, `LWPsiAll`, `LWXi`) and `n_M ≤ p`.  The sums over the non-centre atoms are not in
`auxVal` (centre level), so the `NGraph` is `baAuxNested_pin`'s.  The form on the BA flow carrier is fixed by L3c3's 1a. -/
def BAAnpAux (d : ℕ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ (p : ℕ) (P : BAPGraph (Fin 2)), 0 < p → P.g.nM ≤ p → (BAShadowPG P).LocReg345 p →
      P.g.mol (Sum.inl (P.ext 0)) ≠ P.g.mol (Sum.inl (P.ext 1)) →
      ∀ (ε₀ C₁ C₂ C₃ : ℝ) (Cc : ℝ → ℝ), ∃ c : ℝ, 0 < c ∧
        ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z →
          ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ lemT (z n)) →
            ∀ Φ : ℕ → ℝ → ℝ, LWPsiAll sz ε₀ C₁ C₂ C₃ Cc Φ →
              ∀ ξ : ∀ n, Zd d (sz.L n) → Zd d (sz.L n) → sz.SeqΩ → ℝ, LWXi sz (STflowE z) t Φ ξ →
                Prec sz (U := fun n => Zd d (sz.L n) × Zd d (sz.L n))
                  (fun n ab ω => P.g.auxVal (fun α β => ξ n α β ω) (fun e => if e = P.ext 0 then ab.1 else ab.2))
                  (fun n ab _ => ((((sz.W n : ℕ) : ℝ) ^ d) * etaT (STflowE z n) (t n))⁻¹ ^ P.g.nM *
                    Φ n (c * ((zdistInf d (sz.L n) (ab.1 - ab.2) : ℕ) : ℝ)) ^ p * Φ n 0 ^ (P.g.auxOrd - p))

/-! ## 5. `#check` lines -/

#check @BAGraph.shadow
#check @BAGraph.auxVal
#check @BAGraph.auxOrd
#check @BAShadowPG
#check BAGraph_shadow_mol_pin
#check BAGraph_shadow_nM_pin
#check BAGraph_scalingOrder_sub_auxOrd_pin
#check BAGraph_auxOrd_le_scalingOrder_pin
#check baAtom_offset_pin
#check baAtom_dist_pin
#check baAtom_sedge_xi_pin
#check baAtom_wedge_pin
#check BAGtoAG
#check baGtoAG_E_pin
#check baAuxNested_pin
#check BAAnpAux

/-! ## 6. Nonempty instances: `d = 3`, `L = 4`, `W = 2`, `t = 1/2`, the flow point `P : FlowPt 4 10` -/

namespace T2420Inst

/-- The graph `G*` of the preflight instance: externals `a = inl 0`, `b = inl 1`, internals `u₁ .. u₅ = inr 0 .. inr 4`;
circled solid edges `a → u₁`, `u₅ → b` (red), `u₃ → u₂`, `u₁ → u₄`; waved `S(a,u₃)`, `S⁺(u₂,u₄)`, `S(u₁,u₅)`;
`M̄`-dotted `u₁u₂`, `Ψ`-dotted `u₄u₅`.  Atoms `{a}, {b}, {u₁,u₂}, {u₃}, {u₄,u₅}`; molecules `{a,u₃}, {b}, {u₁,u₂,u₄,u₅}`. -/
def Gstar : BAGraph (Fin 2) (Fin 5) where
  solid := [⟨true, true, .inl 0, .inr 0⟩, ⟨false, true, .inr 4, .inl 1⟩, ⟨true, true, .inr 2, .inr 1⟩,
    ⟨true, true, .inr 0, .inr 3⟩]
  waved := [⟨false, true, .inl 0, .inr 2⟩, ⟨true, true, .inr 1, .inr 3⟩, ⟨false, true, .inr 0, .inr 4⟩]
  dotted := []
  coeff := 1
  psi := [⟨.inr 3, .inr 4⟩]
  mdot := [⟨false, .inr 0, .inr 1⟩]

/-- The packed BA graph of the locally standard graph `localReg2_inst_Q` (two external, two internal vertices, no `M`- or
`Ψ`-dotted edge: its shadow is the band graph), for the nested form and G4. -/
def baPQ : BAPGraph (Fin 2) := ⟨Fin 2, Fin 2, id, Function.surjective_id, BAGraph.ofLGraph localReg2_inst_Q⟩

end T2420Inst

open T2420Inst in
/-- The counters, the order comparison and the exponent of `G*`, computed: `n_S = 4`, `n_W = 3`, `n_A = 3`, `n_M = 1`,
`|𝒢_ℳ| = 3`, `ord Γ = 4`, `ord Γ^aux = 1`, exponent `3 = (n_S - |𝒢_ℳ|) + 2 (n_W - n_A + n_M)`; and the four vocabulary pins
applied at `G*` (`Normal`: no `=`-dotted edge, every solid edge circled). -/
example (p1 : BAGraph_shadow_mol_pin) (p2 : BAGraph_shadow_nM_pin) (p3 : BAGraph_scalingOrder_sub_auxOrd_pin)
    (p4 : BAGraph_auxOrd_le_scalingOrder_pin) : (∀ v, Gstar.shadow.mol v = Gstar.mol v) ∧ Gstar.shadow.nM = Gstar.nM ∧
    Gstar.scalingOrder - Gstar.auxOrd = ((Gstar.nS : ℤ) - (Gstar.shadow.molSolid.length : ℤ)) +
      2 * ((Gstar.nW : ℤ) - (Gstar.nA : ℤ) + (Gstar.nM : ℤ)) ∧ Gstar.auxOrd ≤ Gstar.scalingOrder ∧
    (Gstar.nS = 4 ∧ Gstar.nW = 3 ∧ Gstar.nA = 3 ∧ Gstar.nM = 1) ∧ Gstar.shadow.molSolid.length = 3 ∧
    Gstar.shadow.nM = 1 ∧ Gstar.scalingOrder = 4 ∧ Gstar.auxOrd = 1 ∧ Gstar.scalingOrder - Gstar.auxOrd = 3 := by
  have h1 : Gstar.shadow.molSolid.length = 3 := by rw [auxGraph_molSolid_length]; decide
  have h2 : Gstar.shadow.nM = 1 := by decide
  have h3 : Gstar.nS = 4 ∧ Gstar.nW = 3 ∧ Gstar.nA = 3 ∧ Gstar.nM = 1 := by decide
  have h4 : Gstar.scalingOrder = 4 := by simp [BAGraph.scalingOrder, BAGraph.counters, h3.1, h3.2.1, h3.2.2.1, ord]
  have h5 : Gstar.auxOrd = 1 := by simp [BAGraph.auxOrd, LGraph.auxOrd, h1, h2, ord]
  exact ⟨p1 Gstar, p2 Gstar, p3 Gstar, p4 Gstar ⟨by decide, by decide⟩, h3, h1, h2, h4, h5, by rw [h4, h5]; norm_num⟩

open RBM.BA.MFixedPointInst BASizeClaimInst2 T2420Inst in
/-- **Instance of G3** (`BAGtoAG 3`) at `G*`, the BA data `D0` of `BASizeClaim2` (`G = M + 1/100`), `Ψ = 1/100`, window
`W^{-3} = 1/8 ≤ A Ψ²`, `A = 2000`, `r = 1`, `R = 7 = |E ⊕ I| r`, `ξ ≡ 1/100`: `(K₀, K₁, Kd)` are `baKBound_E`'s, `(C, c)` one decay
of `S`, `S⁺` (`baSpDecay`), `M` (`BAMB_decay_large`) and `g Ψ`; every deterministic hypothesis is discharged.  The second
conjunct is `baAtom_offset_pin` (`scaleatom`) at the same data (`M`, `g Ψ` offset-diagonal, from `BAMres_fine_apply`). -/
example (h : BAGtoAG 3) (hO : baAtom_offset_pin) :
    (∃ K₀ K₁ Kd C c : ℝ, 0 < K₀ ∧ 0 < K₁ ∧ 0 ≤ Kd ∧ 0 ≤ C ∧ 0 < c ∧
      ‖Gstar.val D0 ellInst‖ ≤
        Gstar.sizeConst (K₀ * 2000) K₁ Kd * (1 / 100 : ℝ) ^ (Gstar.scalingOrder - Gstar.auxOrd) *
            ((((2 : ℕ) : ℝ) ^ 3) ^ Gstar.nM * Gstar.auxVal (fun _ _ => (1 / 100 : ℝ)) (fun a => (split 3 4 2 (ellInst a)).1)) +
          Real.exp (-(c * 1 / 2)) * Gstar.sizeConst C (C * expC (3 - 2) (c / 2)) (C * (1 + expC (3 - 2) (c / 2))) *
            Gstar.scalingSize (1 / 100) 2 3 4) ∧
    ∀ ℓ : Fin 2 ⊕ Fin 5 → Idx 3 4 2, Gstar.term D0 ℓ ≠ 0 → ∀ u v, v ∈ Gstar.atom u →
      (split 3 4 2 (ℓ u)).2 = (split 3 4 2 (ℓ v)).2 := by
  have hκ : 0 < P.m0.im := P.real.1.1
  have hw : ((P.E : ℂ) + P.m0).im ≠ 0 := by simpa using P.real.1.1.ne'
  obtain ⟨K₀, K₁, Kd, hK₀, hK₁, hKd, hK⟩ := baKBound_E 3 le_rfl 10 P.m0.im (by norm_num) hκ
  obtain ⟨hS, hSp, hM, hP⟩ := hK 4 2 (by norm_num) P.g0 P.E (1 / 2) P.m0 P.g0_pos P.g0_le P.real (by norm_num) (by norm_num)
  obtain ⟨C₁, c₁, hC₁, hc₁, hdec⟩ := baSpDecay 3 le_rfl 10 P.m0.im (by norm_num) hκ
  obtain ⟨hdS, hdSp⟩ := hdec 4 2 (by norm_num) P.g0 P.E (1 / 2) P.m0 P.g0_pos P.g0_le P.real (by norm_num) (by norm_num)
  have hc₂ := RBM.BA.BAct_rate_pos 3 10 P.m0.im (by norm_num) (by norm_num) hκ
  set c₂ := RBM.BA.BAct_rate 3 10 P.m0.im with hc₂def
  set C : ℝ := max (max C₁ c₂⁻¹) (P.g0 * Real.exp 1) with hCdef
  set c : ℝ := min (min c₁ c₂) 1 with hcdef
  have hC0 : 0 ≤ C := le_max_of_le_left (le_max_of_le_left hC₁.le)
  have hc0 : 0 < c := lt_min (lt_min hc₁ hc₂) one_pos
  have hmono : ∀ (v w u C' c' : ℝ), 0 ≤ w → 0 ≤ u → C' ≤ C → c ≤ c' → v ≤ C' * w * Real.exp (-(c' * u)) →
      v ≤ C * w * Real.exp (-(c * u)) := by
    intro v w u C' c' hw hu hC hc hv
    refine hv.trans (mul_le_mul (mul_le_mul_of_nonneg_right hC hw) (Real.exp_le_exp.2 ?_) (Real.exp_pos _).le
      (mul_nonneg hC0 hw))
    nlinarith
  have hPsi : ∀ x y : Idx 3 4 2, PsiI 3 4 2 x y = if (split 3 4 2 x).2 = (split 3 4 2 y).2 then
      (if Adj 3 4 (split 3 4 2 x).1 (split 3 4 2 y).1 then (1 : ℂ) else 0) else 0 := by
    intro x y
    simp only [PsiI, PsiV, Matrix.submatrix_apply, Matrix.kroneckerMap_apply, Matrix.one_apply, PsiB, Matrix.of_apply]
    have h1 : splitEquiv 3 4 2 x = split 3 4 2 x := rfl
    have h2 : splitEquiv 3 4 2 y = split 3 4 2 y := rfl
    rw [h1, h2]
    by_cases h : (split 3 4 2 x).2 = (split 3 4 2 y).2 <;> simp [h]
  have hMapp : ∀ x y : Idx 3 4 2, D0.M x y = if (split 3 4 2 x).2 = (split 3 4 2 y).2 then
      RBM.BA.BAMB 3 4 P.g0 (P.E : ℂ) P.m0 (split 3 4 2 x).1 (split 3 4 2 y).1 else 0 :=
    fun x y => RBM.BA.BAMres_fine_apply 3 4 2 P.g0 (P.E : ℂ) P.m0 hw x y
  have hoff : ∀ x y : Idx 3 4 2, (split 3 4 2 x).2 ≠ (split 3 4 2 y).2 → D0.M x y = 0 ∧ D0.gPsi x y = 0 := by
    intro x y ho
    refine ⟨?_, ?_⟩
    · rw [hMapp]; simp [ho]
    · show ((P.g0 : ℂ) • PsiI 3 4 2) x y = 0
      rw [Matrix.smul_apply, hPsi]; simp [ho]
  refine ⟨⟨K₀, K₁, Kd, C, c, hK₀, hK₁, hKd, hC0, hc0, h le_rfl 4 2 Gstar ⟨by decide, by decide⟩ (by decide) D0 (1 / 100) 2000
    K₀ K₁ Kd C c 1 7 (fun _ _ => 1 / 100) D0_hG (by norm_num) (by norm_num) hS hSp hM hP hC0 hc0 ?_ ?_ ?_ hoff
    (by norm_num) (by simp) (fun _ _ => by norm_num) (fun x y _ _ _ _ => by simpa using D0_hG x y) ellInst⟩,
    fun ℓ hℓ u v hv => hO Gstar D0 hoff ℓ hℓ u v hv⟩
  · intro x y
    exact hmono _ _ _ C₁ c₁ (by positivity) (Nat.cast_nonneg _) (le_max_of_le_left (le_max_left _ _))
      ((min_le_left _ _).trans (min_le_left _ _)) (hdS x y)
  · intro x y
    exact hmono _ _ _ C₁ c₁ (by positivity) (Nat.cast_nonneg _) (le_max_of_le_left (le_max_left _ _))
      ((min_le_left _ _).trans (min_le_left _ _)) (hdSp x y)
  · intro x y
    refine ⟨?_, ?_⟩
    · rw [hMapp]
      split_ifs with ho
      · have := RBM.BA.BAMB_decay_large 3 4 (by norm_num) (by norm_num) 10 P.g0 P.m0.im P.E P.m0 (by norm_num) P.g0_pos
          P.g0_le hκ P.real (split 3 4 2 x).1 (split 3 4 2 y).1
        have h1 := hmono _ 1 (lwBdist 3 4 2 x y : ℝ) c₂⁻¹ c₂ one_pos.le (Nat.cast_nonneg _)
          (le_max_of_le_left (le_max_right _ _)) ((min_le_left _ _).trans (min_le_right _ _))
          (by simpa [neg_mul, lwBdist] using this)
        simpa using h1
      · rw [norm_zero]; positivity
    · show ‖((P.g0 : ℂ) • PsiI 3 4 2) x y‖ ≤ _
      rw [Matrix.smul_apply, smul_eq_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos P.g0_pos, hPsi]
      split_ifs with ho ha
      · have hd : (lwBdist 3 4 2 x y : ℝ) = 1 := by
          simp only [lwBdist]
          exact_mod_cast ha
        rw [hd, norm_one, mul_one, mul_one]
        have h1 : P.g0 * Real.exp 1 ≤ C := le_max_right _ _
        have h2 : 1 ≤ Real.exp (-c) * Real.exp 1 := by
          rw [← Real.exp_add]
          exact Real.one_le_exp (by linarith [min_le_right (min c₁ c₂) 1])
        nlinarith [Real.exp_pos (-c), Real.exp_pos 1, P.g0_pos]
      all_goals simp only [norm_zero, mul_zero]; positivity

open RBM.BA.MFixedPointInst BASizeClaimInst2 T2420Inst in
/-- **Instance of the model form** `baGtoAG_E_pin` at the same data (`Λ = 10`, `κ = Im m₀`, `t = 1/2`). -/
example (h : baGtoAG_E_pin) : ∃ K₀ K₁ Kd C c : ℝ, 0 < K₀ ∧ 0 < K₁ ∧ 0 ≤ Kd ∧ 0 ≤ C ∧ 0 < c ∧
    ‖Gstar.val D0 ellInst‖ ≤
      Gstar.sizeConst (K₀ * 2000) K₁ Kd * (1 / 100 : ℝ) ^ (Gstar.scalingOrder - Gstar.auxOrd) *
          ((((2 : ℕ) : ℝ) ^ 3) ^ Gstar.nM * Gstar.auxVal (fun _ _ => (1 / 100 : ℝ)) (fun a => (split 3 4 2 (ellInst a)).1)) +
        Real.exp (-(c * 1 / 2)) * Gstar.sizeConst C (C * expC (3 - 2) (c / 2)) (C * (1 + expC (3 - 2) (c / 2))) *
          Gstar.scalingSize (1 / 100) 2 3 4 := by
  obtain ⟨K₀, K₁, Kd, C, c, hK₀, hK₁, hKd, hC, hc, H⟩ := h 3 le_rfl 10 P.m0.im (by norm_num) P.real.1.1
  exact ⟨K₀, K₁, Kd, C, c, hK₀, hK₁, hKd, hC, hc, H 4 2 (by norm_num) P.g0 P.E (1 / 2) P.m0 P.g0_pos P.g0_le P.real
    (by norm_num) (by norm_num) (Fin 2) (Fin 5) Gstar ⟨by decide, by decide⟩ (by decide) D0 rfl rfl rfl rfl (1 / 100) 2000 1 7
    (fun _ _ => 1 / 100) D0_hG (by norm_num) (by norm_num) (by norm_num) (by simp) (fun _ _ => by norm_num)
    (fun x y _ _ _ _ => by simpa using D0_hG x y) ellInst⟩

open BASizeClaimInst2 T2420Inst in
/-- **Instances of `baAtom_sedge_xi_pin`** (`Gyiyjatom`; `lab v = [ℓ v]`, `ξ ≡ 1/100`, `R = 7`) and of `baAtom_wedge_pin`
(`Gyiyjatom2`; `K = D0.S`, the decay of `baSpDecay`, `r = 1`). -/
example (hX : baAtom_sedge_xi_pin) (hW : baAtom_wedge_pin) (ℓ : Fin 2 ⊕ Fin 5 → Idx 3 4 2) :
    (∀ e ∈ Gstar.solid, ‖SEdge.val D0.toLData ℓ e‖ ≤ 1 / 100) ∧ ∃ C c : ℝ, 0 < c ∧ ∀ x y : Idx 3 4 2, ‖D0.S x y‖ ≤
      C * (((2 : ℕ) : ℝ) ^ 3)⁻¹ * ((if (lwBdist 3 4 2 x y : ℝ) ≤ 1 then 1 else 0) + Real.exp (-(c * 1))) := by
  refine ⟨fun e he => hX D0 (fun _ _ => 1 / 100) 7 (fun x y a b _ _ => by simpa using D0_hG x y) ℓ
    (fun v => (split 3 4 2 (ℓ v)).1) (fun v => by simp) e ((⟨by decide, by decide⟩ : Gstar.Normal).2 e he), ?_⟩
  obtain ⟨C, c, -, hc, hdec⟩ := baSpDecay 3 le_rfl 10 RBM.BA.MFixedPointInst.P.m0.im (by norm_num)
    RBM.BA.MFixedPointInst.P.real.1.1
  exact ⟨C, c, hc, hW D0.S C c 1 hc.le (hdec 4 2 (by norm_num) _ _ (1 / 2) _ RBM.BA.MFixedPointInst.P.g0_pos
    RBM.BA.MFixedPointInst.P.g0_le RBM.BA.MFixedPointInst.P.real (by norm_num) (by norm_num)).1⟩

open BASizeClaimInst2 T2420Inst in
/-- **Instance of `baAtom_dist_pin`** (`scaleatom`, the distance half) at `G*`, `r = 1`: the labels of the `M̄`-dotted pair `u₁u₂`
(`0`, `(2,0,0)`) and of the `Ψ`-dotted pair `u₄u₅` (`0`, `(0,2,0)`) are at block distance 1; atom-mates are within `7 r`. -/
example (h : baAtom_dist_pin) : ∃ ℓ : Fin 2 ⊕ Fin 5 → Idx 3 4 2, (lwBdist 3 4 2 (ℓ (.inr 0)) (ℓ (.inr 1)) : ℝ) = 1 ∧
    ∀ u v, v ∈ Gstar.atom u → (lwBdist 3 4 2 (ℓ u) (ℓ v) : ℝ) ≤ 7 * 1 := by
  let ℓ : Fin 2 ⊕ Fin 5 → Idx 3 4 2 := Sum.elim ellInst ![fun _ => 0, ![2, 0, 0], fun _ => 0, fun _ => 0, ![0, 2, 0]]
  have h1 : lwBdist 3 4 2 (ℓ (.inr 0)) (ℓ (.inr 1)) = 1 := by decide
  have h2 : lwBdist 3 4 2 (ℓ (.inr 3)) (ℓ (.inr 4)) = 1 := by decide
  refine ⟨ℓ, by exact_mod_cast h1, fun u v hv => ?_⟩
  have := h Gstar ℓ 1 zero_le_one (fun e he => by simp [Gstar] at he) (fun e he => by
      simp only [Gstar, List.mem_singleton] at he; subst he; exact_mod_cast h1.le)
    (fun e he => by simp only [Gstar, List.mem_singleton] at he; subst he; exact_mod_cast h2.le) u v hv
  simpa using this

open T2420Inst in
/-- **Instance of the nested form** at `baPQ` (`p = 2`, `n_M = 1 ≤ p`; `(BAShadowPG baPQ).LocReg345 2` is, up to definitional
unfolding, `localReg2_inst_Q_locReg345`, `LocalRegular2.lean:2036`). -/
example (hN : baAuxNested_pin) : ∃ Γa : NGraph 2 baPQ.g.nM, Γa.NoGhost ∧ Γa.IsNested ∧ Γa.ordN = baPQ.g.auxOrd := by
  obtain ⟨Γa, h1, h2, h3, -⟩ := hN 2 baPQ (by norm_num) localReg2_inst_Q_locReg345 (by decide)
  exact ⟨Γa, h1, h2, h3⟩

open RBM.Gauss.LWInst RBM.Gauss.SizesInst RBM.Gauss.InductionDefsInst T2420Inst in
/-- **Instance of G4** (`BAAnpAux 3`) at `baPQ`, `p = 2`, the band data of `inst_Anp` (`LWPins.lean:699`: `sz0`, `z0`,
`flow_z0`, `tInst`, `Φ0`, `psiAll0`); the edge variables `ξ` with `(eq:Gbyxi3)` stay a hypothesis (the pin of stage G / L3c3). -/
example (h : BAAnpAux 3) (ξ : ∀ n, Zd 3 (sz0.L n) → Zd 3 (sz0.L n) → sz0.SeqΩ → ℝ) (hξ : LWXi sz0 (STflowE z0) tInst Φ0 ξ) :
    ∃ c : ℝ, 0 < c ∧ Prec sz0 (U := fun n => Zd 3 (sz0.L n) × Zd 3 (sz0.L n))
      (fun n ab ω => baPQ.g.auxVal (fun α β => ξ n α β ω) (fun e => if e = baPQ.ext 0 then ab.1 else ab.2))
      (fun n ab _ => ((((sz0.W n : ℕ) : ℝ) ^ 3) * etaT (STflowE z0 n) (tInst n))⁻¹ ^ baPQ.g.nM *
        Φ0 n (c * ((zdistInf 3 (sz0.L n) (ab.1 - ab.2) : ℕ) : ℝ)) ^ 2 * Φ0 n 0 ^ (baPQ.g.auxOrd - (2 : ℕ))) := by
  obtain ⟨c, hc, H⟩ := h le_rfl (1 / 10) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) 2 baPQ (by norm_num)
    (by decide) localReg2_inst_Q_locReg345 (by decide) (1 / 20) 2 2 1 (fun _ => 1)
  exact ⟨c, hc, H (1 / 6) sz0 z0 flow_z0 tInst tInst_range.1 tInst_range.2 Φ0 psiAll0 ξ hξ⟩

end RBM.Graph
