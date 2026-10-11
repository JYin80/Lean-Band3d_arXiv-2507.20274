/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Graph.LWSizeClaim
import RBM3D.Graph.BAExpandW
import RBM3D.BA.GreenSchur
import RBM3D.BA.Prop5Short
import RBM3D.BA.MFixedPoint

/-!
# T2412 probe (BA-L3c2 design gate, probe step of CONTROL H205; never merged, no root import)

The Lean form of the pins T1-T4 of `docs/reports/T2412-prove.md`, section (a), block "Pins".  Namespace `RBM.Graph`.
The file has definitions, `#check` lines and one `example` only (no theorem, no placeholder proof): the statement of a
theorem `X` of the pins is the `Prop` `X_pin` here (as `BAProp5s`, `BA/FlowPins.lean:184`, is the `Prop` of `baProp5s_holds`).
Stage 1b proves the theorem `X` with the binders of `X_pin` as arguments.  Compile:
`lake env lean RBM3D/Probe/T2412Pins.lean` in the T2412 worktree.

* Section 1: the vocabulary the pins need: `BAGraph.sizeConst` (the pinned constant), the edge index `BAGraph.Jx`
  `= waved ⊕ mdot ⊕ psi` and its endpoints `BAGraph.edgeEnds` (the pin text says "as `LGraph.exists_forest`").
* Section 2: T1, the kernel edges: `baSp_eq_pin`, `baSpDecay_pin`, `baKBound_E_pin`.
* Section 3: T2, peeling and atomic forest: `BASizeClaim_forest_sum_le_pin`, `BAGraph_exists_forest_pin`, `BAGraph_counters_le_pin`.
* Section 4: T3, `claim:size`: `baClaimSize_pin`, `baClaimSizeG_pin` (no `hM`).
* Section 5: T4, model form and tails: `baClaimSize_E_pin`, `baClaimSizeG_E_pin`, `baSpTail_E_pin`, `baMTail_E_pin`, `baTail_log_pin`.
* Section 6: `#check` lines.  Section 7: one nonempty instance (an `example`) at `d = 3`, `L = 4`, `W = 2`, the flow point `P : FlowPt 4 10`.

Reading of the pin text where it is not Lean: `ι, I, E, J` of the forest pin are universe polymorphic; the graph pins use `E I : Type`
(as `BAGraph.partition`, `Graph/BAVocab.lean:229`); `baSpDecay`, `baKBound_E` quantify `L W` after `d Λ κ` as `lwSpOf_decay`, `lwKBound_E`; `baSp_eq` has no `Λ`.
-/

set_option linter.style.setOption false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option autoImplicit false

noncomputable section

open Matrix

namespace RBM.Graph

open RBM RBM.Gauss

universe u₁ u₂ u₃ u₄

/-! ## 1. Vocabulary -/

/-- `C_Γ = ‖coeff‖ K₁^{n_A - n_M} K₀^{n_W - (n_A - n_M)} Kd^{#M-dotted + #Ψ-dotted}` (the pin of section (a), R9). -/
def BAGraph.sizeConst {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]
    (Γ : BAGraph E I) (K₀ K₁ Kd : ℝ) : ℝ :=
  ‖Γ.coeff‖ * K₁ ^ (Γ.nA - Γ.nM) * K₀ ^ (Γ.nW - (Γ.nA - Γ.nM)) * Kd ^ (Γ.mdot.length + Γ.psi.length)

/-- The edge index `J = waved ⊕ mdot ⊕ psi` of the molecular forest. -/
abbrev BAGraph.Jx {E I : Type} (Γ : BAGraph E I) : Type :=
  Fin Γ.waved.length ⊕ Fin Γ.mdot.length ⊕ Fin Γ.psi.length

/-- The endpoints `(x, y)` of an edge of `J`. -/
def BAGraph.edgeEnds {E I : Type} (Γ : BAGraph E I) : Γ.Jx → (E ⊕ I) × (E ⊕ I)
  | Sum.inl j => ((Γ.waved.get j).x, (Γ.waved.get j).y)
  | Sum.inr (Sum.inl j) => ((Γ.mdot.get j).x, (Γ.mdot.get j).y)
  | Sum.inr (Sum.inr j) => ((Γ.psi.get j).x, (Γ.psi.get j).y)

/-! ## 2. T1: the kernel edges `S`, `S⁺ = S W` -/

/-- **T1 `baSp_eq`**: `S⁺ = S W = t · lift(Θ^{(+,+)})` with `W = (1 - M⁺S)⁻¹` (`BAlwW`), `lift = lwLift`. -/
def baSp_eq_pin : Prop :=
  ∀ (d L W : ℕ) [NeZero L] [NeZero W], 3 ≤ L → ∀ (g0 κ E t : ℝ) (m : ℂ), RBM.BA.BAReal d L g0 κ E m → 0 ≤ t → t < 1 →
    Matrix.of (BAlwS d L W t) * BAlwW d L W g0 E t m = (t : ℂ) • lwLift d L W (RBM.BA.BATheta d L g0 E m t true true)

/-- **T1 `baSpDecay`** (BA `(eq:estSpm-W)`): `|S_{xy}|, |(S W)_{xy}| ≤ C W^{-d} e^{-c d_B(x,y)}`. -/
def baSpDecay_pin : Prop :=
  ∀ d : ℕ, 3 ≤ d → ∀ Λ κ : ℝ, 0 < Λ → 0 < κ → ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
    ∀ (L W : ℕ) [NeZero L] [NeZero W], 3 ≤ L → ∀ (g0 E t : ℝ) (m : ℂ), 0 < g0 → g0 ≤ Λ → RBM.BA.BAReal d L g0 κ E m →
      0 ≤ t → t < 1 →
      (∀ x y : Idx d L W, ‖Matrix.of (BAlwS d L W t) x y‖ ≤
        C * ((W : ℝ) ^ d)⁻¹ * Real.exp (-(c * (lwBdist d L W x y : ℝ)))) ∧
      (∀ x y : Idx d L W, ‖(Matrix.of (BAlwS d L W t) * BAlwW d L W g0 E t m) x y‖ ≤
        C * ((W : ℝ) ^ d)⁻¹ * Real.exp (-(c * (lwBdist d L W x y : ℝ))))

/-- **T1 `baKBound_E`**: the `LWKBound` constants of `S`, `S W`, `M`, `g₀ Ψ`, depending on `(d, Λ, κ)` only. -/
def baKBound_E_pin : Prop :=
  ∀ d : ℕ, 3 ≤ d → ∀ Λ κ : ℝ, 0 < Λ → 0 < κ → ∃ K₀ K₁ Kd : ℝ, 0 < K₀ ∧ 0 < K₁ ∧ 0 ≤ Kd ∧
    ∀ (L W : ℕ) [NeZero L] [NeZero W], 3 ≤ L → ∀ (g0 E t : ℝ) (m : ℂ), 0 < g0 → g0 ≤ Λ → RBM.BA.BAReal d L g0 κ E m →
      0 ≤ t → t < 1 →
      LWKBound (Matrix.of (BAlwS d L W t)) (K₀ * ((W : ℝ) ^ d)⁻¹) K₁ ∧
      LWKBound (Matrix.of (BAlwS d L W t) * BAlwW d L W g0 E t m) (K₀ * ((W : ℝ) ^ d)⁻¹) K₁ ∧
      LWKBound (BAlwM d L W g0 E m) Kd Kd ∧ LWKBound ((g0 : ℂ) • PsiI d L W) Kd Kd

/-! ## 3. T2: the peeling bound with per-edge constants, the molecular forest with atoms, the counters -/

/-- **T2 `BASizeClaim_forest_sum_le`**: the peeling `lwForest_sum_le` (`LWSizeClaim.lean:637`) with per-edge `(a_j, K_j)`:
`N^{|C|} Σ_ℓ ∏_j f_j ≤ N^{|I|} ∏_{c ∈ C} K_{e(c)} ∏_{j ∉ e(C)} a_j`. -/
def BASizeClaim_forest_sum_le_pin : Prop :=
  ∀ {ι : Type u₁} {I : Type u₂} {E : Type u₃} {J : Type u₄} [Fintype ι] [DecidableEq ι] [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] [Nonempty ι] (ℓe : E → ι) (u v : J → E ⊕ I) (f : J → ι → ι → ℝ) (a K : J → ℝ),
    (∀ j x y, 0 ≤ f j x y) → (∀ j x y, f j x y ≤ a j) → (∀ j x, ∑ y, f j x y ≤ K j) → (∀ j y, ∑ x, f j x y ≤ K j) →
    ∀ (C : Finset I) (par : I → E ⊕ I) (edge : I → J) (ρ : I → ℕ), Set.InjOn edge C →
    (∀ c ∈ C, (u (edge c) = Sum.inr c ∧ v (edge c) = par c) ∨ (v (edge c) = Sum.inr c ∧ u (edge c) = par c)) →
    (∀ c ∈ C, ∀ w, par c = Sum.inr w → ρ w < ρ c) →
    (Fintype.card ι : ℝ) ^ C.card * ∑ ℓ : I → ι, ∏ j, f j (Sum.elim ℓe ℓ (u j)) (Sum.elim ℓe ℓ (v j)) ≤
      (Fintype.card ι : ℝ) ^ Fintype.card I * (∏ c ∈ C, K (edge c)) * ∏ j ∈ (C.image edge)ᶜ, a j

open Classical in
/-- **T2 `BAGraph.exists_forest`**: the molecular forest with atoms (`LGraph.exists_forest`, `LWSizeClaim.lean:725`, with
`J = waved ⊕ mdot ⊕ psi`): `|C| + n_M = |I|`, and the waved tree edges number `n_A - n_M`. -/
def BAGraph_exists_forest_pin : Prop :=
  ∀ {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I] (Γ : BAGraph E I),
    (∀ e ∈ Γ.dotted, e.eq = false) →
    ∃ (C : Finset I) (par : I → E ⊕ I) (edge : I → Option Γ.Jx) (ρ : I → ℕ),
      C.card + Γ.nM = Fintype.card I ∧
      (C.filter fun c => ∃ j, edge c = some (Sum.inl j)).card + Γ.nM = Γ.nA ∧
      (∀ c ∈ C, ∀ w, par c = Sum.inr w → ρ w < ρ c) ∧
      (∀ c ∈ C, ∃ j, edge c = some j ∧
        (((Γ.edgeEnds j).1 = Sum.inr c ∧ (Γ.edgeEnds j).2 = par c) ∨
         ((Γ.edgeEnds j).2 = Sum.inr c ∧ (Γ.edgeEnds j).1 = par c))) ∧
      (∀ c₁ ∈ C, ∀ c₂ ∈ C, edge c₁ = edge c₂ → c₁ = c₂)

/-- **T2 `BAGraph.counters_le`**: `n_M ≤ n_A` and `n_A - n_M ≤ n_W` for a graph without `=`-dotted edges. -/
def BAGraph_counters_le_pin : Prop :=
  ∀ {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I] (Γ : BAGraph E I),
    (∀ e ∈ Γ.dotted, e.eq = false) → Γ.nM ≤ Γ.nA ∧ Γ.nA - Γ.nM ≤ Γ.nW

/-! ## 4. T3: `claim:size` at BA, deterministic form (no `hM : M = m I`) -/

/-- **T3 `baClaimSize`**: `‖Γ.val‖ ≤ C_Γ size(Γ)` for a normal BA graph; the hypothesis on `G` is `‖G - M‖ ≤ Ψ` entrywise. -/
def baClaimSize_pin : Prop :=
  ∀ {d L W : ℕ} [NeZero L] [NeZero W] {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]
    (Γ : BAGraph E I), Γ.Normal → ∀ (D : BALData (Idx d L W)) {Ψ K₀ K₁ Kd : ℝ},
    (∀ x y, ‖D.G x y - D.M x y‖ ≤ Ψ) → LWKBound D.S (K₀ * ((W : ℝ) ^ d)⁻¹) K₁ →
    LWKBound D.Sp (K₀ * ((W : ℝ) ^ d)⁻¹) K₁ → LWKBound D.M Kd Kd → LWKBound D.gPsi Kd Kd →
    ∀ ℓe : E → Idx d L W, ‖Γ.val D ℓe‖ ≤ Γ.sizeConst K₀ K₁ Kd * Γ.scalingSize Ψ W d L

/-- **T3 `baClaimSizeG`**: the general graph, through `BAGraph.partition` (`BAGraph.val_eq_partition`, unconditional). -/
def baClaimSizeG_pin : Prop :=
  ∀ {d L W : ℕ} [NeZero L] [NeZero W] {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]
    (Γ : BAGraph E I) (D : BALData (Idx d L W)) {Ψ K₀ K₁ Kd : ℝ}, 0 ≤ K₀ → 0 ≤ K₁ → 0 ≤ Kd →
    (∀ x y, ‖D.G x y - D.M x y‖ ≤ Ψ) → LWKBound D.S (K₀ * ((W : ℝ) ^ d)⁻¹) K₁ →
    LWKBound D.Sp (K₀ * ((W : ℝ) ^ d)⁻¹) K₁ → LWKBound D.M Kd Kd → LWKBound D.gPsi Kd Kd →
    ∀ ℓe : E → Idx d L W,
      ‖Γ.val D ℓe‖ ≤ (Γ.partition.map fun P => P.g.sizeConst K₀ K₁ Kd).sum * Γ.scalingSizeG Ψ W d L

/-! ## 5. T4: `claim:size` for the matrices of the BA model, and the confinement tails -/

/-- **T4 `baClaimSize_E`** (twin of `lwClaimSize_E`, `LWSizeClaim.lean:1196`): the constants depend on `(d, Λ, κ)` only; `D.S`, `D.Sp`,
`D.M`, `D.gPsi` are the BA matrices; `G` is any matrix with `‖G - M‖ ≤ Ψ`. -/
def baClaimSize_E_pin : Prop :=
  ∀ d : ℕ, 3 ≤ d → ∀ Λ κ : ℝ, 0 < Λ → 0 < κ → ∃ K₀ K₁ Kd : ℝ, 0 < K₀ ∧ 0 < K₁ ∧ 0 ≤ Kd ∧
    ∀ (L W : ℕ) [NeZero L] [NeZero W], 3 ≤ L → ∀ (g0 E t : ℝ) (m : ℂ), 0 < g0 → g0 ≤ Λ → RBM.BA.BAReal d L g0 κ E m →
      0 ≤ t → t < 1 →
      ∀ (E' I' : Type) [Fintype E'] [DecidableEq E'] [Fintype I'] [DecidableEq I'] (Γ : BAGraph E' I'), Γ.Normal →
        ∀ D : BALData (Idx d L W), D.S = Matrix.of (BAlwS d L W t) →
          D.Sp = Matrix.of (BAlwS d L W t) * BAlwW d L W g0 E t m → D.M = BAlwM d L W g0 E m →
          D.gPsi = (g0 : ℂ) • PsiI d L W → ∀ Ψ : ℝ, (∀ x y, ‖D.G x y - D.M x y‖ ≤ Ψ) →
          ∀ ℓe : E' → Idx d L W, ‖Γ.val D ℓe‖ ≤ Γ.sizeConst K₀ K₁ Kd * Γ.scalingSize Ψ W d L

/-- **T4 `baClaimSizeG_E`**: the general-graph form of `baClaimSize_E_pin`. -/
def baClaimSizeG_E_pin : Prop :=
  ∀ d : ℕ, 3 ≤ d → ∀ Λ κ : ℝ, 0 < Λ → 0 < κ → ∃ K₀ K₁ Kd : ℝ, 0 < K₀ ∧ 0 < K₁ ∧ 0 ≤ Kd ∧
    ∀ (L W : ℕ) [NeZero L] [NeZero W], 3 ≤ L → ∀ (g0 E t : ℝ) (m : ℂ), 0 < g0 → g0 ≤ Λ → RBM.BA.BAReal d L g0 κ E m →
      0 ≤ t → t < 1 →
      ∀ (E' I' : Type) [Fintype E'] [DecidableEq E'] [Fintype I'] [DecidableEq I'] (Γ : BAGraph E' I'),
        ∀ D : BALData (Idx d L W), D.S = Matrix.of (BAlwS d L W t) →
          D.Sp = Matrix.of (BAlwS d L W t) * BAlwW d L W g0 E t m → D.M = BAlwM d L W g0 E m →
          D.gPsi = (g0 : ℂ) • PsiI d L W → ∀ Ψ : ℝ, (∀ x y, ‖D.G x y - D.M x y‖ ≤ Ψ) →
          ∀ ℓe : E' → Idx d L W,
            ‖Γ.val D ℓe‖ ≤ (Γ.partition.map fun P => P.g.sizeConst K₀ K₁ Kd).sum * Γ.scalingSizeG Ψ W d L

/-- **T4 `baSpTail_E`** (twin of `lwSpOf_tail_E`, `LWSizeClaim.lean:1316`): the tail of a row of `S W` beyond block distance `R`. -/
def baSpTail_E_pin : Prop :=
  ∀ d : ℕ, 3 ≤ d → ∀ Λ κ : ℝ, 0 < Λ → 0 < κ → ∃ C₂ c₂ : ℝ, 0 < C₂ ∧ 0 < c₂ ∧
    ∀ (L W : ℕ) [NeZero L] [NeZero W], 3 ≤ L → ∀ (g0 E t : ℝ) (m : ℂ), 0 < g0 → g0 ≤ Λ → RBM.BA.BAReal d L g0 κ E m →
      0 ≤ t → t < 1 → ∀ (x : Idx d L W) (R : ℝ),
        ∑ y ∈ Finset.univ.filter (fun y => R ≤ (lwBdist d L W x y : ℝ)),
          ‖(Matrix.of (BAlwS d L W t) * BAlwW d L W g0 E t m) x y‖ ≤ C₂ * Real.exp (-(c₂ * R))

/-- **T4 `baMTail_E`**: the tail of a row of `M` beyond block distance `R` (the block spread of (B.15)). -/
def baMTail_E_pin : Prop :=
  ∀ d : ℕ, 3 ≤ d → ∀ Λ κ : ℝ, 0 < Λ → 0 < κ → ∃ C₂ c₂ : ℝ, 0 < C₂ ∧ 0 < c₂ ∧
    ∀ (L W : ℕ) [NeZero L] [NeZero W], 3 ≤ L → ∀ (g0 E : ℝ) (m : ℂ), 0 < g0 → g0 ≤ Λ → RBM.BA.BAReal d L g0 κ E m →
      ∀ (x : Idx d L W) (R : ℝ),
        ∑ y ∈ Finset.univ.filter (fun y => R ≤ (lwBdist d L W x y : ℝ)), ‖BAlwM d L W g0 E m x y‖ ≤ C₂ * Real.exp (-(c₂ * R))

/-- **T4 `baTail_log`** (twin of `lwTail_log32`, `LWSizeClaim.lean:1285`, `p = 3/2`): at `R = (log W)^p`, `p > 1`, the tail
`e^{-cR/2}` is eventually `≤ W^{-D}`. -/
def baTail_log_pin : Prop :=
  ∀ c : ℝ, 0 < c → ∀ p : ℝ, 1 < p → ∀ D : ℝ, ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W →
    Real.exp (-(c * (Real.log W) ^ p / 2)) ≤ (W : ℝ) ^ (-D)

/-! ## 6. `#check` lines -/

#check @BAGraph.sizeConst
#check @BAGraph.Jx
#check @BAGraph.edgeEnds
#check baSp_eq_pin
#check baSpDecay_pin
#check baKBound_E_pin
#check BASizeClaim_forest_sum_le_pin
#check BAGraph_exists_forest_pin
#check BAGraph_counters_le_pin
#check baClaimSize_pin
#check baClaimSizeG_pin
#check baClaimSize_E_pin
#check baClaimSizeG_E_pin
#check baSpTail_E_pin
#check baMTail_E_pin
#check baTail_log_pin
-- the upstream declarations the pins are written in
#check @BAlwS
#check @BAlwW
#check @BAlwM
#check @RBM.BA.BAReal
#check @RBM.BA.BATheta
#check @lwLift
#check @lwBdist
#check @LWKBound
#check @BAGraph.val
#check @BAGraph.scalingSize
#check @BAGraph.scalingSizeG
#check @BAGraph.partition

/-! ## 7. One nonempty instance: `d = 3`, `L = 4`, `W = 2`, `t = 1/2`, the flow point `P : FlowPt 4 10`

`P.g0 ∈ (0, 10]`, `P.E`, `P.m0` with `BAReal 3 4 P.g0 (Im P.m0) P.E P.m0`; `Λ = 10`, `κ = Im P.m0`; `G = M + (1/100) J`
(`|Ǧ_{xy}| = 1/100` for all `x, y`, the diagonal included).  The graphs of `BAVocabInst`: `baLWT1` (normal, `(n_S, n_W, n_A, n_M) =
(2, 1, 2, 1)`, no external vertex) and `baGGT1` (normal, `(0, 1, 1, 0)`, two external vertices).  The hypotheses of the example are
the pins of the ticket (unproved here: they are the targets of stage 1b); every deterministic hypothesis of each pin that is applied
is discharged at the data.  Not applied: `BASizeClaim_forest_sum_le_pin` (its instance is the forest of a concrete graph, owed by 1b). -/

namespace T2412Inst

/-- The BA model data at `P`, `t = 1/2`, `W = 2`: `M = BAlwM`, `S`, `S⁺ = S W`, `g₀ Ψ`, and `G = M + (1/100) J`. -/
def D0 : BALData (Idx 3 4 2) where
  G := Matrix.of fun x y => BAlwM 3 4 2 RBM.BA.MFixedPointInst.P.g0 RBM.BA.MFixedPointInst.P.E
    RBM.BA.MFixedPointInst.P.m0 x y + 1 / 100
  M := BAlwM 3 4 2 RBM.BA.MFixedPointInst.P.g0 RBM.BA.MFixedPointInst.P.E RBM.BA.MFixedPointInst.P.m0
  S := Matrix.of (BAlwS 3 4 2 (1 / 2))
  Sp := Matrix.of (BAlwS 3 4 2 (1 / 2)) * BAlwW 3 4 2 RBM.BA.MFixedPointInst.P.g0 RBM.BA.MFixedPointInst.P.E (1 / 2)
    RBM.BA.MFixedPointInst.P.m0
  gPsi := (RBM.BA.MFixedPointInst.P.g0 : ℂ) • PsiI 3 4 2

end T2412Inst

open RBM.BA.MFixedPointInst BAVocabInst T2412Inst in
example (hEq : baSp_eq_pin) (hDec : baSpDecay_pin) (hKB : baKBound_E_pin) (hSz : baClaimSize_pin)
    (hSzG : baClaimSizeG_pin) (hSzE : baClaimSize_E_pin) (hSzGE : baClaimSizeG_E_pin) (hTS : baSpTail_E_pin)
    (hTM : baMTail_E_pin) (hTL : baTail_log_pin) (hCL : BAGraph_counters_le_pin) (hF : BAGraph_exists_forest_pin) :
    (∃ K₀ K₁ Kd : ℝ, 0 < K₀ ∧ 0 < K₁ ∧ 0 ≤ Kd ∧ baLWT1.counters = ⟨2, 1, 2, 1, 0, 0⟩ ∧
      0 < baLWT1.scalingSize (1 / 100) 2 3 4 ∧
      ‖baLWT1.val D0 Fin.elim0‖ ≤ baLWT1.sizeConst K₀ K₁ Kd * baLWT1.scalingSize (1 / 100) 2 3 4 ∧
      ‖baLWT1.val D0 Fin.elim0‖ ≤
        (baLWT1.partition.map fun P => P.g.sizeConst K₀ K₁ Kd).sum * baLWT1.scalingSizeG (1 / 100) 2 3 4) ∧
    (∃ K₀ K₁ Kd : ℝ, 0 < K₀ ∧ 0 < K₁ ∧ 0 ≤ Kd ∧ baGGT1.counters = ⟨0, 1, 1, 0, 0, 0⟩ ∧
      0 < baGGT1.scalingSize (1 / 100) 2 3 4 ∧
      ‖baGGT1.val D0 ![fun _ => 0, fun _ => 1]‖ ≤ baGGT1.sizeConst K₀ K₁ Kd * baGGT1.scalingSize (1 / 100) 2 3 4) ∧
    (∃ K₀ K₁ Kd : ℝ, 0 < K₀ ∧ 0 < K₁ ∧ 0 ≤ Kd ∧
      ‖baGGT1.val D0 ![fun _ => 0, fun _ => 1]‖ ≤
        (baGGT1.partition.map fun P => P.g.sizeConst K₀ K₁ Kd).sum * baGGT1.scalingSizeG (1 / 100) 2 3 4) := by
  have hκ : 0 < P.m0.im := P.real.1.1
  have hG : ∀ x y, ‖D0.G x y - D0.M x y‖ ≤ 1 / 100 := by
    intro x y
    simp [D0]
  -- T1 at the data: the equation `S W = t lift(Θ)`, the entrywise decay, the tails of `S W` and `M`, the radius `(log W)^p`
  have _hEq := hEq 3 4 2 (by norm_num) P.g0 P.m0.im P.E (1 / 2) P.m0 P.real (by norm_num) (by norm_num)
  obtain ⟨C, c, hC, hc, hCc⟩ := hDec 3 le_rfl 10 P.m0.im (by norm_num) hκ
  have _hDec := hCc 4 2 (by norm_num) P.g0 P.E (1 / 2) P.m0 P.g0_pos P.g0_le P.real (by norm_num) (by norm_num)
  obtain ⟨C₂, c₂, hC₂, hc₂, hT⟩ := hTS 3 le_rfl 10 P.m0.im (by norm_num) hκ
  have _hTS := hT 4 2 (by norm_num) P.g0 P.E (1 / 2) P.m0 P.g0_pos P.g0_le P.real (by norm_num) (by norm_num) 0 1
  obtain ⟨C₃, c₃, hC₃, hc₃, hT'⟩ := hTM 3 le_rfl 10 P.m0.im (by norm_num) hκ
  have _hTM := hT' 4 2 (by norm_num) P.g0 P.E P.m0 P.g0_pos P.g0_le P.real 0 1
  have _hTL := hTL 1 one_pos (3 / 2) (by norm_num) 3
  -- T2 on `baLWT1` (no `=`-dotted edge): the counters and the forest
  have _hCL := hCL baLWT1 (by decide)
  have _hF := hF baLWT1 (by decide)
  refine ⟨?_, ?_, ?_⟩
  · -- T1 (`baKBound_E`) feeds T3 and its general form on `baLWT1`
    obtain ⟨K₀, K₁, Kd, hK₀, hK₁, hKd, hK⟩ := hKB 3 le_rfl 10 P.m0.im (by norm_num) hκ
    obtain ⟨hS, hSp, hM, hP⟩ := hK 4 2 (by norm_num) P.g0 P.E (1 / 2) P.m0 P.g0_pos P.g0_le P.real (by norm_num)
      (by norm_num)
    refine ⟨K₀, K₁, Kd, hK₀, hK₁, hKd, baLWT1_counters, ?_, hSz baLWT1 ⟨by decide, by decide⟩ D0 hG hS hSp hM hP _,
      hSzG baLWT1 D0 hK₀.le hK₁.le hKd hG hS hSp hM hP _⟩
    unfold BAGraph.scalingSize
    rw [baLWT1_counters]
    simp only [Counters.scalingSize]
    norm_num
  · -- T4 (`baClaimSize_E`) on `baGGT1` (two external vertices)
    obtain ⟨K₀, K₁, Kd, hK₀, hK₁, hKd, hK⟩ := hSzE 3 le_rfl 10 P.m0.im (by norm_num) hκ
    refine ⟨K₀, K₁, Kd, hK₀, hK₁, hKd, baGGT1_counters, ?_,
      hK 4 2 (by norm_num) P.g0 P.E (1 / 2) P.m0 P.g0_pos P.g0_le P.real (by norm_num) (by norm_num) (Fin 2) (Fin 3)
        baGGT1 ⟨by decide, by decide⟩ D0 rfl rfl rfl rfl (1 / 100) hG _⟩
    unfold BAGraph.scalingSize
    rw [baGGT1_counters]
    simp only [Counters.scalingSize]
    norm_num
  · -- T4 general form (`baClaimSizeG_E`) on `baGGT1`
    obtain ⟨K₀, K₁, Kd, hK₀, hK₁, hKd, hK⟩ := hSzGE 3 le_rfl 10 P.m0.im (by norm_num) hκ
    exact ⟨K₀, K₁, Kd, hK₀, hK₁, hKd,
      hK 4 2 (by norm_num) P.g0 P.E (1 / 2) P.m0 P.g0_pos P.g0_le P.real (by norm_num) (by norm_num) (Fin 2) (Fin 3)
        baGGT1 D0 rfl rfl rfl rfl (1 / 100) hG _⟩

end RBM.Graph
