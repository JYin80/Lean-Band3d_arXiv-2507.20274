/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.BA.KBase
import RBM3D.BA.FlowPins
import RBM3D.BA.Ward
import RBM3D.Loop.Unique
import RBM3D.Loop.KLUnique

/-!
# Stage K, row K03: the levels `n ≤ 3` of the block Anderson `K`-loop equation

Ticket T2368 (design BA-DK, `docs/reports/T2360-design.md` §2 (`BAKsolve`), §4 rows K01 (BA part),
K03).

1. The pins `IsKLoopSLe` (the system of `IsKLoopS` on the loops of length `≤ N`), `BAKsolve`
   (existence of the BA `𝒦` on `[0,1)` with `(Kn2sol)`; K05b's target, a closing condition of
   stage K) and `BAKsolveLe3`.
2. `baKsolveLe3_holds : ∀ d, BAKsolveLe3 d`: `(Kn2sol)` and `(Kn3sol)` (`1_2:1175-1177`, D634)
   with the K00 convention (`BAMLoop` pairs `σ_i` with `(a_{i-1}, a_i)`; a leaf at `a_v` carries
   `Θ^{(σ_v, σ_{v+1})}`) solve the system on the levels `n ≤ 3`.  The `2`-loop is
   `W^{-d} Θ M^{(σσ')}`, the `3`-loop is the triple sum with the `M`-loop `BAMLoop` as weight; the
   cuts of a `3`-loop are `2`- and `3`-loops, and `∂_tΘ = ΘMΘ` on each leaf.
3. The BA instances of the generic K01 pins (`S = 1`, initial data `BAMLoop`): `baK_unique`,
   `baK_rotate`, `baK_translate`, with `BAMLoop_rot`, `BAMLoop_translate`, `BAMsigma_shift`; and
   `BAKsol_isKLoopS`, `BAKsol_rotate`, `BAKsol_translate` under the pin `BAKsolve d`.
-/

set_option linter.style.longLine false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.style.setOption false
set_option linter.flexible false

noncomputable section

open Matrix Filter Topology Finset

namespace RBM.BA

open RBM RBM.Loop RBM.Gauss

/-! ## 1. The pins (verbatim from `docs/tickets/checks/T2368-check.lean`, Part 1) -/

/-- **`BAKsolve`** (verbatim: probe `t/T2360:RBM3D/Probe/T2360Pins.lean:281`): existence of the BA `𝒦` on `[0,1)` with
`(Kn2sol)`; the target of K05b, a closing condition of stage K (supervisor 2051 Q5). -/
def BAKsolve (d : ℕ) : Prop :=
  ∀ (Λ κ : ℝ), 0 < Λ → 0 < κ → ∀ (L : ℕ) (hL : 3 ≤ L) (W : ℕ) (g : ℝ), 0 < g → g ≤ Λ → ∀ (E : ℝ) (m : ℂ),
    haveI : NeZero L := ⟨by omega⟩
    BAReal d L g κ E m →
      ∃ K : ℝ → LoopIdx (Zd d L) → ℂ,
        IsKLoopS d L W (1 : Matrix (Zd d L) (Zd d L) ℂ) (PropSpin m)
          (BAMLoop d L W (BAMsigma d L (BAMB d L g (E : ℂ) m))) (Set.Ico (0 : ℝ) 1) K ∧
        ∀ t ∈ Set.Ico (0 : ℝ) 1, ∀ (σ : Bool × Bool) (a₁ a₂ : Zd d L),
          K t ⟨[σ.1, σ.2], [a₁, a₂]⟩ =
            (((W : ℂ) ^ d)⁻¹) * (BATheta d L g E m t σ.1 σ.2 * BAMss d L (BAMB d L g (E : ℂ) m) σ.1 σ.2) a₁ a₂

/-! ## 2. Calculus facts for `Θ^{(σσ')}` and `M^{(σσ')}` (only what `BA/KBase` does not export) -/

/-! ## 3. The right-hand side of the tree equation at `S = 1`, `n = 2, 3` -/

/-! ## 4. The triple sum `τ` and its calculus -/

/-! ## 5. The family `(Kn2sol)`, `(Kn3sol)` and its three properties -/

/-! ## 6. `baKsolveLe3_holds` -/

/-! ## 7. The BA instances of the generic K01 pins (`S = 1`, initial data `BAMLoop`) -/

section Instances01

/-- `(l ++ [x]).getD j = (x :: l).getD ((j+1) mod (|l|+1))` on `j ≤ |l|`: moving the head to the end. -/
private theorem BAKSolve_getD_snoc {α : Type*} (l : List α) (x d : α) (j : ℕ) (hj : j < l.length + 1) :
    (l ++ [x]).getD j d = (x :: l).getD ((j + 1) % (l.length + 1)) d := by
  rcases Nat.lt_succ_iff_lt_or_eq.1 hj with h | h
  · rw [Nat.mod_eq_of_lt (by omega), List.getD_append _ _ _ _ h, List.getD_cons_succ]
  · subst h
    rw [Nat.mod_self, List.getD_append_right _ _ _ _ le_rfl]
    simp

/-- A cyclic reindexing does not change a product over `range (n+1)`. -/
private theorem BAKSolve_prod_rot (f : ℕ → ℂ) (n : ℕ) :
    ∏ i ∈ Finset.range (n + 1), f ((i + 1) % (n + 1)) = ∏ i ∈ Finset.range (n + 1), f i := by
  rw [Finset.prod_range_succ, Finset.prod_range_succ' f, Nat.mod_self]
  congr 1
  refine Finset.prod_congr rfl fun i hi => ?_
  rw [Nat.mod_eq_of_lt (by have := Finset.mem_range.1 hi; omega)]

/-- **`BAMLoop` is cyclically invariant** (the hypothesis of `RotS` at `M = BAMLoop`): the K00 product
`W^{-(n-1)d} ∏_i M(σ_i)_{a_{i-1} a_i}` over the cyclic edges is a commutative product over the same factors. -/
theorem BAMLoop_rot (d L W : ℕ) (M : Bool → Matrix (Zd d L) (Zd d L) ℂ) (s : Bool) (b : Zd d L)
    (σ : List Bool) (a : List (Zd d L)) (hσa : σ.length = a.length) :
    BAMLoop d L W M ⟨s :: σ, b :: a⟩ = BAMLoop d L W M ⟨σ ++ [s], a ++ [b]⟩ := by
  have e1 := BAMLoop_apply d L W M ⟨s :: σ, b :: a⟩ (a.length + 1) (by omega) (by simp [hσa]) (by simp)
  have e2 := BAMLoop_apply d L W M ⟨σ ++ [s], a ++ [b]⟩ (a.length + 1) (by omega) (by simp [hσa]) (by simp)
  rw [e1, e2]
  congr 1
  rw [← BAKSolve_prod_rot (fun i => M ((s :: σ).getD i false)
    ((b :: a).getD ((i + (a.length + 1 - 1)) % (a.length + 1)) 0) ((b :: a).getD i 0)) a.length]
  refine Finset.prod_congr rfl fun i hi => ?_
  have hi' : i < a.length + 1 := Finset.mem_range.1 hi
  have hj : (i + (a.length + 1 - 1)) % (a.length + 1) < a.length + 1 := Nat.mod_lt _ (by omega)
  have hσ' : i < σ.length + 1 := by omega
  dsimp only
  rw [BAKSolve_getD_snoc σ s false i hσ', BAKSolve_getD_snoc a b 0 i hi',
    BAKSolve_getD_snoc a b 0 _ hj, hσa]
  have e3 : (((i + (a.length + 1 - 1)) % (a.length + 1) + 1) % (a.length + 1)) =
      (((i + 1) % (a.length + 1) + (a.length + 1 - 1)) % (a.length + 1)) := by
    rw [Nat.mod_add_mod, Nat.mod_add_mod]
    congr 1
    omega
  rw [e3]

/-- **`BAMLoop` is translation invariant** (the hypothesis of `TranslS` at `M = BAMLoop`) when every `M(σ)` is
(`M(σ)_{x+c, y+c} = M(σ)_{xy}`). -/
theorem BAMLoop_translate (d L W : ℕ) (M : Bool → Matrix (Zd d L) (Zd d L) ℂ)
    (hM : ∀ (σ : Bool) (x y c : Zd d L), M σ (x + c) (y + c) = M σ x y) (c : Zd d L) (I : LoopIdx (Zd d L)) :
    BAMLoop d L W M ⟨I.σ, I.a.map (· + c)⟩ = BAMLoop d L W M I := by
  unfold BAMLoop
  simp only [LoopIdx.length, List.length_map]
  congr 1
  rw [← List.map_rotate, List.zip_map, List.zip_map_right, List.map_map]
  refine congrArg List.prod (List.map_congr_left fun p _ => ?_)
  simp only [Function.comp, Prod.map_fst, Prod.map_snd, id]
  exact hM _ _ _ _

/-- `M(σ)` of the block Anderson model is translation invariant (`BAMB_shift`, `BA/Ward.lean:53`; `M(-) = M^*`). -/
theorem BAMsigma_shift (d L : ℕ) [NeZero L] (g : ℝ) (z m : ℂ) (σ : Bool) (x y c : Zd d L) :
    BAMsigma d L (BAMB d L g z m) σ (x + c) (y + c) = BAMsigma d L (BAMB d L g z m) σ x y := by
  cases σ
  · simp only [BAMsigma, Bool.false_eq_true, ite_false, Matrix.conjTranspose_apply, BAMB_shift]
  · exact BAMB_shift d L g z m x y c

variable {d L W : ℕ} [NeZero L] (m : Bool → ℂ) (Ms : Bool → Matrix (Zd d L) (Zd d L) ℂ)

/-- **Uniqueness of the BA `𝒦`** (`S = 1`, initial data `BAMLoop`): two families of `K`-loops on `[0,1)` agree on
every well-formed loop of length `≥ 2` (`uniqS_holds` with the `2`-loop bound `retireS_holds` of both). -/
theorem baK_unique {K K' : ℝ → LoopIdx (Zd d L) → ℂ}
    (hK : IsKLoopS d L W (1 : Matrix (Zd d L) (Zd d L) ℂ) m (BAMLoop d L W Ms) (Set.Ico (0 : ℝ) 1) K)
    (hK' : IsKLoopS d L W (1 : Matrix (Zd d L) (Zd d L) ℂ) m (BAMLoop d L W Ms) (Set.Ico (0 : ℝ) 1) K') :
    ∀ t ∈ Set.Ico (0 : ℝ) 1, ∀ I : LoopIdx (Zd d L), I.WF → 2 ≤ I.length → K t I = K' t I := by
  intro t ht I hI h2
  obtain ⟨R, hR0, hR⟩ := retireS_holds d L W 1 m (BAMLoop d L W Ms) hK t ht.2
  obtain ⟨R', hR'0, hR'⟩ := retireS_holds d L W 1 m (BAMLoop d L W Ms) hK' t ht.2
  exact uniqS_holds d L W 1 m (BAMLoop d L W Ms) kernel_one_rot_transl.2.1 hK hK' (T₀ := t) (R := max R R')
    (fun r hr => ⟨hr.1, lt_of_le_of_lt hr.2 ht.2⟩) (le_trans hR0 (le_max_left _ _))
    (fun r hr J hJ hJ2 => ⟨(hR r hr J hJ hJ2).trans (le_max_left _ _),
      (hR' r hr J hJ hJ2).trans (le_max_right _ _)⟩) t ⟨ht.1, le_rfl⟩ I hI h2

/-- **Cyclic invariance of the BA `𝒦`** (the form of `KLK_rotate`): `rotS_holds` at `S = 1`, `M = BAMLoop`
(`kernel_one_rot_transl`, `BAMLoop_rot`). -/
theorem baK_rotate {K : ℝ → LoopIdx (Zd d L) → ℂ}
    (hK : IsKLoopS d L W (1 : Matrix (Zd d L) (Zd d L) ℂ) m (BAMLoop d L W Ms) (Set.Ico (0 : ℝ) 1) K) :
    ∀ t ∈ Set.Ico (0 : ℝ) 1, ∀ (s : Bool) (b : Zd d L) (σ : List Bool) (a : List (Zd d L)),
      σ.length = a.length → K t ⟨s :: σ, b :: a⟩ = K t ⟨σ ++ [s], a ++ [b]⟩ :=
  rotS_holds d L W 1 m (BAMLoop d L W Ms) kernel_one_rot_transl.1 kernel_one_rot_transl.2.1
    (fun s b σ a h => BAMLoop_rot d L W Ms s b σ a h) hK

/-- **Translation invariance of the BA `𝒦`** (the form of `KLK_translate`), for `M(σ)` translation invariant:
`translS_holds` at `S = 1`, `M = BAMLoop` (`kernel_one_rot_transl`, `BAMLoop_translate`). -/
theorem baK_translate (hMs : ∀ (σ : Bool) (x y c : Zd d L), Ms σ (x + c) (y + c) = Ms σ x y)
    {K : ℝ → LoopIdx (Zd d L) → ℂ}
    (hK : IsKLoopS d L W (1 : Matrix (Zd d L) (Zd d L) ℂ) m (BAMLoop d L W Ms) (Set.Ico (0 : ℝ) 1) K) :
    ∀ t ∈ Set.Ico (0 : ℝ) 1, ∀ (c : Zd d L) (I : LoopIdx (Zd d L)), I.WF →
      K t ⟨I.σ, I.a.map (· + c)⟩ = K t I :=
  translS_holds d L W 1 m (BAMLoop d L W Ms) kernel_one_rot_transl.2.2 kernel_one_rot_transl.2.1
    (fun c I => BAMLoop_translate d L W Ms hMs c I) hK

end Instances01

/-! ## 8. `BAKsol` under the pin `BAKsolve d` -/

section BAKsolSection

/-- `BAKsol` is the solution that `BAKsolve` provides (probe `t/T2360:RBM3D/Probe/T2360Pins.lean:293`). -/
theorem BAKsol_isKLoopS {d : ℕ} (h : BAKsolve d) {Λ κ : ℝ} (hΛ : 0 < Λ) (hκ : 0 < κ) {L : ℕ} [NeZero L]
    (hL : 3 ≤ L) {W : ℕ} {g : ℝ} (hg : 0 < g) (hgΛ : g ≤ Λ) {E : ℝ} {m : ℂ} (hr : BAReal d L g κ E m) :
    IsKLoopS d L W (1 : Matrix (Zd d L) (Zd d L) ℂ) (PropSpin m)
      (BAMLoop d L W (BAMsigma d L (BAMB d L g (E : ℂ) m))) (Set.Ico (0 : ℝ) 1)
      (BAKsol d L W (BAMsigma d L (BAMB d L g (E : ℂ) m)) (PropSpin m)) := by
  obtain ⟨K, hK, -⟩ := h Λ κ hΛ hκ L hL W g hg hgΛ E m hr
  have hex : ∃ K : ℝ → LoopIdx (Zd d L) → ℂ, IsKLoopS d L W (1 : Matrix (Zd d L) (Zd d L) ℂ) (PropSpin m)
      (BAMLoop d L W (BAMsigma d L (BAMB d L g (E : ℂ) m))) (Set.Ico (0 : ℝ) 1) K := ⟨K, hK⟩
  simp only [BAKsol, hex, ↓reduceDIte]
  exact hex.choose_spec

/-- **BA rotation**: `BAKsol` is cyclically invariant (the BA counterpart of `KLK_rotate`), under the pin
`BAKsolve d`. -/
theorem BAKsol_rotate {d : ℕ} (h : BAKsolve d) {Λ κ : ℝ} (hΛ : 0 < Λ) (hκ : 0 < κ) {L : ℕ} [NeZero L]
    (hL : 3 ≤ L) {W : ℕ} {g : ℝ} (hg : 0 < g) (hgΛ : g ≤ Λ) {E : ℝ} {m : ℂ} (hr : BAReal d L g κ E m) :
    ∀ t ∈ Set.Ico (0 : ℝ) 1, ∀ (s : Bool) (b : Zd d L) (σ : List Bool) (a : List (Zd d L)),
      σ.length = a.length →
      BAKsol d L W (BAMsigma d L (BAMB d L g (E : ℂ) m)) (PropSpin m) t ⟨s :: σ, b :: a⟩ =
        BAKsol d L W (BAMsigma d L (BAMB d L g (E : ℂ) m)) (PropSpin m) t ⟨σ ++ [s], a ++ [b]⟩ :=
  baK_rotate _ _ (BAKsol_isKLoopS h hΛ hκ hL hg hgΛ hr)

end BAKsolSection

/-! ## 9. Compiled nonempty instances

Data: the merged flow point `P` of `(d, L) = (3, 4)` (`BA/MFixedPoint.lean:893`; `P.real : BAReal 3 4 P.g0 (Im m₀) P.E m₀`,
`0 < P.g0 ≤ 10`, the data of `KBaseInst`), `W = 2` (`W^d = 8`), `Λ = 10`, `κ = Im m₀ > 0`.  Every deterministic hypothesis
is discharged.  `BAKsolve 3` (K05b's pin, not proved here) stays a hypothesis of the examples that need a family at all
lengths (`baK_*`, `BAKsol_*`). -/

end RBM.BA
