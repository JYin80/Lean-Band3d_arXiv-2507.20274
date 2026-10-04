/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Green.MinorGoodLe

/-!
# The size of the iterated minor differences: the `Δ_κ` calculus and `C_m Ψ^{m+1}`, `d ≥ 3` (S1-25)

ST-1 ticket T2113.  Port of RBM2D `Green/MinorDiff.lean` (kept declarations: `MinorDiff:98-913`,
the `Checks` section `915-1283` and the `#print axioms` tail are replaced by the instances at the
end of this file) at commit `c9a24cf` to the fine lattice `Z_{WL}^d`, with the renaming rules R1-R4
of `docs/tickets/ST1-COMMON.md` (item 2): `d : Sizes` becomes `sz : Sizes d`,
`Idx (d.L n) (d.W n)` becomes `Idx d (sz.L n) (sz.W n)`, `spectralZ E t` and `spectralM E`
become `zt E t` and `mE E`.  The paper (arXiv:2507.20274) has no minor `G^{(S)}` and no difference
of minors: `paper/tex/3_5_Loop_Hierarchy.tex:33` states `(GavLGEX)` and `3_5:37` defers the
estimates of `lem_GbEXP` to Lemma 4.1 of `[YY_25]`, whose proof is dimension-independent.  The
equation numbers (4.1)-(4.3), (4.9) below are those of `[YY_25]` (as in `Green/MinorGoodLe.lean`).

## The calculus

Differences are taken of a whole *family* of minors `Y : Finset (Idx d L W) → ℂ` (the level `S` is
the set of removed rows): `Δ_κ Y^{(S)} = Y^{(S)} - Y^{(S ∪ {κ})}` (`deltaFam`), iterated along a
list (`iterDeltaFam`).  The two Leibniz rules are exact:

* `deltaFam_mul`       : `Δ_κ(Y Z) = (Δ_κ Y) Z + Y^{(κ)} (Δ_κ Z)`;
* `deltaFam_inv_apply` : `Δ_κ(1/Y) = -(Δ_κ Y)/(Y · Y^{(κ)})`, where neither value vanishes.

`minorDiff_eq_iterDeltaFam` identifies `minorDiff` of `Green/MinorGoodLe.lean` with this calculus
at the level `∅`.

## The atoms and the grading

The families closed under `Δ_κ` are the *entries* `S ↦ G^{(S ∪ T)}_{ab}` (`gFam`) and the *inverse
diagonal entries* `S ↦ (G^{(S ∪ T)}_{aa})⁻¹` (`gInvFam`), extended by `0` to the levels that
removed `a` or `b` (`gEnt`).  Over them, (4.9) and the reciprocal rule read (pointwise inside the
level budget)

* `deltaFam_gFam_apply`    : `Δ_κ G_{ab} = G_{aκ} G_{κb} (G_{κκ})⁻¹`  -- three atoms;
* `deltaFam_gInvFam_apply` : `Δ_κ (G_{aa})⁻¹ = -G_{aκ} G_{κa} (G_{κκ})⁻¹ (G_{aa})⁻¹
  (G^{(κ)}_{aa})⁻¹`  -- five atoms.

The size is tracked by `DiffBd Ψ I M n c p Y`: "`m ≤ n` further differences along rows outside `I`,
never leaving the level budget `M`, give `‖Δ_{κ_1} ⋯ Δ_{κ_m} Y^{(S)}‖ ≤ c Ψ^{p+m}`", i.e. each
difference gains one power of `Ψ` (the constant `c` does not depend on `Ψ`).  Its closure lemmas
(`DiffBd.delta`, `.shift`, `.congr`, `.mul`: orders add, the `2^m` terms of the Leibniz expansion
cost `2^n`) feed the simultaneous induction `diffBd_atom`, which grades the entries at order `1`
and the inverse diagonals at order `0`.  The rows must be distinct from each other and from every
index the atom mentions (the `Nodup` hypothesis of the endpoint).

## What is proved

1. `norm_minorDiff_greenSetDiagCentered_le`:
   `‖Δ_{κ_1} ⋯ Δ_{κ_m}(G^{(·)}_{kk} - m)‖ ≤ C_m Ψ^{m+1}` on `MinorGoodLe`, for `1 ≤ m ≤ M`,
   distinct rows `κ_i ≠ k`; `C_m = minorDiffC (m-1) = 4^{m-1} atomC(m-1)^3`.
2. `norm_greenSetDiagCentered_le`: the `m = 0` grade, `‖G^{(S)}_{kk} - m‖ ≤ Ψ` for `|S| ≤ M`.
3. `minorDiff_qRow`, `minorDiff_flucDiagSet_eq`: `Δ_{κ_1} ⋯ Δ_{κ_m} Q_k = Q_k Δ_{κ_1} ⋯ Δ_{κ_m}`,
   and `bddMeas_minorDiff`, `bddMeas_applyOps_minorDiff_flucDiagSet` (boundedness and
   measurability of the words applied to the differences; **true for every real `u`** and any
   `|E| < 2`, `t < 1`, D210), with `qList_nodup`, `mem_qList_ne`.

## Dimension: nothing to replace, and where `d` enters the gain

Nothing in this file depends on `d` except the index type `Idx d (sz.L n) (sz.W n)` (a `Fintype`
with `DecidableEq`): there is no `W`, `L`, `size`, no weight (`UniformWeight`/`BoundedWeight`, so
DECISIONS §30 does not touch it), no `ilambda`, no `∀ᶠ n` (DECISIONS §29 (2)-(4) do not apply; the
slice `n` is fixed), and the constants (`atomC 0 = 2`, `atomC (r+1) = 16^r atomC r^5`,
`minorDiffC r = 4^r atomC r^3`, the factor `2^n` of `DiffBd.mul`) contain no `d`.  They are
RBM1D's, not the paper's (paper-delta candidate `T2113a`).  Every statement is pointwise in one
sample point `ω` and one slice `n`; the hypotheses are the level-budgeted good event
`MinorGoodLe sz n u z m ω Ψ M` (produced from (4.1) at `ω` by `minorGoodLe_of_goodEvent_flow`,
which needs `|E| ≤ 2`, `Im z_u ≠ 0`, `Ψ₀ ≤ 1/4`, `8 M Ψ₀ ≤ 1`, `Ψ = 2 Ψ₀`) and `0 ≤ Ψ ≤ 1`.

**The gain interface** (`MinorDiffGainUpTo'`, `Green/MinorGoodLe.lean:751`, the hypothesis of
`flucGainUpTo'_of_minorDiffGainUpTo'`) is **not** concluded here: in RBM2D it is discharged by S1-26
(`Green/MinorDiffCond.lean:869`, `minorDiffGainUpTo'_goodEvent`, with
`B = 2 (2 C_M (2δ) + condCost)`, `ρ = 2 (2δ)`, `δ = δ n`), which consumes
`norm_minorDiff_greenSetDiagCentered_le` and `bddMeas_applyOps_minorDiff_flucDiagSet` of this file.
The `d`-dimensional exponent enters only through the size of `Ψ` (one power of `Ψ` per
difference): `Ψ ≥ W^{-d/2}` (the floor of `lem_GbEXP`, `3_5:27`, D213), so the per-layer scale is
`ρ ≍ W^{-d/2}` (RBM2D `W^{-1}`); this file states no exponent of `W`.

## Differences from RBM2D (residual, after the renaming)

None in any statement (script diff in the prove report).  The `Checks` section is replaced by the
instances at `d = 3`, `L = 3`, `W = 2`, `lam = 1/2`, `u = 1/31` (`MinorDiffInst`, last section).
-/

set_option linter.style.longLine false

namespace RBM.Green

open MeasureTheory ProbabilityTheory Matrix Finset RBM.Gauss

/-! ### The difference calculus on families of minors -/

section Calculus

variable {α : Type*} [DecidableEq α]

/-- `Δ_κ Y`, the minor difference of the family `Y` along the row `κ`. -/
def deltaFam (κ : α) (Y : Finset α → ℂ) : Finset α → ℂ := fun S => Y S - Y (insert κ S)

/-- `Y^{(κ)}`, the family `Y` with the row `κ` removed at every level. -/
def shiftFam (κ : α) (Y : Finset α → ℂ) : Finset α → ℂ := fun S => Y (insert κ S)

/-- `Δ_{κ_1} ⋯ Δ_{κ_m} Y`, as a family (the level `S` is still free). -/
def iterDeltaFam : List α → (Finset α → ℂ) → (Finset α → ℂ)
  | [], Y => Y
  | κ :: l, Y => iterDeltaFam l (deltaFam κ Y)

@[simp] theorem deltaFam_apply (κ : α) (Y : Finset α → ℂ) (S : Finset α) :
    deltaFam κ Y S = Y S - Y (insert κ S) := rfl

@[simp] theorem shiftFam_apply (κ : α) (Y : Finset α → ℂ) (S : Finset α) :
    shiftFam κ Y S = Y (insert κ S) := rfl

@[simp] theorem iterDeltaFam_nil (Y : Finset α → ℂ) : iterDeltaFam ([] : List α) Y = Y := rfl

@[simp] theorem iterDeltaFam_cons (κ : α) (l : List α) (Y : Finset α → ℂ) :
    iterDeltaFam (κ :: l) Y = iterDeltaFam l (deltaFam κ Y) := rfl

/-- `Δ_κ` is additive. -/
theorem deltaFam_add (κ : α) (Y Z : Finset α → ℂ) :
    deltaFam κ (fun S => Y S + Z S) = fun S => deltaFam κ Y S + deltaFam κ Z S := by
  funext S; simp only [deltaFam_apply]; ring

theorem deltaFam_neg (κ : α) (Y : Finset α → ℂ) :
    deltaFam κ (fun S => -Y S) = fun S => -deltaFam κ Y S := by
  funext S; simp only [deltaFam_apply]; ring

/-- The iterated difference is additive. -/
theorem iterDeltaFam_add (l : List α) (Y Z : Finset α → ℂ) :
    iterDeltaFam l (fun S => Y S + Z S) = fun S => iterDeltaFam l Y S + iterDeltaFam l Z S := by
  induction l generalizing Y Z with
  | nil => rfl
  | cons κ l ih => rw [iterDeltaFam_cons, deltaFam_add, ih, iterDeltaFam_cons, iterDeltaFam_cons]

theorem iterDeltaFam_neg (l : List α) (Y : Finset α → ℂ) :
    iterDeltaFam l (fun S => -Y S) = fun S => -iterDeltaFam l Y S := by
  induction l generalizing Y with
  | nil => rfl
  | cons κ l ih => rw [iterDeltaFam_cons, deltaFam_neg, ih, iterDeltaFam_cons]

/-- `Δ_κ` and the shift `·^{(κ')}` commute. -/
theorem deltaFam_shiftFam (κ κ' : α) (Y : Finset α → ℂ) :
    deltaFam κ (shiftFam κ' Y) = shiftFam κ' (deltaFam κ Y) := by
  funext S
  simp only [deltaFam_apply, shiftFam_apply, Finset.insert_comm]

/-- The iterated difference commutes with the shift. -/
theorem iterDeltaFam_shiftFam (l : List α) (κ : α) (Y : Finset α → ℂ) :
    iterDeltaFam l (shiftFam κ Y) = shiftFam κ (iterDeltaFam l Y) := by
  induction l generalizing Y with
  | nil => rfl
  | cons κ' l ih => rw [iterDeltaFam_cons, deltaFam_shiftFam, ih, iterDeltaFam_cons]

/-- **The Leibniz rule for `Δ_κ`**: `Δ_κ(Y Z) = (Δ_κ Y) Z + Y^{(κ)} (Δ_κ Z)`. -/
theorem deltaFam_mul (κ : α) (Y Z : Finset α → ℂ) :
    deltaFam κ (fun S => Y S * Z S)
      = fun S => deltaFam κ Y S * Z S + shiftFam κ Y S * deltaFam κ Z S := by
  funext S
  simp only [deltaFam_apply, shiftFam_apply]
  ring

/-- **The Leibniz rule for the reciprocal**: `Δ_κ(1/Y) = -(Δ_κ Y)/(Y · Y^{(κ)})`.  Both values
must be non-zero: with Lean's `0⁻¹ = 0` the identity is false at a vanishing level. -/
theorem deltaFam_inv_apply (κ : α) (Y : Finset α → ℂ) (S : Finset α)
    (h : Y S ≠ 0) (h' : Y (insert κ S) ≠ 0) :
    deltaFam κ (fun S => (Y S)⁻¹) S
      = -(deltaFam κ Y S * (Y S)⁻¹ * (Y (insert κ S))⁻¹) := by
  simp only [deltaFam_apply]
  field_simp
  ring

/-- **`Δ_{κ_1} ⋯ Δ_{κ_m} Y^{(S)}` only looks at the levels of card at most `S.card + m`.**

Unfolded, the iterated difference is the signed sum of `Y (S ∪ T)` over the subsets `T` of the
differenced rows, so two families that agree below a level budget have the same iterated
differences inside that budget.  This is what lets the identities (4.9) and the reciprocal rule
— which are available only at the levels the good event covers — be substituted into a
`RBM.Green.DiffBd` estimate. -/
theorem iterDeltaFam_congr : ∀ (l : List α) {M : ℕ} {Y Z : Finset α → ℂ},
    (∀ U : Finset α, U.card ≤ M → Y U = Z U) →
    ∀ S : Finset α, S.card + l.length ≤ M → iterDeltaFam l Y S = iterDeltaFam l Z S := by
  intro l
  induction l with
  | nil => intro M Y Z h S hS; exact h S (by simpa using hS)
  | cons κ l ih =>
      intro M Y Z h S hS
      simp only [List.length_cons] at hS
      obtain ⟨M', rfl⟩ : ∃ M', M = M' + 1 := ⟨M - 1, by omega⟩
      simp only [iterDeltaFam_cons]
      refine ih (M := M') (fun U hU => ?_) S (by omega)
      have h1 := h U (by omega)
      have h2 := h (insert κ U) (le_trans (Finset.card_insert_le κ U) (by omega))
      simp only [deltaFam_apply, h1, h2]

end Calculus


/-! ### The graded bound: one power of `Ψ` per difference -/

section Graded

variable {α : Type*} [DecidableEq α]

/-- **`Y` is of order `p` with constant `c`, up to `n` differences, inside the level budget `M`.**
Taking `m ≤ n` further differences along rows *outside* `I` gains `m` powers of `Ψ`:

  `‖Δ_{κ_1} ⋯ Δ_{κ_m} Y^{(S)}‖ ≤ c Ψ^{p + m}`.

The rows must be distinct (`l.Nodup`) and must avoid `I`, the set of indices the family already
mentions: `Δ_κ` applied to a Green's function entry carrying the index `κ` has no gain.

**The budget.**  `Δ_{κ_1} ⋯ Δ_{κ_m} Y^{(S)}` reads `Y` at the levels `S ∪ T`, `T ⊆ {κ_1, …, κ_m}`,
so it never looks above level `S.card + m`; the hypothesis `S.card + l.length ≤ M` is exactly
"this estimate never leaves the budget".  Without it the definition would quantify over *all*
levels `S`; with it, `MinorGoodLe … M`, which covers the levels of card at most `M` and is produced
at one sample point by `minorGoodLe_of_goodEvent`, suffices.  For the consumer the budget costs
nothing: `minorDiff_eq_iterDeltaFam` evaluates at the base level `∅`, so the levels actually
reached are subsets of the differenced rows and their card is at most the word length. -/
def DiffBd (Ψ : ℝ) (I : Finset α) (M n : ℕ) (c : ℝ) (p : ℕ) (Y : Finset α → ℂ) : Prop :=
  ∀ (l : List α) (S : Finset α), l.Nodup → (∀ κ ∈ l, κ ∉ I) → l.length ≤ n →
    S.card + l.length ≤ M → ‖iterDeltaFam l Y S‖ ≤ c * Ψ ^ (p + l.length)

theorem DiffBd.le_self {Ψ : ℝ} {I : Finset α} {M n : ℕ} {c : ℝ} {p : ℕ} {Y : Finset α → ℂ}
    (h : DiffBd Ψ I M n c p Y) (S : Finset α) (hS : S.card ≤ M) : ‖Y S‖ ≤ c * Ψ ^ p := by
  simpa using h [] S (by simp) (by simp) (by simp) (by simpa using hS)

/-- No differences at all: a plain bound inside the budget. -/
theorem diffBd_zero {Ψ : ℝ} {I : Finset α} {M : ℕ} {c : ℝ} {p : ℕ} {Y : Finset α → ℂ}
    (h : ∀ S : Finset α, S.card ≤ M → ‖Y S‖ ≤ c * Ψ ^ p) : DiffBd Ψ I M 0 c p Y := by
  intro l S _ _ hlen hcard
  have hl : l = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.1 hlen)
  subst hl
  simpa using h S (by simpa using hcard)

theorem DiffBd.mono_I {Ψ : ℝ} {I I' : Finset α} {M n : ℕ} {c : ℝ} {p : ℕ} {Y : Finset α → ℂ}
    (h : DiffBd Ψ I M n c p Y) (hII : I ⊆ I') : DiffBd Ψ I' M n c p Y :=
  fun l S hnd hav hlen hcard =>
    h l S hnd (fun κ hκ => fun hmem => hav κ hκ (hII hmem)) hlen hcard

theorem DiffBd.mono_n {Ψ : ℝ} {I : Finset α} {M n n' : ℕ} {c : ℝ} {p : ℕ} {Y : Finset α → ℂ}
    (h : DiffBd Ψ I M n c p Y) (hn : n' ≤ n) : DiffBd Ψ I M n' c p Y :=
  fun l S hnd hav hlen hcard => h l S hnd hav (le_trans hlen hn) hcard

/-- A smaller budget is a weaker statement. -/
theorem DiffBd.mono_M {Ψ : ℝ} {I : Finset α} {M M' n : ℕ} {c : ℝ} {p : ℕ} {Y : Finset α → ℂ}
    (h : DiffBd Ψ I M n c p Y) (hM : M' ≤ M) : DiffBd Ψ I M' n c p Y :=
  fun l S hnd hav hlen hcard => h l S hnd hav hlen (le_trans hcard hM)

theorem DiffBd.mono_c {Ψ : ℝ} {I : Finset α} {M n : ℕ} {c c' : ℝ} {p : ℕ} {Y : Finset α → ℂ}
    (h : DiffBd Ψ I M n c p Y) (hΨ : 0 ≤ Ψ) (hc : c ≤ c') : DiffBd Ψ I M n c' p Y := by
  intro l S hnd hav hlen hcard
  exact le_trans (h l S hnd hav hlen hcard) (by
    have : (0:ℝ) ≤ Ψ ^ (p + l.length) := pow_nonneg hΨ _
    nlinarith)

/-- A lower order is a weaker statement, as `Ψ ≤ 1`. -/
theorem DiffBd.mono_p {Ψ : ℝ} {I : Finset α} {M n : ℕ} {c : ℝ} {p p' : ℕ} {Y : Finset α → ℂ}
    (h : DiffBd Ψ I M n c p Y) (hΨ0 : 0 ≤ Ψ) (hΨ1 : Ψ ≤ 1) (hc : 0 ≤ c) (hp : p' ≤ p) :
    DiffBd Ψ I M n c p' Y := by
  intro l S hnd hav hlen hcard
  refine le_trans (h l S hnd hav hlen hcard) ?_
  have : Ψ ^ (p + l.length) ≤ Ψ ^ (p' + l.length) :=
    pow_le_pow_of_le_one hΨ0 hΨ1 (by omega)
  nlinarith

/-- **The estimate only sees the family inside the budget.**  This is what lets (4.9) and the
reciprocal rule — identities that `RBM.Green.MinorGoodLe` supplies only below level `M` — be
substituted into a `RBM.Green.DiffBd` bound. -/
theorem DiffBd.congr {Ψ : ℝ} {I : Finset α} {M n : ℕ} {c : ℝ} {p : ℕ} {Y Z : Finset α → ℂ}
    (h : DiffBd Ψ I M n c p Y) (hYZ : ∀ S : Finset α, S.card ≤ M → Y S = Z S) :
    DiffBd Ψ I M n c p Z := by
  intro l S hnd hav hlen hcard
  rw [← iterDeltaFam_congr l hYZ S hcard]
  exact h l S hnd hav hlen hcard

/-- **One difference raises the order by one** (and locks the row out of later differences).  It
costs one unit of the level budget: `Δ_κ Y` reads `Y` one level higher than `Y` itself. -/
theorem DiffBd.delta {Ψ : ℝ} {I : Finset α} {M n : ℕ} {c : ℝ} {p : ℕ} {Y : Finset α → ℂ}
    {κ : α} (hκ : κ ∉ I) (h : DiffBd Ψ I (M + 1) (n + 1) c p Y) :
    DiffBd Ψ (insert κ I) M n c (p + 1) (deltaFam κ Y) := by
  intro l S hnd hav hlen hcard
  have hκl : κ ∉ l := fun hm => (hav κ hm) (Finset.mem_insert_self κ I)
  have hnd' : (κ :: l).Nodup := List.nodup_cons.2 ⟨hκl, hnd⟩
  have hav' : ∀ κ' ∈ (κ :: l), κ' ∉ I := by
    intro κ' hκ'
    rcases List.mem_cons.1 hκ' with h1 | h1
    · exact h1 ▸ hκ
    · exact fun hm => hav κ' h1 (Finset.mem_insert_of_mem hm)
  have := h (κ :: l) S hnd' hav' (by simp [List.length_cons]; omega)
    (by simp only [List.length_cons]; omega)
  rw [iterDeltaFam_cons] at this
  have hexp : p + (κ :: l).length = p + 1 + l.length := by simp [List.length_cons]; omega
  rwa [hexp] at this

/-- The shift only moves the level -- and therefore costs exactly one unit of the budget. -/
theorem DiffBd.shift {Ψ : ℝ} {I : Finset α} {M n : ℕ} {c : ℝ} {p : ℕ} {Y : Finset α → ℂ}
    (h : DiffBd Ψ I (M + 1) n c p Y) (κ : α) : DiffBd Ψ I M n c p (shiftFam κ Y) := by
  intro l S hnd hav hlen hcard
  rw [iterDeltaFam_shiftFam, shiftFam_apply]
  exact h l (insert κ S) hnd hav hlen
    (by have := Finset.card_insert_le κ S; omega)

theorem DiffBd.neg {Ψ : ℝ} {I : Finset α} {M n : ℕ} {c : ℝ} {p : ℕ} {Y : Finset α → ℂ}
    (h : DiffBd Ψ I M n c p Y) : DiffBd Ψ I M n c p (fun S => -Y S) := by
  intro l S hnd hav hlen hcard
  rw [iterDeltaFam_neg]
  simpa using h l S hnd hav hlen hcard

/-- **The product rule for the graded bound.**  Orders add; the price of the `2^{m}` terms of
the `m`-fold Leibniz expansion is the factor `2^n`.  The budget is untouched: the Leibniz
expansion splits `Δ_κ` into `Δ_κ` on one factor and the shift on the other, and both cost one
level, which is the level the product's own difference has already paid for. -/
theorem DiffBd.mul {Ψ : ℝ} (hΨ : 0 ≤ Ψ) :
    ∀ (n : ℕ) {I : Finset α} {M : ℕ} {c₁ c₂ : ℝ} {p q : ℕ} {Y Z : Finset α → ℂ},
      0 ≤ c₁ → 0 ≤ c₂ → DiffBd Ψ I M n c₁ p Y → DiffBd Ψ I M n c₂ q Z →
      DiffBd Ψ I M n (2 ^ n * (c₁ * c₂)) (p + q) (fun S => Y S * Z S) := by
  intro n
  induction n with
  | zero =>
      intro I M c₁ c₂ p q Y Z hc₁ hc₂ hY hZ l S hnd hav hlen hcard
      have hl : l = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.1 hlen)
      subst hl
      have hS : S.card ≤ M := by simpa using hcard
      have h1 := hY.le_self S hS
      have h2 := hZ.le_self S hS
      have hp1 : (0:ℝ) ≤ Ψ ^ p := pow_nonneg hΨ _
      have hp2 : (0:ℝ) ≤ Ψ ^ q := pow_nonneg hΨ _
      have : ‖Y S * Z S‖ ≤ (c₁ * Ψ ^ p) * (c₂ * Ψ ^ q) := by
        rw [norm_mul]
        exact mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
      simpa [pow_add] using le_trans this (le_of_eq (by ring))
  | succ n ih =>
      intro I M c₁ c₂ p q Y Z hc₁ hc₂ hY hZ l S hnd hav hlen hcard
      match l with
      | [] =>
          have hS : S.card ≤ M := by simpa using hcard
          have h1 := hY.le_self S hS
          have h2 := hZ.le_self S hS
          have hp1 : (0:ℝ) ≤ Ψ ^ p := pow_nonneg hΨ _
          have hp2 : (0:ℝ) ≤ Ψ ^ q := pow_nonneg hΨ _
          have hmul : ‖Y S * Z S‖ ≤ (c₁ * Ψ ^ p) * (c₂ * Ψ ^ q) := by
            rw [norm_mul]
            exact mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
          have hpow : (1:ℝ) ≤ 2 ^ (n + 1) := one_le_pow₀ (by norm_num)
          simp only [iterDeltaFam_nil, List.length_nil, Nat.add_zero]
          have : (c₁ * Ψ ^ p) * (c₂ * Ψ ^ q) = (c₁ * c₂) * Ψ ^ (p + q) := by
            rw [pow_add]; ring
          rw [this] at hmul
          refine le_trans hmul ?_
          have hnn : (0:ℝ) ≤ (c₁ * c₂) * Ψ ^ (p + q) := by positivity
          nlinarith [pow_nonneg hΨ (p + q)]
      | κ :: l' =>
          have hcard' : S.card + l'.length + 1 ≤ M := by
            simp only [List.length_cons] at hcard; omega
          obtain ⟨M', rfl⟩ : ∃ M', M = M' + 1 := ⟨M - 1, by omega⟩
          have hκI : κ ∉ I := hav κ (List.mem_cons_self ..)
          have hnd' : l'.Nodup := (List.nodup_cons.1 hnd).2
          have hκl' : κ ∉ l' := (List.nodup_cons.1 hnd).1
          have hav' : ∀ κ' ∈ l', κ' ∉ insert κ I := by
            intro κ' hκ' hmem
            rcases Finset.mem_insert.1 hmem with h1 | h1
            · exact hκl' (h1 ▸ hκ')
            · exact hav κ' (List.mem_cons_of_mem _ hκ') h1
          have hlen' : l'.length ≤ n := by
            simp only [List.length_cons] at hlen; omega
          have hcardl' : S.card + l'.length ≤ M' := by omega
          have hδY : DiffBd Ψ (insert κ I) M' n c₁ (p + 1) (deltaFam κ Y) := hY.delta hκI
          have hδZ : DiffBd Ψ (insert κ I) M' n c₂ (q + 1) (deltaFam κ Z) := hZ.delta hκI
          have hYs : DiffBd Ψ (insert κ I) M' n c₁ p (shiftFam κ Y) :=
            ((hY.mono_n (Nat.le_succ n)).mono_I (Finset.subset_insert κ I)).shift κ
          have hZ' : DiffBd Ψ (insert κ I) M' n c₂ q Z :=
            ((hZ.mono_n (Nat.le_succ n)).mono_I (Finset.subset_insert κ I)).mono_M
              (Nat.le_succ M')
          have hA := ih hc₁ hc₂ hδY hZ' l' S hnd' hav' hlen' hcardl'
          have hB := ih hc₁ hc₂ hYs hδZ l' S hnd' hav' hlen' hcardl'
          have hsplit : iterDeltaFam (κ :: l') (fun S => Y S * Z S) S
              = iterDeltaFam l' (fun S => deltaFam κ Y S * Z S) S
                + iterDeltaFam l' (fun S => shiftFam κ Y S * deltaFam κ Z S) S := by
            rw [iterDeltaFam_cons, deltaFam_mul, iterDeltaFam_add]
          rw [hsplit]
          have htri := norm_add_le (iterDeltaFam l' (fun S => deltaFam κ Y S * Z S) S)
            (iterDeltaFam l' (fun S => shiftFam κ Y S * deltaFam κ Z S) S)
          have he1 : p + 1 + q + l'.length = p + q + (κ :: l').length := by
            simp [List.length_cons]; omega
          have he2 : p + (q + 1) + l'.length = p + q + (κ :: l').length := by
            simp [List.length_cons]; omega
          rw [he1] at hA
          rw [he2] at hB
          have hfin : 2 ^ n * (c₁ * c₂) * Ψ ^ (p + q + (κ :: l').length)
              + 2 ^ n * (c₁ * c₂) * Ψ ^ (p + q + (κ :: l').length)
              ≤ 2 ^ (n + 1) * (c₁ * c₂) * Ψ ^ (p + q + (κ :: l').length) := by
            rw [pow_succ]; ring_nf; nlinarith [pow_nonneg hΨ (p + q + (κ :: l').length)]
          linarith

end Graded

/-! ### The bridge to `RBM.Green.minorDiff` -/

variable {d : ℕ} {sz : Sizes d} {n : ℕ}

/-- `RBM.Green.minorDiff` is the iterated difference of the family, evaluated at level `∅`. -/
theorem minorDiff_eq_iterDeltaFam (l : List (Idx d (sz.L n) (sz.W n)))
    (Y : Finset (Idx d (sz.L n) (sz.W n)) → Sizes.SeqΩ sz → ℂ) (ω : Sizes.SeqΩ sz) :
    minorDiff sz n l Y ω = iterDeltaFam l (fun S => Y S ω) ∅ := by
  induction l generalizing Y with
  | nil => rfl
  | cons κ l ih =>
      rw [minorDiff_cons, ih, iterDeltaFam_cons]
      rfl


/-! ### The Green's function atoms -/

section Atoms

variable {u : ℝ} {z m : ℂ} {ω : Sizes.SeqΩ sz} {Ψ : ℝ} {a b κ : Idx d (sz.L n) (sz.W n)}
  {S T : Finset (Idx d (sz.L n) (sz.W n))} {M : ℕ}

/-- The family `S ↦ G^{(S ∪ T)}_{ab}`: an *atom* of the calculus.  Carrying the base level `T`
is what makes the class of atoms closed under the shift `Y ↦ Y^{(κ)}`. -/
noncomputable def gFam (sz : Sizes d) (n : ℕ) (u : ℝ) (z : ℂ) (ω : Sizes.SeqΩ sz)
    (a b : Idx d (sz.L n) (sz.W n)) (T : Finset (Idx d (sz.L n) (sz.W n))) :
    Finset (Idx d (sz.L n) (sz.W n)) → ℂ := fun S => gEnt sz n u z ω a b (S ∪ T)

/-- The family `S ↦ (G^{(S ∪ T)}_{aa})⁻¹`, the second kind of atom. -/
noncomputable def gInvFam (sz : Sizes d) (n : ℕ) (u : ℝ) (z : ℂ) (ω : Sizes.SeqΩ sz)
    (a : Idx d (sz.L n) (sz.W n)) (T : Finset (Idx d (sz.L n) (sz.W n))) :
    Finset (Idx d (sz.L n) (sz.W n)) → ℂ := fun S => (gEnt sz n u z ω a a (S ∪ T))⁻¹

@[simp] theorem gFam_apply (a b : Idx d (sz.L n) (sz.W n)) (T S : Finset (Idx d (sz.L n) (sz.W n))) :
    gFam sz n u z ω a b T S = gEnt sz n u z ω a b (S ∪ T) := rfl

@[simp] theorem gInvFam_apply (a : Idx d (sz.L n) (sz.W n)) (T S : Finset (Idx d (sz.L n) (sz.W n))) :
    gInvFam sz n u z ω a T S = (gEnt sz n u z ω a a (S ∪ T))⁻¹ := rfl

/-! #### (4.9) and the reciprocal rule on the level-budgeted good event

`MinorGoodLe` covers the levels of card at most `M` only, so the two identities are **pointwise**:
they hold at the levels the budget reaches, not as equalities of families.  `DiffBd.congr` is what
turns that back into a usable substitution. -/

/-- **(4.9) for an entry atom, at one level inside the budget**:
`Δ_κ G_{ab} = G_{aκ} G_{κb} (G_{κκ})⁻¹`.  The hypothesis is the card of the *larger* of the two
levels the identity mentions, which is the one the difference reaches. -/
theorem deltaFam_gFam_apply (hg : MinorGoodLe sz n u z m ω Ψ M) (a b κ : Idx d (sz.L n) (sz.W n))
    (T S : Finset (Idx d (sz.L n) (sz.W n))) (hcard : (insert κ (S ∪ T)).card ≤ M) :
    deltaFam κ (gFam sz n u z ω a b T) S
      = gFam sz n u z ω a κ T S * gFam sz n u z ω κ b T S * gInvFam sz n u z ω κ T S := by
  have hU : (S ∪ T).card ≤ M :=
    le_trans (Finset.card_le_card (Finset.subset_insert κ (S ∪ T))) hcard
  have hins : insert κ S ∪ T = insert κ (S ∪ T) := Finset.insert_union κ S T
  simp only [deltaFam_apply, gFam_apply, gInvFam_apply, hins]
  by_cases hκU : κ ∈ S ∪ T
  · rw [Finset.insert_eq_self.2 hκU, gEnt_eq_zero_right hκU]
    ring
  · by_cases haU : a ∈ S ∪ T
    · rw [gEnt_eq_zero_left haU, gEnt_eq_zero_left (Finset.mem_insert_of_mem haU),
        gEnt_eq_zero_left haU]
      ring
    · by_cases hbU : b ∈ S ∪ T
      · rw [gEnt_eq_zero_right hbU, gEnt_eq_zero_right (Finset.mem_insert_of_mem hbU),
          gEnt_eq_zero_right hbU]
        ring
      · have hdiag : gEnt sz n u z ω κ κ (S ∪ T) ≠ 0 := hg.diag_ne (S ∪ T) hU κ hκU
        by_cases hak : a = κ
        · subst hak
          rw [gEnt_eq_zero_left (Finset.mem_insert_self a (S ∪ T)), sub_zero]
          field_simp
        · by_cases hbk : b = κ
          · subst hbk
            rw [gEnt_eq_zero_right (Finset.mem_insert_self b (S ∪ T)), sub_zero]
            field_simp
          · have ha' : a ∉ insert κ (S ∪ T) := by
              simp only [Finset.mem_insert, not_or]
              exact ⟨hak, haU⟩
            have hb' : b ∉ insert κ (S ∪ T) := by
              simp only [Finset.mem_insert, not_or]
              exact ⟨hbk, hbU⟩
            rw [hg.gEnt_insert hU hκU ha' hb']
            ring

/-- **The reciprocal rule at one level inside the budget.**  The fifth atom is written as the
inverse diagonal at the base level `insert κ T`, which is the family
`shiftFam κ (gInvFam sz n u z ω a T)`, so that the level bookkeeping stays inside one budget. -/
theorem deltaFam_gInvFam_apply (hg : MinorGoodLe sz n u z m ω Ψ M) (a κ : Idx d (sz.L n) (sz.W n))
    (hak : a ≠ κ) (T S : Finset (Idx d (sz.L n) (sz.W n))) (hcard : (insert κ (S ∪ T)).card ≤ M) :
    deltaFam κ (gInvFam sz n u z ω a T) S
      = -(gFam sz n u z ω a κ T S * gFam sz n u z ω κ a T S
          * gInvFam sz n u z ω κ T S * gInvFam sz n u z ω a T S
          * gInvFam sz n u z ω a (insert κ T) S) := by
  have hU : (S ∪ T).card ≤ M :=
    le_trans (Finset.card_le_card (Finset.subset_insert κ (S ∪ T))) hcard
  have hUκ : (insert κ S ∪ T).card ≤ M := by rwa [Finset.insert_union]
  by_cases haU : a ∈ S ∪ T
  · have h1 : gEnt sz n u z ω a a (S ∪ T) = 0 := gEnt_eq_zero_left haU
    have h2 : gEnt sz n u z ω a a (insert κ S ∪ T) = 0 := by
      rw [Finset.insert_union]
      exact gEnt_eq_zero_left (Finset.mem_insert_of_mem haU)
    have h3 : gEnt sz n u z ω a κ (S ∪ T) = 0 := gEnt_eq_zero_left haU
    simp only [deltaFam_apply, gInvFam_apply, gFam_apply, h1, h2, h3]
    simp
  · have haU' : a ∉ insert κ S ∪ T := by
      rw [Finset.insert_union]
      simp only [Finset.mem_insert, not_or]
      exact ⟨hak, haU⟩
    have h1 : gFam sz n u z ω a a T S ≠ 0 := hg.diag_ne _ hU a haU
    have h2 : gFam sz n u z ω a a T (insert κ S) ≠ 0 := hg.diag_ne _ hUκ a haU'
    have hinv := deltaFam_inv_apply κ (gFam sz n u z ω a a T) S h1 h2
    have hdel := deltaFam_gFam_apply hg a a κ T S hcard
    change deltaFam κ (fun S => (gFam sz n u z ω a a T S)⁻¹) S = _
    rw [hinv, hdel]
    simp only [gInvFam_apply, gFam_apply, Finset.insert_union, Finset.union_insert]

end Atoms


/-! ### The `n`-fold estimate for the atoms -/

section AtomInduction

/-- The constant of the `n`-fold difference estimate.  The paper has no such constant: the
recursion is `c_{n+1} = 16^n c_n^5`, coming from the five atoms of the reciprocal rule and the
`2^n` terms of each Leibniz expansion.  Only its finiteness for each fixed `n` is used. -/
noncomputable def atomC : ℕ → ℝ
  | 0 => 2
  | n + 1 => 16 ^ n * atomC n ^ 5

@[simp] theorem atomC_zero : atomC 0 = 2 := rfl

@[simp] theorem atomC_succ (n : ℕ) : atomC (n + 1) = 16 ^ n * atomC n ^ 5 := rfl

theorem two_le_atomC : ∀ n : ℕ, (2 : ℝ) ≤ atomC n
  | 0 => le_of_eq atomC_zero.symm
  | n + 1 => by
      have h := two_le_atomC n
      have h5 : (2 : ℝ) ^ 5 ≤ atomC n ^ 5 := pow_le_pow_left₀ (by norm_num) h 5
      have h16 : (1 : ℝ) ≤ 16 ^ n := one_le_pow₀ (by norm_num)
      rw [atomC_succ]
      nlinarith

theorem one_le_atomC (n : ℕ) : (1 : ℝ) ≤ atomC n := le_trans (by norm_num) (two_le_atomC n)

theorem atomC_nonneg (n : ℕ) : (0 : ℝ) ≤ atomC n := le_trans (by norm_num) (one_le_atomC n)

variable {u : ℝ} {z m : ℂ} {ω : Sizes.SeqΩ sz} {Ψ : ℝ} {M : ℕ}

/-- **The `r`-fold difference estimate for the two kinds of atom, proved together.**

For `m ≤ r` rows `κ_1, …, κ_m` distinct from each other and from every index the atom mentions,
with `c = atomC r`,

  `‖Δ_{κ_1} ⋯ Δ_{κ_m} G^{(·)}_{ab}‖ ≤ c Ψ^{m+1}`   (`a ≠ b`),
  `‖Δ_{κ_1} ⋯ Δ_{κ_m} (G^{(·)}_{aa})⁻¹‖ ≤ c Ψ^{m}`.

Each difference gains a power of `Ψ`; the two rules that drive the induction are (4.9)
(`RBM.Green.deltaFam_gFam_apply`, three atoms, order `2`) and the reciprocal rule
(`RBM.Green.deltaFam_gInvFam_apply`, five atoms, order `2`), combined by the Leibniz product rule
`RBM.Green.DiffBd.mul`.

**The budget.**  The good event is `RBM.Green.MinorGoodLe … M`, which covers the levels of card
at most `M`; the atom carries the base level `T` and the estimate is granted the budget `B`, so
the levels it reaches have card at most `B + T.card` and the hypothesis is exactly
`B + T.card ≤ M`.  Each difference spends one unit of `B` and each shift moves one row from `B`
into `T`, so the sum is an invariant of the induction. -/
theorem diffBd_atom (hg : MinorGoodLe sz n u z m ω Ψ M) (hΨ0 : 0 ≤ Ψ) (hΨ1 : Ψ ≤ 1) :
    ∀ (r : ℕ) (I T : Finset (Idx d (sz.L n) (sz.W n))) (B : ℕ), B + T.card ≤ M →
      (∀ a b : Idx d (sz.L n) (sz.W n), a ∈ I → b ∈ I → a ≠ b →
        DiffBd Ψ I B r (atomC r) 1 (gFam sz n u z ω a b T))
      ∧ (∀ a : Idx d (sz.L n) (sz.W n), a ∈ I →
        DiffBd Ψ I B r (atomC r) 0 (gInvFam sz n u z ω a T)) := by
  intro r
  induction r with
  | zero =>
      intro I T B hB
      refine ⟨fun a b _ _ hab => diffBd_zero fun S hS => ?_,
        fun a _ => diffBd_zero fun S hS => ?_⟩
      · have hU : (S ∪ T).card ≤ M :=
          le_trans (Finset.card_union_le S T) (by omega)
        have h := hg.off_le (S ∪ T) hU a b hab
        simp only [gFam_apply, atomC_zero, pow_one]
        linarith
      · have hU : (S ∪ T).card ≤ M :=
          le_trans (Finset.card_union_le S T) (by omega)
        have h := hg.inv_le (S ∪ T) hU a
        simpa using h
  | succ r ih =>
      intro I T B hB
      have hc0 : (0 : ℝ) ≤ atomC r := atomC_nonneg r
      have hc1 : (1 : ℝ) ≤ atomC r := one_le_atomC r
      have hCsucc : (1 : ℝ) ≤ atomC (r + 1) := one_le_atomC (r + 1)
      have hCsucc0 : (0 : ℝ) ≤ atomC (r + 1) := atomC_nonneg (r + 1)
      constructor
      · intro a b ha hb hab l S hnd hav hlen hcard
        match l with
        | [] =>
            have hU : (S ∪ T).card ≤ M := by
              refine le_trans (Finset.card_union_le S T) ?_
              simp only [List.length_nil, Nat.add_zero] at hcard
              omega
            have h := hg.off_le (S ∪ T) hU a b hab
            simp only [iterDeltaFam_nil, List.length_nil, gFam_apply, Nat.add_zero, pow_one]
            nlinarith
        | κ :: l' =>
            have hcardl : S.card + l'.length + 1 ≤ B := by
              simp only [List.length_cons] at hcard; omega
            obtain ⟨B', rfl⟩ : ∃ B', B = B' + 1 := ⟨B - 1, by omega⟩
            have hκI : κ ∉ I := hav κ List.mem_cons_self
            have hnd' : l'.Nodup := (List.nodup_cons.1 hnd).2
            have hκl' : κ ∉ l' := (List.nodup_cons.1 hnd).1
            have hav' : ∀ κ' ∈ l', κ' ∉ insert κ I := by
              intro κ' hκ' hmem
              rcases Finset.mem_insert.1 hmem with h1 | h1
              · exact hκl' (h1 ▸ hκ')
              · exact hav κ' (List.mem_cons_of_mem _ hκ') h1
            have hlen' : l'.length ≤ r := by
              simp only [List.length_cons] at hlen; omega
            obtain ⟨ihoff, ihinv⟩ := ih (insert κ I) T B' (by omega)
            have haκ : a ≠ κ := fun h => hκI (h ▸ ha)
            have hκb : κ ≠ b := fun h => hκI (h ▸ hb)
            have hA := ihoff a κ (Finset.mem_insert_of_mem ha) (Finset.mem_insert_self κ I) haκ
            have hB2 := ihoff κ b (Finset.mem_insert_self κ I) (Finset.mem_insert_of_mem hb) hκb
            have hC := ihinv κ (Finset.mem_insert_self κ I)
            have hAB := DiffBd.mul hΨ0 r hc0 hc0 hA hB2
            have hABC := DiffBd.mul hΨ0 r (by positivity) hc0 hAB hC
            have hle : (2 : ℝ) ^ r * (2 ^ r * (atomC r * atomC r) * atomC r) ≤ atomC (r + 1) := by
              have hexp : (2 : ℝ) ^ r * (2 ^ r * (atomC r * atomC r) * atomC r)
                  = (2 ^ r * 2 ^ r) * atomC r ^ 3 := by ring
              have h4 : (2 : ℝ) ^ r * 2 ^ r = 4 ^ r := by rw [← mul_pow]; norm_num
              have hc3 : atomC r ^ 3 ≤ atomC r ^ 5 := pow_le_pow_right₀ hc1 (by norm_num)
              have h416 : (4 : ℝ) ^ r ≤ 16 ^ r := pow_le_pow_left₀ (by norm_num) (by norm_num) r
              rw [hexp, h4, atomC_succ]
              exact mul_le_mul h416 hc3 (pow_nonneg hc0 3) (pow_nonneg (by norm_num) r)
            have hkey : DiffBd Ψ (insert κ I) B' r (atomC (r + 1)) 2
                (deltaFam κ (gFam sz n u z ω a b T)) := by
              refine (hABC.mono_c hΨ0 hle).congr fun U hU => ?_
              refine (deltaFam_gFam_apply hg a b κ T U ?_).symm
              refine le_trans (Finset.card_insert_le κ (U ∪ T)) ?_
              have := Finset.card_union_le U T
              omega
            have hres := hkey l' S hnd' hav' hlen' (by omega)
            rw [iterDeltaFam_cons]
            have hexp2 : 2 + l'.length = 1 + (κ :: l').length := by
              simp only [List.length_cons]; omega
            rwa [hexp2] at hres
      · intro a ha l S hnd hav hlen hcard
        match l with
        | [] =>
            have hU : (S ∪ T).card ≤ M := by
              refine le_trans (Finset.card_union_le S T) ?_
              simp only [List.length_nil, Nat.add_zero] at hcard
              omega
            have h := hg.inv_le (S ∪ T) hU a
            simp only [iterDeltaFam_nil, List.length_nil, gInvFam_apply, Nat.add_zero, pow_zero,
              mul_one]
            exact le_trans h (two_le_atomC (r + 1))
        | κ :: l' =>
            have hcardl : S.card + l'.length + 1 ≤ B := by
              simp only [List.length_cons] at hcard; omega
            obtain ⟨B', rfl⟩ : ∃ B', B = B' + 1 := ⟨B - 1, by omega⟩
            have hκI : κ ∉ I := hav κ List.mem_cons_self
            have hnd' : l'.Nodup := (List.nodup_cons.1 hnd).2
            have hκl' : κ ∉ l' := (List.nodup_cons.1 hnd).1
            have hav' : ∀ κ' ∈ l', κ' ∉ insert κ I := by
              intro κ' hκ' hmem
              rcases Finset.mem_insert.1 hmem with h1 | h1
              · exact hκl' (h1 ▸ hκ')
              · exact hav κ' (List.mem_cons_of_mem _ hκ') h1
            have hlen' : l'.length ≤ r := by
              simp only [List.length_cons] at hlen; omega
            obtain ⟨ihoff, ihinv⟩ := ih (insert κ I) T B' (by omega)
            have hTκ : B' + (insert κ T).card ≤ M :=
              le_trans (by have := Finset.card_insert_le κ T; omega) hB
            obtain ⟨_, ihinv'⟩ := ih (insert κ I) (insert κ T) B' hTκ
            have haκ : a ≠ κ := fun h => hκI (h ▸ ha)
            have hA := ihoff a κ (Finset.mem_insert_of_mem ha) (Finset.mem_insert_self κ I) haκ
            have hB2 := ihoff κ a (Finset.mem_insert_self κ I) (Finset.mem_insert_of_mem ha)
              (fun h => haκ h.symm)
            have hC := ihinv κ (Finset.mem_insert_self κ I)
            have hD := ihinv a (Finset.mem_insert_of_mem ha)
            have hE := ihinv' a (Finset.mem_insert_of_mem ha)
            have h1 := DiffBd.mul hΨ0 r hc0 hc0 hA hB2
            have h2 := DiffBd.mul hΨ0 r (by positivity) hc0 h1 hC
            have h3 := DiffBd.mul hΨ0 r (by positivity) hc0 h2 hD
            have h4 := DiffBd.mul hΨ0 r (by positivity) hc0 h3 hE
            have hle : (2 : ℝ) ^ r * (2 ^ r * (2 ^ r * (2 ^ r * (atomC r * atomC r) * atomC r)
                * atomC r) * atomC r) ≤ atomC (r + 1) := by
              have hexp : (2 : ℝ) ^ r * (2 ^ r * (2 ^ r * (2 ^ r * (atomC r * atomC r) * atomC r)
                  * atomC r) * atomC r) = (2 ^ r * 2 ^ r * 2 ^ r * 2 ^ r) * atomC r ^ 5 := by ring
              have h16 : (2 : ℝ) ^ r * 2 ^ r * 2 ^ r * 2 ^ r = 16 ^ r := by
                rw [← mul_pow, ← mul_pow, ← mul_pow]; norm_num
              rw [hexp, h16, atomC_succ]
            have hkey : DiffBd Ψ (insert κ I) B' r (atomC (r + 1)) 1
                (deltaFam κ (gInvFam sz n u z ω a T)) := by
              refine (((h4.mono_c hΨ0 hle).neg).mono_p hΨ0 hΨ1 hCsucc0
                (by norm_num)).congr fun U hU => ?_
              refine (deltaFam_gInvFam_apply hg a κ haκ T U ?_).symm
              refine le_trans (Finset.card_insert_le κ (U ∪ T)) ?_
              have := Finset.card_union_le U T
              omega
            have hres := hkey l' S hnd' hav' hlen' (by omega)
            rw [iterDeltaFam_cons]
            have hexp2 : 1 + l'.length = 0 + (κ :: l').length := by
              simp only [List.length_cons]; omega
            rwa [hexp2] at hres

end AtomInduction


/-! ### The `m`-fold difference of the centred diagonal entry -/

section TopLevel

variable {u : ℝ} {z m : ℂ} {ω : Sizes.SeqΩ sz} {Ψ : ℝ} {M : ℕ}

/-- **The first difference of `G^{(·)}_{kk} - m` is the (4.9) triple product, at one level
inside the budget.**  The centring constant `m` cancels, and the extension by `0` at the levels
containing `k` is harmless.  Pointwise form of
`RBM.Green.deltaFam_greenSetDiagCentered`, on the satisfiable good event. -/
theorem deltaFam_greenSetDiagCentered_apply (hg : MinorGoodLe sz n u z m ω Ψ M)
    (k κ : Idx d (sz.L n) (sz.W n))
    (hkκ : k ≠ κ) (S : Finset (Idx d (sz.L n) (sz.W n))) (hcard : (insert κ S).card ≤ M) :
    deltaFam κ (fun S => greenSetDiagCentered sz n u z m k S ω) S
      = gFam sz n u z ω k κ ∅ S * gFam sz n u z ω κ k ∅ S * gInvFam sz n u z ω κ ∅ S := by
  rw [← deltaFam_gFam_apply hg k k κ ∅ S (by simpa using hcard)]
  simp only [deltaFam_apply, gFam_apply, Finset.union_empty, greenSetDiagCentered]
  by_cases hk : k ∉ S
  · have hk' : k ∉ insert κ S := by
      simp only [Finset.mem_insert, not_or]
      exact ⟨hkκ, hk⟩
    rw [dite_eq_left hk, dite_eq_left hk', gEnt_apply hk hk, gEnt_apply hk' hk']
    ring
  · have hkS : k ∈ S := not_not.1 hk
    have hk' : k ∈ insert κ S := Finset.mem_insert_of_mem hkS
    rw [dite_eq_right hk, dite_eq_right (not_not_intro hk'), gEnt_eq_zero_left hkS,
      gEnt_eq_zero_left hk']

/-- The constant of the `m`-fold estimate: three atoms, each carried through `m - 1`
differences. -/
noncomputable def minorDiffC (n : ℕ) : ℝ := 4 ^ n * atomC n ^ 3

theorem minorDiffC_nonneg (n : ℕ) : (0 : ℝ) ≤ minorDiffC n := by
  unfold minorDiffC
  have := atomC_nonneg n
  positivity

theorem one_le_minorDiffC (n : ℕ) : (1 : ℝ) ≤ minorDiffC n := by
  unfold minorDiffC
  have h1 : (1 : ℝ) ≤ 4 ^ n := one_le_pow₀ (by norm_num)
  have h2 : (1 : ℝ) ≤ atomC n ^ 3 := one_le_pow₀ (one_le_atomC n)
  nlinarith

theorem atomC_le_succ (n : ℕ) : atomC n ≤ atomC (n + 1) := by
  have h1 : (1 : ℝ) ≤ atomC n := one_le_atomC n
  have h16 : (1 : ℝ) ≤ 16 ^ n := one_le_pow₀ (by norm_num)
  have h5 : atomC n ≤ atomC n ^ 5 := by
    calc atomC n = atomC n ^ 1 := (pow_one _).symm
      _ ≤ atomC n ^ 5 := pow_le_pow_right₀ h1 (by norm_num)
  rw [atomC_succ]
  nlinarith [pow_nonneg (atomC_nonneg n) 5]

theorem atomC_mono {a b : ℕ} (h : a ≤ b) : atomC a ≤ atomC b := by
  induction b with
  | zero => simp only [Nat.le_zero.1 h]; exact le_rfl
  | succ b ih =>
      rcases Nat.lt_or_ge a (b + 1) with h1 | h1
      · exact le_trans (ih (Nat.lt_succ_iff.1 h1)) (atomC_le_succ b)
      · have : a = b + 1 := le_antisymm h h1
        subst this; exact le_rfl

theorem minorDiffC_mono {a b : ℕ} (h : a ≤ b) : minorDiffC a ≤ minorDiffC b := by
  unfold minorDiffC
  have h4 : (4 : ℝ) ^ a ≤ 4 ^ b := pow_le_pow_right₀ (by norm_num) h
  have hc : atomC a ^ 3 ≤ atomC b ^ 3 :=
    pow_le_pow_left₀ (atomC_nonneg a) (atomC_mono h) 3
  have hc0 : (0 : ℝ) ≤ atomC a ^ 3 := pow_nonneg (atomC_nonneg a) 3
  exact mul_le_mul h4 hc hc0 (by positivity)

/-- **The size of the `m`-fold minor difference, `m ≥ 1`** (here `m = l.length + 1`):

  `‖Δ_{κ_1} ⋯ Δ_{κ_m} (G^{(·)}_{kk} - m)‖ ≤ C_m Ψ^{m+1}`,   `C_m = minorDiffC (m - 1)`,

on `MinorGoodLe`, for distinct rows `κ_i ≠ k` and `m ≤ M`.  The first difference is the (4.9)
triple product (order `2`), and each of the remaining `m - 1` differences gains one more power of
`Ψ` by `diffBd_atom`. -/
theorem norm_minorDiff_greenSetDiagCentered_le (hg : MinorGoodLe sz n u z m ω Ψ M) (hΨ0 : 0 ≤ Ψ)
    (hΨ1 : Ψ ≤ 1) (k κ : Idx d (sz.L n) (sz.W n)) (l : List (Idx d (sz.L n) (sz.W n))) (hkκ : k ≠ κ)
    (hnd : (κ :: l).Nodup) (hkl : ∀ x ∈ l, x ≠ k) (hM : l.length + 1 ≤ M) :
    ‖minorDiff sz n (κ :: l) (greenSetDiagCentered sz n u z m k) ω‖
      ≤ minorDiffC l.length * Ψ ^ (l.length + 2) := by
  classical
  rw [minorDiff_eq_iterDeltaFam, iterDeltaFam_cons]
  obtain ⟨ihoff, ihinv⟩ :=
    diffBd_atom hg hΨ0 hΨ1 l.length ({k, κ} : Finset (Idx d (sz.L n) (sz.W n))) ∅ l.length
      (by simp; omega)
  have hkI : k ∈ ({k, κ} : Finset (Idx d (sz.L n) (sz.W n))) := Finset.mem_insert_self _ _
  have hκI : κ ∈ ({k, κ} : Finset (Idx d (sz.L n) (sz.W n))) := by simp
  have hA := ihoff k κ hkI hκI hkκ
  have hB := ihoff κ k hκI hkI (Ne.symm hkκ)
  have hC := ihinv κ hκI
  have hAB := DiffBd.mul hΨ0 l.length (atomC_nonneg _) (atomC_nonneg _) hA hB
  have hABC := DiffBd.mul hΨ0 l.length
    (by have := atomC_nonneg l.length; positivity) (atomC_nonneg _) hAB hC
  have hkey := hABC.congr fun U hU =>
    (deltaFam_greenSetDiagCentered_apply hg k κ hkκ U
      (le_trans (Finset.card_insert_le κ U) (by omega))).symm
  have hav : ∀ κ' ∈ l, κ' ∉ ({k, κ} : Finset (Idx d (sz.L n) (sz.W n))) := by
    intro κ' hκ' hmem
    rcases Finset.mem_insert.1 hmem with h1 | h1
    · exact hkl κ' hκ' h1
    · exact (List.nodup_cons.1 hnd).1 (by rw [← Finset.mem_singleton.1 h1]; exact hκ')
  have hres := hkey l ∅ (List.nodup_cons.1 hnd).2 hav le_rfl (by simp)
  refine le_trans hres (le_of_eq ?_)
  unfold minorDiffC
  have hexp : 1 + 1 + 0 + l.length = l.length + 2 := by omega
  rw [hexp]
  have h4 : (2 : ℝ) ^ l.length * 2 ^ l.length = 4 ^ l.length := by
    rw [← mul_pow]; norm_num
  have : (2 : ℝ) ^ l.length * (2 ^ l.length * (atomC l.length * atomC l.length)
      * atomC l.length) = (2 ^ l.length * 2 ^ l.length) * atomC l.length ^ 3 := by ring
  rw [this, h4]

/-! #### The undifferenced entry: the `m = 0` grade

The empty word is the one grade of the expansion that the `Δ_κ` calculus never touches: the family
`G^{(S)}_{kk} - m` itself is bounded by the field `diag_sub_le` of `MinorGoodLe`, (4.3). -/

/-- **(4.3) at every minor level inside the budget**: `|G^{(S)}_{kk} - m| ≤ Ψ`, including the
levels that remove `k`, where the family is `0` by convention. -/
theorem norm_greenSetDiagCentered_le (hg : MinorGoodLe sz n u z m ω Ψ M) (hΨ0 : 0 ≤ Ψ)
    (k : Idx d (sz.L n) (sz.W n)) (S : Finset (Idx d (sz.L n) (sz.W n))) (hS : S.card ≤ M) :
    ‖greenSetDiagCentered sz n u z m k S ω‖ ≤ Ψ := by
  change ‖if h : k ∉ S then greenSetMat sz n u z S ω ⟨k, h⟩ ⟨k, h⟩ - m else 0‖ ≤ Ψ
  by_cases hk : k ∉ S
  · rw [dite_eq_left hk, ← gEnt_apply hk hk]
    exact hg.diag_sub_le S hS k hk
  · rw [dite_eq_right hk, norm_zero]
    exact hΨ0

end TopLevel


/-! ### The fluctuation passes through the difference -/

section Assembly

variable {E t : ℝ}

/-- **`Δ_{κ_1} ⋯ Δ_{κ_m}` commutes with `Q_k = 1 - E_k`.**  The difference is a linear
combination with constant coefficients, and `E_k` is linear, so the whole `m`-fold difference of
the *fluctuations* is the fluctuation of the `m`-fold difference.  This is what lets the consumer
bound `minorDiff … (flucDiagSet …)` (the quantity of `MinorDiffGainUpTo'`) through the
deterministic family `greenSetDiagCentered`. -/
theorem minorDiff_qRow (k : Idx d (sz.L n) (sz.W n)) :
    ∀ (l : List (Idx d (sz.L n) (sz.W n)))
      (Y : Finset (Idx d (sz.L n) (sz.W n)) → Sizes.SeqΩ sz → ℂ),
    (∀ S, BddMeas sz (Y S)) →
    minorDiff sz n l (fun S => qRow sz n k (Y S)) = qRow sz n k (minorDiff sz n l Y) := by
  intro l
  induction l with
  | nil => intro Y _; rfl
  | cons κ l ih =>
      intro Y hY
      simp only [minorDiff_cons]
      have hstep : (fun (S : Finset (Idx d (sz.L n) (sz.W n))) (ω : Sizes.SeqΩ sz) =>
            qRow sz n k (Y S) ω - qRow sz n k (Y (insert κ S)) ω)
          = fun S => qRow sz n k (fun ω => Y S ω - Y (insert κ S) ω) := by
        funext S
        rw [qRow_sub k (hY S) (hY (insert κ S))]
      rw [hstep]
      exact ih _ fun S => (hY S).sub (hY _)

theorem minorDiff_flucDiagSet_eq (hE : |E| < 2) (ht : t < 1) (u : ℝ) (k : Idx d (sz.L n) (sz.W n))
    (l : List (Idx d (sz.L n) (sz.W n))) :
    minorDiff sz n l (flucDiagSet sz n u (zt E t) (mE E) k)
      = qRow sz n k (minorDiff sz n l (greenSetDiagCentered sz n u (zt E t) (mE E) k)) :=
  minorDiff_qRow k l _ fun S => bddMeas_greenSetDiagCentered hE ht u k S

theorem qList_nodup {L : List (Bool × Idx d (sz.L n) (sz.W n))} (h : (L.map Prod.snd).Nodup) :
    (qList L).Nodup :=
  List.Nodup.sublist (List.Sublist.map Prod.snd List.filter_sublist) h

theorem mem_qList_ne {L : List (Bool × Idx d (sz.L n) (sz.W n))} {k : Idx d (sz.L n) (sz.W n)}
    (h : ∀ x ∈ L, x.2 ≠ k)
    {y : Idx d (sz.L n) (sz.W n)} (hy : y ∈ qList L) : y ≠ k := by
  have hsub := (List.Sublist.map Prod.snd
    (List.filter_sublist (p := fun x : Bool × Idx d (sz.L n) (sz.W n) => x.1)
    (l := L))).subset hy
  obtain ⟨p, hp, hpy⟩ := List.mem_map.1 hsub
  exact hpy ▸ h p hp

theorem bddMeas_minorDiff (l : List (Idx d (sz.L n) (sz.W n)))
    (Y : Finset (Idx d (sz.L n) (sz.W n)) → Sizes.SeqΩ sz → ℂ) (hY : ∀ S, BddMeas sz (Y S)) :
    BddMeas sz (minorDiff sz n l Y) := by
  induction l generalizing Y with
  | nil => simpa using hY ∅
  | cons κ l ih =>
      rw [minorDiff_cons]
      exact ih _ fun S => (hY S).sub (hY _)

theorem bddMeas_applyOps_minorDiff_flucDiagSet (hE : |E| < 2) (ht : t < 1) (u : ℝ)
    (k : Idx d (sz.L n) (sz.W n)) (L : List (Bool × Idx d (sz.L n) (sz.W n))) :
    BddMeas sz (applyOps sz n L
      (minorDiff sz n (qList L) (flucDiagSet sz n u (zt E t) (mE E) k))) :=
  BddMeas.applyOps (bddMeas_minorDiff _ _ fun S => bddMeas_flucDiagSet hE ht u k S) L

end Assembly
/-! ### Compiled nonempty instances at `d = 3`, `L = 3`, `W = 2`, `lam = 1/2`, `u = 1/31`

`RBM.Green.MinorDiffInst.szM` is the constant size sequence `d = 3`, `L n = 3`, `W n = 2`,
`lam n = 1/2` (no limit statement is claimed at it), at the slice `n = 0`: `N = (W L)^3 = 216`
sites.  The five sites are `A = (0,0,0)`, `B = (0,0,1)`, `C = (0,1,0)`, `D = (1,0,0)`,
`E = (1,1,0)` of the fine lattice `Z_6^3`.

The sample point is `ω = 0`, `E = 0`, `u = t = 1/31`: `H_u = 0`, `z_u = (30/31) i`,
`G = -z_u⁻¹ 1 = (31/30) i 1`, `m = i`, so `‖G - m 1‖_max = 1/30 = Ψ₀`: (4.1) holds exactly at
`Ψ₀ = 1/30`, with `Ψ₀ ≤ 1/4` and `8 M Ψ₀ = 4/5 ≤ 1` at `M = 3`, and `MinorGoodLe` holds at the
threshold `Ψ = 2 Ψ₀ = 1/15` (`minorGoodLe_of_goodEvent_flow`, every hypothesis proved).  The
endpoint theorems are applied at three distinct rows `κ, κ', κ''` (`B, C, D`) besides `k = A`, at
the top of the budget `m = 3 = M`.  The hypotheses of every instance are proved, not assumed.

At `ω = 0` the matrix is diagonal, so the `Δ` themselves vanish and the bounds are trivially
satisfied at this point; the hypotheses are non-empty (`Ψ ≠ 0`, three distinct rows, `M = 3`,
`G ≠ m 1`), and the families are not constant: `G^{(S)}_{aa}` is `(31/30) i` for `a ∉ S` and `0`
for `a ∈ S` (`inst_gEnt_nonconst`).  There is no external hypothesis. -/

namespace MinorDiffInst

noncomputable section

/-- The sizes `d = 3`, `L = 3`, `W = 2`, `lam = 1/2` (constant sequences). -/
private def szM : Sizes 3 where
  L := fun _ => 3
  W := fun _ => 2
  lam := fun _ => 1 / 2
  three_le_L := fun _ => le_rfl
  W_pos := fun _ => by norm_num

/-- Five sites of the fine lattice `Z_6^3`. -/
private def siteA : Idx 3 (szM.L 0) (szM.W 0) := ![0, 0, 0]
private def siteB : Idx 3 (szM.L 0) (szM.W 0) := ![0, 0, 1]
private def siteC : Idx 3 (szM.L 0) (szM.W 0) := ![0, 1, 0]
private def siteD : Idx 3 (szM.L 0) (szM.W 0) := ![1, 0, 0]
private def siteE : Idx 3 (szM.L 0) (szM.W 0) := ![1, 1, 0]

private theorem hE0 : |(0 : ℝ)| < 2 := by norm_num

private theorem hBA : siteB ≠ siteA := by decide
private theorem hCA : siteC ≠ siteA := by decide
private theorem hDA : siteD ≠ siteA := by decide
private theorem hCB : siteC ≠ siteB := by decide
private theorem hDB : siteD ≠ siteB := by decide
private theorem hDC : siteD ≠ siteC := by decide
private theorem hAB : siteA ≠ siteB := hBA.symm
private theorem hAD : siteA ≠ siteD := hDA.symm
private theorem hBC : siteB ≠ siteC := hCB.symm
private theorem hBD : siteB ≠ siteD := hDB.symm
private theorem hCD : siteC ≠ siteD := hDC.symm

/-! #### The sample point `ω = 0` -/

private theorem seqHflow_zero_omega (u : ℝ) :
    Sizes.seqHflow szM 0 u (0 : Sizes.SeqΩ szM) = 0 := by
  rw [Sizes.seqHflow_eq_smul]
  have h : Sizes.seqXmat szM 0 (0 : Sizes.SeqΩ szM) = 0 := by
    ext i j
    simp [Sizes.seqXmat, Xmat, Xentry, Sizes.slice]
  rw [h, smul_zero]

private theorem sqrt_four : Real.sqrt 4 = 2 := by
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

/-- `m^{(0)} = i`. -/
private theorem mE_zero : mE 0 = Complex.I := by
  apply Complex.ext <;> simp [mE, sqrt_four]

/-- `z_u = zt 0 (1/31) = (30/31) i`. -/
private theorem zt_u : zt 0 (1 / 31) = (30 / 31 : ℂ) * Complex.I := by
  simp only [zt, mE_zero]
  push_cast
  ring

/-- `G = (0 - z)⁻¹ = (-z)⁻¹ • 1`. -/
private theorem green_zero {ν : Type*} [Fintype ν] [DecidableEq ν] {z : ℂ} (hz : z ≠ 0) :
    green (0 : Matrix ν ν ℂ) z = (-z)⁻¹ • (1 : Matrix ν ν ℂ) := by
  unfold green
  refine Matrix.inv_eq_right_inv ?_
  simp [smul_smul, inv_mul_cancel₀ hz]

/-- `(-z_u)⁻¹ = (31/30) i`. -/
private theorem inv_neg_zt : (-(zt 0 (1 / 31)))⁻¹ = (31 / 30 : ℂ) * Complex.I := by
  rw [zt_u]
  have hI : Complex.I ≠ 0 := Complex.I_ne_zero
  field_simp
  simp

private theorem zt_ne_zero : zt 0 (1 / 31) ≠ 0 := by
  rw [zt_u]
  exact mul_ne_zero (by norm_num) Complex.I_ne_zero

/-- `‖(31/30) i - i‖ = 1/30`. -/
private theorem norm_diag_sub : ‖(31 / 30 : ℂ) * Complex.I - Complex.I‖ = 1 / 30 := by
  have : (31 / 30 : ℂ) * Complex.I - Complex.I = ((1 / 30 : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [this, norm_mul, Complex.norm_I, mul_one, Complex.norm_real]
  norm_num

/-- (4.1) at `ω = 0`, `u = 1/31`, `E = 0`, `Ψ₀ = 1/30`: `G = (31/30) i 1`, `m = i`,
`‖G - m 1‖_max = 1/30`. -/
private theorem goodEvent_omega_zero :
    GoodEvent (green (Sizes.seqHflow szM 0 (1 / 31) (0 : Sizes.SeqΩ szM)) (zt 0 (1 / 31)))
      (mE 0) (1 / 30) := by
  rw [seqHflow_zero_omega, green_zero zt_ne_zero, inv_neg_zt, mE_zero]
  intro x y
  by_cases h : x = y
  · subst h
    simp only [Matrix.smul_apply, Matrix.one_apply_eq, ite_true, smul_eq_mul, mul_one]
    rw [norm_diag_sub]
  · simp [h]

private theorem zt_im_ne : (zt 0 (1 / 31)).im ≠ 0 := by
  rw [zt_u]
  simp

/-- **The hypothesis of the endpoints**: `MinorGoodLe` at `E = 0`, `u = 1/31`, `ω = 0`, `M = 3`,
threshold `Ψ = 2 · (1/30) = 1/15`, from `minorGoodLe_of_goodEvent_flow` with every hypothesis
proved (`|0| ≤ 2`, `Im z_u ≠ 0`, `0 ≤ 1/30`, `1/30 ≤ 1/4`, `8 · 3 · (1/30) ≤ 1`, and (4.1) at
`ω = 0`).  Private: a public theorem concluding `MinorGoodLe` would hide it from the premise scan. -/
private theorem check_hg :
    MinorGoodLe szM 0 (1 / 31) (zt 0 (1 / 31)) (mE 0) 0 (2 * (1 / 30)) 3 :=
  minorGoodLe_of_goodEvent_flow (E := 0) (by norm_num) zt_im_ne (by norm_num) (by norm_num)
    (by norm_num) goodEvent_omega_zero

/-- The families are not constant: `G^{(S)}_{aa}` is `(31/30) i` at the level `∅` and `0` at the
level `{a}`, and the level-`∅` entry is not `m = i`. -/
theorem inst_gEnt_nonconst :
    gEnt szM 0 (1 / 31) (zt 0 (1 / 31)) 0 siteA siteA ∅ = (31 / 30 : ℂ) * Complex.I
      ∧ gEnt szM 0 (1 / 31) (zt 0 (1 / 31)) 0 siteA siteA {siteA} = 0
      ∧ gEnt szM 0 (1 / 31) (zt 0 (1 / 31)) 0 siteA siteA ∅ ≠ mE 0 := by
  refine ⟨?_, gEnt_eq_zero_left (Finset.mem_singleton_self _), ?_⟩
  · rw [gEnt_empty, seqHflow_zero_omega, green_zero zt_ne_zero, inv_neg_zt]
    simp
  · rw [gEnt_empty, seqHflow_zero_omega, green_zero zt_ne_zero, inv_neg_zt, mE_zero]
    simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]
    intro h
    have h2 := congrArg Complex.im h
    simp at h2
    norm_num at h2

/-- `atomC 1 = 32`, `atomC 2 = 2^29`, `minorDiffC 1 = 131072 = 4 · 32³`, `minorDiffC 2 = 2^91`. -/
theorem inst_constants :
    atomC 1 = 32 ∧ atomC 2 = 2 ^ 29 ∧ minorDiffC 1 = 131072 ∧ minorDiffC 2 = 2 ^ 91 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> norm_num [minorDiffC, atomC]

/-! #### The endpoint `norm_minorDiff_greenSetDiagCentered_le` and the `m = 0` grade -/

/-- **Instance of `norm_minorDiff_greenSetDiagCentered_le`** (the second difference
`m = 3 = M`): `k = A`, `κ = B`, `l = [C, D]`: `(κ :: l).Nodup`, `l.length + 1 = 3 ≤ M = 3`,
`0 ≤ Ψ = 1/15 ≤ 1`; every hypothesis is proved. -/
theorem inst_endpoint :
    ‖minorDiff szM 0 [siteB, siteC, siteD]
        (greenSetDiagCentered szM 0 (1 / 31) (zt 0 (1 / 31)) (mE 0) siteA) 0‖
      ≤ minorDiffC [siteC, siteD].length * (2 * (1 / 30)) ^ ([siteC, siteD].length + 2) :=
  norm_minorDiff_greenSetDiagCentered_le check_hg (by norm_num) (by norm_num)
    siteA siteB [siteC, siteD] hAB (by simp [hBC, hBD, hCD]) (by simp [hCA, hDA]) (by decide)

/-- The same, with the constant evaluated: `C_2 Ψ^4 = 2^91 / 15^4`. -/
theorem inst_endpoint_num :
    ‖minorDiff szM 0 [siteB, siteC, siteD]
        (greenSetDiagCentered szM 0 (1 / 31) (zt 0 (1 / 31)) (mE 0) siteA) 0‖
      ≤ 2 ^ 91 / 15 ^ 4 := by
  refine le_trans inst_endpoint (le_of_eq ?_)
  simp only [List.length_cons, List.length_nil, zero_add]
  rw [show (0 + 1 + 1 : ℕ) = 2 by rfl, inst_constants.2.2.2]
  norm_num

/-- **Instance of `norm_greenSetDiagCentered_le`**: the level `S = {B, C, D}`, `|S| = 3 = M`. -/
theorem inst_diag :
    ‖greenSetDiagCentered szM 0 (1 / 31) (zt 0 (1 / 31)) (mE 0) siteA {siteB, siteC, siteD} 0‖
      ≤ 2 * (1 / 30) :=
  norm_greenSetDiagCentered_le check_hg (by norm_num) siteA {siteB, siteC, siteD} (by decide)

/-- The same at a level that removes `k` (the family is `0` by convention there). -/
theorem inst_diag_removed :
    ‖greenSetDiagCentered szM 0 (1 / 31) (zt 0 (1 / 31)) (mE 0) siteA {siteA, siteB} 0‖
      ≤ 2 * (1 / 30) :=
  norm_greenSetDiagCentered_le check_hg (by norm_num) siteA {siteA, siteB} (by decide)

/-- **Instance of `diffBd_atom`** at `r = 2`: `I = {A, B}`, base level `T = {E}` (`|T| = 1`), budget
`B = 2`, so `B + |T| = 3 = M` (tight). -/
theorem inst_atom :
    (∀ a b : Idx 3 (szM.L 0) (szM.W 0),
      a ∈ ({siteA, siteB} : Finset _) → b ∈ ({siteA, siteB} : Finset _) → a ≠ b →
      DiffBd (2 * (1 / 30)) ({siteA, siteB} : Finset _) 2 2 (atomC 2) 1
        (gFam szM 0 (1 / 31) (zt 0 (1 / 31)) 0 a b {siteE}))
    ∧ (∀ a : Idx 3 (szM.L 0) (szM.W 0),
      a ∈ ({siteA, siteB} : Finset _) →
      DiffBd (2 * (1 / 30)) ({siteA, siteB} : Finset _) 2 2 (atomC 2) 0
        (gInvFam szM 0 (1 / 31) (zt 0 (1 / 31)) 0 a {siteE})) :=
  diffBd_atom check_hg (by norm_num) (by norm_num) 2 {siteA, siteB} {siteE} 2 (by decide)

/-- A consequence of `inst_atom`: two differences along the rows `C, D ∉ I` of the entry
`G_{AB}` at the base level `T = {E}`. -/
theorem inst_atom_entry :
    ‖iterDeltaFam [siteC, siteD]
        (gFam szM 0 (1 / 31) (zt 0 (1 / 31)) 0 siteA siteB {siteE}) ∅‖
      ≤ atomC 2 * (2 * (1 / 30)) ^ (1 + 2) :=
  (inst_atom).1 siteA siteB (by simp) (by simp) hAB
    [siteC, siteD] ∅ (by simp [hCD]) (by simp [hCA, hCB, hDA, hDB]) (by simp) (by simp)

/-- The same for the inverse diagonal `(G_{AA})⁻¹`. -/
theorem inst_atom_inv :
    ‖iterDeltaFam [siteC, siteD]
        (gInvFam szM 0 (1 / 31) (zt 0 (1 / 31)) 0 siteA {siteE}) ∅‖
      ≤ atomC 2 * (2 * (1 / 30)) ^ (0 + 2) :=
  (inst_atom).2 siteA (by simp) [siteC, siteD] ∅ (by simp [hCD]) (by simp [hCA, hCB, hDA, hDB])
    (by simp) (by simp)

/-- **Instance of `deltaFam_gFam_apply`** (4.9): `κ = D`, `T = {E}`, `S = {C}`, level
`|{D, C, E}| = 3 ≤ M` (tight). -/
theorem inst_gFam :
    deltaFam siteD (gFam szM 0 (1 / 31) (zt 0 (1 / 31)) 0 siteA siteB {siteE}) {siteC}
      = gFam szM 0 (1 / 31) (zt 0 (1 / 31)) 0 siteA siteD {siteE} {siteC}
        * gFam szM 0 (1 / 31) (zt 0 (1 / 31)) 0 siteD siteB {siteE} {siteC}
        * gInvFam szM 0 (1 / 31) (zt 0 (1 / 31)) 0 siteD {siteE} {siteC} :=
  deltaFam_gFam_apply check_hg siteA siteB siteD {siteE} {siteC} (by decide)

/-- **Instance of `deltaFam_gInvFam_apply`**, the reciprocal rule at the same data. -/
theorem inst_gInvFam :
    deltaFam siteD (gInvFam szM 0 (1 / 31) (zt 0 (1 / 31)) 0 siteA {siteE}) {siteC}
      = -(gFam szM 0 (1 / 31) (zt 0 (1 / 31)) 0 siteA siteD {siteE} {siteC}
          * gFam szM 0 (1 / 31) (zt 0 (1 / 31)) 0 siteD siteA {siteE} {siteC}
          * gInvFam szM 0 (1 / 31) (zt 0 (1 / 31)) 0 siteD {siteE} {siteC}
          * gInvFam szM 0 (1 / 31) (zt 0 (1 / 31)) 0 siteA {siteE} {siteC}
          * gInvFam szM 0 (1 / 31) (zt 0 (1 / 31)) 0 siteA (insert siteD {siteE}) {siteC}) :=
  deltaFam_gInvFam_apply check_hg siteA siteD hAD {siteE} {siteC} (by decide)

/-- **Instance of `deltaFam_greenSetDiagCentered_apply`**: `k = A`, `κ = B`, level `{C, D}`,
`|{B, C, D}| = 3 ≤ M`. -/
theorem inst_first_diff :
    deltaFam siteB (fun S => greenSetDiagCentered szM 0 (1 / 31) (zt 0 (1 / 31))
        (mE 0) siteA S 0) {siteC, siteD}
      = gFam szM 0 (1 / 31) (zt 0 (1 / 31)) 0 siteA siteB ∅ {siteC, siteD}
        * gFam szM 0 (1 / 31) (zt 0 (1 / 31)) 0 siteB siteA ∅ {siteC, siteD}
        * gInvFam szM 0 (1 / 31) (zt 0 (1 / 31)) 0 siteB ∅ {siteC, siteD} :=
  deltaFam_greenSetDiagCentered_apply check_hg siteA siteB hAB {siteC, siteD} (by decide)

/-- **Instance of `minorDiff_eq_iterDeltaFam`** at the family `G^{(·)}_{kk} - m`, the word
`[B, C, D]`. -/
theorem inst_eq_iter :
    minorDiff szM 0 [siteB, siteC, siteD]
        (greenSetDiagCentered szM 0 (1 / 31) (zt 0 (1 / 31)) (mE 0) siteA) 0
      = iterDeltaFam [siteB, siteC, siteD]
          (fun S => greenSetDiagCentered szM 0 (1 / 31) (zt 0 (1 / 31)) (mE 0)
            siteA S 0) ∅ :=
  minorDiff_eq_iterDeltaFam _ _ 0

/-! #### The assembly: `Δ` commutes with `Q_k`, boundedness, the word `qList` -/

/-- The word `Q_B P_C Q_D`: two letters `Q` (rows `B, D`) and one `P` (row `C`). -/
private def word3 : List (Bool × Idx 3 (szM.L 0) (szM.W 0)) :=
  [(true, siteB), (false, siteC), (true, siteD)]

/-- **Instance of `bddMeas_applyOps_minorDiff_flucDiagSet`** (the key statement,
`MinorDiff:907`): `E = 0`, `t = u = 1/31` (`|E| < 2`, `t < 1`), `k = A`, the word `Q_B P_C Q_D`;
no further hypothesis. -/
theorem inst_bddMeas :
    BddMeas szM (applyOps szM 0 word3
      (minorDiff szM 0 (qList word3)
        (flucDiagSet szM 0 (1 / 31) (zt 0 (1 / 31)) (mE 0) siteA))) :=
  bddMeas_applyOps_minorDiff_flucDiagSet (E := 0) (t := 1 / 31) hE0 (by norm_num) (1 / 31)
    siteA word3

/-- The `Q`-rows of `word3` are `B, D`: a genuine second difference. -/
theorem inst_qList : qList word3 = [siteB, siteD] := rfl

/-- **Instance of `qList_nodup`**: the rows of the word `Q_B P_C Q_D` are distinct. -/
theorem inst_qList_nodup : (qList word3).Nodup :=
  qList_nodup (by simp [word3, hBC, hBD, hCD])

/-- **Instance of `mem_qList_ne`**: no row of the word is `k = A`. -/
theorem inst_mem_qList_ne : siteB ≠ siteA :=
  mem_qList_ne (L := word3) (k := siteA)
    (by simp [word3, hBA, hCA, hDA]) (y := siteB) (by simp [qList, word3])

/-- **Instance of `bddMeas_minorDiff`** at the family `G^{(·)}_{kk} - m`. -/
theorem inst_bddMeas_minorDiff :
    BddMeas szM (minorDiff szM 0 [siteB, siteC, siteD]
      (greenSetDiagCentered szM 0 (1 / 31) (zt 0 (1 / 31)) (mE 0) siteA)) :=
  bddMeas_minorDiff _ _ fun S =>
    bddMeas_greenSetDiagCentered (E := 0) (t := 1 / 31) hE0 (by norm_num) (1 / 31) siteA S

/-- **Instance of `minorDiff_qRow`** at the family `G^{(·)}_{kk} - m`: `Δ` commutes with `Q_A`. -/
theorem inst_qRow :
    minorDiff szM 0 [siteB, siteC, siteD]
        (fun S => qRow szM 0 siteA
          (greenSetDiagCentered szM 0 (1 / 31) (zt 0 (1 / 31)) (mE 0) siteA S))
      = qRow szM 0 siteA
          (minorDiff szM 0 [siteB, siteC, siteD]
            (greenSetDiagCentered szM 0 (1 / 31) (zt 0 (1 / 31)) (mE 0) siteA)) :=
  minorDiff_qRow siteA [siteB, siteC, siteD] _ fun S =>
    bddMeas_greenSetDiagCentered (E := 0) (t := 1 / 31) hE0 (by norm_num) (1 / 31) siteA S

/-- **Instance of `minorDiff_flucDiagSet_eq`** at the same data. -/
theorem inst_flucDiagSet_eq :
    minorDiff szM 0 [siteB, siteC, siteD]
        (flucDiagSet szM 0 (1 / 31) (zt 0 (1 / 31)) (mE 0) siteA)
      = qRow szM 0 siteA
          (minorDiff szM 0 [siteB, siteC, siteD]
            (greenSetDiagCentered szM 0 (1 / 31) (zt 0 (1 / 31)) (mE 0) siteA)) :=
  minorDiff_flucDiagSet_eq (E := 0) (t := 1 / 31) hE0 (by norm_num) (1 / 31) siteA
    [siteB, siteC, siteD]

/-! #### The calculus at toy families on `Fin 3`

The calculus lemmas and `DiffBd` do not mention `d`; they are applied at `α = Fin 3` and the families
`Y S = (1/2)^{|S|}`, `Z S = (1/4)^{|S|}`, which are not constant in `S` (`Δ_0 Y^{(∅)} = 1/2`,
`Δ_0 Z^{(∅)} = 3/4`). -/

/-- The toy families on `Fin 3`: `S ↦ r^{|S|}`, not constant in `S` for `r ≠ 1`. -/
private noncomputable def toyPow (r : ℝ) : Finset (Fin 3) → ℂ :=
  fun S => (r : ℂ) ^ S.card

private noncomputable abbrev toyHalf : Finset (Fin 3) → ℂ := toyPow (1 / 2)

private theorem toy_half_delta : deltaFam 0 toyHalf ∅ = 1 / 2 := by
  simp [deltaFam, toyPow]
  norm_num

private theorem toy_quarter_delta : deltaFam 0 (toyPow (1 / 4)) ∅ = 3 / 4 := by
  simp [deltaFam, toyPow]
  norm_num

/-- `Y_r = r^{|·|}` is of order `0` with constant `c` up to `1` difference, `Ψ = 1/2`, `M = 2`,
as soon as `0 ≤ r ≤ 1`, `1 ≤ c` and `1 - r ≤ c / 2` (`‖Δ_κ Y_r^{(∅)}‖ = 1 - r`). -/
private theorem toy_diffBd_pow {r c : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hc1 : 1 ≤ c)
    (hc2 : 1 - r ≤ c / 2) :
    DiffBd (1 / 2 : ℝ) (∅ : Finset (Fin 3)) 2 1 c 0 (toyPow r) := by
  intro l S _ _ hlen _
  have hnorm : ∀ s : ℕ, ‖(r : ℂ) ^ s‖ = r ^ s := fun s => by
    rw [norm_pow, Complex.norm_real, Real.norm_of_nonneg hr0]
  have hle1 : ∀ s : ℕ, r ^ s ≤ 1 := fun s => pow_le_one₀ hr0 hr1
  rcases l with _ | ⟨κ, _ | ⟨κ', l⟩⟩
  · simp only [iterDeltaFam_nil, List.length_nil, add_zero, pow_zero, mul_one, toyPow]
    rw [hnorm]
    exact le_trans (hle1 _) hc1
  · simp only [iterDeltaFam_cons, iterDeltaFam_nil, deltaFam_apply, List.length_cons,
      List.length_nil, zero_add, pow_one, toyPow]
    by_cases hκ : κ ∈ S
    · rw [Finset.insert_eq_of_mem hκ, sub_self, norm_zero]
      linarith
    · rw [Finset.card_insert_of_notMem hκ]
      have h2 : (r : ℂ) ^ S.card - (r : ℂ) ^ (S.card + 1) = ((r ^ S.card * (1 - r) : ℝ) : ℂ) := by
        push_cast; ring
      rw [h2, Complex.norm_real, Real.norm_of_nonneg (mul_nonneg (pow_nonneg hr0 _) (by linarith))]
      have h3 : r ^ S.card * (1 - r) ≤ 1 * (1 - r) :=
        mul_le_mul_of_nonneg_right (hle1 _) (by linarith)
      linarith
  · simp at hlen

/-- `Y = (1/2)^{|·|}` is of order `0` with constant `1` up to `1` difference, `Ψ = 1/2`, `M = 2`
(tight at `S = ∅`, `l = [κ]`: `‖Δ_κ Y^{(∅)}‖ = 1/2 = Ψ`). -/
private theorem toy_diffBd_half : DiffBd (1 / 2 : ℝ) (∅ : Finset (Fin 3)) 2 1 1 0 toyHalf :=
  toy_diffBd_pow (by norm_num) (by norm_num) le_rfl (by norm_num)

/-- **Instance of `DiffBd.mul`**: the product of the two different non-constant families
`Y = (1/2)^{|·|}` (`c₁ = 1`) and `Z = (1/4)^{|·|}` (`c₂ = 3/2`, tight), `n = 1`, `p = q = 0`:
constant `2^1 · (1 · 3/2) = 3`. -/
theorem inst_mul :
    DiffBd (1 / 2 : ℝ) (∅ : Finset (Fin 3)) 2 1 (2 ^ 1 * (1 * (3 / 2))) (0 + 0)
      (fun S => toyHalf S * toyPow (1 / 4) S) :=
  DiffBd.mul (by norm_num) 1 (by norm_num) (by norm_num) toy_diffBd_half
    (toy_diffBd_pow (by norm_num) (by norm_num) (by norm_num) (by norm_num))

/-- A consequence of `inst_mul`: `‖Δ_0 (Y Z)^{(∅)}‖ = 7/8 ≤ 3 · (1/2)^{0+0+1} = 3/2`. -/
theorem inst_mul_use :
    ‖iterDeltaFam [(0 : Fin 3)] (fun S => toyHalf S * toyPow (1 / 4) S) ∅‖
      ≤ 2 ^ 1 * (1 * (3 / 2)) * (1 / 2 : ℝ) ^ (0 + 0 + [(0 : Fin 3)].length) :=
  inst_mul [0] ∅ (by simp) (by simp) (by simp) (by simp)

/-- **Instance of `deltaFam_inv_apply`**: `Δ_0 (1/Y)^{(∅)} = -(Δ_0 Y^{(∅)} (Y^{(∅)})⁻¹ (Y^{({0})})⁻¹)`. -/
theorem inst_inv :
    deltaFam 0 (fun S => (toyHalf S)⁻¹) ∅
      = -(deltaFam 0 toyHalf ∅ * (toyHalf ∅)⁻¹ * (toyHalf (insert 0 ∅))⁻¹) :=
  deltaFam_inv_apply 0 toyHalf ∅ (by simp [toyPow]) (by simp [toyPow])

/-- **Instance of `deltaFam_mul`** (the Leibniz rule): `Δ_0 (Y Z)^{(∅)} = 7/8`. -/
theorem inst_leibniz :
    deltaFam (0 : Fin 3) (fun S => toyHalf S * toyPow (1 / 4) S) ∅ = 7 / 8 := by
  rw [congrFun (deltaFam_mul (0 : Fin 3) toyHalf (toyPow (1 / 4))) ∅,
    toy_half_delta, toy_quarter_delta]
  simp [toyPow]
  norm_num

/-- The calculus lemmas without hypotheses at the toy families: `Δ_κ` and the shift commute
(`deltaFam_shiftFam`, `iterDeltaFam_shiftFam`), and `Δ_κ`, `Δ_{κ_1} Δ_{κ_2}` are additive and odd
(`deltaFam_add`, `deltaFam_neg`, `iterDeltaFam_add`, `iterDeltaFam_neg`). -/
theorem inst_calculus :
    deltaFam (0 : Fin 3) (shiftFam 1 toyHalf) = shiftFam 1 (deltaFam 0 toyHalf)
      ∧ iterDeltaFam [(0 : Fin 3), 2] (shiftFam 1 toyHalf)
        = shiftFam 1 (iterDeltaFam [0, 2] toyHalf)
      ∧ deltaFam (0 : Fin 3) (fun S => toyHalf S + toyPow (1 / 4) S)
        = (fun S => deltaFam 0 toyHalf S + deltaFam 0 (toyPow (1 / 4)) S)
      ∧ deltaFam (0 : Fin 3) (fun S => -toyHalf S) = (fun S => -deltaFam 0 toyHalf S)
      ∧ iterDeltaFam [(0 : Fin 3), 2] (fun S => toyHalf S + toyPow (1 / 4) S)
        = (fun S => iterDeltaFam [0, 2] toyHalf S + iterDeltaFam [0, 2] (toyPow (1 / 4)) S)
      ∧ iterDeltaFam [(0 : Fin 3), 2] (fun S => -toyHalf S)
        = (fun S => -iterDeltaFam [0, 2] toyHalf S) :=
  ⟨deltaFam_shiftFam 0 1 _, iterDeltaFam_shiftFam [0, 2] 1 _, deltaFam_add 0 _ _,
    deltaFam_neg 0 _, iterDeltaFam_add [0, 2] _ _, iterDeltaFam_neg [0, 2] _⟩

/-- The constants: `atomC 0 = 2 ≤ atomC 2`, `atomC 1 ≤ atomC 2` and `1 ≤ minorDiffC 0 = 8 ≤
minorDiffC 2` (`atomC_mono`, `minorDiffC_mono`, `atomC_le_succ`, `two_le_atomC`, `one_le_atomC`,
`atomC_nonneg`, `one_le_minorDiffC`, `minorDiffC_nonneg`). -/
theorem inst_monotone :
    atomC 0 ≤ atomC 2 ∧ atomC 1 ≤ atomC 2 ∧ 2 ≤ atomC 1 ∧ 1 ≤ atomC 1 ∧ 0 ≤ atomC 1
      ∧ minorDiffC 0 ≤ minorDiffC 2 ∧ 1 ≤ minorDiffC 0 ∧ 0 ≤ minorDiffC 0 :=
  ⟨atomC_mono (by norm_num), atomC_le_succ 1, two_le_atomC 1, one_le_atomC 1, atomC_nonneg 1,
    minorDiffC_mono (by norm_num), one_le_minorDiffC 0, minorDiffC_nonneg 0⟩

/-- **Instance of `iterDeltaFam_congr`**: two families that agree at the levels `≤ 1` have the same
`Δ_0` at the level `∅` (`0 + 1 ≤ 1`). -/
theorem inst_congr :
    iterDeltaFam [(0 : Fin 3)] toyHalf ∅
      = iterDeltaFam [(0 : Fin 3)] (fun S => if S.card ≤ 1 then toyHalf S else 0) ∅ :=
  iterDeltaFam_congr [(0 : Fin 3)] (M := 1) (fun U hU => by simp [hU]) ∅ (by simp)

/-- `DiffBd.le_self`, `diffBd_zero`, `DiffBd.mono_*`, `DiffBd.neg`, `DiffBd.congr`,
`DiffBd.delta`, `DiffBd.shift` at the toy family. -/
theorem inst_le_self : ‖toyHalf ∅‖ ≤ 1 * (1 / 2 : ℝ) ^ 0 :=
  toy_diffBd_half.le_self ∅ (by simp)

theorem inst_zero : DiffBd (1 / 2 : ℝ) (∅ : Finset (Fin 3)) 2 0 1 0 toyHalf :=
  diffBd_zero fun S hS => toy_diffBd_half.le_self S hS

theorem inst_mono :
    DiffBd (1 / 2 : ℝ) ({0} : Finset (Fin 3)) 1 0 2 0 toyHalf :=
  (((toy_diffBd_half.mono_I (I' := {0}) (by simp)).mono_n
    (n' := 0) (by norm_num)).mono_M (M' := 1) (by norm_num)).mono_c (by norm_num)
    (c' := 2) (by norm_num)

theorem inst_neg :
    DiffBd (1 / 2 : ℝ) (∅ : Finset (Fin 3)) 2 1 1 0 (fun S => -toyHalf S) :=
  toy_diffBd_half.neg

theorem inst_congrBd :
    DiffBd (1 / 2 : ℝ) (∅ : Finset (Fin 3)) 2 1 1 0
      (fun S => if S.card ≤ 2 then toyHalf S else 0) :=
  toy_diffBd_half.congr fun S hS => by simp [hS]

theorem inst_delta :
    DiffBd (1 / 2 : ℝ) (insert (0 : Fin 3) ∅) 1 0 1 (0 + 1) (deltaFam 0 toyHalf) :=
  DiffBd.delta (by simp) toy_diffBd_half

theorem inst_mono_p :
    DiffBd (1 / 2 : ℝ) (insert (0 : Fin 3) ∅) 1 0 1 0 (deltaFam 0 toyHalf) :=
  inst_delta.mono_p (by norm_num) (by norm_num) (by norm_num) (Nat.zero_le _)

theorem inst_shift :
    DiffBd (1 / 2 : ℝ) (∅ : Finset (Fin 3)) 1 1 1 0 (shiftFam 0 toyHalf) :=
  DiffBd.shift toy_diffBd_half 0

end

end MinorDiffInst

end RBM.Green
