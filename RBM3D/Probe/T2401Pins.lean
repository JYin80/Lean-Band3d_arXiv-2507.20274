/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.BA.GreenCore
import RBM3D.Green.FlucIterGain
import RBM3D.Green.MinorDiff

/-!
# T2401 probe (BA-G5a design gate, probe step of CONTROL H194; never merged, no root import)

The Lean form of the pins of the design gate `docs/reports/T2401-prove.md`, section (G), G.8 (rows S1-S7), and of the
structural lemma (ii) of the ticket (`GreenMinor_cross`, `GreenMinor_removal_cross`, `GreenMinor_offset_ne`).

* A theorem row of G.8 is written as a closed `Prop` (`..._pin`: the statement of the theorem, `∀ {d L W} ..., hypotheses → conclusion`),
  as `BAimg` in the T2395 probe, so that the file has definitions, `#check` lines and `example`s only: no theorem, no placeholder proof.
* An `example` applies a pin as a hypothesis at concrete data with every deterministic hypothesis discharged.  Data: the hand-made
  datum `GreenMinorInst` (`d = 3`, `L = 3`, `W = 2`, one cross-offset pair `p, q` in one block, `m = i`; explicit tower), the BA carrier
  (`GreenCore_carrier`, `sz0`, `n = 0`, `t = 1/2`) and `sz0` for the moment bound.  `BAGiiGEX`, `STInitialGT2gL` and `GreenMinor_famGain`
  (other gates' pins) stay hypotheses.
* Where the displayed pseudo-Lean of G.8 omits a hypothesis the statement needs, the pin has it and a comment says so; the list is in
  section (a″) of the report.  `GreenMinor_diff_pin` is the display; `GreenMinor_diff_pin'` adds `κ ≤ 1`; the last section of the file
  proves `¬ GreenMinor_diff_pin`.

Compile: `lake env lean RBM3D/Probe/T2401Pins.lean` in the T2401 worktree.
-/

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.flexible false
noncomputable section
open MeasureTheory Filter Matrix Finset
open RBM RBM.Green RBM.Gauss RBM.Gauss.Sizes

namespace RBM.BA

/-! ## 0. Vocabulary: `T_{β,o}`, `R_{β,o}`, the tower of minors, the protected good event (G.8, T2) -/

section Setting
variable {d L W : ℕ} [NeZero L] [NeZero W]

/-- `T_{β,o} = Y_o ∪ [β]`: the sites of offset `o` and the sites of block `β`. -/
def GreenMinor_T (β : Zd d L) (o : Fin (W ^ d)) : Set (Vtx d L W) := {x | x.2 = o ∨ x.1 = β}

/-- `R_{β,o} = [β] ∖ {(β, o)}`: the protected rows (block `β`, offset `≠ o`). -/
def GreenMinor_R (β : Zd d L) (o : Fin (W ^ d)) : Set (Vtx d L W) := {x | x.1 = β ∧ x.2 ≠ o}

/-- The tower of minors: `Gs S = G^{(S)}` (rows and columns of `S` removed and zero-padded), `Gs ∅ = G`, one step is `(4.9)`. -/
structure GreenMinor_Tower (G : Matrix (Vtx d L W) (Vtx d L W) ℂ)
    (Gs : Finset (Vtx d L W) → Matrix (Vtx d L W) (Vtx d L W) ℂ) : Prop where
  base : Gs ∅ = G
  step : ∀ S κ, κ ∉ S → ∀ x y, Gs (insert κ S) x y = greenMinor (Gs S) κ x y

/-- The BA good event on the protected levels: for `S ⊆ R_{β,o}`, `|S| ≤ m₀`, `x, y ∈ T_{β,o} ∖ S`:
`|G^{(S)}_{xy} - M_{xy}| ≤ 2δ` and `|G^{(S)}_{xx}| ≥ κ/2`. -/
def GreenMinor_good (Gs : Finset (Vtx d L W) → Matrix (Vtx d L W) (Vtx d L W) ℂ)
    (M : Matrix (Vtx d L W) (Vtx d L W) ℂ) (κ δ : ℝ) (m₀ : ℕ) (β : Zd d L) (o : Fin (W ^ d)) : Prop :=
  ∀ S : Finset (Vtx d L W), ↑S ⊆ GreenMinor_R β o → S.card ≤ m₀ → ∀ x y, x ∈ GreenMinor_T β o → y ∈ GreenMinor_T β o →
    x ∉ S → y ∉ S → ‖Gs S x y - M x y‖ ≤ 2 * δ ∧ κ / 2 ≤ ‖Gs S x x‖

/-- `Y^A_u = (s Δ_{uu} - Σ_l D_{ul} Δ_{lu}) / m` (G.8, S3). -/
def GreenMinor_YA (G M D : Matrix (Vtx d L W) (Vtx d L W) ℂ) (s m : ℂ) (u : Vtx d L W) : ℂ :=
  (s * (G u u - M u u) - ∑ l, D u l * (G l u - M l u)) / m

/-- `Y^X_{uy}` (G.8, S3). -/
def GreenMinor_YX (G M D : Matrix (Vtx d L W) (Vtx d L W) ℂ) (s m : ℂ) (u y : Vtx d L W) : ℂ :=
  M u y * (s * (G u u - M u u) - ∑ l, D u l * (G l u - M l u)) / m
    + (∑ l, D u l * (G l y - M l y) - s * (G u y - M u y))
    + ((G u u - M u u) * ∑ l, D u l * (G l y - M l y) - (G u y - M u y) * ∑ l, D u l * (G l u - M l u)) / m

end Setting

/-! ## 1. S1 and the structural lemma (ii) -/

/-- S1: `|G^{(w)}_{xy} - G_{xy}| ≤ (2/κ) |G_{xw}| |G_{wy}|` when `|G_{ww}| ≥ κ/2`. -/
def GreenMinor_removal_pin : Prop :=
  ∀ {d L W : ℕ} [NeZero L] [NeZero W] {G : Matrix (Vtx d L W) (Vtx d L W) ℂ} {κ : ℝ} {w : Vtx d L W},
    0 < κ → κ / 2 ≤ ‖G w w‖ → ∀ x y : Vtx d L W,
      ‖greenMinor G w x y - G x y‖ ≤ (2 / κ) * ‖G x w‖ * ‖G w y‖

/-- (ii): `o(x) ≠ o(y) ⇒ M_{xy} = 0` (Kronecker form, `BAMfine_eq`, `GreenSchur.lean:93`); hence `G_{xy} = Δ_{xy}`. -/
def GreenMinor_cross_pin : Prop :=
  ∀ {d L W : ℕ} [NeZero L] [NeZero W] {M : Matrix (Vtx d L W) (Vtx d L W) ℂ} {Mb : Zd d L → Zd d L → ℂ},
    (∀ u v, M u v = if u.2 = v.2 then Mb u.1 v.1 else 0) → ∀ {x y : Vtx d L W}, x.2 ≠ y.2 → M x y = 0

/-- One-sided removal bound (G.8 comment: `(2/κ) δ ‖G w y‖` under `hxw`). -/
def GreenMinor_removal_crossL_pin : Prop :=
  ∀ {d L W : ℕ} [NeZero L] [NeZero W] {G M : Matrix (Vtx d L W) (Vtx d L W) ℂ} {Mb : Zd d L → Zd d L → ℂ} {κ δ : ℝ} {w : Vtx d L W},
    (∀ u v, M u v = if u.2 = v.2 then Mb u.1 v.1 else 0) → (∀ a b, ‖G a b - M a b‖ ≤ δ) → 0 < κ → κ / 2 ≤ ‖G w w‖ →
    ∀ x y : Vtx d L W, x.2 ≠ w.2 → ‖greenMinor G w x y - G x y‖ ≤ (2 / κ) * δ * ‖G w y‖

/-- One-sided removal bound (G.8 comment: `(2/κ) δ ‖G x w‖` under `hwy`). -/
def GreenMinor_removal_crossR_pin : Prop :=
  ∀ {d L W : ℕ} [NeZero L] [NeZero W] {G M : Matrix (Vtx d L W) (Vtx d L W) ℂ} {Mb : Zd d L → Zd d L → ℂ} {κ δ : ℝ} {w : Vtx d L W},
    (∀ u v, M u v = if u.2 = v.2 then Mb u.1 v.1 else 0) → (∀ a b, ‖G a b - M a b‖ ≤ δ) → 0 < κ → κ / 2 ≤ ‖G w w‖ →
    ∀ x y : Vtx d L W, w.2 ≠ y.2 → ‖greenMinor G w x y - G x y‖ ≤ (2 / κ) * δ * ‖G x w‖

/-- S1, cross-offset form: `(2/κ) δ²` when `o(x) ≠ o(w)` and `o(w) ≠ o(y)`. -/
def GreenMinor_removal_cross_pin : Prop :=
  ∀ {d L W : ℕ} [NeZero L] [NeZero W] {G M : Matrix (Vtx d L W) (Vtx d L W) ℂ} {Mb : Zd d L → Zd d L → ℂ} {κ δ : ℝ} {w : Vtx d L W},
    (∀ u v, M u v = if u.2 = v.2 then Mb u.1 v.1 else 0) → (∀ a b, ‖G a b - M a b‖ ≤ δ) → 0 < κ → κ / 2 ≤ ‖G w w‖ →
    ∀ x y : Vtx d L W, x.2 ≠ w.2 → w.2 ≠ y.2 → ‖greenMinor G w x y - G x y‖ ≤ (2 / κ) * δ ^ 2

/-- (ii) in the `T`/`R` form used by the recursion of S2 (not in the G.8 list; G.2 "Recursion"): for `w ∈ R_{β,o}` and
`x ∈ T_{β,o}`, `x ≠ w`, the offsets differ (`x` of offset `o`: `o(w) ≠ o`; `x` in block `β`: same block, different site). -/
def GreenMinor_offset_ne_pin : Prop :=
  ∀ {d L W : ℕ} [NeZero L] [NeZero W] {β : Zd d L} {o : Fin (W ^ d)} {w x : Vtx d L W},
    w ∈ GreenMinor_R β o → x ∈ GreenMinor_T β o → x ≠ w → x.2 ≠ w.2

/-! ## 2. S2: the protected good event from `‖Δ‖_max ≤ δ` -/

/-- S2 (`GreenMinor_good_of_event`). -/
def GreenMinor_good_of_event_pin : Prop :=
  ∀ {d L W : ℕ} [NeZero L] [NeZero W] {G M : Matrix (Vtx d L W) (Vtx d L W) ℂ} {Mb : Zd d L → Zd d L → ℂ} {m : ℂ}
    {Gs : Finset (Vtx d L W) → Matrix (Vtx d L W) (Vtx d L W) ℂ} {κ δ : ℝ} {m₀ : ℕ},
    (∀ u v, M u v = if u.2 = v.2 then Mb u.1 v.1 else 0) → (∀ a, Mb a a = m) → 0 < κ → κ ≤ ‖m‖ → 0 ≤ δ → 4 * δ ≤ κ →
    8 * (m₀ : ℝ) * δ ≤ κ → GreenMinor_Tower G Gs → (∀ x y, ‖G x y - M x y‖ ≤ δ) →
    ∀ (β : Zd d L) (o : Fin (W ^ d)), GreenMinor_good Gs M κ δ m₀ β o

/-! ## 3. S3: the polynomial families, entry forms, splits, base bounds -/

-- G.8 omits `m ≠ 0` in the four identity pins (at `m = 0` the right side of `A_u = Y^A m / G_{uu}` is `0`; BA: `κ ≤ ‖m‖`).

/-- S3 (`GreenMinor_Arow_eq`): `A_u = Y^A_u m / G_{uu}`. -/
def GreenMinor_Arow_eq_pin : Prop :=
  ∀ {d L W : ℕ} [NeZero L] [NeZero W] {G X D M : Matrix (Vtx d L W) (Vtx d L W) ℂ} {Mb : Zd d L → Zd d L → ℂ}
    {t g₀ : ℝ} {m s z : ℂ},
    G * (D + X - z • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) = 1 →
    (D + X - z • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) * G = 1 →
    M * (D - s • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) = 1 → z = s - (t : ℂ) * m →
    (∀ u v, M u v = if u.2 = v.2 then Mb u.1 v.1 else 0) → (∀ a, Mb a a = m) →
    (∀ u l, D u l = if u.2 = l.2 ∧ Adj d L u.1 l.1 then (g₀ : ℂ) else 0) → m ≠ 0 →
    ∀ {u : Vtx d L W}, G u u ≠ 0 →
      GreenCore_Arow G X D t m u = GreenMinor_YA G M D s m u * m / G u u

/-- S3 (`GreenMinor_Xrow_eq`): `𝔛_{uy} = -Y^X_{uy} m / G_{uu}`, `y ≠ u`. -/
def GreenMinor_Xrow_eq_pin : Prop :=
  ∀ {d L W : ℕ} [NeZero L] [NeZero W] {G X D M : Matrix (Vtx d L W) (Vtx d L W) ℂ} {Mb : Zd d L → Zd d L → ℂ}
    {t g₀ : ℝ} {m s z : ℂ},
    G * (D + X - z • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) = 1 →
    (D + X - z • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) * G = 1 →
    M * (D - s • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) = 1 → z = s - (t : ℂ) * m →
    (∀ u v, M u v = if u.2 = v.2 then Mb u.1 v.1 else 0) → (∀ a, Mb a a = m) →
    (∀ u l, D u l = if u.2 = l.2 ∧ Adj d L u.1 l.1 then (g₀ : ℂ) else 0) → m ≠ 0 →
    ∀ {u y : Vtx d L W}, G u u ≠ 0 → y ≠ u →
      GreenCore_Xrow G X u y = -(GreenMinor_YX G M D s m u y * m / G u u)

/-- S3 (`GreenMinor_split_A`): `A_u = Y^A_u - A_u (G_{uu} - m) / m`. -/
def GreenMinor_split_A_pin : Prop :=
  ∀ {d L W : ℕ} [NeZero L] [NeZero W] {G X D M : Matrix (Vtx d L W) (Vtx d L W) ℂ} {Mb : Zd d L → Zd d L → ℂ}
    {t g₀ : ℝ} {m s z : ℂ},
    G * (D + X - z • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) = 1 →
    (D + X - z • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) * G = 1 →
    M * (D - s • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) = 1 → z = s - (t : ℂ) * m →
    (∀ u v, M u v = if u.2 = v.2 then Mb u.1 v.1 else 0) → (∀ a, Mb a a = m) →
    (∀ u l, D u l = if u.2 = l.2 ∧ Adj d L u.1 l.1 then (g₀ : ℂ) else 0) → m ≠ 0 →
    ∀ {u : Vtx d L W}, G u u ≠ 0 →
      GreenCore_Arow G X D t m u = GreenMinor_YA G M D s m u - GreenCore_Arow G X D t m u * (G u u - m) / m

/-- S3 (`GreenMinor_split_X`): `𝔛_{uy} = -Y^X_{uy} - 𝔛_{uy} (G_{uu} - m) / m`, `y ≠ u`. -/
def GreenMinor_split_X_pin : Prop :=
  ∀ {d L W : ℕ} [NeZero L] [NeZero W] {G X D M : Matrix (Vtx d L W) (Vtx d L W) ℂ} {Mb : Zd d L → Zd d L → ℂ}
    {t g₀ : ℝ} {m s z : ℂ},
    G * (D + X - z • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) = 1 →
    (D + X - z • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) * G = 1 →
    M * (D - s • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) = 1 → z = s - (t : ℂ) * m →
    (∀ u v, M u v = if u.2 = v.2 then Mb u.1 v.1 else 0) → (∀ a, Mb a a = m) →
    (∀ u l, D u l = if u.2 = l.2 ∧ Adj d L u.1 l.1 then (g₀ : ℂ) else 0) → m ≠ 0 →
    ∀ {u y : Vtx d L W}, G u u ≠ 0 → y ≠ u →
      GreenCore_Xrow G X u y = -GreenMinor_YX G M D s m u y - GreenCore_Xrow G X u y * (G u u - m) / m

-- G.8 shows `(hL) (hΔ) (hκ) (hMuy)` for the base bounds; `hD`, `0 ≤ g₀` (the row sum `Σ_l ‖D_{ul}‖ = 2 d g₀`, `GreenCore_Drow`) and `0 < κ` are
-- needed and made explicit here.

/-- S3 (`GreenMinor_YA_le`): `‖Y^A_u‖ ≤ (‖s‖ + 2 d g₀) δ' / κ`. -/
def GreenMinor_YA_le_pin : Prop :=
  ∀ {d L W : ℕ} [NeZero L] [NeZero W] {G M D : Matrix (Vtx d L W) (Vtx d L W) ℂ} {s m : ℂ} {κ δ' g₀ : ℝ},
    3 ≤ L → 0 ≤ g₀ → (∀ u l, D u l = if u.2 = l.2 ∧ Adj d L u.1 l.1 then (g₀ : ℂ) else 0) →
    (∀ a b, ‖G a b - M a b‖ ≤ δ') → 0 < κ → κ ≤ ‖m‖ →
    ∀ u : Vtx d L W, ‖GreenMinor_YA G M D s m u‖ ≤ (‖s‖ + 2 * d * g₀) / κ * δ'

/-- S3 (`GreenMinor_YX_le`): `‖Y^X_{uy}‖ ≤ ((‖s‖ + 2 d g₀)(1/κ + 1) + 4 d g₀ δ'/κ) δ'`. -/
def GreenMinor_YX_le_pin : Prop :=
  ∀ {d L W : ℕ} [NeZero L] [NeZero W] {G M D : Matrix (Vtx d L W) (Vtx d L W) ℂ} {s m : ℂ} {κ δ' g₀ : ℝ},
    3 ≤ L → 0 ≤ g₀ → (∀ u l, D u l = if u.2 = l.2 ∧ Adj d L u.1 l.1 then (g₀ : ℂ) else 0) →
    (∀ a b, ‖G a b - M a b‖ ≤ δ') → 0 < κ → κ ≤ ‖m‖ →
    ∀ u y : Vtx d L W, ‖M u y‖ ≤ 1 →
      ‖GreenMinor_YX G M D s m u y‖ ≤ ((‖s‖ + 2 * d * g₀) * (1 / κ + 1) + 4 * d * g₀ * δ' / κ) * δ'

/-! ## 4. S4: the graded bound on protected rows (Route A constants) -/

/-- `a_0 = 2/κ`, `a_{r+1} = 16^r a_r^5` (T2401c: `a_0 = 2/κ` replaces the band's `2` in `atomC`). -/
def GreenMinor_a (κ : ℝ) : ℕ → ℝ
  | 0 => 2 / κ
  | r + 1 => 16 ^ r * GreenMinor_a κ r ^ 5

/-- `c_Y(r) = (‖s‖ + 2 d g₀)(1/κ + 1) a_r + (4 d g₀/κ) 2^r a_r²`. -/
def GreenMinor_cY (d : ℕ) (κ g₀ s : ℝ) (r : ℕ) : ℝ :=
  (s + 2 * d * g₀) * (1 / κ + 1) * GreenMinor_a κ r + (4 * d * g₀ / κ) * 2 ^ r * GreenMinor_a κ r ^ 2

-- G.8 shows `(hT) (hgood) (hu) (hy) (l) (hl) (hR) (hlen) (h2δ)`; `hL`, `0 ≤ g₀`, `hD`, `hM`, `0 < κ`, `κ ≤ ‖m‖`, `‖M u y‖ ≤ 1` (the data of the base
-- bounds `GreenMinor_YA_le`, `GreenMinor_YX_le` and the weight `‖s‖`, `g₀` of `GreenMinor_cY`) are made explicit.

/-- S4 (`GreenMinor_diff`) as displayed in G.8: `‖Δ_{κ_1} ⋯ Δ_{κ_m} Y^X_{uy}‖, ‖Δ_{κ_1} ⋯ Δ_{κ_m} Y^A_u‖ ≤ c_Y(m) (2δ)^{m+1}`
on the protected rows.  False without a bound on `κ` (the last section proves `¬ GreenMinor_diff_pin`). -/
def GreenMinor_diff_pin : Prop :=
  ∀ {d L W : ℕ} [NeZero L] [NeZero W] {G M D : Matrix (Vtx d L W) (Vtx d L W) ℂ} {Mb : Zd d L → Zd d L → ℂ}
    {Gs : Finset (Vtx d L W) → Matrix (Vtx d L W) (Vtx d L W) ℂ} {s m : ℂ} {κ δ g₀ : ℝ} {m₀ : ℕ}
    {β : Zd d L} {o : Fin (W ^ d)} {u y : Vtx d L W},
    3 ≤ L → 0 ≤ g₀ → (∀ u l, D u l = if u.2 = l.2 ∧ Adj d L u.1 l.1 then (g₀ : ℂ) else 0) →
    (∀ u v, M u v = if u.2 = v.2 then Mb u.1 v.1 else 0) → 0 < κ → κ ≤ ‖m‖ → ‖M u y‖ ≤ 1 →
    GreenMinor_Tower G Gs → GreenMinor_good Gs M κ δ m₀ β o → u = (β, o) → (y.2 = o ∧ y.1 ≠ β) →
    ∀ l : List (Vtx d L W), l.Nodup → (∀ k ∈ l, k ∈ GreenMinor_R β o) → l.length ≤ m₀ → 2 * δ ≤ 1 →
      ‖iterDeltaFam l (fun S => GreenMinor_YX (Gs S) M D s m u y) ∅‖ ≤
          GreenMinor_cY d κ g₀ ‖s‖ l.length * (2 * δ) ^ (l.length + 1) ∧
      ‖iterDeltaFam l (fun S => GreenMinor_YA (Gs S) M D s m u) ∅‖ ≤
          GreenMinor_cY d κ g₀ ‖s‖ l.length * (2 * δ) ^ (l.length + 1)

/-- PROPOSED REPAIR of S4 (needs the dispatcher's decision): `GreenMinor_diff_pin` with the hypothesis `κ ≤ 1`
(BA: `κ ≤ ‖m‖ ≤ 1`, `BAm_norm_le_one`; the constant `a_0 = 2/κ` must be `≥ 1`). -/
def GreenMinor_diff_pin' : Prop :=
  ∀ {d L W : ℕ} [NeZero L] [NeZero W] {G M D : Matrix (Vtx d L W) (Vtx d L W) ℂ} {Mb : Zd d L → Zd d L → ℂ}
    {Gs : Finset (Vtx d L W) → Matrix (Vtx d L W) (Vtx d L W) ℂ} {s m : ℂ} {κ δ g₀ : ℝ} {m₀ : ℕ}
    {β : Zd d L} {o : Fin (W ^ d)} {u y : Vtx d L W},
    3 ≤ L → 0 ≤ g₀ → (∀ u l, D u l = if u.2 = l.2 ∧ Adj d L u.1 l.1 then (g₀ : ℂ) else 0) →
    (∀ u v, M u v = if u.2 = v.2 then Mb u.1 v.1 else 0) → 0 < κ → κ ≤ 1 → κ ≤ ‖m‖ → ‖M u y‖ ≤ 1 →
    GreenMinor_Tower G Gs → GreenMinor_good Gs M κ δ m₀ β o → u = (β, o) → (y.2 = o ∧ y.1 ≠ β) →
    ∀ l : List (Vtx d L W), l.Nodup → (∀ k ∈ l, k ∈ GreenMinor_R β o) → l.length ≤ m₀ → 2 * δ ≤ 1 →
      ‖iterDeltaFam l (fun S => GreenMinor_YX (Gs S) M D s m u y) ∅‖ ≤
          GreenMinor_cY d κ g₀ ‖s‖ l.length * (2 * δ) ^ (l.length + 1) ∧
      ‖iterDeltaFam l (fun S => GreenMinor_YA (Gs S) M D s m u) ∅‖ ≤
          GreenMinor_cY d κ g₀ ‖s‖ l.length * (2 * δ) ^ (l.length + 1)

/-! ## 5. S5: the gain interface for a family and the moment bound -/

/-- S5 (`GreenMinor_famGain`): the gain interface `famGain(B, ρ, M, K)` of the family `Y`, for words whose rows are distinct,
`≠ k_i` and in `A` (the twin of `FlucGainUpTo'`, `Green/FlucIterGain.lean:727`, with `qRow (k i) (Y (k i))` for `flucDiag`). -/
def GreenMinor_famGain {d : ℕ} (sz : Sizes d) (n : ℕ) (A : Finset (Idx d (sz.L n) (sz.W n)))
    (Y : Idx d (sz.L n) (sz.W n) → sz.SeqΩ → ℂ) (B ρ : ℝ) (M K : ℕ) : Prop :=
  0 ≤ B ∧ 0 ≤ ρ ∧ ∀ (ι : Type) [Fintype ι] (k : ι → Idx d (sz.L n) (sz.W n))
    (L : ι → List (Bool × Idx d (sz.L n) (sz.W n))),
    (∀ i, k i ∈ A) → (∀ i, ((L i).map Prod.snd).Nodup) → (∀ i, ∀ x ∈ L i, x.2 ≠ k i ∧ x.2 ∈ A) →
    (∀ i, (L i).length ≤ M) → Fintype.card ι ≤ K →
    ∫ ω, ∏ i, ‖applyOps sz n (L i) (qRow sz n (k i) (Y (k i))) ω‖ ∂(Sizes.seqP sz) ≤
      B ^ Fintype.card ι * ρ ^ ∑ i, numQ (L i)

/-- S5 (`GreenMinor_famAvg_moment`): `E |Σ_{k∈A} T_k Q_k Y_k|^{2p} ≤ (2p+1)(2p)^{2p}(2^{2p-1} ρ B)^{2p}`
(the statement of `integral_norm_flucAvg_pow_le_iter_budget`, `Green/FlucIterGain.lean:823`, for the family `Y`). -/
def GreenMinor_famAvg_moment_pin : Prop :=
  ∀ {d : ℕ} {sz : Sizes d} {n : ℕ} {A : Finset (Idx d (sz.L n) (sz.W n))} {T : Idx d (sz.L n) (sz.W n) → ℝ}
    {Y : Idx d (sz.L n) (sz.W n) → sz.SeqΩ → ℂ} {B ρ c : ℝ} {M K p : ℕ},
    (∀ k, BddMeas sz (Y k)) → (∀ k, FinDep sz (Y k)) → GreenMinor_famGain sz n A Y B ρ M K →
    2 * p ≤ M → 2 * p ≤ K → ρ ≤ 1 → c ≤ ρ ^ 2 → BoundedWeight T c A → 2 * p ≤ A.card →
      ∫ ω, ‖∑ k ∈ A, (T k : ℂ) * qRow sz n k (Y k) ω‖ ^ (2 * p) ∂(Sizes.seqP sz) ≤
        ((2 * p : ℝ) + 1) * (2 * p : ℝ) ^ (2 * p) * ((2 : ℝ) ^ (2 * p - 1) * ρ * B) ^ (2 * p)

/-! ## 6. S6: the exact averaging identity for `⟨M𝒦⟩_a` -/

/-- `avg_o f = W^{-d} Σ_o f(o)`. -/
def GreenMinor_avg {d W : ℕ} (f : Fin (W ^ d) → ℂ) : ℂ := (((W : ℝ) ^ d)⁻¹ : ℝ) * ∑ o, f o

/-- `⟨M𝒦⟩_a = W^{-d} Σ_o Σ_{b'} M^B_{ab'} 𝒦_{(b',o),(a,o)}` (`GreenCore_K`). -/
def GreenMinor_avgK {d L W : ℕ} [NeZero L] [NeZero W] (G M X D : Matrix (Vtx d L W) (Vtx d L W) ℂ)
    (Mb : Zd d L → Zd d L → ℂ) (t : ℝ) (m : ℂ) (a : Zd d L) : ℂ :=
  (((W : ℝ) ^ d)⁻¹ : ℝ) * ∑ o : Fin (W ^ d), ∑ b' : Zd d L, Mb a b' * GreenCore_K G M X D t m (b', o) (a, o)

/-- S6, first half (hypotheses of `GreenCore_E3`): `v̄_a - t Σ_b M^B_{ab} M^B_{ba} v̄_b = ⟨M𝒦⟩_a`. -/
def GreenMinor_avgK_pin : Prop :=
  ∀ {d L W : ℕ} [NeZero L] [NeZero W] {G X D M : Matrix (Vtx d L W) (Vtx d L W) ℂ} {Mb : Zd d L → Zd d L → ℂ}
    {t : ℝ} {m s z : ℂ},
    G * (D + X - z • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) = 1 →
    (D + X - z • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) * G = 1 →
    M * (D - s • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) = 1 → z = s - (t : ℂ) * m →
    (∀ u v, M u v = if u.2 = v.2 then Mb u.1 v.1 else 0) → (∀ u, G u u ≠ 0) →
    ∀ a : Zd d L, GreenCore_vbar G M a - (t : ℂ) * ∑ b, Mb a b * Mb b a * GreenCore_vbar G M b =
      GreenMinor_avgK G M X D Mb t m a

/-- S6, second half (only `hM`; the sum is over all `b'`, `𝔛_{uu} = 0` is not used):
`⟨M𝒦⟩_a = Σ_{b'} M^B_{ab'} [t v̄_{b'} avg_o Δ - M^B_{b'a} avg_o 𝒜' - avg_o (𝒜' Δ) - avg_o 𝔛]`, `𝒜'_u = A_u + t v̄_{[u]}`. -/
def GreenMinor_avg_split_pin : Prop :=
  ∀ {d L W : ℕ} [NeZero L] [NeZero W] {G X D M : Matrix (Vtx d L W) (Vtx d L W) ℂ} {Mb : Zd d L → Zd d L → ℂ}
    {t : ℝ} {m : ℂ}, (∀ u v, M u v = if u.2 = v.2 then Mb u.1 v.1 else 0) → ∀ a : Zd d L,
    GreenMinor_avgK G M X D Mb t m a =
      ∑ b', Mb a b' * ((t : ℂ) * GreenCore_vbar G M b' * GreenMinor_avg (fun o : Fin (W ^ d) => G (b', o) (a, o) - M (b', o) (a, o))
        - Mb b' a * GreenMinor_avg (fun o : Fin (W ^ d) => GreenCore_Arow G X D t m (b', o) + (t : ℂ) * GreenCore_vbar G M b')
        - GreenMinor_avg (fun o : Fin (W ^ d) => (GreenCore_Arow G X D t m (b', o) + (t : ℂ) * GreenCore_vbar G M b') *
            (G (b', o) (a, o) - M (b', o) (a, o)))
        - GreenMinor_avg (fun o : Fin (W ^ d) => GreenCore_Xrow G X (b', o) (a, o)))

/-! ## 7. S7: the owed pin `BAFAav` (registry; owner BA-G5b, consumer BA-G6b).  `BAFamGain` has no Lean text in G.8 and is not written. -/

/-- The averaged law of the offset average of `𝒦`: `|W^{-d} Σ_o Σ_{b'} M^B_{ab'} 𝒦_{(b',o),(a,o)}| ≺ Ψ²`, uniformly in `a`, from `BAGiiGEX` and
`(initialGT2)` (`STInitialGT2gL`); no `∃ c` before the flow. -/
def BAFAav (d : ℕ) : Prop :=
  ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z →
    ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ BAflowT0 sz z n) → ∀ ε₀ : ℝ, 0 < ε₀ → BAGiiGEX sz z t ε₀ →
    ∀ Ψ : ℕ → ℝ, (∀ᶠ n in atTop, ((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2) ≤ Ψ n) →
      (∀ᶠ n in atTop, Ψ n ≤ ((sz.W n : ℕ) : ℝ) ^ (-ε₀)) →
      STInitialGT2gL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) t ε₀ Ψ →
        PrecL sz (Sizes.seqP (sz.withLam 0)) (U := fun n => Zd d (sz.L n))
          (fun n a ω => ‖(((sz.W n : ℝ) ^ d)⁻¹ : ℝ) * ∑ o, ∑ b',
            BAMB d (sz.L n) (BAflowLam0 sz z n) (BAflowEs sz z n : ℂ) (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) a b' *
              GreenCore_K (GreenCore_Gc sz z n (t n) ω) (GreenCore_Mc sz z n) (GreenCore_Xc sz n (t n) ω)
                (GreenCore_Dc sz z n) (t n) (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) (b', o) (a, o)‖)
          (fun n _ _ => Ψ n ^ 2)

/-! ## 8. `#check` lines -/

#check GreenMinor_T
#check GreenMinor_R
#check GreenMinor_Tower
#check GreenMinor_good
#check GreenMinor_YA
#check GreenMinor_YX
#check GreenMinor_a
#check GreenMinor_cY
#check GreenMinor_famGain
#check GreenMinor_avg
#check GreenMinor_avgK
#check GreenMinor_removal_pin
#check GreenMinor_cross_pin
#check GreenMinor_removal_crossL_pin
#check GreenMinor_removal_crossR_pin
#check GreenMinor_removal_cross_pin
#check GreenMinor_offset_ne_pin
#check GreenMinor_good_of_event_pin
#check GreenMinor_Arow_eq_pin
#check GreenMinor_Xrow_eq_pin
#check GreenMinor_split_A_pin
#check GreenMinor_split_X_pin
#check GreenMinor_YA_le_pin
#check GreenMinor_YX_le_pin
#check GreenMinor_diff_pin
#check GreenMinor_diff_pin'
#check GreenMinor_famAvg_moment_pin
#check GreenMinor_avgK_pin
#check GreenMinor_avg_split_pin
#check BAFAav

/-! ## 9. Nonemptiness: the hand-made datum (`d = 3`, `L = 3`, `W = 2`; S1, S2, S3 bounds, S4) -/

namespace GreenMinorInst

abbrev HV : Type := Vtx 3 3 2
/-- the site `p = (block 0, offset 0)` -/
def hp : HV := (0, 0)
/-- the site `q = (block 0, offset 1)`, in the protected rows `R_{0,0}` -/
def hq : HV := (0, 1)
/-- `m = i` -/
def hm : ℂ := Complex.I
/-- the cross-offset entry `Δ_{pq} = Δ_{qp} = ε = 1/100` -/
def hε : ℂ := ((1 / 100 : ℝ) : ℂ)
/-- zero inter-block coupling: `M^{(B)} = m I` -/
def hMb : Zd 3 3 → Zd 3 3 → ℂ := fun a b => if a = b then hm else 0
def hM : Matrix HV HV ℂ := Matrix.of fun u v => if u.2 = v.2 then hMb u.1 v.1 else 0
def hΔ : Matrix HV HV ℂ := Matrix.of fun x y => if (x = hp ∧ y = hq) ∨ (x = hq ∧ y = hp) then hε else 0
/-- `G = M + Δ`: block diagonal, one `2 × 2` block on `{p, q}`, `‖Δ‖_max = ε ≠ 0` -/
def hG : Matrix HV HV ℂ := hM + hΔ
/-- the hopping `D = g₀ Ψ`, `g₀ = 1/10` -/
def hD : Matrix HV HV ℂ := Matrix.of fun u l => if u.2 = l.2 ∧ Adj 3 3 u.1 l.1 then ((1 / 10 : ℝ) : ℂ) else 0
/-- `y = (e_0, offset 0)`: a block `≠ 0`, the offset of `p` -/
def hy : HV := (Pi.single 0 1, 0)

end GreenMinorInst

section HandMade
open GreenMinorInst

-- S1: the removal bound at `w = q`, `x = y = p` (`G^{(q)}_{pp} - G_{pp} = -ε²/m`)
example (h : GreenMinor_removal_pin) :
    ‖greenMinor hG hq hp hp - hG hp hp‖ ≤ (2 / (1 / 2 : ℝ)) * ‖hG hp hq‖ * ‖hG hq hp‖ := by
  have hqq : hG hq hq = hm := by
    have : hq ≠ hp := fun h' => (by decide : hp ≠ hq) h'.symm
    simp [hG, hM, hΔ, hMb, this]
  refine h (by norm_num) ?_ _ _
  rw [hqq]
  simp [hm]
  norm_num

-- (ii): `M_{pq} = 0` (offsets `0 ≠ 1`)
example (h : GreenMinor_cross_pin) : hM hp hq = 0 :=
  h (M := hM) (Mb := hMb) (fun _ _ => rfl) (x := hp) (y := hq) (by decide)

-- S1: the one-sided and the cross-offset forms at `w = q`, `x = y = p`, `δ = 1/100 = ‖Δ‖_max`
example (hL : GreenMinor_removal_crossL_pin) (hR : GreenMinor_removal_crossR_pin) (hLR : GreenMinor_removal_cross_pin) :
    ‖greenMinor hG hq hp hp - hG hp hp‖ ≤ (2 / (1 / 2 : ℝ)) * (1 / 100) * ‖hG hq hp‖ ∧
    ‖greenMinor hG hq hp hp - hG hp hp‖ ≤ (2 / (1 / 2 : ℝ)) * (1 / 100) * ‖hG hp hq‖ ∧
    ‖greenMinor hG hq hp hp - hG hp hp‖ ≤ (2 / (1 / 2 : ℝ)) * (1 / 100) ^ 2 := by
  have hqq : hG hq hq = hm := by
    have : hq ≠ hp := fun h' => (by decide : hp ≠ hq) h'.symm
    simp [hG, hM, hΔ, hMb, this]
  have hΔb : ∀ a b, ‖hG a b - hM a b‖ ≤ 1 / 100 := by
    intro a b
    simp only [hG, Matrix.add_apply, add_sub_cancel_left, hΔ, Matrix.of_apply]
    split_ifs
    · simp [hε]
    · simp
  have hw : (1 / 2 : ℝ) / 2 ≤ ‖hG hq hq‖ := by rw [hqq]; simp [hm]; norm_num
  have h1 : hp.2 ≠ hq.2 := by decide
  have h2 : hq.2 ≠ hp.2 := by decide
  exact ⟨hL (Mb := hMb) (fun _ _ => rfl) hΔb (by norm_num) hw _ _ h1,
    hR (Mb := hMb) (fun _ _ => rfl) hΔb (by norm_num) hw _ _ h2,
    hLR (Mb := hMb) (fun _ _ => rfl) hΔb (by norm_num) hw _ _ h1 h2⟩

-- (ii) in the `T`/`R` form: `q ∈ R_{0,0}`; `p` (offset 0) and `(0, 2)` (block 0) in `T_{0,0}`
example (h : GreenMinor_offset_ne_pin) :
    (hp.2 ≠ hq.2) ∧ (((0 : Zd 3 3), (2 : Fin (2 ^ 3))) : HV).2 ≠ hq.2 := by
  have hR : hq ∈ GreenMinor_R (0 : Zd 3 3) (0 : Fin (2 ^ 3)) := ⟨rfl, by decide⟩
  exact ⟨h hR (Or.inl rfl) (by decide), h hR (Or.inr rfl) (by decide)⟩

-- S2 and S4 (the repaired pin): the tower of `G` (explicit: removing `q` turns `G_{pp}` into `m - ε²/m`), the event at `δ = 1/100`,
-- `κ = 1/2`, `m₀ = 3`, `β = 0`, `o = 0` (so `u = p`), `y = (e_0, 0)`, the removed row `q ∈ R_{0,0}`; `g₀ = 1/10`, `s = m`
example (h2 : GreenMinor_good_of_event_pin) (h4 : GreenMinor_diff_pin') :
    ∃ Gs : Finset HV → Matrix HV HV ℂ, GreenMinor_Tower hG Gs ∧ GreenMinor_good Gs hM (1 / 2) (1 / 100) 3 0 0 ∧
      ‖iterDeltaFam [hq] (fun S => GreenMinor_YX (Gs S) hM hD hm hm hp hy) ∅‖ ≤
          GreenMinor_cY 3 (1 / 2) (1 / 10) ‖hm‖ [hq].length * (2 * (1 / 100)) ^ ([hq].length + 1) ∧
      ‖iterDeltaFam [hq] (fun S => GreenMinor_YA (Gs S) hM hD hm hm hp) ∅‖ ≤
          GreenMinor_cY 3 (1 / 2) (1 / 10) ‖hm‖ [hq].length * (2 * (1 / 100)) ^ ([hq].length + 1) := by
  have hpq : hp ≠ hq := by decide
  have hqp : hq ≠ hp := hpq.symm
  have hm0 : hm ≠ 0 := Complex.I_ne_zero
  have hc : hm - hε ^ 2 / hm ≠ 0 := by
    intro h0
    have := congrArg Complex.im h0
    simp [hm, hε] at this
    norm_num at this
  have hMe : ∀ x y, hM x y = if x = y then hm else 0 := by
    intro x y
    simp only [hM, hMb, Matrix.of_apply, Prod.ext_iff]
    split_ifs <;> simp_all
  set c : ℂ := hm - hε ^ 2 / hm with hc_def
  let g : Finset HV → HV → HV → ℂ := fun S x y =>
    if x ∈ S ∨ y ∈ S then 0
    else if x = y then (if (x = hp ∧ hq ∈ S) ∨ (x = hq ∧ hp ∈ S) then c else hm)
    else if (x = hp ∧ y = hq) ∨ (x = hq ∧ y = hp) then hε else 0
  have hT : GreenMinor_Tower hG (fun S => Matrix.of (g S)) := by
    refine ⟨?_, ?_⟩
    · ext x y
      simp only [g, hG, hΔ, Matrix.add_apply, hMe, Matrix.of_apply, Finset.notMem_empty, or_self, ite_false, and_false, false_and, or_false]
      by_cases hxy : x = y
      · subst hxy
        have : ¬ ((x = hp ∧ x = hq) ∨ (x = hq ∧ x = hp)) := by
          rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
          · exact hpq (h1.symm.trans h2)
          · exact hqp (h1.symm.trans h2)
        simp [this]
      · simp [hxy]
    · intro S κ hκ x y
      show g (insert κ S) x y = g S x y - g S x κ * g S κ y / g S κ κ
      have hgκκ : g S κ κ ≠ 0 := by
        simp only [g, hκ, or_self, ite_false, ite_true]
        split_ifs <;> assumption
      by_cases hxS : x ∈ S
      · have e1 : g (insert κ S) x y = 0 := by simp [g, hxS]
        have e2 : g S x y = 0 := by simp [g, hxS]
        have e3 : g S x κ = 0 := by simp [g, hxS]
        rw [e1, e2, e3]; simp
      by_cases hyS : y ∈ S
      · have e1 : g (insert κ S) x y = 0 := by simp [g, hyS]
        have e2 : g S x y = 0 := by simp [g, hyS]
        have e3 : g S κ y = 0 := by simp [g, hyS]
        rw [e1, e2, e3]; simp
      by_cases hxκ : x = κ
      · subst hxκ
        have e1 : g (insert x S) x y = 0 := by simp [g]
        rw [e1, mul_div_cancel_left₀ _ hgκκ, sub_self]
      by_cases hyκ : y = κ
      · subst hyκ
        have e1 : g (insert y S) x y = 0 := by simp [g]
        rw [e1, mul_div_assoc, div_self hgκκ, mul_one, sub_self]
      have hκx : κ ≠ x := fun h => hxκ h.symm
      have hκy : κ ≠ y := fun h => hyκ h.symm
      simp only [g, hxS, hyS, hκ, hxκ, hyκ, hκx, hκy, Finset.mem_insert, or_self, ite_false, or_false, false_or]
      by_cases hκp : κ = hp
      · subst hκp
        by_cases hxq : x = hq
        · subst hxq
          by_cases hyq : y = hq
          · subst hyq
            simp [hpq, hqp, hxS, hκ]
            rw [hc_def]; ring
          · simp [hpq, hqp, hxS, hyq, Ne.symm hyq]
        · simp [hpq, hqp, hxq, Ne.symm hxq]
      by_cases hκq : κ = hq
      · subst hκq
        by_cases hxp : x = hp
        · subst hxp
          by_cases hyp : y = hp
          · subst hyp
            simp [hpq, hqp, hxS, hκ]
            rw [hc_def]; ring
          · simp [hpq, hqp, hxS, hyp, Ne.symm hyp]
        · simp [hpq, hqp, hxp, Ne.symm hxp]
      simp [hpq, hqp, hκp, hκq, Ne.symm hκp, Ne.symm hκq]
  refine ⟨_, hT, ?_⟩
  have hΔb : ∀ a b, ‖hG a b - hM a b‖ ≤ 1 / 100 := by
    intro a b
    simp only [hG, Matrix.add_apply, add_sub_cancel_left, hΔ, Matrix.of_apply]
    split_ifs
    · simp [hε]
    · simp
  have hgood : GreenMinor_good (fun S => Matrix.of (g S)) hM (1 / 2) (1 / 100) 3 0 0 :=
    h2 (Mb := hMb) (m := hm) (fun _ _ => rfl) (fun a => by simp [hMb]) (by norm_num) (by simp [hm]; norm_num) (by norm_num)
      (by norm_num) (by norm_num) hT hΔb 0 0
  refine ⟨hgood, ?_⟩
  have hy1 : hy.1 ≠ 0 := by decide
  have hMuy : ‖hM hp hy‖ ≤ 1 := by
    rw [hMe]
    have : hp ≠ hy := fun h' => hy1 (by rw [← h']; rfl)
    simp [this]
  exact h4 (G := hG) (M := hM) (D := hD) (Mb := hMb) (Gs := fun S => Matrix.of (g S)) (s := hm) (m := hm) (κ := 1 / 2)
    (δ := 1 / 100) (g₀ := 1 / 10) (m₀ := 3) (β := 0) (o := 0) (u := hp) (y := hy) (by norm_num) (by norm_num)
    (fun _ _ => rfl) (fun _ _ => rfl) (by norm_num) (by norm_num) (by simp [hm]; norm_num) hMuy hT hgood rfl ⟨rfl, hy1⟩
    [hq] (by simp) (by simp [GreenMinor_R, hq]) (by simp) (by norm_num)

-- S3: the base bounds at the datum (`d = 3`, `g₀ = 1/10`, `κ = 1/2`, `δ' = 1/100`)
example (hA : GreenMinor_YA_le_pin) (hX : GreenMinor_YX_le_pin) :
    ‖GreenMinor_YA hG hM hD hm hm hp‖ ≤ (‖hm‖ + 2 * ((3 : ℕ) : ℝ) * (1 / 10)) / (1 / 2) * (1 / 100) ∧
    ‖GreenMinor_YX hG hM hD hm hm hp hy‖ ≤
      ((‖hm‖ + 2 * ((3 : ℕ) : ℝ) * (1 / 10)) * (1 / (1 / 2) + 1) + 4 * ((3 : ℕ) : ℝ) * (1 / 10) * (1 / 100) / (1 / 2)) * (1 / 100) := by
  have hMe : ∀ x y, hM x y = if x = y then hm else 0 := by
    intro x y
    simp only [hM, hMb, Matrix.of_apply, Prod.ext_iff]
    split_ifs <;> simp_all
  have hΔb : ∀ a b, ‖hG a b - hM a b‖ ≤ 1 / 100 := by
    intro a b
    simp only [hG, Matrix.add_apply, add_sub_cancel_left, hΔ, Matrix.of_apply]
    split_ifs
    · simp [hε]
    · simp
  have hy1 : hy.1 ≠ 0 := by decide
  have hMuy : ‖hM hp hy‖ ≤ 1 := by
    rw [hMe]
    have : hp ≠ hy := fun h' => hy1 (by rw [← h']; rfl)
    simp [this]
  have hmκ : (1 / 2 : ℝ) ≤ ‖hm‖ := by simp [hm]; norm_num
  exact ⟨hA (G := hG) (M := hM) (D := hD) (g₀ := 1 / 10) (κ := 1 / 2) (δ' := 1 / 100) (by norm_num) (by norm_num)
      (fun _ _ => rfl) hΔb (by norm_num) hmκ hp,
    hX (G := hG) (M := hM) (D := hD) (g₀ := 1 / 10) (κ := 1 / 2) (δ' := 1 / 100) (by norm_num) (by norm_num)
      (fun _ _ => rfl) hΔb (by norm_num) hmκ hp hy hMuy⟩

end HandMade

/-! ## 10. Nonemptiness: the BA carrier (`d = 3`, `sz0` at `n = 0`: `L = 4`, `W = 32`; `t = 1/2`, any sample `ω`; S3 identities, S6) -/

section CarrierInst
open SizesInst FlowPinsInst

private abbrev c_g₀ : ℝ := BAflowLam0 sz0 zSeq 0
private abbrev c_E₀ : ℝ := BAflowEs sz0 zSeq 0
private abbrev c_m₀ : ℂ := BAmF sz0 (BAflowLam0 sz0 zSeq) (BAflowEs sz0 zSeq) 0
private abbrev c_s₀ : ℂ := (c_E₀ : ℂ) + c_m₀

-- S3: the four identity pins at the carrier; the structural hypotheses come from `GreenCore_carrier`, `m ≠ 0` from `BAflow_real`
example (ω : sz0.SeqΩ) (u y : Vtx 3 (sz0.L 0) (sz0.W 0)) (hyu : y ≠ u)
    (hA : GreenMinor_Arow_eq_pin) (hX : GreenMinor_Xrow_eq_pin) (hsA : GreenMinor_split_A_pin) (hsX : GreenMinor_split_X_pin) :
    GreenCore_Arow (GreenCore_Gc sz0 zSeq 0 (1 / 2) ω) (GreenCore_Xc sz0 0 (1 / 2) ω) (GreenCore_Dc sz0 zSeq 0) (1 / 2) c_m₀ u =
      GreenMinor_YA (GreenCore_Gc sz0 zSeq 0 (1 / 2) ω) (GreenCore_Mc sz0 zSeq 0) (GreenCore_Dc sz0 zSeq 0) c_s₀ c_m₀ u * c_m₀ /
        GreenCore_Gc sz0 zSeq 0 (1 / 2) ω u u ∧
    GreenCore_Xrow (GreenCore_Gc sz0 zSeq 0 (1 / 2) ω) (GreenCore_Xc sz0 0 (1 / 2) ω) u y =
      -(GreenMinor_YX (GreenCore_Gc sz0 zSeq 0 (1 / 2) ω) (GreenCore_Mc sz0 zSeq 0) (GreenCore_Dc sz0 zSeq 0) c_s₀ c_m₀ u y * c_m₀ /
        GreenCore_Gc sz0 zSeq 0 (1 / 2) ω u u) ∧
    GreenCore_Arow (GreenCore_Gc sz0 zSeq 0 (1 / 2) ω) (GreenCore_Xc sz0 0 (1 / 2) ω) (GreenCore_Dc sz0 zSeq 0) (1 / 2) c_m₀ u =
      GreenMinor_YA (GreenCore_Gc sz0 zSeq 0 (1 / 2) ω) (GreenCore_Mc sz0 zSeq 0) (GreenCore_Dc sz0 zSeq 0) c_s₀ c_m₀ u -
        GreenCore_Arow (GreenCore_Gc sz0 zSeq 0 (1 / 2) ω) (GreenCore_Xc sz0 0 (1 / 2) ω) (GreenCore_Dc sz0 zSeq 0) (1 / 2) c_m₀ u *
          (GreenCore_Gc sz0 zSeq 0 (1 / 2) ω u u - c_m₀) / c_m₀ ∧
    GreenCore_Xrow (GreenCore_Gc sz0 zSeq 0 (1 / 2) ω) (GreenCore_Xc sz0 0 (1 / 2) ω) u y =
      -GreenMinor_YX (GreenCore_Gc sz0 zSeq 0 (1 / 2) ω) (GreenCore_Mc sz0 zSeq 0) (GreenCore_Dc sz0 zSeq 0) c_s₀ c_m₀ u y -
        GreenCore_Xrow (GreenCore_Gc sz0 zSeq 0 (1 / 2) ω) (GreenCore_Xc sz0 0 (1 / 2) ω) u y *
          (GreenCore_Gc sz0 zSeq 0 (1 / 2) ω u u - c_m₀) / c_m₀ := by
  obtain ⟨hGR, hRG, -, hMR, hz, hM, hMd, hD, hG0⟩ :=
    GreenCore_carrier (by norm_num : (0 : ℝ) < 1 / 2) sz0 flow_sz0 0 (t := 1 / 2) (by norm_num) (half_lt_t0 0).le ω
      (m := c_m₀) (s := c_s₀) (zt := ztOf c_m₀ c_E₀ (1 / 2)) rfl rfl rfl
  have hr := BAflow_real (1 / 2) (1 / 10) (1 / 6) (1 / 10) sz0 zSeq flow_sz0 0
  have hm0 : c_m₀ ≠ 0 := fun h0 => by
    have h1 : (1 / 2 : ℝ) ≤ c_m₀.im := hr.2
    rw [h0] at h1
    simp at h1
    linarith
  exact ⟨hA hGR hRG hMR hz hM hMd hD hm0 (hG0 u), hX hGR hRG hMR hz hM hMd hD hm0 (hG0 u) hyu,
    hsA hGR hRG hMR hz hM hMd hD hm0 (hG0 u), hsX hGR hRG hMR hz hM hMd hD hm0 (hG0 u) hyu⟩

-- S6: the averaging identities at the carrier
example (ω : sz0.SeqΩ) (a : Zd 3 (sz0.L 0)) (hE : GreenMinor_avgK_pin) (hS : GreenMinor_avg_split_pin) :
    GreenCore_vbar (GreenCore_Gc sz0 zSeq 0 (1 / 2) ω) (GreenCore_Mc sz0 zSeq 0) a -
        ((1 / 2 : ℝ) : ℂ) * ∑ b, BAMB 3 (sz0.L 0) c_g₀ (c_E₀ : ℂ) c_m₀ a b * BAMB 3 (sz0.L 0) c_g₀ (c_E₀ : ℂ) c_m₀ b a *
          GreenCore_vbar (GreenCore_Gc sz0 zSeq 0 (1 / 2) ω) (GreenCore_Mc sz0 zSeq 0) b =
      GreenMinor_avgK (GreenCore_Gc sz0 zSeq 0 (1 / 2) ω) (GreenCore_Mc sz0 zSeq 0) (GreenCore_Xc sz0 0 (1 / 2) ω)
        (GreenCore_Dc sz0 zSeq 0) (BAMB 3 (sz0.L 0) c_g₀ (c_E₀ : ℂ) c_m₀) (1 / 2) c_m₀ a ∧
    GreenMinor_avgK (GreenCore_Gc sz0 zSeq 0 (1 / 2) ω) (GreenCore_Mc sz0 zSeq 0) (GreenCore_Xc sz0 0 (1 / 2) ω)
        (GreenCore_Dc sz0 zSeq 0) (BAMB 3 (sz0.L 0) c_g₀ (c_E₀ : ℂ) c_m₀) (1 / 2) c_m₀ a =
      ∑ b', BAMB 3 (sz0.L 0) c_g₀ (c_E₀ : ℂ) c_m₀ a b' *
        (((1 / 2 : ℝ) : ℂ) * GreenCore_vbar (GreenCore_Gc sz0 zSeq 0 (1 / 2) ω) (GreenCore_Mc sz0 zSeq 0) b' *
            GreenMinor_avg (fun o : Fin (sz0.W 0 ^ 3) => GreenCore_Gc sz0 zSeq 0 (1 / 2) ω (b', o) (a, o) - GreenCore_Mc sz0 zSeq 0 (b', o) (a, o))
          - BAMB 3 (sz0.L 0) c_g₀ (c_E₀ : ℂ) c_m₀ b' a *
            GreenMinor_avg (fun o : Fin (sz0.W 0 ^ 3) =>
              GreenCore_Arow (GreenCore_Gc sz0 zSeq 0 (1 / 2) ω) (GreenCore_Xc sz0 0 (1 / 2) ω) (GreenCore_Dc sz0 zSeq 0) (1 / 2) c_m₀ (b', o) +
                ((1 / 2 : ℝ) : ℂ) * GreenCore_vbar (GreenCore_Gc sz0 zSeq 0 (1 / 2) ω) (GreenCore_Mc sz0 zSeq 0) b')
          - GreenMinor_avg (fun o : Fin (sz0.W 0 ^ 3) =>
              (GreenCore_Arow (GreenCore_Gc sz0 zSeq 0 (1 / 2) ω) (GreenCore_Xc sz0 0 (1 / 2) ω) (GreenCore_Dc sz0 zSeq 0) (1 / 2) c_m₀ (b', o) +
                ((1 / 2 : ℝ) : ℂ) * GreenCore_vbar (GreenCore_Gc sz0 zSeq 0 (1 / 2) ω) (GreenCore_Mc sz0 zSeq 0) b') *
              (GreenCore_Gc sz0 zSeq 0 (1 / 2) ω (b', o) (a, o) - GreenCore_Mc sz0 zSeq 0 (b', o) (a, o)))
          - GreenMinor_avg (fun o : Fin (sz0.W 0 ^ 3) =>
              GreenCore_Xrow (GreenCore_Gc sz0 zSeq 0 (1 / 2) ω) (GreenCore_Xc sz0 0 (1 / 2) ω) (b', o) (a, o))) := by
  obtain ⟨hGR, hRG, -, hMR, hz, hM, hMd, hD, hG0⟩ :=
    GreenCore_carrier (by norm_num : (0 : ℝ) < 1 / 2) sz0 flow_sz0 0 (t := 1 / 2) (by norm_num) (half_lt_t0 0).le ω
      (m := c_m₀) (s := c_s₀) (zt := ztOf c_m₀ c_E₀ (1 / 2)) rfl rfl rfl
  exact ⟨hE hGR hRG hMR hz hM hG0 a, hS hM a⟩

end CarrierInst

/-! ## 11. Nonemptiness: the moment bound at `sz0` (`n = 0`: `L = 4`, `W = 32`; `A = [β]`, `T = W^{-d} 1_{[β]}`, `c = W^{-3} = 1/32768 ≤ ρ² = 1/10⁴`,
`ρ = 1/100`, `p = 1`, `M = K = 2 ≤ #A = 32768`); `GreenMinor_famGain` (the pin of G5b) stays a hypothesis -/

namespace GreenMinorInst
open SizesInst

/-- the sites of the block `β` -/
def mA (β : Zd 3 (sz0.L 0)) : Finset (Idx 3 (sz0.L 0) (sz0.W 0)) :=
  (Finset.univ : Finset (Idx 3 (sz0.L 0) (sz0.W 0))).filter fun k => (split 3 (sz0.L 0) (sz0.W 0) k).1 = β

/-- the weight `W^{-d} 1_{[β]}` -/
def mT (β : Zd 3 (sz0.L 0)) : Idx 3 (sz0.L 0) (sz0.W 0) → ℝ :=
  fun k => if (split 3 (sz0.L 0) (sz0.W 0) k).1 = β then (((sz0.W 0 : ℕ) : ℝ) ^ 3)⁻¹ else 0

/-- a bounded, finitely dependent, non-constant family (`cos` of the diagonal coordinate of row `k`) -/
def mY (k : Idx 3 (sz0.L 0) (sz0.W 0)) : sz0.SeqΩ → ℂ := fun ω => ((Real.cos (ω ⟨0, (k, k, false)⟩) : ℝ) : ℂ)

end GreenMinorInst

section MomentInst
open SizesInst GreenMinorInst

example (h : GreenMinor_famAvg_moment_pin) (β : Zd 3 (sz0.L 0)) (B : ℝ)
    (hg : GreenMinor_famGain sz0 0 (mA β) mY B (1 / 100) 2 2) :
    ∫ ω, ‖∑ k ∈ mA β, ((mT β k : ℝ) : ℂ) * qRow sz0 0 k (mY k) ω‖ ^ (2 * 1) ∂(Sizes.seqP sz0) ≤
      ((2 * (1 : ℕ) : ℝ) + 1) * (2 * (1 : ℕ) : ℝ) ^ (2 * 1) * ((2 : ℝ) ^ (2 * 1 - 1) * (1 / 100) * B) ^ (2 * 1) := by
  have hW : sz0.W 0 = 32 := (sz0_values.2.1)
  refine h (c := (((sz0.W 0 : ℕ) : ℝ) ^ 3)⁻¹) (p := 1) (T := mT β) ?_ ?_ hg (by norm_num) (by norm_num) (by norm_num) ?_ ?_ ?_
  · intro k
    refine ⟨((Complex.measurable_ofReal.comp (Real.measurable_cos.comp (measurable_pi_apply _)))), 1, fun ω => ?_⟩
    simp only [mY, Complex.norm_real, Real.norm_eq_abs]
    exact Real.abs_cos_le_one _
  · intro k
    refine ⟨{⟨0, (k, k, false)⟩}, fun ω ω' hω => ?_⟩
    simp only [mY]
    rw [hω ⟨0, (k, k, false)⟩ (Finset.mem_singleton_self _)]
  · rw [hW]; norm_num
  · exact UniformWeight.toBoundedWeight (uniformWeight_blockAvg2 (d := 3) (L := sz0.L 0) (W := sz0.W 0) β)
  · rw [mA, flucVanish_card_blockSupport, hW]; norm_num

end MomentInst

/-! ## 12. Nonemptiness: `BAFAav` at `sz0` and the flow `flow_sz0` (`κ = 1/2`, `ε = 1/10`, `𝔠 = 1/6`, `𝔡 = 1/10`), `t ≡ 1/2 ≤ T₀`, `ε₀ = 1/10`,
`Ψ = W^{-1}` (window `W^{-3/2} ≤ Ψ ≤ W^{-1/10}`); `BAGiiGEX` (G6's pin) and `STInitialGT2gL` (the premise) stay hypotheses -/

section FAavInst
open SizesInst FlowPinsInst

example (h : BAFAav 3) (hii : BAGiiGEX sz0 zSeq (fun _ => 1 / 2) (1 / 10)) :
    STInitialGT2gL (baFMz sz0 zSeq) (Sizes.seqP (sz0.withLam 0)) (fun _ => 1 / 2) (1 / 10)
        (fun n => ((sz0.W n : ℕ) : ℝ) ^ (-1 : ℝ)) →
      PrecL sz0 (Sizes.seqP (sz0.withLam 0)) (U := fun n => Zd 3 (sz0.L n))
        (fun n a ω => ‖(((sz0.W n : ℝ) ^ 3)⁻¹ : ℝ) * ∑ o, ∑ b',
          BAMB 3 (sz0.L n) (BAflowLam0 sz0 zSeq n) (BAflowEs sz0 zSeq n : ℂ) (BAmF sz0 (BAflowLam0 sz0 zSeq) (BAflowEs sz0 zSeq) n) a b' *
            GreenCore_K (GreenCore_Gc sz0 zSeq n (1 / 2) ω) (GreenCore_Mc sz0 zSeq n) (GreenCore_Xc sz0 n (1 / 2) ω)
              (GreenCore_Dc sz0 zSeq n) (1 / 2) (BAmF sz0 (BAflowLam0 sz0 zSeq) (BAflowEs sz0 zSeq) n) (b', o) (a, o)‖)
        (fun n _ _ => (((sz0.W n : ℕ) : ℝ) ^ (-1 : ℝ)) ^ 2) := by
  have h1 : ∀ n, (1 : ℝ) ≤ ((sz0.W n : ℕ) : ℝ) := fun n => by exact_mod_cast sz0.W_pos n
  exact h (1 / 2) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 6) sz0 zSeq flow_sz0 (fun _ => 1 / 2)
    (fun _ => by norm_num) (fun n => (half_lt_t0 n).le) (1 / 10) (by norm_num) hii (fun n => ((sz0.W n : ℕ) : ℝ) ^ (-1 : ℝ))
    (Eventually.of_forall fun n => Real.rpow_le_rpow_of_exponent_le (h1 n) (by norm_num))
    (Eventually.of_forall fun n => Real.rpow_le_rpow_of_exponent_le (h1 n) (by norm_num))

end FAavInst

/-! ## 13. The displayed S4 is false: a compiled negative instance

`κ = 4 = ‖m‖`, `m = 4`, `D = 0` (`g₀ = 0`), `s = 1`, `δ = 1/100`, `m₀ = 3`, `l = []`.  `G = 4·1 + (1/50) E_{u,y}` (`u = (0,0)`, `y = (e_0, 0)`, a
one-sided entry, so the tower is `G` restricted to the sites outside `S`); `Δ_{uy} = 2δ` satisfies the event on every protected level.
`Y^X_{uy} = -s Δ_{uy}`, `‖Y^X_{uy}‖ = 1/50`, but the displayed bound is `c_Y(0) (2δ) = (5/4)(1/2)(1/50) = 1/80`.  For `κ ≤ 1` (BA: `κ ≤ ‖m‖ ≤ 1`)
`a_0 = 2/κ ≥ 1` and the base case holds. -/

section NegS4
open GreenMinorInst

example : ¬ GreenMinor_diff_pin := by
  intro h
  have hpy : hp ≠ hy := by decide
  have hy1 : hy.1 ≠ 0 := by decide
  let M4 : Matrix HV HV ℂ := Matrix.of fun u v => if u.2 = v.2 then (if u.1 = v.1 then (4 : ℂ) else 0) else 0
  let Δ4 : Matrix HV HV ℂ := Matrix.of fun x y => if x = hp ∧ y = hy then ((1 / 50 : ℝ) : ℂ) else 0
  let G4 : Matrix HV HV ℂ := M4 + Δ4
  let Gs : Finset HV → Matrix HV HV ℂ := fun S => Matrix.of fun x y => if x ∈ S ∨ y ∈ S then 0 else G4 x y
  have hM4 : ∀ x y, M4 x y = if x = y then 4 else 0 := by
    intro x y
    simp only [M4, Matrix.of_apply, Prod.ext_iff]
    split_ifs <;> simp_all
  have hG4 : ∀ x y, G4 x y = (if x = y then 4 else 0) + (if x = hp ∧ y = hy then ((1 / 50 : ℝ) : ℂ) else 0) := by
    intro x y; simp [G4, hM4, Δ4]
  have hT : GreenMinor_Tower G4 Gs := by
    refine ⟨by ext x y; simp [Gs], ?_⟩
    intro S κ hκ x y
    show Gs (insert κ S) x y = Gs S x y - Gs S x κ * Gs S κ y / Gs S κ κ
    have hκκ : Gs S κ κ = 4 := by
      have : κ = hp → κ = hy → False := fun h1 h2 => hpy (h1.symm.trans h2)
      simp [Gs, hκ, hG4]
      exact fun h1 h2 => this h1 h2
    by_cases hxS : x ∈ S
    · have e1 : Gs (insert κ S) x y = 0 := by simp [Gs, hxS]
      have e2 : Gs S x y = 0 := by simp [Gs, hxS]
      have e3 : Gs S x κ = 0 := by simp [Gs, hxS]
      rw [e1, e2, e3]; simp
    by_cases hyS : y ∈ S
    · have e1 : Gs (insert κ S) x y = 0 := by simp [Gs, hyS]
      have e2 : Gs S x y = 0 := by simp [Gs, hyS]
      have e3 : Gs S κ y = 0 := by simp [Gs, hyS]
      rw [e1, e2, e3]; simp
    by_cases hxκ : x = κ
    · subst hxκ
      have e1 : Gs (insert x S) x y = 0 := by simp [Gs]
      rw [e1, hκκ]; ring
    by_cases hyκ : y = κ
    · subst hyκ
      have e1 : Gs (insert y S) x y = 0 := by simp [Gs]
      rw [e1, hκκ]; ring
    have e1 : Gs (insert κ S) x y = G4 x y := by simp [Gs, hxS, hyS, hxκ, hyκ]
    have e2 : Gs S x y = G4 x y := by simp [Gs, hxS, hyS]
    have e3 : Gs S x κ = G4 x κ := by simp [Gs, hxS, hκ]
    have e4 : Gs S κ y = G4 κ y := by simp [Gs, hyS, hκ]
    have hprod : G4 x κ * G4 κ y = 0 := by
      rw [hG4, hG4]
      by_cases h1 : x = hp ∧ κ = hy
      · have : ¬ (κ = hp ∧ y = hy) := fun h2 => hpy (h2.1.symm.trans h1.2)
        simp [hxκ, Ne.symm hyκ, this]
      · simp [h1, hxκ]
    rw [e1, e2, e3, e4, hprod, zero_div, sub_zero]
  have hgood : GreenMinor_good Gs M4 4 (1 / 100) 3 0 0 := by
    intro S _ _ x y _ _ hxS hyS
    have e1 : Gs S x y = G4 x y := by simp [Gs, hxS, hyS]
    have e2 : Gs S x x = G4 x x := by simp [Gs, hxS]
    have hd : G4 x y - M4 x y = if x = hp ∧ y = hy then ((1 / 50 : ℝ) : ℂ) else 0 := by
      simp [G4, Δ4]
    refine ⟨?_, ?_⟩
    · rw [e1, hd]
      split_ifs
      · simp; norm_num
      · simp
    · rw [e2, hG4]
      have : ¬ (x = hp ∧ x = hy) := fun h1 => hpy (h1.1.symm.trans h1.2)
      simp [this]
  have hMuy : ‖M4 hp hy‖ ≤ 1 := by
    rw [hM4]; simp [hpy]
  have key := h (G := G4) (M := M4) (D := 0) (Mb := fun a b => if a = b then 4 else 0) (Gs := Gs) (s := 1) (m := 4) (κ := 4)
    (δ := 1 / 100) (g₀ := 0) (m₀ := 3) (β := 0) (o := 0) (u := hp) (y := hy) (by norm_num) (by norm_num)
    (fun u l => by split_ifs <;> simp) (fun _ _ => rfl) (by norm_num) (by simp) hMuy hT hgood rfl ⟨rfl, hy1⟩ [] (by simp)
    (by simp) (by simp) (by norm_num)
  have k1 := key.1
  simp [hT.base, GreenMinor_YX, GreenMinor_cY, GreenMinor_a, hG4, hM4, hpy] at k1
  norm_num at k1

end NegS4

end RBM.BA
