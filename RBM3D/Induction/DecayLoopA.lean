/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Induction.KDecay
import RBM3D.Induction.Step2Defs
import RBM3D.Induction.Split
import RBM3D.Induction.Defs
import RBM3D.Induction.PerTimeCalc
import RBM3D.Green.Pins

/-!
# S3-07a (ticket T2133): `lem_decayLoop` at a single time and over a window

Paper: arXiv:2507.20274, `paper/tex/3_5_Loop_Hierarchy.tex`, `lem_decayLoop` (`3_5:1126`) and
`res_decayLK` (`3_5:1128`).  The source is the `d = 2` file `RBM2D/Induction/DecayLoop.lean`
(read at `9e0f275`; the ticket cites `c9a24cf`) and its pins `DecayLoopAt`, `DecayLoopWindow`
(`RBM2D/Induction/HierVocab.lean:226-262` at `c9a24cf`).

* `STdiamInf a = max_{i,j} |a_i - a_j|_∞` (the `L^∞` diameter of a label vector).
* `STDecayLoopAt sz κ 𝔠 𝔡 C₀ E u P` (the pin) and `stDecayLoopAt_holds` (`3 ≤ d`): from the decay
  input at the single time `u` (a section of `STStep2DecayPT`, prefactor `P`), every loop of length
  `k ≥ 1` with labels spread beyond `ℓ_u W^{τ'}` satisfies `(|𝓛| + |𝓛-𝒦|) ≺ W^{-D'}` per time.
* `STDecayLoopPT sz E s t` and `stDecayLoopPT_of_step2`: the same over `u ∈ [s,t]`, from
  `STStep2DecayPT Cd sz E s t` along the flow `STFlow`, `0 ≤ s ≤ t ≤ lemT z`; prefactor
  `P_u = ((1-s)/(1-u))^{Cd} Bctl^{1/5}`, `C₀ = max Cd 0 + 1`.

Proof of `stDecayLoopAt_holds` (`k ≥ 2`; for `k = 1` the far set is empty), as in RBM2D, with the
`d`-dimensional replacements marked below.  For a far `a`:
1. (`DecayLoopA_adjacent`) some adjacent pair satisfies `diam_∞ a ≤ (k-1) |a_m - a_{m+1}|_∞`
   (triangle inequality of `zdistInf` along the chain).
2. (`DecayLoopA_cut`, `DecayLoopA_pair`) rotate the loop so that this pair is (first, last label),
   cut it into a one-`G` chain and a `(k-1)`-chain; `norm_sq_gloop_le_symIdx` (Cauchy-Schwarz) gives
   `|𝓛_{σ,a}|² ≤ |𝓛_{(+,-),c}| · |symmetric (k-1)-loop|`, and the second factor is at most
   `η_u^{-2(k-1)}` (`norm_gloop_le_of_le_abs_im`).  No entry bound of `G` is used.
3. The `(+,-)` 2-loop at `c`: `|𝓛| ≤ |𝒦| + |𝓛-𝒦|`; `|𝒦|` by `STKcalDecay` at length 2 (the premise
   `W^{-Q} ≤ g` is `(eq:WO)`, `Q = d/2`, `inst_stKcalDecay_admissible`); `|𝓛-𝒦|` by the decay input
   at the pair `c` (`τ₁ = 1`, `D = Q`) with `exp(-√(|c₀-c₁|_∞/ℓ_u)) ≤ W^{-Q}` eventually.
4. `|𝓛-𝒦| ≤ |𝓛| + |𝒦|`; `|𝒦_{σ,a}| ≤ W^{-(D'+1)}` is `STKcalDecay` at length `k`
   (`diam_∞ ≤ KLmaxDist`, `zdistInf ≤ zdistD`).
5. Exponents (`DecayLoopA_alg`): `η_u⁻¹ ≤ (2/√κ) N` (`Im m(E) ≥ √κ/2` and `1 - u ≥ N⁻¹`, which
   follows from the far premise, `DecayLoopA_one_sub_u`), `STWB ≤ 2` (`DecayLoopA_STWB_le`),
   `P ≤ N^{C₀}`, `N ≤ W^{1/𝔠}`, and the exponent `Q = 2D' + (2(k-1) + 1 + C₀)/𝔠 + 1`.
6. Only the event `{|(𝓛-𝒦)_{(+,-),c}| > N ζ_c}` of the decay input at the pair `c` occurs, so the
   pointwise implication `perTimeCalc_of_imp` closes the probability.

Replacements for `d ≥ 3`: `Z2 L ↦ Zd d L`, `zdist2 ↦ zdistInf`, `KLoop.maxDist ↦ STdiamInf`,
`gloop ↦ loopL`, `BlockIndex ↦ Vtx`, `scaleM⁻² ↦ STWB` (bounded by `2` instead of `(2/κ)²`),
`KcalDecay ↦ STKcalDecay`, `Bandwidth/SizeTendsto/RangeCond ↦ Sizes.Admissible` (and the flow
`1 - u ≥ N^{-1+ε/2}` from `v3_premises_of_stFlow` for the window form).
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal

/-! ## 1. Vocabulary: the `L^∞` diameter, the pins -/

namespace RBM.Gauss.Sizes

open RBM RBM.Loop RBM.Path RBM.Gauss

/-- **`diam_∞ a = max_{i,j} |a_i - a_j|_∞`** of a label vector (the paper's `max_{i,j} |a_i - a_j|`
of `lem_decayLoop`, `3_5:1126`, with the `L^∞` distance, paper-delta T2002b).  The KL layer's
`KLmaxDist` is the `ℓ¹` one: `STdiamInf a ≤ KLmaxDist d L a` (`DecayLoopA_diam_le_KLmaxDist`). -/
def STdiamInf {d L k : ℕ} (a : Fin k → Zd d L) : ℕ :=
  Finset.univ.sup fun p : Fin k × Fin k => zdistInf d L (a p.1 - a p.2)

variable {d : ℕ}

/-- **`lem_decayLoop` (`3_5:1126`, `res_decayLK` `3_5:1128`) at a single time** (the `d`-dimensional
form of RBM2D's `DecayLoopAt`, `Induction/HierVocab.lean:236` at `c9a24cf`, `:213` at `9e0f275`):
from the `(+,-)`-decay input of the
2-loops `𝓛 - 𝒦` at the time sequence `u` with a polynomial prefactor `P` (`1 ≤ P ≤ N^{C₀}`
eventually), for every `k ≥ 1`, `τ' > 0`, `D' > 0`:
`(|𝓛^{(k)}_{u,σ,a}| + |(𝓛-𝒦)^{(k)}_{u,σ,a}|) 1(ℓ_u W^{τ'} ≤ diam_∞ a) ≺ W^{-D'}` per time.
The decay input has the shape of a section of the merged `STStep2DecayPT` (`Step2Defs.lean:287`):
`‖(𝓛-𝒦)^{(2)}_{u,σ,(a,b)}‖ ≺ P STWB(u,|a-b|_∞) exp(-(|a-b|_∞/ℓ_u)^{1/2}) + W^{-D}`, every `D > 0`.
No `u`-uniformity and no entry bound of `G` are assumed. -/
def STDecayLoopAt (sz : Sizes d) (κ 𝔠 𝔡 C₀ : ℝ) (E u P : ℕ → ℝ) : Prop :=
  0 < κ → (∀ n, |E n| ≤ 2 - κ) → sz.Admissible 𝔠 𝔡 → (∀ n, 0 ≤ u n) → (∀ n, u n < 1) →
  (∀ᶠ n : ℕ in atTop, 1 ≤ P n ∧ P n ≤ ((sz.size n : ℕ) : ℝ) ^ C₀) →
  (∀ D : ℝ, 0 < D →
    PrecPT sz (U := fun n => Unit × (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)))
      (fun n p ω => ‖Lloop sz n (E n) (u n) p.2.1 p.2.2 ω - STKloop sz n (E n) (u n) p.2.1 p.2.2‖)
      (fun n p _ => P n * STWB sz n (u n) (zdistInf d (sz.L n) (p.2.2 0 - p.2.2 1)) *
          Real.exp (-(((zdistInf d (sz.L n) (p.2.2 0 - p.2.2 1) : ℕ) : ℝ) /
            ellT (sz.L n) (sz.lam n) (u n)) ^ (1 / 2 : ℝ)) +
        ((sz.W n : ℕ) : ℝ) ^ (-D))) →
  ∀ k : ℕ, 1 ≤ k → ∀ τ' : ℝ, 0 < τ' → ∀ D' : ℝ, 0 < D' →
    PrecPT sz (U := fun n => Unit × (Fin k → Bool) × (Fin k → Zd d (sz.L n)))
      (fun n p ω =>
        (‖Lloop sz n (E n) (u n) p.2.1 p.2.2 ω‖ +
          ‖Lloop sz n (E n) (u n) p.2.1 p.2.2 ω - STKloop sz n (E n) (u n) p.2.1 p.2.2‖) *
        (if ellT (sz.L n) (sz.lam n) (u n) * ((sz.W n : ℕ) : ℝ) ^ τ' ≤ (STdiamInf p.2.2 : ℝ)
          then 1 else 0))
      (fun n _ _ => ((sz.W n : ℕ) : ℝ) ^ (-D'))

/-- **`lem_decayLoop` over a window `[s,t]`** (RBM2D `DecayLoopPT`): the conclusion of
`STDecayLoopAt` over `u ∈ [s_n, t_n]` (`TimeIcc s t`) per time. -/
def STDecayLoopPT (sz : Sizes d) (E s t : ℕ → ℝ) : Prop :=
  ∀ k : ℕ, 1 ≤ k → ∀ τ' : ℝ, 0 < τ' → ∀ D' : ℝ, 0 < D' →
    PrecPT sz (U := fun n => TimeIcc s t n × (Fin k → Bool) × (Fin k → Zd d (sz.L n)))
      (fun n p ω =>
        (‖Lloop sz n (E n) (p.1 : ℝ) p.2.1 p.2.2 ω‖ +
          ‖Lloop sz n (E n) (p.1 : ℝ) p.2.1 p.2.2 ω - STKloop sz n (E n) (p.1 : ℝ) p.2.1 p.2.2‖) *
        (if ellT (sz.L n) (sz.lam n) (p.1 : ℝ) * ((sz.W n : ℕ) : ℝ) ^ τ' ≤ (STdiamInf p.2.2 : ℝ)
          then 1 else 0))
      (fun n _ _ => ((sz.W n : ℕ) : ℝ) ^ (-D'))

end RBM.Gauss.Sizes

namespace RBM.Gauss.Sizes

open RBM RBM.Loop RBM.Path RBM.Gauss
open RBM.Ind (symIdx norm_sq_gloop_le_symIdx exists_split_loopIdx norm_gloop_le_of_le_abs_im
  symIdx_a_length)

/-! ## 2. Deterministic: the adjacent far pair and the cut -/

section Adjacent

variable {d L : ℕ} [NeZero L]

private theorem DecayLoopA_zdistInf_add_le (x y : Zd d L) :
    zdistInf d L (x + y) ≤ zdistInf d L x + zdistInf d L y := by
  unfold zdistInf
  refine Finset.sup_le fun i _ => ?_
  calc zdist L ((x + y) i) = zdist L (x i + y i) := rfl
    _ ≤ zdist L (x i) + zdist L (y i) := zdist_add_le L (x i) (y i)
    _ ≤ _ := Nat.add_le_add
        (Finset.le_sup (f := fun j => zdist L (x j)) (Finset.mem_univ i))
        (Finset.le_sup (f := fun j => zdist L (y j)) (Finset.mem_univ i))

private theorem DecayLoopA_zdistInf_neg (x : Zd d L) : zdistInf d L (-x) = zdistInf d L x := by
  unfold zdistInf
  exact Finset.sup_congr rfl fun i _ => by simp [zdist_neg]

omit [NeZero L] in
private theorem DecayLoopA_zdistInf_zero : zdistInf d L (0 : Zd d L) = 0 := by
  unfold zdistInf
  simp

private theorem DecayLoopA_zdistInf_comm (a b : Zd d L) :
    zdistInf d L (a - b) = zdistInf d L (b - a) := by
  rw [← neg_sub b a, DecayLoopA_zdistInf_neg]

private theorem DecayLoopA_zdistInf_tri (a b c : Zd d L) :
    zdistInf d L (a - c) ≤ zdistInf d L (a - b) + zdistInf d L (b - c) := by
  have := DecayLoopA_zdistInf_add_le (a - b) (b - c)
  rwa [sub_add_sub_cancel] at this

/-- `2 |x|_∞ ≤ L`: no two labels are farther than `L/2` on the torus. -/
private theorem DecayLoopA_two_mul_zdistInf_le (x : Zd d L) : 2 * zdistInf d L x ≤ L := by
  have h : zdistInf d L x ≤ L / 2 := by
    unfold zdistInf
    refine Finset.sup_le fun i _ => ?_
    unfold zdist
    omega
  omega

/-- `diam_∞ a ≤ L / 2`. -/
private theorem DecayLoopA_two_mul_diam_le {k : ℕ} (a : Fin k → Zd d L) :
    2 * STdiamInf a ≤ L := by
  have h : STdiamInf a ≤ L / 2 := by
    unfold STdiamInf
    refine Finset.sup_le fun p _ => ?_
    have := DecayLoopA_two_mul_zdistInf_le (a p.1 - a p.2)
    omega
  omega

/-- `diam_∞ a ≤ KLmaxDist a` (`zdistInf ≤ zdistD`). -/
theorem DecayLoopA_diam_le_KLmaxDist {k : ℕ} (a : Fin k → Zd d L) :
    STdiamInf a ≤ KLmaxDist d L a := by
  unfold STdiamInf
  refine Finset.sup_le fun p _ => ?_
  exact (zdistInf_le_zdistD d L _).trans
    (Finset.le_sup (f := fun q : Fin k × Fin k => zdistD d L (a q.1 - a q.2)) (Finset.mem_univ p))

/-- `diam_∞ a = 0` for a single label. -/
private theorem DecayLoopA_diam_one (a : Fin 1 → Zd d L) : STdiamInf a = 0 := by
  unfold STdiamInf
  apply Nat.eq_zero_of_le_zero
  refine Finset.sup_le fun p _ => ?_
  have : p.1 = p.2 := Subsingleton.elim _ _
  simp [this, DecayLoopA_zdistInf_zero]

/-- **Some adjacent pair is far.**  `diam_∞ a ≤ (k-1) |a_m - a_{m+1}|_∞` for some `m + 1 < k`
(triangle inequality along the chain `a_i, a_{i+1}, …, a_j`, which has at most `k - 1` steps). -/
private theorem DecayLoopA_adjacent {k : ℕ} (hk : 2 ≤ k) (a : Fin k → Zd d L) :
    ∃ (m : ℕ) (h : m + 1 < k),
      STdiamInf a ≤ (k - 1) * zdistInf d L (a ⟨m, by omega⟩ - a ⟨m + 1, h⟩) := by
  classical
  let a' : ℕ → Zd d L := fun i => if h : i < k then a ⟨i, h⟩ else 0
  have ha' : ∀ i (h : i < k), a' i = a ⟨i, h⟩ := fun i h => by simp [a', h]
  let δ : ℕ → ℕ := fun i => zdistInf d L (a' i - a' (i + 1))
  have hne : (Finset.range (k - 1)).Nonempty := ⟨0, by simp; omega⟩
  obtain ⟨m, hm, hΔ⟩ := Finset.exists_mem_eq_sup (Finset.range (k - 1)) hne δ
  have hm' : m + 1 < k := by have := Finset.mem_range.mp hm; omega
  refine ⟨m, hm', ?_⟩
  set Δ := (Finset.range (k - 1)).sup δ with hΔdef
  have hδΔ : ∀ i, i + 1 < k → δ i ≤ Δ := fun i hi =>
    Finset.le_sup (f := δ) (Finset.mem_range.mpr (by omega))
  have hchain : ∀ e i, i + e < k → zdistInf d L (a' i - a' (i + e)) ≤ e * Δ := by
    intro e
    induction e with
    | zero =>
      intro i _
      simp [DecayLoopA_zdistInf_zero]
    | succ e ih =>
      intro i hi
      have h1 := ih i (by omega)
      have h2 := hδΔ (i + e) (by omega)
      have h3 := DecayLoopA_zdistInf_tri (a' i) (a' (i + e)) (a' (i + (e + 1)))
      have h4 : δ (i + e) = zdistInf d L (a' (i + e) - a' (i + (e + 1))) := by
        simp only [δ]; rfl
      rw [h4] at h2
      calc zdistInf d L (a' i - a' (i + (e + 1)))
          ≤ zdistInf d L (a' i - a' (i + e)) + zdistInf d L (a' (i + e) - a' (i + (e + 1))) := h3
        _ ≤ e * Δ + Δ := by omega
        _ = (e + 1) * Δ := by ring
  have hmax : STdiamInf a ≤ (k - 1) * Δ := by
    unfold STdiamInf
    refine Finset.sup_le fun p _ => ?_
    obtain ⟨⟨i, hi⟩, ⟨j, hj⟩⟩ := p
    simp only
    rcases le_total i j with hij | hij
    · have := hchain (j - i) i (by omega)
      rw [show i + (j - i) = j by omega, ha' i hi, ha' j hj] at this
      calc _ ≤ (j - i) * Δ := this
        _ ≤ (k - 1) * Δ := Nat.mul_le_mul_right _ (by omega)
    · have := hchain (i - j) j (by omega)
      rw [show j + (i - j) = i by omega, ha' i hi, ha' j hj] at this
      rw [DecayLoopA_zdistInf_comm]
      calc _ ≤ (i - j) * Δ := this
        _ ≤ (k - 1) * Δ := Nat.mul_le_mul_right _ (by omega)
  have hmm : Δ = zdistInf d L (a ⟨m, by omega⟩ - a ⟨m + 1, hm'⟩) := by
    rw [hΔ]
    simp only [δ]
    rw [ha' m (by omega), ha' (m + 1) hm']
  rw [← hmm]
  exact hmax

end Adjacent

section Cut

variable {d L W : ℕ} [NeZero L]

private theorem DecayLoopA_loopL_eq_prod (H : Matrix (Vtx d L W) (Vtx d L W) ℂ) (z : ℂ)
    (I : Loop.LoopIdx (Zd d L)) :
    loopL d L W H z I
      = Matrix.trace (((I.σ.zip I.a).map fun p => Gres H z p.1 * Eblk d L W p.2).prod) := by
  have hfold : ∀ l : List (Bool × Zd d L),
      l.foldr (fun p M => Gres H z p.1 * Eblk d L W p.2 * M) 1
        = (l.map fun p => Gres H z p.1 * Eblk d L W p.2).prod := by
    intro l
    induction l with
    | nil => simp
    | cons p l ih => simp [ih]
  unfold loopL
  rw [hfold]

/-- Cyclic invariance of `𝓛`: moving the first edge to the end (trace cyclicity). -/
private theorem DecayLoopA_loopL_rotate (H : Matrix (Vtx d L W) (Vtx d L W) ℂ) (z : ℂ) (s : Bool)
    (b : Zd d L) (σ : List Bool) (a : List (Zd d L)) (h : σ.length = a.length) :
    loopL d L W H z ⟨s :: σ, b :: a⟩ = loopL d L W H z ⟨σ ++ [s], a ++ [b]⟩ := by
  rw [DecayLoopA_loopL_eq_prod, DecayLoopA_loopL_eq_prod]
  simp only [List.zip_cons_cons, List.map_cons, List.prod_cons]
  rw [List.zip_append h]
  simp only [List.map_append, List.prod_append, List.zip_cons_cons, List.zip_nil_left,
    List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, Matrix.mul_one]
  exact Matrix.trace_mul_comm _ _

/-- Rotating a loop by `j` positions does not change `𝓛`. -/
private theorem DecayLoopA_loopL_rotate_iter {H : Matrix (Vtx d L W) (Vtx d L W) ℂ} {z : ℂ} :
    ∀ (j : ℕ) (σ : List Bool) (a : List (Zd d L)), σ.length = a.length →
      loopL d L W H z ⟨σ.rotate j, a.rotate j⟩ = loopL d L W H z ⟨σ, a⟩ := by
  intro j
  induction j with
  | zero => intro σ a _; simp
  | succ j ih =>
    intro σ a h
    cases σ with
    | nil =>
      have : a = [] := List.eq_nil_of_length_eq_zero (by simpa using h.symm)
      subst this; simp
    | cons s σ =>
      cases a with
      | nil => simp at h
      | cons b a =>
        have h' : σ.length = a.length := by simpa using h
        rw [List.rotate_cons_succ, List.rotate_cons_succ]
        rw [ih (σ ++ [s]) (a ++ [b]) (by simp [h'])]
        exact (DecayLoopA_loopL_rotate H z s b σ a h').symm

variable [NeZero W]

/-- **The cut.**  For a loop of length `k ≥ 2` and `m + 1 < k`, with `s = σ_{m+1}`,
`b' = a_{m+1}`, `b = a_m`: `|𝓛_{σ,a}|² ≤ η^{-2(k-1)} |𝓛 ⟨[s, !s], [b', b]⟩|`.  The loop is rotated by
`m + 1` so that `(a_{m+1}, a_m)` is (first label, last label), then cut into the one-`G` chain
`G_{σ_{m+1}}` and the `(k-1)`-chain; `norm_sq_gloop_le_symIdx` (Cauchy-Schwarz) and
`norm_gloop_le_of_le_abs_im` (operator norm bound of the symmetric `(k-1)`-loop) finish. -/
private theorem DecayLoopA_cut
    {H : Matrix (Vtx d L W) (Vtx d L W) ℂ} (hH : H.IsHermitian) {z : ℂ} {η : ℝ}
    (hη : 0 < η) (hz : η ≤ |z.im|) {k : ℕ} (hk : 2 ≤ k) (σl : List Bool) (al : List (Zd d L))
    (hσ : σl.length = k) (ha : al.length = k) (m : ℕ) (hm : m + 1 < k) :
    ∃ (s : Bool) (b' b : Zd d L), σl[m + 1]? = some s ∧ al[m + 1]? = some b' ∧ al[m]? = some b ∧
      ‖loopL d L W H z ⟨σl, al⟩‖ ^ 2 ≤
        η⁻¹ ^ (2 * (k - 1)) * ‖loopL d L W H z ⟨[s, !s], [b', b]⟩‖ := by
  have hlen : σl.length = al.length := by omega
  have hrot := DecayLoopA_loopL_rotate_iter (H := H) (z := z) (m + 1) σl al hlen
  obtain ⟨σA, σB, aA, aB, b', b, hσeq, haeq, hσA, haA, hσB, haB⟩ :=
    exists_split_loopIdx (k₁ := 1) (k₂ := k - 1) (by omega) (by omega)
      (σ := σl.rotate (m + 1)) (a := al.rotate (m + 1)) (by simp [hσ]; omega) (by simp [ha]; omega)
  have haA0 : aA = [] := List.eq_nil_of_length_eq_zero (by omega)
  obtain ⟨s, hs⟩ : ∃ s, σA = [s] := by
    match σA, hσA with
    | [s], _ => exact ⟨s, rfl⟩
  subst haA0
  subst hs
  refine ⟨s, b', b, ?_, ?_, ?_, ?_⟩
  · have h1 : (σl.rotate (m + 1))[0]? = some s := by
      rw [hσeq]; simp
    rw [List.getElem?_rotate (by omega)] at h1
    have : (0 + (m + 1)) % σl.length = m + 1 := by
      rw [hσ]; simp only [zero_add]; exact Nat.mod_eq_of_lt hm
    rwa [this] at h1
  · have h1 : (al.rotate (m + 1))[0]? = some b' := by
      rw [haeq]; simp
    rw [List.getElem?_rotate (by omega)] at h1
    have : (0 + (m + 1)) % al.length = m + 1 := by
      rw [ha]; simp only [zero_add]; exact Nat.mod_eq_of_lt hm
    rwa [this] at h1
  · have h1 : (al.rotate (m + 1))[k - 1]? = some b := by
      have : (al.rotate (m + 1)).getLast? = some b := by
        rw [haeq, List.nil_append, List.singleton_append, ← List.cons_append, List.getLast?_concat]
      rwa [List.getLast?_eq_getElem?, List.length_rotate, ha] at this
    rw [List.getElem?_rotate (by omega)] at h1
    have : (k - 1 + (m + 1)) % al.length = m := by
      rw [ha]
      have : k - 1 + (m + 1) = m + k := by omega
      rw [this, Nat.add_mod_right]
      exact Nat.mod_eq_of_lt (by omega)
    rwa [this] at h1
  · rw [← hrot, hσeq, haeq]
    have h := norm_sq_gloop_le_symIdx (z := z) hH (σA := [s]) (σB := σB) (aA := []) (aB := aB)
      (by simp) (by omega) b' b
    refine h.trans ?_
    have hsym : symIdx [s] ([] : List (Zd d L)) b' b = ⟨[s, !s], [b', b]⟩ := by
      simp [symIdx]
    rw [hsym, mul_comm (η⁻¹ ^ (2 * (k - 1)))]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    have hB := norm_gloop_le_of_le_abs_im (z := z) (W := W) hH hη hz (symIdx σB aB b b')
      (by simp; omega) (by simp; omega)
    refine hB.trans ?_
    simp only [symIdx_a_length]
    have h2 : 2 * (aB.length + 1) = 2 * (k - 1) := by omega
    rw [h2]
    have hW : (((W : ℝ) ^ d)⁻¹) ≤ 1 := by
      have : (1 : ℝ) ≤ (W : ℝ) ^ d :=
        one_le_pow₀ (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne W))
      exact inv_le_one_of_one_le₀ this
    have hW' : (((W : ℝ) ^ d)⁻¹) ^ (2 * (k - 1) - 1) ≤ 1 :=
      pow_le_one₀ (by positivity) hW
    calc η⁻¹ ^ (2 * (k - 1)) * (((W : ℝ) ^ d)⁻¹) ^ (2 * (k - 1) - 1)
        ≤ η⁻¹ ^ (2 * (k - 1)) * 1 := by gcongr
      _ = _ := mul_one _

/-- `⟨[s, !s], [b', b]⟩` is the `(+,-)` two-loop at `(b', b)` (`s = +`) or at `(b, b')`
(`s = -`, by one rotation). -/
private theorem DecayLoopA_loopL_two_sign {H : Matrix (Vtx d L W) (Vtx d L W) ℂ} {z : ℂ}
    (s : Bool) (b' b : Zd d L) :
    loopL d L W H z ⟨[s, !s], [b', b]⟩ =
      loopL d L W H z ⟨[true, false], [if s then b' else b, if s then b else b']⟩ := by
  cases s
  · have := DecayLoopA_loopL_rotate (L := L) (W := W) H z false b' [true] [b] rfl
    simpa using this
  · simp

/-- **The far pair and the loop bound, with the pair independent of the matrix.**  For `k ≥ 2` there
is `c = (c₀, c₁)` (a function of `σ`, `a` only) with `diam_∞ a ≤ (k-1) |c₀ - c₁|_∞` and, for
every Hermitian `H` and `η ≤ |Im z|`, `|𝓛_{σ,a}|² ≤ η^{-2(k-1)} |𝓛_{(+,-),c}|`. -/
private theorem DecayLoopA_pair {k : ℕ} (hk : 2 ≤ k) (σ : Fin k → Bool) (a : Fin k → Zd d L) :
    ∃ c : Zd d L × Zd d L,
      ((STdiamInf a : ℕ) : ℝ) ≤ ((k : ℝ) - 1) * (zdistInf d L (c.1 - c.2) : ℝ) ∧
      ∀ (H : Matrix (Vtx d L W) (Vtx d L W) ℂ) (z : ℂ) (η : ℝ), H.IsHermitian →
        0 < η → η ≤ |z.im| →
        ‖loopL d L W H z (loopOf σ a)‖ ^ 2 ≤
          η⁻¹ ^ (2 * (k - 1)) * ‖loopL d L W H z ⟨[true, false], [c.1, c.2]⟩‖ := by
  obtain ⟨m, hm, hmax⟩ := DecayLoopA_adjacent hk a
  obtain ⟨s, hs⟩ : ∃ s : Bool, s = σ ⟨m + 1, hm⟩ := ⟨_, rfl⟩
  obtain ⟨b', hb'⟩ : ∃ b' : Zd d L, b' = a ⟨m + 1, hm⟩ := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : Zd d L, b = a ⟨m, by omega⟩ := ⟨_, rfl⟩
  refine ⟨(if s then b' else b, if s then b else b'), ?_, ?_⟩
  · have hcast : ((STdiamInf a : ℕ) : ℝ) ≤
        (((k - 1 : ℕ) : ℝ)) * (zdistInf d L (b - b') : ℝ) := by
      rw [hb, hb']
      exact_mod_cast hmax
    have hk1 : (((k - 1 : ℕ) : ℝ)) = (k : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]; simp
    rw [hk1] at hcast
    cases s
    · simpa using hcast
    · simp only [ite_true]
      rw [DecayLoopA_zdistInf_comm]
      simpa using hcast
  · intro H z η hH hη hz
    obtain ⟨s', b'', b''', hs', hb'', hb''', hbound⟩ := DecayLoopA_cut (W := W) hH hη hz hk
      (List.ofFn σ) (List.ofFn a) (by simp) (by simp) m hm
    rw [List.getElem?_ofFn] at hs' hb'' hb'''
    simp only [hm, dite_true, show m < k by omega] at hs' hb'' hb'''
    have e1 : s' = s := by rw [hs]; exact (Option.some.inj hs').symm
    have e2 : b'' = b' := by rw [hb']; exact (Option.some.inj hb'').symm
    have e3 : b''' = b := by rw [hb]; exact (Option.some.inj hb''').symm
    rw [e1, e2, e3, DecayLoopA_loopL_two_sign] at hbound
    exact hbound

end Cut

/-! ## 3. Deterministic: scales, exponents -/

section Scales

/-- `Im m(E) ≥ √κ / 2` for `|E| ≤ 2 - κ` (the same bound as `ST_mE_im_ge`, `Step2Events.lean:555`,
which is not imported here). -/
private theorem DecayLoopA_mE_im_ge {E κ : ℝ} (hκ : 0 < κ) (hE : |E| ≤ 2 - κ) :
    Real.sqrt κ / 2 ≤ (mE E).im := by
  rw [mE_im]
  have hκ2 : κ ≤ 2 := by have := abs_nonneg E; linarith
  have hE2 : E ^ 2 ≤ (2 - κ) ^ 2 := by
    have h := abs_le.mp hE
    nlinarith [h.1, h.2]
  have : κ ≤ 4 - E ^ 2 := by nlinarith
  have := Real.sqrt_le_sqrt this
  linarith

/-- **`1 - u ≥ N⁻¹` from the far premise.**  If `ℓ_u < L` (which the far premise
`ℓ_u W^{τ'} ≤ diam_∞ a ≤ L/2` gives) then `g² < L² (1 - u)`; with `g² ≥ W^{-d}` (`(eq:WO)`) and
`L² ≤ L^d` this is `1 - u > (W L)^{-d} = N⁻¹`. -/
private theorem DecayLoopA_one_sub_u {d L W : ℕ} (hd : 2 ≤ d) (hL : 3 ≤ L) (hW : 1 ≤ W)
    {g u : ℝ} (hg : 0 < g) (hgW : ((W : ℝ) ^ d)⁻¹ ≤ g ^ 2) (hu : u < 1)
    (hℓ : ellT L g u < L) : ((((W * L) ^ d : ℕ) : ℝ))⁻¹ ≤ 1 - u := by
  have hv : 0 < 1 - u := by linarith
  have h1 : g / Real.sqrt |1 - u| < L := by
    unfold ellT at hℓ
    rcases min_lt_iff.mp hℓ with h | h
    · exact lt_of_le_of_lt (le_max_left _ _) h
    · exact absurd h (lt_irrefl _)
  rw [abs_of_pos hv] at h1
  have hs : 0 < Real.sqrt (1 - u) := Real.sqrt_pos.mpr hv
  have h2 : g < L * Real.sqrt (1 - u) := by rwa [div_lt_iff₀ hs] at h1
  have h3 : g ^ 2 < (L : ℝ) ^ 2 * (1 - u) := by
    have := pow_lt_pow_left₀ h2 hg.le (two_ne_zero)
    rwa [mul_pow, Real.sq_sqrt hv.le] at this
  have hW0 : (0 : ℝ) < (W : ℝ) ^ d := by
    have : (0 : ℝ) < W := by exact_mod_cast hW
    positivity
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast (by omega : 1 ≤ L)
  have hL0 : (0 : ℝ) < (L : ℝ) ^ d := by positivity
  have h4 : 1 ≤ (W : ℝ) ^ d * g ^ 2 := by
    have := mul_le_mul_of_nonneg_left hgW hW0.le
    rwa [mul_inv_cancel₀ hW0.ne'] at this
  have hL2 : (L : ℝ) ^ 2 ≤ (L : ℝ) ^ d := pow_le_pow_right₀ hL1 hd
  have hN : ((((W * L) ^ d : ℕ) : ℝ)) = (W : ℝ) ^ d * (L : ℝ) ^ d := by
    push_cast; ring
  have h5 : 1 ≤ ((((W * L) ^ d : ℕ) : ℝ)) * (1 - u) := by
    rw [hN]
    calc (1 : ℝ) ≤ (W : ℝ) ^ d * g ^ 2 := h4
      _ ≤ (W : ℝ) ^ d * ((L : ℝ) ^ 2 * (1 - u)) := by gcongr
      _ ≤ (W : ℝ) ^ d * ((L : ℝ) ^ d * (1 - u)) := by gcongr
      _ = _ := by ring
  have hNpos : (0 : ℝ) < (((W * L) ^ d : ℕ) : ℝ) := by rw [hN]; positivity
  calc ((((W * L) ^ d : ℕ) : ℝ))⁻¹ = ((((W * L) ^ d : ℕ) : ℝ))⁻¹ * 1 := (mul_one _).symm
    _ ≤ ((((W * L) ^ d : ℕ) : ℝ))⁻¹ * (((((W * L) ^ d : ℕ) : ℝ)) * (1 - u)) := by gcongr
    _ = 1 - u := by field_simp

/-- **`STWB ≤ 2` in the far regime**: `W^{-d} B_{u,K} ≤ (W^d g²)⁻¹ + (N (1-u))⁻¹ ≤ 2` once
`g² W^d ≥ 1` and `N (1-u) ≥ 1`. -/
private theorem DecayLoopA_STWB_le {d : ℕ} (sz : Sizes d) (n : ℕ) {u : ℝ} (K : ℕ) (hu : u < 1)
    (hg : 1 ≤ sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d)
    (hN : 1 ≤ ((sz.size n : ℕ) : ℝ) * (1 - u)) : STWB sz n u K ≤ 2 := by
  have hv : 0 < 1 - u := by linarith
  have hW0 : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) ^ d := by
    have : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
    positivity
  have hL0 : (0 : ℝ) < ((sz.L n : ℕ) : ℝ) ^ d := by
    have : (0 : ℝ) < ((sz.L n : ℕ) : ℝ) := by
      have := sz.three_le_L n; exact_mod_cast (by omega : 0 < sz.L n)
    positivity
  have hg2 : 0 < sz.lam n ^ 2 := by
    by_contra h
    push Not at h
    have : sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h hW0.le
    linarith
  have hNe : ((sz.size n : ℕ) : ℝ) = ((sz.W n : ℕ) : ℝ) ^ d * ((sz.L n : ℕ) : ℝ) ^ d := by
    simp only [Sizes.size]; push_cast; ring
  unfold STWB Bparam
  rw [abs_of_pos hv]
  have hT1 : (sz.lam n ^ 2 + (1 - u))⁻¹ * ((((K : ℕ) : ℝ) + 1) ^ (d - 2))⁻¹ ≤
      (sz.lam n ^ 2)⁻¹ := by
    have ha : (sz.lam n ^ 2 + (1 - u))⁻¹ ≤ (sz.lam n ^ 2)⁻¹ := inv_anti₀ hg2 (by linarith)
    have hb : ((((K : ℕ) : ℝ) + 1) ^ (d - 2))⁻¹ ≤ 1 :=
      inv_le_one_of_one_le₀ (one_le_pow₀ (by linarith [(Nat.cast_nonneg K : (0 : ℝ) ≤ K)]))
    calc (sz.lam n ^ 2 + (1 - u))⁻¹ * ((((K : ℕ) : ℝ) + 1) ^ (d - 2))⁻¹
        ≤ (sz.lam n ^ 2)⁻¹ * 1 := mul_le_mul ha hb (by positivity) (by positivity)
      _ = _ := mul_one _
  calc (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * ((sz.lam n ^ 2 + (1 - u))⁻¹ *
        ((((K : ℕ) : ℝ) + 1) ^ (d - 2))⁻¹ + (((sz.L n : ℕ) : ℝ) ^ d * (1 - u))⁻¹)
      ≤ (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * ((sz.lam n ^ 2)⁻¹ +
          (((sz.L n : ℕ) : ℝ) ^ d * (1 - u))⁻¹) := by gcongr
    _ = (sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d)⁻¹ +
          (((sz.size n : ℕ) : ℝ) * (1 - u))⁻¹ := by
        rw [hNe]; field_simp
    _ ≤ 1 + 1 := by
        gcongr <;> exact inv_le_one_of_one_le₀ ‹_›
    _ = 2 := by norm_num

/-- `STWB ≥ 0`. -/
private theorem DecayLoopA_STWB_nonneg {d : ℕ} (sz : Sizes d) (n : ℕ) (u : ℝ) (K : ℕ) :
    0 ≤ STWB sz n u K := by
  unfold STWB Bparam
  positivity

/-- The chain of inequalities for a far loop, in abstract real quantities: `Λ = |𝓛_{σ,a}|`,
`Lp = |𝓛_{(+,-),c}|`, `Kp = |𝒦_{(+,-),c}|`, `X = |(𝓛-𝒦)_{(+,-),c}|` bounded through the decay input
(`Pn` the prefactor, `Mi = STWB(u,|c₀-c₁|) ≤ Θ`, `ex = exp(-√(|c₀-c₁|_∞/ℓ_u))`), `Kc = |𝒦_{σ,a}|`,
`ηi = η_u⁻¹`; with `Q = 2D' + A(2(k-1) + 1 + C₀) + 1`, `A = 1/𝔠` and `N ≤ W^A`, then
`2Λ + Kc ≤ W^{-D'}` once `W ≥ max(2, 16 Γ^{2(k-1)}(2 + Θ))`.  (RBM2D `DecayLoop_alg`, with
`M_u^{-2} ≤ Γ²` replaced by the constant `Θ`.) -/
private theorem DecayLoopA_alg {W N Γ Θ A ηi Λ Kp X Kc Lp Pn Mi ex : ℝ} {k : ℕ} {D' C₀ Q : ℝ}
    (hk : 2 ≤ k) (hC₀ : 0 ≤ C₀) (hΓ : 0 ≤ Γ) (hΘ : 0 ≤ Θ)
    (hW : 2 ≤ W) (hWmin : 16 * Γ ^ (2 * (k - 1)) * (2 + Θ) ≤ W)
    (hN1 : 1 ≤ N) (hNW : N ≤ W ^ A)
    (hQ : Q = 2 * D' + A * (2 * ((k : ℝ) - 1) + 1 + C₀) + 1)
    (hηi0 : 0 ≤ ηi) (hηi : ηi ≤ Γ * N)
    (hΛ0 : 0 ≤ Λ) (hLp0 : 0 ≤ Lp) (hΛ : Λ ^ 2 ≤ ηi ^ (2 * (k - 1)) * Lp)
    (hLp : Lp ≤ Kp + X) (hKp : Kp ≤ W ^ (-Q))
    (hX : X ≤ N * (Pn * Mi * ex + W ^ (-Q)))
    (hPn : Pn ≤ N ^ C₀) (hMi : Mi ≤ Θ) (hex : ex ≤ W ^ (-Q))
    (hMi0 : 0 ≤ Mi) (hex0 : 0 ≤ ex)
    (hKc : Kc ≤ W ^ (-(D' + 1))) :
    2 * Λ + Kc ≤ W ^ (-D') := by
  have hW0 : 0 < W := by linarith
  have hWQ : 0 < W ^ (-Q) := Real.rpow_pos_of_pos hW0 _
  have hN0 : 0 < N := by linarith
  set r : ℝ := 2 * ((k : ℝ) - 1) + 1 + C₀ with hr
  have hk1 : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hr0 : 0 ≤ r := by rw [hr]; nlinarith
  -- Step 1: Kp + X ≤ W^{-Q} (2 + Θ) N^{1 + C₀}
  have hN1C : 1 ≤ N ^ (1 + C₀) := Real.one_le_rpow hN1 (by linarith)
  have hNN1C : N ≤ N ^ (1 + C₀) := by
    calc N = N ^ (1 : ℝ) := (Real.rpow_one N).symm
      _ ≤ N ^ (1 + C₀) := Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  have hPMe : Pn * Mi * ex ≤ N ^ C₀ * Θ * W ^ (-Q) := by
    have h1 : Pn * Mi ≤ N ^ C₀ * Θ := mul_le_mul hPn hMi hMi0 (by positivity)
    exact mul_le_mul h1 hex hex0 (mul_nonneg (by positivity) hΘ)
  have hX2 : X ≤ W ^ (-Q) * (Θ * N ^ (1 + C₀) + N) := by
    calc X ≤ N * (Pn * Mi * ex + W ^ (-Q)) := hX
      _ ≤ N * (N ^ C₀ * Θ * W ^ (-Q) + W ^ (-Q)) := by gcongr
      _ = W ^ (-Q) * (Θ * (N * N ^ C₀) + N) := by ring
      _ = W ^ (-Q) * (Θ * N ^ (1 + C₀) + N) := by
        rw [Real.rpow_add hN0, Real.rpow_one]
  have hKX : Kp + X ≤ W ^ (-Q) * ((2 + Θ) * N ^ (1 + C₀)) := by
    calc Kp + X ≤ W ^ (-Q) + W ^ (-Q) * (Θ * N ^ (1 + C₀) + N) := add_le_add hKp hX2
      _ = W ^ (-Q) * (1 + (Θ * N ^ (1 + C₀) + N)) := by ring
      _ ≤ W ^ (-Q) * ((2 + Θ) * N ^ (1 + C₀)) := by
        apply mul_le_mul_of_nonneg_left _ hWQ.le
        nlinarith
  -- Step 2: Λ² ≤ Γ^{2(k-1)} (2+Θ) N^r W^{-Q}
  have hηpow : ηi ^ (2 * (k - 1)) ≤ (Γ * N) ^ (2 * (k - 1)) := pow_le_pow_left₀ hηi0 hηi _
  have hLpb : Lp ≤ W ^ (-Q) * ((2 + Θ) * N ^ (1 + C₀)) := hLp.trans hKX
  have hexp : ((2 * (k - 1) : ℕ) : ℝ) = 2 * ((k : ℝ) - 1) := by
    rw [Nat.cast_mul, Nat.cast_sub (by omega)]; simp
  have hNr' : N ^ (2 * (k - 1)) * N ^ (1 + C₀) = N ^ r := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hN0, hexp]
    congr 1; rw [hr]; ring
  have hΛ2 : Λ ^ 2 ≤ Γ ^ (2 * (k - 1)) * (2 + Θ) * (N ^ r * W ^ (-Q)) := by
    have hηnn : 0 ≤ ηi ^ (2 * (k - 1)) := by positivity
    calc Λ ^ 2 ≤ ηi ^ (2 * (k - 1)) * Lp := hΛ
      _ ≤ (Γ * N) ^ (2 * (k - 1)) * (W ^ (-Q) * ((2 + Θ) * N ^ (1 + C₀))) := by
        gcongr
      _ = Γ ^ (2 * (k - 1)) * (2 + Θ) * ((N ^ (2 * (k - 1)) * N ^ (1 + C₀)) * W ^ (-Q)) := by
        rw [mul_pow]; ring
      _ = Γ ^ (2 * (k - 1)) * (2 + Θ) * (N ^ r * W ^ (-Q)) := by rw [hNr']
  -- Step 3: N^r ≤ W^{A r}, W^{A r} W^{-Q} = W^{-D'}² W⁻¹
  have hNr : N ^ r ≤ W ^ (A * r) := by
    calc N ^ r ≤ (W ^ A) ^ r := Real.rpow_le_rpow hN0.le hNW hr0
      _ = W ^ (A * r) := (Real.rpow_mul hW0.le A r).symm
  have ht0 : 0 < W ^ (-D') := Real.rpow_pos_of_pos hW0 _
  have hWQ' : W ^ (A * r) * W ^ (-Q) = (W ^ (-D')) ^ 2 * W⁻¹ := by
    rw [← Real.rpow_add hW0, ← Real.rpow_natCast, ← Real.rpow_mul hW0.le,
      ← Real.rpow_neg_one, ← Real.rpow_add hW0]
    congr 1
    rw [hQ]; push_cast; ring
  have hΛ3 : Λ ^ 2 ≤ Γ ^ (2 * (k - 1)) * (2 + Θ) * ((W ^ (-D')) ^ 2 * W⁻¹) := by
    have hc : 0 ≤ Γ ^ (2 * (k - 1)) * (2 + Θ) := mul_nonneg (by positivity) (by linarith)
    calc Λ ^ 2 ≤ Γ ^ (2 * (k - 1)) * (2 + Θ) * (N ^ r * W ^ (-Q)) := hΛ2
      _ ≤ Γ ^ (2 * (k - 1)) * (2 + Θ) * (W ^ (A * r) * W ^ (-Q)) := by gcongr
      _ = _ := by rw [hWQ']
  -- Step 4: 2 Λ ≤ W^{-D'}/2
  have hcoef : 4 * (Γ ^ (2 * (k - 1)) * (2 + Θ)) * W⁻¹ ≤ 1 / 4 := by
    have h1 : 4 * (Γ ^ (2 * (k - 1)) * (2 + Θ)) * W⁻¹ =
        (16 * Γ ^ (2 * (k - 1)) * (2 + Θ)) / (4 * W) := by
      field_simp; ring
    rw [h1, div_le_iff₀ (by positivity)]
    nlinarith
  have h2Λ : 2 * Λ ≤ W ^ (-D') / 2 := by
    have hsq : (2 * Λ) ^ 2 ≤ (W ^ (-D') / 2) ^ 2 := by
      calc (2 * Λ) ^ 2 = 4 * Λ ^ 2 := by ring
        _ ≤ 4 * (Γ ^ (2 * (k - 1)) * (2 + Θ) * ((W ^ (-D')) ^ 2 * W⁻¹)) := by gcongr
        _ = (4 * (Γ ^ (2 * (k - 1)) * (2 + Θ)) * W⁻¹) * (W ^ (-D')) ^ 2 := by ring
        _ ≤ (1 / 4) * (W ^ (-D')) ^ 2 := by gcongr
        _ = (W ^ (-D') / 2) ^ 2 := by ring
    exact (sq_le_sq₀ (by positivity) (by positivity)).mp hsq
  -- Step 5: Kc ≤ W^{-D'}/2
  have hKc' : Kc ≤ W ^ (-D') / 2 := by
    have : W ^ (-(D' + 1)) = W ^ (-D') * W⁻¹ := by
      rw [← Real.rpow_neg_one, ← Real.rpow_add hW0]; congr 1; ring
    have h3 : W⁻¹ ≤ 1 / 2 := by
      rw [inv_eq_one_div]; exact one_div_le_one_div_of_le (by norm_num) hW
    calc Kc ≤ W ^ (-(D' + 1)) := hKc
      _ = W ^ (-D') * W⁻¹ := this
      _ ≤ W ^ (-D') * (1 / 2) := by gcongr
      _ = W ^ (-D') / 2 := by ring
  linarith

/-- `exp(-√x) ≤ W^{-Q}` for `x ≥ (W^{τ'/2}/K)²`, eventually in `W` (`log W ≤ W^{τ'/4}/(τ'/4)`). -/
private theorem DecayLoopA_exp_small {τ' : ℝ} (hτ' : 0 < τ') {K Q : ℝ} (hK : 0 < K) (hQ : 0 ≤ Q) :
    ∀ᶠ w : ℝ in atTop, ∀ x : ℝ, (w ^ (τ' / 2) / K) ^ 2 ≤ x →
      Real.exp (-Real.sqrt x) ≤ w ^ (-Q) := by
  have hev : ∀ᶠ w : ℝ in atTop, 4 * Q * K / τ' ≤ w ^ (τ' / 4) :=
    (tendsto_rpow_atTop (by linarith : 0 < τ' / 4)).eventually_ge_atTop _
  filter_upwards [hev, eventually_gt_atTop 0] with w hw hw0
  intro x hx
  have hpos : 0 ≤ w ^ (τ' / 2) / K := by positivity
  have hsq : w ^ (τ' / 2) / K ≤ Real.sqrt x := by
    calc w ^ (τ' / 2) / K = Real.sqrt ((w ^ (τ' / 2) / K) ^ 2) := (Real.sqrt_sq hpos).symm
      _ ≤ Real.sqrt x := Real.sqrt_le_sqrt hx
  have hlog : Real.log w ≤ w ^ (τ' / 4) / (τ' / 4) :=
    Real.log_le_rpow_div hw0.le (by linarith)
  have hQlog : Q * Real.log w ≤ w ^ (τ' / 2) / K := by
    have h1 : Q * Real.log w ≤ Q * (w ^ (τ' / 4) / (τ' / 4)) := by gcongr
    have h2 : Q * (w ^ (τ' / 4) / (τ' / 4)) = (4 * Q / τ') * w ^ (τ' / 4) := by
      field_simp
    have h3 : w ^ (τ' / 2) = w ^ (τ' / 4) * w ^ (τ' / 4) := by
      rw [← Real.rpow_add hw0]; congr 1; ring
    have hw4 : 0 < w ^ (τ' / 4) := Real.rpow_pos_of_pos hw0 _
    have h4 : (4 * Q / τ') * w ^ (τ' / 4) ≤ w ^ (τ' / 2) / K := by
      rw [h3, le_div_iff₀ hK]
      have : 4 * Q / τ' * K ≤ w ^ (τ' / 4) := by
        have : 4 * Q * K / τ' = 4 * Q / τ' * K := by ring
        linarith
      nlinarith
    linarith
  calc Real.exp (-Real.sqrt x) ≤ Real.exp (-(Q * Real.log w)) := by
        apply Real.exp_le_exp.mpr; linarith
    _ = w ^ (-Q) := by
        rw [Real.rpow_def_of_pos hw0]; congr 1; ring

/-- From `ℓ W^{τ'} ≤ (k-1) δ` and `k - 1 ≤ W^{τ'/2}`: `ℓ W^{τ'/2} ≤ δ` and
`(W^{τ'/2}/k)² ≤ δ/ℓ` (the two thresholds used for `STKcalDecay` at length `2` and for the
exponential). -/
private theorem DecayLoopA_real_geom {Wr ℓ δ τ' kk : ℝ} (hW : 0 < Wr) (hℓ : 0 < ℓ) (hδ0 : 0 ≤ δ)
    (hk : 2 ≤ kk) (hWk : kk - 1 ≤ Wr ^ (τ' / 2)) (hδ : ℓ * Wr ^ τ' ≤ (kk - 1) * δ) :
    ℓ * Wr ^ (τ' / 2) ≤ δ ∧ (Wr ^ (τ' / 2) / kk) ^ 2 ≤ δ / ℓ := by
  have hs : 0 < Wr ^ (τ' / 2) := Real.rpow_pos_of_pos hW _
  have h1 : Wr ^ τ' = Wr ^ (τ' / 2) * Wr ^ (τ' / 2) := by
    rw [← Real.rpow_add hW]; congr 1; ring
  have hk1 : 0 < kk - 1 := by linarith
  constructor
  · have h2 : ℓ * Wr ^ (τ' / 2) * (kk - 1) ≤ (kk - 1) * δ := by
      calc ℓ * Wr ^ (τ' / 2) * (kk - 1) ≤ ℓ * Wr ^ (τ' / 2) * Wr ^ (τ' / 2) := by gcongr
        _ = ℓ * Wr ^ τ' := by rw [h1]; ring
        _ ≤ _ := hδ
    have h3 : ℓ * Wr ^ (τ' / 2) * (kk - 1) ≤ δ * (kk - 1) := by linarith
    exact le_of_mul_le_mul_right h3 hk1
  · have hkk : 0 < kk := by linarith
    rw [div_pow, div_le_div_iff₀ (by positivity) hℓ, ← Real.rpow_natCast, ← Real.rpow_mul hW.le]
    have h4 : (τ' / 2) * ((2 : ℕ) : ℝ) = τ' := by push_cast; ring
    rw [h4]
    calc Wr ^ τ' * ℓ = ℓ * Wr ^ τ' := mul_comm _ _
      _ ≤ (kk - 1) * δ := hδ
      _ ≤ kk ^ 2 * δ := by
        apply mul_le_mul_of_nonneg_right _ hδ0
        nlinarith
      _ = δ * kk ^ 2 := mul_comm _ _

/-- `|a - b|_{ℓ¹} ≤ KLmaxDist ![a, b]`. -/
private theorem DecayLoopA_zdistD_le_KLmaxDist_two {d L : ℕ} [NeZero L] (a b : Zd d L) :
    zdistD d L (a - b) ≤ KLmaxDist d L (![a, b] : Fin 2 → Zd d L) :=
  Finset.le_sup (f := fun q : Fin 2 × Fin 2 =>
    zdistD d L ((![a, b] : Fin 2 → Zd d L) q.1 - (![a, b] : Fin 2 → Zd d L) q.2))
    (Finset.mem_univ ((0 : Fin 2), (1 : Fin 2)))

end Scales

/-! ## 4. The probabilistic step, `k ≥ 2` -/

section Main

variable {d : ℕ}

/-- **`stDecayLoopAt_holds` for `k ≥ 2`.**  The only random event is that of the decay input at the far
pair `c = c(σ,a)`; on its complement the deterministic chain `DecayLoopA_alg` gives
`(|𝓛| + |𝓛-𝒦|)_{u,σ,a} ≤ W^{-D'}`.  Parameters: `τ₁ = 1` for the input, `D = Q` (its `W^{-D}` term),
`STKcalDecay` at `(2, τ'/2, Q)` and `(k, τ', D'+1)` (`inst_stKcalDecay_admissible`). -/
private theorem DecayLoopA_main (hd : 3 ≤ d) (sz : Sizes d) {κ 𝔠 𝔡 C₀ : ℝ} {E u P : ℕ → ℝ}
    (hκ : 0 < κ) (hE : ∀ n, |E n| ≤ 2 - κ) (hA : sz.Admissible 𝔠 𝔡) (hC₀ : 0 ≤ C₀)
    (hu0 : ∀ n, 0 ≤ u n) (hu1 : ∀ n, u n < 1)
    (hP2 : ∀ᶠ n : ℕ in atTop, P n ≤ ((sz.size n : ℕ) : ℝ) ^ C₀)
    (hdec : ∀ D : ℝ, 0 < D →
      PrecPT sz (U := fun n => Unit × (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)))
        (fun n p ω => ‖Lloop sz n (E n) (u n) p.2.1 p.2.2 ω - STKloop sz n (E n) (u n) p.2.1 p.2.2‖)
        (fun n p _ => P n * STWB sz n (u n) (zdistInf d (sz.L n) (p.2.2 0 - p.2.2 1)) *
            Real.exp (-(((zdistInf d (sz.L n) (p.2.2 0 - p.2.2 1) : ℕ) : ℝ) /
              ellT (sz.L n) (sz.lam n) (u n)) ^ (1 / 2 : ℝ)) +
          ((sz.W n : ℕ) : ℝ) ^ (-D)))
    {k : ℕ} (hk : 2 ≤ k) {τ' : ℝ} (hτ' : 0 < τ') {D' : ℝ} (hD' : 0 < D') :
    PrecPT sz (U := fun n => Unit × (Fin k → Bool) × (Fin k → Zd d (sz.L n)))
      (fun n p ω =>
        (‖Lloop sz n (E n) (u n) p.2.1 p.2.2 ω‖ +
          ‖Lloop sz n (E n) (u n) p.2.1 p.2.2 ω - STKloop sz n (E n) (u n) p.2.1 p.2.2‖) *
        (if ellT (sz.L n) (sz.lam n) (u n) * ((sz.W n : ℕ) : ℝ) ^ τ' ≤ (STdiamInf p.2.2 : ℝ)
          then 1 else 0))
      (fun n _ _ => ((sz.W n : ℕ) : ℝ) ^ (-D')) := by
  obtain ⟨h𝔠, h𝔡, hN, hB, hWO⟩ := id hA
  -- constants
  obtain ⟨Γ, hΓ⟩ : ∃ Γ : ℝ, Γ = 2 / Real.sqrt κ := ⟨_, rfl⟩
  obtain ⟨A, hAdef⟩ : ∃ A : ℝ, A = 1 / 𝔠 := ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q : ℝ, Q = 2 * D' + A * (2 * ((k : ℝ) - 1) + 1 + C₀) + 1 := ⟨_, rfl⟩
  have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hsqκ : 0 < Real.sqrt κ := Real.sqrt_pos.mpr hκ
  have hΓ0 : 0 ≤ Γ := by rw [hΓ]; positivity
  have hA0 : 0 ≤ A := by rw [hAdef]; positivity
  have hQpos : 0 < Q := by
    have : 0 ≤ A * (2 * ((k : ℝ) - 1) + 1 + C₀) := mul_nonneg hA0 (by nlinarith)
    rw [hQ]; linarith
  -- choice of the far pair
  have hpair : ∀ (n : ℕ) (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)),
      ∃ c : Zd d (sz.L n) × Zd d (sz.L n),
        ((STdiamInf a : ℕ) : ℝ) ≤ ((k : ℝ) - 1) * (zdistInf d (sz.L n) (c.1 - c.2) : ℝ) ∧
        ∀ (H : Matrix (Vtx d (sz.L n) (sz.W n)) (Vtx d (sz.L n) (sz.W n)) ℂ) (z : ℂ) (η : ℝ),
          H.IsHermitian → 0 < η → η ≤ |z.im| →
          ‖loopL d (sz.L n) (sz.W n) H z (loopOf σ a)‖ ^ 2 ≤
            η⁻¹ ^ (2 * (k - 1)) *
              ‖loopL d (sz.L n) (sz.W n) H z ⟨[true, false], [c.1, c.2]⟩‖ :=
    fun n σ a => DecayLoopA_pair hk σ a
  choose cp hcp using hpair
  -- the pulled-back source
  have hpb : PrecPT sz (U := fun n => Unit × (Fin k → Bool) × (Fin k → Zd d (sz.L n)))
      (fun n p ω => ‖Lloop sz n (E n) (u n) ![true, false]
          ![(cp n p.2.1 p.2.2).1, (cp n p.2.1 p.2.2).2] ω -
        STKloop sz n (E n) (u n) ![true, false] ![(cp n p.2.1 p.2.2).1, (cp n p.2.1 p.2.2).2]‖)
      (fun n p _ => P n * STWB sz n (u n)
          (zdistInf d (sz.L n) ((cp n p.2.1 p.2.2).1 - (cp n p.2.1 p.2.2).2)) *
          Real.exp (-(((zdistInf d (sz.L n) ((cp n p.2.1 p.2.2).1 - (cp n p.2.1 p.2.2).2) : ℕ) : ℝ) /
            ellT (sz.L n) (sz.lam n) (u n)) ^ (1 / 2 : ℝ)) + ((sz.W n : ℕ) : ℝ) ^ (-Q)) := by
    intro τ₁ hτ₁ D₁ hD₁
    filter_upwards [hdec Q hQpos τ₁ hτ₁ D₁ hD₁] with n hn p
    exact hn ((), ![true, false], ![(cp n p.2.1 p.2.2).1, (cp n p.2.1 p.2.2).2])
  refine RBM.Ind.PerTimeCalc.PerTime.perTimeCalc_of_imp hpb ?_
  intro τ₀ hτ₀
  refine ⟨1, one_pos, ?_⟩
  -- eventual facts
  have hWtend : Tendsto (fun n => ((sz.W n : ℕ) : ℝ)) atTop atTop := by
    have h1 : Tendsto (fun n => ((sz.size n : ℕ) : ℝ) ^ 𝔠) atTop atTop :=
      (tendsto_rpow_atTop h𝔠).comp hN
    exact tendsto_atTop_mono' _ hB h1
  have hK2 := RBM.Gauss.KDecayInst.inst_stKcalDecay_admissible hd sz hA hκ (k := 2) (by norm_num)
    (τ := τ' / 2) (D := Q) (by linarith) hQpos
  have hKk := RBM.Gauss.KDecayInst.inst_stKcalDecay_admissible hd sz hA hκ (k := k) (by omega)
    (τ := τ') (D := D' + 1) hτ' (by linarith)
  have hexp := hWtend.eventually
    (DecayLoopA_exp_small (τ' := τ') hτ' (K := (k : ℝ)) (Q := Q) (by linarith) hQpos.le)
  have hW2 : ∀ᶠ n : ℕ in atTop, (2 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := hWtend.eventually_ge_atTop 2
  have hWΓ : ∀ᶠ n : ℕ in atTop,
      16 * Γ ^ (2 * (k - 1)) * (2 + 2) ≤ ((sz.W n : ℕ) : ℝ) := hWtend.eventually_ge_atTop _
  have hWk : ∀ᶠ n : ℕ in atTop, (k : ℝ) - 1 ≤ ((sz.W n : ℕ) : ℝ) ^ (τ' / 2) :=
    ((tendsto_rpow_atTop (by linarith : 0 < τ' / 2)).comp hWtend).eventually_ge_atTop _
  filter_upwards [hK2, hKk, hexp, hW2, hWΓ, hWk, hB, hWO, hP2] with n hK2n hKkn hexpn hW2n
    hWΓn hWkn hbwn hwo hP2n
  rintro ⟨⟨⟩, σ, a⟩ ω hlt
  by_contra hnot
  dsimp only at hlt hnot
  -- basic facts at the index n
  have hL3 : 3 ≤ sz.L n := sz.three_le_L n
  have hW1 : 1 ≤ sz.W n := sz.W_pos n
  have hW1r : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := by exact_mod_cast hW1
  have hWpos : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by linarith
  have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
  have hNpos : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
  have hL1r : (1 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ sz.L n)
  -- not far: trivial
  by_cases hfar : ellT (sz.L n) (sz.lam n) (u n) * ((sz.W n : ℕ) : ℝ) ^ τ' ≤ (STdiamInf a : ℝ)
  swap
  · simp only [hfar, ↓reduceIte, mul_zero] at hlt
    have : 0 < ((sz.size n : ℕ) : ℝ) ^ τ₀ * ((sz.W n : ℕ) : ℝ) ^ (-D') := by positivity
    linarith
  simp only [hfar, ↓reduceIte, mul_one] at hlt
  -- the scales: `g`, `1 - u`, `η`
  have hlam0 : 0 < sz.lam n :=
    lt_of_lt_of_le (Real.rpow_pos_of_pos hWpos _) hwo.1
  have hg1 : 1 ≤ sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d :=
    (Real.one_le_rpow hW1r (by linarith : (0 : ℝ) ≤ 2 * 𝔡)).trans
      (Sizes.lam_sq_mul_pow_ge sz n hwo.1)
  have hgW : (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ sz.lam n ^ 2 := by
    have hW0 : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) ^ d := by positivity
    calc (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ = (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * 1 := (mul_one _).symm
      _ ≤ (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d) := by gcongr
      _ = sz.lam n ^ 2 := by field_simp
  have hℓ1 : 1 ≤ ellT (sz.L n) (sz.lam n) (u n) := one_le_ellT hL1r
  have hℓpos : 0 < ellT (sz.L n) (sz.lam n) (u n) := by linarith
  have hWτ : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) ^ τ' := Real.one_le_rpow hW1r hτ'.le
  have hdiam : (STdiamInf a : ℝ) ≤ ((sz.L n : ℕ) : ℝ) / 2 := by
    have := DecayLoopA_two_mul_diam_le a
    have h2 : (2 : ℝ) * (STdiamInf a : ℝ) ≤ ((sz.L n : ℕ) : ℝ) := by exact_mod_cast this
    linarith
  have hℓL : ellT (sz.L n) (sz.lam n) (u n) < ((sz.L n : ℕ) : ℝ) := by
    have h3 : (3 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) := by exact_mod_cast hL3
    calc ellT (sz.L n) (sz.lam n) (u n)
        ≤ ellT (sz.L n) (sz.lam n) (u n) * ((sz.W n : ℕ) : ℝ) ^ τ' :=
          le_mul_of_one_le_right hℓpos.le hWτ
      _ ≤ (STdiamInf a : ℝ) := hfar
      _ ≤ ((sz.L n : ℕ) : ℝ) / 2 := hdiam
      _ < _ := by linarith
  have hNu : (((sz.size n : ℕ) : ℝ))⁻¹ ≤ 1 - u n :=
    DecayLoopA_one_sub_u (by omega) hL3 hW1 hlam0 hgW (hu1 n) hℓL
  have hv : 0 < 1 - u n := by linarith [hu1 n]
  have hN1u : 1 ≤ ((sz.size n : ℕ) : ℝ) * (1 - u n) := by
    have := mul_le_mul_of_nonneg_left hNu hNpos.le
    rwa [mul_inv_cancel₀ hNpos.ne'] at this
  have hμ : Real.sqrt κ / 2 ≤ (mE (E n)).im := DecayLoopA_mE_im_ge hκ (hE n)
  have hη : 0 < etaT (E n) (u n) := by
    have : 0 < (mE (E n)).im := lt_of_lt_of_le (by positivity) hμ
    exact mul_pos hv this
  have hηΓ : (etaT (E n) (u n))⁻¹ ≤ Γ * ((sz.size n : ℕ) : ℝ) := by
    have h1 : (1 - u n) * (Real.sqrt κ / 2) ≤ etaT (E n) (u n) :=
      mul_le_mul_of_nonneg_left hμ hv.le
    have h2 : (etaT (E n) (u n))⁻¹ ≤ ((1 - u n) * (Real.sqrt κ / 2))⁻¹ :=
      inv_anti₀ (by positivity) h1
    have h3 : ((1 - u n) * (Real.sqrt κ / 2))⁻¹ = Γ * (1 - u n)⁻¹ := by
      rw [hΓ]; field_simp
    have h4 : (1 - u n)⁻¹ ≤ ((sz.size n : ℕ) : ℝ) := by
      have := inv_anti₀ (by positivity) hNu
      rwa [inv_inv] at this
    calc (etaT (E n) (u n))⁻¹ ≤ ((1 - u n) * (Real.sqrt κ / 2))⁻¹ := h2
      _ = Γ * (1 - u n)⁻¹ := h3
      _ ≤ Γ * ((sz.size n : ℕ) : ℝ) := by gcongr
  have hMi : STWB sz n (u n) (zdistInf d (sz.L n) ((cp n σ a).1 - (cp n σ a).2)) ≤ 2 :=
    DecayLoopA_STWB_le sz n _ (hu1 n) hg1 hN1u
  -- the matrix and the far pair
  have hMh : (sz.seqHflow n (u n) ω).IsHermitian := Sizes.seqHflow_isHermitian sz n (u n) ω
  have hHh : (blockMat d (sz.L n) (sz.W n) (sz.seqHflow n (u n) ω)).IsHermitian :=
    hMh.submatrix _
  have hzim : etaT (E n) (u n) ≤ |(zt (E n) (u n)).im| := by
    rw [← etaT_eq_zt_im, abs_of_pos hη]
  obtain ⟨hcmax, hcb⟩ := hcp n σ a
  have hΛ := hcb (blockMat d (sz.L n) (sz.W n) (sz.seqHflow n (u n) ω)) (zt (E n) (u n))
    (etaT (E n) (u n)) hHh hη hzim
  have hδ : ellT (sz.L n) (sz.lam n) (u n) * ((sz.W n : ℕ) : ℝ) ^ τ' ≤
      ((k : ℝ) - 1) * (zdistInf d (sz.L n) ((cp n σ a).1 - (cp n σ a).2) : ℝ) :=
    hfar.trans hcmax
  obtain ⟨hfar2, hexarg⟩ := DecayLoopA_real_geom hWpos hℓpos (Nat.cast_nonneg _) hk2 hWkn hδ
  -- the bounds on the far pair
  have hKp : ‖STKloop sz n (E n) (u n) ![true, false]
      ![(cp n σ a).1, (cp n σ a).2]‖ ≤ ((sz.W n : ℕ) : ℝ) ^ (-Q) := by
    refine hK2n (E n) (hE n) (u n) (hu0 n) (hu1 n) ![true, false]
      ![(cp n σ a).1, (cp n σ a).2] (hfar2.trans ?_)
    exact_mod_cast (zdistInf_le_zdistD d (sz.L n) _).trans
      (DecayLoopA_zdistD_le_KLmaxDist_two (cp n σ a).1 (cp n σ a).2)
  have hKc : ‖STKloop sz n (E n) (u n) σ a‖ ≤ ((sz.W n : ℕ) : ℝ) ^ (-(D' + 1)) :=
    hKkn (E n) (hE n) (u n) (hu0 n) (hu1 n) σ a
      (hfar.trans (by exact_mod_cast DecayLoopA_diam_le_KLmaxDist a))
  have hex : Real.exp (-(((zdistInf d (sz.L n) ((cp n σ a).1 - (cp n σ a).2) : ℕ) : ℝ) /
        ellT (sz.L n) (sz.lam n) (u n)) ^ (1 / 2 : ℝ)) ≤ ((sz.W n : ℕ) : ℝ) ^ (-Q) := by
    have := hexpn _ hexarg
    rwa [Real.sqrt_eq_rpow] at this
  have hL2 : Lloop sz n (E n) (u n) ![true, false] ![(cp n σ a).1, (cp n σ a).2] ω =
      loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (sz.seqHflow n (u n) ω))
        (zt (E n) (u n)) ⟨[true, false], [(cp n σ a).1, (cp n σ a).2]⟩ := by
    refine (loopM_eq_loopL d (sz.L n) (sz.W n) _ _ ![true, false]
      ![(cp n σ a).1, (cp n σ a).2]).trans ?_
    simp [loopOf, List.ofFn_succ]
  have hLσ : Lloop sz n (E n) (u n) σ a ω =
      loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (sz.seqHflow n (u n) ω))
        (zt (E n) (u n)) (loopOf σ a) :=
    loopM_eq_loopL d (sz.L n) (sz.W n) _ _ σ a
  have hLp : ‖loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (sz.seqHflow n (u n) ω))
        (zt (E n) (u n)) ⟨[true, false], [(cp n σ a).1, (cp n σ a).2]⟩‖ ≤
      ‖STKloop sz n (E n) (u n) ![true, false] ![(cp n σ a).1, (cp n σ a).2]‖ +
        ‖Lloop sz n (E n) (u n) ![true, false] ![(cp n σ a).1, (cp n σ a).2] ω -
          STKloop sz n (E n) (u n) ![true, false] ![(cp n σ a).1, (cp n σ a).2]‖ := by
    rw [← hL2]
    exact norm_le_norm_add_norm_sub' _ _
  have hX := not_lt.mp hnot
  rw [Real.rpow_one] at hX
  have hNW : ((sz.size n : ℕ) : ℝ) ≤ ((sz.W n : ℕ) : ℝ) ^ A := by
    calc ((sz.size n : ℕ) : ℝ) = (((sz.size n : ℕ) : ℝ) ^ 𝔠) ^ (1 / 𝔠) := by
          rw [← Real.rpow_mul hNpos.le, mul_one_div_cancel h𝔠.ne', Real.rpow_one]
      _ ≤ ((sz.W n : ℕ) : ℝ) ^ (1 / 𝔠) := Real.rpow_le_rpow (by positivity) hbwn (by positivity)
      _ = ((sz.W n : ℕ) : ℝ) ^ A := by rw [hAdef]
  have key := DecayLoopA_alg (W := ((sz.W n : ℕ) : ℝ)) (N := ((sz.size n : ℕ) : ℝ)) (Γ := Γ)
    (Θ := 2) (A := A) (k := k) (D' := D') (C₀ := C₀) (Q := Q)
    (Λ := ‖Lloop sz n (E n) (u n) σ a ω‖) hk hC₀ hΓ0 (by norm_num) hW2n
    hWΓn hN1 hNW hQ (inv_nonneg.mpr hη.le) hηΓ (norm_nonneg _) (norm_nonneg _)
    (by rw [hLσ]; exact hΛ) hLp hKp hX hP2n hMi hex (DecayLoopA_STWB_nonneg sz n _ _)
    (Real.exp_pos _).le hKc
  have hlk : ‖Lloop sz n (E n) (u n) σ a ω - STKloop sz n (E n) (u n) σ a‖ ≤
      ‖Lloop sz n (E n) (u n) σ a ω‖ + ‖STKloop sz n (E n) (u n) σ a‖ := norm_sub_le _ _
  have hNτ : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ τ₀ := Real.one_le_rpow hN1 hτ₀.le
  have hWD : 0 < ((sz.W n : ℕ) : ℝ) ^ (-D') := Real.rpow_pos_of_pos hWpos _
  have hle : ((sz.W n : ℕ) : ℝ) ^ (-D') ≤ ((sz.size n : ℕ) : ℝ) ^ τ₀ * ((sz.W n : ℕ) : ℝ) ^ (-D') :=
    le_mul_of_one_le_left hWD.le hNτ
  have hLσ' : ‖loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (sz.seqHflow n (u n) ω))
        (zt (E n) (u n)) (loopOf σ a)‖ = ‖Lloop sz n (E n) (u n) σ a ω‖ := by rw [hLσ]
  linarith

end Main

/-! ## 5. The targets -/

section Targets

variable {d : ℕ}

/-- **Target 1: `lem_decayLoop` (`res_decayLK`) at a single time** (`3 ≤ d`, DECISIONS §36, because
`stKcalDecay_holds` needs it).  From the decay input at the time sequence `u` (prefactor `P` with
`1 ≤ P ≤ N^{C₀}` eventually): for every `k ≥ 1`, `τ', D' > 0`,
`(|𝓛| + |𝓛-𝒦|)_{u,σ,a} 1(ℓ_u W^{τ'} ≤ diam_∞ a) ≺ W^{-D'}` per time.  The lower bound `1 ≤ P` is not
used, and the pin has no hypothesis `0 ≤ C₀` (RBM2D has it): `C₀` is replaced by `max C₀ 0` inside
(`1 ≤ N`). -/
theorem stDecayLoopAt_holds (hd : 3 ≤ d) (sz : Sizes d) (κ 𝔠 𝔡 C₀ : ℝ) (E u P : ℕ → ℝ) :
    STDecayLoopAt sz κ 𝔠 𝔡 C₀ E u P := by
  intro hκ hE hA hu0 hu1 hP hdec k hk τ' hτ' D' hD'
  rcases Nat.lt_or_ge k 2 with hk2 | hk2
  · obtain rfl : k = 1 := by omega
    refine RBM.Green.perTimeDomAt_of_nonpos _ _ _ _ (fun n p ω => ?_) (fun n _ _ => ?_)
    · have hL : (1 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) := by
        have := sz.three_le_L n; exact_mod_cast (by omega : 1 ≤ sz.L n)
      have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
      have hpos : 0 < ellT (sz.L n) (sz.lam n) (u n) * ((sz.W n : ℕ) : ℝ) ^ τ' :=
        mul_pos (ellT_pos hL) (Real.rpow_pos_of_pos hW _)
      have hmax : (STdiamInf p.2.2 : ℝ) = 0 := by
        rw [DecayLoopA_diam_one]; simp
      have hnot : ¬ (ellT (sz.L n) (sz.lam n) (u n) * ((sz.W n : ℕ) : ℝ) ^ τ' ≤
          (STdiamInf p.2.2 : ℝ)) := by
        rw [hmax]; exact not_le.mpr hpos
      simp only [hnot, ↓reduceIte, mul_zero, le_refl]
    · exact (Real.rpow_pos_of_pos (by exact_mod_cast sz.W_pos n) _).le
  · refine DecayLoopA_main hd sz (C₀ := max C₀ 0) hκ hE hA (le_max_right _ _) hu0 hu1 ?_ hdec hk2
      hτ' hD'
    filter_upwards [hP] with n hn
    exact hn.2.trans (Real.rpow_le_rpow_of_exponent_le
      (by exact_mod_cast sz.one_le_size n) (le_max_left _ _))

/-- **Target 2: the window form from the Step-2 decay output** (the `d`-dimensional form of RBM2D
`decayLoopWindow`).  Along the flow `STFlow` (`E = lemE z`) and `0 ≤ s ≤ t ≤ lemT z`: from the
per-time `(Eq:Gdecay_w)`, `STStep2DecayPT Cd sz E s t` (prefactor
`((1-s)/(1-u))^{Cd} Bctl^{1/5}`), every section `u ∈ [s,t]` satisfies the hypotheses of
`stDecayLoopAt_holds` with `P_u' = max P_u 1` and `C₀ = max Cd 0 + 1`:
`1 ≤ (1-s)/(1-u) ≤ N` (`1 - u ≥ N^{-1+ε/2} ≥ N⁻¹` from `RangeCond`, `v3_premises_of_stFlow`),
`Bctl ≤ 2` (`DecayLoopA_STWB_le` at `K = 0`), so `P_u ≤ 2 N^{max Cd 0} ≤ N^{max Cd 0 + 1}`
(`N ≥ 2`).  The sections assemble by `perTime_timeIcc_of_forall_seq`. -/
theorem stDecayLoopPT_of_step2 (hd : 3 ≤ d) (sz : Sizes d) {κ ε 𝔠 𝔡 : ℝ} {z : ℕ → ℂ}
    (hκ : 0 < κ) (hε : 0 < ε) (hflow : STFlow sz κ ε 𝔠 𝔡 z) {s t : ℕ → ℝ}
    (hs : ∀ n, 0 ≤ s n) (hst : ∀ n, s n ≤ t n) (ht : ∀ n, t n ≤ lemT (z n)) (Cd : ℝ)
    (hD : STStep2DecayPT sz Cd (STflowE z) s t) : STDecayLoopPT sz (STflowE z) s t := by
  intro k hk τ' hτ' D' hD'
  have him : ∀ n, 0 < (z n).im := fun n =>
    lt_of_lt_of_le (Real.rpow_pos_of_pos (by exact_mod_cast sz.one_le_size n) _)
      (hflow.2 n).2.1
  refine RBM.Green.perTime_timeIcc_of_forall_seq sz.seqP sz.size hst
    (V := fun n => (Fin k → Bool) × (Fin k → Zd d (sz.L n)))
    (fun n => ⟨(fun _ => true, fun _ => 0)⟩)
    (fun n v q ω =>
      (‖Lloop sz n (STflowE z n) v q.1 q.2 ω‖ +
        ‖Lloop sz n (STflowE z n) v q.1 q.2 ω - STKloop sz n (STflowE z n) v q.1 q.2‖) *
      (if ellT (sz.L n) (sz.lam n) v * ((sz.W n : ℕ) : ℝ) ^ τ' ≤ (STdiamInf q.2 : ℝ)
        then 1 else 0))
    (fun n _ _ _ => ((sz.W n : ℕ) : ℝ) ^ (-D')) ?_
  intro u hu
  have hu0 : ∀ n, 0 ≤ u n := fun n => (hs n).trans (hu n).1
  have hut : ∀ n, u n ≤ lemT (z n) := fun n => (hu n).2.trans (ht n)
  have hu1 : ∀ n, u n < 1 := fun n => (hut n).trans_lt (lemT_lt_one (him n))
  have hE' : ∀ n, |STflowE z n| ≤ 2 - κ := fun n =>
    (abs_lemE_le (him n)).trans (hflow.2 n).1
  have hAdm := hflow.1
  obtain ⟨-, -, -, hrange⟩ := RBM.Green.v3_premises_of_stFlow sz hκ hε hflow hut
  obtain ⟨-, -, hNtend, -, hWO⟩ := hAdm
  -- the prefactor
  have hPev : ∀ᶠ n : ℕ in atTop, 1 ≤ max (((1 - s n) / (1 - u n)) ^ Cd * (sz.Bctl n (u n)) ^ (1 / 5 : ℝ)) 1 ∧
      max (((1 - s n) / (1 - u n)) ^ Cd * (sz.Bctl n (u n)) ^ (1 / 5 : ℝ)) 1 ≤
        ((sz.size n : ℕ) : ℝ) ^ (max Cd 0 + 1) := by
    filter_upwards [hrange, hNtend.eventually_ge_atTop 2, hWO] with n hr hN2 hwo
    have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by linarith
    have hNpos : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
    have hv : 0 < 1 - u n := by linarith [hu1 n]
    have hNu : (((sz.size n : ℕ) : ℝ))⁻¹ ≤ 1 - u n := by
      calc (((sz.size n : ℕ) : ℝ))⁻¹ = ((sz.size n : ℕ) : ℝ) ^ (-1 : ℝ) :=
            (Real.rpow_neg_one _).symm
        _ ≤ ((sz.size n : ℕ) : ℝ) ^ (-1 + ε / 2) :=
            Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
        _ ≤ 1 - u n := hr
    have hN1u : 1 ≤ ((sz.size n : ℕ) : ℝ) * (1 - u n) := by
      have := mul_le_mul_of_nonneg_left hNu hNpos.le
      rwa [mul_inv_cancel₀ hNpos.ne'] at this
    have hW1r : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
    have hg1 : 1 ≤ sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d :=
      (Real.one_le_rpow hW1r (by linarith [hflow.1.2.1] : (0 : ℝ) ≤ 2 * 𝔡)).trans
        (Sizes.lam_sq_mul_pow_ge sz n hwo.1)
    have hB2 : sz.Bctl n (u n) ≤ 2 := DecayLoopA_STWB_le sz n 0 (hu1 n) hg1 hN1u
    have hB0 : 0 ≤ sz.Bctl n (u n) := DecayLoopA_STWB_nonneg sz n _ 0
    have hB5 : (sz.Bctl n (u n)) ^ (1 / 5 : ℝ) ≤ 2 :=
      calc (sz.Bctl n (u n)) ^ (1 / 5 : ℝ) ≤ (2 : ℝ) ^ (1 / 5 : ℝ) :=
            Real.rpow_le_rpow hB0 hB2 (by norm_num)
        _ ≤ (2 : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
        _ = 2 := Real.rpow_one 2
    have hratio1 : 1 ≤ (1 - s n) / (1 - u n) := by
      rw [le_div_iff₀ hv]; linarith [(hu n).1]
    have hratioN : (1 - s n) / (1 - u n) ≤ ((sz.size n : ℕ) : ℝ) := by
      rw [div_le_iff₀ hv]
      linarith [hs n]
    have hpow : ((1 - s n) / (1 - u n)) ^ Cd ≤ ((sz.size n : ℕ) : ℝ) ^ (max Cd 0) :=
      calc ((1 - s n) / (1 - u n)) ^ Cd ≤ ((1 - s n) / (1 - u n)) ^ (max Cd 0) :=
            Real.rpow_le_rpow_of_exponent_le hratio1 (le_max_left _ _)
        _ ≤ ((sz.size n : ℕ) : ℝ) ^ (max Cd 0) :=
            Real.rpow_le_rpow (by linarith) hratioN (le_max_right _ _)
    have hpow0 : 0 ≤ ((1 - s n) / (1 - u n)) ^ Cd := Real.rpow_nonneg (by linarith) _
    have hNC : ((sz.size n : ℕ) : ℝ) ^ (max Cd 0) * ((sz.size n : ℕ) : ℝ) =
        ((sz.size n : ℕ) : ℝ) ^ (max Cd 0 + 1) := by
      rw [Real.rpow_add hNpos, Real.rpow_one]
    have h1N : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ (max Cd 0 + 1) :=
      Real.one_le_rpow hN1 (by have := le_max_right Cd 0; linarith)
    refine ⟨le_max_right _ _, max_le ?_ h1N⟩
    calc ((1 - s n) / (1 - u n)) ^ Cd * (sz.Bctl n (u n)) ^ (1 / 5 : ℝ)
        ≤ ((sz.size n : ℕ) : ℝ) ^ (max Cd 0) * 2 :=
          mul_le_mul hpow hB5 (Real.rpow_nonneg hB0 _) (by positivity)
      _ ≤ ((sz.size n : ℕ) : ℝ) ^ (max Cd 0) * ((sz.size n : ℕ) : ℝ) := by
          gcongr
      _ = _ := hNC
  -- the decay input at the section `u` with the prefactor `P' = max P_u 1`
  have hdec_u : ∀ D : ℝ, 0 < D →
      PrecPT sz (U := fun n => Unit × (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)))
        (fun n p ω => ‖Lloop sz n (STflowE z n) (u n) p.2.1 p.2.2 ω -
          STKloop sz n (STflowE z n) (u n) p.2.1 p.2.2‖)
        (fun n p _ =>
          (fun n => max (((1 - s n) / (1 - u n)) ^ Cd * (sz.Bctl n (u n)) ^ (1 / 5 : ℝ)) 1) n *
            STWB sz n (u n) (zdistInf d (sz.L n) (p.2.2 0 - p.2.2 1)) *
            Real.exp (-(((zdistInf d (sz.L n) (p.2.2 0 - p.2.2 1) : ℕ) : ℝ) /
              ellT (sz.L n) (sz.lam n) (u n)) ^ (1 / 2 : ℝ)) +
          ((sz.W n : ℕ) : ℝ) ^ (-D)) := by
    intro D hD0
    have h1 := RBM.Green.perSeq_of_perTime_timeIcc sz.seqP sz.size (s := s) (t := t)
      (V := fun n => (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)))
      (fun n => ⟨(fun _ => true, fun _ => 0)⟩)
      (fun n v q ω => ‖Lloop sz n (STflowE z n) v q.1 q.2 ω - STKloop sz n (STflowE z n) v q.1 q.2‖)
      (fun n v q _ => ((1 - s n) / (1 - v)) ^ Cd * (sz.Bctl n v) ^ (1 / 5 : ℝ) *
          STWB sz n v (zdistInf d (sz.L n) (q.2 0 - q.2 1)) *
          Real.exp (-(((zdistInf d (sz.L n) (q.2 0 - q.2 1) : ℕ) : ℝ) /
            ellT (sz.L n) (sz.lam n) v) ^ (1 / 2 : ℝ)) +
        ((sz.W n : ℕ) : ℝ) ^ (-D)) (hD D hD0) u hu
    refine RBM.Ind.PerTimeCalc.PerTime.perTimeCalc_of_imp h1 ?_
    intro τ₀ hτ₀
    refine ⟨τ₀, hτ₀, Filter.Eventually.of_forall ?_⟩
    rintro n ⟨⟨⟩, q⟩ ω hlt
    refine lt_of_le_of_lt (mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg (Nat.cast_nonneg _) _)) hlt
    have hP : ((1 - s n) / (1 - u n)) ^ Cd * (sz.Bctl n (u n)) ^ (1 / 5 : ℝ) ≤
        max (((1 - s n) / (1 - u n)) ^ Cd * (sz.Bctl n (u n)) ^ (1 / 5 : ℝ)) 1 := le_max_left _ _
    have hex0 : 0 ≤ Real.exp (-(((zdistInf d (sz.L n) (q.2 0 - q.2 1) : ℕ) : ℝ) /
        ellT (sz.L n) (sz.lam n) (u n)) ^ (1 / 2 : ℝ)) := (Real.exp_pos _).le
    have hS0 := DecayLoopA_STWB_nonneg sz n (u n) (zdistInf d (sz.L n) (q.2 0 - q.2 1))
    gcongr
  exact stDecayLoopAt_holds hd sz κ 𝔠 𝔡 (max Cd 0 + 1) (STflowE z) u
    (fun n => max (((1 - s n) / (1 - u n)) ^ Cd * (sz.Bctl n (u n)) ^ (1 / 5 : ℝ)) 1)
    hκ hE' hflow.1 hu0 hu1 hPev hdec_u k hk τ' hτ' D' hD'

end Targets


end RBM.Gauss.Sizes

/-! ## 6. Compiled nonempty instances (`d = 3`)

The size sequence is the merged preflight sequence `sz0` (`L = 4(n+1)`, `W = (2(n+1))^5`,
`lam = (2(n+1))^{-6}`, `Admissible (1/6) (1/10)` = `sz0_admissible`) and the flow of the merged
instance `z0` (`flow_z0`).  The decay input (`STStep2DecayPT`-shaped) is another gate's output
(the Step 2 chain) and stays a hypothesis of the examples; every deterministic hypothesis is
discharged.  `sz0_far_nonempty` shows that the indicator `1(ℓ_u W^{τ'} ≤ diam_∞ a)` is not
identically `0` at the data of the first example, for every `n`. -/

namespace RBM.Gauss.DecayLoopAInst

open Filter RBM RBM.Path RBM.Gauss RBM.Gauss.Sizes RBM.Gauss.SizesInst
  RBM.Gauss.InductionDefsInst

/-- **The far set is nonempty at the instance**: at `u = 1/2` (`ℓ_u = 1`), `τ' = 1/10`, for every `n`
there is a label vector `a = (0, 0, L/2·(1,1,1))` with `ℓ_u W^{τ'} ≤ diam_∞ a`
(`W^{1/10} = (2(n+1))^{1/2} ≤ 2(n+1) = L/2`). -/
theorem sz0_far_nonempty (n : ℕ) :
    ∃ a : Fin 3 → Zd 3 (sz0.L n),
      ellT (sz0.L n) (sz0.lam n) (1 / 2) * ((sz0.W n : ℕ) : ℝ) ^ (1 / 10 : ℝ) ≤
        (STdiamInf a : ℝ) := by
  have hx : (2 : ℝ) ≤ 2 * ((n : ℝ) + 1) := by
    have := Nat.cast_nonneg (α := ℝ) n; linarith
  have hx0 : (0 : ℝ) < 2 * ((n : ℝ) + 1) := by linarith
  -- `ℓ_{1/2} ≤ 1`
  have hℓ : ellT (sz0.L n) (sz0.lam n) (1 / 2) ≤ 1 := by
    have hg : sz0.lam n ≤ 1 / 64 := by
      have h6 : (64 : ℝ) ≤ (2 * ((n : ℝ) + 1)) ^ 6 := by
        calc (64 : ℝ) = 2 ^ 6 := by norm_num
          _ ≤ (2 * ((n : ℝ) + 1)) ^ 6 := pow_le_pow_left₀ (by norm_num) hx 6
      change ((2 * ((n : ℝ) + 1)) ^ 6)⁻¹ ≤ 1 / 64
      rw [one_div]; exact inv_anti₀ (by norm_num) h6
    have hs : (1 / 2 : ℝ) ≤ Real.sqrt |1 - (1 / 2 : ℝ)| := by
      rw [show |1 - (1 / 2 : ℝ)| = 1 / 2 by norm_num]
      refine Real.le_sqrt_of_sq_le (by norm_num)
    have hq : sz0.lam n / Real.sqrt |1 - (1 / 2 : ℝ)| ≤ 1 := by
      have hg0 : 0 ≤ sz0.lam n := by
        change 0 ≤ ((2 * ((n : ℝ) + 1)) ^ 6)⁻¹
        positivity
      rw [div_le_one (by linarith)]
      linarith
    calc ellT (sz0.L n) (sz0.lam n) (1 / 2)
        ≤ max (sz0.lam n / Real.sqrt |1 - (1 / 2 : ℝ)|) 1 := min_le_left _ _
      _ = 1 := max_eq_right hq
  -- `W^{1/10} ≤ L/2`
  have hW : ((sz0.W n : ℕ) : ℝ) ^ (1 / 10 : ℝ) ≤ 2 * ((n : ℝ) + 1) := by
    have hWe : ((sz0.W n : ℕ) : ℝ) = (2 * ((n : ℝ) + 1)) ^ 5 := by simp [sz0]
    rw [hWe, ← Real.rpow_natCast (2 * ((n : ℝ) + 1)) 5, ← Real.rpow_mul hx0.le]
    calc (2 * ((n : ℝ) + 1)) ^ (((5 : ℕ) : ℝ) * (1 / 10 : ℝ))
        ≤ (2 * ((n : ℝ) + 1)) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
      _ = 2 * ((n : ℝ) + 1) := Real.rpow_one _
  -- the label vector
  have hL : sz0.L n = 4 * (n + 1) := rfl
  obtain ⟨a, ha⟩ : ∃ a : Fin 3 → Zd 3 (sz0.L n),
      a = ![0, 0, fun _ => ((2 * (n + 1) : ℕ) : ZMod (sz0.L n))] := ⟨_, rfl⟩
  refine ⟨a, ?_⟩
  have hdiam : 2 * (n + 1) ≤ STdiamInf a := by
    unfold STdiamInf
    refine le_trans ?_ (Finset.le_sup (f := fun p : Fin 3 × Fin 3 => zdistInf 3 (sz0.L n)
      (a p.1 - a p.2)) (Finset.mem_univ ((2 : Fin 3), (0 : Fin 3))))
    unfold zdistInf
    refine le_trans ?_ (Finset.le_sup (f := fun i : Fin 3 => zdist (sz0.L n)
      ((a 2 - a 0) i)) (Finset.mem_univ (0 : Fin 3)))
    have hv : ((2 * (n + 1) : ℕ) : ZMod (sz0.L n)).val = 2 * (n + 1) := by
      rw [ZMod.val_natCast_of_lt]
      rw [hL]; omega
    have h20 : (a 2 - a 0) 0 = ((2 * (n + 1) : ℕ) : ZMod (sz0.L n)) := by
      rw [ha]; simp
    rw [h20]
    simp only [zdist, hv, hL]
    omega
  have hdiamR : (2 * ((n : ℝ) + 1)) ≤ (STdiamInf a : ℝ) := by
    have h1 : ((2 * (n + 1) : ℕ) : ℝ) ≤ (STdiamInf a : ℝ) := by exact_mod_cast hdiam
    have h2 : ((2 * (n + 1) : ℕ) : ℝ) = 2 * ((n : ℝ) + 1) := by push_cast; ring
    linarith
  have hWnn : 0 ≤ ((sz0.W n : ℕ) : ℝ) ^ (1 / 10 : ℝ) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  calc ellT (sz0.L n) (sz0.lam n) (1 / 2) * ((sz0.W n : ℕ) : ℝ) ^ (1 / 10 : ℝ)
      ≤ 1 * ((sz0.W n : ℕ) : ℝ) ^ (1 / 10 : ℝ) := by gcongr
    _ ≤ _ := by linarith

/-- **Target 1 at `d = 3`** on `sz0`: `κ = 1`, `𝔠 = 1/6`, `𝔡 = 1/10`, `E ≡ 0`, `u ≡ 1/2` (`ℓ_u = 1`),
`P ≡ 1`, `C₀ = 0`, loop length `k = 3`, `τ' = 1/10`, `D' = 1`.  Every deterministic hypothesis
(`0 < κ`, `|E| ≤ 2 - κ`, `Admissible`, `0 ≤ u < 1`, `1 ≤ P ≤ N^0`) is discharged; the decay input
`hdec` is the Step-2 output (another gate) and stays a hypothesis. -/
example (hdec : ∀ D : ℝ, 0 < D →
      PrecPT sz0 (U := fun n => Unit × (Fin 2 → Bool) × (Fin 2 → Zd 3 (sz0.L n)))
        (fun n p ω => ‖Lloop sz0 n 0 (1 / 2) p.2.1 p.2.2 ω - STKloop sz0 n 0 (1 / 2) p.2.1 p.2.2‖)
        (fun n p _ => 1 * STWB sz0 n (1 / 2) (zdistInf 3 (sz0.L n) (p.2.2 0 - p.2.2 1)) *
            Real.exp (-(((zdistInf 3 (sz0.L n) (p.2.2 0 - p.2.2 1) : ℕ) : ℝ) /
              ellT (sz0.L n) (sz0.lam n) (1 / 2)) ^ (1 / 2 : ℝ)) +
          ((sz0.W n : ℕ) : ℝ) ^ (-D))) :
    PrecPT sz0 (U := fun n => Unit × (Fin 3 → Bool) × (Fin 3 → Zd 3 (sz0.L n)))
      (fun n p ω =>
        (‖Lloop sz0 n 0 (1 / 2) p.2.1 p.2.2 ω‖ +
          ‖Lloop sz0 n 0 (1 / 2) p.2.1 p.2.2 ω - STKloop sz0 n 0 (1 / 2) p.2.1 p.2.2‖) *
        (if ellT (sz0.L n) (sz0.lam n) (1 / 2) * ((sz0.W n : ℕ) : ℝ) ^ (1 / 10 : ℝ) ≤
            (STdiamInf p.2.2 : ℝ) then 1 else 0))
      (fun n _ _ => ((sz0.W n : ℕ) : ℝ) ^ (-(1 : ℝ))) :=
  stDecayLoopAt_holds (d := 3) (by norm_num) sz0 1 (1 / 6) (1 / 10) 0 (fun _ => 0)
    (fun _ => 1 / 2) (fun _ => 1) (by norm_num) (fun n => by norm_num) sz0_admissible
    (fun _ => by norm_num) (fun _ => by norm_num)
    (Filter.Eventually.of_forall fun n => ⟨le_rfl, by simp⟩) hdec 3 (by norm_num) (1 / 10)
    (by norm_num) 1 (by norm_num)

/-- **Target 2 at `d = 3`** on the merged flow instance (`sz0`, `z0`, `flow_z0`, `κ = ε = 𝔡 = 1/10`,
`𝔠 = 1/6`), window `[0, 1/16]` (`1/16 ≤ lemT z0`), arbitrary `Cd`; the per-time Step-2 decay
`STStep2DecayPT` stays the hypothesis. -/
example (Cd : ℝ) (hD : STStep2DecayPT sz0 Cd (STflowE z0) sInst tInst) :
    STDecayLoopPT sz0 (STflowE z0) sInst tInst :=
  stDecayLoopPT_of_step2 (d := 3) (by norm_num) sz0 (by norm_num) (by norm_num) flow_z0
    (fun _ => le_rfl) (fun n => by simp only [sInst, tInst]; norm_num)
    (fun n => sixteenth_le_lemT n) Cd hD

/-- **Target 2, applied at `k = 3`, `τ' = 1/10`, `D' = 1`.** -/
example (Cd : ℝ) (hD : STStep2DecayPT sz0 Cd (STflowE z0) sInst tInst) :
    PrecPT sz0 (U := fun n => TimeIcc sInst tInst n × (Fin 3 → Bool) × (Fin 3 → Zd 3 (sz0.L n)))
      (fun n p ω =>
        (‖Lloop sz0 n (STflowE z0 n) (p.1 : ℝ) p.2.1 p.2.2 ω‖ +
          ‖Lloop sz0 n (STflowE z0 n) (p.1 : ℝ) p.2.1 p.2.2 ω -
            STKloop sz0 n (STflowE z0 n) (p.1 : ℝ) p.2.1 p.2.2‖) *
        (if ellT (sz0.L n) (sz0.lam n) (p.1 : ℝ) * ((sz0.W n : ℕ) : ℝ) ^ (1 / 10 : ℝ) ≤
            (STdiamInf p.2.2 : ℝ) then 1 else 0))
      (fun n _ _ => ((sz0.W n : ℕ) : ℝ) ^ (-(1 : ℝ))) := by
  have h : STDecayLoopPT sz0 (STflowE z0) sInst tInst :=
    stDecayLoopPT_of_step2 (d := 3) (by norm_num) sz0 (by norm_num) (by norm_num) flow_z0
      (fun _ => le_rfl) (fun n => by simp only [sInst, tInst]; norm_num)
      (fun n => sixteenth_le_lemT n) Cd hD
  exact h 3 (by norm_num) (1 / 10) (by norm_num) 1 (by norm_num)

end RBM.Gauss.DecayLoopAInst

end
