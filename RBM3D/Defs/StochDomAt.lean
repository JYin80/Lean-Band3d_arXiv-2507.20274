/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Gauss.FineModel
import RBM3D.Defs.StochDom

/-!
# The one `≺` of the chain: stochastic domination at the scale `N = (W L)^d`

Ticket T2012 (MD-2).  `(stoch_domination)` of arXiv:2507.20274 (`1_2:227–231`) and the `w.h.p.`
convention (`1_2:223`) along a size sequence `size : ℕ → ℕ`, the scale being
`N = size l = (W L)^d` (`sz.size`, `RBM3D/Defs/Sizes.lean`).  The merged `RBM.StochDom`,
`RBM.HighProb` (`RBM3D/Defs/StochDom.lean`) are the case `size = id`
(`stochDom_iff_at_id`, `highProb_iff_at_id`).

## Contents

* Section 7 (**pinned**, copied verbatim with proofs from the compiled probe
  `RBM3D/Probe/T2002Vocab.lean` at `5d2a4a8`, lines 795–935, without `LocalLawPT`): `badSetAt`,
  `StochDomAt`, `HighProbAt`, `TimeIcc`, `PerTimeDomAt`, and `Sizes.Prec`, `PrecPT`, `Whp` with
  `one_le_size`, `prec_of_le`, `precPT_of_le`, `Prec.whp`.
* Section 8 (**ported** from `RBM2D/Path/PerTime.lean` at `c9a24cf`): the per-time interface and
  the grid union bound (`perTimeOfStochDomAt`, `perTimeDomAt_iff_forall_section`,
  `stochDomAt_of_perTimeDomAt`, `highProbAt_iInter`).
* Section 9: the calculus of `StochDomAt` and `HighProbAt` at the scale `size`.  RBM2D proves this
  calculus only for the index scale (`RBM2D/Defs/StochDom.lean`, `StochDom.*`, merged here as
  `RBM3D/Defs/StochDom.lean`); the proofs below are those proofs with `N := size l`.  Every
  lemma that uses `2 N^{-(D+1)} ≤ N^{-D}`, `N^C ≥ 1` or `C ≤ N^e` carries `Tendsto size atTop
  atTop` (for `sz : Sizes d`: `Sizes.tendsto_size`).  The same section has the absorption
  section (`StochDomAt.of_add_le`, `of_highProbAt_add_rpow_neg`) and `NormStochDomAt`.
* Section 10: compiled instances at the MD-1 size sequence `RBM.Gauss.SizesInst.sz0`.

`RBM2D` is read-only; every port is cited with its line at `c9a24cf`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal

/-! ## 7. The one `≺` of the chain: scale `N = (W L)^d` -/

namespace RBM

section Prec

variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {U : ℕ → Type*}

/-- The failure event `{∃ u, ξ(l,u) > size(l)^τ ζ(l,u)}` of `(stoch_domination)` (`1_2:229`).
`RBM2D/Defs/StochDom.lean:98`. -/
def badSetAt (size : ℕ → ℕ) (ξ ζ : ∀ l, U l → Ω → ℝ) (τ : ℝ) (l : ℕ) : Set Ω :=
  {ω | ∃ u, (size l : ℝ) ^ τ * ζ l u ω < ξ l u ω}

/-- **`(stoch_domination)`** (`1_2:227–231`) along the scale `size l`: for all `τ, D > 0`,
eventually in `l`, `P(∃ u, ξ(l,u) > size(l)^τ ζ(l,u)) ≤ size(l)^{-D}`; the union over `u` is
inside `P`, as in the paper.  `RBM2D/Defs/StochDom.lean:103`.  The merged `RBM.StochDom` uses the
family index `N` as scale and is kept for families indexed by the matrix size (deterministic
`UnifDetDom` bridge). -/
def StochDomAt (size : ℕ → ℕ) (ξ ζ : ∀ l, U l → Ω → ℝ) : Prop :=
  ∀ τ > (0 : ℝ), ∀ D > (0 : ℝ), ∀ᶠ l : ℕ in atTop,
    P (badSetAt size ξ ζ τ l) ≤ ENNReal.ofReal ((size l : ℝ) ^ (-D))

/-- The merged `RBM.StochDom` (family index `N` as the scale) is `StochDomAt` at `size = id`: there
is one `≺`, and the scale `N` is the matrix size. -/
theorem stochDom_iff_at_id (ξ ζ : ∀ N, U N → Ω → ℝ) : StochDom P ξ ζ ↔ StochDomAt P id ξ ζ :=
  Iff.rfl

end Prec

end RBM

namespace RBM.Gauss

section Whp

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **`w.h.p.`** (`1_2:223`) along the scale `size l`: `P(Ξ(l)ᶜ) ≤ size(l)^{-D}` eventually, for
every `D > 0`.  `RBM2D/Gauss/Domination.lean:463`. -/
def HighProbAt (P : Measure Ω) (size : ℕ → ℕ) (Ξ : ℕ → Set Ω) : Prop :=
  ∀ D > (0 : ℝ), ∀ᶠ l : ℕ in atTop, P (Ξ l)ᶜ ≤ ENNReal.ofReal ((size l : ℝ) ^ (-D))

/-- The merged `RBM.HighProb` is `HighProbAt` at `size = id`. -/
theorem highProb_iff_at_id (P : Measure Ω) (Ξ : ℕ → Set Ω) :
    HighProb P Ξ ↔ HighProbAt P id Ξ := Iff.rfl

end Whp

end RBM.Gauss

namespace RBM.Path

section PerTime

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The times `u ∈ [s_n, t_n]` of the flow `(MBM)` (`1_2:686`).  `RBM2D/Path/PerTime.lean:40`. -/
abbrev TimeIcc (s t : ℕ → ℝ) (n : ℕ) : Type := ↥(Set.Icc (s n) (t n))

/-- **Per-time `≺`** (`(stoch_domination)`, `1_2:227–231`, with DECISIONS §7: single-time law
elsewhere than at stopping times): the union over the parameter `u` is *outside* the probability, so
the statement depends only on the one-parameter marginals.  `RBM2D/Path/PerTime.lean:48`. -/
def PerTimeDomAt (P : Measure Ω) (size : ℕ → ℕ) {U : ℕ → Type*} (ξ ζ : ∀ l, U l → Ω → ℝ) : Prop :=
  ∀ τ > (0 : ℝ), ∀ D > (0 : ℝ), ∀ᶠ l : ℕ in atTop, ∀ u : U l,
    P {ω | (size l : ℝ) ^ τ * ζ l u ω < ξ l u ω} ≤ ENNReal.ofReal ((size l : ℝ) ^ (-D))

end PerTime

end RBM.Path

namespace RBM.Gauss.Sizes

variable {d : ℕ} (sz : Sizes d) {U : ℕ → Type*}

/-- **`ξ ≺ ζ` of the chain** (`(stoch_domination)`, `1_2:227–231`): `StochDomAt` for the model
measure `seqP sz` and the **one scale** `sz.size n = (W n L n)^d`.  Every stochastic and assembly
pin states `≺` through `Prec`, `PrecPT`, `PrecGrid` and `Whp`, never through another scale
(TEAM §9.8; the paper's `W^τ` converts by `W_rpow_le`, `size_rpow_le_W_rpow`). -/
def Prec (ξ ζ : ∀ n, U n → SeqΩ sz → ℝ) : Prop := StochDomAt (seqP sz) sz.size ξ ζ

/-- Per-time `≺` (`1_2:227–231`; union over `u` outside `P`) on the model measure at the scale
`sz.size`. -/
def PrecPT (ξ ζ : ∀ n, U n → SeqΩ sz → ℝ) : Prop := Path.PerTimeDomAt (seqP sz) sz.size ξ ζ

/-- `w.h.p.` (`1_2:223`) on the model measure at the scale `sz.size`. -/
def Whp (Ξ : ℕ → Set (SeqΩ sz)) : Prop := HighProbAt (seqP sz) sz.size Ξ

theorem one_le_size (n : ℕ) : 1 ≤ sz.size n := by
  have hW := sz.W_pos n
  have hL : 0 < sz.L n := by have := sz.three_le_L n; omega
  exact Nat.one_le_pow _ _ (Nat.mul_pos hW hL)

/-- Deterministic domination implies `≺` (the instance of the pin used in section 9). -/
theorem prec_of_le {ξ ζ : ∀ n, U n → SeqΩ sz → ℝ} (hζ : ∀ n u ω, 0 ≤ ζ n u ω)
    (hle : ∀ n u ω, ξ n u ω ≤ ζ n u ω) : sz.Prec ξ ζ := by
  intro τ hτ D _
  refine Eventually.of_forall fun n => ?_
  have h1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ τ :=
    Real.one_le_rpow (by exact_mod_cast sz.one_le_size n) hτ.le
  have hempty : badSetAt (sz.size) ξ ζ τ n = ∅ := by
    ext ω
    simp only [badSetAt, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_exists, not_lt]
    intro u
    nlinarith [hle n u ω, hζ n u ω]
  rw [hempty, measure_empty]
  exact zero_le

/-- Deterministic domination implies the per-time `≺`. -/
theorem precPT_of_le {ξ ζ : ∀ n, U n → SeqΩ sz → ℝ} (hζ : ∀ n u ω, 0 ≤ ζ n u ω)
    (hle : ∀ n u ω, ξ n u ω ≤ ζ n u ω) : sz.PrecPT ξ ζ := by
  intro τ hτ D _
  refine Eventually.of_forall fun n u => ?_
  have h1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ τ :=
    Real.one_le_rpow (by exact_mod_cast sz.one_le_size n) hτ.le
  have hempty : {ω | ((sz.size n : ℕ) : ℝ) ^ τ * ζ n u ω < ξ n u ω} = ∅ := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_lt]
    nlinarith [hle n u ω, hζ n u ω]
  rw [hempty, measure_empty]
  exact zero_le

/-- `ξ ≺ ζ` gives the `w.h.p.` event `{∀ u, ξ ≤ N^τ ζ}`. -/
theorem Prec.whp {ξ ζ : ∀ n, U n → SeqΩ sz → ℝ} (h : sz.Prec ξ ζ) {τ : ℝ} (hτ : 0 < τ) :
    sz.Whp (fun n => {ω | ∀ u, ξ n u ω ≤ ((sz.size n : ℕ) : ℝ) ^ τ * ζ n u ω}) := by
  intro D hD
  filter_upwards [h τ hτ D hD] with n hn
  refine le_trans (le_of_eq ?_) hn
  congr 1
  ext ω
  simp [badSetAt]

end RBM.Gauss.Sizes

/-! ## 8. The per-time interface and the grid union bound (port of `RBM2D/Path/PerTime.lean`)

Ported from `RBM2D/Path/PerTime.lean` at `c9a24cf` (lines cited per declaration); the definitions
`TimeIcc`, `PerTimeDomAt` of that file are the pinned ones of section 7.  None of these
needs `1 ≤ size l`: the exponent identity `x^C x^{-(D+C)} = x^{-D}` holds for every `x ≥ 0` when
`D ≠ 0` (`Real.rpow_add'`).  The proofs are verbatim. -/

namespace RBM.Path

open RBM.Gauss

/-- **Pin (uniform ⇒ per time)**: `StochDomAt` implies `PerTimeDomAt` (each event is contained
in the union).  `RBM2D/Path/PerTime.lean:55`. -/
def PerTimeOfStochDomAt : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (size : ℕ → ℕ) {U : ℕ → Type}
    (ξ ζ : ∀ l, U l → Ω → ℝ), StochDomAt P size ξ ζ → PerTimeDomAt P size ξ ζ

/-- **Target 1 (pinned in RBM2D).** Each per-time event is contained in `badSetAt`.
`RBM2D/Path/PerTime.lean:60`. -/
theorem perTimeOfStochDomAt : PerTimeOfStochDomAt := by
  intro Ω _ P size U ξ ζ h τ hτ D hD
  filter_upwards [h τ hτ D hD] with l hl u
  refine le_trans (measure_mono ?_) hl
  intro ω hω
  exact ⟨u, hω⟩

/-- `x^C · x^{-(D+C)} = x^{-D}` for every `x ≥ 0` and `D ≠ 0` (no `1 ≤ x` needed).
`RBM2D/Path/PerTime.lean:68`. -/
private theorem rpow_mul_rpow_neg_add_of_nonneg {x : ℝ} (hx : 0 ≤ x) (C D : ℝ) (hD : D ≠ 0) :
    x ^ C * x ^ (-(D + C)) = x ^ (-D) := by
  rw [← Real.rpow_add' hx (by rw [show C + -(D + C) = -D by ring]; exact neg_ne_zero.mpr hD)]
  congr 1; ring

/-- **Target 2 (per-sequence equivalence).** For nonempty parameter sets, the per-time bound
holds iff `StochDomAt` holds along every section `u : ∀ l, U l` (one-parameter `Unit` family).
The "⇐" direction picks, at each `l`, a bad parameter when one exists (classical choice); no
measurability is used.  `RBM2D/Path/PerTime.lean:77`. -/
theorem perTimeDomAt_iff_forall_section {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (size : ℕ → ℕ) {U : ℕ → Type*} (hU : ∀ l, Nonempty (U l)) (ξ ζ : ∀ l, U l → Ω → ℝ) :
    PerTimeDomAt P size ξ ζ ↔
      ∀ u : ∀ l, U l,
        StochDomAt P size (fun l (_ : Unit) ω => ξ l (u l) ω)
          (fun l (_ : Unit) ω => ζ l (u l) ω) := by
  constructor
  · intro h u τ hτ D hD
    filter_upwards [h τ hτ D hD] with l hl
    refine le_trans (measure_mono ?_) (hl (u l))
    rintro ω ⟨_, hω⟩
    exact hω
  · intro h τ hτ D hD
    by_contra hne
    rw [Filter.not_eventually] at hne
    classical
    let bad : ∀ l, U l → Prop := fun l v =>
      ENNReal.ofReal ((size l : ℝ) ^ (-D)) < P {ω | (size l : ℝ) ^ τ * ζ l v ω < ξ l v ω}
    let u : ∀ l, U l := fun l =>
      if hb : ∃ v, bad l v then hb.choose else Classical.choice (hU l)
    have hfreq : ∃ᶠ l in atTop, ∃ v, bad l v := by
      refine hne.mono fun l hl => ?_
      push Not at hl
      exact hl
    obtain ⟨l, ⟨v, hv⟩, hl⟩ := (hfreq.and_eventually (h u τ hτ D hD)).exists
    have hb : ∃ v, bad l v := ⟨v, hv⟩
    have hul : bad l (u l) := by
      simp only [u, hb, dite_true]
      exact hb.choose_spec
    refine absurd hl (not_le.mpr (lt_of_lt_of_le hul (measure_mono ?_)))
    intro ω hω
    exact ⟨(), hω⟩

/-- **Target 3 (grid union bound, uniform form).** If `#U(l) ≤ size(l)^C` eventually, the
per-time bound implies the uniform bound `StochDomAt` (the union moves inside `P`).
`RBM2D/Path/PerTime.lean:112`. -/
theorem stochDomAt_of_perTimeDomAt {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (size : ℕ → ℕ) {U : ℕ → Type*} [∀ l, Fintype (U l)] {ξ ζ : ∀ l, U l → Ω → ℝ} {C : ℝ}
    (hC0 : 0 ≤ C)
    (hC : ∀ᶠ l : ℕ in atTop, (Fintype.card (U l) : ℝ) ≤ (size l : ℝ) ^ C)
    (h : PerTimeDomAt P size ξ ζ) :
    StochDomAt P size ξ ζ := by
  intro τ hτ D hD
  filter_upwards [hC, h τ hτ (D + C) (by linarith)] with l hcard hl
  have hs : (0 : ℝ) ≤ (size l : ℝ) := Nat.cast_nonneg _
  have hp : (0 : ℝ) ≤ (size l : ℝ) ^ (-(D + C)) := Real.rpow_nonneg hs _
  have hset : badSetAt size ξ ζ τ l =
      ⋃ u, {ω | (size l : ℝ) ^ τ * ζ l u ω < ξ l u ω} := by
    ext ω; simp [badSetAt]
  calc P (badSetAt size ξ ζ τ l)
      = P (⋃ u, {ω | (size l : ℝ) ^ τ * ζ l u ω < ξ l u ω}) := by rw [hset]
    _ ≤ ∑ u, P {ω | (size l : ℝ) ^ τ * ζ l u ω < ξ l u ω} := measure_iUnion_fintype_le P _
    _ ≤ ∑ _u : U l, ENNReal.ofReal ((size l : ℝ) ^ (-(D + C))) :=
        Finset.sum_le_sum fun u _ => hl u
    _ = ENNReal.ofReal (Fintype.card (U l) * (size l : ℝ) ^ (-(D + C))) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal ((size l : ℝ) ^ C * (size l : ℝ) ^ (-(D + C))) :=
        ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hcard hp)
    _ = ENNReal.ofReal ((size l : ℝ) ^ (-D)) := by
        rw [rpow_mul_rpow_neg_add_of_nonneg hs C D hD.ne']

/-- **Target 4 (grid union bound, event form).** The `size`-indexed analogue of
`RBM.HighProb.biInter`: polynomially many (in `size l`) events that each hold with high
probability, uniformly in `k`, hold simultaneously with high probability.
`RBM2D/Path/PerTime.lean:141`. -/
theorem highProbAt_iInter {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (size : ℕ → ℕ)
    {K : ℕ → Type*} [∀ l, Fintype (K l)] {Ξ : ∀ l, K l → Set Ω} {C : ℝ}
    (hC0 : 0 ≤ C)
    (hC : ∀ᶠ l : ℕ in atTop, (Fintype.card (K l) : ℝ) ≤ (size l : ℝ) ^ C)
    (h : ∀ D > (0 : ℝ), ∀ᶠ l : ℕ in atTop, ∀ k,
      P (Ξ l k)ᶜ ≤ ENNReal.ofReal ((size l : ℝ) ^ (-D))) :
    HighProbAt P size (fun l => ⋂ k, Ξ l k) := by
  intro D hD
  filter_upwards [hC, h (D + C) (by linarith)] with l hcard hl
  have hs : (0 : ℝ) ≤ (size l : ℝ) := Nat.cast_nonneg _
  have hp : (0 : ℝ) ≤ (size l : ℝ) ^ (-(D + C)) := Real.rpow_nonneg hs _
  calc P (⋂ k, Ξ l k)ᶜ = P (⋃ k, (Ξ l k)ᶜ) := by rw [Set.compl_iInter]
    _ ≤ ∑ k, P (Ξ l k)ᶜ := measure_iUnion_fintype_le P _
    _ ≤ ∑ _k : K l, ENNReal.ofReal ((size l : ℝ) ^ (-(D + C))) :=
        Finset.sum_le_sum fun k _ => hl k
    _ = ENNReal.ofReal (Fintype.card (K l) * (size l : ℝ) ^ (-(D + C))) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal ((size l : ℝ) ^ C * (size l : ℝ) ^ (-(D + C))) :=
        ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hcard hp)
    _ = ENNReal.ofReal ((size l : ℝ) ^ (-D)) := by
        rw [rpow_mul_rpow_neg_add_of_nonneg hs C D hD.ne']

end RBM.Path

/-! ## 9. The calculus of `StochDomAt` and `HighProbAt` at the scale `size`

`RBM2D/Defs/StochDom.lean` at `c9a24cf` proves this calculus only for the index scale
(`StochDom.refl`, `trans`, `add`, `mul`, `const_mul_*`, `of_forall_le`, `HighProb.*`, lines
132–432; merged as `RBM3D/Defs/StochDom.lean`); there is no `size`-indexed copy in RBM2D except the
definition (line 103) and `StochDomAt.of_unifDetDom_L_scale` (line 334, scale `W² l²`, `d = 2`).
The proofs below are the index-scale proofs with `N := size l` (each cites the RBM2D line of the
index-scale proof).  Wherever `N ≥ 2`, `N ≥ 1` or `N^e ≥ c` is used, the hypothesis
`hsize : Tendsto size atTop atTop` is explicit; for `sz : Sizes d` it is `Sizes.tendsto_size`. -/

namespace RBM

variable {Ω : Type*} [MeasurableSpace Ω]

namespace StochDomAt

variable {P : Measure Ω} {U : ℕ → Type*} {size : ℕ → ℕ}
  {ξ ζ χ ξ₁ ξ₂ ζ₁ ζ₂ : ∀ l, U l → Ω → ℝ}

/-- A failure event eventually contained in the failure event of a single domination.
`RBM2D/Defs/StochDom.lean:132` (index scale). -/
theorem of_subset (h : StochDomAt P size ξ₁ ζ₁)
    (hsub : ∀ τ > (0 : ℝ), ∃ τ' > (0 : ℝ), ∀ᶠ l : ℕ in atTop,
      badSetAt size ξ ζ τ l ⊆ badSetAt size ξ₁ ζ₁ τ' l) : StochDomAt P size ξ ζ := by
  intro τ hτ D hD
  obtain ⟨τ', hτ', hs⟩ := hsub τ hτ
  filter_upwards [hs, h τ' hτ' D hD] with l h1 h2
  exact (measure_mono h1).trans h2

/-- Restricting or reindexing the parameter family preserves uniform domination.
`RBM2D/Defs/StochDom.lean:141` (index scale). -/
theorem precomp_param {V : ℕ → Type*} (h : StochDomAt P size ξ ζ)
    (φ : ∀ l, V l → U l) :
    StochDomAt P size (fun l v ω => ξ l (φ l v) ω)
      (fun l v ω => ζ l (φ l v) ω) := by
  intro τ hτ D hD
  filter_upwards [h τ hτ D hD] with l hl
  refine (measure_mono fun ω hω => ?_).trans hl
  obtain ⟨v, hv⟩ := hω
  exact ⟨φ l v, hv⟩

/-- A pointwise smaller family is dominated by the same control.
`RBM2D/Defs/StochDom.lean:152` (index scale). -/
theorem of_le_left (hle : ∀ l u ω, ξ l u ω ≤ ξ₁ l u ω)
    (h : StochDomAt P size ξ₁ ζ) : StochDomAt P size ξ ζ :=
  of_subset h fun τ hτ =>
    ⟨τ, hτ, Eventually.of_forall fun l ω ⟨u, hu⟩ =>
      ⟨u, lt_of_lt_of_le hu (hle l u ω)⟩⟩

/-- A failure event eventually contained in the union of two failure events.  Uses
`2 N^{-(D+1)} ≤ N^{-D}`, i.e. `N ≥ 2`.  `RBM2D/Defs/StochDom.lean:159` (index scale). -/
theorem of_subset_union (hsize : Tendsto size atTop atTop)
    {U₁ U₂ : ℕ → Type*} {f₁ g₁ : ∀ l, U₁ l → Ω → ℝ}
    {f₂ g₂ : ∀ l, U₂ l → Ω → ℝ} (h₁ : StochDomAt P size f₁ g₁) (h₂ : StochDomAt P size f₂ g₂)
    (hsub : ∀ τ > (0 : ℝ), ∃ τ' > (0 : ℝ), ∀ᶠ l : ℕ in atTop,
      badSetAt size ξ ζ τ l ⊆ badSetAt size f₁ g₁ τ' l ∪ badSetAt size f₂ g₂ τ' l) :
    StochDomAt P size ξ ζ := by
  intro τ hτ D hD
  obtain ⟨τ', hτ', hs⟩ := hsub τ hτ
  filter_upwards [hs, h₁ τ' hτ' (D + 1) (by linarith), h₂ τ' hτ' (D + 1) (by linarith),
    hsize.eventually (eventually_two_mul_rpow_le D)] with l h0 h1 h2 h3
  have hp : (0 : ℝ) ≤ (size l : ℝ) ^ (-(D + 1)) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  calc P (badSetAt size ξ ζ τ l) ≤ P (badSetAt size f₁ g₁ τ' l ∪ badSetAt size f₂ g₂ τ' l) :=
        measure_mono h0
    _ ≤ P (badSetAt size f₁ g₁ τ' l) + P (badSetAt size f₂ g₂ τ' l) := measure_union_le _ _
    _ ≤ ENNReal.ofReal ((size l : ℝ) ^ (-(D + 1))) + ENNReal.ofReal ((size l : ℝ) ^ (-(D + 1))) :=
        add_le_add h1 h2
    _ = ENNReal.ofReal (2 * (size l : ℝ) ^ (-(D + 1))) := by
        rw [← ENNReal.ofReal_add hp hp]; ring_nf
    _ ≤ ENNReal.ofReal ((size l : ℝ) ^ (-D)) := ENNReal.ofReal_le_ofReal h3

/-- A failure event that is eventually empty.  `RBM2D/Defs/StochDom.lean:176` (index scale). -/
theorem of_eventually_empty
    (h : ∀ τ > (0 : ℝ), ∀ᶠ l : ℕ in atTop, badSetAt size ξ ζ τ l = ∅) :
    StochDomAt P size ξ ζ := by
  intro τ hτ D _
  filter_upwards [h τ hτ] with l hl
  rw [hl, measure_empty]; exact zero_le

/-- **Deterministic domination implies stochastic domination** (Definition 2.1 (ii) ⇒ (i)), at
the scale `size`: a family dominated deterministically at the index scale `l` is dominated at the
scale `size l` as soon as `l ≤ size l`.  `RBM2D/Defs/StochDom.lean:334`
(`of_unifDetDom_L_scale`, scale `W² l²`) and `:183` (`StochDom.of_unifDetDom`, `size = id`). -/
theorem of_unifDetDom {f g : ∀ l, U l → ℝ} (hl : ∀ᶠ l : ℕ in atTop, l ≤ size l)
    (hg : ∀ l u, 0 ≤ g l u) (h : UnifDetDom f g) :
    StochDomAt P size (fun l u _ => f l u) (fun l u _ => g l u) := by
  refine of_eventually_empty fun τ hτ => ?_
  filter_upwards [h τ hτ, hl] with l hdom hlN
  have hpow : (l : ℝ) ^ τ ≤ (size l : ℝ) ^ τ :=
    Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hlN) hτ.le
  ext ω
  simp only [badSetAt, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_exists, not_lt]
  intro u
  exact (hdom u).trans (mul_le_mul_of_nonneg_right hpow (hg l u))

/-- `ζ ≺ ζ` for a non-negative family.  `RBM2D/Defs/StochDom.lean:192` (index scale). -/
theorem refl (hsize : Tendsto size atTop atTop) (hζ : ∀ l u ω, 0 ≤ ζ l u ω) :
    StochDomAt P size ζ ζ :=
  of_eventually_empty fun τ hτ => by
    filter_upwards [hsize.eventually (eventually_ge_atTop 1)] with l hl
    ext ω
    simp only [badSetAt, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_exists, not_lt]
    intro u
    have h1 : (1 : ℝ) ≤ (size l : ℝ) ^ τ := Real.one_le_rpow (by exact_mod_cast hl) hτ.le
    nlinarith [hζ l u ω]

/-- `≺` is transitive.  `RBM2D/Defs/StochDom.lean:202` (index scale). -/
theorem trans (hsize : Tendsto size atTop atTop)
    (h₁ : StochDomAt P size ξ ζ) (h₂ : StochDomAt P size ζ χ) : StochDomAt P size ξ χ := by
  refine of_subset_union hsize h₁ h₂ fun τ hτ =>
    ⟨τ / 2, half_pos hτ, Eventually.of_forall fun l => ?_⟩
  intro ω ⟨u, hu⟩
  by_contra hno
  simp only [Set.mem_union, badSetAt, Set.mem_ofPred_eq, not_or, not_exists, not_lt] at hno
  have hpos : 0 ≤ (size l : ℝ) ^ (τ / 2) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have := calc ξ l u ω ≤ (size l : ℝ) ^ (τ / 2) * ζ l u ω := hno.1 u
    _ ≤ (size l : ℝ) ^ (τ / 2) * ((size l : ℝ) ^ (τ / 2) * χ l u ω) :=
        mul_le_mul_of_nonneg_left (hno.2 u) hpos
    _ = (size l : ℝ) ^ τ * χ l u ω := by
        rw [← mul_assoc, UnifDetDom.rpow_half_mul_rpow_half (size l) hτ]
  linarith

/-- `≺` is closed under addition.  `RBM2D/Defs/StochDom.lean:215` (index scale). -/
theorem add (hsize : Tendsto size atTop atTop)
    (h₁ : StochDomAt P size ξ₁ ζ₁) (h₂ : StochDomAt P size ξ₂ ζ₂) :
    StochDomAt P size (ξ₁ + ξ₂) (ζ₁ + ζ₂) := by
  refine of_subset_union hsize h₁ h₂ fun τ hτ => ⟨τ, hτ, Eventually.of_forall fun l => ?_⟩
  intro ω ⟨u, hu⟩
  by_contra hno
  simp only [Set.mem_union, badSetAt, Set.mem_ofPred_eq, not_or, not_exists, not_lt] at hno
  simp only [Pi.add_apply, mul_add] at hu
  linarith [hno.1 u, hno.2 u]

/-- `≺` is closed under multiplication of non-negative quantities.
`RBM2D/Defs/StochDom.lean:225` (index scale). -/
theorem mul (hsize : Tendsto size atTop atTop)
    (hξ₂ : ∀ l u ω, 0 ≤ ξ₂ l u ω) (hζ₁ : ∀ l u ω, 0 ≤ ζ₁ l u ω)
    (h₁ : StochDomAt P size ξ₁ ζ₁) (h₂ : StochDomAt P size ξ₂ ζ₂) :
    StochDomAt P size (ξ₁ * ξ₂) (ζ₁ * ζ₂) := by
  refine of_subset_union hsize h₁ h₂ fun τ hτ =>
    ⟨τ / 2, half_pos hτ, Eventually.of_forall fun l => ?_⟩
  intro ω ⟨u, hu⟩
  by_contra hno
  simp only [Set.mem_union, badSetAt, Set.mem_ofPred_eq, not_or, not_exists, not_lt] at hno
  have hpos : 0 ≤ (size l : ℝ) ^ (τ / 2) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have := calc ξ₁ l u ω * ξ₂ l u ω
        ≤ ((size l : ℝ) ^ (τ / 2) * ζ₁ l u ω) * ξ₂ l u ω :=
        mul_le_mul_of_nonneg_right (hno.1 u) (hξ₂ l u ω)
    _ ≤ ((size l : ℝ) ^ (τ / 2) * ζ₁ l u ω) * ((size l : ℝ) ^ (τ / 2) * ζ₂ l u ω) :=
        mul_le_mul_of_nonneg_left (hno.2 u) (mul_nonneg hpos (hζ₁ l u ω))
    _ = ((size l : ℝ) ^ (τ / 2) * (size l : ℝ) ^ (τ / 2)) * (ζ₁ l u ω * ζ₂ l u ω) := by ring
    _ = (size l : ℝ) ^ τ * (ζ₁ l u ω * ζ₂ l u ω) := by
        rw [UnifDetDom.rpow_half_mul_rpow_half (size l) hτ]
  simp only [Pi.mul_apply] at hu
  linarith

/-- Constant factors on the left are absorbed: `ξ ≺ ζ` implies `c ξ ≺ ζ`.
`RBM2D/Defs/StochDom.lean:243` (index scale). -/
theorem const_mul_left (hsize : Tendsto size atTop atTop) {c : ℝ} (hc : 0 ≤ c)
    (hζ : ∀ l u ω, 0 ≤ ζ l u ω) (h : StochDomAt P size ξ ζ) :
    StochDomAt P size (fun l u ω => c * ξ l u ω) ζ := by
  refine of_subset h fun τ hτ => ⟨τ / 2, half_pos hτ, ?_⟩
  filter_upwards [hsize.eventually (eventually_le_rpow c (half_pos hτ))] with l hcN
  intro ω ⟨u, hu⟩
  by_contra hno
  simp only [badSetAt, Set.mem_ofPred_eq, not_exists, not_lt] at hno
  have hpos : 0 ≤ (size l : ℝ) ^ (τ / 2) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have h1 := hno u
  have h2 : 0 ≤ (size l : ℝ) ^ (τ / 2) * ζ l u ω := mul_nonneg hpos (hζ l u ω)
  have := calc c * ξ l u ω ≤ c * ((size l : ℝ) ^ (τ / 2) * ζ l u ω) :=
        mul_le_mul_of_nonneg_left h1 hc
    _ ≤ (size l : ℝ) ^ (τ / 2) * ((size l : ℝ) ^ (τ / 2) * ζ l u ω) :=
        mul_le_mul_of_nonneg_right hcN h2
    _ = (size l : ℝ) ^ τ * ζ l u ω := by
        rw [← mul_assoc, UnifDetDom.rpow_half_mul_rpow_half (size l) hτ]
  exact absurd hu (not_lt.2 this)

/-- Constant factors on the right are absorbed: `ξ ≺ ζ` implies `ξ ≺ c ζ` for `c > 0`.
`RBM2D/Defs/StochDom.lean:259` (index scale). -/
theorem const_mul_right (hsize : Tendsto size atTop atTop) {c : ℝ} (hc : 0 < c)
    (hζ : ∀ l u ω, 0 ≤ ζ l u ω) (h : StochDomAt P size ξ ζ) :
    StochDomAt P size ξ (fun l u ω => c * ζ l u ω) := by
  refine of_subset h fun τ hτ => ⟨τ / 2, half_pos hτ, ?_⟩
  filter_upwards [hsize.eventually (eventually_le_rpow c⁻¹ (half_pos hτ))] with l hcN
  intro ω ⟨u, hu⟩
  by_contra hno
  simp only [badSetAt, Set.mem_ofPred_eq, not_exists, not_lt] at hno
  have hpos : 0 ≤ (size l : ℝ) ^ (τ / 2) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have h1 := hno u
  have hζ' := hζ l u ω
  have := calc ξ l u ω ≤ (size l : ℝ) ^ (τ / 2) * ζ l u ω := h1
    _ = (size l : ℝ) ^ (τ / 2) * (c⁻¹ * (c * ζ l u ω)) := by field_simp
    _ ≤ (size l : ℝ) ^ (τ / 2) * ((size l : ℝ) ^ (τ / 2) * (c * ζ l u ω)) := by
        gcongr
    _ = (size l : ℝ) ^ τ * (c * ζ l u ω) := by
        rw [← mul_assoc, UnifDetDom.rpow_half_mul_rpow_half (size l) hτ]
  exact absurd hu (not_lt.2 this)

/-- **The union bound** (the content of "uniformly in `u`"): if each event
`{ξ(l,u) > size(l)^τ ζ(l,u)}` has probability `≤ size(l)^{-D}` for `l ≥ l₀(τ, D)` uniformly in
`u`, and `#U(l) ≤ size(l)^C`, then `ξ ≺ ζ` uniformly in `u`.  The case `C ≥ 0` is
`Path.stochDomAt_of_perTimeDomAt`; the case `C < 0` forces `U l = ∅` (`size l ≥ 2`).
`RBM2D/Defs/StochDom.lean:279` (index scale). -/
theorem of_forall_le (hsize : Tendsto size atTop atTop) [∀ l, Fintype (U l)] {C : ℝ}
    (hC : ∀ᶠ l : ℕ in atTop, (Fintype.card (U l) : ℝ) ≤ (size l : ℝ) ^ C)
    (h : ∀ τ > (0 : ℝ), ∀ D > (0 : ℝ), ∀ᶠ l : ℕ in atTop, ∀ u,
      P {ω | (size l : ℝ) ^ τ * ζ l u ω < ξ l u ω} ≤ ENNReal.ofReal ((size l : ℝ) ^ (-D))) :
    StochDomAt P size ξ ζ := by
  by_cases hC0 : 0 ≤ C
  · exact Path.stochDomAt_of_perTimeDomAt P size hC0 hC h
  · -- `C < 0`: then `#U(l) < 1`, so `U(l)` is empty and so is the failure event
    push Not at hC0
    intro τ hτ D hD
    filter_upwards [hC, hsize.eventually (eventually_ge_atTop 2)] with l hcard hN2
    have hlt : (Fintype.card (U l) : ℝ) < 1 := by
      refine hcard.trans_lt ?_
      exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hN2) hC0
    have h0 : Fintype.card (U l) = 0 := by exact_mod_cast (show (Fintype.card (U l) : ℝ) = 0 by
      have := Nat.cast_nonneg (α := ℝ) (Fintype.card (U l))
      rcases Nat.eq_zero_or_pos (Fintype.card (U l)) with h | h
      · exact_mod_cast h
      · exact absurd hlt (not_lt.2 (by exact_mod_cast h)))
    have hE : IsEmpty (U l) := Fintype.card_eq_zero_iff.1 h0
    have : badSetAt size ξ ζ τ l = ∅ := by
      ext ω; simp only [badSetAt, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨u, -⟩; exact hE.false u
    rw [this, measure_empty]; exact zero_le

/-- **The good event holds with high probability**: `ξ ≺ ζ` means that for every `τ > 0`,
`{∀ u, ξ(l,u) ≤ size(l)^τ ζ(l,u)}` holds w.h.p.  `RBM2D/Defs/StochDom.lean:318` (index scale). -/
theorem highProb (h : StochDomAt P size ξ ζ) {τ : ℝ} (hτ : 0 < τ) :
    Gauss.HighProbAt P size (fun l => {ω | ∀ u, ξ l u ω ≤ (size l : ℝ) ^ τ * ζ l u ω}) := by
  intro D hD
  filter_upwards [h τ hτ D hD] with l hl
  refine le_trans (le_of_eq ?_) hl
  congr 1
  ext ω
  simp [badSetAt]

end StochDomAt

/-- **`A = O≺(ζ)`** at the scale `size` (`‖A‖ ≺ ζ`): the scale version of the merged
`RBM.NormStochDom`; there is no `size`-indexed copy in RBM2D.  The merged predicate is the case
`size = id` (`normStochDom_iff_at_id`). -/
def NormStochDomAt {U : ℕ → Type*} {E : Type*} [Norm E] (P : Measure Ω) (size : ℕ → ℕ)
    (A : ∀ l, U l → Ω → E) (ζ : ∀ l, U l → Ω → ℝ) : Prop :=
  StochDomAt P size (fun l u ω => ‖A l u ω‖) ζ

/-- The merged `RBM.NormStochDom` is `NormStochDomAt` at `size = id`. -/
theorem normStochDom_iff_at_id {U : ℕ → Type*} {E : Type*} [Norm E] (P : Measure Ω)
    (A : ∀ N, U N → Ω → E) (ζ : ∀ N, U N → Ω → ℝ) :
    NormStochDom P A ζ ↔ NormStochDomAt P id A ζ := Iff.rfl

end RBM

namespace RBM.Gauss.HighProbAt

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {size : ℕ → ℕ}

/-- Monotonicity.  `RBM2D/Defs/StochDom.lean:366` (index scale). -/
theorem mono {Ξ Ξ' : ℕ → Set Ω} (h : HighProbAt P size Ξ)
    (hsub : ∀ᶠ l : ℕ in atTop, Ξ l ⊆ Ξ' l) : HighProbAt P size Ξ' := by
  intro D hD
  filter_upwards [h D hD, hsub] with l hl hs
  exact (measure_mono (Set.compl_subset_compl.2 hs)).trans hl

/-- Two w.h.p. events hold simultaneously w.h.p.  `RBM2D/Defs/StochDom.lean:373` (index scale). -/
theorem inter (hsize : Tendsto size atTop atTop) {Ξ₁ Ξ₂ : ℕ → Set Ω}
    (h₁ : HighProbAt P size Ξ₁) (h₂ : HighProbAt P size Ξ₂) :
    HighProbAt P size (fun l => Ξ₁ l ∩ Ξ₂ l) := by
  intro D hD
  filter_upwards [h₁ (D + 1) (by linarith), h₂ (D + 1) (by linarith),
    hsize.eventually (eventually_two_mul_rpow_le D)] with l hl1 hl2 h3
  have hp : (0 : ℝ) ≤ (size l : ℝ) ^ (-(D + 1)) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  calc P (Ξ₁ l ∩ Ξ₂ l)ᶜ = P ((Ξ₁ l)ᶜ ∪ (Ξ₂ l)ᶜ) := by rw [Set.compl_inter]
    _ ≤ P (Ξ₁ l)ᶜ + P (Ξ₂ l)ᶜ := measure_union_le _ _
    _ ≤ ENNReal.ofReal ((size l : ℝ) ^ (-(D + 1))) + ENNReal.ofReal ((size l : ℝ) ^ (-(D + 1))) :=
        add_le_add hl1 hl2
    _ = ENNReal.ofReal (2 * (size l : ℝ) ^ (-(D + 1))) := by
        rw [← ENNReal.ofReal_add hp hp]; ring_nf
    _ ≤ ENNReal.ofReal ((size l : ℝ) ^ (-D)) := ENNReal.ofReal_le_ofReal h3

/-- **Polynomially many w.h.p. events hold simultaneously w.h.p.**: the name of
`RBM.HighProb.biInter` at the scale `size`; it is `Path.highProbAt_iInter`
(`RBM2D/Path/PerTime.lean:141`). -/
theorem biInter {K : ℕ → Type*} [∀ l, Fintype (K l)] {Ξ : ∀ l, K l → Set Ω} {C : ℝ}
    (hC0 : 0 ≤ C) (hC : ∀ᶠ l : ℕ in atTop, (Fintype.card (K l) : ℝ) ≤ (size l : ℝ) ^ C)
    (h : ∀ D > (0 : ℝ), ∀ᶠ l : ℕ in atTop, ∀ k,
      P (Ξ l k)ᶜ ≤ ENNReal.ofReal ((size l : ℝ) ^ (-D))) :
    HighProbAt P size (fun l => ⋂ k, Ξ l k) :=
  Path.highProbAt_iInter P size hC0 hC h

/-- An event that eventually contains every sample point holds with high probability.  This is
how a *deterministic* polynomial lower bound on the control enters
`StochDomAt.of_highProbAt_add_rpow_neg`.  `RBM2D/Defs/StochDom.lean:467` (index scale). -/
theorem of_eventually_univ {Ξ : ℕ → Set Ω}
    (h : ∀ᶠ l : ℕ in atTop, ∀ ω, ω ∈ Ξ l) : HighProbAt P size Ξ := by
  intro D _
  filter_upwards [h] with l hl
  have hc : (Ξ l)ᶜ = (∅ : Set Ω) := by
    ext ω; simp only [Set.mem_compl_iff, Set.mem_empty_iff_false, iff_false, not_not]
    exact hl ω
  rw [hc, measure_empty]
  exact zero_le

/-- **A high-probability family of events is eventually non-empty.**  No measurability is
needed: if `Ξ l` were empty then `(Ξ l)ᶜ = univ` has measure `1`, while `HighProbAt` at `D = 1`
puts it below `size(l)^{-1} < 1` once `size l ≥ 2`.  `RBM2D/Defs/StochDom.lean:411` (index
scale). -/
theorem nonempty (hsize : Tendsto size atTop atTop) {Ξ : ℕ → Set Ω} (hP : P Set.univ = 1)
    (h : HighProbAt P size Ξ) : ∀ᶠ l : ℕ in atTop, (Ξ l).Nonempty := by
  filter_upwards [h 1 one_pos, hsize.eventually (eventually_ge_atTop 2)] with l hl hN2
  rw [Set.nonempty_iff_ne_empty]
  intro hemp
  rw [hemp, Set.compl_empty, hP] at hl
  have hN2' : (2 : ℝ) ≤ (size l : ℝ) := by exact_mod_cast hN2
  have hrw : (size l : ℝ) ^ (-(1 : ℝ)) = ((size l : ℝ))⁻¹ := by
    rw [Real.rpow_neg (by linarith), Real.rpow_one]
  have hlt : (size l : ℝ) ^ (-(1 : ℝ)) < 1 := by
    rw [hrw, inv_lt_one_iff₀]
    right; linarith
  exact absurd hl (not_le.2 (ENNReal.ofReal_lt_one.2 hlt))

end RBM.Gauss.HighProbAt

/-! ### Absorbing a super-polynomially small additive error, at the scale `size`

A bound `ξ ≤ N^τ ζ + ε_N` with `ε_N` super-polynomially small is a `≺` statement as soon as the
control has a polynomial lower bound `N^{-b} ≤ ζ` (without one it is false: `ζ = 0`, `ξ = ε_N > 0`).
The arithmetic step `le_rpow_mul_of_le_add_rpow_neg` is stated for any `N : ℕ` and is used with
`N := size l`.  Ported from `RBM2D/Defs/StochDom.lean:460–554` (`Absorb`, index scale). -/

namespace RBM

section Absorb

variable {Ω : Type*} [MeasurableSpace Ω]

/-- `2 a y ≤ a² y` for `a ≥ 2` and `y ≥ 0`.  `RBM2D/Defs/StochDom.lean:478`. -/
theorem two_mul_le_mul_self {a y : ℝ} (ha : (2 : ℝ) ≤ a) (hy : 0 ≤ y) :
    2 * (a * y) ≤ a * a * y := by
  have ha0 : (0 : ℝ) ≤ a := by linarith
  nlinarith [mul_nonneg (mul_nonneg ha0 hy) (sub_nonneg.2 ha)]

/-- **The pointwise absorption step.**  If the control `y` is bounded below by `N^{-b}`, the
error `ε` is bounded above by the same `N^{-b}`, and `2 ≤ N^{τ/2}`, then a bound
`x ≤ N^{τ/2} y + ε` upgrades to `x ≤ N^τ y`.  `RBM2D/Defs/StochDom.lean:486`. -/
theorem le_rpow_mul_of_le_add_rpow_neg {N : ℕ} {τ b x y ε : ℝ} (hτ : 0 < τ)
    (hN : (2 : ℝ) ≤ (N : ℝ) ^ (τ / 2)) (hy : (N : ℝ) ^ (-b) ≤ y) (hε : ε ≤ (N : ℝ) ^ (-b))
    (hx : x ≤ (N : ℝ) ^ (τ / 2) * y + ε) : x ≤ (N : ℝ) ^ τ * y := by
  have hy0 : 0 ≤ y := le_trans (Real.rpow_nonneg (Nat.cast_nonneg N) _) hy
  have hhalf : (N : ℝ) ^ (τ / 2) * (N : ℝ) ^ (τ / 2) = (N : ℝ) ^ τ :=
    UnifDetDom.rpow_half_mul_rpow_half N hτ
  have hkey := two_mul_le_mul_self hN hy0
  have hεy : ε ≤ y := hε.trans hy
  have hya : y ≤ (N : ℝ) ^ (τ / 2) * y := by nlinarith
  rw [← hhalf]
  linarith

variable {P : Measure Ω} {U : ℕ → Type*} {size : ℕ → ℕ} {ξ ζ : ∀ l, U l → Ω → ℝ}

/-- **Absorbing a super-polynomially small additive error in the control**: if
`ξ ≺ ζ + ε`, the control `ζ` is eventually bounded below by `size(l)^{-b}` (uniformly in `u` and
`ω`) and the error `ε` is eventually bounded above by the same `size(l)^{-b}`, then `ξ ≺ ζ`.
`RBM2D/Defs/StochDom.lean:504` (index scale). -/
theorem StochDomAt.of_add_le (hsize : Tendsto size atTop atTop) {b : ℝ} {ε : ℕ → ℝ}
    (hlow : ∀ᶠ l : ℕ in atTop, ∀ u ω, (size l : ℝ) ^ (-b) ≤ ζ l u ω)
    (hε : ∀ᶠ l : ℕ in atTop, ε l ≤ (size l : ℝ) ^ (-b))
    (h : StochDomAt P size ξ (fun l u ω => ζ l u ω + ε l)) :
    StochDomAt P size ξ ζ := by
  refine StochDomAt.of_subset h fun τ hτ => ⟨τ / 2, half_pos hτ, ?_⟩
  filter_upwards [hlow, hε, hsize.eventually (eventually_le_rpow 2 (half_pos hτ))]
    with l hl he h2
  rintro ω ⟨u, hu⟩
  refine ⟨u, lt_of_le_of_lt ?_ hu⟩
  have hy0 : (0 : ℝ) ≤ ζ l u ω := le_trans (Real.rpow_nonneg (Nat.cast_nonneg _) _) (hl u ω)
  have hhalf : (size l : ℝ) ^ (τ / 2) * (size l : ℝ) ^ (τ / 2) = (size l : ℝ) ^ τ :=
    UnifDetDom.rpow_half_mul_rpow_half (size l) hτ
  have he' : ε l ≤ ζ l u ω := he.trans (hl u ω)
  have ha0 : (0 : ℝ) ≤ (size l : ℝ) ^ (τ / 2) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hkey := two_mul_le_mul_self h2 hy0
  have hya : ζ l u ω ≤ (size l : ℝ) ^ (τ / 2) * ζ l u ω := by nlinarith
  rw [← hhalf]
  nlinarith

/-- **Absorbing a super-polynomially small additive error, the high-probability route.**  If

* the control `ζ` is bounded below by `size(l)^{-b}` for all `u`, with high probability, and
* for every `τ > 0` and `D > 0` the pathwise bound `ξ ≤ size(l)^τ ζ + size(l)^{-D}` holds for all
  `u` with high probability,

then `ξ ≺ ζ`.  For a deterministic lower bound use `Gauss.HighProbAt.of_eventually_univ`.
`RBM2D/Defs/StochDom.lean:535` (index scale). -/
theorem StochDomAt.of_highProbAt_add_rpow_neg (hsize : Tendsto size atTop atTop) {b : ℝ}
    (hlow : Gauss.HighProbAt P size (fun l => {ω | ∀ u, (size l : ℝ) ^ (-b) ≤ ζ l u ω}))
    (h : ∀ τ > (0 : ℝ), ∀ D > (0 : ℝ),
      Gauss.HighProbAt P size (fun l =>
        {ω | ∀ u, ξ l u ω ≤ (size l : ℝ) ^ τ * ζ l u ω + (size l : ℝ) ^ (-D)})) :
    StochDomAt P size ξ ζ := by
  intro τ hτ D hD
  have hD0 : (0 : ℝ) < |b| + 1 := by positivity
  have hev := Gauss.HighProbAt.inter hsize hlow (h (τ / 2) (half_pos hτ) (|b| + 1) hD0) D hD
  filter_upwards [hev, hsize.eventually (eventually_le_rpow 2 (half_pos hτ)),
    hsize.eventually (eventually_ge_atTop 1)] with l hl h2 hl1
  refine (measure_mono ?_).trans hl
  rintro ω ⟨u, hu⟩ hmem
  obtain ⟨hl', hb⟩ := hmem
  simp only [Set.mem_ofPred_eq] at hl' hb
  have hN1' : (1 : ℝ) ≤ (size l : ℝ) := by exact_mod_cast hl1
  have hrp : (size l : ℝ) ^ (-(|b| + 1)) ≤ (size l : ℝ) ^ (-b) :=
    Real.rpow_le_rpow_of_exponent_le hN1' (by cases abs_cases b <;> linarith)
  exact absurd (le_rpow_mul_of_le_add_rpow_neg hτ h2 (hl' u) hrp (hb u)) (not_le.2 hu)

end Absorb

end RBM

/-! ## 10. Compiled instances at the MD-1 size sequence `sz0`

`sz0 = RBM.Gauss.SizesInst.sz0` (`d = 3`, `L n = 4(n+1)`, `W n = (2(n+1))^5`, `N_0 = 2097152`) on
the model measure `seqP sz0` (a probability measure on the product of Gaussian coordinates).  The
observable `obs n` is a genuinely random variable: `|sin|` of the `(0,0)` real coordinate of size
`n`; it is bounded by `1`, so deterministic domination applies, and it is not constant.  All
hypotheses of every example are discharged (`Tendsto sz0.size atTop atTop` is `sz0_tendsto`). -/

namespace RBM.Gauss.Sizes

variable {d : ℕ} (sz : Sizes d)

/-- `N → ∞` as a statement about the `ℕ`-valued scale: the hypothesis `hsize` of the `StochDomAt`
calculus (`tendsto_natCast_atTop_iff`). -/
theorem tendsto_size (h : sz.SizeTendsto) : Tendsto sz.size atTop atTop :=
  tendsto_natCast_atTop_iff.1 h

end RBM.Gauss.Sizes

namespace RBM.Gauss.StochDomAtInst

open RBM.Gauss.SizesInst RBM.Gauss.Sizes

/-- A random bounded observable at size `n`: `|sin|` of the `(0,0)` real coordinate. -/
def obs (n : ℕ) (ω : SeqΩ sz0) : ℝ :=
  |Real.sin (ω ⟨n, ((0 : Idx 3 (sz0.L n) (sz0.W n)), (0 : Idx 3 (sz0.L n) (sz0.W n)), true)⟩)|

theorem obs_nonneg (n : ℕ) (ω : SeqΩ sz0) : 0 ≤ obs n ω := abs_nonneg _

theorem obs_le_one (n : ℕ) (ω : SeqΩ sz0) : obs n ω ≤ 1 := by
  unfold obs; exact Real.abs_sin_le_one _

/-- `obs n` is not constant: it is `0` at `ω = 0` and `1` at `ω = π/2` (nondegenerate data). -/
theorem obs_nonconst (n : ℕ) : ∃ ω ω' : SeqΩ sz0, obs n ω ≠ obs n ω' := by
  refine ⟨fun _ => 0, fun _ => Real.pi / 2, ?_⟩
  simp [obs]

theorem tendsto_sz0_size : Tendsto sz0.size atTop atTop := tendsto_size sz0 sz0_tendsto

/-- The three-step chain of controls `obs ≤ 1 + obs ≤ 2 + obs` (all random, strictly positive
from the second on). -/
def Xi (n : ℕ) (_ : Unit) (ω : SeqΩ sz0) : ℝ := obs n ω
def Ze (n : ℕ) (_ : Unit) (ω : SeqΩ sz0) : ℝ := 1 + obs n ω
def Ch (n : ℕ) (_ : Unit) (ω : SeqΩ sz0) : ℝ := 2 + obs n ω

theorem Ze_nonneg (n : ℕ) (u : Unit) (ω : SeqΩ sz0) : 0 ≤ Ze n u ω := by
  unfold Ze; linarith [obs_nonneg n ω]

theorem Ch_nonneg (n : ℕ) (u : Unit) (ω : SeqΩ sz0) : 0 ≤ Ch n u ω := by
  unfold Ch; linarith [obs_nonneg n ω]

theorem Xi_nonneg (n : ℕ) (u : Unit) (ω : SeqΩ sz0) : 0 ≤ Xi n u ω := obs_nonneg n ω

/-- **Instance of `prec_of_le`** at `sz0`: `obs ≺ 1 + obs` on the model measure at the scale
`N_n = (W_n L_n)^3`, from the pointwise bound `obs ≤ 1 + obs`. -/
theorem prec_Xi_Ze : sz0.Prec Xi Ze :=
  Sizes.prec_of_le sz0 Ze_nonneg fun n u ω => by unfold Xi Ze; linarith [obs_nonneg n ω]

theorem prec_Ze_Ch : sz0.Prec Ze Ch :=
  Sizes.prec_of_le sz0 Ch_nonneg fun n u ω => by unfold Ze Ch; linarith [obs_nonneg n ω]

/-- **Instance of `StochDomAt.trans`** (ported calculus) at the family `Xi ≺ Ze ≺ Ch` on `seqP sz0`,
scale `sz0.size`, with `hsize := tendsto_sz0_size`. -/
theorem stochDomAt_Xi_Ch : StochDomAt (seqP sz0) sz0.size Xi Ch :=
  StochDomAt.trans tendsto_sz0_size prec_Xi_Ze prec_Ze_Ch

/-- **Instance of `stochDom_iff_at_id`**: on the model measure `seqP sz0`, the merged `StochDom`
(family index `N` as scale) for the random positive family `Ze` is `StochDomAt` at `size = id`;
`StochDom.refl` proves the left side, so the right side holds. -/
theorem stochDomAt_id_Ze : StochDomAt (seqP sz0) id Ze Ze :=
  (stochDom_iff_at_id (seqP sz0) Ze Ze).mp (StochDom.refl Ze_nonneg)

/-- The converse direction of `stochDom_iff_at_id` at the same data. -/
theorem stochDom_Ze : StochDom (seqP sz0) Ze Ze :=
  (stochDom_iff_at_id (seqP sz0) Ze Ze).mpr (StochDomAt.refl tendsto_id Ze_nonneg)

/-- **Instance of `highProb_iff_at_id`**: the event `{∀ u, Ze ≤ N^τ Ze}` holds w.h.p. in the merged
sense (`StochDom.highProb`) and therefore at `size = id`. -/
theorem highProbAt_id_Ze : HighProbAt (seqP sz0) id
    (fun N => {ω | ∀ u, Ze N u ω ≤ (N : ℝ) ^ (1 : ℝ) * Ze N u ω}) :=
  (highProb_iff_at_id (seqP sz0) _).mp (StochDom.highProb (StochDom.refl Ze_nonneg) one_pos)

/-- `Prec.whp` at `sz0`: the good event `{∀ u, obs ≤ N^{1/10} (1 + obs)}` holds w.h.p. at the scale
`N_n`. -/
theorem whp_Xi : sz0.Whp
    (fun n => {ω | ∀ u, Xi n u ω ≤ ((sz0.size n : ℕ) : ℝ) ^ (1 / 10 : ℝ) * Ze n u ω}) :=
  Sizes.Prec.whp sz0 prec_Xi_Ze (τ := 1 / 10) (by norm_num)

/-- `precPT_of_le` at `sz0`, on a two-point parameter set `Fin 2` (the per-time form). -/
theorem precPT_Xi_Ze : sz0.PrecPT (U := fun _ => Fin 2) (fun n _ ω => Xi n () ω)
    (fun n _ ω => Ze n () ω) :=
  Sizes.precPT_of_le sz0 (fun n _ ω => Ze_nonneg n () ω) fun n _ ω => by
    unfold Xi Ze; linarith [obs_nonneg n ω]

/-- The grid union bound (`stochDomAt_of_perTimeDomAt`, `StochDomAt.of_forall_le`) at `sz0` with
`#U = 2 ≤ N^1`: per time over `Fin 2` gives the uniform statement. -/
theorem stochDomAt_Fin2 : StochDomAt (seqP sz0) sz0.size (U := fun _ => Fin 2)
    (fun n _ ω => Xi n () ω) (fun n _ ω => Ze n () ω) :=
  StochDomAt.of_forall_le tendsto_sz0_size (C := 1)
    (by
      filter_upwards [tendsto_sz0_size.eventually (eventually_ge_atTop 2)] with n hn
      simpa using (show (2 : ℝ) ≤ (sz0.size n : ℝ) by exact_mod_cast hn))
    precPT_Xi_Ze

/-- `Path.stochDomAt_of_perTimeDomAt` directly (the `C ≥ 0` case behind `of_forall_le`). -/
example : StochDomAt (seqP sz0) sz0.size (U := fun _ => Fin 2)
    (fun n _ ω => Xi n () ω) (fun n _ ω => Ze n () ω) :=
  Path.stochDomAt_of_perTimeDomAt (seqP sz0) sz0.size (C := 1) zero_le_one
    (by
      filter_upwards [tendsto_sz0_size.eventually (eventually_ge_atTop 2)] with n hn
      simpa using (show (2 : ℝ) ≤ (sz0.size n : ℝ) by exact_mod_cast hn))
    precPT_Xi_Ze

/-- `perTimeOfStochDomAt` applied to the uniform statement of `stochDomAt_Fin2`.  (An `example`,
not a theorem: a theorem concluding `PerTimeDomAt` for one family would make the premise scan of
`RBM3D/Test/Axioms.lean` count it as proved.) -/
example : Path.PerTimeDomAt (seqP sz0) sz0.size (U := fun _ => Fin 2)
    (fun n _ ω => Xi n () ω) (fun n _ ω => Ze n () ω) :=
  Path.perTimeOfStochDomAt (seqP sz0) sz0.size _ _ stochDomAt_Fin2

/-! ### The remaining calculus at the same data

One instance for each remaining public theorem of this file, all at `sz0`, `seqP sz0` and the
chain `Xi ≺ Ze ≺ Ch` (`Xi = obs`, `Ze = 1 + obs`, `Ch = 2 + obs`). -/

theorem sz0_self_le_size (n : ℕ) : n ≤ sz0.size n := by
  have h1 : 4 * (n + 1) ≤ (2 * (n + 1)) ^ 5 * (4 * (n + 1)) :=
    Nat.le_mul_of_pos_left _ (by positivity)
  have h2 : (2 * (n + 1)) ^ 5 * (4 * (n + 1)) ≤ ((2 * (n + 1)) ^ 5 * (4 * (n + 1))) ^ 3 :=
    Nat.le_self_pow (by norm_num) _
  change n ≤ ((2 * (n + 1)) ^ 5 * (4 * (n + 1))) ^ 3
  omega

/-- `one_le_size` at `sz0`, `n = 0`: `1 ≤ 2097152`. -/
example : 1 ≤ sz0.size 0 := Sizes.one_le_size sz0 0

theorem stochDomAt_add : StochDomAt (seqP sz0) sz0.size (Xi + Ze) (Ze + Ch) :=
  StochDomAt.add tendsto_sz0_size prec_Xi_Ze prec_Ze_Ch

theorem stochDomAt_mul : StochDomAt (seqP sz0) sz0.size (Xi * Ze) (Ze * Ch) :=
  StochDomAt.mul tendsto_sz0_size Ze_nonneg Ze_nonneg prec_Xi_Ze prec_Ze_Ch

theorem stochDomAt_const_mul_left : StochDomAt (seqP sz0) sz0.size
    (fun n u ω => 2 * Xi n u ω) Ze :=
  StochDomAt.const_mul_left tendsto_sz0_size (by norm_num) Ze_nonneg prec_Xi_Ze

theorem stochDomAt_const_mul_right : StochDomAt (seqP sz0) sz0.size
    Xi (fun n u ω => 3 * Ze n u ω) :=
  StochDomAt.const_mul_right tendsto_sz0_size (by norm_num) Ze_nonneg prec_Xi_Ze

theorem stochDomAt_of_subset : StochDomAt (seqP sz0) sz0.size Xi Ze :=
  StochDomAt.of_subset prec_Xi_Ze fun τ hτ => ⟨τ, hτ, Eventually.of_forall fun _ => subset_rfl⟩

theorem stochDomAt_precomp : StochDomAt (seqP sz0) sz0.size (U := fun _ => Fin 2)
    (fun n _ ω => Xi n (() : Unit) ω) (fun n _ ω => Ze n (() : Unit) ω) :=
  StochDomAt.precomp_param (V := fun _ => Fin 2) prec_Xi_Ze (fun _ _ => ())

theorem stochDomAt_of_le_left : StochDomAt (seqP sz0) sz0.size
    (fun n u ω => Xi n u ω / 2) Ze :=
  StochDomAt.of_le_left (ξ₁ := Xi) (fun n u ω => by
    have := obs_nonneg n ω; unfold Xi; linarith) prec_Xi_Ze

theorem stochDomAt_zero_empty : StochDomAt (seqP sz0) sz0.size
    (fun _ (_ : Unit) _ => (0 : ℝ)) Ze :=
  StochDomAt.of_eventually_empty fun τ _ => Eventually.of_forall fun n => by
    ext ω
    simp only [badSetAt, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_exists, not_lt]
    intro u
    exact mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) (Ze_nonneg n u ω)

/-- `StochDomAt.of_unifDetDom` at `sz0`: the deterministic family `f = 1 ≤ g = 1` at the index
scale gives `1 ≺ 1` at the scale `N_n`, using `n ≤ N_n`. -/
theorem stochDomAt_of_unifDetDom : StochDomAt (seqP sz0) sz0.size (U := fun _ => Unit)
    (fun _ _ _ => (1 : ℝ)) (fun _ _ _ => (1 : ℝ)) :=
  StochDomAt.of_unifDetDom (f := fun _ _ => (1 : ℝ)) (g := fun _ _ => (1 : ℝ))
    (Eventually.of_forall sz0_self_le_size) (fun _ _ => zero_le_one)
    (UnifDetDom.of_le (fun _ _ => zero_le_one) fun _ _ => le_rfl)

theorem highProbAt_good : HighProbAt (seqP sz0) sz0.size
    (fun n => {ω | ∀ u, Xi n u ω ≤ ((sz0.size n : ℕ) : ℝ) ^ (1 / 10 : ℝ) * Ze n u ω}) :=
  StochDomAt.highProb prec_Xi_Ze (τ := 1 / 10) (by norm_num)

theorem highProbAt_inter : HighProbAt (seqP sz0) sz0.size (fun n =>
    {ω | ∀ u, Xi n u ω ≤ ((sz0.size n : ℕ) : ℝ) ^ (1 / 10 : ℝ) * Ze n u ω} ∩
    {ω | ∀ u, Xi n u ω ≤ ((sz0.size n : ℕ) : ℝ) ^ (1 / 10 : ℝ) * Ze n u ω}) :=
  HighProbAt.inter tendsto_sz0_size highProbAt_good highProbAt_good

theorem highProbAt_mono : HighProbAt (seqP sz0) sz0.size (fun _ => (Set.univ : Set (SeqΩ sz0))) :=
  HighProbAt.mono highProbAt_good (Eventually.of_forall fun _ => Set.subset_univ _)

theorem highProbAt_univ_ev :
    HighProbAt (seqP sz0) sz0.size (fun _ => (Set.univ : Set (SeqΩ sz0))) :=
  HighProbAt.of_eventually_univ (Eventually.of_forall fun _ ω => Set.mem_univ ω)

theorem highProbAt_biInter : HighProbAt (seqP sz0) sz0.size (fun n => ⋂ _k : Fin 2,
    {ω | ∀ u, Xi n u ω ≤ ((sz0.size n : ℕ) : ℝ) ^ (1 / 10 : ℝ) * Ze n u ω}) :=
  HighProbAt.biInter (K := fun _ => Fin 2) (C := 1) zero_le_one
    (by
      filter_upwards [tendsto_sz0_size.eventually (eventually_ge_atTop 2)] with n hn
      simpa using (show (2 : ℝ) ≤ (sz0.size n : ℝ) by exact_mod_cast hn))
    (fun D hD => by
      filter_upwards [highProbAt_good D hD] with n hn k using hn)

/-- `StochDomAt.of_subset_union` at `sz0` (the union of the bad events of `Xi ≺ Ze` and `Ze ≺ Ch`
contains that of `Xi ≺ Ze`; `trans`, `add`, `mul` use it with `τ/2`). -/
example : StochDomAt (seqP sz0) sz0.size Xi Ze :=
  StochDomAt.of_subset_union tendsto_sz0_size prec_Xi_Ze prec_Ze_Ch fun τ hτ =>
    ⟨τ, hτ, Eventually.of_forall fun _ => Set.subset_union_left⟩

/-- `Path.highProbAt_iInter` (the grid union bound, event form) at `sz0` on `Fin 2`. -/
example : HighProbAt (seqP sz0) sz0.size (fun n => ⋂ _k : Fin 2,
    {ω | ∀ u, Xi n u ω ≤ ((sz0.size n : ℕ) : ℝ) ^ (1 / 10 : ℝ) * Ze n u ω}) :=
  Path.highProbAt_iInter (seqP sz0) sz0.size (K := fun _ => Fin 2) (C := 1) zero_le_one
    (by
      filter_upwards [tendsto_sz0_size.eventually (eventually_ge_atTop 2)] with n hn
      simpa using (show (2 : ℝ) ≤ (sz0.size n : ℝ) by exact_mod_cast hn))
    (fun D hD => by
      filter_upwards [highProbAt_good D hD] with n hn k using hn)

theorem highProbAt_nonempty : ∀ᶠ n in atTop, ({ω | ∀ u, Xi n u ω ≤
    ((sz0.size n : ℕ) : ℝ) ^ (1 / 10 : ℝ) * Ze n u ω} : Set (SeqΩ sz0)).Nonempty :=
  HighProbAt.nonempty tendsto_sz0_size measure_univ highProbAt_good

/-- `StochDomAt.of_add_le`: `obs ≺ (1 + obs) + 1` with `1 ≤ 1 + obs` and `1 ≤ N^0` gives
`obs ≺ 1 + obs`. -/
theorem stochDomAt_of_add_le : StochDomAt (seqP sz0) sz0.size Xi Ze :=
  StochDomAt.of_add_le tendsto_sz0_size (ε := fun _ => 1) (b := 0)
    (Eventually.of_forall fun n u ω => by
      have := obs_nonneg n ω; simp [Ze]; linarith)
    (Eventually.of_forall fun n => by simp)
    (Sizes.prec_of_le sz0 (fun n u ω => by have := Ze_nonneg n u ω; linarith)
      fun n u ω => by have := obs_nonneg n ω; unfold Xi Ze; linarith)

/-- `StochDomAt.of_highProbAt_add_rpow_neg`: both w.h.p. hypotheses hold surely here. -/
theorem stochDomAt_of_highProb_add : StochDomAt (seqP sz0) sz0.size Xi Ze :=
  StochDomAt.of_highProbAt_add_rpow_neg tendsto_sz0_size (b := 0)
    (HighProbAt.of_eventually_univ (Eventually.of_forall fun n ω u => by
      have := obs_nonneg n ω; simp [Ze]; linarith))
    (fun τ hτ D hD => HighProbAt.of_eventually_univ (Eventually.of_forall fun n ω u => by
      have h0 := obs_nonneg n ω
      have h1 : (1 : ℝ) ≤ ((sz0.size n : ℕ) : ℝ) ^ τ :=
        Real.one_le_rpow (by exact_mod_cast Sizes.one_le_size sz0 n) hτ.le
      have h2 : 0 ≤ ((sz0.size n : ℕ) : ℝ) ^ (-D) := Real.rpow_nonneg (Nat.cast_nonneg _) _
      unfold Xi Ze
      nlinarith))

/-- `le_rpow_mul_of_le_add_rpow_neg` and `two_mul_le_mul_self` at numbers: `N = 4`, `τ = 2`,
`b = 0`, `x = y = 1`, `ε = 0`. -/
example : (1 : ℝ) ≤ ((4 : ℕ) : ℝ) ^ (2 : ℝ) * 1 :=
  le_rpow_mul_of_le_add_rpow_neg (N := 4) (τ := 2) (b := 0) (x := 1) (y := 1) (ε := 0) two_pos
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

example : 2 * ((4 : ℝ) * 1) ≤ 4 * 4 * 1 :=
  two_mul_le_mul_self (a := 4) (y := 1) (by norm_num) zero_le_one

/-- `NormStochDomAt` at `sz0` (norm of the real family `obs`), and `normStochDom_iff_at_id` on the
positive family `Ze`.  (`example`s, not theorems: see the `PerTimeDomAt` example above.) -/
example : NormStochDomAt (seqP sz0) sz0.size (fun n (_ : Unit) ω => obs n ω) Ze :=
  Sizes.prec_of_le sz0 Ze_nonneg fun n u ω => by
    have := obs_nonneg n ω
    simp only [Real.norm_eq_abs, abs_of_nonneg this, Ze]; linarith

example : NormStochDom (seqP sz0) Ze Ze :=
  (normStochDom_iff_at_id (seqP sz0) Ze Ze).mpr
    (StochDomAt.of_le_left (ξ₁ := Ze) (fun l u ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (Ze_nonneg l u ω)])
      (StochDomAt.refl tendsto_id Ze_nonneg))

/-- `perTimeDomAt_iff_forall_section` at `sz0` on `Fin 2`: the per-time bound (`perTimeOfStochDomAt`
at `stochDomAt_Fin2`) gives `StochDomAt` along every section. -/
theorem stochDomAt_section (u : ℕ → Fin 2) : StochDomAt (seqP sz0) sz0.size
    (fun n (_ : Unit) ω => Xi n () ω) (fun n (_ : Unit) ω => Ze n () ω) :=
  (Path.perTimeDomAt_iff_forall_section (seqP sz0) sz0.size (fun _ => ⟨0⟩)
    (U := fun _ => Fin 2) (fun n _ ω => Xi n () ω) (fun n _ ω => Ze n () ω)).mp
    (Path.perTimeOfStochDomAt (seqP sz0) sz0.size _ _ stochDomAt_Fin2) u

end RBM.Gauss.StochDomAtInst
