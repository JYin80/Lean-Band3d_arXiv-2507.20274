/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Universality.ZeroModeProfile
import RBM3D.Universality.PinsK

/-!
# UN-51g: the model-generic OU-layer interface (T2282)

The profile structure `UNOUProfile K` (T-class data of a kind), the pins `UNOUProfRowk`, `UNOULLk`,
`UNOUEq747k`, the rows `UNG1Rowk`, `UNG2bRowk` (definitions only), the generic assembly
`ouDiagk_of_ouLLk` (Markov and a union bound inside `ouP (K.M sz).toUNModel`, on the centred carrier
`ouMatC (K.M sz)`; copy of the merged `ouDiag_of_ouLL`, `ZeroModeProfile.lean:641`), `ouRowk_of_pins`,
and the band bridges that make T2276's `UNOULL`, `UNOUEq747`, `UNG1Row`, `UNG2bRow` the band instance
(pattern of `UNOUQUEk_band`, `PinsK.lean:522`).

Design (T2282a/b): the bulk condition sits inside `∀ᶠ n` in `UNOULLk`/`UNOUEq747k`; at the band kind the
two forms are equivalent by a padding argument (`OUInterfaceK_pad`).  `UNG2bRowk` has no `τ_U` bound.
Not proved here: `UNOULLk`, `UNOUEq747k`, `UNG1Rowk` (UN-51), `UNG2bRowk` (UN-52), `UNOUProfRowk` at
`UNKind.ba` (BA-C3).  Helpers that the ticket does not pin are `private` with the prefix `OUInterfaceK_`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

namespace RBM.Univ

open MeasureTheory Filter Matrix Topology
open RBM RBM.Gauss RBM.Gauss.Sizes RBM.Endpoints
open scoped NNReal ENNReal

/-! ## 2. Vocabulary (target §1; copied verbatim into `RBM.Univ`) -/

/-- **The OU-layer profile of a kind** (T-class data, supplied by the kind's twin: band
`UNOUProfile.band` from `ZeroModeProfile`; block Anderson: BA-C3 `BA/GUEEntry`).  `pm sz n ζ z a b`
and `pp sz n ζ z a b` are the two-loop profiles `|m|² Θ̃^{(+,-)}_{ab}/W^d`, `m² Θ̃^{(+,+)}_{ab}/W^d`
of `𝐇_t` at `ζ = ζ(t)` (`S̃ = (1 - ζ) S + ζ N⁻¹ J`).  The kind `K` is a phantom index: it records
which model the profile belongs to ("two data, one model", DECISIONS §66 (5)). -/
structure UNOUProfile {d : ℕ} (K : UNKind d) where
  pm : ∀ sz : Sizes d, ∀ n : ℕ, ℝ → ℂ → Zd d (sz.L n) → Zd d (sz.L n) → ℂ
  pp : ∀ sz : Sizes d, ∀ n : ℕ, ℝ → ℂ → Zd d (sz.L n) → Zd d (sz.L n) → ℂ

/-- The band profile: `profPMTilde`, `profPPTilde` (T2276, `ZeroModeProfile.lean:88, 93`). -/
noncomputable def UNOUProfile.band (d : ℕ) : UNOUProfile (UNKind.band d) where
  pm := fun sz n ζ z a b => profPMTilde sz n ζ z a b
  pp := fun sz n ζ z a b => profPPTilde sz n ζ z a b

/-! ## 3. Pins of the generic interface (target §2; new `Prop`s) -/

/-- **`UNOUProfRowk`** (T-class; band: `profTilde_rowDiff` verbatim, BA: BA-C3): row differences of
the profile, `C lam⁻² W^{-d}` with `C = C(d, 𝔡, κ)`, uniformly in `ζ ∈ [0,1]` and `z` in the kind's bulk. -/
def UNOUProfRowk {d : ℕ} (K : UNKind d) (P : UNOUProfile K) : Prop :=
  ∀ 𝔡 κ : ℝ, 0 < 𝔡 → 0 < κ → ∃ C : ℝ, 0 < C ∧
    ∀ (sz : Sizes d) (n : ℕ), 0 < sz.lam n → sz.lam n ≤ 𝔡⁻¹ →
      ∀ z : ℂ, 0 < z.im → z.im ≤ 1 → K.bulk sz κ z.re n → ∀ ζ : ℝ, 0 ≤ ζ → ζ ≤ 1 →
        ∀ a b b' : Zd d (sz.L n),
          ‖P.pm sz n ζ z a b - P.pm sz n ζ z a b'‖ ≤
              C * (sz.lam n ^ 2)⁻¹ / ((sz.W n : ℕ) : ℝ) ^ d ∧
          ‖P.pp sz n ζ z a b - P.pp sz n ζ z a b'‖ ≤
              C * (sz.lam n ^ 2)⁻¹ / ((sz.W n : ℕ) : ℝ) ^ d

/-- **`UNOULLk`**: `UNOULL` for the kind `K` (carrier `ouMatC (K.M sz)`, law `ouP (K.M sz).toUNModel`);
the bulk condition sits inside `∀ᶠ n` (for every energy sequence, eventually: if `E n` is in the
bulk at `n`, the moment bound holds), so that a kind whose bulk is empty at some `n` is not vacuous. -/
def UNOULLk {d : ℕ} (K : UNKind d) (sz : Sizes d) (τU : ℝ) : Prop :=
  ∀ κ : ℝ, 0 < κ → ∀ E : ℕ → ℝ,
    ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n ∧ t n ≤ ouTStar sz τU n) → ∀ δ : ℝ, 0 < δ → ∀ p : ℕ,
      ∀ᶠ n in atTop, K.bulk sz κ (E n) n → ∀ x : Idx d (sz.L n) (sz.W n),
        ∫ ω, ‖Gres (ouMatC (K.M sz) n (t n) ω)
            ((E n : ℂ) + ((ouEtaLL sz τU n : ℝ) : ℂ) * Complex.I) true x x‖ ^ (2 * p)
          ∂(ouP (K.M sz).toUNModel n) ≤ Nsz sz n ^ δ

/-- **`UNOUEq747k`**: `UNOUEq747` for the kind `K` with the profile `P`: the expectation half of
`QDiff` for `𝐇_t` at the QUE scale `z_n = E_n + i η_Q` (`η_Q = ouEtaQ sz 𝔡 n`, fixed by the window of
`UNOUQUEk`), error `qdBoundExp sz n τ η_Q` (supervisor 0956 O3), profile `P` at `ζ(t_n)`; bulk inside `∀ᶠ n`. -/
def UNOUEq747k {d : ℕ} (K : UNKind d) (P : UNOUProfile K) (sz : Sizes d) (𝔡 τU : ℝ) : Prop :=
  ∀ κ : ℝ, 0 < κ → ∀ E : ℕ → ℝ,
    ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n ∧ t n ≤ ouTStar sz τU n) → ∀ τ : ℝ, 0 < τ →
      ∀ᶠ n in atTop, K.bulk sz κ (E n) n → ∀ a b : Zd d (sz.L n),
        ‖(∫ ω, avg2 sz n (fun x y => ((‖Gres (ouMatC (K.M sz) n (t n) ω)
              ((E n : ℂ) + ((ouEtaQ sz 𝔡 n : ℝ) : ℂ) * Complex.I) true x y‖ ^ 2 : ℝ) : ℂ)) a b
            ∂(ouP (K.M sz).toUNModel n)) -
          P.pm sz n (ouZeta (t n)) ((E n : ℂ) + ((ouEtaQ sz 𝔡 n : ℝ) : ℂ) * Complex.I) a b‖ ≤
            qdBoundExp sz n τ (ouEtaQ sz 𝔡 n) ∧
        ‖(∫ ω, avg2 sz n (fun x y =>
              Gres (ouMatC (K.M sz) n (t n) ω)
                ((E n : ℂ) + ((ouEtaQ sz 𝔡 n : ℝ) : ℂ) * Complex.I) true x y *
              Gres (ouMatC (K.M sz) n (t n) ω)
                ((E n : ℂ) + ((ouEtaQ sz 𝔡 n : ℝ) : ℂ) * Complex.I) true y x) a b
            ∂(ouP (K.M sz).toUNModel n)) -
          P.pp sz n (ouZeta (t n)) ((E n : ℂ) + ((ouEtaQ sz 𝔡 n : ℝ) : ℂ) * Complex.I) a b‖ ≤
            qdBoundExp sz n τ (ouEtaQ sz 𝔡 n)

/-- **Row `UNG1Rowk`** (UN-51, `RandomLayerB` `g1Rowk`, class P): the two layer pins of every kind
from the kind's inputs `ML`, `Loc`, `Que` (band: `∀ d, UNMLOut d`, `UNLocAvgBand`, `UNQueBand`;
BA: `∀ d, UNMLOutBA d`, `UNLocAvgBA`, `UNQueBA`), at `τ_U ≤ ouTauMax 𝔠 𝔡`. -/
def UNG1Rowk (K : ∀ d, UNKind d) (P : ∀ d, UNOUProfile (K d)) (ML Loc Que : Prop) : Prop :=
  ML → Loc → Que →
    ∀ d : ℕ, 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 →
      ∀ τU : ℝ, 0 < τU → τU ≤ ouTauMax 𝔠 𝔡 →
        UNOULLk (K d) sz τU ∧ UNOUEq747k (K d) (P d) sz 𝔡 τU

/-- **Row `UNG2bRowk`** (UN-52, `QUEFlow` `g2bRowk`, class P): `UNOUQUEk` from `UNOUEq747k` and the
profile's row differences, for every kind and profile; no `τ_U ≤ ouTauMax` (supervisor 0956 O2). -/
def UNG2bRowk (K : ∀ d, UNKind d) (P : ∀ d, UNOUProfile (K d)) : Prop :=
  ∀ d : ℕ, 3 ≤ d → UNOUProfRowk (K d) (P d) → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 →
    ∀ τU : ℝ, 0 < τU → UNOUEq747k (K d) (P d) sz 𝔡 τU → UNOUQUEk (K d) sz 𝔡 τU

/-! ## 4. Generic assembly: `UNOUDiagk` from `UNOULLk` -/

/-- Uniformization over admissible parameter sequences (copy of the private
`ZeroModeProfile_eventually_forall_mem_of_forall_seq'`, `ZeroModeProfile.lean:547`; pure filter combinatorics). -/
private theorem OUInterfaceK_eventually_forall_mem_of_forall_seq {α : Type*} {T : ℕ → Set α}
    (hT : ∀ n, (T n).Nonempty) {P : ℕ → α → Prop}
    (h : ∀ s : ℕ → α, (∀ n, s n ∈ T n) → ∀ᶠ n in atTop, P n (s n)) :
    ∀ᶠ n in atTop, ∀ a ∈ T n, P n a := by
  classical
  by_contra hcon
  rw [Filter.not_eventually] at hcon
  have hcon' : ∃ᶠ n in atTop, ∃ a, a ∈ T n ∧ ¬ P n a := by
    refine hcon.mono ?_
    intro n hn
    push Not at hn
    exact hn
  set g : ℕ → α := fun n =>
    if hn : ∃ a, a ∈ T n ∧ ¬ P n a then hn.choose else (hT n).choose with hg
  have hgmem : ∀ n, g n ∈ T n := by
    intro n
    by_cases hn : ∃ a, a ∈ T n ∧ ¬ P n a
    · simp only [hg, hn, dite_true]
      exact hn.choose_spec.1
    · simp only [hg, hn, dite_false]
      exact (hT n).choose_spec
  have hbad : ∀ n, (∃ a, a ∈ T n ∧ ¬ P n a) → ¬ P n (g n) := by
    intro n hn
    have hgn : g n = hn.choose := by simp only [hg, hn, dite_true]
    rw [hgn]
    exact hn.choose_spec.2
  have heven : ∀ᶠ n in atTop, P n (g n) := h g hgmem
  obtain ⟨n, hn1, hn2⟩ := (hcon'.and_eventually heven).exists
  exact hbad n hn1 hn2

section DiagMarkovK

variable {d : ℕ} {sz : Sizes d}

open scoped Matrix.Norms.L2Operator in
private theorem OUInterfaceK_norm_entry_le (M : UNModelC sz) (n : ℕ) (t : ℝ)
    (ω : SeqΩ sz × Ω d (sz.L n) (sz.W n)) {z : ℂ} {η : ℝ} (hη : 0 < η)
    (hz : η ≤ |z.im|) (x y : Idx d (sz.L n) (sz.W n)) :
    ‖Gres (ouMatC M n t ω) z true x y‖ ≤ η⁻¹ :=
  (RBM.Ind.norm_apply_le_l2_opNorm _ x y).trans
    (norm_Gsig_le_inv_eta (ouMatC_isHermitian M n t ω) hη hz true)

/-- `ω ↦ ouMatC M n t ω` is measurable (`ouMatC = ouMat + constant`, `ouMatC_eq_ouMat_add`). -/
private theorem OUInterfaceK_measurable_ouMatC (M : UNModelC sz) (n : ℕ) (t : ℝ) :
    Measurable (ouMatC M n t) := by
  have h : ouMatC M n t =
      fun ω => ouMat M.toUNModel n t ω + (1 - Real.exp (-t / 2)) • M.mean n :=
    funext (ouMatC_eq_ouMat_add M n t)
  rw [h]
  exact (measurable_ouMat M.toUNModel n t).add_const _

/-- Markov for one diagonal entry on the centred carrier (copy of `ZeroModeProfile_markov`,
`ZeroModeProfile.lean:596`). -/
private theorem OUInterfaceK_markov (M : UNModelC sz) (n : ℕ) (t : ℝ) {z : ℂ} {η : ℝ} (hη : 0 < η)
    (hz : z.im = η) (x : Idx d (sz.L n) (sz.W n)) (p : ℕ) {N ε δ : ℝ} (hN : 1 ≤ N)
    (hmom : ∫ ω, ‖Gres (ouMatC M n t ω) z true x x‖ ^ (2 * p)
      ∂(ouP M.toUNModel n) ≤ N ^ δ) :
    ouP M.toUNModel n {ω | N ^ ε < ‖Gres (ouMatC M n t ω) z true x x‖} ≤
      ENNReal.ofReal (N ^ (δ - 2 * p * ε)) := by
  have hN0 : 0 < N := by linarith
  set μ := ouP M.toUNModel n with hμ
  set f : SeqΩ sz × Ω d (sz.L n) (sz.W n) → ℝ :=
    fun ω => ‖Gres (ouMatC M n t ω) z true x x‖ ^ (2 * p) with hf
  have hfm : Measurable f :=
    (((walk_measurable_Gres_apply z true x x).comp
      (OUInterfaceK_measurable_ouMatC M n t)).norm).pow_const (2 * p)
  have hfi : Integrable f μ := by
    refine Integrable.of_bound hfm.aestronglyMeasurable ((η⁻¹) ^ (2 * p)) (ae_of_all _ fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact pow_le_pow_left₀ (norm_nonneg _)
      (OUInterfaceK_norm_entry_le M n t ω hη (by rw [hz]; exact le_abs_self _) x x) _
  have hM := mul_meas_ge_le_integral_of_nonneg (μ := μ) (f := f)
    (ae_of_all _ fun ω => by positivity) hfi (N ^ (2 * p * ε))
  have hsub : {ω | N ^ ε < ‖Gres (ouMatC M n t ω) z true x x‖} ⊆
      {ω | N ^ (2 * p * ε) ≤ f ω} := by
    intro ω hω
    have h1 : (N ^ ε) ^ (2 * p) ≤ ‖Gres (ouMatC M n t ω) z true x x‖ ^ (2 * p) :=
      pow_le_pow_left₀ (Real.rpow_nonneg hN0.le _) (le_of_lt hω) _
    have h2 : (N ^ ε) ^ (2 * p) = N ^ (2 * p * ε) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]
      congr 1
      push_cast
      ring
    change N ^ (2 * p * ε) ≤ ‖Gres (ouMatC M n t ω) z true x x‖ ^ (2 * p)
    rw [← h2]
    exact h1
  have hreal : μ.real {ω | N ^ (2 * p * ε) ≤ f ω} ≤ N ^ (δ - 2 * p * ε) := by
    have hpos : 0 < N ^ (2 * p * ε) := Real.rpow_pos_of_pos hN0 _
    have h3 : N ^ (2 * p * ε) * μ.real {ω | N ^ (2 * p * ε) ≤ f ω} ≤ N ^ δ := hM.trans hmom
    rw [Real.rpow_sub hN0, le_div_iff₀ hpos]
    linarith
  calc μ {ω | N ^ ε < ‖Gres (ouMatC M n t ω) z true x x‖}
      ≤ μ {ω | N ^ (2 * p * ε) ≤ f ω} := measure_mono hsub
    _ = ENNReal.ofReal (μ.real {ω | N ^ (2 * p * ε) ≤ f ω}) :=
        (ofReal_measureReal (measure_ne_top _ _)).symm
    _ ≤ ENNReal.ofReal (N ^ (δ - 2 * p * ε)) := ENNReal.ofReal_le_ofReal hreal

end DiagMarkovK

/-- **`UNOUDiagk` from the per-sequence moment pin `UNOULLk`, for every kind.**  Uniformization over
`(t, E)` on `T n = {0 ≤ t ≤ ouTStar}` (nonempty; the bulk condition is inside the predicate, so it is
not used to build the sequence), Markov for `E ‖G_{xx}‖^{2p} ≤ N^ε` with `2pε ≥ 1 + ε + D`, and the
union bound over the `N` indices `x` inside `ouP (K.M sz).toUNModel` (copy of `ouDiag_of_ouLL`,
`ZeroModeProfile.lean:641`, without its `κ > 2` case). -/
theorem ouDiagk_of_ouLLk :
    ∀ {d : ℕ} {K : UNKind d} {sz : Sizes d} {τU : ℝ}, UNOULLk K sz τU → UNOUDiagk K sz τU := by
  intro d K sz τU h κ ε D hκ hε hD
  obtain ⟨p, hp⟩ : ∃ p : ℕ, 1 + ε + D ≤ 2 * (p : ℝ) * ε := by
    refine ⟨⌈(1 + ε + D) / (2 * ε)⌉₊, ?_⟩
    have := Nat.le_ceil ((1 + ε + D) / (2 * ε))
    rw [div_le_iff₀ (by positivity)] at this
    linarith
  have hT : ∀ n, ({a : ℝ × ℝ | 0 ≤ a.1 ∧ a.1 ≤ ouTStar sz τU n}).Nonempty := by
    intro n
    exact ⟨(0, 0), le_rfl, Real.rpow_nonneg (Nat.cast_nonneg _) _⟩
  have key := OUInterfaceK_eventually_forall_mem_of_forall_seq
    (P := fun n (a : ℝ × ℝ) => K.bulk sz κ a.2 n → ∀ x : Idx d (sz.L n) (sz.W n),
      ∫ ω, ‖Gres (ouMatC (K.M sz) n a.1 ω)
          ((a.2 : ℂ) + ((ouEtaLL sz τU n : ℝ) : ℂ) * Complex.I) true x x‖ ^ (2 * p)
        ∂(ouP (K.M sz).toUNModel n) ≤ Nsz sz n ^ ε) hT
    (fun s hs => h κ hκ (fun n => (s n).2) (fun n => (s n).1)
      (fun n => ⟨(hs n).1, (hs n).2⟩) ε hε p)
  filter_upwards [key] with n hn t ht0 ht E hE
  have hsz : 1 ≤ Nsz sz n := by
    have : 1 ≤ sz.size n := by
      have h1 := sz.three_le_L n
      have h2 := sz.W_pos n
      simp only [Sizes.size]
      exact Nat.one_le_pow _ _ (Nat.mul_pos h2 (by omega))
    exact_mod_cast this
  set N : ℝ := Nsz sz n with hN
  have hN0 : 0 < N := by linarith
  have hη : 0 < ouEtaLL sz τU n := Real.rpow_pos_of_pos hN0 _
  have hmom := hn (t, E) ⟨ht0, ht⟩ hE
  have hbd : ∀ x : Idx d (sz.L n) (sz.W n),
      ouP (K.M sz).toUNModel n {ω | N ^ ε < ‖Gres (ouMatC (K.M sz) n t ω)
        ((E : ℂ) + ((ouEtaLL sz τU n : ℝ) : ℂ) * Complex.I) true x x‖} ≤
      ENNReal.ofReal (N ^ (ε - 2 * p * ε)) := fun x =>
    OUInterfaceK_markov (K.M sz) n t hη (by simp) x p hsz (hmom x)
  have hset : {ω | ∃ x : Idx d (sz.L n) (sz.W n), N ^ ε < ‖Gres (ouMatC (K.M sz) n t ω)
      ((E : ℂ) + ((ouEtaLL sz τU n : ℝ) : ℂ) * Complex.I) true x x‖} =
      ⋃ x : Idx d (sz.L n) (sz.W n), {ω | N ^ ε < ‖Gres (ouMatC (K.M sz) n t ω)
        ((E : ℂ) + ((ouEtaLL sz τU n : ℝ) : ℂ) * Complex.I) true x x‖} := by
    ext ω; simp
  have hcard : (Fintype.card (Idx d (sz.L n) (sz.W n)) : ℝ) = N := by
    rw [Sizes.card_Idx]
  change ouP (K.M sz).toUNModel n {ω | ∃ x : Idx d (sz.L n) (sz.W n),
      N ^ ε < ‖Gres (ouMatC (K.M sz) n t ω)
        ((E : ℂ) + ((ouEtaLL sz τU n : ℝ) : ℂ) * Complex.I) true x x‖} ≤ ENNReal.ofReal (N ^ (-D))
  rw [hset]
  calc ouP (K.M sz).toUNModel n (⋃ x : Idx d (sz.L n) (sz.W n), {ω | N ^ ε <
        ‖Gres (ouMatC (K.M sz) n t ω)
          ((E : ℂ) + ((ouEtaLL sz τU n : ℝ) : ℂ) * Complex.I) true x x‖})
      ≤ ∑ x : Idx d (sz.L n) (sz.W n), ouP (K.M sz).toUNModel n {ω | N ^ ε <
        ‖Gres (ouMatC (K.M sz) n t ω)
          ((E : ℂ) + ((ouEtaLL sz τU n : ℝ) : ℂ) * Complex.I) true x x‖} :=
        measure_iUnion_fintype_le _ _
    _ ≤ ∑ _x : Idx d (sz.L n) (sz.W n), ENNReal.ofReal (N ^ (ε - 2 * p * ε)) :=
        Finset.sum_le_sum fun x _ => hbd x
    _ = ENNReal.ofReal (N * N ^ (ε - 2 * p * ε)) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ENNReal.ofReal_mul hN0.le]
        congr 1
        rw [← hcard]
        exact (ENNReal.ofReal_natCast _).symm
    _ ≤ ENNReal.ofReal (N ^ (-D)) := by
        apply ENNReal.ofReal_le_ofReal
        calc N * N ^ (ε - 2 * p * ε) = N ^ (1 + (ε - 2 * p * ε)) := by
              rw [Real.rpow_add hN0, Real.rpow_one]
          _ ≤ N ^ (-D) := Real.rpow_le_rpow_of_exponent_le hsz (by linarith)

/-! ## 5. The assembly -/

/-- **The assembly** (copy of `ouRow_of_pins`, `ZeroModeProfile.lean:719`, for every kind): the row
differences of the profile, `UNG1Rowk` and `UNG2bRowk` give `UNOURowk K ML Loc Que` with
`τ₀ = ouTauMax 𝔠 𝔡`; the `UNOUDiagk` half is `ouDiagk_of_ouLLk`. -/
theorem ouRowk_of_pins (K : ∀ d, UNKind d) (P : ∀ d, UNOUProfile (K d)) {ML Loc Que : Prop}
    (hprof : ∀ d : ℕ, 3 ≤ d → UNOUProfRowk (K d) (P d)) :
    UNG1Rowk K P ML Loc Que → UNG2bRowk K P → UNOURowk K ML Loc Que := by
  intro r1 r2b hML hLoc hQ d hd 𝔠 𝔡 sz hA
  refine ⟨ouTauMax 𝔠 𝔡, ouTauMax_pos hA.1 hA.2.1, fun τU hτ hle => ?_⟩
  have h1 := r1 hML hLoc hQ d hd 𝔠 𝔡 sz hA τU hτ hle
  exact ⟨r2b d hd (hprof d hd) 𝔠 𝔡 sz hA τU hτ h1.2, ouDiagk_of_ouLLk h1.1⟩

/-! ## 6. Band bridges: T2276's pins are the band instance -/

/-- Padding: the per-sequence form with the bulk condition outside (`∀ n, |E n| ≤ 2 - κ`) is
equivalent to the form with the bulk condition inside `∀ᶠ n` (`κ > 2`: both vacuous; `κ ≤ 2`: replace
`E n` by `0` where `|E n| > 2 - κ`; the two agree eventually where the bulk condition holds). -/
private theorem OUInterfaceK_pad (κ : ℝ) (Q : ℕ → ℝ → Prop) :
    (∀ E : ℕ → ℝ, (∀ n, |E n| ≤ 2 - κ) → ∀ᶠ n in atTop, Q n (E n)) ↔
      ∀ E : ℕ → ℝ, ∀ᶠ n in atTop, |E n| ≤ 2 - κ → Q n (E n) := by
  constructor
  · intro h E
    by_cases hκ : 2 < κ
    · exact Eventually.of_forall fun n hn => by
        exfalso
        have := abs_nonneg (E n)
        linarith
    · push Not at hκ
      set E' : ℕ → ℝ := fun n => if |E n| ≤ 2 - κ then E n else 0 with hE'
      have hE'b : ∀ n, |E' n| ≤ 2 - κ := by
        intro n
        by_cases hn : |E n| ≤ 2 - κ
        · simp only [hE', hn, ↓reduceIte]
        · simp only [hE', hn, ↓reduceIte, abs_zero]; linarith
      filter_upwards [h E' hE'b] with n hn hb
      have : E' n = E n := by simp only [hE', hb, ↓reduceIte]
      rwa [this] at hn
  · intro h E hE
    filter_upwards [h E] with n hn
    exact hn (hE n)

theorem unOUProfRowk_band :
    ∀ {d : ℕ}, 3 ≤ d → UNOUProfRowk (UNKind.band d) (UNOUProfile.band d) :=
  fun {d} hd 𝔡 κ h𝔡 hκ => profTilde_rowDiff d hd 𝔡 κ h𝔡 hκ

theorem UNOULLk_band :
    ∀ {d : ℕ} (sz : Sizes d) (τU : ℝ), UNOULLk (UNKind.band d) sz τU ↔ UNOULL sz τU := by
  intro d sz τU
  unfold UNOULLk UNOULL
  rw [unPinsK_band_M, ouMatC_toC]
  constructor
  · intro h κ hκ E hE t ht δ hδ p
    exact (OUInterfaceK_pad κ (fun n e => ∀ x : Idx d (sz.L n) (sz.W n),
        ∫ ω, ‖Gres (ouMat (UNModel.band sz) n (t n) ω)
            ((e : ℂ) + ((ouEtaLL sz τU n : ℝ) : ℂ) * Complex.I) true x x‖ ^ (2 * p)
          ∂(ouP (UNModel.band sz) n) ≤ Nsz sz n ^ δ)).2
      (fun E => h κ hκ E t ht δ hδ p) E hE
  · intro h κ hκ E t ht δ hδ p
    exact (OUInterfaceK_pad κ (fun n e => ∀ x : Idx d (sz.L n) (sz.W n),
        ∫ ω, ‖Gres (ouMat (UNModel.band sz) n (t n) ω)
            ((e : ℂ) + ((ouEtaLL sz τU n : ℝ) : ℂ) * Complex.I) true x x‖ ^ (2 * p)
          ∂(ouP (UNModel.band sz) n) ≤ Nsz sz n ^ δ)).1
      (fun E hE => h κ hκ E hE t ht δ hδ p) E

theorem UNOUEq747k_band :
    ∀ {d : ℕ} (sz : Sizes d) (𝔡 τU : ℝ),
      UNOUEq747k (UNKind.band d) (UNOUProfile.band d) sz 𝔡 τU ↔ UNOUEq747 sz 𝔡 τU := by
  intro d sz 𝔡 τU
  unfold UNOUEq747k UNOUEq747
  rw [unPinsK_band_M, ouMatC_toC]
  constructor
  · intro h κ hκ E hE t ht τ hτ
    exact (OUInterfaceK_pad κ (fun n e => ∀ a b : Zd d (sz.L n),
        ‖(∫ ω, avg2 sz n (fun x y => ((‖Gres (ouMat (UNModel.band sz) n (t n) ω)
              ((e : ℂ) + ((ouEtaQ sz 𝔡 n : ℝ) : ℂ) * Complex.I) true x y‖ ^ 2 : ℝ) : ℂ)) a b
            ∂(ouP (UNModel.band sz) n)) -
          profPMTilde sz n (ouZeta (t n)) ((e : ℂ) + ((ouEtaQ sz 𝔡 n : ℝ) : ℂ) * Complex.I) a b‖ ≤
            qdBoundExp sz n τ (ouEtaQ sz 𝔡 n) ∧
        ‖(∫ ω, avg2 sz n (fun x y =>
              Gres (ouMat (UNModel.band sz) n (t n) ω)
                ((e : ℂ) + ((ouEtaQ sz 𝔡 n : ℝ) : ℂ) * Complex.I) true x y *
              Gres (ouMat (UNModel.band sz) n (t n) ω)
                ((e : ℂ) + ((ouEtaQ sz 𝔡 n : ℝ) : ℂ) * Complex.I) true y x) a b
            ∂(ouP (UNModel.band sz) n)) -
          profPPTilde sz n (ouZeta (t n)) ((e : ℂ) + ((ouEtaQ sz 𝔡 n : ℝ) : ℂ) * Complex.I) a b‖ ≤
            qdBoundExp sz n τ (ouEtaQ sz 𝔡 n))).2
      (fun E => h κ hκ E t ht τ hτ) E hE
  · intro h κ hκ E t ht τ hτ
    exact (OUInterfaceK_pad κ (fun n e => ∀ a b : Zd d (sz.L n),
        ‖(∫ ω, avg2 sz n (fun x y => ((‖Gres (ouMat (UNModel.band sz) n (t n) ω)
              ((e : ℂ) + ((ouEtaQ sz 𝔡 n : ℝ) : ℂ) * Complex.I) true x y‖ ^ 2 : ℝ) : ℂ)) a b
            ∂(ouP (UNModel.band sz) n)) -
          profPMTilde sz n (ouZeta (t n)) ((e : ℂ) + ((ouEtaQ sz 𝔡 n : ℝ) : ℂ) * Complex.I) a b‖ ≤
            qdBoundExp sz n τ (ouEtaQ sz 𝔡 n) ∧
        ‖(∫ ω, avg2 sz n (fun x y =>
              Gres (ouMat (UNModel.band sz) n (t n) ω)
                ((e : ℂ) + ((ouEtaQ sz 𝔡 n : ℝ) : ℂ) * Complex.I) true x y *
              Gres (ouMat (UNModel.band sz) n (t n) ω)
                ((e : ℂ) + ((ouEtaQ sz 𝔡 n : ℝ) : ℂ) * Complex.I) true y x) a b
            ∂(ouP (UNModel.band sz) n)) -
          profPPTilde sz n (ouZeta (t n)) ((e : ℂ) + ((ouEtaQ sz 𝔡 n : ℝ) : ℂ) * Complex.I) a b‖ ≤
            qdBoundExp sz n τ (ouEtaQ sz 𝔡 n))).1
      (fun E hE => h κ hκ E hE t ht τ hτ) E

theorem UNG1Rowk_band :
    UNG1Rowk (fun d => UNKind.band d) (fun d => UNOUProfile.band d)
        (∀ d : ℕ, UNMLOut d) UNLocAvgBand UNQueBand ↔ UNG1Row := by
  unfold UNG1Rowk UNG1Row
  constructor
  · intro h hML hLoc hQ d hd 𝔠 𝔡 sz hA τU hτ hle
    have h1 := h hML hLoc hQ d hd 𝔠 𝔡 sz hA τU hτ hle
    exact ⟨(UNOULLk_band sz τU).1 h1.1, (UNOUEq747k_band sz 𝔡 τU).1 h1.2⟩
  · intro h hML hLoc hQ d hd 𝔠 𝔡 sz hA τU hτ hle
    have h1 := h hML hLoc hQ d hd 𝔠 𝔡 sz hA τU hτ hle
    exact ⟨(UNOULLk_band sz τU).2 h1.1, (UNOUEq747k_band sz 𝔡 τU).2 h1.2⟩

theorem unG2bRow_of_k :
    UNG2bRowk (fun d => UNKind.band d) (fun d => UNOUProfile.band d) → UNG2bRow := by
  intro h d hd 𝔠 𝔡 sz hA τU hτ _ hE
  exact (UNOUQUEk_band sz 𝔡 τU).1
    (h d hd (unOUProfRowk_band hd) 𝔠 𝔡 sz hA τU hτ ((UNOUEq747k_band sz 𝔡 τU).2 hE))

theorem ouRow_of_pinsk_band :
    UNG1Rowk (fun d => UNKind.band d) (fun d => UNOUProfile.band d)
        (∀ d : ℕ, UNMLOut d) UNLocAvgBand UNQueBand →
      UNG2bRowk (fun d => UNKind.band d) (fun d => UNOUProfile.band d) → UNOURow :=
  fun r1 r2 =>
    UNOURowk_band.1
      (ouRowk_of_pins (fun d => UNKind.band d) (fun d => UNOUProfile.band d)
        (fun _ hd => unOUProfRowk_band hd) r1 r2)

/-- `UNOULL` from `UNOULLk` at the band (`UNOULLk_band.1`, stated with conclusion `UNOULL` so that the
registry scan (`RBM3D/Test/Axioms.lean`) sees `UNOULL` as proved from the owed `UNOULLk`). -/
theorem OUInterfaceK_UNOULL_of_k {d : ℕ} (sz : Sizes d) (τU : ℝ) :
    UNOULLk (UNKind.band d) sz τU → UNOULL sz τU :=
  (UNOULLk_band sz τU).1

/-- `UNG1Row` from `UNG1Rowk` at the band (`UNG1Rowk_band.1`, stated with conclusion `UNG1Row`; as
`OUInterfaceK_UNOULL_of_k`). -/
theorem OUInterfaceK_UNG1Row_of_k :
    UNG1Rowk (fun d => UNKind.band d) (fun d => UNOUProfile.band d)
        (∀ d : ℕ, UNMLOut d) UNLocAvgBand UNQueBand → UNG1Row :=
  UNG1Rowk_band.1

/-! ## 7. Compiled instances (`d = 3`, `sz0`; the owed pins stay hypotheses) -/

namespace OUInterfaceKInst

open RBM.Gauss.SizesInst

/-- `UNOUProfRowk` at the band kind, `d = 3`: no hypothesis. -/
theorem inst_profRow_band : UNOUProfRowk (UNKind.band 3) (UNOUProfile.band 3) :=
  unOUProfRowk_band le_rfl

/-- `ouDiagk_of_ouLLk` at `sz0`, `τ_U = 1/1000`: the pin `UNOULLk` (another gate's) stays a hypothesis. -/
theorem inst_ouDiagk_band :
    UNOULLk (UNKind.band 3) sz0 (1 / 1000) → UNOUDiagk (UNKind.band 3) sz0 (1 / 1000) :=
  ouDiagk_of_ouLLk

theorem inst_ouLLk_band : UNOULLk (UNKind.band 3) sz0 (1 / 1000) ↔ UNOULL sz0 (1 / 1000) :=
  UNOULLk_band sz0 (1 / 1000)

theorem inst_Eq747k_band :
    UNOUEq747k (UNKind.band 3) (UNOUProfile.band 3) sz0 (1 / 10) (1 / 1000) ↔
      UNOUEq747 sz0 (1 / 10) (1 / 1000) :=
  UNOUEq747k_band sz0 (1 / 10) (1 / 1000)

/-- `UNG1Rowk` at the band, applied at `sz0` (admissible at `𝔠 = 1/6`, `𝔡 = 1/10`),
`τ_U = 1/1000 ≤ ouTauMax = 1/720`. -/
theorem inst_g1k_band
    (r1 : UNG1Rowk (fun d => UNKind.band d) (fun d => UNOUProfile.band d)
      (∀ d : ℕ, UNMLOut d) UNLocAvgBand UNQueBand)
    (hML : ∀ d : ℕ, UNMLOut d) (hLoc : UNLocAvgBand) (hQ : UNQueBand) :
    UNOULLk (UNKind.band 3) sz0 (1 / 1000) ∧
      UNOUEq747k (UNKind.band 3) (UNOUProfile.band 3) sz0 (1 / 10) (1 / 1000) :=
  r1 hML hLoc hQ 3 le_rfl (1 / 6) (1 / 10) sz0 sz0_admissible (1 / 1000) (by norm_num)
    (by rw [show ouTauMax (1 / 6) (1 / 10) = 1 / 720 by unfold ouTauMax; norm_num [min_def]]
        norm_num)

theorem inst_g2b_of_k
    (r2 : UNG2bRowk (fun d => UNKind.band d) (fun d => UNOUProfile.band d)) : UNG2bRow :=
  unG2bRow_of_k r2

/-- `ouRowk_of_pins` at the band kind (the rows are other gates' pins). -/
theorem inst_ouRowk_band
    (r1 : UNG1Rowk (fun d => UNKind.band d) (fun d => UNOUProfile.band d)
      (∀ d : ℕ, UNMLOut d) UNLocAvgBand UNQueBand)
    (r2 : UNG2bRowk (fun d => UNKind.band d) (fun d => UNOUProfile.band d)) :
    UNOURowk (fun d => UNKind.band d) (∀ d : ℕ, UNMLOut d) UNLocAvgBand UNQueBand :=
  ouRowk_of_pins _ _ (fun _ hd => unOUProfRowk_band hd) r1 r2

/-- `ouRow_of_pinsk_band`: the merged `UNOURow` from the two generic rows at the band. -/
theorem inst_ouRow_band
    (r1 : UNG1Rowk (fun d => UNKind.band d) (fun d => UNOUProfile.band d)
      (∀ d : ℕ, UNMLOut d) UNLocAvgBand UNQueBand)
    (r2 : UNG2bRowk (fun d => UNKind.band d) (fun d => UNOUProfile.band d)) : UNOURow :=
  ouRow_of_pinsk_band r1 r2

end OUInterfaceKInst

end RBM.Univ
