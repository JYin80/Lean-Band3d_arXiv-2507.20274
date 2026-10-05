/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Induction.Step6Pins
import RBM3D.Induction.Step5Kit
import RBM3D.Induction.ScaleFacts3
import RBM3D.Induction.Step2Iterate
import RBM3D.Induction.ZeroModeCalc
import RBM3D.Induction.QopNorm
import RBM3D.Induction.GridDuhamelN
import RBM3D.Induction.DecayLoopB
import RBM3D.Loop.KLFinal
import RBM3D.Green.GbEXP
import RBM3D.Graph.LWPins
import RBM3D.Evolution.Prec

/-!
# S6-02 (ST-5): the Step 6 kit

The kit of Step 6 of `lem:main_ind` (paper: arXiv:2507.20274, `paper/tex/1_2_Intro_model_result.tex`
`1390-1396` and `paper/tex/6_Step6_two_loop.tex`): the `Prec` calculus, the bridges at a section `u`
(`STLK_of_STLKU_at`, `STDecay_of_STGdecayW_at`, ...), the compiled glue (windows, the rotation bridge
`STEGt = LWE`, the Duhamel identity along `[s,t]`), the initial-term comparisons in regimes (iii), (iv),
the four regime skeletons `ST_step6_case{I,II,III,IV}_of_pins` (the producers of `STStep6I..IV` from
their ingredient pins), `st6_GdecayW_of_zero`, `ST_step6R_mono`, and the compiled nonempty instances at
`d = 3` (namespace `RBM.Gauss.Step6Inst`).

Moved verbatim (thirteen blocks) from the T2191 design probe `RBM3D/Probe/T2191Pins.lean` at `96c6b4c`
(branch `t/T2191`, never merged); the pins (`STStep6I..IV`, `STExp*`, the instances `inst_step6I..IV`)
are in `RBM3D/Induction/Step6Pins.lean` (S6-01, T2204).  Not ported (DECISIONS §68): `ST_mainInd_of_steps`
and the intermediate-time gluing (`st6_restrict_*`, `st6_cover_two`, `ST_step6_compose`,
`ST_step6_four_of_regimes`, `STGenericPos`, `ST_step6_generic_of_regimes`, `szFour`, the corresponding
instances); they stay on `t/T2191` at `96c6b4c`.  Docstrings are verbatim and may cite them as references.
No registry line: no `Prop` is defined here; `STStep6I..IV` stay owed.
-/

set_option linter.style.longLine false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal

/-! ## 2. `0 < lam n` eventually, the generic lemma "per time sequence ⇒ uniform in `u`", the bridges at a sequence `u ∈ [s,t]`

`(g)` of the ticket: `LWtermEXP` and `STImproveExpAver` are statements at one time sequence; Step 6 integrates over `u`.
For a **deterministic** family the two agree: `Prec` of a deterministic family is the pointwise bound for all large `n`
(`st6_prec_det_iff`), and a failing family of times is a sequence of times (`st6_precU_of_forall_seq`). -/

namespace RBM.Gauss.Sizes

open RBM RBM.Loop RBM.Path RBM.Gauss

variable {d : ℕ} (sz : Sizes d)

/-- `(eq:WO)` gives `0 < lam n` eventually: `W^{-d/2+𝔡} ≤ lam n` and `W ≥ 1` (`W^{x} > 0`).  So the term
`(lam² W^d)^{-1/5}` of `STExp2` is eventually positive (it is `0` at a size with `lam n = 0`, `0 ^ (-1/5) = 0` in Mathlib:
`st6_target_lam_zero`). -/
theorem st6_lam_pos {𝔡 : ℝ} (h : sz.WO 𝔡) : ∀ᶠ n in atTop, 0 < sz.lam n := by
  filter_upwards [h] with n hn
  exact lt_of_lt_of_le (Real.rpow_pos_of_pos (by exact_mod_cast sz.W_pos n) _) hn.1

/-- `(ilambda² W^d)^{-1/5} > 0` for `lam n ≠ 0`. -/
theorem st6_G_pos {n : ℕ} (h : sz.lam n ≠ 0) :
    0 < (sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d) ^ (-(1 / 5 : ℝ)) := by
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  exact Real.rpow_pos_of_pos (by positivity) _

/-- The defect scenario of the ticket (item 2 (6)): at `lam n = 0` the target of `STExp2` falls to `(W^{-d}B)³`. -/
theorem st6_target_lam_zero {n : ℕ} (h : sz.lam n = 0) (u : ℝ) :
    STExpTarget sz n u = (sz.Bctl n u) ^ 3 := by
  unfold STExpTarget
  rw [h]
  rw [zero_pow (by norm_num), zero_mul, Real.zero_rpow (by norm_num)]
  ring

/-- **A deterministic `Prec` is the pointwise bound for all large `n`** (the failure event is `∅` or the whole space,
which has probability `1 > N^{-1}`). -/
theorem st6_prec_det_iff (hsz : sz.SizeTendsto) {V : ℕ → Type*} (F G : ∀ n, V n → ℝ) :
    sz.Prec (U := V) (fun n v _ => F n v) (fun n v _ => G n v) ↔
      ∀ τ : ℝ, 0 < τ → ∀ᶠ n in atTop, ∀ v, F n v ≤ ((sz.size n : ℕ) : ℝ) ^ τ * G n v := by
  constructor
  · intro h τ hτ
    have h1 := h τ hτ 1 one_pos
    filter_upwards [h1, (tendsto_size sz hsz).eventually (eventually_ge_atTop 2)] with n hn hN2
    intro v
    by_contra hcon
    push Not at hcon
    have hbad : badSetAt sz.size (fun n v (_ : sz.SeqΩ) => F n v) (fun n v (_ : sz.SeqΩ) => G n v) τ n =
        (Set.univ : Set sz.SeqΩ) := by
      ext ω
      simp only [badSetAt, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
      exact ⟨v, hcon⟩
    rw [hbad, measure_univ] at hn
    have hN : (2 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast hN2
    have hlt : ((sz.size n : ℕ) : ℝ) ^ (-(1 : ℝ)) < 1 := by
      rw [Real.rpow_neg_one]
      exact inv_lt_one_of_one_lt₀ (by linarith)
    have h2 : ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-(1 : ℝ))) < 1 := by
      rw [← ENNReal.ofReal_one]
      exact (ENNReal.ofReal_lt_ofReal_iff one_pos).2 hlt
    exact absurd hn (not_le.2 h2)
  · intro h
    refine StochDomAt.of_eventually_empty fun τ hτ => ?_
    filter_upwards [h τ hτ] with n hn
    ext ω
    simp only [badSetAt, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_exists, not_lt]
    exact fun v => hn v

/-- **(g) Per time sequence ⇒ uniform in `u ∈ [s,t]`** for a deterministic family: if for every time sequence `u` with
`s ≤ u ≤ t` the family `(F n (u n) w, G n (u n) w)` satisfies `Prec`, then the family indexed by `(u, w) ∈ [s_n,t_n] × W n`
does.  (A failing `(n, u_n, w)` for infinitely many `n` is a time sequence `u`.) -/
theorem st6_precU_of_forall_seq (hsz : sz.SizeTendsto) {s t : ℕ → ℝ} (hst : ∀ n, s n ≤ t n)
    {W : ℕ → Type*} (F G : ∀ n, ℝ → W n → ℝ)
    (h : ∀ u : ℕ → ℝ, (∀ n, s n ≤ u n) → (∀ n, u n ≤ t n) →
      sz.Prec (U := W) (fun n w _ => F n (u n) w) (fun n w _ => G n (u n) w)) :
    sz.Prec (U := fun n => TimeIcc s t n × W n) (fun n p _ => F n (p.1 : ℝ) p.2)
      (fun n p _ => G n (p.1 : ℝ) p.2) := by
  classical
  rw [st6_prec_det_iff sz hsz]
  intro τ hτ
  by_contra hcon
  rw [Filter.not_eventually] at hcon
  let u : ℕ → ℝ := fun n =>
    if hn : ∃ p : TimeIcc s t n × W n,
        ¬ (F n (p.1 : ℝ) p.2 ≤ ((sz.size n : ℕ) : ℝ) ^ τ * G n (p.1 : ℝ) p.2)
    then ((Classical.choose hn).1 : ℝ) else s n
  have hu1 : ∀ n, s n ≤ u n := by
    intro n
    by_cases hn : ∃ p : TimeIcc s t n × W n,
        ¬ (F n (p.1 : ℝ) p.2 ≤ ((sz.size n : ℕ) : ℝ) ^ τ * G n (p.1 : ℝ) p.2)
    · simp only [u, hn, ↓reduceDIte]; exact (Classical.choose hn).1.2.1
    · simp only [u, hn, ↓reduceDIte]; exact le_rfl
  have hu2 : ∀ n, u n ≤ t n := by
    intro n
    by_cases hn : ∃ p : TimeIcc s t n × W n,
        ¬ (F n (p.1 : ℝ) p.2 ≤ ((sz.size n : ℕ) : ℝ) ^ τ * G n (p.1 : ℝ) p.2)
    · simp only [u, hn, ↓reduceDIte]; exact (Classical.choose hn).1.2.2
    · simp only [u, hn, ↓reduceDIte]; exact hst n
  have h' := ((st6_prec_det_iff sz hsz (fun n (w : W n) => F n (u n) w)
    (fun n (w : W n) => G n (u n) w)).1 (h u hu1 hu2)) τ hτ
  obtain ⟨n, hn1, hn2⟩ := (hcon.and_eventually h').exists
  push Not at hn1
  obtain ⟨p, hp⟩ := hn1
  have hex : ∃ p : TimeIcc s t n × W n,
      ¬ (F n (p.1 : ℝ) p.2 ≤ ((sz.size n : ℕ) : ℝ) ^ τ * G n (p.1 : ℝ) p.2) := ⟨p, not_le.2 hp⟩
  have hun : u n = ((Classical.choose hex).1 : ℝ) := by simp only [u, hex, ↓reduceDIte]
  have hc := Classical.choose_spec hex
  have := hn2 (Classical.choose hex).2
  rw [hun] at this
  exact hc this

end RBM.Gauss.Sizes

/-! ### The bridges at a time sequence `u ∈ [s,t]` (consumers: `STImproveExpAver`, `LWtermEXP`, `STMainInd`)

`LWtermEXP` (`Graph/LWPins.lean:311`) has the premises `STLocalEntry`, `LWAvgLaw`, `STLmax`, `STLK`, `STDecay` at **one** time
sequence; Steps 2, 3, 4, 5 give them uniformly in `u ∈ [s,t]` (`STLocalEntryU`, `STAvgU`, `STLmaxU`, `STLKU`,
`STGdecayW … 0`).  The uniform statement restricted to the section `u` is the per-time statement (`precomp_param`).
`STDecayStrong` has no such bridge at `u`: its index set is `ilambda² ≤ 1-t`, not `≤ 1-u`. -/

namespace RBM.Gauss.Sizes

open RBM RBM.Loop RBM.Path RBM.Gauss

variable {d : ℕ} (sz : Sizes d)

theorem STLK_of_STLKU_at {E s t u : ℕ → ℝ} (hsu : ∀ n, s n ≤ u n) (hut : ∀ n, u n ≤ t n)
    (h : STLKU sz E s t) : STLK sz E u := by
  intro k hk
  exact StochDomAt.precomp_param (h k hk)
    (fun n (p : (Fin k → Bool) × (Fin k → Zd d (sz.L n))) => ((⟨u n, hsu n, hut n⟩ : TimeIcc s t n), p))

theorem STLmax_of_STLmaxU_at {E s t u : ℕ → ℝ} (hsu : ∀ n, s n ≤ u n) (hut : ∀ n, u n ≤ t n)
    (h : STLmaxU sz E s t) : STLmax sz E u := by
  intro k hk
  exact StochDomAt.precomp_param (h k hk)
    (fun n (p : (Fin k → Bool) × (Fin k → Zd d (sz.L n))) => ((⟨u n, hsu n, hut n⟩ : TimeIcc s t n), p))

theorem STLocalEntry_of_STLocalEntryU_at {E s t u : ℕ → ℝ} (hsu : ∀ n, s n ≤ u n) (hut : ∀ n, u n ≤ t n)
    (h : STLocalEntryU sz E s t) : STLocalEntry sz E u :=
  StochDomAt.precomp_param h
    (fun n (p : Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n)) => ((⟨u n, hsu n, hut n⟩ : TimeIcc s t n), p))

/-- `(Gt_avgbound_flow)` at the section `u`: `STAvgU` gives the premise `LWAvgLaw` of `LWtermEXP` (and of
`STImproveExpAver`); `𝒦^{(1)}_{σ,a} = m(σ)` is the merged `ST_Kloop_one`. -/
theorem LWAvgLaw_of_STAvgU_at {E s t u : ℕ → ℝ} (hsu : ∀ n, s n ≤ u n) (hut : ∀ n, u n ≤ t n)
    (h : STAvgU sz E s t) : LWAvgLaw sz E u := by
  have h1 := StochDomAt.precomp_param h
    (fun n (a : Zd d (sz.L n)) =>
      ((⟨u n, hsu n, hut n⟩ : TimeIcc s t n), ((fun _ : Fin 1 => true), (fun _ : Fin 1 => a))))
  simp only [ST_Kloop_one, pow_one] at h1
  exact h1

/-- `(Eq:Gdecay_flow)` of Step 5 (`STGdecayW … 0`, no loss `((1-s)/(1-u))^{C_d}`) at the section `u` is `(Eq:Gdecay)` at
the time sequence `u` (the endpoint `u = t` is `ST_step5_assembly`). -/
theorem STDecay_of_STGdecayW_at {E s t u : ℕ → ℝ} (hsu : ∀ n, s n ≤ u n) (hut : ∀ n, u n ≤ t n)
    (h : STGdecayW sz E s t 0) : STDecay sz E u := by
  intro D hD
  have := StochDomAt.precomp_param (h D hD)
    (fun n (p : (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n))) => ((⟨u n, hsu n, hut n⟩ : TimeIcc s t n), p))
  simp only [Real.rpow_zero, one_mul] at this
  exact this

/-- The endpoint `u = t` of `STLocalEntryU` (conclusion `STLocalEntry` of `lem:main_ind`, `Induction/Defs.lean:304`). -/
theorem STLocalEntry_of_STLocalEntryU {E s t : ℕ → ℝ} (hst : ∀ n, s n ≤ t n) (h : STLocalEntryU sz E s t) :
    STLocalEntry sz E t :=
  STLocalEntry_of_STLocalEntryU_at sz hst (fun _ => le_rfl) h

end RBM.Gauss.Sizes

/-! ## 5. Compiled glue: calculus of `Prec` (labels, finitely many signs), flow facts, the windows, the LW bridge `STEGt = LWE`,
the Duhamel identity along `[s,t]` -/

namespace RBM.Gauss.Sizes

open RBM RBM.Loop RBM.Path RBM.Gauss

variable {d : ℕ} (sz : Sizes d)

/-- **The sup norm over the labels of a tensor is `≺` if the entries are** (the union over the labels is inside `P`, so the event
`‖f‖ > r` is contained in `∃ a, |f_a| > r`): from `(Eq:Gtlp_exp+IND)` (index `(σ,a)`) to the `L^∞` hypothesis `‖𝒜‖_∞ ≺ X` of the kernel pins. -/
theorem st6_prec_pi_norm (hsz : sz.SizeTendsto) {E s : ℕ → ℝ} {X : ℕ → ℝ} (hX : ∀ n, 0 ≤ X n)
    (h : sz.Prec (U := fun n => (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)))
      (fun n p _ => ‖STExpErr sz n (E n) (s n) p.1 p.2‖) (fun n _ _ => X n))
    (σ : Fin 2 → Bool) {V : ℕ → Type*} :
    sz.Prec (U := V) (fun n _ _ => ‖(fun b => STExpErr sz n (E n) (s n) σ b)‖) (fun n _ _ => X n) := by
  refine StochDomAt.of_subset_union (tendsto_size sz hsz) h h fun τ hτ => ⟨τ, hτ, Eventually.of_forall fun n ω hω => ?_⟩
  obtain ⟨v, hv⟩ := hω
  have hr : 0 ≤ ((sz.size n : ℕ) : ℝ) ^ τ * X n := mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) (hX n)
  have : ¬ ‖(fun b => STExpErr sz n (E n) (s n) σ b)‖ ≤ ((sz.size n : ℕ) : ℝ) ^ τ * X n := not_le.2 hv
  rw [pi_norm_le_iff_of_nonneg hr] at this
  push Not at this
  obtain ⟨a, ha⟩ := this
  exact Or.inl ⟨(σ, a), ha⟩

/-- **Finitely many signs**: `Prec` for each of finitely many index values `i` (a fixed finite type) gives `Prec` for the family
indexed by `(i, v)` (union bound, `#ι ≤ N`). -/
theorem st6_prec_of_forall_fin (hsz : sz.SizeTendsto) {ι : Type*} [Finite ι] {V : ℕ → Type*}
    (ξ ζ : ∀ n, ι → V n → sz.SeqΩ → ℝ)
    (h : ∀ i : ι, sz.Prec (U := V) (fun n v ω => ξ n i v ω) (fun n v ω => ζ n i v ω)) :
    sz.Prec (U := fun n => ι × V n) (fun n (p : ι × V n) ω => ξ n p.1 p.2 ω)
      (fun n (p : ι × V n) ω => ζ n p.1 p.2 ω) := by
  intro τ hτ D hD
  have : Fintype ι := Fintype.ofFinite ι
  have hall : ∀ᶠ n in atTop, ∀ i : ι, sz.seqP (badSetAt sz.size (fun n v ω => ξ n i v ω)
      (fun n v ω => ζ n i v ω) τ n) ≤ ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-(D + 1))) :=
    Filter.eventually_all.2 fun i => h i τ hτ (D + 1) (by linarith)
  filter_upwards [hall, (tendsto_size sz hsz).eventually (eventually_ge_atTop (Fintype.card ι)),
    (tendsto_size sz hsz).eventually (eventually_ge_atTop 1)] with n hn hN hN1
  have hsub : badSetAt sz.size (fun n (p : ι × V n) ω => ξ n p.1 p.2 ω)
      (fun n (p : ι × V n) ω => ζ n p.1 p.2 ω) τ n ⊆
      ⋃ i : ι, badSetAt sz.size (fun n v ω => ξ n i v ω) (fun n v ω => ζ n i v ω) τ n := by
    intro ω hω
    obtain ⟨p, hp⟩ := hω
    exact Set.mem_iUnion.2 ⟨p.1, p.2, hp⟩
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by exact_mod_cast hN1
  have hNr : (Fintype.card ι : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast hN
  have hp : (0 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ (-(D + 1)) := Real.rpow_nonneg hN0.le _
  have hrw : ((sz.size n : ℕ) : ℝ) ^ (-D) =
      ((sz.size n : ℕ) : ℝ) * ((sz.size n : ℕ) : ℝ) ^ (-(D + 1)) := by
    rw [← Real.rpow_one_add' hN0.le (by linarith)]
    congr 1; ring
  calc sz.seqP (badSetAt sz.size (fun n (p : ι × V n) ω => ξ n p.1 p.2 ω)
        (fun n (p : ι × V n) ω => ζ n p.1 p.2 ω) τ n)
      ≤ sz.seqP (⋃ i : ι, badSetAt sz.size (fun n v ω => ξ n i v ω) (fun n v ω => ζ n i v ω) τ n) :=
        measure_mono hsub
    _ ≤ ∑ i : ι, sz.seqP (badSetAt sz.size (fun n v ω => ξ n i v ω) (fun n v ω => ζ n i v ω) τ n) :=
        measure_iUnion_fintype_le _ _
    _ ≤ ∑ _i : ι, ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-(D + 1))) := Finset.sum_le_sum fun i _ => hn i
    _ = ENNReal.ofReal ((Fintype.card ι : ℝ) * ((sz.size n : ℕ) : ℝ) ^ (-(D + 1))) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _),
          ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-D)) := by
        apply ENNReal.ofReal_le_ofReal
        rw [hrw]
        exact mul_le_mul_of_nonneg_right hNr hp

/-- `|lemE z_n| < 2` on the flow (`|E| ≤ |Re z| ≤ 2 - κ`). -/
theorem st6_flowE_lt_two {κ ε 𝔠 𝔡 : ℝ} (hκ : 0 < κ) {z : ℕ → ℂ} (hz : STFlow sz κ ε 𝔠 𝔡 z) (n : ℕ) :
    |STflowE z n| < 2 := by
  have h := hz.2 n
  have hN : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
  have him : 0 < (z n).im := lt_of_lt_of_le (Real.rpow_pos_of_pos hN _) h.2.1
  have h2 : |lemE (z n)| < 2 := by linarith [(abs_lemE_le him).trans h.1]
  exact h2

/-- The window `ilambda²/L^d ≤ 1-t` contains regime (i). -/
theorem st6_hi_of_reg5I (hd : 2 ≤ d) {s t : ℕ → ℝ} (h : STReg5I sz s t) : STDriftHi sz s t :=
  fun n => (st5_reg5I_mid hd h n).1

/-- The window contains regime (ii). -/
theorem st6_hi_of_reg5II {s t : ℕ → ℝ} (h : STReg5II sz s t) : STDriftHi sz s t := fun n => (h n).1

/-- The window contains regime (iii) (`L^d ≥ 1`). -/
theorem st6_hi_of_reg5III {s t : ℕ → ℝ} (h : STReg5III sz s t) : STDriftHi sz s t := by
  intro n
  have hL : (1 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) := by exact_mod_cast (by have := sz.three_le_L n; omega : 1 ≤ sz.L n)
  have h1 : (1 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) ^ d := one_le_pow₀ hL
  calc sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ d ≤ sz.lam n ^ 2 / 1 :=
        div_le_div_of_nonneg_left (sq_nonneg _) one_pos h1
    _ = sz.lam n ^ 2 := div_one _
    _ ≤ 1 - t n := h n

/-! ### The rotation bridge `STEGt = LWE` (T2080; the proof is that of the `private` `STB_EGt_eq_LWE`,
`Induction/Step2Events.lean:1294`, copied) -/

private theorem st6_trace_six {ι : Type*} [Fintype ι] (P Q R S T U : Matrix ι ι ℂ) :
    (P * (Q * (R * (S * (T * U))))).trace = (T * (U * (P * (Q * (R * S))))).trace := by
  have := Matrix.trace_mul_comm (P * (Q * (R * S))) (T * U)
  simp only [Matrix.mul_assoc] at this ⊢
  exact this

private theorem st6_loop_rot (n : ℕ) (E u : ℝ) (σ₀ σ₁ : Bool) (a₀ y a₁ : Zd d (sz.L n))
    (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) :
    STLM sz n E u H ![σ₁, σ₁, σ₀] ![y, a₁, a₀] = STLM sz n E u H ![σ₀, σ₁, σ₁] ![a₀, y, a₁] := by
  unfold STLM loopFine loopM
  simp only [Nat.succ_eq_add_one, zero_add, Nat.reduceAdd, List.ofFn_succ, Fin.isValue,
    Fin.cast_eq_self, Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_fin_one,
    List.ofFn_zero, List.prod_cons, List.prod_nil, mul_one, Matrix.mul_assoc]
  exact st6_trace_six _ _ _ _ _ _

/-- `STEGt = LWE`: the two forms of the light-weight term agree pointwise (cyclic rotation of the 3-loop and the order of the two
factors). -/
theorem st6_EGt_eq_LWE (n : ℕ) (E t : ℝ) (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) (ω : sz.SeqΩ) :
    STEGt sz n E t σ a ω = LWE sz n E t σ a ω := by
  unfold STEGt STEGtM LWE LWcut
  have hm : ∀ s : Bool, STmsig E s = mSigma E s := fun s => rfl
  have h1 : ∀ s : Bool, (fun _ : Fin 1 => s) = ![s] := fun s => by
    funext i; fin_cases i; rfl
  have h1' : ∀ x : Zd d (sz.L n), (fun _ : Fin 1 => x) = ![x] := fun x => by
    funext i; fin_cases i; rfl
  simp only [STavgM, STLM_seqHflow, hm, h1, h1']
  have hA : ∀ x y : Zd d (sz.L n),
      (Lloop sz n E t ![σ 0] ![x] ω - mSigma E (σ 0)) * SB d (sz.L n) (sz.lam n) x y *
        Lloop sz n E t ![σ 0, σ 0, σ 1] ![y, a 0, a 1] ω =
      SB d (sz.L n) (sz.lam n) x y * (Lloop sz n E t ![σ 0] ![x] ω - mSigma E (σ 0)) *
        Lloop sz n E t ![σ 0, σ 0, σ 1] ![y, a 0, a 1] ω := fun x y => by ring
  have hB : ∀ x y : Zd d (sz.L n),
      (Lloop sz n E t ![σ 1] ![x] ω - mSigma E (σ 1)) * SB d (sz.L n) (sz.lam n) x y *
        Lloop sz n E t ![σ 0, σ 1, σ 1] ![a 0, y, a 1] ω =
      SB d (sz.L n) (sz.lam n) x y * (Lloop sz n E t ![σ 1] ![x] ω - mSigma E (σ 1)) *
        Lloop sz n E t ![σ 1, σ 1, σ 0] ![y, a 1, a 0] ω := fun x y => by
    have := st6_loop_rot sz n E t (σ 0) (σ 1) (a 0) y (a 1) (sz.seqHflow n t ω)
    simp only [STLM_seqHflow] at this
    rw [this]; ring
  simp only [Finset.sum_add_distrib, hA, hB]
  ring

/-- The expected light-weight term is `𝔼 LWE`. -/
theorem st6_expEGt_eq (n : ℕ) (E t : ℝ) (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) :
    STExpEGt sz n E t σ a = ∫ ω, LWE sz n E t σ a ω ∂(sz.seqP) := by
  unfold STExpEGt
  congr 1
  funext ω
  exact st6_EGt_eq_LWE sz n E t σ a ω

/-- **The Duhamel identity along `[s_n, t_n]`** from the pin `STExpDuhamelZ` (`|E_n| < 2`, `0 ≤ s`, `u ≤ t < 1`). -/
theorem st6_duhEq_of_pin (hDu : STExpDuhamelZ d) (hd : 3 ≤ d) {κ ε 𝔠 𝔡 : ℝ} (hκ : 0 < κ) {z : ℕ → ℂ}
    (hflow : STFlow sz κ ε 𝔠 𝔡 z) {s t : ℕ → ℝ} (hs0 : ∀ n, 0 ≤ s n) (htT : ∀ n, t n ≤ lemT (z n)) :
    STExpDuhEq sz (STflowE z) s t := by
  intro n u σ A a
  exact hDu hd sz n (STflowE z n) (st6_flowE_lt_two sz hκ hflow n) (s n) u (hs0 n) u.2.1
    (lt_of_le_of_lt u.2.2 (st5_t_lt_one sz hflow htT n)) σ A a

end RBM.Gauss.Sizes

/-! ## 6. The initial term closes with no `𝔠_d` loss in regimes (iii) and (iv) (compiled; answers the preflight question (iii))

`(1-s) B_s` against `(1-u) B_u`: `x B(x) = W^{-d} x/(ilambda² + x) + N⁻¹` with `x = 1 - u` (`N = (WL)^d`).  In regime (iii),
`x ≥ ilambda²` gives `x/(ilambda²+x) ∈ [1/2, 1]`; in regime (iv), `x ≤ ilambda²/L^d` gives `W^{-d} x/(ilambda²+x) ≤ N⁻¹`: in both
`(1-s) B_s ≤ 2 (1-u) B_u`, so `((1-s)/(1-u))² B_s² ≤ 4 B_u²`: the `L^∞`-only kernel estimate `(sum_res_Ndecay)` costs the constant `4`. -/

namespace RBM.Gauss.Sizes

open RBM RBM.Loop RBM.Path RBM.Gauss

variable {d : ℕ} (sz : Sizes d)

/-- `W^{-d} B_{u,0} = W^{-d}(ilambda² + 1-u)⁻¹ + (N(1-u))⁻¹` for `u < 1` (`N = (WL)^d`; `(eq_B_param)` with `K = 0`). -/
theorem st6_Bctl_eq (n : ℕ) {u : ℝ} (hu : u < 1) :
    sz.Bctl n u = (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (sz.lam n ^ 2 + (1 - u))⁻¹ +
      (((sz.size n : ℕ) : ℝ) * (1 - u))⁻¹ := by
  have hx0 : 0 < 1 - u := by linarith
  have hNeq : ((sz.size n : ℕ) : ℝ) = ((sz.W n : ℕ) : ℝ) ^ d * ((sz.L n : ℕ) : ℝ) ^ d := by
    simp only [Sizes.size]; push_cast; ring
  have hW0 : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  unfold Sizes.Bctl Bparam
  rw [abs_of_pos hx0, hNeq]
  have h0 : (((0 : ℕ) : ℝ) + 1) ^ (d - 2) = 1 := by simp
  rw [h0, inv_one, mul_one]
  have hL0 : (0 : ℝ) < ((sz.L n : ℕ) : ℝ) := by exact_mod_cast (by have := sz.three_le_L n; omega : 0 < sz.L n)
  field_simp

/-- `(1-u) W^{-d}B_{u,0} = W^{-d} (1-u)/(ilambda² + 1-u) + N⁻¹`. -/
theorem st6_xB_eq (n : ℕ) {u : ℝ} (hu : u < 1) :
    (1 - u) * sz.Bctl n u = (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * ((1 - u) / (sz.lam n ^ 2 + (1 - u))) +
      (((sz.size n : ℕ) : ℝ))⁻¹ := by
  have hx0 : 0 < 1 - u := by linarith
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
  have hg : 0 < sz.lam n ^ 2 + (1 - u) := by positivity
  rw [st6_Bctl_eq sz n hu]
  field_simp

/-- Regime (iii): `ilambda² ≤ 1-u ≤ 1-s` gives `(1-s) B_s ≤ 2 (1-u) B_u`. -/
theorem st6_xB_III (n : ℕ) {s u : ℝ} (hsu : s ≤ u) (hu : u < 1) (hg : sz.lam n ^ 2 ≤ 1 - u) :
    (1 - s) * sz.Bctl n s ≤ 2 * ((1 - u) * sz.Bctl n u) := by
  have hs1 : s < 1 := lt_of_le_of_lt hsu hu
  have hx0 : 0 < 1 - u := by linarith
  have hxs0 : 0 < 1 - s := by linarith
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
  have hWd : (0 : ℝ) < (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ := by
    have : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
    positivity
  rw [st6_xB_eq sz n hs1, st6_xB_eq sz n hu]
  have h1 : (1 - s) / (sz.lam n ^ 2 + (1 - s)) ≤ 1 := by
    rw [div_le_one (by positivity)]; nlinarith [sq_nonneg (sz.lam n)]
  have h2 : (1 / 2 : ℝ) ≤ (1 - u) / (sz.lam n ^ 2 + (1 - u)) := by
    rw [le_div_iff₀ (by positivity)]; linarith
  have h3 := mul_le_mul_of_nonneg_left h1 hWd.le
  have h4 := mul_le_mul_of_nonneg_left h2 hWd.le
  have hN : (0 : ℝ) ≤ (((sz.size n : ℕ) : ℝ))⁻¹ := by positivity
  nlinarith

/-- Regime (iv): `1-s ≤ ilambda²/L^d` (and `u ≥ s`) gives `(1-s) B_s ≤ 2 (1-u) B_u`. -/
theorem st6_xB_IV (n : ℕ) {s u : ℝ} (hsu : s ≤ u) (hu : u < 1)
    (hg : 1 - s ≤ sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ d) :
    (1 - s) * sz.Bctl n s ≤ 2 * ((1 - u) * sz.Bctl n u) := by
  have hs1 : s < 1 := lt_of_le_of_lt hsu hu
  have hx0 : 0 < 1 - u := by linarith
  have hxs0 : 0 < 1 - s := by linarith
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
  have hW0 : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hL0 : (0 : ℝ) < ((sz.L n : ℕ) : ℝ) := by exact_mod_cast (by have := sz.three_le_L n; omega : 0 < sz.L n)
  have hLd : (0 : ℝ) < ((sz.L n : ℕ) : ℝ) ^ d := by positivity
  have hWd : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) ^ d := by positivity
  have hNeq : ((sz.size n : ℕ) : ℝ) = ((sz.W n : ℕ) : ℝ) ^ d * ((sz.L n : ℕ) : ℝ) ^ d := by
    simp only [Sizes.size]; push_cast; ring
  rw [st6_xB_eq sz n hs1, st6_xB_eq sz n hu]
  -- `(1-s)/(ilambda² + 1-s) ≤ L^{-d}`
  have hg2 : (1 - s) * ((sz.L n : ℕ) : ℝ) ^ d ≤ sz.lam n ^ 2 := by
    rwa [le_div_iff₀ hLd] at hg
  have h1 : (1 - s) / (sz.lam n ^ 2 + (1 - s)) ≤ (((sz.L n : ℕ) : ℝ) ^ d)⁻¹ := by
    rw [div_le_iff₀ (by positivity), inv_mul_eq_div, le_div_iff₀ hLd]
    nlinarith
  have h2 : 0 ≤ (1 - u) / (sz.lam n ^ 2 + (1 - u)) := by positivity
  have h3 : (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * ((1 - s) / (sz.lam n ^ 2 + (1 - s))) ≤ (((sz.size n : ℕ) : ℝ))⁻¹ := by
    calc (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * ((1 - s) / (sz.lam n ^ 2 + (1 - s)))
        ≤ (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (((sz.L n : ℕ) : ℝ) ^ d)⁻¹ :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = (((sz.size n : ℕ) : ℝ))⁻¹ := by rw [hNeq, mul_inv]
  have h4 : 0 ≤ (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * ((1 - u) / (sz.lam n ^ 2 + (1 - u))) := by positivity
  linarith

/-- From `(1-s) B_s ≤ 2 (1-u) B_u` to the squared ratio: `((1-s)/(1-u))² B_s² ≤ 4 B_u²`. -/
theorem st6_ratio_sq (n : ℕ) {s u : ℝ} (hsu : s ≤ u) (hu : u < 1)
    (h : (1 - s) * sz.Bctl n s ≤ 2 * ((1 - u) * sz.Bctl n u)) :
    ((1 - s) / (1 - u)) ^ 2 * (sz.Bctl n s) ^ 2 ≤ 4 * (sz.Bctl n u) ^ 2 := by
  have hx0 : 0 < 1 - u := by linarith
  have hB0 : 0 ≤ sz.Bctl n s := (STBctl_pos sz n (lt_of_le_of_lt hsu hu)).le
  have h1 : ((1 - s) / (1 - u)) * sz.Bctl n s ≤ 2 * sz.Bctl n u := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hx0]
    linarith
  have h0 : 0 ≤ ((1 - s) / (1 - u)) * sz.Bctl n s := by
    have : 0 ≤ 1 - s := by linarith
    positivity
  calc ((1 - s) / (1 - u)) ^ 2 * (sz.Bctl n s) ^ 2 = (((1 - s) / (1 - u)) * sz.Bctl n s) ^ 2 := by ring
    _ ≤ (2 * sz.Bctl n u) ^ 2 := pow_le_pow_left₀ h0 h1 2
    _ = 4 * (sz.Bctl n u) ^ 2 := by ring

/-- **The comparison of the initial term with the target**: `((1-s)/(1-u))² T_s ≤ 4 T_u`, given `(1-s) B_s ≤ 2 (1-u) B_u`
(`T_u = B_u² (G + B_u)`, `G = (ilambda² W^d)^{-1/5} ≥ 0`, `B_s ≤ B_u`). -/
theorem st6_cmp_ini (n : ℕ) {s u : ℝ} (hsu : s ≤ u) (hu : u < 1)
    (h : (1 - s) * sz.Bctl n s ≤ 2 * ((1 - u) * sz.Bctl n u)) :
    ((1 - s) / (1 - u)) ^ 2 * STExpTarget sz n s ≤ 4 * STExpTarget sz n u := by
  unfold STExpTarget
  have hG : 0 ≤ (sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d) ^ (-(1 / 5 : ℝ)) :=
    Real.rpow_nonneg (by positivity) _
  have hr := st6_ratio_sq sz n hsu hu h
  have hm := STBctl_mono sz n hsu hu
  have hs0 : 0 ≤ sz.Bctl n s := (STBctl_pos sz n (lt_of_le_of_lt hsu hu)).le
  calc ((1 - s) / (1 - u)) ^ 2 * ((sz.Bctl n s) ^ 2 * ((sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d) ^ (-(1 / 5 : ℝ)) +
          sz.Bctl n s))
      = (((1 - s) / (1 - u)) ^ 2 * (sz.Bctl n s) ^ 2) *
          ((sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d) ^ (-(1 / 5 : ℝ)) + sz.Bctl n s) := by ring
    _ ≤ (4 * (sz.Bctl n u) ^ 2) * ((sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d) ^ (-(1 / 5 : ℝ)) + sz.Bctl n u) := by
        apply mul_le_mul hr (by linarith) (by positivity) (by positivity)
    _ = 4 * ((sz.Bctl n u) ^ 2 * ((sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d) ^ (-(1 / 5 : ℝ)) + sz.Bctl n u)) := by ring

/-- `T_u ≥ 0` (every term is nonnegative). -/
theorem st6_target_nonneg (n : ℕ) {u : ℝ} (hu : u < 1) : 0 ≤ STExpTarget sz n u := by
  unfold STExpTarget
  have hB := (STBctl_pos sz n hu).le
  have hG : 0 ≤ (sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d) ^ (-(1 / 5 : ℝ)) :=
    Real.rpow_nonneg (by positivity) _
  positivity

/-- `T_s ≤ T_u` for `s ≤ u < 1` (`B_s ≤ B_u`, `G ≥ 0`). -/
theorem st6_target_mono (n : ℕ) {s u : ℝ} (hsu : s ≤ u) (hu : u < 1) :
    STExpTarget sz n s ≤ STExpTarget sz n u := by
  unfold STExpTarget
  have hm := STBctl_mono sz n hsu hu
  have hs0 : 0 ≤ sz.Bctl n s := (STBctl_pos sz n (lt_of_le_of_lt hsu hu)).le
  have hG : 0 ≤ (sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d) ^ (-(1 / 5 : ℝ)) :=
    Real.rpow_nonneg (by positivity) _
  gcongr

/-- `B_u³ ≤ T_u` (the `Ward` terms of regimes (i), (ii) are below the target). -/
theorem st6_cube_le_target (n : ℕ) {u : ℝ} (hu : u < 1) : (sz.Bctl n u) ^ 3 ≤ STExpTarget sz n u := by
  unfold STExpTarget
  have hB := (STBctl_pos sz n hu).le
  have hG : 0 ≤ (sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d) ^ (-(1 / 5 : ℝ)) :=
    Real.rpow_nonneg (by positivity) _
  nlinarith [mul_nonneg (sq_nonneg (sz.Bctl n u)) hG]

end RBM.Gauss.Sizes

/-! ## 7. The skeletons: Step 6 in each regime from its pins (compiled)

Each skeleton takes the ingredient pins of its regime and the compiled glue: the constant `𝔠_d` is the minimum of the constants of the pins
(`st5_conStInd_mono`); the premises of the integrated pin are the Duhamel identity (from `STExpDuhamelZ`), the drift bounds (`(eq:Exp(L-K)1)`
from `STExpLKLKHi`, `(eq:ExpLWn=2)` compiled from `LWtermEXP` by the bridges of §2 and (g)), and the Ward bounds; the initial term is bounded by
the merged kernel theorems `stek_sumNdecay_holds`, `stek_nonzero_holds` (proved) applied to the deterministic tensor `f_s`, with the
hypothesis `(Eq:Gtlp_exp+IND)` (`STExp2` at `s`); the closing comparisons are §6. -/

namespace RBM.Gauss.Sizes

open RBM RBM.Loop RBM.Path RBM.Gauss

variable {d : ℕ} (sz : Sizes d)

/-- `|E_n| ≤ 2 - κ` on the flow. -/
theorem st6_flowE_le {κ ε 𝔠 𝔡 : ℝ} {z : ℕ → ℂ} (hz : STFlow sz κ ε 𝔠 𝔡 z) (n : ℕ) :
    |STflowE z n| ≤ 2 - κ := by
  have h := hz.2 n
  have hN : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
  have him : 0 < (z n).im := lt_of_lt_of_le (Real.rpow_pos_of_pos hN _) h.2.1
  have h2 : |lemE (z n)| ≤ 2 - κ := (abs_lemE_le him).trans h.1
  exact h2

/-- `Im m(E) ≥ √(2κ)/2` for `|E| ≤ 2 - κ` (bulk). -/
theorem st6_mE_im_ge {κ E : ℝ} (hκ : 0 < κ) (hE : |E| ≤ 2 - κ) : Real.sqrt (2 * κ) / 2 ≤ (mE E).im := by
  rw [mE_im]
  have hκ2 : κ ≤ 2 := by linarith [abs_nonneg E]
  have hE2 : E ^ 2 ≤ (2 - κ) ^ 2 := by
    have h1 : |E| ^ 2 ≤ (2 - κ) ^ 2 := pow_le_pow_left₀ (abs_nonneg E) hE 2
    rwa [sq_abs] at h1
  have h : 2 * κ ≤ 4 - E ^ 2 := by nlinarith
  have := Real.sqrt_le_sqrt h
  linarith

/-- **`(res_ELK_n=1)` uniformly in `u ∈ [s,t]`** from the per-time pin `STImproveExpAver` (consumers: the Ward pins, `STExpDriftLo`):
for each time sequence `u ∈ [s,t]` the premise `LWAvgLaw` is the section of `STAvgU` (Step 2), the premise `STLK` is the section of
`STLKU` (Step 4), and (g) turns the per-time conclusions into the uniform one. -/
theorem st6_expAvgU_of_pin (hAvg : STImproveExpAver d) (hd : 3 ≤ d) {κ ε 𝔠 𝔡 : ℝ} (hκ : 0 < κ) (hε : 0 < ε)
    (h𝔡 : 0 < 𝔡) {z : ℕ → ℂ} (hflow : STFlow sz κ ε 𝔠 𝔡 z) {s t : ℕ → ℝ} (hs0 : ∀ n, 0 ≤ s n)
    (hst : ∀ n, s n < t n) (htT : ∀ n, t n ≤ lemT (z n)) (hS2 : STStep2Core sz (STflowE z) s t)
    (hLKU : STLKU sz (STflowE z) s t) : STExpAvgU sz (STflowE z) s t := by
  refine st6_precU_of_forall_seq sz hflow.1.2.2.1 (fun n => (hst n).le) (W := fun n => Bool × Zd d (sz.L n))
    (fun n u w => ‖(∫ ω, Lloop sz n (STflowE z n) u (fun _ : Fin 1 => w.1) (fun _ => w.2) ω ∂(sz.seqP)) -
      mSigma (STflowE z n) w.1‖) (fun n u _ => (sz.Bctl n u) ^ 2) ?_
  intro u hsu hut
  exact hAvg hd κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow u (fun n => (hs0 n).trans (hsu n))
    (fun n => (hut n).trans (htT n)) (LWAvgLaw_of_STAvgU_at sz hsu hut hS2.2) (STLK_of_STLKU_at sz hsu hut hLKU)

/-- **`(eq:ExpLWn=2)` uniformly in `u ∈ [s,t]`, compiled from `LWtermEXP`** (LW-14, per time): the premises at the section `u` are the
bridges of §2, the conclusion is converted from `LWE` to `STEGt` by `st6_expEGt_eq`, and (g) makes it uniform; the index set
`ilambda²/L^d ≤ 1-u` of `LWtermEXP` is all of `[s,t]` in the window `STDriftHi`. -/
theorem st6_EGtHi_of_LW (hLW : LWtermEXP d) (hd : 3 ≤ d) {κ ε 𝔠 𝔡 : ℝ} (hκ : 0 < κ) (hε : 0 < ε) (h𝔡 : 0 < 𝔡)
    {z : ℕ → ℂ} (hflow : STFlow sz κ ε 𝔠 𝔡 z) {s t : ℕ → ℝ} (hs0 : ∀ n, 0 ≤ s n) (hst : ∀ n, s n < t n)
    (htT : ∀ n, t n ≤ lemT (z n)) (hHi : STDriftHi sz s t) (hS2 : STStep2Core sz (STflowE z) s t)
    (hLmax : STLmaxU sz (STflowE z) s t) (hLKU : STLKU sz (STflowE z) s t)
    (hS5 : STGdecayW sz (STflowE z) s t 0) : STExpEGtHiConcl sz (STflowE z) s t := by
  refine st6_precU_of_forall_seq sz hflow.1.2.2.1 (fun n => (hst n).le)
    (W := fun n => (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)))
    (fun n u w => ‖STExpEGt sz n (STflowE z n) u w.1 w.2‖)
    (fun n u _ => (1 - u)⁻¹ * (sz.Bctl n u) ^ (5 / 2 : ℝ)) ?_
  intro u hsu hut
  have h1 := hLW hd κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow u (fun n => (hs0 n).trans (hsu n))
    (fun n => (hut n).trans (htT n)) (STLocalEntry_of_STLocalEntryU_at sz hsu hut hS2.1)
    (LWAvgLaw_of_STAvgU_at sz hsu hut hS2.2) (STLmax_of_STLmaxU_at sz hsu hut hLmax)
    (STLK_of_STLKU_at sz hsu hut hLKU) (STDecay_of_STGdecayW_at sz hsu hut hS5)
  have h2 := StochDomAt.precomp_param h1
    (fun n (w : (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n))) =>
      (⟨w, (hHi n).trans (by have := hut n; linarith)⟩ :
        {_p : (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)) // sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ d ≤ 1 - u n}))
  have e : (fun n (w : (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n))) (_ : sz.SeqΩ) =>
        ‖STExpEGt sz n (STflowE z n) (u n) w.1 w.2‖) =
      (fun n (w : (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n))) (_ : sz.SeqΩ) =>
        ‖∫ ω, LWE sz n (STflowE z n) (u n) w.1 w.2 ω ∂(sz.seqP)‖) := by
    funext n w ω
    rw [st6_expEGt_eq]
  rw [e]
  exact h2

/-- **The initial term of regimes (iii), (iv)**: `‖𝒰_{s,u} f_s‖ ≺ ((1-s)/(1-u))² T_s` uniformly in `(u,σ,a)`, from `(sum_res_Ndecay)` with `n = 2`
(`stek_sumNdecay_holds`) applied to the deterministic tensor `f_s`, `‖f_s‖_∞ ≺ T_s` being `(Eq:Gtlp_exp+IND)`. -/
theorem st6_ini_sumNdecay (hd : 3 ≤ d) {κ ε 𝔠 𝔡 : ℝ} (hκ : 0 < κ) {z : ℕ → ℂ} (hflow : STFlow sz κ ε 𝔠 𝔡 z)
    {s t : ℕ → ℝ} (hs0 : ∀ n, 0 ≤ s n) (hst : ∀ n, s n < t n) (htT : ∀ n, t n ≤ lemT (z n))
    (hExp : STExp2 sz (STflowE z) s) :
    sz.Prec (U := fun n => TimeIcc s t n × (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)))
      (fun n p _ => ‖RBM.Ind.Ugen d (sz.L n) (sz.lam n) (STflowE z n) p.2.1 (s n) (p.1 : ℝ)
        (fun b => STExpErr sz n (STflowE z n) (s n) p.2.1 b) p.2.2‖)
      (fun n p _ => ((1 - s n) / (1 - (p.1 : ℝ))) ^ 2 * STExpTarget sz n (s n)) := by
  have hsz : sz.SizeTendsto := hflow.1.2.2.1
  have ht1 := st5_t_lt_one sz hflow htT
  have hX : ∀ n, 0 ≤ STExpTarget sz n (s n) := fun n => st6_target_nonneg sz n (lt_trans (hst n) (ht1 n))
  refine st6_precU_of_forall_seq sz hsz (fun n => (hst n).le)
    (W := fun n => (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)))
    (fun n u w => ‖RBM.Ind.Ugen d (sz.L n) (sz.lam n) (STflowE z n) w.1 (s n) u
      (fun b => STExpErr sz n (STflowE z n) (s n) w.1 b) w.2‖)
    (fun n u _ => ((1 - s n) / (1 - u)) ^ 2 * STExpTarget sz n (s n)) ?_
  intro u hsu hut
  have hu1 : ∀ n, u n < 1 := fun n => lt_of_le_of_lt (hut n) (ht1 n)
  have key : ∀ σ : Fin 2 → Bool, sz.Prec (U := fun n => Fin 2 → Zd d (sz.L n))
      (fun n a _ => ‖RBM.Ind.Ugen d (sz.L n) (sz.lam n) (STflowE z n) σ (s n) (u n)
        (fun b => STExpErr sz n (STflowE z n) (s n) σ b) a‖)
      (fun n _ _ => ((1 - s n) / (1 - u n)) ^ 2 * STExpTarget sz n (s n)) := by
    intro σ
    have hdom := st6_prec_pi_norm sz hsz (E := STflowE z) (s := s) hX hExp σ (V := fun n => TimeIcc s u n)
    have hk := stek_sumNdecay_holds d hd 2 le_rfl 𝔠 𝔡 sz hflow.1 s u hs0 hsu hu1
      (fun n => mE (STflowE z n)) (fun n => norm_mE (st6_flowE_lt_two sz hκ hflow n).le) σ
      (fun n _ _ => fun b => STExpErr sz n (STflowE z n) (s n) σ b)
      (fun n _ _ => STExpTarget sz n (s n)) (fun n _ _ => hX n) hdom
    have h2 := StochDomAt.precomp_param hk
      (fun n (_ : Fin 2 → Zd d (sz.L n)) => (⟨s n, le_rfl, hsu n⟩ : TimeIcc s u n))
    refine StochDomAt.of_le_left (ξ₁ := fun n (_ : Fin 2 → Zd d (sz.L n)) (_ : sz.SeqΩ) =>
      ‖UN d (sz.L n) (sz.lam n) (EKsgn (mE (STflowE z n)) σ) (s n) (u n)
        (fun b => STExpErr sz n (STflowE z n) (s n) σ b)‖) (fun n a ω => ?_) h2
    exact norm_le_pi_norm (UN d (sz.L n) (sz.lam n) (EKsgn (mE (STflowE z n)) σ) (s n) (u n)
      (fun b => STExpErr sz n (STflowE z n) (s n) σ b)) a
  exact st6_prec_of_forall_fin sz hsz
    (fun n (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) (_ : sz.SeqΩ) =>
      ‖RBM.Ind.Ugen d (sz.L n) (sz.lam n) (STflowE z n) σ (s n) (u n)
        (fun b => STExpErr sz n (STflowE z n) (s n) σ b) a‖)
    (fun n _ _ _ => ((1 - s n) / (1 - u n)) ^ 2 * STExpTarget sz n (s n)) key

end RBM.Gauss.Sizes

namespace RBM.Gauss.Sizes

open RBM RBM.Loop RBM.Path RBM.Gauss

variable {d : ℕ} (sz : Sizes d)

/-- **The initial term of regime (ii) (and (iv)-type zero modes)**: `‖Q^{(A)} 𝒰_{s,u} f_s‖ ≺ T_s` uniformly in `(u,σ,a)`, for the sign
class `P` and `A ⊇ I_diff(σ)` (`(sum_res_Ndecay_nonzero)` `3_5:1667`, the merged `stek_nonzero_holds`, window `1-s ≤ ilambda²/L²`;
no decay hypothesis, no ratio). -/
theorem st6_ini_nonzero (hd : 3 ≤ d) {κ ε 𝔠 𝔡 : ℝ} (hκ : 0 < κ) {z : ℕ → ℂ} (hflow : STFlow sz κ ε 𝔠 𝔡 z)
    {s t : ℕ → ℝ} (hs0 : ∀ n, 0 ≤ s n) (hst : ∀ n, s n < t n) (htT : ∀ n, t n ≤ lemT (z n))
    (hsg : ∀ n, 1 - sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 ≤ s n) (hExp : STExp2 sz (STflowE z) s)
    (A : Finset (Fin 2)) (P : (Fin 2 → Bool) → Prop)
    (hA : ∀ σ, P σ → ∀ i, σ i ≠ σ (finRotate 2 i) → i ∈ A) :
    sz.Prec (U := STIdx2P sz P s t)
      (fun n p _ => ‖zeroModeSet d (sz.L n) A (RBM.Ind.Ugen d (sz.L n) (sz.lam n) (STflowE z n) p.2.1.1 (s n)
        (p.1 : ℝ) (fun b => STExpErr sz n (STflowE z n) (s n) p.2.1.1 b)) p.2.2‖)
      (fun n _ _ => STExpTarget sz n (s n)) := by
  have hsz : sz.SizeTendsto := hflow.1.2.2.1
  have ht1 := st5_t_lt_one sz hflow htT
  have hX : ∀ n, 0 ≤ STExpTarget sz n (s n) := fun n => st6_target_nonneg sz n (lt_trans (hst n) (ht1 n))
  have hκ' : 0 < Real.sqrt (2 * κ) / 2 := by positivity
  refine st6_precU_of_forall_seq sz hsz (fun n => (hst n).le)
    (W := fun n => {σ : Fin 2 → Bool // P σ} × (Fin 2 → Zd d (sz.L n)))
    (fun n u w => ‖zeroModeSet d (sz.L n) A (RBM.Ind.Ugen d (sz.L n) (sz.lam n) (STflowE z n) w.1.1 (s n) u
      (fun b => STExpErr sz n (STflowE z n) (s n) w.1.1 b)) w.2‖)
    (fun n _ _ => STExpTarget sz n (s n)) ?_
  intro u hsu hut
  have hu1 : ∀ n, u n < 1 := fun n => lt_of_le_of_lt (hut n) (ht1 n)
  have key : ∀ σ : {σ : Fin 2 → Bool // P σ}, sz.Prec (U := fun n => Fin 2 → Zd d (sz.L n))
      (fun n a _ => ‖zeroModeSet d (sz.L n) A (RBM.Ind.Ugen d (sz.L n) (sz.lam n) (STflowE z n) σ.1 (s n) (u n)
        (fun b => STExpErr sz n (STflowE z n) (s n) σ.1 b)) a‖)
      (fun n _ _ => STExpTarget sz n (s n)) := by
    intro σ
    have hdom := st6_prec_pi_norm sz hsz (E := STflowE z) (s := s) hX hExp σ.1 (V := fun n => TimeIcc s u n)
    have hk := stek_nonzero_holds d hd 2 le_rfl (Real.sqrt (2 * κ) / 2) 𝔠 𝔡 hκ' sz hflow.1 s u hsg hs0 hsu hu1
      (fun n => mE (STflowE z n)) (fun n => norm_mE (st6_flowE_lt_two sz hκ hflow n).le)
      (fun n => st6_mE_im_ge hκ (st6_flowE_le sz hflow n)) σ.1 A (hA σ.1 σ.2)
      (fun n _ _ => fun b => STExpErr sz n (STflowE z n) (s n) σ.1 b)
      (fun n _ _ => STExpTarget sz n (s n)) (fun n _ _ => hX n) hdom
    have h2 := StochDomAt.precomp_param hk
      (fun n (_ : Fin 2 → Zd d (sz.L n)) => (⟨s n, le_rfl, hsu n⟩ : TimeIcc s u n))
    refine StochDomAt.of_le_left (ξ₁ := fun n (_ : Fin 2 → Zd d (sz.L n)) (_ : sz.SeqΩ) =>
      ‖zeroModeSet d (sz.L n) A (UN d (sz.L n) (sz.lam n) (EKsgn (mE (STflowE z n)) σ.1) (s n) (u n)
        (fun b => STExpErr sz n (STflowE z n) (s n) σ.1 b))‖) (fun n a ω => ?_) h2
    exact norm_le_pi_norm (zeroModeSet d (sz.L n) A (UN d (sz.L n) (sz.lam n) (EKsgn (mE (STflowE z n)) σ.1)
      (s n) (u n) (fun b => STExpErr sz n (STflowE z n) (s n) σ.1 b))) a
  exact st6_prec_of_forall_fin sz hsz
    (fun n (σ : {σ : Fin 2 → Bool // P σ}) (a : Fin 2 → Zd d (sz.L n)) (_ : sz.SeqΩ) =>
      ‖zeroModeSet d (sz.L n) A (RBM.Ind.Ugen d (sz.L n) (sz.lam n) (STflowE z n) σ.1 (s n) (u n)
        (fun b => STExpErr sz n (STflowE z n) (s n) σ.1 b)) a‖)
    (fun n _ _ _ => STExpTarget sz n (s n)) key

/-- Reindexing `(u,σ,a)` of `STExp2U` and of the sign class `P`: a `Prec` for the sign classes `P`, `¬P`... is combined by `st5_prec_cover`. -/
theorem st6_cover_exp2U {s t : ℕ → ℝ} {ξ ζ : ∀ n, TimeIcc s t n → (Fin 2 → Bool) → (Fin 2 → Zd d (sz.L n)) → ℝ}
    (hsz : sz.SizeTendsto) {P₁ P₂ : (Fin 2 → Bool) → Prop} (hcov : ∀ σ, P₁ σ ∨ P₂ σ)
    (h₁ : sz.Prec (U := STIdx2P sz P₁ s t) (fun n p _ => ξ n p.1 p.2.1.1 p.2.2) (fun n p _ => ζ n p.1 p.2.1.1 p.2.2))
    (h₂ : sz.Prec (U := STIdx2P sz P₂ s t) (fun n p _ => ξ n p.1 p.2.1.1 p.2.2) (fun n p _ => ζ n p.1 p.2.1.1 p.2.2)) :
    sz.Prec (U := fun n => TimeIcc s t n × (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)))
      (fun n p _ => ξ n p.1 p.2.1 p.2.2) (fun n p _ => ζ n p.1 p.2.1 p.2.2) := by
  refine st5_prec_cover sz hsz (V₁ := STIdx2P sz P₁ s t) (V₂ := STIdx2P sz P₂ s t)
    (fun n p => (p.1, p.2.1.1, p.2.2)) (fun n p => (p.1, p.2.1.1, p.2.2)) ?_ h₁ h₂
  intro n p
  rcases hcov p.2.1 with h | h
  · exact Or.inl ⟨(p.1, ⟨p.2.1, h⟩, p.2.2), rfl⟩
  · exact Or.inr ⟨(p.1, ⟨p.2.1, h⟩, p.2.2), rfl⟩

end RBM.Gauss.Sizes

namespace RBM.Gauss.Sizes

open RBM RBM.Loop RBM.Path RBM.Gauss

variable {d : ℕ} (sz : Sizes d)

/-- For `σ₁ = σ₂`, `I_diff(σ) = ∅` (`3_5:1470`): `A = ∅` is allowed in `(sum_res_Ndecay_nonzero)`. -/
theorem st6_Idiff_same {σ : Fin 2 → Bool} (h : σ 0 = σ 1) (i : Fin 2) : ¬ σ i ≠ σ (finRotate 2 i) := by
  fin_cases i
  · have : finRotate 2 (0 : Fin 2) = 1 := by decide
    simp [this, h]
  · have : finRotate 2 (1 : Fin 2) = 0 := by decide
    simp [this, h]

/-- **(F1) The window of `lem:sum_decay` and regime (ii) exclude each other** (`3_5:1637` against `6:97`; paper-delta candidate `T2191a`): case (i)
of `3_5:1105` (`STCaseI`, `1-t ≥ ilambda²/L²`, the hypothesis `t ≤ 1-ilambda²/L²` of `(sum_res_1)`, `(sum_res_2_NAL)`, `(sum_res_2)`) and regime (ii)
(`1-s ≤ ilambda²/L²`) give `t ≤ s`: no `s < t` in regime (ii) satisfies the hypothesis of `(sum_res_2_NAL)`. -/
theorem st6_F1_window_vs_reg5II {s t : ℕ → ℝ} (hI : STCaseI sz s t) (hII : STReg5II sz s t) (n : ℕ) : t n ≤ s n := by
  have h1 := hI n
  have h2 := (hII n).2
  linarith

/-- **Step 6, regime (iii), from its pins.**  The ingredients are `(eq:Exp(L-K)1)` (`STExpLKLKHi`), `lem:LWterm_EXP` (`LWtermEXP`, the per-time
pin of LW-14, consumed through the bridges of §2 and (g)), the Duhamel identity (`STExpDuhamelZ`) and the integrated estimate
(`STExpIntIII`); the initial term is the merged `(sum_res_Ndecay)` (`st6_ini_sumNdecay`) closed by `st6_xB_III`, `st6_cmp_ini` with the
constant `4`, no `𝔠_d` loss.  The constant `𝔠_d` is the minimum of the constants of the two pins. -/
theorem ST_step6_caseIII_of_pins (hLK : STExpLKLKHi d) (hLW : LWtermEXP d) (hDu : STExpDuhamelZ d)
    (hInt : STExpIntIII d) : STStep6III d := by
  intro hd κ ε 𝔡 hκ hε h𝔡
  obtain ⟨c₁, hc₁, hc₁', H₁⟩ := hLK hd κ ε 𝔡 hκ hε h𝔡
  obtain ⟨c₂, hc₂, hc₂', H₂⟩ := hInt hd κ ε 𝔡 hκ hε h𝔡
  have hcpos : 0 < min c₁ c₂ := lt_min hc₁ hc₂
  refine ⟨min c₁ c₂, hcpos, (min_le_left _ _).trans hc₁', ?_⟩
  intro 𝔠 sz z hflow s t hs0 hst htT hR hLK0 hDec hExp hcon hS2 hLmax hLKU hS5
  have ht1 := st5_t_lt_one sz hflow htT
  have hsz : sz.SizeTendsto := hflow.1.2.2.1
  have hHi := st6_hi_of_reg5III sz hR
  have hlk := H₁ 𝔠 sz z hflow s t hs0 hst htT hHi hLK0 hDec hExp
    (st5_conStInd_mono sz hcon ht1 hcpos (min_le_left _ _)) hS2 hLmax hLKU hS5
  have hegt := st6_EGtHi_of_LW sz hLW hd hκ hε h𝔡 hflow hs0 hst htT hHi hS2 hLmax hLKU hS5
  have hduh := st6_duhEq_of_pin sz hDu hd hκ hflow hs0 htT
  have hint := H₂ 𝔠 sz z hflow s t hs0 hst htT hR hLK0 hDec hExp
    (st5_conStInd_mono sz hcon ht1 hcpos (min_le_right _ _)) hS2 hLmax hLKU hS5 hduh ⟨hlk, hegt⟩
  have hini := st6_ini_sumNdecay sz hd hκ hflow hs0 hst htT hExp
  have hini' : sz.Prec (U := STIdx2P sz STSigAll s t)
      (fun n p _ => ‖zeroModeSet d (sz.L n) ∅ (RBM.Ind.Ugen d (sz.L n) (sz.lam n) (STflowE z n) p.2.1.1 (s n)
        (p.1 : ℝ) (fun b => STExpErr sz n (STflowE z n) (s n) p.2.1.1 b)) p.2.2‖)
      (fun n p _ => ((1 - s n) / (1 - (p.1 : ℝ))) ^ 2 * STExpTarget sz n (s n)) := by
    have := StochDomAt.precomp_param hini (fun n (p : STIdx2P sz STSigAll s t n) =>
      ((p.1, p.2.1.1, p.2.2) : TimeIcc s t n × (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n))))
    simp only [st5_zeroModeSet_empty]
    exact this
  have hF0 : ∀ n (p : STIdx2P sz STSigAll s t n),
      0 ≤ ((1 - s n) / (1 - (p.1 : ℝ))) ^ 2 * STExpTarget sz n (s n) := by
    intro n p
    have hx : 0 ≤ (1 - s n) / (1 - (p.1 : ℝ)) :=
      div_nonneg (by linarith [hst n, ht1 n]) (by linarith [p.1.2.2, ht1 n])
    exact mul_nonneg (pow_nonneg hx 2) (st6_target_nonneg sz n (lt_trans (hst n) (ht1 n)))
  have hmain := hint (fun n p => ((1 - s n) / (1 - (p.1 : ℝ))) ^ 2 * STExpTarget sz n (s n)) hF0 hini'
  have h5 := st5_prec_mono sz hsz (c := 5) hmain
    (Eventually.of_forall fun n p ω => ?_)
    (fun n p ω => st6_target_nonneg sz n (lt_of_le_of_lt p.1.2.2 (ht1 n)))
  · have h6 := StochDomAt.precomp_param h5 (fun n (p : STIdx2 sz s t n) =>
      ((p.1, ⟨p.2.1, trivial⟩, p.2.2) : STIdx2P sz STSigAll s t n))
    simp only [st5_zeroModeSet_empty] at h6
    exact h6
  · have hu1 : (p.1 : ℝ) < 1 := lt_of_le_of_lt p.1.2.2 (ht1 n)
    have hxB := st6_xB_III sz n p.1.2.1 hu1 ((hR n).trans (by linarith [p.1.2.2]))
    have := st6_cmp_ini sz n p.1.2.1 hu1 hxB
    change ((1 - s n) / (1 - (p.1 : ℝ))) ^ 2 * STExpTarget sz n (s n) + STExpTarget sz n (p.1 : ℝ) ≤
      5 * STExpTarget sz n (p.1 : ℝ)
    linarith

/-- **Step 6, regime (iv), from its pins.**  `STExpDriftLo` carries `(eq:Exp(L-K)2)`, `(eq:ExpLWn=2_smalleta)`; its premise `(res_ELK_n=1)`
is compiled from `STImproveExpAver` (`st6_expAvgU_of_pin`, (g)); the initial term is `(sum_res_Ndecay)` closed by `st6_xB_IV` (constant `4`). -/
theorem ST_step6_caseIV_of_pins (hAvg : STImproveExpAver d) (hDu : STExpDuhamelZ d) (hLo : STExpDriftLo d)
    (hInt : STExpIntIV d) : STStep6IV d := by
  intro hd κ ε 𝔡 hκ hε h𝔡
  obtain ⟨c₁, hc₁, hc₁', H₁⟩ := hLo hd κ ε 𝔡 hκ hε h𝔡
  obtain ⟨c₂, hc₂, hc₂', H₂⟩ := hInt hd κ ε 𝔡 hκ hε h𝔡
  have hcpos : 0 < min c₁ c₂ := lt_min hc₁ hc₂
  refine ⟨min c₁ c₂, hcpos, (min_le_left _ _).trans hc₁', ?_⟩
  intro 𝔠 sz z hflow s t hs0 hst htT hR hLK0 hDec hExp hcon hS2 hLmax hLKU hS5
  have ht1 := st5_t_lt_one sz hflow htT
  have hsz : sz.SizeTendsto := hflow.1.2.2.1
  have hAvgU := st6_expAvgU_of_pin sz hAvg hd hκ hε h𝔡 hflow hs0 hst htT hS2 hLKU
  have hlo := H₁ 𝔠 sz z hflow s t hs0 hst htT hR hLK0 hDec hExp
    (st5_conStInd_mono sz hcon ht1 hcpos (min_le_left _ _)) hS2 hLmax hLKU hS5 hAvgU
  have hduh := st6_duhEq_of_pin sz hDu hd hκ hflow hs0 htT
  have hint := H₂ 𝔠 sz z hflow s t hs0 hst htT hR hLK0 hDec hExp
    (st5_conStInd_mono sz hcon ht1 hcpos (min_le_right _ _)) hS2 hLmax hLKU hS5 hduh hlo
  have hini := st6_ini_sumNdecay sz hd hκ hflow hs0 hst htT hExp
  have hini' : sz.Prec (U := STIdx2P sz STSigAll s t)
      (fun n p _ => ‖zeroModeSet d (sz.L n) ∅ (RBM.Ind.Ugen d (sz.L n) (sz.lam n) (STflowE z n) p.2.1.1 (s n)
        (p.1 : ℝ) (fun b => STExpErr sz n (STflowE z n) (s n) p.2.1.1 b)) p.2.2‖)
      (fun n p _ => ((1 - s n) / (1 - (p.1 : ℝ))) ^ 2 * STExpTarget sz n (s n)) := by
    have := StochDomAt.precomp_param hini (fun n (p : STIdx2P sz STSigAll s t n) =>
      ((p.1, p.2.1.1, p.2.2) : TimeIcc s t n × (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n))))
    simp only [st5_zeroModeSet_empty]
    exact this
  have hF0 : ∀ n (p : STIdx2P sz STSigAll s t n),
      0 ≤ ((1 - s n) / (1 - (p.1 : ℝ))) ^ 2 * STExpTarget sz n (s n) := by
    intro n p
    have hx : 0 ≤ (1 - s n) / (1 - (p.1 : ℝ)) :=
      div_nonneg (by linarith [hst n, ht1 n]) (by linarith [p.1.2.2, ht1 n])
    exact mul_nonneg (pow_nonneg hx 2) (st6_target_nonneg sz n (lt_trans (hst n) (ht1 n)))
  have hmain := hint (fun n p => ((1 - s n) / (1 - (p.1 : ℝ))) ^ 2 * STExpTarget sz n (s n)) hF0 hini'
  have h5 := st5_prec_mono sz hsz (c := 5) hmain
    (Eventually.of_forall fun n p ω => ?_)
    (fun n p ω => st6_target_nonneg sz n (lt_of_le_of_lt p.1.2.2 (ht1 n)))
  · have h6 := StochDomAt.precomp_param h5 (fun n (p : STIdx2 sz s t n) =>
      ((p.1, ⟨p.2.1, trivial⟩, p.2.2) : STIdx2P sz STSigAll s t n))
    simp only [st5_zeroModeSet_empty] at h6
    exact h6
  · have hu1 : (p.1 : ℝ) < 1 := lt_of_le_of_lt p.1.2.2 (ht1 n)
    have hxB := st6_xB_IV sz n p.1.2.1 hu1 (hR n)
    have := st6_cmp_ini sz n p.1.2.1 hu1 hxB
    change ((1 - s n) / (1 - (p.1 : ℝ))) ^ 2 * STExpTarget sz n (s n) + STExpTarget sz n (p.1 : ℝ) ≤
      5 * STExpTarget sz n (p.1 : ℝ)
    linarith

/-- The `𝒬`-Duhamel identity along `[s_n,t_n]` for a mollifier family, eventually in `n`, from the pin `STExpDuhamelQ`. -/
theorem st6_duhEqQ_of_pin (hDu : STExpDuhamelQ d) (hd : 3 ≤ d) {κ ε 𝔠 𝔡 : ℝ} (hκ : 0 < κ) {z : ℕ → ℂ}
    (hflow : STFlow sz κ ε 𝔠 𝔡 z) {s t : ℕ → ℝ} (hs0 : ∀ n, 0 ≤ s n) (htT : ∀ n, t n ≤ lemT (z n))
    (C c : ℝ) (ϑ : ∀ n : ℕ, ℝ → (Fin 2 → Zd d (sz.L n)) → ℂ)
    (hϑ : ∀ᶠ n in atTop, STMollifierProps (d := d) (sz.lam n) C c (ϑ n)) :
    STExpDuhEqQ sz (STflowE z) s t ϑ := by
  filter_upwards [hϑ] with n hn
  intro u σ a
  exact hDu hd sz n (STflowE z n) (st6_flowE_lt_two sz hκ hflow n) C c (ϑ n) hn (s n) u (hs0 n) u.2.1
    (lt_of_le_of_lt u.2.2 (st5_t_lt_one sz hflow htT n)) σ a

/-- **A mollifier family** (`Def:QtPt`, `rmk:choosechi`): from the proved `stMollifierEx_holds` (`Induction/QopAlgebra.lean:573`) at `m = 1`,
`Λ = 𝔡⁻¹`; `STMollifierProps` holds eventually (`0 < lam n ≤ 𝔡⁻¹` eventually by `(eq:WO)`). -/
theorem st6_mollifier_family (hd : 3 ≤ d) {𝔡 : ℝ} (h𝔡 : 0 < 𝔡) (hWO : sz.WO 𝔡) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∃ ϑ : ∀ n : ℕ, ℝ → (Fin 2 → Zd d (sz.L n)) → ℂ,
      ∀ᶠ n in atTop, STMollifierProps (d := d) (sz.lam n) C c (ϑ n) := by
  obtain ⟨C, c, hC, hc, hex⟩ := stMollifierEx_holds d hd 1 𝔡⁻¹ (inv_pos.2 h𝔡)
  have hall : ∀ n, ∃ ϑ : ℝ → (Fin 2 → Zd d (sz.L n)) → ℂ,
      (0 < sz.lam n ∧ sz.lam n ≤ 𝔡⁻¹) → STMollifierProps (d := d) (sz.lam n) C c ϑ := by
    intro n
    by_cases h : 0 < sz.lam n ∧ sz.lam n ≤ 𝔡⁻¹
    · obtain ⟨ϑ, hϑ⟩ := hex (sz.L n) (sz.three_le_L n) (sz.lam n) h.1 h.2
      exact ⟨ϑ, fun _ => hϑ⟩
    · exact ⟨fun _ _ => 0, fun h' => absurd h' h⟩
  choose ϑ hϑ using hall
  refine ⟨C, c, hC, hc, ϑ, ?_⟩
  filter_upwards [st6_lam_pos sz hWO, hWO] with n hn1 hn2
  exact hϑ n ⟨hn1, hn2.2⟩

/-- **Step 6, regime (ii), from its pins.**  The drift bounds are those of the window (`STExpLKLKHi`, `LWtermEXP`); the integrated pin `STExpIntII`
gives `Q^{({1,2})} f_u` (`σ₁ ≠ σ₂`) and `f_u` (`σ₁ = σ₂`, `A = ∅`: paper-delta candidate `T2191a`) from the initial terms
`st6_ini_nonzero` (`(sum_res_Ndecay_nonzero)`, constant `1`); `f_u = Q^{({1,2})} f_u + (f_u - Q^{({1,2})} f_u)` and the Ward
decomposition `STExpWardII` (`≺ B³ ≤ T`) close `σ₁ ≠ σ₂`; the two sign classes are glued by `st6_cover_exp2U`. -/
theorem ST_step6_caseII_of_pins (hLK : STExpLKLKHi d) (hLW : LWtermEXP d) (hAvg : STImproveExpAver d)
    (hDu : STExpDuhamelZ d) (hInt : STExpIntII d) (hWd : STExpWardII d) : STStep6II d := by
  intro hd κ ε 𝔡 hκ hε h𝔡
  obtain ⟨c₁, hc₁, hc₁', H₁⟩ := hLK hd κ ε 𝔡 hκ hε h𝔡
  obtain ⟨c₂, hc₂, hc₂', H₂⟩ := hInt hd κ ε 𝔡 hκ hε h𝔡
  obtain ⟨c₃, hc₃, hc₃', H₃⟩ := hWd hd κ ε 𝔡 hκ hε h𝔡
  have hcpos : 0 < min c₁ (min c₂ c₃) := lt_min hc₁ (lt_min hc₂ hc₃)
  refine ⟨min c₁ (min c₂ c₃), hcpos, (min_le_left _ _).trans hc₁', ?_⟩
  intro 𝔠 sz z hflow s t hs0 hst htT hR hLK0 hDec hExp hcon hS2 hLmax hLKU hS5
  have ht1 := st5_t_lt_one sz hflow htT
  have hsz : sz.SizeTendsto := hflow.1.2.2.1
  have hHi := st6_hi_of_reg5II sz hR
  have hAvgU := st6_expAvgU_of_pin sz hAvg hd hκ hε h𝔡 hflow hs0 hst htT hS2 hLKU
  have hlk := H₁ 𝔠 sz z hflow s t hs0 hst htT hHi hLK0 hDec hExp
    (st5_conStInd_mono sz hcon ht1 hcpos (min_le_left _ _)) hS2 hLmax hLKU hS5
  have hegt := st6_EGtHi_of_LW sz hLW hd hκ hε h𝔡 hflow hs0 hst htT hHi hS2 hLmax hLKU hS5
  have hduh := st6_duhEq_of_pin sz hDu hd hκ hflow hs0 htT
  have hint := H₂ 𝔠 sz z hflow s t hs0 hst htT hR hLK0 hDec hExp
    (st5_conStInd_mono sz hcon ht1 hcpos ((min_le_right _ _).trans (min_le_left _ _))) hS2 hLmax hLKU hS5
    hduh ⟨hlk, hegt⟩
  have hward := H₃ 𝔠 sz z hflow s t hs0 hst htT hR hLK0 hDec hExp
    (st5_conStInd_mono sz hcon ht1 hcpos ((min_le_right _ _).trans (min_le_right _ _))) hS2 hLmax hLKU hS5
    hAvgU
  have hsg : ∀ n, 1 - sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 ≤ s n := fun n => by linarith [(hR n).2]
  have hT0 : ∀ n (u : ℝ), u ≤ t n → 0 ≤ STExpTarget sz n u := fun n u hu =>
    st6_target_nonneg sz n (lt_of_le_of_lt hu (ht1 n))
  -- initial terms: `(sum_res_Ndecay_nonzero)`
  have hiniM := st6_ini_nonzero sz hd hκ hflow hs0 hst htT hsg hExp (Finset.univ : Finset (Fin 2)) STSigMixed
    (fun σ _ i _ => Finset.mem_univ i)
  have hiniS := st6_ini_nonzero sz hd hκ hflow hs0 hst htT hsg hExp (∅ : Finset (Fin 2)) STSigSame
    (fun σ hσ i hi => absurd hi (st6_Idiff_same hσ i))
  have hmainM := hint.1 (fun n p => STExpTarget sz n (s n))
    (fun n p => hT0 n (s n) (hst n).le) hiniM
  have hmainS := hint.2 (fun n p => STExpTarget sz n (s n))
    (fun n p => hT0 n (s n) (hst n).le) hiniS
  -- `σ₁ = σ₂`
  have hS : sz.Prec (U := STIdx2P sz STSigSame s t)
      (fun n p _ => ‖STExpErr sz n (STflowE z n) (p.1 : ℝ) p.2.1.1 p.2.2‖)
      (fun n p _ => STExpTarget sz n (p.1 : ℝ)) := by
    simp only [st5_zeroModeSet_empty] at hmainS
    refine st5_prec_mono sz hsz (c := 2) hmainS (Eventually.of_forall fun n p ω => ?_)
      (fun n p ω => hT0 n _ p.1.2.2)
    have := st6_target_mono sz n p.1.2.1 (lt_of_le_of_lt p.1.2.2 (ht1 n))
    change STExpTarget sz n (s n) + STExpTarget sz n (p.1 : ℝ) ≤ 2 * STExpTarget sz n (p.1 : ℝ)
    linarith
  -- `σ₁ ≠ σ₂`
  have hM : sz.Prec (U := STIdx2P sz STSigMixed s t)
      (fun n p _ => ‖STExpErr sz n (STflowE z n) (p.1 : ℝ) p.2.1.1 p.2.2‖)
      (fun n p _ => STExpTarget sz n (p.1 : ℝ)) := by
    have hsum := StochDomAt.add (tendsto_size sz hsz) hmainM hward
    have hsum' : sz.Prec (U := STIdx2P sz STSigMixed s t)
        (fun n p _ => ‖STExpErr sz n (STflowE z n) (p.1 : ℝ) p.2.1.1 p.2.2‖)
        (fun n p _ => (STExpTarget sz n (s n) + STExpTarget sz n (p.1 : ℝ)) + (sz.Bctl n (p.1 : ℝ)) ^ 3) := by
      refine StochDomAt.of_le_left (fun n p ω => ?_) hsum
      change ‖STExpErr sz n (STflowE z n) (p.1 : ℝ) p.2.1.1 p.2.2‖ ≤
        ‖zeroModeSet d (sz.L n) (Finset.univ : Finset (Fin 2))
          (fun b => STExpErr sz n (STflowE z n) (p.1 : ℝ) p.2.1.1 b) p.2.2‖ +
        ‖STExpErr sz n (STflowE z n) (p.1 : ℝ) p.2.1.1 p.2.2 -
          zeroModeSet d (sz.L n) (Finset.univ : Finset (Fin 2))
            (fun b => STExpErr sz n (STflowE z n) (p.1 : ℝ) p.2.1.1 b) p.2.2‖
      calc ‖STExpErr sz n (STflowE z n) (p.1 : ℝ) p.2.1.1 p.2.2‖
          = ‖zeroModeSet d (sz.L n) (Finset.univ : Finset (Fin 2))
              (fun b => STExpErr sz n (STflowE z n) (p.1 : ℝ) p.2.1.1 b) p.2.2 +
            (STExpErr sz n (STflowE z n) (p.1 : ℝ) p.2.1.1 p.2.2 -
              zeroModeSet d (sz.L n) (Finset.univ : Finset (Fin 2))
                (fun b => STExpErr sz n (STflowE z n) (p.1 : ℝ) p.2.1.1 b) p.2.2)‖ := by ring_nf
        _ ≤ _ := norm_add_le _ _
    refine st5_prec_mono sz hsz (c := 3) hsum' (Eventually.of_forall fun n p ω => ?_)
      (fun n p ω => hT0 n _ p.1.2.2)
    have h1 := st6_target_mono sz n p.1.2.1 (lt_of_le_of_lt p.1.2.2 (ht1 n))
    have h2 := st6_cube_le_target sz n (lt_of_le_of_lt p.1.2.2 (ht1 n))
    change STExpTarget sz n (s n) + STExpTarget sz n (p.1 : ℝ) + (sz.Bctl n (p.1 : ℝ)) ^ 3 ≤
      3 * STExpTarget sz n (p.1 : ℝ)
    linarith
  exact st6_cover_exp2U sz (ξ := fun n u σ a => ‖STExpErr sz n (STflowE z n) (u : ℝ) σ a‖)
    (ζ := fun n u _ _ => STExpTarget sz n (u : ℝ)) hsz (P₁ := STSigSame) (P₂ := STSigMixed)
    (fun σ => by by_cases h : σ 0 = σ 1 <;> simp [STSigSame, STSigMixed, h]) hS hM

/-- **Step 6, regime (i), from its pins.**  `σ₁ = σ₂`: the plain Duhamel (`STExpIntI.1`) with the initial term `STExpIniI.1`
(`(sum_res_2_NAL)`, ratio `≤ 2`); `σ₁ ≠ σ₂`: for a mollifier family (`st6_mollifier_family`, from the proved `stMollifierEx_holds`) the
`𝒬`-Duhamel (`STExpIntI.2`, identity from `STExpDuhamelQ`) with the initial term `STExpIniI.2` and `f_u = 𝒬_u f_u + (𝒫 f_u) ϑ_u`,
`(𝒫 f_u) ϑ_u ≺ B³` from `STExpWardI` (`(eq:EPL-K)`); the premise `(res_ELK_n=1)` of the Ward pin is compiled from `STImproveExpAver`. -/
theorem ST_step6_caseI_of_pins (hLK : STExpLKLKHi d) (hLW : LWtermEXP d) (hAvg : STImproveExpAver d)
    (hDu : STExpDuhamelZ d) (hDuQ : STExpDuhamelQ d) (hDec : STExpDriftDecay d) (hWd : STExpWardI d)
    (hIni : STExpIniI d) (hInt : STExpIntI d) : STStep6I d := by
  intro hd κ ε 𝔡 hκ hε h𝔡
  obtain ⟨c₁, hc₁, hc₁', H₁⟩ := hLK hd κ ε 𝔡 hκ hε h𝔡
  obtain ⟨c₂, hc₂, hc₂', H₂⟩ := hDec hd κ ε 𝔡 hκ hε h𝔡
  obtain ⟨c₃, hc₃, hc₃', H₃⟩ := hWd hd κ ε 𝔡 hκ hε h𝔡
  obtain ⟨c₄, hc₄, hc₄', H₄⟩ := hIni hd κ ε 𝔡 hκ hε h𝔡
  obtain ⟨c₅, hc₅, hc₅', H₅⟩ := hInt hd κ ε 𝔡 hκ hε h𝔡
  have hcpos : 0 < min c₁ (min c₂ (min c₃ (min c₄ c₅))) :=
    lt_min hc₁ (lt_min hc₂ (lt_min hc₃ (lt_min hc₄ hc₅)))
  refine ⟨min c₁ (min c₂ (min c₃ (min c₄ c₅))), hcpos, (min_le_left _ _).trans hc₁', ?_⟩
  intro 𝔠 sz z hflow s t hs0 hst htT hR hLK0 hDec0 hExp hcon hS2 hLmax hLKU hS5
  have ht1 := st5_t_lt_one sz hflow htT
  have hsz : sz.SizeTendsto := hflow.1.2.2.1
  have m : ∀ c', min c₁ (min c₂ (min c₃ (min c₄ c₅))) ≤ c' → STConStInd sz c' s t :=
    fun c' hcc => st5_conStInd_mono sz hcon ht1 hcpos hcc
  have hm1 := m c₁ (min_le_left _ _)
  have hm2 := m c₂ ((min_le_right _ _).trans (min_le_left _ _))
  have hm3 := m c₃ ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hm4 := m c₄ ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
  have hm5 := m c₅ ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))
  have hHi := st6_hi_of_reg5I sz (by omega) hR
  have hAvgU := st6_expAvgU_of_pin sz hAvg hd hκ hε h𝔡 hflow hs0 hst htT hS2 hLKU
  have hlk := H₁ 𝔠 sz z hflow s t hs0 hst htT hHi hLK0 hDec0 hExp hm1 hS2 hLmax hLKU hS5
  have hegt := st6_EGtHi_of_LW sz hLW hd hκ hε h𝔡 hflow hs0 hst htT hHi hS2 hLmax hLKU hS5
  have hdec := H₂ 𝔠 sz z hflow s t hs0 hst htT hR hLK0 hDec0 hExp hm2 hS2 hLmax hLKU hS5
  have hward := H₃ 𝔠 sz z hflow s t hs0 hst htT hR hLK0 hDec0 hExp hm3 hS2 hLmax hLKU hS5 hAvgU
  have hini := H₄ 𝔠 sz z hflow s t hs0 hst htT hR hLK0 hDec0 hExp hm4 hS2 hLmax hLKU hS5
  have hduh := st6_duhEq_of_pin sz hDu hd hκ hflow hs0 htT
  have hint := H₅ 𝔠 sz z hflow s t hs0 hst htT hR hLK0 hDec0 hExp hm5 hS2 hLmax hLKU hS5
    hduh ⟨hlk, hegt⟩ hdec hward
  have hT0 : ∀ n (u : ℝ), u ≤ t n → 0 ≤ STExpTarget sz n u := fun n u hu =>
    st6_target_nonneg sz n (lt_of_le_of_lt hu (ht1 n))
  -- `σ₁ = σ₂`
  have hS : sz.Prec (U := STIdx2P sz STSigSame s t)
      (fun n p _ => ‖STExpErr sz n (STflowE z n) (p.1 : ℝ) p.2.1.1 p.2.2‖)
      (fun n p _ => STExpTarget sz n (p.1 : ℝ)) := by
    have hiniS : sz.Prec (U := STIdx2P sz STSigSame s t)
        (fun n p _ => ‖zeroModeSet d (sz.L n) ∅ (RBM.Ind.Ugen d (sz.L n) (sz.lam n) (STflowE z n) p.2.1.1 (s n)
          (p.1 : ℝ) (fun b => STExpErr sz n (STflowE z n) (s n) p.2.1.1 b)) p.2.2‖)
        (fun n p _ => STExpTarget sz n (p.1 : ℝ)) := by
      simp only [st5_zeroModeSet_empty]
      exact hini.1
    have hmainS := hint.1 (fun n p => STExpTarget sz n (p.1 : ℝ)) (fun n p => hT0 n _ p.1.2.2) hiniS
    simp only [st5_zeroModeSet_empty] at hmainS
    refine st5_prec_mono sz hsz (c := 2) hmainS (Eventually.of_forall fun n p ω => ?_)
      (fun n p ω => hT0 n _ p.1.2.2)
    linarith
  -- `σ₁ ≠ σ₂`
  obtain ⟨C, c', hC, hc', ϑ, hϑ⟩ := st6_mollifier_family sz hd h𝔡 hflow.1.2.2.2.2
  have hduhQ := st6_duhEqQ_of_pin sz hDuQ hd hκ hflow hs0 htT C c' ϑ hϑ
  have hmainQ := hint.2 C c' ϑ hϑ hduhQ (fun n p => STExpTarget sz n (p.1 : ℝ)) (fun n p => hT0 n _ p.1.2.2)
    (hini.2 C c' ϑ hϑ)
  have hw := (hward C c' ϑ hϑ).1
  have hM : sz.Prec (U := STIdx2P sz STSigMixed s t)
      (fun n p _ => ‖STExpErr sz n (STflowE z n) (p.1 : ℝ) p.2.1.1 p.2.2‖)
      (fun n p _ => STExpTarget sz n (p.1 : ℝ)) := by
    have hsum := StochDomAt.add (tendsto_size sz hsz) hmainQ hw
    have hsum' : sz.Prec (U := STIdx2P sz STSigMixed s t)
        (fun n p _ => ‖STExpErr sz n (STflowE z n) (p.1 : ℝ) p.2.1.1 p.2.2‖)
        (fun n p _ => (STExpTarget sz n (p.1 : ℝ) + STExpTarget sz n (p.1 : ℝ)) + (sz.Bctl n (p.1 : ℝ)) ^ 3) := by
      refine StochDomAt.of_le_left (fun n p ω => ?_) hsum
      change ‖STExpErr sz n (STflowE z n) (p.1 : ℝ) p.2.1.1 p.2.2‖ ≤
        ‖STQop (d := d) (ϑ n) (p.1 : ℝ) (fun b => STExpErr sz n (STflowE z n) (p.1 : ℝ) p.2.1.1 b) p.2.2‖ +
        ‖STPsum (d := d) (fun b => STExpErr sz n (STflowE z n) (p.1 : ℝ) p.2.1.1 b) (p.2.2 0) *
          ϑ n (p.1 : ℝ) p.2.2‖
      calc ‖STExpErr sz n (STflowE z n) (p.1 : ℝ) p.2.1.1 p.2.2‖
          = ‖STQop (d := d) (ϑ n) (p.1 : ℝ) (fun b => STExpErr sz n (STflowE z n) (p.1 : ℝ) p.2.1.1 b) p.2.2 +
            STPsum (d := d) (fun b => STExpErr sz n (STflowE z n) (p.1 : ℝ) p.2.1.1 b) (p.2.2 0) *
              ϑ n (p.1 : ℝ) p.2.2‖ := by
            unfold STQop; ring_nf
        _ ≤ _ := norm_add_le _ _
    refine st5_prec_mono sz hsz (c := 3) hsum' (Eventually.of_forall fun n p ω => ?_)
      (fun n p ω => hT0 n _ p.1.2.2)
    have h2 := st6_cube_le_target sz n (lt_of_le_of_lt p.1.2.2 (ht1 n))
    change STExpTarget sz n (p.1 : ℝ) + STExpTarget sz n (p.1 : ℝ) + (sz.Bctl n (p.1 : ℝ)) ^ 3 ≤
      3 * STExpTarget sz n (p.1 : ℝ)
    linarith
  exact st6_cover_exp2U sz (ξ := fun n u σ a => ‖STExpErr sz n (STflowE z n) (u : ℝ) σ a‖)
    (ζ := fun n u _ _ => STExpTarget sz n (u : ℝ)) hsz (P₁ := STSigSame) (P₂ := STSigMixed)
    (fun σ => by by_cases h : σ 0 = σ 1 <;> simp [STSigSame, STSigMixed, h]) hS hM

end RBM.Gauss.Sizes

/-! ## 7b. Two lemmas of the probe's section 7b

`st6_GdecayW_of_zero` (the lossy conjunct of `STStep2Concl` follows from `(Eq:Gdecay_flow)` without loss) and
`ST_step6R_mono` (monotonicity of `STStep6R` in the regime).  The rest of the probe's section 7b (gluing by an
intermediate time) is not ported (DECISIONS §68). -/

namespace RBM.Gauss.Sizes

open RBM RBM.Loop RBM.Path RBM.Gauss

variable {d : ℕ} (sz : Sizes d)

/-- `(Eq:Gdecay_flow)` without loss implies `(Eq:Gdecay_w)` with any loss `C_d ≥ 0` (`((1-s)/(1-u))^{C_d} ≥ 1` for `u ≥ s`): the lossy conjunct of
`STStep2Concl` is not needed by Step 6 (`STStep2Core`). -/
theorem st6_GdecayW_of_zero (hsz : sz.SizeTendsto) {E s t : ℕ → ℝ} (ht1 : ∀ n, t n < 1) {Cd : ℝ} (hCd : 0 ≤ Cd)
    (h : STGdecayW sz E s t 0) : STGdecayW sz E s t Cd := by
  intro D hD
  refine st5_prec_mono sz hsz (c := 1) (h D hD) (Eventually.of_forall fun n p ω => ?_) (fun n p ω => ?_)
  · have h1 : 0 < 1 - (p.1 : ℝ) := by linarith [ht1 n, p.1.2.2]
    have hu : (1 : ℝ) ≤ (1 - s n) / (1 - (p.1 : ℝ)) := by
      rw [le_div_iff₀ h1]; linarith [p.1.2.1]
    have hr : (1 : ℝ) ≤ ((1 - s n) / (1 - (p.1 : ℝ))) ^ Cd := Real.one_le_rpow hu hCd
    have hB : 0 ≤ (sz.Bctl n (p.1 : ℝ)) ^ (1 / 5 : ℝ) :=
      Real.rpow_nonneg (STBctl_pos sz n (by linarith [ht1 n, p.1.2.2])).le _
    have hW : 0 ≤ STWB sz n (p.1 : ℝ) (zdistInf d (sz.L n) (p.2.2 0 - p.2.2 1)) := by
      unfold STWB Bparam; positivity
    have hX : 0 ≤ (sz.Bctl n (p.1 : ℝ)) ^ (1 / 5 : ℝ) * STWB sz n (p.1 : ℝ) (zdistInf d (sz.L n) (p.2.2 0 - p.2.2 1)) *
        Real.exp (-(((zdistInf d (sz.L n) (p.2.2 0 - p.2.2 1) : ℕ) : ℝ) / ellT (sz.L n) (sz.lam n) (p.1 : ℝ)) ^ (1 / 2 : ℝ)) := by
      positivity
    simp only [Real.rpow_zero, one_mul]
    nlinarith
  · have h1 : 0 < 1 - (p.1 : ℝ) := by linarith [ht1 n, p.1.2.2]
    have hu : (1 : ℝ) ≤ (1 - s n) / (1 - (p.1 : ℝ)) := by
      rw [le_div_iff₀ h1]; linarith [p.1.2.1]
    have hbase : 0 ≤ (1 - s n) / (1 - (p.1 : ℝ)) := by linarith
    have hB : 0 ≤ (sz.Bctl n (p.1 : ℝ)) ^ (1 / 5 : ℝ) :=
      Real.rpow_nonneg (STBctl_pos sz n (by linarith [ht1 n, p.1.2.2])).le _
    have hW : 0 ≤ STWB sz n (p.1 : ℝ) (zdistInf d (sz.L n) (p.2.2 0 - p.2.2 1)) := by
      unfold STWB Bparam; positivity
    have hr0 : 0 ≤ ((1 - s n) / (1 - (p.1 : ℝ))) ^ Cd := Real.rpow_nonneg hbase _
    have hW0 : 0 ≤ ((sz.W n : ℕ) : ℝ) ^ (-D) := Real.rpow_nonneg (Nat.cast_nonneg _) _
    have hE0 := (Real.exp_pos (-(((zdistInf d (sz.L n) (p.2.2 0 - p.2.2 1) : ℕ) : ℝ) /
      ellT (sz.L n) (sz.lam n) (p.1 : ℝ)) ^ (1 / 2 : ℝ))).le
    exact add_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hr0 hB) hW) hE0) hW0

/-- The pin of a regime `R'` follows from the pin of a larger regime `R` (`STAny` is the largest). -/
theorem ST_step6R_mono {R R' : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop}
    (hRR : ∀ (sz : Sizes d) (s t : ℕ → ℝ), R' sz s t → R sz s t) (h : STStep6R d R) : STStep6R d R' := by
  intro hd κ ε 𝔡 hκ hε h𝔡
  obtain ⟨c, hc, hc', H⟩ := h hd κ ε 𝔡 hκ hε h𝔡
  exact ⟨c, hc, hc', fun 𝔠 sz z hflow s t hs0 hst htT hR' => H 𝔠 sz z hflow s t hs0 hst htT (hRR sz s t hR')⟩

end RBM.Gauss.Sizes

namespace RBM.Gauss.Step6Inst

open RBM RBM.Gauss RBM.Gauss.Sizes RBM.Gauss.SizesInst RBM.Gauss.InductionDefsInst RBM.Gauss.Step34Inst
  RBM.Gauss.Step5Inst RBM.Path Filter

/-! ### The ingredient pins, one instance per regime of their window -/

theorem inst_hiI : STDriftHi szB (fun _ => 7 / 8) (fun _ => 15 / 16) := st6_hi_of_reg5I szB (by norm_num) szB_reg5I
theorem inst_hiII : STDriftHi szB (fun _ => 15 / 16) (fun _ => 31 / 32) := st6_hi_of_reg5II szB szB_reg5II
theorem inst_hiIII : STDriftHi sz0 sInst tInst := st6_hi_of_reg5III sz0 sz0_reg5III

/-- `(eq:Exp(L-K)1)` at the data of regimes (i), (ii), (iii). -/
theorem inst_expLKLK_I (h : STExpLKLKHi 3) :
    InstIng6Concl (fun sz E s t => STExpLKLKHiConcl sz E s t) szB zB (fun _ => 7 / 8) (fun _ => 15 / 16) :=
  inst_ing6_I STDriftHi _ h inst_hiI
theorem inst_expLKLK_II (h : STExpLKLKHi 3) :
    InstIng6Concl (fun sz E s t => STExpLKLKHiConcl sz E s t) szB zB (fun _ => 15 / 16) (fun _ => 31 / 32) :=
  inst_ing6_II STDriftHi _ h inst_hiII
theorem inst_expLKLK_III (h : STExpLKLKHi 3) :
    InstIng6Concl (fun sz E s t => STExpLKLKHiConcl sz E s t) sz0 z0 sInst tInst :=
  inst_ing6_III STDriftHi _ h inst_hiIII

/-! ### The skeletons applied at the data of their regimes -/

theorem inst_skeleton6I (hLK : STExpLKLKHi 3) (hLW : LWtermEXP 3) (hAvg : STImproveExpAver 3) (hDu : STExpDuhamelZ 3)
    (hDuQ : STExpDuhamelQ 3) (hDec : STExpDriftDecay 3) (hWd : STExpWardI 3) (hIni : STExpIniI 3)
    (hInt : STExpIntI 3) :
    InstIng6Concl (fun sz E s t => STStep6Concl sz E s t) szB zB (fun _ => 7 / 8) (fun _ => 15 / 16) :=
  inst_step6I (ST_step6_caseI_of_pins hLK hLW hAvg hDu hDuQ hDec hWd hIni hInt)

theorem inst_skeleton6II (hLK : STExpLKLKHi 3) (hLW : LWtermEXP 3) (hAvg : STImproveExpAver 3) (hDu : STExpDuhamelZ 3)
    (hInt : STExpIntII 3) (hWd : STExpWardII 3) :
    InstIng6Concl (fun sz E s t => STStep6Concl sz E s t) szB zB (fun _ => 15 / 16) (fun _ => 31 / 32) :=
  inst_step6II (ST_step6_caseII_of_pins hLK hLW hAvg hDu hInt hWd)

theorem inst_skeleton6III (hLK : STExpLKLKHi 3) (hLW : LWtermEXP 3) (hDu : STExpDuhamelZ 3) (hInt : STExpIntIII 3)
    :
    InstIng6Concl (fun sz E s t => STStep6Concl sz E s t) sz0 z0 sInst tInst :=
  inst_step6III (ST_step6_caseIII_of_pins hLK hLW hDu hInt)

theorem inst_skeleton6IV (hAvg : STImproveExpAver 3) (hDu : STExpDuhamelZ 3) (hLo : STExpDriftLo 3)
    (hInt : STExpIntIV 3) :
    InstIng6Concl (fun sz E s t => STStep6Concl sz E s t) szG zB (fun _ => 5 / 8) (fun _ => 3 / 4) :=
  inst_step6IV (ST_step6_caseIV_of_pins hAvg hDu hLo hInt)

end RBM.Gauss.Step6Inst

namespace RBM.Gauss.Step6Inst

open RBM RBM.Gauss RBM.Gauss.Sizes RBM.Gauss.SizesInst RBM.Gauss.InductionDefsInst RBM.Gauss.Step34Inst
  RBM.Gauss.Step5Inst RBM.Path Filter

/-- **(g) at concrete data**: the family `F = 1 - u`, `G = 2 (1 - u)` on `[0, 1/2]` (nonzero, `F ≤ G`), index set `Bool`: for every time
sequence in `[0,1/2]` the deterministic `Prec` holds, hence it holds uniformly in `u ∈ [0,1/2]`. -/
theorem inst_precU :
    sz0.Prec (U := fun n => TimeIcc (fun _ => (0 : ℝ)) (fun _ => (1 / 2 : ℝ)) n × Bool)
      (fun _ p _ => 1 - (p.1 : ℝ)) (fun _ p _ => 2 * (1 - (p.1 : ℝ))) :=
  st6_precU_of_forall_seq sz0 sz0_tendsto (fun n => by norm_num) (W := fun _ => Bool)
    (fun _ u _ => 1 - u) (fun _ u _ => 2 * (1 - u))
    (fun u hsu hut => prec_of_le sz0 (fun n w ω => by have h : u n ≤ 1 / 2 := hut n; change 0 ≤ 2 * (1 - u n); linarith)
      (fun n w ω => by have h : u n ≤ 1 / 2 := hut n; change 1 - u n ≤ 2 * (1 - u n); linarith))

/-- `(Eq:Gdecay_flow)` without loss implies the lossy form of `(Eq:Gdecay_w)` (`C_d = 1`) at the data `(sz0, 0, 1/16)`. -/
theorem inst_GdecayW_of_zero (h : STGdecayW sz0 (STflowE z0) sInst tInst 0) : STGdecayW sz0 (STflowE z0) sInst tInst 1 :=
  st6_GdecayW_of_zero sz0 sz0_tendsto (fun n => by simp only [tInst]; norm_num) zero_le_one h

/-- **(F1) at the data of regime (ii)** (`szB`, `15/16 < 31/32`): the window of `lem:sum_decay` fails (`ilambda²/L² = 1/16 > 1/32 = 1-t`). -/
theorem inst_F1 : ¬ STCaseI szB (fun _ => 15 / 16) (fun _ => 31 / 32) := fun h => by
  have := st6_F1_window_vs_reg5II szB h szB_reg5II 0
  norm_num at this

/-- `ST_step6R_mono`: the general pin gives the regime (i) pin at the data of regime (i). -/
theorem inst_step6R_mono (h : STStep6 3) :
    InstIng6Concl (fun sz E s t => STStep6Concl sz E s t) szB zB (fun _ => 7 / 8) (fun _ => 15 / 16) :=
  inst_step6I (ST_step6R_mono (fun _ _ _ _ => trivial) h)

/-- **The bridges at a section `u ≡ 1/32 ∈ [0, 1/16]`** (the five premises of `LWtermEXP`): the uniform statements stay hypotheses. -/
theorem inst_bridges (hLE : STLocalEntryU sz0 (STflowE z0) sInst tInst) (hAvg : STAvgU sz0 (STflowE z0) sInst tInst)
    (hLmax : STLmaxU sz0 (STflowE z0) sInst tInst) (hLK : STLKU sz0 (STflowE z0) sInst tInst)
    (hDec : STGdecayW sz0 (STflowE z0) sInst tInst 0) :
    STLocalEntry sz0 (STflowE z0) (fun _ => 1 / 32) ∧ LWAvgLaw sz0 (STflowE z0) (fun _ => 1 / 32) ∧
      STLmax sz0 (STflowE z0) (fun _ => 1 / 32) ∧ STLK sz0 (STflowE z0) (fun _ => 1 / 32) ∧
      STDecay sz0 (STflowE z0) (fun _ => 1 / 32) :=
  ⟨STLocalEntry_of_STLocalEntryU_at sz0 (fun n => by simp only [sInst]; norm_num)
      (fun n => by simp only [tInst]; norm_num) hLE,
    LWAvgLaw_of_STAvgU_at sz0 (fun n => by simp only [sInst]; norm_num)
      (fun n => by simp only [tInst]; norm_num) hAvg,
    STLmax_of_STLmaxU_at sz0 (fun n => by simp only [sInst]; norm_num)
      (fun n => by simp only [tInst]; norm_num) hLmax,
    STLK_of_STLKU_at sz0 (fun n => by simp only [sInst]; norm_num)
      (fun n => by simp only [tInst]; norm_num) hLK,
    STDecay_of_STGdecayW_at sz0 (fun n => by simp only [sInst]; norm_num)
      (fun n => by simp only [tInst]; norm_num) hDec⟩

/-- The endpoints `u = t`: `STExp2U ⇒ STExp2`, `STLocalEntryU ⇒ STLocalEntry` at `(sz0, 0, 1/16)`. -/
theorem inst_endpoints (h : STExp2U sz0 (STflowE z0) sInst tInst) (hLE : STLocalEntryU sz0 (STflowE z0) sInst tInst) :
    STExp2 sz0 (STflowE z0) tInst ∧ STLocalEntry sz0 (STflowE z0) tInst :=
  ⟨STExp2_of_STExp2U sz0 (fun n => (sz0_hst n).le) h, STLocalEntry_of_STLocalEntryU sz0 (fun n => (sz0_hst n).le) hLE⟩

/-- **`(res_ELK_n=1)` uniformly from `STImproveExpAver`, `STAvgU` (in `STStep2Concl`) and `STLKU`** at `(sz0, z0, 0, 1/16)`. -/
theorem inst_expAvgU (hAvg : STImproveExpAver 3) (hS2 : STStep2Core sz0 (STflowE z0) sInst tInst)
    (hLKU : STLKU sz0 (STflowE z0) sInst tInst) : STExpAvgU sz0 (STflowE z0) sInst tInst :=
  st6_expAvgU_of_pin sz0 hAvg (by norm_num) (by norm_num : (0 : ℝ) < 1 / 10) (by norm_num : (0 : ℝ) < 1 / 10)
    (by norm_num : (0 : ℝ) < 1 / 10) flow_z0 sz0_hs0 sz0_hst sz0_ht hS2 hLKU

/-- **`(eq:ExpLWn=2)` uniformly from `LWtermEXP`** at `(sz0, z0, 0, 1/16)`: the window `STDriftHi` holds (`inst_hiIII`), the premises are the uniform
conclusions of Steps 2-5. -/
theorem inst_EGtHi (hLW : LWtermEXP 3) (hS2 : STStep2Core sz0 (STflowE z0) sInst tInst)
    (hLmax : STLmaxU sz0 (STflowE z0) sInst tInst) (hLK : STLKU sz0 (STflowE z0) sInst tInst)
    (hS5 : STGdecayW sz0 (STflowE z0) sInst tInst 0) : STExpEGtHiConcl sz0 (STflowE z0) sInst tInst :=
  st6_EGtHi_of_LW sz0 hLW (by norm_num) (by norm_num : (0 : ℝ) < 1 / 10) (by norm_num : (0 : ℝ) < 1 / 10)
    (by norm_num : (0 : ℝ) < 1 / 10) flow_z0 sz0_hs0 sz0_hst sz0_ht inst_hiIII hS2 hLmax hLK hS5

/-- The Duhamel identity along `[0, 1/16]` from the pin. -/
theorem inst_duhEq (hDu : STExpDuhamelZ 3) : STExpDuhEq sz0 (STflowE z0) sInst tInst :=
  st6_duhEq_of_pin sz0 hDu (by norm_num) (by norm_num : (0 : ℝ) < 1 / 10) flow_z0 sz0_hs0 sz0_ht

theorem inst_G_pos_sz0 (n : ℕ) : 0 < (sz0.lam n ^ 2 * ((sz0.W n : ℕ) : ℝ) ^ 3) ^ (-(1 / 5 : ℝ)) :=
  st6_G_pos sz0 (by
    change ((2 * ((n : ℝ) + 1)) ^ 6)⁻¹ ≠ 0
    positivity)

theorem inst_G_pos_szB (n : ℕ) : 0 < (szB.lam n ^ 2 * ((szB.W n : ℕ) : ℝ) ^ 3) ^ (-(1 / 5 : ℝ)) :=
  st6_G_pos szB (by simp [szB])

theorem inst_G_pos_szG (n : ℕ) : 0 < (szG.lam n ^ 2 * ((szG.W n : ℕ) : ℝ) ^ 3) ^ (-(1 / 5 : ℝ)) :=
  st6_G_pos szG (by simp [szG, szB])

/-- The target `T_u > 0` at the four data. -/
theorem st6_target_pos {d : ℕ} (sz : Sizes d) {n : ℕ} (hl : sz.lam n ≠ 0) {u : ℝ} (hu : u < 1) :
    0 < STExpTarget sz n u := by
  unfold STExpTarget
  have hB := STBctl_pos sz n hu
  have hG := st6_G_pos sz hl
  positivity

theorem inst_target_pos_sz0 : 0 < STExpTarget sz0 0 (1 / 16) :=
  st6_target_pos sz0 (by simp [sz0]) (by norm_num)

theorem inst_target_pos_szB (n : ℕ) : 0 < STExpTarget szB n (15 / 16) :=
  st6_target_pos szB (by simp [szB]) (by norm_num)

theorem inst_target_pos_szG (n : ℕ) : 0 < STExpTarget szG n (3 / 4) :=
  st6_target_pos szG (by simp [szG, szB]) (by norm_num)

/-- `(eq:WO)` gives `0 < ilambda_n` eventually (here `sz0`: `ilambda_n = (2(n+1))^{-6} > 0`). -/
theorem inst_lam_pos : ∀ᶠ n in atTop, 0 < sz0.lam n := st6_lam_pos sz0 sz0_admissible.2.2.2.2

/-- The defect scenario at `lam = 0`: the target of `STExp2` falls to `(W^{-d}B)^3` (Mathlib has `0 ^ (-1/5) = 0`); `(eq:WO)` excludes it. -/
theorem inst_target_lam_zero (n : ℕ) (u : ℝ) :
    STExpTarget (sz0.withLam fun _ => 0) n u = ((sz0.withLam fun _ => 0).Bctl n u) ^ 3 :=
  st6_target_lam_zero (sz0.withLam fun _ => 0) rfl u

/-- **The initial-term comparison in regime (iii)** at `(sz0, n = 0)`, `s = 0`, at the boundary `1-u = ilambda² = 1/4096` (`x/(ilambda²+x) = 1/2`
exactly): `(1-s)B_s ≤ 2(1-u)B_u` and `((1-s)/(1-u))² T_s ≤ 4 T_u`, both sides nonzero. -/
theorem inst_cmp_III :
    (1 - (0 : ℝ)) * sz0.Bctl 0 0 ≤ 2 * ((1 - 4095 / 4096 : ℝ) * sz0.Bctl 0 (4095 / 4096)) ∧
    ((1 - (0 : ℝ)) / (1 - 4095 / 4096)) ^ 2 * STExpTarget sz0 0 0 ≤ 4 * STExpTarget sz0 0 (4095 / 4096) := by
  have hg : sz0.lam 0 ^ 2 ≤ 1 - (4095 / 4096 : ℝ) := by
    have : sz0.lam 0 = 1 / 64 := by norm_num [sz0]
    rw [this]; norm_num
  have h := st6_xB_III sz0 0 (s := 0) (u := 4095 / 4096) (by norm_num) (by norm_num) hg
  exact ⟨h, st6_cmp_ini sz0 0 (s := 0) (u := 4095 / 4096) (by norm_num) (by norm_num) h⟩

/-- **The initial-term comparison in regime (iv)** at `(szG, n = 0)`, `1-s = ilambda²/L^3 = 25/64` (the boundary), `u = 3/4`. -/
theorem inst_cmp_IV :
    (1 - (39 / 64 : ℝ)) * szG.Bctl 0 (39 / 64) ≤ 2 * ((1 - 3 / 4 : ℝ) * szG.Bctl 0 (3 / 4)) ∧
    ((1 - (39 / 64 : ℝ)) / (1 - 3 / 4)) ^ 2 * STExpTarget szG 0 (39 / 64) ≤ 4 * STExpTarget szG 0 (3 / 4) := by
  have hg : 1 - (39 / 64 : ℝ) ≤ szG.lam 0 ^ 2 / ((szG.L 0 : ℕ) : ℝ) ^ 3 := by
    have h1 : szG.lam 0 = 5 := by simp [szG, szB]
    have h2 : ((szG.L 0 : ℕ) : ℝ) = 4 := by simp [szG, szB]
    rw [h1, h2]; norm_num
  have h := st6_xB_IV szG 0 (s := 39 / 64) (u := 3 / 4) (by norm_num) (by norm_num) hg
  exact ⟨h, st6_cmp_ini szG 0 (s := 39 / 64) (u := 3 / 4) (by norm_num) (by norm_num) h⟩

/-- **The initial term of regimes (iii), (iv)** at `(sz0, z0, 0, 1/16)`: `(sum_res_Ndecay)` applied to the deterministic tensor `f_s`;
the premise `(Eq:Gtlp_exp+IND)` (`STExp2` at `s`) stays a hypothesis. -/
theorem inst_ini_sumNdecay (hExp : STExp2 sz0 (STflowE z0) sInst) :
    sz0.Prec (U := fun n => TimeIcc sInst tInst n × (Fin 2 → Bool) × (Fin 2 → Zd 3 (sz0.L n)))
      (fun n p _ => ‖RBM.Ind.Ugen 3 (sz0.L n) (sz0.lam n) (STflowE z0 n) p.2.1 (sInst n) (p.1 : ℝ)
        (fun b => sz0.STExpErr n (STflowE z0 n) (sInst n) p.2.1 b) p.2.2‖)
      (fun n p _ => ((1 - sInst n) / (1 - (p.1 : ℝ))) ^ 2 * STExpTarget sz0 n (sInst n)) :=
  st6_ini_sumNdecay sz0 (by norm_num) (by norm_num : (0 : ℝ) < 1 / 10) flow_z0 sz0_hs0 sz0_hst sz0_ht hExp

/-- **The initial term of regime (ii)** at `(szB, zB, 15/16, 31/32)`, `A = {1,2}`, the sign class `σ₁ ≠ σ₂`: the boundary `1 - s = ilambda²/L²`
of `(sum_res_Ndecay_nonzero)` is hit (`1/16 = 1/16`); `(Eq:Gtlp_exp+IND)` stays a hypothesis. -/
theorem inst_ini_nonzero (hExp : STExp2 szB (STflowE zB) (fun _ => 15 / 16)) :
    szB.Prec (U := STIdx2P szB STSigMixed (fun _ => 15 / 16) (fun _ => 31 / 32))
      (fun n p _ => ‖zeroModeSet 3 (szB.L n) (Finset.univ : Finset (Fin 2))
        (RBM.Ind.Ugen 3 (szB.L n) (szB.lam n) (STflowE zB n) p.2.1.1 (15 / 16) (p.1 : ℝ)
          (fun b => szB.STExpErr n (STflowE zB n) (15 / 16) p.2.1.1 b)) p.2.2‖)
      (fun n _ _ => STExpTarget szB n (15 / 16)) :=
  st6_ini_nonzero szB (by norm_num) (by norm_num : (0 : ℝ) < 1 / 10) flow_zB (fun _ => by norm_num)
    (fun _ => by norm_num) (szB_flow_ht (by norm_num)) (fun n => by simp [szB]; norm_num) hExp Finset.univ STSigMixed
    (fun σ _ i _ => Finset.mem_univ i)

/-- **A mollifier family** (`Def:QtPt`) for `szB` (`ilambda = 1 ≤ 𝔡⁻¹ = 10`): constants `C, c > 0` and `ϑ_n` with `STMollifierProps` eventually. -/
theorem inst_mollifier_family :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∃ ϑ : ∀ n : ℕ, ℝ → (Fin 2 → Zd 3 (szB.L n)) → ℂ,
      ∀ᶠ n in atTop, STMollifierProps (d := 3) (szB.lam n) C c (ϑ n) :=
  st6_mollifier_family szB (by norm_num) (by norm_num : (0 : ℝ) < 1 / 10) szB_WO

end RBM.Gauss.Step6Inst
