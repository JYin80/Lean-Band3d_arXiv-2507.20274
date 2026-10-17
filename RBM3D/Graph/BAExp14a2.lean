/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Graph.BAExp14e
import RBM3D.Graph.BAExp14bB
import RBM3D.BA.TwistAvgB

/-!
# BA-L L4a2 (T2490): `lem:LWterm_EXP` at BA, the reduction `LWE → LWcut` and the assembly of S1-S3

Paper: arXiv:2507.20274, `paper/tex/6_Step6_two_loop.tex:83-88` (`lem:LWterm_EXP`),
`paper/tex/7_8_light_weight.tex:10` (`(eq:EGC)`), `paper/tex/B_graphical_lemmas.tex:7-15`
(`(eq:ELW_term)`; both charges `σ`), `B:118` ("analogous ... omit"; route R1, paper delta
T2398d).  Twin of the band files `Graph/LWExpTerm.lean` §1, §3, §4, §13
(`:47-64, 204-328, 1212-1231`) and `Graph/LWExpTerm2.lean` §15 target 7 (`:1953-2023`);
probe `t/T2398:RBM3D/Probe/T2398Pins.lean:411-471`.

## Contents (namespace `RBM.BA`; private helpers carry the stem `BAExp14a2_`)

1. The pins (target 1): `LWCutExpG` (the cut pin over a carrier, five premises), the band
   bridge `LWCutExp_iff`, `band_LWCutExpG`; `BALWCutExpTw` (the BA cut pin under R1, seven
   premises); `BALWtermEXPTw` (the seven-premise successor of `BALWtermEXP`); the statement defs
   `BALWtermEXPTwOfCut`, `BALWCutExpTwOfS2`, `BALWtermEXPTwOfS2`.
2. Bounded continuous random variables and the integrability of `LWcutg` (`BAExp14a2_BM_cutg`,
   from the public `BAExp14a_cont_G`, `BAExp14a_G_le`, `BAExp14a_integrable`).
3. The reduction `baLWtermEXPTw_of_cut` (target 2): `LWEg = LWcutg + LWcutg`, `integral_add`, the
   triangle inequality, `2 ≤ N^{τ/2}`.
4. The assembly `baLWCutExpTw_of_S2` (target 3): `baExp14b_expand_holds` writes `𝔼 LWcutg` as
   6 + 8 + 4 family expectations, each `≺` the same control (`baExp14a_S1_holds`, the
   antecedent `BAExp14bS2`, `baExp14bS3_holds`), `18 ≤ N^{τ/2}`.
5. The composition `baLWtermEXPTw_of_S2` (target 4).
6. Compiled nonempty instances (target 6).

S2 (`BAExp14bS2`, owner L4b2 = T2489) is not proved here: it enters only as the antecedent
inside the statement defs; no public result has a pin binder.  The closures
`baLWCutExpTw_holds`, `baLWtermEXPTw_holds` (target 5) are owed to the last terminal ticket
(T2489 not merged at the start of this row).
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedFintypeInType false
set_option linter.style.setOption false

open MeasureTheory Filter

noncomputable section

namespace RBM.BA
open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes RBM.Graph

/-! ## 1. The pins (target 1) -/

/-- `LWCutExp` (`LWExpTerm.lean:52`, `(eq:ELW_term)` at the loop level) over a carrier family: `‖𝔼 LWcut‖ ≺ (1-t)⁻¹ (W^{-d}B_{t,0})^{5/2}` on
`ĝ²/L^d ≤ 1 - t`.  The premises are the generic Step 1/2 pins (`Chain/Carrier`), as `LWtermEXPG` (`Chain/LWGen.lean:108`). -/
def LWCutExpG (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ)
    (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop)
    (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz) (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), Flow sz κ ε 𝔠 𝔡 z →
      ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ T0 sz z n) →
        STLocalEntrygL (mk sz z) (law sz) t → LWAvgLawgL (mk sz z) (law sz) t → STLmaxgL (mk sz z) (law sz) t →
        STLKgL (mk sz z) (law sz) t → STDecaygL (mk sz z) (law sz) t →
        PrecL sz (law sz) (U := fun n => {_p : (Bool × Bool) × (Zd d (sz.L n) × Zd d (sz.L n)) //
            sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ d ≤ 1 - t n})
          (fun n p _ => ‖∫ ω, LWcutg (mk sz z) n (t n) p.1.1.1 p.1.1.2 p.1.2.1 p.1.2.2 ω ∂(law sz)‖)
          (fun n _ _ => (1 - t n)⁻¹ * (sz.Bctl n (t n)) ^ (5 / 2 : ℝ))

/-- **The BA cut pin under R1** (D3, the assembly of L4a2): the five premises of `LWCutExpG` at the block Anderson data (law
`seqP (sz.withLam 0)`, setting `BAFlow`, carrier `baFMz`, horizon `BAflowT0`) and the twisted laws TL1 (`BATwistAvgLaw`), TL2
(`BATwistLoopLaw`) as premises 6-7 (owed pins of the TL stage); the conclusion of `LWCutExpG`. -/
def BALWCutExpTw (d : ℕ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z →
    ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ BAflowT0 sz z n) → let μ := Sizes.seqP (sz.withLam 0)
      STLocalEntrygL (baFMz sz z) μ t → LWAvgLawgL (baFMz sz z) μ t → STLmaxgL (baFMz sz z) μ t → STLKgL (baFMz sz z) μ t →
      STDecaygL (baFMz sz z) μ t → BATwistAvgLaw (baFMz sz z) μ t → BATwistLoopLaw (baFMz sz z) μ t →
      PrecL sz μ (U := fun n => {_p : (Bool × Bool) × (Zd d (sz.L n) × Zd d (sz.L n)) // sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ d ≤ 1 - t n})
        (fun n p _ => ‖∫ ω, LWcutg (baFMz sz z) n (t n) p.1.1.1 p.1.1.2 p.1.2.1 p.1.2.2 ω ∂μ‖) (fun n _ _ => (1 - t n)⁻¹ * (sz.Bctl n (t n)) ^ (5 / 2 : ℝ))

/-- **The seven-premise successor of `BALWtermEXP`** (`BA/LWPinsBA.lean:49`, `baPin LWtermEXPG`, five premises): `LWtermEXPG` (`Chain/LWGen.lean:108`)
written out at the BA data, with TL1, TL2 in the slots they have in `BALWCutExpTw`.  The merged `BALWtermEXP` is not changed. -/
def BALWtermEXPTw (d : ℕ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z →
    ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ BAflowT0 sz z n) → let μ := Sizes.seqP (sz.withLam 0)
      STLocalEntrygL (baFMz sz z) μ t → LWAvgLawgL (baFMz sz z) μ t → STLmaxgL (baFMz sz z) μ t → STLKgL (baFMz sz z) μ t →
      STDecaygL (baFMz sz z) μ t → BATwistAvgLaw (baFMz sz z) μ t → BATwistLoopLaw (baFMz sz z) μ t →
      PrecL sz μ (U := fun n => {_p : (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)) // sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ d ≤ 1 - t n})
        (fun n p _ => ‖∫ ω, LWEg (baFMz sz z) n (t n) p.1.1 p.1.2 ω ∂μ‖) (fun n _ _ => (1 - t n)⁻¹ * (sz.Bctl n (t n)) ^ (5 / 2 : ℝ))

/-- The reduction `LWE → LWcut` at the BA data (pattern `BALWMomentOfAnp`, `BAMomentGenB:362`: the antecedent sits inside the def, so no public
result has a pin binder). -/
def BALWtermEXPTwOfCut (d : ℕ) : Prop := BALWCutExpTw d → BALWtermEXPTw d

/-- The assembly with S2 as the exact-type antecedent (pattern `BAExp14bS3OfLeaf`, `BAExp14c:915`). -/
def BALWCutExpTwOfS2 (d : ℕ) : Prop := BAExp14bS2 d → BALWCutExpTw d

/-- The composition of the reduction and the assembly, read at the terminal. -/
def BALWtermEXPTwOfS2 (d : ℕ) : Prop := BAExp14bS2 d → BALWtermEXPTw d

/-! ## 2. Bounded continuous random variables; the integrability of `LWcutg` -/

section BM

variable {d : ℕ} {sz : Sizes d} {z : ℕ → ℂ} {κ ε 𝔠 𝔡 : ℝ}

/-- A bounded continuous random variable on the common sample space (a copy of the private `BAExp14b_BM`, `BAExp14bB.lean:389`). -/
private def BAExp14a2_BM (f : sz.SeqΩ → ℂ) : Prop := Continuous f ∧ ∃ C : ℝ, ∀ ω, ‖f ω‖ ≤ C

private theorem BAExp14a2_BM.const (c : ℂ) : BAExp14a2_BM (sz := sz) (fun _ => c) :=
  ⟨continuous_const, ‖c‖, fun _ => le_rfl⟩

private theorem BAExp14a2_BM.add {f g : sz.SeqΩ → ℂ} (hf : BAExp14a2_BM f) (hg : BAExp14a2_BM g) :
    BAExp14a2_BM (fun ω => f ω + g ω) := by
  obtain ⟨cf, Cf, hCf⟩ := hf
  obtain ⟨cg, Cg, hCg⟩ := hg
  exact ⟨cf.add cg, Cf + Cg, fun ω => (norm_add_le _ _).trans (add_le_add (hCf ω) (hCg ω))⟩

private theorem BAExp14a2_BM.neg {f : sz.SeqΩ → ℂ} (hf : BAExp14a2_BM f) : BAExp14a2_BM (fun ω => -f ω) := by
  obtain ⟨cf, Cf, hCf⟩ := hf
  exact ⟨cf.neg, Cf, fun ω => by rw [norm_neg]; exact hCf ω⟩

private theorem BAExp14a2_BM.sub {f g : sz.SeqΩ → ℂ} (hf : BAExp14a2_BM f) (hg : BAExp14a2_BM g) :
    BAExp14a2_BM (fun ω => f ω - g ω) := by
  simp only [sub_eq_add_neg]
  exact hf.add hg.neg

private theorem BAExp14a2_BM.mul {f g : sz.SeqΩ → ℂ} (hf : BAExp14a2_BM f) (hg : BAExp14a2_BM g) :
    BAExp14a2_BM (fun ω => f ω * g ω) := by
  obtain ⟨cf, Cf, hCf⟩ := hf
  obtain ⟨cg, Cg, hCg⟩ := hg
  refine ⟨cf.mul cg, Cf * Cg, fun ω => ?_⟩
  rw [norm_mul]
  exact mul_le_mul (hCf ω) (hCg ω) (norm_nonneg _) ((norm_nonneg _).trans (hCf ω))

private theorem BAExp14a2_BM.star {f : sz.SeqΩ → ℂ} (hf : BAExp14a2_BM f) : BAExp14a2_BM (fun ω => star (f ω)) := by
  obtain ⟨cf, Cf, hCf⟩ := hf
  exact ⟨cf.star, Cf, fun ω => by rw [norm_star]; exact hCf ω⟩

private theorem BAExp14a2_BM.sum {ι : Type*} (s : Finset ι) {f : ι → sz.SeqΩ → ℂ} (h : ∀ i ∈ s, BAExp14a2_BM (f i)) :
    BAExp14a2_BM (fun ω => ∑ i ∈ s, f i ω) := by
  choose! C hC using fun i hi => (h i hi).2
  refine ⟨continuous_finsetSum _ fun i hi => (h i hi).1, ∑ i ∈ s, C i, fun ω => ?_⟩
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun i hi => hC i hi ω)

section Atoms

variable (hκ : 0 < κ) (hflow : BAFlow sz κ ε 𝔠 𝔡 z) (n : ℕ) {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ BAflowT0 sz z n)
include hκ hflow ht0 ht

private theorem BAExp14a2_BM_G (x y : Idx d (sz.L n) (sz.W n)) :
    BAExp14a2_BM (fun ω : sz.SeqΩ => (baFMz sz z).G n t ω x y) :=
  ⟨BAExp14a_cont_G hκ hflow n ht0 ht x y, _, fun ω => BAExp14a_G_le hκ hflow n ht0 ht ω x y⟩

private theorem BAExp14a2_BM_GM (a b : Idx d (sz.L n) (sz.W n)) :
    BAExp14a2_BM (fun ω : sz.SeqΩ => (baFMz sz z).GM n t ω a b) := by
  unfold FlowFM.GM
  exact (BAExp14a2_BM_G hκ hflow n ht0 ht a b).sub (BAExp14a2_BM.const _)

private theorem BAExp14a2_BM_X (c : Zd d (sz.L n)) :
    BAExp14a2_BM (fun ω : sz.SeqΩ => BAExp14a_X sz z n t ω c) := by
  unfold BAExp14a_X
  exact (BAExp14a2_BM.const _).mul (BAExp14a2_BM.sum _ fun v _ => BAExp14a2_BM_GM hκ hflow n ht0 ht v v)

private theorem BAExp14a2_BM_tail (σ : Bool) (x y : Idx d (sz.L n) (sz.W n)) :
    BAExp14a2_BM (fun ω : sz.SeqΩ => BAExp14a_tail sz z n t ω σ x y) := by
  cases σ
  · simp only [BAExp14a_tail, Bool.false_eq_true, ↓reduceIte]
    exact (BAExp14a2_BM_G hκ hflow n ht0 ht x y).star
  · simp only [BAExp14a_tail, ↓reduceIte]
    exact BAExp14a2_BM_G hκ hflow n ht0 ht y x

/-- `LWcutg` is a bounded continuous random variable: for `σc = +` the fine sum `BAExp14b_cut_true` of products of `G`, `X` and the closing
edge; for `σc = -` the conjugate `baExp14b_cut_conj` of the blue cut at the swapped blocks. -/
private theorem BAExp14a2_BM_cutg (σc σo : Bool) (ac ao : Zd d (sz.L n)) :
    BAExp14a2_BM (fun ω : sz.SeqΩ => LWcutg (baFMz sz z) n t σc σo ac ao ω) := by
  have hblue : ∀ (σo : Bool) (ac ao : Zd d (sz.L n)),
      BAExp14a2_BM (fun ω : sz.SeqΩ => LWcutg (baFMz sz z) n t true σo ac ao ω) := by
    intro σo ac ao
    have hSelf := (BAflow_real κ ε 𝔠 𝔡 sz z hflow n).1
    have e : (fun ω : sz.SeqΩ => LWcutg (baFMz sz z) n t true σo ac ao ω) = fun ω =>
        BAExp14b_fr sz n ao ac (fun x y α => BAExp14a_tail sz z n t ω σo x y * (BAExp14a_X sz z n t ω (STblk sz n α) *
          ((baFMz sz z).G n t ω x α * (baFMz sz z).G n t ω α y))) :=
      funext fun ω => BAExp14b_cut_true n t hSelf σo ac ao ω
    rw [e]
    unfold BAExp14b_fr
    exact (BAExp14a2_BM.const _).mul (BAExp14a2_BM.sum _ fun x _ => BAExp14a2_BM.sum _ fun y _ =>
      BAExp14a2_BM.sum _ fun α _ => (BAExp14a2_BM_tail hκ hflow n ht0 ht σo x y).mul
        ((BAExp14a2_BM_X hκ hflow n ht0 ht _).mul
          ((BAExp14a2_BM_G hκ hflow n ht0 ht x α).mul (BAExp14a2_BM_G hκ hflow n ht0 ht α y))))
  cases σc
  · have e : (fun ω : sz.SeqΩ => LWcutg (baFMz sz z) n t false σo ac ao ω) =
        fun ω => star (LWcutg (baFMz sz z) n t true (!σo) ao ac ω) :=
      funext fun ω => baExp14b_cut_conj sz z n t σo ac ao ω
    rw [e]
    exact (hblue _ _ _).star
  · exact hblue _ _ _

end Atoms

end BM

/-! ## 3. Target 2: the reduction `LWE → LWcut` (`(eq:ELW_term)`, `B:10-13`) -/

/-- **`baLWtermEXPTw_of_cut`** (target 2; twin of `lwTermEXP_of_cut`, `LWExpTerm.lean:286`): `LWEg = LWcutg(σ₁,σ₀,a₁,a₀) + LWcutg(σ₀,σ₁,a₀,a₁)`
(`Chain/LWGen.lean:44`, `rfl`); `integral_add` (both cuts are bounded continuous at `seqP (sz.withLam 0)`: `BAExp14a2_BM_cutg`), the triangle
inequality and `2 ≤ N^{τ/2}`; the index `((σ, a), _)` is sent to the two cut indices `((σ 1, σ 0), (a 1, a 0))` and `((σ 0, σ 1), (a 0, a 1))`,
on the same index set `ĝ²/L^d ≤ 1 - t`.  The TL premises are carried unchanged. -/
theorem baLWtermEXPTw_of_cut : ∀ d : ℕ, BALWtermEXPTwOfCut d := by
  intro d hcut hd κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow t ht0 htT μ hE hA hM hK hD hT1 hT2
  have h := hcut hd κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow t ht0 htT hE hA hM hK hD hT1 hT2
  have hsz : Tendsto sz.size atTop atTop := Sizes.tendsto_size sz hflow.1.2.2.1
  have ht1 : ∀ n, t n < 1 := fun n => (ba_G_data hκ sz hflow n (ht0 n) (htT n)).1
  have h' := (BAExp14a_det_iff (P := BAExp14a_μ sz) hsz _ _).1 h
  refine (BAExp14a_det_iff (P := BAExp14a_μ sz) hsz _ _).2 ?_
  intro τ hτ
  have hτ2 : 0 < τ / 2 := half_pos hτ
  filter_upwards [h' (τ / 2) hτ2, ((tendsto_rpow_atTop hτ2).comp (tendsto_natCast_atTop_iff.2 hsz)).eventually
    (eventually_ge_atTop 2)] with n hn hN2
  rintro ⟨⟨σ, a⟩, hg⟩
  have h1 := hn ⟨((σ 1, σ 0), (a 1, a 0)), hg⟩
  have h2 := hn ⟨((σ 0, σ 1), (a 0, a 1)), hg⟩
  simp only at h1 h2
  set N : ℝ := ((sz.size n : ℕ) : ℝ) with hNdef
  have hNpos : 0 < N := Nat.cast_pos.mpr (by have := sz.one_le_size n; omega)
  set ζ : ℝ := (1 - t n)⁻¹ * (sz.Bctl n (t n)) ^ (5 / 2 : ℝ) with hζdef
  have hζ0 : 0 ≤ ζ := by
    have h1t : 0 < 1 - t n := by linarith [ht1 n]
    have hB := STBctl_pos sz n (ht1 n)
    positivity
  have hint : ∀ σc σo (ac ao : Zd d (sz.L n)), Integrable (fun ω : sz.SeqΩ => LWcutg (baFMz sz z) n (t n) σc σo ac ao ω) (BAExp14a_μ sz) :=
    fun σc σo ac ao => by
      obtain ⟨hc, C, hC⟩ := BAExp14a2_BM_cutg hκ hflow n (ht0 n) (htT n) σc σo ac ao
      exact BAExp14a_integrable hc hC
  have hsplit : ∫ ω, LWEg (baFMz sz z) n (t n) σ a ω ∂(BAExp14a_μ sz) =
      ∫ ω, LWcutg (baFMz sz z) n (t n) (σ 1) (σ 0) (a 1) (a 0) ω ∂(BAExp14a_μ sz) +
        ∫ ω, LWcutg (baFMz sz z) n (t n) (σ 0) (σ 1) (a 0) (a 1) ω ∂(BAExp14a_μ sz) := by
    unfold LWEg
    exact integral_add (hint _ _ _ _) (hint _ _ _ _)
  change ‖∫ ω, LWEg (baFMz sz z) n (t n) σ a ω ∂(BAExp14a_μ sz)‖ ≤ N ^ τ * ζ
  rw [hsplit]
  have hNτ : N ^ τ = N ^ (τ / 2) * N ^ (τ / 2) := by
    rw [← Real.rpow_add hNpos]; congr 1; ring
  calc _ ≤ ‖∫ ω, LWcutg (baFMz sz z) n (t n) (σ 1) (σ 0) (a 1) (a 0) ω ∂(BAExp14a_μ sz)‖ +
        ‖∫ ω, LWcutg (baFMz sz z) n (t n) (σ 0) (σ 1) (a 0) (a 1) ω ∂(BAExp14a_μ sz)‖ := norm_add_le _ _
    _ ≤ N ^ (τ / 2) * ζ + N ^ (τ / 2) * ζ := add_le_add h1 h2
    _ = 2 * (N ^ (τ / 2) * ζ) := by ring
    _ ≤ N ^ (τ / 2) * (N ^ (τ / 2) * ζ) :=
        mul_le_mul_of_nonneg_right hN2 (mul_nonneg (Real.rpow_nonneg hNpos.le _) hζ0)
    _ = N ^ τ * ζ := by rw [← mul_assoc, ← hNτ]

/-! ## 4. Target 3: the assembly of S1, S2, S3 into the R1 cut pin -/

/-- A finite sum of `m` terms each of norm `≤ c` has norm `≤ m c`. -/
private theorem BAExp14a2_norm_sum_fin_le {m : ℕ} {F : Fin m → ℂ} {c : ℝ} (h : ∀ k, ‖F k‖ ≤ c) :
    ‖∑ k, F k‖ ≤ m * c :=
  (norm_sum_le _ _).trans ((Finset.sum_le_sum fun k _ => h k).trans (by simp))

/-- **`baLWCutExpTw_of_S2`** (target 3; twin of `lwCutExp_of_terms`, `LWExpTerm2.lean:1956`): per index `(σc, σo, ac, ao)`,
`baExp14b_expand_holds` writes `𝔼 LWcutg` (both charges; the red one inside the identity through `BAExp14bCutConj`) as 6 + 8 + 4 family
expectations; each is `≤ N^{τ/2} (1 - t)⁻¹ B^{5/2}` from `baExp14a_S1_holds` (premises 1-2), the antecedent `BAExp14bS2` (all seven) and
`baExp14bS3_holds` (premises 1-5) at the same index `(k, (σc, σo), (ac, ao))` of the same index set; `18 ≤ N^{τ/2}` eventually. -/
theorem baLWCutExpTw_of_S2 : ∀ d : ℕ, BALWCutExpTwOfS2 d := by
  intro d hS2 hd κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow t ht0 htT μ hE hA hM hK hD hT1 hT2
  have s1 := baExp14a_S1_holds d hd κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow t ht0 htT hE hA
  have s2 := hS2 hd κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow t ht0 htT hE hA hM hK hD hT1 hT2
  have s3 := baExp14bS3_holds d hd κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow t ht0 htT hE hA hM hK hD
  have hsz : Tendsto sz.size atTop atTop := Sizes.tendsto_size sz hflow.1.2.2.1
  have ht1 : ∀ n, t n < 1 := fun n => (ba_G_data hκ sz hflow n (ht0 n) (htT n)).1
  have p1 := (BAExp14a_det_iff (P := BAExp14a_μ sz) hsz _ _).1 s1
  have p2 := (BAExp14a_det_iff (P := BAExp14a_μ sz) hsz _ _).1 s2
  have p3 := (BAExp14a_det_iff (P := BAExp14a_μ sz) hsz _ _).1 s3
  refine (BAExp14a_det_iff (P := BAExp14a_μ sz) hsz _ _).2 ?_
  intro τ hτ
  have hτ2 : 0 < τ / 2 := half_pos hτ
  filter_upwards [p1 (τ / 2) hτ2, p2 (τ / 2) hτ2, p3 (τ / 2) hτ2,
    ((tendsto_rpow_atTop hτ2).comp (tendsto_natCast_atTop_iff.2 hsz)).eventually (eventually_ge_atTop 18)] with n a1 a2 a3 hN18
  rintro ⟨⟨⟨σc, σo⟩, ac, ao⟩, hg⟩
  have hid := baExp14b_expand_holds d hd κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow n (t n) (ht0 n) (htT n) σc σo ac ao
  set N : ℝ := ((sz.size n : ℕ) : ℝ) with hNdef
  have hNpos : 0 < N := Nat.cast_pos.mpr (by have := sz.one_le_size n; omega)
  set ζ : ℝ := (1 - t n)⁻¹ * (sz.Bctl n (t n)) ^ (5 / 2 : ℝ) with hζdef
  have hζ0 : 0 ≤ ζ := by
    have h1t : 0 < 1 - t n := by linarith [ht1 n]
    have hB := STBctl_pos sz n (ht1 n)
    positivity
  have hu0 : 0 ≤ N ^ (τ / 2) := Real.rpow_nonneg hNpos.le _
  have hNτ : N ^ τ = N ^ (τ / 2) * N ^ (τ / 2) := by
    rw [← Real.rpow_add hNpos]; congr 1; ring
  have e1 : ∀ k : Fin 6, ‖∫ ω, BAExp14aS1Fam sz z n (t n) ω k σc σo ac ao ∂(Sizes.seqP (sz.withLam 0))‖ ≤ N ^ (τ / 2) * ζ :=
    fun k => a1 ⟨(k, (σc, σo), (ac, ao)), hg⟩
  have e2 : ∀ j : Fin 8, ‖∫ ω, BAExp14bS2Fam sz z n (t n) ω j σc σo ac ao ∂(Sizes.seqP (sz.withLam 0))‖ ≤ N ^ (τ / 2) * ζ :=
    fun j => a2 ⟨(j, (σc, σo), (ac, ao)), hg⟩
  have e3 : ∀ j : Fin 4, ‖∫ ω, BAExp14bS3Fam sz z n (t n) ω j σc σo ac ao ∂(Sizes.seqP (sz.withLam 0))‖ ≤ N ^ (τ / 2) * ζ :=
    fun j => a3 ⟨(j, (σc, σo), (ac, ao)), hg⟩
  have b1 := BAExp14a2_norm_sum_fin_le e1
  have b2 := BAExp14a2_norm_sum_fin_le e2
  have b3 := BAExp14a2_norm_sum_fin_le e3
  have tri : ∀ A B C : ℂ, ‖A + B + C‖ ≤ ‖A‖ + ‖B‖ + ‖C‖ := fun A B C => by
    have h1 := norm_add_le A B
    have h2 := norm_add_le (A + B) C
    linarith
  change ‖∫ ω, LWcutg (baFMz sz z) n (t n) σc σo ac ao ω ∂(Sizes.seqP (sz.withLam 0))‖ ≤ N ^ τ * ζ
  rw [hid]
  calc _ ≤ _ := tri _ _ _
    _ ≤ (6 : ℕ) * (N ^ (τ / 2) * ζ) + (8 : ℕ) * (N ^ (τ / 2) * ζ) + (4 : ℕ) * (N ^ (τ / 2) * ζ) := by
        simpa only [Fintype.card_fin] using add_le_add (add_le_add b1 b2) b3
    _ = 18 * (N ^ (τ / 2) * ζ) := by push_cast; ring
    _ ≤ N ^ (τ / 2) * (N ^ (τ / 2) * ζ) :=
        mul_le_mul_of_nonneg_right hN18 (mul_nonneg hu0 hζ0)
    _ = N ^ τ * ζ := by rw [← mul_assoc, ← hNτ]


/-! ## 5. Target 4: the composition -/

/-- **`baLWtermEXPTw_of_S2`** (target 4): the reduction after the assembly.  Consumers: L6 in the last terminal ticket (L40-C1), V1-BA. -/
theorem baLWtermEXPTw_of_S2 : ∀ d : ℕ, BALWtermEXPTwOfS2 d :=
  fun d hS2 => baLWtermEXPTw_of_cut d (baLWCutExpTw_of_S2 d hS2)

/-! ## 6. Compiled nonempty instances (target 6)

`d = 3`, `sz0` (`n = 0`: `L = 4`, `W = 32`, `N = 2097152`, `λ = 1/64`), `zSeq`, `flow_sz0` (`κ = 1/2`, `ε = 𝔡 = 1/10`, `𝔠 = 1/6`),
`t ≡ 1/2 ≤ BAflowT0` (`half_lt_t0`): every deterministic hypothesis is discharged (`3 ≤ 3`, `0 < 1/2`, `0 < 1/10`, `flow_sz0`, `0 ≤ t`,
`t ≤ BAflowT0`).  What stays a hypothesis of the examples is the five Step 1/2 pins, TL2 and, where marked, TL1 and S2 (owed by other
gates: `Test/Axioms.lean:192-193`, L4b2 = T2489). -/

end RBM.BA

end
