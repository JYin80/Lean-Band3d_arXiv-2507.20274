/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Universality.GUEPhase.RandomLayerB
import RBM3D.Induction.SizesComp
import Mathlib.Data.Nat.Nth

/-!
# UN-51 repaired (RandomLayerBG): `g1Rowk_of_inputsG`, the generic successor of `g1Rowk_of_inputs`

T2475 (BA stage M/N row C5g; T2449 design `§1.3`, E-a to E-g).  `g1Rowk_of_inputs` (`RandomLayerB.lean:316`) takes
the kind's inputs T1 (`RandomLayerB_Flow`), T1' (`RandomLayerB_Dom`), T6 (`RandomLayerB_Bulk`), T2
(`RandomLayerB_Prod`), T4 (`RandomLayerB_Que`) in a form that is false at `UNKind.ba` (T1 conj. 1, 2, 4, T1', T6:
paper-delta `T2449b`).  This file adds the primed successors; `RandomLayerB`, `RandomLayerA` and the band chain are
not edited, the merged `UNG1Rowk` is the conclusion, unchanged.

* `RBG_Flow` (`Flow'`): the Lemma 2.8 facts at a margin `κ'(κ)`: the margin datum `Ed κ'` replaces `|fE| ≤ 2 - κ`,
  the constant `cT` replaces `1/16`, and `etaT = √fT Im z` is dropped.
* `RBG_Dom` (`Dom'`): the flow domain `Fl` holds at a margin `κ'(κ)`.
* `RBG_Prod` (`Prod'`): T2 with `Ed κ'`, and the scale `√fT Im z` in place of `etaT (fE) (fT)`.
* `RBG_Que` (`Que'`): T4 with `Ed κ'` at a margin `κ' > 0`.
* `RBG_Comp`, `RBG_ProfComp` (D1, replace `RandomLayerB_Bulk`): along a strictly monotone `φ`, the bulk, `LLAt` and
  `QueAt` pass from `sz.comp φ` back to `sz` at `φ j`; `RandomLayerBG_pad_subseq` is the padding along `Nat.nth`
  of the bad `n` that replaces T6 and `RandomLayerB_pad` (paper-delta `T2475a`).
* `g1Rowk_of_inputsG` (D2): `UNG1Rowk K P ML Loc Que` from `RBG_Flow`, `RBG_Dom`, `RBG_Comp`, `RBG_Prod`,
  `RandomLayerB_LL` (T3, unchanged), `RBG_Que` and `RandomLayerB_MLout` (T5, unchanged, under `ML`).  The proof
  copies `RandomLayerB_oull_seq`, `_eq747_seq` with `κ'`, `cT` and the scale `√fT Im z`: the size rows are those of
  `RandomLayerA` at the scale `N^{-τD}√cT η`, reached from `rowsLL`, `rowsQ` (`τD' = τU/4`, resp. `τU/2`) once
  `N^{τU/4}` (resp. `N^{τU/2}`) `≥ 1/(4√cT)`.
* Band side: the band recoveries of `RBG_Flow` (`flowG_of_band`), `RBG_Dom`, `RBG_Comp`, `RBG_Prod`, `RBG_Que` from the
  merged `RandomLayerB_*_band`, and `g1Rowk_of_inputsG` at the band data at `sz0`.  The band margin datum carries the T1
  identity `etaT = √lemT Im z` (paper-delta candidate `T2475b`), which `RBG_Prod` at the band needs.

Everything before the band section is generic: no `lemE`, `lemT`, `msc`, `etaT`, `gueScale`, `STFlow` and no `BA/*`.
Helpers the ticket does not pin are `private` or carry the prefix `RandomLayerBG_`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

namespace RBM.Univ.GUEPhase

open MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.Gauss RBM.Gauss.Sizes RBM.Path RBM.Loop
  RBM.Univ RBM.Endpoints
open scoped NNReal ENNReal

section Generic

variable {d : ℕ}

/-! ### The primed inputs (targets 1-4; the texts of `docs/tickets/checks/T2475-check.lean`, Part 2) -/

/-- `Flow'` (replaces `RandomLayerB_Flow` = T1, `RandomLayerB.lean:103`): `|fE| ≤ 2 - κ` becomes the margin datum
`Ed κ'` at a margin `κ'`, `1/16 ≤ fT` becomes `cT ≤ fT`, and `etaT = √fT Im z` is dropped. -/
def RBG_Flow (K : UNKind d) (Ed : ℝ → Sizes d → ℕ → ℂ → Prop) (fT : Sizes d → ℕ → ℂ → ℝ) : Prop :=
  ∀ κ : ℝ, 0 < κ → ∃ κ' c cT : ℝ, 0 < κ' ∧ 0 < c ∧ 0 < cT ∧ ∀ (sz : Sizes d) (n : ℕ) (z : ℂ),
    K.bulk sz κ z.re n → 0 < z.im → z.im ≤ 1 →
      Ed κ' sz n z ∧ cT ≤ fT sz n z ∧ fT sz n z < 1 ∧ 1 - fT sz n z ≤ z.im / c

/-- `Dom'` (replaces `RandomLayerB_Dom`, `RandomLayerB.lean:111`): the flow domain `Fl` holds at a margin `κ'(κ)`. -/
def RBG_Dom (K : UNKind d) (Fl : Sizes d → ℝ → ℝ → ℝ → ℝ → (ℕ → ℂ) → Prop) : Prop :=
  ∀ κ : ℝ, 0 < κ → ∃ κ' : ℝ, 0 < κ' ∧ ∀ (𝔠 𝔡 ε : ℝ) (sz : Sizes d), sz.Admissible 𝔠 𝔡 → 0 < ε → ∀ E η : ℕ → ℝ,
    (∀ n, K.bulk sz κ (E n) n) → (∀ n, Nsz sz n ^ (-1 + ε) ≤ η n) → (∀ n, η n ≤ 1) →
      Fl sz κ' ε 𝔠 𝔡 (fun n => (E n : ℂ) + (η n : ℂ) * Complex.I)

/-- `Prod'` (replaces `RandomLayerB_Prod` = T2, `RandomLayerB.lean:132`): `|fE| ≤ 2 - κ` becomes `Ed κ'`;
`etaT (fE) (fT)`, `gueScale` become `√fT Im z`, `N √fT Im z`. -/
def RBG_Prod (Ed : ℝ → Sizes d → ℕ → ℂ → Prop) (fE fT : Sizes d → ℕ → ℂ → ℝ)
    (MO : ∀ _ : Sizes d, (ℕ → ℂ) → (ℕ → ℝ) → Prop)
    (KF PB : ∀ sz : Sizes d, (ℕ → ℝ) → (ℕ → ℝ) → (ℕ → ℝ) → (∀ n, ℝ → LoopIdx (Zd d (sz.L n)) → ℂ) → Prop) : Prop :=
  ∀ (𝔠 𝔡 κ' τD : ℝ) (sz : Sizes d), sz.Admissible 𝔠 𝔡 → 0 < κ' → 0 < τD → ∀ (z : ℕ → ℂ) (t1 : ℕ → ℝ),
    (∀ n, Ed κ' sz n (z n)) → (∀ n, 0 ≤ t1 n) → (∀ n, t1 n ≤ fT sz n (z n)) → (∀ n, fT sz n (z n) < 1) →
    (∀ᶠ n in atTop, fT sz n (z n) - t1 n ≤ Nsz sz n ^ (-τD) * (Real.sqrt (fT sz n (z n)) * (z n).im)) →
    (∀ᶠ n in atTop, (Nsz sz n * (Real.sqrt (fT sz n (z n)) * (z n).im))⁻¹ ≤ Nsz sz n ^ (-τD)) →
    (∀ᶠ n in atTop, ((sz.L n : ℕ) : ℝ) ^ d * (1 - t1 n) ≤ sz.lam n ^ 2) →
    (∀ᶠ n in atTop, ((sz.L n : ℕ) : ℝ) ^ d * (1 - t1 n) ≤ 1) → MO sz z t1 →
    ∃ Kt : ∀ n, ℝ → LoopIdx (Zd d (sz.L n)) → ℂ,
      KF sz (fun n => fE sz n (z n)) t1 (fun n => fT sz n (z n)) Kt ∧
        PB sz (fun n => fE sz n (z n)) t1 (fun n => fT sz n (z n)) Kt

/-- `Que'` (replaces `RandomLayerB_Que` = T4, `RandomLayerB.lean:166`): `|fE| ≤ 2 - κ` becomes `Ed κ'` at a margin
`κ' > 0` (T4 has no `etaT`, `gueScale`). -/
def RBG_Que (K : UNKind d) (P : UNOUProfile K) (Ed : ℝ → Sizes d → ℕ → ℂ → Prop) (fE fT : Sizes d → ℕ → ℂ → ℝ)
    (MO : ∀ _ : Sizes d, (ℕ → ℂ) → (ℕ → ℝ) → Prop)
    (KF PB : ∀ sz : Sizes d, (ℕ → ℝ) → (ℕ → ℝ) → (ℕ → ℝ) → (∀ n, ℝ → LoopIdx (Zd d (sz.L n)) → ℂ) → Prop) : Prop :=
  ∀ (𝔠 𝔡 κ κ' τU : ℝ) (sz : Sizes d), sz.Admissible 𝔠 𝔡 → 0 < κ → 0 < κ' → 0 < τU → τU ≤ ouTauMax 𝔠 𝔡 →
    ∀ E t : ℕ → ℝ, (∀ n, K.bulk sz κ (E n) n) → (∀ n, 0 ≤ t n ∧ t n ≤ ouTStar sz τU n) →
      ∀ z : ℕ → ℂ, (∀ᶠ n in atTop, z n = (E n : ℂ) + ((ouEtaQ sz 𝔡 n : ℝ) : ℂ) * Complex.I) →
        (∀ n, Ed κ' sz n (z n) ∧ 0 ≤ (1 - ouZeta (t n)) * fT sz n (z n) ∧
          (1 - ouZeta (t n)) * fT sz n (z n) ≤ fT sz n (z n) ∧ fT sz n (z n) < 1) →
        ∀ Kt, KF sz (fun n => fE sz n (z n)) (fun n => (1 - ouZeta (t n)) * fT sz n (z n)) (fun n => fT sz n (z n)) Kt →
          MO sz z (fun n => (1 - ouZeta (t n)) * fT sz n (z n)) →
          PB sz (fun n => fE sz n (z n)) (fun n => (1 - ouZeta (t n)) * fT sz n (z n)) (fun n => fT sz n (z n)) Kt →
          ∀ τ : ℝ, 0 < τ → ∀ᶠ n in atTop, RandomLayerB_QueAt K P sz 𝔡 n (E n) (t n) τ

/-! ### D1: the compatibility input (target 5) -/

/-- The padding along `Nat.nth` of the bad `n` (paper-delta `T2475a`): if the conclusion `Q` holds eventually along
every strictly monotone `φ` with `S (φ j)` for all `j`, then `S n → Q n` holds eventually.  Replaces
`RandomLayerB_Bulk` (T6) and the private `RandomLayerB_pad`. -/
theorem RandomLayerBG_pad_subseq (S Q : ℕ → Prop)
    (h : ∀ φ : ℕ → ℕ, StrictMono φ → (∀ j, S (φ j)) → ∀ᶠ j in atTop, Q (φ j)) : ∀ᶠ n in atTop, S n → Q n := by
  by_contra hcon
  have hfreq : ∃ᶠ n in atTop, S n ∧ ¬ Q n := Filter.not_eventually.mp hcon |>.mono fun n hn => not_imp.mp hn
  have hinf : (Set.ofPred fun n => S n ∧ ¬ Q n).Infinite := Nat.frequently_atTop_iff_infinite.mp hfreq
  have hmem := fun j => Nat.nth_mem_of_infinite hinf j
  exact (h _ (Nat.nth_strictMono hinf) fun j => (hmem j).1).exists.elim fun j hj => (hmem j).2 hj

/-- **D1, kind half**: along a strictly monotone `φ`, the bulk, `LLAt` and `QueAt` pass from `sz.comp φ` to `sz` at
`φ j` (the bulk in the other direction, from `sz` at `φ j` to `sz.comp φ` at `j`). -/
def RBG_Comp (K : UNKind d) (P : UNOUProfile K) : Prop :=
  ∀ (sz : Sizes d) (φ : ℕ → ℕ), StrictMono φ → ∀ j : ℕ,
    (∀ κ e : ℝ, K.bulk sz κ e (φ j) → K.bulk (sz.comp φ) κ e j) ∧
    (∀ (τU e s δ : ℝ) (p : ℕ),
      RandomLayerB_LLAt K (sz.comp φ) τU j e s δ p → RandomLayerB_LLAt K sz τU (φ j) e s δ p) ∧
    (∀ 𝔡 e s τ : ℝ, RandomLayerB_QueAt K P (sz.comp φ) 𝔡 j e s τ → RandomLayerB_QueAt K P sz 𝔡 (φ j) e s τ)

/-- **D1, profile half**: the profile reads `sz` at the index only. -/
def RBG_ProfComp (K : UNKind d) (P : UNOUProfile K) : Prop :=
  ∀ (sz : Sizes d) (φ : ℕ → ℕ) (j : ℕ) (ζ : ℝ) (z : ℂ) (a b : Zd d (sz.L (φ j))),
    P.pm (sz.comp φ) j ζ z a b = P.pm sz (φ j) ζ z a b ∧ P.pp (sz.comp φ) j ζ z a b = P.pp sz (φ j) ζ z a b

/-- Integral transport along a measure preserving map in the first factor of a product (generic helper). -/
private theorem RandomLayerBG_transport {A A' B E : Type*} [MeasurableSpace A] [MeasurableSpace A']
    [MeasurableSpace B] [NormedAddCommGroup E] [NormedSpace ℝ E] {μ : Measure A} {μ' : Measure A'}
    {ν : Measure B} [SFinite μ] [SFinite μ'] [SFinite ν] {R : A → A'} (hR : MeasurePreserving R μ μ')
    {g : A' × B → E} (hg : AEStronglyMeasurable g (μ'.prod ν)) :
    ∫ ω, g (R ω.1, ω.2) ∂(μ.prod ν) = ∫ ω, g ω ∂(μ'.prod ν) := by
  have hP : MeasurePreserving (Prod.map R id) (μ.prod ν) (μ'.prod ν) := hR.prod (MeasurePreserving.id ν)
  rw [← hP.map_eq] at hg
  have h := integral_map hP.measurable.aemeasurable hg
  rw [hP.map_eq] at h
  exact h.symm

/-- `ouMatC` is measurable in the sample (the statement of the private `UnivMain_measurable_ouMatC`). -/
private theorem RandomLayerBG_meas_ouMatC {sz : Sizes d} (M : UNModelC sz) (n : ℕ) (t : ℝ) :
    Measurable (ouMatC M n t) := by
  have : ouMatC M n t = fun ω => ouMat M.toUNModel n t ω + (1 - Real.exp (-t / 2)) • M.mean n :=
    funext (ouMatC_eq_ouMat_add M n t)
  rw [this]; exact (measurable_ouMat M.toUNModel n t).add_const _

/-- **D1, law-level helper**: `RBG_Comp` from the bulk transfer and a measure preserving `R` intertwining `H` and the
mean (both discharges, band and BA, go through this; the profile half is the hypothesis `RBG_ProfComp`). -/
theorem RandomLayerBG_Comp_of_law (K : UNKind d) (P : UNOUProfile K) (hP : RBG_ProfComp K P)
    (hb : ∀ (sz : Sizes d) (φ : ℕ → ℕ) (j : ℕ) (κ e : ℝ), K.bulk sz κ e (φ j) → K.bulk (sz.comp φ) κ e j)
    (hl : ∀ (sz : Sizes d) (φ : ℕ → ℕ), StrictMono φ → ∃ R : SeqΩ sz → SeqΩ (sz.comp φ),
      MeasurePreserving R (K.M sz).μ (K.M (sz.comp φ)).μ ∧
        (∀ j ω, (K.M (sz.comp φ)).H j (R ω) = (K.M sz).H (φ j) ω) ∧
        ∀ j, (K.M (sz.comp φ)).mean j = (K.M sz).mean (φ j)) : RBG_Comp K P := by
  intro sz φ hφ j
  obtain ⟨R, hR, hH, hm⟩ := hl sz φ hφ
  have hmat : ∀ (s : ℝ) (ω : SeqΩ sz × Ω d (sz.L (φ j)) (sz.W (φ j))),
      ouMatC (K.M (sz.comp φ)) j s (R ω.1, ω.2) = ouMatC (K.M sz) (φ j) s ω := fun s ω => by
    simp only [ouMatC, hH j ω.1, hm j]; rfl
  refine ⟨hb sz φ j, fun τU e s δ p h x => ?_, fun 𝔡 e s τ h a b => ?_⟩
  · refine le_trans (le_of_eq ?_) (h x)
    refine Eq.trans ?_ (RandomLayerBG_transport (ν := gueP d (sz.L (φ j)) (sz.W (φ j))) hR (g := fun ω =>
      ‖Gres (ouMatC (K.M (sz.comp φ)) j s ω) ((e : ℂ) + ((ouEtaLL sz τU (φ j) : ℝ) : ℂ) * Complex.I) true x x‖ ^ (2 * p))
      ((((walk_measurable_Gres_apply _ true x x).comp (RandomLayerBG_meas_ouMatC _ j s)).norm).pow_const
        (2 * p)).aestronglyMeasurable)
    exact integral_congr_ae (Eventually.of_forall fun ω =>
      congrArg (fun A => ‖Gres A ((e : ℂ) + ((ouEtaLL sz τU (φ j) : ℝ) : ℂ) * Complex.I) true x x‖ ^ (2 * p)) (hmat s ω).symm)
  · have key : ∀ F : Matrix (Idx d (sz.L (φ j)) (sz.W (φ j))) (Idx d (sz.L (φ j)) (sz.W (φ j))) ℂ →
        Idx d (sz.L (φ j)) (sz.W (φ j)) → Idx d (sz.L (φ j)) (sz.W (φ j)) → ℂ, (∀ x y, Measurable fun A => F A x y) →
        ∫ ω, avg2 sz (φ j) (fun x y => F (ouMatC (K.M sz) (φ j) s ω) x y) a b ∂(ouP (K.M sz).toUNModel (φ j)) =
          ∫ ω, avg2 (sz.comp φ) j (fun x y => F (ouMatC (K.M (sz.comp φ)) j s ω) x y) a b
            ∂(ouP (K.M (sz.comp φ)).toUNModel j) := fun F hF => by
      refine Eq.trans ?_ (RandomLayerBG_transport (ν := gueP d (sz.L (φ j)) (sz.W (φ j))) hR (g := fun ω =>
        avg2 (sz.comp φ) j (fun x y => F (ouMatC (K.M (sz.comp φ)) j s ω) x y) a b)
        (((measurable_const.mul (Finset.measurable_sum _ fun x _ => Finset.measurable_sum _ fun y _ =>
          (hF x y).comp (RandomLayerBG_meas_ouMatC _ j s))).aestronglyMeasurable)))
      exact integral_congr_ae (Eventually.of_forall fun ω =>
        congrArg (fun A => avg2 sz (φ j) (fun x y => F A x y) a b) (hmat s ω).symm)
    have e1 := key (fun A x y => ((‖Gres A ((e : ℂ) + ((ouEtaQ sz 𝔡 (φ j) : ℝ) : ℂ) * Complex.I) true x y‖ ^ 2 : ℝ) : ℂ))
      fun x y => Complex.measurable_ofReal.comp ((walk_measurable_Gres_apply _ true x y).norm.pow_const 2)
    have e2 := key (fun A x y => Gres A ((e : ℂ) + ((ouEtaQ sz 𝔡 (φ j) : ℝ) : ℂ) * Complex.I) true x y *
      Gres A ((e : ℂ) + ((ouEtaQ sz 𝔡 (φ j) : ℝ) : ℂ) * Complex.I) true y x)
      fun x y => (walk_measurable_Gres_apply _ true x y).mul (walk_measurable_Gres_apply _ true y x)
    have hp := hP sz φ j (ouZeta s) ((e : ℂ) + ((ouEtaQ sz 𝔡 (φ j) : ℝ) : ℂ) * Complex.I) a b
    refine ⟨?_, ?_⟩
    · rw [e1, ← hp.1]; exact (h a b).1
    · rw [e2, ← hp.2]; exact (h a b).2

/-! ### The repaired rows (E-f; private) -/

/-- Scale conversion: from `t ≤ N^{-b} η/4` and `4 (N η)⁻¹ ≤ N^{-b}` to `t ≤ N^{-a} (s η)` and `(N s η)⁻¹ ≤ N^{-a}`
once `(4 s)⁻¹ ≤ N^{b-a}` (`s = √cT`; `b - a = τU/4` for `LL`, `τU/2` for `Que`). -/
private theorem RandomLayerBG_scale {N η t a b s : ℝ} (hN : 0 < N) (hη : 0 < η) (hs : 0 < s)
    (hbig : (4 * s)⁻¹ ≤ N ^ (b - a)) (r1 : t ≤ N ^ (-b) * (η / 4)) (r2 : 4 * (N * η)⁻¹ ≤ N ^ (-b)) :
    t ≤ N ^ (-a) * (s * η) ∧ (N * (s * η))⁻¹ ≤ N ^ (-a) := by
  have hu : 0 < N ^ (b - a) := Real.rpow_pos_of_pos hN _
  have hinv : (N ^ (b - a))⁻¹ ≤ 4 * s := (inv_le_comm₀ hu (by positivity)).2 hbig
  have hNb : N ^ (-b) = N ^ (-a) * (N ^ (b - a))⁻¹ := by
    rw [← Real.rpow_neg hN.le, ← Real.rpow_add hN]; congr 1; ring
  have hNa : 0 < N ^ (-a) := Real.rpow_pos_of_pos hN _
  constructor
  · calc t ≤ N ^ (-b) * (η / 4) := r1
      _ = N ^ (-a) * ((N ^ (b - a))⁻¹ * (η / 4)) := by rw [hNb]; ring
      _ ≤ N ^ (-a) * ((4 * s) * (η / 4)) := by gcongr
      _ = N ^ (-a) * (s * η) := by ring
  · have e : (N * (s * η))⁻¹ = (4 * s)⁻¹ * (4 * (N * η)⁻¹) := by
      have := hN.ne'; have := hη.ne'; have := hs.ne'; field_simp
    calc (N * (s * η))⁻¹ = (4 * s)⁻¹ * (4 * (N * η)⁻¹) := e
      _ ≤ (4 * s)⁻¹ * N ^ (-b) := by gcongr
      _ = (4 * s)⁻¹ * (N ^ (-a) * (N ^ (b - a))⁻¹) := by rw [hNb]
      _ ≤ (4 * s)⁻¹ * (N ^ (-a) * (4 * s)) := by gcongr
      _ = N ^ (-a) := by have := hs.ne'; field_simp

/-- **`RandomLayer_rows_flow` with the repaired flow facts** (copy of `RandomLayerA.lean:98`): `cT ≤ t₀ < 1` replaces
`1/16 ≤ t₀ < 1`, the scale is `√t₀ η` (no `etaT`, `gueScale`), and `r1`, `r2` are stated at `√cT η`
(`√cT ≤ √t₀`): with `t₁ = (1 - ζ(t_n)) t₀` they give the hypotheses of `RBG_Prod`. -/
private theorem RandomLayerBG_rows_flow (sz : Sizes d) {c cT τD : ℝ} {t t0 η : ℕ → ℝ} (hcT : 0 < cT)
    (ht : ∀ n, 0 ≤ t n) (hη0 : ∀ n, 0 < η n) (hs : ∀ n, cT ≤ t0 n) (ht1 : ∀ n, t0 n < 1)
    (h1t : ∀ n, 1 - t0 n ≤ η n / c)
    (r1 : ∀ᶠ n in atTop, t n ≤ Nsz sz n ^ (-τD) * (Real.sqrt cT * η n))
    (r2 : ∀ᶠ n in atTop, (Nsz sz n * (Real.sqrt cT * η n))⁻¹ ≤ Nsz sz n ^ (-τD))
    (r3 : ∀ᶠ n in atTop, ((sz.L n : ℕ) : ℝ) ^ d * (η n / c + t n) ≤ sz.lam n ^ 2)
    (r4 : ∀ᶠ n in atTop, ((sz.L n : ℕ) : ℝ) ^ d * (η n / c + t n) ≤ 1) :
    (∀ n, 0 ≤ (1 - ouZeta (t n)) * t0 n) ∧ (∀ n, (1 - ouZeta (t n)) * t0 n ≤ t0 n) ∧
      (∀ᶠ n in atTop, t0 n - (1 - ouZeta (t n)) * t0 n ≤ Nsz sz n ^ (-τD) * (Real.sqrt (t0 n) * η n)) ∧
      (∀ᶠ n in atTop, (Nsz sz n * (Real.sqrt (t0 n) * η n))⁻¹ ≤ Nsz sz n ^ (-τD)) ∧
      (∀ᶠ n in atTop, ((sz.L n : ℕ) : ℝ) ^ d * (1 - (1 - ouZeta (t n)) * t0 n) ≤ sz.lam n ^ 2) ∧
      (∀ᶠ n in atTop, ((sz.L n : ℕ) : ℝ) ^ d * (1 - (1 - ouZeta (t n)) * t0 n) ≤ 1) := by
  have hNpos : ∀ n, 0 < Nsz sz n := Nsz_pos sz
  have hζ0 : ∀ n, 0 ≤ ouZeta (t n) := fun n => ZeroModeProfile_ouZeta_nonneg (ht n)
  have hζ1 : ∀ n, ouZeta (t n) ≤ 1 := fun n => ZeroModeProfile_ouZeta_le_one (t n)
  have hζt : ∀ n, ouZeta (t n) ≤ t n := fun n => ZeroModeProfile_ouZeta_le (t n)
  have ht0pos : ∀ n, 0 ≤ t0 n := fun n => hcT.le.trans (hs n)
  have hsq : ∀ n, Real.sqrt cT ≤ Real.sqrt (t0 n) := fun n => Real.sqrt_le_sqrt (hs n)
  have hscT : 0 < Real.sqrt cT := Real.sqrt_pos.2 hcT
  have hdiff : ∀ n, t0 n - (1 - ouZeta (t n)) * t0 n ≤ t n := fun n => by
    have := ht1 n
    nlinarith [hζ0 n, hζt n, ht0pos n]
  have hdiff1 : ∀ n, 1 - (1 - ouZeta (t n)) * t0 n ≤ η n / c + t n := fun n => by
    have h2 : ouZeta (t n) * t0 n ≤ t n := by
      nlinarith [hζ0 n, hζt n, ht0pos n, ht1 n]
    nlinarith [h1t n]
  refine ⟨fun n => mul_nonneg (by linarith [hζ1 n]) (ht0pos n),
    fun n => by nlinarith [hζ0 n, ht0pos n], ?_, ?_, ?_, ?_⟩
  · filter_upwards [r1] with n hN
    calc _ ≤ t n := hdiff n
      _ ≤ Nsz sz n ^ (-τD) * (Real.sqrt cT * η n) := hN
      _ ≤ Nsz sz n ^ (-τD) * (Real.sqrt (t0 n) * η n) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hsq n) (hη0 n).le)
            (Real.rpow_nonneg (hNpos n).le _)
  · filter_upwards [r2] with n hN
    refine le_trans ?_ hN
    exact inv_anti₀ (mul_pos (hNpos n) (mul_pos hscT (hη0 n)))
      (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hsq n) (hη0 n).le) (hNpos n).le)
  · filter_upwards [r3] with n hN
    exact le_trans (mul_le_mul_of_nonneg_left (hdiff1 n) (by positivity)) hN
  · filter_upwards [r4] with n hN
    exact le_trans (mul_le_mul_of_nonneg_left (hdiff1 n) (by positivity)) hN

/-! ### One sequence, kind-generic (copies of `RandomLayerB_oull_seq`, `RandomLayerB_eq747_seq`, edited) -/

/-- **The moment bound of `UNOULLk` along one bulk sequence** (`RandomLayerB_oull_seq`, `RandomLayerB.lean:205`, with
`Flow'`, `Dom'`, `Prod'`): `κ'`, `c`, `cT` from `Flow'` for `Ed` and the rows, `κ''` from `Dom'` for `Fl` and T5; the
rows at `η_LL` are `RandomLayer_rowsLL` at `τD = τU/2`, converted to `τD' = τU/4` and the scale `√cT η`
(`N^{τU/4} ≥ 1/(4√cT)`, eventually). -/
private theorem RandomLayerBG_oull_seq {K : UNKind d} {Ed : ℝ → Sizes d → ℕ → ℂ → Prop}
    {fE fT : Sizes d → ℕ → ℂ → ℝ} {Fl : Sizes d → ℝ → ℝ → ℝ → ℝ → (ℕ → ℂ) → Prop}
    {MO : ∀ _ : Sizes d, (ℕ → ℂ) → (ℕ → ℝ) → Prop}
    {KF PB : ∀ sz : Sizes d, (ℕ → ℝ) → (ℕ → ℝ) → (ℕ → ℝ) →
      (∀ n, ℝ → LoopIdx (Zd d (sz.L n)) → ℂ) → Prop} (hd : 3 ≤ d)
    (h1 : RBG_Flow K Ed fT) (hdom : RBG_Dom K Fl) (h2 : RBG_Prod Ed fE fT MO KF PB)
    (h3 : RandomLayerB_LL K fE fT PB) (h5 : RandomLayerB_MLout fT Fl MO) {𝔠 𝔡 : ℝ} {sz : Sizes d}
    (hA : sz.Admissible 𝔠 𝔡) {τU : ℝ} (hτU : 0 < τU) (hτUm : τU ≤ ouTauMax 𝔠 𝔡) {κ : ℝ} (hκ : 0 < κ)
    {E t : ℕ → ℝ} (hE : ∀ n, K.bulk sz κ (E n) n) (ht : ∀ n, 0 ≤ t n ∧ t n ≤ ouTStar sz τU n)
    (δ : ℝ) (hδ : 0 < δ) (p : ℕ) : ∀ᶠ n in atTop, RandomLayerB_LLAt K sz τU n (E n) (t n) δ p := by
  obtain ⟨κ', c, cT, hκ', hc, hcT, hF⟩ := h1 κ hκ
  obtain ⟨κ'', hκ'', hD⟩ := hdom κ hκ
  have hτ1 : τU ≤ 1 / 100 := hτUm.trans (min_le_right _ _)
  have hη0 := RandomLayer_etaLL_pos sz τU
  have hη1 := RandomLayer_etaLL_le_one sz (by linarith : τU ≤ 1 / 2)
  set z : ℕ → ℂ := fun n => (E n : ℂ) + ((ouEtaLL sz τU n : ℝ) : ℂ) * Complex.I with hz
  have hzre : ∀ n, (z n).re = E n := fun n => by simp [hz]
  have hzim : ∀ n, (z n).im = ouEtaLL sz τU n := fun n => by simp [hz]
  have F := fun n => hF sz n (z n) (by rw [hzre]; exact hE n) (by rw [hzim]; exact hη0 n)
    (by rw [hzim]; exact hη1 n)
  obtain ⟨r1, r2, r3, r4⟩ := RandomLayer_rowsLL sz hd hA hτU hτUm hc (t := t) (fun n => (ht n).2)
  have hscT : 0 < Real.sqrt cT := Real.sqrt_pos.2 hcT
  have hbig : ∀ᶠ n in atTop, (4 * Real.sqrt cT)⁻¹ ≤ Nsz sz n ^ (τU / 2 - τU / 4) := by
    have e : τU / 2 - τU / 4 = τU / 4 := by ring
    rw [e]
    exact ((tendsto_rpow_atTop (by positivity : 0 < τU / 4)).comp hA.2.2.1).eventually_ge_atTop _
  have s1 : ∀ᶠ n in atTop, t n ≤ Nsz sz n ^ (-(τU / 4)) * (Real.sqrt cT * ouEtaLL sz τU n) ∧
      (Nsz sz n * (Real.sqrt cT * ouEtaLL sz τU n))⁻¹ ≤ Nsz sz n ^ (-(τU / 4)) := by
    filter_upwards [r1, r2, hbig] with n a b h
    exact RandomLayerBG_scale (Nsz_pos sz n) (hη0 n) hscT h a b
  obtain ⟨hnn, hle, h730, hscale, hell, hell1⟩ := RandomLayerBG_rows_flow sz (c := c) (τD := τU / 4) (t := t)
    (t0 := fun n => fT sz n (z n)) (η := ouEtaLL sz τU) hcT
    (fun n => (ht n).1) hη0 (fun n => (F n).2.1) (fun n => (F n).2.2.1)
    (fun n => by have := (F n).2.2.2; rwa [hzim] at this)
    (s1.mono fun n h => h.1) (s1.mono fun n h => h.2) r3 r4
  have hflow : Fl sz κ'' (2 * τU) 𝔠 𝔡 z :=
    hD 𝔠 𝔡 (2 * τU) sz hA (by linarith) E (ouEtaLL sz τU) hE (fun _ => le_rfl) hη1
  have hMO := h5 κ'' (2 * τU) 𝔡 𝔠 hκ'' (by linarith) hA.2.1 sz z hflow
    (fun n => (1 - ouZeta (t n)) * fT sz n (z n)) hnn hle
  obtain ⟨Kt, -, hPB⟩ := h2 𝔠 𝔡 κ' (τU / 4) sz hA hκ' (by positivity) z
    (fun n => (1 - ouZeta (t n)) * fT sz n (z n)) (fun n => (F n).1) hnn hle
    (fun n => (F n).2.2.1) (h730.mono fun n h => by rwa [hzim]) (hscale.mono fun n h => by rwa [hzim]) hell hell1 hMO
  exact h3 𝔠 𝔡 κ τU sz hA hκ hτU (by linarith) E t hE (fun n => (ht n).1) Kt hPB δ hδ p

/-- **The body of `UNOUEq747k` along one bulk sequence** (`RandomLayerB_eq747_seq`, `RandomLayerB.lean:241`, with
`Flow'`, `Dom'`, `Prod'`, `Que'`): `z_n = E_n + i η_Q` is replaced, at the finitely many `n` where `η_Q ∉ [N^{-1+ε}, 1]`,
by `E_n + i N^{-1+ε}` (`ε = min(𝔠(𝔡 - 𝔡/3), 1)`); the rows are `RandomLayer_rowsQ` at `τD = τU` converted to
`τD' = τU/2` (`N^{τU/2} ≥ 1/(4√cT)`, eventually). -/
private theorem RandomLayerBG_eq747_seq {K : UNKind d} {P : UNOUProfile K} {Ed : ℝ → Sizes d → ℕ → ℂ → Prop}
    {fE fT : Sizes d → ℕ → ℂ → ℝ} {Fl : Sizes d → ℝ → ℝ → ℝ → ℝ → (ℕ → ℂ) → Prop}
    {MO : ∀ _ : Sizes d, (ℕ → ℂ) → (ℕ → ℝ) → Prop}
    {KF PB : ∀ sz : Sizes d, (ℕ → ℝ) → (ℕ → ℝ) → (ℕ → ℝ) →
      (∀ n, ℝ → LoopIdx (Zd d (sz.L n)) → ℂ) → Prop} (hd : 3 ≤ d)
    (h1 : RBG_Flow K Ed fT) (hdom : RBG_Dom K Fl) (h2 : RBG_Prod Ed fE fT MO KF PB)
    (h4 : RBG_Que K P Ed fE fT MO KF PB) (h5 : RandomLayerB_MLout fT Fl MO) {𝔠 𝔡 : ℝ} {sz : Sizes d}
    (hA : sz.Admissible 𝔠 𝔡) {τU : ℝ} (hτU : 0 < τU) (hτUm : τU ≤ ouTauMax 𝔠 𝔡) {κ : ℝ} (hκ : 0 < κ)
    {E t : ℕ → ℝ} (hE : ∀ n, K.bulk sz κ (E n) n) (ht : ∀ n, 0 ≤ t n ∧ t n ≤ ouTStar sz τU n)
    (τ : ℝ) (hτ : 0 < τ) : ∀ᶠ n in atTop, RandomLayerB_QueAt K P sz 𝔡 n (E n) (t n) τ := by
  classical
  obtain ⟨κ', c, cT, hκ', hc, hcT, hF⟩ := h1 κ hκ
  obtain ⟨κ'', hκ'', hD⟩ := hdom κ hκ
  have h𝔠 := hA.1
  have h𝔡 := hA.2.1
  set ε : ℝ := min (𝔠 * (𝔡 - 𝔡 / 3)) 1 with hε
  have hε0 : 0 < ε := lt_min (mul_pos h𝔠 (by linarith)) one_pos
  have hε1 : ε ≤ 𝔠 * (𝔡 - 𝔡 / 3) := min_le_left _ _
  have hε2 : ε ≤ 1 := min_le_right _ _
  have hN1 : ∀ n, (1 : ℝ) ≤ Nsz sz n := fun n => by exact_mod_cast sz.one_le_size n
  -- the scale `η_Q` is in the window `[N^{-1+ε}, 1]` eventually
  have hwin : ∀ᶠ n in atTop, Nsz sz n ^ (-1 + ε) ≤ ouEtaQ sz 𝔡 n ∧ ouEtaQ sz 𝔡 n ≤ 1 := by
    filter_upwards [queDomain sz hA (ε₀ := 𝔡 / 3) (κ := 2) (by linarith) (by linarith)] with n hn
    have h0 : sz.locDomain 2 (𝔠 * (𝔡 - 𝔡 / 3)) n
        (((0 : ℝ) : ℂ) + ((ouEtaQ sz 𝔡 n : ℝ) : ℂ) * Complex.I) := hn 0 (by norm_num)
    obtain ⟨-, h2', h3'⟩ := h0
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_re,
      Complex.I_im, zero_add, mul_zero, mul_one, add_zero] at h2' h3'
    exact ⟨le_trans (Real.rpow_le_rpow_of_exponent_le (hN1 n) (by linarith)) h2', h3'⟩
  set η' : ℕ → ℝ := fun n =>
    if Nsz sz n ^ (-1 + ε) ≤ ouEtaQ sz 𝔡 n ∧ ouEtaQ sz 𝔡 n ≤ 1 then ouEtaQ sz 𝔡 n
    else Nsz sz n ^ (-1 + ε) with hη'
  have hη'1 : ∀ n, Nsz sz n ^ (-1 + ε) ≤ η' n ∧ η' n ≤ 1 := fun n => by
    by_cases hn : Nsz sz n ^ (-1 + ε) ≤ ouEtaQ sz 𝔡 n ∧ ouEtaQ sz 𝔡 n ≤ 1
    · simp only [hη', hn, and_self, ↓reduceIte]
    · simp only [hη', hn, ↓reduceIte]
      exact ⟨le_rfl, Real.rpow_le_one_of_one_le_of_nonpos (hN1 n) (by linarith)⟩
  have hη'0 : ∀ n, 0 < η' n := fun n =>
    lt_of_lt_of_le (Real.rpow_pos_of_pos (Nsz_pos sz n) _) (hη'1 n).1
  have hev : ∀ᶠ n in atTop, η' n = ouEtaQ sz 𝔡 n := hwin.mono fun n hn => by
    simp only [hη', hn, and_self, ↓reduceIte]
  set z : ℕ → ℂ := fun n => (E n : ℂ) + ((η' n : ℝ) : ℂ) * Complex.I with hz
  have hzre : ∀ n, (z n).re = E n := fun n => by simp [hz]
  have hzim : ∀ n, (z n).im = η' n := fun n => by simp [hz]
  have F := fun n => hF sz n (z n) (by rw [hzre]; exact hE n) (by rw [hzim]; exact hη'0 n)
    (by rw [hzim]; exact (hη'1 n).2)
  obtain ⟨q1, q2, q3, q4⟩ := RandomLayer_rowsQ sz hd hA hτU hτUm hc (t := t) (fun n => (ht n).2)
  have hscT : 0 < Real.sqrt cT := Real.sqrt_pos.2 hcT
  have hbig : ∀ᶠ n in atTop, (4 * Real.sqrt cT)⁻¹ ≤ Nsz sz n ^ (τU - τU / 2) := by
    have e : τU - τU / 2 = τU / 2 := by ring
    rw [e]
    exact ((tendsto_rpow_atTop (by positivity : 0 < τU / 2)).comp hA.2.2.1).eventually_ge_atTop _
  have s1 : ∀ᶠ n in atTop, t n ≤ Nsz sz n ^ (-(τU / 2)) * (Real.sqrt cT * η' n) ∧
      (Nsz sz n * (Real.sqrt cT * η' n))⁻¹ ≤ Nsz sz n ^ (-(τU / 2)) := by
    filter_upwards [q1, q2, hbig, hev] with n a b h he
    rw [he]
    exact RandomLayerBG_scale (Nsz_pos sz n) (he ▸ hη'0 n) hscT h a b
  obtain ⟨hnn, hle, h730, hscale, hell, hell1⟩ := RandomLayerBG_rows_flow sz (c := c) (τD := τU / 2) (t := t)
    (t0 := fun n => fT sz n (z n)) (η := η') hcT
    (fun n => (ht n).1) hη'0 (fun n => (F n).2.1) (fun n => (F n).2.2.1)
    (fun n => by have := (F n).2.2.2; rwa [hzim] at this)
    (s1.mono fun n h => h.1) (s1.mono fun n h => h.2)
    (by filter_upwards [q3, hev] with n h he; rw [he]; exact h)
    (by filter_upwards [q4, hev] with n h he; rw [he]; exact h)
  have hflow : Fl sz κ'' ε 𝔠 𝔡 z :=
    hD 𝔠 𝔡 ε sz hA hε0 E η' hE (fun n => (hη'1 n).1) (fun n => (hη'1 n).2)
  have hMO := h5 κ'' ε 𝔡 𝔠 hκ'' hε0 h𝔡 sz z hflow
    (fun n => (1 - ouZeta (t n)) * fT sz n (z n)) hnn hle
  have hgood : ∀ n, Ed κ' sz n (z n) ∧ 0 ≤ (1 - ouZeta (t n)) * fT sz n (z n) ∧
      (1 - ouZeta (t n)) * fT sz n (z n) ≤ fT sz n (z n) ∧ fT sz n (z n) < 1 :=
    fun n => ⟨(F n).1, hnn n, hle n, (F n).2.2.1⟩
  obtain ⟨Kt, hKF, hPB⟩ := h2 𝔠 𝔡 κ' (τU / 2) sz hA hκ' (by positivity) z
    (fun n => (1 - ouZeta (t n)) * fT sz n (z n)) (fun n => (F n).1) hnn hle
    (fun n => (F n).2.2.1) (h730.mono fun n h => by rwa [hzim]) (hscale.mono fun n h => by rwa [hzim]) hell hell1 hMO
  have hzQ : ∀ᶠ n in atTop, z n = (E n : ℂ) + ((ouEtaQ sz 𝔡 n : ℝ) : ℂ) * Complex.I :=
    hev.mono fun n hn => by simp only [hz, hn]
  exact h4 𝔠 𝔡 κ κ' τU sz hA hκ hκ' hτU hτUm E t hE ht z hzQ hgood Kt hKF hMO hPB τ hτ

/-! ### The kind-generic target (target 7, D2) -/

end Generic

/-! ### Band side (target 8): every premise of `g1Rowk_of_inputsG` at the band from the merged discharges

This section uses the band vocabulary (`lemE`, `lemT`, `etaT`, `gueScale`, `|e| ≤ 2 - κ`). -/

/-! ## Compiled nonempty instance

`g1Rowk_of_inputsG` at the band data (`UNKind.band`, `UNOUProfile.band`, `Ed = RandomLayerBG_bandEd`, `fE = lemE`,
`fT = lemT`, `Fl = STFlow`, `MO`, `KF`, `PB` of the band), every deterministic premise discharged by the lemmas above and
the merged `RandomLayerB_*_band`, at `d = 3`, `sz0` (`L = 4(n+1)`, `W = (2(n+1))^5`, `lam = (2(n+1))^{-6}`),
`𝔠 = 1/6`, `𝔡 = 1/10`, `τ_U = ouTauMax (1/6) (1/10) = 1/720`: `UNMLOut`, `UNLocAvgBand`, `UNQueBand` (pins of other
gates) stay hypotheses.  A nonvacuity instance: `g1Rowk_band` is not replaced. -/

end RBM.Univ.GUEPhase

end
