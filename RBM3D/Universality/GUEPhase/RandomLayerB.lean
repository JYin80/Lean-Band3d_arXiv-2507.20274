/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Universality.GUEPhase.RandomLayerA
import RBM3D.Universality.GUEPhase.LLTransfer
import RBM3D.Universality.GUEPhase.PathBounds
import RBM3D.Universality.GUEPhase.KPrim
import RBM3D.Universality.OUInterfaceK
import RBM3D.Universality.ZeroModeProfile

/-!
# UN-51 (RandomLayerB): `g1Rowk_of_inputs`, `g1Row`, `g1Rowk_band`, `d ≥ 3`

Port of RBM2D `Universality/GUEPhase/RandomLayerB.lean` (152 lines, `g1Row : G1Row`, `9e0f275`).
Paper: arXiv:2507.20274, `paper/tex/1_2_Intro_model_result.tex:566-581`, §7.2 (`(eq:zztE)`,
(7.26)-(7.29), (7.47)).

* `g1Rowk_of_inputs` (U1, kind-generic): `UNG1Rowk K P ML Loc Que` for every kind `K` and
  profile `P`, with the kind's vocabulary as parameters (flow maps `fE`, `fT`, flow domain `Fl`,
  `G`-loop outputs `MO`, primitive family `KF`, path bounds `PB`), from the kind's inputs
  `RandomLayerB_Flow` (T1: the Lemma 2.8 facts of `fE`, `fT`), `RandomLayerB_Dom`,
  `RandomLayerB_Bulk` (T1', T6: flow domain `Fl` and nonempty-or-empty bulk), `RandomLayerB_Prod`
  (T2: producer of `KF` and `PB` from `h730`, `hscale`, `hell`, `hell1`, `MO`), `RandomLayerB_LL`
  (T3: `PB` gives the moment bound of `UNOULLk`), `RandomLayerB_Que` (T4: `KF`, `MO`, `PB` give
  the body of `UNOUEq747k`) and `RandomLayerB_MLout` (T5: `ML` gives `MO` along `Fl`).  Proved
  generically: the rows (`RandomLayerA`) at both scales from `Admissible` and T1, the flow
  selection (the QUE scale is modified at finitely many `n` to stay in the window
  `[N^{-1+ε}, 1]`), the quantifier and padding bookkeeping.
* `g1Rowk_band`: the band instance of `g1Rowk_of_inputs` (`UNKind.band`, `UNOUProfile.band`,
  `fE = lemE`, `fT = lemT`, `Fl = STFlow`, `MO` = `STLK ∧ STLocalEntry ∧ STExp2`,
  `KF = RandomLayerB_KFam`, `PB = GUEPathBounds (gueGridK sz 3) 3`): T1-T6 are discharged by
  `RandomLayer_lem28`, `gueK_exists` with `gueGrid_pathBounds`, `oull_of_pathBounds`,
  `Eq729B_eq747_of_inputs` and `UNMLOut` (public lemmas `RandomLayerB_*_band`).
* `g1Row : UNG1Row` (no hypothesis beyond the three inputs of the row) is
  `UNG1Rowk_band.1 g1Rowk_band`.

`n₀ = 3` is used for both scales (`gueGrid_pathBounds`: `n₀ ≥ 2`; `Eq729B_eq747_of_inputs`:
`n₀ ≥ 3`).  `UNLocAvgBand`, `UNQueBand` are not used (as the source's `G1Row`, which has only
`P7Out`, `P7ExpOut`).  Helpers that the ticket does not pin are `private` or carry the prefix
`RandomLayerB_`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

namespace RBM.Univ.GUEPhase

open MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.Gauss RBM.Gauss.Sizes RBM.Path RBM.Loop
  RBM.Univ RBM.Endpoints
open scoped NNReal ENNReal

variable {d : ℕ}

/-! ### The vocabulary of the kind's inputs (T1-T6) -/

/-- The band's primitive family `KF` on the window `[t₁, t₀]` (`n₀ = 3`, loops of length `≤ 12`): initial value `𝒦` at `t₁`,
the ODE `primRhsGUE`, and the 2-loops are `kTwoGUE` (`gueK_exists`; the fields `hKinit`, `hK`, `hK2` of
`Eq729B_eq747_of_inputs`). -/
def RandomLayerB_KFam (sz : Sizes d) (E' t1 t0 : ℕ → ℝ)
    (Kt : ∀ n, ℝ → LoopIdx (Zd d (sz.L n)) → ℂ) : Prop :=
  (∀ n {k : ℕ} (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)),
      Kt n (t1 n) (loopOf σ a) = sz.STKloop n (E' n) (t1 n) σ a) ∧
  (∀ n, ∀ s ∈ Set.Icc (t1 n) (t0 n), ∀ I : LoopIdx (Zd d (sz.L n)), I.WF → 1 ≤ I.length →
      I.length ≤ 4 * 3 →
      HasDerivWithinAt (fun u => Kt n u I) (primRhsGUE d (sz.L n) (sz.W n) (Kt n s) I)
        (Set.Icc (t1 n) (t0 n)) s) ∧
  (∀ n, ∀ s ∈ Set.Icc (t1 n) (t0 n), ∀ (σ₁ σ₂ : Bool) (a b : Zd d (sz.L n)),
      Kt n s ⟨[σ₁, σ₂], [a, b]⟩ =
        kTwoGUE d (sz.L n) (sz.W n) (sz.lam n) (mSigma (E' n)) (t1 n) s σ₁ σ₂ a b)

/-- The body of `UNOULLk` at one `n`, energy `e` and time `s`. -/
def RandomLayerB_LLAt (K : UNKind d) (sz : Sizes d) (τU : ℝ) (n : ℕ) (e s δ : ℝ) (p : ℕ) : Prop :=
  ∀ x : Idx d (sz.L n) (sz.W n),
    ∫ ω, ‖Gres (ouMatC (K.M sz) n s ω)
        ((e : ℂ) + ((ouEtaLL sz τU n : ℝ) : ℂ) * Complex.I) true x x‖ ^ (2 * p)
      ∂(ouP (K.M sz).toUNModel n) ≤ Nsz sz n ^ δ

/-- The body of `UNOUEq747k` at one `n`, energy `e`, time `s` and loss `τ`. -/
def RandomLayerB_QueAt (K : UNKind d) (P : UNOUProfile K) (sz : Sizes d) (𝔡 : ℝ) (n : ℕ)
    (e s τ : ℝ) : Prop :=
  ∀ a b : Zd d (sz.L n),
    ‖(∫ ω, avg2 sz n (fun x y => ((‖Gres (ouMatC (K.M sz) n s ω)
          ((e : ℂ) + ((ouEtaQ sz 𝔡 n : ℝ) : ℂ) * Complex.I) true x y‖ ^ 2 : ℝ) : ℂ)) a b
        ∂(ouP (K.M sz).toUNModel n)) -
      P.pm sz n (ouZeta s) ((e : ℂ) + ((ouEtaQ sz 𝔡 n : ℝ) : ℂ) * Complex.I) a b‖ ≤
        qdBoundExp sz n τ (ouEtaQ sz 𝔡 n) ∧
    ‖(∫ ω, avg2 sz n (fun x y =>
          Gres (ouMatC (K.M sz) n s ω)
            ((e : ℂ) + ((ouEtaQ sz 𝔡 n : ℝ) : ℂ) * Complex.I) true x y *
          Gres (ouMatC (K.M sz) n s ω)
            ((e : ℂ) + ((ouEtaQ sz 𝔡 n : ℝ) : ℂ) * Complex.I) true y x) a b
        ∂(ouP (K.M sz).toUNModel n)) -
      P.pp sz n (ouZeta s) ((e : ℂ) + ((ouEtaQ sz 𝔡 n : ℝ) : ℂ) * Complex.I) a b‖ ≤
        qdBoundExp sz n τ (ouEtaQ sz 𝔡 n)

/-- **T1: the flow maps and the Lemma 2.8 facts of the kind** (band: `fE = lemE`, `fT = lemT`, `c = c_κ`, from
`RandomLayer_lem28`).  For `0 < Im z ≤ 1` with `Re z` in the bulk at `n`: `|fE z| ≤ 2 - κ`, `1/16 ≤ fT z < 1`,
`η_{t₀} = √t₀ Im z` and `1 - t₀ ≤ Im z/c`. -/
def RandomLayerB_Flow (K : UNKind d) (fE fT : ∀ _ : Sizes d, ℕ → ℂ → ℝ) : Prop :=
  ∀ κ : ℝ, 0 < κ → ∃ c : ℝ, 0 < c ∧ ∀ (sz : Sizes d) (n : ℕ) (z : ℂ),
    K.bulk sz κ z.re n → 0 < z.im → z.im ≤ 1 →
      |fE sz n z| ≤ 2 - κ ∧ 1 / 16 ≤ fT sz n z ∧ fT sz n z < 1 ∧
        etaT (fE sz n z) (fT sz n z) = Real.sqrt (fT sz n z) * z.im ∧ 1 - fT sz n z ≤ z.im / c

/-- **T1': the flow domain `Fl` of the kind** (band: `Fl = STFlow`): a bulk sequence `E` with imaginary parts in
`[N^{-1+ε}, 1]` gives a flow sequence `E + iη` in `Fl sz κ ε 𝔠 𝔡`. -/
def RandomLayerB_Dom (K : UNKind d) (Fl : ∀ _ : Sizes d, ℝ → ℝ → ℝ → ℝ → (ℕ → ℂ) → Prop) : Prop :=
  ∀ (𝔠 𝔡 κ ε : ℝ) (sz : Sizes d), sz.Admissible 𝔠 𝔡 → 0 < κ → 0 < ε → ∀ E η : ℕ → ℝ,
    (∀ n, K.bulk sz κ (E n) n) → (∀ n, Nsz sz n ^ (-1 + ε) ≤ η n) → (∀ n, η n ≤ 1) →
      Fl sz κ ε 𝔠 𝔡 (fun n => (E n : ℂ) + (η n : ℂ) * Complex.I)

/-- **T6: the bulk is nonempty at every `n` or empty at every `n`** (band: `κ ≤ 2` or `κ > 2`). -/
def RandomLayerB_Bulk (K : UNKind d) : Prop :=
  ∀ (sz : Sizes d) (κ : ℝ), (∀ n, ∃ e, K.bulk sz κ e n) ∨ ∀ n e, ¬ K.bulk sz κ e n

/-- **T5: the `G`-loop outputs `MO` of the kind along its flow domain `Fl`** (`ML` gives `MO sz z t` at every time
sequence `0 ≤ t_n ≤ fT z_n`; band: `Fl = STFlow`, `MO = RandomLayerB_MOband` = three of the five conclusions of
`UNMLOut`). -/
def RandomLayerB_MLout (fT : ∀ _ : Sizes d, ℕ → ℂ → ℝ)
    (Fl : ∀ _ : Sizes d, ℝ → ℝ → ℝ → ℝ → (ℕ → ℂ) → Prop)
    (MO : ∀ _ : Sizes d, (ℕ → ℂ) → (ℕ → ℝ) → Prop) : Prop :=
  ∀ κ ε 𝔡 𝔠 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ (sz : Sizes d) (z : ℕ → ℂ), Fl sz κ ε 𝔠 𝔡 z →
    ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ fT sz n (z n)) → MO sz z t

/-- **T2: the producer of the primitive family `KF` and of the path bounds `PB`** (band: `gueK_exists` and
`gueGrid_pathBounds`, `KF = RandomLayerB_KFam`, `PB = GUEPathBounds (gueGridK sz 3) 3`): from the flow data
`E' = fE z_n`, `t₀ = fT z_n`, `t₁`, `h730`, `hscale`, `hell`, `hell1` and the `G`-loop outputs `MO sz z t₁`. -/
def RandomLayerB_Prod (fE fT : ∀ _ : Sizes d, ℕ → ℂ → ℝ)
    (MO : ∀ _ : Sizes d, (ℕ → ℂ) → (ℕ → ℝ) → Prop)
    (KF PB : ∀ sz : Sizes d, (ℕ → ℝ) → (ℕ → ℝ) → (ℕ → ℝ) →
      (∀ n, ℝ → LoopIdx (Zd d (sz.L n)) → ℂ) → Prop) : Prop :=
  ∀ (𝔠 𝔡 κ τD : ℝ) (sz : Sizes d), sz.Admissible 𝔠 𝔡 → 0 < κ → 0 < τD → ∀ (z : ℕ → ℂ) (t1 : ℕ → ℝ),
    (∀ n, |fE sz n (z n)| ≤ 2 - κ) → (∀ n, 0 ≤ t1 n) → (∀ n, t1 n ≤ fT sz n (z n)) →
    (∀ n, fT sz n (z n) < 1) →
    (∀ᶠ n in atTop, fT sz n (z n) - t1 n ≤
      Nsz sz n ^ (-τD) * etaT (fE sz n (z n)) (fT sz n (z n))) →
    (∀ᶠ n in atTop, (gueScale sz (fun n => fE sz n (z n)) n (fT sz n (z n)))⁻¹ ≤ Nsz sz n ^ (-τD)) →
    (∀ᶠ n in atTop, ((sz.L n : ℕ) : ℝ) ^ d * (1 - t1 n) ≤ sz.lam n ^ 2) →
    (∀ᶠ n in atTop, ((sz.L n : ℕ) : ℝ) ^ d * (1 - t1 n) ≤ 1) →
    MO sz z t1 →
    ∃ Kt : ∀ n, ℝ → LoopIdx (Zd d (sz.L n)) → ℂ,
      KF sz (fun n => fE sz n (z n)) t1 (fun n => fT sz n (z n)) Kt ∧
        PB sz (fun n => fE sz n (z n)) t1 (fun n => fT sz n (z n)) Kt

/-- **T3: the `OULL` transfer** (band: `oull_of_pathBounds`): `PB` at the flow `E' = fE z_n`, `t₀ = fT z_n`,
`t₁ = (1 - ζ(t_n)) t₀`, `z_n = E_n + i η_LL` gives the moment bound of `UNOULLk`. -/
def RandomLayerB_LL (K : UNKind d) (fE fT : ∀ _ : Sizes d, ℕ → ℂ → ℝ)
    (PB : ∀ sz : Sizes d, (ℕ → ℝ) → (ℕ → ℝ) → (ℕ → ℝ) →
      (∀ n, ℝ → LoopIdx (Zd d (sz.L n)) → ℂ) → Prop) : Prop :=
  ∀ (𝔠 𝔡 κ τU : ℝ) (sz : Sizes d), sz.Admissible 𝔠 𝔡 → 0 < κ → 0 < τU → τU < 1 / 2 →
    ∀ E t : ℕ → ℝ, (∀ n, K.bulk sz κ (E n) n) → (∀ n, 0 ≤ t n) →
      ∀ Kt, PB sz (fun n => fE sz n ((E n : ℂ) + ((ouEtaLL sz τU n : ℝ) : ℂ) * Complex.I))
          (fun n => (1 - ouZeta (t n)) *
            fT sz n ((E n : ℂ) + ((ouEtaLL sz τU n : ℝ) : ℂ) * Complex.I))
          (fun n => fT sz n ((E n : ℂ) + ((ouEtaLL sz τU n : ℝ) : ℂ) * Complex.I)) Kt →
        ∀ δ : ℝ, 0 < δ → ∀ p : ℕ, ∀ᶠ n in atTop, RandomLayerB_LLAt K sz τU n (E n) (t n) δ p

/-- **T4: the target-3 form of `Eq729B`** (band: `Eq729B_eq747_of_inputs`): a flow sequence `z` with
`z_n = E_n + i η_Q` eventually, the flow data `E' = fE z_n`, `t₀ = fT z_n`, `t₁ = (1 - ζ(t_n)) t₀` with
`|E'| ≤ 2 - κ`, `0 ≤ t₁ ≤ t₀ < 1` at every `n`, the primitive family `KF`, the `G`-loop outputs `MO sz z t₁` and
`PB` give the body of `UNOUEq747k` for every loss `τ > 0`. -/
def RandomLayerB_Que (K : UNKind d) (P : UNOUProfile K) (fE fT : ∀ _ : Sizes d, ℕ → ℂ → ℝ)
    (MO : ∀ _ : Sizes d, (ℕ → ℂ) → (ℕ → ℝ) → Prop)
    (KF PB : ∀ sz : Sizes d, (ℕ → ℝ) → (ℕ → ℝ) → (ℕ → ℝ) →
      (∀ n, ℝ → LoopIdx (Zd d (sz.L n)) → ℂ) → Prop) : Prop :=
  ∀ (𝔠 𝔡 κ τU : ℝ) (sz : Sizes d), sz.Admissible 𝔠 𝔡 → 0 < κ → 0 < τU → τU ≤ ouTauMax 𝔠 𝔡 →
    ∀ E t : ℕ → ℝ, (∀ n, K.bulk sz κ (E n) n) → (∀ n, 0 ≤ t n ∧ t n ≤ ouTStar sz τU n) →
      ∀ z : ℕ → ℂ, (∀ᶠ n in atTop, z n = (E n : ℂ) + ((ouEtaQ sz 𝔡 n : ℝ) : ℂ) * Complex.I) →
        (∀ n, |fE sz n (z n)| ≤ 2 - κ ∧ 0 ≤ (1 - ouZeta (t n)) * fT sz n (z n) ∧
          (1 - ouZeta (t n)) * fT sz n (z n) ≤ fT sz n (z n) ∧ fT sz n (z n) < 1) →
        ∀ Kt, KF sz (fun n => fE sz n (z n)) (fun n => (1 - ouZeta (t n)) * fT sz n (z n))
            (fun n => fT sz n (z n)) Kt →
          MO sz z (fun n => (1 - ouZeta (t n)) * fT sz n (z n)) →
          PB sz (fun n => fE sz n (z n)) (fun n => (1 - ouZeta (t n)) * fT sz n (z n))
            (fun n => fT sz n (z n)) Kt →
          ∀ τ : ℝ, 0 < τ → ∀ᶠ n in atTop, RandomLayerB_QueAt K P sz 𝔡 n (E n) (t n) τ

/-! ### Padding -/

/-- From the sequences in the bulk at every `n` to arbitrary sequences with the bulk condition inside `∀ᶠ`
(T6: the bulk is nonempty at every `n`, or empty at every `n`). -/
private theorem RandomLayerB_pad {K : UNKind d} {sz : Sizes d} {κ : ℝ}
    (hb : (∀ n, ∃ e, K.bulk sz κ e n) ∨ ∀ n e, ¬ K.bulk sz κ e n) (Q : ℕ → ℝ → Prop)
    (h : ∀ E : ℕ → ℝ, (∀ n, K.bulk sz κ (E n) n) → ∀ᶠ n in atTop, Q n (E n)) (E : ℕ → ℝ) :
    ∀ᶠ n in atTop, K.bulk sz κ (E n) n → Q n (E n) := by
  classical
  rcases hb with hne | hemp
  · set E' : ℕ → ℝ := fun n => if K.bulk sz κ (E n) n then E n else (hne n).choose with hE'
    have hE'b : ∀ n, K.bulk sz κ (E' n) n := fun n => by
      by_cases hn : K.bulk sz κ (E n) n
      · simp only [hE', hn, ↓reduceIte]
      · simp only [hE', hn, ↓reduceIte]; exact (hne n).choose_spec
    filter_upwards [h E' hE'b] with n hn hb
    have : E' n = E n := by simp only [hE', hb, ↓reduceIte]
    rwa [this] at hn
  · exact Eventually.of_forall fun n hn => absurd hn (hemp n _)

/-! ### One sequence, kind-generic -/

/-- **The moment bound of `UNOULLk` along one bulk sequence** (T1, T1', T2, T3, T5 and the rows at `η_LL`). -/
private theorem RandomLayerB_oull_seq {K : UNKind d} {fE fT : ∀ _ : Sizes d, ℕ → ℂ → ℝ}
    {Fl : ∀ _ : Sizes d, ℝ → ℝ → ℝ → ℝ → (ℕ → ℂ) → Prop} {MO : ∀ _ : Sizes d, (ℕ → ℂ) → (ℕ → ℝ) → Prop}
    {KF PB : ∀ sz : Sizes d, (ℕ → ℝ) → (ℕ → ℝ) → (ℕ → ℝ) →
      (∀ n, ℝ → LoopIdx (Zd d (sz.L n)) → ℂ) → Prop} (hd : 3 ≤ d)
    (h1 : RandomLayerB_Flow K fE fT) (hdom : RandomLayerB_Dom K Fl) (h2 : RandomLayerB_Prod fE fT MO KF PB)
    (h3 : RandomLayerB_LL K fE fT PB) (h5 : RandomLayerB_MLout fT Fl MO) {𝔠 𝔡 : ℝ} {sz : Sizes d}
    (hA : sz.Admissible 𝔠 𝔡) {τU : ℝ} (hτU : 0 < τU) (hτUm : τU ≤ ouTauMax 𝔠 𝔡) {κ : ℝ} (hκ : 0 < κ)
    {E t : ℕ → ℝ} (hE : ∀ n, K.bulk sz κ (E n) n) (ht : ∀ n, 0 ≤ t n ∧ t n ≤ ouTStar sz τU n)
    (δ : ℝ) (hδ : 0 < δ) (p : ℕ) : ∀ᶠ n in atTop, RandomLayerB_LLAt K sz τU n (E n) (t n) δ p := by
  obtain ⟨c, hc, hF⟩ := h1 κ hκ
  have hτ1 : τU ≤ 1 / 100 := hτUm.trans (min_le_right _ _)
  have hη0 := RandomLayer_etaLL_pos sz τU
  have hη1 := RandomLayer_etaLL_le_one sz (by linarith : τU ≤ 1 / 2)
  set z : ℕ → ℂ := fun n => (E n : ℂ) + ((ouEtaLL sz τU n : ℝ) : ℂ) * Complex.I with hz
  have hzre : ∀ n, (z n).re = E n := fun n => by simp [hz]
  have hzim : ∀ n, (z n).im = ouEtaLL sz τU n := fun n => by simp [hz]
  have F := fun n => hF sz n (z n) (by rw [hzre]; exact hE n) (by rw [hzim]; exact hη0 n)
    (by rw [hzim]; exact hη1 n)
  obtain ⟨r1, r2, r3, r4⟩ := RandomLayer_rowsLL sz hd hA hτU hτUm hc (t := t) (fun n => (ht n).2)
  obtain ⟨hnn, hle, h730, hscale, hell, hell1⟩ := RandomLayer_rows_flow sz (c := c) (τD := τU / 2) (t := t)
    (t0 := fun n => fT sz n (z n)) (η := ouEtaLL sz τU) (E' := fun n => fE sz n (z n))
    (fun n => (ht n).1) hη0 (fun n => (F n).2.1) (fun n => (F n).2.2.1)
    (fun n => by rw [(F n).2.2.2.1, hzim]) (fun n => by have := (F n).2.2.2.2; rwa [hzim] at this)
    r1 r2 r3 r4
  have hflow : Fl sz κ (2 * τU) 𝔠 𝔡 z :=
    hdom 𝔠 𝔡 κ (2 * τU) sz hA hκ (by linarith) E (ouEtaLL sz τU) hE (fun _ => le_rfl) hη1
  have hMO := h5 κ (2 * τU) 𝔡 𝔠 hκ (by linarith) hA.2.1 sz z hflow
    (fun n => (1 - ouZeta (t n)) * fT sz n (z n)) hnn hle
  obtain ⟨Kt, -, hPB⟩ := h2 𝔠 𝔡 κ (τU / 2) sz hA hκ (by positivity) z
    (fun n => (1 - ouZeta (t n)) * fT sz n (z n)) (fun n => (F n).1) hnn hle
    (fun n => (F n).2.2.1) h730 hscale hell hell1 hMO
  exact h3 𝔠 𝔡 κ τU sz hA hκ hτU (by linarith) E t hE (fun n => (ht n).1) Kt hPB δ hδ p

/-- **The body of `UNOUEq747k` along one bulk sequence** (T1, T1', T2, T4, T5 and the rows at `η_Q`): `z_n = E_n + i η_Q`
is replaced, at the finitely many `n` where `η_Q ∉ [N^{-1+ε}, 1]`, by `E_n + i N^{-1+ε}` (`STFlow` needs
`locDomain` at every `n`; `ε = min(𝔠(𝔡 - 𝔡/3), 1)`). -/
private theorem RandomLayerB_eq747_seq {K : UNKind d} {P : UNOUProfile K}
    {fE fT : ∀ _ : Sizes d, ℕ → ℂ → ℝ}
    {Fl : ∀ _ : Sizes d, ℝ → ℝ → ℝ → ℝ → (ℕ → ℂ) → Prop} {MO : ∀ _ : Sizes d, (ℕ → ℂ) → (ℕ → ℝ) → Prop}
    {KF PB : ∀ sz : Sizes d, (ℕ → ℝ) → (ℕ → ℝ) → (ℕ → ℝ) →
      (∀ n, ℝ → LoopIdx (Zd d (sz.L n)) → ℂ) → Prop} (hd : 3 ≤ d)
    (h1 : RandomLayerB_Flow K fE fT) (hdom : RandomLayerB_Dom K Fl) (h2 : RandomLayerB_Prod fE fT MO KF PB)
    (h4 : RandomLayerB_Que K P fE fT MO KF PB) (h5 : RandomLayerB_MLout fT Fl MO) {𝔠 𝔡 : ℝ} {sz : Sizes d}
    (hA : sz.Admissible 𝔠 𝔡) {τU : ℝ} (hτU : 0 < τU) (hτUm : τU ≤ ouTauMax 𝔠 𝔡) {κ : ℝ} (hκ : 0 < κ)
    {E t : ℕ → ℝ} (hE : ∀ n, K.bulk sz κ (E n) n) (ht : ∀ n, 0 ≤ t n ∧ t n ≤ ouTStar sz τU n)
    (τ : ℝ) (hτ : 0 < τ) : ∀ᶠ n in atTop, RandomLayerB_QueAt K P sz 𝔡 n (E n) (t n) τ := by
  classical
  obtain ⟨c, hc, hF⟩ := h1 κ hκ
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
  obtain ⟨hnn, hle, h730, hscale, hell, hell1⟩ := RandomLayer_rows_flow sz (c := c) (τD := τU) (t := t)
    (t0 := fun n => fT sz n (z n)) (η := η') (E' := fun n => fE sz n (z n))
    (fun n => (ht n).1) hη'0 (fun n => (F n).2.1) (fun n => (F n).2.2.1)
    (fun n => by rw [(F n).2.2.2.1, hzim]) (fun n => by have := (F n).2.2.2.2; rwa [hzim] at this)
    (by filter_upwards [q1, hev] with n h he; rw [he]; exact h)
    (by filter_upwards [q2, hev] with n h he; rw [he]; exact h)
    (by filter_upwards [q3, hev] with n h he; rw [he]; exact h)
    (by filter_upwards [q4, hev] with n h he; rw [he]; exact h)
  have hflow : Fl sz κ ε 𝔠 𝔡 z :=
    hdom 𝔠 𝔡 κ ε sz hA hκ hε0 E η' hE (fun n => (hη'1 n).1) (fun n => (hη'1 n).2)
  have hMO := h5 κ ε 𝔡 𝔠 hκ hε0 h𝔡 sz z hflow
    (fun n => (1 - ouZeta (t n)) * fT sz n (z n)) hnn hle
  have hgood : ∀ n, |fE sz n (z n)| ≤ 2 - κ ∧ 0 ≤ (1 - ouZeta (t n)) * fT sz n (z n) ∧
      (1 - ouZeta (t n)) * fT sz n (z n) ≤ fT sz n (z n) ∧ fT sz n (z n) < 1 :=
    fun n => ⟨(F n).1, hnn n, hle n, (F n).2.2.1⟩
  obtain ⟨Kt, hKF, hPB⟩ := h2 𝔠 𝔡 κ τU sz hA hκ hτU z
    (fun n => (1 - ouZeta (t n)) * fT sz n (z n)) (fun n => (F n).1) hnn hle
    (fun n => (F n).2.2.1) h730 hscale hell hell1 hMO
  have hzQ : ∀ᶠ n in atTop, z n = (E n : ℂ) + ((ouEtaQ sz 𝔡 n : ℝ) : ℂ) * Complex.I :=
    hev.mono fun n hn => by simp only [hz, hn]
  exact h4 𝔠 𝔡 κ τU sz hA hκ hτU hτUm E t hE ht z hzQ hgood Kt hKF hMO hPB τ hτ

/-! ### The kind-generic target -/

/-- **`g1Rowk_of_inputs` (UN-51, U1)**: `UNG1Rowk K P ML Loc Que` for every kind `K` and profile `P`, from the kind's
inputs T1-T6 (`RandomLayerB_Flow`, `RandomLayerB_Dom`, `RandomLayerB_Bulk`, `RandomLayerB_Prod`,
`RandomLayerB_LL`, `RandomLayerB_Que`, `RandomLayerB_MLout`).  The kind's vocabulary is a parameter: flow maps
`fE`, `fT`, flow domain `Fl`, `G`-loop outputs `MO`, primitive family `KF`, path bounds `PB`.  `Loc`, `Que` are
not used.  `n₀ = 3` for both scales. -/
theorem g1Rowk_of_inputs (K : ∀ d, UNKind d) (P : ∀ d, UNOUProfile (K d)) {ML Loc Que : Prop}
    (fE fT : ∀ d : ℕ, ∀ _ : Sizes d, ℕ → ℂ → ℝ)
    (Fl : ∀ d : ℕ, ∀ _ : Sizes d, ℝ → ℝ → ℝ → ℝ → (ℕ → ℂ) → Prop)
    (MO : ∀ d : ℕ, ∀ _ : Sizes d, (ℕ → ℂ) → (ℕ → ℝ) → Prop)
    (KF PB : ∀ d : ℕ, ∀ sz : Sizes d, (ℕ → ℝ) → (ℕ → ℝ) → (ℕ → ℝ) →
      (∀ n, ℝ → LoopIdx (Zd d (sz.L n)) → ℂ) → Prop)
    (hT1 : ∀ d, 3 ≤ d → RandomLayerB_Flow (K d) (fE d) (fT d))
    (hT1' : ∀ d, 3 ≤ d → RandomLayerB_Dom (K d) (Fl d))
    (hT6 : ∀ d, 3 ≤ d → RandomLayerB_Bulk (K d))
    (hT2 : ∀ d, 3 ≤ d → RandomLayerB_Prod (fE d) (fT d) (MO d) (KF d) (PB d))
    (hT3 : ∀ d, 3 ≤ d → RandomLayerB_LL (K d) (fE d) (fT d) (PB d))
    (hT4 : ∀ d, 3 ≤ d → RandomLayerB_Que (K d) (P d) (fE d) (fT d) (MO d) (KF d) (PB d))
    (hT5 : ML → ∀ d, 3 ≤ d → RandomLayerB_MLout (fT d) (Fl d) (MO d)) :
    UNG1Rowk K P ML Loc Que := by
  intro hML _ _ d hd 𝔠 𝔡 sz hA τU hτU hτUm
  refine ⟨?_, ?_⟩
  · intro κ hκ E t ht δ hδ p
    exact RandomLayerB_pad (hT6 d hd sz κ)
      (fun n e => RandomLayerB_LLAt (K d) sz τU n e (t n) δ p)
      (fun E hE => RandomLayerB_oull_seq hd (hT1 d hd) (hT1' d hd) (hT2 d hd) (hT3 d hd) (hT5 hML d hd) hA
        hτU hτUm hκ hE ht δ hδ p) E
  · intro κ hκ E t ht τ hτ
    exact RandomLayerB_pad (hT6 d hd sz κ)
      (fun n e => RandomLayerB_QueAt (K d) (P d) sz 𝔡 n e (t n) τ)
      (fun E hE => RandomLayerB_eq747_seq hd (hT1 d hd) (hT1' d hd) (hT2 d hd) (hT4 d hd) (hT5 hML d hd) hA
        hτU hτUm hκ hE ht τ hτ) E

/-! ### The band instance: T1-T6 are discharged by the merged lemmas -/

/-- The path bounds of the band: `GUEPathBounds` on the grid `gueGridK sz 3`, `n₀ = 3`. -/
def RandomLayerB_PBband (sz : Sizes d) (E' t1 t0 : ℕ → ℝ)
    (Kt : ∀ n, ℝ → LoopIdx (Zd d (sz.L n)) → ℂ) : Prop :=
  GUEPathBounds sz E' t1 t0 (gueGridK sz 3) 3 Kt

/-- T1 at the band: `fE = lemE`, `fT = lemT`, `c = c_κ = √(κ(4-κ))/8` (`RandomLayer_lem28`). -/
theorem RandomLayerB_flow_band :
    RandomLayerB_Flow (UNKind.band d) (fun _ _ z => lemE z) (fun _ _ z => lemT z) := by
  intro κ hκ
  by_cases hκ2 : κ ≤ 2
  · refine ⟨Real.sqrt (κ * (4 - κ)) / 8, div_pos (Real.sqrt_pos.2 (mul_pos hκ (by linarith))) (by norm_num),
      fun sz n z hb hz0 hz1 => ?_⟩
    have hb' : |z.re| ≤ 2 - κ := hb
    obtain ⟨-, h2, h3, h4, h5, -, -, h8⟩ := RandomLayer_lem28 (κ := κ) (e := z.re) (η := z.im) hκ hb'
      hz0 hz1 (z := z) (Complex.re_add_im z).symm
    exact ⟨h2, h3, h4, h5, h8⟩
  · exact ⟨1, one_pos, fun sz n z hb => by
      exfalso
      have hb' : |z.re| ≤ 2 - κ := hb
      linarith [abs_nonneg z.re]⟩

/-- The flow domain of the band: `Fl = STFlow`. -/
def RandomLayerB_Flband (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ) : Prop :=
  STFlow sz κ ε 𝔠 𝔡 z

/-- The `G`-loop outputs of the band at the flow `z` (`E' = lemE z_n`): `STLK`, `STLocalEntry`, `STExp2`. -/
def RandomLayerB_MOband (sz : Sizes d) (z : ℕ → ℂ) (t : ℕ → ℝ) : Prop :=
  sz.STLK (fun n => lemE (z n)) t ∧ sz.STLocalEntry (fun n => lemE (z n)) t ∧
    sz.STExp2 (fun n => lemE (z n)) t

/-- T1' at the band (`Fl = STFlow`). -/
theorem RandomLayerB_dom_band : RandomLayerB_Dom (UNKind.band d) (RandomLayerB_Flband (d := d)) := by
  intro 𝔠 𝔡 κ ε sz hA _ _ E η hb h1 h2
  refine ⟨hA, fun n => ?_⟩
  have hb' : |E n| ≤ 2 - κ := hb n
  exact ⟨by simpa using hb', by simpa using h1 n, by simpa using h2 n⟩

/-- T6 at the band: `κ ≤ 2` (`e = 0`) or `κ > 2`. -/
theorem RandomLayerB_bulk_band : RandomLayerB_Bulk (UNKind.band d) := by
  intro sz κ
  by_cases hκ : κ ≤ 2
  · exact Or.inl fun n => ⟨0, by change |(0 : ℝ)| ≤ 2 - κ; simp; linarith⟩
  · refine Or.inr fun n e he => ?_
    have he' : |e| ≤ 2 - κ := he
    linarith [abs_nonneg e]

/-- T5 at the band: three of the five conclusions of `UNMLOut`. -/
theorem RandomLayerB_ML_band (hML : ∀ d : ℕ, UNMLOut d) (hd : 3 ≤ d) :
    RandomLayerB_MLout (d := d) (fun _ _ z => lemT z) RandomLayerB_Flband RandomLayerB_MOband := by
  intro κ ε 𝔡 𝔠 hκ hε h𝔡 sz z hflow t ht0 ht
  obtain ⟨h1, -, -, h4, h5⟩ := hML d hd κ ε 𝔡 𝔠 hκ hε h𝔡 sz z hflow t ht0 ht
  exact ⟨h1, h5, h4⟩

/-- T2 at the band: `gueK_exists` at every `n` and `gueGrid_pathBounds` (`n₀ = 3`, `STKbound` from
`stKbound_holds`). -/
theorem RandomLayerB_prod_band (hd : 3 ≤ d) :
    RandomLayerB_Prod (fun _ _ z => lemE z) (fun _ _ z => lemT z) RandomLayerB_MOband
      (RandomLayerB_KFam (d := d)) (RandomLayerB_PBband (d := d)) := by
  intro 𝔠 𝔡 κ τD sz hA hκ hτD z t1 hE ht1 ht10 ht0 h730 hscale hell hell1 hMO
  obtain ⟨hLK, hLoc, -⟩ := hMO
  set E' : ℕ → ℝ := fun n => lemE (z n) with hE'd
  set t0 : ℕ → ℝ := fun n => lemT (z n) with ht0d
  change ∀ n, |E' n| ≤ 2 - κ at hE
  change ∀ n, t1 n ≤ t0 n at ht10
  change ∀ n, t0 n < 1 at ht0
  have hlam : ∀ᶠ n in atTop, 0 < sz.lam n ∧ sz.lam n ≤ 𝔡⁻¹ := by
    filter_upwards [hA.2.2.2.2] with n hn
    exact ⟨lt_of_lt_of_le (Real.rpow_pos_of_pos (by exact_mod_cast sz.W_pos n) _) hn.1, hn.2⟩
  have hKb := Sizes.stKbound_holds sz hd hκ (inv_pos.2 hA.2.1) hA.2.2.1
    (Eventually.of_forall fun n => hE n) hlam
  choose Kt h1 h2 h3 using fun n => gueK_exists d (sz.L n) (sz.W n) (sz.three_le_L n) (sz.lam n)
    (E := E' n) (by linarith [hE n, abs_nonneg (E' n)] : |E' n| < 2) (ht1 n) (ht10 n) (ht0 n) (4 * 3)
  have hKinit : ∀ n {k : ℕ} (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)),
      Kt n (t1 n) (loopOf σ a) = sz.STKloop n (E' n) (t1 n) σ a := fun n k σ a => h1 n _
  have hK : ∀ n, ∀ s ∈ Set.Icc (t1 n) (t0 n), ∀ I : LoopIdx (Zd d (sz.L n)), I.WF → 1 ≤ I.length →
      I.length ≤ 4 * 3 → HasDerivWithinAt (fun u => Kt n u I)
        (primRhsGUE d (sz.L n) (sz.W n) (Kt n s) I) (Set.Icc (t1 n) (t0 n)) s :=
    fun n s hs I hI h hl => h2 n s hs I hI h hl
  exact ⟨Kt, ⟨hKinit, hK, h3⟩, gueGrid_pathBounds sz hd hA hκ hτD 3 (by norm_num) hE ht1 ht10 ht0 h730
    hscale hell hell1 hKb Kt hKinit hK hLK hLoc⟩

/-- T3 at the band: `oull_of_pathBounds` (`ouMatC (UNModel.band sz).toC = ouMat (UNModel.band sz)`). -/
theorem RandomLayerB_LL_band :
    RandomLayerB_LL (UNKind.band d) (fun _ _ z => lemE z) (fun _ _ z => lemT z)
      (RandomLayerB_PBband (d := d)) := by
  intro 𝔠 𝔡 κ τU sz hA hκ hτU hτU1 E t hE ht Kt hP δ hδ p
  have h := oull_of_pathBounds sz (κ := κ) hκ hτU hτU1 3 (by norm_num) (Sizes.tendsto_size sz hA.2.2.1)
    (E := E) (t := t) (fun n => hE n) ht Kt hP δ hδ p
  filter_upwards [h] with n hn
  unfold RandomLayerB_LLAt
  rw [unPinsK_band_M, ouMatC_toC]
  exact hn

/-- T4 at the band: `Eq729B_eq747_of_inputs` (`n₀ = 3`). -/
theorem RandomLayerB_Que_band (hd : 3 ≤ d) :
    RandomLayerB_Que (UNKind.band d) (UNOUProfile.band d) (fun _ _ z => lemE z) (fun _ _ z => lemT z)
      RandomLayerB_MOband (RandomLayerB_KFam (d := d)) (RandomLayerB_PBband (d := d)) := by
  intro 𝔠 𝔡 κ τU sz hA hκ hτU hτUm E t hE ht z hz hgood Kt hKF hMO hPB τ hτ
  have h := Eq729B_eq747_of_inputs sz hd hA hκ hτU hτUm 3 (le_refl 3) (E := E) (t := t) hE ht
    (E' := fun n => lemE (z n)) (t0 := fun n => lemT (z n)) (t1 := fun n => (1 - ouZeta (t n)) * lemT (z n))
    ⟨hz.mono fun n hn => by simp only [hn]; rfl, hz.mono fun n hn => by simp only [hn]; rfl,
      Eventually.of_forall fun n => rfl⟩
    hgood Kt hKF.1 hKF.2.1 hKF.2.2 hMO.2.2 hPB τ hτ
  filter_upwards [h] with n hn
  unfold RandomLayerB_QueAt
  rw [unPinsK_band_M, ouMatC_toC]
  exact hn

/-- **`g1Rowk_band`**: the band instance of `g1Rowk_of_inputs` (every input T1-T6 discharged). -/
theorem g1Rowk_band :
    UNG1Rowk (fun d => UNKind.band d) (fun d => UNOUProfile.band d) (∀ d : ℕ, UNMLOut d) UNLocAvgBand
      UNQueBand :=
  g1Rowk_of_inputs (fun d => UNKind.band d) (fun d => UNOUProfile.band d)
    (fun _ _ _ z => lemE z) (fun _ _ _ z => lemT z)
    (fun d => RandomLayerB_Flband (d := d)) (fun d => RandomLayerB_MOband (d := d))
    (fun d => RandomLayerB_KFam (d := d)) (fun d => RandomLayerB_PBband (d := d))
    (fun _ _ => RandomLayerB_flow_band) (fun _ _ => RandomLayerB_dom_band) (fun _ _ => RandomLayerB_bulk_band)
    (fun _ hd => RandomLayerB_prod_band hd) (fun _ _ => RandomLayerB_LL_band)
    (fun _ hd => RandomLayerB_Que_band hd) (fun hML _ hd => RandomLayerB_ML_band hML hd)

/-- **`g1Row : UNG1Row`** (UN-51, the band instance of the two layer pins; no hypothesis beyond the three inputs of
the row): `UNOULL sz τ_U` and `UNOUEq747 sz 𝔡 τ_U` for every `d ≥ 3`, `Admissible 𝔠 𝔡`, `0 < τ_U ≤ ouTauMax 𝔠 𝔡`
from `UNMLOut` (the other two inputs are not used, as the source's `G1Row`). -/
theorem g1Row : UNG1Row := UNG1Rowk_band.1 g1Rowk_band

/-! ## Compiled nonempty instance

`g1Row` has no hypothesis other than the row's three inputs; `g1Rowk_band` is the instance of
`g1Rowk_of_inputs` at the band data (T1-T6 discharged above).  Here `g1Row`, `g1Rowk_band` and
`g1Rowk_of_inputs` (at the explicit band data) at `d = 3`, `sz0`
(`L = 4(n+1)`, `W = (2(n+1))^5`, `lam = (2(n+1))^{-6}`, `n = 0`: `N = 2097152`), `𝔠 = 1/6`, `𝔡 = 1/10`,
`τ_U = ouTauMax (1/6) (1/10) = 1/720`: `UNMLOut`, `UNLocAvgBand`, `UNQueBand` (pins of other gates) stay
hypotheses. -/

namespace RandomLayerBInst

open RBM.Gauss.SizesInst

theorem inst_g1Row (hML : ∀ d : ℕ, UNMLOut d) (hLoc : UNLocAvgBand) (hQ : UNQueBand) :
    UNOULL sz0 (ouTauMax (1 / 6) (1 / 10)) ∧ UNOUEq747 sz0 (1 / 10) (ouTauMax (1 / 6) (1 / 10)) :=
  g1Row hML hLoc hQ 3 le_rfl (1 / 6) (1 / 10) sz0 sz0_admissible _
    (ouTauMax_pos (by norm_num) (by norm_num)) le_rfl

/-- `g1Rowk_band` at the same data (the kind-generic form). -/
theorem inst_g1Rowk (hML : ∀ d : ℕ, UNMLOut d) (hLoc : UNLocAvgBand) (hQ : UNQueBand) :
    UNOULLk (UNKind.band 3) sz0 (ouTauMax (1 / 6) (1 / 10)) ∧
      UNOUEq747k (UNKind.band 3) (UNOUProfile.band 3) sz0 (1 / 10) (ouTauMax (1 / 6) (1 / 10)) :=
  g1Rowk_band hML hLoc hQ 3 le_rfl (1 / 6) (1 / 10) sz0 sz0_admissible _
    (ouTauMax_pos (by norm_num) (by norm_num)) le_rfl

/-- `g1Rowk_of_inputs` at the explicit band data (`fE = lemE`, `fT = lemT`, `Fl`, `MO`, `KF`, `PB` of the band,
T1-T6 discharged by the `RandomLayerB_*_band` lemmas), at the same data. -/
theorem inst_g1Rowk_of_inputs (hML : ∀ d : ℕ, UNMLOut d) (hLoc : UNLocAvgBand) (hQ : UNQueBand) :
    UNOULLk (UNKind.band 3) sz0 (ouTauMax (1 / 6) (1 / 10)) ∧
      UNOUEq747k (UNKind.band 3) (UNOUProfile.band 3) sz0 (1 / 10) (ouTauMax (1 / 6) (1 / 10)) :=
  g1Rowk_of_inputs (fun d => UNKind.band d) (fun d => UNOUProfile.band d)
    (fun _ _ _ z => lemE z) (fun _ _ _ z => lemT z)
    (fun d => RandomLayerB_Flband (d := d)) (fun d => RandomLayerB_MOband (d := d))
    (fun d => RandomLayerB_KFam (d := d)) (fun d => RandomLayerB_PBband (d := d))
    (fun _ _ => RandomLayerB_flow_band) (fun _ _ => RandomLayerB_dom_band) (fun _ _ => RandomLayerB_bulk_band)
    (fun _ hd => RandomLayerB_prod_band hd) (fun _ _ => RandomLayerB_LL_band)
    (fun _ hd => RandomLayerB_Que_band hd) (fun hML _ hd => RandomLayerB_ML_band hML hd)
    hML hLoc hQ 3 le_rfl (1 / 6) (1 / 10) sz0 sz0_admissible _
    (ouTauMax_pos (by norm_num) (by norm_num)) le_rfl

end RandomLayerBInst

end RBM.Univ.GUEPhase

end
