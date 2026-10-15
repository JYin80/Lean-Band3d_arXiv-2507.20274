/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.BA.UNPins
import RBM3D.BA.MFixedPoint
import RBM3D.BA.MReg
import RBM3D.Propagator.Pins
import RBM3D.Endpoints

/-!
# M/N M1, row a, file 1 (T2514a): the MN1 pin texts of block Anderson, once (`BA/MAPins`)

Ticket T2514 (dispatcher V4, DECISIONS §337; supervisor `2026-10-15-0643` Q4 (a), X1-C4, MNO-C3).  Every MN1 pin text of the
block Anderson end statements is published here once; `BA/MALocal` (this ticket), M2, M3, N2 and MN-D3 read them by name.

* P1 `BAGz`, `BAMz`, `BAprof`, `BAendDom`, `BAlocBad1z`, `BAlocBad2z`, `BAqdBadz`, `BAdecolBad`: the vocabulary, the text of the
  compiled probe `t/T2449` 921369b `RBM3D/Probe/T2449Pins.lean:158-189` (never merged), law `Sizes.seqP (sz.withLam 0)`,
  ρ-bulk `BAbulk` (DECISIONS §51), matrix `sz.seqHBA`.
* P2 `BAEnd_locSCL`, `BAEnd_QDiffL`, `BAEnd_decolL`, `BAThm27L`: the end pins (probe `:192-217`).
* P3 `BAlocSCFixed`, `BAQDiffFixed`, `BAMAFixed`, `BAMANetLoc`, `BAMANetQD`, `BAMADecol`, `BAMAQUE`: the fixed-`z` and step pins
  (probe `:232-257`).
* P4, P5 `UNLocAvgBAAt`, `UNTrLocalBAAt`, `UNTrLocalInitBAAt'` (new, MNO-C3): the merged `∀ d` rows of `UNPins` cut at one `d`.
* P6 `UNLocAvgBA_iff_at`, `UNTrLocalBARow_iff_at`, `UNTrLocalInitBARow'_iff_at`: the merged rows are the `∀ d, 3 ≤ d →` closure of
  the per-`d` forms (`Iff.rfl`).

No theorem here has content: P6 is `Iff.rfl`.  The instances are `example`s at `S0` (`d = 3`); a pin that no M1 theorem concludes appears
there only as a hypothesis.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open MeasureTheory Filter Topology

noncomputable section

namespace RBM.BA

open RBM RBM.Loop RBM.Gauss RBM.Gauss.Sizes RBM.Univ RBM.Endpoints

/-! ## P1: the vocabulary (probe `:158-189`) -/

section Vocab

variable {d : ℕ} (sz : Sizes d)

/-- `G(z) = (H - z)⁻¹` of `H = V + λΨ` (T2161 `BAGz`, `Probe/T2161Pins.lean:1475`). -/
def BAGz (n : ℕ) (z : ℂ) (ω : sz.SeqΩ) : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ :=
  Gres (sz.seqHBA n ω) z true

/-- `M(z) = (λΨ - z - m(z, λ))⁻¹` on the fine lattice (T2161 `BAMz`, `:1479`, `(def_G0)`, `1_2:631`). -/
def BAMz (n : ℕ) (z : ℂ) : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ :=
  Mres ((sz.lam n : ℂ) • PsiI d (sz.L n) (sz.W n)) z (BAm d (sz.L n) (sz.lam n) z)

/-- `W^{-d} (Θ^{(σ₁,σ₂)} M^{(σ₁,σ₂)})_{ab}` of `(def:Theta_BA)` (`1_2:658-666`; T2161 `BAprof`, `:1494`). -/
def BAprof (n : ℕ) (z : ℂ) (σ₁ σ₂ : Bool) (a b : Zd d (sz.L n)) : ℂ :=
  (PropThetaQ (BAMss d (sz.L n) (BAMB d (sz.L n) (sz.lam n) z (BAm d (sz.L n) (sz.lam n) z)) σ₁ σ₂) 1 *
    BAMss d (sz.L n) (BAMB d (sz.L n) (sz.lam n) z (BAm d (sz.L n) (sz.lam n) z)) σ₁ σ₂) a b /
      ((sz.W n : ℕ) : ℂ) ^ d

/-- The end domain `𝐃^{BA}_{κ,ε}`: `Re z ∈ B_κ = {ρ_N ≥ κ}` (DECISIONS §51), `N^{-1+ε} ≤ Im z ≤ 1` (`7_8:1817`). -/
def BAendDom (κ ε : ℝ) (n : ℕ) (z : ℂ) : Prop :=
  BAbulk d (sz.L n) (sz.lam n) κ z.re ∧ Nsz sz n ^ (-1 + ε) ≤ z.im ∧ z.im ≤ 1

/-- Failure of `(G_bound)` at one `z` (the band `locBad1z`, `Endpoints.lean:114`). -/
def BAlocBad1z (τ : ℝ) (n : ℕ) (z : ℂ) (ω : sz.SeqΩ) : Prop :=
  ∃ x y : Idx d (sz.L n) (sz.W n), ((sz.W n : ℕ) : ℝ) ^ τ * calB sz n z.im (distB sz n (STblk sz n x) (STblk sz n y)) <
    ‖BAGz sz n z ω x y - BAMz sz n z x y‖ ^ 2

/-- Failure of `(G_bound_ave)` at one `z` (`locBad2z`, `Endpoints.lean:120`). -/
def BAlocBad2z (τ : ℝ) (n : ℕ) (z : ℂ) (ω : sz.SeqΩ) : Prop :=
  ∃ a : Zd d (sz.L n), ((sz.W n : ℕ) : ℝ) ^ τ * calB sz n z.im 0 <
    ‖(((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * ∑ x ∈ Iblk d (sz.L n) (sz.W n) a, BAGz sz n z ω x x - BAm d (sz.L n) (sz.lam n) z‖

/-- Failure of `(eq:diffu1)` / `(eq:diffu2)` at one `z` (`qd1Badz`, `qd2Badz`, `Endpoints.lean:125-130`), profile `(Θ M)^{(+,-)}` /
`(Θ M)^{(+,+)}`. -/
def BAqdBadz (τ : ℝ) (n : ℕ) (z : ℂ) (ω : sz.SeqΩ) (σ : Bool) : Prop :=
  ∃ a b : Zd d (sz.L n), qdBound sz n τ z.im a b <
    ‖avg2 sz n (fun x y => if σ then BAGz sz n z ω x y * BAGz sz n z ω y x else ((‖BAGz sz n z ω x y‖ ^ 2 : ℝ) : ℂ)) a b -
      BAprof sz n z true σ a b‖

/-- Failure of `(eq:psikLinfty)` (`decolBad`, `Endpoints.lean:107`) with the ρ-bulk `{ρ_N ≥ κ}` for the eigenvalue. -/
def BAdecolBad (κ τ : ℝ) (n : ℕ) (ω : sz.SeqΩ) : Prop :=
  ¬ ∀ (μ : Idx d (sz.L n) (sz.W n) → ℝ) (ψ : Idx d (sz.L n) (sz.W n) → Idx d (sz.L n) (sz.W n) → ℂ),
    IsOrthoEigenbasis (sz.seqHBA n ω) μ ψ → ∀ k, BAbulk d (sz.L n) (sz.lam n) κ (μ k) → ∀ x,
      ‖ψ k x‖ ^ 2 ≤ Nsz sz n ^ (-1 + τ)

end Vocab

/-! ## P2: the end pins (probe `:192-217`) -/

/-- **Pin `MR:locSC` for `BA`** (`1_2:653`; `(G_bound)`, `(G_bound_ave)`, `1_2:388-393`): the law-corrected, explicit-form successor
of T2161 `BAEnd_locSC` (`Probe/T2161Pins.lean:1543`, law `sz.seqP`, `Prec`).  Owner BA-M1. -/
def BAEnd_locSCL (d : ℕ) : Prop :=
  3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 → ∀ κ ε τ D : ℝ, 0 < κ → 0 < ε → 0 < τ → 0 < D →
    ∀ᶠ n in atTop,
      Sizes.seqP (sz.withLam 0) {ω | ∃ z : ℂ, BAendDom sz κ ε n z ∧ BAlocBad1z sz τ n z ω} ≤
        ENNReal.ofReal (Nsz sz n ^ (-D)) ∧
      Sizes.seqP (sz.withLam 0) {ω | ∃ z : ℂ, BAendDom sz κ ε n z ∧ BAlocBad2z sz τ n z ω} ≤
        ENNReal.ofReal (Nsz sz n ^ (-D))

/-- **Pin `MR:QuDiff` for `BA`** (`1_2:657-666`): `(eq:diffu1,2)` (union over `z`, `a`, `b` inside), `(Meq:QdS1,2)` (each `z`), profile
`(Θ M)^{(σ₁,σ₂)}`.  Owner BA-M2. -/
def BAEnd_QDiffL (d : ℕ) : Prop :=
  3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 → ∀ κ ε τ D : ℝ, 0 < κ → 0 < ε → 0 < τ → 0 < D →
    ∀ᶠ n in atTop,
      (Sizes.seqP (sz.withLam 0) {ω | ∃ z : ℂ, BAendDom sz κ ε n z ∧ BAqdBadz sz τ n z ω false} ≤
          ENNReal.ofReal (Nsz sz n ^ (-D)) ∧
        Sizes.seqP (sz.withLam 0) {ω | ∃ z : ℂ, BAendDom sz κ ε n z ∧ BAqdBadz sz τ n z ω true} ≤
          ENNReal.ofReal (Nsz sz n ^ (-D))) ∧
      ∀ z : ℂ, BAendDom sz κ ε n z → ∀ a b : Zd d (sz.L n),
        ‖(∫ ω, avg2 sz n (fun x y => ((‖BAGz sz n z ω x y‖ ^ 2 : ℝ) : ℂ)) a b ∂(Sizes.seqP (sz.withLam 0))) -
            BAprof sz n z true false a b‖ ≤ qdBoundExp sz n τ z.im ∧
        ‖(∫ ω, avg2 sz n (fun x y => BAGz sz n z ω x y * BAGz sz n z ω y x) a b ∂(Sizes.seqP (sz.withLam 0))) -
            BAprof sz n z true true a b‖ ≤ qdBoundExp sz n τ z.im

/-- **Pin `MR:decol` for `BA`** (`MR:decol_BA` bullet 1, `1_2:651`; `(eq:psikLinfty)`, `1_2:367`).  Owner BA-M3. -/
def BAEnd_decolL (d : ℕ) : Prop :=
  3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 → ∀ κ τ D : ℝ, 0 < κ → 0 < τ → 0 < D →
    ∀ᶠ n in atTop, Sizes.seqP (sz.withLam 0) {ω | BAdecolBad sz κ τ n ω} ≤ ENNReal.ofReal (Nsz sz n ^ (-D))

/-- **Theorem 2.7 (`MR:decol_BA`)**, in the order of `band_terminal` (`BandTerminal.lean:104`).  The input of MA-06b. -/
def BAThm27L (d : ℕ) : Prop :=
  BAEnd_decolL d ∧ BAEnd_locSCL d ∧ BAEnd_QUEL d ∧ BAEnd_BUnivL d ∧ BAEnd_QDiffL d

/-! ## P3: the fixed-`z` forms and the step pins (probe `:232-257`) -/

/-- Fixed-`z` form of `(G_bound)`, `(G_bound_ave)` at `BA`, `N₀` uniform over `𝐃^{BA}_{κ,ε}` (band `locSCFixed`, `FixedZ.lean:51`). -/
def BAlocSCFixed (d : ℕ) : Prop :=
  3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 → ∀ κ ε τ D : ℝ, 0 < κ → 0 < ε → 0 < τ → 0 < D →
    ∀ᶠ n in atTop, ∀ z : ℂ, BAendDom sz κ ε n z →
      Sizes.seqP (sz.withLam 0) {ω | BAlocBad1z sz τ n z ω} ≤ ENNReal.ofReal (Nsz sz n ^ (-D)) ∧
      Sizes.seqP (sz.withLam 0) {ω | BAlocBad2z sz τ n z ω} ≤ ENNReal.ofReal (Nsz sz n ^ (-D))

/-- Fixed-`z` form of `QDiff` at `BA` (band `QDiffFixed`, `FixedZ.lean:59`). -/
def BAQDiffFixed (d : ℕ) : Prop :=
  3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 → ∀ κ ε τ D : ℝ, 0 < κ → 0 < ε → 0 < τ → 0 < D →
    ∀ᶠ n in atTop, ∀ z : ℂ, BAendDom sz κ ε n z →
      (Sizes.seqP (sz.withLam 0) {ω | BAqdBadz sz τ n z ω false} ≤ ENNReal.ofReal (Nsz sz n ^ (-D)) ∧
        Sizes.seqP (sz.withLam 0) {ω | BAqdBadz sz τ n z ω true} ≤ ENNReal.ofReal (Nsz sz n ^ (-D))) ∧
      ∀ a b : Zd d (sz.L n),
        ‖(∫ ω, avg2 sz n (fun x y => ((‖BAGz sz n z ω x y‖ ^ 2 : ℝ) : ℂ)) a b ∂(Sizes.seqP (sz.withLam 0))) -
            BAprof sz n z true false a b‖ ≤ qdBoundExp sz n τ z.im ∧
        ‖(∫ ω, avg2 sz n (fun x y => BAGz sz n z ω x y * BAGz sz n z ω y x) a b ∂(Sizes.seqP (sz.withLam 0))) -
            BAprof sz n z true true a b‖ ≤ qdBoundExp sz n τ z.im

/-- M1+M2, step 1: the fixed-`z` forms from the flow outputs (band `MAFixed`, `FixedZ.lean:73`); reads conjuncts 1, 3, 4, 5 of
`UNMLOutBA`. -/
def BAMAFixed (d : ℕ) : Prop := UNMLOutBA d → BAlocSCFixed d ∧ BAQDiffFixed d

/-- M1, step 2, the `N^{-C}`-net (band `MANetLoc`, `ZNet.lean:82`). -/
def BAMANetLoc (d : ℕ) : Prop := BAlocSCFixed d → BAEnd_locSCL d

/-- M2, step 2 (band `MANetQD`, `ZNet.lean:85`). -/
def BAMANetQD (d : ℕ) : Prop := BAQDiffFixed d → BAEnd_QDiffL d

/-- M3: `decol` from `locSC` (band `MADecol`, `FixedZ.lean:787`). -/
def BAMADecol (d : ℕ) : Prop := BAEnd_locSCL d → BAEnd_decolL d

/-- M3: `QUE` from `QDiff` (band `MAQUE`, `QUEFromQDiff.lean:234`). -/
def BAMAQUE (d : ℕ) : Prop := BAEnd_QDiffL d → BAEnd_QUEL d

/-! ## P4, P5: the merged `∀ d` rows cut at one `d` (MNO-C3) -/

/-- **P4 `UNLocAvgBAAt d`** (new, MNO-C3): `UNLocAvgk` (`Universality/PinsK.lean:406-414`) at `UNKind.ba d`, after `∀ d, 3 ≤ d →`.
`(G_bound_ave)` of the block Anderson matrix, the ρ-bulk end domain, the tolerance `W^τ Bctl n (1 - Im z)`. -/
def UNLocAvgBAAt (d : ℕ) : Prop :=
  ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 →
    ∀ κ ε τ D : ℝ, 0 < κ → 0 < ε → 0 < τ → 0 < D → ∀ᶠ n in atTop,
      ((UNKind.ba d).M sz).μ {ω | ∃ z : ℂ, ((UNKind.ba d).bulk sz κ z.re n ∧ ((sz.size n : ℕ) : ℝ) ^ (-1 + ε) ≤ z.im ∧
          z.im ≤ 1) ∧ ∃ a : Zd d (sz.L n), ((sz.W n : ℕ) : ℝ) ^ τ * sz.Bctl n (1 - z.im) <
            ‖(((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * ∑ x ∈ Iblk d (sz.L n) (sz.W n) a,
                Gres (((UNKind.ba d).M sz).H n ω) z true x x - (UNKind.ba d).mdet sz n z‖} ≤
        ENNReal.ofReal (Nsz sz n ^ (-D))

/-- **P5 `UNTrLocalBAAt d`** (new, MNO-C3): `UNTrLocalBARow` (`UNPins.lean:169-174`) after `UNLocAvgBA → ∀ d, 3 ≤ d →`. -/
def UNTrLocalBAAt (d : ℕ) : Prop :=
  ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 → ∀ κ : ℝ, 0 < κ →
    ∀ E : ℝ, (∀ᶠ n in atTop, BAbulk d (sz.L n) (sz.lam n) κ E) → ∀ δ : ℝ, 0 < δ →
      (∀ x : ℝ, |x - E| ≤ δ → ∀ᶠ n in atTop, BAbulk d (sz.L n) (sz.lam n) (κ / 2) x) →
        UNTrLocal sz (UNModelC.ba sz).toUNModel (fun n => BAm d (sz.L n) (sz.lam n)) E δ

/-- **P5 `UNTrLocalInitBAAt' d`** (new, MNO-C3): `UNTrLocalInitBARow'` (`UNPins.lean:181-186`), the same cut. -/
def UNTrLocalInitBAAt' (d : ℕ) : Prop :=
  ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 → ∀ κ : ℝ, 0 < κ →
    ∀ E : ℝ, (∀ᶠ n in atTop, BAbulk d (sz.L n) (sz.lam n) κ E) → ∀ δ : ℝ, 0 < δ →
      (∀ x : ℝ, |x - E| ≤ δ → ∀ᶠ n in atTop, BAbulk d (sz.L n) (sz.lam n) (κ / 2) x) →
        UNTrLocalInit' sz (UNModelC.ba sz) (fun n => BAm d (sz.L n) (sz.lam n)) E δ

/-! ## P6: the merged rows are the closure of the per-`d` readings -/

/-- **P6a**: `UNLocAvgBA` is `∀ d, 3 ≤ d → UNLocAvgBAAt d` (`Iff.rfl`). -/
theorem UNLocAvgBA_iff_at : UNLocAvgBA ↔ ∀ d : ℕ, 3 ≤ d → UNLocAvgBAAt d := Iff.rfl

/-- **P6b**: `UNTrLocalBARow` is `UNLocAvgBA → ∀ d, 3 ≤ d → UNTrLocalBAAt d` (`Iff.rfl`). -/
theorem UNTrLocalBARow_iff_at : UNTrLocalBARow ↔ (UNLocAvgBA → ∀ d : ℕ, 3 ≤ d → UNTrLocalBAAt d) := Iff.rfl

/-- **P6c**: `UNTrLocalInitBARow'` is `UNLocAvgBA → ∀ d, 3 ≤ d → UNTrLocalInitBAAt' d` (`Iff.rfl`). -/
theorem UNTrLocalInitBARow'_iff_at :
    UNTrLocalInitBARow' ↔ (UNLocAvgBA → ∀ d : ℕ, 3 ≤ d → UNTrLocalInitBAAt' d) := Iff.rfl

/-! ## Compiled nonempty instances at `d = 3` on the class sequence `S0` (`(L, g) = (4, 3/10)`, `(𝔠, 𝔡) = (1/6, 1/10)`) -/

section Inst

open RBM.BA.UNPinsInst RBM.Univ.BAInst

private theorem MAPins_hg : (0 : ℝ) < 3 / 10 := by norm_num

/-- The five conjuncts of `BAThm27L 3` applied at `S0`, `κ_* = clsκ`, `E_* ∈` bulk (probe `:277-286`; the QUE conjunct at
`τ = 1/300`). -/
example (h : BAThm27L 3) : True := by
  have _ := h.1 le_rfl (1 / 6) (1 / 10) S0 S0_adm (clsκ 4 MAPins_hg) (1 / 10) 1 (clsκ_pos 4 MAPins_hg) (by norm_num) (by norm_num)
  have _ := h.2.1 le_rfl (1 / 6) (1 / 10) S0 S0_adm (clsκ 4 MAPins_hg) (1 / 20) (1 / 10) 2 (clsκ_pos 4 MAPins_hg) (by norm_num)
    (by norm_num) (by norm_num)
  have _ := h.2.2.1 le_rfl (1 / 6) (1 / 10) S0 S0_adm (clsκ 4 MAPins_hg) (clsκ_pos 4 MAPins_hg) (1 / 30) (1 / 60) (1 / 300)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have _ := h.2.2.2.1 le_rfl (1 / 6) (1 / 10) S0 S0_adm 1 le_rfl (clsκ 4 MAPins_hg) (clsκ_pos 4 MAPins_hg) (fp 4 MAPins_hg).E S0_bulk 0
    (by norm_num) UNInst.bump UNInst.bump_testFun
  have _ := h.2.2.2.2 le_rfl (1 / 6) (1 / 10) S0 S0_adm (clsκ 4 MAPins_hg) (1 / 20) (1 / 10) 2 (clsκ_pos 4 MAPins_hg)
    (by norm_num) (by norm_num) (by norm_num)
  trivial

/-- The fixed-`z` pins and the step pins applied at `S0` (the pins that no M1 theorem concludes are hypotheses; probe `:288-296`). -/
example (hF : BAlocSCFixed 3) (hQ : BAQDiffFixed 3) (hN : BAMANetLoc 3) (hM : BAMADecol 3) (hNQ : BAMANetQD 3)
    (hMQ : BAMAQUE 3) (hFx : BAMAFixed 3) (hML : UNMLOutBA 3) : True := by
  have _ := (hFx hML).2 le_rfl (1 / 6) (1 / 10) S0 S0_adm (clsκ 4 MAPins_hg) (1 / 20) (1 / 10) 2 (clsκ_pos 4 MAPins_hg)
    (by norm_num) (by norm_num) (by norm_num)
  have _ := hF le_rfl (1 / 6) (1 / 10) S0 S0_adm (clsκ 4 MAPins_hg) (1 / 20) (1 / 10) 2 (clsκ_pos 4 MAPins_hg)
    (by norm_num) (by norm_num) (by norm_num)
  have _ := hM (hN hF) le_rfl (1 / 6) (1 / 10) S0 S0_adm (clsκ 4 MAPins_hg) (1 / 10) 1 (clsκ_pos 4 MAPins_hg)
    (by norm_num) (by norm_num)
  have _ := hMQ (hNQ hQ) le_rfl (1 / 6) (1 / 10) S0 S0_adm (clsκ 4 MAPins_hg) (clsκ_pos 4 MAPins_hg) (1 / 30) (1 / 60) (1 / 300)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  trivial

/-- The end domain is nonempty at every `n` for the class sequence: `z = E_* + i` (merged `inst_locAvg_domain`; probe `:391`). -/
example : ∀ n, ∃ z : ℂ, BAendDom S0 (clsκ 4 MAPins_hg) (1 / 20) n z := fun n => inst_locAvg_domain (by norm_num) n

/-- The per-`d` readings P4, P5 applied at `S0`, `κ_*`, `E_* ∈` bulk, with the window radius `δ = (π κ_*)³/8`: the window hypothesis is
discharged by the merged `BAbulk_window` (`BA/MReg.lean:122`). -/
example (hL : UNLocAvgBAAt 3) (hT : UNTrLocalBAAt 3) (hI : UNTrLocalInitBAAt' 3) : True := by
  have hδ : 0 < (Real.pi * clsκ 4 MAPins_hg) ^ 3 / 8 := by have := clsκ_pos 4 MAPins_hg; positivity
  have hwin : ∀ x : ℝ, |x - (fp 4 MAPins_hg).E| ≤ (Real.pi * clsκ 4 MAPins_hg) ^ 3 / 8 →
      ∀ᶠ n in atTop, BAbulk 3 (S0.L n) (S0.lam n) (clsκ 4 MAPins_hg / 2) x := fun x hx =>
    S0_bulk.mono fun n hn => BAbulk_window 3 (S0.L n) (S0.lam n) _ _ x (clsκ_pos 4 MAPins_hg) hn hx
  have _ := hL (1 / 6) (1 / 10) S0 S0_adm (clsκ 4 MAPins_hg) (1 / 10) (1 / 10) 1 (clsκ_pos 4 MAPins_hg) (by norm_num)
    (by norm_num) (by norm_num)
  have _ := hT (1 / 6) (1 / 10) S0 S0_adm (clsκ 4 MAPins_hg) (clsκ_pos 4 MAPins_hg) (fp 4 MAPins_hg).E S0_bulk _ hδ hwin
  have _ := hI (1 / 6) (1 / 10) S0 S0_adm (clsκ 4 MAPins_hg) (clsκ_pos 4 MAPins_hg) (fp 4 MAPins_hg).E S0_bulk _ hδ hwin
  trivial

/-- **P6** at `d = 3` on `S0`: the merged rows (hypotheses of the example, other gates' pins: `UNLocAvgBA` is `BA/MALocal`'s A7 from `∀ d`,
`UNTrLocalBARow`, `UNTrLocalInitBARow'` are row b's) read at one `d`, `κ_*`, `E_*` in the bulk, `δ = (π κ_*)³/8`; and the converse reading,
the merged `UNLocAvgBA` from its per-`d` forms. -/
example (hL : UNLocAvgBA) (hR : UNTrLocalBARow) (hI : UNTrLocalInitBARow') : True := by
  have hδ : 0 < (Real.pi * clsκ 4 MAPins_hg) ^ 3 / 8 := by have := clsκ_pos 4 MAPins_hg; positivity
  have hwin : ∀ x : ℝ, |x - (fp 4 MAPins_hg).E| ≤ (Real.pi * clsκ 4 MAPins_hg) ^ 3 / 8 →
      ∀ᶠ n in atTop, BAbulk 3 (S0.L n) (S0.lam n) (clsκ 4 MAPins_hg / 2) x := fun x hx =>
    S0_bulk.mono fun n hn => BAbulk_window 3 (S0.L n) (S0.lam n) _ _ x (clsκ_pos 4 MAPins_hg) hn hx
  have _ := (UNLocAvgBA_iff_at.1 hL) 3 le_rfl (1 / 6) (1 / 10) S0 S0_adm (clsκ 4 MAPins_hg) (1 / 10) (1 / 10) 1
    (clsκ_pos 4 MAPins_hg) (by norm_num) (by norm_num) (by norm_num)
  have _ := (UNTrLocalBARow_iff_at.1 hR hL) 3 le_rfl (1 / 6) (1 / 10) S0 S0_adm (clsκ 4 MAPins_hg) (clsκ_pos 4 MAPins_hg)
    (fp 4 MAPins_hg).E S0_bulk _ hδ hwin
  have _ := (UNTrLocalInitBARow'_iff_at.1 hI hL) 3 le_rfl (1 / 6) (1 / 10) S0 S0_adm (clsκ 4 MAPins_hg) (clsκ_pos 4 MAPins_hg)
    (fp 4 MAPins_hg).E S0_bulk _ hδ hwin
  have _ : UNLocAvgBA := UNLocAvgBA_iff_at.2 fun d hd => (UNLocAvgBA_iff_at.1 hL) d hd
  have _ : UNTrLocalBARow := UNTrLocalBARow_iff_at.2 fun h d hd => (UNTrLocalBARow_iff_at.1 hR) h d hd
  have _ : UNTrLocalInitBARow' := UNTrLocalInitBARow'_iff_at.2 fun h d hd => (UNTrLocalInitBARow'_iff_at.1 hI) h d hd
  trivial

end Inst

end RBM.BA

end
