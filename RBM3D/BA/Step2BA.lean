/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.BA.FlowPins
import RBM3D.Chain.Step2Gen

/-!
# The block Anderson Step 2 carrier (BA-T row T8-BA, ticket T2415)

Design `docs/reports/T2379-design.md` §2 (row T8), §4; supervisor
`docs/supervisor/2026-10-11-0853.md` REQ-BAT (Q1, BAT-C1).  The band instances `bandStep2Mat sz E`,
`bandStep2Data sz z` (`Chain/Step2Gen.lean:128-145`) feed every generic Step 2 statement at the
band; this file writes their block Anderson twins at the carrier `baFM` / `baFMz`
(`BA/FlowPins.lean:321-330, 393`).  No new mathematics, no drift kernel; nothing imports this file.

* `baStep2Mat sz lam0 E : Step2Mat sz`: `toFlowFM := baFM sz lam0 E`; `LM`, `GMM`, `LIM`, `KI` are
  the BA objects of a fine matrix (`BALloop`, `BAGt`/`BAMfine`, `BAKsol`, each `(BA: …)`);
  BAT-C1: `Pp := pathP (sz.withLam 0)` and `Hpath := lam0 • PsiI + pathH (sz.withLam 0)` as in
  `seqHflowBA` (`Gauss/BlockAnderson.lean:83-86`).
* `baStep2Data sz z : Step2Data sz` along `z`:
  `toStep2Mat := baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)`, `T0 := BAflowT0 sz z`,
  `flowOK := BAFlow`, and the facts `flowOK_adm`, `flowOK_T`, `L_swap` (`L_swap` reuses the private
  `Step2Gen_loopFine_swap` of `Chain/Step2Gen.lean:114` by `open private`).
* Bridges (`rfl`), among them `BAStep2 d ↔ STStep2G d … (baStep2Data …)`.
* `baStep2Fam sz E := baStep2Mat sz sz.lam E`, the energy family of the pins `STNewKLKgL`,
  `STK2decaygL` (the coupling is carried by `sz`).
* Compiled instances at `d = 3`, `sz0`, `zSeq` (`RBM3D/BA/FlowPins.lean:1181, 1214`).
-/

set_option linter.style.longLine false
set_option linter.unusedVariables false

open private Step2Gen_loopFine_swap from RBM3D.Chain.Step2Gen

noncomputable section

open MeasureTheory

namespace RBM.BA

open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes

/-! ## 1. The carrier `baStep2Mat` -/

section Mat

/-- **The block Anderson instance of `Step2Mat` at the flow parameters `(g₀, E) = (lam0, E)`** (BAT-C1; every field is a BA object):
`toFlowFM = baFM sz lam0 E`; `LM` is `BALloop` with the matrix `H` in place of `seqHflowBA`; `GMM` is `BAGM` (`G_u - M`, with
the non-scalar `M = BAMfine`); `LIM` the list-based loop of `H`; `KI` the list-indexed `(Kn2sol)` solution `BAKsol`; the law
`Pp` and the grid walk `Hpath` are those of `seqHflowBA`: `H_0 = g₀ Ψ` plus the walk of the model at coupling `0`
(`S^{(B)}(0) = I`). -/
def baStep2Mat {d : ℕ} (sz : Sizes d) (lam0 E : ℕ → ℝ) : Step2Mat sz where
  toFlowFM := baFM sz lam0 E
  -- (BA: `BALloop` of the fine matrix `H`, at `z_u = ztOf m E u`)
  LM := fun n u {_k} H σ a => loopFine d (sz.L n) (sz.W n) H (ztOf (BAmF sz lam0 E n) (E n) u) σ a
  -- (BA: `BAGt - BAMfine` of the fine matrix `H`)
  GMM := fun n u H x y => Gres H (ztOf (BAmF sz lam0 E n) (E n) u) true x y - BAMfine sz lam0 E n x y
  -- (BA: `𝓛_{u,I}` of the fine matrix `H`, at `z_u`)
  LIM := fun n u H I =>
    loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) H) (ztOf (BAmF sz lam0 E n) (E n) u) I
  -- (BA: `BAKsol`, the list-indexed solution of the convolution tree equations with `S^{(B)}(0) = I`)
  KI := fun n u I =>
    BAKsol d (sz.L n) (sz.W n) (BAMsigma d (sz.L n) (BAMB d (sz.L n) (lam0 n) (E n : ℂ) (BAmF sz lam0 E n)))
      (PropSpin (BAmF sz lam0 E n)) u I
  -- (BA: the law of the grid walk of the model at coupling `0`, `(MBM)` with `S^{(B)}(0) = I`)
  Pp := pathP (sz.withLam 0)
  -- (BA: `H_{u_k} = g₀ Ψ + pathH`, as `seqHflowBA`)
  Hpath := fun s t K n k ω =>
    ((lam0 n : ℝ) : ℂ) • PsiI d (sz.L n) (sz.W n) +
      (show Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ from pathH (sz.withLam 0) s t K n k ω)

/-- The `FlowFM` part of `baStep2Mat` is `baFM`. -/
theorem baStep2Mat_toFlowFM {d : ℕ} (sz : Sizes d) (lam0 E : ℕ → ℝ) :
    (baStep2Mat sz lam0 E).toFlowFM = baFM sz lam0 E := rfl

/-- `LM` at the flow matrix is `BALloop`. -/
theorem baStep2Mat_LM {d : ℕ} (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ) (u : ℝ) {k : ℕ} (σ : Fin k → Bool)
    (a : Fin k → Zd d (sz.L n)) (ω : sz.SeqΩ) :
    (baStep2Mat sz lam0 E).LM n u (sz.seqHflowBA lam0 n u ω) σ a = BALloop sz lam0 E n u σ a ω := rfl

/-- `GMM` at the flow matrix is `BAGM`. -/
theorem baStep2Mat_GMM {d : ℕ} (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ) (u : ℝ) (ω : sz.SeqΩ)
    (x y : Idx d (sz.L n) (sz.W n)) :
    (baStep2Mat sz lam0 E).GMM n u (sz.seqHflowBA lam0 n u ω) x y = BAGM sz lam0 E n u ω x y := rfl

/-- `KI` at a loop of the form `KLloopOf σ a` is `BAKloop`. -/
theorem baStep2Mat_KI {d : ℕ} (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ) (u : ℝ) {k : ℕ} (σ : Fin k → Bool)
    (a : Fin k → Zd d (sz.L n)) :
    (baStep2Mat sz lam0 E).KI n u (KLloopOf d (sz.L n) σ a) = BAKloop sz lam0 E n u σ a := rfl

/-- (BAT-C1) the grid walk at `s = u`, `k = 0`: `Hpath` is `g₀ Ψ + pathH` of the model at coupling `0`, the shape of `seqHflowBA`. -/
theorem baStep2Mat_Hpath {d : ℕ} (sz : Sizes d) (lam0 E : ℕ → ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ)
    (ω : PathΩ sz) :
    (baStep2Mat sz lam0 E).Hpath s t K n k ω =
      ((lam0 n : ℝ) : ℂ) • PsiI d (sz.L n) (sz.W n) +
        (show Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ from pathH (sz.withLam 0) s t K n k ω) := rfl

/-- (BAT-C1) the law of the grid walk is `pathP (sz.withLam 0)`. -/
theorem baStep2Mat_Pp {d : ℕ} (sz : Sizes d) (lam0 E : ℕ → ℝ) :
    (baStep2Mat sz lam0 E).Pp = pathP (sz.withLam 0) := rfl

end Mat

/-! ## 2. The data `baStep2Data` and its three facts -/

section Data

private theorem Step2BA_flow_im_pos {d : ℕ} {sz : Sizes d} {κ ε 𝔠 𝔡 : ℝ} {z : ℕ → ℂ}
    (h : BAFlow sz κ ε 𝔠 𝔡 z) (n : ℕ) : 0 < (z n).im := by
  have hN : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
  exact lt_of_lt_of_le (Real.rpow_pos_of_pos hN _) (h.2 n).2.1

private theorem Step2BA_T0_lt_one {d : ℕ} {sz : Sizes d} {κ ε 𝔠 𝔡 : ℝ} {z : ℕ → ℂ} (hκ : 0 < κ)
    (h : BAFlow sz κ ε 𝔠 𝔡 z) (n : ℕ) : BAflowT0 sz z n < 1 :=
  BAt0_lt_one (Step2BA_flow_im_pos h n) (lt_of_lt_of_le hκ (h.2 n).1)

/-- **The block Anderson instance of `Step2Data` along the flow `z`**: `(g₀, E) = (BAflowLam0 sz z, BAflowEs sz z)`,
`T0 = BAflowT0 sz z` (`(eq:t0E0_BA)`, `7_8:1798`), `flowOK = BAFlow`.  The facts: `flowOK_adm` is the first conjunct of
`BAFlow`; `flowOK_T` is `BAt0_lt_one` with `0 < Im z_n` (from `N^{-1+ε} ≤ Im z_n`) and `0 < Im m` (from `κ ≤ Im m` in `BAdom`);
`L_swap` is the model-free trace cyclicity `Step2Gen_loopFine_swap` (opened private, not re-proved). -/
def baStep2Data {d : ℕ} (sz : Sizes d) (z : ℕ → ℂ) : Step2Data sz where
  toStep2Mat := baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)
  T0 := BAflowT0 sz z
  flowOK := fun κ ε 𝔠 𝔡 => BAFlow sz κ ε 𝔠 𝔡 z
  flowOK_adm := fun h => h.1
  flowOK_T := fun hκ h n => Step2BA_T0_lt_one hκ h n
  L_swap := fun n t a b ω => Step2Gen_loopFine_swap _ _ a b

/-- Bridge: the carrier of `baStep2Data` is `baFMz`. -/
theorem baStep2Data_toFlowFM {d : ℕ} (sz : Sizes d) (z : ℕ → ℂ) :
    (baStep2Data sz z).toFlowFM = baFMz sz z := rfl

/-- Bridge: the horizon of `baStep2Data` is `BAflowT0`. -/
theorem baStep2Data_T0 {d : ℕ} (sz : Sizes d) (z : ℕ → ℂ) : (baStep2Data sz z).T0 = BAflowT0 sz z := rfl

/-- Bridge: the setting of `baStep2Data` is `BAFlow`. -/
theorem baStep2Data_flowOK {d : ℕ} (sz : Sizes d) (z : ℕ → ℂ) (κ ε 𝔠 𝔡 : ℝ) :
    (baStep2Data sz z).flowOK κ ε 𝔠 𝔡 = BAFlow sz κ ε 𝔠 𝔡 z := rfl

/-- **Bridge: the pin `BAStep2 d` is `STStep2G` at the data of `baStep2Data`** (`Iff.rfl`: the three projections of the explicit
structure `baStep2Data sz z` reduce to `BAFlow`, `baFMz`, `BAflowT0`). -/
theorem BAStep2_iff_STStep2G (d : ℕ) :
    BAStep2 d ↔ STStep2G d (fun sz => Sizes.seqP (sz.withLam 0))
      (fun sz κ ε 𝔠 𝔡 z => (baStep2Data sz z).flowOK κ ε 𝔠 𝔡) (fun sz z => (baStep2Data sz z).toFlowFM)
      (fun sz z => (baStep2Data sz z).T0) := Iff.rfl

end Data

/-! ## 3. The energy family -/

/-- **The energy family of the block Anderson Step 2** for the pins `STNewKLKgL d mk`, `STK2decaygL d mk` (they quantify over every
`sz` and use `mk sz (fun _ => E)`): the flow coupling `g₀` is carried by `sz`, `baStep2Fam sz E := baStep2Mat sz sz.lam E`.  At
the flow `z` apply the pin at `sz.withLam (BAflowLam0 sz z)`: there `(baStep2Fam _ E).K = (baFM sz (BAflowLam0 sz z) E).K` is `rfl`
(`baStep2Fam_K`). -/
def baStep2Fam {d : ℕ} (sz : Sizes d) (E : ℕ → ℝ) : Step2Mat sz := baStep2Mat sz sz.lam E

/-- The `𝒦` of the family at `sz.withLam lam0` is that of `baFM sz lam0 E`. -/
theorem baStep2Fam_K {d : ℕ} (sz : Sizes d) (lam0 E : ℕ → ℝ) :
    (baStep2Fam (sz.withLam lam0) E).K = (baFM sz lam0 E).K := rfl

/-- The one-loop value `m` of the family at the constant sequence is `BAm` at `(L_n, g_n, E)` (the datum `κ ≤ Im m` of the primed pins). -/
theorem baStep2Fam_m {d : ℕ} (sz : Sizes d) (E : ℝ) (n : ℕ) :
    (baStep2Fam sz (fun _ => E)).m n = BAm d (sz.L n) (sz.lam n) (E : ℂ) := rfl

/-- The pin hypotheses `0 < lam n`, `lam n ≤ 𝔡⁻¹` of `STNewKLKgL`, `STK2decaygL` at the flow coupling: if `0 < g_n` then
`0 < g₀_n ≤ g_n` for `sz.withLam (BAflowLam0 sz z)` (`g₀ = √t₀ g`, `0 < t₀ < 1`; `WO` gives `0 < g_n ≤ 𝔡⁻¹` only eventually
in `n`, so the pins apply at the `n` where `g_n` is in range). -/
theorem baStep2Fam_lam_pos_le {d : ℕ} {sz : Sizes d} {κ ε 𝔠 𝔡 : ℝ} {z : ℕ → ℂ} (hκ : 0 < κ)
    (h : BAFlow sz κ ε 𝔠 𝔡 z) (n : ℕ) (hg : 0 < sz.lam n) :
    0 < (sz.withLam (BAflowLam0 sz z)).lam n ∧ (sz.withLam (BAflowLam0 sz z)).lam n ≤ sz.lam n :=
  ⟨mul_pos (Real.sqrt_pos.mpr (BAt0_pos (Step2BA_flow_im_pos h n) (lt_of_lt_of_le hκ (h.2 n).1))) hg,
    BAg0_le hg.le (Step2BA_flow_im_pos h n) (lt_of_lt_of_le hκ (h.2 n).1)⟩

/-! ## 4. Compiled nonempty instances at `d = 3` -/

namespace Step2BAInst

open RBM.Gauss.SizesInst RBM.BA.FlowPinsInst

/-- Instance of the setting: `flowOK` of `baStep2Data` holds along `sz0`, `zSeq` at `(1/2, 1/10, 1/6, 1/10)` (`n = 0`:
`L = 4`, `W = 32`, `g = 1/64`, `Im z_0 ≈ 0.3675`, `Im m ≈ 0.8325`; `flow_sz0` proves every conjunct). -/
example : (baStep2Data sz0 zSeq).flowOK (1 / 2) (1 / 10) (1 / 6) (1 / 10) := flow_sz0

/-- Instance of `flowOK_T`: `T0 n < 1` for every `n` through the field `flowOK_T` of the data. -/
example (n : ℕ) : (baStep2Data sz0 zSeq).T0 n < 1 :=
  (baStep2Data sz0 zSeq).flowOK_T (by norm_num) flow_sz0 n

/-- The same at `n = 0`, with `T0 0 = BAflowT0 sz0 zSeq 0` and the lower bound `2/3 ≤ t₀` of `t0_sz0`. -/
example : 2 / 3 ≤ (baStep2Data sz0 zSeq).T0 0 ∧ (baStep2Data sz0 zSeq).T0 0 < 1 :=
  ⟨t0_sz0 0, (baStep2Data sz0 zSeq).flowOK_T (by norm_num) flow_sz0 0⟩

/-- Instance of `flowOK_adm`: the sizes `sz0` are admissible at `(1/6, 1/10)`. -/
example : sz0.Admissible (1 / 6) (1 / 10) := (baStep2Data sz0 zSeq).flowOK_adm flow_sz0

/-- Instance of `L_swap` at `n = 0` (`L_0 = 4`, any `a b ω`). -/
example (a b : Zd 3 (sz0.L 0)) (ω : sz0.SeqΩ) (t : ℝ) :
    (baStep2Data sz0 zSeq).L 0 t ![true, false] ![a, b] ω = (baStep2Data sz0 zSeq).L 0 t ![false, true] ![b, a] ω :=
  (baStep2Data sz0 zSeq).L_swap 0 t a b ω

/-- Instance of `baStep2Fam_lam_pos_le`: the flow coupling `g₀_n = √t₀ g_n` of `sz0` satisfies `0 < g₀_n ≤ g_n` for every `n`. -/
example (n : ℕ) : 0 < (sz0.withLam (BAflowLam0 sz0 zSeq)).lam n ∧
    (sz0.withLam (BAflowLam0 sz0 zSeq)).lam n ≤ sz0.lam n :=
  baStep2Fam_lam_pos_le (by norm_num) flow_sz0 n (sz0_lam_pos n)

end Step2BAInst

end RBM.BA
