/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Chain.Carrier
import RBM3D.Induction.Step2Defs

/-!
# The Step 2 vocabulary over the carrier

`Induction/Step2Defs` is the band vocabulary.  This file reads each of its definitions that mentions
a band object over a carrier, and bridges the two by `rfl` / `Iff.rfl`.

* **Data.** `Step2Mat sz extends FlowFM sz` (no facts): `LM` (`𝓛^{(k)}` of a fine matrix),
  `GMM`, the list-indexed `LIM`, `KI`, the grid law `Pp` and the grid walk `Hpath`.
  `Step2Data sz extends Step2Mat sz` adds `T0`, the setting `flowOK` and three facts (`flowOK_adm`,
  `flowOK_T`, `L_swap`).
* **Names.** The band name plus the suffix g (data) or gL (a `Prop`).  A statement that quantifies over
  the flow takes the shape `(law, Flow, mk, T0)` of `STMainIndG`; the matrix-level statements take `mk`
  valued in `Step2Mat`; the energy-quantified statements `STNewKLKAt`, `STNewKLK`, `STK2decay` take a
  family `mk : ∀ sz, (ℕ → ℝ) → Step2Mat sz` read at `fun _ => E`.
* **Bridges.** `bandStep2Mat sz E`, `bandStep2Data sz z` are the band instances; every generic
  name has a bridge `bandStep2_<band name>` or `bandFM_<band name>` (`rfl` / `Iff.rfl`; the
  exceptions are `bandFM_STGijGEX` and the bridges of the drift (below), which are proved).
* **Drift kernels.** `Step2Kern_Mss` is the block kernel
  `M^{(σσ')}_{ab} = W^{-d} Σ_{x∈[a], y∈[b]} M(σ)_{yx} M(σ')_{xy}` ((2.35) `def:Theta_BA`)
  read from the field `M` of the carrier; `Step2Gen_thetaKer`, `Step2Gen_uKer`, `Step2Gen_ThetaN`,
  `Step2Gen_UN` are the drift kernels `X Θ_t(X)`, `(1 - sX) Θ_t(X)`, `X = M^{(σσ')} S`, over a
  carrier (slot `i` of a `k`-loop with the charges `(σ_i, σ_{i+1})`); `STthetaOpg`, `STgDriftNg`,
  `STeeUMg`, `STGridRepNAtgL` read them.  Band identities and the bridges: here; block Anderson
  identities: `Chain/Step2Kern`; `lem:newKLK`: `Chain/NewKLKGen`.  `STK2decaygL'` is the primed
  `K^{(2)}` decay.
* `STJhatg`, `STLWassmExpgL` are here because `STLWTgL`, `STEMn2ExpgL` read them, and this file
  cannot import `BA/FlowPins`.
-/

set_option linter.style.longLine false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.style.setOption false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal Topology Kronecker

namespace RBM.BA

open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes

/-! ## 1. The carrier of the Step 2 vocabulary -/

section Moved

variable {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (μ : Measure sz.SeqΩ)

/-- The random bound `Ĵ^ℓ_{u,D}` ((3.24) `defCALJ`): `max |(𝓛-𝒦)^{(2)}_{u,σ,a}| / [W^{-d} 𝒯̃^ℓ_{u,D}(|a₁-a₂|)]`. -/
def STJhatg (n : ℕ) (D ℓ u : ℝ) (ω : sz.SeqΩ) : ℝ :=
  Finset.univ.sup' ⟨((fun _ => true), (fun _ => 0)), Finset.mem_univ _⟩
    (fun p : (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)) =>
      ‖C.L n u p.1 p.2 ω - C.K n u p.1 p.2‖ / STprof sz n u D ℓ (p.2 0) (p.2 1))

/-- (3.31) `eq:LW_assm_exp`: `𝓛^{(2)}_{t,σ,(a,b)} ≺ W^{-d} 𝒯̃^ℓ_{t,D}(|a-b|)`, `σ ∈ {(+,-),(-,+)}`. -/
def STLWassmExpgL (t : ℕ → ℝ) (D : ℝ) (ℓ : ℕ → ℝ) : Prop :=
  PrecL sz μ (U := fun n => {σ : Fin 2 → Bool // σ 0 ≠ σ 1} × (Fin 2 → Zd d (sz.L n)))
    (fun n p ω => ‖C.L n (t n) p.1.1 p.2 ω‖)
    (fun n p _ => STprof sz n (t n) D (ℓ n) (p.2 0) (p.2 1))

end Moved

/-- `≺` per time at an arbitrary law `μ` (`PrecPT sz` is the case `μ = seqP sz`). -/
def PrecPTL {d : ℕ} (sz : Sizes d) (μ : Measure sz.SeqΩ) {U : ℕ → Type*} (ξ ζ : ∀ n, U n → sz.SeqΩ → ℝ) :
    Prop :=
  Path.PerTimeDomAt μ sz.size ξ ζ

/-- **The matrix-level data of Step 2 over `FlowFM sz`** (no facts): `𝓛^{(k)}_{u,σ,a}` of a fine matrix `H` (`LM`),
`(G_u - M)_{xy}` of `H` (`GMM`), `𝓛_{u,I}` of `H` for a list-based loop index (`LIM`) and the value `𝒦_{u,I}` (`KI`),
the law `Pp` and the walk `Hpath` of the grid walk. -/
structure Step2Mat {d : ℕ} (sz : Sizes d) extends FlowFM sz where
  /-- `𝓛^{(k)}_{u,σ,a}` of a fine matrix (band: `STLM sz n (E n) u`) -/
  LM : ∀ (n : ℕ) (u : ℝ) {k : ℕ}, Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ →
    (Fin k → Bool) → (Fin k → Zd d (sz.L n)) → ℂ
  /-- `(G_u - M)_{xy}` of a fine matrix (band: `STGMM sz n (E n) u`) -/
  GMM : ∀ (n : ℕ) (u : ℝ), Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ →
    Idx d (sz.L n) (sz.W n) → Idx d (sz.L n) (sz.W n) → ℂ
  /-- `𝓛_{u,I}` of a fine matrix, `I` a list-based loop index (band: `STLIM sz n (E n) u`) -/
  LIM : ∀ (n : ℕ) (u : ℝ), Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ →
    LoopIdx (Zd d (sz.L n)) → ℂ
  /-- `𝒦_{u,I}` (band: `KLK d (sz.L n) (sz.lam n) (sz.W n) (E n) u`) -/
  KI : ∀ (n : ℕ) (u : ℝ), LoopIdx (Zd d (sz.L n)) → ℂ
  /-- the law of the grid walk (band: `pathP sz`) -/
  Pp : Measure (PathΩ sz)
  /-- the grid walk `H_{u_k}` (band: `pathH sz`) -/
  Hpath : ∀ (s t : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ), PathΩ sz →
    Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ

/-- **The Step 2 carrier**: `Step2Mat sz` plus the end of the flow `T0`, the setting `flowOK κ ε 𝔠 𝔡` of the flow and the
three facts that the generic proofs of `Induction/LocalAvg1` and `Induction/LocalAvg2` read (admissibility, `T0 < 1`, trace cyclicity of `𝓛^{(2)}`). -/
structure Step2Data {d : ℕ} (sz : Sizes d) extends Step2Mat sz where
  /-- the end `t₀_n` of the flow (band: `lemT (z n)`) -/
  T0 : ℕ → ℝ
  /-- the setting of the flow at `(κ, ε, 𝔠, 𝔡)` (band: `STFlow sz κ ε 𝔠 𝔡 z`) -/
  flowOK : ℝ → ℝ → ℝ → ℝ → Prop
  /-- **fact**: the setting contains the admissibility of the sizes -/
  flowOK_adm : ∀ {κ ε 𝔠 𝔡 : ℝ}, flowOK κ ε 𝔠 𝔡 → sz.Admissible 𝔠 𝔡
  /-- **fact**: `t₀ < 1` (the block Anderson reading needs `0 < κ`: `Im m ≥ κ`) -/
  flowOK_T : ∀ {κ ε 𝔠 𝔡 : ℝ}, 0 < κ → flowOK κ ε 𝔠 𝔡 → ∀ n, T0 n < 1
  /-- **fact**: trace cyclicity `𝓛_{(+,-),(a,b)} = 𝓛_{(-,+),(b,a)}` -/
  L_swap : ∀ (n : ℕ) (t : ℝ) (a b : Zd d (sz.L n)) (ω : sz.SeqΩ),
    L n t ![true, false] ![a, b] ω = L n t ![false, true] ![b, a] ω

/-! ## 2. The band instance -/

section BandInst

private theorem Step2Gen_loopFine_swap {d L W : ℕ} [NeZero L] [NeZero W] (H : Matrix (Idx d L W) (Idx d L W) ℂ)
    (z : ℂ) (a b : Zd d L) :
    loopFine d L W H z ![true, false] ![a, b] = loopFine d L W H z ![false, true] ![b, a] := by
  unfold loopFine loopM
  simp only [List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, mul_one,
    Matrix.cons_val_zero, Matrix.cons_val_succ]
  exact Matrix.trace_mul_comm _ _

private theorem Step2Gen_flow_im_pos {d : ℕ} {sz : Sizes d} {κ ε 𝔠 𝔡 : ℝ} {z : ℕ → ℂ} (h : STFlow sz κ ε 𝔠 𝔡 z)
    (n : ℕ) : 0 < (z n).im := by
  have hN : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
  exact lt_of_lt_of_le (Real.rpow_pos_of_pos hN _) (h.2 n).2.1

/-- **The band instance of `Step2Mat` at the energy sequence `E`** (every field is the corresponding band object). -/
def bandStep2Mat {d : ℕ} (sz : Sizes d) (E : ℕ → ℝ) : Step2Mat sz where
  toFlowFM := bandFM sz E
  LM := fun n u {_k} H σ a => STLM sz n (E n) u H σ a
  GMM := fun n u H x y => STGMM sz n (E n) u H x y
  LIM := fun n u H I => STLIM sz n (E n) u H I
  KI := fun n u I => KLK d (sz.L n) (sz.lam n) (sz.W n) (E n) u I
  Pp := pathP sz
  Hpath := fun s t K n k ω => pathH sz s t K n k ω

/-- **The band instance of `Step2Data` along the flow `z`**: `E = STflowE z`, `T0 = lemT (z ·)`, `flowOK = STFlow`. -/
def bandStep2Data {d : ℕ} (sz : Sizes d) (z : ℕ → ℂ) : Step2Data sz where
  toStep2Mat := bandStep2Mat sz (STflowE z)
  T0 := fun n => lemT (z n)
  flowOK := fun κ ε 𝔠 𝔡 => STFlow sz κ ε 𝔠 𝔡 z
  flowOK_adm := fun h => h.1
  flowOK_T := fun _ h n => lemT_lt_one (Step2Gen_flow_im_pos h n)
  L_swap := fun n t a b ω => Step2Gen_loopFine_swap _ _ a b

end BandInst


/-! ## 2b. The block kernel `M^{(σσ')}` and the drift kernels read from the carrier -/

section Kern

variable {d : ℕ} {sz : Sizes d}

/-- The propagator `Θ_ξ = (1 - ξ S)⁻¹` of a kernel `S` (the band `Theta d L g` is the case `S = SB d L g`). -/
def Step2Gen_Theta {Λ : Type*} [Fintype Λ] [DecidableEq Λ] (S : Matrix Λ Λ ℂ) (ξ : ℂ) : Matrix Λ Λ ℂ :=
  Ring.inverse (1 - ξ • S)

/-- `M(σ)_{xy}` of the carrier `C`: `M(+) = M`, `M(−) = M^*`, i.e. `M(−)_{xy} = conj M_{yx}` (the charge convention of
`STmsigg` and of `G(z̄) = G(z)^*`; `BAMsigma`, `BA/MFixedPoint`). -/
def Step2Kern_Msig (C : FlowFM sz) (n : ℕ) (σ : Bool) (x y : Idx d (sz.L n) (sz.W n)) : ℂ :=
  if σ then C.M n x y else (starRingEnd ℂ) (C.M n y x)

/-- `B(σ)` of a block matrix: `B(+) = B`, `B(−) = B^*` (`BAMsigma` at a general `B`). -/
def Step2Kern_Bsig {Λ : Type*} (Bm : Matrix Λ Λ ℂ) (σ : Bool) : Matrix Λ Λ ℂ :=
  if σ then Bm else Bmᴴ

/-- **The block kernel** `M^{(σσ')}_{ab} = W^{-d} Σ_{x∈[a]} Σ_{y∈[b]} M(σ)_{yx} M(σ')_{xy}` ((2.35) `def:Theta_BA`;
`tr(M(σ)E_a M(σ')E_b)` of (2.59) `eq:Msig`, up to the `W^{±d}` normalisation).  **Charge and index order**: `M(+) = M`,
`M(−) = M^*`, and the block reading is `M(σ)_{ba} M(σ')_{ab}` (first charge on the entry `(b, a)`), as `BAMss`
(`BA/MFixedPoint`), `BAMssOf` (`BA/KCactus`) and the right-hand side of `BAKsolve` (`BA/KSolve`,
`W^{-d} (Θ_BA M^{(σ₁σ₂)})_{a₁a₂}`).  It reads only `C.M`. -/
def Step2Kern_Mss (C : FlowFM sz) (n : ℕ) (σ σ' : Bool) : Matrix (Zd d (sz.L n)) (Zd d (sz.L n)) ℂ :=
  Matrix.of fun a b => (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ *
    ∑ x ∈ Iblk d (sz.L n) (sz.W n) a, ∑ y ∈ Iblk d (sz.L n) (sz.W n) b,
      Step2Kern_Msig C n σ y x * Step2Kern_Msig C n σ' x y

/-- **`thetaKer`** ((3.11) `def:op_thn`): `X Θ_t(X) = X (1 - t X)⁻¹`, `X = M^{(σσ')} S`; at the band `X = μ S`. -/
def Step2Gen_thetaKer (C : FlowFM sz) (n : ℕ) (σ σ' : Bool) (t : ℝ) : Matrix (Zd d (sz.L n)) (Zd d (sz.L n)) ℂ :=
  (Step2Kern_Mss C n σ σ' * C.S n) * Step2Gen_Theta (Step2Kern_Mss C n σ σ' * C.S n) (t : ℂ)

/-- **`uKer`** ((3.12) `def_Ustz`): `(1 - s X) Θ_t(X)`, `X = M^{(σσ')} S`. -/
def Step2Gen_uKer (C : FlowFM sz) (n : ℕ) (σ σ' : Bool) (s t : ℝ) : Matrix (Zd d (sz.L n)) (Zd d (sz.L n)) ℂ :=
  (1 - (s : ℂ) • (Step2Kern_Mss C n σ σ' * C.S n)) * Step2Gen_Theta (Step2Kern_Mss C n σ σ' * C.S n) (t : ℂ)

/-- **`ThetaN`** ((3.11) `def:op_thn`): the operator `Θ^{(k)}_{t,σ}` on `k`-index tensors; slot `i` uses the charge pair
`(σ_i, σ_{i+1})`, `σ_{k+1} = σ_1` (`finRotate`, as `cycProd`, `Kernel/Evolution`, and `BAUN`, `BA/EKPins`). -/
def Step2Gen_ThetaN (C : FlowFM sz) (n : ℕ) {k : ℕ} (σ : Fin k → Bool) (t : ℝ) (A : (Fin k → Zd d (sz.L n)) → ℂ) :
    (Fin k → Zd d (sz.L n)) → ℂ :=
  fun a => ∑ i, ∑ b, Step2Gen_thetaKer C n (σ i) (σ (finRotate k i)) t (a i) b * A (Function.update a i b)

/-- **`UN`** (`(def_Ustz)`): the evolution kernel `U^{(k)}_{s,t,σ}` on `k`-index tensors, slot `i` with `(σ_i, σ_{i+1})`. -/
def Step2Gen_UN (C : FlowFM sz) (n : ℕ) {k : ℕ} (σ : Fin k → Bool) (s t : ℝ) (A : (Fin k → Zd d (sz.L n)) → ℂ) :
    (Fin k → Zd d (sz.L n)) → ℂ :=
  fun a => ∑ b : Fin k → Zd d (sz.L n), (∏ i, Step2Gen_uKer C n (σ i) (σ (finRotate k i)) s t (a i) (b i)) * A b

private theorem Step2Kern_count_ofs (n : ℕ) (a b : Zd d (sz.L n)) :
    ∑ x ∈ Iblk d (sz.L n) (sz.W n) a, ∑ y ∈ Iblk d (sz.L n) (sz.W n) b,
      (if (split d (sz.L n) (sz.W n) x).2 = (split d (sz.L n) (sz.W n) y).2 then (1 : ℂ) else 0) =
        (((sz.W n : ℕ) : ℂ) ^ d) := by
  have h1 : ∀ x ∈ Iblk d (sz.L n) (sz.W n) a, ∑ y ∈ Iblk d (sz.L n) (sz.W n) b,
      (if (split d (sz.L n) (sz.W n) x).2 = (split d (sz.L n) (sz.W n) y).2 then (1 : ℂ) else 0) = 1 := by
    intro x hx
    rw [Finset.sum_boole]
    have : (Iblk d (sz.L n) (sz.W n) b).filter
        (fun y => (split d (sz.L n) (sz.W n) x).2 = (split d (sz.L n) (sz.W n) y).2) =
        {(splitEquiv d (sz.L n) (sz.W n)).symm (b, (split d (sz.L n) (sz.W n) x).2)} := by
      ext y
      simp only [Iblk, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · rintro ⟨h1, h2⟩
        apply (splitEquiv d (sz.L n) (sz.W n)).injective
        simp only [Equiv.apply_symm_apply]
        exact Prod.ext h1 h2.symm
      · rintro rfl
        have h' : split d (sz.L n) (sz.W n)
            ((splitEquiv d (sz.L n) (sz.W n)).symm (b, (split d (sz.L n) (sz.W n) x).2)) =
              (b, (split d (sz.L n) (sz.W n) x).2) :=
          (splitEquiv d (sz.L n) (sz.W n)).apply_symm_apply (b, (split d (sz.L n) (sz.W n) x).2)
        rw [h']
        exact ⟨rfl, rfl⟩
    rw [this]
    simp
  rw [Finset.sum_congr rfl h1]
  simp [card_Iblk]

/-- **`Step2Kern_Mss_of_kron`**: if `M = Bm ⊗ I_{W^d}`, i.e. `M_{xy} = Bm(blk x, blk y) · 1{ofs x = ofs y}` (`split`,
`Defs/Sizes`), then `M^{(σσ')}_{ab} = B(σ)_{ba} B(σ')_{ab}` (`B(σ)` as in `Step2Kern_Bsig`). -/
theorem Step2Kern_Mss_of_kron (C : FlowFM sz) (n : ℕ) (Bm : Matrix (Zd d (sz.L n)) (Zd d (sz.L n)) ℂ)
    (hM : ∀ x y : Idx d (sz.L n) (sz.W n), C.M n x y =
      Bm (split d (sz.L n) (sz.W n) x).1 (split d (sz.L n) (sz.W n) y).1 *
        (if (split d (sz.L n) (sz.W n) x).2 = (split d (sz.L n) (sz.W n) y).2 then 1 else 0))
    (σ σ' : Bool) :
    Step2Kern_Mss C n σ σ' = Matrix.of fun a b => Step2Kern_Bsig Bm σ b a * Step2Kern_Bsig Bm σ' a b := by
  ext a b
  simp only [Step2Kern_Mss, Matrix.of_apply]
  have hterm : ∀ x ∈ Iblk d (sz.L n) (sz.W n) a, ∀ y ∈ Iblk d (sz.L n) (sz.W n) b,
      Step2Kern_Msig C n σ y x * Step2Kern_Msig C n σ' x y =
        (Step2Kern_Bsig Bm σ b a * Step2Kern_Bsig Bm σ' a b) *
          (if (split d (sz.L n) (sz.W n) x).2 = (split d (sz.L n) (sz.W n) y).2 then (1 : ℂ) else 0) := by
    intro x hx y hy
    have hxa : (split d (sz.L n) (sz.W n) x).1 = a := by simpa [Iblk] using hx
    have hyb : (split d (sz.L n) (sz.W n) y).1 = b := by simpa [Iblk] using hy
    by_cases ho : (split d (sz.L n) (sz.W n) x).2 = (split d (sz.L n) (sz.W n) y).2
    · cases σ <;> cases σ' <;>
        simp [Step2Kern_Msig, Step2Kern_Bsig, hM, hxa, hyb, ho, Matrix.conjTranspose_apply]
    · have ho' : ¬ (split d (sz.L n) (sz.W n) y).2 = (split d (sz.L n) (sz.W n) x).2 := fun h => ho h.symm
      cases σ <;> cases σ' <;>
        simp [Step2Kern_Msig, Step2Kern_Bsig, hM, hxa, hyb, ho, ho', Matrix.conjTranspose_apply]
  rw [Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun y hy => hterm x hx y hy]
  simp_rw [← Finset.mul_sum]
  rw [Step2Kern_count_ofs n a b]
  have hW : (((sz.W n : ℕ) : ℂ) ^ d) ≠ 0 := by
    have := NeZero.ne (sz.W n)
    exact pow_ne_zero _ (by exact_mod_cast this)
  field_simp

/-- **`Step2Kern_Mss_band`**: at `bandFM`, `M = m(E) I` gives `M^{(σσ')} = m(σ) m(σ') I`. -/
theorem Step2Kern_Mss_band (sz : Sizes d) (E : ℕ → ℝ) (n : ℕ) (σ σ' : Bool) :
    Step2Kern_Mss (bandFM sz E) n σ σ' =
      (mSigma (E n) σ * mSigma (E n) σ') • (1 : Matrix (Zd d (sz.L n)) (Zd d (sz.L n)) ℂ) := by
  have hker : ∀ x y : Idx d (sz.L n) (sz.W n), (bandFM sz E).M n x y =
      (Matrix.of fun a b : Zd d (sz.L n) => if a = b then mE (E n) else 0) (split d (sz.L n) (sz.W n) x).1
        (split d (sz.L n) (sz.W n) y).1 *
      (if (split d (sz.L n) (sz.W n) x).2 = (split d (sz.L n) (sz.W n) y).2 then 1 else 0) := by
    intro x y
    by_cases hxy : x = y
    · subst hxy
      simp [bandFM]
    · by_cases h1 : (split d (sz.L n) (sz.W n) x).1 = (split d (sz.L n) (sz.W n) y).1
      · have h2 : ¬ (split d (sz.L n) (sz.W n) x).2 = (split d (sz.L n) (sz.W n) y).2 := fun h2 =>
          hxy (split_injective d (sz.L n) (sz.W n) (Prod.ext h1 h2))
        simp [bandFM, hxy, h2]
      · simp [bandFM, hxy, h1]
  rw [Step2Kern_Mss_of_kron (bandFM sz E) n _ hker σ σ']
  ext a b
  by_cases h : a = b
  · subst h
    cases σ <;> cases σ' <;> simp [Step2Kern_Bsig, mSigma]
  · cases σ <;> cases σ' <;> simp [Step2Kern_Bsig, mSigma, h, Matrix.one_apply, Ne.symm h]

/-- **`Step2Kern_thetaKer_band`**: `thetaKer` at `bandFM` is the band kernel `μ S^{(B)} Θ_{tμ}`
(`RBM.thetaKer`, `Kernel/Evolution`), `μ = m(σ) m(σ')`. -/
theorem Step2Kern_thetaKer_band (sz : Sizes d) (E : ℕ → ℝ) (n : ℕ) (σ σ' : Bool) (t : ℝ) :
    Step2Gen_thetaKer (bandFM sz E) n σ σ' t =
      RBM.thetaKer d (sz.L n) (sz.lam n) (mSigma (E n) σ * mSigma (E n) σ') t := by
  unfold Step2Gen_thetaKer RBM.thetaKer Theta
  rw [Step2Kern_Mss_band]
  have hS : (bandFM sz E).S n = SB d (sz.L n) (sz.lam n) := rfl
  rw [hS, smul_mul_assoc, one_mul]
  unfold Step2Gen_Theta
  rw [smul_smul, mul_comm]

/-- **`Step2Kern_uKer_band`**: `uKer` at `bandFM` is the band kernel `(1 - s μ S^{(B)}) Θ_{tμ}` (`RBM.uKer`,
`Kernel/Evolution`). -/
theorem Step2Kern_uKer_band (sz : Sizes d) (E : ℕ → ℝ) (n : ℕ) (σ σ' : Bool) (s t : ℝ) :
    Step2Gen_uKer (bandFM sz E) n σ σ' s t =
      RBM.uKer d (sz.L n) (sz.lam n) (mSigma (E n) σ * mSigma (E n) σ') s t := by
  unfold Step2Gen_uKer RBM.uKer Theta
  rw [Step2Kern_Mss_band]
  have hS : (bandFM sz E).S n = SB d (sz.L n) (sz.lam n) := rfl
  rw [hS, smul_mul_assoc, one_mul]
  unfold Step2Gen_Theta
  rw [smul_smul, smul_smul, mul_comm (t : ℂ), mul_comm (s : ℂ)]

/-- **`Step2Kern_UN_band`**: `UN` at `bandFM` is the band `RBM.UN` at `m_i = m(σ_i)`
(`Kernel/Evolution`). -/
theorem Step2Kern_UN_band (sz : Sizes d) (E : ℕ → ℝ) (n k : ℕ) (σ : Fin k → Bool) (s t : ℝ)
    (A : (Fin k → Zd d (sz.L n)) → ℂ) :
    Step2Gen_UN (bandFM sz E) n σ s t A =
      RBM.UN d (sz.L n) (sz.lam n) (fun i => mSigma (E n) (σ i)) s t A := by
  funext a
  unfold Step2Gen_UN RBM.UN
  simp only [Step2Kern_uKer_band]
  rfl

end Kern

/-! ## 3. The matrix-level and model-level vocabulary -/

section Matrix

variable {d : ℕ} {sz : Sizes d} (Cm : Step2Mat sz)

/-- `STmsig`: `K^{(1)}_σ = m(σ)` with `m` of the carrier. -/
def STmsigg (n : ℕ) (σ : Bool) : ℂ := if σ then Cm.m n else (starRingEnd ℂ) (Cm.m n)

/-- `STLM`: `𝓛^{(k)}_{u,σ,a}` of a fine matrix `H`. -/
def STLMg (n : ℕ) (u : ℝ) (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) {k : ℕ}
    (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)) : ℂ := Cm.LM n u H σ a

/-- `STLKM`: `(𝓛 - 𝒦)^{(k)}_{u,σ,a}` of a fine matrix `H`. -/
def STLKMg (n : ℕ) (u : ℝ) (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) {k : ℕ}
    (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)) : ℂ := STLMg Cm n u H σ a - Cm.K n u σ a

/-- `STJhatM`: the random bound `Ĵ^ℓ_{u,D}` of a fine matrix `H`. -/
def STJhatMg (n : ℕ) (D ℓ u : ℝ) (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) : ℝ :=
  Finset.univ.sup' ⟨((fun _ => true), (fun _ => 0)), Finset.mem_univ _⟩
    (fun p : (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)) =>
      ‖STLKMg Cm n u H p.1 p.2‖ / STprof sz n u D ℓ (p.2 0) (p.2 1))

/-- `STavgM`: `⟨G̃_u(σ) E_a⟩ = 𝓛^{(1)}_{u,σ,a} - m(σ)` of a fine matrix. -/
def STavgMg (n : ℕ) (u : ℝ) (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    (σ : Bool) (a : Zd d (sz.L n)) : ℂ :=
  STLMg Cm n u H (fun _ : Fin 1 => σ) (fun _ => a) - STmsigg Cm n σ

/-- `STEGtM`: the light-weight term `𝓔^{G̃,(2)}_{u,σ,a}` of a fine matrix (`(def_EwtG)`, `n = 2`). -/
def STEGtMg (n : ℕ) (u : ℝ) (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) : ℂ :=
  (((sz.W n : ℕ) : ℂ) ^ d) * ∑ x : Zd d (sz.L n), ∑ y : Zd d (sz.L n),
    (STavgMg Cm n u H (σ 0) x * Cm.S n x y * STLMg Cm n u H ![σ 0, σ 0, σ 1] ![y, a 0, a 1] +
      STavgMg Cm n u H (σ 1) x * Cm.S n x y * STLMg Cm n u H ![σ 0, σ 1, σ 1] ![a 0, y, a 1])

/-- `STELKLKM`: `𝓔^{(𝓛-𝓚)×(𝓛-𝓚),(2)}_{u,σ,a}` of a fine matrix (`(def_ELKLK)`). -/
def STELKLKMg (n : ℕ) (u : ℝ) (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) : ℂ :=
  (((sz.W n : ℕ) : ℂ) ^ d) * ∑ x : Zd d (sz.L n), ∑ y : Zd d (sz.L n),
    STLKMg Cm n u H σ ![x, a 1] * Cm.S n x y * STLKMg Cm n u H σ ![a 0, y]

/-- `STthetaOp`: the operator `Θ^{(2)}_{u,σ}` of Definition 3.3 (`DefTHUST`) acting on a tensor `A`.  The drift kernel of slot `i` is the
block-kernel form `Step2Gen_thetaKer` at the charge pair `(σ_i, σ_{i+1})` (slot 0 has `(σ₀, σ₁)`, slot 1 has `(σ₁, σ₀)`). -/
def STthetaOpg (n : ℕ) (u : ℝ) (σ : Fin 2 → Bool) (A : (Fin 2 → Zd d (sz.L n)) → ℂ)
    (a : Fin 2 → Zd d (sz.L n)) : ℂ :=
  ∑ i : Fin 2, ∑ b : Zd d (sz.L n),
    Step2Gen_thetaKer Cm.toFlowFM n (σ i) (σ (finRotate 2 i)) u (a i) b * A (Function.update a i b)

/-- `STEEkM`: the quadratic-variation loop `(𝓔⊗𝓔)^{M,(2;k)}_{u,σ,a,a}` of a fine matrix. -/
def STEEkMg (n : ℕ) (u : ℝ) (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    (k : Fin 2) (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) : ℂ :=
  (((sz.W n : ℕ) : ℂ) ^ d) * ∑ c : Zd d (sz.L n), ∑ c' : Zd d (sz.L n),
    Cm.S n c c' *
      (if k = 0 then
        STLMg Cm n u H ![σ 0, σ 1, σ 0, !(σ 0), !(σ 1), !(σ 0)] ![a 0, a 1, c', a 1, a 0, c]
      else
        STLMg Cm n u H ![σ 1, σ 0, σ 1, !(σ 1), !(σ 0), !(σ 1)] ![a 1, a 0, c', a 0, a 1, c])

/-- `STEEM`: `(𝓔⊗𝓔)^{M,(2)} = Σ_{k=1}^2 (𝓔⊗𝓔)^{M,(2;k)}` of a fine matrix. -/
def STEEMg (n : ℕ) (u : ℝ) (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) : ℂ :=
  STEEkMg Cm n u H 0 σ a + STEEkMg Cm n u H 1 σ a

/-- `STGMM`: `(G_u - M)_{xy}` of a fine matrix `H`. -/
def STGMMg (n : ℕ) (u : ℝ) (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    (x y : Idx d (sz.L n) (sz.W n)) : ℂ := Cm.GMM n u H x y

end Matrix

section MatrixBridge

variable {d : ℕ} (sz : Sizes d) (E : ℕ → ℝ) (n : ℕ) (u : ℝ)
  (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)

/-- Not `rfl`: (`Fin.sum_univ_two`, `mul_comm` at slot 1, `Step2Kern_thetaKer_band`). -/
theorem bandStep2_STthetaOp (σ : Fin 2 → Bool) (A : (Fin 2 → Zd d (sz.L n)) → ℂ) (a : Fin 2 → Zd d (sz.L n)) :
    STthetaOp sz n (E n) u σ A a = STthetaOpg (bandStep2Mat sz E) n u σ A a := by
  unfold STthetaOp STthetaOpg
  have hfm : (bandStep2Mat sz E).toFlowFM = bandFM sz E := rfl
  have e0 : finRotate 2 0 = 1 := rfl
  have e1 : finRotate 2 1 = 0 := rfl
  rw [Fin.sum_univ_two, Fin.sum_univ_two]
  simp only [hfm, e0, e1, Step2Kern_thetaKer_band]
  have hm : ∀ s : Bool, STmsig (E n) s = mSigma (E n) s := fun s => rfl
  simp only [hm]
  unfold RBM.thetaKer
  simp only [Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul]
  rw [mul_comm (mSigma (E n) (σ 1)) (mSigma (E n) (σ 0))]
end MatrixBridge

section Model

variable {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (μ : Measure sz.SeqΩ)

/-- `STEGt`: the model-level light-weight term `𝓔^{G̃,(2)}_{t,σ,a}` over a carrier. -/
def STEGtg (n : ℕ) (t : ℝ) (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) (ω : sz.SeqΩ) : ℂ :=
  (((sz.W n : ℕ) : ℂ) ^ d) * ∑ x : Zd d (sz.L n), ∑ y : Zd d (sz.L n),
    ((C.L n t (fun _ : Fin 1 => σ 0) (fun _ => x) ω - (if σ 0 then C.m n else (starRingEnd ℂ) (C.m n))) *
        C.S n x y * C.L n t ![σ 0, σ 0, σ 1] ![y, a 0, a 1] ω +
      (C.L n t (fun _ : Fin 1 => σ 1) (fun _ => x) ω - (if σ 1 then C.m n else (starRingEnd ℂ) (C.m n))) *
        C.S n x y * C.L n t ![σ 0, σ 1, σ 1] ![a 0, y, a 1] ω)

/-- (3.27) `eq:LW_assm`: `𝓛^{(2)}_{t,σ,(a,b)} ≺ Ψ_t²(|a-b|)` for `σ ∈ {(+,-),(-,+)}`. -/
def STLWassmgL (t : ℕ → ℝ) (Ψ : ℕ → ℕ → ℝ) : Prop :=
  PrecL sz μ (U := fun n => {σ : Fin 2 → Bool // σ 0 ≠ σ 1} × (Fin 2 → Zd d (sz.L n)))
    (fun n p ω => ‖C.L n (t n) p.1.1 p.2 ω‖)
    (fun n p _ => (Ψ n (zdistInf d (sz.L n) (p.2 0 - p.2 1))) ^ 2)

end Model

/-! ## 4. The Step 2 statements over a carrier `(law, Flow, mk, T0)` -/

section StepPins

variable {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (μ : Measure sz.SeqΩ)

/-- `STAvgU` (`Step34Pins`): `(Gt_avgbound_flow)` uniformly in `u ∈ [s,t]`, `k = 1`. -/
def STAvgUgL (s t : ℕ → ℝ) : Prop :=
  PrecL sz μ (U := fun n => TimeIcc s t n × (Fin 1 → Bool) × (Fin 1 → Zd d (sz.L n)))
    (fun n p ω => ‖C.L n (p.1 : ℝ) p.2.1 p.2.2 ω - C.K n (p.1 : ℝ) p.2.1 p.2.2‖)
    (fun n p _ => (sz.Bctl n (p.1 : ℝ)) ^ 1)

/-- `STLocalEntryU` (`Step34Pins`): `(Gt_bound_flow)` uniformly in `u ∈ [s,t]`. -/
def STLocalEntryUgL (s t : ℕ → ℝ) : Prop :=
  PrecL sz μ (U := fun n => TimeIcc s t n × Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n))
    (fun n p ω => ‖C.GM n (p.1 : ℝ) ω p.2.1 p.2.2‖ ^ 2)
    (fun n p _ => STWB sz n (p.1 : ℝ) (zdistInf d (sz.L n) (STblk sz n p.2.1 - STblk sz n p.2.2)))

/-- `STGdecayW` (`Step34Pins`): `(Eq:Gdecay_w)` uniformly in `u ∈ [s,t]`, with the loss exponent `Cd`. -/
def STGdecayWgL (s t : ℕ → ℝ) (Cd : ℝ) : Prop :=
  ∀ D : ℝ, 0 < D →
    PrecL sz μ (U := fun n => TimeIcc s t n × (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)))
      (fun n p ω => ‖C.L n (p.1 : ℝ) p.2.1 p.2.2 ω - C.K n (p.1 : ℝ) p.2.1 p.2.2‖)
      (fun n p _ => ((1 - s n) / (1 - (p.1 : ℝ))) ^ Cd * (sz.Bctl n (p.1 : ℝ)) ^ (1 / 5 : ℝ) *
          STWB sz n (p.1 : ℝ) (zdistInf d (sz.L n) (p.2.2 0 - p.2.2 1)) *
          Real.exp (-(((zdistInf d (sz.L n) (p.2.2 0 - p.2.2 1) : ℕ) : ℝ) /
            ellT (sz.L n) (sz.lam n) (p.1 : ℝ)) ^ (1 / 2 : ℝ)) +
        ((sz.W n : ℕ) : ℝ) ^ (-D))

/-- `STStep2Concl` (`Step34Pins`): the three conclusions of Step 2 that Steps 3-4 consume. -/
def STStep2ConclgL (s t : ℕ → ℝ) (Cd : ℝ) : Prop :=
  STLocalEntryUgL C μ s t ∧ STAvgUgL C μ s t ∧ STGdecayWgL C μ s t Cd

/-- `STStep2Local`: (2.87) `Gt_bound_flow` uniformly in `u ∈ [s,t]` (the statement of `STLocalEntryUgL`). -/
def STStep2LocalgL (s t : ℕ → ℝ) : Prop := STLocalEntryUgL C μ s t

/-- `STStep2Avg`: (2.88) `Gt_avgbound_flow` uniformly in `u ∈ [s,t]`, `tr((G_u - M)E_a) = 𝓛^{(1)} - m`. -/
def STStep2AvggL (s t : ℕ → ℝ) : Prop :=
  PrecL sz μ (U := fun n => TimeIcc s t n × Zd d (sz.L n))
    (fun n p ω => ‖C.L n (p.1 : ℝ) (fun _ : Fin 1 => true) (fun _ => p.2) ω - C.m n‖)
    (fun n p _ => sz.Bctl n (p.1 : ℝ))

/-- `STStep2Decay`: (2.89) `Eq:Gdecay_w` uniformly in `u ∈ [s,t]`, with the loss exponent `Cd`. -/
def STStep2DecaygL (Cd : ℝ) (s t : ℕ → ℝ) : Prop := STGdecayWgL C μ s t Cd

/-- `STStep2LocalPT`: `(Gt_bound_flow)` per time. -/
def STStep2LocalPTgL (s t : ℕ → ℝ) : Prop :=
  PrecPTL sz μ (U := fun n => TimeIcc s t n × Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n))
    (fun n p ω => ‖C.GM n (p.1 : ℝ) ω p.2.1 p.2.2‖ ^ 2)
    (fun n p _ => STWB sz n (p.1 : ℝ) (zdistInf d (sz.L n) (STblk sz n p.2.1 - STblk sz n p.2.2)))

/-- `STStep2AvgPT`: `(Gt_avgbound_flow)` per time. -/
def STStep2AvgPTgL (s t : ℕ → ℝ) : Prop :=
  PrecPTL sz μ (U := fun n => TimeIcc s t n × Zd d (sz.L n))
    (fun n p ω => ‖C.L n (p.1 : ℝ) (fun _ : Fin 1 => true) (fun _ => p.2) ω - C.m n‖)
    (fun n p _ => sz.Bctl n (p.1 : ℝ))

/-- `STStep2DecayPT`: `(Eq:Gdecay_w)` per time. -/
def STStep2DecayPTgL (Cd : ℝ) (s t : ℕ → ℝ) : Prop :=
  ∀ D : ℝ, 0 < D →
    PrecPTL sz μ (U := fun n => TimeIcc s t n × (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)))
      (fun n p ω => ‖C.L n (p.1 : ℝ) p.2.1 p.2.2 ω - C.K n (p.1 : ℝ) p.2.1 p.2.2‖)
      (fun n p _ => ((1 - s n) / (1 - (p.1 : ℝ))) ^ Cd * (sz.Bctl n (p.1 : ℝ)) ^ (1 / 5 : ℝ) *
          STWB sz n (p.1 : ℝ) (zdistInf d (sz.L n) (p.2.2 0 - p.2.2 1)) *
          Real.exp (-(((zdistInf d (sz.L n) (p.2.2 0 - p.2.2 1) : ℕ) : ℝ) /
            ellT (sz.L n) (sz.lam n) (p.1 : ℝ)) ^ (1 / 2 : ℝ)) +
        ((sz.W n : ℕ) : ℝ) ^ (-D))

/-- `STL2decayPT`: `(eq:L2_decay)` per time, `𝓛^{(2)}_{u,(-,+),(a₁,a₂)} ≺ W^{-d} B_{u,|a₁-a₂|}`. -/
def STL2decayPTgL (s t : ℕ → ℝ) : Prop :=
  PrecPTL sz μ (U := fun n => TimeIcc s t n × (Fin 2 → Zd d (sz.L n)))
    (fun n p ω => ‖C.L n (p.1 : ℝ) ![false, true] p.2 ω‖)
    (fun n p _ => STWB sz n (p.1 : ℝ) (zdistInf d (sz.L n) (p.2 0 - p.2 1)))

end StepPins

section StepG

variable (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ)
  (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop)
  (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz) (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ)

/-- **Step 2 over a carrier** `(law, Flow, mk, T0)` (the shape of `STMainIndG`). -/
def STStep2G : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∃ Cd : ℝ, 0 < Cd ∧ ∃ 𝔠d : ℝ, 0 < 𝔠d ∧ 𝔠d ≤ 1 / 100 ∧
      ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), Flow sz κ ε 𝔠 𝔡 z →
        ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n ≤ T0 sz z n) → (∀ n, s n < t n) →
          (∀ n, t n ≤ T0 sz z n) →
          STLKgL (mk sz z) (law sz) s → STDecaygL (mk sz z) (law sz) s → STConStInd sz 𝔠d s t →
          STStep1LoopgL (mk sz z) (law sz) s t → STStep1WeakgL (mk sz z) (law sz) s t →
            STStep2ConclgL (mk sz z) (law sz) s t Cd

/-- `STNetLift2`: the net lift of Step 2, per-time conclusions give the uniform ones, for every `C_d`. -/
def STNetLift2gL : Prop :=
  ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), Flow sz κ ε 𝔠 𝔡 z →
      ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n ≤ t n) → (∀ n, t n ≤ T0 sz z n) →
        ∀ Cd : ℝ, STStep2LocalPTgL (mk sz z) (law sz) s t → STStep2AvgPTgL (mk sz z) (law sz) s t →
          STStep2DecayPTgL (mk sz z) (law sz) Cd s t →
            STStep2LocalgL (mk sz z) (law sz) s t ∧ STStep2AvggL (mk sz z) (law sz) s t ∧
              STStep2DecaygL (mk sz z) (law sz) Cd s t

/-- `STLocalAvgOfL2`: the closing paragraph of Step 2, `(eq:L2_decay)` and `(Gtmwc)` give `(Gt_bound_flow)` and
`(Gt_avgbound_flow)` per time. -/
def STLocalAvgOfL2gL : Prop :=
  ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), Flow sz κ ε 𝔠 𝔡 z →
      ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n ≤ t n) → (∀ n, t n ≤ T0 sz z n) →
        STStep1WeakgL (mk sz z) (law sz) s t → STL2decayPTgL (mk sz z) (law sz) s t →
          STStep2LocalPTgL (mk sz z) (law sz) s t ∧ STStep2AvgPTgL (mk sz z) (law sz) s t

/-- `STOptL2`: `(eq:opt_L2)`, the maximal bound `|(𝓛-𝒦)^{(2)}| ≺ W^{-d} B_{u,0}` per time. -/
def STOptL2gL : Prop :=
  ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∃ 𝔠₀ : ℝ, 0 < 𝔠₀ ∧ ∀ 𝔠d : ℝ, 0 < 𝔠d → 𝔠d ≤ 𝔠₀ →
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), Flow sz κ ε 𝔠 𝔡 z →
      ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n ≤ t n) → (∀ n, t n ≤ T0 sz z n) →
        STLKgL (mk sz z) (law sz) s → STConStInd sz 𝔠d s t → STStep1LoopgL (mk sz z) (law sz) s t →
          STStep1WeakgL (mk sz z) (law sz) s t →
          PrecPTL sz (law sz) (U := fun n => TimeIcc s t n × (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)))
            (fun n p ω => ‖(mk sz z).L n (p.1 : ℝ) p.2.1 p.2.2 ω - (mk sz z).K n (p.1 : ℝ) p.2.1 p.2.2‖)
            (fun n p _ => sz.Bctl n (p.1 : ℝ))

/-- `STScaleExists`: the admissible scale family `K_u^{(m)}` exists for every flow (reads only the setting and the horizon). -/
def STScaleExistsgL : Prop :=
  ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), Flow sz κ ε 𝔠 𝔡 z →
      ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n ≤ t n) → (∀ n, t n ≤ T0 sz z n) →
        ∃ Kseq : ℕ → ℕ → ℝ → ℝ, STScaleAdm sz s t Kseq

/-- `STLWB`: `lem:LWterm`, the light-weight `B`-bound `𝓔^{G̃,(2)} ≺ η_t^{-1} Ψ_t(0) Ψ_t²(|a-b|)`. -/
def STLWBgL : Prop :=
  ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), Flow sz κ ε 𝔠 𝔡 z →
      ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ T0 sz z n) →
        ∀ ε₀ : ℝ, 0 < ε₀ → ∀ Ψ : ℕ → ℕ → ℝ, STPsiClass sz ε₀ Ψ →
          STInitialGT2gL (mk sz z) (law sz) t ε₀ (fun n => Ψ n 0) → STLWassmgL (mk sz z) (law sz) t Ψ →
            PrecL sz (law sz) (U := fun n => (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)))
              (fun n p ω => ‖STEGtg (mk sz z) n (t n) p.1 p.2 ω‖)
              (fun n p _ => ((mk sz z).eta n (t n))⁻¹ * Ψ n 0 *
                (Ψ n (zdistInf d (sz.L n) (p.2 0 - p.2 1))) ^ 2)

/-- `STLWT`: `lem: EWGn2_N`, the light-weight `𝒯`-bound. -/
def STLWTgL : Prop :=
  ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), Flow sz κ ε 𝔠 𝔡 z →
      ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ T0 sz z n) →
        ∀ ε₀ : ℝ, 0 < ε₀ → ∀ Ψ : ℕ → ℝ,
          (∀ᶠ n in atTop, ((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2) ≤ Ψ n ∧
            Ψ n ≤ ((sz.W n : ℕ) : ℝ) ^ (-ε₀)) →
          STInitialGT2gL (mk sz z) (law sz) t ε₀ Ψ →
          ∀ ℓ : ℕ → ℝ, (∀ᶠ n in atTop, 0 ≤ ℓ n ∧ ℓ n ≤ (Real.log ((sz.W n : ℕ) : ℝ)) ^ 10 *
              ellT (sz.L n) (sz.lam n) (t n)) →
            (∀ D : ℝ, 0 < D → STLWassmExpgL (mk sz z) (law sz) t D ℓ) →
            ∀ D : ℝ, 0 < D →
              PrecL sz (law sz) (U := fun n => (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)))
                (fun n p ω => ‖STEGtg (mk sz z) n (t n) p.1 p.2 ω‖)
                (fun n p _ => ((mk sz z).eta n (t n))⁻¹ * (sz.Bctl n (t n)) ^ (1 / 2 : ℝ) *
                  STprof sz n (t n) D (ℓ n) (p.2 0) (p.2 1))

/-- `STEMn2Poly`: `lem: EMn2_N`, first estimate `(eq:MG_conclusion)`. -/
def STEMn2PolygL : Prop :=
  ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), Flow sz κ ε 𝔠 𝔡 z →
      ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ T0 sz z n) →
        ∀ ε₀ : ℝ, 0 < ε₀ → ∀ Ψ : ℕ → ℕ → ℝ, STPsiClass sz ε₀ Ψ →
          STInitialGT2gL (mk sz z) (law sz) t ε₀ (fun n => Ψ n 0) → STLWassmgL (mk sz z) (law sz) t Ψ →
            PrecL sz (law sz) (U := fun n => Fin 2 × (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)))
              (fun n p ω => ‖STEEg (mk sz z) n (t n) p.1 p.2.1 p.2.2 ω‖)
              (fun n p _ => ((mk sz z).eta n (t n))⁻¹ * Ψ n 0 *
                (Ψ n (zdistInf d (sz.L n) (p.2.2 0 - p.2.2 1))) ^ 4)

/-- `STEMn2Exp`: `lem: EMn2_N`, third estimate (3.35) `eq:MG_conclusion3`, with the random bound `Ĵ`. -/
def STEMn2ExpgL : Prop :=
  ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), Flow sz κ ε 𝔠 𝔡 z →
      ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ T0 sz z n) →
        ∀ ε₀ : ℝ, 0 < ε₀ → ∀ Ψ : ℕ → ℝ,
          (∀ᶠ n in atTop, ((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2) ≤ Ψ n ∧
            Ψ n ≤ ((sz.W n : ℕ) : ℝ) ^ (-ε₀)) →
          STInitialGT2gL (mk sz z) (law sz) t ε₀ Ψ →
          ∀ ℓ : ℕ → ℝ, (∀ᶠ n in atTop, 0 ≤ ℓ n ∧ ℓ n ≤ (Real.log ((sz.W n : ℕ) : ℝ)) ^ 10 *
              ellT (sz.L n) (sz.lam n) (t n)) →
            (∀ D : ℝ, 0 < D → STLWassmExpgL (mk sz z) (law sz) t D ℓ) →
            ∀ D : ℝ, 0 < D →
              PrecL sz (law sz) (U := fun n => Fin 2 × (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)))
                (fun n p ω => ‖STEEg (mk sz z) n (t n) p.1 p.2.1 p.2.2 ω‖)
                (fun n p ω => ((mk sz z).eta n (t n))⁻¹ *
                  ((sz.Bctl n (t n)) ^ (1 / 2 : ℝ) + (STJhatg (mk sz z) n D (ℓ n) (t n) ω) ^ 3) *
                  (STprof sz n (t n) D (ℓ n) (p.2.2 0) (p.2.2 1)) ^ 2)

end StepG

section StepGBridge

variable (d : ℕ)

theorem bandFM_STLWT :
    STLWT d ↔ STLWTgL d (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
      (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n)) := Iff.rfl
theorem bandFM_STEMn2Poly :
    STEMn2Poly d ↔ STEMn2PolygL d (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
      (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n)) := Iff.rfl
theorem bandFM_STEMn2Exp :
    STEMn2Exp d ↔ STEMn2ExpgL d (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
      (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n)) := Iff.rfl

end StepGBridge


/-! ## 5. The forms of `lem_GbEXP`, the grid, the list-indexed loops, the energy statements -/

section GbEXPForms

variable {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (μ : Measure sz.SeqΩ)

/-- `STindMax`: the indicator of `{‖G_τ - M‖_max ≤ A}`. -/
def STindMaxg (n : ℕ) (τ A : ℝ) (ω : sz.SeqΩ) : ℝ :=
  if ∀ x y : Idx d (sz.L n) (sz.W n), ‖C.GM n τ ω x y‖ ≤ A then 1 else 0

/-- `STgexRHS`: the right side of (3.3) `GijGEX`. -/
def STgexRHSg (n : ℕ) (τ : ℝ) (ω : sz.SeqΩ) (a b : Zd d (sz.L n)) : ℝ :=
  (∑ σ ∈ ({![true, false], ![false, true]} : Finset (Fin 2 → Bool)),
    ∑ a' ∈ Finset.univ.filter (fun a' : Zd d (sz.L n) => zdistInf d (sz.L n) (a' - a) ≤ 1),
      ∑ b' ∈ Finset.univ.filter (fun b' : Zd d (sz.L n) => zdistInf d (sz.L n) (b' - b) ≤ 1),
        ‖C.L n τ σ ![a', b'] ω‖) +
    (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (if zdistInf d (sz.L n) (a - b) ≤ 1 then 1 else 0)

/-- `STGiiGEX`: (3.2) `GiiGEX` over a carrier. -/
def STGiiGEXgL (t : ℕ → ℝ) (ε₀ : ℝ) : Prop :=
  PrecL sz μ (U := fun n => Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n))
    (fun n p ω => STindMaxg C n (t n) (((sz.W n : ℕ) : ℝ) ^ (-ε₀)) ω * ‖C.GM n (t n) ω p.1 p.2‖ ^ 2)
    (fun n _ ω => STmaxLoop2g C n (t n) ω)

/-- `STGijGEX`: (3.3) `GijGEX` over a carrier, stated for `(G_t - M)_{xy}` (`x ≠ y`), not `(G_t)_{xy}`: at the
band `M` is diagonal and the two agree (`bandFM_STGijGEX`); at a carrier with a non-diagonal `M` they differ. -/
def STGijGEXgL (t : ℕ → ℝ) (ε₀ : ℝ) : Prop :=
  PrecL sz μ
    (U := fun n => {p : Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n) // p.1 ≠ p.2})
    (fun n p ω => STindMaxg C n (t n) (((sz.W n : ℕ) : ℝ) ^ (-ε₀)) ω * ‖C.GM n (t n) ω p.1.1 p.1.2‖ ^ 2)
    (fun n p ω => STgexRHSg C n (t n) ω (STblk sz n p.1.1) (STblk sz n p.1.2))

/-- `STGavLGEX`: (3.5) `GavLGEX` under (3.4) `initialGT2` over a carrier. -/
def STGavLGEXgL (t : ℕ → ℝ) (ε₀ : ℝ) : Prop :=
  ∀ Ψ : ℕ → ℝ, (∀ᶠ n in atTop, ((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2) ≤ Ψ n) →
    (∀ᶠ n in atTop, Ψ n ≤ ((sz.W n : ℕ) : ℝ) ^ (-ε₀)) →
    PrecL sz μ (U := fun n => Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n))
      (fun n p ω => ‖C.GM n (t n) ω p.1 p.2‖) (fun n _ _ => ((sz.W n : ℕ) : ℝ) ^ (-ε₀)) →
    PrecL sz μ (U := fun _ => Unit) (fun n _ ω => STmaxLoop2g C n (t n) ω) (fun n _ _ => Ψ n ^ 2) →
    PrecL sz μ (U := fun n => Zd d (sz.L n))
      (fun n a ω => ‖C.L n (t n) (fun _ : Fin 1 => true) (fun _ => a) ω - C.m n‖)
      (fun n _ _ => Ψ n ^ 2)

end GbEXPForms

section GbEXPBridge

variable {d : ℕ} (sz : Sizes d) (E t : ℕ → ℝ) (ε₀ : ℝ)

/-- *Not `Iff.rfl`*: the band `STGijGEX` is stated for `‖(G_t)_{xy}‖²`, the generic one for `‖(G_t - M)_{xy}‖²`; they agree
off the diagonal because the band `M = m(E) I` is diagonal. -/
theorem bandFM_STGijGEX : STGijGEX sz E t ε₀ ↔ STGijGEXgL (bandFM sz E) (Sizes.seqP sz) t ε₀ := by
  unfold STGijGEX STGijGEXgL Prec PrecL
  have h : ∀ (n : ℕ) (p : {p : Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n) // p.1 ≠ p.2}) (ω : sz.SeqΩ),
      ‖Gt sz n (E n) (t n) true ω p.1.1 p.1.2‖ ^ 2 = ‖(bandFM sz E).GM n (t n) ω p.1.1 p.1.2‖ ^ 2 := by
    intro n p ω
    simp [FlowFM.GM, bandFM, p.2]
  simp only [h]
  rfl

end GbEXPBridge

section WardBridge

variable {d : ℕ} (sz : Sizes d) (E : ℕ → ℝ)

/-- *Not `Iff.rfl`*: the band `STKward` (`Induction/Step34Pins`) reads the list-indexed `𝒦`
(`STKI` at `⟨List.ofFn σ, List.ofFn a ++ [x]⟩`), the generic `STKwardgL` (`Chain/Carrier`) the `Fin k`-indexed `C.K`; they agree by
`Carrier_ofFn_ext`; `η` is `etaT (E n) τ = (bandFM sz E).eta n τ` by definition. -/
theorem bandFM_STKward : STKward sz E ↔ STKwardgL (bandFM sz E) (Sizes.seqP sz) := by
  unfold STKward STKwardgL Prec PrecL
  have h : ∀ (τ : ℕ → ℝ) (k : ℕ), 2 ≤ k → ∀ (n : ℕ) (p : (Fin k → Bool) × (Fin (k - 1) → Zd d (sz.L n)))
      (x : Zd d (sz.L n)),
      STKI sz n (E n) (τ n) ⟨List.ofFn p.1, List.ofFn p.2 ++ [x]⟩ =
        (bandFM sz E).K n (τ n) p.1 (fun i : Fin k => if h : (i : ℕ) < k - 1 then p.2 ⟨i, h⟩ else x) := by
    intro τ k hk n p x
    change KLK d (sz.L n) (sz.lam n) (sz.W n) (E n) (τ n) _ = KLK d (sz.L n) (sz.lam n) (sz.W n) (E n) (τ n) _
    rw [KLloopOf, Carrier_ofFn_ext (by omega)]
  constructor
  · intro hh τ h0 h1 k hk
    have := hh τ h0 h1 k hk
    simp only [h τ k hk] at this
    exact this
  · intro hh τ h0 h1 k hk
    have := hh τ h0 h1 k hk
    simp only [← h τ k hk] at this
    exact this

end WardBridge

section Grid

variable {d : ℕ} {sz : Sizes d} (Cm : Step2Mat sz)

/-- `STgA`: `A_k = (𝓛-𝒦)^{(2)}_{u_k,σ,a}(H_k)`, the observable of the grid walk. -/
def STgAg (s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) (k : ℕ)
    (ω : PathΩ sz) : ℂ :=
  STLKMg Cm n (gridTime s t K n k) (Cm.Hpath s t K n k ω) σ a

/-- `STgDrift`: the drift of `(𝓛-𝒦)^{(2)}` ((3.23) `LK_simple`) at the grid state. -/
def STgDriftg (s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) (k : ℕ)
    (ω : PathΩ sz) : ℂ :=
  STthetaOpg Cm n (gridTime s t K n k) σ (STLKMg Cm n (gridTime s t K n k) (Cm.Hpath s t K n k ω) σ) a +
    STELKLKMg Cm n (gridTime s t K n k) (Cm.Hpath s t K n k ω) σ a +
    STEGtMg Cm n (gridTime s t K n k) (Cm.Hpath s t K n k ω) σ a

/-- `STstopIdx`: the stopping index `T` of `(eq:def2_stopping)` on the grid. -/
def STstopIdxg (s t : ℕ → ℝ) (K : ℕ → ℕ) (D : ℝ) (ℓ : ℕ → ℝ → ℝ) (n : ℕ) : PathΩ sz → ℕ :=
  firstHit (fun j (ω : PathΩ sz) =>
    STJhatMg Cm n D (ℓ n (gridTime s t K n j)) (gridTime s t K n j) (Cm.Hpath s t K n j ω) /
      (sz.Bctl n (gridTime s t K n j)) ^ (1 / 6 : ℝ)) 1 (K n)

end Grid

/-- `STGridMartAt`: Lemma 3.4 (`Sol_CalL`) + Lemma 3.6 (`lem:DIfREP`), the grid decomposition and the martingale tail,
over a carrier `(Flow, mk, T0)` with `mk` valued in `Step2Mat`. -/
def STGridMartAtgL (d : ℕ) (C₀ : ℝ) (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop)
    (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), Step2Mat sz) (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) : Prop :=
  ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), Flow sz κ ε 𝔠 𝔡 z →
      ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n ≤ t n) → (∀ n, t n ≤ T0 sz z n) →
        ∀ D : ℝ, 0 < D → ∃ CK : ℝ, 0 ≤ CK ∧
          ∀ K : ℕ → ℕ, (∀ n, K n ≠ 0) → (∀ᶠ n in atTop, ((sz.size n : ℕ) : ℝ) ^ CK ≤ K n) →
            ∃ Mart Rem : ∀ n, ((Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n))) → ℕ → PathΩ sz → ℂ,
              (∀ n i, ∀ᵐ ω ∂((mk sz z).Pp), ∀ k, k ≤ K n →
                STgAg (mk sz z) s t K n i.1 i.2 k ω =
                  STgAg (mk sz z) s t K n i.1 i.2 0 ω +
                    ((gridStep s t K n : ℝ) : ℂ) *
                      ∑ j ∈ Finset.range k, STgDriftg (mk sz z) s t K n i.1 i.2 j ω +
                    Rem n i k ω + Mart n i k ω) ∧
              (∀ᶠ n in atTop, ∀ i, ∀ᵐ ω ∂((mk sz z).Pp), ∀ k, k ≤ K n →
                ‖Rem n i k ω‖ ≤ ((sz.size n : ℕ) : ℝ) ^ C₀ * Real.sqrt (gridStep s t K n)) ∧
              (∀ ε' : ℝ, 0 < ε' → ∀ᶠ n in atTop, ∀ i,
                (mk sz z).Pp {ω | ∃ k, k ≤ K n ∧
                  ((sz.size n : ℕ) : ℝ) ^ ε' *
                      (∑ j ∈ Finset.range k, gridStep s t K n *
                        ‖STEEMg (mk sz z) n (gridTime s t K n j) ((mk sz z).Hpath s t K n j ω)
                          i.1 i.2‖ + ((sz.size n : ℕ) : ℝ) ^ (-D)) ^ (1 / 2 : ℝ) <
                    ‖Mart n i k ω‖} ≤ ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-D)))

/-- `STGridMart`: the statement `∃ C₀` with `STGridMartAtgL`. -/
def STGridMartgL (d : ℕ) (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop)
    (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), Step2Mat sz) (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) : Prop :=
  ∃ C₀ : ℝ, 0 ≤ C₀ ∧ STGridMartAtgL d C₀ Flow mk T0

section GridBridge

variable {d : ℕ} (sz : Sizes d) (E s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ)

/-- Not `rfl` (through `bandStep2_STthetaOp`). -/
theorem bandStep2_STgDrift (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) (k : ℕ) (ω : PathΩ sz) :
    STgDrift sz s t K n (E n) σ a k ω = STgDriftg (bandStep2Mat sz E) s t K n σ a k ω := by
  unfold STgDrift STgDriftg
  rw [bandStep2_STthetaOp]
  rfl
/-- Not `Iff.rfl` (the drift reads the block kernel; through `bandStep2_STgDrift`). -/
theorem bandStep2_STGridMartAt (C₀ : ℝ) :
    STGridMartAt d C₀ ↔ STGridMartAtgL d C₀ (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
      (fun sz z => bandStep2Mat sz (STflowE z)) (fun _ z n => lemT (z n)) := by
  unfold STGridMartAt STGridMartAtgL
  simp only [bandStep2_STgDrift]
  exact Iff.rfl
theorem bandStep2_STGridMart :
    STGridMart d ↔ STGridMartgL d (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
      (fun sz z => bandStep2Mat sz (STflowE z)) (fun _ z n => lemT (z n)) := by
  unfold STGridMart STGridMartgL
  simp only [bandStep2_STGridMartAt]

end GridBridge


/-! ## 6. The list-indexed loops of `Step2Defs` (`STLIM`, ..., `STGridRepN`) -/

section ListLoops

variable {d : ℕ} {sz : Sizes d} (Cm : Step2Mat sz)

/-- `STLIM`: `𝓛_{u,I}` of a fine matrix, `I` a list-based loop index. -/
def STLIMg (n : ℕ) (u : ℝ) (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    (I : LoopIdx (Zd d (sz.L n))) : ℂ := Cm.LIM n u H I

/-- `STLKIM`: `(𝓛 - 𝒦)_{u,I}` of a fine matrix. -/
def STLKIMg (n : ℕ) (u : ℝ) (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    (I : LoopIdx (Zd d (sz.L n))) : ℂ := STLIMg Cm n u H I - Cm.KI n u I

/-- `STksimLKM`: `[𝒦^{(l)} ∼ (𝓛-𝒦)]^{(n)}_{u,I}` of a fine matrix. -/
def STksimLKMg (n : ℕ) (u : ℝ) (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    (l : ℕ) (I : LoopIdx (Zd d (sz.L n))) : ℂ :=
  (((sz.W n : ℕ) : ℂ) ^ d) * ∑ k ∈ Finset.Icc 1 I.length, ∑ l' ∈ Finset.Ioc k I.length,
    ∑ a : Zd d (sz.L n), ∑ b : Zd d (sz.L n),
      ((if (I.cutGlueR k l' b).length = l then
          STLKIMg Cm n u H (I.cutGlueL k l' a) * Cm.S n a b * Cm.KI n u (I.cutGlueR k l' b)
        else 0) +
       (if (I.cutGlueL k l' a).length = l then
          Cm.KI n u (I.cutGlueL k l' a) * Cm.S n a b * STLKIMg Cm n u H (I.cutGlueR k l' b)
        else 0))

/-- `STelklkM`: `ℰ^{(𝓛-𝒦)×(𝓛-𝒦),(n)}_{u,I}` of a fine matrix. -/
def STelklkMg (n : ℕ) (u : ℝ) (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    (I : LoopIdx (Zd d (sz.L n))) : ℂ :=
  (((sz.W n : ℕ) : ℂ) ^ d) * ∑ k ∈ Finset.Icc 1 I.length, ∑ l' ∈ Finset.Ioc k I.length,
    ∑ a : Zd d (sz.L n), ∑ b : Zd d (sz.L n),
      STLKIMg Cm n u H (I.cutGlueL k l' a) * Cm.S n a b * STLKIMg Cm n u H (I.cutGlueR k l' b)

/-- `STavgErrM`: `tr(G̃_u(σ) E_a)` of a fine matrix. -/
def STavgErrMg (n : ℕ) (u : ℝ) (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    (σ : Bool) (a : Zd d (sz.L n)) : ℂ := STLIMg Cm n u H ⟨[σ], [a]⟩ - STmsigg Cm n σ

/-- `STegtM`: `ℰ^{G̃,(n)}_{u,I}` of a fine matrix. -/
def STegtMg (n : ℕ) (u : ℝ) (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    (I : LoopIdx (Zd d (sz.L n))) : ℂ :=
  (((sz.W n : ℕ) : ℂ) ^ d) * ∑ k ∈ Finset.Icc 1 I.length, ∑ a : Zd d (sz.L n), ∑ b : Zd d (sz.L n),
    STavgErrMg Cm n u H (I.σ.getD (k - 1) false) a * Cm.S n a b * STLIMg Cm n u H (I.cutGlue k b)

/-- `STeeM`: `(ℰ⊗ℰ)^{M,(m)}_{u,σ,a,a'}` of a fine matrix. -/
def STeeMg (n : ℕ) (u : ℝ) (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    {m : ℕ} (σ : Fin m → Bool) (a a' : Fin m → Zd d (sz.L n)) : ℂ :=
  (((sz.W n : ℕ) : ℂ) ^ d) * ∑ k ∈ Finset.Icc 1 m, ∑ b : Zd d (sz.L n), ∑ b' : Zd d (sz.L n),
    Cm.S n b b' * STLIMg Cm n u H (STeeLoop (List.ofFn σ) (List.ofFn a) (List.ofFn a') k b b')

/-- `STgAN`: `A_k = (𝓛-𝒦)^{(m)}_{u_k,σ,a}(H_k)`, the observable of the grid walk, loop length `m`. -/
def STgANg (s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) {m : ℕ} (σ : Fin m → Bool) (a : Fin m → Zd d (sz.L n)) (k : ℕ)
    (ω : PathΩ sz) : ℂ :=
  STLKIMg Cm n (gridTime s t K n k) (Cm.Hpath s t K n k ω) (KLloopOf d (sz.L n) σ a)

/-- `STgDriftN`: the drift of `(𝓛-𝒦)^{(m)}` ((3.8) `eq_L-Keee`) at the grid state (the call of `ThetaN` reads the
carrier `Cm.toFlowFM` and the charges `σ`). -/
def STgDriftNg (s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) {m : ℕ} (σ : Fin m → Bool) (a : Fin m → Zd d (sz.L n)) (k : ℕ)
    (ω : PathΩ sz) : ℂ :=
  Step2Gen_ThetaN Cm.toFlowFM n σ (gridTime s t K n k)
      (fun a' => STLKIMg Cm n (gridTime s t K n k) (Cm.Hpath s t K n k ω) (KLloopOf d (sz.L n) σ a')) a +
    ∑ l ∈ Finset.Icc 3 m, STksimLKMg Cm n (gridTime s t K n k) (Cm.Hpath s t K n k ω) l
      (KLloopOf d (sz.L n) σ a) +
    STelklkMg Cm n (gridTime s t K n k) (Cm.Hpath s t K n k ω) (KLloopOf d (sz.L n) σ a) +
    STegtMg Cm n (gridTime s t K n k) (Cm.Hpath s t K n k ω) (KLloopOf d (sz.L n) σ a)

/-- `STeeUM`: the weighted quadratic-variation loop `((𝒰_{v,w,σ} ⊗ 𝒰_{v,w,σ̄}) ∘ (ℰ⊗ℰ)^{M,(m)}_{v,σ})_{a,a}` (`uKer` at
`(σ_i, σ_{i+1})` and `(!σ_i, !σ_{i+1})`). -/
def STeeUMg (n : ℕ) (v w : ℝ) (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    {m : ℕ} (σ : Fin m → Bool) (a : Fin m → Zd d (sz.L n)) : ℂ :=
  ∑ b : Fin m → Zd d (sz.L n), ∑ b' : Fin m → Zd d (sz.L n),
    (∏ i, Step2Gen_uKer Cm.toFlowFM n (σ i) (σ (finRotate m i)) v w (a i) (b i)) *
      (∏ i, Step2Gen_uKer Cm.toFlowFM n (!σ i) (!σ (finRotate m i)) v w (a i) (b' i)) *
        STeeMg Cm n v H σ b b'

end ListLoops

/-- `STGridRepNAt`: `Sol_CalL` and `lem:DIfREP` on the grid, every loop length `m` (`(int_K-L_ST)`, `(aaswtghh)`,
`(alu9_STime)`), over a carrier `(Flow, mk, T0)` with `mk` valued in `Step2Mat`. -/
def STGridRepNAtgL (d m : ℕ) (C₀ : ℝ) (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop)
    (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), Step2Mat sz) (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) : Prop :=
  ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), Flow sz κ ε 𝔠 𝔡 z →
      ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n ≤ t n) → (∀ n, t n ≤ T0 sz z n) →
        ∀ D : ℝ, 0 < D → ∃ CK : ℝ, 0 ≤ CK ∧
          ∀ K : ℕ → ℕ, (∀ n, K n ≠ 0) → (∀ᶠ n in atTop, ((sz.size n : ℕ) : ℝ) ^ CK ≤ K n) →
            ∃ Mart Rem : ∀ n, ((Fin m → Bool) × (Fin m → Zd d (sz.L n))) → ℕ → PathΩ sz → ℂ,
              (∀ (n : ℕ) (i : (Fin m → Bool) × (Fin m → Zd d (sz.L n))), ∀ᵐ ω ∂((mk sz z).Pp), ∀ k, k ≤ K n →
                STgANg (mk sz z) s t K n i.1 i.2 k ω =
                  STgANg (mk sz z) s t K n i.1 i.2 0 ω +
                    ((gridStep s t K n : ℝ) : ℂ) *
                      ∑ j ∈ Finset.range k, STgDriftNg (mk sz z) s t K n i.1 i.2 j ω +
                    Rem n i k ω + Mart n i k ω) ∧
              (∀ᶠ n in atTop, ∀ i : (Fin m → Bool) × (Fin m → Zd d (sz.L n)), ∀ᵐ ω ∂((mk sz z).Pp), ∀ k, k ≤ K n →
                ‖Rem n i k ω‖ ≤ ((sz.size n : ℕ) : ℝ) ^ C₀ * Real.sqrt (gridStep s t K n)) ∧
              (∀ ε' : ℝ, 0 < ε' → ∀ᶠ n in atTop, ∀ i : (Fin m → Bool) × (Fin m → Zd d (sz.L n)),
                (mk sz z).Pp {ω | ∃ k, k ≤ K n ∧
                  ((sz.size n : ℕ) : ℝ) ^ ε' *
                      (∑ j ∈ Finset.range k, gridStep s t K n *
                        ‖STeeMg (mk sz z) n (gridTime s t K n j) ((mk sz z).Hpath s t K n j ω)
                          i.1 i.2 i.2‖ + ((sz.size n : ℕ) : ℝ) ^ (-D)) ^ (1 / 2 : ℝ) <
                    ‖Mart n i k ω‖} ≤ ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-D))) ∧
              (∀ ε' : ℝ, 0 < ε' → ∀ᶠ n in atTop, ∀ i : (Fin m → Bool) × (Fin m → Zd d (sz.L n)),
                (mk sz z).Pp {ω | ∃ k, k ≤ K n ∧
                  ((sz.size n : ℕ) : ℝ) ^ ε' *
                      (∑ j ∈ Finset.range k, gridStep s t K n *
                        ‖STeeUMg (mk sz z) n (gridTime s t K n j) (gridTime s t K n k)
                          ((mk sz z).Hpath s t K n j ω) i.1 i.2‖ + ((sz.size n : ℕ) : ℝ) ^ (-D)) ^
                          (1 / 2 : ℝ) <
                    ‖∑ j ∈ Finset.range k,
                      Step2Gen_UN (mk sz z).toFlowFM n i.1
                        (gridTime s t K n j) (gridTime s t K n k)
                        (fun b => Mart n (i.1, b) (j + 1) ω - Mart n (i.1, b) j ω) i.2‖} ≤
                  ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-D)))

/-! ## 7. The energy-quantified statements `STNewKLKAt`, `STNewKLK`, `STK2decay` -/

/-- **`STK2decaygL'`**: `STK2decay` with the hypothesis `|E| ≤ 2 - κ` replaced by `κ ≤ Im m` (the one-loop value of
the family at the constant sequence `fun _ => E`).  `K` is a carrier field: no kernel enters. -/
def STK2decaygL' (d : ℕ) (mk : ∀ sz : Sizes d, (ℕ → ℝ) → Step2Mat sz) : Prop :=
  3 ≤ d → ∀ κ 𝔡 : ℝ, 0 < κ → 0 < 𝔡 → ∃ C : ℝ, 0 < C ∧
    ∀ (sz : Sizes d) (n : ℕ) (E u D : ℝ), 0 < sz.lam n → sz.lam n ≤ 𝔡⁻¹ → κ ≤ ((mk sz (fun _ => E)).m n).im →
      0 ≤ u → u < 1 → 0 ≤ D → ∀ (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)),
        ‖(mk sz (fun _ => E)).K n u σ a‖ ≤ C * STprof sz n u D ((sz.L n : ℕ) : ℝ) (a 0) (a 1)

end RBM.BA
