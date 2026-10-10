/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Chain.Carrier
import RBM3D.Induction.Step2Defs

/-!
# The Step 2 vocabulary over the carrier (BA-T row T8, ticket T2386)

Design `docs/reports/T2379-design.md` §2 (L1), §3 (row T8); probe
`t/T2379:RBM3D/Probe/T2379Pins.lean:39-104`; pilot
`t/T2326:RBM3D/Probe/T2326PilotStep2.lean:69-178`.  `Induction/Step2Defs.lean` is **not**
edited: this file reads each of its definitions that mentions a band object over a carrier, and
bridges the two by `rfl` / `Iff.rfl`.

* **Data.** `Step2Mat sz extends FlowFM sz` (no facts): `LM` (`𝓛^{(k)}` of a fine matrix),
  `GMM`, the list-indexed `LIM`, `KI`, the grid law `Pp` and the grid walk `Hpath`.
  `Step2Data sz extends Step2Mat sz` adds `T0`, the setting `flowOK` and three facts (`flowOK_adm`,
  `flowOK_T`, `L_swap`).  Pilot fields left to T7 / T1: `ev1`-`ev4`, `Good`, `ident`,
  `martTail`, `pLWT`, `pEMe`, `pNew`.
* **Names.** the band name plus `g` (data) or `gL` (a `Prop`).  A pin that quantifies over the
  flow takes the shape `(law, Flow, mk, T0)` of `STMainIndG`; the matrix-level pins take `mk`
  valued in `Step2Mat`; the energy-quantified pins `STNewKLKAt`, `STNewKLK`, `STK2decay` take a
  family `mk : ∀ sz, (ℕ → ℝ) → Step2Mat sz` read at `fun _ => E`.
* **Bridges.** `bandStep2Mat sz E`, `bandStep2Data sz z` are the band instances; every generic
  name has a bridge `bandStep2_<band name>` or `bandFM_<band name>` (`rfl` / `Iff.rfl`; the one
  exception is `bandFM_STGijGEX`).  The probe's family `STAvgUgL`, ..., `STStep2G`,
  `STStep2_iff` is section 4.
* `STJhatg`, `STLWassmExpgL` moved here from `BA/FlowPins.lean` (`STLWTgL`, `STEMn2ExpgL` read
  them, and this file cannot import `BA/FlowPins`).
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

/-- The random control `Ĵ^ℓ_{u,D}` (`(defCALJ)`, `3_5:365`): `max |(𝓛-𝒦)^{(2)}_{u,σ,a}| / [W^{-d} 𝒯̃^ℓ_{u,D}(|a₁-a₂|)]`. -/
def STJhatg (n : ℕ) (D ℓ u : ℝ) (ω : sz.SeqΩ) : ℝ :=
  Finset.univ.sup' ⟨((fun _ => true), (fun _ => 0)), Finset.mem_univ _⟩
    (fun p : (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)) =>
      ‖C.L n u p.1 p.2 ω - C.K n u p.1 p.2‖ / STprof sz n u D ℓ (p.2 0) (p.2 1))

/-- `(eq:LW_assm_exp)` (`3_5:409`): `𝓛^{(2)}_{t,σ,(a,b)} ≺ W^{-d} 𝒯̃^ℓ_{t,D}(|a-b|)`, `σ ∈ {(+,-),(-,+)}`. -/
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
three facts that the generic proofs of `LocalAvg1/2` read (admissibility, `T0 < 1`, trace cyclicity of `𝓛^{(2)}`). -/
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

/-- **The band instance of `Step2Mat` at the energy sequence `E`** (every field is the merged band object). -/
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


/-! ## 3. The matrix-level and model-level vocabulary (`Step2Defs` §1, §2.2) -/

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

/-- `STJhatM`: the random control `Ĵ^ℓ_{u,D}` of a fine matrix `H`. -/
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

/-- The propagator `Θ_ξ = (1 - ξ S)⁻¹` of a kernel `S` (the band `Theta d L g` is the case `S = SB d L g`). -/
def Step2Gen_Theta {Λ : Type*} [Fintype Λ] [DecidableEq Λ] (S : Matrix Λ Λ ℂ) (ξ : ℂ) : Matrix Λ Λ ℂ :=
  Ring.inverse (1 - ξ • S)

/-- `STthetaOp`: the operator `Θ^{(2)}_{u,σ}` of `DefTHUST` acting on a tensor `A`. -/
def STthetaOpg (n : ℕ) (u : ℝ) (σ : Fin 2 → Bool) (A : (Fin 2 → Zd d (sz.L n)) → ℂ)
    (a : Fin 2 → Zd d (sz.L n)) : ℂ :=
  ∑ i : Fin 2, ∑ b : Zd d (sz.L n),
    (STmsigg Cm n (σ 0) * STmsigg Cm n (σ 1)) *
      ((Cm.S n * Step2Gen_Theta (Cm.S n) ((u : ℂ) * (STmsigg Cm n (σ 0) * STmsigg Cm n (σ 1)))) (a i) b) *
      A (Function.update a i b)

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

theorem bandStep2_STmsig (σ : Bool) : STmsig (E n) σ = STmsigg (bandStep2Mat sz E) n σ := rfl
theorem bandStep2_STLM {k : ℕ} (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)) :
    STLM sz n (E n) u H σ a = STLMg (bandStep2Mat sz E) n u H σ a := rfl
theorem bandStep2_STLKM {k : ℕ} (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)) :
    STLKM sz n (E n) u H σ a = STLKMg (bandStep2Mat sz E) n u H σ a := rfl
theorem bandStep2_STJhatM (D ℓ : ℝ) :
    STJhatM sz n (E n) D ℓ u H = STJhatMg (bandStep2Mat sz E) n D ℓ u H := rfl
theorem bandStep2_STavgM (σ : Bool) (a : Zd d (sz.L n)) :
    STavgM sz n (E n) u H σ a = STavgMg (bandStep2Mat sz E) n u H σ a := rfl
theorem bandStep2_STEGtM (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) :
    STEGtM sz n (E n) u H σ a = STEGtMg (bandStep2Mat sz E) n u H σ a := rfl
theorem bandStep2_STELKLKM (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) :
    STELKLKM sz n (E n) u H σ a = STELKLKMg (bandStep2Mat sz E) n u H σ a := rfl
theorem bandStep2_STthetaOp (σ : Fin 2 → Bool) (A : (Fin 2 → Zd d (sz.L n)) → ℂ) (a : Fin 2 → Zd d (sz.L n)) :
    STthetaOp sz n (E n) u σ A a = STthetaOpg (bandStep2Mat sz E) n u σ A a := rfl
theorem bandStep2_STEEkM (k : Fin 2) (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) :
    STEEkM sz n (E n) u H k σ a = STEEkMg (bandStep2Mat sz E) n u H k σ a := rfl
theorem bandStep2_STEEM (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) :
    STEEM sz n (E n) u H σ a = STEEMg (bandStep2Mat sz E) n u H σ a := rfl
theorem bandStep2_STGMM (x y : Idx d (sz.L n) (sz.W n)) :
    STGMM sz n (E n) u H x y = STGMMg (bandStep2Mat sz E) n u H x y := rfl

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

/-- `(eq:LW_assm)` (`3_5:388`): `𝓛^{(2)}_{t,σ,(a,b)} ≺ Ψ_t²(|a-b|)` for `σ ∈ {(+,-),(-,+)}`. -/
def STLWassmgL (t : ℕ → ℝ) (Ψ : ℕ → ℕ → ℝ) : Prop :=
  PrecL sz μ (U := fun n => {σ : Fin 2 → Bool // σ 0 ≠ σ 1} × (Fin 2 → Zd d (sz.L n)))
    (fun n p ω => ‖C.L n (t n) p.1.1 p.2 ω‖)
    (fun n p _ => (Ψ n (zdistInf d (sz.L n) (p.2 0 - p.2 1))) ^ 2)

end Model

section ModelBridge

variable {d : ℕ} (sz : Sizes d) (E : ℕ → ℝ)

theorem bandFM_STJhat (n : ℕ) (D ℓ u : ℝ) (ω : sz.SeqΩ) :
    STJhat sz n (E n) D ℓ u ω = STJhatg (bandFM sz E) n D ℓ u ω := rfl
theorem bandFM_STEGt (n : ℕ) (t : ℝ) (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) (ω : sz.SeqΩ) :
    STEGt sz n (E n) t σ a ω = STEGtg (bandFM sz E) n t σ a ω := rfl
theorem bandFM_STLWassm (t : ℕ → ℝ) (Ψ : ℕ → ℕ → ℝ) :
    STLWassm sz E t Ψ ↔ STLWassmgL (bandFM sz E) (Sizes.seqP sz) t Ψ := Iff.rfl

end ModelBridge


/-! ## 4. The Step 2 pins over a carrier `(law, Flow, mk, T0)` (`Step2Defs` §2.1, §2.2, §2.5; probe `t/T2379:39-104`) -/

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

/-- `STStep2Local`: `(Gt_bound_flow)` (`1_2:1343`) uniformly in `u ∈ [s,t]` (the statement of `STLocalEntryUgL`). -/
def STStep2LocalgL (s t : ℕ → ℝ) : Prop := STLocalEntryUgL C μ s t

/-- `STStep2Avg`: `(Gt_avgbound_flow)` (`1_2:1345`) uniformly in `u ∈ [s,t]`, `tr((G_u - M)E_a) = 𝓛^{(1)} - m`. -/
def STStep2AvggL (s t : ℕ → ℝ) : Prop :=
  PrecL sz μ (U := fun n => TimeIcc s t n × Zd d (sz.L n))
    (fun n p ω => ‖C.L n (p.1 : ℝ) (fun _ : Fin 1 => true) (fun _ => p.2) ω - C.m n‖)
    (fun n p _ => sz.Bctl n (p.1 : ℝ))

/-- `STStep2Decay`: `(Eq:Gdecay_w)` (`1_2:1349`) uniformly in `u ∈ [s,t]`, with the loss exponent `Cd`. -/
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

section StepBridge

variable {d : ℕ} (sz : Sizes d) (E s t : ℕ → ℝ)

theorem bandFM_STAvgU : STAvgU sz E s t ↔ STAvgUgL (bandFM sz E) (Sizes.seqP sz) s t := Iff.rfl
theorem bandFM_STLocalEntryU : STLocalEntryU sz E s t ↔ STLocalEntryUgL (bandFM sz E) (Sizes.seqP sz) s t :=
  Iff.rfl
theorem bandFM_STGdecayW (Cd : ℝ) : STGdecayW sz E s t Cd ↔ STGdecayWgL (bandFM sz E) (Sizes.seqP sz) s t Cd :=
  Iff.rfl
theorem bandFM_STStep2Concl (Cd : ℝ) :
    STStep2Concl sz E s t Cd ↔ STStep2ConclgL (bandFM sz E) (Sizes.seqP sz) s t Cd := Iff.rfl
theorem bandFM_STStep2Local : STStep2Local sz E s t ↔ STStep2LocalgL (bandFM sz E) (Sizes.seqP sz) s t := Iff.rfl
theorem bandFM_STStep2Avg : STStep2Avg sz E s t ↔ STStep2AvggL (bandFM sz E) (Sizes.seqP sz) s t := Iff.rfl
theorem bandFM_STStep2Decay (Cd : ℝ) :
    STStep2Decay sz Cd E s t ↔ STStep2DecaygL (bandFM sz E) (Sizes.seqP sz) Cd s t := Iff.rfl
theorem bandFM_STStep2LocalPT : STStep2LocalPT sz E s t ↔ STStep2LocalPTgL (bandFM sz E) (Sizes.seqP sz) s t :=
  Iff.rfl
theorem bandFM_STStep2AvgPT : STStep2AvgPT sz E s t ↔ STStep2AvgPTgL (bandFM sz E) (Sizes.seqP sz) s t := Iff.rfl
theorem bandFM_STStep2DecayPT (Cd : ℝ) :
    STStep2DecayPT sz Cd E s t ↔ STStep2DecayPTgL (bandFM sz E) (Sizes.seqP sz) Cd s t := Iff.rfl
theorem bandFM_STL2decayPT : STL2decayPT sz E s t ↔ STL2decayPTgL (bandFM sz E) (Sizes.seqP sz) s t := Iff.rfl

end StepBridge

section StepG

variable (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ)
  (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop)
  (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz) (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ)

/-- **Step 2 over a carrier** `(law, Flow, mk, T0)` (the shape of `STMainIndG`; probe `t/T2379:78-90`). -/
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

/-- `STEMn2Exp`: `lem: EMn2_N`, third estimate `(eq:MG_conclusion3)`, with the random control `Ĵ`. -/
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

theorem STStep2_iff :
    STStep2 d ↔ STStep2G d (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
      (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n)) := Iff.rfl
theorem bandFM_STNetLift2 :
    STNetLift2 d ↔ STNetLift2gL d (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
      (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n)) := Iff.rfl
theorem bandFM_STLocalAvgOfL2 :
    STLocalAvgOfL2 d ↔ STLocalAvgOfL2gL d (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
      (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n)) := Iff.rfl
theorem bandFM_STOptL2 :
    STOptL2 d ↔ STOptL2gL d (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
      (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n)) := Iff.rfl
theorem bandFM_STScaleExists :
    STScaleExists d ↔ STScaleExistsgL d (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z) (fun _ z n => lemT (z n)) := Iff.rfl
theorem bandFM_STLWB :
    STLWB d ↔ STLWBgL d (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
      (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n)) := Iff.rfl
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


/-! ## 5. The forms of `lem_GbEXP` (`Induction/Defs.lean` §1b), the grid, the list-indexed loops, the energy pins -/

section GbEXPForms

variable {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (μ : Measure sz.SeqΩ)

/-- `STindMax`: the indicator of `{‖G_τ - M‖_max ≤ A}`. -/
def STindMaxg (n : ℕ) (τ A : ℝ) (ω : sz.SeqΩ) : ℝ :=
  if ∀ x y : Idx d (sz.L n) (sz.W n), ‖C.GM n τ ω x y‖ ≤ A then 1 else 0

/-- `STgexRHS`: the right side of `(GijGEX)` (`3_5:24-26`). -/
def STgexRHSg (n : ℕ) (τ : ℝ) (ω : sz.SeqΩ) (a b : Zd d (sz.L n)) : ℝ :=
  (∑ σ ∈ ({![true, false], ![false, true]} : Finset (Fin 2 → Bool)),
    ∑ a' ∈ Finset.univ.filter (fun a' : Zd d (sz.L n) => zdistInf d (sz.L n) (a' - a) ≤ 1),
      ∑ b' ∈ Finset.univ.filter (fun b' : Zd d (sz.L n) => zdistInf d (sz.L n) (b' - b) ≤ 1),
        ‖C.L n τ σ ![a', b'] ω‖) +
    (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (if zdistInf d (sz.L n) (a - b) ≤ 1 then 1 else 0)

/-- `STGiiGEX`: `(GiiGEX)` (`3_5:21`) over a carrier. -/
def STGiiGEXgL (t : ℕ → ℝ) (ε₀ : ℝ) : Prop :=
  PrecL sz μ (U := fun n => Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n))
    (fun n p ω => STindMaxg C n (t n) (((sz.W n : ℕ) : ℝ) ^ (-ε₀)) ω * ‖C.GM n (t n) ω p.1 p.2‖ ^ 2)
    (fun n _ ω => STmaxLoop2g C n (t n) ω)

/-- `STGijGEX`: `(GijGEX)` (`3_5:24`) over a carrier, stated for `(G_t - M)_{xy}` (`x ≠ y`), not `(G_t)_{xy}`: at the
band `M` is diagonal and the two agree (`bandFM_STGijGEX`); at a carrier with a non-diagonal `M` they differ (T2386a). -/
def STGijGEXgL (t : ℕ → ℝ) (ε₀ : ℝ) : Prop :=
  PrecL sz μ
    (U := fun n => {p : Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n) // p.1 ≠ p.2})
    (fun n p ω => STindMaxg C n (t n) (((sz.W n : ℕ) : ℝ) ^ (-ε₀)) ω * ‖C.GM n (t n) ω p.1.1 p.1.2‖ ^ 2)
    (fun n p ω => STgexRHSg C n (t n) ω (STblk sz n p.1.1) (STblk sz n p.1.2))

/-- `STGavLGEX`: `(GavLGEX)` (`3_5:33`) under `(initialGT2)` over a carrier. -/
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

theorem bandFM_STindMax (n : ℕ) (τ A : ℝ) (ω : sz.SeqΩ) :
    STindMax sz n (E n) τ A ω = STindMaxg (bandFM sz E) n τ A ω := rfl
theorem bandFM_STgexRHS (n : ℕ) (τ : ℝ) (ω : sz.SeqΩ) (a b : Zd d (sz.L n)) :
    STgexRHS sz n (E n) τ ω a b = STgexRHSg (bandFM sz E) n τ ω a b := rfl
theorem bandFM_STGiiGEX : STGiiGEX sz E t ε₀ ↔ STGiiGEXgL (bandFM sz E) (Sizes.seqP sz) t ε₀ := Iff.rfl
theorem bandFM_STGavLGEX : STGavLGEX sz E t ε₀ ↔ STGavLGEXgL (bandFM sz E) (Sizes.seqP sz) t ε₀ := Iff.rfl
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

section Grid

variable {d : ℕ} {sz : Sizes d} (Cm : Step2Mat sz)

/-- `STgA`: `A_k = (𝓛-𝒦)^{(2)}_{u_k,σ,a}(H_k)`, the observable of the grid walk. -/
def STgAg (s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) (k : ℕ)
    (ω : PathΩ sz) : ℂ :=
  STLKMg Cm n (gridTime s t K n k) (Cm.Hpath s t K n k ω) σ a

/-- `STgDrift`: the drift of `(𝓛-𝒦)^{(2)}` (`(LK_simple)`, `3_5:360-362`) at the grid state. -/
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

/-- `STGridMartAt`: `Sol_CalL` + `lem:DIfREP` (`3_5:134-148`, `218-228`), the grid decomposition and the martingale tail,
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

/-- `STGridMart`: the pin, `∃ C₀` with `STGridMartAtgL`. -/
def STGridMartgL (d : ℕ) (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop)
    (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), Step2Mat sz) (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) : Prop :=
  ∃ C₀ : ℝ, 0 ≤ C₀ ∧ STGridMartAtgL d C₀ Flow mk T0

section GridBridge

variable {d : ℕ} (sz : Sizes d) (E s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ)

theorem bandStep2_STgA (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) (k : ℕ) (ω : PathΩ sz) :
    STgA sz s t K n (E n) σ a k ω = STgAg (bandStep2Mat sz E) s t K n σ a k ω := rfl
theorem bandStep2_STgDrift (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) (k : ℕ) (ω : PathΩ sz) :
    STgDrift sz s t K n (E n) σ a k ω = STgDriftg (bandStep2Mat sz E) s t K n σ a k ω := rfl
theorem bandStep2_STstopIdx (D : ℝ) (ℓ : ℕ → ℝ → ℝ) :
    STstopIdx sz s t K E D ℓ n = STstopIdxg (bandStep2Mat sz E) s t K D ℓ n := rfl
theorem bandStep2_STGridMartAt (C₀ : ℝ) :
    STGridMartAt d C₀ ↔ STGridMartAtgL d C₀ (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
      (fun sz z => bandStep2Mat sz (STflowE z)) (fun _ z n => lemT (z n)) := Iff.rfl
theorem bandStep2_STGridMart :
    STGridMart d ↔ STGridMartgL d (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
      (fun sz z => bandStep2Mat sz (STflowE z)) (fun _ z n => lemT (z n)) := Iff.rfl

end GridBridge


/-! ## 6. The list-indexed loops of `Step2Defs` §3 (`STLIM`, ..., `STGridRepN`) -/

section Kernels

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] (S : Matrix Λ Λ ℂ)

/-- `thetaKer`: `μ S Θ_{tμ}` (`(def:op_thn)`) of a kernel `S`. -/
def Step2Gen_thetaKer (μ : ℂ) (t : ℝ) : Matrix Λ Λ ℂ := (μ • S) * Step2Gen_Theta S ((t : ℂ) * μ)

/-- `uKer`: `(1 - s μ S) Θ_{tμ}` (`(def_Ustz)`) of a kernel `S`. -/
def Step2Gen_uKer (μ : ℂ) (s t : ℝ) : Matrix Λ Λ ℂ := (1 - ((s : ℂ) * μ) • S) * Step2Gen_Theta S ((t : ℂ) * μ)

end Kernels

section KernelsN

variable {d L : ℕ} [NeZero L] (S : Matrix (Zd d L) (Zd d L) ℂ)

/-- `ThetaN`: the operator `Θ^{(n)}_{t,σ}` on `n`-index tensors (`(def:op_thn)`) of a kernel `S`. -/
def Step2Gen_ThetaN {n : ℕ} (m : Fin n → ℂ) (t : ℝ) (A : (Fin n → Zd d L) → ℂ) : (Fin n → Zd d L) → ℂ :=
  fun a => ∑ i, ∑ b, Step2Gen_thetaKer S (cycProd m i) t (a i) b * A (Function.update a i b)

/-- `UN`: the evolution kernel `U^{(n)}_{s,t,σ}` on `n`-index tensors (`(def_Ustz)`) of a kernel `S`. -/
def Step2Gen_UN {n : ℕ} (m : Fin n → ℂ) (s t : ℝ) (A : (Fin n → Zd d L) → ℂ) : (Fin n → Zd d L) → ℂ :=
  fun a => ∑ b : Fin n → Zd d L, (∏ i, Step2Gen_uKer S (cycProd m i) s t (a i) (b i)) * A b

end KernelsN

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

/-- `STgDriftN`: the drift of `(𝓛-𝒦)^{(m)}` (`(eq_L-Keee)`, `3_5:75-100`) at the grid state. -/
def STgDriftNg (s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) {m : ℕ} (σ : Fin m → Bool) (a : Fin m → Zd d (sz.L n)) (k : ℕ)
    (ω : PathΩ sz) : ℂ :=
  Step2Gen_ThetaN (Cm.S n) (fun i => STmsigg Cm n (σ i)) (gridTime s t K n k)
      (fun a' => STLKIMg Cm n (gridTime s t K n k) (Cm.Hpath s t K n k ω) (KLloopOf d (sz.L n) σ a')) a +
    ∑ l ∈ Finset.Icc 3 m, STksimLKMg Cm n (gridTime s t K n k) (Cm.Hpath s t K n k ω) l
      (KLloopOf d (sz.L n) σ a) +
    STelklkMg Cm n (gridTime s t K n k) (Cm.Hpath s t K n k ω) (KLloopOf d (sz.L n) σ a) +
    STegtMg Cm n (gridTime s t K n k) (Cm.Hpath s t K n k ω) (KLloopOf d (sz.L n) σ a)

/-- `STeeUM`: the weighted quadratic-variation loop `((𝒰_{v,w,σ} ⊗ 𝒰_{v,w,σ̄}) ∘ (ℰ⊗ℰ)^{M,(m)}_{v,σ})_{a,a}`. -/
def STeeUMg (n : ℕ) (v w : ℝ) (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    {m : ℕ} (σ : Fin m → Bool) (a : Fin m → Zd d (sz.L n)) : ℂ :=
  ∑ b : Fin m → Zd d (sz.L n), ∑ b' : Fin m → Zd d (sz.L n),
    (∏ i, Step2Gen_uKer (Cm.S n) (cycProd (fun i => STmsigg Cm n (σ i)) i) v w (a i) (b i)) *
      (∏ i, Step2Gen_uKer (Cm.S n) (cycProd (fun i => STmsigg Cm n (!σ i)) i) v w (a i) (b' i)) *
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
                      Step2Gen_UN ((mk sz z).S n) (fun i' => STmsigg (mk sz z) n (i.1 i'))
                        (gridTime s t K n j) (gridTime s t K n k)
                        (fun b => Mart n (i.1, b) (j + 1) ω - Mart n (i.1, b) j ω) i.2‖} ≤
                  ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-D)))

/-- `STGridRepN`: the pin, every `m ≥ 2` has `C₀` with `STGridRepNAtgL`. -/
def STGridRepNgL (d : ℕ) (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop)
    (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), Step2Mat sz) (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) : Prop :=
  ∀ m : ℕ, 2 ≤ m → ∃ C₀ : ℝ, 0 ≤ C₀ ∧ STGridRepNAtgL d m C₀ Flow mk T0

section ListBridge

variable {d : ℕ} (sz : Sizes d) (E : ℕ → ℝ) (n : ℕ) (u : ℝ)
  (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)

theorem bandStep2_STLIM (I : LoopIdx (Zd d (sz.L n))) : STLIM sz n (E n) u H I = STLIMg (bandStep2Mat sz E) n u H I := rfl
theorem bandStep2_STLKIM (I : LoopIdx (Zd d (sz.L n))) :
    STLKIM sz n (E n) u H I = STLKIMg (bandStep2Mat sz E) n u H I := rfl
theorem bandStep2_STksimLKM (l : ℕ) (I : LoopIdx (Zd d (sz.L n))) :
    STksimLKM sz n (E n) u H l I = STksimLKMg (bandStep2Mat sz E) n u H l I := rfl
theorem bandStep2_STelklkM (I : LoopIdx (Zd d (sz.L n))) :
    STelklkM sz n (E n) u H I = STelklkMg (bandStep2Mat sz E) n u H I := rfl
theorem bandStep2_STavgErrM (σ : Bool) (a : Zd d (sz.L n)) :
    STavgErrM sz n (E n) u H σ a = STavgErrMg (bandStep2Mat sz E) n u H σ a := rfl
theorem bandStep2_STegtM (I : LoopIdx (Zd d (sz.L n))) :
    STegtM sz n (E n) u H I = STegtMg (bandStep2Mat sz E) n u H I := rfl
theorem bandStep2_STeeM {m : ℕ} (σ : Fin m → Bool) (a a' : Fin m → Zd d (sz.L n)) :
    STeeM sz n (E n) u H σ a a' = STeeMg (bandStep2Mat sz E) n u H σ a a' := rfl
theorem bandStep2_STgAN (s t : ℕ → ℝ) (K : ℕ → ℕ) {m : ℕ} (σ : Fin m → Bool) (a : Fin m → Zd d (sz.L n)) (k : ℕ)
    (ω : PathΩ sz) : STgAN sz s t K n (E n) σ a k ω = STgANg (bandStep2Mat sz E) s t K n σ a k ω := rfl
theorem bandStep2_STgDriftN (s t : ℕ → ℝ) (K : ℕ → ℕ) {m : ℕ} (σ : Fin m → Bool) (a : Fin m → Zd d (sz.L n))
    (k : ℕ) (ω : PathΩ sz) :
    STgDriftN sz s t K n (E n) σ a k ω = STgDriftNg (bandStep2Mat sz E) s t K n σ a k ω := rfl
theorem bandStep2_STeeUM (v w : ℝ) {m : ℕ} (σ : Fin m → Bool) (a : Fin m → Zd d (sz.L n)) :
    STeeUM sz n (E n) v w H σ a = STeeUMg (bandStep2Mat sz E) n v w H σ a := rfl
theorem bandStep2_STGridRepNAt (m : ℕ) (C₀ : ℝ) :
    STGridRepNAt d m C₀ ↔ STGridRepNAtgL d m C₀ (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
      (fun sz z => bandStep2Mat sz (STflowE z)) (fun _ z n => lemT (z n)) := Iff.rfl
theorem bandStep2_STGridRepN :
    STGridRepN d ↔ STGridRepNgL d (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
      (fun sz z => bandStep2Mat sz (STflowE z)) (fun _ z n => lemT (z n)) := Iff.rfl

end ListBridge

/-! ## 7. The energy-quantified pins `STNewKLKAt`, `STNewKLK`, `STK2decay` -/

/-- `STNewKLKAt`: `lem:newKLK` (`3_5:371-378`) at the constants `C, δ₀`.  The pin quantifies over every energy `E` and every
`H`: the carrier is the family `mk` of `Step2Mat`, read at the constant sequence `fun _ => E`. -/
def STNewKLKAtgL (d : ℕ) (κ 𝔡 C δ₀ : ℝ) (mk : ∀ sz : Sizes d, (ℕ → ℝ) → Step2Mat sz) : Prop :=
  ∀ (sz : Sizes d) (n : ℕ) (E u D ℓ : ℝ), 0 < sz.lam n → sz.lam n ≤ 𝔡⁻¹ → |E| ≤ 2 - κ →
    0 ≤ u → u < 1 → 0 ≤ D → 0 ≤ ℓ → ℓ ≤ ((sz.L n : ℕ) : ℝ) →
    ∀ H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ, H.IsHermitian →
      (∀ x y, ‖STGMMg (mk sz (fun _ => E)) n u H x y‖ ≤ δ₀) →
      ∀ (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)),
        ‖STthetaOpg (mk sz (fun _ => E)) n u σ (STLKMg (mk sz (fun _ => E)) n u H σ) a‖ ≤
            C / (1 - u) * STJhatMg (mk sz (fun _ => E)) n D ℓ u H * STprof sz n u D ℓ (a 0) (a 1) ∧
        ‖STELKLKMg (mk sz (fun _ => E)) n u H σ a‖ ≤
            C / (1 - u) * (STJhatMg (mk sz (fun _ => E)) n D ℓ u H +
              STJhatMg (mk sz (fun _ => E)) n D ℓ u H ^ 2 * (if 1 ≤ ℓ then 1 else 0)) *
              STprof sz n u D ℓ (a 0) (a 1)

/-- `STNewKLK`: `lem:newKLK`, the pin: `∃ C, δ₀` with `STNewKLKAtgL`. -/
def STNewKLKgL (d : ℕ) (mk : ∀ sz : Sizes d, (ℕ → ℝ) → Step2Mat sz) : Prop :=
  3 ≤ d → ∀ κ 𝔡 : ℝ, 0 < κ → 0 < 𝔡 → ∃ C δ₀ : ℝ, 0 < C ∧ 0 < δ₀ ∧ STNewKLKAtgL d κ 𝔡 C δ₀ mk

/-- `STK2decay`: `(eq:simpleboundK)` (`3_5:518`), the deterministic `𝒦^{(2)}` decay, over the family `mk`. -/
def STK2decaygL (d : ℕ) (mk : ∀ sz : Sizes d, (ℕ → ℝ) → Step2Mat sz) : Prop :=
  3 ≤ d → ∀ κ 𝔡 : ℝ, 0 < κ → 0 < 𝔡 → ∃ C : ℝ, 0 < C ∧
    ∀ (sz : Sizes d) (n : ℕ) (E u D : ℝ), 0 < sz.lam n → sz.lam n ≤ 𝔡⁻¹ → |E| ≤ 2 - κ →
      0 ≤ u → u < 1 → 0 ≤ D → ∀ (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)),
        ‖(mk sz (fun _ => E)).K n u σ a‖ ≤ C * STprof sz n u D ((sz.L n : ℕ) : ℝ) (a 0) (a 1)

section EnergyBridge

variable (d : ℕ)

theorem bandStep2_STNewKLKAt (κ 𝔡 C δ₀ : ℝ) :
    STNewKLKAt d κ 𝔡 C δ₀ ↔ STNewKLKAtgL d κ 𝔡 C δ₀ (fun sz E => bandStep2Mat sz E) := Iff.rfl
theorem bandStep2_STNewKLK : STNewKLK d ↔ STNewKLKgL d (fun sz E => bandStep2Mat sz E) := Iff.rfl
theorem bandStep2_STK2decay : STK2decay d ↔ STK2decaygL d (fun sz E => bandStep2Mat sz E) := Iff.rfl

end EnergyBridge

end RBM.BA

/-! ## 8. Compiled nonempty instances at `d = 3`

The merged preflight sequence `sz0` (`L_n = 4(n+1)`, `W_n = (2(n+1))^5`), the flow `z0` (`κ = ε = 𝔡 = 1/10`, `𝔠 = 1/6`), the
window `s ≡ 0`, `t ≡ 1/16` and `n = 0`.  Every bridge theorem is applied at this data (`bandStep2Mat sz0 (STflowE z0)`, the
band instance); the instance of each generic `LocalAvg` theorem is in `Induction/LocalAvg1.lean`, `LocalAvg2.lean`. -/

namespace RBM.BA.Step2GenInst

open RBM RBM.Path RBM.Gauss RBM.Gauss.Sizes RBM.Gauss.SizesInst RBM.Gauss.InductionDefsInst

/-- `bandStep2Data sz0 z0`: the setting is `flow_z0`, the horizon is `< 1`, the carrier is `bandFM`, and the trace cyclicity
holds (`n = 0`, `t = 0`, `a = b = 0`). -/
example (ω : sz0.SeqΩ) : (bandStep2Data sz0 z0).flowOK (1 / 10) (1 / 10) (1 / 6) (1 / 10) ∧
    (∀ n, (bandStep2Data sz0 z0).T0 n < 1) ∧ (bandStep2Data sz0 z0).toFlowFM = bandFM sz0 (STflowE z0) ∧
    (bandStep2Data sz0 z0).L 0 0 ![true, false] ![0, 0] ω = (bandStep2Data sz0 z0).L 0 0 ![false, true] ![0, 0] ω :=
  ⟨flow_z0, (bandStep2Data sz0 z0).flowOK_T (by norm_num) flow_z0, rfl, (bandStep2Data sz0 z0).L_swap 0 0 0 0 ω⟩

/-- The matrix-level vocabulary (`STmsig`, ..., `STGMM`) at `bandStep2Mat sz0 (STflowE z0)`. -/
example (H : Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ) (A : (Fin 2 → Zd 3 (sz0.L 0)) → ℂ)
    (x y : Idx 3 (sz0.L 0) (sz0.W 0)) :=
  And.intro (bandStep2_STmsig sz0 (STflowE z0) 0 true) <|
  And.intro (bandStep2_STLM sz0 (STflowE z0) 0 0 H (fun _ : Fin 1 => true) (fun _ => 0)) <|
  And.intro (bandStep2_STLKM sz0 (STflowE z0) 0 0 H ![true, false] ![0, 0]) <|
  And.intro (bandStep2_STJhatM sz0 (STflowE z0) 0 0 H 1 0) <|
  And.intro (bandStep2_STavgM sz0 (STflowE z0) 0 0 H true 0) <|
  And.intro (bandStep2_STEGtM sz0 (STflowE z0) 0 0 H ![true, false] ![0, 0]) <|
  And.intro (bandStep2_STELKLKM sz0 (STflowE z0) 0 0 H ![true, false] ![0, 0]) <|
  And.intro (bandStep2_STthetaOp sz0 (STflowE z0) 0 0 ![true, false] A ![0, 0]) <|
  And.intro (bandStep2_STEEkM sz0 (STflowE z0) 0 0 H 0 ![true, false] ![0, 0]) <|
  And.intro (bandStep2_STEEM sz0 (STflowE z0) 0 0 H ![true, false] ![0, 0])
    (bandStep2_STGMM sz0 (STflowE z0) 0 0 H x y)

/-- The model-level vocabulary and the Step 2 conclusion pins at `bandFM sz0 (STflowE z0)`, law `seqP sz0`, window `[0, 1/16]`. -/
example (ω : sz0.SeqΩ) :=
  And.intro (bandFM_STJhat sz0 (STflowE z0) 0 1 0 0 ω) <|
  And.intro (bandFM_STEGt sz0 (STflowE z0) 0 0 ![true, false] ![0, 0] ω) <|
  And.intro (bandFM_STLWassm sz0 (STflowE z0) tInst (fun _ _ => 1)) <|
  And.intro (bandFM_STAvgU sz0 (STflowE z0) sInst tInst) <|
  And.intro (bandFM_STLocalEntryU sz0 (STflowE z0) sInst tInst) <|
  And.intro (bandFM_STGdecayW sz0 (STflowE z0) sInst tInst 1) <|
  And.intro (bandFM_STStep2Concl sz0 (STflowE z0) sInst tInst 1) <|
  And.intro (bandFM_STStep2Local sz0 (STflowE z0) sInst tInst) <|
  And.intro (bandFM_STStep2Avg sz0 (STflowE z0) sInst tInst) <|
  And.intro (bandFM_STStep2Decay sz0 (STflowE z0) sInst tInst 1) <|
  And.intro (bandFM_STStep2LocalPT sz0 (STflowE z0) sInst tInst) <|
  And.intro (bandFM_STStep2AvgPT sz0 (STflowE z0) sInst tInst) <|
  And.intro (bandFM_STStep2DecayPT sz0 (STflowE z0) sInst tInst 1)
    (bandFM_STL2decayPT sz0 (STflowE z0) sInst tInst)

/-- The pins over `(law, Flow, mk, T0)` at `d = 3`: `STStep2` and the closing pins. -/
example := And.intro (STStep2_iff 3) <| And.intro (bandFM_STNetLift2 3) <| And.intro (bandFM_STLocalAvgOfL2 3) <|
  And.intro (bandFM_STOptL2 3) <| And.intro (bandFM_STScaleExists 3) <| And.intro (bandFM_STLWB 3) <|
  And.intro (bandFM_STLWT 3) <| And.intro (bandFM_STEMn2Poly 3) (bandFM_STEMn2Exp 3)

/-- The three forms of `lem_GbEXP` and their helpers at `bandFM sz0 (STflowE z0)`, window `t ≡ 1/16`, `ε₀ = 1/20`;
`bandFM_STGijGEX` is the one bridge that is not `Iff.rfl` (the band `M` is diagonal). -/
example (ω : sz0.SeqΩ) (a b : Zd 3 (sz0.L 0)) :=
  And.intro (bandFM_STindMax sz0 (STflowE z0) 0 (1 / 16) (1 / 20) ω) <|
  And.intro (bandFM_STgexRHS sz0 (STflowE z0) 0 (1 / 16) ω a b) <|
  And.intro (bandFM_STGiiGEX sz0 (STflowE z0) tInst (1 / 20)) <|
  And.intro (bandFM_STGijGEX sz0 (STflowE z0) tInst (1 / 20)) (bandFM_STGavLGEX sz0 (STflowE z0) tInst (1 / 20))

/-- The grid vocabulary and the grid pins at `bandStep2Mat sz0 (STflowE z0)`: the grid of `8` steps on `[0, 1/16]`. -/
example (ω : PathΩ sz0) :=
  And.intro (bandStep2_STgA sz0 (STflowE z0) sInst tInst (fun _ => 8) 0 ![true, false] ![0, 0] 0 ω) <|
  And.intro (bandStep2_STgDrift sz0 (STflowE z0) sInst tInst (fun _ => 8) 0 ![true, false] ![0, 0] 0 ω) <|
  And.intro (bandStep2_STstopIdx sz0 (STflowE z0) sInst tInst (fun _ => 8) 0 1 (fun _ _ => 0)) <|
  And.intro (bandStep2_STGridMartAt (d := 3) 0) (bandStep2_STGridMart (d := 3))

/-- The list-indexed vocabulary (`STLIM`, ..., `STeeUM`) and the pins `STGridRepNAt`, `STGridRepN` at `d = 3`, loop length `3`. -/
example (H : Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ) (I : Loop.LoopIdx (Zd 3 (sz0.L 0)))
    (ω : PathΩ sz0) :=
  And.intro (bandStep2_STLIM sz0 (STflowE z0) 0 0 H I) <|
  And.intro (bandStep2_STLKIM sz0 (STflowE z0) 0 0 H I) <|
  And.intro (bandStep2_STksimLKM sz0 (STflowE z0) 0 0 H 3 I) <|
  And.intro (bandStep2_STelklkM sz0 (STflowE z0) 0 0 H I) <|
  And.intro (bandStep2_STavgErrM sz0 (STflowE z0) 0 0 H true 0) <|
  And.intro (bandStep2_STegtM sz0 (STflowE z0) 0 0 H I) <|
  And.intro (bandStep2_STeeM sz0 (STflowE z0) 0 0 H ![true, false, true] ![0, 0, 0] ![0, 0, 0]) <|
  And.intro (bandStep2_STgAN sz0 (STflowE z0) 0 sInst tInst (fun _ => 8) ![true, false, true] ![0, 0, 0] 0 ω) <|
  And.intro (bandStep2_STgDriftN sz0 (STflowE z0) 0 sInst tInst (fun _ => 8) ![true, false, true] ![0, 0, 0] 0 ω) <|
  And.intro (bandStep2_STeeUM sz0 (STflowE z0) 0 H 0 (1 / 16) ![true, false, true] ![0, 0, 0]) <|
  And.intro (bandStep2_STGridRepNAt (d := 3) 3 0) (bandStep2_STGridRepN (d := 3))

/-- The energy-quantified pins `STNewKLKAt`, `STNewKLK`, `STK2decay` at `d = 3`, `κ = 𝔡 = 1/10`, `C = δ₀ = 1`. -/
example := And.intro (bandStep2_STNewKLKAt 3 (1 / 10) (1 / 10) 1 1) <|
  And.intro (bandStep2_STNewKLK 3) (bandStep2_STK2decay 3)

end RBM.BA.Step2GenInst
