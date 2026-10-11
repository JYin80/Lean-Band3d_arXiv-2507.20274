/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Induction.Defs

/-!
# The flow carrier `FlowFM` and the generic estimate-level predicates (BA-T row 0)

Ticket T2382 (dispatcher V2, DECISIONS §195; design `docs/reports/T2379-design.md`
§2 L1, §4 row 0).  The block `BA/FlowPins.lean:315-466` of `main` at `2192dea` (its
section 4), moved with its text unchanged: `PrecL`, the structure `FlowFM`, `FlowFM.GM`,
and the generic predicates `STLKgL`, ..., `STEEg` over a carrier `C : FlowFM sz` and a
law `μ`.  The namespace is `RBM.BA`, so every name keeps its full name.  The only import
is `RBM3D.Induction.Defs` (for `STWB`, `STblk`, `Bctl`, `zdistInf`, `ellT`, `StochDomAt`,
`TimeIcc`), hence a chain file above `Induction/Defs` can import this file.  `STJhatg`
and `STLWassmExpgL` use `STprof` (`Induction/Step2Defs`) and are in `Chain/Step2Gen.lean` (T2386).
The band carrier `bandFM` (moved from `BA/FlowPins.lean`, T2386) closes the file.
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



/-! ## 4. Target 4: one pin shape for both models, the flow carrier over a law

The stochastic pins of the chain (`STLK`, `STDecay`, ..., `STMainInd`; `RBM3D/Induction/Defs.lean`) mention the
model only through four objects: `𝓛` (`Lloop`), `𝒦` (`STKloop`), `G_t` (`Gt`) and `M` (`mE E · I`).  The carrier
`FlowFM` bundles them; the estimate-level predicates are restated over it (`STLKgL`, ...), with the law `μ` of the
sample space as an explicit argument right after the carrier (T2173a, DECISIONS §57 (3), §58 (3)): the band
instance is `μ = seqP sz` (the bridges below are `Iff.rfl`), the block Anderson instance is
`μ = seqP (sz.withLam 0)` (the law of `UNModel.ba`; `S^{(B)}(0) = I`, `bandcwV`, `1_2:606`).  The probe's
`Prec`-forms without a law are not ported.  This makes "the unchanged steps reuse the ST pins with `M` for `m`" a
compiled statement; it does **not** make the merged band *proofs* generic. -/

/-- `≺` of the chain at an arbitrary law `μ` on the common sample space (`Prec sz` is the case `μ = seqP sz`;
the block Anderson law is `seqP (sz.withLam 0)`). -/
def PrecL {d : ℕ} (sz : Sizes d) (μ : Measure sz.SeqΩ) {U : ℕ → Type*} (ξ ζ : ∀ n, U n → sz.SeqΩ → ℝ) : Prop :=
  StochDomAt μ sz.size ξ ζ

/-- The four model objects of the stochastic estimates. -/
structure FlowFM {d : ℕ} (sz : Sizes d) where
  /-- `𝓛^{(k)}_{t,σ,a}` at size index `n` -/
  L : ∀ (n : ℕ) (t : ℝ) {k : ℕ}, (Fin k → Bool) → (Fin k → Zd d (sz.L n)) → sz.SeqΩ → ℂ
  /-- `𝒦^{(k)}_{t,σ,a}` -/
  K : ∀ (n : ℕ) (t : ℝ) {k : ℕ}, (Fin k → Bool) → (Fin k → Zd d (sz.L n)) → ℂ
  /-- the entries of `G_t` -/
  G : ∀ (n : ℕ) (t : ℝ), sz.SeqΩ → Idx d (sz.L n) (sz.W n) → Idx d (sz.L n) (sz.W n) → ℂ
  /-- the entries of `M` -/
  M : ∀ n : ℕ, Idx d (sz.L n) (sz.W n) → Idx d (sz.L n) (sz.W n) → ℂ
  /-- the block kernel `S^{(B)}` of the variance (`S^{(B)}(g)` for the band model, `S^{(B)}(0) = I` for `BA`) -/
  S : ∀ n : ℕ, Matrix (Zd d (sz.L n)) (Zd d (sz.L n)) ℂ
  /-- `η_t` (`(eta)`, `1_2:720`) -/
  eta : ∀ (n : ℕ) (t : ℝ), ℝ
  /-- the one-loop value `m` (`𝒦^{(1)}_{+} = m(E)`, `Def_Ktza`) -/
  m : ℕ → ℂ

section Generic

variable {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (μ : Measure sz.SeqΩ)

/-- `(G_t - M)_{xy}`. -/
def FlowFM.GM (n : ℕ) (t : ℝ) (ω : sz.SeqΩ) (x y : Idx d (sz.L n) (sz.W n)) : ℂ :=
  C.G n t ω x y - C.M n x y

/-- `(Eq:L-KGt)` (a): `max |𝓛^{(k)} - 𝒦^{(k)}| ≺ (W^{-d}B_{τ,0})^k`. -/
def STLKgL (τ : ℕ → ℝ) : Prop :=
  ∀ k : ℕ, 1 ≤ k →
    PrecL sz μ (U := fun n => (Fin k → Bool) × (Fin k → Zd d (sz.L n)))
      (fun n p ω => ‖C.L n (τ n) p.1 p.2 ω - C.K n (τ n) p.1 p.2‖)
      (fun n _ _ => (sz.Bctl n (τ n)) ^ k)

/-- `(Eq:L-KGt2)`: `max |𝓛^{(k)}| ≺ (W^{-d}B_{τ,0})^{k-1}`. -/
def STLmaxgL (τ : ℕ → ℝ) : Prop :=
  ∀ k : ℕ, 1 ≤ k →
    PrecL sz μ (U := fun n => (Fin k → Bool) × (Fin k → Zd d (sz.L n)))
      (fun n p ω => ‖C.L n (τ n) p.1 p.2 ω‖)
      (fun n _ _ => (sz.Bctl n (τ n)) ^ (k - 1))

/-- `(Eq:Gdecay)`: the decay of `𝓛^{(2)} - 𝒦^{(2)}`. -/
def STDecaygL (τ : ℕ → ℝ) : Prop :=
  ∀ D : ℝ, 0 < D →
    PrecL sz μ (U := fun n => (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)))
      (fun n p ω => ‖C.L n (τ n) p.1 p.2 ω - C.K n (τ n) p.1 p.2‖)
      (fun n p _ => (sz.Bctl n (τ n)) ^ (1 / 5 : ℝ) *
          STWB sz n (τ n) (zdistInf d (sz.L n) (p.2 0 - p.2 1)) *
          Real.exp (-(((zdistInf d (sz.L n) (p.2 0 - p.2 1) : ℕ) : ℝ) /
            ellT (sz.L n) (sz.lam n) (τ n)) ^ (1 / 2 : ℝ)) +
        ((sz.W n : ℕ) : ℝ) ^ (-D))

/-- `(Eq:Gdecay+s<g)`: only at the sizes with `1 - τ ≥ lam²`. -/
def STDecayStronggL (τ : ℕ → ℝ) : Prop :=
  ∀ D : ℝ, 0 < D →
    PrecL sz μ
      (U := fun n => {_p : (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)) // sz.lam n ^ 2 ≤ 1 - τ n})
      (fun n p ω => ‖C.L n (τ n) p.1.1 p.1.2 ω - C.K n (τ n) p.1.1 p.1.2‖)
      (fun n p _ => (sz.Bctl n (τ n)) ^ 2 *
          Real.exp (-((zdistInf d (sz.L n) (p.1.2 0 - p.1.2 1) : ℕ) : ℝ) ^ (1 / 2 : ℝ)) +
        ((sz.W n : ℕ) : ℝ) ^ (-D))

/-- `(Gt_bound+IND)`: `‖G_τ - M‖_max ≺ (W^{-d}B_{τ,0})^{1/2}`. -/
def STLocalMaxgL (τ : ℕ → ℝ) : Prop :=
  PrecL sz μ (U := fun n => Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n))
    (fun n p ω => ‖C.GM n (τ n) ω p.1 p.2‖)
    (fun n _ _ => (sz.Bctl n (τ n)) ^ (1 / 2 : ℝ))

/-- `(Gt_bound)`: `|(G_τ - M)_{xy}|² ≺ W^{-d} B_{τ,|[x]-[y]|}`. -/
def STLocalEntrygL (τ : ℕ → ℝ) : Prop :=
  PrecL sz μ (U := fun n => Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n))
    (fun n p ω => ‖C.GM n (τ n) ω p.1 p.2‖ ^ 2)
    (fun n p _ => STWB sz n (τ n) (zdistInf d (sz.L n) (STblk sz n p.1 - STblk sz n p.2)))

/-- `(Eq:Gtlp_exp)`: `|𝔼 𝓛^{(2)} - 𝒦^{(2)}| ≺ (W^{-d}B_{τ,0})²((lam² W^d)^{-1/5} + W^{-d}B_{τ,0})`. -/
def STExp2gL (τ : ℕ → ℝ) : Prop :=
  PrecL sz μ (U := fun n => (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)))
    (fun n p _ => ‖(∫ ω, C.L n (τ n) p.1 p.2 ω ∂μ) - C.K n (τ n) p.1 p.2‖)
    (fun n _ _ => (sz.Bctl n (τ n)) ^ 2 *
        ((sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d) ^ (-(1 / 5 : ℝ)) + sz.Bctl n (τ n)))


/-- `max_{a,b} 𝓛^{(2)}_{t,(-,+),(a,b)}` (the control of `(GiiGEX)`, `3_5:21`). -/
def STmaxLoop2g (n : ℕ) (t : ℝ) (ω : sz.SeqΩ) : ℝ :=
  Finset.univ.sup' ⟨((0 : Zd d (sz.L n)), (0 : Zd d (sz.L n))), Finset.mem_univ _⟩
    (fun p : Zd d (sz.L n) × Zd d (sz.L n) => ‖C.L n t ![false, true] ![p.1, p.2] ω‖)

/-- `(initialGT2)` (`3_5:28-30`): `‖G_t - M‖_max ≺ W^{-ε₀}` and `max_{a,b} 𝓛^{(2)}_{t,(-,+),(a,b)} ≺ Ψ_t²`. -/
def STInitialGT2gL (t : ℕ → ℝ) (ε₀ : ℝ) (Ψ : ℕ → ℝ) : Prop :=
  PrecL sz μ (U := fun n => Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n))
      (fun n p ω => ‖C.GM n (t n) ω p.1 p.2‖) (fun n _ _ => ((sz.W n : ℕ) : ℝ) ^ (-ε₀)) ∧
    PrecL sz μ (U := fun _ => Unit) (fun n _ ω => STmaxLoop2g C n (t n) ω)
      (fun n _ _ => Ψ n ^ 2)

/-- `(Eq:L-KGt)`-type bound `max_{σ,a} |𝒦^{(k)}_{τ,σ,a}| ≺ (W^{-d}B_{τ,0})^{k-1}` (`ML:Kbound`, `1_2:1056`). -/
def STKboundgL : Prop :=
  ∀ τ : ℕ → ℝ, (∀ n, 0 ≤ τ n) → (∀ n, τ n < 1) →
    ∀ k : ℕ, 1 ≤ k →
      PrecL sz μ (U := fun n => (Fin k → Bool) × (Fin k → Zd d (sz.L n)))
        (fun n p _ => ‖C.K n (τ n) p.1 p.2‖) (fun n _ _ => (sz.Bctl n (τ n)) ^ (k - 1))

/-- The loop-index lemma of `STKwardgL`: the `Fin k`-vector `(a, x)` (`a` on the first `k - 1` places, `x` on the last) as a
list is `List.ofFn a ++ [x]` (the list-indexed `STKward`, `Induction/Step34Pins.lean:229`, reads `⟨List.ofFn σ, List.ofFn a ++ [x]⟩`). -/
theorem Carrier_ofFn_ext {α : Type*} {k : ℕ} (hk : 1 ≤ k) (a : Fin (k - 1) → α) (x : α) :
    List.ofFn (fun i : Fin k => if h : (i : ℕ) < k - 1 then a ⟨i, h⟩ else x) = List.ofFn a ++ [x] := by
  refine List.ext_getElem (by simp; omega) fun i h1 h2 => ?_
  simp only [List.getElem_ofFn, List.length_ofFn] at h1 ⊢
  rw [List.getElem_append]
  by_cases hi : i < k - 1
  · simp [hi]
  · have e : i = k - 1 := by omega
    simp [hi, e]

/-- **`(wardineq_K)`, `lem_wardineq_K`** (`3_5:1001`) over a carrier `C` and a law `μ`: the generic form of `STKward`
(`Induction/Step34Pins.lean:229`).  For every time sequence `τ ∈ [0,1)` and `k ≥ 2`,
`max_σ Σ_{a_k} |𝒦^{(k)}_{τ,σ,a}| ≺ (W^d η_τ)⁻¹ (W^{-d}B_{τ,0})^{k-2}`, the sum over the last label `x`, the first `k - 1` labels `p.2`;
`η_τ` is `C.eta n (τ n)`. -/
def STKwardgL : Prop :=
  ∀ τ : ℕ → ℝ, (∀ n, 0 ≤ τ n) → (∀ n, τ n < 1) → ∀ k : ℕ, 2 ≤ k →
    PrecL sz μ (U := fun n => (Fin k → Bool) × (Fin (k - 1) → Zd d (sz.L n)))
      (fun n p _ => ∑ x : Zd d (sz.L n),
        ‖C.K n (τ n) p.1 (fun i : Fin k => if h : (i : ℕ) < k - 1 then p.2 ⟨i, h⟩ else x)‖)
      (fun n _ _ => (((sz.W n : ℕ) : ℝ) ^ d * C.eta n (τ n))⁻¹ * (sz.Bctl n (τ n)) ^ (k - 2))

/-- `(lRB1)`, uniform in `u ∈ [s,t]` (`1_2:1321`). -/
def STStep1LoopgL (s t : ℕ → ℝ) : Prop :=
  ∀ k : ℕ, 1 ≤ k →
    PrecL sz μ (U := fun n => TimeIcc s t n × (Fin k → Bool) × (Fin k → Zd d (sz.L n)))
      (fun n p ω => ‖C.L n (p.1 : ℝ) p.2.1 p.2.2 ω‖)
      (fun n p _ => ((1 - s n) / (1 - (p.1 : ℝ))) ^ (k - 1) * (sz.Bctl n (s n)) ^ (k - 1))

/-- `(Gtmwc)`, uniform in `u ∈ [s,t]` (`1_2:1327`). -/
def STStep1WeakgL (s t : ℕ → ℝ) : Prop :=
  PrecL sz μ (U := fun n => TimeIcc s t n × Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n))
    (fun n p ω => ‖C.GM n (p.1 : ℝ) ω p.2.1 p.2.2‖)
    (fun n p _ => (sz.Bctl n (p.1 : ℝ)) ^ (1 / 4 : ℝ))

/-- **The quadratic-variation loop `(𝓔⊗𝓔)^{M,(2;k)}_{t,σ,a,a}`** (`def:CALE`, `3_5:176-190`, `n = 2`):
`W^d Σ_{c,c'} S^{(B)}_{cc'} 𝓛^{(6)}_{(σ⊗σ̄)^{(k)}, (a⊗a)^{(k)}(c',c)}`, with the kernel `S` of the carrier
(`S^{(B)}(g)` for the band model, `I` for `BA`). -/
def STEEg (n : ℕ) (u : ℝ) (k : Fin 2) (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) (ω : sz.SeqΩ) : ℂ :=
  (((sz.W n : ℕ) : ℂ) ^ d) * ∑ c : Zd d (sz.L n), ∑ c' : Zd d (sz.L n),
    C.S n c c' *
      (if k = 0 then
        C.L n u ![σ 0, σ 1, σ 0, !(σ 0), !(σ 1), !(σ 0)] ![a 0, a 1, c', a 1, a 0, c] ω
      else
        C.L n u ![σ 1, σ 0, σ 1, !(σ 1), !(σ 0), !(σ 1)] ![a 1, a 0, c', a 0, a 1, c] ω)

end Generic

/-- **The band carrier at the energy sequence `E`.** -/
def bandFM {d : ℕ} (sz : Sizes d) (E : ℕ → ℝ) : FlowFM sz where
  L := fun n t {_k} σ a ω => Lloop sz n (E n) t σ a ω
  K := fun n t {_k} σ a => STKloop sz n (E n) t σ a
  G := fun n t ω x y => Gt sz n (E n) t true ω x y
  M := fun n x y => if x = y then mE (E n) else 0
  S := fun n => SB d (sz.L n) (sz.lam n)
  eta := fun n t => etaT (E n) t
  m := fun n => mE (E n)

end RBM.BA
