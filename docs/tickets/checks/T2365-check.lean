/-
Release check for T2365 (dispatcher V2, Fri Oct 9 23:00 UTC 2026; DECISIONS §171).  BA-K09a: the abstract
induction step `(eq:ind-step-bound)`, route G in place in `Loop/KLIndStepA.lean`, `Loop/KLIndStepB.lean`
(supervisor `docs/supervisor/2026-10-09-2051.md` A: Q1 K-a, K-b (finding F2); Q3 G1-G3).
Part 1: the pins.  The ticket copies them verbatim into the target files (namespace `RBM.Loop`); here they live
in `RBM.Loop.T2365Check` so that this file also compiles on the branch, where the auditor adds
`example : @RBM.Loop.X = @RBM.Loop.T2365Check.X := rfl` for each pin `X` and
`example : RBM.Loop.T2365Check.IndStepAbsOfStmt := @RBM.Loop.indStepAbs_of`.
Part 2: G1, every public declaration of the two files that is used outside them, statement unchanged.
Merged names on main.  No proofs (only `@name` and `Iff.rfl`), no sorry.
Run: lake env lean docs/tickets/checks/T2365-check.lean
-/
import RBM3D.Loop.KLIndStepB

open Finset

namespace RBM.Loop.T2365Check

/-! ## Part 1: the pins -/

/-- **`IndStepAbs`** (verbatim: probe `t/T2360:RBM3D/Probe/T2360Pins.lean:261`): `(eq:ind-step-bound)` over abstract
data, an index family `ι` with sizes `L`, weight `Bp = B_{t,0}`, molecule weight `Sig` and leaf edges `TH`. -/
def IndStepAbs {ι : Type} (d n : ℕ) [NeZero n] (L : ι → ℕ) [∀ i, NeZero (L i)] (Bp : ι → ℝ)
    (Sig : ∀ i, (Fin n → Bool) → (Fin n → Zd d (L i)) → ℂ)
    (TH : ∀ i, Bool → Bool → Matrix (Zd d (L i)) (Zd d (L i)) ℂ) : Prop :=
  ∀ τ : ℝ, 0 < τ → ∃ C : ℝ, 0 < C ∧ ∀ (i : ι) (σ : Fin n → Bool) (r : Fin n), σ r ≠ σ (r + 1) →
    ∀ a : Fin n → Zd d (L i),
      ∑ b : Zd d (L i), ‖∑ δ ∈ Finset.univ.filter (fun δ : Fin n → Zd d (L i) => δ r = b),
          Sig i σ δ * ∏ j ∈ Finset.univ.erase r, TH i (σ j) (σ (j + 1)) (a j) (δ j)‖
        ≤ C * (L i : ℝ) ^ τ * (Bp i) ^ (n - 2)

/-- **`SigSumZeroAbs`** (supervisor 2051 K-b, form (i): the one sum-zero interface; hypothesis of K09a, target of
K08b, replacing the probe's `SumZeroAbs`).  For every alternating `σ`: reflection `Σ(c - δ) = Σ(δ)`, translation
`Σ(δ + c) = Σ(δ)`, and on every slice `δ_r = x` (every root `r`) the signed estimate `O(1-t)` and the weighted
absolute estimate `O(g² + 1 - t)` with weight `(max_{i,j}|δ_i - δ_j| + 1)^Q`, every `Q ≤ 2(d-1)` (the band step
uses `Q = d` and `Q = 2(d-1)`, `KLIndStepB.lean:283, 348`).  Band form: `KLsumZero_weighted` (D194). -/
def SigSumZeroAbs {ι : Type} (d n : ℕ) [NeZero n] (L : ι → ℕ) [∀ i, NeZero (L i)] (g t : ι → ℝ)
    (Sig : ∀ i, (Fin n → Bool) → (Fin n → Zd d (L i)) → ℂ) : Prop :=
  (∀ (i : ι) (σ : Fin n → Bool), (∀ j, σ j ≠ σ (j + 1)) → ∀ (c : Zd d (L i)) (δ : Fin n → Zd d (L i)),
      Sig i σ (fun j => c - δ j) = Sig i σ δ) ∧
  (∀ (i : ι) (σ : Fin n → Bool), (∀ j, σ j ≠ σ (j + 1)) → ∀ (δ : Fin n → Zd d (L i)) (c : Zd d (L i)),
      Sig i σ (fun j => δ j + c) = Sig i σ δ) ∧
  ∀ Q : ℕ, Q ≤ 2 * (d - 1) → ∃ C : ℝ, 0 < C ∧
    ∀ (i : ι) (σ : Fin n → Bool), (∀ j, σ j ≠ σ (j + 1)) → ∀ (r : Fin n) (x : Zd d (L i)),
      ‖∑ δ ∈ Finset.univ.filter (fun δ : Fin n → Zd d (L i) => δ r = x), Sig i σ δ‖ ≤ C * (1 - t i) ∧
      ∑ δ ∈ Finset.univ.filter (fun δ : Fin n → Zd d (L i) => δ r = x),
          ‖Sig i σ δ‖ * ((KLmaxDist d (L i) δ : ℝ) + 1) ^ Q ≤ C * (g i ^ 2 + (1 - t i))

/-- **`SigDecayAbs`** (`(eq:molecule-decay)` over abstract data; band form `KLmoleculeAt`, `KLMolecule.lean:44`;
BA: row K07): `|Σ(σ, δ)| ≤ C e^{-c max_{i,j}|δ_i - δ_j|}` for every `σ`.  Used by case (i) (a short leaf). -/
def SigDecayAbs {ι : Type} (d n : ℕ) [NeZero n] (L : ι → ℕ) [∀ i, NeZero (L i)]
    (Sig : ∀ i, (Fin n → Bool) → (Fin n → Zd d (L i)) → ℂ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ c : ℝ, 0 < c ∧ ∀ (i : ι) (σ : Fin n → Bool) (δ : Fin n → Zd d (L i)),
    ‖Sig i σ δ‖ ≤ C * Real.exp (-(c * (KLmaxDist d (L i) δ : ℝ)))

/-- **`IndStepTH`**, the leaf bundle in place of `KLPT` (`KLTree.lean:321`): properties 5, 5', 6, 7, 8 of
`lem_propTH` for the edge family `TH` in the shape of `KLPT` / `BAProp5to8` (`BA/FlowPins.lean:224`; long edges
`s ≠ s'` for 5, 6, 7, 8, short edges `s = s'` for 5'; 6 and 7 at `c = 1/2`, the only range the band proof uses,
`KLIndStepA.lean:182, 291`; loss `L^τ` in 6-8 as in `KLPT`), translation invariance, and the row sum of a long
edge (`KLlat_sum_norm_Theta_row_le`).  Constants uniform in `i`.  BA instance: row K12 from `baProp5to8_holds`. -/
structure IndStepTH {ι : Type} (d : ℕ) (L : ι → ℕ) [∀ i, NeZero (L i)] (g t : ι → ℝ)
    (TH : ∀ i, Bool → Bool → Matrix (Zd d (L i)) (Zd d (L i)) ℂ) : Prop where
  transl : ∀ (i : ι) (s s' : Bool) (a b : Zd d (L i)), TH i s s' a b = TH i s s' 0 (b - a)
  decay : ∃ C : ℝ, 0 < C ∧ ∃ c : ℝ, 0 < c ∧ ∀ (i : ι) (s s' : Bool), s ≠ s' → ∀ a : Zd d (L i),
    ‖TH i s s' 0 a‖ ≤ C * Bparam d (L i) (g i) (t i) (zdistD d (L i) a)
      * Real.exp (-c * (zdistD d (L i) a : ℝ) / ellT (L i) (g i) (t i))
  short : ∃ C : ℝ, 0 < C ∧ ∃ c : ℝ, 0 < c ∧ ∀ (i : ι) (s : Bool) (a : Zd d (L i)),
    ‖TH i s s 0 a‖ ≤ C * ((if a = 0 then (1 : ℝ) else 0) + g i ^ 2 * Real.exp (-c * (zdistD d (L i) a : ℝ)))
  diffOne : ∀ τ : ℝ, 0 < τ → ∃ C : ℝ, 0 < C ∧ ∀ (i : ι) (s s' : Bool), s ≠ s' → ∀ a r : Zd d (L i),
    (zdistD d (L i) r : ℝ) ≤ (1 / 2 : ℝ) * (zdistD d (L i) a : ℝ) →
    ‖TH i s s' 0 (a + r) - TH i s s' 0 a‖
      ≤ C * (L i : ℝ) ^ τ * (g i ^ 2 + |1 - t i|)⁻¹ * (zdistD d (L i) r : ℝ)
        * (((zdistD d (L i) a : ℝ) + 1) ^ (d - 1))⁻¹
  diffTwo : ∀ τ : ℝ, 0 < τ → ∃ C : ℝ, 0 < C ∧ ∀ (i : ι) (s s' : Bool), s ≠ s' → ∀ a r : Zd d (L i),
    (zdistD d (L i) r : ℝ) ≤ (1 / 2 : ℝ) * (zdistD d (L i) a : ℝ) →
    ‖TH i s s' 0 (a + r) + TH i s s' 0 (a - r) - 2 * TH i s s' 0 a‖
      ≤ C * (L i : ℝ) ^ τ * (g i ^ 2 + |1 - t i|)⁻¹ * (zdistD d (L i) r : ℝ) ^ 2
        * (((zdistD d (L i) a : ℝ) + 1) ^ d)⁻¹
  zeroMode : ∀ τ : ℝ, 0 < τ → ∃ C : ℝ, 0 < C ∧ ∀ (i : ι) (s s' : Bool), s ≠ s' → ∀ a : Zd d (L i),
    ‖TH i s s' 0 a - ((L i : ℂ) ^ (2 * d))⁻¹ * ∑ a' : Zd d (L i), ∑ b' : Zd d (L i), TH i s s' a' b'‖
      ≤ C * (L i : ℝ) ^ τ * (g i ^ 2 + |1 - t i|)⁻¹ * (((zdistD d (L i) a : ℝ) + 1) ^ (d - 2))⁻¹
  rowSum : ∀ (i : ι) (s s' : Bool), s ≠ s' → ∀ a : Zd d (L i),
    ∑ b : Zd d (L i), ‖TH i s s' a b‖ ≤ (1 - t i)⁻¹

/-- The statement of target 3, `indStepAbs_of` (binders in this order): the generic step from the three bundles
and the parameter range of `KLPar` (`KLTree.lean:250`), with `Bp = B_{t,0}`. -/
def IndStepAbsOfStmt : Prop :=
  ∀ (d n : ℕ) [NeZero n] (gmax : ℝ) {ι : Type} (L : ι → ℕ) [∀ i, NeZero (L i)] (g t : ι → ℝ)
    (Sig : ∀ i, (Fin n → Bool) → (Fin n → Zd d (L i)) → ℂ)
    (TH : ∀ i, Bool → Bool → Matrix (Zd d (L i)) (Zd d (L i)) ℂ),
    3 ≤ d → 3 ≤ n → (∀ i, 3 ≤ L i ∧ 0 < g i ∧ g i ≤ gmax ∧ 0 ≤ t i ∧ t i < 1) →
    IndStepTH d L g t TH → SigDecayAbs d n L Sig → SigSumZeroAbs d n L g t Sig →
    IndStepAbs d n L (fun i => Bparam d (L i) (g i) (t i) 0) Sig TH

/-! ## Part 2: G1, the band statements unchanged (old statement := old name) -/

example : ∀ {d L : ℕ} {g : ℝ} [NeZero L], 3 ≤ L → ∀ {ξ : ℂ}, ‖ξ‖ < 1 → ∀ (a b : Zd d L),
    Theta d L g ξ a b = Theta d L g ξ 0 (b - a) := @RBM.Loop.KLIndStepA_Theta_apply_sub

example : ∀ {d L : ℕ} {g : ℝ} (t : ℝ), (g ^ 2 + |1 - t|)⁻¹ ≤ Bparam d L g t 0 :=
  @RBM.Loop.KLlat_inv_le_Bparam

example : ∀ {d L : ℕ} {g : ℝ} (t : ℝ) (K : ℕ), Bparam d L g t K ≤ Bparam d L g t 0 :=
  @RBM.Loop.KLIndStepA_Bparam_le_zero

example : ∀ {d L : ℕ} {g : ℝ} (t : ℝ) (K : ℕ), 0 ≤ Bparam d L g t K :=
  @RBM.Loop.KLIndStepA_Bparam_nonneg

example : ∀ {d : ℕ} {κ gmax : ℝ}, KLPT d κ gmax →
    ∃ Cd : ℝ, 0 < Cd ∧ ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ g : ℝ, 0 < g → g ≤ gmax →
      ∀ t : ℝ, 0 ≤ t → t < 1 → ∀ a b : Zd d L,
        ‖Theta d L g (t : ℂ) a b‖ ≤ Cd * Bparam d L g t 0 := @RBM.Loop.KLIndStepA_Theta_norm_le

example : ∀ {d L : ℕ} [NeZero L] {g E : ℝ}, |E| ≤ 2 → ∀ (t : ℝ) {s s' : Bool}, s ≠ s' →
    thetaEdge d L g (mSigma E) t s s' = Theta d L g (t : ℂ) := @RBM.Loop.KLIndStepA_thetaEdge_long

example : ∀ {d : ℕ} {κ gmax : ℝ} (n : ℕ) [NeZero n], 3 ≤ d → 3 ≤ n → 0 < κ → 0 < gmax → KLPT d κ gmax →
    ∃ C : ℝ, 0 < C ∧ ∀ (p : KLPar κ gmax) (σ : Fin n → Bool) (j r : Fin n), j ≠ r →
      σ j = σ (j + 1) → ∀ a : Fin n → Zd d p.L,
      ∑ b : Zd d p.L, ‖∑ δ ∈ univ.filter (fun δ : Fin n → Zd d p.L => δ r = b),
          KLSigmaPi d p.L p.g (mSigma p.E) p.t σ ∅ δ *
            ∏ i ∈ univ.erase r,
              thetaEdge d p.L p.g (mSigma p.E) p.t (σ i) (σ (i + 1)) (a i) (δ i)‖
        ≤ C * (Bparam d p.L p.g p.t 0) ^ (n - 2) := @RBM.Loop.KLindStep_nonAlt_noloss

example (d n : ℕ) [NeZero n] (κ gmax : ℝ) :
    KLindStepAt d n κ gmax ↔
      ∀ τ : ℝ, 0 < τ → ∃ C : ℝ, 0 < C ∧ ∀ (p : KLPar κ gmax) (σ : Fin n → Bool) (r : Fin n),
        σ r ≠ σ (r + 1) → ∀ a : Fin n → Zd d p.L,
          ∑ b : Zd d p.L, ‖∑ δ ∈ Finset.univ.filter (fun δ : Fin n → Zd d p.L => δ r = b),
              KLSigmaPi d p.L p.g (mSigma p.E) p.t σ ∅ δ *
                ∏ i ∈ Finset.univ.erase r,
                  thetaEdge d p.L p.g (mSigma p.E) p.t (σ i) (σ (i + 1)) (a i) (δ i)‖
            ≤ C * (p.L : ℝ) ^ τ * (Bparam d p.L p.g p.t 0) ^ (n - 2) := Iff.rfl

example : KLindStepPin ↔ ∀ (d n : ℕ) [NeZero n] (κ gmax : ℝ), 3 ≤ d → 3 ≤ n → 0 < κ → 0 < gmax →
    KLPT d κ gmax → KLindStepAt d n κ gmax := Iff.rfl

example : KLindStepPin := @RBM.Loop.KLindStepPin_holds

/-! ## Names the targets use (merged) -/
#check @RBM.Loop.KLsumZero_weighted
#check @RBM.Loop.KLSigmaPi_reflect
#check @RBM.Loop.KLIndStepA_SigmaPi_add_const
#check @RBM.Loop.KLmolecule_holds
#check @RBM.Loop.KLmoleculeAt
#check @RBM.Loop.KLShort_holds
#check @RBM.Loop.KLlat_sum_norm_Theta_row_le
#check @RBM.Loop.KLindStepAt_holds
#check @RBM.Loop.KLindStep_alt
#check @RBM.Loop.KLindStep_nonAlt

end RBM.Loop.T2365Check
