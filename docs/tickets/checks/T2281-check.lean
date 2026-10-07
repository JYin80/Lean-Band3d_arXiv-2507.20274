/-
T2281 (LW-13a) check file: pins only.  No proofs, no `sorry`, no `by`.
Compiles on `main` (803bb88) as is: merged imports only.
-/
import RBM3D.Graph.AnpKey6
import RBM3D.Evolution.Pins
import RBM3D.Graph.LWPins

/-! ## Section 1: merged names used (namespace from the enclosing `namespace … end` blocks) -/

-- `Graph/LWVocab.lean` (37db678), namespace `RBM.Graph` / `RBM.Graph.NGraph`
#check @RBM.Graph.NGraph
#check @RBM.Graph.NGraph.val
#check @RBM.Graph.NGraph.IsNested
#check @RBM.Graph.NGraph.NoGhost
#check @RBM.Graph.NGraph.GhostOK
#check @RBM.Graph.NGraph.ordN
#check @RBM.Graph.NGraph.nngh
#check @RBM.Graph.NGraph.noGhostPath
-- `Graph/AnpKey.lean` (e5b944a), namespace `RBM.Graph`
#check @RBM.Graph.AnpDetGhAt
#check @RBM.Graph.AnpDetGh
#check @RBM.Graph.anpKey_long_edge
-- `Graph/AnpKey6.lean` (e2703ec), namespace `RBM.Graph`
#check @RBM.Graph.anpKey6_w
#check @RBM.Graph.anpKey6_val_eq
#check @RBM.Graph.anpKey6_union
#check @RBM.Graph.anpDetGh_holds
#check @RBM.Graph.lwAnpKeyGh_holds
#check @RBM.Graph.lwAnp_holds
-- `Kernel/PropT.lean` (c3f3d5d), namespace `RBM`, section `TTk`
#check @RBM.sfT
#check @RBM.PsiT
#check @RBM.sfT_nonneg
-- `Evolution/Pins.lean` (d9de66f), namespace `RBM`
#check @RBM.EKTTk
#check @RBM.ekTTk_holds
-- `Defs/Sizes.lean`, namespace `RBM.Gauss`
#check @RBM.Gauss.zdistInf
-- `Graph/LWPins.lean`, namespace `RBM.Gauss.Sizes` (registry spelling, `Axioms.lean:162-163`)
#check @RBM.Gauss.Sizes.LWMomentExp
#check @RBM.Gauss.Sizes.LWMoment
#check @RBM.Gauss.Sizes.LWAssmExp

/-! ## Section 2: vocabulary and pins of T2281 (LW-13a) -/

namespace RBM.Graph.T2281Check

open RBM RBM.Gauss RBM.Graph

/-- The value of a nested graph with the internal labels restricted to `D` (`7_8:1636`, `7_8:1650`):
`Σ_{ℓ ∈ D^q} Π_k w_k(ℓ)`, the summand of the merged `anpKey6_val_eq`. -/
noncomputable def valOnD {p q : ℕ} {ι : Type*} (Γ : NGraph p q) (ξ : ι → ι → ℝ) (a b : Fin p → ι)
    (D : Finset ι) : ℝ :=
  ∑ ℓ ∈ Fintype.piFinset (fun _ : Fin q => D), ∏ k : Fin Γ.es.length, anpKey6_w Γ ξ a b ℓ k

/-- `𝐃_{>ℓ}` (`7_8:1636`): `|a_i - c| ∨ |b_i - c| > ℓ` for every `i` (`‖·‖_∞` as in `LWMomentExp`). -/
noncomputable def farD (d L : ℕ) [NeZero L] {p : ℕ} (a b : Fin p → Zd d L) (ℓ : ℝ) : Finset (Zd d L) :=
  Finset.univ.filter fun c => ∀ i : Fin p,
    ℓ < max ((zdistInf d L (a i - c) : ℕ) : ℝ) ((zdistInf d L (b i - c) : ℕ) : ℝ)

/-- `𝐃_{≤ℓ}` (`7_8:1650`): `|a - c| ∨ |b - c| ≤ ℓ`, block distance `zdistD` (the norm of the merged `EKTTk`). -/
noncomputable def nearD (d L : ℕ) [NeZero L] (a b : Zd d L) (ℓ : ℝ) : Finset (Zd d L) :=
  Finset.univ.filter fun c =>
    ((zdistD d L (a - c) : ℕ) : ℝ) ≤ ℓ ∧ ((zdistD d L (b - c) : ℕ) : ℝ) ≤ ℓ

/-- **Far pin** (`(adsuu33)` deterministic, `7_8:1637`): for a nested graph without ghost edges whose edge
variables are bounded by `𝖳_t(|α-β|)`, the value with internal labels in `𝐃_{>ℓ}` is
`≤ C θ^q 𝖳_t(0)^{ord - p} 𝖳_t(ℓ)^p`.  STAGE 1a TESTS THIS FIRST (ticket, Preflight (ii)(1)): the paper's
"each path has an ending edge of length `> ℓ`" fails for `𝐃_{>ℓ}` with `∨`. -/
def AnpDetFarAt (d : ℕ) {p q : ℕ} (Γ : NGraph p q) : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ (L : ℕ) [NeZero L] (W g t θ ℓ : ℝ), 0 < W → t < 1 → 0 < θ → 0 ≤ ℓ →
      ∀ ξ : Zd d L → Zd d L → ℝ, (∀ α β, 0 ≤ ξ α β ∧ ξ α β = ξ β α) →
        (∀ α β, ξ α β ≤ sfT d L W g t ((zdistInf d L (α - β) : ℕ) : ℝ)) →
        (∀ α, ∑ β, ξ α β ^ 2 ≤ θ) →
        ∀ a b : Fin p → Zd d L,
          valOnD Γ ξ a b (farD d L a b ℓ) ≤
            C * θ ^ q * sfT d L W g t 0 ^ (Γ.ordN - (p : ℤ)) * sfT d L W g t ℓ ^ p

def AnpDetFar (d : ℕ) : Prop :=
  3 ≤ d → ∀ (p q : ℕ) (Γ : NGraph p q), Γ.NoGhost → Γ.IsNested → AnpDetFarAt d Γ

/-- **Near pin** (`(adsuu_exp2)`, `7_8:1655-1786`): `a_i ≡ a`, `b_i ≡ b`; edges `ξ ≤ 𝖳_t(|α-β|∧ℓ)` in
`zdistD`; in the regime of `EKTTk` (`1 - t ≥ g²/L²`, `1 ≤ ℓ ≤ Λ ℓ_t`), the value with internal labels in
`𝐃_{≤ℓ}` is `≤ C (Λ²(W^d(1-t))⁻¹)^q Ψ_t^{ord - p} 𝖳_t(|a-b|∧ℓ)^p`; `C` depends on `Γ`, `d` only. -/
def AnpDetNearAt (d : ℕ) {p q : ℕ} (Γ : NGraph p q) : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ (L : ℕ) [NeZero L] (W g t : ℝ), 0 < W → 0 ≤ g → t < 1 → g ^ 2 ≤ (L : ℝ) ^ 2 * (1 - t) →
      ∀ ℓ Λ : ℝ, 1 ≤ ℓ → ℓ ≤ Λ * ellT L g t →
      ∀ ξ : Zd d L → Zd d L → ℝ, (∀ α β, 0 ≤ ξ α β ∧ ξ α β = ξ β α) →
        (∀ α β, ξ α β ≤ sfT d L W g t (min ((zdistD d L (α - β) : ℕ) : ℝ) ℓ)) →
        ∀ a b : Zd d L,
          valOnD Γ ξ (fun _ => a) (fun _ => b) (nearD d L a b ℓ) ≤
            C * (Λ ^ 2 * ((W ^ d)⁻¹ / (1 - t))) ^ q * PsiT d L W g t ^ (Γ.ordN - (p : ℤ)) *
              sfT d L W g t (min ((zdistD d L (a - b) : ℕ) : ℝ) ℓ) ^ p

def AnpDetNear (d : ℕ) : Prop :=
  3 ≤ d → ∀ (p q : ℕ) (Γ : NGraph p q), Γ.NoGhost → Γ.IsNested → AnpDetNearAt d Γ

/-- The one-vertex step of the near sum (`7_8:1770-1775`, path-preserving): the merged `EKTTk` at `n = k`
pairs through one internal vertex; recorded as the shape the step lemma `lwMomExp_near_step` instantiates. -/
def NearStepShape (d : ℕ) : Prop := ∀ k : ℕ, 2 ≤ k → EKTTk d k

end RBM.Graph.T2281Check

/-! ## Section 3: instance shapes (Prop-valued, no proof obligation) -/

example : Prop := RBM.Graph.T2281Check.AnpDetFar 3
example : Prop := RBM.Graph.T2281Check.AnpDetNear 3
example : Prop := RBM.Graph.T2281Check.AnpDetFarAt 3 RBM.Graph.figAux
example : Prop := RBM.Graph.T2281Check.AnpDetNearAt 3 RBM.Graph.figAux
example : Prop := RBM.Graph.T2281Check.NearStepShape 3
