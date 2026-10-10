/-
Release check for T2370 (dispatcher V2, Sat Oct 10 03:57 UTC 2026; DECISIONS §182).  BA-K05a: the derivative of the cactus
value and the leaf pairs of `treeEqRhsS` (supervisor `docs/supervisor/2026-10-10-0350.md` K-c PASS, C1–C3).
Part 1: the pins (copied verbatim by the ticket into namespace `RBM.BA`; here in `RBM.BA.T2370Check`; the auditor adds
`example : @RBM.BA.X = @RBM.BA.T2370Check.X := rfl` for each, and `example : T2370Check.BAGammaDerivStmt d := ...`,
`example : T2370Check.BALeafPairsStmt d := ...` against the proved theorems).  Part 2: merged names.  No proofs, no sorry.
Run: lake env lean docs/tickets/checks/T2370-check.lean
-/
import RBM3D.BA.KCactus
import RBM3D.BA.KBase
import RBM3D.BA.FlowPins
import RBM3D.BA.Ward
import RBM3D.Loop.KLTree

open RBM RBM.Loop

namespace RBM.BA.T2370Check

/-- **`BASplicedFam`** (supervisor 0350 C1): the K05b witness family. Length 1: `PropSpin m`. Length 2: the closed form
`(Kn2sol)` (`1_2:1175`; the 2-loop is not a cactus). Length `n ≥ 3`: the cactus sum `W^{-d(n-1)} ∑_{F ∈ TSP n} BAGamma`. -/
def BASplicedFam (d L W : ℕ) [NeZero L] (g E : ℝ) (m : ℂ) (K : ℝ → LoopIdx (Zd d L) → ℂ) : Prop :=
  (∀ (t : ℝ) (s : Bool) (a : Zd d L), K t ⟨[s], [a]⟩ = PropSpin m s) ∧
  (∀ (t : ℝ) (σ₁ σ₂ : Bool) (a₁ a₂ : Zd d L),
    K t ⟨[σ₁, σ₂], [a₁, a₂]⟩ =
      (((W : ℂ) ^ d)⁻¹) * (BATheta d L g E m t σ₁ σ₂ * BAMss d L (BAMB d L g (E : ℂ) m) σ₁ σ₂) a₁ a₂) ∧
  (∀ (t : ℝ) (n : ℕ) [NeZero n], 3 ≤ n → ∀ (σ : Fin n → Bool) (a : Fin n → Zd d L),
    K t (KLloopOf d L σ a) =
      (((W : ℂ) ^ d)⁻¹) ^ (n - 1) * ∑ F ∈ TSP n, BAGamma d L n (BAMsigma d L (BAMB d L g (E : ℂ) m)) t F σ a)

/-- **`BAGammaDerivRHS`**: `∂_t Γ_F`. A leaf `v` carries `Θ → ΘMΘ`, written as `Σ_b (ΘM^{(σ_vσ_{v+1})})(a_v, b) Γ_F(a_v ← b)`.
A chord `J` carries `tΘ → Θ²` (`∂_t(tΘ) = Θ + tΘMΘ = Θ²`, `BATheta_resolvent`), written as the cactus `KLgval` with the
weight of the edge `Sum.inl J` replaced. -/
noncomputable def BAGammaDerivRHS (d L n : ℕ) [NeZero L] [NeZero n] (g E : ℝ) (m : ℂ) (t : ℝ)
    (F : Finset (Fin n × Fin n)) (σ : Fin n → Bool) (a : Fin n → Zd d L) : ℂ :=
  (∑ v : Fin n, ∑ b : Zd d L,
      (BATheta d L g E m t (σ v) (σ (v + 1)) * BAMss d L (BAMB d L g (E : ℂ) m) (σ v) (σ (v + 1))) (a v) b *
        BAGamma d L n (BAMsigma d L (BAMB d L g (E : ℂ) m)) t F σ (Function.update a v b)) +
  ∑ J : ↥F, KLgval d L (Nd := BAslot F) (Lf := Fin n) a
      (BACactusValLeafW (BAMsigma d L (BAMB d L g (E : ℂ) m)) t σ) (BAslotLeaf F)
      (Function.update (BACactusValEdgeW (BAMsigma d L (BAMB d L g (E : ℂ) m)) t F σ) (Sum.inl J)
        (BATheta d L g E m t (σ J.1.1) (σ J.1.2) * BATheta d L g E m t (σ J.1.1) (σ J.1.2)))
      (BACactusValSrc F) (BACactusValTgt F)

/-- **`BAGammaDerivStmt`** (target 2): the derivative of every cactus value at the BA data, `0 ≤ t < 1`. -/
def BAGammaDerivStmt (d : ℕ) : Prop :=
  ∀ (L : ℕ) [NeZero L] (n : ℕ) [NeZero n] (g κ E : ℝ) (m : ℂ), 3 ≤ n → BAReal d L g κ E m →
    ∀ (F : Finset (Fin n × Fin n)), KLIsTSP F → ∀ (σ : Fin n → Bool) (a : Fin n → Zd d L) (t : ℝ), 0 ≤ t → t < 1 →
      HasDerivAt (fun s : ℝ => BAGamma d L n (BAMsigma d L (BAMB d L g (E : ℂ) m)) s F σ a)
        (BAGammaDerivRHS d L n g E m t F σ a) t

/-- **`BALeafPairsStmt`** (target 3; supervisor 0350 Q1 table, C1, C2): for every family with `BASplicedFam`, the leaf part of
`W^{-d(n-1)} Σ_F ∂_tΓ_F` equals the `n` leaf pairs of `treeEqRhsS` at `S = 1`: the pair `(v+1, v+2)` for `v ≤ n-2` and the
wrap pair `(1, n)` for `v = n-1` (whose 2-piece is reversed; C2). -/
def BALeafPairsStmt (d : ℕ) : Prop :=
  ∀ (L W : ℕ) [NeZero L] (g κ E : ℝ) (m : ℂ), BAReal d L g κ E m →
    ∀ K : ℝ → LoopIdx (Zd d L) → ℂ, BASplicedFam d L W g E m K →
    ∀ (n : ℕ) [NeZero n], 3 ≤ n → ∀ (σ : Fin n → Bool) (a : Fin n → Zd d L) (t : ℝ), 0 ≤ t → t < 1 →
      (((W : ℂ) ^ d)⁻¹) ^ (n - 1) * ∑ F ∈ TSP n, ∑ v : Fin n, ∑ b : Zd d L,
          (BATheta d L g E m t (σ v) (σ (v + 1)) * BAMss d L (BAMB d L g (E : ℂ) m) (σ v) (σ (v + 1))) (a v) b *
            BAGamma d L n (BAMsigma d L (BAMB d L g (E : ℂ) m)) t F σ (Function.update a v b)
        = ∑ v : Fin n, ((W : ℂ) ^ d) * ∑ x : Zd d L,
            K t (LoopIdx.cutGlueL (if v.val + 1 < n then v.val + 1 else 1) (if v.val + 1 < n then v.val + 2 else n) x
              (KLloopOf d L σ a)) *
            K t (LoopIdx.cutGlueR (if v.val + 1 < n then v.val + 1 else 1) (if v.val + 1 < n then v.val + 2 else n) x
              (KLloopOf d L σ a))

end RBM.BA.T2370Check

/-! ## Part 2: merged names -/
#check @RBM.BA.BACactusVal
#check @RBM.BA.BAGamma
#check @RBM.BA.BACactusVal_congr
#check @RBM.BA.BACactusVal_orient
#check @RBM.BA.BAThetaOf_BAMsigma
#check @RBM.BA.BATheta_hasDerivAt
#check @RBM.BA.BATheta_resolvent
#check @RBM.BA.BATheta_swap
#check @RBM.BA.BATheta_isSymm
#check @RBM.BA.BAMB_symm
#check @RBM.Loop.KLgval
#check @RBM.Loop.KLgval_congr
#check @RBM.Loop.treeEqRhsS
#check @RBM.Loop.LoopIdx.cutGlueL
#check @RBM.Loop.LoopIdx.cutGlueR
#check @RBM.Loop.KLloopOf
