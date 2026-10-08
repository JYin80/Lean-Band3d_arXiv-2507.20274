/-
Release check for T2332 (dispatcher V1, Thu Oct  8 11:52 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §147; supervisor
2026-10-08-1143 C7/O1; Fable LW review 2026-10-06 §1 row "LW engine", §2a, §3 "Pin before" (1)).
LW engine (LW gate): `RBM3D/Graph/LWEngine.lean`, the `m`-free form of `lw_localregular`: one pair of lists on the
exponent-tracking carrier `(ℕ × ℕ) × PGraph (Fin 2)` (as T2307's `partitionX`) that, evaluated at every `m ≠ 0` by
`lwEvX m` (coefficient times `m^j m̄^{j'}`), satisfies the six conjuncts of `lw_localregular` and has `≥ p` black waved edges.
Section 1: merged names (exact namespaces; `main` 7b9fefe).  Section 2: the definitions `lwEvX`, `LWLocRegConcl` (copied
verbatim into `RBM.Graph`; `LWLocRegConcl` is the conclusion of `lw_localregular`, `LocalRegular6d.lean:1110-1129`, word for
word) and the target.  Statements, definitions and `#check` only.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2332-check.lean`.
-/
import RBM3D.Graph.LocalRegular6d
import RBM3D.Graph.LWExpTerm5

/-! ## 1. Merged names -/

#check @RBM.Graph.lw_localregular            -- LocalRegular6d.lean:1110 (the `m`-dependent form)
#check @RBM.Graph.lw_localregular_upto5      -- LocalRegular2.lean:1857
#check @RBM.Graph.lvl1_exists_aux            -- LWLvl1.lean:3837 (the WF recursion to mirror)
#check @RBM.Graph.lvl1_exists_step           -- LWLvl1.lean:3655
#check @RBM.Graph.lvl1_induction             -- LWLvl1.lean:3763
#check @RBM.Graph.Lvl1Mu                     -- LWLvl1.lean:3778
#check @RBM.Graph.lvl1Cutoff                 -- LWLvl1.lean:3981
#check @RBM.Graph.LocStep                    -- LWLvl1.lean:3260
#check @RBM.Graph.Lvl1Reach                  -- LWLvl1.lean:3277
#check @RBM.Graph.lvl1WeightOuts0            -- LWLvl1.lean:3228
#check @RBM.Graph.lvl1EdgeOuts0              -- LWLvl1.lean:3236
#check @RBM.Graph.lvl1GGOuts0                -- LWLvl1.lean:3243
#check @RBM.Graph.lvl1Pack                   -- LWLvl1.lean:3252
#check @RBM.Graph.LGraph.partition           -- LWVocab.lean:1303
#check @RBM.Gauss.Sizes.partitionX                 -- LWExpTerm5.lean:106 (T2307)
#check @RBM.Gauss.Sizes.lwSplitLoopsX              -- LWExpTerm5.lean (T2307)
#check @RBM.Gauss.Sizes.lwSplitLoopsX_spec         -- LWExpTerm5.lean:281 (T2307)
#check @RBM.Gauss.Sizes.partitionX_spec            -- LWExpTerm5.lean:310 (T2307)
#check @RBM.Gauss.Sizes.val_eq_partitionX          -- LWExpTerm5.lean:337 (T2307)
#check @RBM.Graph.fxyPowGraph                -- LocalRegular.lean:1354
#check @RBM.Graph.locReg6Inv_locStep         -- LocalRegular6d.lean:1085
#check @RBM.Graph.PGraph                     -- LWVocab.lean:653

noncomputable section

namespace RBM.Graph.T2332Check

open MeasureTheory ProbabilityTheory Matrix
open RBM RBM.Gauss RBM.Green RBM.Graph

/-! ## 2. Definitions (copied verbatim into `RBM.Graph`) and the target -/

/-- Evaluation of a tagged graph at `m`: the coefficient multiplied by `m^j m̄^{j'}` (as `PartitionXSpec`). -/
def lwEvX (m : ℂ) (r : (ℕ × ℕ) × PGraph (Fin 2)) : PGraph (Fin 2) :=
  { r.2 with g := { r.2.g with coeff := m ^ r.1.1 * star m ^ r.1.2 * r.2.g.coeff } }

/-- The conclusion of `lw_localregular` (`LocalRegular6d.lean:1110-1129`) for given lists, word for word. -/
def LWLocRegConcl (p : ℕ) (m : ℂ) (c : ℝ) (K0 d : ℕ) (D : ℝ) (outs errs : List (PGraph (Fin 2))) : Prop :=
  (∀ Q ∈ outs, Q.g.LocStd ∧ (fxyPowGraph p).pack.g.scalingOrder ≤ Q.g.scalingOrder) ∧
  (∀ Q ∈ errs, ∀ (W L : ℕ) (Ψ : ℝ), 1 ≤ W → 1 ≤ L → (L : ℝ) ^ d ≤ (W : ℝ) ^ K0 →
    (W : ℝ) ^ (-(d : ℝ) / 2) ≤ Ψ → Ψ ≤ (W : ℝ) ^ (-c) → Q.g.scalingSize Ψ W d L ≤ (W : ℝ) ^ (-D)) ∧
  (∀ Q ∈ outs ++ errs, Lvl1Reach m (lvl1Cutoff c K0 d D (fxyPowGraph p).pack.g.counters : ℤ) (fxyPowGraph p).pack Q ∧
    Q.g.Normal ∧ (fxyPowGraph p).pack.g.scalingOrder ≤ Q.g.scalingOrder ∧ Q.g.nM ≤ (fxyPowGraph p).pack.g.nM ∧
    (Q.g.nV : ℤ) - Q.g.nW ≤ ((fxyPowGraph p).pack.g.nV : ℤ) - (fxyPowGraph p).pack.g.nW) ∧
  (∀ {sz : Sizes d} {n : ℕ} {z : ℂ} {u : ℝ}
    (Sp M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ),
    GaussIBP sz → 0 < z.im → 0 < u → m ≠ 0 → z + (u : ℂ) * m = -m⁻¹ →
    (∀ i j, Sp i j - m ^ 2 * ∑ w, Sp i w * lwS sz n u w j = lwS sz n u i j) → Spᵀ = Sp →
    (∀ a, M a a = m) → (∀ a b, a ≠ b → M a b = 0) → ∀ ℓe : Fin 2 → Idx d (sz.L n) (sz.W n),
      ∫ ω, (fxyPowGraph p).pack.val (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓe ∂(Sizes.seqP sz) =
        (outs.map fun Q => ∫ ω, Q.val (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓe ∂(Sizes.seqP sz)).sum +
        (errs.map fun Q => ∫ ω, Q.val (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓe ∂(Sizes.seqP sz)).sum) ∧
  (∀ Q ∈ outs, Q.LocReg1 ∧ Q.LocReg2 p ∧ Q.LocReg345 p ∧ Q.LocReg6 p ∧
    (Q.ext 0 ≠ Q.ext 1 → 3 * (p : ℤ) ≤ Q.g.scalingOrder))

/-- **The `m`-free `lem:localregular`** (supervisor 1143 O1, Fable §3 (1)): one pair of tagged lists for all `m ≠ 0`, and every
output and error has at least `p` black waved edges (T2297's S1 invariant `nWS ≥ p`). -/
def T2332_lw_localregularX : Prop :=
  ∀ (p : ℕ) (c : ℝ), 0 < c → ∀ (K0 d : ℕ) (D : ℝ),
    ∃ outsX errsX : List ((ℕ × ℕ) × PGraph (Fin 2)), ∀ m : ℂ, m ≠ 0 →
      LWLocRegConcl p m c K0 d D (outsX.map (lwEvX m)) (errsX.map (lwEvX m)) ∧
      ∀ Q ∈ outsX.map (lwEvX m) ++ errsX.map (lwEvX m), p ≤ Q.g.waved.countP (fun e => !e.col)

example : Prop := T2332_lw_localregularX

end RBM.Graph.T2332Check

end
