/-
Release check for T2323 (dispatcher V1, Thu Oct  8 08:55 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §141, §134).
UN-31b (bulk universality, GUE phase, process layer, second cut): `RBM3D/Universality/GUEPhase/ProcK.lean`, port of RBM2D
`Universality/GUEPhase/Proc.lean:862-1424` (`KprocDom`, `KprocInput`: `gueKproc_detDom`), with the K-loop initial data
from the owed/proved pin `STKbound` in place of RBM2D's `KLoop.Kbound_prec_uncond` (precedent T2153a, `GridEnvelopeN.lean:36-41`).
Section 1: merged names (exact namespaces; file:line on `main` 5d9506a).
Section 2: the target statement as a `Prop` (T2323 proves it with this text).
Statements and `#check` only: no theorem, no proof, no tactic block.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2323-check.lean`.
-/
import RBM3D.Universality.GUEPhase.Proc
import RBM3D.Induction.Defs

open MeasureTheory Filter Topology

/-! ## 1. Merged names -/

-- UN-31a (T2322, e17d56f), `Universality/GUEPhase/Proc.lean`, namespace `RBM.Univ.GUEPhase`
#check @RBM.Univ.GUEPhase.gueKproc         -- :122
#check @RBM.Univ.GUEPhase.gueKbar
#check @RBM.Univ.GUEPhase.gueInterp
#check @RBM.Univ.GUEPhase.gueTent
-- UN-27 Grid, UN-26 Bootstrap
#check @RBM.Univ.GUEPhase.gueScale         -- Grid.lean:84
#check @RBM.Univ.GUEPhase.gueGridK         -- Grid.lean:106
#check @RBM.Univ.GUEPhase.primRhsGUE       -- Bootstrap.lean:178
#check @RBM.Univ.GUEPhase.eq736            -- Bootstrap.lean:442 (the bootstrap (7.36))
#check @RBM.Univ.GUEPhase.ellT_eq_L        -- Bootstrap.lean:148
-- the K-loop and its bound (`Induction/Defs.lean`, `RBM.Gauss.Sizes`)
#check @RBM.Gauss.Sizes.STKloop            -- :64
#check @RBM.Gauss.Sizes.STKbound           -- :174
#check @RBM.Gauss.Sizes.Bctl               -- Defs/Sizes.lean:214
-- loops, path, scales
#check @RBM.Loop.LoopIdx                   -- Loop/TreeRep.lean:56
#check @RBM.Gauss.loopOf                   -- Loop/GLoopFlow.lean:117
#check @RBM.Gauss.etaT                     -- Loop/GLoop.lean:75
#check @RBM.Path.TimeIcc                   -- Defs/StochDomAt.lean:100
#check @RBM.Path.gridTime                  -- Path/Walk.lean:70
#check @RBM.Path.gridStep                  -- Path/Walk.lean:67
#check @RBM.eventually_le_rpow             -- Defs/Domination.lean:68

/-! ## 2. Target statement -/

namespace RBM.Univ.GUEPhase.T2323Check

open RBM RBM.Gauss RBM.Gauss.Sizes RBM.Path RBM.Univ.GUEPhase

/-- **`gueKproc_detDom`** (RBM2D `Proc.lean:1247`) at `d ≥ 3`: `K̃ ≺ (N η_t)^{-(m-1)}` on the grid, interpolated,
in the explicit size-scale form; the initial data at `t₁` from `STKbound E` (new hypothesis `hKb`, as T2153a) under the
zero-mode condition `L^d (1 - t₁) ≤ ilambda²` (`hell`; RBM2D's `L²(1-t₁) ≤ 1` is its `d = 2`, `ilambda = 1` case), and the
initial values identified with the band K-loop `STKloop` (`hKinit`). -/
def T2323_gueKproc_detDom : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) {κ τU : ℝ}, 0 < κ → 0 < τU → ∀ (n0 : ℕ) {E t1 t0 : ℕ → ℝ},
    (∀ n, |E n| ≤ 2 - κ) → (∀ n, 0 ≤ t1 n) → (∀ n, t1 n ≤ t0 n) → (∀ n, t0 n < 1) →
    Tendsto sz.size atTop atTop →
    (∀ᶠ n : ℕ in atTop, t0 n - t1 n ≤ ((sz.size n : ℕ) : ℝ) ^ (-τU) * etaT (E n) (t0 n)) →
    (∀ᶠ n : ℕ in atTop, (gueScale sz E n (t0 n))⁻¹ ≤ ((sz.size n : ℕ) : ℝ) ^ (-τU)) →
    (∀ᶠ n : ℕ in atTop, ((sz.L n : ℕ) : ℝ) ^ d * (1 - t1 n) ≤ sz.lam n ^ 2) →
    sz.STKbound E →
    ∀ (Kt : ∀ n, ℝ → RBM.Loop.LoopIdx (Zd d (sz.L n)) → ℂ),
    (∀ n {k : ℕ} (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)),
      Kt n (t1 n) (loopOf σ a) = STKloop sz n (E n) (t1 n) σ a) →
    (∀ n, ∀ t ∈ Set.Icc (t1 n) (t0 n), ∀ I : RBM.Loop.LoopIdx (Zd d (sz.L n)), I.WF →
      1 ≤ I.length → I.length ≤ 4 * n0 →
      HasDerivWithinAt (fun s => Kt n s I) (primRhsGUE d (sz.L n) (sz.W n) (Kt n t) I)
        (Set.Icc (t1 n) (t0 n)) t) →
    ∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop, ∀ (t : TimeIcc t1 t0 n) (m : Set.Icc 2 (2 * n0)),
      gueKproc sz t1 t0 (gueGridK sz n0) Kt n (m : ℕ) (t : ℝ) ≤
        ((sz.size n : ℕ) : ℝ) ^ ε * (gueScale sz E n (t : ℝ))⁻¹ ^ ((m : ℕ) - 1)

example : Prop := T2323_gueKproc_detDom

end RBM.Univ.GUEPhase.T2323Check
