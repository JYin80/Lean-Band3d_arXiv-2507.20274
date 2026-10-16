/-
Proposals for T2519 (dispatcher V5, 2026-10-16 10:34 UTC; DECISIONS §348): the `T2519_*` texts of the draft (DECISIONS
§343-§344), Part 2 over names merged at 13b68cea, Part 3 over the names of C4 a/b and C3 b (merged ff7bd277, 26561542,
fde07256). NOT binding until the 1a-audit, and NOT a release gate: the hub compiles this file for information and pastes
the error lines; the 1a restates in its probe every text it needs (with the instance arguments it needs) and the
1a-audit signs them. Statements only; no proofs.
Run: lake env lean docs/tickets/checks/T2519-pins.lean
-/
import RBM3D.BA.GUEKPrim
import RBM3D.BA.KBound
import RBM3D.BA.KCactus
import RBM3D.BA.GreenStab
import RBM3D.BA.GUEOneLoop
import RBM3D.BA.GUEEq729BA
import RBM3D.BA.GUEEntry2

set_option linter.style.longLine false
set_option linter.unusedVariables false

/-! ## Part 2: proposals over merged names (prefix `T2519_`; NOT binding until the 1a-audit) -/

namespace RBM.BA.T2519Check

open MeasureTheory Filter Matrix RBM RBM.Gauss RBM.Path RBM.Loop RBM.Univ RBM.Univ.GUEPhase RBM.BA

/-- **Target 16a, `ba_prodG`**: `RBG_Prod` at the BA vocabulary of C5g for a primitive family `KF` and path bounds `PB`
(C5 instantiates `KF := T2519_KFamBA`, `PB := T2519_PBBA`, Part 3); text of `RandomLayerBGBA:204`. -/
def T2519_ProdBA (KF PB : ∀ d : ℕ, ∀ sz : Sizes d, (ℕ → ℝ) → (ℕ → ℝ) → (ℕ → ℝ) →
    (∀ n, ℝ → LoopIdx (Zd d (sz.L n)) → ℂ) → Prop) : Prop :=
  ∀ d : ℕ, 3 ≤ d → RBG_Prod (BAEd d) (BAfE d) (BAfT d) (BAMO d) (KF d) (PB d)

/-- **Target 16b, `ba_LLG`**: the unprimed T3 at BA (`RandomLayerBGBA:205`). -/
def T2519_LLBA (PB : ∀ d : ℕ, ∀ sz : Sizes d, (ℕ → ℝ) → (ℕ → ℝ) → (ℕ → ℝ) →
    (∀ n, ℝ → LoopIdx (Zd d (sz.L n)) → ℂ) → Prop) : Prop :=
  ∀ d : ℕ, 3 ≤ d → RandomLayerB_LL (UNKind.ba d) (BAfE d) (BAfT d) (PB d)

/-- **Target 16c, `ba_QueG`**: `RBG_Que` at BA with the BA profile `UNOUProfile.ba` (`RandomLayerBGBA:206`). -/
def T2519_QueBA (KF PB : ∀ d : ℕ, ∀ sz : Sizes d, (ℕ → ℝ) → (ℕ → ℝ) → (ℕ → ℝ) →
    (∀ n, ℝ → LoopIdx (Zd d (sz.L n)) → ℂ) → Prop) : Prop :=
  ∀ d : ℕ, 3 ≤ d → RBG_Que (UNKind.ba d) (UNOUProfile.ba d) (BAEd d) (BAfE d) (BAfT d) (BAMO d) (KF d) (PB d)

/-- **Target 1, `BAKFam`** (twin of `RandomLayerB_KFam`, `RandomLayerB:63`): at the flow point `g = √t₀ λ`,
`m = BAm d L g E'` (the real-axis solution), start `BAKsol` at `t₁`, the ODE `primRhsGUE` on `[t₁, t₀]` (`n₀ = 3`), 2-loops
`kTwoGUEBA`.  Every clause is guarded by `0 < g` (`gueK_existsBA` needs it; `Sizes.lam` has no sign: coverage row 14). -/
def T2519_KFamBA (d : ℕ) (sz : Sizes d) (E' t1 t0 : ℕ → ℝ) (Kt : ∀ n, ℝ → LoopIdx (Zd d (sz.L n)) → ℂ) : Prop :=
  (∀ n, 0 < Real.sqrt (t0 n) * sz.lam n → ∀ I : LoopIdx (Zd d (sz.L n)),
      Kt n (t1 n) I =
        BAKsol d (sz.L n) (sz.W n)
          (BAMsigma d (sz.L n) (BAMB d (sz.L n) (Real.sqrt (t0 n) * sz.lam n) (E' n : ℂ)
            (BAm d (sz.L n) (Real.sqrt (t0 n) * sz.lam n) (E' n : ℂ))))
          (PropSpin (BAm d (sz.L n) (Real.sqrt (t0 n) * sz.lam n) (E' n : ℂ))) (t1 n) I) ∧
  (∀ n, 0 < Real.sqrt (t0 n) * sz.lam n → ∀ s ∈ Set.Icc (t1 n) (t0 n), ∀ I : LoopIdx (Zd d (sz.L n)), I.WF →
      1 ≤ I.length → I.length ≤ 4 * 3 →
      HasDerivWithinAt (fun u => Kt n u I) (primRhsGUE d (sz.L n) (sz.W n) (Kt n s) I) (Set.Icc (t1 n) (t0 n)) s) ∧
  (∀ n, 0 < Real.sqrt (t0 n) * sz.lam n → ∀ s ∈ Set.Icc (t1 n) (t0 n), ∀ (σ₁ σ₂ : Bool) (a b : Zd d (sz.L n)),
      Kt n s ⟨[σ₁, σ₂], [a, b]⟩ =
        kTwoGUEBA d (sz.L n) (sz.W n) (Real.sqrt (t0 n) * sz.lam n) (E' n)
          (BAm d (sz.L n) (Real.sqrt (t0 n) * sz.lam n) (E' n : ℂ)) (t1 n) s σ₁ σ₂ a b)

/-- `BAKFam` has the type of `KF` in the three RBG texts (exact-type check of D1 (ii)). -/
example : Prop :=
  ∀ PB : (∀ d : ℕ, ∀ sz : Sizes d, (ℕ → ℝ) → (ℕ → ℝ) → (ℕ → ℝ) → (∀ n, ℝ → LoopIdx (Zd d (sz.L n)) → ℂ) → Prop),
    T2519_ProdBA T2519_KFamBA PB ∧ T2519_LLBA PB ∧ T2519_QueBA T2519_KFamBA PB

/-- The consumer (N2, `T2513_n2_three`; `RandomLayerBGBA:199-212`): the three C5 targets with the merged C5g/C3 pieces give
`UNG1Rowk` at `UNKind.ba` through `g1Rowk_of_inputsG` (a `Prop` here; N2 proves it in MN-D3's filtered form). -/
example : Prop :=
  ∀ KF PB : (∀ d : ℕ, ∀ sz : Sizes d, (ℕ → ℝ) → (ℕ → ℝ) → (ℕ → ℝ) → (∀ n, ℝ → LoopIdx (Zd d (sz.L n)) → ℂ) → Prop),
    T2519_ProdBA KF PB → T2519_LLBA PB → T2519_QueBA KF PB →
      UNG1Rowk (fun d => UNKind.ba d) (fun d => UNOUProfile.ba d) (∀ d : ℕ, UNMLOutBA d) UNLocAvgBA UNQueBA

/-- **Coverage row 13, the margin datum gives the real-axis datum** (family premise of C4's texts): `BAEd κ'` at `z`
is `BAReal` at `(√t₀ λ, BAfE, BAm d L (√t₀ λ) BAfE)` (`BAm_spec`, `BASelf_unique`). -/
def T2519_EdRealBA : Prop :=
  ∀ (d : ℕ) (κ' : ℝ) (sz : Sizes d) (n : ℕ) (z : ℂ), BAEd d κ' sz n z →
    BAReal d (sz.L n) (Real.sqrt (BAfT d sz n z) * sz.lam n) κ' (BAfE d sz n z)
      (BAm d (sz.L n) (Real.sqrt (BAfT d sz n z) * sz.lam n) (BAfE d sz n z : ℂ))

/-- **Coverage row 13, the scale of the RBG texts is the flow scale**: `√fT Im z = etaOf m t₀` at the flow point
(`BAzztE_data`, `BAt0_mul`): the hypotheses `h730`, `hscale` of `RBG_Prod` are the `η_{t₀}` rows of the grid twins. -/
def T2519_FlowEtaBA : Prop :=
  ∀ (d : ℕ) (sz : Sizes d) (n : ℕ) (z : ℂ), 0 < z.im →
    etaOf (BAm d (sz.L n) (Real.sqrt (BAfT d sz n z) * sz.lam n) (BAfE d sz n z : ℂ)) (BAfT d sz n z) =
      Real.sqrt (BAfT d sz n z) * z.im

/-- **Target 15, `baEq729_Kdisc`** (T2517 target 8, moved to C5 by T2517 Decision (1)): `eq729_Kdisc` (`Eq729A:562`) at
`Kf = kTwoGUELoopBA … t₁` on real-axis data; `hKd` is `hasDerivAt_kTwoGUELoopBA` (`GUEKPrim:776`); `b₂ ≤ 1` stays a
premise (fed by `baTheta_weighted_l1` or by `Hyp_Kt_detDomBA`). -/
def T2519_KdiscBA : Prop :=
  ∀ (d L : ℕ) [NeZero L] (W : ℕ) [NeZero W] (g κ E : ℝ) (m : ℂ), BAReal d L g κ E m →
    ∀ {t1 t0 u Δ b2 : ℝ}, 0 ≤ t1 → t0 < 1 → u ∈ Set.Icc t1 t0 → u + Δ ∈ Set.Icc t1 t0 → 0 ≤ Δ → b2 ≤ 1 →
      (((W * L) ^ d : ℕ) : ℝ) * Δ ≤ 1 →
      (∀ s ∈ Set.Icc t1 t0, ∀ s1 s2 x y, ‖kTwoGUELoopBA d L W g E m t1 s ⟨[s1, s2], [x, y]⟩‖ ≤ b2) →
      ∀ (s1 s2 : Bool) (a1 a2 : Zd d L),
        ‖kTwoGUELoopBA d L W g E m t1 u ⟨[s1, s2], [a1, a2]⟩ +
            (Δ : ℂ) * primRhsGUE d L W (kTwoGUELoopBA d L W g E m t1 u) ⟨[s1, s2], [a1, a2]⟩ -
          kTwoGUELoopBA d L W g E m t1 (u + Δ) ⟨[s1, s2], [a1, a2]⟩‖ ≤
          3 * (((W * L) ^ d : ℕ) : ℝ) ^ 2 * Δ ^ 2

/-! ## Part 3: proposals over the names of C4 a/b and C3 b -/





/-- **Target 1, `GUEPathBoundsBA`** (twin of `GUEPathBounds`, `Grid:89`): the path `gueHBA`, the flow `ztOf (m n) (E n)`,
the scale `N etaOf (m n) u`; the local law is against `Mres (g Ψ_I) E m = M^{(B)} ⊗ 1` (not `m • 1`).  No twist field:
`hoff` is target 7, a consequence at each grid time (D1 (i)). -/
def T2519_PathBoundsBA {d : ℕ} (sz : Sizes d) (g E t1 t0 : ℕ → ℝ) (m : ℕ → ℂ) (K : ℕ → ℕ) (n0 : ℕ)
    (Kt : ∀ n, ℝ → LoopIdx (Zd d (sz.L n)) → ℂ) : Prop :=
  (∀ k : ℕ, 1 ≤ k → k ≤ n0 → StochDomAt (Pgue (sz.withLam 0)) sz.size
    (fun n (p : Fin (K n + 1) × (Fin k → Bool) × (Fin k → Zd d (sz.L n))) ω =>
      ‖loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (gueHBA sz g t1 t0 K n p.1 ω))
          (ztOf (m n) (E n) (gridTime t1 t0 K n p.1)) (loopOf p.2.1 p.2.2) -
        Kt n (gridTime t1 t0 K n p.1) (loopOf p.2.1 p.2.2)‖)
    (fun n p _ => (((sz.size n : ℕ) : ℝ) * etaOf (m n) (gridTime t1 t0 K n p.1))⁻¹ ^ k)) ∧
  StochDomAt (Pgue (sz.withLam 0)) sz.size
    (fun n (p : Fin (K n + 1) × (Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n))) ω =>
      ‖green (gueHBA sz g t1 t0 K n p.1 ω) (ztOf (m n) (E n) (gridTime t1 t0 K n p.1)) p.2.1 p.2.2 -
        Mres (((g n : ℝ) : ℂ) • PsiI d (sz.L n) (sz.W n)) (E n : ℂ) (m n) p.2.1 p.2.2‖)
    (fun n p _ => (((sz.size n : ℕ) : ℝ) * etaOf (m n) (gridTime t1 t0 K n p.1))⁻¹ ^ ((1 : ℝ) / 2))

/-- **Target 1, `BAPB`** (twin of `RandomLayerB_PBband`, `RandomLayerB:346`): `GUEPathBoundsBA` at the flow point of the
RBG texts, `g = √t₀ λ`, `m = BAm d L g E'`, grid `gueGridK sz 3`, `n₀ = 3`. -/
def T2519_PBBA (d : ℕ) (sz : Sizes d) (E' t1 t0 : ℕ → ℝ) (Kt : ∀ n, ℝ → LoopIdx (Zd d (sz.L n)) → ℂ) : Prop :=
  T2519_PathBoundsBA sz (fun n => Real.sqrt (t0 n) * sz.lam n) E' t1 t0
    (fun n => BAm d (sz.L n) (Real.sqrt (t0 n) * sz.lam n) (E' n : ℂ)) (gueGridK sz 3) 3 Kt

/-- **Target 16 at C5's vocabulary** (the statements of `ba_prodG`, `ba_LLG`, `ba_QueG`). -/
def T2519_ProducersBA : Prop :=
  T2519_ProdBA T2519_KFamBA T2519_PBBA ∧ T2519_LLBA T2519_PBBA ∧ T2519_QueBA T2519_KFamBA T2519_PBBA

/-- **Target 7, `gueGrid_twistBA` = D1 (i), the `hoff` producer**: from `GUEPathBoundsBA` (with `Kt = m` on 1-loops)
the `M`-weighted block traces `t_{aq} = W^{-d} Σ_{x∈[a], y∈[q]} M_{xy} G_{yx}` are within `‖M^{(B)}_{aq}‖ (N η_u)⁻¹` of
`M^{(++)}_{aq}`: the conclusion is the second `StochDomAt` premise of `T2517_OneLoopBA` verbatim (at `K = gueGridK sz n0`).
Route R1: `t_{aq} - Q_{aq} = M^{(B)}_{aq} twTr(q, a)` and a fixed-time Stein moment bound on `twTr` at the one-time
Gaussian law of `gueHBA … k` (`ol_gueHBA_eq`). `0 < g` only eventually (coverage row 14). -/
def T2519_HoffBA (d : ℕ) : Prop :=
  3 ≤ d → ∀ (sz : Sizes d) (κ Λ : ℝ), 0 < κ → 0 < Λ →
    ∀ (g E t1 t0 : ℕ → ℝ) (m : ℕ → ℂ) (n0 : ℕ) (Kt : ∀ n, ℝ → LoopIdx (Zd d (sz.L n)) → ℂ),
    Tendsto (fun n => sz.size n) atTop atTop → 1 ≤ n0 →
    (∀ᶠ n in atTop, 0 < g n ∧ g n ≤ Λ) → (∀ n, BAReal d (sz.L n) (g n) κ (E n) (m n)) →
    (∀ n, 0 ≤ t1 n) → (∀ n, t1 n ≤ t0 n) → (∀ n, t0 n < 1) →
    (∀ n, ∀ s ∈ Set.Icc (t1 n) (t0 n), ∀ (σ : Bool) (a : Zd d (sz.L n)), Kt n s ⟨[σ], [a]⟩ = mSigOf (m n) σ) →
    T2519_PathBoundsBA sz g E t1 t0 m (gueGridK sz n0) n0 Kt →
    StochDomAt (Pgue (sz.withLam 0)) sz.size
      (fun n (p : Fin (gueGridK sz n0 n + 1) × Zd d (sz.L n) × Zd d (sz.L n)) ω =>
        ‖(((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * ∑ x ∈ Iblk d (sz.L n) (sz.W n) p.2.1, ∑ y ∈ Iblk d (sz.L n) (sz.W n) p.2.2,
            Mres (((g n : ℝ) : ℂ) • PsiI d (sz.L n) (sz.W n)) (E n : ℂ) (m n) x y *
              Gres (gueHBA sz g t1 t0 (gueGridK sz n0) n p.1 ω)
                (ztOf (m n) (E n) (gridTime t1 t0 (gueGridK sz n0) n p.1)) true y x -
          BAMss d (sz.L n) (BAMB d (sz.L n) (g n) (E n : ℂ) (m n)) true true p.2.1 p.2.2‖)
      (fun n p _ => ‖BAMB d (sz.L n) (g n) (E n : ℂ) (m n) p.2.1 p.2.2‖ *
        (((sz.size n : ℕ) : ℝ) * etaOf (m n) (gridTime t1 t0 (gueGridK sz n0) n p.1))⁻¹)









/-- **Target 4a, `map_gueHBA_eq_mixMatBA`** (twin of `map_gueH_eq_mixMat`, `EntryGrid:118`): under `Pgue (sz.withLam 0)`
the BA grid path at step `k` has the law of C3 b's mixture `g Ψ_I + √t₁ X_block + √(u_k - t₁) X_GUE` under the BA carrier
law `ouP (UNModel.band (sz.withLam 0)) n`; consumer: `gueGrid_entry_boundBA` (from `gueEntryMixBA`). -/
def T2519_MapMixBA : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (g t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ), 0 ≤ t1 n → t1 n ≤ t0 n →
    (Pgue (sz.withLam 0)).map (gueHBA sz g t1 t0 K n k) =
      (ouP (UNModel.band (sz.withLam 0)) n).map (mixMatBA sz n (g n) (t1 n) (gridTime t1 t0 K n k - t1 n))
end RBM.BA.T2519Check
