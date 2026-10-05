/-
Release check for T2168 (dispatcher V1, Mon Oct  5 03:25 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §16, §20, §28, §29, §36, §45 O2).
ST2-12: `STGridRepN` part 1 -- the canonical split `A_k = A_0 + Δ Σ_{j<k} Drift_j + Rem_k + Mart_k` of the grid
observable at every loop length, the remainder bound `‖Rem_k‖ ≤ N^{m+9} Δ^{1/2}`, and the assembly of the pins
`STGridRepN` / `STGridMart` from it and the two tail statements owed to ST2-13.  Section 1: the merged names it
builds on (`Induction/{Step2Defs,Step2Iterate,GridDuhamelN,GridDriftN,GridEnvelopeN,NQGood1,Split}`,
`Loop/KLFinal`, `Defs/Semicircle`, `Green/CondDom`, `Path/OneStep`, the instance data) and the downstream pins.
Section 2: the pinned vocabulary (five definitions), in namespace `RBM.Ind.T2168Check` here; T2168 defines it in
`RBM.Ind` verbatim.  Section 3: the pinned theorem statements as `Prop`s (elaboration check only; each target
theorem's type is the body of the corresponding `Prop`).
Statement and `#check` only: no proofs, no `sorry`.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2168-check.lean`.
-/
import RBM3D

/-! ## 1. Merged names -/

-- the pin and its vocabulary (`Induction/Step2Defs`, ST2-01 = T2066; identifications `Induction/Step2Iterate`)
#check @RBM.Gauss.Sizes.STGridRepNAt
#check @RBM.Gauss.Sizes.STGridRepN
#check @RBM.Gauss.Sizes.STGridMartAt
#check @RBM.Gauss.Sizes.STGridMart
#check @RBM.Gauss.Sizes.STgAN
#check @RBM.Gauss.Sizes.STgDriftN
#check @RBM.Gauss.Sizes.STLKIM
#check @RBM.Gauss.Sizes.STLKM
#check @RBM.Gauss.Sizes.STksimLKM
#check @RBM.Gauss.Sizes.STelklkM
#check @RBM.Gauss.Sizes.STegtM
#check @RBM.Gauss.Sizes.STeeM
#check @RBM.Gauss.Sizes.STeeUM
#check @RBM.Gauss.Sizes.STLKM_eq_STLKIM
#check @RBM.Gauss.Sizes.STgA_eq_STgAN
#check @RBM.Gauss.Sizes.STgDrift_eq_STgDriftN
#check @RBM.Gauss.Sizes.STEEM_eq_STeeM
-- flow, sizes, `ML:Kbound` at the sequence level, Lemma 2.8
#check @RBM.Gauss.Sizes.STFlow
#check @RBM.Gauss.Sizes.STflowE
#check @RBM.Gauss.Sizes.locDomain
#check @RBM.Gauss.Sizes.Admissible
#check @RBM.Gauss.Sizes.SizeTendsto
#check @RBM.Gauss.Sizes.size
#check @RBM.Gauss.Sizes.STKbound
#check @RBM.Gauss.Sizes.stKbound_of_flow
#check @RBM.lemT
#check @RBM.lemE
#check @RBM.lemT_lt_one
#check @RBM.abs_lemE_le
#check @RBM.lemma28_quant
#check @RBM.zt_im
#check @RBM.norm_mSigma
#check @RBM.Gauss.etaT
#check @RBM.Gauss.etaT_pos
#check @RBM.Green.etaT_le_of_le
-- grid walk, Duhamel vocabulary, one grid step of the hierarchy, envelopes
#check @RBM.Path.gridStep
#check @RBM.Path.gridTime
#check @RBM.Path.gridTime_last
#check @RBM.Path.pathH
#check @RBM.Path.pathH_isHermitian
#check @RBM.Path.pathP
#check @RBM.Path.filt
#check @RBM.Ind.Ugen
#check @RBM.Ind.AvecN
#check @RBM.Ind.martIncN
#check @RBM.Ind.predIncN
#check @RBM.ThetaN
#check @RBM.UN
#check @RBM.uKer
#check @RBM.Ind.GridDriftN
#check @RBM.Ind.gridDriftN_at
#check @RBM.Ind.gridDriftN_envelope
#check @RBM.Ind.stepErrN
#check @RBM.Ind.kStepC
#check @RBM.Ind.uStepC
#check @RBM.Path.envConst
#check @RBM.Ind.exists_norm_Kcal_le_win
#check @RBM.Ind.driftTensorN
#check @RBM.Ind.norm_gloop_le_of_le_abs_im
#check @RBM.Loop.KLK
#check @RBM.Loop.KLloopOf
#check @RBM.Gauss.loopOf
-- instance data
#check @RBM.Gauss.SizesInst.sz0
#check @RBM.Gauss.SizesInst.sz0_tendsto
#check @RBM.Gauss.InductionDefsInst.z0
#check @RBM.Gauss.InductionDefsInst.flow_z0
#check @RBM.Gauss.InductionDefsInst.sInst
#check @RBM.Gauss.InductionDefsInst.tInst
#check @RBM.Gauss.InductionDefsInst.sixteenth_le_lemT
-- downstream (consumers of `STGridRepN`, `STGridMart`)
#check @RBM.Gauss.Sizes.ST_gridMart_of_repN
#check @RBM.Gauss.Sizes.ST_step2_of_pinsN
#check @RBM.Gauss.Sizes.ST_step2_of_pinsN'
#check @RBM.Gauss.Sizes.ST_step2_of_pinsLW'
#check @RBM.Gauss.Sizes.STStep2
#check @RBM.Gauss.Sizes.stOptL2_of_pins
#check @RBM.Gauss.Step2DefsInst.inst_gridRepN
#check @RBM.Gauss.Sizes.STDuhamelConcl

/-! ## 2. Pinned vocabulary (T2168 target 1; defined in `RBM.Ind` verbatim) -/

noncomputable section

namespace RBM.Ind.T2168Check

open MeasureTheory Filter RBM RBM.Loop RBM.Gauss RBM.Gauss.Sizes RBM.Path RBM.Ind
open scoped NNReal ENNReal

/-- **The martingale part** `Mart_k = Σ_{j<k} ξ_{j+1}`, `ξ_{j+1} = A_{j+1} - 𝔼[A_{j+1} | F_j]` (the merged
`martIncN`), of the grid observable `A_j = (𝓛 - 𝒦)^{(m)}_{u_j,σ,a}(H_j)` at the label pair `i = (σ, a)`; the
type is that of `Mart` in `STGridRepNAt`. -/
def difRepMartN {d : ℕ} (sz : Sizes d) (E s t : ℕ → ℝ) (K : ℕ → ℕ) {m : ℕ} (n : ℕ)
    (i : (Fin m → Bool) × (Fin m → Zd d (sz.L n))) (k : ℕ) (ω : PathΩ sz) : ℂ :=
  ∑ j ∈ Finset.range k, martIncN sz E s t K n j i.1 ω i.2

/-- **The remainder** `Rem_k = Σ_{j<k} (𝔼[A_{j+1} | F_j] - A_j - Δ Drift_j)`, `Drift_j` the merged general-`n`
drift `STgDriftN` (`(eq_L-Keee)`, `3_5:73`) at `(u_j, H_j)`; the type is that of `Rem` in `STGridRepNAt`. -/
def difRepRemN {d : ℕ} (sz : Sizes d) (E s t : ℕ → ℝ) (K : ℕ → ℕ) {m : ℕ} (n : ℕ)
    (i : (Fin m → Bool) × (Fin m → Zd d (sz.L n))) (k : ℕ) (ω : PathΩ sz) : ℂ :=
  ∑ j ∈ Finset.range k,
    ((pathP sz)[fun ω' => AvecN sz E s t K n (j + 1) i.1 ω' i.2 | filt sz j] ω -
      AvecN sz E s t K n j i.1 ω i.2 -
      ((gridStep s t K n : ℝ) : ℂ) * STgDriftN sz s t K n (E n) i.1 i.2 j ω)

/-- **Clauses (i)-(ii) of `STGridRepNAt d m C₀`** (`Step2Defs.lean:817`) for `Mart = difRepMartN`,
`Rem = difRepRemN`, with their own grid exponent: the decomposition, and `‖Rem_k‖ ≤ N^{C₀} Δ^{1/2}` a.e.,
for all `k ≤ K` at once, eventually in `n`. -/
def GridRepRemNAt (d m : ℕ) (C₀ : ℝ) : Prop :=
  ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z →
      ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n ≤ t n) → (∀ n, t n ≤ lemT (z n)) →
        ∃ CK : ℝ, 0 ≤ CK ∧
          ∀ K : ℕ → ℕ, (∀ n, K n ≠ 0) → (∀ᶠ n in atTop, ((sz.size n : ℕ) : ℝ) ^ CK ≤ K n) →
            (∀ (n : ℕ) (i : (Fin m → Bool) × (Fin m → Zd d (sz.L n))), ∀ᵐ ω ∂(pathP sz),
              ∀ k, k ≤ K n →
                STgAN sz s t K n (STflowE z n) i.1 i.2 k ω =
                  STgAN sz s t K n (STflowE z n) i.1 i.2 0 ω +
                    ((gridStep s t K n : ℝ) : ℂ) *
                      ∑ j ∈ Finset.range k, STgDriftN sz s t K n (STflowE z n) i.1 i.2 j ω +
                    difRepRemN sz (STflowE z) s t K n i k ω +
                    difRepMartN sz (STflowE z) s t K n i k ω) ∧
            (∀ᶠ n in atTop, ∀ i : (Fin m → Bool) × (Fin m → Zd d (sz.L n)),
              ∀ᵐ ω ∂(pathP sz), ∀ k, k ≤ K n →
                ‖difRepRemN sz (STflowE z) s t K n i k ω‖ ≤
                  ((sz.size n : ℕ) : ℝ) ^ C₀ * Real.sqrt (gridStep s t K n))

/-- **Clause (iii) of `STGridRepNAt`** (`(aaswtghh)` with Azuma + Doob, `3_5:220`) for `Mart = difRepMartN`:
the plain martingale tail, for all `k ≤ K` at once.  Owed to ST2-13. -/
def GridRepTailNAt (d m : ℕ) : Prop :=
  ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z →
      ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n ≤ t n) → (∀ n, t n ≤ lemT (z n)) →
        ∀ D : ℝ, 0 < D → ∃ CK : ℝ, 0 ≤ CK ∧
          ∀ K : ℕ → ℕ, (∀ n, K n ≠ 0) → (∀ᶠ n in atTop, ((sz.size n : ℕ) : ℝ) ^ CK ≤ K n) →
            ∀ ε' : ℝ, 0 < ε' → ∀ᶠ n in atTop, ∀ i : (Fin m → Bool) × (Fin m → Zd d (sz.L n)),
              pathP sz {ω | ∃ k, k ≤ K n ∧
                ((sz.size n : ℕ) : ℝ) ^ ε' *
                    (∑ j ∈ Finset.range k, gridStep s t K n *
                      ‖STeeM sz n (STflowE z n) (gridTime s t K n j) (pathH sz s t K n j ω)
                        i.1 i.2 i.2‖ + ((sz.size n : ℕ) : ℝ) ^ (-D)) ^ (1 / 2 : ℝ) <
                  ‖difRepMartN sz (STflowE z) s t K n i k ω‖} ≤
                ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-D))

/-- **Clause (iv) of `STGridRepNAt`** (`(alu9_STime)` with Azuma + Doob, `3_5:229`) for `Mart = difRepMartN`:
the `𝒰`-weighted martingale tail, for all `k ≤ K` at once.  Owed to ST2-13. -/
def GridRepWTailNAt (d m : ℕ) : Prop :=
  ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z →
      ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n ≤ t n) → (∀ n, t n ≤ lemT (z n)) →
        ∀ D : ℝ, 0 < D → ∃ CK : ℝ, 0 ≤ CK ∧
          ∀ K : ℕ → ℕ, (∀ n, K n ≠ 0) → (∀ᶠ n in atTop, ((sz.size n : ℕ) : ℝ) ^ CK ≤ K n) →
            ∀ ε' : ℝ, 0 < ε' → ∀ᶠ n in atTop, ∀ i : (Fin m → Bool) × (Fin m → Zd d (sz.L n)),
              pathP sz {ω | ∃ k, k ≤ K n ∧
                ((sz.size n : ℕ) : ℝ) ^ ε' *
                    (∑ j ∈ Finset.range k, gridStep s t K n *
                      ‖STeeUM sz n (STflowE z n) (gridTime s t K n j) (gridTime s t K n k)
                        (pathH sz s t K n j ω) i.1 i.2‖ + ((sz.size n : ℕ) : ℝ) ^ (-D)) ^
                        (1 / 2 : ℝ) <
                  ‖∑ j ∈ Finset.range k,
                    UN d (sz.L n) (sz.lam n) (fun i' => mSigma (STflowE z n) (i.1 i'))
                      (gridTime s t K n j) (gridTime s t K n k)
                      (fun b => difRepMartN sz (STflowE z) s t K n (i.1, b) (j + 1) ω -
                        difRepMartN sz (STflowE z) s t K n (i.1, b) j ω) i.2‖} ≤
                ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-D))

/-! ## 3. Pinned theorem statements (T2168 targets 2-5; elaboration only) -/

/-- Target 2, `difRep_identity`: the split is an identity, pathwise, for every `k` and `ω`. -/
def DifRepIdentityStmt : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (E s t : ℕ → ℝ) (K : ℕ → ℕ) {m : ℕ} (n : ℕ)
    (i : (Fin m → Bool) × (Fin m → Zd d (sz.L n))) (k : ℕ) (ω : PathΩ sz),
    STgAN sz s t K n (E n) i.1 i.2 k ω =
      STgAN sz s t K n (E n) i.1 i.2 0 ω +
        ((gridStep s t K n : ℝ) : ℂ) *
          ∑ j ∈ Finset.range k, STgDriftN sz s t K n (E n) i.1 i.2 j ω +
        difRepRemN sz E s t K n i k ω + difRepMartN sz E s t K n i k ω

/-- Target 2, `difRepMartN_succ_sub`: the increments of `difRepMartN` are the merged `martIncN`. -/
def DifRepMartSuccStmt : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (E s t : ℕ → ℝ) (K : ℕ → ℕ) {m : ℕ} (n : ℕ)
    (i : (Fin m → Bool) × (Fin m → Zd d (sz.L n))) (j : ℕ) (ω : PathΩ sz),
    difRepMartN sz E s t K n i (j + 1) ω - difRepMartN sz E s t K n i j ω =
      martIncN sz E s t K n j i.1 ω i.2

/-- Target 3, `difRep_Ugen_step_le`: one step of `𝒰` (the statement of the private `gdn_Ugen_step_le`,
`GridDriftN.lean:468`, made public). -/
def DifRepUgenStepStmt : Prop :=
  ∀ (d L : ℕ) [NeZero L] (g : ℝ), 3 ≤ L → ∀ {E : ℝ}, |E| ≤ 2 → ∀ {k : ℕ} (σ : Fin k → Bool) {u Δ : ℝ},
    0 ≤ u → 0 ≤ Δ → u + Δ < 1 → ∀ (A : (Fin k → Zd d L) → ℂ) (M : ℝ), (∀ y, ‖A y‖ ≤ M) →
      ∀ x : Fin k → Zd d L,
        ‖Ugen d L g E σ u (u + Δ) A x - A x -
            (Δ : ℂ) * ThetaN d L g (fun i => mSigma E (σ i)) u A x‖ ≤
          uStepC k Δ (u + Δ) * M

/-- Target 3, `difRep_flow_bounds`: the flow energy is in the bulk, `t₀ < 1`, and below `t₀` the
spectral height is `≥ N^{-1+ε}/16` and `≤ 1 - u` (Lemma 2.8, `(2.40)`). -/
def DifRepFlowBoundsStmt : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) {κ ε 𝔠 𝔡 : ℝ}, 0 < κ → ∀ {z : ℕ → ℂ}, STFlow sz κ ε 𝔠 𝔡 z →
    ∀ (n : ℕ) {u : ℝ}, u ≤ lemT (z n) →
      |STflowE z n| ≤ 2 - κ ∧ lemT (z n) < 1 ∧
        ((sz.size n : ℕ) : ℝ) ^ (-1 + ε) / 16 ≤ etaT (STflowE z n) u ∧
        etaT (STflowE z n) u ≤ 1 - u

/-- Target 4, `gridRepRemN_holds`: clauses (i)-(ii) with `C₀ = m + 9`, for `3 ≤ d` (DECISIONS §36). -/
def GridRepRemNHoldsStmt : Prop :=
  ∀ d : ℕ, 3 ≤ d → ∀ m : ℕ, 2 ≤ m → GridRepRemNAt d m ((m : ℝ) + 9)

/-- Target 5, `stGridRepNAt_of_parts`: the four clauses assemble to the pin at one loop length. -/
def StGridRepNAtOfPartsStmt : Prop :=
  ∀ (d m : ℕ) (C₀ : ℝ), 0 ≤ C₀ → GridRepRemNAt d m C₀ → GridRepTailNAt d m →
    GridRepWTailNAt d m → STGridRepNAt d m C₀

/-- Target 5, `stGridRepN_of_tails`: the pin `STGridRepN` from the two owed tails. -/
def StGridRepNOfTailsStmt : Prop :=
  ∀ d : ℕ, 3 ≤ d → (∀ m : ℕ, 2 ≤ m → GridRepTailNAt d m) →
    (∀ m : ℕ, 2 ≤ m → GridRepWTailNAt d m) → STGridRepN d

/-- Target 5, `stGridMartAt_of_parts2`: the loop-length-`2` pin needs only clauses (i)-(iii). -/
def StGridMartAtOfParts2Stmt : Prop :=
  ∀ (d : ℕ) (C₀ : ℝ), 0 ≤ C₀ → GridRepRemNAt d 2 C₀ → GridRepTailNAt d 2 → STGridMartAt d C₀

/-- Target 5, `stGridMart_of_tail`: the pin `STGridMart` from the plain tail at `m = 2` alone. -/
def StGridMartOfTailStmt : Prop :=
  ∀ d : ℕ, 3 ≤ d → GridRepTailNAt d 2 → STGridMart d

end RBM.Ind.T2168Check

end
