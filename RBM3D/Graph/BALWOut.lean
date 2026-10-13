/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Graph.BAExp14a2
import RBM3D.Graph.BAExp14b2B

/-!
# BA-L L6 (T2494), file C: the closures of the L4a2 successor pins (`lem:LWterm_EXP` at BA)

Paper: arXiv:2507.20274, `paper/tex/6_Step6_two_loop.tex:83-88` (`lem:LWterm_EXP`),
`paper/tex/7_8_light_weight.tex:10` (`(eq:EGC)`), `paper/tex/B_graphical_lemmas.tex:7-15`
(`(eq:ELW_term)`), `:118` ("analogous ... omit"; route R1, paper delta T2398d of the L4a2 row).

The last terminal row of stage L (supervisor `2026-10-12-2246` L40-C1): the two closures that the
L4a2 row (`Graph/BAExp14a2.lean`, T2490) left open, because their antecedent `BAExp14bS2` was
produced by the L4b2b row (`baExp14bS2_holds`, `Graph/BAExp14b2B.lean`, T2489) only afterwards.

* **`baLWCutExpTw_holds : ∀ d, BALWCutExpTw d`** (the R1 cut pin, seven premises): the assembly
  `baLWCutExpTw_of_S2` at `baExp14bS2_holds d`.
* **`baLWtermEXPTw_holds : ∀ d, BALWtermEXPTw d`** (the seven-premise successor of `BALWtermEXP`,
  `BA/LWPinsBA.lean:49`): the composition `baLWtermEXPTw_of_S2` at `baExp14bS2_holds d`.
* Compiled nonempty instances at `d = 3` (`sz0`, `zSeq`, `flow_sz0`, `t ≡ 1/2`), with TL1
  discharged by `baTwistAvgProd_holds 3` (`BA/TwistAvgB.lean`); TL2 and the five Step 1/2 pins
  stay hypotheses (other gates' pins).

`BAExp14bS2` is read at the merged type only, through `baExp14bS2_holds`; it is not a binder of
any public result.  No pin of the stage-L registry is edited here.
-/

set_option linter.style.longLine false
set_option linter.style.setOption false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open MeasureTheory Filter

noncomputable section

namespace RBM.BA

open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes RBM.Graph

/-- **`lem:LWterm_EXP` at BA, the cut pin (target 7 (a); = `T2490_CutClosed`)**: the R1 cut pin
`BALWCutExpTw d` (`Graph/BAExp14a2.lean:82`) for every `d`; `baLWCutExpTw_of_S2` applied to the
binding conclusion `baExp14bS2_holds` of L4b2. -/
theorem baLWCutExpTw_holds : ∀ d : ℕ, BALWCutExpTw d :=
  fun d => baLWCutExpTw_of_S2 d (baExp14bS2_holds d)

/-- **`lem:LWterm_EXP` at BA (target 7 (b); = `T2490_TermClosed`)**: the seven-premise successor of
`BALWtermEXP`, `BALWtermEXPTw d` (`Graph/BAExp14a2.lean:92`), for every `d`;
`baLWtermEXPTw_of_S2` applied to `baExp14bS2_holds`. -/
theorem baLWtermEXPTw_holds : ∀ d : ℕ, BALWtermEXPTw d :=
  fun d => baLWtermEXPTw_of_S2 d (baExp14bS2_holds d)

/-! ## Compiled nonempty instances (`d = 3`)

Data: `sz0` (`n = 0`: `L = 4`, `W = 32`, `N = 2097152`, `λ = 1/64`), `zSeq`, `flow_sz0`
(`κ = 1/2`, `ε = 𝔡 = 1/10`, `𝔠 = 1/6`), `t ≡ 1/2 ≤ BAflowT0` (`half_lt_t0`).  Every deterministic
hypothesis is discharged (`3 ≤ 3`, `0 < 1/2`, `0 < 1/10`, `flow_sz0`, `0 ≤ t`, `t ≤ BAflowT0`);
TL1 is `baTwistAvgProd_holds 3` applied to the average law and `STLmaxgL`.  What stays a
hypothesis is another gate's input: the five Step 1/2 pins (`STLocalEntrygL`, `LWAvgLawgL`,
`STLmaxgL`, `STLKgL`, `STDecaygL`) and TL2 (`BATwistLoopLaw`).  The index set
`λ²/L^d ≤ 1 - t` is all of the sizes at `t ≡ 1/2` (`λ_n ≤ 1/64`, `L_n ≥ 1`). -/

section Inst

open RBM.BA.FlowPinsInst RBM.Gauss.SizesInst

local notation "μ0" => Sizes.seqP (sz0.withLam 0)

/-- `λ_n²/L_n³ ≤ 1 - 1/2` at every size of `sz0`: the index sets of the two instances are nonempty. -/
private theorem BALWOut_reg (n : ℕ) : sz0.lam n ^ 2 / ((sz0.L n : ℕ) : ℝ) ^ 3 ≤ 1 - (1 / 2 : ℝ) := by
  have hx : (2 : ℝ) ≤ 2 * ((n : ℝ) + 1) := by have := Nat.cast_nonneg (α := ℝ) n; linarith
  have hlam : sz0.lam n ≤ 1 / 64 := by
    change ((2 * ((n : ℝ) + 1)) ^ 6)⁻¹ ≤ 1 / 64
    rw [one_div]
    exact inv_anti₀ (by norm_num) (by nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hx 6])
  have hlam0 : 0 ≤ sz0.lam n := by change 0 ≤ ((2 * ((n : ℝ) + 1)) ^ 6)⁻¹; positivity
  have hL1 : (1 : ℝ) ≤ ((sz0.L n : ℕ) : ℝ) := by exact_mod_cast (by have := sz0.three_le_L n; omega : 1 ≤ sz0.L n)
  have h1 : sz0.lam n ^ 2 / ((sz0.L n : ℕ) : ℝ) ^ 3 ≤ sz0.lam n ^ 2 :=
    div_le_self (by positivity) (one_le_pow₀ hL1)
  have h2 : sz0.lam n ^ 2 ≤ (1 / 64) ^ 2 := pow_le_pow_left₀ hlam0 hlam 2
  nlinarith

example : ∀ n, Nonempty {_p : (Fin 2 → Bool) × (Fin 2 → Zd 3 (sz0.L n)) //
    sz0.lam n ^ 2 / ((sz0.L n : ℕ) : ℝ) ^ 3 ≤ 1 - (1 / 2 : ℝ)} :=
  fun n => ⟨⟨(fun _ => true, fun _ => 0), BALWOut_reg n⟩⟩

/-- **Instance of target 7 (b)** (`baLWtermEXPTw_holds 3`, shape of the check `T2494_EXPClosed` and of
instance 8 (c)): `‖𝔼 𝓔^{Gc,(2)}‖ ≺ (1 - t)⁻¹ (W^{-d} B_{t,0})^{5/2}` on `λ²/L^d ≤ 1 - t` at the data
above; TL1 produced by `baTwistAvgProd_holds 3`. -/
example (hE : STLocalEntrygL (baFMz sz0 zSeq) μ0 (fun _ => 1 / 2))
    (hA : LWAvgLawgL (baFMz sz0 zSeq) μ0 (fun _ => 1 / 2)) (hM : STLmaxgL (baFMz sz0 zSeq) μ0 (fun _ => 1 / 2))
    (hK : STLKgL (baFMz sz0 zSeq) μ0 (fun _ => 1 / 2)) (hD : STDecaygL (baFMz sz0 zSeq) μ0 (fun _ => 1 / 2))
    (hT2 : BATwistLoopLaw (baFMz sz0 zSeq) μ0 (fun _ => 1 / 2)) :
    PrecL sz0 μ0 (U := fun n => {_p : (Fin 2 → Bool) × (Fin 2 → Zd 3 (sz0.L n)) //
        sz0.lam n ^ 2 / ((sz0.L n : ℕ) : ℝ) ^ 3 ≤ 1 - (1 / 2 : ℝ)})
      (fun n p _ => ‖∫ ω, LWEg (baFMz sz0 zSeq) n (1 / 2 : ℝ) p.1.1 p.1.2 ω ∂μ0‖)
      (fun n _ _ => (1 - (1 / 2 : ℝ))⁻¹ * (sz0.Bctl n (1 / 2 : ℝ)) ^ (5 / 2 : ℝ)) :=
  baLWtermEXPTw_holds 3 le_rfl (1 / 2) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 6) sz0 zSeq flow_sz0
    (fun _ => 1 / 2) (fun _ => by norm_num) (fun n => (half_lt_t0 n).le) hE hA hM hK hD
    (baTwistAvgProd_holds 3 le_rfl (1 / 2) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 6) sz0 zSeq flow_sz0
      (fun _ => 1 / 2) (fun _ => by norm_num) (fun n => (half_lt_t0 n).le) hA hM) hT2

/-- **Instance of target 7 (a)** (`baLWCutExpTw_holds 3`): the same data, the cut `𝓔 LWcutg` for every pair of
charges and blocks. -/
example (hE : STLocalEntrygL (baFMz sz0 zSeq) μ0 (fun _ => 1 / 2))
    (hA : LWAvgLawgL (baFMz sz0 zSeq) μ0 (fun _ => 1 / 2)) (hM : STLmaxgL (baFMz sz0 zSeq) μ0 (fun _ => 1 / 2))
    (hK : STLKgL (baFMz sz0 zSeq) μ0 (fun _ => 1 / 2)) (hD : STDecaygL (baFMz sz0 zSeq) μ0 (fun _ => 1 / 2))
    (hT2 : BATwistLoopLaw (baFMz sz0 zSeq) μ0 (fun _ => 1 / 2)) :
    PrecL sz0 μ0 (U := fun n => {_p : (Bool × Bool) × (Zd 3 (sz0.L n) × Zd 3 (sz0.L n)) //
        sz0.lam n ^ 2 / ((sz0.L n : ℕ) : ℝ) ^ 3 ≤ 1 - (1 / 2 : ℝ)})
      (fun n p _ => ‖∫ ω, LWcutg (baFMz sz0 zSeq) n (1 / 2 : ℝ) p.1.1.1 p.1.1.2 p.1.2.1 p.1.2.2 ω ∂μ0‖)
      (fun n _ _ => (1 - (1 / 2 : ℝ))⁻¹ * (sz0.Bctl n (1 / 2 : ℝ)) ^ (5 / 2 : ℝ)) :=
  baLWCutExpTw_holds 3 le_rfl (1 / 2) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 6) sz0 zSeq flow_sz0
    (fun _ => 1 / 2) (fun _ => by norm_num) (fun n => (half_lt_t0 n).le) hE hA hM hK hD
    (baTwistAvgProd_holds 3 le_rfl (1 / 2) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 6) sz0 zSeq flow_sz0
      (fun _ => 1 / 2) (fun _ => by norm_num) (fun n => (half_lt_t0 n).le) hA hM) hT2

end Inst

end RBM.BA

end
