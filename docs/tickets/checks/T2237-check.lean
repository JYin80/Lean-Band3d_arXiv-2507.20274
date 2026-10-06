import RBM3D.BA.FlowPins
import RBM3D.BA.CouplingWindow
import RBM3D.Induction.ConArg

/-!
# T2237 check file (dispatcher V1, Tue Oct  6 00:45 UTC 2026): BA-S1 `BA/ConArg`

Statements only (no proofs).  Section 1: the merged names the ticket uses.  Section 2: the intermediate
statements of the route (supervisor `2026-10-05-1806` §1.4; `2026-10-05-2252` Q3), each `…_stmt` a target of
`RBM3D/BA/ConArg.lean` with the same body (name without `_stmt`).  Section 3: the hypothesis bundle of
`BAConArg'` and the two conjunct statements (the split line, if the preflight estimates > 1500 lines).
-/

open MeasureTheory ProbabilityTheory Filter Matrix

/-! ## 1. Merged names (`main` 3a58663) -/

-- the pin and its vocabulary (`RBM3D/BA/FlowPins.lean`, b750bf3)
#check @RBM.BA.BAConArg'
#check @RBM.BA.BAConArgLoop
#check @RBM.BA.BAConArgVec
#check @RBM.BA.BAlamS
#check @RBM.BA.BAvecEntry
#check @RBM.BA.BAFlow
#check @RBM.BA.BAflowT0
#check @RBM.BA.BAflowEs
#check @RBM.BA.BAflowLam0
#check @RBM.BA.baFMz
#check @RBM.BA.baFM
#check @RBM.BA.FlowFM
#check @RBM.BA.BAmF
#check @RBM.BA.BAGt
#check @RBM.BA.BALloop
#check @RBM.BA.PrecL
#check @RBM.BA.STLmaxgL
#check @RBM.BA.baSelf_none_of_gt
#check @RBM.BA.BAm_eq_zero_of_gt
#check @RBM.BA.BAConArg'_premise_diag
#check @RBM.BA.not_BAConArg_of_data
#check @RBM.BA.FlowPinsInst.zSeq
#check @RBM.BA.FlowPinsInst.flow_sz0
#check @RBM.BA.FlowPinsInst.t0_sz0
#check @RBM.BA.FlowPinsInst.inst_BAConArg'
#check @RBM.BA.FlowPinsInst.inst_premise_diag

-- deterministic layer (`RBM3D/BA/MFixedPoint.lean`, ae63e74; `RBM3D/BA/CouplingWindow.lean`, e1fec21)
#check @RBM.BA.BASelf
#check @RBM.BA.BAm
#check @RBM.BA.BAm_self
#check @RBM.BA.BAm_real_eq_of_self
#check @RBM.BA.BAdom
#check @RBM.BA.BAt0
#check @RBM.BA.BAflowE
#check @RBM.BA.BAt0_pos
#check @RBM.BA.BAt0_lt_one
#check @RBM.BA.BAzztE_data
#check @RBM.BA.BAward_avg
#check @RBM.BA.BAself_im_le_one

-- the flow and the loops (`Gauss/BlockAnderson.lean`, `Loop/GLoopFlow.lean`, 868b3b4; `Gauss/FineModel.lean`, 0a873f1)
#check @RBM.Gauss.Sizes.seqHflowBA
#check @RBM.Gauss.Sizes.seqHflow_eq_smul
#check @RBM.Gauss.ztOf
#check @RBM.Gauss.etaOf
#check @RBM.Gauss.Gres
#check @RBM.Gauss.loopM
#check @RBM.Gauss.loopFine

-- the band model of the proof (`Induction/ConArg.lean`, 8a8cfeb; `Induction/ConArgDet.lean`, bbd22a5;
-- `Induction/Split.lean`, aa42e43; `Induction/ScaleFacts.lean`, 5d1e6b1; `Induction/Defs.lean`, 64bdfd3)
#check @RBM.Gauss.Sizes.stConArg_holds
#check @RBM.Gauss.Sizes.STConArg
#check @RBM.Gauss.Sizes.STomegaC
#check @RBM.Ind.ConArgPin
#check @RBM.Ind.conArg
#check @RBM.Ind.ztTilde
#check @RBM.Ind.ztTilde_arith
#check @RBM.Ind.loopMax
#check @RBM.Ind.loopMax_nonneg
#check @RBM.Ind.loopMax_odd_sq_le
#check @RBM.Ind.loopMax_two_mul_le_tilde
#check @RBM.Gauss.Sizes.STBctl_pos

-- stochastic domination (`Defs/StochDomAt.lean`, 9e2b00f)
#check @RBM.Path.PerTimeDomAt
#check @RBM.Path.perTimeOfStochDomAt
#check @RBM.Path.stochDomAt_of_perTimeDomAt
#check @RBM.Gauss.Sizes.tendsto_size

namespace RBM.BA.T2237Check

open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes RBM.BA

/-! ## 2. Intermediate statements (targets of `RBM3D/BA/ConArg.lean`, names without `_stmt`) -/

/-- **Same-`ω` scaling** (1806 §1.4): `H_t(g₀) = √(t/s) · H_s(g_s)` for `g_s = √(s/t) g₀` (`BAlamS`), with the
same `ω` (`seqHflowBA`: `g₀Ψ + √u X(ω)`; `seqHflow_eq_smul`). -/
def BAhflow_scale_stmt (d : ℕ) : Prop :=
  ∀ (sz : Sizes d) (z : ℕ → ℂ) (s t : ℕ → ℝ) (n : ℕ) (ω : sz.SeqΩ), 0 < s n → 0 < t n →
    sz.seqHflowBA (BAflowLam0 sz z) n (t n) ω =
      ((Real.sqrt (t n / s n) : ℝ) : ℂ) • sz.seqHflowBA (BAlamS sz z s t) n (s n) ω

/-- **Resolvent scaling**: `(rH - rw)^{-1} = r^{-1}(H - w)^{-1}` for real `r ≠ 0`, both charges (the BA form
of the band's private `conArg_Gres_smul_mul`, `Induction/ConArg.lean:409`). -/
def BAGres_smul_stmt : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (H : Matrix ι ι ℂ) (w : ℂ) (σ : Bool) (r : ℝ), r ≠ 0 →
    Gres ((r : ℂ) • H) ((r : ℂ) * w) σ = ((r : ℂ))⁻¹ • Gres H w σ

/-- **`η`-monotonicity** of `Im v^*G(x+iy)v` at a fixed Hermitian matrix: `y ↦ y · Im G_vv` is nondecreasing and
`y ↦ Im G_vv / y` is nonincreasing (spectral decomposition). -/
def BAimG_eta_mono_stmt : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (H : Matrix ι ι ℂ) (v : ι → ℂ) (x y y' : ℝ),
    H.IsHermitian → 0 < y → y ≤ y' →
      y * (BAvecEntry (Gres H ((x : ℂ) + (y : ℂ) * Complex.I) true) v v).im ≤
          y' * (BAvecEntry (Gres H ((x : ℂ) + (y' : ℂ) * Complex.I) true) v v).im ∧
        (BAvecEntry (Gres H ((x : ℂ) + (y' : ℂ) * Complex.I) true) v v).im / y' ≤
          (BAvecEntry (Gres H ((x : ℂ) + (y : ℂ) * Complex.I) true) v v).im / y

/-- **Poisson-kernel comparison** (1806 §1.4): `Im G_vv(x+iy) ≤ (2 + 2C²) Im G_vv(x'+iy)` for `|x - x'| ≤ C y`. -/
def BAimG_poisson_stmt : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (H : Matrix ι ι ℂ) (v : ι → ℂ) (x x' y C : ℝ),
    H.IsHermitian → 0 < y → 0 ≤ C → |x - x'| ≤ C * y →
      (BAvecEntry (Gres H ((x : ℂ) + (y : ℂ) * Complex.I) true) v v).im ≤
        (2 + 2 * C ^ 2) * (BAvecEntry (Gres H ((x' : ℂ) + (y : ℂ) * Complex.I) true) v v).im

/-- `|m| ≤ 1` for every solution of `(self_m)` with `Im z ≥ 0` (`BAward_avg` + Cauchy–Schwarz, 1806 §1.1; public
form of the private step inside `baSelf_none_of_gt`). -/
def BAself_norm_le_one_stmt : Prop :=
  ∀ (d L : ℕ) [NeZero L] (g : ℝ) (z m : ℂ), 0 ≤ z.im → BASelf d L g z m → ‖m‖ ≤ 1

/-- **The bulk energy is bounded**: `Im m(E, g) > 0 ⇒ |E| ≤ 2 + 2d|g|` (contrapositive of `BAm_eq_zero_of_gt`).
With `(eq:WO)` (`g_n ≤ 𝔡⁻¹` eventually) this gives `|E_n| ≤ Λ := 2 + 2d/𝔡` eventually. -/
def BAenergy_le_stmt : Prop :=
  ∀ (d L : ℕ) [NeZero L] (g E : ℝ), 0 < (BAm d L g (E : ℂ)).im → |E| ≤ 2 + 2 * d * |g|

/-- **The shifted spectral parameter** (BA form of `ztTilde_arith`, `ConArgDet.lean:850`):
`z̃ = √(t/s) z_s(E, g_s)`; constants depend on `(c, κ, Λ)` only.  The fourth conjunct replaces the band's
`η_t ≤ η_s` (false in general for BA: the couplings differ). -/
def BAztTilde_arith_stmt : Prop :=
  ∀ c κ Λ : ℝ, 0 < c → 0 < κ → 0 < Λ → ∃ C : ℝ, 0 < C ∧
    ∀ (E s t : ℝ) (m₀ ms : ℂ), c ≤ s → s ≤ t → t < 1 → |E| ≤ Λ → ‖m₀‖ ≤ 1 → ‖ms‖ ≤ 1 → κ ≤ ms.im →
      ‖ztOf m₀ E t - (Real.sqrt (t / s) : ℂ) * ztOf ms E s‖ ^ 2 ≤ C * etaOf ms s ^ 2 ∧
      etaOf ms s ≤ ((Real.sqrt (t / s) : ℂ) * ztOf ms E s).im ∧
      ((Real.sqrt (t / s) : ℂ) * ztOf ms E s).im ≤ C * etaOf ms s ∧
      etaOf m₀ t ≤ C * etaOf ms s

/-- **Comparison of the `Im`-trace factors** (η-monotonicity + Poisson comparison + scaling, deterministic,
every `ω`): `max_a tr(Im G_s(z_s, g_s) E_a) ≤ C (η_s/η_t) tr(Im G_t(z_t, g₀) E_a)`, written with the `k = 1`
loops of the two carriers as in `BAConArgLoop`.  Preflight item P1 decides whether this (with a lower bound on
the left side) is the route of the `max_a tr(Im G_t E_a)` factor. -/
def BAimTrace_compare_stmt (d : ℕ) : Prop :=
  ∀ c κ Λ : ℝ, 0 < c → 0 < κ → 0 < Λ → ∃ C : ℝ, 0 < C ∧
    ∀ (sz : Sizes d) (z : ℕ → ℂ) (s t : ℕ → ℝ) (n : ℕ) (ω : sz.SeqΩ) (a : Zd d (sz.L n)),
      0 < (z n).im → c ≤ s n → s n ≤ t n → t n < 1 → |BAflowEs sz z n| ≤ Λ →
      κ ≤ (BAmF sz (BAlamS sz z s t) (BAflowEs sz z) n).im →
        ((baFM sz (BAlamS sz z s t) (BAflowEs sz z)).L n (s n) (fun _ : Fin 1 => true) (fun _ => a) ω -
            (baFM sz (BAlamS sz z s t) (BAflowEs sz z)).L n (s n) (fun _ : Fin 1 => false) (fun _ => a) ω).im ≤
          C * ((baFM sz (BAlamS sz z s t) (BAflowEs sz z)).eta n (s n) / (baFMz sz z).eta n (t n)) *
            ((baFMz sz z).L n (t n) (fun _ : Fin 1 => true) (fun _ => a) ω -
              (baFMz sz z).L n (t n) (fun _ : Fin 1 => false) (fun _ => a) ω).im

/-! ## 3. The hypothesis bundle of `BAConArg'` and the two conjuncts -/

/-- The hypotheses of `BAConArg'` (`FlowPins.lean:630-636`), verbatim, as one conjunction. -/
def BAConArgHyp {d : ℕ} (κ ε 𝔡 ε₁ 𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ) (s t : ℕ → ℝ) : Prop :=
  0 < κ ∧ 0 < ε ∧ 0 < 𝔡 ∧ 0 < ε₁ ∧ BAFlow sz κ ε 𝔠 𝔡 z ∧ (∀ n, ε₁ ≤ s n) ∧ (∀ n, s n ≤ t n) ∧
    (∀ n, t n < 1) ∧ (∀ n, κ ≤ (BAmF sz (BAlamS sz z s t) (BAflowEs sz z) n).im) ∧
    STLmaxgL (baFM sz (BAlamS sz z s t) (BAflowEs sz z)) (Sizes.seqP (sz.withLam 0)) s

/-- Conjunct 1 (`(res_lo_bo_eta_BA)`, `7_8:1965`): `baConArgLoop_holds`. -/
def baConArgLoop_holds_stmt (d : ℕ) : Prop :=
  ∀ (κ ε 𝔡 ε₁ 𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ) (s t : ℕ → ℝ), BAConArgHyp κ ε 𝔡 ε₁ 𝔠 sz z s t →
    ∀ k : ℕ, 2 ≤ k → BAConArgLoop sz z s t k

/-- Conjunct 2 (`(eq:ImGs)` ⇒ `(eq:ImGt)`, `7_8:1976-1979`): `baConArgVec_holds`. -/
def baConArgVec_holds_stmt (d : ℕ) : Prop :=
  ∀ (κ ε 𝔡 ε₁ 𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ) (s t : ℕ → ℝ), BAConArgHyp κ ε 𝔡 ε₁ 𝔠 sz z s t →
    BAConArgVec sz z s t

-- The target: `baConArg'_holds (d : ℕ) : BAConArg' d` (the merged pin, unchanged).
example : Prop := ∀ d : ℕ, BAConArg' d

-- The instance target (`RBM.BA.ConArgInst.inst_baConArg'`): `s ≡ t ≡ 1/2`, `κ = ε₁ = 1/2` at `sz0`, `zSeq`;
-- only the loop bound `(eq:loopbound_s)` at `s` stays a hypothesis.
example : Prop :=
  STLmaxgL (baFM RBM.Gauss.SizesInst.sz0
      (BAlamS RBM.Gauss.SizesInst.sz0 RBM.BA.FlowPinsInst.zSeq (fun _ => 1 / 2) (fun _ => 1 / 2))
      (BAflowEs RBM.Gauss.SizesInst.sz0 RBM.BA.FlowPinsInst.zSeq))
    (Sizes.seqP (RBM.Gauss.SizesInst.sz0.withLam 0)) (fun _ => 1 / 2) →
  (∀ k : ℕ, 2 ≤ k →
      BAConArgLoop RBM.Gauss.SizesInst.sz0 RBM.BA.FlowPinsInst.zSeq (fun _ => 1 / 2) (fun _ => 1 / 2) k) ∧
    BAConArgVec RBM.Gauss.SizesInst.sz0 RBM.BA.FlowPinsInst.zSeq (fun _ => 1 / 2) (fun _ => 1 / 2)

end RBM.BA.T2237Check
