/-
Release check for T2359 (dispatcher V1, Fri Oct 9 01:53 UTC 2026; DECISIONS §162; supervisor 2026-10-09-0143 PASS, C4).  LW-13b R2 = M + X:
`claim:TTk` and the near pin in `ℓ^∞`, G2 for the exp class, the `(log W)^{3/2}` tail, (A).
Section 1: merged names (`main` 83847ef).  Section 2: the target statements (Prop values; no proof), copied from the T2348 probe
(`t/T2348:RBM3D/Probe/T2348Pins.lean`, 9f3bd75) with the prefix `T2359_`, and the (A) form fixed by §162 (2).
Amend 1 (Fri Oct 9 02:52 UTC 2026, DECISIONS §163 (1), supervisor 0243 L2): conjunct 2 of `T2359_LWXiE` on the subtype `λ²/L² < 1 - t`.
Run: `lake env lean docs/tickets/checks/T2359-check.lean`.
-/
import RBM3D.Graph.LWEngine
import RBM3D.Graph.AuxGraph2
import RBM3D.Graph.LWMoment
import RBM3D.Graph.LWMomExp
import RBM3D.Graph.LWMomExpD
import RBM3D.Graph.LWMomExpFar
import RBM3D.Graph.LWTermExpN

set_option linter.style.whitespace false
set_option linter.style.longLine false
noncomputable section
open MeasureTheory Matrix Filter
open RBM RBM.Gauss RBM.Green RBM.Graph RBM.Gauss.Sizes

-- Section 1
#check @RBM.EKTTk
#check @RBM.ekTTk_holds
#check @RBM.Graph.AnpDetNearAt
#check @RBM.Graph.AnpDetNear
#check @RBM.Graph.lwMomExp_near
#check @RBM.Graph.lwMomExp_valOnD
#check @RBM.Graph.NGraph
#check @RBM.Graph.LWXiClaim
#check @RBM.Graph.lwXiClaim_holds
#check @RBM.Graph.lwXiVar
#check @RBM.sfT
#check @RBM.PsiT
#check @RBM.Gauss.zdistInf
#check @RBM.sum_ball_min_pow_le
#check @RBM.key_T_reduce_absorbed
#check @RBM.Gauss.Sizes.LWAssmExp
#check @RBM.Gauss.Sizes.LWMomentExp
#check @RBM.Gauss.Sizes.LWf
#check @RBM.Gauss.Sizes.lwMoment_holds
#check @RBM.Gauss.Sizes.lwtermExpN_of_LWterm
#check @RBM.Gauss.Sizes.STFlow
#check @RBM.Gauss.Sizes.STflowE

-- Section 2
namespace RBM.Graph.T2359Check

def T2359_EKTTkInf (d n : ℕ) : Prop :=
  3 ≤ d → 2 ≤ n → ∃ C : ℝ, 0 < C ∧
    ∀ (L : ℕ) [NeZero L] (W g t : ℝ), 0 < W → 0 ≤ g → t < 1 → g ^ 2 ≤ (L : ℝ) ^ 2 * (1 - t) →
      ∀ ℓ Λ : ℝ, 1 ≤ ℓ → ℓ ≤ Λ * ellT L g t →
      ∀ (D : Finset (Zd d L)) (c : Zd d L), (∀ α ∈ D, (zdistInf d L (c - α) : ℝ) ≤ ℓ) → ∀ x y : Fin n → Zd d L,
        ∑ α ∈ D, ∏ i, (sfT d L W g t (min (zdistInf d L (x i - α) : ℝ) ℓ) * sfT d L W g t (min (zdistInf d L (y i - α) : ℝ) ℓ))
          ≤ C * (Λ ^ 2 * ((W ^ d)⁻¹ / (1 - t))) *
              (PsiT d L W g t ^ (n - 2) * ∏ i, sfT d L W g t (min (zdistInf d L (x i - y i) : ℝ) ℓ))

def T2359_AnpNearInfAt (d : ℕ) {p q : ℕ} (Γ : NGraph p q) : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ (L : ℕ) [NeZero L] (W g t : ℝ), 0 < W → 0 ≤ g → t < 1 → g ^ 2 ≤ (L : ℝ) ^ 2 * (1 - t) →
      ∀ ℓ Λ : ℝ, 1 ≤ ℓ → ℓ ≤ Λ * ellT L g t → ∀ ξ : Zd d L → Zd d L → ℝ, (∀ α β, 0 ≤ ξ α β ∧ ξ α β = ξ β α) →
        (∀ α β, ξ α β ≤ sfT d L W g t (min ((zdistInf d L (α - β) : ℕ) : ℝ) ℓ)) →
        ∀ (c a b : Zd d L) (D : Finset (Zd d L)), (∀ α ∈ D, ((zdistInf d L (c - α) : ℕ) : ℝ) ≤ ℓ) →
          lwMomExp_valOnD Γ ξ (fun _ => a) (fun _ => b) D ≤
            C * (Λ ^ 2 * ((W ^ d)⁻¹ / (1 - t))) ^ q * PsiT d L W g t ^ (Γ.ordN - (p : ℤ)) *
              sfT d L W g t (min ((zdistInf d L (a - b) : ℕ) : ℝ) ℓ) ^ p

def T2359_LWXiE {d : ℕ} (sz : Sizes d) (E t ℓ : ℕ → ℝ) (D : ℝ) (ξ : ∀ n, Zd d (sz.L n) → Zd d (sz.L n) → sz.SeqΩ → ℝ) : Prop :=
  (∀ n α β ω, 0 ≤ ξ n α β ω ∧ ξ n α β ω = ξ n β α ω) ∧
    sz.Prec (U := fun n => {_p : Zd d (sz.L n) × Zd d (sz.L n) // sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 < 1 - t n})
      (fun n p ω => ξ n p.1.1 p.1.2 ω)
      (fun n p _ => sfT d (sz.L n) ((sz.W n : ℕ) : ℝ) (sz.lam n) (t n)
        (min ((zdistInf d (sz.L n) (p.1.1 - p.1.2) : ℕ) : ℝ) (ℓ n)) + ((sz.W n : ℕ) : ℝ) ^ (-D)) ∧
    sz.Prec (U := fun n => Zd d (sz.L n)) (fun n α ω => ∑ β, ξ n α β ω ^ 2)
      (fun n _ _ => ((((sz.W n : ℕ) : ℝ) ^ d) * etaT (E n) (t n))⁻¹)

def T2359_LWXiExpClaim (d : ℕ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z →
    ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ lemT (z n)) → ∀ (ε₀ : ℝ) (Ψ ℓ : ℕ → ℝ), LWAssmExp sz (STflowE z) t ε₀ Ψ ℓ →
      ∀ ε₁ : ℝ, 0 < ε₁ → sz.Prec (U := fun n => Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n))
          (fun n p ω => ‖STGM sz n (STflowE z n) (t n) ω p.1 p.2‖) (fun n _ _ => ((sz.W n : ℕ) : ℝ) ^ (-ε₁)) →
        ∀ D : ℝ, 0 < D → ∀ ρ : ℕ → ℝ, (∀ n, 0 ≤ ρ n) →
          (∀ τ : ℝ, 0 < τ → ∀ᶠ n in atTop, Real.sqrt (ρ n) ≤ τ * Real.log ((sz.size n : ℕ) : ℝ)) →
          T2359_LWXiE sz (STflowE z) t ℓ D (lwXiVar sz (STflowE z) t ρ)

def T2359_regA (d : ℕ) (K : ℝ) (sz : Sizes d) (n : ℕ) (t ℓ : ℝ) (q : Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n)) : Prop :=
  ((zdistInf d (sz.L n) (STblk sz n q.1 - STblk sz n q.2) : ℕ) : ℝ) ≤
      K * Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ) * ellT (sz.L n) (sz.lam n) t ∨
    ℓ ≤ K * Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ) * ellT (sz.L n) (sz.lam n) t

/-- `AnpDetNear` (`Graph/LWMomExp.lean:911`) in `ℓ^∞`. -/
def T2359_AnpNearInf (d : ℕ) : Prop :=
  3 ≤ d → ∀ (p q : ℕ) (Γ : NGraph p q), Γ.NoGhost → Γ.IsNested → T2359_AnpNearInfAt d Γ

/-- (A) on the regime `regA d K` (the target `LWMomentExp`, `Graph/LWPins.lean:341`, with the subtype restricted by `regA`; `LWf`
as in the target: the `D`-restricted `LWfD` of R1 is not used here, R3 converts by `LWfD … univ = LWf`). -/
def T2359_LWMomExpNoExpF (d : ℕ) (K : ℝ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ (p : ℕ), 2 ∣ p → ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ),
    STFlow sz κ ε 𝔠 𝔡 z → ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ lemT (z n)) →
      ∀ (ε₀ : ℝ) (Ψ ℓ : ℕ → ℝ), LWAssmExp sz (STflowE z) t ε₀ Ψ ℓ → ∀ D : ℝ, 0 < D →
        sz.Prec (U := fun n => {q : Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n) //
            sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 < 1 - t n ∧ T2359_regA d K sz n (t n) (ℓ n) q})
          (fun n q _ => ∫ ω, ‖LWf sz n (STflowE z n) (t n) ω q.1.1 q.1.2‖ ^ p ∂(sz.seqP))
          (fun n q _ => ((etaT (STflowE z n) (t n))⁻¹ * (sz.Bctl n (t n)) ^ (1 / 2 : ℝ) *
            sfT d (sz.L n) ((sz.W n : ℕ) : ℝ) (sz.lam n) (t n)
              (min ((zdistInf d (sz.L n) (STblk sz n q.1.1 - STblk sz n q.1.2) : ℕ) : ℝ) (ℓ n))) ^ p + ((sz.W n : ℕ) : ℝ) ^ (-D))

/-- the tail, free constant `c` (C4 (c)); the statement of the probe's `lwTail32` (`T2348Pins.lean:467`). -/
def T2359_lwTail32 : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) {𝔠 c : ℝ}, 0 < 𝔠 → 0 < c → sz.SizeTendsto →
    (∀ᶠ n in atTop, ((sz.size n : ℕ) : ℝ) ^ 𝔠 ≤ ((sz.W n : ℕ) : ℝ)) → ∀ (a b : ℝ),
    ∀ᶠ n in atTop, Real.exp (-(c * Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ) / 2)) * ((sz.size n : ℕ) : ℝ) ^ a ≤
      ((sz.size n : ℕ) : ℝ) ^ (-b)

/-- Targets. -/
def T2359_ekTTkInf_holds : Prop := ∀ d n : ℕ, T2359_EKTTkInf d n
def T2359_lwMomExp_nearInf : Prop := ∀ d : ℕ, T2359_AnpNearInf d
def T2359_lwXiExpClaim_holds : Prop := ∀ d : ℕ, T2359_LWXiExpClaim d
def T2359_lwMomExpNoExp_holds : Prop := ∀ (d : ℕ) (K : ℝ), 0 < K → T2359_LWMomExpNoExpF d K

end RBM.Graph.T2359Check

#check @RBM.sfT_TtTt
#check @RBM.sfT_KtKt
#check @RBM.sfT_pair_cases
#check @RBM.zeroMode_le_of_ge
#check @RBM.tailW_pos
#check @RBM.Gauss.Sizes.LWPhiB_psiAll
