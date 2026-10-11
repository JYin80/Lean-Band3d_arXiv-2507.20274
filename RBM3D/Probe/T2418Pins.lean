/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.BA.LWPinsBA
import RBM3D.Graph.BAExpandW

/-!
# T2418 probe (Amend 1 repair item (i), CONTROL H219): the pin S1 of `lem:LWterm_EXP` at BA (never merged)

Paper `paper/tex/B_graphical_lemmas.tex:11-14` (`(eq:ELW_term)`), `GGGamma` `:393-405` (D402 coefficient `W - 1 = M⁺S⁺`),
`lanlw` `:359-372`; design `docs/reports/T2398-design.md` §1 (term table), §2 (S1 = the crude families); consumer `BALWCutExpTw`
(`t/T2398:RBM3D/Probe/T2398Pins.lean:434-440`).  Definitions, instances and `#check`s only; no proof of S1.

The sum behind the cut `LWcutg C n t σc σo ac ao` at the carrier `baFMz` (`C.S = 1`, `M_{vv} = m`) is
`Λ = W^{-2d} Σ_{x∈[ao],y∈[ac],α} X_{[α]} G(σc)_{xα} G(σc)_{αy} G(σo)_{yx}` (`B:11-14` with `a = ao`, `b = ac`).
After `G = Ǧ + M` and one `GGGamma` (resp. `lanlw`) step at `α`, the families of S1 are the terms with two weights, no loop and no
derivative: `MM`, `T1`, `T3A^{(0)}`, `T3A^{(1)}` and the two `lanlw` children `C1`, `C2` of `M_{xα}Ǧ_{αy}`, `Ǧ_{xα}M_{αy}`.
Not here: `T2a`, `T2b`, `T3B`, `T3C` (S2, S3), the `∂Ḡ_{xy}` children of `lanlw` on `MǦ`, `ǦM` (L4b2) and the `∂tr` children (S3).
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.setOption false

open MeasureTheory Filter

noncomputable section

namespace RBM.BA
open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes RBM.Graph

section S1Fam
variable {d : ℕ} (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ) (t : ℝ) (ω : sz.SeqΩ)

/-- `X_c = tr(Ǧ E_c) = W^{-d} Σ_{v ∈ [c]} Ǧ_{vv}` (`= 𝓛^{(1)}_{+,c} - m`).  With `S_{γδ} = t W^{-d} 1([γ] = [δ])` (`BAlwS`,
`Graph/BAExpand.lean:75`): `Σ_δ S_{γδ} Ǧ_{δδ} = t X_{[γ]}`. -/
def BAExp14a_X (c : Zd d (sz.L n)) : ℂ :=
  (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * ∑ v ∈ Iblk d (sz.L n) (sz.W n) c, (baFMz sz z).GM n t ω v v

/-- `W^{(0)} = 1`, `W^{(1)} = W - 1`, `W = 1 + M⁺S⁺ = (1 - M⁺S)⁻¹` (`BAlwW`, `Graph/BAExpand.lean`) at the flow data of `baFMz sz z`. -/
def BAExp14a_Wk (k : Bool) : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ :=
  if k then BAlwW d (sz.L n) (sz.W n) (BAflowLam0 sz z n) (BAflowEs sz z n) t ((baFMz sz z).m n) - 1 else 1

/-- The closing edge `G(σ)_{yx}`: `G_{yx}` for `σ = true`, `\overline{G_{xy}}` for `σ = false` (the entry of `G^*`). -/
def BAExp14a_tail (σ : Bool) (x y : Idx d (sz.L n) (sz.W n)) : ℂ :=
  if σ then (baFMz sz z).G n t ω y x else star ((baFMz sz z).G n t ω x y)

/-- `W^{-2d} Σ_{x ∈ [a], y ∈ [b]} G(σ)_{yx} Σ_α X_{[α]} T(x, y, α)`: the frame of the families (`x ∈ [a]`, `y ∈ [b]`, `α` in the whole
fine lattice; `S^{(B)} = 1` so `a₁ = a₂ = [α]`, `B:11-14`). -/
def BAExp14a_outer (σ : Bool) (a b : Zd d (sz.L n))
    (T : Idx d (sz.L n) (sz.W n) → Idx d (sz.L n) (sz.W n) → Idx d (sz.L n) (sz.W n) → ℂ) : ℂ :=
  ((((sz.W n : ℕ) : ℂ) ^ d)⁻¹) ^ 2 * ∑ x ∈ Iblk d (sz.L n) (sz.W n) a, ∑ y ∈ Iblk d (sz.L n) (sz.W n) b,
    BAExp14a_tail sz z n t ω σ x y * ∑ α, BAExp14a_X sz z n t ω (STblk sz n α) * T x y α

/-- `F_MM`: `M_{xα} M_{αy}` (the two-`M` term of `G_{xα}G_{αy}`). -/
def BAExp14a_FMM (σ : Bool) (a b : Zd d (sz.L n)) : ℂ :=
  BAExp14a_outer sz z n t ω σ a b fun x y α => (baFMz sz z).M n x α * (baFMz sz z).M n α y

/-- `F_T1`: `Σ_β (W - 1)_{αβ} M_{xβ} M_{βy}` (the first sum of `GGGamma`, D402). -/
def BAExp14a_FT1 (σ : Bool) (a b : Zd d (sz.L n)) : ℂ :=
  BAExp14a_outer sz z n t ω σ a b fun x y α =>
    ∑ β, BAExp14a_Wk sz z n t true α β * (baFMz sz z).M n x β * (baFMz sz z).M n β y

/-- `F_T3A^{(k)}`: `Σ_{w,γ} W^{(k)}_{αw} M_{wγ} · t X_{[γ]} · G_{γy} Ǧ_{xw}` (the `Ǧ_{δδ} G_{γy} Ǧ_{xw}` term of `GGGamma`, `δ`-sum done). -/
def BAExp14a_FT3A (k : Bool) (σ : Bool) (a b : Zd d (sz.L n)) : ℂ :=
  BAExp14a_outer sz z n t ω σ a b fun x y α =>
    ∑ w, ∑ γ, BAExp14a_Wk sz z n t k α w * (baFMz sz z).M n w γ * ((t : ℂ) * BAExp14a_X sz z n t ω (STblk sz n γ)) *
      (baFMz sz z).G n t ω γ y * (baFMz sz z).GM n t ω x w

/-- `F_C1`: the `Ǧ_{ββ} G_{α'y}` child of `lanlw` on `M_{xα} Ǧ_{αy}`: `Σ_{α'} M_{xα} · t X_{[α']} M_{αα'} G_{α'y}`. -/
def BAExp14a_FC1 (σ : Bool) (a b : Zd d (sz.L n)) : ℂ :=
  BAExp14a_outer sz z n t ω σ a b fun x y α =>
    ∑ α', (baFMz sz z).M n x α * ((t : ℂ) * BAExp14a_X sz z n t ω (STblk sz n α')) * (baFMz sz z).M n α α' *
      (baFMz sz z).G n t ω α' y

/-- `F_C2`: the `Ǧ_{ββ} G_{α'α}` child of `lanlw` on `Ǧ_{xα} M_{αy}`: `Σ_{α'} t X_{[α']} M_{xα'} G_{α'α} M_{αy}`. -/
def BAExp14a_FC2 (σ : Bool) (a b : Zd d (sz.L n)) : ℂ :=
  BAExp14a_outer sz z n t ω σ a b fun x y α =>
    ∑ α', ((t : ℂ) * BAExp14a_X sz z n t ω (STblk sz n α')) * (baFMz sz z).M n x α' * (baFMz sz z).G n t ω α' α *
      (baFMz sz z).M n α y

/-- The six families of S1 at the loop charge `+`, in the order `F_MM, F_T1, F_T3A^{(0)}, F_T3A^{(1)}, F_C1, F_C2`; `x ∈ [a]`, `y ∈ [b]`,
closing edge `G(σ)_{yx}`. -/
def BAExp14a_F (k : Fin 6) (σ : Bool) (a b : Zd d (sz.L n)) : ℂ :=
  ![BAExp14a_FMM sz z n t ω σ a b, BAExp14a_FT1 sz z n t ω σ a b, BAExp14a_FT3A sz z n t ω false σ a b,
    BAExp14a_FT3A sz z n t ω true σ a b, BAExp14a_FC1 sz z n t ω σ a b, BAExp14a_FC2 sz z n t ω σ a b] k

/-- **The integrand of S1** at the labelling of `LWcutg` (`Chain/LWGen.lean:39`): `k` the family, `σc` the charge of the loop `X` and of the two
path edges, `σo` the charge of the closing edge, `ac`, `ao` the blocks of the cut.  For `σc = true` the sum behind `LWcutg C n t true σo ac ao`
is `Σ_k F_k` over `x ∈ [ao]`, `y ∈ [ac]` (and the terms of S2, S3).  For `σc = false` the cut is the complex conjugate of the cut
`(true, !σo, ao, ac)` (cyclicity of the trace, `S = 1`: the intended reading, to be proved by the assembly), so the red families are the
conjugates of the blue ones at the swapped blocks and the same tail charge flipped. -/
def BAExp14aS1Fam (k : Fin 6) (σc σo : Bool) (ac ao : Zd d (sz.L n)) : ℂ :=
  if σc then BAExp14a_F sz z n t ω k σo ao ac else star (BAExp14a_F sz z n t ω k (!σo) ac ao)

end S1Fam

/-- **S1** (the crude families of `lem:LWterm_EXP` at BA; owner T2418, row L4a): for the six families `F_MM, F_T1, F_T3A^{(0)}, F_T3A^{(1)},
F_C1, F_C2` (`BAExp14aS1Fam`), every charge pair `(σc, σo)` and every block pair `(ac, ao)`,
`‖𝔼 F‖ ≺ (1 - t)⁻¹ (W^{-d} B_{t,0})^{5/2}` on `U_n = {λ²/L^d ≤ 1 - t}`, over the carrier `baFMz sz z` and the law `seqP (sz.withLam 0)`,
from the two premises `STLocalEntrygL` and `LWAvgLawgL` only (no premise on `𝔼 tr`; `STLmaxgL`, `STLKgL`, `STDecaygL`, `BATwistAvgLaw`,
`BATwistLoopLaw` of `BALWCutExpTw` are not used).  The binders, the range of `t`, `U` and the bound are those of `BALWCutExpTw`.
It does **not** cover the `∂Ḡ_{xy}` children of `lanlw` on `MǦ`, `ǦM` (L4b2) nor the `∂tr` children (S3). -/
def BAExp14aS1 (d : ℕ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z →
    ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ BAflowT0 sz z n) → let μ := Sizes.seqP (sz.withLam 0)
      STLocalEntrygL (baFMz sz z) μ t → LWAvgLawgL (baFMz sz z) μ t →
      PrecL sz μ (U := fun n => {_p : Fin 6 × (Bool × Bool) × (Zd d (sz.L n) × Zd d (sz.L n)) // sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ d ≤ 1 - t n})
        (fun n p _ => ‖∫ ω, BAExp14aS1Fam sz z n (t n) ω p.1.1 p.1.2.1.1 p.1.2.1.2 p.1.2.2.1 p.1.2.2.2 ∂μ‖) (fun n _ _ => (1 - t n)⁻¹ * (sz.Bctl n (t n)) ^ (5 / 2 : ℝ))

/-! ## Compiled checks -/

#check @BAExp14a_F
#check @BAExp14aS1Fam
#check @BAExp14aS1
#print axioms BAExp14aS1Fam
#print axioms BAExp14aS1

section Checks
variable {d : ℕ} (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ) (t : ℝ) (ω : sz.SeqΩ) (σ : Bool) (a b : Zd d (sz.L n))

/-- The tags `0, …, 5` of `BAExp14a_F` are `F_MM, F_T1, F_T3A^{(0)}, F_T3A^{(1)}, F_C1, F_C2`. -/
example : (BAExp14a_F sz z n t ω 0 σ a b, BAExp14a_F sz z n t ω 1 σ a b, BAExp14a_F sz z n t ω 2 σ a b, BAExp14a_F sz z n t ω 3 σ a b,
    BAExp14a_F sz z n t ω 4 σ a b, BAExp14a_F sz z n t ω 5 σ a b) =
    (BAExp14a_FMM sz z n t ω σ a b, BAExp14a_FT1 sz z n t ω σ a b, BAExp14a_FT3A sz z n t ω false σ a b,
      BAExp14a_FT3A sz z n t ω true σ a b, BAExp14a_FC1 sz z n t ω σ a b, BAExp14a_FC2 sz z n t ω σ a b) := rfl

/-- The matrix `M` inside `W` (`BAlwM` of `BAlwW`) is the `M` of the carrier that the families use. -/
example : BAlwM d (sz.L n) (sz.W n) (BAflowLam0 sz z n) (BAflowEs sz z n) ((baFMz sz z).m n) = Matrix.of ((baFMz sz z).M n) := rfl
end Checks

section Inst
open RBM.BA.FlowPinsInst RBM.Gauss.SizesInst

local notation "μ0" => Sizes.seqP (sz0.withLam 0)

/-- Nonempty instance of S1 at `d = 3`, `sz0` (`n = 0`: `L = 4`, `W = 32`, `λ = 1/64`), `flow_sz0` (`κ = 1/2`, `ε = 𝔡 = 1/10`, `𝔠 = 1/6`),
`t ≡ 1/2 ≤ BAflowT0`: every deterministic hypothesis is discharged; the Step 1/2 bounds `STLocalEntrygL`, `LWAvgLawgL` (other gates' pins)
stay hypotheses. -/
example (h : BAExp14aS1 3) (hE : STLocalEntrygL (baFMz sz0 zSeq) μ0 (fun _ => 1 / 2))
    (hA : LWAvgLawgL (baFMz sz0 zSeq) μ0 (fun _ => 1 / 2)) :=
  h le_rfl (1 / 2) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 6) sz0 zSeq flow_sz0 (fun _ => 1 / 2)
    (fun _ => by norm_num) (fun n => (half_lt_t0 n).le) hE hA

/-- The index set `U_n` of S1 is nonempty for every `n` at these data: `λ_n² / L_n³ ≤ 1 - 1/2`. -/
example (n : ℕ) : sz0.lam n ^ 2 / ((sz0.L n : ℕ) : ℝ) ^ 3 ≤ 1 - (1 / 2 : ℝ) := by
  have h1 : sz0.lam n ≤ 1 := by
    change ((2 * ((n : ℝ) + 1)) ^ 6)⁻¹ ≤ 1
    exact inv_le_one_of_one_le₀ (one_le_pow₀ (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]))
  have h2 : (4 : ℝ) ≤ ((sz0.L n : ℕ) : ℝ) := by
    change (4 : ℝ) ≤ (((4 * (n + 1) : ℕ)) : ℝ)
    push_cast
    nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have h3 : (64 : ℝ) ≤ ((sz0.L n : ℕ) : ℝ) ^ 3 := by
    have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 4) h2 3
    norm_num at this ⊢
    linarith
  rw [div_le_iff₀ (by positivity)]
  nlinarith [mul_le_mul h1 h1 (sz0_lam_pos n).le zero_le_one]

end Inst

end RBM.BA

end
