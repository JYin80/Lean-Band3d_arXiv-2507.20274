/-
Amend 1 check for T2502 row c (dispatcher V4, 2026-10-14 08:12 UTC; DECISIONS §319; ticket amendment
`docs/tickets/T2502-amend-1.md`; 1a-audit `docs/reports/T2502c-1a-audit.md`).
W1 sign-off **(A), per-time form**: the binding W1 texts of row c, copied from the gate probe `RBM3D/Probe/T2502Pins.lean`
(`t/T2502c` 0f0ad532: `T2502c_W1i` `:41`, `T2502c_W1ii` `:50`, `T2502c_W1fam` `:57`, `T2502c_tM` `:142`, `T2502c_MB` `:177`,
`T2502c_W1iii` `:182`, `T2502c_W1iv` `:190`) under the prefix `T2502_`; (iv) joins the family text with `CM` beside `Cs`;
new: the per-time core `T2502_ImproveCoregL` (target 16a), family row 15 `T2502_W1iiiOfLW` (target 16b only) and the shapes of
targets 16a, 16b.  Supersedes the drafts `T2502_W1SelfConsDraft`, `T2502_W1SameRowDraft` (`T2502-check.lean:330-342`).
Only names, statements and definitions; no proofs.
Run: lake env lean docs/tickets/checks/T2502-amend-1-check.lean
-/
import RBM3D.Chain.Step6KitGen
import RBM3D.Chain.CltGen
import RBM3D.Chain.Step2Gen

set_option linter.style.longLine false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Matrix

namespace RBM.BA
open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes

/-! ## Part 1: merged names read by the amended texts -/

#check @STExpAvgAtgL        -- Chain/Step6Gen:153
#check @STImproveExpAvergL  -- Chain/Step6Gen:316
#check @st6_expAvgU_of_ping -- Chain/Step6KitGen:338 (target 16c copies its shape)
#check @STExpAvgUgL
#check @LWAvgLawgL          -- Chain/LWGen:48
#check @STLKgL              -- Chain/Carrier:80
#check @PrecL               -- Chain/Carrier:51
#check @CltRepg             -- Chain/CltGen
#check @Step2Kern_Mss       -- Chain/Step2Gen:181
#check @Step2Gen_uKer       -- Chain/Step2Gen:192
#check @SB                  -- Defs/Block:44
#check @splitEquiv          -- Defs/Sizes:87
#check @Iblk                -- Defs/Sizes:92

/-! ## Part 2: the W1 texts (binding) -/

section Texts
variable {d : ℕ} {sz : Sizes d}

/-- **W1 (i)′** (probe `T2502c_W1i`): (a) the variance kernel of the carrier is the block profile `SB d (L n) (g' n)`;
(b) `(H₀ - E - m) M = 1`; (c) the block average of `M` is `C.m n`. -/
def T2502_W1i (C : FlowFM sz) (H₀ : ∀ n, Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    (g' E : ℕ → ℝ) (n : ℕ) : Prop :=
  C.S n = SB d (sz.L n) (g' n) ∧
  (H₀ n - ((E n : ℂ) + C.m n) • (1 : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)) *
      Matrix.of (fun x y => C.M n x y) = 1 ∧
  ∀ a : Zd d (sz.L n), (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * ∑ x ∈ Iblk d (sz.L n) (sz.W n) a, C.M n x x = C.m n

/-- **W1 (ii)′** (probe `T2502c_W1ii`): the same-charge row bound of the carrier kernel, eventual in `n`. -/
def T2502_W1ii (C : FlowFM sz) (Cs : ℝ) : Prop :=
  ∀ᶠ n in atTop, ∀ (σ : Bool) (s t : ℝ), 0 ≤ s → s ≤ t → t < 1 → ∀ a : Zd d (sz.L n),
    ∑ b : Zd d (sz.L n), ‖Step2Gen_uKer C n σ σ s t a b‖ ≤ Cs

/-- The `M`-weighted block trace `t_{aq} = tr(E_a M P_q G_u)` (probe `T2502c_tM`). -/
def T2502_tM (C : FlowFM sz) (n : ℕ) (u : ℝ) (ω : sz.SeqΩ) (a q : Zd d (sz.L n)) : ℂ :=
  (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * ∑ x ∈ Iblk d (sz.L n) (sz.W n) a, ∑ y ∈ Iblk d (sz.L n) (sz.W n) q, C.M n x y * C.G n u ω y x

/-- The block entry `M^{(B)}_{aq} = M_{(a,0),(q,0)}` (probe `T2502c_MB`). -/
def T2502_MB (C : FlowFM sz) (n : ℕ) (a q : Zd d (sz.L n)) : ℂ :=
  C.M n ((splitEquiv d (sz.L n) (sz.W n)).symm (a, 0)) ((splitEquiv d (sz.L n) (sz.W n)).symm (q, 0))

/-- **W1 (iii)**, per time (probe `T2502c_W1iii`): `|t_{aq} - M^{(++)}_{aq}| ≺ |M^{(B)}_{aq}| W^{-d}B_{τ,0}`.
Band: `δ_{aq} m (ḡ_a - m)` (probe `T2502c_band_collapse` `:153`) and `LWAvgLawgL`; BA: `TwistPins_circ_term`
(`BA/TwistPins:439`) and TL1 `BATwistAvgLaw` (`BA/TwistPins:91`; owed: TL stage + BA-V), owner of the bridge V1-BA. -/
def T2502_W1iii (C : FlowFM sz) (μ : Measure sz.SeqΩ) (τ : ℕ → ℝ) : Prop :=
  PrecL sz μ (U := fun n => Zd d (sz.L n) × Zd d (sz.L n))
    (fun n p ω => ‖T2502_tM C n (τ n) ω p.1 p.2 - Step2Kern_Mss C n true true p.1 p.2‖)
    (fun n p _ => ‖T2502_MB C n p.1 p.2‖ * sz.Bctl n (τ n))

/-- **W1 (iv)** (probe `T2502c_W1iv`): `ℓ¹` row bound of `M^{(B)}`, eventual.  Band `CM = 1`; BA: `CltFlowBA_MB_decay`
(`BA/CltFlowBA:221`, private; constants at `(κ, 𝔡)`) summed, made public by V1-BA. -/
def T2502_W1iv (C : FlowFM sz) (CM : ℝ) : Prop :=
  ∀ᶠ n in atTop, ∀ a : Zd d (sz.L n), ∑ q, ‖T2502_MB C n a q‖ ≤ CM

end Texts

/-! ## Part 3: family texts, the per-time core and the target shapes (binding) -/

/-- **Family rows 9 + 14 merged, with (iv)** (probe `T2502c_W1fam` plus `CM`): `Cs`, `CM` after `(κ, ε, 𝔡)`, before
`(𝔠, sz, z)`; one witness `(H₀, g', E)` per flow.  Band: probe `T2502c_band_W1fam` (`:121`) and `CM = 1`; BA: probe
`T2502c_ba_W1fam` (`:249`) and W1 (iv) from `CltFlowBA_MB_decay`, owner V1-BA. -/
def T2502_W1fam (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ)
    (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop)
    (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∃ Cs CM : ℝ, 0 < Cs ∧ 0 < CM ∧
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), Flow sz κ ε 𝔠 𝔡 z →
      ∃ (H₀ : ∀ n, Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (g' E : ℕ → ℝ),
        CltRepg (mk sz z) (law sz) H₀ g' E ∧ (∀ n, T2502_W1i (mk sz z) H₀ g' E n) ∧
          T2502_W1ii (mk sz z) Cs ∧ T2502_W1iv (mk sz z) CM

/-- **Target 16a, the per-time core**: `lem:improve_exp_aver` at a matrix carrier; the Stein remainder is controlled by
W1 (iii) at the same time `u` (band `STImproveExpAvergL` plus the premise `T2502_W1iii`). -/
def T2502_ImproveCoregL (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ)
    (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop)
    (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz) (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), Flow sz κ ε 𝔠 𝔡 z →
      ∀ u : ℕ → ℝ, (∀ n, 0 ≤ u n) → (∀ n, u n ≤ T0 sz z n) →
        LWAvgLawgL (mk sz z) (law sz) u → STLKgL (mk sz z) (law sz) u → T2502_W1iii (mk sz z) (law sz) u →
          STExpAvgAtgL (mk sz z) (law sz) u

/-- **Family row 15** (target 16b only): W1 (iii) follows from `LWAvgLawgL` at the same time.  Band: probe
`T2502c_band_collapse` (`:153`); BA: not read (BA goes through 16a, V1-BA). -/
def T2502_W1iiiOfLW (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ)
    (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop)
    (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz) (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) : Prop :=
  ∀ (κ ε 𝔠 𝔡 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z →
    ∀ u : ℕ → ℝ, (∀ n, 0 ≤ u n) → (∀ n, u n ≤ T0 sz z n) →
      LWAvgLawgL (mk sz z) (law sz) u → T2502_W1iii (mk sz z) (law sz) u

/-- Shape of target 16a (`stImproveCoregL_of`; family rows 9 + 14 with (iv)). -/
def T2502_Target16a (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ)
    (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop)
    (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz) (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) : Prop :=
  T2502_W1fam d law Flow mk → T2502_ImproveCoregL d law Flow mk T0

/-- Shape of target 16b (`stImproveExpAvergL_of`, the merged row-a pin under rows 9 + 14 and row 15). -/
def T2502_Target16b (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ)
    (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop)
    (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz) (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) : Prop :=
  T2502_W1fam d law Flow mk → T2502_W1iiiOfLW d law Flow mk T0 → STImproveExpAvergL d law Flow mk T0

end RBM.BA
