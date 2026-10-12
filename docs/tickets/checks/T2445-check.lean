/-
Release check for T2445 (dispatcher V3, Mon Oct 12 09:34 UTC 2026; DECISIONS §257).  BA-L L4d2a `BA/TwistFold2`: the model-free two-insertion
fold (A′) (`twLoop2X`, `twFold2`, `twFold2_bound`, `twVec`), the BA facts of `M` it uses, S3A-C2, S3A-C3, and one `≺` row
for an abstract weight `ρ` (supervisor 0851 Q2, S3A-C1–C4; Fable `docs/claude-team/fable/2026-10-12-s3-fold-A.md` §2.2, §4, §5).
Section 1: merged names only.  Section 2: the targets as Prop pins; targets 1–3, 7, 7′ over the object `L2X` (the 1b's
`twLoop2X`, entered as `fun d sz => @twLoop2X d sz`), and Prop-valued shapes.  No proofs, no sorry.
Run: lake env lean docs/tickets/checks/T2445-check.lean
-/
import RBM3D.BA.TwistPins
import RBM3D.Graph.BAExp14aB
import RBM3D.BA.GreenStab
import RBM3D.BA.GreenCond2
import RBM3D.BA.FlowPins

-- Section 1: merged names
-- the twisted vocabulary and the model-free lemmas of TL0 (`BA/TwistPins.lean`, T2421; index convention 0652 C3)
#check @RBM.BA.twBlk
#check @RBM.BA.twShift
#check @RBM.BA.twChg
#check @RBM.BA.twTrP
#check @RBM.BA.twLoopX
#check @RBM.BA.twTr_eq
#check @RBM.BA.twSq
#check @RBM.BA.twFold
#check @RBM.BA.twFold_holds
#check @RBM.BA.twWard
#check @RBM.BA.twWard_holds
#check @RBM.BA.twCirc
#check @RBM.BA.twCirc_holds
#check @RBM.BA.twK_bound
#check @RBM.BA.twK_bound_holds
#check @RBM.BA.twMB
#check @RBM.BA.twMB_ba
-- the carrier, `≺` and the stochastic premises (`Chain/Carrier.lean:47-125`; registered owed, `Test/Axioms.lean:133, 144`)
#check @RBM.BA.PrecL
#check @RBM.BA.FlowFM.GM
#check @RBM.BA.FlowFM.eta
#check @RBM.BA.STLocalEntrygL
#check @RBM.BA.STLmaxgL
#check @RBM.BA.STLKgL
#check @RBM.BA.STDecaygL
#check @RBM.BA.LWAvgLawgL
-- the BA flow, its carrier, `M`, the loops (`BA/FlowPins.lean`, `Loop/GLoopFlow.lean`)
#check @RBM.BA.BAFlow
#check @RBM.BA.BAflowT0
#check @RBM.BA.baFM
#check @RBM.BA.baFMz
#check @RBM.BA.BAMfine
#check @RBM.BA.BAmF
#check @RBM.BA.BALloop
#check @RBM.Gauss.loopFine
#check @RBM.Gauss.etaOf
-- `BAMfine_eq`, the `M`-Ward identity, symmetry, the ℓ¹ rows (`BA/GreenSchur`, `BA/Ward`, `BA/GreenStab`, `Graph/BAExpandW`)
#check @RBM.BA.BAMfine_eq
#check @RBM.BA.BAMfine_norm_le_one
#check @RBM.BA.BAMB_row_sq_real
#check @RBM.BA.BAMB_symm
#check @RBM.BA.BAMB_row_l1
#check @RBM.BA.BAMfine_row_l1
#check @RBM.BA.baM_row_l1
#check @RBM.BA.baM_col_l1
#check @RBM.BA.baM_rho2
#check @RBM.Graph.BAlwM
#check @RBM.Graph.baM_row_sq
#check @RBM.BA.BASelf
#check @RBM.BA.BAReal
-- S3A-C2, S3A-C3 inputs (`Defs/Sizes.lean:163-178, 211-215`, `Defs/Params.lean:36`, `BA/GreenSchur.lean:59, 72`, `BA/GreenCond2.lean:321-350`)
#check @RBM.Gauss.Sizes.WO
#check @RBM.Gauss.Sizes.Admissible
#check @RBM.Gauss.Sizes.Bctl
#check @RBM.Bparam
#check @RBM.Gauss.Sizes.STWB
#check @RBM.BA.BAflow_real
#check @RBM.BA.BAflow_lam0_window
#check @RBM.BA.GreenCond2_eta_lower
-- the resolvent at the carrier: Ward identities, `η > 0`, `‖G‖ ≤ η⁻¹`, `𝓛^{(1)}`, the profile, the tail, `≺ → 𝔼`, S1's frame
#check @RBM.BA.ba_G_data
#check @RBM.BA.BAGt_eq_green
#check @RBM.green_sub_green_conj'
#check @RBM.BA.BAExp14a_G_green
#check @RBM.BA.BAExp14a_eta_eq
#check @RBM.BA.BAExp14a_G_ward
#check @RBM.BA.BAExp14a_eta_pos
#check @RBM.BA.BAExp14a_G_le
#check @RBM.BA.BAExp14a_L1_eq
#check @RBM.BA.BAExp14a_STWB_le
#check @RBM.BA.BAExp14a_tailG
#check @RBM.BA.BAExp14a_prec_integral
#check @RBM.BA.BAExp14a_prec_int
#check @RBM.BA.BAExp14aS1
-- the `d = 3` instance data (`Defs/Sizes.lean` §Inst, `BA/FlowPins.lean` §Inst)
#check @RBM.Gauss.SizesInst.sz0
#check @RBM.BA.FlowPinsInst.zSeq
#check @RBM.BA.FlowPinsInst.flow_sz0
#check @RBM.BA.FlowPinsInst.half_lt_t0

-- Section 2: the targets (Prop pins) and shapes
noncomputable section

namespace RBM.BA.T2445Check

open MeasureTheory Filter
open RBM RBM.Loop RBM.Gauss RBM.Gauss.Sizes RBM.Graph RBM.BA

/-- Target 4 (`twVec`, Fable §5; the vector twin of `twWard`), any finite index type: if `G - G^* = 2iη G^*G`, `η ≠ 0`, then
`‖(G - M)φ‖² ≤ 2η⁻¹ Im⟨φ, Gφ⟩ + 2‖Mφ‖²` (`‖Gφ‖² = η⁻¹ Im⟨φ, Gφ⟩`).  The `G^*G` form is the one `‖Gφ‖²` needs. -/
def T2445_twVec : Prop :=
  ∀ {ι : Type} [Fintype ι] (G M : Matrix ι ι ℂ) (η : ℝ), η ≠ 0 →
    G - G.conjTranspose = (2 * (η : ℂ) * Complex.I) • (G.conjTranspose * G) →
    ∀ φ : ι → ℂ, ∑ u, ‖∑ v, (G u v - M u v) * φ v‖ ^ 2 ≤
      2 * η⁻¹ * (∑ u, star (φ u) * ∑ v, G u v * φ v).im + 2 * ∑ u, ‖∑ v, M u v * φ v‖ ^ 2

/-- Target 5a (`‖M^* e_x‖² ≤ 1`; `BAMfine_eq` and the `M`-Ward identity; an upper bound only, 0851 `:45`). -/
def T2445_twMrow_le : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ), BASelf d (sz.L n) (lam0 n) (E n : ℂ) (BAmF sz lam0 E n) →
    ∀ x : Idx d (sz.L n) (sz.W n), ∑ v, ‖BAMfine sz lam0 E n x v‖ ^ 2 ≤ 1

/-- Target 5b (`Π_b M^* M Π_b ≤ Π_b`, vector form, an upper bound only): `‖Mφ‖² ≤ ‖φ‖²` for `φ` supported in `[b]`. -/
def T2445_twMblk_le : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ), BASelf d (sz.L n) (lam0 n) (E n : ℂ) (BAmF sz lam0 E n) →
    ∀ (b : Zd d (sz.L n)) (φ : Idx d (sz.L n) (sz.W n) → ℂ), (∀ v, v ∉ twBlk n b → φ v = 0) →
      ∑ u, ‖∑ v, BAMfine sz lam0 E n u v * φ v‖ ^ 2 ≤ ∑ v, ‖φ v‖ ^ 2

/-- Target 6a (S3A-C2, `B_0 ≥ c` in the Lean frame): `(eq:WO)` gives eventually `W^d · W^{-d} B_{t,0} ≥ (𝔡^{-2} + 1)^{-1}` for
`0 ≤ t ≤ 1` (`Bctl` contains `W^{-d} (lam² + |1 - t|)⁻¹`; `BAFlow → Admissible → WO` is `h.1.2.2.2.2`). -/
def T2445_twB0_ge : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (𝔡 : ℝ), sz.WO 𝔡 → ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ 1) →
    ∀ᶠ n in atTop, (𝔡⁻¹ ^ 2 + 1)⁻¹ ≤ ((sz.W n : ℕ) : ℝ) ^ d * sz.Bctl n (t n)

/-- Target 6b (S3A-C3): `η_t = (1 - t) Im m ≥ κ (1 - t)` at the carrier (`etaOf`, `BAflow_real`; `GreenCond2.lean:321-345`). -/
def T2445_twEta_ge : Prop :=
  ∀ {d : ℕ} (κ ε 𝔠 𝔡 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z →
    ∀ (n : ℕ) (t : ℝ), t ≤ 1 → κ * (1 - t) ≤ (baFMz sz z).eta n t

section Fold

-- The object of target 1: the 1b's `twLoop2X` (implicit `d`, `sz`, as `twLoopX`) enters as `fun d sz => @twLoop2X d sz`.
variable (L2X : ∀ (d : ℕ) (sz : Sizes d) (n : ℕ), (Idx d (sz.L n) (sz.W n) → Idx d (sz.L n) (sz.W n) → ℂ) →
  (Idx d (sz.L n) (sz.W n) → Idx d (sz.L n) (sz.W n) → ℂ) → (Idx d (sz.L n) (sz.W n) → Idx d (sz.L n) (sz.W n) → ℂ) →
  (Zd d (sz.L n) → Zd d (sz.L n) → Zd d (sz.L n) → Zd d (sz.L n) → ℂ) → Zd d (sz.L n) → ℂ)

/-- Target 1 (`twLoop2X`, Fable §5; twin of `twLoopX`, `TwistPins.lean:66`), its body: `Σ_c ρ(c) Tr(E_a A P_{c₁c₂} X P_{c₃c₄} C)`
in the `twTrP` convention (`P_{c₁c₂} = W^{-d} Σ_o |(c₁,o)⟩⟨(c₂,o)|`; `w = (c₁,o) ∈ [c₁]`, `w' = (c₃,o') ∈ [c₃]`), i.e.
`W^{-3d} Σ_c ρ(c) Σ_{x∈[a]} Σ_{o,o'} A_{x,(c₁,o)} X_{(c₂,o),(c₃,o')} C_{(c₄,o'),x}`.  The 1b's definition satisfies it by `rfl`. -/
def T2445_twLoop2X_eq : Prop :=
  ∀ (d : ℕ) (sz : Sizes d) (n : ℕ) (A X C : Idx d (sz.L n) (sz.W n) → Idx d (sz.L n) (sz.W n) → ℂ)
    (ρ : Zd d (sz.L n) → Zd d (sz.L n) → Zd d (sz.L n) → Zd d (sz.L n) → ℂ) (a : Zd d (sz.L n)),
    L2X d sz n A X C ρ a = ∑ c₁, ∑ c₂, ∑ c₃, ∑ c₄, ρ c₁ c₂ c₃ c₄ * (((((sz.W n : ℕ) : ℂ) ^ d)⁻¹) ^ 3 *
      ∑ x ∈ twBlk n a, ∑ w ∈ twBlk n c₁, ∑ w' ∈ twBlk n c₃, A x w * X (twShift n c₂ w) w' * C (twShift n c₄ w') x)

/-- Target 1, trace form (`twLoop2X_trace`, twin of `twTr_eq`): the summand at `c` is the merged `twLoopX` of `(X P_{c₃c₄} C, A)`,
`Tr(E_a A P_{c₁c₂} X P_{c₃c₄} C) = Tr((X P_{c₃c₄} C) E_a A P_{c₁c₂})`. -/
def T2445_twLoop2X_trace : Prop :=
  ∀ (d : ℕ) (sz : Sizes d) (n : ℕ) (A X C : Idx d (sz.L n) (sz.W n) → Idx d (sz.L n) (sz.W n) → ℂ)
    (ρ : Zd d (sz.L n) → Zd d (sz.L n) → Zd d (sz.L n) → Zd d (sz.L n) → ℂ) (a : Zd d (sz.L n)),
    L2X d sz n A X C ρ a = ∑ c₁, ∑ c₂, ∑ c₃, ∑ c₄, ρ c₁ c₂ c₃ c₄ *
      twLoopX n (fun (u x : Idx d (sz.L n) (sz.W n)) =>
        (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * ∑ w' ∈ twBlk n c₃, X u w' * C (twShift n c₄ w') x) A a c₁ c₂

/-- Target 2 (`twFold2`, Fable §5; twin of `twFold`): one Cauchy–Schwarz over `(c₁, c₂, c₃, c₄, x, o, o')` with the weight `|ρ|`
(0851 Q2), split `[A_{x,(c₁,o)} X_{(c₂,o),(c₃,o')}] · [C_{(c₄,o'),x}]`; all matrices. -/
def T2445_twFold2 : Prop :=
  ∀ (d : ℕ) (sz : Sizes d) (n : ℕ) (A X C : Idx d (sz.L n) (sz.W n) → Idx d (sz.L n) (sz.W n) → ℂ)
    (ρ : Zd d (sz.L n) → Zd d (sz.L n) → Zd d (sz.L n) → Zd d (sz.L n) → ℂ) (a : Zd d (sz.L n)),
    ‖L2X d sz n A X C ρ a‖ ^ 2 ≤ ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹) ^ 6 *
      (∑ c₁, ∑ c₂, ∑ c₃, ∑ c₄, ‖ρ c₁ c₂ c₃ c₄‖ * ∑ x ∈ twBlk n a, ∑ w ∈ twBlk n c₁, ∑ w' ∈ twBlk n c₃,
        ‖A x w‖ ^ 2 * ‖X (twShift n c₂ w) w'‖ ^ 2) *
      (∑ c₁, ∑ c₂, ∑ c₃, ∑ c₄, ‖ρ c₁ c₂ c₃ c₄‖ * ∑ x ∈ twBlk n a, ∑ _w ∈ twBlk n c₁, ∑ w' ∈ twBlk n c₃,
        ‖C (twShift n c₄ w') x‖ ^ 2)

/-- Target 3 (`twFold2_bound`, Fable §4, §5): `β ≥ max_{u,c} Σ_{v∈[c]} |X_{uv}|²`, `r₁ ≥ max_{c₁} Σ_{c₂c₃c₄} |ρ|`,
`r₂ ≥ max_{c₄} Σ_{c₁c₂c₃} |ρ|` give `|twLoop2X|² ≤ W^{-5d} β r₁ r₂ (Σ_{x∈[a]} ‖A^* e_x‖²)(Σ_{x∈[a]} ‖C e_x‖²)`.  `W^{-5d}` is
`W^{-6d}` of target 2 times the `W^d` of the free `o`-sum (Fable §2.2 `F₂` step 1); Fable §5's `W^{-3d/2}` reads `W^{-5d/2}`. -/
def T2445_twFold2_bound : Prop :=
  ∀ (d : ℕ) (sz : Sizes d) (n : ℕ) (A X C : Idx d (sz.L n) (sz.W n) → Idx d (sz.L n) (sz.W n) → ℂ)
    (ρ : Zd d (sz.L n) → Zd d (sz.L n) → Zd d (sz.L n) → Zd d (sz.L n) → ℂ) (a : Zd d (sz.L n)) (β r₁ r₂ : ℝ),
    (∀ (u : Idx d (sz.L n) (sz.W n)) (c : Zd d (sz.L n)), ∑ v ∈ twBlk n c, ‖X u v‖ ^ 2 ≤ β) →
    (∀ c₁, ∑ c₂, ∑ c₃, ∑ c₄, ‖ρ c₁ c₂ c₃ c₄‖ ≤ r₁) → (∀ c₄, ∑ c₁, ∑ c₂, ∑ c₃, ‖ρ c₁ c₂ c₃ c₄‖ ≤ r₂) →
    ‖L2X d sz n A X C ρ a‖ ^ 2 ≤ ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹) ^ 5 * (β * r₁ * r₂) *
      (∑ x ∈ twBlk n a, ∑ v, ‖A x v‖ ^ 2) * (∑ x ∈ twBlk n a, ∑ v, ‖C v x‖ ^ 2)

/-- Target 7 (the `≺` row, 0851 Q2 `:125`; Fable §5 "Pin instantiation"), frame of `BAExp14aS1` without its `U`-subtype:
from `STLocalEntrygL`, `STLmaxgL`, a deterministic weight `ρ` with `r₁, r₂ ≤ Cρ` (eventually, uniformly in `(σ, a, b)`) and a
random factor `X` with `‖X‖ ≺ W^d·Bctl` (#17, #47), pathwise over `(σ, a, b)`:
`‖Σ_c ρ(c) X(c) Tr(E_a Ǧ P_{c₁c₂} Ǧ P_{c₃c₄} Ǧ E_b Ǧ(σ))‖ ≺ (1 - t)⁻¹ (W^{-d} B_{t,0})^{5/2}` (the `[a]×[b]`-averaged node, Fable §1;
`σ` the tail charge, `Ǧ(σ)` by `twChg`, the closing edge circled as `BAExp14a_tailG`). -/
def T2445_twFold2Prec (d : ℕ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z →
    ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ BAflowT0 sz z n) →
      STLocalEntrygL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) t → STLmaxgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) t →
      ∀ (Cρ : ℝ) (ρ : ∀ n, Bool × Zd d (sz.L n) × Zd d (sz.L n) → Zd d (sz.L n) → Zd d (sz.L n) → Zd d (sz.L n) →
          Zd d (sz.L n) → ℂ),
        (∀ᶠ n in atTop, ∀ p, (∀ c₁, ∑ c₂, ∑ c₃, ∑ c₄, ‖ρ n p c₁ c₂ c₃ c₄‖ ≤ Cρ) ∧
          (∀ c₄, ∑ c₁, ∑ c₂, ∑ c₃, ‖ρ n p c₁ c₂ c₃ c₄‖ ≤ Cρ)) →
      ∀ X : ∀ n, Bool × Zd d (sz.L n) × Zd d (sz.L n) → Zd d (sz.L n) → Zd d (sz.L n) → Zd d (sz.L n) → Zd d (sz.L n) →
          sz.SeqΩ → ℂ,
        PrecL sz (Sizes.seqP (sz.withLam 0))
          (U := fun n => (Bool × Zd d (sz.L n) × Zd d (sz.L n)) × Zd d (sz.L n) × Zd d (sz.L n) × Zd d (sz.L n) × Zd d (sz.L n))
          (fun n q ω => ‖X n q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2 ω‖)
          (fun n _ _ => ((sz.W n : ℕ) : ℝ) ^ d * sz.Bctl n (t n)) →
      PrecL sz (Sizes.seqP (sz.withLam 0)) (U := fun n => Bool × Zd d (sz.L n) × Zd d (sz.L n))
        (fun n p ω => ‖L2X d sz n ((baFMz sz z).GM n (t n) ω) ((baFMz sz z).GM n (t n) ω)
          (fun (u x : Idx d (sz.L n) (sz.W n)) => (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ *
            ∑ y ∈ twBlk n p.2.2, (baFMz sz z).GM n (t n) ω u y * twChg ((baFMz sz z).GM n (t n) ω) p.1 y x)
          (fun c₁ c₂ c₃ c₄ => ρ n p c₁ c₂ c₃ c₄ * X n p c₁ c₂ c₃ c₄ ω) p.2.1‖)
        (fun n _ _ => (1 - t n)⁻¹ * (sz.Bctl n (t n)) ^ (5 / 2 : ℝ))

/-- Target 7′ (`twFold2PrecDet`): the deterministic weight, `X ≡ 1` (the twelve nodes other than #17, #47); from 7 and 6a. -/
def T2445_twFold2PrecDet (d : ℕ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z →
    ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ BAflowT0 sz z n) →
      STLocalEntrygL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) t → STLmaxgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) t →
      ∀ (Cρ : ℝ) (ρ : ∀ n, Bool × Zd d (sz.L n) × Zd d (sz.L n) → Zd d (sz.L n) → Zd d (sz.L n) → Zd d (sz.L n) →
          Zd d (sz.L n) → ℂ),
        (∀ᶠ n in atTop, ∀ p, (∀ c₁, ∑ c₂, ∑ c₃, ∑ c₄, ‖ρ n p c₁ c₂ c₃ c₄‖ ≤ Cρ) ∧
          (∀ c₄, ∑ c₁, ∑ c₂, ∑ c₃, ‖ρ n p c₁ c₂ c₃ c₄‖ ≤ Cρ)) →
      PrecL sz (Sizes.seqP (sz.withLam 0)) (U := fun n => Bool × Zd d (sz.L n) × Zd d (sz.L n))
        (fun n p ω => ‖L2X d sz n ((baFMz sz z).GM n (t n) ω) ((baFMz sz z).GM n (t n) ω)
          (fun (u x : Idx d (sz.L n) (sz.W n)) => (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ *
            ∑ y ∈ twBlk n p.2.2, (baFMz sz z).GM n (t n) ω u y * twChg ((baFMz sz z).GM n (t n) ω) p.1 y x)
          (ρ n p) p.2.1‖)
        (fun n _ _ => (1 - t n)⁻¹ * (sz.Bctl n (t n)) ^ (5 / 2 : ℝ))

/-- Target 7 beside S1's statement (same frame and right-hand side; elaboration check only). -/
example : Prop := BAExp14aS1 3 ∧ T2445_twFold2Prec L2X 3 ∧ T2445_twFold2PrecDet L2X 3

section Inst
open RBM.BA.FlowPinsInst RBM.Gauss.SizesInst

/-- Target 8, the shape of the instance of 7′ at the `d = 3` data (`sz0`, `zSeq`, `flow_sz0`, `t ≡ 1/2`) for the root-#2 weight
`ρ₀ = t² 1[c₃ = c₁ ∧ c₄ = c₂] (M^{(B)}_{c₁c₂})²` (Fable §1, §5; `twMB`), the two stochastic premises kept as hypotheses. -/
example : Prop :=
  STLocalEntrygL (baFMz sz0 zSeq) (Sizes.seqP (sz0.withLam 0)) (fun _ => 1 / 2) →
  STLmaxgL (baFMz sz0 zSeq) (Sizes.seqP (sz0.withLam 0)) (fun _ => 1 / 2) →
  PrecL sz0 (Sizes.seqP (sz0.withLam 0)) (U := fun n => Bool × Zd 3 (sz0.L n) × Zd 3 (sz0.L n))
    (fun n p ω => ‖L2X 3 sz0 n ((baFMz sz0 zSeq).GM n (1 / 2) ω) ((baFMz sz0 zSeq).GM n (1 / 2) ω)
      (fun (u x : Idx 3 (sz0.L n) (sz0.W n)) => (((sz0.W n : ℕ) : ℂ) ^ 3)⁻¹ *
        ∑ y ∈ twBlk n p.2.2, (baFMz sz0 zSeq).GM n (1 / 2) ω u y * twChg ((baFMz sz0 zSeq).GM n (1 / 2) ω) p.1 y x)
      (fun c₁ c₂ c₃ c₄ => if c₃ = c₁ ∧ c₄ = c₂ then (1 / 2 : ℂ) ^ 2 * twMB (baFMz sz0 zSeq) n c₁ c₂ ^ 2 else 0) p.2.1‖)
    (fun n _ _ => (1 - (1 / 2 : ℝ))⁻¹ * (sz0.Bctl n (1 / 2)) ^ (5 / 2 : ℝ))

end Inst

end Fold

end RBM.BA.T2445Check

end
