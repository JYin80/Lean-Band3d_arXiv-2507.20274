/-
Release check for T2366 (dispatcher V2, Fri Oct 9 23:09 UTC 2026; DECISIONS §172).  BA-K01, generic part: uniqueness,
two-loop bound, rotation and translation of `K`-loops over a general kernel `S` and general initial data `M`,
route G in place in `Loop/Unique.lean`, `Loop/KLUnique.lean` (supervisor `docs/supervisor/2026-10-09-2051.md` A: Q1 K-a,
Q3 G1-G3).  The BA instances of design row K01 move to K03 (§172): nothing here mentions a BA object.
Part 1: the pins (copied verbatim by the ticket into namespace `RBM.Loop`; here in `RBM.Loop.T2366Check`, so that the
file also compiles on the branch, where the auditor adds `example : @RBM.Loop.X = @RBM.Loop.T2366Check.X := rfl`).
Part 2: G1 — the 18 public declarations of the two files used outside them (dump `K01-statement-dump.out`, H156),
statements unchanged.  Merged names on main.  No proofs (only `@name` and `rfl`), no sorry.
Run: lake env lean docs/tickets/checks/T2366-check.lean
-/
import RBM3D.Loop.Unique
import RBM3D.Loop.KLUnique

universe u

namespace RBM.Loop.T2366Check

/-! ## Part 1: the pins -/

/-- **`UniqS`** (verbatim: probe `t/T2360:RBM3D/Probe/T2360Pins.lean:232`): uniqueness of `K`-loops over `IsKLoopS`; the
only fact about `S` is `‖S a b‖ ≤ 1`. -/
def UniqS : Prop :=
  ∀ (d L W : ℕ) [NeZero L] (S : Matrix (Zd d L) (Zd d L) ℂ) (m : Bool → ℂ) (M : LoopIdx (Zd d L) → ℂ),
    (∀ a b, ‖S a b‖ ≤ 1) → ∀ {T : Set ℝ} {K K' : ℝ → LoopIdx (Zd d L) → ℂ},
      IsKLoopS d L W S m M T K → IsKLoopS d L W S m M T K' → ∀ {T₀ R : ℝ}, Set.Icc 0 T₀ ⊆ T → 0 ≤ R →
      (∀ t ∈ Set.Icc 0 T₀, ∀ I : LoopIdx (Zd d L), I.WF → I.length = 2 → ‖K t I‖ ≤ R ∧ ‖K' t I‖ ≤ R) →
      ∀ t ∈ Set.Icc 0 T₀, ∀ I : LoopIdx (Zd d L), I.WF → 2 ≤ I.length → K t I = K' t I

/-- **`RetireS`**: `KLretire_twoLoopBounded` over `IsKLoopS` (continuity on `[0, T₀] ⊆ [0,1)`; no fact about `S`). -/
def RetireS : Prop :=
  ∀ (d L W : ℕ) [NeZero L] (S : Matrix (Zd d L) (Zd d L) ℂ) (m : Bool → ℂ) (M : LoopIdx (Zd d L) → ℂ)
    {K : ℝ → LoopIdx (Zd d L) → ℂ}, IsKLoopS d L W S m M (Set.Ico 0 1) K →
    ∀ T₀ : ℝ, T₀ < 1 → ∃ R : ℝ, 0 ≤ R ∧ ∀ t ∈ Set.Icc (0 : ℝ) T₀,
      ∀ I : LoopIdx (Zd d L), I.WF → I.length = 2 → ‖K t I‖ ≤ R

/-- **`RotS`**: cyclic invariance of every family of `K`-loops on `[0,1)` (the form of `KLK_rotate`), for a symmetric
kernel with `‖S a b‖ ≤ 1` and rotation-invariant initial data. -/
def RotS : Prop :=
  ∀ (d L W : ℕ) [NeZero L] (S : Matrix (Zd d L) (Zd d L) ℂ) (m : Bool → ℂ) (M : LoopIdx (Zd d L) → ℂ),
    (∀ a b, S a b = S b a) → (∀ a b, ‖S a b‖ ≤ 1) →
    (∀ (s : Bool) (b : Zd d L) (σ : List Bool) (a : List (Zd d L)), σ.length = a.length →
      M ⟨s :: σ, b :: a⟩ = M ⟨σ ++ [s], a ++ [b]⟩) →
    ∀ {K : ℝ → LoopIdx (Zd d L) → ℂ}, IsKLoopS d L W S m M (Set.Ico 0 1) K →
    ∀ t ∈ Set.Ico (0 : ℝ) 1, ∀ (s : Bool) (b : Zd d L) (σ : List Bool) (a : List (Zd d L)),
      σ.length = a.length → K t ⟨s :: σ, b :: a⟩ = K t ⟨σ ++ [s], a ++ [b]⟩

/-- **`TranslS`**: translation invariance of every family of `K`-loops on `[0,1)` (the form of `KLK_translate`), for a
translation-invariant kernel with `‖S a b‖ ≤ 1` and translation-invariant initial data. -/
def TranslS : Prop :=
  ∀ (d L W : ℕ) [NeZero L] (S : Matrix (Zd d L) (Zd d L) ℂ) (m : Bool → ℂ) (M : LoopIdx (Zd d L) → ℂ),
    (∀ a b c : Zd d L, S (a + c) (b + c) = S a b) → (∀ a b, ‖S a b‖ ≤ 1) →
    (∀ (c : Zd d L) (I : LoopIdx (Zd d L)), M ⟨I.σ, I.a.map (· + c)⟩ = M I) →
    ∀ {K : ℝ → LoopIdx (Zd d L) → ℂ}, IsKLoopS d L W S m M (Set.Ico 0 1) K →
    ∀ t ∈ Set.Ico (0 : ℝ) 1, ∀ (c : Zd d L) (I : LoopIdx (Zd d L)), I.WF →
      K t ⟨I.σ, I.a.map (· + c)⟩ = K t I

/-! ## Part 2: G1, the band statements unchanged (old statement := old name) -/

example : ∀ {α : Type u} (x : LoopIdx α) (b : α) {k l : ℕ},
    1 ≤ k → k < l → l ≤ x.length → 2 ≤ (LoopIdx.cutGlueL k l b x).length :=
  @RBM.Loop.LoopIdx.two_le_length_cutGlueL

example : ∀ {α : Type u} (x : LoopIdx α) (b : α) {k l : ℕ},
    1 ≤ k → k < l → l ≤ x.length → 2 ≤ (LoopIdx.cutGlueR k l b x).length :=
  @RBM.Loop.LoopIdx.two_le_length_cutGlueR

example : ∀ {α : Type u} (x : LoopIdx α) (a b : α) {k l : ℕ},
    1 ≤ k → k < l → l ≤ x.length →
      (LoopIdx.cutGlueL k l a x).length = x.length → (LoopIdx.cutGlueR k l b x).length = 2 :=
  @RBM.Loop.LoopIdx.length_cutGlueR_eq_two

example : ∀ {α : Type u} (x : LoopIdx α) (a b : α) {k l : ℕ},
    1 ≤ k → k < l → l ≤ x.length →
      (LoopIdx.cutGlueR k l b x).length = x.length → (LoopIdx.cutGlueL k l a x).length = 2 :=
  @RBM.Loop.LoopIdx.length_cutGlueL_eq_two

example (d L n : ℕ) : LoopVec d L n = (List.Vector Bool n × List.Vector (Zd d L) n) := rfl

example (d L n : ℕ) (p : LoopVec d L n) : LoopVec.toLoop d L p = (⟨p.1.1, p.2.1⟩ : LoopIdx (Zd d L)) := rfl

example : ∀ {d L n : ℕ} (J : LoopIdx (Zd d L)),
    J.WF → J.length = n → ∃ p : LoopVec d L n, LoopVec.toLoop d L p = J :=
  @RBM.Loop.LoopVec.exists_toLoop

example : ∀ {d L : ℕ} [NeZero L] (g : ℝ), 3 ≤ L → ∀ (a b : Zd d L), ‖SB d L g a b‖ ≤ 1 :=
  @RBM.Loop.norm_SB_apply_le

example : ∀ {X X' Y Y' s : ℂ} {R D : ℝ},
    ‖s‖ ≤ 1 → ‖X - X'‖ * ‖Y‖ ≤ R * D → ‖X'‖ * ‖Y - Y'‖ ≤ R * D → ‖X * s * Y - X' * s * Y'‖ ≤ 2 * (R * D) :=
  @RBM.Loop.norm_mul_mul_sub_le

example : ∀ (d L : ℕ) [NeZero L] (W : ℕ) (g : ℝ), 3 ≤ L →
    ∀ (K K' : ℝ → LoopIdx (Zd d L) → ℂ) (T₀ R : ℝ) (n : ℕ), 0 ≤ R →
      (∀ t ∈ Set.Icc 0 T₀, ∀ (I : LoopIdx (Zd d L)),
          I.WF → I.length = n → HasDerivAt (fun (s : ℝ) => K s I) (treeEqRhs d L W g (K t) I) t) →
      (∀ t ∈ Set.Icc 0 T₀, ∀ (I : LoopIdx (Zd d L)),
          I.WF → I.length = n → HasDerivAt (fun (s : ℝ) => K' s I) (treeEqRhs d L W g (K' t) I) t) →
      (∀ t ∈ Set.Icc 0 T₀, ∀ (I : LoopIdx (Zd d L)), I.WF → I.length = 2 → ‖K t I‖ ≤ R ∧ ‖K' t I‖ ≤ R) →
      (∀ t ∈ Set.Icc 0 T₀, ∀ (I : LoopIdx (Zd d L)), I.WF → 2 ≤ I.length → I.length < n → K t I = K' t I) →
      (∀ (I : LoopIdx (Zd d L)), I.WF → I.length = n → K 0 I = K' 0 I) →
      ∀ t ∈ Set.Icc 0 T₀, ∀ (I : LoopIdx (Zd d L)), I.WF → I.length = n → K t I = K' t I :=
  @RBM.Loop.eq_on_level

example : ∀ {d L : ℕ} [NeZero L] {W : ℕ} {g : ℝ}, 3 ≤ L →
    ∀ (m : Bool → ℂ) {T : Set ℝ} {K K' : ℝ → LoopIdx (Zd d L) → ℂ},
      IsKLoop d L W g m T K → IsKLoop d L W g m T K' →
      ∀ {T₀ R : ℝ}, Set.Icc 0 T₀ ⊆ T → 0 ≤ R →
        (∀ t ∈ Set.Icc 0 T₀, ∀ (I : LoopIdx (Zd d L)), I.WF → I.length = 2 → ‖K t I‖ ≤ R ∧ ‖K' t I‖ ≤ R) →
        ∀ t ∈ Set.Icc 0 T₀, ∀ (I : LoopIdx (Zd d L)), I.WF → 2 ≤ I.length → K t I = K' t I :=
  @RBM.Loop.isKLoop_unique

example : ∀ {d L : ℕ} {I : LoopIdx (Zd d L)}, I.WF → I.length = 2 →
    ∃ (σ₁ : Bool) (σ₂ : Bool) (a₁ : Zd d L) (a₂ : Zd d L), I = { σ := [σ₁, σ₂], a := [a₁, a₂] } :=
  @RBM.Loop.exists_eq_of_length_two

example : ∀ {d L : ℕ} [NeZero L] {W : ℕ} {g : ℝ} {m : Bool → ℂ} {K : ℝ → LoopIdx (Zd d L) → ℂ},
    IsKLoop d L W g m (Set.Ico 0 1) K →
    ∀ T₀ : ℝ, T₀ < 1 → ∃ R : ℝ, 0 ≤ R ∧ ∀ t ∈ Set.Icc (0 : ℝ) T₀,
      ∀ (I : LoopIdx (Zd d L)), I.WF → I.length = 2 → ‖K t I‖ ≤ R :=
  @RBM.Loop.KLretire_twoLoopBounded

example : ∀ {d L : ℕ} [NeZero L] {W : ℕ} {g : ℝ}, 3 ≤ L → (W : ℂ) ^ d ≠ 0 →
    ∀ {m : Bool → ℂ}, (∀ (s : Bool), ‖m s‖ = 1) →
      ∀ {K : ℝ → LoopIdx (Zd d L) → ℂ}, IsKLoop d L W g m (Set.Ico 0 1) K → KTwoFormula d L W g m K :=
  @RBM.Loop.kTwoFormula_of_isKLoop

example : ∀ {L : ℕ} [NeZero L] {W : ℕ} {g : ℝ} {k : ℕ}, 3 ≤ k + 2 → 0 < g → 3 ≤ L → (W : ℂ) ^ (k + 2) ≠ 0 →
    ∀ {m : Bool → ℂ}, (∀ (s : Bool), ‖m s‖ = 1) → ∀ {σ : Bool}, 0 < (m σ).im →
      ThetaDecayShort (k + 2) g (m σ) →
      ∀ {K : ℝ → LoopIdx (Zd (k + 2) L) → ℂ}, IsKLoop (k + 2) L W g m (Set.Ico 0 1) K →
        ∃ C > (0 : ℝ), ∃ c > (0 : ℝ), ∀ (t : ℝ), 0 ≤ t → t < 1 → ∀ (a₁ a₂ : Zd (k + 2) L),
          ‖K t ⟨[σ, σ], [a₁, a₂]⟩‖
            ≤ C * ‖((W : ℂ) ^ (k + 2))⁻¹‖ * Real.exp (-(c * (zdistD (k + 2) L (a₁ - a₂) : ℝ))) :=
  @RBM.Loop.pureLoop_two_of_isKLoop

example : ∀ (d L W : ℕ) [NeZero L] (g E : ℝ), 3 ≤ L → 1 ≤ W → |E| < 2 →
    ∀ (K : ℝ → LoopIdx (Zd d L) → ℂ), IsKLoop d L W g (mSigma E) (Set.Ico 0 1) K →
      ∀ t ∈ Set.Ico (0 : ℝ) 1, ∀ (I : LoopIdx (Zd d L)), I.WF → 1 ≤ I.length →
        K t I = KLK d L g W E t I :=
  @RBM.Loop.KLK_unique

example : ∀ (d L W : ℕ) [NeZero L] (g E : ℝ), 3 ≤ L → 1 ≤ W → |E| < 2 → ∀ t ∈ Set.Ico (0 : ℝ) 1,
    ∀ (c : Zd d L) (I : LoopIdx (Zd d L)), I.WF →
      KLK d L g W E t ⟨I.σ, I.a.map (· + c)⟩ = KLK d L g W E t I :=
  @RBM.Loop.KLK_translate

example : ∀ (d L W : ℕ) [NeZero L] (g E : ℝ), 3 ≤ L → 1 ≤ W → |E| < 2 → ∀ t ∈ Set.Ico (0 : ℝ) 1,
    ∀ (s : Bool) (b : Zd d L) (σ : List Bool) (a : List (Zd d L)), σ.length = a.length →
      KLK d L g W E t ⟨s :: σ, b :: a⟩ = KLK d L g W E t ⟨σ ++ [s], a ++ [b]⟩ :=
  @RBM.Loop.KLK_rotate

/-! ## Names the targets use (merged) -/
#check @RBM.Loop.IsKLoopS
#check @RBM.Loop.treeEqRhsS
#check @RBM.Loop.IsKLoop_iff_IsKLoopS
#check @RBM.Loop.KLK_isKLoop
#check @RBM.SB_transpose
#check @RBM.SB_apply_add_right

end RBM.Loop.T2366Check
