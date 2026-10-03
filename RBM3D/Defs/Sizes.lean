/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Gauss.Model
import RBM3D.Defs.Params

/-!
# The fine lattice `Z_{WL}^d` and the size data of an admissible sequence

Ticket T2006 (MD-1).  Sections 1 and 2 of the compiled T2002 probe (`RBM3D/Probe/T2002Vocab.lean`
at `5d2a4a8` on branch `t/T2002`, never merged), copied with their docstrings and proofs; the
checks at the end of the file are copied from the probe's section 9, except `sz0_locDomain`,
which is new.  Paper: arXiv:2507.20274,
`paper/tex/1_2_Intro_model_result.tex` (cited `1_2:line`).  RBM2D sources are cited as
`RBM2D/<file>:<line>` at commit `c9a24cf`.

* Section 1: the fine lattice `Idx d L W = Z_{WL}^d`, the block label `blk` and the offset `ofs`
  of a coordinate, the bridge `split`/`splitEquiv` to the block-product index `Vtx d L W` of
  `RBM3D/Gauss/Model.lean`, the blocks `Iblk` (`W^d` points each), the fine-lattice cardinality
  `card_Idx`, and the `L^∞` distance `zdistInf`.
* Section 2: `Sizes d` (the block count `L`, the block side `W` and the coupling `lam` as
  sequences), the scale `size n = (W n * L n)^d`, the predicates `WO`, `Bandwidth`,
  `SizeTendsto`, `Admissible`, `locDomain`, the control `Bctl`, and the conversions
  `W^τ ↔ N^τ'` (`W_rpow_le`, `size_rpow_le_W_rpow`).

`lam` is the paper's `\ilambda`, nothing in `Sizes` fixes it; `(eq:WO)` is the separate predicate
`Sizes.WO`.
-/

noncomputable section

open Filter

namespace RBM.Gauss

/-! ## 1. The fine lattice `Z_{WL}^d`, blocks, distance -/

section Lattice

variable (d L W : ℕ)

/-- The fine lattice `Z_{WL}^d` of Section 2 (`1_2:262`); RBM2D `Idx L W := Z2 (W * L)`
(`RBM2D/Gauss/Model.lean:39`), rule R2. -/
abbrev Idx : Type := Zd d (W * L)

/-- The block (coordinate in `Z_L`) of a one-dimensional coordinate of `Z_{WL}` (`(eq:blockIa)`,
`1_2:266`; zero-based blocks, paper delta T2002d): `RBM2D/Defs/Model.lean:126`. -/
def blk (i : ZMod (W * L)) : ZMod L := ((i.val / W : ℕ) : ZMod L)

variable [NeZero L] [NeZero W]

/-- The offset inside a one-dimensional block (`(eq:blockIa)`, `1_2:266`):
`RBM2D/Defs/Model.lean:129`. -/
def ofs (i : ZMod (W * L)) : Fin W := ⟨i.val % W, Nat.mod_lt _ (NeZero.pos W)⟩

theorem blk_val (i : ZMod (W * L)) : (blk L W i).val = i.val / W :=
  ZMod.val_natCast_of_lt (Nat.div_lt_of_lt_mul (ZMod.val_lt i))

/-- Block label and offset of a lattice point, coordinatewise (`(eq:blockIa)`, `1_2:266`);
the offset is stored in `Fin (W^d)` so that the target is the merged `Vtx d L W`.
`RBM2D/Defs/Model.lean:132` (`split`), rules R2/R3. -/
def split (i : Idx d L W) : Vtx d L W :=
  (fun k => blk L W (i k), finFunctionFinEquiv (fun k => ofs L W (i k)))

theorem split_injective : Function.Injective (split d L W) := by
  intro i j h
  simp only [split, Prod.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  funext k
  apply ZMod.val_injective
  have hb : (i k).val / W = (j k).val / W := by
    rw [← blk_val, ← blk_val]; exact congrArg ZMod.val (congrFun h1 k)
  have ho : (i k).val % W = (j k).val % W :=
    congrArg Fin.val (congrFun (finFunctionFinEquiv.injective h2) k)
  rw [← Nat.div_add_mod' (i k).val W, ← Nat.div_add_mod' (j k).val W, hb, ho]

theorem split_bijective : Function.Bijective (split d L W) := by
  refine (Fintype.bijective_iff_injective_and_card _).mpr ⟨split_injective d L W, ?_⟩
  simp only [Idx, Vtx, Zd, Fintype.card_prod, Fintype.card_fun, ZMod.card, Fintype.card_fin]
  rw [mul_pow, mul_comm]

/-- `Z_{WL}^d ≃ Z_L^d × {0,…,W^d-1}` (`(eq:blockIa)`, `1_2:266`): the bridge between the fine
lattice (statements) and the block-product index `Vtx` (loops).
`RBM2D/Defs/Model.lean:186` (`splitEquiv`). -/
noncomputable def splitEquiv : Idx d L W ≃ Vtx d L W :=
  Equiv.ofBijective _ (split_bijective d L W)

/-- The block `[a] = {x : x ∈ block a}` of `(eq:blockIa)` (`1_2:266`); it has `W^d` points.
`RBM2D/Defs/Model.lean:143` (`Iblk`). -/
def Iblk (a : Zd d L) : Finset (Idx d L W) :=
  Finset.univ.filter fun x => (split d L W x).1 = a

theorem card_Iblk (a : Zd d L) : (Iblk d L W a).card = W ^ d := by
  have h : (Iblk d L W a).card =
      (Finset.univ.filter fun p : Vtx d L W => p.1 = a).card := by
    refine Finset.card_equiv (splitEquiv d L W) fun x => ?_
    simp [Iblk, splitEquiv, Equiv.ofBijective_apply]
  rw [h, Finset.card_filter, Fintype.sum_prod_type]
  have hx : ∀ x : Zd d L, (∑ _y : Fin (W ^ d), if x = a then 1 else 0) =
      if x = a then W ^ d else 0 := by
    intro x; by_cases h : x = a <;> simp [h]
  simp only [hx, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

/-- The fine lattice has `(W L)^d = N` points (`1_2:263`): the matrix dimension. -/
theorem card_Idx : Fintype.card (Idx d L W) = (W * L) ^ d := by
  simp [Idx, Zd, ZMod.card]

end Lattice

/-- The paper's `|x|` is the periodic `L^∞` norm (`1_2:274`, `|x-y| ≡ ‖[x-y]_{WL}‖_∞`);
the merged `RBM.zdistD` (`Defs/Lattice.lean:71`) is the `ℓ¹` norm.  Both are kept: this one for
the stochastic and endpoint statements, `zdistD` for the propagator side. -/
def zdistInf (d L : ℕ) (x : Zd d L) : ℕ := Finset.univ.sup fun i => zdist L (x i)

theorem zdistInf_le_zdistD (d L : ℕ) (x : Zd d L) : zdistInf d L x ≤ zdistD d L x :=
  Finset.sup_le fun i _ =>
    Finset.single_le_sum (f := fun j => zdist L (x j)) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ i)

theorem zdistD_le_mul_zdistInf (d L : ℕ) (x : Zd d L) : zdistD d L x ≤ d * zdistInf d L x := by
  calc zdistD d L x = ∑ i, zdist L (x i) := rfl
    _ ≤ ∑ _i : Fin d, zdistInf d L x :=
        Finset.sum_le_sum fun i _ => Finset.le_sup (f := fun j => zdist L (x j)) (Finset.mem_univ i)
    _ = d * zdistInf d L x := by simp

/-! ## 2. The size data: `λ` is a sequence -/

/-- **The size data of an admissible sequence** (`1_2:262`, `(eq:WO)` `1_2:363`).
`L n`, `W n`: the number and the side of the blocks at size index `n`; `lam n`: the coupling
`ilambda` of `def:ilambda` (`1_2:256`, `ilambda = λ^{-1}`; the TeX macro prints it as `g`,
`main.tex:199`), passed as the `g` argument of the merged `SB`, `ellT`, `Bparam`.
**`lam` is a sequence**; nothing here fixes it (it may tend to `0`); `(eq:WO)` is the separate
predicate `Sizes.WO`.  The dimension `d` is the parameter of the structure (rule R1: RBM2D's
`d : Sizes` becomes `sz : Sizes d`).
`RBM2D/Gauss/Model.lean:405` (`Sizes`), extended by `lam`. -/
structure Sizes (d : ℕ) where
  /-- number of blocks per side, `L ≥ 3` -/
  L : ℕ → ℕ
  /-- block side, `W ≥ 1` -/
  W : ℕ → ℕ
  /-- the coupling `ilambda` of `def:ilambda` -/
  lam : ℕ → ℝ
  three_le_L : ∀ n, 3 ≤ L n
  W_pos : ∀ n, 0 < W n

namespace Sizes

variable {d : ℕ} (sz : Sizes d)

instance neZeroL (n : ℕ) : NeZero (sz.L n) := ⟨by have := sz.three_le_L n; omega⟩
instance neZeroW (n : ℕ) : NeZero (sz.W n) := ⟨(sz.W_pos n).ne'⟩

/-- **The scale `N = (W L)^d`** (`1_2:263`): the matrix dimension, and the one scale parameter of
every `≺` of the stochastic chain (section 7).  `RBM2D/Gauss/Model.lean:419` (`size`), rule R3. -/
def size (n : ℕ) : ℕ := (sz.W n * sz.L n) ^ d

/-- The scale is the matrix dimension: `N = (W L)^d` is the number of lattice points. -/
theorem card_Idx (n : ℕ) : Fintype.card (Idx d (sz.L n) (sz.W n)) = sz.size n :=
  RBM.Gauss.card_Idx d (sz.L n) (sz.W n)

/-- `(eq:WO)` (`1_2:363`): `W^{-d/2+𝔡} ≤ ilambda ≤ 𝔡^{-1}`, eventually along the sequence. -/
def WO (𝔡 : ℝ) : Prop :=
  ∀ᶠ n in atTop, ((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2 + 𝔡) ≤ sz.lam n ∧ sz.lam n ≤ 𝔡⁻¹

/-- `(Main_DEL_COND)` (`1_2:359`): `W ≥ N^𝔠`, eventually. -/
def Bandwidth (𝔠 : ℝ) : Prop :=
  ∀ᶠ n in atTop, ((sz.size n : ℕ) : ℝ) ^ 𝔠 ≤ (sz.W n : ℝ)

/-- `N → ∞`: the paper's "provided `N` is sufficiently large" (`1_2:366`), made explicit (paper
delta T2001b of RBM2D, DECISIONS §13). -/
def SizeTendsto : Prop := Tendsto (fun n => ((sz.size n : ℕ) : ℝ)) atTop atTop

/-- The standing hypotheses of `MR:decol`, `MR:locSC`, ... (`1_2:357–363`): constants `𝔠, 𝔡 > 0`
with `W ≥ N^𝔠` and `(eq:WO)`.  `RBM2D/Endpoints.lean:63` (`Admissible`), extended by `(eq:WO)`. -/
def Admissible (𝔠 𝔡 : ℝ) : Prop :=
  0 < 𝔠 ∧ 0 < 𝔡 ∧ sz.SizeTendsto ∧ sz.Bandwidth 𝔠 ∧ sz.WO 𝔡

/-- The same blocks with another coupling sequence: the Gaussian potential `V` of the block
Anderson model has `S^(B)(0) = I` (`bandcwV`, `1_2:606`), i.e. the model of `sz.withLam 0`. -/
def withLam (g : ℕ → ℝ) : Sizes d := { sz with lam := g }

/-- `𝐃_{κ,ε}` of `(eq:spectral_domain)` (`1_2:380`) at size index `n`; the scale of the lower
bound on `η` is `N = sz.size n`.  `RBM2D/Endpoints.lean:74` (`locDomain`). -/
def locDomain (κ ε : ℝ) (n : ℕ) (z : ℂ) : Prop :=
  |z.re| ≤ 2 - κ ∧ ((sz.size n : ℕ) : ℝ) ^ (-1 + ε) ≤ z.im ∧ z.im ≤ 1

/-- `ilambda² W^d ≥ W^{2𝔡}` from `(eq:WO)` (`1_2:363`), pointwise in `n`.  Hence `(ilambda² W^d)⁻¹ ≤
W^{-2𝔡}`: the bound on the first term of `W^{-d} B_{t,0}` (`(eq_B_param)`, `1_2:1108`:
`W^{-d} (ilambda² + 1 - t)⁻¹ ≤ (ilambda² W^d)⁻¹`; `(eq:BetaK)`, `1_2:514`), and, to the power `1/5`,
the small factor of `(Eq:Gtlp_exp)` (`1_2:1211`). -/
theorem lam_sq_mul_pow_ge (n : ℕ) {𝔡 : ℝ}
    (h : ((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2 + 𝔡) ≤ sz.lam n) :
    ((sz.W n : ℕ) : ℝ) ^ (2 * 𝔡) ≤ sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d := by
  have hW : (0 : ℝ) < sz.W n := by exact_mod_cast sz.W_pos n
  have h0 : 0 ≤ ((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2 + 𝔡) := Real.rpow_nonneg hW.le _
  have hsq : (((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2 + 𝔡)) ^ 2 ≤ sz.lam n ^ 2 :=
    pow_le_pow_left₀ h0 h 2
  have hexp : (((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2 + 𝔡)) ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d =
      ((sz.W n : ℕ) : ℝ) ^ (2 * 𝔡) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hW.le, ← Real.rpow_natCast (((sz.W n : ℕ) : ℝ)) d,
      ← Real.rpow_add hW]
    congr 1; push_cast; ring
  calc ((sz.W n : ℕ) : ℝ) ^ (2 * 𝔡)
      = (((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2 + 𝔡)) ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d := hexp.symm
    _ ≤ sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d :=
        mul_le_mul_of_nonneg_right hsq (by positivity)

/-- **The induction control `W^{-d} B_{t,0}`** (`(Eq:L-KGt)` `1_2:1196`, `(con_st_ind)` `1_2:1296`),
built from the merged `Bparam` (`(eq_B_param)`, `1_2:1108`) at the coupling `sz.lam n`: the single
deterministic control of the chain, in the role of RBM2D's `scaleM⁻¹` (`Path/Scales.lean:44`, a d=2
scale that is not ported). -/
def Bctl (n : ℕ) (t : ℝ) : ℝ :=
  (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * Bparam d (sz.L n) (sz.lam n) t 0

/-! ### Conversion `W^τ ↔ N^τ'` (the scale is `N`; `W ≥ N^𝔠`) -/

/-- `W^τ ≤ N^{τ/d}`: the paper's `W^τ` is dominated by the one scale `N` (`τ ≥ 0`, `d ≥ 1`). -/
theorem W_rpow_le (hd : 0 < d) (n : ℕ) {τ : ℝ} (hτ : 0 ≤ τ) :
    ((sz.W n : ℕ) : ℝ) ^ τ ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / d) := by
  have hW : (0 : ℝ) ≤ sz.W n := Nat.cast_nonneg _
  have hL : 0 < sz.L n := by have := sz.three_le_L n; omega
  have hle : ((sz.W n : ℕ) : ℝ) ^ d ≤ ((sz.size n : ℕ) : ℝ) := by
    have h : (sz.W n) ^ d ≤ (sz.W n * sz.L n) ^ d :=
      Nat.pow_le_pow_left (Nat.le_mul_of_pos_right _ hL) d
    exact_mod_cast h
  have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  calc ((sz.W n : ℕ) : ℝ) ^ τ = (((sz.W n : ℕ) : ℝ) ^ (d : ℝ)) ^ (τ / d) := by
        rw [← Real.rpow_mul hW]; congr 1; field_simp
    _ ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / d) := by
        apply Real.rpow_le_rpow (by positivity) _ (by positivity)
        rwa [Real.rpow_natCast]

/-- `N^τ ≤ W^{τ/𝔠}` from `W ≥ N^𝔠` (`(Main_DEL_COND)`): `≺` at the scale `N` gives the paper's
`W^τ` statements and conversely. -/
theorem size_rpow_le_W_rpow {𝔠 : ℝ} (h𝔠 : 0 < 𝔠) (n : ℕ)
    (hb : ((sz.size n : ℕ) : ℝ) ^ 𝔠 ≤ (sz.W n : ℝ)) {τ : ℝ} (hτ : 0 ≤ τ) :
    ((sz.size n : ℕ) : ℝ) ^ τ ≤ ((sz.W n : ℕ) : ℝ) ^ (τ / 𝔠) := by
  have hN : (0 : ℝ) ≤ (sz.size n : ℝ) := Nat.cast_nonneg _
  calc ((sz.size n : ℕ) : ℝ) ^ τ = (((sz.size n : ℕ) : ℝ) ^ 𝔠) ^ (τ / 𝔠) := by
        rw [← Real.rpow_mul hN]; congr 1; field_simp
    _ ≤ ((sz.W n : ℕ) : ℝ) ^ (τ / 𝔠) :=
        Real.rpow_le_rpow (Real.rpow_nonneg hN _) hb (by positivity)

end Sizes

end RBM.Gauss

/-! ### Checks: the preflight sequence at `d = 3`

`L_n = 4(n+1)`, `W_n = (2(n+1))^5`, `lam_n = (2(n+1))^{-6}`, `N_n = (W_n L_n)^3`; `n = 0` is
`L = 4`, `W = 32`, `lam = 1/64`, `N = 2097152`; constants `𝔠 = 1/6`, `𝔡 = 1/10`, `κ = ε = 1/10`.
Source: the probe section 9 (`5d2a4a8`, lines 1048-1150, 1202-1214, 1396-1404), namespace renamed
from `T2002Inst`; the check `sz0_locDomain` is new. -/

namespace RBM.Gauss.SizesInst

/-- The preflight size sequence: `lam` tends to `0`, `L ≤ W`, `W ≥ N^{1/6}`. -/
def sz0 : Sizes 3 where
  L := fun n => 4 * (n + 1)
  W := fun n => (2 * (n + 1)) ^ 5
  lam := fun n => ((2 * ((n : ℝ) + 1)) ^ 6)⁻¹
  three_le_L := fun n => by omega
  W_pos := fun n => by positivity

theorem sz0_values : sz0.L 0 = 4 ∧ sz0.W 0 = 32 ∧ sz0.size 0 = 2097152 ∧ sz0.lam 0 = 1 / 64 := by
  refine ⟨rfl, rfl, ?_, ?_⟩
  · norm_num [Sizes.size, sz0]
  · norm_num [sz0]

theorem sz0_L_le_W (n : ℕ) : sz0.L n ≤ sz0.W n := by
  have hm : 2 ≤ 2 * (n + 1) := by omega
  have h4 : 2 ^ 4 ≤ (2 * (n + 1)) ^ 4 := Nat.pow_le_pow_left hm 4
  change 4 * (n + 1) ≤ (2 * (n + 1)) ^ 5
  calc 4 * (n + 1) ≤ 2 ^ 4 * (2 * (n + 1)) := by omega
    _ ≤ (2 * (n + 1)) ^ 4 * (2 * (n + 1)) := Nat.mul_le_mul_right _ h4
    _ = (2 * (n + 1)) ^ 5 := by ring

theorem sz0_size_le_W_pow (n : ℕ) : sz0.size n ≤ (sz0.W n) ^ 6 := by
  have h := sz0_L_le_W n
  calc sz0.size n = (sz0.W n * sz0.L n) ^ 3 := rfl
    _ = (sz0.W n) ^ 3 * (sz0.L n) ^ 3 := by rw [mul_pow]
    _ ≤ (sz0.W n) ^ 3 * (sz0.W n) ^ 3 :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h 3)
    _ = (sz0.W n) ^ 6 := by ring

theorem sz0_bandwidth_at (n : ℕ) :
    ((sz0.size n : ℕ) : ℝ) ^ (1 / 6 : ℝ) ≤ (sz0.W n : ℝ) := by
  have h : ((sz0.size n : ℕ) : ℝ) ≤ ((sz0.W n : ℕ) : ℝ) ^ 6 := by exact_mod_cast sz0_size_le_W_pow n
  calc ((sz0.size n : ℕ) : ℝ) ^ (1 / 6 : ℝ)
      ≤ (((sz0.W n : ℕ) : ℝ) ^ 6) ^ (1 / 6 : ℝ) :=
        Real.rpow_le_rpow (Nat.cast_nonneg _) h (by norm_num)
    _ = (sz0.W n : ℝ) := by
        rw [show (1 / 6 : ℝ) = ((6 : ℕ) : ℝ)⁻¹ by norm_num]
        exact Real.pow_rpow_inv_natCast (Nat.cast_nonneg _) (by norm_num)

theorem sz0_bandwidth : sz0.Bandwidth (1 / 6) := Eventually.of_forall sz0_bandwidth_at

theorem sz0_tendsto : sz0.SizeTendsto := by
  refine tendsto_atTop_mono (fun n => ?_) tendsto_natCast_atTop_atTop
  have h1 : 4 * (n + 1) ≤ (2 * (n + 1)) ^ 5 * (4 * (n + 1)) :=
    Nat.le_mul_of_pos_left _ (by positivity)
  have h2 : (2 * (n + 1)) ^ 5 * (4 * (n + 1)) ≤ ((2 * (n + 1)) ^ 5 * (4 * (n + 1))) ^ 3 :=
    Nat.le_self_pow (by norm_num) _
  have h3 : n ≤ sz0.size n := by
    change n ≤ ((2 * (n + 1)) ^ 5 * (4 * (n + 1))) ^ 3
    omega
  exact_mod_cast h3

theorem sz0_WO : sz0.WO (1 / 10) := by
  refine Eventually.of_forall fun n => ?_
  have hx0 : (0 : ℝ) < 2 * ((n : ℝ) + 1) := by positivity
  have hx1 : (1 : ℝ) ≤ 2 * ((n : ℝ) + 1) := by
    have := Nat.cast_nonneg (α := ℝ) n; linarith
  have hW : ((sz0.W n : ℕ) : ℝ) = (2 * ((n : ℝ) + 1)) ^ 5 := by simp [sz0]
  have hlam : sz0.lam n = ((2 * ((n : ℝ) + 1)) ^ 6)⁻¹ := rfl
  have hexp : (-((3 : ℕ) : ℝ) / 2 + 1 / 10 : ℝ) = -(7 / 5) := by norm_num
  have hpow : ((2 * ((n : ℝ) + 1)) ^ 5) ^ (-(7 / 5) : ℝ) = ((2 * ((n : ℝ) + 1)) ^ 7)⁻¹ := by
    rw [← Real.rpow_natCast (2 * ((n : ℝ) + 1)) 5, ← Real.rpow_mul hx0.le,
      show ((5 : ℕ) : ℝ) * (-(7 / 5)) = -((7 : ℕ) : ℝ) by norm_num, Real.rpow_neg hx0.le,
      Real.rpow_natCast]
  refine ⟨?_, ?_⟩
  · rw [hW, hexp, hpow, hlam]
    exact inv_anti₀ (by positivity) (pow_le_pow_right₀ hx1 (by norm_num))
  · rw [hlam]
    refine (inv_le_one_of_one_le₀ (one_le_pow₀ hx1)).trans (by norm_num)

/-- **The size pin, instantiated**: the preflight sequence is admissible at `𝔠 = 1/6`,
`𝔡 = 1/10`, with `lam → 0`, every hypothesis discharged. -/
theorem sz0_admissible : sz0.Admissible (1 / 6) (1 / 10) :=
  ⟨by norm_num, by norm_num, sz0_tendsto, sz0_bandwidth, sz0_WO⟩

/-- `ilambda² W^d ≥ W^{2𝔡}` along the preflight sequence (`n = 0`: `8 ≥ 32^{1/5} = 2`). -/
theorem sz0_lam_sq : ∀ᶠ n in atTop,
    ((sz0.W n : ℕ) : ℝ) ^ (2 * (1 / 10 : ℝ)) ≤ sz0.lam n ^ 2 * ((sz0.W n : ℕ) : ℝ) ^ 3 := by
  filter_upwards [sz0_WO] with n hn
  exact Sizes.lam_sq_mul_pow_ge sz0 n hn.1

/-- The merged scales at the instance, `t = 0`, `n = 0`: `ℓ_0 = 1` (`(eq:ellt)`) and
`B_{0,0} = (1 + lam²)⁻¹ + L^{-d}` (`(eq_B_param)`), so `W^{-d}B_{0,0} > 0`. -/
theorem scales_sz0 : ellT 4 (1 / 64) 0 = 1 ∧
    Bparam 3 4 (1 / 64) 0 0 = ((1 / 64 : ℝ) ^ 2 + 1)⁻¹ + ((4 : ℝ) ^ 3)⁻¹ ∧ 0 < sz0.Bctl 0 0 := by
  refine ⟨?_, ?_, ?_⟩
  · norm_num [ellT]
  · norm_num [Bparam]
  · have : (0 : ℝ) < Bparam 3 (sz0.L 0) (sz0.lam 0) 0 0 := by
      have h := sz0_values
      rw [h.1, h.2.2.2]; norm_num [Bparam]
    have hW : (0 : ℝ) < ((sz0.W 0 : ℕ) : ℝ) := by exact_mod_cast sz0.W_pos 0
    unfold Sizes.Bctl
    exact mul_pos (by positivity) this

/-- `lam` really tends to `0`: nothing in the size pins fixes `λ`. -/
theorem sz0_lam_tendsto : Tendsto sz0.lam atTop (nhds 0) := by
  have h : Tendsto (fun n : ℕ => (2 * ((n : ℝ) + 1)) ^ 6) atTop atTop := by
    refine (tendsto_pow_atTop (by norm_num : 6 ≠ 0)).comp ?_
    refine tendsto_atTop_mono (fun n => ?_) (tendsto_natCast_atTop_atTop (R := ℝ))
    have := Nat.cast_nonneg (α := ℝ) n; linarith
  exact h.inv_tendsto_atTop


/-- A block of the fine lattice at the instance has `W^d = 32768` points. -/
theorem card_Iblk_sz0 (a : Zd 3 4) : (Iblk 3 4 32 a).card = 32768 := by
  rw [card_Iblk]; norm_num

/-- The matrix dimension at the instance is `N = (32 · 4)^3 = 2097152`. -/
theorem card_Idx_sz0 : Fintype.card (Idx 3 (sz0.L 0) (sz0.W 0)) = 2097152 := by
  rw [Sizes.card_Idx]; exact sz0_values.2.2.1

/-- The two distances at a concrete point of `Z_4^3` (`(eq:blockIa)` torus, `1_2:274`): the `L^∞`
distance of the stochastic statements is `2`, the merged `ℓ¹` distance is `4`. -/
theorem zdistInf_inst :
    zdistInf 3 4 ![(2 : ZMod 4), 1, 3] = 2 ∧ zdistD 3 4 ![(2 : ZMod 4), 1, 3] = 4 := by
  constructor <;> decide

/-! ### The scale conversion at the instance -/

theorem W_le_size_sz0 :
    ((sz0.W 0 : ℕ) : ℝ) ^ (1 / 10 : ℝ) ≤
      ((sz0.size 0 : ℕ) : ℝ) ^ ((1 / 10 : ℝ) / (3 : ℕ)) :=
  Sizes.W_rpow_le sz0 (by norm_num) 0 (by norm_num)

theorem size_le_W_sz0 :
    ((sz0.size 0 : ℕ) : ℝ) ^ (1 / 10 : ℝ) ≤
      ((sz0.W 0 : ℕ) : ℝ) ^ ((1 / 10 : ℝ) / (1 / 6 : ℝ)) :=
  Sizes.size_rpow_le_W_rpow sz0 (by norm_num) 0 (sz0_bandwidth_at 0) (by norm_num)

/-- The two distances at the same concrete point obey `zdistInf ≤ zdistD ≤ d · zdistInf`
(`zdistInf_le_zdistD`, `zdistD_le_mul_zdistInf`): `2 ≤ 4 ≤ 3 · 2`. -/
example : zdistInf 3 4 ![(2 : ZMod 4), 1, 3] ≤ zdistD 3 4 ![(2 : ZMod 4), 1, 3] ∧
    zdistD 3 4 ![(2 : ZMod 4), 1, 3] ≤ 3 * zdistInf 3 4 ![(2 : ZMod 4), 1, 3] :=
  ⟨zdistInf_le_zdistD 3 4 _, zdistD_le_mul_zdistInf 3 4 _⟩

/-- The bridge `Z_{WL}^3 ≃ Z_4^3 × Fin (32^3)` at the instance (`split_bijective`). -/
example : Function.Bijective (split 3 4 32) := split_bijective 3 4 32

/-- `withLam` changes only the coupling: the same blocks and the same scale. -/
example (g : ℕ → ℝ) (n : ℕ) :
    (sz0.withLam g).L n = sz0.L n ∧ (sz0.withLam g).W n = sz0.W n ∧
      (sz0.withLam g).size n = sz0.size n := ⟨rfl, rfl, rfl⟩

/-- `𝐃_{κ,ε}` is nonempty at the instance (`κ = ε = 1/10`, `n = 0`, `N = 2097152`): the point
`z = 1/2 + i N^{-4/5}` has `|Re z| = 1/2 ≤ 2 - κ` and
`N^{-1+ε} = N^{-9/10} ≤ N^{-4/5} = Im z ≤ 1`. -/
theorem sz0_locDomain :
    sz0.locDomain (1 / 10) (1 / 10) 0
      (⟨1 / 2, ((sz0.size 0 : ℕ) : ℝ) ^ (-(4 / 5) : ℝ)⟩ : ℂ) := by
  have hN : (1 : ℝ) ≤ ((sz0.size 0 : ℕ) : ℝ) := by
    rw [sz0_values.2.2.1]; norm_num
  refine ⟨?_, ?_, ?_⟩
  · simp only [abs_of_pos (show (0 : ℝ) < 1 / 2 by norm_num)]
    norm_num
  · exact Real.rpow_le_rpow_of_exponent_le hN (by norm_num)
  · exact Real.rpow_le_one_of_one_le_of_nonpos hN (by norm_num)

end RBM.Gauss.SizesInst
