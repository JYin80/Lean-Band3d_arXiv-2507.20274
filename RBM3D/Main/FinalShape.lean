/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Main.BandTerminal
import RBM3D.BA.UNBUniv
import RBM3D.BA.MAPins

set_option linter.style.longLine false

/-!
# The final shape: Theorems 2.1-2.5 and Theorem 2.7

The final theorem: the band Theorems 2.1-2.5 (`band_terminal`, in `Main/BandTerminal.lean`) together
with the block Anderson Theorem 2.7 (`MR:decol_BA`) at every `d ≥ 3`, conditional only on the
external input `UNL32` (Theorem 2.2 of Landon-Sosoe-Yau, arXiv:1609.09011v4).  No new mathematics:
every conjunct is a theorem proved elsewhere.

* `Thm27 := ∀ d, 3 ≤ d → BAThm27L d`: Theorem 2.7 at every `d ≥ 3`, the five bullets in the order of
  `band_terminal` (decol, locSC, QUE, BUniv, QDiff) at each `d`;
* `Thm27_of_L32 := baThm27L_all` (`BA/UNBUniv`);
* `final_shape : UNL32 → (decol ∧ locSC ∧ QUE ∧ BUniv ∧ QDiff) ∧ Thm27`.

The instances at the end apply the conjuncts at concrete data.  At `d = 3` all five block Anderson
conjuncts are applied on the class sequence `S0` (`L = 4`, `W_n = (2(n+1))⁵`, constant coupling
`λ = g₀`), `(𝔠, 𝔡) = (1/6, 1/10)`, and at `d = 4` all five conjuncts (decol, locSC, QUE, BUniv,
QDiff) are applied on the class sequence with `L = 4`, `W_n = (2(n+1))⁵`, `(𝔠, 𝔡) = (1/8, 1/10)`,
over a bulk proved to be nonempty.  Only `UNL32` stays a
hypothesis.
-/

namespace RBM.Endpoints

open RBM.Univ

/-- **Theorem 2.7 (`MR:decol_BA`) at every `d ≥ 3`**: `BAThm27L d` for each `d ≥ 3`, the five bullets in
the order of `band_terminal`: decol, locSC, QUE, BUniv, QDiff. -/
def Thm27 : Prop := ∀ d : ℕ, 3 ≤ d → RBM.BA.BAThm27L d

/-- Theorem 2.7 at every `d ≥ 3` from the external input `UNL32` only: `baThm27L_all` (`BA/UNBUniv`). -/
theorem Thm27_of_L32 : RBM.Univ.UNL32 → Thm27 := RBM.BA.baThm27L_all

/-- **The final shape**: the paper's main results (band Theorems 2.1-2.5, block Anderson Theorem 2.7 at every `d ≥ 3`) with the single
external hypothesis `UNL32` (Theorem 2.2 of Landon-Sosoe-Yau, arXiv:1609.09011v4). -/
theorem final_shape : RBM.Univ.UNL32 →
    (decol ∧ locSC ∧ QUE ∧ BUniv ∧ QDiff) ∧ Thm27 := fun h32 =>
  ⟨band_terminal h32, Thm27_of_L32 h32⟩

/-! ## Instances at concrete data (`d = 3`, `(𝔠, 𝔡) = (1/6, 1/10)`; then `d = 4`, `(𝔠, 𝔡) = (1/8, 1/10)`)

The band conjuncts are applied at `Inst.inst_*` (the instances section of `Main/BandTerminal.lean`) on `sz0`.  The five
block Anderson conjuncts at `d = 3` are applied on the class sequence `S0`, at `κ_* = clsκ 4 _` and at the energy
`E_* = (fp 4 _).E`, which is in the bulk for every `n`.  Only `UNL32` stays a hypothesis. -/

section Instances

open RBM.Gauss.SizesInst RBM.Univ.UNInst

private theorem FinalShape_hg : (0 : ℝ) < 3 / 10 := by norm_num

/-- `decol` of `final_shape` at the instance data. -/
example (h32 : UNL32) :=
  Inst.inst_decol (final_shape h32).1.1

/-- `locSC` of `final_shape` at the instance data. -/
example (h32 : UNL32) :=
  Inst.inst_locSC (final_shape h32).1.2.1

/-- `QUE` of `final_shape` at the instance data. -/
example (h32 : UNL32) :=
  Inst.inst_QUE (final_shape h32).1.2.2.1

/-- `BUniv` of `final_shape` at the instance data. -/
example (h32 : UNL32) :=
  Inst.inst_BUniv (final_shape h32).1.2.2.2.1

/-- `QDiff` of `final_shape` at the instance data. -/
example (h32 : UNL32) :=
  Inst.inst_QDiff (final_shape h32).1.2.2.2.2

section BAInstances

open RBM.BA.UNPinsInst RBM.Univ.BAInst RBM.BA

/-- The five block Anderson conjuncts of `(final_shape h32).2 3 le_rfl` applied at `S0`, `κ_* = clsκ 4`, `E_*` in the bulk; the QUE
conjunct at `τ = 1/300`. -/
example (h32 : UNL32) : True := by
  have h := (final_shape h32).2 3 le_rfl
  have _ := h.1 le_rfl (1 / 6) (1 / 10) S0 S0_adm (clsκ 4 FinalShape_hg) (1 / 10) 1 (clsκ_pos 4 FinalShape_hg) (by norm_num) (by norm_num)
  have _ := h.2.1 le_rfl (1 / 6) (1 / 10) S0 S0_adm (clsκ 4 FinalShape_hg) (1 / 20) (1 / 10) 2 (clsκ_pos 4 FinalShape_hg) (by norm_num)
    (by norm_num) (by norm_num)
  have _ := h.2.2.1 le_rfl (1 / 6) (1 / 10) S0 S0_adm (clsκ 4 FinalShape_hg) (clsκ_pos 4 FinalShape_hg) (1 / 30) (1 / 60) (1 / 300)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have _ := h.2.2.2.1 le_rfl (1 / 6) (1 / 10) S0 S0_adm 1 le_rfl (clsκ 4 FinalShape_hg) (clsκ_pos 4 FinalShape_hg) (fp 4 FinalShape_hg).E S0_bulk 0
    (by norm_num) UNInst.bump UNInst.bump_testFun
  have _ := h.2.2.2.2 le_rfl (1 / 6) (1 / 10) S0 S0_adm (clsκ 4 FinalShape_hg) (1 / 20) (1 / 10) 2 (clsκ_pos 4 FinalShape_hg)
    (by norm_num) (by norm_num) (by norm_num)
  trivial

/-- The whole `final_shape` at the instance data: all ten conjuncts at once, `UNL32` the only hypothesis (Theorem 2.7 at `d = 3`). -/
example (h32 : UNL32) : True := by
  have h := final_shape h32
  have h2 := h.2 3 le_rfl
  have _ := Inst.inst_decol h.1.1
  have _ := Inst.inst_locSC h.1.2.1
  have _ := Inst.inst_QUE h.1.2.2.1
  have _ := Inst.inst_BUniv h.1.2.2.2.1
  have _ := Inst.inst_QDiff h.1.2.2.2.2
  have _ := h2.1 le_rfl (1 / 6) (1 / 10) S0 S0_adm (clsκ 4 FinalShape_hg) (1 / 10) 1 (clsκ_pos 4 FinalShape_hg) (by norm_num) (by norm_num)
  have _ := h2.2.1 le_rfl (1 / 6) (1 / 10) S0 S0_adm (clsκ 4 FinalShape_hg) (1 / 20) (1 / 10) 2 (clsκ_pos 4 FinalShape_hg) (by norm_num)
    (by norm_num) (by norm_num)
  have _ := h2.2.2.1 le_rfl (1 / 6) (1 / 10) S0 S0_adm (clsκ 4 FinalShape_hg) (clsκ_pos 4 FinalShape_hg) (1 / 30) (1 / 60) (1 / 300)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have _ := h2.2.2.2.1 le_rfl (1 / 6) (1 / 10) S0 S0_adm 1 le_rfl (clsκ 4 FinalShape_hg) (clsκ_pos 4 FinalShape_hg) (fp 4 FinalShape_hg).E S0_bulk 0
    (by norm_num) UNInst.bump UNInst.bump_testFun
  have _ := h2.2.2.2.2 le_rfl (1 / 6) (1 / 10) S0 S0_adm (clsκ 4 FinalShape_hg) (1 / 20) (1 / 10) 2 (clsκ_pos 4 FinalShape_hg)
    (by norm_num) (by norm_num) (by norm_num)
  trivial

end BAInstances

/-! ### The `d = 4` instance: `(𝔠, 𝔡) = (1/8, 1/10)`, nonempty bulk

The class sequence at `d = 4` (the analogue of `clsSz` at `d = 3`): constant block size `L = 4`, bandwidth `W_n = (2(n+1))^5` and
constant coupling `g₀`.  The bulk is nonempty: a real-axis solution of `(self_m)` at `(d, L) = (4, 4)` is built from the
subordination point `w = 6i/5` (`BASelf_subord`, `BAzztE_data`, as `exists_flowPt` does at `d = 3`), and `BAbulk_iff_exists` turns it
into `BAbulk 4 4 g₀ κ E` with `κ = Im m₀ / π > 0`, for every `n`.  All five conjuncts of `Thm27 4`
(decol, locSC, QUE, BUniv, QDiff) are applied over it, `BUniv` at `k = 1`, `E' = 0`, `𝒪 = UNInst.bump`. -/

section D4Instance

open Filter RBM.Gauss RBM.BA RBM.BA.MFixedPointInst

/-- The class sequence at `d = 4`: `L = 4`, `W_n = (2(n+1))^5`, `lam = g₀`. -/
private def FinalShape_cls4 (g0 : ℝ) : Sizes 4 where
  L := fun _ => 4
  W := fun n => (2 * (n + 1)) ^ 5
  lam := fun _ => g0
  three_le_L := fun _ => by norm_num
  W_pos := fun n => by positivity

private theorem FinalShape_cls4_W4 (n : ℕ) : 4 ≤ (FinalShape_cls4 0).W n := by
  have h := Nat.pow_le_pow_left (show 2 ≤ 2 * (n + 1) by omega) 5
  change 4 ≤ (2 * (n + 1)) ^ 5
  omega

private theorem FinalShape_cls4_adm {g0 : ℝ} (h0 : 0 < g0) (h10 : g0 ≤ 10) :
    (FinalShape_cls4 g0).Admissible (1 / 8) (1 / 10) := by
  have hx1 (n : ℕ) : (1 : ℝ) ≤ 2 * ((n : ℝ) + 1) := by have := Nat.cast_nonneg (α := ℝ) n; linarith
  refine ⟨by norm_num, by norm_num, ?_, Eventually.of_forall fun n => ?_, ?_⟩
  · refine tendsto_atTop_mono (fun n => ?_) tendsto_natCast_atTop_atTop
    have h1 : 2 * (n + 1) ≤ (2 * (n + 1)) ^ 5 := Nat.le_self_pow (by norm_num) _
    have h2 : (2 * (n + 1)) ^ 5 ≤ (2 * (n + 1)) ^ 5 * 4 := Nat.le_mul_of_pos_right _ (by norm_num)
    have h3 : (2 * (n + 1)) ^ 5 * 4 ≤ ((2 * (n + 1)) ^ 5 * 4) ^ 4 := Nat.le_self_pow (by norm_num) _
    have h4 : n ≤ (FinalShape_cls4 g0).size n := by
      change n ≤ ((2 * (n + 1)) ^ 5 * 4) ^ 4
      omega
    exact_mod_cast h4
  · have hW := FinalShape_cls4_W4 n
    have hle : (FinalShape_cls4 g0).size n ≤ ((FinalShape_cls4 g0).W n) ^ 8 := by
      change ((FinalShape_cls4 g0).W n * 4) ^ 4 ≤ ((FinalShape_cls4 g0).W n) ^ 8
      calc ((FinalShape_cls4 g0).W n * 4) ^ 4 ≤ ((FinalShape_cls4 g0).W n * (FinalShape_cls4 g0).W n) ^ 4 :=
            Nat.pow_le_pow_left (Nat.mul_le_mul_left _ hW) 4
        _ = ((FinalShape_cls4 g0).W n) ^ 8 := by ring
    have h' : (((FinalShape_cls4 g0).size n : ℕ) : ℝ) ≤ (((FinalShape_cls4 g0).W n : ℕ) : ℝ) ^ 8 := by exact_mod_cast hle
    calc (((FinalShape_cls4 g0).size n : ℕ) : ℝ) ^ (1 / 8 : ℝ)
        ≤ ((((FinalShape_cls4 g0).W n : ℕ) : ℝ) ^ 8) ^ (1 / 8 : ℝ) := Real.rpow_le_rpow (Nat.cast_nonneg _) h' (by norm_num)
      _ = (((FinalShape_cls4 g0).W n : ℕ) : ℝ) := by
          rw [show (1 / 8 : ℝ) = ((8 : ℕ) : ℝ)⁻¹ by norm_num]
          exact Real.pow_rpow_inv_natCast (Nat.cast_nonneg _) (by norm_num)
  · rw [Sizes.WO, Filter.eventually_atTop]
    refine ⟨⌈g0⁻¹⌉₊, fun n hn => ?_⟩
    have hx0 : (0 : ℝ) < 2 * ((n : ℝ) + 1) := by positivity
    have hnR : g0⁻¹ ≤ (n : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hn)
    have hW : (((FinalShape_cls4 g0).W n : ℕ) : ℝ) = (2 * ((n : ℝ) + 1)) ^ 5 := by simp [FinalShape_cls4]
    have hexp : (-((4 : ℕ) : ℝ) / 2 + 1 / 10 : ℝ) = -(19 / 10) := by norm_num
    have hpow : ((2 * ((n : ℝ) + 1)) ^ 5) ^ (-(19 / 10) : ℝ) = (2 * ((n : ℝ) + 1)) ^ (-(19 / 2) : ℝ) := by
      rw [← Real.rpow_natCast (2 * ((n : ℝ) + 1)) 5, ← Real.rpow_mul hx0.le]
      norm_num
    refine ⟨?_, ?_⟩
    · rw [hW, hexp, hpow]
      calc (2 * ((n : ℝ) + 1)) ^ (-(19 / 2) : ℝ) ≤ (2 * ((n : ℝ) + 1)) ^ (-1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (hx1 n) (by norm_num)
        _ = (2 * ((n : ℝ) + 1))⁻¹ := Real.rpow_neg_one _
        _ ≤ (g0⁻¹)⁻¹ := inv_anti₀ (inv_pos.mpr h0) (by linarith)
        _ = g0 := inv_inv g0
    · change g0 ≤ (1 / 10 : ℝ)⁻¹
      norm_num
      exact h10

/-- A nonempty bulk at `(d, L) = (4, 4)`: a coupling `g₀ ∈ (0, 3/10]`, an energy `E` and `κ > 0` with `κ ≤ ρ(E)`. -/
private theorem FinalShape_bulk4 : ∃ g0 E κ : ℝ, 0 < g0 ∧ g0 ≤ 3 / 10 ∧ 0 < κ ∧ BAbulk 4 4 g0 κ E := by
  have hg : (0 : ℝ) < 3 / 10 := by norm_num
  obtain ⟨z, m, hs, hzim⟩ : ∃ z m : ℂ, BASelf 4 4 (3 / 10) z m ∧ 0 < z.im :=
    ⟨_, _, (BASelf_subord 4 4 (3 / 10) one_lt_wI).1, (BASelf_subord 4 4 (3 / 10) one_lt_wI).2.2.2⟩
  obtain ⟨ht0, -, hself0, -⟩ := BAzztE_data 4 4 (3 / 10) hzim hs
  have hm0 := hself0.1
  refine ⟨Real.sqrt (BAt0 z m) * (3 / 10), BAflowE z m, (m / (Real.sqrt (BAt0 z m) : ℂ)).im / Real.pi,
    mul_pos (Real.sqrt_pos.mpr ht0) hg, BAg0_le hg.le hzim hs.1, div_pos hm0 Real.pi_pos, ?_⟩
  rw [BAbulk_iff_exists 4 4 _ _ _ (div_pos hm0 Real.pi_pos)]
  exact ⟨_, hself0, le_of_eq (by field_simp)⟩

/-- The end domain is nonempty at every `n`: `z = E + i` (`E` in the bulk, `N^{-1+ε} ≤ 1 ≤ 1`). -/
private theorem FinalShape_dom4 {g0 E κ ε : ℝ} (hε : ε ≤ 1) (hb : BAbulk 4 4 g0 κ E) (n : ℕ) :
    ∃ z : ℂ, BAendDom (FinalShape_cls4 g0) κ ε n z := by
  refine ⟨⟨E, 1⟩, hb, ?_, le_rfl⟩
  have hN : (1 : ℝ) ≤ Nsz (FinalShape_cls4 g0) n := by
    have h1 : 1 ≤ (FinalShape_cls4 g0).size n :=
      Nat.one_le_pow _ _ (Nat.mul_pos ((FinalShape_cls4 g0).W_pos n) (by change 0 < 4; norm_num))
    exact_mod_cast h1
  exact Real.rpow_le_one_of_one_le_of_nonpos hN (by linarith)

/-- **The `d = 4` instance of `Thm27`**: `Sizes 4` data `FinalShape_cls4 g₀` admissible at `(1/8, 1/10)`, a
**nonempty bulk** `BAbulk 4 4 g₀ κ E` (every `n`) and nonempty end domains, and all five conjuncts of
`(final_shape h32).2 4` (decol, locSC, QUE, BUniv, QDiff) applied at it; `UNL32` is the only hypothesis. -/
example (h32 : UNL32) : ∃ g0 E κ : ℝ, 0 < κ ∧ (FinalShape_cls4 g0).Admissible (1 / 8) (1 / 10) ∧
    (∀ᶠ n in atTop, BAbulk 4 ((FinalShape_cls4 g0).L n) ((FinalShape_cls4 g0).lam n) κ E) ∧
    ∀ n, ∃ z : ℂ, BAendDom (FinalShape_cls4 g0) κ (1 / 10) n z := by
  obtain ⟨g0, E, κ, hg0, hg3, hκ, hb⟩ := FinalShape_bulk4
  have hadm := FinalShape_cls4_adm hg0 (hg3.trans (by norm_num))
  have h := (final_shape h32).2 4 (by norm_num)
  have _ := h.1 (by norm_num) (1 / 8) (1 / 10) (FinalShape_cls4 g0) hadm κ (1 / 10) 1 hκ (by norm_num) (by norm_num)
  have _ := h.2.1 (by norm_num) (1 / 8) (1 / 10) (FinalShape_cls4 g0) hadm κ (1 / 20) (1 / 10) 2 hκ (by norm_num) (by norm_num)
    (by norm_num)
  have _ := h.2.2.1 (by norm_num) (1 / 8) (1 / 10) (FinalShape_cls4 g0) hadm κ hκ (1 / 30) (1 / 60) (1 / 300)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have _ := h.2.2.2.1 (by norm_num) (1 / 8) (1 / 10) (FinalShape_cls4 g0) hadm 1 le_rfl κ hκ E (Eventually.of_forall fun _ => hb) 0
    (by norm_num) UNInst.bump UNInst.bump_testFun
  have _ := h.2.2.2.2 (by norm_num) (1 / 8) (1 / 10) (FinalShape_cls4 g0) hadm κ (1 / 20) (1 / 10) 2 hκ (by norm_num) (by norm_num)
    (by norm_num)
  exact ⟨g0, E, κ, hκ, hadm, Eventually.of_forall fun _ => hb, FinalShape_dom4 (by norm_num) hb⟩

end D4Instance

end Instances

end RBM.Endpoints
