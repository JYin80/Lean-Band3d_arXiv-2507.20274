/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Graph.LWExpSound
import RBM3D.Graph.LWExpTerm4
import RBM3D.Induction.ExpIntIQ
import RBM3D.Induction.ExpWardII
import RBM3D.Induction.ExpIntEasy

set_option linter.style.header false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

/-!
# LW-14f (T2334): `(Gammamuxy)` for a joined graph, the consumer of `LWG5Expand'`, and the Step 6 closures

Paper: arXiv:2507.20274, `paper/tex/B_graphical_lemmas.tex:78-108` (`B:line`): the expansion `(eq:sizeGammamu_E)` and the bound
`(Gammamuxy)`; `paper/tex/6_Step6_two_loop.tex:83-97` (`lem:LWterm_EXP`, the Step 6 regimes).  No port (RBM2D has no
light-weight layer).

## What is proved (namespace `RBM.Gauss.Sizes`, helpers `lwExpTerm6_`, instances `RBM.Gauss.Sizes.LWExpTerm6Inst`)

* §1 the pin `LwGraphPrecJoin` (the check file `docs/tickets/checks/T2334-check.lean`, section 2, verbatim).
* §2 **the pathwise bound of a joined graph** `lwExpTerm6_pathwise`: for a normal packed graph with `n_M = 0` (every vertex lies in
  the molecule of the external vertices), `|Γ_{xy}| ≤ t^{n_W} C_Γ Ψ^{n_S} (W^{-d})^{n_W - n_V}` on the entry event
  `‖(G - M)_{xy}‖ ≤ Ψ`: every solid factor is `≤ Ψ` (`LGraph.term_norm_le`) and the waved factors are summed along a spanning forest
  (`LGraph.waved_sum_le`, no `ξ`, no `GtoAG`, no `scalemole`).
* §3 its arithmetic, `W^{-d} ≤ (𝔡⁻² + 1) B` (`STBctl_ge`), `Ψ = N^{τ'} B^{1/2}`: `≤ N^τ η⁻¹ B^{ord/2}`.
* §4 `lwGraphPrecJoin_holds : ∀ d, LwGraphPrecJoin d` (the skeleton of `lwGraphPrec1`: `≺ → 𝔼` for `t^{-n_W} Γ`).
* §5 the consumer `lwExpG5'_of_expand' : LWG5Expand' d → LwGraphPrecJoin d → LWExpG5' d` (copies of `lwExpTerm3_T4pos` and
  `lwExpG5'_of_expand` with the coefficients `m^j m̄^{j'}`, `‖m^j m̄^{j'}‖ = 1`, and the joined branch).
* §6 the unconditional chain `lwExpG5'_holds`, `lwCutExp_holds`, `lwTermEXP_holds` and the closures `stStep6I_holds`,
  `stStep6II_holds`, `stStep6III_holds`.
* §7 compiled instances.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Matrix

namespace RBM.Gauss.Sizes

open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Graph RBM.Green

/-! ## 1. The pin (copied verbatim from `docs/tickets/checks/T2334-check.lean`, section 2) -/

/-- **`(Gammamuxy)` for a joined graph** (`q = 0`, one molecule containing both external vertices): the analogue of
`LwGraphPrec1` without `ξ` (pathwise: waved spanning tree, `W^{-d} ≤ (𝔡⁻² + 1) B` by `STBctl_ge`). -/
def LwGraphPrecJoin (d : ℕ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z →
      ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ lemT (z n)) →
        STLocalEntry sz (STflowE z) t →
        ∀ P : PGraph (Fin 2), P.g.Normal → LWJoined P →
          Prec sz (U := fun n => Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n))
            (fun n p _ => ‖∫ ω, P.val (LWG5Data sz n (STflowE z n) (t n) ω) ![p.1, p.2] ∂(sz.seqP)‖)
            (fun n _ _ => (t n) ^ P.g.nW * (etaT (STflowE z n) (t n))⁻¹ *
              (sz.Bctl n (t n)) ^ ((P.g.scalingOrder : ℝ) / 2))

/-! ## 2. The pathwise bound of a graph with `n_M = 0` -/

section Pathwise6

variable {d : ℕ} (sz : Sizes d)

/-- **The pathwise bound of a graph without internal molecule** (`B:78-108`, the joined case of `(Gammamuxy)`): on the entry event
`‖(G - M)_{xy}‖ ≤ Ψ`, `|Γ_{xy}| ≤ t^{n_W} C_Γ Ψ^{n_S} (W^{-d})^{n_W - n_V}`.  Every solid factor is `≤ Ψ` (the `×`-dotted edges force
distinct labels, `LGraph.term_norm_le`), the waved factors are summed along a spanning forest rooted at the external vertices
(`LGraph.waved_sum_le`: `n_V` tree edges cost `t C e`, the other `n_W - n_V` edges cost `t C W^{-d}`). -/
theorem lwExpTerm6_pathwise (hd : 3 ≤ d) (P : PGraph (Fin 2)) (hN : P.g.Normal) (hnM : P.g.nM = 0)
    (Es ts : ℕ → ℝ) (n : ℕ) (ω : sz.SeqΩ) (C₁ c₁ Ψ : ℝ) (hC₁ : 0 ≤ C₁) (hc₁ : 0 < c₁) (hΨ : 0 ≤ Ψ)
    (ht0 : 0 ≤ ts n)
    (hS : ∀ x y, ‖lwS sz n (ts n) x y‖ ≤ ts n * C₁ * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ *
      Real.exp (-(c₁ * (lwBdist d (sz.L n) (sz.W n) x y : ℝ))))
    (hSp : ∀ x y, ‖lwSplus sz n (ts n) (mE (Es n)) x y‖ ≤ ts n * C₁ * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ *
      Real.exp (-(c₁ * (lwBdist d (sz.L n) (sz.W n) x y : ℝ))))
    (hE1 : ∀ x y : Idx d (sz.L n) (sz.W n), ‖STGM sz n (Es n) (ts n) ω x y‖ ≤ Ψ)
    (v : Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n)) :
    ‖P.val (LWG5Data sz n (Es n) (ts n) ω) ![v.1, v.2]‖ ≤ (ts n) ^ P.g.nW *
      (P.g.sizeConst C₁ (C₁ * expC (d - 2) c₁) *
        (Ψ ^ P.g.nS * ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹) ^ (P.g.nW - P.g.nV))) := by
  classical
  set D := LWG5Data sz n (Es n) (ts n) ω with hD
  have hcnt := P.g.counters_le hN.1
  have hnVW : P.g.nV ≤ P.g.nW := by have := hcnt.2; omega
  have hK1 : 0 ≤ P.g.sizeConst C₁ (C₁ * expC (d - 2) c₁) :=
    LGraph.sizeConst_nonneg P.g hC₁ (mul_nonneg hC₁ (by unfold expC; positivity))
  have hWi : 0 ≤ (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ := by positivity
  have hrhs : 0 ≤ (ts n) ^ P.g.nW *
      (P.g.sizeConst C₁ (C₁ * expC (d - 2) c₁) *
        (Ψ ^ P.g.nS * ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹) ^ (P.g.nW - P.g.nV))) :=
    mul_nonneg (pow_nonneg ht0 _) (mul_nonneg hK1 (mul_nonneg (pow_nonneg hΨ _) (pow_nonneg hWi _)))
  by_cases hf : ∃ ℓ' : P.E' → Idx d (sz.L n) (sz.W n), ![v.1, v.2] = ℓ' ∘ P.ext
  swap
  · rw [P.val_of_not D hf, norm_zero]
    exact hrhs
  obtain ⟨ℓ', hℓ'⟩ := hf
  rw [P.val_of_factor D hℓ']
  have hM := lwExpTerm3_Data_M sz n (Es n) (ts n) ω
  have hG : ∀ x y, x ≠ y → ‖D.G x y‖ ≤ Ψ := fun x y hxy => by
    have h := hE1 x y
    simp only [STGM, hxy, ite_false, sub_zero] at h
    rw [hD, lwExpTerm3_Data_G]
    exact h
  have hGd : ∀ x, ‖D.G x x - mE (Es n)‖ ≤ Ψ := fun x => by
    have h := hE1 x x
    simp only [STGM, ite_true] at h
    rw [hD, lwExpTerm3_Data_G]
    exact h
  have hts : 0 ≤ ts n * C₁ := mul_nonneg ht0 hC₁
  have hKS := lwKBound_of_decay hd hts hc₁ (K := D.S) hS
  have hKSp := lwKBound_of_decay hd hts hc₁ (K := D.Sp) hSp
  have hsum := P.g.waved_sum_le hN D hKS hKSp ℓ'
  have hterm : ∀ ℓi : P.I' → Idx d (sz.L n) (sz.W n), ‖P.g.term D (Sum.elim ℓ' ℓi)‖ ≤
      ‖P.g.coeff‖ * Ψ ^ P.g.nS * (P.g.waved.map fun e => ‖WEdge.val D (Sum.elim ℓ' ℓi) e‖).prod :=
    fun ℓi => P.g.term_norm_le hN D hM hG hGd _
  unfold LGraph.val
  have hcn : 0 ≤ ‖P.g.coeff‖ * Ψ ^ P.g.nS := by positivity
  calc ‖∑ ℓi : P.I' → Idx d (sz.L n) (sz.W n), P.g.term D (Sum.elim ℓ' ℓi)‖
      ≤ ∑ ℓi : P.I' → Idx d (sz.L n) (sz.W n), ‖P.g.term D (Sum.elim ℓ' ℓi)‖ := norm_sum_le _ _
    _ ≤ ∑ ℓi : P.I' → Idx d (sz.L n) (sz.W n), ‖P.g.coeff‖ * Ψ ^ P.g.nS *
          (P.g.waved.map fun e => ‖WEdge.val D (Sum.elim ℓ' ℓi) e‖).prod :=
        Finset.sum_le_sum fun ℓi _ => hterm ℓi
    _ = ‖P.g.coeff‖ * Ψ ^ P.g.nS * ∑ ℓi : P.I' → Idx d (sz.L n) (sz.W n),
          (P.g.waved.map fun e => ‖WEdge.val D (Sum.elim ℓ' ℓi) e‖).prod := by rw [Finset.mul_sum]
    _ ≤ ‖P.g.coeff‖ * Ψ ^ P.g.nS * ((Fintype.card (Idx d (sz.L n) (sz.W n)) : ℝ) ^ P.g.nM *
          ((ts n * C₁ * expC (d - 2) c₁) ^ (P.g.nV - P.g.nM) *
            (ts n * C₁ * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹) ^ (P.g.nW - (P.g.nV - P.g.nM)))) := by
        refine mul_le_mul_of_nonneg_left ?_ hcn
        have := hsum
        rw [mul_assoc] at this
        exact this
    _ = _ := by
        unfold LGraph.sizeConst
        rw [hnM, Nat.sub_zero, pow_zero, one_mul]
        obtain ⟨k, hk⟩ : ∃ k, P.g.nW = P.g.nV + k := ⟨P.g.nW - P.g.nV, by omega⟩
        have hk' : P.g.nW - P.g.nV = k := by omega
        rw [hk']
        rw [hk]
        ring

end Pathwise6

/-! ## 3. The arithmetic of the joined bound -/

/-- `K Ψ^{n_S} (W^{-d})^k ≤ N^τ η⁻¹ B^{(n_S + 2k)/2}` for `Ψ = N^{τ'} B^{1/2}`, `W^{-d} ≤ A B`, `K A^k ≤ N^{τ/2}`,
`τ' n_S ≤ τ/2` (`η ≤ 1`). -/
theorem lwExpTerm6_arith {N B η Wi A K τ τ' Ψ : ℝ} (nS k : ℕ)
    (hN : 1 ≤ N) (hB0 : 0 < B) (hη0 : 0 < η) (hη1 : η ≤ 1)
    (hΨ : Ψ = N ^ τ' * Real.sqrt B) (hτ' : τ' * (nS : ℝ) ≤ τ / 2)
    (hWi0 : 0 ≤ Wi) (hWi : Wi ≤ A * B) (hK0 : 0 ≤ K)
    (hKN : K * A ^ k ≤ N ^ (τ / 2)) :
    K * (Ψ ^ nS * Wi ^ k) ≤ N ^ τ * (η⁻¹ * B ^ (((nS : ℝ) + 2 * (k : ℝ)) / 2)) := by
  have hN0 : 0 < N := by linarith
  have hη' : 1 ≤ η⁻¹ := (one_le_inv₀ hη0).2 hη1
  have hΨ1 : Ψ ^ nS = N ^ (τ' * (nS : ℝ)) * B ^ ((nS : ℝ) / 2) := by
    rw [hΨ, mul_pow, ← Real.rpow_natCast, ← Real.rpow_mul hN0.le, Real.sqrt_eq_rpow,
      ← Real.rpow_natCast (B ^ (1 / 2 : ℝ)), ← Real.rpow_mul hB0.le]
    congr 2; ring
  have hBk : B ^ (((nS : ℝ) + 2 * (k : ℝ)) / 2) = B ^ ((nS : ℝ) / 2) * B ^ k := by
    rw [← Real.rpow_natCast B k, ← Real.rpow_add hB0]; congr 1; ring
  have hBp : 0 ≤ B ^ (((nS : ℝ) + 2 * (k : ℝ)) / 2) := Real.rpow_nonneg hB0.le _
  have hN1 : N ^ (τ' * (nS : ℝ)) ≤ N ^ (τ / 2) := Real.rpow_le_rpow_of_exponent_le hN hτ'
  have hBs : 0 ≤ B ^ ((nS : ℝ) / 2) := Real.rpow_nonneg hB0.le _
  have hNs : 0 ≤ N ^ (τ' * (nS : ℝ)) := Real.rpow_nonneg hN0.le _
  calc K * (Ψ ^ nS * Wi ^ k)
      ≤ K * (N ^ (τ' * (nS : ℝ)) * B ^ ((nS : ℝ) / 2) * (A * B) ^ k) := by
        rw [hΨ1]; gcongr
    _ = (K * A ^ k) * N ^ (τ' * (nS : ℝ)) * (B ^ ((nS : ℝ) / 2) * B ^ k) := by rw [mul_pow]; ring
    _ ≤ N ^ (τ / 2) * N ^ (τ / 2) * B ^ (((nS : ℝ) + 2 * (k : ℝ)) / 2) := by
        rw [← hBk]; gcongr
    _ = N ^ τ * B ^ (((nS : ℝ) + 2 * (k : ℝ)) / 2) := by
        rw [← Real.rpow_add hN0]; congr 2; ring
    _ ≤ N ^ τ * (η⁻¹ * B ^ (((nS : ℝ) + 2 * (k : ℝ)) / 2)) := by
        have : 0 ≤ N ^ τ := Real.rpow_nonneg hN0.le _
        gcongr
        nlinarith

/-! ## 4. `(Gammamuxy)` for a joined graph -/

theorem lwGraphPrecJoin_holds (d : ℕ) : LwGraphPrecJoin d := by
  intro hd κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hz t ht0 htz hLE P hN hJ
  classical
  obtain ⟨-, -, hnM⟩ := hJ
  obtain ⟨hA, -, ht1, hRange⟩ := RBM.Green.v3_premises_of_stFlow sz hκ hε hz htz
  obtain ⟨h𝔠, -, hsz, hbw, hWO⟩ := hA
  have hE2 : ∀ n, |STflowE z n| < 2 := st6_flowE_lt_two sz hκ hz
  have hEκ : ∀ n, |STflowE z n| ≤ 2 - κ := st6_flowE_le sz hz
  have hd0 : 0 < d := by omega
  have hsize := sz.tendsto_size hsz
  obtain ⟨Cs, cs, hCs, hcs, hSd⟩ := lwExpTerm3_Sp_decay d hd 𝔡⁻¹ κ (inv_pos.2 h𝔡) hκ
  have hcnt := P.g.counters_le hN.1
  have hnVW : P.g.nV ≤ P.g.nW := by have := hcnt.2; omega
  set k : ℕ := P.g.nW - P.g.nV with hk
  set o : ℤ := P.g.scalingOrder with ho
  have hoR : (o : ℝ) = (P.g.nS : ℝ) + 2 * (k : ℝ) := by
    have : o = (P.g.nS : ℤ) + 2 * ((k : ℕ) : ℤ) := by
      rw [ho, hk]
      unfold LGraph.scalingOrder
      simp only [ord, LGraph.counters]
      omega
    rw [this]; push_cast; ring
  -- the random statement
  set X : ∀ n, (Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n)) → sz.SeqΩ → ℂ := fun n v ω =>
    (((t n) ^ P.g.nW : ℝ)⁻¹ : ℝ) * P.val (LWG5Data sz n (STflowE z n) (t n) ω) ![v.1, v.2] with hX
  have hB1 := st5_Bctl_le_one sz hκ hε hz htz
  have hηev := expAvg_eta_inv_le sz hκ hε hz
  have hlam : ∀ᶠ n in atTop, 0 < sz.lam n ∧ sz.lam n ≤ 𝔡⁻¹ := by
    filter_upwards [hWO] with n hn
    exact ⟨lt_of_lt_of_le (Real.rpow_pos_of_pos (by exact_mod_cast sz.W_pos n) _) hn.1, hn.2⟩
  have hdecay : ∀ n, 0 < sz.lam n → sz.lam n ≤ 𝔡⁻¹ → (∀ x y, ‖lwS sz n (t n) x y‖ ≤ t n * Cs *
      (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * Real.exp (-(cs * (lwBdist d (sz.L n) (sz.W n) x y : ℝ)))) ∧
      (∀ x y, ‖lwSplus sz n (t n) (mE (STflowE z n)) x y‖ ≤ t n * Cs * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ *
      Real.exp (-(cs * (lwBdist d (sz.L n) (sz.W n) x y : ℝ)))) := fun n hl1 hl2 =>
    ⟨fun x y => ((hSd sz n hl1 hl2 (t n) (STflowE z n) (ht0 n) (ht1 n) (hEκ n) x y).1),
      fun x y => ((hSd sz n hl1 hl2 (t n) (STflowE z n) (ht0 n) (ht1 n) (hEκ n) x y).2)⟩
  have henv : ∀ᶠ n in atTop, ∀ v ω, ‖X n v ω‖ ≤ ((sz.size n : ℕ) : ℝ) ^ (((P.g.nV + 2 * P.g.nS + 2 : ℕ)) : ℝ) := by
    filter_upwards [hηev, hlam, hsz.eventually_ge_atTop (max (max ‖P.g.coeff‖ (Cs ^ P.g.nW)) 2)] with n hηn hlamn hNn
    intro v ω
    obtain ⟨hS1, hS2⟩ : (∀ x y, ‖lwS sz n (t n) x y‖ ≤ t n * Cs) ∧
        (∀ x y, ‖lwSplus sz n (t n) (mE (STflowE z n)) x y‖ ≤ t n * Cs) := by
      have hW1 : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
      have hWi : (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ hW1)
      have hdrop : ∀ x y : Idx d (sz.L n) (sz.W n), t n * Cs * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ *
          Real.exp (-(cs * (lwBdist d (sz.L n) (sz.W n) x y : ℝ))) ≤ t n * Cs := fun x y => by
        have he : Real.exp (-(cs * (lwBdist d (sz.L n) (sz.W n) x y : ℝ))) ≤ 1 :=
          Real.exp_le_one_iff.2 (by have := Nat.cast_nonneg (α := ℝ) (lwBdist d (sz.L n) (sz.W n) x y); nlinarith)
        have h0 : 0 ≤ t n * Cs := mul_nonneg (ht0 n) hCs.le
        calc t n * Cs * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * Real.exp (-(cs * (lwBdist d (sz.L n) (sz.W n) x y : ℝ)))
            ≤ t n * Cs * 1 * 1 := by gcongr
          _ = _ := by ring
      have := hdecay n hlamn.1 hlamn.2
      exact ⟨fun x y => (this.1 x y).trans (hdrop x y), fun x y => (this.2 x y).trans (hdrop x y)⟩
    have hbd := lwExpTerm3_X_norm_le sz P n (hE2 n) (ht0 n) (ht1 n) hCs.le hS1 hS2 ω v
    have hpoly := lwExpTerm3_poly (N := ((sz.size n : ℕ) : ℝ)) (η := etaT (STflowE z n) (t n))
      (cn := ‖P.g.coeff‖) (Cw := Cs ^ P.g.nW) ((le_max_right _ _).trans hNn)
      (hηn (t n) (htz n)) (inv_nonneg.2 (etaT_pos (hE2 n) (ht1 n)).le)
      (((le_max_left _ _).trans (le_max_left _ _)).trans hNn)
      (((le_max_right _ _).trans (le_max_left _ _)).trans hNn) (pow_nonneg hCs.le _) P.g.nV P.g.nS
    refine hbd.trans (hpoly.trans (le_of_eq ?_))
    rw [← Real.rpow_natCast]
  have hfloor : ∀ᶠ n in atTop, ∀ v : Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n),
      ((sz.size n : ℕ) : ℝ) ^ (-(((|o| : ℤ) : ℝ) / 2)) ≤
        (etaT (STflowE z n) (t n))⁻¹ * (sz.Bctl n (t n)) ^ ((o : ℝ) / 2) := by
    filter_upwards [hB1] with n hBn v
    have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
    exact lwExpTerm3_floor hN1 (STBctl_pos sz n (ht1 n)) (hBn (t n) le_rfl) (expAvg_Bctl_ge sz n (ht0 n) (ht1 n))
      (etaT_pos (hE2 n) (ht1 n)) (lwExpTerm3_etaT_le_one (hE2 n) (ht0 n) (ht1 n)) o
  have hprecX : Prec sz (U := fun n => Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n))
      (fun n v ω => ‖X n v ω‖)
      (fun n _ _ => (etaT (STflowE z n) (t n))⁻¹ * (sz.Bctl n (t n)) ^ ((o : ℝ) / 2)) := by
    refine StochDomAt.of_highProbAt_add_rpow_neg (P := sz.seqP) (size := sz.size) hsize
      (b := ((|o| : ℤ) : ℝ) / 2) ?_ ?_
    · refine HighProbAt.of_eventually_univ ?_
      filter_upwards [hfloor] with n hn ω v
      exact hn v
    · intro τ hτ D hD
      set τ' : ℝ := τ / (2 * ((P.g.nS : ℝ) + 1)) with hτ'def
      have hτ'0 : 0 < τ' := by positivity
      have hτ' : τ' * (P.g.nS : ℝ) ≤ τ / 2 := by
        rw [hτ'def, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
        nlinarith [(Nat.cast_nonneg P.g.nS : (0 : ℝ) ≤ P.g.nS)]
      have hE₁ := lwExpTerm3_entry_whp sz hLE hτ'0
      refine HighProbAt.mono hE₁ ?_
      set K₀ : ℝ := P.g.sizeConst Cs (Cs * expC (d - 2) cs) with hK₀
      have hτ2 : 0 < τ / 2 := by positivity
      have hK₀0 : 0 ≤ K₀ := LGraph.sizeConst_nonneg P.g hCs.le (mul_nonneg hCs.le (by unfold expC; positivity))
      have hev1 : ∀ᶠ n in atTop, K₀ * ((𝔡⁻¹) ^ 2 + 1) ^ k ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) :=
        ((tendsto_rpow_atTop hτ2).comp hsz).eventually_ge_atTop _
      filter_upwards [hlam, hB1, hev1] with n hlamn hBn hK1n
      intro ω hω1 v
      have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
      have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
      have hB0 : 0 < sz.Bctl n (t n) := STBctl_pos sz n (ht1 n)
      have hη0 : 0 < etaT (STflowE z n) (t n) := etaT_pos (hE2 n) (ht1 n)
      have hη1 : etaT (STflowE z n) (t n) ≤ 1 := lwExpTerm3_etaT_le_one (hE2 n) (ht0 n) (ht1 n)
      have hW0 : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
      have hΨ0 : 0 ≤ ((sz.size n : ℕ) : ℝ) ^ τ' * Real.sqrt (sz.Bctl n (t n)) :=
        mul_nonneg (Real.rpow_nonneg hN0.le _) (Real.sqrt_nonneg _)
      have hBge := STBctl_ge sz n (ht0 n) (ht1 n)
      have hl2 : sz.lam n ^ 2 + 1 ≤ (𝔡⁻¹) ^ 2 + 1 := by
        have := pow_le_pow_left₀ hlamn.1.le hlamn.2 2
        linarith
      have hl0 : 0 < sz.lam n ^ 2 + 1 := by positivity
      have hWinv : (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ ((𝔡⁻¹) ^ 2 + 1) * sz.Bctl n (t n) := by
        have h1 : (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ (sz.lam n ^ 2 + 1) * sz.Bctl n (t n) := by
          have := mul_le_mul_of_nonneg_left hBge hl0.le
          calc (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ = (sz.lam n ^ 2 + 1) * ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (sz.lam n ^ 2 + 1)⁻¹) := by
                field_simp
            _ ≤ _ := this
        exact h1.trans (mul_le_mul_of_nonneg_right hl2 hB0.le)
      obtain ⟨hS1, hS2⟩ := hdecay n hlamn.1 hlamn.2
      have hpath := lwExpTerm6_pathwise sz hd P hN hnM (STflowE z) t n ω Cs cs
        (((sz.size n : ℕ) : ℝ) ^ τ' * Real.sqrt (sz.Bctl n (t n))) hCs.le hcs hΨ0 (ht0 n) hS1 hS2 hω1 v
      change ‖X n v ω‖ ≤ ((sz.size n : ℕ) : ℝ) ^ τ * ((etaT (STflowE z n) (t n))⁻¹ * (sz.Bctl n (t n)) ^ ((o : ℝ) / 2)) +
        ((sz.size n : ℕ) : ℝ) ^ (-D)
      have hDnn : 0 ≤ ((sz.size n : ℕ) : ℝ) ^ (-D) := Real.rpow_nonneg hN0.le _
      refine le_trans ?_ (le_add_of_nonneg_right hDnn)
      simp only [hX]
      by_cases h : (t n) ^ P.g.nW = 0
      · rw [h]
        simp only [_root_.inv_zero, Complex.ofReal_zero, zero_mul, norm_zero]
        have hη' : 0 < (etaT (STflowE z n) (t n))⁻¹ := inv_pos.2 hη0
        have hBo : 0 ≤ sz.Bctl n (t n) ^ ((o : ℝ) / 2) := Real.rpow_nonneg hB0.le _
        positivity
      · rw [norm_mul, Complex.norm_real, norm_inv, Real.norm_of_nonneg (pow_nonneg (ht0 n) _)]
        have hpos : 0 < (t n) ^ P.g.nW := lt_of_le_of_ne (pow_nonneg (ht0 n) _) (Ne.symm h)
        have harith := lwExpTerm6_arith (N := ((sz.size n : ℕ) : ℝ)) (B := sz.Bctl n (t n))
          (η := etaT (STflowE z n) (t n)) (Wi := (((sz.W n : ℕ) : ℝ) ^ d)⁻¹) (A := (𝔡⁻¹) ^ 2 + 1) (K := K₀)
          (τ := τ) (τ' := τ') (Ψ := ((sz.size n : ℕ) : ℝ) ^ τ' * Real.sqrt (sz.Bctl n (t n))) P.g.nS k hN1 hB0 hη0 hη1
          rfl hτ' (by positivity) hWinv hK₀0 hK1n
        rw [← hoR] at harith
        calc ((t n) ^ P.g.nW)⁻¹ * ‖P.val (LWG5Data sz n (STflowE z n) (t n) ω) ![v.1, v.2]‖
            ≤ ((t n) ^ P.g.nW)⁻¹ * ((t n) ^ P.g.nW * (K₀ * (_ * _))) :=
              mul_le_mul_of_nonneg_left hpath (inv_nonneg.2 hpos.le)
          _ = K₀ * (_ * _) := by rw [← mul_assoc, inv_mul_cancel₀ hpos.ne', one_mul]
          _ ≤ _ := harith
  have hint := lwExpTerm_prec_integral sz X (fun n v => (etaT (STflowE z n) (t n))⁻¹ *
    (sz.Bctl n (t n)) ^ ((o : ℝ) / 2)) hsz henv hfloor hprecX
  have hdet := (st6_prec_det_iff sz hsz (fun n (v : Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n)) =>
      ‖∫ ω, X n v ω ∂(sz.seqP)‖) (fun n v => (etaT (STflowE z n) (t n))⁻¹ *
      (sz.Bctl n (t n)) ^ ((o : ℝ) / 2))).1 hint
  refine (st6_prec_det_iff sz hsz _ _).2 fun τ hτ => ?_
  filter_upwards [hdet τ hτ] with n hn v
  have h1 := hn v
  have hval : ∀ ω, P.val (LWG5Data sz n (STflowE z n) (t n) ω) ![v.1, v.2] =
      (((t n) ^ P.g.nW : ℝ) : ℂ) * X n v ω := by
    intro ω
    simp only [hX]
    by_cases h : (t n) ^ P.g.nW = 0
    · have hnW : P.g.nW ≠ 0 := by
        intro h0; rw [h0, pow_zero] at h; exact one_ne_zero h
      have ht : t n = 0 := (pow_eq_zero_iff hnW).1 h
      have h0 : P.val (LWG5Data sz n (STflowE z n) (t n) ω) ![v.1, v.2] = 0 := by
        rw [ht]; exact lwExpTerm3_val_zero sz P hnW n _ ω _
      rw [h0, h]; simp
    · rw [Complex.ofReal_inv, mul_inv_cancel_left₀ (by exact_mod_cast h)]
  have hI : ∫ ω, P.val (LWG5Data sz n (STflowE z n) (t n) ω) ![v.1, v.2] ∂(sz.seqP) =
      (((t n) ^ P.g.nW : ℝ) : ℂ) * ∫ ω, X n v ω ∂(sz.seqP) := by
    simp_rw [hval]; exact integral_const_mul _ _
  rw [hI, norm_mul, Complex.norm_real, Real.norm_of_nonneg (pow_nonneg (ht0 n) _)]
  calc (t n) ^ P.g.nW * ‖∫ ω, X n v ω ∂(sz.seqP)‖
      ≤ (t n) ^ P.g.nW * (((sz.size n : ℕ) : ℝ) ^ τ * ((etaT (STflowE z n) (t n))⁻¹ *
        (sz.Bctl n (t n)) ^ ((o : ℝ) / 2))) := mul_le_mul_of_nonneg_left h1 (pow_nonneg (ht0 n) _)
    _ = _ := by ring

/-! ## 5. The consumer of `LWG5Expand'` -/

section T4pos6

variable {d : ℕ} (sz : Sizes d) (n : ℕ)

/-- **`t > 0` case of the assembly** (copy of `lwExpTerm3_T4pos` with the coefficients `m^j m̄^{j'}` of `LWG5Expand'`, `‖m^j m̄^{j'}‖ = 1`):
`‖W^d Σ K S^{(B)} 𝔼 𝓛^{(5)}‖ ≤ Λ N^{τ'} η⁻¹ (B^{5/2} + W^{-d} B²)`, `Λ = #Ls`. -/
theorem lwExpTerm6_T4pos (Lk : List ((ℕ × ℕ) × PGraph (Fin 2)))
    (hLk : ∀ q ∈ Lk, 2 ≤ q.2.g.nW ∧ (if q.2.ext 0 = q.2.ext 1 then (4 : ℤ) else 5) ≤ q.2.g.scalingOrder)
    {E t : ℝ} (hE : |E| < 2) (ht0 : 0 < t) (ht1 : t < 1) (k s : Bool) (a b : Zd d (sz.L n))
    (hexp : ∀ x y : Idx d (sz.L n) (sz.W n),
      ∫ ω, (LWG5Graph k s).val (LWG5Data sz n E t ω) ![x, y] ∂(sz.seqP) =
        (Lk.map fun q => (mE E) ^ q.1.1 * star (mE E) ^ q.1.2 *
          ∫ ω, q.2.val (LWG5Data sz n E t ω) ![x, y] ∂(sz.seqP)).sum)
    {N B η τ' : ℝ} (hN : 1 ≤ N) (hB0 : 0 < B) (hB1 : B ≤ 1) (hη0 : 0 < η)
    (hqb : ∀ q ∈ Lk, ∀ x y : Idx d (sz.L n) (sz.W n),
      ‖∫ ω, q.2.val (LWG5Data sz n E t ω) ![x, y] ∂(sz.seqP)‖ ≤
        N ^ τ' * (t ^ q.2.g.nW * η⁻¹ * B ^ ((q.2.g.scalingOrder : ℝ) / 2))) :
    ‖(((sz.W n : ℕ) : ℂ) ^ d) * ∑ a₁, ∑ a₂, ∑ a₃,
        (if k then LWExpKp sz n E t a₁ a₂ else (SB d (sz.L n) (sz.lam n) a₁ a₂ : ℂ)) *
        (SB d (sz.L n) (sz.lam n) a₂ a₃ : ℂ) *
        ∫ ω, Lloop sz n E t ![true, true, true, true, s] ![a₂, a₁, a₃, b, a] ω ∂(sz.seqP)‖ ≤
      (Lk.length : ℝ) * N ^ τ' * η⁻¹ * (B ^ ((5 : ℝ) / 2) + (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * B ^ (2 : ℝ)) := by
  classical
  set e : ℕ := if k then 1 else 2 with he
  have he2 : e ≤ 2 := by rw [he]; split_ifs <;> norm_num
  have hb := lwExpTerm3_bridge d sz n E t hE ht0 ht1 k s a b
  set X : ℂ := (((sz.W n : ℕ) : ℂ) ^ d) * ∑ a₁, ∑ a₂, ∑ a₃,
        (if k then LWExpKp sz n E t a₁ a₂ else (SB d (sz.L n) (sz.lam n) a₁ a₂ : ℂ)) *
        (SB d (sz.L n) (sz.lam n) a₂ a₃ : ℂ) *
        ∫ ω, Lloop sz n E t ![true, true, true, true, s] ![a₂, a₁, a₃, b, a] ω ∂(sz.seqP) with hXdef
  set M : ℕ := (sz.W n) ^ d with hM
  have hW0 : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hMpos : (0 : ℝ) < (M : ℝ) := by rw [hM]; push_cast; positivity
  have hMc : (((sz.W n : ℕ) : ℂ) ^ d) = (M : ℂ) := by rw [hM]; push_cast; rfl
  have hMr : (((sz.W n : ℕ) : ℝ) ^ d) = (M : ℝ) := by rw [hM]; push_cast; rfl
  have hte : (0 : ℝ) < t ^ e := pow_pos ht0 _
  have hb' : ((t : ℂ) ^ e) * X = ((((sz.W n : ℕ) : ℂ) ^ d) ^ 2)⁻¹ *
      ∑ x ∈ Finset.univ.filter (fun x => lwExpTerm2_bl d (sz.L n) (sz.W n) x = a),
        ∑ y ∈ Finset.univ.filter (fun y => lwExpTerm2_bl d (sz.L n) (sz.W n) y = b),
          ∫ ω, (LWG5Graph k s).val (LWG5Data sz n E t ω) ![x, y] ∂(sz.seqP) := hb
  have hXeq : ‖X‖ = (t ^ e)⁻¹ * ‖((((sz.W n : ℕ) : ℂ) ^ d) ^ 2)⁻¹ *
      ∑ x ∈ Finset.univ.filter (fun x => lwExpTerm2_bl d (sz.L n) (sz.W n) x = a),
        ∑ y ∈ Finset.univ.filter (fun y => lwExpTerm2_bl d (sz.L n) (sz.W n) y = b),
          ∫ ω, (LWG5Graph k s).val (LWG5Data sz n E t ω) ![x, y] ∂(sz.seqP)‖ := by
    have h1 : ‖((t : ℂ) ^ e) * X‖ = t ^ e * ‖X‖ := by
      rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg ht0.le]
    rw [hb'] at h1
    rw [h1]
    field_simp
  rw [hXeq]
  -- the pair sum
  set Gq : Idx d (sz.L n) (sz.W n) → Idx d (sz.L n) (sz.W n) → ℝ := fun x y =>
    N ^ τ' * (t ^ e * η⁻¹ * (B ^ ((5 : ℝ) / 2) + if x = y then B ^ (2 : ℝ) else 0)) with hGq
  have hpair : ∀ x y : Idx d (sz.L n) (sz.W n),
      ‖∫ ω, (LWG5Graph k s).val (LWG5Data sz n E t ω) ![x, y] ∂(sz.seqP)‖ ≤ (Lk.length : ℝ) * Gq x y := by
    intro x y
    rw [hexp]
    refine lwExpTerm3_list_norm_sum_le Lk _ _ (fun q hq => ?_)
    obtain ⟨hnW, hord⟩ := hLk q hq
    simp only [norm_mul, norm_pow, norm_star, norm_mE hE.le, one_pow, one_mul]
    exact lwExpTerm3_graph_pair_bound sz n q.2 he2 hnW hord ht0 ht1 hN hB0 hB1 hη0 E x y (hqb q hq x y)
  have hG₂ : 0 ≤ (Lk.length : ℝ) * (N ^ τ' * (t ^ e * η⁻¹ * B ^ (2 : ℝ))) := by
    have : 0 ≤ N ^ τ' := Real.rpow_nonneg (by linarith) _
    have : 0 ≤ η⁻¹ := inv_nonneg.2 hη0.le
    positivity
  have hcardA : (Finset.univ.filter (fun x => lwExpTerm2_bl d (sz.L n) (sz.W n) x = a)).card = M := by
    have h := card_Iblk d (sz.L n) (sz.W n) a
    exact h
  have hcardB : (Finset.univ.filter (fun y => lwExpTerm2_bl d (sz.L n) (sz.W n) y = b)).card = M := by
    have h := card_Iblk d (sz.L n) (sz.W n) b
    exact h
  have hsum := lwExpTerm3_pairsum (Finset.univ.filter (fun x => lwExpTerm2_bl d (sz.L n) (sz.W n) x = a))
    (Finset.univ.filter (fun y => lwExpTerm2_bl d (sz.L n) (sz.W n) y = b)) hcardA hcardB
    (fun x y => ‖∫ ω, (LWG5Graph k s).val (LWG5Data sz n E t ω) ![x, y] ∂(sz.seqP)‖)
    (G₁ := (Lk.length : ℝ) * (N ^ τ' * (t ^ e * η⁻¹ * B ^ ((5 : ℝ) / 2))))
    (G₂ := (Lk.length : ℝ) * (N ^ τ' * (t ^ e * η⁻¹ * B ^ (2 : ℝ)))) hG₂
    (fun x y => by
      refine (hpair x y).trans (le_of_eq ?_)
      simp only [hGq]
      split_ifs <;> ring)
  have hnorm : ‖((((sz.W n : ℕ) : ℂ) ^ d) ^ 2)⁻¹ *
      ∑ x ∈ Finset.univ.filter (fun x => lwExpTerm2_bl d (sz.L n) (sz.W n) x = a),
        ∑ y ∈ Finset.univ.filter (fun y => lwExpTerm2_bl d (sz.L n) (sz.W n) y = b),
          ∫ ω, (LWG5Graph k s).val (LWG5Data sz n E t ω) ![x, y] ∂(sz.seqP)‖ ≤
      ((M : ℝ) ^ 2)⁻¹ * ((M : ℝ) ^ 2 * ((Lk.length : ℝ) * (N ^ τ' * (t ^ e * η⁻¹ * B ^ ((5 : ℝ) / 2)))) +
        M * ((Lk.length : ℝ) * (N ^ τ' * (t ^ e * η⁻¹ * B ^ (2 : ℝ))))) := by
    rw [norm_mul, hMc, norm_inv, norm_pow, Complex.norm_natCast]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine (norm_sum_le _ _).trans ?_
    refine le_trans ?_ hsum
    refine Finset.sum_le_sum fun x _ => ?_
    exact norm_sum_le _ _
  calc (t ^ e)⁻¹ * ‖((((sz.W n : ℕ) : ℂ) ^ d) ^ 2)⁻¹ *
      ∑ x ∈ Finset.univ.filter (fun x => lwExpTerm2_bl d (sz.L n) (sz.W n) x = a),
        ∑ y ∈ Finset.univ.filter (fun y => lwExpTerm2_bl d (sz.L n) (sz.W n) y = b),
          ∫ ω, (LWG5Graph k s).val (LWG5Data sz n E t ω) ![x, y] ∂(sz.seqP)‖
      ≤ (t ^ e)⁻¹ * (((M : ℝ) ^ 2)⁻¹ * ((M : ℝ) ^ 2 * ((Lk.length : ℝ) * (N ^ τ' * (t ^ e * η⁻¹ * B ^ ((5 : ℝ) / 2)))) +
        M * ((Lk.length : ℝ) * (N ^ τ' * (t ^ e * η⁻¹ * B ^ (2 : ℝ)))))) :=
        mul_le_mul_of_nonneg_left hnorm (inv_nonneg.2 hte.le)
    _ = _ := by
        rw [hMr]
        field_simp

end T4pos6

/-- **The assembly of `LWExpG5'`** from the expansion pin `LWG5Expand'` and the joined bound `LwGraphPrecJoin` (copy of
`lwExpG5'_of_expand`, with the joined branch of the leaf property routed to `LwGraphPrecJoin`). -/
theorem lwExpG5'_of_expand' (d : ℕ) : LWG5Expand' d → LwGraphPrecJoin d → LWExpG5' d := by
  intro hexp hJoin hd κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hz t ht0 htz hLE hLW hLmax hLK hDec
  classical
  obtain ⟨Ls, hLs, hLexp⟩ := hexp
  obtain ⟨hA, -, ht1, hRange⟩ := RBM.Green.v3_premises_of_stFlow sz hκ hε hz htz
  obtain ⟨h𝔠, -, hsz, hbw, hWO⟩ := hA
  have hE2 : ∀ n, |STflowE z n| < 2 := st6_flowE_lt_two sz hκ hz
  have hlam : ∀ᶠ n in atTop, 0 < sz.lam n ∧ sz.lam n ≤ 𝔡⁻¹ := by
    filter_upwards [hWO] with n hn
    exact ⟨lt_of_lt_of_le (Real.rpow_pos_of_pos (by exact_mod_cast sz.W_pos n) _) hn.1, hn.2⟩
  have hB1 := st5_Bctl_le_one sz hκ hε hz htz
  refine (st6_prec_det_iff sz hsz _ _).2 fun τ hτ => ?_
  have hτ2 : 0 < τ / 2 := by positivity
  have hq : ∀ k s : Bool, ∀ q ∈ Ls k s, ∀ᶠ n in atTop, ∀ v : Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n),
      ‖∫ ω, q.2.val (LWG5Data sz n (STflowE z n) (t n) ω) ![v.1, v.2] ∂(sz.seqP)‖ ≤
        ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * ((t n) ^ q.2.g.nW * (etaT (STflowE z n) (t n))⁻¹ *
          (sz.Bctl n (t n)) ^ ((q.2.g.scalingOrder : ℝ) / 2)) := by
    intro k s q hq
    obtain ⟨hn, hm, -, ha, he, -⟩ := hLs k s q hq
    rcases he with he | hJ
    · have := lwGraphPrec1 d hd κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hz t ht0 htz hLE hLmax q.2 hn hm ha he
      exact (st6_prec_det_iff sz hsz _ _).1 this (τ / 2) hτ2
    · have := hJoin hd κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hz t ht0 htz hLE q.2 hn hJ
      exact (st6_prec_det_iff sz hsz _ _).1 this (τ / 2) hτ2
  have hq' : ∀ᶠ n in atTop, ∀ k s : Bool, ∀ q ∈ Ls k s, ∀ v : Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n),
      ‖∫ ω, q.2.val (LWG5Data sz n (STflowE z n) (t n) ω) ![v.1, v.2] ∂(sz.seqP)‖ ≤
        ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * ((t n) ^ q.2.g.nW * (etaT (STflowE z n) (t n))⁻¹ *
          (sz.Bctl n (t n)) ^ ((q.2.g.scalingOrder : ℝ) / 2)) := by
    have h1 : ∀ k s : Bool, ∀ᶠ n in atTop, ∀ q ∈ Ls k s, ∀ v : Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n),
        ‖∫ ω, q.2.val (LWG5Data sz n (STflowE z n) (t n) ω) ![v.1, v.2] ∂(sz.seqP)‖ ≤
          ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * ((t n) ^ q.2.g.nW * (etaT (STflowE z n) (t n))⁻¹ *
            (sz.Bctl n (t n)) ^ ((q.2.g.scalingOrder : ℝ) / 2)) := fun k s =>
      (Filter.eventually_all_finite (List.finite_toSet (Ls k s))).2 (hq k s)
    exact Filter.eventually_all.2 fun k => Filter.eventually_all.2 fun s => h1 k s
  set Λ : ℝ := (((Ls false false).length + (Ls false true).length + (Ls true false).length +
    (Ls true true).length : ℕ) : ℝ) with hΛ
  have hΛk : ∀ k s : Bool, ((Ls k s).length : ℝ) ≤ Λ := by
    intro k s
    rw [hΛ]
    have : (Ls k s).length ≤ (Ls false false).length + (Ls false true).length + (Ls true false).length +
        (Ls true true).length := by
      cases k <;> cases s <;> omega
    exact_mod_cast this
  have hΛ0 : 0 ≤ Λ := Nat.cast_nonneg _
  have hev1 : ∀ᶠ n in atTop, Λ * (2 + (𝔡⁻¹) ^ 2) + ((𝔡⁻¹) ^ 2 + 1) ^ ((5 : ℝ) / 2) ≤
      ((sz.size n : ℕ) : ℝ) ^ (τ / 2) :=
    ((tendsto_rpow_atTop hτ2).comp hsz).eventually_ge_atTop _
  filter_upwards [hq', hlam, hB1, hev1] with n hqn hlamn hBn hev1n
  rintro ⟨⟨⟨k, s⟩, av⟩, hg⟩
  change ‖(((sz.W n : ℕ) : ℂ) ^ d) * ∑ a₁, ∑ a₂, ∑ a₃,
        (if k then LWExpKp sz n (STflowE z n) (t n) a₁ a₂ else (SB d (sz.L n) (sz.lam n) a₁ a₂ : ℂ)) *
        (SB d (sz.L n) (sz.lam n) a₂ a₃ : ℂ) *
        ∫ ω, Lloop sz n (STflowE z n) (t n) ![true, true, true, true, s] ![a₂, a₁, a₃, av 1, av 0] ω ∂(sz.seqP)‖ ≤
    ((sz.size n : ℕ) : ℝ) ^ τ * ((etaT (STflowE z n) (t n))⁻¹ * (sz.Bctl n (t n)) ^ (5 / 2 : ℝ))
  have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
  have hB0 : 0 < sz.Bctl n (t n) := STBctl_pos sz n (ht1 n)
  have hB1' : sz.Bctl n (t n) ≤ 1 := hBn (t n) le_rfl
  have hη0 : 0 < etaT (STflowE z n) (t n) := etaT_pos (hE2 n) (ht1 n)
  have hη1 : etaT (STflowE z n) (t n) ≤ 1 := lwExpTerm3_etaT_le_one (hE2 n) (ht0 n) (ht1 n)
  have hη' : 1 ≤ (etaT (STflowE z n) (t n))⁻¹ := one_le_inv₀ hη0 |>.2 hη1
  have hW0 : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hWd : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) ^ d := by positivity
  have hWd1 : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) ^ d := one_le_pow₀ (by exact_mod_cast sz.W_pos n)
  have hBge := STBctl_ge sz n (ht0 n) (ht1 n)
  have hl2 : sz.lam n ^ 2 + 1 ≤ (𝔡⁻¹) ^ 2 + 1 := by
    have := pow_le_pow_left₀ hlamn.1.le hlamn.2 2
    linarith
  have hl0 : 0 < sz.lam n ^ 2 + 1 := by positivity
  have hWinv : (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ ((𝔡⁻¹) ^ 2 + 1) * sz.Bctl n (t n) := by
    have h1 : (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ (sz.lam n ^ 2 + 1) * sz.Bctl n (t n) := by
      have := mul_le_mul_of_nonneg_left hBge hl0.le
      calc (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ = (sz.lam n ^ 2 + 1) * ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (sz.lam n ^ 2 + 1)⁻¹) := by
            field_simp
        _ ≤ _ := this
    exact h1.trans (mul_le_mul_of_nonneg_right hl2 hB0.le)
  have hB52 : 0 ≤ sz.Bctl n (t n) ^ ((5 : ℝ) / 2) := Real.rpow_nonneg hB0.le _
  have hNτ2 : 1 ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) := Real.one_le_rpow hN1 hτ2.le
  have hNτ : ((sz.size n : ℕ) : ℝ) ^ (τ / 2) ≤ ((sz.size n : ℕ) : ℝ) ^ τ :=
    Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  by_cases ht : t n = 0
  · -- `t = 0`
    refine (lwExpTerm3_T4zero sz n (hE2 n) ht k s (av 0) (av 1)).trans ?_
    have hw1 : (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hWd1
    have hw0 : 0 < (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ := inv_pos.2 hWd
    have h3 : ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹) ^ 3 ≤ ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹) ^ ((5 : ℝ) / 2) := by
      rw [show ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹) ^ 3 = ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹) ^ ((3 : ℕ) : ℝ) from
        (Real.rpow_natCast _ 3).symm]
      exact Real.rpow_le_rpow_of_exponent_ge hw0 hw1 (by norm_num)
    have h4 : ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹) ^ ((5 : ℝ) / 2) ≤
        (((𝔡⁻¹) ^ 2 + 1) * sz.Bctl n (t n)) ^ ((5 : ℝ) / 2) :=
      Real.rpow_le_rpow hw0.le hWinv (by norm_num)
    have h5 : (((𝔡⁻¹) ^ 2 + 1) * sz.Bctl n (t n)) ^ ((5 : ℝ) / 2) =
        ((𝔡⁻¹) ^ 2 + 1) ^ ((5 : ℝ) / 2) * sz.Bctl n (t n) ^ ((5 : ℝ) / 2) :=
      Real.mul_rpow (by positivity) hB0.le
    have hC : ((𝔡⁻¹) ^ 2 + 1) ^ ((5 : ℝ) / 2) ≤ ((sz.size n : ℕ) : ℝ) ^ τ := by
      have : 0 ≤ Λ * (2 + (𝔡⁻¹) ^ 2) := by positivity
      linarith
    calc ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹) ^ 3 ≤ ((𝔡⁻¹) ^ 2 + 1) ^ ((5 : ℝ) / 2) * sz.Bctl n (t n) ^ ((5 : ℝ) / 2) :=
          h3.trans (h4.trans (le_of_eq h5))
      _ ≤ ((sz.size n : ℕ) : ℝ) ^ τ * sz.Bctl n (t n) ^ ((5 : ℝ) / 2) := by gcongr
      _ ≤ ((sz.size n : ℕ) : ℝ) ^ τ * ((etaT (STflowE z n) (t n))⁻¹ * sz.Bctl n (t n) ^ ((5 : ℝ) / 2)) := by
          gcongr
          nlinarith
  · -- `t > 0`
    have hpos : 0 < t n := lt_of_le_of_ne (ht0 n) (Ne.symm ht)
    have hLk : ∀ q ∈ Ls k s, 2 ≤ q.2.g.nW ∧ (if q.2.ext 0 = q.2.ext 1 then (4 : ℤ) else 5) ≤ q.2.g.scalingOrder :=
      fun q hq => by
        obtain ⟨-, -, hnW, -, -, hord⟩ := hLs k s q hq
        exact ⟨hnW, hord⟩
    have hmain := lwExpTerm6_T4pos sz n (Ls k s) hLk (hE2 n) hpos (ht1 n) k s (av 0) (av 1)
      (fun x y => hLexp sz n (STflowE z n) (t n) (hE2 n) hpos (ht1 n) k s x y)
      (N := ((sz.size n : ℕ) : ℝ)) (B := sz.Bctl n (t n)) (η := etaT (STflowE z n) (t n)) (τ' := τ / 2) hN1 hB0 hB1' hη0
      (fun q hq x y => hqn k s q hq (x, y))
    refine hmain.trans ?_
    set Bc : ℝ := sz.Bctl n (t n) with hBc
    set Nn : ℝ := ((sz.size n : ℕ) : ℝ) with hNn
    set η : ℝ := etaT (STflowE z n) (t n) with hη
    have hB3 : Bc * Bc ^ (2 : ℝ) ≤ Bc ^ ((5 : ℝ) / 2) := by
      have e : Bc * Bc ^ (2 : ℝ) = Bc ^ (3 : ℝ) := by
        rw [show (3 : ℝ) = 1 + 2 by norm_num, Real.rpow_add hB0, Real.rpow_one]
      rw [e]
      exact Real.rpow_le_rpow_of_exponent_ge hB0 hB1' (by norm_num)
    have hB2p : 0 ≤ Bc ^ (2 : ℝ) := Real.rpow_nonneg hB0.le _
    have hW2 : (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * Bc ^ (2 : ℝ) ≤ ((𝔡⁻¹) ^ 2 + 1) * Bc ^ ((5 : ℝ) / 2) := by
      calc (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * Bc ^ (2 : ℝ) ≤ (((𝔡⁻¹) ^ 2 + 1) * Bc) * Bc ^ (2 : ℝ) :=
            mul_le_mul_of_nonneg_right hWinv hB2p
        _ = ((𝔡⁻¹) ^ 2 + 1) * (Bc * Bc ^ (2 : ℝ)) := by ring
        _ ≤ ((𝔡⁻¹) ^ 2 + 1) * Bc ^ ((5 : ℝ) / 2) := by gcongr
    have hΛ' : ((Ls k s).length : ℝ) * (2 + (𝔡⁻¹) ^ 2) ≤ Nn ^ (τ / 2) := by
      have := hΛk k s
      have h1 : ((Ls k s).length : ℝ) * (2 + (𝔡⁻¹) ^ 2) ≤ Λ * (2 + (𝔡⁻¹) ^ 2) :=
        mul_le_mul_of_nonneg_right this (by positivity)
      have : 0 ≤ ((𝔡⁻¹) ^ 2 + 1) ^ ((5 : ℝ) / 2) := by positivity
      linarith
    have hη0' : 0 < η⁻¹ := inv_pos.2 hη0
    calc ((Ls k s).length : ℝ) * Nn ^ (τ / 2) * η⁻¹ * (Bc ^ ((5 : ℝ) / 2) + (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * Bc ^ (2 : ℝ))
        ≤ ((Ls k s).length : ℝ) * Nn ^ (τ / 2) * η⁻¹ * (Bc ^ ((5 : ℝ) / 2) + ((𝔡⁻¹) ^ 2 + 1) * Bc ^ ((5 : ℝ) / 2)) := by
          gcongr
      _ = (((Ls k s).length : ℝ) * (2 + (𝔡⁻¹) ^ 2)) * Nn ^ (τ / 2) * (η⁻¹ * Bc ^ ((5 : ℝ) / 2)) := by ring
      _ ≤ Nn ^ (τ / 2) * Nn ^ (τ / 2) * (η⁻¹ * Bc ^ ((5 : ℝ) / 2)) := by
          gcongr
      _ = Nn ^ τ * (η⁻¹ * Bc ^ ((5 : ℝ) / 2)) := by
          rw [← Real.rpow_add hN0]; congr 2; ring




/-! ## 6. The unconditional chain and the Step 6 closures -/

/-- **`LWExpG5'` unconditionally** (`I₄₂`, `J₄₂`): the expansion `lwG5Expand'_holds` and the joined bound `lwGraphPrecJoin_holds`. -/
theorem lwExpG5'_holds : ∀ d : ℕ, LWExpG5' d := fun d =>
  lwExpG5'_of_expand' d (lwG5Expand'_holds d) (lwGraphPrecJoin_holds d)

/-- **`LWCutExp` unconditionally** (one cut of `(eq:EGC)` in expectation, `(eq:ELW_term)`, `B:10-13`). -/
theorem lwCutExp_holds : ∀ d : ℕ, LWCutExp d := fun d => lwCutExp_of_G5' d (lwExpG5'_holds d)

/-- **`LWtermEXP` unconditionally** (`lem:LWterm_EXP`, `6:83-88`). -/
theorem lwTermEXP_holds : ∀ d : ℕ, LWtermEXP d := fun d => lwTermEXP_of_cut d (lwCutExp_holds d)

/-- **Step 6, regime (i)** (`6:97`): `stStep6I_of_LW` with the proved `LWtermEXP`. -/
theorem stStep6I_holds : ∀ d : ℕ, STStep6I d := fun d => stStep6I_of_LW d (lwTermEXP_holds d)

/-- **Step 6, regime (ii)** (`6:97`, `6:136-147`): `ST_step6_caseII_of_pins` with the six proved ingredients. -/
theorem stStep6II_holds : ∀ d : ℕ, STStep6II d := fun d =>
  ST_step6_caseII_of_pins (stExpLKLKHi_holds d) (lwTermEXP_holds d) (stImproveExpAver_holds d) (stExpDuhamelZ_holds d)
    (stExpIntII_holds d) (stExpWardII_holds d)

/-- **Step 6, regime (iii)** (`6:94-96`): `ST_step6_caseIII_of_pins` with the four proved ingredients. -/
theorem stStep6III_holds : ∀ d : ℕ, STStep6III d := fun d =>
  ST_step6_caseIII_of_pins (stExpLKLKHi_holds d) (lwTermEXP_holds d) (stExpDuhamelZ_holds d) (stExpIntIII_holds d)

/-! ## 7. Compiled instances (namespace `LWExpTerm6Inst`; `d = 3`, `sz0`, `z0`, `tInst`; `STLocalEntry`, `LWAvgLaw`, `STLmax`,
`STLK`, `STDecay` are other gates' pins and stay hypotheses) -/

namespace LWExpTerm6Inst

open RBM.Gauss.SizesInst RBM.Gauss.InductionDefsInst RBM.Gauss.Step34Inst RBM.Gauss.LWInst

/-- The joined graph of the preflight instance (the term `α = x`, `β = y` of `𝒢_xy`, T2265 F2):
`Σ_γ S_{γx} S_{xy} G_{xγ} G_{γy} Ḡ_{xy}` with external `x = inl 0`, `y = inl 1`, internal `γ = inr 0`; solid `G_{xγ}, G_{γy}, Ḡ_{xy}`,
waved `S_{γx}, S_{xy}`, `×`-dotted `(x, γ), (γ, y), (x, y)`.  One molecule, `n_M = 0`, `ord = 3 + 2 (2 - 1) = 5`. -/
def lwExpTerm6_instGraph : LGraph (Fin 2) (Fin 1) where
  solid := [SEdge.mk true false (Sum.inl 0) (Sum.inr 0), SEdge.mk true false (Sum.inr 0) (Sum.inl 1),
    SEdge.mk false false (Sum.inl 0) (Sum.inl 1)]
  waved := [WEdge.mk false true (Sum.inr 0) (Sum.inl 0), WEdge.mk false false (Sum.inl 0) (Sum.inl 1)]
  dotted := [DEdge.mk false (Sum.inl 0) (Sum.inr 0), DEdge.mk false (Sum.inr 0) (Sum.inl 1),
    DEdge.mk false (Sum.inl 0) (Sum.inl 1)]
  coeff := 1

theorem lwExpTerm6_instGraph_normal : lwExpTerm6_instGraph.Normal := by decide

theorem lwExpTerm6_instGraph_nM : lwExpTerm6_instGraph.nM = 0 := by decide

theorem lwExpTerm6_instGraph_joined : LWJoined lwExpTerm6_instGraph.pack := by
  refine ⟨by decide, ?_, lwExpTerm6_instGraph_nM⟩
  change lwExpTerm6_instGraph.molOf (Sum.inl 0) = lwExpTerm6_instGraph.molOf (Sum.inl 1)
  rw [LGraph.molOf_eq_iff]
  decide

/-- The counters of the instance graph: `n_S = 3`, `n_W = 2`, `n_V = 1`, `ord = 5`. -/
theorem lwExpTerm6_instGraph_counters :
    lwExpTerm6_instGraph.nS = 3 ∧ lwExpTerm6_instGraph.nW = 2 ∧ lwExpTerm6_instGraph.nV = 1 ∧
      lwExpTerm6_instGraph.scalingOrder = 5 := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  simp [LGraph.scalingOrder, LGraph.counters, ord, LGraph.nS, LGraph.nW, LGraph.nV, lwExpTerm6_instGraph]

/-- **Instance of `lwGraphPrecJoin_holds`** at `d = 3`, `sz0`, `z0`, `tInst ≡ 1/16`, the joined graph `lwExpTerm6_instGraph`
(`Normal`, `LWJoined` by `decide`); `STLocalEntry` is the pin of the gate of `(Gt_bound)`. -/
theorem lwExpTerm6_inst_join (hLE : STLocalEntry sz0 (STflowE z0) tInst) :
    Prec sz0 (U := fun n => Idx 3 (sz0.L n) (sz0.W n) × Idx 3 (sz0.L n) (sz0.W n))
      (fun n p _ => ‖∫ ω, (lwExpTerm6_instGraph.pack).val (LWG5Data sz0 n (STflowE z0 n) (tInst n) ω) ![p.1, p.2] ∂(sz0.seqP)‖)
      (fun n _ _ => (tInst n) ^ (lwExpTerm6_instGraph.pack).g.nW * (etaT (STflowE z0 n) (tInst n))⁻¹ *
        (sz0.Bctl n (tInst n)) ^ (((lwExpTerm6_instGraph.pack).g.scalingOrder : ℝ) / 2)) :=
  lwGraphPrecJoin_holds 3 le_rfl (1 / 10) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 6) sz0 z0 flow_z0
    tInst tInst_range.1 tInst_range.2 hLE (lwExpTerm6_instGraph.pack) lwExpTerm6_instGraph_normal
    lwExpTerm6_instGraph_joined

/-- **Instance of `lwExpG5'_of_expand'`**: the proved expansion `lwG5Expand'_holds 3` and the proved joined bound give
`LWExpG5'` at the instance data. -/
theorem lwExpTerm6_inst_expand (hLE : STLocalEntry sz0 (STflowE z0) tInst)
    (hLW : LWAvgLaw sz0 (STflowE z0) tInst) (hLmax : STLmax sz0 (STflowE z0) tInst)
    (hLK : STLK sz0 (STflowE z0) tInst) (hDec : STDecay sz0 (STflowE z0) tInst) :
    Prec sz0 (U := fun n => {_p : (Bool × Bool) × (Fin 2 → Zd 3 (sz0.L n)) //
        sz0.lam n ^ 2 / ((sz0.L n : ℕ) : ℝ) ^ 3 ≤ 1 - tInst n})
      (fun n p _ => ‖(((sz0.W n : ℕ) : ℂ) ^ 3) * ∑ a₁, ∑ a₂, ∑ a₃,
          (if p.1.1.1 then LWExpKp sz0 n (STflowE z0 n) (tInst n) a₁ a₂
            else (SB 3 (sz0.L n) (sz0.lam n) a₁ a₂ : ℂ)) *
          (SB 3 (sz0.L n) (sz0.lam n) a₂ a₃ : ℂ) *
          ∫ ω, Lloop sz0 n (STflowE z0 n) (tInst n) ![true, true, true, true, p.1.1.2]
            ![a₂, a₁, a₃, p.1.2 1, p.1.2 0] ω ∂(sz0.seqP)‖)
      (fun n _ _ => (etaT (STflowE z0 n) (tInst n))⁻¹ * (sz0.Bctl n (tInst n)) ^ (5 / 2 : ℝ)) :=
  lwExpG5'_of_expand' 3 (lwG5Expand'_holds 3) (lwGraphPrecJoin_holds 3) le_rfl (1 / 10) (1 / 10) (1 / 10) (by norm_num)
    (by norm_num) (by norm_num) (1 / 6) sz0 z0 flow_z0 tInst tInst_range.1 tInst_range.2 hLE hLW hLmax hLK hDec

/-- **Instance of `lwExpG5'_holds`** at the instance data. -/
theorem lwExpTerm6_inst_G5 (hLE : STLocalEntry sz0 (STflowE z0) tInst)
    (hLW : LWAvgLaw sz0 (STflowE z0) tInst) (hLmax : STLmax sz0 (STflowE z0) tInst)
    (hLK : STLK sz0 (STflowE z0) tInst) (hDec : STDecay sz0 (STflowE z0) tInst) :
    Prec sz0 (U := fun n => {_p : (Bool × Bool) × (Fin 2 → Zd 3 (sz0.L n)) //
        sz0.lam n ^ 2 / ((sz0.L n : ℕ) : ℝ) ^ 3 ≤ 1 - tInst n})
      (fun n p _ => ‖(((sz0.W n : ℕ) : ℂ) ^ 3) * ∑ a₁, ∑ a₂, ∑ a₃,
          (if p.1.1.1 then LWExpKp sz0 n (STflowE z0 n) (tInst n) a₁ a₂
            else (SB 3 (sz0.L n) (sz0.lam n) a₁ a₂ : ℂ)) *
          (SB 3 (sz0.L n) (sz0.lam n) a₂ a₃ : ℂ) *
          ∫ ω, Lloop sz0 n (STflowE z0 n) (tInst n) ![true, true, true, true, p.1.1.2]
            ![a₂, a₁, a₃, p.1.2 1, p.1.2 0] ω ∂(sz0.seqP)‖)
      (fun n _ _ => (etaT (STflowE z0 n) (tInst n))⁻¹ * (sz0.Bctl n (tInst n)) ^ (5 / 2 : ℝ)) :=
  lwExpG5'_holds 3 le_rfl (1 / 10) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 6) sz0 z0 flow_z0 tInst
    tInst_range.1 tInst_range.2 hLE hLW hLmax hLK hDec

/-- **Instance of `lwCutExp_holds`** at the instance data. -/
theorem lwExpTerm6_inst_cut (hLE : STLocalEntry sz0 (STflowE z0) tInst)
    (hLW : LWAvgLaw sz0 (STflowE z0) tInst) (hLmax : STLmax sz0 (STflowE z0) tInst)
    (hLK : STLK sz0 (STflowE z0) tInst) (hDec : STDecay sz0 (STflowE z0) tInst) :
    Prec sz0 (U := fun n => {_p : (Bool × Bool) × (Zd 3 (sz0.L n) × Zd 3 (sz0.L n)) //
        sz0.lam n ^ 2 / ((sz0.L n : ℕ) : ℝ) ^ 3 ≤ 1 - tInst n})
      (fun n p _ => ‖∫ ω, LWcut sz0 n (STflowE z0 n) (tInst n) p.1.1.1 p.1.1.2 p.1.2.1 p.1.2.2 ω ∂(sz0.seqP)‖)
      (fun n _ _ => (1 - tInst n)⁻¹ * (sz0.Bctl n (tInst n)) ^ (5 / 2 : ℝ)) :=
  lwCutExp_holds 3 le_rfl (1 / 10) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 6) sz0 z0 flow_z0 tInst
    tInst_range.1 tInst_range.2 hLE hLW hLmax hLK hDec

/-- **Instance of `lwTermEXP_holds`** (into the merged `inst_LWtermEXP`). -/
theorem lwExpTerm6_inst_term (hLE : STLocalEntry sz0 (STflowE z0) tInst)
    (hLW : LWAvgLaw sz0 (STflowE z0) tInst) (hLmax : STLmax sz0 (STflowE z0) tInst)
    (hLK : STLK sz0 (STflowE z0) tInst) (hDec : STDecay sz0 (STflowE z0) tInst) :
    Prec sz0 (U := fun n => {_p : (Fin 2 → Bool) × (Fin 2 → Zd 3 (sz0.L n)) //
        sz0.lam n ^ 2 / ((sz0.L n : ℕ) : ℝ) ^ 3 ≤ 1 - tInst n})
      (fun n p _ => ‖∫ ω, LWE sz0 n (STflowE z0 n) (tInst n) p.1.1 p.1.2 ω ∂(sz0.seqP)‖)
      (fun n _ _ => (1 - tInst n)⁻¹ * (sz0.Bctl n (tInst n)) ^ (5 / 2 : ℝ)) :=
  inst_LWtermEXP (lwTermEXP_holds 3) hLE hLW hLmax hLK hDec

/-- **Instance of `stStep6I_holds`** at the data of regime (i) `(szB, zB, 7/8, 15/16)`: the constant `𝔠_d`, the stochastic premises
as hypotheses, the conclusion `(Eq:Gtlp_exp_flow)`. -/
theorem lwExpTerm6_inst_step6I :
    RBM.Gauss.Step6Inst.InstIng6Concl (fun sz E s t => STStep6Concl sz E s t) szB zB (fun _ => 7 / 8) (fun _ => 15 / 16) :=
  RBM.Gauss.Step6Inst.inst_step6I (stStep6I_holds 3)

/-- **Instance of `stStep6II_holds`** at the data of regime (ii) `(szB, zB, 15/16, 31/32)`. -/
theorem lwExpTerm6_inst_step6II :
    RBM.Gauss.Step6Inst.InstIng6Concl (fun sz E s t => STStep6Concl sz E s t) szB zB (fun _ => 15 / 16) (fun _ => 31 / 32) :=
  RBM.Gauss.Step6Inst.inst_step6II (stStep6II_holds 3)

/-- **Instance of `stStep6III_holds`** at the data of regime (iii) `(sz0, z0, 0, 1/16)`. -/
theorem lwExpTerm6_inst_step6III :
    RBM.Gauss.Step6Inst.InstIng6Concl (fun sz E s t => STStep6Concl sz E s t) sz0 z0 sInst tInst :=
  RBM.Gauss.Step6Inst.inst_step6III (stStep6III_holds 3)

end LWExpTerm6Inst

end RBM.Gauss.Sizes

end
