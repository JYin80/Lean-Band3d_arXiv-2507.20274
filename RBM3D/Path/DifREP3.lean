/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Path.DifREP2
import RBM3D.Induction.ZeroModeCalc
import RBM3D.Induction.GridDuhamelN

/-!
# `STGridRepN`, part 3: the `Q^{(A)} ∘ 𝒰`-weighted martingale tail (`d ≥ 3`)

Ticket T2200 (ST2-13b, stochastic layer ST-2).  Paper: arXiv:2507.20274, `3_5`: `lem:DIfREP`,
`(alu9_STime)` (`3_5:218-245`: the Burkholder-Davis-Gundy step of `[YY_25]` Lemma 5.5 at a
**fixed** endpoint `t`, replaced by the Azuma + Doob steps of `DifREP2`, DECISIONS §7, paper-delta
D90) and the zero-mode-removed form `Q^{(A)} ∘ 𝒰 ∘ dℰ^M` of `(sahwNQ_smalleta)`, `(sahwNQ2)`
(`3_5:1898-1915`).  The pin is clause (iv) of `STGridRepNAt`: `GridRepWTailNAt d m` of the merged
`Path/DifREP1.lean` (T2168, `3df1812`), the `𝒰`-weighted martingale tail of `difRepMartN`, uniform
in `k ≤ K` with the `k`-dependent kernel `𝒰_{u_j,u_k}`.  Here it is proved for the kernel `Q^{(A)}
∘ 𝒰 = zeroModeSet Q ∘ UN` and every `Q ⊆ ⟦m⟧` (DECISIONS §59 O3), at every loop length `m ≥ 2`;
`GridRepWTailNAt` is the case `Q = ∅`.  With `stGridRepN_of_tails` and `gridRepTailN_holds`
(`DifREP2`) this makes `STGridRepN d` unconditional for `d ≥ 3` (`C₀ = m + 9`).  RBM1D and RBM2D
have no counterpart of the uniform-endpoint weighted tail (RBM2D has only the fixed-endpoint
stopped form).

## The route (no source in RBM1D, RBM2D or Mathlib)

The kernel `𝒰_{u_j,u_k}` depends on the endpoint `k`, so `Σ_{j<k} 𝒰_{u_j,u_k} ξ_j` is not a
martingale in `k`, and `K` is unbounded, so there is no union over `k`.  A coarse **time** grid
`v_p = s + p (t - s)/P`, `P = ⌈N^{C'}⌉` (`C' = 4m + D + 6`, independent of `K`) replaces it.  For
each `(p, a')` the sums `W^p_k(a') = Σ_{j<k} (Q 𝒰_{u_j,v_p} ξ_j)_{a'}` are martingales in `k` with
deterministic weights `κ^{p,a'}_j = ∏_i uKerQ σ (u_j, v_p)(a'_i, ·_i)`, switched off for `u_j >
v_p`.  The first-chaos part `Z` is handled by the peeling `difRep2_peel` (the weighted conditional
mgf `difRepTail_condMGF_Z`; the proxy is moved from `u_{j+1}` to `u_j` and from `(u_j, v_p)` to
`(u_j, u_k)`).  The second-order part `Y` is handled by Doob's `L²` maximal inequality with
`j`-dependent weights (`difRep3_Y_tail`: the **variant** of step (e) of the ticket, Doob per `(p,
a')` with the weights of the `Z` part, no factorisation `T_w P_j`; `CK = 9m + 3D + 22`).  For `k ≤
K` and `p = ⌈kP/K⌉` one has `u_k ≤ v_p ≤ u_k + N^{-C'}`, and the **exact transfer** `Σ_{j<k} Q
𝒰_{u_j,u_k} ξ_j = 𝒰_{v_p,u_k} W^p_k` (target 4: the semigroup of `𝒰` and the commutation of `Q`),
with `𝒰_{v_p,u_k} = id + O(N^{1-C'})` entrywise on the tensors (`difRep3_norm_UN_sub_le`), closes
the pathwise inclusion (`difRep3_pathwise`).  The union is over `(p, a')`, that is `(P + 1) N^m`
events, free of `K` (`difRep3_core`).

## Main results (namespace `RBM.Ind`)

* §1 the vocabulary `uKerQ` (the slot kernel of `Q^{(A)} ∘ 𝒰`), `STeeUQM` (the zero-mode-removed
  weighted quadratic variation loop), `GridRepWTailQNAt` (clause (iv) for `Q^{(A)} ∘ 𝒰`).
* §2 targets 1-4: **`STeeUQM_empty`**, **`gridRepWTailN_of_Q`**, **`zeroModeSet_UN_eq_uKerQ`**,
  **`difRep3_UN_transfer`**.
* §3-§9 private helpers (prefix `difRep3_`): the conjugation identity and the proxy as a weighted
  quadratic form, row sums of `uKerQ`, the product difference `difRep3_sum_prod_sub_prod`, the
  kernel transfer (f1) and the proxy transfer (f2), the coarse grid, the weighted Doob tail, the
  `Z` increments, the pathwise inclusion, the numerical budgets and the tail at one size index.
* §10 targets 5-7: **`gridRepWTailQN_holds`** (every `d`, `m ≥ 2`, `Q`),
  **`gridRepWTailN_holds`**, **`stGridRepN_holds`** (`3 ≤ d`, only through `stGridRepN_of_tails`).
* §11 compiled nonempty instances at `d = 3` (namespace `RBM.Ind.DifREP3Inst`).

Copies (private, prefix `difRep3_`; sources are the merged RBM3D files):
`Induction/NQGood1.lean:151-196` (`691566a`; RBM2D `StoppedEndDefs.lean:690`, `c9a24cf`, as
there), `Induction/GridDuhamelN.lean:75-79, 91-104, 242` (`2ebee73`), `Path/DifREP2.lean:658-748,
923-954, 1265, 1308, 2098` (`76b840e`), and the weighted form of `difRepTail_Y_tail`
(`:1777-1908`).  `difRep3_Z_tail`, `difRep3_core` and `difRep3_eventually_Z` follow the pattern of
`difRepTail_Z_tail`, `difRepTail_core` and `difRepTail_eventually_Z` (`:1546-1766`, `:1951-2088`,
`:2112`).

`3 ≤ d` is used nowhere in targets 1-6 (`3 ≤ L` is `sz.three_le_L`; `L^d ≤ N` needs only `W ≥ 1`);
target 7 needs it only through `stGridRepN_of_tails` (DECISIONS §36).  Every unpinned helper is
`private` with the prefix `difRep3_`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

noncomputable section

namespace RBM.Ind

open MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.Loop RBM.Gauss RBM.Gauss.Sizes RBM.Path
  RBM.Gauss.LinearForm
open scoped NNReal ENNReal

/-! ## 1. The vocabulary -/

/-- Vocabulary 1, `uKerQ`: **the slot kernel of `Q^{(A)} ∘ 𝒰_{v,w,σ}`** at slot `i`: `(I − L^{-d}J)(1 − v μ_i S)Θ_{wμ_i}` for
`i ∈ Q`, `(1 − v μ_i S)Θ_{wμ_i}` otherwise, `μ_i = m(σ_i)m(σ_{i+1})` (`cycProd`); the kernel family of `zeroModeSet_tensorKer`
applied to `UN_eq_tensorKer`.  (`Q` is the zero-mode set `Q^{(A)}`, not the `𝒬`-process of S3-14.) -/
noncomputable def uKerQ (d L : ℕ) [NeZero L] (g E : ℝ) {m : ℕ} (Q : Finset (Fin m)) (σ : Fin m → Bool)
    (v w : ℝ) (i : Fin m) : Matrix (Zd d L) (Zd d L) ℂ :=
  if i ∈ Q then projMat d L * uKer d L g (cycProd (fun i => mSigma E (σ i)) i) v w
  else uKer d L g (cycProd (fun i => mSigma E (σ i)) i) v w

/-- Vocabulary 2, `STeeUQM`: **the zero-mode-removed weighted quadratic-variation loop**
`(((Q^{(A)}∘𝒰_{v,w,σ}) ⊗ (Q^{(A)}∘𝒰_{v,w,σ̄})) ∘ (ℰ⊗ℰ)^{M,(m)}_{v,σ})_{a,a}` for a fine matrix `H` (the paper's
`(sahwNQ2)`, `3_5:1908`, with `lem:DIfREP`); `STeeUM` is the case `Q = ∅` (target 1). -/
noncomputable def STeeUQM {d : ℕ} (sz : Sizes d) (n : ℕ) (E v w : ℝ)
    (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    {m : ℕ} (Q : Finset (Fin m)) (σ : Fin m → Bool) (a : Fin m → Zd d (sz.L n)) : ℂ :=
  ∑ b : Fin m → Zd d (sz.L n), ∑ b' : Fin m → Zd d (sz.L n),
    (∏ i, uKerQ d (sz.L n) (sz.lam n) E Q σ v w i (a i) (b i)) *
      (∏ i, uKerQ d (sz.L n) (sz.lam n) E Q (fun i => !σ i) v w i (a i) (b' i)) *
        sz.STeeM n E v H σ b b'

/-- Vocabulary 3, `GridRepWTailQNAt`: **clause (iv) of `STGridRepNAt` for `Q^{(A)} ∘ 𝒰`** (`difRepMartN`, every zero-mode
set `Q`): the `Q^{(A)}∘𝒰`-weighted martingale tail, for all `k ≤ K` at once.  `GridRepWTailNAt d m` is the case
`Q = ∅` (target 2). -/
def GridRepWTailQNAt (d m : ℕ) (Q : Finset (Fin m)) : Prop :=
  ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z →
      ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n ≤ t n) → (∀ n, t n ≤ lemT (z n)) →
        ∀ D : ℝ, 0 < D → ∃ CK : ℝ, 0 ≤ CK ∧
          ∀ K : ℕ → ℕ, (∀ n, K n ≠ 0) → (∀ᶠ n in atTop, ((sz.size n : ℕ) : ℝ) ^ CK ≤ K n) →
            ∀ ε' : ℝ, 0 < ε' → ∀ᶠ n in atTop, ∀ i : (Fin m → Bool) × (Fin m → Zd d (sz.L n)),
              pathP sz {ω | ∃ k, k ≤ K n ∧
                ((sz.size n : ℕ) : ℝ) ^ ε' *
                    (∑ j ∈ Finset.range k, gridStep s t K n *
                      ‖STeeUQM sz n (STflowE z n) (gridTime s t K n j) (gridTime s t K n k)
                        (pathH sz s t K n j ω) Q i.1 i.2‖ + ((sz.size n : ℕ) : ℝ) ^ (-D)) ^
                        (1 / 2 : ℝ) <
                  ‖∑ j ∈ Finset.range k,
                    zeroModeSet d (sz.L n) Q
                      (UN d (sz.L n) (sz.lam n) (fun i' => mSigma (STflowE z n) (i.1 i'))
                        (gridTime s t K n j) (gridTime s t K n k)
                        (fun b => difRepMartN sz (STflowE z) s t K n (i.1, b) (j + 1) ω -
                          difRepMartN sz (STflowE z) s t K n (i.1, b) j ω)) i.2‖} ≤
                ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-D))

/-! ## 2. Targets 1-4: the algebra -/

/-- Target 1, `STeeUQM_empty`: without zero-mode removal the proxy is the merged `STeeUM`. -/
theorem STeeUQM_empty :
    ∀ {d : ℕ} (sz : Sizes d) (n : ℕ) (E v w : ℝ)
      (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
      {m : ℕ} (σ : Fin m → Bool) (a : Fin m → Zd d (sz.L n)),
      STeeUQM sz n E v w H (∅ : Finset (Fin m)) σ a = sz.STeeUM n E v w H σ a := by
  intro d sz n E v w H m σ a
  simp only [STeeUQM, STeeUM, uKerQ, Finset.notMem_empty, ite_false]

/-- Target 2, `gridRepWTailN_of_Q`: the case `Q = ∅` is the merged clause (iv) (`zeroModeSet_empty`, target 1). -/
theorem gridRepWTailN_of_Q :
    ∀ d m : ℕ, GridRepWTailQNAt d m (∅ : Finset (Fin m)) → GridRepWTailNAt d m := by
  intro d m h κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hz s t hs hst htT D hD
  obtain ⟨CK, hCK, h'⟩ := h κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hz s t hs hst htT D hD
  refine ⟨CK, hCK, fun K hK0 hKN ε' hε' => ?_⟩
  filter_upwards [h' K hK0 hKN ε' hε'] with n hn i
  have := hn i
  simpa only [zeroModeSet_empty, STeeUQM_empty] using this

/-- Target 3, `zeroModeSet_UN_eq_uKerQ`: `Q^{(A)} ∘ 𝒰_{v,w,σ}` is the tensor kernel of `uKerQ` (no hypothesis). -/
theorem zeroModeSet_UN_eq_uKerQ :
    ∀ {d L : ℕ} [NeZero L] (g E : ℝ) {m : ℕ} (Q : Finset (Fin m)) (σ : Fin m → Bool) (v w : ℝ)
      (A : (Fin m → Zd d L) → ℂ),
      zeroModeSet d L Q (UN d L g (fun i => mSigma E (σ i)) v w A) =
        tensorKer d L (uKerQ d L g E Q σ v w) A := by
  intro d L _ g E m Q σ v w A
  rw [UN_eq_tensorKer, zeroModeSet_tensorKer]
  rfl

/-- Target 4, `difRep3_UN_transfer`: **the transfer identity** (semigroup of `𝒰` + `Q^{(A)}` commutes with `𝒰`):
`Σ_{j<k} Q∘𝒰_{u_j,w} A_j = 𝒰_{v,w} (Σ_{j<k} Q∘𝒰_{u_j,v} A_j)` for `0 ≤ v, w < 1`, `|E| ≤ 2`, the `u_j` arbitrary. -/
theorem difRep3_UN_transfer :
    ∀ {d L : ℕ} [NeZero L] (g : ℝ), 3 ≤ L → ∀ {E : ℝ}, |E| ≤ 2 →
      ∀ {m : ℕ} (σ : Fin m → Bool) (Q : Finset (Fin m)) {v w : ℝ}, 0 ≤ v → v < 1 → 0 ≤ w → w < 1 →
        ∀ (k : ℕ) (u : ℕ → ℝ) (A : ℕ → (Fin m → Zd d L) → ℂ),
          ∑ j ∈ Finset.range k, zeroModeSet d L Q (UN d L g (fun i => mSigma E (σ i)) (u j) w (A j)) =
            UN d L g (fun i => mSigma E (σ i)) v w
              (∑ j ∈ Finset.range k,
                zeroModeSet d L Q (UN d L g (fun i => mSigma E (σ i)) (u j) v (A j))) := by
  intro d L _ g hL E hE m σ Q v w hv0 hv1 hw0 hw1 k u A
  have hsum : ∀ (s : Finset ℕ) (F : ℕ → (Fin m → Zd d L) → ℂ),
      UN d L g (fun i => mSigma E (σ i)) v w (∑ j ∈ s, F j) =
        ∑ j ∈ s, UN d L g (fun i => mSigma E (σ i)) v w (F j) := fun s F => by
    have := map_sum (GridDuhamelN_UgenHom d L g E σ v w) F s
    simp only [GridDuhamelN_UgenHom_apply] at this
    exact this
  rw [hsum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hc : UN d L g (fun i => mSigma E (σ i)) v w (UN d L g (fun i => mSigma E (σ i)) (u j) v (A j)) =
      UN d L g (fun i => mSigma E (σ i)) (u j) w (A j) :=
    GridDuhamelN_Ugen_comp hL hE σ hv0 hv1 hw0 hw1 (A j)
  rw [← hc]
  exact zeroModeSet_UN hL (fun i => norm_mul_mSigma_lt_one hE hw0 hw1 (σ i) (σ (finRotate m i))) Q _


/-! ## 3. Kernel algebra (private helpers, prefix `difRep3_`)

Copies of the private `nqGood1_SB_conj`, `nqGood1_Theta_star`, `nqGood1_conj_uKer`, `nqGood1_mSigma_not`
(`Induction/NQGood1.lean:151-196`, RBM3D `691566a`; RBM2D `StoppedEndDefs.lean:690` provenance as there) and of
the slot condition of `GridDuhamelN_Ugen_comp` (`Induction/GridDuhamelN.lean:75-79`, `2ebee73`). -/

section KernelAlg

open scoped Matrix.Norms.Operator

variable {d L : ℕ} [NeZero L] {g : ℝ}

private theorem difRep3_SB_conj (a b : Zd d L) :
    (starRingEnd ℂ) (SB d L g a b) = SB d L g a b := by
  rw [SB_apply, sbKernel_eq_ofReal, Complex.conj_ofReal]

/-- `Θ_{conj ξ} = conj Θ_ξ` entrywise. -/
private theorem difRep3_Theta_star (hL : 3 ≤ L) {ξ : ℂ} (hξ : ‖ξ‖ < 1) (a b : Zd d L) :
    Theta d L g (star ξ) a b = star (Theta d L g ξ a b) := by
  have hξ' : ‖star ξ‖ < 1 := by rwa [norm_star]
  have hmul : (Theta d L g ξ).map (starRingEnd ℂ) * (1 - star ξ • SB d L g) = 1 := by
    have h := congrArg (fun A : Matrix (Zd d L) (Zd d L) ℂ => A.map (starRingEnd ℂ))
      (Theta_mul_of_three_le (d := d) (g := g) hL hξ)
    simp only [Matrix.map_mul] at h
    have h1 : (1 - ξ • SB d L g).map (starRingEnd ℂ) = 1 - star ξ • SB d L g := by
      ext x y
      simp only [Matrix.map_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
        smul_eq_mul, map_sub, map_mul, difRep3_SB_conj]
      split_ifs <;> simp
    rw [h1] at h
    rw [h]
    ext x y
    simp only [Matrix.map_apply, Matrix.one_apply]
    split_ifs <;> simp
  have key := eq_Theta_of_mul d L g (norm_SB d L g hL) hξ' hmul
  have := congrFun (congrFun key a) b
  simpa using this.symm

/-- `conj (uKer μ v w) = uKer (conj μ) v w` for real `v, w` (`S^{(B)}` is real). -/
private theorem difRep3_conj_uKer (hL : 3 ≤ L) {μ : ℂ} {v w : ℝ} (hξ : ‖(w : ℂ) * μ‖ < 1)
    (x y : Zd d L) :
    (starRingEnd ℂ) (uKer d L g μ v w x y) = uKer d L g ((starRingEnd ℂ) μ) v w x y := by
  have hT := difRep3_Theta_star (d := d) (L := L) (g := g) hL hξ
  have hw : star ((w : ℂ) * μ) = (w : ℂ) * (starRingEnd ℂ) μ := by
    simp [Complex.conj_ofReal]
  rw [hw] at hT
  unfold uKer
  simp only [Matrix.mul_apply, map_sum, map_mul]
  refine Finset.sum_congr rfl fun z _ => ?_
  congr 1
  · simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, map_sub,
      map_mul, difRep3_SB_conj, Complex.conj_ofReal]
    split_ifs <;> simp
  · exact (hT z y).symm ▸ rfl

private theorem difRep3_mSigma_not (E : ℝ) (s : Bool) :
    mSigma E (!s) = (starRingEnd ℂ) (mSigma E s) := by
  cases s <;> simp [mSigma]

/-- The slot condition `‖v m(σ_i) m(σ_{i+1})‖ < 1` for `0 ≤ v < 1`, `|E| ≤ 2`. -/
private theorem difRep3_norm_slot_lt_one {E : ℝ} (hE : |E| ≤ 2) {k : ℕ} (σ : Fin k → Bool)
    (i : Fin k) {v : ℝ} (hv0 : 0 ≤ v) (hv1 : v < 1) :
    ‖(v : ℂ) * cycProd (fun i => mSigma E (σ i)) i‖ < 1 :=
  norm_mul_mSigma_lt_one hE hv0 hv1 (σ i) (σ (finRotate k i))

/-- `I - L^{-d} J` has real entries. -/
private theorem difRep3_conj_projMat (x y : Zd d L) :
    (starRingEnd ℂ) (projMat d L x y) = projMat d L x y := by
  simp only [projMat, Matrix.sub_apply, Matrix.one_apply, Matrix.of_apply, map_sub, map_inv₀,
    map_pow, Complex.conj_natCast]
  split_ifs <;> simp

/-- **Conjugation of the `Q`-kernel**: `conj (uKerQ σ v w) = uKerQ σ̄ v w` entrywise for `0 ≤ w < 1`, `|E| ≤ 2`
(`m(σ̄) = conj m(σ)`, `S^{(B)}` and `I - L^{-d} J` real). -/
private theorem difRep3_conj_uKerQ (hL : 3 ≤ L) {E : ℝ} (hE : |E| ≤ 2) {m : ℕ} (Q : Finset (Fin m))
    (σ : Fin m → Bool) {v w : ℝ} (hw0 : 0 ≤ w) (hw1 : w < 1) (i : Fin m) (x y : Zd d L) :
    (starRingEnd ℂ) (uKerQ d L g E Q σ v w i x y) = uKerQ d L g E Q (fun i => !σ i) v w i x y := by
  have hn := difRep3_norm_slot_lt_one hE σ i hw0 hw1
  have key : ∀ x y : Zd d L, (starRingEnd ℂ) (uKer d L g (cycProd (fun i => mSigma E (σ i)) i) v w x y) =
      uKer d L g (cycProd (fun i => mSigma E (!σ i)) i) v w x y := by
    intro x y
    rw [difRep3_conj_uKer hL hn]
    congr 1
    simp only [cycProd, map_mul, ← difRep3_mSigma_not]
  unfold uKerQ
  split_ifs with hi
  · simp only [Matrix.mul_apply, map_sum, map_mul, difRep3_conj_projMat, key]
  · exact key x y


/-- Row sums of the `Q`-kernel: `Σ_y |uKerQ σ v w i x y| ≤ 2 (1 - v)/(1 - w)` for `0 ≤ v ≤ w < 1`
(`norm_uKer_le`, `norm_projMat_le`). -/
private theorem difRep3_sum_norm_uKerQ_le (hL : 3 ≤ L) {E : ℝ} (hE : |E| ≤ 2) {m : ℕ}
    (Q : Finset (Fin m)) (σ : Fin m → Bool) {v w : ℝ} (hv : 0 ≤ v) (hvw : v ≤ w) (hw : w < 1)
    (i : Fin m) (x : Zd d L) :
    ∑ y, ‖uKerQ d L g E Q σ v w i x y‖ ≤ 2 * ((1 - v) / (1 - w)) := by
  have hμ : ‖cycProd (fun i => mSigma E (σ i)) i‖ = 1 :=
    norm_cycProd (fun i => norm_mSigma hE (σ i)) i
  have hu := norm_uKer_le (d := d) (L := L) (g := g) hL hv hvw hw hμ
  have h0 : 0 ≤ (1 - v) / (1 - w) := div_nonneg (by linarith) (by linarith)
  refine (sum_norm_row_le (uKerQ d L g E Q σ v w i) x).trans ?_
  unfold uKerQ
  split_ifs
  · calc ‖projMat d L * uKer d L g (cycProd (fun i => mSigma E (σ i)) i) v w‖
        ≤ ‖projMat d L‖ * ‖uKer d L g (cycProd (fun i => mSigma E (σ i)) i) v w‖ :=
          norm_mul_le _ _
      _ ≤ 2 * ((1 - v) / (1 - w)) := mul_le_mul norm_projMat_le hu (norm_nonneg _) (by norm_num)
  · linarith

end KernelAlg

section SumProd

/-- `Σ_b ∏_i G_i(b_i) = ∏_i Σ_x G_i(x)` (`Finset.prod_univ_sum`). -/
private theorem difRep3_sum_prod_eq {X : Type*} [Fintype X] {m : ℕ} (G : Fin m → X → ℝ) :
    ∑ b : Fin m → X, ∏ i, G i (b i) = ∏ i, ∑ x, G i x := by
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]

/-- `Σ_b |∏_i G_i(b_i)| ≤ R^m` when every row `Σ_x |G_i(x)| ≤ R`. -/
private theorem difRep3_sum_norm_prod_le {X : Type*} [Fintype X] {m : ℕ} (G : Fin m → X → ℂ)
    {R : ℝ} (hG : ∀ i, ∑ x, ‖G i x‖ ≤ R) :
    ∑ b : Fin m → X, ‖∏ i, G i (b i)‖ ≤ R ^ m := by
  simp only [norm_prod]
  rw [difRep3_sum_prod_eq (fun i x => ‖G i x‖)]
  calc ∏ i, ∑ x, ‖G i x‖ ≤ ∏ _i : Fin m, R :=
        Finset.prod_le_prod₀ (fun i _ => Finset.sum_nonneg fun x _ => norm_nonneg _) fun i _ => hG i
    _ = R ^ m := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- `‖Σ_{x,y} P_x P'_y T_{xy}‖ ≤ (Σ|P|)(Σ|P'|) M` for `|T_{xy}| ≤ M`. -/
private theorem difRep3_norm_double_sum_le {X : Type*} [Fintype X] (P P' : X → ℂ)
    (T : X → X → ℂ) {R R' M : ℝ} (hM : 0 ≤ M) (hP : ∑ x, ‖P x‖ ≤ R) (hP' : ∑ x, ‖P' x‖ ≤ R')
    (hT : ∀ x y, ‖T x y‖ ≤ M) :
    ‖∑ x, ∑ y, P x * P' y * T x y‖ ≤ R * R' * M := by
  calc ‖∑ x, ∑ y, P x * P' y * T x y‖ ≤ ∑ x, ∑ y, ‖P x‖ * ‖P' y‖ * M := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun x _ =>
          (norm_sum_le _ _).trans (Finset.sum_le_sum fun y _ => ?_))
        rw [norm_mul, norm_mul]
        exact mul_le_mul_of_nonneg_left (hT x y) (by positivity)
    _ = (∑ x, ‖P x‖) * (∑ y, ‖P' y‖) * M := by
        rw [Finset.sum_mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.sum_mul]
    _ ≤ R * R' * M := by
        have h1 : 0 ≤ ∑ x, ‖P x‖ := Finset.sum_nonneg fun x _ => norm_nonneg _
        have h2 : 0 ≤ ∑ y, ‖P' y‖ := Finset.sum_nonneg fun x _ => norm_nonneg _
        have h3 : 0 ≤ R := h1.trans hP
        gcongr

/-- **The difference of two tensor products of kernels**: for rows with `Σ_x |G_i(x)|, Σ_x |G'_i(x)| ≤ R`
and `Σ_x |G_i(x) - G'_i(x)| ≤ θ`,
`Σ_b |∏_i G_i(b_i) - ∏_i G'_i(b_i)| ≤ m θ R^{m-1}` (induction on the number of slots through
`Fin.consEquiv`, `a Π - a' Π' = (a - a') Π' + a (Π - Π')`). -/
private theorem difRep3_sum_prod_sub_prod {X : Type*} [Fintype X] (R θ : ℝ) (hR : 0 ≤ R)
    (hθ : 0 ≤ θ) :
    ∀ (m : ℕ) (G G' : Fin m → X → ℂ), (∀ i, ∑ x, ‖G i x‖ ≤ R) → (∀ i, ∑ x, ‖G' i x‖ ≤ R) →
      (∀ i, ∑ x, ‖G i x - G' i x‖ ≤ θ) →
      ∑ b : Fin m → X, ‖∏ i, G i (b i) - ∏ i, G' i (b i)‖ ≤ (m : ℝ) * θ * R ^ (m - 1) := by
  intro m
  induction m with
  | zero =>
    intro G G' _ _ _
    simp
  | succ m ih =>
    intro G G' hG hG' hD
    rw [← Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (m + 1) => X)), Fintype.sum_prod_type]
    have hcons : ∀ (x : X) (b' : Fin m → X),
        (Fin.consEquiv (fun _ : Fin (m + 1) => X)) (x, b') = (Fin.cons x b' : Fin (m + 1) → X) :=
      fun x b' => rfl
    simp only [hcons, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
    set P1 : (Fin m → X) → ℂ := fun b' => ∏ i : Fin m, G i.succ (b' i) with hP1
    set P2 : (Fin m → X) → ℂ := fun b' => ∏ i : Fin m, G' i.succ (b' i) with hP2
    have hstep : ∀ (x : X) (b' : Fin m → X),
        ‖G 0 x * P1 b' - G' 0 x * P2 b'‖ ≤
          ‖G 0 x - G' 0 x‖ * ‖P2 b'‖ + ‖G 0 x‖ * ‖P1 b' - P2 b'‖ := by
      intro x b'
      have : G 0 x * P1 b' - G' 0 x * P2 b' =
          (G 0 x - G' 0 x) * P2 b' + G 0 x * (P1 b' - P2 b') := by ring
      rw [this]
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, norm_mul]
    have hP2sum : ∑ b' : Fin m → X, ‖P2 b'‖ ≤ R ^ m :=
      difRep3_sum_norm_prod_le (fun i : Fin m => G' i.succ) (fun i => hG' i.succ)
    have hdiff := ih (fun i => G i.succ) (fun i => G' i.succ) (fun i => hG i.succ)
      (fun i => hG' i.succ) (fun i => hD i.succ)
    have hsum : ∑ x : X, ∑ b' : Fin m → X, ‖G 0 x * P1 b' - G' 0 x * P2 b'‖ ≤
        (∑ x, ‖G 0 x - G' 0 x‖) * (∑ b', ‖P2 b'‖) +
          (∑ x, ‖G 0 x‖) * ∑ b' : Fin m → X, ‖P1 b' - P2 b'‖ := by
      calc ∑ x : X, ∑ b' : Fin m → X, ‖G 0 x * P1 b' - G' 0 x * P2 b'‖
          ≤ ∑ x : X, ∑ b' : Fin m → X, (‖G 0 x - G' 0 x‖ * ‖P2 b'‖ + ‖G 0 x‖ * ‖P1 b' - P2 b'‖) :=
            Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun b' _ => hstep x b'
        _ = _ := by
            simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
    refine hsum.trans ?_
    have h1 : (∑ x, ‖G 0 x - G' 0 x‖) * (∑ b', ‖P2 b'‖) ≤ θ * R ^ m :=
      mul_le_mul (hD 0) hP2sum (Finset.sum_nonneg fun _ _ => norm_nonneg _) hθ
    have h2 : (∑ x, ‖G 0 x‖) * ∑ b' : Fin m → X, ‖P1 b' - P2 b'‖ ≤
        R * ((m : ℝ) * θ * R ^ (m - 1)) :=
      mul_le_mul (hG 0) hdiff (Finset.sum_nonneg fun _ _ => norm_nonneg _) hR
    refine (add_le_add h1 h2).trans ?_
    rcases m with _ | m
    · simp
    · have : R * ((((m + 1 : ℕ)) : ℝ) * θ * R ^ (m + 1 - 1)) = (m + 1 : ℝ) * θ * R ^ (m + 1) := by
        simp only [Nat.add_sub_cancel]
        push_cast
        ring
      rw [this]
      simp only [Nat.add_sub_cancel]
      push_cast
      nlinarith [mul_nonneg hθ (pow_nonneg hR (m + 1))]

end SumProd

section Transfer

open scoped Matrix.Norms.Operator

variable {d L : ℕ} [NeZero L] {g : ℝ}

/-- The identity kernel: `tensorKer 1 A = A` (the computation of `GridDuhamelN_Ugen_self`,
`Induction/GridDuhamelN.lean:91-104`, `2ebee73`). -/
private theorem difRep3_tensorKer_one {m : ℕ} (A : (Fin m → Zd d L) → ℂ) :
    tensorKer d L (fun _ => (1 : Matrix (Zd d L) (Zd d L) ℂ)) A = A := by
  funext a
  simp only [tensorKer, Matrix.one_apply]
  rw [Finset.sum_eq_single a]
  · simp
  · intro b _ hb
    have : ¬ ∀ i, a i = b i := fun h => hb (funext h).symm
    simp [Fintype.prod_boole, this]
  · intro h; exact absurd (Finset.mem_univ a) h

/-- `Σ_y |(uKer μ v w - 1)(x,y)| ≤ |w - v| (1 - w)⁻¹` for `‖μ‖ = 1`, `0 ≤ w < 1`, no order between
`v` and `w` (`uKer_eq_one_add`, `norm_Theta_le`). -/
private theorem difRep3_sum_norm_uKer_sub_one (hL : 3 ≤ L) {μ : ℂ} (hμ : ‖μ‖ = 1) {v w : ℝ}
    (hw0 : 0 ≤ w) (hw1 : w < 1) (x : Zd d L) :
    ∑ y, ‖uKer d L g μ v w x y - (1 : Matrix (Zd d L) (Zd d L) ℂ) x y‖ ≤ |w - v| * (1 - w)⁻¹ := by
  have hξ : ‖(w : ℂ) * μ‖ < 1 := norm_t_mul_lt_one hw0 hw1 hμ
  have hu := uKer_eq_one_add (d := d) (L := L) (g := g) (s := v) hL hξ
  have hΘ := norm_Theta_le (d := d) (L := L) (g := g) hL hw0 hw1 hμ
  have hentry : ∀ y, uKer d L g μ v w x y - (1 : Matrix (Zd d L) (Zd d L) ℂ) x y =
      ((((w : ℂ) - v) * μ) • (SB d L g * Theta d L g ((w : ℂ) * μ))) x y := by
    intro y
    rw [hu]
    simp
  simp only [hentry]
  refine (sum_norm_row_le _ x).trans ?_
  have hc : ‖((w : ℂ) - v) * μ‖ = |w - v| := by
    rw [norm_mul, hμ, mul_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  calc ‖(((w : ℂ) - v) * μ) • (SB d L g * Theta d L g ((w : ℂ) * μ))‖
      ≤ ‖((w : ℂ) - v) * μ‖ * (‖SB d L g‖ * ‖Theta d L g ((w : ℂ) * μ)‖) :=
        (norm_smul_le _ _).trans (mul_le_mul_of_nonneg_left (norm_mul_le _ _) (norm_nonneg _))
    _ = |w - v| * ‖Theta d L g ((w : ℂ) * μ)‖ := by rw [hc, norm_SB d L g hL, one_mul]
    _ ≤ |w - v| * (1 - w)⁻¹ := mul_le_mul_of_nonneg_left hΘ (abs_nonneg _)

/-- **(f1), the kernel transfer** `𝒰_{v,w} A ≈ A`: for `0 ≤ w < 1`, `|E| ≤ 2` and `|w - v| (1 - w)⁻¹ ≤ ε₀`,
`|(𝒰_{v,w} A)_a - A_a| ≤ m ε₀ (1 + ε₀)^{m-1} ‖A‖_∞` (entrywise product difference
`difRep3_sum_prod_sub_prod` with `G_i = uKer_i(a_i, ·)`, `G'_i = δ_{a_i}`; no order between `v` and `w`). -/
private theorem difRep3_norm_UN_sub_le (hL : 3 ≤ L) {E : ℝ} (hE : |E| ≤ 2) {m : ℕ}
    (σ : Fin m → Bool) {v w : ℝ} (hw0 : 0 ≤ w) (hw1 : w < 1) {ε₀ : ℝ}
    (hε : |w - v| * (1 - w)⁻¹ ≤ ε₀) (A : (Fin m → Zd d L) → ℂ) (a : Fin m → Zd d L) :
    ‖UN d L g (fun i => mSigma E (σ i)) v w A a - A a‖ ≤ (m : ℝ) * ε₀ * (1 + ε₀) ^ (m - 1) * ‖A‖ := by
  have h1w : 0 < 1 - w := by linarith
  have hε0 : 0 ≤ ε₀ := (mul_nonneg (abs_nonneg _) (inv_nonneg.2 h1w.le)).trans hε
  set G : Fin m → Zd d L → ℂ := fun i y =>
    uKer d L g (cycProd (fun i => mSigma E (σ i)) i) v w (a i) y with hGdef
  set G' : Fin m → Zd d L → ℂ := fun i y => (1 : Matrix (Zd d L) (Zd d L) ℂ) (a i) y with hG'def
  have hD : ∀ i, ∑ y, ‖G i y - G' i y‖ ≤ ε₀ := fun i =>
    (difRep3_sum_norm_uKer_sub_one hL (norm_cycProd (fun i => norm_mSigma hE (σ i)) i) hw0 hw1
      (a i)).trans hε
  have hG'sum : ∀ i, ∑ y, ‖G' i y‖ = 1 := by
    intro i
    simp only [hG'def, Matrix.one_apply]
    rw [Finset.sum_eq_single (a i)]
    · simp
    · intro b _ hb
      simp [Ne.symm hb]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hG' : ∀ i, ∑ y, ‖G' i y‖ ≤ 1 + ε₀ := fun i => by rw [hG'sum i]; linarith
  have hG : ∀ i, ∑ y, ‖G i y‖ ≤ 1 + ε₀ := fun i => by
    calc ∑ y, ‖G i y‖ ≤ ∑ y, (‖G' i y‖ + ‖G i y - G' i y‖) :=
          Finset.sum_le_sum fun y _ => by
            have := norm_add_le (G' i y) (G i y - G' i y)
            simpa using this
      _ = ∑ y, ‖G' i y‖ + ∑ y, ‖G i y - G' i y‖ := Finset.sum_add_distrib
      _ ≤ 1 + ε₀ := by rw [hG'sum i]; exact add_le_add le_rfl (hD i)
  have hmain := difRep3_sum_prod_sub_prod (1 + ε₀) ε₀ (by linarith) hε0 m G G' hG hG' hD
  have hid : UN d L g (fun i => mSigma E (σ i)) v w A a - A a =
      ∑ b : Fin m → Zd d L, (∏ i, G i (b i) - ∏ i, G' i (b i)) * A b := by
    have h1 : tensorKer d L (fun _ => (1 : Matrix (Zd d L) (Zd d L) ℂ)) A a = A a :=
      congrFun (difRep3_tensorKer_one A) a
    have h2 : UN d L g (fun i => mSigma E (σ i)) v w A a = ∑ b : Fin m → Zd d L, (∏ i, G i (b i)) * A b := rfl
    have h3 : tensorKer d L (fun _ => (1 : Matrix (Zd d L) (Zd d L) ℂ)) A a =
        ∑ b : Fin m → Zd d L, (∏ i, G' i (b i)) * A b := rfl
    rw [h2, ← h1, h3, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun b _ => by ring
  rw [hid]
  calc ‖∑ b : Fin m → Zd d L, (∏ i, G i (b i) - ∏ i, G' i (b i)) * A b‖
      ≤ ∑ b : Fin m → Zd d L, ‖(∏ i, G i (b i) - ∏ i, G' i (b i)) * A b‖ := norm_sum_le _ _
    _ ≤ ∑ b : Fin m → Zd d L, ‖∏ i, G i (b i) - ∏ i, G' i (b i)‖ * ‖A‖ := by
        refine Finset.sum_le_sum fun b _ => ?_
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (norm_le_pi_norm A b) (norm_nonneg _)
    _ = (∑ b : Fin m → Zd d L, ‖∏ i, G i (b i) - ∏ i, G' i (b i)‖) * ‖A‖ := by rw [Finset.sum_mul]
    _ ≤ (m : ℝ) * ε₀ * (1 + ε₀) ^ (m - 1) * ‖A‖ :=
        mul_le_mul_of_nonneg_right hmain (norm_nonneg _)

/-- One row of the `Q`-kernel: `Σ_y |uKerQ σ v w i x y| ≤ 32 N` when `(1 - w)⁻¹ ≤ 16 N`, `0 ≤ v ≤ w < 1`. -/
private theorem difRep3_sum_norm_uKerQ_le_N (hL : 3 ≤ L) {E : ℝ} (hE : |E| ≤ 2) {m : ℕ}
    (Q : Finset (Fin m)) (σ : Fin m → Bool) {v w : ℝ} (hv : 0 ≤ v) (hvw : v ≤ w) (hw : w < 1)
    {N : ℝ} (hN : (1 - w)⁻¹ ≤ 16 * N) (i : Fin m) (x : Zd d L) :
    ∑ y, ‖uKerQ d L g E Q σ v w i x y‖ ≤ 32 * N := by
  refine (difRep3_sum_norm_uKerQ_le hL hE Q σ hv hvw hw i x).trans ?_
  have h1w : 0 < 1 - w := by linarith
  have : (1 - v) / (1 - w) ≤ (1 - w)⁻¹ := by
    rw [div_eq_mul_inv]
    exact mul_le_of_le_one_left (inv_nonneg.2 h1w.le) (by linarith)
  linarith

/-- The sum of the `Q`-kernel rows is at most `(32 N)^m` when `(1 - w)⁻¹ ≤ 16 N`, `0 ≤ v ≤ w < 1`. -/
private theorem difRep3_sum_norm_kappa_le (hL : 3 ≤ L) {E : ℝ} (hE : |E| ≤ 2) {m : ℕ}
    (Q : Finset (Fin m)) (σ : Fin m → Bool) {v w : ℝ} (hv : 0 ≤ v) (hvw : v ≤ w) (hw : w < 1)
    {N : ℝ} (hN : (1 - w)⁻¹ ≤ 16 * N) (a : Fin m → Zd d L) :
    ∑ b : Fin m → Zd d L, ‖∏ i, uKerQ d L g E Q σ v w i (a i) (b i)‖ ≤ (32 * N) ^ m :=
  difRep3_sum_norm_prod_le (fun i y => uKerQ d L g E Q σ v w i (a i) y) (R := 32 * N) fun i =>
    difRep3_sum_norm_uKerQ_le_N hL hE Q σ hv hvw hw hN i (a i)

/-- Row sums of the difference of two `Q`-kernels at times `w₁ ≤ w₂`: `≤ 4 (16 N)² (w₂ - w₁)`
(`Theta_sub_Theta`, `norm_Theta_le`, `‖1 - u μ S‖ ≤ 2`, `‖I - L^{-d}J‖ ≤ 2`). -/
private theorem difRep3_sum_norm_uKerQ_sub_le (hL : 3 ≤ L) {E : ℝ} (hE : |E| ≤ 2) {m : ℕ}
    (Q : Finset (Fin m)) (σ : Fin m → Bool) {u w₁ w₂ : ℝ} (hu0 : 0 ≤ u) (hu : u ≤ w₁)
    (hw12 : w₁ ≤ w₂) (hw2 : w₂ < 1) {N : ℝ} (h16₁ : (1 - w₁)⁻¹ ≤ 16 * N)
    (h16₂ : (1 - w₂)⁻¹ ≤ 16 * N) (i : Fin m) (x : Zd d L) :
    ∑ y, ‖uKerQ d L g E Q σ u w₂ i x y - uKerQ d L g E Q σ u w₁ i x y‖ ≤
      4 * (16 * N) ^ 2 * (w₂ - w₁) := by
  set μ : ℂ := cycProd (fun i => mSigma E (σ i)) i with hμdef
  have hμ : ‖μ‖ = 1 := norm_cycProd (fun i => norm_mSigma hE (σ i)) i
  have hw1 : w₁ < 1 := hw12.trans_lt hw2
  have hw10 : 0 ≤ w₁ := hu0.trans hu
  have hw20 : 0 ≤ w₂ := hw10.trans hw12
  have hξ₁ : ‖(w₁ : ℂ) * μ‖ < 1 := norm_t_mul_lt_one hw10 hw1 hμ
  have hξ₂ : ‖(w₂ : ℂ) * μ‖ < 1 := norm_t_mul_lt_one hw20 hw2 hμ
  have hΘ₁ := norm_Theta_le (d := d) (L := L) (g := g) hL hw10 hw1 hμ
  have hΘ₂ := norm_Theta_le (d := d) (L := L) (g := g) hL hw20 hw2 hμ
  have hN0 : 0 ≤ 16 * N := (inv_nonneg.2 (by linarith : (0 : ℝ) ≤ 1 - w₁)).trans h16₁
  have hΘ₁' : ‖Theta d L g ((w₁ : ℂ) * μ)‖ ≤ 16 * N := hΘ₁.trans h16₁
  have hΘ₂' : ‖Theta d L g ((w₂ : ℂ) * μ)‖ ≤ 16 * N := hΘ₂.trans h16₂
  have hsub := Theta_sub_Theta d L g (norm_SB d L g hL) hξ₁ hξ₂
  have hc : ‖(w₂ : ℂ) * μ - (w₁ : ℂ) * μ‖ = w₂ - w₁ := by
    have : (w₂ : ℂ) * μ - (w₁ : ℂ) * μ = ((w₂ - w₁ : ℝ) : ℂ) * μ := by push_cast; ring
    rw [this, norm_mul, hμ, mul_one, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
  -- the difference of the two `uKer`
  have hU : uKer d L g μ u w₂ - uKer d L g μ u w₁ =
      (1 - ((u : ℂ) * μ) • SB d L g) *
        (((w₂ : ℂ) * μ - (w₁ : ℂ) * μ) •
          (Theta d L g ((w₂ : ℂ) * μ) * SB d L g * Theta d L g ((w₁ : ℂ) * μ))) := by
    unfold uKer
    rw [← Matrix.mul_sub, hsub]
  have hP : ‖(1 - ((u : ℂ) * μ) • SB d L g : Matrix (Zd d L) (Zd d L) ℂ)‖ ≤ 2 := by
    have h1 : ‖((u : ℂ) * μ) • SB d L g‖ ≤ u := by
      refine (norm_smul_le _ _).trans ?_
      rw [norm_mul, hμ, mul_one, Complex.norm_real, Real.norm_of_nonneg hu0, norm_SB d L g hL,
        mul_one]
    calc ‖(1 - ((u : ℂ) * μ) • SB d L g : Matrix (Zd d L) (Zd d L) ℂ)‖
        ≤ ‖(1 : Matrix (Zd d L) (Zd d L) ℂ)‖ + ‖((u : ℂ) * μ) • SB d L g‖ := norm_sub_le _ _
      _ ≤ 1 + u := by rw [norm_one]; exact add_le_add le_rfl h1
      _ ≤ 2 := by linarith
  have hD : ‖uKer d L g μ u w₂ - uKer d L g μ u w₁‖ ≤ 2 * ((w₂ - w₁) * (16 * N) ^ 2) := by
    rw [hU]
    refine (norm_mul_le _ _).trans ?_
    have hT : ‖((w₂ : ℂ) * μ - (w₁ : ℂ) * μ) •
        (Theta d L g ((w₂ : ℂ) * μ) * SB d L g * Theta d L g ((w₁ : ℂ) * μ))‖ ≤
        (w₂ - w₁) * (16 * N) ^ 2 := by
      refine (norm_smul_le _ _).trans ?_
      rw [hc]
      refine mul_le_mul_of_nonneg_left ?_ (by linarith)
      calc ‖Theta d L g ((w₂ : ℂ) * μ) * SB d L g * Theta d L g ((w₁ : ℂ) * μ)‖
          ≤ ‖Theta d L g ((w₂ : ℂ) * μ) * SB d L g‖ * ‖Theta d L g ((w₁ : ℂ) * μ)‖ :=
            norm_mul_le _ _
        _ ≤ (‖Theta d L g ((w₂ : ℂ) * μ)‖ * ‖SB d L g‖) * ‖Theta d L g ((w₁ : ℂ) * μ)‖ :=
            mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
        _ ≤ ((16 * N) * 1) * (16 * N) := by
            rw [norm_SB d L g hL]
            gcongr
        _ = (16 * N) ^ 2 := by ring
    exact mul_le_mul hP hT (norm_nonneg _) (by norm_num)
  have hmat : ∑ y, ‖uKerQ d L g E Q σ u w₂ i x y - uKerQ d L g E Q σ u w₁ i x y‖ ≤
      ‖uKerQ d L g E Q σ u w₂ i - uKerQ d L g E Q σ u w₁ i‖ := by
    simpa only [Matrix.sub_apply] using sum_norm_row_le
      (uKerQ d L g E Q σ u w₂ i - uKerQ d L g E Q σ u w₁ i) x
  refine hmat.trans ?_
  have hwk : 0 ≤ (w₂ - w₁) * (16 * N) ^ 2 := mul_nonneg (by linarith) (by positivity)
  unfold uKerQ
  split_ifs
  · rw [← Matrix.mul_sub]
    calc ‖projMat d L * (uKer d L g μ u w₂ - uKer d L g μ u w₁)‖
        ≤ ‖projMat d L‖ * ‖uKer d L g μ u w₂ - uKer d L g μ u w₁‖ := norm_mul_le _ _
      _ ≤ 2 * (2 * ((w₂ - w₁) * (16 * N) ^ 2)) :=
          mul_le_mul norm_projMat_le hD (norm_nonneg _) (by norm_num)
      _ = 4 * (16 * N) ^ 2 * (w₂ - w₁) := by ring
  · calc ‖uKer d L g μ u w₂ - uKer d L g μ u w₁‖ ≤ 2 * ((w₂ - w₁) * (16 * N) ^ 2) := hD
      _ ≤ 4 * (16 * N) ^ 2 * (w₂ - w₁) := by nlinarith

end Transfer

section STee

open scoped Matrix.Norms.Operator

variable {d : ℕ} (sz : Sizes d)

/-- The constant of the proxy transfer (f2): `‖STeeUQM_{u,w₂} - STeeUQM_{u,w₁}‖ ≤ c₃(N, m) (w₂ - w₁)`,
`c₃ = 2 (m θ₁ R^{m-1}) R^m M_ee` with `θ₁ = 4 (16 N)²`, `R = 32 N`, `M_ee = m N (16 N)^{2m+2}`
(`c₃ ≤ c N^{4m+4}`). -/
private def difRep3_c3 (N : ℝ) (m : ℕ) : ℝ :=
  2 * ((m : ℝ) * (4 * (16 * N) ^ 2) * (32 * N) ^ (m - 1)) * (32 * N) ^ m *
    ((m : ℝ) * N * (16 * N) ^ (2 * m + 2))

/-- **(β), the proxy is the weighted quadratic form**: for `0 ≤ w < 1`, `|E| ≤ 2`,
`STeeUQM_{v,w}(H)_{Q,σ,a} = Σ_{b,b'} κ_b conj(κ_{b'}) (𝓔⊗𝓔)_v(H)_{σ,b,b'}` with
`κ_b = ∏_i uKerQ σ v w i (a_i, b_i)` (`difRep3_conj_uKerQ`; the `Q`-analogue of `qvFormN_eq_re_UgenPairN`). -/
private theorem difRep3_STeeUQM_eq (n : ℕ) {E : ℝ} (hE : |E| ≤ 2) (v : ℝ) {w : ℝ} (hw0 : 0 ≤ w)
    (hw1 : w < 1) (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) {m : ℕ}
    (Q : Finset (Fin m)) (σ : Fin m → Bool) (a : Fin m → Zd d (sz.L n)) :
    STeeUQM sz n E v w H Q σ a =
      ∑ b : Fin m → Zd d (sz.L n), ∑ b' : Fin m → Zd d (sz.L n),
        (∏ i, uKerQ d (sz.L n) (sz.lam n) E Q σ v w i (a i) (b i)) *
          (starRingEnd ℂ) (∏ i, uKerQ d (sz.L n) (sz.lam n) E Q σ v w i (a i) (b' i)) *
            sz.STeeM n E v H σ b b' := by
  unfold STeeUQM
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun b' _ => ?_
  have h : (starRingEnd ℂ) (∏ i, uKerQ d (sz.L n) (sz.lam n) E Q σ v w i (a i) (b' i)) =
      ∏ i, uKerQ d (sz.L n) (sz.lam n) E Q (fun i => !σ i) v w i (a i) (b' i) := by
    rw [map_prod]
    exact Finset.prod_congr rfl fun i _ =>
      difRep3_conj_uKerQ (sz.three_le_L n) hE Q σ hw0 hw1 i (a i) (b' i)
  rw [h]

/-- The crude bound of the proxy: `|STeeUQM_{u,w}(H)| ≤ (32 N)^{2m} · m N (16 N)^{2m+2}` for `0 ≤ u ≤ w < 1`,
`(1 - w)⁻¹ ≤ 16 N`, `η_u ≥ 1/(16 N)` (`difRep3_sum_norm_kappa_le` for `σ` and `σ̄`,
`difRep2_norm_STeeM_le_N`). -/
private theorem difRep3_norm_STeeUQM_le (n : ℕ) {E u w : ℝ} (hE : |E| < 2) (hu0 : 0 ≤ u)
    (huw : u ≤ w) (hw1 : w < 1) (hw16 : (1 - w)⁻¹ ≤ 16 * ((sz.size n : ℕ) : ℝ))
    (hη : 1 / (16 * ((sz.size n : ℕ) : ℝ)) ≤ etaT E u)
    {H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ} (hH : H.IsHermitian)
    {m : ℕ} (Q : Finset (Fin m)) (σ : Fin m → Bool) (a : Fin m → Zd d (sz.L n)) :
    ‖STeeUQM sz n E u w H Q σ a‖ ≤
      ((32 * ((sz.size n : ℕ) : ℝ)) ^ m * (32 * ((sz.size n : ℕ) : ℝ)) ^ m) *
        ((m : ℝ) * ((sz.size n : ℕ) : ℝ) * (16 * ((sz.size n : ℕ) : ℝ)) ^ (2 * m + 2)) := by
  unfold STeeUQM
  have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
  exact difRep3_norm_double_sum_le _ _ _ (by positivity)
    (difRep3_sum_norm_kappa_le (sz.three_le_L n) hE.le Q σ hu0 huw hw1 hw16 a)
    (difRep3_sum_norm_kappa_le (sz.three_le_L n) hE.le Q (fun i => !σ i) hu0 huw hw1 hw16 a)
    fun b b' => difRep2_norm_STeeM_le_N sz n hE (huw.trans_lt hw1) hH hη σ b b'

/-- **(f2), the proxy transfer** `v_p → u_k`: for `0 ≤ u ≤ w₁ ≤ w₂ < 1`, `(1 - w_i)⁻¹ ≤ 16 N` and `η_u ≥ 1/(16 N)`,
`|STeeUQM_{u,w₂}(H) - STeeUQM_{u,w₁}(H)| ≤ c₃(N, m) (w₂ - w₁)` (`difRep3_sum_norm_uKerQ_sub_le` and the
product difference `difRep3_sum_prod_sub_prod` on both kernel products). -/
private theorem difRep3_norm_STeeUQM_sub_le (n : ℕ) {E u w₁ w₂ : ℝ} (hE : |E| < 2) (hu0 : 0 ≤ u)
    (hu : u ≤ w₁) (hw12 : w₁ ≤ w₂) (hw2 : w₂ < 1)
    (h16₁ : (1 - w₁)⁻¹ ≤ 16 * ((sz.size n : ℕ) : ℝ))
    (h16₂ : (1 - w₂)⁻¹ ≤ 16 * ((sz.size n : ℕ) : ℝ))
    (hη : 1 / (16 * ((sz.size n : ℕ) : ℝ)) ≤ etaT E u)
    {H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ} (hH : H.IsHermitian)
    {m : ℕ} (Q : Finset (Fin m)) (σ : Fin m → Bool) (a : Fin m → Zd d (sz.L n)) :
    ‖STeeUQM sz n E u w₂ H Q σ a - STeeUQM sz n E u w₁ H Q σ a‖ ≤
      difRep3_c3 ((sz.size n : ℕ) : ℝ) m * (w₂ - w₁) := by
  set N : ℝ := ((sz.size n : ℕ) : ℝ) with hN
  have hN1 : (1 : ℝ) ≤ N := by rw [hN]; exact_mod_cast sz.one_le_size n
  have hw1 : w₁ < 1 := hw12.trans_lt hw2
  have hEE : |E| ≤ 2 := hE.le
  set Mee : ℝ := (m : ℝ) * N * (16 * N) ^ (2 * m + 2) with hMee
  have hMee0 : 0 ≤ Mee := by positivity
  have hθ0 : 0 ≤ 4 * (16 * N) ^ 2 * (w₂ - w₁) := mul_nonneg (by positivity) (by linarith)
  set θ : ℝ := 4 * (16 * N) ^ 2 * (w₂ - w₁) with hθ
  set R : ℝ := 32 * N with hR
  have hR0 : 0 ≤ R := by positivity
  set T : (Fin m → Zd d (sz.L n)) → (Fin m → Zd d (sz.L n)) → ℂ :=
    fun b b' => sz.STeeM n E u H σ b b' with hT
  have hT' : ∀ b b', ‖T b b'‖ ≤ Mee := fun b b' =>
    difRep2_norm_STeeM_le_N sz n hE (hu.trans_lt hw1) hH hη σ b b'
  -- the four products
  set P₂ : (Fin m → Zd d (sz.L n)) → ℂ := fun b =>
    ∏ i, uKerQ d (sz.L n) (sz.lam n) E Q σ u w₂ i (a i) (b i) with hP₂
  set P₁ : (Fin m → Zd d (sz.L n)) → ℂ := fun b =>
    ∏ i, uKerQ d (sz.L n) (sz.lam n) E Q σ u w₁ i (a i) (b i) with hP₁
  set Q₂ : (Fin m → Zd d (sz.L n)) → ℂ := fun b =>
    ∏ i, uKerQ d (sz.L n) (sz.lam n) E Q (fun i => !σ i) u w₂ i (a i) (b i) with hQ₂
  set Q₁ : (Fin m → Zd d (sz.L n)) → ℂ := fun b =>
    ∏ i, uKerQ d (sz.L n) (sz.lam n) E Q (fun i => !σ i) u w₁ i (a i) (b i) with hQ₁
  have hS : ∀ (σ' : Fin m → Bool) {w : ℝ}, u ≤ w → w < 1 → (1 - w)⁻¹ ≤ 16 * N →
      ∑ b : Fin m → Zd d (sz.L n), ‖∏ i, uKerQ d (sz.L n) (sz.lam n) E Q σ' u w i (a i) (b i)‖ ≤
        R ^ m := fun σ' w huw hw1 hw16 =>
    difRep3_sum_norm_kappa_le (sz.three_le_L n) hEE Q σ' hu0 huw hw1 hw16 a
  have hdiff : ∀ (σ' : Fin m → Bool),
      ∑ b : Fin m → Zd d (sz.L n),
        ‖∏ i, uKerQ d (sz.L n) (sz.lam n) E Q σ' u w₂ i (a i) (b i) -
          ∏ i, uKerQ d (sz.L n) (sz.lam n) E Q σ' u w₁ i (a i) (b i)‖ ≤
        (m : ℝ) * θ * R ^ (m - 1) := fun σ' =>
    difRep3_sum_prod_sub_prod R θ hR0 hθ0 m
      (fun i y => uKerQ d (sz.L n) (sz.lam n) E Q σ' u w₂ i (a i) y)
      (fun i y => uKerQ d (sz.L n) (sz.lam n) E Q σ' u w₁ i (a i) y)
      (fun i => difRep3_sum_norm_uKerQ_le_N (sz.three_le_L n) hEE Q σ' hu0 (hu.trans hw12) hw2
        h16₂ i (a i))
      (fun i => difRep3_sum_norm_uKerQ_le_N (sz.three_le_L n) hEE Q σ' hu0 hu hw1 h16₁ i (a i))
      (fun i => difRep3_sum_norm_uKerQ_sub_le (sz.three_le_L n) hEE Q σ' hu0 hu hw12 hw2 h16₁
        h16₂ i (a i))
  have hsplit : STeeUQM sz n E u w₂ H Q σ a - STeeUQM sz n E u w₁ H Q σ a =
      ∑ b : Fin m → Zd d (sz.L n), ∑ b' : Fin m → Zd d (sz.L n), (P₂ b - P₁ b) * Q₂ b' * T b b' +
        ∑ b : Fin m → Zd d (sz.L n), ∑ b' : Fin m → Zd d (sz.L n),
          P₁ b * (Q₂ b' - Q₁ b') * T b b' := by
    unfold STeeUQM
    rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b' _ => ?_
    simp only [hP₂, hP₁, hQ₂, hQ₁, hT]
    ring
  rw [hsplit]
  refine (norm_add_le _ _).trans ?_
  have h1 := difRep3_norm_double_sum_le (fun b => P₂ b - P₁ b) Q₂ T hMee0 (hdiff σ)
    (hS (fun i => !σ i) (hu.trans hw12) hw2 h16₂) hT'
  have h2 := difRep3_norm_double_sum_le P₁ (fun b => Q₂ b - Q₁ b) T hMee0 (hS σ hu hw1 h16₁)
    (hdiff (fun i => !σ i)) hT'
  refine (add_le_add h1 h2).trans (le_of_eq ?_)
  unfold difRep3_c3
  simp only [hθ, hR, hMee]
  ring

end STee

/-! ## 4. Grid arithmetic and the coarse time grid (private)

`difRep3_gridTime_nonneg`, `_le`, `_succ`, `_K_mul_step`, `_size_cast` are copies of the private
`difRepTail_*` helpers of `Path/DifREP2.lean:923-954` (RBM3D `76b840e`), `difRep3_gridTime_mono` of
`GridDuhamelN_gridTime_mono` (`Induction/GridDuhamelN.lean:242`, `2ebee73`). -/

section GridArith

private theorem difRep3_gridTime_nonneg {s t : ℕ → ℝ} {K : ℕ → ℕ} {n : ℕ} (hs0 : 0 ≤ s n)
    (hst : s n ≤ t n) (j : ℕ) : 0 ≤ gridTime s t K n j := by
  have hΔ := ST_gridStep_nonneg s t K n hst
  unfold gridTime
  have : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg _
  nlinarith [mul_nonneg this hΔ]

private theorem difRep3_gridTime_le {s t : ℕ → ℝ} {K : ℕ → ℕ} {n : ℕ} (hst : s n ≤ t n)
    (hK0 : K n ≠ 0) {j : ℕ} (hj : j ≤ K n) : gridTime s t K n j ≤ t n := by
  have hΔ := ST_gridStep_nonneg s t K n hst
  have hj' : (j : ℝ) ≤ (K n : ℝ) := by exact_mod_cast hj
  have h := mul_le_mul_of_nonneg_right hj' hΔ
  have hlast := gridTime_last s t K n hK0
  unfold gridTime at hlast ⊢
  nlinarith

private theorem difRep3_gridTime_succ (s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ) :
    gridTime s t K n (j + 1) = gridTime s t K n j + gridStep s t K n := by
  unfold gridTime; push_cast; ring

private theorem difRep3_gridTime_mono {s t : ℕ → ℝ} {K : ℕ → ℕ} {n : ℕ} (hst : s n ≤ t n)
    {i j : ℕ} (hij : i ≤ j) : gridTime s t K n i ≤ gridTime s t K n j := by
  have hΔ := ST_gridStep_nonneg s t K n hst
  unfold gridTime
  have : (i : ℝ) ≤ (j : ℝ) := Nat.cast_le.2 hij
  nlinarith

private theorem difRep3_K_mul_step (s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) (hK : K n ≠ 0) :
    (K n : ℝ) * gridStep s t K n = t n - s n := by
  have hK' : (K n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hK
  unfold gridStep
  field_simp

private theorem difRep3_size_cast {d : ℕ} (sz : Sizes d) (n : ℕ) :
    (sz.W n : ℝ) ^ d * (sz.L n : ℝ) ^ d = ((sz.size n : ℕ) : ℝ) := by
  have : ((sz.size n : ℕ) : ℝ) = (((sz.W n * sz.L n) ^ d : ℕ) : ℝ) := rfl
  rw [this]
  push_cast
  ring

/-- The number of labels `|(Z_L^d)^m| = (L^d)^m` is at most `N^m` (`L^d ≤ W^d L^d = N`). -/
private theorem difRep3_card_label_le {d : ℕ} (sz : Sizes d) (n m : ℕ) :
    (Fintype.card (Fin m → Zd d (sz.L n)) : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ m := by
  have hcard : Fintype.card (Zd d (sz.L n)) = (sz.L n) ^ d := by simp [Zd, ZMod.card]
  have h1 : (Fintype.card (Fin m → Zd d (sz.L n)) : ℝ) = ((sz.L n : ℝ) ^ d) ^ m := by
    rw [Fintype.card_fun, Fintype.card_fin, hcard]
    push_cast
    rfl
  rw [h1]
  refine pow_le_pow_left₀ (by positivity) ?_ m
  have hW : (1 : ℝ) ≤ (sz.W n : ℝ) ^ d :=
    one_le_pow₀ (by exact_mod_cast sz.W_pos n)
  have hL0 : (0 : ℝ) ≤ (sz.L n : ℝ) ^ d := by positivity
  rw [← difRep3_size_cast sz n]
  nlinarith

end GridArith

section Coarse

/-- The coarse time grid `v_p = s + p (t - s)/P`, `p ≤ P` (independent of the fine grid size `K`). -/
private def difRep3_vc (s t : ℝ) (P p : ℕ) : ℝ := s + (p : ℝ) * ((t - s) / P)

private theorem difRep3_vc_ge {s t : ℝ} (hst : s ≤ t) (P p : ℕ) : s ≤ difRep3_vc s t P p := by
  unfold difRep3_vc
  have : 0 ≤ (p : ℝ) * ((t - s) / P) :=
    mul_nonneg (Nat.cast_nonneg _) (div_nonneg (by linarith) (Nat.cast_nonneg _))
  linarith

private theorem difRep3_vc_le {s t : ℝ} (hst : s ≤ t) {P : ℕ} (hP : 1 ≤ P) {p : ℕ} (hp : p ≤ P) :
    difRep3_vc s t P p ≤ t := by
  unfold difRep3_vc
  have hP0 : (0 : ℝ) < P := by exact_mod_cast hP
  have hp' : (p : ℝ) ≤ P := by exact_mod_cast hp
  have : (p : ℝ) * ((t - s) / P) ≤ (P : ℝ) * ((t - s) / P) :=
    mul_le_mul_of_nonneg_right hp' (div_nonneg (by linarith) hP0.le)
  have h2 : (P : ℝ) * ((t - s) / P) = t - s := by field_simp
  linarith

/-- **The coarse index of a fine index**: for `k ≤ K`, `p = ⌈k P / K⌉` satisfies `p ≤ P`,
`u_k ≤ v_p` and `v_p - u_k ≤ (t - s)/P`. -/
private theorem difRep3_coarse (s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) (hst : s n ≤ t n) (hK : K n ≠ 0)
    {P : ℕ} (hP : 1 ≤ P) {k : ℕ} (hk : k ≤ K n) :
    ⌈((k : ℝ) * P) / (K n : ℝ)⌉₊ ≤ P ∧
      gridTime s t K n k ≤ difRep3_vc (s n) (t n) P ⌈((k : ℝ) * P) / (K n : ℝ)⌉₊ ∧
      difRep3_vc (s n) (t n) P ⌈((k : ℝ) * P) / (K n : ℝ)⌉₊ - gridTime s t K n k ≤
        (t n - s n) / P := by
  have hP0 : (0 : ℝ) < P := by exact_mod_cast hP
  have hK0 : (0 : ℝ) < K n := by exact_mod_cast Nat.pos_of_ne_zero hK
  set x : ℝ := ((k : ℝ) * P) / (K n : ℝ) with hx
  have hx0 : 0 ≤ x := by positivity
  have hxP : x ≤ P := by
    rw [hx, div_le_iff₀ hK0]
    have : (k : ℝ) ≤ K n := by exact_mod_cast hk
    nlinarith
  have hc : 0 ≤ (t n - s n) / P := div_nonneg (by linarith) hP0.le
  have hxc : x * ((t n - s n) / P) = (k : ℝ) * ((t n - s n) / K n) := by
    rw [hx]; field_simp
  have h1 : x ≤ (⌈x⌉₊ : ℝ) := Nat.le_ceil x
  have h2 : (⌈x⌉₊ : ℝ) < x + 1 := Nat.ceil_lt_add_one hx0
  refine ⟨Nat.ceil_le.2 hxP, ?_, ?_⟩
  · unfold difRep3_vc gridTime gridStep
    have := mul_le_mul_of_nonneg_right h1 hc
    linarith
  · unfold difRep3_vc gridTime gridStep
    have := mul_le_mul_of_nonneg_right h2.le hc
    nlinarith

end Coarse

/-! ## 5. Doob's `L²` tail with `j`-dependent weights (the `Y` part)

`difRep3_memLp_two_of_pow4`, `difRep3_doob_tail` are copies of the private `difRepTail_memLp_two_of_pow4`,
`difRepTail_doob_tail` (`Path/DifREP2.lean:658-748`, RBM3D `76b840e`); `difRep3_Y_tail` is the weighted form of
the private `difRepTail_Y_tail` (`:1790-1908`): the weights `κ_j` are deterministic and depend on `j`. -/

section YPart

/-- A function with integrable fourth power is square-integrable (probability space). -/
private theorem difRep3_memLp_two_of_pow4 {Ω' : Type*} {m : MeasurableSpace Ω'} {μ : Measure Ω'}
    [IsFiniteMeasure μ] {f : Ω' → ℝ} (hf : AEStronglyMeasurable f μ)
    (h4 : Integrable (fun ω => f ω ^ 4) μ) : MemLp f 2 μ := by
  rw [memLp_two_iff_integrable_sq hf]
  have hg : AEStronglyMeasurable (fun ω => f ω ^ 2) μ := hf.pow 2
  have h2 : MemLp (fun ω => f ω ^ 2) 2 μ := by
    rw [memLp_two_iff_integrable_sq hg]
    refine h4.congr (ae_of_all _ fun ω => ?_)
    simp only
    ring
  exact memLp_one_iff_integrable.1 (h2.mono_exponent (by norm_num))

/-- **Doob's `L²` tail for martingale differences**: `F_j` is `ℱ_{j+1}`-measurable, square-integrable,
conditionally centred, with `𝔼 F_j² ≤ q`; then `μ(∃ k ≤ K, x ≤ |Σ_{j<k} F_j|) ≤ K q / x²`. -/
private theorem difRep3_doob_tail {Ω' : Type} {mΩ' : MeasurableSpace Ω'} (μ : Measure Ω')
    [IsProbabilityMeasure μ] (ℱ : Filtration ℕ mΩ') (F : ℕ → Ω' → ℝ) (K : ℕ) (q x : ℝ)
    (hF : ∀ j < K, StronglyMeasurable[ℱ (j + 1)] (F j))
    (hL2 : ∀ j < K, MemLp (F j) 2 μ)
    (hmean : ∀ j < K, μ[F j | ℱ j] =ᵐ[μ] 0)
    (hq : ∀ j < K, ∫ ω, (F j ω) ^ 2 ∂μ ≤ q) (hx : 0 < x) :
    μ.real {ω | ∃ k, k ≤ K ∧ x ≤ |∑ j ∈ Finset.range k, F j ω|} ≤ K * q / x ^ 2 := by
  classical
  set F' : ℕ → Ω' → ℝ := fun j ω => if j < K then F j ω else 0 with hF'
  set M : ℕ → Ω' → ℝ := fun k ω => ∑ j ∈ Finset.range k, F' j ω with hM
  have hF'm : ∀ j, StronglyMeasurable[ℱ (j + 1)] (F' j) := fun j => by
    by_cases h : j < K
    · simpa only [hF', h, ↓reduceIte] using hF j h
    · simp only [hF', h, ↓reduceIte]
      exact stronglyMeasurable_const
  have hF'L2 : ∀ j, MemLp (F' j) 2 μ := fun j => by
    by_cases h : j < K
    · simpa only [hF', h, ↓reduceIte] using hL2 j h
    · simp only [hF', h, ↓reduceIte]
      exact MemLp.zero'
  have hMad : StronglyAdapted ℱ M := fun k =>
    Finset.stronglyMeasurable_fun_sum _ fun j hj =>
      (hF'm j).mono (ℱ.mono (Nat.succ_le_of_lt (Finset.mem_range.1 hj)))
  have hML2 : ∀ k, MemLp (M k) 2 μ := fun k =>
    memLp_finsetSum _ fun j _ => hF'L2 j
  have hMint : ∀ k, Integrable (M k) μ := fun k => (memLp_one_iff_integrable.1
    ((hML2 k).mono_exponent (by norm_num)))
  have hMsub : ∀ k, M (k + 1) - M k = F' k := fun k => by
    funext ω
    simp only [hM, Pi.sub_apply, Finset.sum_range_succ]
    ring
  have hmart : Martingale M ℱ μ := by
    refine martingale_of_condExp_sub_eq_zero_nat hMad hMint fun k => ?_
    rw [hMsub]
    by_cases h : k < K
    · have : F' k = F k := funext fun ω => by simp only [hF', h, ↓reduceIte]
      rw [this]
      exact hmean k h
    · have : F' k = 0 := funext fun ω => by simp only [hF', h, ↓reduceIte, Pi.zero_apply]
      rw [this]
      exact (condExp_zero).eventuallyEq
  have hM0 : M 0 = 0 := by funext ω; simp [hM]
  have hdoob := doob_L2_max hmart hM0 hML2 K hx
  have hset : {ω | ∃ k, k ≤ K ∧ x ≤ |∑ j ∈ Finset.range k, F j ω|} =
      {ω | x ≤ (Finset.range (K + 1)).sup' Finset.nonempty_range_add_one fun k => |M k ω|} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Finset.le_sup'_iff, Finset.mem_range, Nat.lt_succ_iff]
    constructor
    · rintro ⟨k, hk, hxk⟩
      refine ⟨k, hk, ?_⟩
      have : M k ω = ∑ j ∈ Finset.range k, F j ω :=
        Finset.sum_congr rfl fun j hj => by
          simp only [hF', lt_of_lt_of_le (Finset.mem_range.1 hj) hk, ↓reduceIte]
      rw [this]; exact hxk
    · rintro ⟨k, hk, hxk⟩
      refine ⟨k, hk, ?_⟩
      have : M k ω = ∑ j ∈ Finset.range k, F j ω :=
        Finset.sum_congr rfl fun j hj => by
          simp only [hF', lt_of_lt_of_le (Finset.mem_range.1 hj) hk, ↓reduceIte]
      rw [← this]; exact hxk
  rw [hset]
  refine hdoob.trans ?_
  gcongr
  rw [martingale_sq_eq_sum hmart hM0 hML2 K]
  calc ∑ k ∈ Finset.range K, ∫ ω, (M (k + 1) ω - M k ω) ^ 2 ∂μ
      ≤ ∑ k ∈ Finset.range K, q := by
        refine Finset.sum_le_sum fun k hk => ?_
        have hk' : k < K := Finset.mem_range.1 hk
        have : (fun ω => (M (k + 1) ω - M k ω) ^ 2) = fun ω => (F k ω) ^ 2 := by
          funext ω
          have := congrFun (hMsub k) ω
          simp only [Pi.sub_apply, hF', hk', ↓reduceIte] at this
          rw [this]
        rw [this]
        exact hq k hk'
    _ = K * q := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

end YPart

section YTail

open scoped Matrix.Norms.L2Operator

variable {d : ℕ} (sz : Sizes d)

/-- The stopped weighted increment at `τ ≡ K n` is `Σ_c κ_c Y_{j,c}` for `j < K n` (the weighted form of the
private `difRepTail_stopW_eq`, `Path/DifREP2.lean:1777`). -/
private theorem difRep3_stopW_eq (E s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ) (hj : j < K n) {m : ℕ}
    (σ : Fin m → Bool) (κ : (Fin m → Zd d (sz.L n)) → ℂ) (ω : PathΩ sz) :
    AzumaProxyN_stopW sz E s t K n j σ κ (fun _ => K n) ω =
      ∑ c, κ c * YvecN sz E s t K n j σ ω c := by
  unfold AzumaProxyN_stopW
  have hset : {ω' : PathΩ sz | j < (fun _ => K n) ω'} = Set.univ := by
    ext ω'; simpa using hj
  rw [hset, Set.indicator_univ]

/-- **The `Y` part of the tail, weighted**: for deterministic `j`-dependent weights `κ_j` with
`Σ_c |κ_j(c)| ≤ S`, `C2 = m (m+1) N (16 N)^{m+2}` and any `P ≥ 2000 (S C2)² N⁸`,
`μ (∃ k ≤ K, x ≤ |Σ_{j<k} Σ_c κ_j(c) Y_{j,c}|) ≤ 4 K Δ² P / x²` (`AzumaProxyN_YfieldsW` at `κ_j`, `τ ≡ K n`, and
`difRep3_doob_tail` for `Re` and `Im`). -/
private theorem difRep3_Y_tail (E s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ)
    (hE : |E n| < 2) (hs0 : 0 ≤ s n) (hst : s n ≤ t n) (ht1 : t n < 1)
    {m : ℕ} (σ : Fin m → Bool) (κ : ℕ → (Fin m → Zd d (sz.L n)) → ℂ) {S : ℝ} (hS0 : 0 ≤ S)
    (hrow : ∀ j, ∑ c, ‖κ j c‖ ≤ S)
    (hη : ∀ j, j + 1 ≤ K n →
      1 / (16 * ((sz.size n : ℕ) : ℝ)) ≤ etaT (E n) (gridTime s t K n (j + 1)))
    {P : ℝ} (hP : 2000 * (S * (((m * (m + 1) : ℕ) : ℝ) * ((sz.size n : ℕ) : ℝ) *
        (16 * ((sz.size n : ℕ) : ℝ)) ^ (m + 2))) ^ 2 * ((sz.size n : ℕ) : ℝ) ^ 8 ≤ P)
    {x : ℝ} (hx : 0 < x) :
    (pathP sz).real {ω | ∃ k, k ≤ K n ∧
        x ≤ ‖∑ j ∈ Finset.range k, ∑ c, κ j c * YvecN sz E s t K n j σ ω c‖} ≤
      4 * ((K n : ℝ) * (gridStep s t K n ^ 2 * P)) / x ^ 2 := by
  have hΔ := ST_gridStep_nonneg s t K n hst
  set N : ℝ := ((sz.size n : ℕ) : ℝ) with hN
  have hN1 : 1 ≤ N := by rw [hN]; exact_mod_cast sz.one_le_size n
  set C2 : ℝ := ((m * (m + 1) : ℕ) : ℝ) * N * (16 * N) ^ (m + 2) with hC2def
  have hC20 : 0 ≤ C2 := by positivity
  have hτ : ∀ j, MeasurableSet[filt sz j] {ω : PathΩ sz | j < (fun _ => K n) ω} := fun j =>
    MeasurableSet.const _
  -- the moment fields of `Σ_c κ_j(c) Y_{j,c}` for `j < K n`
  have hfields : ∀ j < K n,
      (pathP sz)[fun ω => (∑ c, κ j c * YvecN sz E s t K n j σ ω c).re | filt sz j]
        =ᵐ[pathP sz] 0 ∧
      (pathP sz)[fun ω => (∑ c, κ j c * YvecN sz E s t K n j σ ω c).im | filt sz j]
        =ᵐ[pathP sz] 0 ∧
      Integrable (fun ω => (∑ c, κ j c * YvecN sz E s t K n j σ ω c).re ^ 4) (pathP sz) ∧
      Integrable (fun ω => (∑ c, κ j c * YvecN sz E s t K n j σ ω c).im ^ 4) (pathP sz) ∧
      (pathP sz)[fun ω => (∑ c, κ j c * YvecN sz E s t K n j σ ω c).re ^ 2 | filt sz j]
        ≤ᵐ[pathP sz] (fun _ => gridStep s t K n ^ 2 * P) ∧
      (pathP sz)[fun ω => (∑ c, κ j c * YvecN sz E s t K n j σ ω c).im ^ 2 | filt sz j]
        ≤ᵐ[pathP sz] (fun _ => gridStep s t K n ^ 2 * P) := by
    intro j hj
    have hj' : j + 1 ≤ K n := hj
    have hK : K n ≠ 0 := by omega
    have hu0 := difRep3_gridTime_nonneg (K := K) hs0 hst (j + 1)
    have hu1 : gridTime s t K n (j + 1) < 1 := (difRep3_gridTime_le hst hK hj').trans_lt ht1
    have hη0 : 0 < etaT (E n) (gridTime s t K n (j + 1)) := etaT_pos hE hu1
    have hinv : (etaT (E n) (gridTime s t K n (j + 1)))⁻¹ ≤ 16 * N := by
      calc (etaT (E n) (gridTime s t K n (j + 1)))⁻¹ ≤ (1 / (16 * N))⁻¹ :=
            inv_anti₀ (by positivity) (hη j hj')
        _ = 16 * N := by rw [one_div, inv_inv]
    have hC2 : ∀ (a' : Fin m → Zd d (sz.L n))
        (M y : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ), M.IsHermitian →
        y.IsHermitian → ‖fderiv ℝ (fderiv ℝ (loopFamN sz E s t K n j σ a')) M y y‖ ≤
          C2 * ‖y‖ ^ 2 := by
      intro a' M y hM hy
      refine ((hermTestFunLoopN sz m n (E n) (gridTime s t K n (j + 1)) hE hu0 hu1 σ a').2 M y hM
        hy).trans ?_
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      rw [hC2def]
      gcongr
    have h := AzumaProxyN_YfieldsW sz E s t K n j hE hs0 hst ht1 hj' σ (κ j) hS0 hC20 (hrow j) hC2
      hP (fun _ => K n) hτ
    simp only [difRep3_stopW_eq sz E s t K n j hj σ (κ j)] at h
    exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1⟩
  have hYm : ∀ j, StronglyMeasurable[filt sz (j + 1)]
      (fun ω => ∑ c, κ j c * YvecN sz E s t K n j σ ω c) := fun j =>
    Finset.stronglyMeasurable_fun_sum _ fun c _ =>
      ((continuous_apply c).comp_stronglyMeasurable
        (gridAsm_stronglyMeasurable_YvecN sz E s t K n j σ)).const_mul _
  have hxs : 0 < x / Real.sqrt 2 := div_pos hx (Real.sqrt_pos.2 (by norm_num))
  have hq : ∀ (F : ℕ → PathΩ sz → ℝ) (j : ℕ), j < K n →
      (pathP sz)[fun ω => F j ω ^ 2 | filt sz j] ≤ᵐ[pathP sz] (fun _ => gridStep s t K n ^ 2 * P) →
      ∫ ω, (F j ω) ^ 2 ∂(pathP sz) ≤ gridStep s t K n ^ 2 * P := by
    intro F j hj h5
    rw [← integral_condExp ((filt sz).le j) (f := fun ω => F j ω ^ 2)]
    calc ∫ ω, ((pathP sz)[fun ω => F j ω ^ 2 | filt sz j]) ω ∂(pathP sz)
        ≤ ∫ _ω, gridStep s t K n ^ 2 * P ∂(pathP sz) :=
          integral_mono_ae integrable_condExp (integrable_const _) h5
      _ = gridStep s t K n ^ 2 * P := by simp
  have hRe := difRep3_doob_tail (pathP sz) (filt sz)
    (fun j ω => (∑ c, κ j c * YvecN sz E s t K n j σ ω c).re)
    (K n) (gridStep s t K n ^ 2 * P) (x / Real.sqrt 2)
    (fun j _ => Complex.continuous_re.comp_stronglyMeasurable (hYm j))
    (fun j hj => difRep3_memLp_two_of_pow4
      ((Complex.continuous_re.comp_stronglyMeasurable
        ((hYm j).mono ((filt sz).le (j + 1)))).aestronglyMeasurable) (hfields j hj).2.2.1)
    (fun j hj => (hfields j hj).1)
    (fun j hj => hq (fun j ω => (∑ c, κ j c * YvecN sz E s t K n j σ ω c).re) j hj
      (hfields j hj).2.2.2.2.1)
    hxs
  have hIm := difRep3_doob_tail (pathP sz) (filt sz)
    (fun j ω => (∑ c, κ j c * YvecN sz E s t K n j σ ω c).im)
    (K n) (gridStep s t K n ^ 2 * P) (x / Real.sqrt 2)
    (fun j _ => Complex.continuous_im.comp_stronglyMeasurable (hYm j))
    (fun j hj => difRep3_memLp_two_of_pow4
      ((Complex.continuous_im.comp_stronglyMeasurable
        ((hYm j).mono ((filt sz).le (j + 1)))).aestronglyMeasurable) (hfields j hj).2.2.2.1)
    (fun j hj => (hfields j hj).2.1)
    (fun j hj => hq (fun j ω => (∑ c, κ j c * YvecN sz E s t K n j σ ω c).im) j hj
      (hfields j hj).2.2.2.2.2)
    hxs
  have hsub : {ω | ∃ k, k ≤ K n ∧
      x ≤ ‖∑ j ∈ Finset.range k, ∑ c, κ j c * YvecN sz E s t K n j σ ω c‖} ⊆
      {ω | ∃ k, k ≤ K n ∧ x / Real.sqrt 2 ≤
        |∑ j ∈ Finset.range k, (∑ c, κ j c * YvecN sz E s t K n j σ ω c).re|} ∪
      {ω | ∃ k, k ≤ K n ∧ x / Real.sqrt 2 ≤
        |∑ j ∈ Finset.range k, (∑ c, κ j c * YvecN sz E s t K n j σ ω c).im|} := by
    intro ω hω
    obtain ⟨k, hk, hxk⟩ := hω
    have h1 := Complex.norm_le_sqrt_two_mul_max
      (∑ j ∈ Finset.range k, ∑ c, κ j c * YvecN sz E s t K n j σ ω c)
    have hs2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
    have h2 : x / Real.sqrt 2 ≤
        max |(∑ j ∈ Finset.range k, ∑ c, κ j c * YvecN sz E s t K n j σ ω c).re|
          |(∑ j ∈ Finset.range k, ∑ c, κ j c * YvecN sz E s t K n j σ ω c).im| := by
      rw [div_le_iff₀ hs2]
      linarith
    rw [Complex.re_sum, Complex.im_sum] at h2
    rcases le_max_iff.1 h2 with h | h
    · exact Or.inl ⟨k, hk, h⟩
    · exact Or.inr ⟨k, hk, h⟩
  calc (pathP sz).real {ω | ∃ k, k ≤ K n ∧
        x ≤ ‖∑ j ∈ Finset.range k, ∑ c, κ j c * YvecN sz E s t K n j σ ω c‖}
      ≤ (pathP sz).real ({ω | ∃ k, k ≤ K n ∧ x / Real.sqrt 2 ≤
          |∑ j ∈ Finset.range k, (∑ c, κ j c * YvecN sz E s t K n j σ ω c).re|} ∪
        {ω | ∃ k, k ≤ K n ∧ x / Real.sqrt 2 ≤
          |∑ j ∈ Finset.range k, (∑ c, κ j c * YvecN sz E s t K n j σ ω c).im|}) :=
        measureReal_mono hsub
    _ ≤ _ := measureReal_union_le _ _
    _ ≤ (K n : ℝ) * (gridStep s t K n ^ 2 * P) / (x / Real.sqrt 2) ^ 2 +
        (K n : ℝ) * (gridStep s t K n ^ 2 * P) / (x / Real.sqrt 2) ^ 2 := add_le_add hRe hIm
    _ = 4 * ((K n : ℝ) * (gridStep s t K n ^ 2 * P)) / x ^ 2 := by
        rw [div_pow, Real.sq_sqrt (by norm_num)]
        field_simp
        ring

end YTail

/-! ## 6. The `Z` part at a coarse level `v_p` and a label `a'`: the weights, the proxy, the threshold

For a coarse time `v_p` and a label `a'`, `κ^{p,a'}_j := ∏_i uKerQ σ (u_j, v_p)(a'_i, ·_i)` if `u_j ≤ v_p` and `0`
otherwise (a deterministic switch), `ζ_j := Σ_b κ_{j,b} Z_{j,b}`, `a_j := 1[u_j ≤ v_p] Δ ‖STeeUQM_{u_j,v_p}(H_j)‖`,
`v_j := max(0, Δ m Re Σ κ κ̄ (𝓔⊗𝓔)_{u_{j+1}}(H_j))` and `e_j := Δ S² eeShiftErrN(u_j, u_{j+1})`. -/

section ZPart

variable {d : ℕ} (sz : Sizes d)

/-- `STeeM` is measurable in the matrix argument (copy of the private `difRepTail_measurable_STeeM`,
`Path/DifREP2.lean:1265`, RBM3D `76b840e`). -/
private theorem difRep3_measurable_STeeM (n : ℕ) (E u : ℝ) {m : ℕ} (σ : Fin m → Bool)
    (a a' : Fin m → Zd d (sz.L n)) :
    Measurable (fun M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ =>
      sz.STeeM n E u M σ a a') := by
  unfold Sizes.STeeM
  refine measurable_const.mul (Finset.measurable_sum _ fun k _ => Finset.measurable_sum _ fun b _ =>
    Finset.measurable_sum _ fun b' _ => measurable_const.mul ?_)
  exact (walk_measurable_loopL d (sz.L n) (sz.W n) (zt E u) _).comp
    (walk_measurable_blockMat d (sz.L n) (sz.W n))

/-- `STeeUQM` is measurable in the matrix argument. -/
private theorem difRep3_measurable_STeeUQM (n : ℕ) (E v w : ℝ) {m : ℕ} (Q : Finset (Fin m))
    (σ : Fin m → Bool) (a : Fin m → Zd d (sz.L n)) :
    Measurable (fun M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ =>
      STeeUQM sz n E v w M Q σ a) := by
  unfold STeeUQM
  exact Finset.measurable_sum _ fun b _ => Finset.measurable_sum _ fun b' _ =>
    measurable_const.mul (difRep3_measurable_STeeM sz n E v σ b b')

/-- `eeShiftErrN` is nonnegative for `η_{u'} ≥ 0`, `u ≤ u'` (copy of the private
`difRepTail_eeShiftErrN_nonneg`, `Path/DifREP2.lean:1308`). -/
private theorem difRep3_eeShiftErrN_nonneg (L W : ℕ) (E : ℝ) (m : ℕ) {u u' : ℝ}
    (hη : 0 ≤ etaT E u') (huu' : u ≤ u') : 0 ≤ eeShiftErrN d L W E m u u' := by
  unfold eeShiftErrN
  have := nqGood1_loopShiftErrN_nonneg hη (sub_nonneg.2 huu') d W (2 * m + 2)
  positivity

/-- The switched weights of the coarse level `vp` at the label `a`. -/
private def difRep3_kap (E s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) {m : ℕ} (Q : Finset (Fin m))
    (σ : Fin m → Bool) (vp : ℝ) (a : Fin m → Zd d (sz.L n)) (j : ℕ) :
    (Fin m → Zd d (sz.L n)) → ℂ :=
  fun b => if gridTime s t K n j ≤ vp then
    ∏ i, uKerQ d (sz.L n) (sz.lam n) (E n) Q σ (gridTime s t K n j) vp i (a i) (b i) else 0

/-- The first-chaos increment `ζ_j = Σ_b κ_{j,b} Z_{j,b}` at the coarse level `vp`. -/
private def difRep3_zeta (E s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) {m : ℕ} (Q : Finset (Fin m))
    (σ : Fin m → Bool) (vp : ℝ) (a : Fin m → Zd d (sz.L n)) (j : ℕ) (ω : PathΩ sz) : ℂ :=
  ∑ b, difRep3_kap sz E s t K n Q σ vp a j b * ZvecN sz E s t K n j σ ω b

/-- The second-order increment `Σ_b κ_{j,b} Y_{j,b}` at the coarse level `vp`. -/
private def difRep3_yinc (E s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) {m : ℕ} (Q : Finset (Fin m))
    (σ : Fin m → Bool) (vp : ℝ) (a : Fin m → Zd d (sz.L n)) (j : ℕ) (ω : PathΩ sz) : ℂ :=
  ∑ b, difRep3_kap sz E s t K n Q σ vp a j b * YvecN sz E s t K n j σ ω b

/-- The threshold increment `a_j = 1[u_j ≤ vp] Δ ‖STeeUQM_{u_j,vp}(H_j)_{Q,σ,a}‖`. -/
private def difRep3_aSeq (E s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) {m : ℕ} (Q : Finset (Fin m))
    (σ : Fin m → Bool) (vp : ℝ) (a : Fin m → Zd d (sz.L n)) (j : ℕ) (ω : PathΩ sz) : ℝ :=
  if gridTime s t K n j ≤ vp then
    gridStep s t K n * ‖STeeUQM sz n (E n) (gridTime s t K n j) vp (pathH sz s t K n j ω) Q σ a‖
  else 0

/-- The quadratic variation `Re Σ_{b,b'} κ_b conj κ_{b'} (𝓔⊗𝓔)_{u_{j+1}}(H_j)_{σ,b,b'}`. -/
private def difRep3_qv (E s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) {m : ℕ} (Q : Finset (Fin m))
    (σ : Fin m → Bool) (vp : ℝ) (a : Fin m → Zd d (sz.L n)) (j : ℕ) (ω : PathΩ sz) : ℝ :=
  (∑ b : Fin m → Zd d (sz.L n), ∑ b' : Fin m → Zd d (sz.L n),
    difRep3_kap sz E s t K n Q σ vp a j b * (starRingEnd ℂ) (difRep3_kap sz E s t K n Q σ vp a j b') *
      sz.STeeM n (E n) (gridTime s t K n (j + 1)) (pathH sz s t K n j ω) σ b b').re

/-- The proxy `v_j = max(0, Δ m Re Σ κ κ̄ (𝓔⊗𝓔)_{u_{j+1}}(H_j))`. -/
private def difRep3_vSeq (E s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) {m : ℕ} (Q : Finset (Fin m))
    (σ : Fin m → Bool) (vp : ℝ) (a : Fin m → Zd d (sz.L n)) (j : ℕ) (ω : PathΩ sz) : ℝ :=
  max 0 (gridStep s t K n * ((m : ℝ) * difRep3_qv sz E s t K n Q σ vp a j ω))

/-- The deterministic shift slack `e_j = Δ S² eeShiftErrN (u_j, u_{j+1})`. -/
private def difRep3_eSeq (E s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) (S : ℝ) (m : ℕ) (j : ℕ) : ℝ :=
  gridStep s t K n * (S ^ 2 * eeShiftErrN d (sz.L n) (sz.W n) (E n) m (gridTime s t K n j)
    (gridTime s t K n (j + 1)))


/-- The switched weights have `Σ_b |κ_{j,b}| ≤ (32 N)^m` (`difRep3_sum_norm_kappa_le`). -/
private theorem difRep3_kap_sum_le (E s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) (hE : |E n| < 2)
    (hs0 : 0 ≤ s n) (hst : s n ≤ t n) {m : ℕ} (Q : Finset (Fin m)) (σ : Fin m → Bool) {vp : ℝ}
    (hvp1 : vp < 1) (hvp16 : (1 - vp)⁻¹ ≤ 16 * ((sz.size n : ℕ) : ℝ))
    (a : Fin m → Zd d (sz.L n)) (j : ℕ) :
    ∑ b, ‖difRep3_kap sz E s t K n Q σ vp a j b‖ ≤ (32 * ((sz.size n : ℕ) : ℝ)) ^ m := by
  unfold difRep3_kap
  by_cases h : gridTime s t K n j ≤ vp
  · simp only [h, ↓reduceIte]
    exact difRep3_sum_norm_kappa_le (sz.three_le_L n) hE.le Q σ
      (difRep3_gridTime_nonneg hs0 hst j) h hvp1 hvp16 a
  · simp only [h, ↓reduceIte, norm_zero, Finset.sum_const_zero]
    positivity

private theorem difRep3_aSeq_nonneg (E s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) (hst : s n ≤ t n)
    {m : ℕ} (Q : Finset (Fin m)) (σ : Fin m → Bool) (vp : ℝ) (a : Fin m → Zd d (sz.L n))
    (j : ℕ) (ω : PathΩ sz) : 0 ≤ difRep3_aSeq sz E s t K n Q σ vp a j ω := by
  unfold difRep3_aSeq
  split_ifs
  · exact mul_nonneg (ST_gridStep_nonneg s t K n hst) (norm_nonneg _)
  · exact le_rfl

private theorem difRep3_vSeq_nonneg (E s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) {m : ℕ}
    (Q : Finset (Fin m)) (σ : Fin m → Bool) (vp : ℝ) (a : Fin m → Zd d (sz.L n)) (j : ℕ)
    (ω : PathΩ sz) : 0 ≤ difRep3_vSeq sz E s t K n Q σ vp a j ω :=
  le_max_left _ _

private theorem difRep3_eSeq_nonneg (E s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ) (hE : |E n| < 2)
    (hst : s n ≤ t n) (ht1 : t n < 1) (hj : j + 1 ≤ K n) (S : ℝ) (m : ℕ) :
    0 ≤ difRep3_eSeq sz E s t K n S m j := by
  have hK : K n ≠ 0 := by omega
  have hu1 : gridTime s t K n (j + 1) < 1 := (difRep3_gridTime_le hst hK hj).trans_lt ht1
  have hsucc := difRep3_gridTime_succ s t K n j
  have hΔ := ST_gridStep_nonneg s t K n hst
  unfold difRep3_eSeq
  refine mul_nonneg hΔ (mul_nonneg (sq_nonneg _)
    (difRep3_eeShiftErrN_nonneg _ _ _ _ (etaT_pos hE hu1).le ?_))
  rw [hsucc]; linarith

/-- **The proxy is dominated by `m (a_j + e_j)`**: the switched weights give
`Σ κ κ̄ (𝓔⊗𝓔)_{u_j} = STeeUQM_{u_j,vp}` (`difRep3_STeeUQM_eq`) and the shift `u_j → u_{j+1}` costs
`S² eeShiftErrN` (`norm_STeeM_shiftN_le`, `difRep3_norm_double_sum_le`). -/
private theorem difRep3_vSeq_le (E s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ) (hE : |E n| < 2)
    (hs0 : 0 ≤ s n) (hst : s n ≤ t n) (ht1 : t n < 1) (hj : j + 1 ≤ K n) {m : ℕ}
    (Q : Finset (Fin m)) (σ : Fin m → Bool) {vp : ℝ} (hvp0 : 0 ≤ vp) (hvp1 : vp < 1)
    (hvp16 : (1 - vp)⁻¹ ≤ 16 * ((sz.size n : ℕ) : ℝ)) (a : Fin m → Zd d (sz.L n))
    (ω : PathΩ sz) :
    difRep3_vSeq sz E s t K n Q σ vp a j ω ≤
      (m : ℝ) * (difRep3_aSeq sz E s t K n Q σ vp a j ω +
        difRep3_eSeq sz E s t K n ((32 * ((sz.size n : ℕ) : ℝ)) ^ m) m j) := by
  have hK : K n ≠ 0 := by omega
  have hu1 : gridTime s t K n (j + 1) < 1 := (difRep3_gridTime_le hst hK hj).trans_lt ht1
  have hsucc := difRep3_gridTime_succ s t K n j
  have hΔ := ST_gridStep_nonneg s t K n hst
  have hH := pathH_isHermitian sz s t K n j ω
  have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
  have hS0 : 0 ≤ (32 * ((sz.size n : ℕ) : ℝ)) ^ m := by positivity
  have he0 := difRep3_eSeq_nonneg sz E s t K n j hE hst ht1 hj ((32 * ((sz.size n : ℕ) : ℝ)) ^ m) m
  have ha0 := difRep3_aSeq_nonneg sz E s t K n hst Q σ vp a j ω
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  unfold difRep3_vSeq
  refine max_le (mul_nonneg hm0 (add_nonneg ha0 he0)) ?_
  by_cases h : gridTime s t K n j ≤ vp
  · have hshift := norm_STeeM_shiftN_le sz n hE hH (u := gridTime s t K n j)
      (u' := gridTime s t K n (j + 1)) (by rw [hsucc]; linarith) hu1 (k := m) σ
    have hS := difRep3_kap_sum_le sz E s t K n hE hs0 hst Q σ hvp1 hvp16 a j
    have herr0 : 0 ≤ eeShiftErrN d (sz.L n) (sz.W n) (E n) m (gridTime s t K n j)
        (gridTime s t K n (j + 1)) :=
      difRep3_eeShiftErrN_nonneg _ _ _ _ (etaT_pos hE hu1).le (by rw [hsucc]; linarith)
    -- the quadratic form at `u_j` is the proxy
    have hkap : ∀ b, difRep3_kap sz E s t K n Q σ vp a j b =
        ∏ i, uKerQ d (sz.L n) (sz.lam n) (E n) Q σ (gridTime s t K n j) vp i (a i) (b i) := by
      intro b; simp only [difRep3_kap, h, ↓reduceIte]
    have hX : (∑ b : Fin m → Zd d (sz.L n), ∑ b' : Fin m → Zd d (sz.L n),
        difRep3_kap sz E s t K n Q σ vp a j b *
          (starRingEnd ℂ) (difRep3_kap sz E s t K n Q σ vp a j b') *
          sz.STeeM n (E n) (gridTime s t K n (j + 1)) (pathH sz s t K n j ω) σ b b') =
        STeeUQM sz n (E n) (gridTime s t K n j) vp (pathH sz s t K n j ω) Q σ a +
          ∑ b : Fin m → Zd d (sz.L n), ∑ b' : Fin m → Zd d (sz.L n),
            difRep3_kap sz E s t K n Q σ vp a j b *
              (starRingEnd ℂ) (difRep3_kap sz E s t K n Q σ vp a j b') *
              (sz.STeeM n (E n) (gridTime s t K n (j + 1)) (pathH sz s t K n j ω) σ b b' -
                sz.STeeM n (E n) (gridTime s t K n j) (pathH sz s t K n j ω) σ b b') := by
      rw [difRep3_STeeUQM_eq sz n hE.le (gridTime s t K n j) hvp0 hvp1]
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun b' _ => ?_
      simp only [hkap]
      ring
    have hdiff : ‖∑ b : Fin m → Zd d (sz.L n), ∑ b' : Fin m → Zd d (sz.L n),
        difRep3_kap sz E s t K n Q σ vp a j b *
          (starRingEnd ℂ) (difRep3_kap sz E s t K n Q σ vp a j b') *
          (sz.STeeM n (E n) (gridTime s t K n (j + 1)) (pathH sz s t K n j ω) σ b b' -
            sz.STeeM n (E n) (gridTime s t K n j) (pathH sz s t K n j ω) σ b b')‖ ≤
        (32 * ((sz.size n : ℕ) : ℝ)) ^ m * (32 * ((sz.size n : ℕ) : ℝ)) ^ m *
          eeShiftErrN d (sz.L n) (sz.W n) (E n) m (gridTime s t K n j)
            (gridTime s t K n (j + 1)) :=
      difRep3_norm_double_sum_le _ (fun b' => (starRingEnd ℂ) (difRep3_kap sz E s t K n Q σ vp a j b'))
        _ herr0 hS (by simpa only [Complex.norm_conj] using hS) fun b b' => hshift b b'
    have hqv : difRep3_qv sz E s t K n Q σ vp a j ω ≤
        ‖STeeUQM sz n (E n) (gridTime s t K n j) vp (pathH sz s t K n j ω) Q σ a‖ +
          (32 * ((sz.size n : ℕ) : ℝ)) ^ m * (32 * ((sz.size n : ℕ) : ℝ)) ^ m *
            eeShiftErrN d (sz.L n) (sz.W n) (E n) m (gridTime s t K n j)
              (gridTime s t K n (j + 1)) := by
      unfold difRep3_qv
      rw [hX]
      refine (Complex.re_le_norm _).trans ((norm_add_le _ _).trans ?_)
      exact add_le_add le_rfl hdiff
    unfold difRep3_aSeq difRep3_eSeq
    simp only [h, ↓reduceIte]
    calc gridStep s t K n * ((m : ℝ) * difRep3_qv sz E s t K n Q σ vp a j ω)
        ≤ gridStep s t K n * ((m : ℝ) * (‖STeeUQM sz n (E n) (gridTime s t K n j) vp
            (pathH sz s t K n j ω) Q σ a‖ + (32 * ((sz.size n : ℕ) : ℝ)) ^ m *
            (32 * ((sz.size n : ℕ) : ℝ)) ^ m * eeShiftErrN d (sz.L n) (sz.W n) (E n) m
            (gridTime s t K n j) (gridTime s t K n (j + 1)))) := by gcongr
      _ = (m : ℝ) * (gridStep s t K n * ‖STeeUQM sz n (E n) (gridTime s t K n j) vp
            (pathH sz s t K n j ω) Q σ a‖ + gridStep s t K n *
            (((32 * ((sz.size n : ℕ) : ℝ)) ^ m) ^ 2 * eeShiftErrN d (sz.L n) (sz.W n) (E n) m
              (gridTime s t K n j) (gridTime s t K n (j + 1)))) := by ring
  · have hk : ∀ b, difRep3_kap sz E s t K n Q σ vp a j b = 0 := fun b => by
      simp only [difRep3_kap, h, ↓reduceIte]
    have hq : difRep3_qv sz E s t K n Q σ vp a j ω = 0 := by
      unfold difRep3_qv
      simp only [hk, zero_mul, Finset.sum_const_zero, Complex.zero_re]
    rw [hq, mul_zero, mul_zero]
    exact mul_nonneg hm0 (add_nonneg ha0 he0)


/-- `ω ↦ a_j(ω)` is `filt sz j`-strongly measurable. -/
private theorem difRep3_aSeq_sm (E s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ) {m : ℕ}
    (Q : Finset (Fin m)) (σ : Fin m → Bool) (vp : ℝ) (a : Fin m → Zd d (sz.L n)) :
    StronglyMeasurable[filt sz j] (difRep3_aSeq sz E s t K n Q σ vp a j) := by
  by_cases h : gridTime s t K n j ≤ vp
  · have e : difRep3_aSeq sz E s t K n Q σ vp a j = fun ω => gridStep s t K n *
        ‖STeeUQM sz n (E n) (gridTime s t K n j) vp (pathH sz s t K n j ω) Q σ a‖ :=
      funext fun ω => by simp only [difRep3_aSeq, h, ↓reduceIte]
    rw [e]
    have hH := pathH_measurable_filt sz s t K n j
    have hS : Measurable[filt sz j] (fun ω => STeeUQM sz n (E n) (gridTime s t K n j) vp
        (pathH sz s t K n j ω) Q σ a) :=
      (difRep3_measurable_STeeUQM sz n (E n) _ vp Q σ a).comp hH
    exact hS.stronglyMeasurable.norm.const_mul _
  · have e : difRep3_aSeq sz E s t K n Q σ vp a j = fun _ => 0 :=
      funext fun ω => by simp only [difRep3_aSeq, h, ↓reduceIte]
    rw [e]
    exact stronglyMeasurable_const

/-- `ω ↦ v_j(ω)` is `filt sz j`-strongly measurable. -/
private theorem difRep3_vSeq_sm (E s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ) {m : ℕ}
    (Q : Finset (Fin m)) (σ : Fin m → Bool) (vp : ℝ) (a : Fin m → Zd d (sz.L n)) :
    StronglyMeasurable[filt sz j] (difRep3_vSeq sz E s t K n Q σ vp a j) := by
  have hH := pathH_measurable_filt sz s t K n j
  have hf : Measurable (fun M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ =>
      (∑ b : Fin m → Zd d (sz.L n), ∑ b' : Fin m → Zd d (sz.L n),
        difRep3_kap sz E s t K n Q σ vp a j b *
          (starRingEnd ℂ) (difRep3_kap sz E s t K n Q σ vp a j b') *
          sz.STeeM n (E n) (gridTime s t K n (j + 1)) M σ b b').re) :=
    Complex.measurable_re.comp (Finset.measurable_sum _ fun b _ => Finset.measurable_sum _
      fun b' _ => measurable_const.mul (difRep3_measurable_STeeM sz n _ _ σ b b'))
  have hqv : Measurable[filt sz j] (difRep3_qv sz E s t K n Q σ vp a j) := hf.comp hH
  have : Measurable[filt sz j] (difRep3_vSeq sz E s t K n Q σ vp a j) :=
    measurable_const.max ((hqv.const_mul _).const_mul _)
  exact this.stronglyMeasurable

/-- `Re ζ_j` is `filt sz (j+1)`-strongly measurable. -/
private theorem difRep3_zeta_re_sm (E s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ) {m : ℕ}
    (Q : Finset (Fin m)) (σ : Fin m → Bool) (vp : ℝ) (a : Fin m → Zd d (sz.L n)) :
    StronglyMeasurable[filt sz (j + 1)] (fun ω => (difRep3_zeta sz E s t K n Q σ vp a j ω).re) :=
  Complex.continuous_re.comp_stronglyMeasurable
    (Finset.stronglyMeasurable_fun_sum _ fun b _ =>
      ((continuous_apply b).comp_stronglyMeasurable
        (gridAsm_stronglyMeasurable_ZvecN sz E s t K n j σ)).const_mul _)

/-- `Im ζ_j` is `filt sz (j+1)`-strongly measurable. -/
private theorem difRep3_zeta_im_sm (E s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ) {m : ℕ}
    (Q : Finset (Fin m)) (σ : Fin m → Bool) (vp : ℝ) (a : Fin m → Zd d (sz.L n)) :
    StronglyMeasurable[filt sz (j + 1)] (fun ω => (difRep3_zeta sz E s t K n Q σ vp a j ω).im) :=
  Complex.continuous_im.comp_stronglyMeasurable
    (Finset.stronglyMeasurable_fun_sum _ fun b _ =>
      ((continuous_apply b).comp_stronglyMeasurable
        (gridAsm_stronglyMeasurable_ZvecN sz E s t K n j σ)).const_mul _)

/-- **The mgf facts of `Re ζ_j`, `Im ζ_j` with the proxy `v_j`** (`difRepTail_condMGF_Z` at the weights
`κ_j`; `exp` is monotone and `v_j = max(0, ·)`). -/
private theorem difRep3_zeta_mgf (E s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ) (hE : |E n| < 2)
    (hs0 : 0 ≤ s n) (hst : s n ≤ t n) (ht1 : t n < 1) (hj : j + 1 ≤ K n) {m : ℕ} (hm : 2 ≤ m)
    (Q : Finset (Fin m)) (σ : Fin m → Bool) (vp : ℝ) (a : Fin m → Zd d (sz.L n)) (r : ℝ) :
    Integrable (fun ω => Real.exp (r * (difRep3_zeta sz E s t K n Q σ vp a j ω).re)) (pathP sz) ∧
    Integrable (fun ω => Real.exp (r * (difRep3_zeta sz E s t K n Q σ vp a j ω).im)) (pathP sz) ∧
    (pathP sz)[fun ω => Real.exp (r * (difRep3_zeta sz E s t K n Q σ vp a j ω).re) | filt sz j]
      ≤ᵐ[pathP sz] (fun ω => Real.exp (r ^ 2 * difRep3_vSeq sz E s t K n Q σ vp a j ω / 2)) ∧
    (pathP sz)[fun ω => Real.exp (r * (difRep3_zeta sz E s t K n Q σ vp a j ω).im) | filt sz j]
      ≤ᵐ[pathP sz] (fun ω => Real.exp (r ^ 2 * difRep3_vSeq sz E s t K n Q σ vp a j ω / 2)) := by
  obtain ⟨h1, h2, h3, h4⟩ := difRepTail_condMGF_Z sz E s t K n j hE hs0 hst ht1 hj hm σ
    (difRep3_kap sz E s t K n Q σ vp a j) r
  have hle : ∀ ω : PathΩ sz, r ^ 2 * (gridStep s t K n * ((m : ℝ) * difRep3_qv sz E s t K n Q σ vp a j ω)) / 2 ≤
      r ^ 2 * difRep3_vSeq sz E s t K n Q σ vp a j ω / 2 := by
    intro ω
    unfold difRep3_vSeq
    have := le_max_right 0 (gridStep s t K n * ((m : ℝ) * difRep3_qv sz E s t K n Q σ vp a j ω))
    have h0 : 0 ≤ r ^ 2 := sq_nonneg r
    nlinarith
  refine ⟨h1, h2, h3.trans (Eventually.of_forall fun ω => ?_), h4.trans (Eventually.of_forall fun ω => ?_)⟩
  · exact Real.exp_le_exp.2 (hle ω)
  · exact Real.exp_le_exp.2 (hle ω)

/-- The threshold increment is at most `Δ (32 N)^{2m} m N (16 N)^{2m+2}` (the crude bound
`difRep3_norm_STeeUQM_le`). -/
private theorem difRep3_aSeq_le (E s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ) (hE : |E n| < 2)
    (hs0 : 0 ≤ s n) (hst : s n ≤ t n) (hK : K n ≠ 0) (hj : j ≤ K n)
    (hη : ∀ u : ℝ, u ≤ t n → 1 / (16 * ((sz.size n : ℕ) : ℝ)) ≤ etaT (E n) u) {m : ℕ}
    (Q : Finset (Fin m)) (σ : Fin m → Bool) {vp : ℝ} (hvp1 : vp < 1)
    (hvp16 : (1 - vp)⁻¹ ≤ 16 * ((sz.size n : ℕ) : ℝ)) (a : Fin m → Zd d (sz.L n))
    (ω : PathΩ sz) :
    difRep3_aSeq sz E s t K n Q σ vp a j ω ≤ gridStep s t K n *
      (((32 * ((sz.size n : ℕ) : ℝ)) ^ m * (32 * ((sz.size n : ℕ) : ℝ)) ^ m) *
        ((m : ℝ) * ((sz.size n : ℕ) : ℝ) * (16 * ((sz.size n : ℕ) : ℝ)) ^ (2 * m + 2))) := by
  have hΔ := ST_gridStep_nonneg s t K n hst
  have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
  unfold difRep3_aSeq
  split_ifs with h
  · exact mul_le_mul_of_nonneg_left
      (difRep3_norm_STeeUQM_le sz n hE (difRep3_gridTime_nonneg hs0 hst j) h hvp1 hvp16
        (hη _ (difRep3_gridTime_le hst hK hj)) (pathH_isHermitian sz s t K n j ω) Q σ a) hΔ
  · positivity

/-- **The `Z` part of the tail**, through the peeling lemma `difRep2_peel` (`ζ_j`, `a_j`, `v_j`, `e_j`, `c = m`). -/
private theorem difRep3_Z_tail (E s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) (hE : |E n| < 2)
    (hs0 : 0 ≤ s n) (hst : s n ≤ t n) (ht1 : t n < 1) {m : ℕ} (hm : 2 ≤ m)
    (Q : Finset (Fin m)) (σ : Fin m → Bool) {vp : ℝ} (hvp0 : 0 ≤ vp) (hvp1 : vp < 1)
    (hvp16 : (1 - vp)⁻¹ ≤ 16 * ((sz.size n : ℕ) : ℝ)) (a : Fin m → Zd d (sz.L n)) (Lmax : ℕ)
    {δ ρ : ℝ} (hδ : 0 < δ) (hρ : 0 ≤ ρ)
    (hesum : ∑ j ∈ Finset.range (K n),
      difRep3_eSeq sz E s t K n ((32 * ((sz.size n : ℕ) : ℝ)) ^ m) m j ≤ δ)
    (haL : ∀ ω, ∑ j ∈ Finset.range (K n), difRep3_aSeq sz E s t K n Q σ vp a j ω ≤ 2 ^ Lmax * δ) :
    (pathP sz).real {ω | ∃ k, k ≤ K n ∧
        ρ * (∑ j ∈ Finset.range k, difRep3_aSeq sz E s t K n Q σ vp a j ω + δ) ^ (1 / 2 : ℝ) <
          ‖∑ j ∈ Finset.range k, difRep3_zeta sz E s t K n Q σ vp a j ω‖} ≤
      ((Lmax : ℝ) + 1) * (4 * Real.exp (-ρ ^ 2 / (16 * m))) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  exact difRep2_peel (pathP sz) (filt sz) (fun j ω => difRep3_zeta sz E s t K n Q σ vp a j ω)
    (fun j => difRep3_aSeq sz E s t K n Q σ vp a j) (fun j => difRep3_vSeq sz E s t K n Q σ vp a j)
    (fun j => difRep3_eSeq sz E s t K n ((32 * ((sz.size n : ℕ) : ℝ)) ^ m) m j) (K n) Lmax (m : ℝ)
    δ ρ hm0 hδ hρ
    (fun j _ => difRep3_zeta_re_sm sz E s t K n j Q σ vp a)
    (fun j _ => difRep3_zeta_im_sm sz E s t K n j Q σ vp a)
    (fun j _ => difRep3_aSeq_sm sz E s t K n j Q σ vp a)
    (fun j _ => difRep3_vSeq_sm sz E s t K n j Q σ vp a)
    (fun j _ ω => difRep3_aSeq_nonneg sz E s t K n hst Q σ vp a j ω)
    (fun j _ ω => difRep3_vSeq_nonneg sz E s t K n Q σ vp a j ω)
    (fun j hj => difRep3_eSeq_nonneg sz E s t K n j hE hst ht1 hj _ m)
    (fun j hj ω => difRep3_vSeq_le sz E s t K n j hE hs0 hst ht1 hj Q σ hvp0 hvp1 hvp16 a ω)
    hesum haL
    (fun j hj r => (difRep3_zeta_mgf sz E s t K n j hE hs0 hst ht1 hj hm Q σ vp a r).1)
    (fun j hj r => (difRep3_zeta_mgf sz E s t K n j hE hs0 hst ht1 hj hm Q σ vp a r).2.1)
    (fun j hj r => (difRep3_zeta_mgf sz E s t K n j hE hs0 hst ht1 hj hm Q σ vp a r).2.2.1)
    (fun j hj r => (difRep3_zeta_mgf sz E s t K n j hE hs0 hst ht1 hj hm Q σ vp a r).2.2.2)

end ZPart

/-! ## 7. The pathwise inclusion (step (g)): from the good events at the coarse level to the pin's bound -/

section Pathwise

variable {d : ℕ} (sz : Sizes d)

/-- `M_ee = m N (16 N)^{2m+2}`, the crude bound of `(𝓔⊗𝓔)` (`difRep2_norm_STeeM_le_N`). -/
private def difRep3_Mee (N : ℝ) (m : ℕ) : ℝ := (m : ℝ) * N * (16 * N) ^ (2 * m + 2)

/-- `V_Q = (32 N)^{2m} M_ee`, the crude bound of `STeeUQM` (`difRep3_norm_STeeUQM_le`). -/
private def difRep3_VQ (N : ℝ) (m : ℕ) : ℝ :=
  ((32 * N) ^ m * (32 * N) ^ m) * difRep3_Mee N m

/-- `(1 - u)⁻¹ ≤ 16 N` from `η_u ≥ 1/(16 N)` and `η_u ≤ 1 - u`. -/
private theorem difRep3_inv_le {E N u : ℝ} (hN : 0 < N) (h1 : 1 / (16 * N) ≤ etaT E u)
    (h2 : etaT E u ≤ 1 - u) : (1 - u)⁻¹ ≤ 16 * N := by
  have h3 : 1 / (16 * N) ≤ 1 - u := h1.trans h2
  calc (1 - u)⁻¹ ≤ (1 / (16 * N))⁻¹ := inv_anti₀ (by positivity) h3
    _ = 16 * N := by rw [one_div, inv_inv]


/-- **The pathwise inclusion** (step (g) of the ticket): at the coarse level `v_p`, `p = ⌈k P/K⌉`, if the first-chaos sums
`Σ_{j<k} ζ^{p,a'}_j` obey the peeled bound and the second-order sums `Σ_{j<k} Σ_b κ^{p,a'}_{j,b} Y_{j,b}` are at most
`x_Y = ρ √δ`, for every label `a'`, then the pin's sum `X_k = Σ_{j<k} (Q 𝒰_{u_j,u_k} ΔMart_j)_a` is at most
`ρ (A_k + N^{-D})^{1/2} + 2 x_Y`: the exact transfer `X_k = (𝒰_{v_p,u_k} W_k)_a`
(`difRep3_UN_transfer`, `zeroModeSet_UN_eq_uKerQ`), the kernel transfer (f1) `difRep3_norm_UN_sub_le` and the
proxy transfer (f2) `difRep3_norm_STeeUQM_sub_le`. -/
private theorem difRep3_pathwise (E s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ)
    (hE : |E n| < 2) (hs0 : 0 ≤ s n) (hst : s n ≤ t n) (ht1 : t n < 1) (hK : K n ≠ 0)
    {m : ℕ} (hm : 2 ≤ m) (Q : Finset (Fin m)) (σ : Fin m → Bool) (a : Fin m → Zd d (sz.L n))
    (hη : ∀ u : ℝ, u ≤ t n → 1 / (16 * ((sz.size n : ℕ) : ℝ)) ≤ etaT (E n) u)
    (h1u : ∀ u : ℝ, u ≤ t n → etaT (E n) u ≤ 1 - u)
    {P : ℕ} (hP1 : 1 ≤ P) {ρ₁ : ℝ} (hPρ : 1 / (P : ℝ) ≤ ρ₁) (D : ℝ) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hKΔ : (K n : ℝ) * gridStep s t K n ≤ 1)
    (hf2 : difRep3_c3 ((sz.size n : ℕ) : ℝ) m * ρ₁ ≤ ((sz.size n : ℕ) : ℝ) ^ (-D) / 4)
    (hf1 : (m : ℝ) * (16 * ((sz.size n : ℕ) : ℝ) * ρ₁) *
        (1 + 16 * ((sz.size n : ℕ) : ℝ) * ρ₁) ^ (m - 1) *
        (ρ * Real.sqrt (difRep3_VQ ((sz.size n : ℕ) : ℝ) m + ((sz.size n : ℕ) : ℝ) ^ (-D) / 2) +
          ρ * Real.sqrt (((sz.size n : ℕ) : ℝ) ^ (-D) / 2)) ≤
        ρ * Real.sqrt (((sz.size n : ℕ) : ℝ) ^ (-D) / 2))
    (ω : PathΩ sz) {k : ℕ} (hk : k ≤ K n)
    (hZg : ∀ a' : Fin m → Zd d (sz.L n),
      ‖∑ j ∈ Finset.range k, difRep3_zeta sz E s t K n Q σ
          (difRep3_vc (s n) (t n) P ⌈((k : ℝ) * P) / (K n : ℝ)⌉₊) a' j ω‖ ≤
        ρ * (∑ j ∈ Finset.range k, difRep3_aSeq sz E s t K n Q σ
          (difRep3_vc (s n) (t n) P ⌈((k : ℝ) * P) / (K n : ℝ)⌉₊) a' j ω +
          ((sz.size n : ℕ) : ℝ) ^ (-D) / 2) ^ (1 / 2 : ℝ))
    (hYg : ∀ a' : Fin m → Zd d (sz.L n),
      ‖∑ j ∈ Finset.range k, difRep3_yinc sz E s t K n Q σ
          (difRep3_vc (s n) (t n) P ⌈((k : ℝ) * P) / (K n : ℝ)⌉₊) a' j ω‖ ≤
        ρ * Real.sqrt (((sz.size n : ℕ) : ℝ) ^ (-D) / 2)) :
    ‖∑ j ∈ Finset.range k, zeroModeSet d (sz.L n) Q
        (UN d (sz.L n) (sz.lam n) (fun i' => mSigma (E n) (σ i')) (gridTime s t K n j)
          (gridTime s t K n k)
          (fun b => difRepMartN sz E s t K n (σ, b) (j + 1) ω -
            difRepMartN sz E s t K n (σ, b) j ω)) a‖ ≤
      ρ * (∑ j ∈ Finset.range k, gridStep s t K n *
          ‖STeeUQM sz n (E n) (gridTime s t K n j) (gridTime s t K n k)
            (pathH sz s t K n j ω) Q σ a‖ + ((sz.size n : ℕ) : ℝ) ^ (-D)) ^ (1 / 2 : ℝ) +
        2 * (ρ * Real.sqrt (((sz.size n : ℕ) : ℝ) ^ (-D) / 2)) := by
  -- notation
  set N : ℝ := ((sz.size n : ℕ) : ℝ) with hN
  have hN1 : (1 : ℝ) ≤ N := by rw [hN]; exact_mod_cast sz.one_le_size n
  have hN0 : 0 < N := by linarith
  set Δ := gridStep s t K n with hΔdef
  have hΔ : 0 ≤ Δ := ST_gridStep_nonneg s t K n hst
  set p : ℕ := ⌈((k : ℝ) * P) / (K n : ℝ)⌉₊ with hp
  set vp : ℝ := difRep3_vc (s n) (t n) P p with hvp
  set uk : ℝ := gridTime s t K n k with huk
  -- the coarse index
  obtain ⟨hpP, hukvp, hvpuk⟩ := difRep3_coarse s t K n hst hK hP1 hk
  have hvp_t : vp ≤ t n := difRep3_vc_le hst hP1 hpP
  have huk0 : 0 ≤ uk := difRep3_gridTime_nonneg hs0 hst k
  have hvp0 : 0 ≤ vp := huk0.trans hukvp
  have hvp1 : vp < 1 := hvp_t.trans_lt ht1
  have hukt : uk ≤ t n := difRep3_gridTime_le hst hK hk
  have huk1 : uk < 1 := hukt.trans_lt ht1
  have hts : t n - s n ≤ 1 := by linarith
  have hP0 : (0 : ℝ) < P := by exact_mod_cast hP1
  have hvpuk' : vp - uk ≤ ρ₁ :=
    hvpuk.trans ((div_le_div_of_nonneg_right hts hP0.le).trans hPρ)
  have hvp16 : (1 - vp)⁻¹ ≤ 16 * N := difRep3_inv_le hN0 (hη vp hvp_t) (h1u vp hvp_t)
  have huk16 : (1 - uk)⁻¹ ≤ 16 * N := difRep3_inv_le hN0 (hη uk hukt) (h1u uk hukt)
  have hρ₁ : 0 ≤ ρ₁ := (div_nonneg zero_le_one hP0.le).trans hPρ
  -- `δ`, `x_Y`
  have hND : 0 < N ^ (-D) := Real.rpow_pos_of_pos hN0 _
  set δ : ℝ := N ^ (-D) / 2 with hδdef
  have hδ0 : 0 < δ := by positivity
  set xY : ℝ := ρ * Real.sqrt δ with hxY
  have hxY0 : 0 ≤ xY := mul_nonneg hρ (Real.sqrt_nonneg _)
  -- Step 1: the exact transfer
  set ξ : ℕ → (Fin m → Zd d (sz.L n)) → ℂ := fun j => martIncN sz E s t K n j σ ω with hξ
  have hfun : ∀ j, (fun b => difRepMartN sz E s t K n (σ, b) (j + 1) ω -
      difRepMartN sz E s t K n (σ, b) j ω) = ξ j := fun j =>
    funext fun b => difRepMartN_succ_sub sz E s t K n (σ, b) j ω
  simp only [hfun]
  have hT := difRep3_UN_transfer (sz.lam n) (sz.three_le_L n) hE.le σ Q hvp0 hvp1 huk0 huk1 k
    (fun j => gridTime s t K n j) ξ
  set W : (Fin m → Zd d (sz.L n)) → ℂ :=
    ∑ j ∈ Finset.range k, zeroModeSet d (sz.L n) Q
      (UN d (sz.L n) (sz.lam n) (fun i' => mSigma (E n) (σ i')) (gridTime s t K n j) vp (ξ j))
    with hWdef
  have hX : ∑ j ∈ Finset.range k, zeroModeSet d (sz.L n) Q
      (UN d (sz.L n) (sz.lam n) (fun i' => mSigma (E n) (σ i')) (gridTime s t K n j) uk (ξ j)) a =
      UN d (sz.L n) (sz.lam n) (fun i' => mSigma (E n) (σ i')) vp uk W a := by
    rw [← hT, Finset.sum_apply]
  rw [hX]
  -- Step 2: the label sums
  have hW : ∀ a' : Fin m → Zd d (sz.L n), W a' =
      ∑ j ∈ Finset.range k, difRep3_zeta sz E s t K n Q σ vp a' j ω +
        ∑ j ∈ Finset.range k, difRep3_yinc sz E s t K n Q σ vp a' j ω := by
    intro a'
    rw [hWdef, Finset.sum_apply, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hjk : j < k := Finset.mem_range.1 hj
    have hon : gridTime s t K n j ≤ vp := (difRep3_gridTime_mono hst hjk.le).trans hukvp
    rw [zeroModeSet_UN_eq_uKerQ]
    simp only [tensorKer, difRep3_zeta, difRep3_yinc, difRep3_kap, hon, ↓reduceIte,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    have : ξ j b = ZvecN sz E s t K n j σ ω b + YvecN sz E s t K n j σ ω b := by
      simp only [hξ, YvecN]; ring
    rw [this]; ring
  -- Step 3: the crude bound on `‖W‖_∞`
  have hVQ0 : 0 ≤ difRep3_VQ N m := by unfold difRep3_VQ difRep3_Mee; positivity
  have hkΔ : (k : ℝ) * Δ ≤ 1 :=
    ((mul_le_mul_of_nonneg_right (by exact_mod_cast hk : (k : ℝ) ≤ K n) hΔ)).trans hKΔ
  have haSum : ∀ a' : Fin m → Zd d (sz.L n),
      ∑ j ∈ Finset.range k, difRep3_aSeq sz E s t K n Q σ vp a' j ω ≤ difRep3_VQ N m := by
    intro a'
    have hterm : ∀ j ∈ Finset.range k,
        difRep3_aSeq sz E s t K n Q σ vp a' j ω ≤ Δ * difRep3_VQ N m := fun j hj =>
      difRep3_aSeq_le sz E s t K n j hE hs0 hst hK ((Finset.mem_range.1 hj).le.trans hk) hη Q σ
        hvp1 hvp16 a' ω
    calc ∑ j ∈ Finset.range k, difRep3_aSeq sz E s t K n Q σ vp a' j ω
        ≤ ∑ j ∈ Finset.range k, Δ * difRep3_VQ N m := Finset.sum_le_sum hterm
      _ = (k : ℝ) * Δ * difRep3_VQ N m := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
      _ ≤ 1 * difRep3_VQ N m := mul_le_mul_of_nonneg_right hkΔ hVQ0
      _ = difRep3_VQ N m := one_mul _
  have haSum0 : ∀ a' : Fin m → Zd d (sz.L n),
      0 ≤ ∑ j ∈ Finset.range k, difRep3_aSeq sz E s t K n Q σ vp a' j ω := fun a' =>
    Finset.sum_nonneg fun j _ => difRep3_aSeq_nonneg sz E s t K n hst Q σ vp a' j ω
  have hZ' : ∀ a' : Fin m → Zd d (sz.L n),
      ‖∑ j ∈ Finset.range k, difRep3_zeta sz E s t K n Q σ vp a' j ω‖ ≤
        ρ * Real.sqrt (difRep3_VQ N m + δ) := by
    intro a'
    refine (hZg a').trans (mul_le_mul_of_nonneg_left ?_ hρ)
    rw [← Real.sqrt_eq_rpow]
    exact Real.sqrt_le_sqrt (by linarith [haSum a'])
  have hWa : ∀ a' : Fin m → Zd d (sz.L n), ‖W a'‖ ≤ ρ * Real.sqrt (difRep3_VQ N m + δ) + xY := by
    intro a'
    rw [hW a']
    exact (norm_add_le _ _).trans (add_le_add (hZ' a') (hYg a'))
  have hWmax0 : 0 ≤ ρ * Real.sqrt (difRep3_VQ N m + δ) + xY := by positivity
  have hWsup : ‖W‖ ≤ ρ * Real.sqrt (difRep3_VQ N m + δ) + xY :=
    (pi_norm_le_iff_of_nonneg hWmax0).2 hWa
  -- Step 4: the kernel transfer (f1)
  have hε : |uk - vp| * (1 - uk)⁻¹ ≤ 16 * N * ρ₁ := by
    rw [abs_sub_comm, abs_of_nonneg (by linarith)]
    calc (vp - uk) * (1 - uk)⁻¹ ≤ ρ₁ * (16 * N) :=
          mul_le_mul hvpuk' huk16 (inv_nonneg.2 (by linarith)) hρ₁
      _ = 16 * N * ρ₁ := by ring
  have hf := difRep3_norm_UN_sub_le (g := sz.lam n) (sz.three_le_L n) hE.le σ huk0 huk1 hε W a
  have herr : ‖UN d (sz.L n) (sz.lam n) (fun i' => mSigma (E n) (σ i')) vp uk W a - W a‖ ≤
      ρ * Real.sqrt δ := by
    refine hf.trans ?_
    have hc0 : 0 ≤ (m : ℝ) * (16 * N * ρ₁) * (1 + 16 * N * ρ₁) ^ (m - 1) := by positivity
    exact (mul_le_mul_of_nonneg_left hWsup hc0).trans hf1
  -- Step 5: the proxy transfer (f2)
  have hc3 : 0 ≤ difRep3_c3 N m := by unfold difRep3_c3; positivity
  have hAk : ∑ j ∈ Finset.range k, difRep3_aSeq sz E s t K n Q σ vp a j ω ≤
      ∑ j ∈ Finset.range k, Δ * ‖STeeUQM sz n (E n) (gridTime s t K n j) uk
        (pathH sz s t K n j ω) Q σ a‖ + N ^ (-D) / 4 := by
    have hterm : ∀ j ∈ Finset.range k, difRep3_aSeq sz E s t K n Q σ vp a j ω ≤
        Δ * ‖STeeUQM sz n (E n) (gridTime s t K n j) uk (pathH sz s t K n j ω) Q σ a‖ +
          Δ * (difRep3_c3 N m * ρ₁) := by
      intro j hj
      have hjk : j < k := Finset.mem_range.1 hj
      have hon : gridTime s t K n j ≤ vp := (difRep3_gridTime_mono hst hjk.le).trans hukvp
      have hju : gridTime s t K n j ≤ uk := difRep3_gridTime_mono hst hjk.le
      have hjt : gridTime s t K n j ≤ t n := difRep3_gridTime_le hst hK (hjk.le.trans hk)
      have hsub := difRep3_norm_STeeUQM_sub_le sz n hE (difRep3_gridTime_nonneg hs0 hst j) hju
        hukvp hvp1 huk16 hvp16 (hη _ hjt) (pathH_isHermitian sz s t K n j ω) Q σ a
      have h1 : ‖STeeUQM sz n (E n) (gridTime s t K n j) vp (pathH sz s t K n j ω) Q σ a‖ ≤
          ‖STeeUQM sz n (E n) (gridTime s t K n j) uk (pathH sz s t K n j ω) Q σ a‖ +
            difRep3_c3 N m * ρ₁ := by
        have h0 := norm_sub_norm_le
          (STeeUQM sz n (E n) (gridTime s t K n j) vp (pathH sz s t K n j ω) Q σ a)
          (STeeUQM sz n (E n) (gridTime s t K n j) uk (pathH sz s t K n j ω) Q σ a)
        have h2 : difRep3_c3 N m * (vp - uk) ≤ difRep3_c3 N m * ρ₁ :=
          mul_le_mul_of_nonneg_left hvpuk' hc3
        linarith
      unfold difRep3_aSeq
      simp only [hon, ↓reduceIte]
      calc Δ * ‖STeeUQM sz n (E n) (gridTime s t K n j) vp (pathH sz s t K n j ω) Q σ a‖
          ≤ Δ * (‖STeeUQM sz n (E n) (gridTime s t K n j) uk (pathH sz s t K n j ω) Q σ a‖ +
            difRep3_c3 N m * ρ₁) := mul_le_mul_of_nonneg_left h1 hΔ
        _ = _ := by ring
    calc ∑ j ∈ Finset.range k, difRep3_aSeq sz E s t K n Q σ vp a j ω
        ≤ ∑ j ∈ Finset.range k, (Δ * ‖STeeUQM sz n (E n) (gridTime s t K n j) uk
            (pathH sz s t K n j ω) Q σ a‖ + Δ * (difRep3_c3 N m * ρ₁)) := Finset.sum_le_sum hterm
      _ = ∑ j ∈ Finset.range k, Δ * ‖STeeUQM sz n (E n) (gridTime s t K n j) uk
            (pathH sz s t K n j ω) Q σ a‖ + (k : ℝ) * (Δ * (difRep3_c3 N m * ρ₁)) := by
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ ∑ j ∈ Finset.range k, Δ * ‖STeeUQM sz n (E n) (gridTime s t K n j) uk
            (pathH sz s t K n j ω) Q σ a‖ + N ^ (-D) / 4 := by
          have hc3ρ : 0 ≤ difRep3_c3 N m * ρ₁ := mul_nonneg hc3 hρ₁
          have : (k : ℝ) * (Δ * (difRep3_c3 N m * ρ₁)) =
              ((k : ℝ) * Δ) * (difRep3_c3 N m * ρ₁) := by ring
          rw [this]
          nlinarith [mul_le_mul_of_nonneg_right hkΔ hc3ρ, hf2]
  -- the conclusion
  set Ak : ℝ := ∑ j ∈ Finset.range k, Δ * ‖STeeUQM sz n (E n) (gridTime s t K n j) uk
    (pathH sz s t K n j ω) Q σ a‖ with hAkdef
  have hAk0 : 0 ≤ Ak := Finset.sum_nonneg fun j _ => mul_nonneg hΔ (norm_nonneg _)
  have hT1 : (∑ j ∈ Finset.range k, difRep3_aSeq sz E s t K n Q σ vp a j ω + δ) ^ (1 / 2 : ℝ) ≤
      (Ak + N ^ (-D)) ^ (1 / 2 : ℝ) :=
    Real.rpow_le_rpow (by linarith [haSum0 a]) (by linarith [hAk]) (by norm_num)
  have hT2 : Real.sqrt δ ≤ (Ak + N ^ (-D)) ^ (1 / 2 : ℝ) := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow hδ0.le (by linarith) (by norm_num)
  have hWa' : ‖W a‖ ≤ ρ * (∑ j ∈ Finset.range k, difRep3_aSeq sz E s t K n Q σ vp a j ω + δ) ^
      (1 / 2 : ℝ) + xY := by
    rw [hW a]
    exact (norm_add_le _ _).trans (add_le_add (hZg a) (hYg a))
  calc ‖UN d (sz.L n) (sz.lam n) (fun i' => mSigma (E n) (σ i')) vp uk W a‖
      = ‖W a + (UN d (sz.L n) (sz.lam n) (fun i' => mSigma (E n) (σ i')) vp uk W a - W a)‖ := by
        congr 1; ring
    _ ≤ ‖W a‖ + ‖UN d (sz.L n) (sz.lam n) (fun i' => mSigma (E n) (σ i')) vp uk W a - W a‖ :=
        norm_add_le _ _
    _ ≤ (ρ * (∑ j ∈ Finset.range k, difRep3_aSeq sz E s t K n Q σ vp a j ω + δ) ^
        (1 / 2 : ℝ) + xY) + ρ * Real.sqrt δ := add_le_add hWa' herr
    _ ≤ (ρ * (Ak + N ^ (-D)) ^ (1 / 2 : ℝ) + ρ * Real.sqrt δ) + ρ * Real.sqrt δ := by
        have := mul_le_mul_of_nonneg_left hT1 hρ
        linarith
    _ = ρ * (Ak + N ^ (-D)) ^ (1 / 2 : ℝ) + 2 * (ρ * Real.sqrt δ) := by ring


/-- `P_Y = 2000 ((32 N)^m C₂)² N⁸`, `C₂ = m (m+1) N (16 N)^{m+2}`: the second-moment constant of the weighted `Y`
increments (`AzumaProxyN_YfieldsW` at `S = (32 N)^m`). -/
private def difRep3_PY (N : ℝ) (m : ℕ) : ℝ :=
  2000 * ((32 * N) ^ m * (((m * (m + 1) : ℕ) : ℝ) * N * (16 * N) ^ (m + 2))) ^ 2 * N ^ 8

/-- **The tail at one size index** (steps (c)-(g) of the ticket): given the numerical budgets and the
spectral height `η_u ≥ 1/(16 N)` for `u ≤ t`, the pin of `GridRepWTailQNAt` holds at the label `(σ, a)`:
the pin's event is contained in the union over the coarse levels `p ≤ P` and the labels `a'` of the bad events of
the `Z` part (peeling, `difRep3_Z_tail`) and of the `Y` part (Doob, `difRep3_Y_tail`), by `difRep3_pathwise`. -/
private theorem difRep3_core (E s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ)
    (hE : |E n| < 2) (hs0 : 0 ≤ s n) (hst : s n ≤ t n) (ht1 : t n < 1) (hK : K n ≠ 0)
    {m : ℕ} (hm : 2 ≤ m) (Q : Finset (Fin m)) (D ε' : ℝ) (hD : 0 < D) (hε' : 0 < ε')
    (hη : ∀ u : ℝ, u ≤ t n → 1 / (16 * ((sz.size n : ℕ) : ℝ)) ≤ etaT (E n) u)
    (h1u : ∀ u : ℝ, u ≤ t n → etaT (E n) u ≤ 1 - u)
    {P : ℕ} (hP1 : 1 ≤ P) {ρ₁ : ℝ} (hPρ : 1 / (P : ℝ) ≤ ρ₁)
    (hKΔ : (K n : ℝ) * gridStep s t K n ≤ 1)
    (hshift : ((32 * ((sz.size n : ℕ) : ℝ)) ^ m) ^ 2 *
      ((m : ℝ) * (2 * m + 2) * 16 ^ (2 * m + 3) * ((sz.size n : ℕ) : ℝ) ^ (2 * m + 4)) *
        gridStep s t K n ≤ ((sz.size n : ℕ) : ℝ) ^ (-D) / 2)
    (hf2 : difRep3_c3 ((sz.size n : ℕ) : ℝ) m * ρ₁ ≤ ((sz.size n : ℕ) : ℝ) ^ (-D) / 4)
    (hf1 : (m : ℝ) * (16 * ((sz.size n : ℕ) : ℝ) * ρ₁) *
        (1 + 16 * ((sz.size n : ℕ) : ℝ) * ρ₁) ^ (m - 1) *
        (((sz.size n : ℕ) : ℝ) ^ ε' / 4 * Real.sqrt (difRep3_VQ ((sz.size n : ℕ) : ℝ) m +
            ((sz.size n : ℕ) : ℝ) ^ (-D) / 2) +
          ((sz.size n : ℕ) : ℝ) ^ ε' / 4 * Real.sqrt (((sz.size n : ℕ) : ℝ) ^ (-D) / 2)) ≤
        ((sz.size n : ℕ) : ℝ) ^ ε' / 4 * Real.sqrt (((sz.size n : ℕ) : ℝ) ^ (-D) / 2))
    (hY : ((P : ℝ) + 1) * ((sz.size n : ℕ) : ℝ) ^ m *
        (4 * (gridStep s t K n * difRep3_PY ((sz.size n : ℕ) : ℝ) m) /
          (((sz.size n : ℕ) : ℝ) ^ ε' / 4 * Real.sqrt (((sz.size n : ℕ) : ℝ) ^ (-D) / 2)) ^ 2) ≤
      ((sz.size n : ℕ) : ℝ) ^ (-D) / 4)
    (hZ : ((P : ℝ) + 1) * ((sz.size n : ℕ) : ℝ) ^ m *
        (((⌈difRep3_VQ ((sz.size n : ℕ) : ℝ) m / (((sz.size n : ℕ) : ℝ) ^ (-D) / 2)⌉₊ : ℝ) + 1) *
          (4 * Real.exp (-(((sz.size n : ℕ) : ℝ) ^ ε' / 4) ^ 2 / (16 * (m : ℝ))))) ≤
      ((sz.size n : ℕ) : ℝ) ^ (-D) / 2)
    (i : (Fin m → Bool) × (Fin m → Zd d (sz.L n))) :
    pathP sz {ω | ∃ k, k ≤ K n ∧
      ((sz.size n : ℕ) : ℝ) ^ ε' * (∑ j ∈ Finset.range k, gridStep s t K n *
          ‖STeeUQM sz n (E n) (gridTime s t K n j) (gridTime s t K n k)
            (pathH sz s t K n j ω) Q i.1 i.2‖ + ((sz.size n : ℕ) : ℝ) ^ (-D)) ^ (1 / 2 : ℝ) <
        ‖∑ j ∈ Finset.range k, zeroModeSet d (sz.L n) Q
          (UN d (sz.L n) (sz.lam n) (fun i' => mSigma (E n) (i.1 i')) (gridTime s t K n j)
            (gridTime s t K n k)
            (fun b => difRepMartN sz E s t K n (i.1, b) (j + 1) ω -
              difRepMartN sz E s t K n (i.1, b) j ω)) i.2‖} ≤
      ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-D)) := by
  set N : ℝ := ((sz.size n : ℕ) : ℝ) with hN
  have hN1 : (1 : ℝ) ≤ N := by rw [hN]; exact_mod_cast sz.one_le_size n
  have hN0 : 0 < N := by linarith
  set Δ := gridStep s t K n with hΔdef
  have hΔ : 0 ≤ Δ := ST_gridStep_nonneg s t K n hst
  have hND : 0 < N ^ (-D) := Real.rpow_pos_of_pos hN0 _
  set δ : ℝ := N ^ (-D) / 2 with hδdef
  have hδ0 : 0 < δ := by positivity
  have hNε : 1 ≤ N ^ ε' := Real.one_le_rpow hN1 hε'.le
  set ρ : ℝ := N ^ ε' / 4 with hρdef
  have hρ0 : 0 < ρ := by rw [hρdef]; linarith
  have hρ : 0 ≤ ρ := hρ0.le
  set VQ : ℝ := difRep3_VQ N m with hVQ
  have hVQ0 : 0 ≤ VQ := by rw [hVQ]; unfold difRep3_VQ difRep3_Mee; positivity
  set Lmax : ℕ := ⌈VQ / δ⌉₊ with hLmax
  set xY : ℝ := ρ * Real.sqrt δ with hxY
  have hxY0 : 0 < xY := mul_pos hρ0 (Real.sqrt_pos.2 hδ0)
  set PY : ℝ := difRep3_PY N m with hPY
  have hPY0 : 0 ≤ PY := by rw [hPY]; unfold difRep3_PY; positivity
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  -- the coarse levels
  have hvp0 : ∀ p : ℕ, 0 ≤ difRep3_vc (s n) (t n) P p := fun p =>
    hs0.trans (difRep3_vc_ge hst P p)
  have hvpt : ∀ p : ℕ, p ≤ P → difRep3_vc (s n) (t n) P p ≤ t n := fun p hp =>
    difRep3_vc_le hst hP1 hp
  have hvp1 : ∀ p : ℕ, p ≤ P → difRep3_vc (s n) (t n) P p < 1 := fun p hp =>
    (hvpt p hp).trans_lt ht1
  have hvp16 : ∀ p : ℕ, p ≤ P → (1 - difRep3_vc (s n) (t n) P p)⁻¹ ≤ 16 * N := fun p hp =>
    difRep3_inv_le hN0 (hη _ (hvpt p hp)) (h1u _ (hvpt p hp))
  -- the shift budget
  have hesum : ∑ j ∈ Finset.range (K n), difRep3_eSeq sz E s t K n ((32 * N) ^ m) m j ≤ δ := by
    have h1 := difRep2_eeShift_sum_le sz E s t K n m hst hKΔ
      (fun j hj => hη _ (difRep3_gridTime_le hst hK hj))
    have h2 : ∑ j ∈ Finset.range (K n), difRep3_eSeq sz E s t K n ((32 * N) ^ m) m j =
        ((32 * N) ^ m) ^ 2 * ∑ j ∈ Finset.range (K n), gridStep s t K n *
          eeShiftErrN d (sz.L n) (sz.W n) (E n) m (gridTime s t K n j)
            (gridTime s t K n (j + 1)) := by
      unfold difRep3_eSeq
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [h2]
    calc ((32 * N) ^ m) ^ 2 * ∑ j ∈ Finset.range (K n), gridStep s t K n *
          eeShiftErrN d (sz.L n) (sz.W n) (E n) m (gridTime s t K n j) (gridTime s t K n (j + 1))
        ≤ ((32 * N) ^ m) ^ 2 * (((m : ℝ) * (2 * m + 2) * 16 ^ (2 * m + 3) * N ^ (2 * m + 4)) *
            gridStep s t K n) := mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
      _ = ((32 * N) ^ m) ^ 2 * ((m : ℝ) * (2 * m + 2) * 16 ^ (2 * m + 3) * N ^ (2 * m + 4)) *
            gridStep s t K n := by ring
      _ ≤ δ := hshift
  -- the threshold sums
  have haL : ∀ p : ℕ, p ≤ P → ∀ (a' : Fin m → Zd d (sz.L n)) (ω : PathΩ sz),
      ∑ j ∈ Finset.range (K n), difRep3_aSeq sz E s t K n Q i.1 (difRep3_vc (s n) (t n) P p) a' j ω ≤
        2 ^ Lmax * δ := by
    intro p hp a' ω
    have hterm : ∀ j ∈ Finset.range (K n),
        difRep3_aSeq sz E s t K n Q i.1 (difRep3_vc (s n) (t n) P p) a' j ω ≤ Δ * VQ := fun j hj =>
      difRep3_aSeq_le sz E s t K n j hE hs0 hst hK (Finset.mem_range.1 hj).le hη Q i.1
        (hvp1 p hp) (hvp16 p hp) a' ω
    have hVL : VQ ≤ (Lmax : ℝ) * δ := (div_le_iff₀ hδ0).1 (Nat.le_ceil _)
    have hL2 : (Lmax : ℝ) < 2 ^ Lmax := by exact_mod_cast Nat.lt_two_pow_self
    calc ∑ j ∈ Finset.range (K n),
          difRep3_aSeq sz E s t K n Q i.1 (difRep3_vc (s n) (t n) P p) a' j ω
        ≤ ∑ j ∈ Finset.range (K n), Δ * VQ := Finset.sum_le_sum hterm
      _ = (K n : ℝ) * Δ * VQ := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
      _ ≤ 1 * VQ := mul_le_mul_of_nonneg_right hKΔ hVQ0
      _ = VQ := one_mul _
      _ ≤ (Lmax : ℝ) * δ := hVL
      _ ≤ 2 ^ Lmax * δ := mul_le_mul_of_nonneg_right hL2.le hδ0.le
  -- the bad events
  set EZ : ℕ → (Fin m → Zd d (sz.L n)) → Set (PathΩ sz) := fun p a' =>
    {ω | ∃ k, k ≤ K n ∧ ρ * (∑ j ∈ Finset.range k, difRep3_aSeq sz E s t K n Q i.1
        (difRep3_vc (s n) (t n) P p) a' j ω + δ) ^ (1 / 2 : ℝ) <
      ‖∑ j ∈ Finset.range k, difRep3_zeta sz E s t K n Q i.1 (difRep3_vc (s n) (t n) P p) a' j ω‖}
    with hEZ
  set EY : ℕ → (Fin m → Zd d (sz.L n)) → Set (PathΩ sz) := fun p a' =>
    {ω | ∃ k, k ≤ K n ∧
      xY ≤ ‖∑ j ∈ Finset.range k, difRep3_yinc sz E s t K n Q i.1 (difRep3_vc (s n) (t n) P p) a' j ω‖}
    with hEY
  have hZbad : ∀ p : ℕ, p ≤ P → ∀ a' : Fin m → Zd d (sz.L n),
      (pathP sz).real (EZ p a') ≤ ((Lmax : ℝ) + 1) * (4 * Real.exp (-ρ ^ 2 / (16 * m))) :=
    fun p hp a' => difRep3_Z_tail sz E s t K n hE hs0 hst ht1 hm Q i.1 (hvp0 p) (hvp1 p hp)
      (hvp16 p hp) a' Lmax hδ0 hρ hesum (haL p hp a')
  have hYbad : ∀ p : ℕ, p ≤ P → ∀ a' : Fin m → Zd d (sz.L n),
      (pathP sz).real (EY p a') ≤ 4 * (Δ * PY) / xY ^ 2 := by
    intro p hp a'
    have h := difRep3_Y_tail sz E s t K n hE hs0 hst ht1 i.1
      (fun j => difRep3_kap sz E s t K n Q i.1 (difRep3_vc (s n) (t n) P p) a' j)
      (S := (32 * N) ^ m) (by positivity)
      (fun j => difRep3_kap_sum_le sz E s t K n hE hs0 hst Q i.1 (hvp1 p hp) (hvp16 p hp) a' j)
      (fun j hj => hη _ (difRep3_gridTime_le hst hK hj)) (P := PY) (le_refl _) hxY0
    refine h.trans ?_
    refine div_le_div_of_nonneg_right ?_ (sq_nonneg _)
    have : (K n : ℝ) * (Δ ^ 2 * PY) = ((K n : ℝ) * Δ) * (Δ * PY) := by ring
    rw [this]
    have := mul_le_mul_of_nonneg_right hKΔ (mul_nonneg hΔ hPY0)
    linarith
  -- the pathwise inclusion
  have hincl : {ω | ∃ k, k ≤ K n ∧
      N ^ ε' * (∑ j ∈ Finset.range k, Δ * ‖STeeUQM sz n (E n) (gridTime s t K n j)
        (gridTime s t K n k) (pathH sz s t K n j ω) Q i.1 i.2‖ + N ^ (-D)) ^ (1 / 2 : ℝ) <
      ‖∑ j ∈ Finset.range k, zeroModeSet d (sz.L n) Q
        (UN d (sz.L n) (sz.lam n) (fun i' => mSigma (E n) (i.1 i')) (gridTime s t K n j)
          (gridTime s t K n k)
          (fun b => difRepMartN sz E s t K n (i.1, b) (j + 1) ω -
            difRepMartN sz E s t K n (i.1, b) j ω)) i.2‖} ⊆
      ⋃ p ∈ Finset.range (P + 1), ⋃ a' ∈ (Finset.univ : Finset (Fin m → Zd d (sz.L n))),
        (EZ p a' ∪ EY p a') := by
    intro ω hω
    obtain ⟨k, hk, hlt⟩ := hω
    by_contra hnot
    have hgood : ∀ p ∈ Finset.range (P + 1), ∀ a' : Fin m → Zd d (sz.L n),
        ω ∉ EZ p a' ∧ ω ∉ EY p a' := by
      intro p hp a'
      by_contra hcon
      apply hnot
      simp only [Set.mem_iUnion]
      refine ⟨p, hp, a', Finset.mem_univ _, ?_⟩
      by_cases h1 : ω ∈ EZ p a'
      · exact Or.inl h1
      · exact Or.inr (by_contra fun h2 => hcon ⟨h1, h2⟩)
    obtain ⟨hpP, -, -⟩ := difRep3_coarse s t K n hst hK hP1 hk
    have hmem : ⌈((k : ℝ) * P) / (K n : ℝ)⌉₊ ∈ Finset.range (P + 1) :=
      Finset.mem_range.2 (Nat.lt_succ_of_le hpP)
    have hZg : ∀ a' : Fin m → Zd d (sz.L n),
        ‖∑ j ∈ Finset.range k, difRep3_zeta sz E s t K n Q i.1
            (difRep3_vc (s n) (t n) P ⌈((k : ℝ) * P) / (K n : ℝ)⌉₊) a' j ω‖ ≤
          ρ * (∑ j ∈ Finset.range k, difRep3_aSeq sz E s t K n Q i.1
            (difRep3_vc (s n) (t n) P ⌈((k : ℝ) * P) / (K n : ℝ)⌉₊) a' j ω + δ) ^ (1 / 2 : ℝ) := by
      intro a'
      by_contra hcon
      exact (hgood _ hmem a').1 ⟨k, hk, not_le.1 hcon⟩
    have hYg : ∀ a' : Fin m → Zd d (sz.L n),
        ‖∑ j ∈ Finset.range k, difRep3_yinc sz E s t K n Q i.1
            (difRep3_vc (s n) (t n) P ⌈((k : ℝ) * P) / (K n : ℝ)⌉₊) a' j ω‖ ≤
          ρ * Real.sqrt δ := by
      intro a'
      by_contra hcon
      exact (hgood _ hmem a').2 ⟨k, hk, (not_le.1 hcon).le⟩
    have hpw := difRep3_pathwise sz E s t K n hE hs0 hst ht1 hK hm Q i.1 i.2 hη h1u hP1 hPρ D hρ
      hKΔ hf2 hf1 ω hk hZg hYg
    set Ak : ℝ := ∑ j ∈ Finset.range k, Δ * ‖STeeUQM sz n (E n) (gridTime s t K n j)
      (gridTime s t K n k) (pathH sz s t K n j ω) Q i.1 i.2‖ with hAkdef
    have hAk0 : 0 ≤ Ak := Finset.sum_nonneg fun j _ => mul_nonneg hΔ (norm_nonneg _)
    have hT0 : 0 ≤ (Ak + N ^ (-D)) ^ (1 / 2 : ℝ) := Real.rpow_nonneg (by linarith) _
    have hsq : Real.sqrt δ ≤ (Ak + N ^ (-D)) ^ (1 / 2 : ℝ) := by
      rw [Real.sqrt_eq_rpow]
      exact Real.rpow_le_rpow hδ0.le (by linarith) (by norm_num)
    have hρ4 : N ^ ε' = 4 * ρ := by rw [hρdef]; ring
    rw [hρ4] at hlt
    nlinarith [mul_le_mul_of_nonneg_left hsq hρ]
  -- the measure
  have hcard : (Fintype.card (Fin m → Zd d (sz.L n)) : ℝ) ≤ N ^ m := difRep3_card_label_le sz n m
  have hbound : (pathP sz).real (⋃ p ∈ Finset.range (P + 1),
      ⋃ a' ∈ (Finset.univ : Finset (Fin m → Zd d (sz.L n))), (EZ p a' ∪ EY p a')) ≤ N ^ (-D) := by
    calc (pathP sz).real (⋃ p ∈ Finset.range (P + 1),
          ⋃ a' ∈ (Finset.univ : Finset (Fin m → Zd d (sz.L n))), (EZ p a' ∪ EY p a'))
        ≤ ∑ p ∈ Finset.range (P + 1), (pathP sz).real
          (⋃ a' ∈ (Finset.univ : Finset (Fin m → Zd d (sz.L n))), (EZ p a' ∪ EY p a')) :=
          measureReal_biUnion_finset_le _ _
      _ ≤ ∑ p ∈ Finset.range (P + 1), ∑ a' : Fin m → Zd d (sz.L n),
          (((Lmax : ℝ) + 1) * (4 * Real.exp (-ρ ^ 2 / (16 * m))) + 4 * (Δ * PY) / xY ^ 2) := by
          refine Finset.sum_le_sum fun p hp => ?_
          have hpP : p ≤ P := Nat.lt_succ_iff.1 (Finset.mem_range.1 hp)
          refine (measureReal_biUnion_finset_le _ _).trans (Finset.sum_le_sum fun a' _ => ?_)
          exact (measureReal_union_le _ _).trans (add_le_add (hZbad p hpP a') (hYbad p hpP a'))
      _ = ((P : ℝ) + 1) * (Fintype.card (Fin m → Zd d (sz.L n)) : ℝ) *
          (((Lmax : ℝ) + 1) * (4 * Real.exp (-ρ ^ 2 / (16 * m))) + 4 * (Δ * PY) / xY ^ 2) := by
          simp only [Finset.sum_const, Finset.card_range, Finset.card_univ, nsmul_eq_mul]
          push_cast
          ring
      _ ≤ ((P : ℝ) + 1) * N ^ m *
          (((Lmax : ℝ) + 1) * (4 * Real.exp (-ρ ^ 2 / (16 * m))) + 4 * (Δ * PY) / xY ^ 2) := by
          have h0 : (0 : ℝ) ≤ ((Lmax : ℝ) + 1) * (4 * Real.exp (-ρ ^ 2 / (16 * m))) +
              4 * (Δ * PY) / xY ^ 2 := by positivity
          have hP0 : (0 : ℝ) ≤ (P : ℝ) + 1 := by positivity
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcard hP0) h0
      _ = ((P : ℝ) + 1) * N ^ m * (((Lmax : ℝ) + 1) * (4 * Real.exp (-ρ ^ 2 / (16 * m)))) +
          ((P : ℝ) + 1) * N ^ m * (4 * (Δ * PY) / xY ^ 2) := by ring
      _ ≤ N ^ (-D) / 2 + N ^ (-D) / 4 := add_le_add hZ hY
      _ ≤ N ^ (-D) := by linarith
  calc pathP sz {ω | ∃ k, k ≤ K n ∧
        N ^ ε' * (∑ j ∈ Finset.range k, Δ * ‖STeeUQM sz n (E n) (gridTime s t K n j)
          (gridTime s t K n k) (pathH sz s t K n j ω) Q i.1 i.2‖ + N ^ (-D)) ^ (1 / 2 : ℝ) <
        ‖∑ j ∈ Finset.range k, zeroModeSet d (sz.L n) Q
          (UN d (sz.L n) (sz.lam n) (fun i' => mSigma (E n) (i.1 i')) (gridTime s t K n j)
            (gridTime s t K n k)
            (fun b => difRepMartN sz E s t K n (i.1, b) (j + 1) ω -
              difRepMartN sz E s t K n (i.1, b) j ω)) i.2‖}
      ≤ pathP sz (⋃ p ∈ Finset.range (P + 1),
          ⋃ a' ∈ (Finset.univ : Finset (Fin m → Zd d (sz.L n))), (EZ p a' ∪ EY p a')) :=
        measure_mono hincl
    _ = ENNReal.ofReal ((pathP sz).real (⋃ p ∈ Finset.range (P + 1),
          ⋃ a' ∈ (Finset.univ : Finset (Fin m → Zd d (sz.L n))), (EZ p a' ∪ EY p a'))) := by
        rw [ofReal_measureReal (measure_ne_top _ _)]
    _ ≤ ENNReal.ofReal (N ^ (-D)) := ENNReal.ofReal_le_ofReal hbound

end Pathwise

/-! ## 8. The numerical budgets (pure real arithmetic)

With `N ≥ 1`, `ND = N^D ≥ 1`, `N^{-D} = ND⁻¹`, the coarse grid `P = ⌈N^{4m+6} ND⌉` (`C' = 4m + D + 6`) and the fine grid
`Δ N^{9m+22} ND³ ≤ 1` (`CK = 9m + 3D + 22`), the budgets (B1)-(B4) of `difRep3_core` hold once `N` exceeds a constant depending on `m`; the `Z` budget (B5)
is `difRep3_budget_Z` together with the eventual inequality of `difRep3_eventually_Z`. -/

section Budgets

/-- `VQ`, `PY` and `c₃` are `const(m) · N^k`. -/
private theorem difRep3_VQ_eq (N : ℝ) (m : ℕ) :
    difRep3_VQ N m = difRep3_VQ 1 m * N ^ (4 * m + 3) := by
  unfold difRep3_VQ difRep3_Mee
  ring

private theorem difRep3_PY_eq (N : ℝ) (m : ℕ) :
    difRep3_PY N m = difRep3_PY 1 m * N ^ (4 * m + 14) := by
  unfold difRep3_PY
  ring

private theorem difRep3_c3_eq (N : ℝ) (m : ℕ) (hm : 1 ≤ m) :
    difRep3_c3 N m = difRep3_c3 1 m * N ^ (4 * m + 4) := by
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  unfold difRep3_c3
  simp only [Nat.add_sub_cancel]
  ring

/-- The constant of the shift budget: `((32 N)^m)² · m (2m+2) 16^{2m+3} N^{2m+4} = c_shift N^{4m+4}`. -/
private def difRep3_cShift (m : ℕ) : ℝ :=
  ((32 : ℝ) ^ m) ^ 2 * ((m : ℝ) * (2 * m + 2) * 16 ^ (2 * m + 3))

private theorem difRep3_cShift_nonneg (m : ℕ) : 0 ≤ difRep3_cShift m := by
  unfold difRep3_cShift; positivity

/-- **(B1) the shift budget.** -/
private theorem difRep3_budget_shift {N ND Δ : ℝ} (m : ℕ) (hN : 1 ≤ N) (hND : 1 ≤ ND)
    (hΔ0 : 0 ≤ Δ) (hΔ : Δ * (N ^ (9 * m + 22) * ND ^ 3) ≤ 1)
    (hbig : 2 * difRep3_cShift m ≤ N) :
    ((32 * N) ^ m) ^ 2 * ((m : ℝ) * (2 * m + 2) * 16 ^ (2 * m + 3) * N ^ (2 * m + 4)) * Δ ≤
      ND⁻¹ / 2 := by
  have hND0 : 0 < ND := by linarith
  have hN0 : 0 < N := by linarith
  have h1 : ((32 * N) ^ m) ^ 2 * ((m : ℝ) * (2 * m + 2) * 16 ^ (2 * m + 3) * N ^ (2 * m + 4)) * Δ =
      difRep3_cShift m * (N ^ (4 * m + 4) * Δ) := by
    unfold difRep3_cShift; ring
  rw [h1, le_div_iff₀ (by norm_num : (0 : ℝ) < 2), ← one_div, le_div_iff₀ hND0]
  have h2 : 2 * difRep3_cShift m ≤ N ^ (5 * m + 18) * ND ^ 2 :=
    hbig.trans (calc N ≤ N ^ (5 * m + 18) := le_self_pow₀ hN (by omega)
      _ ≤ N ^ (5 * m + 18) * ND ^ 2 :=
        le_mul_of_one_le_right (by positivity) (one_le_pow₀ hND))
  calc difRep3_cShift m * (N ^ (4 * m + 4) * Δ) * 2 * ND
      = (2 * difRep3_cShift m) * (N ^ (4 * m + 4) * ND * Δ) := by ring
    _ ≤ (N ^ (5 * m + 18) * ND ^ 2) * (N ^ (4 * m + 4) * ND * Δ) :=
        mul_le_mul_of_nonneg_right h2 (by positivity)
    _ = Δ * (N ^ (9 * m + 22) * ND ^ 3) := by ring
    _ ≤ 1 := hΔ

/-- **(B2) the proxy-transfer budget** (`C' = 4m + D + 6`): `c₃ N^{-(4m+6)} ND⁻¹ ≤ ND⁻¹/4`. -/
private theorem difRep3_budget_f2 {N ND : ℝ} (m : ℕ) (hm : 1 ≤ m) (hN : 1 ≤ N) (hND : 1 ≤ ND)
    (hbig : 4 * difRep3_c3 1 m ≤ N) :
    difRep3_c3 N m * (N ^ (4 * m + 6) * ND)⁻¹ ≤ ND⁻¹ / 4 := by
  have hN0 : 0 < N := by linarith
  have hND0 : 0 < ND := by linarith
  rw [difRep3_c3_eq N m hm]
  have hX : 0 < N ^ (4 * m + 6) * ND := by positivity
  rw [← div_eq_mul_inv, div_le_iff₀ hX]
  have h1 : ND⁻¹ / 4 * (N ^ (4 * m + 6) * ND) = N ^ (4 * m + 6) / 4 := by field_simp
  rw [h1]
  have hc : 4 * difRep3_c3 1 m ≤ N ^ 2 := hbig.trans (le_self_pow₀ hN (by norm_num))
  have h2 : N ^ (4 * m + 6) = N ^ (4 * m + 4) * N ^ 2 := by ring
  rw [h2]
  nlinarith [pow_pos hN0 (4 * m + 4)]

/-- The arithmetic of (B3): `A (√(V + δ) + √δ) ≤ √δ` from `A ≤ 1/4`, `A V ≤ δ/4`, `δ ≤ 1 ≤ V`. -/
private theorem difRep3_f1_arith {A V δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hV : 1 ≤ V)
    (hA0 : 0 ≤ A) (hA : A ≤ 1 / 4) (hAV : A * V ≤ δ / 4) :
    A * (Real.sqrt (V + δ) + Real.sqrt δ) ≤ Real.sqrt δ := by
  have h1 : δ ≤ Real.sqrt δ := by
    rw [Real.le_sqrt hδ0.le hδ0.le]; nlinarith
  have h2 : Real.sqrt (V + δ) ≤ V + δ := by
    rw [Real.sqrt_le_left (by linarith)]; nlinarith
  have h3 : 0 ≤ Real.sqrt δ := Real.sqrt_nonneg _
  nlinarith [mul_le_mul_of_nonneg_left h2 hA0, mul_le_mul_of_nonneg_right hA hδ0.le,
    mul_le_mul_of_nonneg_right hA h3]

/-- **(B3) the kernel-transfer budget** (`err1 ≤ ρ √δ`; `ρ` cancels, so the exponents are `ε'`-free). -/
private theorem difRep3_budget_f1 {N ND : ℝ} (m : ℕ) (hm : 1 ≤ m) (hN : 1 ≤ N) (hND : 1 ≤ ND)
    (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hbig : 64 * (m : ℝ) * 2 ^ m + 128 * (m : ℝ) * 2 ^ m * difRep3_VQ 1 m ≤ N) :
    (m : ℝ) * (16 * N * (N ^ (4 * m + 6) * ND)⁻¹) *
        (1 + 16 * N * (N ^ (4 * m + 6) * ND)⁻¹) ^ (m - 1) *
        (ρ * Real.sqrt (difRep3_VQ N m + ND⁻¹ / 2) + ρ * Real.sqrt (ND⁻¹ / 2)) ≤
      ρ * Real.sqrt (ND⁻¹ / 2) := by
  have hN0 : 0 < N := by linarith
  have hND0 : 0 < ND := by linarith
  set X : ℝ := N ^ (4 * m + 6) * ND with hX
  have hX0 : 0 < X := by positivity
  set ε₀ : ℝ := 16 * N * X⁻¹ with hε₀
  have hε₀0 : 0 ≤ ε₀ := by positivity
  have hVQ1' : 1 ≤ difRep3_VQ 1 m := by
    unfold difRep3_VQ difRep3_Mee
    have h32 : (1 : ℝ) ≤ (32 * 1) ^ m := one_le_pow₀ (by norm_num)
    have h16 : (1 : ℝ) ≤ (16 * 1) ^ (2 * m + 2) := one_le_pow₀ (by norm_num)
    have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
    calc (1 : ℝ) = 1 * 1 * (1 * 1 * 1) := by norm_num
      _ ≤ ((32 * 1) ^ m * (32 * 1) ^ m) * ((m : ℝ) * 1 * (16 * 1) ^ (2 * m + 2)) := by gcongr
  have hVQ1 : 1 ≤ difRep3_VQ N m := by
    rw [difRep3_VQ_eq]
    exact one_le_mul_of_one_le_of_one_le hVQ1' (one_le_pow₀ hN)
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have h2m : (2 : ℝ) ≤ 2 ^ m := by
    calc (2 : ℝ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ m := pow_le_pow_right₀ (by norm_num) hm
  have hm2 : (1 : ℝ) ≤ (m : ℝ) * 2 ^ m := by nlinarith
  have hcV0 : 0 ≤ difRep3_VQ 1 m := by linarith
  have hb1 : 64 * (m : ℝ) * 2 ^ m ≤ N := by
    have : 0 ≤ 128 * (m : ℝ) * 2 ^ m * difRep3_VQ 1 m := by positivity
    linarith
  have hb2 : 128 * (m : ℝ) * 2 ^ m * difRep3_VQ 1 m ≤ N := by
    have : 0 ≤ 64 * (m : ℝ) * 2 ^ m := by positivity
    linarith
  have hN64 : (64 : ℝ) ≤ N := by nlinarith
  -- `ε₀ ≤ 16 / N`
  have hNX : N ^ 2 ≤ X := by
    rw [hX]
    calc N ^ 2 ≤ N ^ (4 * m + 6) := pow_le_pow_right₀ hN (by omega)
      _ ≤ N ^ (4 * m + 6) * ND := le_mul_of_one_le_right (by positivity) hND
  have hε₀N : ε₀ * N ≤ 16 := by
    rw [hε₀]
    calc 16 * N * X⁻¹ * N = 16 * N ^ 2 / X := by field_simp
      _ ≤ 16 := by rw [div_le_iff₀ hX0]; nlinarith
  have hε₀1 : ε₀ ≤ 1 := by nlinarith
  have hpow : (1 + ε₀) ^ (m - 1) ≤ 2 ^ m :=
    (pow_le_pow_left₀ (by positivity) (by linarith : 1 + ε₀ ≤ 2) (m - 1)).trans
      (pow_le_pow_right₀ (by norm_num) (Nat.sub_le m 1))
  set A : ℝ := (m : ℝ) * ε₀ * (1 + ε₀) ^ (m - 1) with hAdef
  have hA0 : 0 ≤ A := by positivity
  have hAle : A ≤ (m : ℝ) * 2 ^ m * ε₀ := by
    rw [hAdef]
    calc (m : ℝ) * ε₀ * (1 + ε₀) ^ (m - 1) ≤ (m : ℝ) * ε₀ * 2 ^ m :=
          mul_le_mul_of_nonneg_left hpow (by positivity)
      _ = (m : ℝ) * 2 ^ m * ε₀ := by ring
  have hA : A ≤ 1 / 4 := by
    refine hAle.trans ?_
    have h1 : (m : ℝ) * 2 ^ m * ε₀ * N ≤ N / 4 := by
      have : (m : ℝ) * 2 ^ m * (ε₀ * N) ≤ (m : ℝ) * 2 ^ m * 16 :=
        mul_le_mul_of_nonneg_left hε₀N (by positivity)
      nlinarith
    by_contra hcon
    push Not at hcon
    nlinarith
  have hεV : ε₀ * difRep3_VQ N m = 16 * difRep3_VQ 1 m / (N ^ 2 * ND) := by
    rw [hε₀, hX, difRep3_VQ_eq N m]
    field_simp
    ring
  have hAV : A * difRep3_VQ N m ≤ ND⁻¹ / 2 / 4 := by
    calc A * difRep3_VQ N m ≤ ((m : ℝ) * 2 ^ m * ε₀) * difRep3_VQ N m :=
          mul_le_mul_of_nonneg_right hAle (by linarith)
      _ = (m : ℝ) * 2 ^ m * (ε₀ * difRep3_VQ N m) := by ring
      _ = (m : ℝ) * 2 ^ m * (16 * difRep3_VQ 1 m / (N ^ 2 * ND)) := by rw [hεV]
      _ ≤ ND⁻¹ / 2 / 4 := by
          have hden : 0 < N ^ 2 * ND := by positivity
          have e : (m : ℝ) * 2 ^ m * (16 * difRep3_VQ 1 m / (N ^ 2 * ND)) =
              ((m : ℝ) * 2 ^ m * (16 * difRep3_VQ 1 m)) / (N ^ 2 * ND) := by ring
          rw [e, div_le_iff₀ hden]
          have h3 : ND⁻¹ / 2 / 4 * (N ^ 2 * ND) = N ^ 2 / 8 := by field_simp; norm_num
          rw [h3]
          have hc : 128 * (m : ℝ) * 2 ^ m * difRep3_VQ 1 m ≤ N ^ 2 :=
            hb2.trans (le_self_pow₀ hN (by norm_num))
          nlinarith
  have hδ1 : ND⁻¹ / 2 ≤ 1 := by
    have : ND⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hND
    linarith
  have hδ0 : 0 < ND⁻¹ / 2 := by positivity
  have h := difRep3_f1_arith hδ0 hδ1 hVQ1 hA0 hA hAV
  calc (m : ℝ) * ε₀ * (1 + ε₀) ^ (m - 1) *
        (ρ * Real.sqrt (difRep3_VQ N m + ND⁻¹ / 2) + ρ * Real.sqrt (ND⁻¹ / 2))
      = ρ * (A * (Real.sqrt (difRep3_VQ N m + ND⁻¹ / 2) + Real.sqrt (ND⁻¹ / 2))) := by
        rw [hAdef]; ring
    _ ≤ ρ * Real.sqrt (ND⁻¹ / 2) := mul_le_mul_of_nonneg_left h hρ


/-- **(B4) the `Y` budget** (`CK = 9m + 3D + 22`): `(P+1) N^m 4 Δ P_Y/(ρ √δ)² ≤ ND⁻¹/4`, `ρ ≥ 1/4`,
`P + 1 ≤ 3 N^{4m+6} ND`. -/
private theorem difRep3_budget_Y {N ND Δ Pp ρ : ℝ} (m : ℕ) (hN : 1 ≤ N) (hND : 1 ≤ ND)
    (hΔ0 : 0 ≤ Δ) (hΔ : Δ * (N ^ (9 * m + 22) * ND ^ 3) ≤ 1) (hPp0 : 0 ≤ Pp)
    (hPp : Pp + 1 ≤ 3 * (N ^ (4 * m + 6) * ND)) (hρ : 1 / 4 ≤ ρ)
    (hbig : 1536 * difRep3_PY 1 m ≤ N) :
    (Pp + 1) * N ^ m * (4 * (Δ * difRep3_PY N m) / (ρ * Real.sqrt (ND⁻¹ / 2)) ^ 2) ≤ ND⁻¹ / 4 := by
  have hN0 : 0 < N := by linarith
  have hND0 : 0 < ND := by linarith
  have hPY1 : 0 ≤ difRep3_PY 1 m := by unfold difRep3_PY; positivity
  have hδ0 : 0 < ND⁻¹ / 2 := by positivity
  have hsq : (ρ * Real.sqrt (ND⁻¹ / 2)) ^ 2 = ρ ^ 2 * (ND⁻¹ / 2) := by
    rw [mul_pow, Real.sq_sqrt hδ0.le]
  have hρ2 : 1 / 16 ≤ ρ ^ 2 := by nlinarith
  have hden0 : 0 < (ρ * Real.sqrt (ND⁻¹ / 2)) ^ 2 := by
    rw [hsq]; have : 0 < ρ := by linarith
    positivity
  have hden : 1 / (32 * ND) ≤ (ρ * Real.sqrt (ND⁻¹ / 2)) ^ 2 := by
    rw [hsq]
    calc 1 / (32 * ND) = 1 / 16 * (ND⁻¹ / 2) := by field_simp; norm_num
      _ ≤ ρ ^ 2 * (ND⁻¹ / 2) := mul_le_mul_of_nonneg_right hρ2 hδ0.le
  have hPY : difRep3_PY N m = difRep3_PY 1 m * N ^ (4 * m + 14) := difRep3_PY_eq N m
  have h1 : 4 * (Δ * difRep3_PY N m) / (ρ * Real.sqrt (ND⁻¹ / 2)) ^ 2 ≤
      128 * (Δ * difRep3_PY N m) * ND := by
    rw [div_le_iff₀ hden0]
    have hpy0 : 0 ≤ Δ * difRep3_PY N m := mul_nonneg hΔ0 (by rw [hPY]; positivity)
    calc 4 * (Δ * difRep3_PY N m) = 128 * (Δ * difRep3_PY N m) * ND * (1 / (32 * ND)) := by
          field_simp; ring
      _ ≤ 128 * (Δ * difRep3_PY N m) * ND * (ρ * Real.sqrt (ND⁻¹ / 2)) ^ 2 :=
          mul_le_mul_of_nonneg_left hden (by positivity)
  have hNm0 : 0 ≤ N ^ m := by positivity
  calc (Pp + 1) * N ^ m * (4 * (Δ * difRep3_PY N m) / (ρ * Real.sqrt (ND⁻¹ / 2)) ^ 2)
      ≤ (3 * (N ^ (4 * m + 6) * ND)) * N ^ m * (128 * (Δ * difRep3_PY N m) * ND) := by
        have h0 : 0 ≤ 128 * (Δ * difRep3_PY N m) * ND := by rw [hPY]; positivity
        calc (Pp + 1) * N ^ m * (4 * (Δ * difRep3_PY N m) / (ρ * Real.sqrt (ND⁻¹ / 2)) ^ 2)
            ≤ (Pp + 1) * N ^ m * (128 * (Δ * difRep3_PY N m) * ND) :=
              mul_le_mul_of_nonneg_left h1 (by positivity)
          _ ≤ (3 * (N ^ (4 * m + 6) * ND)) * N ^ m * (128 * (Δ * difRep3_PY N m) * ND) :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hPp hNm0) h0
    _ = 384 * difRep3_PY 1 m * (Δ * (N ^ (9 * m + 20) * ND ^ 2)) := by rw [hPY]; ring
    _ ≤ ND⁻¹ / 4 := by
        rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 4), ← one_div, le_div_iff₀ hND0]
        have h2 : 1536 * difRep3_PY 1 m ≤ N ^ 2 := hbig.trans (le_self_pow₀ hN (by norm_num))
        calc 384 * difRep3_PY 1 m * (Δ * (N ^ (9 * m + 20) * ND ^ 2)) * 4 * ND
            = (1536 * difRep3_PY 1 m) * (Δ * (N ^ (9 * m + 20) * ND ^ 3)) := by ring
          _ ≤ N ^ 2 * (Δ * (N ^ (9 * m + 20) * ND ^ 3)) :=
              mul_le_mul_of_nonneg_right h2 (by positivity)
          _ = Δ * (N ^ (9 * m + 22) * ND ^ 3) := by ring
          _ ≤ 1 := hΔ


/-- **(B5) the `Z` budget, arithmetic**: from `(P+1) ≤ 3 N^{4m+6} ND`, `L + 1 ≤ 2 V_Q ND + 2` and
`24 (2 c_V + 2) N^{9m+9} ND³ E ≤ 1`, `(P+1) N^m (L+1) 4 E ≤ ND⁻¹/2`. -/
private theorem difRep3_budget_Z {N ND E Pp Lc : ℝ} (m : ℕ) (hN : 1 ≤ N) (hND : 1 ≤ ND)
    (hE0 : 0 ≤ E) (hPp0 : 0 ≤ Pp) (hPp : Pp + 1 ≤ 3 * (N ^ (4 * m + 6) * ND)) (hLc0 : 0 ≤ Lc)
    (hLc : Lc + 1 ≤ 2 * difRep3_VQ N m * ND + 2)
    (hZ : 24 * (2 * difRep3_VQ 1 m + 2) * (N ^ (9 * m + 9) * ND ^ 3) * E ≤ 1) :
    (Pp + 1) * N ^ m * ((Lc + 1) * (4 * E)) ≤ ND⁻¹ / 2 := by
  have hN0 : 0 < N := by linarith
  have hND0 : 0 < ND := by linarith
  have hcV0 : 0 ≤ difRep3_VQ 1 m := by unfold difRep3_VQ difRep3_Mee; positivity
  have hNp1 : 1 ≤ N ^ (4 * m + 3) * ND := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hN) hND
  have hL2 : Lc + 1 ≤ (2 * difRep3_VQ 1 m + 2) * (N ^ (4 * m + 3) * ND) := by
    refine hLc.trans ?_
    rw [difRep3_VQ_eq N m]
    nlinarith [mul_nonneg hcV0 (by positivity : (0 : ℝ) ≤ N ^ (4 * m + 3) * ND)]
  have hLc1 : 0 ≤ Lc + 1 := by linarith
  calc (Pp + 1) * N ^ m * ((Lc + 1) * (4 * E))
      ≤ (3 * (N ^ (4 * m + 6) * ND)) * N ^ m *
        (((2 * difRep3_VQ 1 m + 2) * (N ^ (4 * m + 3) * ND)) * (4 * E)) := by
        gcongr
    _ = 12 * (2 * difRep3_VQ 1 m + 2) * (N ^ (9 * m + 9) * ND ^ 2) * E := by ring
    _ ≤ ND⁻¹ / 2 := by
        rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2), ← one_div, le_div_iff₀ hND0]
        calc 12 * (2 * difRep3_VQ 1 m + 2) * (N ^ (9 * m + 9) * ND ^ 2) * E * 2 * ND
            = 24 * (2 * difRep3_VQ 1 m + 2) * (N ^ (9 * m + 9) * ND ^ 3) * E := by ring
          _ ≤ 1 := hZ

end Budgets

/-! ## 9. The asymptotics and the tail at one size index -/

section Asymptotics

/-- A polynomial against a stretched exponential: `N^s e^{-b N^c} → 0` (copy of the private
`difRepTail_tendsto_rpow_exp`, `Path/DifREP2.lean:2098`, RBM3D `76b840e`). -/
private theorem difRep3_tendsto_rpow_exp (s b c : ℝ) (hb : 0 < b) (hc : 0 < c) :
    Tendsto (fun N : ℝ => N ^ s * Real.exp (-b * N ^ c)) atTop (nhds 0) := by
  have h1 := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (s / c) b hb
  have h2 : Tendsto (fun N : ℝ => N ^ c) atTop atTop := tendsto_rpow_atTop hc
  have h3 := h1.comp h2
  refine h3.congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with N hN
  simp only [Function.comp]
  rw [← Real.rpow_mul hN]
  congr 2
  field_simp

/-- **The `Z` budget holds for large `N`**: `24 (2 c_V + 2) N^{9m+9} (N^D)³ exp (-(N^{ε'}/4)²/(16 m)) ≤ 1` eventually
(a polynomial against a stretched exponential; the only place `ε'` enters). -/
private theorem difRep3_eventually_Z (m : ℕ) (hm : 0 < m) (D ε' : ℝ) (hD : 0 < D) (hε' : 0 < ε') :
    ∀ᶠ N : ℝ in atTop, 1 ≤ N ∧
      24 * (2 * difRep3_VQ 1 m + 2) * (N ^ (9 * m + 9) * (N ^ D) ^ 3) *
        Real.exp (-(N ^ ε' / 4) ^ 2 / (16 * (m : ℝ))) ≤ 1 := by
  set c₄ : ℝ := 24 * (2 * difRep3_VQ 1 m + 2) with hc₄
  have hc₄0 : 0 < c₄ := by
    have : 0 ≤ difRep3_VQ 1 m := by unfold difRep3_VQ difRep3_Mee; positivity
    rw [hc₄]; positivity
  set q : ℝ := ((9 * m + 9 : ℕ) : ℝ) + D * 3 with hq
  have hlim := difRep3_tendsto_rpow_exp q (1 / (256 * (m : ℝ))) (2 * ε') (by positivity)
    (by positivity)
  have hev := hlim.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < 1 / c₄))
  filter_upwards [hev, eventually_ge_atTop (1 : ℝ)] with N hN hN1
  refine ⟨hN1, ?_⟩
  have hN0 : 0 < N := by linarith
  have h1 : N ^ (9 * m + 9) * (N ^ D) ^ 3 = N ^ q := by
    rw [hq, Real.rpow_add hN0, Real.rpow_natCast, Real.rpow_mul hN0.le]
    norm_num
  have h2 : -(N ^ ε' / 4) ^ 2 / (16 * (m : ℝ)) = -(1 / (256 * (m : ℝ))) * N ^ (2 * ε') := by
    have : (N ^ ε') ^ 2 = N ^ (2 * ε') := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]
      congr 1
      push_cast
      ring
    rw [div_pow, this]
    have hm0 : (m : ℝ) ≠ 0 := by positivity
    field_simp
    ring
  rw [h1, h2]
  have hlt : N ^ q * Real.exp (-(1 / (256 * (m : ℝ))) * N ^ (2 * ε')) < 1 / c₄ := hN
  calc c₄ * N ^ q * Real.exp (-(1 / (256 * (m : ℝ))) * N ^ (2 * ε'))
      = c₄ * (N ^ q * Real.exp (-(1 / (256 * (m : ℝ))) * N ^ (2 * ε'))) := by ring
    _ ≤ c₄ * (1 / c₄) := mul_le_mul_of_nonneg_left hlt.le hc₄0.le
    _ = 1 := by field_simp

/-- `N^{9m + 3D + 22} = N^{9m+22} (N^D)³` (`CK = 9m + 3D + 22`). -/
private theorem difRep3_rpow_CK {N : ℝ} (hN : 0 < N) (m : ℕ) (D : ℝ) :
    N ^ (9 * (m : ℝ) + 3 * D + 22) = N ^ (9 * m + 22) * (N ^ D) ^ 3 := by
  have h1 : (9 * (m : ℝ) + 3 * D + 22) = ((9 * m + 22 : ℕ) : ℝ) + D * 3 := by push_cast; ring
  rw [h1, Real.rpow_add hN, Real.rpow_natCast, Real.rpow_mul hN.le]
  norm_num

/-- The constant `N₀(m)` beyond which the deterministic budgets hold (`ε'`-free). -/
private def difRep3_Cbig (m : ℕ) : ℝ :=
  1 + 2 * difRep3_cShift m + 4 * difRep3_c3 1 m +
    (64 * (m : ℝ) * 2 ^ m + 128 * (m : ℝ) * 2 ^ m * difRep3_VQ 1 m) + 1536 * difRep3_PY 1 m

variable {d : ℕ} (sz : Sizes d)

/-- **The tail at one size index**: given `η_u ≥ 1/(16 N)` for `u ≤ t`, `K ≥ N^{9m+3D+22}`, `N ≥ N₀(m)` and the
`Z` budget, the pin of `GridRepWTailQNAt` holds at the label `(σ, a)`, with the coarse grid
`P = ⌈N^{4m+6} N^D⌉` (`C' = 4m + D + 6`). -/
private theorem difRep3_tail_at (E s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ)
    (hE : |E n| < 2) (hs0 : 0 ≤ s n) (hst : s n ≤ t n) (ht1 : t n < 1) (hK : K n ≠ 0)
    {m : ℕ} (hm : 2 ≤ m) (Q : Finset (Fin m)) (D ε' : ℝ) (hD : 0 < D) (hε' : 0 < ε')
    (hη : ∀ u : ℝ, u ≤ t n → 1 / (16 * ((sz.size n : ℕ) : ℝ)) ≤ etaT (E n) u)
    (h1u : ∀ u : ℝ, u ≤ t n → etaT (E n) u ≤ 1 - u)
    (hKN : ((sz.size n : ℕ) : ℝ) ^ (9 * (m : ℝ) + 3 * D + 22) ≤ K n)
    (hbig : difRep3_Cbig m ≤ ((sz.size n : ℕ) : ℝ))
    (hZ : 24 * (2 * difRep3_VQ 1 m + 2) *
        (((sz.size n : ℕ) : ℝ) ^ (9 * m + 9) * (((sz.size n : ℕ) : ℝ) ^ D) ^ 3) *
        Real.exp (-(((sz.size n : ℕ) : ℝ) ^ ε' / 4) ^ 2 / (16 * (m : ℝ))) ≤ 1)
    (i : (Fin m → Bool) × (Fin m → Zd d (sz.L n))) :
    pathP sz {ω | ∃ k, k ≤ K n ∧
      ((sz.size n : ℕ) : ℝ) ^ ε' * (∑ j ∈ Finset.range k, gridStep s t K n *
          ‖STeeUQM sz n (E n) (gridTime s t K n j) (gridTime s t K n k)
            (pathH sz s t K n j ω) Q i.1 i.2‖ + ((sz.size n : ℕ) : ℝ) ^ (-D)) ^ (1 / 2 : ℝ) <
        ‖∑ j ∈ Finset.range k, zeroModeSet d (sz.L n) Q
          (UN d (sz.L n) (sz.lam n) (fun i' => mSigma (E n) (i.1 i')) (gridTime s t K n j)
            (gridTime s t K n k)
            (fun b => difRepMartN sz E s t K n (i.1, b) (j + 1) ω -
              difRepMartN sz E s t K n (i.1, b) j ω)) i.2‖} ≤
      ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-D)) := by
  set N : ℝ := ((sz.size n : ℕ) : ℝ) with hN
  have hN1 : (1 : ℝ) ≤ N := by rw [hN]; exact_mod_cast sz.one_le_size n
  have hN0 : 0 < N := by linarith
  set Δ := gridStep s t K n with hΔdef
  have hΔ0 : 0 ≤ Δ := ST_gridStep_nonneg s t K n hst
  have hKΔ : (K n : ℝ) * Δ ≤ 1 := by
    rw [hΔdef, difRep3_K_mul_step s t K n hK]; linarith
  set ND : ℝ := N ^ D with hNDdef
  have hND1 : 1 ≤ ND := Real.one_le_rpow hN1 hD.le
  have hND0 : 0 < ND := by linarith
  have hNmD : N ^ (-D) = ND⁻¹ := Real.rpow_neg hN0.le D
  have hΔN : Δ * (N ^ (9 * m + 22) * ND ^ 3) ≤ 1 := by
    have h1 : N ^ (9 * (m : ℝ) + 3 * D + 22) = N ^ (9 * m + 22) * ND ^ 3 :=
      difRep3_rpow_CK hN0 m D
    calc Δ * (N ^ (9 * m + 22) * ND ^ 3) = Δ * N ^ (9 * (m : ℝ) + 3 * D + 22) := by rw [h1]
      _ ≤ Δ * K n := mul_le_mul_of_nonneg_left hKN hΔ0
      _ = (K n : ℝ) * Δ := mul_comm _ _
      _ ≤ 1 := hKΔ
  -- the coarse grid
  set X : ℝ := N ^ (4 * m + 6) * ND with hXdef
  have hX1 : 1 ≤ X := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hN1) hND1
  have hX0 : 0 < X := by linarith
  set P : ℕ := ⌈X⌉₊ with hPdef
  have hP1 : 1 ≤ P := Nat.one_le_iff_ne_zero.2 (Nat.pos_iff_ne_zero.1 (Nat.ceil_pos.2 hX0))
  have hXP : X ≤ (P : ℝ) := Nat.le_ceil X
  have hP3 : (P : ℝ) + 1 ≤ 3 * X := by
    have := Nat.ceil_lt_add_one hX0.le
    linarith
  have hPρ : 1 / (P : ℝ) ≤ X⁻¹ := by
    rw [← one_div]; exact one_div_le_one_div_of_le hX0 hXP
  -- the constants
  have hcs := difRep3_cShift_nonneg m
  have hc3 : 0 ≤ difRep3_c3 1 m := by unfold difRep3_c3; positivity
  have hVQ1 : 0 ≤ difRep3_VQ 1 m := by unfold difRep3_VQ difRep3_Mee; positivity
  have hPY1 : 0 ≤ difRep3_PY 1 m := by unfold difRep3_PY; positivity
  have hb64 : 0 ≤ 64 * (m : ℝ) * 2 ^ m + 128 * (m : ℝ) * 2 ^ m * difRep3_VQ 1 m := by positivity
  have hbig_shift : 2 * difRep3_cShift m ≤ N := by unfold difRep3_Cbig at hbig; linarith
  have hbig_f2 : 4 * difRep3_c3 1 m ≤ N := by unfold difRep3_Cbig at hbig; linarith
  have hbig_f1 : 64 * (m : ℝ) * 2 ^ m + 128 * (m : ℝ) * 2 ^ m * difRep3_VQ 1 m ≤ N := by
    unfold difRep3_Cbig at hbig; linarith
  have hbig_Y : 1536 * difRep3_PY 1 m ≤ N := by unfold difRep3_Cbig at hbig; linarith
  have hm1 : 1 ≤ m := by omega
  have hρ0 : 0 ≤ N ^ ε' / 4 := by positivity
  have hρ14 : 1 / 4 ≤ N ^ ε' / 4 := by
    have := Real.one_le_rpow hN1 hε'.le
    linarith
  refine difRep3_core sz E s t K n hE hs0 hst ht1 hK hm Q D ε' hD hε' hη h1u hP1 hPρ hKΔ
    ?_ ?_ ?_ ?_ ?_ i
  · rw [hNmD]; exact difRep3_budget_shift m hN1 hND1 hΔ0 hΔN hbig_shift
  · rw [hNmD]; exact difRep3_budget_f2 m hm1 hN1 hND1 hbig_f2
  · rw [hNmD]; exact difRep3_budget_f1 m hm1 hN1 hND1 _ hρ0 hbig_f1
  · rw [hNmD]
    exact difRep3_budget_Y m hN1 hND1 hΔ0 hΔN (Nat.cast_nonneg _) hP3 hρ14 hbig_Y
  · rw [hNmD]
    have hVQ0 : 0 ≤ difRep3_VQ N m := by unfold difRep3_VQ difRep3_Mee; positivity
    have hceil : ((⌈difRep3_VQ N m / (ND⁻¹ / 2)⌉₊ : ℕ) : ℝ) + 1 ≤ 2 * difRep3_VQ N m * ND + 2 := by
      have h0 : 0 ≤ difRep3_VQ N m / (ND⁻¹ / 2) := by positivity
      have := Nat.ceil_lt_add_one h0
      have e : difRep3_VQ N m / (ND⁻¹ / 2) = 2 * difRep3_VQ N m * ND := by
        field_simp
      linarith
    exact difRep3_budget_Z m hN1 hND1 (Real.exp_pos _).le (Nat.cast_nonneg _) hP3
      (Nat.cast_nonneg _) hceil hZ

end Asymptotics


/-! ## 10. Targets 5-7 -/

/-- **Target 5, `gridRepWTailQN_holds`**: the `Q^{(A)} ∘ 𝒰`-weighted martingale tail (clause (iv) of `STGridRepNAt`,
zero-mode-removed form), at every loop length `m ≥ 2`, every `Q`, every `d` (no input is stated only for `d ≥ 3`).
The grid exponent is `CK = 9m + 3D + 22` (the coarse time grid `P = ⌈N^{C'}⌉`, `C' = 4m + D + 6`; both depend on
`m, D` only, not on `ε'`, `Q`, `κ`, `ε`).  Route (T2200): a coarse time grid `v_0 < … < v_P` of `[s, t]` independent
of `K`; for each `(p, a')` the sums `Σ_{j<k} Q 𝒰_{u_j,v_p} Z_j` (peeling `difRep2_peel`) and
`Σ_{j<k} Q 𝒰_{u_j,v_p} Y_j` (Doob, weights depending on `j`) are martingales in `k`; the exact transfer
`Σ_{j<k} Q 𝒰_{u_j,u_k} ξ_j = 𝒰_{v_p,u_k} W^p_k` (`difRep3_UN_transfer`) and the kernel and proxy transfers
(`difRep3_norm_UN_sub_le`, `difRep3_norm_STeeUQM_sub_le`) end the proof (`difRep3_pathwise`, `difRep3_core`). -/
theorem gridRepWTailQN_holds :
    ∀ d m : ℕ, 2 ≤ m → ∀ Q : Finset (Fin m), GridRepWTailQNAt d m Q := by
  intro d m hm Q κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hz s t hs hst htT D hD
  refine ⟨9 * (m : ℝ) + 3 * D + 22, by positivity, ?_⟩
  intro K hK0 hKN ε' hε'
  have hfl : ∀ n, |STflowE z n| ≤ 2 - κ ∧ lemT (z n) < 1 := fun n =>
    let h := difRep_flow_bounds sz hκ hz n (htT n)
    ⟨h.1, h.2.1⟩
  have hE : ∀ n, |STflowE z n| < 2 := fun n => by linarith [(hfl n).1]
  have ht1 : ∀ n, t n < 1 := fun n => lt_of_le_of_lt (htT n) (hfl n).2
  have hsize : sz.SizeTendsto := hz.1.2.2.1
  have hbig := hsize.eventually (eventually_ge_atTop (difRep3_Cbig m))
  have hZev := hsize.eventually (difRep3_eventually_Z m (by omega) D ε' hD hε')
  filter_upwards [hKN, hbig, hZev] with n hKNn hbign hZn
  intro i
  obtain ⟨hN1, hZn⟩ := hZn
  have hη : ∀ u : ℝ, u ≤ t n →
      1 / (16 * ((sz.size n : ℕ) : ℝ)) ≤ etaT (STflowE z n) u := by
    intro u hu
    have h := (difRep_flow_bounds sz hκ hz n (hu.trans (htT n))).2.2.1
    refine le_trans ?_ h
    have h2 : ((sz.size n : ℕ) : ℝ) ^ (-1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ (-1 + ε) :=
      Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
    rw [Real.rpow_neg_one] at h2
    calc 1 / (16 * ((sz.size n : ℕ) : ℝ)) = ((sz.size n : ℕ) : ℝ)⁻¹ / 16 := by field_simp
      _ ≤ ((sz.size n : ℕ) : ℝ) ^ (-1 + ε) / 16 := by gcongr
  have h1u : ∀ u : ℝ, u ≤ t n → etaT (STflowE z n) u ≤ 1 - u := fun u hu =>
    (difRep_flow_bounds sz hκ hz n (hu.trans (htT n))).2.2.2
  exact difRep3_tail_at sz (STflowE z) s t K n (hE n) (hs n) (hst n) (ht1 n) (hK0 n) hm Q D ε' hD
    hε' hη h1u hKNn hbign hZn i

/-- **Target 6, `gridRepWTailN_holds`**: clause (iv) as pinned by T2168 (`Q = ∅`), every `d` and `m ≥ 2`. -/
theorem gridRepWTailN_holds : ∀ d m : ℕ, 2 ≤ m → GridRepWTailNAt d m :=
  fun d m hm => gridRepWTailN_of_Q d m (gridRepWTailQN_holds d m hm ∅)

/-- **Target 7, `stGridRepN_holds`**: the pin `STGridRepN` is unconditional for `3 ≤ d` (`C₀ = m + 9`;
`stGridRepN_of_tails`, `gridRepTailN_holds`, target 6).  `3 ≤ d` enters only through `stGridRepN_of_tails`
(`gridRepRemN_holds`, `stKbound_of_flow`, DECISIONS §36): targets 1-6 hold for every `d`. -/
theorem stGridRepN_holds : ∀ d : ℕ, 3 ≤ d → STGridRepN d :=
  fun d hd => stGridRepN_of_tails d hd (gridRepTailN_holds d) (gridRepWTailN_holds d)

end RBM.Ind

namespace RBM.Ind.DifREP3Inst

open MeasureTheory ProbabilityTheory Filter RBM RBM.Loop RBM.Gauss RBM.Gauss.Sizes RBM.Path RBM.Ind
  RBM.Gauss.SizesInst RBM.Gauss.InductionDefsInst RBM.Gauss.Step2DefsInst

/-! ## 11. Compiled nonempty instances at `d = 3`

The size data are the merged preflight sequence `sz0` (`d = 3`, `L_n = 4 (n+1)`, `W_n = (2 (n+1))^5`,
`N_0 = 2097152`) and the flow block of `Induction/Defs.lean` (`z0`, `flow_z0` with `κ = ε = 𝔡 = 1/10`, `𝔠 = 1/6`,
`s ≡ 0`, `t ≡ 1/16 ≤ lemT z0`), as in `DifREP2Inst`.  Targets 1, 3, 4 are applied at `n = 0` (`L = 4`,
`g = lam 0`, `E = 1/2`, the loop `(+,-,+)`, `Q = {0}`); target 5 at the flow data for `(m, Q) = (2, {0})` and
`(3, ∅)`, with the grid exponent `CK` it returns and `K_n = ⌈N_n^{CK}⌉ + 1`; targets 6, 7 at `d = 3`.  Every
deterministic hypothesis is discharged; what stays a hypothesis of the chain instance are the other gates' pins. -/

theorem hs0 : ∀ n, 0 ≤ sInst n := fun _ => le_rfl

theorem hst : ∀ n, sInst n ≤ tInst n := fun n => by simp only [sInst, tInst]; norm_num

theorem htT : ∀ n, tInst n ≤ lemT (z0 n) := fun n => sixteenth_le_lemT n

/-- The instance grid is nondegenerate: `K ≡ 4` on `[0, 1/16]` has `Δ = 1/64`. -/
theorem gridStep_inst : gridStep sInst tInst (fun _ => 4) 0 = 1 / 64 := by
  norm_num [gridStep, sInst, tInst]

/-- The loop `(+,-,+)` of length `3`. -/
def σ3 : Fin 3 → Bool := ![true, false, true]

/-- The label `a = 0`. -/
def a0 : Fin 3 → Zd 3 (sz0.L 0) := fun _ => 0

/-- **Target 1, `STeeUQM_empty`, at the data** (`n = 0`, `E = 1/2`, `v = 0`, `w = 1/16`, `H = 0`). -/
example :
    STeeUQM sz0 0 (1 / 2) 0 (1 / 16)
        (0 : Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ)
        (∅ : Finset (Fin 3)) σ3 a0 =
      sz0.STeeUM 0 (1 / 2) 0 (1 / 16)
        (0 : Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ) σ3 a0 :=
  STeeUQM_empty sz0 0 (1 / 2) 0 (1 / 16) 0 σ3 a0

/-- **Target 3, `zeroModeSet_UN_eq_uKerQ`, at the data** (`L = 4`, `g = lam 0`, `E = 1/2`, `Q = {0}`,
`v = 0`, `w = 1/16`, the tensor `A ≡ 1`). -/
example :
    zeroModeSet 3 (sz0.L 0) ({0} : Finset (Fin 3))
        (UN 3 (sz0.L 0) (sz0.lam 0) (fun i => mSigma (1 / 2) (σ3 i)) 0 (1 / 16)
          (fun _ : Fin 3 → Zd 3 (sz0.L 0) => (1 : ℂ))) =
      tensorKer 3 (sz0.L 0) (uKerQ 3 (sz0.L 0) (sz0.lam 0) (1 / 2) ({0} : Finset (Fin 3)) σ3 0
        (1 / 16)) (fun _ : Fin 3 → Zd 3 (sz0.L 0) => (1 : ℂ)) :=
  zeroModeSet_UN_eq_uKerQ (sz0.lam 0) (1 / 2) ({0} : Finset (Fin 3)) σ3 0 (1 / 16) _

/-- **Target 4, `difRep3_UN_transfer`, at the data** (`L = 4`, `g = lam 0`, `E = 1/2`, `Q = {0}`,
`v = 1/32`, `w = 1/16`, `k = 4`, `u_j` the grid times of `K ≡ 4`, `A_j ≡ 1`). -/
example :
    ∑ j ∈ Finset.range 4, zeroModeSet 3 (sz0.L 0) ({0} : Finset (Fin 3))
        (UN 3 (sz0.L 0) (sz0.lam 0) (fun i => mSigma (1 / 2) (σ3 i))
          (gridTime sInst tInst (fun _ => 4) 0 j) (1 / 16)
          (fun _ : Fin 3 → Zd 3 (sz0.L 0) => (1 : ℂ))) =
      UN 3 (sz0.L 0) (sz0.lam 0) (fun i => mSigma (1 / 2) (σ3 i)) (1 / 32) (1 / 16)
        (∑ j ∈ Finset.range 4, zeroModeSet 3 (sz0.L 0) ({0} : Finset (Fin 3))
          (UN 3 (sz0.L 0) (sz0.lam 0) (fun i => mSigma (1 / 2) (σ3 i))
            (gridTime sInst tInst (fun _ => 4) 0 j) (1 / 32)
            (fun _ : Fin 3 → Zd 3 (sz0.L 0) => (1 : ℂ)))) :=
  difRep3_UN_transfer (d := 3) (sz0.lam 0) (sz0.three_le_L 0) (E := 1 / 2) (by norm_num) σ3
    ({0} : Finset (Fin 3)) (v := 1 / 32) (w := 1 / 16) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) 4 (fun j => gridTime sInst tInst (fun _ => 4) 0 j)
    (fun _ _ => (1 : ℂ))

/-- Targets 1, 3, 4 again at nonconstant data: `H = 1` (the identity, Hermitian and nonzero), the tensors
`A b = (b_0)_0` and `A_j b = j + (b_0)_0` (the `ZMod 4` representative of the first coordinate of the first index). -/
example :
    STeeUQM sz0 0 (1 / 2) 0 (1 / 16)
        (1 : Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ)
        (∅ : Finset (Fin 3)) σ3 a0 =
      sz0.STeeUM 0 (1 / 2) 0 (1 / 16)
        (1 : Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ) σ3 a0 :=
  STeeUQM_empty sz0 0 (1 / 2) 0 (1 / 16) 1 σ3 a0

example :
    zeroModeSet 3 (sz0.L 0) ({0} : Finset (Fin 3))
        (UN 3 (sz0.L 0) (sz0.lam 0) (fun i => mSigma (1 / 2) (σ3 i)) 0 (1 / 16)
          (fun b : Fin 3 → Zd 3 (sz0.L 0) => (((b 0) 0).val : ℂ))) =
      tensorKer 3 (sz0.L 0) (uKerQ 3 (sz0.L 0) (sz0.lam 0) (1 / 2) ({0} : Finset (Fin 3)) σ3 0
        (1 / 16)) (fun b : Fin 3 → Zd 3 (sz0.L 0) => (((b 0) 0).val : ℂ)) :=
  zeroModeSet_UN_eq_uKerQ (sz0.lam 0) (1 / 2) ({0} : Finset (Fin 3)) σ3 0 (1 / 16) _

example :
    ∑ j ∈ Finset.range 4, zeroModeSet 3 (sz0.L 0) ({0} : Finset (Fin 3))
        (UN 3 (sz0.L 0) (sz0.lam 0) (fun i => mSigma (1 / 2) (σ3 i))
          (gridTime sInst tInst (fun _ => 4) 0 j) (1 / 16)
          (fun b : Fin 3 → Zd 3 (sz0.L 0) => (j : ℂ) + (((b 0) 0).val : ℂ))) =
      UN 3 (sz0.L 0) (sz0.lam 0) (fun i => mSigma (1 / 2) (σ3 i)) (1 / 32) (1 / 16)
        (∑ j ∈ Finset.range 4, zeroModeSet 3 (sz0.L 0) ({0} : Finset (Fin 3))
          (UN 3 (sz0.L 0) (sz0.lam 0) (fun i => mSigma (1 / 2) (σ3 i))
            (gridTime sInst tInst (fun _ => 4) 0 j) (1 / 32)
            (fun b : Fin 3 → Zd 3 (sz0.L 0) => (j : ℂ) + (((b 0) 0).val : ℂ)))) :=
  difRep3_UN_transfer (d := 3) (sz0.lam 0) (sz0.three_le_L 0) (E := 1 / 2) (by norm_num) σ3
    ({0} : Finset (Fin 3)) (v := 1 / 32) (w := 1 / 16) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) 4 (fun j => gridTime sInst tInst (fun _ => 4) 0 j)
    (fun j b => (j : ℂ) + (((b 0) 0).val : ℂ))

/-- **Target 5, `gridRepWTailQN_holds`, at the flow data**, every loop length `m ≥ 2` and every `Q` (`D = 1`,
`ε' = 1/10`): the grid exponent `CK` it returns, the grid `K_n = ⌈N^{CK}⌉ + 1`, and the weighted tail bound `≤ N^{-1}`
eventually, for every label `(σ, a)`. -/
theorem inst_gridRepWTailQN (m : ℕ) (hm : 2 ≤ m) (Q : Finset (Fin m)) :
    ∃ CK : ℝ, 0 ≤ CK ∧ ∃ K : ℕ → ℕ, (∀ n, K n ≠ 0) ∧
      (∀ᶠ n in atTop, ((sz0.size n : ℕ) : ℝ) ^ CK ≤ K n) ∧
      (∀ᶠ n in atTop, ∀ i : (Fin m → Bool) × (Fin m → Zd 3 (sz0.L n)),
        pathP sz0 {ω | ∃ k, k ≤ K n ∧
          ((sz0.size n : ℕ) : ℝ) ^ (1 / 10 : ℝ) *
              (∑ j ∈ Finset.range k, gridStep sInst tInst K n *
                ‖STeeUQM sz0 n (STflowE z0 n) (gridTime sInst tInst K n j)
                  (gridTime sInst tInst K n k) (pathH sz0 sInst tInst K n j ω) Q i.1 i.2‖ +
                ((sz0.size n : ℕ) : ℝ) ^ (-(1 : ℝ))) ^ (1 / 2 : ℝ) <
            ‖∑ j ∈ Finset.range k, zeroModeSet 3 (sz0.L n) Q
              (UN 3 (sz0.L n) (sz0.lam n) (fun i' => mSigma (STflowE z0 n) (i.1 i'))
                (gridTime sInst tInst K n j) (gridTime sInst tInst K n k)
                (fun b => difRepMartN sz0 (STflowE z0) sInst tInst K n (i.1, b) (j + 1) ω -
                  difRepMartN sz0 (STflowE z0) sInst tInst K n (i.1, b) j ω)) i.2‖} ≤
          ENNReal.ofReal (((sz0.size n : ℕ) : ℝ) ^ (-(1 : ℝ)))) := by
  obtain ⟨CK, hCK, h⟩ := gridRepWTailQN_holds 3 m hm Q (1 / 10) (1 / 10) (1 / 10)
    (by norm_num) (by norm_num) (by norm_num) (1 / 6) sz0 z0 flow_z0 sInst tInst hs0 hst htT 1
    one_pos
  have hK0 : ∀ n, ⌈((sz0.size n : ℕ) : ℝ) ^ CK⌉₊ + 1 ≠ 0 := fun n => Nat.succ_ne_zero _
  have hKN : ∀ᶠ n in atTop, ((sz0.size n : ℕ) : ℝ) ^ CK ≤
      ((⌈((sz0.size n : ℕ) : ℝ) ^ CK⌉₊ + 1 : ℕ) : ℝ) :=
    Eventually.of_forall fun n => (Nat.le_ceil _).trans (by exact_mod_cast Nat.le_succ _)
  exact ⟨CK, hCK, fun n => ⌈((sz0.size n : ℕ) : ℝ) ^ CK⌉₊ + 1, hK0, hKN,
    h (fun n => ⌈((sz0.size n : ℕ) : ℝ) ^ CK⌉₊ + 1) hK0 hKN (1 / 10) (by norm_num)⟩

/-- Target 5 at `(m, Q) = (2, {0})` (the case `Q^{(1)}` of S5-26) and at `(m, Q) = (3, ∅)`. -/
example := inst_gridRepWTailQN 2 le_rfl ({0} : Finset (Fin 2))
example := inst_gridRepWTailQN 3 (by norm_num) (∅ : Finset (Fin 3))

/-- **Target 2, `gridRepWTailN_of_Q`, at `d = 3`, `m = 2`**: the case `Q = ∅` of target 5 is the pinned clause (iv). -/
example : GridRepWTailNAt 3 2 := gridRepWTailN_of_Q 3 2 (gridRepWTailQN_holds 3 2 le_rfl ∅)

/-- **Target 6, `gridRepWTailN_holds`, at the flow data**, every loop length `m ≥ 2` (`D = 1`, `ε' = 1/10`). -/
theorem inst_gridRepWTailN (m : ℕ) (hm : 2 ≤ m) :
    ∃ CK : ℝ, 0 ≤ CK ∧ ∃ K : ℕ → ℕ, (∀ n, K n ≠ 0) ∧
      (∀ᶠ n in atTop, ((sz0.size n : ℕ) : ℝ) ^ CK ≤ K n) ∧
      (∀ᶠ n in atTop, ∀ i : (Fin m → Bool) × (Fin m → Zd 3 (sz0.L n)),
        pathP sz0 {ω | ∃ k, k ≤ K n ∧
          ((sz0.size n : ℕ) : ℝ) ^ (1 / 10 : ℝ) *
              (∑ j ∈ Finset.range k, gridStep sInst tInst K n *
                ‖sz0.STeeUM n (STflowE z0 n) (gridTime sInst tInst K n j)
                  (gridTime sInst tInst K n k) (pathH sz0 sInst tInst K n j ω) i.1 i.2‖ +
                ((sz0.size n : ℕ) : ℝ) ^ (-(1 : ℝ))) ^ (1 / 2 : ℝ) <
            ‖∑ j ∈ Finset.range k,
              UN 3 (sz0.L n) (sz0.lam n) (fun i' => mSigma (STflowE z0 n) (i.1 i'))
                (gridTime sInst tInst K n j) (gridTime sInst tInst K n k)
                (fun b => difRepMartN sz0 (STflowE z0) sInst tInst K n (i.1, b) (j + 1) ω -
                  difRepMartN sz0 (STflowE z0) sInst tInst K n (i.1, b) j ω) i.2‖} ≤
          ENNReal.ofReal (((sz0.size n : ℕ) : ℝ) ^ (-(1 : ℝ)))) := by
  obtain ⟨CK, hCK, h⟩ := gridRepWTailN_holds 3 m hm (1 / 10) (1 / 10) (1 / 10)
    (by norm_num) (by norm_num) (by norm_num) (1 / 6) sz0 z0 flow_z0 sInst tInst hs0 hst htT 1
    one_pos
  have hK0 : ∀ n, ⌈((sz0.size n : ℕ) : ℝ) ^ CK⌉₊ + 1 ≠ 0 := fun n => Nat.succ_ne_zero _
  have hKN : ∀ᶠ n in atTop, ((sz0.size n : ℕ) : ℝ) ^ CK ≤
      ((⌈((sz0.size n : ℕ) : ℝ) ^ CK⌉₊ + 1 : ℕ) : ℝ) :=
    Eventually.of_forall fun n => (Nat.le_ceil _).trans (by exact_mod_cast Nat.le_succ _)
  exact ⟨CK, hCK, fun n => ⌈((sz0.size n : ℕ) : ℝ) ^ CK⌉₊ + 1, hK0, hKN,
    h (fun n => ⌈((sz0.size n : ℕ) : ℝ) ^ CK⌉₊ + 1) hK0 hKN (1 / 10) (by norm_num)⟩

/-- Target 6 at `m = 2` and `m = 3`. -/
example := inst_gridRepWTailN 2 le_rfl
example := inst_gridRepWTailN 3 (by norm_num)

/-- **Target 7, `stGridRepN_holds`, at `d = 3`**: the pin `STGridRepN 3` is unconditional. -/
example : STGridRepN 3 := stGridRepN_holds 3 (by norm_num)

/-- `STGridMart 3` through `ST_gridMart_of_repN` and target 7. -/
example : STGridMart 3 := ST_gridMart_of_repN (stGridRepN_holds 3 (by norm_num))

/-- **`STStep2 3` through `ST_step2_of_pinsN'`**: the `hRep` premise is the proved `stGridRepN_holds`; the other
pins of the chain (`STNewKLK`, `STLWT`, `STEMn2Exp`, `STOptL2`, `STLocalAvgOfL2`) stay hypotheses (CLAUDE.md §4
step 2; DECISIONS §36 (iii)). -/
example (hNew : STNewKLK 3) (hLWT : STLWT 3) (hEMe : STEMn2Exp 3) (hOpt : STOptL2 3)
    (hClos : STLocalAvgOfL2 3) : STStep2 3 :=
  ST_step2_of_pinsN' hNew hLWT hEMe (stGridRepN_holds 3 (by norm_num)) hOpt hClos

end RBM.Ind.DifREP3Inst

end
