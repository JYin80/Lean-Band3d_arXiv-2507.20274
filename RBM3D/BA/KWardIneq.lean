/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.BA.KInduct
import RBM3D.BA.KMolecule
import RBM3D.BA.KPure

/-!
# Stage K, row K11: Ward's inequality for the block Anderson `𝒦`-loops, `lem_wardineq_K`

Ticket T2384 (design BA-DK, `docs/reports/T2360-design.md` §4 row K11, §5; supervisor
`docs/supervisor/2026-10-10-0350.md` C2, C4 and `2026-10-10-1155.md` C1).  The statements are
those of `docs/reports/T2384-prove.md` section (a), audited in `docs/reports/T2384-1a-audit.md`.
Paper: `lem_wardineq_K` (`3_5_Loop_Hierarchy.tex:1001-1012`), proof
`A_deterministic_estimates.tex:809-827`; `d ≥ 3`.  The BA twin of `Loop/KLWardIneq.lean` (T2122),
over the cactus objects `BAKpi`, `BASigmaPi` (K06, `BA/KMolecule.lean`), the cut `baKpi_cut` (K10,
`BA/KInduct.lean`) and the solution `BAKsol`.  The paper's proof uses no Ward identity: `baK_ward`
(K02) does not enter; `n = 2` is `baKsol_two` and the row sums `Σ_x |M^{(s,s')}_{zx}| = 1`.

1. The statements: `BAWardIneqAt` (the BA `KLwardIneqAt`), the layer form `BAWardKpiAt` (the BA
   `KLWardIneq_KpiAt`), the premise `KWardIneq_IndAt` (`(eq:ind-step-bound)`, `IndStepAbs` at
   `BASig`) and `KWardIneq_MolAt` (`(eq:molecule-decay)`, `SigDecayAbs` at `BASig`), and the
   family `KWardIneq_Data` of the data of the real-axis pins.
2. Scalars and `ℓ¹` bounds: `η_t = (1 - t) Im m ≤ 1 - t`, `(1 - t)⁻¹ ≤ η_t⁻¹`; for every charge
   pair the rows and columns of `Θ^{(s,s')}_t` have `ℓ¹` norm `≤ (1-t)⁻¹` (`(eq:THETAinftinf)`;
   the resolvent identity of K00 and `Σ_b |M^{(s,s')}_{cb}| = Σ_b K_{cb} = 1`, no Neumann series
   and no `|Θ^{(σσ')}| ≤ Θ^{(+,-)}`); the sup bound and the `ℓ¹` bound of a short leaf (copies of
   `KInduct_theta_sup/_l1`, properties 5, 5').
3. `baWardMol_holds` (K07's `baSig_decay` at the family `KWardIneq_Data`) and
   `KWardIneq_IndAt_of_abs` (`IndStepAbs ⊢ KWardIneq_IndAt`: the bridge K12 uses from
   `indStepAbs_of`).
4. The layer `π = ∅` with the last label summed (`baWardKpi_empty_bound`): `K^{(∅)}(a[x]) = Σ_b
   Θ(x, b) X_b` (`baKpi_empty_slice`), a long last leaf by `(eq:ind-step-bound)` and the column
   sums of `Θ`, a short last leaf (not covered by the paper's displayed line `A:816-818`) by
   property 5' and the absolute bound `KWardIneq_abs_sum_le`.
5. The cut `baKpi_cut` keeps the summed last label in the outer polygon: the label twins
   `KWardIneq_aIn_update`, `KWardIneq_aOut_update`.
6. The induction step `baWardKpi_step`, the induction `baWardKpi_holds`, `n = 2`
   (`baWardIneq_two`), the assembly over the layers `baWardIneq_of_Kpi` (`(eq_K-Kpi)`,
   `baK_eq_sum_Kpi`) and `baWardIneq_holds`.
7. Compiled nonempty instances at the flow point `P` of `(d, L) = (3, 4)`.

**The induction.**  Notation: `n = m + 1` polygon vertices, the summed label is the label of the
last vertex `v = Fin.last m`, `a[x] = Function.update a v x`, `K^{(π)} = BAKpi`, `B = Bparam d L g
t 0`, `η = (1 - t) Im m`.  Strong induction on `m ≥ 2` for `P(m) := ∑_x |K^{(π)}(σ, a[x])| ≤ C L^τ
η⁻¹ B^{n-2}`. At `n`, given `P(m'')` for `2 ≤ m'' < m`: (L) `π = ∅`, `σ_v ≠ σ_{v+1}`:
`K^{(∅)}(a[x]) = ∑_b Θ(x, b) X_b`, the column sums of `Θ` are `≤ (1-t)⁻¹ ≤ η⁻¹`, and `∑_b |X_b| ≺
B^{n-2}` is `(eq:ind-step-bound)` at `k = n`.  (S) `π = ∅`, `σ_v = σ_{v+1}`: `∑_x |Θ^{(s,s)}(x,
b)| ≤ S`, `|Σ^{(∅)}(δ)| ≤ C_m e^{-c_m max|δ_i - δ_j|}`, the leaves other than `v` and `0` are `≤
C_d B`, the leaf at `0` is summed (`≤ (1-t)⁻¹`): `∑_x |K^{(∅)}| ≤ S C_m (C_d B)^{n-2} expC^{n-1}
(1-t)⁻¹`, no loss. (C) `π ≠ ∅`: `K^{(π)} = 0` if no tree has the long edges `π`; otherwise cut at
an innermost long edge `J = (i, j)` (`baKpi_cut`): one glue sum `t ∑_u A(u) K^{(π')}(σ_out,
a_out(u))` (the chord `tΘ` is the glue leaf of the outer polygon: no `S^{(B)}`, no `Θ - 1 = ξ_J
SΘ`), `A(u)` does not depend on `x` (`j ≤ n - 1`), so `∑_x |K^{(π)}| ≤ |t| (∑_u |A(u)|) sup_u ∑_x
|K^{(π')}(a_out(u)[x])|`, `∑_u |A| ≺ B^{k-2}` (`(eq:ind-step-bound)` at `k = j - i + 1 ∈ [3,
n-1]`, loss `L^{τ/2}`) and `sup ∑_x |K^{(π')}| ≺ η⁻¹ B^{n''-2}` (`P(m'')` at `τ/2`, `n'' = n - (j
- i) + 1 ∈ [3, n-1]`): `(k-2) + (n''-2) = n - 2`, `L^{τ/2} L^{τ/2} = L^τ`, `η⁻¹` once. Then
`(wardineq_K)`: `n = 2` is `baKsol_two`; `n ≥ 3` is `(eq_K-Kpi)` (`baK_eq_sum_Kpi`): `W^{-d(n-1)}`
times the sum over the `2^{|diagonals n|}` layers. The constants depend on `(d, n, Λ, κ, τ)` only
(never on `L, W, g, E, m, t`): no smallness of `g`.

**Differences from the paper and from the band.**  (i) As `Loop/KLWardIneq.lean`, the induction is
on the number of polygon vertices for the standard `K^{(π)}`, not on molecules. (ii) The case (S)
is proved here (as in the band).  (iii) `(eq:K-pi-bound_partial)` is for `n ≥ 3`; `n = 2` is
`baWardIneq_two`.  (iv) The loss is `L^τ`, `τ > 0` arbitrary. (v) The BA chord is `tΘ` (no
`S^{(B)}`): one glue sum, no `∑_w |S^{(B)}_{uw}| = 1`.  (vi) `lem_wardineq_K` is conditional on
`(eq:ind-step-bound)` (`KWardIneq_IndAt`: K09b/K12's pin), as in the paper, where it is an input.

Public: the declarations above; every other helper is `private` with the stem `KWardIneq_`.
Copied, because private in merged files: `KInduct_theta_perm`, `_shift`, `_sup`, `_l1`,
`KInduct_one_le_rpow` (`BA/KInduct.lean:128, 147, 188, 203, 265`), `KLWardIneq_sum_slice`,
`KLWardIneq_sum_exp_maxDist` (`Loop/KLWardIneq.lean:220, 255`), `KLWardIneq_aIn_update`,
`KLWardIneq_aOut_update` (`Loop/KLWardIneq.lean:531, 550`).

-/

set_option linter.style.longLine false

namespace RBM.BA

open RBM RBM.Loop
open scoped Matrix

/-! ## 1. The statements -/

/-- **`lem_wardineq_K`, `(wardineq_K)` for the block Anderson `𝒦`** (`3_5_Loop_Hierarchy.tex:1001-1012`; the BA twin of
`KLwardIneqAt`, `Loop/KLWardIneq.lean:90`; the binders are those of `BAKBoundAt`, `BA/KInduct.lean:55`, plus `W ≥ 1`):
at `(d, n, Λ, κ)` fixed, for every `τ > 0` one constant `C`, uniform in `L ≥ 3`, `W ≥ 1`, `g ∈ (0, Λ]`, the real-axis
data `BAReal d L g κ E m` and `t ∈ [0,1)`: `max_σ ∑_{a_n} |𝒦^{(n)}_{t,σ,a}| ≤ C L^τ (W^d η_t)⁻¹ (W^{-d} B_{t,0})^{n-2}`,
`η_t = (1 - t) Im m` (`1_2:721`), the sum over the last label. -/
def BAWardIneqAt (d n : ℕ) (Λ κ : ℝ) : Prop :=
  ∀ τ : ℝ, 0 < τ → ∃ C : ℝ, 0 < C ∧ ∀ (L : ℕ) (hL : 3 ≤ L) (W : ℕ), 1 ≤ W → ∀ g : ℝ, 0 < g → g ≤ Λ →
    ∀ (E : ℝ) (m : ℂ),
      haveI : NeZero L := ⟨by omega⟩
      BAReal d L g κ E m → ∀ t : ℝ, 0 ≤ t → t < 1 → ∀ (σ : Fin n → Bool) (a : Fin (n - 1) → Zd d L),
        ∑ x : Zd d L,
            ‖BAKsol d L W (BAMsigma d L (BAMB d L g (E : ℂ) m)) (PropSpin m) t ⟨List.ofFn σ, List.ofFn a ++ [x]⟩‖
          ≤ C * (L : ℝ) ^ τ * (((W : ℝ) ^ d) * ((1 - t) * m.im))⁻¹ *
              (((W : ℝ) ^ d)⁻¹ * Bparam d L g t 0) ^ (n - 2)

/-- **`(eq:ind-step-bound)` at BA** (`A_deterministic_estimates.tex:703`; the premise of the induction, owed by K09b/K12 through
`KWardIneq_IndAt_of_abs`): `IndStepAbs` (`Loop/KLIndStepB.lean:77`) at the molecule weight `BASig` and the leaf edges `Θ` of the BA data,
with `Bp = B_{t,0}`: for `σ_r ≠ σ_{r+1}`, `∑_b |∑_{δ_r = b} Σ^{(∅)}(σ,δ) ∏_{j ≠ r} Θ^{(σ_j,σ_{j+1})}(a_j, δ_j)| ≤ C L^τ B_{t,0}^{k-2}`. -/
def KWardIneq_IndAt (d k : ℕ) [NeZero k] (Λ κ : ℝ) : Prop :=
  ∀ τ : ℝ, 0 < τ → ∃ C : ℝ, 0 < C ∧ ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → g ≤ Λ → ∀ (E : ℝ) (m : ℂ),
    haveI : NeZero L := ⟨by omega⟩
    BAReal d L g κ E m → ∀ t : ℝ, 0 ≤ t → t < 1 → ∀ (σ : Fin k → Bool) (r : Fin k), σ r ≠ σ (r + 1) →
      ∀ a : Fin k → Zd d L,
        ∑ b : Zd d L, ‖∑ δ ∈ Finset.univ.filter (fun δ : Fin k → Zd d L => δ r = b),
            BASigmaPi d L k (BAMsigma d L (BAMB d L g (E : ℂ) m)) t σ ∅ δ *
              ∏ j ∈ Finset.univ.erase r,
                BAThetaOf (BAMsigma d L (BAMB d L g (E : ℂ) m)) t (σ j) (σ (j + 1)) (a j) (δ j)‖
          ≤ C * (L : ℝ) ^ τ * (Bparam d L g t 0) ^ (k - 2)

/-- **`(eq:molecule-decay)` at BA** (`A:691`): `|Σ^{(∅)}(σ,δ)| ≤ C e^{-c max_{i,j} |δ_i - δ_j|}` for every `σ`
(`SigDecayAbs` at `BASig`); proved by `baWardMol_holds` from K07's `baSig_decay`. -/
def KWardIneq_MolAt (d k : ℕ) [NeZero k] (Λ κ : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ c : ℝ, 0 < c ∧ ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → g ≤ Λ → ∀ (E : ℝ) (m : ℂ),
    haveI : NeZero L := ⟨by omega⟩
    BAReal d L g κ E m → ∀ t : ℝ, 0 ≤ t → t < 1 → ∀ (σ : Fin k → Bool) (δ : Fin k → Zd d L),
      ‖BASigmaPi d L k (BAMsigma d L (BAMB d L g (E : ℂ) m)) t σ ∅ δ‖
        ≤ C * Real.exp (-(c * (KLmaxDist d L δ : ℝ)))

/-- **`(eq:K-pi-bound_partial)` at the polygon with `n = m + 1` vertices** (the layer form of `BAWardIneqAt`; the BA twin of
`KLWardIneq_KpiAt`, `Loop/KLWardIneq.lean:662`): the sum over the last label `a_n = x`,
`∑_x |K^{(π)}(t,σ,a[x])| ≤ C L^τ η_t⁻¹ B_{t,0}^{n-2}`, every `σ`, every layer `π`; `BAKpi` carries no `W`. -/
def BAWardKpiAt (d m : ℕ) (Λ κ : ℝ) : Prop :=
  ∀ τ : ℝ, 0 < τ → ∃ C : ℝ, 0 < C ∧ ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → g ≤ Λ → ∀ (E : ℝ) (z : ℂ),
    haveI : NeZero L := ⟨by omega⟩
    BAReal d L g κ E z → ∀ t : ℝ, 0 ≤ t → t < 1 → ∀ (σ : Fin (m + 1) → Bool)
      (π : Finset (Fin (m + 1) × Fin (m + 1))) (a : Fin (m + 1) → Zd d L),
      ∑ x : Zd d L,
          ‖BAKpi d L (m + 1) (BAMsigma d L (BAMB d L g (E : ℂ) z)) t σ (Function.update a (Fin.last m) x) π‖
        ≤ C * (L : ℝ) ^ τ * ((1 - t) * z.im)⁻¹ * (Bparam d L g t 0) ^ (m - 1)

/-- **The data of the real-axis pins** at `(d, Λ, κ)`: the parameters `(L, g, E, m, t)` with `3 ≤ L`, `0 < g ≤ Λ`,
`BAReal d L g κ E m` and `t ∈ [0,1)`.  The index family `ι` through which the abstract interfaces `IndStepAbs`, `SigDecayAbs`
(`Loop/KLIndStepB.lean:77`, `Loop/KLIndStepA.lean:1050`) see the BA data. -/
structure KWardIneq_Data (d : ℕ) (Λ κ : ℝ) where
  L : ℕ
  hL : 3 ≤ L
  g : ℝ
  hg : 0 < g
  hgΛ : g ≤ Λ
  E : ℝ
  m : ℂ
  hr : haveI : NeZero L := ⟨by omega⟩; BAReal d L g κ E m
  t : ℝ
  ht0 : 0 ≤ t
  ht1 : t < 1

instance KWardIneq_Data.instNeZero {d : ℕ} {Λ κ : ℝ} (i : KWardIneq_Data d Λ κ) : NeZero i.L :=
  ⟨by have := i.hL; omega⟩

/-! ## 2. Scalar facts, the `ℓ¹` bounds of the leaves -/

section Scalar

variable {d L : ℕ} [NeZero L] {g κ E : ℝ} {m : ℂ}

/-- `Im m ≤ 1` at BA data (`Im m ≤ ‖m‖ ≤ 1`, `BAm_norm_le_one`, `BA/Ward.lean:136`). -/
private theorem KWardIneq_im_le_one (hr : BAReal d L g κ E m) : m.im ≤ 1 :=
  (Complex.im_le_norm m).trans (BAm_norm_le_one d L g (E : ℂ) m (by simp) hr.1)

/-- `η_t = (1 - t) Im m > 0`. -/
private theorem KWardIneq_eta_pos {z : ℂ} (hκ : 0 < κ) (hz : κ ≤ z.im) {t : ℝ} (ht : t < 1) : 0 < (1 - t) * z.im :=
  mul_pos (by linarith) (by linarith)

/-- `(1 - t)⁻¹ ≤ η_t⁻¹` (`η_t = (1 - t) Im m`, `0 < Im m ≤ 1`). -/
private theorem KWardIneq_inv_le (hr : BAReal d L g κ E m) (hκ : 0 < κ) {t : ℝ} (ht : t < 1) :
    (1 - t)⁻¹ ≤ ((1 - t) * m.im)⁻¹ := by
  refine inv_anti₀ (KWardIneq_eta_pos hκ hr.2 ht) ?_
  calc (1 - t) * m.im ≤ (1 - t) * 1 := mul_le_mul_of_nonneg_left (KWardIneq_im_le_one hr) (by linarith)
    _ = 1 - t := mul_one _

/-- `1 ≤ L^τ` for `L ≥ 3`, `τ > 0` (a copy of `KInduct_one_le_rpow`, `BA/KInduct.lean:265`, private there). -/
private theorem KWardIneq_one_le_rpow {L : ℕ} (hL : 3 ≤ L) {τ : ℝ} (hτ : 0 < τ) : (1 : ℝ) ≤ (L : ℝ) ^ τ :=
  Real.one_le_rpow (by exact_mod_cast (by omega : 1 ≤ L)) hτ.le

end Scalar

section Leaves

/-- `Σ_b |Θ(a,b)| ≤ (1-t)⁻¹` from the right resolvent identity `Θ = 1 + t Θ Q` and `Σ_b |Q(c,b)| ≤ 1`. -/
private theorem KWardIneq_row_of_resolvent {G : Type*} [Fintype G] [DecidableEq G] (Θ Q : Matrix G G ℂ)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) (hres : Θ = 1 + (t : ℂ) • (Θ * Q))
    (hQ : ∀ c, ∑ b, ‖Q c b‖ ≤ 1) (a : G) : ∑ b, ‖Θ a b‖ ≤ (1 - t)⁻¹ := by
  set R : ℝ := ∑ b, ‖Θ a b‖ with hR
  have hpt : ∀ b, ‖Θ a b‖ ≤ (if a = b then (1 : ℝ) else 0) + t * ∑ c, ‖Θ a c‖ * ‖Q c b‖ := by
    intro b
    have h := congrFun (congrFun hres a) b
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, Matrix.mul_apply] at h
    rw [h]
    refine (norm_add_le _ _).trans ?_
    have h1 : ‖(if a = b then (1 : ℂ) else 0)‖ = if a = b then (1 : ℝ) else 0 := by split_ifs <;> simp
    have h2 : ‖(t : ℂ) * ∑ c, Θ a c * Q c b‖ ≤ t * ∑ c, ‖Θ a c‖ * ‖Q c b‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ht0]
      refine mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (le_of_eq ?_)) ht0
      exact Finset.sum_congr rfl fun c _ => norm_mul _ _
    rw [h1]
    linarith
  have hsum : R ≤ 1 + t * R := by
    calc R = ∑ b, ‖Θ a b‖ := rfl
      _ ≤ ∑ b, ((if a = b then (1 : ℝ) else 0) + t * ∑ c, ‖Θ a c‖ * ‖Q c b‖) := Finset.sum_le_sum fun b _ => hpt b
      _ = 1 + t * ∑ c, ‖Θ a c‖ * ∑ b, ‖Q c b‖ := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_comm]
          simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true, ← Finset.mul_sum]
      _ ≤ 1 + t * ∑ c, ‖Θ a c‖ * 1 := by
          gcongr with c _
          exact hQ c
      _ = 1 + t * R := by simp [hR]
  have h1t : 0 < 1 - t := by linarith
  rw [← one_div, le_div_iff₀ h1t]
  nlinarith

/-- `Σ_a |Θ(a,b)| ≤ (1-t)⁻¹` from the left resolvent identity `Θ = 1 + t Q Θ` and `Σ_a |Q(a,c)| ≤ 1`. -/
private theorem KWardIneq_col_of_resolvent {G : Type*} [Fintype G] [DecidableEq G] (Θ Q : Matrix G G ℂ)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) (hres : Θ = 1 + (t : ℂ) • (Q * Θ))
    (hQ : ∀ c, ∑ a, ‖Q a c‖ ≤ 1) (b : G) : ∑ a, ‖Θ a b‖ ≤ (1 - t)⁻¹ := by
  set R : ℝ := ∑ a, ‖Θ a b‖ with hR
  have hpt : ∀ a, ‖Θ a b‖ ≤ (if a = b then (1 : ℝ) else 0) + t * ∑ c, ‖Q a c‖ * ‖Θ c b‖ := by
    intro a
    have h := congrFun (congrFun hres a) b
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, Matrix.mul_apply] at h
    rw [h]
    refine (norm_add_le _ _).trans ?_
    have h1 : ‖(if a = b then (1 : ℂ) else 0)‖ = if a = b then (1 : ℝ) else 0 := by split_ifs <;> simp
    have h2 : ‖(t : ℂ) * ∑ c, Q a c * Θ c b‖ ≤ t * ∑ c, ‖Q a c‖ * ‖Θ c b‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ht0]
      refine mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (le_of_eq ?_)) ht0
      exact Finset.sum_congr rfl fun c _ => norm_mul _ _
    rw [h1]
    linarith
  have hsum : R ≤ 1 + t * R := by
    calc R = ∑ a, ‖Θ a b‖ := rfl
      _ ≤ ∑ a, ((if a = b then (1 : ℝ) else 0) + t * ∑ c, ‖Q a c‖ * ‖Θ c b‖) := Finset.sum_le_sum fun a _ => hpt a
      _ = 1 + t * ∑ c, (∑ a, ‖Q a c‖) * ‖Θ c b‖ := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_comm]
          simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true, ← Finset.sum_mul]
      _ ≤ 1 + t * ∑ c, 1 * ‖Θ c b‖ := by
          gcongr with c _
          exact hQ c
      _ = 1 + t * R := by simp [hR]
  have h1t : 0 < 1 - t := by linarith
  rw [← one_div, le_div_iff₀ h1t]
  nlinarith

variable {d L : ℕ} [NeZero L] {g κ E : ℝ} {m : ℂ}

/-- **`(eq:THETAinftinf)` at BA, rows**: `Σ_b |Θ_t^{(s,s')}(a,b)| ≤ (1-t)⁻¹` for all four charge pairs: the right resolvent
identity (`BATheta_resolvent`) and `Σ_b |M^{(s,s')}_{cb}| = Σ_b K_{cb} = 1` (`BAMss_norm_eq_BAK`, `BAK_row_sum`).  The band's
`sum_norm_Theta_row_le` (`Propagator/Props4.lean:210`) goes through `|Θ^{(σσ')}_{ab}| ≤ Θ^{(+,-)}_{ab}`; the resolvent identity is used here instead. -/
private theorem KWardIneq_theta_row_le (hr : BAReal d L g κ E m) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1)
    (s s' : Bool) (a : Zd d L) :
    ∑ b, ‖BAThetaOf (BAMsigma d L (BAMB d L g (E : ℂ) m)) t s s' a b‖ ≤ (1 - t)⁻¹ := by
  refine KWardIneq_row_of_resolvent (BATheta d L g E m t s s') (BAMss d L (BAMB d L g (E : ℂ) m) s s') ht0 ht1
    (BATheta_resolvent d L g κ E m hr t ht0 ht1 s s').2 (fun c => ?_) a
  simp only [BAMss_norm_eq_BAK]
  exact (BAK_row_sum d L g E m hr.1 c).le

/-- **`(eq:THETAinftinf)` at BA, columns**: `Σ_a |Θ_t^{(s,s')}(a,b)| ≤ (1-t)⁻¹` (the left resolvent identity and
`Σ_a |M^{(s,s')}_{ac}| = Σ_a K_{ac} = 1`, `BAK_col_sum`; no symmetry of `Θ`). -/
private theorem KWardIneq_theta_col_le (hr : BAReal d L g κ E m) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1)
    (s s' : Bool) (b : Zd d L) :
    ∑ a, ‖BAThetaOf (BAMsigma d L (BAMB d L g (E : ℂ) m)) t s s' a b‖ ≤ (1 - t)⁻¹ := by
  refine KWardIneq_col_of_resolvent (BATheta d L g E m t s s') (BAMss d L (BAMB d L g (E : ℂ) m) s s') ht0 ht1
    (BATheta_resolvent d L g κ E m hr t ht0 ht1 s s').1 (fun c => ?_) b
  simp only [BAMss_norm_eq_BAK]
  exact (BAK_col_sum d L g E m hr.1 c).le

/-- `Θ^{(s,s')}_t` is invariant under a permutation `e` of the labels fixing every `M(σ)` (a copy of the private
`KInduct_theta_perm`, `BA/KInduct.lean:128`). -/
private theorem KWardIneq_theta_perm (e : Zd d L ≃ Zd d L) (M : Bool → Matrix (Zd d L) (Zd d L) ℂ)
    (hM : ∀ σ x y, M σ (e x) (e y) = M σ x y) (t : ℝ) (s s' : Bool) (x y : Zd d L) :
    BAThetaOf M t s s' (e x) (e y) = BAThetaOf M t s s' x y := by
  have hQ : ∀ x y, BAMssOf M s s' (e x) (e y) = BAMssOf M s s' x y := fun x y => by
    simp only [BAMssOf, Matrix.of_apply, hM]
  have hA : ((1 : Matrix (Zd d L) (Zd d L) ℂ) - (t : ℂ) • BAMssOf M s s').submatrix e e =
      1 - (t : ℂ) • BAMssOf M s s' := by
    ext x y
    simp only [Matrix.submatrix_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
      e.injective.eq_iff, hQ]
  have h2 := Matrix.inv_submatrix_equiv ((1 : Matrix (Zd d L) (Zd d L) ℂ) - (t : ℂ) • BAMssOf M s s') e e
  rw [hA] at h2
  unfold BAThetaOf PropThetaQ
  rw [← Matrix.nonsing_inv_eq_ringInverse]
  have h3 := congrFun (congrFun h2 x) y
  rw [Matrix.submatrix_apply] at h3
  exact h3.symm

/-- Translation invariance of `Θ`: `Θ_t^{(s,s')}(x, y) = Θ_t^{(s,s')}(0, y - x)` (a copy of the private `KInduct_theta_shift`,
`BA/KInduct.lean:147`). -/
private theorem KWardIneq_theta_shift (g E : ℝ) (m : ℂ) (t : ℝ) (s s' : Bool) (x y : Zd d L) :
    BATheta d L g E m t s s' x y = BATheta d L g E m t s s' 0 (y - x) := by
  have h := KWardIneq_theta_perm (Equiv.addRight (-x)) (BAMsigma d L (BAMB d L g (E : ℂ) m))
    (fun σ u v => BAMsigma_shift d L g (E : ℂ) m σ u v (-x)) t s s' x y
  simp only [Equiv.coe_addRight, add_neg_cancel, ← sub_eq_add_neg] at h
  exact h.symm

end Leaves

section Constants

/-- **Properties 4 + 5** (`BAProp5`): every entry of every `Θ_t^{(σ₁,σ₂)}` is `≤ C_d B_{t,0}` (a copy of the private
`KInduct_theta_sup`, `BA/KInduct.lean:188`). -/
private theorem KWardIneq_theta_sup {d : ℕ} (hd : 3 ≤ d) {Λ κ : ℝ} (hΛ : 0 < Λ) (hκ : 0 < κ) :
    ∃ Cd : ℝ, 0 < Cd ∧ ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → g ≤ Λ → ∀ (E : ℝ) (m : ℂ),
      haveI : NeZero L := ⟨by omega⟩
      BAReal d L g κ E m → ∀ t : ℝ, 0 ≤ t → t < 1 → ∀ (σ₁ σ₂ : Bool) (x y : Zd d L),
        ‖BATheta d L g E m t σ₁ σ₂ x y‖ ≤ Cd * Bparam d L g t 0 := by
  obtain ⟨Cd, hCd, cd, hcd, hbd⟩ := baProp5_holds d Λ κ hd hΛ hκ
  refine ⟨Cd, hCd, fun L hL g hg hgΛ E m => ?_⟩
  have : NeZero L := ⟨by omega⟩
  intro hr t ht0 ht1 σ₁ σ₂ x y
  rw [KWardIneq_theta_shift]
  exact KLIndStepA_decay_le_zero (by omega) hCd.le hcd.le (y - x)
    (hbd L hL g hg hgΛ E m hr t ht0 ht1 σ₁ σ₂ (y - x))

/-- **Property 5'** (`BAProp5s`): `Σ_b |Θ_t^{(σ,σ)}(x, b)| ≤ S`, `S = C_s (1 + Λ² expC k c_s)` (`d = k + 2`; a copy of the
private `KInduct_theta_l1`, `BA/KInduct.lean:203`). -/
private theorem KWardIneq_theta_l1 {k : ℕ} (hd : 3 ≤ k + 2) {Λ κ : ℝ} (hΛ : 0 < Λ) (hκ : 0 < κ) :
    ∃ S : ℝ, 0 < S ∧ ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → g ≤ Λ → ∀ (E : ℝ) (m : ℂ),
      haveI : NeZero L := ⟨by omega⟩
      BAReal (k + 2) L g κ E m → ∀ t : ℝ, 0 ≤ t → t < 1 → ∀ (σ : Bool) (x : Zd (k + 2) L),
        ∑ b : Zd (k + 2) L, ‖BATheta (k + 2) L g E m t σ σ x b‖ ≤ S := by
  obtain ⟨Cs, hCs, cs, hcs, hbd⟩ := baProp5s_holds (k + 2) Λ κ hd hΛ hκ
  have hexpC : 0 ≤ expC k cs := by unfold expC; positivity
  refine ⟨Cs * (1 + Λ ^ 2 * expC k cs), by positivity, fun L hL g hg hgΛ E m => ?_⟩
  have : NeZero L := ⟨by omega⟩
  intro hr t ht0 ht1 σ x
  have hpt : ∀ b : Zd (k + 2) L, ‖BATheta (k + 2) L g E m t σ σ x b‖
      ≤ Cs * ((if b - x = 0 then (1 : ℝ) else 0)
          + g ^ 2 * Real.exp (-(cs * (zdistD (k + 2) L (b - x) : ℝ)))) := by
    intro b
    rw [KWardIneq_theta_shift]
    have := hbd L hL g hg hgΛ E m hr t ht0 ht1 σ (b - x)
    simpa [neg_mul] using this
  have h1 : ∑ b : Zd (k + 2) L, (if b - x = 0 then (1 : ℝ) else 0) = 1 := by
    simp [sub_eq_zero]
  have h2 : ∑ b : Zd (k + 2) L, Real.exp (-(cs * (zdistD (k + 2) L (b - x) : ℝ))) ≤ expC k cs :=
    (le_of_eq (Fintype.sum_equiv (Equiv.subRight x) _
      (fun y : Zd (k + 2) L => Real.exp (-(cs * (zdistD (k + 2) L y : ℝ)))) fun b => rfl)).trans
      (sum_radial_exp_decay_le k hcs)
  calc ∑ b : Zd (k + 2) L, ‖BATheta (k + 2) L g E m t σ σ x b‖
      ≤ ∑ b : Zd (k + 2) L, Cs * ((if b - x = 0 then (1 : ℝ) else 0)
          + g ^ 2 * Real.exp (-(cs * (zdistD (k + 2) L (b - x) : ℝ)))) :=
        Finset.sum_le_sum fun b _ => hpt b
    _ = Cs * (1 + g ^ 2 * ∑ b : Zd (k + 2) L, Real.exp (-(cs * (zdistD (k + 2) L (b - x) : ℝ)))) := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib, h1, ← Finset.mul_sum]
    _ ≤ Cs * (1 + g ^ 2 * expC k cs) := by gcongr
    _ ≤ Cs * (1 + Λ ^ 2 * expC k cs) := by
        have : g ^ 2 ≤ Λ ^ 2 := pow_le_pow_left₀ hg.le hgΛ 2
        gcongr

end Constants

section DataBridge

/-- **`(eq:molecule-decay)` at BA is proved** (`A:691`): K07's `baSig_decay` (`BA/KPure.lean:632`, `SigDecayAbs` at `BASig`, uniform in the
family `ι`) at the family `ι = KWardIneq_Data d Λ κ` of the data of the real-axis pins. -/
theorem baWardMol_holds {d k : ℕ} [NeZero k] (hd : 3 ≤ d) (hk : 3 ≤ k) {Λ κ : ℝ} (hΛ : 0 < Λ) (hκ : 0 < κ) :
    KWardIneq_MolAt d k Λ κ := by
  obtain ⟨C, hC, c, hc, H⟩ := baSig_decay (ι := KWardIneq_Data d Λ κ) hd hk hΛ hκ (fun i => i.L) (fun i => i.g)
    (fun i => i.E) (fun i => i.m) (fun i => i.t) (fun i => i.hL) (fun i => i.hg) (fun i => i.hgΛ)
    (fun i => i.hr) (fun i => i.ht0) (fun i => i.ht1.le)
  refine ⟨C, hC, c, hc, ?_⟩
  intro L hL g hg hgΛ E m hr t ht0 ht1 σ δ
  exact H ⟨L, hL, g, hg, hgΛ, E, m, hr, t, ht0, ht1⟩ σ δ

/-- **`(eq:ind-step-bound)` at BA from its abstract form** (the bridge K12 uses: `indStepAbs_of`, `Loop/KLIndStepB.lean:879`, concludes
`IndStepAbs` over an index family; here the family `ι = KWardIneq_Data d Λ κ` of the data of the real-axis pins, the molecule weight
`BASig`, the leaf edges `Θ` of the BA data and `Bp = B_{t,0}`): `IndStepAbs ⊢ KWardIneq_IndAt`.  Conclusion of this theorem is the premise
of `baWardKpi_*` and `baWardIneq_holds`, so `KWardIneq_IndAt` carries no owed line in `Test/Axioms.lean`. -/
theorem KWardIneq_IndAt_of_abs {d k : ℕ} [NeZero k] {Λ κ : ℝ}
    (h : IndStepAbs (ι := KWardIneq_Data d Λ κ) d k (fun i => i.L) (fun i => Bparam d i.L i.g i.t 0)
      (BASig (ι := KWardIneq_Data d Λ κ) d k (fun i => i.L) (fun i => i.g) (fun i => i.E) (fun i => i.m) (fun i => i.t))
      (fun i s s' => BAThetaOf (BAMsigma d i.L (BAMB d i.L i.g (i.E : ℂ) i.m)) i.t s s')) :
    KWardIneq_IndAt d k Λ κ := by
  intro τ hτ
  obtain ⟨C, hC, H⟩ := h τ hτ
  refine ⟨C, hC, ?_⟩
  intro L hL g hg hgΛ E m hr t ht0 ht1 σ r hσ a
  exact H ⟨L, hL, g, hg, hgΛ, E, m, hr, t, ht0, ht1⟩ σ r hσ a

end DataBridge

/-! ## 3. The layer `π = ∅` with the last label summed -/

section Empty

variable {d L : ℕ} [NeZero L]

/-- **`K^{(∅)}` with the last label `x`**: `K^{(∅)}(σ, a[x]) = ∑_b Θ^{(σ_v,σ_{v+1})}(x, b) X_b`, `v = Fin.last m`,
`X_b = ∑_{δ_v = b} Σ^{(∅)}(δ) ∏_{i ≠ v} Θ^{(σ_i,σ_{i+1})}(a_i, δ_i)` (`baKpi_empty_slice` at the root `v`; `X_b` does not see `a_v`). -/
private theorem KWardIneq_Kempty_slice (M : Bool → Matrix (Zd d L) (Zd d L) ℂ) (t : ℝ) {m : ℕ}
    (σ : Fin (m + 1) → Bool) (a : Fin (m + 1) → Zd d L) (x : Zd d L) :
    BAKpi d L (m + 1) M t σ (Function.update a (Fin.last m) x) ∅
      = ∑ b : Zd d L, BAThetaOf M t (σ (Fin.last m)) (σ (Fin.last m + 1)) x b *
          ∑ δ ∈ Finset.univ.filter (fun δ : Fin (m + 1) → Zd d L => δ (Fin.last m) = b),
            BASigmaPi d L (m + 1) M t σ ∅ δ *
              ∏ i ∈ Finset.univ.erase (Fin.last m), BAThetaOf M t (σ i) (σ (i + 1)) (a i) (δ i) := by
  rw [baKpi_empty_slice M t σ (Function.update a (Fin.last m) x) (Fin.last m), Function.update_self]
  refine Finset.sum_congr rfl fun b _ => ?_
  congr 1
  refine Finset.sum_congr rfl fun δ _ => ?_
  congr 1
  exact Finset.prod_congr rfl fun i hi => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]

/-- If the column sums of the last leaf are `≤ Λ'`, then `∑_x |K^{(∅)}(σ, a[x])| ≤ Λ' ∑_b |X_b|`. -/
private theorem KWardIneq_sum_Kempty_le (M : Bool → Matrix (Zd d L) (Zd d L) ℂ) (t : ℝ) {m : ℕ}
    (σ : Fin (m + 1) → Bool) (a : Fin (m + 1) → Zd d L) {Λ' : ℝ}
    (hΛ : ∀ b : Zd d L,
      ∑ x : Zd d L, ‖BAThetaOf M t (σ (Fin.last m)) (σ (Fin.last m + 1)) x b‖ ≤ Λ') :
    ∑ x : Zd d L, ‖BAKpi d L (m + 1) M t σ (Function.update a (Fin.last m) x) ∅‖
      ≤ Λ' * ∑ b : Zd d L, ‖∑ δ ∈ Finset.univ.filter
          (fun δ : Fin (m + 1) → Zd d L => δ (Fin.last m) = b),
            BASigmaPi d L (m + 1) M t σ ∅ δ *
              ∏ i ∈ Finset.univ.erase (Fin.last m), BAThetaOf M t (σ i) (σ (i + 1)) (a i) (δ i)‖ := by
  simp only [KWardIneq_Kempty_slice]
  set X : Zd d L → ℝ := fun b => ‖∑ δ ∈ Finset.univ.filter
          (fun δ : Fin (m + 1) → Zd d L => δ (Fin.last m) = b),
            BASigmaPi d L (m + 1) M t σ ∅ δ *
              ∏ i ∈ Finset.univ.erase (Fin.last m), BAThetaOf M t (σ i) (σ (i + 1)) (a i) (δ i)‖ with hX
  calc ∑ x : Zd d L, ‖∑ b : Zd d L, BAThetaOf M t (σ (Fin.last m)) (σ (Fin.last m + 1)) x b *
          ∑ δ ∈ Finset.univ.filter (fun δ : Fin (m + 1) → Zd d L => δ (Fin.last m) = b),
            BASigmaPi d L (m + 1) M t σ ∅ δ *
              ∏ i ∈ Finset.univ.erase (Fin.last m), BAThetaOf M t (σ i) (σ (i + 1)) (a i) (δ i)‖
      ≤ ∑ x : Zd d L, ∑ b : Zd d L,
          ‖BAThetaOf M t (σ (Fin.last m)) (σ (Fin.last m + 1)) x b‖ * X b := by
        refine Finset.sum_le_sum fun x _ => (norm_sum_le _ _).trans (le_of_eq ?_)
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [norm_mul]
    _ = ∑ b : Zd d L, (∑ x : Zd d L,
          ‖BAThetaOf M t (σ (Fin.last m)) (σ (Fin.last m + 1)) x b‖) * X b := by
        rw [Finset.sum_comm]
        simp only [Finset.sum_mul]
    _ ≤ ∑ b : Zd d L, Λ' * X b :=
        Finset.sum_le_sum fun b _ => mul_le_mul_of_nonneg_right (hΛ b) (norm_nonneg _)
    _ = Λ' * ∑ b : Zd d L, X b := by rw [Finset.mul_sum]

end Empty

section Short

variable {n : ℕ} [NeZero n] {d L : ℕ} [NeZero L]

/-- A sum over the slice `δ_0 = x` of a product of one-point functions (a copy of the private `KLWardIneq_sum_slice`,
`Loop/KLWardIneq.lean:220`, itself a copy of `KLMolecule_sum_slice`). -/
private theorem KWardIneq_sum_slice (x : Zd d L) (f : Zd d L → ℝ) :
    ∑ δ ∈ Finset.univ.filter (fun δ : Fin n → Zd d L => δ 0 = x), ∏ i : Fin n, f (δ i)
      = f x * (∑ y, f y) ^ (n - 1) := by
  classical
  have hS : Finset.univ.filter (fun δ : Fin n → Zd d L => δ 0 = x)
      = Fintype.piFinset (fun i : Fin n => if i = 0 then ({x} : Finset (Zd d L)) else Finset.univ) := by
    ext δ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset]
    constructor
    · intro h i
      by_cases hi : i = 0
      · simp [hi, h]
      · simp [hi]
    · intro h
      have := h 0
      simpa using this
  have h := Finset.prod_univ_sum
    (fun i : Fin n => if i = 0 then ({x} : Finset (Zd d L)) else Finset.univ) (fun _ y => f y)
  rw [hS, ← h]
  have hfac : ∀ i : Fin n,
      ∑ y ∈ (if i = 0 then ({x} : Finset (Zd d L)) else Finset.univ), f y
        = if i = 0 then f x else ∑ y, f y := by
    intro i
    by_cases hi : i = 0 <;> simp [hi]
  simp only [hfac]
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ (0 : Fin n))]
  have h0 : (if (0 : Fin n) = 0 then f x else ∑ y, f y) = f x := by simp
  have h1 : ∀ i ∈ Finset.univ.erase (0 : Fin n),
      (if i = 0 then f x else ∑ y, f y) = ∑ y, f y := fun i hi => by
    simp [Finset.ne_of_mem_erase hi]
  rw [h0, Finset.prod_congr rfl h1, Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ _),
    Finset.card_univ, Fintype.card_fin]

/-- `∑_{δ_0 = x} e^{-c max|δ_i - δ_j|} ≤ expC(c/n)^{n-1}` (a copy of the private `KLWardIneq_sum_exp_maxDist`,
`Loop/KLWardIneq.lean:255`, itself a copy of `KLMolecule_sum_exp_maxDist`; generic lattice sums). -/
private theorem KWardIneq_sum_exp_maxDist (k : ℕ) {c : ℝ} (hc : 0 < c) (x : Zd (k + 2) L) :
    ∑ δ ∈ Finset.univ.filter (fun δ : Fin n → Zd (k + 2) L => δ 0 = x),
        Real.exp (-(c * (KLmaxDist (k + 2) L δ : ℝ))) ≤ (expC k (c / n)) ^ (n - 1) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast NeZero.pos n
  have hcn : 0 < c / n := by positivity
  set f : Zd (k + 2) L → ℝ := fun y => Real.exp (-(c / n * (zdistD (k + 2) L (x - y) : ℝ)))
    with hf
  have hterm : ∀ δ ∈ Finset.univ.filter (fun δ : Fin n → Zd (k + 2) L => δ 0 = x),
      Real.exp (-(c * (KLmaxDist (k + 2) L δ : ℝ))) ≤ ∏ i : Fin n, f (δ i) := by
    intro δ hδ
    have hδ0 : δ 0 = x := (Finset.mem_filter.1 hδ).2
    simp only [hf, ← Real.exp_sum]
    apply Real.exp_le_exp.2
    have hle : ∀ i : Fin n, (zdistD (k + 2) L (x - δ i) : ℝ) ≤ KLmaxDist (k + 2) L δ := by
      intro i
      have : zdistD (k + 2) L (δ 0 - δ i) ≤ KLmaxDist (k + 2) L δ :=
        Finset.le_sup (f := fun q : Fin n × Fin n => zdistD (k + 2) L (δ q.1 - δ q.2))
          (Finset.mem_univ ((0 : Fin n), i))
      rw [hδ0] at this
      exact_mod_cast this
    have hsum : ∑ i : Fin n, (zdistD (k + 2) L (x - δ i) : ℝ)
        ≤ n * (KLmaxDist (k + 2) L δ : ℝ) := by
      calc _ ≤ ∑ _i : Fin n, (KLmaxDist (k + 2) L δ : ℝ) := Finset.sum_le_sum fun i _ => hle i
        _ = n * (KLmaxDist (k + 2) L δ : ℝ) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have h1 : ∑ i : Fin n, -(c / n * (zdistD (k + 2) L (x - δ i) : ℝ))
        = -(c / n * ∑ i : Fin n, (zdistD (k + 2) L (x - δ i) : ℝ)) := by
      rw [Finset.mul_sum, Finset.sum_neg_distrib]
    rw [h1]
    have h2 : c / n * ∑ i : Fin n, (zdistD (k + 2) L (x - δ i) : ℝ)
        ≤ c * (KLmaxDist (k + 2) L δ : ℝ) := by
      calc _ ≤ c / n * (n * (KLmaxDist (k + 2) L δ : ℝ)) :=
            mul_le_mul_of_nonneg_left hsum hcn.le
        _ = c * (KLmaxDist (k + 2) L δ : ℝ) := by field_simp
    linarith
  have hfx : f x = 1 := by simp [hf]
  have hfs : ∑ y, f y ≤ expC k (c / n) := sum_exp_decay_centre k hcn x
  have hf0 : 0 ≤ ∑ y, f y := Finset.sum_nonneg fun _ _ => (Real.exp_pos _).le
  calc _ ≤ ∑ δ ∈ Finset.univ.filter (fun δ : Fin n → Zd (k + 2) L => δ 0 = x), ∏ i : Fin n, f (δ i) :=
        Finset.sum_le_sum hterm
    _ = f x * (∑ y, f y) ^ (n - 1) := KWardIneq_sum_slice x f
    _ ≤ 1 * (expC k (c / n)) ^ (n - 1) := by
        rw [hfx]
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hf0 hfs _) zero_le_one
    _ = _ := one_mul _

end Short

section ShortLast

/-- **The absolute-value bound for a short last leaf** (case (S); the paper's displayed `π = ∅` bound `A:816-818` writes the last leaf as
`Θ^{(+,-)}`; paper-delta candidate `T2384b`): `∑_δ |Σ^{(∅)}(δ) ∏_{i ≠ v} Θ^{(σ_i,σ_{i+1})}(a_i, δ_i)| ≲ (1-t)⁻¹ B^{n-2}` for every `σ`.
`|Σ^{(∅)}(δ)| ≤ C_m e^{-c_m max|δ_i - δ_j|}` (`KWardIneq_MolAt`); all leaves but two are `≤ C_d B` pointwise (`KWardIneq_theta_sup`), the leaf at the
vertex `0` is summed (`∑_y |Θ(a_0, y)| ≤ (1-t)⁻¹`), the vertex `v` is free.  No cancellation and no loss `L^τ`. -/
private theorem KWardIneq_abs_sum_le (d m : ℕ) {Λ κ : ℝ} (hd : 3 ≤ d) (hm : 2 ≤ m) (hΛ : 0 < Λ) (hκ : 0 < κ)
    (hMol : KWardIneq_MolAt d (m + 1) Λ κ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → g ≤ Λ → ∀ (E : ℝ) (z : ℂ),
      haveI : NeZero L := ⟨by omega⟩
      BAReal d L g κ E z → ∀ t : ℝ, 0 ≤ t → t < 1 → ∀ (σ : Fin (m + 1) → Bool) (a : Fin (m + 1) → Zd d L),
        ∑ δ : Fin (m + 1) → Zd d L,
            ‖BASigmaPi d L (m + 1) (BAMsigma d L (BAMB d L g (E : ℂ) z)) t σ ∅ δ *
              ∏ i ∈ Finset.univ.erase (Fin.last m),
                BAThetaOf (BAMsigma d L (BAMB d L g (E : ℂ) z)) t (σ i) (σ (i + 1)) (a i) (δ i)‖
          ≤ C * (1 - t)⁻¹ * (Bparam d L g t 0) ^ (m - 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, d = k + 2 := ⟨d - 2, by omega⟩
  obtain ⟨Cm, hCm, cm, hcm, hmol⟩ := hMol
  obtain ⟨Cd, hCd, hsup⟩ := KWardIneq_theta_sup hd hΛ hκ
  have hn0 : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by positivity
  have hcn : 0 < cm / ((m + 1 : ℕ) : ℝ) := by positivity
  have hEC : 0 < expC k (cm / ((m + 1 : ℕ) : ℝ)) := by unfold expC; positivity
  refine ⟨Cm * Cd ^ (m - 1) * (expC k (cm / ((m + 1 : ℕ) : ℝ))) ^ m, by positivity, ?_⟩
  intro L hL g hg hgΛ E z
  have : NeZero L := ⟨by omega⟩
  intro hr t ht0 ht1 σ a
  set v : Fin (m + 1) := Fin.last m with hv
  set B0 := Bparam (k + 2) L g t 0 with hB0def
  have hB0 : 0 ≤ B0 := KLIndStepA_Bparam_nonneg _ _
  have hv0 : (0 : Fin (m + 1)) ∈ Finset.univ.erase v := by
    refine Finset.mem_erase.2 ⟨?_, Finset.mem_univ _⟩
    intro h
    have := congrArg Fin.val h
    simp [hv] at this
    omega
  have hcard : ((Finset.univ.erase v).erase (0 : Fin (m + 1))).card = m - 1 := by
    rw [Finset.card_erase_of_mem hv0, Finset.card_erase_of_mem (Finset.mem_univ _),
      Finset.card_univ, Fintype.card_fin]
    omega
  have hleaf : ∀ (i : Fin (m + 1)) (y w : Zd (k + 2) L),
      ‖BAThetaOf (BAMsigma (k + 2) L (BAMB (k + 2) L g (E : ℂ) z)) t (σ i) (σ (i + 1)) y w‖ ≤ Cd * B0 :=
    fun i y w => hsup L hL g hg hgΛ E z hr t ht0 ht1 (σ i) (σ (i + 1)) y w
  set e1 : (Fin (m + 1) → Zd (k + 2) L) → ℝ := fun δ =>
    Real.exp (-(cm * (KLmaxDist (k + 2) L δ : ℝ))) with he1
  set T0 : Zd (k + 2) L → ℝ := fun y =>
    ‖BAThetaOf (BAMsigma (k + 2) L (BAMB (k + 2) L g (E : ℂ) z)) t (σ 0) (σ (0 + 1)) (a 0) y‖ with hT0
  have hpt : ∀ δ : Fin (m + 1) → Zd (k + 2) L,
      ‖BASigmaPi (k + 2) L (m + 1) (BAMsigma (k + 2) L (BAMB (k + 2) L g (E : ℂ) z)) t σ ∅ δ *
          ∏ i ∈ Finset.univ.erase v,
            BAThetaOf (BAMsigma (k + 2) L (BAMB (k + 2) L g (E : ℂ) z)) t (σ i) (σ (i + 1)) (a i) (δ i)‖
        ≤ (Cm * (Cd * B0) ^ (m - 1)) * (e1 δ * T0 (δ 0)) := by
    intro δ
    rw [norm_mul, norm_prod, ← Finset.mul_prod_erase (Finset.univ.erase v) _ hv0]
    have h1 := hmol L hL g hg hgΛ E z hr t ht0 ht1 σ δ
    have h3 : ∏ i ∈ (Finset.univ.erase v).erase (0 : Fin (m + 1)),
        ‖BAThetaOf (BAMsigma (k + 2) L (BAMB (k + 2) L g (E : ℂ) z)) t (σ i) (σ (i + 1)) (a i) (δ i)‖
        ≤ (Cd * B0) ^ (m - 1) := by
      calc _ ≤ ∏ _i ∈ (Finset.univ.erase v).erase (0 : Fin (m + 1)), (Cd * B0) :=
            Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun i _ => hleaf i (a i) (δ i)
        _ = (Cd * B0) ^ (m - 1) := by rw [Finset.prod_const, hcard]
    have h4 : 0 ≤ ∏ i ∈ (Finset.univ.erase v).erase (0 : Fin (m + 1)),
        ‖BAThetaOf (BAMsigma (k + 2) L (BAMB (k + 2) L g (E : ℂ) z)) t (σ i) (σ (i + 1)) (a i) (δ i)‖ :=
      Finset.prod_nonneg fun _ _ => norm_nonneg _
    have h5 : 0 ≤ T0 (δ 0) := norm_nonneg _
    have h6 : ‖BAThetaOf (BAMsigma (k + 2) L (BAMB (k + 2) L g (E : ℂ) z)) t (σ 0) (σ (0 + 1)) (a 0) (δ 0)‖ *
          ∏ i ∈ (Finset.univ.erase v).erase (0 : Fin (m + 1)),
            ‖BAThetaOf (BAMsigma (k + 2) L (BAMB (k + 2) L g (E : ℂ) z)) t (σ i) (σ (i + 1)) (a i) (δ i)‖
        ≤ T0 (δ 0) * (Cd * B0) ^ (m - 1) := mul_le_mul le_rfl h3 h4 h5
    have h7 : 0 ≤ Cm * e1 δ := by positivity
    calc ‖BASigmaPi (k + 2) L (m + 1) (BAMsigma (k + 2) L (BAMB (k + 2) L g (E : ℂ) z)) t σ ∅ δ‖ *
          (‖BAThetaOf (BAMsigma (k + 2) L (BAMB (k + 2) L g (E : ℂ) z)) t (σ 0) (σ (0 + 1)) (a 0) (δ 0)‖ *
            ∏ i ∈ (Finset.univ.erase v).erase (0 : Fin (m + 1)),
              ‖BAThetaOf (BAMsigma (k + 2) L (BAMB (k + 2) L g (E : ℂ) z)) t (σ i) (σ (i + 1)) (a i) (δ i)‖)
        ≤ (Cm * e1 δ) * (T0 (δ 0) * (Cd * B0) ^ (m - 1)) :=
          mul_le_mul h1 h6 (mul_nonneg (norm_nonneg _) h4) h7
      _ = (Cm * (Cd * B0) ^ (m - 1)) * (e1 δ * T0 (δ 0)) := by ring
  have hsum : ∑ δ : Fin (m + 1) → Zd (k + 2) L, e1 δ * T0 (δ 0)
      ≤ (1 - t)⁻¹ * (expC k (cm / ((m + 1 : ℕ) : ℝ))) ^ m := by
    calc ∑ δ : Fin (m + 1) → Zd (k + 2) L, e1 δ * T0 (δ 0)
        = ∑ y : Zd (k + 2) L, ∑ δ ∈ Finset.univ.filter (fun δ : Fin (m + 1) → Zd (k + 2) L => δ 0 = y),
            e1 δ * T0 (δ 0) :=
          (Finset.sum_fiberwise Finset.univ (fun δ : Fin (m + 1) → Zd (k + 2) L => δ 0)
            (fun δ => e1 δ * T0 (δ 0))).symm
      _ = ∑ y : Zd (k + 2) L, T0 y *
            ∑ δ ∈ Finset.univ.filter (fun δ : Fin (m + 1) → Zd (k + 2) L => δ 0 = y), e1 δ := by
          refine Finset.sum_congr rfl fun y _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun δ hδ => ?_
          have hδ0 : δ 0 = y := (Finset.mem_filter.1 hδ).2
          simp only [hδ0]
          ring
      _ ≤ ∑ y : Zd (k + 2) L, T0 y * (expC k (cm / ((m + 1 : ℕ) : ℝ))) ^ m := by
          refine Finset.sum_le_sum fun y _ => ?_
          exact mul_le_mul_of_nonneg_left (KWardIneq_sum_exp_maxDist (n := m + 1) k hcm y)
            (norm_nonneg _)
      _ = (∑ y : Zd (k + 2) L, T0 y) * (expC k (cm / ((m + 1 : ℕ) : ℝ))) ^ m := by
          rw [Finset.sum_mul]
      _ ≤ (1 - t)⁻¹ * (expC k (cm / ((m + 1 : ℕ) : ℝ))) ^ m := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          exact KWardIneq_theta_row_le hr ht0 ht1 (σ 0) (σ (0 + 1)) (a 0)
  have hP0 : 0 ≤ Cm * (Cd * B0) ^ (m - 1) := by positivity
  calc ∑ δ : Fin (m + 1) → Zd (k + 2) L,
        ‖BASigmaPi (k + 2) L (m + 1) (BAMsigma (k + 2) L (BAMB (k + 2) L g (E : ℂ) z)) t σ ∅ δ *
          ∏ i ∈ Finset.univ.erase v,
            BAThetaOf (BAMsigma (k + 2) L (BAMB (k + 2) L g (E : ℂ) z)) t (σ i) (σ (i + 1)) (a i) (δ i)‖
      ≤ ∑ δ : Fin (m + 1) → Zd (k + 2) L, (Cm * (Cd * B0) ^ (m - 1)) * (e1 δ * T0 (δ 0)) :=
        Finset.sum_le_sum fun δ _ => hpt δ
    _ = (Cm * (Cd * B0) ^ (m - 1)) * ∑ δ : Fin (m + 1) → Zd (k + 2) L, e1 δ * T0 (δ 0) := by
        rw [Finset.mul_sum]
    _ ≤ (Cm * (Cd * B0) ^ (m - 1)) *
          ((1 - t)⁻¹ * (expC k (cm / ((m + 1 : ℕ) : ℝ))) ^ m) :=
        mul_le_mul_of_nonneg_left hsum hP0
    _ = Cm * Cd ^ (m - 1) * (expC k (cm / ((m + 1 : ℕ) : ℝ))) ^ m * (1 - t)⁻¹ * B0 ^ (m - 1) := by
        rw [mul_pow]; ring

end ShortLast

section EmptyBound

/-- **The layer `π = ∅` with the last label summed** (`n = m + 1 ≥ 3`; the BA twin of `KLWardIneq_Kpi_empty_bound`,
`Loop/KLWardIneq.lean:430`): `∑_x |K^{(∅)}(σ, a[x])| ≤ C L^τ η_t⁻¹ B_{t,0}^{n-2}`, every `σ`.  Long last leaf (`σ_v ≠ σ_{v+1}`): the column sums
of `Θ^{(σ_v,σ_{v+1})}` are `≤ (1-t)⁻¹` (`KWardIneq_theta_col_le`) and the root sum is `(eq:ind-step-bound)` (`KWardIneq_IndAt` at `k = n`,
with its cancellation), loss `L^τ`.  Short last leaf: the paper's displayed line does not cover it; `∑_x |Θ^{(s,s)}(x, b)| ≤ S` (property 5',
`KWardIneq_theta_l1`, `Θ` symmetric) and the absolute bound `KWardIneq_abs_sum_le` (`(eq:molecule-decay)` from K07, `baWardMol_holds`), no loss. -/
theorem baWardKpi_empty_bound (d m : ℕ) {Λ κ : ℝ} (hd : 3 ≤ d) (hm : 2 ≤ m) (hΛ : 0 < Λ) (hκ : 0 < κ)
    (hInd : KWardIneq_IndAt d (m + 1) Λ κ) (τ : ℝ) (hτ : 0 < τ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → g ≤ Λ → ∀ (E : ℝ) (z : ℂ),
      haveI : NeZero L := ⟨by omega⟩
      BAReal d L g κ E z → ∀ t : ℝ, 0 ≤ t → t < 1 → ∀ (σ : Fin (m + 1) → Bool) (a : Fin (m + 1) → Zd d L),
        ∑ x : Zd d L, ‖BAKpi d L (m + 1) (BAMsigma d L (BAMB d L g (E : ℂ) z)) t σ (Function.update a (Fin.last m) x) ∅‖
          ≤ C * (L : ℝ) ^ τ * ((1 - t) * z.im)⁻¹ * (Bparam d L g t 0) ^ (m - 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, d = k + 2 := ⟨d - 2, by omega⟩
  obtain ⟨Cl, hCl, hind⟩ := hInd τ hτ
  obtain ⟨Cs, hCs, habs⟩ := KWardIneq_abs_sum_le (k + 2) m hd hm hΛ hκ (baWardMol_holds hd (by omega) hΛ hκ)
  obtain ⟨S, hS0, hS⟩ := KWardIneq_theta_l1 (k := k) hd hΛ hκ
  refine ⟨Cl + S * Cs, by positivity, ?_⟩
  intro L hL g hg hgΛ E z
  have : NeZero L := ⟨by omega⟩
  intro hr t ht0 ht1 σ a
  have hB0 : 0 ≤ Bparam (k + 2) L g t 0 := KLIndStepA_Bparam_nonneg _ _
  have hBm : 0 ≤ (Bparam (k + 2) L g t 0) ^ (m - 1) := pow_nonneg hB0 _
  have hL1 := KWardIneq_one_le_rpow hL hτ
  have hLτ0 : 0 ≤ (L : ℝ) ^ τ := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hη := KWardIneq_inv_le hr hκ ht1
  have hη0 : 0 < ((1 - t) * z.im)⁻¹ := inv_pos.2 (KWardIneq_eta_pos hκ hr.2 ht1)
  have h1t : 0 < (1 - t)⁻¹ := inv_pos.2 (by linarith)
  by_cases hl : σ (Fin.last m) = σ (Fin.last m + 1)
  · -- a short last leaf
    have hcol : ∀ b : Zd (k + 2) L,
        ∑ x : Zd (k + 2) L, ‖BAThetaOf (BAMsigma (k + 2) L (BAMB (k + 2) L g (E : ℂ) z)) t (σ (Fin.last m))
          (σ (Fin.last m + 1)) x b‖ ≤ S := by
      intro b
      rw [← hl]
      have hsymm := BATheta_isSymm (k + 2) L g κ E z hr t ht0 ht1 (σ (Fin.last m)) (σ (Fin.last m))
      have hrow := hS L hL g hg hgΛ E z hr t ht0 ht1 (σ (Fin.last m)) b
      refine le_trans (le_of_eq (Finset.sum_congr rfl fun x _ => ?_)) hrow
      have h := congrFun (congrFun hsymm b) x
      rw [Matrix.transpose_apply] at h
      exact congrArg norm h
    refine (KWardIneq_sum_Kempty_le _ t σ a hcol).trans ?_
    have hX : ∑ b : Zd (k + 2) L, ‖∑ δ ∈ Finset.univ.filter
        (fun δ : Fin (m + 1) → Zd (k + 2) L => δ (Fin.last m) = b),
          BASigmaPi (k + 2) L (m + 1) (BAMsigma (k + 2) L (BAMB (k + 2) L g (E : ℂ) z)) t σ ∅ δ *
            ∏ i ∈ Finset.univ.erase (Fin.last m),
              BAThetaOf (BAMsigma (k + 2) L (BAMB (k + 2) L g (E : ℂ) z)) t (σ i) (σ (i + 1)) (a i) (δ i)‖
        ≤ Cs * (1 - t)⁻¹ * (Bparam (k + 2) L g t 0) ^ (m - 1) := by
      refine le_trans ?_ (habs L hL g hg hgΛ E z hr t ht0 ht1 σ a)
      calc _ ≤ ∑ b : Zd (k + 2) L, ∑ δ ∈ Finset.univ.filter
            (fun δ : Fin (m + 1) → Zd (k + 2) L => δ (Fin.last m) = b),
            ‖BASigmaPi (k + 2) L (m + 1) (BAMsigma (k + 2) L (BAMB (k + 2) L g (E : ℂ) z)) t σ ∅ δ *
              ∏ i ∈ Finset.univ.erase (Fin.last m),
                BAThetaOf (BAMsigma (k + 2) L (BAMB (k + 2) L g (E : ℂ) z)) t (σ i) (σ (i + 1)) (a i) (δ i)‖ :=
            Finset.sum_le_sum fun b _ => norm_sum_le _ _
        _ = _ := Finset.sum_fiberwise Finset.univ
            (fun δ : Fin (m + 1) → Zd (k + 2) L => δ (Fin.last m))
            (fun δ => ‖BASigmaPi (k + 2) L (m + 1) (BAMsigma (k + 2) L (BAMB (k + 2) L g (E : ℂ) z)) t σ ∅ δ *
              ∏ i ∈ Finset.univ.erase (Fin.last m),
                BAThetaOf (BAMsigma (k + 2) L (BAMB (k + 2) L g (E : ℂ) z)) t (σ i) (σ (i + 1)) (a i) (δ i)‖)
    calc S * ∑ b : Zd (k + 2) L, ‖∑ δ ∈ Finset.univ.filter
          (fun δ : Fin (m + 1) → Zd (k + 2) L => δ (Fin.last m) = b),
            BASigmaPi (k + 2) L (m + 1) (BAMsigma (k + 2) L (BAMB (k + 2) L g (E : ℂ) z)) t σ ∅ δ *
              ∏ i ∈ Finset.univ.erase (Fin.last m),
                BAThetaOf (BAMsigma (k + 2) L (BAMB (k + 2) L g (E : ℂ) z)) t (σ i) (σ (i + 1)) (a i) (δ i)‖
        ≤ S * (Cs * (1 - t)⁻¹ * (Bparam (k + 2) L g t 0) ^ (m - 1)) :=
          mul_le_mul_of_nonneg_left hX hS0.le
      _ ≤ S * (Cs * ((1 - t) * z.im)⁻¹ * (Bparam (k + 2) L g t 0) ^ (m - 1)) := by
          gcongr
      _ = (S * Cs) * 1 * ((1 - t) * z.im)⁻¹ * (Bparam (k + 2) L g t 0) ^ (m - 1) := by
          ring
      _ ≤ (S * Cs) * (L : ℝ) ^ τ * ((1 - t) * z.im)⁻¹
            * (Bparam (k + 2) L g t 0) ^ (m - 1) := by
          gcongr
      _ ≤ (Cl + S * Cs) * (L : ℝ) ^ τ * ((1 - t) * z.im)⁻¹
            * (Bparam (k + 2) L g t 0) ^ (m - 1) := by
          have : 0 ≤ Cl * (L : ℝ) ^ τ * ((1 - t) * z.im)⁻¹
              * (Bparam (k + 2) L g t 0) ^ (m - 1) := by positivity
          nlinarith [this]
  · -- a long last leaf
    refine (KWardIneq_sum_Kempty_le _ t σ a (fun b => KWardIneq_theta_col_le hr ht0 ht1 _ _ b)).trans ?_
    have hroot := hind L hL g hg hgΛ E z hr t ht0 ht1 σ (Fin.last m) hl a
    have e : m + 1 - 2 = m - 1 := by omega
    rw [e] at hroot
    calc (1 - t)⁻¹ * ∑ b : Zd (k + 2) L, ‖∑ δ ∈ Finset.univ.filter
          (fun δ : Fin (m + 1) → Zd (k + 2) L => δ (Fin.last m) = b),
            BASigmaPi (k + 2) L (m + 1) (BAMsigma (k + 2) L (BAMB (k + 2) L g (E : ℂ) z)) t σ ∅ δ *
              ∏ i ∈ Finset.univ.erase (Fin.last m),
                BAThetaOf (BAMsigma (k + 2) L (BAMB (k + 2) L g (E : ℂ) z)) t (σ i) (σ (i + 1)) (a i) (δ i)‖
        ≤ (1 - t)⁻¹ * (Cl * (L : ℝ) ^ τ * (Bparam (k + 2) L g t 0) ^ (m - 1)) :=
          mul_le_mul_of_nonneg_left hroot h1t.le
      _ ≤ ((1 - t) * z.im)⁻¹ * (Cl * (L : ℝ) ^ τ * (Bparam (k + 2) L g t 0) ^ (m - 1)) :=
          mul_le_mul_of_nonneg_right hη (by positivity)
      _ = Cl * (L : ℝ) ^ τ * ((1 - t) * z.im)⁻¹ * (Bparam (k + 2) L g t 0) ^ (m - 1) := by
          ring
      _ ≤ (Cl + S * Cs) * (L : ℝ) ^ τ * ((1 - t) * z.im)⁻¹
            * (Bparam (k + 2) L g t 0) ^ (m - 1) := by
          have : 0 ≤ S * Cs * (L : ℝ) ^ τ * ((1 - t) * z.im)⁻¹
              * (Bparam (k + 2) L g t 0) ^ (m - 1) := by positivity
          nlinarith [this]

end EmptyBound

/-! ## 4. The cut with the last label summed -/

section CutLabels

variable {d L : ℕ}

/-- The inner labels at the non-root vertices do not see the last vertex `v = n - 1` of the polygon (`i + k < j ≤ n - 1` for `k` below
the root; the BA twin of `KLWardIneq_aIn_update`, `Loop/KLWardIneq.lean:531`, over `BAinVinv`, `BA/KCactusCut.lean:44`). -/
private theorem KWardIneq_aIn_update {m : ℕ} (J : Fin (m + 1) × Fin (m + 1)) (hJ : J.1.val < J.2.val)
    (a : Fin (m + 1) → Zd d L) (x : Zd d L) (i : Fin (KLwIn J + 1)) (hi : i ≠ Fin.last (KLwIn J)) :
    Function.update a (Fin.last m) x (BAinVinv J i) = a (BAinVinv J i) := by
  apply Function.update_of_ne
  intro h
  have h1 := congrArg Fin.val h
  have h2 : i.val < KLwIn J := by
    have := i.isLt
    rcases Nat.lt_or_ge i.val (KLwIn J) with h | h
    · exact h
    · exact absurd (Fin.ext (by simp [Fin.val_last]; omega)) hi
  have h3 := J.2.isLt
  simp only [BAinVinv, KLwIn, Fin.val_last] at h1 h2
  omega

/-- The last vertex of the polygon is the last vertex of the outer polygon (it is not the glue vertex `i < j ≤ n - 1`), with the same
label: `a_out(a[x], u) = a_out(a, u)[x]` (the BA twin of `KLWardIneq_aOut_update`, `Loop/KLWardIneq.lean:550`, over `BAdeltaOut`,
`BA/KCactusCut.lean:59`). -/
private theorem KWardIneq_aOut_update {m : ℕ} (J : Fin (m + 1) × Fin (m + 1)) (hJ : J.1.val < J.2.val)
    (a : Fin (m + 1) → Zd d L) (w x : Zd d L) :
    BAdeltaOut J (Function.update a (Fin.last m) x) w
      = Function.update (BAdeltaOut J a w) (Fin.last (m + 1 - KLwIn J)) x := by
  have h3 := J.2.isLt
  have hw1 : 1 ≤ KLwIn J := by simp only [KLwIn]; omega
  funext k
  by_cases hk : k = Fin.last (m + 1 - KLwIn J)
  · subst hk
    have hne : Fin.last (m + 1 - KLwIn J) ≠ KLglueV J := by
      intro h
      have := congrArg Fin.val h
      simp only [Fin.val_last, KLglueV] at this
      simp only [KLwIn] at this hw1
      omega
    unfold BAdeltaOut
    rw [Function.update_of_ne hne, Function.update_self]
    have hcol : KLunCol J (m + 1 - KLwIn J) = m := by
      have hnot : ¬ (m + 1 - KLwIn J ≤ J.1.val) := by simp only [KLwIn]; omega
      unfold KLunCol
      simp only [hnot, ↓reduceIte]
      simp only [KLwIn]
      omega
    have : BAoutVinv J (Fin.last (m + 1 - KLwIn J)) = Fin.last m := by
      apply Fin.ext
      simp only [BAoutVinv, Fin.val_last, hcol]
      omega
    rw [this, Function.update_self]
  · rw [Function.update_of_ne hk]
    unfold BAdeltaOut
    by_cases hg : k = KLglueV J
    · subst hg
      simp
    · rw [Function.update_of_ne hg, Function.update_of_ne hg]
      apply Function.update_of_ne
      intro h
      have h1 := congrArg Fin.val h
      have h2 : k.val < m + 1 - KLwIn J := by
        have := k.isLt
        have hk' : k.val ≠ m + 1 - KLwIn J := fun h' => hk (Fin.ext (by simp [Fin.val_last]; omega))
        omega
      simp only [BAoutVinv, KLunCol, KLwIn] at h1 h2 hw1
      split_ifs at h1 <;> simp at h1 <;> omega

end CutLabels

/-! ## 5. The induction step: `(eq:K-pi-bound_partial)` for all `π` -/

section StepAux

variable {d L : ℕ} [NeZero L]

/-- `∑_x |∑_u ξ A(u) K(u, x)| ≤ |ξ| (∑_u |A(u)|) M` when `∑_x |K(u, x)| ≤ M` for every `u`: the summed last label stays in the outer factor
(`baKpi_cut` has one glue sum, no kernel `S^{(B)}_{uw}`; the BA twin of `KLWardIneq_norm_cut_sum_le`, `Loop/KLWardIneq.lean:605`). -/
private theorem KWardIneq_norm_cut_sum_le (ξ : ℂ) (A : Zd d L → ℂ) (K : Zd d L → Zd d L → ℂ) {M : ℝ}
    (hK : ∀ u, ∑ x, ‖K u x‖ ≤ M) :
    ∑ x : Zd d L, ‖∑ u : Zd d L, ξ * A u * K u x‖ ≤ ‖ξ‖ * (∑ u : Zd d L, ‖A u‖) * M := by
  calc ∑ x, ‖∑ u, ξ * A u * K u x‖
      ≤ ∑ x, ∑ u, ‖ξ‖ * ‖A u‖ * ‖K u x‖ := by
        refine Finset.sum_le_sum fun x _ => ?_
        refine (norm_sum_le _ _).trans (le_of_eq ?_)
        refine Finset.sum_congr rfl fun u _ => ?_
        simp only [norm_mul]
    _ = ∑ u, ‖ξ‖ * ‖A u‖ * ∑ x, ‖K u x‖ := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun u _ => ?_
        rw [Finset.mul_sum]
    _ ≤ ∑ u, ‖ξ‖ * ‖A u‖ * M := by
        refine Finset.sum_le_sum fun u _ => ?_
        exact mul_le_mul_of_nonneg_left (hK u) (by positivity)
    _ = ‖ξ‖ * (∑ u, ‖A u‖) * M := by
        rw [Finset.mul_sum, Finset.sum_mul]

end StepAux

section Step

/-- **The induction step** (strong induction on the number `n = m + 1` of polygon vertices, as `KLWardIneq_Kpi_step`,
`Loop/KLWardIneq.lean:675`): the bound at `n ≥ 3` follows from the bound at every `3 ≤ n'' < n`.  The layer `π = ∅` is
`baWardKpi_empty_bound`; a layer `π ≠ ∅` is cut at an innermost long edge (`baKpi_cut`, K10): the inner polygon `k = j - i + 1 ∈ [3, n-1]` has root
sum `≺ B^{k-2}` (`KWardIneq_IndAt`, `L^{τ/2}`), the summed last label `x` is the last label of the outer polygon
(`n'' = n - (j - i) + 1 ∈ [3, n-1]`), whose bound is `L^{τ/2} η_t⁻¹ B^{n''-2}`; `(k-2) + (n''-2) = n - 2`, `L^{τ/2} L^{τ/2} = L^τ`, and `η_t⁻¹`
appears exactly once.  The chord is the glue leaf `tΘ` of the outer polygon (no `S^{(B)}`, paper-delta candidate `T2381a`). -/
theorem baWardKpi_step (d m : ℕ) {Λ κ : ℝ} (hd : 3 ≤ d) (hm : 2 ≤ m) (hΛ : 0 < Λ) (hκ : 0 < κ)
    (hInd : ∀ k : ℕ, 3 ≤ k → k ≤ m + 1 → ∀ [NeZero k], KWardIneq_IndAt d k Λ κ)
    (hout : ∀ m'' : ℕ, 2 ≤ m'' → m'' < m → BAWardKpiAt d m'' Λ κ) :
    BAWardKpiAt d m Λ κ := by
  intro τ hτ
  have hτ2 : 0 < τ / 2 := half_pos hτ
  have hn : 3 ≤ m + 1 := by omega
  obtain ⟨C₀, hC₀, H₀⟩ := baWardKpi_empty_bound d m hd hm hΛ hκ (hInd (m + 1) hn le_rfl) τ hτ
  -- the inner constants (at `τ/2`) and the outer constants (at `τ/2`), one per width
  have hin : ∀ k : ℕ, ∃ C : ℝ, 0 < C ∧ (3 ≤ k → k ≤ m + 1 → ∀ [NeZero k], ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g →
      g ≤ Λ → ∀ (E : ℝ) (z : ℂ),
      haveI : NeZero L := ⟨by omega⟩
      BAReal d L g κ E z → ∀ t : ℝ, 0 ≤ t → t < 1 → ∀ (σ : Fin k → Bool) (r : Fin k), σ r ≠ σ (r + 1) →
        ∀ a : Fin k → Zd d L,
          ∑ b : Zd d L, ‖∑ δ ∈ Finset.univ.filter (fun δ : Fin k → Zd d L => δ r = b),
              BASigmaPi d L k (BAMsigma d L (BAMB d L g (E : ℂ) z)) t σ ∅ δ *
                ∏ j ∈ Finset.univ.erase r,
                  BAThetaOf (BAMsigma d L (BAMB d L g (E : ℂ) z)) t (σ j) (σ (j + 1)) (a j) (δ j)‖
            ≤ C * (L : ℝ) ^ (τ / 2) * (Bparam d L g t 0) ^ (k - 2)) := by
    intro k
    by_cases hk : 3 ≤ k ∧ k ≤ m + 1
    · have : NeZero k := ⟨by omega⟩
      obtain ⟨C, hC, H⟩ := hInd k hk.1 hk.2 (τ / 2) hτ2
      exact ⟨C, hC, fun _ _ _ => H⟩
    · exact ⟨1, one_pos, fun h1 h2 => absurd ⟨h1, h2⟩ hk⟩
  have hout' : ∀ k : ℕ, ∃ C : ℝ, 0 < C ∧ (2 ≤ k → k < m → ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → g ≤ Λ →
      ∀ (E : ℝ) (z : ℂ),
      haveI : NeZero L := ⟨by omega⟩
      BAReal d L g κ E z → ∀ t : ℝ, 0 ≤ t → t < 1 → ∀ (σ : Fin (k + 1) → Bool)
        (π : Finset (Fin (k + 1) × Fin (k + 1))) (a : Fin (k + 1) → Zd d L),
        ∑ x : Zd d L, ‖BAKpi d L (k + 1) (BAMsigma d L (BAMB d L g (E : ℂ) z)) t σ
            (Function.update a (Fin.last k) x) π‖
          ≤ C * (L : ℝ) ^ (τ / 2) * ((1 - t) * z.im)⁻¹ * (Bparam d L g t 0) ^ (k - 1)) := by
    intro k
    by_cases hk : 2 ≤ k ∧ k < m
    · obtain ⟨C, hC, H⟩ := hout k hk.1 hk.2 (τ / 2) hτ2
      exact ⟨C, hC, fun _ _ => H⟩
    · exact ⟨1, one_pos, fun h2 hlt => absurd ⟨h2, hlt⟩ hk⟩
  choose Ci hCi0 hCi using hin
  choose Co hCo0 hCo using hout'
  have hsum0 : 0 ≤ ∑ w ∈ Finset.range (m + 1), Ci (w + 1) * Co (m + 1 - w) :=
    Finset.sum_nonneg fun w _ => mul_nonneg (hCi0 _).le (hCo0 _).le
  refine ⟨C₀ + ∑ w ∈ Finset.range (m + 1), Ci (w + 1) * Co (m + 1 - w), by positivity, ?_⟩
  intro L hL g hg hgΛ E z
  have : NeZero L := ⟨by omega⟩
  intro hr t ht0 ht1 σ π a
  have hB0 : 0 ≤ Bparam d L g t 0 := KLIndStepA_Bparam_nonneg _ _
  have hLτ0 : 0 ≤ (L : ℝ) ^ τ := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hBm : 0 ≤ (Bparam d L g t 0) ^ (m - 1) := pow_nonneg hB0 _
  have hηpos : 0 < (1 - t) * z.im := KWardIneq_eta_pos hκ hr.2 ht1
  have hη0 : 0 < ((1 - t) * z.im)⁻¹ := inv_pos.2 hηpos
  have hRHS : 0 ≤ (C₀ + ∑ w ∈ Finset.range (m + 1), Ci (w + 1) * Co (m + 1 - w)) * (L : ℝ) ^ τ
      * ((1 - t) * z.im)⁻¹ * (Bparam d L g t 0) ^ (m - 1) := by positivity
  by_cases hπ0 : π = ∅
  · -- the layer `π = ∅`
    subst hπ0
    refine (H₀ L hL g hg hgΛ E z hr t ht0 ht1 σ a).trans ?_
    have : 0 ≤ (∑ w ∈ Finset.range (m + 1), Ci (w + 1) * Co (m + 1 - w)) * (L : ℝ) ^ τ
        * ((1 - t) * z.im)⁻¹ * (Bparam d L g t 0) ^ (m - 1) := by positivity
    nlinarith [this]
  rcases (KLTSPlong (m + 1) σ π).eq_empty_or_nonempty with hemp | ⟨F₀, hF₀⟩
  · -- no tree has the long edges `π`
    have hz : ∀ x : Zd d L,
        BAKpi d L (m + 1) (BAMsigma d L (BAMB d L g (E : ℂ) z)) t σ (Function.update a (Fin.last m) x) π = 0 :=
      fun x => by simp only [BAKpi, hemp, Finset.sum_empty]
    simp only [hz, norm_zero, Finset.sum_const_zero]
    exact hRHS
  obtain ⟨hF₀T, hπ⟩ := Finset.mem_filter.1 hF₀
  have hsub : π ⊆ diagonals (m + 1) := by
    rw [← hπ]; exact Flong_subset_diagonals hF₀T σ
  obtain ⟨J, hJ, hinner⟩ := exists_innermost hsub (Finset.nonempty_iff_ne_empty.2 hπ0)
  have hJd : IsDiag (m + 1) J.1 J.2 := (Finset.mem_filter.1 (hsub hJ)).2
  have hJlong : σ J.1 ≠ σ J.2 := by
    have hJ' : J ∈ KLFlong F₀ σ := by rw [hπ]; exact hJ
    exact (Finset.mem_filter.1 hJ').2
  obtain ⟨hJ12, hJadj, hJwhole⟩ := hJd
  rw [Fin.lt_def] at hJ12
  have hJ2n := J.2.isLt
  have hw2 : 2 ≤ KLwIn J := by simp only [KLwIn]; omega
  have hwn : KLwIn J + 2 ≤ m + 1 := by
    simp only [KLwIn]
    by_cases h0 : J.1.val = 0
    · have : J.2.val ≠ m + 1 - 1 := fun h => hJwhole ⟨h0, h⟩
      omega
    · omega
  -- the inner root sum, independent of the last label
  set A : Zd d L → ℂ := fun u => ∑ δ ∈ Finset.univ.filter
      (fun δ : Fin (KLwIn J + 1) → Zd d L => δ (Fin.last (KLwIn J)) = u),
        BASigmaPi d L (KLwIn J + 1) (BAMsigma d L (BAMB d L g (E : ℂ) z)) t (sigmaIn σ J) ∅ δ *
          ∏ k ∈ Finset.univ.erase (Fin.last (KLwIn J)),
            BAThetaOf (BAMsigma d L (BAMB d L g (E : ℂ) z)) t (sigmaIn σ J k) (sigmaIn σ J (k + 1))
              (a (BAinVinv J k)) (δ k) with hAdef
  have hcut : ∀ x : Zd d L,
      BAKpi d L (m + 1) (BAMsigma d L (BAMB d L g (E : ℂ) z)) t σ (Function.update a (Fin.last m) x) π
        = ∑ u : Zd d L, (t : ℂ) * A u *
            BAKpi d L (m + 1 - KLwIn J + 1) (BAMsigma d L (BAMB d L g (E : ℂ) z)) t (sigmaOut σ J)
              (Function.update (BAdeltaOut J a u) (Fin.last (m + 1 - KLwIn J)) x)
              ((π.erase J).image (KLshiftOut J)) := by
    intro x
    rw [baKpi_cut hn (BAMsigma d L (BAMB d L g (E : ℂ) z)) t σ hF₀T hπ hJ hinner
      (Function.update a (Fin.last m) x)]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [KWardIneq_aOut_update J hJ12 a u x]
    have hAx : (∑ δ ∈ Finset.univ.filter
        (fun δ : Fin (KLwIn J + 1) → Zd d L => δ (Fin.last (KLwIn J)) = u),
          BASigmaPi d L (KLwIn J + 1) (BAMsigma d L (BAMB d L g (E : ℂ) z)) t (sigmaIn σ J) ∅ δ *
            ∏ k ∈ Finset.univ.erase (Fin.last (KLwIn J)),
              BAThetaOf (BAMsigma d L (BAMB d L g (E : ℂ) z)) t (sigmaIn σ J k) (sigmaIn σ J (k + 1))
                (Function.update a (Fin.last m) x (BAinVinv J k)) (δ k)) = A u := by
      refine Finset.sum_congr rfl fun δ _ => ?_
      congr 1
      refine Finset.prod_congr rfl fun k hk => ?_
      rw [KWardIneq_aIn_update J hJ12 a x k (Finset.ne_of_mem_erase hk)]
    rw [hAx]
  have hB : ∀ u : Zd d L, ∑ x : Zd d L, ‖BAKpi d L (m + 1 - KLwIn J + 1)
      (BAMsigma d L (BAMB d L g (E : ℂ) z)) t (sigmaOut σ J)
      (Function.update (BAdeltaOut J a u) (Fin.last (m + 1 - KLwIn J)) x)
      ((π.erase J).image (KLshiftOut J))‖
        ≤ Co (m + 1 - KLwIn J) * (L : ℝ) ^ (τ / 2) * ((1 - t) * z.im)⁻¹ *
          (Bparam d L g t 0) ^ (m + 1 - KLwIn J - 1) := fun u =>
    hCo (m + 1 - KLwIn J) (by omega) (by omega) L hL g hg hgΛ E z hr t ht0 ht1 (sigmaOut σ J) _
      (BAdeltaOut J a u)
  have hroot : sigmaIn σ J (Fin.last (KLwIn J)) ≠ sigmaIn σ J (Fin.last (KLwIn J) + 1) := by
    rw [Fin.last_add_one]
    have e1 : sigmaIn σ J (Fin.last (KLwIn J)) = σ J.2 := by
      simp only [sigmaIn, Fin.val_last]
      congr 1
      ext
      simp only [KLwIn]
      omega
    have e2 : sigmaIn σ J 0 = σ J.1 := by
      simp only [sigmaIn, Fin.val_zero, add_zero]
      congr 1
      ext
      simp only
      omega
    rw [e1, e2]
    exact Ne.symm hJlong
  have hA : ∑ u : Zd d L, ‖A u‖
      ≤ Ci (KLwIn J + 1) * (L : ℝ) ^ (τ / 2) * (Bparam d L g t 0) ^ (KLwIn J + 1 - 2) :=
    hCi (KLwIn J + 1) (by omega) (by omega) L hL g hg hgΛ E z hr t ht0 ht1 (sigmaIn σ J)
      (Fin.last (KLwIn J)) hroot (fun k => a (BAinVinv J k))
  have hξ : ‖((t : ℝ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_of_nonneg ht0]; exact ht1.le
  simp only [hcut]
  refine (KWardIneq_norm_cut_sum_le _ _ _ hB).trans ?_
  have hM0 : 0 ≤ Co (m + 1 - KLwIn J) * (L : ℝ) ^ (τ / 2) * ((1 - t) * z.im)⁻¹ *
      (Bparam d L g t 0) ^ (m + 1 - KLwIn J - 1) :=
    mul_nonneg (mul_nonneg (mul_nonneg (hCo0 _).le (Real.rpow_nonneg (Nat.cast_nonneg _) _))
      hη0.le) (pow_nonneg hB0 _)
  have hsumA : 0 ≤ ∑ u : Zd d L, ‖A u‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hpow : (Bparam d L g t 0) ^ (KLwIn J + 1 - 2) *
      (Bparam d L g t 0) ^ (m + 1 - KLwIn J - 1) = (Bparam d L g t 0) ^ (m - 1) := by
    rw [← pow_add]; congr 1; omega
  have hLL : (L : ℝ) ^ (τ / 2) * (L : ℝ) ^ (τ / 2) = (L : ℝ) ^ τ := by
    rw [← Real.rpow_add (by exact_mod_cast (by omega : 0 < L)), add_halves]
  have hterm : Ci (KLwIn J + 1) * Co (m + 1 - KLwIn J)
      ≤ ∑ w ∈ Finset.range (m + 1), Ci (w + 1) * Co (m + 1 - w) :=
    Finset.single_le_sum (f := fun w => Ci (w + 1) * Co (m + 1 - w))
      (fun w _ => mul_nonneg (hCi0 _).le (hCo0 _).le) (Finset.mem_range.2 (by omega))
  calc ‖((t : ℝ) : ℂ)‖ * (∑ u : Zd d L, ‖A u‖) *
        (Co (m + 1 - KLwIn J) * (L : ℝ) ^ (τ / 2) * ((1 - t) * z.im)⁻¹ *
          (Bparam d L g t 0) ^ (m + 1 - KLwIn J - 1))
      ≤ 1 * (Ci (KLwIn J + 1) * (L : ℝ) ^ (τ / 2) *
            (Bparam d L g t 0) ^ (KLwIn J + 1 - 2)) *
          (Co (m + 1 - KLwIn J) * (L : ℝ) ^ (τ / 2) * ((1 - t) * z.im)⁻¹ *
            (Bparam d L g t 0) ^ (m + 1 - KLwIn J - 1)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul hξ hA hsumA zero_le_one) hM0
    _ = (Ci (KLwIn J + 1) * Co (m + 1 - KLwIn J)) *
          ((L : ℝ) ^ (τ / 2) * (L : ℝ) ^ (τ / 2)) * ((1 - t) * z.im)⁻¹ *
          ((Bparam d L g t 0) ^ (KLwIn J + 1 - 2) *
            (Bparam d L g t 0) ^ (m + 1 - KLwIn J - 1)) := by ring
    _ = (Ci (KLwIn J + 1) * Co (m + 1 - KLwIn J)) * (L : ℝ) ^ τ * ((1 - t) * z.im)⁻¹ *
          (Bparam d L g t 0) ^ (m - 1) := by rw [hLL, hpow]
    _ ≤ (C₀ + ∑ w ∈ Finset.range (m + 1), Ci (w + 1) * Co (m + 1 - w)) * (L : ℝ) ^ τ *
          ((1 - t) * z.im)⁻¹ * (Bparam d L g t 0) ^ (m - 1) := by
        have h1 : Ci (KLwIn J + 1) * Co (m + 1 - KLwIn J)
            ≤ C₀ + ∑ w ∈ Finset.range (m + 1), Ci (w + 1) * Co (m + 1 - w) := by linarith
        gcongr

/-- **`(eq:K-pi-bound_partial)` is proved** for every `n = m + 1 ≥ 3`, every `π`: strong induction on `m` with `baWardKpi_step`; the premise is
`(eq:ind-step-bound)` at every `k ∈ [3, m + 1]` (`KWardIneq_IndAt`). -/
theorem baWardKpi_holds (d m : ℕ) {Λ κ : ℝ} (hd : 3 ≤ d) (hm : 2 ≤ m) (hΛ : 0 < Λ) (hκ : 0 < κ)
    (hInd : ∀ k : ℕ, 3 ≤ k → k ≤ m + 1 → ∀ [NeZero k], KWardIneq_IndAt d k Λ κ) :
    BAWardKpiAt d m Λ κ := by
  have key : ∀ m : ℕ, 2 ≤ m → (∀ k : ℕ, 3 ≤ k → k ≤ m + 1 → ∀ [NeZero k], KWardIneq_IndAt d k Λ κ) →
      BAWardKpiAt d m Λ κ := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro hm hI
      exact baWardKpi_step d m hd hm hΛ hκ hI
        (fun m'' h2 hlt => ih m'' hlt h2 (fun k hk1 hk2 => hI k hk1 (by omega)))
  exact key m hm hInd

end Step

/-! ## 6. `n = 2`, the assembly over the layers, the statement `lem_wardineq_K` -/

section Assembly

/-- **`(wardineq_K)` at `n = 2`**, every `σ` (also `(s, s)`): `∑_x |𝒦^{(2)}(σ, (a₁, x))| = W^{-d} ∑_x |(Θ^{(σ₀,σ₁)} M^{(σ₀,σ₁)})(a₁, x)| ≤
W^{-d} (1-t)⁻¹ ≤ (W^d η_t)⁻¹` (`baKsol_two`, `(Kn2sol)`; `Σ_x |M^{(σσ')}_{zx}| = Σ_x K_{zx} = 1` and `Σ_z |Θ(a₁, z)| ≤ (1-t)⁻¹`; no hypothesis on `d`;
the band twin `KLWardIneq_At_two`, `Loop/KLWardIneq.lean:863`). -/
theorem baWardIneq_two (d : ℕ) {Λ κ : ℝ} (hκ : 0 < κ) : BAWardIneqAt d 2 Λ κ := by
  intro τ hτ
  refine ⟨1, one_pos, ?_⟩
  intro L hL W hW g hg hgΛ E m
  have : NeZero L := ⟨by omega⟩
  intro hr t ht0 ht1 σ a
  have hloop : ∀ x : Zd d L, (⟨List.ofFn σ, List.ofFn a ++ [x]⟩ : LoopIdx (Zd d L)) = KLloopOf d L σ ![a 0, x] := by
    intro x
    simp [KLloopOf, List.ofFn_succ]
  have h2 : ∀ x : Zd d L,
      BAKsol d L W (BAMsigma d L (BAMB d L g (E : ℂ) m)) (PropSpin m) t ⟨List.ofFn σ, List.ofFn a ++ [x]⟩
        = (((W : ℂ) ^ d)⁻¹) *
          (BATheta d L g E m t (σ 0) (σ 1) * BAMss d L (BAMB d L g (E : ℂ) m) (σ 0) (σ 1)) (a 0) x := by
    intro x
    rw [hloop x, baKsol_two d hκ hg hL W hr ⟨ht0, ht1⟩ σ ![a 0, x]]
    simp
  have hW0 : 0 ≤ ((W : ℝ) ^ d)⁻¹ := by positivity
  have hrow : ∑ x : Zd d L, ‖(BATheta d L g E m t (σ 0) (σ 1) *
      BAMss d L (BAMB d L g (E : ℂ) m) (σ 0) (σ 1)) (a 0) x‖ ≤ (1 - t)⁻¹ := by
    calc ∑ x : Zd d L, ‖(BATheta d L g E m t (σ 0) (σ 1) * BAMss d L (BAMB d L g (E : ℂ) m) (σ 0) (σ 1)) (a 0) x‖
        ≤ ∑ x : Zd d L, ∑ y : Zd d L, ‖BATheta d L g E m t (σ 0) (σ 1) (a 0) y‖ *
            ‖BAMss d L (BAMB d L g (E : ℂ) m) (σ 0) (σ 1) y x‖ := by
          refine Finset.sum_le_sum fun x _ => ?_
          rw [Matrix.mul_apply]
          refine (norm_sum_le _ _).trans (le_of_eq ?_)
          exact Finset.sum_congr rfl fun y _ => norm_mul _ _
      _ = ∑ y : Zd d L, ‖BATheta d L g E m t (σ 0) (σ 1) (a 0) y‖ *
            ∑ x : Zd d L, ‖BAMss d L (BAMB d L g (E : ℂ) m) (σ 0) (σ 1) y x‖ := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun y _ => (Finset.mul_sum _ _ _).symm
      _ = ∑ y : Zd d L, ‖BATheta d L g E m t (σ 0) (σ 1) (a 0) y‖ := by
          refine Finset.sum_congr rfl fun y _ => ?_
          simp only [BAMss_norm_eq_BAK]
          rw [BAK_row_sum d L g E m hr.1 y, mul_one]
      _ ≤ (1 - t)⁻¹ := KWardIneq_theta_row_le hr ht0 ht1 (σ 0) (σ 1) (a 0)
  have hη := KWardIneq_inv_le hr hκ ht1
  have hηpos := KWardIneq_eta_pos hκ hr.2 ht1
  have hL1 := KWardIneq_one_le_rpow hL hτ
  simp only [h2, norm_mul, norm_inv, norm_pow, Complex.norm_natCast]
  rw [← Finset.mul_sum]
  rw [show (2 : ℕ) - 2 = 0 from rfl, pow_zero, mul_one, one_mul, mul_inv]
  calc ((W : ℝ) ^ d)⁻¹ * ∑ x : Zd d L, ‖(BATheta d L g E m t (σ 0) (σ 1) *
          BAMss d L (BAMB d L g (E : ℂ) m) (σ 0) (σ 1)) (a 0) x‖
      ≤ ((W : ℝ) ^ d)⁻¹ * ((1 - t) * m.im)⁻¹ :=
        mul_le_mul_of_nonneg_left (hrow.trans hη) hW0
    _ = 1 * (((W : ℝ) ^ d)⁻¹ * ((1 - t) * m.im)⁻¹) := (one_mul _).symm
    _ ≤ (L : ℝ) ^ τ * (((W : ℝ) ^ d)⁻¹ * ((1 - t) * m.im)⁻¹) :=
        mul_le_mul_of_nonneg_right hL1 (by positivity)

/-- **`(wardineq_K)` for `n = m + 1 ≥ 3`, from the layers**: `(eq_K-Kpi)` (`baK_eq_sum_Kpi`, K06) gives the prefactor `W^{-d(n-1)}`, the same for every
`π`, times the sum over the `2^{|diagonals n|}` layers, each `∑_x |K^{(π)}| ≺ η_t⁻¹ B^{n-2}` (`BAWardKpiAt`): `(W^d)^{-(n-1)} η_t⁻¹ B^{n-2} =
(W^d η_t)⁻¹ (W^{-d} B)^{n-2}` (the band twin `KLWardIneq_At_of_Kpi`, `Loop/KLWardIneq.lean:898`). -/
theorem baWardIneq_of_Kpi (d m : ℕ) {Λ κ : ℝ} (hκ : 0 < κ) (hm : 2 ≤ m) (h : BAWardKpiAt d m Λ κ) :
    BAWardIneqAt d (m + 1) Λ κ := by
  intro τ hτ
  obtain ⟨C, hC, H⟩ := h τ hτ
  refine ⟨2 ^ (diagonals (m + 1)).card * C, by positivity, ?_⟩
  intro L hL W hW g hg hgΛ E z
  have : NeZero L := ⟨by omega⟩
  intro hr t ht0 ht1 σ a
  have hn : 3 ≤ m + 1 := by omega
  have hB0 : 0 ≤ Bparam d L g t 0 := KLIndStepA_Bparam_nonneg _ _
  have hLτ0 : 0 ≤ (L : ℝ) ^ τ := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hW0 : 0 ≤ ((W : ℝ) ^ d)⁻¹ := by positivity
  have hηpos := KWardIneq_eta_pos hκ hr.2 ht1
  have hloop : ∀ x : Zd d L,
      (⟨List.ofFn σ, List.ofFn a ++ [x]⟩ : LoopIdx (Zd d L))
        = KLloopOf d L σ (Fin.snoc (α := fun _ => Zd d L) a x) := by
    intro x
    simp only [KLloopOf]
    congr 1
    rw [List.ofFn_succ']
    simp [Fin.snoc_castSucc, Fin.snoc_last]
  have hterm : ∀ x : Zd d L,
      ‖BAKsol d L W (BAMsigma d L (BAMB d L g (E : ℂ) z)) (PropSpin z) t ⟨List.ofFn σ, List.ofFn a ++ [x]⟩‖
        ≤ ((W : ℝ) ^ d)⁻¹ ^ m * ∑ π ∈ (diagonals (m + 1)).powerset,
            ‖BAKpi d L (m + 1) (BAMsigma d L (BAMB d L g (E : ℂ) z)) t σ
              (Function.update (Fin.snoc (α := fun _ => Zd d L) a 0) (Fin.last m) x) π‖ := by
    intro x
    rw [hloop, baK_eq_sum_Kpi d hκ hg hL W hr ⟨ht0, ht1⟩ hn σ _, norm_mul, norm_pow, norm_inv,
      norm_pow, Complex.norm_natCast, Nat.add_sub_cancel, Fin.update_snoc_last]
    exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) (pow_nonneg hW0 _)
  calc ∑ x : Zd d L, ‖BAKsol d L W (BAMsigma d L (BAMB d L g (E : ℂ) z)) (PropSpin z) t
          ⟨List.ofFn σ, List.ofFn a ++ [x]⟩‖
      ≤ ∑ x : Zd d L, ((W : ℝ) ^ d)⁻¹ ^ m * ∑ π ∈ (diagonals (m + 1)).powerset,
            ‖BAKpi d L (m + 1) (BAMsigma d L (BAMB d L g (E : ℂ) z)) t σ
              (Function.update (Fin.snoc (α := fun _ => Zd d L) a 0) (Fin.last m) x) π‖ :=
        Finset.sum_le_sum fun x _ => hterm x
    _ = ((W : ℝ) ^ d)⁻¹ ^ m * ∑ π ∈ (diagonals (m + 1)).powerset, ∑ x : Zd d L,
            ‖BAKpi d L (m + 1) (BAMsigma d L (BAMB d L g (E : ℂ) z)) t σ
              (Function.update (Fin.snoc (α := fun _ => Zd d L) a 0) (Fin.last m) x) π‖ := by
        rw [← Finset.mul_sum, Finset.sum_comm]
    _ ≤ ((W : ℝ) ^ d)⁻¹ ^ m * ∑ _π ∈ (diagonals (m + 1)).powerset,
            C * (L : ℝ) ^ τ * ((1 - t) * z.im)⁻¹ * (Bparam d L g t 0) ^ (m - 1) :=
        mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum fun π _ => H L hL g hg hgΛ E z hr t ht0 ht1 σ π _) (pow_nonneg hW0 _)
    _ = ((W : ℝ) ^ d)⁻¹ ^ m * (2 ^ (diagonals (m + 1)).card *
            (C * (L : ℝ) ^ τ * ((1 - t) * z.im)⁻¹ * (Bparam d L g t 0) ^ (m - 1))) := by
        rw [Finset.sum_const, Finset.card_powerset, nsmul_eq_mul]
        push_cast
        ring
    _ = 2 ^ (diagonals (m + 1)).card * C * (L : ℝ) ^ τ *
          (((W : ℝ) ^ d) * ((1 - t) * z.im))⁻¹ *
          (((W : ℝ) ^ d)⁻¹ * Bparam d L g t 0) ^ (m + 1 - 2) := by
        have e : m + 1 - 2 = m - 1 := by omega
        have hpow : ((W : ℝ) ^ d)⁻¹ ^ m = ((W : ℝ) ^ d)⁻¹ ^ (m - 1) * ((W : ℝ) ^ d)⁻¹ := by
          rw [← pow_succ]; congr 1; omega
        rw [e, mul_inv ((W : ℝ) ^ d) ((1 - t) * z.im), mul_pow, hpow]
        ring

/-- **`lem_wardineq_K`, `(wardineq_K)`, at BA, conditional on `(eq:ind-step-bound)`** (`3_5_Loop_Hierarchy.tex:1001-1012`, proof
`A_deterministic_estimates.tex:809-827`): `BAWardIneqAt d n Λ κ` for every `n ≥ 2`, uniformly in `L, W, g ∈ (0, Λ], t ∈ [0,1)` and the real-axis data:
`n = 2` is `baWardIneq_two`, `n ≥ 3` is `baWardIneq_of_Kpi` and `baWardKpi_holds`.  The premises are `KWardIneq_IndAt d k Λ κ` at `k ∈ [3, n]`
(`(eq:ind-step-bound)` at BA, K09b/K12; `(eq:molecule-decay)` is proved, `baWardMol_holds`).  A conditional form, not the unconditional lemma
(paper-delta candidate `T2384c`). -/
theorem baWardIneq_holds (d n : ℕ) {Λ κ : ℝ} (hd : 3 ≤ d) (hn : 2 ≤ n) (hΛ : 0 < Λ) (hκ : 0 < κ)
    (hInd : ∀ k : ℕ, 3 ≤ k → k ≤ n → ∀ [NeZero k], KWardIneq_IndAt d k Λ κ) :
    BAWardIneqAt d n Λ κ := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rcases (show m = 1 ∨ 2 ≤ m by omega) with rfl | hm
  · exact baWardIneq_two d hκ
  · exact baWardIneq_of_Kpi d m hκ hm (baWardKpi_holds d m hd hm hΛ hκ hInd)

end Assembly

/-! ## 7. Compiled nonempty instances

Datum: the merged flow point `P` of `(d, L) = (3, 4)` (`BA/MFixedPoint.lean:893`; `P.real : BAReal 3 4 P.g0 (Im m₀) P.E P.m₀`,
`0 < P.g0 ≤ 10`; no smallness of `g` is used), `Λ = 10`, `κ = Im m₀ > 0`, `W = 2` (`W^d = 8`), `t = 1/2`, `τ = 1`.
`n = 2`: `baWardIneq_two` at `σ = (+,-)` and `(+,+)`, no premise.  `n = 3, 4`: `baWardIneq_holds` at `σ = (+,-,+)` and `(+,+,-,-)` (spread
labels, the last label summed); the layer form at `n = 4`: `baWardKpi_empty_bound` at `σ = (+,+,-,-)` (long last leaf) and `σ = (+,+,-,+)`
(short last leaf, case (S)), `baWardKpi_step` at `m = 3` and the three layers `∅`, `{(0,2)}`, `{(1,3)}` of `σ = (+,+,-,-)` (both chords are long,
`n_in = n_out = 3`; the induction hypothesis at `m'' = 2` is the proved `baWardKpi_holds`), `baWardIneq_of_Kpi`.  The only hypotheses left are the
premises `KWardIneq_IndAt` (`(eq:ind-step-bound)`, K09b/K12's pin; K12 gets it from `KWardIneq_IndAt_of_abs`); `(eq:molecule-decay)` is proved
(`baWardMol_holds`), every other hypothesis is discharged at the data. -/

namespace KWardIneqInst

open RBM.BA.MFixedPointInst

/-- The flow point is a datum of the family `KWardIneq_Data`. -/
example : Nonempty (KWardIneq_Data 3 10 P.m0.im) :=
  ⟨⟨4, by norm_num, P.g0, P.g0_pos, P.g0_le, P.E, P.m0, P.real, 1 / 2, by norm_num, by norm_num⟩⟩

/-- **`baWardIneq_two`** at the flow point (`n = 2`, `σ = (+,-)` and `(+,+)`, `W = 2`, `t = 1/2`, `τ = 1`): `∑_x |𝒦^{(2)}(σ, (a₁, x))| ≤ C L^τ (W^d η_t)⁻¹`. -/
example : (∃ C : ℝ, 0 < C ∧
      ∑ x : Zd 3 4, ‖BAKsol 3 4 2 (BAMsigma 3 4 (BAMB 3 4 P.g0 (P.E : ℂ) P.m0)) (PropSpin P.m0) (1 / 2)
          ⟨List.ofFn ![true, false], List.ofFn ![![0, 0, 0]] ++ [x]⟩‖
        ≤ C * (4 : ℝ) ^ (1 : ℝ) * (((2 : ℝ) ^ 3) * ((1 - 1 / 2) * P.m0.im))⁻¹ *
          (((2 : ℝ) ^ 3)⁻¹ * Bparam 3 4 P.g0 (1 / 2) 0) ^ (2 - 2)) ∧
    (∃ C : ℝ, 0 < C ∧
      ∑ x : Zd 3 4, ‖BAKsol 3 4 2 (BAMsigma 3 4 (BAMB 3 4 P.g0 (P.E : ℂ) P.m0)) (PropSpin P.m0) (1 / 2)
          ⟨List.ofFn ![true, true], List.ofFn ![![0, 0, 0]] ++ [x]⟩‖
        ≤ C * (4 : ℝ) ^ (1 : ℝ) * (((2 : ℝ) ^ 3) * ((1 - 1 / 2) * P.m0.im))⁻¹ *
          (((2 : ℝ) ^ 3)⁻¹ * Bparam 3 4 P.g0 (1 / 2) 0) ^ (2 - 2)) := by
  obtain ⟨C, hC, H⟩ := baWardIneq_two 3 (Λ := 10) P.real.1.1 1 one_pos
  exact ⟨⟨C, hC, H 4 (by norm_num) 2 (by norm_num) P.g0 P.g0_pos P.g0_le P.E P.m0 P.real (1 / 2)
      (by norm_num) (by norm_num) ![true, false] ![![0, 0, 0]]⟩,
    ⟨C, hC, H 4 (by norm_num) 2 (by norm_num) P.g0 P.g0_pos P.g0_le P.E P.m0 P.real (1 / 2)
      (by norm_num) (by norm_num) ![true, true] ![![0, 0, 0]]⟩⟩

/-- **`baWardIneq_holds`** at the flow point, `n = 3` (`σ = (+,-,+)`) and `n = 4` (`σ = (+,+,-,-)`): `∑_x |𝒦^{(n)}(σ, (a, x))| ≤
C L^τ (W^d η_t)⁻¹ (W^{-d} B_{t,0})^{n-2}`; the premises `KWardIneq_IndAt` at `k = 3, 4` are the only hypotheses. -/
example (hInd : ∀ k : ℕ, 3 ≤ k → k ≤ 4 → ∀ [NeZero k], KWardIneq_IndAt 3 k 10 P.m0.im) :
    (∃ C : ℝ, 0 < C ∧
      ∑ x : Zd 3 4, ‖BAKsol 3 4 2 (BAMsigma 3 4 (BAMB 3 4 P.g0 (P.E : ℂ) P.m0)) (PropSpin P.m0) (1 / 2)
          ⟨List.ofFn ![true, false, true], List.ofFn ![![0, 0, 0], ![1, 0, 0]] ++ [x]⟩‖
        ≤ C * (4 : ℝ) ^ (1 : ℝ) * (((2 : ℝ) ^ 3) * ((1 - 1 / 2) * P.m0.im))⁻¹ *
          (((2 : ℝ) ^ 3)⁻¹ * Bparam 3 4 P.g0 (1 / 2) 0) ^ (3 - 2)) ∧
    (∃ C : ℝ, 0 < C ∧
      ∑ x : Zd 3 4, ‖BAKsol 3 4 2 (BAMsigma 3 4 (BAMB 3 4 P.g0 (P.E : ℂ) P.m0)) (PropSpin P.m0) (1 / 2)
          ⟨List.ofFn ![true, true, false, false], List.ofFn ![![0, 0, 0], ![1, 0, 0], ![2, 1, 0]] ++ [x]⟩‖
        ≤ C * (4 : ℝ) ^ (1 : ℝ) * (((2 : ℝ) ^ 3) * ((1 - 1 / 2) * P.m0.im))⁻¹ *
          (((2 : ℝ) ^ 3)⁻¹ * Bparam 3 4 P.g0 (1 / 2) 0) ^ (4 - 2)) := by
  refine ⟨?_, ?_⟩
  · obtain ⟨C, hC, H⟩ := baWardIneq_holds 3 3 (Λ := 10) le_rfl (by norm_num) (by norm_num) P.real.1.1
      (fun k h1 h2 => hInd k h1 (by omega)) 1 one_pos
    exact ⟨C, hC, H 4 (by norm_num) 2 (by norm_num) P.g0 P.g0_pos P.g0_le P.E P.m0 P.real (1 / 2)
      (by norm_num) (by norm_num) ![true, false, true] ![![0, 0, 0], ![1, 0, 0]]⟩
  · obtain ⟨C, hC, H⟩ := baWardIneq_holds 3 4 (Λ := 10) le_rfl (by norm_num) (by norm_num) P.real.1.1
      (fun k h1 h2 => hInd k h1 h2) 1 one_pos
    exact ⟨C, hC, H 4 (by norm_num) 2 (by norm_num) P.g0 P.g0_pos P.g0_le P.E P.m0 P.real (1 / 2)
      (by norm_num) (by norm_num) ![true, true, false, false] ![![0, 0, 0], ![1, 0, 0], ![2, 1, 0]]⟩

/-- **`baWardKpi_empty_bound`** at the flow point, `n = 4` (`m = 3`): the layer `π = ∅` with the last label summed, `σ = (+,+,-,-)` (long last
leaf, the root sum `KWardIneq_IndAt` at `k = 4`) and `σ = (+,+,-,+)` (short last leaf, case (S): `ℓ¹ ≤ S` and `(eq:molecule-decay)`, proved). -/
example (hInd4 : KWardIneq_IndAt 3 4 10 P.m0.im) :
    ∃ C : ℝ, 0 < C ∧
      (∑ x : Zd 3 4, ‖BAKpi 3 4 4 (BAMsigma 3 4 (BAMB 3 4 P.g0 (P.E : ℂ) P.m0)) (1 / 2) ![true, true, false, false]
          (Function.update ![![0, 0, 0], ![1, 0, 0], ![2, 1, 0], ![3, 0, 0]] (Fin.last 3) x) ∅‖
        ≤ C * (4 : ℝ) ^ (1 : ℝ) * ((1 - 1 / 2) * P.m0.im)⁻¹ * (Bparam 3 4 P.g0 (1 / 2) 0) ^ (3 - 1)) ∧
      (∑ x : Zd 3 4, ‖BAKpi 3 4 4 (BAMsigma 3 4 (BAMB 3 4 P.g0 (P.E : ℂ) P.m0)) (1 / 2) ![true, true, false, true]
          (Function.update ![![0, 0, 0], ![1, 0, 0], ![2, 1, 0], ![3, 0, 0]] (Fin.last 3) x) ∅‖
        ≤ C * (4 : ℝ) ^ (1 : ℝ) * ((1 - 1 / 2) * P.m0.im)⁻¹ * (Bparam 3 4 P.g0 (1 / 2) 0) ^ (3 - 1)) := by
  obtain ⟨C, hC, H⟩ := baWardKpi_empty_bound 3 3 (Λ := 10) le_rfl (by norm_num) (by norm_num) P.real.1.1 hInd4 1 one_pos
  exact ⟨C, hC, H 4 (by norm_num) P.g0 P.g0_pos P.g0_le P.E P.m0 P.real (1 / 2) (by norm_num) (by norm_num) _ _,
    H 4 (by norm_num) P.g0 P.g0_pos P.g0_le P.E P.m0 P.real (1 / 2) (by norm_num) (by norm_num) _ _⟩

/-- **`baWardKpi_step`** at the flow point, `n = 4` (`m = 3`): the three layers `π = ∅`, `{(0,2)}`, `{(1,3)}` of `σ = (+,+,-,-)` (both chords are long;
a cut has `n_in = n_out = 3`).  The induction hypothesis at `m'' = 2` is the proved `baWardKpi_holds`; the premises `KWardIneq_IndAt` at `k = 3, 4`
are the only hypotheses. -/
example (hInd : ∀ k : ℕ, 3 ≤ k → k ≤ 4 → ∀ [NeZero k], KWardIneq_IndAt 3 k 10 P.m0.im) :
    ∃ C : ℝ, 0 < C ∧
      (∑ x : Zd 3 4, ‖BAKpi 3 4 4 (BAMsigma 3 4 (BAMB 3 4 P.g0 (P.E : ℂ) P.m0)) (1 / 2) ![true, true, false, false]
          (Function.update ![![0, 0, 0], ![1, 0, 0], ![2, 1, 0], ![3, 0, 0]] (Fin.last 3) x) ∅‖
        ≤ C * (4 : ℝ) ^ (1 : ℝ) * ((1 - 1 / 2) * P.m0.im)⁻¹ * (Bparam 3 4 P.g0 (1 / 2) 0) ^ (3 - 1)) ∧
      (∑ x : Zd 3 4, ‖BAKpi 3 4 4 (BAMsigma 3 4 (BAMB 3 4 P.g0 (P.E : ℂ) P.m0)) (1 / 2) ![true, true, false, false]
          (Function.update ![![0, 0, 0], ![1, 0, 0], ![2, 1, 0], ![3, 0, 0]] (Fin.last 3) x) {((0 : Fin 4), (2 : Fin 4))}‖
        ≤ C * (4 : ℝ) ^ (1 : ℝ) * ((1 - 1 / 2) * P.m0.im)⁻¹ * (Bparam 3 4 P.g0 (1 / 2) 0) ^ (3 - 1)) ∧
      (∑ x : Zd 3 4, ‖BAKpi 3 4 4 (BAMsigma 3 4 (BAMB 3 4 P.g0 (P.E : ℂ) P.m0)) (1 / 2) ![true, true, false, false]
          (Function.update ![![0, 0, 0], ![1, 0, 0], ![2, 1, 0], ![3, 0, 0]] (Fin.last 3) x) {((1 : Fin 4), (3 : Fin 4))}‖
        ≤ C * (4 : ℝ) ^ (1 : ℝ) * ((1 - 1 / 2) * P.m0.im)⁻¹ * (Bparam 3 4 P.g0 (1 / 2) 0) ^ (3 - 1)) := by
  obtain ⟨C, hC, H⟩ := baWardKpi_step 3 3 (Λ := 10) le_rfl (by norm_num) (by norm_num) P.real.1.1 hInd
    (fun m'' h2 hlt => baWardKpi_holds 3 m'' (Λ := 10) le_rfl h2 (by norm_num) P.real.1.1
      (fun k hk1 hk2 => hInd k hk1 (by omega))) 1 one_pos
  exact ⟨C, hC, H 4 (by norm_num) P.g0 P.g0_pos P.g0_le P.E P.m0 P.real (1 / 2) (by norm_num) (by norm_num) _ ∅ _,
    H 4 (by norm_num) P.g0 P.g0_pos P.g0_le P.E P.m0 P.real (1 / 2) (by norm_num) (by norm_num) _ _ _,
    H 4 (by norm_num) P.g0 P.g0_pos P.g0_le P.E P.m0 P.real (1 / 2) (by norm_num) (by norm_num) _ _ _⟩

/-- **`baWardKpi_holds`** at `m = 2` (`n = 3`, the triangle, `π = ∅` the only layer) and **`baWardIneq_of_Kpi`**: the layer form gives `BAWardIneqAt` at `n = 3` and
`n = 4`. -/
example (hInd : ∀ k : ℕ, 3 ≤ k → k ≤ 4 → ∀ [NeZero k], KWardIneq_IndAt 3 k 10 P.m0.im) :
    BAWardKpiAt 3 2 10 P.m0.im ∧ BAWardIneqAt 3 3 10 P.m0.im ∧ BAWardIneqAt 3 4 10 P.m0.im :=
  ⟨baWardKpi_holds 3 2 le_rfl le_rfl (by norm_num) P.real.1.1 (fun k hk1 hk2 => hInd k hk1 (by omega)),
    baWardIneq_of_Kpi 3 2 P.real.1.1 le_rfl
      (baWardKpi_holds 3 2 le_rfl le_rfl (by norm_num) P.real.1.1 (fun k hk1 hk2 => hInd k hk1 (by omega))),
    baWardIneq_of_Kpi 3 3 P.real.1.1 (by norm_num)
      (baWardKpi_holds 3 3 le_rfl (by norm_num) (by norm_num) P.real.1.1 hInd)⟩

/-- **`baWardMol_holds`** at the flow point (`k = 4`): `|Σ^{(∅)}(σ,δ)| ≤ C e^{-c max|δ_i - δ_j|}` with distinct labels (no hypothesis). -/
example : ∃ C : ℝ, 0 < C ∧ ∃ c : ℝ, 0 < c ∧
    ‖BASigmaPi 3 4 4 (BAMsigma 3 4 (BAMB 3 4 P.g0 (P.E : ℂ) P.m0)) (1 / 2) ![true, true, false, true] ∅
        ![![0, 0, 0], ![1, 0, 0], ![2, 1, 0], ![3, 0, 0]]‖
      ≤ C * Real.exp (-(c * (KLmaxDist 3 4 ![![0, 0, 0], ![1, 0, 0], ![2, 1, 0], ![3, 0, 0]] : ℝ))) := by
  obtain ⟨C, hC, c, hc, H⟩ := baWardMol_holds (d := 3) (k := 4) le_rfl (by norm_num) (Λ := 10) (by norm_num) P.real.1.1
  exact ⟨C, hC, c, hc, H 4 (by norm_num) P.g0 P.g0_pos P.g0_le P.E P.m0 P.real (1 / 2) (by norm_num) (by norm_num) _ _⟩

/-- **`KWardIneq_IndAt_of_abs`** at the flow point's family: the abstract `IndStepAbs` (the output of `indStepAbs_of`, K09b) at the inner sizes `3` and `4` gives the
premises of `baWardIneq_holds`, hence the bound of `(wardineq_K)` at `n = 4` and `σ = (+,+,-,-)` at the flow point.  `IndStepAbs` is the only hypothesis. -/
example (h3 : IndStepAbs (ι := KWardIneq_Data 3 10 P.m0.im) 3 3 (fun i => i.L) (fun i => Bparam 3 i.L i.g i.t 0)
      (BASig (ι := KWardIneq_Data 3 10 P.m0.im) 3 3 (fun i => i.L) (fun i => i.g) (fun i => i.E) (fun i => i.m) (fun i => i.t))
      (fun i s s' => BAThetaOf (BAMsigma 3 i.L (BAMB 3 i.L i.g (i.E : ℂ) i.m)) i.t s s'))
    (h4 : IndStepAbs (ι := KWardIneq_Data 3 10 P.m0.im) 3 4 (fun i => i.L) (fun i => Bparam 3 i.L i.g i.t 0)
      (BASig (ι := KWardIneq_Data 3 10 P.m0.im) 3 4 (fun i => i.L) (fun i => i.g) (fun i => i.E) (fun i => i.m) (fun i => i.t))
      (fun i s s' => BAThetaOf (BAMsigma 3 i.L (BAMB 3 i.L i.g (i.E : ℂ) i.m)) i.t s s')) :
    ∃ C : ℝ, 0 < C ∧
      ∑ x : Zd 3 4, ‖BAKsol 3 4 2 (BAMsigma 3 4 (BAMB 3 4 P.g0 (P.E : ℂ) P.m0)) (PropSpin P.m0) (1 / 2)
          ⟨List.ofFn ![true, true, false, false], List.ofFn ![![0, 0, 0], ![1, 0, 0], ![2, 1, 0]] ++ [x]⟩‖
        ≤ C * (4 : ℝ) ^ (1 : ℝ) * (((2 : ℝ) ^ 3) * ((1 - 1 / 2) * P.m0.im))⁻¹ *
          (((2 : ℝ) ^ 3)⁻¹ * Bparam 3 4 P.g0 (1 / 2) 0) ^ (4 - 2) := by
  have hInd : ∀ k : ℕ, 3 ≤ k → k ≤ 4 → ∀ [NeZero k], KWardIneq_IndAt 3 k 10 P.m0.im := by
    intro k hk1 hk2 _
    obtain rfl | rfl : k = 3 ∨ k = 4 := by omega
    · exact KWardIneq_IndAt_of_abs h3
    · exact KWardIneq_IndAt_of_abs h4
  obtain ⟨C, hC, H⟩ := baWardIneq_holds 3 4 (Λ := 10) le_rfl (by norm_num) (by norm_num) P.real.1.1 hInd 1 one_pos
  exact ⟨C, hC, H 4 (by norm_num) 2 (by norm_num) P.g0 P.g0_pos P.g0_le P.E P.m0 P.real (1 / 2)
    (by norm_num) (by norm_num) ![true, true, false, false] ![![0, 0, 0], ![1, 0, 0], ![2, 1, 0]]⟩

/-- **Nondegeneracy of the instances above**: for `σ = (+,+,-,-)` the last leaf is long (`σ_3 ≠ σ_0`, the case (L)) and both chords `(0,2)`, `(1,3)` are
long, so the layers `{(0,2)}` and `{(1,3)}` are nonempty sums of cactus values (the step is the cut, not the vacuous branch `KLTSPlong = ∅`); for
`σ = (+,+,-,+)` the last leaf is short (`σ_3 = σ_0`, the case (S)). -/
example : (![true, true, false, false] : Fin 4 → Bool) (Fin.last 3) ≠ (![true, true, false, false] : Fin 4 → Bool) (Fin.last 3 + 1) ∧
    (![true, true, false, true] : Fin 4 → Bool) (Fin.last 3) = (![true, true, false, true] : Fin 4 → Bool) (Fin.last 3 + 1) ∧
    (KLTSPlong 4 ![true, true, false, false] {((0 : Fin 4), (2 : Fin 4))}).Nonempty ∧
    (KLTSPlong 4 ![true, true, false, false] {((1 : Fin 4), (3 : Fin 4))}).Nonempty :=
  ⟨by decide, by decide, ⟨{((0 : Fin 4), (2 : Fin 4))}, by decide⟩, ⟨{((1 : Fin 4), (3 : Fin 4))}, by decide⟩⟩

end KWardIneqInst

end RBM.BA
