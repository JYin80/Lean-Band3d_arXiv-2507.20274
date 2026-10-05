/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Main.ZTransfer
import RBM3D.Green.LDE

/-!
# MA-03: the fixed-`z` statements and `decol` from `locSC` (Theorems 2.1-2.5, assembly)

Ticket T2225 (MA-03 of the T2192 assembly split).  Moved verbatim from the compiled probe
`RBM3D/Probe/T2192Pins.lean` at `97d958e` (branch `t/T2192`, never merged); the probe
namespace `RBM.Probe.T2192` becomes `RBM.Endpoints`, its `Inst` becomes `RBM.Endpoints.Inst`.

Paper: arXiv:2507.20274, `paper/tex/1_2_Intro_model_result.tex` (cited `1_2:line`).

* The fixed-`z` statements `(G_bound)`, `(G_bound_ave)` (`1_2:388-391`) and `(eq:diffu1,2)`,
  `(Meq:QdS1,2)` (`1_2:490-509`) "at each fixed `z`" (`1_2:1228`), from `UNMLOut` at
  `t₀ = lemT z` through the transfer of MA-02: `locSCFixed`, `QDiffFixed`, `MAFixed`
  (proofs `locSCFixed_of_ML`, `QDiffFixed_of_ML`, `fixed_of_ML`); `N₀` uniform over `𝐃_{κ,ε}`
  (D500), `a, b` inside the probability (D503).
* `decol` (`1_2:357-370`) from `locSC` by `(eq:ukx)` (`1_2:399`) with
  `η = N^{-1+min(τ/2,1/2)}` (D502), no net: `MADecol`, `decol_of_locSC`.
* The six domain lemmas of the probe's `section Fixed` are MA-01's (`RBM3D/Endpoints.lean:472-507`).
* Consumers: MA-04 (`Main/ZNet`: `MANetLoc`, `MANetQD`), MA-06.  Registry: one line,
  `locBad1` (structural, hypothesis of `decol_core`).
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Matrix Topology
open RBM RBM.Gauss RBM.Gauss.Sizes RBM.Univ
open scoped NNReal ENNReal

namespace RBM.Endpoints

/-! ### (c) The fixed-`z` statements with `N₀` uniform over `𝐃_{κ,ε}`, from `UNMLOut` by the sections lemma -/

section Fixed

variable {d : ℕ}

/-- **`locSCFixed`: `(G_bound)`, `(G_bound_ave)` for every single `z ∈ 𝐃_{κ,ε}`, eventually uniformly** (RBM2D's
pointwise `locSC`, `RBM2D/Endpoints.lean:99`; the paper's "at each fixed `z`", `1_2:1228`): the union over `x, y` (resp. `a`)
is inside the probability, `z` is outside.  It is what `UNMLOut` gives through the sections lemma. -/
def locSCFixed : Prop :=
  ∀ d : ℕ, 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 →
    ∀ κ ε τ D : ℝ, 0 < κ → 0 < ε → 0 < τ → 0 < D → ∀ᶠ n in atTop, ∀ z : ℂ, sz.locDomain κ ε n z →
      Sizes.seqP sz {ω | locBad1z sz τ n z ω} ≤ ENNReal.ofReal (Nsz sz n ^ (-D)) ∧
      Sizes.seqP sz {ω | locBad2z sz τ n z ω} ≤ ENNReal.ofReal (Nsz sz n ^ (-D))

/-- **`QDiffFixed`: `(eq:diffu1)`, `(eq:diffu2)` for every single `z`** (blocks `a, b` inside), and
`(Meq:QdS1)`, `(Meq:QdS2)` (already pointwise in `z`), `N₀` uniform over `𝐃_{κ,ε}`. -/
def QDiffFixed : Prop :=
  ∀ d : ℕ, 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 →
    ∀ κ ε τ D : ℝ, 0 < κ → 0 < ε → 0 < τ → 0 < D → ∀ᶠ n in atTop, ∀ z : ℂ, sz.locDomain κ ε n z →
      (Sizes.seqP sz {ω | qd1Badz sz τ n z ω} ≤ ENNReal.ofReal (Nsz sz n ^ (-D)) ∧
       Sizes.seqP sz {ω | qd2Badz sz τ n z ω} ≤ ENNReal.ofReal (Nsz sz n ^ (-D))) ∧
      ∀ a b : Zd d (sz.L n),
        ‖(∫ ω, avg2 sz n (fun x y => ((‖sz.Gn n z ω x y‖ ^ 2 : ℝ) : ℂ)) a b ∂(Sizes.seqP sz)) -
            profPM sz n z a b‖ ≤ qdBoundExp sz n τ z.im ∧
        ‖(∫ ω, avg2 sz n (fun x y => sz.Gn n z ω x y * sz.Gn n z ω y x) a b ∂(Sizes.seqP sz)) -
            profPP sz n z a b‖ ≤ qdBoundExp sz n τ z.im

/-- **`MAFixed`** (RBM2D `locSC_of_pins`, `QDiff_of_pins`, `RBM2D/Main/EndpointsFromSTO.lean`, `locSC_of_pins` `:518`,
`QDiff_of_pins` `:565`): the fixed-`z` statements from the flow outputs `UNMLOut`.  Proved below (`fixed_of_ML`, from
`locSCFixed_of_ML` and `QDiffFixed_of_ML`); owed by MA-03 as a port of this file. -/
def MAFixed : Prop := (∀ d : ℕ, UNMLOut d) → locSCFixed ∧ QDiffFixed

end Fixed

section FixedProof

variable {d : ℕ}

theorem Bctl_nonneg (sz : Sizes d) (n : ℕ) (t : ℝ) : 0 ≤ sz.Bctl n t := by
  unfold Sizes.Bctl Bparam
  positivity

open RBM.Loop in
/-- `STKloop` at `k = 1` is `m(E)` (`(Kn1sol)`, `KLK_one`). -/
theorem STKloop_one (sz : Sizes d) (n : ℕ) (E t : ℝ) (a : Zd d (sz.L n)) :
    sz.STKloop n E t (fun _ : Fin 1 => true) (fun _ => a) = mE E := by
  have hI : (KLloopOf d (sz.L n) (fun _ : Fin 1 => true) (fun _ : Fin 1 => a)) =
      (⟨[true], [a]⟩ : LoopIdx (Zd d (sz.L n))) := by simp [KLloopOf]
  unfold Sizes.STKloop
  rw [hI, KLK_one]
  simp [mSigma]

open RBM.Loop in
/-- **The fixed-`z` statements of `locSC` from `UNMLOut`** (the proof plan of MA-03, compiled here for
`(G_bound)` and `(G_bound_ave)`): sections lemma, `UNMLOut` at the time sequence `t_n = lemT z_n`
(`0 ≤ t_n ≤ lemT z_n`, `STFlow`), the transfer `zLocal`/`zAve`, the constants of `btBt`, the form bridge
`explicit_of_prec` at `τ/2`, and `2 ≤ W^{τ/2}` eventually. -/
theorem locSCFixed_of_ML (hML : ∀ d, UNMLOut d) : locSCFixed := by
  intro d hd 𝔠 𝔡 sz hA κ ε τ D hκ hε hτ hD
  have hA' := hA
  obtain ⟨h𝔠, h𝔡, hsz, hbw, hWO⟩ := hA'
  by_cases hκ2 : κ ≤ 2
  swap
  · exact Filter.Eventually.of_forall fun n z hz => absurd hz (locDomain_empty_kappa sz (not_le.mp hκ2) n z)
  by_cases hε1 : ε ≤ 1
  swap
  · filter_upwards [hsz.eventually_gt_atTop 1] with n hn z hz
    exact absurd hz (locDomain_empty_eps sz (not_le.mp hε1) hn z)
  have hne : ∀ n, Nonempty {z : ℂ // sz.locDomain κ ε n z} := fun n =>
    (locDomain_nonempty sz hκ2 hε1 n).elim fun z hz => ⟨⟨z, hz⟩⟩
  refine (eventually_forall_of_sections hne (Q := fun n z =>
      Sizes.seqP sz {ω | locBad1z sz τ n z.1 ω} ≤ ENNReal.ofReal (Nsz sz n ^ (-D)) ∧
      Sizes.seqP sz {ω | locBad2z sz τ n z.1 ω} ≤ ENNReal.ofReal (Nsz sz n ^ (-D))) ?_).mono
    fun n hn z hz => hn ⟨z, hz⟩
  intro s
  set z : ℕ → ℂ := fun n => (s n).1 with hzdef
  have hzim : ∀ n, 0 < (z n).im := fun n => locDomain_im_pos (s n).2
  have hflow : STFlow sz κ ε 𝔠 𝔡 z := ⟨hA, fun n => (s n).2⟩
  obtain ⟨hLK, -, -, -, hLoc⟩ := hML d hd κ ε 𝔡 𝔠 hκ hε h𝔡 sz z hflow (fun n => lemT (z n))
    (fun n => (lemT_pos (hzim n)).le) (fun n => le_rfl)
  have hτ2 : 0 < τ / 2 := half_pos hτ
  have hζ1 : ∀ (n : ℕ) (u : Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n)) (ω : sz.SeqΩ),
      0 ≤ STWB sz n (lemT (z n)) (zdistInf d (sz.L n) (STblk sz n u.1 - STblk sz n u.2)) :=
    fun n u ω => STWB_nonneg sz n _ _
  have hζ2 : ∀ (n : ℕ) (u : (Fin 1 → Bool) × (Fin 1 → Zd d (sz.L n))) (ω : sz.SeqΩ),
      0 ≤ (sz.Bctl n (lemT (z n))) ^ 1 := fun n u ω => pow_nonneg (Bctl_nonneg sz n _) 1
  have hE1 := explicit_of_prec sz h𝔠 hζ1 hbw hLoc hτ2 hD
  have hE2 := explicit_of_prec sz h𝔠 hζ2 hbw (hLK 1 le_rfl) hτ2 hD
  have hW2 : ∀ᶠ n in atTop, (2 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) ^ (τ / 2) :=
    ((tendsto_rpow_atTop hτ2).comp (RBM.Green.tendsto_W sz h𝔠 hsz hbw)).eventually_ge_atTop 2
  filter_upwards [hE1, hE2, hW2] with n hn1 hn2 hn3
  have hWpos : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hWτ : ((sz.W n : ℕ) : ℝ) ^ τ = ((sz.W n : ℕ) : ℝ) ^ (τ / 2) * ((sz.W n : ℕ) : ℝ) ^ (τ / 2) := by
    rw [← Real.rpow_add hWpos]; congr 1; ring
  have hWh : 0 ≤ ((sz.W n : ℕ) : ℝ) ^ (τ / 2) := Real.rpow_nonneg hWpos.le _
  have hz1 : (z n).im ≤ 1 := (s n).2.2.2
  have hre : |(z n).re| ≤ 2 - κ := (s n).2.1
  have ht1 : lemT (z n) < 1 := lemT_lt_one (hzim n)
  refine ⟨le_trans (measure_mono ?_) hn1, le_trans (measure_mono ?_) hn2⟩
  · rintro ω ⟨x, y, hxy⟩
    refine ⟨(x, y), ?_⟩
    simp only
    set k := zdistInf d (sz.L n) (STblk sz n x - STblk sz n y) with hk
    obtain ⟨hb1, -⟩ := btBt hd sz n κ hκ (z n) (hzim n) hz1 hre k
    have hcB : 0 ≤ calB sz n (z n).im (((sz.W n : ℕ) : ℝ) * (k : ℝ)) :=
      calB_nonneg sz n (hzim n) (by positivity)
    have hloc := zLocal sz n (z n) (hzim n) ω x y
    have hSTGM : ‖STGM sz n (STflowE z n) (lemT (z n)) ω x y‖ ^ 2 =
        ‖STGM sz n (lemE (z n)) (lemT (z n)) ω x y‖ ^ 2 := rfl
    have hle : lemT (z n) * ‖STGM sz n (lemE (z n)) (lemT (z n)) ω x y‖ ^ 2 ≤
        ‖STGM sz n (lemE (z n)) (lemT (z n)) ω x y‖ ^ 2 :=
      mul_le_of_le_one_left (sq_nonneg _) ht1.le
    have hxy' : ((sz.W n : ℕ) : ℝ) ^ τ * calB sz n (z n).im (((sz.W n : ℕ) : ℝ) * (k : ℝ)) <
        ‖sz.Gn n (z n) ω x y - Mband sz n (z n) x y‖ ^ 2 := hxy
    rw [hSTGM]
    calc ((sz.W n : ℕ) : ℝ) ^ (τ / 2) * STWB sz n (lemT (z n)) k
        ≤ ((sz.W n : ℕ) : ℝ) ^ (τ / 2) * (2 * calB sz n (z n).im (((sz.W n : ℕ) : ℝ) * (k : ℝ))) :=
          mul_le_mul_of_nonneg_left hb1 hWh
      _ = (((sz.W n : ℕ) : ℝ) ^ (τ / 2) * 2) * calB sz n (z n).im (((sz.W n : ℕ) : ℝ) * (k : ℝ)) := by ring
      _ ≤ (((sz.W n : ℕ) : ℝ) ^ (τ / 2) * ((sz.W n : ℕ) : ℝ) ^ (τ / 2)) *
            calB sz n (z n).im (((sz.W n : ℕ) : ℝ) * (k : ℝ)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hn3 hWh) hcB
      _ = ((sz.W n : ℕ) : ℝ) ^ τ * calB sz n (z n).im (((sz.W n : ℕ) : ℝ) * (k : ℝ)) := by rw [hWτ]
      _ < ‖sz.Gn n (z n) ω x y - Mband sz n (z n) x y‖ ^ 2 := hxy'
      _ = lemT (z n) * ‖STGM sz n (lemE (z n)) (lemT (z n)) ω x y‖ ^ 2 := hloc
      _ ≤ ‖STGM sz n (lemE (z n)) (lemT (z n)) ω x y‖ ^ 2 := hle
  · rintro ω ⟨a, ha⟩
    refine ⟨(fun _ => true, fun _ => a), ?_⟩
    simp only
    obtain ⟨hb1, -⟩ := btBt hd sz n κ hκ (z n) (hzim n) hz1 hre 0
    have hb1' : sz.Bctl n (lemT (z n)) ≤ 2 * calB sz n (z n).im 0 := by
      have h := hb1
      simp only [Nat.cast_zero, mul_zero] at h
      exact h
    have hcB : 0 ≤ calB sz n (z n).im 0 := calB_nonneg sz n (hzim n) le_rfl
    have hav := zAve sz n (z n) (hzim n) ω a
    have hmsc := msc_eq_sqrt_mul_mE (hzim n)
    have hdiff : (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * ∑ x ∈ Iblk d (sz.L n) (sz.W n) a, sz.Gn n (z n) ω x x - msc (z n) =
        (Real.sqrt (lemT (z n)) : ℂ) *
          (sz.Lloop n (lemE (z n)) (lemT (z n)) (fun _ : Fin 1 => true) (fun _ => a) ω - mE (lemE (z n))) := by
      rw [hav]; conv_lhs => rw [hmsc]
      ring
    have hnorm : ‖(((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * ∑ x ∈ Iblk d (sz.L n) (sz.W n) a, sz.Gn n (z n) ω x x - msc (z n)‖ ≤
        ‖sz.Lloop n (lemE (z n)) (lemT (z n)) (fun _ : Fin 1 => true) (fun _ => a) ω - mE (lemE (z n))‖ := by
      rw [hdiff, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
      exact mul_le_of_le_one_left (norm_nonneg _) (Real.sqrt_le_one.2 ht1.le)
    have hK := STKloop_one sz n (lemE (z n)) (lemT (z n)) a
    have hBct : sz.Bctl n (lemT (z n)) ^ 1 = sz.Bctl n (lemT (z n)) := pow_one _
    change ((sz.W n : ℕ) : ℝ) ^ (τ / 2) * (sz.Bctl n (lemT (z n))) ^ 1 <
      ‖sz.Lloop n (STflowE z n) (lemT (z n)) (fun _ : Fin 1 => true) (fun _ => a) ω -
        sz.STKloop n (STflowE z n) (lemT (z n)) (fun _ : Fin 1 => true) (fun _ => a)‖
    have hK' : sz.STKloop n (STflowE z n) (lemT (z n)) (fun _ : Fin 1 => true) (fun _ => a) =
        mE (lemE (z n)) := hK
    rw [hK', hBct]
    calc ((sz.W n : ℕ) : ℝ) ^ (τ / 2) * sz.Bctl n (lemT (z n))
        ≤ ((sz.W n : ℕ) : ℝ) ^ (τ / 2) * (2 * calB sz n (z n).im 0) :=
          mul_le_mul_of_nonneg_left hb1' hWh
      _ = (((sz.W n : ℕ) : ℝ) ^ (τ / 2) * 2) * calB sz n (z n).im 0 := by ring
      _ ≤ (((sz.W n : ℕ) : ℝ) ^ (τ / 2) * ((sz.W n : ℕ) : ℝ) ^ (τ / 2)) * calB sz n (z n).im 0 :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hn3 hWh) hcB
      _ = ((sz.W n : ℕ) : ℝ) ^ τ * calB sz n (z n).im 0 := by rw [hWτ]
      _ < ‖(((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * ∑ x ∈ Iblk d (sz.L n) (sz.W n) a, sz.Gn n (z n) ω x x - msc (z n)‖ := ha
      _ ≤ ‖sz.Lloop n (lemE (z n)) (lemT (z n)) (fun _ : Fin 1 => true) (fun _ => a) ω - mE (lemE (z n))‖ := hnorm

end FixedProof

/-! ### (c) The fixed-`z` statements of `QDiff` from `UNMLOut` (compiled): the deterministic comparisons, the union bound, the proof -/

section QDFixed

variable {d : ℕ}

/-- The periodic `L^∞` norm is even (the merged copies are `private`). -/
theorem zdistInf_neg' (d L : ℕ) [NeZero L] (x : Zd d L) : zdistInf d L (-x) = zdistInf d L x := by
  unfold zdistInf
  exact Finset.sup_congr rfl fun i _ => by simp [zdist_neg]

/-- The floor that absorbs the additive `W^{-D}` of `(Eq:Gdecay)` (preflight row 5): for `0 < η ≤ 1`, `K ≥ 0`,
`W^{-6/(5𝔠)} ≤ 𝓑_{η,0}^{1/5} 𝓑_{η,K}` (`𝓑 ≥ (Nη)⁻¹ ≥ N⁻¹ ≥ W^{-1/𝔠}`). -/
theorem floor_X (sz : Sizes d) (n : ℕ) (hd : 2 ≤ d) {𝔠 η K : ℝ} (h𝔠 : 0 < 𝔠)
    (hb : ((sz.size n : ℕ) : ℝ) ^ 𝔠 ≤ (sz.W n : ℝ)) (hη : 0 < η) (hη1 : η ≤ 1) (hK : 0 ≤ K) :
    ((sz.W n : ℕ) : ℝ) ^ (-(6 / (5 * 𝔠))) ≤ calB sz n η 0 ^ ((1 : ℝ) / 5) * calB sz n η K := by
  have hW0 : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hNpos : (0 : ℝ) < Nsz sz n := Nsz_pos sz n
  have hN1 : (1 : ℝ) ≤ Nsz sz n := by exact_mod_cast one_le_size sz n
  -- `N ≤ W^{1/𝔠}`
  have hNW : Nsz sz n ≤ ((sz.W n : ℕ) : ℝ) ^ (1 / 𝔠) := by
    have h := Sizes.size_rpow_le_W_rpow sz h𝔠 n hb (τ := 1) zero_le_one
    simpa [Nsz] using h
  have hu : ((sz.W n : ℕ) : ℝ) ^ (-(1 / 𝔠)) ≤ (Nsz sz n)⁻¹ := by
    rw [Real.rpow_neg hW0.le]
    exact inv_anti₀ hNpos hNW
  have hfl : ∀ K' : ℝ, 0 ≤ K' → ((sz.W n : ℕ) : ℝ) ^ (-(1 / 𝔠)) ≤ calB sz n η K' := by
    intro K' hK'
    refine hu.trans (le_trans ?_ (inv_size_mul_le_calB sz n hd hη hK'))
    apply inv_anti₀ (by positivity)
    have : Nsz sz n * η ≤ Nsz sz n * 1 := mul_le_mul_of_nonneg_left hη1 hNpos.le
    simpa [Nsz] using this
  have hA := hfl 0 le_rfl
  have hB := hfl K hK
  set u := ((sz.W n : ℕ) : ℝ) ^ (-(1 / 𝔠)) with hudef
  have hu0 : 0 < u := Real.rpow_pos_of_pos hW0 _
  have h15 : u ^ ((1 : ℝ) / 5) ≤ calB sz n η 0 ^ ((1 : ℝ) / 5) :=
    Real.rpow_le_rpow hu0.le hA (by norm_num)
  have hprod : u ^ ((1 : ℝ) / 5) * u ≤ calB sz n η 0 ^ ((1 : ℝ) / 5) * calB sz n η K :=
    mul_le_mul h15 hB hu0.le (Real.rpow_nonneg (le_trans hu0.le hA) _)
  refine le_trans (le_of_eq ?_) hprod
  rw [hudef, ← Real.rpow_mul hW0.le, ← Real.rpow_add hW0]
  congr 1
  field_simp
  ring

/-- **The deterministic comparison of the probability halves of `QDiffFixed`**: if `Δ = ‖𝓛^{(2)} - 𝒦^{(2)}‖` satisfies the two
bounds of `(Eq:Gdecay)` (with the additive `W^{-6/(5𝔠)}`) and of `(Eq:L-KGt)` at `k = 2`, both at the scale `W^{τ/2}`, at
`t₀ = lemT z`, then `t₀ Δ ≤ W^τ [𝓑_{η,0}^{1/5} 𝓑_{η,W|a-b|} ∧ 𝓑_{η,0}²]`: `(eq:BtBt)` (`btBt`, constants `2`), the floor
`floor_X`, and `min (2 a X, a Y) ≤ 2 a min (X, Y)`. -/
theorem qd_core (sz : Sizes d) (n : ℕ) (hd : 3 ≤ d) {𝔠 κ τ e Δ : ℝ} (h𝔠 : 0 < 𝔠) (hκ : 0 < κ)
    (hb : ((sz.size n : ℕ) : ℝ) ^ 𝔠 ≤ (sz.W n : ℝ)) {z : ℂ} (hz : 0 < z.im) (hz1 : z.im ≤ 1)
    (hre : |z.re| ≤ 2 - κ) (hW : 5 ≤ ((sz.W n : ℕ) : ℝ) ^ (τ / 2)) (a b : Zd d (sz.L n))
    (hΔ : 0 ≤ Δ) (he0 : 0 ≤ e) (he1 : e ≤ 1)
    (h1 : Δ ≤ ((sz.W n : ℕ) : ℝ) ^ (τ / 2) *
      (sz.Bctl n (lemT z) ^ ((1 : ℝ) / 5) * STWB sz n (lemT z) (zdistInf d (sz.L n) (b - a)) * e +
        ((sz.W n : ℕ) : ℝ) ^ (-(6 / (5 * 𝔠)))))
    (h2 : Δ ≤ ((sz.W n : ℕ) : ℝ) ^ (τ / 2) * sz.Bctl n (lemT z) ^ 2) :
    lemT z * Δ ≤ qdBound sz n τ z.im a b := by
  have hd2 : 2 ≤ d := by omega
  have hW0 : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  set w := ((sz.W n : ℕ) : ℝ) ^ (τ / 2) with hw
  have hwpos : 0 < w := by linarith
  set B0 := calB sz n z.im 0 with hB0
  have hB0n : 0 ≤ B0 := calB_nonneg sz n hz le_rfl
  set k := zdistInf d (sz.L n) (b - a) with hk
  have hkab : zdistInf d (sz.L n) (b - a) = zdistInf d (sz.L n) (a - b) := by
    rw [← neg_sub a b, zdistInf_neg']
  have hdist : distB sz n a b = ((sz.W n : ℕ) : ℝ) * (k : ℝ) := by
    unfold distB
    rw [hk, hkab]
  have hdist0 : 0 ≤ distB sz n a b := by unfold distB; positivity
  set Bk := calB sz n z.im (distB sz n a b) with hBkdef
  have hBk : 0 ≤ Bk := calB_nonneg sz n hz hdist0
  have hbt := btBt hd sz n κ hκ z hz hz1 hre k
  have hbt0 := (btBt hd sz n κ hκ z hz hz1 hre 0).1
  have hSB0 : sz.Bctl n (lemT z) ≤ 2 * B0 := by
    have h := hbt0
    simp only [Nat.cast_zero, mul_zero] at h
    exact h
  have hSBk : STWB sz n (lemT z) k ≤ 2 * Bk := by
    rw [hBkdef, hdist]; exact hbt.1
  have hfl := floor_X sz n hd2 h𝔠 hb hz hz1 hdist0
  have hBc : 0 ≤ sz.Bctl n (lemT z) := Bctl_nonneg sz n _
  have hSTn : 0 ≤ STWB sz n (lemT z) k := STWB_nonneg sz n _ _
  have hBc15 : sz.Bctl n (lemT z) ^ ((1 : ℝ) / 5) ≤ 2 * B0 ^ ((1 : ℝ) / 5) := by
    calc sz.Bctl n (lemT z) ^ ((1 : ℝ) / 5) ≤ (2 * B0) ^ ((1 : ℝ) / 5) :=
          Real.rpow_le_rpow hBc hSB0 (by norm_num)
      _ = (2 : ℝ) ^ ((1 : ℝ) / 5) * B0 ^ ((1 : ℝ) / 5) := Real.mul_rpow (by norm_num) hB0n
      _ ≤ 2 * B0 ^ ((1 : ℝ) / 5) := by
          have h2' : (2 : ℝ) ^ ((1 : ℝ) / 5) ≤ 2 := by
            calc (2 : ℝ) ^ ((1 : ℝ) / 5) ≤ (2 : ℝ) ^ (1 : ℝ) :=
                  Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
              _ = 2 := Real.rpow_one 2
          exact mul_le_mul_of_nonneg_right h2' (Real.rpow_nonneg hB0n _)
  set X := B0 ^ ((1 : ℝ) / 5) * Bk with hX
  have hX0 : 0 ≤ X := mul_nonneg (Real.rpow_nonneg hB0n _) hBk
  have hterm : sz.Bctl n (lemT z) ^ ((1 : ℝ) / 5) * STWB sz n (lemT z) k * e ≤ 4 * X := by
    calc sz.Bctl n (lemT z) ^ ((1 : ℝ) / 5) * STWB sz n (lemT z) k * e
        ≤ sz.Bctl n (lemT z) ^ ((1 : ℝ) / 5) * STWB sz n (lemT z) k * 1 :=
          mul_le_mul_of_nonneg_left he1 (mul_nonneg (Real.rpow_nonneg hBc _) hSTn)
      _ = sz.Bctl n (lemT z) ^ ((1 : ℝ) / 5) * STWB sz n (lemT z) k := mul_one _
      _ ≤ (2 * B0 ^ ((1 : ℝ) / 5)) * (2 * Bk) :=
          mul_le_mul hBc15 hSBk hSTn (by positivity)
      _ = 4 * X := by rw [hX]; ring
  have h1' : Δ ≤ w * (5 * X) := by
    calc Δ ≤ w * (sz.Bctl n (lemT z) ^ ((1 : ℝ) / 5) * STWB sz n (lemT z) k * e +
          ((sz.W n : ℕ) : ℝ) ^ (-(6 / (5 * 𝔠)))) := h1
      _ ≤ w * (4 * X + X) := mul_le_mul_of_nonneg_left (add_le_add hterm hfl) hwpos.le
      _ = w * (5 * X) := by ring
  have hY : sz.Bctl n (lemT z) ^ 2 ≤ 4 * B0 ^ 2 := by
    have := pow_le_pow_left₀ hBc hSB0 2
    calc sz.Bctl n (lemT z) ^ 2 ≤ (2 * B0) ^ 2 := this
      _ = 4 * B0 ^ 2 := by ring
  have h2' : Δ ≤ w * (4 * B0 ^ 2) := h2.trans (mul_le_mul_of_nonneg_left hY hwpos.le)
  have hmin : Δ ≤ w * (5 * min X (B0 ^ 2)) := by
    rcases le_total X (B0 ^ 2) with h | h
    · rw [min_eq_left h]; exact h1'
    · rw [min_eq_right h]
      refine h2'.trans (mul_le_mul_of_nonneg_left ?_ hwpos.le)
      nlinarith [sq_nonneg B0]
  have hm0 : 0 ≤ min X (B0 ^ 2) := le_min hX0 (sq_nonneg _)
  have hWτ : ((sz.W n : ℕ) : ℝ) ^ τ = w * w := by
    rw [hw, ← Real.rpow_add hW0]; congr 1; ring
  have ht1 : lemT z ≤ 1 := (lemT_lt_one hz).le
  calc lemT z * Δ ≤ Δ := mul_le_of_le_one_left hΔ ht1
    _ ≤ w * (5 * min X (B0 ^ 2)) := hmin
    _ ≤ w * (w * min X (B0 ^ 2)) := by
        apply mul_le_mul_of_nonneg_left _ hwpos.le
        exact mul_le_mul_of_nonneg_right hW hm0
    _ = ((sz.W n : ℕ) : ℝ) ^ τ * min X (B0 ^ 2) := by rw [hWτ]; ring
    _ = qdBound sz n τ z.im a b := by
        unfold qdBound
        rfl

/-- The union bound of the two events of the probability halves, in an abstract form (any law, any index type). -/
theorem prob_union_le {Ω U : Type*} [MeasurableSpace Ω] (P : Measure Ω) (w : ℝ) {ξ ζ₁ ζ₂ : U → Ω → ℝ} {Bad : Set Ω}
    {δ : ENNReal} (h1 : P {ω | ∃ u, w * ζ₁ u ω < ξ u ω} ≤ δ) (h2 : P {ω | ∃ u, w * ζ₂ u ω < ξ u ω} ≤ δ)
    (hsub : ∀ ω, (∀ u, ξ u ω ≤ w * ζ₁ u ω) → (∀ u, ξ u ω ≤ w * ζ₂ u ω) → ω ∉ Bad) : P Bad ≤ δ + δ := by
  have hsubset : Bad ⊆ {ω | ∃ u, w * ζ₁ u ω < ξ u ω} ∪ {ω | ∃ u, w * ζ₂ u ω < ξ u ω} := by
    intro ω hω
    by_contra hcon
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_exists, not_lt] at hcon
    exact hsub ω hcon.1 hcon.2 hω
  calc P Bad ≤ P ({ω | ∃ u, w * ζ₁ u ω < ξ u ω} ∪ {ω | ∃ u, w * ζ₂ u ω < ξ u ω}) := measure_mono hsubset
    _ ≤ P {ω | ∃ u, w * ζ₁ u ω < ξ u ω} + P {ω | ∃ u, w * ζ₂ u ω < ξ u ω} := measure_union_le _ _
    _ ≤ δ + δ := add_le_add h1 h2

/-- `2 N^{-(D+1)} ≤ N^{-D}` for `N ≥ 2`: two events of probability `N^{-(D+1)}` have a union of probability `≤ N^{-D}`. -/
theorem two_rpow_le {N D : ℝ} (hN : 2 ≤ N) :
    ENNReal.ofReal (N ^ (-(D + 1))) + ENNReal.ofReal (N ^ (-(D + 1))) ≤ ENNReal.ofReal (N ^ (-D)) := by
  have hN0 : 0 < N := by linarith
  have h2 : 0 < N ^ (-D) := Real.rpow_pos_of_pos hN0 _
  have h1 : N ^ (-(D + 1)) = N ^ (-D) * N⁻¹ := by
    rw [neg_add, Real.rpow_add hN0, Real.rpow_neg_one]
  have h3 : N⁻¹ ≤ 1 / 2 := by
    rw [one_div]; exact inv_anti₀ (by norm_num) hN
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  rw [h1]
  nlinarith

/-- **The deterministic comparison of the expectation halves**: `t₀ Δ ≤ qdBoundExp` from `Δ ≤ W^{τ/2} 𝓑_{t₀,0}²((ilambda² W^d)^{-1/5} + 𝓑_{t₀,0})`
(`(Eq:Gtlp_exp)`) and `(eq:BtBt)` (constant `2`: `8 ≤ W^{τ/2}`). -/
theorem qd_exp_core (sz : Sizes d) (n : ℕ) (hd : 3 ≤ d) {κ τ Δ : ℝ} (hκ : 0 < κ) {z : ℂ} (hz : 0 < z.im)
    (hz1 : z.im ≤ 1) (hre : |z.re| ≤ 2 - κ) (hW : 8 ≤ ((sz.W n : ℕ) : ℝ) ^ (τ / 2)) (hΔ : 0 ≤ Δ)
    (h : Δ ≤ ((sz.W n : ℕ) : ℝ) ^ (τ / 2) * (sz.Bctl n (lemT z) ^ 2 *
      ((sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d) ^ (-(1 / 5 : ℝ)) + sz.Bctl n (lemT z)))) :
    lemT z * Δ ≤ qdBoundExp sz n τ z.im := by
  have hW0 : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  set w := ((sz.W n : ℕ) : ℝ) ^ (τ / 2) with hw
  have hwpos : 0 < w := by linarith
  set B0 := calB sz n z.im 0 with hB0
  have hB0n : 0 ≤ B0 := calB_nonneg sz n hz le_rfl
  have hSB0 : sz.Bctl n (lemT z) ≤ 2 * B0 := by
    have h' := (btBt hd sz n κ hκ z hz hz1 hre 0).1
    simp only [Nat.cast_zero, mul_zero] at h'
    exact h'
  have hBc : 0 ≤ sz.Bctl n (lemT z) := Bctl_nonneg sz n _
  set E := (sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d) ^ (-(1 / 5 : ℝ)) with hE
  have hE0 : 0 ≤ E := Real.rpow_nonneg (by positivity) _
  have hY : sz.Bctl n (lemT z) ^ 2 ≤ 4 * B0 ^ 2 := by
    have := pow_le_pow_left₀ hBc hSB0 2
    calc sz.Bctl n (lemT z) ^ 2 ≤ (2 * B0) ^ 2 := this
      _ = 4 * B0 ^ 2 := by ring
  have hZ : sz.Bctl n (lemT z) ^ 2 * (E + sz.Bctl n (lemT z)) ≤ 8 * (B0 ^ 2 * (E + B0)) := by
    have h1 : sz.Bctl n (lemT z) ^ 2 * (E + sz.Bctl n (lemT z)) ≤ 4 * B0 ^ 2 * (E + 2 * B0) :=
      mul_le_mul hY (by linarith) (by positivity) (by positivity)
    nlinarith [mul_nonneg (sq_nonneg B0) hE0, mul_nonneg (sq_nonneg B0) hB0n]
  have hm0 : 0 ≤ B0 ^ 2 * (E + B0) := by positivity
  have hWτ : ((sz.W n : ℕ) : ℝ) ^ τ = w * w := by
    rw [hw, ← Real.rpow_add hW0]; congr 1; ring
  have ht1 : lemT z ≤ 1 := (lemT_lt_one hz).le
  have hexp : (-(1 : ℝ) / 5) = -(1 / 5 : ℝ) := by ring
  calc lemT z * Δ ≤ Δ := mul_le_of_le_one_left hΔ ht1
    _ ≤ w * (sz.Bctl n (lemT z) ^ 2 * (E + sz.Bctl n (lemT z))) := h
    _ ≤ w * (8 * (B0 ^ 2 * (E + B0))) := mul_le_mul_of_nonneg_left hZ hwpos.le
    _ ≤ w * (w * (B0 ^ 2 * (E + B0))) := by
        apply mul_le_mul_of_nonneg_left _ hwpos.le
        exact mul_le_mul_of_nonneg_right hW hm0
    _ = ((sz.W n : ℕ) : ℝ) ^ τ * B0 ^ 2 * (E + B0) := by rw [hWτ]; ring
    _ = qdBoundExp sz n τ z.im := by
        unfold qdBoundExp
        rw [hexp]

open RBM.Loop in
/-- **The fixed-`z` statements of `QDiff` from `UNMLOut`** (the proof plan of MA-03, compiled): sections lemma; at `t_n = lemT z_n`
the outputs `STLK` (`k = 2`), `STDecay` (`D = 6/(5𝔠)`), `STExp2`; the transfer `zTrace`, `zProfile` (loop indices `(b, a)`);
`(eq:BtBt)` and the floor (`qd_core`, `qd_exp_core`); the form bridge `explicit_of_prec` at `τ/2` and `det_of_prec` at `𝔠 τ/2`;
the union bound with `D + 1`. -/
theorem QDiffFixed_of_ML (hML : ∀ d, UNMLOut d) : QDiffFixed := by
  intro d hd 𝔠 𝔡 sz hA κ ε τ D hκ hε hτ hD
  have hA' := hA
  obtain ⟨h𝔠, h𝔡, hsz, hbw, hWO⟩ := hA'
  by_cases hκ2 : κ ≤ 2
  swap
  · exact Filter.Eventually.of_forall fun n z hz => absurd hz (locDomain_empty_kappa sz (not_le.mp hκ2) n z)
  by_cases hε1 : ε ≤ 1
  swap
  · filter_upwards [hsz.eventually_gt_atTop 1] with n hn z hz
    exact absurd hz (locDomain_empty_eps sz (not_le.mp hε1) hn z)
  have hne : ∀ n, Nonempty {z : ℂ // sz.locDomain κ ε n z} := fun n =>
    (locDomain_nonempty sz hκ2 hε1 n).elim fun z hz => ⟨⟨z, hz⟩⟩
  refine (eventually_forall_of_sections hne (Q := fun n z =>
      (Sizes.seqP sz {ω | qd1Badz sz τ n z.1 ω} ≤ ENNReal.ofReal (Nsz sz n ^ (-D)) ∧
       Sizes.seqP sz {ω | qd2Badz sz τ n z.1 ω} ≤ ENNReal.ofReal (Nsz sz n ^ (-D))) ∧
      ∀ a b : Zd d (sz.L n),
        ‖(∫ ω, avg2 sz n (fun x y => ((‖sz.Gn n z.1 ω x y‖ ^ 2 : ℝ) : ℂ)) a b ∂(Sizes.seqP sz)) -
            profPM sz n z.1 a b‖ ≤ qdBoundExp sz n τ z.1.im ∧
        ‖(∫ ω, avg2 sz n (fun x y => sz.Gn n z.1 ω x y * sz.Gn n z.1 ω y x) a b ∂(Sizes.seqP sz)) -
            profPP sz n z.1 a b‖ ≤ qdBoundExp sz n τ z.1.im) ?_).mono fun n hn z hz => hn ⟨z, hz⟩
  intro s
  set z : ℕ → ℂ := fun n => (s n).1 with hzdef
  have hzim : ∀ n, 0 < (z n).im := fun n => locDomain_im_pos (s n).2
  have hflow : STFlow sz κ ε 𝔠 𝔡 z := ⟨hA, fun n => (s n).2⟩
  obtain ⟨hLK, -, hDec, hExp, -⟩ := hML d hd κ ε 𝔡 𝔠 hκ hε h𝔡 sz z hflow (fun n => lemT (z n))
    (fun n => (lemT_pos (hzim n)).le) (fun n => le_rfl)
  have hτ2 : 0 < τ / 2 := half_pos hτ
  have hD1 : 0 < D + 1 := by linarith
  have hD'' : 0 < 6 / (5 * 𝔠) := by positivity
  have hζ2 : ∀ (n : ℕ) (u : (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n))) (ω : sz.SeqΩ),
      0 ≤ (sz.Bctl n (lemT (z n))) ^ 2 := fun n u ω => pow_nonneg (Bctl_nonneg sz n _) 2
  have hζ1 : ∀ (n : ℕ) (u : (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n))) (ω : sz.SeqΩ),
      0 ≤ (sz.Bctl n (lemT (z n))) ^ (1 / 5 : ℝ) * STWB sz n (lemT (z n)) (zdistInf d (sz.L n) (u.2 0 - u.2 1)) *
          Real.exp (-(((zdistInf d (sz.L n) (u.2 0 - u.2 1) : ℕ) : ℝ) / ellT (sz.L n) (sz.lam n) (lemT (z n))) ^
            (1 / 2 : ℝ)) + ((sz.W n : ℕ) : ℝ) ^ (-(6 / (5 * 𝔠))) :=
    fun n u ω => add_nonneg (mul_nonneg (mul_nonneg (Real.rpow_nonneg (Bctl_nonneg sz n _) _)
      (STWB_nonneg sz n _ _)) (Real.exp_nonneg _)) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hE2 := explicit_of_prec sz h𝔠 hζ2 hbw (hLK 2 (by norm_num)) hτ2 hD1
  have hE1 := explicit_of_prec sz h𝔠 hζ1 hbw (hDec (6 / (5 * 𝔠)) hD'') hτ2 hD1
  have hExpDet := det_of_prec sz hsz (by intro _ _ _ _; rfl) (by intro _ _ _ _; rfl) hExp
    (τ := 𝔠 * (τ / 2)) (by positivity)
  have hW8 : ∀ᶠ n in atTop, (8 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) ^ (τ / 2) :=
    ((tendsto_rpow_atTop hτ2).comp (RBM.Green.tendsto_W sz h𝔠 hsz hbw)).eventually_ge_atTop 8
  have hN2 : ∀ᶠ n in atTop, (2 : ℝ) ≤ Nsz sz n := hsz.eventually_ge_atTop 2
  filter_upwards [hE1, hE2, hW8, hN2, hExpDet, hbw] with n hn1 hn2 hn3 hn4 hn5 hbn
  have hz := hzim n
  have hz1 : (z n).im ≤ 1 := (s n).2.2.2
  have hre : |(z n).re| ≤ 2 - κ := (s n).2.1
  have hWpos : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hW5 : (5 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) ^ (τ / 2) := by linarith
  have ht0 : 0 < lemT (z n) := lemT_pos hz
  have hfin := two_rpow_le (D := D) hn4
  refine ⟨⟨?_, ?_⟩, fun a b => ?_⟩
  · refine (prob_union_le (Sizes.seqP sz) (((sz.W n : ℕ) : ℝ) ^ (τ / 2)) hn1 hn2 ?_).trans hfin
    intro ω h1 h2 hbad
    obtain ⟨a, b, hab⟩ := hbad
    have hΔ1 := h1 (![true, false], ![b, a])
    have hΔ2 := h2 (![true, false], ![b, a])
    have htr := (zTrace sz n (z n) hz ω a b).2
    have hpf := (zProfile sz n (z n) hz a b).1
    have hnorm : ‖avg2 sz n (fun x y => ((‖sz.Gn n (z n) ω x y‖ ^ 2 : ℝ) : ℂ)) a b - profPM sz n (z n) a b‖ =
        lemT (z n) * ‖sz.Lloop n (lemE (z n)) (lemT (z n)) ![true, false] ![b, a] ω -
          sz.STKloop n (lemE (z n)) (lemT (z n)) ![true, false] ![b, a]‖ := by
      rw [htr, hpf, ← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht0.le]
    have hcore := qd_core sz n hd h𝔠 hκ hbn hz hz1 hre hW5 a b (norm_nonneg _) (Real.exp_nonneg _)
      (Real.exp_le_one_iff.2 (neg_nonpos.2 (Real.rpow_nonneg (div_nonneg (Nat.cast_nonneg _) ellT_nonneg) _)))
      hΔ1 hΔ2
    rw [hnorm] at hab
    exact absurd hab (not_lt.2 hcore)
  · refine (prob_union_le (Sizes.seqP sz) (((sz.W n : ℕ) : ℝ) ^ (τ / 2)) hn1 hn2 ?_).trans hfin
    intro ω h1 h2 hbad
    obtain ⟨a, b, hab⟩ := hbad
    have hΔ1 := h1 (![true, true], ![b, a])
    have hΔ2 := h2 (![true, true], ![b, a])
    have htr := (zTrace sz n (z n) hz ω a b).1
    have hpf := (zProfile sz n (z n) hz a b).2
    have hnorm : ‖avg2 sz n (fun x y => sz.Gn n (z n) ω x y * sz.Gn n (z n) ω y x) a b - profPP sz n (z n) a b‖ =
        lemT (z n) * ‖sz.Lloop n (lemE (z n)) (lemT (z n)) ![true, true] ![b, a] ω -
          sz.STKloop n (lemE (z n)) (lemT (z n)) ![true, true] ![b, a]‖ := by
      rw [htr, hpf, ← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht0.le]
    have hcore := qd_core sz n hd h𝔠 hκ hbn hz hz1 hre hW5 a b (norm_nonneg _) (Real.exp_nonneg _)
      (Real.exp_le_one_iff.2 (neg_nonpos.2 (Real.rpow_nonneg (div_nonneg (Nat.cast_nonneg _) ellT_nonneg) _)))
      hΔ1 hΔ2
    rw [hnorm] at hab
    exact absurd hab (not_lt.2 hcore)
  · -- the expectation halves
    have hW8n : (8 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) ^ (τ / 2) := hn3
    have hNW : Nsz sz n ^ (𝔠 * (τ / 2)) ≤ ((sz.W n : ℕ) : ℝ) ^ (τ / 2) := by
      rw [Real.rpow_mul (Nat.cast_nonneg _)]
      exact Real.rpow_le_rpow (Real.rpow_nonneg (Nat.cast_nonneg _) _) hbn hτ2.le
    have hbd : ∀ σ : Fin 2 → Bool,
        ‖(∫ ω, sz.Lloop n (lemE (z n)) (lemT (z n)) σ ![b, a] ω ∂(Sizes.seqP sz)) -
            sz.STKloop n (lemE (z n)) (lemT (z n)) σ ![b, a]‖ ≤
          ((sz.W n : ℕ) : ℝ) ^ (τ / 2) * (sz.Bctl n (lemT (z n)) ^ 2 *
            ((sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d) ^ (-(1 / 5 : ℝ)) + sz.Bctl n (lemT (z n)))) := by
      intro σ
      have h := hn5 (σ, ![b, a]) (Classical.arbitrary _)
      refine h.trans ?_
      refine mul_le_mul_of_nonneg_right hNW ?_
      refine mul_nonneg (pow_nonneg (Bctl_nonneg sz n _) 2) (add_nonneg (Real.rpow_nonneg (by positivity) _)
        (Bctl_nonneg sz n _))
    refine ⟨?_, ?_⟩
    · have hint : ∫ ω, avg2 sz n (fun x y => ((‖sz.Gn n (z n) ω x y‖ ^ 2 : ℝ) : ℂ)) a b ∂(Sizes.seqP sz) =
          (lemT (z n) : ℂ) * ∫ ω, sz.Lloop n (lemE (z n)) (lemT (z n)) ![true, false] ![b, a] ω ∂(Sizes.seqP sz) := by
        rw [← integral_const_mul]
        exact integral_congr_ae (Filter.Eventually.of_forall fun ω => (zTrace sz n (z n) hz ω a b).2)
      have hpf := (zProfile sz n (z n) hz a b).1
      rw [hint, hpf, ← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht0.le]
      exact qd_exp_core sz n hd hκ hz hz1 hre hW8n (norm_nonneg _) (hbd ![true, false])
    · have hint : ∫ ω, avg2 sz n (fun x y => sz.Gn n (z n) ω x y * sz.Gn n (z n) ω y x) a b ∂(Sizes.seqP sz) =
          (lemT (z n) : ℂ) * ∫ ω, sz.Lloop n (lemE (z n)) (lemT (z n)) ![true, true] ![b, a] ω ∂(Sizes.seqP sz) := by
        rw [← integral_const_mul]
        exact integral_congr_ae (Filter.Eventually.of_forall fun ω => (zTrace sz n (z n) hz ω a b).1)
      have hpf := (zProfile sz n (z n) hz a b).2
      rw [hint, hpf, ← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht0.le]
      exact qd_exp_core sz n hd hκ hz hz1 hre hW8n (norm_nonneg _) (hbd ![true, true])

/-- **`MAFixed` proved**: both fixed-`z` statements follow from the flow outputs `∀ d, UNMLOut d` (the one input owed by ST-6). -/
theorem fixed_of_ML : MAFixed := fun hML => ⟨locSCFixed_of_ML hML, QDiffFixed_of_ML hML⟩

end QDFixed


/-! ### (d) `decol` from `locSC` by `(eq:ukx)`: no net once `∩_z` is inside (compiled) -/

section Spectral

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {H : Matrix ι ι ℂ} {μ : ι → ℝ} {ψ : ι → ι → ℂ}

/-- `G_xx(z) = ∑_l |ψ_l(x)|² / (μ_l - z)` for any orthonormal eigenbasis (port of RBM2D
`DecolFromLocal_green_apply_self`, `RBM2D/Main/DecolFromLocal.lean:35`, `green` → `Gres`). -/
theorem Gres_apply_self (hψ : IsOrthoEigenbasis H μ ψ) {z : ℂ}
    (hz : ∀ l, (μ l : ℂ) ≠ z) (x : ι) :
    Gres H z true x x = ∑ l, (Complex.normSq (ψ l x) : ℂ) / ((μ l : ℂ) - z) := by
  set U : Matrix ι ι ℂ := Matrix.of fun y l => ψ l y with hU
  have hUU : star U * U = 1 := by
    ext k k'
    have h := hψ.1 k k'
    simp only [dotProduct, Pi.star_apply] at h
    simp only [Matrix.mul_apply, Matrix.star_apply, hU, Matrix.of_apply, Matrix.one_apply]
    exact h
  have hUU' : U * star U = 1 := mul_eq_one_comm.mp hUU
  have hHU : H * U = U * diagonal (fun l => (μ l : ℂ)) := by
    ext y l
    have h := congrFun (hψ.2 l) y
    simp only [mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at h
    rw [mul_diagonal, Matrix.mul_apply]
    simp only [hU, Matrix.of_apply]
    rw [h, mul_comm]
  have hsub : (H - z • 1) * U = U * diagonal (fun l => (μ l : ℂ) - z) := by
    rw [Matrix.sub_mul, hHU, Matrix.smul_mul, Matrix.one_mul, ← diagonal_sub,
      Matrix.mul_sub, ← smul_one_eq_diagonal, Matrix.mul_smul, Matrix.mul_one]
  have hinv : Gres H z true = U * diagonal (fun l => ((μ l : ℂ) - z)⁻¹) * star U := by
    unfold Gres
    simp only [↓reduceIte, ← Matrix.nonsing_inv_eq_ringInverse]
    apply Matrix.inv_eq_right_inv
    calc (H - z • 1) * (U * diagonal (fun l => ((μ l : ℂ) - z)⁻¹) * star U)
        = ((H - z • 1) * U) * diagonal (fun l => ((μ l : ℂ) - z)⁻¹) * star U := by
          simp only [Matrix.mul_assoc]
      _ = U * (diagonal (fun l => (μ l : ℂ) - z)
            * diagonal (fun l => ((μ l : ℂ) - z)⁻¹)) * star U := by
          rw [hsub]; simp only [Matrix.mul_assoc]
      _ = 1 := by
          have hd : (fun l => ((μ l : ℂ) - z) * ((μ l : ℂ) - z)⁻¹) = fun _ => (1 : ℂ) :=
            funext fun l => mul_inv_cancel₀ (sub_ne_zero.mpr (hz l))
          rw [diagonal_mul_diagonal, hd, diagonal_one, Matrix.mul_one, hUU']
  rw [hinv, mul_apply]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [mul_diagonal, star_apply, Complex.normSq_eq_conj_mul_self]
  simp only [hU, Matrix.of_apply, RCLike.star_def]
  ring

/-- **`(eq:ukx)`** (`1_2:399`): `|ψ_k(x)|² ≤ η Im G_xx(λ_k + iη)` for every `η > 0` and every orthonormal
eigenbasis: the term `l = k` of `Im G_xx = ∑_l η|ψ_l(x)|²/((μ_l - E)² + η²)` at `E = μ_k`.  (RBM2D
`DecolFromLocal_sq_le_two_mul_im_green` has the factor `2η` for `|μ_k - E| ≤ η`; at `E = μ_k` it is exact.) -/
theorem ukx (hψ : IsOrthoEigenbasis H μ ψ) {η : ℝ} (hη : 0 < η) (k x : ι) :
    ‖ψ k x‖ ^ 2 ≤ η * (Gres H ((μ k : ℂ) + η * Complex.I) true x x).im := by
  have hz : ∀ l, (μ l : ℂ) ≠ (μ k : ℂ) + η * Complex.I := by
    intro l h
    have := congrArg Complex.im h
    simp at this
    exact hη.ne' this.symm
  rw [Gres_apply_self hψ hz, Complex.im_sum]
  have hterm : ∀ l ∈ Finset.univ, 0 ≤ η * ((Complex.normSq (ψ l x) : ℂ) /
      ((μ l : ℂ) - ((μ k : ℂ) + η * Complex.I))).im := by
    intro l _
    have hn : Complex.normSq ((μ l : ℂ) - ((μ k : ℂ) + η * Complex.I)) = (μ l - μ k) ^ 2 + η ^ 2 := by
      rw [Complex.normSq_apply]; simp; ring
    have him : ((μ l : ℂ) - ((μ k : ℂ) + η * Complex.I)).im = -η := by simp
    rw [div_eq_mul_inv, Complex.im_ofReal_mul, Complex.inv_im, hn, him]
    have hpos : 0 < (μ l - μ k) ^ 2 + η ^ 2 := by positivity
    have := Complex.normSq_nonneg (ψ l x)
    have : 0 ≤ Complex.normSq (ψ l x) * (η / ((μ l - μ k) ^ 2 + η ^ 2)) := by positivity
    calc 0 ≤ η * (Complex.normSq (ψ l x) * (η / ((μ l - μ k) ^ 2 + η ^ 2))) := by positivity
      _ = η * (Complex.normSq (ψ l x) * (-(-η) / ((μ l - μ k) ^ 2 + η ^ 2))) := by ring
  rw [Finset.mul_sum]
  refine le_trans ?_ (Finset.single_le_sum hterm (Finset.mem_univ k))
  have hn : Complex.normSq ((μ k : ℂ) - ((μ k : ℂ) + η * Complex.I)) = η ^ 2 := by
    rw [Complex.normSq_apply]; simp; ring
  have him : ((μ k : ℂ) - ((μ k : ℂ) + η * Complex.I)).im = -η := by simp
  rw [div_eq_mul_inv, Complex.im_ofReal_mul, Complex.inv_im, hn, him, Complex.normSq_eq_norm_sq]
  have h2 : η ^ 2 ≠ 0 := by positivity
  have h3 : η ≠ 0 := hη.ne'
  field_simp
  exact le_refl _

end Spectral

section Decol

variable {d : ℕ}

theorem zdistInf_zero (d L : ℕ) : zdistInf d L 0 = 0 := by
  simp [zdistInf, zdist]

/-- The scalars of the deduction (preflight row 7): `ε = min(τ/2, 1/2)`, `τ_L = min(𝔡, dε/2)`, `η = N^{-1+ε}`:
`W^{τ_L} 𝓑_{η,0} ≤ 1` (`𝓑_{η,0} ≤ W^{-2𝔡} + W^{-dε}`, `ilambda² W^d ≥ W^{2𝔡}` by `(eq:WO)`, `N ≥ W^d`) and
`2 η ≤ N^{-1+τ}`; both eventually, from `W → ∞`, `N → ∞`. -/
theorem decol_scalars (sz : Sizes d) {𝔠 𝔡 : ℝ} (hd : 2 ≤ d) (hA : sz.Admissible 𝔠 𝔡) {τ : ℝ} (hτ : 0 < τ) :
    ∀ᶠ n in atTop,
      ((sz.W n : ℕ) : ℝ) ^ (min 𝔡 ((d : ℝ) * min (τ / 2) (1 / 2) / 2)) *
          calB sz n (Nsz sz n ^ (-1 + min (τ / 2) (1 / 2))) 0 ≤ 1 ∧
        2 * Nsz sz n ^ (-1 + min (τ / 2) (1 / 2)) ≤ Nsz sz n ^ (-1 + τ) := by
  obtain ⟨h𝔠, h𝔡, hsz, hbw, hWO⟩ := hA
  have hd' : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  set ε := min (τ / 2) (1 / 2) with hεdef
  set τL := min 𝔡 ((d : ℝ) * ε / 2) with hτLdef
  have hε0 : 0 < ε := lt_min (half_pos hτ) (by norm_num)
  have hετ : ε ≤ τ / 2 := min_le_left _ _
  have hτL0 : 0 < τL := lt_min h𝔡 (by positivity)
  have hτL1 : τL ≤ 𝔡 := min_le_left _ _
  have hτL2 : τL ≤ (d : ℝ) * ε / 2 := min_le_right _ _
  have hW := RBM.Green.tendsto_W sz h𝔠 hsz hbw
  filter_upwards [hWO, hW.eventually_ge_atTop 1, ((tendsto_rpow_atTop hτL0).comp hW).eventually_ge_atTop 2,
    ((tendsto_rpow_atTop (half_pos hτ)).comp hsz).eventually_ge_atTop 2, hsz.eventually_ge_atTop 1]
    with n hWOn hW1 hWτ2 hNτ2 hN1
  have hWpos : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by linarith
  have hNpos : (0 : ℝ) < Nsz sz n := Nsz_pos sz n
  have hη : 0 < Nsz sz n ^ (-1 + ε) := Real.rpow_pos_of_pos hNpos _
  refine ⟨?_, ?_⟩
  · -- `W^{τ_L} 𝓑_{η,0} ≤ 1`
    have hlam : 0 < sz.lam n := lt_of_lt_of_le (Real.rpow_pos_of_pos hWpos _) hWOn.1
    have hlsq := Sizes.lam_sq_mul_pow_ge sz n hWOn.1
    have hWd : 0 < ((sz.W n : ℕ) : ℝ) ^ d := by positivity
    -- term 1
    have hT1 : (sz.lam n ^ 2 + Nsz sz n ^ (-1 + ε))⁻¹ /
        (((sz.W n : ℕ) : ℝ) ^ 2 * (0 + ((sz.W n : ℕ) : ℝ)) ^ (d - 2)) ≤
        ((sz.W n : ℕ) : ℝ) ^ (-(2 * 𝔡)) := by
      have hWW : ((sz.W n : ℕ) : ℝ) ^ 2 * (0 + ((sz.W n : ℕ) : ℝ)) ^ (d - 2) = ((sz.W n : ℕ) : ℝ) ^ d := by
        rw [zero_add, ← pow_add]; congr 1; omega
      rw [hWW, Real.rpow_neg hWpos.le]
      have h1 : (sz.lam n ^ 2 + Nsz sz n ^ (-1 + ε))⁻¹ ≤ (sz.lam n ^ 2)⁻¹ :=
        inv_anti₀ (by positivity) (by linarith)
      calc (sz.lam n ^ 2 + Nsz sz n ^ (-1 + ε))⁻¹ / ((sz.W n : ℝ) ^ d)
          ≤ (sz.lam n ^ 2)⁻¹ / ((sz.W n : ℝ) ^ d) := div_le_div_of_nonneg_right h1 hWd.le
        _ = (sz.lam n ^ 2 * ((sz.W n : ℝ) ^ d))⁻¹ := by rw [div_eq_mul_inv, mul_inv]
        _ ≤ (((sz.W n : ℕ) : ℝ) ^ (2 * 𝔡))⁻¹ := inv_anti₀ (by positivity) hlsq
    -- term 2
    have hT2 : (Nsz sz n * Nsz sz n ^ (-1 + ε))⁻¹ ≤ ((sz.W n : ℕ) : ℝ) ^ (-((d : ℝ) * ε)) := by
      have h1 : Nsz sz n * Nsz sz n ^ (-1 + ε) = Nsz sz n ^ ε := by
        have := Real.rpow_add hNpos 1 (-1 + ε)
        rw [Real.rpow_one] at this
        rw [← this]; congr 1; ring
      rw [h1, ← Real.rpow_neg hNpos.le]
      have hle : ((sz.W n : ℕ) : ℝ) ^ d ≤ Nsz sz n := by
        have h : (sz.W n) ^ d ≤ (sz.W n * sz.L n) ^ d :=
          Nat.pow_le_pow_left (Nat.le_mul_of_pos_right _ (by have := sz.three_le_L n; omega)) d
        exact_mod_cast h
      have h2 : Nsz sz n ^ (-ε) ≤ (((sz.W n : ℕ) : ℝ) ^ d) ^ (-ε) :=
        Real.rpow_le_rpow_of_nonpos hWd hle (by linarith)
      have h3 : (((sz.W n : ℕ) : ℝ) ^ d) ^ (-ε) = ((sz.W n : ℕ) : ℝ) ^ (-((d : ℝ) * ε)) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hWpos.le]; congr 1; ring
      linarith
    have hcal : calB sz n (Nsz sz n ^ (-1 + ε)) 0 ≤
        ((sz.W n : ℕ) : ℝ) ^ (-(2 * 𝔡)) + ((sz.W n : ℕ) : ℝ) ^ (-((d : ℝ) * ε)) := by
      unfold calB
      have := add_le_add hT1 hT2
      simpa [Sizes.size, Nsz] using this
    have hA1 : ((sz.W n : ℕ) : ℝ) ^ τL * ((sz.W n : ℕ) : ℝ) ^ (-(2 * 𝔡)) ≤ ((sz.W n : ℕ) : ℝ) ^ (-τL) := by
      rw [← Real.rpow_add hWpos]
      exact Real.rpow_le_rpow_of_exponent_le hW1 (by linarith)
    have hA2 : ((sz.W n : ℕ) : ℝ) ^ τL * ((sz.W n : ℕ) : ℝ) ^ (-((d : ℝ) * ε)) ≤ ((sz.W n : ℕ) : ℝ) ^ (-τL) := by
      rw [← Real.rpow_add hWpos]
      exact Real.rpow_le_rpow_of_exponent_le hW1 (by linarith)
    have hWτ2' : (2 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) ^ τL := hWτ2
    have hinv : ((sz.W n : ℕ) : ℝ) ^ (-τL) ≤ 1 / 2 := by
      rw [Real.rpow_neg hWpos.le]
      have : (2 : ℝ)⁻¹ = 1 / 2 := by norm_num
      rw [← this]
      exact inv_anti₀ (by norm_num) hWτ2'
    calc ((sz.W n : ℕ) : ℝ) ^ τL * calB sz n (Nsz sz n ^ (-1 + ε)) 0
        ≤ ((sz.W n : ℕ) : ℝ) ^ τL * (((sz.W n : ℕ) : ℝ) ^ (-(2 * 𝔡)) + ((sz.W n : ℕ) : ℝ) ^ (-((d : ℝ) * ε))) :=
          mul_le_mul_of_nonneg_left hcal (by positivity)
      _ = ((sz.W n : ℕ) : ℝ) ^ τL * ((sz.W n : ℕ) : ℝ) ^ (-(2 * 𝔡)) +
            ((sz.W n : ℕ) : ℝ) ^ τL * ((sz.W n : ℕ) : ℝ) ^ (-((d : ℝ) * ε)) := by ring
      _ ≤ 1 / 2 + 1 / 2 := add_le_add (hA1.trans hinv) (hA2.trans hinv)
      _ = 1 := by norm_num
  · -- `2 η ≤ N^{-1+τ}`
    have h1 : Nsz sz n ^ (-1 + τ) = Nsz sz n ^ (-1 + ε) * Nsz sz n ^ (τ - ε) := by
      rw [← Real.rpow_add hNpos]; congr 1; ring
    have hN1' : (1 : ℝ) ≤ Nsz sz n := by exact_mod_cast hN1
    have hNτ2' : (2 : ℝ) ≤ Nsz sz n ^ (τ / 2) := hNτ2
    have h2 : Nsz sz n ^ (τ / 2) ≤ Nsz sz n ^ (τ - ε) :=
      Real.rpow_le_rpow_of_exponent_le hN1' (by linarith)
    rw [h1]
    nlinarith [mul_le_mul_of_nonneg_left (hNτ2'.trans h2) hη.le]


/-- **The spectral core of delocalization, for any Hermitian matrix and any deterministic diagonal** (carrier-free: no
`msc`, no band model; this is the part of `decol` that the block Anderson model reuses): if at `z = λ_k + iη` the diagonal
local law `|G_xx(z) - M_xx(z)| ≤ 1` holds and `Im M_xx(z) ≤ C_M`, then `|ψ_k(x)|² ≤ η (C_M + 1)` (`(eq:ukx)`).  The band
instance is `M_xx = m(z)`, `C_M = 1`. -/
theorem decol_spectral_core {ι : Type*} [Fintype ι] [DecidableEq ι] {H : Matrix ι ι ℂ} {μ : ι → ℝ}
    {ψ : ι → ι → ℂ} (hψ : IsOrthoEigenbasis H μ ψ) {η CM B : ℝ} (hη : 0 < η) {k x : ι} {M : ℂ}
    (hloc : ‖Gres H ((μ k : ℂ) + η * Complex.I) true x x - M‖ ≤ 1) (hM : M.im ≤ CM)
    (hB : η * (CM + 1) ≤ B) : ‖ψ k x‖ ^ 2 ≤ B := by
  have him : (Gres H ((μ k : ℂ) + η * Complex.I) true x x).im ≤ CM + 1 := by
    have h1 : (Gres H ((μ k : ℂ) + η * Complex.I) true x x).im =
        (Gres H ((μ k : ℂ) + η * Complex.I) true x x - M).im + M.im := by simp
    have h2 := Complex.im_le_norm (Gres H ((μ k : ℂ) + η * Complex.I) true x x - M)
    linarith
  calc ‖ψ k x‖ ^ 2 ≤ η * (Gres H ((μ k : ℂ) + η * Complex.I) true x x).im := ukx hψ hη k x
    _ ≤ η * (CM + 1) := mul_le_mul_of_nonneg_left him hη.le
    _ ≤ B := hB

/-- **The deterministic core of `decol` from `locSC`** (band instance of `decol_spectral_core`): on the event `¬ locBad1`
at `(κ, ε, τ_L)` (`∩_z` inside), every orthonormal eigenbasis has `‖ψ_k‖²_∞ ≤ N^{-1+τ}` for the bulk eigenvalues: take
`z = λ_k + iη`, `η = N^{-1+ε} ∈ 𝐃_{κ,ε}`, `|G_xx - m|² ≤ W^{τ_L} 𝓑_{η,0} ≤ 1` and `|m| < 1`, so `‖ψ_k(x)‖² ≤ 2η ≤ N^{-1+τ}`.
No net. -/
theorem decol_core (sz : Sizes d) {κ ε τ τL : ℝ} (n : ℕ) (ω : sz.SeqΩ) (hε1 : ε ≤ 1)
    (hgood : ¬ locBad1 sz κ ε τL n ω)
    (hs1 : ((sz.W n : ℕ) : ℝ) ^ τL * calB sz n (Nsz sz n ^ (-1 + ε)) 0 ≤ 1)
    (hs2 : 2 * Nsz sz n ^ (-1 + ε) ≤ Nsz sz n ^ (-1 + τ)) : ¬ decolBad sz n κ τ ω := by
  intro hbad
  apply hbad
  intro μ ψ hψ k hk x
  set η := Nsz sz n ^ (-1 + ε) with hηdef
  have hNpos := Nsz_pos sz n
  have hη0 : 0 < η := Real.rpow_pos_of_pos hNpos _
  have hN1 : (1 : ℝ) ≤ Nsz sz n := by exact_mod_cast one_le_size sz n
  have hη1 : η ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN1 (by linarith)
  have hdom : sz.locDomain κ ε n ((μ k : ℂ) + η * Complex.I) :=
    ⟨by simpa using hk, by simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_add, add_zero]; exact le_rfl, by simpa using hη1⟩
  have hnot : ¬ locBad1z sz τL n ((μ k : ℂ) + η * Complex.I) ω := fun h => hgood ⟨_, hdom, h⟩
  unfold locBad1z at hnot
  push Not at hnot
  have hxx := hnot x x
  have hdist : distB sz n (STblk sz n x) (STblk sz n x) = 0 := by simp [distB, zdistInf_zero]
  have him : ((μ k : ℂ) + η * Complex.I).im = η := by simp
  rw [hdist, him] at hxx
  have hM : Mband sz n ((μ k : ℂ) + η * Complex.I) x x = msc ((μ k : ℂ) + η * Complex.I) := by simp [Mband]
  rw [hM] at hxx
  have hsq := hxx.trans hs1
  have hloc : ‖Gres (sz.seqXmat n ω) ((μ k : ℂ) + η * Complex.I) true x x - msc ((μ k : ℂ) + η * Complex.I)‖ ≤ 1 := by
    have h0 := norm_nonneg (sz.Gn n ((μ k : ℂ) + η * Complex.I) ω x x - msc ((μ k : ℂ) + η * Complex.I))
    have : ‖sz.Gn n ((μ k : ℂ) + η * Complex.I) ω x x - msc ((μ k : ℂ) + η * Complex.I)‖ ≤ 1 := by nlinarith
    exact this
  have hmsc : ‖msc ((μ k : ℂ) + η * Complex.I)‖ < 1 := norm_msc_lt_one (by simpa using hη0)
  have hMim : (msc ((μ k : ℂ) + η * Complex.I)).im ≤ 1 := (Complex.im_le_norm _).trans hmsc.le
  exact decol_spectral_core hψ hη0 hloc hMim (by linarith)

/-- **Pin `MADecol` proved: `decol` from `locSC`** (`1_2:397-401`, `(eq:ukx)` `1_2:399`).  The local law is used at
`ε = min(τ/2, 1/2)` (the paper's `η = N^{-1+τ}` gives `ψ² ≤ C N^{-1+τ}` with a constant `C ≥ 1` that is not absorbed;
paper-delta candidate `T2192c`) and `τ_L = min(𝔡, dε/2)`.  RBM2D `decol_of_locSC` (`RBM2D/Main/DecolFromLocal.lean:239`)
needs an energy net because its `locSC` is pointwise in `z`. -/
def MADecol : Prop := locSC → decol

theorem decol_of_locSC : MADecol := by
  intro h d hd 𝔠 𝔡 sz hA κ τ D hκ hτ hD
  have hd2 : 2 ≤ d := by omega
  have h𝔡 : 0 < 𝔡 := hA.2.1
  have hε0 : 0 < min (τ / 2) (1 / 2 : ℝ) := lt_min (half_pos hτ) (by norm_num)
  have hε1 : min (τ / 2) (1 / 2 : ℝ) ≤ 1 := (min_le_right _ _).trans (by norm_num)
  have hτL0 : 0 < min 𝔡 ((d : ℝ) * min (τ / 2) (1 / 2) / 2) := by
    refine lt_min h𝔡 ?_
    have : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
    positivity
  filter_upwards [h d hd 𝔠 𝔡 sz hA κ (min (τ / 2) (1 / 2)) (min 𝔡 ((d : ℝ) * min (τ / 2) (1 / 2) / 2)) D
    hκ hε0 hτL0 hD, decol_scalars sz hd2 hA hτ] with n hn hsc
  refine le_trans (measure_mono ?_) hn.1
  intro ω hbad
  by_contra hnot
  exact decol_core sz n ω hε1 hnot hsc.1 hsc.2 hbad

end Decol

namespace Inst

open RBM.Gauss.SizesInst RBM.Univ.UNInst

/-- **`decol` from `locSC`** at the instance (proved). -/
theorem inst_decol_of_locSC (h : locSC) :
    ∀ᶠ n in atTop, Sizes.seqP sz0 {ω | decolBad sz0 n (1 / 10) (1 / 10) ω} ≤
      ENNReal.ofReal (Nsz sz0 n ^ (-(1 : ℝ))) :=
  decol_of_locSC h 3 le_rfl (1 / 6) (1 / 10) sz0 sz0_admissible (1 / 10) (1 / 10) 1 (by norm_num) (by norm_num)
    (by norm_num)

/-- **The fixed-`z` statements from `UNMLOut`** at the instance (proved, `locSCFixed_of_ML`; the flow outputs are the
hypothesis). -/
theorem inst_locSCFixed (hML : ∀ d : ℕ, UNMLOut d) :
    ∀ᶠ n in atTop, ∀ z : ℂ, sz0.locDomain (1 / 10) (1 / 20) n z →
      Sizes.seqP sz0 {ω | locBad1z sz0 (1 / 10) n z ω} ≤ ENNReal.ofReal (Nsz sz0 n ^ (-(2 : ℝ))) ∧
      Sizes.seqP sz0 {ω | locBad2z sz0 (1 / 10) n z ω} ≤ ENNReal.ofReal (Nsz sz0 n ^ (-(2 : ℝ))) :=
  locSCFixed_of_ML hML 3 le_rfl (1 / 6) (1 / 10) sz0 sz0_admissible (1 / 10) (1 / 20) (1 / 10) 2 (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

/-- **The fixed-`z` statements of `QDiff` from `UNMLOut`** at the instance (proved, `QDiffFixed_of_ML`): both probability halves
and both expectation halves, for every `z ∈ 𝐃_{1/10,1/20}` and every pair of blocks, `N₀` uniform. -/
theorem inst_QDiffFixed (hML : ∀ d : ℕ, UNMLOut d) :
    ∀ᶠ n in atTop, ∀ z : ℂ, sz0.locDomain (1 / 10) (1 / 20) n z →
      (Sizes.seqP sz0 {ω | qd1Badz sz0 (1 / 10) n z ω} ≤ ENNReal.ofReal (Nsz sz0 n ^ (-(2 : ℝ))) ∧
       Sizes.seqP sz0 {ω | qd2Badz sz0 (1 / 10) n z ω} ≤ ENNReal.ofReal (Nsz sz0 n ^ (-(2 : ℝ)))) ∧
      ∀ a b : Zd 3 (sz0.L n),
        ‖(∫ ω, avg2 sz0 n (fun x y => ((‖sz0.Gn n z ω x y‖ ^ 2 : ℝ) : ℂ)) a b ∂(Sizes.seqP sz0)) -
            profPM sz0 n z a b‖ ≤ qdBoundExp sz0 n (1 / 10) z.im ∧
        ‖(∫ ω, avg2 sz0 n (fun x y => sz0.Gn n z ω x y * sz0.Gn n z ω y x) a b ∂(Sizes.seqP sz0)) -
            profPP sz0 n z a b‖ ≤ qdBoundExp sz0 n (1 / 10) z.im :=
  QDiffFixed_of_ML hML 3 le_rfl (1 / 6) (1 / 10) sz0 sz0_admissible (1 / 10) (1 / 20) (1 / 10) 2 (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

/-- The scalars of `decol` at the instance (`τ = 1/10`). -/
theorem inst_decol_scalars :
    ∀ᶠ n in atTop, ((sz0.W n : ℕ) : ℝ) ^ (min (1 / 10 : ℝ) (((3 : ℕ) : ℝ) * min ((1 / 10 : ℝ) / 2) (1 / 2) / 2)) *
        calB sz0 n (Nsz sz0 n ^ (-1 + min ((1 / 10 : ℝ) / 2) (1 / 2))) 0 ≤ 1 ∧
      2 * Nsz sz0 n ^ (-1 + min ((1 / 10 : ℝ) / 2) (1 / 2)) ≤ Nsz sz0 n ^ (-1 + (1 / 10 : ℝ)) :=
  decol_scalars (d := 3) sz0 (by norm_num) sz0_admissible (τ := 1 / 10) (by norm_num)

end Inst

end RBM.Endpoints
