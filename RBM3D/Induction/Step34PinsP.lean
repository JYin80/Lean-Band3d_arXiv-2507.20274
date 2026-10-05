/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Induction.Step34Pins

/-!
# The primed pins of `lem:STOeq_NQ` (`STNQConcl'`, `STOeqNQ'`)

Ticket T2186 (S3-12a, stochastic layer ST-3, first of three).  The merged `STNQConcl`
(`Induction/Step34Pins.lean:428`) has the random self-term
`B_u^{1/6} sup_{w ∈ [s,u]} Ξ̂^{𝓛-𝒦}_{w,n_}` on the right of `(am;asoiuw)`; it cannot be reached
by route (R) (DECISIONS §60: the random multi-time self-term `STsupXiLK` is the obstruction;
§62: Jun's choice "A").  The primed pin is the form of RBM2D `STOeqPT`
(`Induction/Defs.lean:247` at `c9a24cf`): the current length `n_` is controlled by a
deterministic `XLK n_ n u` (hypothesis `Ξ̂^{𝓛-𝒦}_m ≺ XLK m` for `1 ≤ m ≤ n_`, the current length
included) and the right side is `B_u^{1/6} XLK n_ n u + STbootRHS 2 …` (paper-delta candidate
`T2186a`).

* §1 `STNQConcl'`, `STOeqNQ'` (check file `docs/tickets/checks/T2186-check.lean`, section 2,
  verbatim);
* §2 the old pin implies the new one: private `stNQConcl'_of_stNQConcl` (private, because a
  public theorem with `STNQConcl` in a binder would make the registry scan report `STNQConcl` as
  an unregistered premise), and the public `stOeqNQ'_of_stOeqNQ`;
* §3 the instance `inst_OeqNQ'` (namespace `RBM.Gauss.Step34PInst`) and its compiled use.

The merged `STNQConcl`, `STOeqNQ`, `inst_OeqNQ` are not modified.
-/

set_option linter.style.longLine false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal

/-! ## 1. The primed pins -/

namespace RBM.Gauss.Sizes

open RBM RBM.Loop RBM.Path RBM.Gauss

section Pins

variable {d : ℕ} (sz : Sizes d)

/-- **`lem:STOeq_NQ`, primed** (`3_5:1136`, bound `(am;asoiuw)` `3_5:1143-1148`; DECISIONS §62 (1), the form of
RBM2D `STOeqPT`, `Induction/Defs.lean:247` at `c9a24cf`): the merged `STNQConcl` (`Step34Pins.lean:428`) with
the hypothesis `Ξ̂^{𝓛-𝒦}_m ≺ XLK m` for `1 ≤ m ≤ n_` (the current length included) and the random self-term
`B_u^{1/6} · STsupXiLK … (s n) u n_` replaced by the deterministic `B_u^{1/6} · XLK n_ n u`
(paper-delta candidate `T2186a`). -/
def STNQConcl' (E s t : ℕ → ℝ) : Prop :=
  ∀ n_ p : ℕ, 2 ≤ n_ → 1 ≤ p → ∀ XL XLK : ℕ → ℕ → ℝ → ℝ,
    (∀ m n u, 1 ≤ XL m n u) → (∀ m n u, 1 ≤ XLK m n u) →
    (∀ m, 1 ≤ m → STlenL n_ p m →
      Prec sz (U := STPair s t) (fun n q ω => STXiL sz n (E n) q.1.1 m ω) (fun n q _ => XL m n q.1.2)) →
    (∀ m, 1 ≤ m → m ≤ n_ →
      Prec sz (U := STPair s t) (fun n q ω => STXiLK sz n (E n) q.1.1 m ω) (fun n q _ => XLK m n q.1.2)) →
    Prec sz (U := fun n => TimeIcc s t n × {σ : Fin n_ → Bool // ∃ k, σ k = σ (finRotate n_ k)} ×
        (Fin n_ → Zd d (sz.L n)))
      (fun n q ω => ‖Lloop sz n (E n) (q.1 : ℝ) q.2.1.1 q.2.2 ω - STKloop sz n (E n) (q.1 : ℝ) q.2.1.1 q.2.2‖ /
        (sz.Bctl n (q.1 : ℝ)) ^ n_)
      (fun n q _ => (sz.Bctl n (q.1 : ℝ)) ^ (1 / 6 : ℝ) * XLK n_ n (q.1 : ℝ) +
        STbootRHS 2 (fun m => XL m n (q.1 : ℝ)) (fun m => XLK m n (q.1 : ℝ)) (sz.Bctl n (q.1 : ℝ)) n_ p)

end Pins

/-- `lem:STOeq_NQ` primed (`3_5:1136`): case (i), the conclusion `STNQConcl'`. -/
def STOeqNQ' (d : ℕ) : Prop := STIngR d STCaseI (fun sz E s t => STNQConcl' sz E s t)

/-! ## 2. The merged pin implies the primed one -/

section Implication

variable {d : ℕ}

/-- `0 ≤ STbootRHS lo XL XLK B n_ p` for `B ≥ 0`, `XL, XLK ≥ 0` (all terms are nonnegative). -/
private theorem stP_bootRHS_nonneg {lo : ℕ} {XL XLK : ℕ → ℝ} {B : ℝ} {n_ p : ℕ} (hB : 0 ≤ B)
    (hXL : ∀ m, 0 ≤ XL m) (hXLK : ∀ m, 0 ≤ XLK m) : 0 ≤ STbootRHS lo XL XLK B n_ p := by
  unfold STbootRHS
  refine add_nonneg ?_ ?_
  · exact mul_nonneg (mul_nonneg (Real.rpow_nonneg hB _) (Real.rpow_nonneg (hXL _) _))
      (Real.rpow_nonneg (hXL _) _)
  · refine add_nonneg (add_nonneg (Finset.sum_nonneg fun m _ => hXLK m)
      (Finset.sum_nonneg fun m _ => hXL m)) (Finset.sum_nonneg fun m _ => ?_)
    exact mul_nonneg (hXLK _) (Real.rpow_nonneg (mul_nonneg (hXL _) (hXL _)) _)

/-- **The merged pin implies the primed one** (`T2186_stNQConcl'_of_stNQConcl`): the hypotheses of `STNQConcl'`
contain those of `STNQConcl` (`m + 1 ≤ n_ ⇒ m ≤ n_`); the hypothesis at `m = n_` is one event on which
`Ξ̂^{𝓛-𝒦}_{w,n_} ≤ N^{τ/2} XLK n_ n u` for all `s_n ≤ w ≤ u` (the union over `(w,u)` is inside `P`), so
`STsupXiLK … (s n) u n_ ≤ N^{τ/2} XLK n_ n u` there (`Real.iSup_le`); then
`X ≤ N^{τ/2}(B^{1/6} sup + R) ≤ N^τ (B^{1/6} XLK + R)` (`B ≥ 0`, `R = STbootRHS 2 … ≥ 0` need `u ≤ t_n < 1`);
the failure probabilities add (`StochDomAt.of_subset_union`, `2 N^{-(D+1)} ≤ N^{-D}` by `SizeTendsto`).
Private: a public theorem with `STNQConcl` in a binder would make the registry scan (`Test/Axioms.lean`)
report `STNQConcl` as an unregistered premise (no theorem concludes it). -/
private theorem stNQConcl'_of_stNQConcl (sz : Sizes d) (E s t : ℕ → ℝ) (hsz : sz.SizeTendsto)
    (ht1 : ∀ n, t n < 1) (h : STNQConcl sz E s t) : STNQConcl' sz E s t := by
  intro n_ p hn hp XL XLK hXL hXLK hXLp hXLKp
  have hold := h n_ p hn hp XL XLK hXL hXLK hXLp (fun m hm1 hm2 => hXLKp m hm1 (by omega))
  have hhyp := hXLKp n_ (by omega) le_rfl
  refine StochDomAt.of_subset_union (tendsto_size sz hsz) hold hhyp
    (fun τ hτ => ⟨τ / 2, half_pos hτ, Eventually.of_forall fun n => ?_⟩)
  intro ω hω
  obtain ⟨q, hq⟩ := hω
  by_contra hno
  simp only [Set.mem_union, badSetAt, Set.mem_ofPred_eq, not_or, not_exists, not_lt] at hno
  obtain ⟨hno1, hno2⟩ := hno
  have hu1 : ((q.1 : ℝ)) < 1 := (q.1.2.2).trans_lt (ht1 n)
  have hB : 0 < sz.Bctl n (q.1 : ℝ) := st_Bctl_pos sz hu1
  have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
  have hNh1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) := Real.one_le_rpow hN1 (half_pos hτ).le
  have hsq : ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * ((sz.size n : ℕ) : ℝ) ^ (τ / 2) =
      ((sz.size n : ℕ) : ℝ) ^ τ := UnifDetDom.rpow_half_mul_rpow_half _ hτ
  have hx0 : 0 ≤ XLK n_ n (q.1 : ℝ) := zero_le_one.trans (hXLK _ _ _)
  have hR0 : 0 ≤ STbootRHS 2 (fun m => XL m n (q.1 : ℝ)) (fun m => XLK m n (q.1 : ℝ))
      (sz.Bctl n (q.1 : ℝ)) n_ p :=
    stP_bootRHS_nonneg hB.le (fun m => zero_le_one.trans (hXL _ _ _))
      (fun m => zero_le_one.trans (hXLK _ _ _))
  have hb6 : 0 ≤ (sz.Bctl n (q.1 : ℝ)) ^ (1 / 6 : ℝ) := Real.rpow_nonneg hB.le _
  have hsup : STsupXiLK sz n (E n) (s n) (q.1 : ℝ) n_ ω ≤
      ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * XLK n_ n (q.1 : ℝ) := by
    refine Real.iSup_le (fun w => ?_) (mul_nonneg (by linarith) hx0)
    exact hno2 ⟨((w : ℝ), (q.1 : ℝ)), w.2.1, w.2.2, q.1.2.2⟩
  have h1 := hno1 q
  have h2 : ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * ((sz.Bctl n (q.1 : ℝ)) ^ (1 / 6 : ℝ) *
      STsupXiLK sz n (E n) (s n) (q.1 : ℝ) n_ ω + STbootRHS 2 (fun m => XL m n (q.1 : ℝ))
        (fun m => XLK m n (q.1 : ℝ)) (sz.Bctl n (q.1 : ℝ)) n_ p) ≤
      ((sz.size n : ℕ) : ℝ) ^ τ * ((sz.Bctl n (q.1 : ℝ)) ^ (1 / 6 : ℝ) * XLK n_ n (q.1 : ℝ) +
        STbootRHS 2 (fun m => XL m n (q.1 : ℝ)) (fun m => XLK m n (q.1 : ℝ))
          (sz.Bctl n (q.1 : ℝ)) n_ p) := by
    set Nh : ℝ := ((sz.size n : ℕ) : ℝ) ^ (τ / 2) with hNh
    set b6 : ℝ := (sz.Bctl n (q.1 : ℝ)) ^ (1 / 6 : ℝ) with hb6def
    set R : ℝ := STbootRHS 2 (fun m => XL m n (q.1 : ℝ)) (fun m => XLK m n (q.1 : ℝ))
      (sz.Bctl n (q.1 : ℝ)) n_ p with hRdef
    set x : ℝ := XLK n_ n (q.1 : ℝ) with hxdef
    set S : ℝ := STsupXiLK sz n (E n) (s n) (q.1 : ℝ) n_ ω with hSdef
    rw [← hsq]
    have e1 : b6 * S ≤ b6 * (Nh * x) := mul_le_mul_of_nonneg_left hsup hb6
    have e2 : Nh * (b6 * S + R) ≤ Nh * (b6 * (Nh * x) + R) :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    have e3 : Nh * R ≤ Nh * Nh * R := by
      have : 0 ≤ Nh * R * (Nh - 1) := mul_nonneg (mul_nonneg (by linarith) hR0) (by linarith)
      nlinarith
    nlinarith [e2, e3]
  linarith

/-- The statement pinned by the ticket for the private implication (`T2186_stNQConcl'_of_stNQConcl`,
check file section 4): the theorem above has exactly this type. -/
example : ∀ {d : ℕ} (sz : Sizes d) (E s t : ℕ → ℝ), sz.SizeTendsto → (∀ n, t n < 1) →
    STNQConcl sz E s t → STNQConcl' sz E s t := @stNQConcl'_of_stNQConcl

/-- **`lem:STOeq_NQ` implies its primed form** (`T2186_stOeqNQ'_of_stOeqNQ`): unfold `STIngR`, keep `𝔠_d`, and
apply `stNQConcl'_of_stNQConcl` with `SizeTendsto` from `Admissible` (`hflow.1`) and `t_n < 1` from
`t_n ≤ lemT z_n < 1` (`lemT_lt_one`; the imaginary part of `z_n` is positive by the flow condition). -/
theorem stOeqNQ'_of_stOeqNQ : ∀ d : ℕ, STOeqNQ d → STOeqNQ' d := by
  intro d h hd κ ε 𝔡 hκ hε h𝔡 Cd hCd
  obtain ⟨𝔠d, h𝔠d0, h𝔠d1, H⟩ := h hd κ ε 𝔡 hκ hε h𝔡 Cd hCd
  refine ⟨𝔠d, h𝔠d0, h𝔠d1, ?_⟩
  intro 𝔠 sz z hflow s t hs hst ht hR hK hKw hLK hcon hStep2
  have hold := H 𝔠 sz z hflow s t hs hst ht hR hK hKw hLK hcon hStep2
  have him : ∀ n, 0 < (z n).im := fun n =>
    lt_of_lt_of_le (Real.rpow_pos_of_pos (by exact_mod_cast sz.one_le_size n) _)
      (hflow.2 n).2.1
  have ht1 : ∀ n, t n < 1 := fun n => (ht n).trans_lt (lemT_lt_one (him n))
  exact stNQConcl'_of_stNQConcl sz (STflowE z) s t hflow.1.2.2.1 ht1 hold

end Implication

end RBM.Gauss.Sizes

/-! ## 3. The instance of the primed pin

The common shape of the instances of the ingredient pins (`inst_ing`, `Step34Pins.lean:895`) at the merged
data `(sz0, z0, s ≡ 0, t ≡ 1/16)`, case (i): the copy of `inst_OeqNQ` (`Step34Pins.lean:994`) with
`STOeqNQ'`, `STNQConcl'`. -/

namespace RBM.Gauss.Step34PInst

open RBM RBM.Gauss RBM.Gauss.Sizes RBM.Gauss.SizesInst RBM.Gauss.InductionDefsInst RBM.Path Filter
  RBM.Gauss.Step34Inst

/-- `lem:STOeq_NQ`, primed (case (i)) at `(sz0, z0, 0, 1/16)`. -/
theorem inst_OeqNQ' (h : STOeqNQ' 3) (Cd : ℝ) (hCd : 0 < Cd) :
    InstIngConcl (fun sz E s t => STNQConcl' sz E s t) sz0 z0 sInst tInst Cd :=
  inst_ing STCaseI (fun sz E s t => STNQConcl' sz E s t) h sz0 z0 flow_z0 sInst tInst sz0_hs0 sz0_hst
    sz0_ht sz0_caseI sz0_con Cd hCd

/-- **Compiled nonempty instance** (CLAUDE.md §4 step 2): the merged pin `STOeqNQ 3` (the owed
`lem:STOeq_NQ`, a hypothesis of the example) gives the primed pin by `stOeqNQ'_of_stOeqNQ`, which is applied at
the merged data `sz0, z0` (`d = 3`; at `n = 0`: `L = 4`, `W = 32`, `N = 2097152`; window `[0, 1/16]`,
`C_d = 1`): the premises
`STKbound`, `STKward`, `STLK`, `STStep2Concl` of `STIngR` are other gates' pins and stay hypotheses; every
deterministic hypothesis (`3 ≤ d`, the flow, `0 ≤ s < t ≤ lemT z`, the regime `STCaseI`, `(con_st_ind)`,
`C_d > 0`) is discharged by `inst_ing`. -/
example (h : STOeqNQ 3) : InstIngConcl (fun sz E s t => STNQConcl' sz E s t) sz0 z0 sInst tInst 1 :=
  inst_OeqNQ' (stOeqNQ'_of_stOeqNQ 3 h) 1 one_pos

/-- The same with the conclusion applied: at the data, the stochastic premises of the pin being given, the primed
conclusion `STNQConcl'` holds for `(sz0, E = STflowE z0, s, t)`. -/
example (h : STOeqNQ 3) (hKb : STKbound sz0 (STflowE z0)) (hKw : STKward sz0 (STflowE z0))
    (hLK : STLK sz0 (STflowE z0) sInst) (hStep2 : STStep2Concl sz0 (STflowE z0) sInst tInst 1) :
    STNQConcl' sz0 (STflowE z0) sInst tInst := by
  obtain ⟨𝔠d, -, -, hC⟩ := inst_OeqNQ' (stOeqNQ'_of_stOeqNQ 3 h) 1 one_pos
  exact hC hKb hKw hLK hStep2

/-- **The private implication at the data** (`sz0`, `E = STflowE z0`, `s ≡ 0`, `t ≡ 1/16`): `SizeTendsto` (`sz0_tendsto`)
and `t_n < 1` are discharged; the merged conclusion `STNQConcl` (the owed `lem:STOeq_NQ`) is the hypothesis. -/
example (h : STNQConcl sz0 (STflowE z0) sInst tInst) : STNQConcl' sz0 (STflowE z0) sInst tInst :=
  stNQConcl'_of_stNQConcl sz0 (STflowE z0) sInst tInst sz0_tendsto
    (fun n => by simp only [tInst]; norm_num) h

end RBM.Gauss.Step34PInst

end

#print axioms RBM.Gauss.Sizes.STNQConcl'
#print axioms RBM.Gauss.Sizes.STOeqNQ'
#print axioms RBM.Gauss.Sizes.stOeqNQ'_of_stOeqNQ
#print axioms RBM.Gauss.Step34PInst.inst_OeqNQ'
