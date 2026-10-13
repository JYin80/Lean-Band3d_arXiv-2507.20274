/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Graph.LWMomentExp
import RBM3D.Graph.AuxGraphRooted
import RBM3D.Graph.BAMomentGenB
import RBM3D.Graph.BAProvB
import RBM3D.Graph.BALocReg2B
import RBM3D.Graph.BAExp14d
import RBM3D.Graph.BAAtom2
import RBM3D.Graph.BASizeClaim2

set_option linter.style.header false
set_option linter.style.longLine false
set_option linter.style.setOption false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.flexible false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedSimpArgs false

/-!
# BA-L L3d2b-1 (T2483), part A: the carrier, the pin, the weighted lemmas and the rooted G3

Paper: arXiv:2507.20274, `paper/tex/7_8_light_weight.tex` (cited `7_8:line`): `lem:LW_moment_exp` (`7_8:78-83`), its proof (`7_8:1595-1660`, the domains
`7_8:1603-1611`); `paper/tex/B_graphical_lemmas.tex:486-497` (G3, G4).  Twin of `Graph/LWMomentExp.lean` §1-§4 (`:28-460`) and of
`Graph/AuxGraphRooted.lean` (`:1-569`) in a new file (namespace `RBM.BA`, private stem `BAMomentExpGen_`); additive, no merged file is edited.  The second
half (regime (A), the weighted expansion, the far and near pins, the assembly; targets 6-10) is `Graph/BAMomentExpGenB.lean` (ticket T2483, split).

## Contents

1. The carrier `LWfgD` (target 1): the `β`-sum of `f_{xy}` over a carrier restricted to the blocks `[β] ∈ Dm`; (a) the band bridge, (b) `Dm = univ`, (c)
   additivity over disjoint domains, (d) the bridge to the data-level `fxyValD`, (e) the exact three-way split `LWfg_split`.
2. The generic pin `LWMomentExpG` (target 2) in the `PinFam` shape, its band bridge `LWMomentExp_iff_bandPin`, the BA reading `BALWMomentExp`.
3. `baLWMomentOfAnp_closed` (target 3): T2470's target 4 without the path binder (`baPathBinder_holds`).
4. The weighted lemmas (target 4): (a) `BAMomentExp_valW_scale`; (b) the `L¹` form, the claim `size` and the packed claim for a real weight `|Wt| ≤ 1`; (c) the
   weighted scale-mole tail `BAMomentExp_scalemole`; (d) the weight `BAMomentExp_wt` over `BAProvOut.π` and the roots `BAMomentExpGen_rep`.
5. The BA rooted G3 (target 5): the atom-first forest with prescribed roots `BAMomentExpGen_exists_forest` (a copy of `BAGraph.exists_forest`,
   `Graph/BASizeClaim.lean:727`, with `rep` in place of `choose`), the rooted `BAMomentExpGen_sum_J`, the restricted main sum `BAMomentExpGen_main_sum`, the
   deterministic `BAMomentExpGen_G3Rooted`, the pin `BAGtoAGTRooted` and `baGtoAGTRooted_holds` (constants of `BAMomentGen_consts`).
6. Compiled nonempty instances of targets 1-3 (`sz0`, `flow_sz0`, `zSeq`, `t ≡ 1/2`).
7. Compiled nonempty instances of targets 4 and 5 (the flow point `g0P, EP, t0P, m0P`, a start partition term of `fxyPowGraph 2`, `Dm = {0}`).

**No twin of `LWAuxNestedOwnOn`.**  The merged `lwAuxNestedOwnOn_holds` (`Graph/AuxGraphRooted.lean:457`) applies at `BAShadowPG Q` (`Graph/BAAtom.lean:139`), whose graph
is the shadow `Q.g.shadow`: its `auxValOn` is the `auxValOn Q.g.shadow` of target 5, its premise `(BAShadowPG Q).LocReg345 p` comes from `baLocRegConcl_upto5`.
**Premise scan** (`Test/Axioms.lean`): `LWAssmExpgL` occurs only inside the statement def `LWMomentExpG`; `BAAnpAuxG` does not occur (it enters in part B, as the antecedent
of `BALWMomentExpOfAnp`); no theorem here assumes a `Prop`-valued definition that no theorem proves.
-/

open MeasureTheory Filter Matrix

noncomputable section

namespace RBM.BA

open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes RBM.Graph

/-! ## 1. The carrier `f_{xy}` with the sum over `β` restricted to a domain (target 1) -/

/-- **The carrier `f^{D}_{xy}`** (`7_8:1607-1611`, `f^{>ℓ}`, `f^{≤ℓ}`) over a carrier `C : FlowFM sz`: the sum over `β` restricted to the blocks `[β] ∈ Dm`
(twin of `LWfD`, `Graph/LWProv.lean:190`, over a carrier, as `LWfg`, `Graph/BAMomentGen.lean:71`); `Dm = univ` is `LWfg`. -/
def LWfgD {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (n : ℕ) (t : ℝ) (ω : sz.SeqΩ) (Dm : Finset (Zd d (sz.L n)))
    (x y : Idx d (sz.L n) (sz.W n)) : ℂ :=
  ∑ α, if α = x ∨ α = y then (0 : ℂ) else
    ∑ β, if STblk sz n β ∈ Dm then
      ((((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * C.S n (STblk sz n α) (STblk sz n β)) * C.GM n t ω β β * C.G n t ω x α * C.G n t ω α y
    else 0

/-- **Target 1 (a)**: at the band carrier `LWfgD` is the merged `LWfD` (route of `LWfg_bandFM`, `Graph/BAMomentGen.lean:77`). -/
theorem LWfgD_bandFM {d : ℕ} (sz : Sizes d) (E : ℕ → ℝ) (n : ℕ) (t : ℝ) (ω : sz.SeqΩ) (Dm : Finset (Zd d (sz.L n)))
    (x y : Idx d (sz.L n) (sz.W n)) :
    LWfgD (bandFM sz E) n t ω Dm x y = LWfD sz n (E n) t ω Dm x y := by
  unfold LWfgD LWfD
  refine Finset.sum_congr rfl fun α _ => ?_
  split_ifs
  · rfl
  refine Finset.sum_congr rfl fun β _ => ?_
  split_ifs
  · have h : ((((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * (bandFM sz E).S n (STblk sz n α) (STblk sz n β)) = (LWS sz n α β : ℂ) := by
      simp only [bandFM, LWS, svarF, SB_eq_map_SBR, Matrix.map_apply, STblk]
      push_cast
      rfl
    rw [h]
    rfl
  · rfl

/-- **Target 1 (b)**: at `Dm = univ` the domain form is the carrier `LWfg`. -/
theorem LWfgD_univ {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (n : ℕ) (t : ℝ) (ω : sz.SeqΩ) (x y : Idx d (sz.L n) (sz.W n)) :
    LWfgD C n t ω Finset.univ x y = LWfg C n t ω x y := by
  simp [LWfgD, LWfg]

/-- **Target 1 (c)**: the domain form is additive over disjoint domains (twin of `LWfD_union`, `Graph/LWProv.lean:196`). -/
theorem LWfgD_union {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (n : ℕ) (t : ℝ) (ω : sz.SeqΩ) {D₁ D₂ : Finset (Zd d (sz.L n))}
    (h : Disjoint D₁ D₂) (x y : Idx d (sz.L n) (sz.W n)) :
    LWfgD C n t ω (D₁ ∪ D₂) x y = LWfgD C n t ω D₁ x y + LWfgD C n t ω D₂ x y := by
  unfold LWfgD
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun α _ => ?_
  split_ifs with hα
  · simp
  · rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun β _ => ?_
    by_cases h1 : STblk sz n β ∈ D₁
    · simp [h1, Finset.disjoint_left.1 h h1]
    · by_cases h2 : STblk sz n β ∈ D₂ <;> simp [h1, h2]

/-- **Target 1 (d)** (twin of `LWfg_baFMz`, `Graph/BAMomentGen.lean:93`, to `fxyValD`, `Graph/BAProv.lean:678`): at the block Anderson carrier, `t` times the
domain form is the data-level `fxyValD` at `BAlwData` of the slice of the sample. -/
theorem LWfgD_baFMz {d : ℕ} (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ) (t : ℝ) (ω : sz.SeqΩ) (Dm : Finset (Zd d (sz.L n)))
    (x y : Idx d (sz.L n) (sz.W n)) :
    (t : ℂ) * LWfgD (baFMz sz z) n t ω Dm x y =
      fxyValD (BAlwData d (sz.L n) (sz.W n) (BAflowLam0 sz z n) (BAflowEs sz z n) t
        (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) (BAExp14a_slc sz n ω)).toLData Dm x y := by
  unfold LWfgD fxyValD
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  split_ifs
  · simp
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun β _ => ?_
  by_cases hβ : STblk sz n β ∈ Dm
  · have hβ' : (split d (sz.L n) (sz.W n) β).1 ∈ Dm := hβ
    simp only [hβ, hβ', ite_true]
    have hS : (BAlwData d (sz.L n) (sz.W n) (BAflowLam0 sz z n) (BAflowEs sz z n) t
          (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) (BAExp14a_slc sz n ω)).toLData.S α β =
        (t : ℂ) * ((((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * (baFMz sz z).S n (STblk sz n α) (STblk sz n β)) := by
      change BAlwS d (sz.L n) (sz.W n) t α β = _
      rw [BAExp14a_S_apply]
      simp only [baFMz, baFM, STblk, Matrix.one_apply]
    rw [hS]
    change (t : ℂ) * ((((((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * (baFMz sz z).S n (STblk sz n α) (STblk sz n β)) * (baFMz sz z).GM n t ω β β *
        (baFMz sz z).G n t ω x α * (baFMz sz z).G n t ω α y)) =
      (t : ℂ) * ((((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * (baFMz sz z).S n (STblk sz n α) (STblk sz n β)) *
        ((baFMz sz z).G n t ω β β - (baFMz sz z).M n β β) * (baFMz sz z).G n t ω x α * (baFMz sz z).G n t ω α y
    unfold FlowFM.GM
    ring
  · have hβ' : ¬ (split d (sz.L n) (sz.W n) β).1 ∈ Dm := hβ
    simp [hβ, hβ']

/-- **Target 1 (e)** (twin of `LWf_split`, `Graph/LWMomentExp.lean:68`; `dom_union`, `dom_disj` imported): `f = f^{>} + f^{(a)} + f^{(b)}` exactly, `a = [x]`, `b = [y]`,
over a carrier. -/
theorem LWfg_split {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (n : ℕ) (t ℓ : ℝ) (ω : sz.SeqΩ) (x y : Idx d (sz.L n) (sz.W n)) :
    LWfg C n t ω x y =
      LWfgD C n t ω (domFar d (sz.L n) (STblk sz n x) (STblk sz n y) ℓ) x y +
      LWfgD C n t ω (domNearA d (sz.L n) (STblk sz n x) ℓ) x y +
      LWfgD C n t ω (domNearB d (sz.L n) (STblk sz n x) (STblk sz n y) ℓ) x y := by
  rw [← LWfgD_union C n t ω (dom_disj _ _ ℓ).1, ← LWfgD_union C n t ω (dom_disj _ _ ℓ).2, dom_union, LWfgD_univ]

/-! ## 2. The generic pin `LWMomentExpG` (target 2) -/

/-- **`lem:LW_moment_exp`** (`7_8:78-83`; `Graph/LWPins.lean:341`) over a carrier family, in the `PinFam` shape of `LWtermExpG` (`Chain/LWGen.lean:93`):
`STFlow` becomes `Flow`, `lemT` becomes `T0`, `LWAssmExp` becomes `LWAssmExpgL (mk sz z) (law sz)`, `Prec` becomes `PrecL sz (law sz)`, `LWf` becomes the
carrier `f_{xy}` `LWfg (mk sz z)`, `η_t` becomes `(mk sz z).eta`; the rest is verbatim. -/
def LWMomentExpG (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ)
    (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop)
    (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz) (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ (p : ℕ), 2 ∣ p →
      ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), Flow sz κ ε 𝔠 𝔡 z →
        ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ T0 sz z n) →
          ∀ (ε₀ : ℝ) (Ψ ℓ : ℕ → ℝ), LWAssmExpgL (mk sz z) (law sz) t ε₀ Ψ ℓ →
            ∀ D : ℝ, 0 < D →
              PrecL sz (law sz) (U := fun n => {_q : Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n) //
                  sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 < 1 - t n})
                (fun n q _ => ∫ ω, ‖LWfg (mk sz z) n (t n) ω q.1.1 q.1.2‖ ^ p ∂(law sz))
                (fun n q _ => (((mk sz z).eta n (t n))⁻¹ * (sz.Bctl n (t n)) ^ (1 / 2 : ℝ) *
                  sfT d (sz.L n) ((sz.W n : ℕ) : ℝ) (sz.lam n) (t n)
                    (min ((zdistInf d (sz.L n) (STblk sz n q.1.1 - STblk sz n q.1.2) : ℕ) : ℝ) (ℓ n))) ^ p +
                  ((sz.W n : ℕ) : ℝ) ^ (-D))

/-- **Target 2**: the band instance of the generic pin is the merged `LWMomentExp` (a result through target 1 and `LWfg_bandFM`, not definitional;
`LWAssmExp`, `Prec`, `η_t` are `LWAssmExpgL`, `PrecL`, `eta` at the band carrier, as in `LWtermExp_iff`, `Chain/LWGen.lean:143`). -/
theorem LWMomentExp_iff_bandPin (d : ℕ) : RBM.Gauss.Sizes.LWMomentExp d ↔ bandPin LWMomentExpG d := by
  unfold RBM.Gauss.Sizes.LWMomentExp bandPin LWMomentExpG
  simp only [LWfg_bandFM]
  exact Iff.rfl

/-- **Target 2**: the block Anderson reading (law `seqP (sz.withLam 0)`, `BAFlow`, `baFMz`, `BAflowT0`), beside `BALWMoment` (`Graph/BAMomentGen.lean:146`)
and `BALWtermExp` (`BA/LWPinsBA.lean:47`). -/
abbrev BALWMomentExp : ℕ → Prop := baPin LWMomentExpG

/-! ## 3. The path binder concluded (target 3) -/

/-- **Target 3** (supervisor 2246 L40-F2): `baLWMoment_of_anp` (`Graph/BAMomentGenB.lean:370`) without the path binder, which T2469 concludes
(`baPathBinder_holds`, `Graph/BALocReg2B.lean:338`).  After it no public statement of stage L carries the path binder. -/
theorem baLWMomentOfAnp_closed : ∀ d : ℕ, BALWMomentOfAnp d := baLWMoment_of_anp baPathBinder_holds

/-! ## 4. The weighted lemmas (target 4; band `Graph/LWMomentExp.lean` §3, §4) -/

section Weighted

open private BASizeClaim_term_le BASizeClaim_sum_le BASizeClaim_size_alg BASizeClaim_sizeConst_nonneg from RBM3D.Graph.BASizeClaim2
open private BAExp14d_term_scale from RBM3D.Graph.BAExp14d

/-- **Target 4 (a)** (`T2483_ValWScale`; band `lwMomentExp_pvalW_smul`, `Graph/LWMomentExp.lean:266`; the weighted form of `BAExp14d_val_scale`, `Graph/BAExp14d.lean:111`):
for every real weight, every waved factor of `BAlwData` is `t` times that of `BAExp14d_dataT`, so the weighted packed value is `t^{n_W}` times its
value at the rescaled data (`BAReal`, `0 ≤ t < 1`; `t = 0` included). -/
theorem BAMomentExp_valW_scale : ∀ (d L W : ℕ) [NeZero L] [NeZero W], 3 ≤ L → ∀ (g0 κ E t : ℝ) (m : ℂ), BAReal d L g0 κ E m → 0 ≤ t → t < 1 →
    ∀ (ω : Ω d L W) (P : BAPGraph (Fin 2)) (Wt : (P.E' ⊕ P.I' → Idx d L W) → ℝ) (ℓ : Fin 2 → Idx d L W),
      P.valW (BAlwData d L W g0 E t m ω) Wt ℓ = (t : ℂ) ^ P.g.nW * P.valW (BAExp14d_dataT d L W g0 E t m ω) Wt ℓ := by
  intro d L W _ _ hL g0 κ E t m hr ht0 ht1 ω P Wt ℓ
  have hsp := baSp_eq d L W hL g0 κ E t m hr ht0 ht1
  have hSp : ∀ x y, (BAlwData d L W g0 E t m ω).Sp x y = (t : ℂ) * (BAExp14d_dataT d L W g0 E t m ω).Sp x y := fun x y => by
    have := congrFun (congrFun hsp x) y
    simp only [BAlwData, BAExp14d_dataT, this, Matrix.smul_apply, smul_eq_mul]
  have hS : ∀ x y, (BAlwData d L W g0 E t m ω).S x y = (t : ℂ) * (BAExp14d_dataT d L W g0 E t m ω).S x y := fun x y => by
    simp only [BAlwData, BAExp14d_dataT, Matrix.of_apply, BAlwS]
  unfold BAPGraph.valW
  split_ifs with h
  · unfold BAGraph.valW
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun ℓi _ => ?_
    rw [BAExp14d_term_scale P.g _ _ t hS hSp rfl rfl rfl _]
    ring
  · simp

variable {d L W : ℕ} [NeZero L] [NeZero W] {ι : Type} [Fintype ι] [DecidableEq ι] {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

/-- For a real weight `|Wt| ≤ 1` the weighted value is bounded by the `L¹` sum of the terms (the first step of `lwMomentExp_valW_norm_le`,
`Graph/LWMomentExp.lean:297-301`). -/
theorem BAMomentExpGen_valW_le_sum (Γ : BAGraph E I) (D : BALData ι) (Wt : (E ⊕ I → ι) → ℝ) (hWt : ∀ ℓ, |Wt ℓ| ≤ 1) (ℓe : E → ι) :
    ‖Γ.valW D Wt ℓe‖ ≤ ∑ ℓi : I → ι, ‖Γ.term D (Sum.elim ℓe ℓi)‖ := by
  unfold BAGraph.valW
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun ℓi _ => ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_of_le_one_left (norm_nonneg _) (hWt _)

/-- **Target 4 (b), the weighted `L¹` form of `claim:size`** (twin of `lwMomentExp_valW_norm_le`, `Graph/LWMomentExp.lean:289`, of `BASizeClaim_val_le`,
`Graph/BASizeClaim2.lean:420`): `|Wt| ≤ 1` costs nothing.  No `hM : M = m I`. -/
theorem BAMomentExp_valW_norm_le [Nonempty ι] (Γ : BAGraph E I) (hN : Γ.Normal) (D : BALData ι) {Ψ a K₁ Kd : ℝ}
    (hG : ∀ x y, ‖D.G x y - D.M x y‖ ≤ Ψ) (hS : LWKBound D.S a K₁) (hSp : LWKBound D.Sp a K₁)
    (hM : LWKBound D.M Kd Kd) (hP : LWKBound D.gPsi Kd Kd) (ℓe : E → ι) (Wt : (E ⊕ I → ι) → ℝ) (hWt : ∀ ℓ, |Wt ℓ| ≤ 1) :
    ‖Γ.valW D Wt ℓe‖ ≤ ‖Γ.coeff‖ * Ψ ^ Γ.nS *
      ((Fintype.card ι : ℝ) ^ Γ.nM * K₁ ^ (Γ.nA - Γ.nM) * a ^ (Γ.nW - (Γ.nA - Γ.nM)) * Kd ^ (Γ.mdot.length + Γ.psi.length)) := by
  obtain ⟨x0⟩ := ‹Nonempty ι›
  have hΨ : 0 ≤ Ψ := (norm_nonneg _).trans (hG x0 x0)
  calc ‖Γ.valW D Wt ℓe‖ ≤ ∑ ℓi : I → ι, ‖Γ.term D (Sum.elim ℓe ℓi)‖ := BAMomentExpGen_valW_le_sum Γ D Wt hWt ℓe
    _ ≤ ∑ ℓi : I → ι, ‖Γ.coeff‖ * Ψ ^ Γ.nS *
        ((Γ.waved.map fun e => ‖WEdge.val D.toLData (Sum.elim ℓe ℓi) e‖).prod *
          (Γ.psi.map fun e => ‖BAPsiEdge.val D (Sum.elim ℓe ℓi) e‖).prod *
          (Γ.mdot.map fun e => ‖BAMEdge.val D (Sum.elim ℓe ℓi) e‖).prod) :=
        Finset.sum_le_sum fun ℓi _ => BASizeClaim_term_le Γ hN D hΨ hG _
    _ = ‖Γ.coeff‖ * Ψ ^ Γ.nS * ∑ ℓi : I → ι,
        ((Γ.waved.map fun e => ‖WEdge.val D.toLData (Sum.elim ℓe ℓi) e‖).prod *
          (Γ.psi.map fun e => ‖BAPsiEdge.val D (Sum.elim ℓe ℓi) e‖).prod *
          (Γ.mdot.map fun e => ‖BAMEdge.val D (Sum.elim ℓe ℓi) e‖).prod) := by
        rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (BASizeClaim_sum_le Γ hN D hS hSp hM hP ℓe)
          (mul_nonneg (norm_nonneg _) (pow_nonneg hΨ _))

/-- **Target 4 (b), the weighted `claim:size` at BA** (twin of `lwMomentExp_claimSize`, `Graph/LWMomentExp.lean:322`, of `baClaimSize`,
`Graph/BASizeClaim2.lean:473`): `|valW Γ| ≤ C_Γ size(Γ)` for `|Wt| ≤ 1`, `C_Γ = Γ.sizeConst K₀ K₁ Kd`; the constants of the BA model are those of
`baClaimSize_E` (`Graph/BASizeClaim2.lean:566`). -/
theorem BAMomentExp_claimSize (Γ : BAGraph E I) (hN : Γ.Normal) (D : BALData (Idx d L W))
    {Ψ K₀ K₁ Kd : ℝ} (hG : ∀ x y, ‖D.G x y - D.M x y‖ ≤ Ψ) (hS : LWKBound D.S (K₀ * ((W : ℝ) ^ d)⁻¹) K₁)
    (hSp : LWKBound D.Sp (K₀ * ((W : ℝ) ^ d)⁻¹) K₁) (hM : LWKBound D.M Kd Kd) (hP : LWKBound D.gPsi Kd Kd) (ℓe : E → Idx d L W)
    (Wt : (E ⊕ I → Idx d L W) → ℝ) (hWt : ∀ ℓ, |Wt ℓ| ≤ 1) :
    ‖Γ.valW D Wt ℓe‖ ≤ Γ.sizeConst K₀ K₁ Kd * Γ.scalingSize Ψ W d L := by
  have : Nonempty (Idx d L W) := ⟨fun _ => 0⟩
  have hb := BAMomentExp_valW_norm_le Γ hN D hG hS hSp hM hP ℓe Wt hWt
  have hW : (W : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne W)
  obtain ⟨h1, h2⟩ := Γ.counters_le hN.1
  have hcard : (Fintype.card (Idx d L W) : ℝ) = ((((W * L) ^ d : ℕ)) : ℝ) := by rw [RBM.Gauss.card_Idx]
  rw [hcard] at hb
  refine hb.trans (le_of_eq ?_)
  have hal := BASizeClaim_size_alg W d L Γ.nM Γ.nA Γ.nW hW h1 h2 K₀
  unfold BAGraph.sizeConst BAGraph.scalingSize Counters.scalingSize
  change ‖Γ.coeff‖ * Ψ ^ Γ.nS * ((((W * L) ^ d : ℕ) : ℝ) ^ Γ.nM * K₁ ^ (Γ.nA - Γ.nM) *
      (K₀ * ((W : ℝ) ^ d)⁻¹) ^ (Γ.nW - (Γ.nA - Γ.nM)) * Kd ^ (Γ.mdot.length + Γ.psi.length)) = _
  calc ‖Γ.coeff‖ * Ψ ^ Γ.nS * ((((W * L) ^ d : ℕ) : ℝ) ^ Γ.nM * K₁ ^ (Γ.nA - Γ.nM) *
        (K₀ * ((W : ℝ) ^ d)⁻¹) ^ (Γ.nW - (Γ.nA - Γ.nM)) * Kd ^ (Γ.mdot.length + Γ.psi.length))
      = ‖Γ.coeff‖ * Ψ ^ Γ.nS * K₁ ^ (Γ.nA - Γ.nM) * Kd ^ (Γ.mdot.length + Γ.psi.length) *
        (((((W * L) ^ d : ℕ) : ℝ)) ^ Γ.nM * (K₀ * ((W : ℝ) ^ d)⁻¹) ^ (Γ.nW - (Γ.nA - Γ.nM))) := by ring
    _ = _ := by rw [hal]; simp only [BAGraph.counters]; ring

/-- **Target 4 (b), the weighted claim for a packed output** (twin of `BAMomentGen_pval_claim`, `Graph/BAMomentGen.lean:444`, with the weight):
`|Q.valW D Wt ℓe| ≤ C_Q size_Ψ(Q)` for `‖G - M‖_max ≤ Ψ` and `|Wt| ≤ 1`. -/
theorem BAMomentExp_pvalW_claim {K₀ K₁ Kd Ψ : ℝ} (Q : BAPGraph (Fin 2)) (hQ : Q.g.Normal)
    (D : BALData (Idx d L W)) (hG : ∀ x y, ‖D.G x y - D.M x y‖ ≤ Ψ) (hS : LWKBound D.S (K₀ * ((W : ℝ) ^ d)⁻¹) K₁)
    (hSp : LWKBound D.Sp (K₀ * ((W : ℝ) ^ d)⁻¹) K₁) (hM : LWKBound D.M Kd Kd) (hP : LWKBound D.gPsi Kd Kd)
    (hK₀ : 0 ≤ K₀) (hK₁ : 0 ≤ K₁) (hKd : 0 ≤ Kd) (ℓe : Fin 2 → Idx d L W)
    (Wt : (Q.E' ⊕ Q.I' → Idx d L W) → ℝ) (hWt : ∀ ℓ, |Wt ℓ| ≤ 1) :
    ‖Q.valW D Wt ℓe‖ ≤ Q.g.sizeConst K₀ K₁ Kd * Q.g.scalingSize Ψ W d L := by
  classical
  by_cases hf : ∃ ℓ' : Q.E' → Idx d L W, ℓe = ℓ' ∘ Q.ext
  · obtain ⟨ℓ', hℓ'⟩ := hf
    rw [BAPGraph.valW_of_factor Q D Wt hℓ']
    exact BAMomentExp_claimSize Q.g hQ D hG hS hSp hM hP ℓ' Wt hWt
  · rw [BAPGraph.valW_of_not Q D Wt hf, norm_zero]
    refine mul_nonneg (BASizeClaim_sizeConst_nonneg Q.g hK₀ hK₁ hKd) ?_
    unfold BAGraph.scalingSize Counters.scalingSize
    have hW : (0 : ℝ) < (W : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne W)
    have hL : (0 : ℝ) < (L : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    have hΨ : 0 ≤ Ψ := (norm_nonneg _).trans (hG (fun _ => 0) (fun _ => 0))
    positivity

/-- **Target 4 (c), the weighted BA scale-mole tail** (twin of `lwMomentExp_scalemole`, `Graph/LWMomentExp.lean:344`; route of `BAMomentGen_scalemole`,
`Graph/BAMomentGen.lean:738`, with `|Wt| ≤ 1`): if the labels of two external vertices of one molecule (`b ∈ Γ.mol a`) are at block distance
`> |E ⊕ I| r`, no labelling is confined, so the tail bound applies to every term.  It covers every output with `𝓜_x = 𝓜_y`, every `x ~ y` among them
(an atom is inside a molecule, `BALocReg1_mol_of_atom`, `Graph/BALocReg1.lean:304`; L4-C4 (b)). -/
theorem BAMomentExp_scalemole (hd : 3 ≤ d) (Γ : BAGraph E I) (hN : Γ.Normal) (D : BALData (Idx d L W))
    {Ψ C c r : ℝ} (hG : ∀ x y, ‖D.G x y - D.M x y‖ ≤ Ψ) (hC : 0 ≤ C) (hc : 0 < c)
    (hSd : ∀ x y, ‖D.S x y‖ ≤ C * ((W : ℝ) ^ d)⁻¹ * Real.exp (-(c * (lwBdist d L W x y : ℝ))))
    (hSpd : ∀ x y, ‖D.Sp x y‖ ≤ C * ((W : ℝ) ^ d)⁻¹ * Real.exp (-(c * (lwBdist d L W x y : ℝ))))
    (hMPd : ∀ x y, ‖D.M x y‖ ≤ C * Real.exp (-(c * (lwBdist d L W x y : ℝ))) ∧
      ‖D.gPsi x y‖ ≤ C * Real.exp (-(c * (lwBdist d L W x y : ℝ))))
    (hoff : ∀ x y, (split d L W x).2 ≠ (split d L W y).2 → D.M x y = 0 ∧ D.gPsi x y = 0) (hr : 0 ≤ r)
    (Wt : (E ⊕ I → Idx d L W) → ℝ) (hWt : ∀ ℓ, |Wt ℓ| ≤ 1)
    (ℓe : E → Idx d L W) (a b : E) (hab : Sum.inl b ∈ Γ.mol (Sum.inl a))
    (hfar : (Fintype.card (E ⊕ I) : ℝ) * r < (lwBdist d L W (ℓe a) (ℓe b) : ℝ)) :
    ‖Γ.valW D Wt ℓe‖ ≤ Real.exp (-(c * r / 2)) * Γ.sizeConst C (C * expC (d - 2) (c / 2)) (C * (1 + expC (d - 2) (c / 2))) *
      Γ.scalingSize Ψ W d L := by
  classical
  have hne : Nonempty (Idx d L W) := ⟨fun _ => 0⟩
  have hΨ : 0 ≤ Ψ := (norm_nonneg _).trans (hG (fun _ => 0) (fun _ => 0))
  have htail := BAAtom_tail_sum (r := r) hd Γ hN D hΨ hC hc hSd hSpd hMPd hoff ℓe
  have hpt : ∀ ℓi : I → Idx d L W, ‖Γ.term D (Sum.elim ℓe ℓi)‖ ≤ ‖Γ.coeff‖ * Ψ ^ Γ.nS *
      (Real.exp (-(c * r / 2)) * ∏ j : Γ.Jx, BAAtom_fJw Γ D c j (Sum.elim ℓe ℓi (Γ.edgeEnds j).1)
        (Sum.elim ℓe ℓi (Γ.edgeEnds j).2)) := by
    intro ℓi
    refine BAAtom_term_tail Γ hN D hG hc _ ?_
    by_contra hcon
    have hconf : ∀ j : Γ.Jx, (lwBdist d L W (Sum.elim ℓe ℓi (Γ.edgeEnds j).1) (Sum.elim ℓe ℓi (Γ.edgeEnds j).2) : ℝ) ≤ r := by
      intro j
      by_contra h
      exact hcon ⟨j, not_le.1 h⟩
    have hsh := BAAtom_shadow_conf Γ (Sum.elim ℓe ℓi) r hconf
    have := auxGraph_mol_dist Γ.shadow hN.1 (Sum.elim ℓe ℓi) hr hsh (u := Sum.inl a) (v := Sum.inl b)
      ((BAAtom_shadow_molOf_eq_iff Γ _ _).2 hab)
    simp only [Sum.elim_inl] at this
    exact absurd hfar (not_lt.2 this)
  exact (BAMomentExpGen_valW_le_sum Γ D Wt hWt ℓe).trans ((Finset.sum_le_sum fun ℓi _ => hpt ℓi).trans htail)

end Weighted

section Expand

variable {d : ℕ} (sz : Sizes d)

/-- **Target 4 (d), the weight of the starting graph pulled back to an output `o` through its provenance map** (twin of `lwMomentExp_wt`,
`Graph/LWMomentExp.lean:379`; no `ev`, no tags): `Π_k 1_{Dm}([ℓ(π β^{(k)})])`, the weight of `BAWExp.prod` (`Graph/BAProv.lean:166`). -/
def BAMomentExp_wt (n : ℕ) (Dm : Finset (Zd d (sz.L n))) {p : ℕ} (o : BAProvOut (baPG (BAGraph.ofLGraph (fxyPowGraph p)))) :
    (o.Q.E' ⊕ o.Q.I' → Idx d (sz.L n) (sz.W n)) → ℝ :=
  fun ℓ => ∏ k : Fin p, if STblk sz n (ℓ (o.π (Sum.inr (localReg_fxyBeta k)))) ∈ Dm then 1 else 0

/-- **Target 4 (d)**: the weight is bounded by `1` (twin of `lwMomentExp_wt_abs`, `Graph/LWMomentExp.lean:382`). -/
theorem BAMomentExp_wt_abs (n : ℕ) (Dm : Finset (Zd d (sz.L n))) {p : ℕ} (o : BAProvOut (baPG (BAGraph.ofLGraph (fxyPowGraph p))))
    (ℓ : o.Q.E' ⊕ o.Q.I' → Idx d (sz.L n) (sz.W n)) : |BAMomentExp_wt sz n Dm o ℓ| ≤ 1 := by
  unfold BAMomentExp_wt
  have h0 : ∀ k ∈ (Finset.univ : Finset (Fin p)), 0 ≤ if STblk sz n (ℓ (o.π (Sum.inr (localReg_fxyBeta k)))) ∈ Dm then (1 : ℝ) else 0 :=
    fun k _ => by split_ifs <;> norm_num
  rw [abs_of_nonneg (Finset.prod_nonneg h0)]
  exact Finset.prod_le_one₀ h0 fun k _ => by split_ifs <;> norm_num

/-- **Target 4 (d), the roots from the coverage** (twin of the private `lwMomentExp_rep`, `Graph/LWMomentExp.lean:1000`; `BACoverBy.rep`, `Graph/BAProv.lean:130`):
every internal molecule of the shadow of an output with `BACoverBy` contains the image `π β^{(k)}` of some initial vertex, an internal vertex carrying the
weight, so the weight vanishes unless the block of every root is in `Dm`. -/
theorem BAMomentExpGen_rep {p : ℕ} (o : BAProvOut (baPG (BAGraph.ofLGraph (fxyPowGraph p))))
    (hcov : BACoverBy (P := o.Q) (fun k : Fin p => o.π (Sum.inr (localReg_fxyBeta k)))) (n : ℕ) (Dm : Finset (Zd d (sz.L n))) :
    ∃ rep : LGraph.AuxIMol o.Q.g.shadow → o.Q.I', (∀ c, o.Q.g.shadow.molOf (Sum.inr (rep c)) = c.1) ∧
      ∀ ℓ : o.Q.E' ⊕ o.Q.I' → Idx d (sz.L n) (sz.W n), BAMomentExp_wt sz n Dm o ℓ ≠ 0 →
        ∀ c, (split d (sz.L n) (sz.W n) (ℓ (Sum.inr (rep c)))).1 ∈ Dm := by
  obtain ⟨rep, k, hk⟩ := hcov.rep
  refine ⟨rep, fun c => (hk c).2, fun ℓ hℓ c => ?_⟩
  have h := Finset.prod_ne_zero_iff.1 hℓ (k c) (Finset.mem_univ _)
  rw [(hk c).1] at h
  by_contra hn
  have hn' : ¬ STblk sz n (ℓ (Sum.inr (rep c))) ∈ Dm := hn
  exact h (by simp [hn'])

end Expand

/-! ## 5. The BA rooted G3 (target 5)

The twin of `LWGtoAGRooted` (`Graph/AuxGraphRooted.lean:225`) at the rescaled kernels of `BAGtoAGT` (`Graph/BAExp14d.lean:269`).  The roots `rep` of the
internal molecules (from `BACoverBy.rep`) are prescribed.  The band forest of `Γ.shadow` (`lwAuxRoot_exists_forest`, `Graph/AuxGraphRooted.lean:62`)
does not give the exponent count: the shadow waved edges are the waved, the `M`-dotted and the `Ψ`-dotted edges (`Graph/BAAtom.lean:65`), so a tree
may use a waved edge where an atom edge exists, whereas the bound `K₁^{n_A - n_M} a^{n_W - (n_A - n_M)}` needs exactly `n_A - n_M` waved tree edges.
Hence a copy of the atom-first forest `BAGraph.exists_forest` (`Graph/BASizeClaim.lean:727-933`) with the prescribed roots, the rooted `BAAtom_sum_J`
(`Graph/BAAtom.lean:896`) and the main sum with the indicator of the root blocks. -/

section Rooted

variable {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

open private BASizeClaim_atomAdj_comm BASizeClaim_wAdj BASizeClaim_adj_cases BASizeClaim_atomAdj_cases BASizeClaim_atom_eq
  BASizeClaim_self_mem_atom BASizeClaim_forest_abs from RBM3D.Graph.BASizeClaim
open private BAAtom_alg_prod from RBM3D.Graph.BAAtom

open Classical in
/-- **The atom-first molecular forest with prescribed roots** (`BAGraph.exists_forest`, `Graph/BASizeClaim.lean:727`, whose proof chooses the roots; here the
roots `rep` are given, one vertex in each internal molecule of the shadow): the children are the internal vertices outside the range of `rep`, a tree
edge of a child is an edge of `J = waved ⊕ mdot ⊕ psi`, and exactly `n_A - n_M` of the tree edges are waved (a gate is the first vertex of an atom
reached by the forest; the `n_M` atoms of the roots have none). -/
theorem BAMomentExpGen_exists_forest (Γ : BAGraph E I) (hD : ∀ e ∈ Γ.dotted, e.eq = false)
    (rep : LGraph.AuxIMol Γ.shadow → I) (hrep : ∀ c, Γ.shadow.molOf (Sum.inr (rep c)) = c.1) :
    ∃ (C : Finset I) (par : I → E ⊕ I) (edge : I → Option Γ.Jx) (ρ : I → ℕ),
      (∀ i, i ∈ C ↔ i ∉ Set.range rep) ∧
      (C.filter fun c => ∃ j, edge c = some (Sum.inl j)).card + Γ.nM = Γ.nA ∧
      (∀ c ∈ C, ∀ w, par c = Sum.inr w → ρ w < ρ c) ∧
      (∀ c ∈ C, ∃ j, edge c = some j ∧
        (((Γ.edgeEnds j).1 = Sum.inr c ∧ (Γ.edgeEnds j).2 = par c) ∨
         ((Γ.edgeEnds j).2 = Sum.inr c ∧ (Γ.edgeEnds j).1 = par c))) ∧
      (∀ c₁ ∈ C, ∀ c₂ ∈ C, edge c₁ = edge c₂ → c₁ = c₂) := by
  have : Fintype (LGraph.AuxIMol Γ.shadow) := Fintype.ofFinite _
  let IAfin : Finset (E ⊕ I) := Finset.univ.filter (fun v : E ⊕ I => ∀ w ∈ Γ.atom v, w.isRight = true)
  have hint : ∀ m : LGraph.AuxIMol Γ.shadow, ∀ w ∈ Γ.mol (Sum.inr (rep m)), w.isRight = true := by
    intro m w hw
    have h1 := (Γ.shadow.forall_mol_isRight_iff (Sum.inr (rep m))).2 (by rw [hrep m]; exact m.2)
    rw [BAGraph.shadow_mol] at h1
    exact h1 w hw
  let T : E ⊕ I → Prop := fun v => v.isLeft = true ∨ ∃ m : LGraph.AuxIMol Γ.shadow, v = Sum.inr (rep m)
  let A : E ⊕ I → E ⊕ I → Prop := fun u v => Γ.atomAdj u v = true
  let Wd : E ⊕ I → E ⊕ I → Prop := fun u v => BASizeClaim_wAdj Γ u v
  have hA : ∀ u v, A u v → A v u := fun u v h => by
    simp only [A] at h ⊢
    rwa [BASizeClaim_atomAdj_comm] at h
  have hreach : ∀ v, ∃ t, T t ∧ Relation.ReflTransGen (fun a b => A a b ∨ Wd a b) v t := by
    intro v
    have hmono : ∀ t, Relation.ReflTransGen (fun a b => Γ.adj a b = true) v t →
        Relation.ReflTransGen (fun a b => A a b ∨ Wd a b) v t := fun t h => by
      refine Relation.ReflTransGen.mono (fun a b hab => ?_) v t h
      rcases BASizeClaim_adj_cases Γ hD hab with h1 | h1
      · exact Or.inr h1
      · exact Or.inl h1
    by_cases hext : ∀ w ∈ Γ.mol v, w.isRight = true
    · have hm : ¬ Γ.shadow.IsExtMol (Γ.shadow.molOf v) :=
        (Γ.shadow.forall_mol_isRight_iff v).1 (by rw [BAGraph.shadow_mol]; exact hext)
      let m : LGraph.AuxIMol Γ.shadow := ⟨Γ.shadow.molOf v, hm⟩
      refine ⟨Sum.inr (rep m), Or.inr ⟨m, rfl⟩, hmono _ ?_⟩
      rw [← BAGraph.mem_mol_iff]
      exact (BAAtom_shadow_molOf_eq_iff Γ v (Sum.inr (rep m))).1 (hrep m).symm
    · push Not at hext
      obtain ⟨w, hw, hwl⟩ := hext
      refine ⟨w, Or.inl ?_, hmono _ ((BAGraph.mem_mol_iff Γ v w).1 hw)⟩
      cases w with
      | inl a => rfl
      | inr b => simp at hwl
  obtain ⟨gate, parA, ρ, hP1, hP2, hP3, hP4, hP5⟩ := BASizeClaim_forest_abs A Wd hA T hreach
  let C : Finset I := Finset.univ.filter (fun c => ¬ T (Sum.inr c))
  have hCmem : ∀ c, c ∈ C ↔ ¬ T (Sum.inr c) := fun c => by simp [C]
  have hgateT : ∀ v, gate v → ¬ T v := fun v hv ht => hP1 v hv v ht .refl
  have hedge : ∀ c : I, ∃ e : Option Γ.Jx, (c ∈ C → ∃ j, e = some j ∧
      (((Γ.edgeEnds j).1 = Sum.inr c ∧ (Γ.edgeEnds j).2 = parA (Sum.inr c)) ∨
       ((Γ.edgeEnds j).2 = Sum.inr c ∧ (Γ.edgeEnds j).1 = parA (Sum.inr c))) ∧
      (gate (Sum.inr c) ↔ ∃ j', j = Sum.inl j')) ∧ (c ∉ C → e = none) := by
    intro c
    by_cases hc : c ∈ C
    · have hT := (hCmem c).1 hc
      rcases hP2 (Sum.inr c) hT with ⟨hg, hw⟩ | ⟨hg, ha⟩
      · obtain ⟨j, hj⟩ := hw
        exact ⟨some (Sum.inl j), fun _ => ⟨_, rfl, hj.imp id And.symm, ⟨fun _ => ⟨j, rfl⟩, fun _ => hg⟩⟩,
          fun h => absurd hc h⟩
      · rcases BASizeClaim_atomAdj_cases Γ hD ha with ⟨j, hj⟩ | ⟨j, hj⟩
        · exact ⟨some (Sum.inr (Sum.inl j)), fun _ => ⟨_, rfl, hj.imp id And.symm,
            ⟨fun h => absurd h hg, fun ⟨j', h⟩ => nomatch h⟩⟩, fun h => absurd hc h⟩
        · exact ⟨some (Sum.inr (Sum.inr j)), fun _ => ⟨_, rfl, hj.imp id And.symm,
            ⟨fun h => absurd h hg, fun ⟨j', h⟩ => nomatch h⟩⟩, fun h => absurd hc h⟩
    · exact ⟨none, fun h => absurd h hc, fun _ => rfl⟩
  choose edge hedge using hedge
  let IA : Finset (Finset (E ⊕ I)) := IAfin.image Γ.atom
  let RA : Finset (Finset (E ⊕ I)) := (Finset.univ : Finset (LGraph.AuxIMol Γ.shadow)).image (fun m => Γ.atom (Sum.inr (rep m)))
  have hNTint : ∀ v, (∀ t, T t → ¬ Relation.ReflTransGen A v t) → ∀ w ∈ Γ.atom v, w.isRight = true := by
    intro v hv w hw
    rw [BAGraph.mem_atom_iff] at hw
    by_contra hwr
    have : w.isLeft = true := by cases w <;> simp_all
    exact hv w (Or.inl this) hw
  have hRAsub : RA ⊆ IA := by
    intro X hX
    obtain ⟨m, _, rfl⟩ := Finset.mem_image.1 hX
    refine Finset.mem_image.2 ⟨Sum.inr (rep m), ?_, rfl⟩
    simp only [IAfin, Finset.mem_filter, Finset.mem_univ, true_and]
    intro w hw
    exact hint m w (Γ.atom_subset_mol _ hw)
  have hRAcard : RA.card = Γ.nM := by
    rw [Finset.card_image_of_injective, Finset.card_univ, auxGraph_card_aux, BAGraph.shadow_nM]
    intro m m' h
    have h' : Γ.atom (Sum.inr (rep m)) = Γ.atom (Sum.inr (rep m')) := h
    have h1 : Sum.inr (rep m') ∈ Γ.atom (Sum.inr (rep m)) := by
      rw [h']; exact BASizeClaim_self_mem_atom Γ _
    apply Subtype.ext
    rw [← hrep m, ← hrep m']
    exact (BAAtom_shadow_molOf_eq_iff Γ _ _).2 (Γ.atom_subset_mol _ h1)
  have hB : ∀ X, X ∈ IA \ RA ↔ ∃ v, X = Γ.atom v ∧ ∀ t, T t → ¬ Relation.ReflTransGen A v t := by
    intro X
    rw [Finset.mem_sdiff]
    constructor
    · rintro ⟨hX, hXR⟩
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hX
      refine ⟨v, rfl, fun t ht hvt => ?_⟩
      have hv' : ∀ w ∈ Γ.atom v, w.isRight = true := by simpa [IAfin] using hv
      have htv : t ∈ Γ.atom v := (BAGraph.mem_atom_iff Γ v t).2 hvt
      rcases ht with ht | ⟨m, rfl⟩
      · have := hv' t htv
        cases t <;> simp_all
      · apply hXR
        refine Finset.mem_image.2 ⟨m, Finset.mem_univ _, ?_⟩
        exact (BASizeClaim_atom_eq Γ htv)
    · rintro ⟨v, rfl, hv⟩
      refine ⟨Finset.mem_image.2 ⟨v, ?_, rfl⟩, fun hXR => ?_⟩
      · simpa [IAfin] using hNTint v hv
      · obtain ⟨m, _, hm⟩ := Finset.mem_image.1 hXR
        have : Sum.inr (rep m) ∈ Γ.atom v := by
          rw [← hm]; exact BASizeClaim_self_mem_atom Γ _
        exact hv _ (Or.inr ⟨m, rfl⟩) ((BAGraph.mem_atom_iff Γ v _).1 this)
  have hfilter : (C.filter fun c => ∃ j, edge c = some (Sum.inl j)) =
      Finset.univ.filter (fun c : I => gate (Sum.inr c)) := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hc, j, hj⟩
      obtain ⟨j0, e0, _, hgi⟩ := (hedge c).1 hc
      rw [hj] at e0
      cases e0
      exact hgi.2 ⟨j, rfl⟩
    · intro hg
      have hc : c ∈ C := (hCmem c).2 (hgateT _ hg)
      obtain ⟨j0, e0, _, hgi⟩ := (hedge c).1 hc
      obtain ⟨j', hj'⟩ := hgi.1 hg
      exact ⟨hc, j', by rw [e0, hj']⟩
  have hgcard : (Finset.univ.filter (fun c : I => gate (Sum.inr c))).card = (IA \ RA).card := by
    refine Finset.card_bij (fun c _ => Γ.atom (Sum.inr c)) (fun c hc => ?_) (fun c₁ h₁ c₂ h₂ h => ?_)
      (fun X hX => ?_)
    · have hg : gate (Sum.inr c) := by simpa using hc
      exact (hB _).2 ⟨_, rfl, hP1 _ hg⟩
    · have hg₁ : gate (Sum.inr c₁) := by simpa using h₁
      have hg₂ : gate (Sum.inr c₂) := by simpa using h₂
      have h3 : Sum.inr c₂ ∈ Γ.atom (Sum.inr c₁) := by
        rw [h]; exact BASizeClaim_self_mem_atom Γ _
      exact Sum.inr_injective (hP5 _ _ hg₁ hg₂ ((BAGraph.mem_atom_iff Γ _ _).1 h3))
    · obtain ⟨v, rfl, hv⟩ := (hB X).1 hX
      obtain ⟨u, hu, hvu⟩ := hP4 v hv
      have hu' : u ∈ Γ.atom v := (BAGraph.mem_atom_iff Γ v u).2 hvu
      have hur := hNTint v hv u hu'
      obtain ⟨c, rfl⟩ : ∃ c, u = Sum.inr c := by
        cases u with
        | inl a => simp at hur
        | inr c => exact ⟨c, rfl⟩
      exact ⟨c, by simpa using hu, BASizeClaim_atom_eq Γ hu'⟩
  refine ⟨C, fun c => parA (Sum.inr c), edge, fun c => ρ (Sum.inr c), ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    rw [hCmem]
    constructor
    · rintro h ⟨m, hm⟩
      exact h (Or.inr ⟨m, by rw [hm]⟩)
    · rintro h (hT | ⟨m, hm⟩)
      · simp at hT
      · exact h ⟨m, (Sum.inr_injective hm).symm⟩
  · rw [hfilter, hgcard]
    have := Finset.card_sdiff_add_card_eq_card hRAsub
    rw [hRAcard] at this
    exact this
  · intro c hc w hw
    have hw' : parA (Sum.inr c) = Sum.inr w := hw
    have := hP3 (Sum.inr c) ((hCmem c).1 hc)
    rw [hw'] at this
    exact this
  · intro c hc
    obtain ⟨j, hj, hends, _⟩ := (hedge c).1 hc
    exact ⟨j, hj, hends⟩
  · intro c₁ h₁ c₂ h₂ h
    obtain ⟨j₁, e₁, hends₁, _⟩ := (hedge c₁).1 h₁
    obtain ⟨j₂, e₂, hends₂, _⟩ := (hedge c₂).1 h₂
    rw [e₁, e₂] at h
    cases h
    by_contra hne
    have hr₁ := hP3 (Sum.inr c₁) ((hCmem c₁).1 h₁)
    have hr₂ := hP3 (Sum.inr c₂) ((hCmem c₂).1 h₂)
    rcases hends₁ with ⟨a₁, b₁⟩ | ⟨a₁, b₁⟩ <;> rcases hends₂ with ⟨a₂, b₂⟩ | ⟨a₂, b₂⟩
    · exact hne (Sum.inr_injective (a₁.symm.trans a₂))
    · rw [a₁] at b₂
      rw [b₁] at a₂
      rw [a₂] at hr₁
      rw [← b₂] at hr₂
      omega
    · rw [a₁] at b₂
      rw [b₁] at a₂
      rw [a₂] at hr₁
      rw [← b₂] at hr₂
      omega
    · exact hne (Sum.inr_injective (a₁.symm.trans a₂))

/-- **The sum over the internal labels with the prescribed roots as free labels, per-edge constants** (twin of `BAAtom_sum_J`, `Graph/BAAtom.lean:896`, whose
roots are chosen; the same peeling `BAAtom_forest_roots`, `Graph/BAAtom.lean:722`, on the forest of `BAMomentExpGen_exists_forest`):
`Σ_{ℓ_I} Φ(ℓ ∘ rep) ∏_J f_j ≤ (Σ_x Φ x) K₁^{n_A - n_M} a^{n_W - (n_A - n_M)} Kd^{#M + #Ψ}`. -/
theorem BAMomentExpGen_sum_J {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι] (Γ : BAGraph E I)
    (hD : ∀ e ∈ Γ.dotted, e.eq = false) (f : Γ.Jx → ι → ι → ℝ) {a K₁ Kd : ℝ}
    (hf0 : ∀ j x y, 0 ≤ f j x y)
    (hwa : ∀ (j : Fin Γ.waved.length) x y, f (Sum.inl j) x y ≤ a)
    (hwr : ∀ (j : Fin Γ.waved.length) x, ∑ y, f (Sum.inl j) x y ≤ K₁)
    (hwc : ∀ (j : Fin Γ.waved.length) y, ∑ x, f (Sum.inl j) x y ≤ K₁)
    (hda : ∀ (j : Fin Γ.mdot.length ⊕ Fin Γ.psi.length) x y, f (Sum.inr j) x y ≤ Kd)
    (hdr : ∀ (j : Fin Γ.mdot.length ⊕ Fin Γ.psi.length) x, ∑ y, f (Sum.inr j) x y ≤ Kd)
    (hdc : ∀ (j : Fin Γ.mdot.length ⊕ Fin Γ.psi.length) y, ∑ x, f (Sum.inr j) x y ≤ Kd)
    [Fintype (LGraph.AuxIMol Γ.shadow)] [DecidableEq (LGraph.AuxIMol Γ.shadow)] (ℓe : E → ι)
    (rep : LGraph.AuxIMol Γ.shadow → I) (hrep : ∀ c, Γ.shadow.molOf (Sum.inr (rep c)) = c.1)
    (Φ : (LGraph.AuxIMol Γ.shadow → ι) → ℝ) (hΦ : ∀ x, 0 ≤ Φ x) :
    ∑ ℓi : I → ι, Φ (fun t => ℓi (rep t)) *
        ∏ j : Γ.Jx, f j (Sum.elim ℓe ℓi (Γ.edgeEnds j).1) (Sum.elim ℓe ℓi (Γ.edgeEnds j).2) ≤
      (∑ x : LGraph.AuxIMol Γ.shadow → ι, Φ x) *
        (K₁ ^ (Γ.nA - Γ.nM) * a ^ (Γ.nW - (Γ.nA - Γ.nM)) * Kd ^ (Γ.mdot.length + Γ.psi.length)) := by
  classical
  obtain ⟨C, par, edge, ρ, hC, hgcard, hrank, hedge, hinj⟩ := BAMomentExpGen_exists_forest Γ hD rep hrep
  have hroot : Function.Injective rep := fun c c' h => Subtype.ext (by rw [← hrep c, ← hrep c', h])
  choose edgeJ hedgeJ using fun c : C => hedge c.1 c.2
  have hinjJ : Function.Injective edgeJ := fun c₁ c₂ h =>
    Subtype.ext (hinj c₁.1 c₁.2 c₂.1 c₂.2 (by rw [(hedgeJ c₁).1, (hedgeJ c₂).1, h]))
  let aJ : Γ.Jx → ℝ := fun j => match j with
    | Sum.inl _ => a
    | Sum.inr _ => Kd
  let KJ : Γ.Jx → ℝ := fun j => match j with
    | Sum.inl _ => K₁
    | Sum.inr _ => Kd
  have hmain := BAAtom_forest_roots (ι := ι) (E := E) (I := I) (Rt := LGraph.AuxIMol Γ.shadow) (J := Γ.Jx) ℓe
    (fun j => (Γ.edgeEnds j).1) (fun j => (Γ.edgeEnds j).2) f aJ KJ hf0
    (by rintro (j | j) x y; exacts [hwa j x y, hda j x y])
    (by rintro (j | j) x; exacts [hwr j x, hdr j x])
    (by rintro (j | j) y; exacts [hwc j y, hdc j y])
    rep hroot C hC par edgeJ ρ hinjJ (fun c => (hedgeJ c).2) (fun c => hrank c.1 c.2) Φ hΦ
  have halg := BAAtom_alg_prod (I := C) (p := Γ.waved.length) (q := Γ.mdot.length) (r := Γ.psi.length)
    a K₁ Kd KJ aJ (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (Finset.univ : Finset C) edgeJ
    hinjJ.injOn
  have hw : (Finset.univ.filter fun c : C => ∃ jw, edgeJ c = Sum.inl jw).card = Γ.nA - Γ.nM := by
    have h1 : (Finset.univ.filter fun c : C => ∃ jw, edgeJ c = Sum.inl jw).card =
        (C.filter fun c => ∃ j, edge c = some (Sum.inl j)).card := by
      refine Finset.card_bij (fun c _ => c.1) (fun c hc => ?_) (fun c₁ _ c₂ _ h => Subtype.ext h) (fun c hc => ?_)
      · obtain ⟨jw, hjw⟩ := (Finset.mem_filter.1 hc).2
        exact Finset.mem_filter.2 ⟨c.2, jw, by rw [(hedgeJ c).1, hjw]⟩
      · obtain ⟨hcC, jw, hjw⟩ := Finset.mem_filter.1 hc
        refine ⟨⟨c, hcC⟩, Finset.mem_filter.2 ⟨Finset.mem_univ _, jw, ?_⟩, rfl⟩
        have := (hedgeJ ⟨c, hcC⟩).1
        rw [hjw] at this
        exact (Option.some.inj this).symm
    omega
  rw [halg, hw] at hmain
  exact hmain

variable {d L W : ℕ} [NeZero L] [NeZero W]

open Classical in
/-- **The main sum with the indicator of the root blocks** (twin of `BAAtom_main_sum`, `Graph/BAAtom2.lean:338`, and of `lwAuxRoot_main_sum`,
`Graph/AuxGraphRooted.lean:136`): the sum over the labels of the internal vertices of the confined bound, multiplied by `1[every root block ∈ Dm]`, is
`≤ (W^d)^{n_M} Γ^aux_{[ℓe]}(Dm) K₁^{n_A - n_M} a^{n_W - (n_A - n_M)} Kd^{#M + #Ψ}`, the aux graph summed over the blocks in `Dm`. -/
theorem BAMomentExpGen_main_sum (Γ : BAGraph E I) (hN : Γ.Normal) (D : BALData (Idx d L W)) {a K₁ Kd : ℝ}
    {ξ : Zd d L → Zd d L → ℝ} (hξ0 : ∀ a b, 0 ≤ ξ a b)
    (hS : LWKBound D.S a K₁) (hSp : LWKBound D.Sp a K₁) (hM : LWKBound D.M Kd Kd) (hP : LWKBound D.gPsi Kd Kd)
    (ℓe : E → Idx d L W) (Dm : Finset (Zd d L))
    (rep : LGraph.AuxIMol Γ.shadow → I) (hrep : ∀ c, Γ.shadow.molOf (Sum.inr (rep c)) = c.1) :
    ∑ ℓi : I → Idx d L W, (if ∀ c, (split d L W (ℓi (rep c))).1 ∈ Dm then (1 : ℝ) else 0) *
        ((Γ.shadow.molSolid.map fun e => ξ
            (LGraph.auxLab Γ.shadow (fun a => (split d L W (ℓe a)).1) (fun c => (split d L W (ℓi (rep c))).1) e.src)
            (LGraph.auxLab Γ.shadow (fun a => (split d L W (ℓe a)).1) (fun c => (split d L W (ℓi (rep c))).1) e.dst)).prod *
          ∏ j : Γ.Jx, BAAtom_fJ Γ D j (Sum.elim ℓe ℓi (Γ.edgeEnds j).1) (Sum.elim ℓe ℓi (Γ.edgeEnds j).2)) ≤
      ((W : ℝ) ^ d) ^ Γ.nM * auxValOn Γ.shadow ξ (fun a => (split d L W (ℓe a)).1) Dm *
        (K₁ ^ (Γ.nA - Γ.nM) * a ^ (Γ.nW - (Γ.nA - Γ.nM)) * Kd ^ (Γ.mdot.length + Γ.psi.length)) := by
  have : Nonempty (Idx d L W) := ⟨fun _ => 0⟩
  have : Fintype (LGraph.AuxIMol Γ.shadow) := Fintype.ofFinite _
  set P : (LGraph.AuxIMol Γ.shadow → Zd d L) → ℝ := fun b =>
    (Γ.shadow.molSolid.map fun e => ξ
        (LGraph.auxLab Γ.shadow (fun a => (split d L W (ℓe a)).1) b e.src)
        (LGraph.auxLab Γ.shadow (fun a => (split d L W (ℓe a)).1) b e.dst)).prod with hP'
  have hP0 : ∀ b, 0 ≤ P b := fun b => List.prod_nonneg fun y hy => by
    obtain ⟨e, _, rfl⟩ := List.mem_map.1 hy
    exact hξ0 _ _
  set Φ : (LGraph.AuxIMol Γ.shadow → Idx d L W) → ℝ := fun x =>
    (if ∀ c, (split d L W (x c)).1 ∈ Dm then (1 : ℝ) else 0) * P (fun c => (split d L W (x c)).1) with hΦ
  have hΦ0 : ∀ x, 0 ≤ Φ x := fun x => mul_nonneg (by split_ifs <;> norm_num) (hP0 _)
  have hmain := BAMomentExpGen_sum_J Γ hN.1 (BAAtom_fJ Γ D)
    (fun j x y => BAAtom_nonneg_fJ Γ D j x y)
    (fun j x y => (auxGraph_wval_bound hS hSp (Γ.waved.get j)).1 x y)
    (fun j x => (auxGraph_wval_bound hS hSp (Γ.waved.get j)).2.1 x)
    (fun j y => (auxGraph_wval_bound hS hSp (Γ.waved.get j)).2.2 y)
    (fun j x y => by rcases j with j | j; exacts [hM.1 x y, hP.1 x y])
    (fun j x => by rcases j with j | j; exacts [hM.2.1 x, hP.2.1 x])
    (fun j y => by rcases j with j | j; exacts [hM.2.2 y, hP.2.2 y]) ℓe rep hrep Φ hΦ0
  have hblocks := auxGraph_sum_blocks (d := d) (L := L) (W := W) (Rt := LGraph.AuxIMol Γ.shadow)
    (fun b => (if ∀ c, b c ∈ Dm then (1 : ℝ) else 0) * P b)
  rw [auxGraph_card_aux, BAGraph.shadow_nM] at hblocks
  have hind : ∀ b : LGraph.AuxIMol Γ.shadow → Zd d L, (if ∀ c, b c ∈ Dm then (1 : ℝ) else 0) * P b =
      if b ∈ Fintype.piFinset (fun _ : LGraph.AuxIMol Γ.shadow => Dm) then P b else 0 := by
    intro b
    by_cases h : ∀ c, b c ∈ Dm
    · simp [Fintype.mem_piFinset, h]
    · simp [Fintype.mem_piFinset, h]
  have hΦsum : ∑ x : LGraph.AuxIMol Γ.shadow → Idx d L W, Φ x =
      ((W : ℝ) ^ d) ^ Γ.nM * auxValOn Γ.shadow ξ (fun a => (split d L W (ℓe a)).1) Dm := by
    have h1 : ∑ b : LGraph.AuxIMol Γ.shadow → Zd d L, (if ∀ c, b c ∈ Dm then (1 : ℝ) else 0) * P b =
        auxValOn Γ.shadow ξ (fun a => (split d L W (ℓe a)).1) Dm := by
      simp_rw [hind]
      rw [Finset.sum_ite_mem, Finset.univ_inter]
      unfold auxValOn
      congr
      exact Subsingleton.elim _ _
    rw [← h1]
    exact hblocks
  rw [hΦsum] at hmain
  refine le_trans (le_of_eq (Finset.sum_congr rfl fun ℓi _ => ?_)) hmain
  simp only [hΦ, hP']
  by_cases h : ∀ c, (split d L W (ℓi (rep c))).1 ∈ Dm
  · simp [h]
  · simp [h]

/-- **G3 for a weighted sum, deterministic form** (twin of `BAExp14d_G3`, `Graph/BAExp14d.lean:138`, and of the proof of `lwGtoAGRooted_holds`,
`Graph/AuxGraphRooted.lean:244`): the roots `rep` are prescribed, a real weight `|Wt| ≤ 1` vanishing unless every root block lies in `Dm` multiplies the
terms, the restricted main sum `BAMomentExpGen_main_sum` bounds the confined part, the tail sum `BAAtom_tail_sum` the rest. -/
theorem BAMomentExpGen_G3Rooted (d : ℕ) (hd : 3 ≤ d) (L W : ℕ) [NeZero L] [NeZero W] (Γ : BAGraph E I) (hN : Γ.Normal)
    (D : BALData (Idx d L W)) (Ψ A K₀ K₁ Kd C c r R : ℝ) (ξ : Zd d L → Zd d L → ℝ) (Dm : Finset (Zd d L))
    (hG : ∀ x y, ‖D.G x y - D.M x y‖ ≤ Ψ) (hA : 0 ≤ A) (hwin : ((W : ℝ) ^ d)⁻¹ ≤ A * Ψ ^ 2)
    (hS : LWKBound D.S (K₀ * ((W : ℝ) ^ d)⁻¹) K₁) (hSp : LWKBound D.Sp (K₀ * ((W : ℝ) ^ d)⁻¹) K₁)
    (hM : LWKBound D.M Kd Kd) (hP : LWKBound D.gPsi Kd Kd) (hC : 0 ≤ C) (hc : 0 < c)
    (hSd : ∀ x y, ‖D.S x y‖ ≤ C * ((W : ℝ) ^ d)⁻¹ * Real.exp (-(c * (lwBdist d L W x y : ℝ))))
    (hSpd : ∀ x y, ‖D.Sp x y‖ ≤ C * ((W : ℝ) ^ d)⁻¹ * Real.exp (-(c * (lwBdist d L W x y : ℝ))))
    (hMPd : ∀ x y, ‖D.M x y‖ ≤ C * Real.exp (-(c * (lwBdist d L W x y : ℝ))) ∧
      ‖D.gPsi x y‖ ≤ C * Real.exp (-(c * (lwBdist d L W x y : ℝ))))
    (hoff : ∀ x y, (split d L W x).2 ≠ (split d L W y).2 → D.M x y = 0 ∧ D.gPsi x y = 0)
    (hr : 0 ≤ r) (hRr : (Fintype.card (E ⊕ I) : ℝ) * r ≤ R) (hξ0 : ∀ a b, 0 ≤ ξ a b)
    (hξ : ∀ (x y : Idx d L W) (a b : Zd d L), (zdistD d L ((split d L W x).1 - a) : ℝ) ≤ R →
      (zdistD d L ((split d L W y).1 - b) : ℝ) ≤ R → ‖D.G x y - D.M x y‖ ≤ ξ a b)
    (rep : LGraph.AuxIMol Γ.shadow → I) (hrep : ∀ c, Γ.shadow.molOf (Sum.inr (rep c)) = c.1)
    (Wt : (E ⊕ I → Idx d L W) → ℝ) (hWt1 : ∀ ℓ, |Wt ℓ| ≤ 1)
    (hWt0 : ∀ ℓ, Wt ℓ ≠ 0 → ∀ c, (split d L W (ℓ (Sum.inr (rep c)))).1 ∈ Dm) (ℓe : E → Idx d L W) :
    ‖Γ.valW D Wt ℓe‖ ≤
      Γ.sizeConst (K₀ * A) K₁ Kd * Ψ ^ (Γ.scalingOrder - Γ.auxOrd) *
          (((W : ℝ) ^ d) ^ Γ.nM * auxValOn Γ.shadow ξ (fun a => (split d L W (ℓe a)).1) Dm) +
        Real.exp (-(c * r / 2)) * Γ.sizeConst C (C * expC (d - 2) (c / 2)) (C * (1 + expC (d - 2) (c / 2))) *
          Γ.scalingSize Ψ W d L := by
  classical
  have hne : Nonempty (Idx d L W) := ⟨fun _ => 0⟩
  have hΨ : 0 ≤ Ψ := (norm_nonneg _).trans (hG (fun _ => 0) (fun _ => 0))
  have hWpos : (0 : ℝ) < ((W : ℕ) : ℝ) := Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne W))
  have hWd : (0 : ℝ) < (W : ℝ) ^ d := pow_pos hWpos d
  have hK₀' : 0 ≤ K₀ * ((W : ℝ) ^ d)⁻¹ := (norm_nonneg _).trans (hS.1 (fun _ => 0) (fun _ => 0))
  have hK₀ : 0 ≤ K₀ := by
    by_contra h
    push Not at h
    have : K₀ * ((W : ℝ) ^ d)⁻¹ < 0 := mul_neg_of_neg_of_pos h (inv_pos.2 hWd)
    linarith
  obtain ⟨h1, h2⟩ := Γ.counters_le hN.1
  have hmS := Γ.molSolid_length_le
  have hmain := BAMomentExpGen_main_sum Γ hN D hξ0 hS hSp hM hP ℓe Dm rep hrep
  have htail := BAAtom_tail_sum (r := r) hd Γ hN D hΨ hC hc hSd hSpd hMPd hoff ℓe
  have ha : K₀ * ((W : ℝ) ^ d)⁻¹ ≤ K₀ * (A * Ψ ^ 2) := mul_le_mul_of_nonneg_left hwin hK₀
  have hapow : (K₀ * ((W : ℝ) ^ d)⁻¹) ^ (Γ.nW - (Γ.nA - Γ.nM)) ≤
      (K₀ * A) ^ (Γ.nW - (Γ.nA - Γ.nM)) * Ψ ^ (2 * (Γ.nW - (Γ.nA - Γ.nM))) := by
    calc (K₀ * ((W : ℝ) ^ d)⁻¹) ^ (Γ.nW - (Γ.nA - Γ.nM)) ≤ (K₀ * (A * Ψ ^ 2)) ^ (Γ.nW - (Γ.nA - Γ.nM)) :=
          pow_le_pow_left₀ hK₀' ha _
      _ = _ := by rw [← mul_assoc, mul_pow, ← pow_mul, mul_comm 2]
  have hexp : Γ.scalingOrder - Γ.auxOrd =
      (((Γ.nS - Γ.shadow.molSolid.length) + 2 * (Γ.nW - (Γ.nA - Γ.nM)) : ℕ) : ℤ) := by
    rw [Γ.scalingOrder_sub_auxOrd]
    unfold BAGraph.nS BAGraph.nW at *
    omega
  rw [hexp, zpow_natCast]
  have hav0 : 0 ≤ auxValOn Γ.shadow ξ (fun a => (split d L W (ℓe a)).1) Dm := by
    unfold auxValOn
    exact Finset.sum_nonneg fun b _ => List.prod_nonneg fun y hy => by
      obtain ⟨e, _, rfl⟩ := List.mem_map.1 hy
      exact hξ0 _ _
  have hK₁ : 0 ≤ K₁ := (Finset.sum_nonneg fun y _ => norm_nonneg _).trans (hS.2.1 (fun _ => 0))
  have hKd : 0 ≤ Kd := (norm_nonneg _).trans (hM.1 (fun _ => 0) (fun _ => 0))
  have hmain' : ∑ ℓi : I → Idx d L W, ‖Γ.coeff‖ * Ψ ^ (Γ.nS - Γ.shadow.molSolid.length) *
        ((if ∀ c, (split d L W (ℓi (rep c))).1 ∈ Dm then (1 : ℝ) else 0) * ((Γ.shadow.molSolid.map fun e => ξ
            (LGraph.auxLab Γ.shadow (fun a => (split d L W (ℓe a)).1) (fun c => (split d L W (ℓi (rep c))).1) e.src)
            (LGraph.auxLab Γ.shadow (fun a => (split d L W (ℓe a)).1) (fun c => (split d L W (ℓi (rep c))).1) e.dst)).prod *
          ∏ j : Γ.Jx, BAAtom_fJ Γ D j (Sum.elim ℓe ℓi (Γ.edgeEnds j).1) (Sum.elim ℓe ℓi (Γ.edgeEnds j).2))) ≤
      Γ.sizeConst (K₀ * A) K₁ Kd * Ψ ^ ((Γ.nS - Γ.shadow.molSolid.length) + 2 * (Γ.nW - (Γ.nA - Γ.nM))) *
        (((W : ℝ) ^ d) ^ Γ.nM * auxValOn Γ.shadow ξ (fun a => (split d L W (ℓe a)).1) Dm) := by
    rw [← Finset.mul_sum]
    have hcn : 0 ≤ ‖Γ.coeff‖ * Ψ ^ (Γ.nS - Γ.shadow.molSolid.length) := by positivity
    calc ‖Γ.coeff‖ * Ψ ^ (Γ.nS - Γ.shadow.molSolid.length) * ∑ ℓi : I → Idx d L W,
          ((if ∀ c, (split d L W (ℓi (rep c))).1 ∈ Dm then (1 : ℝ) else 0) * ((Γ.shadow.molSolid.map fun e => ξ
              (LGraph.auxLab Γ.shadow (fun a => (split d L W (ℓe a)).1) (fun c => (split d L W (ℓi (rep c))).1) e.src)
              (LGraph.auxLab Γ.shadow (fun a => (split d L W (ℓe a)).1) (fun c => (split d L W (ℓi (rep c))).1) e.dst)).prod *
            ∏ j : Γ.Jx, BAAtom_fJ Γ D j (Sum.elim ℓe ℓi (Γ.edgeEnds j).1) (Sum.elim ℓe ℓi (Γ.edgeEnds j).2)))
        ≤ ‖Γ.coeff‖ * Ψ ^ (Γ.nS - Γ.shadow.molSolid.length) *
          (((W : ℝ) ^ d) ^ Γ.nM * auxValOn Γ.shadow ξ (fun a => (split d L W (ℓe a)).1) Dm *
            (K₁ ^ (Γ.nA - Γ.nM) * (K₀ * ((W : ℝ) ^ d)⁻¹) ^ (Γ.nW - (Γ.nA - Γ.nM)) *
              Kd ^ (Γ.mdot.length + Γ.psi.length))) :=
          mul_le_mul_of_nonneg_left hmain hcn
      _ ≤ ‖Γ.coeff‖ * Ψ ^ (Γ.nS - Γ.shadow.molSolid.length) *
          (((W : ℝ) ^ d) ^ Γ.nM * auxValOn Γ.shadow ξ (fun a => (split d L W (ℓe a)).1) Dm *
            (K₁ ^ (Γ.nA - Γ.nM) * ((K₀ * A) ^ (Γ.nW - (Γ.nA - Γ.nM)) * Ψ ^ (2 * (Γ.nW - (Γ.nA - Γ.nM)))) *
              Kd ^ (Γ.mdot.length + Γ.psi.length))) := by
          refine mul_le_mul_of_nonneg_left ?_ hcn
          refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (by positivity) hav0)
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          exact mul_le_mul_of_nonneg_left hapow (by positivity)
      _ = _ := by
          unfold BAGraph.sizeConst
          rw [pow_add]
          ring
  have hpt : ∀ ℓi : I → Idx d L W, ‖((Wt (Sum.elim ℓe ℓi) : ℝ) : ℂ) * Γ.term D (Sum.elim ℓe ℓi)‖ ≤
      ‖Γ.coeff‖ * Ψ ^ (Γ.nS - Γ.shadow.molSolid.length) *
        ((if ∀ c, (split d L W (ℓi (rep c))).1 ∈ Dm then (1 : ℝ) else 0) * ((Γ.shadow.molSolid.map fun e => ξ
            (LGraph.auxLab Γ.shadow (fun a => (split d L W (ℓe a)).1) (fun c => (split d L W (ℓi (rep c))).1) e.src)
            (LGraph.auxLab Γ.shadow (fun a => (split d L W (ℓe a)).1) (fun c => (split d L W (ℓi (rep c))).1) e.dst)).prod *
          ∏ j : Γ.Jx, BAAtom_fJ Γ D j (Sum.elim ℓe ℓi (Γ.edgeEnds j).1) (Sum.elim ℓe ℓi (Γ.edgeEnds j).2))) +
      ‖Γ.coeff‖ * Ψ ^ Γ.nS * (Real.exp (-(c * r / 2)) *
        ∏ j : Γ.Jx, BAAtom_fJw Γ D c j (Sum.elim ℓe ℓi (Γ.edgeEnds j).1) (Sum.elim ℓe ℓi (Γ.edgeEnds j).2)) := by
    intro ℓi
    have hMn0 : 0 ≤ (Γ.shadow.molSolid.map fun e => ξ
          (LGraph.auxLab Γ.shadow (fun a => (split d L W (ℓe a)).1) (fun c => (split d L W (ℓi (rep c))).1) e.src)
          (LGraph.auxLab Γ.shadow (fun a => (split d L W (ℓe a)).1) (fun c => (split d L W (ℓi (rep c))).1) e.dst)).prod :=
      List.prod_nonneg fun y hy => by
        obtain ⟨e, _, rfl⟩ := List.mem_map.1 hy
        exact hξ0 _ _
    have h2' : 0 ≤ ∏ j : Γ.Jx, BAAtom_fJ Γ D j (Sum.elim ℓe ℓi (Γ.edgeEnds j).1) (Sum.elim ℓe ℓi (Γ.edgeEnds j).2) :=
      Finset.prod_nonneg fun j _ => BAAtom_nonneg_fJ _ _ _ _ _
    have hInd0 : 0 ≤ (if ∀ c, (split d L W (ℓi (rep c))).1 ∈ Dm then (1 : ℝ) else 0) := by split_ifs <;> norm_num
    have hMn : 0 ≤ ‖Γ.coeff‖ * Ψ ^ (Γ.nS - Γ.shadow.molSolid.length) *
        ((if ∀ c, (split d L W (ℓi (rep c))).1 ∈ Dm then (1 : ℝ) else 0) * ((Γ.shadow.molSolid.map fun e => ξ
            (LGraph.auxLab Γ.shadow (fun a => (split d L W (ℓe a)).1) (fun c => (split d L W (ℓi (rep c))).1) e.src)
            (LGraph.auxLab Γ.shadow (fun a => (split d L W (ℓe a)).1) (fun c => (split d L W (ℓi (rep c))).1) e.dst)).prod *
          ∏ j : Γ.Jx, BAAtom_fJ Γ D j (Sum.elim ℓe ℓi (Γ.edgeEnds j).1) (Sum.elim ℓe ℓi (Γ.edgeEnds j).2))) := by positivity
    have hTl : 0 ≤ ‖Γ.coeff‖ * Ψ ^ Γ.nS * (Real.exp (-(c * r / 2)) *
        ∏ j : Γ.Jx, BAAtom_fJw Γ D c j (Sum.elim ℓe ℓi (Γ.edgeEnds j).1) (Sum.elim ℓe ℓi (Γ.edgeEnds j).2)) := by
      have h2 : 0 ≤ ∏ j : Γ.Jx, BAAtom_fJw Γ D c j (Sum.elim ℓe ℓi (Γ.edgeEnds j).1) (Sum.elim ℓe ℓi (Γ.edgeEnds j).2) :=
        Finset.prod_nonneg fun j _ => BAAtom_fJw_nonneg _ _ _ _ _ _
      positivity
    by_cases hW0 : Wt (Sum.elim ℓe ℓi) = 0
    · rw [hW0]
      simp only [Complex.ofReal_zero, zero_mul, norm_zero]
      exact add_nonneg hMn hTl
    · have hall : ∀ c, (split d L W (ℓi (rep c))).1 ∈ Dm := fun c' => by simpa using hWt0 _ hW0 c'
      have hind : (if ∀ c, (split d L W (ℓi (rep c))).1 ∈ Dm then (1 : ℝ) else 0) = 1 := by simp [hall]
      have hw1 : ‖((Wt (Sum.elim ℓe ℓi) : ℝ) : ℂ) * Γ.term D (Sum.elim ℓe ℓi)‖ ≤ ‖Γ.term D (Sum.elim ℓe ℓi)‖ := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        exact mul_le_of_le_one_left (norm_nonneg _) (hWt1 _)
      refine hw1.trans ?_
      rw [hind, one_mul]
      by_cases hconf : ∀ j : Γ.Jx, (lwBdist d L W (Sum.elim ℓe ℓi (Γ.edgeEnds j).1) (Sum.elim ℓe ℓi (Γ.edgeEnds j).2) : ℝ) ≤ r
      · exact (BAAtom_term_conf Γ hN D hG hξ hr hRr ℓe ℓi rep hrep hconf).trans (le_add_of_nonneg_right hTl)
      · push Not at hconf
        refine (BAAtom_term_tail Γ hN D hG hc _ hconf).trans (le_add_of_nonneg_left ?_)
        rw [hind, one_mul] at hMn
        exact hMn
  unfold BAGraph.valW
  calc ‖∑ ℓi : I → Idx d L W, ((Wt (Sum.elim ℓe ℓi) : ℝ) : ℂ) * Γ.term D (Sum.elim ℓe ℓi)‖
      ≤ ∑ ℓi : I → Idx d L W, ‖((Wt (Sum.elim ℓe ℓi) : ℝ) : ℂ) * Γ.term D (Sum.elim ℓe ℓi)‖ := norm_sum_le _ _
    _ ≤ ∑ ℓi : I → Idx d L W, (‖Γ.coeff‖ * Ψ ^ (Γ.nS - Γ.shadow.molSolid.length) *
        ((if ∀ c, (split d L W (ℓi (rep c))).1 ∈ Dm then (1 : ℝ) else 0) * ((Γ.shadow.molSolid.map fun e => ξ
            (LGraph.auxLab Γ.shadow (fun a => (split d L W (ℓe a)).1) (fun c => (split d L W (ℓi (rep c))).1) e.src)
            (LGraph.auxLab Γ.shadow (fun a => (split d L W (ℓe a)).1) (fun c => (split d L W (ℓi (rep c))).1) e.dst)).prod *
          ∏ j : Γ.Jx, BAAtom_fJ Γ D j (Sum.elim ℓe ℓi (Γ.edgeEnds j).1) (Sum.elim ℓe ℓi (Γ.edgeEnds j).2))) +
      ‖Γ.coeff‖ * Ψ ^ Γ.nS * (Real.exp (-(c * r / 2)) *
        ∏ j : Γ.Jx, BAAtom_fJw Γ D c j (Sum.elim ℓe ℓi (Γ.edgeEnds j).1) (Sum.elim ℓe ℓi (Γ.edgeEnds j).2))) :=
        Finset.sum_le_sum fun ℓi _ => hpt ℓi
    _ = _ := Finset.sum_add_distrib
    _ ≤ _ := add_le_add hmain' htail

end Rooted

/-- **Target 5, the BA rooted G3** (`T2483_GtoAGRooted`; `LWGtoAGRooted`, `Graph/AuxGraphRooted.lean:225`, at the rescaled kernels of `BAGtoAGT`,
`Graph/BAExp14d.lean:269`; constants from `(d, Λ, κ)` only, uniformly in `0 < g₀ ≤ Λ`, `0 ≤ t < 1`): `rep c` is the root of the internal molecule `c` of
the shadow and carries the weight (`BACoverBy.rep`, `Graph/BAProv.lean:130`); `Wt ≠ 0` only where every root block is in `Dm`; the weighted value
`BAGraph.valW` is bounded by the auxiliary graph of the shadow summed over the blocks in `Dm` (`auxValOn`).  No `hext`. -/
def BAGtoAGTRooted (d : ℕ) : Prop :=
  3 ≤ d → ∀ Λ κ : ℝ, 0 < Λ → 0 < κ →
    ∃ K₀ K₁ Kd C c : ℝ, 0 < K₀ ∧ 0 < K₁ ∧ 0 ≤ Kd ∧ 0 ≤ C ∧ 0 < c ∧
      ∀ (L W : ℕ) [NeZero L] [NeZero W], 3 ≤ L → ∀ (g0 E t : ℝ) (m : ℂ), 0 < g0 → g0 ≤ Λ →
        BAReal d L g0 κ E m → 0 ≤ t → t < 1 →
        ∀ (E' I' : Type) [Fintype E'] [DecidableEq E'] [Fintype I'] [DecidableEq I'] (Γ : BAGraph E' I'), Γ.Normal →
          ∀ rep : LGraph.AuxIMol Γ.shadow → I', (∀ c, Γ.shadow.molOf (Sum.inr (rep c)) = c.1) →
          ∀ D : BALData (Idx d L W), D.S = Matrix.of (fun x y => ((svarF d L W 0 x y : ℝ) : ℂ)) →
            D.Sp = lwLift d L W (BATheta d L g0 E m t true true) → D.M = BAlwM d L W g0 E m →
            D.gPsi = (g0 : ℂ) • PsiI d L W → ∀ (Ψ A r R : ℝ) (ξ : Zd d L → Zd d L → ℝ) (Dm : Finset (Zd d L)),
            (∀ x y, ‖D.G x y - D.M x y‖ ≤ Ψ) → 0 ≤ A → ((W : ℝ) ^ d)⁻¹ ≤ A * Ψ ^ 2 →
            0 ≤ r → (Fintype.card (E' ⊕ I') : ℝ) * r ≤ R → (∀ a b, 0 ≤ ξ a b) →
            (∀ (x y : Idx d L W) (a b : Zd d L), (zdistD d L ((split d L W x).1 - a) : ℝ) ≤ R →
              (zdistD d L ((split d L W y).1 - b) : ℝ) ≤ R → ‖D.G x y - D.M x y‖ ≤ ξ a b) →
            ∀ Wt : (E' ⊕ I' → Idx d L W) → ℝ, (∀ ℓ, |Wt ℓ| ≤ 1) →
              (∀ ℓ, Wt ℓ ≠ 0 → ∀ c, (split d L W (ℓ (Sum.inr (rep c)))).1 ∈ Dm) →
              ∀ ℓe : E' → Idx d L W,
                ‖Γ.valW D Wt ℓe‖ ≤
                  Γ.sizeConst (K₀ * A) K₁ Kd * Ψ ^ (Γ.scalingOrder - Γ.auxOrd) *
                      (((W : ℝ) ^ d) ^ Γ.nM * auxValOn Γ.shadow ξ (fun a => (split d L W (ℓe a)).1) Dm) +
                    Real.exp (-(c * r / 2)) * Γ.sizeConst C (C * expC (d - 2) (c / 2)) (C * (1 + expC (d - 2) (c / 2))) *
                      Γ.scalingSize Ψ W d L

/-- **Target 5** (`baGtoAGTRooted_holds`; twin of `lwGtoAGRooted_holds`, `Graph/AuxGraphRooted.lean:244`, and of `baGtoAGT_holds`, `Graph/BAExp14d.lean:307`):
the constants are those of `baGtoAGT_holds` (`BAMomentGen_consts`, `Graph/BAMomentGen.lean:364`, the first half of its proof); the bound is
`BAMomentExpGen_G3Rooted` with the atom-first forest rooted at `rep`. -/
theorem baGtoAGTRooted_holds (d : ℕ) : BAGtoAGTRooted d := by
  intro hd Λ κ hΛ hκ
  obtain ⟨C, c, Kd, hC1, hc0, hKd, H⟩ := BAMomentGen_consts d hd Λ κ hΛ hκ
  have hE : 0 < expC (d - 2) c := by unfold expC; positivity
  refine ⟨C, C * expC (d - 2) c, Kd, C, c, by linarith, by positivity, hKd, by linarith, hc0, ?_⟩
  intro L W _ _ hL g0 E t m hg hgΛ hr ht0 ht1 E' I' _ _ _ _ Γ hN rep hrep D hDS hDSp hDM hDP Ψ A r R ξ Dm hG hA hwin hr0 hRr hξ0 hξ
    Wt hWt1 hWt0 ℓe
  obtain ⟨hSd, hSpd, hMPd, hoff, hS, hSp, hM, hP⟩ := H L W hL g0 E t m hg hgΛ hr ht0 ht1 D hDS hDSp hDM hDP
  exact BAMomentExpGen_G3Rooted d hd L W Γ hN D Ψ A C (C * expC (d - 2) c) Kd C c r R ξ Dm hG hA hwin hS hSp hM hP
    (by linarith) hc0 hSd hSpd hMPd hoff hr0 hRr hξ0 hξ rep hrep Wt hWt1 hWt0 ℓe

/-! ## 6. Compiled nonempty instances of targets 1-3

Data (`BA/LWPinsBA.lean` §3, `Graph/BAMomentGenB.lean` §4): `d = 3`, `sz0` (`n = 0`: `L = 4`, `W = 32`, `N = 2097152`, `λ = 1/64`), the flow `flow_sz0`
(`κ = 1/2`, `ε = 𝔡 = 1/10`, `𝔠 = 1/6`), `z = zSeq`, `t ≡ 1/2 ≤ BAflowT0` (`half_lt_t0`), `ε₀ = 1/10`, `Ψ_n = Φ_n ≡ W_n^{-1/2}`.  What stays a hypothesis is another
gate's pin: `STInitialGT2gL`, `LWLoopExpgL` (inside `LWAssmExpgL`), `LWLoop2gL`, `BAAnpAuxG 3` (L3d1) and the pin `BALWMomentExp 3` itself (part B). -/

section Inst

open RBM.Gauss.SizesInst RBM.BA.FlowPinsInst

local notation "μ0" => Sizes.seqP (sz0.withLam 0)

/-- The class `Φ ≡ W^{-1/2}` and the entry scale `Ψ_n = W_n^{-1/2}` of the instances. -/
private def BAMomentExpGen_Φ0 : ℕ → ℝ → ℝ := fun n _ => ((sz0.W n : ℕ) : ℝ) ^ (-(1 / 2 : ℝ))

private def BAMomentExpGen_Ψ0 : ℕ → ℝ := fun n => ((sz0.W n : ℕ) : ℝ) ^ (-(1 / 2 : ℝ))

/-- The window of the instances: `W^{-3/2} ≤ Ψ ≤ W^{-1/10}`. -/
private theorem BAMomentExpGen_Ψ0_window : LWWindow sz0 (1 / 10) BAMomentExpGen_Ψ0 :=
  Eventually.of_forall fun n => ⟨Real.rpow_le_rpow_of_exponent_le (RBM.Gauss.LWInst.one_le_W n) (by norm_num),
    Real.rpow_le_rpow_of_exponent_le (RBM.Gauss.LWInst.one_le_W n) (by norm_num)⟩

private theorem BAMomentExpGen_ell0 (n : ℕ) :
    (0 : ℝ) ≤ (Real.log ((sz0.W n : ℕ) : ℝ)) ^ 10 * ellT (sz0.L n) (sz0.lam n) (1 / 2) :=
  mul_nonneg (pow_nonneg (Real.log_nonneg (by exact_mod_cast sz0.W_pos n)) 10)
    (zero_le_one.trans (one_le_ellT (by exact_mod_cast (sz0.three_le_L n).trans' (by norm_num))))

/-- The class and its relation `(eq:Psi)` at `(ε₀, C₁, C₂, C₃, Cc) = (1/10, 2, 2, 1, 1)` (copy of `BAMomentGen_psiAll0`, `Graph/BAMomentGenB.lean:454`). -/
private theorem BAMomentExpGen_psiAll0 : LWPsiAll sz0 (1 / 10) 2 2 1 (fun _ => 1) BAMomentExpGen_Φ0 := by
  have hW1 := RBM.Gauss.LWInst.one_le_W
  refine ⟨by norm_num, ⟨Eventually.of_forall fun n r _ => ⟨Real.rpow_pos_of_pos (by linarith [hW1 n]) _,
    Real.rpow_le_rpow_of_exponent_le (hW1 n) (by norm_num)⟩, one_pos, Eventually.of_forall fun n => ?_⟩,
    fun n a _ b _ _ => le_rfl, by norm_num, by norm_num,
    fun C _ => Eventually.of_forall fun n ℓ _ _ => by simp [BAMomentExpGen_Φ0], Eventually.of_forall fun n ℓ₁ ℓ₂ h1 h12 => ?_⟩
  · simp only [BAMomentExpGen_Φ0, one_mul]
    exact Real.rpow_le_rpow_of_exponent_le (hW1 n) (by norm_num)
  · simp only [BAMomentExpGen_Φ0]
    have hW : 0 < ((sz0.W n : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos (by linarith [hW1 n]) _
    have hr : 1 ≤ ℓ₂ / ℓ₁ := (one_le_div (by linarith)).mpr h12
    have : (1 : ℝ) ≤ (ℓ₂ / ℓ₁) ^ (2 : ℝ) := Real.one_le_rpow hr (by norm_num)
    nlinarith

/-- **Instance (iv) of target 1** at `n = 0` of the data above, `x = 0`, `y = 1`, `t = 1/2`, for every sample `ω`: (b) at `Dm = univ` the domain form is the carrier `LWfg`; (c)
it is additive over the disjoint domains `{0}` and `univ \ {0}` (a proper non-empty domain: 1 of the `4^3` blocks); (d) `t` times the form at `Dm = {0}` is the data-level
`fxyValD` at `BAlwData` of the slice of the sample. -/
example (ω : sz0.SeqΩ) :
    LWfgD (baFMz sz0 zSeq) 0 (1 / 2) ω Finset.univ 0 1 = LWfg (baFMz sz0 zSeq) 0 (1 / 2) ω 0 1 ∧
    LWfgD (baFMz sz0 zSeq) 0 (1 / 2) ω Finset.univ 0 1 =
      LWfgD (baFMz sz0 zSeq) 0 (1 / 2) ω {0} 0 1 + LWfgD (baFMz sz0 zSeq) 0 (1 / 2) ω (Finset.univ \ {0}) 0 1 ∧
    ((1 / 2 : ℝ) : ℂ) * LWfgD (baFMz sz0 zSeq) 0 (1 / 2) ω {0} 0 1 =
      fxyValD (BAlwData 3 (sz0.L 0) (sz0.W 0) (BAflowLam0 sz0 zSeq 0) (BAflowEs sz0 zSeq 0) (1 / 2)
        (BAmF sz0 (BAflowLam0 sz0 zSeq) (BAflowEs sz0 zSeq) 0) (BAExp14a_slc sz0 0 ω)).toLData {0} 0 1 :=
  ⟨LWfgD_univ (baFMz sz0 zSeq) 0 (1 / 2) ω 0 1,
    by rw [← LWfgD_union (baFMz sz0 zSeq) 0 (1 / 2) ω (D₁ := {0}) (D₂ := Finset.univ \ {0}) (by simp) 0 1]; simp,
    LWfgD_baFMz sz0 zSeq 0 (1 / 2) ω {0} 0 1⟩

/-- **Instances (a) and (e) of target 1** at the same data: the band bridge at `Dm = {0}` and the exact three-way split `f = f^> + f^(a) + f^(b)` of the carrier at the
radius `ℓ = 1`. -/
example (ω : sz0.SeqΩ) : LWfgD (bandFM sz0 (fun _ => 0)) 0 (1 / 2) ω {0} 0 1 = LWfD sz0 0 0 (1 / 2) ω {0} 0 1 :=
  LWfgD_bandFM sz0 (fun _ => 0) 0 (1 / 2) ω {0} 0 1

example (ω : sz0.SeqΩ) : LWfg (baFMz sz0 zSeq) 0 (1 / 2) ω 0 1 =
    LWfgD (baFMz sz0 zSeq) 0 (1 / 2) ω (domFar 3 (sz0.L 0) (STblk sz0 0 0) (STblk sz0 0 1) 1) 0 1 +
    LWfgD (baFMz sz0 zSeq) 0 (1 / 2) ω (domNearA 3 (sz0.L 0) (STblk sz0 0 0) 1) 0 1 +
    LWfgD (baFMz sz0 zSeq) 0 (1 / 2) ω (domNearB 3 (sz0.L 0) (STblk sz0 0 0) (STblk sz0 0 1) 1) 0 1 :=
  LWfg_split (baFMz sz0 zSeq) 0 (1 / 2) 1 ω 0 1

open RBM.Gauss.InductionDefsInst RBM.Gauss.LWInst in
/-- **Instance (ii) of target 2**: the band instance of the generic pin at `d = 3` from the merged `lwMomentExp_holds 3`, applied at the preflight data of the band
(`LWMomentExp.lean` §12: `sz0`, `z0`, `flow_z0`, `t ≡ 1/16`, `ε₀ = 1/20`, `Ψ0 = W^{-1}`, `p = 2`); only `LWInit` and `LWLoopExp` (stochastic inputs) stay hypotheses. -/
example (hI : LWInit sz0 (STflowE z0) tInst (1 / 20) Ψ0) (hL : LWLoopExp sz0 (STflowE z0) tInst (ℓT tInst)) (D : ℝ) (hD : 0 < D) :=
  (LWMomentExp_iff_bandPin 3).1 (RBM.Gauss.Sizes.lwMomentExp_holds 3) le_rfl (1 / 10) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num)
    2 (dvd_refl 2) (1 / 6) sz0 z0 flow_z0 tInst tInst_range.1 tInst_range.2 (1 / 20) Ψ0 (ℓT tInst) (assmExp_of hI hL) D hD

/-- **Instance of the BA reading of target 2**: `BALWMomentExp 3` (a pin; its proof is part B) applied at the data above, `p = 2`, `ℓ ≡ 0`, `D = 1`; every deterministic
hypothesis is discharged, `(initialGT2)` and `(LW_assm_exp)` stay hypotheses. -/
example (h : BALWMomentExp 3) (hI : STInitialGT2gL (baFMz sz0 zSeq) μ0 (fun _ => 1 / 2) (1 / 10) BAMomentExpGen_Ψ0)
    (hL : LWLoopExpgL (baFMz sz0 zSeq) μ0 (fun _ => 1 / 2) (fun _ => 0)) :=
  h le_rfl (1 / 2) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) 2 (dvd_refl 2) (1 / 6) sz0 zSeq flow_sz0 (fun _ => 1 / 2)
    (fun _ => by norm_num) (fun n => (half_lt_t0 n).le) (1 / 10) BAMomentExpGen_Ψ0 (fun _ => 0)
    ⟨by norm_num, BAMomentExpGen_Ψ0_window, hI, fun _ => le_rfl, BAMomentExpGen_ell0, hL⟩ 1 one_pos

/-- **Instance (iii) of target 3**: `baLWMomentOfAnp_closed` at `d = 3` (no path binder), `p = 2`, the data above: the moment bound `𝔼 |f_{xy}|² ≺ (η⁻¹ Φ(0) Φ(c|a-b|))²`
for some `c > 0`.  The deterministic hypotheses are discharged; `BAAnpAuxG 3` (L3d1), `STInitialGT2gL` and `LWLoop2gL` stay hypotheses. -/
example (hAnp : BAAnpAuxG 3) (hI : STInitialGT2gL (baFMz sz0 zSeq) μ0 (fun _ => 1 / 2) (1 / 10) BAMomentExpGen_Ψ0)
    (hL : LWLoop2gL (baFMz sz0 zSeq) μ0 (fun _ => 1 / 2) BAMomentExpGen_Φ0) :
    ∃ c : ℝ, 0 < c ∧ PrecL sz0 μ0 (U := fun n => Idx 3 (sz0.L n) (sz0.W n) × Idx 3 (sz0.L n) (sz0.W n))
      (fun n q _ => ∫ ω, ‖LWfg (baFMz sz0 zSeq) n ((fun _ => (1 / 2 : ℝ)) n) ω q.1 q.2‖ ^ 2 ∂μ0)
      (fun n q _ => (((baFMz sz0 zSeq).eta n ((fun _ => (1 / 2 : ℝ)) n))⁻¹ * BAMomentExpGen_Φ0 n 0 *
        BAMomentExpGen_Φ0 n (c * ((zdistInf 3 (sz0.L n) (STblk sz0 n q.1 - STblk sz0 n q.2) : ℕ) : ℝ))) ^ 2) := by
  obtain ⟨c, hc, H⟩ := baLWMomentOfAnp_closed 3 hAnp le_rfl (1 / 2) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num)
    2 (dvd_refl 2) (1 / 10) 2 2 1 (fun _ => 1)
  exact ⟨c, hc, H (1 / 6) sz0 zSeq flow_sz0 (fun _ => 1 / 2) (fun _ => by norm_num) (fun n => (half_lt_t0 n).le)
    BAMomentExpGen_Ψ0 BAMomentExpGen_Φ0 ⟨by norm_num, BAMomentExpGen_Ψ0_window, hI, BAMomentExpGen_psiAll0.2.1, BAMomentExpGen_psiAll0.2.2, hL⟩⟩

end Inst

/-! ## 7. Compiled nonempty instances of targets 4 and 5 (the flow point)

Data (`BA/CouplingWindow.lean` §7.2, `Graph/BAProv.lean` §7, `Graph/BASymm1.lean`): `d = 3`, `L = 4`, `W = 2` (the one-point sizes `szP`, `n = 0`), the flow point
`(g₀, E, t₀, m₀) = (g0P, EP, t0P, m0P)` of `(L, g) = (4, 10)` (`flowP_real : BAReal 3 4 g0P (Im m_S) EP m0P`, `0 < g₀ ≤ 10 = Λ`, `0 < t₀ < 1`), the rescaled data
`BAExp14d_dataT` of an arbitrary sample `ω`, the entry scale `Ψ = 1 + Σ_{x,y} |G_{xy} - M_{xy}|`, the labels `ℓ0` (blocks `0` and `e₀`).  The start term is the
first term of the partition of `fxyPowGraph 2` with its coverage `BAProv_start`; the weight is `Π_k 1_{Dm}`, `Dm = {0}` (1 of the `4^3` blocks). -/

section InstFlow

open RBM.BA.CouplingWindowInst RBM.BA.MFixedPointInst RBM.Graph.BASymm1Inst

/-- the rescaled data of the instances: `S' = svarF(0)`, `S⁺' = lift(ω_t)`, `M = BAlwM`, `g₀ Ψ`, `G = BAlwG` of the sample `ω` -/
private abbrev BAMomentExpGen_Df (ω : Ω 3 4 2) : BALData (Idx 3 4 2) := BAExp14d_dataT 3 4 2 g0P EP t0P m0P ω

/-- the entry scale: `1 + Σ_{x,y} |G_{xy} - M_{xy}| ≥ 1` bounds every entry of `G - M` -/
private def BAMomentExpGen_Ψ (ω : Ω 3 4 2) : ℝ :=
  1 + ∑ x, ∑ y, ‖(BAMomentExpGen_Df ω).G x y - (BAMomentExpGen_Df ω).M x y‖

private theorem BAMomentExpGen_Ψ_one (ω : Ω 3 4 2) : 1 ≤ BAMomentExpGen_Ψ ω := by
  unfold BAMomentExpGen_Ψ
  have : 0 ≤ ∑ x, ∑ y, ‖(BAMomentExpGen_Df ω).G x y - (BAMomentExpGen_Df ω).M x y‖ :=
    Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ => norm_nonneg _
  linarith

private theorem BAMomentExpGen_Ψ_le (ω : Ω 3 4 2) (x y : Idx 3 4 2) :
    ‖(BAMomentExpGen_Df ω).G x y - (BAMomentExpGen_Df ω).M x y‖ ≤ BAMomentExpGen_Ψ ω := by
  unfold BAMomentExpGen_Ψ
  have h1 : ‖(BAMomentExpGen_Df ω).G x y - (BAMomentExpGen_Df ω).M x y‖ ≤ ∑ b, ‖(BAMomentExpGen_Df ω).G x b - (BAMomentExpGen_Df ω).M x b‖ :=
    Finset.single_le_sum (f := fun b => ‖(BAMomentExpGen_Df ω).G x b - (BAMomentExpGen_Df ω).M x b‖) (fun b _ => norm_nonneg _)
      (Finset.mem_univ y)
  have h2 : ∑ b, ‖(BAMomentExpGen_Df ω).G x b - (BAMomentExpGen_Df ω).M x b‖ ≤
      ∑ a, ∑ b, ‖(BAMomentExpGen_Df ω).G a b - (BAMomentExpGen_Df ω).M a b‖ :=
    Finset.single_le_sum (f := fun a => ∑ b, ‖(BAMomentExpGen_Df ω).G a b - (BAMomentExpGen_Df ω).M a b‖)
      (fun a _ => Finset.sum_nonneg fun b _ => norm_nonneg _) (Finset.mem_univ x)
  linarith

/-- the block distance of the labels `ℓ0` is `1` -/
private theorem BAMomentExpGen_ℓ0_dist : lwBdist 3 4 2 (ℓ0 0) (ℓ0 1) = 1 := by
  unfold lwBdist
  have h0 : split 3 4 2 (ℓ0 0) = ((0 : Zd 3 4), (0 : Fin (2 ^ 3))) := by
    have e : ℓ0 0 = (splitEquiv 3 4 2).symm ((0 : Zd 3 4), (0 : Fin (2 ^ 3))) := by simp [ℓ0]
    rw [e]
    exact Equiv.apply_symm_apply (splitEquiv 3 4 2) _
  have h1 : split 3 4 2 (ℓ0 1) = ((Pi.single 0 1 : Zd 3 4), (0 : Fin (2 ^ 3))) := by
    have e : ℓ0 1 = (splitEquiv 3 4 2).symm ((Pi.single 0 1 : Zd 3 4), (0 : Fin (2 ^ 3))) := by simp [ℓ0]
    rw [e]
    exact Equiv.apply_symm_apply (splitEquiv 3 4 2) _
  rw [h0, h1]
  decide +kernel

/-- a start term of the partition of `fxyPowGraph 2` with its provenance map and the coverage of its internal shadow molecules (`BAProv_start`) -/
private theorem BAMomentExpGen_start : ∃ o : BAProvOut (baPG (BAGraph.ofLGraph (fxyPowGraph 2))),
    o.Q ∈ (BAGraph.ofLGraph (fxyPowGraph 2)).partition ∧
      BACoverBy (P := o.Q) fun k : Fin 2 => o.π (Sum.inr (localReg_fxyBeta k)) := by
  have hlen : ((BAGraph.ofLGraph (fxyPowGraph 2)).partition).length = 16 := by
    rw [BAGraph.partition, List.length_map]; decide +kernel
  have hmem : _ ∈ (BAGraph.ofLGraph (fxyPowGraph 2)).partition :=
    List.getElem_mem (show 0 < ((BAGraph.ofLGraph (fxyPowGraph 2)).partition).length by omega)
  obtain ⟨o, ho, -, -, hcov⟩ := BAProv_start 2 _ hmem
  exact ⟨o, ho ▸ hmem, hcov⟩

/-- the weight `Π_k 1_{0}` of a start term takes the values `1` (labels in the block `0`) and `0` (labels in the block `e₀`) -/
private theorem BAMomentExpGen_wt_vals (o : BAProvOut (baPG (BAGraph.ofLGraph (fxyPowGraph 2)))) :
    (∃ ℓ, BAMomentExp_wt szP 0 ({0} : Finset (Zd 3 4)) o ℓ = 1) ∧ ∃ ℓ, BAMomentExp_wt szP 0 ({0} : Finset (Zd 3 4)) o ℓ = 0 := by
  refine ⟨⟨fun _ => (splitEquiv 3 4 2).symm ((0 : Zd 3 4), (0 : Fin (2 ^ 3))), ?_⟩,
    ⟨fun _ => (splitEquiv 3 4 2).symm ((Pi.single 0 1 : Zd 3 4), (0 : Fin (2 ^ 3))), ?_⟩⟩
  · change (∏ k : Fin 2, if (split 3 4 2 ((splitEquiv 3 4 2).symm ((0 : Zd 3 4), (0 : Fin (2 ^ 3))))).1 ∈ ({0} : Finset (Zd 3 4))
      then (1 : ℝ) else 0) = 1
    rw [show split 3 4 2 ((splitEquiv 3 4 2).symm ((0 : Zd 3 4), (0 : Fin (2 ^ 3)))) = ((0 : Zd 3 4), (0 : Fin (2 ^ 3))) from
      Equiv.apply_symm_apply (splitEquiv 3 4 2) _]
    simp
  · change (∏ k : Fin 2, if (split 3 4 2 ((splitEquiv 3 4 2).symm ((Pi.single 0 1 : Zd 3 4), (0 : Fin (2 ^ 3))))).1 ∈ ({0} : Finset (Zd 3 4))
      then (1 : ℝ) else 0) = 0
    rw [show split 3 4 2 ((splitEquiv 3 4 2).symm ((Pi.single 0 1 : Zd 3 4), (0 : Fin (2 ^ 3)))) =
      ((Pi.single 0 1 : Zd 3 4), (0 : Fin (2 ^ 3))) from Equiv.apply_symm_apply (splitEquiv 3 4 2) _]
    have hne : ¬ ((Pi.single 0 1 : Zd 3 4) ∈ ({0} : Finset (Zd 3 4))) := by decide +kernel
    simp [hne]

/-- **Instance of target 4 (a) and (d)** at the flow point: for a start term `o` and the weight `Π_k 1_{0}` (taking the values `1` and `0`), the weighted packed value at
`BAlwData` is `t₀^{n_W}` times its value at the rescaled data, for every sample `ω`. -/
example (ω : Ω 3 4 2) : ∃ o : BAProvOut (baPG (BAGraph.ofLGraph (fxyPowGraph 2))),
    o.Q ∈ (BAGraph.ofLGraph (fxyPowGraph 2)).partition ∧
    ((∃ ℓ, BAMomentExp_wt szP 0 ({0} : Finset (Zd 3 4)) o ℓ = 1) ∧ ∃ ℓ, BAMomentExp_wt szP 0 ({0} : Finset (Zd 3 4)) o ℓ = 0) ∧
    o.Q.valW (BAlwData 3 4 2 g0P EP t0P m0P ω) (BAMomentExp_wt szP 0 ({0} : Finset (Zd 3 4)) o) ℓ0 =
      (t0P : ℂ) ^ o.Q.g.nW * o.Q.valW (BAExp14d_dataT 3 4 2 g0P EP t0P m0P ω) (BAMomentExp_wt szP 0 ({0} : Finset (Zd 3 4)) o) ℓ0 := by
  obtain ⟨o, ho, -⟩ := BAMomentExpGen_start
  exact ⟨o, ho, BAMomentExpGen_wt_vals o, BAMomentExp_valW_scale 3 4 2 (by norm_num) g0P _ EP t0P m0P flowP_real flowP_data.1.le
    flowP_data.2.1 ω o.Q _ ℓ0⟩

/-- **Instance of target 4 (b)** at the flow point: the weighted claim `size` for the packed start term `o.Q` at the rescaled data, with the constants of
`BAMomentGen_consts` (`d = 3`, `Λ = 10`, `κ = Im m_S`). -/
example (ω : Ω 3 4 2) : ∃ C c Kd : ℝ, ∃ o : BAProvOut (baPG (BAGraph.ofLGraph (fxyPowGraph 2))),
    o.Q ∈ (BAGraph.ofLGraph (fxyPowGraph 2)).partition ∧
    ‖o.Q.valW (BAExp14d_dataT 3 4 2 g0P EP t0P m0P ω) (BAMomentExp_wt szP 0 ({0} : Finset (Zd 3 4)) o) ℓ0‖ ≤
      o.Q.g.sizeConst C (C * expC (3 - 2) c) Kd * o.Q.g.scalingSize (BAMomentExpGen_Ψ ω) 2 3 4 := by
  obtain ⟨C, c, Kd, hC1, hc0, hKd, H⟩ := BAMomentGen_consts 3 le_rfl 10 (mS 4 10).im (by norm_num) (selfS 4 10).1
  obtain ⟨hSd, hSpd, hMPd, hoff, hS, hSp, hM, hP⟩ := H 4 2 (by norm_num) g0P EP t0P m0P g0P_pos g0P_le flowP_real flowP_data.1.le
    flowP_data.2.1 (BAExp14d_dataT 3 4 2 g0P EP t0P m0P ω) rfl rfl rfl rfl
  obtain ⟨o, ho, -⟩ := BAMomentExpGen_start
  exact ⟨C, c, Kd, o, ho, BAMomentExp_pvalW_claim o.Q (BAGraph.partition_normal _ _ ho) (BAExp14d_dataT 3 4 2 g0P EP t0P m0P ω)
    (BAMomentExpGen_Ψ_le ω) hS hSp hM hP (by linarith) (mul_nonneg (by linarith) (by unfold expC; positivity)) hKd ℓ0 _
    (BAMomentExp_wt_abs szP 0 _ o)⟩

/-- **Instance of target 4 (c)**: the weighted scale-mole tail at the graph `G0` of `Graph/BASymm1.lean` (externals `v0`, `v1` in one molecule through the waved edge
`S⁺_{v0 v1}`), the labels `ℓ0` at block distance `1 > |E ⊕ I| r = 5 · (1/10)`, a weight in `{0, 1}`, and the rescaled data at the flow point. -/
example (ω : Ω 3 4 2) : ∃ C c : ℝ, 0 ≤ C ∧ 0 < c ∧
    ‖G0.valW (BAExp14d_dataT 3 4 2 g0P EP t0P m0P ω) (fun ℓ => if (split 3 4 2 (ℓ (Sum.inl 0))).1 = 0 then 1 else 0) ℓ0‖ ≤
      Real.exp (-(c * (1 / 10) / 2)) * G0.sizeConst C (C * expC (3 - 2) (c / 2)) (C * (1 + expC (3 - 2) (c / 2))) *
        G0.scalingSize (BAMomentExpGen_Ψ ω) 2 3 4 := by
  obtain ⟨C, c, Kd, hC1, hc0, hKd, H⟩ := BAMomentGen_consts 3 le_rfl 10 (mS 4 10).im (by norm_num) (selfS 4 10).1
  obtain ⟨hSd, hSpd, hMPd, hoff, -⟩ := H 4 2 (by norm_num) g0P EP t0P m0P g0P_pos g0P_le flowP_real flowP_data.1.le
    flowP_data.2.1 (BAExp14d_dataT 3 4 2 g0P EP t0P m0P ω) rfl rfl rfl rfl
  have hfar : (Fintype.card (Fin 2 ⊕ Fin 3) : ℝ) * (1 / 10) < (lwBdist 3 4 2 (ℓ0 0) (ℓ0 1) : ℝ) := by
    rw [BAMomentExpGen_ℓ0_dist]; norm_num
  exact ⟨C, c, by linarith, hc0, BAMomentExp_scalemole le_rfl G0 G0_normal (BAExp14d_dataT 3 4 2 g0P EP t0P m0P ω)
    (BAMomentExpGen_Ψ_le ω) (by linarith) hc0 hSd hSpd hMPd hoff (by norm_num) _
    (fun ℓ => by split_ifs <;> norm_num) ℓ0 0 1 (by decide) hfar⟩

/-- **Instance (v) of target 5** (the BA rooted G3): a start term `o` of the partition of `fxyPowGraph 2`, the roots `rep` of its internal shadow molecules from its
coverage (`BACoverBy.rep`), the weight `Π_k 1_{0}` (values `1` and `0`; `|Wt| ≤ 1`, vanishing unless every root block is in `Dm = {0}`), the rescaled data at the
flow point (`Λ = 10`, `κ = Im m_S`, `A = 1/8`, `r = 1`, `R = |E ⊕ I| r`, `ξ ≡ Ψ`, every `ω`): the weighted value `BAGraph.valW` is bounded by the auxiliary graph of the
shadow summed over `Dm`. -/
example (ω : Ω 3 4 2) : ∃ K₀ K₁ Kd C c : ℝ, 0 < K₀ ∧ 0 < K₁ ∧ 0 ≤ Kd ∧ 0 ≤ C ∧ 0 < c ∧
    ∃ (o : BAProvOut (baPG (BAGraph.ofLGraph (fxyPowGraph 2)))) (rep : LGraph.AuxIMol o.Q.g.shadow → o.Q.I'),
      o.Q ∈ (BAGraph.ofLGraph (fxyPowGraph 2)).partition ∧ (∀ c, o.Q.g.shadow.molOf (Sum.inr (rep c)) = c.1) ∧
      ((∃ ℓ, BAMomentExp_wt szP 0 ({0} : Finset (Zd 3 4)) o ℓ = 1) ∧ ∃ ℓ, BAMomentExp_wt szP 0 ({0} : Finset (Zd 3 4)) o ℓ = 0) ∧
      ‖o.Q.g.valW (BAExp14d_dataT 3 4 2 g0P EP t0P m0P ω) (BAMomentExp_wt szP 0 ({0} : Finset (Zd 3 4)) o) (fun _ => ℓ0 0)‖ ≤
        o.Q.g.sizeConst (K₀ * (1 / 8)) K₁ Kd * BAMomentExpGen_Ψ ω ^ (o.Q.g.scalingOrder - o.Q.g.auxOrd) *
            ((((2 : ℕ) : ℝ) ^ 3) ^ o.Q.g.nM *
              auxValOn o.Q.g.shadow (fun _ _ => BAMomentExpGen_Ψ ω) (fun a => (split 3 4 2 ((fun _ : o.Q.E' => ℓ0 0) a)).1)
                ({0} : Finset (Zd 3 4))) +
          Real.exp (-(c * 1 / 2)) * o.Q.g.sizeConst C (C * expC (3 - 2) (c / 2)) (C * (1 + expC (3 - 2) (c / 2))) *
            o.Q.g.scalingSize (BAMomentExpGen_Ψ ω) 2 3 4 := by
  obtain ⟨K₀, K₁, Kd, C, c, hK₀, hK₁, hKd, hC, hc, H⟩ := baGtoAGTRooted_holds 3 le_rfl 10 (mS 4 10).im (by norm_num) (selfS 4 10).1
  obtain ⟨o, ho, hcov⟩ := BAMomentExpGen_start
  obtain ⟨rep, hrep, hWt0⟩ := BAMomentExpGen_rep szP o hcov 0 ({0} : Finset (Zd 3 4))
  have hΨ1 := BAMomentExpGen_Ψ_one ω
  have hwin : (((2 : ℕ) : ℝ) ^ 3)⁻¹ ≤ 1 / 8 * BAMomentExpGen_Ψ ω ^ 2 := by
    have h8 : ((2 : ℕ) : ℝ) ^ 3 = 8 := by norm_num
    rw [h8]
    nlinarith
  refine ⟨K₀, K₁, Kd, C, c, hK₀, hK₁, hKd, hC, hc, o, rep, ho, hrep, BAMomentExpGen_wt_vals o, ?_⟩
  exact H 4 2 (by norm_num) g0P EP t0P m0P g0P_pos g0P_le flowP_real flowP_data.1.le flowP_data.2.1 o.Q.E' o.Q.I' o.Q.g
    (BAGraph.partition_normal _ _ ho) rep hrep (BAExp14d_dataT 3 4 2 g0P EP t0P m0P ω) rfl rfl rfl rfl (BAMomentExpGen_Ψ ω) (1 / 8) 1
    (Fintype.card (o.Q.E' ⊕ o.Q.I') * 1) (fun _ _ => BAMomentExpGen_Ψ ω) {0} (BAMomentExpGen_Ψ_le ω) (by norm_num)
    hwin (by norm_num) le_rfl (fun _ _ => by linarith) (fun x y a b _ _ => BAMomentExpGen_Ψ_le ω x y)
    (BAMomentExp_wt szP 0 {0} o) (BAMomentExp_wt_abs szP 0 _ o) hWt0 (fun _ => ℓ0 0)

end InstFlow

end RBM.BA

end
