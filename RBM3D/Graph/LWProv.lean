/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Graph.LWEngine
import RBM3D.Graph.LWMoment

/-!
# LW-13b R1 (T2358): the provenance engine

Statements = the T2348 probe (`t/T2348:RBM3D/Probe/T2348Pins.lean:29-185, 291-310`), with
`LWExpData` written inline (C3) and the hypothesis `P.g.Normal` of the step lemma
(Amend 1).
Namespace `RBM.Graph`, prefix `lwProv_`.

The pinned step lemma is `lwProv_locStepXProvPos_holds : lwProv_LocStepXProvPos` (Amend 2):
the position-indexed provenance step, one map per position of the output list
(`lwProv_stepPos`). `lw_localregularXP` is proved from it.
-/

set_option linter.style.whitespace false
set_option linter.style.longLine false
set_option linter.style.setOption false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.flexible false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false

noncomputable section
open MeasureTheory Matrix Filter
open RBM RBM.Gauss RBM.Green RBM.Graph RBM.Gauss.Sizes

namespace RBM.Graph

/-! ## 1. Weighted values, provenance maps, the generic lemma over `LocStepX` -/

section Weighted

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- value of a graph with a **real weight on the labellings of all its vertices** (`W ≡ 1` is `LGraph.val`) -/
def valW {E I : Type} [Fintype I] [DecidableEq I] (Γ : LGraph E I) (D : LData ι) (W : (E ⊕ I → ι) → ℝ)
    (ℓe : E → ι) : ℂ :=
  ∑ ℓi : I → ι, ((W (Sum.elim ℓe ℓi) : ℝ) : ℂ) * Γ.term D (Sum.elim ℓe ℓi)

/-- the weighted value of a packed graph (`PGraph.val` with the weight) -/
def pvalW {E : Type} (P : PGraph E) (D : LData ι) (W : (P.E' ⊕ P.I' → ι) → ℝ) (ℓe : E → ι) : ℂ :=
  open Classical in
  if h : ∃ ℓ' : P.E' → ι, ℓe = ℓ' ∘ P.ext then valW P.g D W h.choose else 0

theorem valW_one {E I : Type} [Fintype I] [DecidableEq I] (Γ : LGraph E I) (D : LData ι) (ℓe : E → ι) :
    valW Γ D (fun _ => 1) ℓe = Γ.val D ℓe := by
  simp [valW, LGraph.val]

theorem pvalW_one {E : Type} (P : PGraph E) (D : LData ι) (ℓe : E → ι) :
    pvalW P D (fun _ => 1) ℓe = P.val D ℓe := by
  unfold pvalW PGraph.val
  simp only [valW_one]

end Weighted

/-- an output `Q` of a step from `P`, with its **provenance map** `π` (old vertex ↦ vertex of the output) -/
structure ProvOut (P : PGraph (Fin 2)) where
  Q : PGraph (Fin 2)
  π : P.E' ⊕ P.I' → Q.E' ⊕ Q.I'

/-- the external vertices go to the external vertices: old external labels are read consistently -/
def ProvOut.ExtOK {P : PGraph (Fin 2)} (o : ProvOut P) : Prop := ∀ i : Fin 2, o.π (Sum.inl (P.ext i)) = Sum.inl (o.Q.ext i)

/-- `π` is **molecular**: a molecule goes into a molecule, and every internal molecule of the output is the image of an internal
molecule of the input (no new molecule: every new vertex is joined to an old one by a path of dotted or waved edges, `7_8:351`; the waved edges of the input are kept) -/
def ProvOut.Molecular {P : PGraph (Fin 2)} (o : ProvOut P) : Prop :=
  (∀ v w, P.g.molOf v = P.g.molOf w → o.Q.g.molOf (o.π v) = o.Q.g.molOf (o.π w)) ∧
    ∀ c : o.Q.g.Mol, ¬ o.Q.g.IsExtMol c → ∃ v, ¬ P.g.IsExtMol (P.g.molOf v) ∧ o.Q.g.molOf (o.π v) = c

/-- **weighted expansion**: for every real weight `W` on the labellings of the vertices of `P`, the expectation of the weighted
value of `P` is the sum over the outputs of the expectations of their weighted values, the weight read through `π`.
(The nine conjuncts of the data are written inline, as in conjunct 4 of `LWLocRegConcl`, `LWEngine.lean:68-75`.) -/
def WExp (m : ℂ) (P : PGraph (Fin 2)) (outs : List (ProvOut P)) : Prop :=
  ∀ {d : ℕ} {sz : Sizes d} {n : ℕ} {z : ℂ} {u : ℝ}
    (Sp M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ),
    GaussIBP sz → 0 < z.im → 0 < u → m ≠ 0 → z + (u : ℂ) * m = -m⁻¹ →
    (∀ i j, Sp i j - m ^ 2 * ∑ w, Sp i w * lwS sz n u w j = lwS sz n u i j) → Spᵀ = Sp →
    (∀ a, M a a = m) → (∀ a b, a ≠ b → M a b = 0) →
    ∀ (W : (P.E' ⊕ P.I' → Idx d (sz.L n) (sz.W n)) → ℝ) (ℓe : Fin 2 → Idx d (sz.L n) (sz.W n)),
      ∫ ω, pvalW P (lwSampleData sz n z u M (lwS sz n u) Sp ω) W ℓe ∂(Sizes.seqP sz) =
        (outs.map fun o => ∫ ω, pvalW o.Q (lwSampleData sz n z u M (lwS sz n u) Sp ω)
          (fun ℓ => W (ℓ ∘ o.π)) ℓe ∂(Sizes.seqP sz)).sum

/-- composition of provenance maps -/
def ProvOut.comp {P : PGraph (Fin 2)} (o : ProvOut P) (o' : ProvOut o.Q) : ProvOut P := ⟨o'.Q, o'.π ∘ o.π⟩

theorem ProvOut.Molecular.comp {P : PGraph (Fin 2)} {o : ProvOut P} {o' : ProvOut o.Q} (h : o.Molecular)
    (h' : o'.Molecular) : (o.comp o').Molecular := by
  refine ⟨fun v w hvw => h'.1 _ _ (h.1 v w hvw), fun c hc => ?_⟩
  obtain ⟨v', hv', hc'⟩ := h'.2 c hc
  obtain ⟨v, hv, hvv⟩ := h.2 _ hv'
  exact ⟨v, hv, (h'.1 _ _ hvv).trans hc'⟩

/-- a leaf of the recursion: the graph itself with the identity map -/
theorem WExp.refl (m : ℂ) (P : PGraph (Fin 2)) : WExp m P [⟨P, id⟩] := by
  intro d sz n z u Sp M _ _ _ _ _ _ _ _ _ W ℓe; simp

/-- **the recursion step** (`lwEngine_combine`, `LWEngine.lean:628`, with maps): if `P` expands into `outs` and each output
expands into `outs' o`, then `P` expands into the composites, the maps composing. -/
theorem WExp.comp {m : ℂ} {P : PGraph (Fin 2)} {outs : List (ProvOut P)} (h : WExp m P outs)
    (outs' : ∀ o : ProvOut P, List (ProvOut o.Q)) (h' : ∀ o ∈ outs, WExp m o.Q (outs' o)) :
    WExp m P (outs.flatMap fun o => (outs' o).map o.comp) := by
  intro d sz n z u Sp M hG hz hu hm0 hzm hSp hSpT hM hM0 W ℓe
  rw [h Sp M hG hz hu hm0 hzm hSp hSpT hM hM0 W ℓe, lvl1_sum_flatMap]
  refine congrArg List.sum (List.map_congr_left fun o ho => ?_)
  rw [h' o ho Sp M hG hz hu hm0 hzm hSp hSpT hM hM0 (fun ℓ => W (ℓ ∘ o.π)) ℓe, List.map_map]
  rfl

/-- **the weighted identity of the ticket**: `W = Π_k w_k(ℓ β^{(k)})` gives `E[Π_k f^{w_k}] = Σ_r E[Σ_{ℓ_i} Π_k w_k(ℓ(π_r β^{(k)})) term_r]` -/
theorem WExp.prod {m : ℂ} {p : ℕ} {outs : List (ProvOut (fxyPowGraph p).pack)} (h : WExp m (fxyPowGraph p).pack outs)
    {d : ℕ} {sz : Sizes d} {n : ℕ} {z : ℂ} {u : ℝ} (Sp M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    (hG : GaussIBP sz) (hz : 0 < z.im) (hu : 0 < u) (hm0 : m ≠ 0) (hzm : z + (u : ℂ) * m = -m⁻¹)
    (hSp : ∀ i j, Sp i j - m ^ 2 * ∑ w, Sp i w * lwS sz n u w j = lwS sz n u i j) (hSpT : Spᵀ = Sp)
    (hM : ∀ a, M a a = m) (hM0 : ∀ a b, a ≠ b → M a b = 0)
    (w : Fin p → Idx d (sz.L n) (sz.W n) → ℝ) (ℓe : Fin 2 → Idx d (sz.L n) (sz.W n)) :
    ∫ ω, pvalW (fxyPowGraph p).pack (lwSampleData sz n z u M (lwS sz n u) Sp ω)
        (fun ℓ => ∏ k, w k (ℓ (Sum.inr (localReg_fxyBeta k)))) ℓe ∂(Sizes.seqP sz) =
      (outs.map fun o => ∫ ω, pvalW o.Q (lwSampleData sz n z u M (lwS sz n u) Sp ω)
        (fun ℓ => ∏ k, w k (ℓ (o.π (Sum.inr (localReg_fxyBeta k))))) ℓe ∂(Sizes.seqP sz)).sum :=
  h Sp M hG hz hu hm0 hzm hSp hSpT hM hM0 _ ℓe

/-- every internal molecule of `P` contains a vertex of the family `β` -/
def CoverBy {P : PGraph (Fin 2)} {κ : Type} (β : κ → P.E' ⊕ P.I') : Prop :=
  ∀ c : P.g.Mol, ¬ P.g.IsExtMol c → ∃ k, P.g.molOf (β k) = c

/-- **molecule coverage propagates**: the images of the initial `β^{(k)}` cover the internal molecules of every output
(`T2289d`, `T2289-prove.md:103`, read at the molecule level as in supervisor 2244 R1: the weight on `β^{(k)}` restricts every auxiliary internal vertex) -/
theorem CoverBy.comp {P : PGraph (Fin 2)} {κ : Type} {β : κ → P.E' ⊕ P.I'} (h : CoverBy β) {o : ProvOut P}
    (ho : o.Molecular) : CoverBy (P := o.Q) (fun k => o.π (β k)) := by
  intro c hc
  obtain ⟨v, hv, hvc⟩ := ho.2 c hc
  obtain ⟨k, hk⟩ := h _ hv
  exact ⟨k, by rw [← hvc]; exact ho.1 _ _ hk⟩

/-- an output of a step with its tag (the exponents of `m`, `m̄` of the coefficient) and provenance map -/
structure ProvOutX (P : PGraph (Fin 2)) where
  tag : ℕ × ℕ
  Q : PGraph (Fin 2)
  π : P.E' ⊕ P.I' → Q.E' ⊕ Q.I'

/-- the output evaluated at `m` -/
def ProvOutX.ev (m : ℂ) {P : PGraph (Fin 2)} (o : ProvOutX P) : ProvOut P := ⟨lwEvX m (o.tag, o.Q), o.π⟩

def ProvOutX.ExtOK {P : PGraph (Fin 2)} (o : ProvOutX P) : Prop := (⟨o.Q, o.π⟩ : ProvOut P).ExtOK

/-- **coverage at the start graph**: every internal molecule of the output contains the image of some initial `β^{(k)}` -/
def ProvOutX.Cover (p : ℕ) (o : ProvOutX (fxyPowGraph p).pack) : Prop :=
  CoverBy (P := o.Q) fun k : Fin p => o.π (Sum.inr (localReg_fxyBeta k))

/-- the outputs of a step, evaluated at `m` with the input tag `t0`, with their maps -/
def mkProv (m : ℂ) (t0 : ℕ × ℕ) (P : PGraph (Fin 2)) (r : (ℕ × ℕ) × PGraph (Fin 2))
    (π : P.E' ⊕ P.I' → r.2.E' ⊕ r.2.I') : ProvOut (lwEvX m (t0, P)) := ⟨lwEvX m (lwEngine_shift t0 r), π⟩

def stepOuts (m : ℂ) (t0 : ℕ × ℕ) (P : PGraph (Fin 2)) (LX : List ((ℕ × ℕ) × PGraph (Fin 2)))
    (π : ∀ r ∈ LX, P.E' ⊕ P.I' → r.2.E' ⊕ r.2.I') : List (ProvOut (lwEvX m (t0, P))) :=
  LX.attach.map fun r => mkProv m t0 P r.1 (π r.1 r.2)

/-- **`lw_localregularX` with provenance** (the statement of the engine row) -/
def LWEngineProv : Prop :=
  ∀ (p : ℕ) (c : ℝ), 0 < c → ∀ (K0 d : ℕ) (D : ℝ),
    ∃ outs errs : List (ProvOutX (fxyPowGraph p).pack),
      (∀ o ∈ outs ++ errs, o.ExtOK ∧ o.Cover p) ∧ ∀ m : ℂ, m ≠ 0 →
        LWLocRegConcl p m c K0 d D ((outs.map (·.ev m)).map (·.Q)) ((errs.map (·.ev m)).map (·.Q)) ∧
        (∀ Q ∈ ((outs ++ errs).map (·.ev m)).map (·.Q), p ≤ Q.g.waved.countP (fun e => !e.col)) ∧
        WExp m (fxyPowGraph p).pack ((outs ++ errs).map (·.ev m))

/-- the engine with provenance strengthens the merged `lw_localregularX` (`LWEngine.lean:771-775`) -/
theorem lwEngineProv_imp_localregularX (h : LWEngineProv) : ∀ (p : ℕ) (c : ℝ), 0 < c → ∀ (K0 d : ℕ) (D : ℝ),
    ∃ outsX errsX : List ((ℕ × ℕ) × PGraph (Fin 2)), ∀ m : ℂ, m ≠ 0 →
      LWLocRegConcl p m c K0 d D (outsX.map (lwEvX m)) (errsX.map (lwEvX m)) ∧
      ∀ Q ∈ outsX.map (lwEvX m) ++ errsX.map (lwEvX m), p ≤ Q.g.waved.countP (fun e => !e.col) := by
  intro p c hc K0 d D
  obtain ⟨outs, errs, -, H⟩ := h p c hc K0 d D
  refine ⟨outs.map fun o => (o.tag, o.Q), errs.map fun o => (o.tag, o.Q), fun m hm => ?_⟩
  obtain ⟨h1, h2, -⟩ := H m hm
  simp only [List.map_map, Function.comp_def, ProvOutX.ev] at h1 h2 ⊢
  refine ⟨h1, fun Q hQ => h2 Q ?_⟩
  simpa [List.map_append, List.map_map, Function.comp_def, ProvOutX.ev] using hQ

/-- `f_{xy}` with the sum over `β` restricted to the blocks in `D` (`f^{>ℓ}`, `f^{≤ℓ}`, `7_8:1607-1611`); `D = univ` is `LWf` -/
def LWfD {d : ℕ} (sz : Sizes d) (n : ℕ) (E t : ℝ) (ω : sz.SeqΩ) (D : Finset (Zd d (sz.L n)))
    (x y : Idx d (sz.L n) (sz.W n)) : ℂ :=
  ∑ α, if α = x ∨ α = y then 0 else
    ∑ β, if STblk sz n β ∈ D then (LWS sz n α β : ℂ) * STGM sz n E t ω β β * Gt sz n E t true ω x α * Gt sz n E t true ω α y
      else 0

theorem LWfD_union {d : ℕ} (sz : Sizes d) (n : ℕ) (E t : ℝ) (ω : sz.SeqΩ) {D₁ D₂ : Finset (Zd d (sz.L n))}
    (h : Disjoint D₁ D₂) (x y : Idx d (sz.L n) (sz.W n)) :
    LWfD sz n E t ω (D₁ ∪ D₂) x y = LWfD sz n E t ω D₁ x y + LWfD sz n E t ω D₂ x y := by
  unfold LWfD
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun α _ => ?_
  split_ifs with hα
  · simp
  · rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun β _ => ?_
    by_cases h1 : STblk sz n β ∈ D₁
    · simp [h1, Finset.disjoint_left.1 h h1]
    · by_cases h2 : STblk sz n β ∈ D₂ <;> simp [h1, h2]


/-! ## 2. The weighted `|f|^p` bridge (C1) -/

section Bridge

theorem lwProv_pvalW_of_factor {E : Type} {ι : Type*} [Fintype ι] [DecidableEq ι] (P : PGraph E) (D : LData ι)
    (W : (P.E' ⊕ P.I' → ι) → ℝ) {ℓe : E → ι} {ℓ' : P.E' → ι} (h : ℓe = ℓ' ∘ P.ext) :
    pvalW P D W ℓe = valW P.g D W ℓ' := by
  classical
  have hex : ∃ ℓ'' : P.E' → ι, ℓe = ℓ'' ∘ P.ext := ⟨ℓ', h⟩
  simp only [pvalW, hex, ↓reduceDIte]
  congr 1
  apply P.ext_surj.injective_comp_right
  exact hex.choose_spec.symm.trans h

theorem lwProv_pvalW_of_not {E : Type} {ι : Type*} [Fintype ι] [DecidableEq ι] (P : PGraph E) (D : LData ι)
    (W : (P.E' ⊕ P.I' → ι) → ℝ) {ℓe : E → ι} (h : ¬ ∃ ℓ' : P.E' → ι, ℓe = ℓ' ∘ P.ext) :
    pvalW P D W ℓe = 0 := by
  classical
  simp only [pvalW, h, ↓reduceDIte]

/-- **the weighted `|f|^p` bridge** (C1): the weight `Π_k 1_D(blk ℓ β_k)` on the starting graph is `S ↦ 1_D(blk ·) S` in the data,
and the value is `f_D^{p/2} \bar{f_D}^{p/2}` (twin of `lwMoment_fxyPow_val`, `LWMoment.lean:1748`). -/
theorem lwProv_bridge {d : ℕ} (sz : Sizes d) {p : ℕ} (hp : Even p) (n : ℕ) (E t : ℝ) (ω : sz.SeqΩ)
    (D : Finset (Zd d (sz.L n))) (x y : Idx d (sz.L n) (sz.W n)) :
    pvalW (fxyPowGraph p).pack (lwMoment_D sz n E t ω)
      (fun ℓ => ∏ k : Fin p, if STblk sz n (ℓ (Sum.inr (localReg_fxyBeta k))) ∈ D then 1 else 0) ![x, y] =
      ((‖LWfD sz n E t ω D x y‖ ^ p : ℝ) : ℂ) := by
  classical
  let D0 := lwMoment_D sz n E t ω
  let D1 : LData (Idx d (sz.L n) (sz.W n)) :=
    { D0 with S := fun a b => (if STblk sz n b ∈ D then 1 else 0) * D0.S a b }
  have hS0 : ∀ i j, star (D0.S i j) = D0.S i j := fun i j => by simp [D0, lwMoment_D, lwSampleData, lwS]
  have hS1 : ∀ i j, star (D1.S i j) = D1.S i j := fun i j => by
    simp only [D1, star_mul', hS0]
    congr 1
    split_ifs <;> simp
  refine (lwProv_pvalW_of_factor (fxyPowGraph p).pack D0 _ (ℓ' := ![x, y]) rfl).trans ?_
  have hBV : ∀ (σ : Bool) (a b : Idx d (sz.L n) (sz.W n)), localReg_fxyBlockVal D1 x y σ a b =
      (if STblk sz n b ∈ D then 1 else 0 : ℂ) * localReg_fxyBlockVal D0 x y σ a b := by
    intro σ a b
    unfold localReg_fxyBlockVal
    change _ * ((if STblk sz n b ∈ D then 1 else 0 : ℂ) * D0.S a b) * _ = _
    ring
  have h1 : valW (fxyPowGraph p) D0 (fun ℓ => ∏ k : Fin p, if STblk sz n (ℓ (Sum.inr (localReg_fxyBeta k))) ∈ D then 1 else 0)
      ![x, y] = (fxyPowGraph p).val D1 ![x, y] := by
    unfold valW LGraph.val
    refine Finset.sum_congr rfl fun ℓi _ => ?_
    rw [localReg_fxy_term D0 p x y ℓi, localReg_fxy_term D1 p x y ℓi]
    simp only [Sum.elim_inr, hBV, Finset.prod_mul_distrib, Complex.ofReal_prod]
    congr 1
    refine Finset.prod_congr rfl fun k _ => ?_
    by_cases hk : STblk sz n (ℓi (localReg_fxyBeta k)) ∈ D <;> simp [hk]
  refine h1.trans ?_
  rw [fxyPowGraph_val_eq D1 hS1 p hp x y]
  have h2 : fxyVal D1 x y = LWfD sz n E t ω D x y := by
    unfold fxyVal LWfD
    refine Finset.sum_congr rfl fun α _ => ?_
    split_ifs with hα
    · rfl
    · refine Finset.sum_congr rfl fun β _ => ?_
      simp only [D1, D0, lwMoment_D, lwSampleData, lwS, Matrix.of_apply, Matrix.diagonal_apply_eq, STGM, ite_true,
        RBM.Gauss.Sizes.LWS]
      by_cases hb : STblk sz n β ∈ D
      · simp only [hb, ite_true, one_mul]; rfl
      · simp [hb]
  rw [h2]
  obtain ⟨k, hk⟩ := hp
  have hk2 : p / 2 = k := by omega
  have hk3 : 2 * k = p := by omega
  rw [hk2, lwMoment_pow_conj, hk3]

end Bridge


/-! ## 3. Molecular provenance maps -/

section Mol

variable {E I E' I' : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]
  [Fintype E'] [DecidableEq E'] [Fintype I'] [DecidableEq I']

/-- a map sending adjacent vertices to equal or adjacent vertices sends reachable vertices to reachable ones -/
theorem lwProv_reach_map (G : LGraph E I) (G' : LGraph E' I') (f : E ⊕ I → E' ⊕ I')
    (hadj : ∀ u v, G.adj u v = true → f u = f v ∨ G'.adj (f u) (f v) = true) {u v : E ⊕ I}
    (h : G.molGraph.Reachable u v) : G'.molGraph.Reachable (f u) (f v) := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at h ⊢
  refine Relation.ReflTransGen.lift' (p := G'.molGraph.Adj) f (fun a b hab => ?_) u v h
  obtain ⟨hne, hab⟩ := (owx_molGraph_adj G a b).1 hab
  change Relation.ReflTransGen G'.molGraph.Adj (f a) (f b)
  rcases hadj a b hab with h1 | h1
  · rw [h1]
  · by_cases h2 : f a = f b
    · rw [h2]
    · exact Relation.ReflTransGen.single ((owx_molGraph_adj G' _ _).2 ⟨h2, h1⟩)

/-- **a map that preserves adjacency and reaches every vertex of the target is `Molecular`** -/
theorem lwProv_molecular {P : PGraph (Fin 2)} (o : ProvOut P)
    (hadj : ∀ u v, P.g.adj u v = true → o.π u = o.π v ∨ o.Q.g.adj (o.π u) (o.π v) = true)
    (hreach : ∀ w : o.Q.E' ⊕ o.Q.I', ∃ v, o.Q.g.molGraph.Reachable w (o.π v))
    (hext : ∀ a : P.E', ∃ a' : o.Q.E', o.π (Sum.inl a) = Sum.inl a') : o.Molecular := by
  have h1 : ∀ v w, P.g.molOf v = P.g.molOf w → o.Q.g.molOf (o.π v) = o.Q.g.molOf (o.π w) := fun v w h =>
    SimpleGraph.ConnectedComponent.eq.2
      (lwProv_reach_map P.g o.Q.g o.π hadj (SimpleGraph.ConnectedComponent.eq.1 h))
  refine ⟨h1, fun c hc => ?_⟩
  induction c using SimpleGraph.ConnectedComponent.ind with | h w => ?_
  obtain ⟨v, hv⟩ := hreach w
  refine ⟨v, fun ⟨a, ha⟩ => ?_, SimpleGraph.ConnectedComponent.eq.2 hv.symm⟩
  obtain ⟨a', ha'⟩ := hext a
  refine hc ⟨a', ?_⟩
  have := h1 _ _ ha
  rw [ha'] at this
  exact this.trans (SimpleGraph.ConnectedComponent.eq.2 hv.symm)

end Mol

/-! ### The partition with vertex maps -/

section Part

variable {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

theorem lwProv_vmap_inl (Γ : LGraph E I) (a : E) : Γ.vmap (Sum.inl a) = Sum.inl (Γ.extMap a) := by
  have h : Γ.IsExtCls (Γ.cls (Sum.inl a)) := ⟨a, rfl⟩
  simp [LGraph.vmap, LGraph.vmapC, LGraph.extMap, h]

theorem lwProv_vmap_surj (Γ : LGraph E I) : Function.Surjective Γ.vmap := by
  rintro (⟨q, hq⟩ | ⟨q, hq⟩)
  · obtain ⟨v, rfl⟩ := Quotient.exists_rep q
    exact ⟨v, by simp [LGraph.vmap, LGraph.vmapC, hq]⟩
  · obtain ⟨v, rfl⟩ := Quotient.exists_rep q
    exact ⟨v, by simp [LGraph.vmap, LGraph.vmapC, hq]⟩

/-- merging keeps adjacency up to equality -/
theorem lwProv_merge_adj (Δ : LGraph E I) {u v : E ⊕ I} (h : Δ.adj u v = true) :
    Δ.vmap u = Δ.vmap v ∨ Δ.merge.adj (Δ.vmap u) (Δ.vmap v) = true := by
  simp only [LGraph.adj, Bool.or_eq_true, List.any_eq_true, decide_eq_true_eq, Bool.and_eq_true] at h
  rcases h with ⟨e, he, h⟩ | ⟨e, he, h1, h⟩
  · right
    simp only [LGraph.adj, Bool.or_eq_true, List.any_eq_true, decide_eq_true_eq]
    refine Or.inl ⟨WEdge.map Δ.vmap e, List.mem_map_of_mem he, ?_⟩
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left; simp [WEdge.map, h1, h2]
    · right; simp [WEdge.map, h1, h2]
  · left
    have hrel : Δ.EqRel u v := by
      rcases h with ⟨h2, h3⟩ | ⟨h2, h3⟩
      · exact ⟨e, he, h1, Or.inl ⟨h2, h3⟩⟩
      · exact ⟨e, he, h1, Or.inr ⟨h2, h3⟩⟩
    exact congrArg Δ.vmapC (Quotient.sound (Relation.EqvGen.rel _ _ hrel))

/-- the dotted edge expansion keeps adjacency -/
theorem lwProv_withDots_adj (Y : LGraph E I) (c : ℤ × List (DEdge (E ⊕ I))) {u v : E ⊕ I}
    (h : Y.adj u v = true) : (Y.withDots c).adj u v = true := by
  simp only [LGraph.adj, Bool.or_eq_true, List.any_eq_true, decide_eq_true_eq, Bool.and_eq_true] at h ⊢
  rcases h with ⟨e, he, h⟩ | ⟨e, he, h1, h⟩
  · exact Or.inl ⟨e, he, h⟩
  · refine Or.inr ⟨e, ?_, h1, h⟩
    simp only [LGraph.withDots, List.mem_append, LGraph.dotBase, List.mem_filter]
    exact Or.inl ⟨he, by simp [LGraph.isB, h1]⟩

end Part

section Part2

variable {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

/-- an output of the exponent-tracking dotted edge partition, with its tag and the vertex map of the merge -/
structure lwProv_Part (E I : Type) where
  tag : ℕ × ℕ
  Q : PGraph E
  vm : E ⊕ I → Q.E' ⊕ Q.I'

/-- the merge of `Δ` as a packed graph, with the solid edges `s` (the weights split) -/
def lwProv_mergeQ (Δ : LGraph E I) (s : List (SEdge (Δ.ExtCls ⊕ Δ.IntCls))) : PGraph E :=
  { E' := Δ.ExtCls, I' := Δ.IntCls, ext := Δ.extMap, ext_surj := Δ.extMap_surj, g := { Δ.merge with solid := s } }

/-- `Sizes.partitionX` with the vertex maps `Δ.vmap` of the merges -/
def lwProv_partX (Y : LGraph E I) : List (lwProv_Part E I) :=
  Y.partitionTerms.flatMap fun Δ =>
    (Sizes.lwSplitLoopsX Δ.merge.solid).map fun r => ⟨r.1, lwProv_mergeQ Δ r.2, Δ.vmap⟩

theorem lwProv_partX_map (Y : LGraph E I) :
    (lwProv_partX Y).map (fun o => (o.tag, o.Q)) = Sizes.partitionX Y := by
  simp [lwProv_partX, lwProv_mergeQ, Sizes.partitionX, List.map_flatMap, List.map_map, Function.comp_def]

/-- **the structure of the maps of the partition**: external vertices go to the external vertices, the map is onto, adjacent
vertices go to equal or adjacent vertices -/
theorem lwProv_partX_struct (Y : LGraph E I) (o : lwProv_Part E I) (ho : o ∈ lwProv_partX Y) :
    (∀ a : E, o.vm (Sum.inl a) = Sum.inl (o.Q.ext a)) ∧ Function.Surjective o.vm ∧
      ∀ u v, Y.adj u v = true → o.vm u = o.vm v ∨ o.Q.g.adj (o.vm u) (o.vm v) = true := by
  unfold lwProv_partX at ho
  obtain ⟨Δ, hΔ, ho⟩ := List.mem_flatMap.1 ho
  obtain ⟨r, hr, rfl⟩ := List.mem_map.1 ho
  unfold LGraph.partitionTerms at hΔ
  obtain ⟨hmem, -⟩ := List.mem_filter.1 hΔ
  obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hmem
  refine ⟨fun a => lwProv_vmap_inl _ a, lwProv_vmap_surj _, fun u v h => ?_⟩
  exact lwProv_merge_adj _ (lwProv_withDots_adj Y c h)

/-- the packed outputs of a term `Y` with tag `u`, read through `emb` from the vertices of `P` -/
def lwProv_blk (P : PGraph (Fin 2)) {I'' : Type} [Fintype I''] [DecidableEq I''] (u : ℕ × ℕ)
    (Y : LGraph P.E' I'') (emb : P.E' ⊕ P.I' → P.E' ⊕ I'') : List (ProvOutX P) :=
  (lwProv_partX Y).map fun o => ⟨u + o.tag, o.Q.lvl1Comp P.ext P.ext_surj, o.vm ∘ emb⟩

/-- `Y` is an extension of `Γ` along `emb`: adjacency is kept, external vertices are fixed, every vertex of `Y` is joined to an
image of a vertex of `Γ` -/
def lwProv_Ext {I'' : Type} [Fintype I''] [DecidableEq I''] (Γ : LGraph E I) (Y : LGraph E I'')
    (emb : E ⊕ I → E ⊕ I'') : Prop :=
  (∀ u v, Γ.adj u v = true → Y.adj (emb u) (emb v) = true) ∧ (∀ a : E, emb (Sum.inl a) = Sum.inl a) ∧
    ∀ w : E ⊕ I'', ∃ v : E ⊕ I, Y.molGraph.Reachable w (emb v)

end Part2

section Blk

/-- **every output of a block over an extension is `ExtOK` and `Molecular`** -/
theorem lwProv_blk_mol (P : PGraph (Fin 2)) {I'' : Type} [Fintype I''] [DecidableEq I''] (u : ℕ × ℕ)
    (Y : LGraph P.E' I'') (emb : P.E' ⊕ P.I' → P.E' ⊕ I'') (h : lwProv_Ext P.g Y emb) :
    ∀ o ∈ lwProv_blk P u Y emb, o.ExtOK ∧ (⟨o.Q, o.π⟩ : ProvOut P).Molecular := by
  intro o ho
  unfold lwProv_blk at ho
  obtain ⟨o', ho', rfl⟩ := List.mem_map.1 ho
  obtain ⟨h1, h2, h3⟩ := lwProv_partX_struct Y o' ho'
  obtain ⟨hA, hE, hR⟩ := h
  refine ⟨fun i => ?_, ?_⟩
  · change o'.vm (emb (Sum.inl (P.ext i))) = Sum.inl (o'.Q.ext (P.ext i))
    rw [hE, h1]
  · refine lwProv_molecular (⟨o'.Q.lvl1Comp P.ext P.ext_surj, o'.vm ∘ emb⟩ : ProvOut P) (fun u v huv => ?_) (fun w => ?_)
      (fun a => ⟨o'.Q.ext a, ?_⟩)
    · exact h3 _ _ (hA u v huv)
    · obtain ⟨t, rfl⟩ := h2 w
      obtain ⟨v, hv⟩ := hR t
      exact ⟨v, lwProv_reach_map Y o'.Q.g o'.vm h3 hv⟩
    · change o'.vm (emb (Sum.inl a)) = _
      rw [hE, h1]
      rfl

end Blk

section WeightStruct

variable {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

theorem lwProv_molGraph_congr {E' I' : Type} [Fintype E'] [DecidableEq E'] [Fintype I'] [DecidableEq I']
    {Γ₁ Γ₂ : LGraph E' I'} (h : Γ₁.adj = Γ₂.adj) : Γ₁.molGraph = Γ₂.molGraph := by
  unfold LGraph.molGraph; rw [h]

/-- **an expansion `owxExt` along `owxEmb k`, twisted, is an extension** (adjacency of the base `Z` is that of `Γ`; every new vertex
reaches an old one) -/
theorem lwProv_ext_twist (Γ Z : LGraph E I) (hZ : Z.adj = Γ.adj) (c t : Bool) (k : ℕ) (κ : ℂ)
    (s : List (SEdge (E ⊕ (I ⊕ Fin k)))) (w : List (WEdge (E ⊕ (I ⊕ Fin k))))
    (hr : ∀ v, ∃ v', (Z.owxExt (owxEmb k) κ s w).molGraph.Reachable v (owxEmb k v')) :
    lwProv_Ext Γ (lwSymmTwistG c t (Z.owxExt (owxEmb k) κ s w)) (owxEmb k) := by
  refine ⟨fun u v h => ?_, fun a => rfl, fun v => ?_⟩
  · rw [lwSymmTwistG_adj]
    exact oe2x_adj_owxExt Z (owxEmb k) κ s w u v (by rw [hZ]; exact h)
  · obtain ⟨v', hv'⟩ := hr v
    exact ⟨v', by rw [lwProv_molGraph_congr (lwSymmTwistG_adj c t _)]; exact hv'⟩

theorem lwProv_ext_twist1 (Γ Z : LGraph E I) (hZ : Z.adj = Γ.adj) (c t : Bool) (κ : ℂ)
    (s : List (SEdge (E ⊕ (I ⊕ Fin 1)))) (w : List (WEdge (E ⊕ (I ⊕ Fin 1)))) (x : E ⊕ I) (col σ : Bool)
    (hw : (⟨col, σ, owxEmb 1 x, Sum.inr (Sum.inr 0)⟩ : WEdge _) ∈ w) :
    lwProv_Ext Γ (lwSymmTwistG c t (Z.owxExt (owxEmb 1) κ s w)) (owxEmb 1) :=
  lwProv_ext_twist Γ Z hZ c t 1 κ s w fun v => ⟨_, lwSymmExt_reach1 Z x κ s w col σ hw v⟩

theorem lwProv_ext_twist2 (Γ Z : LGraph E I) (hZ : Z.adj = Γ.adj) (c t : Bool) (κ : ℂ)
    (s : List (SEdge (E ⊕ (I ⊕ Fin 2)))) (w : List (WEdge (E ⊕ (I ⊕ Fin 2)))) (x : E ⊕ I) (col σ col' σ' : Bool)
    (hw : (⟨col, σ, owxEmb 2 x, Sum.inr (Sum.inr 0)⟩ : WEdge _) ∈ w)
    (hw' : (⟨col', σ', Sum.inr (Sum.inr 0), Sum.inr (Sum.inr 1)⟩ : WEdge _) ∈ w) :
    lwProv_Ext Γ (lwSymmTwistG c t (Z.owxExt (owxEmb 2) κ s w)) (owxEmb 2) :=
  lwProv_ext_twist Γ Z hZ c t 2 κ s w fun v => ⟨_, lwSymmExt_reach2 Z x κ s w col σ col' σ' hw hw' v⟩

theorem lwProv_adj_solid (Γ : LGraph E I) (s : List (SEdge (E ⊕ I))) : ({ Γ with solid := s } : LGraph E I).adj = Γ.adj := rfl

end WeightStruct

section WeightList

/-- the outputs of Step 1 (`lvl1WeightOutsX`) with their vertex maps -/
def lwProv_weightOuts (P : PGraph (Fin 2)) (p : SEdge (P.E' ⊕ P.I') × List (SEdge (P.E' ⊕ P.I')))
    (x : P.E' ⊕ P.I') (c t : Bool) : List (ProvOutX P) :=
  lwProv_blk P (lwEngine_sw c (1, 0)) (lwSymmOwxT1 c t 1 P.g x) (owxEmb 1) ++
    lwProv_blk P (lwEngine_sw c (3, 0)) (lwSymmOwxT2 c t 1 P.g p x) (owxEmb 2) ++
    (lwSplit p.2).flatMap (fun q => lwProv_blk P (lwEngine_sw c (1, 0)) (lwSymmOwxT3 c t 1 P.g x q) (owxEmb 1)) ++
    (lwSplit p.2).flatMap (fun q => lwProv_blk P (lwEngine_sw c (3, 0)) (lwSymmOwxT4 c t 1 P.g x q) (owxEmb 2))

theorem lwProv_blk_map (P : PGraph (Fin 2)) {I'' : Type} [Fintype I''] [DecidableEq I''] (u : ℕ × ℕ)
    (Y : LGraph P.E' I'') (emb : P.E' ⊕ P.I' → P.E' ⊕ I'') :
    (lwProv_blk P u Y emb).map (fun o => (o.tag, o.Q)) = lvl1PackX P (lwEngine_blk u Y) := by
  have := lwProv_partX_map Y
  simp only [lwProv_blk, lvl1PackX, lwEngine_blk, List.map_map, Function.comp_def, lwEngine_shift]
  rw [← this, List.map_map]
  rfl

theorem lwProv_weightOuts_map (P : PGraph (Fin 2)) (p : SEdge (P.E' ⊕ P.I') × List (SEdge (P.E' ⊕ P.I')))
    (x : P.E' ⊕ P.I') (c t : Bool) :
    (lwProv_weightOuts P p x c t).map (fun o => (o.tag, o.Q)) = lvl1PackX P (lvl1WeightOutsX P.g p x c t) := by
  simp only [lwProv_weightOuts, lvl1WeightOutsX, lvl1PackX, List.map_append, List.map_flatMap, lwProv_blk_map]

theorem lwProv_weightOuts_mol (P : PGraph (Fin 2)) (p : SEdge (P.E' ⊕ P.I') × List (SEdge (P.E' ⊕ P.I')))
    (x : P.E' ⊕ P.I') (c t : Bool) :
    ∀ o ∈ lwProv_weightOuts P p x c t, o.ExtOK ∧ (⟨o.Q, o.π⟩ : ProvOut P).Molecular := by
  intro o ho
  simp only [lwProv_weightOuts, List.mem_append, List.mem_flatMap] at ho
  rcases ho with ((ho | ho) | ⟨q, hq, ho⟩) | ⟨q, hq, ho⟩
  · refine lwProv_blk_mol P _ _ _ ?_ o ho
    simp only [lwSymmOwxT1, owxET1]
    exact lwProv_ext_twist1 P.g (lwSymmTwistG c t P.g) (lwSymmTwistG_adj c t _) c t _ _ _ x false true
      (List.mem_singleton.2 rfl)
  · refine lwProv_blk_mol P _ _ _ ?_ o ho
    simp only [lwSymmOwxT2, owxET2]
    exact lwProv_ext_twist2 P.g _ ((lwProv_adj_solid _ _).trans (lwSymmTwistG_adj c t P.g)) c t _ _ _ x true true false true
      (List.mem_cons_self) (List.mem_cons_of_mem _ (List.mem_singleton.2 rfl))
  · refine lwProv_blk_mol P _ _ _ ?_ o ho
    simp only [lwSymmOwxT3, owxET3]
    exact lwProv_ext_twist1 P.g _ ((lwProv_adj_solid _ _).trans (lwSymmTwistG_adj c t P.g)) c t _ _ _ x false true (List.mem_singleton.2 rfl)
  · refine lwProv_blk_mol P _ _ _ ?_ o ho
    simp only [lwSymmOwxT4, owxET4]
    exact lwProv_ext_twist2 P.g _ ((lwProv_adj_solid _ _).trans (lwSymmTwistG_adj c t P.g)) c t _ _ _ x true true false true
      (List.mem_cons_self) (List.mem_cons_of_mem _ (List.mem_singleton.2 rfl))

end WeightList

section Cover

/-- **the initial coverage** (C2): every internal molecule of `fxyPowGraph p` is `{α_i, β_i}`, it contains `β_i` -/
theorem lwProv_fxyCover (p : ℕ) :
    CoverBy (P := (fxyPowGraph p).pack) (fun k : Fin p => (Sum.inr (localReg_fxyBeta k) : Fin 2 ⊕ Fin (2 * p))) := by
  intro c hc
  induction c using SimpleGraph.ConnectedComponent.ind with | h v => ?_
  rcases v with a | j
  · exact absurd ⟨a, rfl⟩ hc
  · obtain ⟨i, hi⟩ : ∃ i : Fin p, j = localReg_fxyAlpha i ∨ j = localReg_fxyBeta i := by
      have h2 : j.1 / 2 < p := by have := j.2; omega
      refine ⟨⟨j.1 / 2, h2⟩, ?_⟩
      by_cases hj : j.1 % 2 = 0
      · exact Or.inl (Fin.ext (by simp [localReg_fxyAlpha]; omega))
      · exact Or.inr (Fin.ext (by simp [localReg_fxyBeta]; omega))
    refine ⟨i, ?_⟩
    rcases hi with rfl | rfl
    · refine SimpleGraph.ConnectedComponent.eq.2 (SimpleGraph.Adj.reachable ((owx_molGraph_adj _ _ _).2
        ⟨fun h => by
          have := congrArg Fin.val (Sum.inr_injective h)
          simp [localReg_fxyAlpha, localReg_fxyBeta] at this, ?_⟩)).symm
      simp only [LGraph.adj, Bool.or_eq_true, List.any_eq_true, decide_eq_true_eq]
      exact Or.inl ⟨⟨false, true, Sum.inr (localReg_fxyAlpha i), Sum.inr (localReg_fxyBeta i)⟩,
        List.mem_map.2 ⟨i, List.mem_finRange i, rfl⟩, Or.inl ⟨rfl, rfl⟩⟩
    · rfl

end Cover


/-! ## 4. The weighted dotted edge partition -/

section MergeW

variable {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I] {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem lwProv_good_eq {Γ : LGraph E I} {ℓ : E ⊕ I → ι} (h : Γ.Good ℓ) {u v : E ⊕ I} (huv : Γ.cls u = Γ.cls v) :
    ℓ u = ℓ v := by
  have h' : Relation.EqvGen Γ.EqRel u v := Quotient.exact huv
  clear huv
  induction h' with
  | rel _ _ hr => exact h _ _ hr
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih1 ih2 => exact ih1.trans ih2

private theorem lwProv_term_zero_of_not_good (Γ : LGraph E I) (D : LData ι) {ℓ : E ⊕ I → ι} (h : ¬ Γ.Good ℓ) :
    Γ.term D ℓ = 0 := by
  unfold LGraph.Good at h
  push Not at h
  obtain ⟨u, v, ⟨e, he, heq, hxy⟩, hne⟩ := h
  have hne' : ℓ e.x ≠ ℓ e.y := by
    rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hne
    · exact fun h => hne h.symm
  have h0 : DEdge.val ℓ e = 0 := by simp [DEdge.val, heq, hne']
  have hprod : (Γ.dotted.map (DEdge.val ℓ)).prod = 0 := List.prod_eq_zero (List.mem_map.2 ⟨e, he, h0⟩)
  simp [LGraph.term, hprod]

theorem lwProv_prod_dotted_merge (Γ : LGraph E I) (ℓ' : Γ.ExtCls ⊕ Γ.IntCls → ι) :
    ∀ l : List (DEdge (E ⊕ I)), (∀ e ∈ l, e ∈ Γ.dotted) →
      ((l.filter fun e => !e.eq).map (DEdge.val (ℓ' ∘ Γ.vmap))).prod = (l.map (DEdge.val (ℓ' ∘ Γ.vmap))).prod
  | [], _ => rfl
  | e :: l, h => by
    have ih := lwProv_prod_dotted_merge Γ ℓ' l fun e' he' => h e' (List.mem_cons_of_mem _ he')
    cases heq : e.eq
    · simp [heq, ih]
    · have hv : Γ.vmap e.x = Γ.vmap e.y := congrArg Γ.vmapC (Quotient.sound
        (Relation.EqvGen.rel _ _ ⟨e, h e List.mem_cons_self, heq, Or.inl ⟨rfl, rfl⟩⟩))
      have h1 : DEdge.val (ℓ' ∘ Γ.vmap) e = 1 := by simp [DEdge.val, heq, hv]
      simp [heq, ih, h1]

theorem lwProv_term_merge (Γ : LGraph E I) (D : LData ι) (ℓ' : Γ.ExtCls ⊕ Γ.IntCls → ι) :
    Γ.merge.term D ℓ' = Γ.term D (ℓ' ∘ Γ.vmap) := by
  have hS : (SEdge.val D ℓ') ∘ (SEdge.map Γ.vmap) = SEdge.val D (ℓ' ∘ Γ.vmap) := funext fun e => rfl
  have hW : (WEdge.val D ℓ') ∘ (WEdge.map Γ.vmap) = WEdge.val D (ℓ' ∘ Γ.vmap) := funext fun e => rfl
  have hDm : (DEdge.val ℓ') ∘ (DEdge.map Γ.vmap) = DEdge.val (ℓ' ∘ Γ.vmap) := funext fun e => rfl
  have hD := lwProv_prod_dotted_merge Γ ℓ' Γ.dotted fun e he => he
  simp only [LGraph.term, LGraph.merge, List.map_map, hS, hW, hDm]
  rw [hD]

theorem lwProv_exists_inr (Γ : LGraph E I) (q : Γ.IntCls) : ∃ b : I, Γ.cls (Sum.inr b) = q.1 := by
  obtain ⟨v, hv⟩ := Quotient.exists_rep q.1
  rcases v with a | b
  · exact absurd ⟨a, hv⟩ q.2
  · exact ⟨b, hv⟩

/-- **the weighted value is preserved by merging** (`LGraph.val_eq_merge_val` with a weight on all the vertices) -/
theorem lwProv_valW_merge (Γ : LGraph E I) (D : LData ι) (W : (E ⊕ I → ι) → ℝ) (ℓ' : Γ.ExtCls → ι) :
    valW Γ D W (ℓ' ∘ Γ.extMap) = valW Γ.merge D (fun ℓ => W (ℓ ∘ Γ.vmap)) ℓ' := by
  classical
  set Φ : (Γ.IntCls → ι) → (I → ι) := fun ℓi' b => (Sum.elim ℓ' ℓi') (Γ.vmap (Sum.inr b)) with hΦ
  have hlab : ∀ ℓi', Sum.elim (ℓ' ∘ Γ.extMap) (Φ ℓi') = (Sum.elim ℓ' ℓi') ∘ Γ.vmap := by
    intro ℓi'
    funext v
    rcases v with a | b
    · simp [lwProv_vmap_inl]
    · rfl
  have hRHS : valW Γ.merge D (fun ℓ => W (ℓ ∘ Γ.vmap)) ℓ' =
      ∑ ℓi', ((W (Sum.elim (ℓ' ∘ Γ.extMap) (Φ ℓi')) : ℝ) : ℂ) * Γ.term D (Sum.elim (ℓ' ∘ Γ.extMap) (Φ ℓi')) := by
    unfold valW
    refine Finset.sum_congr rfl fun ℓi' _ => ?_
    rw [lwProv_term_merge, hlab]
  have hinj : Function.Injective Φ := by
    intro f g hfg
    funext q
    obtain ⟨b, hb⟩ := lwProv_exists_inr Γ q
    have hq : ¬ Γ.IsExtCls (Γ.cls (Sum.inr b)) := by rw [hb]; exact q.2
    have hv : Γ.vmap (Sum.inr b) = Sum.inr q := by
      simp only [LGraph.vmap, LGraph.vmapC, hq, ↓reduceDIte]
      congr 1
      exact Subtype.ext hb
    have := congrFun hfg b
    simpa [hΦ, hv] using this
  have hrange : ∀ ℓi : I → ι, ℓi ∉ Set.range Φ → Γ.term D (Sum.elim (ℓ' ∘ Γ.extMap) ℓi) = 0 := by
    intro ℓi hℓi
    apply lwProv_term_zero_of_not_good
    intro hgood
    apply hℓi
    refine ⟨fun q => ℓi (Classical.choose (lwProv_exists_inr Γ q)), ?_⟩
    funext b
    by_cases hext : Γ.IsExtCls (Γ.cls (Sum.inr b))
    · obtain ⟨a, ha⟩ := hext
      have h1 := lwProv_good_eq hgood (u := Sum.inl a) (v := Sum.inr b) ha
      have hext' : Γ.IsExtCls (Γ.cls (Sum.inr b)) := ⟨a, ha⟩
      have h2 : Γ.vmap (Sum.inr b) = Sum.inl ⟨Γ.cls (Sum.inr b), hext'⟩ := by
        simp only [LGraph.vmap, LGraph.vmapC, hext', ↓reduceDIte]
      simp only [hΦ, h2, Sum.elim_inl, Sum.elim_inr, Function.comp_apply] at h1 ⊢
      rw [← h1]
      congr 1
      exact Subtype.ext ha.symm
    · have hc := Classical.choose_spec (lwProv_exists_inr Γ ⟨Γ.cls (Sum.inr b), hext⟩)
      have h1 := lwProv_good_eq hgood
        (u := Sum.inr (Classical.choose (lwProv_exists_inr Γ ⟨Γ.cls (Sum.inr b), hext⟩))) (v := Sum.inr b) hc
      have h2 : Γ.vmap (Sum.inr b) = Sum.inr ⟨Γ.cls (Sum.inr b), hext⟩ := by
        simp only [LGraph.vmap, LGraph.vmapC, hext, ↓reduceDIte]
      simp only [hΦ, h2, Sum.elim_inr]
      simpa using h1
  rw [hRHS]
  unfold valW
  rw [← Finset.sum_image (f := fun ℓi => ((W (Sum.elim (ℓ' ∘ Γ.extMap) ℓi) : ℝ) : ℂ) *
    Γ.term D (Sum.elim (ℓ' ∘ Γ.extMap) ℓi)) (fun x _ y _ h => hinj h)]
  refine (Finset.sum_subset (Finset.subset_univ _) ?_).symm
  intro ℓi _ hni
  have := hrange ℓi (fun ⟨x, hx⟩ => hni (Finset.mem_image.2 ⟨x, Finset.mem_univ _, hx⟩))
  simp [this]

end MergeW

section SplitW

variable {V : Type*} [DecidableEq V] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- the product of the edge factors of a list of solid edges as a sum over the weight splits, with the exponents of `m`, `m̄` -/
theorem lwProv_prod_splitLoopsX (D : LData ι) (m : ℂ) (hM : ∀ x, D.M x x = m) (ℓ : V → ι) :
    ∀ es : List (SEdge V), (es.map (SEdge.val D ℓ)).prod =
      ((Sizes.lwSplitLoopsX es).map fun r => (m ^ r.1.1 * star m ^ r.1.2) * (r.2.map (SEdge.val D ℓ)).prod).sum
  | [] => by simp [Sizes.lwSplitLoopsX]
  | e :: es => by
    have ih := lwProv_prod_splitLoopsX D m hM ℓ es
    rw [List.map_cons, List.prod_cons, ih, Sizes.lwSplitLoopsX, lvl1_sum_flatMap, ← List.sum_map_mul_left]
    refine congrArg List.sum (List.map_congr_left fun r _ => ?_)
    by_cases h : e.src = e.dst ∧ e.circ = false
    · have hv : SEdge.val D ℓ e = SEdge.val D ℓ ⟨e.σ, true, e.src, e.dst⟩ + (if e.σ then m else star m) := by
        obtain ⟨h1, h2⟩ := h
        cases hσ : e.σ <;> simp [SEdge.val, h1, h2, hM, hσ]
      simp only [h, and_self, ↓reduceIte, List.map_cons, List.sum_cons, List.prod_cons, List.map_nil, List.sum_nil,
        add_zero, hv]
      by_cases hσ : e.σ <;> simp [hσ, pow_succ] <;> ring
    · simp only [h, ↓reduceIte, List.map_cons, List.sum_cons, List.prod_cons, List.map_nil, List.sum_nil, add_zero]
      ring

end SplitW

section PartW

variable {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I] {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem lwProv_sum_comm_list {α β : Type*} [Fintype α] (l : List β) (f : β → α → ℂ) :
    ∑ x, (l.map fun c => f c x).sum = (l.map fun c => ∑ x, f c x).sum := by
  induction l with
  | nil => simp
  | cons c l ih => simp [Finset.sum_add_distrib, ih]

theorem lwProv_sum_filter {α : Type*} (l : List α) (p : α → Bool) (f : α → ℂ) (h : ∀ x ∈ l, p x = false → f x = 0) :
    ((l.filter p).map f).sum = (l.map f).sum := by
  induction l with
  | nil => simp
  | cons x l ih =>
    have ih' := ih fun y hy => h y (List.mem_cons_of_mem _ hy)
    cases hp : p x
    · simp [hp, ih', h x List.mem_cons_self hp]
    · simp [hp, ih']

/-- **the dotted edge expansion of a weighted value** (`term_eq_sum_dotChoices`, the inconsistent terms vanish) -/
theorem lwProv_valW_dot (Y : LGraph E I) (D : LData ι) (W : (E ⊕ I → ι) → ℝ) (ℓ' : E → ι) :
    valW Y D W ℓ' = (Y.partitionTerms.map fun Δ => valW Δ D W ℓ').sum := by
  classical
  have h1 : valW Y D W ℓ' = (Y.dotChoices.map fun c => valW (Y.withDots c) D W ℓ').sum := by
    unfold valW
    simp only [Y.term_eq_sum_dotChoices, ← List.sum_map_mul_left]
    exact lwProv_sum_comm_list Y.dotChoices fun c ℓi => ((W (Sum.elim ℓ' ℓi) : ℝ) : ℂ) * (Y.withDots c).term D (Sum.elim ℓ' ℓi)
  rw [h1, LGraph.partitionTerms, lwProv_sum_filter, List.map_map]
  · rfl
  · intro Δ _ hp
    unfold valW
    refine Finset.sum_eq_zero fun ℓi _ => ?_
    rw [Δ.term_eq_zero_of_not_consistent D (by simpa using hp), mul_zero]

/-- the weight split of a graph at the level of terms, with the exponents of `m`, `m̄` -/
theorem lwProv_term_split (m : ℂ) (G : LGraph E I) (D : LData ι) (hM : ∀ x, D.M x x = m) (ℓ : E ⊕ I → ι) :
    G.term D ℓ = ((Sizes.lwSplitLoopsX G.solid).map fun r =>
      (m ^ r.1.1 * star m ^ r.1.2) * ({ G with solid := r.2 } : LGraph E I).term D ℓ).sum := by
  have := lwProv_prod_splitLoopsX D m hM ℓ G.solid
  unfold LGraph.term
  simp only [this, ← List.sum_map_mul_left]
  rw [← List.sum_map_mul_right, ← List.sum_map_mul_right]
  refine congrArg List.sum (List.map_congr_left fun r _ => ?_)
  ring

end PartW

section PartW2

variable {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- the weight split of a weighted value -/
theorem lwProv_valW_split (m : ℂ) (G : LGraph E I) (D : LData ι) (hM : ∀ x, D.M x x = m) (W : (E ⊕ I → ι) → ℝ)
    (ℓ : E → ι) : valW G D W ℓ = ((Sizes.lwSplitLoopsX G.solid).map fun r =>
      (m ^ r.1.1 * star m ^ r.1.2) * valW ({ G with solid := r.2 } : LGraph E I) D W ℓ).sum := by
  unfold valW
  simp only [lwProv_term_split m G D hM, ← List.sum_map_mul_left]
  rw [lwProv_sum_comm_list]
  refine congrArg List.sum (List.map_congr_left fun r _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun ℓi _ => ?_
  ring

/-- **a term and its merge with the weights split** (`mergeSplitP_val` with a weight and the exponents of `m`, `m̄`) -/
theorem lwProv_valW_mergeSplit (m : ℂ) (Δ : LGraph E I) (D : LData ι) (hM : ∀ x, D.M x x = m)
    (W : (E ⊕ I → ι) → ℝ) (ℓ' : E → ι) :
    valW Δ D W ℓ' = ((Sizes.lwSplitLoopsX Δ.merge.solid).map fun r => (m ^ r.1.1 * star m ^ r.1.2) *
      pvalW (lwProv_mergeQ Δ r.2) D (fun ℓ => W (ℓ ∘ Δ.vmap)) ℓ').sum := by
  classical
  by_cases h : ∃ ℓ'' : Δ.ExtCls → ι, ℓ' = ℓ'' ∘ Δ.extMap
  · obtain ⟨ℓ'', rfl⟩ := h
    have e1 : ∀ r : (ℕ × ℕ) × List (SEdge (Δ.ExtCls ⊕ Δ.IntCls)),
        pvalW (lwProv_mergeQ Δ r.2) D (fun ℓ => W (ℓ ∘ Δ.vmap)) (ℓ'' ∘ Δ.extMap) =
        valW ({ Δ.merge with solid := r.2 } : LGraph Δ.ExtCls Δ.IntCls) D (fun ℓ => W (ℓ ∘ Δ.vmap)) ℓ'' := fun r =>
      lwProv_pvalW_of_factor _ D _ rfl
    simp only [e1]
    rw [lwProv_valW_merge Δ D W ℓ'', lwProv_valW_split m Δ.merge D hM]
  · have e0 : valW Δ D W ℓ' = 0 := by
      refine Finset.sum_eq_zero fun ℓi _ => ?_
      rw [lwProv_term_zero_of_not_good Δ D ?_, mul_zero]
      intro hgood
      apply h
      refine ⟨fun q => ℓ' (Classical.choose q.2), ?_⟩
      funext a
      have hc := Classical.choose_spec (Δ.extMap a).2
      have := lwProv_good_eq hgood (u := Sum.inl (Classical.choose (Δ.extMap a).2)) (v := Sum.inl a) hc
      simpa using this.symm
    rw [e0]
    symm
    refine List.sum_eq_zero fun x hx => ?_
    obtain ⟨r, -, rfl⟩ := List.mem_map.1 hx
    rw [lwProv_pvalW_of_not _ D _ h, mul_zero]

end PartW2

section PartW3

variable {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **the weighted dotted edge partition** (`val_eq_partition` with a real weight on the vertices and the exponents of `m`, `m̄`):
`valW Y W = Σ_o m^{j} m̄^{j'} pvalW o.Q (W ∘ o.vm)`, pointwise in the data `D` (`M = m` on the diagonal) -/
theorem lwProv_valW_partX (m : ℂ) (Y : LGraph E I) (D : LData ι) (hM : ∀ x, D.M x x = m) (W : (E ⊕ I → ι) → ℝ)
    (ℓ' : E → ι) :
    valW Y D W ℓ' = ((lwProv_partX Y).map fun o => (m ^ o.tag.1 * star m ^ o.tag.2) *
      pvalW o.Q D (fun ℓ => W (ℓ ∘ o.vm)) ℓ').sum := by
  rw [lwProv_valW_dot, lwProv_partX, lvl1_sum_flatMap]
  refine congrArg List.sum (List.map_congr_left fun Δ _ => ?_)
  rw [lwProv_valW_mergeSplit m Δ D hM W ℓ', List.map_map]
  rfl

end PartW3


/-! ## 5. The weighted expansions of the three steps -/

section LayerA

variable {d : ℕ} {sz : Sizes d} {n : ℕ} {z : ℂ} {u : ℝ}

/-- the expectation of the weighted value of a graph at the sample data -/
def lwProv_EW (sz : Sizes d) (n : ℕ) (z : ℂ) (u : ℝ)
    (M Sp : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) {E I : Type} [Fintype I] [DecidableEq I]
    (T : LGraph E I) (W : (E ⊕ I → Idx d (sz.L n) (sz.W n)) → ℝ) (ℓe : E → Idx d (sz.L n) (sz.W n)) : ℂ :=
  ∫ ω, valW T (lwSampleData sz n z u M (lwS sz n u) Sp ω) W ℓe ∂(Sizes.seqP sz)

variable {M Sp : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ} {E I : Type} [Fintype E] [DecidableEq E]
  [Fintype I] [DecidableEq I]

theorem lwProv_EW_eq (hG : GaussIBP sz) (hz : 0 < z.im) (T : LGraph E I)
    (W : (E ⊕ I → Idx d (sz.L n) (sz.W n)) → ℝ) (ℓe : E → Idx d (sz.L n) (sz.W n)) :
    lwProv_EW sz n z u M Sp T W ℓe = ∑ ℓi : I → Idx d (sz.L n) (sz.W n), ((W (Sum.elim ℓe ℓi) : ℝ) : ℂ) *
      ∫ ω, T.term (lwSampleData sz n z u M (lwS sz n u) Sp ω) (Sum.elim ℓe ℓi) ∂(Sizes.seqP sz) := by
  have hint : ∀ ℓ', Integrable (fun ω => T.term (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓ') (Sizes.seqP sz) :=
    fun ℓ' => Tame.integrable hG (lwStein_term_tame1 hz T ℓ').tame
  unfold lwProv_EW valW
  rw [integral_finsetSum _ fun ℓi _ => (hint _).const_mul _]
  exact Finset.sum_congr rfl fun ℓi _ => integral_const_mul _ _

theorem lwProv_EW_ext1 (hG : GaussIBP sz) (hz : 0 < z.im) (T : LGraph E (I ⊕ Fin 1))
    (W : (E ⊕ I → Idx d (sz.L n) (sz.W n)) → ℝ) (ℓe : E → Idx d (sz.L n) (sz.W n)) :
    lwProv_EW sz n z u M Sp T (fun ℓ => W (ℓ ∘ owxEmb 1)) ℓe = ∑ ℓi : I → Idx d (sz.L n) (sz.W n),
      ((W (Sum.elim ℓe ℓi) : ℝ) : ℂ) * ∑ α, ∫ ω, T.term (lwSampleData sz n z u M (lwS sz n u) Sp ω)
        (owxLab1 ℓe ℓi α) ∂(Sizes.seqP sz) := by
  have hint : ∀ ℓ', Integrable (fun ω => T.term (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓ') (Sizes.seqP sz) :=
    fun ℓ' => Tame.integrable hG (lwStein_term_tame1 hz T ℓ').tame
  rw [lwProv_EW_eq hG hz, owx_sum_fin1]
  refine Finset.sum_congr rfl fun ℓi _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [show ((Sum.elim ℓe (Sum.elim ℓi fun _ : Fin 1 => α) : E ⊕ (I ⊕ Fin 1) → _) ∘ owxEmb 1) = Sum.elim ℓe ℓi from
    owxLab1_emb ℓe ℓi α]
  rfl

theorem lwProv_EW_ext2 (hG : GaussIBP sz) (hz : 0 < z.im) (T : LGraph E (I ⊕ Fin 2))
    (W : (E ⊕ I → Idx d (sz.L n) (sz.W n)) → ℝ) (ℓe : E → Idx d (sz.L n) (sz.W n)) :
    lwProv_EW sz n z u M Sp T (fun ℓ => W (ℓ ∘ owxEmb 2)) ℓe = ∑ ℓi : I → Idx d (sz.L n) (sz.W n),
      ((W (Sum.elim ℓe ℓi) : ℝ) : ℂ) * ∑ α, ∑ β, ∫ ω, T.term (lwSampleData sz n z u M (lwS sz n u) Sp ω)
        (owxLab2 ℓe ℓi α β) ∂(Sizes.seqP sz) := by
  rw [lwProv_EW_eq hG hz, owx_sum_fin2]
  refine Finset.sum_congr rfl fun ℓi _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [show ((Sum.elim ℓe (Sum.elim ℓi ![α, β]) : E ⊕ (I ⊕ Fin 2) → _) ∘ owxEmb 2) = Sum.elim ℓe ℓi from
    owxLab2_emb ℓe ℓi α β]
  rfl

theorem lwProv_swap1 {a κ κ' : Type*} [Fintype a] [Fintype κ] (L : List κ') (w : κ → ℂ) (f : κ' → κ → a → ℂ) :
    ∑ ℓi, w ℓi * ∑ x, (L.map fun q => f q ℓi x).sum = (L.map fun q => ∑ ℓi, w ℓi * ∑ x, f q ℓi x).sum := by
  induction L with
  | nil => simp
  | cons q L ih => simp [mul_add, Finset.sum_add_distrib, ih]

theorem lwProv_swap2 {a κ κ' : Type*} [Fintype a] [Fintype κ] (L : List κ') (w : κ → ℂ) (f : κ' → κ → a → a → ℂ) :
    ∑ ℓi, w ℓi * ∑ x, ∑ y, (L.map fun q => f q ℓi x y).sum =
      (L.map fun q => ∑ ℓi, w ℓi * ∑ x, ∑ y, f q ℓi x y).sum := by
  induction L with
  | nil => simp
  | cons q L ih => simp [mul_add, Finset.sum_add_distrib, ih]

/-- **`(Owx)` with a weight on all the vertices** (the weighted `owxE_graph_E`) -/
theorem lwProv_weight_EW (hG : GaussIBP sz) (hz : 0 < z.im) (hu : 0 < u) {m : ℂ} (hm0 : m ≠ 0)
    (hzm : z + (u : ℂ) * m = -m⁻¹)
    (hSp : ∀ i j, Sp i j - m ^ 2 * ∑ w, Sp i w * lwS sz n u w j = lwS sz n u i j) (hM : ∀ a, M a a = m)
    (Γ : LGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid) (x : E ⊕ I)
    (hx : p.1 = ⟨true, true, x, x⟩) (W : (E ⊕ I → Idx d (sz.L n) (sz.W n)) → ℝ)
    (ℓe : E → Idx d (sz.L n) (sz.W n)) :
    lwProv_EW sz n z u M Sp Γ W ℓe =
      lwProv_EW sz n z u M Sp (owxET1 m Γ x) (fun ℓ => W (ℓ ∘ owxEmb 1)) ℓe +
      lwProv_EW sz n z u M Sp (owxET2 m Γ p x) (fun ℓ => W (ℓ ∘ owxEmb 2)) ℓe +
      ((lwSplit p.2).map fun q => lwProv_EW sz n z u M Sp (owxET3 m Γ x q) (fun ℓ => W (ℓ ∘ owxEmb 1)) ℓe).sum +
      ((lwSplit p.2).map fun q => lwProv_EW sz n z u M Sp (owxET4 m Γ x q) (fun ℓ => W (ℓ ∘ owxEmb 2)) ℓe).sum := by
  rw [lwProv_EW_ext1 hG hz, lwProv_EW_ext2 hG hz, lwProv_EW_eq hG hz,
    congrArg List.sum (List.map_congr_left fun q _ => lwProv_EW_ext1 (M := M) (Sp := Sp) hG hz (owxET3 m Γ x q) W ℓe),
    congrArg List.sum (List.map_congr_left fun q _ => lwProv_EW_ext2 (M := M) (Sp := Sp) hG hz (owxET4 m Γ x q) W ℓe),
    ← lwProv_swap1, ← lwProv_swap2]
  simp_rw [owxE_term_integral hG hz hu hm0 hzm Sp M hSp hM Γ p hp x hx ℓe]
  simp only [mul_add, Finset.sum_add_distrib]

theorem lwProv_twist_term {ι : Type*} [Fintype ι] [DecidableEq ι] (D : LData ι) (hS : ∀ i j, star (D.S i j) = D.S i j)
    (c t : Bool) (Γ : LGraph E I) (ℓ : E ⊕ I → ι) :
    (lwSymmTwistG c t Γ).term D ℓ = lwSymmCj c (Γ.term (lwSymmDataTr D t) ℓ) := by
  have hT : ∀ i j, star (D.transpose.S i j) = D.transpose.S i j := fun i j => hS j i
  cases c <;> cases t
  · rfl
  · simp only [lwSymmTwistG, lwSymmCj, lwSymmDataTr, Bool.cond_true, Bool.cond_false, lwSymm_term_transpose]; rfl
  · simp only [lwSymmTwistG, lwSymmCj, lwSymmDataTr, Bool.cond_true, Bool.cond_false, lwSymm_term_conj D hS]; rfl
  · simp only [lwSymmTwistG, lwSymmCj, lwSymmDataTr, Bool.cond_true, lwSymm_term_conj D hS, lwSymm_term_transpose]; rfl

/-- **the twist in expectation, with a weight** (`lwSymm_twist_integral`) -/
theorem lwProv_EW_twist (hM : Mᵀ = M) (hSp : Spᵀ = Sp) (c t : Bool) {I' : Type} [Fintype I'] [DecidableEq I']
    (Γ : LGraph E I') (W : (E ⊕ I' → Idx d (sz.L n) (sz.W n)) → ℝ) (ℓe : E → Idx d (sz.L n) (sz.W n)) :
    lwProv_EW sz n z u M Sp (lwSymmTwistG c t Γ) W ℓe = lwSymmCj c (lwProv_EW sz n z u M Sp Γ W ℓe) := by
  have hSr : ∀ i j, star ((lwS sz n u) i j) = lwS sz n u i j := lwSymm_lwS_real sz n u
  have h1 : ∀ ω, valW (lwSymmTwistG c t Γ) (lwSampleData sz n z u M (lwS sz n u) Sp ω) W ℓe =
      lwSymmCj c (valW Γ (lwSymmDataTr (lwSampleData sz n z u M (lwS sz n u) Sp ω) t) W ℓe) := by
    intro ω
    have hS : ∀ i j, star ((lwSampleData sz n z u M (lwS sz n u) Sp ω).S i j) =
        (lwSampleData sz n z u M (lwS sz n u) Sp ω).S i j := fun i j => hSr i j
    unfold valW
    simp only [lwProv_twist_term _ hS c t, map_sum, map_mul]
    refine Finset.sum_congr rfl fun ℓi _ => ?_
    cases c <;> simp [lwSymmCj]
  have h2 : ∫ ω, valW Γ (lwSymmDataTr (lwSampleData sz n z u M (lwS sz n u) Sp ω) t) W ℓe ∂(Sizes.seqP sz) =
      ∫ ω, valW Γ (lwSampleData sz n z u M (lwS sz n u) Sp ω) W ℓe ∂(Sizes.seqP sz) := by
    cases t
    · rfl
    · simp only [lwSymmDataTr, Bool.cond_true, lwSymm_data_flip hM (lwSymm_lwS_symm sz n u) hSp]
      exact lwSymm_integral_flip sz (fun ω => valW Γ (lwSampleData sz n z u M (lwS sz n u) Sp ω) W ℓe)
  unfold lwProv_EW
  simp only [h1]
  rw [lwSymm_integral_cj, h2]

/-- **The weight step (`lwSymm_weight_graph_E`) with a weight**: the four families of `lvl1WeightOutsX`, twisted -/
theorem lwProv_weight_EW' (hG : GaussIBP sz) (hz : 0 < z.im) (hu : 0 < u) {m : ℂ} (hm0 : m ≠ 0)
    (hzm : z + (u : ℂ) * m = -m⁻¹)
    (hSp : ∀ i j, Sp i j - m ^ 2 * ∑ w, Sp i w * lwS sz n u w j = lwS sz n u i j) (hSpT : Spᵀ = Sp)
    (hM : ∀ a, M a a = m) (hM0 : ∀ a b, a ≠ b → M a b = 0)
    (Γ : LGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid) (x : E ⊕ I) (c t : Bool)
    (hx : lwSymmTwistS c t p.1 = ⟨true, true, x, x⟩) (W : (E ⊕ I → Idx d (sz.L n) (sz.W n)) → ℝ)
    (ℓe : E → Idx d (sz.L n) (sz.W n)) :
    lwProv_EW sz n z u M Sp Γ W ℓe =
      lwProv_EW sz n z u M Sp (lwSymmOwxT1 c t m Γ x) (fun ℓ => W (ℓ ∘ owxEmb 1)) ℓe +
      lwProv_EW sz n z u M Sp (lwSymmOwxT2 c t m Γ p x) (fun ℓ => W (ℓ ∘ owxEmb 2)) ℓe +
      ((lwSplit p.2).map fun q => lwProv_EW sz n z u M Sp (lwSymmOwxT3 c t m Γ x q) (fun ℓ => W (ℓ ∘ owxEmb 1)) ℓe).sum +
      ((lwSplit p.2).map fun q => lwProv_EW sz n z u M Sp (lwSymmOwxT4 c t m Γ x q) (fun ℓ => W (ℓ ∘ owxEmb 2)) ℓe).sum := by
  simp only [lwSymmOwxT1, lwSymmOwxT2, lwSymmOwxT3, lwSymmOwxT4]
  have hMs := lwSymm_M_symm hM0
  have tw : ∀ {I' : Type} [Fintype I'] [DecidableEq I'] (T : LGraph E I')
      (W' : (E ⊕ I' → Idx d (sz.L n) (sz.W n)) → ℝ), lwProv_EW sz n z u M Sp (lwSymmTwistG c t T) W' ℓe =
        lwSymmCj c (lwProv_EW sz n z u M Sp T W' ℓe) := fun T W' => lwProv_EW_twist hMs hSpT c t T W' ℓe
  have hp' : lwSymmTwistP c t p ∈ lwSplit (lwSymmTwistG c t Γ).solid := by
    rw [lwSymmTwistG_solid, lwSymm_lwSplit_twistP]
    exact List.mem_map_of_mem hp
  have key := lwProv_weight_EW hG hz hu hm0 hzm hSp hM (lwSymmTwistG c t Γ) (lwSymmTwistP c t p) hp' x hx W ℓe
  have e0 : lwProv_EW sz n z u M Sp Γ W ℓe = lwSymmCj c (lwProv_EW sz n z u M Sp (lwSymmTwistG c t Γ) W ℓe) := by
    conv_lhs => rw [← lwSymmTwistG_invol c t Γ]
    exact tw (lwSymmTwistG c t Γ) W
  rw [e0, key, map_add, map_add, map_add, tw, tw, lwSymm_cj_list_sum, lwSymm_cj_list_sum]
  have hS : lwSplit (lwSymmTwistP c t p).2 = (lwSplit p.2).map (lwSymmTwistP c t) := lwSymm_lwSplit_twistP c t p.2
  rw [hS, List.map_map, List.map_map]
  simp only [Function.comp_def, ← tw]

/-- a graph with a `=`-dotted and a `×`-dotted edge between the same two vertices has every term `0` -/
theorem lwProv_term_zero_dots {ι : Type*} [Fintype ι] [DecidableEq ι] (T : LGraph E I) (D : LData ι)
    (ℓ : E ⊕ I → ι) (a b : E ⊕ I) (h1 : (⟨true, a, b⟩ : DEdge (E ⊕ I)) ∈ T.dotted)
    (h2 : ∃ d ∈ T.dotted, d.eq = false ∧ ((d.x = a ∧ d.y = b) ∨ (d.x = b ∧ d.y = a))) : T.term D ℓ = 0 := by
  obtain ⟨d, hd, hde, hdab⟩ := h2
  have hprod : (T.dotted.map (DEdge.val ℓ)).prod = 0 := by
    by_cases hl : ℓ a = ℓ b
    · refine List.prod_eq_zero (List.mem_map.2 ⟨d, hd, ?_⟩)
      have : ℓ d.x = ℓ d.y := by rcases hdab with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;> simp [h3, h4, hl]
      simp [DEdge.val, hde, this]
    · exact List.prod_eq_zero (List.mem_map.2 ⟨_, h1, by simp [DEdge.val, hl]⟩)
  simp [LGraph.term, hprod]

theorem lwProv_EW_zero (hG : GaussIBP sz) (hz : 0 < z.im) {I' : Type} [Fintype I'] [DecidableEq I'] (T : LGraph E I')
    (hT : ∀ (D : LData (Idx d (sz.L n) (sz.W n))) ℓ, T.term D ℓ = 0) (W : (E ⊕ I' → Idx d (sz.L n) (sz.W n)) → ℝ)
    (ℓe : E → Idx d (sz.L n) (sz.W n)) : lwProv_EW sz n z u M Sp T W ℓe = 0 := by
  rw [lwProv_EW_eq hG hz]
  exact Finset.sum_eq_zero fun ℓi _ => by simp [hT]

theorem lwProv_valW_integrable (hG : GaussIBP sz) (hz : 0 < z.im) {I' : Type} [Fintype I'] [DecidableEq I']
    (T : LGraph E I') (W : (E ⊕ I' → Idx d (sz.L n) (sz.W n)) → ℝ) (ℓe : E → Idx d (sz.L n) (sz.W n)) :
    Integrable (fun ω => valW T (lwSampleData sz n z u M (lwS sz n u) Sp ω) W ℓe) (Sizes.seqP sz) :=
  integrable_finsetSum _ fun ℓi _ => (Tame.integrable hG (lwStein_term_tame1 hz T _).tame).const_mul _

/-- the derivative term and its split (`oe1xDs_integral` with a weight) -/
theorem lwProv_oe1xDs_EW (hG : GaussIBP sz) (hz : 0 < z.im) {m : ℂ} (hM : ∀ a, M a a = m) (Γ : LGraph E I) (x : I)
    (v : E ⊕ I) (q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (W : (E ⊕ (I ⊕ Fin 1) → Idx d (sz.L n) (sz.W n)) → ℝ)
    (ℓe : E → Idx d (sz.L n) (sz.W n)) :
    lwProv_EW sz n z u M Sp (oe1xD m Γ x v q) W ℓe =
      ((oe1xDs m Γ x v q).map fun T => lwProv_EW sz n z u M Sp T W ℓe).sum := by
  have hMd : ∀ ω, ∀ a, (lwSampleData sz n z u M (lwS sz n u) Sp ω).M a a = m := fun ω a => hM a
  have hsplit : ∀ (A B : LGraph E (I ⊕ Fin 1)),
      (∀ ℓ' ω, (oe1xD m Γ x v q).term (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓ' =
        A.term (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓ' + B.term (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓ') →
      lwProv_EW sz n z u M Sp (oe1xD m Γ x v q) W ℓe = lwProv_EW sz n z u M Sp A W ℓe + lwProv_EW sz n z u M Sp B W ℓe := by
    intro A B h
    unfold lwProv_EW
    rw [← integral_add (lwProv_valW_integrable hG hz A W ℓe) (lwProv_valW_integrable hG hz B W ℓe)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    simp only [valW, ← Finset.sum_add_distrib, h, mul_add]
  unfold oe1xDs
  split_ifs with h1 h2
  · simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    exact hsplit _ _ fun ℓ' ω => oe1xD_red_term _ m (hMd ω) Γ x v q h1.1 h1.2 ℓ'
  · simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    exact hsplit _ _ fun ℓ' ω => oe1xD_blue_term _ m (hMd ω) Γ x v q h2.1 h2.2 ℓ'
  · simp

/-- **`(Oe1x)` with a weight**, the terms before the twist (`oe1x_term_integral`, the `x = y₁` term is `0`) -/
theorem lwProv_oe1x_EW (hG : GaussIBP sz) (hz : 0 < z.im) (hu : 0 < u) {m : ℂ} (hm0 : m ≠ 0)
    (hzm : z + (u : ℂ) * m = -m⁻¹) (hM : ∀ a, M a a = m) (Γ : LGraph E I)
    (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid) (x : I) (v : E ⊕ I)
    (hx : p.1 = ⟨true, false, Sum.inr x, v⟩)
    (hXd : ∃ d ∈ Γ.dotted, d.eq = false ∧ ((d.x = Sum.inr x ∧ d.y = v) ∨ (d.x = v ∧ d.y = Sum.inr x)))
    (W : (E ⊕ I → Idx d (sz.L n) (sz.W n)) → ℝ) (ℓe : E → Idx d (sz.L n) (sz.W n)) :
    lwProv_EW sz n z u M Sp Γ W ℓe = lwProv_EW sz n z u M Sp (owxT1 m Γ x) (fun ℓ => W (ℓ ∘ owxEmb 1)) ℓe +
      ((lwSplit p.2).map fun q => lwProv_EW sz n z u M Sp (oe1xD m Γ x v q) (fun ℓ => W (ℓ ∘ owxEmb 1)) ℓe).sum := by
  have hz0 : ∀ ℓi : I → Idx d (sz.L n) (sz.W n), ∫ ω, (oe1xT1d m Γ p x v).term
      (lwSampleData sz n z u M (lwS sz n u) Sp ω) (Sum.elim ℓe ℓi) ∂(Sizes.seqP sz) = 0 := fun ℓi => by
    have : ∀ ω, (oe1xT1d m Γ p x v).term (lwSampleData sz n z u M (lwS sz n u) Sp ω) (Sum.elim ℓe ℓi) = 0 := fun ω =>
      lwProv_term_zero_dots _ _ _ (Sum.inr x) v List.mem_cons_self
        (by obtain ⟨d, hd, h⟩ := hXd; exact ⟨d, List.mem_cons_of_mem _ hd, h⟩)
    simp [this]
  rw [lwProv_EW_ext1 hG hz, lwProv_EW_eq hG hz,
    congrArg List.sum (List.map_congr_left fun q _ => lwProv_EW_ext1 (M := M) (Sp := Sp) hG hz (oe1xD m Γ x v q) W ℓe),
    ← lwProv_swap1]
  simp_rw [oe1x_term_integral hG hz hu hm0 hzm Sp M hM Γ p hp x v hx ℓe, hz0]
  simp only [zero_add, mul_add, Finset.sum_add_distrib]

/-- **The edge step (`lwSymm_oe1x_graph_E`) with a weight**: the families of `lvl1EdgeOutsX`, twisted -/
theorem lwProv_edge_EW' (hG : GaussIBP sz) (hz : 0 < z.im) (hu : 0 < u) {m : ℂ} (hm0 : m ≠ 0)
    (hzm : z + (u : ℂ) * m = -m⁻¹) (hSpT : Spᵀ = Sp) (hM : ∀ a, M a a = m) (hM0 : ∀ a b, a ≠ b → M a b = 0)
    (Γ : LGraph E I) (hN : Γ.Normal) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid) (x : I)
    (v : E ⊕ I) (hv : v ≠ Sum.inr x) (c t : Bool) (hx : lwSymmTwistS c t p.1 = ⟨true, p.1.circ, Sum.inr x, v⟩)
    (W : (E ⊕ I → Idx d (sz.L n) (sz.W n)) → ℝ) (ℓe : E → Idx d (sz.L n) (sz.W n)) :
    lwProv_EW sz n z u M Sp Γ W ℓe =
      lwProv_EW sz n z u M Sp (lwSymmOe1xOwx c t m Γ p x) (fun ℓ => W (ℓ ∘ owxEmb 1)) ℓe +
      ((lwSplit p.2).map fun q => ((lwSymmOe1xDs c t m Γ p x v q).map fun T =>
        lwProv_EW sz n z u M Sp T (fun ℓ => W (ℓ ∘ owxEmb 1)) ℓe).sum).sum := by
  have hpne := lvl1_hpne c t p x v hv hx
  have hX := lwSymm_hX_of_normal Γ hN p hp hpne
  have hMs := lwSymm_M_symm hM0
  have tw : ∀ {I' : Type} [Fintype I'] [DecidableEq I'] (T : LGraph E I')
      (W' : (E ⊕ I' → Idx d (sz.L n) (sz.W n)) → ℝ), lwProv_EW sz n z u M Sp (lwSymmTwistG c t T) W' ℓe =
        lwSymmCj c (lwProv_EW sz n z u M Sp T W' ℓe) := fun T W' => lwProv_EW_twist hMs hSpT c t T W' ℓe
  have hab := lvl1_ends_of_twist c t p.1 (Sum.inr x) v (by rw [hx]; exact ⟨rfl, rfl⟩)
  obtain ⟨d, hd, hde, hdxy⟩ := lvl1_xBetween_of_edge Γ hN p.1 (lvl1_mem_split_fst _ p hp) hpne
  have hXd : ∃ d ∈ (lwSymmFrame c t Γ p).dotted, d.eq = false ∧
      ((d.x = Sum.inr x ∧ d.y = v) ∨ (d.x = v ∧ d.y = Sum.inr x)) := by
    refine ⟨d, ?_, hde, ?_⟩
    · rw [lvl1_frame_dotted]; exact hd
    · rcases hdxy with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;> rcases hab with ⟨h5, h6⟩ | ⟨h5, h6⟩ <;> simp_all
  have e00 : lwProv_EW sz n z u M Sp Γ W ℓe = lwProv_EW sz n z u M Sp (lwSymmUncirc Γ p) W ℓe := by
    unfold lwProv_EW
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    simp only [valW, lwSymmUncirc_term (lwSampleData sz n z u M (lwS sz n u) Sp ω) hM0 Γ p hp hX]
  have e0 : lwProv_EW sz n z u M Sp (lwSymmUncirc Γ p) W ℓe =
      lwSymmCj c (lwProv_EW sz n z u M Sp (lwSymmFrame c t Γ p) W ℓe) := by
    conv_lhs => rw [← lwSymmTwistG_invol c t (lwSymmUncirc Γ p)]
    exact tw (lwSymmFrame c t Γ p) W
  have key := lwProv_oe1x_EW (Sp := Sp) hG hz hu hm0 hzm hM (lwSymmFrame c t Γ p) (lwSymmFrameP c t p) (lwSymmFrameP_mem c t Γ p) x v
    (lwSymmFrameP_fst c t p _ _ hx) hXd W ℓe
  have hS : lwSplit (lwSymmFrameP c t p).2 = (lwSplit p.2).map (lwSymmTwistP c t) := lwSymm_lwSplit_twistP c t p.2
  simp only [lwProv_oe1xDs_EW hG hz hM, hS, List.map_map, Function.comp_def] at key
  rw [e00, e0, key, map_add, lwSymm_cj_list_sum]
  simp only [lwSymmOe1xOwx, lwSymmOe1xDs, List.map_map, Function.comp_def, lwSymm_cj_list_sum, ← tw]

/-- **`(Oe2x)` with a weight**, the terms before the twist (`oe2x_term_integral`, the `δ_{xy}` term is `0`) -/
theorem lwProv_oe2x_EW (hG : GaussIBP sz) (hz : 0 < z.im) (hu : 0 < u) {m : ℂ} (hm0 : m ≠ 0)
    (hzm : z + (u : ℂ) * m = -m⁻¹)
    (hSp : ∀ i j, Sp i j - m ^ 2 * ∑ w, Sp i w * lwS sz n u w j = lwS sz n u i j) (hM : ∀ a, M a a = m)
    (Γ : LGraph E I) (x : I) (y y' : E ⊕ I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid)
    (hp1 : p.1 = ⟨true, false, Sum.inr x, y⟩) (q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hq : q ∈ lwSplit p.2)
    (hq1 : q.1 = ⟨true, false, y', Sum.inr x⟩)
    (hXd : ∃ d ∈ Γ.dotted, d.eq = false ∧ ((d.x = Sum.inr x ∧ d.y = y) ∨ (d.x = y ∧ d.y = Sum.inr x)))
    (W : (E ⊕ I → Idx d (sz.L n) (sz.W n)) → ℝ) (ℓe : E → Idx d (sz.L n) (sz.W n)) :
    lwProv_EW sz n z u M Sp Γ W ℓe = lwProv_EW sz n z u M Sp (oe2xR2 m Γ q x y y') W ℓe +
      lwProv_EW sz n z u M Sp (owxT1 m Γ x) (fun ℓ => W (ℓ ∘ owxEmb 1)) ℓe +
      lwProv_EW sz n z u M Sp (oe2xR4 m Γ q x y y') (fun ℓ => W (ℓ ∘ owxEmb 2)) ℓe +
      lwProv_EW sz n z u M Sp (oe2xR5 m Γ q x y y') (fun ℓ => W (ℓ ∘ owxEmb 1)) ℓe +
      lwProv_EW sz n z u M Sp (oe2xR6 m Γ q x y y') (fun ℓ => W (ℓ ∘ owxEmb 2)) ℓe +
      ((lwSplit q.2).map fun q' => lwProv_EW sz n z u M Sp (oe2xR7 m Γ x y y' q') (fun ℓ => W (ℓ ∘ owxEmb 1)) ℓe).sum +
      ((lwSplit q.2).map fun q' => lwProv_EW sz n z u M Sp (oe2xR8 m Γ x y y' q') (fun ℓ => W (ℓ ∘ owxEmb 2)) ℓe).sum := by
  have hz0 : ∀ ℓi : I → Idx d (sz.L n) (sz.W n), ∫ ω, (oe2xR1d m Γ p x y).term
      (lwSampleData sz n z u M (lwS sz n u) Sp ω) (Sum.elim ℓe ℓi) ∂(Sizes.seqP sz) = 0 := fun ℓi => by
    have : ∀ ω, (oe2xR1d m Γ p x y).term (lwSampleData sz n z u M (lwS sz n u) Sp ω) (Sum.elim ℓe ℓi) = 0 := fun ω =>
      lwProv_term_zero_dots _ _ _ (Sum.inr x) y List.mem_cons_self
        (by obtain ⟨d, hd, h⟩ := hXd; exact ⟨d, List.mem_cons_of_mem _ hd, h⟩)
    simp [this]
  rw [lwProv_EW_eq hG hz Γ W ℓe, lwProv_EW_eq hG hz (oe2xR2 m Γ q x y y') W ℓe, lwProv_EW_ext1 hG hz,
    lwProv_EW_ext2 hG hz, lwProv_EW_ext1 hG hz, lwProv_EW_ext2 hG hz,
    congrArg List.sum (List.map_congr_left fun q' _ => lwProv_EW_ext1 (M := M) (Sp := Sp) hG hz (oe2xR7 m Γ x y y' q') W ℓe),
    congrArg List.sum (List.map_congr_left fun q' _ => lwProv_EW_ext2 (M := M) (Sp := Sp) hG hz (oe2xR8 m Γ x y y' q') W ℓe),
    ← lwProv_swap1, ← lwProv_swap2]
  simp_rw [oe2x_term_integral hG hz hu hm0 hzm Sp M hSp hM Γ x y y' p hp hp1 q hq hq1 ℓe, hz0]
  simp only [zero_add, mul_add, Finset.sum_add_distrib]

/-- **The `GG` step (`lwSymm_oe2x_graph_E`) with a weight**: the families of `lvl1GGOutsX`, twisted -/
theorem lwProv_gg_EW' (hG : GaussIBP sz) (hz : 0 < z.im) (hu : 0 < u) {m : ℂ} (hm0 : m ≠ 0)
    (hzm : z + (u : ℂ) * m = -m⁻¹)
    (hSp : ∀ i j, Sp i j - m ^ 2 * ∑ w, Sp i w * lwS sz n u w j = lwS sz n u i j) (hSpT : Spᵀ = Sp)
    (hM : ∀ a, M a a = m) (hM0 : ∀ a b, a ≠ b → M a b = 0)
    (Γ : LGraph E I) (hN : Γ.Normal) (x : I) (y y' : E ⊕ I) (hy : y ≠ Sum.inr x) (hy' : y' ≠ Sum.inr x)
    (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid) (q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I)))
    (hq : q ∈ lwSplit p.2) (c t : Bool) (hp1 : lwSymmTwistS c t p.1 = ⟨true, p.1.circ, Sum.inr x, y⟩)
    (hq1 : lwSymmTwistS c t q.1 = ⟨true, q.1.circ, y', Sum.inr x⟩)
    (W : (E ⊕ I → Idx d (sz.L n) (sz.W n)) → ℝ) (ℓe : E → Idx d (sz.L n) (sz.W n)) :
    lwProv_EW sz n z u M Sp Γ W ℓe =
      lwProv_EW sz n z u M Sp (lwSymmOe2xR2 c t m Γ p q x y y') W ℓe +
      lwProv_EW sz n z u M Sp (lwSymmOe2xR3 c t m Γ p q x) (fun ℓ => W (ℓ ∘ owxEmb 1)) ℓe +
      lwProv_EW sz n z u M Sp (lwSymmOe2xR4 c t m Γ p q x y y') (fun ℓ => W (ℓ ∘ owxEmb 2)) ℓe +
      lwProv_EW sz n z u M Sp (lwSymmOe2xR5 c t m Γ p q x y y') (fun ℓ => W (ℓ ∘ owxEmb 1)) ℓe +
      lwProv_EW sz n z u M Sp (lwSymmOe2xR6 c t m Γ p q x y y') (fun ℓ => W (ℓ ∘ owxEmb 2)) ℓe +
      ((lwSplit q.2).map fun q' => lwProv_EW sz n z u M Sp (lwSymmOe2xR7 c t m Γ p q x y y' q')
        (fun ℓ => W (ℓ ∘ owxEmb 1)) ℓe).sum +
      ((lwSplit q.2).map fun q' => lwProv_EW sz n z u M Sp (lwSymmOe2xR8 c t m Γ p q x y y' q')
        (fun ℓ => W (ℓ ∘ owxEmb 2)) ℓe).sum := by
  have hpne := lvl1_hpne c t p x y hy hp1
  have hqne := lvl1_qne c t q x y' hq1 hy'
  have hqΓ : q.1 ∈ Γ.solid := lvl1_mem_split _ p hp q.1 (lvl1_mem_split_fst _ q hq)
  have hX1 := lwSymm_hX_of_normal Γ hN p hp hpne
  have hX2 : q.1.circ = true → ∃ d ∈ Γ.dotted, d.eq = false ∧
      ((d.x = q.1.src ∧ d.y = q.1.dst) ∨ (d.x = q.1.dst ∧ d.y = q.1.src)) := fun _ => lvl1_xBetween_of_edge Γ hN q.1 hqΓ hqne
  have hMs := lwSymm_M_symm hM0
  have tw : ∀ {I' : Type} [Fintype I'] [DecidableEq I'] (T : LGraph E I')
      (W' : (E ⊕ I' → Idx d (sz.L n) (sz.W n)) → ℝ), lwProv_EW sz n z u M Sp (lwSymmTwistG c t T) W' ℓe =
        lwSymmCj c (lwProv_EW sz n z u M Sp T W' ℓe) := fun T W' => lwProv_EW_twist hMs hSpT c t T W' ℓe
  have hab := lvl1_ends_of_twist c t p.1 (Sum.inr x) y (by rw [hp1]; exact ⟨rfl, rfl⟩)
  obtain ⟨d, hd, hde, hdxy⟩ := lvl1_xBetween_of_edge Γ hN p.1 (lvl1_mem_split_fst _ p hp) hpne
  have hXd : ∃ d ∈ (lwSymmFrame2 c t Γ p q).dotted, d.eq = false ∧
      ((d.x = Sum.inr x ∧ d.y = y) ∨ (d.x = y ∧ d.y = Sum.inr x)) := by
    refine ⟨d, ?_, hde, ?_⟩
    · rw [lvl1_frame2_dotted]; exact hd
    · rcases hdxy with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;> rcases hab with ⟨h5, h6⟩ | ⟨h5, h6⟩ <;> simp_all
  have e00 : lwProv_EW sz n z u M Sp Γ W ℓe = lwProv_EW sz n z u M Sp (lwSymmUncirc2 Γ p q) W ℓe := by
    unfold lwProv_EW
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    simp only [valW, lwSymmUncirc2_term (lwSampleData sz n z u M (lwS sz n u) Sp ω) hM0 Γ p q hp hq hX1 hX2]
  have e0 : lwProv_EW sz n z u M Sp (lwSymmUncirc2 Γ p q) W ℓe =
      lwSymmCj c (lwProv_EW sz n z u M Sp (lwSymmFrame2 c t Γ p q) W ℓe) := by
    conv_lhs => rw [← lwSymmTwistG_invol c t (lwSymmUncirc2 Γ p q)]
    exact tw (lwSymmFrame2 c t Γ p q) W
  have key := lwProv_oe2x_EW hG hz hu hm0 hzm hSp hM (lwSymmFrame2 c t Γ p q) x y y' (lwSymmFrame2P c t p q)
    (lwSymmFrame2P_mem c t Γ p q) (lwSymmFrameP_fst c t p _ _ hp1) (lwSymmFrame2Q c t q) (lwSymmFrame2Q_mem c t p q)
    (lwSymmFrameP_fst c t q _ _ hq1) hXd W ℓe
  have hS : lwSplit (lwSymmFrame2Q c t q).2 = (lwSplit q.2).map (lwSymmTwistP c t) := lwSymm_lwSplit_twistP c t q.2
  rw [e00, e0, key]
  simp only [lwSymmOe2xR2, lwSymmOe2xR3, lwSymmOe2xR4, lwSymmOe2xR5, lwSymmOe2xR6, lwSymmOe2xR7, lwSymmOe2xR8, hS,
    map_add, lwSymm_cj_list_sum, List.map_map, Function.comp_def, ← tw]

end LayerA


/-! ## 6. Packing, tags, and the weighted expansion of one step -/

section Pack

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- the coefficient of a graph scales its weighted value -/
theorem lwProv_valW_sc {E I : Type} [Fintype I] [DecidableEq I] (κ : ℂ) (Y : LGraph E I) (D : LData ι)
    (W : (E ⊕ I → ι) → ℝ) (ℓ : E → ι) : valW (lwEngine_sc κ Y) D W ℓ = κ * valW Y D W ℓ := by
  unfold valW
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun ℓi _ => ?_
  unfold LGraph.term lwEngine_sc
  ring

/-- the evaluation of a tagged packed graph scales its weighted value by `m^j m̄^{j'}` -/
theorem lwProv_pvalW_evX {E0 : Type} (m : ℂ) (r : (ℕ × ℕ) × PGraph E0) (D : LData ι)
    (W : (r.2.E' ⊕ r.2.I' → ι) → ℝ) (ℓe : E0 → ι) :
    pvalW (lwEngine_ev m r) D W ℓe = lwEngine_ev3 m r.1 * pvalW r.2 D W ℓe := by
  classical
  by_cases h : ∃ ℓ' : r.2.E' → ι, ℓe = ℓ' ∘ r.2.ext
  · obtain ⟨ℓ', hℓ'⟩ := h
    rw [lwProv_pvalW_of_factor r.2 D W hℓ', lwProv_pvalW_of_factor (lwEngine_ev m r) D W hℓ']
    exact lwProv_valW_sc (lwEngine_ev3 m r.1) r.2.g D W ℓ'
  · rw [lwProv_pvalW_of_not r.2 D W h, lwProv_pvalW_of_not (lwEngine_ev m r) D W h, mul_zero]

/-- reading a packed graph through a surjection of the external vertices -/
theorem lwProv_pvalW_comp {E E' : Type} (Q : PGraph E') (f : E → E') (hf : Function.Surjective f) (D : LData ι)
    (W : (Q.E' ⊕ Q.I' → ι) → ℝ) (ℓ' : E' → ι) :
    pvalW (Q.lvl1Comp f hf) D W (ℓ' ∘ f) = pvalW Q D W ℓ' := by
  classical
  by_cases h : ∃ ℓ'' : Q.E' → ι, ℓ' = ℓ'' ∘ Q.ext
  · obtain ⟨ℓ'', hℓ''⟩ := h
    rw [lwProv_pvalW_of_factor Q D W hℓ'', lwProv_pvalW_of_factor (Q.lvl1Comp f hf) D W (ℓ' := ℓ'') (by rw [hℓ'']; rfl)]
    rfl
  · rw [lwProv_pvalW_of_not Q D W h]
    refine lwProv_pvalW_of_not (Q.lvl1Comp f hf) D W ?_
    rintro ⟨ℓ'', hℓ''⟩
    apply h
    refine ⟨ℓ'', ?_⟩
    have : ℓ' ∘ f = (ℓ'' ∘ Q.ext) ∘ f := hℓ''
    exact hf.injective_comp_right this

/-- the evaluated packed output at the factored labels -/
theorem lwProv_pvalW_evX_pack (m : ℂ) (v : ℕ × ℕ) (P : PGraph (Fin 2)) (Q : PGraph P.E') (D : LData ι)
    (W : (Q.E' ⊕ Q.I' → ι) → ℝ) (ℓ' : P.E' → ι) :
    pvalW (lwEvX m (v, Q.lvl1Comp P.ext P.ext_surj)) D W (ℓ' ∘ P.ext) = lwEngine_ev3 m v * pvalW Q D W ℓ' := by
  exact (lwProv_pvalW_evX m (v, Q.lvl1Comp P.ext P.ext_surj) D W (ℓ' ∘ P.ext)).trans
    (congrArg _ (lwProv_pvalW_comp Q P.ext P.ext_surj D W ℓ'))

theorem lwProv_pvalW_comp_not {E E' : Type} (Q : PGraph E') (f : E → E') (hf : Function.Surjective f) (D : LData ι)
    (W : (Q.E' ⊕ Q.I' → ι) → ℝ) {ℓe : E → ι} (h : ¬ ∃ ℓ' : E' → ι, ℓe = ℓ' ∘ f) :
    pvalW (Q.lvl1Comp f hf) D W ℓe = 0 := by
  refine lwProv_pvalW_of_not (Q.lvl1Comp f hf) D W ?_
  rintro ⟨ℓ'', hℓ''⟩
  exact h ⟨ℓ'' ∘ Q.ext, hℓ''⟩

end Pack

section Blk

variable {d : ℕ} {sz : Sizes d} {n : ℕ} {z : ℂ} {u : ℝ} {M Sp : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ}

theorem lwProv_pvalW_integrable (hG : GaussIBP sz) (hz : 0 < z.im) {E : Type} (Q : PGraph E)
    (W : (Q.E' ⊕ Q.I' → Idx d (sz.L n) (sz.W n)) → ℝ) (ℓe : E → Idx d (sz.L n) (sz.W n)) :
    Integrable (fun ω => pvalW Q (lwSampleData sz n z u M (lwS sz n u) Sp ω) W ℓe) (Sizes.seqP sz) := by
  classical
  by_cases h : ∃ ℓ' : Q.E' → Idx d (sz.L n) (sz.W n), ℓe = ℓ' ∘ Q.ext
  · obtain ⟨ℓ', hℓ'⟩ := h
    simp only [lwProv_pvalW_of_factor Q _ W hℓ']
    exact lwProv_valW_integrable hG hz Q.g W ℓ'
  · simp only [lwProv_pvalW_of_not Q _ W h]
    exact integrable_zero _ _ _

/-- **one block of the weighted expansion**: the expectation of the weighted value of the scaled term `Y` is the sum, over the
outputs of its dotted edge partition with their maps, of the expectations of the evaluated outputs -/
theorem lwProv_blk_EW (hG : GaussIBP sz) (hz : 0 < z.im) {m : ℂ} (hM : ∀ a, M a a = m) (P : PGraph (Fin 2))
    {I'' : Type} [Fintype I''] [DecidableEq I''] (t0 tg : ℕ × ℕ) (Y : LGraph P.E' I'')
    (emb : P.E' ⊕ P.I' → P.E' ⊕ I'') (W : (P.E' ⊕ P.I' → Idx d (sz.L n) (sz.W n)) → ℝ)
    (ℓ' : P.E' → Idx d (sz.L n) (sz.W n)) :
    lwProv_EW sz n z u M Sp (lwEngine_sc (lwEngine_ev3 m (tg + t0)) Y) (fun ℓ => W (ℓ ∘ emb)) ℓ' =
      ((lwProv_blk P tg Y emb).map fun o => ∫ ω, pvalW (lwEvX m (lwEngine_shift t0 (o.tag, o.Q)))
        (lwSampleData sz n z u M (lwS sz n u) Sp ω) (fun ℓ => W (ℓ ∘ o.π)) (ℓ' ∘ P.ext) ∂(Sizes.seqP sz)).sum := by
  have hMd : ∀ ω, ∀ a, (lwSampleData sz n z u M (lwS sz n u) Sp ω).M a a = m := fun ω a => hM a
  unfold lwProv_EW
  simp only [lwProv_valW_sc, lwProv_valW_partX m Y _ (hMd _) _ ℓ']
  rw [integral_const_mul, owx_integral_list_sum _ _ _ fun o _ => (lwProv_pvalW_integrable hG hz o.Q _ ℓ').const_mul _,
    lwProv_blk, List.map_map, ← List.sum_map_mul_left]
  refine congrArg List.sum (List.map_congr_left fun o _ => ?_)
  rw [← integral_const_mul]
  change _ = ∫ ω, pvalW (lwEvX m (lwEngine_shift t0 (tg + o.tag, o.Q.lvl1Comp P.ext P.ext_surj))) _
    (fun ℓ => W (ℓ ∘ (o.vm ∘ emb))) (ℓ' ∘ P.ext) ∂_
  refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
  refine Eq.trans ?_ (lwProv_pvalW_evX_pack m (t0 + (tg + o.tag)) P o.Q _ (fun ℓ => W (ℓ ∘ (o.vm ∘ emb))) ℓ').symm
  beta_reduce
  rw [← mul_assoc]
  refine congrArg (· * _) ?_
  simp only [lwEngine_ev3, Prod.fst_add, Prod.snd_add, pow_add]
  ring

end Blk

section Gen

/-- the outputs of a block factor their external map through that of the input -/
theorem lwProv_blk_ext (P : PGraph (Fin 2)) {I'' : Type} [Fintype I''] [DecidableEq I''] (tg : ℕ × ℕ) (Y : LGraph P.E' I'')
    (emb : P.E' ⊕ P.I' → P.E' ⊕ I'') : ∀ o ∈ lwProv_blk P tg Y emb, ∃ f : P.E' → o.Q.E', o.Q.ext = f ∘ P.ext := by
  intro o ho
  obtain ⟨o', -, rfl⟩ := List.mem_map.1 ho
  exact ⟨o'.Q.ext, rfl⟩

/-- **from the unpacked expansion to `WExp`**: if the weighted value of the evaluated input is the sum of the evaluated outputs at
the factored labels, and every output factors its external map through `P.ext`, then `WExp` holds for the evaluated lists -/
theorem lwProv_WExp_of_unpacked (m : ℂ) (t0 : ℕ × ℕ) (P : PGraph (Fin 2)) (ps : List (ProvOutX P))
    (Hext : ∀ o ∈ ps, ∃ f : P.E' → o.Q.E', o.Q.ext = f ∘ P.ext)
    (H : ∀ {d : ℕ} {sz : Sizes d} {n : ℕ} {z : ℂ} {u : ℝ}
      (Sp M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ),
      GaussIBP sz → 0 < z.im → 0 < u → m ≠ 0 → z + (u : ℂ) * m = -m⁻¹ →
      (∀ i j, Sp i j - m ^ 2 * ∑ w, Sp i w * lwS sz n u w j = lwS sz n u i j) → Spᵀ = Sp →
      (∀ a, M a a = m) → (∀ a b, a ≠ b → M a b = 0) →
      ∀ (W : (P.E' ⊕ P.I' → Idx d (sz.L n) (sz.W n)) → ℝ) (ℓ' : P.E' → Idx d (sz.L n) (sz.W n)),
        lwProv_EW sz n z u M Sp (lwEngine_sc (lwEngine_ev3 m t0) P.g) W ℓ' =
          (ps.map fun o => ∫ ω, pvalW (lwEvX m (lwEngine_shift t0 (o.tag, o.Q)))
            (lwSampleData sz n z u M (lwS sz n u) Sp ω) (fun ℓ => W (ℓ ∘ o.π)) (ℓ' ∘ P.ext) ∂(Sizes.seqP sz)).sum) :
    WExp m (lwEvX m (t0, P)) (ps.map fun o => mkProv m t0 P (o.tag, o.Q) o.π) := by
  intro d sz n z u Sp M hG hz hu hm0 hzm hSp hSpT hM hM0 W ℓe
  rw [List.map_map]
  by_cases h : ∃ ℓ' : P.E' → Idx d (sz.L n) (sz.W n), ℓe = ℓ' ∘ P.ext
  · obtain ⟨ℓ', rfl⟩ := h
    have e := H Sp M hG hz hu hm0 hzm hSp hSpT hM hM0 W ℓ'
    unfold lwProv_EW at e
    refine Eq.trans ?_ (e.trans rfl)
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    exact lwProv_pvalW_of_factor (lwEvX m (t0, P)) _ W rfl
  · have h0 : ∀ ω, pvalW (lwEvX m (t0, P)) (lwSampleData sz n z u M (lwS sz n u) Sp ω) W ℓe = 0 := fun ω =>
      lwProv_pvalW_of_not (lwEvX m (t0, P)) _ W h
    simp only [h0, integral_zero]
    symm
    refine List.sum_eq_zero fun x hx => ?_
    obtain ⟨o, ho, rfl⟩ := List.mem_map.1 hx
    obtain ⟨f, hf⟩ := Hext o ho
    have : ∀ ω, pvalW (lwEvX m (lwEngine_shift t0 (o.tag, o.Q))) (lwSampleData sz n z u M (lwS sz n u) Sp ω)
        (fun ℓ => W (ℓ ∘ o.π)) ℓe = 0 := fun ω => by
      refine lwProv_pvalW_of_not (lwEvX m (lwEngine_shift t0 (o.tag, o.Q))) _ _ ?_
      rintro ⟨ℓ'', hℓ''⟩
      exact h ⟨ℓ'' ∘ f, hℓ''.trans (by change ℓ'' ∘ o.Q.ext = _; rw [hf]; rfl)⟩
    simp only [Function.comp_apply, mkProv, this, integral_zero]

end Gen

section StepW

/-- **the weighted expansion of Step 1** (the `weight` constructor of `LocStepX`) at `(m, t0)` -/
theorem lwProv_weight_step (P : PGraph (Fin 2)) (p : SEdge (P.E' ⊕ P.I') × List (SEdge (P.E' ⊕ P.I')))
    (hp : p ∈ lwSplit P.g.solid) (x : P.E' ⊕ P.I') (c t : Bool) (hx : lwSymmTwistS c t p.1 = ⟨true, true, x, x⟩)
    (m : ℂ) (t0 : ℕ × ℕ) :
    WExp m (lwEvX m (t0, P)) ((lwProv_weightOuts P p x c t).map fun o => mkProv m t0 P (o.tag, o.Q) o.π) := by
  refine lwProv_WExp_of_unpacked m t0 P _ ?_ ?_
  · intro o ho
    simp only [lwProv_weightOuts, List.mem_append, List.mem_flatMap] at ho
    rcases ho with ((ho | ho) | ⟨q, -, ho⟩) | ⟨q, -, ho⟩ <;> exact lwProv_blk_ext P _ _ _ o ho
  · intro d sz n z u Sp M hG hz hu hm0 hzm hSp hSpT hM hM0 W ℓ'
    rw [lwProv_weight_EW' hG hz hu hm0 hzm hSp hSpT hM hM0 (lwEngine_sc (lwEngine_ev3 m t0) P.g) p hp x c t hx W ℓ']
    simp only [lwEngine_T1, lwEngine_T2, lwEngine_T3, lwEngine_T4, ← lwEngine_ev3_add, lwProv_blk_EW hG hz hM P t0,
      lwProv_weightOuts, List.map_append, List.sum_append, lvl1_sum_flatMap]

end StepW

section EdgeList

variable {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

theorem lwProv_frame_adj (c t : Bool) (Γ : LGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) :
    (lwSymmFrame c t Γ p).adj = Γ.adj := (lwSymmTwistG_adj c t _).trans (lwProv_adj_solid Γ _)

theorem lwProv_frame2_adj (c t : Bool) (Γ : LGraph E I) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) :
    (lwSymmFrame2 c t Γ p q).adj = Γ.adj := (lwSymmTwistG_adj c t _).trans (lwProv_adj_solid Γ _)

/-- an expansion along `id` (no new vertex), twisted, is an extension -/
theorem lwProv_ext_twist0 (Γ Z : LGraph E I) (hZ : Z.adj = Γ.adj) (c t : Bool) (κ : ℂ) (s : List (SEdge (E ⊕ I)))
    (w : List (WEdge (E ⊕ I))) : lwProv_Ext Γ (lwSymmTwistG c t (Z.owxExt id κ s w)) id := by
  refine ⟨fun u v h => ?_, fun a => rfl, fun v => ⟨v, SimpleGraph.Reachable.refl _⟩⟩
  rw [lwSymmTwistG_adj]
  exact oe2x_adj_owxExt Z id κ s w u v (by rw [hZ]; exact h)

end EdgeList

section EdgeStep

/-- the outputs of Step 2 (`lvl1EdgeOutsX`) with their vertex maps -/
def lwProv_edgeOuts (P : PGraph (Fin 2)) (p : SEdge (P.E' ⊕ P.I') × List (SEdge (P.E' ⊕ P.I'))) (x : P.I')
    (v : P.E' ⊕ P.I') (c t : Bool) : List (ProvOutX P) :=
  lwProv_blk P (lwEngine_sw c (1, 0)) (lwSymmOe1xOwx c t 1 P.g p x) (owxEmb 1) ++
    (lwSplit p.2).flatMap (fun q => (lwEngine_DsX c t P.g p x v q).flatMap (fun r => lwProv_blk P r.1 r.2 (owxEmb 1)))

theorem lwProv_edgeOuts_map (P : PGraph (Fin 2)) (p : SEdge (P.E' ⊕ P.I') × List (SEdge (P.E' ⊕ P.I'))) (x : P.I')
    (v : P.E' ⊕ P.I') (c t : Bool) :
    (lwProv_edgeOuts P p x v c t).map (fun o => (o.tag, o.Q)) = lvl1PackX P (lvl1EdgeOutsX P.g p x v c t) := by
  simp only [lwProv_edgeOuts, lvl1EdgeOutsX, lvl1PackX, List.map_append, List.map_flatMap, lwProv_blk_map]

theorem lwProv_edgeOuts_ext (P : PGraph (Fin 2)) (p : SEdge (P.E' ⊕ P.I') × List (SEdge (P.E' ⊕ P.I'))) (x : P.I')
    (v : P.E' ⊕ P.I') (c t : Bool) :
    ∀ o ∈ lwProv_edgeOuts P p x v c t, ∃ f : P.E' → o.Q.E', o.Q.ext = f ∘ P.ext := by
  intro o ho
  simp only [lwProv_edgeOuts, List.mem_append, List.mem_flatMap] at ho
  rcases ho with ho | ⟨q, -, r, -, ho⟩ <;> exact lwProv_blk_ext P _ _ _ o ho

theorem lwProv_edgeOuts_mol (P : PGraph (Fin 2)) (p : SEdge (P.E' ⊕ P.I') × List (SEdge (P.E' ⊕ P.I'))) (x : P.I')
    (v : P.E' ⊕ P.I') (c t : Bool) :
    ∀ o ∈ lwProv_edgeOuts P p x v c t, o.ExtOK ∧ (⟨o.Q, o.π⟩ : ProvOut P).Molecular := by
  intro o ho
  simp only [lwProv_edgeOuts, List.mem_append, List.mem_flatMap] at ho
  rcases ho with ho | ⟨q, -, r, hr, ho⟩
  · refine lwProv_blk_mol P _ _ _ ?_ o ho
    simp only [lwSymmOe1xOwx, owxT1]
    exact lwProv_ext_twist1 P.g _ (lwProv_frame_adj c t P.g p) c t _ _ _ (Sum.inr x) false true (List.mem_singleton.2 rfl)
  · refine lwProv_blk_mol P _ _ _ ?_ o ho
    simp only [lwEngine_DsX, lwEngine_oe1xDsX, List.mem_map] at hr
    obtain ⟨r0, hr0, rfl⟩ := hr
    split_ifs at hr0 <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at hr0 <;>
      (try rcases hr0 with rfl | rfl) <;>
      exact lwProv_ext_twist1 P.g _ ((lwProv_adj_solid _ _).trans (lwProv_frame_adj c t P.g p)) c t _ _ _ (Sum.inr x) false true
        (List.mem_singleton.2 rfl)

/-- **the weighted expansion of Step 2** (the `edge` constructor of `LocStepX`, on a normal input) at `(m, t0)` -/
theorem lwProv_edge_step (P : PGraph (Fin 2)) (hN : P.g.Normal)
    (p : SEdge (P.E' ⊕ P.I') × List (SEdge (P.E' ⊕ P.I'))) (hp : p ∈ lwSplit P.g.solid) (x : P.I')
    (v : P.E' ⊕ P.I') (hv : v ≠ Sum.inr x) (c t : Bool)
    (hx : lwSymmTwistS c t p.1 = ⟨true, p.1.circ, Sum.inr x, v⟩) (m : ℂ) (t0 : ℕ × ℕ) :
    WExp m (lwEvX m (t0, P)) ((lwProv_edgeOuts P p x v c t).map fun o => mkProv m t0 P (o.tag, o.Q) o.π) := by
  refine lwProv_WExp_of_unpacked m t0 P _ (lwProv_edgeOuts_ext P p x v c t) ?_
  intro d sz n z u Sp M hG hz hu hm0 hzm hSp hSpT hM hM0 W ℓ'
  rw [lwProv_edge_EW' hG hz hu hm0 hzm hSpT hM hM0 (lwEngine_sc (lwEngine_ev3 m t0) P.g) hN p hp x v hv c t hx W ℓ']
  have hblk : ∀ (tg : ℕ × ℕ) (Y : LGraph P.E' (P.I' ⊕ Fin 1)),
      lwProv_EW sz n z u M Sp (lwEngine_sc (lwEngine_ev3 m (tg + t0)) Y) (fun ℓ => W fun x => ℓ (owxEmb 1 x)) ℓ' =
        ((lwProv_blk P tg Y (owxEmb 1)).map fun o => ∫ ω, pvalW (lwEvX m (lwEngine_shift t0 (o.tag, o.Q)))
          (lwSampleData sz n z u M (lwS sz n u) Sp ω) (fun ℓ => W (ℓ ∘ o.π)) (ℓ' ∘ P.ext) ∂(Sizes.seqP sz)).sum :=
    fun tg Y => lwProv_blk_EW hG hz hM P t0 tg Y (owxEmb 1) W ℓ'
  simp only [lwEngine_Oe1xOwx, lwEngine_Ds, List.map_map, Function.comp_def, ← lwEngine_ev3_add, hblk, lwProv_edgeOuts,
    List.map_append, List.sum_append, lvl1_sum_flatMap]

end EdgeStep

section GGStep

/-- the outputs of Step 3 (`lvl1GGOutsX`) with their vertex maps -/
def lwProv_ggOuts (P : PGraph (Fin 2)) (p q : SEdge (P.E' ⊕ P.I') × List (SEdge (P.E' ⊕ P.I'))) (x : P.I')
    (y y' : P.E' ⊕ P.I') (c t : Bool) : List (ProvOutX P) :=
  lwProv_blk P (lwEngine_sw c (3, 0)) (lwSymmOe2xR2 c t 1 P.g p q x y y') id ++
    lwProv_blk P (lwEngine_sw c (1, 0)) (lwSymmOe2xR3 c t 1 P.g p q x) (owxEmb 1) ++
    lwProv_blk P (lwEngine_sw c (3, 0)) (lwSymmOe2xR4 c t 1 P.g p q x y y') (owxEmb 2) ++
    lwProv_blk P (lwEngine_sw c (1, 0)) (lwSymmOe2xR5 c t 1 P.g p q x y y') (owxEmb 1) ++
    lwProv_blk P (lwEngine_sw c (3, 0)) (lwSymmOe2xR6 c t 1 P.g p q x y y') (owxEmb 2) ++
    (lwSplit q.2).flatMap (fun q' => lwProv_blk P (lwEngine_sw c (1, 0)) (lwSymmOe2xR7 c t 1 P.g p q x y y' q') (owxEmb 1)) ++
    (lwSplit q.2).flatMap (fun q' => lwProv_blk P (lwEngine_sw c (3, 0)) (lwSymmOe2xR8 c t 1 P.g p q x y y' q') (owxEmb 2))

theorem lwProv_ggOuts_map (P : PGraph (Fin 2)) (p q : SEdge (P.E' ⊕ P.I') × List (SEdge (P.E' ⊕ P.I'))) (x : P.I')
    (y y' : P.E' ⊕ P.I') (c t : Bool) :
    (lwProv_ggOuts P p q x y y' c t).map (fun o => (o.tag, o.Q)) = lvl1PackX P (lvl1GGOutsX P.g p q x y y' c t) := by
  simp only [lwProv_ggOuts, lvl1GGOutsX, lvl1PackX, List.map_append, List.map_flatMap, lwProv_blk_map]

theorem lwProv_ggOuts_ext (P : PGraph (Fin 2)) (p q : SEdge (P.E' ⊕ P.I') × List (SEdge (P.E' ⊕ P.I'))) (x : P.I')
    (y y' : P.E' ⊕ P.I') (c t : Bool) :
    ∀ o ∈ lwProv_ggOuts P p q x y y' c t, ∃ f : P.E' → o.Q.E', o.Q.ext = f ∘ P.ext := by
  intro o ho
  simp only [lwProv_ggOuts, List.mem_append, List.mem_flatMap] at ho
  rcases ho with (((((ho | ho) | ho) | ho) | ho) | ⟨q', -, ho⟩) | ⟨q', -, ho⟩ <;> exact lwProv_blk_ext P _ _ _ o ho

theorem lwProv_ggOuts_mol (P : PGraph (Fin 2)) (p q : SEdge (P.E' ⊕ P.I' ) × List (SEdge (P.E' ⊕ P.I'))) (x : P.I')
    (y y' : P.E' ⊕ P.I') (c t : Bool) :
    ∀ o ∈ lwProv_ggOuts P p q x y y' c t, o.ExtOK ∧ (⟨o.Q, o.π⟩ : ProvOut P).Molecular := by
  intro o ho
  simp only [lwProv_ggOuts, List.mem_append, List.mem_flatMap] at ho
  have hZ : ∀ s, ({ lwSymmFrame2 c t P.g p q with solid := s } : LGraph P.E' P.I').adj = P.g.adj := fun s =>
    (lwProv_adj_solid _ _).trans (lwProv_frame2_adj c t P.g p q)
  rcases ho with (((((ho | ho) | ho) | ho) | ho) | ⟨q', -, ho⟩) | ⟨q', -, ho⟩
  · refine lwProv_blk_mol P _ _ _ ?_ o ho
    simp only [lwSymmOe2xR2, oe2xR2]
    exact lwProv_ext_twist0 P.g _ (hZ _) c t _ _ _
  · refine lwProv_blk_mol P _ _ _ ?_ o ho
    simp only [lwSymmOe2xR3, owxT1]
    exact lwProv_ext_twist1 P.g _ (lwProv_frame2_adj c t P.g p q) c t _ _ _ (Sum.inr x) false true (List.mem_singleton.2 rfl)
  · refine lwProv_blk_mol P _ _ _ ?_ o ho
    simp only [lwSymmOe2xR4, oe2xR4]
    exact lwProv_ext_twist2 P.g _ (hZ _) c t _ _ _ (Sum.inr x) true true false true List.mem_cons_self
      (List.mem_cons_of_mem _ (List.mem_singleton.2 rfl))
  · refine lwProv_blk_mol P _ _ _ ?_ o ho
    simp only [lwSymmOe2xR5, oe2xR5]
    exact lwProv_ext_twist1 P.g _ (hZ _) c t _ _ _ (Sum.inr x) false true (List.mem_singleton.2 rfl)
  · refine lwProv_blk_mol P _ _ _ ?_ o ho
    simp only [lwSymmOe2xR6, oe2xR6]
    exact lwProv_ext_twist2 P.g _ (hZ _) c t _ _ _ (Sum.inr x) true true false true List.mem_cons_self
      (List.mem_cons_of_mem _ (List.mem_singleton.2 rfl))
  · refine lwProv_blk_mol P _ _ _ ?_ o ho
    simp only [lwSymmOe2xR7, oe2xR7]
    exact lwProv_ext_twist1 P.g _ (hZ _) c t _ _ _ (Sum.inr x) false true (List.mem_singleton.2 rfl)
  · refine lwProv_blk_mol P _ _ _ ?_ o ho
    simp only [lwSymmOe2xR8, oe2xR8]
    exact lwProv_ext_twist2 P.g _ (hZ _) c t _ _ _ (Sum.inr x) true true false true List.mem_cons_self
      (List.mem_cons_of_mem _ (List.mem_singleton.2 rfl))

/-- **the weighted expansion of Step 3** (the `gg` constructor of `LocStepX`, on a normal input) at `(m, t0)` -/
theorem lwProv_gg_step (P : PGraph (Fin 2)) (hN : P.g.Normal)
    (p q : SEdge (P.E' ⊕ P.I') × List (SEdge (P.E' ⊕ P.I'))) (hp : p ∈ lwSplit P.g.solid) (hq : q ∈ lwSplit p.2)
    (x : P.I') (y y' : P.E' ⊕ P.I') (hy : y ≠ Sum.inr x) (c t : Bool)
    (hp1 : lwSymmTwistS c t p.1 = ⟨true, p.1.circ, Sum.inr x, y⟩)
    (hq1 : lwSymmTwistS c t q.1 = ⟨true, q.1.circ, y', Sum.inr x⟩) (hwf : ∀ e ∈ P.g.solid, e.src ≠ e.dst)
    (m : ℂ) (t0 : ℕ × ℕ) :
    WExp m (lwEvX m (t0, P)) ((lwProv_ggOuts P p q x y y' c t).map fun o => mkProv m t0 P (o.tag, o.Q) o.π) := by
  have hqne : q.1.src ≠ q.1.dst := hwf q.1 (lvl1_mem_split _ p hp q.1 (lvl1_mem_split_fst _ q hq))
  have hy' : y' ≠ Sum.inr x := fun h => hqne (by rw [← lwSymmTwistS_loop c t q.1, hq1]; exact h)
  apply lwProv_WExp_of_unpacked m t0 P (lwProv_ggOuts P p q x y y' c t) (lwProv_ggOuts_ext P p q x y y' c t)
  intro d sz n z u Sp M hG hz hu hm0 hzm hSp hSpT hM hM0 W ℓ'
  rw [lwProv_gg_EW' hG hz hu hm0 hzm hSp hSpT hM hM0 (lwEngine_sc (lwEngine_ev3 m t0) P.g) hN x y y' hy hy' p hp q hq c t
    hp1 hq1 W ℓ']
  have hblk : ∀ (k : ℕ) (emb : P.E' ⊕ P.I' → P.E' ⊕ (P.I' ⊕ Fin k)) (tg : ℕ × ℕ) (Y : LGraph P.E' (P.I' ⊕ Fin k)),
      lwProv_EW sz n z u M Sp (lwEngine_sc (lwEngine_ev3 m (tg + t0)) Y) (fun ℓ => W (ℓ ∘ emb)) ℓ' =
        ((lwProv_blk P tg Y emb).map fun o => ∫ ω, pvalW (lwEvX m (lwEngine_shift t0 (o.tag, o.Q)))
          (lwSampleData sz n z u M (lwS sz n u) Sp ω) (fun ℓ => W (ℓ ∘ o.π)) (ℓ' ∘ P.ext) ∂(Sizes.seqP sz)).sum :=
    fun k emb tg Y => lwProv_blk_EW hG hz hM P t0 tg Y emb W ℓ'
  have hblk1 : ∀ (tg : ℕ × ℕ) (Y : LGraph P.E' (P.I' ⊕ Fin 1)),
      lwProv_EW sz n z u M Sp (lwEngine_sc (lwEngine_ev3 m (tg + t0)) Y) (fun ℓ => W (ℓ ∘ owxEmb 1)) ℓ' =
        ((lwProv_blk P tg Y (owxEmb 1)).map fun o => ∫ ω, pvalW (lwEvX m (lwEngine_shift t0 (o.tag, o.Q)))
          (lwSampleData sz n z u M (lwS sz n u) Sp ω) (fun ℓ => W (ℓ ∘ o.π)) (ℓ' ∘ P.ext) ∂(Sizes.seqP sz)).sum :=
    fun tg Y => hblk 1 (owxEmb 1) tg Y
  have hblk2 : ∀ (tg : ℕ × ℕ) (Y : LGraph P.E' (P.I' ⊕ Fin 2)),
      lwProv_EW sz n z u M Sp (lwEngine_sc (lwEngine_ev3 m (tg + t0)) Y) (fun ℓ => W (ℓ ∘ owxEmb 2)) ℓ' =
        ((lwProv_blk P tg Y (owxEmb 2)).map fun o => ∫ ω, pvalW (lwEvX m (lwEngine_shift t0 (o.tag, o.Q)))
          (lwSampleData sz n z u M (lwS sz n u) Sp ω) (fun ℓ => W (ℓ ∘ o.π)) (ℓ' ∘ P.ext) ∂(Sizes.seqP sz)).sum :=
    fun tg Y => hblk 2 (owxEmb 2) tg Y
  have hblk0 : ∀ (tg : ℕ × ℕ) (Y : LGraph P.E' P.I'),
      lwProv_EW sz n z u M Sp (lwEngine_sc (lwEngine_ev3 m (tg + t0)) Y) W ℓ' =
        ((lwProv_blk P tg Y id).map fun o => ∫ ω, pvalW (lwEvX m (lwEngine_shift t0 (o.tag, o.Q)))
          (lwSampleData sz n z u M (lwS sz n u) Sp ω) (fun ℓ => W (ℓ ∘ o.π)) (ℓ' ∘ P.ext) ∂(Sizes.seqP sz)).sum :=
    fun tg Y => lwProv_blk_EW hG hz hM P t0 tg Y id W ℓ'
  simp only [lwEngine_R2, lwEngine_R3, lwEngine_R4, lwEngine_R5, lwEngine_R6, lwEngine_R7, lwEngine_R8, ← lwEngine_ev3_add,
    hblk0, hblk1, hblk2, lwProv_ggOuts, List.map_append, List.sum_append, lvl1_sum_flatMap]

end GGStep


/-! ## 7. The step lemma with positions, the recursion, `lw_localregularXP` -/

section Rec

/-- **the step lemma with positions** (the content of `lwProv_LocStepXProvPos`, the position-indexed provenance step (Amend 2)) -/
theorem lwProv_stepPos (P : PGraph (Fin 2)) (LX : List ((ℕ × ℕ) × PGraph (Fin 2))) (h : LocStepX P LX)
    (hN : P.g.Normal) : ∃ ps : List (ProvOutX P), ps.map (fun o => (o.tag, o.Q)) = LX ∧
      (∀ o ∈ ps, o.ExtOK ∧ (⟨o.Q, o.π⟩ : ProvOut P).Molecular) ∧ ∀ (m : ℂ) (t0 : ℕ × ℕ),
        WExp m (lwEvX m (t0, P)) (ps.map fun o => mkProv m t0 P (o.tag, o.Q) o.π) := by
  cases h with
  | weight p hp x c t hx =>
    exact ⟨_, lwProv_weightOuts_map P p x c t, lwProv_weightOuts_mol P p x c t, fun m t0 => lwProv_weight_step P p hp x c t hx m t0⟩
  | edge p hp x v hv c t hx hwf hbad =>
    exact ⟨_, lwProv_edgeOuts_map P p x v c t, lwProv_edgeOuts_mol P p x v c t,
      fun m t0 => lwProv_edge_step P hN p hp x v hv c t hx m t0⟩
  | gg p q hp hq x y y' hy c t hp1 hq1 hwf hnb =>
    exact ⟨_, lwProv_ggOuts_map P p q x y y' c t, lwProv_ggOuts_mol P p q x y y' c t,
      fun m t0 => lwProv_gg_step P hN p q hp hq x y y' hy c t hp1 hq1 hwf m t0⟩

/-- the composite of two outputs -/
def lwProv_comp {P : PGraph (Fin 2)} (o : ProvOutX P) (o' : ProvOutX o.Q) : ProvOutX P := ⟨o.tag + o'.tag, o'.Q, o'.π ∘ o.π⟩

/-- the leaf: the graph itself with the identity map -/
def lwProv_id (P : PGraph (Fin 2)) : ProvOutX P := ⟨(0, 0), P, id⟩

private theorem lwProv_comp_ok {P : PGraph (Fin 2)} {o : ProvOutX P} {o' : ProvOutX o.Q}
    (h : o.ExtOK ∧ (⟨o.Q, o.π⟩ : ProvOut P).Molecular) (h' : o'.ExtOK ∧ (⟨o'.Q, o'.π⟩ : ProvOut o.Q).Molecular) :
    (lwProv_comp o o').ExtOK ∧ (⟨(lwProv_comp o o').Q, (lwProv_comp o o').π⟩ : ProvOut P).Molecular := by
  exact ⟨fun i => (congrArg o'.π (h.1 i)).trans (h'.1 i),
    ProvOut.Molecular.comp (o := ⟨o.Q, o.π⟩) (o' := ⟨o'.Q, o'.π⟩) h.2 h'.2⟩

theorem lwProv_id_ok (P : PGraph (Fin 2)) : (lwProv_id P).ExtOK ∧ (⟨(lwProv_id P).Q, (lwProv_id P).π⟩ : ProvOut P).Molecular :=
  ⟨fun i => rfl, lwProv_molecular (⟨P, id⟩ : ProvOut P) (fun u v h => Or.inr h) (fun w => ⟨w, SimpleGraph.Reachable.refl _⟩)
    (fun a => ⟨a, rfl⟩)⟩

/-- **composition of weighted expansions, with positions** (`WExp.comp`) -/
theorem lwProv_WExp_comp_pos {m : ℂ} {P : PGraph (Fin 2)} {α : Type*} (ps : List α) (f : α → ProvOut P)
    (h : WExp m P (ps.map f)) (c₁ c₂ : ∀ a, List (ProvOut (f a).Q)) (h' : ∀ a ∈ ps, WExp m (f a).Q (c₁ a ++ c₂ a)) :
    WExp m P (ps.flatMap (fun a => (c₁ a).map (f a).comp) ++ ps.flatMap (fun a => (c₂ a).map (f a).comp)) := by
  intro d sz n z u Sp M hG hz hu hm0 hzm hSp hSpT hM hM0 W ℓe
  rw [h Sp M hG hz hu hm0 hzm hSp hSpT hM hM0 W ℓe, List.map_append, List.sum_append, lvl1_sum_flatMap, lvl1_sum_flatMap,
    ← List.sum_map_add, List.map_map]
  refine congrArg List.sum (List.map_congr_left fun a ha => ?_)
  have := h' a ha Sp M hG hz hu hm0 hzm hSp hSpT hM hM0 (fun ℓ => W (ℓ ∘ (f a).π)) ℓe
  rw [List.map_append, List.sum_append] at this
  simp only [Function.comp_apply, this, List.map_map]
  rfl

theorem lwProv_mk_comp (m : ℂ) (t0 : ℕ × ℕ) {Γ : PGraph (Fin 2)} (o : ProvOutX Γ) (o' : ProvOutX o.Q) :
    mkProv m t0 Γ ((lwProv_comp o o').tag, (lwProv_comp o o').Q) (lwProv_comp o o').π =
      (mkProv m t0 Γ (o.tag, o.Q) o.π).comp (mkProv m (t0 + o.tag) o.Q (o'.tag, o'.Q) o'.π) := by
  exact congrArg (fun v => (⟨lwEvX m (v, o'.Q), o'.π ∘ o.π⟩ : ProvOut (lwEvX m (t0, Γ)))) (add_assoc t0 o.tag o'.tag).symm

/-- **the recursion with provenance** (`lwEngine_exists` with maps) -/
theorem lwProv_exists (K : ℤ) (Γ : PGraph (Fin 2)) (hN : Γ.g.Normal) :
    ∃ oP eP : List (ProvOutX Γ), (∀ o ∈ oP ++ eP, o.ExtOK ∧ (⟨o.Q, o.π⟩ : ProvOut Γ).Molecular) ∧
      ∀ (m : ℂ) (t0 : ℕ × ℕ),
        lwEngine_Exp m K (lwEvX m (t0, Γ)) (oP.map fun o => lwEvX m (lwEngine_shift t0 (o.tag, o.Q)))
          (eP.map fun o => lwEvX m (lwEngine_shift t0 (o.tag, o.Q))) ∧
        WExp m (lwEvX m (t0, Γ)) ((oP ++ eP).map fun o => mkProv m t0 Γ (o.tag, o.Q) o.π) := by
  classical
  induction Γ using (InvImage.wf (Lvl1Mu K) lvl1Lt_wf).induction with
  | _ Γ ih =>
    have hid : ∀ (m : ℂ) (t0 : ℕ × ℕ), WExp m (lwEvX m (t0, Γ)) [mkProv m t0 Γ ((lwProv_id Γ).tag, (lwProv_id Γ).Q) (lwProv_id Γ).π] :=
      fun m t0 => WExp.refl m (lwEvX m (t0, Γ))
    by_cases hK : K ≤ ord Γ.g.counters
    · refine ⟨[], [lwProv_id Γ], fun o ho => ?_, fun m t0 => ⟨⟨by simp, ?_, ?_, ?_⟩, hid m t0⟩⟩
      · simp only [List.nil_append, List.mem_singleton] at ho
        subst ho
        exact lwProv_id_ok Γ
      · intro Q hQ
        simp only [lwProv_id, lwEngine_shift, List.map_cons, List.map_nil, List.mem_singleton] at hQ
        subst hQ
        exact hK
      · intro Q hQ
        simp only [lwProv_id, lwEngine_shift, List.map_cons, List.map_nil, List.nil_append, List.mem_singleton,
          Prod.mk_zero_zero, add_zero] at hQ
        subst hQ
        exact Lvl1Reach.refl _
      · intro d sz n z u Sp M _ _ _ _ _ _ _ _ _ ℓe
        simp [lwProv_id, lwEngine_shift, Prod.mk_zero_zero, add_zero]
    have hlt : ord Γ.g.counters < K := by omega
    by_cases hL : Γ.g.LocStd
    · refine ⟨[lwProv_id Γ], [], fun o ho => ?_, fun m t0 => ⟨⟨?_, by simp, ?_, ?_⟩, by rw [List.append_nil]; exact hid m t0⟩⟩
      · simp only [List.append_nil, List.mem_singleton] at ho
        subst ho
        exact lwProv_id_ok Γ
      · intro Q hQ
        simp only [lwProv_id, lwEngine_shift, List.map_cons, List.map_nil, List.mem_singleton] at hQ
        subst hQ
        exact ⟨hL, hlt⟩
      · intro Q hQ
        simp only [lwProv_id, lwEngine_shift, List.map_cons, List.map_nil, List.append_nil, List.mem_singleton,
          Prod.mk_zero_zero, add_zero] at hQ
        subst hQ
        exact Lvl1Reach.refl _
      · intro d sz n z u Sp M _ _ _ _ _ _ _ _ _ ℓe
        simp [lwProv_id, lwEngine_shift, Prod.mk_zero_zero, add_zero]
    obtain ⟨LX, hLX⟩ := lwEngine_exists_stepX Γ hN hL
    obtain ⟨ps, hpsLX, hpsok, hpsW⟩ := lwProv_stepPos Γ LX hLX hN
    have hgood := lvl1_step_good (hLX.eval 1 0) hN
    have hch : ∀ o ∈ ps, Lvl1Lt (Lvl1Mu K o.Q) (Lvl1Mu K Γ) ∧ o.Q.g.Normal := by
      intro o ho
      have hr : (o.tag, o.Q) ∈ LX := hpsLX ▸ List.mem_map_of_mem ho
      have := hgood (lwEvX 1 (lwEngine_shift 0 (o.tag, o.Q))) (List.mem_map_of_mem (List.mem_map_of_mem hr))
      exact ⟨lvl1_mu_lt hlt this.2, this.1⟩
    have hall : ∀ o : ProvOutX Γ, ∃ oc ec : List (ProvOutX o.Q), o ∈ ps →
        ((∀ o' ∈ oc ++ ec, o'.ExtOK ∧ (⟨o'.Q, o'.π⟩ : ProvOut o.Q).Molecular) ∧ ∀ (m : ℂ) (t0 : ℕ × ℕ),
          lwEngine_Exp m K (lwEvX m (t0, o.Q)) (oc.map fun o' => lwEvX m (lwEngine_shift t0 (o'.tag, o'.Q)))
            (ec.map fun o' => lwEvX m (lwEngine_shift t0 (o'.tag, o'.Q))) ∧
          WExp m (lwEvX m (t0, o.Q)) ((oc ++ ec).map fun o' => mkProv m t0 o.Q (o'.tag, o'.Q) o'.π)) := by
      intro o
      by_cases ho : o ∈ ps
      · obtain ⟨oc, ec, h⟩ := ih o.Q (hch o ho).1 (hch o ho).2
        exact ⟨oc, ec, fun _ => h⟩
      · exact ⟨[], [], fun h => absurd h ho⟩
    choose foP feP hfoP using hall
    refine ⟨ps.flatMap (fun o => (foP o).map (lwProv_comp o)), ps.flatMap (fun o => (feP o).map (lwProv_comp o)),
      fun o2 ho2 => ?_, fun m t0 => ⟨?_, ?_⟩⟩
    · simp only [List.mem_append, List.mem_flatMap, List.mem_map] at ho2
      rcases ho2 with ⟨o, ho, o', ho', rfl⟩ | ⟨o, ho, o', ho', rfl⟩
      · exact lwProv_comp_ok (hpsok o ho) ((hfoP o ho).1 o' (List.mem_append_left _ ho'))
      · exact lwProv_comp_ok (hpsok o ho) ((hfoP o ho).1 o' (List.mem_append_right _ ho'))
    · have hst : LocStep m (lwEvX m (t0, Γ)) (ps.map fun o => lwEvX m (lwEngine_shift t0 (o.tag, o.Q))) := by
        have := hLX.eval m t0
        rwa [← hpsLX, List.map_map, List.map_map] at this
      have key := lwEngine_combine (α := ProvOutX Γ) (m := m) (Γ := lwEvX m (t0, Γ)) hN hlt hL ps
        (fun o => lwEvX m (lwEngine_shift t0 (o.tag, o.Q))) hst
        (fun o => (foP o).map fun o' => lwEvX m (lwEngine_shift (t0 + o.tag) (o'.tag, o'.Q)))
        (fun o => (feP o).map fun o' => lwEvX m (lwEngine_shift (t0 + o.tag) (o'.tag, o'.Q)))
        (fun o ho => ((hfoP o ho).2 m (t0 + o.tag)).1)
      have e1 : ∀ F : ∀ o : ProvOutX Γ, List (ProvOutX o.Q),
          (ps.flatMap fun o => (F o).map (lwProv_comp o)).map (fun o => lwEvX m (lwEngine_shift t0 (o.tag, o.Q))) =
            ps.flatMap fun o => (F o).map fun o' => lwEvX m (lwEngine_shift (t0 + o.tag) (o'.tag, o'.Q)) := by
        intro F
        rw [List.map_flatMap]
        refine List.flatMap_congr fun o _ => ?_
        simp only [List.map_map, Function.comp_def, lwProv_comp, lwEngine_shift, add_assoc]
      rw [e1 foP, e1 feP]
      exact key
    · have hEq : ((ps.flatMap (fun o => (foP o).map (lwProv_comp o)) ++ ps.flatMap (fun o => (feP o).map (lwProv_comp o))).map
          fun o => mkProv m t0 Γ (o.tag, o.Q) o.π) =
          ps.flatMap (fun (o : ProvOutX Γ) => ((foP o).map fun o' => mkProv m (t0 + o.tag) o.Q (o'.tag, o'.Q) o'.π).map
            (mkProv m t0 Γ (o.tag, o.Q) o.π).comp) ++
          ps.flatMap (fun (o : ProvOutX Γ) => ((feP o).map fun o' => mkProv m (t0 + o.tag) o.Q (o'.tag, o'.Q) o'.π).map
            (mkProv m t0 Γ (o.tag, o.Q) o.π).comp) := by
        simp only [List.map_append, List.map_flatMap, List.map_map, Function.comp_def, lwProv_mk_comp]
        exact congrArg₂ _
          (List.flatMap_congr fun o _ => (List.map_map (g := (mkProv m t0 Γ (o.tag, o.Q) o.π).comp)
            (f := fun (o' : ProvOutX o.Q) => mkProv m (t0 + o.tag) o.Q (o'.tag, o'.Q) o'.π) (l := foP o)).symm)
          (List.flatMap_congr fun o _ => (List.map_map (g := (mkProv m t0 Γ (o.tag, o.Q) o.π).comp)
            (f := fun (o' : ProvOutX o.Q) => mkProv m (t0 + o.tag) o.Q (o'.tag, o'.Q) o'.π) (l := feP o)).symm)
      rw [hEq]
      apply lwProv_WExp_comp_pos (m := m) (α := ProvOutX Γ) ps (fun (o : ProvOutX Γ) => mkProv m t0 Γ (o.tag, o.Q) o.π)
        (hpsW m t0)
      intro o ho
      exact (congrArg (fun L => WExp m (lwEvX m (t0 + o.tag, o.Q)) L) (List.map_append ..)).mp
        ((hfoP o ho).2 m (t0 + o.tag)).2

end Rec

section Engine

/-- the evaluation at the tag `0` of a graph of coefficient `1` is the graph (`pvalW` level) -/
theorem lwProv_WExp_ev0 {m : ℂ} {P : PGraph (Fin 2)} (hc : P.g.coeff = 1) (outs : List (ProvOut (lwEvX m ((0, 0), P))))
    (h : WExp m (lwEvX m ((0, 0), P)) outs) : WExp m P (outs.map fun o => (⟨o.Q, o.π⟩ : ProvOut P)) := by
  intro d sz n z u Sp M hG hz hu hm0 hzm hSp hSpT hM hM0 W ℓe
  rw [List.map_map]
  refine Eq.trans ?_ (h Sp M hG hz hu hm0 hzm hSp hSpT hM hM0 W ℓe)
  refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
  refine ((lwProv_pvalW_evX m ((0, 0), P) _ W ℓe).trans ?_).symm
  simp [lwEngine_ev3]

/-- **`lw_localregularX` with provenance** (`LWEngineProv`) -/
theorem lw_localregularXP : LWEngineProv := by
  intro p c hc K0 d D
  obtain ⟨oP, eP, hok, h⟩ := lwProv_exists (lvl1Cutoff c K0 d D (fxyPowGraph p).pack.g.counters : ℤ) (fxyPowGraph p).pack
    (fxyPowGraph_normal p)
  refine ⟨oP, eP, fun o ho => ⟨(hok o ho).1, ?_⟩, fun m _ => ?_⟩
  · exact CoverBy.comp (P := (fxyPowGraph p).pack) (lwProv_fxyCover p) (hok o ho).2
  obtain ⟨hExp, hW⟩ := h m (0, 0)
  have e0 : lwEvX m ((0, 0), (fxyPowGraph p).pack) = (fxyPowGraph p).pack := lwEngine_ev_zero m _ rfl
  have eL : ∀ L : List (ProvOutX (fxyPowGraph p).pack), (L.map fun o => lwEvX m (lwEngine_shift (0, 0) (o.tag, o.Q))) =
      (L.map (·.ev m)).map (·.Q) := fun L => by simp [ProvOutX.ev, lwEngine_shift, Prod.mk_zero_zero, zero_add]
  rw [e0, eL, eL] at hExp
  refine ⟨lwEngine_assemble p m c hc K0 d D _ _ hExp, fun Q hQ => ?_, ?_⟩
  · simp only [List.map_append, List.mem_append] at hQ
    have := lw_nWS_ge (hExp.2.2.1 Q (by simpa only [List.mem_append] using hQ))
    rw [lwEngine_fxy_nWS] at this
    exact this
  · have hE : ((oP ++ eP).map (·.ev m)) = ((oP ++ eP).map fun o => mkProv m (0, 0) (fxyPowGraph p).pack (o.tag, o.Q) o.π).map
        fun o => (⟨o.Q, o.π⟩ : ProvOut (fxyPowGraph p).pack) := by
      simp only [List.map_map, Function.comp_def, ProvOutX.ev, mkProv, lwEngine_shift]
      exact List.map_congr_left fun o _ => congrArg (fun v => (⟨lwEvX m (v, o.Q), o.π⟩ : ProvOut (fxyPowGraph p).pack))
        (zero_add o.tag).symm
    rw [hE]
    apply lwProv_WExp_ev0 (m := m) (P := (fxyPowGraph p).pack) rfl
    exact hW

end Engine


/-! ## 8. Compiled instances -/

namespace LWProvInst

/-- the identity map is molecular (the induction start of `CoverBy.comp`) -/
theorem ProvOut.molecular_id (P : PGraph (Fin 2)) : (⟨P, id⟩ : ProvOut P).Molecular := (lwProv_id_ok P).2

/-- `valW_one`, `pvalW_one` at `fxyPowGraph 2`, the data of `lwEngine_inst_step1_identity` at the sample `ω = 0` -/
example : pvalW (fxyPowGraph 2).pack (lwSampleData lwWxInstSz 0 (zt 0 (1 / 2)) (1 / 2) lwWxInstM
    (lwS lwWxInstSz 0 (1 / 2)) lwWxInstSp 0) (fun _ => 1) lwSymmInstL =
    (fxyPowGraph 2).pack.val (lwSampleData lwWxInstSz 0 (zt 0 (1 / 2)) (1 / 2) lwWxInstM (lwS lwWxInstSz 0 (1 / 2))
      lwWxInstSp 0) lwSymmInstL := pvalW_one _ _ _

/-- the leaf composed with itself: `WExp.refl`, `WExp.comp` at `fxyPowGraph 2` -/
example (m : ℂ) : ∃ outs : List (ProvOut (fxyPowGraph 2).pack), WExp m (fxyPowGraph 2).pack outs :=
  ⟨_, WExp.comp (WExp.refl m _) (fun o => [⟨o.Q, id⟩]) fun o _ => WExp.refl m o.Q⟩

/-- `Molecular.comp`, `CoverBy.comp` at the identity maps of `fxyPowGraph 2`; the initial coverage is proved -/
example : ((⟨_, id⟩ : ProvOut (fxyPowGraph 2).pack).comp ⟨_, id⟩).Molecular :=
  (ProvOut.molecular_id _).comp (ProvOut.molecular_id _)
example : CoverBy (P := (fxyPowGraph 2).pack) fun k : Fin 2 => Sum.inr (localReg_fxyBeta k) :=
  CoverBy.comp (lwProv_fxyCover 2) (ProvOut.molecular_id _)

/-- **`lw_localregularXP`** at `p = 2`, `c = 1/4`, `K0 = 1`, `d = 3`, `D = 10` (the only hypothesis `0 < c` is discharged), and its
strengthened consequence `lw_localregularX` -/
example := lw_localregularXP 2 (1 / 4) (by norm_num) 1 3 10
example := lwEngineProv_imp_localregularX lw_localregularXP 2 (1 / 4) (by norm_num) 1 3 10

/-- **`WExp.prod`** at the data of `lwEngine_inst_step1_identity` (`d = 3`, `L = 3`, `W = 1`, `m = i`; every hypothesis discharged,
the expansion `WExp` from `lw_localregularXP`), `p = 2`, weights `w_k(x) = 1` at `x = 0` and `1/2` elsewhere -/
example : ∃ outs : List (ProvOut (fxyPowGraph 2).pack), WExp (mE 0) (fxyPowGraph 2).pack outs ∧
    ∫ ω, pvalW (fxyPowGraph 2).pack (lwSampleData lwWxInstSz 0 (zt 0 (1 / 2)) (1 / 2) lwWxInstM (lwS lwWxInstSz 0 (1 / 2))
        lwWxInstSp ω) (fun ℓ => ∏ k, (fun _ x => if x = 0 then (1 : ℝ) else 1 / 2) k (ℓ (Sum.inr (localReg_fxyBeta k))))
        lwSymmInstL ∂(Sizes.seqP lwWxInstSz) =
      (outs.map fun o => ∫ ω, pvalW o.Q (lwSampleData lwWxInstSz 0 (zt 0 (1 / 2)) (1 / 2) lwWxInstM
        (lwS lwWxInstSz 0 (1 / 2)) lwWxInstSp ω) (fun ℓ => ∏ k, (fun _ x => if x = 0 then (1 : ℝ) else 1 / 2) k
          (ℓ (o.π (Sum.inr (localReg_fxyBeta k))))) lwSymmInstL ∂(Sizes.seqP lwWxInstSz)).sum := by
  obtain ⟨outs, errs, -, H⟩ := lw_localregularXP 2 (1 / 4) (by norm_num) 1 3 10
  have h : WExp (mE 0) (fxyPowGraph 2).pack ((outs ++ errs).map (·.ev (mE 0))) := (H (mE 0) (lwWx_mE_ne 0 lwWx_inst_hE)).2.2
  exact ⟨_, h, WExp.prod h lwWxInstSp lwWxInstM (gaussIBP lwWxInstSz) lwWx_inst_im (by norm_num)
    (lwWx_mE_ne 0 lwWx_inst_hE) (lwWx_flow 0 (1 / 2) lwWx_inst_hE) lwWx_inst_hSp lwSymm_inst_hSpT lwWx_inst_hM
    lwSymm_inst_hM0 (fun _ x => if x = 0 then 1 else 1 / 2) lwSymmInstL⟩

/-- **the weighted bridge** at `p = 2`, `D = univ`: the merged value `|f_{xy}|²` of `fxyPowGraph 2`, at `lwWxInstSz`, `n = 0`,
`E = 0`, `t = 1/2`, the sample `ω = 0` and `x = 0`, `y = e₀` -/
example : (fxyPowGraph 2).pack.val (lwMoment_D lwWxInstSz 0 0 (1 / 2) 0) lwSymmInstL =
    ((‖LWf lwWxInstSz 0 0 (1 / 2) 0 0 (Pi.single 0 1)‖ ^ 2 : ℝ) : ℂ) := by
  have h := lwProv_bridge lwWxInstSz (p := 2) (by decide) 0 0 (1 / 2) 0 Finset.univ 0 (Pi.single 0 1)
  rw [← pvalW_one]
  have e1 : (fun ℓ : (fxyPowGraph 2).pack.E' ⊕ (fxyPowGraph 2).pack.I' → Idx 3 (lwWxInstSz.L 0) (lwWxInstSz.W 0) => (1 : ℝ)) =
      fun ℓ => ∏ k : Fin 2, if STblk lwWxInstSz 0 (ℓ (Sum.inr (localReg_fxyBeta k))) ∈ (Finset.univ : Finset (Zd 3 (lwWxInstSz.L 0)))
        then 1 else 0 := by
    funext ℓ; simp
  have e2 : LWfD lwWxInstSz 0 0 (1 / 2) 0 Finset.univ 0 (Pi.single 0 1) = LWf lwWxInstSz 0 0 (1 / 2) 0 0 (Pi.single 0 1) := by
    simp [LWfD, LWf]
  rw [e1, ← e2]
  exact h

/-- **the weighted bridge** at `p = 2` with the proper nonempty domain `D = {0}` (one block of the `27`), every sample `ω` -/
example (ω : lwWxInstSz.SeqΩ) : pvalW (fxyPowGraph 2).pack (lwMoment_D lwWxInstSz 0 0 (1 / 2) ω)
    (fun ℓ => ∏ k : Fin 2, if STblk lwWxInstSz 0 (ℓ (Sum.inr (localReg_fxyBeta k))) ∈ ({0} : Finset (Zd 3 (lwWxInstSz.L 0)))
      then 1 else 0) ![0, Pi.single 0 1] =
    ((‖LWfD lwWxInstSz 0 0 (1 / 2) ω {0} 0 (Pi.single 0 1)‖ ^ 2 : ℝ) : ℂ) :=
  lwProv_bridge lwWxInstSz (p := 2) (by decide) 0 0 (1 / 2) ω {0} 0 (Pi.single 0 1)

/-- `LWfD_union` for the disjoint nonempty pair `{0}`, `{1}` -/
example (ω : lwWxInstSz.SeqΩ) : LWfD lwWxInstSz 0 0 (1 / 2) ω ({0} ∪ {1}) 0 (Pi.single 0 1) =
    LWfD lwWxInstSz 0 0 (1 / 2) ω {0} 0 (Pi.single 0 1) + LWfD lwWxInstSz 0 0 (1 / 2) ω {1} 0 (Pi.single 0 1) :=
  LWfD_union lwWxInstSz 0 0 (1 / 2) ω (Finset.disjoint_singleton.2 (by decide)) 0 (Pi.single 0 1)

/-- the position-indexed step lemma (`lwProv_stepPos`) at the merged instance of `LocStepX.weight` on `p2Graph = fxyPowGraph 2`
(`lwEngine_inst_stepX`); the normality of the input is the proved `fxyPowGraph_normal` -/
example := lwProv_stepPos p2Graph.pack _ LWEngineInst.lwEngine_inst_stepX (fxyPowGraph_normal 2)

end LWProvInst


/-! ## 9. The pinned step lemma: the position-indexed provenance step (Amend 2) -/

section Pin

/-- **the position-indexed provenance step (Amend 2)**: the maps are carried by the
outputs (`ProvOutX`), one per position of the list, so equal outputs at two positions may carry different maps -/
def lwProv_LocStepXProvPos : Prop :=
  ∀ (P : PGraph (Fin 2)) (LX : List ((ℕ × ℕ) × PGraph (Fin 2))), LocStepX P LX → P.g.Normal →
    ∃ ps : List (ProvOutX P), ps.map (fun o => (o.tag, o.Q)) = LX ∧
      (∀ o ∈ ps, o.ExtOK ∧ (⟨o.Q, o.π⟩ : ProvOut P).Molecular) ∧ ∀ (m : ℂ) (t0 : ℕ × ℕ),
        WExp m (lwEvX m (t0, P)) (ps.map fun o => mkProv m t0 P (o.tag, o.Q) o.π)

theorem lwProv_locStepXProvPos_holds : lwProv_LocStepXProvPos := fun P LX h hN => lwProv_stepPos P LX h hN

/-- its instance: the merged `LocStepX.weight` step at `p2Graph = fxyPowGraph 2` (`lwEngine_inst_stepX`), normal by `fxyPowGraph_normal` -/
example := lwProv_locStepXProvPos_holds p2Graph.pack _ LWEngineInst.lwEngine_inst_stepX (fxyPowGraph_normal 2)

/-- a normal graph with a circled solid loop at the internal vertex `0` and an internal vertex `1` that no edge touches -/
def lwProv_wildGraph : LGraph (Fin 2) (Fin 2) where
  solid := [⟨true, true, .inr 0, .inr 0⟩]
  waved := []
  dotted := []
  coeff := 1

/-- **remark (R-b analysis): the hypotheses `LocStepX P LX` and `P.g.Normal` of the position-indexed provenance step (Amend 2) do
not force a waved edge at an internal vertex**: the `weight` step at the loop of `lwProv_wildGraph` is a `LocStepX` of a normal graph without waved edges (so
the maps of two outputs cannot be compared through the waved edges of the input) -/
example : lwProv_wildGraph.Normal ∧ lwProv_wildGraph.waved = [] ∧ ∃ LX, LocStepX lwProv_wildGraph.pack LX :=
  ⟨by decide, rfl, _, LocStepX.weight lwProv_wildGraph.pack
    ((⟨true, true, Sum.inr (0 : Fin 2), Sum.inr (0 : Fin 2)⟩ : SEdge (Fin 2 ⊕ Fin 2)), []) List.mem_cons_self
    (Sum.inr (0 : Fin 2)) false false rfl⟩

end Pin

end RBM.Graph
end
