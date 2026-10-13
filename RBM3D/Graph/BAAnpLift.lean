/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Graph.AnpKey6
import RBM3D.Graph.BAAtom2
import RBM3D.Graph.BAAuxGraph2B
import RBM3D.Graph.BAExp14a
import RBM3D.Graph.BAMomentGen
import RBM3D.Graph.BAMomentExpGen
import RBM3D.Graph.BAMomentExpGenB

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
# BA-L L3d1 (T2488): G4 on the BA carrier, `lem:Anp` at the block Anderson law

Paper: arXiv:2507.20274 (`B:line` is `paper/tex/B_graphical_lemmas.tex:line`, `7_8:line` is `paper/tex/7_8_light_weight.tex:line`):
G4 `B:491-497` (`:494` "summation over non-centre vertices", `:496` Cauchy-Schwarz with `(eq:Gbyxi2_BA)` `:428-429`), the aux graph
`B:420-465`, `(G_by_auxG_BA)` `B:486-490`; `lem:Anp` `7_8:933-939` (proof `:953-1077`), `lem:Anp_key` `7_8:960-985`, its corollary
`7_8:1025`, `lem:Anp_key_gh` `7_8:1041-1077` ("`≺` throughout").  Twin of `Graph/AnpKey.lean` §5-§6 (`:658-836`) and of
`baAnpAux_holds` (`Graph/BAAtom2.lean:694-708`) in a new file (namespaces `RBM.Graph` and `RBM.BA`, private stem `BAAnpLift_`);
additive, no merged file is edited.

## Contents

1. Target 1: `BAAnpKeyGhG` (the statement of `LWAnpKeyGh`, `Graph/LWPins.lean:389`, at the BA law `seqP (sz.withLam 0)`, carrier `baFMz`,
   horizon `BAflowT0`) and `baAnpKeyGhG_holds`: the `≺`-lift of the deterministic `anpDetGh_holds` (`AnpKey6.lean:862`, model-free).
   The lift reads the data only through `η > 0` (`BAExp14a_eta_pos`) and `size → ∞` (`BAFlow`).
2. Target 2: `BAAnpG` (the statement of `LWAnp`, `LWPins.lean:409`) and `baAnpG_holds` (`lwAnpKey_of_gh`, `lwAnp_of_key` in one step).
3. Target 3: `baAnpAuxG_holds : ∀ d, BAAnpAuxG d` (the merged pin, `Graph/BAAuxGraph2B.lean:865`), by the nested form `baAuxNested_holds`
   (`BAAtom2.lean:647`) and target 2, as `baAnpAux_holds` (`BAAtom2.lean:694`).
4. Target 4: the closures `baLWMoment_closed`, `baLWMomentExp_closed` (namespace `RBM.BA`).
5. Target 5: compiled nonempty instances at the `d = 3` data of `BA/LWPinsBA.lean` §3.

**G4 (the argument).**  At the molecule centres the BA aux graph is the band aux graph of `Γ.shadow` (`BAGraph.auxVal`, `auxOrd`,
`BAAtom.lean:71, 75`), so its nested form is the band's (`baAuxNested_holds`).  The "summation over non-centre vertices" of `B:494` is not a G4
step: the atoms of `𝓜_i` lie in the `R`-ball of the root, every solid edge at an atom is `≤ ξ([α_i], ·)` there (G3's premise `hξ`,
`BAAtom2.lean:403-406`), and `baGbyZeta_hxi` supplies `ξ = c · baZetaVar`.  The Cauchy-Schwarz of `B:496` is the Ward sum
`Σ_β ξ² ≺ (W^d η_t)⁻¹` of `LWXigL` (`BAZetaClaim`), which is the hypothesis `Σ_β ξ² ≤ θ` of the model-free `anpDetGh_holds`;
`(W^d)^{n_M} (W^d η_t)^{-n_M} = η_t^{-n_M}` is the paper's `η_t⁻¹` per molecule.  `lem:Anp_key_gh` then holds at the BA law, carrier and horizon
with `η_t = (1 - t) Im m₀ > 0` (`BAExp14a_eta_pos`); only the law, `η` and the flow predicate differ from the band.

**Premise scan** (`Test/Axioms.lean`): `LWXigL`, `LWPsiAll`, `BAAnpAuxG` occur only inside statement defs, as the conclusion of a theorem or in
`private` helpers; every public theorem here is `∀ d : ℕ, P d`.
-/

open MeasureTheory Filter

noncomputable section

namespace RBM.Graph

open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes RBM.BA

open private anpKey_rescale anpKey_stochDomAt_congr from RBM3D.Graph.AnpKey

/-! ## 1. Target 1: the carrier lift of `lem:Anp_key_gh` -/

/-- **`lem:Anp_key_gh` at the BA carrier** (`7_8:1041-1077`; `LWAnpKeyGh`, `Graph/LWPins.lean:389`, with `STFlow → BAFlow`, `lemT → BAflowT0`,
`Prec sz → PrecL sz (seqP (sz.withLam 0))`, `LWXi sz (STflowE z) → LWXigL (baFMz sz z) (seqP (sz.withLam 0))`, `etaT (STflowE z n) → (baFMz sz z).eta n`):
a nested graph with the ghost condition and edge variables `ξ` satisfying `(eq:Gbyxi3)` has
`𝒢_{ab} ≺ (W^d η_t)^{-q} Ψ_t^{ord(𝒢) - n_ngh} Π_i [Ψ_t(c|a_i - b_i|)]^{1(𝔓_i has no ghost edge)}`. -/
def BAAnpKeyGhG (d : ℕ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ (p q : ℕ), q ≤ p → ∀ Γ : NGraph p q, Γ.GhostOK → Γ.IsNested →
      ∀ (ε₀ C₁ C₂ C₃ : ℝ) (Cc : ℝ → ℝ), ∃ c : ℝ, 0 < c ∧
        ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z →
          ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ BAflowT0 sz z n) →
            ∀ Φ : ℕ → ℝ → ℝ, LWPsiAll sz ε₀ C₁ C₂ C₃ Cc Φ →
              ∀ ξ : ∀ n, Zd d (sz.L n) → Zd d (sz.L n) → sz.SeqΩ → ℝ,
                LWXigL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) t Φ ξ →
                PrecL sz (Sizes.seqP (sz.withLam 0)) (U := fun n => (Fin p → Zd d (sz.L n)) × (Fin p → Zd d (sz.L n)))
                  (fun n ab ω => Γ.val (fun α β => ξ n α β ω) ab.1 ab.2)
                  (fun n ab _ => ((((sz.W n : ℕ) : ℝ) ^ d) * (baFMz sz z).eta n (t n))⁻¹ ^ q *
                    Φ n 0 ^ (Γ.ordN - Γ.nngh) *
                    ∏ i, (if Γ.noGhostPath i = true then
                      Φ n (c * ((zdistInf d (sz.L n) (ab.1 i - ab.2 i) : ℕ) : ℝ)) else 1))

/-- **The `≺`-lift over any law and carrier** (`7_8:1041-1077` read with `≺`; the twin of `lwAnpKeyGh_of_det`, `AnpKey.lean:689-770`): from the
deterministic bound `AnpDetGhAt d Γ` and `η > 0` at every `n`, `size → ∞`.  The good event is
`Ξ_n = {ξ ≤ N^{τ'} Φ_n(|α-β|) ∀ α β} ∩ {Σ_β ξ² ≤ N^{τ'} θ_n ∀ α}` (the two `≺` premises of `LWXigL`, `BAMomentGen_whp_of_prec`,
`HighProbAt.inter`), `ψ = N^{τ'} Φ_n`, `θ = N^{τ'} θ_n`, `θ_n = (W^d η_t)⁻¹`, `τ' = τ / (2 (q + |ord - n_ngh| + p + 1))`; the factor
`C N^{τ'(q + k + n_ngh)}` is at most `N^τ` for large `n`. -/
private theorem BAAnpLift_core {d p q : ℕ} {Γ : NGraph p q} (hdet : AnpDetGhAt d Γ) :
    ∃ c : ℝ, 0 < c ∧ ∀ (sz : Sizes d) (μ : Measure sz.SeqΩ) (C : FlowFM sz),
      Tendsto (fun n => ((sz.size n : ℕ) : ℝ)) atTop atTop → ∀ t : ℕ → ℝ, (∀ n, 0 < C.eta n (t n)) →
      ∀ (ε₀ C₁ C₂ C₃ : ℝ) (Cc : ℝ → ℝ) (Φ : ℕ → ℝ → ℝ), LWPsiAll sz ε₀ C₁ C₂ C₃ Cc Φ →
        ∀ ξ : ∀ n, Zd d (sz.L n) → Zd d (sz.L n) → sz.SeqΩ → ℝ, LWXigL C μ t Φ ξ →
          PrecL sz μ (U := fun n => (Fin p → Zd d (sz.L n)) × (Fin p → Zd d (sz.L n)))
            (fun n ab ω => Γ.val (fun α β => ξ n α β ω) ab.1 ab.2)
            (fun n ab _ => ((((sz.W n : ℕ) : ℝ) ^ d) * C.eta n (t n))⁻¹ ^ q *
              Φ n 0 ^ (Γ.ordN - Γ.nngh) *
              ∏ i, (if Γ.noGhostPath i = true then
                Φ n (c * ((zdistInf d (sz.L n) (ab.1 i - ab.2 i) : ℕ) : ℝ)) else 1)) := by
  obtain ⟨C, c, hC, hc, -, H⟩ := hdet
  refine ⟨c, hc, ?_⟩
  intro sz μ Cr hsz' t hη ε₀ C₁ C₂ C₃ Cc Φ hΦ ξ hξ
  obtain ⟨hξnn, hξ1, hξ2⟩ := hξ
  have hsz : Tendsto sz.size atTop atTop := Sizes.tendsto_size sz hsz'
  have hN1 : ∀ n, (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := fun n => by exact_mod_cast sz.one_le_size n
  have hθ : ∀ n, 0 < ((((sz.W n : ℕ) : ℝ) ^ d) * Cr.eta n (t n))⁻¹ := fun n =>
    inv_pos.2 (mul_pos (pow_pos (by exact_mod_cast sz.W_pos n) d) (hη n))
  intro τ hτ D hD
  -- the exponents
  set k : ℤ := Γ.ordN - (Γ.nngh : ℤ) with hk
  set M : ℕ := q + k.natAbs + p with hM
  set τ' : ℝ := τ / (2 * ((M : ℝ) + 1)) with hτ'
  have hτ'pos : 0 < τ' := by positivity
  have hτ'M : τ' * (M : ℝ) ≤ τ / 2 := by
    rw [hτ']
    have hM0 : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg _
    rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  -- the good event
  have hΞ := HighProbAt.inter hsz (BAMomentGen_whp_of_prec sz hξ1 hτ'pos) (BAMomentGen_whp_of_prec sz hξ2 hτ'pos)
  have hev1 : ∀ᶠ n in atTop, ∀ r : ℝ, 0 ≤ r → 0 < Φ n r :=
    hΦ.2.1.1.mono fun n hn r hr => (hn r hr).1
  have hev2 : ∀ᶠ n in atTop, C ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) :=
    ((tendsto_rpow_atTop (half_pos hτ)).comp hsz').eventually_ge_atTop C
  filter_upwards [hΞ D hD, hev1, hev2] with n hn hΦn hCn
  refine le_trans (MeasureTheory.measure_mono ?_) hn
  rintro ω ⟨u, hu⟩ ⟨h1, h2⟩
  set N : ℝ := ((sz.size n : ℕ) : ℝ) with hNdef
  set x : ℝ := N ^ τ' with hx
  set θn : ℝ := ((((sz.W n : ℕ) : ℝ) ^ d) * Cr.eta n (t n))⁻¹ with hθn
  have hx1 : 1 ≤ x := Real.one_le_rpow (hN1 n) hτ'pos.le
  have hx0 : 0 < x := lt_of_lt_of_le one_pos hx1
  have hN0 : 0 ≤ N := (zero_le_one.trans (hN1 n))
  have hψ : AntitoneOn (fun r => x * Φ n r) (Set.Ici 0) := fun a ha b hb hab =>
    mul_le_mul_of_nonneg_left (hΦ.2.2.1 n ha hb hab) hx0.le
  have hdet := H (sz.L n) (fun r => x * Φ n r) (x * θn) hψ (fun r hr => mul_pos hx0 (hΦn r hr))
    (mul_pos hx0 (hθ n)) (fun α β => ξ n α β ω) (fun α β => hξnn n α β ω) (fun α β => h1 (α, β)) h2
    u.1 u.2
  have hrs := anpKey_rescale Γ x C θn (Φ n 0) hx0
    (fun i => Φ n (c * ((zdistInf d (sz.L n) (u.1 i - u.2 i) : ℕ) : ℝ)))
  have hζ0 : 0 ≤ θn ^ q * Φ n 0 ^ (Γ.ordN - (Γ.nngh : ℤ)) *
      ∏ i, (if Γ.noGhostPath i = true then
        Φ n (c * ((zdistInf d (sz.L n) (u.1 i - u.2 i) : ℕ) : ℝ)) else 1) := by
    refine mul_nonneg (mul_nonneg (pow_nonneg (hθ n).le _) (zpow_nonneg (hΦn 0 le_rfl).le _))
      (Finset.prod_nonneg fun i _ => ?_)
    split_ifs
    · exact (hΦn _ (by positivity)).le
    · exact zero_le_one
  have hexp : x ^ ((q : ℤ) + (Γ.ordN - (Γ.nngh : ℤ)) + (Γ.nngh : ℤ)) ≤ N ^ (τ / 2) := by
    have hm : (q : ℤ) + (Γ.ordN - (Γ.nngh : ℤ)) + (Γ.nngh : ℤ) ≤ (M : ℤ) := by
      have h1 : (Γ.ordN - (Γ.nngh : ℤ)) ≤ ((Γ.ordN - (Γ.nngh : ℤ)).natAbs : ℤ) := Int.le_natAbs
      have h2 : Γ.nngh ≤ p := by
        unfold NGraph.nngh
        exact (Finset.card_filter_le _ _).trans (by simp)
      have h2' : (Γ.nngh : ℤ) ≤ p := by exact_mod_cast h2
      have h3 : (M : ℤ) = q + ((Γ.ordN - (Γ.nngh : ℤ)).natAbs : ℤ) + p := by simp only [hM]; push_cast; ring
      rw [h3]
      linarith
    calc x ^ ((q : ℤ) + (Γ.ordN - (Γ.nngh : ℤ)) + (Γ.nngh : ℤ)) ≤ x ^ (M : ℤ) :=
          zpow_le_zpow_right₀ hx1 hm
      _ = N ^ (τ' * (M : ℝ)) := by
          rw [zpow_natCast, hx, ← Real.rpow_natCast, ← Real.rpow_mul hN0]
      _ ≤ N ^ (τ / 2) := Real.rpow_le_rpow_of_exponent_le (hN1 n) hτ'M
  have hfin : Γ.val (fun α β => ξ n α β ω) u.1 u.2 ≤ N ^ τ *
      (θn ^ q * Φ n 0 ^ (Γ.ordN - (Γ.nngh : ℤ)) *
        ∏ i, (if Γ.noGhostPath i = true then
          Φ n (c * ((zdistInf d (sz.L n) (u.1 i - u.2 i) : ℕ) : ℝ)) else 1)) := by
    refine (hdet.trans (le_of_eq hrs)).trans ?_
    refine mul_le_mul_of_nonneg_right ?_ hζ0
    calc C * x ^ ((q : ℤ) + (Γ.ordN - (Γ.nngh : ℤ)) + (Γ.nngh : ℤ)) ≤ N ^ (τ / 2) * N ^ (τ / 2) :=
          mul_le_mul hCn hexp (zpow_nonneg hx0.le _) (Real.rpow_nonneg hN0 _)
      _ = N ^ τ := by rw [← Real.rpow_add (lt_of_lt_of_le one_pos (hN1 n))]; congr 1; ring
  exact absurd hu (not_lt.2 hfin)

/-- **Target 1** (`lem:Anp_key_gh` at the BA carrier, every `d`; twin of `lwAnpKeyGh_of_det`, `AnpKey.lean:689`, at `anpDetGh_holds`): `η > 0` from
`BAExp14a_eta_pos` in place of `etaT_pos`, `size → ∞` from `BAFlow`, the good event from `BAMomentGen_whp_of_prec` and `HighProbAt.inter`. -/
theorem baAnpKeyGhG_holds : ∀ d : ℕ, BAAnpKeyGhG d := by
  intro d hd κ ε 𝔡 hκ hε h𝔡 p q hqp Γ hG hN ε₀ C₁ C₂ C₃ Cc
  obtain ⟨c, hc, H⟩ := BAAnpLift_core (anpDetGh_holds d p q Γ hG hN)
  refine ⟨c, hc, fun 𝔠 sz z hflow t ht0 htT Φ hΦ ξ hξ => ?_⟩
  exact H sz _ (baFMz sz z) hflow.1.2.2.1 t (fun n => BAExp14a_eta_pos hκ hflow n (ht0 n) (htT n))
    ε₀ C₁ C₂ C₃ Cc Φ hΦ ξ hξ

/-! ## 2. Target 2: `lem:Anp` at the BA carrier -/

/-- **`lem:Anp` at the BA carrier** (`7_8:933-939`, `(eq:bddGamma_aux)`; `LWAnp`, `Graph/LWPins.lean:409`, under the substitution of `BAAnpKeyGhG`): a nested
graph without ghost edge, all `a_i = [a]`, `b_i = [b]`: `Γ_{[a][b]} ≺ (W^d η_t)^{-q} [Ψ_t(c|[a]-[b]|)]^p Ψ_t^{ord(Γ) - p}`. -/
def BAAnpG (d : ℕ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ (p q : ℕ), q ≤ p → ∀ Γ : NGraph p q, Γ.NoGhost → Γ.IsNested →
      ∀ (ε₀ C₁ C₂ C₃ : ℝ) (Cc : ℝ → ℝ), ∃ c : ℝ, 0 < c ∧
        ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z →
          ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ BAflowT0 sz z n) →
            ∀ Φ : ℕ → ℝ → ℝ, LWPsiAll sz ε₀ C₁ C₂ C₃ Cc Φ →
              ∀ ξ : ∀ n, Zd d (sz.L n) → Zd d (sz.L n) → sz.SeqΩ → ℝ,
                LWXigL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) t Φ ξ →
                PrecL sz (Sizes.seqP (sz.withLam 0)) (U := fun n => Zd d (sz.L n) × Zd d (sz.L n))
                  (fun n ab ω => Γ.val (fun α β => ξ n α β ω) (fun _ => ab.1) (fun _ => ab.2))
                  (fun n ab _ => ((((sz.W n : ℕ) : ℝ) ^ d) * (baFMz sz z).eta n (t n))⁻¹ ^ q *
                    Φ n (c * ((zdistInf d (sz.L n) (ab.1 - ab.2) : ℕ) : ℝ)) ^ p *
                    Φ n 0 ^ (Γ.ordN - p))

/-- **Target 2** (twins of `lwAnpKey_of_gh`, `lwAnp_of_key`, `AnpKey.lean:814, 825`, in one step): no ghost edge gives `GhostOK`, `noGhostPath i = true` for every `i`,
`n_ngh = p` (`anpKey_ghostOK_of_noGhost`, `anpKey_noGhostPath_of_noGhost`, `anpKey_nngh_of_noGhost`, `AnpKey.lean:782-799`), and the special case
`a_i ≡ [a]`, `b_i ≡ [b]` is a restriction of the parameter family (`StochDomAt.precomp_param`). -/
theorem baAnpG_holds : ∀ d : ℕ, BAAnpG d := by
  intro d hd κ ε 𝔡 hκ hε h𝔡 p q hqp Γ hng hnest ε₀ C₁ C₂ C₃ Cc
  obtain ⟨c, hc, H⟩ := baAnpKeyGhG_holds d hd κ ε 𝔡 hκ hε h𝔡 p q hqp Γ (anpKey_ghostOK_of_noGhost hng) hnest
    ε₀ C₁ C₂ C₃ Cc
  refine ⟨c, hc, fun 𝔠 sz z hflow t ht0 htT Φ hΦ ξ hξ => ?_⟩
  have h2 := StochDomAt.precomp_param (H 𝔠 sz z hflow t ht0 htT Φ hΦ ξ hξ)
    (V := fun n => Zd d (sz.L n) × Zd d (sz.L n))
    (fun n ab => ((fun _ => ab.1 : Fin p → Zd d (sz.L n)), (fun _ => ab.2 : Fin p → Zd d (sz.L n))))
  refine anpKey_stochDomAt_congr h2 fun n ab ω => ?_
  simp only [anpKey_noGhostPath_of_noGhost hng, anpKey_nngh_of_noGhost hng, ite_true, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]
  exact mul_right_comm _ _ _

/-! ## 3. Target 3: G4, the binding conclusion -/

/-- **Target 3, G4 on the BA carrier** (`B:491-497`; the merged pin `BAAnpAuxG`, `Graph/BAAuxGraph2B.lean:865`, unchanged; twin of `baAnpAux_holds`, `BAAtom2.lean:694-708`):
`baAuxNested_holds` gives the nested graph `Γa` of the aux graph (no ghost edge, `ordN = auxOrd`, value `auxVal` for symmetric `ξ`, `q = n_M ≤ p`), target 2 is
applied at `Γa`, and the value and the order are transported (symmetry from the first conjunct of `LWXigL`). -/
theorem baAnpAuxG_holds : ∀ d : ℕ, BAAnpAuxG d := by
  intro d hd κ ε 𝔡 hκ hε h𝔡 p P hp hq hLR hxy ε₀ C₁ C₂ C₃ Cc
  obtain ⟨Γa, h1, h2, h3, h4⟩ := baAuxNested_holds p P hp hLR hxy
  obtain ⟨c, hc, H⟩ := baAnpG_holds d hd κ ε 𝔡 hκ hε h𝔡 p P.g.nM hq Γa h1 h2 ε₀ C₁ C₂ C₃ Cc
  refine ⟨c, hc, fun 𝔠 sz z hz t ht0 ht1 Φ hΦ ξ hξ => ?_⟩
  have hne : P.ext 1 ≠ P.ext 0 := fun h => hxy (by rw [h])
  have hfun : (fun (n : ℕ) (ab : Zd d (sz.L n) × Zd d (sz.L n)) (ω : sz.SeqΩ) =>
      P.g.auxVal (fun α β => ξ n α β ω) (fun e => if e = P.ext 0 then ab.1 else ab.2)) =
      (fun n ab ω => Γa.val (fun α β => ξ n α β ω) (fun _ => ab.1) (fun _ => ab.2)) := by
    funext n ab ω
    have := h4 (fun α β => ξ n α β ω) (fun u v => (hξ.1 n u v ω).2) (fun e => if e = P.ext 0 then ab.1 else ab.2)
    simp only [ite_true, hne, ite_false] at this
    exact this.symm
  rw [hfun, ← h3]
  exact H 𝔠 sz z hz t ht0 ht1 Φ hΦ ξ hξ

end RBM.Graph

/-! ## 4. Target 4: the closures -/

namespace RBM.BA

open RBM.Graph

/-- **Target 4 (a), `lem:LW_moment` at BA with no antecedent left** (supervisor 2246 L40-F2): `baLWMomentOfAnp_closed` (`Graph/BAMomentExpGen.lean:189`, the path binder
concluded by T2469) applied to G4 (`baAnpAuxG_holds`).  After it, no public statement of stage L carries `BAAnpAuxG`. -/
theorem baLWMoment_closed : ∀ d : ℕ, BALWMoment d := fun d => baLWMomentOfAnp_closed d (baAnpAuxG_holds d)

/-- **Target 4 (b), `lem:LW_moment_exp` at BA with no antecedent** (`7_8:78-83`): `baLWMomentExp_of_anp` (`Graph/BAMomentExpGenB.lean:1207`) applied to G4. -/
theorem baLWMomentExp_closed : ∀ d : ℕ, BALWMomentExp d := fun d => baLWMomentExp_of_anp d (baAnpAuxG_holds d)

end RBM.BA

/-! ## 5. Compiled nonempty instances of targets 1-4

Data (`BA/LWPinsBA.lean` §3, `Graph/BAAuxGraph2B.lean` §7): `d = 3`, `sz0` (`n = 0`: `L = 4`, `W = 32`, `N = 2097152`), the flow `flow_sz0` (`κ = 1/2`, `ε = 𝔡 = 1/10`,
`𝔠 = 1/6`), `z = zSeq`, `t ≡ 1/2 ≤ BAflowT0` (`half_lt_t0`), the class `Φ0 ≡ W^{-1/2}` (`LWPsiAll` with `ε₀ = 1/10`, `C₁ = C₂ = 2`, `C₃ = 1`, `Cc ≡ 1`),
`ε₁ = 1/20`, `D₁ = 12`, `ρ = 2R + (log W)^{3/2}` (the private data of `BAAuxGraph2B` §7, by `open private`).  What stays a hypothesis is another gate's input:
`LWLoop2gL`, the entry law `‖G_t - M‖_max ≺ W^{-1/20}`, `STInitialGT2gL`, `LWLoopExpgL`; no hypothesis for targets 1-4. -/

namespace RBM.Graph

open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes RBM.BA

section Inst

open RBM.Gauss.SizesInst RBM.BA.FlowPinsInst

local notation "μ0" => Sizes.seqP (sz0.withLam 0)

open private BAAuxGraph2B_Φ0 BAAuxGraph2B_ρ0 BAAuxGraph2B_psiAll BAAuxGraph2B_ρ0_nonneg BAAuxGraph2B_ρ0_rad
  from RBM3D.Graph.BAAuxGraph2B

local notation "Φb" => BAAuxGraph2B_Φ0
local notation "ζ0" => baZetaVar sz0 zSeq (fun _ => 1 / 2) BAAuxGraph2B_ρ0 12

/-- `LWXigL` for `ζ = baZetaVar` at the instance data (`baZetaClaim_holds 3`; the same term as the instance of `BAAuxGraph2B:979`): the edge variables of
the instances below; `LWLoop2gL` and the entry law are other gates' pins. -/
private theorem BAAnpLift_zeta0 (hL : LWLoop2gL (baFMz sz0 zSeq) μ0 (fun _ => 1 / 2) Φb)
    (hent : PrecL sz0 μ0 (U := fun n => Idx 3 (sz0.L n) (sz0.W n) × Idx 3 (sz0.L n) (sz0.W n))
      (fun n p ω => ‖(baFMz sz0 zSeq).GM n (1 / 2) ω p.1 p.2‖) (fun n _ _ => ((sz0.W n : ℕ) : ℝ) ^ (-(1 / 20 : ℝ)))) :
    LWXigL (baFMz sz0 zSeq) μ0 (fun _ => 1 / 2) Φb ζ0 :=
  baZetaClaim_holds 3 le_rfl (1 / 2) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 6) sz0 zSeq flow_sz0
    (fun _ => 1 / 2) (fun _ => by norm_num) (fun n => (half_lt_t0 n).le) (1 / 10) 2 2 1 (fun _ => 1) Φb
    BAAuxGraph2B_psiAll hL (1 / 20) (by norm_num) hent BAAuxGraph2B_ρ0 BAAuxGraph2B_ρ0_nonneg BAAuxGraph2B_ρ0_rad 12
    (by norm_num)

/-- **Instance of target 3** (`baAnpAuxG_holds 3`) at `baPQ` (`p = 2`, `n_M = 1 ≤ p`, `ord Γ^aux = 2`, four molecular solid edges), `ξ = ζ` of `baZetaClaim_holds 3`:
the BA twin of `inst_Anp`; `BAAnpAuxG 3` is not a hypothesis (the instance of `BAAuxGraph2B:979` with `h6` discharged). -/
example (hL : LWLoop2gL (baFMz sz0 zSeq) μ0 (fun _ => 1 / 2) Φb)
    (hent : PrecL sz0 μ0 (U := fun n => Idx 3 (sz0.L n) (sz0.W n) × Idx 3 (sz0.L n) (sz0.W n))
      (fun n p ω => ‖(baFMz sz0 zSeq).GM n (1 / 2) ω p.1 p.2‖) (fun n _ _ => ((sz0.W n : ℕ) : ℝ) ^ (-(1 / 20 : ℝ)))) :
    ∃ c : ℝ, 0 < c ∧ PrecL sz0 μ0 (U := fun n => Zd 3 (sz0.L n) × Zd 3 (sz0.L n))
      (fun n ab ω => BAAtomInst2.baPQ.g.auxVal (fun α β => ζ0 n α β ω) (fun e => if e = BAAtomInst2.baPQ.ext 0 then ab.1 else ab.2))
      (fun n ab _ => ((((sz0.W n : ℕ) : ℝ) ^ 3) * (baFMz sz0 zSeq).eta n (1 / 2))⁻¹ ^ BAAtomInst2.baPQ.g.nM *
        Φb n (c * ((zdistInf 3 (sz0.L n) (ab.1 - ab.2) : ℕ) : ℝ)) ^ 2 * Φb n 0 ^ (BAAtomInst2.baPQ.g.auxOrd - 2)) := by
  obtain ⟨c, hc, H⟩ := baAnpAuxG_holds 3 le_rfl (1 / 2) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) 2
    BAAtomInst2.baPQ (by norm_num) (by decide) localReg2_inst_Q_locReg345 (by decide) (1 / 10) 2 2 1 (fun _ => 1)
  exact ⟨c, hc, H (1 / 6) sz0 zSeq flow_sz0 (fun _ => 1 / 2) (fun _ => by norm_num) (fun n => (half_lt_t0 n).le)
    Φb BAAuxGraph2B_psiAll _ (BAAnpLift_zeta0 hL hent)⟩

/-- **Instance of target 1** (`baAnpKeyGhG_holds 3`) at the one-edge graph `a_0 — b_0` (`anpKey_oneEdge`, `AnpKey.lean:843`: `p = 1`, `q = 0`, one solid edge, one path),
the data above, `ξ = ζ`. -/
example (hL : LWLoop2gL (baFMz sz0 zSeq) μ0 (fun _ => 1 / 2) Φb)
    (hent : PrecL sz0 μ0 (U := fun n => Idx 3 (sz0.L n) (sz0.W n) × Idx 3 (sz0.L n) (sz0.W n))
      (fun n p ω => ‖(baFMz sz0 zSeq).GM n (1 / 2) ω p.1 p.2‖) (fun n _ _ => ((sz0.W n : ℕ) : ℝ) ^ (-(1 / 20 : ℝ)))) :
    ∃ c : ℝ, 0 < c ∧ PrecL sz0 μ0 (U := fun n => (Fin 1 → Zd 3 (sz0.L n)) × (Fin 1 → Zd 3 (sz0.L n)))
      (fun n ab ω => anpKey_oneEdge.val (fun α β => ζ0 n α β ω) ab.1 ab.2)
      (fun n ab _ => ((((sz0.W n : ℕ) : ℝ) ^ 3) * (baFMz sz0 zSeq).eta n (1 / 2))⁻¹ ^ 0 *
        Φb n 0 ^ (anpKey_oneEdge.ordN - anpKey_oneEdge.nngh) *
        ∏ i, (if anpKey_oneEdge.noGhostPath i = true then
          Φb n (c * ((zdistInf 3 (sz0.L n) (ab.1 i - ab.2 i) : ℕ) : ℝ)) else 1)) := by
  obtain ⟨c, hc, H⟩ := baAnpKeyGhG_holds 3 le_rfl (1 / 2) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) 1 0
    (Nat.zero_le 1) anpKey_oneEdge anpKey_oneEdge_ghostOK anpKey_oneEdge_nested (1 / 10) 2 2 1 (fun _ => 1)
  exact ⟨c, hc, H (1 / 6) sz0 zSeq flow_sz0 (fun _ => 1 / 2) (fun _ => by norm_num) (fun n => (half_lt_t0 n).le)
    Φb BAAuxGraph2B_psiAll _ (BAAnpLift_zeta0 hL hent)⟩

/-- **Instance of target 2** (`baAnpG_holds 3`) at the same one-edge graph (no ghost edge) and data. -/
example (hL : LWLoop2gL (baFMz sz0 zSeq) μ0 (fun _ => 1 / 2) Φb)
    (hent : PrecL sz0 μ0 (U := fun n => Idx 3 (sz0.L n) (sz0.W n) × Idx 3 (sz0.L n) (sz0.W n))
      (fun n p ω => ‖(baFMz sz0 zSeq).GM n (1 / 2) ω p.1 p.2‖) (fun n _ _ => ((sz0.W n : ℕ) : ℝ) ^ (-(1 / 20 : ℝ)))) :
    ∃ c : ℝ, 0 < c ∧ PrecL sz0 μ0 (U := fun n => Zd 3 (sz0.L n) × Zd 3 (sz0.L n))
      (fun n ab ω => anpKey_oneEdge.val (fun α β => ζ0 n α β ω) (fun _ => ab.1) (fun _ => ab.2))
      (fun n ab _ => ((((sz0.W n : ℕ) : ℝ) ^ 3) * (baFMz sz0 zSeq).eta n (1 / 2))⁻¹ ^ 0 *
        Φb n (c * ((zdistInf 3 (sz0.L n) (ab.1 - ab.2) : ℕ) : ℝ)) ^ 1 * Φb n 0 ^ (anpKey_oneEdge.ordN - (1 : ℕ))) := by
  have hng : anpKey_oneEdge.NoGhost := by
    intro e he
    simp [anpKey_oneEdge] at he
    simp [he]
  obtain ⟨c, hc, H⟩ := baAnpG_holds 3 le_rfl (1 / 2) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) 1 0
    (Nat.zero_le 1) anpKey_oneEdge hng anpKey_oneEdge_nested (1 / 10) 2 2 1 (fun _ => 1)
  exact ⟨c, hc, H (1 / 6) sz0 zSeq flow_sz0 (fun _ => 1 / 2) (fun _ => by norm_num) (fun n => (half_lt_t0 n).le)
    Φb BAAuxGraph2B_psiAll _ (BAAnpLift_zeta0 hL hent)⟩

end Inst

end RBM.Graph

namespace RBM.BA

open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes RBM.Graph

section Inst

open RBM.Gauss.SizesInst RBM.BA.FlowPinsInst RBM.Gauss.LWInst

local notation "μ0" => Sizes.seqP (sz0.withLam 0)
local notation "ℓh" => ℓT (fun _ : ℕ => (1 / 2 : ℝ))

open private BAMomentExpGen_Φ0 BAMomentExpGen_Ψ0 BAMomentExpGen_Ψ0_window BAMomentExpGen_psiAll0
  from RBM3D.Graph.BAMomentExpGen

/-- **Instance of target 4 (a)** (`baLWMoment_closed 3`; the data of `BAMomentGenB:473`, `BAMomentExpGen:982`, without `BAAnpAuxG 3` and without the path binder): the
moment bound `𝔼 |f_{xy}|² ≺ (η⁻¹ Φ(0) Φ(c|a-b|))²` for some `c > 0`, `p = 2`.  Every deterministic hypothesis is discharged; `STInitialGT2gL` and `LWLoop2gL`
(inside `LWAssmgL`) stay hypotheses. -/
example (hI : STInitialGT2gL (baFMz sz0 zSeq) μ0 (fun _ => 1 / 2) (1 / 10) BAMomentExpGen_Ψ0)
    (hL : LWLoop2gL (baFMz sz0 zSeq) μ0 (fun _ => 1 / 2) BAMomentExpGen_Φ0) :
    ∃ c : ℝ, 0 < c ∧ PrecL sz0 μ0 (U := fun n => Idx 3 (sz0.L n) (sz0.W n) × Idx 3 (sz0.L n) (sz0.W n))
      (fun n q _ => ∫ ω, ‖LWfg (baFMz sz0 zSeq) n ((fun _ => (1 / 2 : ℝ)) n) ω q.1 q.2‖ ^ 2 ∂μ0)
      (fun n q _ => (((baFMz sz0 zSeq).eta n ((fun _ => (1 / 2 : ℝ)) n))⁻¹ * BAMomentExpGen_Φ0 n 0 *
        BAMomentExpGen_Φ0 n (c * ((zdistInf 3 (sz0.L n) (STblk sz0 n q.1 - STblk sz0 n q.2) : ℕ) : ℝ))) ^ 2) := by
  obtain ⟨c, hc, H⟩ := baLWMoment_closed 3 le_rfl (1 / 2) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num)
    2 (dvd_refl 2) (1 / 10) 2 2 1 (fun _ => 1)
  exact ⟨c, hc, H (1 / 6) sz0 zSeq flow_sz0 (fun _ => 1 / 2) (fun _ => by norm_num) (fun n => (half_lt_t0 n).le)
    BAMomentExpGen_Ψ0 BAMomentExpGen_Φ0 ⟨by norm_num, BAMomentExpGen_Ψ0_window, hI, BAMomentExpGen_psiAll0.2.1,
      BAMomentExpGen_psiAll0.2.2, hL⟩⟩

/-- **Instance of target 4 (b)** (`baLWMomentExp_closed 3`; the data of `BAMomentExpGenB:1317`, without `BAAnpAuxG 3`): `lem:LW_moment_exp` at `d = 3`, `p = 2`, `ε₀ = 1/20`,
`Ψ_n = W_n^{-1}`, `ℓ_n = ℓ_t` and every `D > 0`; `STInitialGT2gL` and `LWLoopExpgL` (inside `LWAssmExpgL`) stay hypotheses. -/
example (hI : STInitialGT2gL (baFMz sz0 zSeq) μ0 (fun _ => 1 / 2) (1 / 20) Ψ0)
    (hL : LWLoopExpgL (baFMz sz0 zSeq) μ0 (fun _ => 1 / 2) ℓh) (D : ℝ) (hD : 0 < D) :=
  baLWMomentExp_closed 3 le_rfl (1 / 2) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) 2 (dvd_refl 2) (1 / 6) sz0 zSeq flow_sz0
    (fun _ => 1 / 2) (fun _ => by norm_num) (fun n => (half_lt_t0 n).le) (1 / 20) Ψ0 ℓh
    ⟨by norm_num, window0, hI, fun n => zero_le_one.trans (ℓT_one_le _ n), ℓT_window _, hL⟩ D hD

end Inst

end RBM.BA

end
