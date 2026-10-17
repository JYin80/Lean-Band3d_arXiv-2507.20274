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
# `lem:Anp` at the block Anderson law: the auxiliary graph bound

Paper: Lemma B.7 (`lem_lweight`), the end of its proof: the auxiliary graph (B.24)
`eq:ordGaux_BAM`, (B.25) `G_by_auxG_BA`, "summation over non-centre vertices", and the
Cauchy-Schwarz step with (B.22) `eq:Gbyxi2_BA`; Lemma 7.22 (`lem:Anp`), Lemma 7.23
(`lem:Anp_key`) with its corollary from Lemma 7.24 (`lem:Anp_key_gh`, "`≺` throughout").  The
statements and proofs run parallel to `Graph/AnpKey.lean` (Sections 4 and 5), in namespaces
`RBM.Graph` and `RBM.BA` (private stem `BAAnpLift_`).

## Contents

1. `BAAnpKeyGhG` (the statement of `LWAnpKeyGh`, `Graph/LWPins.lean`, at the BA law
   `seqP (sz.withLam 0)`, carrier `baFMz`, horizon `BAflowT0`) and `baAnpKeyGhG_holds`: the `≺`-lift
   of the deterministic `anpDetGh_holds` (`Graph/AnpKey6.lean`, model-free).  The lift reads the data
   only through `η > 0` (`BAExp14a_eta_pos`) and `size → ∞` (`BAFlow`).
2. `BAAnpG` (the statement of `LWAnp`) and `baAnpG_holds` (`lwAnpKey_of_gh`, `lwAnp_of_key` in one
   step).
3. `baAnpAuxG_holds : ∀ d, BAAnpAuxG d` (`BAAnpAuxG` is stated in `Graph/BAAuxGraph2B.lean`), by the
   nested form `baAuxNested_holds` (`Graph/BAAtom2.lean`) and `baAnpG_holds`.
4. The closures `baLWMoment_closed`, `baLWMomentExp_closed` (namespace `RBM.BA`).

**The argument.**  At the molecule centres the BA auxiliary graph is the band auxiliary graph of
`Γ.shadow` (`BAGraph.auxVal`, `auxOrd`, `Graph/BAAtom.lean`), so its nested form is the band's
(`baAuxNested_holds`).  The "summation over non-centre vertices" of the paper is not a separate step:
the atoms of `𝓜_i` lie in the `R`-ball of the root, every solid edge at an atom is `≤ ξ([α_i], ·)`
there (the premise `hξ` of `baAtom_sedge_xi` in `Graph/BAAtom.lean`), and `baGbyZeta_holds`
(`Graph/BAAuxGraph2B.lean`) supplies `ξ = c · baZetaVar`.  The Cauchy-Schwarz step is the Ward sum `Σ_β ξ² ≺ (W^d η_t)⁻¹` of
`LWXigL` (`BAZetaClaim`), which is the hypothesis `Σ_β ξ² ≤ θ` of the model-free `anpDetGh_holds`;
`(W^d)^{n_M} (W^d η_t)^{-n_M} = η_t^{-n_M}` is the factor `η_t⁻¹` per molecule of the paper.
`lem:Anp_key_gh` then holds at the BA law, carrier and horizon with `η_t = (1 - t) Im m₀ > 0`
(`BAExp14a_eta_pos`); only the law, `η` and the flow predicate differ from the band.
-/

open MeasureTheory Filter

noncomputable section

namespace RBM.Graph

open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes RBM.BA

open private anpKey_rescale anpKey_stochDomAt_congr from RBM3D.Graph.AnpKey

/-! ## 1. The carrier lift of `lem:Anp_key_gh` -/

/-- **`lem:Anp_key_gh` at the BA carrier** (Lemma 7.24; `LWAnpKeyGh`, `Graph/LWPins.lean`, with `STFlow → BAFlow`, `lemT → BAflowT0`,
`Prec sz → PrecL sz (seqP (sz.withLam 0))`, `LWXi sz (STflowE z) → LWXigL (baFMz sz z) (seqP (sz.withLam 0))`, `etaT (STflowE z n) → (baFMz sz z).eta n`):
a nested graph with the ghost condition and edge variables `ξ` satisfying (7.38) `eq:Gbyxi3` has
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

/-- **The `≺`-lift over any law and carrier** (Lemma 7.24 read with `≺`; parallel to `lwAnpKeyGh_of_det` in `Graph/AnpKey.lean`): from the
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

/-- **`lem:Anp_key_gh` at the BA carrier, every `d`** (parallel to `lwAnpKeyGh_of_det` at `anpDetGh_holds`): `η > 0` from
`BAExp14a_eta_pos` in place of `etaT_pos`, `size → ∞` from `BAFlow`, the good event from `BAMomentGen_whp_of_prec` and `HighProbAt.inter`. -/
theorem baAnpKeyGhG_holds : ∀ d : ℕ, BAAnpKeyGhG d := by
  intro d hd κ ε 𝔡 hκ hε h𝔡 p q hqp Γ hG hN ε₀ C₁ C₂ C₃ Cc
  obtain ⟨c, hc, H⟩ := BAAnpLift_core (anpDetGh_holds d p q Γ hG hN)
  refine ⟨c, hc, fun 𝔠 sz z hflow t ht0 htT Φ hΦ ξ hξ => ?_⟩
  exact H sz _ (baFMz sz z) hflow.1.2.2.1 t (fun n => BAExp14a_eta_pos hκ hflow n (ht0 n) (htT n))
    ε₀ C₁ C₂ C₃ Cc Φ hΦ ξ hξ

/-! ## 2. `lem:Anp` at the BA carrier -/

/-- **`lem:Anp` at the BA carrier** (Lemma 7.22, (7.37) `eq:bddGamma_aux`; `LWAnp`, `Graph/LWPins.lean`, under the substitution of `BAAnpKeyGhG`): a nested
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

/-- **`lem:Anp` at the BA carrier from `BAAnpKeyGhG`** (parallel to `lwAnpKey_of_gh`, `lwAnp_of_key` in `Graph/AnpKey.lean`, in one step): no ghost edge gives `GhostOK`, `noGhostPath i = true` for every `i`,
`n_ngh = p` (`anpKey_ghostOK_of_noGhost`, `anpKey_noGhostPath_of_noGhost`, `anpKey_nngh_of_noGhost`), and the special case
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

/-! ## 3. The auxiliary graph bound at the BA carrier -/

/-- **The auxiliary graph bound at the BA carrier** (end of the proof of Lemma B.7; `BAAnpAuxG` is stated in `Graph/BAAuxGraph2B.lean`):
`baAuxNested_holds` gives the nested graph `Γa` of the aux graph (no ghost edge, `ordN = auxOrd`, value `auxVal` for symmetric `ξ`, `q = n_M ≤ p`), `baAnpG_holds` is
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

/-! ## 4. The closures -/

namespace RBM.BA

open RBM.Graph

/-- **`lem:LW_moment` at BA with no antecedent**: `baLWMomentOfAnp_closed` (`Graph/BAMomentExpGen.lean`, the path binder
concluded here) applied to the auxiliary graph bound `baAnpAuxG_holds`. -/
theorem baLWMoment_closed : ∀ d : ℕ, BALWMoment d := fun d => baLWMomentOfAnp_closed d (baAnpAuxG_holds d)

/-- **`lem:LW_moment_exp` at BA with no antecedent** (Lemma 7.2): `baLWMomentExp_of_anp` (`Graph/BAMomentExpGenB.lean`) applied to the auxiliary graph bound `baAnpAuxG_holds`. -/
theorem baLWMomentExp_closed : ∀ d : ℕ, BALWMomentExp d := fun d => baLWMomentExp_of_anp d (baAnpAuxG_holds d)

end RBM.BA

end
