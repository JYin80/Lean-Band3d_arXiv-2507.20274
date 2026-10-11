/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Chain.NewKLKGen
import RBM3D.BA.FlowPins
import RBM3D.BA.KSolve
import RBM3D.BA.EKPins
import RBM3D.BA.KTreeRep

/-!
# T2414 probe (BA-T T8b design gate, probe step of CONTROL H209; never merged, no root import)

The Lean form of the pins of `docs/reports/T2414-prove.md`, section (a): the block kernel `M^{(σσ')}` derived from the carrier,
the drift kernels over it, the operators and predicates that read them, the band bridges, the BA identities, `lem:newKLK`
over the new kernel (F7 restated) and the primed `K^{(2)}` decay (BAT-F2).  Namespace `RBM.BA.T2414Pins`.  The file has
definitions, `Prop` pins, `#check` lines and `example`s only (no theorem, no placeholder proof): the statement of a theorem `X` of (a) is
the `Prop` `X_pin` here (as `BAProp5s`, `BA/FlowPins.lean:184`, is the `Prop` of `baProp5s_holds`); stage 1b proves `X` with the
binders of `X_pin` as arguments.  Compile: `lake env lean RBM3D/Probe/T2414Pins.lean` in the T2414 worktree.

* §1 vocabulary (targets 1, 2): `Step2Kern_Msig`, `Step2Kern_Bsig`, `Step2Kern_Mss`; the kernels `Step2Gen_thetaKer`, `_uKer`,
  `_ThetaN`, `_UN` over a carrier `C : FlowFM sz` (they read `C.M` and `C.S`).
* §2 the operators and predicates that read the kernels, at their final text: `STthetaOpg`, `STgDriftg`, `STgDriftNg`,
  `STeeUMg`, `STGridMartAtgL/gL`, `STGridRepNAtgL/gL`, `STNewKLKAtgL/gL`, `STNewKLKAtgL'/gL'`, `NewKLKGenHyp` (F7 restated),
  `STK2decaygL'`.
* §3 pins of (b): `Step2Kern_Mss_of_kron`, `_Mss_band`, `_thetaKer_band`, `_uKer_band`, `_ThetaN_band`, `_UN_band` and the ten
  bridges that stop being `Iff.rfl` / `rfl`.  §4 pins of (c): `Step2Kern_Theta_comm`, `_Mss_BA`, `_thetaKer_BA`,
  `_BAKsolve_form`, `_uKer_BA`, `_UN_BA`.  §5 pins of (e).  §6 the pin of BAT-F2.
* §7 `#check` lines.  §8 compiled nonempty instances at `d = 3`: (b) at `sz0` (`L = 4`, `W = 32`), `E ≡ 0`; (c) at `sz0` along
  `zSeq`, `n = 0`; (e) at the band, pointwise at `n = 0`, `E = 0`, `u = 1/32`; G1; BAT-F2.

**Naming.**  The objects that 1b redefines in place carry their final names (`Step2Gen_thetaKer`, `STthetaOpg`, ...); here they
shadow the merged ones of `RBM.BA`, which are written `RBM.BA.X`.  The new public names of (a) carry `Step2Kern_`.

**Readings of the pseudo-Lean of (a)** (for the 1a-audit).
1. `Bsig` of (b) is `Step2Kern_Bsig Bm σ := if σ then Bm else Bmᴴ`, equal to `BAMsigma` by `rfl` (§8, BA instance); `Mss_of_kron`
   states the `kron` hypothesis with `split` (`Defs/Sizes.lean:64`: block label and offset of the fine point), `blk x = (split x).1`,
   `ofs x = (split x).2`.
2. (a) says `STgDriftNg`, `STGridRepNAtgL` "keep their text".  Compiled: their signature and the text of the clauses are
   unchanged, but the calls of `ThetaN` and `UN` read `Cm.toFlowFM n σ` (the operators take the carrier and the charges instead of
   `Cm.S n` and `fun i => STmsigg Cm n (σ i)`); `STeeUMg` reads `uKer` at `(σ_i, σ_{i+1})` and `(!σ_i, !σ_{i+1})`.
3. `STthetaOpg` is written as the sum over `i : Fin 2` with `(σ i, σ (finRotate 2 i))`; it is `Step2Gen_ThetaN` at `k = 2` by `rfl`
   (§8).  `finRotate`, as `cycProd` and `BAUN`.
4. F7 quantifies `s s' : Bool` (all four pairs, i.e. both slot pairs of every `σ`); F6 stays in `NewKLKGenHyp`, unused.
5. `stNewKLKAtgL'_holds_pin` is the `choose_spec` form (`NewKLKGen.lean:617`), quantified over a proof `hof` of
   `stNewKLKAtgL'_of_pin`.
6. The BA pins take `(E n + BAmF n).im ≠ 0` (the hypothesis of `BAMres_fine_kron`) and the data `lam0 E : ℕ → ℝ`; the instance
   `sz0` along `zSeq` is `lam0 = BAflowLam0 sz0 zSeq`, `E = BAflowEs sz0 zSeq`, `baFMz sz0 zSeq = baFM sz0 lam0 E` by `rfl`.
7. "The current ones" of (b) are the merged band kernels `RBM.thetaKer`, `uKer`, `ThetaN`, `UN` (`Kernel/Evolution.lean:52-67`):
   the in-place redefinition replaces the merged generic `Step2Gen_thetaKer S μ t`, `_uKer`, `_ThetaN`, `_UN`, so the `_band`
   pins are stated against `RBM.*`; at `S = SB` the two agree by `rfl` (§8).
8. In `Chain/Step2Gen.lean` the operator `STthetaOpg` (`:195`) comes before the kernels (`:715-733`): in 1b `Step2Kern_Msig`,
   `Step2Kern_Mss` and the kernels `thetaKer`, `uKer` go above it (after `Step2Gen_Theta`, `:191`).
-/

set_option linter.style.longLine false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.style.setOption false
set_option autoImplicit false

open private nkl_mE_zero nkl_STGMM_zero from RBM3D.Induction.NewKLK

noncomputable section

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal Topology Kronecker

namespace RBM.BA.T2414Pins

open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes

/-! ## 1. Vocabulary: the block kernel and the drift kernels read from the carrier (targets 1, 2) -/

section Vocab

variable {d : ℕ} {sz : Sizes d}

/-- `M(σ)_{xy}` of the carrier `C`: `M(+) = M`, `M(−) = M^*`, i.e. `M(−)_{xy} = conj M_{yx}` (the charge convention of
`STmsigg`, `Chain/Step2Gen.lean:156`, and of `G(z̄) = G(z)^*`; `BAMsigma`, `BA/MFixedPoint.lean:507`). -/
def Step2Kern_Msig (C : FlowFM sz) (n : ℕ) (σ : Bool) (x y : Idx d (sz.L n) (sz.W n)) : ℂ :=
  if σ then C.M n x y else (starRingEnd ℂ) (C.M n y x)

/-- `B(σ)` of a block matrix: `B(+) = B`, `B(−) = B^*` (`BAMsigma` at a general `B`). -/
def Step2Kern_Bsig {Λ : Type*} (Bm : Matrix Λ Λ ℂ) (σ : Bool) : Matrix Λ Λ ℂ :=
  if σ then Bm else Bmᴴ

/-- **The block kernel** `M^{(σσ')}_{ab} = W^{-d} Σ_{x∈[a]} Σ_{y∈[b]} M(σ)_{yx} M(σ')_{xy}` (`def:Theta_BA`, `1_2:663-664`;
`tr(M(σ)E_a M(σ')E_b)` of `eq:Msig`, `1_2:1070`, up to the `W^{±d}` normalisation).  **Charge and index order**: `M(+) = M`,
`M(−) = M^*`, and the block reading is `M(σ)_{ba} M(σ')_{ab}` (first charge on the entry `(b, a)`), as `BAMss`
(`BA/MFixedPoint.lean:511`), `BAMssOf` (`BA/KCactus.lean:50`) and the right-hand side of `BAKsolve` (`BA/KSolve.lean:63-66`,
`W^{-d} (Θ_BA M^{(σ₁σ₂)})_{a₁a₂}`; checked in §8 against the merged `baKsolve`).  It reads only `C.M`. -/
def Step2Kern_Mss (C : FlowFM sz) (n : ℕ) (σ σ' : Bool) : Matrix (Zd d (sz.L n)) (Zd d (sz.L n)) ℂ :=
  Matrix.of fun a b => (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ *
    ∑ x ∈ Iblk d (sz.L n) (sz.W n) a, ∑ y ∈ Iblk d (sz.L n) (sz.W n) b,
      Step2Kern_Msig C n σ y x * Step2Kern_Msig C n σ' x y

/-- **`thetaKer`** (`(def:op_thn)`, `3_5:109`): `X Θ_t(X) = X (1 - t X)⁻¹`, `X = M^{(σσ')} S` (replaces the merged
`Step2Gen_thetaKer S μ t = μ S Θ_{tμ}`; at the band `X = μ S`). -/
def Step2Gen_thetaKer (C : FlowFM sz) (n : ℕ) (σ σ' : Bool) (t : ℝ) : Matrix (Zd d (sz.L n)) (Zd d (sz.L n)) ℂ :=
  (Step2Kern_Mss C n σ σ' * C.S n) * Step2Gen_Theta (Step2Kern_Mss C n σ σ' * C.S n) (t : ℂ)

/-- **`uKer`** (`(def_Ustz)`, `3_5:116`): `(1 - s X) Θ_t(X)`, `X = M^{(σσ')} S`. -/
def Step2Gen_uKer (C : FlowFM sz) (n : ℕ) (σ σ' : Bool) (s t : ℝ) : Matrix (Zd d (sz.L n)) (Zd d (sz.L n)) ℂ :=
  (1 - (s : ℂ) • (Step2Kern_Mss C n σ σ' * C.S n)) * Step2Gen_Theta (Step2Kern_Mss C n σ σ' * C.S n) (t : ℂ)

/-- **`ThetaN`** (`(def:op_thn)`): slot `i` of a `k`-loop uses the charge pair `(σ_i, σ_{i+1})`, `σ_{k+1} = σ_1`
(`finRotate`, as `cycProd`, `Kernel/Evolution.lean:49`, and `BAUN`, `BA/EKPins.lean:53`). -/
def Step2Gen_ThetaN (C : FlowFM sz) (n : ℕ) {k : ℕ} (σ : Fin k → Bool) (t : ℝ) (A : (Fin k → Zd d (sz.L n)) → ℂ) :
    (Fin k → Zd d (sz.L n)) → ℂ :=
  fun a => ∑ i, ∑ b, Step2Gen_thetaKer C n (σ i) (σ (finRotate k i)) t (a i) b * A (Function.update a i b)

/-- **`UN`** (`(def_Ustz)`): the evolution kernel on `k`-index tensors, slot `i` with `(σ_i, σ_{i+1})`. -/
def Step2Gen_UN (C : FlowFM sz) (n : ℕ) {k : ℕ} (σ : Fin k → Bool) (s t : ℝ) (A : (Fin k → Zd d (sz.L n)) → ℂ) :
    (Fin k → Zd d (sz.L n)) → ℂ :=
  fun a => ∑ b : Fin k → Zd d (sz.L n), (∏ i, Step2Gen_uKer C n (σ i) (σ (finRotate k i)) s t (a i) (b i)) * A b

end Vocab

/-! ## 2. The operators and predicates that read the kernels (target 2), at their final text

Each is the merged declaration (`Chain/Step2Gen.lean`, `Chain/NewKLKGen.lean`; the source line is in the docstring) with the
kernel read from the carrier.  In 1b the same names are redefined in place; here they shadow the merged ones, which are written
`RBM.BA.X`.  A declaration whose docstring says "text unchanged" is a copy that unfolds through the new operator. -/

section Operators

variable {d : ℕ} {sz : Sizes d} (Cm : Step2Mat sz)

/-- `STthetaOpg` (`Chain/Step2Gen.lean:195`): `Σ_i Σ_b (thetaKer C n σ_i σ_{i+1} u)_{a_i b} A_{a^{(i)}(b)}`; `n = 2`: slot 0 has
`(σ₀, σ₁)`, slot 1 has `(σ₁, σ₀)`. -/
def STthetaOpg (n : ℕ) (u : ℝ) (σ : Fin 2 → Bool) (A : (Fin 2 → Zd d (sz.L n)) → ℂ) (a : Fin 2 → Zd d (sz.L n)) : ℂ :=
  ∑ i : Fin 2, ∑ b : Zd d (sz.L n),
    Step2Gen_thetaKer Cm.toFlowFM n (σ i) (σ (finRotate 2 i)) u (a i) b * A (Function.update a i b)

/-- `STgDriftg` (`:643`), text unchanged. -/
def STgDriftg (s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) (k : ℕ)
    (ω : PathΩ sz) : ℂ :=
  STthetaOpg Cm n (gridTime s t K n k) σ (STLKMg Cm n (gridTime s t K n k) (Cm.Hpath s t K n k ω) σ) a +
    STELKLKMg Cm n (gridTime s t K n k) (Cm.Hpath s t K n k ω) σ a +
    STEGtMg Cm n (gridTime s t K n k) (Cm.Hpath s t K n k ω) σ a

/-- `STgDriftNg` (`:789`): the call of `ThetaN` reads `Cm.toFlowFM` and the charges `σ` (it was `Cm.S n` and `m_σ`). -/
def STgDriftNg (s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) {m : ℕ} (σ : Fin m → Bool) (a : Fin m → Zd d (sz.L n)) (k : ℕ)
    (ω : PathΩ sz) : ℂ :=
  Step2Gen_ThetaN Cm.toFlowFM n σ (gridTime s t K n k)
      (fun a' => STLKIMg Cm n (gridTime s t K n k) (Cm.Hpath s t K n k ω) (KLloopOf d (sz.L n) σ a')) a +
    ∑ l ∈ Finset.Icc 3 m, STksimLKMg Cm n (gridTime s t K n k) (Cm.Hpath s t K n k ω) l
      (KLloopOf d (sz.L n) σ a) +
    STelklkMg Cm n (gridTime s t K n k) (Cm.Hpath s t K n k ω) (KLloopOf d (sz.L n) σ a) +
    STegtMg Cm n (gridTime s t K n k) (Cm.Hpath s t K n k ω) (KLloopOf d (sz.L n) σ a)

/-- `STeeUMg` (`:799`): the two products read `uKer` at `(σ_i, σ_{i+1})` and `(!σ_i, !σ_{i+1})`. -/
def STeeUMg (n : ℕ) (v w : ℝ) (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    {m : ℕ} (σ : Fin m → Bool) (a : Fin m → Zd d (sz.L n)) : ℂ :=
  ∑ b : Fin m → Zd d (sz.L n), ∑ b' : Fin m → Zd d (sz.L n),
    (∏ i, Step2Gen_uKer Cm.toFlowFM n (σ i) (σ (finRotate m i)) v w (a i) (b i)) *
      (∏ i, Step2Gen_uKer Cm.toFlowFM n (!σ i) (!σ (finRotate m i)) v w (a i) (b' i)) *
        STeeMg Cm n v H σ b b'

end Operators

/-- `STGridMartAtgL` (`:659`), text unchanged (through `STgDriftg`). -/
def STGridMartAtgL (d : ℕ) (C₀ : ℝ) (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop)
    (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), Step2Mat sz) (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) : Prop :=
  ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), Flow sz κ ε 𝔠 𝔡 z →
      ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n ≤ t n) → (∀ n, t n ≤ T0 sz z n) →
        ∀ D : ℝ, 0 < D → ∃ CK : ℝ, 0 ≤ CK ∧
          ∀ K : ℕ → ℕ, (∀ n, K n ≠ 0) → (∀ᶠ n in atTop, ((sz.size n : ℕ) : ℝ) ^ CK ≤ K n) →
            ∃ Mart Rem : ∀ n, ((Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n))) → ℕ → PathΩ sz → ℂ,
              (∀ n i, ∀ᵐ ω ∂((mk sz z).Pp), ∀ k, k ≤ K n →
                STgAg (mk sz z) s t K n i.1 i.2 k ω =
                  STgAg (mk sz z) s t K n i.1 i.2 0 ω +
                    ((gridStep s t K n : ℝ) : ℂ) *
                      ∑ j ∈ Finset.range k, STgDriftg (mk sz z) s t K n i.1 i.2 j ω +
                    Rem n i k ω + Mart n i k ω) ∧
              (∀ᶠ n in atTop, ∀ i, ∀ᵐ ω ∂((mk sz z).Pp), ∀ k, k ≤ K n →
                ‖Rem n i k ω‖ ≤ ((sz.size n : ℕ) : ℝ) ^ C₀ * Real.sqrt (gridStep s t K n)) ∧
              (∀ ε' : ℝ, 0 < ε' → ∀ᶠ n in atTop, ∀ i,
                (mk sz z).Pp {ω | ∃ k, k ≤ K n ∧
                  ((sz.size n : ℕ) : ℝ) ^ ε' *
                      (∑ j ∈ Finset.range k, gridStep s t K n *
                        ‖STEEMg (mk sz z) n (gridTime s t K n j) ((mk sz z).Hpath s t K n j ω)
                          i.1 i.2‖ + ((sz.size n : ℕ) : ℝ) ^ (-D)) ^ (1 / 2 : ℝ) <
                    ‖Mart n i k ω‖} ≤ ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-D)))

/-- `STGridMartgL` (`:684`), text unchanged. -/
def STGridMartgL (d : ℕ) (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop)
    (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), Step2Mat sz) (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) : Prop :=
  ∃ C₀ : ℝ, 0 ≤ C₀ ∧ STGridMartAtgL d C₀ Flow mk T0

/-- `STGridRepNAtgL` (`:810`): text unchanged (through `STgDriftNg`, `STeeUMg`) except the last clause, whose `UN` call reads
`(mk sz z).toFlowFM` and the charges `i.1` (it was `(mk sz z).S n` and `m_{i.1}`). -/
def STGridRepNAtgL (d m : ℕ) (C₀ : ℝ) (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop)
    (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), Step2Mat sz) (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) : Prop :=
  ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), Flow sz κ ε 𝔠 𝔡 z →
      ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n ≤ t n) → (∀ n, t n ≤ T0 sz z n) →
        ∀ D : ℝ, 0 < D → ∃ CK : ℝ, 0 ≤ CK ∧
          ∀ K : ℕ → ℕ, (∀ n, K n ≠ 0) → (∀ᶠ n in atTop, ((sz.size n : ℕ) : ℝ) ^ CK ≤ K n) →
            ∃ Mart Rem : ∀ n, ((Fin m → Bool) × (Fin m → Zd d (sz.L n))) → ℕ → PathΩ sz → ℂ,
              (∀ (n : ℕ) (i : (Fin m → Bool) × (Fin m → Zd d (sz.L n))), ∀ᵐ ω ∂((mk sz z).Pp), ∀ k, k ≤ K n →
                STgANg (mk sz z) s t K n i.1 i.2 k ω =
                  STgANg (mk sz z) s t K n i.1 i.2 0 ω +
                    ((gridStep s t K n : ℝ) : ℂ) *
                      ∑ j ∈ Finset.range k, STgDriftNg (mk sz z) s t K n i.1 i.2 j ω +
                    Rem n i k ω + Mart n i k ω) ∧
              (∀ᶠ n in atTop, ∀ i : (Fin m → Bool) × (Fin m → Zd d (sz.L n)), ∀ᵐ ω ∂((mk sz z).Pp), ∀ k, k ≤ K n →
                ‖Rem n i k ω‖ ≤ ((sz.size n : ℕ) : ℝ) ^ C₀ * Real.sqrt (gridStep s t K n)) ∧
              (∀ ε' : ℝ, 0 < ε' → ∀ᶠ n in atTop, ∀ i : (Fin m → Bool) × (Fin m → Zd d (sz.L n)),
                (mk sz z).Pp {ω | ∃ k, k ≤ K n ∧
                  ((sz.size n : ℕ) : ℝ) ^ ε' *
                      (∑ j ∈ Finset.range k, gridStep s t K n *
                        ‖STeeMg (mk sz z) n (gridTime s t K n j) ((mk sz z).Hpath s t K n j ω)
                          i.1 i.2 i.2‖ + ((sz.size n : ℕ) : ℝ) ^ (-D)) ^ (1 / 2 : ℝ) <
                    ‖Mart n i k ω‖} ≤ ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-D))) ∧
              (∀ ε' : ℝ, 0 < ε' → ∀ᶠ n in atTop, ∀ i : (Fin m → Bool) × (Fin m → Zd d (sz.L n)),
                (mk sz z).Pp {ω | ∃ k, k ≤ K n ∧
                  ((sz.size n : ℕ) : ℝ) ^ ε' *
                      (∑ j ∈ Finset.range k, gridStep s t K n *
                        ‖STeeUMg (mk sz z) n (gridTime s t K n j) (gridTime s t K n k)
                          ((mk sz z).Hpath s t K n j ω) i.1 i.2‖ + ((sz.size n : ℕ) : ℝ) ^ (-D)) ^
                          (1 / 2 : ℝ) <
                    ‖∑ j ∈ Finset.range k,
                      Step2Gen_UN (mk sz z).toFlowFM n i.1
                        (gridTime s t K n j) (gridTime s t K n k)
                        (fun b => Mart n (i.1, b) (j + 1) ω - Mart n (i.1, b) j ω) i.2‖} ≤
                  ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-D)))

/-- `STGridRepNgL` (`:847`), text unchanged. -/
def STGridRepNgL (d : ℕ) (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop)
    (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), Step2Mat sz) (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) : Prop :=
  ∀ m : ℕ, 2 ≤ m → ∃ C₀ : ℝ, 0 ≤ C₀ ∧ STGridRepNAtgL d m C₀ Flow mk T0

/-- `STNewKLKAtgL` (`:889`), text unchanged (through `STthetaOpg`). -/
def STNewKLKAtgL (d : ℕ) (κ 𝔡 C δ₀ : ℝ) (mk : ∀ sz : Sizes d, (ℕ → ℝ) → Step2Mat sz) : Prop :=
  ∀ (sz : Sizes d) (n : ℕ) (E u D ℓ : ℝ), 0 < sz.lam n → sz.lam n ≤ 𝔡⁻¹ → |E| ≤ 2 - κ →
    0 ≤ u → u < 1 → 0 ≤ D → 0 ≤ ℓ → ℓ ≤ ((sz.L n : ℕ) : ℝ) →
    ∀ H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ, H.IsHermitian →
      (∀ x y, ‖STGMMg (mk sz (fun _ => E)) n u H x y‖ ≤ δ₀) →
      ∀ (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)),
        ‖STthetaOpg (mk sz (fun _ => E)) n u σ (STLKMg (mk sz (fun _ => E)) n u H σ) a‖ ≤
            C / (1 - u) * STJhatMg (mk sz (fun _ => E)) n D ℓ u H * STprof sz n u D ℓ (a 0) (a 1) ∧
        ‖STELKLKMg (mk sz (fun _ => E)) n u H σ a‖ ≤
            C / (1 - u) * (STJhatMg (mk sz (fun _ => E)) n D ℓ u H +
              STJhatMg (mk sz (fun _ => E)) n D ℓ u H ^ 2 * (if 1 ≤ ℓ then 1 else 0)) *
              STprof sz n u D ℓ (a 0) (a 1)

/-- `STNewKLKgL` (`:903`), text unchanged. -/
def STNewKLKgL (d : ℕ) (mk : ∀ sz : Sizes d, (ℕ → ℝ) → Step2Mat sz) : Prop :=
  3 ≤ d → ∀ κ 𝔡 : ℝ, 0 < κ → 0 < 𝔡 → ∃ C δ₀ : ℝ, 0 < C ∧ 0 < δ₀ ∧ STNewKLKAtgL d κ 𝔡 C δ₀ mk

/-- `STNewKLKAtgL'` (`Chain/NewKLKGen.lean:55`), text unchanged (through `STthetaOpg`): premise `κ ≤ Im m`. -/
def STNewKLKAtgL' (d : ℕ) (κ 𝔡 C δ₀ : ℝ) (mk : ∀ sz : Sizes d, (ℕ → ℝ) → Step2Mat sz) : Prop :=
  ∀ (sz : Sizes d) (n : ℕ) (E u D ℓ : ℝ), 0 < sz.lam n → sz.lam n ≤ 𝔡⁻¹ → κ ≤ ((mk sz (fun _ => E)).m n).im →
    0 ≤ u → u < 1 → 0 ≤ D → 0 ≤ ℓ → ℓ ≤ ((sz.L n : ℕ) : ℝ) →
    ∀ H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ, H.IsHermitian →
      (∀ x y, ‖STGMMg (mk sz (fun _ => E)) n u H x y‖ ≤ δ₀) →
      ∀ (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)),
        ‖STthetaOpg (mk sz (fun _ => E)) n u σ (STLKMg (mk sz (fun _ => E)) n u H σ) a‖ ≤
            C / (1 - u) * STJhatMg (mk sz (fun _ => E)) n D ℓ u H * STprof sz n u D ℓ (a 0) (a 1) ∧
        ‖STELKLKMg (mk sz (fun _ => E)) n u H σ a‖ ≤
            C / (1 - u) * (STJhatMg (mk sz (fun _ => E)) n D ℓ u H +
              STJhatMg (mk sz (fun _ => E)) n D ℓ u H ^ 2 * (if 1 ≤ ℓ then 1 else 0)) *
              STprof sz n u D ℓ (a 0) (a 1)

/-- `STNewKLKgL'` (`Chain/NewKLKGen.lean:69`), text unchanged. -/
def STNewKLKgL' (d : ℕ) (mk : ∀ sz : Sizes d, (ℕ → ℝ) → Step2Mat sz) : Prop :=
  3 ≤ d → ∀ κ 𝔡 : ℝ, 0 < κ → 0 < 𝔡 → ∃ C δ₀ : ℝ, 0 < C ∧ 0 < δ₀ ∧ STNewKLKAtgL' d κ 𝔡 C δ₀ mk

/-- **`NewKLKGenHyp`, F7 restated over the new kernel** (`Chain/NewKLKGen.lean:378-407`; F5, F6, F8, F9 are the merged text,
F6 stays and is unused).  F7: for every charge pair `(s, s')` (both slot pairs `(σ₀, σ₁)`, `(σ₁, σ₀)` of every `σ`),
`Σ_b ‖thetaKer C n s s' u (a, b)‖ 𝒯̃(|b - a'|_∞) ≤ K_c/(1-u) 𝒯̃(|a - a'|_∞)`, `C = mk sz (fun _ => E)`; it was
`Σ_b ‖(S Θ_{u m_{σ₀} m_{σ₁}})(a, b)‖ …`. -/
def NewKLKGenHyp (d : ℕ) (κ 𝔡 : ℝ) (mk : ∀ sz : Sizes d, (ℕ → ℝ) → Step2Mat sz) : Prop :=
  ∃ K_c C_K : ℝ, 0 ≤ K_c ∧ 0 ≤ C_K ∧
  (∀ (sz : Sizes d) (n : ℕ) (E : ℝ), 0 < sz.lam n → sz.lam n ≤ 𝔡⁻¹ →
      κ ≤ ((mk sz (fun _ => E)).m n).im →
      (∀ x y, (mk sz (fun _ => E)).S n x y ≠ 0 → zdistInf d (sz.L n) (x - y) ≤ 1) ∧
        (∀ x, ∑ y, ‖(mk sz (fun _ => E)).S n x y‖ ≤ 1) ∧
        (∀ x y, ‖(mk sz (fun _ => E)).S n x y‖ = ‖(mk sz (fun _ => E)).S n y x‖)) ∧
  (∀ (sz : Sizes d) (n : ℕ) (E : ℝ), 0 < sz.lam n → sz.lam n ≤ 𝔡⁻¹ →
      κ ≤ ((mk sz (fun _ => E)).m n).im → ‖(mk sz (fun _ => E)).m n‖ ≤ 1) ∧
  (∀ (sz : Sizes d) (n : ℕ) (E u : ℝ), 0 < sz.lam n → sz.lam n ≤ 𝔡⁻¹ →
      κ ≤ ((mk sz (fun _ => E)).m n).im → 0 ≤ u → u < 1 → ∀ (s s' : Bool) (ℓ' D' : ℝ), 0 ≤ ℓ' → 0 ≤ D' →
      ∀ a a' : Zd d (sz.L n),
        ∑ b, ‖Step2Gen_thetaKer (mk sz (fun _ => E)).toFlowFM n s s' u a b‖ *
          tailW d (sz.L n) (sz.lam n) u ℓ' ((sz.W n : ℕ) : ℝ) D' ((zdistInf d (sz.L n) (b - a') : ℕ) : ℝ) ≤
        K_c / (1 - u) *
          tailW d (sz.L n) (sz.lam n) u ℓ' ((sz.W n : ℕ) : ℝ) D' ((zdistInf d (sz.L n) (a - a') : ℕ) : ℝ)) ∧
  (∀ (sz : Sizes d) (n : ℕ) (E u : ℝ), 0 < sz.lam n → sz.lam n ≤ 𝔡⁻¹ →
      κ ≤ ((mk sz (fun _ => E)).m n).im → 0 ≤ u → u < 1 → ∀ σ : Fin 2 → Bool,
      (∀ a₁ : Zd d (sz.L n), ∑ x, ‖(mk sz (fun _ => E)).K n u σ ![x, a₁]‖ ≤
        C_K * ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (1 - u)⁻¹)) ∧
      (∀ a₀ : Zd d (sz.L n), ∑ y, ‖(mk sz (fun _ => E)).K n u σ ![a₀, y]‖ ≤
        C_K * ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (1 - u)⁻¹))) ∧
  (∀ (sz : Sizes d) (n : ℕ) (E u : ℝ), 0 < sz.lam n → sz.lam n ≤ 𝔡⁻¹ →
      κ ≤ ((mk sz (fun _ => E)).m n).im → 0 ≤ u → u < 1 →
      ∃ ζ : ℂ, ζ.im = (1 - u) * ((mk sz (fun _ => E)).m n).im ∧
        (∀ (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (σ : Fin 2 → Bool)
          (a : Fin 2 → Zd d (sz.L n)), (mk sz (fun _ => E)).LM n u H σ a = loopFine d (sz.L n) (sz.W n) H ζ σ a) ∧
        (∀ (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (x : Idx d (sz.L n) (sz.W n)),
          (mk sz (fun _ => E)).GMM n u H x x = Gres H ζ true x x - (mk sz (fun _ => E)).m n))

/-! ### 2.1 BAT-F2: the primed predicate `STK2decaygL'` -/

/-- **`STK2decaygL'`** (BAT-F2): `STK2decaygL` (`Chain/Step2Gen.lean:907-913`) with the premise `|E| ≤ 2 - κ` replaced by
`κ ≤ Im m` (the one-loop value of the family at the constant sequence `fun _ => E`), as `STNewKLKgL'`.  `K` is a carrier
field: no kernel enters. -/
def STK2decaygL' (d : ℕ) (mk : ∀ sz : Sizes d, (ℕ → ℝ) → Step2Mat sz) : Prop :=
  3 ≤ d → ∀ κ 𝔡 : ℝ, 0 < κ → 0 < 𝔡 → ∃ C : ℝ, 0 < C ∧
    ∀ (sz : Sizes d) (n : ℕ) (E u D : ℝ), 0 < sz.lam n → sz.lam n ≤ 𝔡⁻¹ → κ ≤ ((mk sz (fun _ => E)).m n).im →
      0 ≤ u → u < 1 → 0 ≤ D → ∀ (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)),
        ‖(mk sz (fun _ => E)).K n u σ a‖ ≤ C * STprof sz n u D ((sz.L n : ℕ) : ℝ) (a 0) (a 1)

/-! ## 3. Pins of target 3 (b): the block kernel at the band, and the bridges that stop being `Iff.rfl`

A pin `X_pin : Prop` is the statement of the theorem `X` that 1b proves (the shape of `BAProp5s`/`baProp5s_holds`).  The merged
declarations that the new ones replace are written `RBM.BA.X`. -/

/-- **`Step2Kern_Mss_of_kron`**: if `M = Bm ⊗ I_{W^d}`, i.e. `M_{xy} = Bm(blk x, blk y) · 1{ofs x = ofs y}` (`split`,
`Defs/Sizes.lean:64`), then `M^{(σσ')}_{ab} = Bsig(σ)_{ba} Bsig(σ')_{ab}`. -/
def Step2Kern_Mss_of_kron_pin : Prop :=
  ∀ (d : ℕ) (sz : Sizes d) (C : FlowFM sz) (n : ℕ) (Bm : Matrix (Zd d (sz.L n)) (Zd d (sz.L n)) ℂ),
    (∀ x y : Idx d (sz.L n) (sz.W n), C.M n x y =
      Bm (split d (sz.L n) (sz.W n) x).1 (split d (sz.L n) (sz.W n) y).1 *
        (if (split d (sz.L n) (sz.W n) x).2 = (split d (sz.L n) (sz.W n) y).2 then 1 else 0)) →
    ∀ σ σ' : Bool, Step2Kern_Mss C n σ σ' = Matrix.of fun a b => Step2Kern_Bsig Bm σ b a * Step2Kern_Bsig Bm σ' a b

/-- **`Step2Kern_Mss_band`**: at `bandFM`, `M = m(E) I` gives `M^{(σσ')} = m(σ) m(σ') I`. -/
def Step2Kern_Mss_band_pin : Prop :=
  ∀ (d : ℕ) (sz : Sizes d) (E : ℕ → ℝ) (n : ℕ) (σ σ' : Bool),
    Step2Kern_Mss (bandFM sz E) n σ σ' = (mSigma (E n) σ * mSigma (E n) σ') • (1 : Matrix (Zd d (sz.L n)) (Zd d (sz.L n)) ℂ)

/-- **`Step2Kern_thetaKer_band`**: the new `thetaKer` at `bandFM` is the merged band kernel `μ S^{(B)} Θ_{tμ}`
(`RBM.thetaKer`, `Kernel/Evolution.lean:52`), `μ = m(σ) m(σ')`.  (The merged generic `Step2Gen_thetaKer S μ t` is replaced by the
redefinition; at `S = SB` it is `RBM.thetaKer` by `rfl`, §8.) -/
def Step2Kern_thetaKer_band_pin : Prop :=
  ∀ (d : ℕ) (sz : Sizes d) (E : ℕ → ℝ) (n : ℕ) (σ σ' : Bool) (t : ℝ),
    Step2Gen_thetaKer (bandFM sz E) n σ σ' t =
      RBM.thetaKer d (sz.L n) (sz.lam n) (mSigma (E n) σ * mSigma (E n) σ') t

/-- **`Step2Kern_uKer_band`**: the new `uKer` at `bandFM` is the merged band kernel `(1 - s μ S^{(B)}) Θ_{tμ}` (`RBM.uKer`,
`Kernel/Evolution.lean:56`). -/
def Step2Kern_uKer_band_pin : Prop :=
  ∀ (d : ℕ) (sz : Sizes d) (E : ℕ → ℝ) (n : ℕ) (σ σ' : Bool) (s t : ℝ),
    Step2Gen_uKer (bandFM sz E) n σ σ' s t =
      RBM.uKer d (sz.L n) (sz.lam n) (mSigma (E n) σ * mSigma (E n) σ') s t

/-- **`Step2Kern_ThetaN_band`**: the new `ThetaN` at `bandFM` is the merged band `RBM.ThetaN` at `m_i = m(σ_i)` (slot `i` has
`cycProd`, `Kernel/Evolution.lean:60`). -/
def Step2Kern_ThetaN_band_pin : Prop :=
  ∀ (d : ℕ) (sz : Sizes d) (E : ℕ → ℝ) (n k : ℕ) (σ : Fin k → Bool) (t : ℝ) (A : (Fin k → Zd d (sz.L n)) → ℂ),
    Step2Gen_ThetaN (bandFM sz E) n σ t A =
      RBM.ThetaN d (sz.L n) (sz.lam n) (fun i => mSigma (E n) (σ i)) t A

/-- **`Step2Kern_UN_band`**: the new `UN` at `bandFM` is the merged band `RBM.UN` at `m_i = m(σ_i)`
(`Kernel/Evolution.lean:65`). -/
def Step2Kern_UN_band_pin : Prop :=
  ∀ (d : ℕ) (sz : Sizes d) (E : ℕ → ℝ) (n k : ℕ) (σ : Fin k → Bool) (s t : ℝ) (A : (Fin k → Zd d (sz.L n)) → ℂ),
    Step2Gen_UN (bandFM sz E) n σ s t A =
      RBM.UN d (sz.L n) (sz.lam n) (fun i => mSigma (E n) (σ i)) s t A

/-- Bridge `bandStep2_STthetaOp` (`:241`): the merged band `STthetaOp` is the new `STthetaOpg` at `bandStep2Mat` (was `rfl`;
now `Fin.sum_univ_two`, `mul_comm` at slot 1, `Step2Kern_thetaKer_band`). -/
def bandStep2_STthetaOp_pin : Prop :=
  ∀ (d : ℕ) (sz : Sizes d) (E : ℕ → ℝ) (n : ℕ) (u : ℝ) (σ : Fin 2 → Bool) (A : (Fin 2 → Zd d (sz.L n)) → ℂ)
    (a : Fin 2 → Zd d (sz.L n)), STthetaOp sz n (E n) u σ A a = STthetaOpg (bandStep2Mat sz E) n u σ A a

/-- Bridge `bandStep2_STgDrift` (`:694`). -/
def bandStep2_STgDrift_pin : Prop :=
  ∀ (d : ℕ) (sz : Sizes d) (E s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) (k : ℕ)
    (ω : PathΩ sz), STgDrift sz s t K n (E n) σ a k ω = STgDriftg (bandStep2Mat sz E) s t K n σ a k ω

/-- Bridge `bandStep2_STgDriftN` (`:871`). -/
def bandStep2_STgDriftN_pin : Prop :=
  ∀ (d : ℕ) (sz : Sizes d) (E s t : ℕ → ℝ) (K : ℕ → ℕ) (n m : ℕ) (σ : Fin m → Bool) (a : Fin m → Zd d (sz.L n)) (k : ℕ)
    (ω : PathΩ sz), STgDriftN sz s t K n (E n) σ a k ω = STgDriftNg (bandStep2Mat sz E) s t K n σ a k ω

/-- Bridge `bandStep2_STeeUM` (`:874`; **not in the ticket's list**: `STeeUMg` is redefined, it reads `uKer`). -/
def bandStep2_STeeUM_pin : Prop :=
  ∀ (d : ℕ) (sz : Sizes d) (E : ℕ → ℝ) (n : ℕ) (v w : ℝ)
    (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (m : ℕ) (σ : Fin m → Bool)
    (a : Fin m → Zd d (sz.L n)), STeeUM sz n (E n) v w H σ a = STeeUMg (bandStep2Mat sz E) n v w H σ a

/-- Bridge `bandStep2_STGridMartAt` (`:698`). -/
def bandStep2_STGridMartAt_pin : Prop :=
  ∀ (d : ℕ) (C₀ : ℝ), STGridMartAt d C₀ ↔ STGridMartAtgL d C₀ (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
    (fun sz z => bandStep2Mat sz (STflowE z)) (fun _ z n => lemT (z n))

/-- Bridge `bandStep2_STGridMart` (`:701`). -/
def bandStep2_STGridMart_pin : Prop :=
  ∀ d : ℕ, STGridMart d ↔ STGridMartgL d (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
    (fun sz z => bandStep2Mat sz (STflowE z)) (fun _ z n => lemT (z n))

/-- Bridge `bandStep2_STGridRepNAt` (`:876`). -/
def bandStep2_STGridRepNAt_pin : Prop :=
  ∀ (d m : ℕ) (C₀ : ℝ), STGridRepNAt d m C₀ ↔ STGridRepNAtgL d m C₀ (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
    (fun sz z => bandStep2Mat sz (STflowE z)) (fun _ z n => lemT (z n))

/-- Bridge `bandStep2_STGridRepN` (`:879`). -/
def bandStep2_STGridRepN_pin : Prop :=
  ∀ d : ℕ, STGridRepN d ↔ STGridRepNgL d (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
    (fun sz z => bandStep2Mat sz (STflowE z)) (fun _ z n => lemT (z n))

/-- Bridge `bandStep2_STNewKLKAt` (`:917`). -/
def bandStep2_STNewKLKAt_pin : Prop :=
  ∀ (d : ℕ) (κ 𝔡 C δ₀ : ℝ), STNewKLKAt d κ 𝔡 C δ₀ ↔ STNewKLKAtgL d κ 𝔡 C δ₀ (fun sz E => bandStep2Mat sz E)

/-- Bridge `bandStep2_STNewKLK` (`:919`). -/
def bandStep2_STNewKLK_pin : Prop :=
  ∀ d : ℕ, STNewKLK d ↔ STNewKLKgL d (fun sz E => bandStep2Mat sz E)

/-! ## 4. Pins of target 4 (c): the BA identities, at the carrier `baFM sz lam0 E` (`S = 1`)

The hypothesis `(E n + m).im ≠ 0` is that of `BAMres_fine_kron` (`BA/FlowPins.lean:72`); `NeZero (sz.L n)`, `NeZero (sz.W n)`
are instances. -/

/-- `Θ_ξ(X)` commutes with `X` (`Ring.inverse (1 - ξ X)`; BA only, to turn `Mss Θ` into the `Θ Mss` of `BAKsolve`). -/
def Step2Kern_Theta_comm_pin : Prop :=
  ∀ {Λ : Type} [Fintype Λ] [DecidableEq Λ] (X : Matrix Λ Λ ℂ) (ξ : ℂ), X * Step2Gen_Theta X ξ = Step2Gen_Theta X ξ * X

/-- **`Step2Kern_Mss_BA`**: the derived block kernel at the BA carrier is `BAMss` of `M^{(B)} = BAMB` (index order of
`BAKsolve`, `BA/KSolve.lean:58-66`). -/
def Step2Kern_Mss_BA_pin : Prop :=
  ∀ (d : ℕ) (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ), (((E n : ℝ) : ℂ) + BAmF sz lam0 E n).im ≠ 0 →
    ∀ σ σ' : Bool, Step2Kern_Mss (baFM sz lam0 E) n σ σ' =
      BAMss d (sz.L n) (BAMB d (sz.L n) (lam0 n) (E n : ℂ) (BAmF sz lam0 E n)) σ σ'

/-- **`Step2Kern_thetaKer_BA`**: `thetaKer = Θ_BA M^{(σσ')}` (`S = 1`; `BATheta`, `BAMss`). -/
def Step2Kern_thetaKer_BA_pin : Prop :=
  ∀ (d : ℕ) (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ), (((E n : ℝ) : ℂ) + BAmF sz lam0 E n).im ≠ 0 →
    ∀ (σ σ' : Bool) (t : ℝ), Step2Gen_thetaKer (baFM sz lam0 E) n σ σ' t =
      BATheta d (sz.L n) (lam0 n) (E n) (BAmF sz lam0 E n) t σ σ' *
        BAMss d (sz.L n) (BAMB d (sz.L n) (lam0 n) (E n : ℂ) (BAmF sz lam0 E n)) σ σ'

/-- **`Step2Kern_BAKsolve_form`**: `W^{-d}` times the two-loop drift kernel is the right-hand side of `BAKsolve`
(`BA/KSolve.lean:63-66`), for the four charge pairs `σ : Bool × Bool`. -/
def Step2Kern_BAKsolve_form_pin : Prop :=
  ∀ (d : ℕ) (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ), (((E n : ℝ) : ℂ) + BAmF sz lam0 E n).im ≠ 0 →
    ∀ (t : ℝ) (σ : Bool × Bool) (a₁ a₂ : Zd d (sz.L n)),
      (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * Step2Gen_thetaKer (baFM sz lam0 E) n σ.1 σ.2 t a₁ a₂ =
        (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * (BATheta d (sz.L n) (lam0 n) (E n) (BAmF sz lam0 E n) t σ.1 σ.2 *
          BAMss d (sz.L n) (BAMB d (sz.L n) (lam0 n) (E n : ℂ) (BAmF sz lam0 E n)) σ.1 σ.2) a₁ a₂

/-- **`Step2Kern_uKer_BA`**: `uKer = BAuKer` (`BA/EKPins.lean:49`). -/
def Step2Kern_uKer_BA_pin : Prop :=
  ∀ (d : ℕ) (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ), (((E n : ℝ) : ℂ) + BAmF sz lam0 E n).im ≠ 0 →
    ∀ (σ σ' : Bool) (s t : ℝ), Step2Gen_uKer (baFM sz lam0 E) n σ σ' s t =
      BAuKer d (sz.L n) (lam0 n) (E n) (BAmF sz lam0 E n) s t σ σ'

/-- **`Step2Kern_UN_BA`** (E-C1): the BA reading of the new `UN` is stage E's `BAUN` (`BA/EKPins.lean:53`); both products use
`finRotate`.  There is no `ThetaN` twin in `BA/*.lean`. -/
def Step2Kern_UN_BA_pin : Prop :=
  ∀ (d : ℕ) (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ), (((E n : ℝ) : ℂ) + BAmF sz lam0 E n).im ≠ 0 →
    ∀ (k : ℕ) (σ : Fin k → Bool) (s t : ℝ) (A : (Fin k → Zd d (sz.L n)) → ℂ),
      Step2Gen_UN (baFM sz lam0 E) n σ s t A = BAUN d (sz.L n) (lam0 n) (E n) (BAmF sz lam0 E n) σ s t A

/-! ## 5. Pins of target 5 (e): `lem:newKLK` over the new kernel -/

/-- `stNewKLKAtgL'_of` (`Chain/NewKLKGen.lean:412`): `δ₀ = κ/2`, over the restated `NewKLKGenHyp` (F7). -/
def stNewKLKAtgL'_of_pin : Prop :=
  ∀ (d : ℕ), 3 ≤ d → ∀ (κ 𝔡 : ℝ), 0 < κ → ∀ (mk : ∀ sz : Sizes d, (ℕ → ℝ) → Step2Mat sz),
    NewKLKGenHyp d κ 𝔡 mk → ∃ C : ℝ, 0 < C ∧ STNewKLKAtgL' d κ 𝔡 C (κ / 2) mk

/-- `stNewKLKAtgL'_holds` (`:617`): the pointwise form at the constant that `stNewKLKAtgL'_of` chooses. -/
def stNewKLKAtgL'_holds_pin : Prop :=
  ∀ (hof : stNewKLKAtgL'_of_pin) (d : ℕ) (hd : 3 ≤ d) (κ 𝔡 : ℝ) (hκ : 0 < κ) (mk : ∀ sz : Sizes d, (ℕ → ℝ) → Step2Mat sz)
    (hyp : NewKLKGenHyp d κ 𝔡 mk), STNewKLKAtgL' d κ 𝔡 (hof d hd κ 𝔡 hκ mk hyp).choose (κ / 2) mk

/-- `stNewKLKgL'_of` (`:624`). -/
def stNewKLKgL'_of_pin : Prop :=
  ∀ (d : ℕ) (mk : ∀ sz : Sizes d, (ℕ → ℝ) → Step2Mat sz),
    (3 ≤ d → ∀ κ 𝔡 : ℝ, 0 < κ → 0 < 𝔡 → NewKLKGenHyp d κ 𝔡 mk) → STNewKLKgL' d mk

/-- `newKLKGenHyp_band` (`:664`): F5-F9 at the band family, F7 through `Step2Kern_thetaKer_band`. -/
def newKLKGenHyp_band_pin : Prop :=
  ∀ (d : ℕ), 3 ≤ d → ∀ κ 𝔡 : ℝ, 0 < κ → 0 < 𝔡 → NewKLKGenHyp d κ 𝔡 (fun sz E => bandStep2Mat sz E)

/-- `stNewKLKgL_of_primed` (`:644`), text unchanged over the new `STNewKLKgL`, `STNewKLKgL'`. -/
def stNewKLKgL_of_primed_pin : Prop :=
  ∀ (d : ℕ) (mk : ∀ sz : Sizes d, (ℕ → ℝ) → Step2Mat sz), STNewKLKgL' d mk →
    (∀ κ 𝔡 : ℝ, 0 < κ → 0 < 𝔡 → ∀ (sz : Sizes d) (n : ℕ) (E : ℝ), 0 < sz.lam n → sz.lam n ≤ 𝔡⁻¹ →
      |E| ≤ 2 - κ → κ / 2 ≤ ((mk sz (fun _ => E)).m n).im) → STNewKLKgL d mk

/-! ## 6. Pin of target 6 (BAT-F2): the bridge from the primed to the unprimed `K^{(2)}` decay -/

/-- `stK2decaygL_of_primed` (the shape of `stNewKLKgL_of_primed`): `STK2decaygL' d mk` at `κ' = κ/2` and the domain fact
`|E| ≤ 2 - κ → κ/2 ≤ Im m` give `STK2decaygL d mk`. -/
def stK2decaygL_of_primed_pin : Prop :=
  ∀ (d : ℕ) (mk : ∀ sz : Sizes d, (ℕ → ℝ) → Step2Mat sz), STK2decaygL' d mk →
    (∀ κ 𝔡 : ℝ, 0 < κ → 0 < 𝔡 → ∀ (sz : Sizes d) (n : ℕ) (E : ℝ), 0 < sz.lam n → sz.lam n ≤ 𝔡⁻¹ →
      |E| ≤ 2 - κ → κ / 2 ≤ ((mk sz (fun _ => E)).m n).im) → STK2decaygL d mk

/-! ## 7. `#check` lines -/

#check Step2Kern_Msig
#check Step2Kern_Bsig
#check Step2Kern_Mss
#check Step2Gen_thetaKer
#check Step2Gen_uKer
#check Step2Gen_ThetaN
#check Step2Gen_UN
#check STthetaOpg
#check STgDriftg
#check STgDriftNg
#check STeeUMg
#check STGridMartAtgL
#check STGridMartgL
#check STGridRepNAtgL
#check STGridRepNgL
#check STNewKLKAtgL
#check STNewKLKgL
#check STNewKLKAtgL'
#check STNewKLKgL'
#check NewKLKGenHyp
#check STK2decaygL'
#check Step2Kern_Mss_of_kron_pin
#check Step2Kern_Mss_band_pin
#check Step2Kern_thetaKer_band_pin
#check Step2Kern_uKer_band_pin
#check Step2Kern_ThetaN_band_pin
#check Step2Kern_UN_band_pin
#check bandStep2_STthetaOp_pin
#check bandStep2_STgDrift_pin
#check bandStep2_STgDriftN_pin
#check bandStep2_STeeUM_pin
#check bandStep2_STGridMartAt_pin
#check bandStep2_STGridMart_pin
#check bandStep2_STGridRepNAt_pin
#check bandStep2_STGridRepN_pin
#check bandStep2_STNewKLKAt_pin
#check bandStep2_STNewKLK_pin
#check Step2Kern_Theta_comm_pin
#check Step2Kern_Mss_BA_pin
#check Step2Kern_thetaKer_BA_pin
#check Step2Kern_BAKsolve_form_pin
#check Step2Kern_uKer_BA_pin
#check Step2Kern_UN_BA_pin
#check stNewKLKAtgL'_of_pin
#check stNewKLKAtgL'_holds_pin
#check stNewKLKgL'_of_pin
#check newKLKGenHyp_band_pin
#check stNewKLKgL_of_primed_pin
#check stK2decaygL_of_primed_pin

/-! ## 8. Compiled nonempty instances at `d = 3`

The merged preflight sequence `sz0` (`L_n = 4(n+1)`, `W_n = (2(n+1))^5`, `lam_n = (2(n+1))^{-6}`; `n = 0`: `L = 4`, `W = 32`,
`lam = 1/64`, `N = 2097152`).  The hypotheses of an `example` are the pins of this file (the targets of the ticket, unproved at
the probe step); every deterministic hypothesis is discharged at the concrete data, and no `N = 0`, empty index set or `False`
premise occurs.
* Three `rfl` facts of (a): `cycProd`, `STthetaOpg = ThetaN` at `k = 2`, the merged generic kernels at `SB` are the band kernels.
* (b) at the band: `E ≡ 0` (`m = i`), all four charge pairs, `k = 3` loops with `σ` arbitrary; `kron` hypothesis discharged.
* (b) the ten bridges at `bandStep2Mat sz0 (STflowE z0)` (window `[0, 1/16]`, a grid of `8` steps).
* (c) at BA: `sz0` along `zSeq`, `n = 0`, `S = 1`, `M^{(B)} = BAMB` not diagonal, `Im m > 0`; the cut (`baKsolve`) at the same datum.
* (e) at the band (`κ = 𝔡 = 1/10`, `δ₀ = 1/20`) and pointwise (`n = 0`, `E = 0`, `u = 1/32`, `D = 1`, `ℓ = 2`, `H = 0`).
* G1: `STNewKLK d` through the generic route and the bridge.  BAT-F2: `STK2decay d` through `STK2decaygL'` and the bridge. -/

section Inst

open RBM.Gauss.SizesInst RBM.Gauss.InductionDefsInst

/-- Two `rfl` facts of (a): `cycProd (fun i => m_{σ_i}) i = m_{σ_i} m_{σ_{i+1}}` ((b) written out), and `STthetaOpg` is
`Step2Gen_ThetaN` at `k = 2` (slot 0 has `(σ₀, σ₁)`, slot 1 has `(σ₁, σ₀)`). -/
example (E : ℝ) {k : ℕ} (σ : Fin k → Bool) (i : Fin k) :
    cycProd (fun i => mSigma E (σ i)) i = mSigma E (σ i) * mSigma E (σ (finRotate k i)) := rfl

example {d : ℕ} {sz : Sizes d} (Cm : Step2Mat sz) (n : ℕ) (u : ℝ) (σ : Fin 2 → Bool)
    (A : (Fin 2 → Zd d (sz.L n)) → ℂ) (a : Fin 2 → Zd d (sz.L n)) :
    STthetaOpg Cm n u σ A a = Step2Gen_ThetaN Cm.toFlowFM n σ u A a := rfl

/-- The merged generic kernels at `S = SB` are the merged band kernels of `Kernel/Evolution.lean` (`rfl`): the "current ones" of
(b) are the band kernels, which the redefinition does not touch. -/
example (d L : ℕ) [NeZero L] (g : ℝ) (μ : ℂ) (s t : ℝ) {k : ℕ} (m : Fin k → ℂ) (A : (Fin k → Zd d L) → ℂ) :
    RBM.BA.Step2Gen_thetaKer (SB d L g) μ t = RBM.thetaKer d L g μ t ∧
    RBM.BA.Step2Gen_uKer (SB d L g) μ s t = RBM.uKer d L g μ s t ∧
    RBM.BA.Step2Gen_ThetaN (SB d L g) m t A = RBM.ThetaN d L g m t A ∧
    RBM.BA.Step2Gen_UN (SB d L g) m s t A = RBM.UN d L g m s t A := ⟨rfl, rfl, rfl, rfl⟩

/-- The band block matrix `Bm = m(0) · 1`, `m(0) = i`, at `sz0`, `n = 0`: the band `M = m I` is `Bm ⊗ I_{W^d}`. -/
def Bm0 : Matrix (Zd 3 (sz0.L 0)) (Zd 3 (sz0.L 0)) ℂ := Matrix.of fun a b => if a = b then mE 0 else 0

/-- **(b) at one band size**: `sz0` (`L = 4`, `W = 32`, `lam = 1/64`, `N = 2097152`), `E ≡ 0` (`m = i`, `‖m(σ) m(σ')‖ = 1`),
all four charge pairs; the `kron` hypothesis of `Step2Kern_Mss_of_kron` is discharged (`split_injective`), and the two routes to
`M^{(σσ')}` (`kron`, `band`) agree. -/
example (hkr : Step2Kern_Mss_of_kron_pin) (hMb : Step2Kern_Mss_band_pin) (hTb : Step2Kern_thetaKer_band_pin)
    (hUb : Step2Kern_uKer_band_pin) (hTN : Step2Kern_ThetaN_band_pin) (hUN : Step2Kern_UN_band_pin) :
    (∀ σ σ' : Bool, ‖mSigma 0 σ * mSigma 0 σ'‖ = 1 ∧
      Step2Kern_Mss (bandFM sz0 fun _ => (0 : ℝ)) 0 σ σ' = (mSigma 0 σ * mSigma 0 σ') • 1 ∧
      Step2Kern_Mss (bandFM sz0 fun _ => (0 : ℝ)) 0 σ σ' =
        Matrix.of fun a b => Step2Kern_Bsig Bm0 σ b a * Step2Kern_Bsig Bm0 σ' a b) ∧
    (∀ σ σ' : Bool, (Matrix.of fun a b => Step2Kern_Bsig Bm0 σ b a * Step2Kern_Bsig Bm0 σ' a b) =
      (mSigma 0 σ * mSigma 0 σ') • (1 : Matrix (Zd 3 (sz0.L 0)) (Zd 3 (sz0.L 0)) ℂ)) ∧
    (∀ (σ σ' : Bool) (t : ℝ), Step2Gen_thetaKer (bandFM sz0 fun _ => (0 : ℝ)) 0 σ σ' t =
      RBM.thetaKer 3 (sz0.L 0) (sz0.lam 0) (mSigma 0 σ * mSigma 0 σ') t) ∧
    (∀ (σ σ' : Bool) (s t : ℝ), Step2Gen_uKer (bandFM sz0 fun _ => (0 : ℝ)) 0 σ σ' s t =
      RBM.uKer 3 (sz0.L 0) (sz0.lam 0) (mSigma 0 σ * mSigma 0 σ') s t) ∧
    (∀ (σ : Fin 3 → Bool) (t : ℝ) (A : (Fin 3 → Zd 3 (sz0.L 0)) → ℂ),
      Step2Gen_ThetaN (bandFM sz0 fun _ => (0 : ℝ)) 0 σ t A =
        RBM.ThetaN 3 (sz0.L 0) (sz0.lam 0) (fun i => mSigma 0 (σ i)) t A) ∧
    (∀ (σ : Fin 3 → Bool) (s t : ℝ) (A : (Fin 3 → Zd 3 (sz0.L 0)) → ℂ),
      Step2Gen_UN (bandFM sz0 fun _ => (0 : ℝ)) 0 σ s t A =
        RBM.UN 3 (sz0.L 0) (sz0.lam 0) (fun i => mSigma 0 (σ i)) s t A) := by
  have hker : ∀ x y : Idx 3 (sz0.L 0) (sz0.W 0), (bandFM sz0 fun _ => (0 : ℝ)).M 0 x y =
      Bm0 (split 3 (sz0.L 0) (sz0.W 0) x).1 (split 3 (sz0.L 0) (sz0.W 0) y).1 *
        (if (split 3 (sz0.L 0) (sz0.W 0) x).2 = (split 3 (sz0.L 0) (sz0.W 0) y).2 then 1 else 0) := by
    intro x y
    by_cases hxy : x = y
    · subst hxy
      simp [bandFM, Bm0]
    · by_cases h1 : (split 3 (sz0.L 0) (sz0.W 0) x).1 = (split 3 (sz0.L 0) (sz0.W 0) y).1
      · have h2 : ¬ (split 3 (sz0.L 0) (sz0.W 0) x).2 = (split 3 (sz0.L 0) (sz0.W 0) y).2 := fun h2 =>
          hxy (split_injective 3 (sz0.L 0) (sz0.W 0) (Prod.ext h1 h2))
        simp [bandFM, Bm0, hxy, h2]
      · simp [bandFM, Bm0, hxy, h1]
  refine ⟨fun σ σ' => ⟨?_, hMb 3 sz0 _ 0 σ σ', hkr 3 sz0 _ 0 Bm0 hker σ σ'⟩, ?_, fun σ σ' t => hTb 3 sz0 _ 0 σ σ' t,
    fun σ σ' s t => hUb 3 sz0 _ 0 σ σ' s t, fun σ t A => hTN 3 sz0 _ 0 3 σ t A, fun σ s t A => hUN 3 sz0 _ 0 3 σ s t A⟩
  · rw [norm_mul, norm_mSigma (by norm_num), norm_mSigma (by norm_num), mul_one]
  · intro σ σ'
    ext a b
    by_cases h : a = b
    · subst h
      cases σ <;> cases σ' <;> simp [Step2Kern_Bsig, Bm0, mSigma]
    · cases σ <;> cases σ' <;> simp [Step2Kern_Bsig, Bm0, mSigma, h, Matrix.one_apply, Ne.symm h]

/-- **(b) the ten bridges at the band instance** `bandStep2Mat sz0 (STflowE z0)` (the merged `sz0`, `z0`, window
`[0, 1/16]`, a grid of `8` steps, `n = 0`): every bridge that stops being `Iff.rfl` is applied at concrete data. -/
example (h1 : bandStep2_STthetaOp_pin) (h2 : bandStep2_STgDrift_pin) (h3 : bandStep2_STgDriftN_pin)
    (h4 : bandStep2_STeeUM_pin) (h5 : bandStep2_STGridMartAt_pin) (h6 : bandStep2_STGridMart_pin)
    (h7 : bandStep2_STGridRepNAt_pin) (h8 : bandStep2_STGridRepN_pin) (h9 : bandStep2_STNewKLKAt_pin)
    (h10 : bandStep2_STNewKLK_pin) (A : (Fin 2 → Zd 3 (sz0.L 0)) → ℂ)
    (H : Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ) (ω : PathΩ sz0) :=
  And.intro (h1 3 sz0 (STflowE z0) 0 (1 / 16) ![true, false] A ![0, 0]) <|
  And.intro (h2 3 sz0 (STflowE z0) sInst tInst (fun _ => 8) 0 ![true, false] ![0, 0] 0 ω) <|
  And.intro (h3 3 sz0 (STflowE z0) sInst tInst (fun _ => 8) 0 3 ![true, false, true] ![0, 0, 0] 0 ω) <|
  And.intro (h4 3 sz0 (STflowE z0) 0 0 (1 / 16) H 3 ![true, false, true] ![0, 0, 0]) <|
  And.intro (h5 3 0) <| And.intro (h6 3) <| And.intro (h7 3 3 0) <| And.intro (h8 3) <|
  And.intro (h9 3 (1 / 10) (1 / 10) 1 1) (h10 3)

end Inst

section InstBA

open RBM.Gauss.SizesInst RBM.BA.FlowPinsInst RBM.BA.EKPinsInst

/-- `M^{(B)}` of the BA flow of `sz0` at `n = 0` (`g₀ = gI`, `E = EI`, `m = mI` of `EKPinsInst`): `Im m > 0`, `L = 4`, `W = 32`,
`g₀ ≤ 1/64`; `M^{(B)} = (g₀ Ψ - (E + m))⁻¹` is not diagonal. -/
abbrev BI : Matrix (Zd 3 (sz0.L 0)) (Zd 3 (sz0.L 0)) ℂ := BAMB 3 (sz0.L 0) gI (EI : ℂ) mI

/-- **(c) at one BA size**: `sz0` along `zSeq`, `n = 0`, the carrier `baFMz sz0 zSeq` (`S = 1`, `M = BAMfine`); all four charge
pairs, `k = 3` loops with `σ = (+,+,-)` for `UN`.  The hypothesis `(E + m).im ≠ 0` is discharged by `BAmF_sz0_im_pos`; the `kron`
hypothesis of `Step2Kern_Mss_of_kron` by `BAMfine_sz0_kron`; `Bsig = BAMsigma` by `rfl`. -/
example (hkr : Step2Kern_Mss_of_kron_pin) (hMBA : Step2Kern_Mss_BA_pin) (hTBA : Step2Kern_thetaKer_BA_pin)
    (hKs : Step2Kern_BAKsolve_form_pin) (hUBA : Step2Kern_uKer_BA_pin) (hNBA : Step2Kern_UN_BA_pin) :
    0 < mI.im ∧
    (∀ σ σ' : Bool, Step2Kern_Mss (baFMz sz0 zSeq) 0 σ σ' = BAMss 3 (sz0.L 0) BI σ σ' ∧
      Step2Kern_Mss (baFMz sz0 zSeq) 0 σ σ' =
        (Matrix.of fun a b => Step2Kern_Bsig BI σ b a * Step2Kern_Bsig BI σ' a b) ∧
      Step2Kern_Bsig BI σ = BAMsigma 3 (sz0.L 0) BI σ) ∧
    (∀ (σ σ' : Bool) (t : ℝ), Step2Gen_thetaKer (baFMz sz0 zSeq) 0 σ σ' t =
      BATheta 3 (sz0.L 0) gI EI mI t σ σ' * BAMss 3 (sz0.L 0) BI σ σ') ∧
    (∀ (t : ℝ) (σ : Bool × Bool) (a₁ a₂ : Zd 3 (sz0.L 0)),
      (((sz0.W 0 : ℕ) : ℂ) ^ 3)⁻¹ * Step2Gen_thetaKer (baFMz sz0 zSeq) 0 σ.1 σ.2 t a₁ a₂ =
        (((sz0.W 0 : ℕ) : ℂ) ^ 3)⁻¹ * (BATheta 3 (sz0.L 0) gI EI mI t σ.1 σ.2 * BAMss 3 (sz0.L 0) BI σ.1 σ.2) a₁ a₂) ∧
    (∀ (σ σ' : Bool) (s t : ℝ), Step2Gen_uKer (baFMz sz0 zSeq) 0 σ σ' s t = BAuKer 3 (sz0.L 0) gI EI mI s t σ σ') ∧
    (∀ (σ : Fin 3 → Bool) (s t : ℝ) (A : (Fin 3 → Zd 3 (sz0.L 0)) → ℂ),
      Step2Gen_UN (baFMz sz0 zSeq) 0 σ s t A = BAUN 3 (sz0.L 0) gI EI mI σ s t A) := by
  have hIm : (((BAflowEs sz0 zSeq 0 : ℝ) : ℂ) + BAmF sz0 (BAflowLam0 sz0 zSeq) (BAflowEs sz0 zSeq) 0).im ≠ 0 := by
    simpa using (BAmF_sz0_im_pos 0).ne'
  have hker : ∀ x y : Idx 3 (sz0.L 0) (sz0.W 0), (baFMz sz0 zSeq).M 0 x y =
      BI (split 3 (sz0.L 0) (sz0.W 0) x).1 (split 3 (sz0.L 0) (sz0.W 0) y).1 *
        (if (split 3 (sz0.L 0) (sz0.W 0) x).2 = (split 3 (sz0.L 0) (sz0.W 0) y).2 then 1 else 0) := by
    intro x y
    change BAMfine sz0 (BAflowLam0 sz0 zSeq) (BAflowEs sz0 zSeq) 0 x y = _
    rw [BAMfine_sz0_kron 0]
    simp [Matrix.submatrix_apply, Matrix.kroneckerMap_apply, splitEquiv, Matrix.one_apply, BI]
  refine ⟨BAmF_sz0_im_pos 0, fun σ σ' => ⟨hMBA 3 sz0 _ _ 0 hIm σ σ', hkr 3 sz0 _ 0 BI hker σ σ', rfl⟩,
    fun σ σ' t => hTBA 3 sz0 _ _ 0 hIm σ σ' t, fun t σ a₁ a₂ => hKs 3 sz0 _ _ 0 hIm t σ a₁ a₂,
    fun σ σ' s t => hUBA 3 sz0 _ _ 0 hIm σ σ' s t, fun σ s t A => hNBA 3 sz0 _ _ 0 hIm 3 σ s t A⟩

/-- `Θ_t(M^{(σσ')})` commutes with `M^{(σσ')}` at the BA datum (the one lemma that turns `Mss Θ` into the `Θ Mss` of `BAKsolve`). -/
example (hc : Step2Kern_Theta_comm_pin) (σ σ' : Bool) (t : ℝ) :
    BAMss 3 (sz0.L 0) BI σ σ' * Step2Gen_Theta (BAMss 3 (sz0.L 0) BI σ σ') t =
      Step2Gen_Theta (BAMss 3 (sz0.L 0) BI σ σ') t * BAMss 3 (sz0.L 0) BI σ σ' := hc _ _

/-- **(c), the cut at BA**: the merged `baKsolve` (`BA/KTreeRep.lean:1699`) at the flow datum gives a solution `K` of the
tree equations whose two-loop value is `W^{-d}` times the derived kernel `thetaKer` (with `Step2Kern_thetaKer_BA`). -/
example (hTBA : Step2Kern_thetaKer_BA_pin) :
    ∃ K : ℝ → LoopIdx (Zd 3 (sz0.L 0)) → ℂ,
      IsKLoopS 3 (sz0.L 0) (sz0.W 0) (1 : Matrix (Zd 3 (sz0.L 0)) (Zd 3 (sz0.L 0)) ℂ) (PropSpin mI)
        (BAMLoop 3 (sz0.L 0) (sz0.W 0) (BAMsigma 3 (sz0.L 0) BI)) (Set.Ico (0 : ℝ) 1) K ∧
      ∀ t ∈ Set.Ico (0 : ℝ) 1, ∀ (σ : Bool × Bool) (a₁ a₂ : Zd 3 (sz0.L 0)),
        K t ⟨[σ.1, σ.2], [a₁, a₂]⟩ =
          (((sz0.W 0 : ℕ) : ℂ) ^ 3)⁻¹ * Step2Gen_thetaKer (baFMz sz0 zSeq) 0 σ.1 σ.2 t a₁ a₂ := by
  have hIm : (((BAflowEs sz0 zSeq 0 : ℝ) : ℂ) + BAmF sz0 (BAflowLam0 sz0 zSeq) (BAflowEs sz0 zSeq) 0).im ≠ 0 := by
    simpa using (BAmF_sz0_im_pos 0).ne'
  obtain ⟨K, hK, hK2⟩ := baKsolve 3 1 (1 / 2) one_pos (by norm_num) (sz0.L 0) (sz0.three_le_L 0) (sz0.W 0) gI gI_pos
    (gI_le.trans (by norm_num)) EI mI hrI
  refine ⟨K, hK, fun t ht σ a₁ a₂ => ?_⟩
  rw [hK2 t ht σ a₁ a₂]
  exact congrArg ((((sz0.W 0 : ℕ) : ℂ) ^ 3)⁻¹ * ·) (congrFun (congrFun (hTBA 3 sz0 _ _ 0 hIm σ.1 σ.2 t) a₁) a₂).symm

end InstBA

section InstE

open RBM.Gauss.SizesInst

/-- The band carrier at `sz0`, `E ≡ 0` (`m = i`). -/
abbrev Cm0 : Step2Mat sz0 := bandStep2Mat sz0 (fun _ => 0)

/-- The matrix `H = 0` at `sz0`, `n = 0`. -/
abbrev H0 : Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ := 0

/-- **(e) at the band**: `d = 3`, `κ = 𝔡 = 1/10`, `δ₀ = 1/20`; F5-F9 over the new kernel (`newKLKGenHyp_band_pin`) feed
`stNewKLKAtgL'_of_pin`. -/
example (hband : newKLKGenHyp_band_pin) (hof : stNewKLKAtgL'_of_pin) :
    ∃ C : ℝ, 0 < C ∧ STNewKLKAtgL' 3 (1 / 10) (1 / 10) C (1 / 20) (fun sz E => bandStep2Mat sz E) := by
  obtain ⟨C, hC, h⟩ := hof 3 (by norm_num) (1 / 10) (1 / 10) (by norm_num) _
    (hband 3 (by norm_num) (1 / 10) (1 / 10) (by norm_num) (by norm_num))
  refine ⟨C, hC, ?_⟩
  have e : (1 / 10 : ℝ) / 2 = 1 / 20 := by norm_num
  rw [e] at h
  exact h

/-- **(e), pointwise** (`d = 3`, `sz0`, `n = 0`, `E = 0`, `u = 1/32`, `D = 1`, `ℓ = 2` so that the indicator `1_{ℓ ≥ 1}` is on,
`H = 0`, so `‖G_u - M‖_max = u/(1-u) = 1/31 ≤ 1/20 = δ₀` and `G_u ≠ M`): the two bounds of `STNewKLKAtgL'` with the new
`STthetaOpg`, every deterministic hypothesis discharged. -/
example (hband : newKLKGenHyp_band_pin) (hof : stNewKLKAtgL'_of_pin) :
    ∃ C : ℝ, 0 < C ∧ ∀ (σ : Fin 2 → Bool) (a : Fin 2 → Zd 3 (sz0.L 0)),
    ‖STthetaOpg Cm0 0 (1 / 32) σ (STLKMg Cm0 0 (1 / 32) H0 σ) a‖ ≤
        C / (1 - 1 / 32) * STJhatMg Cm0 0 1 2 (1 / 32) H0 * STprof sz0 0 (1 / 32) 1 2 (a 0) (a 1) ∧
      ‖STELKLKMg Cm0 0 (1 / 32) H0 σ a‖ ≤
        C / (1 - 1 / 32) * (STJhatMg Cm0 0 1 2 (1 / 32) H0 +
          STJhatMg Cm0 0 1 2 (1 / 32) H0 ^ 2 * (if 1 ≤ (2 : ℝ) then 1 else 0)) *
          STprof sz0 0 (1 / 32) 1 2 (a 0) (a 1) := by
  obtain ⟨C, hC, h⟩ := hof 3 (by norm_num) (1 / 10) (1 / 10) (by norm_num) _
    (hband 3 (by norm_num) (1 / 10) (1 / 10) (by norm_num) (by norm_num))
  have hlam : 0 < sz0.lam 0 := by simp [sz0]
  have hlam' : sz0.lam 0 ≤ ((1 : ℝ) / 10)⁻¹ := by
    have : sz0.lam 0 = 1 / 64 := by norm_num [sz0]
    rw [this]; norm_num
  have hL4 : (2 : ℝ) ≤ ((sz0.L 0 : ℕ) : ℝ) := by norm_num [sz0]
  have hIm : (1 / 10 : ℝ) ≤ ((bandStep2Mat sz0 fun _ => 0).m 0).im := by
    change (1 / 10 : ℝ) ≤ (mE 0).im
    rw [nkl_mE_zero]; norm_num
  refine ⟨C, hC, fun σ a => ?_⟩
  exact h sz0 0 0 (1 / 32) 1 2 hlam hlam' hIm (by norm_num) (by norm_num) zero_le_one (by norm_num) hL4 0
    Matrix.isHermitian_zero
    (fun x y => (nkl_STGMM_zero sz0 0 (by norm_num) (by norm_num) x y).trans (by norm_num)) σ a

/-- **G1** (target 7): the merged band pins re-derived through the generic route and the bridges: `STNewKLK d`. -/
example (d : ℕ) (hband : newKLKGenHyp_band_pin) (hmain : stNewKLKgL'_of_pin) (hprim : stNewKLKgL_of_primed_pin)
    (hbr : bandStep2_STNewKLK_pin) : STNewKLK d :=
  (hbr d).mpr (hprim d _ (hmain d _ fun hd κ 𝔡 hκ h𝔡 => hband d hd κ 𝔡 hκ h𝔡)
    fun _ _ hκ _ _ _ _ _ _ hE => Ind.half_le_mE_im hκ.le hE)

/-- **BAT-F2** (target 6) at the band: the primed pin `STK2decaygL'` at `bandStep2Mat`, the corollary and the merged bridge
`bandStep2_STK2decay` (`Iff.rfl`) give the band pin `STK2decay d`; the domain fact is `Ind.half_le_mE_im`. -/
example (d : ℕ) (hprim : STK2decaygL' d (fun sz E => bandStep2Mat sz E)) (hof : stK2decaygL_of_primed_pin) :
    STK2decay d :=
  (bandStep2_STK2decay d).mpr (hof d _ hprim fun _ _ hκ _ _ _ _ _ _ hE => Ind.half_le_mE_im hκ.le hE)

end InstE

end RBM.BA.T2414Pins
