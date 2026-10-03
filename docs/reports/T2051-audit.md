Auditor model: claude-opus-5-5

# T2051 audit (round 1) — Sat Oct  3 15:37:29 UTC 2026
Branch `t/T2051` `d8f8bd3` (base `86368fa`; main `31476de`); worktree `RBM3D-wt/T2051-audit1` (detached).

## 1. Scope, build, hygiene, axioms
```
$ git diff --name-only main...t/T2051
RBM3D/Graph/LWPsi.lean
$ lake build RBM3D.Graph.LWPsi 2>&1 | grep -v ^trace | grep -E "error|warning|sorry|Build"
Build completed successfully (3313 jobs).
$ grep -nE "sorry|admit|native_decide|^axiom|^\s*axiom " RBM3D/Graph/LWPsi.lean; echo "hygiene grep exit $?"
hygiene grep exit 1
$ lake env lean ax.lean   # 41 lines: 14 RBM.Gauss.Sizes.* (defs + targets), 4 RBM.tail*_regime*, 23 RBM.Gauss.LWPsiInst.inst_*
$ ... | sed -E 's/^[^ ]* : //' | sort | uniq -c
  41 [propext, Classical.choice, Quot.sound]
$ lake build RBM3D 2>&1 | grep -E "error|Build completed"
Build completed successfully (3777 jobs).
$ lake env lean pre.lean; echo exit $?   # import RBM3D / import RBM3D.Graph.LWPsi / #assert_rbm_axioms
exit 0
axiom audit: 1963 theorems, 834 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
premises found by scanning: 47 (borrowed 2, owed 32, structural 13).
```
Imports (:6-9): `RBM3D.Induction.Defs`, `.Defs.Tail`, `.Defs.Params`, Mathlib (as pinned; no `import RBM3D`). `RBM3D/Test/Axioms.lean` untouched (pre-check exit 0). No frozen signature touched (one new file).
Name clash of all 56 public `theorem`/`def` names against current `main` (`git grep -nE "(def|theorem|lemma|abbrev) NAME\b" main`): 0 hits.

## 2. Target 1 — copied definitions (script diff against `eeda441:RBM3D/Probe/T2040Graphs.lean`)
```
$ bash cmp.sh   # diff of line ranges, docstrings included
LWWindow probe:918-920 vs LWPsi:46-48 diff=identical
LWClass probe:928-932 vs LWPsi:50-54 diff=identical
LWPsiRel probe:934-940 vs LWPsi:56-62 identical
LWPsiAll probe:1076-1078 vs LWPsi:65-67 diff=identical
$ diff <(probe :970-971 lambda body) <(LWPsi :74-75 LWPhiB body)
< Bparam d (sz.L n) (sz.lam n) (t n) (min ⌊r⌋₊ (K n))) ^ (1 / 2 : ℝ)) →
> Bparam d (sz.L n) (sz.lam n) (t n) (min ⌊r⌋₊ (K n))) ^ (1 / 2 : ℝ)
$ diff <(sed -n 1200,1202p probe.lean) <(sed -n 303,305p LWPsi.lean)
LWPsiAll.shift statement probe:1200-1202 = LWPsi:303-305 (identical)
```
The only difference in the B-class body is the trailing `) →` of the probe's binder (context, not term).
The probe has no *definition* `classB` (probe :1939 `theorem classB` is about `ΦB` at `sz0`, `c₀ = 1`);
the B class used by `LWtermB` is the lambda at :970-973, now the named `LWPhiB` (same term). **PASS.**

## 3. Target 2(a) — `(eq:Psi)` for the B class (`3_5:389-392`)
Paper: `∃ C₁,C₂ > 1`, `∀ C > 1`: `Ψ_t(0) ≍ Ψ_t(ℓ)` (`0 ≤ ℓ ≤ C`), `Ψ_t(ℓ₁)/Ψ_t(ℓ₂) ≤ C₁(ℓ₂/ℓ₁)^{C₂}` (`ℓ₂ ≥ ℓ₁ ≥ 1`),
plus monotonicity; B class `Ψ_t(r) = (W^{-c₀}B_{t,r∧K})^{1/2}`. Lean (extracted, file :220-221, :242-243, :312-314):
```
theorem LWPhiB_psiRel (hd : 2 ≤ d) (c₀ : ℝ) (K : ℕ → ℕ) (t : ℕ → ℝ) :
    LWPsiRel ((2 : ℝ) ^ d) (d : ℝ) (fun C => Real.sqrt ((C + 1) ^ (d - 2))) (LWPhiB sz c₀ K t)
theorem LWPhiB_psiRel_three (hd : d = 3) (c₀ : ℝ) (K : ℕ → ℕ) (t : ℕ → ℝ) :
    LWPsiRel 2 2 (fun C => Real.sqrt ((C + 1) ^ (d - 2))) (LWPhiB sz c₀ K t)
theorem LWPhiB_shift (hd : 2 ≤ d) (c₀ : ℝ) (K : ℕ → ℕ) (t : ℕ → ℝ) {c : ℝ} (hc : 0 < c) :
    ∃ Kc : ℝ, 0 < Kc ∧ ∀ᶠ n in atTop, ∀ r : ℝ, 0 ≤ r →
      LWPhiB sz c₀ K t n (c * r) ≤ Kc * LWPhiB sz c₀ K t n r
theorem LWPsiAll.shift ... (h : LWPsiAll sz ε₀ C₁ C₂ C₃ Cc Φ) {c : ℝ} (hc : 0 < c) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ n in atTop, ∀ r : ℝ, 0 ≤ r → Φ n (c * r) ≤ K * Φ n r
```
- Constants before the sequence (`∃ Kc` before `∀ᶠ n`); `C₁ = 2^d`, `C₂ = d`; `(2,2)` at `d = 3` as the ticket asks. No
  hypothesis on `t, g, L, W, K, c₀`; `2 ≤ d` weaker than `3 ≤ d`; merged `Bparam` (`Defs/Params.lean:36`). **PASS.**

## 4. Target 2(b) — the window (T2040a)
```
theorem LWWindow_max {ε₀ : ℝ} (hε : ε₀ ≤ (d : ℝ) / 2) {Φ₀ : ℕ → ℝ}
    (h : ∀ᶠ n in atTop, Φ₀ n ≤ ((sz.W n : ℕ) : ℝ) ^ (-ε₀)) :
    LWWindow sz ε₀ (fun n => max (((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2)) (Φ₀ n))
theorem LWWindow_max_Bctl {ε₀ : ℝ} (hε : ε₀ ≤ (d : ℝ) / 2) (t : ℕ → ℝ)
    (h : ∀ᶠ n in atTop, sz.Bctl n (t n) ≤ ((sz.W n : ℕ) : ℝ) ^ (-2 * ε₀)) :
    LWWindow sz ε₀ (fun n => max (((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2)) (Real.sqrt (sz.Bctl n (t n))))
theorem LWClass_B {ε₀ c₀ Λ : ℝ} (K : ℕ → ℕ) (t : ℕ → ℝ) (hc₀ : c₀ ≤ (d : ℝ))
    (hg : ∀ᶠ n in atTop, 0 < sz.lam n ∧ sz.lam n ≤ Λ) (ht : ∀ᶠ n in atTop, 0 ≤ t n ∧ t n ≤ 1)
    (hup : ∀ᶠ n in atTop, ((sz.W n : ℕ) : ℝ) ^ (-c₀) * Bparam d (sz.L n) (sz.lam n) (t n) 0 ≤
      ((sz.W n : ℕ) : ℝ) ^ (-2 * ε₀)) :
    LWClass sz ε₀ (Real.sqrt (1 + Λ ^ 2)) (LWPhiB sz c₀ K t)
theorem LWPsiMax_asymp (h : LWClass sz ε₀ C₃ Φ) : ∀ᶠ n, Φ n 0 ≤ max (W^{-d/2}) (Φ n 0) ∧ max .. ≤ max 1 C₃ * Φ n 0
theorem LWPhiB_psiAll (hd : 2 ≤ d) ... (hε : 0 < ε₀) (hc₀ ...) (hg ...) (ht ...) (hup ...) :
    LWPsiAll sz ε₀ ((2 : ℝ) ^ d) (d : ℝ) (Real.sqrt (1 + Λ ^ 2)) (fun C => √((C+1)^(d-2))) (LWPhiB sz c₀ K t)
$ grep -n -A1 "def Bctl" RBM3D/Defs/Sizes.lean
214:def Bctl (n : ℕ) (t : ℝ) : ℝ :=
215-  (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * Bparam d (sz.L n) (sz.lam n) t 0
```
- `Bctl = W^{-d}B_{t,0}`, so `LWWindow_max_Bctl` is the window for `Ψ_t = max(W^{-d/2}, (W^{-d}B_{t,0})^{1/2})` (T2040a).
  Lower side unconditional; upper side `Ψ_t ≤ W^{-ε₀}` is a data hypothesis. That is necessary, not hidden:
  `W^{-d}B_{t,0} ≥ (W^dL^d|1-t|)⁻¹ > 1` when `1-t < N⁻¹`, and the paper's lemma (`3_5:386`) itself
  assumes the window. Limit check at concrete data: `upper_core` proves it at `sz0` for all `n` (§6).
- B class: `C₃ = (1+Λ²)^{1/2}` independent of `W, L, K, t`; the ticket's `c₀ ≤ d` is the hypothesis. `hg`, `ht`
  are data conditions of the paper (`g ∈ (0,Λ]`, `t ∈ [0,1]`). **PASS.**

## 5. Target 2(c) — `W^{-d}𝒯̃ ≍ [s𝒯]²` for `r ≤ L` (T2040k; `7_8:20-24`)
```
theorem tailT_regime1_bounds {d L : ℕ} {W g t : ℝ} (hd : 2 ≤ d) (hL : 1 ≤ (L : ℝ)) (ht : t < 1)
    (hW : 0 < W) (hgt : g ^ 2 / (L : ℝ) ^ 2 ≤ 1 - t) {r : ℝ} (hr0 : 0 ≤ r) (hrL : r ≤ L) :
    sfT d L W g t r ^ 2 ≤ (W ^ d)⁻¹ * tailT d L g t r ∧
      (W ^ d)⁻¹ * tailT d L g t r ≤ (1 + 2 ^ (d - 1)) * sfT d L W g t r ^ 2
theorem tailW_regime1_bounds ... (hℓ0 : 0 ≤ ℓ) (hℓL : ℓ ≤ L) {r : ℝ} (hr : 0 ≤ r) :
    (1/2) * (sfT .. (min r ℓ) ^ 2 + (W ^ d)⁻¹ * W ^ (-D)) ≤ (W ^ d)⁻¹ * tailW d L g t ℓ W D r ∧
      (W ^ d)⁻¹ * tailW d L g t ℓ W D r ≤ (1 + 2 ^ (d - 1)) * (sfT .. (min r ℓ) ^ 2 + (W ^ d)⁻¹ * W ^ (-D))
theorem tailT_regime2_bounds {d L : ℕ} {g t : ℝ} (hg : 0 ≤ g) (ht : t < 1) (hL : 1 ≤ (L : ℝ))
    (h : 1 - t ≤ g ^ 2 / (L : ℝ) ^ 2) {r : ℝ} (hr0 : 0 ≤ r) (hrL : r ≤ L) :
    Real.exp (-1) * BparamR d L g t r ≤ tailT d L g t r ∧ tailT d L g t r ≤ BparamR d L g t r
theorem tailW_regime2_bounds ... : max (e⁻¹ BparamR (min r ℓ)) (W^-D) ≤ tailW .. ∧ tailW .. ≤ max (BparamR (min r ℓ)) (W^-D)
$ grep -n -A2 "def sfT" RBM3D/Kernel/PropT.lean
469:noncomputable def sfT (r : ℝ) : ℝ :=
470-  √((W ^ d)⁻¹) * √((g ^ 2 + |1 - t|)⁻¹) * √(((r + 1) ^ (d - 2))⁻¹)
471-    * exp (-(1 / 2) * √(r / ellT L g t))
```
- `sfT` equals the paper's `sT_t` (`7_8:24`); merged `tailT`, `tailW`, `BparamR` (`Defs/Tail.lean:44-53`).
- Regime `1-t > ĝ²/L²` (paper) is weakened to `≥` (stronger theorem). Regime `1-t ≤ ĝ²/L²`: comparison with
  `B_{t,r}` (T2040k's "W^-d T~ ≍ B for r ≤ L"); `[s𝒯]²` is not comparable there (zero mode). Constants explicit.
- `W^{-D}` → `W^{-d}W^{-D}` in the truncated form: proposed as new candidate **T2051a** (prove report (d)). **PASS.**

## 6. Compiled nonempty instances (`RBM.Gauss.LWPsiInst`, file :533-813; 23 `inst_*`, all compiled, axioms above)
Data: merged `sz0` (`d = 3`, `L_n = 4(n+1)`, `W_n = (2(n+1))^5`, `lam_n = (2(n+1))^{-6}`), `c₀ = 3`, `ε₀ = 1/5`,
`Λ = 1`, `K_n = L_n`; `tInst` (`Induction/Defs.lean:440`: `fun _ => 1 / 16`) and `tW n = 1 - W_n^{-2}`.
| Target | Instance(s) | hypotheses discharged |
|---|---|---|
| `LWPhiB_psiRel` | `inst_psiRel` (all `t,K`), `_tInst`, `_tW` | `2 ≤ 3` |
| `LWPhiB_psiRel_three` | `inst_psiRel_three_tInst/_tW` | `rfl : 3 = 3` |
| `LWPhiB_shift` | `inst_shift_tInst` (`c = 1/4, 2`), `inst_shift_tW` (`c = 1/2`) | `0 < c` |
| `LWPsiAll.shift` | `inst_shift_all_tInst` (`c=1/4`), `_tW` (`c=2`), on the proved `inst_psiAll_*` | all |
| `LWWindow_max_Bctl` | `inst_window_tInst/_tW` (`ε₀ = 1/5 ≤ 3/2`, `upper_core`, ∀ n) | all |
| `LWClass_B`, `LWPhiB_psiAll` | `inst_class_*`, `inst_psiAll_*` (`lam_pos`, `lam_le_64`, `tInst_ok`/`tW_ok`, `upper_core`) | all, ∀ n |
| `LWPsiMax_asymp` | `inst_asymp_tInst/_tW` (on `inst_class_*`) | all |
| `tailT/tailW_regime1_bounds` | `inst_tail1_*`, `inst_tailW1_*` at `r = 2`, `ℓ = 3`, `D = 1` (`hgt_tInst`, `hgt_tW`, `L_ge_4`) | all, ∀ n |
| `tailT/tailW_regime2_bounds` | `inst_tail2`, `inst_tailW2`: `n = 0` (`L = 4`, `g = 1/64`), `t = 1 - 2^{-17}` | all |
Nondegenerate: `N > 0`, `W ≥ 32`, `L ≥ 4`, `r = 2 ≤ L`, `ε₀ > 0`, no `False` premise, no large-witness trick.
Regime 2 cannot be instantiated at the ticket's two times (`hgt_tInst`, `hgt_tW` prove `1 - t ≥ g²/L²` ∀ n),
so its instance at a concrete `t` with `1-t = 2^{-17} ≤ 2^{-16} = g²/L²` is the correct substitute.

## 7. Hidden hypotheses, vacuity, cycles
- The four class predicates are `Prop` defs (verbatim pins); `LWPhiB` is a function def; no structure carries a
  hypothesis. `LWPsiAll.shift`/`LWPsiMax_asymp` take a class predicate as input and are instantiated with the
  proved `LWPsiAll`/`LWClass` of the B class (§6), so not vacuous.
- Dependencies are merged only (`Bparam`, `BparamR`, `tailT`, `tailW`, `sfT`, `ellT`, `Bctl`, `zeroMode_le_of_ge`,
  `exp_tail_ge`, `sz0`, `tInst`); no import of a target downstream file; no external hypothesis.

## 8. Paper deltas
- T2040a (window/`C₃`/`max`), h (monotonicity; proved here for B), k (regime split): cited (DECISIONS §24). New: T2051a.

## 9. Observations (no statement/instance/build/axiom/delta effect)
- O1. `LWClass_B` needs `c₀ ≤ d` (ticket's hypothesis); the paper's "in particular" says `c₀ > 0`. For `c₀ > d`
  the clause `W^{-d/2} ≲ Ψ_t(0)` of `(eq:Psi)` fails in general (`t = 1/16`: `Ψ_t(0) ≍ W^{-c₀/2}`). This is
  within T2040a's subject; the dispatcher may mention `c₀ ≤ d` when numbering T2040a.
- O2. `tailW_regime1/2_bounds` assume `ℓ ≤ L` (paper: `ℓ ≤ (log W)^{10}ℓ_t`, may exceed `L`). No loss for
  `r ≤ L`: `tailW` at `ℓ` and at `min ℓ L` agree there, and `tailT_regime*_bounds` cover `r ≤ L` directly.
- O3. `LWWindow_max` has no direct instance; it is applied at concrete data through `LWWindow_max_Bctl`
  (`Φ₀ = √Bctl` at `sz0`, `inst_window_*`). Unpinned public helpers in `RBM.Gauss.LWPsiInst` (`tW`, `lam_pos`,
  `L_ge_4`, `upper_core`, ...) are namespaced by the file stem (`LWPsiInst`), not prefixed; 0 clashes on main.

## Verdict
Target 1, 2(a), 2(b), 2(c): PASS. Ticket T2051: **PASS**. No dispatcher sign-off needed.
