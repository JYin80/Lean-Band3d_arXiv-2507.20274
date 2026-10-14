Auditor model: claude-opus-5-5

# T2502 row c — 1a-audit (W1 design gate, ticket answer (7))
Written: Wed Oct 14 07:47:08 UTC 2026 (`date -u`). Audit worktree `RBM3D-wt/T2502c-audit1a`, detached at `t/T2502c` = `0f0ad532` (base `bd5531ea`, on `main`). Scratch: `scratchpad/T2502c/audit1a/`.
Inputs: ticket `docs/tickets/T2502.md` (answer (7), W1 `:18`, family table row 14 `:60`, stop rules `:75`), report `docs/reports/T2502c-prove.md` (a), (a″), probe `RBM3D/Probe/T2502Pins.lean`, check `docs/tickets/checks/T2502-check.lean:332-341`, paper `6_Step6_two_loop.tex:12-21`, `1_2_Intro_model_result.tex:1256-1396`.

## 1. Probe recompile (own worktree)
```
$ cd RBM3D-wt/T2502c-audit1a && lake env lean RBM3D/Probe/T2502Pins.lean; echo "exit=$?"
@BATwistAvgLaw : {d : ℕ} → {sz : Sizes d} → FlowFM sz → Measure sz.SeqΩ → (ℕ → ℝ) → Prop
'RBM.BA.T2502c_band_W1fam' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.T2502c_ba_W1fam' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.T2502c_band_collapse' depends on axioms: [propext, Classical.choice, Quot.sound]
exit=0
$ git diff --stat main...HEAD
 RBM3D/Probe/T2502Pins.lean | 291 +++++++++++++++++++++++++++++++++++++++++++++
$ grep -cE "sorry|admit|native_decide|^axiom " RBM3D/Probe/T2502Pins.lean; wc -l RBM3D/Probe/T2502Pins.lean
0
     291 RBM3D/Probe/T2502Pins.lean          # answer (7): probe <= 300 lines
$ grep -rn "Probe.T2502Pins" RBM3D.lean; echo "root-import-hits=$?"
root-import-hits=1                           # no root import (never merged)
```

## 2. Numerics rerun (section (a) table and (a″) Monte Carlo)
```
$ python3 scratchpad/T2502c/inst.py > audit1a/inst.out; diff audit1a/inst.out scratchpad/T2502c/inst.out && echo INST_IDENTICAL
INST_IDENTICAL                               # all 13 lines of (a)(ii) reproduced verbatim
$ python3 scratchpad/T2502c/stein2.py
L=3 Wd=1 g=0.5 u=0.6: max|x|=0.0256 max|x-rhs|=2.14e-03 (std err 6.3e-04) max|x-wrong|=2.37e-01
L=3 Wd=2 g=0.5 u=0.6: max|x|=0.0064 max|x-rhs|=6.10e-04 (std err 2.9e-04) max|x-wrong|=2.42e-01
L=4 Wd=1 g=0.8 u=0.8: max|x|=0.1325 max|x-rhs|=2.57e-03 (std err 2.7e-03) max|x-wrong|=6.22e-01
```
Identical to the report. (Python with numpy; `python3 -I` fails with `No module named 'numpy'`, so run with the user site.)

## 3. No merged W1 text (re-checked on `main`)
```
$ git grep -n "Step2Gen_uKer" main -- RBM3D | grep -iE "≤ C|row|Cs"     # every same-row bound over a carrier
main:RBM3D/Chain/AzumaProxyGen.lean:529:  ... ‖Step2Gen_uKer C n (σ i) (σ (finRotate k i)) v w (a i) c‖ ≤ 1 + (1 - w)⁻¹
main:RBM3D/Chain/GridRepTailGen.lean:50: (K2) Σ_b ‖uKer_{v,w}(a,b)‖ ≤ (1 - v)/(1 - w)
main:RBM3D/BA/GridDriftBA.lean:396,427: (BA-specific, uKer - 1)
```
All carry the `(1-w)⁻¹` loss or are BA-specific: W1 (ii) has no merged generic text. W1 (i) has none either (drafts only, check `:332-341`). The gate of answer (7) applies.

## 4. D1 against the drafts (script diff; prefix `<` = check draft, `>` = probe)
```
$ diff draft.txt d1.txt          # check :332-341 vs probe :41-52, docstrings stripped
< def T2502_W1SelfConsDraft {d : ℕ} {sz : Sizes d} (C : FlowFM sz)
<     (H₀ : ∀ n, Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (E : ℕ → ℝ) : Prop :=
<   ∀ n, (H₀ n - ((E n : ℂ) + C.m n) • (1 : Matrix ...)) * Matrix.of (fun x y => C.M n x y) = 1
---
> def T2502c_W1i (C : FlowFM sz) (H₀ : ...) (g' E : ℕ → ℝ) (n : ℕ) : Prop :=
>   C.S n = SB d (sz.L n) (g' n) ∧
>   (H₀ n - ((E n : ℂ) + C.m n) • (1 : Matrix ...)) * Matrix.of (fun x y => C.M n x y) = 1 ∧
>   ∀ a : Zd d (sz.L n), (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * ∑ x ∈ Iblk d (sz.L n) (sz.W n) a, C.M n x x = C.m n
< def T2502_W1SameRowDraft {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (Cs : ℝ) : Prop :=
<   ∀ (n : ℕ) (σ : Bool) (s t : ℝ), 0 ≤ s → s ≤ t → t < 1 → ∀ a : Zd d (sz.L n),
---
> def T2502c_W1ii (C : FlowFM sz) (Cs : ℝ) : Prop :=
>   ∀ᶠ n in atTop, ∀ (σ : Bool) (s t : ℝ), 0 ≤ s → s ≤ t → t < 1 → ∀ a : Zd d (sz.L n),
```
Checks of the three changes:
- (c) block average `= C.m n`: needed. Paper `6:17` bounds `|𝔼 tr((G_u - M) E_a)|`; the pin `T2502_ExpAvgAtgL` (check `:218-222`) bounds `‖∫ C.L … - C.m n‖`; (c) is exactly the bridge `tr(M E_a) = m`. The ticket W1 (i) (`:18`) already demands it; the draft omitted it. Compiled counterexample to the draft alone: probe `:197-221` (exit 0 above).
- (a) `C.S n = SB d (L n) (g' n)`: needed. `CltRepg` (`Chain/CltGen:84-92`) fixes `μ = seqP (sz.withLam g')` but says nothing of `C.S`, while `Step2Gen_uKer` (`Chain/Step2Gen:192-193`) is `(1 - s X) Θ_t(X)`, `X = Mss * C.S n`. Without (a) the Stein covariance and the inverted kernel are unrelated.
- (ii) `∀ n` → `∀ᶠ n`: forced. Both sources need the window `0 < g ≤ Λ`:
```
Evolution/XiPins:308   ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → g ≤ Λ → ∀ m : ℂ, ‖m‖ = 1 → κ ≤ m.im → …
BA/EKPins:263          ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → g ≤ Λ → ∀ (E : ℝ) (m : ℂ), … BAReal d L g κ E m → …
BA/GreenSchur:72-73    BAflow_lam0_window … : ∀ᶠ n in atTop, 0 < BAflowLam0 sz z n ∧ BAflowLam0 sz z n ≤ 𝔡⁻¹
```
The target is a `PrecL` (eventual in `n`), so `∀ᶠ` costs nothing.
- Family text `T2502c_W1fam` (`:57-63`): `∃ Cs` after `(κ, ε, 𝔡)` and before `(𝔠, sz, z)` (table row 14 / "Pinned ∃" `:61`). It merges rows 9 and 14 into one `∃ (H₀, g', E)`. This is necessary: W1 (i) must hold at the `(H₀, g', E)` of `CltRepg`. It is a change to the family table, which is draft text.

## 5. Discharges and compiled nonempty instances (probe)
| text | band (`bandFM`, `H₀ = 0`, `g' = sz.lam`) | BA (`baFMz`, `H₀ = λ₀Ψ`, `g' = 0`) |
|---|---|---|
| (i)′ | `T2502c_band_W1i` `:88` (`|E n| ≤ 2`, every `n`) | `T2502c_ba_W1i` `:227` (every `BAFlow`, `0 < κ`, every `n`) |
| (ii)′ + family | `T2502c_band_W1fam` `:121` via `ekSameRow_holds`, `Step2Kern_uKer_band` | `T2502c_ba_W1fam` `:249` via `baEKSameRow_holds`, `Step2Kern_uKer_BA` |
| instance | `:270`, `d = 3`, `sz0`, `z0`, `flow_z0`, `(κ,ε,𝔠,𝔡) = (1/10,1/10,1/6,1/10)` | `:277`, `sz0`, `zSeq`, `flow_sz0`, exact type `baFMz sz0 zSeq`, `(1/2,1/10,1/6,1/10)` |
```
$ sed -n 260,268p RBM3D/Defs/Sizes.lean          # sz0: L n = 4(n+1), W n = (2(n+1))^5, lam n = (2(n+1))^-6
theorem sz0_values : sz0.L 0 = 4 ∧ sz0.W 0 = 32 ∧ sz0.size 0 = 2097152 ∧ sz0.lam 0 = 1 / 64
```
The instances are nondegenerate: no `N = 0`, the window is open, the flow premises are discharged by merged `flow_z0` / `flow_sz0`, and `Cs > 0` comes from the merged producers. Every deterministic premise is discharged. Answer (7)'s requirement "band and BA discharges at `sz0`, BA at exact type" is met.

## 6. Finding (3): Stein remainder at non-scalar `M` (the open item)
Re-checked against the signatures:
```
Chain/LWGen:48-50   LWAvgLawgL: PrecL … ‖C.L n (t n) (fun _ : Fin 1 => true) (fun _ => a) ω - C.m n‖ ≼ Bctl     (diagonal block a)
Chain/Carrier:80-84 STLKgL: ∀ k ≥ 1, PrecL … ‖C.L n τ σ a ω - C.K n τ σ a‖ ≼ Bctl^k                              (untwisted loops)
BA/TwistPins:91-93  BATwistAvgLaw: PrecL … ‖twTr C n (τ n) ω p.1 p.2‖ ≼ Bctl    (ordered block pairs; registry Test/Axioms:192, owed: TL stage + BA-V)
```
- Band: `T2502c_band_collapse` (`:153`, compiled, axioms standard) shows `t_{aq} - Mss_{aq} = δ_{aq} m (ḡ_a - m)`, so the remainder is a second moment of `LWAvgLawgL`. W1 (i)′ and (ii)′ are enough at the band.
- BA (`M = M^B ⊗ I`): `t_{aq} - Mss_{aq} = M^B_{aq}(G̃_{qa} - M^B_{qa})` is an off-diagonal twisted partial trace (numeric identity `|diff| = 2.2e-19`, reproduced in §2). Neither pinned premise of `T2502_ImproveExpAvergL` (check `:226-232`: `LWAvgLawgL`, `STLKgL`) controls it. The report's route is TL1 `BATwistAvgLaw` plus an `ℓ¹` bound on `M^B`. TL1 is an owed pin, and its producer `baTwistAvgProd_holds` (`BA/TwistAvgB:451`) also needs `STLmaxgL`. The `ℓ¹` source `CltFlowBA_MB_decay` is `private`. The proposed `T2502c_W1iii` (`:182`) and `T2502c_W1iv` (`:190`) compile, but neither has a BA discharge or a named owner.
- Paper: `6:12-21` gives `lem:improve_exp_aver` "in the setting of `lem:main_ind`" with "the same proof as [YY_25, Lemma 5.15]" (the scalar-`M` case) using `(Gt_avgbound_flow)` and `(Eq:L-KGt-flow)` (`1_2:1344`, `:1371`). Neither is a twisted off-diagonal average. The ticket's expectation in acceptance (10), "paper-delta: none; `6:12-21` covers `H₀ ≠ 0`", is therefore unconfirmed at non-scalar `M`.
- Stop lines hit (ticket `:75`) if row c went ahead as generic with (iii)/(iv):
  - "a family premise without a named BA discharge or owner";
  - "a public result with an unproved `Prop` premise neither concluded nor registered".
- Stop line hit if row c went ahead without them: at BA, "a binding `T2502_*` text unprovable as stated" (`T2502_ImproveExpAvergL` at the BA tuple) cannot be excluded on the current premise list.
- The two options of report `:138` are both outside the ticket:
  - (A) generic with (iii), (iv) as guarded family premises. Owners: TL stage / BA-V for (iii); a public `MB` row bound for (iv).
  - (B) row c only for band-type carriers (`M = m • 1`), with BA's `lem:improve_exp_aver` going to V1-BA. This changes the scope of target 16 and the family table row 14.

## 7. Section (a) deliverables (CLAUDE.md §4 step 1; ticket 1a fill-in (v))
| item | status |
|---|---|
| (i) exponent table | present, 11 rows; values reproduced (§2) |
| (ii) concrete instance + script | present; reproduced verbatim (§2); `d = 3`, `L = 4`, `W = 2`, `E = 1/2`, nondegenerate |
| (v) W1 decided, with lines | (i)′, (ii)′ decided and compiled (§4–§5); the non-scalar-`M` remainder **not decided** (§6) |
| answer (7) probe ≤ 300, band+BA at `sz0`, BA exact type | met (§1, §5) |
| rows, layout, cut | unchanged (`ExpAvgGen` alone; probe only on the branch) |

## Observations (no verdict effect)
- O1. The Monte Carlo of (a″) is weak evidence. Case 1 has `max|x-rhs| = 2.14e-3` against a standard error of `6.3e-4` (3.4σ) at `|x| = 0.0256`. The Stein identity rests on the mathematics, not on this check.
- O2. (a) row 2 says `Cs` is "expected to depend on kappa only"; (a″) finding 4 says `(d, κ, 𝔡)`. The probe is consistent with the latter (`Cs` sits after `(κ, ε, 𝔡)`).
- O3. (a) row 7 quotes `‖G‖ = 267.5`. That is the BA line; the band line gives `‖G‖ = 2.00`. Both lines lie inside the envelope.
- O4. The probe imports `Chain/Step2Kern` and `BA/*`. That is allowed for a probe that is never merged; the 1b file must not import them (ticket `:14`, `:85`).
- O5. Neither section proposes a paper-delta candidate tag `T2502ca` for finding (3). It belongs in the 1b report (d) once the dispatcher has chosen (A) or (B).

## Verdict
- D1 W1 (i)′ (`T2502c_W1i`): **PASS** as a text. It strengthens the draft as needed, is discharged at band and at BA for every flow, and has nonempty instances.
- D1 W1 (ii)′ (`T2502c_W1ii`, `∀ᶠ`): **PASS** as a text. It is discharged at both, with instances.
- W1 as a whole, i.e. whether `lem:improve_exp_aver` holds at a non-scalar carrier from (i)′, (ii)′ and the pinned premises: **BLOCKED, needs dispatcher sign-off** (H183 (3)). Missing input: the dispatcher's choice between (A) and (B) of §6, with the owners of (iii)/(iv) under (A), or the restricted scope of target 16 under (B). Then the amended W1 texts go into the ticket/check: (i)′ with conjuncts (a) and (c), (ii)′ eventual, and rows 9 + 14 merged. Stage 1b must not start before that.

Overall: **BLOCKED — needs dispatcher sign-off.** There is no defect in section (a) or in the probe for the prover to repair.
