Auditor model: claude-opus-5-5

# T2149 audit (round 1): S5-20 `Evolution/CltGood`. Written Sun Oct  4 18:10:20 UTC 2026

Branch `t/T2149` at `f0f46c7`. Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2149-audit1` (detached).

## 1. Scope, build, axioms, hygiene

```
$ git diff main...HEAD --name-status
A	RBM3D/Evolution/CltGood.lean
$ lake build RBM3D.Evolution.CltGood     (exit=0)
⚠ [3808/3808] Built RBM3D.Evolution.CltGood (4.5s)
warning: RBM3D/Evolution/CltGood.lean:19:100: This line exceeds the 100 character limit, please shorten it!
info: RBM3D/Evolution/CltGood.lean:672:0: 'RBM.Evol.cltCoord_tail' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM3D/Evolution/CltGood.lean:673:0: 'RBM.Evol.cltGmax_whp' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM3D/Evolution/CltGood.lean:674:0: 'RBM.Evol.cltFarEntry_whp' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM3D/Evolution/CltGood.lean:675:0: 'RBM.Evol.cltGood_whp' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM3D/Evolution/CltGood.lean:676:0: 'RBM.Gauss.Step5Inst.cltGood_hclt_szCL' depends on axioms: [propext, Classical.choice, Quot.sound]
Build completed successfully (3808 jobs).
$ grep -nE "\bsorry\b|\badmit\b|native_decide|^\s*axiom\b|maxHeartbeats" RBM3D/Evolution/CltGood.lean
(no output)
$ grep -cE "^private (theorem|lemma|def)" RBM3D/Evolution/CltGood.lean
9
```
Only the sole writable file is touched (new file; no merged signature changed; `Test/Axioms.lean` untouched, no registry line expected). Imports: `Evolution/FarEntry`, `Evolution/CltPath`, two Mathlib files; not `RBM3D`.

## 2. Statements (item by item)

Public declarations (script):
```
64:def HClt (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ) (s τ t : ℕ → ℝ) (Cd : ℝ) : Prop :=
65:   3 ≤ d ∧ 0 < κ ∧ 0 < ε ∧ STFlow sz κ ε 𝔠 𝔡 z ∧ (∀ n, 0 ≤ s n) ∧ (∀ n, s n ≤ τ n) ∧
66:     (∀ n, τ n ≤ t n) ∧ (∀ n, t n ≤ lemT (z n)) ∧ STStep2Concl sz (STflowE z) s t Cd
77:def CltCoordTail : Prop :=
78:   2 ≤ d → ∀ 𝔠 : ℝ, 0 < 𝔠 → sz.SizeTendsto → sz.Bandwidth 𝔠 →
79:     ∀ D : ℝ, 0 < D → CltCoordConcl sz D
91:def CltGmaxWhp : Prop := ∀ (κ ε 𝔠 𝔡) z (s τ t) Cd, HClt sz … → ∀ D, 0 < D → CltGmaxConcl sz (STflowE z) τ D
110:def CltFarEntryWhp : Prop := ∀ … HClt sz … → ∀ c, 0 < c → ∀ D', 0 < D' → ∀ D, 0 < D → CltFarEntryConcl sz (STflowE z) τ c D' D
125:def CltGoodWhp : Prop := ∀ … HClt sz … → ∀ (c : ℝ) (θ : ℕ → ℝ), 0 < c →
128:       (∀ n, c * Real.log ((sz.W n : ℕ) : ℝ) ^ 3 * ellT (sz.L n) (sz.lam n) (τ n) ≤ θ n) →
129:       ∀ D' : ℝ, 0 < D' → ∀ D : ℝ, 0 < D → CltGoodConcl sz (STflowE z) τ θ D' D
120:   PF … {ω | ¬ cltGoodAt d (sz.L n) (sz.W n) (E n) (τ n) (θ n) D' ω} ≤ ENNReal.ofReal (N ^ (-D))   [CltGoodConcl body]
323:theorem cltCoord_tail {d : ℕ} (sz : Sizes d) : CltCoordTail sz
414:theorem cltGmax_whp {d : ℕ} (sz : Sizes d) : CltGmaxWhp sz
491:theorem cltFarEntry_whp {d : ℕ} (sz : Sizes d) : CltFarEntryWhp sz
561:theorem cltGood_whp {d : ℕ} (sz : Sizes d) : CltGoodWhp sz
```
(lines 91/110/120 abbreviated by hand; full text at the line numbers.)

Script diff of the event bodies against the RBM2D source pins (`c9a24cf`, `CltGood.lean:83-105`), after normalising `(d.L n) (d.W n)`/`d (sz.L n) (sz.W n)` to `LW`, `u ↦ τ`, `P LW ↦ PF`:
```
$ diff -w r2.txt r3.txt   (event-body lines only)
<           (d.W n : ℝ) ^ τ' * ellT (d.L n) (τ n) ≤
<               (zdist2 (d.L n) ((splitEquiv LW x).1 -
<                 (splitEquiv LW y).1) : ℝ) ∧
<             (d.W n : ℝ) ^ (-D') <
---
>         c * Real.log ((sz.W n : ℕ) : ℝ) ^ 3 * ellT (sz.L n) (sz.lam n) (τ n) ≤
>             ((zdistInf d (sz.L n) ((split LW x).1 -
>               (split LW y).1) : ℕ) : ℝ) ∧
>           ((sz.W n : ℕ) : ℝ) ^ (-D') <
```
The `CltGmaxWhp` event `{ω | ∃ σ x y, 2 < ‖gEntry … (τ n) (Hflow … (τ n) ω) σ x y‖}` is identical; the far event differs only by the ticket's mandated `W^{τ'} ↦ c (log W)^3` (DECISIONS §43) and the `d ≥ 3` dictionary (`zdist2 ↦ zdistInf`, `splitEquiv ↦ split`). The remaining hunks are the split into `*Concl` definitions (elaboration trap) and the `HClt` argument list.

Merged definition consumed by item 5 (`CltPath.lean:83`):
```
def cltGoodAt (d L W : ℕ) [NeZero L] [NeZero W] (E u θ D' : ℝ) (ω : Ω d L W) : Prop :=
  (∀ σ x y, ‖gEntry d L W E u (Hflow d L W u ω) σ x y‖ ≤ 2) ∧
    ∀ σ x y, θ ≤ (zdistInf d L ((split d L W x).1 - (split d L W y).1) : ℝ) →
      ‖gEntry d L W E u (Hflow d L W u ω) σ x y‖ ≤ (W : ℝ) ^ (-D')
```
`CltGoodConcl` uses `cltGoodAt` verbatim (same `gEntry`, `Hflow`, `split`, `zdistInf`).

Per item, against the ticket:
- **Item 1 `HClt`.** Flow, `0<κ`, `0<ε`, `0 ≤ s ≤ τ ≤ t ≤ lemT z`, `STStep2Concl sz (STflowE z) s t Cd`, plus `3 ≤ d` (the `hd` of `stFarEntryAtLog`, `FarEntry.lean:835`). Each conjunct is exactly a hypothesis of `stFarEntryAtLog`; explicit Prop conjunction, no structure fields. Hypothesis map of RBM2D's `Step2LocalPT/Step2DecayPT/GbEXPHypV3/RangeCond/Bandwidth` given in the file header (lines 20-25) and prove report (a)(i). PASS.
- **Item 2 `CltCoordTail`.** Per coordinate, threshold `W^{-1/2}`, probability `≤ N^{-D}`, `∀ᶠ n`, quantifier order as RBM2D (`∀ 𝔠 … ∀ D, ∀ᶠ n, ∀ c`). Extra hypothesis `2 ≤ d` (weaker than the project's `3 ≤ d`; covered by candidate `T2149a`). PASS.
- **Item 3 `CltGmaxWhp`.** As pinned; charge `D` (union over `(σ,x,y)` inside the event). PASS.
- **Item 4 `CltFarEntryWhp`.** `θ = c (log W)^3 ℓ_τ`, every `c > 0`, `D' > 0`, `D > 0`, `ellT (sz.L n) (sz.lam n) (τ n)` exactly as in the merged `STFarEntryAtLog` (`FarEntry.lean:677`). PASS.
- **Item 5 `cltGood_whp`.** Takes any `θ n ≥ c (log W)^3 ℓ_τ` (a sequence) rather than the exact threshold: a strictly more general statement (the exact one is the instance `θ n := c (log W)^3 ℓ_τ`, used in the example below). Covered by `T2149c`. PASS.

## 3. Vacuity, hidden hypotheses, cycles

- No structure-field hypotheses: `HClt` is a conjunction of merged predicates. `STStep2Concl` (`Step34Pins.lean:221`) is `STLocalEntryU ∧ STAvgU ∧ STGdecayW`, another gate's pin; no merged theorem concludes it (`grep` for `) : STStep2Concl` / `→ STStep2Concl` outside CltGood: no hit), so it may stay a hypothesis of the examples, as the ticket's "Instances" line also prescribes.
- Dependencies are merged: `stFarEntryAtLog`, `prec_timeIcc_section`, `farEntry_szCL_far_nonempty` (`FarEntry.lean:835,63,904`), `cltGoodAt` (`CltPath.lean:83`), `szCL`, `sCL`, `tCL`, `zCL`, `flow_zCL`, `lemT_zCL`, `szCL_hst`, `szCL_bandwidth`, `szCL_tendsto` (`Step5Pins.lean:640-782`). New file imports only merged modules; no cycle.
- No external hypothesis is introduced (only `STStep2Concl`, an internal pin); no new limit check needed beyond the preflight's (a)(ii) numbers.

## 4. Compiled nonempty instances (same file, lines 632-666, built above)

```
632: theorem cltGood_hclt_szCL (hStep2 : STStep2Concl szCL (STflowE zCL) sCL tCL 1) :
633:     HClt szCL (1 / 10) (1 / 10) (1 / 6) (1 / 10) zCL sCL sCL tCL 1 :=
634:   ⟨le_refl 3, by norm_num, by norm_num, flow_zCL, fun _ => le_rfl, fun _ => le_rfl,
635:     fun n => (szCL_hst n).le, lemT_zCL, hStep2⟩
639: example : CltCoordConcl szCL 10 :=
640:   cltCoord_tail szCL (by norm_num) (1 / 6) (by norm_num) szCL_tendsto szCL_bandwidth 10 (by norm_num)
644: example (hStep2 : …) : CltGmaxConcl szCL (STflowE zCL) sCL 10 :=
646:   cltGmax_whp szCL (1 / 10) (1 / 10) (1 / 6) (1 / 10) zCL sCL sCL tCL 1 (cltGood_hclt_szCL hStep2) 10 (by norm_num)
651: example (hStep2 : …) : CltFarEntryConcl szCL (STflowE zCL) sCL 1 5 10 ∧ ∀ n, farEntry_FarNonempty szCL sCL 1 n :=
653:   ⟨cltFarEntry_whp szCL … (cltGood_hclt_szCL hStep2) 1 (by norm_num) 5 (by norm_num) 10 (by norm_num),
655:    farEntry_szCL_far_nonempty⟩
658: example (hStep2 : …) : CltGoodConcl szCL (STflowE zCL) sCL
660:     (fun n => 1 * Real.log ((szCL.W n : ℕ) : ℝ) ^ 3 * ellT (szCL.L n) (szCL.lam n) (sCL n)) 5 10 ∧
661:     ∀ n, farEntry_FarNonempty szCL sCL 1 n := ⟨cltGood_whp szCL … 1 (fun n => …) (by norm_num) (fun _ => le_rfl) 5 … 10 …,
666:    farEntry_szCL_far_nonempty⟩
```
`d = 3`, `L_n = 2(n+24)^5`, `W_n = 2^{n+24}` (`szCL`), `s = τ = 0 < t_n = 1 - L^{-2}`, `D = 10`, `D' = 5`, `c = 1`: nondegenerate (index sets of size `N² > 0`; far set nonempty at every `n` by the merged `farEntry_szCL_far_nonempty`, conjoined in the examples). Every deterministic hypothesis is discharged; only `STStep2Concl` remains. All four endpoint theorems instantiated. PASS.

## 5. Paper deltas

Report (d) proposes `T2149a` (`CltCoordTail` carries `2 ≤ d`; `W^{-1/2}` step length not an explicit paper statement), `T2149b` (Lean-only i.i.d.-copy route; which `STStep2Concl` parts are used), `T2149c` (`CltGoodWhp` takes `θ n ≥ c (log W)^3 ℓ_τ`). Every Lean/paper difference found in §2 (the `2 ≤ d` hypothesis, the general `θ`, the log-scale far threshold of §43 which is already a merged decision via `STFarEntryAtLog`) is covered. PASS.

## 6. Observations (no effect on verdict)

- Unpinned public helper definitions `CltCoordConcl`, `CltGmaxConcl`, `CltFarEntryConcl` are not prefixed with the file stem `CltGood` (CLAUDE.md §3 (E)); they are the "generic definitions" the ticket asks for, and grep shows no clash on `main` (report (b)). `CltGoodConcl`, `cltGood_hclt_szCL` are stem-prefixed.
- Docstring `CltGood.lean:19` cites `FarEntry.lean:673` for `STFarEntryAtLog` (correct) and the long-line warning at line 19 is cosmetic.
- `cltTransfer` named in ticket item 3 is not used; the event transfer is via `seqP_map_slice` + `Measure.map_apply` (report (b) narrative). Not a statement issue.

## Verdict

| Target | Verdict |
|---|---|
| `HClt` | PASS |
| `CltCoordTail` / `cltCoord_tail` | PASS |
| `CltGmaxWhp` / `cltGmax_whp` | PASS |
| `CltFarEntryWhp` / `cltFarEntry_whp` | PASS |
| `cltGood_whp` | PASS |

**T2149: PASS.** No dispatcher sign-off needed.
