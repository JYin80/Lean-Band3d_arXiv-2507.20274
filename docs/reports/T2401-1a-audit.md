Auditor model: claude-opus-5-5

# T2401 1a-audit round 2 (BA-G5a design gate, after one rule-(B) repair under Amend 1): sections (a), (G), (a″), (a′), (a‴) of `docs/reports/T2401-prove.md`; probe `t/T2401:RBM3D/Probe/T2401Pins.lean` (aec5a16)

Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2401-1a-audit2` (detached at aec5a16, base cbda0ab = G3a merge). Written Sun Oct 11 04:42:45 UTC 2026 (`date -u`). Scratch files: `<scratchpad>/T2401/`. Round-1 list: D1–D3 concrete, D4 dispatcher (answered by Amend 1, `docs/tickets/T2401-amend-1.md`, DECISIONS §220).

## 1. Probe recompile, scope, hygiene
```
$ git log --oneline main..t/T2401
aec5a16 T2401: probe recompile under Amend 1 D1-D3 (RBM3D/Probe/T2401Pins.lean, never merged)
a48c0ce T2401: probe pins of the BA-G5a design gate (RBM3D/Probe/T2401Pins.lean, never merged)
$ git diff --stat main...t/T2401
 RBM3D/Probe/T2401Pins.lean | 847 +++++++++++++++++++++++++++++++++++++++++++++
 1 file changed, 847 insertions(+)
$ lake build RBM3D.BA.GreenCore RBM3D.Green.FlucIterGain RBM3D.Green.MinorDiff   (deps rebuilt at the cbda0ab base; Chain/Carrier differs from main)
✔ [3781/3781] Built RBM3D.BA.GreenCore (13s)
$ lake env lean RBM3D/Probe/T2401Pins.lean > probe.out 2>&1; echo EXIT=$?
EXIT=0
$ grep -cE 'error|warning' probe.out ; grep -c '^RBM' probe.out
0
33
$ diff <(sed -n 358,395p T2401-prove.md) probe.out && echo "probe output identical to (a‴) listing"
probe output identical to (a‴) listing
$ grep -nE '\bsorry\b|\badmit\b|^axiom|native_decide' RBM3D/Probe/T2401Pins.lean; echo grep-exit=$?
grep-exit=1
$ grep -c '^example' …; grep -c '^#check' …; grep -cE '^(theorem|lemma)' …
14
33
0
$ git grep -n -e GreenMinor -e BAFAav -e BAFamGain main -- RBM3D RBM3D.lean | wc -l      (main = 1c25de0)
       0
```
The probe has no root import and no proofs; every pin is a `Prop`, applied in the `example`s as a hypothesis (the T2390 pattern).

## 2. Numerics reproduced (copies of `docs/reports/T2401/*.py`; outputs diffed with the committed `*.out`)
```
$ for s in replan_a2 probe_chk fa_consts fa_ident fa_walk; do python3 $s.py > ../rerun/$s.out; echo "$s exit=$? diff_lines=…"; done
replan_a2 exit=0 diff_lines=0
probe_chk exit=0 diff_lines=0
fa_consts exit=0 diff_lines=0
fa_ident exit=0 diff_lines=0
fa_walk exit=0 diff_lines=0
```
(`fa_scale`, `fa_poly` unchanged since round 1, where they were reproduced; not rerun.)

## 3. Round-1 "Required for resubmission", item by item

**D1 (`BAFAav` hypothesis at `ε₀/2`; G.6 event inclusion). Met.**
```
$ git diff a48c0ce aec5a16 | grep -E '^[-+] .*BAGiiGEX sz z t' | cut -c1-150
+  sections 9, 10 and 12: D1 (`BAFAav` takes `BAGiiGEX sz z t (ε₀ / 2)`), D2 (S4 is `GreenMinor_diff_pin'`), D3 (`BAFamGain` is a compiled `Prop`
+    ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ BAflowT0 sz z n) → ∀ ε₀ : ℝ, 0 < ε₀ → BAGiiGEX sz z t (ε₀ / 2) →
-    ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ BAflowT0 sz z n) → ∀ ε₀ : ℝ, 0 < ε₀ → BAGiiGEX sz z t ε₀ →
+    ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ BAflowT0 sz z n) → ∀ ε₀ : ℝ, 0 < ε₀ → BAGiiGEX sz z t (ε₀ / 2) →
```
(Line 1 is the header comment; line 2 is the new `BAFamGain`; lines 3–4 are `BAFAav`.) Nothing else in the `BAFAav` statement changed. I checked the argument in (a′) D1 against the definitions:
- `PrecL = StochDomAt μ sz.size` (`Chain/Carrier.lean:51`), and the union over `u` is inside `badSetAt` (`Defs/StochDomAt.lean:53`).
- `STInitialGT2gL` conjunct 1 is `‖GM‖ ≺ W^{-ε₀}` (`Carrier.lean:140`).
- `Bandwidth 𝔠 : N^𝔠 ≤ W` eventually (`Defs/Sizes.lean:168`, part of `Admissible`).
- So with `ζ = 𝔠ε₀/2`, `{‖Δ‖_max ≤ N^ζ W^{-ε₀}} ⊆ {‖Δ‖_max ≤ W^{-ε₀/2}} = Ω(ε₀/2)` (the `indMax` of `BAGiiGEX`, `BA/Step1Boot.lean:79`).
- `BAGiiGEX(ε₀/2)` and conjunct 2 then give `‖Δ‖_max ≺ Ψ`. Both use the same carrier `baFMz sz z`, law `seqP (sz.withLam 0)` and time `t n`.

Independent check of the inclusion (`aud_plan.py`):
```
D1 random (log2 W, c, log2 N <= log2 W / c, eps0): violations 0
```
- The new premise is satisfiable from an owed pin: probe :716 compiles `BAGbEXPii 3 → BAGiiGEX sz0 zSeq (fun _ => 1/2) (1/10/2)`.
- Instance :721 is at `ε₀ = 1/10`, `hii` at `1/20`.
- No new external hypothesis; no cycle (`BAGbEXPii` is G6's owed pin and stays a hypothesis).

**D2 (S4 = `GreenMinor_diff_pin'`). Met.**
```
$ diff <(sed -n 213,225p …T2401Pins.lean) <(sed -n 228,240p …T2401Pins.lean)
1c1
< def GreenMinor_diff_pin : Prop :=
---
> def GreenMinor_diff_pin' : Prop :=
6c6
<     (∀ u v, M u v = if u.2 = v.2 then Mb u.1 v.1 else 0) → 0 < κ → κ ≤ ‖m‖ → ‖M u y‖ ≤ 1 →
---
>     (∀ u v, M u v = if u.2 = v.2 then Mb u.1 v.1 else 0) → 0 < κ → κ ≤ 1 → κ ≤ ‖m‖ → ‖M u y‖ ≤ 1 →
```
- (a′) D2 names `diff'` the S4 pin ("1b must take `diff'`"). The probe docstrings drop the dispatcher clause, and `¬ GreenMinor_diff_pin` (:770) stays as the record.
- The BA fact `1/2 ≤ ‖m‖ ≤ 1` at the carrier is compiled at :657 (`BAflow_real`, `BAm_norm_le_one`).
- Paper delta `T2401d` stays.

Independent checks:
- `aud_plan.py`: the base case and the monotonicity of `a_r`, over a grid of `κ`, `s`, `g₀` and `δ'`.
- `aud_s4.py`: a numerical tower of Schur minors (`d=1, L=4, W=3`, an `O(1)` random `M^B`, `G = M + e·noise`) on the protected levels `S ⊆ R_{β,o}`. Here `δ` and `κ` are read off the levels, and `l = R[:r]`.
```
D2 grid k in (0,1], s,g0 >= 0, delta'=2delta in [0,1]: base <= c_Y(0) and a_r monotone: True
e=0.01 g0=2.0955 |m|=0.060: delta=1.42e-02 kappa=0.060 r=0: …=14.7 cY=1.58e+05 ok=True; r=1: …=210 cY=4.73e+17 ok=True; r=2: …=1.64e+03 cY=1.99e+81 ok=True
e=0.001 g0=2.0955 |m|=0.060: delta=1.42e-03 kappa=0.060 r=0: …=16.3 cY=1.58e+05 ok=True; r=1: …=243 cY=4.73e+17 ok=True; r=2: …=532 cY=1.99e+81 ok=True
e=0.0001 g0=2.0955 |m|=0.060: delta=1.38e-04 kappa=0.060 r=0: …=56 cY=1.58e+05 ok=True; r=1: …=50.1 cY=4.73e+17 ok=True; r=2: …=1.15e+03 cY=1.99e+81 ok=True
e=0.0001 g0=0.535 |m|=0.583: delta=1.83e-04 kappa=0.583 r=0: …=0.854 cY=59.9 ok=True; r=1: …=0.215 cY=1.66e+06 ok=True; r=2: …=0.148 cY=2.19e+30 ok=True
```
(`…` = `|Δ_l Y|/(2δ)^{r+1}`, max over `Y^X`, `Y^A`; all 9 rows `ok=True`.) The ratio stays bounded as `e` falls over 2 decades, so the order `(2δ)^{r+1}` holds with O(1) cross-block `M^B` (no smallness of `g`).

**D3 (`BAFamGain` compiled with an instance). Met.**
- `BAFamGain` is at probe :320, with families `GreenMinor_famA` :303 and `GreenMinor_famX` :310 (fine index, `split`, `y = (α, o(u))`).
- Hypotheses are those of `BAFAav` (D1 form), plus `0 < τ ≤ ε₀/2` and `∀ p`.
- The order is `∃ C ≥ 0` after the data, then `∀ᶠ n`, then `∀ β α, β ≠ α`. The conclusion has `A = Iblk β`, `B = C·δ_n`, `ρ = 4δ_n`, `δ_n = W^τΨ_n` and `M = K = 2p`. This matches G.5 and the amend.
- There is no structure field and no `∃ c` before the flow.
- Instance :739: `sz0`, `flow_sz0`, `t ≡ 1/2`, `ε₀ = 1/10`, `Ψ = W^{-1}` (window `W^{-3/2} ≤ Ψ ≤ W^{-1/10}` discharged), `τ = 1/20`, `p = 1`.
- Left as hypotheses: `h : BAFamGain 3` (allowed by the amend), `hii` (G6's) and `STInitialGT2gL` (the premise). Not degenerate.

**D4 (file plan under the dispatcher's decision). Met.** The amend authorises a third file if, after R6 moves to G5b, a file's hi estimate is still above 2,000. Independent arithmetic from the (G.8) rows (`aud_plan.py`):
```
round-1 layout, R6 removed: GreenMinor (940, 1300, 2079)  GreenMinor2 (876, 1319, 1973)
  third file authorised (some hi > 2000): True
(a') three files: [(777, 1037, 1676), (463, 718, 1078), (576, 864, 1298)]  max hi 1676  max central 1037  total [1816, 2619, 4052]
```
- The split is by section (V+S1, R1 | R2, R3 | R4, R7) and the import chain is linear.
- Every file has hi ≤ 2,000 (the binding stop line) and central ≤ 1,500.
- The (a′) re-plan `1816 / 2619 / 4052` becomes the ticket estimate (amend D4).
- 1b targets in (a′): S1 (with `removal_cross`, `offset_ne`), S2, S3, S4 as `diff'`, S6, R1 tower, and registry lines `BAFamGain`, `BAFAav`. S5/R6 is G5b's.

## 4. Deliverables (i)–(vii) after the repair
- (i) good event and minor identity; (ii) structural fact (pins :85-:109); (iii) one-block FA: unchanged since round 1 and still met.
- (iv) two-block FA closes; no REQ. The gain order is spot-checked again above.
- (v) averaged law and quantifiers: met after D1. The order is `∀κ ε 𝔡`, flow, `t`, `ε₀`, `BAGiiGEX(ε₀/2)`, `Ψ` window, `(initialGT2)`, `PrecL`. There is no `∃ c` before the flow. G5b's 1a need not be a design gate (G.6 last item, unchanged).
- (vi) C1/G2: no new constant. D1 uses only `Bandwidth`, and D2 uses `κ ≤ ‖m‖ ≤ 1`, a uniform BA fact. No `g ≤ W^{-ε}`, no smallness of `‖M − m₀I‖`, no `(Cλ)^{|a-b|}`.
- (vii) pins compiled (§1), files and estimates (D4), nonempty instances for each pin family (D1–D3 plus the round-1 instances).

## 5. Paper deltas
`T2401a–d` (G.9, (a″)) cover the Lean/paper differences: the averaged law for all `g ≤ Λ`, the family gain restricted to the block, `a_0 = 2/κ`, and `κ ≤ 1` in S4.
- D1 adds none: the paper's `lem_GbEXP` holds for all small `ε₀`, and the hypothesis at `ε₀/2` is an instance of `BAGbEXPii`.
- `BAFamGain` is an intermediate pin with no paper counterpart.

## 6. Observations (no RETURN)
- **O1 (vocabulary home of `GreenMinor_famGain`).** (a′) :321 calls `GreenMinor_famGain` "now G5b's vocabulary", and (a‴) :418 says the same. But the 1b registry line `BAFamGain`, which lives in G5a's `GreenMinor3` (R7), is stated through `GreenMinor_famGain`, `GreenMinor_famA` and `GreenMinor_famX`.
  - For 1b: these three `def`s (about 30 lines, probe :246, :303, :310) go into `GreenMinor3` with the registry line. Only the R6 proof work (`famAvg_moment`, the graded-iteration twin) moves to G5b.
  - This does not change a statement, an instance or a stop line (`GreenMinor3` hi 1298 + 30 < 2000). The G5b ticket should import these defs rather than redefine them.
- O2: the 1a sections are now 419 lines (the ticket's frame is ≤ 300 for the 1a section). This is a length defect only.
- O3: `t/T2401` is based on cbda0ab. The 1b branch must start from current main (`GreenStab`, Carrier changes; round-1 O4).
- O4: round-1 O1 (Route A `hB1` thresholds `10^{33–91}`, eventual only) still stands. G5b's preflight carries row 9.

## 7. Verdict
**PASS.** Round-1 items D1–D3 are met as the amend specifies, and D4 is met under the dispatcher's decision (third file authorised by its condition). Every stage-1a deliverable (i)–(vii) is met. No binding stop line is hit: (iv) closes, and every file has hi ≤ 2,000. Numerics reproduced; the probe recompiles with `EXIT=0` and output identical to (a‴). No C1-forbidden step. No dispatcher sign-off needed; O1 is a note for the 1b prover and the G5b ticket.
