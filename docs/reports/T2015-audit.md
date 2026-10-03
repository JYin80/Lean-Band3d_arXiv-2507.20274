Auditor model: claude-opus-5-5

# T2015 audit (round 2) — ST-D1 pins of `lem:main_ind`, `lem_GbEXP`, `lem_ConArg`, Step 1

Audit time: Sat Oct  3 04:59:41 UTC 2026 (`date -u`). Branch `t/T2015` at `752e027`; audit worktree
`/Users/junyin/Lean_proof/RBM3D-wt/T2015-audit2` (detached). Ticket type: report only (probe stays on the branch).
Round 1 (`6f8684e`) returned D1 (no compiled instance of `lem_GbEXP` part 3 at a concrete `Ψ`) and D2 (two
missing paper-delta candidates). This round checks the repair and re-runs build, axioms and hygiene.

**Verdict: PASS.** No dispatcher sign-off needed.

## 1. Repair diff (pins unchanged)

```
$ git diff --stat 6f8684e 752e027
 RBM3D/Probe/T2015Pins.lean | 20 ++++++++++++++++++++
 1 file changed, 20 insertions(+)
$ git diff --name-only main...t/T2015
RBM3D/Probe/T2015Pins.lean
```
The 20 added lines are `theorem inst_gbEXP_av` (probe:666-680) and its `#print axioms` (probe:1964). No pin
definition (`STMainInd` 407, `STGbEXPii/ij/av` 421/428/435, `STConArg` 447, `STStep1` 462, `STBootstrap`,
`STNetLift`, `STKbound`) and no skeleton line changed, so the round-1 statement checks (paper comparison
table, quantifier order, `≺` scale `N`, ranges of `n,s,t,σ,a`, extreme inputs, no hidden hypothesis, no cycle,
binding to merged MD-2/MD-3 declarations by scratch compile) carry over unchanged.

## 2. Build, axioms, hygiene (audit worktree)

```
$ lake build RBM3D.Probe.T2015Pins > a2build.out 2>&1; echo exit=$?
exit=0
$ grep -c 'depends on axioms: \[propext, Classical.choice, Quot.sound\]' a2build.out; grep -c 'depends on axioms' a2build.out
52
52
$ grep -cE '^(warning|.*: warning)' a2build.out; grep -cE '^error|: error' a2build.out
0
0
$ tail -1 a2build.out
Build completed successfully (3308 jobs).
$ grep inst_gbEXP_av a2build.out
info: RBM3D/Probe/T2015Pins.lean:1964:0: 'RBM.Probe.T2015.Inst.inst_gbEXP_av' depends on axioms: [propext, Classical.choice, Quot.sound]
$ grep -nE '\bsorry\b|\badmit\b|native_decide|^\s*axiom ' RBM3D/Probe/T2015Pins.lean | wc -l
0
```
52 = round 1's 51 plus `inst_gbEXP_av`; every axiom line is the standard three.

## 3. D1 — compiled nonempty instance of `STGbEXPav` (part 3, `(GavLGEX)`, `3_5:28-33`)

Pin premise (probe, `STGavLGEX`):
```
def STGavLGEX (E t : ℕ → ℝ) (ε₀ : ℝ) : Prop :=
  ∀ Ψ : ℕ → ℝ, (∀ᶠ n in atTop, ((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2) ≤ Ψ n) →
    (∀ᶠ n in atTop, Ψ n ≤ ((sz.W n : ℕ) : ℝ) ^ (-ε₀)) →
    Prec … ‖STGM …‖ … W^(-ε₀) →  Prec … STmaxLoop2 … (Ψ n ^ 2) →  Prec … ‖Lloop … - mE …‖ … (Ψ n ^ 2)
```
Instance (probe:666-680):
```
theorem inst_gbEXP_av (h : STGbEXP 3)
    (hG : Prec sz0 … (fun n p ω => ‖STGM sz0 n (STflowE z0 n) (tInst n) ω p.1 p.2‖)
      (fun n _ _ => ((sz0.W n : ℕ) : ℝ) ^ (-(1 / 20 : ℝ))))
    (hL : Prec sz0 … (fun n _ ω => STmaxLoop2 sz0 n (STflowE z0 n) (tInst n) ω)
      (fun n _ _ => (((sz0.W n : ℕ) : ℝ) ^ (-(1 : ℝ))) ^ 2)) :
    Prec sz0 … ‖Lloop … (fun _ : Fin 1 => true) (fun _ => a) ω - mE (STflowE z0 n)‖ … (W^(-1))^2 := by
  refine (inst_gbEXP h).2.2 (fun n => ((sz0.W n : ℕ) : ℝ) ^ (-(1 : ℝ))) ?_ ?_ hG hL
  · exact Eventually.of_forall fun n => Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast sz0.W_pos n) (by norm_num)
  · exact Eventually.of_forall fun n => Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast sz0.W_pos n) (by norm_num)
```
Data: `sz0` (`d=3`, `W_n=(2(n+1))^5`, `L_n=4(n+1)`), `z0`, `t ≡ 1/16 ≤ t₀` (`sixteenth_le_lemT`), `ε₀ = 1/20`,
`Ψ_n = W_n^{-1}`. Deterministic premises discharged in the file: `3 ≤ d`, `STFlow` (`flow_z0`), `0 ≤ t`,
`t ≤ t₀`, `0 < ε₀`, and both window bounds `W^{-3/2} ≤ W^{-1} ≤ W^{-1/20}` (exponents `-3/2 ≤ -1 ≤ -1/20`,
base `W_n ≥ 1`): the window is nonempty and the control is strictly interior. Remaining hypotheses: `STGbEXP 3`
(the pin) and the two `Prec` premises of `(initialGT2)` (stochastic). Not degenerate (no `N = 0`, no empty
index, no collapsed window, no `False` premise). **D1 resolved.**

## 4. D2 — paper-delta coverage (prove report (d))

```
$ grep -o 'T2015[a-h]' docs/reports/T2015-prove.md | sort -u | tr '\n' ' '
T2015a T2015b T2015c T2015d T2015e T2015f T2015g T2015h
```
* `T2015g`: `STStep1` stated for every `𝔠_d ∈ (0,10^-2]` with premises (a), (c), `ML:Kbound` only — stronger
  than the paper's Step 1 inside `lem:main_ind` (single `∃𝔠_d`, all of (a)-(d)). Matches round-1 D2(i).
* `T2015h`: `STConArg` keeps only the first bound of `(res_lo_bo_eta)`. Paper `3_5:52-56` (read this round):
```
    {\bf 1}(\Omega_t) \cdot \max_{\bsig, {\ba}} \big|{\cal L}^{(n)}_{t, \bsig, {\ba}} \big|\prec \left(
    (W^{-d}B_{s,0})\cdot\frac{\eta_{s}}{\eta_{t}}\right)^{n-1}
    \le  \left(
    (W^{-d}B_{t,0})\cdot\frac{\eta_{s}}{\eta_{t}}\right)^{n-1}.
```
  The omitted inequality is deterministic; the cited `STBctl_mono` exists in the probe:
```
962:theorem STBctl_mono (n : ℕ) {s u : ℝ} (hsu : s ≤ u) (hu : u < 1) : sz.Bctl n s ≤ sz.Bctl n u := by
```
  Matches round-1 D2(ii). `T2015a` is declared void (pin uses the paper's `a_t`). **D2 resolved.**

Every Lean/paper difference found in round 1 is now covered: T2015b-h, D18, D20, D23, T2001e.

## 5. Observations (no verdict effect)

* O1. Prove report b.1 still records the build at `6f8684e` and "1958 lines"; the probe is now 1978 lines at
  `752e027`. The repair section of the report pastes the post-repair build (`std=52`, exit 0), which this
  audit reproduced (§2). Header-only staleness; no statement, instance, build or axiom effect.
* O2. Prove report is 300 lines (limit 300).
* O3. Round-1 observations stand: section-0 copies of MD-2/MD-3 declarations bind to the merged ones (checked
  by scratch compile in round 1; unaffected by this repair); split = 36 tickets (below the O2 threshold 50);
  moving 4 ST-3/ST-6 files into ST-1 is a normal dispatcher decision for downstream tickets, not an audit
  sign-off; `t → 1` for `STMainInd`/`STStep1` is numeric only (report (d)(iii)).

## 6. Verdict per target

| target | verdict |
|---|---|
| 1 inventory, 3 exponent table, 4 routes, 6 BA reuse, 7 split | PASS (report-only content, unchanged since round 1) |
| 2 pins `STMainInd`, `STGbEXPii/ij`, `STConArg`, `STStep1`, `STKbound`, `STBootstrap`, `STNetLift` | PASS (statements unchanged; build, axioms) |
| 2/8 `STGbEXPav` (`lem_GbEXP` part 3) with `inst_gbEXP_av` | PASS (D1 resolved) |
| 5 skeleton `ST_step1_skeleton`, `inst_skeleton` | PASS |
| 8 instances (`inst_*`, 52 axiom lines standard) | PASS |
| (d) paper-delta coverage `T2015b`-`T2015h` | PASS (D2 resolved) |

Overall: **PASS**. Merge (report-only ticket): only `RBM3D/Probe/T2015Pins.lean` differs from `main`; per the
ticket the probe stays on branch `t/T2015`, so the hub brings in only the reports.
