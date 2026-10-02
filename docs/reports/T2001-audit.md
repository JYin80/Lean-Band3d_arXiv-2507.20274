Auditor model: claude-opus-5-5

# T2001 audit, round 2 (Fri Oct  2 19:04:20 UTC 2026)

Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2001-audit2`, detached at `bd95cc9` (`t/T2001`, the same commit as round 1; the repair changed only `docs/reports/T2001-prove.md`). Ticket type: report only (survey), targets 1-6.

**Verdict: PASS** (all targets). Round-1 RETURN items 1-3 are resolved (§3). Dispatcher sign-off is not needed for this verdict. The freeze-time decisions the report flags (T2001b, c, l) are recorded under Observations.

## 1. Build, axioms, hygiene, diff

```
$ lake build RBM3D.Probe.T2001Endpoints 2>&1 | grep -E "error|warning|axioms|Build|sorry"
info: RBM3D.lean:44:0: axiom audit: 509 theorems, 173 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
info: RBM3D/Probe/T2001Endpoints.lean:502:0: 'RBM.Probe.T2001_decol' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM3D/Probe/T2001Endpoints.lean:503:0: 'RBM.Probe.T2001_locSC' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM3D/Probe/T2001Endpoints.lean:504:0: 'RBM.Probe.T2001_QUE' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM3D/Probe/T2001Endpoints.lean:505:0: 'RBM.Probe.T2001_BUniv' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM3D/Probe/T2001Endpoints.lean:506:0: 'RBM.Probe.T2001_QDiff' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM3D/Probe/T2001Endpoints.lean:507:0: 'RBM.Probe.T2001_decol_BA' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM3D/Probe/T2001Endpoints.lean:508:0: 'RBM.Probe.T2001_BA_BUniv_literal' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM3D/Probe/T2001Endpoints.lean:509:0: 'RBM.Probe.admissible_witnessSeq' depends on axioms: [propext, Classical.choice, Quot.sound]
Build completed successfully (3254 jobs).
$ grep -nE 'sorry|admit|native_decide|^\s*axiom' RBM3D/Probe/T2001Endpoints.lean | wc -l
       0
$ git diff --name-only main...HEAD
RBM3D/Probe/T2001Endpoints.lean
$ wc -l docs/reports/T2001-prove.md ; head -1 docs/reports/T2001-prove.md
     297 docs/reports/T2001-prove.md
Prover model: claude-sonnet-5-5
```
`main` is still `3c11d7b`. `T2001-coverage.md` was last modified at 18:51:34 UTC, before round 1 (19:00 UTC), so it is unchanged since round 1.

## 2. Statements (target 5)

The probe is byte-identical to round 1 (`bd95cc9`). The round-1 statement table (band pins 1-5 and BA pins against 1_2 TeX 357-420, 440-512, 600-670) therefore still holds. The one defect was paper-delta coverage of `BAData.supp`. The field is still present, and it is now covered (§3):
```
$ grep -n "supp :" RBM3D/Probe/T2001Endpoints.lean
350:  supp : ∀ n, (μ n).support = Set.Icc (-(e n)) (e n)
$ grep -n "def Admissible" -A 3 RBM3D/Probe/T2001Endpoints.lean
70:def Admissible (d : ℕ) (𝔠 𝔡 : ℝ) (s : SizeSeq) : Prop :=
71-  Tendsto (fun n => s.N d n) atTop atTop ∧
72-    (∀ᶠ n in atTop, ((s.N d n : ℕ) : ℝ) ^ 𝔠 ≤ (s.W n : ℝ)) ∧
73-    ∀ᶠ n in atTop, (s.W n : ℝ) ^ (-(d : ℝ) / 2 + 𝔡) ≤ s.g n ∧ s.g n ≤ 𝔡⁻¹
```
`Admissible` places no condition on `L_n` other than `SizeSeq.three_le_L`, so fixed `L` with large `g` is admissible.

## 3. Repair check (round-1 "Required for resubmission")

1. **Candidate T2001l** (prove report (d), line 254): it states that 1_2:624 fails when `supp μ_N` is not an interval, gives the example `d=3, L=4, g=10`, and says that `BAData d s` is empty and every `T2001_BA_*` pin is vacuous there. The script output is in `## Repair` (lines 260-297). My independent re-check uses its own code (numpy, `η = 1e-4`, grid 0.05 over `[-70,70]`):
```
$ python3 sup.py
components of {rho_N>1e-3} (eta=1e-4, grid 0.05): [(-60.25, -59.8), (-40.6, -39.45), (-20.95, -19.1), (-1.1, 1.1), (19.1, 20.95), (39.45, 40.6), (59.8, 60.25)]
max rho_N on [3,17]: 1.2e-06  total mass ~ 0.999
2 N^c<=W: True W^(-d/2+dd)<=g<=1/dd: True
4 N^c<=W: True W^(-d/2+dd)<=g<=1/dd: True
8 N^c<=W: True W^(-d/2+dd)<=g<=1/dd: True
```
   The support of `μ_N` has seven separated components, and the sequence `L_n=4, g_n=10, W_n=10^n, 𝔠=1/20, 𝔡=1/10` is admissible. This confirms T2001l. Resolved.
2. **Non-vacuity bullet** (line 149): it names both empty-`BAData` classes, odd `L` (T2001d) and non-interval support (T2001l), and it says "the BA pins are non-vacuous only where `supp μ_n` is a symmetric interval". Resolved.
3. **Freeze-ticket proposal** (line 256): it gives option (1), `dist(E, ℝ∖supp μ_N) ≥ κ` without `BAData.supp`, and option (2), a restriction `L_n → ∞` even or `g_n ≤ 1`, marked "to be checked, not done here". It is a proposal for the dispatcher, as asked. Resolved.

## 4. Hidden hypotheses, vacuity, cycles, instance

- The pins are closed `Prop`s, with no proofs and no dependence on unproved results.
  - `SizeSeq` has deterministic fields only (`three_le_L`, `W_pos`).
  - `BAData` has the defining properties of `m, μ, e` (self_m, Stieltjes, support).
  - The vacuity classes of `BAData` are now disclosed as T2001d and T2001l.
- The ticket requires no compiled instance for `Prop` pins. `admissible_witnessSeq : Admissible 3 (1/7) (2/5) witnessSeq` compiles at the nondegenerate sequence `L_n = W_n = 4(n+1)`, `g_n = 1/W_n` (axioms in §1).

## 5. Coverage table (target 2): re-check this round

Every class (i) row: each citation in the "Lean on main" column is checked against `git show main:RBM3D/<file>` at the cited line, and each citation in the RBM2D column against `git -C ../RBM2D show c9a24cf:RBM2D/<file>` (declaration name present on the cited line):
```
$ python3 - <<'EOF' ... (columns 9 and 12 of rows with class = i)
main class-i citations: match 54 mismatch 0 []
RBM2D class-i citations: match 15 mismatch 0 []
```
In round 1 the label-completeness scan (617 uncommented labels, 0 absent; 97 theorem-like environment labels, all in the table) and the row-by-row paper comparisons (16 rows) were done on this same, unchanged file. Target 2 PASS.

## 6. Targets 1, 3, 4, 6

None of these sections changed in substance since round 1. The only change in (b) is the BA bullet at line 149.
- Target 1 (endpoint table): PASS.
- Target 3 (gap list, grouped by gate, with the gate-less flag): PASS. The BA gap row (line 176) cites T2001c, d, g. T2001l is in (d).
- Target 4 (`ThetaDecay`, … in `Interface.lean`): the constants are `∃` after `(d g m …)`, so they depend on `g, m`, while `lem_propTH` has constants depending on `d` (resp. `d, κ`). This is correct, as in round 1. PASS.
- Target 6 (proposed tickets): PASS.

## 7. Paper-delta coverage

T2001a-l cover every Lean/paper difference found in round 1 and in this round:
- sequence form;
- `∩_z`;
- BA universality at the same `E`;
- odd `L`;
- non-interval support (new, T2001l);
- block distance;
- `A ≠ ∅`;
- the 7_8:1797 typo;
- the readings;
- the three findings on `main`.

`docs/paper-deltas.md` contains no entry on this yet (the dispatcher numbers the candidates). Coverage complete.

## Observations (no RETURN)

- O1 (carried over): row 148 `claim:TTk` is class i, but the Lean statement needs `1 ≤ ℓ` where the paper has `0 ≤ ℓ`. That makes it closer to iii. No pin depends on it.
- O2: T2001c (the literal BA universality fails when `ρ_N(E) ≠ ρ_sc(E)`) and T2001l (the `e_g` support) are substantive and decide the BA pin form. They are for the dispatcher/Jun at freeze time, not for this survey.
- O3: the claim in option (2) of line 256 that the support is an interval for `g_n ≤ 1` is unverified, and the report says so.
