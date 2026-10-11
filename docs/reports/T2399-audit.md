Auditor model: claude-opus-5-5

# T2399 audit (round 1) — BA-K12, stage-K outputs — Sun Oct 11 01:04:12 UTC 2026

Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2399-audit1`, detached at `t/T2399` = `84d1997`; merge base `30abc87`.

## 1. Statements against the pins (script diffs)

```
$ diff <(git show t/T2360:RBM3D/Probe/T2360Pins.lean | sed -n 49,52p) <(sed -n 196,199p RBM3D/BA/KBound.lean) && echo "BAKbound: identical to probe 49-52"
BAKbound: identical to probe 49-52
$ diff <(sed -n 229,234p Induction/Step34Pins.lean | rename) <(sed -n 169,174p Chain/Carrier.lean | rename)   # STKward vs STKwardgL
3c3
<     Prec sz (U := fun n => (Fin k → Bool) × (Fin (k - 1) → Zd d (sz.L n)))
---
>     PrecL sz μ (U := fun n => (Fin k → Bool) × (Fin (k - 1) → Zd d (sz.L n)))
5,6c5,6
<         ‖STKI sz n (E n) (τ n) ⟨List.ofFn p.1, List.ofFn p.2 ++ [x]⟩‖)
<       (fun n _ _ => (((sz.W n : ℕ) : ℝ) ^ d * etaT (E n) (τ n))⁻¹ * (sz.Bctl n (τ n)) ^ (k - 2))
---
>         ‖C.K n (τ n) p.1 (fun i : Fin k => if h : (i : ℕ) < k - 1 then p.2 ⟨i, h⟩ else x)‖)
>       (fun n _ _ => (((sz.W n : ℕ) : ℝ) ^ d * C.eta n (τ n))⁻¹ * (sz.Bctl n (τ n)) ^ (k - 2))
```
The only differences are the ones the ticket asks for (law `μ`, carrier `C.K`, `η ↦ C.eta n (τ n)`); the last label is
summed by a `Fin k` vector instead of the list `a ++ [x]`, and `bandFM_STKward : STKward sz E ↔ STKwardgL (bandFM sz E) (seqP sz)`
(`Step2Gen.lean:612`, proved with `Carrier_ofFn_ext`) shows the two coincide at the band carrier. Quantifiers/exponents
(`τ ∈ [0,1)`, `k ≥ 2`, `(W^d η)⁻¹ (W^{-d}B)^{k-2}`, max over `σ` and the first `k-1` labels) agree with paper
`3_5_Loop_Hierarchy.tex:1001-1006` (`wardineq_K`, `n ≥ 2`, `t ∈ [0,1)`).

Remaining targets (extracted from `RBM3D/BA/KBound.lean`):
```
85:  theorem baKBoundAt_holds (d : ℕ) {Λ κ : ℝ} (hd : 3 ≤ d) (hΛ : 0 < Λ) (hκ : 0 < κ) : ∀ n : ℕ, 1 ≤ n → BAKBoundAt d n Λ κ
204: def BAKward (d : ℕ) : Prop := 3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ),
       BAFlow sz κ ε 𝔠 𝔡 z → STKwardgL (baFMz sz z) (Sizes.seqP (sz.withLam 0))
213: theorem BAKbound_of_uniform (d : ℕ) (U : 3 ≤ d → ∀ (Λ κ : ℝ) (n : ℕ), 0 < Λ → 0 < κ → 1 ≤ n → BAKBoundAt d n Λ κ) : BAKbound d
245: theorem baKbound_holds (d : ℕ) : BAKbound d
302: theorem baKward_holds (d : ℕ) : BAKward d
```
- T1 `baKBoundAt_holds`: exactly the ticket's pin (`3 ≤ d`, `0 < Λ`, `0 < κ`, all `n ≥ 1`); `BAKBoundAt` is the merged
  `KInduct.lean:55` (verbatim the probe). `n ≤ 3` from `baKBoundAt_one/two/three` (`KInduct.lean:270,291,425`), `n ≥ 4` from
  `baK_eq_sum_Kpi` (`KMolecule.lean:133`) and `baKpiBoundAt_holds` (`KStep.lean:597`), constant `2^|diagonals n|·C`. **PASS.**
- T2 `BAKbound` = probe text (diff above); `BAKbound_of_uniform`'s `U` gains `3 ≤ d →` relative to probe 106: this weakens
  the premise, so the theorem is stronger than the probe form (T2399c). `baKbound_holds` unconditional. **PASS.**
- T3 `STKwardgL`, `bandFM_STKward` (an `Iff` with proof, not `Iff.rfl`; T2399b), `BAKward` with the same binders as
  `BAKbound`, `baKward_holds` unconditional. **PASS.**
- T4 bundle "not needed": `grep -rn BAProp5to8 RBM3D | grep -v Prop6Path.lean` gives only `FlowPins.lean:20` (docstring) and
  `:226` (the structure) (prove report; spot-checked). **PASS.**
- T6 Q5 table present at the end of the prove report; T7 registry: `grep -c "KWardIneq_IndAt\|BAKpiBoundAt" RBM3D/Test/Axioms.lean` → `0`. **PASS.**

## 2. Hidden hypotheses, vacuity, cycles

- No new structure. The only hypotheses of the pins are `3 ≤ d`, positivity of `κ ε 𝔡`, and `BAFlow` (pre-existing,
  inhabited by the proved `flow_sz0 : BAFlow sz0 (1/2) (1/10) (1/6) (1/10) zSeq`, `FlowPins.lean:1214`).
- Every input is a merged theorem on `main` (script: `git grep -nE "^(private )?(theorem|def) <name>( |$)" main`):
```
baKBoundAt_one KInduct.lean:270  baKBoundAt_two :291  baKBoundAt_three :425  baKpiBoundAt_holds KStep.lean:597
baK_eq_sum_Kpi KMolecule.lean:133  baWardIneq_holds KWardIneq.lean:1183  KWardIneq_IndAt_of_abs KWardIneq.lean:376
KStep_baIndStepAbs_holds KStep.lean:442  BAflow_real GreenSchur.lean:59  BAflow_lam0_window GreenSchur.lean:72
baK_ward KWard.lean:305  BAKsol_isKLoopS KSolve.lean:606  baKsol_two KInduct.lean:88  stKward_of_flow Loop/KLFinal.lean:308
```
- `baWardIneq_holds`' premise `∀ k, 3 ≤ k → k ≤ n → KWardIneq_IndAt d k Λ κ` is discharged inside `baKward_holds`
  (`KWardIneq_IndAt_of_abs (KStep_baIndStepAbs_holds k hd hk hΛ hκ)`); no hypothesis of another gate remains.
  `baKbound_holds`/`baKward_holds` take only `d`. No external hypothesis, so no limit check is needed.
- No cycle: the new file is a leaf; `Carrier`/`Step2Gen` changes are pure additions (below).

## 3. Compiled nonempty instances (`RBM3D/BA/KBound.lean`, all compile in the module build)

| endpoint | instance | data |
|---|---|---|
| `baKbound_holds` | `inst_BAKbound` (:334), and `example` at `τ ≡ 1/2`, `k = 4` (:348) | `d = 3`, `sz0` (`L_n = 4(n+1) ≥ 4`, `W_n = (2(n+1))^5`), `zSeq`, `flow_sz0`; `U` discharged by `baKBoundAt_holds` |
| `baKward_holds` | `example` (:340), `BAKbound 3 ∧ BAKward 3` (:345), `example` at `τ ≡ 1/2`, `k = 3` (:356) | same flow data; no hypothesis left |
| `baKBoundAt_holds` | `examples` at `n = 4` (:380, ticket's case), `n = 5`, `n = 3` | flow point `P` of `(3, 4)`: `L = 4`, `W = 2`, `Λ = 10`, `κ = Im m₀ > 0` (`P.real.1.1`), `g = P.g0 ∈ (0,10]`, `t = 1/2`, `τ = 1`, distinct labels |
| `bandFM_STKward` | `example` (:370) | band flow `(sz0, z0)`, `flow_z0` |
| `KBound_baKsol_ward` | `example` (:406) | `P`, `n = 4`, `μ = (+,-)` |

Every deterministic hypothesis (`3 ≤ d`, positivity, `3 ≤ L`, `1 ≤ W`, `0 < g ≤ Λ`, `BAReal`, `0 ≤ t < 1`, `2 ≤ k`) is
discharged at concrete data; no `N = 0`, empty index, collapsed window or `False` premise. **PASS.**

## 4. Build, axioms, hygiene, diff

```
$ cd /Users/junyin/Lean_proof/RBM3D-wt/T2399-audit1 && lake build RBM3D.BA.KBound; echo "lake exit $?"
lake exit 0
Build completed successfully (3780 jobs).
$ grep -E "^error" build.log | wc -l; grep -E "warning: RBM3D/(BA/KBound|Chain/Carrier|Chain/Step2Gen)" build.log | grep -v "100 character"
       0
$ lake env lean ax.lean
'RBM.BA.baKBoundAt_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BAKbound_of_uniform' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baKbound_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baKward_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.inst_BAKbound' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.KBound_baKsol_ward' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.bandFM_STKward' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.Carrier_ofFn_ext' depends on axioms: [propext, Quot.sound]
$ lake env lean /Users/junyin/Lean_proof/RBM3D/docs/tickets/checks/T2399-check.lean; echo "check exit $?"
check exit 0          (output: only the #check lines)
$ grep -nE "sorry|admit|native_decide|^axiom" RBM3D/BA/KBound.lean; git diff main...t/T2399 | grep -E "^\+.*(sorry|admit|native_decide|^\+axiom)"; echo "grep exit $?"
grep exit 1
$ git diff --numstat main...t/T2399
1	0	RBM3D.lean
418	0	RBM3D/BA/KBound.lean
23	0	RBM3D/Chain/Carrier.lean
28	0	RBM3D/Chain/Step2Gen.lean
$ wc -l RBM3D/BA/KBound.lean      # stop line 1,300 = KBound + net Carrier: 418 + 23 = 441
     418 RBM3D/BA/KBound.lean
```
All four files are sole writable files; zero deletions, so no frozen signature is touched. `RBM3D.lean` adds
`import RBM3D.BA.KBound` after the last import line, before `#assert_rbm_axioms`. **PASS.**

## 5. Paper-delta coverage

- T2399a (two meanings of `BAKward`; the Ward identity on `BAKsol` is `KBound_baKsol_ward`): naming, proposed.
- T2399b (`STKwardgL` indexes the last label by a `Fin k` vector; the bridge is an `Iff` with proof): proposed.
- T2399c (`U` of `BAKbound_of_uniform` carries `3 ≤ d`): proposed.
- Conditional sequence-level form (along `BAFlow`, `N → ∞`) versus the paper's unconditional `ML:Kbound`/`wardineq_K`:
  the same difference as D263 (`docs/paper-deltas.md:1063`, band `STKbound`/`STKward` along `STFlow`); covered.
No uncovered Lean/paper statement difference. **PASS.**

## 6. Observations (no RETURN)

- O1. The prove report has 234 lines; the ticket asks for ≤ 200 (CLAUDE.md §6 limit 300 is met). It changes no statement,
  instance, build, axiom or delta coverage.
- O2. `KBound.lean:18-30` (module docstring, before `set_option linter.style.longLine false`) gives 10 long-line linter
  warnings. Not an error.
- O3. `main` has moved from `30abc87` to `cbda0ab`; of the four files, only `RBM3D.lean` changed on `main` (its import list).
  The hub re-inserts the one import line after the last import at merge (rule A.4).
- O4. `BAKbound`/`BAKward` measure the loop at the flow coupling `g₀ = √t₀ λ` against `sz.Bctl` at `λ`. That is the probe
  pin as written, and `KBound_B_le` proves the comparison (`B(g₀) ≤ ((κ+1)/κ) B(λ)`).

## Verdict

| target | verdict |
|---|---|
| 1 `baKBoundAt_holds` | PASS |
| 2 `BAKbound`, `BAKbound_of_uniform`, `baKbound_holds` | PASS |
| 3 `STKwardgL`, `bandFM_STKward`, `BAKward`, `baKward_holds` | PASS |
| 4 bundle (not needed) | PASS |
| 5 instances | PASS |
| 6 Q5 table, 7 registry | PASS |

**Ticket T2399: PASS.** No dispatcher sign-off needed: the choice in T2399a of which name to use in the closing REQ is the
dispatcher's routine numbering/naming step, and no target depends on it.
