Auditor model: claude-opus-5-5
# T2110 audit (round 1): ST2-14 `Induction/OptL2a.lean`

Written Sun Oct  4 05:49:17 UTC 2026 (`date -u`). Audit worktree `RBM3D-wt/T2110-audit1`, detached at `t/T2110` = 879daff
(merge base 6187713; main now f590e74). Scratch: `scratchpad/T2110/`.

## Build, axioms, hygiene, diff
```
$ lake build RBM3D.Induction.OptL2a 2>&1 | grep -E "error|OptL2a|Build completed"
⚠ [3766/3766] Replayed RBM3D.Induction.OptL2a
warning: RBM3D/Induction/OptL2a.lean:10:0: The module doc-string for a file should be the first command after the imports.
warning: RBM3D/Induction/OptL2a.lean:284:19: Variable name `hκ` is not explicitly referenced.
warning: RBM3D/Induction/OptL2a.lean:284:32: Variable name `hε` is not explicitly referenced.
warning: RBM3D/Induction/OptL2a.lean:284:45: Variable name `h𝔡` is not explicitly referenced.
Build completed successfully (3766 jobs).
$ lake env lean scratchpad/T2110/ax.lean
'RBM.Gauss.Sizes.stOptL2a_drift' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.stOptL2a_martingale' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.stOptL2a_gronwall' depends on axioms: [propext, Classical.choice, Quot.sound]
$ grep -nE "sorry|admit|native_decide|^axiom|maxHeartbeats" RBM3D/Induction/OptL2a.lean ; echo $?
1
$ grep -n "^structure\|^class\|^def .*: Prop\|^instance" RBM3D/Induction/OptL2a.lean ; echo $?
1
$ git diff --name-only main...t/T2110
RBM3D/Induction/OptL2a.lean
$ git grep -n "OptL2a" main -- RBM3D RBM3D.lean     (name clash)
(no output)
```
Only the sole writable file is touched; `Test/Axioms.lean` not needed (no new `Prop`-valued definition; new defs
`OptL2aJ`, `OptL2alam`, `OptL2aPsi` are `ℝ`-valued). No frozen signature edited (new file only).

## Statements (extracted by script from the file; identical to the prove report's paste)
```
$ python3 extract.py > stmts.txt ; awk <first lean block of T2110-prove.md> > report_stmts.txt ; diff stmts.txt report_stmts.txt && echo IDENTICAL
IDENTICAL
```
(Statements at `OptL2a.lean:983` `stOptL2a_drift`, `:1078` `stOptL2a_martingale`, `:1260` `stOptL2a_gronwall`; not
repeated here, see the prove report (b).) Checked against `3_5:466–486` and the ticket's targets 1–3:

**Target 1 `stOptL2a_drift`** (`(l>0EQ)` integrand). `3 ≤ d`, `STLWB d` (owed pin, hypothesis); `∃ C₀ > 0` chosen after
`κ ε 𝔡` only, before `𝔠, sz, z, s, T` (DECISIONS §29: free of `W, L, λ`). Premises: `STFlow`, `0 ≤ s ≤ T ≤ lemT`,
`𝔠d ≤ 1/2`, first conjunct of `(con_st_ind)` at `(s,T)`, `STStep1Loop/Weak` on `[s,T]`. Conclusion: `HighProbAt`, for all
grid `j ≤ K_n`, all `σ ∈ {+,-}², a`: `‖STgDrift‖ ≤ C₀/(1-u_j)·J_j + N^τ η_{u_j}⁻¹ λ^{3/2}`, with `J_j = max_{σ,a}|(𝓛-𝒦)^{(2)}|`
(`OptL2aJ`, sup over all of `STLab`) and `λ = ((1-s)/(1-T))W^{-d}B_{T,0}` = paper's `W^{-c₀}` (`OptL2alam`). `STgDrift`
(`Step2Defs:496`) is the full drift `Θ∘(𝓛-𝒦) + 𝓔^{LK×LK} + 𝓔^{G̃}` of `(LK_simple)`. The `η⁻¹λ^{3/2}` per-time error is
`lem:LWterm`'s form (`STLWB`: `η_t⁻¹Ψ(0)Ψ²`); its `Δ`-sum gives the paper's integrated `O_≺(W^{-3c₀/2})` up to `log ρ`.
The ticket's per-time wording "`O_≺((W^{-d}B_{s,0})² + W^{-3c₀/2})`" mixes in the initial value; the Lean split
(initial value in Target 3) is the paper's mathematics. Covered by `T2110e`. **PASS.**

**Target 2 `stOptL2a_martingale`.** `0 < d`, `STGridMart d` (owed pin, hypothesis); same premises; `∀ τ D > 0, ∃ CK ≥ 0`,
`∀ K = ⌈N^CK⌉`: `∃ Mart Rem` with the pathP-a.e. decomposition of `STGridMartAt` verbatim, `‖Rem‖ ≤ N^{-2}` eventually, and
`P(∃ i, k ≤ K: N^τ λ^{5/4} < ‖Mart‖) ≤ N^{-D}` eventually: the ticket's `|ΣΔMart| ≺ W^{-5c₀/4}` with Markov inside the
pin (`3_5:476–478`). Uses merged `stEMn2Poly_holds` (`OptL2a.lean:449`). **PASS.**

**Target 3 `stOptL2a_gronwall`** (`(eq:Gronwall_2L_max)`, `3_5:481`). `3 ≤ d`, `STLWB d`, `STGridMart d` (hypotheses);
adds `STLK` at `s` (the paper's `(Eq:L-KGt+IND)`, `n = 2`). Conclusion: `∀ τ D > 0, ∃ CK`, `∀ K = ⌈N^CK⌉`, eventually
`P(¬ ∀ k ≤ K_n: J_k ≤ N^τ(B_s² + λ^{5/4}) + Δ Σ_{j<k} C₀/(1-u_j) J_j) ≤ N^{-D}`. This is the paper's display with
`∫ → Δ Σ` (grid form, existing deltas D90 / `3_5:134` grid entry) and `O_≺` as `N^τ`. The `𝓔^{G̃}` sum is absorbed into
the `λ^{5/4}` term, as in the paper. Shape check that the event feeds `ST_gronwall` (`Step2Core:56`) verbatim
(α constant, β_j = C₀/(1-u_j) ≥ 0):
```
$ cat scratchpad/T2110/shape.lean   (core)
example ... (h : ∀ k, k ≤ K n → OptL2aJ … k … ≤ N^τ * (B_s^2 + λ^(5/4)) + gridStep * ∑ j ∈ range k, C₀/(1-u_j) * OptL2aJ … j …) :=
  ST_gronwall (m := K n) hΔ (α := fun _ => …) (β := fun j => C₀ / (1 - gridTime s T K n j)) (J := …)
    (fun _ _ _ _ _ => le_rfl) (fun j hj => div_nonneg hC₀.le (by linarith [hT j hj])) h
$ lake env lean scratchpad/T2110/shape.lean; echo exit=$?
exit=0
```
**PASS.**

Paper check of the remaining steps (ST2-15) against `3_5:493–512`, by hand with merged signatures: for a section `T`,
`ρ_T = (1-s)/(1-T) ≤ B_T^{-𝔠d}` (first conjunct); `B_s ≤ B_T` (`STBctl_mono`, `ScaleFacts:74`: `s ≤ u < 1 → Bctl s ≤ Bctl u`),
so `ρ^{C₀}B_s² ≤ B_T·B_T^{1-C₀𝔠d}` and `ρ^{C₀}λ^{5/4} = B_T·ρ^{C₀+5/4}B_T^{1/4}`; both `≪ B_T` for `𝔠d(C₀+5/4) < 1/4`. The
first conjunct restricts from `(s,t)` to `(s,T)` for `𝔠d > 0` (pin `STOptL2` has `0 < 𝔠d`) by the same monotonicity.
Target 3 is therefore usable by ST2-15.

## No vacuity, hidden hypotheses, cycles
- No structure/class/`Prop` definition in the file (grep above); all hypotheses are in the signatures.
- Dependencies: merged `stNewKLK_holds` (`:999`), `stEMn2Poly_holds` (`:449`), `ST_grid_whp_of_sections` (`:487,:519`),
  `ST_event_weak` (`:1029`), `ST_gronwall`; owed pins `STLWB`, `STGridMart` enter only as explicit hypotheses (ticket's
  pattern, DECISIONS §32). No pin of this ticket (`STOptL2`) is assumed. No cycle.
- External-type hypotheses at the instance: `B_t ≤ 1.1W^{-3} → 0`, `N → ∞` (`sz0_admissible`, merged); `STConStInd`
  holds in full at the instance data (`conStInd_inst`, `Defs.lean:516`), not only its first conjunct.
- `𝔠d` is not required positive (more general than needed; `𝔠d ≤ 0` forces `T = s` eventually, theorem still true).

## Compiled nonempty instances (in the same file, compiled by the build above)
```
$ grep -n "^example" RBM3D/Induction/OptL2a.lean
1441:example (hLWB : STLWB 3) (hS1L : STStep1Loop sz0 (STflowE z0) sInst tInst)
1459:example (hGM : STGridMart 3) (hS1L : STStep1Loop sz0 (STflowE z0) sInst tInst)
1466:example (hLWB : STLWB 3) (hGM : STGridMart 3) (hLK : STLK sz0 (STflowE z0) sInst)
```
Data: `d = 3`, merged `sz0` (`N_n → ∞`), `z0`, `flow_z0 : STFlow sz0 (1/10) (1/10) (1/6) (1/10) z0`, `s ≡ 0`, `T ≡ 1/16`
(`hs0`, `hst`, `htT` via `sixteenth_le_lemT`), `κ=ε=𝔡=1/10`, `𝔠d = 1/26`, `τ = D = 1`, `K_n = ⌈N_n^CK⌉ ≥ 1`. Discharged:
`3 ≤ 3`, positivity, `STFlow`, time ranges, `𝔠d ≤ 1/2`, `(con_st_ind)` first conjunct (`OptL2a_hcon` from `conStInd_inst`).
Kept as hypotheses: owed pins `STLWB`, `STGridMart`; stochastic premises `STLK`, `STStep1Loop`, `STStep1Weak` (Step 1 /
induction outputs about the random model, not deterministic). Nondegenerate (`s < T`, `N → ∞`, nonempty `STLab`).
All three endpoint theorems covered. **PASS.**

## Paper deltas
Lean/paper differences and coverage: per-time vs uniform `u` (no net) `T2110a`; `W^{-c₀} := λ` `T2110b`;
`Ψ = min(√λ, W^{-ε₀})` `T2110c`; only the first conjunct of `(con_st_ind)` + `𝔠d ≤ 1/2` `T2110d`; explicit `O_≺` terms
(`η⁻¹λ^{3/2}`, `N^{-2}`, `N^τλ^{5/4}`, constant α) `T2110e`; `3 ≤ d` `T2110f`; grid instead of `∫` (existing D90 and
the `(int_K-L_ST)` grid entry, `docs/paper-deltas.md:403,773`). Every difference found is covered.

## Observations (no verdict effect)
- O1. The cut moves to ST2-15 more than the ticket's "only `ST_gronwall`, the `𝔠_d` choice and the net": ST2-15 also
  needs restriction of `STStep1Loop/Weak` and `(con_st_ind)` from `[s,t]` to `[s,T]`, `ST_model_le_path`,
  `ST_PT_of_sections`. Preflight was authorized to fix the cut and recorded it; the net is not needed (`PrecPT`).
- O2. Forward to the dispatcher for the ST2-15 ticket text (`T2110f`): `stOptL2_of_pins` needs `(hd : 3 ≤ d)` since
  `STNewKLK d` starts `3 ≤ d →` while `STOptL2 d`, `STLWB d` do not. No pin of this ticket is affected.
- O3. Lint warnings in the new file: module doc-string position (`:10`), unused `hκ hε h𝔡` in `OptL2a_premises` (`:284`).
- O4. The branch base is 6187713; main has since moved to f590e74 (T2106, another file). The diff is still one file.

## Verdict
| target | statement | vacuity/hidden/cycle | instance | build/axioms | deltas | verdict |
|---|---|---|---|---|---|---|
| `stOptL2a_drift` | ok | ok | `:1441` | ok | `T2110b–e` | PASS |
| `stOptL2a_martingale` | ok | ok | `:1459` | ok | `T2110b,e` | PASS |
| `stOptL2a_gronwall` | ok | ok | `:1466` | ok | `T2110a–f` | PASS |

**T2110: PASS.** No dispatcher sign-off needed for this ticket (O2 is a note for the ST2-15 ticket text).
