Auditor model: claude-opus-5-5

# T2384 (BA-K11, `RBM3D/BA/KWardIneq.lean`, `lem_wardineq_K`) — audit round 1 — Sat Oct 10 13:04:36 UTC 2026

Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2384-audit1`, detached at `t/T2384` = `7dac9b5` (merge-base `5bc433a`); scratch `scratchpad/T2384/`.

## 1. Diff scope, forbidden tokens

```
$ git diff --name-only main...t/T2384
RBM3D/BA/KWardIneq.lean
$ git show t/T2384:RBM3D/BA/KWardIneq.lean > f.lean; wc -l < f.lean     # stop line 2000
    1338
$ grep -nE '\bsorry\b|\badmit\b|native_decide|^\s*axiom\b|set_option.*(maxHeartbeats|debug)' f.lean | wc -l
       0
$ grep -n import f.lean      # never `import RBM3D`
6:import RBM3D.BA.KInduct
7:import RBM3D.BA.KMolecule
8:import RBM3D.BA.KPure
```
Only the sole writable file; no frozen signature touched (no other file in the diff).

## 2. Build and axioms (audit worktree)

```
$ rm .lake/build/{ir,lib/lean}/RBM3D/BA/KWardIneq.*   # 8 artifacts, forced rebuild; 13:01:01 UTC
$ lake build RBM3D.BA.KWardIneq ; echo exit=$?
✔ [3770/3770] Built RBM3D.BA.KWardIneq (5.5s)
Build completed successfully (3770 jobs).
exit=0                                   # grep -c error build2.log = 0
$ lake env lean RBM3D/BA/KWardIneq.lean ; echo exit=$?     # fresh elaboration, 13:01:15 -> 13:01:21 UTC
exit=0                                   # 0 error lines, 0 warning lines
$ lake env lean ax.lean     # #print axioms of the 13 public declarations
'RBM.BA.BAWardIneqAt' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.KWardIneq_IndAt' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.KWardIneq_MolAt' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BAWardKpiAt' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.KWardIneq_Data' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baWardMol_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.KWardIneq_IndAt_of_abs' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baWardIneq_two' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baWardKpi_empty_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baWardKpi_step' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baWardKpi_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baWardIneq_of_Kpi' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baWardIneq_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
```
Merge simulation (same worktree, temporarily `git checkout --detach main` = `69b7abc` + the branch file as an untracked copy; reverted after):
```
$ lake build RBM3D RBM3D.BA.KWardIneq ; echo exit=$?      # 13:01:38 -> 13:03:28 UTC
✔ [4198/4200] Built RBM3D.BA.KWardIneq (6.0s)
Build completed successfully (4200 jobs).
exit=0
$ printf 'import RBM3D\nimport RBM3D.BA.KWardIneq\n#assert_rbm_axioms\n' > pre.lean; lake env lean pre.lean; echo exit=$?   # registry pre-check
1:axiom audit: 11045 theorems, 3239 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
91:premises found by scanning: 113 (borrowed 1, owed 48, structural 45, refuted 6, superseded 13).
exit=0
$ lake env lean docs/tickets/checks/T2384-check.lean; echo exit=$?
exit=0                                   # 0 error lines
```

## 3. Statements against the paper and the pins

Paper `3_5_Loop_Hierarchy.tex:1001-1012`: for `n ≥ 2`, `t ∈ [0,1)`, `max_σ Σ_{a_n} |𝒦^{(n)}_{t,σ,a}| ≺ (W^d η_t)⁻¹ (W^{-d}B_{t,0})^{n-2}`;
`1_2:721`: `η_t = (1-t) Im m`. Script diff of `BAWardIneqAt` against the binders of `BAKBoundAt` (`BA/KInduct.lean:54-60`) and the band pin
`KLwardIneqAt` (`Loop/KLWardIneq.lean:90-94`):
```
$ diff kb.txt wi.txt          # BAKBoundAt vs BAWardIneqAt (binder lines 3-5 identical)
<       BAReal d L g κ E m → ∀ t : ℝ, 0 ≤ t → t < 1 → ∀ (σ : Fin n → Bool) (a : Fin n → Zd d L),
<         ‖BAKsol d L W (BAMsigma d L (BAMB d L g (E : ℂ) m)) (PropSpin m) t (KLloopOf d L σ a)‖
---
>       BAReal d L g κ E m → ∀ t : ℝ, 0 ≤ t → t < 1 → ∀ (σ : Fin n → Bool) (a : Fin (n - 1) → Zd d L),
>         ∑ x : Zd d L,
>             ‖BAKsol d L W (BAMsigma d L (BAMB d L g (E : ℂ) m)) (PropSpin m) t ⟨List.ofFn σ, List.ofFn a ++ [x]⟩‖
>           ≤ C * (L : ℝ) ^ τ * (((W : ℝ) ^ d) * ((1 - t) * m.im))⁻¹ *
>               (((W : ℝ) ^ d)⁻¹ * Bparam d L g t 0) ^ (n - 2)
```
Band `KLwardIneqAt` (`diff kw.txt wi.txt`): same body, `KLPar` -> BA binders, `Gauss.etaT` -> `(1-t)*m.im`, `KLK` -> `BAKsol`.
- `BAWardIneqAt d n Λ κ`: `∀τ>0 ∃C>0` before all of `L ≥ 3, W ≥ 1, g ∈ (0,Λ], E, m, BAReal, t ∈ [0,1), σ, a`; `∀σ` = `max_σ`; sum over the last
  label; loss `L^τ` (`≺`); exponent `n-2`; `(W^d η_t)⁻¹`. Matches `(wardineq_K)`. PASS.
- `BAWardKpiAt d m`: twin of `KLWardIneq_KpiAt` (`:662`) = `(eq:K-pi-bound_partial)` (`A:813-815`, `η_t⁻¹ B^{n-2}`, `n = m+1`). PASS.
- `KWardIneq_IndAt d k`: `(eq:ind-step-bound)` (`A:703-705`) at every root `r` with `σ r ≠ σ(r+1)`, `Σ_b |Σ_{δ_r=b} Σ^∅ ∏_{j≠r} Θ| ≤ C L^τ B^{k-2}`;
  `KWardIneq_IndAt_of_abs` concludes it from `IndStepAbs` (`Loop/KLIndStepB.lean:77`, the output of `indStepAbs_of`, `:879`) at the family
  `KWardIneq_Data` (proof: field-wise application, read above). PASS.
- `KWardIneq_MolAt d k`: `(eq:molecule-decay)` (`A:691`); proved by `baWardMol_holds` from K07 `baSig_decay` (no extra hypothesis). PASS.
- Theorems `baWardIneq_two` (no premise), `baWardKpi_empty_bound` (`IndAt` at `k = m+1`), `baWardKpi_step` (`IndAt` on `[3,m+1]`, IH `hout`
  on `[2,m)`), `baWardKpi_holds`, `baWardIneq_of_Kpi`, `baWardIneq_holds` (`3 ≤ d`, `2 ≤ n`, `0<Λ`, `0<κ`, `IndAt` on `[3,n]`): statements
  as listed in the 1a table (`T2384-prove.md:12-18`) and in (b) (`:171-205`), checked against the file (`grep -n` of declaration lines above).
- **Conditional form.** `baWardIneq_holds` is `lem_wardineq_K` conditional on `(eq:ind-step-bound)`. This is the paper's own dependency
  (`A:809`: "follows from the bound (eq:ind-step-bound) together with an induction") and the design order (K11 needs K02, K10; K12 needs
  K09b, K11: `T2360-design.md:132-133`); the ticket lets the 1a fix the statements and the 1a-audit passed this form. Labelled as conditional
  (`T2384c`); not claimed as the unconditional lemma. Constants depend on `(d,n,Λ,κ,τ)` only (`∃C` before every data binder); no smallness
  of `g` in any signature (1155 C1).

## 4. Hidden hypotheses, vacuity, cycles

- `KWardIneq_Data` fields: `L, hL : 3 ≤ L, g, hg, hgΛ, E, m, hr : BAReal …, t, ht0, ht1` — exactly the binders of `KWardIneq_IndAt`; it is
  used only as the index `ι` of `IndStepAbs`/`SigDecayAbs`. No target statement takes a structure argument. No hidden hypothesis.
- The only premise of the endpoint theorems is `KWardIneq_IndAt`, the paper's `(eq:ind-step-bound)`, to be produced by K12 through
  `KWardIneq_IndAt_of_abs` ∘ `indStepAbs_of`. Limit check present (`T2384-prove.md:49-57`, `C_ind` bounded for `q = 4..24`, `d = 1` mirror);
  the band analogue is proved (`KLindStepPin_holds`). Not refuted; not `False`.
- No cycle: imports are `BA.KInduct`, `BA.KMolecule`, `BA.KPure` (all merged); `KWardIneq_IndAt` is not defined from any target.
- `1 ≤ W` is an unused binder of `BAWardIneqAt` (as in `BAKBoundAt`); harmless (weakens nothing at `W ≥ 1`).

## 5. Compiled nonempty instances (`KWardIneqInst`, lines 1209-1337; all compile, §2)

Data: merged flow point `P` (`BA/MFixedPoint.lean:893`), `(d,L) = (3,4)`, `Λ = 10`, `κ = Im m₀` (`P.real.1.1 : 0 < κ`), `W = 2`, `t = 1/2`,
`τ = 1`, `BAReal` discharged by `P.real`, `0 < g₀ ≤ 10` by `P.g0_pos`, `P.g0_le`.
```
$ grep -n "^example" RBM3D/BA/KWardIneq.lean | cut -d: -f1
1209 1213 1231 1254 1269 1289 1298 1307 1330
```
| endpoint | example | data | hypotheses left |
|---|---|---|---|
| `baWardIneq_two` | 1213 | `σ = (+,-)`, `(+,+)`, `a₁ = 0` | none |
| `baWardIneq_holds` | 1231 | `n = 3` `σ=(+,-,+)`; `n = 4` `σ=(+,+,-,-)`, spread labels | `IndAt` at `k = 3,4` |
| `baWardKpi_empty_bound` | 1254 | `m = 3`, long last leaf `(+,+,-,-)`, short `(+,+,-,+)` | `IndAt` at `k = 4` |
| `baWardKpi_step` | 1269 | `m = 3`, layers `∅`, `{(0,2)}`, `{(1,3)}`; `hout` by `baWardKpi_holds` | `IndAt` at `k = 3,4` |
| `baWardKpi_holds`, `baWardIneq_of_Kpi` | 1289 | `m = 2, 3` | `IndAt` |
| `baWardMol_holds` | 1298 | `k = 4`, distinct labels | none |
| `KWardIneq_IndAt_of_abs` | 1307 | `IndStepAbs` at sizes 3, 4 → `(wardineq_K)` at `n = 4` | `IndStepAbs` (K09b output) |
| nondegeneracy | 1330 | `decide`: last leaf long/short as claimed; `KLTSPlong` of both layers nonempty | none |

`IndAt`/`IndStepAbs` is another gate's statement (K12 via K09b), allowed to stay (CLAUDE.md §4 step 2). No `N = 0`, empty index, collapsed
window, `False` premise or huge witness (`N = 64`). PASS.

## 6. Paper deltas

| Lean/paper difference | covered by |
|---|---|
| `≺` read as `C(d,n,Λ,κ,τ) L^τ`, uniform in `L ≥ 3, W ≥ 1, g ∈ (0,Λ]`, data, `t`; `η_t = (1-t) Im m` | `T2384a` |
| short last leaf `σ_n = σ_1` not covered by `A:816-818` (`Θ^{(+,-)}` only); proved here | `T2384b` |
| conditional on `(eq:ind-step-bound)` (`KWardIneq_IndAt`, every root `r`); induction on vertices, not molecules | `T2384c` |
| BA chord `tΘ`, one glue sum, no `S^{(B)}` in the cut | `T2381a` (reused; not yet numbered in `docs/paper-deltas.md`: 0 grep hits) |
Every difference found in §3 is covered.

## 7. Observations (no RETURN)

- The 1a-audit (`T2384-1a-audit.md` §6) asked for dispatcher sign-off on D1 (owed registry line vs inline `IndStepAbs`). 1b took a third
  route inside the sole file: keep `KWardIneq_IndAt` and add the bridge `KWardIneq_IndAt_of_abs` (+ `KWardIneq_Data`, its `NeZero` instance),
  so no `Test/Axioms.lean` line is needed (pre-check above passes on `main` + file). The 1a table's statements are unchanged; the three
  additions carry the file stem (§3 (E)). Recorded for the dispatcher's ledger; no statement defect.
- `import RBM3D.BA.KWard` unused (`baK_ward` not in `A:811-826`; D3). Branch base `5bc433a` < `main` `69b7abc`; §2 simulation clean.

## Verdict

All targets (`BAWardIneqAt`, `BAWardKpiAt`, `KWardIneq_IndAt`, `KWardIneq_MolAt`, `baWardIneq_two`, `baWardKpi_empty_bound`,
`baWardKpi_step`, `baWardKpi_holds`, `baWardIneq_of_Kpi`, `baWardIneq_holds`, `baWardMol_holds`, `KWardIneq_IndAt_of_abs`): **PASS**
(conditional form of `lem_wardineq_K` as fixed by the audited 1a; premise `(eq:ind-step-bound)` owed by K12). No dispatcher sign-off needed.
Hub: root import `import RBM3D.BA.KWardIneq`; no `Test/Axioms.lean` line.
