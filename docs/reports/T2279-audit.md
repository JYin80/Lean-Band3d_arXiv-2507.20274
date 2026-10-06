Auditor model: claude-opus-5-5

# T2279 audit (round 1): S3-17a `Induction/QBudgetA.lean` — Tue Oct  6 10:42:53 UTC 2026

Branch `t/T2279` at `284e06f`; audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2279-audit1` (detached at `284e06f`).
Scratch files in the scratchpad `T2279/` (`sdiff.py`, `AuditStmt.lean`, `AuditCons.lean`, `build.log`, `inst.out`, `reg.log`).

## 1. Diff, build, axioms, hygiene

```
$ git diff --name-status main...t/T2279
A	RBM3D/Induction/QBudgetA.lean
$ grep -n "^import" RBM3D/Induction/QBudgetA.lean
6:import RBM3D.Induction.QLevelsB
7:import RBM3D.Induction.QProxy
8:import RBM3D.Induction.NQLin
$ lake build RBM3D.Induction.QBudgetA > build.log 2>&1; echo exit=$?      # audit worktree
... 'RBM.Ind.budgetAltQN' depends on axioms: [propext, Classical.choice, Quot.sound]
... 'RBM.Ind.QBudgetAInst.budgetAltQN_instance' depends on axioms: [propext, Classical.choice, Quot.sound]
Build completed successfully (3861 jobs).
exit=0
$ grep "QBudgetA.lean.*depends on axioms" build.log | sed 's/.*axioms: //' | sort | uniq -c
  17 [propext, Classical.choice, Quot.sound]
$ grep "QBudgetA.lean" build.log | grep -ciE "warning|error"
0
$ grep -nE "\bsorry\b|\badmit\b|native_decide|^axiom|^\s*axiom |maxHeartbeats" RBM3D/Induction/QBudgetA.lean | wc -l
       0
$ printf 'import RBM3D\nimport RBM3D.Induction.QBudgetA\n\n#assert_rbm_axioms\n' > AuditReg.lean; lake env lean AuditReg.lean | head -4; echo exit=$?
axiom audit: 8185 theorems, 2656 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
All within [propext,
 Classical.choice,
 Quot.sound]; no project axioms: ...
exit=0
```
17 `#print axioms` = 16 public declarations + `budgetAltQN_instance`. Only the new file is touched (no frozen signature changes); imports are the three pinned merged modules. Full `lake build`: hub.

Name clashes on current `main` (`44dd942`):
```
$ for n in <16 public names> QBudgetAInst QBudgetA_; do git grep -n -F -w "$n" main -- RBM3D RBM3D.lean | wc -l; done
altBudget_kapFar:0 altBudget_qvFar:0 qvBdAltQN:0 cQVAltQN:0 dDriftAltLinQN:0 assembledRHSAltQN:0 kappaAltQN_mul_Bctl_pow_le:0
kappaAltQN_succ_mul_Bctl_pow_le:0 kappaAltQN_le_kapFar:0 qvBdAltQN_eq_qvShape:0 tbInitAltQN:0 tbDriftAltQN:0 tbQvAltQN:0
dDriftAltLinQN_le_shape:0 dDriftAltQN_le_shape:0 budgetAltQN:0 QBudgetAInst:0 QBudgetA_:0
```
Unpinned helpers are `private`; the only extra public name is `QBudgetAInst.budgetAltQN_instance` (ticket's instance namespace).

## 2. Statements against the pins (text diff and type-level check)

```
$ python3 sdiff.py     # check §2 def blocks ⊂ QBudgetA.lean (exact text); §3 Prop bodies vs `theorem NAME :` bodies (exact text)
vocab defs: 6 all verbatim: True
kappaAltQN_mul_Bctl_pow_le identical
kappaAltQN_succ_mul_Bctl_pow_le identical
kappaAltQN_le_kapFar identical
qvBdAltQN_eq_qvShape identical
tbInitAltQN identical
tbDriftAltQN identical
tbQvAltQN identical
dDriftAltLinQN_le_shape identical
dDriftAltQN_le_shape identical
budgetAltQN identical
```
Type-level check: `AuditStmt.lean` imports `QBudgetA`, re-declares check §2-§3 (lines 105-325) verbatim in `namespace RBM.Ind.AuditT2279` (pinned Props
over the *pinned* defs), then `example : @AuditT2279.v = @RBM.Ind.v := rfl` (each def `v`) and `example : AuditT2279.T2279_X := @RBM.Ind.X` (each target `X`).
```
$ lake env lean AuditStmt.lean; echo exit=$?
exit=0
```
Defs agree with the pins; every target has exactly the pinned type (no extra binder from `section Terms`' `variable (sz)`).

Consumer shape (Design (a), (d); independent scratch check `AuditCons.lean`):
- (iii-b): `qvBdAltQN … = ` the right side of `qvFormQN_le_of_goodSetN` (`QProxy.lean:1186-1196`; script substitution `(m + 1)↦(m + 1 + 1)`, `d m↦d (m + 1)`, `K↦KL`) by `rfl`.
- (iii-a): the six-term right side of `AssembledN` (`GridAssemblyN.lean:250-255`, verbatim), with `m := K n`, `κ := kappaAltQN … (gridTime s v K n)`,
  `εK := epsAltQN`, `dDrift j _ := dd j`, `δD _ _ := δD`, `c := cQVAltQN …`, `stepErr := stepErrN …` and the sup term replaced by `X0`, equals
  `assembledRHSAltQN …`, proved by `rfl`.
```
$ lake env lean AuditCons.lean; echo exit=$?
exit=0
```

## 3. Per-target verdict (statement, hypotheses, vacuity, cycle)

No structure in any statement (all hypotheses are real inequalities/equalities over merged definitions); only merged imports, no cycle; no external
hypothesis (`hlog`, `hR` of target 10 are numerical premises, discharged by the merged `NQBudgetInst.hlog_instance`, `hR_instance`).

| # | target | pin diff | hypotheses / vacuity | instance | verdict |
|---|---|---|---|---|---|
| 0 | 6 vocabulary defs | verbatim + `rfl` | — | used in 1-10 | PASS |
| 1 | `kappaAltQN_mul_Bctl_pow_le` | identical | `0≤W`, `u i≤u m<1`, any real `g` | `(i,m)=(0,4)`, `u_4=1/32` | PASS |
| 2 | `kappaAltQN_succ_mul_Bctl_pow_le` | identical | as 1, with `(j+1,m)` | `(j,m)=(0,4)` | PASS |
| 3 | `kappaAltQN_le_kapFar` | identical | `0≤u i≤u m<1`, `(1-u m)⁻¹≤N` | `(1-1/32)⁻¹≤2^21` | PASS |
| 4 | `qvBdAltQN_eq_qvShape` | identical | none (identity) | `m=1`, `u=1/128`, `w=1/32` | PASS |
| 5 | `tbInitAltQN` | identical | 6 premises | `X0=4B_s^3`, `G=4` | PASS |
| 6 | `tbDriftAltQN` | identical | 11 premises, generic `dd` | `dd=dDriftAltLinQN(u_j)`, `hdd` by target 8 | PASS |
| 7 | `tbQvAltQN` | identical | 7 premises | label `aFar`, `D''=7+2C_n` | PASS |
| 8 | `dDriftAltLinQN_le_shape` | identical | `|E|<2`, `u<1`, `Φ_i,X≥0` | `u=0`, `(Γ,Φ)=(4,1,12,1)` | PASS |
| 9 | `dDriftAltQN_le_shape` | identical | `|E|<2`, `u<1`, `Γ,Φ,X≥0` | `u=0`, `Γ=4`, `Φ=1` | PASS |
| 10 | `budgetAltQN` | identical | 26 premises, all numerical | full instance, below | PASS |

## 4. Compiled nonempty instances

Instance data (merged, `NQLinInst`/`AzumaProxyN`): `sz0` (`sz0_values: L=4, W=32, N=2097152, lam=1/64`); `sInst = 0`, `vg = 1/32`, `Kg = 4`
(`grid_data: Δ=1/128, u_0=0, u_4=1/32`); `Einst = 1/2`, `Γ4 = 4`, `Λ3 = 3`; nonempty label `aFar : Fin 3 → Zd 3 4`; `m = 1`, so `k = 3`.

Targets 5-9 are instantiated as `example := thm …`. To show they are fully applied, the copy `AuditInst.lean` (the same file with
`example :=` replaced by `#check`) prints their types:
```
$ sed 's/^example := /#check /; s/^#print axioms.*//; s|^/--|/-|' RBM3D/Induction/QBudgetA.lean > AuditInst.lean
$ lake env lean AuditInst.lean > inst.out; echo exit=$?; grep -c error inst.out
exit=0
0
(type heads, scripted from inst.out; none starts with ∀ or contains a top-level →)
tbInitAltQN …  : kappaAltQN 3 3 10 (1 / 2) 1 (sz0.lam 0) (↑(sz0.W 0)) (4 / 5) (gridTime sInst vg Kg 0) 0 (Kg 0) * … ≤ …
tbDriftAltQN … : gridStep sInst vg Kg 0 * ∑ j ∈ Finset.range (Kg 0), (kappaAltQN 3 3 10 … * … + …) ≤ …
tbQvAltQN …    : ∑ j ∈ Finset.range (Kg 0), … ≤ …
dDriftAltLinQN_le_shape … : dDriftAltLinQN sz0 0 (1 / 2) 0 1 4 1 12 1 Cn₀ (1 / 5) 6 1 1 ≤ …
dDriftAltQN_le_shape …    : dDriftAltQN sz0 0 (1 / 2) 0 1 4 1 Cn₀ (1 / 5) 6 1 1 ≤ …
```
Targets 1-4 are `example : <closed statement> := thm …` (`QBudgetA.lean:1230-1260`). Target 10 is the named theorem
`QBudgetAInst.budgetAltQN_instance` (`:1290`). Its statement is closed: `assembledRHSAltQN sz0 Einst sInst vg Kg 0 1 … aFar ≤ N^{C4₀+Cn₀+12}(Λ3 0^{1/2}+(1+12+1+1))B_{v}^3`.
It discharges all 26 premises at the data: `hdd` by `hdd_inst` (target 8 at each `u_j`); `hlog`, `hR` by the merged `NQBudgetInst` instances;
`ha1`-`he4` by the private `*_inst` lemmas, for the abstract `C4₀ = qProxy4C 3 3 10 (1/2) 1 > 0`, `Cn₀ = qProxyCn 3 2 10 1 1 (1/2) > 0` (both proved positive).

Nothing is degenerate: `N = 2^21`, `K = 4`, `KΔ = 1/32`, the label type is nonempty, and no premise is `False`. Its axioms are the three standard ones (§1).

## 5. Paper deltas

The report proposes `T2279a` (one kernel `W^{C₄ε}r^k`, one drift, no `ℚ/𝔼` split; `r B_u ≤ B_t` replaces the `d = 2` identity), `T2279b` (hypotheses
beyond `budgetNonAltLinN`: generic `hdd`/`Pa`/`Φd`/`b`, separate `δ0`/`δD`, `he0`, the `b`-part of `he1`) and `T2279c` (`Φd` shown as `1+12+1+1`).

The remaining Lean/paper differences that the targets inherit are already numbered in `docs/paper-deltas.md`:
```
$ grep -n "T2186\|budgetNonAltLinN\|T2179\|T2272\|T2250" docs/paper-deltas.md | cut -c1-60
1408:- **D449（T2179a）** … 1412:- **D453（T2179e）**     (budget shape, far part, Δη⁻¹≤1, N^{-1}≤B_v)
1432:- **D473（T2186a）** … 1436:- **D477（T2186e）**     (linear levels, fixed-n numerical budget, degree 1 in levels)
1525:- **D566（T2250a–d）**                              (one drift, no ℚ/𝔼 split at d≥3)
1542:- **D583（T2272a）**                                (quadratic dDriftAltQN level)
```
Coverage is complete.

## 6. Observations (no effect on statement, instance, build, axioms or delta coverage)

1. The instance uses `D'' = 7 + 2C_n`, while the ticket's preflight data say `D'' = 5`. The report discloses this (narrative 5), but section (a′) says "None".
   With this value `-D''+C_Q = -5`, and `D''` meets S3-18a's `hD` at `m ↦ m+1`. The instance is still nondegenerate, and the pin is unchanged.
2. The instance exponent `ε₀ = C₄ + C_n + 12` and `Pa ∋ N^{τ_N} = N` are the ticket's prescribed data at fixed `n = 0`. Meaningful smallness of `ε₀` belongs to the eventual forms (S3-17b).
3. Ticket preflight (iii) asks for a list of eventual forms of `ha1`-`he4` for S3-17b. The report does not give it (narrative 8). This is not a Lean deliverable.
4. The ticket's Open issues 1-3 (linear per-matrix level `dFlowQN_levelLin`, the cut, `hY`) remain with the dispatcher; T2279 does not need them.

## Verdict

Every target (0-10) passes. **T2279: PASS.** No dispatcher sign-off is needed.
