Auditor model: claude-opus-5-5

# T2286 audit (S3-17b, `RBM3D/Induction/QBudgetB.lean`), round 1 — Tue Oct  6 11:46:37 UTC 2026

Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2286-audit1`, detached at `t/T2286` = `e1e4846`; merge-base with `main` `f3e7c74`.

## 1. Scope, imports, hygiene
```
$ git diff --stat main...t/T2286
 RBM3D/Induction/QBudgetB.lean | 1142 +++++++++++++++++++++++++++++++++++++++++
 1 file changed, 1142 insertions(+)
$ grep -n "^import" RBM3D/Induction/QBudgetB.lean
6:import RBM3D.Induction.QBudgetA
$ grep -nE "sorry|admit|native_decide|^axiom|maxHeartbeats" RBM3D/Induction/QBudgetB.lean | wc -l
       0
$ for n in <8 public names> QBudgetBInst; git grep -c -w -F $n main -- RBM3D | wc -l   (name clash on main)
dFlowQN_levelLin 0 / alt_hdriftLinQN 0 / dDriftAltLinQN_nonneg 0 / dDriftAltQN_eq_lin 0
altBudgetNumQN 0 / altBudgetExpQN 0 / altBudgetExpQN_of_choice 0 / altBudgetNumQN_eventually 0 / QBudgetBInst 0
```
Only the sole writable file is touched; `RBM3D/Test/Axioms.lean` unchanged (registry diff empty, as expected by the ticket). No frozen signature touched (new file only). Unpinned helpers are `private` (`QBudgetB_*`, `QBudgetBInst.*`).

## 2. Statements against the pin (script diff, check file `docs/tickets/checks/T2286-check.lean`)
Script `diff.py`: extracts each `def T2286_<name> : Prop :=` body from the check file and the `theorem <name> :` statement (up to `:= by`) from the Lean file, and each §2 `def`, whitespace-normalised, compares.
```
$ python3 T2286/diff.py
altBudgetNumQN IDENTICAL
altBudgetExpQN IDENTICAL
dFlowQN_levelLin IDENTICAL 1305
alt_hdriftLinQN IDENTICAL 1684
dDriftAltLinQN_nonneg IDENTICAL 191
dDriftAltQN_eq_lin IDENTICAL 201
altBudgetExpQN_of_choice IDENTICAL 429
altBudgetNumQN_eventually IDENTICAL 464
```
(Third column: length in characters of the compared statement.) Every target is proved with exactly the pinned statement; the two §2 definitions are verbatim. Against the ticket's mathematics:
- T1 `dFlowQN_levelLin`: `GoodSetN` at the free crude level `(Γc,Λc,Φc)` (not in the conclusion), `GoodLinN` at `(Γ,Φ₁,Φ₂,Φ₃)`, `hY` explicit at length `m+1`, alternating `σ`, `C_n = qProxyCn d (m+1) Λg KL C c` explicit; conclusion `dDriftAltLinQN` with all parameters (`ε', D', τN, X`). Time window `0 ≤ u < 1`, `N⁻¹ ≤ 1-u`, `L^d ≤ W^{KL}` explicit, as the ticket's §29 list says.
- T2 `alt_hdriftLinQN`: the walk field at `C = (1+40d(m+1))6^{d(m+1)}`, `c = 1/2`, membership `GoodSetN ∩ GoodLinN` on `{j < τ}`, `hY` separate; conclusion for every `j < Kg n`, `j < τ ω`, every `b`.
- T3/T4: unconditional apart from `|E|<2`, `u<1`, nonnegativity of levels (T3); T4 an identity.
- T5: one explicit choice, monotone in the depths. T6: `∀ᶠ n` in conclusion and in the two `E`/`g` premises; fixed parameters before `∀ᶠ`; constants `C₄, C_n, C_Q` depend only on `(d,m,Λg,κ',KL,C,c)`.
Result: no special case, no weakened/strengthened variant.

## 3. Hidden hypotheses, vacuity, cycles
- New vocabulary `altBudgetNumQN`, `altBudgetExpQN` are conjunctions of real inequalities (no structure fields, no `Prop` fields). Every hypothesis of T1/T2 is a real inequality, a merged definition's membership (`GoodSetN`, `GoodLinN`), `STMollifierProps` (merged, discharged by `QopAlgebra_mollifier_props` in the instance) or the explicit bound `hY`.
- The Prop hypothesis `altBudgetExpQN …` of T6 is concluded by T5 for all positive `C₄, C_n, 𝔠, ε₀`; the instance chains them (`altBudgetNumQN_eventually_instance` uses `altBudgetExpQN_of_choice_instance`), so it is not vacuous.
- No cycle: the file imports only the merged `RBM3D.Induction.QBudgetA`; no external hypothesis is introduced (no TEAM §8 lesson-14 limit check needed).

## 4. Compiled nonempty instances (namespace `RBM.Ind.QBudgetBInst`)
| Target | Instance | Data | Hypotheses |
|---|---|---|---|
| T1 | `dFlowQN_levelLin_instance` (:938) | `d=3`, `m=2`, `sz0`, `n=4` (`W=10^5`, `N=8·10^18`), `E=u=0`, `H=0`, `σ=![t,f,t,f]`, `GoodSetN` at `(4,100,1)`, `GoodLinN` at `(4,1,16,1)`, `κ=1`, `τ'=1/10`, `ε'=1/5`, `D'=40`, `ν=W`, `X=1`, `τN=2`, `C=Cmol3`, `c=1/2`, `KL=2`, every `a` | all discharged (`hY` via `goodSetN_LKM_le`; `GoodLinN` via `goodSetN_subset_goodLinN`) |
| T2 | `alt_hdriftLinQN_instance` (:956) | walk `E≡0`, `s≡0`, `v≡1/2`, `Kg≡4`, `τ≡1`, `j=0`, every `ω`, `b`, same levels | all discharged (membership and `hY` on `{j<1}` proved) |
| T3 | `dDriftAltLinQN_nonneg_instance` (:994) | `sz0`, `n=4`, `E=u=0`, `m=2`, `(4,1,16,1)`, `X=1` | all discharged |
| T4 | `dDriftAltQN_eq_lin_instance` (:1001) | same data | none |
| T5 | `altBudgetExpQN_of_choice_instance` (:1062) | `k=3`, `C₄=qProxy4C 3 3 1 (24/25) 1`, `C_n=qProxyCn 3 2 1 1 1 (1/2)`, `𝔠=1/6`, `ε₀=1`, `ε=min(1/(8(C₄+C_n)),1/2)`, `ε'=1/(8C_n)`, `ε₁=εq=τN=1/8`, `D'=C₄+C_n+42`, `D''=2C_n+2+2C₄+81`, `D_Y=D_t=3` | all discharged |
| T6 | `altBudgetNumQN_eventually_instance` (:1074) | `sz0` (`sz0_tendsto`, `sz0_bandwidth`), `E≡1/2`, `κ'=24/25` (`im_ge`), `m=1`, `Λg=KL=C=1`, `c=1/2`, exponents of T5; `.exists` | all discharged |
Plus a compiled consumer `example` (:1085) feeding `altBudgetNumQN` into the merged `budgetAltQN` with `Pa`, `b`, `δ0`, `δD` as in Design (d) (the 8 conjuncts match `ha1`–`he4` syntactically). None degenerate: no `N=0`, nonempty index sets, `σ` genuinely alternating, `False`-free premises; the T1/T2 numbers are the ticket's preflight data.

## 5. Build and axioms (audit worktree)
```
$ lake build RBM3D.Induction.QBudgetB ; echo exit $?    (grep of the QBudgetB lines; prefix "info: RBM3D/Induction/QBudgetB.lean:" stripped)
ℹ [3862/3862] Built RBM3D.Induction.QBudgetB (11s)
1129:0: 'RBM.Ind.altBudgetNumQN' depends on axioms: [propext, Classical.choice, Quot.sound]
1130:0: 'RBM.Ind.altBudgetExpQN' depends on axioms: [propext, Classical.choice, Quot.sound]
1131:0: 'RBM.Ind.dFlowQN_levelLin' depends on axioms: [propext, Classical.choice, Quot.sound]
1132:0: 'RBM.Ind.alt_hdriftLinQN' depends on axioms: [propext, Classical.choice, Quot.sound]
1133:0: 'RBM.Ind.dDriftAltLinQN_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
1134:0: 'RBM.Ind.dDriftAltQN_eq_lin' depends on axioms: [propext, Classical.choice, Quot.sound]
1135:0: 'RBM.Ind.altBudgetExpQN_of_choice' depends on axioms: [propext, Classical.choice, Quot.sound]
1136:0: 'RBM.Ind.altBudgetNumQN_eventually' depends on axioms: [propext, Classical.choice, Quot.sound]
1137:0: 'RBM.Ind.QBudgetBInst.dFlowQN_levelLin_instance' depends on axioms: [propext, Classical.choice, Quot.sound]
1138:0: 'RBM.Ind.QBudgetBInst.alt_hdriftLinQN_instance' depends on axioms: [propext, Classical.choice, Quot.sound]
1139:0: 'RBM.Ind.QBudgetBInst.dDriftAltLinQN_nonneg_instance' depends on axioms: [propext, Classical.choice, Quot.sound]
1140:0: 'RBM.Ind.QBudgetBInst.dDriftAltQN_eq_lin_instance' depends on axioms: [propext, Classical.choice, Quot.sound]
1141:0: 'RBM.Ind.QBudgetBInst.altBudgetExpQN_of_choice_instance' depends on axioms: [propext, Classical.choice, Quot.sound]
1142:0: 'RBM.Ind.QBudgetBInst.altBudgetNumQN_eventually_instance' depends on axioms: [propext, Classical.choice, Quot.sound]
Build completed successfully (3862 jobs).
exit 0
$ grep -E "^(warning|error): RBM3D/Induction/QBudgetB" build.log | wc -l
       0
$ printf 'import RBM3D\nimport RBM3D.Induction.QBudgetB\n#assert_rbm_axioms\n' > precheck.lean; lake env lean precheck.lean; echo exit=$?
exit=0
$ grep -c error pre.out
0
```
Axioms: only `propext`, `Classical.choice`, `Quot.sound` for all 8 public declarations and 6 instances. No `set_option maxHeartbeats`. (Full `lake build` is the hub's at merge.)

## 6. Paper deltas
- `T2286a` proposed in the prove report (d): the alternating drift level at `d ≥ 3` is linear in `Φ₁, Φ₂, Φ₃` and the length-`(k−1)` control `X`, `hY` explicit (paper `(y27kasdfg)`/`(A4)`/`(A5)`, `(normQA)`, §62 (4)). This covers the one Lean/paper statement difference of T1/T2 (linear deterministic level, `hY` premise, `N^{τN}` absorption of the `ν²` constant inherited from the merged `altB45N_levelM`).
- `T2286b`: none claimed; confirmed by the T6 statement (hypotheses `1 ≤ d`, `SizeTendsto`, `Bandwidth 𝔠`, `0 < κ'`, eventual `κ' ≤ Im m`, eventual `0 < g ≤ Λg`, and the exponent Prop). T3–T6 are Lean bookkeeping of the paper's absorption with no statement difference beyond the eventual form already pinned by the ticket.

## 7. Observations (no RETURN)
- Prove report (b): the line "Axioms (`#print axioms` lines at the end of the file, from the build output):" is followed by no axiom lines (the paste is missing). The axioms are verified in §5 above; no statement, instance, build or delta is affected.
- Prove report (d) notes `altBudgetExpQN` is a new `Prop` hypothesis of public T6, contrary to the ticket's literal "no public theorem takes a new Prop as a hypothesis"; it is proved by T5 and the registry pre-check passes (exit 0). For the dispatcher's information only; the pinned T6 statement itself contains this hypothesis.

## Verdict
| Target | Verdict |
|---|---|
| 0 vocabulary `altBudgetNumQN`, `altBudgetExpQN` | PASS |
| 1 `dFlowQN_levelLin` | PASS |
| 2 `alt_hdriftLinQN` | PASS |
| 3 `dDriftAltLinQN_nonneg` | PASS |
| 4 `dDriftAltQN_eq_lin` | PASS |
| 5 `altBudgetExpQN_of_choice` | PASS |
| 6 `altBudgetNumQN_eventually` | PASS |
Ticket T2286: **PASS**. No dispatcher sign-off needed.
