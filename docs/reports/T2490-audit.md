Auditor model: claude-opus-5-5

# T2490 audit, round 1 (Tue Oct 13 06:07:35 UTC 2026)

Branch `t/T2490` b10f2c9f (base e6c26ca4); audit worktree `RBM3D-wt/T2490-audit1` (detached). Section (a) took no split (one row). Start decision: T2489 not merged, so target 5 is not delivered.
```
$ git log main --oneline | grep -c "T2489: merge"; head -1 docs/queue/T2489.state
0
state: proving
```

## 1. Diff scope, hygiene, importers
```
$ git diff --stat main...t/T2490
 RBM3D.lean                 |   1 +
 RBM3D/Graph/BAExp14a2.lean | 406 +++++++++++++++++++++++++++++++++++++++++++++
$ git diff main...t/T2490 -- RBM3D.lean   (hunk)
 import RBM3D.Chain.IniTermIGen2
+import RBM3D.Graph.BAExp14a2
 /-! Hard axiom audit ... -/
 #assert_rbm_axioms
$ grep -cE '\bsorry\b|\badmit\b|native_decide|^axiom|^\s*axiom ' RBM3D/Graph/BAExp14a2.lean
0
$ git grep -l BAExp14a2 t/T2490 -- RBM3D | grep -v Graph/BAExp14a2.lean     (outside importers)
(none)
$ grep -nE "^(theorem|lemma|def|abbrev|structure|inductive|class|instance)" RBM3D/Graph/BAExp14a2.lean
59:def LWCutExpG ...            73:theorem LWCutExp_iff ...      77:theorem band_LWCutExpG ...
82:def BALWCutExpTw ...         92:def BALWtermEXPTw ...         102:def BALWtermEXPTwOfCut ...
105:def BALWCutExpTwOfS2 ...    108:def BALWtermEXPTwOfS2 ...    218:theorem baLWtermEXPTw_of_cut ...
272:theorem baLWCutExpTw_of_S2 ...                                326:theorem baLWtermEXPTw_of_S2 ...
```
Only the sole writable files are touched (`BAExp14a2B` is not used). `Test/Axioms.lean` is unchanged. No `structure`/`inductive`/`class`. All 13 other helpers are `private` with stem `BAExp14a2_`.

## 2. Statements against the pins (check file `docs/tickets/checks/T2490-check.lean`)
Text diff (docstrings removed, `T2490_` stripped, whitespace normalised):
```
$ python3 -I diff.py T2490-check.lean RBM3D/Graph/BAExp14a2.lean
IDENTICAL LWCutExpG
IDENTICAL BALWCutExpTw
IDENTICAL BALWtermEXPTw
IDENTICAL BALWtermEXPTwOfCut
IDENTICAL BALWCutExpTwOfS2
IDENTICAL BALWtermEXPTwOfS2
DIFFERS/ABSENT BandCut / Reduction / Assembly / TermOfS2      (theorem types: checked by Lean below)
DIFFERS/ABSENT CutClosed / TermClosed                         (target 5: not delivered, start decision)
```
Lean check: the check file with `import RBM3D.Graph.BAExp14a2` added, plus the lines below (`cmp.lean`, compiled in the audit worktree):
```
example (d : ℕ) : BALWCutExpTw d = T2490_BALWCutExpTw d := rfl        (and the same for BALWtermEXPTw,
example : @LWCutExpG = @T2490_LWCutExpG := rfl                          …OfCut, …CutExpTwOfS2, …termEXPTwOfS2)
example : T2490_BandCut := band_LWCutExpG
example : T2490_Reduction := baLWtermEXPTw_of_cut
example : T2490_Assembly := baLWCutExpTw_of_S2
example : T2490_TermOfS2 := baLWtermEXPTw_of_S2
example : ∀ d : ℕ, LWCutExp d ↔ bandPin T2490_LWCutExpG d := LWCutExp_iff
$ lake env lean T2490cmp_audit.lean; echo exit=$?
exit=0      (output: only unused-variable warnings at the check file's own `T2490_LWCutExpG` binder line; no error)
```
Against the paper (`6_Step6_two_loop.tex:83-88`, `lem:LWterm_EXP`: "suppose 1-t ≥ λ²/L^d and (Gt_bound_flow)–(Eq:Gdecay_flow) hold; then for all σ ∈ {±}², a ∈ (Z_n)², 𝔼 E^{G,(2)}_{t,σ,a} ≺ (1-t)^{-1}(W^{-d}B_{t,0})^{5/2}"):
- index set `sz.lam n ^ 2 / L^d ≤ 1 - t n` = `1-t ≥ λ²/L^d`; index `(Fin 2 → Bool) × (Fin 2 → Zd d L)` = `{±}² × (Z_n)²`; bound `(1 - t n)⁻¹ * Bctl^{5/2}`, the same text as the merged band `LWtermEXPG` (`Chain/LWGen:108`); exponent 5/2, no loss.
- Order: the fixed parameters `κ ε 𝔡 𝔠 sz z`, `BAFlow`, `t` come before `PrecL` (∀ τ, eventually in n). `3 ≤ d` is the first premise. `d` is a parameter.
- Premises: the five Step 1/2 pins (the paper's "estimates hold") plus TL1 `BATwistAvgLaw`, TL2 `BATwistLoopLaw`. These are the two extra premises of route R1 that the BA case needs (`B:118` "analogous … omit"). Covered by D666 (= T2398d) and the new candidate T2490a.
- Targets 2–4 are conditional by design (`…Of…` defs: `BALWCutExpTw d → …`, `BAExp14bS2 d → …`). The ticket pins them this way, and the report states it (prove report narrative, "None is the unconditional pin"). The unconditional closures (target 5) are owed to the last terminal ticket, as dispatcher answer (5) of §292 (4) provides.

## 3. Vacuity, hidden hypotheses, cycles
- No structure field carries a hypothesis. Every premise is an explicit `→` in a pinned def.
- The public theorems have no binder besides `d`. `BAExp14bS2`, TL1, TL2 and the five pins occur only inside the bodies of the pinned defs (prove report `binders.py`; confirmed by the declaration list above: `baLWtermEXPTw_of_cut : ∀ d, BALWtermEXPTwOfCut d` and similar).
- Dependencies are merged results, with signatures:
```
RBM3D/Graph/BAExp14aB.lean:1692:theorem baExp14a_S1_holds (d : ℕ) : BAExp14aS1 d
RBM3D/Graph/BAExp14e.lean:347:theorem baExp14bS3_holds : ∀ d : ℕ, BAExp14bS3 d := fun d => baExp14bS3_of_leaf d (baG5LeafPrec_holds d)
RBM3D/Graph/BAExp14bB.lean:1035:theorem baExp14b_expand_holds (d : ℕ) : BAExp14bExpand d
RBM3D/BA/TwistAvgB.lean:451:theorem baTwistAvgProd_holds (d : ℕ) : BATwistAvgProd d
```
- The antecedent `BAExp14bS2` (`BAExp14b.lean:170`) is a merged pin with the same seven premises, `t`-range and bound, on index `Fin 8 × (Bool×Bool) × (Zd×Zd)` with the same predicate. The proof applies it at `⟨(j,(σc,σo),(ac,ao)),hg⟩` (l.301-302): it is used as stated, with nothing extra. No cycle: the file imports `BAExp14e`, `BAExp14bB`, `TwistAvgB`, and nothing imports it.
- The proofs do not trivialise any premise. The reduction uses `integral_add` with integrability from `BAExp14a2_BM_cutg` (continuity and the bound `‖G‖ ≤ η⁻¹` via the public `BAExp14a_cont_G`, `BAExp14a_G_le`, `BAExp14a_integrable`), then `2 ≤ N^{τ/2}`. The assembly uses `baExp14b_expand_holds` and the bounds 6+8+4 ≤ 18 ≤ N^{τ/2}. It uses only `t < 1` (`ba_G_data`) and `size → ∞` (`Sizes.tendsto_size`), which is within the stop rule.
- External hypotheses: none new. TL2 and the five pins are other gates' pins (owed lines `Test/Axioms.lean:192-193`, etc.). S2 is T2489's pin.

## 4. Compiled nonempty instances (l.341-400, in the file; compiled by the module build)
| endpoint | example | data | discharged | left as hypotheses (other gates' pins) |
|---|---|---|---|---|
| `baLWCutExpTw_of_S2` | l.342 | d=3, `sz0`, `zSeq`, `flow_sz0`, κ=1/2, ε=𝔡=1/10, 𝔠=1/6, t≡1/2 | `3≤3`, positivity ×3, `BAFlow`, `0≤t`, `t≤BAflowT0` (`half_lt_t0`) | S2, 5 pins, TL1, TL2 |
| `baLWtermEXPTw_of_cut` | l.350 | same | same | `BALWCutExpTw 3`, 5 pins, TL1, TL2 |
| `baLWtermEXPTw_of_S2` | l.358 | same | same | S2, 5 pins, TL1, TL2 |
| 6 (c), TL1 by name | l.367, l.377 | same | plus TL1 = `baTwistAvgProd_holds 3 … hA hM` | S2 / `BALWCutExpTw 3`, 5 pins, TL2 |
| `band_LWCutExpG` | l.393 | d=3, `sz0`, `z0`, `flow_z0`, `tInst` | `tInst_range`, positivity | 5 band local laws |
| `LWCutExp_iff` | l.400 | d=3 | all (no hypothesis) | none |

Nondegenerate: `sz0` at n=0 has L=4, W=32, N=2^21, and the index predicate λ²/L³ ≈ 3.8e-6 ≤ 1/2, so the index set is all 16384 cut indices (section (a) script). No `False` premise, no `N = 0`, no collapsed window. The constants 2 and 18 are reached from n=0 at τ=1 (section (a)), so the instance does not depend on a very large witness. Instance l.377 has the check's 6 (c) shape (same premise list; `t n` reduces to `1/2`).

## 5. Build and axioms (audit worktree)
```
$ lake build RBM3D.Graph.BAExp14a2 2>&1 | grep -E "error|warning.*BAExp14a2|Build completed"; echo exit=$?
Build completed successfully (4050 jobs).
exit=0
$ lake build 2>&1 | grep -E "error:|axiom audit|premises found|Build completed"     (RBM3D.lean with the branch's import line)
info: RBM3D.lean:583:0: axiom audit: 14600 theorems, 4558 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
premises found by scanning: 128 (borrowed 1, owed 61, structural 46, refuted 6, superseded 14).
Build completed successfully (4351 jobs).
exit=0
$ (cmp.lean) #print axioms
'RBM.BA.LWCutExp_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.band_LWCutExpG' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baLWtermEXPTw_of_cut' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baLWCutExpTw_of_S2' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baLWtermEXPTw_of_S2' depends on axioms: [propext, Classical.choice, Quot.sound]
```
The registry scan passes with `Test/Axioms.lean` unchanged. No frozen signature is touched: the change is additive and edits no merged file.

## 6. Paper deltas
```
$ grep -n "T2398d" docs/paper-deltas.md | cut -c1-60
1630:- **D666（T2398d）**：`B:118` 说 BA 情形的 Lemma B.1（`lem:LWterm_EXP`）
```
- The seven-premise BA statement (TL1, TL2 beyond the paper's Step 1/2 estimates) is covered by D666 (T2398d) and proposed again as **T2490a** for the successor pin `BALWtermEXPTw`.
- The decomposition `LWE → LWcut → S1+S2+S3` with S2 as an antecedent (a conditional result until target 5) is proposed as **T2490b**.
- No other Lean/paper difference was found.

## 7. Observations (no verdict effect)
- O1: the ticket cites `main` 4270f377; the branch base is e6c26ca4. The inputs named in the ticket are present: the full build passes.
- O2: the prove report's (a′) correction (`BAExp14a_t_lt_one` → `ba_G_data`) matches the file (l.222, l.278).

## Verdicts
| target | verdict |
|---|---|
| 1 pins `LWCutExpG`, `BALWCutExpTw`, `BALWtermEXPTw`, the three `…Of…` defs, `LWCutExp_iff`, `band_LWCutExpG` | PASS |
| 2 `baLWtermEXPTw_of_cut` | PASS |
| 3 `baLWCutExpTw_of_S2` | PASS |
| 4 `baLWtermEXPTw_of_S2` | PASS |
| 5 closures | not in scope (T2489 not merged; deferred to the last terminal ticket by §292 (4) answer (5)) |
| 6 instances | PASS |
| 7 C1 / registry | PASS |

**Overall: PASS.** No dispatcher sign-off needed.
