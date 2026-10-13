Auditor model: claude-opus-5-5
# T2489b audit, round 1 (L4b2b = file B `Graph/BAExp14b2B.lean`, targets 4-7 of T2489), written Tue Oct 13 07:10:41 UTC 2026

Branch `t/T2489b` at a4e272dc. Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2489b-audit1` (detached at a4e272dc). merge-base(main, t/T2489b) = 6a1c1f8f (L4b2a merge).
Verdict: **PASS** (targets 4, 5, 6, 7).

## 1. Diff scope (sole writable files)
```
$ git diff --name-only main...HEAD
RBM3D.lean
RBM3D/Graph/BAExp14b2B.lean
$ git diff main...HEAD -- RBM3D.lean
@@ -581,6 +581,7 @@ import RBM3D.BA.KDecayBA
 import RBM3D.BA.SEforLnBA
 import RBM3D.Graph.BAExp14a2
 import RBM3D.Graph.BAExp14b2
+import RBM3D.Graph.BAExp14b2B
 
 /-! Hard axiom audit of the whole library: see `RBM3D.Test.Axioms`. -/
 #assert_rbm_axioms
$ git diff main...HEAD -- RBM3D | grep -c "^-[^-]"      # deleted lines in merged files
0
$ wc -l RBM3D/Graph/BAExp14b2B.lean                      # stop line 2000, reserve trigger 1800
    1174 RBM3D/Graph/BAExp14b2B.lean
$ grep -rln "BAExp14b2B" RBM3D RBM3D.lean
RBM3D/Graph/BAExp14b2B.lean
RBM3D/Graph/BAExp14b2.lean        # docstring line 18 only (on main)
RBM3D.lean
```
Both files are sole writable files of T2489 (file B and the import line). No frozen signature or merged file is touched.

## 2. Build and axioms
```
$ lake build RBM3D.Graph.BAExp14b2B        (audit worktree)
Build completed successfully (4026 jobs).
exit=0
$ lake build                                (full library, registry check, #assert_rbm_axioms last)
non-vacuity certificates: 0 of 123 premises in the two ledgers; the rest are not known to be satisfiable (`RBM3D/Test/InterfaceShape.lean` says what each would take)
Build completed successfully (4355 jobs).
exit=0
$ lake env lean ax.lean     # import RBM3D.Graph.BAExp14b2B; open private T3B T3CG core8; #print axioms
'RBM.BA.baExp14bS2_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'_private.RBM3D.Graph.BAExp14b2B.0.RBM.BA.BAExp14b2B_T3B' depends on axioms: [propext, Classical.choice, Quot.sound]
'_private.RBM3D.Graph.BAExp14b2B.0.RBM.BA.BAExp14b2B_T3CG' depends on axioms: [propext, Classical.choice, Quot.sound]
'_private.RBM3D.Graph.BAExp14b2B.0.RBM.BA.BAExp14b2B_core8' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BAExp14b2B_core' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BAExp14b2B_I41_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
$ grep -nE "sorry|admit|native_decide|^axiom|^\s*axiom |inductive|^structure|^class" RBM3D/Graph/BAExp14b2B.lean
(no hit, exit=1)
```

## 3. Statements
### Target 6 `baExp14bS2_holds` (binding; must equal `T2489_S2`)
```
-- RBM3D/Graph/BAExp14b2B.lean:1064
theorem baExp14bS2_holds (d : ℕ) : BAExp14bS2 d := by
-- docs/tickets/checks/T2489-check.lean:184
def T2489_S2 : Prop := ∀ d : ℕ, BAExp14bS2 d
$ chk2.lean = check file + `import RBM3D.Graph.BAExp14b2B` + `example : T2489_S2 := baExp14bS2_holds` (a term) before `end RBM.BA.T2489Check`
$ lake env lean chk2.lean > chk2.out 2>&1; echo exit=$?; grep -c error chk2.out
exit=0
0
```
`BAExp14bS2` is the merged pin (`Graph/BAExp14b.lean:170`, untouched by the diff): `3 ≤ d → ∀ κ ε 𝔡 > 0, ∀ 𝔠 sz z, BAFlow → ∀ t ∈ [0, BAflowT0]`,
the seven premises (`STLocalEntrygL, LWAvgLawgL, STLmaxgL, STLKgL, STDecaygL, BATwistAvgLaw, BATwistLoopLaw`) at `μ = seqP (sz.withLam 0)`,
conclusion `PrecL` over `U_n = {Fin 8 × (Bool×Bool) × blocks² // λ²/L^d ≤ 1 - t}` with bound `(1 - t)⁻¹ Bctl^{5/2}`. Identical by elaboration. **PASS.**

### Targets 4, 5 (private, consumer target 6)
```
-- :258  private theorem BAExp14b2B_T3B  (... hE : STLocalEntrygL, hA : LWAvgLawgL, hLm : STLmaxgL, hT1 : BATwistAvgLaw) (kb : Bool) :
    PrecL sz (BAExp14a_μ sz) (U := fun n => Bool × Zd (k + 2) (sz.L n) × Zd (k + 2) (sz.L n))
      (fun n p _ => ‖∫ ω, BAExp14b_FT3B sz z n (t n) ω kb p.1 p.2.1 p.2.2 ∂(BAExp14a_μ sz)‖)
      (fun n _ _ => (1 - t n)⁻¹ * (sz.Bctl n (t n)) ^ (5 / 2 : ℝ))
-- :815  private theorem BAExp14b2B_T3CG (... hE, hA, hK : STLKgL, hT1 : BATwistAvgLaw, hT2 : BATwistLoopLaw) (kb : Bool) : (same shape, BAExp14b_FT3CG)
-- :1027 example: BAExp14b_FS2 tags 4,5,6,7 = (FT3B false, FT3B true, FT3CG false, FT3CG true) := rfl
```
Families `j = 4..7` are the merged integrands `BAExp14b_FT3B`, `BAExp14b_FT3CG` (`BAExp14b.lean:112, 118`), both `kb`, all charges and block pairs,
bound `(1-t)⁻¹𝔟^{5/2}` without the `U_n` restriction (a stronger uniform form; `core8` restricts nothing either and target 6 precomposes onto `U_n`).
Binders are subsets of the seven S2 premises (T3B: 4, T3CG: 5), with `t ∈ [0, BAflowT0]`, `BAFlow`, `1 ≤ k` (`d = k+2 ≥ 3`). **PASS.**

### Hidden hypotheses, vacuity, cycles
- No new `structure`/`class`/`inductive` (grep above). P3 (`hP3`) and the constants `(CM, S)` come from file A's merged private `BAExp14b2_base`
  (`:265`, `:822`: `obtain ⟨CM, S, hCM, hS, hfacts, hDa, hP3, hDτ, hτenv⟩ := BAExp14b2_base hk hκ hε h𝔡 hflow ht0 ht hE hA hT1`); TL2 data from merged
  `BAExp14b2_tl2`; `j < 4` from merged `BAExp14b2_I1K` (`open private ... from RBM3D.Graph.BAExp14b2`, line 26). Dependencies are merged (6a1c1f8f); no cycle
  (file B imports only `RBM3D.Graph.BAExp14b2`; no importer of file B besides `RBM3D.lean`).
- `BAExp14b2B_core` (:90, public) has `hP3 : PrecL ...` as an explicit hypothesis of a generic closing lemma; it is discharged at every use (`:307`, `:998`).
- No new external hypothesis: the seven premises are the merged pin's own (registry unchanged; DECISIONS §292 (3)(1): TL2 and Step 1/2 pins exact-type).
- Pin binders only in private declarations:
```
$ python3 -I scan.py RBM3D/Graph/BAExp14b2B.lean     # seven pins in signatures (text before the first `:=`)
public decls 36 | with pin in signature: []
private decls 4 : [('BAExp14b2B_T3B', 4), ('BAExp14b2B_T3CG', 5), ('BAExp14b2B_core8', 6), ('BAExp14b2B_U0', 0)]
```
- UBA-C1 / C1 greps:
```
$ grep -nE "sz\.lam|withLam|gK" RBM3D/Graph/BAExp14b2B.lean | cut -c1-100
1061:on `U_n = {λ²/L^d ≤ 1 - t}`, over the carrier `baFMz sz z` and the law `seqP (sz.withLam 0)`, f      # docstring
1072:        sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ (k + 2) ≤ 1 - t n}) =>                              # the pin's own U (target 6 proof)
$ grep -nwE 'mE|STGM|STKloop|etaT|STflowE|lwS|lwSplus' RBM3D/Graph/BAExp14b2B.lean
(no hit, exit=1)
```

## 4. Compiled nonempty instances (target 7; in the file, built above)
Data: `d = 3`, `sz0` (`n = 0`: `L = 4`, `W = 32`), `zSeq`, `flow_sz0` (`κ = 1/2`, `ε = 𝔡 = 1/10`, `𝔠 = 1/6`), `t ≡ 1/2` with `half_lt_t0`.
```
:1114 example (n : ℕ) : Nonempty {_p : Fin 8 × (Bool × Bool) × (Zd 3 (sz0.L n) × Zd 3 (sz0.L n)) //
          sz0.lam n ^ 2 / ((sz0.L n : ℕ) : ℝ) ^ 3 ≤ 1 - (1 / 2 : ℝ)} := ⟨⟨(0, (true, true), (0, 0)), BAExp14b2B_U0 n⟩⟩
:1121 example (hE hA hLm hK hDec hT1 hT2 : <the seven pins at baFMz sz0 zSeq, μ0, t ≡ 1/2>) : PrecL sz0 μ0 ... :=
  baExp14bS2_holds 3 le_rfl (1 / 2) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 6) sz0 zSeq flow_sz0
    (fun _ => 1 / 2) (fun _ => by norm_num) (fun n => (half_lt_t0 n).le) hE hA hLm hK hDec hT1 hT2
:1134 same with hT1 := baTwistAvgProd_holds 3 le_rfl ... sz0 zSeq flow_sz0 (fun _ => 1 / 2) ... hA hLm      (TL1 discharged by name)
:1147 BAExp14b2B_T3B  (k := 1) le_rfl ... flow_sz0 (t := fun _ => 1 / 2) (fun _ => by norm_num) (fun n => (half_lt_t0 n).le) hE hA hLm hT1 kb
:1156 BAExp14b2B_T3CG (k := 1) le_rfl ... flow_sz0 (t := fun _ => 1 / 2) ... hE hA hK hT1 hT2 kb
:1166 BAExp14b2B_I41_eq (z := zSeq) (BAflow_real ... sz0 zSeq flow_sz0 0) (n := 0) (t := 1 / 2) (by norm_num) (by norm_num) kb σ 0 (Pi.single 0 1) ω
```
Every deterministic hypothesis (`3 ≤ d`, `κ, ε, 𝔡 > 0`, `BAFlow`, `0 ≤ t ≤ BAflowT0`, `1 ≤ k`, `BAReal`) is discharged at concrete data; the
`U_n` index set is proved nonempty for every `n` (`BAExp14b2B_U0`: `λ_n ≤ 1`, `L_n³ ≥ 64`); `t = 1/2` is an interior time, not a collapsed window.
Only other gates' pins (the seven S2 premises) stay hypotheses, as CLAUDE.md §4 step 2 allows. Target 1 (a), (b) instances belong to file A (L4b2a, merged). **PASS.**

## 5. Name clashes
```
$ for r in <all refs/heads, refs/remotes except t/T2489b>; do git grep -nE "(theorem|def|lemma) (baExp14bS2_holds|BAExp14b2B_)" $r -- RBM3D; done
(no hit)
```

## 6. Paper deltas
- Target 6 is the merged pin text unchanged; its Lean/paper differences (BA "analogous" `B:118`; TL1, TL2 premises absent from `lem:LWterm_EXP`)
  are recorded: `docs/paper-deltas.md:1630` D666 (T2398d), `:1649` D685 (T2434c).
- Targets 4, 5 are private intermediate forms; no new statement difference. The report's candidates T2489c, T2489d are route notes (no statement difference),
  proposed in `docs/reports/T2489b-prove.md` (d). Coverage complete.

## 7. Observations (no RETURN)
- O1. `main` moved past the merge-base (5e44951d adds `import RBM3D.BA.B45BA` at the same position in `RBM3D.lean`); the full build here is on 6a1c1f8f + this
  branch. The hub re-adds the import after the last `import` line and runs the full build at merge (CLAUDE.md §3 (A) 4-5).
- O2. Premise `STDecaygL` of S2 is read by none of the eight families (core8 binds 6 of 7); it stays in the pinned text (X1-C4). Not a statement defect.
- O3. Report line 153 states the grep as `"\.lam|..."` while the ticket's grep is `"sz\.lam|..."`; the hits listed match the ticket form plus instance lines. No effect.

## Verdict
| target | statement | hidden/vacuity/cycle | instance | build/axioms | paper deltas | verdict |
|---|---|---|---|---|---|---|
| 4 `BAExp14b2B_T3B` (private) | families j=4,5, bound `(1-t)⁻¹𝔟^{5/2}` | none | :1147 | pass / std 3 | none new | PASS |
| 5 `BAExp14b2B_T3CG` (private) | families j=6,7, same bound | none | :1156 | pass / std 3 | none new | PASS |
| 6 `baExp14bS2_holds` | `= T2489_S2` (compiled term check) | none | :1121, :1134, :1114 | pass / std 3 | D666, D685 | PASS |
| 7 instances | d=3, sz0, zSeq, t≡1/2, U_n nonempty | n/a | compiled | pass | n/a | PASS |

No dispatcher sign-off needed.
