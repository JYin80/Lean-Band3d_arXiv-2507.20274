Auditor model: claude-opus-5-5

# T2504 audit (round 1): V V3, `BA/MainIndOutBA`

Written 2026-10-14 08:17 UTC (`date -u`). Branch `t/T2504` at 43f2230d (merge-base `main` 41e55513); audit worktree
`/Users/junyin/Lean_proof/RBM3D-wt/T2504-audit1` (detached). **Verdict: PASS for all targets (1-12).**

## 1. Diff scope

```
$ git diff --stat main...t/T2504
 RBM3D.lean                 |   1 +
 RBM3D/BA/EMn2BA.lean       |   2 +-
 RBM3D/BA/LWPinsBA.lean     |   6 +-
 RBM3D/BA/MainIndOutBA.lean | 430 +++++++++++++++++++++++++++++++++++++++++++++
 RBM3D/Test/Axioms.lean     |  12 +-
```
All five are sole writable files. `RBM3D.lean`: one line `+import RBM3D.BA.MainIndOutBA` after the last import, before
`#assert_rbm_axioms`. Comment-only script (comment-depth scan of each changed line on the branch, line counts vs `main`):
```
RBM3D/BA/LWPinsBA.lean 20 comment-only
RBM3D/BA/LWPinsBA.lean 50 comment-only
RBM3D/BA/LWPinsBA.lean 52 comment-only
RBM3D/BA/LWPinsBA.lean lines main 111 branch 111
RBM3D/BA/EMn2BA.lean 124 comment-only
RBM3D/BA/EMn2BA.lean lines main 1090 branch 1090
$ grep -rln 'import RBM3D.BA.MainIndOutBA' RBM3D RBM3D.lean
RBM3D.lean
```
No other `RBM3D/Chain`, `RBM3D/Induction`, `RBM3D/Graph` or merged `RBM3D/BA/*` file changed; no merged statement touched.

## 2. Statements against the pins (check `docs/tickets/checks/T2504-check.lean` + auditor examples)

Scratch file = the check verbatim, plus `import RBM3D.BA.MainIndOutBA` and the lines below (uncommitted, in the scratchpad):
```
example (d R) : T2504_BAMainIndFamTL d R ↔ RBM.BA.BAMainIndFamTL d R := Iff.rfl
example : T2504_TL2Congr := RBM.BA.BATwistLoopLaw_congr
example (d) : T2504_MemberFlow d := RBM.BA.baFamMember_flow d
example (d) : T2504_MemberBase d := RBM.BA.baFamMember_base d
example (d) : T2504_TailPassage d := RBM.BA.baTailPassage d
example : T2504_ConclShift := RBM.BA.baConclShift
example (d) : T2504_BAChainFamTL d := RBM.BA.baChainFamTL_holds d
example (d) : T2504_G0M d := RBM.BA.baG0M_holds d
example (d) : T2504_LK0 d := RBM.BA.baLK0_holds d
example : T2504_BaseGInit' := RBM.BA.stBaseG_of_init'
example (d) : T2504_BaseGBA d := RBM.BA.baBaseG_holds d
example (d) : T2504_HorizonGBA d := RBM.BA.baHorizonG_holds d
example (d) : T2504_MLOutOfStep d := RBM.BA.baMLOutTL_of_famStep d
example (d) : T2504_UNOfMLOut d := RBM.BA.unMLOutBA_of_BAMLOutTL d
example (d) : T2504_UNOfStep d := RBM.BA.unMLOutBA_of_famStep d
$ lake env lean <scratch>/T2504-audit-check.lean 2>&1 | grep -E 'error|axioms'   # (warnings: unused binders in the check's shape examples only)
'RBM.BA.BAMainIndFamTL' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BATwistLoopLaw_congr' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baFamMember_flow' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baFamMember_base' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baTailPassage' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baConclShift' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baChainFamTL_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baG0M_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baLK0_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.stBaseG_of_init'' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baBaseG_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baHorizonG_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baMLOutTL_of_famStep' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.unMLOutBA_of_BAMLOutTL' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.unMLOutBA_of_famStep' depends on axioms: [propext, Classical.choice, Quot.sound]
exit 0
```
Every target elaborates against its `T2504_*` pin (`BAMainIndFamTL` by `Iff.rfl`: T2503's binding text). Hypotheses, quantifier order (`∃ 𝔠d` after `(κ, ε, 𝔡)`; `∃ c₁` before `(ε, 𝔠, sz, z)`;
`∃ κ' ε'` before `(𝔠, sz, z)`), the `κ/2` tail and the index ranges are therefore exactly the dispatcher's pins.

## 3. Hidden hypotheses, vacuity, cycles

- One public def (`BAMainIndFamTL`, a `Prop`), no structure. Endpoint premises (read from the signatures, file :216-326):
  `baChainFamTL_holds` takes `hmain : BAMainIndFamTL d STAny`, `STHorizonG`, `STBaseG`, `BATwistLoopBase d`, `STG0M`-uniform;
  `baMLOutTL_of_famStep` discharges the last four by `baHorizonG_holds d`, `baBaseG_holds d`, `baTwistLoopBase_holds d`
  (merged), `baG0M_holds d`; only the family step remains (family table row 1). `unMLOutBA_of_famStep` composes with the
  4-line projection. `stBaseG_of_init'` reuses merged `stBaseG_of_init` at the strengthened setting (no edit of `MainIndBase`).
- No cycle: `BAMainIndFamTL` is a hypothesis everywhere it occurs; no theorem in the file concludes it. Its producer is
  V2a/V2b (another gate's pin, not yet proved; allowed as a hypothesis of the instances by the ticket and §4 step 2).
- `baLK0_holds` uses `CltFlowBA_Ksol_isKLoopS` (`BAReal` only) at every `n`, not `GridGoodBA_LM_sub_K_zero` (answer (5)).
```
== forbidden (sorry|admit|axiom|native_decide)     hits=1 (none)
== C1 grep (BAK_le_small|...|STGridRepNgL)        hits=1 (none)
== defs: 60:def BAMainIndFamTL (d : ℕ) (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop) : Prop :=
== T250[34]_ text                                 hits=1 (none)
== open private: TwistChain_{LK,Lmax,Decay,Exp2,LocalEntry,TL2}_mix; Boot_GM_zero; GridGoodBA_loopFine_init,
   GridGoodBA_BAMLoop_one_loop; CltFlowBA_Ksol_isKLoopS, CltFlowBA_one_sub_T0   (exactly the ticket's list)
== withLam not of the form `withLam 0`: only the lemma name seqP_withLam_reindex_preimage (:151)
== comp: 19 × comp (· + n₀), 2 × comp (· + 3)
```
Name clash (theorem/def/abbrev of the 15 public names): `main` 0, `t/T2498b` 0, `t/T2502b` 0, `t/T2502c` 0 for every name.

## 4. Compiled nonempty instances (file :337-426, built in §5)

Data: d = 3, `sz0` (`n = 0`: `L = 4`, `W = 32`), `zSeq`, `BAFlow sz0 (1/4) (1/10) (1/6) (1/10) zSeq`, `c₁ = 1/3`, `sz0_lam_pos`,
`t ≡ 1/2 ≤ T₀` (`half_lt_t0`), non-main member `mem0 = BAzSrc sz0 zSeq (2/3) (17/25)` of `Fam(0)`, `Fam(1/2)`.
| target | instance | open hypotheses |
|---|---|---|
| 7 `baG0M_holds`, 8 `baLK0_holds` | at `zSeq` | none |
| 9a `stBaseG_of_init'`, 9b `baBaseG_holds` | `STConclgL (baFMz sz0 zSeq) μ0 0` | none |
| 10 `baHorizonG_holds` | admissible, `0<T₀<1`, eventual `N^{-1+ε/2} ≤ 1-T₀` | none |
| 2a `BATwistLoopLaw_congr` | `zSeq` vs `zMod` (`zMod_ev`) | `μ, τ` free (universal) |
| 2b `baFamMember_flow` | `mem0 ∈ Fam(1/2)` | none |
| 3 `baFamMember_base` | `mem0 ∈ Fam(0)` (non-main member) | none |
| 4 `baTailPassage` | `κ = 1/2`, `flow_sz0` | none |
| 5 `baConclShift` | `n₀ = 3`, `τ ≡ 1/2` | the seven tail conclusions (ticket) |
| 6 `baChainFamTL_holds` | `t ≡ 1/2` and `t ≡ 0` | `hm : BAMainIndFamTL 3 STAny` |
| 11 (three) | `t ≡ 1/2`; composite at `t ≡ 0` | `hm` |
Every deterministic premise is discharged by `norm_num`, `le_rfl` or a merged instance lemma; no `N = 0`, empty index,
collapsed window or `False` premise. Target 1 (a def) is exercised as the hypothesis `hm` of 6 and 11.

## 5. Build and axioms (audit worktree)

```
$ lake build RBM3D.BA.MainIndOutBA 2>&1 | grep -E '^error|Build completed'
Build completed successfully (4154 jobs).
$ lake build RBM3D 2>&1 | grep -E '^error|^exit|Build completed|premises found|registry:'     # full library, runs #assert_rbm_axioms
premises found by scanning: 143 (borrowed 1, owed 64, structural 58, refuted 6, superseded 14).
registry: 2 borrowed + 118 owed + 138 structural + 7 refuted + 19 superseded; 141 registered premise(s) carry nothing yet: [...]
Build completed successfully (4386 jobs).
exit 0
$ grep -oE 'RBM\.(BA\.(STLK0|STG0M|STBaseG|STHorizonG|BAMainIndFamTL)|Univ\.UNMLOutBA)\b' <"carry nothing" list>   → no hit
```
Registry edit (`Test/Axioms.lean`): deletes `STLK0`, `STG0M`, `STBaseG`, `STHorizonG`, `UNMLOutBA`; adds
`RBM.BA.BAMainIndFamTL` with the owner text of answer (2); `STMainIndG` owner text changed as in answer (3); notes added in
the T2340 and T2241 comments. Entries in `owedProps` by script: 58bcd8b6 121, 41e55513 121, t/T2504 117 (ticket: 121 → 117).
The scan's "118 owed" counts differently (report: 122 → 118); same −5 +1.

## 6. Paper deltas

Lean/paper differences: the family form of `lem:main_ind_BA` (D536), the `0 < lam` tail / route through `Sizes.comp` at
`κ/2` (D538), `d > 3` regime (iii) out of scope (D723): all three present in `docs/paper-deltas.md:1495, 1497, 1803`.
`stBaseG_of_init'` is a Lean-side variant of a merged lemma (no paper statement). Report (d): "none new"; agreed.

## 7. Per-target verdicts

Targets 1-12 (`BAMainIndFamTL`; `BATwistLoopLaw_congr`, `baFamMember_flow`; `baFamMember_base`; `baTailPassage`;
`baConclShift`; `baChainFamTL_holds`; `baG0M_holds`; `baLK0_holds`; `stBaseG_of_init'`, `baBaseG_holds`; `baHorizonG_holds`;
`baMLOutTL_of_famStep`, `unMLOutBA_of_BAMLOutTL`, `unMLOutBA_of_famStep`; instances): statement = pin (§2), no hidden
hypothesis or cycle (§3), compiled nondegenerate instance (§4), build and standard axioms (§5), deltas covered (§6).
**PASS** for each.

## 8. Observations (no RETURN)

- O1. The prove report has 254 lines; the ticket asks for ≤ 150 (CLAUDE.md §6 allows 300). It changes no statement,
  instance, build, axiom or paper-delta coverage.
- O2. File length 430 (ticket 240 / 395 (≈ 435) / 766): within the stop line.
- O3. M/N shape (closing (iii)): N's readers take `∀ d, UNMLOutBA d`; this ticket gives `UNMLOutBA d` only under
  `BAMainIndFamTL d STAny`. As the ticket decides (answer (7)), this goes to M/N; it is not a defect here.
