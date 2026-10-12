Auditor model: claude-opus-5-5
# T2434 audit (round 1) — Mon Oct 12 09:28 UTC 2026 (`date -u`)

Inputs: ticket `docs/tickets/T2434.md`, Amend 1 (`T2434-amend-1.md`, H229), prove report `docs/reports/T2434-prove.md`, check file
`docs/tickets/checks/T2434-check.lean`. Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2434-audit1`, detached at `t/T2434` = `6cccbdd`.
Targets under Amend 1 item 2: (1) the pins `BAExp14bS2`, `BAExp14bS3`, `BAExp14bExpand`, `BAExp14bCutConj` verbatim from the probe;
(2) `baExp14b_expand_holds`; (3) the block-form lemmas; (4) instances; (5) C1; (6) no registry line. Proofs of S2/S3 are not this row's.

## 1. Diff and hygiene
```
$ git diff --name-status main...t/T2434
A	RBM3D/Graph/BAExp14b.lean
A	RBM3D/Graph/BAExp14bB.lean
A	RBM3D/Probe/T2434Pins.lean          # sole writable (probe step only, never merged)
$ git merge-base main t/T2434  ->  e3f59c2
$ git diff --stat e3f59c2 main -- Graph/BAExp14aB.lean Graph/BAExp14a.lean BA/TwistPins.lean Chain/LWGen.lean Graph/BAGGExp.lean
(empty: the upstream files these modules read are unchanged on main)
$ wc -l Graph/BAExp14b.lean Graph/BAExp14bB.lean Probe/T2434Pins.lean
     998 / 1076 / 267                    # stop line 2,000 per file: both below
$ grep -nE '\b(sorry|admit|native_decide)\b|^\s*axiom |@\[implemented_by|@\[extern|unsafe' (3 files)
(no hits)
$ grep -n maxHeartbeats  ->  BAExp14b.lean:758, :803  `set_option maxHeartbeats 1600000 in` (FT3B_block, FT3CG_block)
$ grep -vciE '^(BAExp14b|baExp14b)' pub.txt     # 69 public names of the two files
0                                       # every public name carries the stem
$ git grep -n -i 'BAExp14b' main -- RBM3D RBM3D.lean | grep -v BAExp14b2 | wc -l
0                                       # no clash on main
```
No existing file modified; no frozen signature touched; `RBM3D.lean` unchanged (root imports are the hub's).

## 2. Build and axioms (audit worktree)
```
$ lake build RBM3D.Graph.BAExp14b RBM3D.Graph.BAExp14bB
✔ [4007/4008] Built RBM3D.Graph.BAExp14b (35s)
✔ [4008/4008] Built RBM3D.Graph.BAExp14bB (17s)
Build completed successfully (4008 jobs).       EXIT=0
$ grep -c BAExp14b build.log  ->  3   (the two "Built" lines + none else: no warning/error in the two files; replayed warnings are upstream only)
$ lake env lean ax.lean     # #print axioms of all 69 public declarations (pub.txt, extracted by grep of ^theorem|def)
EXIT=0  lines: 69; [propext, Classical.choice, Quot.sound]: 69; other: 0
$ lake env lean docs/tickets/checks/T2434-check.lean     # on the branch
EXIT=0 errors=0
$ lake env lean RBM3D/Probe/T2434Pins.lean
EXIT=0 errors=0
```

## 3. Statements against the pins (target 1)
Amend 1 item 1 pins the statements "as the 1a wrote them"; the check file fixes their outer shape (`T2434_FamShape`, `T2434_Prem7`,
`T2434_ExpandShape`, `T2434_CutConj`). Binding re-done independently (`bind.lean` = `import RBM3D.Graph.BAExp14bB` + check-file section 2 verbatim + below):
```
example (d) : BAExp14bExpand d = T2434_ExpandShape d (Fin 8) (Fin 4) BAExp14bS2Fam BAExp14bS3Fam := rfl
example (sz z) : BAExp14bCutConj sz z = T2434_CutConj sz z := rfl
example (d) : BAExp14bS2 d ↔ T2434_FamShape d (Fin 8) BAExp14bS2Fam T2434_Prem7 := by (un)curry the 7 premises
example (d) : BAExp14bS3 d ↔ T2434_FamShape d (Fin 4) BAExp14bS3Fam (STLocalEntrygL ∧ LWAvgLawgL ∧ STLmaxgL ∧ STLKgL ∧ STDecaygL) := by (un)curry
$ lake env lean bind.lean
EXIT=0   (only an unused-variable lint from the check-file template)
$ diff <(sed -n 39,185p Probe/T2434Pins.lean) <(sed -n 59,205p Graph/BAExp14b.lean)
identical   # pins and integrands in the file are the probe's verbatim (Amend 1 item 1)
```
- S2: 8 families (`D1t, D2t, T2a, T2b, T3B_0, T3B_1, T3C-Ḡ_0, T3C-Ḡ_1`), premises exactly the seven of `BALWCutExpTw` (TL1/TL2 imported from
  `BA/TwistPins`, not redefined). S3: 4 families (`D1X, D2X, T3C-tr_0, T3C-tr_1`), premises the five of `LWCutExpG` — as Amend 1 item 1.
- Binders, `t ∈ [0, BAflowT0]`, law `seqP (sz.withLam 0)`, carrier `baFMz`, `U_n = {λ²/L^d ≤ 1 - t}`, bound `(1-t)⁻¹ 𝔟^{5/2}`: identical to
  `BAExp14aS1` (the template enforces it by `↔`/`rfl`).
- `σc` convention: `BAExp14bS2Fam/S3Fam := if σc then F σo ao ac else star (F (!σo) ac ao)` — the same as the merged
  `BAExp14aS1Fam` (`Graph/BAExp14aB.lean:113-114`).
- Family content (read from `BAExp14b.lean:59-205`): the S2 families are the `∂tail` children (`BAExp14b_dtail`: `-G_{yδ}G_{γx}` for σ=+,
  `-conj(G_{xγ}G_{δy})` for σ=−) of `lanlw` on `MǦ`, `ǦM` and of the `∂f` term of `GGGamma`, plus `T2a/T2b` (`W^{(1)} = W − 1`) and `T3B_k`;
  the S3 families are the `∂X_{[α]}` children (`BAExp14b_dX = -W^{-d}Σ_{v∈[α]}G_{vδ}G_{γv}`). This is the partition of T2418 Amend 1 D4 /
  DECISIONS §244 Q3 (∂Ḡ children to S2/L4b2, ∂tr children to S3). Their sum with S1 is the cut: proved in Lean (§4), so the partition closes.
Verdict target 1: **PASS**.

## 4. The identity (target 2) and the conjugation
```
$ sed -n 1035p BAExp14bB.lean ; sed -n 210p BAExp14bB.lean
theorem baExp14b_expand_holds (d : ℕ) : BAExp14bExpand d := by
theorem baExp14b_cut_conj (sz : Sizes d) (z : ℕ → ℂ) : BAExp14bCutConj sz z := by
```
- Quantification (`BAExp14bExpand`, `BAExp14b.lean:192`): `3 ≤ d → ∀ κ ε 𝔡 > 0, ∀ 𝔠 sz z, BAFlow … → ∀ n t, 0 ≤ t → t ≤ BAflowT0 sz z n →
  ∀ σc σo ac ao, ∫ LWcutg … = Σ_{Fin 6} ∫ S1Fam + Σ_{Fin 8} ∫ S2Fam + Σ_{Fin 4} ∫ S3Fam` — as ticket target 2 (every `n`, every `t` in range,
  both charges). No premise on the law beyond `BAFlow`; the red charge goes through `baExp14b_cut_conj` (`BAExp14bB.lean:1036-1059`,
  `integral_conj`), which is proved pathwise for all `n t σo ac ao ω`, not assumed.
- Hidden hypotheses / cycle: the only structure hypothesis is the merged `BAFlow` (also the hypothesis of `BAExp14aS1`), discharged
  concretely by `flow_sz0` in the instance; the proof uses merged `baGGGamma_holds`/`baLanlw_holds` (imports `Graph/BAExp14aB`,
  `BA/TwistPins`, `Graph/BAGGExp`: all on main); no dependency on S2/S3 or on any unproved pin.
- C1: exact identity, no smallness of `g` or `M − m₀I`, no constants.
Verdict target 2: **PASS**.

## 5. Block forms (target 3)
`BAExp14b_FD1t_block :673`, `_FD2t_ :695`, `_FT2a_ :717`, `_FT2b_ :739`, `_FT3B_ :762`, `_FT3CG_ :807`, dispatcher `BAExp14b_FS2_block :879`,
`BAExp14bS2Fam_block`, `BAExp14b_Wk_blk :598`, `BAExp14b_twTie(_ba)`, `BAExp14b_twLoopX_twL2'` (rfl). Pathwise identities; hypotheses only
`hr : BAReal …` (merged, discharged by `BAflow_real`) and `0 ≤ t < 1`. `#print axioms`: standard three (§2). They are equalities of the pinned
families with block sums (`M^{(B)}`, `ω − 1`, `κ_k`, `X_{a₁}`, `twTrP`, `twLoopX`, `𝓛^{(2,3)}`), so they cannot change the content of S2.
Verdict target 3: **PASS**.

## 6. Compiled nonempty instances (target 4)
```
$ sed -n 1065,1067p BAExp14bB.lean
example (σc σo : Bool) :=
  baExp14b_expand_holds 3 le_rfl (1 / 2) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 6) sz0 zSeq flow_sz0 0 (1 / 2)
    (by norm_num) (half_lt_t0 0).le σc σo 0 (Pi.single 0 1)
$ sed -n 1070p BAExp14bB.lean
example (t : ℝ) (σo : Bool) (ω : sz0.SeqΩ) := baExp14b_cut_conj sz0 zSeq 0 t σo 0 (Pi.single 0 1) ω
$ sed -n 926,928p BAExp14b.lean
example (ω : sz0.SeqΩ) (j : Fin 8) (σ : Bool) :
    BAExp14b_FS2 sz0 zSeq 0 (1 / 2) ω j σ 0 (Pi.single 0 1) = BAExp14b_BS2 sz0 zSeq 0 (1 / 2) ω j σ 0 (Pi.single 0 1) :=
  BAExp14b_FS2_block BAExp14b_hr0 (by norm_num) (by norm_num) j σ 0 (Pi.single 0 1)
```
- Data: `d = 3`, `sz0` at `n = 0` (`L = 4`, `W = 32`), `zSeq`, `flow_sz0`, `t = 1/2 ≤ BAflowT0` (`half_lt_t0`), blocks `0 ≠ e₀`
  (`BAExp14b.lean:988` proves `(0 : Zd 3 (sz0.L 0)) ≠ Pi.single 0 1`). Every hypothesis of `baExp14b_expand_holds` is discharged; the
  instance matches ticket target 4 (as `BAExp14aB.lean:1741`). Same data for each of the six block-form lemmas (`:931-939`), `S2Fam_block`
  (`:943`), `Wk_blk` (`:947`), `twTie_ba` (`:950`).
- S2 (`:954`), S3 (`:962`): applied at the same data with all deterministic hypotheses discharged (`3 ≤ 3`, `κ ε 𝔡 > 0`, `flow_sz0`,
  `0 ≤ 1/2 ≤ BAflowT0` for every `n`); the 7 / 5 premises are other gates' pins and stay hypotheses, as the ticket allows (target 4).
  `:970` proves both index sets `U_n` nonempty for every `n` at these data (`λ_n²/L_n³ ≤ 1/2`).
- Not degenerate: `L = 4`, `W^d = 32768`, two distinct blocks, `t = 1/2` interior; no `False` premise, no empty index.
All examples compile (part of the module build, §2). Verdict target 4: **PASS**.

## 7. Targets 5, 6; S3 root (Amend 1 item 3); P3 (item 4)
- C1: §4. Registry: none; no `Test/Axioms.lean` change in the diff (§1).
- Item 3: the report (b) names the three roots `baD1XGraph`, `baD2XGraph`, `baT3CtrGraph k` with vertex data (script `s3roots2.py`) and
  `BAExpandId.lean:83 mdot := []`; nothing in the two files depends on them (`grep -c baG5Graph`: BAExp14b 1 (docstring `:179`), BAExp14bB 0; `grep -c 'baGGGamma_holds\|baLanlw_holds' BAExp14bB.lean` = 4;
  no use of `BAExp14bS2 `/`BAExp14bS3 ` in BAExp14bB: 0 lines).
- Item 4: P3 is not among the premises of S2 (§3); left to L4b2 as the amend says.

## 8. Paper deltas
- Report (d)1: no new candidate (`T2434a`: none). The `W − 1 = M⁺S⁺` coefficient used by `T2a/T2b`, `T3*_1` is D402; the S1 bound form
  and outer frame are inherited from the merged `BAExp14aS1` (T2418). The 18-family partition is the BA transcription of `B:7-121`
  (`(eq:ELW_term)`, written in the paper for the band model, BA "analogous") and a proof-structure device; the identity is exact.
- No Lean/paper difference introduced by this row's statements is left uncovered. See observation O2.

## Observations (no verdict effect)
- O1. The diff contains `RBM3D/Probe/T2434Pins.lean` (a sole writable file for the probe step, "never merged"): at merge the hub brings
  in only `Graph/BAExp14b.lean`, `Graph/BAExp14bB.lean` (CLAUDE.md §3 (A) step 3) and adds their two root imports.
- O2. The S2 pin carries `BATwistAvgLaw`, `BATwistLoopLaw` (TL1, TL2) as premises, which `lem:LWterm_EXP` (D102: the five Step 1/2
  hypotheses) does not have. They are pins of the TL stage (introduced by T2398/T2421, dispatcher-decided, DECISIONS §244), not
  introduced here; `grep -n -i 'twist' docs/paper-deltas.md` gives 0 lines. The dispatcher may want a delta at the L4a2 assembly if TL1/TL2
  are not derived from the five pins there.
- O3. Bound form `(1−t)⁻¹ 𝔟^{5/2}` vs paper `η_t⁻¹ (W^{-d}B_{t,0})^{5/2}` is the merged S1 convention (`η⁻¹ ≤ κ⁻¹(1−t)⁻¹`), enforced by
  the check-file template; not new here.
- O4. Report length 242 lines (ticket limit 250).

## Verdict
| target | verdict |
|---|---|
| 1 pins S2, S3, Expand, CutConj | PASS |
| 2 `baExp14b_expand_holds` (+ `baExp14b_cut_conj`) | PASS |
| 3 block-form lemmas | PASS |
| 4 instances | PASS |
| 5 C1, 6 registry | PASS |
**T2434: PASS.** No dispatcher sign-off needed.
