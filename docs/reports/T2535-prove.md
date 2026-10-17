Prover model: claude-sonnet-5-5

## (a) Math preflight — Sat Oct 17 01:33:38 UTC 2026

**(i) Exponent table.** No exponents, thresholds or constants: T2535 is a report-only document (`docs/PAPER-VS-LEAN.md`), with no mathematics and no Lean change.

**(ii) Concrete instance.** Not applicable (no hypotheses to instantiate).

Verdict: PASS (ticket Process: short preflight; hub compile of `docs/tickets/checks/T2535-check.lean` on main d44d29d1: exit 0, no error lines, as stated in the task text).

## (b) Script output

Scope: report-only ticket. The only file written is `docs/PAPER-VS-LEAN.md` (branch `t/T2535`, worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2535`). No Lean file was written or edited, so there is no module build, no new declaration, no instance of my own, no name-clash grep and no port from `../RBM1D` or `../RBM2D` (read with `cat`/`grep`/`pypdf` only).

### Size of the document at each commit (ticket stop size 700)

```
Sat Oct 17 02:05:58 UTC 2026  144 docs/PAPER-VS-LEAN.md  c38fff37 header, section 1
Sat Oct 17 02:06:03 UTC 2026  288 docs/PAPER-VS-LEAN.md  96b5a505 section 2
Sat Oct 17 02:06:03 UTC 2026  403 docs/PAPER-VS-LEAN.md  77c64898 sections 3, 4
Sat Oct 17 02:06:03 UTC 2026  694 docs/PAPER-VS-LEAN.md  f2f47b2d section 5, Appendix A
Sat Oct 17 02:07:45 UTC 2026  693 docs/PAPER-VS-LEAN.md  4b808b6b wording
Sat Oct 17 02:10:21 UTC 2026  693 docs/PAPER-VS-LEAN.md  398dd730 wording
Sat Oct 17 02:10:42 UTC 2026  693 docs/PAPER-VS-LEAN.md  f145ee43 wording
Sat Oct 17 02:15:20 UTC 2026  695 docs/PAPER-VS-LEAN.md  a84e21da namespace comments (final)
$ git diff --stat main...t/T2535
 docs/PAPER-VS-LEAN.md | 695 ++++++++++++++++++++++++++++++++++++++++++++++++++
 1 file changed, 695 insertions(+)
```

### The ticket's check file compiles (T2535 worktree, Sat Oct 17 01:40:19 UTC 2026)

```
$ lake env lean docs/tickets/checks/T2535-check.lean      -> exit 0
RBM.Endpoints.final_shape : RBM.Univ.UNL32 → (RBM.Endpoints.decol ∧ ... ∧ RBM.Endpoints.QDiff) ∧ RBM.Endpoints.Thm27
RBM.Endpoints.band_terminal : RBM.Univ.UNL32 → RBM.Endpoints.decol ∧ ... ∧ RBM.Endpoints.QDiff
RBM.Endpoints.Thm27_of_L32 : RBM.Univ.UNL32 → RBM.Endpoints.Thm27
... (17 `#check` results in all; last: RBM.Univ.UNL32 : Prop)
```

### Every `RBM.` name of the document exists on main (scratch file, not committed; Sat Oct 17 02:15:20 UTC 2026, commit a84e21da)

```
$ { echo "import RBM3D"; grep -v "^'RBM" docs/PAPER-VS-LEAN.md | grep -oE "RBM\.[A-Za-z0-9_.'′]*[A-Za-z0-9_'′]" | sort -u \
    | grep -vxE 'RBM\.(Gauss|Univ|BA|Endpoints|Loop|Path|Ind|Heat)' | grep -vE 'baStep5III_holds_any|baThm27L_all' \
    | sed 's/^/#check @/'; } > scratch_check.lean
$ grep -c '^#check' scratch_check.lean      -> 136
$ lake env lean scratch_check.lean          -> exit 0 ; `grep -c error` of the output: 0
```

Names that are not prefixed `RBM.` (113 `#check @<name>` lines, after `open RBM RBM.Gauss RBM.Gauss.Sizes RBM.Endpoints RBM.Univ RBM.BA RBM.Path RBM.Gauss.SizesInst RBM.Univ.UNInst`; Sat Oct 17 02:06:49 UTC 2026): exit 0, 0 errors.

Pending T2533/T2534 (listed as such; absent from main and from the tip of `t/T2523`): `RBM.BA.baStep5III_holds_any`, `RBM.BA.baThm27L_all`. The final texts of `Thm27`, `Thm27_of_L32`, `baThm27L_all` and `final_shape` in §1 are copied by script from `docs/tickets/checks/T2534-check.lean` (`Thm27New`, `FinalShapeNew`, and the type of the commented Part 2 example of `baThm27L_all`, `Thm27_of_L32`); the dispatcher rechecks them after T2534 merges.

Against the tip of `t/T2523` (`git log -1 --format=%h t/T2523` -> `a9d1a6d4`, the committed work in progress), a text search for the declaration of the last component of each name (`git grep` on that ref; 138 `RBM.` names, 113 other names):

```
MISSING on t/T2523: RBM.BA.baStep5III_holds_any
MISSING on t/T2523: RBM.BA.baThm27L_all
MISSING on t/T2523: Sizes.three_le_L      (a structure field of `Sizes`; present: `three_le_L : ∀ n, 3 ≤ L n`, Defs/Sizes.lean:145)
MISSING on t/T2523: UNModel.ba            (present: `def UNModel.ba`, Universality/Pins.lean:124)
```

On main and absent on that tip, hence not used in the document: `RBM.msc_eq_integral`, `RBM.Loop.KLK_unique`, `RBM.Univ.gueLocal`, `RBM.Ind.stoppedAzumaZN`, `RBM.Gauss.Sizes.stMainInd_holds`. The document describes main plus the final forms; after T2523 merges the two `#check` commands above should be rerun.

### `#print axioms` (scratch file, Sat Oct 17 01:46:10 UTC 2026, main d44d29d1; pasted in §1 of the document)

```
'RBM.Endpoints.decol_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Endpoints.locSC_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Endpoints.QUE_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Endpoints.QDiff_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Endpoints.BUniv_of_L32' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Endpoints.band_terminal' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Endpoints.Thm27_of_L32' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Endpoints.final_shape' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baThm27L_three' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### Lean statements copied from the source files by script

Scripts `ex.py` (33 lines) and `build.py` (46 lines), template `full.tpl` (67 marker lines `@@ex FILE NAME`, `@@exsub`, `@@thm`, `@@cex`), in the scratchpad directory `T2535/` (not committed). One declaration, docstring removed:

```
$ python3 ex.py RBM3D/Endpoints.lean locSC
def locSC : Prop :=
  ∀ d : ℕ, 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 →
    ∀ κ ε τ D : ℝ, 0 < κ → 0 < ε → 0 < τ → 0 < D → ∀ᶠ n in atTop,
      Sizes.seqP sz {ω | locBad1 sz κ ε τ n ω} ≤ ENNReal.ofReal (Nsz sz n ^ (-D)) ∧
      Sizes.seqP sz {ω | locBad2 sz κ ε τ n ω} ≤ ENNReal.ofReal (Nsz sz n ^ (-D))
$ python3 build.py full.tpl x > docs/PAPER-VS-LEAN.md
$ python3 build.py full.tpl x | cmp - docs/PAPER-VS-LEAN.md      (Sat Oct 17 02:15:40 UTC 2026) -> identical, exit 0
```

Markers by source file: `Defs/Sizes.lean` (Sizes size WO Bandwidth SizeTendsto Admissible locDomain), `Gauss/FineModel.lean` (svarF), `BA/MFixedPoint.lean` (BASelf BAm BArho BAbulk), `Universality/Pins.lean` (IsRegular32 IsFreeConv32 UNL32 IsOrthoEigenbasis kPoint gueVar gueP queWindow queBound queBadMat UNBUniv UNUnivDilAt), `Endpoints.lean` (calB distB Mband avg2 ThetaPM ThetaPP profPM profPP qdBound qdBoundExp decolBad locBad1z locBad2z qd1Badz qd2Badz locBad1 locBad2 qd1Bad qd2Bad que2BadMat decol locSC QUE BUniv QDiff), `BA/MAPins.lean` (BAprof BAendDom BAlocBad1z BAlocBad2z BAqdBadz BAdecolBad BAEnd_decolL BAEnd_locSCL BAEnd_QDiffL BAThm27L), `BA/UNPins.lean` (BAqueConclL BAEnd_QUEL BAEnd_BUnivL), `docs/tickets/checks/T2534-check.lean` (Thm27New, FinalShapeNew, two commented examples).

### Page, equation and theorem references against the PDF

`pdftotext` is not installed (`which pdftotext` -> "pdftotext not found"). Text was extracted per page with `pypdf` (`python3 dump.py paper/final/DubovaYangYauYin_RBM3D_Lean_version.pdf` -> `pp/pNNN.txt`, 106 pages; page number = printed number), and `pdfcheck2.py` tests that each reference of §1 and §4 occurs on the page cited:

```
p7: OK (2.1) | OK (2.2) | OK (2.4) | OK (2.5) | OK (2.6) | OK N = (W
p8: OK Theorem 2.1 (Delocalization) | OK Theorem 2.2 (Local semicircle law) | OK (2.9) | OK (2.10) | OK (2.12) | OK (2.14) | OK (2.15) | OK Fix any dimension d
p9: OK Theorem 2.3 (Quantum unique ergodicity) | OK (2.18) | OK (2.19) | OK Theorem 2.4 (Bulk universality) | OK (2.20) | OK Theorem 2.5 (Quantum diffusion) | OK (2.22) | OK (2.23)
p10: OK (2.24) | OK (2.25) | OK Proof of Theorem 2.4 | OK [28, Theorem 2.6]
p11: OK (2.29) | OK (2.30) | OK (2.31) | OK (2.32) | OK (2.33) | OK Theorem 2.7 (Main results for the block Anderson model) | OK Fix any dimension d
p12: OK (2.34)
p45: OK (iii) 1−s≥ 1−t≥g2
p72: OK centered at the deterministic matrix
p104: OK [28] S. Dubova
p105: OK [59] S. K. Truong | OK [64] C. Xu
p106: OK [69] H.-T. Yau
not found: 0
```

The references of §2 and §5 were checked the same way (`pdfcheck.py`: 0 not found apart from one placeholder token of the script itself). `docs/claude-team/tools/paper-labels.tsv` was used for the label-to-number map. `paper/final/` does not exist in the T2535 worktree (`paper/` is untracked); the PDF and TeX were read from `/Users/junyin/Lean_proof/RBM3D/paper/final/`.

### Process vocabulary (the ticket's grep, run on commit a84e21da, Sat Oct 17 02:15:20 UTC 2026)

```
$ grep -nEi 'T2[0-9]{3}|DECISIONS|paper-delta|ticket|prover|auditor|dispatcher|\bgate\b|pinned|\bowed\b' docs/PAPER-VS-LEAN.md
(no output)   grep exit 1
```

### The density factors of [LANDON20191137] (read-only, `../RBM1D/paper/1609.09011v3.pdf`, page 9, `pypdf`)

The (2.9) display of arXiv:1609.09011v3 has the two integrals without prefactors: `∫ O(α) p^{(k)}_{H_t}(E + α/(Nρ_{fc,t}(E)),…) dα − ∫ O(α) p^{(k)}_{GOE}(E + α/(Nρ_{sc}(E)),…) dα ≤ C N^{-κ}`; its (2.7) defines `p^{(k)}` by integrating the symmetrized density `p^{(N)}`; Definition 2.1 is (2.2), (2.3); (2.4) is `ρ_sc`; (2.5) the free convolution; (2.6) `ρ_{fc,t}`; (2.8) the time range. arXiv:1609.09011v4 is not in the repository.

### Narrative

- The document `docs/PAPER-VS-LEAN.md` (695 lines) follows the structure of the RBM2D and RBM1D documents: header, §1 what is proved, §2 twelve numbered differences, §3 uniformity, §4 the external input, §5 routes, Appendix A (Lean statements).
- §1 describes the final forms named by the ticket: `Thm27 := ∀ d, 3 ≤ d → BAThm27L d`, `final_shape` with only `UNL32`, the public axiom audit, and the examples of `FinalShape`, `BandTerminal` §Instances, `MAPins`, `BUnivHolds`. The pending parts (`baThm27L_all`, `baStep5III_holds_any`, `.2 3 le_rfl`, the `d = 4` example, the `baThm27L_all` line of the axiom list) are written from `T2534-check.lean`, `T2534.md` and the probe of `t/T2524`; none of them compiles on main yet.
- The ticket's table puts `bUniv_holds` with the hypothesis `UNL32`; on main `bUniv_holds` has six leaf hypotheses (`UNNormBandRow`, `UNL32`, `∀ d, UNMLOut d`, `UNLocAvgBand`, `UNQueBand`, `UNGUESchurTail`), and only `BUniv_of_L32 : UNL32 → BUniv` has `UNL32` alone. The table of §1 uses `BUniv_of_L32`.
- §2 items: sequences, blocks and `L ≥ 3`, labels, failure probability, uniform thresholds and unions, QUE and `A ≠ ∅`, the distance in `𝓑`, `m`/`Θ`, correlation functions, the bulk `ρ_N ≥ κ`, the density-normalized universality, the block Anderson profiles. Each item cites the PDF page and equation and the Lean name; the statements were compared against the Lean source, and items were dropped or corrected when they did not match (for example `msc_eq_integral` is not cited because it is absent on the `t/T2523` tip).
- The distance bound of §2.7 (`W(k−1) < K < W(k+1)`, factor `2^{d−2}`), the uniformity argument of §3 and the range remark (`d𝔠 < 1`, `𝔡 < d/2`) are paper arguments written in the document and not compiled; the document says so.
- Facts about arXiv:1609.09011v4 (the prefactors `ρ^{-k}`, the Remark on the complex Hermitian case) are taken from `../RBM2D/docs/PAPER-VS-LEAN.md` §4.2 and `../RBM1D/docs/PAPER-VS-LEAN.md` §4.1 and the docstring of `UNL32`; I verified only the v3 side (above).
- §5 lists nine route differences; each Lean name was compiled and compared with the module docstring and signature; the paper side (pages, labels) was checked with the PDF text and `paper-labels.tsv`.

## (c) Verified Mathlib names

`#check @Matrix.trace`, `ProbabilityTheory.gaussianReal`, `Ring.inverse`, `ContDiff`, `HasCompactSupport`, `ENNReal.ofReal`, `Fintype.card`, `Nat.descFactorial`: each elaborates (scratch file with `import RBM3D`, Sat Oct 17 02:09:11 UTC 2026, exit 0). No name was verified absent. No new Mathlib name is used by any Lean file (none written).

## (d) Open issues and paper-delta candidates

1. **Recheck after T2534 merges** (dispatcher): the two pending names; the `#print axioms` line for `RBM.BA.baThm27L_all` (the document lists `baThm27L_three` and the others only); §1 "Dimension", the table row of Theorem 2.7 and the `.2 3 le_rfl` and `d = 4` sentences of "The statements are not vacuous"; Part 2 of `T2534-check.lean`.
2. **Recheck after T2523 merges:** rerun the two name compiles of (b); T2523's tip `a9d1a6d4` was a work in progress.
3. **Possible empty bulk in the `d = 4` instance.** The probe of T2524 applies the four conjuncts at the bulk parameter `κ = 1/2`:
   ```
   $ git show t/T2524:RBM3D/Probe/T2524Pins.lean | grep -n "T2524_sz4 T2524_sz4_adm (1 / 2)"
   400:  have _ := h.1 (by norm_num) (1 / 8) (1 / 10) T2524_sz4 T2524_sz4_adm (1 / 2) 1 1 ...
   401:  have _ := h.2.1 ... T2524_sz4_adm (1 / 2) (1 / 10) 1 1 ...     (403, 405 likewise)
   $ grep -n "theorem BAm_norm_le_one\|def BArho\|def BAbulk" RBM3D/BA/Ward.lean RBM3D/BA/MFixedPoint.lean
   Ward.lean:136:theorem BAm_norm_le_one (g : ℝ) (z m : ℂ) (hz : 0 ≤ z.im) (h : BASelf d L g z m) : ‖m‖ ≤ 1
   MFixedPoint.lean:384:def BArho (g E : ℝ) : ℝ := (BAm d L g (E : ℂ)).im / Real.pi
   MFixedPoint.lean:429:def BAbulk (g κ E : ℝ) : Prop := κ ≤ BArho d L g E
   ```
   `BAm` is a solution of (2.32) or `0`, so `BArho ≤ 1/π ≈ 0.318 < 1/2`, and `BAbulk d L g (1/2) E` holds for no `E`: at that `κ` the four conjuncts of the example are applied over an empty bulk. The `d = 3` examples use `κ_* = Im m₀/π` with a bulk point. If T2534 keeps the probe's `κ`, the example is degenerate in the sense of CLAUDE.md §4 step 2.
4. **Statement-level facts for the paper-delta list** (each is documented in §2 of the document and already has a row or decision; candidates `T2535a`, `T2535b` only if the dispatcher wants a number): `T2535a`: the PDF states no lower bound on `L`, and the printed `S^{(B)}` of (2.5) is not doubly stochastic for `L ≤ 2`; Lean requires `L n ≥ 3` (rows D1, D63 of `class_1.md`). `T2535b`: (2.19) read with `A ≠ ∅`, since for `A = ∅` the event is `0 ≥ 0` (DECISIONS §10, T2001f). Other §2 items correspond to rows D20 (sequences), D501 (distance), D502 (`η` in the proof of Theorem 2.1), D19 (indexing from 0), D22 (`Ring.inverse`), D24 (unused coordinates) and DECISIONS §10, §11, §51.
5. `pdftotext` is missing on this machine; the page checks used `pypdf`.
