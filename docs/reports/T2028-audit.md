Auditor model: claude-opus-5-5

# T2028 audit (S1-07: ST pins `Induction/Defs`, port `Green/Pins`, registry), round 2

Generated Sat Oct  3 08:01:16 UTC 2026 (`date -u`). Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2028-audit2`, detached at `t/T2028`.
SP = `/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/d787b0e7-ec73-431d-9968-a805c3e11390/scratchpad`.

**Round 1** (07:56 UTC, same commit `f9fce58`): Target 1 PASS, Target 3 PASS, Target 2 RETURN on paper-delta
coverage only (missing candidates for the diagonal-only `GiiOmegaSeq`/`GiiSeq`/`GiiGEXPT` vs (`GiiGEX`) `3_5:21`,
and for the indicator-free clause of `GbEXPHypV3` under (`asGMc`)); repair was declared report-only.
The repair added `T2028e`, `T2028f` and a "Repair" section to the prove report; no `.lean` change.

## 1. Commit identity, build, axioms, hygiene, scope
```
$ git rev-parse main t/T2028 ; git merge-base main t/T2028 ; git log --oneline main..t/T2028
cca94be7c231e05e62847e0b78a0773213948d04
f9fce5826722d6bb9c22743421ca2da69bf8f5e6          # = round-1 audited commit
1892ec6a4eb100794b7b9372393264cddffb7687
f9fce58 T2028: registry comments cite the RBM2D lines of gijOmegaSeq and goodSet_asGMc
6213186 T2028: bridges AsGMcPT/LoopDetSeq, time-zero checks, fully discharged bridge instance
7f5c0f8 T2028: S1-07 ST pins (Induction/Defs), Green/Pins port with ST bridges, registry entries
$ lake build RBM3D.Induction.Defs RBM3D.Green.Pins | grep -E "error|warning|Build completed"
Build completed successfully (3313 jobs).          # exit=0
$ lake build | grep -E "^error|Build completed"    # whole library at the branch base
Build completed successfully (3728 jobs).          # exit=0
$ lake env lean $SP/t2028r2_pre.lean   # import RBM3D; import RBM3D.Induction.Defs; import RBM3D.Green.Pins; #assert_rbm_axioms
axiom audit: 1137 theorems, 465 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
All within [propext, ...
premises found by scanning: 22 (borrowed 3, owed 14, structural 5).
registry: 11 borrowed + 18 owed + 15 structural; ...
pre exit=0
$ lake env lean $SP/t2028r2_ax.lean   # #print axioms
'RBM.Green.gijGEXPTSwap_giiGEXPT_of_V3' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Green.stGbEXP_of_v3' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Green.stGiiGEX_of_omegaSeq' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Green.stGijGEX_of_gijOmegaSeq' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Green.v3_premises_of_stFlow' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Green.norm_loopPM_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Green.Instance.inst_stGbEXP_of_v3' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Green.Instance.inst_bridges_time_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Green.Instance.inst_gijGEXPTSwap' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.InductionDefsInst.inst_step1_lowg' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.InductionDefsInst.inst_mainInd' depends on axioms: [propext, Classical.choice, Quot.sound]
$ grep -nE "sorry|admit|native_decide|^\s*axiom\b" RBM3D/Induction/Defs.lean RBM3D/Green/Pins.lean ; echo "exit=$?"
exit=1
$ git diff --name-only main...HEAD
RBM3D/Green/Pins.lean
RBM3D/Induction/Defs.lean
RBM3D/Test/Axioms.lean
```
Name clashes against current `main` (cca94be), 152 short `def/theorem/abbrev/lemma/structure` names of the two files:
```
$ comm -12 $SP/t2028r2_names.txt $SP/t2028r2_main.txt
z0
z0_im_pos
```
Both are in distinct namespaces (`RBM.Gauss.InductionDefsInst` here, `RBM.Gauss.GLoopFlowInst` in `Loop/GLoopFlow.lean:925`),
and `Induction/Defs` imports `GLoopFlow` and builds: no clash.

## 2. Targets 1-3: statements, instances (unchanged since round 1)
The Lean files are byte-identical to the round-1 commit, so the round-1 findings stand and are not repeated:
Target 1 probe-text diffs `IDENTICAL1`/`IDENTICAL3` (sections 1/1b/2 and 3 of `752e027`, binding rewrite only);
Target 2 statement comparison with RBM2D `c9a24cf` (R1 `Admissible`/`𝔡`, R2 index renaming), bridges and the
23 instances of `RBM.Green.Instance` at `sz0`, `z_n = 1/2 + i N_n^{-4/5}`, `t ≡ 1/16` (nondegenerate, deterministic
hypotheses discharged, pins left as hypotheses); Target 3 append-only registry with the §19 classes.

## 3. Paper-delta coverage (the round-1 defect)
Repair content, `docs/reports/T2028-prove.md` (d) (274 lines, ≤ 300):
```
$ grep -o "T2028[a-z]" docs/reports/T2028-prove.md | sort -u
T2028a T2028b T2028c T2028d T2028e T2028f
```
Verification of the facts cited by `T2028e`/`T2028f` against the file and the paper:
```
$ sed -n '141,144p;164,167p;290,293p' RBM3D/Green/Pins.lean   (abridged to the summands)
141 def GiiOmegaSeq ... omegaInd ... * diagSq ... p.2           # U = Unit × Idx: diagonal only
164 def GiiSeq      ... diagSq ... p.2                          # diagonal only, no indicator
290 def GiiGEXPT    ... ‖Gt sz n (E n) p.1 true ω p.2 p.2 - mE (E n)‖ ^ 2   # diagonal only
$ sed -n 210,220p RBM3D/Green/Pins.lean
def GbEXPHypV3 (κ 𝔠 𝔡 δ : ℝ) : Prop :=
  sz.Admissible 𝔠 𝔡 → ∀ E t ..., sz.RangeCond δ t → ∀ c > (0 : ℝ),
    GijOmegaSeq sz E t c ∧ GiiOmegaSeq sz E t c ∧
    (AsGMcSeq sz E t c → GijSeq sz E t ∧ GiiSeq sz E t ∧ ∀ (Ψ : ℕ → ℝ) (a : ℝ), ... → GavLDetSeq sz E t Ψ)
$ sed -n 871,873p RBM3D/Green/Pins.lean
theorem stGiiGEX_of_omegaSeq {E t : ℕ → ℝ} {c 𝔠 𝔡 : ℝ} (hA : sz.Admissible 𝔠 𝔡)
    (hE : ∀ n, |E n| ≤ 2) (hc : 0 < c)
    (hii : GiiOmegaSeq sz E t c) (hij : GijOmegaSeq sz E t c) : STGiiGEX sz E t c := by
$ grep -n "GiiSeq\|GijSeq" RBM3D/Green/Pins.lean | grep -v "^1[46][0-9]:"
216:      GijSeq sz E t ∧ GiiSeq sz E t ∧                       # GbEXPHypV3
316:      GijSeq sz E u ∧ GiiSeq sz E u := by                   # inside gijGEXPTSwap_giiGEXPT_of_V3 (:310)
1379:      GijSeq sz E (fun _ => 0) ∧ GiiSeq sz E (fun _ => 0) ∧  # time-zero check
1549:      GijSeq sz0 (STflowE z0) (fun _ => 0) ∧ ...            # instance
$ grep -n -i "without the indicator\|GijSeq\|GiiSeq\|asGMc" docs/DECISIONS.md docs/paper-deltas.md ; echo "exit=$?"
exit=1
$ sed -n 20,22p paper/tex/3_5*.tex     # (GiiGEX): 1(Ω(t,ε₀))·‖G_t−M‖²_max ≤ W^τ max L^{(2)}_{t,(-,+),(a,b)}
$ sed -n 28,30p paper/tex/3_5*.tex     # (initialGT2): ‖G_t − M‖_max ≺ W^{-ε₀}, max L^{(2)} ≺ Ψ_t² ; only (GavLGEX) is concluded under it
```
* **Required item 1** (diagonal-only `Gii*` candidate): `T2028e` states the difference (diagonal `|G_pp − m|²` vs
  `‖G_t − M‖²_max`, `3_5:21`), the recovery of the paper's form from `GiiOmegaSeq ∧ GijOmegaSeq` by
  `stGiiGEX_of_omegaSeq` (:871, hypotheses `Admissible`, `|E| ≤ 2` as in the signature above), that `GiiSeq`/`GiiGEXPT`
  alone are weaker, and their only consumer (`gijGEXPTSwap_giiGEXPT_of_V3`, :310; no use outside the file, grep in
  the Repair section). Line numbers checked above. It also covers observation O2 (`PrecPT` vs uniform `≺`).
  **Covered.**
* **Required item 2** (indicator-free clause): `T2028f` names the third clause of `GbEXPHypV3` (:216), states that
  `lem_GbEXP` (`3_5:14-40`) displays only the indicator forms and, under (`initialGT2`), only (`GavLGEX`), that it is
  RBM2D's reading kept as ported, that no signed entry covers it (grep exit 1 above), and that no theorem of the file
  derives it (true: the only producers at :1379/:1549 are the time-zero check and its instance, not a derivation from
  the indicator forms). **Covered.**
* **Required item 3**: report length 274 ≤ 300. **Met.**

Coverage now: T2028a (R1 `Admissible`/`𝔡`), T2028b (one-orientation `gexRHS`), T2028c (`Ψ` range), T2028d
(`RangeCond`), T2028e (diagonal-only `Gii*`, per-time `≺`), T2028f (indicator-free clause). I find no further
Lean/paper statement difference in the ported pins beyond these and the signed entries cited in round 1.

## 4. Observations (no verdict effect)
* O1 (round 1, still open): the `AsGMcPT` registry comment names RBM2D `Path/GoodSet.lean:439` but no P.7 ticket.
* O3: `main` moved since the branch base (1892ec6 → cca94be). `git merge-tree --write-tree main t/T2028` reports a
  content conflict in `RBM3D/Test/Axioms.lean` only, in two hunks, both inside the registry lists: `owedProps`
  (main adds `RBM.Green.GaussIBP`; branch adds 16 owed names) and `structuralProps` (main adds 8 names; branch adds
  `STConStInd`, `STFlow`). DECISIONS §20 (3) prescribes the union at merge, followed by the full build; the hub
  must re-join the list closers (`]`) when taking the union. No other file conflicts.
* O4: `T2028f` could add that, with `Ω(t,c)` defined at the same `c` as (`asGMc`), the indicator-free form does not
  follow from the indicator form by `c` alone (the `≺` loss `W^τ` needs `Ω(t,c−τ)`); this is a wording point for the
  dispatcher when numbering, not a coverage gap.

## 5. Verdicts
* Target 1 (`RBM3D/Induction/Defs.lean`): **PASS** (round 1, file unchanged).
* Target 2 (`RBM3D/Green/Pins.lean`): **PASS** (statements, instances, build, axioms as round 1; paper-delta
  coverage repaired by `T2028e`, `T2028f`).
* Target 3 (registry, `RBM3D/Test/Axioms.lean`): **PASS** (O1; merge union per §20, O3).
* No dispatcher sign-off is requested by the audit; the candidate classes and `T2028a` (R1) go to the dispatcher's
  normal numbering, as stated in round 1.

**Ticket verdict: PASS.**
