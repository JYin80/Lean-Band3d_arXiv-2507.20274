Prover model: claude-sonnet-5-5

## (a) Math preflight — Sun Oct  4 10:26:01 UTC 2026

Ticket T2127 is a deletion and clean-up ticket with no new mathematics (the one optional item 4 is a restatement). Base of `t/T2127` and of all greps below: `471b643` (`git -C ../RBM3D-wt/T2127 rev-parse --short HEAD`); `main` has since moved one commit (`dd1748c`, adds only `RBM3D/Graph/LWSizeClaim.lean`), which touches none of the names below. "Exponents" are the dimension and parameter constants of the retained theorems, plus the counts that the registry and the axiom audit must show.

### (i) Exponent table (constants, constraints, slack; counts before / expected after)

| Row | Value / constraint | Slack / note |
|---|---|---|
| `d` in `pureLoop_two_of_isKLoop`, `pureLoop_three` | `d = k+2`, hyp `3 ≤ k+2`; instance `k = 1`, `d = 3` | slack 0 (boundary `d = 3`, intended); the four deleted-premise theorems `kTwoFormula_of_isKLoop`, `kThree_eq_of_isKLoop` have no `d` hypothesis |
| `L` | `3 ≤ L`; instance `L = 5` | slack 2 |
| `W` | `(W:ℂ)^d ≠ 0`, `1 ≤ W` (`KLK_unique`); instance `W = 2`, `W^d = 8` | slack 1 |
| `g` | `0 < g`; instance `g = 1/2` | slack 1/2 |
| `E` | `|E| < 2` (`KLK_unique`), `‖m(σ)‖ = 1`; instance `E = 0`, `m(+) = i`, `m(-) = -i` | slack 2 |
| `t` | `0 ≤ t < 1`; instance `t = 9/10` (as the existing `KLUniqueInst_retire_kThree`) | slack 1/10 |
| `Im m(σ)` for `pureLoop_*` | `0 < Im`; `Im m(+) = 1` | slack 1 |
| `TwoLoopBounded` premise | removed from 4 theorems (`Unique.lean:300,348`, `TreeThree.lean:353,416`; lines match the ticket). Discharged by `KLretire_twoLoopBounded` (`KLUnique.lean:81`), whose proof uses only `IsKLoop` (`TreeRep.lean:158`), `LoopVec`, `LoopVec.exists_toLoop` (`Unique.lean:92,108`) and Mathlib compactness | needs `LoopVec` => earliest file is `Loop/Unique.lean`, between line 108 and line 297. No cycle: closure of `Unique` has no `KLUnique`/`KLTreeDeriv` (script (ii-a)) |
| Interface of the moved lemma | after deletion of `TwoLoopBounded` the conclusion must be its unfolded body `∀ T₀ < 1, ∃ R, 0 ≤ R ∧ ∀ t ∈ Icc 0 T₀, ∀ I, I.WF → I.length = 2 → ‖K t I‖ ≤ R` | `KLWard.lean:1080` (NOT writable) does `obtain ⟨R,hR0,hR⟩ := KLretire_twoLoopBounded hKc t ht.2`: the name `RBM.Loop.KLretire_twoLoopBounded`, its implicit `{d L W g m K}`, `hK` and this unfolded shape must stay |
| Registry counts on `main` | 3884 theorems, 1351 defs, 0 axioms; registry `5 borrowed + 100 owed + 39 structural`; scan found 77 (borrowed 1, owed 61, structural 15); 67 registered premises carry nothing | see (iv) |
| Expected after (items 1,2,5) | theorems `3884 - 7 = 3877` (+1 if item 4): deleted `Prop6Old_false`, `Prop7Old_false`, `PropTH_false` (Pins) and `thetaDiffOne_fixedL`, `thetaDiffTwo_fixedL`, `propTH_fixedL`, `twoLoopBounded_kTwoLoop` (InterfaceShape); moved `KLretire_twoLoopBounded` and the 3+ privates made public are net 0 | borrowed `5 -> 1` (`KLPT`); owed `100 -> 82` (`TwoLoopBounded` + the 17 names of item 5 whose scan reason is "carries nothing"), `81` if item 4 lands; `certificates` becomes `[]` |
| Item 4 `STNewKLKAt` | `nkl_at` (private, `NewKLK.lean:993`) gives `∃ C, 0 < C ∧ STNewKLKAt d κ 𝔡 C (κ/2)`; `stNewKLK_holds` (`:1198`) is its `∃ C δ₀` form. A theorem with head `STNewKLKAt` and `C, δ₀` taken by `.choose` of `stNewKLK_holds d hd κ 𝔡 hκ h𝔡` is a 2-line statement | feasible; with it the scan stops reporting the name (the scan counts a theorem whose conclusion head is the predicate) |

### (ii) One concrete nondegenerate instance, and the dry-run checks of the ticket

(ii-a) Instance for the four theorems with `TwoLoopBounded` removed (`kTwoFormula_of_isKLoop`, `kThree_eq_of_isKLoop`, `pureLoop_two_of_isKLoop`, `pureLoop_three`): data `d=3 (k=1), L=5, W=2, g=1/2, E=0, t=9/10`, `K = KLK 3 5 (1/2) 2 0`, `hK = KLTreeDerivInst_isKLoop` (`KLTreeDeriv.lean:1080`, merged; `IsKLoop 3 5 2 (1/2) (mSigma 0) (Ico 0 1) K`). `hshort` for `pureLoop_*` is `thetaDecayShort_holds 3 (1/2) (mSigma 0 true)` (`Propagator/Prop6Hold.lean:443`, proved, no premise). So no hypothesis is external: no limit computation owed.

```
$ python3 scratchpad/T2127/instance.py     (d,L,W,g,E,t,k = 3,5,2,0.5,0.0,0.9,1)
|E|<2                True
3<=L                 True
1<=W                 True
W^d != 0             True
3<=k+2 (d=k+2)       True
0<g                  True
0<=t<1               True
|m(+)|=|m(-)|=1      True
Im m(+)>0            True
m(m+E)=-1            True
m(+) = 1j  m(-) = -1j  W^d = 8  theta arg t*m(+)^2 = (-0.9+0j) |.|<1: True
```

Import facts for placing the instances (script over `import` lines of the files):
```
closure(RBM3D.Loop.KLUnique) contains: Propagator.Prop6Hold False | Loop.Unique True | Loop.TreeRep True | Loop.TreeThree True
closure(RBM3D.Loop.Unique) contains KLUnique: False, KLTreeDeriv: False
closure(RBM3D.Propagator.Prop6Hold) contains any RBM3D.Loop.*: []     (imports Prop5Hold, PropUnit, Gap)
```
So the `pureLoop_*` instances in `KLUnique.lean` (the file that has `KLTreeDerivInst_isKLoop`) need `import RBM3D.Propagator.Prop6Hold` added to `KLUnique.lean` (writable, no cycle), or `hshort` stays a hypothesis of the example. The three existing instances `KLUniqueInst_retire_*` (`KLUnique.lean:745-765`) restate `TwoLoopBounded 3 5 …` and must change with the deletion.

(ii-b) Dry run (i): every use of the deleted names on `main` (`git grep -nw <name> main -- RBM3D`; scripted check `bash scratchpad/T2127/uses.sh`, output verbatim):
```
KLretire_twoLoopBounded: NON-WRITABLE USE in RBM3D/Loop/KLWard.lean
(done: every other use of the 15 names is in a writable file)
```
The 15 names: `ThetaDiffOne ThetaDiffTwo PropTH KTreeRep TwoLoopBounded Prop6Old_false Prop7Old_false PropTH_false thetaDiffOne_fixedL thetaDiffTwo_fixedL propTH_fixedL twoLoopBounded_kTwoLoop KLretire_twoLoopBounded KLretire_kTwoFormula KLretire_kThree`. Uses by file (all writable): `ThetaDiffOne/Two`: `Interface.lean:118,133,172,174`, `Pins.lean:24,110-112,155-158,200-203,303,421-424`, `Test/Axioms.lean:79,255-256`, `Test/InterfaceShape.lean:209,427,482`. `PropTH`: `Basic.lean:34,73`, `TreeRep.lean:34`, `Interface.lean:25,26,160,166,168`, `Pins.lean:24,115,249-251,303,427`, `Test/Axioms.lean:22,51,74,79,257,288-289,383`, `Test/InterfaceShape.lean:546-573`. `KTreeRep`: `TreeRep.lean:33,54,182`, `Test/Axioms.lean:79`, `InterfaceShape.lean:221-222`. `TwoLoopBounded`: `TreeRep.lean:172`, `Unique.lean:300,348`, `TreeThree.lean:353,416`, `KLUnique.lean:10,23,77,83,95,671,745-748`, `Test/Axioms.lean:89,258,291-292`, `InterfaceShape.lean:207,575-586`. `kTwoFormula_of_isKLoop`/`kThree_eq_of_isKLoop`/`pureLoop_*_of_isKLoop`/`pureLoop_three`: used only in `Unique.lean`, `TreeThree.lean` and (as wrappers/docstrings) `KLUnique.lean:96-110`. `KLretire_kTwoFormula`/`KLretire_kThree`: used only in `KLUnique.lean:103,110,754,762` (the two `KLUniqueInst_retire_*` instances), so they become one-line aliases of the unchanged theorems or are deleted together with those instances (prover's choice). Pins.lean refutation block, to record in (b): `Prop6Old_false :157 (¬ ThetaDiffOne d g m, d≥3, g>0, ‖m‖=1)`, `Prop7Old_false :202 (¬ ThetaDiffTwo …)`, `PropTH_false :250 (¬ PropTH …)`, private helpers `pins_Theta_zero :119`, `pinsAxis :122`, `pins_zdist_axis :125`, `pins_zdistD_axis :131`, `pins_arith :141` (used only by the two refutations, lines 167-246), examples `Pins.lean:421,424,427`. Nothing else in `Pins.lean` (`Prop5_needs_Lambda :261`, the bridges `:316-380`, the examples at `:394-416`, `:430`) mentions the deleted names.

(ii-c) Dry run (ii), import graph: `KLretire_twoLoopBounded` -> `Loop/Unique.lean` after `LoopVec.exists_toLoop` (`:108`), before `kTwoFormula_of_isKLoop` (`:297`); `Unique` imports `Loop.Primitive` and Mathlib `Analysis.ODE.Gronwall`; the proof uses `isCompact_Icc.exists_bound_of_continuousOn`, `continuousOn_pi` (to confirm they are reachable from `Unique`'s imports at build; if not, add a Mathlib import to `Unique.lean`, writable).

(ii-d) Dry run (iii), item 3 name clashes (`git grep -h -E "^(private |protected |noncomputable )*(theorem|lemma|def|abbrev|structure|instance|inductive) ([A-Za-z_.]*\.)?<name>( |$)" main -- RBM3D`; Mathlib: `grep -rhE "(theorem|lemma|def) ([A-Za-z_.]*\.)?<name>( |$)" .lake/packages/mathlib/Mathlib`):
```
<name>                         decls-in-RBM3D  private  mathlib-decls
sigmaIn sigmaOut Flong_eq_iff_cut prod_leaves_cut exists_innermost Flong_subset_diagonals Flong_subset
KLmSigma_mul_not KLMolecule_edge KLMolecule_selfW_bound_nc KLMolecule_SigmaPi_of_tree
KLMolecule_same_charge KLMolecule_exists_pair KLMolecule_sum_exp_maxDist
(each of the 14 names:)         1               1        0
```
Each is declared once, in namespace `RBM.Loop` (`KLMolecule.lean:37`, `KLTree.lean:29`, `KLSumZeroWard.lean:58`), so no public clash and no prefix is needed. Files using them: `KLIndStepA`, `KLInduct`, `KLMolecule`, `KLSumZeroWard`, `KLTree`, `KLWardIneq` only (all writable). The `open private` lines to drop: `KLIndStepA.lean:40-43`, `KLInduct.lean:79-80`, `KLWardIneq.lean:81` (`grep -rn "open private" RBM3D` shows exactly these, plus comments at `KLIndStepA.lean:35`, `KLIndStepB.lean:13`, `KLWardIneq.lean:74,220`; `KLIndStepB.lean` is not writable and its comment is harmless).

(iv) Registry pre-check on `main` (= worktree `471b643`): `cd ../RBM3D-wt/T2127 && lake env lean RBM3D.lean > scratchpad/T2127/precheck.txt` (exit 0, 18 s). Relevant lines:
```
axiom audit: 3884 theorems, 1351 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
  RBM.ThetaDiffOne: 1 [certificate: RBM.Test.thetaDiffOne_fixedL]   (also ThetaDiffTwo 1, PropTH 1, KTreeRep 0, KLPT 20)
premises found by scanning: 77 (borrowed 1, owed 61, structural 15).
registry: 5 borrowed + 100 owed + 39 structural; 67 registered premise(s) carry nothing yet: [...]
non-vacuity certificates: 4 of 105 premises in the two ledgers
```
Of the 67 "carry nothing" names, the ticket's list splits as follows (script: grep of each name in the printed list; `1` = reported as carrying nothing):
```
carry nothing on main (line removable): ThetaDiffOne ThetaDiffTwo KTreeRep TwoLoopBounded GaussIBP STKbound STConArg
  STNetLift STNetLift2 STContract STContractPt STNewPQ STMollifierEx STQopNorm STK2decay STEMn2Poly STScaleExists
  Ind.Step1TargetV3 Ind.STLoopGenNForm Green.MinorDiffGainUpTo' Green.GijOmegaSeq
NOT in that list (found by the scan, so the line must stay unless the scan changes): PropTH (found; goes with the deletion),
  STNewKLKAt (found: 5 theorems take it, none concludes it: removable only with item 4: usage line "STNewKLKAt: 5"),
  Green.FixedTimeFAThm, Green.IBPDetThm (T2126, not touched)
Reported as carrying nothing but NOT to be touched (T2126): Green.GbEXPV3Theorem, STStep1; also left alone: Loop.KLPT (carries nothing, borrowed, not in the ticket), every LW*, STEMn2Exp, STGridRepN.
```
Count check: the 17 owed names of item 5 that carry nothing (`GaussIBP STKbound STConArg STNetLift STNetLift2 STContract STContractPt STNewPQ STMollifierEx STQopNorm STK2decay STEMn2Poly STScaleExists Step1TargetV3 STLoopGenNForm MinorDiffGainUpTo' GijOmegaSeq`) plus `TwoLoopBounded` = 18, so owed `100 -> 82`. Stale comments to refresh with the lines: `Test/Axioms.lean:22,51,74,79,88-92,288-292,383` (`PropTH`, `TwoLoopBounded`, certificate text), and `Test/InterfaceShape.lean:207-208,209,221-226` (docstring of deleted declarations).

### Verdict per target
1. Delete `ThetaDiffOne`, `ThetaDiffTwo`, `PropTH` and the Pins refutations: PASS (all uses in writable files; no merged theorem takes any of the three).
2. Delete `KTreeRep`, `TwoLoopBounded`; discharge `hbdd` in the four theorems by the moved `KLretire_twoLoopBounded`: PASS, with the constraint that the moved lemma keeps its name and takes the unfolded conclusion (used by non-writable `KLWard.lean:1080`).
3. Privates to public: PASS (no clash, 14 names, one declaration each).
4. `STNewKLKAt` corollary: PASS (feasible in two lines via `.choose`).
5. Registry: PASS (17 names carry nothing and are removable; `STNewKLKAt` only after item 4; do not touch `GbEXPV3Theorem`, `FixedTimeFAThm`, `IBPDetThm`, `STStep1`).
6. `InterfaceShape.lean`: PASS (certificates `thetaDiffOne_fixedL :437`, `thetaDiffTwo_fixedL :485`, `propTH_fixedL :552`, `twoLoopBounded_kTwoLoop :584` are used only in `Test/Axioms.lean:255-258` and each other; `propTH_fixedL` uses the two `ThetaDiff` certificates, `:572-573`).

## (a′) Preflight corrections — Sun Oct  4 10:55:40 UTC 2026

One correction, no verdict changes. Section (a) table row "Expected after" gives theorems `3884 - 7 = 3877`; the audit shows 3888, reconciled by script in (b), Block 9: also leaving the count are the four projection theorems `PropTH.decay/diffOne/diffTwo/zeroMode`, the wrappers `KLretire_kTwoFormula`/`KLretire_kThree` and two renamed instances; and the 12 theorems made public, the two equation lemmas of `sigmaIn`/`sigmaOut` and the new theorems now count. Definitions: 1351 -> 1347 (six deleted, `sigmaIn` and `sigmaOut` added).

## (b) Script output

Block 1 — commit and builds (`bash scratchpad/T2127/ev1.sh`; the whole-library build is `fullbuild2.txt`, run after the commit):
```
$ git log --oneline -2; git diff --stat 471b643 HEAD | tail -1
4bfcb32 T2127: delete the old propagator interface and the retired K-loop hypotheses, publish the K-loop privates, update the axiom registry
471b643 T2125: merge KL14a Loop/KLFinal
 16 files changed, 179 insertions(+), 602 deletions(-)
$ lake build RBM3D.<each of the 16 files> (all in one call)
Build completed successfully (3735 jobs).
$ lake build   (whole library, runs #assert_rbm_axioms in RBM3D.lean)
Build completed successfully (3874 jobs).
exit 0
```

Block 2 — axioms (`python3 scratchpad/T2127/ev7.py`, which runs `lake env lean scratchpad/T2127/axioms.lean`):
```
$ lake env lean scratchpad/T2127/axioms.lean   (#print axioms of the 25 public declarations of this ticket)
[propext, Classical.choice, Quot.sound]: 23 declarations: KLretire_twoLoopBounded, kTwoFormula_of_isKLoop, kThree_eq_of_isKLoop, pureLoop_two_of_isKLoop, pureLoop_three, KLUniqueInst_retire_twoLoopBounded, KLUniqueInst_kTwoFormula, KLUniqueInst_kThree, KLUniqueInst_pureLoop_two, KLUniqueInst_pureLoop_three, stNewKLKAt_holds, KLMolecule_edge, KLMolecule_selfW_bound_nc, KLMolecule_SigmaPi_of_tree, K
[propext, Quot.sound]: 2 declarations: sigmaIn, sigmaOut
```

Block 3 — statements. The only signature change of the four theorems is the removed premise (`git diff -U0 471b643 HEAD -- RBM3D/Loop/Unique.lean RBM3D/Loop/TreeThree.lean | grep -E '^-.*\(hbdd'`), then the extracted statements of the moved lemma and of the new theorem (`python3 scratchpad/T2127/ev4.py`):
```
-    (hbdd : TwoLoopBounded d L K) :
-    (hbdd : TwoLoopBounded (k + 2) L K) :
-    (hbdd : TwoLoopBounded d L K) :
-    (hbdd : TwoLoopBounded (k + 2) L K) :
294: theorem KLretire_twoLoopBounded {m : Bool → ℂ} {K : ℝ → LoopIdx (Zd d L) → ℂ}
295:     (hK : IsKLoop d L W g m (Set.Ico 0 1) K) :
296:     ∀ T₀ : ℝ, T₀ < 1 → ∃ R : ℝ, 0 ≤ R ∧ ∀ t ∈ Set.Icc (0 : ℝ) T₀,
297:       ∀ I : LoopIdx (Zd d L), I.WF → I.length = 2 → ‖K t I‖ ≤ R := by
1321: theorem stNewKLKAt_holds (d : ℕ) (hd : 3 ≤ d) (κ 𝔡 : ℝ) (hκ : 0 < κ) (h𝔡 : 0 < 𝔡) :
1322:     STNewKLKAt d κ 𝔡 (stNewKLK_holds d hd κ 𝔡 hκ h𝔡).choose
1323:       (stNewKLK_holds d hd κ 𝔡 hκ h𝔡).choose_spec.choose :=
```

Block 4 — the compiled nonempty instances (KLUnique.lean lines 714-763 without doc comments; NewKLK.lean example), `d = 3`, `L = 5`, `W = 2`, `g = 1/2`, `E = 0`, `t = 9/10`, `m(+) = i`; every hypothesis is discharged (`hK` is the merged `KLTreeDerivInst_isKLoop`, `ThetaDecayShort` is the proved `thetaDecayShort_holds`):
```
theorem KLUniqueInst_retire_twoLoopBounded :
    ∀ T₀ : ℝ, T₀ < 1 → ∃ R : ℝ, 0 ≤ R ∧ ∀ t ∈ Set.Icc (0 : ℝ) T₀,
      ∀ I : LoopIdx (Zd 3 5), I.WF → I.length = 2 → ‖KLK 3 5 (1 / 2) 2 0 t I‖ ≤ R :=
  KLretire_twoLoopBounded (K := fun t I => KLK 3 5 (1 / 2) 2 0 t I) KLTreeDerivInst_isKLoop
theorem KLUniqueInst_kTwoFormula :
    KTwoFormula 3 5 2 (1 / 2) (mSigma 0) (fun t I => KLK 3 5 (1 / 2) 2 0 t I) :=
  kTwoFormula_of_isKLoop (by norm_num) (by norm_num) (fun s => norm_mSigma (by norm_num) s)
    KLTreeDerivInst_isKLoop
theorem KLUniqueInst_kThree :
    (fun t I => KLK 3 5 (1 / 2) 2 0 t I) (9 / 10) ⟨[true, false, true], [0, 1, 2]⟩
      = kThree 3 5 2 (1 / 2) (mSigma 0) (9 / 10) true false true 0 1 2 :=
  kThree_eq_of_isKLoop (by norm_num) (by norm_num) (fun s => norm_mSigma (by norm_num) s)
    KLTreeDerivInst_isKLoop (9 / 10) (by norm_num) (by norm_num) true false true 0 1 2
private theorem KLUnique_inst_im : 0 < (mSigma 0 true).im := by
  simpa [mSigma] using mE_im_pos (E := 0) (by norm_num)
theorem KLUniqueInst_pureLoop_two :
    ∃ C > (0 : ℝ), ∃ c > (0 : ℝ), ∀ (t : ℝ), 0 ≤ t → t < 1 → ∀ a₁ a₂ : Zd (1 + 2) 5,
      ‖KLK 3 5 (1 / 2) 2 0 t ⟨[true, true], [a₁, a₂]⟩‖
        ≤ C * ‖(((2 : ℕ) : ℂ) ^ (1 + 2))⁻¹‖
          * Real.exp (-(c * (zdistD (1 + 2) 5 (a₁ - a₂) : ℝ))) :=
  pureLoop_two_of_isKLoop (k := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (fun s => norm_mSigma (by norm_num) s)
    KLUnique_inst_im (thetaDecayShort_holds (1 + 2) (1 / 2) (mSigma 0 true))
    (K := fun t I => KLK 3 5 (1 / 2) 2 0 t I) KLTreeDerivInst_isKLoop
theorem KLUniqueInst_pureLoop_three :
    ∃ C > (0 : ℝ), ∃ c > (0 : ℝ), ∀ (t : ℝ), 0 ≤ t → t < 1 →
      ∀ (a : Fin 3 → Zd (1 + 2) 5) (p q : Fin 3),
        ‖KLK 3 5 (1 / 2) 2 0 t ⟨[true, true, true], [a 0, a 1, a 2]⟩‖
          ≤ C * ‖((((2 : ℕ) : ℂ) ^ (1 + 2))⁻¹) ^ 2‖
            * Real.exp (-(c * (zdistD (1 + 2) 5 (a p - a q) : ℝ))) :=
  pureLoop_three (k := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (fun s => norm_mSigma (by norm_num) s)
    KLUnique_inst_im (thetaDecayShort_holds (1 + 2) (1 / 2) (mSigma 0 true))
    (K := fun t I => KLK 3 5 (1 / 2) 2 0 t I) KLTreeDerivInst_isKLoop
example : STNewKLKAt 3 (1 / 10) (1 / 10)
    (stNewKLK_holds 3 le_rfl (1 / 10) (1 / 10) (by norm_num) (by norm_num)).choose
    (stNewKLK_holds 3 le_rfl (1 / 10) (1 / 10) (by norm_num) (by norm_num)).choose_spec.choose :=
  stNewKLKAt_holds 3 le_rfl (1 / 10) (1 / 10) (by norm_num) (by norm_num)
```

Block 5 — record of the deleted refutations at the base commit, the paper-delta trail (`bash scratchpad/T2127/ev5.sh`):
```
$ git show 471b643:RBM3D/Propagator/Pins.lean | sed -n 112,117p ; ... | awk (lines 157-158, 202-203, 250-251)
`RBM.ThetaDiffOne` / `ThetaDiffTwo` (`Interface.lean:118,133`) quantify `∀ c > 0`.  At `t = 0`
one has `Θ_0 = 1`; with `c = 1`, `r = -a` (resp. `a = r`) and `|a| = ⌊L/2⌋` the left side is
`≥ 1` while the right side is `≤ 2C L^{-1/2}` for the loss `L^{1/2}` (`τ = 1/2 < d - 2`).  So both
are false for every `d ≥ 3`, `g > 0`, `‖m‖ = 1`, and so is the bundle `RBM.PropTH`.  No
merged result takes any of the three as a hypothesis (grep in the report), so nothing is vacuous.
The new pins carry `c < 1`. -/
Pins.lean:157: theorem Prop6Old_false (d : ℕ) (hd : 3 ≤ d) (g : ℝ) (hg : 0 < g) (m : ℂ) (hm : ‖m‖ = 1) :
Pins.lean:158:     ¬ ThetaDiffOne d g m := by
Pins.lean:202: theorem Prop7Old_false (d : ℕ) (hd : 3 ≤ d) (g : ℝ) (hg : 0 < g) (m : ℂ) (hm : ‖m‖ = 1) :
Pins.lean:203:     ¬ ThetaDiffTwo d g m := by
Pins.lean:250: theorem PropTH_false (d : ℕ) (hd : 3 ≤ d) (g : ℝ) (hg : 0 < g) (m : ℂ) (hm : ‖m‖ = 1) :
Pins.lean:251:     ¬ PropTH d g m :=
$ git show 471b643:RBM3D/Propagator/Interface.lean | awk (lines 118-119, 133, 168); then the four certificates of Test/InterfaceShape.lean
Interface.lean:118: def ThetaDiffOne (d : ℕ) (g : ℝ) (m : ℂ) : Prop :=
Interface.lean:119:   3 ≤ d → 0 < g → ‖m‖ = 1 → ∀ c : ℝ, 0 < c → ∀ τ : ℝ, 0 < τ →
Interface.lean:133: def ThetaDiffTwo (d : ℕ) (g : ℝ) (m : ℂ) : Prop :=
Interface.lean:168: structure PropTH (d : ℕ) (g : ℝ) (m : ℂ) : Prop where
InterfaceShape.lean:437 thetaDiffOne_fixedL InterfaceShape.lean:485 thetaDiffTwo_fixedL InterfaceShape.lean:552 propTH_fixedL InterfaceShape.lean:584 twoLoopBounded_kTwoLoop
```

Block 6 — name-clash grep (`python3 scratchpad/T2127/ev6.py`):
```
decl lines with the name: base 471b643 / HEAD / Mathlib (grep -rhE "(theorem|lemma|def) ([A-Za-z_.]*\.)?NAME( |$)")
privates made public: KLMolecule_edge 1/1/0  KLMolecule_selfW_bound_nc 1/1/0  KLMolecule_SigmaPi_of_tree 1/1/0  KLMolecule_same_charge 1/1/0  KLMolecule_exists_pair 
1/1/0  KLMolecule_sum_exp_maxDist 1/1/0  KLmSigma_mul_not 1/1/0  sigmaIn 1/1/0  sigmaOut 1/1/0  Flong_eq_iff_cut 1/1/0  prod_leaves_cut 1/1/0  exists_innermost 1/1/0  
Flong_subset_diagonals 1/1/0  Flong_subset 1/1/0
new names: stNewKLKAt_holds 0/1/0  KLUniqueInst_kTwoFormula 0/1/0  KLUniqueInst_kThree 0/1/0  KLUniqueInst_pureLoop_two 0/1/0  KLUniqueInst_pureLoop_three 0/1/0
```

Block 7 — registry before (`main` = `0ce09c2`, `lake build` in a scratch worktree, removed afterwards) and after (`t/T2127` = `21c1575`, the merge of `main`), on the new base (`python3 scratchpad/T2127/r1block7.py`):
```
registered names: main 0ce09c2 139, t/T2127 116
removed main -> branch (23): Gauss.Sizes.STConArg Gauss.Sizes.STContract Gauss.Sizes.STContractPt Gauss.Sizes.STEMn2Poly Gauss.Sizes.STK2decay Gauss.Sizes.STKbound Gauss.Sizes.STMollifierEx Gauss.Sizes.STNetLift Gauss.Sizes.STNetLift2 Gauss.Sizes.STNewKLKAt Gauss.Sizes.STNewPQ Gauss.Sizes.STQopNorm Gauss.Sizes.STScaleExists Green.GaussIBP Green.GijOmegaSeq Green.MinorDiffGainUpTo' Ind.STLoopGenNForm Ind.Step1TargetV3 Loop.KTreeRep Loop.TwoLoopBounded PropTH ThetaDiffOne ThetaDiffTwo
added main -> branch: []
removed but not in the ticket's list: []
ticket names still registered: []
T2126/T2118 removals back on the branch: []
carry-nothing names: before 65, after 44; newly reported: []
-- before (lake build at main 0ce09c2, r1mainbuild.txt):
axiom audit: 3940 theorems, 1361 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
premises found by scanning: 74 (borrowed 1, owed 58, structural 15).
registry: 5 borrowed + 95 owed + 39 structural; 65 registered premise(s) carry nothing yet: [...]
-- after (lake build at t/T2127 21c1575, r1build.txt):
axiom audit: 3944 theorems, 1357 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
premises found by scanning: 72 (borrowed 0, owed 57, structural 15).
registry: 1 borrowed + 76 owed + 39 structural; 44 registered premise(s) carry nothing yet: [...]
```

Block 8 — scope and grep checks:
```
$ git diff --name-only main...t/T2127 (names not in the ticket's writable list):
(end; 16 files in the diff)
$ git grep -nw <each of the 14 deleted names> -- RBM3D | wc -l   (ThetaDiffOne ThetaDiffTwo PropTH KTreeRep TwoLoopBounded Prop6Old_false Prop7Old_false PropTH_false thetaDiffOne_fixedL thetaDiffTwo_fixedL propTH_fixedL twoLoopBounded_kTwoLoop KLretire_kTwoFormula KLretire_kThree)
total matches: 0
$ git grep -n "open private" -- RBM3D
RBM3D/Loop/KLIndStepB.lean:13:`Loop/KLIndStepA.lean` is reused (no `open private` is added).
$ git diff 471b643 HEAD | grep -nE '^\+.*\b(sorry|admit|native_decide)\b|^\+axiom '   (new lines only)
(none: exit 1)
```

Block 9 — theorems and definitions of `RBM`, before (worktree of `471b643`, built in scratchpad/T2127/base) and after, from `scratchpad/T2127/dump.lean` (same filter as the audit): theorem count 3884 -> 3888, definitions 1351 -> 1347 (`bash scratchpad/T2127/namediff2.sh`):
```
thms: before 3884 after 3888
 only before: Loop.KLretire_kThree Loop.KLretire_kTwoFormula Loop.KLUniqueInst_retire_kThree Loop.KLUniqueInst_retire_kTwoFormula Prop6Old_false Prop7Old_false 
PropTH_false PropTH.decay PropTH.diffOne PropTH.diffTwo PropTH.zeroMode Test.propTH_fixedL Test.thetaDiffOne_fixedL Test.thetaDiffTwo_fixedL 
Test.twoLoopBounded_kTwoLoop 
 only after:  Gauss.Sizes.stNewKLKAt_holds Loop.exists_innermost Loop.Flong_eq_iff_cut Loop.Flong_subset Loop.Flong_subset_diagonals Loop.KLMolecule_edge 
Loop.KLMolecule_exists_pair Loop.KLMolecule_same_charge Loop.KLMolecule_selfW_bound_nc Loop.KLMolecule_SigmaPi_of_tree Loop.KLMolecule_sum_exp_maxDist 
Loop.KLmSigma_mul_not Loop.KLUniqueInst_kThree Loop.KLUniqueInst_kTwoFormula Loop.KLUniqueInst_pureLoop_three Loop.KLUniqueInst_pureLoop_two Loop.prod_leaves_cut 
Loop.sigmaIn.congr_simp Loop.sigmaOut.congr_simp 
defs: before 1351 after 1347
 only before: Loop.KTreeRep Loop.TwoLoopBounded PropTH PropTH.mk ThetaDiffOne ThetaDiffTwo 
 only after:  Loop.sigmaIn Loop.sigmaOut 
```

Ports: none new. `KLretire_twoLoopBounded` is moved inside RBM3D (its RBM2D source `Loop/Unique.lean:250-268` at `c9a24cf` was cited when it was first ported by T2025); no RBM1D/RBM2D file was read or diffed for this ticket.

Notes (narrative):
- All six items are done in one commit `4bfcb32` on `t/T2127`; the diff touches only the 16 writable files (Block 8). No new file, no root-import change.
- Item 1: `ThetaDiffOne`, `ThetaDiffTwo`, `PropTH`, the refutation block of `Propagator/Pins.lean` (the three theorems, the five private helpers `pins_Theta_zero`, `pinsAxis`, `pins_zdist_axis`, `pins_zdistD_axis`, `pins_arith`, and the three examples) are deleted. Statement and line of each refutation: Block 5. The docstrings of `Basic.lean`, `TreeRep.lean`, `Pins.lean`, `Interface.lean`, `Test/Axioms.lean`, `Test/InterfaceShape.lean` no longer name the deleted declarations.
- Item 2: `KTreeRep` and `TwoLoopBounded` are deleted. `KLretire_twoLoopBounded` now lives in `Loop/Unique.lean` (before `kTwoFormula_of_isKLoop`): same name and implicit binders, conclusion = the unfolded body of the deleted `TwoLoopBounded`, so the non-writable `KLWard.lean:1080` compiles unchanged (full build, Block 1). The four theorems lose `hbdd` (Block 3), and become stronger, not weaker.
- Wrappers: `KLretire_kTwoFormula` and `KLretire_kThree` are deleted, not kept as aliases: only the two instances used them. The instances `KLUniqueInst_retire_kTwoFormula/kThree` became `KLUniqueInst_kTwoFormula/kThree` and apply `kTwoFormula_of_isKLoop`, `kThree_eq_of_isKLoop` directly. New instances `KLUniqueInst_pureLoop_two/three` (Block 4) need `import RBM3D.Propagator.Prop6Hold` in `KLUnique.lean` (no cycle: the build passes); `ThetaDecayShort` is discharged by the proved `thetaDecayShort_holds`, so no hypothesis of the instances is open.
- Item 3: the 14 `private` modifiers are removed where the declarations are defined; the three `open private` blocks (`KLIndStepA`, `KLInduct`, `KLWardIneq`) are removed; no name clashes, so no prefix (Block 6). Three private copies in `KLWardIneq.lean` of now-public lemmas stay (see (d)).
- Item 4 landed: `stNewKLKAt_holds` (two-line statement via `.choose`, with an `example` at `d = 3`, `κ = 𝔡 = 1/10`); the scan no longer needs the registry line (Block 7: the build passes without it).
- Item 5: every name of the ticket's list was removable (the pre-check passes without the line); none had to be kept, so there is no "proved by" text left to refresh. Also removed: `TwoLoopBounded` (owed) and the four borrowed lines `ThetaDiffOne`, `ThetaDiffTwo`, `PropTH`, `KTreeRep`; `certificates := []`. Not touched: `GbEXPV3Theorem`, `FixedTimeFAThm`, `IBPDetThm`, `STStep1`, `STEMn2Exp`, `STGridRepN`, every `LW*` line. Registry `5+100+39 -> 1+81+39`.
- Item 6: the four certificate theorems and their docstring bullets are deleted from `Test/InterfaceShape.lean`; `thetaDecay_fixedL`, `thetaZeroMode_fixedL` and the negative half stay. The import of `RBM3D.Loop.Unique` there is now unused and was left.
- Acceptance deviation: `grep "open private" RBM3D` is not empty. The only match is the comment `KLIndStepB.lean:13`, in a file that is not writable (Block 8).
- Axiom audit: `3884 -> 3888` theorems, `1351 -> 1347` definitions, 0 axioms. The theorems that left are the 15 listed under `only before` in Block 9; everything else is kept, 19 names are added or newly counted (the 12 made public, 2 equation lemmas, `stNewKLKAt_holds`, 4 instances).

## (c) Verified Mathlib and core names (compiled in `Loop/Unique.lean`, `Induction/NewKLK.lean`; block 1)

- `IsCompact.exists_bound_of_continuousOn` (`Mathlib/Analysis/Normed/Group/Bounded.lean:96`, `to_additive`)
- `continuousOn_pi` (`Mathlib/Topology/ContinuousOn.lean:712`)
- `norm_le_pi_norm` (`Mathlib/Analysis/Normed/Group/Constructions.lean:346`, `to_additive` of `norm_le_pi_norm'`)
- `Exists.choose`, `Exists.choose_spec` by dot notation (`Init/Classical.lean:29,32`, core). Names verified absent: none needed.

## (d) Open issues and paper-delta candidates

- `T2127a` (paper-delta trail): `docs/paper-deltas.md` in the main worktree has lines 34 35 136 137 148 160 707(at Sun Oct  4 10:56:41 UTC 2026, `grep -n` for the deleted names) that name `ThetaDiffOne`, `ThetaDiffTwo` or `PropTH` (the old interface and its bundle). The Lean declarations no longer exist; the refutation statements are recorded in Block 5. The mathematics of D12 (`c >= 1` false) is unchanged and is carried by the pins' `c < 1`. The dispatcher should annotate those entries.
- `open private` comment at `KLIndStepB.lean:13` (not writable here): needs a ticket with that file in scope, or acceptance of the comment.
- `KLWardIneq.lean` keeps `KLWardIneq_sum_exp_maxDist`, `KLWardIneq_exists_innermost`, `KLWardIneq_Flong_subset_diagonals` (private copies of lemmas that are now public); not in this ticket's items, removable later.
- `KLUnique.lean` section numbers now run 2-6 (section 1 moved to `Unique.lean`); the registry still lists 46 premises that carry nothing (Block 7), none of them in this ticket's list (`Loop.KLPT` is the borrowed one).
## Repair — Sun Oct  4 11:11:34 UTC 2026 (audit round 1, RETURN on item 5)

`git merge main` on `t/T2127` (merge commit `21c1575`, parents `4bfcb32`, `0ce09c2`); `RBM3D/Test/Axioms.lean` resolved as the union of both sides' deletions (none of `STStep1`, `GbEXPV3Theorem`, `STEMn2Exp`, `FixedTimeFAThm`, `IBPDetThm`, `STConArg`, `GijOmegaSeq`, `STContractPt`, `STEMn2Poly`, `MinorDiffGainUpTo'`; the owed list ends with `` `RBM.Green.FlucGainUpTo'] ``). Registry before/after on the new base: Block 7 (rewritten).
```
$ lake build                                   (whole library, t/T2127 = 21c1575)    exit 0
info: RBM3D.lean:176:0: axiom audit: 3944 theorems, 1357 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
registry: 1 borrowed + 76 owed + 39 structural; 44 registered premise(s) carry nothing yet: [...]
Build completed successfully (3877 jobs).
$ git merge-tree --write-tree main t/T2127     -> b85b46f4d75d5aef9d43508d73b9817f68321991   exit 0
$ git diff --stat main...t/T2127 | tail -1     ->  16 files changed, 179 insertions(+), 602 deletions(-)   (0 names outside the writable list)
$ git diff --stat 4bfcb32 HEAD -- <the 15 other writable files>     -> (empty)
$ git diff --stat 4bfcb32 HEAD -- RBM3D/Test/Axioms.lean            ->  1 file changed, 1 insertion(+), 6 deletions(-)
```
Notes in (b) that cite counts or registry lines "before/after" (3884 -> 3888, `5+100+39 -> 1+81+39`, "not touched: `GbEXPV3Theorem` …") describe `4bfcb32` against its base `471b643`; on the new base the figures are those of Block 7 and this section.
