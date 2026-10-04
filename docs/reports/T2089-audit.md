Auditor model: claude-opus-5-5

# T2089 audit (S1-20, `RBM3D/Green/FlucIter.lean`, first part of RBM2D `Green/FlucIter.lean`), round 1

Written Sat Oct  3 23:57:19 UTC 2026 (`date -u`). Audit worktree `RBM3D-wt/T2089-audit1`, detached at `t/T2089` = `400d42e`.
Scratch: `scratchpad/T2089/` (S below). Pin: the ticket has no pinned Lean text; the pin is ST1-COMMON item 6
("each ported public statement equals RBM2D's after renaming and exponents"), RBM2D `c9a24cf`, and the ticket's
cut instruction (cut at a section/lemma boundary near `:800`; `condRow_eq_condPred` stated for the merged `condRow`).

## 1. Scope of the diff, build, axioms
```
$ git diff --stat main...t/T2089 ; git diff --name-only main...t/T2089
 RBM3D/Green/FlucIter.lean | 1085 +++++++++++++++++++++++++++++++++++++++++++++
RBM3D/Green/FlucIter.lean
$ git diff main...t/T2089 -- RBM3D/Test/Axioms.lean | wc -l
       0
$ git merge-base main t/T2089 ; git log -1 --format=%h main ; git diff --stat 7f9bfa1 3b8c687 -- RBM3D | tail -5
7f9bfa15b1396371fa764c86b92cf44c0823757e
3b8c687
 RBM3D/Green/IBPPoly.lean     | 1157 +++++  RBM3D/Path/DriftAlgebra.lean | 765 +++  RBM3D/Path/LoopStep.lean | 428 +++
 RBM3D/Path/QVIdentity.lean   | 1309 +++++  4 files changed, 3659 insertions(+)      (main since base: new files only)
$ lake build RBM3D.Green.FlucIter 2>&1 | grep -E "error|warning|Build completed|sorry"   (warning lines all upstream)
warning: RBM3D/Green/LDEQuad.lean:24:100: ... [18 `show`/line-length lint warnings in LDEQuad.lean, 1 in FlucVanish.lean:1004]
Build completed successfully (3332 jobs).
exit: 0
$ lake env lean RBM3D/Green/FlucIter.lean; echo "exit: $?"        (no warning or error from this file)
exit: 0
$ grep -cE "\bsorry\b|\badmit\b|native_decide|^\s*axiom " RBM3D/Green/FlucIter.lean
0
$ lake env lean S/ax.lean      (collectAxioms over every non-internal constant whose module is RBM3D.Green.FlucIter)
decls in module: 89; only std axioms: 89; others: #[]
$ cat S/precheck.lean ; lake env lean S/precheck.lean | head -3 ; echo exit      (registry pre-check, root olean of main 3b8c687)
import RBM3D
import RBM3D.Green.FlucIter
#assert_rbm_axioms
axiom audit: 2922 theorems, 1132 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
All within [propext,
 Classical.choice,
exit 0
```
The pre-check loads the root olean (which already contains main's T2083/T2084/T2088 modules: 2922 theorems vs 2849
in the prover's run) together with the new module without a duplicate-declaration error, so there is no full-name
clash with current main. Frozen signatures: untouched (one new file only).

## 2. Statements against RBM2D `c9a24cf` (ST1-COMMON item 6), independent token-level diff
My own script (S/tokdiff.py): RBM3D lines 60–798 with R1/R2 undone (`{d : ℕ} {sz : Sizes d}`→`{d : Sizes}`,
`(sz : Sizes d)`→`(d : Sizes)`, `Idx d (sz.L n) (sz.W n)`→`Idx (d.L n) (d.W n)`, `sz`→`d`, `zt`→`spectralZ`,
`mE`→`spectralM`), whitespace-tokenized (so line wraps vanish), against `c9a24cf:84–818`, `difflib` opcodes:
```
$ git -C ../RBM2D --no-optional-locks show c9a24cf:RBM2D/Green/FlucIter.lean > S/c9.txt; wc -l < S/c9.txt
    1877
$ python3 S/tokdiff.py RBM3D/Green/FlucIter.lean S/c9.txt
insert 2D: DecidablePred p => @condPred d p || 3D: DecidablePred p => @condPred d d p
token diffs: 1 tokens 2D 6797 3D 6798
```
The single difference is the explicit implicit argument `@condPred d sz p` inside the proof of `condPred_congr`
(file line 212), not in any statement. Hence every one of the 71 declarations (statements, definitions, proofs)
equals RBM2D's after R1–R4; no hypothesis added or dropped, quantifier order unchanged. The dimension enters only
through `Sizes d` and `Idx d …`; no `3 ≤ d` is assumed and none is needed (dimension-free statements):
```
$ sed -n 60,798p RBM3D/Green/FlucIter.lean | grep -nE "Sizes 3|3 ≤ d|variable"
7:variable {d : ℕ} {sz : Sizes d} {n : ℕ}
424:variable {ι : Type*} [Fintype ι] [DecidableEq ι]
539:variable {ι : Type*}
548:variable [DecidableEq ι]
604:variable {ι : Type*} [Fintype ι] [DecidableEq ι]
683:variable {E t : ℝ}
```
`d = 2` tokens (portmap row 38: `W⁻²/L⁻²:5 d=2:2 Z2/zdist2:3`), whole RBM2D file:
```
$ grep -nE "Z2|zdist|W ?\^ ?2|L ?\^ ?2|W⁻²|L⁻²|d = 2|d=2|two-dim|\(W \* L\)" S/c9.txt | cut -c1-60
14:`integral_norm_flucAvg_pow_le_iter_budget` and what they n      21:`Idx (d.L n) (d.W n) = Z2 (W L)`, with ...
55:## d = 2     58:the d = 2 model are the merged G4.1 ...     60:`c = W⁻²`, `#A = W²`), in place of ...
1642:/-- Check 4 (... `W⁻² 1(k ∈ 𝓘_a)`) ...   1650: ... Z2 (flucIterCheckSizes.L 0))   1654: ... Z2 (...)
```
All in the module docstring (`:1–83`, not ported) or in S1-21 (`:1642ff`); none in `:84–818`. Accounted for.

Cut: `c9a24cf` `section Slice1 :88` … `end Slice1 :818`; the ticket's `:800` lies in `applyOps_conj` (`:798–807`),
so the cut at the section end `:818` (adding `applyOps_epsHom :810–816`) is the nearest section boundary, as the
ticket permits. Both declaration lists (71 / 33) are in the prove report (a)(i) and (b). DECISIONS §30:
`UniformWeight` first occurs at `c9a24cf:967` (S1-21); Part 1 has no weight hypothesis.

Merged reuse (ticket): `condRow`, `IsRowCoord`, `rowSplit`, `RowIntegrable`, `FinDepOffRow`, `FinDep`, `epsHom`,
`greenDiagCentered`, `flucDiag` are not redefined (none among the 71 names); `condRow_eq_condPred` is stated for
the merged `condRow` at file line 203:
```
theorem condRow_eq_condPred (sz : Sizes d) (n : ℕ) (k : Idx d (sz.L n) (sz.W n))
    (X : Sizes.SeqΩ sz → ℂ) :
    condRow sz n k X = condPred sz (IsRowCoord sz n k) X := rfl
```

## 3. Hidden hypotheses, vacuity, cycles
New definitions (file lines 77–666), read in full: `predSplit` (coordinatewise `if p c then ω' c else ω c`),
`condPred` (`∫ ω', X (predSplit sz p ω ω')`), `qRow` (`X ω - condRow sz n k X ω`), `applyOps` (structural
recursion on the word), `numQ` (`countP (·.1)`), `pivotFam`, `pivotWords`, and the `Prop`s
```
structure BddMeas (sz : Sizes d) (X : Sizes.SeqΩ sz → ℂ) : Prop where
  meas : Measurable X
  bdd : ∃ C : ℝ, ∀ ω, ‖X ω‖ ≤ C
def OpsOk ... := (l.map Prod.snd).Nodup ∧ ∀ x ∈ l, x.2 ≠ k i
def OpsOkOut ... := (l.map Prod.snd).Nodup ∧ ∀ x ∈ l, (∃ j, j ∉ R ∧ x.2 = k j) ∧ x.2 ≠ k i
```
These are the RBM2D definitions (token diff above), carry no estimate or paper result, and are concluded by
theorems of the file (`bddMeas_greenDiagCentered`, `BddMeas.condRow`, `OpsOkOut.cons`, `OpsOkOut.opsOk`), so they
are not owed hypotheses; the registry pre-check passes with `Test/Axioms.lean` unchanged. Hypotheses of the
endpoints are deterministic (`|E| < 2`, `t < 1`, `BddMeas`, `FinDep`, `h0 : condRow … (F i₀) = 0`,
`hS : S ⊆ univ.erase i₀`, `hlone`), no external hypothesis. Dependencies: only merged files
(`import RBM3D.Green.LDE`, line 6); no cycle (a new leaf module).

## 4. Compiled nonempty instances (file lines 799–1083, namespace `FlucIterInst`, compiled in §1)
Data: `szT : Sizes 3` with `L = 3`, `W = 2`, `lam = 1/2`, slice `n = 0` (216 sites), three distinct sites
`site = ![(0,0,0),(0,0,1),(2,0,0)]` (`site_inj` by `decide`), `E = 0`, `t = 0` (`hE0`, `ht0` by `norm_num`),
`u = 1/2`; `G i = greenDiagCentered …`, `Z i = flucDiag …`; nonempty words `w1 = [(true, site 1), (false, site 2)]`,
`l2 = [(true, site 2)]`; `ι = Fin 3`, `S12 = {1, 2}`. Endpoints checked by reading the examples:
```
prod_eq_sum_pivotFam         : example (ω) : ∏ i, Z i ω = ∑ S ∈ (univ.erase 0).powerset, ∏ i, pivotFam szT 0 (site 0) 0 S Z i ω
integral_prod_pivotFam_empty : hF := bZ, hFd := fZ, h0 := condRow_qRow (bG 0) (site 0)  (all discharged)
pivotFam_eq_applyOps         : at Lw = ![[], l2, []], S12
sum_numQ_pivotWords          : hS by decide, Lw, S12 (card 2)
OpsOkOut.cons                : hlone from site_inj, 0 ∈ {0}, 1 ≠ 0 by decide, l2_ok (proved), nonempty word
norm_applyOps_le             : w1, hX := norm_greenDiagCentered_le_env hE0 ht0 (1/2) (site 0)
norm_condRow_le, flucDiag_eq_qRow, condRow_conj, qRow_conj, applyOps_conj, applyOps_epsHom (i : Fin 2 ⊕ Fin 2)
bddMeas_greenDiagCentered/_flucDiag : named theorems ..._szT (i : Fin 3), hE0 ht0
finDep_* , BddMeas.*, predSplit lemmas, condPred lemmas, condRow_condRow_comm, condRow_applyOps_qRow: one example each
```
No `N = 0`, no empty index, no `False` premise, no large witness; every hypothesis is discharged by a lemma,
`decide` or `norm_num`. Prover's coverage script (each of the 71 names occurs in the block, min count 1) agrees
with my reading. PASS.

## 5. Paper deltas
Part 1 contains no statement of the paper (infrastructure for `(GavLGEX)`, `3_5:33`, a `[YY_25]` input) and no
statement differs from RBM2D beyond renaming; no Lean/paper statement difference arises, so no candidate is owed.
The prove report proposes none; consistent.

## 6. Observations (no effect on verdict)
- O1. Ticket text: "1540 lines at `c9a24cf`" — the file has 1877 lines there (portmap row 38: 1877 raw / 1540
  code). The prove report flags this to the dispatcher.
- O2. Three public instance theorems `FlucIterInst.{bddMeas_greenDiagCentered_szT, bddMeas_flucDiag_szT,
  finDep_greenDiagCentered_szT}` are in a namespace with the file stem; acceptable under CLAUDE.md §3 (E).
- O3. Upstream lint warnings appear when the module is rebuilt (LDEQuad, FlucVanish); none from this file.

## Verdict
| Target group | Statement | Hidden hyp./vacuity/cycle | Instance | Build/axioms | Deltas | Verdict |
|---|---|---|---|---|---|---|
| `Slice1` core (`predSplit`, `BddMeas`, `condPred`, `condRow_eq_condPred`, `qRow`, `applyOps`, `finDep_*`) | = RBM2D | none | yes | ok | none needed | PASS |
| `Pivot` (`pivotFam`, `prod_eq_sum_pivotFam`, `integral_prod_pivotFam_empty`) | = RBM2D | none | yes | ok | none needed | PASS |
| `Words`/`Iterate` (`OpsOk`, `OpsOkOut(.cons)`, `pivotWords`, `pivotFam_eq_applyOps`, `sum_numQ_pivotWords`) | = RBM2D | none | yes | ok | none needed | PASS |
| bounds, `Env`, conjugation (`norm_condRow_le`, `norm_applyOps_le`, `flucDiag_eq_qRow`, `bddMeas_*`, `*_conj`, `applyOps_epsHom`) | = RBM2D | none | yes | ok | none needed | PASS |

**T2089: PASS.** No dispatcher sign-off needed.
