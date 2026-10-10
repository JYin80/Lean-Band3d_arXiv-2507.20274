Auditor model: claude-opus-5-5
# T2376 (BA-K06, `BA/KMolecule.lean` + `BA/KCactusCut.lean`, Amend 1) — stage 2 audit, round 1, Sat Oct 10 10:19:57 UTC 2026

Inputs: ticket `docs/tickets/T2376.md`, `T2376-amend-1.md`; 1a pins = `docs/reports/T2376-prove.md` §(a)(i) table (audited in
`T2376-1a-audit.md`: statements PASS); branch `t/T2376` = 3fa3746 (base 9d5d47d); audit worktree
`/Users/junyin/Lean_proof/RBM3D-wt/T2376-audit1` (detached at 3fa3746). Scratch: `scratchpad/T2376/audit2/`.

## 1. Diff scope, size, hygiene
```
$ git diff --name-status main...HEAD
A	RBM3D/BA/KCactusCut.lean
A	RBM3D/BA/KMolecule.lean
$ git diff main...t/T2376 --stat -- RBM3D.lean lakefile.lean lean-toolchain lake-manifest.json   # (empty)
$ wc -l RBM3D/BA/KCactusCut.lean RBM3D/BA/KMolecule.lean
    1288 RBM3D/BA/KCactusCut.lean
     449 RBM3D/BA/KMolecule.lean
    1737 total                                  (Amend 1 stop line 2000, combined)
$ per commit (git show <c>:<file> | wc -l):
9938bd8 KCactusCut=1194 KMolecule=0   sum=1194 | 45fe7da 1194/155 sum=1349 | d6d30df 1194/263 sum=1457
5252f53 1194/378 sum=1572 | 040d455 1287/454 sum=1741 | ab616f0 1288/445 sum=1733 | 3fa3746 1288/449 sum=1737
$ grep -n '^import' (both files)
KMolecule.lean:6:import RBM3D.BA.KCactusCut   :7 RBM3D.BA.KTreeRep   :8 RBM3D.Loop.KLSumZeroWard   :9 RBM3D.Loop.KLIndStepB
KCactusCut.lean:6:import RBM3D.BA.KCactus     :7 RBM3D.Loop.KLCut    :8 RBM3D.Loop.KLSumZeroWard
$ grep -nE '\bsorry\b|\badmit\b|native_decide|^\s*axiom\b|set_option|implemented_by|extern|unsafe' (both files)
KMolecule.lean:42:set_option linter.style.longLine false
KCactusCut.lean:29:set_option linter.style.longLine false
KCactusCut.lean:1105:set_option synthInstance.maxSize 512 in
$ private decls: KCactusCut 78, KMolecule 11; private without stem KCactusCut_/KMolecule_: KMolecule.lean:412 `Sig0` (private: OK, §3(E))
$ name clash on main 1f710ee (git grep -nw, 17 public names + KMoleculeInst/KCactusCutInst; stems by plain grep): 0 hits each
```
Two-file split (Amend 1): `baCactus_cut` is public in `KCactusCut.lean:1111`, `KMolecule.lean:6` imports it. Restated plan: report
§(b1) (before the first commit 9938bd8, 09:44:29 UTC), copy counted at 790 + 208 code lines with the dropped K05b lemmas listed. Met.

## 2. Build and axioms (audit worktree)
```
$ lake build RBM3D.BA.KCactusCut RBM3D.BA.KMolecule; echo exit=$?    (oleans absent from the copied cache: built fresh)
exit=0   errors: 0   (warnings only from upstream modules; none from the two new files)
✔ [3751/3752] Built RBM3D.BA.KCactusCut (5.6s)
✔ [3752/3752] Built RBM3D.BA.KMolecule (3.4s)
Build completed successfully (3752 jobs).
$ lake env lean audit2/ax.lean   (#print axioms of the 17 public declarations); exit=0
  13 [propext, Classical.choice, Quot.sound]   (baCactus_cut, baCactus_leafW_in/out, BAKpi, BASigmaTree, BASigmaPi, BASig,
                                                baKpi_eq_sum_SigmaPi, baK_eq_sum_Kpi, baSigmaPi_shift/reflect, baSig_transl, baSigmaPi_cut)
   4 [propext, Quot.sound]                     (BAinVinv, BAoutVinv, BAdeltaIn, BAdeltaOut)
$ lake env lean docs/tickets/checks/T2376-check.lean; echo exit=$?
exit=0  (0 error lines)
$ registry pre-check (uncommitted scratch: import RBM3D; import RBM3D.BA.KCactusCut; import RBM3D.BA.KMolecule; #assert_rbm_axioms)
pre_exit=0
axiom audit: 11000 theorems, 3221 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
$ same without the two imports: pre0_exit=0, "axiom audit: 10986 theorems, 3213 definitions, 0 axioms ..."
$ diff <(tail -n +2 pre0.out) <(tail -n +2 pre.out); echo $?
0                (premise ledgers identical: no unregistered premise, no registry edit needed)
```
(The theorem counts differ from the prove report's 10951/10937 because the copied cache holds main's newer `RBM3D.olean`; no effect.)

## 3. Statements against the 1a pins (prove report :9-17) and the ticket
Lean heads extracted by `sed`/`grep -n` from the branch files (full text in report §(b2) :164-201, re-read here):
| target | Lean (file:line) | pin / ticket check | result |
|---|---|---|---|
| `BAKpi d L n M t σ a π` | KMolecule:53 `∑ F ∈ KLTSPlong n σ π, BAGamma d L n M t F σ a` | `(eq:defKpi)`; rfl-checked (iface.lean (3)) | PASS |
| `BASigmaTree`, `BASigmaPi` | :60 `KLgval δ (fun _ => 1) (BAslotLeaf F) (BACactusValEdgeW M t F σ) Src Tgt`; :67 layer sum | = `BAGamma` (rfl, iface (3)) with leaf weights `1` ⇒ indicator of `δ_v`; `n` implicit in `BASigmaTree` | PASS |
| `baK_eq_sum_Kpi` | :133 `0<κ, 0<g, 3≤L, BAReal d L g κ E m, t∈Ico 0 1, 3≤n ⊢ BAKsol … = ((W^d)⁻¹)^(n-1) * Σ_{π∈(diagonals n).powerset} BAKpi …` | `BATreeRep` (KTreeRep:48) hypotheses at `Λ:=g`; `(eq_K-Kpi)` | PASS |
| `baKpi_eq_sum_SigmaPi` | :110 no hypothesis; `= Σ_δ BASigmaPi … π δ * ∏ v, BAThetaOf M t (σ v) (σ (v+1)) (a v) (δ v)` | 1a :12 | PASS |
| `baSigmaPi_cut` | :313 `2≤n, F₀∈TSP n, KLFlong F₀ σ=π, J∈π, ∀e∈π, KLArcLe e J→e=J ⊢ ∀δ, Σ^π δ = Σ_{u,w} BASigmaPi (KLwIn J+1) (sigmaIn σ J) ∅ (BAdeltaIn J δ u) * ((t:ℂ) * BAThetaOf M t (σ J.1) (σ J.2) u w) * BASigmaPi (n-KLwIn J+1) (sigmaOut σ J) ((π.erase J).image (KLshiftOut J)) (BAdeltaOut J δ w)` | 1a :15 verbatim (inner `u` = row index); no `W`, no `M`/`t` hypothesis (C2: no symmetry used) | PASS |
| `BAdeltaIn/Out` | KCactusCut:54/59 `Function.update (f ∘ BAinVinv J) (Fin.last _) x` / `update (f ∘ BAoutVinv J) (KLglueV J) x` | 1a :13 at `α = Zd d L`; polymorphic `α` is a generalisation of a definition | PASS |
| `baCactus_cut` (public, Amend 1) | KCactusCut:1111 `KLIsTSP F, 2≤n, J∈F`, any `M t σ a Lw P S Q` | 1a :14 verbatim | PASS |
| `baCactus_leafW_in/out` (public helpers, Amend 1) | :1204/:1232 `J.1+2≤J.2 ⊢ BAdeltaIn J (BACactusValLeafW M t σ) (Θ^{σ_iσ_j})ᵀ = BACactusValLeafW M t (sigmaIn σ J)` / out with `Θ^{σ_iσ_j}` | not in the 1a table; Amend 1 allows "public helper lemmas that K06 and K10 need"; any `M` | PASS |
| `baSigmaPi_shift/reflect` | :204/:224 explicit `hshift` (reflect also `hsymm`), every `σ`, `π` | 1a :16 | PASS |
| `BASig`, `baSig_transl` | :74 `BASigmaPi d (L i) n (BAMsigma d (L i) (BAMB d (L i) (g i) (E i) (m i))) (t i) σ ∅ δ`; :244 the first two conjuncts at alternating `σ`, no other hypothesis | 1a :17; ticket "at alternating σ"; type and conjuncts checked below | PASS |

Type/interface checks (general `ι, d, n, L, g, E, m, t`, not only at the instance):
```
$ lake env lean audit2/iface.lean; echo iface_exit=$?
  (1) example (h : SigSumZeroAbs d n L g t (BASig d n L g E m t)) : SigSumZeroAbs … := ⟨(baSig_transl …).1, (baSig_transl …).2, h.2.2⟩
  (2) example … (TH : ∀ i, Bool → Bool → Matrix (Zd d (L i)) (Zd d (L i)) ℂ) : Prop := IndStepAbs d n L Bp (BASig d n L g E m t) TH
  (3) BAKpi … = ∑ F ∈ KLTSPlong n σ π, BAGamma … := rfl ;  BAGamma … = KLgval … (BACactusValLeafW M t σ) … := rfl
  (4) example : diagonals 4 = {(0,2), (1,3)} := by decide ;  #eval (diagonals 5).card
5
iface_exit=0
```
So `BASig` has the `Sig` type of `SigSumZeroAbs` (KLIndStepA:1036) and `IndStepAbs` (KLIndStepB:77), and `baSig_transl` is exactly
their first two conjuncts. `diagonals n` = `Z_n^off` at n = 4, 5 (|Z_5^off| = 5).

## 4. Hidden hypotheses, vacuity, cycles
- No structure or class carries a hypothesis: the only new definitions are `def`s of values (`BAKpi`, `BASigmaTree`, `BASigmaPi`,
  `BASig`, `BAinVinv`, `BAoutVinv`, `BAdeltaIn/Out`); all hypotheses are explicit binders.
- `baK_eq_sum_Kpi` rests on merged `baTreeRep d : BATreeRep d (@BAGamma d)` (KTreeRep:1709, unconditional theorem, K05b ab54184).
- No external hypothesis is introduced (the `SigSumZeroAbs` bound clause stays K07/K08's pin, only as a hypothesis of an `example`).
- Imports are merged modules only; no cycle (KMolecule → KCactusCut → KCactus/KLCut/KLSumZeroWard).

## 5. Compiled nonempty instances (all in the same files, built in §2)
Data: flow point `P` of `(d,L)=(3,4)` (`MFixedPoint.lean:893`), `M0 = BAMsigma 3 4 (BAMB 3 4 P.g0 P.E P.m0)`, `t = 1/2`, `n = 4`,
labels `a = ((0,0,0),(1,0,0),(2,0,0),(3,0,0))` (distinct), `W = 2`.
| endpoint | file:line | data / hypotheses discharged | result |
|---|---|---|---|
| `baK_eq_sum_Kpi` | KMolecule:382 | `P.real.1.1 : 0<κ`, `P.g0_pos`, `3≤4`, `P.real`, `1/2∈[0,1)`, `3≤4`, `σ=(+,+,-,+)` | PASS |
| `baKpi_eq_sum_SigmaPi` | :387 | `π = {(0,2)}`, `M0`, `σ=(+,+,-,+)` | PASS |
| `baSigmaPi_cut` | :393 | `J=(0,2)`, `F₀={(0,2)} ∈ TSP 4` (`TSP_four`), `KLFlong F₀ σ = {(0,2)}` by `decide` (σ₀=+ ≠ σ₂=-: mixed charges, long chord), innermost by `mem_singleton` | PASS |
| `baSigmaPi_shift`, `_reflect` | :401, :406 | `hshift` = merged `BAMsigma_shift`, `hsymm` = `KMolecule_BAMsigma_symm` (from merged `BAMB_symm`), `c=(1,0,0)` | PASS |
| `baSig_transl` (.1, .2) | :416, :422 | `ι = Unit`, alternating `σ=(+,-,+,-)` by `decide`, `c=(1,0,0)` | PASS |
| interface `SigSumZeroAbs` / `IndStepAbs` | :429, :444 | bound clause (K07/K08 pin) as hypothesis only; `IndStepAbs … Sig0 Θ` elaborates | PASS |
| `baCactus_cut` | KCactusCut:1270 | `F={(0,2)}`, `KLIsTSP` from `TSP_four`, `2≤4`, `Lw = Θ`-leaves, `P = Q = Θ^{(+,-)}`, `S = 1` | PASS |
| `baCactus_leafW_in/out` | :1280, :1283 | `J=(0,2)`, `0+2≤2` | PASS |
No `N = 0`, empty index, collapsed window, `False` premise or large witness: L = 4, n = 4, both cut polygons are triangles (n ≥ 4 is
the least size with a diagonal). Nonzero values at this data: preflight `inst.py` (report :36-42, both sides of every identity nonzero).

## 6. Paper deltas (paper `A_deterministic_estimates.tex:600-640` read)
| Lean/paper difference | candidate |
|---|---|
| chord `tΘ^{(σ_i,σ_j)}` (both orientations) vs paper `tS^{(B)}Θ_t^{(+,-)}` in `(eq:molecule-Kpi)` | `T2376a` (report :257) |
| BA `K^{(π)}`, `Σ^{(π)}` carry no `∏ m(σ_i)`, no `W`; `W^{-d(n-1)}` only in `baK_eq_sum_Kpi` | `T2376b` (:258) |
| recursive one-edge factorisation `baSigmaPi_cut` vs product over `r` molecules with `r-1` chords; `BASigmaPi … π`, `π ≠ ∅`, has no paper counterpart; paper's per-molecule `Σ^{(π)}` = Lean `BASigmaPi σ^{(k)} ∅` | `T2376c` (:259; 1a-audit item 3, Amend 1) |
Index shift `1..n` → `Fin n` is the project convention (no delta). Coverage: complete.

## 7. Observations (no verdict effect)
- `baSig_transl` carries the alternation hypothesis (as `SigSumZeroAbs`); the 1a row :17 said "no hypothesis". The Lean form is the
  ticket's ("at alternating σ") and the general-`σ` facts are `baSigmaPi_shift/reflect`. Not a weakening of a target.
- `BAdeltaIn/Out` are polymorphic in the codomain (report item 6 (i)); at `α = Zd d L` they are the 1a definition.
- `set_option synthInstance.maxSize 512 in` at `baCactus_cut` (KCactusCut:1105): elaboration setting, no logical effect.
- The K10 fit of `baCactus_leafW_in/out` is shown only by an uncommitted scratch file (`k10check.lean`); K10 will check it.
- Prove report registry counts (10951/10937) differ from this run's (11000/10986): different `RBM3D.olean` in cache; ledgers identical in both.

## Verdict
| target | verdict |
|---|---|
| `BAKpi`, `BASigmaTree`, `BASigmaPi`, `BASig` | PASS |
| `baK_eq_sum_Kpi` | PASS |
| `baKpi_eq_sum_SigmaPi` | PASS |
| `baSigmaPi_cut` (factorisation at an innermost long edge) | PASS |
| `baSigmaPi_shift`, `baSigmaPi_reflect`, `baSig_transl` (first two conjuncts of `SigSumZeroAbs`) | PASS |
| `baCactus_cut`, `baCactus_leafW_in/out`, `BAinVinv/BAoutVinv/BAdeltaIn/BAdeltaOut` (Amend 1, `KCactusCut.lean`) | PASS |
| instances, build, axioms, registry pre-check, diff scope, stop line 1737 ≤ 2000 | PASS |
**Overall: PASS.** No dispatcher sign-off needed.
