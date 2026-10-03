Auditor model: claude-opus-5-5

# T2014 audit (round 1) — KL2 cut of a tree at an internal edge, cut bijection

Written Sat Oct  3 03:19:13 UTC 2026 (`date -u`). Branch `t/T2014` = `b470e51`, main = `33049c0`.
Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2014-audit1` (detached at `b470e51`).
`SP=/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/d787b0e7-ec73-431d-9968-a805c3e11390/scratchpad`, `W=` the audit worktree.
Targets (ticket + Amend 1): `KLtreeValW_cut`, `KLsum_cut`, `KLgval`, `KLgval_congr`, `KLgval_split`, `KLtreeValW_eq_gval`,
`KLFIn_mem_TSP`, `KLFOut_mem_TSP`, `KLglueF_mem_TSP`, `KLglueF_cut`, `KLFIn_glueF`, `KLFOut_glueF` and the objects their statements mention.

## 1. Scope, hygiene, build, axioms
```
$ git diff --name-status main...t/T2014
A	RBM3D/Loop/KLCut.lean
$ grep -nE '\bsorry\b|\badmit\b|native_decide|^\s*axiom\b|@\[implemented_by|@\[extern|unsafe' RBM3D/Loop/KLCut.lean; echo "grep exit $?"
grep exit 1
$ grep -nE '^\s*(structure|class)\b' RBM3D/Loop/KLCut.lean      # no structure/class => no hypothesis hidden in a field
(no output)
$ cd $W && (time lake build RBM3D.Loop.KLCut) 2>&1 | grep -E 'error|warning|Built RBM3D.Loop.KLCut|Build completed|total'
✔ [3237/3237] Built RBM3D.Loop.KLCut (10s)
Build completed successfully (3237 jobs).
lake build RBM3D.Loop.KLCut  19.90s user 5.09s system 174% cpu 14.356 total
$ lake env lean $SP/aud_ax.lean      # #print axioms of targets and pinned instances
'RBM.Loop.KLtreeValW_cut' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Loop.KLsum_cut' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Loop.KLgval_congr' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Loop.KLgval_split' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Loop.KLtreeValW_eq_gval' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Loop.KLFIn_mem_TSP' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Loop.KLFOut_mem_TSP' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Loop.KLglueF_mem_TSP' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Loop.KLglueF_cut' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Loop.KLFIn_glueF' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Loop.KLFOut_glueF' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Loop.KLCutInst_sum_cut' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Loop.KLCutInst_sum_cut_count' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Loop.KLCutInst_treeValW_cut' depends on axioms: [propext, Classical.choice, Quot.sound]
$ lake env lean $SP/aud_ax2.lean     # Lean.collectAxioms over every non-internal constant of the module
KLCut: 119 non-internal constants (81 theorems); constants using an axiom outside [propext, Classical.choice, Quot.sound]: []
```
The full `lake build` (root `#assert_rbm_axioms`) is run by the hub at merge; `RBM3D.lean` is untouched on the branch.

## 2. Statements against the pin (RBM2D `TreeRep.lean` 415-1667 at `c9a24cf`, renamed by the ticket's map)
Script `$SP/aud_diff.py` (auditor's own): split both files into declarations; RBM2D text renamed
`x -> KLx` whenever `KLx` is declared in KLTree.lean/KLCut.lean, `Z2 L -> Zd d L`, `(L : ℕ) -> (d L : ℕ)`, `KLfoo L -> KLfoo d L`;
comments removed, whitespace collapsed; compare each header up to the first top-level `:=`.
```
$ python3 $SP/aud_diff.py $SP $W
RBM2D decls in 415-1667: 90  RBM3D KLCut decls: 121
headers identical after renaming: 88
treeValW_empty : MISSING
hasDerivAt_treeValW : HEADER DIFF
  2D: ... + ∑ d : ↥F, KLtreeValW d L F a (M t) (Function.update (E t) d (E' d))) t
  3D: ... + ∑ e : ↥F, KLtreeValW d L F a (M t) (Function.update (E t) e (E' e))) t
$ awk 'NR>=415 && NR<=1667 && /^ *(variable|section|end |include|omit)/' tr2d.lean   vs   grep the same in KLCut.lean
(identical sequence of 60 context lines, except `variable (L : ℕ)` -> `variable (d L : ℕ)` and `variable {L}` -> `variable {d L}`;
 hypothesis blocks e.g. `variable {F} (hF : KLIsTSP F) (hn : 2 ≤ n) (hJ : J ∈ F)`, `variable (hJd : IsDiag n J.1 J.2)` unchanged)
```
- `treeValW_empty` is the merged `KLtreeValW_empty` (KLTree.lean:161), same statement after renaming (Amend 1: do not duplicate).
- `hasDerivAt_treeValW`: bound variable `d -> e` only (here `d` is the dimension); alpha-equivalent.
- All targets, including `KLtreeValW_cut` and `KLsum_cut`, are header-identical to RBM2D after the renaming.
Elaborated signatures (no hypothesis beyond RBM2D's; `KLIsTSP` is a plain `def`, discharged from `F ∈ TSP n` by `KLisTSP_of_mem_TSP`):
```
RBM.Loop.KLtreeValW_cut : ∀ (d L : ℕ) [inst : NeZero L] {n : ℕ} [inst_1 : NeZero n] {F : Finset (Fin n × Fin n)}
  (hF : RBM.Loop.KLIsTSP F) (hn : 2 ≤ n) {J : Fin n × Fin n} (hJ : J ∈ F) (a : Fin n → RBM.Zd d L)
  (M : Fin n → Matrix (RBM.Zd d L) (RBM.Zd d L) ℂ) (E : ↥F → Matrix (RBM.Zd d L) (RBM.Zd d L) ℂ)
  (P S Q : Matrix (RBM.Zd d L) (RBM.Zd d L) ℂ),
  RBM.Loop.KLtreeValW d L F a M (Function.update E ⟨J, hJ⟩ (P * S * Q)) =
    ∑ u, ∑ w, RBM.Loop.KLgval d L (fun o => o.elim u fun v => a ↑v) (fun o => o.elim P.transpose fun v => M ↑v)
              (fun o => o.elim (RBM.Loop.KLcutIn hJ) (RBM.Loop.KLinLeafPar hF hJ)) (fun d => E ↑d) RBM.Loop.KLinChild
              (RBM.Loop.KLinPar hF hn hJ) * S u w *
          RBM.Loop.KLgval d L (fun o => o.elim w fun v => a ↑v) (fun o => o.elim Q fun v => M ↑v)
            (fun o => o.elim (RBM.Loop.KLcutOut hF hn hJ) (RBM.Loop.KLoutLeafPar hF hJ)) (fun d => E ↑d)
            RBM.Loop.KLoutChild (RBM.Loop.KLoutPar hF hn)
@RBM.Loop.KLsum_cut : ∀ {n : ℕ} [NeZero n] {J : Fin n × Fin n}, RBM.Loop.IsDiag n J.1 J.2 → 2 ≤ n →
  ∀ (f : Finset (Fin (n - KLwIn J + 1) × Fin (n - KLwIn J + 1)) → Finset (Fin (KLwIn J + 1) × Fin (KLwIn J + 1)) → ℂ),
    ∑ F ∈ TSP n with J ∈ F, f (KLFOut F J) (KLFIn F J) = ∑ G ∈ TSP (n - KLwIn J + 1), ∑ H ∈ TSP (KLwIn J + 1), f G H
$ #print RBM.Loop.KLIsTSP
def RBM.Loop.KLIsTSP : {n : ℕ} → Finset (Fin n × Fin n) → Prop :=
fun {n} F => (∀ d ∈ F, RBM.Loop.IsDiag n d.1 d.2) ∧ RBM.Loop.CrossingFree F
```
Against the ticket mathematics: cut edge carries `P S Q`; inside polygon `KLwIn J + 1` vertices with root leaf `(u, Pᵀ)`;
outside polygon `n - KLwIn J + 1` vertices with glue leaf `(w, Q)`; `∑_{u,w} … S u w …`; bijection `F ↦ (F_out, F_in)` with inverse `glueF`. Matches.
Dimension: the only hypotheses on `d, L` are `(d L : ℕ) [NeZero L]`; no `d`-specific fact enters (combinatorics + one algebraic splitting identity).

## 3. Vacuity, hidden hypotheses, cycles
- No `structure`/`class` in the file; no new hypothesis `Prop`. Hypotheses `hF`, `hn`, `hJ`, `hJd` are RBM2D's, all decidable at concrete data (see §4).
- Imports: `Mathlib.Analysis.Calculus.Deriv.Mul`, `RBM3D.Loop.KLTree` (merged, KL1). No dependency on unmerged work; no cycle.
- Privacy/visibility: 92 public names, whole-word `git grep` on main:
```
$ for n in <92 public names of KLCut.lean>; do git grep -wc "$n" main -- RBM3D RBM3D.lean; done
public names with a whole-word hit on main: 0
```

## 4. Compiled nonempty instances (section `Instances`, KLCut.lean:1332-1646; compiled in the build of §1)
- `KLCutInst_sum_cut` (ticket pin): `KLsum_cut (n := 5) (J := (1,3)) (by decide) (by norm_num) (fun _ _ => 1)`.
  `IsDiag 5 1 3` and `2 ≤ 5` discharged; nondegenerate: `KLCutInst_sum_cut_count` proves by `decide`
  `#{F ∈ T_SP(5) : (1,3) ∈ F} = 3 ∧ |T_SP(4)|·|T_SP(3)| = 3`, and `KLCutInst_sum_cut_card` derives the count equality from `KLsum_cut`.
- `KLCutInst_treeValW_cut` (Amend 1 pin): `n = 4`, `F = {(0,2)}`, `J = (0,2)`, `d = L = 3`;
  `hF := KLisTSP_of_mem_TSP KLCutInst_F4_mem` (`{(0,2)} ∈ TSP 4` by `decide`), `hn` by `norm_num`, `hJ` by `decide`;
  concrete matrices `thetaEdge 3 3 (1/2) (mSigma 0) (9/10) …`, `S = SB 3 3 (1/2)`. No external hypothesis, no other gate's pin.
- Other targets, each applied at concrete data with every hypothesis discharged: `KLFIn_mem_TSP`, `KLFOut_mem_TSP`,
  `KLglueF_cut` at `F = {(0,3),(1,3)} ∈ TSP 5`, `J = (1,3)`; `KLglueF_mem_TSP`, `KLFIn_glueF`, `KLFOut_glueF` at
  `G = {(0,2)} ∈ TSP 4`, `H = ∅ ∈ TSP 3`; `KLtreeValW_eq_gval`, `KLgval_congr` (leaf swap `0 ↔ 1`) on `F = {(0,2)}`;
  `KLgval_split` on two 2-node trees; `KLgval_in_eq`, `KLgval_out_eq`, `KLhasDerivAt_treeValW` on the square.
  None uses `N = 0`, an empty index type, or a `False` premise.

## 5. Paper deltas
The file is a statement-preserving port of RBM2D tree/laminar combinatorics and of an algebraic splitting identity (§2: 88/90
header-identical, 1 alpha-variant, 1 merged elsewhere). It restates no theorem of arXiv:2507.20274 with a different hypothesis.
No Lean/paper statement difference; no paper-delta candidate needed (prove report (d): `T2014a` unused). Coverage: complete.

## 6. Observations (no effect on statement, instance, build, axioms or paper-delta coverage)
- O1 (visibility, prove report D1): 22 RBM2D helpers that no target statement mentions are public with prefix `KL`
  (`KLprod_update_eq`, `KLhasDerivAt_treeValW`, `KLgval_in_eq`, `KLgval_out_eq`, `KLOutEnds`, `KLshiftIn_val`, …), whereas
  ticket item 2 says such helpers "stay `private`". The change is visibility only: statements are RBM2D's (§2), names are
  `KL`-prefixed (CLAUDE.md §3 (E) satisfied) and clash-free (§3). The dispatcher may note it for KL3/KL7/KL11 (which can then
  use them instead of re-porting). Not a RETURN.
- O2: RBM2D `abbrev`s `NIn NOut LIn LOut EIn EOut` stay `abbrev` (reducibility unchanged); `private` dropped as the ticket asks.
- O3: the ticket's phrase "the cut part of `Assembly`" — at `c9a24cf`, `sum_cut` (:1643) lies in `section CutBij` (1265-1667);
  the ported range 415-1667 contains everything the ticket and Amend 1 name (prove report (d)).

## Verdict
| Target | Statement | Vacuity/hidden/cycle | Instance | Build/axioms | Deltas | Verdict |
|---|---|---|---|---|---|---|
| `KLtreeValW_cut` | = RBM2D renamed | none | n=4, F={(0,2)} | ok | none needed | PASS |
| `KLsum_cut` | = RBM2D renamed | none | n=5, J=(1,3), count 3 | ok | none needed | PASS |
| `KLgval`, `KLgval_congr`, `KLgval_split`, `KLtreeValW_eq_gval` | = RBM2D renamed | none | yes | ok | none needed | PASS |
| `KLFIn_mem_TSP`, `KLFOut_mem_TSP`, `KLglueF_mem_TSP`, `KLglueF_cut`, `KLFIn_glueF`, `KLFOut_glueF` | = RBM2D renamed | none | yes | ok | none needed | PASS |
| objects `KLwIn KLFIn KLFOut KLglueF KLinV KLoutV KLglueV KLLIn KLLOut KLEIn KLEOut KLinChild KLoutChild KLcutIn …` | = RBM2D renamed | — | — | ok | — | PASS |

Overall: **PASS**. No dispatcher sign-off required (O1 is visibility only).
