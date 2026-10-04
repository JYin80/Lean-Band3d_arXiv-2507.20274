Prover model: claude-sonnet-5-5

## (a) Math preflight — Sat Oct  3 23:04:09 UTC 2026

Scripts (scratch, no Lean): `<scratchpad>/T2089/check.py`, `comb.py`, `c9.txt` (= `git -C ../RBM2D --no-optional-locks show c9a24cf:RBM2D/Green/FlucIter.lean`, 1877 lines; the ticket's "1540 lines" is not the line count of `c9a24cf`; RBM2D HEAD `9e0f275` has 1521 lines and differs from `c9a24cf` by 36+/392- lines; all line numbers below are `c9a24cf`, where `integral_norm_flucAvg_pow_le_iter_budget` is at `:1453` as the ticket says).

### (i) Exponent table, the cut, and the map to the merged `condRow` / `FinDep`

Cut (at `c9a24cf`): Part 1 (this ticket) = `:81–:818`, i.e. through `end Slice1`; Part 2 (S1-21) = `:819–:1877` (starts with the `Counting` docstring, `section Counting` `:828`). `:800` of the ticket falls inside `applyOps_conj` (`:798–:807`); the nearest section boundary is `end Slice1 :818`, which also carries `applyOps_epsHom` (`:810–:816`, needs only `epsHom_inl/inr`, merged `FlucVanish.lean:976–981`). Part 1 has 71 declarations:
```
predSplit measurable_predSplit preimage_predSplit_pi measurePreserving_predSplit predSplit_predSplit BddMeas
BddMeas.integrable BddMeas.rowIntegrable BddMeas.sub BddMeas.mul bddMeas_const bddMeas_prod condPred
condRow_eq_condPred condPred_congr BddMeas.condPred integral_integral_predSplit condPred_condPred
condRow_condRow_comm qRow qRow_apply qRow_add_condRow BddMeas.condRow BddMeas.qRow condRow_zero condRow_qRow
condRow_qRow_comm applyOps applyOps_nil applyOps_cons_true applyOps_cons_false numQ numQ_nil numQ_cons_true
numQ_cons_false BddMeas.applyOps condRow_applyOps_comm applyOps_zero condRow_applyOps_qRow finDep_sub
finDep_condRow finDepOffRow_condRow_self finDep_qRow finDep_applyOps pivotFam pivotFam_self pivotFam_of_mem
pivotFam_of_not_mem prod_pivotFam_eq prod_eq_sum_pivotFam integral_prod_pivotFam_empty bddMeas_pivotFam OpsOk
OpsOkOut opsOkOut_nil OpsOkOut.opsOk OpsOkOut.mono OpsOkOut.cons pivotWords pivotFam_eq_applyOps
sum_numQ_pivotWords norm_condRow_le norm_applyOps_le flucDiag_eq_qRow finDep_greenDiagCentered
bddMeas_greenDiagCentered bddMeas_flucDiag condRow_conj qRow_conj applyOps_conj applyOps_epsHom
```
Part 2 (33, S1-21): `loneSlots mem_loneSlots image_loneSlots_eq two_mul_card_image_le_add_card_loneSlots card_filter_card_image_le sum_prod_abs_card_image_le sum_weighted_le bddMeas_epsHom_flucDiag OpsOkOut.length_le norm_integral_prod_applyOps_le_graded norm_integral_prod_qRow_le_graded FlucGainUpTo' (+3 projections) norm_integral_prod_epsHom_flucDiag_le_budget integral_norm_flucAvg_pow_le_iter_budget` and the 14 `flucIter_*` checks/helpers (`:1623ff`).
`UniformWeight` first occurs at `:967` and `:1024` (Part 2), so DECISIONS §30 does not touch Part 1.

| Item | Value / constraint | Slack |
|---|---|---|
| d-exponents in Part 1 | none: no `Z2`, `zdist`, `UniformWeight`, `svar`, `W ^ 2`, `L ^ 2`, `(W * L)` token in `:81–:818` (grep below, count 0); the only powers are `2 ^ numQ l` and comment text | nothing to re-derive at d ≥ 3; no statement is false at d ≥ 3 |
| lattice parameters of the instance | d = 3, L = 3 (≥ 3, `Sizes.three_le_L`), W = 2, g = 1/2; N = (WL)^d = 216, W^d = 8 | `hd : 3 ≤ d` is not needed in Part 1 |
| variance profile at the instance | S_ii = W^{-d}(1+2dg²)^{-1} = 0.4/8 = 0.05; 2d = 6 neighbour blocks of weight 0.1/8; row sum 1 (script) | exact |
| `η_t = Im zt E t = (1-t)·√(4-E²)/2` | `> 0` iff `|E| < 2`, `t < 1` (hypotheses of `bddMeas_greenDiagCentered`, `bddMeas_flucDiag`); `E=0, t=0`: `mE 0 = i`, `zt = i`, `η = 1` | `η = 1`; slacks: `1 - t = 1`, `2 - |E| = 2` |
| envelope `b = η_t⁻¹ + 1` (`norm_greenDiagCentered_le_env`, merged `LDE.lean:239`) | `‖G_kk - m‖ ≤ b = 2` | observed max 0.625 (10⁴ samples): factor 3.2 |
| crude constant in `norm_applyOps_le` | `‖applyOps l X‖ ≤ 2^{numQ l}·b`, factor 2 per `Q` from `norm_sub_condRow_le` | `Q_κ F`: bound 4, observed 0.106; `P_κ F`: bound 2, observed 0.619 |
| `sum_numQ_pivotWords` | `∑ numQ(pivotWords) = ∑ numQ(L i) + #S`, needs `S ⊆ univ.erase i₀` | equality, slack 0 (6144 cases checked) |
| `OpsOkOut.cons` | needs `hlone : ∀ j ≠ i₀, k j ≠ k i₀`, `i₀ ∈ R`, `i ≠ i₀`, `OpsOkOut k i R l` | at the instance: 3 distinct sites, hlone true; 96 admissible cases (48 with nonempty word) |
| `prod_eq_sum_pivotFam` | exact pointwise identity, `2^{#ι-1}` subsets `S ⊆ univ.erase i₀`; no condition on `F` | #ι = 3: 4 terms; max pointwise error 2.1e-17 |
| `integral_prod_pivotFam_empty` | `F i` bounded measurable and `FinDep`, `condRow κ (F i₀) = 0`; value `0` | MC: `|E[term ∅]|/se = 0.42` |

Map of RBM2D (`c9a24cf`, `d : Sizes`, `Idx (d.L n) (d.W n)`) to the merged files (`sz : Sizes d`, `Idx d (sz.L n) (sz.W n)`, `Sizes.SeqΩ sz`, `Sizes.seqP sz`):
- `condRow d n k X` is the merged `RBM.Green.condRow sz n k X`, `FlucVanish.lean:170` (`∫ ω', X (rowSplit sz n k ω ω')`; `condRow_apply :174` is `rfl`). Reused as is: `IsRowCoord :80`, `rowSplit :97` (`if IsRowCoord sz n k c then ω' c else ω c`), `rowSplit_apply_of_(not_)isRowCoord :101/:106`, `RowIntegrable :178`, `rowIntegrable_of_measurable_of_bound :187`, `condRow_const :196`, `condRow_condRow :202`, `rowSplit_condRow :212`, `condRow_sub :217`, `condRow_sub_condRow :225`, `FinDepOffRow :243`, `condRow_of_finDepOffRow :261`, `condRow_mul_of_finDepOffRow' :270`, `integral_condRow :282`, `finDepOffRow_prod :746`, `finDepOffRow_condRow :761`, `integrable_P_of_measurable_of_bound :779`, `integral_mul_prod_eq_zero :793` (hypotheses `hZ0 hY hint`, as in RBM2D), `norm_sub_condRow_le :888`, `epsHom :976`; `LDE.lean`: `measurable_condRow :154`, `measurable_greenDiagCentered :162`, `norm_greenDiagCentered_le_env :239`; `greenDiagCentered :813`, `flucDiag :818` (`flucDiag_eq_qRow` stays `rfl`).
- `FinDep d g` is the merged `FinDep sz g` (`LDEQuad.lean:79`, `∃ I, ∀ ω ω', (∀ e ∈ I, ω e = ω' e) → g ω = g ω'`, any value type `V`); `finDep_of_Hflow` is merged `FlucVanish.lean:582` (`finDep_greenDiagCentered` uses it). `FinDepOffRow sz n k g` = `FinDep` with witness set off row `k`.
- `condRow_eq_condPred` (`:223`) for the merged `condRow`: `condRow sz n k X = condPred sz (IsRowCoord sz n k) X`; both unfold to `∫ ω', X (fun c => if IsRowCoord sz n k c then ω' c else ω c)` with the instance `decidableIsRowCoord`, so it is `rfl` as in RBM2D.
- To port (not merged): `predSplit` + its 4 lemmas, `condPred`, `BddMeas` and closure lemmas, `condRow_zero`, `qRow`, `applyOps`, `numQ`, `finDep_sub/condRow/qRow/applyOps`, `finDepOffRow_condRow_self` (merged `finDepOffRow_condRow :761` has a `FinDepOffRow` hypothesis, not `FinDep`, so it does not replace it), `norm_condRow_le` (the merged `norm_sub_condRow_le` inlines the same bound).
- Renames inside Part 1: `spectralZ E t → zt E t`, `spectralM E → mE E` (`Defs/Semicircle.lean:179, :38`); `integral_conj` is Mathlib (`Integral/Bochner/ContinuousLinearMap.lean:173`).

### (ii) One concrete nondegenerate instance (d = 3, L = 3, W = 2, g = 1/2)

Hypotheses of the targets: `|E| < 2`, `t < 1` (E = 0, t = 0, u arbitrary), three distinct rows `k0 = (0,0,0)` (block (0,0,0)), `k1 = (0,0,1)` (same block), `k2 = (2,0,0)` (neighbour block (1,0,0)); `ι = Fin 3`, pivot `i₀ = 0`, `κ = k0`; all bounded measurable `F_i = G_{k_i k_i} - m`, `z = i`, `m = i` (`m = -(t m + z)⁻¹` at `t = 0`, asserted in the script). `E_κ` is the exact resampling of row `κ` (Schur complement of the minor), estimated by 64 inner samples, an independent set per slot.
```
$ python3 <scratchpad>/T2089/check.py          (10^4 outer samples, 41.5 s)
N = 216  W^d = 8  row sums of S: min/max 1.0 1.0  S_ii = 0.05  2d neighbours/block: 6
slot sites [(0, 0, 0), (0, 0, 1), (2, 0, 0)] blocks [(0, 0, 0), (0, 0, 0), (1, 0, 0)] distinct: True
samples 10000 inner K 64
max pointwise |prod F_i - sum_S prod pivotFam_S| = 2.0888836804026048e-17
E[prod F_i]        = -3.964e-05+2.989e-05i  (se 1.5e-04)
E[term S=()]       = -4.080e-05-4.839e-05i  (se 1.5e-04)
E[term S=(1,)]     = -8.254e-07+6.969e-05i  (se 5.5e-06)
E[term S=(2,)]     = 2.006e-06+8.600e-06i  (se 1.6e-06)
E[term S=(1, 2)]   = -1.744e-08+7.967e-10i  (se 6.3e-08)
sum_{S != empty}   = 1.163e-06+7.829e-05i  (se 5.7e-06)
max |G_kk-m| observed 0.6248301232039836 <= eta^-1+1 = 2.0 ; max|Q_k F| = 0.10550583202044175 <= 2*2 = 4; max|P_k F| = 0.619049685764106 <= 2
|E[term empty]|/se = 0.42 (vanishing lemma: 0 exactly); rms of term empty = 1.49e-02
$ python3 <scratchpad>/T2089/comb.py
sum_numQ_pivotWords: 6144 cases (iota = Fin 3, all i0, all S, all word families of length<=1), identity holds
OpsOkOut.cons: 96 admissible cases (48 with nonempty word), conclusion holds
$ sed -n 81,818p c9.txt | grep -cE 'Z2|zdist|UniformWeight|svar|blockAvg|W \^ 2|L \^ 2|\(W \* L\)'
0
```
Reading: `prod_eq_sum_pivotFam` holds pointwise to 2e-17 (the pivot factor `F_0 = Q_κ(G_κκ - m)`, so `E_κ F_0 = 0`); the all-`P` term `S = ∅` has mean 0 within 0.42 se, as `integral_prod_pivotFam_empty` asserts (its rms is 1.5e-2 = 100 se, so the test is not trivial); the terms `S = {1}` and `S = {2}` are resolved nonzero (12σ and 5σ), so the expansion is not vacuous. Sample space and all bounds are concrete: no `N = 0`, no empty `ι`, no collapsed window; the file's own `FinDep`/`BddMeas` hypotheses hold (bounded measurable functions of finitely many coordinates). External hypotheses: none in Part 1 (the gain interface `FlucGainUpTo'` is Part 2).

Verdicts (this ticket, Part 1 of `Green/FlucIter.lean`, `c9a24cf:81–818`): **PASS**. No statement of Part 1 carries a `d = 2` exponent; no hypothesis set is unsatisfiable; nothing missing (every upstream declaration used has a merged counterpart or is ported as listed above). Observation for the dispatcher: the ticket's "1540 lines at `c9a24cf`" is 1877 lines there; the `:800`/`:980–995`/`:1453` references are consistent with `c9a24cf`.

## (a′) Preflight corrections — Sat Oct  3 23:54:35 UTC 2026

No verdict changes. Two details of (a) differ from the script output in (b):
1. The ported code of Part 1 starts at `c9a24cf:84` (`namespace RBM.Green`); `:81–:83` are the last docstring line, its closing `-/` and a blank line. The 71 names of (i) are confirmed by script (b, "declaration lists").
2. Part 2 (S1-21), script in (b): 33 top-level declarations from `:819` on, 13 of them named `flucIter_*` (plus `flucIterCheckSizes/V/K` inside the 33); (a) says "33 + 14".

## (b) Script output — Sat Oct  3 23:50:31 UTC 2026

Scratch dir S = scratchpad/T2089 (outside the repository); worktree RBM3D-wt/T2089, branch t/T2089.
```
$ git status --short | wc -l; git log --oneline -1; git diff main...t/T2089 --stat | cat
       0
400d42e T2089: S1-20 Green/FlucIter, first part (coordinate slicing, BddMeas, qRow/applyOps words, pivot expansion)
 RBM3D/Green/FlucIter.lean | 1085 +++++++++++++++++++++++++++++++++++++++++++++
 1 file changed, 1085 insertions(+)
$ git -C /Users/junyin/Lean_proof/RBM2D --no-optional-locks log -1 --format=%h; git -C /Users/junyin/Lean_proof/RBM2D --no-optional-locks diff --stat c9a24cf HEAD -- RBM2D/Green/FlucIter.lean
9e0f275
 RBM2D/Green/FlucIter.lean | 428 ++++------------------------------------------
 1 file changed, 36 insertions(+), 392 deletions(-)
$ lake build RBM3D.Green.FlucIter 2>&1 | tail -2; echo "exit: ${PIPESTATUS[0]}"
Note: This linter can be disabled with `set_option linter.unusedDecidableInType false`
Build completed successfully (3332 jobs).
exit: 0
$ lake env lean RBM3D/Green/FlucIter.lean; echo "exit: $?   (no output: no warning, no error)"
exit: 0   (no output: no warning, no error)
$ lake build 2>&1 | tail -1; echo "exit: ${PIPESTATUS[0]}"
Build completed successfully (3825 jobs).
exit: 0
# registry pre-check (CLAUDE.md 4.8, DECISIONS 20); the root import is added only at merge
$ cat $S/precheck.lean; lake env lean $S/precheck.lean > $S/precheck.out 2>&1; echo "exit: $?"; head -1 $S/precheck.out; grep -c "unregistered\|error" $S/precheck.out
import RBM3D
import RBM3D.Green.FlucIter
#assert_rbm_axioms
exit: 0
axiom audit: 2849 theorems, 1114 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
0
$ lake env lean $S/precheck0.lean > $S/precheck0.out 2>&1; echo "baseline (import RBM3D only) exit: $?"; head -1 $S/precheck0.out
baseline (import RBM3D only) exit: 0
axiom audit: 2780 theorems, 1103 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
# axioms: #print axioms of the 71 declarations of Part 1 and the 3 public instance theorems
$ lake env lean $S/axioms.lean > $S/axioms.out 2>&1; echo "exit: $?"; bash $S/axsum.sh
exit: 0
2 declarations depend on exactly [propext]
69 declarations depend on exactly [propext, Classical.choice, Quot.sound]
3 declarations depend on no axiom: numQ numQ_nil OpsOk
$ grep -cE "sorry|admit|native_decide|^axiom|^[[:space:]]+axiom " RBM3D/Green/FlucIter.lean
0
# declaration lists (top-level names, script)
$ diff $S/names2d.txt $S/names3d.txt && echo "RBM2D c9a24cf:81-818 and RBM3D lines 1-815: the same $(wc -l < $S/names3d.txt) names, same order"
RBM2D c9a24cf:81-818 and RBM3D lines 1-815: the same       71 names, same order
```

```
# the cut: S1-21 side (RBM2D c9a24cf, c9.txt = git show c9a24cf:RBM2D/Green/FlucIter.lean)
$ grep -nE "^(section|end) (Slice1|Counting)" $S/c9.txt
88:section Slice1
818:end Slice1
828:section Counting
949:end Counting
$ sed -n 819,1877p $S/c9.txt | grep -E "^(@\[[^]]*\] )?(private |noncomputable |protected )*(theorem|lemma|def|structure|abbrev|example|instance)" | sed -E "s/^(@\[[^]]*\] )?((private|noncomputable|protected) )*(theorem|lemma|def|structure|abbrev|example|instance) ?([^ ]*).*/\5/" > $S/names2d_part2.txt; wc -l < $S/names2d_part2.txt; paste -sd" " $S/names2d_part2.txt | fold -s -w 150
      33
loneSlots mem_loneSlots image_loneSlots_eq two_mul_card_image_le_add_card_loneSlots card_filter_card_image_le sum_prod_abs_card_image_le 
sum_weighted_le bddMeas_epsHom_flucDiag OpsOkOut.length_le norm_integral_prod_applyOps_le_graded norm_integral_prod_qRow_le_graded FlucGainUpTo' 
FlucGainUpTo'.B_nonneg FlucGainUpTo'.rho_nonneg FlucGainUpTo'.gain norm_integral_prod_epsHom_flucDiag_le_budget 
integral_norm_flucAvg_pow_le_iter_budget flucIter_integral_prod_norm_applyOps_le_crude flucIter_flucGainUpTo'_of_crude flucIterCheckSizes 
flucIter_check_eta flucIter_check_crude flucIter_check_gain_one flucIter_check_gain_half flucIter_check_moment_row flucIter_check_moment_block 
flucIterCheckV flucIter_check_iter flucIterCheckK flucIter_check_hgain flucIter_check_graded flucIter_check_qRow flucIter_check_comm
$ grep -n "UniformWeight" $S/c9.txt | sed -n 3,5p | cut -c1-72
967:    (hw : UniformWeight t c A) {s n : ℕ} (hs : s ≤ A.card) (hsn : s 
1024:theorem sum_weighted_le {t : κ → ℝ} {c : ℝ} {A : Finset κ} (hw : Un
1458:    (hw : UniformWeight T c A) (hp : 2 * p ≤ A.card) :
```

```
# port diff: RBM3D lines 60-798 renamed back to RBM2D (R1 `sz : Sizes d` -> `d : Sizes`, R2 `Idx d (sz.L n) (sz.W n)` -> `Idx (d.L n) (d.W n)`, `zt`/`mE` -> `spectralZ`/`spectralM`) against `c9a24cf:84-818`
$ sed -n 60,798p RBM3D/Green/FlucIter.lean | perl -pe 's/\{d : ℕ\} \{sz : Sizes d\}/{d : Sizes}/g; s/\(sz : Sizes d\)/(d : Sizes)/g; s/Idx d \(sz\.L n\) \(sz\.W n\)/Idx (d.L n) (d.W n)/g; s/\bsz\b/d/g; s/\bzt\b/spectralZ/g; s/\bmE\b/spectralM/g' > $S/3d_norm.txt; sed -n 84,818p $S/c9.txt > $S/2d_part.txt; diff $S/2d_part.txt $S/3d_norm.txt | grep -v "^---" | cut -c1-110
58c58,59
< theorem measurePreserving_predSplit (d : Sizes) (p : Sizes.SeqCoord d → Prop) [DecidablePred p] :
> theorem measurePreserving_predSplit (d : Sizes) (p : Sizes.SeqCoord d → Prop)
>     [DecidablePred p] :
152c153
<   exact congrArg (fun inst : DecidablePred p => @condPred d p inst X) (Subsingleton.elim hp hq)
>   exact congrArg (fun inst : DecidablePred p => @condPred d d p inst X) (Subsingleton.elim hp hq)
234c235,236
< noncomputable def qRow (d : Sizes) (n : ℕ) (k : Idx (d.L n) (d.W n)) (X : Sizes.SeqΩ d → ℂ) :
> noncomputable def qRow (d : Sizes) (n : ℕ) (k : Idx (d.L n) (d.W n))
>     (X : Sizes.SeqΩ d → ℂ) :
606c608,609
<     (L : ι → List (Bool × Idx (d.L n) (d.W n))) (i : ι) : List (Bool × Idx (d.L n) (d.W n)) :=
>     (L : ι → List (Bool × Idx (d.L n) (d.W n))) (i : ι) :
>     List (Bool × Idx (d.L n) (d.W n)) :=
682c685,686
< theorem bddMeas_greenDiagCentered (hE : |E| < 2) (ht : t < 1) (u : ℝ) (k : Idx (d.L n) (d.W n)) :
> theorem bddMeas_greenDiagCentered (hE : |E| < 2) (ht : t < 1) (u : ℝ)
>     (k : Idx (d.L n) (d.W n)) :
$ sed -n 81,818p $S/c9.txt | grep -cE "Z2|zdist|UniformWeight|svar|blockAvg|W \^ 2|L \^ 2|\(W \* L\)"; sed -n 60,798p RBM3D/Green/FlucIter.lean | grep -cE "Z2|zdist|UniformWeight|svar|blockAvg|W \^ 2|L \^ 2|\(W \* L\)"
0
0
```

```
# target statements (declaration line to `:=`), lines of RBM3D/Green/FlucIter.lean; sections Pivot/Words/Iterate declare {ι} [Fintype ι] [DecidableEq ι], Env declares {E t : ℝ}
$ bash $S/stmt.sh condRow_eq_condPred prod_eq_sum_pivotFam integral_prod_pivotFam_empty sum_numQ_pivotWords OpsOkOut.cons norm_applyOps_le bddMeas_greenDiagCentered bddMeas_flucDiag | grep -v "^$"
203: theorem condRow_eq_condPred (sz : Sizes d) (n : ℕ) (k : Idx d (sz.L n) (sz.W n))
    (X : Sizes.SeqΩ sz → ℂ) :
    condRow sz n k X = condPred sz (IsRowCoord sz n k) X := rfl
539: theorem prod_eq_sum_pivotFam (sz : Sizes d) (n : ℕ) (κ : Idx d (sz.L n) (sz.W n)) (i₀ : ι)
    (F : ι → Sizes.SeqΩ sz → ℂ) (ω : Sizes.SeqΩ sz) :
    ∏ i, F i ω
      = ∑ S ∈ (Finset.univ.erase i₀).powerset, ∏ i, pivotFam sz n κ i₀ S F i ω := by
557: theorem integral_prod_pivotFam_empty (sz : Sizes d) (n : ℕ) {κ : Idx d (sz.L n) (sz.W n)} {i₀ : ι}
    {F : ι → Sizes.SeqΩ sz → ℂ} (hF : ∀ i, BddMeas sz (F i)) (hFd : ∀ i, FinDep sz (F i))
    (h0 : condRow sz n κ (F i₀) = 0) :
    ∫ ω, ∏ i, pivotFam sz n κ i₀ (∅ : Finset ι) F i ω ∂(Sizes.seqP sz) = 0 := by
681: theorem sum_numQ_pivotWords {k : ι → Idx d (sz.L n) (sz.W n)} {i₀ : ι} {S : Finset ι}
    (hS : S ⊆ Finset.univ.erase i₀) (L : ι → List (Bool × Idx d (sz.L n) (sz.W n))) :
    ∑ i, numQ (pivotWords k i₀ S L i) = (∑ i, numQ (L i)) + S.card := by
633: theorem OpsOkOut.cons {k : ι → Idx d (sz.L n) (sz.W n)} {i i₀ : ι} {R : Finset ι}
    (hlone : ∀ j, j ≠ i₀ → k j ≠ k i₀) (hi₀ : i₀ ∈ R) (hne : i ≠ i₀)
    {l : List (Bool × Idx d (sz.L n) (sz.W n))} (h : OpsOkOut k i R l) (b : Bool) :
    OpsOkOut k i (R.erase i₀) ((b, k i₀) :: l) := by
713: theorem norm_applyOps_le (l : List (Bool × Idx d (sz.L n) (sz.W n))) {X : Sizes.SeqΩ sz → ℂ}
    {b : ℝ}
    (hX : ∀ ω, ‖X ω‖ ≤ b) (ω : Sizes.SeqΩ sz) :
    ‖applyOps sz n l X ω‖ ≤ 2 ^ numQ l * b := by
744: theorem bddMeas_greenDiagCentered (hE : |E| < 2) (ht : t < 1) (u : ℝ)
    (k : Idx d (sz.L n) (sz.W n)) :
    BddMeas sz (greenDiagCentered sz n u (zt E t) (mE E) k) :=
750: theorem bddMeas_flucDiag (hE : |E| < 2) (ht : t < 1) (u : ℝ) (k : Idx d (sz.L n) (sz.W n)) :
    BddMeas sz (flucDiag sz n u (zt E t) (mE E) k) :=

# the compiled nonempty instances: 54 examples in lines 816-1085 (data below), three named instance theorems
$ sed -n 821,826p RBM3D/Green/FlucIter.lean; sed -n 830,831p RBM3D/Green/FlucIter.lean
private def szT : Sizes 3 where
  L := fun _ => 3
  W := fun _ => 2
  lam := fun _ => 1 / 2
  three_le_L := fun _ => le_rfl
  W_pos := fun _ => by norm_num
private def site : Fin 3 → Idx 3 (szT.L 0) (szT.W 0) :=
  ![![0, 0, 0], ![0, 0, 1], ![2, 0, 0]]
$ sed -n 995,1007p RBM3D/Green/FlucIter.lean
/-- **Instance of `prod_eq_sum_pivotFam`**: the product of the three fluctuations `Z_0 Z_1 Z_2`
is the sum of the four terms `S ⊆ {1, 2}` of the pivot expansion at `κ = site 0`, `i₀ = 0`. -/
example (ω : Sizes.SeqΩ szT) :
    ∏ i, Z i ω = ∑ S ∈ (Finset.univ.erase (0 : Fin 3)).powerset,
      ∏ i, pivotFam szT 0 (site 0) 0 S Z i ω :=
  prod_eq_sum_pivotFam szT 0 (site 0) 0 Z ω

/-- **Instance of `integral_prod_pivotFam_empty`**: the all-`P` term has integral `0`; the pivot
factor is `Z_0 = Q_{site 0} (G_{00} - m)`, killed by `E_{site 0}`. -/
example :
    ∫ ω, ∏ i, pivotFam szT 0 (site 0) 0 (∅ : Finset (Fin 3)) Z i ω ∂(Sizes.seqP szT) = 0 :=
  integral_prod_pivotFam_empty szT 0 bZ fZ (condRow_qRow (bG 0) (site 0))

$ grep -c "^example" RBM3D/Green/FlucIter.lean; sed -n 816,1085p RBM3D/Green/FlucIter.lean > $S/inst.txt; while read n; do s=${n##*.}; if [[ "$n" == *.* ]]; then p="\\.$s\\b"; else p="\\b$n\\b"; fi; echo "$(grep -cE "$p" $S/inst.txt) $n"; done < $S/names3d.txt | sort -n | head -2
54
1 applyOps_conj
1 applyOps_cons_false

# name clash (positive control first), then the 71 names
$ grep -rnE "(theorem|lemma|def|structure|abbrev) +condRow([^A-Za-z0-9_'.]|$)" RBM3D --include="*.lean" | cut -c1-90
RBM3D/Green/FlucVanish.lean:170:noncomputable def condRow {d : ℕ} (sz : Sizes d) (n : ℕ) (
$ bash $S/clash.sh
names declared in another RBM3D file: 0 (of       71)

# merged declarations reused by name (count of uses in lines 60-798; file that declares it)
$ for n in condRow rowSplit IsRowCoord RowIntegrable FinDepOffRow FinDep epsHom condRow_condRow condRow_sub integral_mul_prod_eq_zero norm_sub_condRow_le finDepOffRow_condRow finDepOffRow_prod finDep_of_Hflow measurable_condRow norm_greenDiagCentered_le_env rowIntegrable_of_measurable_of_bound integrable_P_of_measurable_of_bound greenDiagCentered flucDiag; do c=$(sed -n 60,798p RBM3D/Green/FlucIter.lean | grep -ow "$n" | wc -l | tr -d " "); f=$(grep -lE "(theorem|def|structure|abbrev) +$n([^A-Za-z0-9_]|$)" RBM3D/Green/*.lean | grep -v FlucIter | head -1 | xargs -n1 basename 2>/dev/null); [ "$c" -gt 0 ] && echo "$n:$c:${f%.lean}"; done | paste -sd" " - | fold -s -w 150
condRow:46:FlucVanish rowSplit:3:FlucVanish IsRowCoord:8:FlucVanish RowIntegrable:1:FlucVanish FinDepOffRow:3:FlucVanish FinDep:12:LDEQuad 
epsHom:2:FlucVanish condRow_sub:1:FlucVanish integral_mul_prod_eq_zero:3:FlucVanish norm_sub_condRow_le:1:FlucVanish finDep_of_Hflow:1:FlucVanish 
norm_greenDiagCentered_le_env:1:LDE rowIntegrable_of_measurable_of_bound:1:FlucVanish integrable_P_of_measurable_of_bound:1:FlucVanish 
greenDiagCentered:3:FlucVanish flucDiag:2:FlucVanish
```

### Narrative (facts only)
1. State: branch `t/T2089` held commit `400d42e` (`RBM3D/Green/FlucIter.lean`, 1085 lines, the only file of `git diff main...t/T2089`) with a clean working tree when this stage started; this stage did not edit the Lean file. Every script above ran on that commit.
2. Cut: Part 1 = `c9a24cf:84–818` (`namespace RBM.Green` through `end Slice1`), 71 declarations, list in (a)(i), equal in order to the file's top-level names. `:800` is inside `applyOps_conj` (`:798–807`); the nearest section boundary is `:818`, so `applyOps_epsHom` (`:810–816`) is in S1-20. S1-21 = `:819–1877` (`section Counting :828`, 33 declarations listed above, key statement `integral_norm_flucAvg_pow_le_iter_budget :1453`).
3. Reuse: `condRow`, `IsRowCoord`, `rowSplit`, `RowIntegrable`, `FinDepOffRow`, `FinDep`, `epsHom`, `greenDiagCentered`, `flucDiag` and the lemmas counted above are the merged ones, none redefined; `condRow_eq_condPred` (`:203`) is `rfl` for the merged `condRow`, as in RBM2D. New here: `predSplit`, `BddMeas`, `condPred`, `qRow`, `applyOps`, `numQ`, `pivotFam`, `OpsOk`, `OpsOkOut`, `pivotWords`, `condRow_zero`, `finDepOffRow_condRow_self`, `norm_condRow_le` and the other lemmas of the 71.
4. Dimension: counts 0 and 0 above (no `Z2`, `zdist`, `svar`, `UniformWeight`, `W ^ 2`, `L ^ 2` token in `c9a24cf:81–818` or in the ported lines): no statement has a `d = 2` exponent and `hd : 3 ≤ d` is not needed. The first code occurrence of `UniformWeight` is `c9a24cf:967` (S1-21), so DECISIONS §30 does not touch this ticket; S1-21 needs `BoundedWeight` at `:967`, `:1024`, `:1458`.
5. Port: after renaming back, the file differs from `c9a24cf:84–818` in four line wraps and one artifact of the renaming (`@condPred d sz p inst X`, file line 212, reads `d d` after `sz → d`); every statement is the RBM2D one after R1–R4. The paper states none of these lemmas (file docstring cites `paper/tex/3_5_Loop_Hierarchy.tex:37`: proofs dimension-independent, from `[YY_25]`).
6. Instance: `szT : Sizes 3`, `L = 3`, `W = 2`, `lam = 1/2` (constant sequences, no limit claim), slice `n = 0`, `N = 216`; sites `(0,0,0)`, `(0,0,1)`, `(2,0,0)` pairwise distinct (`decide`); `E = 0`, `t = 0`, `u = 1/2`, `η_t = 1`: the data of the numeric check in (a)(ii). 54 `example`s; each of the 71 declarations occurs in the instance block (min count 1, script); hypotheses (`BddMeas`, `FinDep`, `|E| < 2`, `t < 1`, `hS`, `hlone`, `h0`, ...) are discharged inside the examples by lemmas, `decide` or `norm_num`; no external hypothesis.
7. Registry: pre-check exit 0, 0 unregistered, `Test/Axioms.lean` unchanged. `scanPremises` (`Test/Axioms.lean:285`) flags a `Prop`-valued predicate only if no theorem concludes it; `BddMeas` and `OpsOkOut`/`OpsOk` are concluded by theorems of this file (`BddMeas.condRow`, `OpsOkOut.cons`, `OpsOkOut.opsOk`).
8. Merge: the hub adds `import RBM3D.Green.FlucIter` to `RBM3D.lean`; the full `lake build` above does not contain the module, the pre-check above does.

## (c) Verified Mathlib names used (the non-routine ones; `#check` exit 0 for each; module by `env.getModuleIdxFor?`)
- Finset.prod_add : Mathlib.Algebra.BigOperators.Ring.Finset
- Finset.mul_prod_erase : Mathlib.Algebra.BigOperators.Group.Finset.Basic
- Finset.prod_sdiff : Mathlib.Algebra.BigOperators.Group.Finset.Basic
- Finset.prod_filter_mul_prod_filter_not : Mathlib.Algebra.BigOperators.Group.Finset.Basic
- Finset.cons_induction_on : Mathlib.Data.Finset.Insert
- Finset.sum_ite_mem : Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
- Finset.notMem_erase : Mathlib.Data.Finset.Erase
- Finset.sum_add_distrib : Mathlib.Algebra.BigOperators.Group.Finset.Basic
- integral_conj : Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
- MeasureTheory.integral_map : Mathlib.MeasureTheory.Integral.Bochner.Basic
- MeasureTheory.integral_congr_ae : Mathlib.MeasureTheory.Integral.Bochner.Basic
- MeasureTheory.norm_integral_le_of_norm_le_const : Mathlib.MeasureTheory.Integral.Bochner.Basic
- MeasureTheory.StronglyMeasurable.integral_prod_right' : Mathlib.MeasureTheory.Integral.Prod
- MeasureTheory.Measure.infinitePi_pi : Mathlib.Probability.ProductMeasure
- MeasureTheory.Measure.eq_infinitePi : Mathlib.Probability.ProductMeasure
- MeasureTheory.Measure.prod_prod : Mathlib.MeasureTheory.Measure.Prod
- MeasureTheory.Measure.map_apply : Mathlib.MeasureTheory.Measure.Map
- MeasureTheory.MeasurePreserving : Mathlib.Dynamics.Ergodic.MeasurePreserving
- measurable_pi_iff : Mathlib.MeasureTheory.MeasurableSpace.Constructions
- measurable_pi_apply : Mathlib.MeasureTheory.MeasurableSpace.Constructions
- List.nodup_cons : Init.Data.List.Pairwise

Names verified absent: none looked up.

## (d) Open issues and paper-delta candidates
- Paper-delta candidates: none. Every statement of Part 1 is the RBM2D one after R1–R4, dimension-free; the paper states none of these lemmas.
- For the dispatcher (ticket text): (1) "1540 lines at `c9a24cf`" is 1877 lines (as in (a)); (2) the cut is `:818`, not `:800`, and includes `applyOps_epsHom`; S1-21 starts at `:819`; (3) `UniformWeight` is in S1-21 code at `c9a24cf:967, :1024, :1458` (DECISIONS §30).
- Public names beyond the 71: `RBM.Green.FlucIterInst.{bddMeas_greenDiagCentered_szT, bddMeas_flucDiag_szT, finDep_greenDiagCentered_szT}` (instance theorems, prefixed with the file stem, CLAUDE.md §3 (E)); the other helpers of the instance block are `private`.
- No obstruction: no hypothesis added, no statement weakened, no pinned signature changed, no file outside the sole writable files touched.
