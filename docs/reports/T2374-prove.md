Prover model: claude-sonnet-5-5
## (a) Math preflight — Sat Oct 10 07:42:18 UTC 2026

Input read on `t/T2370` at d8bc699 (state `audit-pass`; `KTreeDeriv.lean` is 612 lines by `wc -l`); no `lake` run, no Lean written. Scripts: `S=/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/966b45d4-be15-4db2-88b3-45a074bfecd5/scratchpad/T2374` (not in the repository): `chord.py` (mirror of `KLwIn, KLshiftIn, KLFIn, KLcol, KLshiftOut, KLFOut, KLinV, KLoutV, KLglueV`, `KLCut.lean:361-600`, of `KLArcLe`, of `cutGlueL/R` `TreeRep.lean:75-82`, of `treeEqRhsS` at `S=1`, of the spliced family, and of the chord part of `BAGammaDerivRHS`), `c3.py`, `mirror.py`, `mgraph.py`, `kode.py` (T2370's/T2367's, `cmp` same), `control.py`, `nonsym.py`, `table.py`, `instance.py`. Notation: `J=(i,j)` a diagonal, `w=j-i`, `p=n-w+1` (outer polygon), `q=w+1` (inner polygon), `Q=M^{(σσ')}`, `Θ=(1-tQ)⁻¹`, `Γ_F=BAGamma`.

### (i) Exponent table
| quantity | value | constraint | slack |
|---|---|---|---|
| `n` | `≥ 3` | pins; `BASplicedFam` clause 3 | `n=3`: `diagonals 3 = ∅` (both sides of target 2 are empty sums); first nonempty case `n=4` |
| width `w` | `2 ≤ w ≤ n-2` | `IsDiag n i j`: `i<j`, `j≠i+1`, `¬(i=0∧j=n-1)` (`Loop/Partition.lean:65`; `KLwidth_of_isDiag`) | `0` at `n=4` (`w=2`); `table.py` below: `w`-range `(2,n-2)` |
| outer length `p` | `n-w+1` | `length_cutGlueL`, `(k,l)=(i+1,j+1)`: `k+n-l+1`; must be `≥3` so clause 3 (not the closed 2-loop) gives `K(cutL)` | `p-3 = n-w-2 ≥ 0`, `0` at `w=n-2` |
| inner length `q` | `w+1` | `length_cutGlueR = l-k+1`; `≥3` | `q-3 = w-2 ≥ 0`, `0` at `w=2` |
| `p+q` | `n+2` | needed for the `W` power | exact |
| `W` power | `(W^d)⁻¹^(n-1) = W^d·(W^d)⁻¹^(p-1)·(W^d)⁻¹^(q-1)` | exponent `(p-1)+(q-1)-1 = n-1` | exact; at `W^d=0` (Lean `0⁻¹=0`): both sides `0` as `n-1 ≥ 2`; no `W≠0` hypothesis (as T2370) |
| pair count | `n` leaf pairs `+ n(n-3)/2` diagonal pairs `= n(n-1)/2` | pairs of `treeEqRhsS`: leaf `(v+1,v+2)` `v≤n-2`, wrap `(1,n)`, diagonal `(i+1,j+1)`; disjoint | exact; `(1,n)` is not a diagonal pair (`¬(i=0∧j=n-1)`); `chord.py` checks partition: `True`, `n=3..6` |
| cut bijection | `|{F∈TSP n: J∈F}| = |TSP p|·|TSP q|` (`KLsum_cut`, needs `2≤n`, `IsDiag`) | `(KLFOut,KLFIn)` bijective onto `TSP p × TSP q` | exact; `chord.py` `bijection True`, `n=4..6` |
| `t` | `0 ≤ t < 1` | only the derivative part (`baGamma_hasDerivAt`: `BATheta_hasDerivAt`, `BATheta_resolvent`); the chord-pair identity holds for all `t` | instance `t=1/2` |
| `BAReal`, `L≥3` | `BAReal d L g κ E m` (`BASelf`, `κ ≤ Im m`) | derivative and `BATheta` facts; `L≥3` only in the pins `BAKsolve`/`BATreeRep` (`NeZero L` for targets 2, 3) | instance `(d,L)=(3,4)`, `κ=Im m` |
| orientation (C2) | inner new leaf `Θ^{(σ_j,σ_i)}` vs chord `Θ^{(σ_i,σ_j)}` | `KLgval_split` gives the leaf `Pᵀ` with `P=Θ^{(σ_i,σ_j)}`; `Θ^{(s',s)}=(Θ^{(s,s')})ᵀ` is `BAKTreeDeriv_Theta_swap` (`t/T2370:RBM3D/BA/KTreeDeriv.lean:118`, private there; no hypothesis) | **no symmetry of `M` needed** (unlike the wrap pair of K05a); `nonsym.py`: non-symmetric `M`, `1e-14`. Not a C2 failure |
| C3 tolerance | `≤ 1e-12` (ticket), no ODE | per-`F` `2.9e-14`, per-`J` `3.4e-14`, (c) total `1.4e-13` (values up to `1.1e2`, relative `1e-15`) | factors `35`, `29`, `7` |
| `(Kn2sol)` at `n=2` | `K(t,[σ₁,σ₂],[a₁,a₂]) = (W^d)⁻¹ (ΘQ)(a₁,a₂)` | derivative `(W^d)⁻¹ΘQΘQ = W^d·(W^d)⁻¹ΘQ·(W^d)⁻¹ΘQ`; value at `t=0` is `BAMLoop` | exact; `baKsolveLe3_holds` (`KSolve.lean:478`) is public, its `BAKSolve_two_hasDerivAt` (`:359`) private (copy, stem `KTreeRep_`) |
| size | `KTreeRep.lean` central `1300`, low `900`, high `1800` | stop line `2000` (binding) | `700` / `1100` / `200` |
| Q4 (K05 total) | `612 + 1300 = 1912` (low `1512`, high `2412`; at the stop line `2612`) | 2051 Q4 line for K05 `3.3k` (0350 C5, `:99`) | `1388` / `1788` / `888` / `688`: not crossed |

### (ii) Concrete nondegenerate instance and C3 per-chord numerics
**Hypotheses of the targets.** Target 2: `BAReal d L g κ E m`, `BASplicedFam` (any `K`; `BAKcac` by K05a), `3 ≤ n`, `0 ≤ t<1`; target 3: `BAReal`; targets 4, 5: `Λ,κ>0`, `3≤L`, `g∈(0,Λ]`, `BAReal`. No external hypothesis (`BAKsolve` is proved here, not assumed): no limit computation owed. Lean instance: the flow point `P` of `(d,L)=(3,4)` (`MFixedPoint.lean:893`, `P.real : BAReal 3 4 P.g0 (Im m₀) P.E m₀`; `P` is a choice, so the numbers below use `g=1/2, E=0.3` and `m` solving `BASelf`, the same `BAReal` shape). Instance: `(d,L)=(3,4)`, `N=64`, `W=2`, `Λ=10`, `t=1/2`, `κ=Im m`, `n=4`, `J=(0,2)`, `F={(0,2)}`, plus `n=5`, `J=(1,3)` (`3` trees). `cd $S; python3 instance.py`:
```
Psi == Adj (l1 torus nearest neighbours):  True  N = L^d = 64  3 <= L: True  0 < g <= Lambda: True  W^d = 8
m = -0.096078036194+0.681402583263j; BASelf residual |m - L^-d tr M| = 2.3e-16; kappa := Im m = 0.681403 > 0: True; kappa <= Im m: True; M symmetric: True; 0 <= t < 1: True
n = 4, J = (0, 2): IsDiag: True, |{F in TSP n : J in F}| = 1 = |TSP 3|*|TSP 3| = 1, piece lengths (outer, inner) = (3, 3) both >= 3
  sigma = ++-+, a = (32, 45, 3, 59): per-F |chord-J term - sum_x Gout Gin| = 1.5e-21; W^-d(n-1) sum_F chord-J = -8.267103e-09-7.215653e-10j, (i+1,j+1) summand = -8.267103e-09-7.215653e-10j, diff 2.9e-24, nonzero: True; (c) total -1.790062e-08+2.511883e-09j vs treeEqRhsS -1.790062e-08+2.511883e-09j, diff 2.8e-23
  sigma = +-+-, a = (31, 6, 20, 14): per-F |chord-J term - sum_x Gout Gin| = 2.1e-20; W^-d(n-1) sum_F chord-J = -7.501559e-08-8.373779e-09j, (i+1,j+1) summand = -7.501559e-08-8.373779e-09j, diff 4.2e-23, nonzero: True; (c) total 5.745159e-07-1.324239e-07j vs treeEqRhsS 5.745159e-07-1.324239e-07j, diff 4.5e-22
n = 5, J = (1, 3): IsDiag: True, |{F in TSP n : J in F}| = 3 = |TSP 4|*|TSP 3| = 3, piece lengths (outer, inner) = (4, 3) both >= 3
  sigma = ++-+-, a = (47, 60, 31, 48, 13): per-F |chord-J term - sum_x Gout Gin| = 6.8e-22; W^-d(n-1) sum_F chord-J = 4.231443e-11-1.723940e-10j, (i+1,j+1) summand = 4.231443e-11-1.723940e-10j, diff 1.6e-25, nonzero: True; (c) total -1.780077e-09+3.806175e-09j vs treeEqRhsS -1.780077e-09+3.806175e-09j, diff 6.0e-24
  sigma = -++--, a = (31, 1, 27, 52, 35): per-F |chord-J term - sum_x Gout Gin| = 1.1e-21; W^-d(n-1) sum_F chord-J = 1.490522e-11-2.899704e-11j, (i+1,j+1) summand = 1.490522e-11-2.899704e-11j, diff 3.0e-25, nonzero: True; (c) total -7.116536e-11+1.856513e-10j vs treeEqRhsS -7.116536e-11+1.856513e-10j, diff 3.3e-25
```
**C3 per-chord (binding).** `cd $S; python3 chord.py 6` (`q∈{4,5}`, `g∈{.2,.5}`, `t∈{.3,.5,.7}`, `W∈{1,2}`, 4 configurations; every `σ`; all `a` at `n≤4`, 6 random `a` at `n=5,6`; for each `J`, each `F∋J`: `chord-J` term of `∂_tΓ_F` against `Σ_x Γ_{F_out}(σ_out,a_out(x))·Γ_{F_in}(σ_in,a_in(x))` with `F_out=KLFOut`, `F_in=KLFIn`, `σ_out,a_out` read from `cutGlueL(i+1,j+1,x)`, `σ_in,a_in` from `cutGlueR(i+1,j+1,x)`; the list entries are asserted equal to the vertex maps `KLinV, KLoutV, KLglueV`, `σ_in(last)=σ_j`, `σ_in(0..w-1)=σ_i..σ_{j-1}`, `σ_out(glue)=σ_i`; then `W^{-d(n-1)}Σ_{F∋J}` against the `(i+1,j+1)` summand of `treeEqRhsS` (`S=1`, `K` spliced); (c) leaf+chord total against the whole `treeEqRhsS`; `114 s`). Aggregate (max over configurations, absolute):
```
  n  per-F max   per-J max   (c) total max   bijection  partition  #(F,J) checked  list-checks  max|term|
  3  0.00e+00   0.00e+00   1.78e-15        True      True      0      0     0.0e+00
  4  4.44e-15   4.44e-15   1.42e-14        True      True      56384      265536     5.8e+00
  5  7.12e-15   4.90e-15   8.89e-15        True      True      11520      17280     2.4e+01
  6  2.85e-14   3.40e-14   1.35e-13        True      True      142848      62208     1.1e+02
elapsed 114s
```
`n=3` has no diagonal (the `(c)` column is the leaf part only). Controls: `python3 control.py` (a flipped inner glue charge, or a dropped outer chord, fails at `O(1)`; the dropped-chord control is vacuous at `n=4`, `F_out=∅`) and `python3 nonsym.py`; `python3 table.py` (exact rationals for the `W` identity at `W^d=8,3/2`):
```
4 {'inner glue charge flipped': '5.45e+00', 'outer family = FOut with glue chord dropped': '0.00e+00', 'faithful': '4.45e-16'}
5 {'inner glue charge flipped': '1.13e+01', 'outer family = FOut with glue chord dropped': '1.95e+01', 'faithful': '1.80e-15'}
6 {'inner glue charge flipped': '5.25e+01', 'outer family = FOut with glue chord dropped': '3.35e+01', 'faithful': '7.32e-15'}
max |M - M^T| = 0.80
Theta^{(-,+)} == (Theta^{(+,-)})^T (swap = transpose, no symmetry used): True  Theta^{(+,-)} symmetric: False
n=4 (non-symmetric M, W=2): per-F 9.31e-16  per-J 1.16e-16
n=5 (non-symmetric M, W=2): per-F 5.55e-16  per-J 5.72e-17
n=6 (non-symmetric M, W=2): per-F 1.07e-14  per-J 3.89e-16
 n  #diag n(n-3)/2  w-range  (p,q) range: min p, min q, p+q==n+2  W-power identity (Wd=8, 3/2, 0)   |TSP n|  sum_J |{F∋J}|  = sum_J |TSP p||TSP q|
 3    0      0   None   min p=None, min q=None, True   1   - = -
 4    2      2   (2, 2)   min p=3, min q=3, True   3   2 = 2
 5    5      5   (2, 3)   min p=3, min q=3, True   11   15 = 15
 6    9      9   (2, 4)   min p=3, min q=3, True   45   93 = 93
 7   14     14   (2, 5)   min p=3, min q=3, True   197   546 = 546
 8   20     20   (2, 6)   min p=3, min q=3, True   903   3140 = 3140
 9   27     27   (2, 7)   min p=3, min q=3, True   -   - = -
```
No indexing failure and no false identity: no pin repair, no REQ.

### (iii) The written argument
**Pin of target 2 (statement text, not compiled at 1a; `BAReal` and `0≤t<1` are not used by the proof, kept to match `BALeafPairsStmt`).**
```
def BAChordPairsStmt (d : ℕ) : Prop :=
  ∀ (L W : ℕ) [NeZero L] (g κ E : ℝ) (m : ℂ), BAReal d L g κ E m →
    ∀ K : ℝ → LoopIdx (Zd d L) → ℂ, BASplicedFam d L W g E m K →
    ∀ (n : ℕ) [NeZero n], 3 ≤ n → ∀ (σ : Fin n → Bool) (a : Fin n → Zd d L) (t : ℝ), 0 ≤ t → t < 1 →
      (((W : ℂ) ^ d)⁻¹) ^ (n - 1) * ∑ F ∈ TSP n, ∑ J : ↥F, KLgval d L (Nd := BAslot F) (Lf := Fin n) a
          (BACactusValLeafW (BAMsigma d L (BAMB d L g (E : ℂ) m)) t σ) (BAslotLeaf F)
          (Function.update (BACactusValEdgeW (BAMsigma d L (BAMB d L g (E : ℂ) m)) t F σ) (Sum.inl J)
            (BATheta d L g E m t (σ J.1.1) (σ J.1.2) * BATheta d L g E m t (σ J.1.1) (σ J.1.2)))
          (BACactusValSrc F) (BACactusValTgt F)
        = ∑ J ∈ diagonals n, ((W : ℂ) ^ d) * ∑ x : Zd d L,
            K t (LoopIdx.cutGlueL (J.1.val + 1) (J.2.val + 1) x (KLloopOf d L σ a)) *
            K t (LoopIdx.cutGlueR (J.1.val + 1) (J.2.val + 1) x (KLloopOf d L σ a))
```
The left side is the chord part of `W^{-d(n-1)}Σ_F BAGammaDerivRHS` verbatim (`t/T2370:KTreeDeriv.lean:70`); `baChordPairs : ∀ d, BAChordPairsStmt d`.
**Per-`F` cut (the new mathematics).** `F∈TSP n`, `J=(i,j)∈F`, `F_in=KLFIn F J`, `F_out=KLFOut F J` (both `TSP`, `KLFIn_mem_TSP`, `KLFOut_mem_TSP`). The cactus is `KLgval` on the slots `BAslot F = Fin n ⊕ F ⊕ F` (`KCactus.lean:100`). Chord `J` is the bridge `BAslotIn J → BAslotOut J` between the cycle of node `J` and the cycle of `KLnodePar F J`. Slots: `BAslot F_out ⊕ BAslot F_in ≃ BAslot F` (cards `p+2|F_out| + q+2|F_in| = n+2|F|`), by `KLunColP`/`KLunShift` on chords, `KLoutV`/`KLinV` inverses on leaves, and `leaf(glue) ↦ out J`, `leaf(last) ↦ in J`. Edges: `↥F ⊕ BAslot F ≃ Option(Ed_out ⊕ Ed_in)`, `J ↦ none`. Facts to prove (the slot-level analogue of `KLgval_in_eq`/`KLgval_out_eq`, whose leafPar/nodePar correspondences are inline there): (1) `BAslotNode` of the image is the shifted node (root `KLwholeP` ↔ `J` inside, `nodePar J` ↔ `KLwholeP p` outside); (2) `BAslotStart` of the image is `KLinV`/`KLoutV` of the start (`in J`: `j ↦ w=min(j-i,w)`; `out J`: `i ↦ glue=min(i,p-1)`), strictly monotone on each node's keys (`KLcol` is monotone and injective off `(i,j)`), hence by `BAnextSlot_eq_of_above`/`_wrap` (`KCactus.lean:374-382`) `BAnextSlot` commutes with the maps; (3) so `BAMcharge` (`σ` at the start of the next slot) is `σ_in`/`σ_out` at the image of the start, with `σ_in=σ_i..σ_j`, `σ_out=σ_0..σ_i,σ_j..σ_{n-1}`; chords `J'≠J` keep `tΘ^{(σ_{i'},σ_{j'})}` (endpoint charges transport); leaves `v` keep `Θ^{(σ_v,σ_{v+1})}`, and the leaf at the outer glue vertex `i` (next vertex carries `σ_j`) is `Θ^{(σ_i,σ_j)}`, at the inner last vertex `w` (next vertex `0`) is `Θ^{(σ_j,σ_i)}`. Then `KLgval_congr` and `KLgval_split` (`N₂=` inside, `c₀=in J`, `q₀=out J`, `P=Q=Θ^{(σ_i,σ_j)}`, `S=1`, `P S Q=Θ·Θ` by `Matrix.mul_one`) give
`chord-J(F) = Σ_x Γ_{F_out}(σ_out, a_out^x) · Γ_{F_in}(σ_in, a_in^x)`, `a_out^x` = `a` outside, `x` at the glue vertex; `a_in^x` = `a_i..a_{j-1},x`. The inner leaf weight is `Pᵀ=Θ^{(σ_j,σ_i)}` by the swap-transpose identity (C2, no symmetry). The list side: `cutGlueL (i+1)(j+1) x (KLloopOf σ a) = KLloopOf σ_out a_out^x`, `cutGlueR (i+1)(j+1) x (KLloopOf σ a) = KLloopOf σ_in a_in^x` (`take/drop` against `List.ofFn`; the `chord.py` list assertions).
**Sum.** `Σ_{F∈TSP n}Σ_{J:↥F} = Σ_{J∈diagonals n}Σ_{F∈TSP n, J∈F}` (`F ⊆ diagonals n`); the summand depends on `(F_out,F_in)` only, so `KLsum_cut` (`KLCut.lean:1297`) turns it into `Σ_{G∈TSP p}Σ_{H∈TSP q}Σ_x Γ_GΓ_H = Σ_x(Σ_GΓ_G)(Σ_HΓ_H)`. Clause 3 of `BASplicedFam` (`p,q≥3`) gives `K t (cutL)=(W^d)⁻¹^{p-1}Σ_GΓ_G`, `K t (cutR)=(W^d)⁻¹^{q-1}Σ_HΓ_H`; the `W` row of (i) closes the factor. This is target 2.
**Targets 3-5.** (a) `n≥3`, `I=KLloopOf σ a` (WF `I` is of this form, `getD`/`List.ofFn`), clause 3 for all `s`: `HasDerivAt.const_mul`, `HasDerivAt.sum` of `baGamma_hasDerivAt`; unfold `BAGammaDerivRHS` = leaf part + chord part = `baLeafPairs` + target 2 = `Σ_{v}` + `Σ_{J∈diagonals}`, and `treeEqRhsS` at `S=1` (`Σ_{a,b}K·1_{ab}·K=Σ_x`) is the sum over `(k,l)`, `1≤k<l≤n`, which is the disjoint union of the `n` leaf pairs and the `n(n-3)/2` diagonal pairs (counting row). `n=2`: copy `BAKSolve_rhs_two`, `_two_hasDerivAt` (stem `KTreeRep_`). (b) `n≥3`: `BACactusVal_sum_zero_BAMLoop` (`KCactus.lean:736`); `n=2`: `baKsolveLe3_holds` at `t=0∈Ico 0 1` (`K₃ 0 I = BAMLoop I`) and clause 2 of both. (c) `BAKcac_spliced` clause 1. Target 4: witness `BAKcac`, `(Kn2sol)` clause is `BAKcac_spliced.2.1`. Target 5: `baKsolve` → `BAKsol_isKLoopS` (`KSolve.lean:606`); `baK_unique` (`:568`) with `baKcac_isKLoopS` gives `BAKsol t I = BAKcac t I` for WF `I`, length `≥2`; clause 3 at `KLloopOf σ a`.
**Target 7.** `scanPremises` (`Test/Axioms.lean`, `elab "#assert_rbm_axioms"`) counts a premise as proved when a theorem's conclusion head is it; `baKsolve : ∀ d, BAKsolve d` has head `BAKsolve`. The line to delete is `Test/Axioms.lean:141`. Not compiled at 1a; the pre-check is a 1b step.

### (iv) C5 and the plan against the stop line `2000` (`wc -l RBM3D/BA/KTreeRep.lean` at each section commit)
Q4: K05a `612` (`t/T2370` `wc -l`) + K05b central `1300` = `1912` against `3.3k`; low `1512`, high `2412`: **not crossed**, even at the stop line (`2612`). The gross sum of the rows below, before calibrating to the K05a outcome (`612` against its preflight `≈1265`), is `1620`; I take central `1300`.
| § | content | central / cumulative |
|---|---|---|
| 0 | header, pins `BATreeRep` (verbatim), `BAChordPairsStmt` | 70 / 70 |
| 1 | vertex maps `σ_in,a_in,σ_out,a_out`; `cutGlueL/R (i+1)(j+1)` list identities | 180 / 250 (commit 1) |
| 2 | slot bijection `BAslot F_out ⊕ BAslot F_in ≃ BAslot F`, node correspondences | 170 / 420 |
| 3 | `BAnextSlot`/`BAMcharge` commute with the maps (in, out) | 200 / 620 (commit 2) |
| 4 | per-`F` cut lemma (`KLgval_congr`, `KLgval_split`, swap-transpose) | 160 / 780 |
| 5 | `KLsum_cut`, `W` powers, `baChordPairs` | 120 / 900 (commit 3) |
| 6 | pair partition, `n=2` copy, `baKcac_isKLoopS` | 270 / 1170 (commit 4) |
| 7 | `baKsolve`, `baTreeRep` | 50 / 1220 |
| 8 | instances (target 6: per-`F` cut at `F={(0,2)}`, target 2, `baKcac_isKLoopS`, `baTreeRep` at `P`, `n=4`), registry | 80 / 1300 (commit 5) |
Risks: §3 (outer `KLcol` is not injective; keys of the parent node at `j` and `i`), §1/§2 (`Fin (n-KLwIn J+1)` casts and the `Option` leaf types of `KLgval_split`); at any boundary `>2000`: commit, stop, RETURN.

### Verdicts
Target 1 (pins `BATreeRep`, `BAChordPairsStmt`): PASS. Target 2 (chord pairs): PASS. Target 3 (`baKcac_isKLoopS`): PASS. Target 4 (`baKsolve`): PASS. Target 5 (`baTreeRep`): PASS. Target 6 (instances): PASS (nonvacuous data above). Target 7 (registry): PASS at the level of reading the scan. No `FAIL`, no `BLOCKED`. Paper-delta candidate `T2374a`: none arises; `BATreeRep` stays at `3 ≤ n` (supervisor 0350 Q1). **Overall: PASS.**

### (a′) Preflight corrections — Sat Oct 10 08:41:37 UTC 2026
One plan item of (a) is not usable as written; no verdict changes. (a)(iii) "Targets 3-5 (b)" takes the `n=2` derivative and value from `baKsolveLe3_holds` (`BA/KSolve.lean:478`), which carries `Λ, κ > 0`, `3 ≤ L`, `0 < g ≤ Λ`; target 3 as pinned (ticket) has `BAReal` only. The `n=2` pieces are copies of the private `BAKSolve_rhs_two`, `BAKSolve_two_hasDerivAt`, `BAKSolve_zero` (`BA/KSolve.lean:175, 359, 459`), stem `KTreeRep_` (the row "`(Kn2sol)` at `n=2`" of (a)(i) already allows this).

## (b) Script output — Sat Oct 10 08:41:37 UTC 2026
Branch `t/T2374` (worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2374`), base `main` e004671 (T2370 merged as 06fd533). Files: `RBM3D/BA/KTreeRep.lean` (new), `RBM3D/Test/Axioms.lean` (one line deleted). Scripts (not in the repository): `S=/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/966b45d4-be15-4db2-88b3-45a074bfecd5/scratchpad/T2374`: `extract.py`, `pindiff.py`, `names.lean`, `precheck.lean`, `check_aud.lean`.

**Q4 (C5) and section commits (stop line 2000)** — `git log` + `git show <h>:RBM3D/BA/KTreeRep.lean | wc -l`; `wc -l` of K05a on `main`:
```
ee756ad 2026-10-10 08:10:54 UTC KTreeRep.lean lines=871
10879a4 2026-10-10 08:22:06 UTC KTreeRep.lean lines=1368
489bcc5 2026-10-10 08:30:42 UTC KTreeRep.lean lines=1717
edaa2ec 2026-10-10 08:35:07 UTC KTreeRep.lean lines=1763
K05a      612 + K05b     1763 = 2375   (2051 Q4 line for K05: 3.3k; (a)(iv) central 1300 -> 1912)
```
Not crossed. `git diff main...t/T2374 --stat`: 2 files changed, 1763 insertions(+), 1 deletion(-) (only the two sole writable files).

**Build, axioms** (`date -u` at run: Sat Oct 10 08:41:37 UTC 2026):
```
$ lake build RBM3D.BA.KTreeRep 2>&1 | tail -2
Note: This linter can be disabled with `set_option linter.style.longLine false`
Build completed successfully (3743 jobs).
$ lake env lean RBM3D/BA/KTreeRep.lean; echo exit=$?   (no warnings, no errors)
exit=0
$ (temporary uncommitted `import RBM3D.BA.KTreeRep` after the last import of RBM3D.lean) lake build   [08:35:35 UTC]
non-vacuity certificates: 0 of 123 premises in the two ledgers; the rest are not known to be satisfiable (`RBM3D/Test/InterfaceShape.lean` says what each would take)
Build completed successfully (4189 jobs).        (RBM3D.lean restored; `git status --short` empty)
$ lake env lean $S/ax.lean      (#print axioms)
'RBM.BA.baChordPairs' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baKcac_isKLoopS' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baKsolve' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baTreeRep' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BATreeRep' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BAChordPairsStmt' depends on axioms: [propext, Classical.choice, Quot.sound]
```
`grep -c "sorry\|admit\|native_decide" RBM3D/BA/KTreeRep.lean` = 0; no `axiom` declaration; 6 public declarations (`grep -nE "^(noncomputable )?(theorem|def|lemma|abbrev) " RBM3D/BA/KTreeRep.lean`: lines 48, 61, 1396, 1674, 1699, 1709), every other name is `private` with the stem `KTreeRep_`.

**Pins and target statements, extracted by script** (`python3 $S/pindiff.py`, `$S/extract.py`):
```
BATreeRep vs docs/tickets/checks/T2374-check.lean Part 1: token streams identical = True (200 tokens)
BAChordPairsStmt vs docs/reports/T2374-prove.md lines 70-81: token streams identical = True (228 tokens)
--- BATreeRep (RBM3D/BA/KTreeRep.lean:48)
def BATreeRep (d : ℕ)
    (Γ : ∀ (L n : ℕ) [NeZero L] [NeZero n], (Bool → Matrix (Zd d L) (Zd d L) ℂ) → ℝ →
      Finset (Fin n × Fin n) → (Fin n → Bool) → (Fin n → Zd d L) → ℂ) : Prop :=
  ∀ (Λ κ : ℝ), 0 < Λ → 0 < κ → ∀ (L : ℕ) (hL : 3 ≤ L) (W : ℕ) (g : ℝ), 0 < g → g ≤ Λ → ∀ (E : ℝ) (m : ℂ),
    haveI : NeZero L := ⟨by omega⟩
    BAReal d L g κ E m → ∀ t ∈ Set.Ico (0 : ℝ) 1, ∀ (n : ℕ) [NeZero n], 3 ≤ n → ∀ (σ : Fin n → Bool) (a : Fin n → Zd d L),
      BAKsol d L W (BAMsigma d L (BAMB d L g (E : ℂ) m)) (PropSpin m) t (KLloopOf d L σ a)
        = (((W : ℂ) ^ d)⁻¹) ^ (n - 1) *
            ∑ F ∈ TSP n, Γ L n (BAMsigma d L (BAMB d L g (E : ℂ) m)) t F σ a
--- BAChordPairsStmt (RBM3D/BA/KTreeRep.lean:61)
def BAChordPairsStmt (d : ℕ) : Prop :=
  ∀ (L W : ℕ) [NeZero L] (g κ E : ℝ) (m : ℂ), BAReal d L g κ E m →
    ∀ K : ℝ → LoopIdx (Zd d L) → ℂ, BASplicedFam d L W g E m K →
    ∀ (n : ℕ) [NeZero n], 3 ≤ n → ∀ (σ : Fin n → Bool) (a : Fin n → Zd d L) (t : ℝ), 0 ≤ t → t < 1 →
      (((W : ℂ) ^ d)⁻¹) ^ (n - 1) * ∑ F ∈ TSP n, ∑ J : ↥F, KLgval d L (Nd := BAslot F) (Lf := Fin n) a
          (BACactusValLeafW (BAMsigma d L (BAMB d L g (E : ℂ) m)) t σ) (BAslotLeaf F)
          (Function.update (BACactusValEdgeW (BAMsigma d L (BAMB d L g (E : ℂ) m)) t F σ) (Sum.inl J)
            (BATheta d L g E m t (σ J.1.1) (σ J.1.2) * BATheta d L g E m t (σ J.1.1) (σ J.1.2)))
          (BACactusValSrc F) (BACactusValTgt F)
        = ∑ J ∈ diagonals n, ((W : ℂ) ^ d) * ∑ x : Zd d L,
            K t (LoopIdx.cutGlueL (J.1.val + 1) (J.2.val + 1) x (KLloopOf d L σ a)) *
            K t (LoopIdx.cutGlueR (J.1.val + 1) (J.2.val + 1) x (KLloopOf d L σ a))
--- baChordPairs (RBM3D/BA/KTreeRep.lean:1396)
theorem baChordPairs (d : ℕ) : BAChordPairsStmt d := by
--- baKcac_isKLoopS (RBM3D/BA/KTreeRep.lean:1674)
theorem baKcac_isKLoopS {d L W : ℕ} [NeZero L] {g κ E : ℝ} {m : ℂ} (hr : BAReal d L g κ E m) :
    IsKLoopS d L W (1 : Matrix (Zd d L) (Zd d L) ℂ) (PropSpin m)
      (BAMLoop d L W (BAMsigma d L (BAMB d L g (E : ℂ) m))) (Set.Ico (0 : ℝ) 1) (BAKcac d L W g E m) := by
--- baKsolve (RBM3D/BA/KTreeRep.lean:1699)
theorem baKsolve : ∀ d, BAKsolve d := by
--- baTreeRep (RBM3D/BA/KTreeRep.lean:1709)
theorem baTreeRep (d : ℕ) : BATreeRep d (@BAGamma d) := by
```
Auditor checks (ticket): `lake env lean docs/tickets/checks/T2374-check.lean` on the branch: exit 0 (`$S/check_out.txt`). The same file plus `import RBM3D.BA.KTreeRep` and
`example : @RBM.BA.BATreeRep = @RBM.BA.T2374Check.BATreeRep := rfl`, `example : ∀ d, RBM.BA.BAKsolve d := RBM.BA.baKsolve`, `example : ∀ d, RBM.BA.BATreeRep d (@RBM.BA.BAGamma d) := RBM.BA.baTreeRep`: exit 0 (`$S/check_aud_out.txt`).

**Compiled nonempty instances** (target 6; `sed`/`python3` extraction of `namespace KTreeRepInst` of the file, docstrings dropped; datum in the file docstring: flow point `P` of `(d,L)=(3,4)`, `W=2`, `t=1/2`, `n=4`, `F={(0,2)}`, `J=(0,2)`; no hypothesis left open):
```lean
namespace KTreeRepInst

open RBM.BA.MFixedPointInst

private theorem KTreeRep_isTSP_F02 :
    KLIsTSP ({((0 : Fin 4), (2 : Fin 4))} : Finset (Fin 4 × Fin 4)) :=
  KLisTSP_of_mem_TSP (by rw [TSP_four]; simp)

example := KTreeRep_cut (d := 3) (L := 4) (F := {((0 : Fin 4), (2 : Fin 4))}) (J := ((0 : Fin 4), (2 : Fin 4)))
  KTreeRep_isTSP_F02 (by norm_num) (Finset.mem_singleton_self _) (BAMsigma 3 4 (BAMB 3 4 P.g0 (P.E : ℂ) P.m0)) (1 / 2)
  ![true, true, false, true] ![![0, 0, 0], ![1, 0, 0], ![2, 0, 0], ![3, 0, 0]]

example :=
  baChordPairs 3 4 2 P.g0 P.m0.im P.E P.m0 P.real (BAKcac 3 4 2 P.g0 P.E P.m0) BAKcac_spliced 4 (by norm_num)
    ![true, true, false, true] ![![0, 0, 0], ![1, 0, 0], ![2, 0, 0], ![3, 0, 0]] (1 / 2) (by norm_num) (by norm_num)

example : IsKLoopS 3 4 2 (1 : Matrix (Zd 3 4) (Zd 3 4) ℂ) (PropSpin P.m0)
    (BAMLoop 3 4 2 (BAMsigma 3 4 (BAMB 3 4 P.g0 (P.E : ℂ) P.m0))) (Set.Ico (0 : ℝ) 1) (BAKcac 3 4 2 P.g0 P.E P.m0) :=
  baKcac_isKLoopS P.real

example := baKsolve 3 10 P.m0.im (by norm_num) P.real.1.1 4 (by norm_num) 2 P.g0 P.g0_pos P.g0_le P.E P.m0 P.real

example :=
  baTreeRep 3 10 P.m0.im (by norm_num) P.real.1.1 4 (by norm_num) 2 P.g0 P.g0_pos P.g0_le P.E P.m0 P.real (1 / 2)
    ⟨by norm_num, by norm_num⟩ 4 (by norm_num) ![true, true, false, true]
    ![![0, 0, 0], ![1, 0, 0], ![2, 0, 0], ![3, 0, 0]]

end KTreeRepInst
```

**Registry pre-check** (target 7): `git diff main...t/T2374 -- RBM3D/Test/Axioms.lean | grep "^[-+]"`:
```
--- a/RBM3D/Test/Axioms.lean
+++ b/RBM3D/Test/Axioms.lean
-   `RBM.BA.BAKsolve, -- existence of the BA `𝒦` on `[0,1)` with `(Kn2sol)` (`1_2:1175`), hypothesis of `BAKsol_isKLoopS`, `BAKsol_rotate`, `BAKsol_tr
$ lake env lean $S/precheck.lean     # import RBM3D; import RBM3D.BA.KTreeRep; #assert_rbm_axioms   [49.368 s total]
registry: 2 borrowed + 121 owed + 109 structural + 7 refuted + 14 superseded; 125 registered premise(s) carry nothing yet: [...]
exit code: 0      (`grep -c BAKsolve $S/precheck_out.txt` = 0: no unregistered premise)
```
On `main` 0aafa2c (T2373 merged after the base) line 141 of `Test/Axioms.lean` is still the `RBM.BA.BAKsolve` line (`git show main:RBM3D/Test/Axioms.lean | grep -n "RBM.BA.BAKsolve,"`): the deletion re-applies (H23 (b)).

**Name clash** (`grep -rnE "^(private )?(noncomputable )?(theorem|def|lemma|abbrev|structure|instance) (RBM\.BA\.)?(BATreeRep|BAChordPairsStmt|baChordPairs|baKcac_isKLoopS|baKsolve|baTreeRep)( |$)" RBM3D RBM3D.lean` on the branch): hits only in `RBM3D/BA/KTreeRep.lean` (lines 48, 61, 1396, 1674, 1699, 1709); `grep -rnE "(theorem|def|lemma) KTreeRep" RBM3D` outside the file: 0 hits; `git grep -nE "(theorem|def|lemma|abbrev) (RBM\.BA\.)?(BATreeRep|BAChordPairsStmt|baChordPairs|baKcac_isKLoopS|baKsolve|baTreeRep|KTreeRep)" main -- RBM3D` on `main` 0aafa2c: one hit, `BA/KSolve.lean:478 baKsolveLe3_holds` (prefix match, a different name). **Ports:** nothing from RBM1D/RBM2D (not read; no `git -C ../RBM*` diff-stat applies). Copies inside RBM3D at `main` e004671, stem `KTreeRep_`: `Loop/KLCut.lean:394-448, 488-523, 537-571, 637-742, 780-836, 847-905` (private cut helpers, `KLgval_in_eq`/`KLgval_out_eq` proof bodies), `BA/KSolve.lean:169-191, 359-376, 459-467` (`n=2`), `BA/KTreeDeriv.lean:112-122` (`Θ`-swap, now for general `M`).

**Narrative.**
1. All seven targets are delivered; no obstruction, no pin repair, no REQ, no weakened target, no added hypothesis; `BAKsolve` and `BATreeRep` are proved, not assumed.
2. Target 2, the new mathematics (sections 1-5, lines 74-1369): for `F ∈ TSP n`, `J ∈ F` the slots `BAslot F_out ⊕ BAslot F_in ≃ BAslot F` (`KTreeRep_eN`) are built from two maps `ψ` (glue leaf ↦ `BAslotOut J`, leaves `KLoutV⁻¹`, chords `KLshiftOut⁻¹`) and `φ` (last leaf ↦ `BAslotIn J`, leaves `+i`, chords `KLshiftIn⁻¹`). For each, the node map `node(F_·, s) = KLshift·(node(F, φ s))` (the six parent identities of `KLgval_in_eq/out_eq`, copied as lemmas), the start map `start(F_·, s) = KLinV/KLoutV (start(F, φ s))`, and closure under "same node" are proved; injectivity of `ψ`, `φ` comes from `BAslot_start_inj` of the pieces.
3. `KTreeRep_next_map` (section 2) transports `BAnextSlot` along any such map from nodes and starts alone (`BAnextSlot_eq_of_above/_wrap`); with it `φ`, `ψ` commute with the cycles and the `M`-edge charges agree (`KTreeRep_charge_in/out`): the preflight risk "slot-level `BAnextSlot` commutation" is this lemma. The edge bijection `KTreeRep_Eb` is explicit (five shapes).
4. `KTreeRep_cut` = `KLgval_split` (`S=1`, `P=Q=Θ^{(σ_i,σ_j)}`) + three `KLgval_congr`; the reversed inner leaf is `Θ^{(σ_j,σ_i)} = Θᵀ` (`KTreeRep_Theta_swap`, general `M`): C2 is not hit, no symmetry of `M` is used. `baChordPairs`: `Finset.sum_comm'`, `KLsum_cut`, `KTreeRep_wpow` (`W^d W^{-d(p-1)} W^{-d(q-1)} = W^{-d(n-1)}`, also at `W^d=0`), clause 3 of `BASplicedFam` at `p, q ≥ 3` through the list identities `KTreeRep_cutGlueL_eq/R_eq`.
5. Target 3: `n ≥ 3`: `baGamma_hasDerivAt` + `baLeafPairs` + `baChordPairs` + `KTreeRep_pairs` (pair partition of `treeEqRhsS`: `n` leaf pairs plus `n(n-3)/2` diagonal pairs); `n=2`: see (a′); `t=0`: `BACactusVal_sum_zero_BAMLoop` (`n ≥ 3`), `Θ_0=1` (`n=2`); length 1: clause 1. Targets 4, 5 as planned in (a)(iii): witness `BAKcac`; `baTreeRep` = `BAKsol_isKLoopS` + `baK_unique` + clause 3.
6. Used hypotheses: `baChordPairs` does not use `BAReal`, `0 ≤ t < 1` (kept for the `BALeafPairsStmt` shape, as (a)); `KTreeRep_cut` needs `KLIsTSP F`, `2 ≤ n`, `J ∈ F` only. Three declarations (`KTreeRep_cut`, `baChordPairs`, `baKcac_isKLoopS`, file lines 1278, 1391, 1670) carry `set_option synthInstance.maxSize 512 in`: `DecidableEq (BAslot F_out ⊕ BAslot F_in)` exceeds the default instance size.
7. Size: 1763 lines against (a)(iv) central 1300, high 1800; sections 3-4 (inner/outer node and slot facts, lines 299-872) and 5 (cut, lines 873-1369) are 1071 of them.

## (c) Verified Mathlib names (`lake env lean $S/names.lean`, 31 `#check` lines, all elaborate; `names.lean` imports `RBM3D.BA.KTreeRep` since `import Mathlib` is not built in `.lake/packages`)
- `Finset.sum_finset_product (r s t) (h : ∀ p, p ∈ r ↔ p.1 ∈ s ∧ p.2 ∈ t p.1) {f} : ∑ p ∈ r, f p = ∑ c ∈ s, ∑ a ∈ t c, f (c, a)`
- `Finset.sum_nbij' (i j) (hi hj left_inv right_inv h) : ∑ x ∈ s, f x = ∑ x ∈ t, g x`
- `Finset.sum_comm' (h : ∀ x y, x ∈ s ∧ y ∈ t x ↔ x ∈ s' y ∧ y ∈ t') : ∑ x ∈ s, ∑ y ∈ t x, f x y = ∑ y ∈ t', ∑ x ∈ s' y, f x y`
- `Finset.sum_mul_sum (s t f g) : (∑ i ∈ s, f i) * ∑ j ∈ t, g j = ∑ i ∈ s, ∑ j ∈ t, f i * g j`
- `Finset.sum_coe_sort (s) (f) : ∑ i : ↥s, f ↑i = ∑ i ∈ s, f i`; `Finset.sum_eq_single (a) (h₀ h₁)`; `Finset.sum_filter (p f)`
- `Equiv.ofBijective (f) (Function.Bijective f) : α ≃ β`; `Equiv.sumCompl (p) : {a // p a} ⊕ {a // ¬p a} ≃ α`; `Equiv.sumComm (α β)`
- `Equiv.apply_symm_apply (e) (x) : e (e.symm x) = x`; `Equiv.symm_apply_apply (e) (x) : e.symm (e x) = x`
- `Function.Injective.sumElim (hf hg) (∀ a b, f a ≠ g b) : Injective (Sum.elim f g)`
- `Fin.val_add (a b : Fin n) : ↑(a + b) = (↑a + ↑b) % n`; `Fin.val_one' (n) [NeZero n] : ↑1 = 1 % n`; `Fin.last_add_one (n) : Fin.last n + 1 = 0`
- `Function.update_self (a) (v) (f) : update f a v a = v`; `Function.update_of_ne (h : a ≠ a') (v) (f) : update f a' v a = f a`
- `Matrix.transpose_nonsing_inv (A) : A⁻¹.transpose = A.transpose⁻¹`; `Matrix.nonsing_inv_eq_ringInverse (A) : A⁻¹ = Ring.inverse A`
- `List.ext_getElem`; `List.getElem_append_left (h : i < as.length)`; `List.getElem_append_right (h₁ : as.length ≤ i)`
- `HasDerivAt.fun_sum`; `HasDerivAt.const_mul (c)`; `HasDerivAt.mul_const (d)`; `Fintype.sum_prod_type (f)`
- `Nat.mod_eq_of_lt : a < b → a % b = a`; `Nat.mod_self`; `ite_eq_right_iff`; `mul_inv_cancel₀ : a ≠ 0 → a * a⁻¹ = 1`
- Verified absent (`grep -rn "Option (α ⊕ β)\|optionSum\|sumOption" Mathlib/Logic/Equiv Mathlib/Data/Sum`, only `Equiv.sumSumSumComm` found): an equivalence `Option α ⊕ β ≃ Option (α ⊕ β)`; the edge bijection is explicit instead.

## (d) Open issues and paper-delta candidates
- Paper-delta candidates: none (`T2374a` not needed). Target 2 and `KTreeRep_cut` are internal identities; `BATreeRep` stays at `3 ≤ n` (supervisor 0350 Q1, D634). The Lean statements equal the pins (token diffs above).
- Hub steps at merge: add `import RBM3D.BA.KTreeRep` after the last import of `RBM3D.lean` (a temporary import there gave `lake build` success, above); re-apply the one-line deletion in `Test/Axioms.lean` against the `main` of merge time.
- `KTreeRep_cut`, `KTreeRep_ψ`, `KTreeRep_φ` and their node/start facts are `private`; a later row that needs the per-tree cut with other weights would need them public (a separate ticket; this file is the sole writable file here).
- No finding on old-mode documents; no REQ candidate (all identities of (a)(ii) hold in Lean at the stated generality).
