Auditor model: claude-opus-5-5
# T2370 (BA-K05a) — stage-1a design-gate audit — Sat Oct 10 04:30:31 UTC 2026

Scope: section (a) of `docs/reports/T2370-prove.md` (77 lines) against the ticket's "Stage 1a, design gate" deliverables
(i)–(iii) and its binding stop lines. `S=…/scratchpad/T2370`; auditor copies and scripts in `$S/audit/`.

## 0. Inputs
```
$ git log --oneline main..t/T2370 | wc -l ; git diff --stat main...t/T2370      # no Lean on the branch (design gate)
       0
$ for f in mirror mgraph kode; do cmp ../T2367/$f.py audit/$f.py && echo "same $f"; done
same mirror
same mgraph
same kode
```

## 1. Deliverable (ii): C3 per-term numerics — rerun of the preflight's script
```
$ cd $S/audit; time python3 c3.py 6 > c3_out.txt; python3 summ.py
n  #TSP  (a)abs      (a)rel     (b)leaf    (b)wrap    (c)total   list-identity checks
3     1  2.10e-12  3.08e-13  1.78e-15  1.86e-15  7.11e-15   39360
4     3  3.90e-11  1.15e-12  2.84e-14  2.14e-14  9.95e-14   483840
5    11  1.21e-10  2.66e-12  7.11e-15  4.44e-15  8.88e-15   17280
6    45  9.07e-09  5.36e-11  4.10e-14  7.11e-14  1.85e-13   41472
matrix-level max over 9 configs: dTheta=4.4e-13 resolvent=4.4e-16 commute=4.4e-16 symm=3.3e-16 swap=4.4e-16 dTT=3.0e-13
MAX over all: (a) abs 9.07e-09 rel 5.36e-11  (b) leaf 4.10e-14   (b) wrap 7.11e-14   (c) total 1.85e-13   elapsed 432s
python3 c3.py 6 > c3_out.txt  424.82s user 2.14s system 98% cpu 7:12.62 total
$ diff <(grep -v elapsed audit/c3_out.txt | sed 's/([0-9]*s)//') <(grep -v elapsed c3_out.txt | sed 's/([0-9]*s)//')
54a55
> python3 c3.py 6  423.85s user 0.80s system 99% cpu 7:04.92 total
```
Reproduced exactly (the only difference is a timing line the preflight appended to its own file). Data = the ticket's
B8 grid (`d=1, W=1, q∈{4,5}, E=0.3, g∈{0.2,0.5}, t∈{0.3,0.7}`) plus `(4,0.5,0.3,0.7,W=2)`; `n=3..6`, every `σ`, every
`F ∈ TSP n`; (b) all `a` at `n≤4`, 6 random `a` at `n=5,6`. **(b) max 7.1e-14 ≤ 1e-12 ≤ 1e-10: stop line not hit.**
(a) max abs 9.07e-9 ≤ 1e-8 (9-point stencil, see §2 for the 5-point check).

Mirror fidelity (read against Lean): `cutGlueL/R` = `TreeRep.lean:75-82` (1-indexed `take`/`drop`); `KLloopOf` =
`KLTree.lean:149-150`; `Mss[a,b] = Mm[s1][b,a]·Mm[s2][a,b]` = `BAMss` (`MFixedPoint.lean:511`), `Mm[False] = Mᴴ` =
`BAMsigma`; `Θ = inv(1 − tQ)` = `PropThetaQ` (`Ring.inverse`, invertible at `0≤t<1` by `BATheta_isUnit`); leaf
`v ↦ Θ^{(σ_v,σ_{v+1 mod n})}`, chord `tΘ^{(σ_i,σ_j)}` from `in J` to `out J`, `M`-edge charge `σ(start(next s))` =
`BACactusValLeafW/EdgeW/Src/Tgt`, `BAMcharge`, `BAslotStart` (`KCactus.lean:120-123, 434-470`); `treeEqRhsS` at `S=1`
(`KLTree.lean:809-813`) = `W^d Σ_{k<l} Σ_x K(cutL x)K(cutR x)`; closed form = `BASplicedFam` clause 2.

## 2. Auditor's independent check (written from the pin text of the check file; reuses only `mirror.cactus_val`)
`aud.py`: pin LHS of `BALeafPairsStmt` per `v` (explicit `Σ_b P(a_v,b)Γ_F(update a v b)`) vs the pin RHS summand with its
own `if v.val+1<n` pair selection, a `BASplicedFam` family (length 1 `PropSpin`, 2 closed form, ≥3 cactus sum); (a) by a
**5-point** stencil `h=1e-3` against `BAGammaDerivRHS` (leaf part + chord part with `Sum.inl J ↦ Θ·Θ`); includes
`t = 0`, `W^d = 3^2 = 9`, `q = 3`, `E < 0`; negative control: the wrap leaf against the wrong pair `(1,2)`.
```
$ time python3 aud.py
BA q=3 g=0.7 E=-0.2 t=0.0 W^d=3^2: (b) max|pin LHS_v - pin RHS_v| = 8.74e-19   (a) 5pt FD abs 0.00e+00 rel 0.00e+00   neg.control wrap-vs-(1,2) = 7.91e-03
BA q=3 g=0.7 E=-0.2 t=0.5 W^d=3^2: (b) max|pin LHS_v - pin RHS_v| = 3.48e-18   (a) 5pt FD abs 6.07e-09 rel 1.53e-09   neg.control wrap-vs-(1,2) = 2.58e-02
BA q=4 g=0.4 E=0.3 t=0.9 W^d=1^1: (b) max|pin LHS_v - pin RHS_v| = 1.59e-12   (a) 5pt FD abs 3.89e-03 rel 6.46e-07   neg.control wrap-vs-(1,2) = 4.73e+02
BA q=5 g=0.5 E=0.3 t=0.3 W^d=2^1: (b) max|pin LHS_v - pin RHS_v| = 6.94e-18   (a) 5pt FD abs 1.39e-10 rel 1.18e-10   neg.control wrap-vs-(1,2) = 5.75e-02
NON-symmetric M (control, expect (b) >> 0): (b) max|pin LHS_v - pin RHS_v| = 6.94e-18   (a) 5pt FD abs 6.31e-13 rel 6.31e-13   neg.control wrap-vs-(1,2) = 1.16e-01
MAX over BA configs: (b) 1.59e-12  (a) 3.89e-03
python3 aud.py  62.71s user 0.70s system 98% cpu 1:04.58 total
```
The `t=0.9` row (outside the B8 grid, `|values| ~ 5e2–7e3`) is relative `≤ 3e-15` in (b); its (a) entry is FD truncation:
```
$ python3 aud2.py
q=4 g=0.4 t=0.9 n=3: h=1.0e-03: max|FD-RHS|=9.49e-06 (|RHS|=9.2e+01)  h=2.5e-04: max|FD-RHS|=3.71e-08 (|RHS|=9.2e+01)
q=4 g=0.4 t=0.9 n=4: h=1.0e-03: max|FD-RHS|=3.89e-03 (|RHS|=7.3e+03)  h=2.5e-04: max|FD-RHS|=1.52e-05 (|RHS|=7.3e+03)
generic M: |Q(s2,s1) - Q(s1,s2)^T| = 2.4e-17; |Theta'Q' - (Theta Q)^T| = 1.1e-16; but |Q(s2,s1) - Q(s1,s2)| = 2.7e-01
```
Error ratio `256 = 4^4` under `h → h/4`: the 5-point `O(h^4)` truncation, not an identity defect. The negative controls
(wrong pair) are `≥ 7.9e-3`, so (b) is sensitive to indexing. The "non-symmetric `M`" control did **not** break (b): see O1.

## 3. Deliverable (i): the written argument (targets 2, 3; and target 4's definition)
Checked line by line against the pins (check file Part 1) and the merged signatures
(`BATheta_hasDerivAt` `KBase.lean:341`: `0≤t`, `t<1`, `BAReal`, two-sided `HasDerivAt`, derivative `(ΘQΘ) a b`;
`BATheta_resolvent` `:330`; `BATheta_swap` `:350` (no hypotheses); `BATheta_isSymm` `:371`; `BAMB_symm` `Ward.lean:83`;
`KLgval` `KLCut.lean:58`; the band twin `KLhasDerivAt_treeValW` `KLCut.lean:178` is the same product-rule shape).
- Target 2: product rule over `Σ_b ∏_leaves ∏_{↥F ⊕ BAslot F}`; leaf `ΘQΘ` row rewrite to `Σ_b (ΘQ)(a_v,b)Γ_F(update a v b)`
  matches the pin's leaf part; chord `∂_s(s•Θ_s) = Θ + tΘQΘ = Θ·Θ` (either resolvent conjunct) matches the pin's
  `Function.update … (Sum.inl J) (Θ*Θ)`; `M`-edges constant ⇒ zero-weight terms vanish. Hypotheses used ⊆ the pin's. OK.
- Target 3: leaf `v ≤ n−2`: `cutGlueL (v+1)(v+2) x I = ⟨σ, update a v x⟩`, `cutGlueR = ⟨[σ_v,σ_{v+1}],[a_v,x]⟩` (verified
  from `TreeRep.lean:75-82` by hand and by 581 952 asserted instances in `c3.py`); `W^d·(W^d)⁻¹ = 1`, and the case
  `W^d = 0` gives `0 = 0` since `n−1 ≥ 2` (Lean `0⁻¹ = 0`). Wrap `(1,n)`: `cutGlueL = ⟨[σ_0,σ_{n−1}],[x,a_{n−1}]⟩`,
  `cutGlueR = ⟨σ, update a (n−1) x⟩`; reversal closed via `P' (a_{n−1},x) = P(x,a_{n−1})`. Correct. No extra hypothesis.
- Target 4: `BAKcac` by cases (non-WF ↦ 0; length 1, 2, ≥3 with `getD` and a length transport at `KLloopOf`) meets all
  three `BASplicedFam` clauses as pinned; same shape as the merged `KLgen`. OK.
- Hypotheses/vacuity: none beyond the pins; no structure field; deps are merged (`KCactus`, `KBase`, `Ward`, `KLTree`,
  `TreeRep`, `KLCut`). Lean instance data: `P : FlowPt 4 10` (`MFixedPoint.lean:893`) carries `P.real : BAReal 3 4 …`
  (`:883`), so `BAReal` is dischargeable at the planned instance; `n = 3`, `F = ∅`, `0 ≤ 1/2 < 1`, family `BAKcac`.
- Paper deltas: `T2370a` (no `0 < W`) proposed; `n ≥ 3` vs `A:593` `n ≥ 4` is already D634 (`paper-deltas.md:1593`);
  `tΘ` for `tS^{(B)}Θ` (`A:561`, `S^{(B)} = I`) is D633 (cited in `KCactus.lean:455`). Coverage complete for (a).

## 4. Deliverable (iii): plan against the stop line 2000
Sections 0–7, central ≈ 1265 (low 800, high 1600), section commits at ≈ 575 / 895 / 1265, `wc -l` rule restated.
Calibration: band blueprint `Loop/KLTreeDeriv.lean` 1153 lines covers the leaf + chord + diagonal parts; K05a is the leaf
part plus `BAKcac`; the generic product rule for `KLgval` is a ~35-line generalisation of `KLhasDerivAt_treeValW`.
High estimate 1600 < 2000. Plan acceptable.

## 5. Stop lines
| stop line | measured | hit? |
|---|---|---|
| C3 (b) > 1e-10 → no 1b | 7.1e-14 (rerun), 1.6e-12 abs / 3e-15 rel at an extra `t=0.9` point outside the grid | no |
| extra hypothesis beyond the pins → stop at 1a | none needed (§3) | no |
| false identity on the target domain → REQ | none | no |
| size > 2000 at a section boundary | plan high 1600 (applies in 1b) | n/a at 1a |

## 6. Observations (no RETURN)
- O1 (simplification for 1b): the wrap reversal does not need `BAMB_symm`/`BATheta_isSymm`/`BATheta_swap`.
  `BAMss M s₂ s₁ = (BAMss M s₁ s₂)ᵀ` holds for every `M` straight from `BAMss`'s definition, hence
  `Θ^{(s₂,s₁)} = (Θ^{(s₁,s₂)})ᵀ` and `(Θ'Q')(a,x) = (QΘ)(x,a) = (ΘQ)(x,a)` using only `ΘQ = QΘ` (see `aud2.py`, and the
  non-symmetric control in §2). The preflight's C2 route is also valid at BA data; either is fine.
- O2: (a) used a 9-point stencil where the ticket names complex-step/5-point; §2 repeats (a) with a 5-point stencil
  (`≤ 6.1e-9` on B8-type data at `h = 1e-3`). No effect on the verdict.
- O3: the numeric instance in (a)(ii) uses `g = 1/2`, `E = 0.3` at `(d,L) = (3,4)`; the planned Lean instance uses the flow
  point `P` (`g₀ ≤ 10`, `E = BAflowE …`). Both are nondegenerate; no defect.

## Verdict
Deliverables (i), (ii), (iii): met. Binding stop lines: not hit. **PASS** — stage 1b (`prover-max`) may start.
No dispatcher sign-off needed.
