Auditor model: claude-opus-5-5
# T2376 (BA-K06, `BA/KMolecule.lean`) — 1a-audit (design gate), Sat Oct 10 09:17:08 UTC 2026

Inputs: ticket `docs/tickets/T2376.md`; report `docs/reports/T2376-prove.md` §(a) (94 lines); branch `t/T2376` = 9d5d47d,
`git diff --stat main...t/T2376` empty (no Lean yet, as expected). Scripts rerun from the preflight's directory
`$S=/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/966b45d4-be15-4db2-88b3-45a074bfecd5/scratchpad/T2376`, outputs in `$S/audit/`.

## 1. Numerics (binding, ticket (iii)): rerun, verbatim
```
$ cd $S; time python3 k6.py layers 6 > audit/layers_out.txt; python3 summ.py audit/layers_out.txt
data  n  |TSP| (A)err/max  (B)err/max  (C)#cases err (max|Sigma|) layer-iff-cut,partition | control non-innermost J: #,max diff | control transposed chord: #,max diff
BA-A  3    1   0.00e+00/2.1e+00  1.78e-15/2.1e+00    0 0.00e+00 (0.0e+00)  True,True |   0, 0.00e+00 |   0, 0.00e+00
BA-A  4    3   4.44e-16/4.4e+00  6.22e-15/4.4e+00   16 3.33e-16 (6.4e-01)  True,True |   0, 0.00e+00 |  16, 1.67e-16
BA-A  5   11   5.33e-15/7.0e+00  8.45e-15/3.1e+00  128 3.34e-16 (6.7e-01)  True,True |  32, 6.72e-01 | 128, 4.45e-16
BA-A  6   45   3.91e-14/1.6e+01  6.84e-14/6.5e+00  832 5.56e-16 (7.1e-01)  True,True | 416, 7.13e-01 | 832, 5.80e-16
BA-B  3    1   0.00e+00/1.5e+00  6.68e-16/1.5e+00    0 0.00e+00 (0.0e+00)  True,True |   0, 0.00e+00 |   0, 0.00e+00
BA-B  4    3   2.22e-16/3.0e+00  1.78e-15/3.0e+00   16 1.12e-16 (2.9e-01)  True,True |   0, 0.00e+00 |  16, 1.11e-16
BA-B  5   11   3.55e-15/5.1e+00  2.26e-15/1.8e+00  128 8.33e-17 (2.1e-01)  True,True |  32, 1.95e-01 | 128, 7.85e-17
BA-B  6   45   1.52e-14/1.1e+01  1.03e-14/3.7e+00  832 8.58e-17 (1.6e-01)  True,True | 416, 1.59e-01 | 832, 8.78e-17
RAND  3    1   0.00e+00/1.1e+00  1.14e-16/1.1e+00    0 0.00e+00 (0.0e+00)  True,True |   0, 0.00e+00 |   0, 0.00e+00
RAND  4    3   5.72e-17/2.0e+00  5.55e-16/2.0e+00   16 5.82e-18 (1.3e-02)  True,True |   0, 0.00e+00 |  16, 9.73e-04
RAND  5   11   1.24e-16/4.2e+00  1.83e-15/4.2e+00  128 5.49e-18 (1.4e-02)  True,True |  32, 1.38e-03 | 128, 1.05e-03
RAND  6   45   4.58e-16/9.8e+00  5.62e-15/9.8e+00  832 1.04e-17 (2.1e-02)  True,True | 416, 1.48e-03 | 832, 1.48e-03
python3 k6.py layers 6 > audit/layers_out.txt  110.13s user 0.58s system 99% cpu 1:51.76 total
$ diff <(grep -v elapsed audit/layers_out.txt) <(grep -v elapsed layers_out.txt) && echo identical
identical
$ python3 gen.py; python3 table.py; python3 k6.py clauses     # all exit 0; inst/gen/table outputs byte-identical to the preflight's
generic cut, n=4..6, every diagonal J, 3 random sigma each, random Lw,P,S,Q, all F in TSP n with J in F: 330 cases, max|LHS - RHS| = 1.43e-14 (max|LHS| = 4.0e+01)
n, |TSP n|, #diagonals, min(p,q), all-J check (...bijective): [(4, 3, 2, 3, True), (5, 11, 5, 3, True), (6, 45, 9, 3, True), (7, 197, 14, 3, True), (8, 903, 20, 3, True)]
BA-sym   n=4: #(sigma,pi)=32: max|Sigma(delta+c)-Sigma(delta)|=1.49e-15; max|Sigma(c-delta)-Sigma(delta)|=1.49e-15
BA-sym   n=6: #(sigma,pi)=784: max|Sigma(delta+c)-Sigma(delta)|=3.82e-15; max|Sigma(c-delta)-Sigma(delta)|=3.82e-15
CONTROL circulant NON-symmetric M(+),M(-) n=4: ... max|Sigma(delta+c)-Sigma(delta)|=1.43e-17; max|Sigma(c-delta)-Sigma(delta)|=1.11e-01
CONTROL circulant NON-symmetric M(+),M(-) n=6: ... max|Sigma(delta+c)-Sigma(delta)|=1.43e-17; max|Sigma(c-delta)-Sigma(delta)|=4.91e-02
$ python3 inst.py > audit/inst_out.txt; diff -q audit/inst_out.txt inst_out.txt && echo identical
identical      (instance block of the prove report, lines 34-46, reproduced exactly)
```
Max error 6.84e-14 <= 1e-12 at n = 3..6, every sigma, every pi, full delta/a arrays, two BA data sets and non-symmetric random data;
no ODE. Controls fail as they must (non-innermost J: 1.4e-3..7.1e-1; transposed chord on non-symmetric data: ~1e-3).
**Mirror check (audit).** `k6.py` maps vs Lean `Loop/KLCut.lean`: `KLwIn:361`, `KLshiftIn:364` (ℕ-truncation = `max(.,0)`), `KLFIn:368`,
`KLcol:581`, `KLshiftOut:584`, `KLFOut:589`, `KLglueV:598`, `KLunCol:919`; `sigmaIn/sigmaOut` `KLSumZeroWard.lean:70,75`; Θ mirror
`Q[a,b]=M(s1)[b,a]·M(s2)[a,b]`, `inv(I-tQ)` = `BAMssOf` (`KCactus.lean:50`), `BAThetaOf` (`:70`). Chord src=`BAslotIn` (inner), tgt=`BAslotOut`
(`KCactus.lean:462-470`) and `KLgval_split` (`KLCut.lean:116`: `S u w`, `u` on `c₀ ∈ N₂`, new leaf `Pᵀ`) agree with the report's "`u` inner = row index".
All match. Verdict (iii): **met**.

## 2. Statements (ticket (i)) against the ticket, the paper and the consumers
Paper `A_deterministic_estimates.tex:617-627` (`eq:defKpi`, `eq_K-Kpi`, `eq:molecule-Kpi`); interface signatures read:
```
KLIndStepA.lean:1036  def SigSumZeroAbs {ι} (d n) [NeZero n] (L : ι → ℕ) [∀ i, NeZero (L i)] (g t : ι → ℝ)
    (Sig : ∀ i, (Fin n → Bool) → (Fin n → Zd d (L i)) → ℂ) : Prop :=
  (∀ i σ, (∀ j, σ j ≠ σ (j + 1)) → ∀ c δ, Sig i σ (fun j => c - δ j) = Sig i σ δ) ∧
  (∀ i σ, (∀ j, σ j ≠ σ (j + 1)) → ∀ δ c, Sig i σ (fun j => δ j + c) = Sig i σ δ) ∧ ∀ Q ≤ 2(d-1), ∃ C ...
KLIndStepB.lean:77    def IndStepAbs ... (Sig : ∀ i, (Fin n → Bool) → (Fin n → Zd d (L i)) → ℂ) (TH : ...) : Prop := ... Sig i σ δ * ∏ TH i (σ j) (σ (j+1)) (a j) (δ j)
KTreeRep.lean:48      BATreeRep: ∀ Λ κ, 0<Λ → 0<κ → ∀ L, 3≤L → ∀ W g, 0<g → g≤Λ → ∀ E m, BAReal d L g κ E m → ∀ t ∈ Ico 0 1, ∀ n [NeZero n], 3≤n → ∀ σ a,
                        BAKsol d L W (BAMsigma d L (BAMB d L g E m)) (PropSpin m) t (KLloopOf d L σ a) = ((W:ℂ)^d)⁻¹^(n-1) * Σ_{F∈TSP n} Γ ...
KLSumZeroWard.lean:165 Flong_eq_iff_cut (hF₀ : KLIsTSP F₀) (hπ : KLFlong F₀ σ = π) (hJπ : J ∈ π) (hinner : ∀ e ∈ π, KLArcLe e J → e = J)
KLCut.lean:1297       KLsum_cut (hn : 2 ≤ n) f : Σ_{F∈TSP n, J∈F} f (KLFOut F J) (KLFIn F J) = Σ_{G∈TSP(n-w+1)} Σ_{H∈TSP(w+1)} f G H
KSolve.lean:558       BAMsigma_shift (merged);  Ward.lean:83 BAMB_symm (merged, unconditional);  MFixedPoint.lean:507 BAMsigma M σ = if σ then M else Mᴴ
```
| target (report line) | check | result |
|---|---|---|
| `BAKpi d L n M t σ a π` (:9) | `= Σ_{F∈KLTSPlong n σ π} BAGamma …` = `(eq:defKpi)`; arg order = ticket; no `∏m` (as `BATreeRep`) | OK |
| `BASigmaTree`, `BASigmaPi … σ π δ` (:10) | `KLgval` with leaf weights `1` ⇒ `1[δ_v=b(leaf v)]` = ticket's "indicator of δ_v at the leaf's slot"; same edges as `BACactusVal` | OK |
| `baK_eq_sum_Kpi` (:11) | hypotheses = `BATreeRep`'s at `Λ:=g` (removes `Λ`, `0<g≤g`), `W` power `((W)^d)⁻¹^(n-1)` = `eq_K-Kpi`; Σ over `(diagonals n).powerset` = `π ⊂ Z_n^off` | OK |
| `baKpi_eq_sum_SigmaPi` (:12) | same shape as band `KLKpi_eq_sum_SigmaPi` (`KLTree.lean:435`), leaf `Θ^{σ_vσ_{v+1}}(a_v,δ_v)` = `IndStepAbs`'s `TH (σ j)(σ(j+1)) (a j)(δ j)`; no hypothesis | OK |
| `baSigmaPi_cut` (:15) | hypotheses = `Qlayer_cut`'s / `Flong_eq_iff_cut`'s (`2≤n`, `F₀∈TSP n`, layer, `J∈π`, innermost); outer `BASigmaPi (sigmaOut σ J) ((π.erase J).image (KLshiftOut J))`, inner `BASigmaPi (sigmaIn σ J) ∅`, chord `t•Θ^{σ_iσ_j}` = ticket; `W`-free; no `M`/`t` hypothesis | OK |
| `BAdeltaIn/Out` (:13) | index layout = `rhs_factor` einsum in `k6.py` (inner `δ_i..δ_{j-1},u`; outer `δ_<i, w @ KLglueV, δ_≥j`) | OK |
| `BASig` / `baSig_transl` (:17) | type `∀ i, (Fin n→Bool)→(Fin n→Zd d (L i))→ℂ` = `Sig` of `SigSumZeroAbs`/`IndStepAbs`; clauses = conjuncts 1 (reflection) and 2 (translation), stated for every σ (stronger than alternating); no hypothesis: reflection of `Mᴴ` needs only `BAMB_symm` + `BAMsigma_shift` (both merged) | OK |
| `baSigmaPi_shift/reflect` (:16) | carry `hshift`, `hsymm` as explicit hypotheses (C2 allows `M` symmetry); discharged at BA data by the merged lemmas | OK |
| `baCactus_cut` (:14, proposed public) | generic in `Lw,P,S,Q`; checked numerically (`gen.py`, 330 cases, 1.4e-14) | statement OK; public status: see §4 |
Consumers named per row (K07, K08a/b, K10, K09b): ticket (i) **met**. C2: the Σ-level cut uses no symmetry of `M` (indicators,
`1ᵀ=1`; RAND data pass); reversal `Θ^{σ_jσ_i}=(Θ^{σ_iσ_j})ᵀ` is `BAMssOf` transposition, any `M`. No non-symmetric-`M` fact needed: **not a 1a FAIL**.
Hidden hypotheses / vacuity: none (no structure fields; all hypotheses explicit). Cycle: none (inputs `BA/KTreeRep` ab54184, `Loop/*` merged).
Name clash (`grep -rnw <name> RBM3D RBM3D.lean --include='*.lean' | wc -l`): `BAKpi BASigmaTree BASigmaPi BAdeltaIn BAdeltaOut baCactus_cut
baSigmaPi_cut baSigmaPi_shift baSigmaPi_reflect BASig baSig_transl baK_eq_sum_Kpi baKpi_eq_sum_SigmaPi KMolecule_`: 0 each.
Instance plan (target 2): `P` of `(3,4)`, `W=2`, `t=1/2`, `n=4`, `σ=(+,+,-,+)`, `F₀={(0,2)}`, `π={(0,2)}` (KLFlong = {(0,2)}, mixed charges,
J trivially innermost); clauses at alternating `σ`; third conjunct of `SigSumZeroAbs` kept as hypothesis of the interface example
(other gate's pin): nondegenerate, all deterministic hypotheses dischargeable. **OK.**

## 3. Written argument (ticket (ii))
Layer bijection (`Flong_eq_iff_cut` + `KLsum_cut`, as the band `Qlayer_cut` `KLSumZeroWard.lean:293`), `W`-free gluing (`W` only in
`baK_eq_sum_Kpi`), reversed leaf (C2, via `KLgval_split`'s `Pᵀ`), leaf-removal bookkeeping (indicator labels `BAdeltaIn/Out`): all four
items present (report :75-78) and consistent with the Lean signatures above and the numerics. **Met.**

## 4. Plan (ticket (iv)) against the binding stop line 1500 — DEFECT
```
$ for s in Maps ... CutThm; do <code lines (no blanks/comments/docstrings) of section s of RBM3D/BA/KTreeRep.lean>; done
Maps 76-146 raw 71 code 49 | Transport 264-297 raw 34 code 28 | InSide 301-382 raw 82 code 71 | InSlots 384-558 raw 175 code 151
OutSide 562-700 raw 139 code 123 | OutSlots 702-871 raw 170 code 146 | CutEquivs 875-959 raw 85 code 73 | CutEquivs2 961-1040 raw 80 code 69
CutLabels 1042-1111 raw 70 code 62 | CutMain 1113-1136 raw 24 code 18 | CutParts 1138-1272 raw 135 code 121 | CutThm 1274-1368 raw 95 code 87
total raw 1160 code 998            (all helpers private: `grep -cE '^private ...' KTreeRep.lean` = 94 private, 6 public; copying is forced)
$ python3 $S/audit/plan.py
plan (iv) code central: 1350 + docstrings 100 = 1450
K05b sections plan says are copied: section 4 = 790 (plan 650); section 5 = 208 (plan 200)
plan with measured copy sizes: code 1498 + docstrings 100 = 1598 ; stop line 1500; ticket estimate 500/750/1200
```
The report's own section counts are exact (998 / 1160 reproduced), but its §4 row books 650 lines for sections that measure 790 code
lines, with no stated reduction. With the measured sizes the **central** estimate is ≈1600 > 1500; the report's own high is 1800 and
it states "The stop line binds at the central estimate" (:90), leaving the remedy ((a) raise to 1800, (b) a second file) to the
dispatcher. Option (b) changes the sole writable files; the public `baCactus_cut` (not stem-prefixed, CLAUDE.md §3 (E)) is tied to the
same decision (K10 would import it instead of a third copy of the cut machinery). Neither is decidable by stage 1b or a repairer.
Ticket (iv) is therefore **not met**: the plan does not fit the binding stop line.

## 5. Paper deltas
Proposed: `T2376a` (BA chord `tΘ^{(σ_i,σ_j)}` vs paper `tS^{(B)}Θ^{(+,-)}`), `T2376b` (no `∏m(σ_i)`). Missing: the Lean form of
`(eq:molecule-Kpi)` is the one-edge recursive factorisation (outer factor `BASigmaPi(σ_out, π')` still carries long edges; the
"first stage" `BASigmaPi … π` with `π ≠ ∅` has no paper counterpart; the paper's per-molecule `Σ^{(π)}(t,σ^{(k)},b^{(k)})` is Lean's
`BASigmaPi (σ^{(k)}) ∅`), not the paper's product over `r` molecules with `r-1` chords. This Lean/paper difference needs a candidate.

## 6. Observations (no verdict effect)
- Ticket text calls conjunct 1 of `SigSumZeroAbs` a translation; it is a reflection (report :78, confirmed at `KLIndStepA.lean:1036`).
- `KLsum_TSPlong` is at `KLTree.lean:381` (ticket says :384). `BAMsigma_shift` is merged (`KSolve.lean:558`), as the report says.
- Report row :17 writes `BAMB (L i) (g i) (E i) (m i)` without `d` (mathematical shorthand; Lean form `BAMB d (L i) (g i) (E i : ℂ) (m i)`).
- Numerics run on a 1-dimensional cycle `Z_q` (q = 3, 4): adequate, all identities are algebraic in `M`, `t`.

## Verdict
Statements (i): PASS. Argument (ii): PASS. Numerics (iii): PASS (6.84e-14, reproduced byte-identically). Plan (iv): **RETURN** —
central estimate with measured copy sizes ≈1598 lines > binding stop line 1500 (report's own high 1800); the remedy is a scope/limit
decision. **Overall: RETURN; needs dispatcher sign-off.**

**Required for resubmission**
1. Dispatcher decision on size: raise the stop line (≥ 1800), or add a second sole writable file for the copied K05b cut machinery and
   `baCactus_cut` (with its import into `KMolecule.lean`), or another re-scope; and decide public vs private `baCactus_cut`.
2. Re-state plan (iv) under that decision with §4 counted at the measured 790 code lines (or list which K05b lemmas are dropped and why),
   with decision points that fit the new limit.
3. Add a paper-delta candidate (`T2376c`) for the recursive one-edge form of `(eq:molecule-Kpi)` (§5 above).
