Prover model: claude-sonnet-5-5

## (a) Math preflight — Tue Oct  6 13:39:15 UTC 2026

Scripts (Python, no Lean; `S` = scratchpad dir `T2295/`): `bagraph.py` (counters, `split`, `merge` of T2287 `ba.py`, plus `lanlwT1/lanlwD/lanlwTerms` = (M4)), `ord.py`, `val.py`, `m1.py`, `mc2.py`; all four commands below were rerun at the time above.
Paper: `B_graphical_lemmas.tex:359-372` (`lanlw`, `eq:BE` at :361), `7_8_light_weight.tex:110` (`eq:def-Spm`).

### (i) Exponent table

| # | quantity | value | constraint | slack |
|---|---|---|---|---|
| 1 | `t` | `0 ≤ t < 1` (hyps of `BAlanlw`) | `Im z_t = (1-t) Im m > 0` so `G` exists; `Im(E+m) = Im m > 0` so `M` exists | `t = 1/2`: `Im z_t = 0.3617`, `1-t = 1/2`; `t = 0`: `V_0 = 0`, `S = 0`, `G = M`, both sides 0 (separate branch, as `lwWeightExp_holds`) |
| 2 | `L`, `W` | `3 ≤ L`; `W ≥ 1` (`NeZero`) | `3 ≤ L` enters through `sz.three_le_L` in `lwS_row_sum` (`LWStein.lean:1215`); no `L`–`W` relation | `L = 3` (slack 0, allowed), `W = 1` |
| 3 | `g₀`, `E` | any reals | none; `BASelf d L g₀ E m` (`MFixedPoint.lean:193`) is the only condition on the data | `g₀ = 1/2`, `E = 0.3`: `m = -0.139326+0.723352i`, `Im m > 0`, residual `3.4e-16` |
| 4 | row sum of `S` | `Σ_β S_{αβ} = t` | `svarF d L W 0 = W^{-d} SBR(..)` (`FineModel.lean:47`); `sbKernelR 0 = 1(x=0) + 0` since the second summand has factor `g²` (`Defs/Block.lean:73-75`); through `lwWx_lwS_apply` (`LWWeightExp.lean:281`) at `g = 0` | numeric `max\|rowsum(S) - t\| = 0.0e+00` (Command B) |
| 5 | `M_{ββ} = m` | exact, needs `BASelf` | `BAMres_fine_apply` (`FlowPins.lean:100`, needs `(E+m).im ≠ 0`) gives `M_{ββ} = M^{(B)}_{[β][β]}`, then `BAMB_diag_eq` (`Ward.lean:89`) | `3.6e-16` at `m`; `8.7e-02` at `m+0.15i` (so `BASelf` is necessary) |
| 6 | (M1) `Ǧ = -M(V_t+tm)G` | pathwise, any `m` | `IsUnit` of `G⁻¹` (row 1) and of `M⁻¹`; `H = g₀Ψ+√t X` Hermitian (`PsiI_isHermitian`, `BlockAnderson.lean:65`) | residual `7.6e-16` (`m`), `5.1e-16` (`m+0.15i`): "two data, one model" PASS |
| 7 | Stein | `E[(H_u)_{wα}F] = u S_{wα} E[∂_{h_{αw}}F]` (`stein_sample`, `LWStein.lean:1013`) | closed forms `∂G_{ij} = -G_{iα}G_{wj}` need `0 < u`; `GaussIBP sz` is discharged by `RBM.Green.gaussIBP` (`IBPPoly.lean:305`, proved) | `u = t = 1/2 > 0`; `t = 0` is row 1 |
| 8 | raw counters of `lanlw` terms | `(ΔnS, ΔnW, ΔnA, ΔnM) = (+1, +1, +1, 0)`, `Δord = +1`, term 1 and every derivative term | `β` is a new singleton internal atom; `α` joins the atom of `x` (`M` edge); `α, β` join the molecule of `x` | 18270 terms, 0 violations (Command D) |
| 9 | `ordG` vs `ord Γ` (`Γ` normal) | `ord Δ - ord Γ = 1 - j + 2κ` for a partition term with `j` `M`-splits (`j ≤ 1` for term 1; `j ≤ 3` for derivative terms) and `κ` internal atoms lost | `≥ 0`: for `j ≥ 2` an edge at `β` is split (only one derivative edge avoids `β`), then `κ ≥ 1`; for `j ≤ 1`, `1-j ≥ 0` | min over 18270 terms `= 0`, equality in 13228; so `Γ.Normal → Γ.scalingOrder ≤ Δ.scalingOrderG` holds, slack 0 (tight) |
| 10 | derivative-term coefficient | `+Γ.coeff` (= `-1` times the coefficient of `LGraph.dTerm`, `LWStein.lean:1381`) | the explicit `-` of `-Σ M S G ∂f` cancels the `-` of `∂G = -GG` | with `+Γ.coeff`: error `1.0e-09`; with `-Γ.coeff`: `3.2e+01` (Command C) |
| 11 | downstream (L2b/L2c; `BAlwMp`, `BAlwW` unused here) | max row abs-sum of `M⁺S` `= 0.5000 = t` | Gershgorin from `Σ_b\|M_ab\|² = 1` (`BAMB_row_sq_real`, `Ward.lean:125`) and `\|M_xy\| = \|M_yx\|` (`BAMB_symm`, `:83`): row sum `≤ t < 1` | `1 - t = 1/2`; `max\|Σ_b\|M_ab\|² - 1\| = 6.7e-16` |
| 12 | §29 | (1) `0 ≤ t < 1` present; (2) no gate; (3) only `3 ≤ L`; (4) no `∀ n`; (5) expectation over `PF d L W 0` only; (6) no hypothesis on `g₀`, `E`; (7) no constants | | |

External hypotheses: none unproved (`gaussIBP` merged; `BASelf` is a hypothesis on the data, satisfied at the instance below with residual `3.4e-16`; no limit is involved).

### (ii) Concrete nondegenerate instance: `d = 3`, `L = 3`, `W = 1`, `N = 27`, `g₀ = 1/2`, `E = 0.3`, `t = 1/2`, `m = -0.139326+0.723352i`

Hypotheses of `baLanlw_holds` at the instance: `3 ≤ 3`; `0 ≤ 1/2 < 1`; `BASelf` (row 3); `P` = `f1 = G_{ab}`, `f2 = G_{ab} conj(G_{cd})`; `gaussIBP` proved.

Command A (`cd $S; python3 m1.py`):
    m (BASelf)   Im z_t=0.3617  max|(G-M) + M(V+t*m)G| = 7.6e-16   max|M_xx-m| = 3.6e-16
    m+0.15i      Im z_t=0.4367  max|(G-M) + M(V+t*m)G| = 5.1e-16   max|M_xx-m| = 8.7e-02
    max row abs-sum of M^+ S = 0.5000 (<= t=0.5); max |sum_b |M_ab|^2 - 1| = 6.7e-16

Command B (`python3 mc2.py 3 3 1 200000 11`; Monte Carlo, `V` Gaussian with variance `t·svarF d L W 0`; LHS-RHS of `BAlanlwL/R` for `lanlw`, of `lem_lweight` with `1+M⁺S⁺ = (1-M⁺S)⁻¹`, `S⁺ = S(1-M⁺S)⁻¹`, of `GGGamma` as printed (`S⁺_{xβ}`) and with D402 (`(M⁺S⁺)_{xβ}`, `docs/paper-deltas.md:1361`); case A `x=y=a=b=c=d=0`, case B `x=0,y=1,a=1,b=0,c=1,d=0`):
    d=3 L=3 W=1 N=27 g0=0.5 E=0.3 t=0.5: m=-0.139326+0.723352j, self_m residual=3.4e-16, max|M_xx-m|=3.6e-16, max|rowsum(S)-t|=0.0e+00
      Im z_t=0.3617; ||M^+S||_op=0.348; max|(M^+S^+) - ((1+M^+S^+)-1)|=1.0e-15
      samples=200000 per row. LHS=E[...] vs RHS: |E(LHS-RHS)|, s.e., |E LHS|, |E LHS|/s.e., |diff|/s.e.
      correct m         case A f1 lanlw                |diff|=1.85e-03 se=1.85e-03 |E LHS|=7.12e-02 sig=  38.5 diff/se=  1.0
      correct m         case A f1 lweight              |diff|=1.50e-03 se=1.46e-03 |E LHS|=7.12e-02 sig=  48.7 diff/se=  1.0
      correct m         case A f1 GGGamma printed S+   |diff|=1.89e-01 se=1.18e-03 |E LHS|=3.14e-02 sig=  26.7 diff/se=160.3
      correct m         case A f1 GGGamma D402 M+S+    |diff|=1.64e-03 se=1.20e-03 |E LHS|=3.14e-02 sig=  26.1 diff/se=  1.4
      correct m         case A f2 lanlw                |diff|=9.29e-04 se=1.53e-03 |E LHS|=9.94e-02 sig=  65.0 diff/se=  0.6
      correct m         case A f2 lweight              |diff|=7.76e-04 se=1.21e-03 |E LHS|=9.94e-02 sig=  82.2 diff/se=  0.6
      correct m         case A f2 GGGamma printed S+   |diff|=3.48e-01 se=9.34e-04 |E LHS|=6.37e-02 sig=  68.2 diff/se=372.4
      correct m         case A f2 GGGamma D402 M+S+    |diff|=1.61e-03 se=1.08e-03 |E LHS|=6.37e-02 sig=  59.1 diff/se=  1.5
      correct m         case B f1 lanlw                |diff|=1.67e-04 se=2.27e-04 |E LHS|=6.42e-03 sig=  28.3 diff/se=  0.7
      correct m         case B f1 lweight              |diff|=2.61e-04 se=3.65e-04 |E LHS|=1.39e-02 sig=  38.0 diff/se=  0.7
      correct m         case B f1 GGGamma printed S+   |diff|=1.29e-03 se=6.43e-05 |E LHS|=2.27e-04 sig=   3.5 diff/se= 20.1
      correct m         case B f1 GGGamma D402 M+S+    |diff|=8.58e-05 se=7.29e-05 |E LHS|=2.27e-04 sig=   3.1 diff/se=  1.2
      correct m         case B f2 lanlw                |diff|=4.58e-05 se=5.84e-05 |E LHS|=4.48e-03 sig=  76.7 diff/se=  0.8
      correct m         case B f2 lweight              |diff|=7.99e-05 se=9.59e-05 |E LHS|=6.01e-03 sig=  62.7 diff/se=  0.8
      correct m         case B f2 GGGamma printed S+   |diff|=1.74e-03 se=2.03e-05 |E LHS|=5.33e-04 sig=  26.2 diff/se= 85.4
      correct m         case B f2 GGGamma D402 M+S+    |diff|=2.29e-05 se=2.32e-05 |E LHS|=5.33e-04 sig=  23.0 diff/se=  1.0
      wrong m (+0.15i)  case A f1 lanlw                |diff|=4.02e-02 se=1.37e-03 |E LHS|=2.60e-02 sig=  18.9 diff/se= 29.2
      wrong m (+0.15i)  case A f1 lweight              |diff|=3.28e-02 se=1.13e-03 |E LHS|=2.60e-02 sig=  22.9 diff/se= 28.9
      wrong m (+0.15i)  case A f1 GGGamma printed S+   |diff|=1.63e-01 se=7.60e-04 |E LHS|=2.96e-02 sig=  39.0 diff/se=215.0
      wrong m (+0.15i)  case A f1 GGGamma D402 M+S+    |diff|=2.86e-03 se=7.84e-04 |E LHS|=2.96e-02 sig=  37.8 diff/se=  3.7

Command C (`python3 val.py 1`, `python3 val.py -1`; 40 random (graph, data) pairs, `N = 3`, random `M, S, Ψ`, `f` = value of `Γ-e`, `∂_{h_{βα}}f` by central finite differences of the holomorphic extension; sum of the term graphs of (M4) vs `BAlanlwR`'s formula):
    derivative coefficient = +1 * Gamma.coeff; 41 derivative terms (19 red edges differentiated) in 40 random (graph, data) pairs, N=3: max |RHS_direct - sum of term-graph values| = 1.01e-09 (max |RHS| = 5.49e+01); FD step 1e-5
    derivative coefficient = -1 * Gamma.coeff; 41 derivative terms (19 red edges differentiated) in 40 random (graph, data) pairs, N=3: max |RHS_direct - sum of term-graph values| = 3.18e+01 (max |RHS| = 5.49e+01); FD step 1e-5
Orientation: blue `e'=(a,b)` gives `(a,β),(α,b)`, red gives `(a,α),(β,b)` (`∂_{h_{βα}}`, `dhSample_lwG` `LWStein.lean:561`, `dhSample_lwG_star` `:591`; `BAlwdf β α` = `LWPins_dH … β α`, `LWPins.lean:62`).

Command D (`python3 ord.py`; counters `(nS,nW,nA,nM)`, `ord`, `ordG`; (I3), (I4), the paper examples, random normal graphs):
    --- paper examples (T2287 ba.py rows reproduced)
    LHS  Gc_xy (x,y external)                    counters=(1, 0, 0, 0) ord=1 ordG=1
      term1                                      counters=(2, 1, 1, 0) ord=2 ordG=1
    LHS  Gc_xx (x internal)                      counters=(1, 0, 1, 1) ord=-1 ordG=-1
      term1                                      counters=(2, 1, 2, 1) ord=0 ordG=-1
    baGGLhs  Gc_{y'x}Gc_{xy}                     counters=(2, 0, 1, 1) ord=0 ordG=0
      lanlw at Gc_xy: term1                      counters=(3, 1, 2, 1) ord=1 ordG=1
      lanlw at Gc_xy: term2                      counters=(3, 1, 2, 1) ord=1 ordG=0
    normal: Gc_xy + blue + red + weight          counters=(4, 1, 1, 0) ord=4 ordG=4
      term1                                      counters=(5, 2, 2, 0) ord=5 ordG=4
      term2                                      counters=(5, 2, 2, 0) ord=5 ordG=5
      term3                                      counters=(5, 2, 2, 0) ord=5 ordG=4
      term4                                      counters=(5, 2, 2, 0) ord=5 ordG=5
    random normal graphs: 2456, terms: 18270; raw counters != (nS+1,nW+1,nA+1,nM): 0; ordG(term) < ord(Gamma): 0; min(ordG-ord(Gamma))=0; equality cases 13228
Dispatcher's numbers reproduce: `lanlw` LHS `1 0 0 0` ord 1; term 1 `2 1 1 0`, raw 2, `ordG` 1 (= (I3): `E = Fin 2`, `I = Fin 0`); `Ǧ_{xx}` (I4: `E = Fin 0`, `I = Fin 1`) term 1 `2 1 2 1`, raw ord 0, `ordG` -1. (I1): `BAlwS 3 3 1 (1/2) x x = t·W^{-d} = 1/2` (row 4). (I2): at `t = 0`, `S = 0`, `G = M`, both sides `0`.

### Verdicts

- Target 1 (vocabulary, `BAlanlw` pin text): PASS. `BAlanlwR` is `eq:BE` term by term; `S = t W^{-d}1([α]=[β])` is the variance of `√t V` (row 4, Command B).
- Target 2 (`baLanlw_holds`): PASS; route (M1)-(M3) closes with the merged inputs of rows 4-7, no hypothesis beyond `BASelf`.
- Target 3 (graph operation): PASS for (a)-(c) at the level of mathematics; `lanlw_scalingOrderG` holds (row 9, Command D). Note for the writer: the derivative-term graph has coefficient `+Γ.coeff` (row 10), not `-Γ.coeff` as `LGraph.dTerm` has; read as coefficient `-Γ.coeff`, the ticket's "sign `-1`" fails (Command C). No paper delta; T2295a/T2295b not needed. (Amend 1, `docs/tickets/T2295-amend-1.md`, moves target 3 and (I3), (I4) to BA-L2b; this verdict is unchanged by it.)
- Preflight (v): target 3(c) is the shape `LWLvl1` uses (`ord Δ.counters = ord Γ.counters + 1`, `lvl1_good_R2` `LWLvl1.lean:2531`); L2b needs `lanlw` at `y = x` (`Ǧ_{xx}`, (I4)); L2c needs `Ǧ_{xy}` with `f ↦ Ǧ_{y'x} f`.

## (b) Script output, stage 1b (written Tue Oct  6 13:12:43 UTC 2026; branch `t/T2295` at `d57aa36`, parent `1ba63a2`)

Scope. Delivered: target 1 (vocabulary and pin), target 2 (`baLanlw_holds`), instances (I1), (I2) = cut BA-L2a1. NOT delivered:
target 3 (`lanlwT1`, `lanlwD`, `lanlwTerms`, value identity (b), counters (c), `lanlw_scalingOrderG`) and instances (I3), (I4) = cut BA-L2a2,
by the ticket rule "Over 1500 at 1b: stop and RETURN with the cut". Basis (command, output):
```
$ wc -l RBM3D/Graph/BAExpand.lean | awk '{print $1}'; echo $((1500 - $(wc -l < RBM3D/Graph/BAExpand.lean)))
904
596
$ sed -n '435,1369p' RBM3D/Graph/LWWeightExp.lean | wc -l    # merged twin: the graph operation of (Owx), no atom counter
935
$ grep -n "private theorem BAVocab_\(cnt_equiv\|merge_counters\|baSplitSolid_circ\)" RBM3D/Graph/BAVocab.lean
993:private theorem BAVocab_cnt_equiv {E' I' : Type} [Fintype E'] [DecidableEq E'] [Fintyp
1107:private theorem BAVocab_merge_counters (Γ : BAGraph E I) (h : ∀ e ∈ Γ.dotted, e.eq = 
1128:private theorem BAVocab_baSplitSolid_circ {V : Type*} :
$ grep -n "def lwSampleData\|theorem lwStein_term_eq\|theorem lwStein_sedge_val_blue" RBM3D/Graph/LWStein.lean   # LData-based, `lwG` only
1420:def lwSampleData (z : ℂ) (u : ℝ) (M S Sp : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (s
1427:theorem lwStein_sedge_val_blue {V : Type*} (e : SEdge V) (hσ : e.σ = true) (ℓ : V → I
1506:theorem lwStein_term_eq (Γ : LGraph E I) (ℓ : E ⊕ I → Idx d (sz.L n) (sz.W n)) (ω : S
```

b.1 Build (the module olean removed first, then rebuilt) and the registry pre-check (CONTROL H28 scratch file, not committed):
```
$ lake build RBM3D.Graph.BAExpand 2>&1 | grep -n "Built RBM3D.Graph.BAExpand\|Build completed\|error\|BAExpand.lean"
266:✔ [3778/3778] Built RBM3D.Graph.BAExpand (5.5s)
267:Build completed successfully (3778 jobs).
$ printf "import RBM3D\nimport RBM3D.Graph.BAExpand\n\n#assert_rbm_axioms\n" > $SCRATCH/precheck.lean; lake env lean $SCRATCH/precheck.lean; echo exit=$?
axiom audit: 8443 theorems, 2805 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
exit=0
$ lake build 2>&1 | tail -1    # the whole library (the root does not import BAExpand before the hub merge)
Build completed successfully (4100 jobs).
exit=0
```

b.2 Axioms: `#print axioms` of all 35 theorems of the file (script: names from the file), distinct results:
```
  35 [propext, Classical.choice, Quot.sound]
'RBM.Graph.baLanlw_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
```

b.3 Target statements, extracted from the file (BAExpand.lean line numbers):
```
-- target 1, the pin (BAExpand.lean:117-121); the vocabulary BAlwH..BAlanlwR (lines 54-115) is the check-file block, see b.6
def BAlanlw (d : ℕ) : Prop :=
  ∀ (L W : ℕ) [NeZero L] [NeZero W], 3 ≤ L → ∀ (g0 E t : ℝ) (m : ℂ), RBM.BA.BASelf d L g0 (E : ℂ) m →
    0 ≤ t → t < 1 →
    ∀ (P : MvPolynomial (Bool × Idx d L W × Idx d L W) ℂ) (x y : Idx d L W),
      ∫ ω, BAlanlwL d L W g0 E t m P x y ω ∂(PF d L W 0) = ∫ ω, BAlanlwR d L W g0 E t m P x y ω ∂(PF d L W 0)
-- target 2 (BAExpand.lean:744)
theorem baLanlw_holds (d : ℕ) : BAlanlw d := by
-- BAExpand.lean:250
theorem dhSample_baG {z : ℂ} (hz : z.im ≠ 0) {u : ℝ} (hu : 0 < u) (g0 : ℝ)
    (α w i j : Idx d (sz.L n) (sz.W n)) (ω : Sizes.SeqΩ sz) :
    dhSample sz n u α w (baG sz n g0 z u i j) ω = -(baG sz n g0 z u i α ω * baG sz n g0 z u w j ω) :=
-- BAExpand.lean:256
theorem dhSample_baG_star {z : ℂ} (hz : z.im ≠ 0) {u : ℝ} (hu : 0 < u) (g0 : ℝ)
    (α w i j : Idx d (sz.L n) (sz.W n)) (ω : Sizes.SeqΩ sz) :
    dhSample sz n u α w (fun ω => star (baG sz n g0 z u i j ω)) ω =
      -star (baG sz n g0 z u i w ω * baG sz n g0 z u α j ω) :=
-- BAExpand.lean:354
theorem stein_baPoly (hG : GaussIBP sz) {z : ℂ} (hz : z.im ≠ 0) (g0 : ℝ) {u : ℝ} (hu : 0 ≤ u)
    (P : MvPolynomial (Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n) × Bool) ℂ)
    (α w : Idx d (sz.L n) (sz.W n)) :
    ∫ ω, sz.seqHflow n u ω w α * baPoly sz n g0 z u P ω ∂(Sizes.seqP sz) =
      lwS sz n u w α * ∫ ω, dhSample sz n u α w (baPoly sz n g0 z u P) ω ∂(Sizes.seqP sz) :=
-- BAExpand.lean:485
theorem baWx_dh {z : ℂ} (hz : z.im ≠ 0) {u : ℝ} (hu : 0 < u) (g0 : ℝ) (α w : Idx d L W)
    (ω : Sizes.SeqΩ (lwWxSizes d L W 0 hL)) (P : MvPolynomial (Bool × Idx d L W × Idx d L W) ℂ) :
    dhSample (lwWxSizes d L W 0 hL) 0 u α w (baPoly (lwWxSizes d L W 0 hL) 0 g0 z u (lwWxRename d L W P)) ω =
      LWPins_dH (LWPins_resPoly d L W z P) ((g0 : ℂ) • PsiI d L W +
        Hflow d L W u (Sizes.slice (lwWxSizes d L W 0 hL) 0 ω)) α w :=
```

b.4 Compiled nonempty instances (BAExpand.lean lines 789-899, namespace `RBM.Graph.BAExpandInst`; proofs elided where noted):
```
theorem baS_diag (x : Idx 3 3 1) : BAlwS 3 3 1 (1 / 2) x x = 1 / 2 := by
theorem baS_row_sum (x : Idx 3 3 1) : ∑ y, BAlwS 3 3 1 (1 / 2) x y = 1 / 2 := by
theorem baLanlw_t0 (g0 E : ℝ) (m : ℂ) (hSelf : RBM.BA.BASelf 3 3 g0 (E : ℂ) m)
    (P : MvPolynomial (Bool × Idx 3 3 1 × Idx 3 3 1) ℂ) (x y : Idx 3 3 1) :
    ∫ ω, BAlanlwL 3 3 1 g0 E 0 m P x y ω ∂(PF 3 3 1 0) = 0 ∧
      ∫ ω, BAlanlwR 3 3 1 g0 E 0 m P x y ω ∂(PF 3 3 1 0) = 0 ∧
      ∫ ω, BAlanlwL 3 3 1 g0 E 0 m P x y ω ∂(PF 3 3 1 0) =
        ∫ ω, BAlanlwR 3 3 1 g0 E 0 m P x y ω ∂(PF 3 3 1 0) := by
  have hL0 : ∀ ω, BAlanlwL 3 3 1 g0 E 0 m P x y ω = 0 := fun ω => by
  ...  (proof: pointwise vanishing, then `baLanlw_holds 3 3 1 _ g0 E 0 m hSelf le_rfl one_pos P x y`)
theorem baSelf_zero : RBM.BA.BASelf 3 3 0 ((0 : ℝ) : ℂ) Complex.I := by
example :
    ∫ ω, BAlanlwL 3 3 1 0 0 (1 / 2) Complex.I (MvPolynomial.X (true, (fun i => if i = 0 then 1 else 0), 0)) 0
      (fun i => if i = 0 then 1 else 0) ω ∂(PF 3 3 1 0) =
    ∫ ω, BAlanlwR 3 3 1 0 0 (1 / 2) Complex.I (MvPolynomial.X (true, (fun i => if i = 0 then 1 else 0), 0)) 0
      (fun i => if i = 0 then 1 else 0) ω ∂(PF 3 3 1 0) :=
  baLanlw_holds 3 3 1 (by norm_num) 0 0 (1 / 2) Complex.I baSelf_zero (by norm_num) (by norm_num) _ _ _
example (m : ℂ) (hSelf : RBM.BA.BASelf 3 3 (1 / 2) (((3 / 10 : ℝ)) : ℂ) m) :
    ∫ ω, BAlanlwL 3 3 1 (1 / 2) (3 / 10) (1 / 2) m
      (MvPolynomial.X (true, (fun i => if i = 0 then 1 else 0), 0) *
        MvPolynomial.X (false, (fun i => if i = 0 then 1 else 0), 0)) 0
      (fun i => if i = 0 then 1 else 0) ω ∂(PF 3 3 1 0) =
    ∫ ω, BAlanlwR 3 3 1 (1 / 2) (3 / 10) (1 / 2) m
      (MvPolynomial.X (true, (fun i => if i = 0 then 1 else 0), 0) *
        MvPolynomial.X (false, (fun i => if i = 0 then 1 else 0), 0)) 0
      (fun i => if i = 0 then 1 else 0) ω ∂(PF 3 3 1 0) :=
  baLanlw_holds 3 3 1 (by norm_num) (1 / 2) (3 / 10) (1 / 2) m hSelf (by norm_num) (by norm_num) _ _ _
-- also in the file, 8 `example`s (lines 817-863): dhSample_baG, dhSample_baG_star, baG_tame1, baPoly_tame1, stein_baPoly, baWx_baG, baWx_baPoly, baWx_dh at d=3, L=3, W=1
```

b.5 Name-clash grep (all 54 new public names, `grep -rnw` over `RBM3D/`, `Probe/` excluded) and the ticket's list on `main`:
```
54 distinct new public names; hits outside RBM3D/Graph/BAExpand.lean (RBM3D/Probe/ excluded): 0
BAlanlw=0 BAlanlwL=0 BAlanlwR=0 BAlwH=0 BAlwM=0 BAlwG=0 BAlwGc=0 BAlwS=0 BAlwMp=0 BAlwW=0 BAlwf=0 BAlwdf=0 BAExpand=0 baG=0 baGm=0 baVar=0 baPoly=0 baStein=0 
```

b.6 Check-file equality (ticket acceptance): (a) block between `namespace RBM.Graph.T2295Check` and `end ...` vs BAExpand.lean; (b) compile:
```
check block lines: 69 chars(normalized): 3224
block found verbatim (whitespace-normalized) in BAExpand.lean: True
check section 2 vocabulary declarations: 16
$ lake env lean $SCRATCH/eqb.lean   # check-file imports + import RBM3D.Graph.BAExpand + example : ∀ d, RBM.Graph.BAlanlw d := RBM.Graph.baLanlw_holds
exit=0
```

b.7 Files and ports:
```
$ git diff --stat main...t/T2295
 RBM3D/Graph/BAExpand.lean | 904 ++++++++++++++++++++++++++++++++++++++++++++++
 1 file changed, 904 insertions(+)
$ grep -c "LWweightExp\|BAlanlw" RBM3D/Test/Axioms.lean   # no registry line needed, see narrative 6
0
$ grep -c "sorry\|admit\|native_decide\|^axiom" RBM3D/Graph/BAExpand.lean
0
```
No port (ticket: RBM2D has no block Anderson graph layer); RBM1D and RBM2D were not read; no RBM1D/RBM2D diff-stat applies.

Narrative.
1. Target 2 route, as in the ticket: (M1) `BAExpand_G_sub_M`: `G - M = -M (H_u + u m) G` for `G = (g₀Ψ + H_u - z_u)⁻¹`, `M = Mres (g₀Ψ) E m`,
   from `BAExpand_inv_sub_inv` and `isUnit_sub_smul_of_isHermitian` (needs `Im m > 0`, `u < 1`); (M3) `M_{ββ} = m` is `BAExpand_M_diag`
   (`BAMres_fine_apply` + `BAMB_diag_eq`), the row sum is `lwS_row_sum`; the pathwise identity is `BAExpand_defect_identity`
   (`Ǧ_{xy} f - RHS = -Σ_α M_{xα} Z_α`, `Z_α = Σ_β (H_{αβ} G_{βy} f - S_{αβ} ∂_{h_{βα}}(G_{βy} f))`); (M2) `BAExpand_integral_defect`
   (`E Z_α = 0`, `stein_sample` on `G_{βy} f` with `dhSample_baG`); `BAExpand_integral` is `lanlw` on `Sizes.seqP`; `baLanlw_holds` transports it by
   `lwWx_integral` for `0 < t < 1` and shows both integrands vanish pointwise at `t = 0` (`BAExpand_Gc_zero`, `BAlwS 0 = 0`).
2. The Stein layer is the twin of `lwG`, `lwPoly`, `dhSample_lwG*` (LWStein.lean:469-967) with `H_u` replaced by `g₀Ψ + H_u` (`BAExpand_Hm`); the closed
   forms go through the generic cores `BAExpand_dh_of_partial`, `BAExpand_dh_star_of_partial` (any matrix `Gm` with partials `-√u (Gm D_c Gm)`).
   The bridge twins `baWx_baG`, `baWx_baPoly`, `baWx_dh` copy `lwWx_lwG`, `lwWx_lwPoly`, `lwWx_dh` (LWWeightExp.lean:70-271) at `lwWxSizes d L W 0 hL`.
   No merged file is changed (§57 (1)).
3. Binders fixed (ticket: "the prover fixes binders"): `baGm sz n g0 z u ω`, `baG sz n g0 z u i j ω`, `baVar sz n g0 z u v ω`, `baPoly sz n g0 z u P ω`;
   the lemmas on the Stein layer take `hz : z.im ≠ 0` (the `lw` twins take `0 < z.im`; only `Im z ≠ 0` is used); `dhSample_baG`, `dhSample_baG_star`,
   `baG_tame1`, `baPoly_tame1`, `stein_baPoly` take `g0` after the hypotheses; `baWx_*` take `hL : 3 ≤ L` first. All 12 pinned helper names exist;
   every other helper is prefixed `BAExpand_` (rule E); the unpinned bridge helpers are `BAExpand_bridge_*`. `local macro ba_tame` is local.
4. Instances: (I1) `baS_diag` (`S_{xx} = 1/2`), `baS_row_sum` (`Σ_y S_{xy} = 1/2`); (I2) `baLanlw_t0` (at `t = 0` both integrals are `0`, equal) and two
   `example`s of `baLanlw_holds 3`: A at `g₀ = 0`, `E = 0`, `m = i` with every hypothesis discharged (`baSelf_zero` proves `BASelf 3 3 0 0 i`:
   `M^{(B)} = i I`, `L^{-d} tr = i`), B at `g₀ = 1/2`, `E = 3/10`, `t = 1/2` with `m`, `hSelf` kept as hypotheses of the example: `BASelf_exists`
   (MFixedPoint.lean:691) is stated for `0 < z.im`, so no merged theorem produces `m` at a real energy for `g₀ ≠ 0`. Both use `x = 0`, `y = e₀ ≠ x`.
5. `(M3)` needs exactly `BASelf` (through `M_{ββ} = m`); no hypothesis on `g₀`, `E`; `0 ≤ t < 1` as pinned; `3 ≤ L` only; no constant, no `∀ n`.
6. Registry: the pre-check exits 0 with no unclassified premise; `BAlanlw` is concluded by `baLanlw_holds` (the scan counts it as proved), as `LWweightExp`
   (`RBM3D/Test/Axioms.lean` has 0 hits for both, b.7); no line added, the diff stat lists only `BAExpand.lean`.
7. Cut. The merged twin of target 3 for `(Owx)` is 935 lines (basis above) without an atom counter, `BAVocab_cnt_equiv`, `BAVocab_merge_counters`,
   `BAVocab_baSplitSolid_circ` are `private`, and `lwSampleData` and its edge lemmas are `LData`/`lwG` only; with 596 lines left under 1500, target 3 does
   not fit; nothing of it was written or tested in Lean. The numbers and the (M4) graph forms of (a) rows 8-10 and Commands C, D are what BA-L2a2 starts from.
8. Paper-delta candidates: none new. The pin text is the check-file block; the resolvent-polynomial class (T2040d) and the derivative convention (T2060a)
   apply as in LW-04 (they are documented in the module docstring of LWStein.lean).

## (c) Verified Mathlib names used (`#exists` script, output `true` = present in this Mathlib)
Matrix.mul_sub: true
Matrix.sub_mul: true
Matrix.mul_assoc: true
Matrix.mul_one: true
Matrix.one_mul: true
Matrix.mul_apply: true
Matrix.sub_apply: true
Matrix.neg_apply: true
Matrix.conjTranspose_smul: true
Matrix.IsHermitian.add: true
Matrix.trace_smul: true
Matrix.trace_one: true
Ring.inverse_mul_cancel: true
Ring.mul_inverse_cancel: true
Complex.conj_ofReal: true
Complex.inv_I: true
Complex.I_sq: true
inv_neg: true
ite_true: true
inv_mul_eq_iff_eq_mul₀: true
mul_inv_cancel₀: true
Finset.sum_sub_distrib: true
Finset.mul_sum: true
Finset.sum_mul: true
Finset.sum_neg_distrib: true
Finset.sum_congr: true
Finset.sum_eq_zero: true
MeasureTheory.integral_finsetSum: true
MeasureTheory.integral_sub: true
MeasureTheory.integral_neg: true
MeasureTheory.integral_const_mul: true
MeasureTheory.Integrable.sub: true
MeasureTheory.Integrable.const_mul: true
MvPolynomial.eval_rename: true
MvPolynomial.induction_on: true
MvPolynomial.eval_X: true
MvPolynomial.rename_X: true
HasDerivAt.mul: true
HasDerivAt.add: true
HasDerivAt.congr_deriv: true
HasDerivAt.congr_of_eventuallyEq: true
HasDerivAt.deriv: true
HasDerivAt.differentiableAt: true
hasDerivAt_const: true
if_true: present but deprecated in this Mathlib (Lean warning "`if_true` has been deprecated: Use `ite_true` instead"); the file uses `ite_true`.
Names verified absent: none looked up and missing. Merged project names used (all `true` in the same script): RBM.BA.{BAMres_fine_apply, BAMB_diag_eq, BAcard_Zd, BASelf_exists}, RBM.Gauss.{ring_inverse_smul_one, PsiI_isHermitian, svarF_diag, ztOf_im, continuous_green_of_isHermitian}, RBM.Graph.{lwStein_hasDerivAt_inv, stein_sample, lwS_row_sum, lwWx_integral}, RBM.Green.gaussIBP, RBM.isUnit_sub_smul_of_isHermitian, RBM.norm_inverse_entry_le.

## (d) Open issues and paper-delta candidates
1. Cut BA-L2a2 (dispatcher to number): `BAGraph.lanlwT1`, `BAGraph.lanlwD`, `BAGraph.lanlwTerms`, value identity in expectation (b), `lanlwT1_counters`, `lanlwD_counters`,
   `lanlw_ord`, `lanlw_scalingOrderG`, instances (I3), (I4); not started in Lean. Inputs available from this ticket: `baLanlw_holds`, the Stein layer `baG`, `baPoly`, `dhSample_baG*`, `baWx_*`.
   Facts for its ticket, from (a): the derivative-term graph has coefficient `+Γ.coeff` (row 10, Command C: error 1.0e-09 with `+`, 3.2e+01 with `-`); 18270 terms, min of
   `ordG(Δ) - ord(Γ)` is 0 (row 9, Command D); from the files: the private lemmas of narrative 7 must be re-proved or the ticket must allow editing `BAVocab.lean`.
2. Paper-delta candidates: none (`T2295a`/`T2295b` of the ticket are not needed: `lanlw` needs exactly `BASelf`, and target 3(c) was not attempted in Lean).
3. Existence of `m` for `BASelf` at a real energy and `g₀ ≠ 0` is not a merged theorem (`BASelf_exists` needs `0 < z.im`), so the `g₀ = 1/2` instance keeps `hSelf`.
