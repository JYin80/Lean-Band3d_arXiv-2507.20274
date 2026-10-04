Prover model: claude-sonnet-5-5
## (a) Math preflight — Sun Oct  4 11:31:01 UTC 2026
Scripts (python3 + numpy, outside the repo, no Lean): `S=/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/e2e8bc03-a5c7-4581-b49e-f30bd123d3b2/scratchpad/T2131` (`model.py` = T2107's `svarF`/`sampleX`; `counters.py` imports T2128's `lvl1.py`).
Notation: `D = (G,M,S,Sp)`; `Gamma^T` = swap `src/dst` of every solid and `x/y` of every waved edge; `Gamma^c` = flip `sigma` of every solid edge, coeff `-> conj`, coloured waved `S^+_{xy} -> S^-_{yx}` (colour flipped AND ends swapped, "swap version") or colour flipped only ("no-swap version"); black waved and dotted edges unchanged.

### (i) Exponent table (the targets have no exponents; these are the thresholds, signs and counter changes they rest on)
| quantity | value | constraint | slack |
|---|---|---|---|
| Delta(nS,nW,nV,nM), `owxT1..4` at `x` external | (1,1,1,0), (1,2,2,0), (1,1,1,0), (1,2,2,0) = internal `x` (`counters.py` below; `LWWeightExp.lean:811-838` `owxT*_ord`) | `nM` unchanged: new leaves join the molecule of `x` (external or internal) | script: 300 graphs, identical |
| Delta ord, `owxT1..4` (any `x`) | +1 each (`ord = nS + 2(nW-nV)`) | >= 0 for `lvl1` | +1 |
| conj, transpose | Delta(nS,nW,nV,nM,ord) = 0 | every term keeps its merged `ord` | script: 300 graphs, 0 violations |
| Delta ord, `oe1x` family (selected edge `e0` at `x`) | `oe1xT1_ord`, `owxT1_ord` = +1; `oe1xDs_ord`: +1, or +0 only if `q.1.sigma=false & src=x` or `q.1.sigma=true & dst=x` (`LWEdgeExp.lean:1227-1232`) | >= 0 | tight (0) for the +0 pulls |
| same, after conj / transpose | +0 only if the colour OR the direction of `q.1` at `x` differs from `e0`'s (blue-out: red-out, blue-in; blue-in: red-in, blue-out; red-out: blue-out, red-in; red-in: blue-in, red-out), derived by mapping the merged condition through `K` | >= 0 | tight (0) as merged |
| Delta ord, `oe2xR1..R8` | +1 each (`LWGGExp.lean:1106-1158`) | >= 0 | +1 |
| flow data | `0<Im z`, `0<u`, `m != 0`, `z+u m = -1/m`, `Sp-m^2 Sp S = S`, `M_aa = m` (all merged `*_graph_E`) | DECISIONS §29 grid | instance below: `Im z = 0.5`, residual 0, `1.4e-16` |
| new data hypotheses | `M a b = 0` (a!=b), `M, S, Sp` symmetric (S2 only); `S` real (S1, black waved edges); `Sp` arbitrary for the swap version of S1 | `lwS` is `ofReal` and symmetric (`svarF_comm`); `M = mI`; `Sp = S(1-m^2 S)^-1` symmetric | `|Sp-Sp^T| = 4.9e-17`; for no-swap S1 `Sp` symmetric is needed (alg.py below) |
| flip of coordinates | negate every coordinate `(i,j,false)`; `false` = IMAGINARY part (`FineModel.lean:105-109`: `w(i,j,true) + I w(i,j,false)`) | `gvarF` has no `b` (`FineModel.lean:89-93`), so every coordinate law `gaussianReal 0 v` is symmetric: `seqP` preserved | exact; the ticket's `(if b then -1 else 1)` negates the REAL part: wrong (flip.py below) |
| selected edge circled (T2128 C4) | `(G-M)_{x y1} = G_{x y1} - m 1_{x=y1}` when `M = mI` (`M a b = 0`, `M a a = m`) | merged `oe1x/oe2x` need `circ = false` for `p.1`, `q.1` | term `oe1xT1` (`m 1_{x=y1}`) cancels exactly; circ.py below |
| order of `p`, `q` in `Gamma.solid` | `oe2x_graph_E` needs `p.1 = G_{xy}` before `q.1 = G_{y'x}` in `lwSplit` | in-edge listed first = a different `p` | permuting `solid` leaves `term` unchanged (commutative product): one reorder lemma |

### (ii) One concrete nondegenerate instance
Data: `d=3, L=3, W=1, g=1/2, E=0, t=u=1/2`, `N=(WL)^d=27`; `x` external with label `(0,0,0)` (S3), `y=(1,0,0)`; `M = m I`, `S = lwS` (`t*svarF`), `Sp = S(1-m^2 S)^-1`; `Gamma` = `p2Graph` (S2), `G_{xv}G_{yv}`, `Ǧ_xx f` (S3). `GaussIBP sz` is the proved `gaussIBP` (`Green/IBPPoly.lean:305`): no external hypothesis, no limit computation is owed; no `∀ᶠ`, no window.
`cd $S && python3 inst.py`
```
d=3 L=3 W=1 g=0.5 E=0.0 t=u=0.50  N=(WL)^d=27 (x external, label (0,0,0); y=(1,0,0))
m=1j z=0.5j | Im z = 0.500 > 0: True | u=0.50 > 0: True | m != 0: True | |z + u m + 1/m| = 0.0e+00 | |m|^2 u = 0.50 < 1
hSp: max|Sp - m^2 Sp S - S| = 1.4e-16 | hM: M_aa = m: True | M_ab = 0 (a!=b): True | S real: True, symmetric: True | Sp symmetric: max|Sp-Sp^T| = 4.9e-17 | row sums of S = 0.500
distinct entries: S_aa=0.2000 S_ab(neighbour)=0.0500 ; Sp_aa=0.1581 Sp_ab=0.0341 (nondegenerate, N=27)
```
`cd $S && python3 flip.py` (`Xentry` as `FineModel.lean:105-109` with `idxKey` = natural order; `omega'` = negate the stated Bool coordinate; N=27; E=0, t=1/2):
```
flip b=false (imaginary part):  |X(w') - X^T| = 0.0e+00   |G(w') - G^T| = 7.0e-16
flip b=true (ticket literal):   |X(w') + X^T| = 0.0e+00   |X(w') - X^T| = 3.2e+00   |G(w') - G^T| = 1.6e+00 (|G^T| max 1.65)
```
So `X(omega') = X(omega)^T` and `G(omega') = G(omega)^T` for `false`-flip; the literal `true`-flip gives `X(omega') = -X^T`, hence `(−H^T − z)^{-1} != G^T`.
`cd $S && python3 alg.py` (brute-force `LGraph.val` on 200 random graphs, 2 external + 2 internal vertices, 4 solid / 2 waved / 2 dotted edges of all colours, complex coeff; `D` random, `Sp` non-symmetric unless stated):
```
random graphs (2 ext, 2 int, 4 solid, 2 waved, 2 dotted, all kinds/colours), n=3 labels, 200 trials; max residuals
conj(Gamma.val D) vs Gamma.conj.val D   (swap version, S real, Sp arbitrary)        : 0.00e+00
conj(Gamma.val D) vs Gamma.conj.val D   (no-swap version, Sp NON-symmetric)         : 5.64e+02
conj(Gamma.val D) vs Gamma.conj.val D   (no-swap version, Sp symmetric)             : 0.00e+00
conj(Gamma.val D) vs Gamma.conj.val D   (S not real, swap version)                  : 8.93e+02
ticket literal conj(Gamma.val D) vs Gamma.conj.val (Gbar,Mbar,S,Sp)                 : 3.61e+02
solid+dotted graph, coeff 1: Gamma.val D vs Gamma.conj.val (Gbar,Mbar,..)  (double conjugation): 0.00e+00
Gamma^T.val D^T vs Gamma.val D           (any data)                                 : 0.00e+00
Gamma^T.val D   vs Gamma.val D           (data not transposed)                      : 4.44e+02
symmetric M,S,Sp: Gamma^T.val D vs Gamma.val (G^T, M,S,Sp)                          : 0.00e+00
```
`cd $S && python3 circ.py | tail -1`:
```
circled selected edge, M=mI: max|val(circ) - (val(uncirc) - m*val(dotted x=y1, edge dropped))| over 100 trials = 1.4e-14
```
`cd $S && python3 counters.py` (lvl1 model; `owx_terms` with `x = e0` external vs `i0` internal):
```
conj (swap and no-swap version) and transpose preserve (nS,nW,nV,nM,ord) on 300 random graphs: violations 0
Delta (nS,nW,nV,nM,ord) per term, x external (e0) vs x internal (i0), 300 random graphs each (key: delta -> #graphs):
  owxT1       {(1, 1, 1, 0, 1): 300}
  owxT1(int)  {(1, 1, 1, 0, 1): 300}
  owxT2       {(1, 2, 2, 0, 1): 300}
  owxT2(int)  {(1, 2, 2, 0, 1): 300}
  owxT3       {(1, 1, 1, 0, 1): 1215}
  owxT3(int)  {(1, 1, 1, 0, 1): 1187}
  owxT4       {(1, 2, 2, 0, 1): 1215}
  owxT4(int)  {(1, 2, 2, 0, 1): 1187}
```
`cd $S && python3 mc3.py 100000` (Monte Carlo, both sides of (2) and (3) at the instance; `|diff|/SE` = mean(Gamma - Gamma^T) or mean(LHS-RHS) over its standard error; `pathwise rms` shows the two sides differ sample by sample):
```
(2) d=3 L=3 W=1 g=1/2 E=0 t=1/2, 100000 samples, x=(0,0,0) y=(1,0,0) v=(1,1,0): mean(SE) of Gamma side | Gamma^T side | |diff|/SE
   G_xv G_yv          -8.429e-07+9.853e-05j(1.2e-04) | -3.640e-06+1.018e-04j(1.2e-04) | |diff|/SE = 0.02 ; pathwise rms|a-b| = 5.6e-02
   sum_v G_xv G_xv    -0.9048+0.0004j(0.0035) | -0.9042-0.0009j(0.0035) | |diff|/SE = 0.99 ; pathwise rms|a-b| = 4.5e-01
   G_xx G_xv          +5.574e-05+4.422e-04j(4.2e-04) | -2.637e-04-6.907e-05j(4.2e-04) | |diff|/SE = 1.01 ; pathwise rms|a-b| = 1.9e-01
   p2Graph |f_xy|^2   +2.376e-04+0.000e+00j(1.0e-06) | +2.371e-04+0.000e+00j(1.0e-06) | |diff|/SE = 0.50 ; pathwise rms|a-b| = 3.4e-04
(3) x=(0,0,0) external, 100000 samples: LHS=E[(G-M)_xx f]; T1..T4 = owxT1..owxT4 with x := inl a; LHS-RHS
   f=one        E LHS -0.0010+0.0148j | E(T1+T2) -0.0000+0.0141j | E(T3+T4) +0.0000+0.0000j | E(LHS-RHS) -0.0010+0.0007j (SE 0.0016) |diff|/SE=0.73
   f=G_xy       E LHS -0.0001+0.0001j | E(T1+T2) +0.0000-0.0000j | E(T3+T4) +0.0001+0.0000j | E(LHS-RHS) -0.0001+0.0001j (SE 0.0006) |diff|/SE=0.31
   f=Gbar_xy    E LHS -0.0003+0.0002j | E(T1+T2) -0.0000-0.0000j | E(T3+T4) -0.0000-0.0000j | E(LHS-RHS) -0.0002+0.0003j (SE 0.0005) |diff|/SE=0.82
   f=Gbar_xx    E LHS +0.2837+0.0010j | E(T1+T2) +0.0166-0.0000j | E(T3+T4) +0.2675-0.0002j | E(LHS-RHS) -0.0004+0.0012j (SE 0.0018) |diff|/SE=0.69
   f=Gyx_Gbarxy E LHS -0.0001-0.0000j | E(T1+T2) +0.0000+0.0000j | E(T3+T4) +0.0000-0.0000j | E(LHS-RHS) -0.0001-0.0000j (SE 0.0002) |diff|/SE=0.60
   f=Gxx_Gbaryy E LHS -0.0001-0.1236j | E(T1+T2) -0.0002+0.0059j | E(T3+T4) -0.0001-0.1310j | E(LHS-RHS) +0.0001+0.0014j (SE 0.0031) |diff|/SE=0.47
```

### Verdicts
- **Target 1 (S1 conjugation): PASS, with two corrections to the ticket's wording.** (a) With the data `D.conj = (conj G, conj M, S, Sp)` the stated `conj(Gamma.val D) = Gamma.conj.val D.conj` is FALSE (residual `3.6e+02`; `Gamma.conj.val D.conj = Gamma.val D`, a double conjugation, residual `0` on solid+dotted graphs): the red edge already reads `star` of `G`. The true statement is `conj(Gamma.val D l) = Gamma.conj.val D l` with the SAME `D`, hypotheses `star (D.S i j) = D.S i j` (fails for complex `S`, residual `8.9e+02`) and, for the swap version, nothing on `Sp`; for the no-swap version `Sp` symmetric (residual `5.6e+02` otherwise). The data hypotheses of the merged theorems are applied to `Gamma.conj` with `D` itself, so no "`lwSampleData` with conjugated parameters" is needed: a red expansion is `E Gamma.val = Sum E (T.conj).val` with `T` the merged terms of `Gamma.conj` (coefficients `m -> conj m` come from `coeff -> conj`). (b) Counters and `ord` are conj-invariant (0 violations).
- **Target 2 (S2 transposition): PASS, with a sign correction.** `Gamma^T.val D^T = Gamma.val D` for every `D` (residual 0); with `M,S,Sp` symmetric `Gamma^T.val D = Gamma.val (G^T,M,S,Sp)`. The flip must negate the `b = false` coordinates (imaginary part); the ticket's formula negates `b = true` and gives `X(omega') = -X^T`, not `G^T`. With the correct flip `seqP` is preserved (each `gaussianReal 0 v` symmetric, variance independent of `b`), `Xentry(omega') = conj Xentry(omega) = Xentry(omega)^T` by the case split of `Xentry_swap`'s proof (`idxKey i<j, i=j, j<i`), and `Gres (H^T) z true = (Gres H z true)^T`. Chain: `Gamma^T.val D = Gamma.val D^T` (first identity at `D^T`), `D(omega)^T = D(omega')` (symmetric `M,S,Sp`), then `E F(omega') = E F(omega)` by the measure-preservation. MC: all four statistics agree within `|diff|/SE <= 1.01`, sample-wise they differ.
- **Target 3 (S3 `(Owx)` at external `x`): PASS.** The Stein identity is pointwise in the labels and involves only the label `l(x)` (`owx_term_integral` fixes `l`); the four terms are the merged ones with `x := inl a` (`owxT1..4` with the waved and derivative edges attached to `inl a`), `nM` unchanged because the leaves join `x`'s external molecule; `Delta ord = +1` each (table). Needs only `M_xx = m` (+ the merged hypotheses). MC: six `f` incl. `f = 1` (`G̊_xx`, `T3 = T4 = 0`), `f = Ḡ_xx` (`T3` dominant `+0.27`), all `|diff|/SE <= 0.82`.
- **Target 4 (forms for `strat_local`): PASS** via `K in {id, conj, transpose, conj∘transpose}`: `E Gamma.val D = Sum E (K T).val D` where `T` ranges over the merged terms of `K Gamma` (`K^-1` applied to each term), `K` chosen from the selected edge/weight (blue-out `id`; blue-in `transpose`; red-out `conj`; red-in `conj∘transpose`; red weight `conj`). Needed: S1 (`conj`), S2 (every term `T`: `E (T^T).val = E T.val`, hypotheses `M,S,Sp` symmetric; `hSpT` as an explicit hypothesis, discharged at the instance), `M a b = 0` for `a != b` (selected circled edge: drop `oe1xT1`, row 'circled'), the reorder lemma for `oe2x` (row 'order'). A hypothesis set exists (instance above); no hypothesis is empty or collapsed.

## (b) Script output — Sun Oct  4 12:12:07 UTC 2026
Worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2131`, branch `t/T2131`; `git log --oneline main..t/T2131`: 6d9aae1 T2131: LWSymm docstring fix (flip invariance); 1df0598 T2131: LWSymm selector lemmas, normal-graph support lemma; 6e895e8 T2131: LW-08a Graph/LWSymm (conjugation, transposition, (Owx) at any vertex, forms for strat_local); 48bba26 T2131: WIP LWSymm (instances); fe8eccc T2131: WIP LWSymm (forms a,b,c, counters, selector); 5bc7817 T2131: WIP LWSymm (twists, flip, owxE, forms a,b)
Scripts (outside the repo): `S=/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/e2e8bc03-a5c7-4581-b49e-f30bd123d3b2/scratchpad/T2131` (`stmt.py`, `clash.py`, `axioms.lean`, `precheck.lean`).
```
$ date -u; lake build RBM3D.Graph.LWSymm 2>&1 | tail -1
Sun Oct  4 12:10:37 UTC 2026
Build completed successfully (3364 jobs).
$ lake build 2>&1 | tail -1      # full library (the root RBM3D.lean imports the new module only at the hub merge step)
Build completed successfully (3877 jobs).
$ lake env lean $S/precheck.lean   # import RBM3D; import RBM3D.Graph.LWSymm; #assert_rbm_axioms   (registry pre-check, DECISIONS §20)
exit: 0
axiom audit: 4073 theorems, 1415 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
$ lake env lean $S/axioms.lean     # union over every declaration of the module, then #print axioms of the targets
RBM3D.Graph.LWSymm: 239 declarations (181 theorems); axioms used (union): [Quot.sound, Classical.choice, propext]
'RBM.Graph.LGraph.val_conj' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.lwSymm_conj_integral' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.LGraph.val_transpose' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.lwSymm_flip_measurePreserving' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.lwSymm_lwGm_flip' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.lwSymm_transpose_integral' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.lwSymm_twist_integral' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.owxE_graph_E' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.owxET1_counters' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.lwSymm_weight_graph_E' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.lwSymm_oe1x_graph_E' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.lwSymm_oe2x_graph_E' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.lwSymm_weight_counters' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.lwSymm_oe1x_counters' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.lwSymm_oe2x_counters' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.lwSymm_conj_literal_false' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.lwSymm_flipLit_ne' depends on axioms: [propext, Classical.choice, Quot.sound]
$ git diff --stat main...t/T2131 | tail -2
 RBM3D/Graph/LWSymm.lean | 2326 +++++++++++++++++++++++++++++++++++++++++++++++
 1 file changed, 2326 insertions(+)
$ python3 $S/clash.py   # new public names against every other RBM3D/**/*.lean
new public declarations in RBM3D/Graph/LWSymm.lean : 187 (theorem/def/abbrev/instance names parsed, anonymous examples excluded)
exact-name clashes with the other RBM3D/**/*.lean files: none
```
Ports: none from RBM1D/RBM2D (no `git diff --stat` owed); `owxE_term_integral`, `owxE_graph_E` and the `owxET*` lemmas are the merged `owx_term_integral`, `owx_graph_E`,
`owxT*_{counters,term,ord}`, `owxExt_{nM,reach1,reach2}` of `RBM3D/Graph/LWWeightExp.lean` (T2107, main `b06ff9b`) with `x : I` replaced by `x : E ⊕ I`.

Target statements, extracted from the file by `python3 $S/stmt.py RBM3D/Graph/LWSymm.lean <names>` (whitespace collapsed; `[file:line]`):
```
[RBM3D/Graph/LWSymm.lean:259] theorem LGraph.val_conj (D : LData ι) (hS : ∀ i j, star (D.S i j) = D.S i j) (Γ : LGraph E I) (ℓe : E → ι) : Γ.conj.val D ℓe = star (Γ.val D ℓe)
[RBM3D/Graph/LWSymm.lean:541] theorem lwSymm_conj_integral (hS : ∀ i j, star (S i j) = S i j) (Γ : LGraph E I) (ℓe : E → Idx d (sz.L n) (sz.W n)) : ∫ ω, Γ.conj.val (lwSampleData sz n z u M S Sp ω) ℓe ∂(Sizes.seqP sz) =
    star (∫ ω, Γ.val (lwSampleData sz n z u M S Sp ω) ℓe ∂(Sizes.seqP sz))
[RBM3D/Graph/LWSymm.lean:441] theorem lwSymm_flip_measurePreserving (sz : Sizes d) : MeasurePreserving (lwSymmFlipEquiv sz) (Sizes.seqP sz) (Sizes.seqP sz)
[RBM3D/Graph/LWSymm.lean:417] theorem lwSymm_lwGm_flip (z : ℂ) (u : ℝ) (ω : Sizes.SeqΩ sz) : lwGm sz n z u (lwSymmFlip sz ω) = (lwGm sz n z u ω)ᵀ
[RBM3D/Graph/LWSymm.lean:533] theorem lwSymm_transpose_integral (hM : Mᵀ = M) (hS : Sᵀ = S) (hSp : Spᵀ = Sp) (Γ : LGraph E I) (ℓe : E → Idx d (sz.L n) (sz.W n)) : ∫ ω, Γ.transpose.val (lwSampleData sz n z u M S Sp ω) ℓe
    ∂(Sizes.seqP sz) = ∫ ω, Γ.val (lwSampleData sz n z u M S Sp ω) ℓe ∂(Sizes.seqP sz)
[RBM3D/Graph/LWSymm.lean:558] theorem lwSymm_twist_integral (hSr : ∀ i j, star (S i j) = S i j) (hM : Mᵀ = M) (hS : Sᵀ = S) (hSp : Spᵀ = Sp) (c t : Bool) (Γ : LGraph E I) (ℓe : E → Idx d (sz.L n) (sz.W n)) : ∫ ω,
    (lwSymmTwistG c t Γ).val (lwSampleData sz n z u M S Sp ω) ℓe ∂(Sizes.seqP sz) = lwSymmCj c (∫ ω, Γ.val (lwSampleData sz n z u M S Sp ω) ℓe ∂(Sizes.seqP sz))
[RBM3D/Graph/LWSymm.lean:1157] theorem owxE_graph_E (hG : GaussIBP sz) {z : ℂ} (hz : 0 < z.im) {u : ℝ} (hu : 0 < u) {m : ℂ} (hm0 : m ≠ 0) (hzm : z + (u : ℂ) * m = -m⁻¹) (Sp M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d
    (sz.L n) (sz.W n)) ℂ) (hSp : ∀ i j, Sp i j - m ^ 2 * ∑ w, Sp i w * lwS sz n u w j = lwS sz n u i j) (hM : ∀ a, M a a = m) (Γ : LGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p
    ∈ lwSplit Γ.solid) (x : E ⊕ I) (hx : p.1 = ⟨true, true, x, x⟩) (ℓe : E → Idx d (sz.L n) (sz.W n)) : ∫ ω, Γ.val (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓe ∂(Sizes.seqP sz) = ∫ ω, (owxET1
    m Γ x).val (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓe ∂(Sizes.seqP sz) + ∫ ω, (owxET2 m Γ p x).val (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓe ∂(Sizes.seqP sz) + ((lwSplit p.2).map
    fun q => ∫ ω, (owxET3 m Γ x q).val (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓe ∂(Sizes.seqP sz)).sum + ((lwSplit p.2).map fun q => ∫ ω, (owxET4 m Γ x q).val (lwSampleData sz n z u M (lwS
    sz n u) Sp ω) ℓe ∂(Sizes.seqP sz)).sum
[RBM3D/Graph/LWSymm.lean:1590] theorem lwSymm_weight_graph_E (hG : GaussIBP sz) {z : ℂ} (hz : 0 < z.im) {u : ℝ} (hu : 0 < u) {m : ℂ} (hm0 : m ≠ 0) (hzm : z + (u : ℂ) * m = -m⁻¹) (Sp M : Matrix (Idx d (sz.L n) (sz.W n))
    (Idx d (sz.L n) (sz.W n)) ℂ) (hSp : ∀ i j, Sp i j - m ^ 2 * ∑ w, Sp i w * lwS sz n u w j = lwS sz n u i j) (hSpT : Spᵀ = Sp) (hM : ∀ a, M a a = m) (hM0 : ∀ a b, a ≠ b → M a b = 0) (Γ :
    LGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid) (x : E ⊕ I) (c t : Bool) (hx : lwSymmTwistS c t p.1 = ⟨true, true, x, x⟩) (ℓe : E → Idx d (sz.L n) (sz.W n))
    : ∫ ω, Γ.val (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓe ∂(Sizes.seqP sz) = ∫ ω, (lwSymmOwxT1 c t m Γ x).val (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓe ∂(Sizes.seqP sz) + ∫ ω,
    (lwSymmOwxT2 c t m Γ p x).val (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓe ∂(Sizes.seqP sz) + ((lwSplit p.2).map fun q => ∫ ω, (lwSymmOwxT3 c t m Γ x q).val (lwSampleData sz n z u M (lwS
    sz n u) Sp ω) ℓe ∂(Sizes.seqP sz)).sum + ((lwSplit p.2).map fun q => ∫ ω, (lwSymmOwxT4 c t m Γ x q).val (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓe ∂(Sizes.seqP sz)).sum
[RBM3D/Graph/LWSymm.lean:1639] theorem lwSymm_oe1x_graph_E (hG : GaussIBP sz) {z : ℂ} (hz : 0 < z.im) {u : ℝ} (hu : 0 < u) {m : ℂ} (hm0 : m ≠ 0) (hzm : z + (u : ℂ) * m = -m⁻¹) (Sp M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx
    d (sz.L n) (sz.W n)) ℂ) (hSpT : Spᵀ = Sp) (hM : ∀ a, M a a = m) (hM0 : ∀ a b, a ≠ b → M a b = 0) (Γ : LGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid) (x :
    I) (v : E ⊕ I) (hv : v ≠ Sum.inr x) (c t : Bool) (hx : lwSymmTwistS c t p.1 = ⟨true, p.1.circ, Sum.inr x, v⟩) (hX : p.1.circ = true → ∃ d ∈ Γ.dotted, d.eq = false ∧ ((d.x = p.1.src ∧ d.y =
    p.1.dst) ∨ (d.x = p.1.dst ∧ d.y = p.1.src))) (ℓe : E → Idx d (sz.L n) (sz.W n)) : ∫ ω, Γ.val (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓe ∂(Sizes.seqP sz) = ∫ ω, (lwSymmOe1xT1 c t m Γ p x
    v hv).val (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓe ∂(Sizes.seqP sz) + ∫ ω, (lwSymmOe1xOwx c t m Γ p x).val (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓe ∂(Sizes.seqP sz) + ((lwSplit
    p.2).map fun q => ((lwSymmOe1xDs c t m Γ p x v q).map fun T => ∫ ω, T.val (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓe ∂(Sizes.seqP sz)).sum).sum
[RBM3D/Graph/LWSymm.lean:1690] theorem lwSymm_oe2x_graph_E (hG : GaussIBP sz) {z : ℂ} (hz : 0 < z.im) {u : ℝ} (hu : 0 < u) {m : ℂ} (hm0 : m ≠ 0) (hzm : z + (u : ℂ) * m = -m⁻¹) (Sp M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx
    d (sz.L n) (sz.W n)) ℂ) (hSp : ∀ i j, Sp i j - m ^ 2 * ∑ w, Sp i w * lwS sz n u w j = lwS sz n u i j) (hSpT : Spᵀ = Sp) (hM : ∀ a, M a a = m) (hM0 : ∀ a b, a ≠ b → M a b = 0) (Γ : LGraph E
    I) (x : I) (y y' : E ⊕ I) (hy : y ≠ Sum.inr x) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid) (q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hq : q ∈ lwSplit p.2) (c t :
    Bool) (hp1 : lwSymmTwistS c t p.1 = ⟨true, p.1.circ, Sum.inr x, y⟩) (hq1 : lwSymmTwistS c t q.1 = ⟨true, q.1.circ, y', Sum.inr x⟩) (hX1 : p.1.circ = true → ∃ d ∈ Γ.dotted, d.eq = false ∧
    ((d.x = p.1.src ∧ d.y = p.1.dst) ∨ (d.x = p.1.dst ∧ d.y = p.1.src))) (hX2 : q.1.circ = true → ∃ d ∈ Γ.dotted, d.eq = false ∧ ((d.x = q.1.src ∧ d.y = q.1.dst) ∨ (d.x = q.1.dst ∧ d.y =
    q.1.src))) (ℓe : E → Idx d (sz.L n) (sz.W n)) : ∫ ω, Γ.val (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓe ∂(Sizes.seqP sz) = ∫ ω, (lwSymmOe2xR1 c t m Γ p q x y hy).val (lwSampleData sz n z u
    M (lwS sz n u) Sp ω) ℓe ∂(Sizes.seqP sz) + ∫ ω, (lwSymmOe2xR2 c t m Γ p q x y y').val (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓe ∂(Sizes.seqP sz) + ∫ ω, (lwSymmOe2xR3 c t m Γ p q x).val
    (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓe ∂(Sizes.seqP sz) + ∫ ω, (lwSymmOe2xR4 c t m Γ p q x y y').val (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓe ∂(Sizes.seqP sz) + ∫ ω,
    (lwSymmOe2xR5 c t m Γ p q x y y').val (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓe ∂(Sizes.seqP sz) + ∫ ω, (lwSymmOe2xR6 c t m Γ p q x y y').val (lwSampleData sz n z u M (lwS sz n u) Sp ω)
    ℓe ∂(Sizes.seqP sz) + ((lwSplit q.2).map fun q' => ∫ ω, (lwSymmOe2xR7 c t m Γ p q x y y' q').val (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓe ∂(Sizes.seqP sz)).sum + ((lwSplit q.2).map fun
    q' => ∫ ω, (lwSymmOe2xR8 c t m Γ p q x y y' q').val (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓe ∂(Sizes.seqP sz)).sum
```
Counters and `ord` of every output: `lwSymm_weight_counters`, `lwSymm_oe1x_counters`, `lwSymm_oe2x_counters` (every output `ord Γ + 1`; `oe1xDs` pulls `ord Γ`), `owxET1_counters ... owxET4_ord`.

Compiled nonempty instances (`grep -n "^example" RBM3D/Graph/LWSymm.lean | cut -c1-118`; each at `d = 3, L = 3, W = 1, g = 1/2, E = 0, t = 1/2`, `gaussIBP` proved, every deterministic hypothesis discharged):
```
2078:example : lwSymmInstGraph.conj.val lwSymmInstD ![0, 1] = star (lwSymmInstGraph.val lwSymmInstD ![0, 1]) :=
2082:example : lwSymmInstGraph.conj ≠ lwSymmInstGraph ∧ lwSymmInstGraph.conj.counters = lwSymmInstGraph.counters := by
2088:example : (lwSymmInstGraph.nS, lwSymmInstGraph.nW, lwSymmInstGraph.nV, lwSymmInstGraph.nM) = (4, 3, 1, 0) ∧
2095:example : lwSymmInstGraph.conj.conj = lwSymmInstGraph := lwSymm_conj_conj _
2102:example :
2110:example :
2119:example : (∃ ω : Sizes.SeqΩ lwWxInstSz, lwSymmFlip lwWxInstSz ω ≠ ω) ∧
2144:example := owxE_graph_E (sz := lwWxInstSz) (n := 0) (gaussIBP lwWxInstSz) lwWx_inst_im
2153:example :
2171:example := owxET1_ord (mE 0) (lwSymmInstExtGraph (mE 0)) (Sum.inl 0)
2173:example := owxET2_ord (mE 0) (lwSymmInstExtGraph (mE 0))
2176:example := owxET3_ord (mE 0) (lwSymmInstExtGraph (mE 0))
2180:example := owxET4_ord (mE 0) (lwSymmInstExtGraph (mE 0))
2184:example := lwSymm_flip_measurePreserving lwWxInstSz
2196:example := lwSymm_weight_graph_E (sz := lwWxInstSz) (n := 0) (gaussIBP lwWxInstSz) lwWx_inst_im
2210:example := lwSymm_weight_graph_E (sz := lwWxInstSz) (n := 0) (gaussIBP lwWxInstSz) lwWx_inst_im
2216:example := lwSymm_weight_counters (mE 0) (lwSymmInstRedGraph (mE 0))
2245:example := lwSymm_oe1x_graph_E (sz := lwWxInstSz) (n := 0) (gaussIBP lwWxInstSz) lwWx_inst_im
2252:example : ∃ (c t : Bool) (v : Fin 2 ⊕ Fin 2), v ≠ Sum.inr 0 ∧
2257:example := lwSymm_oe1x_counters (mE 0) (lwSymmInstEdgeGraph (mE 0)) lwSymmInstEdgeP (lwSymmInstEdge_mem _) 0
2263:example : ((lwSplit lwSymmInstEdgeP.2).map fun q =>
2287:example := lwSymm_oe2x_graph_E (sz := lwWxInstSz) (n := 0) (gaussIBP lwWxInstSz) lwWx_inst_im
2293:example := lwSymm_oe2x_counters (mE 0) (oe2xInstGraph (mE 0)) lwSymmInstPairP lwSymmInstPairQ (lwSymmInstPair_hp 
2317:example := lwSymm_oe2x_graph_E (sz := lwWxInstSz) (n := 0) (gaussIBP lwWxInstSz) lwWx_inst_im
```
Instance map: (1) S1 on a record with both colours, coloured and black waved edges, a `×`-dotted edge, coefficient `1 + i`: lines 2078-2095; (2) S2 on `p2Graph`: 2102 (conjugate version 2110, flip 2119); (3) `(Owx)` at the
external weight `Ǧ_{aa} G_{ax}`, `a = inl 0` (label fixed): 2144, counters `(3,1,2,1)`: 2153, `owxET*_ord`: 2171-2180; (4a) red light-weight, external 2196 / internal 2210;
(4b) circled red in-edge, `c = t = true`: 2245; (4c) transposed blue pair `c = false, t = true`: 2287, red pair `c = true, t = false`: 2317. The list `[1, 2, 2, 1]` (2263, `decide`) is the
number of `oe1xDs` graphs for the four other edges, i.e. the preflight row "+0 only if exactly one of colour and direction differs".

Narrative
1. New file `RBM3D/Graph/LWSymm.lean` (2326 lines; module has 239 declarations, 181 theorems), only writable file changed; `Test/Axioms.lean` untouched (no new `Prop`-valued hypothesis).
2. S1: `LGraph.conj` flips `σ`, sends a coloured waved `S^+_{xy}` to `S^-_{yx}` (ends swap), keeps black waved and dotted edges, `m ↦ m̄`. `LGraph.val_conj : Γ.conj.val D ℓe = star (Γ.val D ℓe)`
   needs only `D.S` real (nothing on `S⁺`); in expectation `lwSymm_conj_integral` (`lwS` is real). The ticket's reading with conjugate data `D.conj = (Ḡ, M̄, S, S⁺)` is FALSE
   (conjugates twice): `lwSymm_conj_literal_false` (one blue edge `G_{01} = i`: `-i` against `i`). The preflight's correction (a) is therefore compiled, not only simulated.
3. S2: the flip negates the coordinates `b = false`, which are the imaginary parts (`Xentry`, `FineModel.lean:105-109`); `lwSymm_Xentry_flip : X(ω')_{ij} = X(ω)_{ji}`. The ticket's
   `(if b then -1 else 1)` negates the real parts: `lwSymm_Xentry_flipLit : X(ω') = -X(ω)ᵀ`, `lwSymm_flipLit_ne`. Invariance of `seqP`: `Measure.infinitePi_map_pi` with
   `(gaussianReal 0 v).map (±1 · ) = gaussianReal 0 v` (a centred Gaussian is symmetric; the equal variances of `b = true/false` are not used), then `MeasurePreserving.integral_comp'`.
   `Gres Hᵀ z true = (Gres H z true)ᵀ` (`lwSymm_Gres_transpose`) gives `G(ω') = G(ω)ᵀ`; `lwSymm_transpose_integral` needs `Mᵀ = M`, `Sᵀ = S`, `S⁺ᵀ = S⁺` (all true at `M = m I`,
   `S = lwS`, `S⁺ = lwSplus`: `lwSymm_M_symm`, `lwSymm_lwS_symm`, `lwSymm_lwSplus_symm`, proved from `lwS_isUnit`).
4. S3: the Stein identity only reads the label of the weight's vertex, so `owx_term_integral`/`owx_graph_E` are re-proved for `x : E ⊕ I` (`owxE_term_integral`, `owxE_graph_E`);
   `owxT1 .. owxT4` are the instances at `inr x` (`owxET*_inr`, `rfl`). `n_M` is unchanged also for an external `x` (retraction `lwSymmRho` sends the new vertices to `x`).
5. Forms: `lwSymm_{weight,oe1x,oe2x}_graph_E` apply the merged expansion to the frame `Γ' = (Γ with the selected edges uncircled)^{(c,t)}` and carry every output back by
   `lwSymm_twist_integral`; the output graphs are the functions `lwSymmOwxT1..4`, `lwSymmOe1xT1/Owx/Ds`, `lwSymmOe2xR1..R8` of the ORIGINAL `Γ, p, q`. Selector `(c,t)`: `c` iff the selected
   edge is red, `t` iff it is an in-edge of `x`; `lwSymm_selector_edge`, `lwSymm_selector_pair` produce it, `lwSymm_twist_{out,in,pair_in,pair_out,weight}` are the four cases. The pair
   `G_{yx} G_{xy'}` (in-edge first) is reached by `t = true`, so no reorder lemma is needed. A circled selected non-loop edge needs `M a b = 0` and a `×`-dotted edge between its ends
   (`hX`, `lwSymmUncirc_val`; `lwSymm_hX_of_normal` gives it for every normal graph); with uncircled edges `hX` is vacuous. Twists keep `(n_S, n_W, n_V, n_M)` (`lwSymmTwistG_counters`),
   loops and degrees (`lwSymmTwistS_loop`, `lwSymmTwistS_at`), so the termination measure of T2128 is the merged one.
6. Not done (outside the ticket): the dotted-edge partition of the outputs, `PGraph` packaging (the `oe1xT1`/`R1` outputs live on `{i // i ≠ x}`), the loop case `y₁ = x` (`oe1x_graph_E_loop`;
   `strat_local` Step 2 has no weights), several selected edges at once (the merged identities take one `p ∈ lwSplit Γ.solid`).
7. Section (a) was not edited; its four verdicts hold and its two wording corrections (the conjugate data, the sign of the flip) are the ones compiled above; no (a′) is needed.

## (c) Verified Mathlib names (compiled in `LWSymm.lean`; paths under `.lake/packages/mathlib/Mathlib/`)
- `MeasureTheory.Measure.infinitePi_map_pi` (`Probability/ProductMeasure.lean:482`), `MeasureTheory.MeasurePreserving.integral_comp'`, `MeasureTheory.Measure.map_id`, `Measurable.of_eval`.
- `ProbabilityTheory.gaussianReal_map_neg` (`Probability/Distributions/Gaussian/Real.lean:360`), `MeasureTheory.integral_conj` (`MeasureTheory/Integral/Bochner/ContinuousLinearMap.lean:173`).
- `Matrix.transpose_nonsing_inv` (`LinearAlgebra/Matrix/NonsingularInverse.lean:202`), `Matrix.nonsing_inv_eq_ringInverse` (`:195`), `Matrix.transpose_smul`, `Matrix.transpose_mul`.
- `Ring.mul_inverse_cancel`, `Ring.inverse_mul_cancel`, `map_list_prod`, `map_list_sum`, `List.prod_eq_zero`, `List.any_map`, `List.map_congr_left`, `decide_eq_decide`, `Bool.cond_true`, `Bool.cond_false`.
- Verified absent by `clash.py` / `grep` (no declaration of these in RBM3D): `SEdge.conj`, `SEdge.transpose`, `WEdge.conj`, `WEdge.transpose`, `LGraph.conj`, `LGraph.transpose`, `LData.transpose`, every `owxE*`, `lwSymm*`.
- Deprecated names avoided: `cond_true`/`cond_false` (use `Bool.cond_true`), `measurable_pi_lambda` (use `Measurable.of_eval`), `if_true`/`if_false` (use `ite_true`/`ite_false`).

## (d) Open issues and paper-delta candidates
- `T2131a`: the flip of `Gauss/FineModel.lean:105-109` negates the imaginary parts `(i, j, false)`; the ticket's formula negates the real parts and gives `X(ω') = -X(ω)ᵀ` (compiled, `lwSymm_flipLit_ne`).
- `T2131b`: `Γ.conj.val D = conj (Γ.val D)` with the same data `D`; the reading with conjugate data is false (`lwSymm_conj_literal_false`).
- `T2131c`: `WEdge.conj` swaps the ends of a coloured waved edge (`conj S^+_{xy} = S^-_{yx}`, from `WEdge.val`); black edges stay since `S` is real.
- `T2131d`: `(Owx)` is stated for any vertex `x : E ⊕ I`; the merged `owxT1 .. owxT4` are its internal case (`owxET*_inr`).
- `T2131e`: circled non-loop selected edges (T2128 (a) C4) are handled by `M a b = 0` plus a `×`-dotted edge between the ends (`hX`), not by cancelling the `m δ_{xy}` term (a normal graph has a `×`-dotted edge between the ends of every non-loop solid edge: `defnlvl0` (iii), `LGraph.Normal`, `lwSymm_hX_of_normal`).
- `T2131f`: the transposed forms carry `S⁺ᵀ = S⁺` as a hypothesis (also in `lwSymm_oe1x_graph_E`, where `S⁺` does not occur in the expansion but may occur on waved edges of `Γ`); `lwSymm_lwSplus_symm` proves it for `S⁺ = lwSplus`.
- For T2128 (`LocStep`): call `lwSymm_selector_edge` / `lwSymm_selector_pair` for `(c, t)`; red outputs carry `star m` coefficients (the twist conjugates the coefficient); partition the OUTPUTS (already twisted back).
- Open: the forms handle one selected edge or pair (`p ∈ lwSplit Γ.solid`); a consumer that wants the paper's multi-edge notation `𝒢 = ∏ G_{xy_i} ...` selects one factor, as in the merged theorems.
