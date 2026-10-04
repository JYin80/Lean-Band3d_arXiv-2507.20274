Prover model: claude-sonnet-5-5

## (a) Math preflight — Sun Oct  4 08:17:28 UTC 2026

Setting: `d ≥ 3`, `L ≥ 3`, `W ≥ 1`, `N = (WL)^d`, lattice `Idx = Z_{WL}^d`, block of `x` = `x / W` (`Defs/Sizes.lean:blk`), `d_B(x,y)` = periodic `ℓ¹` distance of the blocks (`zdistD`). `S = t·svarF`, `S⁺ = S (1 − m²S)⁻¹` (`LWPins_lwSp`; `lwSplus`), `m = mE E`, `a₀ = (1+2dg²)⁻¹`, `svarF = W^{-d}·SBR_{ab}`, `SBR = a₀ (same block) | g²a₀ (adjacent) | 0`.

### Exact statements (mathematics)
**T1** (`eq:estSpm-W`). Assume `0<g≤Λ`, `0≤t<1`, `|E| ≤ 2−κ`, `κ>0`. Then `∃ c, C₀ >0` (depending on `d, Λ, κ` only) with `|S_xy| ≤ C₀W^{-d}e^{-c d_B}`, `|S⁺_xy| ≤ C₀W^{-d}e^{-c d_B}` for all `x,y`, `L,W,t,E,g`. Proof: `S⁺ = Σ_k m^{2k}S^{k+1}` (`‖m²S‖_{∞→∞} ≤ t<1`); with `Lift(B)_xy := W^{-d}B_{[x][y]}` multiplicative, `S⁺ = t·Lift(SB·Θ_{tm²})`, `Θ_ξ = (1−ξSB)⁻¹` (`Theta`, `Theta_eq_tsum`). `SB(a,c)≠0` only for `|a−c|≤1` (`2d+1` values, each `≤1`), `Θ(c,b)=Θ(0,b−c)` (`Theta_apply_add_right_of_three_le`), merged `prop5Short_holds d Λ κ''` with `κ'' = √(κ(4−κ))/2 ≤ Im m` gives `|Θ(0,a)| ≤ C_s(1_{a=0}+g²e^{-c_s|a|})≤C_s(1+Λ²)e^{-c_s|a|}`, `|b−c|≥|b−a|−1`: `C₀ = max(1,(2d+1)(1+Λ²)C_s e^{c_s})`, `c=c_s`. `S`: `svarF ≤ W^{-d}` (`a₀≤1`, `g²a₀<1/2d`), supported on `d_B≤1`. Consequences (`expC` of `Defs/RadialSum.lean:271`, `Σ_{b∈Z_L^d}e^{-c|b|} ≤ expC(d−2,c)`, `W^d` points per block): `Σ_y|w_xy| ≤ C₁ := C₀·expC(d−2,c)` and the same for `Σ_x` (symmetric RHS). Paper form `e^{-c|x−y|/W}`: `|x−y|/W ≤ d_B + d`, factor `e^{cd}`.
**T2** (`scalemole`, exact form). (2a, peeling, **needed by T3**): `ι` finite, `K:ι→ι→ℝ≥0` with `K≤K₀W^{-d}`, `Σ_yK(x,y)≤K₁`, `Σ_yK(y,x)≤K₁`; `I` finite, `p : I → Option(E⊕I)` acyclic (rank function). Then `Σ_{ℓ:I→ι}∏_vK(ℓ_v,ℓ_{p v}) ≤ |ι|^{#none}·K₁^{#some}`. (2b, paper form): `Σ_{y: d_B(x,y)≥R}|S⁺_xy| ≤ C₁(c/2)·e^{-cR/2}` (`e^{-cd}≤e^{-cR/2}e^{-cd/2}`); at `R=(log W)^{3/2}` this is `e^{-c'(log W)^{3/2}}`. The confinement of the non-free vertices to `W(log W)^{3/2}` (`7_8:258`) is NOT needed for the deterministic claim (see T3); (2b) is its exact content.
**T3** (`claim:size`, deterministic). `Γ` normal (`LGraph.Normal`), `D : LData ι`, `ι=Idx d L W`: (h1) `D.M x y = (if x=y then m else 0)`; (h2) `x≠y → ‖D.G x y‖ ≤ Ψ`; (h3) `‖D.G x x − m‖ ≤ Ψ` (the entry bound, `(GiiGEX)`/`(GijGEX)` + `(initialGT2)`, as hypotheses); (h4) T1 bounds for `D.S`, `D.Sp` (`K₀W^{-d}`, row/column sums `K₁`). Then for every `ℓe`: `‖Γ.val D ℓe‖ ≤ ‖Γ.coeff‖·K₁^{nV−nM}·K₀^{nW−(nV−nM)}·Γ.scalingSize Ψ W d L`, `Ψ≥0` arbitrary. No `N^τ`, no `log W`, no `ℓ`-decay of solid edges and no `Ψ`-window is needed. Proof: each term `|term| ≤ |coeff|Ψ^{nS}∏|waved|·∏dotted`: a non-loop solid edge has `ℓu≠ℓv` on the support of its `×`-dotted edge (`Normal` (iii)), so `|G−M|_{xy}=|G_xy|≤Ψ`; loops are circled (`Normal` (iv)): `|G_xx−m|≤Ψ`; the `×`-dotted factors are `≤1`. Waved graph on `E⊕I`: components = molecules (`Normal` (ii): no `=`-dotted edge). Rooted forest: root = an external vertex of the molecule, else one internal vertex (free vertex), parent by BFS depth: `nV−nM` tree edges (`≤ nW`). Non-tree waved edges (also loops): `K₀W^{-d}` each; tree edges: (2a) with `N^{nM}K₁^{nV−nM}`. Total `N^{nM}W^{-d(nW−nV+nM)} = (L^d)^{nM}W^{-d(nW−nV)}` (`N=(WL)^d`, exact). General graph: `Γ.val = Σ_{P∈partition m}P.val` (`val_eq_partition`, needs only `D.M x x = m`), each `P.g` normal (`partition_normal`), `‖P.val‖≤‖P.g.val‖` uniformly: `‖Γ.val‖ ≤ (Σ_P C_P)·scalingSizeG m Ψ W d L`. Probabilistic form: if `Ψ' ≤ N^τΨ` then `size(Ψ') ≤ N^{τ nS}size(Ψ)`.

### (i) Exponent table
| item | value | constraint | slack |
|---|---|---|---|
| `nS,nW,nV,nM` `p2Graph` (`LWVocab:241`) | 6,2,4,2 | `nV−nM ≤ nW` (tree edges) | `nW−nV+nM = 0` |
| `figGraph` (`LWVocab:266`) | 8,4,6,2 | same | `0` |
| size identity | `N^{nM}W^{-d(nW−nV+nM)} = (L^d)^{nM}W^{-d(nW−nV)}` | exact, `N=(WL)^d` | `0` (algebra) |
| `κ''` | `√(κ(4−κ))/2` | `κ'' ≤ Im m(E)=√(4−E²)/2` iff `|E|≤2−κ` | equality at `|E|=2−κ`; `κ=1/2`: `κ''=0.6614`, `E=0`: `Im m=1` |
| `(C_s,c_s)` | existential in `prop5Short_holds d Λ κ''` | depend on `(d,Λ,κ'')` only | numerical value not available; measured below |
| `C₀` (sup constant) | `max(1,(2d+1)(1+Λ²)C_s e^{c_s})` | `|S⁺|≤C₀W^{-d}e^{-c d_B}` | measured `W^d max|S⁺|=0.158` (instance) |
| `C₁` (row/col sum) | `C₀·expC(d−2,c_s)` | `Σ|S⁺|≤C₁` | measured `0.427` (instance); `2.51` (g=1,1−t=1e-3,E=0) |
| `S` constants | `K₀=1`, `K₁=t≤1` | `svarF≤W^{-d}`, row sum 1 (`lwS_row_sum`) | measured `W^d max S=0.2`, row sum `0.5` |
| `g` | `0<g≤Λ` | pin 5s needs `0<g` (`Propagator/Pins.lean:47`); `g≤0` is NOT covered by it (`g=0` needs a separate block-diagonal argument) | ticket's "every `g`" is restricted to `0<g≤Λ` |
| `E` | `|E|≤2−κ`, `κ>0` | ticket/§29 write `|E|<2`: false uniformly (script 3) | constants depend on `κ` |
| `t` | `0≤t<1`; `L≥3`, `W≥1`, `d≥3` | `‖tm²‖=t<1`, `Ψ` unconstrained (`Ψ≥0`) | `t=0` trivial |
| constants of T3 | `‖coeff‖K₁^{nV−nM}K₀^{nW−nV+nM}` | depend on `Γ,d,Λ,κ` only | no `L,W,t,E,g` |
| `scalemole` radius | block radius `R=(log W)^{3/2}` | tail `e^{-cR/2}≤W^{-D}` iff `c(log W)^{1/2}/2 ≥ D` | eventually in `W` (not used by T3) |
| external window `Ψ` | paper `W^{-d/2}≤Ψ≤W^{-ε₀}`; `W=2,d=3`: `W^{-d/2}=0.3536` | only for `scalingSize_le` | instance uses `Ψ=0.01` and `Ψ=0.4` |

### (ii) Concrete nondegenerate instance
`d=3, L=4, W=2` (`N=512`), `g=1/2, E=0, t=1/2, Λ=1, κ=1/2`; T3 on `p2Graph`, `x=0`, `y=(4,0,0)`, `G = m·I + Ψ·J` (all entries `≠0`, `|G_xy|=|G_xx−m|=Ψ`), `M=mI`. The merged `prop5Short_holds` is proved (no external limit needed for T1); the entry bound is a hypothesis of T3 and is checked on samples below.
`python3 inst.py` (scratch `T2124/inst.py`):
```
hyp: 3<=d True; 3<=L True; W>=1 True; 0<g<=Lam True; 0<=t<1 True; |E|<=2-kap True; |m|=1.000000; kappa''=0.6614 <= Im m=1.0000: True; |t m^2|=0.500<1
Ring.inverse form vs Neumann series (60 terms), max diff: 3.885780586188048e-16
T1: max_{x,y} W^d|S_xy| = 0.2  (<= t*max(a0,g^2 a0) = 0.2 ); row sum S = 0.5 (= t = 0.5 )
T1: max_{x,y} |S+_xy|/(W^-d e^{-c dB}), c=1 : 0.1577346264846296
T1: max W^d|S+| = 0.1577346264846296 ; row sums max_x sum_y|S+_xy| = 0.4265803640803645 ; col sums = 0.42658036408037714
T1: symmetric: max|S+ - S+^T| = 7.424616477180734e-16
T2b: tail max_x sum_(dB>=R=1.0) |S+_xy| = 0.2688  vs total row sum 0.4266
T3 p2Graph (nS,nW,nV,nM)=(6,2,4,2), Psi=0.01 (W^-d/2=0.3536): |val|=6.502500e-08 size=2.621440e-07 ratio=0.2481 <= peeling const t^2=0.2500*(W^d smax)^0=0.2500: True
T3 p2Graph (nS,nW,nV,nM)=(6,2,4,2), Psi=0.4 (W^-d/2=0.3536): |val|=2.663424e+02 size=1.073742e+03 ratio=0.2481 <= peeling const t^2=0.2500*(W^d smax)^0=0.2500: True
```
The peeling constant is nearly attained (0.2481 vs 0.2500): the claim is sharp here. Ratios `|S⁺_xy|/(W^{-d}e^{-c d_B})`, `d=3,L=4,W=2` (`python3 splus.py`, columns: `c=1` `S⁺` | `c=1` `S` | `c=1/2` `S⁺` | fine `|x−y|/W`, `c=1/2` | `W^d max|S⁺|` | max row sum; identity `S⁺ = t·Lift(SBΘ)` error in last column was `≤8.5e-16` on all 12 rows):
```
g  1-t   E   | c=1:S+  S   | c=.5 S+ | fine c=.5 | W^d max | rowsum
0.5 1e-01 0.0 | 0.2439 0.3600 | 0.2439 | 0.5163 | 0.2439 | 0.7073
0.5 1e-01 1.5 | 0.3335 0.3600 | 0.3335 | 0.7061 | 0.3335 | 1.0748
0.5 1e-03 0.0 | 0.2616 0.3996 | 0.2616 | 0.5539 | 0.2616 | 0.7730
0.5 1e-03 1.5 | 0.3628 0.3996 | 0.3628 | 0.7680 | 0.3628 | 1.1928
1.0 1e-01 0.0 | 1.4059 0.3495 | 0.2185 | 0.4625 | 0.1325 | 1.8467
1.0 1e-03 0.0 | 3.1264 0.3879 | 0.2572 | 0.5444 | 0.1560 | 2.5073
1.0 1e-03 1.5 | 1.0307 0.3879 | 0.1844 | 0.3904 | 0.1605 | 1.5124
```
(output condensed: header shortened, rows with `E=1.0` and two others omitted for length; all 12 rows had every ratio `≤3.13`, max row sum `2.51`.)
`python3 graphs.py check` then `graphs.py 1.0 0.5 0.0 1000` and `graphs.py 0.5 0.9 1.0 1000` (complex Hermitian `H_t`, `E|h_xy|²=t·svarF`, `G=(H_t−z_t)⁻¹`, `Ψ` = sample `max|G−m|`; contraction of `figGraph`/`p2Graph` checked against the brute-force sum at `n=5`):
```
contraction vs brute force (n=5, random data), p2/fig: [5.8e-15, 3.5e-13]
g=1.0 t=0.5 E=0.0 samples=1000 N=512 x=0 y=(4,0,0)
p2Graph  (6,2,4,2): |val|/size min=1.708e-14 median=1.505e-10 max=3.250e-09  peeling bound=2.500e-01  max<=bound: True
figGraph (8,4,6,2): |val|/size min=1.715e-15 median=7.936e-14 max=8.029e-13  peeling bound=6.250e-02  max<=bound: True
g=0.5 t=0.9 E=1.0 samples=1000 N=512 x=0 y=(4,0,0)
p2Graph  (6,2,4,2): |val|/size min=2.321e-12 median=1.224e-09 max=4.208e-08  peeling bound=8.100e-01  max<=bound: True
figGraph (8,4,6,2): |val|/size min=6.556e-13 median=4.400e-11 max=4.502e-10  peeling bound=6.561e-01  max<=bound: True
```
Script 3, `python3 edge.py` (`d=3,g=1,t=0.999,W=1`, `sup_y|S⁺_{0y}|/e^{-0.5|y|}`, the constant needed at fixed rate `c=1/2`): it grows without bound as `E→2` and with `L`, so no `E`-uniform constant exists on `|E|<2`:
```
L=6  E=0.0:0.245 E=1.5:0.186 E=1.9:0.277 E=1.99:1.058 E=1.999:5.883 E=1.99999:63.922
L=14 E=0.0:0.245 E=1.5:0.186 E=1.9:0.277 E=1.99:0.684 E=1.999:44.611 E=1.99999:1836.594
```

### Verdicts
- **T1: PASS** with hypotheses `0<g≤Λ`, `|E|≤2−κ` (the ticket's `|E|<2`, "every `g`" are false/uncovered, see table and script 3); constants `(d,Λ,κ)`; proved from merged `prop5Short_holds`; no extra input.
- **T2: PASS** in the form (2a)+(2b); the `W(log W)^{3/2}`-confinement of `7_8:258` is replaced by the `L¹` peeling bound (sharper, deterministic); delta candidate `T2124a`.
- **T3: PASS** in the deterministic form above, with no `ℓ`-decay hypothesis on solid edges, no `N^τ` loss; hypotheses h1–h4 are the whole input. Delta candidates `T2124b` (no `N^τ`), `T2124c` (`g>0`, `|E|≤2−κ`).

## (b) Script output (stage 1b, Sun Oct  4 10:18:01 UTC 2026)
```
$ git log -1 --format="%h %s" t/T2124; git diff --stat main...t/T2124
ddcbbcd T2124: LW-09 Graph/LWSizeClaim (claim:size, (eq:estSpm-W), scalemole)
 RBM3D/Graph/LWSizeClaim.lean | 1484 ++++++++++++++++++++++++++++++++++++++++++
 1 file changed, 1484 insertions(+)
$ lake build RBM3D.Graph.LWSizeClaim 2>&1 | tail -3   # the `Note:` line ends the style warnings of the replayed dependency RBM3D/Green/LDEQuad.lean; `grep -c LWSizeClaim.lean` of the full output: 0
Note: This linter can be disabled with `set_option linter.style.show false`
✔ [3346/3346] Built RBM3D.Graph.LWSizeClaim (5.4s)
Build completed successfully (3346 jobs).
$ lake env lean precheck.lean > precheck.out; echo exit=$?; sed -n 1,3p precheck.out; grep -c error precheck.out   # precheck.lean = import RBM3D; import RBM3D.Graph.LWSizeClaim; #assert_rbm_axioms
exit=0
axiom audit: 3872 theorems, 1355 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
All within [propext,
 Classical.choice,
0
$ lake build   # full library (root RBM3D.lean, #assert_rbm_axioms)
Build completed successfully (3872 jobs).
exit=0
$ grep -c "sorry\|admit\|native_decide\|^axiom" RBM3D/Graph/LWSizeClaim.lean
0
```

Axioms of the targets (the registry pre-check above also covers every declaration of `RBM`: "All within [propext, Classical.choice, Quot.sound]").
```
$ lake env lean axioms.lean   # #print axioms <targets>; the `depends on axioms:` words are cut by sed
'RBM.Graph.lwSpOf_decay_E' [propext, Classical.choice, Quot.sound]
'RBM.Graph.lwKBound_E' [propext, Classical.choice, Quot.sound]
'RBM.Graph.LWPins_lwSp_decay' [propext, Classical.choice, Quot.sound]
'RBM.Graph.lwSplus_decay' [propext, Classical.choice, Quot.sound]
'RBM.Graph.lwForest_sum_le' [propext, Classical.choice, Quot.sound]
'RBM.Graph.LGraph.exists_forest' [propext, Classical.choice, Quot.sound]
'RBM.Graph.LGraph.waved_sum_le' [propext, Classical.choice, Quot.sound]
'RBM.Graph.lwKernel_tail' [propext, Classical.choice, Quot.sound]
'RBM.Graph.lwTail_log32' [propext, Classical.choice, Quot.sound]
'RBM.Graph.lwClaimSize' [propext, Classical.choice, Quot.sound]
'RBM.Graph.lwClaimSizeG' [propext, Classical.choice, Quot.sound]
'RBM.Graph.lwClaimSize_E' [propext, Classical.choice, Quot.sound]
'RBM.Graph.lwClaimSizeG_E' [propext, Classical.choice, Quot.sound]
```

Target statements, extracted by script.
```
$ python3 extract.py <names>   # statements copied from RBM3D/Graph/LWSizeClaim.lean (line numbers; text up to `:= by`)
-- :461
theorem lwSpOf_decay_E (d : ℕ) (hd : 3 ≤ d) (Λ κ : ℝ) (hΛ : 0 < Λ) (hκ : 0 < κ) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ (L W : ℕ) [NeZero L] [NeZero W], 3 ≤ L →
      ∀ g t E : ℝ, 0 < g → g ≤ Λ → 0 ≤ t → t < 1 → |E| ≤ 2 - κ →
        (∀ x y : Idx d L W, ‖lwSmat d L W g t x y‖ ≤
            C * ((W : ℝ) ^ d)⁻¹ * Real.exp (-(c * (lwBdist d L W x y : ℝ)))) ∧
        ∀ x y : Idx d L W, ‖lwSpOf d L W g t (mE E) x y‖ ≤
            C * ((W : ℝ) ^ d)⁻¹ * Real.exp (-(c * (lwBdist d L W x y : ℝ)))
-- :475
theorem lwKBound_E (d : ℕ) (hd : 3 ≤ d) (Λ κ : ℝ) (hΛ : 0 < Λ) (hκ : 0 < κ) :
    ∃ K₀ K₁ : ℝ, 0 < K₀ ∧ 0 < K₁ ∧ ∀ (L W : ℕ) [NeZero L] [NeZero W], 3 ≤ L →
      ∀ g t E : ℝ, 0 < g → g ≤ Λ → 0 ≤ t → t < 1 → |E| ≤ 2 - κ →
        LWKBound (lwSmat d L W g t) (K₀ * ((W : ℝ) ^ d)⁻¹) K₁ ∧
        LWKBound (lwSpOf d L W g t (mE E)) (K₀ * ((W : ℝ) ^ d)⁻¹) K₁
-- :388
def LWKBound {ι : Type*} [Fintype ι] (K : Matrix ι ι ℂ) (a K₁ : ℝ) : Prop :=
  (∀ x y, ‖K x y‖ ≤ a) ∧ (∀ x, ∑ y, ‖K x y‖ ≤ K₁) ∧ (∀ y, ∑ x, ‖K x y‖ ≤ K₁)
-- :637
theorem lwForest_sum_le [Nonempty ι]
    (ℓe : E → ι) (u v : J → E ⊕ I) (f : J → ι → ι → ℝ) (a K : ℝ) (ha : 0 ≤ a) (hK : 0 ≤ K)
    (hf0 : ∀ j x y, 0 ≤ f j x y) (hfa : ∀ j x y, f j x y ≤ a)
    (hrow : ∀ j x, ∑ y, f j x y ≤ K) (hcol : ∀ j y, ∑ x, f j x y ≤ K)
    (C : Finset I) (par : I → E ⊕ I) (edge : I → J) (ρ : I → ℕ) (hinj : Set.InjOn edge C)
    (hedge : ∀ c ∈ C, (u (edge c) = Sum.inr c ∧ v (edge c) = par c) ∨
      (v (edge c) = Sum.inr c ∧ u (edge c) = par c))
    (hrank : ∀ c ∈ C, ∀ w, par c = Sum.inr w → ρ w < ρ c) :
    (Fintype.card ι : ℝ) ^ C.card * ∑ ℓ : I → ι,
        ∏ j, f j (Sum.elim ℓe ℓ (u j)) (Sum.elim ℓe ℓ (v j))
      ≤ (Fintype.card ι : ℝ) ^ Fintype.card I * K ^ C.card * a ^ (Fintype.card J - C.card)
-- :974
theorem LGraph.waved_sum_le (Γ : LGraph E I) (hN : Γ.Normal) (D : LData ι) {a K₁ : ℝ}
    (hS : LWKBound D.S a K₁) (hSp : LWKBound D.Sp a K₁) (ℓe : E → ι) :
    ∑ ℓi : I → ι, (Γ.waved.map fun e => ‖WEdge.val D (Sum.elim ℓe ℓi) e‖).prod ≤
      (Fintype.card ι : ℝ) ^ Γ.nM * K₁ ^ (Γ.nV - Γ.nM) * a ^ (Γ.nW - (Γ.nV - Γ.nM))
-- :1248
theorem lwKernel_tail (hd : 3 ≤ d) {C c : ℝ} (hC : 0 ≤ C) (hc : 0 < c)
    {K : Matrix (Idx d L W) (Idx d L W) ℂ}
    (h : ∀ x y, ‖K x y‖ ≤ C * ((W : ℝ) ^ d)⁻¹ * Real.exp (-(c * (lwBdist d L W x y : ℝ))))
    (x : Idx d L W) (R : ℝ) :
    ∑ y ∈ Finset.univ.filter (fun y => R ≤ (lwBdist d L W x y : ℝ)), ‖K x y‖ ≤
      C * expC (d - 2) (c / 2) * Real.exp (-(c * R / 2))
-- :1285
theorem lwTail_log32 {c : ℝ} (hc : 0 < c) (D : ℝ) :
    ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W →
      Real.exp (-(c * (Real.log W) ^ ((3 : ℝ) / 2) / 2)) ≤ (W : ℝ) ^ (-D)
-- :1118
theorem lwClaimSize (Γ : LGraph E I) (hN : Γ.Normal) (D : LData (Idx d L W)) {m : ℂ} {Ψ K₀ K₁ : ℝ}
    (hM : ∀ x y, D.M x y = if x = y then m else 0)
    (hG : ∀ x y, x ≠ y → ‖D.G x y‖ ≤ Ψ) (hGd : ∀ x, ‖D.G x x - m‖ ≤ Ψ)
    (hS : LWKBound D.S (K₀ * ((W : ℝ) ^ d)⁻¹) K₁) (hSp : LWKBound D.Sp (K₀ * ((W : ℝ) ^ d)⁻¹) K₁)
    (ℓe : E → Idx d L W) :
    ‖Γ.val D ℓe‖ ≤ Γ.sizeConst K₀ K₁ * Γ.scalingSize Ψ W d L
-- :1196
theorem lwClaimSize_E (d : ℕ) (hd : 3 ≤ d) (Λ κ : ℝ) (hΛ : 0 < Λ) (hκ : 0 < κ) :
    ∃ K₀ K₁ : ℝ, 0 < K₀ ∧ 0 < K₁ ∧ ∀ (L W : ℕ) [NeZero L] [NeZero W], 3 ≤ L →
      ∀ g t E : ℝ, 0 < g → g ≤ Λ → 0 ≤ t → t < 1 → |E| ≤ 2 - κ →
      ∀ (E' I' : Type) [Fintype E'] [DecidableEq E'] [Fintype I'] [DecidableEq I'] (Γ : LGraph E' I'),
        Γ.Normal → ∀ D : LData (Idx d L W), D.S = lwSmat d L W g t → D.Sp = lwSpOf d L W g t (mE E) →
        (∀ x y, D.M x y = if x = y then mE E else 0) → ∀ Ψ : ℝ,
        (∀ x y, x ≠ y → ‖D.G x y‖ ≤ Ψ) → (∀ x, ‖D.G x x - mE E‖ ≤ Ψ) → ∀ ℓe : E' → Idx d L W,
        ‖Γ.val D ℓe‖ ≤ Γ.sizeConst K₀ K₁ * Γ.scalingSize Ψ W d L
-- not printed (statements in the file): LGraph.exists_forest :725, lwClaimSizeG :1162, lwClaimSizeG_E :1213, LWPins_lwSp_decay :1341, lwSplus_decay :1353, lwSpOf_tail_E :1316, lwSpOf_eq :165, lwSpOf_decay :327
```

Compiled nonempty instances in the same file (`RBM3D/Graph/LWSizeClaim.lean`, section 9; the `example`s are the six listed here; every hypothesis is discharged (the `LWPins_lwSp`/`lwSplus` example is at the merged `sz0`, `n = 0`: `L = 4`, `W = 32`, `lam = 1/64`; the others at `d = 3`): `L = 4 ≥ 3`, `W = 2`, `g = 1/2 ∈ (0, 1]`, `t = 1/2 ∈ [0,1)`, `|0| ≤ 2 - 1/2`, `p2Graph.Normal` by `decide`, the entry bounds `|G_xy| = |G_xx - m| = 1/100` for `G = M + J/100`, `M = m(0) I`).
```
$ grep -n "^example" ...; statements of the compiled instances (each proof `obtain`s the target theorem and applies it)
-- :1367
example : (∃ C c : ℝ, 0 < C ∧ 0 < c ∧
    ∀ x y : Idx 3 4 32, ‖LWPins_lwSp 3 4 32 (1 / 64) 0 (1 / 2) x y‖ ≤
        C * (((32 : ℕ) : ℝ) ^ 3)⁻¹ * Real.exp (-(c * (lwBdist 3 4 32 x y : ℝ)))) ∧
    (∃ C c : ℝ, 0 < C ∧ 0 < c ∧
    ∀ x y : Idx 3 (SizesInst.sz0.L 0) (SizesInst.sz0.W 0), ‖lwSplus SizesInst.sz0 0 (1 / 2) (mE 0) x y‖ ≤
        C * (((SizesInst.sz0.W 0 : ℕ) : ℝ) ^ 3)⁻¹ * Real.exp (-(c * (lwBdist 3 (SizesInst.sz0.L 0) (SizesInst.sz0.W 0) x y : ℝ))))
-- :1403
example : ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
    (∀ x y : Idx 3 4 2, ‖lwSmat 3 4 2 (1 / 2) (1 / 2) x y‖ ≤
        C * ((2 : ℝ) ^ 3)⁻¹ * Real.exp (-(c * (lwBdist 3 4 2 x y : ℝ)))) ∧
    (∀ x y : Idx 3 4 2, ‖lwSpOf 3 4 2 (1 / 2) (1 / 2) (mE 0) x y‖ ≤
        C * ((2 : ℝ) ^ 3)⁻¹ * Real.exp (-(c * (lwBdist 3 4 2 x y : ℝ)))) ∧
    lwSmat 3 4 2 (1 / 2) (1 / 2) 0 0 ≠ 0
-- :1430
example : ∃ K₀ K₁ : ℝ, 0 < K₀ ∧ 0 < K₁ ∧
    p2Graph.nS = 6 ∧ p2Graph.nW = 2 ∧ p2Graph.nV = 4 ∧ p2Graph.nM = 2 ∧
    ‖p2Graph.val lwSizeD0 lwSizeEll‖ ≤
      p2Graph.sizeConst K₀ K₁ * p2Graph.scalingSize (1 / 100) 2 3 4
-- :1444
example : ∃ K₀ K₁ : ℝ, 0 < K₀ ∧ 0 < K₁ ∧
    0 < p2Graph.scalingSizeG (mE 0) (1 / 100) 2 3 4 ∧
    ‖p2Graph.val lwSizeD0 lwSizeEll‖ ≤
      p2Graph.sizeConstG (mE 0) K₀ K₁ * p2Graph.scalingSizeG (mE 0) (1 / 100) 2 3 4
-- :1459
example : ∃ K₀ K₁ : ℝ, 0 < K₀ ∧ 0 < K₁ ∧
    ∑ ℓi : Fin 4 → Idx 3 4 2, (p2Graph.waved.map fun e => ‖WEdge.val lwSizeD0 (Sum.elim lwSizeEll ℓi) e‖).prod ≤
      (Fintype.card (Idx 3 4 2) : ℝ) ^ p2Graph.nM * K₁ ^ (p2Graph.nV - p2Graph.nM) *
        (K₀ * ((2 : ℝ) ^ 3)⁻¹) ^ (p2Graph.nW - (p2Graph.nV - p2Graph.nM))
-- :1474
example : (∃ C₂ c₂ : ℝ, 0 < C₂ ∧ 0 < c₂ ∧ ∀ x : Idx 3 4 2,
    ∑ y ∈ Finset.univ.filter (fun y => 1 ≤ (lwBdist 3 4 2 x y : ℝ)),
      ‖lwSpOf 3 4 2 (1 / 2) (1 / 2) (mE 0) x y‖ ≤ C₂ * Real.exp (-(c₂ * 1))) ∧
    ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → Real.exp (-(1 * (Real.log W) ^ ((3 : ℝ) / 2) / 2)) ≤ (W : ℝ) ^ (-(3 : ℝ))
```

Name-clash grep (new public names against every `theorem|def|lemma|abbrev|structure|inductive|instance` of the same name in `RBM3D/`, branch worktree and main worktree at the hash printed below it):
```
$ python3 clash.py; git -C ../RBM3D rev-parse --short main
/Users/junyin/Lean_proof/RBM3D-wt/T2124: 37 new public names, declarations of the same name in other files: 0
/Users/junyin/Lean_proof/RBM3D: 37 new public names, declarations of the same name in other files: 0
471b643
```
Ports: none (no RBM1D/RBM2D file was read or copied; the paper has no proof of `claim:size`, T2040 inventory). `git diff --stat` RBM1D/RBM2D: not applicable.

Narrative.
- Only `RBM3D/Graph/LWSizeClaim.lean` is new (1484 lines, commit on `t/T2124`); `RBM3D/Test/Axioms.lean` is unchanged: the only new `Prop` def, `LWKBound`, is concluded by the theorem `lwKBound_of_decay`, so the scan reports no new premise (pre-check exit 0).
- Target 1: `lwSpOf_eq` proves `S^± = t·Lift(S^{(B)} Θ_{t m²})` with `Lift(B)_xy = W^{-d} B_[x][y]` multiplicative (`lwLift_mul`), `(1 - m²S)⁻¹ = 1 + Lift(Θ - 1)`; the decay is the merged `prop5Short_holds` (`σ = +`) plus `Σ_c S^(B)_ac = 1` and range one, constant `max((1+Λ²) C_s e^{c_s}, e^{c_s})` (the `S` bound needs `e^{c_s}`; no `(2d+1)` count as in (a): stochasticity of `S^(B)` gives it); `κ/2 ≤ Im m(E)` for `|E| ≤ 2 - κ` (`lwIm_mE_ge`) replaces (a)'s `κ''`. Row and column sums by `expC(d-2, c)` (`lwSum_decay_row`, `W^d` points per block).
- Target 2 (`scalemole`): `lwForest_sum_le` (peeling): children `C ⊆ I` with parent edges, ranks; induction with `Finset.induction_on_max_value` on the rank, one coordinate summed out by `Equiv.funSplitAt` (`lwSum_sep`), the other edges bounded by the entry bound `a`. `LGraph.exists_forest` builds `C` for a graph without `=`-dotted edges: targets = external vertices and one chosen vertex per internal molecule (`nM_eq_card`), rank = least walk length to a target (`lwExists_rank`), `|C| + n_M = n_V` (in its statement) and `|C| ≤ n_W` (`LGraph.counters_le`). `LGraph.waved_sum_le`: the case `n_W = 0` is separate inside the proof (an edge map `I → Fin 0` exists only for empty `I`; there `C = ∅`, `n_M = n_V`).
- Target 3: `LGraph.term_norm_le` (Normal (iii): a `×`-dotted edge between the ends of a non-loop solid edge kills equal labels, so every solid factor is `≤ Ψ`; (iv): loops carry the circle, `|G_xx - m| ≤ Ψ`); `lwSize_alg` is `N^{n_M} (K₀ W^{-d})^{n_W-(n_V-n_M)} = K₀^{..} (L^d)^{n_M} W^{-d(n_W-n_V)}` (`N = (WL)^d`); `lwClaimSize`; general graphs by `val_eq_partition`, `partition_normal`, `scalingSizeG_le_iff` (`lwClaimSizeG`). `lwClaimSize_E` takes `(K₀, K₁)` from `lwKBound_E`, so `C_Γ` depends on `Γ`, `d`, `Λ`, `κ` only.
- Same as (a): T1 form, T3 form `‖Γ.coeff‖ K₁^(nV-nM) K₀^(nW-(nV-nM))`; no `N^τ`, no `log W`, no ℓ-decay of solid edges, no window on `Ψ`. The statements T1-T3 of (a) are the ones proved (constants differ as noted above), so there is no (a′).
- The confinement `W (log W)^{3/2}` of `7_8:258` is not used by the claim; its content is `lwKernel_tail` (`Σ_{d_B ≥ R} |K| ≤ C expC(d-2,c/2) e^{-cR/2}`) and `lwTail_log32` (`R = (log W)^{3/2}` gives `≤ W^{-D}` for `W ≥ W₀(c, D)`).

## (c) Verified Mathlib names (every name below, except the one under "absent", elaborated by `#check` in `names.lean`; file:line from grep)
`Equiv.funSplitAt` (Logic/Equiv/Prod.lean:498); `Finset.induction_on_max_value` (Data/Finset/Max.lean:365, cases `empty`/`insert`, hypothesis `f x ≤ f a`); `Finset.prod_le_prod₀` (Algebra/Order/BigOperators/GroupWithZero/Finset.lean:39; `Finset.prod_le_prod` has no nonnegativity argument); `Fin.prod_ofFn` (Algebra/BigOperators/Fin.lean:52); `mul_eq_one_comm` (Algebra/Group/Monoid.lean:54, Dedekind-finite monoid); `Ring.inverse_mul_cancel` (Algebra/GroupWithZero/Units/Basic.lean:104); `SimpleGraph.fromRel_adj`, `SimpleGraph.ConnectedComponent.eq`/`.ind`, `SimpleGraph.Walk.length_cons`; `Nat.find_spec`, `Nat.find_min'`; `List.prod_nonneg`, `List.prod_eq_zero`, `List.mem_iff_get`, `List.ext_getElem`; `Finset.prod_image`, `Finset.prod_mul_prod_compl`, `Finset.card_le_card_of_injOn`, `Finset.sum_le_sum_of_subset_of_nonneg`, `Finset.card_image_of_injective`, `Finset.card_compl`; `Real.le_sqrt_of_sq_le`, `Real.rpow_def_of_pos`, `Real.rpow_one_add'`, `Real.sqrt_eq_rpow`, `Real.one_le_exp`; `zpow_sub₀`.
Verified absent: `Matrix.mul_eq_one_comm` (`Unknown constant`; use the root-namespace `mul_eq_one_comm`).

## (d) Open issues and paper-delta candidates
- `T2124a`: `scalemole` (`7_8:190-193`, confinement to `W (log W)^{3/2}`) is replaced in `claim:size` by the deterministic `L¹` peeling bound (`lwForest_sum_le`, `LGraph.waved_sum_le`): each tree edge costs `K₁` (row/column sum of `S`, `S^±`), each other waved edge the entry bound `K₀ W^{-d}`, each internal molecule `N`; no `W^{-D}` error, no `log W`. The confinement itself is kept as `lwKernel_tail`, `lwTail_log32`.
- `T2124b`: `claim:size` (`7_8:264-266`) is proved deterministically: entry bound `|G_xy| ≤ Ψ` (`x ≠ y`), `|G_xx - m| ≤ Ψ` as hypotheses, any `Ψ ≥ 0`, no window `W^{-d/2} ≤ Ψ`, no `N^τ`; the paper's `≺` is recovered with `Ψ := N^τ Ψ_t` (`LGraph.scalingSize_mul`). In the random setting the hypotheses are the owed `STGbEXPii`/`STGbEXPij` (S1-30) on the sample; LW-08 has to supply them per sample.
- `T2124c`: `(eq:estSpm-W)` is proved for `0 < g ≤ Λ` (the pin 5s of `prop5Short_holds` needs `0 < g`; `g = 0` is not covered) and `|E| ≤ 2 - κ` with constants in `(d, Λ, κ)` (DECISIONS §29's `|E| < 2` with constants free of `E` is false: (a) script 3, `sup_y |S^+_0y| e^{|y|/2}` grows as `E → 2`).
- `T2124d`: the decay is stated with the block `ℓ¹` distance `lwBdist` (periodic `ℓ¹` of `[x] - [y]`), not the paper's `|x-y|/W` (fine `ℓ^∞`); (a) states that the paper form follows up to a factor `e^{c d}`; that step is not formalized here.
- Open: `lwClaimSizeG` bounds by `(Σ_P C_P)`, a finite sum over the dotted edge partition, whose terms depend on `Γ` only. `(a)`'s probabilistic remark (`Ψ' ≤ N^τ Ψ`) is only the homogeneity lemma `LGraph.scalingSize_mul`; no stochastic statement is proved here.
