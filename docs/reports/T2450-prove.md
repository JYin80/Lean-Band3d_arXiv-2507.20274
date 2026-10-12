Prover model: claude-sonnet-5-5

## (a) Math preflight — Mon Oct 12 12:15:38 UTC 2026 (`date -u`)

Scratch (Python only, no Lean): `P`=/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/000e860b-4f24-47be-83fa-df6f7c59f990/scratchpad/T2450 (`fold14*.py bounds.py kern.py closure14.py pins_sum.py instance.py`). Engine and model reused by path: T2433 `l4s3/{ba,tree,stuck_list,check_roots}.py`, T2434 `mc_cut.py` (md5 8a33d3cc6b2359fa541dfebb6a32d240). Notation: `lift(A)_{uv}=A_{[u][v]}`, `B2=M^B∘M^B`, `ω=Θ^{++}=(1-tB2)⁻¹` (`BAExp14b_om`), `κ=ω-1` (`BAExp14b_kap true`, symmetric), `Z13=1[c3=c1]` (k=0) / `κ_{c3c1}` (k=1), `Q13=κ_{c1c3}` (k=0) / `(κ²)_{c1c3}` (k=1), `Mij=M^B_{ci cj}`, `X24=X(c2,c4)`.

### (i) Exponent table
**Normalisation (W, t powers).** `S=(t/W^d)lift(1)`, `M⁺_{uv}=B2_{cc'}δ_{oo'}`, `S⁺=S·W=(t/W^d)lift(ω)`. Kernels of the stuck nodes: `K1=S M⁺ S⁺=(t/W^d)lift κ`, `K2=S M⁺ S=(t²/W^d)lift B2`, `K11=S⁺M⁺SM⁺S⁺=(t/W^d)lift κ²` (`kern.py`; k=1 replaces `S_{wv}` by `K1`), `K3=Σ_{i2∈[c2],i5∈[c4]} S S ǦǦ=(t²/W^d)X24` (hand count, confirmed by the `e=1` cells below). So `W^{-2d}Σ_{x∈[a],y∈[b]}node = twLoop2X(Ǧ,Ǧ,ǦE_bǦ(σ),ρ·X^e)(a)` with `ρ=W^{2d}×(black weights)`: **W-power 0** in `ρ`; **t-power** `t²` (root#2, #1, #2), `t³` (#17, #22, #47, #52), both k. Tail `σ`: `s=true` ↔ `Ǧ_{yx}`, `s=false` ↔ `conj Ǧ_{xy}` (`twChg`).
```
 j node(engine order)  e  ρ (slots c1..c4)                    r1,r2 ≤ t^p·(k=0)   (k=1)
 0 root term #2        0  t² Z13 1[c4=c2] M12 M34           1          κℓ
 1 kid #1              0  t² Z13 M12 κ24 M34                κℓ         Mℓ κℓ²
 2 kid #2              0  t² 1[c4=c2] Q13 M12 M34           κℓ         κℓ²
 3 kid #17             1  t³ Z13 M12 M34 · X24              Mℓ²        Mℓ² κℓ
 4 kid #22             0  t³ Z13 M12 B2_24 M34              Mℓ | 1     Mℓ κℓ
 5 kid #47             1  t³ Q13 M12 M34 · X24              Mℓ² κℓ     Mℓ² κℓ²
 6 kid #52             0  t³ Q13 M12 B2_24 M34              Mℓ κℓ      Mℓ κℓ²
```
(k=0, j=0 is `ρ₀=t²1[c3=c1]1[c4=c2](M^B_{c1c2})²` of `TwistFold2_rho2`; Fable §4 lists k=0 and the `tr_1` root #2 only; k=1 kids derived here; the printed `W^{2d}` of its #17/#47 rows is not used: see X row.) Bounds (`bounds.py`, closed forms checked against the explicit `ρ`: 0 violations among the 28 values `r1,r2` of the 14 weights in each model; the script's label "28 (k,node) pairs" counts these 28 values): `Σ_c|M_ac|²=1` (`BAMB_row_sq_real`) + `BAMB_symm`; `Σ_b|M_ab||M_bc|≤1` (`baM_rho2`); `B2` row sum ≤ 1; `Mℓ=max row ℓ¹(M^B)≤c⁻¹expC(d-2)(c)`, `c=BAct_rate d 𝔡⁻¹ κ` (`baM_row_l1`, `baM_col_l1`; `g₀=√t₀λ≤λ≤𝔡⁻¹` by `WO`); `κℓ=max row ℓ¹(κ)≤1+C(1+g₀²expC(d-2)(c'))` from `baProp5s_holds` (`BAProp5s`, `σ₁=σ₂`: `|Θ(0,a)|≤C(1[a=0]+g²e^{-c'|a|})`, `sum_radial_exp_decay_le`), translated by shift invariance (copy of private `EKPins_Theta_shift`, `BA/EKPins.lean:289`; column = row); `κ²` by submultiplicativity; the `ℓ²` bounds of `κ` (j=1, 2) by the Schur test. Uniform in `n`, `t∈[0,T₀]`, `(a,b)` (`ρ` does not depend on `(a,b)`): `Cρ:=Mℓ²max(1,κℓ)²`, `t≤1`. Merged `Cρ` constant at `d=3,Λ=10,κ=1/2` is `c⁻¹expC 1 c=4.9e15` (existential in `BAFoldLeaf`, not an instance witness; instance values in (ii)).
**X row (#17, #47; S3).** `X24=W^{-d}Σ_{u∈[c2],v∈[c4]}Ǧ_{uv}Ǧ_{vu}=W^d Tr(E_{c2}ǦE_{c4}Ǧ)`, **not** `W^{2d}Tr`: the `W^{2d}` reading (X·W^d) misses the node value by relative error 1.0 / 1.0 / 2.0 (models A/B/C, `bounds.py` last lines). Chain: `|X|≤W^d(L̊(c2,c4)L̊(c4,c2))^{1/2}` (Cauchy-Schwarz), `L̊=W^{-2d}Σ|Ǧ|²≤2L^{(2)}_{(+,-)}(G)+2W^{-d}|M^B|²` (`BAExp14b_L2_eq`, `|M^B|≤1` by Ward), so `|X|≤2W^d·max L^{(2)}+2≺2W^dBctl+2≤(2+2c0⁻¹)W^dBctl` from `STLmaxgL` `k=2` and `W^dBctl=B_{t,0}≥c0=(𝔡⁻²+1)⁻¹` (`twB0_ge_holds`); only `STLmaxgL` is used (`STLocalEntrygL` stays a premise of the statement). Pathwise inequalities: 0 violations (`bounds.py`).
**Exponent chain.** Fable §2.2: node average `≺η⁻¹(W^{-d}B_0)^{5/2}B_0⁻¹`; Lean target `(1-t)⁻¹Bctl^{5/2}` (`twFold2Prec`, `twFold2PrecDet`), `Bctl=W^{-d}B_{t,0}`. Per root: 5 nodes with `e=0` (10 over k=0,1; the ticket's "12" reads 10) keep the margin `B_0⁻¹≤c0⁻¹=101` (slack 205 at the instance); the 2 nodes with `e=1` per root (4 in all) spend it exactly (`X≺W^dBctl=B_0`, term `Xmax/(W^dBctl)` of `Z` in `twFold2Prec_holds`). Both charges share `ρ` (the fold uses `|·|²` and Ward only).

**S1/S3 evidence (S3A-C5 (a)).** Each of the 28 cells `(k, s, node)` is the engine's stuck graph evaluated by `graph_val` (all internal indices summed) against the matrix formula `twLoop2X`, per sample, for `(a,b)` including `a=b`; models A: `L=3,W^d=2,t=0.6`, B: `L=4,W^d=2,t=0.35`, C: `L=3,W^d=3,t=0.5`:
```
$ cd P && python3 fold14_sum.py | grep '^>>'
>> model A: 28 cells (k,s,node): max rel.err 1.3e-15 (e=false: 1.3e-15, e=true #17/#47: 1.1e-15); wrong rho (kappa<->B2) min rel.err 4.98e-01
>> model B: 28 cells (k,s,node): max rel.err 2.7e-15 (e=false: 2.7e-15, e=true #17/#47: 2.7e-15); wrong rho (kappa<->B2) min rel.err 7.28e-01
>> model C: 28 cells (k,s,node): max rel.err 2.2e-15 (e=false: 2.2e-15, e=true #17/#47: 1.8e-15); wrong rho (kappa<->B2) min rel.err 5.63e-01
$ python3 kern.py
model A: S M+ S+ = (t/W^d) lift(kappa): True | S M+ S = (t^2/W^d) lift(B2): True | S+ M+ S M+ S+ = (t/W^d) lift(kappa^2): True | kappa symmetric: True
model B: S M+ S+ = (t/W^d) lift(kappa): True | S M+ S = (t^2/W^d) lift(B2): True | S+ M+ S M+ S+ = (t/W^d) lift(kappa^2): True | kappa symmetric: True
model C: S M+ S+ = (t/W^d) lift(kappa): True | S M+ S = (t^2/W^d) lift(B2): True | S+ M+ S M+ S+ = (t/W^d) lift(kappa^2): True | kappa symmetric: True
$ python3 bounds.py
model A: t=0.60  Ward sum |M|^2 = 1 ok; Ml = 1.7104, Kl = 0.5210; 28 (k,node) pairs: r1,r2 above the closed form: 0; max r/bound = 1.000
   X chain: max|X| = 1.793e+00 <= 2.089e+00 (CS) ; W^d Lb <= 8.573e+00 (<= 2 L2G + 2 W^-d |M|^2 scaled): violations 0, 0
model B: t=0.35  Ward sum |M|^2 = 1 ok; Ml = 1.7784, Kl = 0.2607; 28 (k,node) pairs: r1,r2 above the closed form: 0; max r/bound = 1.000
   X chain: max|X| = 3.668e-01 <= 5.096e-01 (CS) ; W^d Lb <= 4.272e+00 (<= 2 L2G + 2 W^-d |M|^2 scaled): violations 0, 0
model C: t=0.50  Ward sum |M|^2 = 1 ok; Ml = 1.6705, Kl = 0.3768; 28 (k,node) pairs: r1,r2 above the closed form: 0; max r/bound = 1.000
   X chain: max|X| = 7.454e-01 <= 9.327e-01 (CS) ; W^d Lb <= 5.330e+00 (<= 2 L2G + 2 W^-d |M|^2 scaled): violations 0, 0
control: node value vs twLoop2X with X*W^d (the W^{2d} reading), relative error, models A, B, C
   model A (W^d=2): min relative error over the 8 cells = 1.00e+00
   model B (W^d=2): min relative error over the 8 cells = 1.00e+00
   model C (W^d=3): min relative error over the 8 cells = 2.00e+00
```
**S4 (closure, S3A-C5 (c)).** All `BACtx` choices (blue and red), fuel 2, per root and charge; fold = stuck nodes (no `BACtx` candidate), `fold==catalogue` = the stuck graphs of `MERGED`, `T3C-tr_1` equal (as tuples) those of `stuck_list(k,s)` (`k=0` for `MERGED`); the `s=0` catalogue is the `s=1` one with `Gc(y,x)→Gbarc(x,y)`:
```
$ python3 closure14.py | head -10
root     s terms parents | leaves=props x~y | fold other fail | depth minmargin | blue red | even+conn/nodes | fold==catalogue
MERGED    1    32       6 |   2648  2648  182 |    7     0    0 |     2         0 |   38   0 |  2682/ 2682 | True
MERGED    0    32       6 |   2490  2490  182 |    7     0    0 |     2         0 |   36   0 |  2524/ 2524 | True
T3C-tr_1  1    16       5 |   2539  2539  169 |    7     0    0 |     2         0 |   36   0 |  2572/ 2572 | True
T3C-tr_1  0    16       5 |   2381  2381  169 |    7     0    0 |     2         0 |   34   0 |  2414/ 2414 | True
D2X       1    16       1 |    109   109   13 |    0     0    0 |     1         0 |    2   0 |   110/  110 | True
D2X       0    16       1 |    109   109   13 |    0     0    0 |     1         0 |    2   0 |   110/  110 | True
distinct stuck graphs per (T3C-tr_k, s) among the 7 occurrences: {(0, 1): 7, (0, 0): 7, (1, 1): 7, (1, 0): 7}
T3C-tr_0: catalogue(s=0)[j] == catalogue(s=1)[j] with Gc(y,x) -> Gbarc(x,y) for all j: True
T3C-tr_1: catalogue(s=0)[j] == catalogue(s=1)[j] with Gc(y,x) -> Gbarc(x,y) for all j: True
$ python3 inv.py | head -1   # T2433 script: random even+connected graphs are attached
even+connected graphs 4792 attached? {True: 4792}
$ python3 xdiff.py | tail -2   # T2433: Lean (xcheck) vs Python engine
xcheck.out (Lean) vs depth1.py (Python): 8 (s, root) blocks, 32 lines compared, mismatching lines: 0
xcheck2.out (Lean) vs stuck_py.py (Python): 22 vs 22 lines, mismatching lines: 0
```
Attachment: `Even∧Connected⇒BAG5Attached` (solid edges leaving a molecule ≡ Σ atom degrees ≡ 0 mod 2, and ≥1 by connectedness since waved/`M` edges stay inside molecules, so ≥2); `Even∧Connected` holds at all visited nodes (last column).
**S5 (roots).** Pins parsed from `docs/tickets/checks/T2450-check.lean`, compared with `roots.py` and evaluated against the independent families of `mc_cut.py` (`root value/t = S3 integrand`, F1):
```
$ python3 pins_sum.py
pins parsed from the check file, 6 (root,s) pairs: identical to roots.py up to the sigma field of the black waved edges: True ; black-edge sigma in pins [False], in roots.py [True]
model A (L=3 W^d=2 t=0.6): max over 3 pinned roots, both s, 24 samples x 4 pairs of |root value/t - mc_cut S3 integrand| = 2.2e-15 (max|integrand| 4.06e+00)
   negative control MERGED s=1, wrong black edge S(i1,i3): 2.25e+00
   negative control MERGED s=1, Gc(x,i0) circled: 1.09e+00
   anchor T2450_stuck0_val vs engine stuck_list(0,s)[0] (root term #2), both s: max |difference| of the values = 0.0e+00
model B (L=4 W^d=2 t=0.35): max over 3 pinned roots, both s, 12 samples x 4 pairs of |root value/t - mc_cut S3 integrand| = 3.9e-17 (max|integrand| 7.95e-02)
```
Observation (no S5): the pins write the black waved edges as `WEdge.mk false false …` (as `baG5Graph`, `BAExpandId.lean:79`); T2433's `roots.py`/`xcheck.lean` write `true`. `WEdge.val` ignores `σ` when `col=false` (`LWVocab.lean:120-122`) and `BAExpandId_flipW` leaves black edges unchanged (`:113`); values, counters and the closure are unchanged. 1b writes the pin's `false`.

### (ii) Instance: `d=3`, `sz0` at `n=0` (`L=4`, `W=32`, `N=2097152`, `λ=1/64`), `zSeq`, `t=1/2`, `𝔡=1/10`, `κ=1/2`, `ε=1/10`, `𝔠=1/6`
```
$ cd P && python3 instance.py
mS = 0.000000+0.832488i  zS = 0.000000+0.367512i  Im zS + Im mS = 1.200000 (Lean: 6/5)
t0 = 0.693740 (Lean t0_sz0: >= 2/3)  t = 1/2 < t0: True  g0 = 0.013014  E_flow = 0.00e+00  m_F = 0.000000+0.999493i  mS/sqrt(t0) - m_F = 1.1e-16
BAdom: Im m_F = 0.9995 >= kappa = 1/2: True ; N^(-1+eps) = 2.044e-06 <= Im zS = 0.3675 <= 1: True ; N = 2097152 ; W = 32 >= N^(1/6) = 11.31 ; W^(2*dd) = 2.000 <= lam^2 W^3 = 8.000
(self_m) residual |m - L^-d tr M^B| = 1.1e-16 ; Ward: max_a |sum_c |M^B_ac|^2 - 1| = 1.1e-15 ; symmetric: True
Bparam(t=1/2) = 2.030274 ; Bctl = 6.195904e-05 ; B_0 = W^d Bctl = 2.030274 >= c0 = (dd^-2+1)^-1 = 0.009901 (slack 205.058) ; margin (W^d Bctl)^-1 = 0.4925 <= c0^-1 = 101
Ml = max_a sum_b |M_ab| = 1.0828 (col 1.0828) ; omega=Theta^{++}: max row l1 0.6671, col 0.6671 ; kappa = omega - 1: row 0.3333, col 0.3333 ; B2 row sum max 1.0000
instance r1, r2 of the 14 weights (t=1/2; X not included), and Cr = Ml^2 max(1,Kl)^2:
  k=0: root#2 0.2500/0.2500 | kid#1 0.0833/0.0833 | kid#2 0.0833/0.0833 | kid#17 0.1466/0.1466 | kid#22 0.1249/0.1249 | kid#47 0.0489/0.0489 | kid#52 0.0416/0.0416
  k=1: root#2 0.0833/0.0833 | kid#1 0.0277/0.0277 | kid#2 0.0277/0.0277 | kid#17 0.0489/0.0489 | kid#22 0.0416/0.0416 | kid#47 0.0163/0.0163 | kid#52 0.0139/0.0139
  max over the 28 values = 0.2500 <= Cr = 1.1724 ; rho_0 of T2445 (j=0,k=0): r1 = r2 = t^2 = 0.2500 (Lean TwistFold2_rho2_bounds: 1/4)
stochastic premises: leading term W^d * L2_(+,-)(a,b) = [(1-tA)^-1 A]_ab: max entry 1.9959, diagonal 1.9959, row sum 2.0000 (= 1/(1-t) = 2.0000) ; B_0 = 2.0303 ; max entry / B_0 = 0.983
```
Hypotheses of the targets at these numbers: `BAFlow sz0 (1/2) (1/10) (1/6) (1/10) zSeq` (proved `flow_sz0`; its `BAdom`, bandwidth and `WO` entries are the numbers in line 3 of the output: `Im m_F=0.9995≥1/2`, `W^{0.2}=2≤λ²W³=8`, `λ=1/64≤𝔡⁻¹=10`); `0≤t=1/2≤T₀=0.6937` (`t0_sz0`: ≥2/3); `Cρ=1/4` for `ρ₀` (line `max over the 28 values`; the 14 weights have `r1,r2≤0.25` and the closed form gives `Cρ=1.17`); `ρ` row sums are `W`-independent. Stochastic premises `STLocalEntrygL`, `STLmaxgL` (external, registered owed): leading term of `W^d L^{(2)}_{(+,-)}(a,b)` is `[(1-tA)⁻¹A]_{ab}`, `A=|M^B|²`, max entry 1.9959 vs `B_0=2.0303` (ratio 0.983 < 1, row sum `1/(1-t)=2`; last line), so the premises are consistent at the instance and not vacuous; the deterministic part of the loop, `W^{-d}|M^B_{ab}|²≤W^{-d}=B_0⁻¹Bctl`, is below `Bctl`.

### Verdicts
- T1 roots, lists, identity: **PASS** (pins equal `roots.py` up to the inert black `σ`; values match `mc_cut` to 2.2e-15; S5 not triggered).
- T2 `BAFoldLeaf`, `baFoldLeaf_congr`: **PASS** (identity at the carrier shape, 28/28 cells to ≤2.7e-15 at three `(L,W^d,t)`; `ρ` independent of `(a,b)`, `r1,r2≤Cρ`).
- T3 14 reductions: **PASS**, S1 (explicit `ρ` per node, sample by sample), S2 (`r1,r2=O(1)` from merged bounds), S3 (`X=W^dTr`, `X≺W^dBctl`) do not occur. T3′ `BAS3Xprec`: **PASS** (chain above).
- T4 `BAS3Close`: **PASS**, S4 does not occur (fold 7 per `T3C-tr_k` tree, other stuck 0, depth ≤2, least margin 0, red `BACtx` 0, `x~y` leaves 182/169/13 included). T5 `BAS3Expand'`: **PASS** (T1 + T4). T6 instances: **PASS** (numbers in (ii); lists of `MERGED` at `s=false` hold 2490 `BAG5LeafProps` leaves and 7 fold leaves).

## (b) Script output, stage 1b — Mon Oct 12 15:30:25 UTC 2026 (`date -u`); branch `t/T2450`, worktree `RBM3D-wt/T2450`

**Size against the stop line (2,000 per file) and verdict.**
```
$ wc -l RBM3D/Graph/BAS3Close.lean RBM3D/Graph/BAS3CloseB.lean RBM3D/Graph/BAS3CloseC.lean
    1953 RBM3D/Graph/BAS3Close.lean
     837 RBM3D/Graph/BAS3CloseB.lean
    1661 RBM3D/Graph/BAS3CloseC.lean
    4451 total
```
Stop line not reached (largest file 1953); no `T2450_*` pin changed; no new `inductive`/`structure` (`BAS3Close_Inv` is an `abbrev`); `Test/Axioms.lean` untouched.
**S3A-C5 verdict: S1–S5 do not occur.** (a) each of the 14 catalogue graphs, both charges, equals `twLoop2X` with an explicit `ρ` *pathwise* (`baS3Fold_holds`, clause (i); stronger than the 1e-12 sample check of (a)); (b) `r₁, r₂ ≤ Cρ` from the merged `baM_row_l1`, `baM_col_l1`, `BAExp14a_theta_l1`, `BAExp14a_theta_col`; the #17/#47 factor is `W^d Tr` (`BAS3Close_cK3_blk`, `BAS3Close_CL`) and `‖X‖ ≺ W^d Bctl` is `baS3Xprec_holds`; (c) `baS3Close_holds`.

**Closure table as finally proved** (1a (iv) numbers are the Python engine's and are not re-derived in Lean; Lean proves the classification they count):
```
root (tree)   split terms [decide +kernel]   outputs, s = false and s = true (baS3Close_mod / baS3Close_holds)
MERGED        32  (baS3RootM)                every output: BAG5LeafProps leaf, or value = a graph of baS3Stuck (7 stuck, k = 0)
T3C-tr_1      16  (baS3Root1)                same, catalogue k = 1
D2X           16  (baS3RootD)                same; no fold node expected (1a: fold 0), none needed
split terms: scratch counts.lean, 6 examples `(baS3Root.. s).splitG.length = 32/32/16/16/16/16` by `decide +kernel` compile, `#eval` prints 32 16 16
witnesses [baS3_inst_close]: all 6 lists nonempty; MERGED/false has a leaf (split term with 5 <= MCM, 2 <= nW) and a fold (CatR0 = root term #2)
```

**Build** (`lake build RBM3D.Graph.BAS3Close RBM3D.Graph.BAS3CloseB RBM3D.Graph.BAS3CloseC`, last full rebuild of the three modules in the tool log; upstream replay warnings omitted, none from these files):
```
✔ [4026/4028] Built RBM3D.Graph.BAS3Close (11s)
✔ [4027/4028] Built RBM3D.Graph.BAS3CloseB (64s)
✔ [4028/4028] Built RBM3D.Graph.BAS3CloseC (16s)      # rebuilt after the last edit
Build completed successfully (4028 jobs).
```
Full `lake build` with `import RBM3D.Graph.BAS3Close/B/C` added to a *temporary* `RBM3D.lean` (reverted; the hub adds the imports at merge, as in the merged tickets), HEAD `195837c`:
```
info: RBM3D.lean:514:0: axiom audit: 13284 theorems, 4171 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
All within [propext, Classical.choice, Quot.sound]   ...   Build completed successfully (4282 jobs).
```

**Axioms** (`#print axioms`, scratch `axfinal.lean`; 14 theorems, one distinct set):
```
$ lake env lean axfinal.lean | sed ... | awk -F' : ' '{print $2}' | sort | uniq -c
  14 [propext, Classical.choice, Quot.sound]
names: baS3Identity_holds, baS3Close_mod, baFoldLeaf_congr, baS3Stuck0_val, baS3Fold_holds, baS3Xprec_holds, baS3Close_holds, baS3Expand'_holds, BAS3CloseInst.baS3_inst_identity, BAS3CloseInst.baS3_inst_fold, BAS3CloseInst.baS3_inst_congr, BAS3CloseInst.baS3_inst_expand', BAS3CloseInst.baS3_inst_close, BAS3CloseInst.baS3_inst_rho0
```

**Target statements, extracted by `extract.py` (first line of each public declaration; file:line; full text in the files):**
```
BAS3Close.lean:56: def baS3RootM (s : Bool) : BAGraph (Fin 2) (Fin 4)
BAS3Close.lean:66: def baS3Root1 (s : Bool) : BAGraph (Fin 2) (Fin 6)
BAS3Close.lean:78: def baS3RootD (s : Bool) : BAGraph (Fin 2) (Fin 4)
BAS3Close.lean:88: def BAS3expandRoot (sel : BASel) (fuel : ℕ) : Fin 3 → Bool → List (BAPGraph (Fin 2)) | 0, s => (baS3RootM s).partition.flatMap fun P => (BAexpand sel fuel P).map Prod....
BAS3Close.lean:95: def BAS3Identity (d : ℕ) (Ls : Fin 3 → Bool → List (BAPGraph (Fin 2))) : Prop
BAS3Close.lean:130: theorem baS3Identity_holds (d : ℕ) (sel : BASel) (fuel : ℕ) : BAS3Identity d (BAS3expandRoot sel fuel)
BAS3CloseB.lean:326: def baS3Stuck : Bool → Fin 7 → Bool → BAPGraph (Fin 2) | false, ⟨0, _⟩, s => BAS3Close_pk (BAS3Close_cf0_0 s) | false, ⟨1, _⟩, s => BAS3Close_pk (BAS3Close_cf0_1 s) | ...
BAS3CloseB.lean:827: theorem baS3Close_mod : ∀ (r : Fin 3) (s : Bool), ∀ q ∈ BAS3expandRoot BAselStar 2 r s, BAG5LeafProps (fun _ _ => [q]) ∨ ∃ (k : Bool) (j : Fin 7), ∀ {ι : Type} [Fintyp...
BAS3CloseC.lean:965: def BAFoldLeaf (q : BAPGraph (Fin 2)) : Prop
BAS3CloseC.lean:985: theorem baFoldLeaf_congr : ∀ q q' : BAPGraph (Fin 2), (∀ {ι : Type} [Fintype ι] [DecidableEq ι] (D : BALData ι) (ℓ : Fin 2 → ι), q.val D ℓ = q'.val D ℓ) → BAFoldLeaf q...
BAS3CloseC.lean:1364: def BAS3Xprec (d : ℕ) : Prop
BAS3CloseC.lean:1374: theorem baS3Xprec_holds : ∀ d : ℕ, BAS3Xprec d
BAS3CloseC.lean:1427: theorem baS3Fold_holds : ∀ (k : Bool) (j : Fin 7) (s : Bool), BAFoldLeaf (baS3Stuck k j s)
BAS3CloseC.lean:1448: theorem baS3Stuck0_val : ∀ (s : Bool) {ι : Type} [Fintype ι] [DecidableEq ι] (D : BALData ι) (ℓ : Fin 2 → ι), (baS3Stuck false 0 s).val D ℓ = ({ solid := [SEdge.mk tru...
BAS3CloseC.lean:1483: def BAS3Close : Prop
BAS3CloseC.lean:1486: theorem baS3Close_holds : BAS3Close
BAS3CloseC.lean:1493: def BAS3Expand' (d : ℕ) : Prop
BAS3CloseC.lean:1497: theorem baS3Expand'_holds : ∀ d : ℕ, BAS3Expand' d := fun d =>
```

**Scratch copy of the check file** (`check_closed.lean` = `docs/tickets/checks/T2450-check.lean` + `import RBM3D.Graph.BAS3Close/B/C` + the lines below inside `namespace RBM.Graph.T2450Check`; not committed): `lake env lean check_closed.lean` exit code 0, 0 errors; each pin closed by the theorem as a term:
```
example : T2450_rootM_eq baS3RootM := fun s => rfl            -- likewise T2450_root1_eq baS3Root1, T2450_rootD_eq baS3RootD
example : T2450_expandRoot_eq baS3RootM baS3Root1 baS3RootD BAS3expandRoot := fun sel fuel s => ⟨rfl, rfl, rfl⟩
example : T2450_identity baS3RootM baS3Root1 baS3RootD BAS3expandRoot := baS3Identity_holds
example : T2450_BAS3Close BAS3expandRoot := baS3Close_holds
example : ∀ d : ℕ, T2450_BAS3Expand' baS3RootM baS3Root1 baS3RootD d := baS3Expand'_holds
example : T2450_foldCongr := baFoldLeaf_congr
example : ∀ d : ℕ, T2450_BAS3Xprec d := baS3Xprec_holds
example : T2450_stuck0_val baS3Stuck := baS3Stuck0_val        -- anchor, a value theorem: the pin's labels are renamed by BAS3Close_eI0_0 = swap 2 3
example : T2450_reductions baS3Stuck := baS3Fold_holds
```

**Compiled nonempty instances** (`RBM.Graph.BAS3CloseInst`, `BAS3CloseC.lean:1502-1657`; every deterministic hypothesis discharged):
```
baS3_inst_identity (s) (x y : Idx 3 3 1)   :1508  target 1 at d=3, L=3, W=1, g0=0, E=0, t=1/2, m=i (BAExpandInst.baSelf_zero), 3 roots
baS3_inst_fold / _congr                   :1523  targets 2, 3: BAFoldLeaf (baS3Stuck false 0 false); transfer applied to itself
example (hE hL) [target 3 consumed]       :1530  target 3 consumed once: [a]x[b] average of baS3Stuck false 0 p.1 at sz0, zSeq, t = 1/2 is ≺ (1-t)^-1 Bctl^(5/2)
                                                  via twFold2PrecDet_holds; the two stochastic premises STLocalEntrygL, STLmaxgL stay hypotheses
baS3_inst_rho0                            :1550  the weight used is TwistFold2_rho2 (T2445 rho_0 = t^2 1[c3=c1 ∧ c4=c2] (M^B_c1c2)^2)
example (hE hL) [target 3']               :1573  target 3' at d=3, sz0, zSeq, t = 1/2 (premises as above)
baS3_inst_expand'                         :1584  target 5 at d = 3
baS3_inst_close                           :1637  target 4: 6 lists nonempty ∧ a BAG5LeafProps leaf and a BAFoldLeaf in MERGED/false
```

**Name clash** (`git grep -E 'BAS3|baS3|BAFoldLeaf|baFoldLeaf'` on `main` `0390b84` and on the 59 other `t/T24*` branches): 0 hits everywhere.
**Diff** (`git diff --stat main...t/T2450`; 16 commits):
```
 RBM3D/Graph/BAS3Close.lean  | 1953 +++++++++++++++++++++++++++++++++++++++++++
 RBM3D/Graph/BAS3CloseB.lean |  837 +++++++++++++++++++
 RBM3D/Graph/BAS3CloseC.lean | 1661 ++++++++++++++++++++++++++++++++++++
 3 files changed, 4451 insertions(+)
```

**Narrative.**
1. Part A (`BAS3Close.lean`): the three roots as data (the pins' edge lists), `BAS3expandRoot`, `baS3Identity_holds` (`expandG_sum` with `Normal`, `kids_normal`, `kids_identity`, as `baExpandIdentity_holds`); renamings of packed graphs keep value, counters, atoms (`BAS3Close_Iso`); `Even` and `Conn` are preserved by every `gg2`/`gg4` step and give `BAG5Attached` (T2433a route); Lemma A for the kids of a `BACtx` step; the abstract closure at margins `≥ -1` and `-2`.
2. Part B (`BAS3CloseB.lean`): `baS3Stuck` is the engine's stuck output flattened to core-first labels (`BAS3Close_cf{k}_{j}`); the classification of the root splits and of the kids of the order-3 terms is `decide +kernel` through a list mirror of the atom closure (section `Mirror`: `BAS3Close_MCM ≤ BAS3Close_MC`), giving `baS3Close_mod`.
3. Part C (`BAS3CloseC.lean`), the analytic half. The generic 4-cycle lemma is `BAS3Close_CL`: the ties `M_{u0u1}`, `M_{u2u3}` are summed by `BAExp14b_M_pt` (`BAS3Close_tie2`), the free ends run over blocks (`TwistFold2_sum_blk`) and the average is `twLoop2X` with `ρ = W^{2d} M^B M^B Z N`. Five chain kernels (`S M⁺ S⁺`, `S⁺ M⁺ S`, `S M⁺ S`, `S Ǧ Ǧ S`, `S⁺ M⁺ S M⁺ S⁺`) have block forms from `BAExp14a_W_sub_one`, `BATheta_resolvent`, `BATheta_isSymm` (`BAS3Close_cK*_blk`); the 14 shape lemmas `BAS3Close_shape{k}{j}` unroll the real `BAGraph.val` (`sum_pi_fin_succ`); `BAS3Close_hq{k}{j}` + `BAS3Close_fold_gen` give the 14 reductions.
4. Weights (the `BAS3Close_Hq` lines of `BAS3CloseC.lean`, listed by script below): `ρ = t^p Z_{c1c3} M^B_{c1c2} M^B_{c3c4} N_{c2c4}` (times `X(c2,c4)` when `e = true`), kernels `kD = 1[c = c']`, `kK = κ = ω - 1`, `kKK = κ²`, `kB = M^B_{cc'} M^B_{c'c}`, `k1 = 1`; `ρ` is the same for both charges and independent of `(a, b)`; this is the table of (a)(i). `Cρ = (K m²)(m (K² m))` with the uniform `ℓ¹` constants `m` of `M^B` (`baM_row_l1`, `baM_col_l1`) and `K` of `κ` (`BAExp14a_theta_l1`, `BAExp14a_theta_col`), eventually in `n` by `BAflow_lam0_window`; cruder than the closed forms of (a)(i) (no Ward cancellation, no Schur test), enough for the pin.
```
BAS3CloseC.lean:1044  k=0 j=0  e=false p=2  Z=kD   N=kD
BAS3CloseC.lean:1060  k=0 j=1  e=false p=2  Z=kD   N=kK
BAS3CloseC.lean:1076  k=0 j=2  e=false p=2  Z=kK   N=kD
BAS3CloseC.lean:1092  k=0 j=3  e=true  p=3  Z=kD   N=k1
BAS3CloseC.lean:1108  k=0 j=4  e=false p=3  Z=kD   N=kB
BAS3CloseC.lean:1124  k=0 j=5  e=true  p=3  Z=kK   N=k1
BAS3CloseC.lean:1140  k=0 j=6  e=false p=3  Z=kK   N=kB
BAS3CloseC.lean:1156  k=1 j=0  e=false p=2  Z=kK   N=kD
BAS3CloseC.lean:1172  k=1 j=1  e=false p=2  Z=kK   N=kK
BAS3CloseC.lean:1188  k=1 j=2  e=false p=2  Z=kKK  N=kD
BAS3CloseC.lean:1204  k=1 j=3  e=true  p=3  Z=kK   N=k1
BAS3CloseC.lean:1220  k=1 j=4  e=false p=3  Z=kK   N=kB
BAS3CloseC.lean:1236  k=1 j=5  e=true  p=3  Z=kKK  N=k1
BAS3CloseC.lean:1252  k=1 j=6  e=false p=3  Z=kKK  N=kB
```
5. `baS3Xprec_holds`: pathwise `‖X‖ ≤ 2 W^d max|𝓛^{(2)}| + 2` (AM-GM, `baM_row_sq`, `BAExp14b_L2_eq`, `BAS3Close_Xbound`), then the `BAExp14a_Dom` calculus of T2445 and `twB0_ge_holds`; only `STLmaxgL` (`k = 2`) is used, `STLocalEntrygL` is carried by the statement.
6. `baS3Close_holds` = `baS3Close_mod` + `baS3Fold_holds` + `baFoldLeaf_congr`; `baS3Expand'_holds` adds `baS3Identity_holds`. Nothing in a statement differs from its pin (11 closing examples above).
7. Differences from the plan: clause (i) of `BAFoldLeaf` is proved without `0 < κ` and without `3 ≤ d` (the pin has neither; the data come from `BAflow_real`, `BAm_self`); `BAS3Close_Inv` is an `abbrev` of a conjunction instead of a `structure`; `RBM3D.lean` is not edited on the branch.

## (c) Mathlib names verified (by compile in this branch)
`Finset.sum_comm`, `Finset.sum_ite_eq`, `Finset.sum_ite_eq'`, `Finset.sum_ite_irrel`, `Finset.sum_const_zero`, `Finset.sum_eq_single_of_mem`, `Finset.single_le_sum`, `Finset.sum_le_sum_of_subset_of_nonneg`, `Finset.mul_sum`, `Finset.sum_mul`, `Finset.sum_fiberwise` (through `TwistFold2_sum_blk`), `norm_sum_le`, `norm_sub_le`, `norm_mul`, `norm_pow`, `pow_le_one₀`, `one_le_pow₀`, `Complex.mul_conj`, `Complex.normSq_eq_norm_sq`, `Complex.star_def`, `Complex.norm_real`, `Matrix.sub_apply`, `Matrix.one_apply`, `Matrix.mul_add`, `Matrix.mul_apply`, simproc `Matrix.cons_val` (evaluates `![a,…] 5` and `7`), `List.mem_flatMap`, `List.ne_nil_of_mem`, `Fin.consEquiv` (inside the merged `sum_pi_fin_succ`). Deprecated in this toolchain and avoided: `if_pos`, `if_true`, `if_false` (replaced by `ite_true`, `↓reduceIte`).

## (d) Open issues and paper-delta candidates
- **T2450a** (black waved `σ`): the pins write `WEdge.mk false false …` (as `baG5Graph`); T2433's `roots.py`/`xcheck.lean` write `true`; `WEdge.val` ignores `σ` when `col = false` (`LWVocab.lean:120-122`). Inert (a); the pins are used as written.
- **T2450b** (Fable §4 table): the `W^{2d}` printed in the #17/#47 rows is `W^d`: `BAS3Close_cK3_blk` gives `S Ǧ Ǧ S = (t²/W^d) X` with `X = W^{-d} Σ_{u∈[c₂], v∈[c₄]} Ǧ_{uv} Ǧ_{vu}`, and `baS3Xprec_holds` is `‖X‖ ≺ W^d Bctl`.
- **T2450c** (weights of `T3C-tr_1`): Fable lists `k = 0` and root #2 of `tr_1` only; the six kids are `BAS3Close_hq1{1..6}` (weights as in the table of (a)(i); `Z_{13}` of `k = 1` is `κ` or `κ²`).
- **T2450d** (constants): `BAFoldLeaf` quantifies `∃ Cρ`; Lean gives `Cρ = (K m²)(m (K² m))` from the merged `ℓ¹` bounds; the numerical constants at the instance of (a)(ii) are not recomputed in Lean.
- Observations: (1) `RBM3D.lean` imports for the three modules are the hub's (A.4); the full `lake build` above had them added temporarily. (2) The counts of (a)(iv) (leaves 2648, 2490, ...) are the Python engine's; Lean proves the classification (32/16/16 split terms are `decide +kernel` facts). (3) Extra public names beyond the pins: `baS3Close_mod` (closure modulo the catalogue), `baS3Stuck0_val` (anchor value theorem, needed for `T2450_stuck0_val`), and the `BAS3CloseInst` instances. (4) The `ρ` of (a)(i) for `j = 4, 6` uses `M^B∘M^{BT}` (`kB`), matching `B2` of the table. (5) No design question is open.
