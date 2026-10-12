Prover model: claude-sonnet-5-5

## (a) Math preflight — Mon Oct 12 18:14:27 UTC 2026 (`date -u`)

Scratch (Python only, no Lean): `P2464` = /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/000e860b-4f24-47be-83fa-df6f7c59f990/scratchpad/T2464 (`s1_literal s1_bridge s2_subroot s3_tpower s4_exponents s5_census s6b_xy s7_premises s8_lines`). Engine reused by path: T2433 `l4s3/{ba,tree,roots,check_roots,closure}.py`, T2450 `fold14.py`, `instance.py` (`P2450`); model = T2434 `mc_cut.py`, md5 8a33d3cc6b2359fa541dfebb6a32d240 (verified; run unmodified up to `names = [`). Pins are parsed from text: `rT0` from `docs/tickets/checks/T2464-check.lean` (`T2464_rootT0_eq`); `baS3RootM/Root1/RootD` from merged `RBM3D/Graph/BAS3Close.lean:56-85`. Models: A `L=3 W^d=2 t=0.6`, B `L=4 W^d=2 t=0.35`, C `L=3 W^d=3 t=0.5`.

### (i) Exponent table

**Bridge (target 2; S1).** Root value = t × S3 integrand: the black edge `S(w,v) = t W^{-d}1[v∈[w]]` of each root is the block identity; `n_W(rT0) = 2`. Literal numpy transcription of `BAExp14b_FD1X/FD2X/FT3CX` (`BAExp14b:69-72, 132-149`, `BAExp14aB:57-66`; `dX = -W^{-d}Σ_{v∈[α]}G_{vδ}G_{γv}`; tail `G_{yx}` for `σ=true`, `conj G_{xy}` for `σ=false`) against the block average of the parsed root pins, all block pairs incl. `a=b`, both `σ`; then the pins against `mc_cut` integrands `R[14..17]` (`D1X = MERGED − T3C-tr_0` is the `j=0` split):
```
$ cd P2464 && python3 s1_literal.py
model A (L=3 W^d=2 t=0.6, 24 samples, 9 block pairs incl. a=b, both sigma): max|t*F(Lean family) - avg root|: T3C-tr_0 6.7e-16; MERGED 1.4e-15; T3C-tr_1 4.5e-16; D2X 3.5e-16; (max|avg| 2.44e+00) control t*T3C-tr_0 vs MERGED min err 2.7e-01
model B (L=4 W^d=2 t=0.35, 12 samples, 16 block pairs incl. a=b, both sigma): max|t*F(Lean family) - avg root|: T3C-tr_0 5.3e-18; MERGED 1.6e-17; T3C-tr_1 3.5e-18; D2X 1.1e-17; (max|avg| 2.78e-02) control t*T3C-tr_0 vs MERGED min err 2.5e-03
model C (L=3 W^d=3 t=0.5, 8 samples, 9 block pairs incl. a=b, both sigma): max|t*F(Lean family) - avg root|: T3C-tr_0 7.3e-18; MERGED 1.2e-17; T3C-tr_1 4.3e-18; D2X 4.7e-18; (max|avg| 3.52e-02) control t*T3C-tr_0 vs MERGED min err 4.0e-03
$ python3 s1_bridge.py | cut -c1-330
pins vs roots.py (edge lists, same order, up to the inert sigma of black waved edges): T3C-tr_0 True, MERGED True, T3C-tr_1 True, D2X True
first solid edge of the rT0 pin / baS3RootM pin (s=1): (True, True, ('e', 0), ('i', 0)) (True, False, ('e', 0), ('i', 0))
model A (L=3 W^d=2 t=0.6, 24 samples, 9 block pairs incl. a=b, both sigma): max|root avg/t - mc_cut S3 integrand|: T3C-tr_0 9.9e-16; MERGED 2.2e-15; T3C-tr_1 8.0e-16; D2X 6.7e-16; D1X=MERGED-T3C0 1.3e-15 (max|integrand| 4.06e+00)
   negative controls (T3C-tr_0), MIN error over pairs/sigma: rT0 first edge uncircled 4.5e-01; no factor t (root, not root/t) 4.9e-01; wrong sigma (s swapped) 2.4e+00; black edge S(i0,i3)->S(i0,i2) 4.9e-01
model B (L=4 W^d=2 t=0.35, 12 samples, 16 block pairs incl. a=b, both sigma): max|root avg/t - mc_cut S3 integrand|: T3C-tr_0 1.4e-17; MERGED 3.9e-17; T3C-tr_1 9.0e-18; D2X 3.6e-17; D1X=MERGED-T3C0 4.5e-17 (max|integrand| 7.95e-02)
   negative controls (T3C-tr_0), MIN error over pairs/sigma: rT0 first edge uncircled 7.2e-03; no factor t (root, not root/t) 3.1e-03; wrong sigma (s swapped) 6.7e-03; black edge S(i0,i3)->S(i0,i2) 1.4e-03
```
S1 does not occur (every identity as pinned, `σ=true ↔ s=1`; controls fail by ≥ 1.4e-3 against errors ≤ 2.2e-15).

**Sub-root (target 1; S2).** The partition of `rT0` lies in `MERGED`'s (first step of `baSplitSolid`, `BAVocab:163-168`: `Ǧ(x,i0)` kept; the `M(x,i0)` branch is `D1X`). `BAexpand sel fuel P` depends on `P` only, so the expanded list ⊆ `BAS3expandRoot sel fuel 0 s` for every `sel, fuel`.
```
$ python3 s2_subroot.py | cut -c1-250
s=1: |partition(rT0)|=16 |partition(MERGED)|=32  every term of rT0 is a term of MERGED: True ; rT0 terms = MERGED terms with Gc(x,i0) (the other 16 carry the new M(x,i0)): True ; complement 16 terms, counters-multiset == partition(D1X): True
s=0: |partition(rT0)|=16 |partition(MERGED)|=32  every term of rT0 is a term of MERGED: True ; rT0 terms = MERGED terms with Gc(x,i0) (the other 16 carry the new M(x,i0)): True ; complement 16 terms, counters-multiset == partition(D1X): True
$ (cd T2433/l4s3; for r in T3C-tr_0,D1X MERGED; do python3 closure.py 2 $r; done) | grep 'closure F=' | sed -E 's/.*leaves ([0-9]+) .*below target\) ([0-9]+).*/\1 leaves, \2 stuck/' | paste -sd'|' -
2539 leaves, 7 stuck|2381 leaves, 7 stuck|109 leaves, 0 stuck|109 leaves, 0 stuck|2648 leaves, 7 stuck|2490 leaves, 7 stuck   # T3C-tr_0 s=1,0; D1X s=1,0; MERGED s=1,0 (2539+109, 2381+109)
```
S2 does not occur; the 7 stuck nodes of `T3C-tr_0` are the catalogue `baS3Stuck false j s` of `MERGED`'s list.

**`t`-power table (target 4; S3).** Parsed from `BAS3CloseC:1043-1265`. `ρ_Lean = BAS3Close_rho(2+qq) = t^{2+qq}·Z M M N = t·BAS3Close_rho(1+qq)`; `BAFoldLeafT` takes `ρ' = BAS3Close_rho(1+qq)` (spare `t`, power `1+qq ≥ 1`) and `Bd_of(1+qq)` with the same `hZ_*, hN_*` (`Bd_of` uses only `‖t^p‖ ≤ 1`, `BAS3CloseC:858`).
```
$ python3 s3_tpower.py | cut -c1-330
Hq lines parsed: 14 ; fold_gen+Bd_of lines parsed: 14
node: e=true/false, p=2+qq, (Zk,Nk) for k=0 | k=1 ; rho_Lean = t * BAS3Close_rho(1+qq)
0: e=f p=2 k0(D,D) k1(K,D) ; 1: e=f p=2 k0(D,K) k1(K,K) ; 2: e=f p=2 k0(K,D) k1(KK,D) ; 3: e=t p=3 k0(D,1) k1(K,1) ; 4: e=f p=3 k0(D,B) k1(K,B) ; 5: e=t p=3 k0(K,1) k1(KK,1) ; 6: e=f p=3 k0(K,B) k1(KK,B)
p = 2+qq equals the t-power of the T2450 1a table (t^2 for nodes 0-2, t^3 for nodes 3-6), e = X-factor for nodes 3, 5 only: True
model A (L=3 W^d=2 t=0.6): 28 cells (k,s,node), pairs incl. a=b: max |avg node - t*twLoop2X(Gc,Gc,tail,rho,..)| = 1.4e-16 (max|avg| 2.20e-01); control without the factor t: min err 3.0e-03; max l1 of rho rows/cols = 1.0531
model B (L=4 W^d=2 t=0.35): 28 cells (k,s,node), pairs incl. a=b: max |avg node - t*twLoop2X(Gc,Gc,tail,rho,..)| = 8.8e-19 (max|avg| 2.14e-03); control without the factor t: min err 1.9e-06; max l1 of rho rows/cols = 0.3874
```
(Here `rho` in the last two lines is `ρ' = ρ_Lean/t`.) Every catalogue weight has a spare `t`; the private route's names (`BAS3Close_{Hq, fold_gen_i, rho, Bd_of, Kern, k*, hZ_*, hN_*}`, `hq00-hq16`: 14 `theorem BAS3Close_hq..`) are in `BAS3CloseC.lean` (grep). S3 does not occur.

**Target 5 (leaf bound), one row per branch** (instance of (ii): `t=1/2, κ=1/2, 𝔡=1/10`; `X ≺ …` is written `X << …`):
```
$ python3 s4_exponents.py | tail -n +2 | cut -c1-300
```
| branch / constant | value | constraint | slack |
|---|---|---|---|
| apart (ord>=5): t^nW, nW=2,3,4 | 0.25, 0.125, 0.0625 | <= t=0.5 (nW>=1, t<1) | x2, x4, x8 |
| apart: eta^-1 | 2.00102 | <= kappa^-1(1-t)^-1 = 4.0 (twEta_ge: eta >= kappa(1-t)) | x2.00 |
| apart: B^(ord/2)/B^(5/2), ord=5,6,7 | 1, 0.00787, 6.2e-05 | <= 2^((ord-5)/2) (Bctl<=2: lam^2W^d=8>=1, N(1-t)=1048576>=1) | x1 at ord 5 (closes exactly) |
| apart total t^2 eta^-1 B^(5/2) vs t(1-t)^-1 B^(5/2) | 1.5117e-11 vs 3.0218e-11 | general constant kappa^-1 2^((ord-5)/2) | ratio 0.500 |
| tied (x~y, ord>=3): support | W^d of W^2d pairs | offset x = offset y (baAtom_offset, BAAtom_offdiag_E) | factor W^-d = 3.052e-05 |
| tied: W^-d B^(3/2) | 1.488e-11 | <= (dd^-2+1) B^(5/2) = 3.052e-09 (twB0_ge: W^dB >= 0.0099, here 2.0303) | x205.1 |
| tied total W^-d t^2 eta^-1 B^(3/2) | 7.4456e-12 | <= 3.0218e-11 | ratio 0.246 |
| fold e=false (twFold2PrecDet): margin (W^dB)^-1 | 0.4925 | <= dd^-2+1 = 101 | x205.1, then factor t |
| fold e=true (twFold2Prec + baS3Xprec): \|X\| | <= 204 * W^dBctl (2+2*101) | X << W^dBctl spends the margin | 0 by design, then factor t |
| rho1 = rho/t row/col l1, 28 values | max 0.5000 | <= C_rho = Ml^2 max(1,Kl)^2 = 1.1724 (Ml=1.0828, Kl=0.3333; instance proxy, Lean C_rho existential) | x2.34 |
| floor N^(-5/2) (BAExp14a_floor) | 1.570e-16 | <= (1-t)^-1 B^(5/2) = 6.044e-11 | x3.85e+05 |
| fold envelope exponent K | e=false 1+8=9; e=true 1+1+12=14; Kenv=15 | \|Gc\|<=eta^-1+1<=2N^2, \|M\|<=1, sum\|rho\|<=L^d C_rho, C-slot<=4N^4, X-factor<=4W^dN^4 | N >= 64 C_rho eventually |

(The table is the script output, rows as printed; `instance:` line = line 1 of `s4_exponents.out` after `tail`.) `t`-bookkeeping: at `t=0` the fold average is `0` (explicit factor `t`) and a `BAG5LeafProps` leaf has `n_W ≥ 2`, so its value is `0` (target 3, `BAlwS 0 = 0`); the bound `t(1-t)⁻¹B^{5/2}` is `0` and `‖0‖ ≤ 0`. At `t>0` the `≺→𝔼` step is applied to `X = twLoop2X(..ρ'..)` with `R = (1-t)⁻¹B^{5/2}` (floor row), then multiplied by `t`; the S3 integrand is `t⁻¹ ×` the root average, so `t` cancels uniformly in `t`. List lengths are syntactic, independent of `n, d, t`: finite, `MERGED` 2648/2490, `T3C-tr_1` 2539/2381, `D2X` 109/109 (+7, +7, +0 stuck) over all BACtx choices; 1196/1134/62 nodes (2/2/0 fold) when the first candidate is taken (`s5_census.out`).

**Leaf census for L4c2 / L4g (report only).** `python3 s5_census.py | sed -n 10,16p | cut -c1-175` ('all' BACtx choices; fold = stuck nodes):
```
  MERGED    s=1 total 2655 | fold 7 | BAG5 leaves 2648: nM=0 1487, nM=1 1161 ; tied atoms 182, apart 2466 ; ext molecules one  411 two 2237
     breakdown (nM, atoms, molecules): (0, 'apart', 'oneMol')=229, (0, 'apart', 'twoMol')=1129, (0, 'tied', 'oneMol')=129, (1, 'apart', 'twoMol')=1108, (1, 'tied', 'oneMol')=53
  MERGED    s=0 total 2497 | fold 7 | BAG5 leaves 2490: nM=0 1427, nM=1 1063 ; tied atoms 182, apart 2308 ; ext molecules one  411 two 2079
  T3C-tr_1  s=1 total 2546 | fold 7 | BAG5 leaves 2539: nM=0 1378, nM=1 1161 ; tied atoms 169, apart 2370 ; ext molecules one  355 two 2184
  T3C-tr_1  s=0 total 2388 | fold 7 | BAG5 leaves 2381: nM=0 1318, nM=1 1063 ; tied atoms 169, apart 2212 ; ext molecules one  355 two 2026
  D2X       s=1 total  109 | fold 0 | BAG5 leaves  109: nM=0  109, nM=1    0 ; tied atoms  13, apart   96 ; ext molecules one   85 two   24   (s=0 equal)
```
`n_M=1` leaves need the `GtoAG` half (L4c2); `n_M=0` leaves are L4g's half; all tied leaves lie in one external molecule (`x~y` count). The 229 `(0,apart,one)` leaves (x, y in one molecule, different atoms) fall under `BAG5LeafPrec` as pinned, which has no distinct-molecule hypothesis, unlike `LwGraphPrec1` (`LWExpTerm3:1430`); paper `(Gammamuxy)` (`B_graphical_lemmas.tex:88`) states none.

**`x ~ y` count (S4).** Tied-atom leaves of the six lists with ≤ 8 internal vertices (436 of the 728 tied leaves; larger ones cost > 5 min each in `einsum`), all BACtx choices, valued by `graph_val` (`M`, `g₀Ψ` offset-diagonal; the control shows `G` is not):
```
$ python3 s6b_xy.py A ; python3 s6b_xy.py B | cut -c1-420   # s6_xy_A.out, s6_xy_B.out
model A (L=3 W^d=2): 2527 distinct leaves with <= 8 internal vertices over the 6 lists (all BACtx choices), 436 with x~y; violations of "value = 0 at offset(x) != offset(y)" (rel. 1e-12): 0 ; max |v offdiag-offset|/max|v| = 0.0e+00 ; same-offset entries nonzero in 436 of them (max ratio 1.00) ; control (apart-atom leaves, first 60 of MERGED s=1, n<=6): max |v offset-off|/max|v| = 1.00
model B (L=4 W^d=2): 2527 distinct leaves with <= 8 internal vertices over the 6 lists (all BACtx choices), 436 with x~y; violations of "value = 0 at offset(x) != offset(y)" (rel. 1e-12): 0 ; max |v offdiag-offset|/max|v| = 0.0e+00 ; same-offset entries nonzero in 436 of them (max ratio 1.00) ; control (apart-atom leaves, first 60 of MERGED s=1, n<=6): max |v offset-off|/max|v| = 0.38
```
S4 does not occur (structural reason: `baAtom_offset`; model C not run to completion, killed).

**Section map.** `python3 s8_lines.py | tail -2 | cut -c1-110`: part A (T2 bridge 344 band lines, T3 kit 197) = 541 → ×1.2 = 649, ×2.6 = 1407; part B (T5 `x~y`/pair 110, T6 `T4pos` 97 + `of_expand` 146, rest 5, T7 instances 76) = 434 → 521 / 1128. BA-only content is not in these sums (T1 sub-root; T4 `t`-class, analogue `BAS3CloseC:1043-1265` = 223 lines; defs of 2/4/5/6; fold-leaf branch of T5), so the 1,800 rule cannot be decided from the measured basis alone. File A `BAExp14c`: T1-T4 and defs; file B `BAExp14cB`: T5-T7; `BAExp14cC` reserve.

### (ii) One nondegenerate instance
`d=3`, `sz0` at `n=0` (`L=4, W=32, N=2097152, λ=1/64`), `zSeq`, `t≡1/2`, `κ=1/2`, `ε=𝔡=1/10`, `𝔠=1/6`:
```
$ cd P2450 && python3 instance.py | head -4 | cut -c1-250
mS = 0.000000+0.832488i  zS = 0.000000+0.367512i  Im zS + Im mS = 1.200000 (Lean: 6/5)
t0 = 0.693740 (Lean t0_sz0: >= 2/3)  t = 1/2 < t0: True  g0 = 0.013014  E_flow = 0.00e+00  m_F = 0.000000+0.999493i  mS/sqrt(t0) - m_F = 1.1e-16
BAdom: Im m_F = 0.9995 >= kappa = 1/2: True ; N^(-1+eps) = 2.044e-06 <= Im zS = 0.3675 <= 1: True ; N = 2097152 ; W = 32 >= N^(1/6) = 11.31 ; W^(2*dd) = 2.000 <= lam^2 W^3 = 8.000
(self_m) residual |m - L^-d tr M^B| = 1.1e-16 ; Ward: max_a |sum_c |M^B_ac|^2 - 1| = 1.1e-15 ; symmetric: True
$ cd P2464 && python3 s7_premises.py | cut -c1-290     # external hypotheses: concrete limit computations (TEAM §8 lesson 14)
STLmaxgL k=2 / STLocalEntrygL leading term: W^d L2(a,b) -> [(1-tA)^-1 A]_ab: max 1.9959, row sum 2.0000 (=1/(1-t)=2.0000) vs B_0 = W^d Bctl = 2.0303 : ratio max/B_0 = 0.983 < 1
E|G_xy|^2 leading scale W^-d Kd_ab = 6.091e-05 <= Bctl = 6.196e-05 (ratio 0.983) ; Ward sum_c |M_ac|^2 = 1.000000
STDecaygL / Theta decay: omega=Theta^{++}=(1-tB2)^-1, |kappa_{0a}| by lattice distance r: r=0 3.33e-01, r=1 3.75e-05, r=2 2.11e-08, r=3 3.07e-11, r=4 8.38e-14, r=5 3.64e-16, r=6 2.28e-18 ; sum_a |omega_0a| = 0.6671
leaf pin RHS t^nW eta^-1 B^(ord/2) at the instance: nW=2: ord=3 2.440e-07, ord=5 1.512e-11, ord=7 9.366e-16 ; floor N^(-5/2) = 1.570e-16 ; at t=0 the RHS is 0 and val_zero gives value 0 (nW>=2)
```
Hypotheses at these numbers: `BAFlow sz0 (1/2)(1/10)(1/6)(1/10) zSeq` (`flow_sz0`, `RBM3D/BA/FlowPins.lean:1214`; entries in line 3); `0 ≤ t=1/2 ≤ T₀=0.6937` (`half_lt_t0`, `FlowPins.lean:1254`); `d=3`, `L=4 ≥ 3`, `κ,ε,𝔡 > 0`; `BASelf` (self_m residual 1.1e-16); all block pairs incl. `a=b` and both `σ` (bridge); `Cρ` proxy `1.1724 ≥ 0.5000` (target 4). The five Step 1/2 pins and `BAG5LeafPrec` are external and stay hypotheses of the target-7 examples: their leading terms stay below `Bctl` (ratio 0.983), `Θ` decays (`r=1` is 1e-4 of `r=0`), and the leaf pin's right side exceeds the polynomial floor (1.5e-11 vs 1.6e-16 at ord 5). Target 7 lists: `MERGED`'s list at `s=false` holds `BAG5LeafProps` leaves (1194 with the first-candidate rule, 2490 over all choices) and fold nodes (2 / 7); the root term `#2` has no `BACtx` candidate (T2433-prove table, `(4,-1,0,2,0,0,0)`), so it is stuck for every selector, and both disjuncts of `BAS3CloseT` occur; `rT0` has 16 partition terms for both `s`.

### Verdicts
- Target 1 (sub-root, partition, list, identity): **PASS** (pin = `roots.py` T3C0; S2 not triggered).
- Target 2 (bridge, four identities): **PASS** (≤ 2.2e-15 at models A-C, controls ≥ 1.4e-3; S1 not triggered).
- Target 3 (`val_zero`, envelope, floor, `η ≤ 1`): **PASS** (`BAlwS 0 = 0`; K=15 count above).
- Target 4 (`BAFoldLeafT`, congr, weaken, catalogue, `BAS3CloseT`): **PASS** (spare `t` in all 14; S3 not triggered).
- Target 5 (`xy` support, `BAG5LeafPrec` statement, `BAS3LeafAvg`): **PASS** (all branches close, ord 5 exactly; S4 not triggered).
- Target 6 (assembly `BAG5LeafPrec → BAExp14bS3`, `t=0` and `t>0`): **PASS**. Target 7 (instances): **PASS**.

### (a′) Preflight corrections — Mon Oct 12 19:26:46 UTC 2026 (`date -u`)
- (a)(i) fold-envelope row (`Kenv = 15`, `|Ǧ| ≤ η⁻¹+1 ≤ 2N²`): the pin `T2464_val_env` has no `0 < ε` (target 3 shares the scale), so Lean uses `η⁻¹ ≤ 2κ⁻¹N^{1-ε}` and the scale `N^c`, `c = |1-ε|+1` (fold envelope `N^{2+8c}`, `BAExp14c_Y_le`). No verdict of (a) changes.

## (b) Script output — Mon Oct 12 19:26:46 UTC 2026
Worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2464`, branch `t/T2464`, base a1628b9d, 7 commits `99d76d45..51f5a5b8` (`git log --oneline main..t/T2464`). `BAExp14cC.lean` not created.
```
$ wc -l RBM3D/Graph/BAExp14c.lean RBM3D/Graph/BAExp14cB.lean     # stop line 2,000 per file (binding)
     919 RBM3D/Graph/BAExp14c.lean
    1153 RBM3D/Graph/BAExp14cB.lean
# 1a verdict PASS; S1-S4 did not occur in Lean either (bridge proved as pinned, `baS3RootT0_sub` proved, `baS3FoldT_holds` via the private route,
# `BAExp14c_xy_support` proved); Lean stops: none (files < 2,000, no pin changed, no `inductive`, `Test/Axioms.lean` unchanged)
$ lake build RBM3D.Graph.BAExp14c RBM3D.Graph.BAExp14cB 2>&1 | tail -1
Build completed successfully (4032 jobs).
$ # RBM3D.lean + 2 import lines (hub-owned; restored from a copy, NOT committed): lake build 2>&1 | tail -1; audit line
Build completed successfully (4292 jobs).
info: RBM3D.lean:524:0: axiom audit: 13488 theorems, 4285 definitions, 0 axioms in `RBM` ... All within [propext, Classical.choice, Quot.sound]
$ # same build without the 2 lines (the branch library at base a1628b9d, 4290 jobs); diff of the two 230-line audit blocks (premise scan): lines 1 and 230 only
< info: RBM3D.lean:522:0: axiom audit: 13455 theorems, 4277 definitions, 0 axioms      > ... :524:0: ... 13488 theorems, 4285 definitions, 0 axioms   (+33, +8 = the 41 public declarations)
$ (regex ^(theorem|def) over the two files -> 41 names); lake env lean axioms.lean   # one `#print axioms` per name; sed/awk keep the axiom list
$ ... | sort | uniq -c
     41 [propext, Classical.choice, Quot.sound]
$ python3 pindiff.py | awk '{print $3}' | sort | uniq -c        # statement bodies vs T2464-check.lean, names normalised (T2464_ and rT0 stripped)
  14 IDENTICAL
$ # scratch copy of the check file (+2 imports, + the 16 lines below, not committed): lake env lean check_scratch.lean; echo exit=$?   -> exit=0
example : T2464_rootT0_eq baS3RootT0 := fun s => rfl
example : T2464_rootT0_sub baS3RootT0 := baS3RootT0_sub
example : T2464_rootT0_list baS3RootT0 := baS3RootT0_list
example : T2464_rootT0_identity baS3RootT0 3 := baS3RootT0_identity 3
example : T2464_BAS3Bridge baS3RootT0 3 := baS3Bridge_holds 3
example : T2464_val_zero := BAExp14c_val_zero
example : T2464_val_env := BAExp14c_val_env
example : T2464_foldTCongr := baFoldLeafT_congr
example : T2464_foldT_weaken := baFoldLeafT_fold
example : T2464_foldT_cat := baS3FoldT_holds
example : T2464_BAS3CloseT := baS3CloseT_holds
example : T2464_xy_support := BAExp14c_xy_support
example (d : ℕ) : T2464_BAG5LeafPrec d = BAG5LeafPrec d := rfl
example (d : ℕ) : T2464_BAS3LeafAvg d := baS3LeafAvg_holds d
example (d : ℕ) : T2464_S3OfLeaf d := baExp14bS3_of_leaf d
example (q : BAPGraph (Fin 2)) : T2464_BAFoldLeafT q = BAFoldLeafT q := rfl
```
Target statements, extracted by `stmts.py` (file:line, first 148 chars; every `∀`/hypothesis list is in the file):
```
BAExp14c:58 def baS3RootT0 (s : Bool) : BAGraph (Fin 2) (Fin 4) :=
BAExp14c:77 theorem baS3RootT0_sub : ∀ s : Bool, ∀ P ∈ (baS3RootT0 s).partition, P ∈ (baS3RootM s).partition := by …
BAExp14c:86 theorem baS3RootT0_list : ∀ (sel : BASel) (fuel : ℕ) (s : Bool), ∀ q ∈ (baS3RootT0 s).partition.flatMap (fun P => (BAexpand sel fuel P).
BAExp14c:94 theorem baS3RootT0_identity (d : ℕ) : ∀ (sel : BASel) (fuel : ℕ) (L W : ℕ) [NeZero L] [NeZero W], 3 ≤ L → ∀ (g0 E t : ℝ) (m : ℂ), BASelf
BAExp14c:383 def BAS3Bridge (d : ℕ) : Prop :=
BAExp14c:403 theorem baS3Bridge_holds : ∀ d : ℕ, BAS3Bridge d := by …
BAExp14c:440 theorem BAExp14c_val_zero : ∀ (d : ℕ) (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ) (ω : sz.SeqΩ) (P : BAPGraph (Fin 2)), P.g.nW ≠ 0 → ∀ ℓ : Fin 2
BAExp14c:666 theorem BAExp14c_val_env : ∀ (d : ℕ), 3 ≤ d → ∀ (κ ε 𝔠 𝔡 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), 0 < κ → BAFlow sz κ ε 𝔠 𝔡 z → ∀ P : BAPGraph 
BAExp14c:712 theorem BAExp14c_eta_le_one {d : ℕ} {sz : Sizes d} {z : ℕ → ℂ} {κ ε 𝔠 𝔡 : ℝ} (hκ : 0 < κ) (hflow : BAFlow sz κ ε 𝔠 𝔡 z) (n : ℕ) {t : ℝ}
BAExp14c:725 theorem BAExp14c_floor {d : ℕ} {sz : Sizes d} {z : ℕ → ℂ} {κ ε 𝔠 𝔡 : ℝ} (hκ : 0 < κ) (hflow : BAFlow sz κ ε 𝔠 𝔡 z) (n : ℕ) {t : ℝ} (ht0
BAExp14c:771 def BAFoldLeafT (q : BAPGraph (Fin 2)) : Prop :=
BAExp14c:791 theorem baFoldLeafT_congr : ∀ q q' : BAPGraph (Fin 2), (∀ {ι : Type} [Fintype ι] [DecidableEq ι] (D : BALData ι) (ℓ : Fin 2 → ι), q.val
BAExp14c:801 theorem baFoldLeafT_fold : ∀ q : BAPGraph (Fin 2), BAFoldLeafT q → BAFoldLeaf q := by …
BAExp14c:832 theorem baS3FoldT_holds : ∀ (k : Bool) (j : Fin 7) (s : Bool), BAFoldLeafT (baS3Stuck k j s) := by …
BAExp14c:867 def BAS3CloseT : Prop :=
BAExp14c:870 theorem baS3CloseT_holds : BAS3CloseT := by …
BAExp14cB:55 theorem BAExp14c_xy_support : ∀ (d : ℕ) (κ ε 𝔠 𝔡 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z → ∀ (n : ℕ) (t : ℝ), 0 ≤ t → t ≤ 
BAExp14c:884 def BAG5LeafPrec (d : ℕ) : Prop :=
BAExp14c:900 def BAS3LeafAvg (d : ℕ) : Prop :=
BAExp14cB:642 theorem baS3LeafAvg_holds : ∀ d : ℕ, BAS3LeafAvg d := by …
BAExp14c:915 def BAExp14bS3OfLeaf (d : ℕ) : Prop := BAG5LeafPrec d → BAExp14bS3 d
BAExp14cB:832 theorem baExp14bS3_of_leaf : ∀ d : ℕ, BAExp14bS3OfLeaf d := by …
```
Compiled nonempty instances (namespace `BAExp14cInst`, `BAExp14cB.lean:935-1150`; `d = 3`, `sz0`, `zSeq`, `flow_sz0`, `n = 0` or `t ≡ 1/2`, `half_lt_t0`; every deterministic hypothesis discharged, the leaf pin `BAG5LeafPrec 3` and the five Step 1/2 pins are hypotheses of the examples of targets 5, 6 only):
```
T1 :951 rootT0_inst (s) (partition ≠ [], P ∈ both partitions, q ∈ both lists, q a BAG5LeafProps leaf); :961 rootT0_inst_identity (d=3,L=3,W=1,t=1/2)
T2 :972 example (ω σ a b) := baS3Bridge_holds 3 (1/2) (1/10) (1/6) (1/10) sz0 zSeq flow_sz0 0 (1/2) (by norm_num) (half_lt_t0 0).le ω σ a b
T3 :981 val_zero at the anchor (nW = 2, :978 anchor_nW); :987 val_env; :990 eta_le_one; :994 floor at an n with N ≥ 4, B ≤ 2, all o : ℤ
T4 :1006 foldT_rho0 (ρ' = (1/2)·1[c₃=c₁ ∧ c₄=c₂](M^(B)_{c₁c₂})²); :1028 foldT_anchor; :1063 closeT_inst (leaf and fold leaf in MERGED's list, s=false); :1068 baS3CloseT_holds
T5 :1075 tiedGraph (M-dotted x–y), :1082 tiedGraph_atom, :1085 offsets_exist, :1095 xy_support; :1103 fold leaf, :1118 G5 leaf of baS3LeafAvg_holds
T6 :1134 baExp14bS3_of_leaf 3 hpin; :1137 the same at sz0, zSeq, t ≡ 1/2 with the five premises as hypotheses
```
Name clash (`git grep -wE` of the 41 public names, in `RBM3D` and `docs/tickets/checks`): `main`: no declaration; hits only in `docs/tickets/checks/T2464-T2466-check.lean` and in comments of `Graph/BAExp14dB.lean` (merged T2466: its `BAG5LeafPrec1` is the `n_M = 1` half). The other 134 `t/T24*` refs: only the same check files (t/T2457, T2462b, T2463, T2466, T2468) and the `BAExp14dB.lean` comments on t/T2466, t/T2468; no branch `t/T2465` exists.
```
$ grep -nwE 'mE|STGM|STKloop|etaT|STflowE|lwS|lwSplus' RBM3D/Graph/BAExp14c.lean RBM3D/Graph/BAExp14cB.lean; echo $?        -> 1 (no match; C1)
$ grep -nE 'sorry|admit|native_decide|^axiom' RBM3D/Graph/BAExp14c.lean RBM3D/Graph/BAExp14cB.lean; echo $?                -> 1 (no match)
$ git diff --stat main...t/T2464
 RBM3D/Graph/BAExp14c.lean  |  919 +++...   RBM3D/Graph/BAExp14cB.lean | 1153 +++...   2 files changed, 2072 insertions(+)   # only the sole writable files; RBM3D.lean untouched
```

Narrative (route; every fact is in the files above)
- Target 1: `baS3RootT0_sub` is one unfolding of `baSplitSolid` at the first edge (`BAExp14c_split_circ`: the circled child is the first child of the uncircled edge); `_list` is `List.mem_flatMap` with it; `_identity` is the private `BAS3Close_root_identity` (`open private`, precedent `BAS3CloseC:41-50`); no merged file is edited.
- Target 2: four `sum_pi_fin_succ` shape lemmas (`BAExp14c_shapeT0/M/T1/D`) and a pointwise lemma per family (`BAExp14c_ptT0/D1/T1/D2`): the black edge `S(i0,i3)` is the block sum with the factor `t` (`BAS3Close_blk_sum`), `W^(0) = 1` collapses `α = w`, `W^(1) = M⁺ S W` is the `hWe` step of `BAExp14a_W_sub_one` (`baW_mul`), the `b`-sum is moved by `BAExp14c_insb`; `MERGED = T3C-tr_0 + D1X` is `G = M + Ǧ` on the first edge (`BAExp14c_valM_split`).
- Target 3: `BAExp14c_val_norm_le` (edge-by-edge bound, `|ι|^{n_V}` labellings), the entries of the carrier in one scale `N^c` (`BAExp14c_entries`: `S⁺` through `BAS3Close_D_Sp`, `g₀Ψ` through `BAAtom_PsiI_apply`), `val_zero` from `BAlwS 0 = 0`; the BA floor needs `B ≤ 2` (the band has `B ≤ 1`).
- Target 4: `t · BAS3Close_rho (1+qq) = BAS3Close_rho (2+qq)` (`ring`) and `BAS3Close_Bd_of (1+qq)` give `BAExp14c_foldT_gen`; the 14 cases as in `baS3Fold_holds`.
- Target 5: `BAExp14c_xy_support` is `baAtom_offset` (a nonzero term forces equal offsets); `BAExp14a_pair_count` gives the factor `W^{-d}`. G5 branch: `hpin` per pair, then `BAExp14c_avg_le(_tied)`. Fold branch: `twFold2Prec_holds` with the flag factor (`e = false`: `TwistFold2_one_prec`; `e = true`: `baS3Xprec_holds`), the envelope `BAExp14c_Y_le`, `BAExp14a_prec_integral` with `BAExp14a_floor`, then `BAExp14c_twLoop2X_smul` restores `t`.
- Target 6: expectations carried from `PF` to the carrier law (`BAExp14c_int_slice`; integrability by `BAExpandId_integrable_{val,pval}` and `integrable_map_measure`); `BAExp14c_fam_E` (families against the lists, `D1X = MERGED - T3C-tr_0` pathwise); union bound over the finite lists (`Λn`, independent of `n`); `t = 0` by `BAExp14c_FS3_zero`; `σc = false` by `integral_conj`.
- Instances: the leaf witnesses are `decide +kernel` (`rT0`: `BAS3Close_RootFacts` and the MCM test); the fold occurrence is the proof of `BAS3Close_inst_fold` ending in `baFoldLeafT_congr`.

## (c) Verified Mathlib names (present: compiled; absent or deprecated: unknown-identifier errors / warnings of the tool log)
- present: `Real.rpow_le_rpow_of_nonpos`, `Real.rpow_add`, `Real.rpow_mul`, `Real.rpow_natCast`, `Real.rpow_one_add'`, `Real.rpow_le_rpow_of_exponent_le`, `Real.one_le_rpow`, `Real.inv_rpow`, `Real.rpow_neg`
- present: `integral_conj` (root namespace), `integral_finsetSum`, `integrable_finsetSum`, `integrable_map_measure`, `integral_map`, `integral_sub`, `integral_const_mul`, `integral_congr_ae`
- present: `Filter.eventually_all_finite`, `Filter.eventually_all`, `List.finite_toSet`, `List.sum_map_mul_left`, `List.exists_mem_of_ne_nil`, `pow_le_of_le_one`, `one_le_inv₀`, `inv_anti₀`, `RCLike.norm_conj`, `Complex.norm_real`, `Complex.star_def`, `tendsto_natCast_atTop_iff`, `Fin.sum_univ_three`
- absent: `MeasureTheory.integral_conj`, `RCLike.integral_conj`, `norm_list_sum_le`, `List.norm_sum_le`; deprecated: `integral_finset_sum`, `integrable_finset_sum` (use `…finsetSum`), `List.sum_le_card_nsmul` (use `List.sum_le_length_nsmul`), `if_pos`/`if_neg` (use `simp only [h, ↓reduceIte]`)

## (d) Open issues and paper-delta candidates
- No Lean/paper statement difference arose; no paper-delta candidate `T2464a` is proposed. 14 pinned bodies are identical by script; `T2464_rootT0_eq` is `fun s => rfl`, `T2464_rootT0_identity` is the typed example of the scratch check.
- The leaf pin `BAG5LeafPrec` is, as pinned, over every `BAG5LeafProps` leaf with no distinct-molecule hypothesis (the 229 `(0,apart,one)` leaves of (a)); its producers: the `n_M = 1` half is `BAG5LeafPrec1` (merged T2466, extra hypothesis `P.g.nM = 1`), the `n_M = 0` half is L4g.
- `RBM3D.lean` is not edited (hub-owned): at merge add `import RBM3D.Graph.BAExp14c` and `import RBM3D.Graph.BAExp14cB` (the full build with these two lines is above).
- Public helpers beyond the targets (stem-prefixed, no pinned-premise binder): `BAExp14c_etainv`, `_scale`, `_int_slice`, `_integrable_val`, `_integrable_graph`, `_int_avg`, `_avg_le`, `_avg_le_tied`; the instance facts are in `BAExp14cInst`.
- `open private` of `BAS3Close*`, `BAVocab`, `BAExpandId` names as in `BAS3CloseC:41-50`; `Test/Axioms.lean` unchanged; no new `inductive`.
- `BAFoldLeafT`, `BAS3CloseT` are defined here; the T2465 check file (released on main) mentions only `BAG5LeafPrec`, `baExp14bS3_of_leaf` (dispatcher note 4).
