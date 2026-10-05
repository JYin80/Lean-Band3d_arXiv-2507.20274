Prover model: claude-sonnet-5-5

## (a) Math preflight — Mon Oct  5 03:53:58 UTC 2026

Notation: V = |E ⊕ I|, N = (WL)^d, A = n_W − n_V + n_M (≥ 0), mS = |molSolid|, `ord c = n_S + 2(n_W − n_V)` (RBM3D/Graph/ScalingOrder.lean:65), `auxOrd = mS − 2 n_M`.

**(i) Exponent table.**

| # | quantity | value | constraint | slack |
|---|---|---|---|---|
| 1 | `ord Γ − auxOrd Γ` | `(n_S − mS) + 2A` (identity, every Γ) | `mS ≤ n_S` (molSolid ⊆ solid); `A ≥ 0` (`counters_le`: n_V − n_M ≤ n_W, Normal ⇒ no `=`-dotted) | figGraph (n_S,n_W,n_V,n_M,mS)=(8,4,6,2,6): 2+2·0=2 (A tight); localReg2_inst_Q (4,1,2,1,4): 0+2·0=0 (both tight); 20000 random normal graphs: 0 violations, 2182 tight in both |
| 2 | `W`-power of the confined part | `(W^d)^{n_M} · (C W^{-d})^{A} · K₁^{n_V−n_M}` | roots: one per internal molecule, `W^d` points per block (`card_Iblk`); tree edges (n_V−n_M of them) cost a row/column sum K₁; each non-tree waved edge costs the entry bound `C W^{-d}`; matches the paper's `W^{-d(n_W−n_V+q)} W^{qd}`, `q = n_M` (`7_8:922-926`) | A ≥ 0 exactly the number of non-tree waved edges; nothing is lost |
| 3 | `Ψ`-power | `e = (n_S − mS) + 2A = ord − auxOrd ≥ 0` (integer `zpow` exponent) | `W^{-dA} ≤ Ψ^{2A}` from `W^{-d} ≤ Ψ²` ⇔ window `W^{-d/2} ≤ Ψ` (`one_le_pow_mul_sq_iff`); `Ψ > 0` follows from the window; no `Ψ ≤ 1`, no `L^d ≤ W^K` | instance: `W^{-d/2} = 0.3536 ≤ Ψ = 1/2`, `W^d Ψ² = 2 ≥ 1` |
| 4 | `K₀, K₁, K₁'` | `K₀ = C`, `K₁ = C·expC(d−2) c`, `K₁' = C·expC(d−2)(c/2)` (`lwKBound_of_decay` at `c` and `c/2`, `0 ≤ C`, `0 < c`, `3 ≤ d`); `sizeConst = ‖coeff‖ K₁^{n_V−n_M} K₀^{A}` | depend on the graph and `(d, C, c)` only | fitted `(C,c)=(0.2,1)`: K₁=1280 vs actual row/col sum 0.5; K₁'=19712 vs weighted 0.695 (checked ≤, script below) |
| 5 | confinement | confined = every waved edge has `lwBdist ≤ r`; in a normal graph molecules = components of waved edges; a simple path has ≤ V−1 steps; `lwBdist` triangle from `zdistD_add_le`, `zdistD_neg`, `lwBdist_comm` ⇒ two vertices of a molecule are at `lwBdist ≤ (V−1) r` | used: `hξ` at radius `R ≥ V r` (target 3), premise `lwBdist(ℓa,ℓb) > V r` (target 4) | slack `R − (V−1) r ≥ r ≥ 0`; `r = 0` allowed (confined = same block; checked at r=0 below) |
| 6 | tail | non-confined ⇒ some waved edge `> r` ⇒ `∏|w| ≤ e^{-cr/2} ∏|w| e^{(c/2) lwBdist}`; weighted kernels `≤ C W^{-d} e^{-(c/2) lwBdist}`; result `e^{-cr/2} sizeConst(C,K₁') size(Γ)`, `size = (L^d)^{n_M} Ψ^{n_S} W^{-d(n_W−n_V)}` | consumer only (not a premise): `size ≤ W^{(K₀'+d)n_M}` from `L^d ≤ W^{K₀'}`, `Ψ ≤ 1`, `n_V−n_W ≤ n_M`; `n_M ≤ p` (`LocReg2` 1st conjunct) ⇒ `D' = D + (K₀'+d)p` | the form of `r` is not in any target; see row 6a |
| 6a | choice of `r` (consumer, LW-11b/LW-02) | (a) literal `r=(log W)^{3/2}` (ticket): `R = V (log W)^{3/2}`; the target-4 premise is `> V (log W)^{3/2}`, but `(eq:far_ab)` (`7_8:96`) is only `|a−b| > (log W)^{3/2}`: the band `(log W)^{3/2} < |a−b| ≤ V(log W)^{3/2}` is uncovered. (b) recommended `r = (log W)^{3/2}/V`, `lwTail_log32` at `c/V` (needs `(log W)^{1/2} ≥ 2VD'/c`): `R = (log W)^{3/2}`, `(eq:far_ab)` is exactly the target-4 premise (`zdistInf ≤ zdistD`, `Sizes.lean:117`, passes `ℓ^∞` data to `ℓ¹`); LW-11b's `ξ` must then cover `ℓ^∞` radius `(log W)^{3/2}` instead of the paper's `(log W)^{1+2ε₁}`. (c) `r=(log W)^{1+ε₁}/V`, `R=(log W)^{1+ε₁}` inside the paper's radius, needs a new `lwTail` at exponent `1+ε₁` (merged one is `3/2` only) | limit computed in (ii) | none for T2170 |
| 7 | composition with `LWAnp` (`7_8:945`) | target 3: `Ψ^{ord Γ − auxOrd} (W^d)^{n_M} auxVal`; `LWAnp`: `auxVal ≺ (W^d η)^{-q} Φ(c|a−b|)^p Φ0^{ordN − p}`, `q = n_M`, `ordN = auxOrd` ⇒ `η^{-n_M} Ψ^{ord Γ − p} Φ(c|a−b|)^p` | exponents add: `(ord−auxOrd) + (auxOrd−p) = ord − p`; `(W^d)^{n_M} (W^d η)^{-n_M} = η^{-n_M}` | exact |
| 8 | target 5 counts | `|es| = mS` (walk steps by `LocReg3` plus the unused remainder), `ordN = |es| − 2 n_M = auxOrd`; `q = n_M ≤ p` (`LocReg2`); `0 < p` (unused edges go to `a_0, b_0`) | `IsNested` (1)-(6) hold from `LocReg3,4,5` and `𝓜_x ≠ 𝓜_y` (no loops: steps are off-diagonal since `LocReg3`'s multiset bound excludes diagonal pairs; `LocReg4`/`5` ⇒ NGraph (5)/(6): graph visits ⊇ walk visits) | at loc2, p=2: es = 4 = mS, ordN = 2 = auxOrd, 1 ≤ 2 |

Consumer check (§45 O2): `LWAnp` (`LWPins.lean:409`): `q ≤ p` = `LocReg2.1`, `NoGhost`/`IsNested` = target 5 (`q = Q.g.nM`, needs `0<p`, `𝓜_x≠𝓜_y`), value `Γ.val ξ (fun _=>a) (fun _=>b)` = `auxVal` for symmetric `ξ` (`LWXi` conjunct 1: `0 ≤ ξ`, `ξ = ξᵀ`), factor `Φ0^(ordN−p)` with `ordN = auxOrd` (target 5). `LWMoment` (LW-02): `lw_localregular_upto5` outputs are `LocStd` (`LWLvl1.lean:3204`: includes `Normal`) with `LocReg345` ⇒ target 3 (`hext` from `ext_surj` + `𝓜_x≠𝓜_y`: `Q.E'` is `{ext 0, ext 1}`) + target 5 + `LWAnp`; outputs with `𝓜_x = 𝓜_y` under `(eq:far_ab)` ⇒ target 4 with row 6a(b). `LWtermEXP` (LW-14, `B:84-90`): target 3 for `Γ_{μ,xy}`, `q = n_M ∈ {0,1}`, `Ψ = (W^{-d}B)^{1/2}`; `hext` (x,y in different molecules) is LW-14's premise to check, target 4 only covers the far case. `LWAnpKeyGh` (LW-13): target 5's `Γa` is `NoGhost` ⇒ `GhostOK`, but ghost edges arise inside LW-13's induction: no premise supplied. BA-L3 (`B:488`): its auxiliary graph has waved edges (`eq:ordGaux_BAM`: `#solid + 2#waved − 2#internal`), so `auxOrd`/`auxVal` (n_W = 0) do not match; only the confinement/tail lemmas are shared.

Route notes for stage 1b (mathematics; none blocks a target):
- (N1) `lwForest_sum_le` (generic in `ι, E, I, J`, `LWSizeClaim.lean:637`) sums the root labels uniformly, but step (d) needs the fixed-root bound `Σ_children ∏ ≤ K₁^{|C|} a^{n_W−|C|}` (the weight `∏ξ` depends on the roots). It follows from the merged lemma with `E' = E ⊕ {roots}`, `I' = C` (children): then `C = I'` is the whole forest and `N^{|C|}Σ ≤ N^{|C|} K^{|C|} a^{…}`; no copy of the private `lwForest_core` needed.
- (N2) roots: non-`C` internal vertices number `|I| − |C| = n_M` (`exists_forest`); each internal molecule has ≥ 1 (the parent chain has strictly decreasing rank, stays in the molecule through waved edges, cannot reach an external vertex, ends outside `C`), so exactly one each and none lies in an external molecule.
- (N3) `LGraph.term_norm_le` has no `ξ`; step (c) needs its case split (a non-zero term has distinct labels at the ends of every non-loop solid edge, Normal (iii)) with cross-molecule edges bounded by `hξ` in the orientation `G(ℓ src, ℓ dst) ≤ ξ(auxLab src, auxLab dst)` (`‖star g‖ = ‖g‖`).
- (N4) `PGraph.ext_surj` makes `Q.E'` the image of `Fin 2`; with `𝓜_x ≠ 𝓜_y` the `choose` in `auxLab` returns `ext 0` / `ext 1`.
- (N5) In the target-4 instance `instXY` take the waved edge coloured (`S^+_{xy}`): with the plain `S` (block range 1) the value is exactly 0 at block distance 6 (void), with `S^+` it is 1.08e-7 > 0.

**(ii) One concrete nondegenerate instance** (`d=3, L=4, W=2, g=t=1/2, E=0` so `m=i`, `N=512`, `Ψ=1/2`; `lwSizeD0` with `1/2`; `Λ=1, κ=1/2`: `|E|=0 ≤ 3/2`, `g ≤ Λ`, `t<1`). The decay pair `(C,c)` comes from the merged `lwSpOf_decay_E` (proved, no external input; the sample premises `|G|`, `hξ` are other gates' pins, here instantiated by numbers); in the script `(C,c)` is fitted.
Command: `cd /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/e2e8bc03-a5c7-4581-b49e-f30bd123d3b2/scratchpad/T2170 && python3 pre1.py`
```
figGraph normal=True (nS,nW,nV,nM,|molSolid|)= (8, 4, 6, 2, 6) ord=4 auxOrd=2 diff=2 rhs=(nS-|mS|)+2(nW-nV+nM)=2 nV-nM<=nW: True
localReg2_inst_Q normal=True (nS,nW,nV,nM,|molSolid|)= (4, 1, 2, 1, 4) ord=2 auxOrd=2 diff=0 rhs=(nS-|mS|)+2(nW-nV+nM)=0 nV-nM<=nW: True
random normal graphs tested: 20000 violations: 0 tight (both equalities): 2182
```
Command: `python3 pre3.py` (targets 3, 4 data, tail limit):
```
window: W^(-d/2) = 0.3535533905932738 <= Psi = 0.5 : True ; 1 <= W^d Psi^2 = 2.0
|G_xy| (x!=y) max = 0.5  |G_xx - m| = 0.5  N = 512
fitted (C,c) = (np.float64(0.2), 1.0)  S(0,0) = 0.025  S^+(0,0) = 0.01972
figGraph: |E+I| r = 8  R = 8  blocks of ell_e: 0 0  max block distance = 6
auxVal(figGraph, xi=1/2, [ell_e]) = nb^nM * (1/2)^|mS| = 64.0 (expected 64^2 * 2^-6 = 64)
|val(figGraph)| = 57.09468317413328  Psi-exponent = 2  main = 2748779069440000.0  tail = 9.377249634141803e+19  |val| <= main+tail: True
instXY: blocks 0 42  lwBdist = 6  > |E+I| r = 2
 waved S_xy (col=false) : (nS,nW,nV,nM) = (2, 1, 0, 0)  |val| = 0.0  tail = 0.003790816623203959  |val|<=tail: True  (G-product |G_xy|^2 = 0.25 )
 waved S^+_xy (col=true) : (nS,nW,nV,nM) = (2, 1, 0, 0)  |val| = 1.0839854589854618e-07  tail = 0.003790816623203959  |val|<=tail: True  (G-product |G_xy|^2 = 0.25 )
tail limit: V=4 c=1 D'=3 threshold log W0=576; at log W=581.8: log(lhs)=-1754.0 <= log(rhs)=-1745.3: True
tail limit: V=8 c=1 D'=3 threshold log W0=2304; at log W=2327.0: log(lhs)=-7015.9 <= log(rhs)=-6981.1: True
```
Command (falsification test of target 3, TEST 1 = localReg2_inst_Q with V=4, 512² labellings, TEST 2 = triangle molecule `A=1`, light weight, inside solid edge, `N=216`; `ξ` = smallest admissible function for radius R; `main/tail_stated` = the pin's constants with `K₁, K₁'`; `main_tight` uses actual row sums; `OK` = |val| ≤ main+tail and conf ≤ main and unconf ≤ tail, stated and tight):  `python3 pre2.py | grep -v '^  \['`
```
TEST 1: localReg2_inst_Q, d=3 L=4 W=2 (N=512), g=t=1/2, E=0 (m=i), Psi=1/2
  loc2 flat r=0 R= 0: |val|=1.594e+01 conf=6.375e+00 unconf=9.563e+00 | main_tight=1.600e+01 tail_exact=2.223e+01 | main_stated=4.10e+04 tail_stated=6.31e+05 | auxVal=4.000 OK=True
  loc2 flat r=1 R= 4: |val|=1.594e+01 conf=1.594e+01 unconf=0.000e+00 | main_tight=1.600e+01 tail_exact=1.348e+01 | main_stated=4.10e+04 tail_stated=3.83e+05 | auxVal=4.000 OK=True
  loc2 flat r=2 R= 8: |val|=1.594e+01 conf=1.594e+01 unconf=0.000e+00 | main_tight=1.600e+01 tail_exact=8.177e+00 | main_stated=4.10e+04 tail_stated=2.32e+05 | auxVal=4.000 OK=True
  loc2 decay r=0 R= 0: |val|=3.120e-01 conf=1.227e-01 unconf=1.893e-01 | main_tight=9.073e-01 tail_exact=2.223e+01 | main_stated=2.32e+03 tail_stated=6.31e+05 | auxVal=0.227 OK=True
  loc2 decay r=1 R= 4: |val|=3.120e-01 conf=3.120e-01 unconf=0.000e+00 | main_tight=1.599e+01 tail_exact=1.348e+01 | main_stated=4.09e+04 tail_stated=3.83e+05 | auxVal=3.997 OK=True
  loc2 decay r=2 R= 8: |val|=3.120e-01 conf=3.120e-01 unconf=0.000e+00 | main_tight=1.599e+01 tail_exact=8.177e+00 | main_stated=4.09e+04 tail_stated=2.32e+05 | auxVal=3.997 OK=True
TEST 2: triangle molecule (A=1, light weight, inside solid edge), d=3 L=3 W=2 (N=216), Psi=0.6
  tri flat r=0 R= 0: |val|=8.379e-05 conf=1.147e-02 unconf=1.424e-02 | main_tight=1.050e-01 tail_exact=5.745e-02 | main_stated=1.98e+06 tail_stated=1.63e+08 | auxVal=5.832 OK=True
  tri flat r=1 R= 5: |val|=8.379e-05 conf=2.538e-02 unconf=3.286e-04 | main_tight=1.050e-01 tail_exact=3.484e-02 | main_stated=1.98e+06 tail_stated=9.90e+07 | auxVal=5.832 OK=True
  tri flat r=2 R=10: |val|=8.379e-05 conf=2.571e-02 unconf=0.000e+00 | main_tight=1.050e-01 tail_exact=2.113e-02 | main_stated=1.98e+06 tail_stated=6.00e+07 | auxVal=5.832 OK=True
  tri decay r=0 R= 0: |val|=9.480e-06 conf=5.947e-04 unconf=5.726e-04 | main_tight=2.205e-02 tail_exact=5.745e-02 | main_stated=4.16e+05 tail_stated=1.63e+08 | auxVal=1.225 OK=True
  tri decay r=1 R= 5: |val|=9.480e-06 conf=1.156e-03 unconf=1.153e-05 | main_tight=1.048e-01 tail_exact=3.484e-02 | main_stated=1.98e+06 tail_stated=9.90e+07 | auxVal=5.821 OK=True
  tri decay r=2 R=10: |val|=9.480e-06 conf=1.167e-03 unconf=0.000e+00 | main_tight=1.048e-01 tail_exact=2.113e-02 | main_stated=1.98e+06 tail_stated=6.00e+07 | auxVal=5.821 OK=True
ALL TESTS OK: True
```
Command (target 5, random walk families satisfying LocReg3,4,5 incl. revisits, mid-walk visits of `𝓜_x,𝓜_y`, unused edges; checks `IsNested` (1)-(6), `|es| = mS`, multiset identity of label pairs = `auxVal`'s, tested for q ≤ 3): `python3 pre4.py`
```
random (walk family satisfying LocReg3,4,5) examples constructed: 38055  all of IsNested(1-6), value identity, |es|=|molSolid| hold: True
{'q1': 4931, 'q2': 676, 'q3': 22, 'revisit': 21517, 'mid01': 20506, 'rest': 33272}
```
Instance reading: figGraph (hext: `x,y` carry no waved edge) `r=1`, `V=8=R`, `ξ≡1/2`, `auxVal = 64 > 0`, `ℓe` blocks equal (0,0); target 4: `lwBdist=6 > 2 = V r`; target 5 at `localReg2_inst_Q`, `p=2`; limit (consumer): at `V=4, c=1, D'=3` the threshold `log W0=576` and the inequality holds beyond it (output above).

**Verdicts.** Target 1 (vocabulary, `auxVal_nonneg`, label helper): PASS. Target 2 (identity, `mS ≤ n_S`, `auxOrd ≤ ord` for Normal): PASS. Target 3 (`lwGtoAG_holds`): PASS (hypotheses jointly satisfiable at the instance; exponents close with slack above; the falsification test, including `r=0` and `A=1`, found no counterexample; the main term is nearly attained, 15.94 vs `main_tight` 16.0, so the `W`-powers are sharp). Target 4 (`lwScalemole_holds`): PASS. Target 5 (`lwAuxNested_holds`): PASS. Overall: PASS.

## (b) Script output (stage 1b, role `prover-hard`; every time below is from `date -u`)

Stage 1b started at Mon Oct  5 03:54:25 UTC 2026 (first `date -u` of the stage); last build and axiom runs at 04:26:23 and 04:26:38-04:26:58 UTC; this section written at Mon Oct  5 04:29:18 UTC 2026.

```
$ git -C ../RBM3D-wt/T2170 log --oneline -3 ; git diff --stat main...t/T2170
8c94145 T2170: AuxGraph lint cleanup
d9036d2 T2170: LW-11a GtoAG deterministic part, scalemole tail, nested form of the auxiliary graph (Graph/AuxGraph)
47f9343 T2170: AuxGraph WIP (targets 1-5)
RBM3D/Graph/AuxGraph.lean | 1847 +++++++++++++++++++++++++++++++++++++++++++++
 RBM3D/Test/Axioms.lean    |    1 +
 2 files changed, 1848 insertions(+)
$ wc -l RBM3D/Graph/AuxGraph.lean   # 1847 (ticket estimate 1300-1600)
$ lake build RBM3D.Graph.AuxGraph ; echo exit=$?    # after `touch` of the file, so that it is rebuilt
exit=0
Build completed successfully (3386 jobs).        # lines of the build output that mention AuxGraph.lean: 0
$ lake build   # whole library; RBM3D.lean with `import RBM3D.Graph.AuxGraph` added TEMPORARILY (restored, not committed); runs #assert_rbm_axioms
exit=0
info: RBM3D.lean:215:0: axiom audit: 5135 theorems, 1773 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
registry: 1 borrowed + 85 owed + 50 structural; 53 registered premise(s) carry nothing yet: [RBM.Loop.KLPT,
Build completed successfully (3942 jobs).
```

`#print axioms` of the 8 targets/pinned theorems (`lwGtoAG_holds`, `lwScalemole_holds`, `lwAuxNested_holds`, `LGraph.auxOrd_le_scalingOrder`, `LGraph.scalingOrder_sub_auxOrd`, `LGraph.molSolid_length_le`, `LGraph.auxVal_nonneg`, `auxGraph_auxLab_ext`) and of the 8 instance helpers (`auxGraph_figGraph_molSolid`, `auxGraph_inst_Q_molSolid`, `auxGraph_figGraph_hext`, `auxGraph_instEll_dist`, `auxGraph_instXY_mol`, `auxGraph_instXY_normal`, `auxGraph_figGraph_auxVal`, `auxGraph_inst_Q_hxy`), one `#print axioms` each in a file importing the module:
```
$ (lake env lean ax.lean; lake env lean ax2.lean) | sed 's/.*depends on axioms: //' | sort | uniq -c
     16 [propext, Classical.choice, Quot.sound]
```

Pinned statements against the check file (`python3 diffpins.py`: the text of each `def`/`abbrev` in `docs/tickets/checks/T2170-check.lean` against `RBM3D/Graph/AuxGraph.lean`):
```
AuxIMol IDENTICAL 1
auxLab IDENTICAL 2
auxVal IDENTICAL 4
auxOrd IDENTICAL 1
LWGtoAG IDENTICAL 20
LWScalemole IDENTICAL 13
LWAuxNested IDENTICAL 6
ALL IDENTICAL
```

Target statements, extracted by script from the file (signatures; the `Prop`s `LWGtoAG`, `LWScalemole`, `LWAuxNested` are the three blocks printed after them):
```
-- AuxGraph.lean:117
theorem LGraph.scalingOrder_sub_auxOrd (Γ : LGraph E I) :
    Γ.scalingOrder - Γ.auxOrd =
      ((Γ.nS : ℤ) - (Γ.molSolid.length : ℤ)) + 2 * ((Γ.nW : ℤ) - (Γ.nV : ℤ) + (Γ.nM : ℤ))
-- AuxGraph.lean:124
theorem LGraph.molSolid_length_le (Γ : LGraph E I) : Γ.molSolid.length ≤ Γ.nS
-- AuxGraph.lean:130
theorem LGraph.auxOrd_le_scalingOrder (Γ : LGraph E I) (hN : Γ.Normal) : Γ.auxOrd ≤ Γ.scalingOrder
-- AuxGraph.lean:89
theorem LGraph.auxVal_nonneg {κ : Type} [Fintype κ] (Γ : LGraph E I) (ξ : κ → κ → ℝ)
    (hξ : ∀ u v, 0 ≤ ξ u v) (be : E → κ) : 0 ≤ Γ.auxVal ξ be
-- AuxGraph.lean:97
theorem auxGraph_auxLab_ext {κ : Type} (Γ : LGraph E I)
    (hext : ∀ a b : E, Γ.molOf (Sum.inl a) = Γ.molOf (Sum.inl b) → a = b)
    (be : E → κ) (b : LGraph.AuxIMol Γ → κ) (a : E) :
    LGraph.auxLab Γ be b (Γ.molOf (Sum.inl a)) = be a
-- AuxGraph.lean:1018
theorem lwGtoAG_holds (d : ℕ) : LWGtoAG d
-- AuxGraph.lean:1130
theorem lwScalemole_holds (d : ℕ) : LWScalemole d
-- AuxGraph.lean:1606
theorem lwAuxNested_holds : LWAuxNested
```
-- AuxGraph.lean:979
def LWGtoAG (d : ℕ) : Prop :=
  3 ≤ d → ∀ (L W : ℕ) [NeZero L] [NeZero W] {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]
    (Γ : LGraph E I), Γ.Normal → (∀ a b : E, Γ.molOf (Sum.inl a) = Γ.molOf (Sum.inl b) → a = b) →
    ∀ (D : LData (Idx d L W)) (m : ℂ) (Ψ C c r R : ℝ) (ξ : Zd d L → Zd d L → ℝ),
      (∀ x y, D.M x y = if x = y then m else 0) →
      (∀ x y, x ≠ y → ‖D.G x y‖ ≤ Ψ) → (∀ x, ‖D.G x x - m‖ ≤ Ψ) →
      0 ≤ C → 0 < c →
      (∀ x y, ‖D.S x y‖ ≤ C * ((W : ℝ) ^ d)⁻¹ * Real.exp (-(c * (lwBdist d L W x y : ℝ)))) →
      (∀ x y, ‖D.Sp x y‖ ≤ C * ((W : ℝ) ^ d)⁻¹ * Real.exp (-(c * (lwBdist d L W x y : ℝ)))) →
      (W : ℝ) ^ (-(d : ℝ) / 2) ≤ Ψ →
      0 ≤ r → (Fintype.card (E ⊕ I) : ℝ) * r ≤ R →
      (∀ a b, 0 ≤ ξ a b) →
      (∀ (x y : Idx d L W) (a b : Zd d L), x ≠ y →
        (zdistD d L ((split d L W x).1 - a) : ℝ) ≤ R → (zdistD d L ((split d L W y).1 - b) : ℝ) ≤ R →
        ‖D.G x y‖ ≤ ξ a b) →
      ∀ ℓe : E → Idx d L W,
        ‖Γ.val D ℓe‖ ≤
          Γ.sizeConst C (C * expC (d - 2) c) * Ψ ^ (Γ.scalingOrder - LGraph.auxOrd Γ) *
              (((W : ℝ) ^ d) ^ Γ.nM * LGraph.auxVal Γ ξ (fun a => (split d L W (ℓe a)).1)) +
            Real.exp (-(c * r / 2)) * Γ.sizeConst C (C * expC (d - 2) (c / 2)) * Γ.scalingSize Ψ W d L
-- AuxGraph.lean:1003
def LWScalemole (d : ℕ) : Prop :=
  3 ≤ d → ∀ (L W : ℕ) [NeZero L] [NeZero W] {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]
    (Γ : LGraph E I), Γ.Normal →
    ∀ (D : LData (Idx d L W)) (m : ℂ) (Ψ C c r : ℝ),
      (∀ x y, D.M x y = if x = y then m else 0) →
      (∀ x y, x ≠ y → ‖D.G x y‖ ≤ Ψ) → (∀ x, ‖D.G x x - m‖ ≤ Ψ) →
      0 ≤ C → 0 < c →
      (∀ x y, ‖D.S x y‖ ≤ C * ((W : ℝ) ^ d)⁻¹ * Real.exp (-(c * (lwBdist d L W x y : ℝ)))) →
      (∀ x y, ‖D.Sp x y‖ ≤ C * ((W : ℝ) ^ d)⁻¹ * Real.exp (-(c * (lwBdist d L W x y : ℝ)))) →
      0 ≤ r →
      ∀ (ℓe : E → Idx d L W) (a b : E), Γ.molOf (Sum.inl a) = Γ.molOf (Sum.inl b) →
        (Fintype.card (E ⊕ I) : ℝ) * r < (lwBdist d L W (ℓe a) (ℓe b) : ℝ) →
        ‖Γ.val D ℓe‖ ≤ Real.exp (-(c * r / 2)) * Γ.sizeConst C (C * expC (d - 2) (c / 2)) * Γ.scalingSize Ψ W d L
-- AuxGraph.lean:1597
def LWAuxNested : Prop :=
  ∀ (p : ℕ) (Q : PGraph (Fin 2)), 0 < p → Q.LocReg345 p →
    Q.g.molOf (Sum.inl (Q.ext 0)) ≠ Q.g.molOf (Sum.inl (Q.ext 1)) →
    ∃ Γa : NGraph p Q.g.nM, Γa.NoGhost ∧ Γa.IsNested ∧ Γa.ordN = LGraph.auxOrd Q.g ∧
      ∀ {κ : Type} [Fintype κ] (ξ : κ → κ → ℝ), (∀ u v, ξ u v = ξ v u) → ∀ be : Q.E' → κ,
        Γa.val ξ (fun _ => be (Q.ext 0)) (fun _ => be (Q.ext 1)) = LGraph.auxVal Q.g ξ be
```

Compiled nonempty instances (`example`s in the same file, after the proofs of the targets; the statement lines are extracted by script, every hypothesis of the target is discharged in the proof; the helpers `auxGraph_inst*`, `auxGraph_figGraph_*` are theorems checked above):
```
-- AuxGraph.lean:1710-1715 (statement of the example; the proof follows in the file)
example : figGraph.auxOrd = 2 ∧ figGraph.scalingOrder = 4 ∧ figGraph.auxOrd ≤ figGraph.scalingOrder ∧
    figGraph.scalingOrder - figGraph.auxOrd =
      ((figGraph.nS : ℤ) - (figGraph.molSolid.length : ℤ)) + 2 * ((figGraph.nW : ℤ) - (figGraph.nV : ℤ) + (figGraph.nM : ℤ)) ∧
    figGraph.molSolid.length ≤ figGraph.nS ∧
    localReg2_inst_Q.auxOrd = 2 ∧ localReg2_inst_Q.scalingOrder = 2 ∧
    localReg2_inst_Q.auxOrd ≤ localReg2_inst_Q.scalingOrder
-- AuxGraph.lean:1743-1750 (statement of the example; the proof follows in the file)
example : ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
    figGraph.auxVal (fun _ _ => (1 / 2 : ℝ)) (fun a => (split 3 4 2 (lwSizeEll a)).1) = 64 ∧
    ‖figGraph.val auxGraph_instD lwSizeEll‖ ≤
      figGraph.sizeConst C (C * expC (3 - 2) c) * (1 / 2 : ℝ) ^ (figGraph.scalingOrder - figGraph.auxOrd) *
          ((((2 : ℕ) : ℝ) ^ 3) ^ figGraph.nM *
            figGraph.auxVal (fun _ _ => (1 / 2 : ℝ)) (fun a => (split 3 4 2 (lwSizeEll a)).1)) +
        Real.exp (-(c * 1 / 2)) * figGraph.sizeConst C (C * expC (3 - 2) (c / 2)) *
          figGraph.scalingSize (1 / 2) 2 3 4
-- AuxGraph.lean:1785-1788 (statement of the example; the proof follows in the file)
example : ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ (Fintype.card (Fin 2 ⊕ Fin 0) : ℝ) * 1 < 6 ∧
    ‖auxGraph_instXY.val auxGraph_instD auxGraph_instEll‖ ≤
      Real.exp (-(c * 1 / 2)) * auxGraph_instXY.sizeConst C (C * expC (3 - 2) (c / 2)) *
        auxGraph_instXY.scalingSize (1 / 2) 2 3 4
-- AuxGraph.lean:1818-1819 (statement of the example; the proof follows in the file)
example : ∃ Γa : NGraph 2 localReg2_inst_Q.nM, Γa.NoGhost ∧ Γa.IsNested ∧ Γa.ordN = 2 ∧ localReg2_inst_Q.nM ≤ 2 ∧
    Γa.val (fun _ _ => (1 / 2 : ℝ)) (fun _ => (0 : Zd 3 4)) (fun _ => 0) = 4
-- AuxGraph.lean:1833-1837 (statement of the example; the proof follows in the file)
example : ∃ outs : List (PGraph (Fin 2)),
    ∀ Q ∈ outs, Q.g.Normal ∧ 2 ≤ Q.g.scalingOrder ∧ Q.g.nM ≤ 2 ∧
      (Q.g.molOf (Sum.inl (Q.ext 0)) ≠ Q.g.molOf (Sum.inl (Q.ext 1)) →
        (∀ a b : Q.E', Q.g.molOf (Sum.inl a) = Q.g.molOf (Sum.inl b) → a = b) ∧
        ∃ Γa : NGraph 2 Q.g.nM, Γa.NoGhost ∧ Γa.IsNested ∧ Γa.ordN = Q.g.auxOrd)
```

Name-clash grep and ports:
```
$ python3 clash.py   # every public declaration of the file, `grep -rnw` in RBM3D/ (worktree and main) and docs/tickets/checks/
93 public names declared in RBM3D/Graph/AuxGraph.lean; hits in other files of RBM3D/ (this worktree, main worktree) and in docs/tickets/checks/ other than T2170-check.lean: 0
$ grep -nE "LocReg6|L \^ d ≤ W|Ψ ≤ 1" RBM3D/Graph/AuxGraph.lean     # (empty: exit 1)
$ awk 'NR>=1018 && NR<=1128' RBM3D/Graph/AuxGraph.lean | grep -n hext   # proof of lwGtoAG_holds
2:  intro hd L W _ _ E I _ _ _ _ Γ hN hext D m Ψ C c r R ξ hM hG hGd hC hc hS hSp hwin hr hRr hξ0 hξ ℓe
$ grep -rlE "AuxGraph|auxVal|GtoAG|auxLab" ../RBM1D ../RBM2D --include=*.lean (read-only, outside .lake)   # (empty): no port
```

**Narrative.**
- Targets 1-5 are proved in `RBM3D/Graph/AuxGraph.lean`; the four definitions and the three `Prop`s are identical to the check file (script diff above). No pinned statement, merged statement or signature was changed and no hypothesis was added to a pinned statement.
- Target 3 follows the route (a)-(g) of the ticket. (a) `auxGraph_mol_dist`, `auxGraph_lab_close`; (b) `auxGraph_exists_forest`, the proof of the merged `LGraph.exists_forest` copied with the root map returned; (c) `auxGraph_term_conf`; (d) `auxGraph_forest_roots` applies the merged `lwForest_sum_le` with the roots moved to the external vertices (preflight note N1; `lwForest_core` is not copied), `auxGraph_sum_blocks` gives `(W^d)^{n_M}`; (e) `one_le_pow_mul_sq_iff`; (f) `auxGraph_term_tail`, `auxGraph_tail_sum` apply the merged `LGraph.waved_sum_le` to the weighted data `auxGraph_wdata D c`; (g) the sum in `lwGtoAG_holds`.
- Copied or adapted from private lemmas of `Graph/LWSizeClaim.lean` (prefix `auxGraph_`): `lwExists_rank`, `lwSEdge_norm_le`, `lwList_prod_le`, `lwNorm_list_prod`, `lwWVal_bound`, `lwProd_waved_eq`, `lwSize_alg`, `LGraph.adj_waved`. No port from RBM1D/RBM2D.
- No step used `L^d ≤ W^K`, `Ψ ≤ 1` or `LocReg6` (grep above); `3 ≤ d` enters only through `lwKBound_of_decay`.
- `hext` of `LWGtoAG` is not used by the proof (grep above): a confined labelling puts every vertex of a molecule within `R` of its chosen external vertex. The hypothesis stays because it is pinned.
- Target 4 shares `auxGraph_mol_dist`, `auxGraph_term_tail`, `auxGraph_tail_sum` with target 3; no labelling is confined, so the tail is the whole bound.
- Target 5: `auxGraph_Data` holds the numbering `Fin n_M ≃ AuxIMol`, the walks of (3) and the unused molecular edges (the multiset remainder of (3), `Multiset.le_iff_exists_add`, read as pairs by `Quot.out`); the slots `(i, k)` and `r` are numbered by `Fintype.equivFin`; `auxGraph_isNested` proves the six conjuncts of `IsNested` from `LocReg3`-`5`, `auxGraph_ordN` the order, `auxGraph_val_eq` the value (the multisets of unordered block pairs agree). Walks may revisit molecules and `IsNested` needs no simple path, so no stop was needed.
- Graph facts of the instances (`molSolid` lengths, `hext` at `figGraph`, normality, molecules, block distance `6`) are `decide`/`decide +kernel`; no `native_decide`.
- Instance (3) uses the coloured waved edge `S^+_{xy}` where the ticket text says `S_{xy}`: preflight (a) note N5 records that with the plain `S` the value is exactly 0 at block distance 6, which would make the instance void. That the value is nonzero (1.08e-7) is checked numerically in section (a) only, not in Lean.
- The `outs` of the consumer-chain example is existential, as in `localReg2_inst_expansion`; nothing here proves it nonempty.
- Registry: one line added to `structuralProps` in `RBM3D/Test/Axioms.lean` (`RBM.Graph.LGraph.IsExtMol`, a defining predicate), as the ticket's registry rule says; the scan lists it once a theorem takes `¬ IsExtMol c` as a hypothesis. `RBM3D.lean` is unchanged (the hub adds the root import).

## (c) Verified Mathlib names (44 `#check`s in a file importing the module; the only error is `Sym2.out`)

`Equiv.sumCompl` (`Rt ⊕ Cc ≃ I`); `Equiv.ofInjective` (`Rt ≃ range root`); `Equiv.sumArrowEquivProdArrow` (`(Rt ⊕ Cc → ι) ≃ (Rt → ι) × (Cc → ι)`); `Equiv.arrowCongr`;
`Equiv.arrowProdEquivProdArrow` (`(Rt → Zd × Fin) ≃ (Rt → Zd) × (Rt → Fin)`); `Equiv.sum_comp`; `Fintype.sum_equiv`; `Fintype.sum_prod_type`; `Fintype.prod_sum_type`; `Fintype.prod_sigma`;
`Fintype.equivFin` (slot numbering); `Fintype.equivFinOfCardEq` (`Fin n_M ≃ AuxIMol`); `List.mem_ofFn`; `List.getElem_ofFn`; `List.map_ofFn`; `List.prod_ofFn`; `List.ofFn_get`;
`List.forall₂_iff_get`; `List.nodup_finRange`; `List.prod_map_mul`; `List.prod_nonneg`; `List.length_filter_le`; `Multiset.le_iff_exists_add`; `Multiset.card_add`; `Multiset.mem_of_le`;
`Multiset.prod_add`; `Multiset.map_add`; `Multiset.coe_toList`; `Multiset.mem_toList`; `Sym2.lift`; `Sym2.mk_isDiag_iff`; `Quot.out_eq`; `SimpleGraph.Reachable.exists_isPath`;
`SimpleGraph.Walk.IsPath.length_lt`; `Real.rpow_le_rpow_of_exponent_le`; `Real.rpow_neg_one`; `Real.one_le_exp`; `pow_le_pow_left₀`; `inv_le_iff_one_le_mul₀`; `one_le_mul_of_one_le_of_one_le`; `Finset.sum_add_distrib`.
Verified absent: `Sym2.out` (use `Quot.out`). `List.one_le_prod_of_one_le` exists but fails on `ℝ` (`MulLeftMono ℝ` not synthesized), replaced by `auxGraph_one_le_prod`. `dif_pos`, `dif_neg`, `if_pos`, `if_neg` are deprecated (still used, `linter.deprecated` off in the file).

## (d) Open issues and paper-delta candidates

Nothing is blocked; all five targets and the five instances are delivered. Open: the radius of the consumers (preflight (a) row 6a, `r = (log W)^{3/2}/|E ⊕ I|` recommended) is left to LW-11b/LW-02; target 3 takes `r`, `R` free with `|E ⊕ I| r ≤ R`, target 4 has the premise `|E ⊕ I| r < lwBdist (ℓe a) (ℓe b)`.
- `T2170a`: `GtoAG` in deterministic form: entry bounds, decay of `S`, `S^±` and the `ξ`-domination on the `R`-balls are premises on the sample; the `W^{-D}` is the explicit tail `e^{-cr/2} C'_Γ size(Γ)`; no `(log W)` loss (peeling replaces the volume count, as D265).
- `T2170b`: `Γ^aux` is defined for every normal graph whose distinct external vertices lie in distinct molecules; `(eq:MolVW)` enters only summed (`n_V - n_M ≤ n_W`, `LGraph.counters_le`).
- `T2170c`: `ξ` is any non-negative block function dominating the off-diagonal entries on the `R`-balls; `(eq:xia1a2)`, `claim:xi` are LW-11b.
- `T2170d`: the nested form needs `𝓜_x ≠ 𝓜_y`, `p ≥ 1` and a symmetric `ξ`; it uses walks (D338); the molecular edges used by no walk are attached to `a_0`, `b_0`; the numbering of the internal molecules is arbitrary (`Fintype.equivFinOfCardEq`).
- `T2170e`: `(scalemole)` for two external vertices in one molecule, deterministic (the `𝓜_x = 𝓜_y` outputs under `(eq:far_ab)`).
- `T2170f`: `hext` of `GtoAG` is not needed for the bound (the pin keeps it); the choice of the external vertex of a molecule in `auxLab` is immaterial.
- `T2170g`: the target-4 instance uses `S^+_{xy}` (coloured waved edge), not `S_{xy}` as in the ticket text (see Narrative).
