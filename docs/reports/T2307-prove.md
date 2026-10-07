Prover model: claude-sonnet-5-5

## (a) Math preflight — Tue Oct  6 15:01:58 UTC 2026

Notation: `m = mE E`, `w(a,b) = m^a (star m)^b`; `R2..R8 = oe2xR2, owxT1, oe2xR4..R8` (R1 = `oe2xR1`); `kids` = the seven families partitioned by `partitionX`, exponent shifted by `j`; Inv `= P.g.Normal`; `Φ P = ∫ P.val (LWG5Data ..) ![x,y]`. Scripts (python only, no Lean; `SP=/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/85663390-cb91-4af2-a115-d95547c1e2fb/scratchpad/T2307`): `eng.py` (LGraph, `LGraph.partition` `LWVocab:1000-1303`, families `LWGGExp:485-539`, `LWWeightExp:658`; copy of the T2265 engine), `pre1.py` (literal `lwSplitLoops`/`lwSplitLoopsX`, R1 claim), `mc_step.py` (Monte Carlo), `inst.py`, `node.py`.

### (i) Exponent table
| row | value | constraint | slack |
|---|---|---|---|
| `m`-power shift `j` of the families | R2,R4,R6,R8: `m^3` (`LWGGExp:487,493,510,531`); R3 (`LWWeightExp:659`), R5,R7 (`LWGGExp:502,520`): `m`; R1,R1d: `m` (`:544,567`). `owxExt` sets `coeff := c * Γ.coeff` (`LWWeightExp:463`), so `Rk m` = `Rk 1` with `coeff` times `m^j`, and `val(Rk m) = m^j val(Rk 1)` | `kids` shift `(r.1.1 + j, r.1.2)`, `j=3` for R2,R4,R6,R8, `j=1` for R3,R5,R7 (as pinned) | equality (no inequality) |
| weight `w` | `w(0,0)=1`, `w(a+c,b+e)=w(a,b)w(c,e)` (`pow_add`) | needed by `ExpandGSum` | equality |
| partition exponents | `lwSplitLoopsX` has the same recursion and the same edge lists as `lwSplitLoops m` (`LWVocab:1209`); `m` (σ true) or `star m` (σ false) becomes `(+1,0)` / `(0,+1)`. Order: `partition m = partitionTerms.flatMap (mergeSplitP m)`, `mergeSplitP` = `(lwSplitLoops m Δ.merge.solid).map ..` with `coeff := r.1 * Δ.merge.coeff` (`LWVocab:1290-1303`) | `PartitionXSpec`, `val_eq_partitionX` | equality; script (ii) below |
| `Normal` and `coeff` | `Normal` = dotted all `×`, `XBetween ↔ SBetween` for `u≠v`, solid loops circled (`LWVocab:990-993`): reads `dotted`, `solid` only, not `coeff` | `partitionX_normal` from `partition_normal` at `m = 1` | no hypothesis lost |
| `|E| < 2` | instance `E = lemE(z0 0) = 0.49999999999488` | gives `0 < Im zt` (`lwWx_im_pos`, `LWWeightExp:86`), `m ≠ 0`, flow | slack `1.5` |
| `0 < t < 1` | instance `t = 1/16` | `hu : 0 < t` of `oe2x_graph_E` (`LWGGExp:1550`), `t<1` for `Im zt = (1-t) Im m > 0` | slack `1/16`, `15/16` |
| `hSp` | `‖m‖^2 t < 1`, `‖m‖ = 1` (`norm_mE`) | `lwSplus_spec` (`LWStein:1346`) | `0.9375` at `t=1/16` |
| flow `hzm` | `zt + t m = -m⁻¹` (`lwWx_flow`, `LWWeightExp:98`) | `oe2x_graph_E` | residual `1.2e-41` numerically; exact by the lemma |
| fuel, thresholds `tg ∈ {4,5}` | any `fuel : ℕ`, any `sel`; `tg` only decides leaves in `expand`/`lwStep` | the identity holds for every leaf choice | no constraint (instance fuel 4) |
| `R1` | `oe2xR1_val_zero` hypotheses used: `Γ.Normal`; `p ∈ lwSplit Γ.solid` (only `p.1 ∈ Γ.solid`); `hp1 : p.1 = ⟨true,false,Sum.inr x,y⟩`; `hy : y ≠ Sum.inr x`. **Not needed:** `y` external, any `m`, `D`, `ℓe` | `p.1` is a non-loop solid edge `x–y` (`src ≠ dst`), so `SBetween`, so by `Normal` (iii) `XBetween`: a `×`-edge on `{x,y}` is in `Γ.dotted`; `oe2xR1d` adds `⟨true,x,y⟩` (`LWGGExp:539-544`): the product of the two `DEdge.val` is `0` at every labelling; `oe2xR1_val` (`:592`) turns `R1.val` into `R1d.val` | holds on all 129 depth-0 and 31,299 / 39,488 depth-1 candidates (script) |

### (ii) One concrete nondegenerate instance
`d=3`, `sz0` (`L=4, W=32, N=2097152`, `RBM3D/Defs/Sizes.lean:260-267`), `n=0`, `E=STflowE z0 0`, `t=1/16`, fuel 4, `sel = selClassical`, every `k, s, x, y`. Node: root term 162 of `LWG5Graph False False` (Normal, `ord 3 < tg 5`, ext distinct), candidate at `a`. The only hypotheses of the identity are `|E|<2`, `0<t<1`; no external hypothesis occurs (the inputs are merged theorems), so no limit computation is owed.
```
$ cd $SP; python3 inst.py; python3 node.py
L=4 W=32 N=2097152  z0 0 = (0.5 + 8.76387294767e-6j)
E = lemE(z0 0) = 0.49999999999488
|E| < 2 : True (slack 1.5)
0 < t < 1 : t = 1/16, slack to 1: 15/16
Im zt = (1-t) Im m = 0.9077304718  (> 0: True)
hzm residual |zt + t m + 1/m| = 1.1833e-41
|m| = 1.0 ; ||m||^2 t = 0.0625 < 1 (hSp), slack 0.9375
|m^j conj(m)^j'| = |m|^(j+j') = 1.0 at (j,j')=(12,3)
m^-1 = conj m ? |1/m - conj(m)| = 1.1833e-41
node ext=['x', 'y'] ints=['a', 'b', 'c'] ord=3 tg=5 Normal=True
candidate: x=a p=G(a>c) q=G(x>a) y!=x: True y'!=x: True ; ncand at depth 0 term: 3
R1 value 0: x-edge on {x,y}: True
kids (R2..R8 partitioned): 1125, by family {'R2': 11, 'R3': 1, 'R4': 32, 'R5': 32, 'R6': 32, 'R7': 137, 'R8': 880}, all Normal: True
min nonneg exponent pairs (j,j') over kids: [((1, 0), 65), ((1, 1), 7), ((2, 0), 66), ((2, 1), 3)]
```
Partition and R1 claims (root partition of `LWG5Graph k s`, every candidate at depth 0, every child's candidates at depth 1; `lwSplitLoopsX` and `lwSplitLoops` are literal copies evaluated with `m`, `star m` as independent random complex numbers; edges compared as lists, coefficient against `m^j (star m)^j'`; exponent multisets against the engine's partition):
```
$ cd $SP; python3 pre1.py 1
k=False s=False {'root_terms': 163, 'root_split_terms': 163, 'cand0': 129, 'R1zero0': 129, 'fam_R2': 129, 'fam_R3': 129, 'cand1': 31299, 'fam_R4': 129, 'fam_R5': 129, 'fam_R6': 129, 'fam_R7': 248, 'fam_R8': 248} time 2s
k=False s=True {'root_terms': 163, 'root_split_terms': 163, 'cand0': 129, 'R1zero0': 129, 'fam_R2': 129, 'fam_R3': 129, 'cand1': 39488, 'fam_R4': 129, 'fam_R5': 129, 'fam_R6': 129, 'fam_R7': 248, 'fam_R8': 248} time 2s
k=True s=False {... same counts as (False, False) ...}
k=True s=True {... same counts as (False, True) ...}
split-loops stats {'lists': 51588, 'terms': 194220}
```
(All asserts passed: every merged solid list gives equal edge lists and coefficients; the `(sign,j,j')` multisets of `partitionX` and of the engine partition agree for the root and for the families at `m = 1`; every depth-0 and depth-1 node is Normal; R1 has a `×`-edge and the added `=`-edge on `{x,y}` at all 129 + 31,299 / 39,488 candidates.)

Monte Carlo of `RCand.kids_identity` (expectation, not pathwise): `lhs = coef(P) val(P)(x,y)`, `rhs` = sum of the `kids` (R1 dropped) with their coefficients; paired difference, `d=3`, `L=2` (`N=8`), `E=0.6`, `s_ij` uniform on `{j: differ in ≤ 1 coordinate}`, `S = t s`, `S⁺ = S(1-m²S)⁻¹`, `M = mI`, `G = (√t X - z)⁻¹`, `X` complex Hermitian Gaussian. Cases: A = node 162 (ext distinct), labels `(0,5)`, vertex `a`; B = node 160 (ext merged), labels `(7,7)`, vertex `a`; C, D = the same nodes' children (family R4, 1459 / 1041 kids) with the candidate at the created vertex `n2`. Four `(k,s)` and `t ∈ {0.3, 0.9}` at 2000 samples (aggregate of the 32 runs, `python3 mc_step.py k s t case 2000`, files `out2/mc_*.out`):
```
case t  rows  max |diff|/SE   SE/|lhs| range
A 0.3 4 0.94  0.037-0.131     A 0.9 4 1.75  0.785-6.682
B 0.3 4 1.59  0.060-0.074     B 0.9 4 1.43  0.842-5.375
C 0.3 4 1.53  0.095-0.109     C 0.9 4 1.06  2.177-17.126
D 0.3 4 1.24  0.082-0.243     D 0.9 4 1.50  2.326-8.773
$ python3 mc_step.py 0 0 0.3 {A,B,C,D} 20000      # `out2/big_00_0.3_*.out`; omit-one-family control = |diff|/SE after dropping that family
A: |diff|/SE = 0.58, SE/|lhs| = 0.012 | omit R2 16.3, R3 2.0, R7 59.7, R8 7.9 (R4,R5,R6 0.6)
B: |diff|/SE = 0.51, SE/|lhs| = 0.021 | omit R2 18.4, R3 1.3, R5 2.8, R7 28.3, R8 9.5
C: |diff|/SE = 1.54, SE/|lhs| = 0.032 | omit R2 1.2, R3 2.5, R7 25.6, R8 7.7
D: |diff|/SE = 1.73, SE/|lhs| = 0.027 | omit R2 16.9, R3 2.0, R7 21.7, R8 15.3
```
All 36 rows are within 3 SE (max 1.75). Power is real only at `t=0.3` (SE/|lhs| ≤ 3%, 20000 samples); at `t=0.9` SE/|lhs| is 0.8-17, so those rows are consistency, not evidence. The omit-one-family controls detect R2, R7, R8 at `t=0.3`; R3 (`m`-weighted, one graph), R4-R6 are not separated from noise by this run. The per-step algebra for them rests on the merged `oe2x_graph_E` (`LWGGExp:1550`), not on this check.

§29 (one line each): (1) `0<t<1`, `|E|<2` only in `RCand.kids_identity` and `LWG5Identity` (`hz`, `hu`, `hSp`); `t=0` not here. (2) no index-set boundary. (3) no `L^d ≤ W^K`. (4) every `n`. (5) one list for all `sz,n,E,t,x,y`; `expandRoot` and `sel` see only the graph. (6) no `ĝ`. (7) no scale.

### Mathematical argument for the targets (what (i)-(ii) rest on)
- Step: at `ℓe = ![x,y]` either no `ℓ'` with `ℓe = ℓ' ∘ P.ext` exists (then `P.val = 0`, and every `pcomp P Q` has `ext = Q.ext ∘ P.ext`, so it has no factoring either: all kids `0`), or `P.val = P.g.val ℓ'` and `(pcomp P Q).val = Q.val ℓ'` (`lvl1Comp_val`, `LWLvl1:3105`). Then `oe2x_graph_E` at `ℓe := ℓ'` gives `∫ P.g.val = Σ_{R1..R8} ∫ Rk(m).val`; R1 is `0` (row above); `Rk(m).val = m^j Rk(1).val`; `Rk(1).val = Σ_{partitionX} w r.1 · r.2.val` at `M = mI` (`val_eq_partitionX`, `hM` from `lwExpTerm3_Data_M`), pulled out of the integral by integrability of every graph value (as in `oe2x_graph_E`'s `hint`, `Tame.integrable hG`). R7, R8 are summed over `lwSplit c.q.2` as in `oe2x_graph_E` (`kids` has them in the same `flatMap`).
- Induction: `ExpandGSum` holds because `w` is multiplicative; leaves (`fuel 0`, `st = none`) give `w(0,0) Φ P = Φ P`. `expand sel n P = expandG (lwStep sel) n P`: the two definitions have the same three cases (`fuel 0`; `tg`-leaf or `sel P = none`; `some c`), `lwStep sel P = none` exactly in the first two.
- Root: `LWG5Graph k s : LGraph (Fin 2) (Fin 3)` and `LGraph.val D ![x,y]` is the left side of `LWG5Identity` as it stands; `val_eq_partitionX` at the root gives the `partitionX` sum, each member Normal (`partitionX_normal`) so `expandG_sum` applies; `w r.1 * w t.1 = w (r.1 + t.1)`.

### Verdicts
- Target 1 (vocabulary `LWJoined`, `LWG5Cand`, `LWG5Progress`, `LWG5Identity`): PASS (definitions; `LWJoined`, `LWG5Cand` instances occur in script (ii)).
- Target 2 (procedure, `partitionX`, `pcomp`, `RCand`, `kids`, `expand`, `expandRoot`, `selClassical`): PASS (script (ii): `PartitionXSpec` content checked termwise on 194,220 terms).
- Target 3 (`expandG`, `ExpandGSum`, `expandG_sum`, `lwStep`, `expand_eq_expandG`): PASS (induction as above).
- Target 4 (`lwSplitLoopsX_spec`, `partitionX_spec`, `val_eq_partitionX`, `partitionX_normal`, `oe2xR1_val_zero`, `RCand.kids_normal`, `RCand.kids_identity`): PASS. Exact hypothesis set for `oe2xR1_val_zero`: `Γ.Normal`, `hp : p ∈ lwSplit Γ.solid`, `hp1`, `hy` (nothing else; no re-pin needed). `partitionX_normal`: needs only `coeff`-blindness of `Normal` (checked above) and equality of the edge lists of `lwSplitLoopsX`/`lwSplitLoops`.
- Target 5 (`lwExpandIdentity_holds`): PASS (true for every `sel` and fuel; root `![x,y]` against `LGraph.val` needs no change).
- Target 6 (instance): PASS (numbers above; no hypothesis except `|E|<2`, `0<t<1`, both numerically satisfied).
- Pin differences: none found (no re-pin requested). The root `(0,0)`-exponent coefficient pairs and `star m` pairing are as pinned; paper-delta candidates beyond T2265a-c and T2288a-e: none.

## (b) Script output — Tue Oct  6 15:19:16 UTC 2026 (worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2307`, branch `t/T2307`)

No section (a′): section (a) was not found wrong; its hypothesis sets for `oe2xR1_val_zero`, `partitionX_normal` and its exponent shifts are the ones the Lean proofs use.

```
$ git log --oneline -1 && git diff --stat main...t/T2307 && wc -l RBM3D/Graph/LWExpTerm5.lean && git status --short RBM3D/Test/Axioms.lean RBM3D.lean
90f1a30 T2307: LW-14e-2 expansion procedure on PGraph (Fin 2) and its identity in expectation
 RBM3D/Graph/LWExpTerm5.lean | 739 ++++++++++++++++++++++++++++++++++++++++++++
 1 file changed, 739 insertions(+)
     739 RBM3D/Graph/LWExpTerm5.lean
$ lake build RBM3D.Graph.LWExpTerm5 2>&1 | tail -2
Note: This linter can be disabled with `set_option linter.style.show false`
Build completed successfully (3882 jobs).
$ grep -nE "sorry|admit|native_decide|^axiom" RBM3D/Graph/LWExpTerm5.lean | wc -l
       0
$ lake build   # whole library at the worktree (the root file does not import the new module yet; the hub adds it at merge)
Build completed successfully (4111 jobs).
lake build  1.48s user 3.60s system 252% cpu 2.011 total
```

### Axioms (`lake env lean` on a scratch file importing the module; `#print axioms` of every target and instance)
```
$ lake env lean scratchpad/T2307/axs.lean
'RBM.Gauss.Sizes.lwExpandIdentity_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.expandG_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.expand_eq_expandG' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.RCand.kids_identity' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.RCand.kids_normal' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.val_eq_partitionX' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.partitionX_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.partitionX_normal' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.lwSplitLoopsX_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.oe2xR1_val_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.lwG5Cand_iff_nonempty' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.LWInst.lwExpTerm5_inst_identity' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.LWInst.lwExpTerm5_inst_kids_identity' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.LWInst.lwExpTerm5_inst_kids_normal' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.LWInst.lwExpTerm5_inst_R1_val_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.LWInst.lwExpTerm5_inst_val_eq_partitionX' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### Statements of the targets, extracted from the file (`python3 extract.py RBM3D/Graph/LWExpTerm5.lean stmt <names>`: header up to `:=`, whitespace collapsed; line = file line)
```
234: theorem expandG_sum {X : Type*} (st : X → Option (List ((ℕ × ℕ) × X))) (Inv : X → Prop) (Φ : X → ℂ) (w : ℕ × ℕ → ℂ) : ExpandGSum st Inv Φ w
259: noncomputable def lwStep (sel : Sel) (P : PGraph (Fin 2)) : Option (List ((ℕ × ℕ) × PGraph (Fin 2)))
264: theorem expand_eq_expandG (sel : Sel) (n : ℕ) (P : PGraph (Fin 2)) : expand sel n P = expandG (lwStep sel) n P
281: theorem lwSplitLoopsX_spec {V : Type*} [DecidableEq V] (m : ℂ) (es : List (SEdge V)) : lwSplitLoops m es = (lwSplitLoopsX es).map fun r => (m ^ r.1.1 * star m ^ r.1.2, r.2)
310: theorem partitionX_spec : PartitionXSpec (E := E) (I := I)
337: theorem val_eq_partitionX {ι : Type*} [Fintype ι] [DecidableEq ι] (m : ℂ) (Γ : LGraph E I) (D : LData ι) (hM : ∀ x, D.M x x = m) (ℓe : E → ι) : Γ.val D ℓe = ((partitionX Γ).map fun r => m ^ r.1.1 * star m ^ r.1.2 * r.2.val D ℓe).sum
347: theorem partitionX_normal (Γ : LGraph E I) : ∀ r ∈ partitionX Γ, r.2.g.Normal
364: theorem oe2xR1_val_zero (m : ℂ) (Γ : LGraph E I) (hN : Γ.Normal) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid) (x : I) (y : E ⊕ I) (hy : y ≠ Sum.inr x) (hp1 : p.1 = ⟨true, false, Sum.inr x, y⟩) (D : LData ι) (ℓe : E → ι) : (oe2xR1 m Γ p x y hy).val D ℓe = 0
408: theorem RCand.kids_normal {P : PGraph (Fin 2)} (c : RCand P) : ∀ r ∈ c.kids, r.2.g.Normal
531: theorem RCand.kids_identity {d : ℕ} (sz : Sizes d) (n : ℕ) (E t : ℝ) (hE : |E| < 2) (ht0 : 0 < t) (ht1 : t < 1) {P : PGraph (Fin 2)} (hN : P.g.Normal) (c : RCand P) (x y : Idx d (sz.L n) (sz.W n)) : ∫ ω, P.val (LWG5Data sz n E t ω) ![x, y] ∂(sz.seqP) = (c.kids.map fun r => (mE E) ^ r.1.1 * star (mE E) ^ r.1.2 * ∫ ω, r.2.val (LWG5Data sz n E t ω) ![x, y] ∂(sz.seqP)).sum
594: theorem lwExpandIdentity_holds : ∀ (sel : Sel) (fuel : ℕ), LWExpandIdentity sel fuel
$ sed -n 261p RBM3D/Graph/LWExpTerm5.lean   # body of lwStep (header: line 259 above)
  if (if P.ext 0 = P.ext 1 then (4 : ℤ) else 5) ≤ P.g.scalingOrder then none else (sel P).map RCand.kids
```

### Pins (check file section 2 against the file; scripts in `scratchpad/T2307`)
```
$ python3 pindiff.py probe.lean RBM3D/Graph/LWExpTerm5.lean   # probe = git show t/T2288:RBM3D/Probe/T2288Cert.lean (5f3d37f); block "section Procedure" .. selClassical (partitionX, PartitionXSpec, pcomp, RCand, lwG5Cand_iff_nonempty, RCand.kids, Sel, expand, expandRoot, LWExpandIdentity, selClassical), whitespace-normalised
probe lines 80 mine lines 80
diff lines: 0
$ python3 pindiff2.py probe.lean RBM3D/Graph/LWExpTerm5.lean   # LWJoined, LWG5Cand, LWG5Progress (probe 55-71) and LWG5Identity (probe 80-86)
/-- Copy of T2265's `LWJoinedPin` probe 15 mine 15 diff lines 0
/-- **Identity half** of T2265's probe 8 mine 8 diff lines 0
total diff lines 0
$ lake env lean pincheck.lean   # check-file section 2 copied into RBM.Gauss.Sizes.T2307Check, importing RBM3D.Graph.LWExpTerm5
117:theorem chk_joined (P : PGraph (Fin 2)) : LWJoinedPin P ↔ LWJoined P := Iff.rfl
118:theorem chk_cand (P : PGraph (Fin 2)) : LWG5CandPin P ↔ LWG5Cand P := Iff.rfl
119:theorem chk_progress (P : PGraph (Fin 2)) : LWG5ProgressPin P ↔ LWG5Progress P := Iff.rfl
120:theorem chk_identity (d : ℕ) (Ls : Bool → Bool → List ((ℕ × ℕ) × PGraph (Fin 2))) :
122:theorem chk_splitX {V : Type*} [DecidableEq V] (es : List (SEdge V)) :
127:theorem chk_expandG {X : Type*} (st : X → Option (List ((ℕ × ℕ) × X))) (n : ℕ) (P : X) :
133:theorem chk_sum {X : Type*} (st : X → Option (List ((ℕ × ℕ) × X))) (Inv : X → Prop) (Φ : X → ℂ)
137:theorem chk_main : ∀ (sel : Sel) (fuel : ℕ), LWExpandIdentity sel fuel := @lwExpandIdentity_holds
'RBM.Gauss.Sizes.T2307Check.chk_joined' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.T2307Check.chk_cand' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.T2307Check.chk_progress' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.T2307Check.chk_identity' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.T2307Check.chk_splitX' depends on axioms: [propext]
'RBM.Gauss.Sizes.T2307Check.chk_expandG' depends on axioms: [propext, Quot.sound]
'RBM.Gauss.Sizes.T2307Check.chk_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.T2307Check.chk_main' depends on axioms: [propext, Classical.choice, Quot.sound]
```
`chk_joined/cand/progress/identity` are `Iff.rfl`; `chk_sum` (ExpandGSumPin ↔ ExpandGSum) is `simp only` after rewriting with `chk_expandG`; `chk_main` is `@lwExpandIdentity_holds`.
Observed in the tool log: `rfl` for `lwSplitLoopsXPin es = lwSplitLoopsX es` and `expandGPin st n P = expandG st n P` was rejected ("Type mismatch ... rfl"), so those two are proved by induction (ticket allows this). `SelPin = Sel` is not a definitional equality ("Not a definitional equality" in the tool log): `RCandPin` and `RCand` are two different structure types, so `RCand`/`Sel` are pinned by the text diff above only.

### Compiled nonempty instances (in the file, namespace `RBM.Gauss.LWInst`; `d = 3`, `sz0`, `n = 0`, `E = STflowE z0 0`, `t = 1/16`; hypotheses of the examples: none)
```
$ python3 extract.py RBM3D/Graph/LWExpTerm5.lean stmt lwExpTerm5_inst_identity lwExpTerm5_inst_kids_identity lwExpTerm5_inst_kids_normal lwExpTerm5_inst_R1_val_zero lwExpTerm5_inst_val_eq_partitionX <examples>
637: theorem lwExpTerm5_inst_identity (k s : Bool) (x y : Idx 3 (sz0.L 0) (sz0.W 0)) : ∫ ω, (LWG5Graph k s).val (LWG5Data sz0 0 (STflowE z0 0) (1 / 16) ω) ![x, y] ∂(sz0.seqP) = ((expandRoot selClassical 4 k s).map fun q => (mE (STflowE z0 0)) ^ q.1.1 * star (mE (STflowE z0 0)) ^ q.1.2 * ∫ ω, q.2.val (LWG5Data sz0 0 (STflowE z0 0
676: theorem lwExpTerm5_inst_kids_identity (x y : Idx 3 (sz0.L 0) (sz0.W 0)) : ∫ ω, lwExpTerm5_instP.val (LWG5Data sz0 0 (STflowE z0 0) (1 / 16) ω) ![x, y] ∂(sz0.seqP) = (lwExpTerm5_instCand.kids.map fun r => (mE (STflowE z0 0)) ^ r.1.1 * star (mE (STflowE z0 0)) ^ r.1.2 * ∫ ω, r.2.val (LWG5Data sz0 0 (STflowE z0 0) (1 / 16) ω) 
684: theorem lwExpTerm5_inst_kids_normal : ∀ r ∈ lwExpTerm5_instCand.kids, r.2.g.Normal
688: theorem lwExpTerm5_inst_R1_val_zero {ι : Type*} [Fintype ι] [DecidableEq ι] (m : ℂ) (D : LData ι) (ℓe : Fin 2 → ι) : (oe2xR1 m lwExpTerm3_instGraph lwExpTerm5_instCand.p 0 (Sum.inl 1) (by simp)).val D ℓe = 0
695: theorem lwExpTerm5_inst_val_eq_partitionX (k s : Bool) (ω : sz0.SeqΩ) (x y : Idx 3 (sz0.L 0) (sz0.W 0)) : (LWG5Graph k s).val (LWG5Data sz0 0 (STflowE z0 0) (1 / 16) ω) ![x, y] = ((partitionX (LWG5Graph k s)).map fun r => (mE (STflowE z0 0)) ^ r.1.1 * star (mE (STflowE z0 0)) ^ r.1.2 * r.2.val (LWG5Data sz0 0 (STflowE z0 0)
703: example : PartitionXSpec (E := Fin 2) (I := Fin 3)
704: example (k s : Bool) : ∀ r ∈ partitionX (LWG5Graph k s), r.2.g.Normal
705: example (m : ℂ) : lwSplitLoops m [SEdge.mk true false (0 : Fin 2) 0, SEdge.mk false false 1 1, SEdge.mk true true 0 1] = (lwSplitLoopsX [SEdge.mk true false (0 : Fin 2) 0, SEdge.mk false false 1 1, SEdge.mk true true 0 1]).map fun r => (m ^ r.1.1 * star m ^ r.1.2, r.2)
710: example : (lwSplitLoopsX [SEdge.mk true false (0 : Fin 2) 0, SEdge.mk false false 1 1, SEdge.mk true true 0 1]).length = 4
714: example : expand selClassical 4 (LWG5Graph false false).pack = expandG (lwStep selClassical) 4 (LWG5Graph false false).pack
719: example : (1 : ℂ) = (((expandG (fun n : ℕ => if n < 2 then some [((1, 0), n + 1), ((0, 1), n + 1)] else none) 2 0).map fun t => (1 / 2 : ℂ) ^ (t.1.1 + t.1.2) * 1).sum) ∧ ∀ t ∈ expandG (fun n : ℕ => if n < 2 then some [((1, 0), n + 1), ((0, 1), n + 1)] else none) 2 0, True
$ sed -n 637,644p RBM3D/Graph/LWExpTerm5.lean   # lwExpTerm5_inst_identity with its proof term
theorem lwExpTerm5_inst_identity (k s : Bool) (x y : Idx 3 (sz0.L 0) (sz0.W 0)) :
    ∫ ω, (LWG5Graph k s).val (LWG5Data sz0 0 (STflowE z0 0) (1 / 16) ω) ![x, y] ∂(sz0.seqP) =
      ((expandRoot selClassical 4 k s).map fun q =>
        (mE (STflowE z0 0)) ^ q.1.1 * star (mE (STflowE z0 0)) ^ q.1.2 *
          ∫ ω, q.2.val (LWG5Data sz0 0 (STflowE z0 0) (1 / 16) ω) ![x, y] ∂(sz0.seqP)).sum :=
  lwExpandIdentity_holds selClassical 4 3 sz0 0 (STflowE z0 0) (1 / 16) (abs_lemE_lt_two (z0_im_pos 0))
    (by norm_num) (by norm_num) k s x y

```
The instance of `RCand.kids_identity` is at the packed graph `lwExpTerm3_instGraph` (5 solid edges, 2 waved, 3 `×`-dotted, `Normal` by `lwExpTerm3_instGraph_normal`) with the candidate `x = α`, `p = G_{αy}`, `q = G_{xα}` (`lwExpTerm5_instCand`); `q.2` has 3 edges, so the `R7`/`R8` sums run over a nonempty `lwSplit`. `lwExpTerm5_inst_identity` is `lwExpandIdentity_holds selClassical 4 3 sz0 0 ...` with `abs_lemE_lt_two (z0_im_pos 0)` and two `norm_num` goals `0 < 1/16`, `1/16 < 1`. The example for `expandG_sum` is a two-level branching step on `ℕ` (fuel 2, start 0).

### Registry pre-check (`Test/Axioms.lean`): scratch file `import RBM3D`, `import RBM3D.Graph.LWExpTerm5`, `#assert_rbm_axioms`
```
$ lake env lean scratchpad/T2307/reg.lean > reg_final.out 2>&1; echo $?    # started 15:20:06 UTC (date -u), final file
0
$ head -3 reg_final.out; tail -1 reg_final.out | cut -c1-140
axiom audit: 8675 theorems, 2854 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
All within [propext,
 Classical.choice,
non-vacuity certificates: 0 of 146 premises in the two ledgers; the rest are not known to be satisfiable (`RBM3D/Test/InterfaceShape.lean` s
$ diff reg_before.out reg_final.out | wc -l    # reg_before.out: same command, run between 15:14:24 and 15:16:17 UTC (before the last edit of the file); exit 0 as well
       0
$ git status --short RBM3D/Test/Axioms.lean RBM3D.lean | wc -l
       0
```
Registered: nothing. `scanPremises` (`Test/Axioms.lean:454-475`) lists a `Prop`-valued definition only if some theorem takes it as a binder and no theorem proves it; no theorem of the new file takes `LWJoined`, `LWG5Cand` or `LWG5Progress` as a hypothesis, and `LWG5Identity`, `PartitionXSpec`, `LWExpandIdentity`, `ExpandGSum` are proved (`lwExpandIdentity_holds`, `partitionX_spec`, `expandG_sum`), so the pre-check lists none and `RBM3D/Test/Axioms.lean` and `RBM3D.lean` are unchanged.

### Name-clash grep of the new public names (declarations outside the new file)
```
$ grep -rnE "^\s*(private |protected |noncomputable )*(def|theorem|lemma|structure|abbrev|inductive|class|opaque|axiom)\s+(<new names>)(\s|$)" RBM3D --include="*.lean" | grep -v "RBM3D/Graph/LWExpTerm5.lean" | wc -l
       0
$ grep -rnwE "LWG5Cand|LWG5Progress|LWJoined|partitionX|pcomp|expandG|lwStep|selClassical|expandRoot|RCand" RBM3D --include="*.lean" | grep -v "RBM3D/Graph/LWExpTerm5.lean" | wc -l
       0
```

### Ports
No port from `../RBM1D` or `../RBM2D` (ticket: "No port"); no file of those projects was read or written, so there is no diff-stat. Copied text: the pinned definitions and the proof of `lwSplitLoopsX_spec` are copies of `git show t/T2288:RBM3D/Probe/T2288Cert.lean` (branch t/T2288, commit 5f3d37f); the diff scripts above compare them.

### Public declarations of the file (line: kind name; `extract.py list`)
```
58: def LWJoined;65: def LWG5Cand;72: def LWG5Progress;76: def LWG5Identity;91: def lwSplitLoopsX;106: def partitionX;113: def PartitionXSpec;120: def pcomp;124: structure 
RCand;137: theorem lwG5Cand_iff_nonempty;147: def RCand.kids;159: abbrev Sel;162: def expand;171: def expandRoot;177: def LWExpandIdentity;181: def selClassical;189: def 
expandG;199: def ExpandGSum;234: theorem expandG_sum;259: def lwStep;264: theorem expand_eq_expandG;281: theorem lwSplitLoopsX_spec;310: theorem partitionX_spec;337: theorem 
val_eq_partitionX;347: theorem partitionX_normal;364: theorem oe2xR1_val_zero;408: theorem RCand.kids_normal;531: theorem RCand.kids_identity;594: theorem 
lwExpandIdentity_holds;637: theorem lwExpTerm5_inst_identity;676: theorem lwExpTerm5_inst_kids_identity;684: theorem lwExpTerm5_inst_kids_normal;688: theorem 
lwExpTerm5_inst_R1_val_zero;695: theorem lwExpTerm5_inst_val_eq_partitionX;examples: [703, 704, 705, 710, 714, 719];private helpers: 16
```

### Narrative (facts about the file; all lines refer to `RBM3D/Graph/LWExpTerm5.lean` at commit 90f1a30)
- One new file, 739 lines (cap 1500 not approached); nothing else changed (`git diff --stat` above). The procedure texts are verbatim probe copies (empty diffs above); from line 189 on are the abstract step, the lemmas (the proof of `lwSplitLoopsX_spec` is the probe's, lines 444-454 there) and the instances.
- Partition: `lwExpTerm5_partition_eq` shows `Γ.partition m` is `partitionX Γ` with each coefficient multiplied by `m^j m̄^{j'}` (from `lwSplitLoopsX_spec`). `partitionX_spec`, `val_eq_partitionX` (through `LGraph.val_eq_partition` and `lwExpTerm5_val_scaleP`) and `partitionX_normal` (through `LGraph.partition_normal 1`) follow; `Normal` does not read `coeff`, so no hypothesis is lost.
- `oe2xR1_val_zero` uses exactly `Γ.Normal`, `p ∈ lwSplit Γ.solid`, `p.1 = ⟨true,false,inr x,y⟩`, `y ≠ inr x` (as section (a) found): a solid non-loop edge on `{x,y}` gives by `Normal` a `×`-edge there, and `oe2xR1d` adds the `=`-edge; the product of the two dotted factors is `0` at every labelling.
- `RCand.kids_identity`: if `![x,y]` does not factor through `P.ext`, `P.val` and every `pcomp P Q` value are `0` (`lvl1Comp_val`). Otherwise `P.val = P.g.val ℓ'`, and `oe2x_graph_E` (private wrapper `lwExpTerm5_oe2x` at `LWG5Data`: `hG := gaussIBP sz`, `hz := lwWx_im_pos`, `hu := ht0`, `hm0 := lwWx_mE_ne`, `hzm := lwWx_flow`, `Sp := lwSplus sz n t (mE E)`, `M := diagonal`, `hSp := lwSplus_spec ht0.le (‖m‖ = 1, t < 1)`, `hM`, `c.hq1`) gives the eight integrals. `R1` is `0` by value. Each family `Rk m` has the coefficient `m^j` times that of `Rk 1` with equal edge lists (`lwExpTerm5_val_coeff`; `j = 3` for `R2,R4,R6,R8`, `j = 1` for `R3,R5,R7`, edge lists by `rfl`, coefficient by `simp [oe2xRk, LGraph.owxExt]`); its expectation is re-partitioned by `lwExpTerm5_integral_partitionX` (integrability of every graph value, `Tame.integrable` as in `oe2x_graph_E`), `pcomp` values by `lwExpTerm5_pcomp_val`.
- `expandG_sum` is an induction on the fuel using `lwExpTerm5_flat_sum` (weights multiply along a branch). `lwExpandIdentity_holds` applies it to `lwStep sel` with `Inv P := P.g.Normal` (no strengthening needed), `Φ P := ∫ P.val (LWG5Data ..) ![x,y]`, `w q := m^{q.1} (star m)^{q.2}`, step identity `RCand.kids_identity`, then `expand_eq_expandG`, and the root partition by `lwExpTerm5_integral_partitionX` at `LWG5Graph k s` (`PGraph.val` of a `partitionX` member at `![x,y]` against `LGraph.val` needed no change).
- No hypothesis was added to any pinned statement; no pinned signature differs from the check file or the ticket texts (pin scripts above). `lwG5Cand_iff_nonempty` is a theorem copied from the probe.

## (c) Verified Mathlib and project names used (`#check` in `scratchpad/T2307/chkmathlib.lean`, all resolved)
- `List.flatMap_congr`: exists (signature printed by `#check`)
- `List.map_flatMap`: exists (signature printed by `#check`)
- `List.flatMap_map`: exists (signature printed by `#check`)
- `List.mem_flatMap`: exists (signature printed by `#check`)
- `List.sum_map_mul_left`: exists (signature printed by `#check`)
- `List.sum_map_add`: exists (signature printed by `#check`)
- `List.prod_eq_zero`: exists (signature printed by `#check`)
- `Option.map_eq_some_iff`: exists (signature printed by `#check`)
- `Finset.mul_sum`: exists (signature printed by `#check`)
- `integral_const_mul`: exists (signature printed by `#check`)
- `integral_zero`: exists (signature printed by `#check`)
- `integrable_zero`: exists (signature printed by `#check`)
- `integrable_finsetSum`: exists (signature printed by `#check`)
- `Integrable.const_mul`: exists (signature printed by `#check`)
- `Function.Surjective.injective_comp_right`: exists (signature printed by `#check`)
- `RBM.Graph.lvl1_mem_split_fst` (merged project file): exists (`LWLvl1.lean:1023`)
- `RBM.Graph.owx_integral_list_sum` (merged project file): exists (`LWWeightExp.lean:956`)
- `RBM.Graph.owx_integrable_list_sum` (merged project file): exists (`LWWeightExp.lean:946`)
- `RBM.Graph.lwStein_term_tame1` (merged project file): exists (`LWStein.lean:1514`)
- `RBM.Gauss.Sizes.lwExpTerm3_instGraph_normal` (merged project file): exists (`LWExpTerm3.lean`, used in the instance)
Names checked absent: none needed. Deprecated in this Mathlib (tool log warnings): `dif_pos`, `dif_neg`, `if_pos`, `if_neg`; the file uses `simp only [h, ↓reduceDIte]` / `[↓reduceIte]` instead.

## (d) Open issues and paper-delta candidates
- Paper-delta candidates `T2307a…`: none (the ticket expected none beyond T2265a–c and T2288a–e). The Lean statement is stronger than the paper needs: the identity holds for every `sel` and every fuel.
- Registry: `LWJoined`, `LWG5Cand`, `LWG5Progress` are `Prop`-valued graph predicates that no theorem of this file assumes, so the pre-check lists none; a downstream ticket that assumes one as a hypothesis will see it listed.
- The instance of `RCand.kids_identity` is at a hand-built normal graph (`lwExpTerm3_instGraph`), not at a member of `partitionX (LWG5Graph k s)`: `partitionX` goes through the noncomputable class instances of `LWVocab.lean` (`Fintype`/`DecidableEq` of `ExtCls`/`IntCls`), so `decide` cannot unfold them (not tried). The endpoint instance `lwExpTerm5_inst_identity` is at the real data and root.
- Public names added besides the pinned ones: `lwExpTerm5_inst_identity`, `lwExpTerm5_inst_kids_identity`, `lwExpTerm5_inst_kids_normal`, `lwExpTerm5_inst_R1_val_zero`, `lwExpTerm5_inst_val_eq_partitionX` (five theorems in `RBM.Gauss.LWInst`); six unnamed `example`s; 16 `private` helpers prefixed `lwExpTerm5_`.
- The hub adds `import RBM3D.Graph.LWExpTerm5` after the last import line of `RBM3D.lean` at merge (not done here).
