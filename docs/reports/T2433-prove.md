Prover model: claude-sonnet-5-5

## (a) Math preflight — Mon Oct 12 01:24:03 UTC 2026 (`date -u`)

Cites: `ID` = `RBM3D/Graph/BAExpandId.lean`, `GG` = `Graph/BAGGOp.lean`, `V` = `Graph/BAVocab.lean`, `W` = `Graph/BAWeightOp.lean`, `D` = `docs/reports/T2398-design.md`, `probe` = `t/T2398:RBM3D/Probe/T2398Pins.lean`.
"Model" = a Python mirror (scratchpad `T2433/ba.py`; no Lean anywhere) of `baSplitSolid`/`splitG` (`V:163-172`), `BAGraph.ext` (`W:56`), `owxDE`, `gg2`/`gg4` (`GG:73-92`), `BARCand`/`kids` (`ID:348-366`), `expandG` (`LWExpTerm5:189`), `atom`/`mol`/`nA`/`nM` (`V:92-133`).
**Summary.** Closure PASS for all four `(k,s)` (26 of 32 root terms are leaves, 6 parents, depth 2, minimal margin 0, 0 stuck, 0 fail, under EVERY blue BACtx choice). Lemma PASS (H1, H2, H3 each necessary). No stop-rule trigger. Cost: about 2.7 times the ticket's central (row 14).

### (i) Exponent table

| # | quantity | value (script output in (ii)) | constraint | slack |
|---|---|---|---|---|
| 1 | target of `BAG5Tgt` | `5 ≤ ord + 2·1[x~y]`: ord ≥ 5 (x≁y), ≥ 3 (x~y) | every leaf | min margin over 26,248 leaves = 0 (tight). Paper pointwise `4·1[x=y]+5·1[x≠y]` false: `baAllM` has ord 4, x~y (probe 40-56) |
| 2 | root of the Lean tree | `baG5Graph k s` has `dotted := []` (`ID:75-87`); `BAGraph.ext` keeps `dotted := Γ.dotted.map emb` (`LWWeightExp:462`) | no `=`-dotted edge ever, so `packMerge` is a relabelling (`V:1107`) | 4 × 32 = 128 root terms (not D's 320). The coincidences (1)-(3), `α=β≠γ`, `x=y` of D §3.4 are not roots: they are diagonal terms of the free sums or value-level labels; `x~y` is graph-level |
| 3 | per `(k,s)`: root terms / leaves at once / parents `(ord, margin, x~y, #cand, #BACtx, #kids, #nonleaf kids)` | 32 / 26 / `(3,-2,0,3 or 5,3,63,14)`, 4×`(4,-1,0,1..3,1..2,47,0)`, `(2,-1,1,3,3,47,0)` (`s=0`: 3 cand, `s=1`: 5 for the first) | each parent needs a BACtx candidate | 24 parents, all with 1-3 BACtx candidates; 12 steps at the four ord-3 parents give 168 non-leaf kids (all ord 4, margin -1), 0 stuck |
| 4 | fuel `F`; selector | `F = 2`; `BAselStar P = none` if `BAG5Leaf P`, else a blue BACtx candidate (classical choice) | depth of the closure ≤ `F` | depth 2 = `F` (slack 0); `F ≥ 2` also closes (the selector stops at leaves). Closure holds for every blue BACtx choice, so no S*-specific table is needed; "first candidate" rule: 1,288 leaves per `(k,s)`, 5,152 in all; every choice: 26,248 |
| 5 | red pairs (dispatcher note 5) | BACtx candidates met in the tree: 376 blue, 0 red; every one of the 192 non-leaf nodes has a blue one | selector never picks red | blue-only Lemma suffices for the closure; target 2 asks both charges: red is `BAExpandId_flip` (`ID:127`) of blue; counters, atoms, mol are flip-invariant (about 150 lines) |
| 6 | BACtx (H1-H3) on `BARCand P` | H1: `P.g.Normal`, `atom v` all-internal, exactly 2 solid edges meet `atom v`; H2: `atom v`, `atom y'`, `atom y` pairwise distinct; H3: `atom y'` or `atom y` all-internal | `κ = BAGGOp_kappa P.g y' y` (`GG:1533`) is 1 iff not (equal or both external): H2+H3 give `κ = 1` | each H is necessary (row 7); `instCand` satisfies all three ((ii)) |
| 7 | Lemma `Δord = ord kid - ord P ≥ 1` | tree (376 cand, 26,312 kids): A1 2 (= 2κ, `gg_raw` `GG:1636`); A2,A3 1; A4 1/2; A5 1/2/3; AD 1..4; B1 1/2; B2 1/2/3; BD 1..4. Random 48,000 graphs, both charges, every candidate, `#cand / #(min Δ<1)` by (H1H2H3): 000 18716/18716; 001 31366/29371; 010 2550/2550; 011 31448/24106; 100 1214/1214; 101 4365/2816; 110 760/760; **111 6617/0** (2,012 red) | `Δord ≥ 1` | slack 0 (A2, A3, every `j = 0` term). `Δ = 1 - j + 2κ'` with `j` M-splits needs `κ' ≥ j/2`: `j = 1` needs one merge, `j = 3` needs two (not a corollary of `gg_scalingOrderG`, which gives `≥ 0`) |
| 8 | counters carried to the leaves | root max `nM` = 1, min `nW` = 2; kids `nW ≥ nW+1`, `nM ≤ nM` (`gg_counters` `GG:1621`, `gg_mono` `GG:1702`, splits only merge), `x~y` kept (old `mdot` kept: `W:56-59`, `V:170`) | leaf needs `nM ≤ 1`, `nW ≥ 2` | `nM`: 0 at roots with `nM = 1`; `nW`: 0 at roots, 1 at depth 1. Random BACtx kids: 511,495 of 511,495 satisfy all three |
| 9 | attachment (`BAG5Attached`, twin of `LWAttached` `LWExpTerm3:66`) | ≥ 2 solid edges between an internal molecule and other molecules; leaves: 13,312 have no internal molecule, 12,936 have one; min crossing = 2 at 9,736, 4 at 3,200 | every leaf | tight (2). Route: `Even` (each atom meets an even number of solid half-edges) and `Connected` give crossing even and ≥ 1; both kept by EVERY candidate step (no H): in 7,910,917 random kids, every kid of an even parent is even and every kid of a connected parent is connected (rows (ii)); true at all 26,248 leaves |
| 10 | Lean route, counters | `BAGraph.partition_of_normal` (`V:1137`), private `BAWeightOp_packMerge_counters` (`W:1385`, `open private`): counters of `packMerge Δ` = those of `Δ`; kids: `r.2 = pcomp P (packMerge Δ)`, `Δ ∈ T.splitG`, `T ∈ ggL2/ggL4` (unfold `outsOf`/`partition`) | enough for `nS nW nA nM`, `scalingOrder` | atoms/mol are NOT carried by merged lemmas: private `BAVocab_merge_atomAdj` (`V:1083`), `_adj` (`:1092`), `BAVocab_closure_equiv` (`:979`), `_vmap_injective` (`:1047`) give a new `atom (merge Γ) (vmap u) = (atom Γ u).map vmap` (about 80 lines; needed for `x~y` in `BAG5Tgt`, `BACtx`, `mol`) |
| 11 | Lean route, closure | abstract (no `decide`): Lemma, `nW`, `nM`, `x~y`, Even+Connected+`attached` ⇒ every kid of a BACtx step is a leaf if the parent has margin -1: the 20 parents `(4,-1,0,..)`, `(2,-1,1,..)` (0 non-leaf kids in the script). Concrete (`decide` on `Fin 2`/`Fin 3` and kids over `Fin 5 / Fin 7`): 128 root terms (leaf or BACtx exists); 12 steps × 63 kids: leaf or BACtx exists (756 graphs, 168 non-leaf) | existence of a BACtx candidate at the 192 non-leaf nodes | no certificate lane, no `cert_all'`, `belowOf'`, `partitionSim`, `Sound` twin. The kids of a packed parent live on `ExtCls`/`IntCls` (classical `Fintype`, `LWVocab:754`): needs a relabelling lemma (`BAGraph.map` by an equiv commutes with `ext`, `gg2`, `gg4`, `splitG`, `atom`, `mol`; about 450 lines). **Risk, untested:** kernel `decide` on Finset-based `atom`/`mol` at ≤ 9 internal vertices for 756 kids; the probe step should time one ord-3 parent (3 candidates × 63 kids); fallback: `ℕ`-list mirror plus a bridge lemma (+250 lines) |
| 12 | consumers (v) | L4g (twin of `lwExpG5'_of_expand'`, `LWExpTerm6:462`) takes `BAG5Expand' d` and `BAGraphPrecJoin d` (probe 444, `nM = 0`): leaf `Normal` (both bounds), `nM ≤ 1` (case `0`: joined bound; `1`: L4c2), `BAG5Attached` (L4c2, `(eq:Gbyxi2_BA)`), `nW ≥ 2` and `BAG5Tgt` (the `hLk` step of `lwExpTerm6_T4pos`), identity conjunct as `hLexp`. L4c1 reads `BAG5Tgt` (the `x~y` pair count) | | the joined disjunct of `LWG5LeafProps` is dropped: `nM ≤ 1` lets L4c2 split on `nM` |
| 13 | C1 | only `BASelf` and `0 ≤ t < 1` occur; no smallness of `g`, no scalar `m` | | none |
| 14 | predicted lines (estimate, class F; measured landed/central 1.5-2.1 per supervisor 0951) | `BAG5Leaf.lean`: 1,300 (900-1,900): Lemma 900 for blue (atom-merge count 350, 9 term kinds 450, kids form 80) + red 150 + pins, BACtx, selector, docs 250; `BAG5Leaf2.lean`: 1,900 (1,300-2,800): invariants and monotone counters 800, relabelling 450, closure + decide 350, packaging + instances 300 | stop line 2,000 per file | total 3,200 vs ticket 1,200 central / 2,200 hi (Lemma not in it). File 2 is within 100 of the line: fallback boundary, cut after the invariants (third file needs the dispatcher). Dropping attachment (L4c2's own pin) would save about 650; dropping red (row 5) 150: both the dispatcher's call |

Pins and statements for the probe step (mathematics / pseudo-Lean; `BAG5Tgt`, `BAG5Leaf`, `BAG5Expand` verbatim probe 158-166 = check file §2):
```
BAG5Attached (P : BAPGraph (Fin 2)) : Prop := ∀ v : P.I', (∀ w ∈ P.g.mol (inr v), w.isRight = true) →
  2 ≤ (P.g.solid.filter fun e => decide (P.g.mol e.src ≠ P.g.mol e.dst ∧ (P.g.mol e.src = P.g.mol (inr v) ∨ P.g.mol e.dst = P.g.mol (inr v)))).length
BAG5LeafProps Ls := ∀ k s, ∀ q ∈ Ls k s, q.g.Normal ∧ BAG5Leaf q ∧ BAG5Attached q          -- twin of LWExpSound:43, no Joined disjunct
BAG5Expand' d := ∃ Ls, BAG5LeafProps Ls ∧ BAG5Identity d Ls                                  -- weight 1; twin of LWExpSound:55
BACtx (c : BARCand P) := P.g.Normal ∧ (∀ w ∈ P.g.atom c.v, w.isRight) ∧ (P.g.solid.filter fun e => decide (e.src ∈ P.g.atom c.v ∨ e.dst ∈ P.g.atom c.v)).length = 2
  ∧ P.g.atom c.v ≠ P.g.atom c.p.1.dst ∧ P.g.atom c.v ≠ P.g.atom c.q.1.src ∧ P.g.atom c.q.1.src ≠ P.g.atom c.p.1.dst
  ∧ ((∀ w ∈ P.g.atom c.q.1.src, w.isRight) ∨ (∀ w ∈ P.g.atom c.p.1.dst, w.isRight))
baG5_ctx_kids_ord (c) (h : BACtx c) : ∀ r ∈ c.kids, P.scalingOrder + 1 ≤ r.2.scalingOrder       -- also ∀ T ∈ ggL2/ggL4 σ, ((ord P + 1 : ℤ) : WithTop ℤ) ≤ T.scalingOrderG
BAselStar : BASel := fun P => if BAG5Leaf P then none else if h : ∃ c : BARCand P, c.σ = true ∧ BACtx c then some h.choose else none   (classical)
baG5LeafProps_holds : BAG5LeafProps (BAexpandRoot BAselStar 2);  baG5Expand'_holds : ∀ d, BAG5Expand' d := ⟨_, _, baExpandIdentity_holds d BAselStar 2⟩
```

### (ii) One concrete nondegenerate instance

Data `d = 3, L = 3, W = 1, g0 = 0, E = 0, t = 1/2, m = i` (as `ID:748`, `BAExpandInst.baSelf_zero`); Lemma at `instP = baG5Circ` (a normal root term, 5 solid edges, 3 internal vertices), `instCand` (`v = inr 0`, `p = Ǧ_{inr0 inr1}`, `q = Ǧ_{inl0 inr0}`); closure at all `(k,s)`. No external hypothesis (C1), so no limit computation applies.
```
$ cd <scratchpad>/T2433 && python3 report.py          # 20 lines; the lines of (k,s) = (1,0), (1,1) abbreviated here
== merged decide facts: gg2,gg4,kids at instCand = (8, 5, 63) (Lean 8,5,63); partition lengths [32, 32, 32, 32] (Lean 32)
== roots: max nM over the 128 root terms = 1 ; all normal: True ; min nW = 2
 (k,s)=(0, 0) terms 32, leaf at once 26, parents (3,-2,0,3,3,63,14) (4,-1,0,2,2,47,0) (4,-1,0,1,1,47,0) (4,-1,0,1,1,47,0) (4,-1,0,2,2,47,0) (2,-1,1,3,3,47,0)
    closure: leaves 6404 depth<=2 minmargin 0 fail 0 stuck 0 | of the leaves: normal 6404 nM<=1 6404 nW>=2 6404 attached 6404 even+conn 6404 x~y 277
 (k,s)=(0, 1) terms 32, leaf at once 26, parents (3,-2,0,5,3,63,14) (4,-1,0,3,2,47,0) (4,-1,0,3,1,47,0) (4,-1,0,3,1,47,0) (4,-1,0,3,2,47,0) (2,-1,1,3,3,47,0)
    closure: leaves 6720 depth<=2 minmargin 0 fail 0 stuck 0 | of the leaves: normal 6720 nM<=1 6720 nW>=2 6720 attached 6720 even+conn 6720 x~y 277
 (k,s)=(1, 0): identical to (0,0) (leaves 6404);  (k,s)=(1, 1): identical to (0,1) (leaves 6720)
 totals over (k,s): leaves 26248 fail 0 stuck 0 | BACtx candidates met: blue 376 red 0
== Lemma on the tree: 192 nonleaf nodes, 376 BACtx candidates, 26312 kids; Δord = ord(kid) - ord(parent) per term kind:
  A1 {2: 376}; A2 {1: 376}; A3 {1: 376}; A4 {1: 376, 2: 376}; A5 {1: 376, 2: 752, 3: 376}; AD {1: 1788, 2: 4372, 3: 3380, 4: 796}; B1 {1: 376, 2: 376}; B2 {1: 376, 2: 752, 3: 376}; BD {1: 1788, 2: 4372, 3: 3380, 4: 796}
== instance: d=3, L=3, W=1, g0=0, E=0, t=1/2, m=i
  BASelf: Im m = 1.0 > 0; L^-d tr M^B = 27*(-0+1j)/27 = (-0+1j) equals m: True; 3<=L: True; 0<=t<1: True
  instP=baG5Circ: ord 3 nS 5 nW 2 nA 3 nM 1; v=inr0 y=('i', 1) y'=('e', 0)
  H1 atom(v) internal: True, solid edges at atom(v): 2 (=2); H2 distinct atoms: True; H3 internal y: True; BACtx: True
  63 kids: Δord histogram {1: 14, 2: 27, 3: 18, 4: 4}; leaves among them 49, nonleaf 14 (ord 4, x~y no)
  baAllM (probe 40): ord 4 nW 2 nM 0 x~y True target 4+2>=5 -> leaf True margin 1
$ python3 agg.py          # random part (condensed here): rnd_all.py seeds 41-43 (16,000 graphs each), inv2.py (7,910,917 kids), outputs rnd_all_4*.out, inv2.out
random: 48000 graphs (2 externals, 3-8 internals, both charges), every candidate (p,q), per (H1,H2,H3): #cands / #with min Δord<1
  000: 18716/18716; 001: 31366/29371; 010: 2550/2550; 011: 31448/24106; 100: 1214/1214; 101: 4365/2816; 110: 760/760; 111: 6617/0
  BACtx (111): 6617 cands (2012 red), 511495 kids: nW(kid)>=nW+1 511495, nM(kid)<=nM 511495, x~y kept 511495
  ANY candidate (no H): even,conn -> kid even,conn: (T,T)->(T,T) 756134; (F,T)->(F,T) 6510420, (F,T)->(T,T) 237567; (T,F)->(T,F) 389564, (T,F)->(T,T) 17232
$ python3 final.py 2>/dev/null | grep -o "first-cand leaves [0-9]* maxd [0-9]* fail [0-9]* stuck [0-9]*" | sort | uniq -c
   4 first-cand leaves 1288 maxd 2 fail 0 stuck 0      # first-BACtx-candidate rule, one line per (k,s)
```
Reading. Every hypothesis of the targets holds at these data: `BASelf` (`M^{(B)} = (g0Ψ − (E+m))^{-1} = iI`, `L^{-d} tr = i = m`, `Im m = 1`), `3 ≤ L`, `0 ≤ t < 1`, `NeZero`; `instCand` is a normal blue BACtx pair (H1-H3), its 63 kids have `Δord ∈ {1,…,4}` (the Lemma, tight), 49 are leaves and 14 (ord 4, `x≁y`) are closed by one more BACtx step; `BAexpandRoot BAselStar 2 k s` is non-empty (26 + 6 root terms give ≥ 1 output each). `baAllM` is the non-vacuity leaf of probe 169-179 (`4 + 2 ≥ 5`).

### Verdicts
| target | verdict | reason |
|---|---|---|
| 1 pins (`BAG5Tgt`, `BAG5Leaf`, `BAG5Expand`, `BAG5Attached`, `BAG5LeafProps`, `BAG5Expand'`) | PASS | statements true on the Lean tree (rows 1, 3, 9); `BAG5Tgt` not weakened |
| 2 Lemma, both charges, kids form | PASS | true at every BACtx candidate of the tree and 6,617 random ones (row 7); needs H1-H3 (each necessary) and `Normal`; supervisor 0951's "short corollary of `gg_raw`, `gg_counters` and the split count" covers A1-A3; for A4-BD the split count gives only `≥ 0` (`gg_scalingOrderG`), the `+1` needs the merge count (row 7) |
| 3 `BAselStar`, `baG5LeafProps_holds`, `BAG5Expand` | PASS | closure under every blue BACtx choice, `F = 2` (rows 3-5, 8-9); Lean route open (rows 10-11) |
| 4 `baG5Expand'_holds` | PASS | with `baExpandIdentity_holds d BAselStar 2` (`ID:589`) |
| 5 instances, 6 C1, 7 registry | PASS | (ii); C1 combinatorial; no registry line |
Not a stop (cost, for the dispatcher): the Lemma (900), the invariants (700) and the relabelling (450) are outside the 1,200 central; row 14. Paper-delta candidates for (d): T2398a, T2398b proved on the Lean tree (H1-H3 all necessary); T2433a: attachment of every leaf is Even + Connected, kept by every candidate step.

## (a″) Probe compile — Mon Oct 12 04:50:44 UTC 2026 (`date -u`)

Role `prover-max`, probe step. Worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2433`, branch `t/T2433`; one new file `RBM3D/Probe/T2433Pins.lean` (246 lines, never merged, no root import), commits `d6a0639` and `f275032` (the second changes two docstring line numbers only), the only commits on the branch beyond its base `a24d4e9`. Section (a) is not edited; there is no (a′): no stop-rule trigger was found. Scratch (not in the repository): scratchpad `T2433/w/`.
```
$ cd /Users/junyin/Lean_proof/RBM3D-wt/T2433 && lake env lean RBM3D/Probe/T2433Pins.lean     # Mon Oct 12 04:49:52 .. 04:49:58 UTC 2026, on f275032, working tree clean
BAG5Tgt : BAPGraph (Fin 2) → Prop
BAG5Leaf : BAPGraph (Fin 2) → Prop
BAG5Expand : (Bool → Bool → List (BAPGraph (Fin 2))) → Prop
BAG5Attached : BAPGraph (Fin 2) → Prop
BAG5LeafProps : (Bool → Bool → List (BAPGraph (Fin 2))) → Prop
BAG5Expand' : ℕ → Prop
@BACtx : {P : BAPGraph (Fin 2)} → BARCand P → Prop
BAselStar : BASel
BAG5Fuel : ℕ
def RBM.Graph.BAG5CtxLemma : Prop :=
∀ (P : BAPGraph (Fin 2)) (c : BARCand P),
  BACtx c →
    (∀ T ∈ BAExpandId_ggL2 c.σ P.g c.p c.q, ↑(P.scalingOrder + 1) ≤ T.scalingOrderG) ∧
      ∀ T ∈ BAExpandId_ggL4 c.σ P.g c.p c.q, ↑(P.scalingOrder + 1) ≤ T.scalingOrderG
def RBM.Graph.BAG5CtxKids : Prop :=
∀ (P : BAPGraph (Fin 2)) (c : BARCand P), BACtx c → ∀ r ∈ c.kids, P.scalingOrder + 1 ≤ r.2.scalingOrder
BAG5LeafProps (BAexpandRoot BAselStar BAG5Fuel) : Prop
BAG5Expand (BAexpandRoot BAselStar BAG5Fuel) : Prop
∀ (d : ℕ), BAG5Expand' d : Prop
∀ (k s : Bool), BAexpandRoot BAselStar BAG5Fuel k s ≠ [] : Prop
baExpandIdentity_holds : ∀ (d : ℕ) (sel : BASel) (fuel : ℕ), BAG5Identity d (BAexpandRoot sel fuel)
@BARCand.kids_normal : ∀ {P : BAPGraph (Fin 2)} (c : BARCand P), ∀ r ∈ c.kids, r.2.g.Normal
LWG5LeafProps : (Bool → Bool → List ((ℕ × ℕ) × PGraph (Fin 2))) → Prop
LWG5Expand' : ℕ → Prop
lwExpG5'_of_expand' : ∀ (d : ℕ), LWG5Expand' d → LwGraphPrecJoin d → LWExpG5' d
EXIT=0     # 72 output lines, none with "error" or "warning"; lines 26-72 (not pasted) are 11 more #checks: the inputs of the proofs, Note 5
$ cd /Users/junyin/Lean_proof/RBM3D && lake env lean /Users/junyin/Lean_proof/RBM3D-wt/T2433/RBM3D/Probe/T2433Pins.lean     # main's environment, Mon Oct 12 04:50:04 .. 04:50:10 UTC 2026, main = fc541aa
EXIT=0     # the 72 output lines are identical to the run above; /usr/bin/time -l on f275032 (04:49 UTC): 6.02 real, 3563192320 max RSS
$ pins_diff.sh; checks.sh     # scratch scripts
lines (docstrings dropped): T2398 probe 158-166: 4; check file section 2: 4; this probe: 4
diff(T2398 probe 158-166, this probe) empty
diff(check file section 2 without prefix, this probe) empty
diff(T2398 probe 40-44 baAllM, this probe) empty ( 5 lines)
HEAD=f275032 base=a24d4e9 main=fc541aa commits-beyond-base=2 probe-lines=246 modified-or-untracked= 0 hits[sorry|admit|native_decide|^axiom ]=0
name-clash grep -w of: BAG5Tgt BAG5Leaf BAG5Expand BAG5Expand' BAG5Attached BAG5LeafProps BAG5Fuel BAG5CtxLemma BAG5CtxKids BACtx BAselStar baG5LeafProps_holds baG5Expand'_holds baG5CtxLemma_holds baG5CtxKids_holds
 main worktree RBM3D/ + RBM3D.lean: 0 hits; 439 ref tips (heads+remotes), RBM3D/*.lean + RBM3D.lean outside Probe/: 0 hits; files inside Probe/: refs/heads/t/T2398:RBM3D/Probe/T2398Pins.lean 
 RBM3D/Probe/T2433Pins.lean | 246 +++++++++++++++++++++++++++++++++++++++++++++
 1 file changed, 246 insertions(+)
```
Examples (all compile above): line 164 `BAG5Leaf` at `baAllM` (T2398 probe 40-44: `ord 4`, `x ~ y`, the pointwise target fails), `BAG5LeafProps` at `[baAllMP]`, `BAselStar baAllMP = none`; line 187 `BACtx` at `instCand` (blue) and `instCandRed` (`decide +kernel`) and both Lemma pins specialised there; line 207 `BAG5Attached instP` holds and fails once the edge `inr 2 → inl 1` is removed (two crossing edges: the least allowed); line 216 `BAselStar instP ≠ none` (`instP` is not a leaf); line 232 the identity half at `BAselStar`, `BAG5Fuel` and `d = 3, L = 3, W = 1, g₀ = 0, E = 0, t = 1/2, m = i` (`baExpandIdentity_holds`, `BAExpandInst.baSelf_zero`, no hypothesis left); line 239 `BAG5LeafProps (BAexpandRoot BAselStar BAG5Fuel) → (∀ d, BAG5Expand' d) ∧ BAG5Expand (BAexpandRoot BAselStar BAG5Fuel)`.

Lean-side evidence (scratch, not in the probe). The merged definitions evaluated by `#eval` on the terms of `T.splitG` (before `packMerge`, a relabelling when no `=`-dotted edge arises: the `normal` counts below), `F = 1`, first blue `BACtx` candidate at each parent, four runs 04:37 .. 04:42 UTC (`c5_ff, c5_ft, c5_tf, c5_tt`; the rows of `k = true` equal those of `k = false`, `diff` empty):
```
(k,s) (false,false) = (true,false): 32 root terms, 26 leaves at once, all normal (true), min n_W 2, max n_M 1; parents (ord,margin,x~y,#cand,#BACtx,#kids,#non-leaf kids):
    (3,-2,0,3,3,63,14) (4,-1,0,2,2,47,0) (4,-1,0,1,1,47,0) (4,-1,0,1,1,47,0) (4,-1,0,2,2,47,0) (2,-1,1,3,3,47,0)
    F=1, first BACtx candidate: leaves 310 fail 14 stuck 0 | normal 310 n_M<=1 310 n_W>=2 310 attached 310 (least crossing 2, at 87 leaves) | x~y 67 | min margin 0 | BACtx blue 6 red 0 | Lemma on 298 kids: min Δord 1, violations 0
(k,s) (false,true) = (true,true): 32 root terms, 26 leaves at once, all normal (true), min n_W 2, max n_M 1; parents (ord,margin,x~y,#cand,#BACtx,#kids,#non-leaf kids):
    (3,-2,0,5,3,63,14) (4,-1,0,3,2,47,0) (4,-1,0,3,1,47,0) (4,-1,0,3,1,47,0) (4,-1,0,3,2,47,0) (2,-1,1,3,3,47,0)
    F=1, first BACtx candidate: leaves 310 fail 14 stuck 0 | normal 310 n_M<=1 310 n_W>=2 310 attached 310 (least crossing 2, at 87 leaves) | x~y 67 | min margin 0 | BACtx blue 6 red 0 | Lemma on 298 kids: min Δord 1, violations 0
$ lake env lean d2.lean     # 04:43 .. 04:45 UTC: the ord-3 root term of (k,s) = (false,false), all its blue BACtx candidates, then a depth-2 spot check (first 3 non-leaf kids of the first candidate, their first BACtx candidate)
ord-3 root parents of (false,false): 1
  its blue BACtx candidates: 3
    candidate: kids 63, non-leaf kids 14 (all margin -1), of them with a blue BACtx candidate 14, Lemma min Δord 1
    candidate: kids 63, non-leaf kids 14 (all margin -1), of them with a blue BACtx candidate 14, Lemma min Δord 1
    candidate: kids 63, non-leaf kids 14 (all margin -1), of them with a blue BACtx candidate 14, Lemma min Δord 1
    depth-2 spot check: non-leaf kid with 7 vertices: 47 grandkids, all leaves true, Lemma min Δord 1
    depth-2 spot check: non-leaf kid with 7 vertices: 47 grandkids, all leaves true, Lemma min Δord 1
    depth-2 spot check: non-leaf kid with 7 vertices: 79 grandkids, all leaves true, Lemma min Δord 1
$ lake env lean e2.lean     # Δord = ord Q - ord P, Q in T.splitG, T in the lists at the merged instances, 33 + 30 = 63 members each: blue (instP, instCand) and red (instPRed, instCandRed) both
total [(1, 14), (2, 27), (3, 18), (4, 4), (5, 0)]   # (d, count); blue gg2 [(1,8),(2,14),(3,9),(4,2)], gg4 [(1,6),(2,13),(3,9),(4,2)]
$ /usr/bin/time -l lake env lean t1.lean (gg2) and t2.lean (gg4)   # 03:53 UTC, `decide +kernel`: ∀ T ∈ instP.g.gg2|gg4 instCand.p instCand.q, ∀ Q ∈ T.splitG, instP.g.scalingOrder + 1 ≤ Q.scalingOrder
17.60 real 13.96 user 6153617408 max RSS (gg2)     36.80 real 32.89 user 10169090048 max RSS (gg4)     # no error line in either; t4.lean (red, both lists, 03:32 UTC): no error line, 4:47 wall under load
t3.lean (all (p,q) of instP.g meeting the graph-level BACtx condition, both lists, one `decide +kernel`): killed by `alarm 590` at 9:50 wall, no result; its `lean` process (6:20 CPU min) killed by hand at 03:37 UTC
the probe with four such kernel examples (blue/red × gg2/gg4), 03:51 UTC: 107.81 real, 90.50 user, 10274947072 max RSS, EXIT=0; they are not in the committed probe
#print axioms of a `decide +kernel` proof of the shape of probe line 207 (ax.lean): [propext, Classical.choice, Quot.sound]
```

Notes.
1. **Result.** The probe compiles, exit 0, against the worktree's build (base `a24d4e9`) and against `main` (`fc541aa`); the three pins are verbatim (diff against probe 158-166 of T2398 and against the check file empty); every example compiles. None of the targets of 1b is proved: the Lemma, the leaf properties and the non-emptiness of the root lists are statements that type-check (`#print`, `#check (… : Prop)`).
2. **Names fixed by the probe** (namespace `RBM.Graph`; the 15 names of `checks.sh` have 0 hits outside `Probe/`): `BAG5Attached`; `BAG5LeafProps Ls := ∀ k s, ∀ q ∈ Ls k s, q.g.Normal ∧ q.g.nM ≤ 1 ∧ 2 ≤ q.g.nW ∧ BAG5Attached q ∧ BAG5Tgt q`; `BAG5Expand' d := ∃ Ls, BAG5LeafProps Ls ∧ BAG5Identity d Ls`; `BACtx (c : BARCand P)` = H0-H3, σ-free; `BAG5CtxLemma` (every term of `BAExpandId_ggL2/4 c.σ P.g c.p c.q` has `↑(ord P + 1) ≤ scalingOrderG`) and `BAG5CtxKids` (`∀ r ∈ c.kids, ord P + 1 ≤ ord r.2`), each `∀ P c, BACtx c → …`; `BAselStar` (leaf: `none`; else a blue `BACtx` candidate by classical choice); `BAG5Fuel := 2`. Theorems for 1b: `baG5CtxLemma_holds`, `baG5CtxKids_holds`, `baG5LeafProps_holds : BAG5LeafProps (BAexpandRoot BAselStar BAG5Fuel)`, its corollary `BAG5Expand (…)`, `baG5Expand'_holds : ∀ d, BAG5Expand' d`.
3. **Differences from the pseudo-Lean of (a).** `BAG5LeafProps` is flat, in the order of `LWG5LeafProps` (`LWExpSound:43`), not `Normal ∧ BAG5Leaf ∧ BAG5Attached`: L4g destructures it as `lwExpG5'_of_expand'` destructures the band's tuple, and `BAG5Expand` follows in three lines (probe 239). The Lemma is pinned as two `Prop` defs over all `P : BAPGraph (Fin 2)`; its merged inputs `gg_counters`, `gg_raw`, `gg_scalingOrderG` are stated for every `Ex Ix` (output lines 26-72). The fuel is the number `2`, not `∀ F ≥ 2`. The joined disjunct of the band is dropped ((a) row 12); `BAGraphPrecJoin` (T2398 probe 444) is L4c2's pin and is not compiled here.
4. **No stop-rule trigger.** `BACtx` is met at a blue and a red parent (probe 187). The Lemma's conclusion holds at both merged instances on all 63 members each (`e2`; `decide +kernel` in scratch for blue and red). The table of (a) (row 3 and the script output of (ii)) is reproduced by the Lean definitions for all four `(k,s)` at `F = 1` (same seven numbers per parent, 14 non-leaf kids at the ord-3 parent, `stuck 0`, no red `BACtx` candidate, every leaf normal with `n_M ≤ 1`, `n_W ≥ 2`, attached); at the ord-3 parent of `(k,s) = (false,false)` each of its three `BACtx` candidates has 14 non-leaf kids and each of them has a blue `BACtx` candidate; one more step closes the three kids tried (47, 47, 79 grandkids, all leaves). Only the Python mirror of (a) has run the depth-2 closure for all 14 kids × 3 candidates and the all-choices closure (26,248 leaves): two Lean-side runs of the full `F = 2` walk (`c2_A`, `c2_B`) were stopped by hand after more than 40 CPU minutes each.
5. **The Lean route of (a) rows 10-11.** The 11 route-input `#check`s elaborate (output lines 26-72): `gg_counters`, `gg_raw`, `gg_scalingOrderG`, `BAGGOp_kappa`, `BAGraph.le_scalingOrderG_iff`, `BAGraph.partition_of_normal`, and by `open private` `BAWeightOp_packMerge_counters`, `BAVocab_merge_atomAdj`, `BAVocab_merge_adj`, `BAVocab_closure_equiv` (takes `φ : α ≃ β`), `BAVocab_vmap_injective`; the names, locations and statements of the lemmas that row 10 cites are as written. The untested risk of row 11 is now measured: `decide +kernel` on the unpacked terms costs 14 s + 33 s and 6.2 / 10.2 GB for the order inequality alone at one candidate of `instP`; the three-candidate form did not finish in 590 s; a file with four such calls peaked at 10.3 GB. Row 11 plans 12 such steps of 63 kids each: a time and memory risk for 1b, with the fallback of row 11 (a computable mirror and a bridge) as the alternative. `#eval` of the same definitions took 5353 ms for `leafB` on the 63 kids of `instCand` (`bench.lean`) and proves nothing.
6. **Paper-delta candidates:** none new from this step; T2398a, T2398b (proved by 1b) and T2433a (attachment) stand.

## (a⁗) L4S3-L1 — OUTCOME: NOT LIFTED, stuck nodes (T3C-tr_0, T3C-tr_1); D1X, D2X close — Mon Oct 12 06:28:47 UTC 2026 (`date -u`)

**Outcome.** `T3C-tr_0` and `T3C-tr_1`, each tail charge: 7 stuck nodes (below target, no BACtx candidate) = root partition term #2 (ord 4, margin -1, `x ≁ y`) + 6 depth-1 kids of the ord-3 root term #0; no selector over BACtx closes root terms #0 and #2. `D1X`, `D2X`: 0 stuck, 109 leaves per charge, depth 1, minimal margin 0, every leaf has Normal, `n_M ≤ 1`, `2 ≤ n_W`, attachment, `BAG5Tgt`. The four roots check against `BAlanlwR`, `BAGGGammaR` and `mc_cut.py`. Amend 1 item 2: stop before 1b (`all_targets_done = false`); stuck graphs below.
Role `prover-max` (claude-sonnet-5-5), scratch only: `git status --short -- RBM3D RBM3D.lean lakefile.lean lake-manifest.json lean-toolchain` in the main worktree: 0 lines. `main` = 483a67f at the Lean runs (06:14-06:21 UTC); the next commit 4a0b23b (23:21:24 -07:00) changes no file of `RBM3D/` or `RBM3D.lean` (`git diff --stat 483a67f 4a0b23b -- RBM3D RBM3D.lean`: 0 lines). `S` = `/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/60e5425b-ae97-4201-b2dc-fc981af93073/scratchpad/T2433/l4s3`. Engine: `S/../ba.py`, `tree.py`, `attach.py`, `inv.py` of the 1a step (a Python mirror of `baSplitSolid`, `BAGraph.gg2/gg4` with `owxDE`, `BAExpandId_gg2r/gg4r` (flip), `BARCand.kids`, `atom`, `mol`, `nA`, `nM`); `BACtx` = `Probe/T2433Pins.lean:73-79` (H0-H3). MC: T2434 scratch `mc_cut.py` (md5 8a33d3cc6b2359fa541dfebb6a32d240), run unmodified up to its `names = [` line (`sample`, `fam`).

### (a) Roots as `BAGraph` data with `mdot` (`x = inl 0`, `y = inl 1`, `iJ = inr J`; `G` uncircled blue, `Gc` circled blue, `Gbar` red, `S` black waved, `S+` coloured waved, `M` M-dotted; tail `G(y,x)` = blue `G_{yx}` (s=1, σ_o=+), `Gbar(x,y)` = red `Ḡ_{xy}` (s=0); `MERGED` = supervisor 0554 F1 item 2)
```
$ python3 roots.py | grep -A1 's=1' | grep -v '^--' | grep -v 'terms 32' | cut -c1-200
T3C-tr_0               s=1  internal 4 | solid Gc(x,i0) G(i2,y) G(i3,i2) G(i1,i3) G(y,x) | waved S(i1,i2) S(i0,i3) | mdot M(i0,i1)
                            terms 16  normal(all terms) True  nS/nW/nA/nM/ord of the all-Gcheck term: [(5, 2, 3, 1, 3)]
T3C-tr_1               s=1  internal 6 | solid Gc(x,i2) G(i4,y) G(i5,i4) G(i3,i5) G(y,x) | waved S+(i1,i2) S(i3,i4) S(i0,i5) | mdot M(i0,i1) M(i1,i0) M(i2,i3)
                            terms 16  normal(all terms) True  nS/nW/nA/nM/ord of the all-Gcheck term: [(5, 3, 4, 1, 3)]
D1X                    s=1  internal 4 | solid G(i3,y) G(i2,i3) G(i1,i2) G(y,x) | waved S(i1,i3) S(i0,i2) | mdot M(x,i0) M(i0,i1)
                            terms 16  normal(all terms) True  nS/nW/nA/nM/ord of the all-Gcheck term: [(4, 2, 2, 0, 4)]
D2X                    s=1  internal 4 | solid G(i3,i0) G(i2,i3) G(i1,i2) G(y,x) | waved S(i1,i3) S(i0,i2) | mdot M(x,i1) M(i0,y)
                            terms 16  normal(all terms) True  nS/nW/nA/nM/ord of the all-Gcheck term: [(4, 2, 2, 0, 4)]
MERGED(T3C-tr_0+D1X)   s=1  internal 4 | solid G(x,i0) G(i2,y) G(i3,i2) G(i1,i3) G(y,x) | waved S(i1,i2) S(i0,i3) | mdot M(i0,i1)
$ python3 cmp_iii.py
T3C-tr_0  T2434-prove (iii): internal 4, M-dotted 1 | roots.py: internal 4, M-dotted 1 | equal True
T3C-tr_1  T2434-prove (iii): internal 6, M-dotted 3 | roots.py: internal 6, M-dotted 3 | equal True
D1X       T2434-prove (iii): internal 4, M-dotted 2 | roots.py: internal 4, M-dotted 2 | equal True
D2X       T2434-prove (iii): internal 4, M-dotted 2 | roots.py: internal 4, M-dotted 2 | equal True
```
Lean text of the roots: `S/lean/xcheck.lean` (`gen_lean.py`, same data; compiles). `∂_{δγ}X_{[α]} = -W^{-d} Σ_{v∈[α]} G_{vδ} G_{γv}` and `W^{-d} 1[v ∈ [α]] = S_{αv}/t`: the block identity is the black waved edge `S(a,v)`, so **root value = t × S3 integrand** (F1).
```
$ python3 summary_roots.py
model A: L=3 W^d=2 (g0,E,t)=(0.7,0.3,0.6), 48 samples x 4 block pairs (ao,ac), both sigma_o
model B: L=4 W^d=2 (g0,E,t)=(0.5,0.2,0.35), 16 samples x 4 block pairs (ao,ac), both sigma_o
max over samples, pairs and both sigma_o of |S3 integrand (mc_cut R[14..17]) - root value / t|, and max |integrand|:
   D1X                    model A 2.6e-16 (max|integrand| 8.09e-01)   model B 2.1e-17 (max|integrand| 5.12e-02)
   D2X                    model A 2.3e-16 (max|integrand| 7.82e-01)   model B 2.1e-17 (max|integrand| 4.64e-02)
   T3C-tr_0               model A 5.6e-16 (max|integrand| 2.37e+00)   model B 1.7e-17 (max|integrand| 4.23e-02)
   T3C-tr_1               model A 5.6e-16 (max|integrand| 8.50e-01)   model B 1.2e-17 (max|integrand| 8.73e-03)
   MERGED=D1X+T3C-tr_0    model A 6.3e-16 (max|integrand| 2.88e+00)   model B 6.9e-17 (max|integrand| 6.53e-02)
   negative control, model A: T3C-tr_0 with Gc(w,x) in place of Gc(x,w)                  5.32e-01 (max|integrand| 1.26e+00)
   negative control, model A: T3C-tr_0 with the block edge on (c,v) in place of (w,v)    4.02e-01 (max|integrand| 1.26e+00)
$ python3 check_lean_formulas.py | grep -E 'literal|D1X|D2X|T3C-tr|BAGGGammaR|MG:|GM:'
literal Lean formulas (finite-difference df, eps=1e-06) vs mc_cut families, 12 samples, (ao,ac) in [(0, 0), (0, 1), (1, 2)]:
   D1X = lanlw df on X (MG)                  max|lhs-rhs|: sigma_o=+ 6.9e-11  sigma_o=- 6.0e-11    (max|rhs|: 9.23e-01 / 9.86e-01)
   D2X = lanlw df on X (GM)                  max|lhs-rhs|: sigma_o=+ 5.8e-11  sigma_o=- 4.1e-11    (max|rhs|: 7.93e-01 / 8.76e-01)
   T3C-tr_0 (df on X)                        max|lhs-rhs|: sigma_o=+ 1.2e-10  sigma_o=- 1.2e-10    (max|rhs|: 2.54e+00 / 2.60e+00)
   T3C-tr_1 (df on X)                        max|lhs-rhs|: sigma_o=+ 6.1e-11  sigma_o=- 6.5e-11    (max|rhs|: 9.31e-01 / 9.54e-01)
   BAGGGammaR (all three sums, full W)       max|lhs-rhs|: sigma_o=+ 1.7e-10  sigma_o=- 1.4e-10    (max|rhs|: 6.50e+00 / 3.87e+00)
   MG: M.BAlanlwR = C1+D1t+D1X               max|lhs-rhs|: sigma_o=+ 9.8e-11  sigma_o=- 7.1e-11    (max|rhs|: 2.08e+00 / 1.05e+00)
   GM: BAlanlwR.M = C2+D2t+D2X               max|lhs-rhs|: sigma_o=+ 8.9e-11  sigma_o=- 6.4e-11    (max|rhs|: 1.96e+00 / 9.82e-01)
```
Reading. D1X (D2X) = the `df`-on-`X` part of the second sum of `BAlanlwR` (`BAExpand.lean:106`) at `(x,y) := (α,y)` times `M_{xα}` (at `(x,α)` times `M_{αy}`); T3C-tr_k = the `df`-on-`X` part of the third sum of `BAGGGammaR` (`BAGGExp.lean:72-77`) at `(x,y,y') := (α,y,x)`, `W = 1 + (W-1)` giving `k = 0, 1`. The second script transcribes the two Lean right sides literally, with `df` by central finite differences of the resolvent (formal variables), against the families of `mc_cut.py` (which use its analytic `dX`, `dtail`). `MERGED` holds pathwise, both charges.

### (b) Closure (all BACtx choices, blue and red, fuel 2; every root partition term; `x ≁ y` and `x ~ y`)
```
$ python3 table.py
root      s | terms  leaf0 | non-leaf root terms (ord,margin,x~y,#cand,#BACtx,#kids,#nonleaf)                                | leaves depth minmar | stuck  fail | leaf props (of leaves): Normal nM<=1 nW>=2 attached Tgt
T3C-tr_0  1 |    16     11 | (3,-2,0,4,2,63,14) (4,-1,0,2,1,47,0) (4,-1,0,2,0,0,0) (4,-1,0,3,1,47,0) (2,-1,1,2,2,47,0)       |   2539     2      0 |     7     0 | 2539 2539 2539 2539 2539
T3C-tr_0  0 |    16     11 | (3,-2,0,2,2,63,14) (4,-1,0,1,1,47,0) (4,-1,0,0,0,0,0) (4,-1,0,1,1,47,0) (2,-1,1,2,2,47,0)       |   2381     2      0 |     7     0 | 2381 2381 2381 2381 2381
T3C-tr_1  1 |    16     11 | (3,-2,0,4,2,63,14) (4,-1,0,2,1,47,0) (4,-1,0,2,0,0,0) (4,-1,0,3,1,47,0) (2,-1,1,2,2,47,0)       |   2539     2      0 |     7     0 | 2539 2539 2539 2539 2539
T3C-tr_1  0 |    16     11 | (3,-2,0,2,2,63,14) (4,-1,0,1,1,47,0) (4,-1,0,0,0,0,0) (4,-1,0,1,1,47,0) (2,-1,1,2,2,47,0)       |   2381     2      0 |     7     0 | 2381 2381 2381 2381 2381
D1X       1 |    16     15 | (4,-1,0,3,2,47,0)                                                                               |    109     1      0 |     0     0 | 109 109 109 109 109
D1X       0 |    16     15 | (4,-1,0,2,2,47,0)                                                                               |    109     1      0 |     0     0 | 109 109 109 109 109
D2X       1 |    16     15 | (4,-1,0,2,2,47,0)                                                                               |    109     1      0 |     0     0 | 109 109 109 109 109
D2X       0 |    16     15 | (4,-1,0,2,2,47,0)                                                                               |    109     1      0 |     0     0 | 109 109 109 109 109
$ diff <(python3 closure.py 2 | sed -e 's/F=2/F=N/' -e 's/ | [0-9.]*s$//') <(python3 closure.py 3 | sed -e 's/F=3/F=N/' -e 's/ | [0-9.]*s$//') && echo 'closure.py 3 vs 2: diff empty (no node needs depth > 2)'
closure.py 3 vs 2: diff empty (no node needs depth > 2)
$ python3 closure.py 2 MERGED | grep -E 'closure F=' | cut -c1-240
          closure F=2 all BACtx choices: leaves 2648 maxdepth 2 minmargin 0 | stuck(below target) 7 stuck(other) 0 fail(depth F) 0 | BACtx cands blue 38 red 0, steps 38, kids 2650, Lemma min Δord 1 violations 0
          closure F=2 all BACtx choices: leaves 2490 maxdepth 2 minmargin 0 | stuck(below target) 7 stuck(other) 0 fail(depth F) 0 | BACtx cands blue 36 red 0, steps 36, kids 2492, Lemma min Δord 1 violations 0
$ python3 closure.py 2 | grep -o 'x~y leaves [0-9]*' | sort | uniq -c   # x ~ y leaves of the 8 trees: T3C-tr 169, D1X/D2X 13
   4 x~y leaves 13
   4 x~y leaves 169
$ python3 lemma_totals.py
Lemma over the 8 (root, s) trees: BACtx steps 148, kids 10284, min Δord 1, kids with Δord < 1: 0
$ python3 flipped.py | grep -c 'same up to blue<->red candidates: True'   # of 8 (root, s): flip(root) = red cut charge
8
$ python3 widened.py
closable within F=2 (1 = leaf or some candidate of the set has all kids closable), one digit per root term #0..#15; V1 = BACtx (H1-H3), V2 = H1 without "atom(v) internal", V3 = any BARCand
  T3C-tr_0  V1 s=1 0101111111111111 s=0 0101111111111111 | V2 s=1 1111111111111111 s=0 0101111111111111 | V3 s=1 1111111111111111 s=0 0101111111111111
  T3C-tr_1  V1 s=1 0101111111111111 s=0 0101111111111111 | V2 s=1 1111111111111111 s=0 0101111111111111 | V3 s=1 1111111111111111 s=0 0101111111111111
  D1X       V1 s=1 1111111111111111 s=0 1111111111111111 | V2 s=1 1111111111111111 s=0 1111111111111111 | V3 s=1 1111111111111111 s=0 1111111111111111
  D2X       V1 s=1 1111111111111111 s=0 1111111111111111 | V2 s=1 1111111111111111 s=0 1111111111111111 | V3 s=1 1111111111111111 s=0 1111111111111111
```
Columns: leaf0 = root terms that are leaves; non-leaf root terms = the parents (ord, margin = ord + 2·1[x~y] - 5, x~y, #candidates, #BACtx, #kids and #non-leaf kids at the first BACtx candidate); leaves = leaves reached under all BACtx choices; depth = largest leaf depth; minmar = least leaf margin; stuck = nodes below target (or failing `n_M ≤ 1`, `2 ≤ n_W`) with no BACtx candidate; fail = non-leaf nodes at depth F; last five = leaves with Normal, `n_M ≤ 1`, `2 ≤ n_W`, attached, `BAG5Tgt`. `x ~ y` is covered: root term #8 (M on the tail) and 169 (13) leaves. The trees are small (at most 2,539 leaves), so the exploration is exhaustive; no random sampling was needed. AND/OR (V1 = pinned BACtx): a 0 at term #0 or #2 means every BACtx candidate of #0 leaves a kid with no BACtx candidate (1 and 5 of its 14 non-leaf kids per candidate; at `δ = i2`, `v = i3` for `T3C-tr_0`) and #2 has none, so no choice at any fuel closes them.

### Stuck graphs (`T3C-tr_0`: i0..i3 = w, γ, δ, v; `T3C-tr_1`: i0..i5 = α, b, w, γ, δ, v; `s=0` lists: last script)
```
$ python3 stuck_one.py T3C-tr_0 1
T3C-tr_0 s=1: 7 stuck nodes (below target, no BACtx candidate); line = [path] ord margin | vertices with an in- and an out-solid edge | graph
  [root term #2] ord 4 margin -1 | x,y | int 4 | Gc(x,i0) Gc(i2,y) Gc(i1,i3) Gc(y,x) ; S(i1,i2) S(i0,i3) ; M(i3,i2) M(i0,i1)
  [root term #0 -> GG at i2 -> kid #1] ord 4 margin -1 | x,y | int 6 | Gc(x,i0) Gc(i1,i3) Gc(y,x) Gc(i5,y) ; S(i1,i2) S(i0,i3) S+(i4,i5) ; M(i2,i4) M(i4,i2) M(i3,i5) M(i0,i1)
  [root term #0 -> GG at i3 -> kid #2] ord 4 margin -1 | x,y | int 6 | Gc(x,i0) Gc(i2,y) Gc(y,x) Gc(i1,i5) ; S(i1,i2) S(i0,i3) S+(i4,i5) ; M(i3,i4) M(i4,i3) M(i5,i2) M(i0,i1)
  [root term #0 -> GG at i3 -> kid #17] ord 4 margin -1 | x,y,i2,i5 | int 6 | Gc(x,i0) Gc(y,x) Gc(i2,i5) Gc(i4,y) Gc(i5,i2) Gc(i1,i3) ; S(i1,i2) S(i0,i3) S(i4,i5) ; M(i3,i4) M(i0,i1)
  [root term #0 -> GG at i3 -> kid #22] ord 4 margin -1 | x,y | int 6 | Gc(x,i0) Gc(y,x) Gc(i4,y) Gc(i1,i3) ; S(i1,i2) S(i0,i3) S(i4,i5) ; M(i2,i5) M(i5,i2) M(i3,i4) M(i0,i1)
  [root term #0 -> GG at i3 -> kid #47] ord 4 margin -1 | x,y,i2,i7 | int 8 | Gc(x,i0) Gc(y,x) Gc(i2,i7) Gc(i6,y) Gc(i7,i2) Gc(i1,i5) ; S(i1,i2) S(i0,i3) S+(i4,i5) S(i6,i7) ; M(i3,i4) M(i4,i3) M(i5,i6) M(i0,i1)
  [root term #0 -> GG at i3 -> kid #52] ord 4 margin -1 | x,y | int 8 | Gc(x,i0) Gc(y,x) Gc(i6,y) Gc(i1,i5) ; S(i1,i2) S(i0,i3) S+(i4,i5) S(i6,i7) ; M(i2,i7) M(i7,i2) M(i3,i4) M(i4,i3) M(i5,i6) M(i0,i1)
$ python3 stuck_one.py T3C-tr_1 1
T3C-tr_1 s=1: 7 stuck nodes (below target, no BACtx candidate); line = [path] ord margin | vertices with an in- and an out-solid edge | graph
  [root term #2] ord 4 margin -1 | x,y | int 6 | Gc(x,i2) Gc(i4,y) Gc(i3,i5) Gc(y,x) ; S+(i1,i2) S(i3,i4) S(i0,i5) ; M(i5,i4) M(i0,i1) M(i1,i0) M(i2,i3)
  [root term #0 -> GG at i4 -> kid #1] ord 4 margin -1 | x,y | int 8 | Gc(x,i2) Gc(i3,i5) Gc(y,x) Gc(i7,y) ; S+(i1,i2) S(i3,i4) S(i0,i5) S+(i6,i7) ; M(i4,i6) M(i6,i4) M(i5,i7) M(i0,i1) M(i1,i0) M(i2,i3)
  [root term #0 -> GG at i5 -> kid #2] ord 4 margin -1 | x,y | int 8 | Gc(x,i2) Gc(i4,y) Gc(y,x) Gc(i3,i7) ; S+(i1,i2) S(i3,i4) S(i0,i5) S+(i6,i7) ; M(i5,i6) M(i6,i5) M(i7,i4) M(i0,i1) M(i1,i0) M(i2,i3)
  [root term #0 -> GG at i5 -> kid #17] ord 4 margin -1 | x,y,i4,i7 | int 8 | Gc(x,i2) Gc(y,x) Gc(i4,i7) Gc(i6,y) Gc(i7,i4) Gc(i3,i5) ; S+(i1,i2) S(i3,i4) S(i0,i5) S(i6,i7) ; M(i5,i6) M(i0,i1) M(i1,i0) M(i2,i3)
  [root term #0 -> GG at i5 -> kid #22] ord 4 margin -1 | x,y | int 8 | Gc(x,i2) Gc(y,x) Gc(i6,y) Gc(i3,i5) ; S+(i1,i2) S(i3,i4) S(i0,i5) S(i6,i7) ; M(i4,i7) M(i7,i4) M(i5,i6) M(i0,i1) M(i1,i0) M(i2,i3)
  [root term #0 -> GG at i5 -> kid #47] ord 4 margin -1 | x,y,i4,i9 | int 10 | Gc(x,i2) Gc(y,x) Gc(i4,i9) Gc(i8,y) Gc(i9,i4) Gc(i3,i7) ; S+(i1,i2) S(i3,i4) S(i0,i5) S+(i6,i7) S(i8,i9) ; M(i5,i6) M(i6,i5) M(i7,i8) M(i0,i1) M(i1,i0) M(i2,i3)
  [root term #0 -> GG at i5 -> kid #52] ord 4 margin -1 | x,y | int 10 | Gc(x,i2) Gc(y,x) Gc(i8,y) Gc(i3,i7) ; S+(i1,i2) S(i3,i4) S(i0,i5) S+(i6,i7) S(i8,i9) ; M(i4,i9) M(i9,i4) M(i5,i6) M(i6,i5) M(i7,i8) M(i0,i1) M(i1,i0) M(i2,i3)
$ python3 stuck_cmp.py
T3C-tr_0: s=1 has 7 stuck nodes, s=0 has 7; s=0 list == s=1 list with the tail Gc(y,x) replaced by Gbarc(x,y) (same paths, same graphs): True
T3C-tr_1: s=1 has 7 stuck nodes, s=0 has 7; s=0 list == s=1 list with the tail Gc(y,x) replaced by Gbarc(x,y) (same paths, same graphs): True
```
Shape. Five of the seven per tree (root term #2 and kids #1, #2, #22, #52): the solid edges form a 4-cycle `x → A → B → y → x` through atoms `A, B` whose two solid edges sit at different vertices (the `M` ties split them), so only `x`, `y` carry an in- and an out-edge: the candidates are external (H1 fails; `#cand 2` for the blue tail) and for the red tail `Ḡ_{xy}` there is none (`#cand 0`, `lean/xcheck2.out`). Kids #17, #47 also hold `Ǧ_{i2 i5} Ǧ_{i5 i2}`: the candidate at `i2` has `y = y'` (H2 fails). Supervisor 0554 (F1 item 5) expected this configuration (`baTwB_stuck`, T2398c: "4-cycles whose M-ties separate the two edges at an atom").

### Lean-side cross-check of the engine on these roots (`lake env lean` in the main worktree on `S/lean/xcheck.lean`, `xcheck2.lean`: roots as `BAGraph (Fin 2) (Fin n)`, kids by the merged `BAExpandId_ggL2/ggL4`, `splitG`, `ctxB` = BACtx)
```
$ lake env lean S/lean/xcheck.lean    # 06:14:25 .. 06:20:58 UTC, 392.69 s real, 3461824512 max RSS, exit 0; xcheck2.lean 06:19:45 .. 06:20:31, exit 0
$ python3 xdiff.py
xcheck.out (Lean) vs depth1.py (Python): 8 (s, root) blocks, 32 lines compared, mismatching lines: 0
xcheck2.out (Lean) vs stuck_py.py (Python): 22 vs 22 lines, mismatching lines: 0
```
### Diagnostics (not the lift criterion) and findings
```
$ python3 relaxed2.py | cut -c1-260
T3C-tr_0 s=1: 33 distinct nodes (roots non-leaf terms + BACtx descendants), candidates in V2 minus V1: 58; min Δord 0, min Δmargin 1; (min Δord, min Δmargin) -> #candidates {(0, 1): 56, (1, 1): 2}
T3C-tr_1 s=1: 33 distinct nodes (roots non-leaf terms + BACtx descendants), candidates in V2 minus V1: 58; min Δord 0, min Δmargin 1; (min Δord, min Δmargin) -> #candidates {(0, 1): 56, (1, 1): 2}
```
- **F1 (block identity).** Every S3 root has the waved edge `S(α,v)`; a fixed `BAGraph` (chosen before `∀ t`) cannot hold `1/t` in `coeff : ℂ`, so a root identity (L4d2) reads `t · 𝔼[S3 integrand] = 𝔼[root value]`, both sides 0 at `t = 0`; `n_W` counts this edge (`n_W = 2, 3` at the roots), as in all counts above.
- **F2.** `T3C-tr_0 + D1X` is one graph (`MERGED`, 32 partition terms = 16 + 16); its closure has 2648 / 2490 leaves (= 2539 + 109, 2381 + 109) and the same 7 stuck nodes. `T3C-tr_1` and `D2X` have no such partner.
- **F3.** The stuck nodes occur only for `T3C-tr_k` (an internal molecule, `{w,γ,δ,v}` for k = 0 and `{α,b,w,γ,δ,v}` for k = 1, and `Ǧ_{xw}` circled); `D1X`, `D2X` have `n_M = 0`. Dropping "`atom(v)` internal" from H1 (V2) makes every root term closable for the blue tail (s=1) only; for the red tail V1 = V2 = V3. The 58 candidates of V2 minus V1 in the blue trees raise the margin `ord + 2·1[x ~ y]` by at least 1, while `ord` alone does not always rise (min `Δord` 0 at 56 of them, last output): a relaxed H1 would need the Lemma in the margin form.
- **Paper-delta candidate T2433b.** At BA the graph of `I₄₂`/`J₄₂` (`T3C-tr_k`) has the root partition term `Ǧ_{xw} M_{wγ} Ǧ_{γv} M_{vδ} Ǧ_{δy} Ǧ_{yx}` (ord 4, `x ≁ y`) with no GG vertex satisfying H1-H3, and the case analysis of `B:102-108` does not cover it (extends T2398c, T2434a).

## (b) Script output, stage 1b (`prover-max`, claude-sonnet-5-5), generic half only (Amend 1, H234, H235) — Mon Oct 12 11:02:21 UTC 2026 (`date -u`, first line of the run below)

Branch `t/T2433`, HEAD `40155a3`. New file `RBM3D/Graph/BAG5Leaf.lean`. Not created: `BAG5Leaf2.lean` (Amend 1 item 3). Not touched: `RBM3D.lean` (root import: hub, CLAUDE.md §1), the probe `RBM3D/Probe/T2433Pins.lean` (never merged), section (a) (no (a′): nothing in (a) rows 6-7 is false, T2433c in (d) refines "each H necessary"; the closure rows 3-5, 8-9, 11 are not exercised, Amend 1), and (a″), (a⁗), which the supervisor cites by line (0851: (a⁗) lines 163-260).
**First lines.** Closure over `baG5Graph` per `(k, s)`: not delivered (Amend 1 item 1 drops it; no theorem about `baG5Graph` here). **Lemma, both charges, and its kids form: PASS** (`baG5CtxLemma_holds`, `baG5CtxKids_holds`; hypothesis `BACtx c` only; no data, no smallness: C1). Q3-C1: no completeness statement (the only grep hit below is the module docstring naming `baG5Graph` as out of scope). Q3-C2: `BAselStar` returns only blue `BACtx` candidates (`baselStar_spec`). Lines: `BAG5Leaf.lean` 1,136 against the stop line 2,000, below it at every commit.

```
$ date -u; git rev-parse --short HEAD; git status --short | wc -l; git log --oneline a24d4e9..HEAD | wc -l
Mon Oct 12 11:02:21 UTC 2026
40155a3
       0
      10
$ wc -l RBM3D/Graph/BAG5Leaf.lean at each commit that touched it (stop line 2,000); ls RBM3D/Graph/BAG5Leaf2.lean
e038c06      805; 96bdf45      983; 62b0ba7     1111; 8305bf5     1107; b06b027     1130; 2aeceab     1132; edfd912     1134; 40155a3     1136; 
ls: RBM3D/Graph/BAG5Leaf2.lean: No such file or directory
$ lake build RBM3D.Graph.BAG5Leaf 2>&1 | grep -E "Built RBM3D.Graph.BAG5Leaf|BAG5Leaf.lean|Build completed|error"   # artifacts of the module removed first
✔ [3912/3912] Built RBM3D.Graph.BAG5Leaf (7.6s)
Build completed successfully (3912 jobs).
$ lake env lean axioms_check.lean   # #print axioms of every public theorem
'baG5CtxLemma_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'baG5CtxKids_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'baselStar_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
'baselStar_eq_none_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'BAG5LeafInst.instCtx' depends on axioms: [propext, Classical.choice, Quot.sound]
'BAG5LeafInst.instP_ord' depends on axioms: [propext, Classical.choice, Quot.sound]
'BAG5LeafInst.baG5CtxLemma_inst' depends on axioms: [propext, Classical.choice, Quot.sound]
'BAG5LeafInst.baG5CtxKids_inst' depends on axioms: [propext, Classical.choice, Quot.sound]
'BAG5LeafInst.baAllM_leaf' depends on axioms: [propext, Classical.choice, Quot.sound]
'BAG5LeafInst.baG5Attached_inst' depends on axioms: [propext, Classical.choice, Quot.sound]
'BAG5LeafInst.baG5Ctx_H3_needed' depends on axioms: [propext, Classical.choice, Quot.sound]
'BAG5LeafInst.baselStar_inst' depends on axioms: [propext, Classical.choice, Quot.sound]
$ lake env lean axioms_full.lean   # import RBM3D; import RBM3D.Graph.BAG5Leaf; #assert_rbm_axioms   (first line of its output)
axiom audit: 12377 theorems, 3831 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
exit status of lean: 0
$ (cd $WT) lake env lean $MAIN/docs/tickets/checks/T2433-check.lean; (cd $MAIN) lake env lean $WT/RBM3D/Graph/BAG5Leaf.lean   # WT = RBM3D-wt/T2433, MAIN = main worktree
check file on the branch: EXIT=0 lines=     197 error-lines=0
against main 20917ed: EXIT=0, output lines above (none = no warning)
$ git diff --stat main...t/T2433
 RBM3D/Graph/BAG5Leaf.lean  | 1136 ++++++++++++++++++++++++++++++++++++++++++++
 RBM3D/Probe/T2433Pins.lean |  246 ++++++++++
 2 files changed, 1382 insertions(+)
$ clash3.sh   # name-clash grep -w of the public constants
public constants of RBM3D.Graph.BAG5Leaf (Lean, non-private): 23: BACtx BAG5Attached BAG5CtxKids BAG5CtxLemma BAG5Expand BAG5Leaf baAllM baAllMP baAllM_leaf baG5Attached_inst baG5CtxKids_inst baG5CtxLemma_inst baG5Ctx_H3_needed baselStar_inst instCtx instP_ord BAG5LeafProps BAG5Tgt BAselStar baG5CtxKids_holds baG5CtxLemma_holds baselStar_eq_none_iff baselStar_spec
main worktree (20917ed), RBM3D/ + RBM3D.lean: total -w hits = 0
448 ref tips (heads+remotes, not t/T2433): RBM3D/*.lean + RBM3D.lean outside Probe/: total -w hits = 0
files inside Probe/ with a hit (never imported): refs/heads/t/T2398:RBM3D/Probe/T2398Pins.lean refs/heads/t/T2398:RBM3D/Probe/T2398Pins.lean refs/heads/t/T2398:RBM3D/Probe/T2398Pins.lean refs/heads/t/T2398:RBM3D/Probe/T2398Pins.lean
$ pins_diff.sh; pins2_diff.sh   # statements of the pins vs T2398 probe 158-166, check file section 2, T2433 probe
def lines: branch        4, T2398 probe (158-166 region)        4, check file section 2        4
(empty)
(empty)
BAG5Attached: identical (       4 lines)
BAG5LeafProps: identical (       2 lines)
BACtx: identical (       5 lines)
BAG5CtxLemma: identical (       4 lines)
BAG5CtxKids: identical (       2 lines)
BAselStar: identical (       3 lines)
$ grep -nE "BAexpandRoot|BAexpand |expandG|BAstep|baG5Graph|BAG5Expand'|BAG5Fuel|baG5LeafProps_holds" RBM3D/Graph/BAG5Leaf.lean | cut -c1-110
16:H235): no theorem about `baG5Graph` is proved, and no statement that a tree of the procedure ends
$ grep -cE "sorry|admit|native_decide|^axiom" RBM3D/Graph/BAG5Leaf.lean
0
$ date -u
Mon Oct 12 11:11:26 UTC 2026
```

```
$ extract_def.sh BAG5CtxLemma BAG5CtxKids BAselStar; extract.sh baG5CtxLemma_holds baG5CtxKids_holds baselStar_spec baselStar_eq_none_iff   # BAG5Leaf.lean:117,124,927,947,965,970,984
def BAG5CtxLemma : Prop :=
  ∀ (P : BAPGraph (Fin 2)) (c : BARCand P), BACtx c →
    (∀ T ∈ BAExpandId_ggL2 c.σ P.g c.p c.q, ((P.scalingOrder + 1 : ℤ) : WithTop ℤ) ≤ T.scalingOrderG) ∧
    (∀ T ∈ BAExpandId_ggL4 c.σ P.g c.p c.q, ((P.scalingOrder + 1 : ℤ) : WithTop ℤ) ≤ T.scalingOrderG)
def BAG5CtxKids : Prop :=
  ∀ (P : BAPGraph (Fin 2)) (c : BARCand P), BACtx c → ∀ r ∈ c.kids, P.scalingOrder + 1 ≤ r.2.scalingOrder
def BAselStar : BASel := fun P =>
  open Classical in
  if BAG5Leaf P then none else if h : ∃ c : BARCand P, c.σ = true ∧ BACtx c then some h.choose else none
theorem baG5CtxLemma_holds : BAG5CtxLemma
theorem baG5CtxKids_holds : BAG5CtxKids
theorem baselStar_spec (P : BAPGraph (Fin 2)) (c : BARCand P) (h : BAselStar P = some c) :
    ¬ BAG5Leaf P ∧ c.σ = true ∧ BACtx c
theorem baselStar_eq_none_iff (P : BAPGraph (Fin 2)) :
    BAselStar P = none ↔ BAG5Leaf P ∨ ¬ ∃ c : BARCand P, c.σ = true ∧ BACtx c
$ extract.sh instCtx instP_ord baG5CtxLemma_inst baG5CtxKids_inst baselStar_inst baAllM_leaf   # BAG5Leaf.lean:1010-1062, 1118 (namespace BAG5LeafInst)
theorem instCtx : BACtx instCand ∧ BACtx instCandRed
theorem instP_ord : instP.scalingOrder = 3
theorem baG5CtxLemma_inst :
    ((∀ T ∈ BAExpandId_ggL2 instCand.σ instP.g instCand.p instCand.q, ((4 : ℤ) : WithTop ℤ) ≤ T.scalingOrderG) ∧
      (∀ T ∈ BAExpandId_ggL4 instCand.σ instP.g instCand.p instCand.q, ((4 : ℤ) : WithTop ℤ) ≤ T.scalingOrderG)) ∧
    ((∀ T ∈ BAExpandId_ggL2 instCandRed.σ instPRed.g instCandRed.p instCandRed.q, ((4 : ℤ) : WithTop ℤ) ≤ T.scalingOrderG) ∧
      (∀ T ∈ BAExpandId_ggL4 instCandRed.σ instPRed.g instCandRed.p instCandRed.q, ((4 : ℤ) : WithTop ℤ) ≤ T.scalingOrderG))
theorem baG5CtxKids_inst :
    (instCand.kids.length = 63 ∧ ∀ r ∈ instCand.kids, 4 ≤ r.2.scalingOrder) ∧
    (instCandRed.kids.length = 63 ∧ ∀ r ∈ instCandRed.kids, 4 ≤ r.2.scalingOrder)
theorem baselStar_inst : ∃ c : BARCand instP, BAselStar instP = some c ∧ BACtx c ∧
    ∀ r ∈ c.kids, 4 ≤ r.2.scalingOrder
theorem baAllM_leaf : BAG5Leaf baAllMP ∧ BAG5LeafProps (fun _ _ => [baAllMP]) ∧ BAselStar baAllMP = none ∧
    baAllMP.scalingOrder = 4
```

**Narrative.**
1. Statements. `BAG5Tgt`, `BAG5Leaf`, `BAG5Expand` are verbatim (diff empty against the T2398 probe and the check file); `BAG5Attached`, `BAG5LeafProps`, `BACtx`, `BAG5CtxLemma`, `BAG5CtxKids`, `BAselStar` are identical to the probe step's text. `BAG5Expand`, `BAG5LeafProps`, `BAG5Attached` are definitions only; no theorem concludes them for a list (Q3-C1).
2. Route (sections 3-6 of the file). A term `T` of `gg2 ++ gg4` other than `A1`-`A3` is `ext k Γ rest s w md` with unsplit counters those of `Γ` plus `(1, k/2, k/2)` (merged `BAGGOp_tail2_cnt`, `_tail4_cnt`), so `ord T° = ord Γ + 1`. A member of `T.splitG` with `j` `M`-splits has `ord = ord Γ + 1 - j + 2κ'`, `κ'` the internal atoms lost (`BAG5Leaf_core`); the `+1` needs `κ' ≥ ⌈j/2⌉` (`BAG5Leaf_kappa`). One generic lemma counts `κ'` (`BAG5Leaf_nA_lt`: an internal atom merged with a vertex outside it loses one internal atom; it generalizes the private `BAExpandWOrd_nA_lt` from a singleton atom): `j ≤ 2` needs one merge, `j = 3` two (stage-wise). Pattern lemmas `BAG5Leaf_pat_one/_two/_D` give the `M`-edges of the six terms; `A4`, `B1` one split, `A5`, `B2` two at `β`, `AD`, `BD` three.
3. Hypotheses used. `h2c`, `h3` by `A1` (`κ = 1`, via merged `gg_raw`); `h1i` (the atom of `x` is internal) by `A4`, `A5`, `AD`; `h2a` (`y` outside it) by `A4`; `h1c` (only `p.1`, `q.1` meet the atom of `x`, so the ends of the derivative edge lie outside it, `BAG5Leaf_tail_out`) by `AD`; `A2`, `A3` and the `k = 4` terms `B1`, `B2`, `BD` use only `Normal`. The inequality `atom v ≠ atom y'` of `BACtx` is not used (line 929, pattern `h2a, -, h2c`).
4. Red charge. `BAExpandId_gg2r`, `gg4r` are the conjugates of the blue lists of `BAExpandId_flip Γ`; atoms, `ord`, normality, `splitG` and the filter of H1 commute with conjugation (`BAG5Leaf_flip_*`, `BAG5Leaf_red`), so the red Lemma is the blue one at `flip Γ`. The kids form is `BAGraph.le_scalingOrderG_iff` on the partition.
5. Differences from (a) rows 10-11. The order is bookkept on `T.splitG`, before `packMerge` (the merged `BAGGOp_ordG_of_split` calls `BAWeightOp_packMerge_counters`), so `atom (merge Γ) (vmap u) = (atom Γ u).map vmap` and the relabelling lemma are not needed; the Lemma is abstract over all `P` (no `decide` over kids); no certificate lane. (a) row 14 priced file 1 at 1,300 and file 2 at 1,900 lines; the closure being out of scope, one file of 1,136 lines delivers the generic half. The instances use `decide`/`decide +kernel` on the `Fin 2`/`Fin 3` data of the merged `BAExpandIdInst` only. Ports: none from RBM1D/RBM2D (no diff-stat); `BAG5Leaf_nA_lt` is the proof of `BAExpandWOrd_nA_lt` (RBM3D, `Graph/BAExpandWOrd.lean:233`) with a general atom in place of `{b}`.
6. Premise scan. A first version of the selector lemmas assumed `BAG5Leaf P` as a hypothesis; the pre-check (`import RBM3D`, `#assert_rbm_axioms`) then reported `[RBM.Graph.BAG5Leaf]` as an unregistered premise (a `Prop`-valued definition assumed by a theorem, concluded by none). The delivered `baselStar_eq_none_iff` has no such hypothesis and `instCtx` is a conjunction (a theorem concluding `BACtx` would count as its proof), so no theorem here assumes or concludes `BAG5Leaf`, `BAG5Tgt`, `BACtx`, `BAG5Attached`; the pre-check above passes and "Registry: none" holds.
7. Length. `docs/reports/T2433-prove.md` had 286 lines (`wc -l`) before this stage, from (a), (a″), (a⁗) which I did not shorten; (b)-(d) add 147, so the report exceeds the 300 lines of CLAUDE.md §6.

## (c) Verified names used (`#check` in `lake env lean` on the branch, Mon Oct 12 11:14:19 UTC 2026 (`date -u`))

List.Sublist.eq_of_length : ∀ {α : Type u_1} {l₁ l₂ : List α}, l₁.Sublist l₂ → l₁.length = l₂.length → l₁…
List.exists_mem_of_length_pos : ∀ {α : Type u_1} {l : List α}, 0 < l.length → ∃ a, a ∈ l
List.Sublist.cons_cons : ∀ {α : Type u_1} {l₁ l₂ : List α} (a : α), l₁.Sublist l₂ → (a :: l₁).Sublist (…
List.Sublist.cons : ∀ {α : Type u_1} {l₁ l₂ : List α} (a : α), l₁.Sublist l₂ → l₁.Sublist (a :: l₂…
List.Sublist.length_le : ∀ {α : Type u_1} {l₁ l₂ : List α}, l₁.Sublist l₂ → l₁.length ≤ l₂.length
List.Sublist.subset : ∀ {α : Type u_1} {l₁ l₂ : List α}, l₁.Sublist l₂ → l₁ ⊆ l₂
List.filter_eq_nil_iff : ∀ {α : Type u_1} {p : α → Bool} {l : List α}, List.filter p l = [] ↔ ∀ a ∈ l,…
List.filter_append : ∀ {α : Type u_1} {p : α → Bool} (l₁ l₂ : List α), List.filter p (l₁ ++ l₂) = L…
List.length_eq_zero_iff : ∀ {α : Type u_1} {l : List α}, l.length = 0 ↔ l = []
List.filter_map : ∀ {β : Type u_1} {α : Type u_2} {f : β → α} {p : α → Bool} {l : List β}, List.…
List.Perm.filter : ∀ {α : Type u_1} (p : α → Bool) {l₁ l₂ : List α}, l₁.Perm l₂ → (List.filter p…
List.Perm.length_eq : ∀ {α : Type u_1} {l₁ l₂ : List α}, l₁.Perm l₂ → l₁.length = l₂.length
List.flatMap_congr : ∀ {α : Type u_1} {β : Type u_2} {l : List α} {f g : α → List β}, (∀ x ∈ l, f x…
List.map_flatMap : ∀ {β : Type u_1} {γ : Type u_2} {α : Type u_3} {f : β → γ} {g : α → List β} {l…
List.flatMap_map : ∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} (f : α → β) (g : β → List γ) (l…
List.any_map : ∀ {α : Type u_1} {β : Type u_2} {f : α → β} {l : List α} {p : β → Bool}, (List…
List.any_append : ∀ {α : Type u_1} {f : α → Bool} {xs ys : List α}, (xs ++ ys).any f = (xs.any f…
List.any_eq_true : ∀ {α : Type u_1} {p : α → Bool} {l : List α}, l.any p = true ↔ ∃ x ∈ l, p x =…
Option.ne_none_iff_exists' : ∀ {α : Type u_1} {o : Option α}, o ≠ none ↔ ∃ x, o = some x
Bool.eq_false_or_eq_true : ∀ (b : Bool), b = true ∨ b = false
Finset.card_erase_of_mem : ∀ {α : Type u_1} {s : Finset α} {a : α} [inst : DecidableEq α], a ∈ s → (s.era…
Finset.card_pos : ∀ {α : Type u_1} {s : Finset α}, 0 < s.card ↔ s.Nonempty
Finset.card_le_card : ∀ {α : Type u_1} {s t : Finset α}, s ⊆ t → s.card ≤ t.card
Finset.card_image_le : ∀ {α : Type u_1} {β : Type u_2} {s : Finset α} {f : α → β} [inst : DecidableEq…
Finset.mem_erase : ∀ {α : Type u_1} [inst : DecidableEq α] {a b : α} {s : Finset α}, a ∈ s.erase…
Relation.ReflTransGen.single : ∀ {α : Type u_1} {r : α → α → Prop} {a b : α}, r a b → Relation.ReflTransGen r…
Relation.ReflTransGen.tail : ∀ {α : Type u_1} {r : α → α → Prop} {a b c : α}, Relation.ReflTransGen r a b →…
List.Sublist.cons₂ : deprecated (lean core); `List.Sublist.cons_cons` used instead

## (d) Open issues and paper-delta candidates

Not delivered, by Amend 1 / H234 / H235 (not defects): the closure over `baG5Graph` and the fuel; `BAG5Expand'` and `baG5Expand'_holds`; `baG5LeafProps_holds` and its corollary (Q3-C1); any theorem about `BAG5Attached` or about the leaves of a tree. Paper-delta candidates (numbers: dispatcher):
- **T2398a** (corrected target `ord ≥ 5 - 2·1[x ~ y]`): carried as the pin `BAG5Tgt`. Compiled here: `baAllM_leaf` (`ord 4`, `x ~ y`; a leaf for the corrected target, so the pointwise `ord ≥ 5` fails at this graph). `baAllM` is the all-`M` leaf of `𝒢_{xy}` according to the T2398 probe's docstring (`ba_pointwise_fails` there); that it occurs in the partition of `baG5Graph` is not re-proved here.
- **T2398b** (`(eq:GGraisesord)` needs the context H1-H3): proved by `baG5CtxLemma_holds`, both charges. H3 is necessary: compiled in `baG5Ctx_H3_needed` (H1, H2 hold, H3 fails at the merged `baGGLhs`, the term `A1` of `gg2` has `ordG < ord Γ + 1`, from the merged `BAGGOpInst.A1_keeps`). The necessity of H1 and of H2 is the randomized evidence of (a) row 7, not compiled here.
- **T2433a** (every leaf is attached, by Even + Connected): NOT proved by this row (closure dropped; `BAG5Attached` is a pin), as the 1a-audit §6 item 3 asks.
- **T2433b** (the `T3C-tr` configuration with no GG vertex satisfying H1-H3): stands as proposed in (a⁗); not re-derived.
- **T2433c** (observation, not a paper difference): the inequality `atom v ≠ atom y'` of `BACtx` is not used by the proof (item 3 above), so `baG5CtxLemma_holds` holds without it; the pin is unchanged, weakening it is the dispatcher's call.
Notes for consumers: (1) a theorem that takes `BAG5Leaf`, `BAG5Tgt`, `BACtx` or `BAG5Attached` as a hypothesis (L4g, L4c1) makes `#assert_rbm_axioms` ask for a registry line unless some theorem concludes the predicate (the `structuralProps` list of `Test/Axioms.lean`, as for `LWAttached`); this file needs none. (2) `BAselStar` is blue-only as in the probe; red `BACtx` candidates are covered by the Lemma, so a selector over them needs no new Lemma work. (3) Merge step for the hub: `import RBM3D.Graph.BAG5Leaf` after the last import of `RBM3D.lean`.
