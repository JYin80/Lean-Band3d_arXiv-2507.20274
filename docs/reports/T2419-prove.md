Prover model: claude-sonnet-5-5

## (a) Math preflight — Sun Oct 11 10:28:12 UTC 2026

Citations: `LW5` = `RBM3D/Graph/LWExpTerm5.lean`, `BAGO` = `Graph/BAGGOp.lean`, `BAGE` = `Graph/BAGGExp.lean`, `BAV` = `Graph/BAVocab.lean`, `probe` = `t/T2398:RBM3D/Probe/T2398Pins.lean`. The targets have no exponent pairs, so the table lists the constants, weights, binders and size counts they depend on; the ticket's three preflight items (section map, packing, predicted lines) are rows of the table.

### (i) Exponent table

| # | quantity | value | constraint it must satisfy | slack |
|---|---|---|---|---|
| 1 | engine weight `w : ℕ×ℕ → ℂ` | `w = fun _ => 1` (probe 490-494) | `ExpandGSum` (`LW5:199`) needs `w (0,0) = 1` and `w (a+c, b+e) = w (a,b) * w (c,e)` | `1 = 1*1` holds identically; kid pairs are all `(0,0)`, no `m^j m̄^{j'}` |
| 2 | step identity coefficient | D402: `(W-1)_{xβ} = (M⁺S⁺)_{xβ}` (`ba_W_sub_one`, `BAGE:51`; `baGGGamma_holds`, `BAGE:358`) | the one-step identity is `baExpFrame_gg` (`BAGO:785`), the graph form of `baGGGamma_holds` at `BAlwData`, `PF d L W 0`; no new coefficient is proved in this ticket | none to prove: `gg2`/`gg4` lists are those of T2410 |
| 3 | binders of the step | `baExpFrame_gg`: `L W` with `NeZero`, `3 ≤ L`, `g0 Em t : ℝ`, `m : ℂ`, `BASelf d L g0 Em m`, `0 ≤ t`, `t < 1`; for `p ∈ lwSplit Γ.solid`, `q ∈ lwSplit p.2`: `p.1.σ = q.1.σ = true`, `p.1.circ = q.1.circ = true`, `p.1.src = q.1.dst` | must coincide with `BAG5Identity` (probe 149): `∀ L W [NeZero L] [NeZero W], 3 ≤ L → ∀ g0 E t m, BASelf d L g0 (E:ℂ) m → 0 ≤ t → t < 1 → ∀ k s x y` | identical binder lists (`BAGO:785-789` vs probe 149-152); `t = 0` is included, `t = 1` excluded, `L = 3` allowed (slack 0 at `L = 3`, intended) |
| 4 | candidate `BARCand P` (`P : BAPGraph (Fin 2)`) | data `v : P.E' ⊕ P.I'`, `p q` with `hp : p ∈ lwSplit P.g.solid`, `hq : q ∈ lwSplit p.2`, `p.1.σ = true`, `p.1.circ = true`, `q.1.σ = true`, `q.1.circ = true`, `p.1.src = v`, `q.1.dst = v` | exactly the hypotheses of `baExpFrame_gg`; `v` may be external or internal (the frame identity has no condition on `v`, `y`, `y'`) | none missing. **Finding:** the ticket says "two same-charge solid edges"; the merged identity (`BAGGGamma`, `baExpFrame_gg`) is for the blue charge only (`σ = true`). A red pair has no merged identity here, so `BARCand` is blue-only; a red-pair rule would be a new identity (owed to L4e-C if its selector needs it) |
| 5 | step output `kids` | `((gg2 Γ p q ++ gg4 Γ p q).flatMap partition)` packed with `pcomp`-style read through `P.ext`, each pair `(0,0)` (twin of `BAPGraph.outsOf`, `t/T2395:RBM3D/Probe/T2395Pins.lean:154`; **not merged**: `grep -rn outsOf RBM3D` is empty, so it is twinned as `BAExpandId_outsOf`) | the value identity needs `T.val = BAComb.val T.partition` (`BAGraph.val_eq_partition`, `BAV:919`, no hypothesis on the data) and `(pcomp P Q).val ℓe = Q.val ℓ'` for `ℓe = ℓ' ∘ P.ext` (`0` if `ℓe` does not factor); normality of kids by `BAGraph.partition_normal` (`BAV:930`) | merged lemmas cover the partition; only the packing lemma is new |
| 6 | integrability (needed to split `∫ Σ = Σ ∫`) | `Integrable (fun ω => T.val (BAlwData d L W g0 E t m ω) ℓ) (PF d L W 0)` for every `BAGraph T`, then for `BAPGraph` | `0 < t`: tame (`BAWeightOp_val_tame`, private in `Graph/BAWeightOp.lean:644`, reached by `open private` as `BAGO:47-56` does) transported by `BAExpandW_integrable_PF` (private, `BAExpandW.lean:295`; copy `BAGGExp_integrable_PF` exists privately in `BAGE`); `t = 0`: `BAExpand_Gc_zero` (`BAExpand.lean:731`) gives `Ǧ = 0`, so `G = M` and `BAlwData` does not depend on `ω` (constant, integrable) | the merged proofs (`BAGO:795`) split `t = 0` from `0 < t` and use tameness only for `0 < t`; the same split here, no extra hypothesis |
| 7 | the root | `baG5Graph k s` (probe 135), all 5 solid edges uncircled; `Ls k s := (baG5Graph k s).partition.flatMap (expand ·)` | `val_eq_partition` + integrability (row 6) give `𝔼 root.val = Σ_{Q ∈ partition} 𝔼 Q.val`; script: partition of the root has `2^5 = 32` terms, all normal | exact (no loss) |
| 8 | the expansion | `BAexpand sel fuel := expandG (BAstep sel) fuel`, `BAstep sel P = (sel P).map BARCand.kids`; `Inv := P.g.Normal` | `expandG_sum` (`LW5:234`) hypotheses: `w` (row 1) and the step lemma `Inv P → st P = some l → (∀ r ∈ l, Inv r.2) ∧ Φ P = Σ w r.1 * Φ r.2` (= `kids_normal` + `kids_identity`) | holds for every selector and every fuel; no stop rule on `ord` (that is L4e-C): `LWG5Progress` (`LW5:72`) is not claimed, `baTwB_stuck` (probe 97) |
| 9 | flat-sum lemma for the root list | `lwExpTerm5_flat_sum` (`LW5:215`), model-free in the carrier `X`, weight `w` | reached by `open private ... from RBM3D.Graph.LWExpTerm5` (same mechanism as `BAGO:47`); fallback: a 20-line private copy `BAExpandId_flat_sum` | none |
| 10 | section map `LW5` -> `BAExpandId` | `LW5:55-83` vocabulary -> `baG5Graph`, `BAG5Identity` (probe 135-153, copied; `LWJoined`, `LWG5Cand`, `LWG5Progress` dropped); `:86-117` `lwSplitLoopsX`, `partitionX` -> **dropped** (BA `partition` is merged, no exponent pairs); `:120` `pcomp` -> `BAExpandId_pcomp`; `:124-147` `RCand`, `kids` -> `BARCand`, `BARCand.kids`; `:159-183` `Sel`, `expand`, `expandRoot`, `selClassical` -> `BASel`, `BAstep`, `BAexpand`, `BAexpandRoot`, `BAselClassical` + `BARCand` nonempty iff; `:185-274` `expandG`, `ExpandGSum`, `expandG_sum`, `lwStep`, `expand_eq_expandG` -> **imported** (`expandG`, `ExpandGSum`, `expandG_sum`), `lwStep` replaced by `BAstep` (no `expand_eq_expandG`: `BAexpand` is `expandG`); `:278-353` bridge, `:355-388` `R1` -> **dropped** (no vanishing family: all 7 `gg2`/`gg4` kinds are kids); `:390-414` `kids_mem`, `kids_normal` -> twin; `:416-524` integrability, `pcomp_val`, `fam`, `oe2x` -> integrability (row 6), `pcomp_val`, `pcomp_val_zero` twins, `fam`/`oe2x` replaced by `baExpFrame_gg`; `:526-624` `kids_identity`, `lwExpandIdentity_holds` -> `BARCand.kids_identity`, `BAexpandIdentity_holds`; `:628-739` instances -> section "compiled instances" | all dropped items have a BA-side replacement above or are not needed | n/a |
| 11 | predicted lines | header and docs 55; vocabulary 35; procedure defs 90; `kids_normal` 30; integrability 90; `pcomp_val` 55; root partition integral 30; `kids_identity` 90; main 60; instances 130; total about 665, band 600-1,000 | stop line 2,000 (binding); single file iff prediction <= 1,500 | central 665 vs ticket 575 central / 1,090 hi; with the ticket's ratio 1.5 the high end is about 1,000: slack >= 1,000 lines below the stop line; **one file** `Graph/BAExpandId.lean`, no `BAExpandId2.lean` |
| 12 | imports | `RBM3D.Graph.LWExpTerm5` (for `expandG`, `expandG_sum`, privates), `RBM3D.Graph.BAGGOp`, `RBM3D.Graph.BAExpandW`, `RBM3D.BA.MFixedPoint` (as the check file `docs/tickets/checks/T2419-check.lean`, which compiled with exit 0 on main per CONTROL) | no cycle: the direct imports of `LWExpTerm5` (`LW5:6-15`) contain no BA file, and the check file imports it together with `BAGGOp`, `BAExpandW`, `MFixedPoint` (exit 0 on main per CONTROL) | n/a |

External hypotheses: none. `baGGGamma_holds` and `baExpFrameE_holds` are unconditional theorems (`gaussIBP` discharged inside), `BASelf` is a hypothesis of the targets, discharged at the instance by `BAExpandInst.baSelf_zero` (`BAExpand.lean:865`: `BASelf 3 3 0 0 I`), so no limit computation (TEAM §8 lesson 14) applies.

### (ii) One concrete nondegenerate instance

Data: `d = 3`, `L = 3`, `W = 1`, `g0 = 0`, `E = 0`, `t = 1/2`, `m = i`. Targets 2 and 3 (one-step identity, `BAG5Identity`, fuel 1) at the packed graph `P = (baG5Graph true true)` with every solid edge circled (`E' = Fin 2`, `I' = Fin 3`, `ext = id`; a normal term of the root partition), candidate `v = inr 0`, `p = (Ǧ_{inr0 inr1}, [Ǧ_{inl0 inr0}, Ǧ_{inr1 inr2}, Ǧ_{inr2 inl1}, Ǧ_{inl1 inl0}])`, `q = (Ǧ_{inl0 inr0}, [Ǧ_{inr1 inr2}, Ǧ_{inr2 inl1}, Ǧ_{inl1 inl0}])`, external labels any `x y`. Model of the combinatorial hypotheses (Python; no Lean written):

```
cd <scratchpad>/T2419 && python3 -I inst.py
BASelf: Im m = 1.0 > 0;  L^-d tr M^B = 1j  equals m: True
hyps: 3<=L: True  NeZero L,W: True  0<=t<1: True  slack t: 0.5
Normal: dotted empty, all solid circled: True
counters nS,nW,nA = 5 2 3  ord = nS + 2(nW-nA) = 3
p in lwSplit solid: True ; q in lwSplit p.2: True
p.sigma=q.sigma=true, circ=true: True ; p.src = q.dst = ('i', 0) ('i', 0) True
|q.2| = 3 ; |lwSplit q.2| = 3
len gg2, gg4 = 8 5 (Lean lists_baGGLhs: 5,2 at |q.2|=0; baGG3: 6,3 at |q.2|=1; here 5+r, 2+r)
partition terms: gg2 -> 33 , gg4 -> 30 , kids total = 63
weight w = 1: w(0,0)=1 and w(a+c,b+e)=w(a,b)w(c,e): True
root partition terms = 2^5 = 32 (design T2398 s3.4: '32 normal terms each')
```

Reading of the output. Every hypothesis of the targets holds at once: `BASelf` (`m = i`, `g0 = 0`: `M^{(B)} = (-E - m)^{-1} I = i I`, so `L^{-d} tr M^{(B)} = i = m`, `Im m = 1 > 0`), `3 ≤ L`, `0 ≤ 1/2 < 1`, `p, q` blue and circled, `p ∈ lwSplit P.g.solid`, `q ∈ lwSplit p.2`, `p.1.src = q.1.dst = inr 0`. The graph is nondegenerate: 5 solid edges, 2 waved edges, 3 internal vertices, `n_A = 3`, `ord = 3`, `L^d = 27` sites. The step has 63 kids (`33` from `gg2`, `30` from `gg4`, as the partition term counts of the 13 listed terms with `r = 3`; the same 63 as the design row "`x ≠ y`, (4), ord 3 / target 5" in `docs/reports/T2398-design.md` §3.4, an independent count), the root has 32 partition terms, nonempty index sets throughout (`Idx 3 3 1` has 27 points). The gg list lengths are a model: `5 + r`, `2 + r` agree with the two merged length checks `lists_baGGLhs`, `lists_baGG3` (`BAGO:1788`, `BAGO:1796`) and with the definitions `BAGO:73-92`; the exact Lean values are a 1b `decide`/`rfl` check. At fuel 1 `BAG5Identity 3 (BAexpandRoot BAselClassical 1)` (a classical choice of candidate where one exists) is applied at `(L, W, g0, E, t, m) = (3, 1, 0, 0, 1/2, i)` (hypotheses: `by norm_num`, `BAExpandInst.baSelf_zero`). Constants of the merged instances at the same data: `baGGLhs`/`baGG3` instances at `d = 3`, `L = 3`, `W = 1`, `g₀ = 0`, `E = 0`, `m = i`, `t = 1/2` (`BAGO:1731-1736`).

### Verdicts

| target | verdict | reason |
|---|---|---|
| 1. `baG5Graph`, `BAG5Identity` (statements verbatim from probe 135-153) | PASS | binders equal those of `baExpFrame_gg` (row 3); engine instance at `BAPGraph (Fin 2)` is the probe's own (probe 490-494) |
| 2. `BARCand`, `kids_identity`, `kids_normal` | PASS | identity = `baExpFrame_gg` + `val_eq_partition` + packing + integrability (rows 4-6); **blue charge only** (row 4 finding, to be reported as a ticket reading, not a failure) |
| 3. `BAexpand`, `BAexpandIdentity_holds` | PASS | `expandG_sum` with `w = fun _ => 1` (rows 1, 7-9); `LWG5Progress` not claimed |
| 4. instances | PASS | data above, all hypotheses discharged, no `N = 0`, no empty index, `t = 1/2` |
| 5. C1 | PASS | only `BASelf` and `0 ≤ t < 1` occur; no smallness of `g`, no scalar `m` |
| 6. registry / size | PASS | none; predicted 665 lines (band 600-1,000) against stop line 2,000, one file |

Paper-delta candidate: T2419a (reading of the ticket): the candidate rule is blue-only (`σ = true`), as the merged `baExpFrame_gg` (`BAGO:785-789`) and `BAGGGamma` (`BAGE:79-82`, `Ǧ_{y'x} Ǧ_{xy}` blue) are; no merged identity covers a red pair.


## (a′) Preflight corrections — Sun Oct 11 11:12:37 UTC 2026
Amend 1 (`docs/tickets/T2419-amend-1.md`, CONTROL H217) supersedes three statements of (a), none of them a verdict: (1) row 4 "Finding"
and the row 2 verdict "blue charge only": the red-pair identity is not a new identity; it is the complex conjugate of `baExpFrame_gg`
(`BAGGOp:788`) at the conjugate graph (section 1b of the file, no input beyond conjugation), so `BARCand` has both charges; (2) the row 10
map: `BARCand` carries `σ`, and a new section 1b is added; (3) the paper-delta candidate T2419a of (a) is withdrawn (see (d)).
Verdict of (a) stays PASS; the instance of (ii) is the blue instance, the red one is in (b).

## (b) Script output (round 2, Amend 1) — Sun Oct 11 11:12:37 UTC 2026
Branch `t/T2419`, head as in the first line of the log below. `RBM3D.lean` is untouched (the root import is the hub's, CLAUDE.md §1, §3 (A) 4).
Scripts (`final.sh`, `stmts.py`, `inst.py`, `rbdiff.py`, `map.sh`, `genax.py`, `clash.sh`) are in the scratchpad `T2419/`. Output of `bash final.sh`:
```
$ git log --oneline -5
0de3517 T2419: BAExpandId docstring line lengths (Amend 1)
42e1858 T2419: BAExpandId Amend 1: red-charge GG identity (baExpFrame_gg_red by conjugation), BARCand carries sigma, red instance
de1eb31 T2419: BAExpandId section 6 (baExpandIdentity_holds), section 7 (compiled instances)
be64753 T2419: BAExpandId sections 1-5 (vocabulary, procedure, kids_normal, kids_identity)
bd0efad T2411: merge BA-G5b BA/GreenCond, GreenCond2 (baFamGain_holds, baFAav_holds)
$ wc -l RBM3D/Graph/BAExpandId.lean   # stop line 2,000
     772 RBM3D/Graph/BAExpandId.lean
$ git diff --name-only main...t/T2419; git status --short | wc -l
RBM3D/Graph/BAExpandId.lean
       0
$ grep -cE "sorry|admit|native_decide|^axiom|^\s*axiom " RBM3D/Graph/BAExpandId.lean
0
$ lake build RBM3D.Graph.BAExpandId 2>&1 | grep "BAExpandId.lean\|error\|Build completed"
Build completed successfully (3911 jobs).
$ (temporary import line in RBM3D.lean, reverted) lake build 2>&1 | grep "axiom audit\|error\|Build completed"
info: RBM3D.lean:461:0: axiom audit: 11828 theorems, 3608 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
Build completed successfully (4229 jobs).
$ git status --short | wc -l   # after revert
       0
$ lake env lean docs/tickets/checks/T2419-check.lean 2>&1 | grep -c error
0
$ python3 -I genax.py; lake env lean ax.lean | grep -c "depends on axioms: [propext, Classical.choice, Quot.sound]"; (same) | grep -vc (same); no-axiom lines
51 public declarations
46
5
'RBM.Graph.BAExpandId_flipS' does not depend on any axioms
'RBM.Graph.BAExpandId_flipW' does not depend on any axioms
'RBM.Graph.BAExpandId_flipM' does not depend on any axioms
'RBM.Graph.BAExpandId_flipPsi' does not depend on any axioms
'RBM.Graph.BAExpandId_flipP' does not depend on any axioms
'RBM.Graph.BAExpandId_star_val' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.baExpFrame_gg_red' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.BAExpandId_gg_identity' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.BARCand' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.BARCand.kids' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.BARCand.kids_normal' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.BARCand.kids_identity' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.baExpandIdentity_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.BAExpandIdInst.instCandRed' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.BAExpandIdInst.instCandRed_sizes' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.BAExpandIdInst.baExpandId_inst_kids_identity' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.BAExpandIdInst.baExpandId_inst_kids_normal' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.BAExpandIdInst.baExpandId_inst_gg_red' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.BAExpandIdInst.baExpandId_inst_kids_identity_red' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.BAExpandIdInst.baExpandId_inst_kids_normal_red' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.BAExpandIdInst.baExpandId_inst_identity' depends on axioms: [propext, Classical.choice, Quot.sound]
```
Target statements, `python3 -I stmts.py` (extracted from the file; unchanged one-line definitions `BASel`, `BAstep`, `BAexpand`, `BAexpandRoot`, `BARCand.kids` omitted; the structure fields of `BARCand` are joined by the script; the last two lines diff the code blocks of `baG5Graph`, `BAG5Identity` against `git show t/T2398:RBM3D/Probe/T2398Pins.lean`):
```
def baG5Graph (k s : Bool) : BAGraph (Fin 2) (Fin 3) where
def BAG5Identity (d : ℕ) (Ls : Bool → Bool → List (BAPGraph (Fin 2))) : Prop :=
  ∀ (L W : ℕ) [NeZero L] [NeZero W], 3 ≤ L → ∀ (g0 E t : ℝ) (m : ℂ), RBM.BA.BASelf d L g0 (E : ℂ) m → 0 ≤ t → t < 1 →
    ∀ (k s : Bool) (x y : Idx d L W),
      ∫ ω, (baG5Graph k s).val (BAlwData d L W g0 E t m ω) ![x, y] ∂(PF d L W 0) =
        ((Ls k s).map fun q => ∫ ω, q.val (BAlwData d L W g0 E t m ω) ![x, y] ∂(PF d L W 0)).sum
structure BARCand (P : BAPGraph (Fin 2)) where
  σ : Bool; v : P.E' ⊕ P.I'; p : SEdge (P.E' ⊕ P.I') × List (SEdge (P.E' ⊕ P.I')); q : SEdge (P.E' ⊕ P.I') × List (SEdge (P.E' ⊕ P.I'));
  hp : p ∈ lwSplit P.g.solid; hq : q ∈ lwSplit p.2; hpσ : p.1.σ = σ; hpc : p.1.circ = true; hqσ : q.1.σ = σ; hqc : q.1.circ = true;
  hpv : p.1.src = v; hqv : q.1.dst = v;
def BAExpandId_flip {E I : Type} (Γ : BAGraph E I) : BAGraph E I where
theorem BAExpandId_star_val {E I : Type} [Fintype I] [DecidableEq I] (Γ : BAGraph E I) (D : BALData ι)
    (hS : ∀ a b, star (D.S a b) = D.S a b) (hP : ∀ a b, star (D.gPsi a b) = D.gPsi b a) (ℓe : E → ι) :
    star (Γ.val D ℓe) = (BAExpandId_flip Γ).val D ℓe := by
def BAExpandId_gg2r (Γ : BAGraph E I) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) :
    List (BAGraph E (I ⊕ Fin 2)) :=
theorem baExpFrame_gg_red (d : ℕ) : ∀ (L W : ℕ) [NeZero L] [NeZero W], 3 ≤ L → ∀ (g0 Em t : ℝ) (m : ℂ),
    RBM.BA.BASelf d L g0 (Em : ℂ) m → 0 ≤ t → t < 1 →
    ∀ {Ex Ix : Type} [Fintype Ex] [DecidableEq Ex] [Fintype Ix] [DecidableEq Ix] (Γ : BAGraph Ex Ix)
      (ℓe : Ex → Idx d L W), ∀ p ∈ lwSplit Γ.solid, ∀ q ∈ lwSplit p.2, p.1.σ = false → p.1.circ = true →
      q.1.σ = false → q.1.circ = true → p.1.src = q.1.dst →
      ∫ ω, Γ.val (BAlwData d L W g0 Em t m ω) ℓe ∂(PF d L W 0) =
        ∫ ω, baSum (BAExpandId_gg2r Γ p q) (BAlwData d L W g0 Em t m ω) ℓe +
          baSum (BAExpandId_gg4r Γ p q) (BAlwData d L W g0 Em t m ω) ℓe ∂(PF d L W 0) := by
theorem BARCand.kids_normal {P : BAPGraph (Fin 2)} (c : BARCand P) : ∀ r ∈ c.kids, r.2.g.Normal := by
theorem BARCand.kids_identity (hL : 3 ≤ L) (g0 E t : ℝ) (m : ℂ) (hSelf : RBM.BA.BASelf d L g0 (E : ℂ) m) (ht0 : 0 ≤ t)
    (ht1 : t < 1) {P : BAPGraph (Fin 2)} (c : BARCand P) (x y : Idx d L W) :
    ∫ ω, P.val (BAlwData d L W g0 E t m ω) ![x, y] ∂(PF d L W 0) =
      (c.kids.map fun r => ∫ ω, r.2.val (BAlwData d L W g0 E t m ω) ![x, y] ∂(PF d L W 0)).sum := by
theorem baExpandIdentity_holds (d : ℕ) (sel : BASel) (fuel : ℕ) : BAG5Identity d (BAexpandRoot sel fuel) := by
def baG5Graph : probe lines 9 file lines 9 diff lines 0
def BAG5Identity : probe lines 5 file lines 5 diff lines 0
```
The red statement against the merged blue one, `python3 -I rbdiff.py` (whitespace-normalised text of `baExpFrame_gg_red` with `σ = false -> true`, `BAExpandId_gg2r/gg4r Γ p q -> Γ.gg2/gg4 p q`, against `baExpFrame_gg` at `Graph/BAGGOp.lean`):
```
red statement with (false -> true, gg2r/gg4r -> gg2/gg4) equals the merged blue statement: True
```
Instances, `python3 -I inst.py` (`d = 3`, `L = 3`, `W = 1`, `g0 = 0`, `E = 0`, `t = 1/2`, `m = i`; lines cut at 118 characters by the script; `BASelf` is `BAExpandInst.baSelf_zero`, `3 ≤ 3` and `0 ≤ 1/2 < 1` by `norm_num`; `instP`/`instPRed` are `baG5Circ`/`baG5CircRed` packed with `E' = Fin 2`, `I' = Fin 3`, `ext = id`, both normal; `instCand` blue and `instCandRed` red at `v = inr 0`; the `*_sizes` theorems are `decide`):
```
theorem instCand_sizes : (instP.g.gg2 instCand.p instCand.q).length = 8 ∧
    (instP.g.gg4 instCand.p instCand.q).length = 5 ∧ instCand.kids.length = 63 := by
theorem instP_selected : BAselClassical instP ≠ none := baSelClassical_isSome _ ⟨instCand⟩
theorem baG5Graph_partition_length : ∀ k s : Bool, (baG5Graph k s).partition.length = 32 := by
theorem baExpandId_inst_kids_identity (x y : Idx 3 3 1) :
    ∫ ω, instP.val (BAlwData 3 3 1 0 0 (1 / 2) Complex.I ω) ![x, y] ∂(PF 3 3 1 0) =
      (instCand.kids.map fun r => ∫ ω, r.2.val (BAlwData 3 3 1 0 0 (1 / 2) Complex.I ω) ![x, y] ∂(PF 3 3 1 0)).sum :=
theorem baExpandId_inst_kids_normal : ∀ r ∈ instCand.kids, r.2.g.Normal := instCand.kids_normal
theorem instCandRed_sizes : (BAExpandId_gg2r instPRed.g instCandRed.p instCandRed.q).length = 8 ∧
    (BAExpandId_gg4r instPRed.g instCandRed.p instCandRed.q).length = 5 ∧ instCandRed.kids.length = 63 := by
theorem instPRed_selected : BAselClassical instPRed ≠ none := baSelClassical_isSome _ ⟨instCandRed⟩
theorem baExpandId_inst_gg_red (ℓe : Fin 2 → Idx 3 3 1) :
    ∫ ω, baG5CircRed.val (BAlwData 3 3 1 0 0 (1 / 2) Complex.I ω) ℓe ∂(PF 3 3 1 0) =
      ∫ ω, baSum (BAExpandId_gg2r baG5CircRed instCandRed.p instCandRed.q) (BAlwData 3 3 1 0 0 (1 / 2) Complex.I ω) ℓe
        baSum (BAExpandId_gg4r baG5CircRed instCandRed.p instCandRed.q) (BAlwData 3 3 1 0 0 (1 / 2) Complex.I ω) ℓe
        ∂(PF 3 3 1 0) :=
theorem baExpandId_inst_kids_identity_red (x y : Idx 3 3 1) :
    ∫ ω, instPRed.val (BAlwData 3 3 1 0 0 (1 / 2) Complex.I ω) ![x, y] ∂(PF 3 3 1 0) =
      (instCandRed.kids.map fun r => ∫ ω, r.2.val (BAlwData 3 3 1 0 0 (1 / 2) Complex.I ω) ![x, y] ∂(PF 3 3 1 0)).sum 
theorem baExpandId_inst_kids_normal_red : ∀ r ∈ instCandRed.kids, r.2.g.Normal := instCandRed.kids_normal
theorem baExpandId_inst_identity (k s : Bool) (x y : Idx 3 3 1) :
    ∫ ω, (baG5Graph k s).val (BAlwData 3 3 1 0 0 (1 / 2) Complex.I ω) ![x, y] ∂(PF 3 3 1 0) =
      ((BAexpandRoot BAselClassical 1 k s).map fun q =>
        ∫ ω, q.val (BAlwData 3 3 1 0 0 (1 / 2) Complex.I ω) ![x, y] ∂(PF 3 3 1 0)).sum :=
```
Name-clash grep (`bash clash.sh`: `grep -rnw --include='*.lean' <name> RBM3D RBM3D.lean` outside the new file; count per new public name):
`baG5Graph: 0 BAG5Identity: 0 BARCand: 0 BASel: 0 BAstep: 0 BAexpand: 0 BAexpandRoot: 0 BAselClassical: 0 baRCand_nonempty_iff: 0 baSelClassical_isSome: 0 baExpandIdentity_holds: 0 BAExpandIdInst: 0 baG5Graph_partition_length: 0 BAExpandId_pcomp: 0 BAExpandId_outsOf: 0 baExpFrame_gg_red: 0 BAExpandId_gg_identity: 0 BAExpandId_flip: 0 BAExpandId_flipS: 0 BAExpandId_flipW: 0 BAExpandId_flipM: 0 BAExpandId_flipPsi: 0 BAExpandId_flipP: 0 BAExpandId_star_term: 0 BAExpandId_star_val: 0 BAExpandId_star_baSum: 0 BAExpandId_data_real: 0 BAExpandId_gg2r: 0 BAExpandId_gg4r: 0 BAExpandId_ggL2: 0 BAExpandId_ggL4: 0 baG5CircRed: 0 instCandRed: 0 instPRed: 0`
Section map as finally written (`LW5` = `Graph/LWExpTerm5.lean`; lines of `Graph/BAExpandId.lean`; `BAWeightOp_val_tame`, `BAWeightOp_sd`, `BAExpandW_integrable_PF`, `BAVocab_val_of_factor`, `BAVocab_val_of_not` are reached by `open private`; no port from RBM1D/RBM2D):
```
LW5:55-83   vocabulary -> baG5Graph :75, BAG5Identity :89 (probe 135-153); LWJoined, LWG5Cand, LWG5Progress dropped
(new)       section 1b :95-331 (Amend 1): BAExpandId_flip{S,W,M,Psi,P,} :110-134, BAExpandId_star_term/val/baSum :179-211,
            BAExpandId_data_real :232, BAExpandId_gg2r/gg4r :251-256, baExpFrame_gg_red :267, BAExpandId_ggL2/ggL4 :308-313,
            BAExpandId_gg_identity :320
LW5:86-117, 278-388  lwSplitLoopsX, partitionX, bridge, R1 -> dropped (BA `partition`, BAVocab:229; no exponent pairs, no vanishing family)
LW5:120     pcomp -> BAExpandId_pcomp :336, BAExpandId_outsOf :341 (twin of the unmerged T2395 outsOf)
LW5:124-147 RCand, kids -> BARCand :348 (with sigma), BARCand.kids :364
LW5:159-183 Sel, expand, expandRoot, selClassical -> BASel :368, BAstep :371, BAexpand :375, BAexpandRoot :379, BAselClassical :383,
            baRCand_nonempty_iff :387, baSelClassical_isSome :397
LW5:185-274 expandG, ExpandGSum, expandG_sum -> IMPORTED; lwStep, expand_eq_expandG -> BAstep, BAexpand := expandG
LW5:390-414 kids_normal -> BARCand.kids_normal :403
LW5:416-524 integrability, pcomp_val, fam, oe2x -> BAExpandId_integrable_*, _integral_partition, _pcomp_val(_zero), _integral_outsOf :415-530
LW5:526-624 kids_identity, lwExpandIdentity_holds -> BARCand.kids_identity :537, BAExpandId_flat_sum :576, baExpandIdentity_holds :589
LW5:628-739 instances -> BAExpandIdInst :610-768
```
Narrative.
- Amend 1 targets 1-3 are delivered. Target 1: `baExpFrame_gg_red` (:267), the red-charge `GG` identity, from `baExpFrame_gg` by conjugation. Target 2: `BARCand` carries `σ` (:348, `hpσ : p.1.σ = σ`, `hqσ : q.1.σ = σ`); `kids` (:364) takes the lists by `σ`; `kids_normal`, `kids_identity`, `baExpandIdentity_holds` are unchanged in statement and now cover both charges. Target 3: a red instance (:667-707, :728-744).
- Conjugation, which facts it uses (all from the files): `SEdge.val` and `BAMEdge.val` define a red edge as `star` of the blue value at the same endpoints, so `BAExpandId_flipS`/`flipM` toggle `σ`; `WEdge.val` defines `S^-_{xy} = star S^+_{yx}`, so `BAExpandId_flipW` toggles `σ` and swaps the endpoints of a coloured waved edge; a black waved edge is `D.S`, real for `BAlwData` (`BAlwS = t * svarF`, `BAExpandId_data_real`); `Ψ`-dotted edges go to `gPsi b a`, by `PsiI_isHermitian`; `DEdge.val` is `0/1`.
- The law is not used: the blue identity at `BAExpandId_flip Γ` is conjugated inside the integral (`integral_conj`), so no invariance of `PF d L W 0` under `H -> H̄` is needed. `BAExpandId_star_val : star (Γ.val D ℓ) = (flip Γ).val D ℓ` is for any `D` with real `S` and Hermitian `gPsi`.
- The red lists are `BAExpandId_gg2r Γ p q = ((flip Γ).gg2 (flipP p) (flipP q)).map flip`, and likewise `gg4r`; `flip` keeps `src`/`dst`, so `p.1.src = q.1.dst` carries over. `rbdiff.py` shows the red statement equals the merged blue one after the two substitutions.
- Stop rule of Amend 1: not triggered, the red identity needs no input beyond conjugation. File 772 lines against the stop line 2,000 (round 1: 462).
- Hypotheses of every target statement: `BASelf`, `3 ≤ L`, `0 ≤ t`, `t < 1` (C1); no smallness of `g`, no scalar `m`. `LWG5Progress` is not claimed (`baTwB_stuck`, probe 97).
- The red step is exercised at `instCandRed` (all five solid edges of `baG5CircRed` red); `baG5Graph k s` has at most one red solid edge (:75-88), so the fuel-1 instance `baExpandId_inst_identity` takes blue steps only, as in round 1 (the only change to the blue instance is the field `σ := true`).
- `BARCand.v` is determined by `p`, `q` (`hpv`, `hqv`); it is kept as data to match the ticket's `(v, i₁, i₂)`.
## (c) Verified Mathlib names used (`#check` in a scratch file importing the module, `lake env lean` exit 0, no error line)
New in round 2: `integral_conj` (root namespace, `Mathlib/MeasureTheory/Integral/Bochner/ContinuousLinearMap.lean:173`, `conj = starRingEnd`), `star_sum`, `star_mul'`, `star_add`, `star_star`, `Complex.star_def`, `Complex.conj_ofReal`, `Matrix.IsHermitian.apply` (`star (A j i) = A i j`), `Matrix.smul_apply`, `MeasureTheory.integral_congr_ae`, `Filter.Eventually.of_forall`, `List.mem_cons_self`, `List.mem_cons_of_mem`, `List.prod_cons`, `List.sum_cons`; merged `RBM.Gauss.PsiI_isHermitian` (`BlockAnderson.lean:65`).
Round 1 (unchanged): `MeasureTheory.integrable_const`, `integrable_zero`, `integral_zero`, `integral_add`; `Function.Surjective.comp`, `Function.Surjective.injective_comp_right`; `List.mem_flatMap`, `List.map_flatMap`, `List.map_congr_left`, `List.sum_eq_zero`; `Option.map_eq_some_iff`; `one_mul`, `sub_eq_zero`.
Absent: a public `BAPGraph.val_of_factor` / `val_of_not` (only the private `BAVocab_val_of_factor`, `BAVocab_val_of_not`, `BAVocab.lean:874, 883`); `integral_conj` is not in `MeasureTheory` (root namespace).
## (d) Open issues and paper-delta candidates
- **T2419a** (round 1, blue-only reading) is withdrawn: Amend 1 puts both charges in this row, so the Lean candidate rule agrees with "two solid edges of the same charge" (`B_graphical_lemmas.tex`, the sentence before `\label{GGGamma}`).
- **T2419b** (new): `\eqref{GGGamma}` (`B:393-405`) displays only the blue form `Ǧ_{y'x} Ǧ_{xy} f`; the red form is not displayed. Lean takes it as the complex conjugate (`baExpFrame_gg_red`): the coloured waved edge `S^+_{xβ}` becomes `S^-_{βx}` (endpoints swapped, `WEdge.val`), black waved and dotted edges are unchanged, `M ↔ M̄`; the term lists are the conjugates `BAExpandId_gg2r`, `BAExpandId_gg4r`.
- L4e-C owns the stop rule, the `ord` target and the leaf property; `BAexpandRoot` has no stop on `ord`.
- The hub adds `import RBM3D.Graph.BAExpandId` after the last import line of `RBM3D.lean` at merge.
