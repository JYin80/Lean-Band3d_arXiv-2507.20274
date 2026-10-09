Prover model: claude-opus-5-5

## (a) Math preflight — Fri Oct  9 03:06:09 UTC 2026

Restart under H149, Amend 1 (`docs/tickets/T2358-amend-1.md`). The previous (a) (FAIL: pin of `LocStepXProv` false on non-normal input) is preserved at `docs/reports/T2358-prove-1a0.md`; its C1/C2 mathematics is cited and its scripts re-run below. Scripts (mathematics only, no Lean): `/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/ec1cbe39-5957-4519-82e4-38af3363ddc4/scratchpad/T2358/` `bridge.py`, `molecular.py`, `expdata.py`, `pininst.py` (new). Citations `file:line` are at `main` 1fcb883, paths relative to `RBM3D/`; `probe NNN` is line NNN of `t/T2348:RBM3D/Probe/T2348Pins.lean`. No analytic exponents enter any target; the table lists the parameters and constants the targets depend on.

### (i) Exponent / parameter table

| # | quantity | value / range | constraint (source) | slack |
|---|---|---|---|---|
| 1 | `p` (`fxyPowGraph p`, `LWEngineProv`, bridge) | engine: every `p : ℕ`; bridge and instance: even `p`; instance `p = 2` (also `p = 4`) | bridge needs `Even p`: blue blocks `i < p/2`, red the rest (`fxyPowGraph`, `Graph/LocalRegular.lean:1354`; `fxyPowGraph_val_eq` :1739) | `p = 0` degenerate, excluded from the instance |
| 2 | weight `W = Π_k 1_D(blk ℓ(β_k))` | real, values in `{0,1}` | `WExp` accepts any real `W` (probe 77-84); the Gaussian integral is linear in the deterministic factor `W` | none needed on `D` |
| 3 | `(c, K0, d, D)` of `LWEngineProv` | `c > 0`; `K0, d, D` free | as merged `lw_localregularX` (`Graph/LWEngine.lean:771-775`) | unchanged by provenance |
| 4 | tags `(j, j')` | any in `ℕ × ℕ` | the scalar `m^j m̄^{j'}` multiplies only the coefficient (`LWEngine.lean:57`), commutes with `π`, `W` | none |
| 5 | data `LWExpData` (nine conjuncts, inline by C3) | `GaussIBP sz` (`gaussIBP`, `Green/IBPPoly.lean:305`), `Im z > 0`, `u > 0`, `m ≠ 0`, `z+um = -m⁻¹`, `Sp - m² Sp·(lwS u) = lwS u`, `Spᵀ = Sp`, `M = m·I` | `LWEngine.lean:68-75`; `lwS u = u·lwS 1` (`Graph/LWMoment.lean:211`) | instance: `Im z = 0.25`, `u = 0.5`, `‖m²S‖ = |m|²u = 0.70 < 1` |
| 6 | initial molecules of `fxyPowGraph p` | `p` internal `{α_k, β_k}`, 2 external `{x}`, `{y}` | waved edges `α_k–β_k` only (`LocalRegular.lean:1356`); `×`-dotted edges are not in `LGraph.adj` | `CoverBy β` with equality |
| 7 | normality `P.g.Normal` of the step input (AMENDED pin) | hypothesis of `LocStepXProv` (Amend 1) | needed by `lvl1_step_identity` (`hN`, `Graph/LWLvl1.lean:3591`): kills the `oe1xT1` / `R1` terms (`lvl1_oe1xT1_zero` :3389, `lvl1_oe2xR1_zero` :3408), dropped from `lvl1EdgeOutsX` / `lvl1GGOutsX` | supplied at every call: root `fxyPowGraph_normal` (:1462), children `hch` (`LWEngine.lean:703`) — see (iii) |

Mathematics (as far as (ii)-(iii) need; C1, C2 as in 1a0, unchanged by the amend).
- **C1, bridge** (twin of `lwMoment_fxyPow_val`, `LWMoment.lean:1748`). `term(ℓ) = Π_i blockVal_i(ℓα_i, ℓβ_i)` (`localReg_fxy_term`, `LocalRegular.lean:1689`); the weight factorises over blocks (it sits on the `β_k` only), so `Σ_ℓ W term = Π_i Σ_{a,b} 1_D(blk b) blockVal_i(a,b)` (`localReg_fxy_sum_pairs`, :1660). Blue block sum `= LWfD` (the `ring` step of `lwMoment_fxyVal_D`, `LWMoment.lean:1595`, with `if STblk β ∈ D` wrapped); red block `= conj` of it (`1_D`, `S` real). Product `= LWfD^{p/2} conj(LWfD)^{p/2} = ‖LWfD‖^p` (`lwMoment_pow_conj` :252). `pvalW` on a packed graph has `ext = id`, so `h.choose = ![x,y]`. At `D = univ`: `LWf`.
- **C2, `Molecular` for all constructors.** Every output of `weight`, `edge`, `gg` is `Γ.owxExt emb c s w` (waved `= Γ.waved.map emb ++ w`, `LWWeightExp.lean:458-464`), then a twist (`LGraph.conj`, `LGraph.transpose`: edges mapped endpointwise, `LWSymm.lean:100-111`; `lwSymmTwistG` :171), the dotted partition and `LGraph.merge` (`LWVocab.lean:778-782`: waved edges mapped, `=` edges delete = identify). Every new vertex is joined by an appended waved edge to `emb x` (T1,T3: `x–α`; T2,T4,R4,R6,R8: `x–α, α–β`; `oe1xD`, P3..P6, R5, R7: `x–α`; R2 adds `x–y`). With `π = vmap ∘ emb`: waved/`=` paths go to paths or equalities; an internal output molecule contains `π v` for an old `v`, or a new vertex joined to `π x`; merging cannot create a new internal molecule. `ExtOK`: `vmap (inl a) = inl (extMap a)`. Cover: `Molecular.comp`, `CoverBy.comp` (probe 88, 125). None of this reads `Normal`.

### (ii) One concrete nondegenerate instance

(A) Bridge at `p = 2` (`n = 6`, `x=0≠y=1`, `D` = labels with `blk a = a mod 3 ∈ {1,2}`: neither empty nor everything) and `p = 4` (`n = 4`); `G=(H-z)⁻¹`, `H` real symmetric, `z=0.3+0.4i`, `M=0.55i·I`, `S` real symmetric, row sums 1; brute force over all `n^{2p}` labellings with the formulas of `localReg_fxyBlockVal` (`LocalRegular.lean:1684`):
```
$ python3 /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/ec1cbe39-5957-4519-82e4-38af3363ddc4/scratchpad/T2358/bridge.py
p=2 n=6: weighted pval = 3.1951590863e-05+4.1481735277e-20j; |fD|^p = 3.1951590863e-05; |tot-|fD|^p| = 1.22e-19; |fD|=5.653e-03; unweighted pval vs |f|^p diff = 5.86e-19
p=4 n=4: weighted pval = 1.3243141238e-03-2.0216131051e-19j; |fD|^p = 1.3243141238e-03; |tot-|fD|^p| = 2.18e-18; |fD|=1.908e-01; unweighted pval vs |f|^p diff = 3.92e-18
```
(B) `LWExpData` algebraic conjuncts (conjunct 1 is the theorem `gaussIBP`; no target has an external hypothesis, so no limit computation is owed):
```
$ python3 /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/ec1cbe39-5957-4519-82e4-38af3363ddc4/scratchpad/T2358/expdata.py
m = (-0.24663709070824297+1.1554705973758683j)  |z+u m+1/m| = 0.0  Im z = 0.25  u = 0.5  m!=0: True
max|Sp - m^2 Sp S - S| = 2.7809732887839817e-17  |Sp-Sp^T| = 1.4046172853913364e-17
M diag = m, offdiag 0:  True
```
(C) `Molecular` / `ExtOK` / `Cover` on `fxyPowGraph p` (combinatorial model of `LGraph.adj` molecules; all step patterns of (i), every `x`, `y`, every partition of output vertices as the merge; random depth-4 chains with composed `π`; initial `Cover`; negative control):
```
$ python3 /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/ec1cbe39-5957-4519-82e4-38af3363ddc4/scratchpad/T2358/molecular.py
exhaustive depth-1, p=2: cases 187920 failures 0
random chains (composition), cases 24000 failures 0
p=2: internal molecules 2, ext molecules 2, each contains some beta_k: True
p=3: internal molecules 3, ext molecules 2, each contains some beta_k: True
p=4: internal molecules 4, ext molecules 2, each contains some beta_k: True
control (no waved edge to the new vertex): Molecular(2) fails in 203 of 877 merges
```
(D) **Hypotheses of the AMENDED `locStepXProv_holds`** (`LocStepX P LX` and `P.g.Normal`) at concrete data, `weight` and `edge` constructors. `weight`: `P = (fxyPowGraph 2).pack`, `x = β_0`, `p` = the loop `Ǧ_{β_0β_0}`, `c = t = false` (`lwSymmTwistS false false = id`, `LWSymm.lean:167-168`). `edge`: `P*` on `Fin 2 × Fin 1` with `solid = [⟨true,false,inr 0,inl 0⟩]` (`G_{a,x0}`) and `dotted = [⟨false, inr 0, inl 0⟩]` (`1_{a≠x0}`), `x = a`, `v = inl 0 ≠ inr a`, `p = (that edge, [])`, `c = t = false`; `P*` is the counterexample of 1a0 made normal by the `×`-dotted edge (`LGraph.Normal`, `LWVocab.lean:990-993`; `SBetween`/`XBetween` :969-975; `hbad` and `hwf` of `LocStepX.edge`, `LWEngine.lean:397-398`):
```
$ python3 /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/ec1cbe39-5957-4519-82e4-38af3363ddc4/scratchpad/T2358/pininst.py
1a0 counterexample : Normal = False | hwf = True | deg(a) = 1 hbad = True | hv: v=x0 != a: True
amended instance : Normal = True | hwf = True | deg(a) = 1 hbad = True | hv: v=x0 != a: True
fxyPowGraph 2: Normal = True | loop at beta_0 = (True, True, ('i', 1), ('i', 1)) -> weight step x=beta_0, c=t=false: hx holds: True
fxyPowGraph 2 LocStd? self-loops present: True (so a step exists; not LocStd)
```
At `P*` the dropped term has `val(lwSymmOe1xT1) = 0` pointwise in the labellings, since the `×`-dotted edge `(x≠y₁)` becomes a `×`-self-loop on the contracted vertex:
```
$ sed -n 3373,3381p RBM3D/Graph/LWLvl1.lean
theorem lvl1_val_zero_of_xself {ι : Type*} [Fintype ι] [DecidableEq ι] {E' I' : Type} [Fintype I'] [DecidableEq I']
    (T : LGraph E' I') (a : E' ⊕ I') (h : (⟨false, a, a⟩ : DEdge (E' ⊕ I')) ∈ T.dotted) (D : LData ι) (ℓe : E' → ι) :
    T.val D ℓe = 0 := by
  unfold LGraph.val
  refine Finset.sum_eq_zero fun ℓi _ => ?_
  have h0 : DEdge.val (Sum.elim ℓe ℓi) (⟨false, a, a⟩ : DEdge (E' ⊕ I')) = 0 := by simp [DEdge.val]
  have hprod : (T.dotted.map (DEdge.val (Sum.elim ℓe ℓi))).prod = 0 :=
    List.prod_eq_zero (List.mem_map.2 ⟨_, h, h0⟩)
  simp [LGraph.term, hprod]
```
(the sum is zero term by term, so every weight `W(ℓ∘π)` multiplies zero; the weighted twin of the edge/gg identity therefore loses no term).

### (iii) The amended pin and its normality suppliers (Amend 1, §29 re-check)

```
$ git show t/T2348:RBM3D/Probe/T2348Pins.lean | sed -n 157,159p   (probe; Amend 1 inserts "P.g.Normal →" after "LocStepX P LX →")
def LocStepXProv : Prop :=
  ∀ (P : PGraph (Fin 2)) (LX : List ((ℕ × ℕ) × PGraph (Fin 2))), LocStepX P LX →
    ∃ π : ∀ r ∈ LX, P.E' ⊕ P.I' → r.2.E' ⊕ r.2.I', ∀ (m : ℂ) (t0 : ℕ × ℕ),
$ sed -n 455,456p RBM3D/Graph/LWEngine.lean ; sed -n 667,668p RBM3D/Graph/LWEngine.lean
theorem lwEngine_exists_stepX (P : PGraph (Fin 2)) (hN : P.g.Normal) (hn : ¬ P.g.LocStd) :
    ∃ LX, LocStepX P LX := by
theorem lwEngine_exists (K : ℤ) (Γ : PGraph (Fin 2)) (hN : Γ.g.Normal) :
    ∃ oX eX : List ((ℕ × ℕ) × PGraph (Fin 2)), ∀ (m : ℂ) (t0 : ℕ × ℕ),
$ sed -n 702,706p RBM3D/Graph/LWEngine.lean
    have hgood := lvl1_step_good (hLX.eval 1 0) hN
    have hch : ∀ r ∈ LX, Lvl1Lt (Lvl1Mu K r.2) (Lvl1Mu K Γ) ∧ r.2.g.Normal := by
      intro r hr
      have := hgood (lwEvX 1 (lwEngine_shift 0 r)) (List.mem_map_of_mem (List.mem_map_of_mem hr))
      exact ⟨lvl1_mu_lt hlt this.2, this.1⟩
$ sed -n 1462p RBM3D/Graph/LocalRegular.lean ; sed -n 3290,3291p RBM3D/Graph/LWLvl1.lean
theorem fxyPowGraph_normal (p : ℕ) : (fxyPowGraph p).Normal := by
theorem lvl1_step_good {m : ℂ} {P : PGraph E} {outs : List (PGraph E)} (hst : LocStep m P outs) (hN : P.g.Normal) :
    ∀ Q ∈ outs, Q.g.Normal ∧ Lvl1Good P.g Q.g := by
```
- **Truth of the amended pin.** For `P.g.Normal` and each constructor, `lvl1_step_identity` (`LWLvl1.lean:3591-3600`) gives the unweighted identity; the `weight` case needs no `hN`, the `edge`/`gg` cases use `hN` exactly for `lvl1_oe1xT1_zero` / `lvl1_oe2xR1_zero`, whose proof is zero term by term (above), so the weighted twin holds for every real `W`. `Molecular`/`ExtOK` do not read `Normal` (C2). The 1a0 counterexample (non-normal `P`) is excluded by the new hypothesis, and `P*` of (D) is its normal variant.
- **Suppliers.** Root: `fxyPowGraph_normal p : (fxyPowGraph p).Normal` (check file line 32 `#check`; `example` at `LocalRegular.lean:2086`; `lwEngine_assemble` uses it at `LWEngine.lean:729`). Child: in `lwEngine_exists` (hypothesis `hN : Γ.g.Normal`, :667) the step lemma output `hgood := lvl1_step_good (hLX.eval 1 0) hN` (:702) yields `r.2.g.Normal` for every `r ∈ LX` (`hch`, :703-706), which is the hypothesis `hN` of the recursive call `ih r.2 … (hch r hr).2`. So `lw_localregularXP : LWEngineProv` (statement unchanged, probe 164-171) calls the amended step lemma only at normal graphs. `LWEngineProv` itself carries no `Normal` hypothesis because its start graph is `fxyPowGraph p`.
- Other pin parts unchanged by Amend 1: `ProvOut.Molecular`, `WExp.comp`, `CoverBy.comp` (compiled in the probe, T2348 prove report); consumers (R3) call the step lemma only through the engine recursion (Amend 1).

### Verdicts

| target | verdict | reason |
|---|---|---|
| copied probe declarations (`valW` … `ProvOutX.Cover`, `mkProv`, `stepOuts`, `LWEngineProv`, `lwEngineProv_imp_localregularX`, `LWfD`, `LWfD_union`) with C3 | PASS | true statements; proved ones compiled in the probe; `LWEngineProv` true: normal start graph, leaves carry `id`, steps carry `π`, `Cover` by `CoverBy.comp` |
| `lwProv_bridge` (C1) | PASS (mathematics; compilation is 1b) | block factorisation, real weight on `β_k`; verified numerically at `p = 2, 4`; hypothesis `Even p` |
| `Molecular` for `weight` (C2) and all constructors, initial `Cover` | PASS (mathematics) | uniform `owxExt` + merge argument; exhaustive and random checks, negative control fails as it must |
| `locStepXProv_holds : LocStepXProv` (amended, with `P.g.Normal →`) | PASS | hypothesis set satisfiable (D); identity true on normal inputs; suppliers (iii) |
| `lw_localregularXP : LWEngineProv` | PASS | recursion supplies normality at every step (iii) |

Overall verdict: **PASS**. C1 and C2 close; the Amend 1 repair removes the only defect found by 1a0.


## (a′) Preflight corrections — Fri Oct  9 19:58:03 UTC 2026

- The verdict row "`locStepXProv_holds : LocStepXProv` | PASS" and (iii) "Truth of the amended pin" argue the identity output by output. The pinned statement indexes the maps by the **value** `r ∈ LX` (`π : ∀ r ∈ LX, …`, `RBM3D/Graph/LWProv.lean:171-175`), and `stepOuts` reads `π r.1 r.2` at every position of `LX` (`:164-166`): two positions with the same value `(tag, Q)` must carry the same map. (a) does not discuss this.
- Effect: the per-position mathematics of (a) stands (proved as `lwProv_stepPos`); for the pinned Lean statement the verdict changes from PASS to **BLOCKED** (analysis in (b), repair in (d)). Every other row of (a) stands (C1, C2, C3, the bridge, `lw_localregularXP`: compiled).

## (b) Script output (repair stage, Amend 2)

Repairer round under `docs/tickets/T2358-amend-2.md` (decision R-a), model claude-opus-5-5; first `date -u` of this round: Fri Oct  9 20:44:03 UTC 2026. All commands run in `/Users/junyin/Lean_proof/RBM3D-wt/T2358` (branch `t/T2358`); `F=RBM3D/Graph/LWProv.lean`; `S` = the `T2358/` subdirectory of the scratchpad. Line numbers are those of `F` at 6d6ef4d. Sections (a) and (a′) above are unchanged.

### Branch, build, hygiene, size
```
$ date -u; git log --oneline -1; git status --short | wc -l; git diff --stat main...t/T2358 | tail -1; wc -l $F
Fri Oct  9 20:50:10 UTC 2026
6d6ef4d T2358: Amend 2 (R-a): drop value-indexed LocStepXProv and its section-9 scaffolding; docstrings name lwProv_locStepXProvPos_holds
       0
 1 file changed, 1820 insertions(+)
    1820 RBM3D/Graph/LWProv.lean
$ lake build RBM3D.Graph.LWProv > $S/build.log 2>&1; echo exit=$?; tail -2 $S/build.log; grep -c "LWProv.lean" $S/build.log   # 20:44:48-20:45:02 UTC
exit=0
✔ [3895/3895] Built RBM3D.Graph.LWProv (11s)
Build completed successfully (3895 jobs).
0
$ grep -nE "sorry|admit|native_decide|^axiom|^\s*axiom " $F; echo grep_exit=$?
grep_exit=1
```

### Amend 2 edit check (`git diff da182dc..HEAD -- F`)
```
$ git diff --stat da182dc -- $F | tail -1; git diff -U0 da182dc -- $F | grep "^@@" | cut -d@ -f3
 1 file changed, 10 insertions(+), 80 deletions(-)
 -13 +13 
 -17,4 +17,3 
 -168,9 +166,0 
 -1520 +1510 
 -1795 +1785 
 -1799,61 +1789 
 -1879,3 +1809,3 
$ diff <(git show da182dc:$F | python3 -I $S/nodoc.py) <(python3 -I $S/nodoc.py < $F) | grep -E "^[0-9]"   # nodoc.py drops /-- -/, /-! -/ and blank lines
103,107d102
1459,1508d1453
$ diff <(git show da182dc:$F | python3 -I $S/nodoc.py) <(python3 -I $S/nodoc.py < $F) | grep -c "^>"
0
$ diff <(git show da182dc:$F | python3 -I $S/nodoc.py) <(python3 -I $S/nodoc.py < $F) | grep -E "^< (private )?(def|theorem|lemma) " | cut -c1-90
< def LocStepXProv : Prop :=
< private def lwProv_Functional {P : PGraph (Fin 2)} (ps : List (ProvOutX P)) : Prop :=
< private theorem lwProv_pin_of_functional (P : PGraph (Fin 2)) (ps : List (ProvOutX P)) (
< private def lwProv_StepFunctional : Prop :=
< private theorem lwProv_locStepXProv_of_functional (hfun : lwProv_StepFunctional) : LocSt
$ grep -n "LocStepXProv\b\|LocStepXProv\`\|lwProv_Functional\|lwProv_StepFunctional\|pin_of_functional\|locStepXProv_of_functional\|locStepXProv_holds" $F; echo grep_exit=$?
grep_exit=1
```
Hunks: module doc (13, 17-20); `LocStepXProv` with its docstring (168-176); docstring of `lwProv_stepPos` (1520); section 9 heading (1795); the four section-9 declarations and the docstring of `lwProv_LocStepXProvPos` (1799-1859); docstring of the `lwProv_wildGraph` example (1879-1881). Outside doc comments the diff has no added line; the removed code lines are exactly the five declarations named by Amend 2 item 1.

### Axioms and existence (`lake env lean $S/axioms.lean`, exit 0)
```
'RBM.Graph.lwProv_bridge' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.lw_localregularXP' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.lwProv_locStepXProvPos_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.lwProv_stepPos' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.lwEngineProv_imp_localregularX' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.WExp.prod' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.WExp.comp' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.WExp.refl' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.ProvOut.Molecular.comp' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.CoverBy.comp' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.LWfD_union' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.valW_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.pvalW_one' depends on axioms: [propext, Classical.choice, Quot.sound]
lwProv_locStepXProvPos_holds : lwProv_LocStepXProvPos
RBM.Graph.LocStepXProv exists: false
RBM.Graph.locStepXProv_holds exists: false
$ lake env lean $S/deps2.lean     # constants reachable from type and proof term (closure over getUsedConstants)
closure size 53227
lw_localregularXP closure contains lwProv_exists: true
lw_localregularXP closure contains lwProv_stepPos: true
lw_localregularXP closure contains lwProv_locStepXProvPos_holds: false
lw_localregularXP closure contains lwProv_fxyCover: true
lwProv_stepPos closure contains LocStepXProv: false
```
`lw_localregularXP` uses `lwProv_stepPos`, whose statement is `lwProv_LocStepXProvPos` unfolded; `lwProv_locStepXProvPos_holds` is the one-line wrapper `fun P LX h hN => lwProv_stepPos P LX h hN` (F:1797).

### Registry pre-check (temporary scratch file, not in the repo)
```
$ cat $S/registry.lean; lake env lean $S/registry.lean > $S/registry.out 2>&1; echo exit=$?    # 20:45:29-20:46:15 UTC
import RBM3D
import RBM3D.Graph.LWProv
#assert_rbm_axioms
exit=0
$ wc -l < $S/registry.out; grep -n "axiom audit\|premises found" $S/registry.out
     259
1:axiom audit: 10627 theorems, 3124 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
134:premises found by scanning: 133 (borrowed 1, owed 71, structural 42, refuted 6, superseded 13).
```
The da182dc run (previous (b), and audit §3) gave `10627 theorems, 3125 definitions` and 133 premises; the main baseline without `F` is `10524 theorems, 3078 definitions`, 133 premises.

### Targets (statements extracted from `F` by script; `stmt.sh` prints a declaration up to its first `:=`)
```
$ for n in lwProv_bridge lw_localregularXP lwProv_LocStepXProvPos lwProv_locStepXProvPos_holds; do $S/stmt.sh $F $n; done; sed -n 1792,1795p $F
233: theorem lwProv_bridge {d : ℕ} (sz : Sizes d) {p : ℕ} (hp : Even p) (n : ℕ) (E t : ℝ) (ω : sz.SeqΩ)
234:     (D : Finset (Zd d (sz.L n))) (x y : Idx d (sz.L n) (sz.W n)) :
235:     pvalW (fxyPowGraph p).pack (lwMoment_D sz n E t ω)
236:       (fun ℓ => ∏ k : Fin p, if STblk sz n (ℓ (Sum.inr (localReg_fxyBeta k))) ∈ D then 1 else 0) ![x, y] =
237:       ((‖LWfD sz n E t ω D x y‖ ^ p : ℝ) : ℂ) := by
1680: theorem lw_localregularXP : LWEngineProv := by
1791: def lwProv_LocStepXProvPos : Prop :=
1797: theorem lwProv_locStepXProvPos_holds : lwProv_LocStepXProvPos := fun P LX h hN => lwProv_stepPos P LX h hN
  ∀ (P : PGraph (Fin 2)) (LX : List ((ℕ × ℕ) × PGraph (Fin 2))), LocStepX P LX → P.g.Normal →
    ∃ ps : List (ProvOutX P), ps.map (fun o => (o.tag, o.Q)) = LX ∧
      (∀ o ∈ ps, o.ExtOK ∧ (⟨o.Q, o.π⟩ : ProvOut P).Molecular) ∧ ∀ (m : ℂ) (t0 : ℕ × ℕ),
        WExp m (lwEvX m (t0, P)) (ps.map fun o => mkProv m t0 P (o.tag, o.Q) o.π)
```
The names and statements of `lwProv_LocStepXProvPos` / `lwProv_locStepXProvPos_holds` are those of da182dc F:1861-1867 (the doc-stripped diff above has no added line).

### Compiled nonempty instances (sections 8 and 9 of `F`; built by the `lake build` above)
```
$ grep -n "^example\|^theorem ProvOut.molecular_id" $F | cut -d: -f1 | tr '\n' ' '
1713 1716 1722 1726 1728 1733 1734 1738 1753 1767 1774 1780 1800 1812
$ sed -n 1800p $F
example := lwProv_locStepXProvPos_holds p2Graph.pack _ LWEngineInst.lwEngine_inst_stepX (fxyPowGraph_normal 2)
```
These are the da182dc instances shifted by 10 lines (1723 → 1713, …, 1870 → 1800, 1882 → 1812). They are unchanged outside doc comments (edit check above). 1713 `ProvOut.molecular_id`; 1716 `pvalW_one` at `fxyPowGraph 2`; 1722/1726/1728 `WExp.refl` (inside `WExp.comp`), `ProvOut.Molecular.comp`, `CoverBy.comp` at `fxyPowGraph 2`; 1733 `lw_localregularXP 2 (1 / 4) (by norm_num) 1 3 10`; 1734 `lwEngineProv_imp_localregularX` at the same data; 1738 `WExp.prod` at `lwWxInstSz`, `n = 0`, `m = mE 0`, `p = 2`, every deterministic hypothesis discharged; 1753/1767 `lwProv_bridge` at `p = 2`, `D = univ` and `D = {0}`; 1774 `LWfD_union` at `{0}`, `{1}`; 1780 `lwProv_stepPos` and 1800 `lwProv_locStepXProvPos_holds` at the merged `LocStepX.weight` instance on `p2Graph = fxyPowGraph 2`, with normality from `fxyPowGraph_normal 2`; 1812 the `lwProv_wildGraph` remark.

### Probe diff (ticket C3, Amend 1, Amend 2)
```
$ git show t/T2348:RBM3D/Probe/T2348Pins.lean > $S/probe.lean     # t/T2348 = 9f3bd75 (da182dc round)
$ diff <(sed -n "29,185p;291,310p" $S/probe.lean | $S/nodoc.sh | grep -v "^$") <(sed -n "39,210p" $F | $S/nodoc.sh | grep -v "^$") > $S/probediff.txt; grep -E "^[0-9]" $S/probediff.txt
24,28d23
31c26,29
44c42
48,49c46,47
51c49
55c53,56
59c60,61
81,85d82
$ sed -n '/^81,85d82/,$p' $S/probediff.txt
81,85d82
< def LocStepXProv : Prop :=
<   ∀ (P : PGraph (Fin 2)) (LX : List ((ℕ × ℕ) × PGraph (Fin 2))), LocStepX P LX →
<     ∃ π : ∀ r ∈ LX, P.E' ⊕ P.I' → r.2.E' ⊕ r.2.I', ∀ (m : ℂ) (t0 : ℕ × ℕ),
<       (∀ r (hr : r ∈ LX), (mkProv m t0 P r (π r hr)).ExtOK ∧ (mkProv m t0 P r (π r hr)).Molecular) ∧
<       WExp m (lwEvX m (t0, P)) (stepOuts m t0 P LX π)
```
Hunks 24,28d23 through 59c60,61 are the C3 hunks of the da182dc run, with the same line numbers and the same text (`LWExpData` inline in `WExp` and `WExp.prod`, with the matching proof lines). The da182dc hunk `82c84` (Amend 1: `P.g.Normal →`) is now the deletion `81,85d82` of the probe's `LocStepXProv` (Amend 2).

### Name-clash scan (no ports: `F` copies nothing from RBM1D or RBM2D)
```
$ python3 -I $S/names.py | head -2     # every public declaration of F; `grep -rwn --include=*.lean <name> RBM3D`, hits outside F and Probe/
new public declarations: 118
clashing names: 0
```
No name was added; the public count drops from 119 to 118 (`LocStepXProv` removed).

### Narrative

1. Scope: Amend 2 edits 1-3 only, in the sole writable file `F`, in one commit 6d6ef4d on `t/T2358` (parent da182dc).
2. Edit 1: deleted `LocStepXProv` (old F:168-175 with its docstring) and the section-9 declarations `lwProv_Functional`,
   `lwProv_pin_of_functional`, `lwProv_StepFunctional`, `lwProv_locStepXProv_of_functional` (old F:1799-1858 with docstrings).
3. Edit 2: kept `lwProv_LocStepXProvPos`, `lwProv_locStepXProvPos_holds`, its instance, `lwProv_wildGraph` and its `example`
   with their code unchanged. The docstring of `lwProv_LocStepXProvPos` now reads "the position-indexed provenance step
   (Amend 2)", and the docstring of the `lwProv_wildGraph` example is now an R-b remark. No other docstring of these named a deleted name.
   Two further doc comments named the deleted `LocStepXProv`, and their text was changed the same way: the section 9 heading
   (F:1785) and the docstring of `lwProv_stepPos` (F:1510). Both are doc-only edits, which the edit check above shows.
4. Edit 3: the module docstring (F:10-20) names `lwProv_locStepXProvPos_holds` as the pinned step lemma (Amend 2) and says
   that `lw_localregularXP` is proved from `lwProv_stepPos` (closure check above).
5. Acceptance (Amend 2): module build exit 0; registry pre-check exit 0 with premise scan 133; standard axioms for every target;
   hygiene grep empty; 1820 ≤ 1950 lines.
6. Verdict: **PASS**. Every target of the ticket as amended (Amend 1, Amend 2) is built, has standard axioms and has a compiled
   nonempty instance: the copied probe declarations (C3, Amend 1, minus `LocStepXProv` by Amend 2), `LWfD`, `LWfD_union`,
   `lwProv_bridge`, `lwProv_locStepXProvPos_holds : lwProv_LocStepXProvPos`, and `lw_localregularXP : LWEngineProv`.

## (c) Verified library names used

These are unchanged from the da182dc round (`lake env lean $S/r2/mathlib_names2.lean`, exit 0, 161 names resolving to Mathlib, Init, Std or Batteries). Four of them were used only in the deleted section-9 code: `grep -c` in `F` now gives 0 for `cast_heq`, `eq_of_heq`, `attach_map` and `attach_map_val`. The lemmas still used, several per line:

`Bool.{and_eq_true, cond_false, cond_true, or_eq_true}`, `Classical.{choose, choose_spec}`, `Complex.ofReal_prod`, `Filter.Eventually.of_forall`, `Fin.ext`, `Finset.{disjoint_left, disjoint_singleton, mem_image, mem_univ, mul_sum, prod_congr, prod_mul_distrib, subset_univ, sum_add_distrib, sum_congr, sum_eq_zero, sum_image, sum_subset}`, `Function.{comp_apply, comp_def}`, `InvImage.wf`, `List.{any_eq_true, append_nil, flatMap_congr, map_append, map_congr_left, map_cons, map_flatMap, map_map, map_nil, mem_append, mem_append_left, mem_append_right, mem_cons, mem_cons_of_mem, mem_cons_self, mem_filter, mem_finRange, mem_flatMap, mem_map, mem_map_of_mem, mem_singleton, nil_append, not_mem_nil, prod_cons, prod_eq_zero, sum_append, sum_cons, sum_eq_zero, sum_map_add, sum_map_mul_left, sum_map_mul_right, sum_nil}`, `Matrix.{diagonal_apply_eq, of_apply}`, `MeasureTheory.{integrable_finsetSum, integrable_zero, integral_add, integral_congr_ae, integral_const_mul, integral_finsetSum, integral_zero}`, `Pi.single`, `Prod.{fst_add, snd_add, mk_zero_zero}`, `Quotient.{exact, exists_rep, sound}`, `Relation.{EqvGen.rel, ReflTransGen.lift', ReflTransGen.single}`, `SimpleGraph.{Adj.reachable, ConnectedComponent.eq, ConnectedComponent.ind, Reachable.refl, reachable_iff_reflTransGen}`, `Subtype.ext`, `Sum.{elim_inl, elim_inr, inr_injective}`, `add_assoc`, `add_zero`, `and_self`, `congrArg`, `congrFun`, `decide_eq_true_eq`, `funext`, `ite_true`, `map_add`, `map_mul`, `map_sum`, `mul_add`, `mul_assoc`, `MulZeroClass.mul_zero` (written `mul_zero`), `one_mul`, `or_false`, `pow_add`, `pow_succ`, `star_mul'`, `zero_add`.

Verified absent (da182dc round, `.lake/packages/mathlib`): `grep -rnE "Quot(ient)? [^ ]+ = Quot(ient)? [^ ]+" Mathlib | wc -l` gives 0; no Mathlib lemma states that two `Quot` types are equal (19 hits for `Quot*inj|type_eq|eq_of_eq`, all about injectivity of maps).

## (d) Open issues and paper-delta candidates

1. Amend 2 (R-a) replaces the target `locStepXProv_holds : LocStepXProv` with `lwProv_locStepXProvPos_holds : lwProv_LocStepXProvPos` (F:1791-1797, instance F:1800). The value-indexed form is no longer in `F` (`env.contains` false for both names). (R-b) stays an analysis only: see the `lwProv_wildGraph` remark (F:1809-1815) and the da182dc report.
2. Declarations outside the ticket's list (all prefixed `lwProv_`, CLAUDE.md §3 (E)) are the helpers, `lwProv_wildGraph`, `lwProv_stepPos` and `lwProv_exists`. The registry premise scan gives 133, as before the repair.
3. Paper-delta candidates: none new. The statements of `F` are the probe's, with C3 (inline data), Amend 1 (`P.g.Normal`, supplied by the root `fxyPowGraph_normal` and by `lwProv_exists` for the children) and Amend 2 (the position-indexed step). All three are Lean encodings of the provenance layer and change no paper statement (Amend 2; audit §7).
