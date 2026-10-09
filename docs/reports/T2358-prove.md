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

## (b) Script output

All commands below were run in this round (escalation round, DECISIONS §94) in `/Users/junyin/Lean_proof/RBM3D-wt/T2358` (branch `t/T2358`); `F=RBM3D/Graph/LWProv.lean`; `S` = the `T2358/` subdirectory of the scratchpad (helper scripts of the earlier round), this round's outputs in `S/r2/`. Line numbers are those of `F` at da182dc.

### Branch, build, hygiene, axioms
```
$ date -u; git log --oneline -1; git status --short | wc -l; wc -l $F; git diff --stat main...t/T2358 | tail -2
Fri Oct  9 20:17:37 UTC 2026
da182dc T2358: wrap the module doc (no long-line warnings)
       0
    1890 RBM3D/Graph/LWProv.lean
 RBM3D/Graph/LWProv.lean | 1890 +++++++++++++++++++++++++++++++++++++++++++++++
 1 file changed, 1890 insertions(+)
$ lake build RBM3D.Graph.LWProv > $S/r2/build.log 2>&1; echo exit=$?; tail -1 $S/r2/build.log      # 20:12:12-20:12:14 UTC
exit=0
Build completed successfully (3895 jobs).
$ lake build > $S/r2/buildfull.log 2>&1; cat $S/r2/buildfull.exit; tail -1 $S/r2/buildfull.log     # 20:13:27-20:13:33 UTC; RBM3D.lean imports F only at the hub merge
exit=0
Build completed successfully (4170 jobs).
$ grep -c "sorry\|admit\|native_decide" $F; grep -c "^axiom " $F
0
0
$ lake env lean $S/r2/axioms4.lean | sed "s/.*depends on axioms: //" | sort | uniq -c
  20 [propext, Classical.choice, Quot.sound]
```
`axioms4.lean` is `import RBM3D.Graph.LWProv` and `#print axioms` of `lwProv_bridge`, `lw_localregularXP`, `lwProv_stepPos`, `lwProv_locStepXProvPos_holds`, `lwProv_exists`, `lwProv_fxyCover`, `lwProv_{weightOuts,edgeOuts,ggOuts}_mol`, `lwProv_valW_partX`, `WExp.{prod,comp,refl}`, `ProvOut.Molecular.comp`, `CoverBy.comp`, `lwEngineProv_imp_localregularX`, `LWfD_union`, `valW_one`, `pvalW_one`, `LWProvInst.ProvOut.molecular_id` (all in `RBM.Graph`).
```
$ lake env lean $S/r2/deps2.lean     # constants reachable from type and proof term (closure over getUsedConstants)
closure size 53227
lw_localregularXP closure contains lwProv_exists: true
lw_localregularXP closure contains lwProv_stepPos: true
lw_localregularXP closure contains LocStepXProv: false
lw_localregularXP closure contains lwProv_fxyCover: true
lwProv_stepPos closure contains LocStepXProv: false
```

### Targets (statements extracted from `F` by script)
```
$ $S/stmt.sh $F lwProv_bridge; $S/stmt.sh $F lw_localregularXP; sed -n 171,175p $F    # stmt.sh: the declaration up to its first ":="
243: theorem lwProv_bridge {d : ℕ} (sz : Sizes d) {p : ℕ} (hp : Even p) (n : ℕ) (E t : ℝ) (ω : sz.SeqΩ)
244:     (D : Finset (Zd d (sz.L n))) (x y : Idx d (sz.L n) (sz.W n)) :
245:     pvalW (fxyPowGraph p).pack (lwMoment_D sz n E t ω)
246:       (fun ℓ => ∏ k : Fin p, if STblk sz n (ℓ (Sum.inr (localReg_fxyBeta k))) ∈ D then 1 else 0) ![x, y] =
247:       ((‖LWfD sz n E t ω D x y‖ ^ p : ℝ) : ℂ) := by
1690: theorem lw_localregularXP : LWEngineProv := by
def LocStepXProv : Prop :=
  ∀ (P : PGraph (Fin 2)) (LX : List ((ℕ × ℕ) × PGraph (Fin 2))), LocStepX P LX → P.g.Normal →
    ∃ π : ∀ r ∈ LX, P.E' ⊕ P.I' → r.2.E' ⊕ r.2.I', ∀ (m : ℂ) (t0 : ℕ × ℕ),
      (∀ r (hr : r ∈ LX), (mkProv m t0 P r (π r hr)).ExtOK ∧ (mkProv m t0 P r (π r hr)).Molecular) ∧
      WExp m (lwEvX m (t0, P)) (stepOuts m t0 P LX π)
$ grep -n "theorem locStepXProv_holds" $F; echo "grep exit=$?"
grep exit=1
```
The other copied declarations are the probe's text (probe diff below); `lwProv_bridge` assumes `Even p`, as its twin `lwMoment_fxyPow_val` (`LWMoment.lean:1748`).

### Compiled nonempty instances (sections 8 and 9 of `F`; built by the `lake build` above)
```
$ grep -n "^example\|^theorem ProvOut.molecular_id\|^theorem lwProv_locStepXProvPos_holds" $F | cut -d: -f1 | tr '\n' ' '
1723 1726 1732 1736 1738 1743 1744 1748 1763 1777 1784 1790 1867 1870 1882
```
1723 `LWProvInst.ProvOut.molecular_id` (ticket instance 1); 1726 `pvalW_one` at `fxyPowGraph 2`, data `lwSampleData lwWxInstSz 0 …` at the sample `0`; 1732 `WExp.refl` at `fxyPowGraph 2` (ticket instance 2) inside `WExp.comp`; 1736 `ProvOut.Molecular.comp`; 1738 `CoverBy.comp` from `lwProv_fxyCover 2`; 1743 `lw_localregularXP 2 (1 / 4) (by norm_num) 1 3 10` (its only hypothesis `0 < c` discharged); 1744 `lwEngineProv_imp_localregularX` at the same data; 1748 `WExp.prod` at `lwWxInstSz`, `n = 0`, `m = mE 0`, `p = 2`, weights `w_k(x) = if x = 0 then 1 else 1/2`, every deterministic hypothesis discharged (merged lemmas, `norm_num`), its `WExp` input taken from `lw_localregularXP`; 1763 `lwProv_bridge` at `p = 2`, `D = univ`, rewritten to the merged value `‖LWf …‖ ^ 2` (ticket instance 3); 1777 `lwProv_bridge` at `p = 2`, `D = {0}`, every `ω`; 1784 `LWfD_union` at `{0}`, `{1}`; 1790 `lwProv_stepPos` and 1870 `lwProv_locStepXProvPos_holds` (theorem at 1867) at the merged `LocStepX.weight` instance `LWEngineInst.lwEngine_inst_stepX` on `p2Graph`, normality `fxyPowGraph_normal 2`; 1882 the witness `lwProv_wildGraph` (narrative 4). No instance of `locStepXProv_holds`: the theorem does not exist.

### Probe diff (ticket C3 and Amend 1)
```
$ git show t/T2348:RBM3D/Probe/T2348Pins.lean > $S/r2/probe.lean; git log -1 --format=%h t/T2348
9f3bd75
$ diff <(sed -n "29,185p;291,310p" $S/r2/probe.lean | $S/nodoc.sh | grep -v "^$") <(sed -n "39,220p" $F | $S/nodoc.sh | grep -v "^$")    # nodoc.sh drops doc comments
24,28d23
< def LWExpData {d : ℕ} (sz : Sizes d) (n : ℕ) (z : ℂ) (u : ℝ) (m : ℂ)
<     (Sp M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) : Prop :=
<   GaussIBP sz ∧ 0 < z.im ∧ 0 < u ∧ m ≠ 0 ∧ z + (u : ℂ) * m = -m⁻¹ ∧
<     (∀ i j, Sp i j - m ^ 2 * ∑ w, Sp i w * lwS sz n u w j = lwS sz n u i j) ∧ Spᵀ = Sp ∧
<     (∀ a, M a a = m) ∧ (∀ a b, a ≠ b → M a b = 0)
31c26,29
<     (Sp M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ), LWExpData sz n z u m Sp M →
---
>     (Sp M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ),
>     GaussIBP sz → 0 < z.im → 0 < u → m ≠ 0 → z + (u : ℂ) * m = -m⁻¹ →
>     (∀ i j, Sp i j - m ^ 2 * ∑ w, Sp i w * lwS sz n u w j = lwS sz n u i j) → Spᵀ = Sp →
>     (∀ a, M a a = m) → (∀ a b, a ≠ b → M a b = 0) →
44c42
<   intro d sz n z u Sp M _ W ℓe; simp
---
>   intro d sz n z u Sp M _ _ _ _ _ _ _ _ _ W ℓe; simp
48,49c46,47
<   intro d sz n z u Sp M hD W ℓe
<   rw [h Sp M hD W ℓe, lvl1_sum_flatMap]
---
>   intro d sz n z u Sp M hG hz hu hm0 hzm hSp hSpT hM hM0 W ℓe
>   rw [h Sp M hG hz hu hm0 hzm hSp hSpT hM hM0 W ℓe, lvl1_sum_flatMap]
51c49
<   rw [h' o ho Sp M hD (fun ℓ => W (ℓ ∘ o.π)) ℓe, List.map_map]
---
>   rw [h' o ho Sp M hG hz hu hm0 hzm hSp hSpT hM hM0 (fun ℓ => W (ℓ ∘ o.π)) ℓe, List.map_map]
55c53,56
<     (hD : LWExpData sz n z u m Sp M) (w : Fin p → Idx d (sz.L n) (sz.W n) → ℝ) (ℓe : Fin 2 → Idx d (sz.L n) (sz.W n)) :
---
>     (hG : GaussIBP sz) (hz : 0 < z.im) (hu : 0 < u) (hm0 : m ≠ 0) (hzm : z + (u : ℂ) * m = -m⁻¹)
>     (hSp : ∀ i j, Sp i j - m ^ 2 * ∑ w, Sp i w * lwS sz n u w j = lwS sz n u i j) (hSpT : Spᵀ = Sp)
>     (hM : ∀ a, M a a = m) (hM0 : ∀ a b, a ≠ b → M a b = 0)
>     (w : Fin p → Idx d (sz.L n) (sz.W n) → ℝ) (ℓe : Fin 2 → Idx d (sz.L n) (sz.W n)) :
59c60,61
<         (fun ℓ => ∏ k, w k (ℓ (o.π (Sum.inr (localReg_fxyBeta k))))) ℓe ∂(Sizes.seqP sz)).sum := h Sp M hD _ ℓe
---
>         (fun ℓ => ∏ k, w k (ℓ (o.π (Sum.inr (localReg_fxyBeta k))))) ℓe ∂(Sizes.seqP sz)).sum :=
>   h Sp M hG hz hu hm0 hzm hSp hSpT hM hM0 _ ℓe
82c84
<   ∀ (P : PGraph (Fin 2)) (LX : List ((ℕ × ℕ) × PGraph (Fin 2))), LocStepX P LX →
---
>   ∀ (P : PGraph (Fin 2)) (LX : List ((ℕ × ℕ) × PGraph (Fin 2))), LocStepX P LX → P.g.Normal →
```

### Registry pre-check (temporary scratch file, not in the repo; no new premise)
```
$ cat $S/r2/registry.lean; lake env lean $S/r2/registry.lean > $S/r2/registry.out 2>&1; echo exit=$?     # 20:14:11-20:15:01 UTC
import RBM3D
import RBM3D.Graph.LWProv
#assert_rbm_axioms
exit=0
$ cd $S/r2; sed -n "4005,\$p" buildfull.log | sed "s/^info: RBM3D.lean:402:0: //" | grep -v "^Build completed" > baseline.txt   # the audit printed by the full build above (without F)
$ diff baseline.txt registry.out; wc -l baseline.txt registry.out | head -2; grep -n "premises found" registry.out
1c1
< axiom audit: 10524 theorems, 3078 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
---
> axiom audit: 10627 theorems, 3125 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
     259 baseline.txt
     259 registry.out
134:premises found by scanning: 133 (borrowed 1, owed 71, structural 42, refuted 6, superseded 13).
```

### Name-clash scan (no ports: `F` copies nothing from RBM1D or RBM2D)
```
$ python3 -I $S/names.py | head -2     # every public declaration of F; `grep -rwn --include=*.lean <name> RBM3D`, hits outside F and Probe/
new public declarations: 119
clashing names: 0
```
The public names without the prefix `lwProv_` (printed by `names.py`) are the 24 copied declarations of ticket section 1, `LWfD`, `LWfD_union`, `lw_localregularXP` and `ProvOut.molecular_id` (in `LWProvInst`).

### Narrative

1. This round: escalation (DECISIONS §94), model claude-opus-5-5. On entry (`date -u`: 20:02:46 UTC) `t/T2358` was at da182dc (committed
   19:53:21 UTC) with a clean worktree, `F` had 1890 lines, and line 1 of this report read `Prover model: claude-sonnet-5-5`; the Lean on the
   branch and section (a′) (19:58:03 UTC) predate this round. This round changed no Lean and made no commit; every output in (b), (c) was re-run.
2. Delivered (compiled, three standard axioms, premise scan 133 = baseline): the 24 copied declarations and `LWfD`, `LWfD_union` (probe diff:
   only C3 and Amend 1); `lwProv_bridge` (:243, C1); `Molecular` for the three constructors (`lwProv_weightOuts_mol` :520 is C2 for `weight`,
   `lwProv_edgeOuts_mol` :1382, `lwProv_ggOuts_mol` :1443) and the initial cover `lwProv_fxyCover` (:547, C2); the step lemma with positions
   `lwProv_stepPos` (:1521); `lw_localregularXP : LWEngineProv` (:1690), whose closure contains `lwProv_stepPos`, `lwProv_fxyCover`, and not `LocStepXProv`.
3. **Not delivered: `locStepXProv_holds : LocStepXProv`** (grep exit 1). The pin carries one map per *value* `r ∈ LX` (`π : ∀ r ∈ LX, …`, :173)
   and `stepOuts` reads it at every position of `LX` (:164-166). The construction carries one map per *position*: `lwProv_stepPos` returns
   `ps : List (ProvOutX P)` with `ps.map (fun o => (o.tag, o.Q)) = LX`. Two positions with equal values must share one map, and `WExp` must
   still hold for every real weight `W`. `lwProv_locStepXProv_of_functional` (:1843, private) derives the pin when equal values carry
   `HEq` maps (`lwProv_Functional`, :1800); it is a conditional adapter, not the target (CLAUDE.md §5.6).
4. Analysis (why I did not close the gap; not compiled except the witness). Each output of a block is `⟨u + o.tag, o.Q.lvl1Comp …, o.vm ∘ emb⟩`
   (`lwProv_blk`, :421-423) with `o.Q = lwProv_mergeQ Δ r.2` and `o.vm = Δ.vmap` for a partition term `Δ` (`lwProv_partX`, :398-400); the
   vertex types of `o.Q` are `Δ.ExtCls`, `Δ.IntCls` (:394-395), subtypes of `Quotient Δ.eqSetoid` (`RBM3D/Graph/LWVocab.lean:732-747`).
   There are 13 `lwProv_blk` families (4 in `lwProv_weightOuts`, 2 in `lwProv_edgeOuts`, 7 in `lwProv_ggOuts`). Two positions with one `Δ` and one `emb`
   carry the same map. Two positions with `Δ₁ ≠ Δ₂` and equal values give only an equality of types `Δ₁.IntCls = Δ₂.IntCls` (and of
   `ExtCls`) and `HEq` of the two graphs, while each map reads its own setoid (`vmapC`, `vmap`, `LWVocab.lean:763-769`); I found no Lean or Mathlib
   principle that recovers `Δ₁.eqSetoid = Δ₂.eqSetoid` from it ((c), greps). The remaining link between the two maps is the edge lists of
   the common output (`merge` maps each list by `vmap`, `LWVocab.lean:778-782`), and a vertex of `P` on no edge has none: `lwProv_wildGraph`
   (:1873, example :1882) is normal, has no waved edge, has an internal vertex `1` on no edge, and carries a `LocStepX.weight` step.
   A proof of the pin as stated needs, besides a comparison through the edge lists in each of the 13 families, an argument that the two
   weighted expectations agree where nothing compares the maps; I found none, and design §2 (`T2348-design.md`) states `π r` per element
   `r` without treating equal values. Following "on a real obstruction: stop writing", this round added no Lean.
5. Repairs for the dispatcher ((d) 1): (R-a) re-pin `LocStepXProv` position-indexed (compiled and proved, :1861-1870); (R-b) keep the
   value-indexed pin and add a waved-cover premise (analysis only). The consumers named in the ticket (`LWEngineProv`, `WExp.prod`,
   `ProvOutX.Cover`, `LWfD`, `lwProv_bridge`) do not mention `LocStepXProv`, so dropping the target is a third option.
6. Verdict: **BLOCKED** on `locStepXProv_holds` (pinned statement not proved; no hypothesis added, no signature changed); every other target
   is built. The C1/C2 stop conditions did not fire (C1 and C2 compiled, item 2); the size stop did not fire (1890 ≤ 1950).

## (c) Verified library names used

Resolved by `resolveGlobalConst` in the `open` context of `F` (`lake env lean $S/r2/mathlib_names2.lean`, exit 0: "161 names" resolve to Mathlib, Init, Std or Batteries; output identical to the earlier round's after stripping the message prefix). The lemmas among them, several per line:

`Bool.{and_eq_true, cond_false, cond_true, or_eq_true}`, `Classical.{choose, choose_spec}`, `Complex.ofReal_prod`, `Filter.Eventually.of_forall`, `Fin.ext`, `Finset.{disjoint_left, disjoint_singleton, mem_image, mem_univ, mul_sum, prod_congr, prod_mul_distrib, subset_univ, sum_add_distrib, sum_congr, sum_eq_zero, sum_image, sum_subset}`, `Function.{comp_apply, comp_def}`, `InvImage.wf`, `List.{any_eq_true, append_nil, attach_map, attach_map_val, flatMap_congr, map_append, map_congr_left, map_cons, map_flatMap, map_map, map_nil, mem_append, mem_append_left, mem_append_right, mem_cons, mem_cons_of_mem, mem_cons_self, mem_filter, mem_finRange, mem_flatMap, mem_map, mem_map_of_mem, mem_singleton, nil_append, not_mem_nil, prod_cons, prod_eq_zero, sum_append, sum_cons, sum_eq_zero, sum_map_add, sum_map_mul_left, sum_map_mul_right, sum_nil}`, `Matrix.{diagonal_apply_eq, of_apply}`, `MeasureTheory.{integrable_finsetSum, integrable_zero, integral_add, integral_congr_ae, integral_const_mul, integral_finsetSum, integral_zero}`, `Pi.single`, `Prod.{fst_add, snd_add, mk_zero_zero}`, `Quotient.{exact, exists_rep, sound}`, `Relation.{EqvGen.rel, ReflTransGen.lift', ReflTransGen.single}`, `SimpleGraph.{Adj.reachable, ConnectedComponent.eq, ConnectedComponent.ind, Reachable.refl, reachable_iff_reflTransGen}`, `Subtype.ext`, `Sum.{elim_inl, elim_inr, inr_injective}`, `cast_heq`, `eq_of_heq`, `add_assoc`, `add_zero`, `and_self`, `congrArg`, `congrFun`, `decide_eq_true_eq`, `funext`, `ite_true`, `map_add`, `map_mul`, `map_sum`, `mul_add`, `mul_assoc`, `MulZeroClass.mul_zero` (written `mul_zero`), `one_mul`, `or_false`, `pow_add`, `pow_succ`, `star_mul'`, `zero_add`.

Verified absent (in `.lake/packages/mathlib`): `grep -rnE "Quot(ient)? [^ ]+ = Quot(ient)? [^ ]+" Mathlib | wc -l` gives 0; `grep -rnE "(theorem|lemma) [A-Za-z_.]*Quot[A-Za-z_.]*(inj|type_eq|eq_of_eq)" Mathlib` gives 19 hits, all injectivity of maps between or out of quotients (e.g. `Quotient.out_injective`, `Mathlib/Data/Quot.lean:399`), none an equality of two `Quot` types.

## (d) Open issues and paper-delta candidates

1. **`locStepXProv_holds : LocStepXProv` is not delivered** (narrative 3-4); the dispatcher decides the pin. The compiled replacement is the position-indexed form (`F:1861-1865`, proved by `lwProv_stepPos` `F:1521` as `lwProv_locStepXProvPos_holds` `F:1867`, instance `F:1870`):
   `∀ (P : PGraph (Fin 2)) (LX : List ((ℕ × ℕ) × PGraph (Fin 2))), LocStepX P LX → P.g.Normal → ∃ ps : List (ProvOutX P), ps.map (fun o => (o.tag, o.Q)) = LX ∧ (∀ o ∈ ps, o.ExtOK ∧ (⟨o.Q, o.π⟩ : ProvOut P).Molecular) ∧ ∀ (m : ℂ) (t0 : ℕ × ℕ), WExp m (lwEvX m (t0, P)) (ps.map fun o => mkProv m t0 P (o.tag, o.Q) o.π)`.
   (R-b, analysis, not compiled) Keep the pin and add `∀ v : P.I', ∃ e ∈ P.g.waved, e.x = Sum.inr v ∨ e.y = Sum.inr v`. The engine's graphs have it (root: `α_k`, `β_k` on the waved edges `α_k–β_k`, used in `lwProv_fxyCover` :547-568; a step maps the input's waved edges and joins each new vertex by an appended waved edge, the `hw` premises at :480-491). With it every output has `o.Q.g.waved = P.g.waved.map (WEdge.map o.π) ++ new` (`owxExt`, `LWWeightExp.lean:458-464`; edgewise twist `LWSymm.lean:93-111, 171-184`; `withDots`, `merge`, `LWVocab.lean:778-782, 1091-1095`), so equal outputs have equal maps (external vertices by `ExtOK`): `lwProv_Functional`, then `lwProv_pin_of_functional` (:1804). This adds a premise (DECISIONS §163 (1), case (i)); (R-a) changes the conclusion.
2. Section 9 holds the private `lwProv_Functional`, `lwProv_StepFunctional`, `lwProv_pin_of_functional`, `lwProv_locStepXProv_of_functional` (CLAUDE.md §3 (E)); the Prop `lwProv_StepFunctional` is not a premise of any public theorem, and the registry premise scan is 133 before and after. Declarations outside the ticket's list (all prefixed `lwProv_`): the helpers, `lwProv_wildGraph` (witness), `lwProv_LocStepXProvPos`, `lwProv_locStepXProvPos_holds`, `lwProv_stepPos`, `lwProv_exists`.
3. Paper-delta candidates: none new. The statements of `F` are the probe's with C3 (inline data) and Amend 1 (`P.g.Normal`, supplied at every call: the root `fxyPowGraph_normal`, the children in `lwProv_exists` :1617-1621); both are Lean encodings, not changes of a paper statement.
