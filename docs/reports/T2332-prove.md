Prover model: claude-sonnet-5-5

## (a) Math preflight — Thu Oct  8 13:10:41 UTC 2026

Notation. `X = (ℕ×ℕ) × PGraph (Fin 2)`; `ev_m (j,j',P)` = `P` with `coeff := m^j m̄^j' * coeff` (`lwEvX`). `SP=/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/ec1cbe39-5957-4519-82e4-38af3363ddc4/scratchpad/T2332`.
Hand model (`$SP/nat.py`, `nat2.py`, `inst.py`; Python, no Lean): the 13 term generators `lwSymm*` (`LWSymm.lean:1313-1385`) built from `owxExt` (`LWWeightExp.lean:458`), `owxDE`, `oe1xD/P3-P6` (`LWEdgeExp.lean:606,1084-1115`), `oe2xR2,R4-R8` (`LWGGExp.lean:485-535`), twist = conj/transpose (`LWSymm.lean:100-175`), with the coefficient in an abstract *-algebra: `Num` (complex, the m-step) or `Mono(c0,a,b) = c0 m^a m̄^b` (the X-step). `dotted`/`merge` are not modelled: they keep `coeff` except the real sign `c.1 * coeff` (`LWVocab.lean:1095`, `:782`), modelled as two dot choices `±1`.

### (i) Exponent table
(A) Tag increments `(a,b)` of the generator coefficient (before the dot partition); for `(c,t)` with `c = true` (conj) every `(a,b)` becomes `(b,a)`:
| # | rule | constructor (13) | coefficient | tag `c=false` | tag `c=true` |
|---|---|---|---|---|---|
| 1-4 | weight (`lvl1WeightOuts0`, `LWLvl1.lean:3228`) | `owxET1` / `owxET2` / `owxET3` / `owxET4` | `m` / `m³` / `m` / `m³` | (1,0) / (3,0) / (1,0) / (3,0) | (0,1) / (0,3) / (0,1) / (0,3) |
| 5 | edge (`:3236`) | `Oe1xOwx` = `owxT1` on the frame | `m` | (1,0) | (0,1) |
| 6 | edge | `Oe1xDs`: `oe1xD`, `P5`, `P6` (one or two graphs by edge shape) | `m`, `m`, `m` | (1,0) | (0,1) |
| 6' | edge | `Oe1xDs`: `P3` (loop `Ḡ_xx → m̄`), `P4` (loop `G_xx → m`) | `m m̄`, `m m` | (1,1), (2,0) | (1,1), (0,2) |
| 7-13 | gg (`:3243`) | `R2` / `R3` / `R4` / `R5` / `R6` / `R7` / `R8` | `m³`/`m`/`m³`/`m`/`m³`/`m`/`m³` | (3,0)/(1,0)/(3,0)/(1,0)/(3,0)/(1,0)/(3,0) | swapped |
(B) Further tags and constants:
| # | quantity | value | constraint | slack |
|---|---|---|---|---|
| 14 | dot partition tag `partitionX` (`LWExpTerm5.lean:106`, `lwSplitLoopsX :91`) | `+(1,0)` per uncircled `σ=true` loop, `+(0,1)` per uncircled `σ=false` loop; real sign `±1` stays in the base coefficient | `partition m Γ = (partitionX Γ).map (scale (m^j m̄^j'))` (`lwExpTerm5_partition_eq`, private, `:299`; `partitionX_spec :310`) | exact |
| 15 | selection reads no coefficient (ii of ticket) | `LocStep` hypotheses `hp hx hv hwf hbad hnb hy hp1 hq1` use `solid`, `lvl1DegAt`, `lvl1ChargeAt`, `lwSymmTwistS` only; `Normal`, `LocStd`, `StdNeutral`, `Lvl1Mu`, counters: no `coeff` (script G below) | `ev_m` keeps edges and counters, so `Normal/LocStd/ord/Lvl1Mu` of `ev_m r` = those of `r.2` | exact |
| 16 | step input/output tags | output tag = input tag `+ (a,b)` of rows 1-13 `+` row 14; base coefficient `c0` unchanged (conj twice: `star(m^k * star(m^j m̄^j' c0)) = m^j m̄^j' m̄^k c0`) | naturality `lvl1…Outs0 m (ev_m r).g = (…OutsX r).map ev_m` | exact (script N: 2304 checks, 0 failures) |
| 17 | `nWS` (black waved edges) | start `fxyPowGraph p`: `p` (`LocalRegular.lean:1356`, `col=false`); every form appends waved edges only (`owxExt: waved := Γ.waved.map … ++ w`), `WEdge.conj/transpose` keep `col` (`LWSymm.lean:93-96`), `merge` maps `waved` (`LWVocab.lean:780`) | `p ≤ nWS(Q)` along `Lvl1Reach` (invariant by `lvl1_induction`) | `nWS - p ≥ 0` (script N last line) |
| 18 | cutoff `K` | `⌈(D + K0 nM + d (nV-nW)⁺)/c⌉`, independent of `m` (`lvl1Cutoff`, `LWLvl1.lean:3981`) | `c K ≥ D + K0 nM + d(nV-nW)⁺` for `lvl1_size_le` (errs `≤ W^{-D}`) | instance: `cK = 29` vs `29`, slack 0 (exact ceiling) |
| 19 | counters of `fxyPowGraph p` | `nS=3p, nW=p, nV=2p, nM=p, ord=p` (`LocalRegular.lean:33`; `ord = nS+2(nW-nV)`) | `2p ≤ ord` (outs), `3p ≤ ord` if `ext0 ≠ ext1` (conj 6, merged) | merged |
| 20 | measure for WF recursion | `Lvl1Mu K` = `((K-ord).toNat, nLoops, nS, nPairs)` of `r.2` (`LWLvl1.lean:3778`), no tags | falls along a good step (`lvl1_mu_lt`) | merged |
| 21 | parameter order | pin `∀ p c, 0<c → ∀ K0 d D, ∃ lists, ∀ m ≠ 0, …` | merged `lw_localregular p m c hc K0 d D` (`LocalRegular6d.lean:1110`) has `m` before `∃`; the pin moves `m` after | no `∀ᶠ`, no `n`-window |
§29 (one line each): (1) time domain `0≤s`, `t<1`: no `s,t` in the pin, n/a. (2) boundary `1-ilambda²/L²`: n/a. (3) `L^d ≤ W^{K0}`: written in conj 2 (verbatim from the merged theorem). (4) `∀ n` vs `∀ᶠ n`: no `n` outside the verbatim conj 4 (`∀ {n}` as merged). (5) per-time vs probability-inside: n/a (deterministic lists). (6) lower bound `W^{-d/2} ≤ Ψ` is a hypothesis of conj 2 (verbatim). (7) scale `(log W)^k` vs `W^τ`: n/a.

### (ii) Concrete nondegenerate instance
Command: `cd $SP && python3 -I inst.py` (instance `p=2`, `c=1/4`, `K0=3`, `d=3`, `D=17`; `m ∈ {i, (1+i)/2}`; `W=10^4`, `L=4`, `Ψ=10^-2`, `u=1/2`; `Sp` in an `N=8` model, solving `Sp - m² Sp S = S`; the weight step on `fxyPowGraph 2` with selected loop `Ǧ_{β0β0}` at `x = β0`, `(c,t)=(0,0)`):
```
p=2 c=0.25 K0=3 d=3 D=17.0: counters nS,nW,nV,nM=6,2,4,2; ord=2; cutoff K=116 (> ord: steps occur; start graph has circled loops, so not LocStd)
conj(2) window: True True L^d=64 <= W^K0=1000000000000: True W^(-d/2)=1.00e-06 <= Psi=0.01 <= W^(-c)=0.100: True
m=1j: m!=0 True, z=0.0000+0.5000j Im z>0 True, z+u*m=-1/m: True, |Sp-m^2 Sp S-S|max=5.6e-17, |Sp-Sp^T|max=1.4e-17, M=m*I diag/offdiag ok
m=(0.5+0.5j): m!=0 True, z=-1.2500+0.7500j Im z>0 True, z+u*m=-1/m: True, |Sp-m^2 Sp S-S|max=5.6e-17, |Sp-Sp^T|max=2.9e-17, M=m*I diag/offdiag ok
weight step on fxyPowGraph 2: outputs before dot-merge: 12 ; tagged list size (X carrier, partitionX model, 2 dot signs): 24
distinct tags (j,j'): [(1, 0), (3, 0)]
m=1j: |m-step coeff - tag evaluation|max over 24 outputs = 0.0e+00; sample coeffs: [1j, -1j, -1j]
m=(0.5+0.5j): |m-step coeff - tag evaluation|max over 24 outputs = 0.0e+00; sample coeffs: [(0.5+0.5j), (-0.5-0.5j), (-0.25+0.25j)]
black waved edges in every output >= p: True
```
Reading: one tagged list (24 entries after the weight step), evaluated at the two `m` by the same tags, equals the m-step outputs at both. The pin's own hypotheses are `0<c`, `m≠0`, and the conj-2/conj-4 antecedents inherited verbatim from the merged `lw_localregular`; `GaussIBP sz` holds for every `sz` (`gaussIBP`, `Green/IBPPoly.lean:305`). No external hypothesis is added, so no limit computation is owed; in the `N=8` model `Sp = (1-m²S)^{-1}S` solves the resolvent equation and is symmetric at both `m` (residuals above).

Script G (selection reads no `coeff`), `cd /Users/junyin/Lean_proof/RBM3D-wt/T2332/RBM3D/Graph`:
```
grep -c "coeff" LWLvl1.lean            -> 5   (first hits: 4099, 4117 ..., i.e. instance graphs only; none below line 4000)
sed -n 990,992p LWVocab.lean | grep -c coeff   -> 0   (LGraph.Normal)
sed -n 3196,3207p LWLvl1.lean | grep -c coeff  -> 0   (StdNeutral, LocStd)
LGraph.lvl1SolidAt/DegAt/ChargeAt :1540-1546, LocStep :3260-3275, Lvl1Mu :3778: no `coeff`
LWLvl1.lean:3095 PGraph.lvl1Comp: ext := Q.ext ∘ f, g := Q.g (no coefficient change)
```
Script N: `cd $SP && python3 -I nat2.py | sort -u` (13 forms x 4 twists x 3 `m` x 3 choices of the derivative edge: red out-edge / blue in-edge of `x` / other; input tag `(2,1)`, `c0 = 0.7-0.2i`, a non-circled loop included so both `m` and `m̄` splits fire):
```
(c,t)=(0,0) tag increments of the graph before partition: w.T1:(1,0) w.T2:(3,0) w.T3:(1,0) w.T4:(3,0) e.Owx:(1,0) e.Ds:(1,0) g.R2:(3,0) g.R3:(1,0) g.R4:(3,0) g.R5:(1,0) g.R6:(3,0) g.R7:(1,0) g.R8:(3,0)
(c,t)=(0,1) tag increments of the graph before partition: w.T1:(1,0) w.T2:(3,0) w.T3:(1,0) w.T4:(3,0) e.Owx:(1,0) e.Ds:(1,0) g.R2:(3,0) g.R3:(1,0) g.R4:(3,0) g.R5:(1,0) g.R6:(3,0) g.R7:(1,0) g.R8:(3,0)
(c,t)=(1,0) tag increments of the graph before partition: w.T1:(0,1) w.T2:(0,3) w.T3:(0,1) w.T4:(0,3) e.Owx:(0,1) e.Ds:(0,1) g.R2:(0,3) g.R3:(0,1) g.R4:(0,3) g.R5:(0,1) g.R6:(0,3) g.R7:(0,1) g.R8:(0,3)
(c,t)=(1,1) tag increments of the graph before partition: w.T1:(0,1) w.T2:(0,3) w.T3:(0,1) w.T4:(0,3) e.Owx:(0,1) e.Ds:(0,1) g.R2:(0,3) g.R3:(0,1) g.R4:(0,3) g.R5:(0,1) g.R6:(0,3) g.R7:(0,1) g.R8:(0,3)
checks (graph-by-graph, partition output coefficient vs ev_m of X output): 2304 failures: 0
nWS (black waved edges) non-decreasing for all 13 forms x 4 twists: True
```
(No `!` after a tag means the base coefficient equals `c0`.) Tags of the `Oe1xDs` graphs (`exec` of the `nat.py` header, `oe1xP5/P3/P6/P4/D` on `x`): `P5 (1, 0)`, `P3 (1, 1)`, `P6 (1, 0)`, `P4 (2, 0)`, `D (1, 0)`.

### Verdict per target
- `lwEvX`, `LWLocRegConcl` (definitions copied verbatim from the check file): PASS.
- `lw_localregularX` (naturality of all 13 constructors; selection independent of `coeff`; tags in rows 1-14; `nWS ≥ p` invariant; cutoff independent of `m`; nondegenerate instance above): PASS.
- Note for stage 1b (math, not Lean): a selection-data `Prop` `LocStepX` (constructor + `p,x,c,t,…`) can be obtained from `lvl1_exists_step 1 (ev_1 r)` by `cases`, because all constructor hypotheses read only `r.2.g.solid` (row 15); the X-recursion's `K` is `lvl1Cutoff c K0 d D (fxyPowGraph p).pack.g.counters` (row 18). `ev_m` of the root `((0,0), (fxyPowGraph p).pack)` is the root itself (coefficient `1`).

## (a′) Preflight corrections
None (see (d) 7).

## (b) Script output — Thu Oct  8 13:56:45 UTC 2026

```
$ date -u; git log --oneline -4; wc -l RBM3D/Graph/LWEngine.lean   (worktree /Users/junyin/Lean_proof/RBM3D-wt/T2332, branch t/T2332)
Thu Oct  8 13:53:34 UTC 2026
bd9d092 T2332: LWEngine instances for lw_nWS_ge and lwEvX
99a861a T2332: LWEngine (m-free lem:localregular): recursion, transport, lw_localregularX, instances
cd6456f T2332: LWEngine sections 1-5 (tag algebra, generator scaling, X-generators, naturality, LocStepX, nWS)
5b6221f Dispatcher V1: DECISIONS §148 (T2318 sign-off; LW-14f = T2334, BA-P4b = T2335, BA-P4c = T2336; T2332 check fix),
     937 RBM3D/Graph/LWEngine.lean

$ touch RBM3D/Graph/LWEngine.lean && lake build RBM3D.Graph.LWEngine 2>&1 | grep -E "LWEngine|error|Build completed"
Build completed successfully (3887 jobs).

$ lake env lean ax2.lean | sed 's/RBM.Graph.//'   (#print axioms; defs, targets, helpers, instances)
'lwEvX' : [propext, Classical.choice, Quot.sound]
'LWLocRegConcl' : [propext, Classical.choice, Quot.sound]
'lw_localregularX' : [propext, Classical.choice, Quot.sound]
'lw_nWS_ge' : [propext, Classical.choice, Quot.sound]
'lvl1WeightOuts0_nat' : [propext, Classical.choice, Quot.sound]
'lvl1EdgeOuts0_nat' : [propext, Classical.choice, Quot.sound]
'lvl1GGOuts0_nat' : [propext, Classical.choice, Quot.sound]
'LocStepX.eval' : [propext, Classical.choice, Quot.sound]
'LocStepX.eval_one' : [propext, Classical.choice, Quot.sound]
'lwEngine_exists' : [propext, Classical.choice, Quot.sound]
'lwEngine_exists_stepX' : [propext, Classical.choice, Quot.sound]
'lwEngine_locStep_nWS' : [propext, Classical.choice, Quot.sound]
'lwEngine_assemble' : [propext, Classical.choice, Quot.sound]
'LWEngineInst.lwEngine_inst_localregularX' : [propext, Classical.choice, Quot.sound]
'LWEngineInst.lwEngine_inst_two_m' : [propext, Classical.choice, Quot.sound]
'LWEngineInst.lwEngine_inst_stepX_edge_gg' : [propext, Classical.choice, Quot.sound]
'LWEngineInst.lwEngine_inst_step1_identity' : [propext, Classical.choice, Quot.sound]
'LWEngineInst.lwEngine_inst_nWS_ge' : [propext, Classical.choice, Quot.sound]
'LWEngineInst.lwEngine_inst_lwEvX' : [propext, Classical.choice, Quot.sound]

$ grep -c "sorry\|admit\|native_decide\|axiom" RBM3D/Graph/LWEngine.lean
0

$ git diff --stat main...t/T2332
 RBM3D/Graph/LWEngine.lean | 937 ++++++++++++++++++++++++++++++++++++++++++++++
 1 file changed, 937 insertions(+)

$ python3 -I clash.py   (new declaration names, plus LWEngine, LWEngineInst, vs RBM3D/ outside Probe/ and RBM3D.lean)
87 new names (incl. LWEngine, LWEngineInst); files scanned: 374 (RBM3D/ outside Probe/, RBM3D.lean); hits outside LWEngine.lean: 0

$ ports from ../RBM1D, ../RBM2D: none (no file there was read or copied), so no diff-stat

$ awk '/^theorem lw_localregularX/,/:= by$/' RBM3D/Graph/LWEngine.lean   (target; 'def lwEvX' and 'def LWLocRegConcl' are compared with the check file below)
theorem lw_localregularX :
    ∀ (p : ℕ) (c : ℝ), 0 < c → ∀ (K0 d : ℕ) (D : ℝ),
      ∃ outsX errsX : List ((ℕ × ℕ) × PGraph (Fin 2)), ∀ m : ℂ, m ≠ 0 →
        LWLocRegConcl p m c K0 d D (outsX.map (lwEvX m)) (errsX.map (lwEvX m)) ∧
        ∀ Q ∈ outsX.map (lwEvX m) ++ errsX.map (lwEvX m), p ≤ Q.g.waved.countP (fun e => !e.col) := by

$ python3 -I eqcheck.py   (whitespace-normalized equality with docs/tickets/checks/T2332-check.lean)
lwEvX text equal to check: True
LWLocRegConcl text equal to check: True
lw_localregularX statement text equal to T2332_lw_localregularX body: True
$ lake env lean chk.lean   (check imports + import RBM3D.Graph.LWEngine + the check's section 2 + example : RBM.Graph.T2332Check.T2332_lw_localregularX := RBM.Graph.lw_localregularX)
exit=0

$ awk '/^theorem lwEngine_inst_localregularX/,/:= by$/' RBM3D/Graph/LWEngine.lean   (the compiled nonempty instance of lw_localregularX, statement)
theorem lwEngine_inst_localregularX :
    ∃ outsX errsX : List ((ℕ × ℕ) × PGraph (Fin 2)),
      ((∀ Q ∈ outsX.map (lwEvX Complex.I), Q.g.LocStd ∧ 2 ≤ Q.g.scalingOrder) ∧
        (∀ Q ∈ errsX.map (lwEvX Complex.I),
          Q.g.scalingSize (((27 : ℕ) : ℝ) ^ (-(1 / 4 : ℝ))) 27 3 3 ≤ ((27 : ℕ) : ℝ) ^ (-(10 : ℝ))) ∧
        ∫ ω, (fxyPowGraph 2).pack.val (lwSampleData lwWxInstSz 0 (zt 0 (1 / 2)) (1 / 2) lwWxInstM
            (lwS lwWxInstSz 0 (1 / 2)) lwWxInstSp ω) lwSymmInstL ∂(Sizes.seqP lwWxInstSz) =
          ((outsX.map (lwEvX Complex.I)).map fun Q => ∫ ω, Q.val (lwSampleData lwWxInstSz 0 (zt 0 (1 / 2)) (1 / 2)
            lwWxInstM (lwS lwWxInstSz 0 (1 / 2)) lwWxInstSp ω) lwSymmInstL ∂(Sizes.seqP lwWxInstSz)).sum +
          ((errsX.map (lwEvX Complex.I)).map fun Q => ∫ ω, Q.val (lwSampleData lwWxInstSz 0 (zt 0 (1 / 2)) (1 / 2)
            lwWxInstM (lwS lwWxInstSz 0 (1 / 2)) lwWxInstSp ω) lwSymmInstL ∂(Sizes.seqP lwWxInstSz)).sum ∧
        (∀ Q ∈ outsX.map (lwEvX Complex.I), Q.LocReg1 ∧ Q.LocReg2 2 ∧ Q.LocReg345 2 ∧ Q.LocReg6 2 ∧
          (Q.ext 0 ≠ Q.ext 1 → 3 * (2 : ℤ) ≤ Q.g.scalingOrder)) ∧
        ∀ Q ∈ outsX.map (lwEvX Complex.I) ++ errsX.map (lwEvX Complex.I), 2 ≤ Q.g.waved.countP (fun e => !e.col)) ∧
      (LWLocRegConcl 2 ((1 + Complex.I) / 2) (1 / 4) 1 3 10 (outsX.map (lwEvX ((1 + Complex.I) / 2)))
          (errsX.map (lwEvX ((1 + Complex.I) / 2))) ∧
        ∀ Q ∈ outsX.map (lwEvX ((1 + Complex.I) / 2)) ++ errsX.map (lwEvX ((1 + Complex.I) / 2)),
          2 ≤ Q.g.waved.countP (fun e => !e.col)) := by
$ grep -n '^theorem lwEngine_inst\|^namespace LWEngineInst' RBM3D/Graph/LWEngine.lean
794:namespace LWEngineInst
805:theorem lwEngine_inst_lwEvX (P : PGraph (Fin 2)) :
819:theorem lwEngine_inst_stepX :
825:theorem lwEngine_inst_two_m :
836:theorem lwEngine_inst_stepX_edge_gg :
864:theorem lwEngine_inst_nWS_ge :
878:theorem lwEngine_inst_step1_identity :
893:theorem lwEngine_inst_localregularX :

$ lake env lean reg.lean | head -3   (registry pre-check: import RBM3D + import RBM3D.Graph.LWEngine + #assert_rbm_axioms)
Thu Oct  8 13:54:39 UTC 2026
exit=0
axiom audit: 10165 theorems, 3032 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
All within [propext,
 Classical.choice,
lines of output mentioning error / lwEngine / lwEvX / LWLocRegConcl / LocStepX: 0

$ lake build   (full library in the worktree; root RBM3D.lean does not yet import LWEngine, the hub adds it at merge; finished before 13:48:15 UTC)
Build completed successfully (4143 jobs).
exit=0
```

**Narrative** (facts from the file and the logs above).
- `lw_localregularX` is proved with the hypothesis `0 < c` only; its statement, `lwEvX` and `LWLocRegConcl` are the check file's text (`eqcheck.py`) and the `example` of the check compiles (exit 0).
- Carrier `(ℕ × ℕ) × PGraph (Fin 2)`, `lwEngine_ev3 m t = m^t.1 m̄^t.2`, `lwEngine_sw c` swaps the pair when `c` conjugates (`lwSymmTwistG_coeff`: the twist applies `star` to the coefficient when `c`).
- §2: `lwEngine_partitionX_sc` (`partitionX (sc k Δ) = (partitionX Δ).map (scale k)`, from `partitionTerms (sc k Δ) = (partitionTerms Δ).map (sc k)`: `dotChoices` and `Consistent` do not read `coeff`, `lwEngine_dotChoices_sc` is `rfl`) and `lwEngine_partition_eq` (`Γ.partition m = (partitionX Γ).map (ev m)`, a copy of the private `lwExpTerm5_partition_eq`, `LWExpTerm5.lean:299`) give `lwEngine_blk_nat`.
- §3: the 12 single-graph term constructors satisfy `T c t m (sc κ Γ) args = sc (m^a m̄^b · κ, pair swapped if c) (T c t 1 Γ args)` (`lwEngine_T1 … lwEngine_R8`; one local macro: `cases c; cases t`, the three edge lists by `rfl`, the coefficient by `simp; ring`); `lwEngine_Ds` is the list case of `oe1xDs` with the per-term tags `(1,0)`, `(1,1)` (`oe1xP3`, `m m̄`), `(2,0)` (`oe1xP4`, `m²`). Tags per rule: `(1,0)` for `m`, `(3,0)` for `m³`, as in the table of (a)(i).
- §4: `lvl1WeightOutsX`, `lvl1EdgeOutsX`, `lvl1GGOutsX` = `lwEngine_blk` of the `m = 1` terms with these tags; naturality `lvl1…Outs0 m (sc (m^j m̄^{j'}) Γ) = ((lvl1…OutsX Γ).map (shift (j,j'))).map (ev m)` is one `simp only` each; `LocStepX` has the constructors `weight`, `edge`, `gg` with the hypotheses of `LocStep` (none mentions `m`); `LocStepX.eval` gives `LocStep m (lwEvX m (t₀, P))` of the evaluated list; `lwEngine_exists_stepX` re-applies the constructor found by `lvl1_exists_step 1` (the selection reads no coefficient).
- The recursion uses `ord`, `counters`, `Normal`, `LocStd`, `Lvl1Mu` of `lwEvX m r` as those of `r.2` (by definitional unfolding: `exact hK`, `exact ⟨hL, hlt⟩`, `lvl1_mu_lt` in `lwEngine_exists`), so the measure and the cutoff are those of the untagged graph.
- §5: `lwEngine_nWS` (black waved edges) is monotone under each of the 13 term constructors (one local macro), unchanged by `partition` (`lvl1_part_struct`); `lwEngine_locStep_nWS` has the case split of `lvl1_step_good`; `lw_nWS_ge` follows by `lvl1_induction`; `fxyPowGraph p` has `p` black waved edges (`lwEngine_fxy_nWS`).
- §6: `lwEngine_exists` is the WF recursion on `Lvl1Mu K` of `lvl1_exists_aux`, with `lwEngine_combine` its step part for the children `LX.map ev`; the invariant `lwEngine_Exp m K (lwEvX m (t₀, Γ)) …` holds for every `m` and every input tag `t₀`, the lists of a child are tagged by the child's tag (`lwEngine_flat_eval`). `lwEngine_assemble` repeats the proofs of `lvl1_lemma`, `lvl1_lemma_size`, `lw_localregular_upto5`, `lw_localregular` for lists with the four properties; `lw_localregularX` takes `m ≠ 0` only as the binder of the statement (the hypothesis `m ≠ 0` of conjunct 4 is inside `LWLocRegConcl`).
- Technical note for consumers: `(lwEvX m (t₀, P)).E'` equals `P.E'` only by unfolding, so `rw` does not see it; `LocStepX.eval` writes `(E' := P.E') (I' := P.I')` and bridges with `congrArg (lvl1Pack (lwEvX m (t₀, P)))`.
- Instances (namespace `RBM.Graph.LWEngineInst`): the main one is `p = 2`, `d = 3`, `c = 1/4`, `K0 = 1`, `D = 10` (the numbers of the merged `localReg2_inst_expansion`), regime at `W = 27`, `L = 3`, `Ψ = 27^{-1/4}`; (a)(ii) used `K0 = 3`, `D = 17`, `W = 10^4`, `L = 4` in the Python model, another point of the same regime. The same tagged list is evaluated at `m = i` and `m = (1+i)/2` in `lwEngine_inst_localregularX`; the three rules are exercised on the merged graphs `p2Graph`, `lvl1ExDeg1`, `lvl1ExSame` (`lwEngine_inst_two_m`, `lwEngine_inst_stepX_edge_gg`), the identity at the merged data for `m = i` (`lwEngine_inst_step1_identity`, `lwEngine_inst_localregularX`), `lw_nWS_ge` along one `Lvl1Reach.step` (`lwEngine_inst_nWS_ge`), and `lwEvX` at the tag `(3,1)`: factor `-1` at `m = i`, `i/4` at `m = (1+i)/2` (`lwEngine_inst_lwEvX`).
- No hypothesis added, no pinned or frozen signature changed, no file but `RBM3D/Graph/LWEngine.lean`; imports exactly `RBM3D.Graph.LocalRegular6d`, `RBM3D.Graph.LWExpTerm5`; no registry line owed (the pre-check output mentions none of the new names). `wc -l`: 606 at the first section commit `cd6456f`, 937 at the last commit `bd9d092` (stop size 1500 not reached).
- Ports: none from `../RBM1D`, `../RBM2D`; the recursion and the transport follow merged RBM3D proofs (`LWLvl1.lean:3837-3880`, `:3907-3935`, `:4047-4068`, `LocalRegular2.lean:1857-1884`, `LocalRegular6d.lean:1107-1133`).

## (c) Verified Mathlib / core names used (one line each; `#check` output, 0 errors, all exist; none verified absent, no name was guessed)
- `Complex.I_ne_zero : Complex.I ≠ 0`
- `Complex.ext : ∀ {z w : ℂ}, z.re = w.re → z.im = w.im → z = w`
- `Function.comp_apply : ∀ {β : Sort u_1} {δ : Sort u_2} {α : Sort u_3} {f : β → δ} {g : α → β} {x : α}, (f ∘ g) x = f (g`
- `Function.comp_def : ∀ {α : Sort u_1} {β : Sort u_2} {δ : Sort u_3} (f : β → δ) (g : α → β), f ∘ g = fun x => f (g x)`
- `List.append_nil : ∀ {α : Type u_1} (as : List α), as ++ [] = as`
- `List.cons.injEq : ∀ {α : Type u_1} (head : α) (tail : List α) (head_1 : α) (tail_1 : List α), (head :: tail = head_1 :`
- `List.countP_append : ∀ {α : Type u_1} {p : α → Bool} {l₁ l₂ : List α}, List.countP p (l₁ ++ l₂) = List.countP p l₁ + L`
- `List.countP_map : ∀ {α : Type u_2} {β : Type u_1} {p : β → Bool} {f : α → β} {l : List α}, List.countP p (List.map f l`
- `List.filter_map : ∀ {β : Type u_1} {α : Type u_2} {f : β → α} {p : α → Bool} {l : List β}, List.filter p (List.map f l`
- `List.flatMap_congr : ∀ {α : Type u_1} {β : Type u_2} {l : List α} {f g : α → List β}, (∀ x ∈ l, f x = g x) → List.flat`
- `List.flatMap_map : ∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} (f : α → β) (g : β → List γ) (l : List α), List.flat`
- `List.map_append : ∀ {α : Type u_1} {β : Type u_2} {f : α → β} {l₁ l₂ : List α}, List.map f (l₁ ++ l₂) = List.map f l₁ `
- `List.map_congr_left : ∀ {α : Type u_1} {l : List α} {α_1 : Type u_2} {f g : α → α_1}, (∀ a ∈ l, f a = g a) → List.map `
- `List.map_cons : ∀ {α : Type u_1} {β : Type u_2} {f : α → β} {a : α} {l : List α}, List.map f (a :: l) = f a :: List.ma`
- `List.map_flatMap : ∀ {β : Type u_1} {γ : Type u_2} {α : Type u_3} {f : β → γ} {g : α → List β} {l : List α}, List.map `
- `List.map_map : ∀ {β : Type u_1} {γ : Type u_2} {α : Type u_3} {g : β → γ} {f : α → β} {l : List α}, List.map g (List.m`
- `List.map_nil : ∀ {α : Type u_1} {β : Type u_2} {f : α → β}, List.map f [] = []`
- `List.mem_append : ∀ {α : Type u_1} {a : α} {s t : List α}, a ∈ s ++ t ↔ a ∈ s ∨ a ∈ t`
- `List.mem_append_left : ∀ {α : Type u_1} {a : α} {as : List α} (bs : List α), a ∈ as → a ∈ as ++ bs`
- `List.mem_append_right : ∀ {α : Type u_1} {b : α} (as : List α) {bs : List α}, b ∈ bs → b ∈ as ++ bs`
- `List.mem_cons : ∀ {α : Type u_1} {b : α} {l : List α} {a : α}, a ∈ b :: l ↔ a = b ∨ a ∈ l`
- `List.mem_cons_self : ∀ {α : Type u_1} {a : α} {l : List α}, a ∈ a :: l`
- `List.mem_flatMap : ∀ {α : Type u_1} {β : Type u_2} {f : α → List β} {b : β} {l : List α}, b ∈ List.flatMap f l ↔ ∃ a ∈`
- `List.mem_map : ∀ {α : Type u_1} {β : Type u_2} {b : β} {f : α → β} {l : List α}, b ∈ List.map f l ↔ ∃ a ∈ l, f a = b`
- `List.mem_map_of_mem : ∀ {α : Type u_1} {β : Type u_2} {l : List α} {a : α} {f : α → β}, a ∈ l → f a ∈ List.map f l`
- `List.mem_singleton : ∀ {α : Type u_1} {a b : α}, a ∈ [b] ↔ a = b`
- `List.nil_append : ∀ {α : Type u_1} (as : List α), [] ++ as = as`
- `List.not_mem_nil : ∀ {α : Type u_1} {a : α}, a ∉ []`
- `List.sum_map_add : ∀ {ι : Type u_1} {M : Type u_2} [inst : AddCommMonoid M] {l : List ι} {f g : ι → M}, (List.map (fun`
- `Prod.fst_add : ∀ {M : Type u_1} {N : Type u_2} [inst : Add M] [inst_1 : Add N] (p q : M × N), (p + q).1 = p.1 + q.1`
- `Prod.mk_zero_zero : ∀ {M : Type u_1} {N : Type u_2} [inst : Zero M] [inst_1 : Zero N], (0, 0) = 0`
- `Prod.snd_add : ∀ {M : Type u_1} {N : Type u_2} [inst : Add M] [inst_1 : Add N] (p q : M × N), (p + q).2 = p.2 + q.2`
- `Real.rpow_le_rpow_of_exponent_le : ∀ {x y z : ℝ}, 1 ≤ x → y ≤ z → x ^ y ≤ x ^ z`
- `Real.sqrt_sq : ∀ {x : ℝ}, 0 ≤ x → √(x ^ 2) = x`
- `add_assoc : ∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b + c = a + (b + c)`
- `add_zero : ∀ {M : Type u_1} [inst : AddZeroClass M] (a : M), a + 0 = a`
- `mul_comm : ∀ {G : Type u_1} [inst : CommMagma G] (a b : G), a * b = b * a`
- `pow_add : ∀ {M : Type u_1} [inst : Monoid M] (a : M) (m n : ℕ), a ^ (m + n) = a ^ m * a ^ n`

## (d) Open issues and paper-delta candidates
1. The expectation identity (conjunct 4) is instantiated at concrete data only for `m = i` (the merged data `lwWxInstSz`, `m = m(0)`); at `m = (1+i)/2` the Lean instance evaluates the whole conclusion `LWLocRegConcl` (its data hypotheses stay inside the statement) because no merged data `Sp, M, z, u` exist for that `m`; the numerical model check at both `m` is the `N = 8` script of (a)(ii).
2. The lists are existential (WF recursion): consumers (T2297 Amend, LW-13b) get `∃ outsX errsX`, not a computable list. `lwEngine_exists` (any normal root `Γ`, any cutoff `K`, all `m` and input tags) and `LocStepX` are public if another root graph is needed.
3. Public names beyond the ticket's list: `lvl1PackX`, `LocStepX.eval`, `LocStepX.eval_one`, `lwEngine_*` (the unprefixed public names are the ticket's: `lvl1…OutsX`, `lvl1…Outs0_nat`, `LocStepX`, `lw_nWS_ge`, and the three targets); the dispatcher may rename.
4. `LocStepX`, `lwEngine_exists`, `lw_localregularX` are stated for the carrier `PGraph (Fin 2)`; the generator lemmas, naturality lemmas, `lwEngine_locStep_nWS`, `lw_nWS_ge`, `lwEngine_combine` are for general external types.
5. Paper-delta candidate `T2332a`: the paper says every coefficient "is a polynomial in `m`, `m̄`, `m^{-1}`, `m̄^{-1}`, `(1-m²)^{-1}`, `(1-m̄²)^{-1}`" (`paper/tex/7_8_light_weight.tex:144`); the Lean lists record, for every graph, the exponent pair `(j, j')` of the monomial `m^j m̄^{j'}` that multiplies the graph's own coefficient (tags `(1,0)`, `(3,0)`, `(1,1)`, `(2,0)` per step, added along the recursion), a refinement of `T2050a`; the factors of the three rules are `m`, `m³`, `m m̄`, `m²` and their conjugates (`lwEngine_T1 … lwEngine_Ds`), no inverse factor occurs. That the graph's own coefficient is a signed integer is not stated in Lean.
6. Paper-delta candidate `T2332b`: the statement carries `nWS ≥ p` (every graph of both lists has at least `p` black waved edges); the paper has no such sentence, it is T2297's invariant S1 (`docs/reports/T2297-prove.md` row 2).
7. (a′): none; no correction of section (a) was needed.
