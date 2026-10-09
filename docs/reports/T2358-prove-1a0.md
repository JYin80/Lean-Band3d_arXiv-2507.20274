Prover model: claude-sonnet-5-5

## (a) Math preflight — Fri Oct  9 02:08:08 UTC 2026

Scripts (mathematics only, no Lean) are in `/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/ec1cbe39-5957-4519-82e4-38af3363ddc4/scratchpad/T2358/`: `bridge.py`, `molecular.py`, `expdata.py`.
Citations `file:line` are at `main` 5d8f515, paths relative to `RBM3D/`; `probe NNN` is line NNN of `t/T2348:RBM3D/Probe/T2348Pins.lean`.
This ticket has no analytic exponents (no `Φ`, `Ψ`, `W^{-c}` threshold enters any target); the table lists the parameters and constants the targets depend on.

### (i) Exponent / parameter table

| # | quantity | value / range | constraint (source) | slack |
|---|---|---|---|---|
| 1 | `p` (power in `fxyPowGraph p`, `LWEngineProv`, bridge) | engine: every `p : ℕ`; bridge and instance: even `p`, instance `p = 2` (also checked `p = 4`) | bridge needs `Even p`: `fxyPowGraph_val_eq` (`Graph/LocalRegular.lean:1739`), blue blocks `i < p/2`, red the rest | none needed; `p = 0` is degenerate and excluded from the instance |
| 2 | weight `W = Π_k 1_D(blk ℓ(β_k))` | values in `{0,1}`, real | `WExp` takes any real `W`; the Gaussian integral is linear in the deterministic factor `W` | `0 <= W <= 1`, no condition on `D` |
| 3 | `(c, K0, d, D)` of `LWEngineProv`, cutoff `K = lvl1Cutoff c K0 d D counters` | `c > 0` and `K0, d, D` free | as in merged `lw_localregularX` (`Graph/LWEngine.lean:771-775`) | unchanged by provenance |
| 4 | tags `(j, j')` (`lwEvX`) | any in `ℕ × ℕ` | scalar `m^j m̄^{j'}` multiplies the coefficient only (`Graph/LWEngine.lean:57`), so it commutes with `π` and `W` | none |
| 5 | data of `WExp` (`LWExpData`, nine conjuncts) | `GaussIBP sz` (theorem `gaussIBP`, `Green/IBPPoly.lean:305`, all `sz`), `Im z > 0`, `u > 0`, `m ≠ 0`, `z + u m = -m⁻¹`, `Sp - m² Sp·(lwS u) = lwS u`, `Spᵀ = Sp`, `M = m·I` | `Graph/LWEngine.lean:68-75`; `lwS u = u·lwS 1` (`Graph/LWMoment.lean:211` `lwMoment_Dt_eq`) | instance below: `Im z = 0.25`, `u = 0.5`, `|m| = 1.18`, `‖m² S‖ = |m|²·u = 0.70 < 1` so `Sp` exists |
| 6 | initial molecules of `fxyPowGraph p` | `p` internal molecules `{α_k, β_k}`, 2 external `{x}`, `{y}` | waved edges `α_k–β_k` only (`Graph/LocalRegular.lean:1356`); `×`-dotted edges are not in `LGraph.adj` (`Graph/LWVocab.lean:157-160`) | `CoverBy β` holds with equality (each internal molecule contains exactly one `β_k`) |
| 7 | `Normal` of the step input `P.g` | `LocStepXProv` as pinned has NO such hypothesis | the edge and gg identities need it: `lvl1_step_identity` takes `(hN : P.g.Normal)` (`Graph/LWLvl1.lean:3591`); `lwEngine_exists_stepX` takes `hN` (`Graph/LWEngine.lean:455`) | **violated by the pin: see (iii), FAIL** |

Mathematics of the targets (as far as (ii) and the verdicts need).
- **C1, bridge (twin of `lwMoment_fxyPow_val`, `Graph/LWMoment.lean:1748`).** `term(ℓ) = Π_i blockVal_i(ℓα_i, ℓβ_i)` (`localReg_fxy_term`, `LocalRegular.lean:1689`) and the weight factorises over blocks, so `Σ_ℓ W term = Π_i Σ_{a,b} 1_D(blk b) blockVal_i(a,b)` (`localReg_fxy_sum_pairs`, `:1660`). Blue block sum = `LWfD` (same `ring` step as `lwMoment_fxyVal_D`, `LWMoment.lean:1595`, with the `if STblk β ∈ D` wrapped around). Red block sum = `star` of it (`1_D` real, `S` real). Product `= LWfD^{p/2} conj(LWfD)^{p/2} = ‖LWfD‖^p` (`lwMoment_pow_conj`, `:252`). `pvalW` on `LGraph.pack` has `ext = id`, so `h.choose = ![x,y]` (as `pack_val`, `LWVocab.lean:704`). At `D = univ` it is `LWf`.
- **C2, `Molecular` for the whole constructor family (edge identities, no `nWS` count).** Every output of `weight`, `edge`, `gg` is `Γ.owxExt emb c s w` with `emb` the inclusion `owxEmb k` (or `id`), `waved = Γ.waved.map emb ++ w`, `dotted = Γ.dotted.map emb` (`LWWeightExp.lean:458-464`), then a twist (`lwSymmTwistG` keeps the waved/dotted endpoints as a set, `LWSymm.lean:100-111`), the dotted partition and `LGraph.merge` (`LWVocab.lean:778-782`: waved edges mapped by `vmap`, `=` edges deleted, i.e. identifications). Every new vertex is joined by an appended waved edge to `emb x` (T1,T3: `x–α`; T2,T4,R4,R6,R8: `x–α`, `α–β`; `oe1xD`, `P3..P6`, `R5`, `R7`: `x–α`, `LWWeightExp.lean:658-690`, `LWEdgeExp.lean:596-1110`, `LWGGExp.lean:485-535`; `R2` adds `x–y`, no new vertex). So with `π = vmap ∘ emb`: (1) a waved or `=` path maps to a waved path or an equality; (2) an internal output molecule contains `π v` for an old `v` or a new vertex joined to `π x`, and if the input molecule of that `v` contained an external vertex `e`, then `π e` is external in the same output molecule. Coarsening by the merge cannot create a new internal molecule. `ExtOK`: `vmap (inl a) = inl (extMap a)`. Cover: `Molecular.comp` and `CoverBy.comp` (probe 88, 125, compiled).

### (ii) One concrete nondegenerate instance

Bridge at `p = 2` (`n = 6` labels, `x = 0 ≠ y = 1`, `D` = labels with `blk ∈ {1,2}` for the toy map `blk a = a mod 3`, so `D` is neither empty nor everything) and at `p = 4` (`n = 4`); `G = (H - z)^{-1}` with `H` real symmetric, `z = 0.3+0.4i`, `M = 0.55i·I`, `S` real symmetric with row sums 1 (formulas of `localReg_fxyBlockVal`, `LocalRegular.lean:1684`, copied; brute force sum over all `n^{2p}` labellings):
```
$ python3 .../T2358/bridge.py
p=2 n=6: weighted pval = 3.1951590863e-05+4.1481735277e-20j; |fD|^p = 3.1951590863e-05; |tot-|fD|^p| = 1.22e-19; |fD|=5.653e-03; unweighted pval vs |f|^p diff = 5.86e-19
p=4 n=4: weighted pval = 1.3243141238e-03-2.0216131051e-19j; |fD|^p = 1.3243141238e-03; |tot-|fD|^p| = 2.18e-18; |fD|=1.908e-01; unweighted pval vs |f|^p diff = 3.92e-18
```
`LWExpData` algebraic conjuncts (conjunct 1 is the theorem `gaussIBP`; there is no external hypothesis in any target, so no limit computation is owed):
```
$ python3 .../T2358/expdata.py
m = (-0.24663709070824297+1.1554705973758683j)  |z+u m+1/m| = 0.0  Im z = 0.25  u = 0.5  m!=0: True
max|Sp - m^2 Sp S - S| = 2.7809732887839817e-17  |Sp-Sp^T| = 1.4046172853913364e-17
M diag = m, offdiag 0:  True
```
`Molecular`, `ExtOK`, `Cover` on `fxyPowGraph p` (combinatorial model of `LGraph.adj` molecules; all patterns of (i), every `x`, `y`, EVERY partition of the output vertices as the merge; then random depth-4 chains with composed `π`, checked against the start graph; initial `Cover`; negative control):
```
$ python3 .../T2358/molecular.py
exhaustive depth-1, p=2: cases 187920 failures 0
random chains (composition), cases 24000 failures 0
p=2: internal molecules 2, ext molecules 2, each contains some beta_k: True
p=3: internal molecules 3, ext molecules 2, each contains some beta_k: True
p=4: internal molecules 4, ext molecules 2, each contains some beta_k: True
control (no waved edge to the new vertex): Molecular(2) fails in 203 of 877 merges
```
The `weight` step at `x = β_0` (a circled loop `Ǧ_{β_0β_0}` exists) is the `T1..T4` rows of that model.

### (iii) Falsity of the pinned `LocStepXProv` (no `P.g.Normal`)

```
$ git show t/T2348:RBM3D/Probe/T2348Pins.lean | sed -n 157,159p        (the pin, copied verbatim by the ticket)
def LocStepXProv : Prop :=
  ∀ (P : PGraph (Fin 2)) (LX : List ((ℕ × ℕ) × PGraph (Fin 2))), LocStepX P LX →
    ∃ π : ∀ r ∈ LX, P.E' ⊕ P.I' → r.2.E' ⊕ r.2.I', ∀ (m : ℂ) (t0 : ℕ × ℕ),
$ sed -n 3590,3591p RBM3D/Graph/LWLvl1.lean
theorem lvl1_step_identity {E : Type} {P : PGraph E} {outs : List (PGraph E)} (hst : LocStep m P outs)
    (hN : P.g.Normal) (ℓe : E → Idx d (sz.L n) (sz.W n)) :
$ sed -n 1650,1651p RBM3D/Graph/LWSymm.lean            (merged exact identity for the edge step)
      ∫ ω, (lwSymmOe1xT1 c t m Γ p x v hv).val ... ∂(Sizes.seqP sz) +
      ∫ ω, (lwSymmOe1xOwx c t m Γ p x).val ... ∂(Sizes.seqP sz) +  ... (the `Ds` sum)
$ sed -n 338,341p RBM3D/Graph/LWEngine.lean            (`lvl1EdgeOutsX`: Owx and Ds terms only, NO `oe1xT1` term)
```
The true edge identity has the extra term `E[val(lwSymmOe1xT1)]` (`m 1_{x=y₁}`); it is dropped from `LocStepX` outputs and vanishes only on a normal graph (`lvl1_oe1xT1_zero`, `Graph/LWLvl1.lean:3389`, uses the `×`-dotted edge `x≠y₁` supplied by `Normal`). Counterexample to the pin: `Γ : LGraph (Fin 2) (Fin 1)`, `solid = [⟨true,false,inr 0,inl 0⟩]` (`G_{x,a}`), `waved = dotted = []`, `coeff = 1`, `P = Γ.pack`, `p = (that edge, [])` (`lwSplit [e] = [(e,[])]`), `c = t = false`, `v = inl 0 ≠ inr x`, `hwf` holds, `lvl1DegAt (inr x) = 1` (`≠ 0`, `≠ 2`, so `hbad` holds): `LocStepX.edge` applies (`LWEngine.lean:395`). Here `lwSplit p.2 = []` so `LX` is the `Owx` term only. By `lwSymm_oe1x_graph_E` the left side `WExp` (`W ≡ 1`, `pvalW_one`) exceeds the right side by `E[val T1]`; `T1` has no internal vertex (`{i // i ≠ x}` is empty), no solid, waved or dotted edge, and `coeff = m·1`, so `val T1 = m ≠ 0` at every data of `LWExpData` (conjunct `m ≠ 0`; data exist by (ii)). Hence `LocStepXProv` is false as pinned. The same holds for `gg` (term `R1`, `lvl1_oe2xR1_zero`, `LWLvl1.lean:3408`); `weight` needs no normality (`lvl1_step_identity`, `weight` case, passes no `hN`).
Minimal repair (does not change the route, `LWEngineProv`, `ProvOut.Molecular`, `WExp.comp`, `CoverBy.comp`, or any consumer): `LocStepXProv := ∀ P LX, LocStepX P LX → P.g.Normal → ∃ π, …`. The recursion supplies normality of every child: `hch` in `lwEngine_exists` (`LWEngine.lean:703`, from `lvl1_step_good`), and `fxyPowGraph_normal p` at the root.

### Verdicts

| target | verdict | reason |
|---|---|---|
| copied probe declarations (`valW` … `ProvOutX.Cover`, `mkProv`, `stepOuts`, `LWEngineProv`, `lwEngineProv_imp_localregularX`, `LWfD`, `LWfD_union`) except `LocStepXProv` | PASS | true statements; the proved ones compiled in the probe (T2348 prove report B2); `LWEngineProv` is true: start graph normal, leaves carry `id`, steps carry `π`, `Cover` by `CoverBy.comp` |
| `lwProv_bridge` (C1) | PASS (mathematics; compilation is stage 1b) | block factorisation, the `1_D` weight is real and sits on `β_k`; numerically verified at `p = 2, 4`; hypothesis `Even p` |
| `Molecular` for `weight` and all constructors, initial `Cover` (C2) | PASS (mathematics) | uniform `owxExt` + merge argument above; exhaustive and random checks, negative control fails as it should |
| `locStepXProv_holds : LocStepXProv` | **FAIL** | the pinned statement is false for `edge` (and `gg`) on a non-normal input, see (iii); repair: add `P.g.Normal →` (pin change, dispatcher) |
| `lw_localregularXP : LWEngineProv` | PASS conditional | true; its proof uses the repaired step lemma at normal graphs only |

Overall verdict: **FAIL** (a pinned target statement is false; CONTROL H148: RETURN). Not a route break: C1 and C2 close; the defect is one missing hypothesis in the pin of `LocStepXProv`.
