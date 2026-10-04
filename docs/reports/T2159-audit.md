Auditor model: claude-opus-5-5

# T2159 audit (round 1) — ST2-34 `Induction/AzumaProxyN`

Written Sun Oct  4 21:01:52 UTC 2026 (`date -u`). Branch `t/T2159` at `bf84610`; merge-base with `main` `686cf71` (`main` now `275e275`). Audit worktree `RBM3D-wt/T2159-audit1` (detached at `bf84610`).

## 1. Scope of the diff

```
$ git diff --name-only main...t/T2159
RBM3D/Induction/AzumaProxyN.lean
$ git diff --stat main...t/T2159 -- RBM3D/Induction/GridAssemblyN.lean RBM3D/Test/Axioms.lean RBM3D.lean
(empty)
$ grep -n "AzumaSubGN\|azumaSubGN" RBM3D/Test/Axioms.lean      (main)
(empty: no owed registry line to delete)
$ grep -nwE "sorry|admit|native_decide|axiom|unsafe|implemented_by|extern|skipKernelTC|opaque" RBM3D/Induction/AzumaProxyN.lean
(empty)
$ for nm in testFun_const_smul testFun_linComb azumaSubGN zero_mem_goodSetN zero_mem_goodSetN_of_levels AzumaProxyNInst; do git grep -nw $nm main -- RBM3D | wc -l; done
0 0 0 0 0 0
```
Only the sole writable file is touched; the merged pin `AzumaSubGN` (`GridAssemblyN.lean:122`) is unchanged.

## 2. Build and axioms (audit worktree)

```
$ lake build RBM3D.Induction.AzumaProxyN      (errors/warnings of the new module, axiom lines)
ℹ [3789/3789] Built RBM3D.Induction.AzumaProxyN (17s)
$ grep -c "warning: RBM3D/Induction/AzumaProxyN" build.log
0
$ grep -n error build.log
(empty)
Build completed successfully (3789 jobs).
```
$ #print axioms lines of the new module (file line : name : axioms; "RBM.Ind." dropped)
1473:0: 'testFun_const_smul' [propext, Classical.choice, Quot.sound] 
1474:0: 'testFun_linComb' [propext, Classical.choice, Quot.sound] 
1475:0: 'azumaSubGN' [propext, Classical.choice, Quot.sound] 
1476:0: 'zero_mem_goodSetN' [propext, Classical.choice, Quot.sound] 
1477:0: 'azumaProxy_hee_of_levels' [propext, Classical.choice, Quot.sound] 
1478:0: 'zero_mem_goodSetN_of_levels' [propext, Classical.choice, Quot.sound] 
1479:0: 'azumaProxy_pathH_zero_of_s_zero' [propext, Classical.choice, Quot.sound] 
1480:0: 'azumaProxy_subG_ugen' [propext, Classical.choice, Quot.sound] 
1481:0: 'azumaProxy_subG_goodExit' [propext, Classical.choice, Quot.sound] 
1482:0: 'azumaProxy_pos_gridExitTauN' [propext, Classical.choice, Quot.sound] 
1483:0: 'azumaProxy_loop3_scalar' [propext, Classical.choice, Quot.sound] 
1484:0: 'AzumaProxyNInst.azumaSubGN_instance' [propext, Classical.choice, Quot.sound] 
1485:0: 'AzumaProxyNInst.zero_mem_goodSetN_instance' [propext, Classical.choice, Quot.sound] 
1486:0: 'AzumaProxyNInst.zero_mem_goodSetN_of_levels_instance' [propext, Classical.choice, Quot.sound] 
1487:0: 'AzumaProxyNInst.zero_mem_goodSetN_instance_grid' [propext, Classical.choice, Quot.sound] 
1488:0: 'AzumaProxyNInst.azumaSubGN_goodExit_zero_instance' [propext, Classical.choice, Quot.sound] 
1489:0: 'AzumaProxyNInst.goodExitTauN_pos_instance' [propext, Classical.choice, Quot.sound] 
1490:0: 'AzumaProxyNInst.azumaSubGN_goodExit_instance' [propext, Classical.choice, Quot.sound] 
1491:0: 'AzumaProxyNInst.testFun_linComb_instance' [propext, Classical.choice, Quot.sound] 
1492:0: 'AzumaProxyNInst.testFun_const_smul_instance' [propext, Classical.choice, Quot.sound] 
1493:0: 'AzumaProxyNInst.qProxy3_pos' [propext, Classical.choice, Quot.sound]
```
All 21 printed declarations depend only on `propext`, `Classical.choice`, `Quot.sound`.

## 3. Statements against the ticket

Auditor check file `scratchpad/T2159/audit.lean` (imports only `RBM3D.Induction.AzumaProxyN`), `lake env lean` in the audit worktree:
```
-- (1) the pin, no extra argument
example : ∀ {d : ℕ} (sz : Sizes d) (s t : ℕ → ℝ) (K : ℕ → ℕ), AzumaSubGN sz s t K :=
  fun sz s t K => azumaSubGN sz s t K
-- (3) composed instance at concrete levels Γ=4, Λ=3, Φ=1, τ'=1/2, D'=1, m=1, a=(0,0,0)
example : SubGaussFormN sz0 0 (goodExitTauN sz0 Einst sInst vg Kg 3 Γ4 Λ3 Φ1 (1/2) 1 0)
    (fun ω => ∑ b, kap3 1 b0 b * ZfamN sz0 sInst vg Kg 0 0 phi3 ω b) (qProxy3 1 b0) ∧
    0 < qProxy3 1 b0 ∧ (∀ ω, 0 < goodExitTauN sz0 Einst sInst vg Kg 3 Γ4 Λ3 Φ1 (1/2) 1 0 ω) :=
  ⟨azumaSubGN_goodExit_zero_instance Γ4 Λ3 Φ1 (1/2) 1 1 b0, qProxy3_pos, goodExitTauN_pos_instance⟩
example : sz0.L 0 = 4 ∧ sz0.W 0 = 32 := ⟨sz0_values.1, sz0_values.2.1⟩
--- output ---
@zero_mem_goodSetN : ∀ {d : ℕ} (sz : Sizes d) (n : ℕ) {E : ℝ},
  |E| < 2 → ∀ {k : ℕ}, 1 ≤ k → ∀ {Γ Λ Φ τ' D' : ℝ}, 0 ≤ Γ → 1 ≤ Γ * Φ →
    ↑k * ((1 + 2 * ↑d * sz.lam n ^ 2)⁻¹ * etaT E 0) ≤ Γ * (Γ * Λ) * Bparam d (sz.L n) (sz.lam n) 0 0 ^ (2 * k) →
      0 ∈ sz.GoodSetN n E 0 k Γ Λ Φ τ' D'
@testFun_const_smul : ∀ {d} {sz : Sizes d} {n} {Φ : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ → ℂ},
  HermTestFun sz n Φ → ∀ (q : ℂ), HermTestFun sz n fun M => q • Φ M
@testFun_linComb : ∀ {d} {sz : Sizes d} {n} {ι : Type u_1} [Fintype ι] (q : ι → ℂ) {Φ : ι → Matrix … → ℂ},
  (∀ (i : ι), HermTestFun sz n (Φ i)) → HermTestFun sz n fun M => ∑ i, q i * Φ i M
'RBM.Ind.AzumaProxyNInst.qProxy3_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
exit=0
```
RBM2D at `c9a24cf` (`git show c9a24cf:RBM2D/Induction/AzumaProxyN.lean`, lines 110-112, 133-136, 279): `testFun_const_smul (h : HermTestFun d n Φ) (q : ℂ) : HermTestFun d n (fun M => q • Φ M)`, `testFun_linComb … HermTestFun d n (fun M => ∑ i : ι, q i * Φ i M)`, `theorem azumaSubGN (s t : ℕ → ℝ) (K : ℕ → ℕ) : AzumaSubGN d s t K` — identical up to the dictionary `d : Sizes ↦ sz : Sizes d`, `Idx L W ↦ Idx d L W`.

- **Target 1a/1b `testFun_const_smul`, `testFun_linComb`**: same shape as RBM2D; no extra hypothesis. PASS.
- **Target 1c `azumaSubGN`**: proves the merged pin `AzumaSubGN sz s t K` for every `d`, `sz`, `s`, `t`, `K` with no hypothesis (example above; also `section StatementChecks`, file line 1462). Not a special case or conditional adapter. PASS.
- **Target 2 `zero_mem_goodSetN`**: `0 ∈ GoodSetN n E 0 k Γ Λ Φ τ' D'` at `u = 0`, for all `d`, `sz`, `n`, `|E| < 2`, `k ≥ 1`, all `τ'`, `D'`, under three explicit deterministic level hypotheses (`0 ≤ Γ`, `1 ≤ ΓΦ`, `hee`). This is the form the ticket asks for ("explicit hypotheses on the levels, deterministic"). `hee` matches the (D4) clause: RHS of (D4) is `Γ(ΓΛ) Bctl(n,0)^{2k}/η` with `Bctl n t = W^{-d}·Bparam d L g t 0` (`Defs/Sizes.lean:214-215`), so the `W^{-2kd}` factor cancels against the value `k S_cc W^{-2kd}` of `STeeM(0)`, as preflight (a) row 7 states. PASS.
- `zero_mem_goodSetN_of_levels` (not pinned): corollary of target 2 with the sufficient condition `k(1+g²)^{2k} ≤ Γ²Λ`, via `azumaProxy_hee_of_levels`. Not a replacement for target 2.

## 4. Vacuity, hidden hypotheses, cycles

- No hypothesis in a structure field: `zero_mem_goodSetN` has only `Prop` hypotheses in its signature (above); `azumaSubGN` has none beyond the pin's own quantified premises.
- No cycle: `azumaSubGN` is a closed theorem with the three standard axioms; `AzumaSubGN` appears as a hypothesis only of the prefixed helpers `azumaProxy_subG_ugen`, `azumaProxy_subG_goodExit`, and the instance `azumaSubGN_goodExit_instance` feeds it `azumaSubGN sz0 sInst vg Kg` (file line 1259).
- Dependencies are merged modules only (imports: `GridAssemblyN`, `GridGoodN`, `StepDecompN`, `LoopC2N`, `Path/Markov`, `Gauss/LoopGenerator`, `Loop/KLTreeDeriv`; no `import RBM3D`).
- No external hypothesis is introduced (no limit check needed, TEAM §8 lesson 14).

## 5. Compiled nonempty instances (`d = 3`, `sz0`: `L = 4`, `W = 32`, `lam = 1/64`; `E = 1/2`; `s ≡ 0`, `v ≡ 1/32`, `K ≡ 4`)

| endpoint | instance (file line) | data / discharged hypotheses | verdict |
|---|---|---|---|
| `azumaSubGN` | `azumaSubGN_instance` (1168) | `Φ = loopFamN` (k = 3, `hermTestFunLoopN`), `κ = Ugen` weights, `τ ≡ 4`, `G 0 = {0}`, `Q = qProxy3` exact form; all premises discharged | PASS |
| `azumaSubGN` ∘ `goodExitTauN` | `azumaSubGN_goodExit_zero_instance` (1220) + `goodExitTauN_pos_instance` (1240) | `τ = goodExitTauN` (measurability `goodExitMeasN`), `G j = GoodSetN ∩ {j=0→M=0}`; `τ ≥ 1` everywhere at `Γ=4, Λ=3, Φ=1` by target 2 | PASS |
| non-degeneracy of `Q` | `qProxy3_pos` (1441) | `0 < qProxy3 1 (0,0,0)` | PASS |
| `zero_mem_goodSetN` | `zero_mem_goodSetN_instance` (1189), `_instance_grid` (1210) | `k = 3`, `Γ = 4`, `Λ = 3`, `Φ = 1`, `τ' = 1/2`, `D' = 1`; `hee` by `norm_num` (`Γ²Λ = 48`) | PASS |
| `testFun_const_smul`, `testFun_linComb` | `testFun_const_smul_instance` (1269), `testFun_linComb_instance` (1264) | `q = I`, `Φ = loopFamN`; `q = kap3 m a` | PASS |
| `azumaSubGN_goodExit_instance` | (1251) | keeps `hQ` (majorant of `Δ·3·qvFormN` on `GoodSetN`, output of S3-10/S3-14) as hypothesis, exactly as RBM2D `AzumaProxyN:1324-1330` at `c9a24cf` | port of RBM2D instance; not an endpoint — the endpoint `azumaSubGN` has the fully discharged instances above |

No `N = 0`, empty index, collapsed window (`Δ = 1/128`), `False` premise, or astronomically large witness (levels 4, 3, 1).

## 6. Paper deltas

- `T2159a` (prove report (d)): (D4) at `H = 0` needs `k S_cc η_0 ≤ Γ²Λ b^{2k}`; RBM2D's `k/5 ≤ Γ²Λ` and the unit levels do not carry over. Proposed; covers the only Lean/RBM2D difference of target 2.
- `azumaSubGN` proves the merged pin unchanged; the pin's own difference (`[NeZero k]` dropped) is already D360 (`T2154a`, `docs/paper-deltas.md:1319`).
- No other Lean/paper statement difference found.

## 7. Observations (no RETURN)

- O1 (CLAUDE.md §3 (E)): `zero_mem_goodSetN_of_levels` (line 924) is public, not pinned, and not prefixed `azumaProxy_`; name clash grep against `main` is 0. Instance-section auxiliaries (`Einst`, `phi3`, `z1`, `fsc`, `sum_pos_aux`, …) are public but inside `RBM.Ind.AzumaProxyNInst`. The dispatcher may ask for a rename in a later ticket; no statement, instance, build or axiom is affected.
- O2: `main` has advanced to `275e275` since the merge-base `686cf71`; the hub's full `lake build` at merge covers the interaction with T2156/T2158 (name grep against current `main`: 0 hits).

## Verdict

| target | verdict |
|---|---|
| 1 `testFun_const_smul`, `testFun_linComb`, `azumaSubGN` | PASS |
| 2 `zero_mem_goodSetN` | PASS |
| 3 instances | PASS |

**Overall: PASS.** No dispatcher sign-off needed.
