Auditor model: claude-opus-5-5

# T2167 audit (round 1) — S3-10b `Induction/NQGood2` — Mon Oct  5 04:10:32 UTC 2026

Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2167-audit1` (detached at `t/T2167` = 1e0d03a). Scratch: `scratchpad/T2167/`.

## 1. Scope, build, hygiene, axioms
```
$ git diff --name-status main...t/T2167
A	RBM3D/Induction/NQGood2.lean
$ lake build RBM3D.Induction.NQGood2 2>&1 | grep -E "error|NQGood2.*warning|Build completed"; echo exit $?
warning: RBM3D/Induction/NQGood2.lean:24:100: This line exceeds the 100 character limit, please shorten it!
warning: RBM3D/Induction/NQGood2.lean:52:100: This line exceeds the 100 character limit, please shorten it!
Build completed successfully (3838 jobs).
exit 0
$ grep -cwE 'sorry|admit|native_decide|axiom' RBM3D/Induction/NQGood2.lean
0
$ grep -n "^import" NQGood2.lean   -> NQGood1, ScaleFacts, StepDecompN, GridDuhamelN, Step2Events, Green.CondDom (no `import RBM3D`)
$ lake env lean ax.lean   (#print axioms of the 23 targets + 12 instances, incl. gridAssemblyHyp_instance,
                           bundle_fields_instance, subGaussStop_instance, hc_pos_instance, tau0_pos, delta_shift_ok)
lines with exactly [propext, Classical.choice, Quot.sound]: 35
other lines: 0
$ git grep -w <23 target names + NQGood2Inst> main -- 'RBM3D/*.lean' RBM3D.lean | wc -l
0
```
`Test/Axioms.lean` untouched (the registry pre-check in the prove report (b.3) shows no new premise line). Frozen signatures: none touched (file is new).

## 2. Statement checks
### Target 1 (six pinned definitions)
```
$ diff <(sed -n '76,118p' RBM3D/Induction/NQGood2.lean) <(sed -n '101,143p' docs/tickets/checks/T2167-check.lean) && echo EMPTY
EMPTY DIFF (defs 76-118 vs check 101-143)
```
Namespace `RBM.Ind` (file `:70`), as pinned. PASS.

### Target 2 ((5.93) at d ≥ 3)
Paper `3_5:1158`: "we use $\frac{\ilambda^2+|1-u|}{\ilambda^2+|1-t|} B_{u,0} \le B_{t,0}$" (and the bound uses ratio^{n-1}·(W^{-d}B_{u,0})^n ≤ (W^{-d}B_{t,0})^n).
```
nqGood2_ratio_mul_Bctl_le (n) {u t} (hut : u ≤ t) (ht : t < 1) :
  ((sz.lam n ^ 2 + |1 - u|) / (sz.lam n ^ 2 + |1 - t|)) * sz.Bctl n u ≤ sz.Bctl n t
kappaNonAltN_mul_Bctl_pow_le ... (hW : 0 ≤ W) u (him : u i ≤ u m) (hm1 : u m < 1) :
  kappaNonAltN d k Λg κ' (sz.lam n) W ε u i m * (sz.Bctl n (u i)) ^ k ≤ W ^ (nqGood1C d k Λg κ' * ε) * (sz.Bctl n (u m)) ^ k
kappaNonAltN_succ_mul_Bctl_pow_le ... (hjj : u j ≤ u (j+1)) (hj1m : u (j+1) ≤ u m) (hm1 : u m < 1) :
  kappaNonAltN ... (j + 1) m * (sz.Bctl n (u j)) ^ k ≤ W ^ (C * ε) * (sz.Bctl n (u m)) ^ k
```
Hypotheses exactly the ticket's (`u ≤ t < 1`; `0 ≤ W`; `u_j ≤ u_{j+1} ≤ u_m < 1`); every real `g`. PASS (3/3).

### Target 3 (fields of `GridAssemblyHypN`, `GridAssemblyN.lean:183-225`)
- `nonAlt_hkerN`: premise list compared item by item with the ticket (`3 ≤ d`, `2 ≤ k`, `0 < Λg`, `0 < κ'`, `[NeZero L]`, `3 ≤ L`, `0 < g`, `g ≤ Λg`, `1 < W`, `0 < ε < 1`, `4 ≤ W^ε`, `d W^{τ'} ≤ W^ε`, `1 < Dc`, `∀ i ≤ K, 0 ≤ u i`, monotone on `[0,K]`, `u K ≤ 1 - g²/L²`, `W⁻¹ ≤ (1-u K)/(1-u 0)`, `|E| ≤ 2`, `κ' ≤ Im m(E)`, non-alternating σ): identical. Conclusion is the field `hker` with `Cls = nonAltClsN`, `κ = kappaNonAltN`, `εK = epsNonAltN` (general `L, g, W`). The class is exactly `hδD`+`hXcls` of the merged `hker_of_case1N` (`NQGood1.lean`, signature read) at `D = Dc`, `s = u i`.
- `goodSetN_A0clsN` (`1 ≤ k`, `Dc ≤ D'`, `1 ≤ W`, `M ∈ GoodSetN … (u i)`), `nonAlt_hA0clsN` (concl. `∀ ω, 0 < τ ω → Cls 0 (W^{-D'}) (AvecN … 0 σ ω)` = field `hA0cls`), `nonAlt_hdriftN` (`2 ≤ k`; = `hdrift`), `goodSetN_driftClsN` (`u i ≤ u i' < 1`), `nonAlt_hDclsN` (index `j+1`; = `hDcls`), `nonAlt_hκ0N`, `nonAlt_hε0N`, `nonAlt_hdDrift0N` (`0 ≤ Γ n`, `0 ≤ Φ n`, `1 ≤ k`, `|E n| < 2`): all on `hτG : ∀ ω j, j < τ ω → pathH … j ω ∈ GoodSetN … (gridTime … j) …` for a general `τ`. Field shapes certified by `gridAssemblyHyp_instance` (§3), which takes each field directly from these theorems' instances.
- `nonAlt_hDclsN`, `nonAlt_hdDrift0N` add `s n ≤ v n`, `v n < 1` (needed for `u_{j+1} < 1`; both are `∀ n` premises of the consumer `azumaProxy_subG_goodExit`): observation O2.
- §45 O3(3): `grep -nE '0 ≤ sz\.lam|0 ≤ g\)'` → only `:136  have hg : 0 ≤ sz.lam n ^ 2 := sq_nonneg _` (internal, not a premise). No `L^d ≤ W^K` premise (0 hits). PASS (9/9).

### Target 4 (QV constant)
- `qvBdNonAltN_pos` (`0 ≤ Λ`, `u ≤ 1`): weaker premises than the ticket implies; PASS.
- `qvFormN_le_of_goodSetN_shiftN`: ticket premises present (`M ∈ GoodSetN n E u …`, `0 ≤ u ≤ u' ≤ w ≤ 1-g²/L²`, `W⁻¹ ≤ (1-w)/(1-u')`, `0 ≤ Γ`, `0 ≤ Λ`, `k+1 < D''`, `hδ : W^{-D'} + eeShiftErrN d L W E k u u' ≤ W^{-D''}`, premises of `nqGood1_qvFormN_le_of_bounds`); conclusion `qvFormN sz n E u' w σ M a ≤ qvBdNonAltN … u' w`. One difference: `hE : |E| < 2` where `nqGood1_qvFormN_le_of_bounds` has `|E| ≤ 2`. Forced by the ticket's own route: the merged signature is
  `theorem norm_STeeM_shiftN_le (n : ℕ) {E : ℝ} (hE : |E| < 2) {M} (hM : M.IsHermitian) …` (NQGood1.lean); the consumer `azumaProxy_subG_goodExit` already assumes `∀ n, |E n| < 2`; paper works in the bulk. Covered by candidate T2167c. Observation O1, not a defect.
- `hQ_nonAltN`: conclusion is verbatim the `hQ` premise of `azumaProxy_subG_goodExit` (signature read) with `Q = cQVNonAltN … m a j`.
- `subGaussStop_nonAltN`: `∀ n` premises = exactly `hE, hs0, hsv, hv1` of `azumaProxy_subG_goodExit`; all others at fixed `n` (checklist §29 (4)); premise list matches the ticket item by item; conclusion `SubGaussStopN sz (E n) σ (gridTime s v K n) (goodExitTauN sz E s v K k Γ Λ Φ τ' D' n) (fun j ω => ZvecN …) m a j (cQVNonAltN …)` as pinned.
- `cQVNonAltN_sum_pos` (`1 ≤ k`, `s n < v n`, `v n < 1`, `K n ≠ 0`, `0 ≤ Λ n`): conclusion = field `hc_pos`. PASS (5/5).

## 3. Vacuity / hidden hypotheses / cycles
- No new `structure`/`class`; `nonAltClsN` is the pinned Prop-valued definition, assumed only where `GridAssemblyHypN.hker` assumes `Cls`, and concluded by `nonAlt_hA0clsN`, `nonAlt_hDclsN`.
- Imports are merged modules only; the build above resolves them; no cycle.
- External-type premise `hδ` (shift): discharged at the instance for every `j < 4` (`delta_shift_ok`, axioms clean); limit check along `sz0` with `Δ = N^{-11}` in prove report (a)(ii) (ratio ≤ 3e-34 at n = 0, → 0). `C = nqGood1C` stays abstract (only `C > 0`); every instance holds for the actual `C`.

## 4. Compiled nonempty instances (namespace `RBM.Ind.NQGood2Inst`; `d = 3`, `sz0`, `n = 0`: `L = 4`, `W = 32`, `g = 1/64`, `E = 1/2`, `K = 4`, `u_j = j/128`, `k = 3`, `σ = sig3`, levels `(4,3,1)`, `τ' = 1/5`, `ε = 4/5`, `D' = Dc = 6`, `D'' = 5`, `Λg = 10`, `κ' = 1/2`)
Every instance below was read in the file; each applies the named target with every deterministic hypothesis discharged by `norm_num`/data lemmas; none is a hypothesis of the instance.
```
nqGood2_ratio_mul_Bctl_le            ratio_instance (i ≤ 4: covers (u_0,u_4),(u_1,u_4))
kappaNonAltN_mul_Bctl_pow_le         kappa_Bctl_instance (i ≤ 4)
kappaNonAltN_succ_mul_Bctl_pow_le    kappa_succ_instance (j < 4)
nonAlt_hkerN                         hker_field_instance; applied: hker_applied (Xinst, M = 1, δ = W^-6, aFar)
goodSetN_A0clsN / goodSetN_driftClsN A0cls_instance / driftCls_instance (M = 0 ∈ GoodSetN, zero_mem_goodSetN_inst_grid)
nonAlt_hA0clsN / hdriftN / hDclsN    hA0cls_instance / hdrift_instance / hDcls_instance at τ = tau0;
                                     far clauses hA0cls_far_instance, hDcls_far_instance at aFar (ℓ W^{1/5} = 2 ≤ diam aFar)
nonAlt_hκ0N / hε0N / hdDrift0N       hκ0_instance / hε0_instance / hdDrift0_instance
qvBdNonAltN_pos                      qvBd_pos_instance (u_1,u_4)
qvFormN_le_of_goodSetN_shiftN        qvFormN_shift_instance (M = 0, u = 0, u' = u_1, w = u_4, hδ = delta_shift_ok 0)
hQ_nonAltN                           hQ_instance (all j < m ≤ 4, a); hQ_instance_zero (M = 0, Hermitian)
subGaussStop_nonAltN                 subGaussStop_instance (same tau0, same cQVNonAltN, every m ≤ 4, j < m, a)
cQVNonAltN_sum_pos                   hc_pos_instance (Δ = 1/128 > 0)
bundle                               gridAssemblyHyp_instance : GridAssemblyHypN sz0 (Einst 0) sig3 (gridTime …) tau0 Δ (Kg 0)
                                       (nonAltClsN …) A0f Af Dr0 0 0 0 (kappaNonAltN …) (epsNonAltN …) (W^-6)
                                       (dDriftNonAltN …) (W^-6) (cQVNonAltN …) 0 0 0
                                     fields hκ0 hε0 hker hA0cls hdDrift0 hdrift hDcls hc_pos := the instances above;
                                     hexp by `simp [Af]` for the drift-only frozen process
nonvacuity                           tau0_pos : ∀ ω, 0 < tau0 ω (azumaProxy_pos_gridExitTauN + zero_mem_goodSetN_inst_grid);
                                     bundle_fields_instance uses the bundle's hker/hA0cls/hdrift/hDcls on {0 < τ}
```
Not degenerate: `K = 4 ≥ 1`, `Δ = 1/128 > 0`, `u_K = 1/32 < 1 - g²/L²`, `W = 32`, `L = 4`, event `{0 < τ}` is everything, class nonvacuous (`Xinst_cls`, `Xinst ≠ 0`). The axioms of all instances are clean (§1). PASS.

## 5. Paper-delta coverage
Lean/paper differences and their candidates in the prove report (d):
- (5.93) as inequality with `W^{Cε}` weight vs RBM2D identity → T2167a.
- class carries `δ ≤ W^{-Dc}`, `1 < Dc ≤ D'`; `εK = W^C`; `κ = W^{Cε} r^{k-1}` → T2167b.
- shifted majorant needs `k+1 < D''`, `hδ` (so `D'' ≤ D'`), `|E| < 2` → T2167c.
- `hc_pos` needs `Δ > 0` (`s n < v n`, `K n ≠ 0`) → T2167d.
- no energy / `1 < W` in the two positivity lemmas → T2167e; drift level without additive `W^{-D'}`, index-form class lemmas → T2167f.
All expected candidates of the ticket's acceptance list are present. PASS.

## 6. Observations (no effect on statement, instance, build, axioms or delta coverage)
- O1: `|E| < 2` (not `≤ 2`) in `qvFormN_le_of_goodSetN_shiftN` and hence `hQ_nonAltN`/`subGaussStop_nonAltN` at fixed `n`; forced by merged `norm_STeeM_shiftN_le`; the consumer already has `∀ n, |E n| < 2`; listed in T2167c.
- O2: `nonAlt_hDclsN`, `nonAlt_hdDrift0N` carry `s n ≤ v n`, `v n < 1` beyond the ticket's text (needed for `u_{j+1} < 1`; implied by the consumer's `∀ n` premises).
- O3: `0 ≤ Γ` unused in three statements (kept because the ticket lists it).
- O4: two style-linter warnings (lines 24, 52 exceed 100 characters; docstring header), no error.

## Verdict
| target | verdict |
|---|---|
| 1 vocabulary (6 defs) | PASS |
| 2 (5.93) + two kernel-scale inequalities | PASS |
| 3 fields of `GridAssemblyHypN` (7 field theorems + 2 matrix-level) | PASS |
| 4 QV constant (5 theorems) and bundle | PASS |

Overall: **PASS**. No dispatcher sign-off needed.
