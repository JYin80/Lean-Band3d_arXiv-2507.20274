Auditor model: claude-opus-5-5
# T2284 audit (S3-22a, `Induction/QtNonzeroEnd`, `nzGridEndN`) — round 1, Tue Oct  6 11:29:50 UTC 2026

Branch `t/T2284` @ 40fc59f; audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2284-audit1` (detached, cache cloned from main).
Single target: `RBM.Ind.nzGridEndN` (endpoint). Verdict: **PASS**.

## 1. Statement vs the pin (check file §2) — script diff and compiled equality

```
$ sed -n '/^def T2284_nzGridEndN : Prop :=/,/(sz.Bctl n (v n)) \^ k$/p' docs/tickets/checks/T2284-check.lean | tail -n +2 > pin.txt
$ sed -n '/^theorem nzGridEndN :/,/(sz.Bctl n (v n)) \^ k := by$/p' RBM3D/Induction/QtNonzeroEnd.lean | tail -n +2 | sed 's/ := by$//' > lean.txt
$ wc -l pin.txt lean.txt; diff pin.txt lean.txt && echo IDENTICAL
      35 pin.txt
      35 lean.txt
IDENTICAL
```
Compiled check (`StmtCheck.lean` = `import RBM3D.Induction.QtNonzeroEnd` + check-file namespace `RBM.Ind.T2284Check`
verbatim, minus the shape example `STOeqQtNZ' 3` whose module `NQEndFlow` is not imported, + the lines below):
```
example : RBM.Ind.T2284Check.T2284_nzGridEndN := @RBM.Ind.nzGridEndN      -- line 75
$ lake env lean StmtCheck.lean | grep -v "depends on axioms: \[propext, Classical.choice, Quot.sound\]"; echo exit=$?
exit=0
```
Mathematical reading (against ticket "Design" / target 3): hypotheses `3 ≤ d`, `κ 𝔠 τ 𝔡 > 0`, `SizeTendsto`,
`Bandwidth 𝔠`, `WO 𝔡`, `|E| ≤ 2−κ`, `0 ≤ s ≤ t < 1`, `STCaseII s t`, `RangeCond τ t`, `k ≥ 2`, levels
`Λ ≥ 0` (eventually `≥ 1`), `Φ_i ≥ 0`, `s ≤ v ≤ t`, `ε₀, D₁ > 0`; quantifier order: `∃ ε₁ τ' D' C_K` before
`∀ Φc K`, then `∀ᶠ n`, `∃ G`; right side `N^{ε₀}(Λ^{1/2}+Φ₁+Φ₂+Φ₃)B_v^k` (degree 1, no `Φc`, no `^2`);
`Φc` occurs only inside `GoodSetN`; no `STKbound`, no `W⁻¹ ≤ (1−t)/(1−s)`, no `hWt` premise. Matches the pin.
Internal exponent choices (proof, `sed -n 1015,1075p | grep`):
```
11:  obtain ⟨κ', hκ'def⟩ : ∃ κ' : ℝ, κ' = min κ (4 / 5) := ⟨_, rfl⟩
12:  obtain ⟨Λg, hΛgdef⟩ : ∃ Λg : ℝ, Λg = 𝔡⁻¹ := ⟨_, rfl⟩
25:  obtain ⟨C, hC, hCop⟩ := nzUgen_holds d k hd hk Λg κ' hΛg hκ'
32:  obtain ⟨e0, he0def⟩ : ∃ e0 : ℝ, e0 = min ε₀ 1 := ⟨_, rfl⟩
36:  obtain ⟨D'', hD''def⟩ : ∃ D'' : ℝ, D'' = 2 * ((k : ℝ) + 2) / 𝔠 + 1 := ⟨_, rfl⟩
43:  refine ⟨e0 / 8, 1, D'' + 1, C_K, by linarith, one_pos, by linarith, hCK0, ?_⟩
```
= ticket target 0 (`ε₁ = ε₀'/8`, `τ' = 1`, `D' = D''+1`, O4 `D'' = 2(k+2)/𝔠 + 1`). Statement: **PASS**.

## 2. Hidden hypotheses, vacuity, cycles

```
$ grep -cE "^(structure|class) " QtNonzeroEnd.lean            -> 0
$ awk 'NR<1197' QtNonzeroEnd.lean | grep -nE "^(theorem|lemma|def|abbrev|structure|class|instance) "
979:theorem nzGridEndN :
$ git diff --stat $(git merge-base main t/T2284) main -- <the 9 imported Induction/Loop modules>   -> (empty)
```
All premises are explicit in the signature (no structure field); the only public declaration outside the instance
namespace is the target; all helpers are `private` with prefix `nzEnd_`. Upstream (`nzUgen_holds`, `nz_hker`,
`nz_hdriftN`, `subGaussStop_nzN`, `yMomentBounds_nzN`, `budgetNZN`, `assembledN`, `stKbound_holds`) are merged
on main and unchanged since the merge-base; the new file is not imported by any of them (new module), so no cycle.
No external hypothesis is added: `STKbound` is discharged internally. The good-walk hypothesis and the projected
initial bound are hypotheses inside the conclusion, as pinned (their probability is S3-22b's, ticket "Design").
Registry pre-check (no new unregistered premise):
```
$ lake env lean reg_before.lean   # import RBM3D + #assert_rbm_axioms          exit=0 lines=273
$ lake env lean reg_after.lean    # + import RBM3D.Induction.QtNonzeroEnd       exit=0 lines=273
$ diff reg_before.out reg_after.out
1c1
< axiom audit: 8236 theorems, 2681 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
---
> axiom audit: 8276 theorems, 2691 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
```
Only the count line differs: the premise table is unchanged. **PASS**.

## 3. Compiled nonempty instance

```
$ grep -n "^example\|^theorem nzEnd_instance\|^theorem rangeCond_tB\|^theorem window_" QtNonzeroEnd.lean
1271:theorem rangeCond_tB : szB.RangeCond (1 / 2) tB := by
1310:theorem window_nondegenerate (C_K : ℝ) (n : ℕ) :
1317:theorem window_collapsed (C_K : ℝ) (n : ℕ) : sB n = vC n ∧ gridStep sB vC (KB C_K) n = 0 := by
1487:example := assembly_instance (STIdiff sig3) (Finset.Subset.refl _)
1490:example := assembly_instance Finset.univ (Finset.subset_univ _)
1501:theorem nzEnd_instance (k : ℕ) (hk : 2 ≤ k) :
1536:theorem nzEnd_instance_collapsed (k : ℕ) (hk : 2 ≤ k) :
1570:example := nzEnd_instance 2 le_rfl
1573:example := nzEnd_instance 3 (by norm_num)
1576:example := nzEnd_instance 4 (by norm_num)
1579:example := nzEnd_instance_collapsed 3 (by norm_num)
```
`nzEnd_instance` (`:1522-1529`) applies `nzGridEndN` at `szB` (`d = 3`, `L = 4`, `N ≥ 4096`), `κ = 1`, `𝔠 = 1/6`,
`τ = 1/2`, `𝔡 = 1/10`, `E = Einst`, `s ≡ 15/16`, `t ≡ 31/32`, `v ≡ 31/32` (`s < v`, `window_nondegenerate`),
`Λ = Φ_i = Φc ≡ 1`, `ε₀ = 1/10`, `D₁ = 1`, grid `KB C_K = max 1 ⌈N^{C_K}⌉₊`; every premise is a closed term:
`szB_tendsto szB_bandwidth szB_WO hE_B sB_nonneg sB_le_tB tB_lt_one szB_caseII rangeCond_tB`, `norm_num` for the
level/order facts, `KB_ne_zero`, `KB_low`, `KB_up`; the `∀ᶠ n` is turned into a concrete `∃ n, ∃ G` with
`.exists`. No hypothesis of the theorem is left open; no `N = 0`, empty index or `False` premise. Applied at
`k = 2, 3, 4` and at the collapsed window (`v ≡ s`, separately). These declarations compile in the module build
(§4) and their axioms print clean. **PASS**.

## 4. Build, axioms, hygiene, diff scope

```
$ lake build RBM3D.Induction.QtNonzeroEnd
✔ [3846/3846] Built RBM3D.Induction.QtNonzeroEnd (8.2s)
Build completed successfully (3846 jobs).
exit=0
$ grep -c "error" build.log                                   -> 0
$ grep -E "^warning: .*QtNonzeroEnd" build.log | wc -l         -> 0
$ ls .lake/build/lib/lean/RBM3D/Induction/QtNonzeroEnd* (main cache, before build)  -> no matches (fresh build)
$ lake env lean StmtCheck.lean   (#print axioms)
'RBM.Ind.nzGridEndN' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Ind.QtNonzeroEndInst.nzEnd_instance' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Ind.QtNonzeroEndInst.nzEnd_instance_collapsed' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Ind.QtNonzeroEndInst.assembly_instance' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Ind.QtNonzeroEndInst.rangeCond_tB' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Ind.QtNonzeroEndInst.hδ_instance' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Ind.QtNonzeroEndInst.hop_instance' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Ind.QtNonzeroEndInst.H4_instance' depends on axioms: [propext, Classical.choice, Quot.sound]
$ grep -nE "\bsorry\b|\badmit\b|native_decide|^axiom|^\s*axiom |maxHeartbeats" QtNonzeroEnd.lean   -> (no output)
$ git diff --name-status main...t/T2284
A	RBM3D/Induction/QtNonzeroEnd.lean
$ grep -rn -F "nzGridEndN" RBM3D/ RBM3D.lean   (main)        -> (no output)
```
Only the sole writable file is touched; `Test/Axioms.lean` unchanged (as expected); no frozen signature edited;
no `maxHeartbeats` override. **PASS**.

## 5. Paper-delta coverage

Prove report (d) proposes `T2284a` (case-(ii) endpoint on the grid for `Q^{(A)}(𝓛−𝒦)`, every `A ⊇ I_diff(σ)`,
EK-5 kernel loss-free, `GoodSetN` at free crude level, linear right side), `T2284b` (explicit exponents, O4
`D''`; thresholds of "N large" not computed), `T2284c` (initial assumption on the projected loops,
`(normQA2)` left to S3-22b), `T2284d` (collapsed window), `T2284e` (one event `G` for all pairs `(σ, A)`,
per-time statement S3-22b's). These cover every Lean/paper difference visible in the signature (conditional
good-walk form, projected initial hypothesis, free `Φc`, explicit exponents, collapsed window, union). **PASS**.

## Observations (no verdict effect)

- O1. The check file's shape example `STOeqQtNZ' 3` needs `NQEndFlow`, which the new module does not import (the
  ticket forbids it); the audit statement script dropped that one line. Pin text and equality `example` unaffected.
- O2. The worktree's root `RBM3D.olean` is main's (e7d495b), cloned with the cache; the registry pre-check
  therefore ran against main's library plus the new module, which is the merge configuration.
- O3. The good-walk hypothesis is not made non-vacuous here (by design: S3-22b intersects with
  `GridGoodNConcl`/`NQLinConcl`); the instance discharges every deterministic premise.

## Verdict

| Target | Statement | Hidden/vacuity/cycle | Instance | Build/axioms | Paper deltas | Verdict |
|---|---|---|---|---|---|---|
| `nzGridEndN` | pin identical, compiled | none | `nzEnd_instance` k=2,3,4 + collapsed | ok | T2284a–e | **PASS** |

No dispatcher sign-off needed.
