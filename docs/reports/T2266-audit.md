Auditor model: claude-opus-5-5

# T2266 audit (round 1): UN-18 EMCTE2 half (branch t/T2266 @ 709ba21)

Date (date -u): Tue Oct  6 07:26:21 UTC 2026. Audit worktree: `/Users/junyin/Lean_proof/RBM3D-wt/T2266-audit1` (detached at 709ba21).
Scratch: `<scratchpad>/T2266/` (`scratch.lean`, `precheck.lean`, `build.out`, `full.out`, `precheck.out`).

## 1. Scope of the diff
```
$ git diff --stat main...t/T2266        # merge-base c01b292
 RBM3D/Test/Axioms.lean         |   2 -
 RBM3D/Universality/EMCTE2.lean | 778 +++++++++++++++++++++++++++++++++++++++++
$ git diff main...t/T2266 -- RBM3D/Test/Axioms.lean | grep '^[-+] '
-   `RBM.Univ.UNEMCTE2, -- bulk universality pin (T2162 portmap P.4; T2174, UN-01: owed)
-   `RBM.Univ.UNEMCTE2Row, -- bulk universality pin (T2162 portmap P.4; T2174, UN-01: owed)
```
Only the two sole writable files. EMCTE2.lean is a new file, so no merged or frozen signature changes. The registry change is exactly the two deletions the ticket asks for, and no line is added.

## 2. Statements against the ticket pins (check file sections 2.1-2.5)
The scratch file is `import RBM3D.Universality.EMCTE2` + check-file Mathlib imports (lines 18-23) + check-file lines 103-178 verbatim + the examples below:
```
example : T2266_eq225_interval := @RBM.Univ.eq225_interval
example : T2266_unEMCTE2_of_sizeTendsto := @RBM.Univ.unEMCTE2_of_sizeTendsto
example : T2266_unEMCTE2Row := RBM.Univ.unEMCTE2Row
example : T2266_unEMCTE2Rowk_band := RBM.Univ.unEMCTE2Rowk_band
example : T2266_inst_eq225_interval := RBM.Univ.EMCTE2Inst.inst_eq225_interval
example : T2266_inst_unEMCTE2_sz0 := RBM.Univ.EMCTE2Inst.inst_unEMCTE2_sz0
example : T2266_inst_unEMCTE2Row_sz0 := RBM.Univ.EMCTE2Inst.inst_unEMCTE2Row_sz0
$ lake env lean <scratch>/T2266/scratch.lean ; echo exit $?
exit 0
```
All 4 targets and 3 instances have the pinned statements. Lean elaborates each one against the dispatcher's pin text.
Signature heads (from `EMCTE2.lean:455-457, 597-598, 683, 690`):
```
theorem eq225_interval (d : ℕ) (sz : Sizes d) (n nf : ℕ) (z : Fin nf → ℂ)
    (hz : ∀ i : Fin nf, 0 < (z i).im) (t T Bd : ℝ) (ht : 0 ≤ t) (htT : t ≤ T) (hB : ∀ s ∈ Set.Ioo t T, ∫ … ≤ Bd) : |…| ≤ (1 / 2) * (T - t) * Bd
theorem unEMCTE2_of_sizeTendsto (d : ℕ) (sz : Sizes d) (hd : sz.SizeTendsto) (E : ℝ) (nf : ℕ)
    (τU Cn : ℝ) (hτ : τU ≤ Cn * τU) : UNEMCTE2 sz E nf τU Cn
theorem unEMCTE2Row : UNEMCTE2Row
theorem unEMCTE2Rowk_band : UNEMCTE2Rowk (fun d => UNKind.band d)
```
- Target 1: the hypotheses are only `0 < Im z_i`, `0 ≤ t ≤ T` and the real integral bound `hB` on `Ioo t T`. The constant is ½ with no loss. The carrier is the band carrier `ouP (UNModel.band sz) n`. The coupling `sz.lam n` is the same in `L1t`/`L2t` and the flow.
- Target 2: the conclusion is the merged `UNEMCTE2` (`Pins.lean:669`) unchanged: `∀ C₀ ε > 0, ∀ᶠ n, ∀ z ∈ window, ∀ B ≥ 0, hB1 → hB2 → ∀ t ∈ [0,t*], |…| ≤ N^ε N^{-1+Cn τU} B`. It adds two hypotheses, `sz.SizeTendsto` and `τU ≤ Cn τU`, which the ticket pins (T2266a (1)). This is a conditional form of the pin. The ticket designates it as the target, and every consumer reaches the pin through `UNEMCTE2Row`/`UNClaimRow`, where `Admissible` supplies `SizeTendsto`.
- Targets 3 and 4: the merged row definitions are closed propositions (`Pins.lean:797`, `PinsK.lean:429`) with no extra premise.

Verdict on statements: all match their pins.

## 3. Vacuity, hidden hypotheses, cycles
- No new structure or `def` premise. The only new `def` is `private def EMCTE2_BM` and `private def EMCTE2_hsum` (`:66`, `:245`), which are helper predicates and functions, not hypotheses of any target.
- Target premises:
  - `SizeTendsto` is structural (`Axioms.lean`, structural list). It is discharged concretely at `sz0` by `sz0_tendsto`, where `N(n) = 2^21 (n+1)^18 → ∞`; this is the limit check.
  - `τU ≤ Cn τU` holds at `Cn = 1`.
  - `hB`/`hB1`/`hB2` are real inequalities, not `Prop` definitions.
- Imports are only merged modules (`EMCTE2.lean:6-13`): OUGenerator, OUContraction, OUHessian, PinsK, InjSum, Path.Walk, Gauss.FlowCalculus, Induction.Split. There is no `RBM3D`, `BA/*` or `Graph/*` import, so there is no cycle.
- Registry pre-check (scratch = the worktree `RBM3D.lean` import lines + `import RBM3D.Universality.EMCTE2` + `#assert_rbm_axioms`):
```
$ lake env lean <scratch>/T2266/precheck.lean ; echo exit $?
exit 0
axiom audit: 7765 theorems, 2576 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
premises found by scanning: 153 (borrowed 1, owed 95, structural 40, refuted 6, superseded 11).
$ grep -o "RBM.Univ.UNEMCTE2[A-Za-z]*" precheck.out | sort | uniq -c
   1 RBM.Univ.UNEMCTE2k
   1 RBM.Univ.UNEMCTE2RowBA
   2 RBM.Univ.UNEMCTE2Rowk
```
Neither `UNEMCTE2` nor `UNEMCTE2Row` appears any more as a premise without a certificate. The kept lines `UNEMCTE2k`, `UNEMCTE2Rowk` and `UNEMCTE2RowBA` remain owed, as the ticket specifies.
Without the root import, the full build fails as expected. This is the hub's merge step (§3 (A) 4) and not a defect:
```
$ lake build   # audit worktree, RBM3D.lean unchanged
error: RBM3D.lean:309:0: axiom audit: 1 premise(s) that no theorem of this development proves are in none of …
  [RBM.Univ.UNEMCTE2Row]
```

## 4. Compiled nonempty instances (EMCTE2.lean:706-765, namespace RBM.Univ.EMCTE2Inst)
- `inst_eq225_interval` (target 1) uses `sz0`, `d = 3`, `n = 0` (`L = 4`, `W = 32`, `N = 2^21`), `nf = 1`, `z = ![I]`, `t = 0 < T = 1`.
  - `hz` is proved by `fin_cases; simp`, `ht` by `le_rfl` and `htT` by `zero_le_one`.
  - `hB` is discharged inside the proof. `K` comes from `EMCTE2_hsum_bdd`, a uniform bound of the kernel sum over Hermitian matrices at fixed `z`. Then `integral_mono` with `measurable_ouMat`, `ouMat_isHermitian`, `integrable_const` gives `∫ … ≤ K`.
  - It ends in `exact ⟨K, hB, eq225_interval 3 sz0 0 1 ![Complex.I] hz 0 1 K le_rfl zero_le_one hB⟩`.
  - No hypothesis is left open. The index set is nonempty and the window has positive length.
- `inst_unEMCTE2_sz0` (target 2): `unEMCTE2_of_sizeTendsto 3 sz0 sz0_tendsto 0 2 (1 / 2) 1 (one_mul _).ge`, with `nf = 2` and `τU = 1/2`.
- `inst_unEMCTE2Row_sz0` (target 3): `d = 3`, `𝔠 = 1/6`, `𝔡 = 1/10`, `UNInst.sz0_adm`, `κ = 1/2`, `E = 1` (`|1| ≤ 3/2` by `norm_num`), `nf = 2`. It is then specialised at the returned `τ₀` (`0 < τ₀`, `le_rfl`).
- `inst_unEMCTE2Rowk_band_sz0` (target 4): the same data, with the bulk premise `∀ᶠ n, |1| ≤ 2 - 1/2` from `Eventually.of_forall … norm_num`.

All four compile (section 5), and none keeps a premise.

## 5. Build, axioms, hygiene (audit worktree)
```
$ lake build RBM3D.Universality.EMCTE2 ; echo exit $?
exit 0
Build completed successfully (3370 jobs).
$ grep warning build.out | grep EMCTE2
warning: RBM3D/Universality/EMCTE2.lean:20:100: This line exceeds the 100 character limit,
warning: RBM3D/Universality/EMCTE2.lean:24:100: This line exceeds the 100 character limit,
warning: RBM3D/Universality/EMCTE2.lean:34:100: This line exceeds the 100 character limit,
warning: RBM3D/Universality/EMCTE2.lean:36:100: This line exceeds the 100 character limit,
$ grep "EMCTE2.lean.*depends on axioms" build.out
'RBM.Univ.eq225_interval' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.unEMCTE2_of_sizeTendsto' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.unEMCTE2Row' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.unEMCTE2Rowk_band' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.EMCTE2Inst.inst_eq225_interval' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.EMCTE2Inst.inst_unEMCTE2_sz0' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.EMCTE2Inst.inst_unEMCTE2Row_sz0' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.EMCTE2Inst.inst_unEMCTE2Rowk_band_sz0' depends on axioms: [propext, Classical.choice, Quot.sound]
$ grep -nE "sorry|admit|native_decide|^\s*axiom " RBM3D/Universality/EMCTE2.lean | wc -l
0
$ lake build RBM3D.Test.AuditNegative ; echo $?
0
$ for n in eq225_interval unEMCTE2_of_sizeTendsto unEMCTE2Row unEMCTE2Rowk_band EMCTE2Inst; do git grep -nw $n main -- RBM3D RBM3D.lean | wc -l; done
eq225_interval:0 unEMCTE2_of_sizeTendsto:0 unEMCTE2Row:0 unEMCTE2Rowk_band:0 EMCTE2Inst:0
```
- The `private` helpers carry the `EMCTE2_` prefix, which satisfies §3 (E).
- The public names are exactly the four targets plus the instances in `EMCTE2Inst`.

## 6. Paper deltas
- The only Lean/statement difference from a merged pin is target 2's extra hypotheses, `sz.SizeTendsto` and `τU ≤ Cn τU`. It is covered by candidate **T2266a (1)** in the prove report (d).
- T2266a (2) is the BA-kind design correction. The prover has proposed it and says it is unchecked; it is not a statement of this branch.
- T2266a (3) records that the band-kind generic row is proved.
- Target 1 is RBM2D `eq225_interval` on the RBM3D band carrier, with the same constant ½. It introduces no new paper delta.

Coverage is complete.

## 7. Observations (no effect on verdict)
- O1: Preflight (a)(ii) uses `Bd = 8` for the target-1 instance. The compiled instance instead takes `Bd = K`, an existential bound from `EMCTE2_hsum_bdd`. That is the `∃ Bd` form of check 2.5. `K` is a genuine finite bound, and `hB` is proved from it, not assumed.
- O2: There are 4 long-line linter warnings in the module docstring (`:20, :24, :34, :36`). They are style only.
- O3: Before the hub adds `import RBM3D.Universality.EMCTE2` to `RBM3D.lean` (after `OUGenerator`), the full `lake build` fails on `UNEMCTE2Row`. This is expected. With the import, the registry pre-check above passes.

## Verdicts
| target | verdict |
|---|---|
| 1 `eq225_interval` | PASS |
| 2 `unEMCTE2_of_sizeTendsto` | PASS (conditional form pinned by the ticket; T2266a (1)) |
| 3 `unEMCTE2Row` | PASS |
| 4 `unEMCTE2Rowk_band` | PASS |
| 5 instances (`EMCTE2Inst.*`) | PASS |

**Overall: PASS.** No dispatcher sign-off needed.
