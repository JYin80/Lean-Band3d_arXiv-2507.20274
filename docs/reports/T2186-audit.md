Auditor model: claude-opus-5-5

# T2186 audit (round 1) — Mon Oct  5 16:05:24 UTC 2026

Branch `t/T2186` at 5a9f3c2 (author Jun Yin), audit worktree `RBM3D-wt/T2186-audit1` (detached). Scratch: `$SCR/T2186/audit/`
(`cmp.py`, `mk.py`, `AuditT2186.lean`, `build.log`, `assert.lean/.out`, `n12.lean`).

## 1. Diff scope and hygiene
```
$ git diff --stat main...t/T2186
 RBM3D/Induction/NQLin.lean       | 1775 ++++++
 RBM3D/Induction/Step34PinsP.lean |  220 +++++
 RBM3D/Test/Axioms.lean           |    1 +
$ git diff main...t/T2186 -- RBM3D/Test/Axioms.lean   (hunk @@ -111,6 +111,7 @@ def owedProps)
+   `RBM.Gauss.Sizes.STOeqNQ', -- `lem:STOeq_NQ`, primed (DECISIONS §62): S3-12c
$ git diff main...HEAD --stat -- Induction/{Step34Pins,GridGoodN,NQGood1,NQGood2,NQBudget}.lean | wc -l  ->  0
$ grep -nE "sorry|admit|native_decide|^axiom|maxHeartbeats|set_option" NQLin.lean Step34PinsP.lean
Step34PinsP.lean:31:set_option linter.style.longLine false
NQLin.lean:43-45: set_option linter.style.longLine / unusedSectionVars / unusedVariables false
NQLin.lean:959:set_option maxHeartbeats 400000 in        (budgetNonAltLinN)
$ grep -n "^import" ...   Step34PinsP: RBM3D.Induction.Step34Pins only;  NQLin: NQBudget, NQGood2, GridGoodN, SEforLn2, AzumaProxyN
$ git diff 0818c49 main -- RBM3D/Test/Axioms.lean | grep "^@@"     (main moved since the branch base)
@@ -118,7 +118,6 @@   @@ -160,7 +159,6 @@          (two deletions, not adjacent to the added line 114)
```
Only the three sole writable files; exactly one registry line added; `STOeqNQ` (`:113`) kept; imports as the ticket requires.

## 2. Build and axioms (audit worktree; artifacts of the two new modules deleted first)
```
$ lake build RBM3D.Induction.Step34PinsP RBM3D.Induction.NQLin   (Mon Oct  5 16:02:02 .. 16:02:23 UTC 2026)
ℹ [3841/3842] Built RBM3D.Induction.Step34PinsP (5.7s)
ℹ [3842/3842] Built RBM3D.Induction.NQLin (17s)
Build completed successfully (3842 jobs).   exit 0
$ grep -E "(NQLin|Step34PinsP)\.lean.*depends on axioms" build.log | <axiom list> | sort | uniq -c
  34 [propext, Classical.choice, Quot.sound]
(no other info/warning/error line from the two files)
$ lake build RBM3D   (branch root, Mon Oct  5 16:03:57 UTC 2026) -> Build completed successfully (3995 jobs). exit 0
$ lake env lean assert.lean   [import RBM3D + both new modules + #assert_rbm_axioms]   assert exit 0
axiom audit: 5612 theorems, 2021 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
  RBM.Gauss.Sizes.STOeqNQ': 2 [no certificate]
premises found by scanning: 110 (borrowed 1, owed 86, structural 23).
registry: 2 borrowed + 128 owed + 58 structural; 78 registered premise(s) carry nothing yet: [... RBM.Gauss.Sizes.STOeqNQ', ...]
$ grep -niE "error|warn|unregist" assert.out   ->  (no lines)
```

## 3. Statements against the pins (check file `docs/tickets/checks/T2186-check.lean`, §2–§4)
Text identity of the 11 pinned definitions (`python3 cmp.py`, the def block of the check file vs the branch file):
```
STNQConcl'  file=P identical=True lines=13 | STOeqNQ' P True 1 | GoodLinN N True 8 | nqLinPhi1 N True 1
nqLinPhi2 N True 4 | nqLinPhi3 N True 1 | NQLinConcl N True 16 | NQLinGood N True 1 | dDriftLinN N True 2
nqLinExitTauN N True 5 | assembledRHSLinN N True 15
```
Definitional identity and the section-4 statements, compiled independently (`python3 mk.py`: the check file with
`import RBM3D.Induction.{Step34PinsP,NQLin}` added, every pinned name in §2–§4 renamed `*_C`, then):
```
example : @RBM.Gauss.Sizes.STNQConcl' = @STNQConclP_C := rfl        -- and the 10 other pinned defs, all `rfl`
example : T2186_stOeqNQ'_of_stOeqNQ := @RBM.Gauss.Sizes.stOeqNQ'_of_stOeqNQ
example : T2186_measurableGoodLinN := @RBM.Gauss.Sizes.measurableGoodLinN
example : T2186_goodSetN_subset_goodLinN := @RBM.Gauss.Sizes.goodSetN_subset_goodLinN
example : T2186_nqLinGood_holds := @RBM.Gauss.Sizes.nqLinGood_holds
example : T2186_dDriftNonAltN_eq_lin := @RBM.Ind.dDriftNonAltN_eq_lin
example : T2186_driftTensorN_norm_le_of_goodLin := @RBM.Ind.driftTensorN_norm_le_of_goodLin
example : T2186_nqLin_hdriftN := @RBM.Ind.nqLin_hdriftN
example : T2186_nqLinExitMeasN := @RBM.Ind.nqLinExitMeasN
example : T2186_subGaussStop_linN := @RBM.Ind.subGaussStop_linN
example : T2186_budgetNonAltLinN := @RBM.Ind.budgetNonAltLinN
$ lake env lean AuditT2186.lean   (Mon Oct  5 16:03:11 UTC 2026)   exit 0, no error lines; printed:
'RBM.Gauss.Sizes.stOeqNQ'_of_stOeqNQ' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.nqLinGood_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Ind.budgetNonAltLinN' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Ind.subGaussStop_linN' depends on axioms: [propext, Classical.choice, Quot.sound]
```
Private target 1(b) (cannot be named outside the file): the in-file `example : <type> := @stNQConcl'_of_stNQConcl`
(`Step34PinsP.lean:150`, compiled with the module) against the pin:
```
pin : ∀ {d : ℕ} (sz : Sizes d) (E s t : ℕ → ℝ), sz.SizeTendsto → (∀ n, t n < 1) → STNQConcl sz E s t → STNQConcl' sz E s t
file: ∀ {d : ℕ} (sz : Sizes d) (E s t : ℕ → ℝ), sz.SizeTendsto → (∀ n, t n < 1) → STNQConcl sz E s t → STNQConcl' sz E s t
identical: True
```
`STNQConcl'` vs merged `STNQConcl`: since `STNQConcl'` is the check-file text verbatim (above), the three edits are the
dispatcher's pin (prove report (b), `diffnq.py`: `m + 1 ≤ n_ ↦ m ≤ n_`; `fun n q ω ↦ fun n q _` and `STsupXiLK … ↦ XLK n_ n`
on one line). The pin is the RBM2D `STOeqPT` form chosen by Jun (DECISIONS §62 (1)); it is a primed successor, the merged
`STNQConcl`/`STOeqNQ`/`inst_OeqNQ` are unchanged (§1 above). `tbDriftLinN`, `mem_of_lt_nqLinExitTauN` are "statement
free" in the ticket; their statements (prove report (b)) match the ticket's mathematics (drift term
`≤ W^{Cε}Γ²((k−2)Φ₁+Φ₂+Φ₃)B_v^k Σ Δ/η + (KΔ)(W^C W^{−D'})`; membership in `GoodSetN ∩ GoodLinN` before exit).

## 4. Hidden hypotheses, vacuity, cycles
- No structure carries a hypothesis: all new objects are `def … : Prop`/`Set`/`ℝ`/`ℕ`, identical to the pins.
- `STNQConcl` and `STSEforLnConcl` occur only in private theorems; the registry scan (§2) reports no unregistered
  premise; `STOeqNQ'` is owed (S3-12c) and is concluded by `stOeqNQ'_of_stOeqNQ` from the owed `STOeqNQ` — a reduction
  between two registered owed pins, not a cycle (no theorem proves either).
- `nqLinGood_holds` rests on the merged `stSEforLn_holds`; `subGaussStop_linN` on merged `azumaProxy_subG_ugen`,
  `hQ_nonAltN`; budget on merged `tbInitNonAltN`, `tbQvNonAltN`, `kappaNonAltN_succ_mul_Bctl_pow_le`. No new external input.
- Non-vacuity of `NQLinConcl`: `nqLinGood_instance_nonempty` (`∀ᶠ n, ∃ ω`, every `j ≤ 4` in `GoodLinN`).
- `nqLinPhi*` ranges at small `k` (`lake env lean n12.lean`): `#eval (STn12 3, STn12E 2, STn12E 3, STn12E 4)` →
  `((1, 3), (1, 3), (3, 3), 3, 5)`; so at `k = 4` the (D2') term is `XLK 3·(XL 1·XL 3)^{1/2}` (lengths in range).

## 5. Compiled nonempty instances (all compiled in the module build of §2)
| endpoint | instance (file:line) | data / open hypotheses |
|---|---|---|
| `stOeqNQ'_of_stOeqNQ`, `inst_OeqNQ'` | `Step34PinsP` `example (h : STOeqNQ 3) := inst_OeqNQ' (stOeqNQ'_of_stOeqNQ 3 h) 1 one_pos` (:196), applied conclusion (:201) | `sz0, z0`, `d=3, L=4, W=32`, window `[0,1/16]`; open: owed `STOeqNQ 3` and pins `STKbound, STKward, STLK, STStep2Concl` |
| private 1(b) | `Step34PinsP` :209 | `sz0_tendsto`, `t ≡ 1/16 < 1` discharged; `STNQConcl` hypothesis |
| `measurableGoodLinN`, `goodSetN_subset_goodLinN`, `dDriftNonAltN_eq_lin` | `NQLin` :1348, :1352, :1356 | `sz0`, `k=3`, `Γ=4`, `Φ=(1,12,1)` |
| `driftTensorN_norm_le_of_goodLin` | `drift_lin_instance` :1361 + `dDriftLinN_inst_pos` :1367 | `H=0 ∈ GoodLinN` (`zero_mem_goodLinN_inst`), positive level |
| `nqLin_hdriftN`, `mem_of_lt_…`, `nqLinExitMeasN` | :1376, :1387, :1395 | exit time `= tau0`, `0 < nqLinExitTauN ω` (:1314, :1331) |
| `subGaussStop_linN` | `subGaussStop_lin_instance` :1403 | every hypothesis discharged (`NQGood2Inst` data) |
| `nqLinGood_holds` | `nqLinGood_instance` :1428 (`k ≥ 2`), `k = 2, 4` :1483/:1488, `_nonempty` :1454 | `XL≡XLK≡1`, `ε=1/10`, `K≡4`, `v≡1/32`; `hX`,`hY` discharged from `STLmaxU`,`STLKU`; open: pins `STKbound…STLKU` (as merged `gridGood_instance`) |
| `tbDriftLinN` | `NQLin` :1698 | all hypotheses discharged |
| `budgetNonAltLinN` | `budgetNonAltLinN_instance` :1724 | all 24 hypotheses discharged; `ε₀ = C + 12` (see Obs. 1) |

No `N = 0`, empty index, collapsed window or `False` premise: `N = 2^21`, window `[0,1/32] ⊂ [0,1/16]`, `K = 4`,
`Fin 3` labels, `k = 4` makes (D1') and the (D2') sum non-empty.

## 6. Paper-delta coverage
Lean/paper differences and their candidates (prove report (d)): primed pin with deterministic self-term `B^{1/6}XLK n_`
and hypothesis at the current length (`T2186a`); separate deterministic levels in `GoodLinN`, `GoodSetN` at a crude level
(`T2186b`); `ε/3` split (`T2186c`); controls on `[s,v]`, `B_v^{1/6}` in `Φ₂` (`T2186d`); `ha2` with `Γ²` and degree-1
conclusion (`T2186e`). These cover the three the ticket expects plus the window/`B_v` and budget-shape deltas. Complete.

## 7. Observations (no RETURN)
1. `budgetNonAltLinN_instance` uses `ε₀ = C + 12` (`N^{ε₀} ≈ 10^{76}`), the data the ticket prescribes ("at the data of
   `budgetNonAltN_instance`"); the regime `ε₀ = 1/10` is covered only by the preflight table (row 10: `ha2'` holds from
   `log₁₀ N ≥ 48.6/51.5/56.2`, `k = 2/3/6`). The hypotheses are consistent at the data; S3-12b must discharge `ha2`–`ha3`
   `∀ᶠ n` at small `ε₀`.
2. Ticket preflight (iii) says the `k = 4` lengths are `XLK 3, XL 2`; the `#eval` above gives `XL 1, XL 3`
   (the prover's correction in (a) is right). Prose only.
3. `set_option maxHeartbeats 400000 in` on `budgetNonAltLinN` (disclosed in the report); not a hygiene violation.
4. `RBM3D/Test/Axioms.lean` on `main` lost two lines (`:118`, `:160`) after the branch base 0818c49; the hunks do not
   touch the added line 114, so the one-line registry merge applies cleanly.

## Verdict
| target | verdict |
|---|---|
| 1 `STNQConcl'`, `STOeqNQ'`, private `stNQConcl'_of_stNQConcl`, `stOeqNQ'_of_stOeqNQ`, `inst_OeqNQ'` | PASS |
| 2 `GoodLinN`, `measurableGoodLinN`, `goodSetN_subset_goodLinN` | PASS |
| 3 `NQLinConcl`, `NQLinGood`, `nqLinGood_holds` | PASS |
| 4 `dDriftLinN`, `nqLinExitTauN`, `dDriftNonAltN_eq_lin`, `driftTensorN_norm_le_of_goodLin`, `nqLin_hdriftN`, `mem_of_lt_nqLinExitTauN`, `nqLinExitMeasN`, `subGaussStop_linN` | PASS |
| 5 `assembledRHSLinN`, `tbDriftLinN`, `budgetNonAltLinN` | PASS |

Overall: **PASS**. No dispatcher sign-off needed.
