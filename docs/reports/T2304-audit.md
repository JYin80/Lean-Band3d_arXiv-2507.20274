Auditor model: claude-opus-5-5

# T2304 audit (round 1) — S3-22c bootstrap + `stOeqQtNZ'_holds`

Written Tue Oct  6 15:25:26 UTC 2026 (`date -u`). Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2304-audit1`,
detached at `8e4bfe8` (= `t/T2304` head). Scratch: `<scratchpad>/T2304/` (`stmt_audit.lean`, `regcheck.lean`, logs).

## 1. Diff scope
```
$ git diff --stat main...t/T2304
 RBM3D/Induction/QtNonzeroBoot.lean | 1264 ++++++++++++++++++++++++++++++++++++
 RBM3D/Test/Axioms.lean             |    6 +-
```
Both are the ticket's sole writable files. Registry hunk (verbatim, `Test/Axioms.lean:124-126`): the `STXiBoot'` and
`STOeqQt'` comments extended exactly as the ticket asks; the `STOeqQtNZ'` line replaced by
`` `RBM.Gauss.Sizes.STXiRound', -- one round of `(am;asoi222)` with the current-length control (T2304); premise of ...``.
No merged pin touched (`STXiBoot'`, `STOeqQtNZ'`, `STOeqQt'`, `STNZConcl''`, `STIngR`, `STNewPQ` are in untouched files).
```
$ for r in main t/T2304: owedProps entries (awk over `def owedProps`)  ->  main 143, t/T2304 143   (net 0)
  main:   126: `RBM.Gauss.Sizes.STOeqQtNZ', ...        t/T2304: 126: `RBM.Gauss.Sizes.STXiRound', ...
```

## 2. Statements (script diff / compiled `example`s)
Pin body vs check file §2, and vs merged `STXiBoot'` (`NQEndFlow.lean:96-103`):
```
== diff check§2 body vs file body (QtNonzeroBoot.lean:93-101)
exit=0
== diff STXiBoot' body vs STXiRound' body
5c5
<     (∀ m, 1 ≤ m → m + 1 ≤ n_ →
---
>     (∀ m, 1 ≤ m → m ≤ n_ →
8c8,9
<       (fun n q _ => STbootRHS 1 (fun m => XL m n q.1.2) (fun m => XLK m n q.1.2) (sz.Bctl n (s n)) n_ p)
---
>       (fun n q _ => (sz.Bctl n q.1.2) ^ (1 / 6 : ℝ) * XLK n_ n q.1.2 +
>         STbootRHS 1 (fun m => XL m n q.1.2) (fun m => XLK m n q.1.2) (sz.Bctl n (s n)) n_ p)
```
Exactly the two allowed hunks. Pin sits in `namespace RBM.Gauss.Sizes`, `section Pins` (file lines 78-105).

`stmt_audit.lean` = `import RBM3D.Induction.QtNonzeroBoot` + the check file's §3 `T2304_*` defs copied verbatim by
`awk` (so `STXiRound'` resolves to the **library** pin) + these examples:
```
example : T2304_stBoot_rounds := @RBM.Ind.stBoot_rounds
example : T2304_stXiBoot'_of_round := @RBM.Ind.stXiBoot'_of_round
example : T2304_stXiBootR_of_round := @RBM.Ind.stXiBootR_of_round
example : T2304_stXiRoundNZ_holds := @RBM.Ind.stXiRoundNZ_holds
example : T2304_stOeqQtNZ'_holds := @RBM.Ind.stOeqQtNZ'_holds
example : T2304_consumer_II := fun d h => RBM.Ind.stXiBootR_of_round d STCaseII h
example : T2304_consumer_I := fun d h => RBM.Ind.stXiBootR_of_round d STCaseI h
$ lake env lean stmt_audit.lean ; echo exit=$?
exit=0      (only output: an unused-variable linter warning on my own trivial line 58, and)
'RBM.Ind.stOeqQtNZ'_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
```
All five pinned statements and both consumer shapes match the ticket exactly (definitional, by term ascription).
Hypotheses/quantifier order: fixed parameters (`κ ε 𝔡 Cd`) then `∃ 𝔠d` then setting then `Prec` (`∀ᶠ n` inside),
as in the merged `STIngR` (`Step34Pins.lean:445-453`); `stXiBoot'_of_round` takes `3 ≤ d`, `0<κ`, `0<ε`, `STFlow`,
`0 ≤ s < t ≤ lemT z` and the round — the check's type, no extra premise. Contraction exponent is
`qtBoot_c 𝔠 𝔡 ε := min (2 * 𝔡 * 𝔠) (ε / 2) / 12` (`:229`), a function of `(𝔠,𝔡,ε)` only (n-free, regime-free);
`qtBoot_contraction` (`:246`) premises: `Admissible 𝔠 𝔡`, `0<ε`, `t<1`, `RangeCond (ε/2) t` — no `STConStInd`,
no regime predicate. Crude start `qtBoot_crude` (`:337`) at `C₀ = 2 n_ + 1`.

## 3. Hidden hypotheses, vacuity, cycles
- Public declarations (grep `^(theorem|def|...)` minus `private`): `STXiRound'`, `stBoot_rounds`, `stXiBoot'_of_round`,
  `stXiBootR_of_round`, `stXiRoundNZ_holds`, `stOeqQtNZ'_holds`, `inst_OeqQtNZ'`, `inst_RoundNZ`; 27 `private` decls.
  No structure/class introduced; no hypothesis in a structure field.
- `stXiRoundNZ_holds : ∀ d, STIngR d STCaseII (… STXiRound' …)` and `stOeqQtNZ'_holds : ∀ d, STOeqQtNZ' d` are closed
  terms (no theorem-level hypotheses); their premises are `STIngR`'s binders (`STKbound`, `STKward`, `STLK s`,
  `STConStInd`, `STStep2Concl`, regime), the same as every merged ingredient pin.
- `STXiRound'` is a new pin, registered in `owedProps` (§90); it is proved here for case (ii) — not vacuous.
  Cycle: none — `stOeqQtNZ'_holds := stXiBootR_of_round d STCaseII (stXiRoundNZ_holds d)` (`:1074`), and
  `stXiRoundNZ_holds` uses the merged `stOeqNZ''_holds` (`QtNonzeroFlowLift`, 2cf288c); imports are merged modules only
  (`:6-19`: QtNonzeroFlowLift, NQEndFlow, NQEndFlowLift, NewPQ, ZeroModeCalc, NQGood1, GridGoodN, KDecay, Step6Kit,
  ExpWardII, ContinuityNet, ScaleFacts3, Step2Events, Green/Pins).
- Registry pre-check (`regcheck.lean` = `import RBM3D` + `import RBM3D.Induction.QtNonzeroBoot` + `#assert_rbm_axioms`,
  after `lake build RBM3D` in the audit worktree):
```
root build exit=0
Build completed successfully (4111 jobs).
regcheck exit=0
1:axiom audit: 8653 theorems, 2829 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
31:  RBM.Gauss.Sizes.STXiBoot': 7 [no certificate]
33:  RBM.Gauss.Sizes.STXiRound': 4 [no certificate]
153:premises found by scanning: 152 (borrowed 1, owed 93, structural 41, refuted 6, superseded 11).
154:registry: 2 borrowed + 144 owed + 105 structural + 7 refuted + 12 superseded; ...
```
  `found` 152 = the report's pre-change value (not larger); `STOeqQtNZ'` no longer listed as a found premise; no new
  unregistered premise (exit 0); `stOeqQtNZ'_holds` not flagged.

## 4. Compiled nonempty instances (`namespace RBM.Ind.QtNonzeroBootInst`, `:1085-1251`; all compile in the build)
Data: merged `szB` (d = 3, L = 4, W = n+4, N = (4W)^3 ≥ 4096), `zB`, `flow_zB` at κ = ε = 𝔡 = 1/10, 𝔠 = 1/6,
`s ≡ 15/16`, `t ≡ 31/32`, `C_d = 1`. Nondegenerate (N ≥ 4096, s < t, nonempty `STPair`, no `False` premise).
| ticket instance | file | deterministic hypotheses discharged | left as hypotheses |
|---|---|---|---|
| (1) `inst_OeqQtNZ'` from `inst_ing STCaseII … (stOeqQtNZ'_holds 3)` | 1092 | flow, `0≤s<t≤lemT` (`szB_flow_ht`), `szB_caseII`, `conStInd_const` ∀𝔠d, `Cd=1` | `STKbound/STKward/STLK/STStep2Concl` inside `InstIngConcl` (other pins) |
| (1') applied at n_=3, p=1, XL≡XLK≡1 | 1111 | `STKbound`, `STKward` from `flow_zB` | `STLK s`, `STStep2Concl`, pair `Ξ̂ ≺ 1` |
| (2) `inst_RoundNZ` / (2') applied | 1100 / 1129 | as (1) | as (1') |
| (3) `stBoot_rounds`, U=Unit, ξ≡1, R≡1, c=1, C₀=0 | 1148 | all (SizeTendsto, crude, round) | none |
| (3') c=1/360, C₀=5, R≡2; (3'') random ξ = 1+|sin ω| (nonconstant, `obsB_nonconst`) | 1160 / 1188 | all | none |
| (4) contraction unfolded, c = 1/360 | 1209 | `Admissible`, `t<1`, `RangeCond` via `v3_premises_of_stFlow` | none |
| (4') `qtBoot_crude` at n_=3 (Ξ̂ ≺ N^7) | 1220 | all | none |
| (5) `stXiBoot'_of_round` at (szB,zB,15/16,31/32) | 1226 | all deterministic | `STXiRound'` (the round pin) |
| (6) consumers I/II; (6') `stXiBootR_of_round 3 STCaseII (stXiRoundNZ_holds 3)` | 1233/1236/1248 | — | — |
| (7) `∀ d, STOeqQtNZ' d`; `STOeqQtNZ' 3`; `rfl` unfolding | 1241/1243/1245 | — | — |
Every endpoint theorem has an instance; every deterministic hypothesis is discharged at concrete data.

## 5. Build and axioms (audit worktree)
```
$ lake build RBM3D.Induction.QtNonzeroBoot ; echo exit=$?
ℹ [3890/3890] Built RBM3D.Induction.QtNonzeroBoot (7.7s)
info: RBM3D/Induction/QtNonzeroBoot.lean:1257:0: 'RBM.Gauss.Sizes.STXiRound'' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM3D/Induction/QtNonzeroBoot.lean:1258:0: 'RBM.Ind.stBoot_rounds' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM3D/Induction/QtNonzeroBoot.lean:1259:0: 'RBM.Ind.stXiBoot'_of_round' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM3D/Induction/QtNonzeroBoot.lean:1260:0: 'RBM.Ind.stXiBootR_of_round' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM3D/Induction/QtNonzeroBoot.lean:1261:0: 'RBM.Ind.stXiRoundNZ_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM3D/Induction/QtNonzeroBoot.lean:1262:0: 'RBM.Ind.stOeqQtNZ'_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM3D/Induction/QtNonzeroBoot.lean:1263:0: 'RBM.Ind.QtNonzeroBootInst.inst_OeqQtNZ'' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM3D/Induction/QtNonzeroBoot.lean:1264:0: 'RBM.Ind.QtNonzeroBootInst.inst_RoundNZ' depends on axioms: [propext, Classical.choice, Quot.sound]
Build completed successfully (3890 jobs).
exit=0
$ grep -E "^(error|warning): RBM3D/Induction/QtNonzeroBoot" build.log | wc -l   ->  0
$ grep -nE "sorry|admit|native_decide|^axiom|[^_]axiom |maxHeartbeats|open private|_private" QtNonzeroBoot.lean  ->  (no output)
```
Name clash: `git grep` on `main` for a declaration of each new public name / `QtNonzeroBootInst`: 0 for all 7.

## 6. Paper deltas (Lean vs `3_5_Loop_Hierarchy.tex`)
| difference | coverage |
|---|---|
| "solving which yields (am;asoi222)" (`3_5:1929-1930`) made a finite deterministic bootstrap (crude `N^{2n+1}`, contraction `B_u^{1/6} ≤ N^{-c}`, `c = min(2𝔡𝔠,ε/2)/12`, `⌈C₀/c⌉+1` rounds); new round pin `STXiRound'` with self-term at the endpoint `B_u` (paper: `B_{t,0}`, `sup_u`) | `T2304a` (report (d)) |
| lower terms of `(eq:expandQAempty)`, `k_α = 1` included, from the hypotheses; no `(eq:kalpha1)`, no `(am;asoiuw_smalleta)` at `k_α` (`3_5:1925`) | `T2304b` |
| `STbootRHS 1` (`n' = 1..n-1`) vs the paper's display `max_{n'=2}^{n-1}` (`3_5:1928`); first summand at `B_s` (R2*) | merged pin `STXiBoot'` (D563 R2*, §80); `lo = 1` noted in `T2304b` |
| uniform `Prec` over pairs instead of the paper's fixed-u + `N^{-C}`-net (`3_5:1931`) | DECISIONS §7 (existing pin shape) |

## Verdicts
| target | verdict |
|---|---|
| 1 `STXiRound'` (pin) | PASS |
| 2 `stBoot_rounds` | PASS |
| 4 `stXiBoot'_of_round`, `stXiBootR_of_round` | PASS |
| 5 `stXiRoundNZ_holds` | PASS |
| 6 `stOeqQtNZ'_holds` | PASS |
| registry (`Test/Axioms.lean`) | PASS (−`STOeqQtNZ'` +`STXiRound'`, two comments; found 152 not larger) |

Observations (no effect on statement, instance, build, axioms or delta coverage):
- O1: (a)'s crude-start row cites `η⁻¹ ≤ N` (log10 N ≥ 19.03); the code uses `η⁻¹ ≤ μN`; disclosed in (a′).
- O2: report says "144 owed" from the audit tool line; a raw grep of `owedProps` gives 143 on both `main` and the
  branch — different counting, net change 0 either way.
- O3: full `lake build RBM3D` in this worktree (no root import of the new module) passed, 4111 jobs; merge build is the hub's.

**Overall: PASS** — no dispatcher sign-off needed.
