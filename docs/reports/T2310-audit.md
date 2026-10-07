Auditor model: claude-opus-5-5

# T2310 audit (round 1) — S3-18b1 `QEndB1`, target `stOeqQtRoundPT'_holds`

Written Wed Oct  7 10:15:57 UTC 2026 (`date -u`). Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2310-audit1`,
detached at `t/T2310` = `a6e597e`; `main` = `dab3fad`.

**Verdict: PASS** (one target, `stOeqQtRoundPT'_holds : ∀ d, STOeqQtRoundPT' d`; pins `STXiRoundPT'`, `STOeqQtRoundPT'`).

## 1. Statement against the pin (script diff against `docs/tickets/checks/T2310-check.lean`)
```
$ ex(){ awk -v n="$2" '$0 ~ "^def "n" " {p=1} p&&/^$/{exit} p{print}' "$1"; }
$ for n in STXiRoundPT' STOeqQtRoundPT'; do ex QEndB1.lean $n > f; ex T2310-check.lean $n > c; diff c f; done
STXiRoundPT': file       13 check       13 lines; diff:
(identical)
STOeqQtRoundPT': file        2 check        2 lines; diff:
(identical)
$ grep -n "^theorem stOeqQtRoundPT'_holds" RBM3D/Induction/QEndB1.lean
1187:theorem stOeqQtRoundPT'_holds : ∀ d : ℕ, STOeqQtRoundPT' d := by
```
Check file + `import RBM3D.Induction.QEndB1` + identity examples (`<scratch>/T2310/aud_check.lean`):
```
example : @RBM.Gauss.Sizes.T2310Check.STXiRoundPT' = @RBM.Gauss.Sizes.STXiRoundPT' := rfl
example : @RBM.Gauss.Sizes.T2310Check.STOeqQtRoundPT' = @RBM.Gauss.Sizes.STOeqQtRoundPT' := rfl
example : RBM.Gauss.Sizes.T2310Check.stOeqQtRoundPT'_holds_pin := RBM.Ind.stOeqQtRoundPT'_holds
$ lake env lean aud_check.lean ; exit 0   (no error lines)
```
Mathematics (paper `3_5:1362-1378` `(am;asoi222)`, proof `3_5:1676-1714`), read from the signatures:
- `STOeqQtRoundPT' d = STIngR d STCaseI STXiRoundPT'` (`Step34Pins.lean:445`): setting of `lem:main_ind`, regime
  case (i) `λ²/L² ≤ 1-t` (`Step34Pins.lean:237`), `0 ≤ s < t ≤ lemT z`, `STKbound`, `STKward`, `STLK s`,
  `STConStInd 𝔠d`, `STStep2Concl` — the same ingredient shape as the merged `STOeqQt` (`Step34Pins.lean:458`).
- `STXiRoundPT'` = merged `STXiRound'` (`QtNonzeroBoot.lean:92`) with exactly two changes: `2 ≤ n_ ↦ 3 ≤ n_`
  and conclusion `Prec ↦ PrecPT` (per-time: union over the pair `(v,u)` outside `P`, `StochDomAt.lean:105`).
  Both are the dispatcher's pin (DECISIONS §120). Quantifier order `n_ p` fixed before `XL XLK`, then `∀ τ D, ∀ᶠ n`
  inside `PrecPT`: fixed parameters before `∀ᶠ`, as the paper.
- Hypotheses `Ξ̂^𝓛_m ≺ XL m` (`STlenL n_ p m`: `m ≤ n_+1 ∨ m = 2n_-1 ∨ m = 4p`) and `Ξ̂^{𝓛-𝒦}_m ≺ XLK m`
  (`m ≤ n_`, current length included) are the controls the paper's RHS uses; conclusion
  `B_u^{1/6}·XLK n_ + STbootRHS 1 … B_s n_ p` is `(eq:alternatecase1)` + `(eq:alternatecase2)` with constants.
- Non-triviality check: `STbootRHS 1` (`Step34Pins.lean:402`) contains `XLK m` only for `m ≤ n_-1` and
  `XLK (n_+2-m)` with `m ≥ (n_+1)/2+1`, i.e. index `< n_`; the only `XLK n_` term carries `B_u^{1/6}` (small),
  so the conclusion does not follow from the `m = n_` hypothesis by `Prec → PrecPT`.
Verdict on statement: matches the pin exactly; differences from the paper are listed in §5.

## 2. Hidden hypotheses, vacuity, cycles
- Pins are `def … : Prop`, no structure fields. Public declarations of the file (script):
```
84:def STXiRoundPT' (E s t : ℕ → ℝ) : Prop :=
101:def STOeqQtRoundPT' (d : ℕ) : Prop :=
1187:theorem stOeqQtRoundPT'_holds : ∀ d : ℕ, STOeqQtRoundPT' d := by
1251:theorem inst_OeqQtRoundPT' :          (namespace RBM.Ind.QEndB1Inst)
private decls: 36   (all prefixed altQFlow_; grep of private decls without the prefix: empty)
```
- The proof (`QEndB1.lean:1187-1236`) obtains the constants of the merged theorems `gridGoodN_holds`,
  `nqLinGood_holds`, `stOeqNQPT''_holds`, sets `𝔠d = min(𝔠G,𝔠L,𝔠N,1/(2d))`, and uses `stDecayLoopU_of_step2`,
  `altGridEndQN`, `altYGridN`, `startLevelQN` — all merged theorems on `main`, no hypothesis forwarded:
```
'RBM.Ind.stOeqNQPT''_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.gridGoodN_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.nqLinGood_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Ind.altGridEndQN' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Ind.startLevelQN' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.stDecayLoopU_of_step2' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Ind.altYGridN' depends on axioms: [propext, Classical.choice, Quot.sound]
```
- No cycle: `QEndB1` is a new leaf module (`git diff --name-only main...t/T2310` = this file only; nothing on
  `main` imports it). No new external hypothesis: `STConStInd`, `STStep2Concl`, `STLK s` are `STIngR`'s existing
  premises (same as merged `STOeqQt`/`STOeqNQ`).

## 3. Compiled nonempty instance (`QEndB1.lean:1243-1316`, namespace `QEndB1Inst`)
- `inst_OeqQtRoundPT' : InstIngConcl STXiRoundPT' sz0 z0 sInst tInst 1` := `inst_ing … (stOeqQtRoundPT'_holds 3)
  sz0 z0 flow_z0 sInst tInst sz0_hs0 sz0_hst sz0_ht sz0_caseI sz0_con 1 one_pos` — discharges `3 ≤ d`, the flow
  (`κ=ε=𝔡=1/10`, `𝔠=1/6`), `0 = s < t = 1/16 ≤ lemT z`, `STCaseI`, `STConStInd` (every `𝔠d`), `Cd = 1 > 0`.
  Data: `d = 3`, `L = 4(n+1)`, `W = (2(n+1))^5`, `λ = (2(n+1))^{-6}`, `sInst ≡ 0`, `tInst ≡ 1/16` (`Defs.lean:439-440`).
- Two examples apply the conclusion at `(n_,p) = (3,1)` and `(4,2)`, `XL ≡ XLK ≡ 1` (`1 ≤ XL` by `le_rfl`), with
  `STKbound`/`STKward` discharged by `stKbound_of_flow`/`stKward_of_flow`. Left as hypotheses: `STLK s`,
  `STStep2Concl` (other gates' pins) and the pin's stochastic antecedents `Ξ̂ ≺ 1` — no deterministic hypothesis left.
- Index set nonempty and non-collapsed: `example (n) : ∃ q : STPair sInst tInst n, q.1.1 < q.1.2` (pair `(0,1/16)`).
- No `N = 0`, empty index, collapsed window, `False` premise or huge witness. All compile (build below).

## 4. Build, axioms, hygiene, diff scope
```
$ lake build RBM3D.Induction.QEndB1   (audit worktree; QEndB1.olean absent from the copied cache, built fresh)
ℹ [3870/3870] Built RBM3D.Induction.QEndB1 (15s)
info: RBM3D/Induction/QEndB1.lean:1323:0: 'RBM.Gauss.Sizes.STXiRoundPT'' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM3D/Induction/QEndB1.lean:1324:0: 'RBM.Gauss.Sizes.STOeqQtRoundPT'' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM3D/Induction/QEndB1.lean:1325:0: 'RBM.Ind.stOeqQtRoundPT'_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM3D/Induction/QEndB1.lean:1326:0: 'RBM.Ind.QEndB1Inst.inst_OeqQtRoundPT'' depends on axioms: [propext, Classical.choice, Quot.sound]
Build completed successfully (3870 jobs).
exit 0
$ grep "warning" build.log | grep -c QEndB1 ; grep -ci "declaration uses 'sorry'" build.log
0
0
$ grep -nE "sorry|admit|native_decide|^axiom|^\s*axiom |maxHeartbeats|implemented_by|unsafe" QEndB1.lean | wc -l
0
$ git diff --name-only main...t/T2310 ; git diff main...t/T2310 -- RBM3D.lean | wc -l
RBM3D/Induction/QEndB1.lean
0
$ name clash (grep -rnF <name> RBM3D RBM3D.lean | grep -v QEndB1.lean | wc -l)
STXiRoundPT' 0 ; STOeqQtRoundPT' 0 ; stOeqQtRoundPT'_holds 0 ; QEndB1Inst 0
```
Only the sole writable file is touched; no frozen signature changed (no existing file in the diff).

## 5. Paper deltas (Lean vs `3_5:1362-1378`, `3_5:1676-1714`)
| Difference | Coverage |
|---|---|
| per-time `PrecPT` over pairs `(v,u)` instead of `sup_{v∈[s,u]}` inside `≺` | `T2310a` (report (d)); DECISIONS §120/§122 |
| controls `XL, XLK` constant in `v` (paper: `sup_v` of `v`-dependent parameters); `B_v^{1/6} ≤ B_u^{1/6}` | `T2310a`; cf. `T2041a` (`Step34Pins` docstring) |
| `3 ≤ n_` (paper `n ≥ 2`) | `T2310a`; open item (1) of the report |
| martingale term at `B_{s,0}` instead of `B_{u,0}` (weaker) | existing D563 (R2*, §80) |
| non-alternating signs via `stOeqNQPT''_holds` on `[s,uu]` + union over `(σ,a)` | `T2310c` (proof route) |
| initial-loop split `ν = N^{e/8}`, `τ_N = e/2`; collapsed pairs by `STLK s`; factor 2 absorbed | `T2310b`, `T2310d`, `T2310e` (proof route) |
Every statement difference is proposed or already recorded.

## 6. Observations (no effect on statement, instance, build, axioms or delta coverage)
- O1: `n_ = 2` is outside this pin by design (DECISIONS §120 row 2: `altGridEndQN` needs `m = n_-2 ≥ 1`); the
  merged `STXiRound'`/`STXiBoot'` have `2 ≤ n_`, so S3-18b2 needs a separate `n_ = 2` source (report Open (1)).
  Recorded for the dispatcher's S3-18b2 design; not a defect of T2310.
- O2: ticket §2d/§4 still name `stOeqQtPT'_holds`; §1, the check file and the file use `stOeqQtRoundPT'_holds`.
- O3: ticket §2 omitted the non-alternating half and §2a's original `τ_N = ε₁/8` (corrected in §122); the prover
  documented both in (a′); the proof is complete regardless.
- O4: file is 1326 lines (ticket hi 1250, stop rule 1400 not reached).

## Verdict
`stOeqQtRoundPT'_holds` (with pins `STXiRoundPT'`, `STOeqQtRoundPT'`): **PASS**. No dispatcher sign-off required.
