Auditor model: claude-opus-5-5

# T2496 audit, round 1 (row U4s3a: targets 1-5; Amend 1 A6-A9 binding) — Tue Oct 13 11:06:31 UTC 2026
Branch `t/T2496` at e96c59dd; audit worktree `RBM3D-wt/T2496-audit1` (detached, cache cloned). U4s3b (targets 6-10) is a later stacked row, not audited here. Scratch: scratchpad `T2496/audit/` (`$S`).

## 1. Build, axioms, diff, hygiene
```
$ lake build            # full library (in-place ticket, H279 (3)); started Tue Oct 13 10:56:26 UTC 2026
info: RBM3D.lean:597:0: axiom audit: 14871 theorems, 4601 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
Build completed successfully (4366 jobs).      [0 error lines; 6:49 wall]
$ lake build RBM3D.Induction.LemDecCalELip RBM3D.Induction.EtermsMid2 RBM3D.Induction.EtermsMid
Build completed successfully (3910 jobs).
$ lake env lean $S/ax.lean      # #print axioms
stEtermsMidgL_of, etermsMid_band_gL, stEtermsMid_of_LWT, STLemDecCalE_iff_gL, etermsMid_newKLKL_band, lemDecCalELipG_flowMod_band,
lemDecCalELipG_flowMod_base, lemDecCalELipG_Kn, LemDecCalELip_LK2gL, _ELKLKgL, _EGtgL, _eegL, _Lloop_subg, _ee_subg, _STKloop_two_lip,
_Lloop_sub, _ee_sub: [propext, Classical.choice, Quot.sound]   (each of the 17 lines identical)
$ git diff --numstat main...t/T2496
182 1441 RBM3D/Induction/EtermsMid.lean | 1587 0 RBM3D/Induction/EtermsMid2.lean | 643 230 RBM3D/Induction/LemDecCalELip.lean
375 0 RBM3D/Probe/T2496Pins.lean | 1 1 RBM3D/Test/Axioms.lean            (all sole writable files)
$ git diff --name-only main...t/T2496 -- RBM3D/Chain RBM3D/BA RBM3D/Path RBM3D/Induction/{LemDecCalEPrec,PfStep5,PfStep5Alg,PfStep5Grid,
    NQEndFlowLift,QtXiRoundLift,QtNonzeroFlowLift,ExpIntIQ,ExpWardI,MainIndHolds,MainIndOut,Step5Pins,DuhamelI,DuhamelII}.lean RBM3D.lean | wc -l
0
$ grep sorry|admit|native_decide|axiom (3 files): 0;  STGridRepNgL: 0;  X1-C4 regex: 0;  withLam|lam0|BAflowLam0: 0;  ^import RBM3D.BA: 0 0 0
$ grep "import RBM3D.Induction.EtermsMid2" -r RBM3D RBM3D.lean  ->  RBM3D/Induction/EtermsMid.lean:9 only
$ wc -l: LemDecCalELip 1778, EtermsMid 498, EtermsMid2 1587   (all < 1,800)
$ git diff main...t/T2496 -- RBM3D/Test/Axioms.lean: one owner-text line of `STEtermsMidgL` (+ "generic: `stEtermsMidgL_of` (T2496, in place, ...)"); no owedProps line added
```

## 2. G1: band names and types unchanged (frozen signatures)
Dump of every public constant of `LemDecCalELip`/`EtermsMid` (+`EtermsMid2` on the branch): `Expr` of the type and, for defs, of the value; main env (`main` oleans) vs branch env.
```
$ python3 cmp.py  main_dump.txt br_dump.txt
main public decls (LemDecCalELip+EtermsMid): 26 ; branch (+EtermsMid2): 56
identical type(+def value): 25 ; differing: [] ; missing: ['RBM.Gauss.Sizes.STEEk.eq_1']   # auto-generated equation lemma, not a declaration
new public: 31   (30 declarations + bandStep2Mat.eq_1)
$ lake env lean docs/tickets/checks/T2496-check.lean   (in the audit worktree, branch)  ->  check exit 0, 0 error lines
```
Part 3 names in untouched files (`LemDecCalEPrec`, `PfStep5*`, `Step5Pins`, ...) are compiled by the full build; `stEtermsMid_of_LWT : ∀ d, STLWT d → STEtermsMid d` re-checked by `example` (below).

## 3. Statements against the pins (auditor scratch `$S/auditcheck.lean` = the check file + the lines below; `lake env lean` exit 0, 0 errors)
```lean
example : @LemDecCalELipG_FlowMod = @T2496_FlowModA6 := rfl          -- A6: check D2 + `2 *` (A1) + clause `GMM` after `LM`, verbatim
example (h : LemDecCalELipG_FlowMod Cm μ c) : T2496_FlowModA1 Cm μ c := lemDecCalELipG_flowMod_base h   -- 1a-audit D2 text (A1)
example : @EtermsMid_NewKLKLAtN = @T2496_A9AtN := rfl                 -- A9 body = STNewKLKLAtgL' body at a carrier Cm
example : STNewKLKLAtgL' d κ 𝔡 Ck δ₀ mk ↔ ∀ sz n E, 0 < sz.lam n → sz.lam n ≤ 𝔡⁻¹ → κ ≤ ((mk sz (fun _ => E)).m n).im →
    EtermsMid_NewKLKLAtN (mk sz (fun _ => E)) n Ck δ₀ := ⟨…binder reorder…⟩
example : ∀ d, EtermsMid_NewKLKL d (… STFlow …) (fun sz z => bandStep2Mat sz (STflowE z)) := etermsMid_newKLKL_band
example : @STLemDecCalEConclgL = @T2496_LemDecCalEConclgL := rfl     -- target 2 (binding)
example : @STLemDecCalEgL = @T2496_LemDecCalEgL := rfl               -- target 2 (binding)
example : T2496_BandLemDecCalE := STLemDecCalE_iff_gL                  -- target 2 bridge (binding)
run_meta  -- forallTelescope of stEtermsMidgL_of, isDefEq of its conclusion with T2496_EtermsMidHead d law Flow mkM T0
```
```
target 5: conclusion ≡ T2496_EtermsMidHead d law Flow mkM T0 : true; binders 19
  d law Flow mkM T0 E Hf ζf | hF : Step5CasesGen_FlowFacts … | hLW : STLWTgL … | hEMe : emn2ExpFacts … | hHK : emn2ExpHK … | hBd : STBdatagL d Flow T0
  hK2 : Step2IterGen_K2 d Flow mkM | hNew : EtermsMid_NewKLKL d Flow mkM
  hFM : ∀ κ ε 𝔡, 0<κ → 0<ε → 0<𝔡 → ∃ c, 0 ≤ c ∧ ∀ sz 𝔠 z, Flow sz κ ε 𝔠 𝔡 z → LemDecCalELipG_FlowMod (mkM sz z) (law sz) c
  hmn : ∀ sz κ ε 𝔠 𝔡 z, 0 < κ → Flow sz κ ε 𝔠 𝔡 z → ∀ n, ‖(mkM sz z).m n‖ ≤ 1
  hSr : ∀ sz κ ε 𝔠 𝔡 z, 0 < κ → Flow sz κ ε 𝔠 𝔡 z → ∀ (n : ℕ) (a : Zd d (sz.L n)), ∑ b, ‖(mkM sz z).S n a b‖ ≤ 1
  hLF : ∀ sz κ ε 𝔠 𝔡 z, 0 < κ → Flow sz κ ε 𝔠 𝔡 z → StepDecompGen_LoopForm (mkM sz z) (E sz z)
```
D3 (check `:271-274`, verbatim as `T2496_D3`) is accepted unchanged as `hKs` of `LemDecCalELip_LK2gL` (`$S/d3.lean`, `example … (hD3 : T2496_D3 Cm.toFlowFM t) := LemDecCalELip_LK2gL … hD3`, exit 0).

Premise-by-premise against the ticket rows + Amend 1 (target 5):
| row | Lean | verdict |
|---|---|---|
| 1, 5, 6 | `hF`, `hLW`, `hEMe`/`hHK`/`hBd` | merged texts, as in the row |
| 7 (A9) | `hK2` = merged `Step2IterGen_K2`; `hNew` = new class; `STK2decaygL'`, `STNewKLKLgL'`, glue `mkM = mkE ∘ E` absent | as A9 |
| 8 (D2, A1, A6) | `hFM` = check family shape (`:264-267`) with `LemDecCalELipG_FlowMod` (= A6 text, rfl) | as A6 |
| 9 (A7) | `hmn` = check shape (`:277-279`); `hSr` = A7 text, guarded `0 < κ → Flow →` | as A7 |
| 10 | `hLF` guarded; `LCompat/KCompat`, D3 not read by target 5 (fewer premises) | OK |
| A8 | no inline `‖K‖ ≤ N` premise in target 5; (a) closes: `lemDecCalELipG_Kn` derives `∀ᶠ n, ∀ v ∈ [0,t n], ‖C.K n v σ a‖ ≤ N` from the decay (`Step2IterGen_K2` form, `D = 1`) + `STBdatagL` data via `ST_prof_le_Bctl` | (a) as A8 |

A9 class against 0349 U5S-C3 and its use: `3 ≤ d → ∀ κ 𝔡, 0<κ → 0<𝔡 → ∃ Ck δ₀, 0<Ck ∧ 0<δ₀ ∧ ∀ ε 𝔠 sz z, Flow sz κ ε 𝔠 𝔡 z → ∀ᶠ n, EtermsMid_NewKLKLAtN (mk sz z) n Ck δ₀`: family-uniform `∃` before the sizes, eventual `∀ᶠ n`, flow guard present. Sharp `ℓ = L` form with `J²·prof` and the `W^{-d} W^{-D}` floor (rfl against `STNewKLKLAtgL'`, the general-`ℓ` `Step2IterGen_NewKLK` is not used). The window data (`0 < lam ≤ 𝔡⁻¹`, `κ ≤ Im m`) move into `Flow`/`∀ᶠ n` (Iff above). Use: `hnew ε 𝔠 sz z hflow : ∀ᶠ n, EtermsMid_NewKLKLAtN (mkM sz z) n Ck δ₀` into `etermsMid_A_prec` (`EtermsMid2:671`), the `(S5WG+M000)` bound. Pinned `∃` of the conclusion (`𝔠d = min (1/100) (1/(30 Cd))`) is chosen before `𝔠 sz z` (`EtermsMid:376-378`).

Target 1 (carrier forms of `LemDecCalELip` §1-§4, under D2 core `LemDecCalELipG_Mod` + `hLM`, D3, `‖m‖ ≤ 1`, `hS`): `_Lloop_subg` `3k N^{2k+6} N^c √|Δu|` (band `c = 1` gives `N^{2k+7}`, the G1 type), `_LK2gL` `N^{11+c}`, `_ELKLKgL`/`_EGtgL` `N^{17+c}`, `_eegL` `N^{20+c}`; `hKn` of `_ELKLKgL` has the producer `lemDecCalELipG_Kn` (A8 (a)). C1 regex over the 28 generic statements: hits only in band-labelled declarations (`lemDecCalELipG_seqHflow_entry_sub`, `_mod_band`, `_flowMod_band`, `STLemDecCalE_iff_gL`, `etermsMid_band_gL`) and in the name `Lloop_subg`.
Target 3 (D4): `LemDecCalEPrec` untouched (diff 0); `LemDecCalELip` §5-§7 public types identical (section 2).

## 4. Hidden hypotheses, vacuity, cycles
- New Prop defs: `LemDecCalELipG_FlowMod`, `LemDecCalELipG_Mod`, `EtermsMid_NewKLKLAtN`, `EtermsMid_NewKLKL`, `STLemDecCalEConclgL`, `STLemDecCalEgL`; no `structure`/class field added, no `Step2Mat`/`FlowFM` field (Chain diff 0).
- Each new class is concluded by a public band discharge (`lemDecCalELipG_flowMod_band`, `lemDecCalELipG_mod_band`, `etermsMid_newKLKL_band`); `STLemDecCalEgL` is a hypothesis only in an `example` (no generic proof, D4); the full build's `#assert_rbm_axioms` passes with no new `owedProps` line.
- Non-vacuity: `etermsMid_band_gL` applies `stEtermsMidgL_of` at the band tuple with every premise but `hLW` discharged (`step5CasesGen_flowFacts_band`, `emn2Exp_bandFacts`, `emn2Exp2_bandHK`, `bandFM_STBdata`, `step2IterGen_K2_band`, `etermsMid_newKLKL_band`, `lemDecCalELipG_flowMod_band` at `c = 1`, `norm_mE`, `sum_norm_SB_row`, `stepDecompGen_loopForm_band`).
- Cycles: `EtermsMid2` imports `LemDecCalELip` and `Chain/*` only; `EtermsMid` imports `EtermsMid2`; no `BA/*`, no `NQEndFlowGen`; the full build is acyclic.
- BA side (not in this row): D2, A7, A8 (a) at BA are scratch readings of the prover (not re-run here); A9 BA = U4-BA at mixed coupling (R1 inside that discharge only, as A9 fixes); no BA premise of target 5 lacks a named source (prove report table (iii)+(vii)).

## 5. Compiled nonempty instances (all compile in the full build)
| target | instance | data | open hypotheses |
|---|---|---|---|
| 1 | `EtermsMid2.lean:1540, 1548, 1557, 1565` | `bandStep2Mat sz0 (fun _ => 1/2)`, `Hm = seqHflow`, `G = contGood`, `c = 1`, `s ≡ 0`, `t ≡ 1/16` (`N_0 = 2097152`) | none |
| 1 (A8 a) | `EtermsMid2.lean:1576` | `(sz0, z0)`, `κ = ε = 𝔡 = 1/10`, `𝔠 = 1/6`, `t ≡ 1/16` | none |
| 1 band corollaries | `LemDecCalELip.lean:1708-1764` (merged instances, unchanged statements) | `sz0`, `E ≡ 1/2`, `t ≡ 1/16` | none |
| 2 | `LemDecCalELip.lean:1702` | `(sz0, z0, 0, 1/16)`, every `Cd > 0` | the pin `STLemDecCalEgL 3` at the band (no generic proof, D4) |
| 5 | `EtermsMid.lean:493` (via `etermsMid_band_gL`, i.e. `stEtermsMidgL_of` applied) | `(szB, zB, 7/8, 15/16)`, `L = 4`, `W_n = n+4`, every `Cd > 0` | `STLWTgL 3` (L5's pin) and the Step 1-4 premises inside `InstIng5Concl` (other gates' pins) |
| 5 band | `EtermsMid.lean:463, 468` | as above, `Cd = 1, 100` | `STLWT 3` |
No `N = 0`, empty index, collapsed window or `False` premise.

## 6. Paper deltas
Lean/paper differences of this row and their coverage in prove report (d): D2 constant `2`, clause `GMM` (T2496a); carrier exponents `N^c` (T2496b); D3 at the band in Lipschitz form, A8 (a) route (T2496c); A9 window absorbed in `∀ᶠ n` (T2496d). Nothing in `docs/paper-deltas.md` yet (`grep -c T2496` = 0; the dispatcher appends). All differences covered.

## 7. Observations (no RETURN)
- O1. `RBM3D/Probe/T2496Pins.lean` no longer compiles on the branch (`lake env lean` exit 1, 3 errors: `'etermsMid_Bctl_window' not found …`, `Unknown identifier etermsMid_lam`; its `open private` names moved to `EtermsMid2`). It is never merged: at the merge the hub must bring in only `LemDecCalELip`, `EtermsMid`, `EtermsMid2`, `Test/Axioms`, and add `import RBM3D.Induction.EtermsMid2` to `RBM3D.lean`.
- O2. Layout: the four packaged target-1 forms (`LemDecCalELip_*gL`) sit in the reserve `EtermsMid2` (§8), not in `LemDecCalELip` (the prover's 1,800-rule move). It changes no statement; their consumers (targets 6-9, U4s3b) import `EtermsMid`. Readers outside the row read only band names kept in `LemDecCalELip`. Dispatcher may note it on the ROUTES line.
- O3. A7 (`hSr`) and `‖m‖ ≤ 1` are carrier premises with band/BA values `= 1`, `≤ 1`; not paper differences.
- O4. Calibration (UP-C2 (d)): numstat added 2,413 over the writable files (without the probe); the prover's moved-line count 1,002 was not re-run; landing 1,411 < 3,540 either way.

## Verdict
| target | verdict |
|---|---|
| 1 (`LemDecCalELip` §1-§4 over the carrier, D2/D3, A6-A8) | PASS |
| 2 (`STLemDecCalEConclgL`, `STLemDecCalEgL`, `STLemDecCalE_iff_gL`) | PASS |
| 3 (D4: unchanged) | PASS |
| 4 (`EtermsMid` §1-§8 over the carrier, A9) | PASS |
| 5 (`stEtermsMidgL_of`; band `stEtermsMid_of_LWT`) | PASS |
**Row U4s3a: PASS.** No dispatcher sign-off needed (O2 is informational).
