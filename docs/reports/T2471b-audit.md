Auditor model: claude-opus-5-5
# T2471b audit, round 1: P1b-2 of T2471 (targets 4-7; `RBM3D/BA/GridRepTailBA.lean`), Mon Oct 12 22:11:58 UTC 2026
Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2471b-audit1`, detached at `t/T2471b` = `817c5c2f`; `main` = `a931034a`.
Scratch: scratchpad `T2471b/` (`AuditT2471b.lean` = `import RBM3D.BA.GridRepTailBA` + `T2471-check.lean:154-160, 165-206` verbatim + the examples below).

**Verdict: PASS** (targets 4, 5, 6 (a), 6 (b), 7). No dispatcher sign-off needed.

## 1. Build and axioms
```
$ date -u; lake build RBM3D.BA.GridRepTailBA            (Mon Oct 12 22:10:28 UTC 2026)
exit=0   Build completed successfully (4054 jobs).   lines containing "error": 0
warnings in RBM3D/BA/GridRepTailBA.lean: 7, all "This line exceeds the 100 character limit" at l.19, 20, 23, 24, 25, 27, 31 (module docstring)
$ time lake env lean RBM3D/BA/GridRepTailBA.lean        (forced re-elaboration, 22:10:40 UTC)
12.73s user 2.60s system 126% cpu 12.099 total   exit=0   lines containing "error": 0
$ lake env lean AuditT2471b.lean                        (22:11:02 UTC)   exit=0; only unused-variable warnings at l.31-32 (the check's own defs)
'RBM.BA.baGridWTail2_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.gridRepTailGen_hyp_BA' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.gridRepTailGen_ker_BA' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.gridRepTailGen_inc_BA' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.gridRepTailGen_window_BA' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baStep2_STgAg_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baStep2_STgDriftg_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baStep2_STEEMg_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baStep2_filt_withLam' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baGridRepNAt2_of_bridge' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baGridRepNAt2_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.GridRepTailBAInst.inst_baGridWTail2' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.GridRepTailBAInst.inst_baGridRepNAt2' depends on axioms: [propext, Classical.choice, Quot.sound]
$ grep -nE "sorry|admit|native_decide|^axiom|^\s*axiom " RBM3D/BA/GridRepTailBA.lean | wc -l       0
```

## 2. Statements against the pins (compiled in `AuditT2471b.lean`, pins copied verbatim from the check)
```
example : ∀ d : ℕ, T2471_GridRepN2 d := baGridRepNAt2_holds                                   -- 6 (b), ticket acceptance line
example : ∀ d : ℕ, T2471_Bridge d → T2471_GridRepN2 d := baGridRepNAt2_of_bridge              -- 6 (a)
example : ∀ d : ℕ, T2471_WTail2 d BAFlow (fun sz z => baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) BAflowT0 :=
  baGridWTail2_holds                                                                           -- 4
example : ∀ d : ℕ, T2471_WTail2 d BAFlow (…) BAflowT0 ↔ STGridWTail2gL d BAFlow (…) BAflowT0 := fun _ => Iff.rfl
example : ∀ d : ℕ, T2471_Bridge d ↔ BAGridBridge d := fun _ => Iff.rfl                       -- T2460's merged name
example : <check l.237-239 shape> := baStep2_STgAg_eq                                          -- 5 (a)
example : <check l.241-243 shape> := baStep2_STgDriftg_eq                                      -- 5 (b)
example : <check l.245-247 shape> := baStep2_STEEMg_eq                                         -- 5 (c)
example : ∀ {d : ℕ} (sz : Sizes d) (j : ℕ), filt (sz.withLam 0) j = filt sz j := baStep2_filt_withLam
example : ∀ d : ℕ, GridRepTailGen_Hyp d BAFlow (…) BAflowT0 := gridRepTailGen_hyp_BA        -- 4, class discharge
example : T2471_GridRepN2 3 := baGridRepNAt2_holds 3                                           -- consumer shape (U5d, T2459_P1)
exit=0
```
(The `<…>` lines are the check's `example : Prop` bodies copied as the expected type; `(…)` abbreviates the carrier
`fun sz z => baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)` written out in full in the scratch file.)

Per target:
- **4** `baGridWTail2_holds (d : ℕ)`: no premise; type = `T2471_WTail2` at the BA carrier, every `d` (pin compiles by
  term). `gridRepTailGen_hyp_BA (d : ℕ)`: no premise. Fine parameter order (κ ε 𝔡, 𝔠, sz, z, flow, s t, D before `∃ CK`,
  `K`, `ε'`, `∀ᶠ n`) is the pin's own.
- **5** three identities for all `sz lam0 E s t K n σ a k ω` (no premise), `filt` is `rfl` (l.1067).
- **6 (a)** sole premise is the inline body of `T2471_Bridge` (exact type, `Iff.rfl` with T2460's `BAGridBridge`).
  Route per UN-C5 (CONTROL H256 (3)), checked in source:
  ```
  l.1081  def GridRepTailBA_Mart i k ω := ∑ j ∈ Finset.range k, martIncNg (baStep2Mat sz lam0 E) s t K n j i.1 ω i.2
  l.1085  def GridRepTailBA_Rem  i k ω := STgANg … k ω - STgANg … 0 ω - (gridStep : ℂ) * ∑ STgDriftNg … - GridRepTailBA_Mart …
  l.1186  clause 1: Eventually.of_forall … by unfold GridRepTailBA_Rem; ring        (every n, a.e. trivially)
  l.1162  obtain ⟨C₀, hC₀, hRem⟩ := baTwistGridRem_holds d     clause 2 via gridRepTailBA_rem_eq (H1, H2, (5a), (5b))
  l.1196  clause 3 via gridRepTailBA_mart_eq, H3′, baTwistGridTail_holds at ε'/2, gridRepTailBA_shift_ineq (N^{ε'/2} ≥ 2)
  l.1170  CK := max CKr (max CKt CKw)        clause 4: hw K hK0 hKw (= baGridWTail2_holds)
  ```
- **6 (b)** `baGridRepNAt2_holds (d : ℕ) := baGridRepNAt2_of_bridge d (baGridBridge_holds d)`; T2460 merged (`ad52b370`,
  `BA/GridMartBA.lean:538` on main), so 6 (b) is in scope (dispatcher answer (2)). Type = TN-C2 pin verbatim.
- **7** see §4.

## 3. Hidden hypotheses, vacuity, cycles
- Targets 4, 6 (b), `gridRepTailGen_hyp_BA`, target 5: no premise beyond the data binders. 6 (a): one premise, discharged
  by the merged `baGridBridge_holds` (6 (b), and the instances).
- New `Prop` defs `GridRepTailBA_F1/F2` (l.959, 964) are premises of private-stem helpers only, concluded at BA by
  `gridRepTailBA_F1_ba`, `gridRepTailBA_F2_ba` (l.1040, 1045); no target carries them. No structure/class is defined.
- The classes `GridRepTailGen_Ker/Window/Inc/Hyp` (P1b-1, merged) are concluded at BA here with no premise left open at the
  flow level (`gridRepTailGen_hyp_BA`); conclusion is non-vacuous since `BAFlow sz0 (1/2) (1/10) (1/6) (1/10) zSeq`
  holds (merged `flow_sz0`) and the instances apply it.
- Dependencies: imports `Chain.GridRepTailGen2`, `BA.{GridMartBA, TwistKer, TwistGridWTail, TwistGridWTail2, TwistGridTail2,
  TwistGridRem2, GreenSchur, EMn2BA}`, all on `main`; `open private` reaches merged privates only (none deleted). No importer
  of the new module (`grep -rln GridRepTailBA RBM3D RBM3D.lean` → the file itself only). No cycle.
- External hypotheses: none.

## 4. Compiled nonempty instances (same file, `namespace RBM.BA.GridRepTailBAInst`, `d = 3`)
Data: `sz0` (merged admissible sizes, `L_n = 4(n+1)`), `zSeq`, `flow_sz0`, `sI ≡ 1/10 < tI ≡ 1/2 ≤ BAflowT0` (`half_lt_t0`),
`κ = 1/2, ε = 1/10, 𝔡 = 1/10, 𝔠 = 1/6`, `D = 1`, `ε' = 1/10`, `K_n = ⌈N_n^{CK}⌉₊ + 1` (≠ 0, `N^{CK} ≤ K_n` for all `n`).
```
l.1305 theorem inst_baGridWTail2 : ∃ CK, 0 ≤ CK ∧ ∃ K, (∀ n, K n ≠ 0) ∧ (∀ᶠ n, N^CK ≤ K n) ∧ (∀ᶠ n, ∀ i, CmI.Pp {…} ≤ ofReal (N^(-1)))
         := baGridWTail2_holds 3 (1/2) (1/10) (1/10) … (1/6) sz0 zSeq flow_sz0 sI tI hsI hstI htI 1 one_pos; then K applied
l.1346 theorem inst_baGridRepNAt2 : ∃ C₀ … ∃ Mart Rem, clause1 ∧ clause2 ∧ clause3 ∧ clause4   := from baGridRepNAt2_holds 3, same data
l.1385 example : ∃ C₀, 0 ≤ C₀ ∧ STGridRepNAtgL 3 2 C₀ BAFlow (…) BAflowT0 := baGridRepNAt2_of_bridge 3 (baGridBridge_holds 3)
l.1390 example : … := baGridRepNAt2_holds 3
l.1283/1287/1292/1300  Ker (∀ n), Window (∀ n), Inc (∀ K n), Hyp at d = 3
l.1328/1332/1337/1342  target 5 at n = 0, σ = ![false, true], a ≡ 0, k = 2, K ≡ 4, u = 1/4; filt at sz0
```
Every deterministic hypothesis is discharged at concrete data (no open premise; the bridge is the merged theorem).
Nondegenerate: `L_n ≥ 4`, `N_0 = 2097152` (prove report; `sz0` merged), `0 < s < t < 1`, `K_n ≥ 1`, labels over
`Fin 2 → Zd 3 (sz0.L n)` nonempty. No `N = 0`, empty index, collapsed window or `False` premise; the witness `K_n` is the
pin's own minimal grid, not an astronomically large choice made to trivialise a bound.

## 5. Diff, frozen files, greps
```
$ git diff --name-only main...t/T2471b
RBM3D/BA/GridRepTailBA.lean
RBM3D/Probe/T2471Pins.lean
$ git diff --stat main...t/T2471b -- RBM3D/Path RBM3D/Induction 'RBM3D/BA/Twist*' RBM3D/BA/Step2BA.lean RBM3D/BA/GridMartBA.lean RBM3D/Chain RBM3D/Test RBM3D.lean | wc -l
       0
$ wc -l RBM3D/BA/GridRepTailBA.lean        1396     (< 1,800 reserve rule, < 2,000 stop line; GridRepTailBA2 not created)
$ grep T2474 public names (loopFamNg|ZfamNg|ZvecNg|YvecNg|stoppedEdgeNg|SubGaussFormNg|SubGaussStopNg|stepErrNg|GridDriftNg|gridDriftNg|hermTestFunLoopNOf|QVPropagatedNg|StepDecompGen_|HierDriftGen_) | wc -l    0
$ grep -c STGridRepNgL (TN-C4)  0 ;  grep -cE 'Ring\.inverse|Matrix\.of|cycProd|Ugen' (U-C4)  0 ;  grep -cE '\|E\||zt E|etaT|mSigma|STflowE|lemT|STFlow' (X1-C1)  0 ;  grep -c 'sz\.lam' (UBA-C1)  0
$ git grep -nE "GridRepTailBA|gridRepTailBA_|gridRepTailGen_(ker|inc|hyp|window)_BA|baGridWTail2_holds|baGridRepNAt2_(holds|of_bridge)|baStep2_(STgAg_eq|STgDriftg_eq|STEEMg_eq|filt_withLam)" main -- RBM3D RBM3D.lean | wc -l
       0
```
Both files are sole writable files of T2471 (`RBM3D/Probe/T2471Pins.lean` is "1a only, never merged"); `RBM3D.lean` not
touched (import line is the hub's at merge). No frozen signature or merged file changed.

## 6. Paper deltas
- Target 4 (clause 4 at BA, `Z` proxy with the cut-count factor 2): `docs/paper-deltas.md:819` D202 (same type; accepted
  for the generic class at P1b-1's audit).
- Target 6 (BA grid pin from the twisted pin plus identities, not from `lem:DIfREP`): D690 (`docs/paper-deltas.md:1654`).
  H3′ (`‖twEEk‖ ≤ 2‖STEEMg‖`, `ε' → ε'/2`) is T2460's statement, proposed as `T2460a` (`docs/reports/T2460-prove.md:186`);
  this ticket only consumes it in the pinned hypothesis.
- UN-C5 (`Rem` = residual at every `n`) changes no statement (an internal witness choice of `∃ Mart Rem`).
- Target 5 identities are exact equalities (no delta). Coverage complete.

## 7. Observations (no effect on statement, instance, build, axioms or delta coverage)
- O1. Hub merge: bring in only `RBM3D/BA/GridRepTailBA.lean` and add `import RBM3D.BA.GridRepTailBA` after the last
  `import` line of `RBM3D.lean`; `RBM3D/Probe/T2471Pins.lean` (stacked from `t/T2471`) must not be merged.
- O2. Instance helpers `sI`, `tI`, `hsI`, `hstI`, `htI`, `hN1I`, `hεnI`, `CmI` are public but live in the stem namespace
  `RBM.BA.GridRepTailBAInst` (no clash on `main`); acceptable under rule (E) by full name.
- O3. 7 long-line lint warnings in the module docstring (l.19-31), as in `BA/TwistGridWTail2.lean`.
- O4. The ticket's 3 (c) band re-derivation belongs to P1b-1 (dropped by dispatcher answer (5)); not re-checked here.
