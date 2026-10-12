Auditor model: claude-opus-5-5

# T2455 audit, round 1 (stage 2): Mon Oct 12 16:48:41 UTC 2026
Inputs: ticket `docs/tickets/T2455.md`, check `docs/tickets/checks/T2455-check.lean`, `docs/reports/T2455-prove.md`, 1a-audit round 2 (`docs/reports/T2455-1a-audit.md` §9: pins fixed), CONTROL H250 (3) / DECISIONS §269 (2) (UBA-C1). Branch `t/T2455` at `8eb4ff2`, merge base `04118b1`; detached audit worktree `RBM3D-wt/T2455-audit1`. Scratch `<scratchpad>/T2455/audit1/`. `Probe/T2455Pins.lean`, `Probe/T2455Meas.lean` are never-merged 1a probes (no commit after `46fc313`), so they are not audited as deliverables.

## 1. Build, axioms, hygiene, diff
```
$ lake build RBM3D.Evolution.{CltSwap,CltResolvent,CltPath,FarEntry,CltGood,CltStep,ExpInv} RBM3D.Chain.CltGen \
    RBM3D.Evolution.{CltMoments1,CltMoments2,MeanFar,CltFar} RBM3D.Induction.IniTermI
Build completed successfully (3829 jobs).   exit=0   (errors 0; warnings: style only - longLine, `show`, flexible simp, one unused variable)
$ lake build RBM3D.Induction.MainIndHolds RBM3D.Induction.MainIndOut RBM3D.Main.BandTerminal RBM3D.Test.Axioms
Build completed successfully (4150 jobs).   exit=0
$ lake build            (whole library, branch state)
info: RBM3D.lean:514:0: axiom audit: 13321 theorems, 4208 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
premises found by scanning: 120 (borrowed 1, owed 55, structural 45, refuted 6, superseded 13).
Build completed successfully (4282 jobs).   exit=0
$ lake env lean axioms.lean     (#print axioms of the 70 new public names: 45 in the seven files + 25 in Chain/CltGen)
  70 depends on axioms: [propext, Classical.choice, Quot.sound]
$ grep -nE "\bsorry\b|\badmit\b|native_decide|^axiom " <7 files + Chain/CltGen>        grep exit=1 (no match)
$ grep -n "^import" <the 7 files + CltGen> | grep -c RBM3D.BA                            0
$ lake env lean T2455-check.lean   (ticket check, branch env)                            exit=0 errors=0
$ git diff --name-only main...t/T2455
RBM3D.lean  RBM3D/Chain/CltGen.lean  RBM3D/Evolution/{CltGood,CltPath,CltResolvent,CltStep,ExpInv,FarEntry}.lean
RBM3D/Probe/T2455Meas.lean  RBM3D/Probe/T2455Pins.lean  RBM3D/Test/Axioms.lean        (all sole writable files)
$ git diff --quiet main...t/T2455 -- <CltMoments1 CltMoments2 MeanFar CltFar RBM3D/Induction Chain/Carrier Chain/Step2Gen Chain/Step2Kern>   exit=0
$ wc -l   365 CltSwap  1285 CltResolvent  708 CltPath  1865 FarEntry  1080 CltGood  1823 CltStep  634 ExpInv  267 CltGen   (stop 2,000 / CltGen 300)
```
`RBM3D.lean` diff: one line `import RBM3D.Chain.CltGen` after the last import (before `#assert_rbm_axioms`). `Test/Axioms.lean`: +6 owedProps (`STLocalEntryUgL`, `STGdecayWgL`, `STGijDecgL`, `STKfargL`, `STMfarg`, `CltInvg`), +2 structuralProps (`CltRepg`, `HCltOf`).

## 2. Statements against the pins (script)
Check Parts 1-2 verbatim + the auditor's examples (`stmt.lean`, branch env): `lake env lean stmt.lean` exit=0, errors 0.
```
example : ∀ d L W : ℕ, RBM.Evol.CltEtaLowerOf d L W ↔ T2455_CltEtaLowerOf d L W := fun _ _ _ => Iff.rfl
example : @STfFarg = @T2455_STfFarg := rfl
example ... : STCltFarConclgL C μ s t ↔ T2455_STCltFarConclgL C μ s t := Iff.rfl
example : @STcltBg = @T2455_STcltBg := rfl
example : @STcltXg = @T2455_STcltXg := rfl
example ... : STCltIsoConclgL C μ s ↔ T2455_STCltIsoConclgL C μ s := Iff.rfl
example ... : STExpInvgL C μ ↔ T2455_STExpInvgL C μ := Iff.rfl
stCltIsogL_holds : ∀ (d : ℕ), STCltIsogL d
@stExpInvgL_of_rep : ... CltRepg C μ H₀ g' E → CltInvg H₀ → STExpInvgL C μ
Evol.cltEta_lowerOf : ∀ (d L W : ℕ), Evol.CltEtaLowerOf d L W
```
Pins fixed at the 1a-audit (`HCltOf`, `STCltIsogL`, `STCltFargL`, `STExpInvgL`, inputs; Pins:141-283 at `46fc313`):
```
$ diff <(git show 46fc313:RBM3D/Probe/T2455Pins.lean | sed -n 141,283p | grep -v '^\s*$') \
       <(git show t/T2455:RBM3D/Chain/CltGen.lean | sed -n 28,170p | grep -v '^\s*$')      diff exit=0
```
**G1** (the 100 Part-3 names): elaborated `type` (and `value` for defs) hashed by a meta command in the main env (seven files identical on `04118b1` and `main`) and in the branch env:
```
$ lake env lean g1dump_base.lean (main worktree) ; lake env lean g1dump_br.lean (audit worktree) ; diff g1_base.txt g1_branch.txt
diff exit=0      (100 names: 48 thm, 51 def, 1 structure `LocalForm`; none missing)
```
Tier 1, read against the ticket (manual, file lines): `CltEtaLowerOf` (= pin); `CltDerivEvalMultiOf`/`Of` = band M4 with `m : ℂ`, `ztOf m E u`, premise `(ztOf m E u).im ≠ 0`; `CltEvalDetLeMultiOf`/`Of` = band M5 with `κ ≤ m.im`, `κ ≤ 1`, base `2N³/κ` (T2455c); `CltPathBoundMultiOf`/`Of` = band P1 (script `diff` of the two defs: only `m`, `H₀`, `H₀.IsHermitian`, `cltGoodAtOf`, `cltEvalAtOf` differ). Group 2: `STFarEntryAtLoggL` = band `STFarEntryAtLog` on `C.G` (charge `+`, `PrecL μ`; T2455b); `CltGmax/FarEntry/GoodWhpOf` quantify over `HCltOf` with conclusions under `PF (g' n)` at `H₀ n + Hflow`, `C.m n`; `cltStepOf` = band `cltStep` conclusion with `cltStep_XoY (cltEvalAtOf …)`, `PF (g' n)`. Band `stCltIso_holds` is now proved from `stCltIsogL_holds` (CltStep:1565), so the generic pin implies the band pin.

## 3. Hidden hypotheses, vacuity, cycles, X1-C1, UBA-C1
- `FlowFM` (Chain/Carrier) has data fields only (`L K G M S eta m`); `HCltOf` is an explicit premise of `STCltIsogL`, `STCltFargL` and the `…WhpOf` pins. No Prop field anywhere.
- Imports: `CltGen` ← `Chain.Step2Gen`, `Induction.Step5Pins`; `ExpInv` ← `CltGen`; `bandFM_STExpInv` takes `STExpInv d` as a hypothesis (proved later in ExpInv), no cycle. Every input producer named for the band is merged (`gbEXPV3` GbEXP:806, `kellStarEv` KellStar:173, `bandFM_STStep2Concl`).
- Hypotheses kept in the instances: only `STLocalEntryUgL`, `STGdecayWgL` (Step 2 gate pins; registered owed).
- `STCltFargL` is a def (X1b proves it); no public theorem here takes it, `STThPropsg` or `STKpropsg` (`grep` outside CltGen/Probe: no hit).
- X1-C1 grep over the statements of the 70 new public declarations (pattern of the ticket, comments stripped):
```
Evolution/CltResolvent new public 14 statement hits 2   cltCk_facts:710-711 (band margin, |E| ≤ 2 - κ, mE)
Evolution/CltPath 7 / 0   Evolution/FarEntry 6 / 0   Evolution/CltGood 10 / 0   Evolution/CltStep 6 / 0   Evolution/ExpInv 2 / 0
Chain/CltGen new public 25 statement hits 1             bandFM_STThg:202 (bridge to merged Theta, mSigma)
```
  Both hits are band corollaries/bridges (allowed); no hit in a generic definition.
- UBA-C1 (§269 (2) (g)): `STThPropsg`/`STKpropsg` read `Bparam`, `ellT`, `STAI` at `sz.lam`; prove report (a⁗) gives the X1-C2 table with Θ-profile at `gK = g₀` through a profile hypothesis, size level at `sz.lam`, and the one comparison hypothesis `∀ n, gK n ≤ sz.lam n ∧ sz.lam n ^ 2 ≤ A * gK n ^ 2` (band `A = 1`, BA `A = (κ+1)/κ`, `TwistStep2_lam0_sq`); the conversion is U4-BA (a) by §269 (2) (g). `gK`, `A` occur in no pin. Compliant.

## 4. Compiled nonempty instances (read in the files; all compile in the builds of §1)
| endpoint | instance | data / discharged |
|---|---|---|
| `cltEta_lowerOf`, `cltDeriv_eval(Multi)_leOf`, `cltEval_det(Multi)_leOf` | CltResolvent:1144-1190 | `d = L = 3`, `W = 1` (N = 27), `m = 3/10 + 3/5 i` (‖m‖ ≠ 1), `κ = 1/2 ≤ Im m`, `u = 1/2`; all premises discharged |
| `cltCk_facts` | CltResolvent:1191 | `κ = 1`, `E = 0` |
| `cltPath(Multi)_boundOf` | CltPath:641, 663 | `szCL` n = 0, `m = 1/2 + i`, `H₀ = (1/3)·1`, `R = 10w`, step `W^{-1/2} > 0` (`cltpath_chk_nondeg`) |
| `stFarEntryAtLoggL`, `bandFM_STGijDecgL_of_three_le` (→ `bandFM_STGijDecgL` → `stGijDecgL_of_gex`), `bandFM_STKfargL`, `bandFM_STMfarg`, `bandFM_M_le`, `cltRepg_band` | FarEntry:1815 `example` | `bandFM szCL (STflowE zCL)`, `s = τ = sCL`, `t = tCL`, `δ = 1/10`; `hGij` via `gbEXPV3`, `hK` via `kellStarEv`; far set nonempty (`farEntry_szCL_far_nonempty`) |
| `cltGmax/cltFarEntry/cltGood_whpOf` | CltGood:1002 (`cltGood_hCltOf_szCL`), :1037, :1044, :1053 | `HCltOf` at band data, `κ = 1/2`, every non-Step-2 premise discharged |
| `stCltIsogL_holds`, `cltStepOf`, `cltStep_loopForm_evalOf`, `cltStep_pairForm_evalOf` | CltStep:1763-1810 | band data; labels `cltStep_szCL_witness n` (window > 0, isolated); `m = 1/2 + i` |
| `stExpInvgL_of_rep`, `stExpInvgL_band` | ExpInv:624, 628 | carrier `expInv_chkC szCL (1/3) (1/2 + i)`, law `seqP (szCL.withLam 0)`, `H₀ = (1/3)·1` (CltRepg by rfl, CltInvg proved) |
| CltGen bridges | CltGen:239-254 | `szCL`, `n = 0`; `bandFM_STExpInv` keeps `STExpInv 3` (proved in ExpInv, imports CltGen) |
No instance uses `N = 0`, an empty index set, a collapsed window or a `False` premise.

## 5. Paper deltas
Candidates in the prove report (d): **T2455a** (loop premise of `STGijDecgL` for both mixed charges; paper `7_8:1924` states `(−,+)`), **T2455b** (`STFarEntryAtLoggL` for charge `+` only; `−` by transpose in `cltFarEntry_whpOf`), **T2455c** (generic M5 premise `κ ≤ 1` in place of `cltCk κ ≤ 1`). The band statements are unchanged (G1), so no band paper statement moves. Coverage: complete for the statement differences found here.

## 6. Verdict per target
| target | verdict |
|---|---|
| 1 CltSwap (unchanged; `cltTransfer` applied at `sz.withLam g'`) | PASS |
| 2 CltResolvent (E4 = pin, M4, M5 generic; band corollaries) | PASS |
| 3 CltPath (P1 at `H₀ + Hflow`, `m`) | PASS |
| 4 FarEntry (`STFarEntryAtLoggL`, band implications (b), (c)) | PASS |
| 5 CltGood (`…WhpOf`, `cltGood_hCltOf_szCL`) | PASS |
| 6 CltStep (`cltStepOf`, `stCltIsogL_holds`; band `stCltIso_holds` corollary) | PASS |
| 7 ExpInv (`stExpInvgL_of_rep`, `stExpInvgL_band`) | PASS |
| 8 Chain/CltGen (pins = 1a-audit text; conclusions = `T2455_*`; bridges) | PASS |
| 9 G1 (100/100 unchanged) / 10 instances / 11 X1-C1 grep | PASS |
**Overall: PASS.** needs dispatcher sign-off: no.

## 7. Observations (no RETURN)
- Merge (hub, union files): `main` (T2454) already lists `` `RBM.BA.STGdecayWgL `` in `owedProps`; the branch adds it again. The check uses `List.contains`, so the build still passes; drop one line at the union. The probe files `RBM3D/Probe/T2455*.lean` are on the branch and are not part of the merge (ticket: never merged).
- The generic `CltGmaxWhpOf`/`CltFarEntryWhpOf`/`CltGoodWhpOf` are at `τ = s` (the band forms allow `s ≤ τ ≤ t`). The only consumer (`cltStep`, `cltStepOf`, CltStep:973/1020) uses `τ = s`. This is not a paper delta.
- The band theorems `stFarEntryAtLog`, `cltGmax_whp`, `cltFarEntry_whp`, `cltGood_whp`, `stExpInv_holds`, `cltStep` keep their own proofs and are not re-derived from the generic ones (prove report (d)). Their statements are unchanged (G1), so this changes no statement.
- Ticket name `stExpInvOf` is not introduced. Its content is in `stExpInvgL_of_rep` (ticket names are proposals).
- The prove report is 377 lines, over the CLAUDE.md §6 limit of 300 and the ticket's 200. It is a report defect only.
- The `STCltFargL` premises `STThPropsg`, `STKpropsg` (X1-C2) have no producer yet (X1b / U4-BA). There is no instance of the far pin here, as the ticket expects.
