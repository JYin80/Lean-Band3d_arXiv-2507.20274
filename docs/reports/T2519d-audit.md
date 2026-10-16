Auditor model: claude-opus-5-5
# T2519 row d audit (round 1): targets 13-17, `BA/GUELLBA`, `BA/GUEHyp`
Audit started Fri Oct 16 18:50:19 UTC 2026 (first `date -u`); report written Fri Oct 16 18:55:10 UTC 2026. Branch `t/T2519d` 6ae6bd6b, merge-base = `main` 662acb30. Detached audit worktree `RBM3D-wt/T2519d-audit1`. Scratch (uncommitted): `$S` = scratchpad `T2519d/`. Inputs: ticket T2519, Amends 1-5, prove report `T2519d-prove.md`.

## 1. Diff scope, build, axioms, hygiene
```
$ git diff --name-only main...t/T2519d
RBM3D.lean
RBM3D/BA/GUEHyp.lean
RBM3D/BA/GUELLBA.lean
RBM3D/Test/Axioms.lean
$ git diff main...t/T2519d | grep -E '^\+.*\b(sorry|admit|native_decide)\b|^\+\s*axiom ' | wc -l
       0
$ git show t/T2519d:RBM3D.lean | grep -n -E '^import|^#assert' | tail -4
664:import RBM3D.BA.GUETwistBA2
665:import RBM3D.BA.GUELLBA
666:import RBM3D.BA.GUEHyp
669:#assert_rbm_axioms
$ lake build RBM3D.BA.GUELLBA RBM3D.BA.GUEHyp > build.out 2>&1; echo "exit $?"; tail -1 build.out; grep -E '^(error|warning).*(GUELLBA|GUEHyp)' build.out | wc -l
exit 0
Build completed successfully (4140 jobs).
       0
$ lake build 2>&1 | grep -E '^error|axiom audit|premises found|Build completed'     # full library, audit worktree
info: RBM3D.lean:669:0: axiom audit: 15772 theorems, 4843 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
premises found by scanning: 124 (borrowed 1, owed 51, structural 52, refuted 6, superseded 14).
Build completed successfully (4439 jobs).
$ lake env lean $S/signed_audit.lean    # tail: #print axioms of the 13 public theorems
'RBM.BA.ba_prodG' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.ba_LLG' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.ba_QueG' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baEq729_Kdisc' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.oull_of_pathBoundsBA' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.gueGrid_eq729BA' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.Eq729B_perNBA' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.Eq729B_eq747_of_eq729BA' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.Eq729B_derivedBA' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.Eq729B_eq747_of_inputsBA' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.GUELLBA_EdReal' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.GUELLBA_flowEta' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.GUELLBA_flow_data' depends on axioms: [propext, Classical.choice, Quot.sound]
exit 0
```
Registry (`Test/Axioms.lean`): three comment lines changed, located by name, nothing added (word diff):
```
$ git diff main...t/T2519d -- RBM3D/Test/Axioms.lean | grep '^@@'; (changed words)
@@ -165,8 +165,8 @@ def owedProps   -> `UNOULLk`, `UNG1Rowk` owner comments: "BA-C5 (`RBG_Prod`, LL, `RBG_Que` at `UNKind.ba`)" => "C5 (`ba_prodG`, `ba_LLG`, `ba_QueG`, T2519, `BA/GUEHyp`)"
@@ -385,7 +385,7 @@ def structuralProps -> `UNOUQUEk` comment: "BA-C3, BA-C5)" => "C3 (T2515), C5 (T2519))"
```
Direct imports of `MainInd|TwistPins|Step6|TwistStep|TwistAvg` in the two files: 0 (grep). `GUEHyp2.lean`: not created. No merged file edited.

## 2. Statements against the signed texts (targets 15, 16; flow lemmas)
`$S/signed_audit.lean` = `docs/tickets/checks/T2519-pins.lean:9-131` with the two Amend 1 (a)/(b) edits signed by the 1a-audit, plus `example`s:
```
$ diff <(sed -n 9,131p docs/tickets/checks/T2519-pins.lean) <(sed -n 3,125p $S/signed_audit.lean)
45c45
<       1 ≤ I.length → I.length ≤ 4 * 3 →
>       1 ≤ I.length → I.length ≤ 4 * 4 →
119c119
<     (fun n => BAm d (sz.L n) (Real.sqrt (t0 n) * sz.lam n) (E' n : ℂ)) (gueGridK sz 3) 3 Kt
>     (fun n => BAm d (sz.L n) (Real.sqrt (t0 n) * sz.lam n) (E' n : ℂ)) (gueGridK sz 4) 4 Kt
$ grep -E '^example' $S/signed_audit.lean | tail -13    # the first 2 are the pins file's own `example : Prop`
example : T2519_ProdBA T2519_KFamBA T2519_PBBA := ba_prodG
example : T2519_LLBA T2519_PBBA := ba_LLG
example : T2519_QueBA T2519_KFamBA T2519_PBBA := ba_QueG
example : T2519_ProducersBA := ⟨ba_prodG, ba_LLG, ba_QueG⟩
example : T2519_KdiscBA := baEq729_Kdisc
example : T2519_EdRealBA := GUELLBA_EdReal
example : T2519_FlowEtaBA := GUELLBA_flowEta
example : @T2519_KFamBA = @BAKFam := rfl
example : @T2519_PBBA = @BAPB := rfl
example : @T2519_PathBoundsBA = @GUEPathBoundsBA := rfl
example : ∀ d : ℕ, 3 ≤ d → RBG_Prod (BAEd d) (BAfE d) (BAfT d) (BAMO d) (BAKFam d) (BAPB d) := ba_prodG
example : ∀ d : ℕ, 3 ≤ d → RandomLayerB_LL (UNKind.ba d) (BAfE d) (BAfT d) (BAPB d) := ba_LLG
example : ∀ d : ℕ, 3 ≤ d → RBG_Que (UNKind.ba d) (UNOUProfile.ba d) (BAEd d) (BAfE d) (BAfT d) (BAMO d) (BAKFam d) (BAPB d) := ba_QueG
$ lake env lean $S/signed_audit.lean; echo "exit $?"    -> only the 13 axiom lines above; exit 0
```
Target 16 concludes the merged `RBG_Prod` (`RandomLayerBG:70`), `RandomLayerB_LL` (`RandomLayerB:149`), `RBG_Que` (`RandomLayerBG:85`) at exact type (by elaboration, not `rfl` unfolding of the targets). Target 15 = `T2519_KdiscBA` exactly.

## 3. Targets 13, 14 against the band twins (ticket mathematics)
Signatures read: band `oull_of_pathBounds` (`LLTransfer`), `gueGrid_eq729` (`Eq729B:622`), BA `oull_of_pathBoundsBA` (`GUELLBA:236`), `gueGrid_eq729BA` (`GUEHyp:227`), `Eq729BA_Concl` (`GUEHyp:81`). Differences (each checked by reading both signatures):
| item | band | BA (row d) | covered by |
|---|---|---|---|
| energy | `|E n| ≤ 2 - κ` | `BAbulk` (13); `hr : ∀ n, BAReal …` (14) | T2519da, T2519db |
| window | `∀ᶠ n, 0 < lam ≤ Λ` | `hlam : ∀ᶠ n, 0 < g n ∧ g n ≤ Λ` (Amend 4 item 3) | T2519db |
| `n0` | 13: any `1 ≤ n0`; 14: `3 ≤ n0` | 13: `n0 = 4` fixed (= `BAPB`); 14: `4 ≤ n0` | T2519da, T2519db (Amend 1 (a)) |
| zero mode `hell` | `L^d(1-t1) ≤ lam²` | `L^d(1-t1) ≤ 2 g²` | T2519db, T2519dc |
| K-bound | `hKb : STKbound` | none (derived by `Hyp_Kt_detDomBA`) | T2519db |
| K clauses | `∀ n` | guarded `0 < g n →` (signed `BAKFam` form) | T2519db |
| conclusion | `Eq729B_Concl` (`N^δ((Nη)^{-3} + I₀)`) | `Eq729BA_Concl`, same loss form with `etaOf (m n) (t0 n)` | T2519db |
Quantifier order: fixed parameters before `∀ᶠ n` in every target; conclusions eventual. Amend 4 item 3: the only window-carrying public statement (`gueGrid_eq729BA`) takes it eventually; grep `∀ n, 0 < g n ∧` in both files: 0; the proof uses `gueGrid_expect_oneLoopBA'` (`GUEHyp:282`) and `gueGrid_twistBA` as `hoff` (`:259`); the unprimed one-loop/entry lemmas are not named.
C1 regex on the 20 public statements (`$S/c1.py`; `msc|mE|lemE|lemT|zt|etaT|gueScale|mSigma|envConst|gapK|Kstab3|Theta|STKloop|STKbound|STLK|STLocalEntry|STExp2|kTwoGUE|kTwoGUELoop|GUEPathBounds|gueEntryMix|mixMat|gueH` as whole words; `Pgue`/`PathΩ` only at `sz.withLam 0`): 0 hits in all 20.

## 4. Hidden hypotheses, vacuity, cycles
- No `structure` is introduced (grep of declarations: `def`/`abbrev`/`theorem`/`example` only); `GUEPathBoundsBA`, `BAKFam`, `BAPB` are row a's `Prop` defs, `rfl`-equal to the signed texts (§2).
- Dependencies are merged results on `main` 662acb30 (rows a, b, b′, c; C3, C4, C5g); the only new module imports are the two leaves; `GUEHyp` imports `GUELLBA`, not conversely.
- No new owed/structural premise: full-build scan 124 premises, same classification counts, 0 unclassified.

## 5. Compiled nonempty instances (target 17 and each target; `d = 3`)
| target | instance (file:line) | data | open hypotheses |
|---|---|---|---|
| 13 `oull_of_pathBoundsBA` | GUELLBA:372 | `S0`, `E ≡ E_*` (`cls_bulk`), `τU = 1/100`, `t_n = N^{-1+τU}`, `δ = 1/10` | `hP : BAPB …` |
| 14 `gueGrid_eq729BA` | GUEHyp:1318 | `S0`, flow point `(g₀,E_*,m₀)` of `fp 4`, `1-t₀ = g₀²/128`, `t₀-t₁ = x/(2N_n)`, `τU = 1/20`, `n0 = 4`; `Kt` from `gueK_existsBA`, `hP` from `gueGrid_pathBoundsBA` | `hLK hLoc hB` (the 3 conjuncts of `BAMO`) |
| 14 `Eq729B_perNBA` | GUEHyp:1426 | C4 b data at `sz0`, `n = 0`, `t₁ = 17/20`, `t₀ = 9/10`, `B = univ`, `p = 1` | `hX` (observation 2) |
| 14 `Eq729B_derivedBA` | GUEHyp:1245 | QUE point `z_n = E_* + i min(η_Q,1)`, `τU = 1/720` | none |
| 14 `Eq729B_eq747_of_eq729BA`, `_of_inputsBA` | GUEHyp:1374, 1273 | QUE point | `hMO`, `hP`/PB |
| 15 `baEq729_Kdisc` | GUEHyp:1054 | `L = 4`, `W = 2`, `N = 512`, `t₁ = 0`, `t₀ = 1/2`, `u = 1/4`, `Δ = 1/1024`, `b₂ = 1`; `hKb` by `GUEHyp_kTwo_le` | none |
| 16 `ba_prodG` | GUEHyp:1190 | GUE phase (below) | `hMO : BAMO 3 S0 zI t1I` |
| 16 `ba_LLG` / `ba_QueG` | GUEHyp:1201 / 1257 | QUE/LL points at `S0` | `hP` / `hMO`, PB |
| 17 `g1Rowk_of_inputsG` | GUEHyp:1403 | `S0`, `(1/6,1/10)`, `τU = ouTauMax` | `UNMLOutBA`, `UNLocAvgBA`, `UNQueBA` (named by the ticket) |
All compile in the module build (§1). Open hypotheses are `BAMO` (V3 pin `UNMLOutBA`'s conjuncts; Amend 5 item 4 allows it open) or `BAPB` (the output of `ba_prodG`, which is conditional on `BAMO`); the target-17 example chains the three producers with only the ticket-named pins open.
**Amend 5 item 4 (C5D-C2), producer instance `GUEHyp:1190-1197`, read in full:**
- `zI := fun _ => ⟨E0, etaI⟩`, `E0 = (fp 4 _).E` (bulk energy as `BA/MAPins:205-224`, which uses the same `S0`, `clsκ`, `fp 4`), `etaI := cI * g0^2 / (2 * 4^3)`, `cI = min c 1` from `ba_flowG 3 (clsκ 4 _)` (`c = (πκ)^5/2048 = (Im m₀)^5/2048 ≤ 1`, so the clamp does not change it); `t1I n := fI - Nsz S0 n ^ (-(1/20)) * (√fI * etaI)`, `τD = 1/20`. `grep -n -w zSeq` in both files: one hit, `GUEHyp:1070`, a docstring ("never at `zSeq`").
- Every premise of `RBG_Prod` except `MO` is a proof term: `Ed κ'` (`flowS0_spec … .1`, ∀ n), `0 ≤ t₁` (`t1I_nonneg`), `t₁ ≤ fT` (`t1I_le`), `fT < 1` (`fI_facts`), `h730` (`Eventually.of_forall`, equality), `hscale` (`GUEHyp_scale_ev`, a genuine `Tendsto` argument), `hell` (`Eventually.of_forall hellI`: `4^3(1-t1I n) ≤ g0^2`), `hell1` (`hell1I`). The pair `t₁ ≤ fT` / `L^d(1-t₁) ≤ λ²` is proved at every `n` from `1 - fT ≤ η/c = g₀²/128` and `fT - t₁ ≤ η`: not contradictory, not zSeq, no `False` premise. Stop rule item 5 not hit: the instance reads `ba_flowG`, `cls_bulk`, `S0_adm`, `fp` and `Nsz` arithmetic only.

## 6. Paper deltas
Proposed in the prove report (d) 6: `T2519da` (13: bulk energies, `ba_flowG` Lemma 2.8 facts, `M_xx = m`, PB at `n₀ = 4`), `T2519db` (14: eventual window, `BAReal ∀ n`, `2g²` zero mode, guarded K clauses, `n₀ ≥ 4`, no `hKb`), `T2519dc` (`t₀ ≥ 1/2` at the QUE scale), `T2519dd` (flow datum scaling). Targets 15, 16 equal the signed texts (no new delta; 16 is the merged RBG text). Every difference of the §3 table is covered. Existing D742-D745 cover rows a-c.

## 7. Line counts (Amend 5 items 2, 3, 6)
```
$ wc -l RBM3D/BA/GUELLBA.lean RBM3D/BA/GUEHyp.lean
     410 RBM3D/BA/GUELLBA.lean
    1443 RBM3D/BA/GUEHyp.lean
    1853 total
$ echo "GUELLBA 356-406: $((406-356+1)); GUEHyp 996-1042: $((1042-996+1)); 1044-1439: $((1439-1044+1)); sum $((51+47+396))"
GUELLBA 356-406: 51; GUEHyp 996-1042: 47; 1044-1439: 396; sum 494
```
Landed row d 1,853 ≤ 2,386 (C5D-L1; no REQ); C5 total 9,360 + 1,853 = 11,213 ≤ 12,000 (C5D-L2, 787 of 2,640 left). Per file: 410 and 1,443 < 1,500 (reserve not needed) < 2,000. Instance-section subtotal 494 (`GUEHyp_kTwo_le` 996-1042 is a private helper used only by the `baEq729_Kdisc` instance, `:1061`).

## 8. Observations (no RETURN)
1. Amend 5's "from `n = 13`" for `hscale` is not reproduced: the instance proves `hscale` eventually via `GUEHyp_scale_ev`, threshold `N_n^{19/20} √fT η ≥ 1` with `η` depending on the chosen flow point `fp 4` (`Im m₀`, `g₀` not numerically explicit). `N_n = 64(2(n+1))^{15}` grows polynomially, so the threshold is moderate for any `√fT η ≥ 1e-22` (prover table); not a degeneracy. The prover proposes restating it as the formula (prove (d) 2).
2. `Eq729B_perNBA` (a per-`n` helper of target 14, not bold in the ticket) keeps the deterministic one-loop input `hX` open in its example at `sz0`, `n = 0`, with C4 b's `B = univ`, `p = 1` device. Its endpoint consumer `gueGrid_eq729BA` has a complete instance (§5) in which `Eq729B_perNBA` is applied with `hX` supplied by `gueGrid_expect_oneLoopBA'`; no statement or vacuity issue.
3. Public unpinned vocabulary `Eq729BA_eqErr`, `Eq729BA_Concl`, `Eq729BA_t0/g/E/t1/m` is named as the BA twin of the band `Eq729B_*` vocabulary rather than with the file stem `GUEHyp_` (§3 (E)); it appears in target statements, so it must be public; 0 name clashes on `main` (prove report grep).
4. Optional Amend 5 item 4 (primed `twist_sz0` without `hKb`) not done; optional.

## 9. Verdict
- Target 13 `oull_of_pathBoundsBA`: **PASS**.
- Target 14 `Eq729B_perNBA`, `gueGrid_eq729BA`, `Eq729B_eq747_of_eq729BA`, `Eq729B_derivedBA`, `Eq729B_eq747_of_inputsBA`: **PASS**.
- Target 15 `baEq729_Kdisc` (= `T2519_KdiscBA`): **PASS**.
- Target 16 `ba_prodG`, `ba_LLG`, `ba_QueG` (= `T2519_ProdBA BAKFam BAPB`, `T2519_LLBA BAPB`, `T2519_QueBA BAKFam BAPB`; exact merged RBG types): **PASS**.
- Target 17 instances (producer instance in the GUE-phase regime, C5D-C2): **PASS**.
**Overall: PASS.** No dispatcher sign-off needed.
