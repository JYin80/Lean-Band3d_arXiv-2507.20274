Auditor model: claude-opus-5-5
# T2356 audit (stage 1b, round 1) — Fri Oct  9 20:11:50 UTC 2026

Branch `t/T2356` at `86cc4f2` (merge-base with `main`: `cd712be`); audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2356-audit1` (detached, fresh build cache from main). Inputs: `docs/tickets/T2356.md`, `docs/tickets/T2356-1b.md` (E1-E5), `docs/reports/T2356-prove.md`, pins = probe `RBM3D/Probe/T2356Pins.lean` (design section 1, commit `fe9888f`). `$S` = auditor scratchpad `T2356/`.

## 1. Build, hygiene, scope (item 4)
```
$ git diff fe9888f t/T2356 -- RBM3D/Probe/T2356Pins.lean | wc -l      # the passed pins are unchanged on the branch
       0
$ lake build RBM3D.Universality.GUEPhase.Eq729B > $S/build.log 2>&1; echo exit=$?; grep -c "Eq729B.lean" $S/build.log; tail -2 $S/build.log
exit=0
0                                                   # no warning/error line in the new file
Build completed successfully (3818 jobs).
$ lake env lean RBM3D/Universality/GUEPhase/Eq729B.lean; echo exit=$?   # forced re-elaboration, no output
exit=0
$ grep -cE '\bsorry\b|\badmit\b|native_decide|^ *axiom ' Eq729B.lean; grep -c "DuhamelC\|^import RBM3D$" Eq729B.lean; wc -l < Eq729B.lean
0
0
1674                                                # E3: stop line 2400, no cut taken; Eq747.lean absent
$ git diff --name-status main...HEAD
A	RBM3D/Probe/T2356Pins.lean                      # probe: stays on the branch, not merged (H150)
A	RBM3D/Universality/GUEPhase/Eq729B.lean         # sole writable file of stage 1b
```
Imports (lines 6-15): `Eq729A OneLoop KPrim BootstrapAt HypA ZeroModeProfile Main.ZTransfer Main.QUEFromQDiff Loop.KLFinal Loop.KLTree` = the E2 list exactly; no `DuhamelC`, no `import RBM3D`. No merged file is modified, so no frozen signature is touched.

## 2. Statements against the passed pins, both directions (items 1, 2)
Independent check `$S/audchk.lean` (imports the probe and the new module; `fd_iff` converts the probe's `FlowData` and the file's `Eq729B_FlowData`, two Prop structures with the same three fields):
```
example : @Eq729Concl = @Eq729B_Concl ∧ @OUBody = @Eq729B_OUBody ∧ @initTerm = @Eq729B_initTerm ∧ @eqErr = @Eq729B_eqErr ∧ @zQ = @Eq729B_zQ := ⟨rfl, rfl, rfl, rfl, rfl⟩
example : PinGueGrid729 = type_of% @gueGrid_eq729 := rfl                       -- target 1: identical type
example : PinEq747OfEq729 ↔ type_of% @Eq729B_eq747_of_eq729 := by constructor ... -- target 2, both directions
example : PinEq747OfInputs ↔ type_of% @Eq729B_eq747_of_inputs := by ...          -- target 3, both directions
example : PinSTExp2OfUNMLOut ↔ type_of% @Eq729B_bridge := by ...
example : PinGoodFlow ↔ type_of% @Eq729B_goodFlow := by ...
example : PinDerived ↔ type_of% @Eq729B_derived := by ...
example ... : UNOUEq747 sz 𝔡 τU ↔ ∀ κ, 0 < κ → ∀ E, (∀ n, |E n| ≤ 2 - κ) → ∀ t, (∀ n, 0 ≤ t n ∧ t n ≤ ouTStar sz τU n) → ∀ τ, 0 < τ → Eq729B_OUBody sz 𝔡 E t τ := Iff.rfl
$ lake build RBM3D.Probe.T2356Pins | tail -1; lake env lean $S/audchk.lean; echo exit=$?
Build completed successfully (3818 jobs).
[12 #print axioms lines, section 4]
exit=0
```
Each bidirectional proof passes the hypotheses in the same order with no extra argument (`intro ...; exact h ... ((fd_iff ..).1/2 hF) ...`). So each file theorem is equivalent to its pin: it is neither stronger nor weaker.

Statement content, checked against the ticket's mathematics and 1b items (`B4` of the prove report matches the file text):
- Target 1 `gueGrid_eq729` [622-638]: `3 ≤ d`, `hlam`, `hell : ∀ᶠ n, L^d (1 - t₁) ≤ ilambda²`, `hKb : sz.STKbound E`, `hKinit` via `sz.STKloop` (the `Hyp_Kt_detDom` form), `hB : sz.STExp2 E t1`, `hP : GUEPathBounds` (pin). The conclusion `Eq729B_Concl` has `∀ δ > 0, ∀ᶠ n, … ≤ N^δ ((N η_{t₀})^{-3} + I₀(t₁))`, with `I₀` = the right side of `STExp2` (`Induction/Defs.lean:159`, verbatim). Parameters come before `∀ᶠ n`.
- Target 2 `Eq729B_eq747_of_eq729` [1077-1080]: `H729 : Eq729B_Concl sz E' t1 t0 K` ⇒ `Eq729B_OUBody sz 𝔡 E t τ`. That is the body of `UNOUEq747`, with error `qdBoundExp sz n τ (ouEtaQ sz 𝔡 n)` (Iff.rfl above). There is no `hell`.
- Target 3 `Eq729B_eq747_of_inputs` [1221-1235]: `τU ≤ ouTauMax 𝔠 𝔡`, `t n ≤ ouTStar`, flow data, `hgood` (∀ n facts, D630), the Kt hypotheses at `E'`, `hB : STExp2 E' t1`, and `hP`. It derives `h730`, `hscale`, `hell`, `hlam` and `hKb` itself; none of them is a hypothesis.
- Hidden hypotheses: `Eq729B_FlowData` (lines 87-90) has only the three defining equations of (7.47) (`E' = lemE z_n`, `t₀ = lemT z_n`, `t₁ = (1-ζ)t₀`, eventually). These are pinned data, not hidden assumptions, and `Eq729B_flowData_formulas`/`Eq729B_goodFlow` produce them. No other `structure`/`class` is assumed. `STExp2`, `STKbound`, `UNMLOut` and `GUEPathBounds` are merged definitions (`Induction/Defs.lean:159,174`, `Universality/Pins.lean:432`, `GUEPhase/Grid.lean:89`). `hKb` is discharged by merged `Sizes.stKbound_holds` (`Loop/KLFinal.lean:243`).
- No cycle: the module imports only merged modules (section 1), and the probe is not imported.

## 3. Compiled nonempty instances (item 3, E1)
`namespace RBM.Univ.GUEPhase.Eq729BInst` (lines 1339-1670) uses `sz0` (`d = 3`, `L = 4(n+1)`, `W = (2(n+1))^5`, `ilambda = (2(n+1))^{-6}`; at `n = 0`: `N = 2^21 = 2097152`):
```
[1476] inst_gueGrid_eq729   : ∃ Kt, sz0.STExp2 Ei tw1 → GUEPathBounds sz0 Ei tw1 tw0 (gueGridK sz0 3) 3 Kt → Eq729B_Concl …
        κ=1/10, τU=1/30, Λ=1, n0=3, E=0, 1-t₀=y=ilambda²/(2L³)>0, t₀-t₁=y/N>0 (window of positive length ∀ n);
        discharged: hsize (tendsto_size), hlam1, hE0, tw1_nonneg, tw1_le_tw0, tw0_lt_one, h730_at, hscale_at, hell_at,
        hKb0 (stKbound_holds), hKinit/hK/hK2 (gueK_exists ∀ n). Open: STExp2, GUEPathBounds (other gates' pins).
[1589] inst_eq747_of_eq729  : (H729 : Eq729B_Concl sz0 Ec T1c T0c (gueGridK sz0 3)) → ∀ τ>0, Eq729B_OUBody sz0 (1/10) Ei tU τ
        flow data = explicit formulas (fdc), K≠0 by gueGridK_ne_zero, tU = ouTStar = N^{-1+τU} > 0.
[1598] inst_eq747_of_inputs : (hML : UNMLOut 3) → ∃ E' t0 t1 Kt, FlowData ∧ good ∀ n ∧ (GUEPathBounds … → ∀ τ>0, OUBody …)
        τU = ouTauMax(1/6,1/10) = 1/720, hB by Eq729B_bridge, Kt by gueK_exists. Open: UNMLOut 3, GUEPathBounds.
[1562] inst_goodFlow   [1576] inst_derived   [1584] inst_bridge (hML : UNMLOut 3)
[1529] inst_claimA (n=7, 𝔡=3/10, τU=1/240)  [1535] inst_hell_of_scales (n=7, ζ=N^{-1+1/240}>0)
[1544] inst_assembly_747 (numeric)  [1617] inst_bctl_le_two_calB (n=0, η=2^{-18})  + 7 `example`s (lines 1621-1667)
```
Every endpoint (targets 1-3) and every E1 item (`goodFlow`, `bridge`, `hell_of_scales`, `claimA`, `assembly_747`) has an instance. The data are nondegenerate: `N ≥ 2^21`, nonempty `Zd 3 (L n)`, windows of positive length, no `False` premise, no astronomically large witness. The only hypotheses left open are other gates' pins (`STExp2`, `GUEPathBounds`, `UNMLOut`), plus target 1's own conclusion as the premise of target 2. The prove report's B6 has the limit check for these external pins: sizes go to 0, `Nη → ∞`, and `I₀/Bctl(t₁) → 0`.

## 4. Axioms (item 4)
```
'RBM.Univ.GUEPhase.gueGrid_eq729' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.GUEPhase.Eq729B_eq747_of_eq729' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.GUEPhase.Eq729B_eq747_of_inputs' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.GUEPhase.Eq729B_goodFlow' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.GUEPhase.Eq729B_bridge' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.GUEPhase.Eq729B_derived' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.GUEPhase.Eq729BInst.inst_gueGrid_eq729' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.GUEPhase.Eq729BInst.inst_eq747_of_eq729' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.GUEPhase.Eq729BInst.inst_eq747_of_inputs' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.GUEPhase.Eq729BInst.inst_bridge' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.GUEPhase.Eq729BInst.inst_goodFlow' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.GUEPhase.Eq729BInst.inst_derived' depends on axioms: [propext, Classical.choice, Quot.sound]
```
I did not rerun the full `lake build` or the registry pre-check (`#assert_rbm_axioms`). The hub runs them at merge. The prover's run (B9) reports exit 0.

## 5. Names, E3/E4
```
$ grep -nE "^(theorem|lemma|def|structure|abbrev) " Eq729B.lean   → 56 public names: 45 `Eq729B_*`, the pinned `gueGrid_eq729`, 10 `Eq729BInst.inst_*`
$ grep -rlw gueGrid_eq729 RBM3D | grep -v -e Probe/ -e Eq729B.lean   → RBM3D/Universality/GUEPhase/Eq729A.lean (line 15, docstring text only)
$ for n in perN arith final_729 gronwall_factor bctl_le_two_calB Ld_mul_etaQ hell_of_scales claimA h730_hscale_real qdBoundExp_eq assembly_747 STExp2_congr FlowData.ev_eq; …  → 13/13 public, UNModel=0 in each statement
```
E3: one row, 1674 lines (stop line 2400), no cut, and no 1b FAIL in chain links (i)-(iii) or in `PinDerived` (`Eq729B_derived` is proved; section 4). E4 is satisfied. E5 needs no action.

## 6. Paper deltas (item 5)
The Lean/paper statement differences are D628 (= T2356a: `I₀(t₁)` in (7.29) at `t₀`), D629 (= T2356b: (7.47) as `qdBoundExp` at `η_Q = W^{-𝔡/3} ilambda W^{d/2}/N`, profile `Θ̃_{ζ(t_n)}`), D630 (= T2356c: the `∀ n` flow facts `hgood`/`goodFlow`) and D631 (= T2352a: `hell`, `hKb`, `hKinit`). All four are present in `docs/paper-deltas.md:1587-1590`. The prove report proposes no new difference, and I found none.

## Observations (no effect on statement, instance, build, axioms, or delta coverage)
- O1: target 1's `hlam : ∀ᶠ n, 0 < ilambda_n ≤ Λ` is inherited from the merged `gueGrid_expect_oneLoop` (`OneLoop.lean:1308`). It is a consequence of the paper's `(eq:WO)`, and target 3 derives it, so it is not a paper difference. It has no delta entry; the design passed it (design line 31).
- O2: the probe stays on the branch (2 files in `git diff main...t/T2356`). Per H150, the merge brings in only `RBM3D/Universality/GUEPhase/Eq729B.lean`.

## Verdict
| target | statement | hidden hyp / cycle | instance | build / axioms | deltas | verdict |
|---|---|---|---|---|---|---|
| `gueGrid_eq729` | = pin (rfl) | none | `inst_gueGrid_eq729` | ok | D628, D631 | **PASS** |
| `Eq729B_eq747_of_eq729` | ⇔ pin | none | `inst_eq747_of_eq729` | ok | D629 | **PASS** |
| `Eq729B_eq747_of_inputs` | ⇔ pin | none | `inst_eq747_of_inputs` | ok | D629, D630 | **PASS** |
| `Eq729B_goodFlow`, `Eq729B_bridge`, `Eq729B_derived` | ⇔ pins | none | `inst_goodFlow`, `inst_bridge`, `inst_derived` | ok | D630 | **PASS** |

Overall: **PASS**. No dispatcher sign-off needed.
