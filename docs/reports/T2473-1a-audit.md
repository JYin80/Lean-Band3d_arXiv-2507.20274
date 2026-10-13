Auditor model: claude-opus-5-5
# T2473 (ST T4s2): 1a-audit (design gate D1-D3 + probe), Mon Oct 12 23:17:37 UTC 2026
Inputs: `docs/tickets/T2473.md` (V3 + dispatcher answers §276 (3)), `docs/tickets/checks/T2473-check.lean`, `docs/reports/T2473-prove.md` (a), (a″) (163 lines), branch `t/T2473` b8c9b113. Audit worktree: `/Users/junyin/Lean_proof/RBM3D-wt/T2473-1a-audit` (detached at b8c9b113). Scratch: `scratchpad/T2473/audit/` (H28).

**Verdict: RETURN, needs dispatcher sign-off (H183 (3): 1b does not start).** All 13 deliverable rows are filled, the probe compiles with the standard axioms, the numerics rerun byte-identically, and the target 2-4 texts are `Iff.rfl` to the pins. Two binding stop lines of the ticket are hit, though; the 1a reports them as flags F1 and F3 and still writes "Overall verdict: PASS". F2 is a premise substitution in a non-binding shape, and the dispatcher should approve it in the same answer.

## 1. Probe compile, size, hygiene, axioms (in my worktree)
```
$ date -u; lake env lean RBM3D/Probe/T2473Pins.lean 2>&1 | head -30; echo "exit=${pipestatus[1]}"; date -u
Mon Oct 12 23:12:34 UTC 2026
exit=0
Mon Oct 12 23:12:41 UTC 2026
$ lake build <the 8 imports of the probe> | grep -E "error|Build completed"     # oleans current
Build completed successfully (3889 jobs).
$ wc -l RBM3D/Probe/T2473Pins.lean ; grep -nE "sorry|admit|native_decide|^axiom" RBM3D/Probe/T2473Pins.lean; echo grep=$?
     400 RBM3D/Probe/T2473Pins.lean
grep=1
$ # Ax.lean = probe lines 1-397, each `example` renamed auditExN, `#print axioms` for 42 named decls (privates excluded)
$ lake env lean $A/Ax.lean 2>&1 | sed -E "s/^'[^']*' //" | sort | uniq -c; echo "exit=${pipestatus[1]}"
  42 depends on axioms: [propext, Classical.choice, Quot.sound]
exit=0
$ git diff --stat main...HEAD ; git diff --name-only main...HEAD -- RBM3D/Induction RBM3D/Path RBM3D/BA RBM3D/Chain | wc -l
 RBM3D/Probe/T2473Pins.lean | 400 +++++
 1 file changed, 400 insertions(+)
       0
```
The probe is ≤ 400 lines, exits 0, has no sorry, and the diff touches only the probe file, which is a sole writable file. Its `import RBM3D.BA.Step2BA` belongs to the probe only (BA readings at lines 390-395); the final `Chain` files must not import it.

## 2. Targets 2-4 against the binding pins (auditor's scratch `PinDiff.lean`)
PinDiff.lean is the probe (lines 6-397) plus check-file lines 162-230 (`T2473_GoodSetNg`, `T2473_GoodExitMeasNg`, `T2473_GridGoodNConclg`, `T2473_GridGoodNgL`) plus these four examples:
```
example ... : GoodSetNg Cm n u k Γ Λ Φ τ' D' H ↔ T2473_GoodSetNg Cm n u k Γ Λ Φ τ' D' H := Iff.rfl
example ... : GoodExitMeasNg Cm s v K ↔ T2473_GoodExitMeasNg Cm s v K := Iff.rfl
example ... : GridGoodNConclg Cm μ s t ↔ T2473_GridGoodNConclg Cm μ s t := Iff.rfl
example (d : ℕ) law Flow mkM T0 : GridGoodNgL d law Flow mkM T0 ↔ T2473_GridGoodNgL d law Flow mkM T0 := Iff.rfl
$ lake env lean $A/PinDiff.lean 2>&1 | head -20; echo "exit=${pipestatus[1]}"
exit=0
```
The band bridges compile in the probe. Target 2 (`GoodSetN ↔ GoodSetNg (bandStep2Mat sz E)`) and the target-3 bridges are `Iff.rfl`/`rfl` (99-108). Target 4 (`GridGoodN d ↔ GridGoodNgL d seqP STFlow (bandStep2Mat · (STflowE ·)) lemT`) goes through `bandFM_STIngR` (110-113). The BA reading `GridGoodNgL 3 … baStep2Mat … BAflowT0` typechecks (394).

## 3. Numerics rerun (scripts of (a), read-only, run from `scratchpad/T2473/audit/`)
```
$ python3 -I ../inst2.py > inst2.out; diff inst2.out ../inst2.out && echo SAME-as-prover-out
SAME-as-prover-out
$ sed -n 22,39p docs/reports/T2473-prove.md > rep_inst.txt; diff inst2.out rep_inst.txt
17a18
> ```                                   # only the closing code fence differs
$ python3 -I ../d3.py > d3.out; diff d3.out ../d3.out && echo SAME-d3; cat d3.out
SAME-d3
GridGoodGen      port  846 x0.88= 744 +new 160 +inst 120 +hdr 45 = 1069
GridEnvelopeGen  port  105 x0.88=  92 +new 120 +inst  60 +hdr 45 = 317
GridAssemblyGen  port  995 x0.88= 876 +new 140 +inst 150 +hdr 45 = 1211
AzumaProxyGen    port 1099 x0.88= 967 +new 270 +inst 150 +hdr 45 = 1432
T4s2a (GridGood+Envelope) 1386 | GridAssembly 1211 | AzumaProxy 1432 | two-row T4s2b 2643
own central 4029; ticket central 2900 (ratio 1.39); T2474 ticket 1900 -> landed 2627 (ratio 1.38); 2900*1.38=4010; REQ line 3900; max file 1432 < stop 2000
$ python3 -I ../d1.py | head -5
GridGoodN {'B': 32, 'M': 40, 'W': 7}
GridEnvelopeN {'B': 7, 'M': 19, 'W': 2}
GridAssemblyN {'W': 11, 'S': 11, 'M': 30, 'B': 3, 'K': 6}
AzumaProxyN {'B': 19, 'S': 17, 'W': 12, 'M': 57, 'K': 7}
AzumaProxyN2 {'W': 15, 'S': 16, 'M': 41, 'B': 7, 'K': 8}
```
I checked the exponents against the merged sources:
- `C_P = 11+(4k+4)max(0,1-τ')` (`AzumaProxyN2:33,905`).
- Rows A-D of `SumWeightedStepErrN_Stmt` (`GridEnvelopeN:600-603`) appear verbatim in probe 280-281.
- `D₁+4D+k+2C_P+8 ≤ C_K` is in `AssembledNg` (probe 223).
- `sz0` (`Defs/Sizes:260`: L = 4(n+1), W = (2(n+1))^5, λ = (2(n+1))^-6) matches `inst2.py`.

The instance is nondegenerate (K = 4 for GridGood; `K_n = ⌈N^64⌉` is forced by `N^{C_K} ≤ K n` in the pin, the band's structure). The Azuma-tail line fails at n = 0 and 1. That is the eventual threshold of an `∀ᶠ n` conclusion, not a hypothesis.

## 4. D1 census and route (a)
I reran `d1.py` and listed the names it puts in class M (`d1m.py`, a wrapper that prints the M set per file). The heuristic classes some kernel reads as M: `Theta`, `norm_Theta_le`, `uKer_eq_one_add`, `sum_norm_row_le`, `norm_t_mul_lt_one`.
```
$ grep -nw "norm_Theta_le\|uKer_eq_one_add\|sum_norm_row_le" RBM3D/Induction/{GridAssemblyN,AzumaProxyN2}.lean | cut -d: -f1,2
GridAssemblyN:595, :590, :624     AzumaProxyN2:561, :556, :593
```
All of these sit in the coarse row bound (`gridAsm_norm_Ugen_coarse` :616 and the `AzumaProxyN2` row-sum `_pub`), which K2 covers, as (a) (i) and target 10 state. The census also counts as M some initial-membership band reads (`adjacentBlockWeight_*`, `initialLoopValue_*`, `MLoop`, `AdjacentMismatch`) and instance-only reads (`zt_im` at `AzumaProxyN:1291`, `AzumaProxyN2:1574`, `azumaProxy_xmu` :1094). The 1a puts the first group in the no-field block (target 9) and the second in instance sections. Route (a) is unaffected, and the `prover-max` switch correctly does not fire. (Observation: the census heuristic is not a per-declaration table; the route conclusion holds.)

D2 in the probe:
- W, S, K and compat are discharged at `bandStep2Mat sz0 (STflowE z0)` (347-354).
- `GridDriftNg` is discharged at the band (356-359).
- W at `baStep2Mat sz0` is definitional (329-332, 391).
- LoopForm at BA is definitional up to `0 < Im m` (334-335).
- K1-K4 is T2471's merged `GridRepTailGen_Ker`, imported. There is no second named Prop (X1-C4); the U-C4/TN-C4 greps below are empty.
- `qvFormNg := (STeeUMg …).re`, with the band bridge proved (312-318).
- `GridAssemblyHypNg.hKer` replaces `hE`.
- `T2473_InitMem` is inline (target 9) and has a band discharge (374-380).
```
$ grep -nE "def .*[Kk]er\b|def Ugen|STGridRepNgL" RBM3D/Probe/T2473Pins.lean; echo exit=$?
exit=1
$ grep -nE "withLam|BAflowLam0|gK" RBM3D/Probe/T2473Pins.lean | cut -d: -f1 | tr '\n' ' '
137 393 394                     # docstring, BA instance, BA reading (no crossing; UBA-C1 not triggered)
$ grep -nE "<ticket hypothesis-rule pattern>" RBM3D/Probe/T2473Pins.lean | awk -F: '$1>=30 && $1<=306' | cut -d: -f1
111 112 125 171 185 186 269     # 111-112 band bridge; the rest docstrings: no generic text hit
```
I reran the name-clash check (48 names of `clash.sh`, `git grep -w`) on HEAD and all 31 branches `t/T245x`-`t/T2478` except `t/T2473`. It printed no hit.

## 5. Binding stop lines hit (each needs a dispatcher decision)
**S1 = F1: the split boundary does not fit; third row.** The ticket pre-signs a split at T4s2a (targets 1-5, ≈ 1,350) | T4s2b (targets 7-10, ≈ 1,550), and says "a third row (central > 3,900) is a short REQ". The rerun D3 gives:
- own central 4,029 > 3,900;
- T4s2b = GridAssemblyGen 1,211 + AzumaProxyGen 1,432 = 2,643, beyond the 1,950 row size.

No file reaches the 2,000-per-file stop (maximum 1,432). The stop rule "the split boundary does not fit" fires, and the remedy (third row: GridAssemblyGen | AzumaProxyGen, plus a short REQ) is the dispatcher's.

**S2 = F3: a premise outside (a)-(i).**
- `SumWeightedStepErrNg_Stmt` (probe 278) takes `∀ n, (Cm.m n).im ≤ 1`.
- The envelope text (probe 260) takes `0 < Cm.eta n v ∧ Cm.eta n v ≤ 1 - v`. That is the premise `hη` of the merged window lemma `exists_norm_KI_le_wing` (`HierDriftGen:1087`), whose use the ticket allows ("the 𝒦 window comes from `STKboundgL` or is inline").
- `DecayGen_Spec` (`DecayGen:91`) gives only `0 < κm`, `κm ≤ Im m` and `η = (1-t) Im m`.
- The band originals take `|E n| ≤ 2 - κ` (`GridEnvelopeN:114, 598`), which implies `Im m ≤ 1`.

So `Im m ≤ 1` is a new premise not in the ticket's list (a)-(i): stop rule 2, "the dispatcher amends". It has sources: band `hierDriftGen_band_eta` (probe 365); BA `BAm_norm_le_one` (used at `Graph/BAExp14c:715`, with its own side conditions; T4-BA). D3 depends on it. The 105-line port of `GridEnvelopeGen` relies on the E′ reduction `E′ = 2√(1-(Im m)²)`, which needs `Im m ≤ 1`. I checked `stepErrN` (`GridDriftN:289`) and `envConst` (`Path/OneStep:78`): both read E only through `etaT`. If the premise is refused, the target-5 sums must be ported and D3 redone.

**S3 = F2: premise substitution in target 4 (a)** (non-binding shape; listed for the same sign-off). In place of W + KCompat + measurability compat, `T2473_gridGoodNConclg_of_stmt` (probe 293-305) takes:
- `StepDecompGen_LoopForm Cm E`, which adds a free `E : ℕ → ℝ` and fixes `Cm.LM = loopFine … (ztOf (Cm.m n) (E n) u)`;
- T2467's merged `Step2EventsGen_Law Cm μ Hf` (F9's last conjunct).

Both texts are merged and one text (X1-C4). Their band discharges (347, 353) and BA sources (`baStep2Mat_loopForm` 334 up to `0 < Im m`; `Step2EventsGenTw_baLaw`) exist. Dropping KCompat is allowed (an unused premise). But the ticket names W and a measurability compat in (d), and dispatcher answer (4) separates W from F9. The use of F9's `Law` and the stronger LoopForm needs an explicit yes.

Not stop lines:
- BA initial membership has no source (vi): `grep -rlE "GoodSetN|GoodSetNg|zero_mem_goodSet" RBM3D | grep -v ^RBM3D/Induction/` prints nothing. Answer (5) covers it as an owed T4-BA item, not a RETURN.
- `[IsProbabilityMeasure Cm.Pp]` binders follow H258 (check :314-316).

## 6. Deliverables table (H250 (4)) and D1-D3
| # | status (auditor) |
|---|---|
| (i) exponent table | met; reproduced (§3); the `D₁` constant of `gridAsm_core` is not re-derived (stated in (a)) |
| (ii) instance n = 0, 1, 10, band and BA | met; byte-identical rerun |
| (iii) D1 census, route | met; route (a) confirmed (§4); census heuristic observation |
| (iv) D2 texts compiled | met (exit 0, 42 × standard axioms) |
| (v) vocabulary, `stepErrNg`, `qvFormNg`, bridges | met (T2474 names reused; `qvFormNg` bridge proved, 312-318) |
| (vi) BA initial membership | met: no source, owed T4-BA (answer (5)) |
| (vii) UBA-C1 | met: no crossing (grep §4) |
| (viii) hypothesis table | met, apart from the S2/S3 entries that need sign-off |
| (ix) registry preview | met: `STSEforLnConclgL`, `STEKDecaygL`, `STSEforLngL` → U2 / U2-BA |
| (x) `open private` / copies | met (89 file:line candidates plus copy list) |
| (xi) layout | met; corrected by probe finding 1 (`Chain/GridRepTailGen2` import) |
| (xii) size, split | filled, but **S1**: third row, short REQ |
| (xiii) name clash | met; rerun clean on 31 branches |

## 7. Paper deltas
No Lean statement exists yet; section (a) proposes no `T2473a…` candidate. At 1b, candidates are needed for the generic carrier forms, the `Im m ≤ 1` premise (if signed) and the BA initial-membership gap (observation; not a 1a deliverable).

## Required for resubmission (after the dispatcher's answer; a repairer cannot fix these alone)
1. **Dispatcher:** decide S1. Either a third row (GridAssemblyGen | AzumaProxyGen stacked on T4s2a) with the short REQ, or a re-estimate. Confirm whether T4s2a (targets 1-5, 1,386) may start its 1b alone.
2. **Dispatcher:** admit or refuse `∀ n, (Cm.m n).im ≤ 1` (S2) as an allowed premise of target 5, with its BA owner (T4-BA via `BAm_norm_le_one`). If refused, the 1a reruns D3 for `GridEnvelopeGen` without the E′ reduction.
3. **Dispatcher:** approve or refuse `Step2EventsGen_Law` plus `StepDecompGen_LoopForm Cm E` in target 4 (a)/(b) in place of W and the measurability compat (S3).
4. Then the 1a adds an (a‴) section recording the answers (the D3 table per row, the target-5 premise list), and the 1b starts under H183 (3).
