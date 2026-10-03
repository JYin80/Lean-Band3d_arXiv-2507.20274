Auditor model: claude-opus-5-5

# T2067 audit, round 2 (LW-P: `RBM3D/Graph/LWPins.lean`) — Sat Oct  3 19:31:25 UTC 2026
Branch `t/T2067` at 626f3a7 (repair commit on 6958dbd; merge base 65ccfb3). Audit worktree `RBM3D-wt/T2067-audit2` (detached), fresh scripts (`cmp2.py`, `ax2.lean`, `pre2.lean`) in `scratchpad/T2067/`.

## 1. Files, hygiene
```
$ git diff main...t/T2067 --stat
 RBM3D/Graph/LWPins.lean | 1008 +++++++
 RBM3D/Test/Axioms.lean  |   36 +-
$ git diff 6958dbd 626f3a7 --stat            (the repair)
 RBM3D/Graph/LWPins.lean | 36 ++++   (inst_LWReduceB, inst_LWReduceT only)
$ git diff main...t/T2067 -- RBM3D/Graph/LWPins.lean | grep -nE "sorry|admit|native_decide|^\+ *axiom|decide"
720:+  decide +kernel            (figAux_ghostOK; axioms [propext], see §2)
```
Only the two sole writable files. `Axioms.lean`: list additions only (owed: 16 pins + `LWInteg LWInit LWLoop2 LWLoopExp LWXi LWAvgLaw LWAssm LWAssmExp STLocalEntry`; structural: `LWWindow LWClass LWPsiRel LWPsiAll NGraph.{IsNested,NoGhost,GhostOK}`), as ticket target 3 / DECISIONS §20, §24 b.11. No existing registry line altered; no frozen signature touched.

## 2. Build, axioms, registry pre-check (audit worktree)
```
$ lake build RBM3D.Graph.LWPins
✔ [3345/3345] Built RBM3D.Graph.LWPins (6.2s)
Build completed successfully (3345 jobs).
$ lake build RBM3D
Build completed successfully (3782 jobs).
$ lake env lean ax2.lean   [collectAxioms over every non-internal constant of module RBM3D.Graph.LWPins]
declarations: 90; with a non-standard axiom: 0 []
'RBM.Gauss.LWInst.inst_LWReduceB' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.LWInst.inst_LWReduceT' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.LWReduceB' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.LWReduceT' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.LWInstFixed.inst_ssl' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.LWInst.figAux_ghostOK' depends on axioms: [propext]
$ lake env lean pre2.lean  [import RBM3D; import RBM3D.Graph.LWPins; #assert_rbm_axioms]   -> exit 0, error lines 0
axiom audit: 2194 theorems, 930 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
premises found by scanning: 66 (borrowed 2, owed 52, structural 12).
registry: 5 borrowed + 68 owed + 33 structural; ...
```
Main moved since the merge base (65ccfb3 -> 2be5aaf: new `Evolution/Prec.lean`, `Induction/Continuity.lean`, 5 lines of `Step34Pins.lean`; `Test/Axioms.lean` unchanged on main). Short-name clash grep of the 85 `def/theorem` names of LWPins against those three files on `main`: no match; `git grep LWInst main -- RBM3D` hits only `RBM.Graph.LWInstOwx` (LWStein), a different namespace. The hub's full build at merge is the final check.

## 3. Statements against the pin (probe `eeda441:RBM3D/Probe/T2040Graphs.lean`)
`cmp2.py`: cut each top-level declaration block in both files, rename `dH resPoly lwG lwGb lwGc lwGcb lwS lwSp lwf lwdf oe1xRest -> LWPins_<name>` (word boundary), compare strings.
```
$ python3 cmp2.py probe.lean LWPins.lean "<39 names>"
dH probe:745 new:62 IDENTICAL          resPoly probe:756 new:73 IDENTICAL     lwG probe:762 new:79 IDENTICAL
lwGb probe:763 new:80 IDENTICAL        lwGc probe:764 new:81 IDENTICAL        lwGcb probe:765 new:82 IDENTICAL
lwS probe:766 new:83 IDENTICAL         lwSp probe:767 new:84 IDENTICAL        lwf probe:777 new:94 IDENTICAL
lwdf probe:781 new:98 IDENTICAL        oe1xRest probe:804 new:121 IDENTICAL   LWweightExp probe:789 new:106 IDENTICAL
LWedgeExp probe:814 new:131 IDENTICAL  LWggExp probe:847 new:164 IDENTICAL    LWS probe:885 new:194 IDENTICAL
LWf probe:890 new:199 IDENTICAL        LWInteg probe:896 new:205 IDENTICAL    LWcut probe:902 new:211 IDENTICAL
LWE probe:909 new:218 IDENTICAL        LWInit probe:913 new:222 IDENTICAL     LWLoop2 probe:923 new:228 IDENTICAL
LWAssm probe:943 new:234 IDENTICAL     LWterm probe:949 new:240 IDENTICAL     LWtermB probe:964 new:255 IDENTICAL
LWLoopExp probe:983 new:274 IDENTICAL  LWAssmExp probe:992 new:283 IDENTICAL  LWtermExp probe:999 new:290 IDENTICAL
LWAvgLaw probe:1012 new:303 IDENTICAL  LWtermEXP probe:1020 new:311 IDENTICAL LWMoment probe:1034 new:325 IDENTICAL
LWMomentExp probe:1050 new:341 IDENTICAL LWXi probe:1069 new:360 IDENTICAL    LWAnpKey probe:1084 new:372 IDENTICAL
LWAnpKeyGh probe:1101 new:389 IDENTICAL LWAnp probe:1121 new:409 IDENTICAL    LWReduceB probe:1140 new:428 IDENTICAL
LWtermExpS probe:1406 new:447 IDENTICAL LWtermExpN probe:1421 new:462 IDENTICAL LWReduceT probe:1437 new:478 IDENTICAL
DIFF count: 0
$ python3 cmp2.py probe.lean LWPsi_main.lean "LWWindow LWClass LWPsiRel LWPsiAll"     (merged T2051)
LWWindow probe:919 new:47 IDENTICAL   LWClass probe:930 new:52 IDENTICAL
LWPsiRel probe:937 new:59 IDENTICAL   LWPsiAll probe:1077 new:66 IDENTICAL   DIFF count: 0
```
(re-flowed into columns.) Section contexts: probe `open RBM RBM.Gauss` / `section FlowData` / `variable (d L W : ℕ) [NeZero L] [NeZero W]` / `variable (g E t : ℝ)` / `section ExpansionPins` / `namespace RBM.Gauss.Sizes`, `open RBM RBM.Loop RBM.Path RBM.Gauss`, `variable {d : ℕ} (sz : Sizes d)` (probe 738–882, 1396–1400) occur identically at LWPins 55–191.
Paper spot check of the two reductions (`7_8_light_weight.tex`): lines 72–91 (proof of `lem:LWterm`, `lem: EWGn2_N` from `lem:LW_moment(_exp)` by Markov) — from `f_xy ≺ η_t⁻¹Ψ_t(0)Ψ_t(|a−b|)` to `(LW_conclusion)` = `LWReduceB` (premise `LWAssm`, `f`-bound with `Φ n 0 * Φ n |a−b|`, conclusion `Φ n 0 * Φ n(|a−b|)^2`); on `1−t > ĝ²/L²` from `f_xy ≺ η_t⁻¹(W^{-d}B_{t,0})^{1/2} 𝖳_t(|a−b|∧ℓ) + W^{-D}` to `(LW_conclusion_exp)` = `LWReduceT` (index subtype `lam²/L² < 1 − t`, `sfT … (min r ℓ)`, `+ W^{-D}`). Quantifier order: fixed `κ ε 𝔡 𝔠`, sizes, `z`, `t`, constants, then `D`, before the eventual `Prec`. Matches.
Binding (target 1): the merged `lwG`/`dhSample`/`lwPoly`/`lwS`/`lwSplus` (LWStein) are sequence-space objects `(sz, n, u, ω : sz.SeqΩ)`; the probe's are fixed-size on `PF d L W g`; kept as `LWPins_*` with the reason in the module doc and prove report (d).1 (T2067a). `LWPins_dH` = `deriv` along `Matrix.single α w 1` (D65/T2060a convention). No pin text changed, so the ticket's stop clause is not triggered.

## 4. Hidden hypotheses, vacuity, cycles
Every pin is a `def … : Prop` with all hypotheses in its signature; `LWAssm`/`LWAssmExp` are explicit conjunctions and registered owed. No theorem of the file is proved from a pin: no cycle. All `RBM` constants resolve to merged modules (imports: `Induction.Defs, Graph.{ScalingOrder,LWVocab,LWPsi,LWStein}, Defs.Tail, Evolution.Pins`; no `Probe` import). Random premises are registered owed; DECISIONS §29 boundary items are in preflight (a)(ii) (time `0 ≤ t ≤ lemT z < 1`, regime split S/N complementary, `∀ n` only in premises).

## 5. Compiled nonempty instances (every endpoint)
```
$ for p in <16 pins>; do grep -nE "\(h : $p 3\)" RBM3D/Graph/LWPins.lean; done
LWweightExp: 732 inst_ssl          LWedgeExp: 736 inst_edge          LWggExp: 741 inst_gg
LWterm: 567 inst_LWterm 761 inst_LWterm_endT                         LWtermB: 918 inst_LWtermB
LWtermExp: 626 inst_LWtermExp 771 inst_LWtermExp_endT                LWtermExpS: 939 inst_LWtermExpS
LWtermExpN: 783 inst_LWtermExpN    LWtermEXP: 666 inst_LWtermEXP 818 inst_LWtermEXP_endT
LWMoment: 638 inst_LWMoment 794 inst_LWMoment_endT                   LWMomentExp: 651 inst_LWMomentExp
LWAnpKey: 686 inst_AnpKey 806 inst_AnpKey_endT   LWAnpKeyGh: 952 inst_AnpKeyGh   LWAnp: 699 inst_Anp
LWReduceB: 972 inst_LWReduceB      LWReduceT: 988 inst_LWReduceT
```
Round-1 defect closed. `inst_LWReduceB` applies `h le_rfl (1/10) (1/10) (1/10) … (1/6) sz0 z0 flow_z0 tInst tInst_range.1 tInst_range.2 (1/20) 2 2 1 (fun _ => 1) Ψ0 Φ0 (assm_of hI hL) hf`; `inst_LWReduceT` applies `… (1/20) Ψ0 (ℓT tInst) (assmExp_of hI hL) D hD hf`. Explicit result types are the pins' conclusions at the data (accepted by the kernel; build §2).
Deterministic hypotheses discharged: `3 ≤ 3`; `κ ε 𝔡 = 1/10 > 0`; `STFlow` (merged `flow_z0`: `d = 3`, `L_n = 4(n+1)`, `W_n = (2(n+1))^5`); `0 ≤ 1/16 ≤ lemT z_n` (`tInst_range`); `ε₀ = 1/20 > 0`, `LWWindow` (`window0`), `LWClass` (`class0`), `LWPsiRel` (`psiRel0`) inside `assm_of`; `0 ≤ ℓ_t`, `ℓ_t ≤ (log W)^{10} ℓ_t` (`ℓT_one_le`: `1 ≤ ℓ_t`, `ℓT_window`) inside `assmExp_of`. Left as hypotheses: only random premises — `LWInit`, `LWLoop2`/`LWLoopExp` (owed), and `hf`, the `f_xy` bound that is the pin's own input (the Markov consequence of the owed `LWMoment`/`LWMomentExp`). `D > 0` is a universally quantified constant of the paper statement.
Nondegenerate: `Ψ0 = Φ0 = W_n^{-1}` (inside the window `W^{-3/2} ≤ · ≤ W^{-1/20}`), `ℓ_t ≥ 1`; the subtype index of `inst_LWReduceT` is all of `n` (`strict_all : lam²/L² < 1 − 1/16`, LWPins:611). No `N = 0`, empty index, collapsed window or `False` premise. Expansions: `d = 3, L = 3, W = 2, g = 1, E = 0, t = 1/2`, `P = X(true,0,1)·X(false,1,0)`, `3 ≤ L`, `|E| < 2`, `0 ≤ t < 1` by `norm_num`.

## 6. Paper deltas
Pins = signed T2040 design text: differences covered by T2040a, e–h, j–o (DECISIONS §24, numbered at this merge; `main:docs/paper-deltas.md:372` "其余 T2040a、e–h、j–o 等 LW 钉文入库时编号"), D63–D65 and D79 already numbered. New difference of this ticket (fixed-size expansion objects not bound to `Graph/LWStein`) proposed as T2067a (prove report (d).1). The repair adds instances only. Coverage complete.

## 7. Verdicts
| target | verdict |
|---|---|
| `LWweightExp`, `LWedgeExp`, `LWggExp` | PASS |
| `LWterm`, `LWtermB`, `LWtermExp`, `LWtermExpS`, `LWtermExpN`, `LWtermEXP`, `LWMoment`, `LWMomentExp` | PASS |
| `LWAnpKey`, `LWAnpKeyGh`, `LWAnp` | PASS |
| `LWReduceB`, `LWReduceT` | PASS (round-1 RETURN repaired: `inst_LWReduceB`, `inst_LWReduceT`) |
| binding (target 1), copy (target 2), registry (target 3), instances (target 4) | PASS |

Ticket verdict: **PASS**. No dispatcher sign-off needed.

## 8. Observations (no verdict effect)
- O1 (carried from round 1): the ported section-8 helpers in `RBM.Gauss.LWInst` are public and unprefixed (`one_le_W`, `Φ0`, `Ψ0`, `window0`, `class0`, `strict_all`, `ℓT`, `lam_le`, …; CLAUDE.md §3 (E)). No clash today (§2); a later `open RBM.Gauss.LWInst` next to `InductionDefsInst` could become ambiguous.
- O2: none of the five `Graph/LWStein` objects is bound; LW-05/06/07 inherit the bridge `PF d L W g` ↔ `sz.seqP` and the `t = 0` case (T2067a). The dispatcher may want to say this in the LW-05…07 tickets.
- O3: prove report b.3 says 84 declarations; the env scan finds 90 non-internal ones after the repair (all with standard axioms only). Only the report count is off.
