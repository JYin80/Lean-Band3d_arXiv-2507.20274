Prover model: claude-sonnet-5-5
## (a) Math preflight — Mon Oct 12 04:50:29 UTC 2026

### (i) Exponent table
No exponent or size threshold enters (identities of expectations; every term list is finite). Constants and hypotheses the targets 1-5 depend on:

| item | value / statement | constraint it must satisfy | slack |
|---|---|---|---|
| `d` | any `d : ℕ` (statements are `∀ d`-parametrised; `3 ≤ d` not used) | only `Idx d L W` is a nonempty `Fintype`, `NeZero L`, `NeZero W` | instance `d = 3` |
| `L` | `3 ≤ L` | hypothesis `hL` of `lanlw_val` (`BAExpandW:908`), `baExpFrameE_holds` (`BAGGOp:834-852`), `BAExpandId_integrable_val` (`:434`) | `L = 4`: slack 1 |
| `W` | `[NeZero W]` | as above | `W = 2` |
| `t` | `0 ≤ t < 1` | same lemmas (t = 0 handled inside them) | `t0P` with `0 < t0P < 1`: `flowP_data.1, .2.1` (`CouplingWindow:869`) |
| `BASelf d L g0 Em m` | `0 < m.im ∧ m = L^{-d} tr(BAMB …)` (`MFixedPoint:193`) | hypothesis of `lanlw_val`, `baExpFrameE_holds` | `(g0P, EP, m0P)`: `flowP_data.2.2` |
| `M a a = m`, `M a b = 0` (band `hM`, `hM0`) | not assumed (F5; false at BA) | not used: pathwise packing + merged BA frame identities | none needed |
| smallness of `g`, `P.g.Normal` | not used in targets 2-4; `P.g.Normal` stays (unused) in target 5 | pin verbatim | — |
| coefficients | `lanlwExt c = 1` (`BAExpandW:114-120`), `ext` coefficient `1` (`BAWeightOp:56`); derivative term `+1` | each split below is `G = Ǧ + M` with coefficient `+1` (`SEdge.val`, `LWVocab:115-117`; `BAMEdge.val`, `BAVocab:68`) | exact (script: `≈ 1e-13`) |
| hypotheses of the macros | (a) `p ∈ lwSplit P.g.solid`, `p.1.σ ∧ p.1.circ`; (b) additionally `(lwSplit p.2)[j]? = some q`, `q.1.σ = true` (`owxDE` blue branch, `LWWeightExp:468-470`) | `p.1.src ≠ p.1.dst`, atoms, `a ≠ a'`, `hwf`, `hnb` are **not** needed for the identities | none |
| file size | predicted ≈ 850 lines (v) | stop line 2,000 per file | ≈ 1,150 |

### (ii) One concrete nondegenerate instance
Data: `d = 3`, `L = 4`, `W = 2`, `(g0, Em, t, m) = (g0P, EP, t0P, m0P)`, `flowP_data` (merged, `CouplingWindow:869`; `BASymm2Inst` uses the same, `BASymm2:429-554`); `ℓe` any (a constant label).
Graphs: the five R1 data `baPA` (`BASim:1964`), `baPB, baPC, baPW, baPE` (`BASim3:1879-1890`); the `BAFrameStep` constructor hypotheses are discharged by `decide` in the merged example (`BASim:1973`, `BASim3:1951-1956`), so each frame step has the 5 kinds' hypotheses at once, nonempty output lists (`gg` at `P_A`: 31 outputs, `ggSplit` at `P_C`: 48 outputs, `BASim.lean`/`BASim3.lean` examples `decide +kernel`). Target 5 at `P := (baPG baPB).twist true true`, `outs := (withinOuts …).map (twist true true)` and at the twist of `baPC` (`j = 0`): `BALocStep` by `⟨true, true, F, twist_invol ▸ step, rfl⟩`; `P.g.Normal` by `ba_twist_inv_out` (`BASymm2:258`) / `decide`. Target 3 at a two-element list (e.g. `[baPG baPB, baPG baPC]`), `c = t' = true`.
No external hypothesis (the BA fixed point `BASelf` is the merged `flowP_data`; no limit computation is owed).

Pathwise check of the two split identities at `P_B` (macro (a)) and `P_C` (macro (b), `j = 0`) at one random complex sample of `(G, M, S, Sp, gPsi)` (`n = 3` labels, exact graph values summed over all internal labels, edge conventions of `SEdge.val`, `WEdge.val`, `BAMEdge.val`, `BAGraph.ext`, `lanlwT1`, `lanlwD`, `withinOuts`, `splitOuts` as in the files; negative controls drop one term):
```
$ python3 -I /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/60e5425b-ae97-4201-b2dc-fc981af93073/scratchpad/T2440/split_check.py
macro (a) P_B: |val T1 - (val first + val tr)| = 2.5421149729252077e-13  |val T1| = 166.04596157299886  |val tr| = 198.40886951814653
   control (drop M_{alpha y} from tr): 152.81865160727844
   (e, p.2) in lwSplit(tr.solid): True; |lwSplit p.2| = 2
macro (b) P_C: |val D_q - (dq1+dq2+dq3+dq4+tr)| = 3.592459381734991e-14  |val D_q| = 18.01971406295028  part norms: [57.707, 75.185, 38.114, 65.828, 55.538]
   control (drop dq4): 65.82764681011366
   (tr pair) pp in lwSplit(tr.solid): True ; qq in lwSplit(pp.2): True ; pp.src = qq.dst: True
```
`val T1`, `val first`, `val tr`, `val D_q`, `dq1..dq4` are the term values of `lanlwT1 Γ p`, the first graph of `withinOuts`, its transfer `tr`, `lanlwD Γ p q`, the four `dq` and `tr` of `splitOuts`.

### (iii) Section map `LWLvl1` §9-§11 (`:3077-3613`) → `BALvl1A` (as planned)
| band (file:line) | BA (planned) | supplied by / dropped |
|---|---|---|
| `PGraph.lvl1Comp`, `_val` `:3095, 3105`; `lvl1Outs` `:3133`; `lvl1Pack` `:3252` | none: R1's `BAPGraph.outsOf` (`BASim:52`) | R1 supplies |
| `lvl1_comp_val_factor` `:3439`; `lvl1_sum_flatMap` `:3433` | `BALvl1A_pcomp_val` (+ zero case): the child read through `P.ext` (generalises `BAExpandId_pcomp_val`, `:489-512`, `Fin 2` → `E`); `BALvl1A_sum_flatMap`, `BAComb.val` of `++` | ported/adapted |
| `lvl1_pack_identity` `:3450` | **target 2** `BALvl1A_pack`: `BAComb.val (P.outsOf Ts) D ℓe = baSum Ts D ℓ'` if `ℓe = ℓ' ∘ P.ext`, else `= 0 = P.val D ℓe`; pathwise, from `BAGraph.val_eq_partition` (`BAVocab:919`) | no integrability |
| `lvl1_pval_integrable`, `lvl1_term_integral` `:3145-3175` | dropped (needs `hM`); replaced by private integrability copies (iv) for the macro sums only | S′ drops |
| `StdNeutral`/`LocStd` `:3199-3226`; `lvl1WeightOuts0/EdgeOuts0/GGOuts0` `:3228-3250` | merged `BAGraph.LocStd`; R1's `lw2/lw4/lanlwTerms/gg2/gg4/withinOuts/splitOuts` | R1 / L2c supply |
| `LocStep` `:3260` | **target 1** `BALocStep` (probe 207-208 verbatim) | |
| `Lvl1Reach` `:3277` | **target 1** `BAReach` (probe 277-279 verbatim; def only) | |
| `lvl1_step_good` `:3290` | not here (L3a4) | |
| `lvl1_val_zero_of_xself`, `xBetween`, `oe1xT1_zero`, `oe2xR1_zero` `:3373-3432`; `lvl1_weight0/edge0/gg0_identity` `:3489-3589` | dropped: `×`-dot zeros and `hM`, `hM0` false at BA. Replaced by `baFrameStepIdentity_holds` (target 4), cases: `weight` `baExpFrameE_holds.1`; `edge` `lanlw_val`; `gg` `.2`; `within` `BALvl1A_macroA`; `ggSplit` `BALvl1A_macroB` | S′ drops |
| (new) | `BAtwistComb`, `baTwistComb_holds`: pathwise `(Q.twist c t).val D ℓe = cj^c (Q.val (BASymm1_dataTr D t) ℓe)` (`BASymm1_val_twist` `:261`, `BASymm1_data_real`; `BAPGraph.twist` keeps `ext`, `BASim:249`), `lwSymm_cj_list_sum`, then `baTwistIntegral_gen` (`BASymm2:104`) at `F D = BAComb.val Ls D ℓe` | L3a2 supplies |
| `lvl1_step_identity` `:3590` | `baLvl1StepIdentity_holds d`: `∫ P.val = ∫ ((P.twist).twist).val = cj^c ∫ (P.twist).val` (target 3 at `[P.twist c t]`, `BAGraph.twist_invol` `BASymm2:69`) `= cj^c ∫ BAComb.val F` (target 4 at `P.twist c t`) `= ∫ BAComb.val (F.map twist)` (target 3 at `F`) | no `hM`, `hM0` |

### (iv) The two split identities and the integrability route
Notation: `α = bpv 0`, `β = bpv 1`, `x = owxEmb p.1.src`, `y = owxEmb p.1.dst`, `R = p.2` embedded. `ℓe = ℓ' ∘ P.ext` (else both sides are `0` pathwise, target 2).
* **Macro (a)** (`within`). `lanlw_val` at `p`: `∫ P.g.val = ∫ (val T1 + Σ_{q ∈ lwSplit p.2} val D_q)`, `T1 = lanlwT1 Γ p` (`BAExpandW:122`) has solid `R ++ [Ǧ_{ββ}, G_{αy}]`, waved `S_{αβ}`, mdot `[M_{xα}]`. `G_{αy} = Ǧ_{αy} + M_{αy}` gives pathwise `val T1 = val first + val tr`, with `first` = solid `R ++ [Ǧ_{ββ}, Ǧ_{αy}]`, mdot `[M_{xα}]` (head of `withinOuts`, `BASim:56-62`) and `tr` = solid `R ++ [Ǧ_{ββ}]`, mdot `[M_{xα}, M_{αy}]` (term level, `ring` after unfolding `BAGraph.term`; `Finset.sum_add_distrib` over the same label type `I' ⊕ Fin 2`). Then `baExpFrameE_holds`.1 at `tr` and `pp = (Ǧ_{ββ}, R)` (`pp ∈ lwSplit tr.solid`: last position; verified in the script, `σ = circ = true`, `src = dst = β`): `∫ tr.val = ∫ (baSum (tr.lw2 pp) + baSum (tr.lw4 pp))`. Sum: `∫ P.g.val = ∫A + ∫ tr.val = ∫(A + B2 + B4) = ∫ BAComb.val (withinOuts)`, `A = baSum (first :: lwSplit-map lanlwD)`; the two `integral_add` need integrability of `A`, `tr.val`, `B2`, `B4`.
* **Macro (b)** (`ggSplit`, `q = (lwSplit p.2)[j]`, `q.1.σ = true`). `lanlw_val` at `p`, then split the `j`-th derivative term `D_q` (solid `q.2 ++ [G_{y'β}, G_{αa'}, G_{βy}]`, all three uncircled by `owxDE`, `LWWeightExp:468-470`; mdot `[M_{aα}]`) with `G_{αa'} = Ǧ_{αa'} + M_{αa'}` and `G_{y'β} G_{βy} = ǦǦ + ǦM + MǦ + MM`: pathwise `val D_q = val dq1 + val dq2 + val dq3 + val dq4 + val tr` (the five graphs of `splitOuts`, `BASim:63-74`; `tr` = solid `R_q ++ [Ǧ_{y'β}, Ǧ_{βy}]`, mdot `[M_{aα}, M_{αa'}]`). List step: `Σ_i val D_i = val D_j + Σ_{i≠j} val D_i` (`eraseIdx j`). `baExpFrameE_holds`.2 at `tr` with `pp = (Ǧ_{βy}, R_q ++ [Ǧ_{y'β}])`, `qq = (Ǧ_{y'β}, R_q)` (`pp ∈ lwSplit tr.solid`, `qq ∈ lwSplit pp.2`, `pp.src = qq.dst = β`; verified in the script): `∫ tr.val = ∫ (baSum gg2 + baSum gg4)`. Integrals as in (a) with four lists `A'`, `Q4 = [dq1..dq4]`, `B2`, `B4`.
* **Other kinds** need no integrability: `weight`, `gg`: one equation `baExpFrameE_holds` + target 2; `edge`: `lanlw_val` + target 2. Target 3 and 5: none.
* **Integrability route.** The private lemmas `BAExpandId_integrable_val`, `_baSum`, `_data_zero` (`BAExpandId:422-467`) are copied with the stem (`BALvl1A_integrable_val`, `BALvl1A_integrable_baSum`, `BALvl1A_data_zero`) as the dispatcher notes ask. **Finding (no pin repair):** the copies cannot avoid `open private` for the two primitives they call, `BAWeightOp_val_tame` (`BAWeightOp:644`) and `BAExpandW_integrable_PF` (`BAExpandW:295`), both `private` (precedent `BAExpandId:58-59`, `BAGGOp:47`); `BAVocab_val_of_factor/_of_not` are re-proved in two lines or opened likewise (`:60`). No public integrability lemma exists for `BAGraph.val` at `BAlwData`.

### (v) Predicted size
| part | lines |
|---|---|
| header, options, `open private`, `BALocStep`, `BAReach` | 65 |
| packing (target 2) + `BAtwistComb`/`baTwistComb_holds` | 125 |
| integrability copies | 45 |
| macro (a) 120, macro (b) 200 | 320 |
| `BAframeStepIdentity`, `baFrameStepIdentity_holds` (5 cases) | 110 |
| `baLvl1StepIdentity_holds` | 45 |
| instances (targets 2-5, five data, two `BALocStep`) | 140 |
| **total** | **≈ 850 (range 700-950)** |
Stop line 2,000; `BALvl1A2` is not needed (≤ 1,700). If the 1b exceeds 1,700 anyway: `BALvl1A` = header through target 4 incl. the macros, `BALvl1A2` (imports `BALvl1A`) = `baLvl1StepIdentity_holds` and the instances.

### Verdicts
* Target 1 (`BALocStep`, `BAReach`): PASS (probe text equals the merged-name statements; check file compiled exit 0, CONTROL H228 `done:`).
* Target 2 (packing): PASS. Target 3 (`BAtwistComb`): PASS (no `BASelf`, no integrability). Target 4 (`BAframeStepIdentity`): PASS (five cases; (iv) closes, script agrees, no normality). Target 5 (`BAlvl1StepIdentity`): PASS (`P.g.Normal` unused, kept).
* Instances: PASS (merged data at `d = 3`, `L = 4`, `W = 2`, `flowP_data`).

## (b) Script output - written Mon Oct 12 05:19:22 UTC 2026

### Line count against the stop line (2,000 per file)
```
$ wc -l RBM3D/Graph/BALvl1A.lean  (BALvl1A2.lean: not written, the 1a predicted <= 1,700 and the file stays below it)
     676 RBM3D/Graph/BALvl1A.lean
$ git diff --stat main...t/T2440 ; git log --oneline -1 t/T2440
 RBM3D/Graph/BALvl1A.lean | 676 +++++++++++++++++++++++++++++++++++++++++++++++
 1 file changed, 676 insertions(+)
ea4dd16 T2440: BALvl1A: compiled instances of targets 2-5 (five R1 data, twists of P_B, P_C), BAReach, reach_refl
```
### Build and axioms
```
$ lake build RBM3D.Graph.BALvl1A 2>&1 | grep -E "Built|Build completed|error"
Build completed successfully (3823 jobs).
$ grep -nE "sorry|admit|native_decide|^axiom" RBM3D/Graph/BALvl1A.lean ; echo "grep exit: $?"
grep exit: 1
$ #print axioms of every public declaration of the file (38 lines, script axioms.sh); the targets, packing and macro identities:
BALocStep : [propext, Classical.choice, Quot.sound]
BAReach : [propext, Classical.choice, Quot.sound]
baTwistComb_holds : [propext, Classical.choice, Quot.sound]
baFrameStepIdentity_holds : [propext, Classical.choice, Quot.sound]
baLvl1StepIdentity_holds : [propext, Classical.choice, Quot.sound]
BALvl1A_pack : [propext, Classical.choice, Quot.sound]
BALvl1A_macroA : [propext, Classical.choice, Quot.sound]
BALvl1A_macroB : [propext, Classical.choice, Quot.sound]
public declarations printed: 38; lines other than the standard three: 0
```
### Section map as finally written (iii; `LWLvl1` band line -> `BALvl1A` line; script secmap.py)
```
`PGraph.lvl1Comp`, `_val` :3095, 3105; `lvl1Outs` :3133; `lvl1Pack` :3252  ->  `BALvl1A_pcomp`:120, `BALvl1A_pcomp_val`:124, `BALvl1A_pcomp_val_zero`:140, `BALvl1A_val_of_factor`:104, `BALvl1A_val_of_not`:114, `BALvl1A_outsOf_eq`:147   [R1 `BAPGraph.outsOf` (BASim:52) supplies `lvl1Outs`/`lvl1Pack`]
`lvl1_sum_flatMap` :3433; `lvl1_comp_val_factor` :3439  ->  `BALvl1A_sum_flatMap`:155   [private copy]
`lvl1_pack_identity` :3450 (target 2)  ->  `BALvl1A_comb_append`:151, `BALvl1A_pack`:163, `BALvl1A_pack_zero`:176   [pathwise, no integrability]
`lvl1_pval_integrable`, `lvl1_term_integral` :3145-3175  ->  `BALvl1A_data_zero`:237, `BALvl1A_integrable_val`:249, `BALvl1A_integrable_baSum`:265   [dropped (need `hM`); integrability copies of `BAExpandId:422-467` for the macro sums]
`LocStep` :3260 (target 1)  ->  `BALocStep`:65   [probe 207-208]
`Lvl1Reach` :3277 (target 1)  ->  `BAReach`:69, `BALvl1A_reach_refl`:74   [probe 277-279; def only + refl theorem (audit scan)]
`lvl1_val_zero_of_xself` ... `lvl1_oe2xR1_zero` :3373-3432  ->  (none)   [dropped: `×`-dot zeros, false at BA]
`lvl1_weight0/edge0/gg0_identity` :3489-3589  ->  `BALvl1A_lwSplit_last`:282, `BALvl1A_sum_eraseIdx`:290, `BALvl1A_macroA_val`:309, `BALvl1A_macroA_graph`:334, `BALvl1A_macroA`:372, `BALvl1A_dq`:397, `BALvl1A_macroB_val`:403, `BALvl1A_macroB_graph`:423, `BALvl1A_macroB`:481, `BAframeStepIdentity`:85, `baFrameStepIdentity_holds`:509   [replaced by the five-case target 4]
(new, L3a2 `baTwistIntegral_gen`)  ->  `BAtwistComb`:79, `BALvl1A_pval_twist`:198, `BALvl1A_comb_twist`:209, `baTwistComb_holds`:221   [target 3]
`lvl1_step_identity` :3590 (target 5)  ->  `BAlvl1StepIdentity`:92, `BALvl1A_twist_invol`:540, `baLvl1StepIdentity_holds`:547   [no `hM`, `hM0`]
instances: `namespace BALvl1AInst` :558-672
```
### Statements of targets 1, 3-5 extracted from the file by script, and the script diff (diffstmt.py)
```
-- RBM3D/Graph/BALvl1A.lean:65-66
def BALocStep {E : Type} (P : BAPGraph E) (outs : List (BAPGraph E)) : Prop :=
  ∃ (c t : Bool) (F : List (BAPGraph E)), BAFrameStep (P.twist c t) F ∧ outs = F.map (BAPGraph.twist c t)
-- RBM3D/Graph/BALvl1A.lean:69-71
inductive BAReach (K : ℤ) : BAPGraph E → BAPGraph E → Prop
  | refl (P : BAPGraph E) : BAReach K P P
  | step (P Q R : BAPGraph E) (L : List (BAPGraph E)) : BAReach K P Q → Q.g.scalingOrder < K → ¬ Q.g.LocStd → BALocStep Q L → R ∈ L → BAReach K P R
-- RBM3D/Graph/BALvl1A.lean:79-82
def BAtwistComb (d : ℕ) : Prop :=
  ∀ (L W : ℕ) [NeZero L] [NeZero W] (g0 Em t : ℝ) (m : ℂ) {E : Type} (c t' : Bool) (Ls : List (BAPGraph E)) (ℓe : E → Idx d L W),
    ∫ ω, BAComb.val (Ls.map (BAPGraph.twist c t')) (BAlwData d L W g0 Em t m ω) ℓe ∂(PF d L W 0) =
      (if c then (star : ℂ → ℂ) else id) (∫ ω, BAComb.val Ls (BAlwData d L W g0 Em t m ω) ℓe ∂(PF d L W 0))
-- RBM3D/Graph/BALvl1A.lean:85-88
def BAframeStepIdentity (d : ℕ) : Prop :=
  ∀ (L W : ℕ) [NeZero L] [NeZero W], 3 ≤ L → ∀ (g0 Em t : ℝ) (m : ℂ), RBM.BA.BASelf d L g0 (Em : ℂ) m → 0 ≤ t → t < 1 →
    ∀ {E : Type} (P : BAPGraph E) (F : List (BAPGraph E)), BAFrameStep P F → ∀ ℓe : E → Idx d L W,
      ∫ ω, P.val (BAlwData d L W g0 Em t m ω) ℓe ∂(PF d L W 0) = ∫ ω, BAComb.val F (BAlwData d L W g0 Em t m ω) ℓe ∂(PF d L W 0)
-- RBM3D/Graph/BALvl1A.lean:92-95
def BAlvl1StepIdentity (d : ℕ) : Prop :=
  ∀ (L W : ℕ) [NeZero L] [NeZero W], 3 ≤ L → ∀ (g0 Em t : ℝ) (m : ℂ), RBM.BA.BASelf d L g0 (Em : ℂ) m → 0 ≤ t → t < 1 →
    ∀ {E : Type} (P : BAPGraph E) (outs : List (BAPGraph E)), BALocStep P outs → P.g.Normal → ∀ ℓe : E → Idx d L W,
      ∫ ω, P.val (BAlwData d L W g0 Em t m ω) ℓe ∂(PF d L W 0) = ∫ ω, BAComb.val outs (BAlwData d L W g0 Em t m ω) ℓe ∂(PF d L W 0)
$ python3 -I diffstmt.py   (check file `docs/tickets/checks/T2440-check.lean`, probe `t/T2395:RBM3D/Probe/T2395Pins.lean`)
BALocStep: check-file statement vs file statement (names mapped, whitespace normalized): IDENTICAL
BAtwistComb: check-file statement vs file statement (names mapped, whitespace normalized): IDENTICAL
BAframeStepIdentity: check-file statement vs file statement (names mapped, whitespace normalized): IDENTICAL
BAlvl1StepIdentity: check-file statement vs file statement (names mapped, whitespace normalized): IDENTICAL
BAReach: probe lines 277-279 vs file: IDENTICAL
BALocStep: probe def lines 207-208 (section variable {E : Type} written as the explicit binder of the check file) vs file: IDENTICAL
ALL IDENTICAL
$ lake env lean docs/tickets/checks/T2440-check.lean ; echo "exit code: $?"   (the check file on the branch)
exit code: 0
$ lake env lean crosscheck.lean   (imports BALvl1A, the check file Part 2 verbatim, then `example : BAtwistComb = T2440_TwistComb := rfl` and the same for the other three)
0
(number of error lines above; the four rfl examples compile)
```
### The compiled nonempty instances (`d = 3`, `L = 4`, `W = 2`, `flowP_data`; BALvl1A.lean:558-672); target 4 at the five R1 data, target 5 at the twists of `P_B`, `P_C`
```
$ grep -n "^example" RBM3D/Graph/BALvl1A.lean | cut -d: -f1   (line numbers of the examples: target 4, macros, target 3, target 2, target 2 zero case, target 5, BAReach)
581 602 611 617 636 654 666 
$ sed -n 581,600p   (target 4: five steps, nonempty output lists)
example :
    (∫ ω, (baPG baPA).val (BAlwData 3 4 2 g0P EP t0P m0P ω) ℓ0 ∂(PF 3 4 2 0) = ∫ ω, BAComb.val ggF (BAlwData 3 4 2 g0P EP t0P m0P ω) ℓ0 ∂(PF 3 4 2 0)) ∧
    (∫ ω, (baPG baPB).val (BAlwData 3 4 2 g0P EP t0P m0P ω) ℓ0 ∂(PF 3 4 2 0) =
      ∫ ω, BAComb.val ((baPG baPB).withinOuts pB) (BAlwData 3 4 2 g0P EP t0P m0P ω) ℓ0 ∂(PF 3 4 2 0)) ∧
    (∫ ω, (baPG baPC).val (BAlwData 3 4 2 g0P EP t0P m0P ω) ℓ0 ∂(PF 3 4 2 0) =
      ∫ ω, BAComb.val ((baPG baPC).splitOuts pC qC 0) (BAlwData 3 4 2 g0P EP t0P m0P ω) ℓ0 ∂(PF 3 4 2 0)) ∧
    (∫ ω, (baPG baPW).val (BAlwData 3 4 2 g0P EP t0P m0P ω) ℓ1 ∂(PF 3 4 2 0) =
      ∫ ω, BAComb.val ((baPG baPW).outsOf (baPW.lw2 pW) ++ (baPG baPW).outsOf (baPW.lw4 pW)) (BAlwData 3 4 2 g0P EP t0P m0P ω) ℓ1 ∂(PF 3 4 2 0)) ∧
    (∫ ω, (baPG baPE).val (BAlwData 3 4 2 g0P EP t0P m0P ω) ℓ0 ∂(PF 3 4 2 0) =
      ∫ ω, BAComb.val ((baPG baPE).outsOf (BAGraph.lanlwTerms baPE pE)) (BAlwData 3 4 2 g0P EP t0P m0P ω) ℓ0 ∂(PF 3 4 2 0)) ∧
    (0 < ggF.length ∧ 0 < ((baPG baPB).withinOuts pB).length ∧ 0 < ((baPG baPC).splitOuts pC qC 0).length ∧
      0 < ((baPG baPW).outsOf (baPW.lw2 pW) ++ (baPG baPW).outsOf (baPW.lw4 pW)).length ∧
      0 < ((baPG baPE).outsOf (BAGraph.lanlwTerms baPE pE)).length) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩
  · exact baFrameStepIdentity_holds 3 4 2 (by norm_num) g0P EP t0P m0P flowP_data.2.2 flowP_data.1.le flowP_data.2.1 _ _ hFA ℓ0
  · exact baFrameStepIdentity_holds 3 4 2 (by norm_num) g0P EP t0P m0P flowP_data.2.2 flowP_data.1.le flowP_data.2.1 _ _ hFB ℓ0
  · exact baFrameStepIdentity_holds 3 4 2 (by norm_num) g0P EP t0P m0P flowP_data.2.2 flowP_data.1.le flowP_data.2.1 _ _ hFC ℓ0
  · exact baFrameStepIdentity_holds 3 4 2 (by norm_num) g0P EP t0P m0P flowP_data.2.2 flowP_data.1.le flowP_data.2.1 _ _ hFW ℓ1
  · exact baFrameStepIdentity_holds 3 4 2 (by norm_num) g0P EP t0P m0P flowP_data.2.2 flowP_data.1.le flowP_data.2.1 _ _ hFE ℓ0

$ sed -n 642,662p, comment lines dropped   (targets 1 and 5: BALocStep at the twists of P_B and P_C, normality, the identity)
theorem locStepB : BALocStep ((baPG baPB).twist true true) (((baPG baPB).withinOuts pB).map (BAPGraph.twist true true)) :=
  ⟨true, true, (baPG baPB).withinOuts pB, by rw [BALvl1A_twist_invol]; exact hFB, rfl⟩
theorem locStepC : BALocStep ((baPG baPC).twist true true) (((baPG baPC).splitOuts pC qC 0).map (BAPGraph.twist true true)) :=
  ⟨true, true, (baPG baPC).splitOuts pC qC 0, by rw [BALvl1A_twist_invol]; exact hFC, rfl⟩
theorem normalB : ((baPG baPB).twist true true).g.Normal := (ba_twist_inv_out true true baPB).2.2.2.2.2 (by decide)
theorem normalC : ((baPG baPC).twist true true).g.Normal := (ba_twist_inv_out true true baPC).2.2.2.2.2 (by decide)
example :
    (∫ ω, ((baPG baPB).twist true true).val (BAlwData 3 4 2 g0P EP t0P m0P ω) ℓ0 ∂(PF 3 4 2 0) =
      ∫ ω, BAComb.val (((baPG baPB).withinOuts pB).map (BAPGraph.twist true true)) (BAlwData 3 4 2 g0P EP t0P m0P ω) ℓ0 ∂(PF 3 4 2 0)) ∧
    (∫ ω, ((baPG baPC).twist true true).val (BAlwData 3 4 2 g0P EP t0P m0P ω) ℓ0 ∂(PF 3 4 2 0) =
      ∫ ω, BAComb.val (((baPG baPC).splitOuts pC qC 0).map (BAPGraph.twist true true)) (BAlwData 3 4 2 g0P EP t0P m0P ω) ℓ0 ∂(PF 3 4 2 0)) ∧
    0 < ((baPG baPB).withinOuts pB).length ∧ 0 < ((baPG baPC).splitOuts pC qC 0).length :=
  ⟨baLvl1StepIdentity_holds 3 4 2 (by norm_num) g0P EP t0P m0P flowP_data.2.2 flowP_data.1.le flowP_data.2.1 _ _ locStepB normalB ℓ0,
    baLvl1StepIdentity_holds 3 4 2 (by norm_num) g0P EP t0P m0P flowP_data.2.2 flowP_data.1.le flowP_data.2.1 _ _ locStepC normalC ℓ0,
    by decide +kernel, by decide +kernel⟩
```
### Name-clash grep of the new public names (clash.sh), pre-check `import RBM3D` + `#assert_rbm_axioms`
```
$ clash.sh: grep -rnw each of the 27 new names over RBM3D/ outside BALvl1A.lean; git grep of the definitions on main, t/T2433, t/T2434, t/T2437-t/T2439
names with hits outside the file: BALocStep: 2 hit(s) outside BALvl1A.lean (the docstring mentions at BAScost.lean:158 and BASim.lean:198, not definitions); definition lines on the six branches: 0
$ lake env lean precheck.lean  (import RBM3D, import RBM3D.Graph.BALvl1A, #assert_rbm_axioms)
precheck.lean:3:0: error: axiom audit: 1 premise(s) that no theorem of this development proves are in none of `borrowedProps`, `owedProps`, `structuralProps`, `refutedProps`, `supersededProps`: ...
  [RBM.Graph.BAReach.below]
lean exit code: 1
$ the same with ONE scratch registry line `RBM.Graph.BAReach.below` added to a scratch copy of RBM3D/Test/Axioms.lean (scratchpad only, no file of the worktree touched), all root imports of RBM3D.lean except the three RBM3D.Test.*:
axiom audit: 12789 theorems, 4028 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
lean exit code: 0
(lines containing "error": 0)
```
### Narrative (all claims are checked by the output above or by the file)
* Delivered in one file `RBM3D/Graph/BALvl1A.lean` (676 lines, no split file; `RBM3D.lean` not edited: the root import is the hub's at merge, CLAUDE.md §1, §3 (A) 4; the branch diff is this one file).
* Target 2 (packing) is pathwise: `BALvl1A_pack` rewrites `BAComb.val (P.outsOf Ts)` through `BAGraph.val_eq_partition` and `BALvl1A_pcomp_val` (the child read through `P.ext`, `BAExpandId_pcomp_val` for any external type `E`); `BALvl1A_pack_zero` is the non-factoring case. No integrability, no data hypothesis.
* Target 3: `BALvl1A_pval_twist` (cases on whether `ℓe` factors, then `BAGraph.BASymm1_val_twist` at the chosen label) and `baTwistIntegral_gen` at `F D = BAComb.val Ls D ℓe`; no `BASelf`.
* Target 4, cases `weight`, `edge`, `gg`: one merged identity (`baExpFrameE_holds`.1, `lanlw_val`, `baExpFrameE_holds`.2) plus packing, with the non-factoring case by `BALvl1A_pack_zero`.
* Target 4, `within` (`BALvl1A_macroA`) and `ggSplit` (`BALvl1A_macroB`): `lanlw_val` at `p`; then pathwise at the term level (`BAWeightOp_ext_term`, `simp`, `ring`) `val (lanlwT1) = val first + val tr` (`BALvl1A_macroA_val`) and `val (lanlwD p q) = val dq1 + ... + val dq4 + val tr` for `q.1.σ = true` (`BALvl1A_macroB_val`), with `G = Ǧ + M` read off `SEdge.val`; the sum over `lwSplit p.2` is split at the `j`-th position by `BALvl1A_sum_eraseIdx`; the transfer graph `tr` goes through `baExpFrameE_holds`.1 (loop `Ǧ_{ββ}`) resp. `.2` (pair `Ǧ_{βy}`, `Ǧ_{y'β}`), the membership of the pair by `BALvl1A_lwSplit_last`. Integrability of the four sums only here: copies `BALvl1A_data_zero`, `BALvl1A_integrable_val`, `BALvl1A_integrable_baSum` of `BAExpandId:422-467`; they still call the two private primitives `BAWeightOp_val_tame`, `BAExpandW_integrable_PF` through `open private` (BALvl1A.lean:47-48, precedent `BAExpandId:58-59`); `BAVocab_val_of_factor/_of_not` are re-proved (`BALvl1A_val_of_factor/_of_not`), not opened. The two integrability lemmas are public, for later tickets.
* Target 5: `baTwistComb_holds` at `[P.twist c t']` and `F`, `BALvl1A_twist_invol`, `baFrameStepIdentity_holds` at `P.twist c t'`; `P.g.Normal` (`hN`) is not used.
* Hypotheses of targets 4, 5 are those of the pins: `3 ≤ L`, `BASelf`, `0 ≤ t < 1`; no `M a a = m`, no `M a b = 0`, no smallness of `g₀` (C1, F5).
* Instances: target 4 at `P_A`, `P_B`, `P_C`, `P_W`, `P_E`; the macros directly at `P_B`, `P_C`; target 3 at `[P_B, P_C]`; target 2 at `P_E`, `P_W` (`ext = id`) and, in the zero case, at `P2` (`ext` collapses two vertices, `ℓ0_not_factor`); target 5 at the twists of `P_B` (within), `P_C` (ggSplit, `j = 0`), `(c, t) = (true, true)`; `BAReach` one step below `K = 100`. No `N = 0`, empty list or `False` premise; the five output lists are nonempty (`decide +kernel`).
## (c) Verified Mathlib names (`#check` in a scratch file importing BALvl1A, no error)
`Finset.sum_add_distrib`, `Finset.sum_congr`, `MeasureTheory.integral_add`, `MeasureTheory.integral_congr_ae`, `MeasureTheory.Integrable.add`, `MeasureTheory.integrable_const`, `MeasureTheory.integrable_zero`, `List.map_flatMap`, `List.map_map`, `List.sum_eq_zero`, `List.mem_map`, `List.exists_mem_of_length_pos`, `List.append_assoc`, `List.eraseIdx_cons_succ`, `List.getElem?_cons_zero`, `List.getElem?_cons_succ`, `Function.Surjective.injective_comp_right`, `Pi.single_apply`, `Equiv.injective`, `map_zero`. Names verified absent: none (no name was invented).
## (d) Open issues and paper-delta candidates
1. **Registry (blocks the hub's merge build).** `#assert_rbm_axioms` rejects `RBM.Graph.BAReach.below`, the auxiliary predicate Lean generates for the recursive inductive `BAReach` (the same entry exists for `Lvl1Reach.below`, `RBM3D/Test/Axioms.lean:258`, T2128). That file is not in this ticket's writable files and the ticket says "Registry: none". The pinned inductive is recursive, as `Lvl1Reach`, so Lean generates `below` for it. Needed line in `structuralProps` (verified by the scratch run above, exit 0): `` `RBM.Graph.BAReach.below, -- auxiliary predicate that Lean generates for the recursive inductive `BAReach` (BA twin of `Lvl1Reach.below`; T2440) ``. `BAReach` itself is proved by the theorem `BALvl1A_reach_refl` (BALvl1A.lean:74); without it the audit also names `BAReach`.
2. Paper-delta candidate `T2440a`: target 5 keeps `P.g.Normal` (verbatim pin) although the proof does not use it (target 4 has no normality). Candidate `T2440b`: the frame steps `within`, `ggSplit` (R1) have no counterpart in the paper's text (only `lanlw`, `lem_lweight`, `GGGamma`); their identities are the paper's `lanlw` plus the pathwise `G = Ǧ + M` split of a transfer graph.
3. No correction of section (a) is needed ((a′) not written). The check file's `BALocStep` carries an explicit `{E : Type}` and the probe a section variable; the signatures agree (`rfl` cross-check above).
## (e) Repair under Amend 1 (rule (B), repair prover `claude-sonnet-5-5`), written Mon Oct 12 05:34 UTC 2026
Scope: `docs/tickets/T2440-amend-1.md`: one `structuralProps` line in `RBM3D/Test/Axioms.lean`, plus the root import line of `RBM3D.lean` (sole writable file) so that the full build contains `RBM3D.Graph.BALvl1A`. `RBM3D/Graph/BALvl1A.lean` is untouched (676 lines before and after; stop line 2,000).
```
$ git -C RBM3D-wt/T2440 diff --stat ea4dd16 HEAD
 RBM3D.lean             | 1 +
 RBM3D/Test/Axioms.lean | 1 +
 2 files changed, 2 insertions(+)
$ git -C RBM3D-wt/T2440 diff -U0 ea4dd16 HEAD | grep '^[+-]'
--- a/RBM3D.lean
+++ b/RBM3D.lean
+import RBM3D.Graph.BALvl1A
--- a/RBM3D/Test/Axioms.lean
+++ b/RBM3D/Test/Axioms.lean
+  `RBM.Graph.BAReach.below, -- auxiliary predicate that Lean generates for the recursive inductive `BAReach` (BA twin of `Lvl1Reach.below`; T2440)
$ git -C RBM3D-wt/T2440 log -1 --format='%h %an <%ae> %s'
0fac439 Jun Yin <321276894+JYin80@users.noreply.github.com> T2440: registry line RBM.Graph.BAReach.below (Amend 1), root import of RBM3D.Graph.BALvl1A
$ sed -n 257,259p RBM3D/Test/Axioms.lean | cut -c1-90     (the new line is :259, after the band twin's :258)
   `RBM.Graph.lvl1Split.below, -- auxiliary predicate that Lean generates for the recursive inductive `lvl1Split`
   `RBM.Graph.Lvl1Reach.below, -- auxiliary predicate that Lean generates for the recursive inductive `Lvl1Reach`
   `RBM.Graph.BAReach.below, -- auxiliary predicate that Lean generates for the recursive inductive `BAReach` (BA
$ wc -l RBM3D/Graph/BALvl1A.lean
676 RBM3D/Graph/BALvl1A.lean
$ lake build RBM3D.Test.Axioms
✔ [2/2] Built RBM3D.Test.Axioms (3.4s)
Build completed successfully (2 jobs).
$ date -u; lake build  (full library, RBM3D.lean:487 imports RBM3D.Graph.BALvl1A; RBM3D.lean:490 is #assert_rbm_axioms)
Mon Oct 12 05:32:28 UTC 2026
$ grep -n "error\|axiom audit\|Build completed" full.log ; grep -c error full.log
5174:info: RBM3D.lean:490:0: axiom audit: 12796 theorems, 4028 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
5389:Build completed successfully (4258 jobs).
0
(date -u at the end of the full build: Mon Oct 12 05:33:19 UTC 2026; exit code 0)
$ lake build RBM3D.Graph.BALvl1A | tail -1
Build completed successfully (3823 jobs).
```
* Before the repair the scratch pre-check of section (b) rejected exactly one premise, `RBM.Graph.BAReach.below`. After: the full build passes `#assert_rbm_axioms` with 12796 theorems, 4028 definitions, 0 axioms (audit line above).
* The repair adds no hypothesis, changes no signature and no target; sections (a)-(d) are unchanged.
* For the merge: the root import is committed at `RBM3D.lean:487` on `t/T2440` (directly after `import RBM3D.BA.TwistGridRem2`). If another branch has appended imports to `RBM3D.lean` meanwhile, the line should be added to main's copy (union, CLAUDE.md §3 (A) 4), not taken by checking out the branch's file.
