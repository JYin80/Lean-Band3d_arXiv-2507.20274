Auditor model: claude-opus-5-5

# T2407 1a-audit round 2 (design gate of BA-L2c1, after the rule-(B) repair (a′), against Amend 1) — Sun Oct 11 04:56:53 UTC 2026

Inputs: ticket `docs/tickets/T2407.md`; Amend 1 `docs/tickets/T2407-amend-1.md` (CONTROL H203, binding); sections (a) and (a′) of
`docs/reports/T2407-prove.md` ((a′) written 04:52:50 UTC); round-1 list of this file; probe `t/T2395:RBM3D/Probe/T2395Pins.lean` at 4c1de4c.
Scratch: `$SP=/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/60e5425b-ae97-4201-b2dc-fc981af93073/scratchpad/T2407` (1a scripts), auditor's in `$SP/audit`.

## 1. Branch state (no Lean committed; stop line not reachable)
```
$ git rev-parse --short refs/heads/t/T2407; git log --oneline main..refs/heads/t/T2407 | wc -l
5ee937e
       0
$ git -C ../RBM3D-wt/T2407 status --short; wc -l ../RBM3D-wt/T2407/RBM3D/Graph/BAWeightOp.lean
?? RBM3D/Graph/BAWeightOp.lean
     183 ../RBM3D-wt/T2407/RBM3D/Graph/BAWeightOp.lean
```
(Untracked file of the stopped pre-Amend 1b, CONTROL H203 done 04:42:21; not audited.)

## 2. Item 1 (D1): verbatim pins
```
$ git show 4c1de4c:RBM3D/Probe/T2395Pins.lean | sed -n 105,128p | shasum | cut -c1-12
6589d94b2605
$ git show 4c1de4c:RBM3D/Probe/T2395Pins.lean | sed -n 239,241p | shasum | cut -c1-12
4506a4b8dd88
```
Both equal (a′) §1. The auditor read `lwverb.py` against probe `:110-128`: `bpS/bpM/bpW`, `lw2` leaf edges `[Ǧ_{αx}, Ǧ_{ββ}]`, `S_{αβ}`, `M_{xα}`,
`lw4` waved `[S⁺_{zy}, S_{αβ}]`, `M` edges `[M_{xz}, M_{zx}, M_{yα}]`, tail `owxDE (bpv 3) (bpv 2) q.1` + `bpS false (bpv 3) (bpv 1)`, and its
`owxDE` model (`counters.py:66-68`) against `LWWeightExp.lean:468-470`: identical. Model `Mp = M * M.T` = `BAlwMp` (`BAExpand.lean:78-79`). Rerun:
```
$ python3 lwverb.py struct 20000
parents 20000
lw2 leaf  terms  20000 delta [(1, 1, 1, 0)]  nM_ne 0  nAW_ne 0  nExt_ne 0  ordered_mismatch 20000  multiset_mismatch 0
lw2 tail  terms  40106 delta [(1, 1, 1, 0)]  nM_ne 0  nAW_ne 0  nExt_ne 0  ordered_mismatch 0  multiset_mismatch 0
lw4 leaf  terms  20000 delta [(1, 2, 2, 0)]  nM_ne 0  nAW_ne 0  nExt_ne 0  ordered_mismatch 0  multiset_mismatch 0
lw4 tail  terms  40106 delta [(1, 2, 2, 0)]  nM_ne 0  nAW_ne 0  nExt_ne 0  ordered_mismatch 0  multiset_mismatch 0
Q-level (members of splitG(T)): members, min(ord Q - ord P), #(ord Q == ord P), #(nM Q > nM P), #((nA-nW) Q > P), #(nExt Q > nExt P)
lw2 leaf  members  20000 min 1  eq 0  nM_up 0  nAW_up 0  nExt_up 0
lw2 tail  members 320848 min 0  eq 47216  nM_up 0  nAW_up 0  nExt_up 0
lw4 leaf  members  20000 min 1  eq 0  nM_up 0  nAW_up 0  nExt_up 0
lw4 tail  members 320848 min 1  eq 0  nM_up 0  nAW_up 0  nExt_up 0
$ python3 val.py 1 0 0 ; python3 val.py 2 0.5 0.3
W=1 g0=0.0 E=0.0 n=27  m=0.000000+1.000000j
|R|=3.281425e+00  |lw2|=4.922138e+00 |lw4|=1.640713e+00  |R - (lw2 + lw4)| = 6.237e-16
terms: lw2 has 3 graphs, lw4 has 3 (1 + #lwSplit p.2 each)
W=2 g0=0.5 E=0.3 n=216  m=-0.139326+0.723352j
|R|=1.562301e-02  |lw2|=7.602395e-03 |lw4|=8.383912e-03  |R - (lw2 + lw4)| = 8.155e-17
terms: lw2 has 3 graphs, lw4 has 3 (1 + #lwSplit p.2 each)
```
Identical to (a′). The pinned lists reproduce `BAlweightR` (`BAExpandW.lean:70-78`) including the red-edge branch of `owxDE`: no pin found wrong.
`lweightT1A/T1B/DB` and the four-expectation value form are declared superseded. Item 1: met.

## 3. Item 2 (D2): `baExpFrame_lw` against the first conjunct of `BAexpFrameE`
Token diff of (a′) line 133 against probe `:245-248` (normalised only: `RBM.BA.` prefix, `BAlwData d L W g0 Em t m ω` → `BAlwData …`, outer paren):
```
$ diff <(tr ' ' '\n' < a1n.txt) <(tr ' ' '\n' < pinn.txt)
114c114
< 0)
---
> 0)
\ No newline at end of file
$ wc -w a1n.txt pinn.txt
     114 a1n.txt
     114 pinn.txt
```
Same 114 tokens (only a trailing newline differs): hypotheses `NeZero L W`, `3 ≤ L`, `BASelf d L g0 Em m`, `0 ≤ t`, `t < 1`,
`p ∈ lwSplit Γ.solid`, `p.1.σ`, `p.1.circ`, `p.1.src = p.1.dst`, one `∫` of `baSum lw2 + baSum lw4` over `PF d L W 0`, in the pin's order.
Assembly lemmas named in (a′) §2 exist on `main` at the cited lines, with visibility as (a′) states (private ones to be copied):
```
BAExpandW.lean: BAExpandW_term_eq 541, BAExpandW_baPoly_edgePoly_prod 520, BAExpandW_term_tame1 554, BAExpandW_lanlwExt_term 570,
  BAExpandW_term_integral 638, BAExpandW_integral_val2 801, lanlw_val 908, baLweight_holds 354, baW_mul 268, baW_isUnit 247,
  baGcxx 980, BAlwData 98 (Sp field 102), private BAExpandW_integrable_PF 295
LWWeightExp.lean: owxEmb 454, LGraph.owxExt 458, owxDE 468, LGraph.term_owxExt 474, owx_list_aux 968, owx_sum_fin2 985
BAExpand.lean: baWx_baPoly 400, baWx_dh 485, baSelf_zero 865 (BASelf 3 3 0 0 I); lwStein_dh_listProd used at BAExpandW.lean:710
```
`W - 1 = M⁺ S W` from `baW_mul` (`W(1 - M⁺S) = 1`, square matrices) matches `Sp = S * BAlwW` (`BAExpandW.lean:102`). Item 2: met.

## 4. Item 3 (D3): T2395 §3 Step 3 form
T2395 design `:86`: "`T°` is `T` with every uncircled edge circled, `raw = ord T° - ord P`"; `:87` (a): `ord Q = ord P + raw - j + 2κ`,
`n_M(Q) ≤ n_M(P)`, `(n_A - n_W)(Q) ≤ (n_A - n_W)(P)`, `nExt Q ≤ nExt P`. Pin `BAstepMono` (probe `:269-270`) needs, per output `Q`:
`Normal`, `ord P ≤ ord Q`, `nM`, `nA - nW`, `nExt` not rising. (a′) §3 states `lw_counters`, `lw_raw` (`ord T° = ord Γ + 1`), `lw_mono`
(`nM`, `nA - nW` equal, `nExt T° ≤ nExt Γ`) and `lw_scalingOrderG` (`ord Γ ≤ ordG T`, i.e. every partition member), and assigns the
member-level `n_M`, `n_A - n_W`, `nExt` bounds and normality to L3a4. Facts it relies on, checked on `main`:
```
BAVocab.lean:91-95  atomAdj reads dotted (eq), psi, mdot only;  :124-126 adj = toLGraph.adj || atomAdj
BAVocab.lean:135-146 nS = solid.length, nW = waved.length, counters = ⟨nS,nW,nA,nM,0,0⟩, scalingOrder = ord counters
BAVocab.lean:158-159 Normal = (∀ dotted, eq = false) ∧ (∀ solid, circ = true)
BAExpandWOrd.lean:633 private BAExpandWOrd_splitG_of_circ : (∀ e ∈ Δ.solid, e.circ) → Δ.splitG = [Δ]
BAExpandWOrd.lean:803 lanlw_scalingOrderG : p ∈ lwSplit → σ → circ → Γ.Normal → ∀ Δ ∈ lanlwTerms Γ p, ord Γ ≤ Δ.scalingOrderG
private (to copy): _rho 328, _nA_lt 233, _packMerge_counters 648, _split3 670, _ext_ge 697
```
So circling does not change counters or `nExt` (`T°` and `T` agree), the two leaves are all-circled and normal (direct proof, which removes
the round-1 solid-order issue), and the `lw2` tail is the public `lanlw_scalingOrderG`. Numerics in §2: `min ≥ 0`, 0 rises. Item 3: met.

## 5. Item 4 (deliverable (iv)): plan against the stop line 2,000
(a′) §4 table, sums checked: low 70+380+230+350+150+70 = 1,250; central 80+500+260+450+200+90 = 1,580; high 100+650+300+550+260+120 = 1,980.
High < 2,000; check points after S0+S1 (≤ 650) and S2a+S2b (≤ 1,350); stop-and-report rule at projected 1,950. Item 4: met.

## 6. Item 5: instances and names
```
$ python3 instverb.py
baGcxx counters (1, 0, 1, 1) ord -1 ordG -1 nExt 0
   lw2 0 counters (2, 1, 2, 1) ord 0 ordG 0 nExt 0  ord-ord(Gamma) = 1
   lw4 0 counters (2, 2, 3, 1) ord 0 ordG 0 nExt 0  ord-ord(Gamma) = 1
baGwx counters (2, 0, 1, 1) ord 0 ordG 0 nExt 1
   lw2 0 counters (3, 1, 2, 1) ord 1 ordG 1 nExt 1  ord-ord(Gamma) = 1
   lw2 1 counters (3, 1, 2, 1) ord 1 ordG 0 nExt 1  ord-ord(Gamma) = 1
   lw4 0 counters (3, 2, 3, 1) ord 1 ordG 1 nExt 1  ord-ord(Gamma) = 1
   lw4 1 counters (3, 2, 3, 1) ord 1 ordG 1 nExt 1  ord-ord(Gamma) = 1
$ for n in BAGraph.ext bpv bpS bpM bpW baSum BAGraph.lw2 BAGraph.lw4 baExpFrame_lw BAWeightOp_ lw_counters lw_raw lw_mono \
    lw_scalingOrderG BAWeightOpInst; do echo "$n $(git grep -l -E "\\b$n" main -- RBM3D RBM3D.lean | wc -l)"; done
BAGraph.ext 0 | bpv 0 | bpS 0 | bpM 0 | bpW 0 | baSum 0 | BAGraph.lw2 0 | BAGraph.lw4 0 | baExpFrame_lw 0 | BAWeightOp_ 0
lw_counters 0 | lw_raw 0 | lw_mono 0 | lw_scalingOrderG 0 | BAWeightOpInst 0
$ git grep -n -B2 'structure BAGraph' main -- RBM3D/Graph/BAVocab.lean | head -1     # no @[ext]: no generated BAGraph.ext
main:RBM3D/Graph/BAVocab.lean-53-/-- A **block Anderson graph** (`B:290-297`): a graph of `def_graph1` (the merged record) with
```
Instance data `d = L = 3`, `W = 1`, `g₀ = E = 0`, `m = i` (`baSelf_zero`), `t = 1/2`; parents `baGcxx` (one term per list) and `baGwx`
(external vertex, two terms per list, the `lanlwD` tail attaining `ordG = ord Γ`); every deterministic hypothesis discharged. Same data
as the merged `lanlw_val` instance (`BAExpandW.lean:1059`). Item 5: met.

## 7. Per-deliverable verdict
| Item | Requirement (ticket / Amend 1 / round-1 list) | (a)+(a′) | Verdict |
|---|---|---|---|
| (i) term list, D1 | `BAGraph.ext`, `bp*`, `lw2`, `lw4` verbatim; `G̊_{xx}` only | verbatim (shasum), mapped, rerun on verbatim lists | PASS |
| target 2, D2 | `baExpFrame_lw` = first conjunct of `BAexpFrameE`; `baSum` verbatim; assembly | 114/114 tokens; lemmas exist | PASS |
| (ii) counters/order, D3 | `raw = ord T° − ord P`; `nM`, `nA − nW`, `nExt`; `ordG`; leaf fix | stated; facts checked; direct leaf proof | PASS |
| (iii) instances | one per target, nondegenerate | `baGcxx`, `baGwx`, `baSelf_zero` | PASS |
| (iv) plan vs 2,000 | line budget | 1,250 / 1,580 / 1,980, check points | PASS |
| C1 / L5 | uniform BA facts only | `BASelf`, `baM_row_sq`, `baW_isUnit` | PASS |
| stop line | `wc -l BAWeightOp.lean ≤ 2,000` | no Lean committed | not hit |

## Verdict: PASS
Every round-1 "Required for resubmission" item (1-5) and every Amend 1 item (D1-D3) is met; no binding stop line is hit; no dispatcher
decision is needed.

Observations (no RETURN):
1. (a′) §1 "The probe has no `gg2/gg4` in this file" is literally false (probe `:129`, `:141`); read as "BAWeightOp carries none (L2c2)" it is right.
2. Planned central 1,580 / high 1,980 exceed the ticket's 950 / 1,700 (Amend 1 adds the `Fin 4` list and `nExt`), still under the stop line;
   the 1b must honour the 1,950 check-point rule.
3. The verbatim copy needs the probe's section variables (`variable {E I : Type} [Fintype E] [DecidableEq E] …`, probe `:70`).
4. The Lean instance has scalar `M = i·1`; a non-scalar `BASelf` datum exists on `main` (`BAflow_real`, `GreenSchur.lean:59`; `flow_sz0`).
5. The untracked 183-line `BAWeightOp.lean` predates Amend 1; the 1b reconciles it with (a′).
