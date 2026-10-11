Auditor model: claude-opus-5-5

# T2404 1a-audit, round 2 (stage-1a design gate): Sun Oct 11 03:05:18 UTC 2026

Inputs: ticket `docs/tickets/T2404.md`; `docs/reports/T2404-prove.md` section (a) (unchanged, lines 3-69) and section
(a′) (lines 71-169, stamped 02:58:33 UTC); round-1 list (my previous version of this file, 02:39:42 UTC).
`t/T2404` = 1181514 = main base, `git diff --stat main...t/T2404` empty (no Lean yet, as expected).

## 1. Numerics rerun (scripts copied unchanged to scratchpad/T2404/audit2/)
```
$ python3 hk2.py ; diff <(python3 hk2.py) ../o_hk2.txt && echo same_hk2
rate=1  A: n~3.94e+4 (logW=56.4) | B: n~2.277e+10 (logW=122.7)
rate=0.5  A: n~8.778e+18 (logW=221.6) | B: n~1.006e+42 (logW=487.0)
rate=0.1  A: n~1.069e+478 (logW=5507.0) | B: n~4.246e+1054 (logW=12145.3)
at n=1e60: marginA(rate1)=13135.9 marginB(rate1)=10634.6 marginA(rate.1)=-3327.0 marginB(rate.1)=-5828.4
same_hk2
$ python3 j.py ; diff ... && echo same_j
n=1e+06: log10 w=-94.5  log10 J=-1.89  J>=w: True  Bctl>=cB*w: True
n=1e+30: log10 w=-454.5  log10 J=-9.09  J>=w: True  Bctl>=cB*w: True
n=1e+60: log10 w=-904.5  log10 J=-18.09  J>=w: True  Bctl>=cB*w: True
tau 1/100 3*tau/10 = 3/1000 < tau/2 = 1/200 : True  slack exponent 1/500
tau 1/20 3*tau/10 = 3/200 < tau/2 = 1/40 : True  slack exponent 1/100
tau 1 3*tau/10 = 3/10 < tau/2 = 1/2 : True  slack exponent 1/5
same_j
$ python3 -I kinds.py | tail -1 ; python3 -I lines.py
TOTAL mentions (incl. docstring words) = 396
EMn2Poly  A= 117 R=  40 A+R= 157 A-R=  77
EMn2Exp1  A= 315 R= 110 A+R= 425 A-R= 205
EMn2Exp2  A= 331 R=  49 A+R= 380 A-R= 282
TOTAL     A= 763 R= 199 A+R= 962 A-R= 564   (+-25%: A+R in [721,1202])
if the four intermediates are not frozen (no old-name corollaries): A=645 A+R=844
```
All of these reproduce the report verbatim, and so do the 12 per-kind rows of `kinds.py` and every `stmt.py` row. The round-1
scripts `inst.py`, `inst2.py` and `e.py` were rerun in round 1 and are unchanged.

## 2. Round-1 "Required for resubmission" list against (a′)

| # | round-1 requirement | (a′) | status |
|---|---|---|---|
| 1 | (i) one row per band fact: file:line → generic form → BA source → C1 mark; incl. `emn2Exp_kellStar_far`, Step2Iterate/KellStar facts, `ekPropTInf_holds` coupling, `STInitialGT2gL`/`STLWassm(Exp)gL` | H1-H14 table, lines 76-92 | met |
| 2 | row 11: drop `Prop5Decay`, use G3b/`BAKsolve`, redo the limit check | lines 94-102, `hk2.py` | met |
| 3 | row 15: Hermitian realization in carrier form, BA source, owner of the public form | H1 (line 78) | met |
| 4 | (ii) full statements of T1, T2 (and 5′), names, quantifier order, corollary chain | lines 104-115 | met |
| 5 | (iii) band objects with their carrier reading; `rfl` failures | lines 117-139 | met |
| 6 | (iv) predicted lines vs 1,000; I1 answer | lines 141-162 | met |

Spot checks on the claims behind the rows (merged Lean, verbatim):
```
$ python3 -I reads.py      # declarations of the upstream modules named in the three files (word match)
Induction/Step2Iterate: ST_Bdata_holds(5) ST_step2_of_pins'(2) hs0(8) ht1(10) htT(19)
Induction/Step2Events: STLWB_of_LWterm(1) STLWT_of_LWtermExp(1) ST_JhatM_nonneg(3) ST_STprof_pos(3) ST_W_tendsto(3)
  ST_Wpow_le_size(1) ST_flow_im_pos(7) ST_prec_mono_eventually(4) ST_prec_sup(1) ST_prof_le_Bctl(4) ST_rpow_neg_half(1)
  ST_rpow_sq(1) ST_size_pow_big(1) ST_size_pow_small(1) ST_size_rpow_neg_le(1)
Path/KellStar: KellStarEv(6) kellStarEv(7)
Evolution/PropTInf: ekPropTInf_holds(7) pti_sum_radial(3)
```
`hs0/ht1/htT` are local hypothesis names. `ST_step2_of_pins'` occurs only in the instance section (`EMn2Exp2:1293`), and
`STLWB_of_LWterm`/`STLWT_of_LWtermExp` only in a docstring (`:39`). So "of Step2Iterate only `ST_Bdata_holds`" (line 92)
holds. `pti_sum_radial` is the existing `open private` (`EMn2Exp2:53`), so no new private name is opened.
```
$ grep -n "kellStarEv\|STKloop\|emn2Exp_kellStar_far" EMn2Exp1.lean EMn2Exp2.lean   (code hits, docstrings dropped)
EMn2Exp2.lean:717,719,724 emn2Exp2_STKloop_two | :728,730,732 emn2Exp2_norm_STKloop | :764,768,783,784 loop2_far_le
EMn2Exp2.lean:939: have hK := emn2Exp_kellStar_far …  | :1241 instance | EMn2Exp1.lean:1637,1645 def, :2106 instance
```
`K` is read only through `loop2_far_le` and `far3:939`, and both are replaced by (HK). The first estimate does not read `K`.
```
$ sed -n 38,44p RBM3D/Defs/Block.lean   (sbKernel: x=0 ↦ (1+2d g²)⁻¹; |x|=1 ↦ g²(1+2d g²)⁻¹; else 0)  →  SB d L 0 = 1
$ sed -n 327p RBM3D/BA/FlowPins.lean      S := fun n => 1          (H3 dischargeable at BA, lemma owed)
$ sed -n 264,266p RBM3D/BA/FlowPins.lean  BALloop … := loopFine … (sz.seqHflowBA lam0 n t ω) (ztOf (BAmF …) (E n) t) σ a
$ sed -n 158,160p RBM3D/Loop/GLoopFlow.lean  Lloop … := loopFine … (seqHflow sz n t ω) (zt E t) σ a      (H1: rfl at both)
$ grep -n "def etaOf\|def ztOf" RBM3D/Loop/GLoopFlow.lean
55:def ztOf (m : ℂ) (E t : ℝ) : ℂ := E + (1 - t) * m
58:def etaOf (m : ℂ) (t : ℝ) : ℝ := (1 - t) * m.im
$ (public?) seqHflowBA Hermitian lemmas: FlowPins:925, Step1Trivial:103, ConArg:310, Step1Setup:239, Step1Boot:444,
  GreenSchur:202 — all `private theorem`   → "public form owed by the BA twin" is accurate
$ sed -n 173,180p RBM3D/BA/FlowPins.lean  BAProp5: BAReal … → ∀ σ₁ σ₂ a, ‖BATheta … t σ₁ σ₂ 0 a‖ ≤ C·Bparam·exp(-c|a|/ellT L g t)
$ sed -n 32,33p RBM3D/Defs/Params.lean    ellT L g t := min (max (g / √|1-t|) 1) L      (nondecreasing in g)
```
Row 11 is now C1-clean: `BAProp5` covers mixed `σ₁ ≠ σ₂` under `BAReal` (no `‖m‖=1`), and `baTheta_weighted_l1` is
same-sign only, so the change of source is correct. `g₀ = √t₀ g ≤ g` with `ellT` monotone gives decay beyond `ℓ*(g)`. The route
matches the paper (`7_8_light_weight.tex:2002`: "combine (Kn2sol), (Mbound_AO) and (prop:ThfadC) to obtain
(eq:kn2sol_decay)"). `hk2.py` is a valid limit check: both split terms are eventually below `W^{-(D+d)}` for every fixed rate,
because `(log W)^{3/2}` beats `log N ≤ log W/𝔠`.

Near case (`EMn2Exp1:1206-1300`): `STInitialGT2.1` is only weakened (`ST_prec_mono_eventually`) and passed to
`stEMn2Poly_holds`, so `C.GM` needs no link to `Hf`; the H1 relation `C.L = loopFine Hf ζf` is enough. Target 1's proof
(`EMn2Poly:838-947`) reads only `hflow.1` (size data), `etaT_pos`, `seqHflow_isHermitian`, `etaT_eq_zt_im`, and
`emn2_ee_le … (sz.lam n) hH hz'`, which are exactly H1, H3 and H4.

## 3. Statements (ii) against the frozen pins (`Chain/Step2Gen.lean:471`, `:483`)
- T1 `stEMn2PolygL_of`: `emn2PolyFacts … → STEMn2PolygL d law Flow mk T0`. The conclusion is the pin verbatim, with no
  `3 ≤ d`, as in the pin. Corollary via `bandFM_STEMn2Poly` (`Iff.rfl`, `:527`). Correct shape.
- T5′ `stEMn2ExpJgL_of`: the `:483` chain up to `∀ D > 0`, then `∀ J ≥ 0, Ĵ ≺ J → … (Bctl^{1/2} + J³) …`. At
  `J := fun n ω => STJhatg (mk sz z) n D (ℓ n) (t n) ω` the conclusion is the `:483` RHS term for term. `Ĵ ≥ 0`
  (quotient by `STprof > 0`) and `StochDomAt.refl` (`Defs/StochDomAt:400`, needs `ζ ≥ 0`) exist, so T2 is a corollary of T5′.
  T5′ is stronger than the paper's `(eq:MG_conclusion3_BA)`: the `J ≥ W^{-d}` hypothesis is dropped and `ω`-dependence is
  allowed. This is proposed as delta `T2404a`.
- The bundles are explicit Prop hypotheses (no structure fields). Each is discharged at the band (`emn2Poly_bandFacts`,
  `emn2Exp_bandFacts`, `emn2Exp2_bandHK`), so the band corollaries are nonvacuous instances. At BA the owed items are the
  public Hermitian lemma, `SB d L 0 = 1`, (B), and the (HK) composition, each named with its owner. None goes through `‖m‖=1`,
  scalar `m`, `mSigma E`, or `withLam 0` vs `sz.lam`. `ekPropTInf_holds` is reused at the real `sz.lam`, as `STprof` (frozen) does.
- Name clash: none of the 13 proposed names occurs in `RBM3D/` or `docs/tickets/checks/` (grep, 0 files each).

## 4. The three "decisions requested of the dispatcher" (line 169): resolved by the ticket, no sign-off needed
```
$ grep -n "emn2Exp_near\|emn2Exp_far12\|emn2Exp_far3\|emn2Exp_of_far3" docs/tickets/checks/T2404-check.lean
#check @RBM.Gauss.Sizes.emn2Exp_near  …far12  …far3  …of_far3        (4 lines)
$ python3 -I cone.py      # import graph of RBM3D/ (root RBM3D.lean excluded)
EMn2Poly reverse cone 15 | FlowPins closure 66 | intersection []
EMn2Exp1 reverse cone 7 | FlowPins closure 66 | intersection []
EMn2Exp2 reverse cone 6 | FlowPins closure 66 | intersection []
EMn2* in FlowPins closure: []
LWExpCert in FlowPins closure: []
FlowPins closure already in EMn2Exp2 closure: 59 of 67
$ sed -n 38p docs/reports/T2379-design.md
| g, `git diff --no-index --numstat` (pilot B5 primary) | 136 added, 99 removed, of 568: **0.239** |
```
1. The four intermediates: the ticket's acceptance criteria require the check file to compile on the branch, and it
   `#check`s all four names. So they stay, and the plan keeps them. Their cost is already in the central `A = 763`.
2. The `BA.FlowPins` import in `EMn2Exp2`: item 8 requires the example at `baFMz sz0 zSeq` (`FlowPins:393`), so the import
   follows from the ticket. It creates no cycle (empty intersections), stays out of the certificate lane, and adds 8 modules
   to the closure.
3. Stop-line reading: the design's edit measure is numstat *added* lines (pilot `136 added` → `g = 0.239`). The central
   prediction is below 1,000 under every reading: added 763, A+R 962, net 564. **No binding stop line is hit by the
   prediction.**

## 5. Verdict
**PASS** (stage-1a design gate, round 2). Every design-gate deliverable (i)-(iv) and the I1 answer (5′ adopted, ≈40 ≤ 80
lines) is present and checked above. The numerics reproduce. No binding stop line is predicted to be hit, and no item needs
dispatcher sign-off.

Observations (no effect on the verdict):
- The A+R reading's ±25% upper end (1,202) exceeds 1,000. Stage 1b should follow (a′-iv): report `git diff --numstat`
  after `EMn2Poly` and after `EMn2Exp1`, and stop with the T2a/T2b split if the running total projects above 1,000.
- H12 omits four `sz`-only arithmetic lemmas read by `EMn2Exp1` (`ST_Wpow_le_size`, `ST_rpow_neg_half`, `ST_rpow_sq`,
  `ST_size_rpow_neg_le`). They are model-free and reused unchanged, so no statement is affected.
- `emn2ExpHK` (public def in `EMn2Exp2`) uses the stem `emn2Exp`, not `emn2Exp2_`. This follows existing practice
  (`emn2Exp_far3` lives in `EMn2Exp2`). Rule (E) needs only the prefix.
- Place the band-carrier instance of target 1 (`stEMn2Poly_holds` as its corollary) in `EMn2Poly`. Only the BA-carrier
  examples need `EMn2Exp2` (the FlowPins import). The stage-2 auditor checks "instance in the same file".
- The dispatcher should record `T2404a` (5′ `J`-form: no `J ≥ W^{-d}`, `J` may be random) in `docs/paper-deltas.md`.
