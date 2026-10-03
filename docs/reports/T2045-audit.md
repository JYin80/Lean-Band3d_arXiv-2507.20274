Auditor model: claude-opus-5-5
# T2045 audit (round 1) — S1-08 ScaleFacts / PerTimeCalc — Sat Oct  3 13:02:11 UTC 2026

Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2045-audit1` (detached at `60dac4a`, tip of `t/T2045`).
Ticket pins no statement text (check file has `#check` lines only); statements are judged against RBM2D
`c9a24cf` (ST1-COMMON item 6) and against this paper (`1_2:1108`, `1_2:1121`, `1_2:1296`, `(eq:WO)` `1_2:363`).

## 1. Scope, hygiene, build, axioms
```
$ git diff --name-status main...t/T2045
A	RBM3D/Induction/PerTimeCalc.lean
A	RBM3D/Induction/ScaleFacts.lean
$ grep -nE '\b(sorry|admit|native_decide)\b|^[[:space:]]*axiom ' RBM3D/Induction/{ScaleFacts,PerTimeCalc}.lean
grep exit 1
$ lake build RBM3D.Induction.PerTimeCalc RBM3D.Induction.ScaleFacts 2>&1 | grep -E "error|warning|Build|sorry"
Build completed successfully (3314 jobs).
$ lake build RBM3D | grep -E "error|Build"
Build completed successfully (3743 jobs).
$ lake env lean precheck.lean   # import RBM3D, both new modules, #assert_rbm_axioms
axiom audit: 1560 theorems, 549 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
All within [propext, Classical.choice, Quot.sound] ...      # exit 0
$ lake env lean ax.lean   # #print axioms; std3 = [propext, Classical.choice, Quot.sound]
'RBM.Ind.scaleFacts_R1' depends on axioms: [std3]
'RBM.Ind.scaleFacts_R2_pt' depends on axioms: [std3]
'RBM.Ind.scaleFacts_R2' depends on axioms: [std3]
'RBM.Ind.scaleFacts_ellT_ratio' depends on axioms: [std3]
'RBM.Ind.scaleFacts_ellT_pow_four' depends on axioms: [std3]
'RBM.Ind.PerTimeCalc.Unif.forbidden_region' depends on axioms: [std3]
'RBM.Ind.PerTimeCalc.stepOneBootstrap' depends on axioms: [std3]
'RBM.Gauss.Sizes.STBctl_mono' / 'STBctl_xmono' / 'STBctl_ge' depend on axioms: [std3]
'RBM.Ind.closure_scale' / 'RBM.Ind.closure_sq_le' depend on axioms: [std3]
'RBM.Ind.ScaleFactsInst.{R1_sz0,R1_sz0_lt_one,R2_sz0,R2_pt_sz0,ratio_sz0,forbidden_region_Bctl_sz0}': [std3]
'RBM.Ind.PerTimeCalcInst.{forbidden_region_sz0,stepOneBootstrap_sz0}': [std3]
'RBM.Ind.ScaleFactsNeg.scaleFacts_R1_needs_WO' depends on axioms: [std3]
```
(The three lines with `/` and `{…}` group identical one-line outputs.) `RBM3D/Test/Axioms.lean` untouched; no frozen signature touched (both files new).

## 2. Statements (script `stm.py`: RBM2D `c9a24cf:RBM2D/Induction/ScaleFacts.lean` vs RBM3D)
```
## scaleFacts_R1
 2D: (κ c τ : ℝ) (E t : ℕ → ℝ) (hE : ∀ n, |E n| ≤ 2 - κ) (hκ : 0 < κ) (hc : 0 < c) (hτ : 0 < τ) (hB : Bandwidth d c) (hR : RangeCond d τ t) : ∀ᶠ n : ℕ in atTop, ∀ u : ℝ, u ≤ t n → (spectralM (E n)).im * ((d.size n : ℕ) : ℝ) ^ (min (2 * c) τ) ≤ scaleM (d.L n) (d.W n) (E n) u
 3D: (𝔠 𝔡 τ : ℝ) (t : ℕ → ℝ) (h𝔡 : 0 < 𝔡) (hB : sz.Bandwidth 𝔠) (hWO : sz.WO 𝔡) (hR : ∀ᶠ n : ℕ in atTop, ((sz.size n : ℕ) : ℝ) ^ (-1 + τ) ≤ 1 - t n) : ∀ᶠ n : ℕ in atTop, ∀ u : ℝ, u ≤ t n → sz.Bctl n u ≤ 2 * ((sz.size n : ℕ) : ℝ) ^ (-(min (2 * 𝔠 * 𝔡) τ))
## scaleFacts_R2_pt
 2D: {L W : ℕ} {E s u t : ℝ} (hL : 1 ≤ L) (hW : 1 ≤ W) (hE : |E| < 2) (hsu : s ≤ u) (hut : u ≤ t) (ht : t < 1) (hstep : (scaleM L W E s)⁻¹ ≤ ((1 - t) / (1 - s)) ^ 30) : scaleM L W E s ^ ((29 : ℝ) / 30) ≤ scaleM L W E u
 3D: (n : ℕ) {c s u t : ℝ} (hc : 0 < c) (hsu : s ≤ u) (hut : u ≤ t) (ht : t < 1) (hstep : (sz.Bctl n t) ^ c ≤ (1 - t) / (1 - s)) : sz.Bctl n u ≤ (sz.Bctl n s) ^ (1 - c)
## scaleFacts_R2
 2D: (κ τ : ℝ) (E s t : ℕ → ℝ) (hE : ∀ n, |E n| ≤ 2 - κ) (hκ : 0 < κ) (hC : CondStInd d E s t) (hR : RangeCond d τ t) : ∀ᶠ n : ℕ in atTop, ∀ u : ℝ, s n ≤ u → u ≤ t n → scaleM (d.L n) (d.W n) (E n) (s n) ^ ((29 : ℝ) / 30) ≤ scaleM (d.L n) (d.W n) (E n) u
 3D: {𝔠d : ℝ} (h𝔠d : 0 < 𝔠d) {s t : ℕ → ℝ} (hC : sz.STConStInd 𝔠d s t) (ht : ∀ᶠ n : ℕ in atTop, t n < 1) : ∀ᶠ n : ℕ in atTop, ∀ u : ℝ, s n ≤ u → u ≤ t n → sz.Bctl n u ≤ (sz.Bctl n (s n)) ^ (1 - 𝔠d)
## scaleFacts_ellT_ratio
 2D: {L : ℕ} {s u t : ℝ} (hL : 1 ≤ L) (hs0 : 0 ≤ s) (hsu : s ≤ u) (hut : u ≤ t) (ht : t < 1) : ellT L u / ellT L s ≤ ((1 - s) / (1 - t)) ^ ((1 : ℝ) / 2)
 3D: {L : ℕ} {g s u t : ℝ} (hL : 1 ≤ L) (hsu : s ≤ u) (hut : u ≤ t) (ht : t < 1) : ellT L g u / ellT L g s ≤ ((1 - s) / (1 - t)) ^ ((1 : ℝ) / 2)
## scaleFacts_ellT_pow_four
 2D: {L : ℕ} {E s t : ℝ} (hL : 1 ≤ L) (hE : |E| < 2) (hs0 : 0 ≤ s) (hst : s ≤ t) (ht : t < 1) : (ellT L t / ellT L s) ^ 4 ≤ (etaT E s / etaT E t) ^ 2
 3D: {L : ℕ} {g E s t : ℝ} (hL : 1 ≤ L) (hE : |E| < 2) (hst : s ≤ t) (ht : t < 1) : (ellT L g t / ellT L g s) ^ 4 ≤ (etaT E s / etaT E t) ^ 2
```
Merged definitions used (read in the worktree): `Bctl n t = (W^d)⁻¹ * Bparam d L lam t 0` (Sizes.lean:214),
`Bparam = (g²+|1-t|)⁻¹((K+1)^{d-2})⁻¹ + (L^d|1-t|)⁻¹` (Params.lean:36), `ellT L g t = min (max (g/√|1-t|) 1) L`
(Params.lean:32), `WO 𝔡 = ∀ᶠ n, W^{-d/2+𝔡} ≤ lam ∧ lam ≤ 𝔡⁻¹` (Sizes.lean:164), `STConStInd 𝔠d s t =
∀ᶠ n, Bctl n (t n)^𝔠d ≤ (1-t n)/(1-s n) ∧ (1-t n)/(1-s n) < 1` (Induction/Defs.lean:168) = `(con_st_ind)` `1_2:1296` verbatim.

Assessment (ScaleFacts is class c; the ticket mandates restating with `Bctl`/`ellT L g`/`etaT`):
- R1: conclusion on `a_u = W^{-d}B_{u,0}` (role of RBM2D `M_u⁻¹·Im m`); exponent `min(2𝔠𝔡, τ)` follows from
  `a_u ≤ (lam²W^d)⁻¹ + (N x_u)⁻¹ ≤ W^{-2𝔡} + N^{-τ}`. Added hypothesis `sz.WO 𝔡` is the paper's standing `(eq:WO)`
  (`1_2:363`), not a new assumption; `scaleFacts_R1_needs_WO` compiles a counterexample without it. Parameters
  before `∀ᶠ n`. Faithful d-dimensional restatement.
- R2_pt / R2: hypothesis is `(con_st_ind)` of this paper at time `t` (not RBM2D's `M_s` form); `c = 𝔠_d`,
  conclusion `a_u ≤ a_s^{1-c}` = RBM2D's `M_s^{29/30} ≤ M_u` at `c = 1/30`. No hidden hypothesis.
- ratio facts: exponents `1/2`, `4`, `2` unchanged; `g` added (merged `ellT`), `0 ≤ s` dropped (weaker hypotheses).
- `forbidden_region`, `stepOneBootstrap`: copied verbatim, see below; dimension-free.
```
$ diff <(sed -n 67,849p ptc2d.lean | sed 's/RBM2D/RBM3D/g') <(sed -n 49,831p RBM3D/Induction/PerTimeCalc.lean)
758,759c758,759
< renamed `stepOneBootstrap` (T2006 (b.7) rule 3).  It is a statement about events only, so there
< is no per-time / uniform split. -/
---
> renamed `stepOneBootstrap`.  It is a statement about events only, so there is no per-time /
> uniform split. -/
```
Vocabulary: RBM2D `Path/PerTime.lean:40,48` (`TimeIcc`, `PerTimeDomAt`) and RBM3D `Defs/StochDomAt.lean:100,105`
have identical bodies (read); `StochDomAt`, `HighProbAt` (StochDomAt.lean:61,82) are the merged size-indexed predicates.
- Probe 4.1 facts (statement text, whitespace-normalised, vs `752e027:RBM3D/Probe/T2015Pins.lean`):
```
STsize_pos / STBctl_pos / STBctl_mono / STBctl_xmono / STBctl_ge / closure_scale / closure_sq_le:
  statement identical to probe 752e027: True   (7 of 7)
```
Hidden hypotheses / cycles: `Sizes` fields are only `3 ≤ L n`, `0 < W n`; all other hypotheses are in the
signatures. Imports: ScaleFacts -> {Induction.Defs, Induction.PerTimeCalc}; PerTimeCalc -> {Defs.StochDomAt, Mathlib};
no cycle, no import of `RBM3D`, all dependencies merged. No external hypothesis is used.

## 3. Compiled nonempty instances (in the same files; built above)
| endpoint | instance | data (deterministic hypotheses discharged) |
|---|---|---|
| scaleFacts_R1 | `ScaleFactsInst.R1_sz0`, `R1_sz0_lt_one` | `sz0` (d=3), 𝔠=1/6, 𝔡=1/10, τ=1/10, t≡1/16; `sz0_bandwidth`, `sz0_WO`, range proved; bound `< 1` eventually (not trivial) |
| scaleFacts_R2 | `R2_sz0` | s≡0, t≡1/16, 𝔠_d=1/100, `conStInd_inst` (merged), `t<1` proved |
| scaleFacts_R2_pt | `R2_pt_sz0` | s=0<u=1/32<t=1/16, c=1/100, hstep from `conStInd_inst` at an eventual `n` |
| ellT_ratio, ellT_pow_four | `ratio_sz0`, `ratio_sz0_sharp` | L=4, g=1/64, 1-s=10⁻⁴, 1-t=(4·10⁴)⁻¹, E=1/2; both sides =2 (sharp) |
| forbidden_region | `PerTimeCalcInst.forbidden_region_sz0`, `ScaleFactsInst.forbidden_region_Bctl_sz0` | `seqP sz0`, window [0,1/16], non-constant `obs`, ε=1/4 (resp. actual scale a=(W⁻³B_{0,0})^{1/4}, ε=1/480) |
| stepOneBootstrap | `PerTimeCalcInst.stepOneBootstrap_sz0` | M(u)=u·obs, a≡1, b≡2, window [0,1/16]; continuity, a≤b, forbidden, init proved |
| probe 4.1 | `Bctl_facts_sz0`, `closure_sz0` | n=0: W=32, L=4, lam=1/64; s=0≤u=1/2; c=1/100 |
```
$ lake env lean ax.lean | grep -A2 '#check'   # merged facts used by the instances
@Gauss.InductionDefsInst.conStInd_inst : ∀ {𝔠d : ℝ}, 0 < 𝔠d → Gauss.SizesInst.sz0.STConStInd 𝔠d Gauss.InductionDefsInst.sInst Gauss.InductionDefsInst.tInst
Gauss.SizesInst.sz0_WO : Gauss.SizesInst.sz0.WO (1 / 10)
Gauss.SizesInst.sz0_bandwidth : Gauss.SizesInst.sz0.Bandwidth (1 / 6)
```
No `N = 0`, empty window, `False` premise or astronomically large witness. The stochastic premises of the
PerTimeCalc instances hold sample-wise (observation, as the prove report says; allowed: they are discharged).

## 4. Paper deltas
Differences of Lean statements from this paper / RBM2D: R1 on `W^{-d}B` with `(eq:WO)`; ratio facts without
`0 ≤ s`; dropped chain/Step-5 declarations. All proposed: T2045a, T2045b (prove report (d).4). R2 is the paper's
`(con_st_ind)` verbatim: no delta. Coverage complete.

## 5. Scope finding (needs dispatcher sign-off)
The ticket: "Every other public declaration is ported unless the portmap marks it unused". Not ported, and not
marked unused by the portmap: `ChainStepCond`, `chainStepCond`, `scaleFacts_inv_sq_le_tailT`.
```
$ git -C ../RBM2D grep -lw <name> c9a24cf -- RBM2D     # consumers at c9a24cf
ChainStepCond: Induction/Chain.lean Induction/ScaleFacts.lean
chainStepCond: Induction/Chain.lean Induction/MainInd.lean Induction/ScaleFacts.lean
scaleFacts_inv_sq_le_tailT: Induction/ScaleFacts.lean Induction/Step45.lean
```
None of the consumers is an ST-1 file (portmap: Chain/Step45 ST-3, MainInd ST-6), so no S1 ticket downstream
(S1-16, S1-24, S1-32, S1-35, S1-36) loses an input. Their 3D forms would change beyond renaming (2D
`CondStInd` grid with exponent 30; 2D Step-5 objects `tailT`, `ellStar`, `scaleM`), which ST1-COMMON item 6
routes to "stop and report"; the prover reported (prove report (d).1, T2045b). Whether the chain grid and the
Step-5 near-case fact are dropped or deferred to the ST-3/ST-6 chain ticket is a dispatcher decision.

## 6. Observations (no RETURN)
- Prove report (a) row 4 / (a′) wording corrections are internal to the report; no statement affected.

## Verdict
| target | verdict |
|---|---|
| scaleFacts_R1 | PASS |
| scaleFacts_R2_pt, scaleFacts_R2 | PASS |
| scaleFacts_ellT_ratio, scaleFacts_ellT_pow_four | PASS |
| PerTimeCalc.Unif.forbidden_region | PASS |
| PerTimeCalc.stepOneBootstrap | PASS |
| probe 4.1 (STsize_pos, STBctl_{pos,mono,xmono,ge}, closure_scale, closure_sq_le) | PASS |

Overall: **PASS — needs dispatcher sign-off** on the scope deviation of section 5 (three RBM2D public
declarations not ported although the portmap does not mark them unused). No repair is required for the
targets; if the dispatcher accepts T2045b, the branch is mergeable as is.
