Auditor model: claude-opus-5-5

# T2191 audit (round 1) — ST-D5 Step 6 design probe, branch `t/T2191` @ `96c6b4c`

Written Mon Oct  5 17:35:20 UTC 2026 (`date -u`). Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2191-audit1` (detached at `96c6b4c`). Report-only ticket; probe `RBM3D/Probe/T2191Pins.lean` stays on the branch.

## 1. Build, axioms, hygiene, scope (script output)
```
$ lake build RBM3D.Probe.T2191Pins 2>&1 | grep -E "error|warning: RBM3D/Probe|T2191Pins|Build completed"; echo exit $?
✔ [3845/3845] Built RBM3D.Probe.T2191Pins (8.2s)
Build completed successfully (3845 jobs).
exit 0
$ lake env lean RBM3D/Probe/T2191Pins.lean; echo exit $?      # output lines: 0
exit 0
$ grep -nE "sorry|admit|native_decide|^axiom|^\s+axiom" RBM3D/Probe/T2191Pins.lean | wc -l
0
$ # generated file: `#print axioms` for every `theorem` of the probe (namespace-qualified), run with lake env lean
#print lines 142; lines "depends on axioms: [propext, Classical.choice, Quot.sound]": 142; other lines: 0
$ git diff --stat main...t/T2191
 RBM3D/Probe/T2191Pins.lean | 2348 ++++++++++++++++++++++++++++++++++++++++++++
 1 file changed, 2348 insertions(+)
$ # every def/theorem name of the probe, `git grep -lwF <name> main -- RBM3D`
191 public names; clashes on main: []
```
Only a sole writable file is touched; no merged signature changes (no merged file in the diff).

## 2. Statements against the paper

**Target `STExp2U` (`(Eq:Gtlp_exp_flow)`, `1_2:1390-1396`).** Script diff against the merged `STExp2` (`Induction/Defs.lean:159-165`):
```
$ diff <(sed -n 159,165p RBM3D/Induction/Defs.lean) <(sed -n 81,87p RBM3D/Probe/T2191Pins.lean)
< def STExp2 (E τ : ℕ → ℝ) : Prop :=
<   Prec sz (U := fun n => (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)))
<     (fun n p _ => ‖(∫ ω, Lloop sz n (E n) (τ n) p.1 p.2 ω ∂(sz.seqP)) -
<         STKloop sz n (E n) (τ n) p.1 p.2‖)
<     (fun n _ _ => (sz.Bctl n (τ n)) ^ 2 *
<         ((sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d) ^ (-(1 / 5 : ℝ)) + sz.Bctl n (τ n)))
> def STExp2U (E s t : ℕ → ℝ) : Prop :=
>   Prec sz (U := fun n => TimeIcc s t n × (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)))
>     (fun n p _ => ‖(∫ ω, Lloop sz n (E n) (p.1 : ℝ) p.2.1 p.2.2 ω ∂(sz.seqP)) -
>         STKloop sz n (E n) (p.1 : ℝ) p.2.1 p.2.2‖)
>     (fun n p _ => (sz.Bctl n (p.1 : ℝ)) ^ 2 *
>         ((sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d) ^ (-(1 / 5 : ℝ)) + sz.Bctl n (p.1 : ℝ)))
$ sed -n 1392,1394p paper/tex/1_2_Intro_model_result.tex
 \max_{\bsig, \ba}\left|\E{\cal L}^{(2)}_{u, \bsig, \ba}-{\cal K}^{(2)}_{u, \bsig, \ba}\right|\prec \p{W^{-d}B_{u,0}}^2 \p{(\ilambda^2W^d)^{-1/5}+W^{-d}B_{u,0}},\quad
 \forall u \in [s, t] .
```
The only change is `τ n ↦ u ∈ [s_n,t_n]` inside the index set (`TimeIcc`, `Defs/StochDomAt.lean:100`), i.e. the paper's "uniformly in `u ∈ [s,t]`" (`1_2:1400`); `|𝔼𝓛 − 𝒦|`, `max_{σ,a}`, the target and the scale `N` are those of the paper. Endpoint `STExp2_of_STExp2U` (`u = t`, `1_2:1396`). **PASS.**

**Shape `STIngR6` / `STStep6R d R` (R = `STReg5I..IV`, `STAny`).** Premise sets by script against the merged `STIngR5` (`Step5Pins.lean:82`):
```
STIngR5 only: ['Cd', 'STDecayStrong', 'STKbound', 'STKward', 'STStep1Loop', 'STStep2Concl']
STIngR6 only: ['STExp2', 'STGdecayW', 'STStep2Core']
common: ['STConStInd', 'STDecay', 'STFlow', 'STLK', 'STLKU', 'STLmaxU']
```
Constants first (`κ ε 𝔡`, then `∃ 𝔠_d ∈ (0,10^{-2}]`, then `𝔠, sz, z`), as `1_2:1294` ("`𝔠_d` depending on `d, κ, ε, 𝔡`"); `0 ≤ s < t ≤ lemT z`; `(d)` at `s` (`STExp2`, `(Eq:Gtlp_exp+IND)` `1_2:1281`); `(con_st_ind)`; Step 2 loss-free part, Steps 3, 4 and Step 5 `(Eq:Gdecay_flow)` on `[s,t]`. Dropping `STKbound`/`STKward` (theorems `stKbound_of_flow`/`stKward_of_flow`), `STDecayStrong`, `STStep1Loop` and the lossy third conjunct of `STStep2Concl` strengthens the pin (fewer premises). I checked `6:1-152`: Step 6 cites `(Eq:Gtlp_exp+IND)`, `(Eq:Gdecay_flow)`, `(Eq:L-KGt-flow)`, `(Gt_avgbound_flow)`, `(eq:bcal_k)`, `lem:LWterm_EXP` (whose premises are `(Gt_bound_flow)`–`(Eq:Gdecay_flow)`, `6:84`), and never `(Eq:Gdecay+s<g_flow)`, `(lRB1)` or `(Eq:Gdecay_w)`. Recorded as T2191b. Regime predicates are the merged `STReg5*` = `6:94, 97` (`1-s ≥ 1-t ≥ g²`; `g²/L² ≤ 1-t ≤ 1-s ≤ g²`; `g²/L^d ≤ 1-t ≤ 1-s ≤ g²/L²`; `1-t ≤ 1-s ≤ g²/L^d`). **PASS** for `STStep6I..IV`, `STStep6`.

**Ingredient pins (item 2 (b)–(g)), each read against the paper line it cites:**
- `STImproveExpAver`/`STExpAvgAt` (`6:12-17`): `max_a |𝔼 tr((G_u−M)E_a)| ≺ (W^{-d}B_{u,0})²`, both charges (`Bool`), premises `(Gt_avgbound_flow)` (`LWAvgLaw`) and `(Eq:L-KGt-flow)` (`STLK`) at `u`; per time (paper: uniform in `[s,t]`) — T2191c; uniform form `STExpAvgU` compiled via (g) `st6_precU_of_forall_seq`. PASS.
- `STExpHier`, `STExpDuhamelZ` (`(Eexpint_K-L)` `6:3-7`; `A = {1,2}`: `(iisuwjyys_exp)` `6:142-146`, `Q^{(A)}∘𝒰`), `STExpDuhamelQ` (`(int_K-L+QE)` `6:109-116`, commutator `[𝒬_u,Θ]f_u` and `−(𝒫f_u)∂_uϑ_u` with the printed sign `6:115`): initial term from `s`, deterministic at fixed `n`. Drift = `𝔼STELKLK + 𝔼STEGt` (merged objects, `STEGt = LWE` bridge compiled). PASS.
- `STExpLKLKHi` (`(eq:Exp(L-K)1)` `6:58-62`, window `g²/L^d ≤ 1-t`, bound `(1-u)^{-1}Bc_u^{11/5}`), `STExpEGtHiConcl` (`(eq:ExpLWn=2)` `6:85-87`, `5/2`, from per-time `LWtermEXP` by (g) + the five bridges), `STExpDriftLo` (`(eq:Exp(L-K)2)`, `(eq:ExpLWn=2_smalleta)` `6:63-77`, `(1-u)^{-1}(N(1-u))^{-3}`, regime (iv)). Exponents and windows match. PASS.
- `STExpWardI` (`(eq:EPL-K)` `Bc³`, `(eq:boundELKQ1)`, `(eq:boundcommutator)` `(1-u)^{-1}Bc³`, `σ₁ ≠ σ₂`), `STExpWardII` (`6:138-141`: `‖f − Q^{({1,2})}f‖ ≺ Bc³`, `σ₁ ≠ σ₂`): uniform in `u` (paper: at `t`) — T2191d. PASS.
- `STExpIntI..IV`, `STExpIniI`: conditional integrated estimates (design objects, no paper counterpart beyond `6:94-147`); regime (ii) `σ₁ = σ₂` uses `(sum_res_Ndecay_nonzero)` at `A = ∅`, not `(sum_res_2_NAL)`. F1 checked against the paper:
```
$ sed -n 1637p paper/tex/3_5_Loop_Hierarchy.tex      # lem:sum_decay window
	Fix any $0\le s \le t \le 1 -\ilambda^2/L^{2}$ such that $(1-t)/(1-s)\ge W^{-1}$.
$ sed -n 1667p paper/tex/3_5_Loop_Hierarchy.tex | cut -c1-80   # lem:sum_decay_nonzero window
Fix any $1-\ilambda^2/L^{2}\le s \le t<1$ and $\bsig\in \{+,-\}^n$. Let ${\cal A
```
With regime (ii) `1-t < 1-s ≤ g²/L²`, `t ≤ 1-g²/L²` forces `t ≤ s` (compiled `st6_F1_window_vs_reg5II`, instance `inst_F1`). The finding is correct; T2191a covers it. PASS.

**`0 < lam n` (item 2 (6)).** `st6_lam_pos : sz.WO 𝔡 → ∀ᶠ n, 0 < sz.lam n` compiles; `st6_target_lam_zero` shows the `lam n = 0` fall-back. No defect in the merged `STExp2`. PASS.

**Target 5(b) `ST_mainInd_of_steps : STStep1 d → … → STStep6 d → STMainInd d`.** Compiles with no merged signature changed. `𝔠_d` is the min of the five step constants, and `(con_st_ind)` passes by `st5_conStInd_mono`. `STKbound`/`STKward` come from the flow theorems, the endpoints from merged/probe lemmas, and `STStep1 = stStep1_holds` in `inst_assembly6`. The mismatches are reported, not patched (report (b) 9). PASS.

**Target 5(a) skeletons.** `ST_step6_case{I,II,III,IV}_of_pins` compile from their ingredient pins (PASS). **`STStep6` (general) from the four regime pins is not compiled.** The probe gives only:
- `ST_step6_compose`: one intermediate time;
- `ST_step6_four_of_regimes`: the fixed stage order (iii),(i),(ii),(iv), each stage nonempty for every `n`;
- `ST_step6_generic_of_regimes : … → STStep6R d STGenericPos`, a **special case**. `STGenericPos` requires every `[s_n,t_n]` to contain all three boundaries `1-g²`, `1-g²/L²`, `1-g²/L^d`.

The prover documents why (report (d) 1, portmap P.8 F-shape). I re-derived the obstruction: `STIngR6` needs `s_n < t_n`, the regime `∀ n` and `(con_st_ind)` with `(1-t)/(1-s) < 1`. For a general `(s,t)` the set of nonempty stages depends on `n`. A stage that is empty at some `n` cannot be fed to a regime pin. Clamped cut points collapse (`s' = t'`), and dummy intervals lack the stochastic premises. So the gluing needs either:
- (A) a transfer of a pin to a subsequence of sizes. `seqP` is `Measure.infinitePi` (`Gauss/FineModel.lean:169`), and no subsequence/`StrictMono` declaration exists in `RBM3D/` (report (b) grep); or
- (B) restated regime pins with the regime inside the index set. This departs from the ticket's mandated `STStep6R d R` shape.

The same gap applies to the merged `STStep5` (S5-29, no proof ticket yet). **BLOCKED** for this sub-target: the missing input is a dispatcher decision between (A) and (B) for S6-13 and S5-29. It cannot be repaired inside the ticket's fixed pin shapes without new infrastructure. **Needs dispatcher sign-off.**

## 3. Vacuity, hidden hypotheses, cycles
- No pin hides a hypothesis in a structure. Every premise is an explicit arrow or `∀` in the signature. `STMollifierProps` is quantified; a mollifier family exists by the merged proved `stMollifierEx_holds` (`st6_mollifier_family`, instance `inst_mollifier_family` at `szB`).
- No cycle. `STStep6*` depend on the ingredient pins and merged theorems only. Premises from other gates: `LWtermEXP` (LW-14), Steps 2–5 conclusions, and `STExp2` at `s` (the induction hypothesis, `1_2:1281`).
- No new external hypothesis. Registry: 20 owed, 21 structural, 0 borrowed (report (d)).

## 4. Compiled nonempty instances (d = 3)
```
$ grep -c "^theorem inst_" RBM3D/Probe/T2191Pins.lean
67
```
- **Regime instances.** `inst_step6I` `(szB,zB,7/8,15/16)`, `inst_step6II` `(szB,zB,15/16,31/32)`, `inst_step6III`/`inst_step6` `(sz0,z0,0,1/16)` and `inst_step6IV` `(szG,zB,5/8,3/4)` apply each pin through `inst_ing6`. Flow (`flow_zB`/`flow_z0`/`flow_zG`), `0 ≤ s < t ≤ lemT`, the regime (`szB_reg5I` …), and `(con_st_ind)` for every `𝔠_d > 0` (`conStInd_const`, `sz0_con`) are discharged. Only stochastic premises remain as hypotheses.
- **Skeletons and assembly.** `inst_skeleton6I..IV`, `inst_assembly6` (with `stStep1_holds`) and `inst_endpoints` are compiled.
- **Gluing.** `inst_compose` and `inst_generic`/`inst_four` are compiled at `(szFour, zB, 0, 49/50)`, with `L = 3` and `g = 4/5`.
- **Nonzero `G` term.** `inst_A_value`: `g²W^d = 8` at `sz0`, `n = 0`, and `inst_G_pos_*` shows `(g²W^d)^{-1/5} > 0`.
- **Regime check.** The regime inequalities hold in exact fractions (report (b) `insts.py`), and no data is degenerate (`L ≥ 3`, `W_n → ∞`, `s < t`, nonempty index sets).

PASS for every compiled endpoint.

## 5. Paper-delta coverage
Each Lean/paper difference found above has a candidate:
- regime (ii) `σ₁=σ₂` kernel lemma: T2191a;
- the `STIngR6` shape: T2191b;
- per-time `lem:improve_exp_aver`: T2191c;
- Ward bounds uniform in `u` and over mollifier families: T2191d;
- `max` inside `Prec`, `lam > 0` eventual: T2191e.

The `(con_st_ind)` limit (see observation 1) is intrinsic to the paper's condition and is not a delta. Covered.

## 6. Observations (no verdict effect)
1. `(con_st_ind)` holds numerically at the mandated I, II and IV data only for `W ≳ 1e10, 1e10, 3e5` at `𝔠_d = 1/100` (report (a) F2). It holds at every `n` for `sz0` (regime (iii)). It is discharged as the merged eventual predicate, as in the merged Step-5 instances.
2. Report (a) line 17 and (b) 11 give `∫x^{-1}dx ≤ 2 log L`, `(d-2) log L` in regimes (i) and (ii). Both are absorbed by `≺`. The ticket's "no `log`" therefore holds only in (iii) and (iv), and the report says so.

## Verdict
| target | verdict |
|---|---|
| 1 inventory, 3 exponent table, 4 route, 6 split (portmap P.1, P.3–P.5) | PASS (report content, script output present) |
| 2 pins `STExp2U`, `STStep6I..IV`, `STStep6`, ingredient pins (b)–(g) | PASS |
| 5(a) per-regime skeletons | PASS |
| 5(a) `STStep6` from the four regimes (general) | **BLOCKED**: only special cases (`STGenericPos`, fixed stage order) compile. Missing input: a dispatcher decision on route (A) subsequence transfer for `Sizes`/`seqP` vs (B) regime-in-index-set restatement of the regime pins, also for S5-29. **Needs dispatcher sign-off.** |
| 5(b) `ST_mainInd_of_steps` | PASS |
| 7 instances | PASS |

Overall: **BLOCKED (needs dispatcher sign-off)** on the general Step-6 gluing only; everything else passes.
