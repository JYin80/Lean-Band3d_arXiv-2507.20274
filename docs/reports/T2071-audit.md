Auditor model: claude-opus-5-5

# T2071 audit (round 1) — ST2-02 `RBM3D/Induction/Step2Core.lean`
`date -u`: Sat Oct  3 20:23:31 UTC 2026. Worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2071-audit1` (detached at `167e4f0` = `t/T2071`).
Pin: the probe text `git show 0362cbc:RBM3D/Probe/T2039Pins.lean` lines 819–2127 (ticket: "copy verbatim up to the renamings forced by the library").

## 1. Statement: moved block vs pin (script diff)
```
$ git show 0362cbc:RBM3D/Probe/T2039Pins.lean | sed -n 819,2127p > probe.lean
$ git show t/T2071:RBM3D/Induction/Step2Core.lean > core.lean
$ diff probe.lean <(sed -n 35,1301p core.lean) | grep -E '^[<>]' | grep -v '^[<>] *$'   # 65 lines
> namespace RBM.Gauss.Sizes            (x4)       < namespace RBM.Probe.T2039   (x4)
> end RBM.Gauss.Sizes                  (x4)       < end RBM.Probe.T2039         (x4)
> open RBM RBM.Loop RBM.Path                      < open RBM RBM.Loop RBM.Probe.T2039 RBM.Path
>     STBctl_pos sz n (hu_lt j hj)                <     ST2_Bctl_pos sz n (hu_lt j hj)
>     exact STBctl_mono sz n (hu_mono j k hjk) (hu_lt k hk)      < (same with ST2_Bctl_mono)
>     (STBctl_mono sz n (hu_le j hj) ht1).trans hb1              < (same with ST2_Bctl_mono)
>     STBctl_mono sz n (hu_ge k hk) (hu_lt k hk)                 < (same with ST2_Bctl_mono)
>     ... Real.rpow_le_rpow (STBctl_pos sz n hs1).le (hbs k hk)  < (same with ST2_Bctl_pos)
>     ... Real.rpow_nonneg (STBctl_pos sz n hs1).le _))          < (same with ST2_Bctl_pos)
< lines 9-43 of the diff: the whole probe §7 block (doc, namespace, `ST2_Bctl_pos`, `ST2_Bctl_mono`, end)
```
(Columns merged by hand for width; the raw `>`/`<` lines are exactly these.) All differences are proof-term
renamings and namespace brackets; no statement line differs.

Declaration lists (`grep -oE '^(private )?(theorem|lemma|def|abbrev|structure) [^ ]+'`):
```
probe §3–§8: 32 names; core (lines 1–1301): 30 names
probe-only: ST2_Bctl_mono ST2_Bctl_pos          core-only: (none)
```
§7 replacement (ticket item): merged `ScaleFacts.lean`
```
64:theorem STBctl_pos (n : ℕ) {t : ℝ} (ht : t < 1) : 0 < sz.Bctl n t := by
74:theorem STBctl_mono (n : ℕ) {s u : ℝ} (hsu : s ≤ u) (hu : u < 1) : sz.Bctl n s ≤ sz.Bctl n u := by
```
probe: `ST2_Bctl_pos (n : ℕ) {u : ℝ} (hu : u < 1) : 0 < sz.Bctl n u`, `ST2_Bctl_mono` same as merged — identical types up to binder names.

Name resolution after the namespace move (`set_option pp.fullNames true`, `#check @` of all 30, constants found):
```
RBM.Path.gridTime RBM.tailT RBM.tailW RBM.Path.pathH RBM.Gauss.Idx RBM.Path.Path RBM.Path.TimeIcc RBM.Path.pathP
RBM.mE RBM.Path.firstHit RBM.Gauss.HighProbAt RBM.Gauss.Sizes.STNewKLKAt RBM.Gauss.Sizes.STLab RBM.Gauss.Sizes.STGoodAt ...
```
All resolve to merged library constants (no shadowing by a `RBM.Gauss.Sizes.*` homonym).

Quantifiers / windows (`ST_good_engine`, Step2Core.lean:997, statement as in prove report (b)): per-`n`, hypotheses
`K n ≠ 0`, `0 ≤ s n`, `s n ≤ t n`, `t n < 1`, `0 ≤ D`, `0 < Im m(E)`, `|E| ≤ 2-κ`, `0 < lam ≤ 𝔡⁻¹`; no `∀ n` size
condition, no unused `L^d ≤ W^K` — same as the signed probe (DECISIONS §28, §29 items 1–4).

## 2. Vacuity, hidden hypotheses, cycles
- `STGoodAt` (Step2Core.lean:963) is a structure `Prop` with fields `weak, init, lw, mg, mart, rem, ident`; it enters
  `ST_good_engine` as `hg`. It is a ticket target (probe §8, signed design §28), copied verbatim; its fields are
  the paper's good event (E1)–(E5) (`3_5:537–577`), proved w.h.p. by `ST_good_prob` (probe §11, later ST2 ticket).
  No field restates the conclusion (`STstopIdx = K`, the `Ĵ` bound): `mg` contains `Ĵ^3` on the right side, which is
  the bootstrap input, not the output.
- `hNew : STNewKLKAt …` is the pointwise form of the owed pin `STNewKLK` (ST2-07).
- Registry: both Props added to `owedProps` (the only `Test/Axioms.lean` change):
```
$ git diff main...t/T2071 -- RBM3D/Test/Axioms.lean | grep '^+ '
+   `RBM.Gauss.Sizes.STNewKLKAt, -- `lem:newKLK` (`3_5:371-378`) pointwise ... (T2071; class proposed: owed)
+   `RBM.Gauss.Sizes.STGoodAt, -- the pathwise good event (E1)-(E5) ... (T2071; class proposed: owed)
```
- Cycles: Step2Core imports only `RBM3D.Induction.Step2Defs`, `RBM3D.Induction.ScaleFacts` (merged); every used
  lemma is a merged theorem (`transferLaw`, `STBctl_pos/mono`, `prec_of_le`, …) or proved in the file.
- External-hypothesis limit check (TEAM §8 l.14) for `hNew`: prove report (a)(ii): the pin's `C` enters only `hsmall`,
  LHS `≤ c·2^{1/30}W^{-1/10} → 0`; the pin's `δ₀` enters only `STGoodAt.weak`. Accepted.

## 3. Compiled nonempty instances
```
$ grep -c "^example" RBM3D/Induction/Step2Core.lean
28
```
One `example` per theorem (28 theorems; `STLab`/`STGoodAt` are definitions). Endpoint `ST_good_engine` (Step2Core.lean:1726):
`d = 3`, `sz0`, `n = 100` (`L = 404`, `W = 202^5`), `E = 0`, `s ≡ 0`, `t ≡ 1/16`, `K ≡ 16`, `D = 1/2`, `Kf ≡ 1`,
`Λ = C = 1`, `q = κ = 𝔡 = 1/10`, `a₀ = r₀ = q·Bctl(0)^{1/5} > 0`. Discharged in Lean: `hK, hs0, hst, ht1, hD, hmI`
(`mE_zero_im`), `hΛ, hC, ha₀, hr₀, hρ₁, hlam, hlam', hE, hKf0, hKfL, hTmono` (via `ST_tailT_mono_time`), `hb1`
(`Bctl_small`), `hq0, ha, hr, hρ` (equalities), `hsmall` for all `k ≤ 16` (`core_small`, bound 0.85 < 1). Left as
hypotheses: `hNew` (owed pin) and `hg : STGoodAt …` (the w.h.p. event). Nondegenerate: `K = 16` steps, nonempty
window `[0, 1/16]`, positive `a₀`. Other instances: `ST_engine` at `K = τ = 16`, `Δ = 1/256`, one label,
`b = 10^{-30}`; transfer lemmas at `sz0`, `V = Fin 1`, `J_n = range 17`; Grönwall/log lemmas at `K = 4`, `Δ = 1/16`.

## 4. Build and axioms
```
$ lake build RBM3D.Induction.Step2Core 2>&1 | grep -E "error|Step2Core|Build completed"; echo exit
warning: RBM3D/Induction/Step2Core.lean:496:0: `ST_PT_of_sections` does not use the following hypothesis in its type:
Build completed successfully (3719 jobs).
exit: 0
$ lake build RBM3D | grep -E "^error|Build completed"
Build completed successfully (3789 jobs).
$ cat precheck.lean   # import RBM3D; import RBM3D.Induction.Step2Core; #assert_rbm_axioms
$ lake env lean precheck.lean | grep -E "error|axiom audit|premises found"; echo exit
axiom audit: 2475 theorems, 1048 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
premises found by scanning: 82 (borrowed 2, owed 67, structural 13).
exit: 0
$ lake env lean ax.lean     # `#print axioms` of all 30 new names
ST_alpha'_le ST_alpha_bound ST_alpha_mono ST_bootstrap ST_closure_arith ST_cube_le ST_engine ST_firstHit_hit
ST_good_engine ST_gridTime_mem ST_gronwall ST_logstep ST_logsum ST_model_of_whp_grid ST_one_le_prod
ST_pathP_eq_seqP ST_pathwise_ineq ST_prod_le_rpow ST_PT_of_sections ST_rpow_half_add_le ST_rpow_half_mono
ST_sections_of_PT ST_tailT_mono_time ST_tailW_final ST_tailW_L_le ST_tailW_mono_time ST_tailW_scale_step
ST_whp_grid STGoodAt : [propext, Classical.choice, Quot.sound]        (29 lines, each this list)
'RBM.Gauss.Sizes.STLab' does not depend on any axioms
$ grep -cE 'sorry|admit|native_decide|^axiom' RBM3D/Induction/Step2Core.lean
0
$ git diff --stat main...t/T2071
 RBM3D/Induction/Step2Core.lean | 1771 ++++++++++++++++++++++++++++++++++++++++
 RBM3D/Test/Axioms.lean         |    2 +
$ git diff --name-only $(git merge-base main t/T2071) main     # main drift since branch point
RBM3D.lean  RBM3D/Gauss/LoopFlowStein.lean  docs/queue/T2064.state  docs/reports/T2064-*.md
```
Only the two sole writable files; the `Axioms.lean` change is the two registry lines; no frozen signature touched;
main's drift does not touch either file. Name clashes: `git grep` on `main` (excluding `Probe/`) of the 30 new names: 0 hits each.

## 5. Paper deltas
The block is the signed probe text (its Lean/paper differences are T2039a–j, DECISIONS §28). No statement is changed,
so no new Lean/paper difference arises. Proposed candidates: T2071a (namespace of probe §3–§7 now `RBM.Gauss.Sizes`),
T2071b (`ST2_Bctl_*` → `STBctl_*` for later moves of probe §9–§12), T2071c (`hsmall`'s `b^{1/30}` forces `W^3 ≳ 2·10^{23}`,
instance at `n = 100`). Coverage complete.

## Verdicts
| target | verdict |
|---|---|
| §3 `ST_one_le_prod`, `ST_gronwall`, `ST_bootstrap`, `ST_logstep`, `ST_logsum`, `ST_prod_le_rpow`, `ST_pathwise_ineq`, `ST_alpha_mono` | PASS |
| §4 `ST_tailT_mono_time`, `ST_tailW_mono_time`, `ST_tailW_scale_step`, `ST_tailW_L_le`, `ST_tailW_final` | PASS |
| §5 `ST_gridTime_mem`, `ST_pathP_eq_seqP`, `ST_whp_grid`, `ST_model_of_whp_grid`, `ST_PT_of_sections`, `ST_sections_of_PT` | PASS |
| §6 `ST_rpow_half_mono`, `ST_rpow_half_add_le`, `ST_cube_le`, `ST_engine`, `ST_alpha_bound`, `ST_alpha'_le`, `ST_closure_arith` | PASS |
| §7 (dropped; merged `STBctl_pos`, `STBctl_mono` used) | PASS |
| §8 `STLab`, `STGoodAt`, `ST_firstHit_hit`, `ST_good_engine` | PASS |

**Overall: PASS.**

## Observations (no statement, instance, build, axiom or delta-coverage change)
- O1. Registry class of `STNewKLKAt`, `STGoodAt` is `owed` as proposed by the prover (the ticket expected no new
  hypothesis Prop; §28's registry list predates `ST_good_engine`). `owed` is the conservative class; the dispatcher may
  reclassify `STGoodAt` (e.g. structural) when ST2-03/04 prove `ST_good_prob`.
- O2. The endpoint instance passes `Mart = Rem ≡ 0` into `hg : STGoodAt …`, so its `ident` field there asks for an exact
  drift-only identity along the path. `hg` is a non-deterministic premise allowed to stay a hypothesis, and this is not
  shown to be `False`, but the later `ST_good_prob` instance should use the actual martingale/remainder.
- O3. Unused-hypothesis linter warning on `ST_PT_of_sections` (probe text, unchanged), as the prove report says.
