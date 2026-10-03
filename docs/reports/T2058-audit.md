Auditor model: claude-opus-5-5
# T2058 audit (round 1) — S3-23 deterministic scale facts, `RBM3D/Induction/ScaleFacts3.lean`
Branch `t/T2058` at c1ef5fb; audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2058-audit1` (detached). Scratch: `scratchpad/T2058/`.

## 1. Scope, build, axioms, hygiene
```
$ git diff --name-only main...t/T2058
RBM3D/Induction/ScaleFacts3.lean
$ git diff main...t/T2058 -- RBM3D/Test/Axioms.lean RBM3D.lean | wc -l
0
$ head -8 RBM3D/Induction/ScaleFacts3.lean | grep import
import RBM3D.Induction.Step34Pins
import RBM3D.Induction.ScaleFacts
$ lake build RBM3D.Induction.ScaleFacts3 2>&1 | grep -i "error\|ScaleFacts3\|Build completed"; echo exit=$?
Build completed successfully (3706 jobs).
exit=0            # warnings only in other (merged) files; none in ScaleFacts3
$ grep -nE "sorry|admit|native_decide|^\s*axiom " RBM3D/Induction/ScaleFacts3.lean | wc -l
0
$ lake env lean scratchpad/T2058/ax.lean   # #print axioms of all 16 public declarations
'RBM.Gauss.Sizes.st_Bctl_ge'      depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.st_bootRHS_one'  depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.st_iterate'      depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.st_kmin'         depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.st_hscale_I'     depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.st_hscale_II'    depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.st_hscale_I''    depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.st_hscale_II''   depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.st_hBA_I'        depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.st_hBA_II'       depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.scaleFacts3_W_tendsto' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.st_window'       depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.st_EKWin'        depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.st_conStInd_sub' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.st_split_I'      depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.st_split_II'     depends on axioms: [propext, Classical.choice, Quot.sound]
exit=0
$ for n in <public names>; do git grep -n -w -F -- "$n" main -- 'RBM3D/*.lean' RBM3D.lean | wc -l; done
st_kmin=0 st_hscale_I=0 st_hscale_II=0 st_hBA_I=0 st_hBA_II=0 st_window=0 st_EKWin=0 st_conStInd_sub=0
st_split_I=0 st_split_II=0 st_iterate=0 st_Bctl_ge=0 st_bootRHS_one=0 scaleFacts3_W_tendsto=0
```
No new hypothesis `Prop`; `st_kmin` is a `ℕ`-valued def. All other helpers are `private`. `st_Bctl_pos` is not redefined (imported).
Dependencies: merged `Step34Pins`, `ScaleFacts`, `Defs/Sizes` only; no cycle.

## 2. Statements against the ticket
No pinned Lean text in `docs/tickets/checks/T2058-check.lean` for the targets (only `#check`s), so I compare against the ticket's
mathematics and against the downstream pin (probe `st_step3_skeleton` hypotheses `hscale`, `hBA`, `3c58211:RBM3D/Probe/T2041Pins.lean:1099`).
```
$ python3 scratchpad/T2058/shape.py probe.lean ScaleFacts3.lean   # whitespace-normalised conclusion == probe hypothesis with `A n` replaced
st_hscale_I'  MATCHES probe hscale with A n := sz.STAI n : True
st_hscale_II' MATCHES probe hscale with A n := sz.STAII s n : True
st_hBA_I      MATCHES probe hBA with A n := sz.STAI n : True
st_hBA_II     MATCHES probe hBA with A n := sz.STAII s n : True
$ python3 scratchpad/T2058/vd.py probe.lean ScaleFacts3.lean      # item 6, declaration blocks line-for-line
st_Bctl_ge 38 38 IDENTICAL
st_bootRHS_one 5 5 IDENTICAL
st_iterate 14 14 IDENTICAL
```
Merged predicates used (read from main): `STConStInd 𝔠d s t := ∀ᶠ n, Bctl n (t n)^𝔠d ≤ (1-t n)/(1-s n) ∧ (1-t n)/(1-s n) < 1`
(`Induction/Defs.lean:168`); `STCaseI := ∀ n, λ²/L² ≤ 1 - t n`, `STCaseII := ∀ n, 1 - s n ≤ λ²/L²` (`Step34Pins.lean:237,241`);
`STRegIterI := STCaseI ∧ ∀ n, 1 - s n ≤ λ²` (`:493`); `STEKWin` (`:607`); `STPsi A r n k = A^{3/4} + r^{n-1} A^{1-k/8}` (`:76`).

| item | Lean hypotheses (beyond ticket) | assessment | verdict |
|---|---|---|---|
| 1 `st_kmin` | `⌊2 + 8𝔠d((r:ℝ)-1)⌋₊ + 1` | equals ticket formula for `r ≥ 1`; paper `3_5:1431` "k large enough" made explicit | PASS |
| 1 `st_hscale_I`, `'` | `0<𝔠d`, `STRegIterI`, con, `WO 𝔡`, `t<1`, `|E|<2`, `r≥2` | exactly the ticket's list; `'` has the probe's `∀ r, ∃ k, ∃ c` order | PASS |
| 2 `st_hscale_II`, `'` | `0<𝔠d`, con, `t<1`, `|E|<2` — **no `STCaseII`** | strictly more general than the ticket (drops a hypothesis); math: `ρ ≤ (1-s)/(1-t) ≤ B_t^{-𝔠d} ≤ B_s^{-𝔠d} = A^{𝔠d}` and `A ≥ 1` from `B_s ≤ B_t < 1` (con), regime-free. Implies the ticket statement | PASS (obs. O1) |
| 3 `st_hBA_I` | `2 ≤ d`, `STCaseI` (weaker than `STRegIterI`), `WO 𝔡` | `2 ≤ d` used for `L^d ≥ L²`; paper and `STIterR` (`3 ≤ d`) cover it; delta T2058c | PASS |
| 3 `st_hBA_II` | `0<𝔠d`, `𝔠d ≤ 1/4`, con, `t<1`; no range hyp | ticket asked to name the `Bctl ≤ 1` hypothesis: it is derived from con (`B_t^{𝔠d} < 1`). `𝔠d ≤ 1/4` gives `B_s^{1/4-𝔠d} ≤ 1`; `STIterR` fixes `𝔠d ≤ 1/100` (`Step34Pins.lean:481`); delta T2058a | PASS |
| 4 `st_window` | `0<𝔠d`, `d𝔠d<1`, con, `WO 𝔡`, `W → ∞`, `0≤s`, `t<1` | ticket allowed "what else the derivation needs". `W → ∞` is necessary: at `W ≡ 1` the window `1 ≤ (1-t)/(1-s)` contradicts con's `< 1` (prover also compiled a negative, b.5, scratch). `W → ∞` is available from `Admissible` via `scaleFacts3_W_tendsto`; delta T2058b | PASS |
| 4 `st_EKWin` | window hyps + `s ≤ t`, `STCaseI` | all five `STEKWin` fields from hypotheses / `st_window` | PASS |
| 5 `st_conStInd_sub` | `s≤s'`, `s'<t'`, `t'≤t` (∀ n), `t<1` | matches ticket; `t<1` is a standing hypothesis of every consumer | PASS |
| 5 `st_split_I/II` | con, `t<1`, `∀n s<t`; I: `∀n s < u`; II: `∀n u < t`, `u = 1-λ²/L²` | sequences `min(t,u)`, `max(s,u)` as ticket asks; strictness hypotheses are how the empty window is avoided (ticket asked to say how: report (b.6) item 5); delta T2058e | PASS |
| 6 helpers | — | identical to probe text (script above) | PASS |

No structure-field hypotheses: every hypothesis is an explicit argument with a merged definition.

## 3. Compiled nonempty instances (file `ScaleFacts3.lean` §6, lines 551–640; built in §1)
| target | data | hypotheses discharged by |
|---|---|---|
| `st_kmin` | `𝔠d=1/100`, `r=2,3,10,50,100` ↦ `3,3,3,6,10` | `norm_num` |
| `st_hscale_I`, `'` | `szB` (`d=3,L=4,W=n+4,λ=1`), `zB`, `(7/8,15/16)`, `𝔠d=1/100`, `𝔡=1/10` | merged `szB_regIterI`, `szB_WO`, `conStInd_const`, `abs_lemE_lt_two`, `norm_num` |
| `st_hscale_II`, `'` | `szB`, `zB`, `(15/16,31/32)`, `𝔠d=1/100` | `conStInd_const`, `abs_lemE_lt_two`, `norm_num` |
| `st_hBA_I` / `_II` | `szB` at the same two pairs | `d=3`, `szB_regIterI.1`, `szB_WO` / `1/100 ≤ 1/4`, `conStInd_const` |
| `st_window`, `st_EKWin` | `sz0`, `sInst=0`, `tInst=1/16`, `𝔠d=1/100`, `𝔡=1/10` | merged `sz0_con`, `sz0_WO`, `W_tendsto_sz0`, `sz0_admissible`, `sz0_hs0`, `sz0_hst`, `sz0_caseI` |
| `st_conStInd_sub` | `szB`, `[7/8,15/16] → [29/32,59/64]` | `norm_num` |
| `st_split_I/II` | `szB`, `[7/8,31/32]`, `u=15/16` strictly inside | `conStInd_const`, `simp [szB]; norm_num` |
| `st_Bctl_ge`, `st_bootRHS_one`, `st_iterate` | `szB` (`Λ=1`); explicit numbers; `S r k := 2 ≤ r+k` | `tendsto_size`, `simp`, `omega` |

Every deterministic hypothesis is discharged; no `N=0`, empty index, collapsed window or `False` premise; all pairs have `s<t<1`.
Supplementary check (scratch, not committed) that the `szB` instances also go through at `𝔠d = 1/10`, where (con_st_ind) holds
already from `n = 7 / 8` (prove report (a)(ii)), so the instances do not rely on the large threshold of `𝔠d = 1/100` (obs. O2):
```
$ lake env lean scratchpad/T2058/inst10.lean   # st_hscale_I at szB,(7/8,15/16),𝔠d=1/10 ; st_hBA_II at szB,(15/16,31/32),𝔠d=1/10
exit=0
```

## 4. Paper-delta coverage
Report (d) proposes T2058a (`hBA` (ii): `𝔠d ≤ 1/4`, `Bctl < 1` from con), T2058b (window: `d𝔠d<1`, `(eq:WO)`, `W → ∞`),
T2058c (`hBA` (i): `2 ≤ d`), T2058d (explicit `k_min` and constants), T2058e (split with strict `s<u`, `u<t`).
These cover every Lean/paper difference that adds a hypothesis or fixes a choice the paper leaves open. The remaining differences
weaken hypotheses (O1) and need no delta.

## 5. Observations (no effect on statement, instance, build, axioms or delta coverage)
- O1. `st_hscale_II(')` omits the ticket's `STCaseII` hypothesis and `st_hBA_I` takes `STCaseI` instead of `STRegIterI`: both are
  strictly more general and imply the ticket's forms (composers simply do not pass the regime). The report states this in (b.6) items 1, 4.
- O2. At `𝔠d = 1/100` the `szB` instances satisfy (con_st_ind) only from `n ≈ 1.1·10^10` (report (a)(ii)). The hypothesis is still
  proved, not assumed, and is true for this data (not vacuous). The scratch check in §3 compiles the same instances at `𝔠d = 1/10`
  (threshold `n = 7 / 8`). The `sz0` window instances satisfy con already at `n = 0` (`0.902 ≤ 15/16`, report (a)(ii)).
- O3. `st_split_I/II` require the order hypotheses for all `n` (not only eventually). Composers whose time sequences cross `u_n`
  infinitely often must reindex or use a case split per subsequence. This is within the ticket's "say how" clause and recorded as T2058e.

## Verdict
All targets (items 1–6): **PASS**. No dispatcher sign-off needed.
