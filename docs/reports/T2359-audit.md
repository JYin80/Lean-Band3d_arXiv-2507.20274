Auditor model: claude-opus-5-5
# T2359 audit, round 1 (Fri Oct  9 03:55:47 UTC 2026)
Ticket `docs/tickets/T2359.md` + `T2359-amend-1.md`; check file `docs/tickets/checks/T2359-check.lean` (Amend 1 version);
branch `t/T2359` tip `ed12748`, merge base `1fcb883`; audit worktree `../RBM3D-wt/T2359-audit1` (detached at `ed12748`).
Scratch: `S` = scratchpad `T2359/audit/` (`kw.py`, `stm.py`, `auditeq.lean`, `reg.lean`, `build.log`).

## 1. Files touched, keyword-only edit of the merged `LWMomExp.lean`
```
$ git diff --name-only main...t/T2359
RBM3D/Graph/LWMomExp.lean
RBM3D/Graph/LWMomExpInf.lean
RBM3D/Graph/LWMomentExpA.lean
RBM3D/Graph/LWXiExp.lean
$ git diff --name-only 1fcb883 main -- RBM3D      # main moved to cd712be; no Lean change since the base
(empty)
$ python3 -I S/kw.py      # git diff -U0 main...t/T2359 -- RBM3D/Graph/LWMomExp.lean; each hunk must be exactly one
                          # '-' line equal to 'private ' + its '+' line; names/lines compared with the ticket C4 (a) list
hunks 11 all are single-line "private " deletions: True
names/lines match ticket C4(a) list exactly: True
  152: lwMomExp_chain_nonneg
  310: lwMomExp_step_aux
  434: lwMomExp_sys_bound
  710: lwMomExp_stepFn
  752: lwMomExp_walk_chain
  835: lwMomExp_path_ne
  846: lwMomExp_sysOf_length
  851: lwMomExp_sysOf_mem
  862: lwMomExp_pathEdges
  874: lwMomExp_pathEdges_card
  882: lwMomExp_prod_split
$ for n in <the 11 names>; git grep -nwE "(def|theorem|lemma|abbrev) $n" main -- RBM3D | grep -v Graph/LWMomExp.lean | wc -l
all 11: 0          # no downstream redeclaration that the de-privatisation could collide with
```
Only the four sole writable files are touched; the merged file changes by exactly the 11 listed `private ` deletions.

## 2. Statements against the pin (check section 2, prefix `T2359_` removed)
```
$ python3 -I S/stm.py     # textual block comparison, check file vs the three new files
EKTTkInf found identical
AnpNearInfAt found identical
AnpNearInf found identical
LWXiE found identical            # Amend 1 form: conjunct 2 on {_p // λ²/L² < 1 - t n}
LWXiExpClaim found identical
regA found identical
LWMomExpNoExpF found identical
$ grep -n '^theorem <targets>' <three files>
LWMomentExpA.lean:334:theorem lwMomExpNoExp_holds : ∀ (d : ℕ) (K : ℝ), 0 < K → LWMomExpNoExpF d K := by
LWMomExpInf.lean:282:theorem ekTTkInf_holds (d n : ℕ) : EKTTkInf d n := by
LWMomExpInf.lean:547:theorem lwMomExp_nearInf : ∀ d, AnpNearInf d :=
LWXiExp.lean:81:theorem lwTail32 {d : ℕ} (sz : Sizes d) {𝔠 c : ℝ} (h𝔠 : 0 < 𝔠) (hc : 0 < c) (hsz : sz.SizeTendsto)
LWXiExp.lean:568:theorem lwXiExpClaim_holds (d : ℕ) : LWXiExpClaim d := by
```
Definitional equality with the pins, compiled (S/auditeq.lean = check-file imports + the three new imports + check section 2
+ the five examples of the acceptance criteria + `#print axioms`):
```
$ cd ../RBM3D-wt/T2359-audit1 && lake env lean S/auditeq.lean 2>&1 | tail -20; echo "exit ${pipestatus[1]}"
'RBM.Graph.ekTTkInf_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.lwMomExp_nearInf' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.lwXiExpClaim_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.lwMomExpNoExp_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.lwTail32' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.LWMomExpInfInst.inst_ekTTkInf' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.LWMomExpInfInst.inst_near_pt' depends on axioms: [propext, Classical.choice, Quot.sound]
exit 0
```
The examples `T2359_X := X` elaborate, so each target has exactly the pinned type: no extra `variable` hypothesis, quantifier
order as pinned ((A) for every `K > 0`; `lwTail32` with free `c`; G2 with the generic radius hypothesis; conjunct 2 of `LWXiE`
on the subtype `λ²/L² < 1 - t`, Amend 1 change 1).

## 3. Vacuity, hidden hypotheses, cycles
- No `structure`/`class` is introduced (`grep -c '^structure\|^class'` = 0 in each file); the pins are `Prop` definitions
  identical to the check file. The structured hypotheses (`STFlow`, `LWAssmExp`, `Sizes.Prec`) are merged pins named by the
  check file section 1 / pinned statement text.
- Imports (all merged on `main`): `LWMomExpInf`: `Graph.LWMomExp`, `Graph.AnpKey`, `Kernel.PropT`; `LWXiExp`: `Graph.AuxGraph2`,
  `Graph.AnpKey`, `Graph.LWTermExpN`, `Graph.LWPsi`, `Kernel.PropT`; `LWMomentExpA`: `Graph.LWMoment`, `Graph.LWTermExpN`.
  None imports `RBM3D` or a probe; no cycle.
- Subtypes nonempty at the instance data (compiled, §4): conjunct 2 of `LWXiE` (`LWXiExp.lean:760`, by merged `strict_all`)
  and the (A) index set `λ²/L² < 1 - t ∧ regA` for every `K > 0` (`LWMomentExpA.lean:418`, diagonal pair).
- External hypothesis of G2 (`∀ τ > 0, ∀ᶠ n, √ρ_n ≤ τ log N_n`, C4 (d)): concrete limit check compiled as
  `lwXE_ρ0_rad` (`LWXiExp.lean:737`) at `ρ_n = log N_n` (threshold `log N_n ≥ τ^{-2}`, from `Real.tendsto_log_atTop` and
  merged `sz0_tendsto`), and discharged in the G2 instance.

## 4. Compiled nonempty instances (all in the target's own file; compiled by the module builds of §5)
| target | instance | data | left as hypotheses |
|---|---|---|---|
| `ekTTkInf_holds` | `LWMomExpInfInst.inst_ekTTkInf` (`LWMomExpInf.lean:575`) | d=3, n=2, L=ℓ=Λ=5, W=25, g=1/2, t=9/10, D = univ (125 pts), x=(0,e₀), y=(e₁,e₂); every premise by `norm_num`/`one_le_ellT` | none |
| `lwMomExp_nearInf` | `inst_near` (`:589`) + `inst_near_pt` (`:593`) | `figAux` (p=q=2), L=6, W=2, g=t=1/2, ℓ=Λ=2, ξ = τ-kernel, D = ℓ^∞ ball radius 2 (nonemptiness proved in the statement) | none |
| `lwXiExpClaim_holds` | example `LWXiExp.lean:766` | merged `sz0`, `z0`, `flow_z0`, κ=ε=𝔡=1/10, 𝔠=1/6, t ≡ 1/16 (`tInst_range`), ε₀=ε₁=1/20, ρ = log N (radius discharged), every D > 0 | `LWInit`, `LWLoopExp` (other gates' pins), entry law `‖G_t-M‖ ≺ W^{-1/20}` (stochastic input of the pin) |
| `lwTail32` | examples `LWXiExp.lean:774, 779` | `sz0`, 𝔠=1/6, c=1 (a=2,b=3) and c=1/4 (a=5,b=1) | none |
| `lwMomExpNoExp_holds` | examples `LWMomentExpA.lean:429, 443` | `sz0` data as above, (p,K) = (2,6) and (4,1/2), every D > 0 | `LWInit`, `LWLoopExp` |
No `N = 0`, empty index set, collapsed window or `False` premise; the instance data are the merged `sz0` family
(`L_n = 4(n+1)`, `W_n = (2(n+1))^5`) and small explicit lattices.

## 5. Build, axioms, forbidden tokens
```
$ cd ../RBM3D-wt/T2359-audit1 && lake build RBM3D.Graph.LWMomExp RBM3D.Graph.LWMomExpInf RBM3D.Graph.LWXiExp \
    RBM3D.Graph.LWMomentExpA > S/build.log 2>&1; echo exit $?
$ grep -c error S/build.log; tail -2 S/build.log
0
Build completed successfully (3899 jobs).
exit 0
$ grep -E 'LWMomExpInf|LWXiExp|LWMomentExpA' S/build.log | grep -v 'exceeds the 100\|show. tactic'
⚠ [3897/3899] Built RBM3D.Graph.LWMomentExpA (18s)
⚠ [3898/3899] Built RBM3D.Graph.LWMomExpInf (4.4s)
⚠ [3899/3899] Built RBM3D.Graph.LWXiExp (21s)
$ lake env lean S/reg.lean   # import RBM3D + the three new modules + #assert_rbm_axioms (uncommitted scratch)
exit 0
axiom audit: 10542 theorems, 3090 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
(lines containing "error": 0)
$ grep -n 'sorry\|admit\|native_decide\|^axiom\|^ *axiom \|implemented_by\|extern' <three new files>
(no output)
```
Axioms of the five targets: §2 (only `propext`, `Classical.choice`, `Quot.sound`). Warnings are linter style only.
Frozen signatures: the only edit to a merged file is §1 (visibility), no signature text changes.
Public names of the new files: `regA LWMomExpNoExpF lwMomExpNoExp_holds LWXiE LWXiExpClaim lwTail32 lwXE_phi
lwXiExpClaim_holds EKTTkInf AnpNearInfAt AnpNearInf sum_ball_inf_min_pow_le lwMEI_keyC ekTTkInf_holds lwMEI_tau
lwMomExp_nearInf inst_ekTTkInf inst_near inst_near_pt` (pinned names, file-stem prefixes, or the ticket's instance
namespace `LWMomExpInfInst`): rule (E) respected.

## 6. Paper deltas
| Lean/paper difference | coverage |
|---|---|
| conjunct 2 of `claim:xi` (exp class, `7_8:1653`) only on `λ²/L² < 1-t` | proposed `T2359a` (prove report (d)) |
| radius `(log W)^{3/2}` / generic `√ρ = o(log N)` | D620 (T2344c) |
| `claim:TTk` and near pin in `ℓ^∞` | D621 (T2344d) |
| shift factor `(ρ+1)^{(d-2)/2}` | D622 (T2348a) |
| region (A) scale `K (log W)^{3/2} ℓ_t`, free `K` | D623 (T2348b) |
(`grep -n 'T2348a\|T2348b\|T2344c\|T2344d' docs/paper-deltas.md` -> lines 1579-1582.) Every difference is covered.

## 7. Observations (no RETURN)
- O1. `lwMomExp_step_aux` is de-privatised as C4 (a) lists but is not called by the three new files (the prover reports this
  itself, b.7); harmless, it is the pinned list.
- O2. The G2 instance discharges the radius at `ρ = log N` rather than the `(log N)^{3/2}` of the preflight limit check; both
  satisfy the hypothesis, and the compiled one is the binding check.
- O3. `LWXiExp.lean` imports `RBM3D.Graph.LWPsi`, not in the ticket's import list; allowed by "only what a lemma needs".
- O4. Section (a) instance uses `t = 1/2`, the Lean instances `t ≡ 1/16` (merged `tInst`); no statement effect.

## 8. Verdict per target
| target | verdict |
|---|---|
| `ekTTkInf_holds` | PASS |
| `lwMomExp_nearInf` | PASS |
| `lwXiExpClaim_holds` (Amend 1 pin) | PASS |
| `lwTail32` | PASS |
| `lwMomExpNoExp_holds` (every `K > 0`) | PASS |
| `LWMomExp.lean` keyword edit (11 `private ` deletions) | PASS |
Overall: **PASS**. No dispatcher sign-off needed (the only new paper delta `T2359a` follows Amend 1 / DECISIONS §163 (1)).
