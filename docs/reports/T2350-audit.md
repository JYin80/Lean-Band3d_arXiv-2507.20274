Auditor model: claude-opus-5-5
# T2350 audit (round 1): UN-44 `Universality/GUEPhase/Eq729A`. Thu Oct  8 23:36:40 UTC 2026

Branch `t/T2350` at 8b1f52a (merge-base 692a72b, main 198f15c). Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2350-audit1` (detached).
Pin = the source statements of RBM2D `Universality/GUEPhase/Eq729A.lean` at 9e0f275 with the ticket's port map (the ticket's "Targets" line).

## 1. Statements: script diff of source vs port, port map applied
`sdiff.py` pulls each target's text from `theorem|def <name>` up to its top-level `:=` (comments dropped, whitespace collapsed) in both files, applies the ticket's port map to the source as regex rewrites (`(d : Sizes)`→`{d : ℕ} (sz : Sizes d)`, `d.L/W/size n`→`sz.…`, `Z2 L`→`Zd d L`, `gloop L W (blockMat M)`→`loopL d L W (blockMat d L W M)`, `spectralZ/M`→`zt/mE`, `KLoop.mSig`→`mSigma`, `(W:ℂ)^2`→`^d`, `(W*L)^2`→`^d`, `X `→`X d ` for genMatGUE/envConst/primBilGUE/primRhsGUE/egtNGUE/SBgue, `(L W : ℕ)`→`(d L W : ℕ)`), and diffs the tokens:
```
$ python3 -I scratchpad/T2350/sdiff.py RBM2D/RBM2D/Universality/GUEPhase/Eq729A.lean RBM3D-wt/T2350-audit1/RBM3D/Universality/GUEPhase/Eq729A.lean
eq729_primBil2: identical after port map
eq729_eG2: DIFF
   insert src:  | dst: d
   insert src:  | dst: d
eq729_norm_primBil2_le: identical after port map
eq729_primRhs_one: identical after port map
eq729F: identical after port map
eq729_step_nonneg: identical after port map
eq729_KΔ: identical after port map
eq729_time_mem: identical after port map
eq729_eta_pos: identical after port map
eq729_eta_le: identical after port map
eq729_zt_im: identical after port map
eq729_duhamel: identical after port map
eq729_norm_primRhs2_le: identical after port map
eq729_Kdisc: identical after port map
eq729e: identical after port map
eq729c: identical after port map
eq729_one_step: identical after port map
```
The two `eq729_eG2` inserts are `Idx L W`→`Idx d L W` in `(M : Matrix (Idx d L W) (Idx d L W) ℂ)` (source :89). That rename is in the port map, but my regex list left it out. Every hypothesis, binder order and conclusion matches the source; the 17 targets are all present.
The `d`-forms that carry the exponent (merged definitions):
```
RBM3D/Defs/Sizes.lean:157:def size (n : ℕ) : ℕ := (sz.W n * sz.L n) ^ d
RBM3D/Universality/GUEPhase/Bootstrap.lean:54:def SBgue : Matrix (Zd d L) (Zd d L) ℂ := Matrix.of fun _ _ => ((L : ℂ) ^ d)⁻¹
RBM3D/Path/OneStep.lean:78-79: def envConst (d L W : ℕ) (E : ℝ) (k : ℕ) (v : ℝ) : ℝ := 16 * ((k : ℝ) + 3) ^ 4 * (((W * L) ^ d : ℕ) : ℝ) ^ 4 * (1 + (etaT E v)⁻¹) ^ (k + 4)
```
So `N = (W L)^d` throughout: `hMΔ`, `3 N² Δ²` (`eq729_Kdisc`), `N α β` (`eq729_norm_primBil2_le`, `eq729_norm_primRhs2_le`), `eq729c (sz.size n) …` and `1 + Δ·2NρΛ` (`eq729_one_step`). `N^ℓ`, `Λ^j`, `Δ^{3/2}` and the literal `10000 = 16·5⁴` do not depend on `d` (envConst at `k = 2`). The quantifier order is the source's: all at a fixed `n`, with no `∀ᶠ`, in both files. **Statement: PASS for all 17.**

## 2. Vacuity, hidden hypotheses, cycles
```
$ grep -n '^import' RBM3D/Universality/GUEPhase/Eq729A.lean          -> 6:import RBM3D.Universality.GUEPhase.Drift
$ grep -n '^structure\|^class' RBM3D/Universality/GUEPhase/Eq729A.lean | wc -l   -> 0
```
- There are no structure-carried hypotheses. Every hypothesis is in a signature: `hdrift` (integrability, `eq729_duhamel`), and in `eq729_one_step` `hX`, `hB`, `hg1`–`hg3`, `hBk`, all as in the source.
- `hX`/`hB`/`hg1`–`hg3` are the second-half stochastic inputs (UN-47 `gueGrid_expect_oneLoop`, the `GUEPathBounds` fields). They are not from cited work, so no external limit check applies.
- The only import is the merged `Drift` (T2343), so there is no cycle.

## 3. Compiled nonempty instances (namespace `RBM.Univ.GUEPhase.Eq729AInst`, file :1088-1415)
Data: `d = 3`, `sz0` with `L = 4`, `W = 32`, `N = 2097152` (`Eq729AInst_Nnat`, from `sz0_values`); `n = 0`, `E = 0`; `t₁ = 17/20`, `t₀ = 9/10`, `K = 131072`, so `Δ = 1/2621440` and `NΔ = 4/5`. The family `K̃_s` equals `c(s) = 10⁻⁶/(1 − N·10⁻⁶(s − t₁))` on 2-loops and `0` on other lengths. The ODE `c' = N c²` is proved (`Eq729AInst_hasDerivAt`), and `primRhsGUE K̃_s = N c(s)² ≠ 0` (`Eq729AInst_primRhs`). Nothing degenerates: no `N = 0`, no empty index set, no collapsed window, no `False` premise.
| target | instance | deterministic hypotheses |
|---|---|---|
| `eq729_Kdisc` | `eq729_Kdisc_check` :1201 | `hu hu' hΔ hb2 hMΔ hKb hKd`: all discharged (norm_num, `Eq729AInst_hKb`, `Eq729AInst_hKd`) |
| `eq729_norm_primBil2_le` | `_check` :1218 | `hA hB` from `Eq729AInst_hK0` (`‖c(t₁)‖ ≤ 10⁻⁶`) |
| `eq729_norm_primRhs2_le` | `_check` :1343 | `hb` discharged |
| `eq729_primBil2`, `eq729_primRhs_one`, `eq729_eG2` | `_check` :1330/:1338/:1351 | none (identities; eG2 at `M = diag 2`, `u = 1/2`) |
| `eq729_duhamel` | `_check` :1371 | `hE ht1 ht10 ht0 hk hwf hdrift`: all discharged (`hdrift` via private `Eq729A_hdrift_int`) |
| `eq729_one_step` | `_check` :1283 + `example` :1315 | `hE ht1 ht10 ht0 hΛ hΛ1 hρ0 hρΛ hMΔ hK2b hK3b hKd hk hBk`: discharged (`Λ = 10/N`, `ρ = 1`, `Bk = 50`) |
| `eq729_one_step` (cont.) | | `hX hB hg1–hg3` (stochastic inputs of UN-47) stay as hypotheses; the `example` takes `B = univ`, `p = 1`, so only `hX` remains |
| grid facts (6 lemmas) | `eq729_grid_facts_check` :1393 | discharged (`k = 1000 ≤ K`) |
| `eq729F`/`eq729e`/`eq729c` (defs) | used in the instances above; `eq729F` unfolded by `rfl` in `example` :1409 | n/a |
**Instances: PASS.**

## 4. Build, axioms, hygiene, diff
```
$ cd RBM3D-wt/T2350-audit1 && lake build RBM3D.Universality.GUEPhase.Eq729A > build.log 2>&1; echo exit=$?
exit=0
$ grep -E 'error' build.log | head ; grep -c 'Eq729A' build.log ; tail -1 build.log
0
Build completed successfully (3774 jobs).
```
(The first build in this worktree compiled the module. Its warnings all come from upstream merged files: Path/Walk, Path/Markov, Defs/Tail, Propagator/*, Green/LDEQuad. None come from Eq729A.)
```
$ lake env lean scratchpad/T2350/ax.lean     # #print axioms, 17 targets + 9 named checks
'RBM.Univ.GUEPhase.eq729_primBil2' [propext, Classical.choice, Quot.sound]
'RBM.Univ.GUEPhase.eq729_eG2' [propext, Classical.choice, Quot.sound]
'RBM.Univ.GUEPhase.eq729_norm_primBil2_le' [propext, Classical.choice, Quot.sound]
'RBM.Univ.GUEPhase.eq729_primRhs_one' [propext, Classical.choice, Quot.sound]
'RBM.Univ.GUEPhase.eq729F' [propext, Classical.choice, Quot.sound]
'RBM.Univ.GUEPhase.eq729_step_nonneg' [propext, Classical.choice, Quot.sound]
'RBM.Univ.GUEPhase.eq729_KΔ' [propext, Classical.choice, Quot.sound]
'RBM.Univ.GUEPhase.eq729_time_mem' [propext, Classical.choice, Quot.sound]
'RBM.Univ.GUEPhase.eq729_eta_pos' [propext, Classical.choice, Quot.sound]
'RBM.Univ.GUEPhase.eq729_eta_le' [propext, Classical.choice, Quot.sound]
'RBM.Univ.GUEPhase.eq729_zt_im' [propext, Classical.choice, Quot.sound]
'RBM.Univ.GUEPhase.eq729_duhamel' [propext, Classical.choice, Quot.sound]
'RBM.Univ.GUEPhase.eq729_norm_primRhs2_le' [propext, Classical.choice, Quot.sound]
'RBM.Univ.GUEPhase.eq729_Kdisc' [propext, Classical.choice, Quot.sound]
'RBM.Univ.GUEPhase.eq729e' [propext, Classical.choice, Quot.sound]
'RBM.Univ.GUEPhase.eq729c' [propext, Classical.choice, Quot.sound]
'RBM.Univ.GUEPhase.eq729_one_step' [propext, Classical.choice, Quot.sound]
'RBM.Univ.GUEPhase.Eq729AInst.eq729_Kdisc_check' [propext, Classical.choice, Quot.sound]
'RBM.Univ.GUEPhase.Eq729AInst.eq729_norm_primBil2_le_check' [propext, Classical.choice, Quot.sound]
'RBM.Univ.GUEPhase.Eq729AInst.eq729_one_step_check' [propext, Classical.choice, Quot.sound]
'RBM.Univ.GUEPhase.Eq729AInst.eq729_primBil2_check' [propext, Classical.choice, Quot.sound]
'RBM.Univ.GUEPhase.Eq729AInst.eq729_primRhs_one_check' [propext, Classical.choice, Quot.sound]
'RBM.Univ.GUEPhase.Eq729AInst.eq729_norm_primRhs2_le_check' [propext, Classical.choice, Quot.sound]
'RBM.Univ.GUEPhase.Eq729AInst.eq729_eG2_check' [propext, Classical.choice, Quot.sound]
'RBM.Univ.GUEPhase.Eq729AInst.eq729_duhamel_check' [propext, Classical.choice, Quot.sound]
'RBM.Univ.GUEPhase.Eq729AInst.eq729_grid_facts_check' [propext, Classical.choice, Quot.sound]
exit=0
$ grep -nE '\bsorry\b|\badmit\b|native_decide|^axiom|^\s*axiom ' RBM3D/Universality/GUEPhase/Eq729A.lean | wc -l
0
$ git diff --stat main...t/T2350 | tail -1
 1 file changed, 1417 insertions(+)        (RBM3D/Universality/GUEPhase/Eq729A.lean = the sole writable file; new)
$ grep -rnE '\b(eq729_[A-Za-z0-9_]*|eq729F|eq729e|eq729c|Eq729AInst)\b' RBM3D RBM3D.lean --include='*.lean' | grep -v '^RBM3D/Probe/' | wc -l   # on main
0
```
No frozen signature is touched, since the diff adds one new file only. The file is 1417 lines, under the stop size of 1600. **Build/axioms: PASS.**

## 5. Paper deltas
```
$ grep -c '7\.29\|eq:729' paper/tex/*.tex | awk -F: '{s+=$2} END {print s}'
0
```
The d ≥ 3 TeX has no equation numbered (7.29). The numbering is the ticket's and RBM2D's. The prove report proposes:
- `T2350a`: UN-44 is checked against RBM2D `Eq729A` under the port map, not against a d ≥ 3 TeX statement.
- `T2350b`: explicit constants (`3N²Δ²`, `10000N⁴(1+N)⁶Δ^{3/2}`) stand where the paper writes `≺`, and `d` enters only through `N = (WL)^d`.

These two cover every Lean/paper difference found in §1. **Paper deltas: PASS.**

## Observations (no effect on the verdict)
- O1. The conclusion of `eq729_one_step_check` is true but numerically weak (`eq729c ≈ 3.9e57` at `Δ = 1/2621440`, prove report (a′)). This is inherent to the source's statement at any admissible fixed `K`. The witnesses themselves are moderate (`N = 2^21`, `K = 2^17`); nothing is astronomically large.
- O2. The ticket's "109 `^ 2` tokens" is 82 in the source (prove report (a)(i)). This does not affect the port.
- O3. The ticket asked for two instances. The file has 9 named checks and 2 examples, covering every target.

## Verdict
All 17 targets: **PASS**. No dispatcher sign-off needed.
