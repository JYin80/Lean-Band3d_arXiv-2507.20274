Auditor model: claude-opus-5-5

# T2244 audit (round 2, after repair `23d9275`) — UN-09 `GUELocalBootstrap` — Tue Oct  6 03:10:37 UTC 2026

Branch `t/T2244` at `23d9275` (commits `06eefc8`, `23d9275`; merge-base with main `389ad9e`).
Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2244-audit2` (detached at `23d9275`).
Scratch (auditor scratchpad `T2244/`): `gen.sh` (builds `check_lib.lean`, `check_kept.lean`), `ax.lean`, `pre.lean`, `build.log`.

## 1. Diff scope, hygiene, build, axioms, registry

```
$ git diff --stat main...t/T2244
 RBM3D/Test/Axioms.lean                    |    1 +
 RBM3D/Universality/GUELocalBootstrap.lean | 1252 +++++++++++++++++++++++++++++
$ git diff 06eefc8 23d9275 --stat          (the repair)
 RBM3D/Universality/GUELocalBootstrap.lean | 132 +++++++++++++++++++++++++++---   (hunk @@ -1127 only: instance section)
$ git diff main...t/T2244 -- RBM3D/Test/Axioms.lean | grep '^[+-]'
+   `RBM.Univ.UNGUESchurTail, -- bulk universality pin, the Schur tail of the GUE local law (T2244, UN-09: owed; UN-10 GUELocalSchur; with un_gueLocal_of_tail gives UNGUELocal)
$ grep -nE "\bsorry\b|\badmit\b|^\s*axiom |native_decide|^\s*(structure|class) " RBM3D/Universality/GUELocalBootstrap.lean
(no output)
$ grep import RBM3D/Universality/GUELocalBootstrap.lean
import RBM3D.Universality.Step1RegularityGUE
import RBM3D.Green.LDE
import RBM3D.Green.EntryCore
import RBM3D.Induction.ConArgDet
import RBM3D.Induction.Split
import RBM3D.Gauss.FlowCalculus
$ lake build RBM3D.Universality.GUELocalBootstrap
✔ [3367/3367] Built RBM3D.Universality.GUELocalBootstrap (6.4s)
Build completed successfully (3367 jobs).            exit 0
  warning kinds (count): `show` linter 23, line length 17, unused hypothesis 4 (other modules); errors 0
$ lake env lean RBM3D/Universality/GUELocalBootstrap.lean | grep -E "error|sorry"   -> (none), exit 0
$ lake env lean ax.lean       (#print axioms of all 50 public theorem/def of the file, incl. GUELocalBootstrapInst.*)
     50 [propext, Classical.choice, Quot.sound]
$ lake build RBM3D            (worktree root, to refresh Test/Axioms olean for the pre-check)
Build completed successfully (4047 jobs).
$ lake env lean pre.lean      (import RBM3D; import RBM3D.Universality.GUELocalBootstrap; #assert_rbm_axioms)
pre exit 0
axiom audit: 7110 theorems, 2398 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
  RBM.Univ.UNGUELocal: 41 [no certificate]
  RBM.Univ.UNGUESchurTail: 3 [no certificate]
registry: 2 borrowed + 155 owed + 91 structural + 7 refuted; ...
```
Only the two sole writable files; `Pins.lean` (`UNGUELocal`) untouched; one owed line added, none deleted. PASS.

## 2. Statements against the pins (check sections 2.1-2.6)

`gen.sh`: from `docs/tickets/checks/T2244-check.lean` (+ `import RBM3D.Universality.GUELocalBootstrap`) keep sections
2.2-2.6 and append `example : T2244_<t> := @RBM.Univ.<t>` for the 23 targets of 2.2-2.5 and
`example : T2244_<t> := @RBM.Univ.GUELocalBootstrapInst.<t>` for the 5 instances of 2.6. `check_lib` drops the
check's 2.1 vocabulary (names resolve to the library's); `check_kept` keeps it and adds `Iff.rfl`/`rfl` for
`UNGUESchurTail`, `GlSmall`, `schurErr`, `schurBud`, `glPts`, `cGap`, `budSimp`.
```
$ bash gen.sh
examples: 28 (lib), 35 (kept)
check_lib exit 0; error lines 0
check_kept exit 0; error lines 0
```
Every target has exactly the pinned type (up to `Type*`/binder names); the library vocabulary is definitionally the
check's (`GlSmall` a conjunction `def` in the pinned order); `un_gueLocal_of_tail : UNGUESchurTail → UNGUELocal`
concludes the merged pin itself, not a special case. `UNGUESchurTail`: fixed `d, 3 ≤ d, sz, size → ∞, κ τ ε D > 0, q, Γ`,
window and `card ≤ N^q` hypotheses, then `∀ᶠ n`; the union over `z ∈ Γ n` and rows is inside the probability. The
repair changed no statement (hunk only after line 1127, in `GUELocalBootstrapInst`). Statements: PASS.

## 3. Hidden hypotheses, vacuity, cycles

- No `structure`/`class` in the file (grep above); `GlSmall` is a `def` on `ℝ`, satisfiable (`inst_glSmall`, `inst_glSmall_witness`).
- No cycle: `UNGUELocal` occurs only as the conclusion of `un_gueLocal_of_tail`; the single premise is the new owed pin
  `UNGUESchurTail` (registered owed, 3 uses), not refuted-registered; all imports are merged modules.
- External hypothesis `UNGUESchurTail` (TEAM §8 lesson 14): prove report (a) gives the concrete limit check (GUE
  simulation `N ≤ 2000`, ratio flat in `N`, `N^{1/40}` absorbs the constant below the `GlSmall` threshold
  `10^{72.09}`); the pin is eventual in `n` at fixed `ε`. Accepted. PASS.

## 4. Compiled nonempty instances (round-1 items 1-2)

```
$ for n in <23 targets>; do sed -n '1007,1252p' $F | grep -cw $n; done    (uses inside GUELocalBootstrapInst)
norm_msc_add_z_gt_one 1 | im_le_norm_msc_add_z 1 | norm_msc_le_inv_im 2 | msc_disc_sq 1 | sqrt_le_norm_two_msc_add_z 1 |
im_le_norm_two_msc_add_z 3 | sc_stability 2 | norm_msc_sub_le 1 | sc_residual 1 | norm_green_diag_le_two 2 | sc_one_step 2 |
norm_stieltjesN_le 2 | norm_stieltjesN_sub_le 1 | chain_bound 2 | schurBud_le 1 | exists_glPt 2 | interp_le 1 |
card_glPts_le 1 | gue_local_det 3 | glSmall_eventually 1 | glPts_mem 2 | glPts_card 2 | un_gueLocal_of_tail 2
```
New `example`s (read in the file; all compile, exit 0 above):
- `sc_stability`: `z = i`, `m = m_sc(i) + 1/2`, `c = 1` (`1 ≤ ‖2m_sc(i)+i‖` from `im_le_norm_two_msc_add_z`), `‖m − m_sc‖ = 1/2 ≤ c/2`. Nondegenerate.
- `norm_green_diag_le_two`, `sc_one_step`: `H = 0` on `Unit` (card 1), `z = 10i`; proved `G = m_N = Υ = −z⁻¹`
  (`|Υ| = 1/10 ≤ 1/4`), `‖m_N − m_sc‖ ≤ 1/5 ≤ min(c/2, 1/4)`, `c = 10 ≤ ‖2m_sc + z‖`, `υ = 1/10`. All hypotheses discharged.
- `chain_bound`: `κ = 2` (`cGap 2 = 2` proved), `x = 0`, `h = 1`, `K = 1`, `η k = 10 − k`, `υ k = 1/(10 − k)`;
  step `k = 0` discharged by `norm_num`. Two chain points, not degenerate.
- `exists_glPt`: `N = 2097152`, `κ = 1`, `τ = 1/10`, `z = i` (`N^{−9/10} ≤ 1 ≤ 10`).
- `gue_local_det` (the round-1 False-premise example is removed): now at the matched scale
  `N = Nsz sz0 n`, `H = Xmat 3 (sz0.L n) (sz0.W n) ω`, `κ = 1`, `τ = 1/10`, under `h : UNGUESchurTail` only:
  `∀ᶠ n, ∃ ω, ∀ z` in the window, `‖m_N − m_sc‖ ≤ N^{1/10}/√(N Im z)`. `hΓ` is derived (not assumed) from
  `inst_schurTail h` (measure `≤ ofReal(N^{−2}) < 1` since `1 < N` from `GlSmall`.1, so some `ω` is off the event),
  `GlSmall` from `inst_glSmall`, `Nonempty (Idx 3 …)` by `⟨0⟩`. This is the preferred form of round-1 item 2.
- Unchanged and still compiled: `inst_gueLocal` (`un_gueLocal_of_tail` at `d = 3`, `sz0`, `κ = 1`, `τ = 1/10`, `D = 2`;
  only `UNGUESchurTail` kept), `inst_schurTail` (`glPts_mem`, `glPts_card` discharged), `inst_glSmall`
  (`glSmall_eventually`), `inst_grid_nonempty` (`N = 2097152`), `inst_glSmall_witness`, and the round-1 accepted
  examples of the other `msc`/`stieltjesN`/budget/grid lemmas.
Every endpoint now has a compiled nonempty instance with every deterministic hypothesis discharged. PASS.

## 5. Paper deltas

`UNGUELocal` and `UNGUESchurTail` are not paper statements (`Pins.lean:483-485`; RBM2D route). Prove report (d)
proposes `T2244a` (portmap deps), `T2244b` (`GlSmall` conjunction vs RBM2D structure), `T2244c` (threshold
`10^{72.09}` vs RBM2D docstring `10^73`). The repair adds no statement difference. PASS.

## Observations (no verdict effect)
- Prove report repair section prints axioms for `GUELocalBootstrapInst.ex_chain_bound`, `ex_exists_glPt`; the file has
  no such names (the instances are anonymous `example`s). Scratch names only; the file's 50 public declarations print the
  three standard axioms (section 1).
- `inst_glSmall_witness` uses `N = 10^80`; `GlSmall` at `κ = 1`, `τ = 1/10` genuinely needs `N ≳ 10^{72}`, and the
  eventual instance `inst_glSmall` along `sz0` is the operative one. Not a vacuity issue.
- The `H = 0` on `Unit` examples are nondegenerate for the pinned deterministic lemmas (generic `ι`, card 1); the model-scale
  application is the `gue_local_det` example.

## Verdicts per target

| target | verdict |
|---|---|
| 1 `msc` facts (check 2.2) | PASS |
| 2 self-consistent equation (2.3) | PASS |
| 3 chain/budget/grid/`gue_local_det`/`glSmall_eventually` (2.4) | PASS |
| 4 assembly `glPts_mem`, `glPts_card`, `un_gueLocal_of_tail` (2.5) | PASS |
| 5 instances (2.6) | PASS |

**Overall: PASS.** No dispatcher sign-off needed.
