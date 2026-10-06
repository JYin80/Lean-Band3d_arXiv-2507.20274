Auditor model: claude-opus-5-5

# T2290 audit (round 1): BA-D4 `RBM3D/BA/CombesThomas.lean`, `baPropM_holds`

Tue Oct  6 12:15:32 UTC 2026 (`date -u`); `t/T2290` = bda6b84 (base acb4f83), main 30f7ef8; worktree `RBM3D-wt/T2290-audit1`.

## 1. Diff scope
```
$ git diff --stat main...t/T2290
 RBM3D/BA/CombesThomas.lean | 674 +++++++++++++++++++++++++++++++++++++++++++++
 RBM3D/Test/Axioms.lean     |   1 +
$ git diff main...t/T2290 -U0 -- RBM3D/Test/Axioms.lean | grep '^[-+][^-+]' | wc -l
       1
+   `RBM.Adj, -- the nearest-neighbour relation ... hypothesis of `BAzdist_adj_lip` and `BAMB_lower_small` (BA-D4, T2290, DECISIONS §20: structural)
$ git merge-tree --write-tree main t/T2290 >/dev/null; echo $?
0
```
`Axioms.lean` is a sole writable file conditional on the registry pre-check flagging a name; it did (section 4).  No merged signature touched.

## 2. Statements against the pins (script, compiled)
Scratch `eq.lean` = check file's imports + `import RBM3D.BA.CombesThomas` + check file body + 12 examples:
```
example : RBM.BA.T2290Check.BAct_C = RBM.BA.BAct_C := rfl
example : RBM.BA.T2290Check.BAct_rate = RBM.BA.BAct_rate := rfl
example : RBM.BA.T2290Check.<Y>_pin := @RBM.BA.<Y>     -- Y ∈ {BAzdist_adj_lip, BAMB_resolvent_row, BAMB_ct_core,
   BAct_C_pos, BAct_rate_pos, BAMB_upper_small, BAMB_lower_small, BAMB_decay_large, BAPropM3_of_real, baPropM_holds}
$ lake env lean eq.lean ; echo eq_exit=$?      (lines containing "error": 0)
eq_exit=0
```
All 10 theorems and both definitions are definitionally the pins (binder order included).  `baPropM_holds_pin` is
`∀ d Λ κ, BAPropM d Λ κ`, i.e. the merged pin `MFixedPoint.lean:567` in full, unconditionally (no extra hypothesis).

Paper (`7_8:1888-1902`) vs pin: `(Mbound_AO)` `C⁻¹g1(a∼b) ≤ |M_ab| ≤ (Cg)^{|a−b|}` for `g < (2C)⁻¹`; `(Mbound_AO2)`
`|M_ab| ≤ c⁻¹e^{−c|a−b|}` for `g ≥ (2C)⁻¹` — conjuncts 5, 6 of `BAPropM`, with `C` before `L, g, E, m`.
`C = BAct_C d κ = 16d²/κ³` depends on `d, κ` only (as `:1888`); `c = BAct_rate d Λ κ` depends on `d, Λ, κ` (§18).
Quantifier order `3 ≤ d → 0<Λ → 0<κ → ∃C>0, ∃c>0, ∀L≥3, g∈(0,Λ], E, m, BAReal → …` is the merged pin's; unchanged.
The intermediate theorems are stronger than needed where stated: `BAMB_ct_core` holds for any `z, m` with
`κ ≤ Im(z+m)` (no `BAReal`), `BAMB_decay_large` for every `0 < g ≤ Λ` (no `(2C)⁻¹ ≤ g`).  Unused pin premises
(`(2C)⁻¹ ≤ g`; `3 ≤ d` beyond `0 < d`) are listed in prove report (b) narrative 5, as the ticket requires.
Verdict on statements: PASS for all 12 declarations.

## 3. Hidden hypotheses, vacuity, cycles
```
$ grep -nE "^\s*(private )?(structure|class |instance|opaque)" RBM3D/BA/CombesThomas.lean; echo "exit=$?"
exit=1
$ grep -n "^import" RBM3D/BA/CombesThomas.lean
6:import RBM3D.BA.Ward
$ grep -c "seqP\|Prec\|SeqΩ\|Sizes" RBM3D/BA/CombesThomas.lean      # §57 (3)
0
$ grep -c "Matrix.Norms" RBM3D/BA/CombesThomas.lean
0
$ grep -nE "sorry|admit|^axiom|native_decide" RBM3D/BA/CombesThomas.lean
(no hits)
```
No structure fields in the new file; hypotheses of the public theorems are only order conditions, `3 ≤ L`, `Adj`,
`BAReal` (merged data condition `BASelf ∧ κ ≤ Im m`, `MFixedPoint.lean:432`).  Dependencies are merged
(`RBM3D.BA.Ward` closure); `BAPropM` items (1)(2) come from merged `baPropM12_holds` (T2283).  No external
hypothesis (Aizenman Thm 10.5 not used), so no limit check is owed.  No cycle (single import, merged).

## 4. Build, axioms, registry
```
$ lake build RBM3D.BA.CombesThomas            (audit worktree)
Build completed successfully (3333 jobs).
exit=0
$ lake build RBM3D RBM3D.Test.Axioms          (branch root, so that the pre-check reads the branch's registry)
info: RBM3D.lean:332:0: axiom audit: 8288 theorems, 2693 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
Build completed successfully (4096 jobs).
exit=0
```
`#print axioms` (`ax.lean`, `import RBM3D.BA.CombesThomas`):
```
'RBM.BA.BAct_C' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BAct_rate' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BAzdist_adj_lip' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BAMB_resolvent_row' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BAMB_ct_core' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BAct_C_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BAct_rate_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BAMB_upper_small' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BAMB_lower_small' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BAMB_decay_large' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BAPropM3_of_real' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baPropM_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.CombesThomasInst.core_at_point' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.CombesThomasInst.decay_large_at_P' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.CombesThomasInst.propM3_at_P' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.CombesThomasInst.propM_at_P' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.CombesThomasInst.lip_at_point' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.CombesThomasInst.row_at_point' depends on axioms: [propext, Classical.choice, Quot.sound]
```
Registry pre-check `pre.lean` = `import RBM3D` / `import RBM3D.BA.CombesThomas` / `#assert_rbm_axioms`:
```
-- with main's registry olean (before rebuilding Test/Axioms in the worktree):
pre.lean:3:0: error: axiom audit: 1 premise(s) that no theorem of this development proves are in none of `borrowedProps`, `owedProps`, `structuralProps`, `refutedProps`, `supersededProps`:
  [RBM.Adj]
-- with the branch's registry (after the build above): exit 0, lines containing "error": 0
axiom audit: 8311 theorems, 2695 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
All within [propext,
 Classical.choice,
 Quot.sound]; no project axioms: ...
```
So the pre-check genuinely flags `RBM.Adj` and the one added `structuralProps` line is required; Build/axioms: PASS.

## 5. Compiled nonempty instances (`RBM.BA.CombesThomasInst`, `d = 3`, `L = 4`, `|Zd 3 4| = 64`)
| Target | Instance (file line) | Data; deterministic hypotheses discharged |
|---|---|---|
| `BAMB_ct_core` | `core_at_point` :603 | `g=10`, `κ=6/5`, `ν=log(1+1/100)>0` (`nu_pos`), `(zS+mS).im = wI.im = 6/5` (`gap_im`, by `sub_add_cancel`, `rfl`), gap `2·3·10·(1/100)=3/5=κ/2` (`gap_cond`); all closed |
| `BAMB_resolvent_row` | `row_at_point` :610 | same complex point, `Im ≠ 0` by `norm_num` |
| `BAzdist_adj_lip` | `lip_at_point` :618 | `x=(1,0,0)`, `y=0`, `b=(0,0,2)`, `Adj` by `decide` |
| `BAct_C_pos`, `BAct_rate_pos` | `C_pos_at` :665, `rate_pos_at` :668 | `d=3`, `κ=1/2`, `Λ=10` |
| `BAMB_decay_large` | `decay_large_at_P` :623 | merged flow point `P : FlowPt 4 10`: `Λ=10`, `g=P.g0` (`g0_pos`, `g0_le`), `κ=Im m₀` (`P.real.1.1`), `BAReal` (`P.real`); all closed |
| `BAPropM3_of_real` | `propM3_at_P` :630 | at `P`, all hypotheses closed; the two branches are the theorem's own implications |
| `baPropM_holds` | `propM_at_P` :651 | `d=3, Λ=10, κ=Im m₀`, applied at `L=4`, `P`; conclusion stated as `∃ C>0, ∃ c>0, …`; all closed |
| `BAMB_upper_small`, `BAMB_lower_small` | `upper_small_at_P` :641, `lower_small_at_P` :646 | at `P`, with `g₀ < (2C)⁻¹` left as hypothesis `h` |

All compile (build of section 4).  None is degenerate (`L=4`, nonempty index, `ν>0`, `g>0`, `κ>0`).
The small-branch data condition `g₀ < κ³/288` is not discharged in Lean: the ticket prescribes exactly this
("both branches as implications — no merged real-axis datum has a provable `g₀ < κ³/288`, the small branch is
instantiated in implication form only, say so in the report"), and the prove report says so (narrative 4, (d)).
Nonemptiness of `{BAReal, 0<g<(2C)⁻¹}` is evidenced numerically in prove (a)(ii) (`g/thr = 0.144, 0.970`, `L=3,4,6`).
Recorded as observation O1, not a RETURN, since it follows the ticket's explicit instance specification.

## 6. Paper-delta coverage
| Lean/paper difference | Coverage |
|---|---|
| bulk datum `BAReal` (`κ ≤ Im m`) instead of `(eq:WO)`, `|E| ≤ e_g − κ` (`7_8:1849`) | existing D403 (`docs/paper-deltas.md:1362`), §51 |
| explicit `C = 16d²/κ³`, `c = min(log(1+κ/(4dΛ)), κ/2)` depending on `Λ`; `(Mbound_AO2)` for all `0<g≤Λ` | candidate T2290a (prove report (d)) |
| unused pin premises (`(2C)⁻¹ ≤ g`, `3 ≤ d` beyond `0<d`) | listed in report (b) 5 / (d); no statement change |
| `|a − b|` = `zdistD` (periodic ℓ¹) | stated in report (d); same convention as merged pin `BAPropM` |
| route: Combes–Thomas instead of Taylor (`7_8:1909`) | route remark (not a statement difference) |
Coverage: PASS.

## 7. Observations (no effect on statement, instance, build, axioms or delta coverage)
- O1: small-branch instances are implications in `g₀ < (2C)⁻¹` (ticket-prescribed; section 5).
- O2: registry class "structural" chosen for `RBM.Adj` (the ticket anticipated `BAReal`/`BASelf` with class
  "data condition"); the dispatcher may reclassify.  `git merge-tree` against current main: no conflict.
- O3: the prove report's precheck must be run after rebuilding `RBM3D.Test.Axioms` in the worktree; with a stale
  registry olean it fails on `[RBM.Adj]` (section 4).  The report's "before/after" output matches this.
- O4: stale docstrings for the hub: `MFixedPoint.lean:557, 566, 582` ("Owed: BA-D3/BA-D4"); not edited (§57 (1)).

## Verdict
| Target | Verdict |
|---|---|
| `BAct_C`, `BAct_rate`, `BAct_C_pos`, `BAct_rate_pos` | PASS |
| `BAzdist_adj_lip`, `BAMB_resolvent_row`, `BAMB_ct_core` | PASS |
| `BAMB_upper_small`, `BAMB_lower_small` | PASS (O1) |
| `BAMB_decay_large`, `BAPropM3_of_real`, `baPropM_holds` | PASS |
| `RBM3D/Test/Axioms.lean` registry line `RBM.Adj` | PASS (O2) |

**T2290: PASS.**  No dispatcher sign-off needed.
