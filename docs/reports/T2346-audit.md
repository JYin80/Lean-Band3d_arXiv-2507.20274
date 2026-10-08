Auditor model: claude-opus-5-5

# T2346 audit (round 1) — Thu Oct  8 22:20:52 UTC 2026

Ticket: UN-37, port of RBM2D `Universality/GUEPhase/DuhamelA.lean` §5–§7 (lines 1041–1985, 9e0f275) into `RBM3D/Universality/GUEPhase/DuhamelA2.lean`. Branch `t/T2346` at a372a42; audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2346-audit1` (detached).

## 1. Scope of the branch
```
$ git diff --name-status main...t/T2346; git log --oneline main..t/T2346; git -C ../RBM2D log -1 --format=%h
A	RBM3D/Universality/GUEPhase/DuhamelA2.lean
a372a42 T2346: DuhamelA2 section 7 (grid, drift remainder) and compiled instances
e623813 T2346: DuhamelA2 sections 1-6 (one step, truncation bias, loop smoothness)
9e0f275
$ wc -l DuhamelA2.lean
    1334
$ grep -nE "sorry|admit|native_decide|^axiom|structure |class |instance " DuhamelA2.lean | wc -l
       0
```
Only the sole writable file is touched (new). No new structure/class (no hidden hypotheses in fields). Imports: `Drift`, `Path.StepDecomp` (not `RBM3D`).

## 2. Statements: independent translation diff (auditor's own script `tr.py`)
Script: extract each target in RBM2D lines 1041–1985 and in the new file (theorems to the first `:=`, defs with body), collapse whitespace, apply the ticket's port map to the source (`(d : Sizes)`→`(sz : Sizes d)`, `Idx (d.L n) (d.W n)`→`Idx d (sz.L n) (sz.W n)`, `d.size/L/W n`→`sz.… n`, `Sizes.{seqXmat,seqHflow,SeqΩ} d`→`… sz`, `gueUnit/Pgue/PathΩ/HermTestFun/filt/gueH/Duhamel* d`→`… sz`, `LoopIdx (Z2 X)`→`Loop.LoopIdx (Zd d X)`, `gloop L W (blockMat`→`loopL d L W (blockMat d L W`, `spectralZ`→`zt`, `envConst/genMatGUE`→`… d`), compare strings.
```
$ python3 -I tr.py ../RBM2D/RBM2D/Universality/GUEPhase/DuhamelA.lean RBM3D/Universality/GUEPhase/DuhamelA2.lean
DuhamelGood: src:1071 new:166: EQUAL
DuhamelZ: src:1075 new:170: EQUAL
DuhamelR: src:1080 new:175: EQUAL
DuhamelT: src:1085 new:180: EQUAL
DuhamelB: src:1090 new:185: EQUAL
Duhamel_measurableSet_good: src:1106 new:202: EQUAL
Duhamel_Z_re_im: src:1122 new:219: EQUAL
Duhamel_measurable_R: src:1309 new:408: EQUAL
Duhamel_integral_step: src:1360 new:462: EQUAL
Duhamel_measurable_loop: src:1418 new:523: EQUAL
Duhamel_norm_T_le: src:1486 new:594: EQUAL
Duhamel_norm_B_le: src:1710 new:818: EQUAL
Duhamel_measurable_coord: src:1783 new:891: EQUAL
Duhamel_gueH_measurable_filt: src:1798 new:906: EQUAL
Duhamel_drift_remainder_ae: src:1904 new:1008: EQUAL
```
15/15 equal. The binder change `{d : Sizes}`→`{d : ℕ} {sz : Sizes d}` is in `variable` lines (DuhamelA2.lean:162, 189, 364, 553, 692, 888, 912).

**d-lines (semantic check of merged definitions the statements use):**
```
$ grep -n "def size\|theorem card_Idx (n" RBM3D/Defs/Sizes.lean; grep -n "def seqHflow" -A3 RBM3D/Gauss/FineModel.lean
157:def size (n : ℕ) : ℕ := (sz.W n * sz.L n) ^ d
160:theorem card_Idx (n : ℕ) : Fintype.card (Idx d (sz.L n) (sz.W n)) = sz.size n :=
225:def seqHflow (n : ℕ) (u : ℝ) (ω : SeqΩ sz) :
226-    Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ :=
227-  (Real.sqrt u : ℂ) • seqXmat sz n ω
228-
$ grep -n "structure HermTestFun" -A3 RBM3D/Path/StepDecomp.lean
186:structure HermTestFun {d : ℕ} (sz : Sizes d) (n : ℕ)
187-    (Φ : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ → ℂ) : Prop where
188-  contDiffAt : ∀ M, M.IsHermitian → ContDiffAt ℝ 2 Φ M
189-  bdd₀ : ∃ C₀ : ℝ, ∀ M, M.IsHermitian → ‖Φ M‖ ≤ C₀
```
The truncation threshold of `DuhamelGood` and the factors `N^4`, `exp(-N/4)` of `Duhamel_norm_T_le`/`Duhamel_norm_B_le` are `sz.size n = (W L)^d = card Idx` (ticket d-line). Quantifier order, hypotheses (`|e|<2`, `I.WF`, `0 ≤ t1 n ≤ t0 n < 1`, `k < K n`, `hv : 0 ≤ v`, `hM`, `hC₂`) and constants (`C₂/2`, `16 e² C₂`, exponent `3/2`) are the source's verbatim. `HermTestFun` is merged on main (`Path/StepDecomp.lean:186`), deterministic fields only. No external hypothesis occurs in any target. No dependency on unmerged work: `Duhamel_contDiffAt_loop` is re-derived privately (`DuhamelA2_contDiffAt_loop`), nothing from T2345 imported; `gueH_succ`, `condExp_loop_drift_gue` are merged (`Drift.lean`).

## 3. Build and axioms (audit worktree)
```
$ lake build RBM3D.Universality.GUEPhase.DuhamelA2; echo EXIT=$?; tail -1; grep -c error; grep -c DuhamelA2.lean
EXIT=0
Build completed successfully (3776 jobs).
0
0
$ lake env lean ax.lean   # #print axioms of the 15 targets + 5 instance theorems
'RBM.Univ.GUEPhase.DuhamelGood' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.GUEPhase.DuhamelZ' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.GUEPhase.DuhamelR' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.GUEPhase.DuhamelT' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.GUEPhase.DuhamelB' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.GUEPhase.Duhamel_measurableSet_good' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.GUEPhase.Duhamel_Z_re_im' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.GUEPhase.Duhamel_measurable_R' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.GUEPhase.Duhamel_integral_step' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.GUEPhase.Duhamel_measurable_loop' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.GUEPhase.Duhamel_norm_T_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.GUEPhase.Duhamel_norm_B_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.GUEPhase.Duhamel_measurable_coord' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.GUEPhase.Duhamel_gueH_measurable_filt' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.GUEPhase.Duhamel_drift_remainder_ae' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.GUEPhase.DuhamelA2Inst.measurableSet_good_check' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.GUEPhase.DuhamelA2Inst.drift_remainder_ae_check' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.GUEPhase.DuhamelA2Inst.integral_step_check' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.GUEPhase.DuhamelA2Inst.norm_T_le_check' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.GUEPhase.DuhamelA2Inst.norm_B_le_check' depends on axioms: [propext, Classical.choice, Quot.sound]
$ lake env lean reg.lean  # import RBM3D; import RBM3D.Universality.GUEPhase.DuhamelA2; #assert_rbm_axioms  (EXIT=0)
axiom audit: 10399 theorems, 3064 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
```

## 4. Compiled nonempty instances (namespace `RBM.Univ.GUEPhase.DuhamelA2Inst`)
```
$ grep -n "^theorem .*check\|^theorem zero_mem_good\|^theorem exists_not_mem_good" DuhamelA2.lean
1115:theorem zero_mem_good : (0 : Sizes.SeqΩ sz0) ∈ DuhamelGood sz0 0 := by
1123:theorem exists_not_mem_good : ∃ y : Sizes.SeqΩ sz0, y ∉ DuhamelGood sz0 0 := by
1137:theorem measurableSet_good_check :
1172:theorem drift_remainder_ae_check :
1269:theorem Z_re_im_check (y : Sizes.SeqΩ sz0) :
1280:theorem measurable_R_check :
1288:theorem integral_step_check :
1299:theorem norm_T_le_check (y : Sizes.SeqΩ sz0) :
1308:theorem norm_B_le_check :
1317:theorem measurable_loop_check :
1323:theorem measurable_coord_check : Measurable[filt sz0 1] (fun ω : PathΩ sz0 => ω 0) :=
1327:theorem gueH_measurable_filt_check :
$ sed -n 1193,1196p DuhamelA2.lean   # drift instance: every hypothesis discharged by a proof term
  Duhamel_drift_remainder_ae sz0 DuhamelA2Inst_t1 DuhamelA2Inst_t0 DuhamelA2Inst_K 0 0 0
    (by norm_num) (DuhamelA2Inst_loop2_wf _ 0 1) DuhamelA2Inst_t1_nonneg DuhamelA2Inst_t1_le_t0
    (by norm_num [DuhamelA2Inst_t0]) (by norm_num [DuhamelA2Inst_K])
$ grep -n "^def sz0" RBM3D/Defs/Sizes.lean; grep -n "theorem card_Idx_sz0" -A0 RBM3D/Defs/Sizes.lean
260:def sz0 : Sizes 3 where
368:theorem card_Idx_sz0 : Fintype.card (Idx 3 (sz0.L 0) (sz0.W 0)) = 2097152 := by
```
- `Duhamel_measurableSet_good` (pinned): applied at `sz0` (d=3, L=4, W=32, N=2097152; the `Grid.lean` `GridCheck` sizes), together with `0 ∈ Good` and a point `∉ Good`: the set is neither empty nor full. Nondegenerate.
- `Duhamel_drift_remainder_ae` (pinned): applied at `sz0`, `n=k=0`, `e=0`, `t0=9/10`, `t1=(1-ouZeta(1/20))·9/10`, `K=4` (the `GridCheck` grid, Grid.lean:791-814), loop `(+,-;0,1)`; every hypothesis (`|e|<2`, `WF` by `rfl`, `0 ≤ t1`, `t1 ≤ t0`, `t0<1`, `0<4`) is discharged by proof terms; `Pgue sz0` is a probability measure so `∀ᵐ` is not vacuous. No pending-gate hypothesis remains.
- The other 13 targets also have compiled applications (`Φ = sin(Re tr)` with `HermTestFun` and `hC₂` proved, `v=1/4`, `M=0`; `Duhamel_measurable_loop` at `L=W=2`, `z=i`); defs are exercised through them. Not required by the ticket; all nondegenerate.

## 5. Name clashes
```
$ for n in <15 targets> DuhamelA2_ DuhamelA2Inst; git grep -nw $n main -- RBM3D/ :!RBM3D/Probe | wc -l; and in t/T2345:DuhamelA1.lean (code, -w)
all 0 on main; on t/T2345 only one docstring mention of `DuhamelB` (DuhamelA1.lean:796, a comment naming the consumer module). No clash.
```

## 6. Paper deltas
No target restates a paper statement: all fifteen are Lean device lemmas of the GUE-phase grid walk (one-step Taylor/truncation, measurability, the `(3/2)`-power drift remainder of the RBM2D route), ported verbatim under the port map with `N=(W L)^d`. The prove report proposes no candidate; I find no Lean/paper statement difference that needs one. Coverage: complete.

## 7. Verdicts
| Target | Statement | Vacuity/hidden/cycle | Instance | Build/axioms | Deltas | Verdict |
|---|---|---|---|---|---|---|
| `DuhamelGood` | = source + port map | none | yes | ok | n/a | PASS |
| `DuhamelZ` | = source + port map | none | yes | ok | n/a | PASS |
| `DuhamelR` | = source + port map | none | yes | ok | n/a | PASS |
| `DuhamelT` | = source + port map | none | yes | ok | n/a | PASS |
| `DuhamelB` | = source + port map | none | yes | ok | n/a | PASS |
| `Duhamel_measurableSet_good` | = source + port map | none | yes | ok | n/a | PASS |
| `Duhamel_Z_re_im` | = source + port map | none | yes | ok | n/a | PASS |
| `Duhamel_measurable_R` | = source + port map | none | yes | ok | n/a | PASS |
| `Duhamel_integral_step` | = source + port map | none | yes | ok | n/a | PASS |
| `Duhamel_measurable_loop` | = source + port map | none | yes | ok | n/a | PASS |
| `Duhamel_norm_T_le` | = source + port map | none | yes | ok | n/a | PASS |
| `Duhamel_norm_B_le` | = source + port map | none | yes | ok | n/a | PASS |
| `Duhamel_measurable_coord` | = source + port map | none | yes | ok | n/a | PASS |
| `Duhamel_gueH_measurable_filt` | = source + port map | none | yes | ok | n/a | PASS |
| `Duhamel_drift_remainder_ae` | = source + port map | none | yes | ok | n/a | PASS |

Observations (no RETURN): (1) `set_option` linters disabled at DuhamelA2.lean:45-48 (style only). (2) Follow-up noted by the prover: after T2345 merges, `DuhamelA2_contDiffAt_loop` duplicates the public `Duhamel_contDiffAt_loop` of `DuhamelA1`; dedup is optional.

**Overall: PASS** (15/15). No dispatcher sign-off needed. Full `lake build` is the hub's at merge.
