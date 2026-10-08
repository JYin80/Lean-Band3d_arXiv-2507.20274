Auditor model: claude-opus-5-5

# T2345 audit, round 1 (Thu Oct  8 22:18:41 UTC 2026)

Worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2345-audit1`, detached at `t/T2345` = 8b8401f. Source of the port: RBM2D `Universality/GUEPhase/DuhamelA.lean` at 9e0f275 (`git -C ../RBM2D --no-optional-locks log -1 --format=%h` → `9e0f275`).

## 1. Scope, hygiene
```
$ git diff --stat main...HEAD
 RBM3D/Universality/GUEPhase/DuhamelA1.lean | 1266 ++++++++++++++++++++++++++++
 1 file changed, 1266 insertions(+)
$ git diff main...HEAD --name-only | grep -v DuhamelA1.lean; echo rc=$?
rc=1
$ grep -nE "sorry|admit|native_decide|^\s*axiom" RBM3D/Universality/GUEPhase/DuhamelA1.lean; echo rc=$?
rc=1
$ (main worktree) grep -rnE "<7 target names>|DuhamelA1Inst" RBM3D --include='*.lean' -l | grep -v Probe; echo rc=$?
rc=1
```
Imports: the ticket's four plus `RBM3D.Induction.ConArgDet` (imports `Induction.Split`, `Loop.GLoop`, `Green.EntryCore`, `Mathlib.Algebra.Order.Chebyshev`; no `RBM3D` root, no cycle: the module builds). The ticket allows "only what a lemma needs".

## 2. Build and axioms
```
$ lake build RBM3D.Universality.GUEPhase.DuhamelA1 ; echo exit=$?   (grep error|warning DuhamelA1|axioms of the file|Build)
exit=0
info: DuhamelA1.lean:1252:0: 'RBM.Univ.GUEPhase.Duhamel_vGue_le' depends on axioms: [propext, Classical.choice, Quot.sound]
info: DuhamelA1.lean:1253:0: 'RBM.Univ.GUEPhase.DuhamelLoopCut' depends on axioms: [propext, Classical.choice, Quot.sound]
info: DuhamelA1.lean:1254:0: 'RBM.Univ.GUEPhase.Duhamel_frobSq_loopCut_le' depends on axioms: [propext, Classical.choice, Quot.sound]
info: DuhamelA1.lean:1255:0: 'RBM.Univ.GUEPhase.Duhamel_vGue_gradMat_le' depends on axioms: [propext, Classical.choice, Quot.sound]
info: DuhamelA1.lean:1256:0: 'RBM.Univ.GUEPhase.Duhamel_loopMax_le_crude' depends on axioms: [propext, Classical.choice, Quot.sound]
info: DuhamelA1.lean:1257:0: 'RBM.Univ.GUEPhase.Duhamel_loopMax_shift_le' depends on axioms: [propext, Classical.choice, Quot.sound]
info: DuhamelA1.lean:1258:0: 'RBM.Univ.GUEPhase.Duhamel_contDiffAt_loop' depends on axioms: [propext, Classical.choice, Quot.sound]
info: DuhamelA1.lean:1259..1266: the eight DuhamelA1Inst instances: [propext, Classical.choice, Quot.sound]
Build completed successfully (3780 jobs).
(no error lines, no warning from DuhamelA1.lean)
$ lake env lean registry.lean   # import RBM3D; import RBM3D.Universality.GUEPhase.DuhamelA1; #assert_rbm_axioms
registry exit=0
axiom audit: 10391 theorems, 3060 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
All within [propext,
```

## 3. Statements
### 3a. Three pinned targets: check-file equality
```
$ lake env lean pin_eq.lean   # check-file imports + DuhamelA1, check §2 defs, then:
example : RBM.Univ.GUEPhase.T2345Check.T2345_Duhamel_vGue_le := @RBM.Univ.GUEPhase.Duhamel_vGue_le
example : RBM.Univ.GUEPhase.T2345Check.T2345_Duhamel_loopMax_le_crude := @RBM.Univ.GUEPhase.Duhamel_loopMax_le_crude
example : RBM.Univ.GUEPhase.T2345Check.T2345_Duhamel_vGue_gradMat_le := @RBM.Univ.GUEPhase.Duhamel_vGue_gradMat_le
#print axioms RBM.Univ.GUEPhase.DuhamelA1Inst.vGue_le_inst  -> [propext, Classical.choice, Quot.sound]
pin_eq exit=0
```
### 3b. Four unpinned targets vs the source (awk extraction, RBM2D 9e0f275 vs RBM3D 8b8401f)
```
== src 348  def DuhamelLoopCut (L W : ℕ) [NeZero L] (M : Matrix (BlockIndex L W) (BlockIndex L W) ℂ) (z : ℂ)
               (I : LoopIdx (Z2 L)) (k : ℕ) : Matrix (BlockIndex L W) (BlockIndex L W) ℂ :=
             Gsig M z (I.σ.getD k true) * Eblk L W (I.a.getD k 0) *
               gloopProd L W M z ⟨I.σ.drop (k + 1) ++ I.σ.take k, I.a.drop (k + 1) ++ I.a.take k⟩ * Gsig M z (I.σ.getD k true)
== 3D  427  def DuhamelLoopCut (d L W : ℕ) [NeZero L] (M : Matrix (Vtx d L W) (Vtx d L W) ℂ) (z : ℂ)
               (I : LoopIdx (Zd d L)) (k : ℕ) : Matrix (Vtx d L W) (Vtx d L W) ℂ :=
             Gres M z (I.σ.getD k true) * Eblk d L W (I.a.getD k 0) *
               gloopProd d L W M z ⟨I.σ.drop (k + 1) ++ I.σ.take k, I.a.drop (k + 1) ++ I.a.take k⟩ * Gres M z (I.σ.getD k true)
== src 355  theorem Duhamel_frobSq_loopCut_le {M : Matrix (BlockIndex L W) (BlockIndex L W) ℂ}
                (hM : M.IsHermitian) {z : ℂ} (hz : z.im ≠ 0) {I : LoopIdx (Z2 L)} (hI : I.WF) {k : ℕ} (hk : k < I.length) :
                ∑ p, ∑ q, ‖DuhamelLoopCut L W M z I k p q‖ ^ 2 ≤ (|z.im|⁻¹) ^ 2 * RBM.Ind.loopMax L W M z (2 * I.length)
== 3D  434  theorem Duhamel_frobSq_loopCut_le {M : Matrix (Vtx d L W) (Vtx d L W) ℂ}
                (hM : M.IsHermitian) {z : ℂ} (hz : z.im ≠ 0) {I : LoopIdx (Zd d L)} (hI : I.WF) {k : ℕ} (hk : k < I.length) :
                ∑ p, ∑ q, ‖DuhamelLoopCut d L W M z I k p q‖ ^ 2 ≤ (|z.im|⁻¹) ^ 2 * RBM.Ind.loopMax d L W M z (2 * I.length)
== src 713  private theorem Duhamel_contDiffAt_loop {z : ℂ} (hz : z.im ≠ 0) (I : LoopIdx (Z2 L))
                {M : Matrix (Idx L W) (Idx L W) ℂ} (hM : M.IsHermitian) :
                ContDiffAt ℝ 2 (fun M' : Matrix (Idx L W) (Idx L W) ℂ => gloop L W (blockMat M') z I) M :=
== 3D  797  theorem Duhamel_contDiffAt_loop {z : ℂ} (hz : z.im ≠ 0) (I : LoopIdx (Zd d L))
                {M : Matrix (Idx d L W) (Idx d L W) ℂ} (hM : M.IsHermitian) :
                ContDiffAt ℝ 2 (fun M' : Matrix (Idx d L W) (Idx d L W) ℂ => loopL d L W (blockMat d L W M') z I) M :=
== src 970  theorem Duhamel_loopMax_shift_le {M : Matrix (BlockIndex L W) (BlockIndex L W) ℂ}
                (hM : M.IsHermitian) {z z' : ℂ} (hz : z.im ≠ 0) (hz' : z'.im ≠ 0) {K : ℝ} (hK : 1 ≤ K)
                (hGz : ‖green M z‖ ≤ K) (hGz' : ‖green M z'‖ ≤ K) (m : ℕ) :
                RBM.Ind.loopMax L W M z' m ≤ RBM.Ind.loopMax L W M z m + ((L : ℝ) * (W : ℝ)) ^ 2 * m * K ^ m * (‖z' - z‖ * K ^ 2)
== 3D 1053  theorem Duhamel_loopMax_shift_le {M : Matrix (Vtx d L W) (Vtx d L W) ℂ}
                (hM : M.IsHermitian) {z z' : ℂ} (hz : z.im ≠ 0) (hz' : z'.im ≠ 0) {K : ℝ} (hK : 1 ≤ K)
                (hGz : ‖green M z‖ ≤ K) (hGz' : ‖green M z'‖ ≤ K) (m : ℕ) :
                RBM.Ind.loopMax d L W M z' m ≤ RBM.Ind.loopMax d L W M z m + ((L : ℝ) * (W : ℝ)) ^ d * m * K ^ m * (‖z' - z‖ * K ^ 2)
$ grep -n "^variable" (section binders of the targets)
src  240/462/862: variable {L W : ℕ} [NeZero L] [NeZero W]
3D   310/541/946: variable {d L W : ℕ} [NeZero L] [NeZero W]
```
Line-by-line against the ticket's port map: `BlockIndex L W ↦ Vtx d L W`, `Z2 L ↦ Zd d L`, `Idx L W ↦ Idx d L W`, `Gsig ↦ Gres`, `gloop L W (blockMat M') ↦ loopL d L W (blockMat d L W M')`, `loopMax L W ↦ loopMax d L W`, `gloopProd L W ↦ gloopProd d L W`; the only non-renaming changes are the ticket's `d`-line `(L W)^2 ↦ (L W)^d` (shift) and `private ↦ public` (`Duhamel_contDiffAt_loop`, required by the ticket). Hypotheses, quantifier order, constants (`1/η²`, `m K^m`, `K²`) unchanged; no `3 ≤ d` added or needed.

Meaning of the objects (merged signatures): `loopMax d L W H z n := ⨆ x : (Fin n → Bool) × (Fin n → Zd d L), ‖loopL … ⟨ofFn x.1, ofFn x.2⟩‖` (`Induction/Split.lean:515`, a sup over a nonempty finite type, `loopMax_nonneg`); `Gres H z σ := Ring.inverse (H - (if σ then z else z̄) • 1)` (`Loop/GLoopFlow.lean:74`); `vGue sz n A := linVar (gueUnitVar sz) (fun c => linTr n A (seqXmat sz n (Pi.single c 1))) (coordFinset n)` (`GUEPhase/Markov.lean:291`). The `card (Vtx d L W) = (L W)^d` factor in the crude/shift bounds is the correct `d`-dimensional count.

## 4. Hidden hypotheses, vacuity, cycles
- No target takes a structure argument carrying a proof obligation other than `Sizes d` (the merged size sequence; supplies `NeZero (sz.L n)`, `NeZero (sz.W n)`). No `Prop`-valued hypothesis from another gate; no external hypothesis (none needs a limit check).
- Hypotheses `M.IsHermitian`, `z.im ≠ 0`, `I.WF`, `k < I.length`, `1 ≤ K`, `‖green M z‖ ≤ K` are all discharged at concrete data below; no circular dependency (dependencies are merged modules on `main`; the file's helpers are `private` with prefix `Duhamel_`).

## 5. Compiled nonempty instances (namespace `RBM.Univ.GUEPhase.DuhamelA1Inst`, file lines 1126-1248; all compile, §2)
| Target | Instance | Data | Hypotheses discharged |
|---|---|---|---|
| `Duhamel_vGue_le` (pinned data) | `vGue_le_inst`, `vGue_le_inst_value` | `sz0`, `n = 0`, `A = 1`; `frobSq_one_sz0`: `‖1‖_F² = 2097152` | none needed |
| `Duhamel_loopMax_le_crude` (pinned data) | `loopMax_le_crude_inst`, `loopMax_zero_eq` | `d = 3`, `L = W = 2`, `M = 0`, `z = i`, `m = 2`; `m = 0`: `loopMax = 64 = (2·2)^3` (sharp) | `isHermitian_zero`, `by simp` |
| `Duhamel_loopMax_shift_le` | `loopMax_shift_le_inst` | same, `z' = 2i`, `K = 1`, `m = 2` | `‖green 0 w‖ ≤ 1` from merged `norm_Gsig_le_inv_eta` at `η = 1` |
| `DuhamelLoopCut` / `Duhamel_frobSq_loopCut_le` | `loopCut_loop1`, `frobSq_loopCut_le_inst` | `d = 3`, `L = W = 2`, `M = 0`, `z = i`, `I = ([true],[0])`, `k = 0 < 1` | `WF` by `rfl`, `k < 1` by `simp` |
| `Duhamel_vGue_gradMat_le` | `vGue_gradMat_le_inst` | `sz0`, `n = 0`, `M = 0`, `z = i`, one-edge loop | all |
| `Duhamel_contDiffAt_loop` | `contDiffAt_loop_inst` | `d = 3`, `L = W = 2`, `M = 0`, `z = i`, one-edge loop | all |
No `N = 0`, empty index, `False` premise or collapsed window: `N = 2097152` at `sz0`, `card Vtx 3 2 2 = 64`, loop length 1 or 2, `|Im z| = 1`.

## 6. Paper deltas
The seven statements are deterministic port-level lemmas (no paper label states them verbatim). Differences: unit-GUE variance without the `S_GUE = 1/N` factor (T2345a), `Duhamel_contDiffAt_loop` made public (T2345b, API only), `d`-lines and `Coord ↦ CoordF` (T2345c, port map). All proposed in the prove report §(d); nothing uncovered. `docs/paper-deltas.md` has no existing `DuhamelA`/`vGue` entry (grep), so the dispatcher appends these.

## 7. Observations (no RETURN)
- O1. The instance theorems (`frobSq_one_sz0`, `vGue_le_inst`, …) are public but live in the ticket-pinned namespace `DuhamelA1Inst`; no clash (grep §1).
- O2. One import beyond the ticket's four (`Induction.ConArgDet`), within the ticket's "only what a lemma needs".
- O3. The `Duhamel_vGue_le` instance at `A = 1` shows `vGue 1 ≤ 8·2097152`, not the value `vGue 1 = N`; the theorem is applied at nondegenerate data, which is what §4 requires.

## 8. Verdict
| Target | Verdict |
|---|---|
| `Duhamel_vGue_le` | PASS |
| `DuhamelLoopCut` | PASS |
| `Duhamel_frobSq_loopCut_le` | PASS |
| `Duhamel_vGue_gradMat_le` | PASS |
| `Duhamel_loopMax_le_crude` | PASS |
| `Duhamel_loopMax_shift_le` | PASS |
| `Duhamel_contDiffAt_loop` | PASS |

Overall: **PASS**. No dispatcher sign-off needed.
