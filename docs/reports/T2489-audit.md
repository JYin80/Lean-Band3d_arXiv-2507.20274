Auditor model: claude-opus-5-5
# T2489 audit, round 1: L4b2a = file A `RBM3D/Graph/BAExp14b2.lean` (targets 1-3), branch `t/T2489` at 2f825d5e
Written Tue Oct 13 06:12:35 UTC 2026 (`date -u`). Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2489-audit1` (detached at 2f825d5e).
Scope: the pre-signed split (ticket line 8; section (a) row "size"): L4b2a = targets 1 (a)-(d), 2, 3 in file A. Targets 4-7 (file B,
the binding `T2489_S2`) are L4b2b on `t/T2489b` and are not audited here; their absence is not a defect.

## 1. Diff and build
```
$ git diff --name-only main...t/T2489 ; git merge-base main t/T2489
RBM3D.lean
RBM3D/Graph/BAExp14b2.lean
3d0b9578
$ git diff main...t/T2489 -- RBM3D.lean  ->  +import RBM3D.Graph.BAExp14b2  (after `BAAnpLift`, before `#assert_rbm_axioms`)
$ wc -l RBM3D/Graph/BAExp14b2.lean   ->  1794   (stop line 2000; reserve-file trigger 1800)
$ lake build RBM3D.Graph.BAExp14b2 | tail -2
✔ [4025/4025] Built RBM3D.Graph.BAExp14b2 (21s)
Build completed successfully (4025 jobs).          exit=0
$ lake build        (full library, branch root imports; registry check)
✔ [4344/4347] Built RBM3D.Test.Axioms (3.5s)
info: RBM3D.lean:579:0: axiom audit: 14591 theorems, 4552 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
Build completed successfully (4347 jobs).          exit=0
$ lake env lean docs/tickets/checks/T2489-check.lean   ->  exit=0, 0 error lines
$ grep -nwE "sorry|admit|native_decide|axiom" RBM3D/Graph/BAExp14b2.lean   ->  (no hit)
$ grep -rln "RBM3D.Graph.BAExp14b2" RBM3D RBM3D.lean   ->  RBM3D.lean   (no outside importer)
```
Only sole writable files are touched (`BAExp14b2.lean` new, `RBM3D.lean` one import line); no merged file is edited, so no frozen
signature changes. `Test/Axioms.lean` is unchanged.

## 2. Statements against the check shapes (scratch file, not committed)
Scratch `$SP/T2489/AuditChk.lean` imports `RBM3D.Graph.BAExp14b2` with `open private BAExp14b2_P3 BAExp14b2_I1K`. It copies the
check's shapes as `Chk1a`, `Chk1b`, `Chk2`, `Chk3` and closes each from the file's theorem. `Chk3` is the targets 3-5 shape restricted to `j < 4`.
```
$ diff of the shape text, check file vs scratch (whitespace-exact, line ranges)
1a check:219-220 vs Chk1a: identical
1b check:227-232 vs Chk1b: identical
2 check:209-213 vs Chk2: identical
3 check:239-246 vs Chk3: DIFF
5c5
<       ∀ j : Fin 8, PrecL sz μ
---
>       ∀ j : Fin 8, (j : ℕ) < 4 → PrecL sz μ
$ lake env lean $SP/T2489/AuditChk.lean ; echo exit=$?      (bodies below; no error lines)
example : Chk1a := @BAExp14b2_twTrP_G
example : Chk1b := @BAExp14b2_twCirc1
example : Chk2 := by  intro d hd …; obtain ⟨k, rfl⟩ : ∃ k, d = k + 2 := ⟨d - 2, by omega⟩
                      exact BAExp14b2_P3 (k := k) (by omega) hκ hε h𝔡 hflow ht0 ht hE hA
example : Chk3 := by  intro … _hm hK _hD hT1 hT2 j hj; obtain ⟨k, rfl⟩ …
                      have h := BAExp14b2_I1K (k := k) (by omega) hκ hε h𝔡 hflow ht0 ht hE hA hK hT1 hT2 j hj
                      (restriction to the subtype index: `measure_mono` on `badSetAt`, witness `u.1`)
exit=0
```
- **Target 1 (a)** `BAExp14b2_twTrP_G` (:47): the check shape is a term-level match (`@`, no tactic). Its companions are the `false` charge
  `_twTrP_G_false` (:63; `conj(twTr a c + twMB a c)`) and the both-charge form `_twTrP_chg` (:72). The index pattern `twTr c a + twMB c a` is the check's.
- **Target 1 (b)** `BAExp14b2_twCirc1` (:84): the check shape is a term-level match. The slot-1 pattern `MB c₂ a * twTrP n X₂ c₁ a` is the check's.
- **Target 1 (c), (d)** (no pin in the check; the ticket's "names are proposals"): `_L3_ward` (:1473), `_fold_ward` (:1549),
  `_wsum_c2` (:1632), `_wsum_c1` (:1650), `_kap_col` (:1381). Every hypothesis is deterministic data in the signature
  (`BAFlow`, `t ∈ [0,T0]`, `‖G_xx‖ ≤ A`, row/column `ℓ¹` bounds of `MB`, `Σ_a|κ| ≤ S`). There is no pin binder and no structure field.
- **Target 2** (P3, private `BAExp14b2_P3` :264): equals the check shape at `d = k + 2`, `3 ≤ d ↔ 1 ≤ k`. `BAExp14a_μ sz` is
  `abbrev … := Sizes.seqP (sz.withLam 0)` (`BAExp14aB.lean:650`), so it equals the shape's `μ` by definition. The bound is
  `(sz.Bctl n (t n))^(3/2)` with no `(1-t)⁻¹`, as the ticket requires. Premises: `STLocalEntrygL`, `LWAvgLawgL` only.
- **Target 3** (private `BAExp14b2_I1K` :1396): for `j < 4` (`BAExp14b_FS2` order `D1t, D2t, T2a, T2b, …`, `BAExp14b.lean:123-127`)
  it implies the check's family shape (`Chk3` above). Bound `(1 - t n)⁻¹ * Bctl^(5/2)`; same quantifier order (`k, κ, ε, 𝔡, sz, z`
  before `t`, pins, `j`). It is a stronger variant in two harmless directions: (i) five of the seven premises (`STLmaxgL`, `STDecaygL`
  not read); (ii) the index is the full `Bool × Zd × Zd`, not the subtype `λ²/L^d ≤ 1-t` (restriction compiled above).
  The red charge and the eight-tag union are target 6 (L4b2b).

## 3. Vacuity, hidden hypotheses, cycles, registry
```
$ python3 (signature scan: every `theorem|def` up to its first `:=`, grep for the seven S2 pins)
private BAExp14b2_P3 | private BAExp14b2_base | private BAExp14b2_D1t | private BAExp14b2_tl2
private BAExp14b2_D2t | private BAExp14b2_T2a | private BAExp14b2_T2b | private BAExp14b2_I1K
(no public declaration has a pin binder)
$ grep -nE "sz\.lam|withLam|gK" RBM3D/Graph/BAExp14b2.lean   (UBA-C1)  ->  (no hit)
$ grep -nwE 'mE|STGM|STKloop|etaT|STflowE|lwS|lwSplus' RBM3D/Graph/BAExp14b2.lean   (C1)  ->  (no hit)
$ grep -nE "^(structure|inductive)|^axiom" RBM3D/Graph/BAExp14b2.lean   ->  (no hit)
```
- The pins enter as explicit binders of exact merged type: `STLocalEntrygL`, `LWAvgLawgL`, `STLKgL`, `BATwistAvgLaw` (TL1) and
  `BATwistLoopLaw` (TL2), all premises of the merged S2. They sit only in private theorems, as the ticket's registry rule requires (`LWAvgLawgL` is
  unregistered). The full build ran `scanPremises`/`#assert_rbm_axioms` and passed.
- External-hypothesis limit check: TL1, TL2 are not new hypotheses of this row (premises 6, 7 of merged S2, T2434). Section (a) script 3
  still gives the `t = 0` limit (`G = M`): TL2 `max|L̃ - K̃_0| = 1.1e-16`, TL1 `max|twTr| = 0`.
- Dependencies are merged on `main`: `open private BAExp14a_q_prec BAExp14a_Dom_a from RBM3D.Graph.BAExp14aB` (L4a, T2418), plus
  `twK_bound_holds`, `twB0_ge_holds`, `twCirc_holds`, `twFold_holds`, `baKbound_holds`, `baTwistAvgProd_holds`, `BAExp14b_*` (L4b1).
  The new module imports only `BAExp14b`, `TwistFold2`, `KBound`, `TwistAvgB`. Nothing on `main` imports it, so there is no cycle.
- Constants: `C_M, S` from `BAExp14a_facts_of_flow` (depend on `k, 𝔡, κ`), `C` from `twK_bound_holds`. None is chosen after `(sz, z)` in
  a public statement (no `∃ C` in any signature).

## 4. Compiled nonempty instances (file A §8, :1671-1789; built with the module)
Data: `d = 3` (`k = 1`), `sz0`, `zSeq`, `flow_sz0` (`κ = 1/2`, `ε = 𝔡 = 1/10`, `𝔠 = 1/6`), `t ≡ 1/2 ≤ BAflowT0` (`half_lt_t0`),
`n = 0`: `L = 4`, `W = 32`. Blocks `0, e₀, e₁` are pairwise distinct (`example` :1706, proved by `decide` on `ZMod 4`).
| target | example | deterministic hypotheses discharged | left as hypotheses |
|---|---|---|---|
| 1 (a) | :1684 (`a = 0`, `c = e₀`), `false` :1692, `Tsplit` :1689 | `Im m > 0` by `BAflow_real … flow_sz0 0` | none |
| 1 (b) | :1697 (`X₁ = G`, `X₂ = G^*`, carrier `M`, `MB = M^{(B)}`, `a,c₁,c₂ = 0,e₀,e₁`) | tie `hM` by `BAExp14b2_M_tie` | none |
| 1 (c) | `fold_ward` :1767, `L3_ward` :1774 | `κ>0`, flow, `t` window, `‖G_xx‖ ≤ η⁻¹` (`BAExp14a_G_le`), `ℓ¹` of `M^{(B)}` (`_MB0`) | none |
| 1 (d) | `wsum_c2` :1781, `wsum_c1` :1785 (`κ_0 = 1`, `S = 1`) | column sums of `1` by `simp`; `_MB0` | `h ≥ 0` (arbitrary weight) |
| 2 | :1722 | `1 ≤ k`, `κ, ε, 𝔡 > 0`, `flow_sz0`, `0 ≤ t ≤ T0` | `STLocalEntrygL`, `LWAvgLawgL` (pins) |
| 3 | :1730 (all `j < 4`), and :1743 with TL1 discharged by `baTwistAvgProd_holds 3` | same | `STLocalEntrygL`, `LWAvgLawgL`, `STLKgL`, TL2 (+ `STLmaxgL` at :1743) |
The index type is nonempty (:1739, `(true, 0, 0)`). No instance uses `N = 0`, an empty index, a collapsed window, a `False` premise or an
astronomically large witness (`N = 2097152` at `n = 0`). Section (a) script 2 checks at these numbers that `U_n` is nonempty
(`λ²/L^d = 3.81e-06 ≤ 1/2`).

## 5. Axioms
```
$ lake env lean $SP/T2489/AuditChk.lean      (#print axioms)
'RBM.BA.BAExp14b2_twTrP_G' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BAExp14b2_twTrP_G_false' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BAExp14b2_twTrP_chg' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BAExp14b2_twCirc1' depends on axioms: [propext, Classical.choice, Quot.sound]
'_private.RBM3D.Graph.BAExp14b2.0.RBM.BA.BAExp14b2_P3' depends on axioms: [propext, Classical.choice, Quot.sound]
'_private.RBM3D.Graph.BAExp14b2.0.RBM.BA.BAExp14b2_I1K' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BAExp14b2_L3_ward' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BAExp14b2_fold_ward' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BAExp14b2_wsum_c1' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BAExp14b2_wsum_c2' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BAExp14b2_kap_col' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BAExp14b2_Tsplit' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BAExp14b2_close' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BAExp14b2_closeA' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BAExp14b2_closeB' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## 6. Paper deltas
```
$ grep -nE "T2398d|T2434c" docs/paper-deltas.md | cut -c1-40
1630:- **D666（T2398d）**：`B:118` 说 BA 情形的 Lemma
1649:- **D685（T2434c）**：S2 钉文 `BAExp14bS2`（`Graph/BAExp14b.lean:170`）
```
- D666 (T2398d: BA "analogous" Lemma B.1) and D685 (T2434c: S2 carries TL1, TL2) cover the BA twisted families and the premise list.
- Candidates proposed in the prove report (d): **T2489a**, the sharp P3 `𝔼X ≺ 𝔟^{3/2}`, a Lean lemma with no paper counterpart (BA has
  no improved average; band terms that read `𝔼X ≺ 𝔟²` close at `3/2 + 1`). **T2489b**, `I1K` stated over the full index
  `Bool × Zd × Zd` rather than the subtype. These two cover every Lean/paper difference of targets 1-3. Target 1 is pathwise
  algebra (`GGGamma` `:393-405` notation), and target 3 is a private sub-step of S2.

## 7. Observations (no statement, instance, build, axiom or coverage effect)
- O1. The ticket's target 1 (c) lists a twin of band `ward2` (`LWExpTerm4:391`). File A has none. Section (a) finding (1) says no route
  reads it (kernel Ward is `baKward_holds`). If L4b2b needs it, it can add it in file B, so it is not a defect of L4b2a.
- O2. `main` has moved past the branch base 3d0b9578 (T2482b, T2484b, T2486 merged; six import lines after `BAAnpLift`). This
  audit's full build is on the branch tree. At merge the hub takes the union of the `RBM3D.lean` import lines and runs the full build (rule (A) 5).
- O3. File A is 1794 lines, 6 below the reserve-file trigger 1800. Prove report (d) projects file B at about 1680 lines (L4b2b decision).

## Verdict
| target | statement | instance | build / axioms | deltas | verdict |
|---|---|---|---|---|---|
| 1 (a) `BAExp14b2_twTrP_G` (+ `_false`, `_chg`) | = check shape (term) | :1684, :1692 | pass / std3 | n/a (pathwise) | **PASS** |
| 1 (b) `BAExp14b2_twCirc1` | = check shape (term) | :1697 | pass / std3 | n/a | **PASS** |
| 1 (c), (d) `_L3_ward`, `_fold_ward`, `_wsum_c1/c2`, `_kap_col` | unpinned helpers, deterministic hyps | :1767-1785 | pass / std3 | n/a | **PASS** |
| 2 P3 `BAExp14b2_P3` (private) | = check shape at `d = k+2` | :1722 | pass / std3 | T2489a | **PASS** |
| 3 I1K `BAExp14b2_I1K` (private) | implies check shape, `j < 4` (fewer premises, larger index) | :1730, :1743 | pass / std3 | T2489b | **PASS** |
Overall L4b2a (file A, targets 1-3): **PASS**. No dispatcher sign-off is needed. Targets 4-7 remain L4b2b (`t/T2489b`).
