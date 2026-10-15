Auditor model: claude-opus-5-5
# T2517 row a audit, round 1 — Thu Oct 15 10:30:36 UTC 2026 (`date -u`)
Scope: row a only (`BA/GUEOneLoop`, D1, targets 1–5) on `t/T2517` at `bd9781b1`. Row b (`GUEEq729BA`, `t/T2517b`) is a separate row.
Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2517-audit1` (detached at `bd9781b1`). `<S>` = scratchpad `T2517/a1/` (not in the repo).
The signed texts are `<S>/../audit/signed.lean` (sha256 `48cb8c998f82415b…`, the file of `T2517-1a-audit.md` §2).

## 1. Build, axioms, hygiene, diff
```
$ lake build RBM3D.BA.GUEOneLoop     (10:28:09 .. 10:28:25 UTC)
✔ [3933/3933] Built RBM3D.BA.GUEOneLoop (12s)
Build completed successfully (3933 jobs).   EXIT=0   (0 error lines; no warning line names GUEOneLoop; the other warnings are replayed upstream ones)
$ lake env lean <S>/chk.lean    (signed.lean + `import RBM3D.BA.GUEOneLoop` + the examples of §2 + #print axioms)  EXIT=0, 0 lines matching error|warning|sorry
'RBM.BA.gueHBA' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.gueHBA_isHermitian' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.gueHBA_succ' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.ol_gueHBA_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baOneLoop_gap' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baOneLoop_stable' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.GUEOneLoop_blockId' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.gueGrid_expect_oneLoopBA' depends on axioms: [propext, Classical.choice, Quot.sound]
$ grep -cE "sorry|admit|native_decide|^ *axiom " RBM3D/BA/GUEOneLoop.lean   -> 0
$ git diff --name-status main...HEAD
M	RBM3D.lean
A	RBM3D/BA/GUEOneLoop.lean
A	RBM3D/Probe/T2517Pins.lean
$ git diff main...HEAD -- RBM3D.lean   -> one line `+import RBM3D.BA.GUEOneLoop` after `import RBM3D.BA.GUEKPrim`, before `#assert_rbm_axioms`
$ grep -n Probe RBM3D.lean   -> (no output)
$ <S>/clos.lean: import closure of RBM3D.BA.GUEOneLoop
closure modules: 5470; MainInd/TwistPins/Step6/Probe in closure: []
```
All three files are sole writable files. No merged file other than `RBM3D.lean` (one import line) is touched, so no frozen signature changes.

## 2. Statements against the signed pins (script diff and compiled equality)
```
$ python3 -I <S>/sdiff.py RBM3D/BA/GUEOneLoop.lean <S>/../audit/signed.lean     (whitespace collapsed)
baOneLoop_gap              vs T2517_GapBA     : 199 vs 199 identical=True
baOneLoop_stable           vs T2517_StableBA  : 333 vs 333 identical=True
gueGrid_expect_oneLoopBA   vs T2517_OneLoopBA : 1561 vs 1561 identical=True
gueHBA def vs signed       : 269 vs 269 identical=True
# in <S>/chk.lean, compiled (EXIT=0 above):
example : RBM.BA.T2517Check.T2517_GapBA := RBM.BA.baOneLoop_gap
example : RBM.BA.T2517Check.T2517_StableBA := RBM.BA.baOneLoop_stable
example : ∀ d, RBM.BA.T2517Check.T2517_OneLoopBA d := RBM.BA.gueGrid_expect_oneLoopBA
example : @RBM.BA.T2517Check.gueHBA = @RBM.BA.gueHBA := rfl
```
- Target 1 (`gueHBA`, `gueHBA_isHermitian`, `gueHBA_succ`, `ol_gueHBA_eq`): `gueHBA` matches the signed text (probe `:37-39`). The other three are the
  ticket's twins (`gueH_isHermitian` + `PsiI_isHermitian`, `gueH_succ`, `ol_gueH_eq` at `sz.withLam 0`, shifted by `g Ψ_I`). They have no extra hypotheses.
  Row b's base commit `db2015e4` has the same §1 text as `bd9781b1` (script diff of the `def gueHBA` … `ol_gueHBA_eq` block: identical).
- Target 2: equal to `T2517_GapBA` and `T2517_StableBA`. In `T2517_StableBA`, `∃ K` comes before `(d, L, g, E, m)`, so `K` is free of `L` and `g` (U5S-C3).
- Target 4: equal to `T2517_OneLoopBA`. The fixed data and the premises `h1`, `hoff` come before `∀ ε > 0, ∀ᶠ n, ∀ p`. The loss is `N^ε (N η_u)⁻²`.
  Index ranges are `Fin (K n + 1) × Zd` and `Fin (K n + 1) × Zd × Zd`, as signed.
- Target 3 (`GUEOneLoop_blockId`, D1 (i); no `T2517_*` text pinned): checked against the ticket's mathematics.
  Hypotheses: `(H₀ − (z+u m))M = 1`, `tr(M E_a) = m` for every `a`, `u = t₁ + L^d σ`, `σ = c₀ W^d`, the mixed variance
  `v_c = t₁ gvar_c(0) + c₀ w_c`, `Im z ≠ 0`, and `H₀` Hermitian and general.
  Conclusion: `𝔼 g_a − m = Σ_{p,q} (t₁ S^{(B)}(0)_{pq} + σ) 𝔼[W^d tr(G E_a M E_p)(g_q − m)]`, that is, `x_a = Σ Ŝ_{pq} 𝔼[t_{ap}(g_q − m)]` with `Ŝ = t₁1 + σJ`.
  It is general in `H₀`, `M`, `z`, `u`. It is at `g = 0` only through `SB d L 0` and `gvarF … 0` (the step-0 field, coverage row 3).
- C1 / UBA-C1 grep on the 8 public statements (comments dropped; regex `msc|mE|zt|etaT|gueScale|mSigma|envConst|gapK|Kstab3|kTwoGUE|
  kTwoGUELoop|UNModel.band`, `|E|<2`, `Theta d`, `sz.lam`, `SB d L g`):
```
C1/UBA-C1 hits in the 8 public statements: []
gueH/Pgue arguments: ['sz.withLam 0']
SB occurrences: ['SB d L 0']
```

## 3. Vacuity, hidden hypotheses, cycles
- No new `structure`, `class` or `Prop` def. The public declarations are `gueHBA` (def) and seven theorems. `h1` and `hoff` are inline `StochDomAt`
  premises of target 4, as signed (D1 (i)). `BAReal`, `StochDomAt`, `Pgue`, `Sizes` are merged and are read by name.
- The premises `h1` and `hoff` are external (producer C5, DECISIONS §339 (2)). Limit check: report (a) row 8 and `[C]` (re-run identically by the 1a-audit §4).
  The checks are `g → 0` (off-diagonal weights → 0, and the diagonal reduces to `h1`), the exact identity `t_aq − Q_aq = M^B_aq twTr(q,a)` (5e-16),
  and the measured `ρ_τ = ρ_g`. For `G = M` the left sides of both premises vanish. Neither premise is `False` or contradictory.
- No cycle: the closure contains no Probe, `MainInd*`, `TwistPins` or `Step6*` module, and no `T2517Probe` name is used. The axioms are the standard three.
- Name clash on `main` (`git grep -nw <name> main -- RBM3D RBM3D.lean`): 0 hits for all 8 public names and for `GUEOneLoopInst`. Private helpers:
  15 `GUEOneLoop_*`, 7 `GUEOneLoopInst_*`, none unprefixed (rule E).

## 4. Compiled nonempty instances (`GUEOneLoop.lean:1283-1391`, built above)
Data: `d = 3`, `sz0` (`N_0 = 2^21`), the flow datum of `sz0`, `t₁ = 1/4`, `t₀ = 1/2`, `K = 4`.
- T1: `gueHBA_isHermitian` at `n = 0`, `k = 4`; `gueHBA_succ` and `ol_gueHBA_eq` at every `n`, `k`, `ω` (no premises).
- T2 gap: `κ = 1/2`, `hr0I` (`n = 0`), `u = 1/2`, `a = 0`.
- T2 stable: the nonzero `x = δ₀` (`∃ a, x a ≠ 0` is proved), `t₁ = 1/4`, `σ = 1/(4L³)` (so `t₁ + L³σ = 1/2`), `y` from the equation, `B = Σ‖y‖`.
- T3: `hr0I`, `H₀ = blockMat(g0I Ψ)` (Hermitian), `M = blockMat(Mres …)` from `GUEOneLoop_Mdata` (`z + u m = E + m`), `z = ztOf m0I E0I (1/2)`
  with `Im z ≠ 0` proved, `c₀ = σ/W³ > 0`, `a = 0`.
- T4: `gueGrid_expect_oneLoopBA 3 le_rfl sz0 (1/2) 1 …`. Discharged: `3 ≤ d`, `0 < κ`, `0 < Λ`, `Tendsto size` (`sz0_tendsto`),
  `0 < g n ≤ 1` for every `n` (`GUEOneLoopInst_window`), `BAReal` for every `n` (`BAflow_real … flow_sz0 n`), `0 ≤ t₁ ≤ t₀ < 1`, `K n = 4 ≠ 0`.
  Only `h1` and `hoff` remain open (C5's pins).
None of these is degenerate: no `N = 0`, no empty index (`Fin 5 × Zd 3 4`), no collapsed window, no `False` premise, no astronomically large witness.

## 5. Paper deltas
`docs/paper-deltas.md` has no T2517 entry (`grep -c T2517` → 0). Prove report (d) proposes:
- `T2517a`: BA Lemma 5.15 on the grid: stability of `1 − M^{(+,+)}Ŝ`, `K = 16κ⁻⁴(1+16κ⁻⁴)`, bound `N^ε(Nη_u)⁻²`, versus paper `6:12-21`.
- `T2517b`: the `M`-weighted input `hoff`, which is absent at the band.
These cover every Lean/paper difference of targets 2–4. `h1` is the band's input form, and target 1 is a definition. The strengthened `∀ n, 0 < g n ≤ Λ`
on the free family is not a paper difference (1a-audit observation 4).

## Observations (no RETURN)
1. The branch diff contains the probe `RBM3D/Probe/T2517Pins.lean`. It is sole writable for the 1a only, branch-only and never merged.
   At merge the hub brings in only `RBM3D/BA/GUEOneLoop.lean` and the `RBM3D.lean` import line. The probe is not imported by `RBM3D.lean`.
2. Row a imports `Universality/GUEPhase/Drift` in addition to the ticket's list, for `gueH_succ`. It is a merged band file, not a V module, and is
   not edited (report (d) observation 1).
3. Coverage row 1 reads `BAoffDiag_scalar` instead of `BAoffDiag_of_real`. The statement is unchanged, `ε = κ²/4`.
4. The registry `RBM3D/Test/Axioms.lean` is not in the diff. The ticket expects no line, because `h1` and `hoff` are inline.

## Verdict
| target | verdict |
|---|---|
| 1 `gueHBA`, `gueHBA_isHermitian`, `gueHBA_succ`, `ol_gueHBA_eq` | PASS |
| 2 `baOneLoop_gap`, `baOneLoop_stable` (= `T2517_GapBA`, `T2517_StableBA`) | PASS |
| 3 `GUEOneLoop_blockId` (D1 (i)) | PASS |
| 4 `gueGrid_expect_oneLoopBA` (= `T2517_OneLoopBA`) | PASS |
| 5 instances | PASS |
**T2517 row a: PASS.** No dispatcher sign-off is needed.
