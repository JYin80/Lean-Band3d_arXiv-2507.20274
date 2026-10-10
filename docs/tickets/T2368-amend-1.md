# T2368 Amend 1 (dispatcher V2, Sat Oct 10 03:54 UTC 2026; DECISIONS §20, §181; supervisor `docs/supervisor/2026-10-10-0350.md` O4; hub state `docs/queue/T2368.state` 03:40 UTC)

- **Situation:** T2368 (BA-K03, `BA/KSolve.lean` 767 lines, 057f0f4) passed its audit (claude-opus-5-5). The merge stopped at rule (A) step 5: the full build fails on `#assert_rbm_axioms` with one unregistered premise, `RBM.BA.BAKsolve`. It is the hypothesis of `BAKsol_isKLoopS`, `BAKsol_rotate`, `BAKsol_translate`. The ticket wrongly said "Registry: none"; that was the dispatcher's error.
- **Classification (supervisor 0350 O4):** `BAKsolve` is **owed**, with producer **BA-K05b** (stage K, K-e: `BAKsolve` for all `n` is K05b's named target). K05b's ticket deletes the line when it proves `BAKsolve`.
- **Edit (repairer stage, H23 (c); the only edit):** in `RBM3D/Test/Axioms.lean`, inside `owedProps`, directly after the line `` `RBM.BA.STLocalMaxgL, -- … `` (the T2197/T2269 BA chain block), insert one line:
  `` `RBM.BA.BAKsolve, -- existence of the BA `𝒦` on `[0,1)` with `(Kn2sol)` (`1_2:1175`), hypothesis of `BAKsol_isKLoopS`, `BAKsol_rotate`, `BAKsol_translate` (T2368, DECISIONS §181); owed: BA-K05b (supervisor 2051 K-e, 0350 O4), which removes this line ``
- **Acceptance:**
  - registry pre-check (temporary uncommitted `import RBM3D` + `import RBM3D.BA.KSolve` + `#assert_rbm_axioms`, `lake env lean`, exit 0, output pasted);
  - full `lake build`;
  - a round-2 auditor checks by script that `git diff 057f0f4..HEAD` is exactly this one inserted line in `RBM3D/Test/Axioms.lean`.
- **Sole writable files:** now `RBM3D/BA/KSolve.lean` (unchanged by this amend) and `RBM3D/Test/Axioms.lean` (the one line). The new line merges with other `Test/Axioms.lean` edits by the union rule (H23 (b)); T2364 deletes the `LWMomentExp` line in another hunk.
- **Unchanged:** every target and statement of T2368, the stop line, the role.
