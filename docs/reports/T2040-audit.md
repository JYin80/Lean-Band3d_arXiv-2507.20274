Auditor model: claude-opus-5-5
# T2040 audit (round 2) — LW-D1 light-weight layer design; probe `RBM3D/Probe/T2040Graphs.lean`
Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2040-audit2`, detached at `t/T2040` = eeda441. `date -u`: Sat Oct  3 10:22:17 UTC 2026.
`S=/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/d787b0e7-ec73-431d-9968-a805c3e11390/scratchpad`.

**Verdict: PASS** (all eight items). The round-1 RETURN (collapsed window `ℓ ≡ 0` in the `lem: EWGn2_N`-family instances; no
`LWtermExpN` instance) is repaired. No dispatcher sign-off needed.

## 1. Build, hygiene, diff
    $ git diff --name-only main...HEAD
    RBM3D/Probe/T2040Graphs.lean
    $ lake build RBM3D.Probe.T2040Graphs 2>&1 | grep -E "error|warning|T2040|Build completed"; echo exit=$?
    ✔ [3318/3318] Built RBM3D.Probe.T2040Graphs (11s)
    Build completed successfully (3318 jobs).
    exit=0
    $ grep -nE "\bsorry\b|\badmit\b|^\s*axiom\b|native_decide" RBM3D/Probe/T2040Graphs.lean | wc -l
    0
    $ lake env lean $S/audit2/ax2.lean      # collectAxioms over every non-internal constant of the module, then #print axioms
    probe decls=377 theorems=156 with non-standard axioms=0 []
    'RBM.Gauss.Sizes.lwterm_of_moment' depends on axioms: [propext, Classical.choice, Quot.sound]
    'RBM.Gauss.LWInst.ℓT_one_le' depends on axioms: [propext, Classical.choice, Quot.sound]
    'RBM.Gauss.LWInst.ℓT_window' depends on axioms: [propext, Classical.choice, Quot.sound]
    'RBM.Gauss.LWInst.assmExpT_of' depends on axioms: [propext, Classical.choice, Quot.sound]
    'RBM.Gauss.LWInst.inst_LWtermExp' depends on axioms: [propext, Classical.choice, Quot.sound]
    'RBM.Gauss.LWInst.inst_LWMomentExp' depends on axioms: [propext, Classical.choice, Quot.sound]
    'RBM.Gauss.LWInst.inst_LWtermExp_endT' depends on axioms: [propext, Classical.choice, Quot.sound]
    'RBM.Gauss.LWInst.inst_LWtermExpN' depends on axioms: [propext, Classical.choice, Quot.sound]
    'RBM.Gauss.LWInst.inst_chain_LWtermExp' depends on axioms: [propext, Classical.choice, Quot.sound]
    'RBM.Gauss.LWInst.inst_LWtermExpS' depends on axioms: [propext, Classical.choice, Quot.sound]
    'RBM.Gauss.LWInst.inst_LWterm_endT' depends on axioms: [propext, Classical.choice, Quot.sound]
    'RBM.Gauss.Sizes.lwtermexp_of_regimes' depends on axioms: [propext, Classical.choice, Quot.sound]
    'RBM.Gauss.Sizes.lwanp_of_key' depends on axioms: [propext, Classical.choice, Quot.sound]
    'RBM.Graph.owx_smallest' depends on axioms: [propext, Classical.choice, Quot.sound]
Only the sole writable probe file is touched (report-only ticket; probe stays on the branch); no merged file, so no frozen signature, is changed.

## 2. Pin statements (item 3): unchanged since round 1
    $ git diff -U0 9325727 eeda441 | grep "^@@" | cut -c1-60     # the repair commit
    @@ -1643,2 +1643,22 @@ open RBM RBM.Gauss RBM.Gauss.Sizes RBM
    @@ -1647,6 +1667,3 @@ theorem assmExp_of (hI : LWInit sz0 (S
    @@ -1671 +1688 @@ theorem inst_LWtermExp (h : LWtermExp 3) (
    ... (12 more one-line hunks in inst_LWMomentExp, inst_LWtermExp_endT, inst_chain_LWtermExp, inst_LWtermExpS)
    @@ -1823,4 +1840,14 @@ theorem inst_LWtermExp_endT (h : LWtermEx
    $ grep -c "ℓ0" RBM3D/Probe/T2040Graphs.lean
    0
All hunks lie in the instance namespace `RBM.Gauss.LWInst` (from line 1639); every pin (`LWE`, `LWf`, `LWterm`, `LWtermB`, `LWtermExp` 999,
`LWtermEXP`, `LWMoment`, `LWMomentExp`, `LWAnpKey(Gh)`, `LWAnp`, `LWweightExp`, `LWedgeExp`, `LWggExp`, `LWtermExpS` 1406, `LWtermExpN` 1421)
and every skeleton theorem is byte-identical to the version compared with the paper in round 1 (table there: all "match" or "match + delta",
deltas T2040a–o). Re-check of the pin whose instances the repair changed, `LWtermExp`/`LWAssmExp` (probe 992–1010) against 3_5:406–415:
    $ sed -n 407p paper/tex/3_5_Loop_Hierarchy.tex | grep -oE 'deterministic control parameter [^.]*\.|Suppose for some [^,]*,'
    deterministic control parameter $W^{-d/2}\le \Psi_t\le W^{-\e_0}$.
    Suppose for some $0\le \ell \le (\log W)^{10}\ell_t$,
`LWAssmExp` = `0<ε₀ ∧ LWWindow (W^{-d/2} ≤ Ψ ≤ W^{-ε₀}) ∧ LWInit (initialGT2) ∧ 0 ≤ ℓ ∧ ℓ ≤ (log W)^10·ellT ∧ LWLoopExp (LW_assm_exp, ∀D>0)`;
conclusion `η_t⁻¹ (W^{-d}B_{t,0})^{1/2} · W^{-d} tailW ℓ W D |a−b|` for all σ ∈ {±}², a, b, ∀D>0: match. Regime split
`LWtermExpS` (`1−t > ĝ²/L²`) / `LWtermExpN` (`1−t ≤ ĝ²/L²`) is 7_8:20 ("when 1−t ≤ ilambda²/L², ℓ_t = L"): match, delta T2040k.
No hypothesis hidden in a structure field (`LWAssmExp`, `LWLoopExp` are visible `def` conjunctions); no pin proves itself; skeleton dependencies are pins as hypotheses.

## 3. Compiled nonempty instances (item 8) — the repaired part
New window `ℓT t n = ellT (sz0.L n) (sz0.lam n) (t n)` (`ellT L g t = min (max (g/√|1−t|) 1) L`, `Defs/Params.lean:32`):
`ℓT_one_le : 1 ≤ ℓT t n` and `ℓT_window : ℓT t n ≤ (log W_n)^10 · ellT …` are proved (axioms above); `assmExpT_of` discharges all
deterministic conjuncts of `LWAssmExp` (`0<1/20`, `window0`, `0 ≤ ℓ`, window bound); `LWInit`, `LWLoopExp` stay as stochastic premises (allowed).
Used in `inst_LWtermExp`, `inst_LWMomentExp`, `inst_LWtermExpS`, `inst_chain_LWtermExp` (t ≡ 1/16) and `inst_LWtermExp_endT`, new
`inst_LWtermExpN` (t = t₀ = lemT z0_n). Window values and the index set of `inst_LWtermExpN` at the data, by script
(`1−|m|² = η/(Im m + η)` from `m + 1/m = −z`; `z0 n = 1/2 + i N^{-4/5}`, `N = (W L)^3`):
    $ python3 $S/audit2/regime.py
    n=0 L=4 1-t0=9.0512e-06 lam^2/L^2=1.5259e-05 regimeN(t0)=True ellT(t0)=4 ellT(1/16)=1
    n=1 L=8 1-t0=4.1868e-10 lam^2/L^2=9.3132e-10 regimeN(t0)=True ellT(t0)=8 ellT(1/16)=1
    n=2 L=12 1-t0=1.2195e-12 lam^2/L^2=3.1902e-12 regimeN(t0)=True ellT(t0)=12 ellT(1/16)=1
    n=5 L=24 1-t0=5.6407e-17 lam^2/L^2=1.9472e-16 regimeN(t0)=True ellT(t0)=24 ellT(1/16)=1
    n=50 L=204 1-t0=2.3318e-30 lam^2/L^2=1.8947e-29 regimeN(t0)=True ellT(t0)=204 ellT(1/16)=1
    n=500 L=2004 1-t0=1.1996e-44 lam^2/L^2=2.4310e-43 regimeN(t0)=True ellT(t0)=2004 ellT(1/16)=1
    n=5000 L=20004 1-t0=4.9011e-59 lam^2/L^2=2.4930e-57 regimeN(t0)=True ellT(t0)=20004 ellT(1/16)=1
    n=1000000 L=4000004 1-t0=3.6033e-92 lam^2/L^2=1.5259e-89 regimeN(t0)=True ellT(t0)=4e+06 ellT(1/16)=1
Asymptotically `(1−t₀)/(ĝ²/L²) ≈ 1.03 · 2^{-0.8} (n+1)^{-0.4} < 1`. So at t₀ the window is the full `ℓ = L_n` (the paper's 7_8:20 case) and the
index set of `inst_LWtermExpN` is all of `(Fin 2 → Bool) × (Fin 2 → Zd 3 L_n)` for every n: nonempty, nondegenerate. This is also the t → 1 /
L → ∞ extreme input of the acceptance criteria for `lem: EWGn2_N`. At t = 1/16 the window is `ℓ = 1` (two values `|a−b| ∧ ℓ ∈ {0,1}`; see O1).
Other instances (unchanged, checked in round 1, rebuilt here): `inst_owx_smallest`/`_second`/`_E`, `inst_AnpKey`/`inst_Anp`/`inst_AnpKeyGh`/
`inst_chain_Anp` on `figAux` (p = q = 2), `inst_LWterm(_endT)`, `inst_LWtermB` (decaying class `ΦB`), `inst_LWMoment(_endT)`,
`inst_LWtermEXP(_endT)`, `inst_ssl`/`inst_edge`/`inst_gg` at `(d,L,W,g,E,t) = (3,3,2,1,0,1/2)`. All at d = 3, nondegenerate data.

## 4. Inventory and size (items 1, 7): computed from the inventory, not guessed
    $ cd $S && python3 t2040_size.py | grep -E "^R =|tickets at|LW \+ BA"
    R = total merged lines / total kchar = 151 lines per TeX kchar
    tickets at 1000 lines: lo 22, central 27, hi 40   (design band 600-1500 lines: central 18..46)
    tickets at 1000 lines: lo 6, central 6, hi 8   (design band 600-1500 lines: central 4..11)
    LW + BA tickets at 1000 lines: lo 28, central 34, hi 48
Reproduces report b.9 (hi 48 ≤ 50: no first-line flag required by the ticket). Model = inventory span chars × 151 lines/kchar × sketch
multiplier; the cited/no-proof items are fixed judgments disclosed in report (d) (round-1 O5).

## 5. Paper-delta coverage
    $ grep -o "T2040[a-z]\b" docs/reports/T2040-prove.md | sort -u | tr '\n' ' '
    T2040a T2040b T2040c T2040d T2040e T2040f T2040g T2040h T2040i T2040j T2040k T2040l T2040m T2040n T2040o
The repair changes no statement, so no new Lean/paper difference arises; the round-1 coverage (every difference has a candidate) stands.

## 6. Observations (no RETURN)
- O1. At t ≡ 1/16, `ℓT tInst ≡ 1` (`ĝ_n/√(15/16) < 1`), so the window of `inst_LWtermExp(S)`, `inst_LWMomentExp`, `inst_chain_LWtermExp` is
  `{0,1}`: not collapsed, and it is the paper's `ℓ_t` at that t; the full window `ℓ = L_n` is exercised by `inst_LWtermExpN`/`inst_LWtermExp_endT` at t₀.
- O2. Nonemptiness of the `inst_LWtermExpN` index set (`1 − t₀ ≤ ĝ²/L²`) is shown numerically (§3), not proved in Lean; same status as round-1 O3
  for `inst_LWtermEXP`.
- O3. Report section (b) heading still names commit 9325727; b.10 names the repair commit eeda441. Report: 299 lines (≤ 300), line 1 `Prover model: claude-sonnet-5-5`.
- O4. Round-1 O2 (constant class `Φ0` makes `Ψ(c|a−b|)` independent of `c`), O4 (`inst_owx_smallest_E_unit` is 0 = 0; nondegenerate siblings exist)
  and O5 (34% of the LW size estimate is fixed judgment; hi bound 48 is 2 below the §9 O2 flag) still apply.

## 7. Per-target verdicts
| item | verdict |
|---|---|
| 1 inventory (script) | PASS |
| 2 vocabulary (`LGraph` record chosen over `GTerm`) | PASS |
| 3 pins vs paper | PASS (deltas T2040a–o) |
| 4 route/risk | PASS |
| 5 skeleton + (Owx) proved on the smallest graph | PASS |
| 6 block Anderson reuse | PASS |
| 7 split/size from inventory | PASS (O4) |
| 8 instances | PASS (round-1 items 1–3 repaired: `ℓT` window, `inst_LWtermExpN` at t₀, report b.10 updated) |
