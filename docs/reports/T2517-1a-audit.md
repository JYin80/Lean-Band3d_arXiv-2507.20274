Auditor model: claude-opus-5-5
# T2517 1a-audit (design gate) — Thu Oct 15 09:20:52 UTC 2026
Inputs: ticket `docs/tickets/T2517.md`, check `docs/tickets/checks/T2517-check.lean` (H317-amended), section (a), (a′), (a″) of
`docs/reports/T2517-prove.md`, branch `t/T2517` at `c305806d`. Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2517-1a-audit1`
(detached at `c305806d`); scratch `<A>` = scratchpad `T2517/audit/` (not in the repository).

## 1. Probe recompile, hygiene, diff
```
$ lake build <the 5 row-a imports>                       -> Build completed successfully (3927 jobs).
$ lake env lean RBM3D/Probe/T2517Pins.lean               -> EXIT=0, 38 output lines, 0 lines matching error|warning
'RBM.BA.T2517Probe.probe_R_good' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.T2517Probe.probe_R_row7' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.T2517Probe.probe_window' depends on axioms: [propext, Classical.choice, Quot.sound]
$ grep -cE 'sorry|admit|native_decide|^ *axiom ' RBM3D/Probe/T2517Pins.lean   -> 0
$ git diff --name-only main...t/T2517                     -> RBM3D/Probe/T2517Pins.lean   (sole writable, branch-only)
```

## 2. The texts signed here (compiled together)
`<A>/mksigned.py` builds `<A>/signed.lean` (208 lines, sha256 `48cb8c998f82415b…`): check lines 1–122 verbatim (imports,
Part 1, `T2517_GapBA`, `T2517_StableBA`), then `gueHBA` = probe `:37-39`, then check `:124-204` (targets 4, 6, 7) with every inline
body `(((g n : ℝ) : ℂ) • PsiI d (sz.L n) (sz.W n) + gueH (sz.withLam 0) t1 t0 K n X ω)` replaced by `(gueHBA sz g t1 t0 K n X ω)`.
```
inline bodies replaced: 7                                   (3 in target 4, 3 in target 6, 1 in target 7)
$ python3 -I <A>/t4diff.py <A>/signed.lean RBM3D/Probe/T2517Pins.lean
signed :133-158 (1599 chars) vs probe :49-71 (1599 chars): identical=True
$ lake env lean <A>/signed.lean      (09:18:05 UTC)       -> EXIT=0; only the Part-1 #check output, no error line
$ python3 -I <A>/c1s.py <A>/signed.lean                   (Part 2, comments dropped)
C1/UBA-C1 hits: []
gueH/Pgue/PathΩ/filt arguments: ['(sz.withLam']
X1-C4 def hits: 0 | defs: ['T2517_GapBA', 'T2517_StableBA', 'gueHBA', 'T2517_OneLoopBA', 'T2517_DriftBA', 'T2517_OneStepBA']
```
**Instance arguments (H317 (3)).** No explicit instance argument is needed: `NeZero (sz.L n)`, `NeZero (sz.W n)` are global
instances (`Defs/Sizes.lean:152` `instance neZeroL … sz.three_le_L n`, `:153` `neZeroW … sz.W_pos n`). The check's failure was a type
mismatch, `Idx d (sz.L n) …` vs `Idx d ((sz.withLam 0).L n) …` under `HAdd` (report (a″) finding 1, reproduced by the compile
above). The fix is `gueHBA` (target 1), whose body reads `PsiI` at `(sz.withLam 0)`. Its result type is over `sz.L n`, `sz.W n`. It is `rfl`-equal to the check's inline
reading (probe `:42-44`, compiled); `PathΩ (sz.withLam 0) = PathΩ sz` is `rfl` (probe `:46`, compiled).

### Statement check against the band twins (substitution table D1 (iii), script `<A>/bandsub.py`, `<A>/t4band.py`)
```
T6 (Drift:1318-1332 after table): band 378 tokens, signed 378 tokens, residual edits 0
T7 (Eq729A:731-764 after table): band 704 tokens, signed 863 tokens, residual edits 25
   insert: let F … := fun k ω I => loopL … (gueHBA sz g t1 t0 K n k ω) (ztOf (m n) (E n) (gridTime …)) I
           let e … := fun k I => (∫ ω, F k ω I ∂(Pgue (sz.withLam 0))) - Kt n (gridTime t1 t0 K n k) I
   the other 24: binder syntax only (`(hX : P)` -> `P →`, `∀`, `,`, parentheses)
T4 (OneLoop:1308-1322 after table): residual = (κ Λ explicit, `0 < Λ`), `g`, `m` added; `hlam : ∀ᶠ n, 0 < sz.lam n ≤ Λ` ->
   `∀ n, 0 < g n ≤ Λ`; `hE : |E n| ≤ 2 - κ` -> `∀ n, BAReal d (sz.L n) (g n) κ (E n) (m n)`; `gueScale sz E n u` -> `N·etaOf (m n) u`;
   `hoff` inserted after `h1`; the conclusion `∀ ε > 0, ∀ᶠ n, ∀ p, ‖∫ … - m n‖ ≤ N^ε (N η_u)^{-2}` unchanged.
```
The `let` bodies equal band `eq729F` (`Eq729A:275-278`) and `eq729e` (`:716-718`) under the table. T6's `|E| < 2` -> `0 < m.im`,
`‖m‖ ≤ 1` is what the band proof uses: `Drift:643-652` reads `|E| < 2` only through `norm_spectralM` (‖m‖ ≤ 1),
`spectralM_im_pos`, and `spectralZ_im_gap` (`grep -n "hE\b" Drift.lean`: `:643,651,656,765,1209,1332`).
Quantifier order: in T2 `∃ K` comes before `(d, L, g, E, m)` (U5S-C3). In T4 the fixed data come before `∀ ε, ∀ᶠ n`.

**Per text:**
- `T2517_GapBA`, `T2517_StableBA` (check `:108-122`, unchanged): **SIGNED**. Verified signatures: `baStab_of_real` (`‖v - tQv‖ ≤ B ⇒ ‖v‖ ≤ 16κ⁻⁴B`,
  `0 ≤ t ≤ 1`) and `BAoffDiag_of_real` (`κ²/4 ≤ ‖1-tm²‖`, row-0 off-diagonal sum `≤ (1-κ²/4)‖1-tm²‖`).
  `BAMss_row_offdiag_sum = 1-‖m‖²` and `EKNonzero_Mss_shift` were also checked (printed by the compile above). With these, the gap
  argument of (a) row 2 (`|1-ur_a| ≥ ε|1-um²| ≥ ε²`) and the `K` argument of row 3 close. `K = 16κ⁻⁴(1+16κ⁻⁴)` depends on `κ` only.
- `gueHBA` (target 1, probe `:37-39`): **SIGNED** as the row-a text. Its body changes from the ticket's reading only by `PsiI` at
  `(sz.withLam 0)`, and it is `rfl`-equal to that reading.
- `T2517_OneLoopBA` (probe `:49-71` = check `:129-154` via `gueHBA`): **SIGNED**.
- `T2517_DriftBA`, `T2517_OneStepBA` (check `:158-204` via `gueHBA`, `<A>/signed.lean`): **SIGNED**.

## 3. D1 (i)–(iii)
- **(i) SIGNED.** `R = x - QŜx`, `R_a = Σ Ŝ_pq E[τ_ap(g_q - m)]`. The compiled good-event step `probe_R_row7` gives
  `|·| ≤ ρ²(t₁+L^dσ)·CM·Λ_u²` from `hτ` (`hoff` form) and `hγ` (`h1` form), where `CM` comes from `baM_row_l1` with the premises of the
  text. Not compiled at the 1a, by design: the Stein identity, the bad event (`D ≥ 3`, `c_bad = 8`) and the `N^ε` absorption ((a)
  rows 5–6). The identity and `R` are checked numerically below. A `hoff`-free route loses `(Nη)^{1/2}` ((a) row 7), so the stop line
  does not fire. The consumer form of `hoff` is the second `StochDomAt` premise of `T2517_OneLoopBA`. Its producer route is
  `t_aq - Q_aq = M^B_aq twTr(q,a)`: numerically 5e-16, and the diagonal case is `h1`. The producer is C5 (Decision (2)).
- **(ii) SIGNED:** `T2517_DriftBA` is a BA leaf in row b, public (Decision (3)). Exact substitution of `Drift:1318` (0 residual).
- **(iii) SIGNED:** the flow datum is free `(g,E,m)` with `BAReal` (Decision (5)). `PathΩ` `rfl` is compiled. The substitution table is
  confirmed by the T6/T7 diffs.

## 4. Numerics rerun (seeded; identical to (a)(ii))
```
$ cd <A> && python3 final.py      (copies of the prover's final.py, inst.py, ident2.py, mc3.py; 09:18:43 .. 09:19:12 UTC; EXIT=0)
$ diff <(rerun minus timestamps) <(report (a)(ii) block)  -> IDENTICAL to report (a)(ii) block
[A] … E=0.5: GapBA: min_u,a|1-u r_a|=1.0000 >= kappa^4/16=3.91e-03 (True); … StableBA: K_emp=1.500 … <= K=6.579e+04 (True); 0 violations
[A] … E=1.8: GapBA: min_u,a|1-u r_a|=0.7872 >= kappa^4/16=2.14e-03 (True); … K_emp=2.129 … <= K=2.195e+05 (True); 0 violations
[B] … identity x_a=sum_pq S^_pq E[t_ap(g_q-m)]: max_a|x_a - rhs_a|=4.5e-04 (max z-score 0.80 …); negative control … z=11.7; twisted-trace identity … err 5e-16
[C] … N=512 …: |R|/Lu^2=0.073; good-event bound … = 2.45e+00 >= |R|: True
[C] … N=1728 …: |R|/Lu^2=0.184; good-event bound … = 1.58e-01 >= |R|: True
[T4] N_0=2097152=2^21; K_stab=65792; CM=6.2925e+06; c_bad=8 …; threshold N^(eps/2)>=K(CM+8)=4.140e+11
[T6] Im m=0.9676>0, |m|=0.999269<=1; grid time(k=1)=0.25000006<1 …
[T7] eta_t0=0.4838; Lam=9.856e-07<=1; rho*Lam=9.86e-06<=1; N*Delta=0.125<=1; p=2.5e-32>=0 …
```
Instance of the T4 text: probe `:118-124` applies `T2517_OneLoopBA 3` at `sz0`, `κ = 1/2`, `Λ = 1`, the flow datum of `sz0` at every `n`
(`BAflow_real`, `probe_window`), `t₁ = 1/4`, `t₀ = 1/2`, `K = 4`. Only `h1` and `hoff` (C5's) remain, so the example is nondegenerate.

## 5. Census and split
```
$ python3 census2.py && python3 central.py      (copies; census.py = T2515's)
OneLoop 1-1368: pure B/P/M 829/7/442 -> 906 | wide B/P/M 1015/7/256 -> 1091 | ticket 875 / 1031
Eq729A  1-1085: pure B/P/M 355/0/679 -> 416 | wide B/P/M 580/18/436 -> 652 | ticket 460 / 620
Drift   1-1359: pure B/P/M 0/0/1286 -> 80 | wide B/P/M 470/21/795 -> 560 | ticket 422 / 533
row a GUEOneLoop: central(pure)=1044 (1002-1336), central(wide)=1199 (1151-1535)
row b GUEEq729BA: central(pure)=958 (920-1226), central(wide)=1246 (1196-1595)
total central: pure 2002, wide 2445; … pre-signed split threshold 1950 -> split=True
```
**Census SIGNED; split a | b SIGNED** (row a `BA/GUEOneLoop`, targets 1–5, `t/T2517`; row b `BA/GUEEq729BA`, targets 6, 7, 9, `t/T2517b`,
stacked on `gueHBA`). Both rows are ≤ 1,950. The wide upper ends (1,535 and 1,595) exceed the 1,400 soft line but are below the
binding 2,000.

## 6. Stop lines, closure, names, registry
```
$ python3 -I <A>/vclos.py          (transitive import closure on main 13b68cea)
row a (= probe imports): closure 209 modules, V hits []
row b w/o GUEKPrim: closure 214 modules, V hits []
$ git grep -nw <16 ticket names: gueHBA … eq729_one_stepBA baEq729_Kdisc> main -- RBM3D   -> 0 hits each; GUEOneLoop/GUEEq729BA files absent
```
None of the stop lines is hit:
- no file over 2,000;
- no row central over 1,950;
- D1 (i) closes with a C5 route;
- `K` depends on `κ` only;
- no merged file changes;
- no V module or V name is read;
- `h1` and `hoff` are inline premises, so there is no Prop structure and no registry line (ticket expectation: none).

## 7. Paper deltas
No statement exists yet. The signed texts differ from the paper in two ways, which the ticket assigns to the 1b report as
`T2517a` (BA Lemma 5.15, `K = 16κ⁻⁴(1+16κ⁻⁴)`) and `T2517b` (the `M`-weighted input `hoff`). Both are covered by the ticket's report
item (7).

## Observations (no RETURN)
1. If T2515's pure regex is applied literally, Drift's pure census is 80, not 422. The total central is then 1,660
   (row a 1,044 + row b 416+80−10+130 = 616), and the split rule would give one row. Section (a) uses the ticket's Drift pure figure (422), as the ticket's own table
   does. The wide total (2,445) and Decision (4) support the split, so the split stands.
2. Row b's Layout import `BA/GUEKPrim` and target 8 contradict Decision (1). The 1b should drop both ((a) row 12); Decision (1)
   governs, so no sign-off is needed.
3. The ticket's target 5 cites `hr0I` (`n = 0` only). The family premise needs `BAflow_real` at every `n`, as the probe does.
4. T4 strengthens band `hlam` (`∀ᶠ n`, `sz.lam`) to `∀ n, 0 < g n ≤ Λ` on the free family. This is not a paper difference, and the
   instance discharges it.
5. The report has no explicit (i)–(xi) fill-in table. Item (iv), coverage as used, is spread over (a) rows 1–10. Item (xi) greps
   only 5 names. The full 16-name grep (§6) and the signatures of the coverage rows (§2) are verified here.

## Verdict
**PASS.** Every stage-1a deliverable is met: the probe compiles with the standard axioms; the T2517_* texts, D1 (i)–(iii), the census
and the split a | b are signed (§2–§5); no binding stop line is hit. No dispatcher sign-off is needed.
