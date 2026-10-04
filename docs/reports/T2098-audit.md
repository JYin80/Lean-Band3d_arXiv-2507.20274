Auditor model: claude-opus-5-5
# T2098 audit, round 2 (ST2-26 `Path/Expansion`), Sun Oct  4 02:25:41 UTC 2026
Worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2098-audit2` (detached at `t/T2098` = d673266, base c5bbae7). Scratch: `scratchpad/T2098/`.
Round 1 RETURNed on paper-delta coverage only. The repair is report-only (`T2098-prove.md` (d) lines 272-277); the branch is unchanged (one commit, d673266). Everything below was re-run fresh.

## 1. Scope, build, axioms
```
$ git log --oneline main..t/T2098 ; git diff main...t/T2098 --name-only
d673266 T2098: ST2-26 Path/Expansion (Avec, stoppedDuhamel105, condExp_A_succ, grid_expansion_all)
RBM3D/Path/Expansion.lean
$ lake build RBM3D.Path.Expansion ; echo exit=$? ; grep -nE "error|sorry" build.log
exit=0
Build completed successfully (3754 jobs).                    (grep: no lines)
$ grep -nE "\bsorry\b|\badmit\b|native_decide|^axiom" RBM3D/Path/Expansion.lean ; echo grep=$?
grep=1
$ grep -nE "^(structure|class|instance|axiom)" RBM3D/Path/Expansion.lean ; echo rc=$?
rc=1
$ lake env lean ax.lean   (#print axioms RBM.Path.<x> for all 34 public theorem/def of the file); echo exit=$?
exit=0
$ grep -c "depends on axioms: \[propext, Classical.choice, Quot.sound\]" ax.out ; grep -v <that line> ax.out
34                                                           (no other line)
$ lake build RBM3D | tail -1 ; printf 'import RBM3D\nimport RBM3D.Path.Expansion\n#assert_rbm_axioms\n' > pre.lean ; lake env lean pre.lean ; echo precheck exit=$?
Build completed successfully (3839 jobs).
axiom audit: 3112 theorems, 1155 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
precheck exit=0
$ for n in <16 public names incl. the 5 `_at` forms>; git grep -nE "(def|theorem) $n\b" main -- RBM3D | wc -l
all 0
$ git diff --name-only c5bbae7 main      (main drift since the branch base)
RBM3D.lean RBM3D/Induction/HierAlgebra.lean RBM3D/Induction/HierarchyN.lean RBM3D/Test/Axioms.lean docs/... (T2095)
```
Only the sole writable file is touched; `RBM3D/Test/Axioms.lean` unchanged (no new premise). Main drift does not overlap this file; the hub's full build at merge covers it.

## 2. Statements (script diff against RBM2D `Path/Expansion` at c9a24cf; the check file pins no text)
Script `sig.py`: signature up to `:=`, whitespace-normalised; RBM2D renamed by R1-R3 (`(d : Sizes)` dropped, `PathΩ d`->`PathΩ sz`, `Z2 (d.L n)`->`Zd d (sz.L n)`, `d.`->`sz.`, `spectralM`->`mE`, `Sizes.size d n`->`sz.size n`, `Uop (L)`->`Uop d (L) (sz.lam n)`, `envConst (L..`->`envConst d (L..`, `Complex.normSq (mE E)`->`((Complex.normSq (mE E) : ℝ) : ℂ)`).
```
=== StoppedDuhamel105 identical after renaming
=== stoppedDuhamel105 identical after renaming
=== grid_expansion_all  -(Complex.normSq +((Complex.normSq +: +ℝ)   [x2; explicit ℝ->ℂ cast, same value]
=== grid_expansion      -(Complex.normSq +((Complex.normSq +: +ℝ)   [x2; same]
=== condExp_A_succ / Expansion_condExp_A_succ_of_lt_one / _rpow   -d), +sz),   [binder name of ω only]
=== grid_expansion' / grid_expansion_all'   -d), +sz), + cast as above
=== Avec, martInc, predInc, Dgrid, Rgrid, Zvec, Yvec identical after renaming
=== Expansion_uop_martInc_eq_all, stepZ_ukerMat_eq_Uker, stepY_ukerMat_eq_Uker_ae: Uop/ukerMat gain `d`, `(sz.lam n)` (merged Kernel vocabulary)
=== gridDelta  -(L  +(d L
```
`condExp_A_succ` (Lean, verbatim): hypotheses `|E| < 2`, `0 ≤ s n`, `s n ≤ t n`, `K n ≠ 0`, `j < K n`, `gridTime s t K n (j+1) < 1`; conclusion `predInc = Δ·Dgrid + Rgrid` (every ω, a) ∧ a.e. `‖Rgrid‖ ≤ envConst d (sz.L n) (sz.W n) E 2 u_{j+1} · Δ^{3/2} + 7 · (sz.size n) · η_{u_{j+1}}^{-4} · Δ^2`.
Used signatures (merged): `sz.size n := (sz.W n * sz.L n) ^ d` (`Defs/Sizes.lean:157`); `envConst d L W E k v := 16 (k+3)^4 ((WL)^d)^4 (1+η_v^{-1})^{k+4}` (`Path/OneStep.lean:78`); `Uop ξ v w A a = Σ_b ukerMat a.1 b.1 · ukerMat a.2 b.2 · A b`, `ukerMat = (1 - vξ SB d L g) Θ(wξ)` (`Path/Kernel.lean:46-52`); `Avec` = `sz.STLKM … ![true,false]` (= `STLM - STKloop`, `Induction/Step2Defs.lean:68`); `Dgrid` = `STELKLKM + STEGtM` (`Step2Defs.lean:99,110`, both with factor `W^d`).
- Class b: RBM2D's `(LW)^2` becomes `(WL)^d` through `sz.size`/`envConst`; constants `7`, `3/2`, `2`, `4` unchanged. No `d = 2` token remains in the statements.
- Quantifiers and windows: `StoppedDuhamel105`/`grid_expansion(_all)` as RBM2D (`∀ n` hypotheses on `s, t, K`, then `∀ n τ k ω`, `min k (τ ω) ≤ K n`); `_at` forms take the hypotheses at `n` only (DECISIONS §29 (4)). Window `0 ≤ s ≤ t < 1`, `K ≠ 0`.
- `τ : PathΩ sz → ℕ` is arbitrary: the identity is pathwise, at least as strong as the stopping-time form. `n = 2`, `σ = (+,-)` shape as the ticket requires (D149/D155/D161/D162).

## 3. Hidden hypotheses, vacuity, cycles
- No `structure`/`class`/`instance`/`axiom` in the file (grep rc=1). `StoppedDuhamel105` is a `Prop` proved unconditionally by `stoppedDuhamel105` (no premise in the signature). No external hypothesis, so no limit check is needed.
- Imports (`Expansion.lean:6-10`): `Path/{StepDecompLoop,DriftAlgebra,LoopStep,Kernel}`, `Kernel/Evolution`, all on main. No import of `RBM3D` or of an unmerged file; not circular.

## 4. Compiled nonempty instances (`Expansion.lean:1519-1743`, compiled in the module build above)
Data: `sz0` (`d = 3`, `sz0_values : sz0.L 0 = 4 ∧ sz0.W 0 = 32 ∧ sz0.size 0 = 2097152 ∧ sz0.lam 0 = 1/64`, `Defs/Sizes.lean:267`), `n = 0`, `E = 0`, `s = 1/10`, `t = 1/2`, `K = 4` (`Δ = 1/10`, `u_4 = 1/2`), `τ = 3`, `k = 4`.
```
1567 example (ω) : <full conclusion written out> := stoppedDuhamel105 sz0 0 instS instT instK inst_E inst_s0 inst_st inst_t1 inst_K 0 (fun _ => 3) 4 ω (by norm_num [instK])
1588 example (ω) : <full conclusion written out> := grid_expansion_all sz0 0 … 0 (fun _ => 3) 4 ω (by norm_num [instK])
1610 grid_expansion at k = 4 = K
1618 example : <full conclusion written out> := condExp_A_succ sz0 0 … 0 0 inst_E (inst_s0 0) (inst_st 0) (inst_K 0) (j=0<4) (u_1 = 1/5 < 1)
1637/1642 _of_lt_one, _rpow;  1653-1691 bridge lemmas (hΦ from merged hermTestFun_loopPM at u = 1/10)
1699-1719 all five `_at` forms;  1704/1709 grid_expansion'(_all')
1724 grid_expansion_all_at at s = 0;  1729 at s = t = 1/2 (Δ = 0);  1734 condExp_A_succ at s = 0, t = 99/100, j = 3;  1739 at Δ = 0
```
Every deterministic hypothesis is discharged by `norm_num`/named lemmas; no premise is left open. Nondegenerate: `N = 2097152`, `K = 4`, `min k τ = 3 > 0`, window `[1/10, 1/2] ⊂ [0,1)`; DECISIONS §29 boundary cases also compile. `Avec`, `martInc` are defs occurring in 1567/1588.

## 5. Paper-delta coverage (round 1's gap)
```
$ grep -n "T2098[a-z]" docs/reports/T2098-prove.md | cut -c1-120
269:- `T2098a` (pin form, not a mathematics change): `StoppedDuhamel105`, `grid_expansion_all`, ... carry `∀ n` hypotheses
270:- `T2098b` (vocabulary): `Avec`, `Dgrid` are defined through the merged `STLKM`, `STELKLKM`, `STEGtM` at `σ = (+,-)`; ...
272:- `T2098c` (statement form of (int_K-L_ST)): `StoppedDuhamel105`/`stoppedDuhamel105`, `grid_expansion(_all)`, ...
273:- `T2098d` (Lean-only statement): `condExp_A_succ` (and `Expansion_condExp_A_succ_of_lt_one`, `Expansion_condExp_A_succ_rpow`) ...
274:- Correction of section (a), "Verdict per target", last line ("Paper-delta candidate `T2098a`: none expected"): wrong; ...
$ sed -n 134,139p paper/tex/3_5_Loop_Hierarchy.tex | cut -c1-110
\begin{lemma}[Integrated loop hierarchy, Lemma 5.3 of \cite{YY_25}] \label{Sol_CalL}
First, \eqref{eq_L-Keee} is equivalent to the integral equation: for any stopping time $\tau\ge s$ with respect to
\begin{align}\label{int_K-L_ST}
({\cal L}-{\cal K})^{(n)}_{\tau,\bsig,{\ba}}&=({\cal L}-{\cal K})^{(n)}_{s,\bsig,{\ba}}+\int_{s}^{\tau}\p{\varTheta^{(n)}_
```
- `T2098c` states the grid (time-discrete), pathwise, stopped-at-index form of `(int_K-L_ST)` (`3_5:134-139`), `n = 2`, `σ = (+,-)`, `τ` any function, increments `predInc + martInc` / `Δ·Dgrid + Rgrid + martInc` / `Zvec + Yvec + Δ·Dgrid + Rgrid` replacing `∫ du` and `∫ dE^M`; cites D21, D162. Matches the Lean statements of §2.
- `T2098d` states `condExp_A_succ` (+ `_of_lt_one`, `_rpow`) is Lean-only, with the remainder `envConst d L W E 2 u_{j+1} Δ^{3/2} + 7 N η_{u_{j+1}}^{-4} Δ^2`, `N = (WL)^d`; cites D151, D159. Matches the Lean signature verbatim above.
- `T2098a` (`∀ n` pin form, `_at` forms) and `T2098b` (merged `ST*` vocabulary, `Zd×Zd` vs `Fin 2 → Zd` shape) cover the remaining differences. The section (a) "none expected" line is corrected in (d) (line 274), without editing (a).
Every Lean/paper statement difference found in §2 is now covered.

## 6. Verdict per target
| target | statement | hidden/vacuity/cycle | instance | build/axioms | paper delta | verdict |
|---|---|---|---|---|---|---|
| `Avec`, `martInc` (`predInc`) | = RBM2D after renaming | none | used in 1567/1588 | OK | T2098b | PASS |
| `StoppedDuhamel105`, `stoppedDuhamel105` (+`_at`) | = RBM2D after renaming | none | 1567, 1699 | OK | T2098a, c | PASS |
| `grid_expansion_all` (+ `grid_expansion`, `'`, `_at`) | = RBM2D up to cast, `Uop` vocab | none | 1588, 1610, 1704-1729 | OK | T2098a, c | PASS |
| `condExp_A_succ` (+ `Dgrid`, `Rgrid`, `_of_lt_one`, `_rpow`) | `N = (WL)^d`, class b | none | 1618, 1637, 1642, 1734, 1739 | OK | T2098d | PASS |
| bridge (`stepZ_*`, `stepXi_*`, `stepY_*`, `Zvec`, `Yvec`, `Expansion_uop_martInc_eq*`) | vocab only | `hΦ` discharged | 1653-1691 | OK | T2098b | PASS |

**Overall: PASS.** No dispatcher sign-off needed.

## 7. Observations (no verdict effect)
- O1. Public names `stoppedDuhamel105_at`, `grid_expansion_all_at`, `grid_expansion_at`, `grid_expansion'_at`, `grid_expansion_all'_at` are not in RBM2D, not pinned and not `Expansion_`-prefixed (CLAUDE.md §3 (E)); no clash on main (grep above). They are DECISIONS §29 (4) forms; the dispatcher may keep or rename them.
- O2. The portmap row (`T2039-portmap.md:125`) lists `Path/UBounds` as a dependency; the ticket omitted it, and the file re-proves those helpers as private `Expansion_*` (duplicating T2097 content once that merges).
- O3. The branch base is c5bbae7; main is at 9bb2cbe (T2095). No file overlap; the hub's full build at merge is the check.
