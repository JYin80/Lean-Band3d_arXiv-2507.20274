Auditor model: claude-opus-5-5

# T2085 audit, round 2 (ST2-24: `Path/Kernel`, `Path/StepDecompLoop`)

Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2085-audit2`, detached at `t/T2085` = `042dae0`. Written Sat Oct  3 23:54:43 UTC 2026.
Scratch: `scratchpad/T2085/` (`sdiff.py`, `ax2.lean`, `ax2.out`, `build2.log`). Round-1 RETURN was paper-delta coverage only (D1–D3) plus a stale docstring tag.

## 0. Repair delta since round 1
```
$ git diff --stat 1a3d1b3 042dae0
 RBM3D/Path/StepDecompLoop.lean | 2 +-
$ git diff 1a3d1b3 042dae0     (the only hunk, docstring of stepDecomp_loopPM, :691)
-`T2080a`); the fifth conjunct is `stepDecomp_Y_sq` (candidate `T2080b`). -/
+`T2085f`); the fifth conjunct is `stepDecomp_Y_sq` (candidate `T2085f`). -/
```
Comment-only; no statement, proof or instance changed.

## 1. Statements (script diff against the pin = RBM2D `c9a24cf` under the ST1-COMMON renaming)
`sdiff.py` extracts every `theorem`/`def` statement (up to `:=`) of RBM2D `Path/{Kernel,StepDecompLoop}.lean` at `c9a24cf`
(`git show c9a24cf:…`) and of `t/T2085`, applies the renaming map (`Z2 L → Zd d L`, `Theta L/SB L → Theta d L g/SB d L g`,
`(d : Sizes) → {d : ℕ} (sz : Sizes d)`, `gloop … (pmLoop a.1 a.2) → loopPM d (sz.L n) (sz.W n) E u M a.1 a.2`,
`ukerMat (d.L n) → ukerMat d (sz.L n) (sz.lam n)`, `spectralM → mE`), and compares token streams:
```
$ python3 sdiff.py
== k2.lean vs k3.lean: RBM2D public 17, RBM3D public 17; only-2D []; only-3D []
ukerMat / Uop / UopSemigroup / ukerMat_mul / ukerMat_self / Uop_add / Uop_smul / Uop_self / Uop_comp /
UopHom / uopSemigroup / duhamel_telescope / duhamel_telescope_stopped / Uop_grid_semigroup / Uop_factor /
Uop_duhamel_telescope / Uop_duhamel_telescope_stopped: IDENTICAL after renaming      (17 lines, joined)
== s2.lean vs s3.lean: RBM2D public 4, RBM3D public 4; only-2D []; only-3D []
hermTestFun_loopPM / loopPM_real_of_herm / stepDecomp_loopPM / stepDecomp_Z_subG_loopPM: IDENTICAL after renaming
```
Read against the paper (signatures only):
- `ukerMat ξ v w = (1 - vξ SB d L g) * Theta d L g (wξ)` (`Kernel.lean:46`), `Uop` the two-slot product (`:51`): `(def_Ustz)`
  (`3_5_Loop_Hierarchy.tex:116`, Definition `DefTHUST` `:109`) at `n = 2`, `σ = (+,-)`, `ξ = |m|²` (`Complex.normSq (mE E)` at the use sites).
- `UopSemigroup` (`:56`): `3 ≤ L → ∀ ξ, ‖ξ‖ ≤ 1 → ∀ u v w, 0 ≤ u ≤ v ≤ w < 1 → (semigroup) ∧ (𝒰_{u,u} = id)`; DECISIONS §29
  window: `0 ≤ u`, `w < 1` both present. Proved unconditionally by `uopSemigroup` (`:173`).
- `Uop_duhamel_telescope(_stopped)` (`:292`, `:311`): `hL`, `‖ξ‖ ≤ 1`, `0 ≤ u j < 1` for `j ≤ m`; any `A`. Discrete grid telescope.
- `stepDecomp_loopPM` (`StepDecompLoop.lean:692`): `0 ≤ u < 1`, `|E| < 2`, `0 ≤ v ≤ w < 1`, `0 ≤ gridStep`; `C₂ = 6 N η_u⁻⁴`,
  `N = (WL)^d`; no `d = 2` exponent remains in any statement. Quantifier/parameter order unchanged from the pin.
No special case passed off as general beyond what the pin itself is; the restrictions are now covered as paper deltas (§5).

## 2. Vacuity, hidden hypotheses, cycles
- Only `Prop`-valued def: `UopSemigroup`, proved outright by `uopSemigroup` and used as a hypothesis nowhere.
- `HermTestFun` (merged T2073) appears only as a conclusion; `stepDecomp_Z_subG_loopPM`'s `hbound` is explicit and discharged in §3.
- No external hypothesis (nothing to limit-check). Imports, all merged or in this ticket, no cycle:
```
$ grep ^import RBM3D/Path/StepDecompLoop.lean RBM3D/Path/Kernel.lean
StepDecompLoop: Mathlib.Analysis.CStarAlgebra.Hom, RBM3D.Path.StepDecomp, RBM3D.Path.Kernel, RBM3D.Gauss.FlowCalculus, RBM3D.Green.Pins
Kernel:         RBM3D.Propagator.Props4
```

## 3. Compiled nonempty instances (same files; all compile in §4)
| endpoint | instance | data / hypotheses discharged |
|---|---|---|
| `uopSemigroup` / `UopSemigroup` | `Kernel.lean:325`, `:329` | d=3, L=3, g=1/2, ξ=1, (u,v,w)=(1/4,1/2,3/4); `3≤3`, `‖1‖≤1`, order, `w<1` by `norm_num` |
| `Uop_duhamel_telescope` | `Kernel.lean:337` | d=3, L=3, ξ=1, `u j = j/(j+2) ∈ [0,1)` by `positivity`, `div_lt_one`; any `m`, `A` |
| `Uop_duhamel_telescope_stopped` | `Kernel.lean:349` | same grid; arbitrary `τ`, `ω`, `k` |
| `ukerMat_self`, `ukerMat_mul` | `Kernel.lean:365`, `:368` | d=3, L=3, ξ=1; `‖vξ‖<1` by `norm_num` |
| `hermTestFun_loopPM` | `StepDecompLoop.lean:920` | private `Sizes 3` (`:824`: `L n=n+3`, `W n=n+2`, `lam=1/2`), n=0 ⇒ L=3, W=2, N=216; E=0, u=1/2 |
| `loopPM_real_of_herm` | `:924` | same sizes, `M = 1` (Hermitian) |
| `stepDecomp_loopPM` | `:931` | s=1/4, t=3/4, K=2 ⇒ Δ=(t−s)/K=1/4 (`Walk.lean:67`); j=0, v=1/4, w=1/2; all hypotheses by `norm_num` |
| `stepDecomp_Z_subG_loopPM` | `:940` (private named check) | `S = univ`, `c` from `StepDecompLoop_exists_variance_bound`; `hbound` discharged |

No `N = 0`, empty index, collapsed window (`s < t`, `v < w`), `False` premise, or large witness. No other gate's pin is assumed.

## 4. Build, axioms, hygiene, diff
```
$ lake build RBM3D.Path.Kernel RBM3D.Path.StepDecompLoop > build2.log 2>&1      # audit worktree
exit=0
✔ [3360/3360] Built RBM3D.Path.StepDecompLoop (4.6s)
Build completed successfully (3360 jobs).
$ grep -E "^(error|warning)" build2.log | grep -E "Kernel|StepDecompLoop"; grep -c error build2.log
0                       (warnings present are in merged Walk.lean / Markov.lean only)
$ lake env lean ax2.lean     # #print axioms of the 22 public names
exit=0
$ sed 's/.*depends on axioms: //' ax2.out | sort | uniq -c
  22 [propext, Classical.choice, Quot.sound]
$ grep -nE "\bsorry\b|\badmit\b|native_decide|^\s*axiom|private axiom" RBM3D/Path/Kernel.lean RBM3D/Path/StepDecompLoop.lean
(no output; exit 1)
$ git diff --name-only main...t/T2085
RBM3D/Path/Kernel.lean
RBM3D/Path/StepDecompLoop.lean
```
Both files new and sole-writable; `RBM3D/Test/Axioms.lean` untouched (no registrable `Prop` hypothesis); no frozen signature touched.

## 5. Paper-delta coverage
Prove report §(d) and its "Repair" section now propose T2085a–T2085f:
- T2085a `(d, L, g)` parameters; T2085b `W^{-2d}` in the proof, `C₂ = 6Nη⁻⁴`, `N=(LW)^d`; T2085c private `ukerNonneg` copy.
- T2085d (round-1 D1): `ukerMat`/`Uop`/`UopSemigroup`/`Uop_*` = `(def_Ustz)` only at `n = 2`, single `ξ`, `σ = (+,-)`.
- T2085e (D2): `(Uop_)duhamel_telescope(_stopped)` are the discrete grid telescope; paper `(int_K-L_ST)`/`(int_K-LcalE)` are the
  continuous Duhamel formulas with the `𝒦∼(𝓛−𝒦)`, `𝓔` and martingale integrals.
- T2085f (D3): `stepDecomp_loopPM`, `stepDecomp_Z_subG_loopPM` are Lean-only time-discretization statements; `Σ U` for `Σ |U|` under
  `0 ≤ v ≤ w < 1`; the `L²` conjunct.
Paper labels cited by T2085d/e exist at the stated lines; none of the tags is already in `docs/paper-deltas.md`:
```
$ grep -nE "label\{(def_Ustz|DefTHUST|int_K-L_ST|int_K-LcalE|Sol_CalL)\}" paper/tex/3_5_Loop_Hierarchy.tex
109:\begin{definition}[Evolution kernel]\label{DefTHUST}
116:    \begin{align}\label{def_Ustz}
134:\begin{lemma}[Integrated loop hierarchy, Lemma 5.3 of \cite{YY_25}] \label{Sol_CalL}
136:\begin{align}\label{int_K-L_ST}
144:\begin{align}\label{int_K-LcalE}
$ grep -nE "T2085|def_Ustz|int_K-L_ST|int_K-LcalE" docs/paper-deltas.md
(no output; exit 1)
```
Every Lean/paper statement difference found in round 1 (D1–D3) and in this round is now covered by a candidate.

## 6. Observations (no RETURN)
- O1. Instances use a private `Sizes 3` (`L=3`, `W=2`) rather than the merged `sz0`/T2039 probe data; §4 step 2 is met at d = 3.
- O2. The docstring of `stepDecomp_loopPM` cites `T2085f` for both the `Σ U` and the `L²` points (both are D3); fine once numbered.
- O3. `Uop_duhamel_telescope`'s docstring "the algebraic part of (105)" is now matched by candidate T2085e.

## 7. Verdict
| target | statement | vacuity/hidden/cycle | instance | build/axioms | paper deltas | verdict |
|---|---|---|---|---|---|---|
| `ukerMat`, `ukerMat_self`, `Uop`, `uopSemigroup` (+ `Uop_*`) | pass | pass | pass | pass | T2085a,d | PASS |
| Duhamel telescope (`(Uop_)duhamel_telescope(_stopped)`) | pass | pass | pass | pass | T2085d,e | PASS |
| `stepDecomp_loopPM` (+ `hermTestFun_loopPM`, `loopPM_real_of_herm`, `stepDecomp_Z_subG_loopPM`) | pass | pass | pass | pass | T2085b,f | PASS |

**Ticket verdict: PASS.** No dispatcher sign-off needed.
