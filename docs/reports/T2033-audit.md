Auditor model: claude-opus-5-5

# T2033 audit (round 1) — Sat Oct  3 15:43:52 UTC 2026

Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2033-audit1`, detached at `t/T2033` = `22d4235` (merge-base with main `eb6d67a`). `$S` = `<scratchpad>/T2033/audit`. Ticket pin: port RBM2D `Induction/Split.lean` at `c9a24cf`; each ported public statement equals RBM2D's after renaming and exponents (ST1-COMMON item 6). No dispatcher check file exists for this port ticket; the statement reference is the RBM2D source.

## 1. Statements (RBM2D c9a24cf vs RBM3D, independent script)

`$S/sd.py`: comments stripped, every non-private `theorem|lemma|def|abbrev` (with `@[...]` attributes) cut at `:=`/`|`, whitespace normalized. Renaming applied to the 2D text: `BlockIndex L W→Vtx d L W`, `Z2 L→Zd d L`, `gloop L W→loopL d L W`, `\bGsig\b→Gres`, `LoopIdx (→Loop.LoopIdx (`, `{L :→{d L :`, `(W : ℝ)⁻¹ ^ 2→((W : ℝ) ^ d)⁻¹`, `(gchain|Eblk|gloopProd|loopMax|loopXi) L W→… d L W`.
```
$ git -C ../RBM2D --no-optional-locks show c9a24cf:RBM2D/Induction/Split.lean > $S/split2d.lean
$ python3 $S/sd.py $S/split2d.lean $S/split3d.lean
2D public: 56  3D public: 56
missing in 3D: []
extra in 3D: []
identical after renaming: 56
```
Section variables (2D :171/191/233/243/319/441/449/611/647 vs 3D :181/201/302/312/388/510/518/677/712): same binders with `{d L W}` for `{L W}`; `[NeZero L]`, `[NeZero W]` (OpNorm section only) as in RBM2D. Definitions used by the targets (3D file, merged deps):
```
Split:185  def bw (b : Zd d L) (p : Vtx d L W) : ℝ := if p.1 = b then ((W : ℝ) ^ d)⁻¹ else 0
Split:515  def loopMax H z n := ⨆ x : (Fin n → Bool) × (Fin n → Zd d L), ‖loopL d L W H z ⟨List.ofFn x.1, List.ofFn x.2⟩‖
Split:421  def symIdx σ a b' b := ⟨σ ++ (σ.map (!·)).reverse, (a ++ [b']) ++ (a.reverse ++ [b])⟩
GLoop:55   def Eblk a := Matrix.diagonal fun x => if x.1 = a then ((W : ℂ) ^ d)⁻¹ else 0
GLoopFlow:123 def loopL H z I := Matrix.trace ((I.σ.zip I.a).foldr (fun p M => Gres H z p.1 * Eblk d L W p.2 * M) 1)
Model:60   abbrev Vtx : Type := Zd d L × Fin (W ^ d)
```
The four targets (text at `Split.lean:598/700/757/454`, as in the prove report (b), re-read): `loopMax_odd_sq_le` (hH, `1 ≤ m`; `L^{2m+1}` max squared ≤ product of `2m`, `2m+2`), `split_norm_trace_mul_Eblk_le` (`‖tr(M E_b)‖ ≤ ‖M‖`, ℓ² operator norm), `norm_gloop_le_of_le_abs_im` (hH, `0<η ≤ |Im z|`, `σ.length = a.length ≥ 1`; bound `η⁻ⁿ (W^{-d})^{n-1}`), `norm_gloop_symIdx_split_le` (hH, `σᵢ.length = aᵢ.length + 1`). The single exponent change `W⁻² → W^{-d}` is the block weight of the merged `Eblk` (`‖E_b‖ = W^{-d}`, `tr E_b = 1`); the bound `η⁻ⁿ W^{-d(n-1)}` is the correct d-dimensional one (n resolvents, n−1 blocks bounded in operator norm, one absorbed by the trace). d = 2 leftover scan:
```
$ for p in '⁻¹ \^ 2' 'W \^ 2' Z2 BlockIndex 'Gsig H' 'gloop L W' 'Fin W × Fin W' pow_two; do grep -nE "$p" RBM3D/Induction/Split.lean; done
(no output for any pattern)
```

## 2. Vacuity, hidden hypotheses, cycles

- Targets take only `H.IsHermitian`, numeric/length hypotheses; no structure-valued or `Prop`-def hypothesis; `grep -cE "^def .*Prop|: Prop :=" Split.lean` → `0` (no registry line needed).
- Imports (`Split.lean:6-10`): `RBM3D.Loop.GLoopFlow`, `RBM3D.Gauss.FlowCalculus` (S1-01, merged), Mathlib. No ST-2…ST-6 import, no `import RBM3D`. Reused merged lemmas: `norm_Gsig_le_inv_eta` (FlowCalculus:644, `0<η`, `η ≤ |z.im|`), `norm_Eblk_le_inv_W_sq` (:663), `norm_matrix_entry_le_opNorm` (:591). No circular dependency.
- No external hypothesis (all targets deterministic), so no limit check applies.

## 3. Compiled nonempty instances (`Split.lean` section `Checks`, :897-1095)

Data: `d = 3, L = 3, W = 2` (`N = 216`, block `8`), `H = 0` (Hermitian by `Matrix.isHermitian_zero`), `z = i`, `η = 1 = |Im z|`.
```
:1006 check_odd_sq_le             := loopMax_odd_sq_le Matrix.isHermitian_zero le_rfl            (m = 1)
:1022 check_trace_mul_Eblk_le     := split_norm_trace_mul_Eblk_le _ _                             (M = 1, b = 0)
:1035 check_gloop_le_of_le_abs_im := norm_gloop_le_of_le_abs_im Matrix.isHermitian_zero one_pos (by simp) _ rfl (by simp)   (n = 4)
:1056 check_symIdx_split_le       := norm_gloop_symIdx_split_le Matrix.isHermitian_zero rfl rfl 0 0 0   (σ₁ = σ₂ = [true])
```
Every hypothesis discharged by term; no hypothesis left open. Nondegeneracy proved in the same file: `check_odd_sq_le_values` (loopMax₃ = 1/64, loopMax₂ = 1/8, loopMax₄ = 1/512), `check_trace_mul_Eblk_ne_zero` (LHS = 1), `check_gloop_attained` (loop = 1/512 = the bound), `check_symIdx_split_values` (1/512 and 1/8), `check_loopMax_formula` (`loopMax n = (2⁻³)^{n-1} > 0`, all `n ≥ 1`). No `N = 0`, empty index, collapsed window or `False` premise; values are small explicit rationals.

## 4. Build, axioms, hygiene, diff

```
$ cd /Users/junyin/Lean_proof/RBM3D-wt/T2033-audit1 && lake build RBM3D.Induction.Split 2>&1 | grep -iE "error|warning"; tail -1
Build completed successfully (3297 jobs).
$ sed '$d' Split.lean > $S/axcopy.lean; append #print axioms <13 names>; end RBM.Ind; lake env lean $S/axcopy.lean
'RBM.Ind.loopMax_odd_sq_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Ind.split_norm_trace_mul_Eblk_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Ind.norm_gloop_le_of_le_abs_im' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Ind.norm_gloop_symIdx_split_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'_private._stdin.0.RBM.Ind.check_odd_sq_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'_private._stdin.0.RBM.Ind.check_trace_mul_Eblk_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'_private._stdin.0.RBM.Ind.check_gloop_le_of_le_abs_im' depends on axioms: [propext, Classical.choice, Quot.sound]
'_private._stdin.0.RBM.Ind.check_symIdx_split_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'_private._stdin.0.RBM.Ind.check_odd_sq_le_values' depends on axioms: [propext, Classical.choice, Quot.sound]
'_private._stdin.0.RBM.Ind.check_gloop_attained' depends on axioms: [propext, Classical.choice, Quot.sound]
'_private._stdin.0.RBM.Ind.check_symIdx_split_values' depends on axioms: [propext, Classical.choice, Quot.sound]
'_private._stdin.0.RBM.Ind.check_loopMax_formula' depends on axioms: [propext, Classical.choice, Quot.sound]
'_private._stdin.0.RBM.Ind.check_trace_mul_Eblk_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
exit 0
$ grep -nE "\bsorry\b|\badmit\b|native_decide|^axiom|^\s*axiom |implemented_by|extern|unsafe|set_option" Split.lean; echo $?
1
$ git diff --name-only main...t/T2033
RBM3D/Induction/Split.lean
$ git diff --stat eb6d67a main -- 'RBM3D/*.lean' RBM3D.lean      # main since the branch base: new files only
 RBM3D.lean | 4 +; Gauss/LoopCoordinate.lean, Graph/LWPsi.lean, Green/LDEQuadT.lean, Induction/Contract.lean (new)
$ printf 'import RBM3D\nimport RBM3D.Induction.Split\n#assert_rbm_axioms\n' > $S/registry.lean; lake env lean $S/registry.lean   # main's root (461ae86) + Split
axiom audit: 2052 theorems, 847 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
exit 0
```
No frozen signature touched (only a new file). Registry pre-check with main's current root passes, so no duplicate declaration with the four modules merged after the branch base (`Contract.lean`'s private `Gres_conjTranspose` and Split's private copy do not collide).
Name check: `git grep -nE "def loopMax" main -- 'RBM3D/*.lean'` → `RBM3D/Loop/GLoop.lean:102` in `namespace RBM.Gauss` (different full name from `RBM.Ind.loopMax`); no other new public name is declared in main.

## 5. Paper deltas

Lean/paper differences, all proposed in prove report (d): `T2033a` (loop-level forms of the d = 2 paper's (5.114)–(5.118), (6.4); this paper only cites "(5.118) in [YY_25]" at `3_5_Loop_Hierarchy.tex:1841` for `eq:boundtwochains`, which is not stated here); `T2033b` (`loopMax`/`loopXi` deterministic at fixed `(H, z)`, free `A ≥ 0`, versus the paper's random `Ξ^{(L)}_{v,m}` with `A = λ² W^d`); `T2033c` (shared short name `loopMax`). Verified: `grep -n "5\.118\|boundtwochains" paper/tex/*.tex` → `3_5:1841`, `:1842`, `:1856` only. Coverage complete.

## Verdicts

| Target | Statement | Hidden hyp./cycle | Instance | Build/axioms | Deltas | Verdict |
|---|---|---|---|---|---|---|
| `loopMax_odd_sq_le` | = RBM2D after renaming | none | `check_odd_sq_le`, nonzero values | ok | T2033a/b | PASS |
| `split_norm_trace_mul_Eblk_le` | = RBM2D after renaming | none | `check_trace_mul_Eblk_le`, LHS = 1 | ok | T2033a | PASS |
| `norm_gloop_le_of_le_abs_im` | = RBM2D, `W⁻² → W^{-d}` | none | `check_gloop_le_of_le_abs_im`, attained | ok | T2033a | PASS |
| `norm_gloop_symIdx_split_le` | = RBM2D after renaming | none | `check_symIdx_split_le`, nonzero | ok | T2033a | PASS |

Overall: **PASS**. No dispatcher sign-off needed.

## Observations (no verdict effect)

- O1: the file has `open Matrix RBM.Gauss` and declares `RBM.Ind.loopMax` next to `RBM.Gauss.loopMax`; the module builds, but consumers (S1-18, S1-31, S1-35, S1-36) that open both namespaces must qualify the name (`T2033c`, dispatcher's naming decision).
- O2: the instances use `H = 0`, `z = i` (all values explicit and nonzero, one bound attained); the random 216×216 check in (a)(ii) is numeric only. This is enough for §4 step 2.
- O3: the prove report's (b) statement-diff script lists two residual lines that are artifacts of its own renaming; the independent script above finds 56/56 identical.
