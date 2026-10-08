Auditor model: claude-opus-5-5

# T2303 audit (round 1): BA-L2b1 `Graph/BAExpandW` (`BAlweight`, `lanlw` as a graph operation)

Audit time (`date -u`): Thu Oct  8 02:53:31 UTC 2026. Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2303-audit1`,
detached at `t/T2303` = `faea938`. Scratch: scratchpad `T2303/` (`eq.py`, `ax.lean`, `check_b.lean`, `reg.lean`).

## 1. Diff scope, imports, forbidden tokens

$ git diff --name-only main...t/T2303; git diff main...t/T2303 -- RBM3D/Test/Axioms.lean RBM3D.lean | wc -l
```
RBM3D/Graph/BAExpandW.lean
       0
```
$ git diff main...t/T2303 | grep -nE '^\+.*\b(sorry|admit|native_decide|axiom)\b'; echo $?
```
1            (no hit)
```
$ sed -n 6,7p RBM3D/Graph/BAExpandW.lean; wc -l < RBM3D/Graph/BAExpandW.lean
```
import RBM3D.Graph.BAExpand
import Mathlib.LinearAlgebra.Matrix.Gershgorin
    1066
```
Imports exactly as the ticket pins; no `import RBM3D`; no merged file touched (§57 (1)); 1066 < 1500 (stop rule not hit).

## 2. Build and axioms

$ lake build RBM3D.Graph.BAExpandW > build.log 2>&1; echo "exit $?"; grep -E '^error|BAExpandW' build.log; tail -1 build.log
```
exit 0
Build completed successfully (3779 jobs).
```
(`BAExpandW.olean` produced by this build in the audit worktree; main's cache has no `BAExpandW` olean.)
$ lake env lean RBM3D/Graph/BAExpandW.lean (fresh elaboration, non-linter lines) ; exit
```
exit 0       (no error lines)
```
$ lake env lean ax.lean  (`#print axioms` of all 34 public declarations of the file)
```
exit 0
33 lines: depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.BAExpandW_lab2_emb' depends on axioms: [propext, Quot.sound]
```
$ registry pre-check: `import RBM3D` + `import RBM3D.Graph.BAExpandW` + `#assert_rbm_axioms`, `lake env lean reg.lean`
```
axiom audit: 9006 theorems, 2935 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
All within [propext,
 Classical.choice,
 Quot.sound]; no project axioms: ...
exit 0
```
No registry line needed (`RBM3D/Test/Axioms.lean` unchanged), as the ticket expects.

## 3. Statements against the pin (check file sections 2–4)

$ python3 -I eq.py T2303-check.lean BAExpandW.lean  (check text between `namespace RBM.Graph.T2303Check` and `/-! ## 4.`,
split at the `## 3.` header; each part, and the section-4 graph definitions, searched whitespace-normalized in the file)
```
check part 0 chars 1594 found in lean: True      (section 2: BAlweightL, BAlweightR, BAlweight)
check part 1 chars 3030 found in lean: True      (section 3: BAlwData, lanlwExt, lanlwT1, lanlwD, lanlwTerms)
baGcxy found in lean: True
baGcxx found in lean: True
```
$ lake env lean check_b.lean  (check file verbatim + `import RBM3D.Graph.BAExpandW` + the examples below)
```lean
example : RBM.Graph.T2303Check.T2303_baM_row_sq :=
  fun d L W _ _ g0 E m h x => RBM.Graph.baM_row_sq d L W g0 E m h x
example : RBM.Graph.T2303Check.T2303_baW_isUnit :=
  fun d L W _ _ hL g0 E t m h h0 h1 => RBM.Graph.baW_isUnit d L W hL g0 E t m h h0 h1
example : RBM.Graph.T2303Check.T2303_baLweight_holds := fun d => RBM.Graph.baLweight_holds d
example : RBM.Graph.T2303Check.T2303_lanlw_val :=
  fun d L W _ _ hL g0 E t m hS h0 h1 _ _ _ _ Γ p hp hσ hc ℓe =>
    RBM.Graph.lanlw_val d L W hL g0 E t m hS h0 h1 Γ p hp hσ hc ℓe
example : @RBM.Graph.T2303Check.BAlweight = @RBM.Graph.BAlweight := rfl
example : @RBM.Graph.T2303Check.BAGraph.lanlwTerms = @RBM.Graph.BAGraph.lanlwTerms := rfl
example : @RBM.Graph.T2303Check.BAlwData = @RBM.Graph.BAlwData := rfl
example : RBM.Graph.T2303Check.baGcxy = RBM.Graph.baGcxy := rfl
example : RBM.Graph.T2303Check.baGcxx = RBM.Graph.baGcxx := rfl
```
```
exit 0        (no error lines)
```
`baM_symm` (no hypothesis) and `baW_mul` (`hL`, `BASelf`, `0 ≤ t < 1`) are not pinned as section-4 texts; their
statements match the ticket's words (`BAlwM x α = BAlwM α x`; `BAlwW * (1 − M⁺S) = 1`).

Against the paper (`B:376-387`, `(eq:LW)`): `BAlweightL = Ǧ_{xx} f`; `BAlweightR = Σ_y W_{xy}(Σ_{α,β} M_{yα}S_{αβ}Ǧ_{αy}Ǧ_{ββ}f −
Σ_{α,β} M_{yα}S_{αβ}G_{βy}∂_{h_{βα}}f)` with `W = BAlwW = Ring.inverse (1 − M⁺S)`, `M⁺_{xy} = M_{xy}M_{yx}` (`BAlwMp`,
`B:388`): term by term. Quantifiers: fixed `L W`, `3 ≤ L`, `g0 E t m`, `BASelf`, `0 ≤ t < 1`, then `P`, `x`; no `∀ᶠ`,
no constants, no L–W relation. `lanlwT1` = `Σ M_{xα}S_{αβ}Ǧ_{ββ}G_{αy}` (`(eq:BE)` term 1); `lanlwD` = the derivative
term with `+Γ.coeff` (`−` of `(eq:BE)` times `∂_{h_{βα}}G_{ab} = −G_{aβ}G_{αb}`); the sign and orientation are
machine-checked, since `lanlw_val` is proved from the merged `BAExpand_integral`.

## 4. Hidden hypotheses, vacuity, cycles

- `baLweight_holds (d : ℕ) : BAlweight d` and `lanlw_val` carry all hypotheses in their signatures; `gaussIBP`
  discharged (axioms above). `BALData` (BAVocab.lean:39) extends `LData` with the data field `gPsi` only: no
  Prop field. `BASelf` (MFixedPoint.lean:193) = `0 < m.im ∧ m = L^{-d} tr BAMB`: the paper's `(self_m)`, satisfiable
  (merged `BAExpandInst.baSelf_zero : BASelf 3 3 0 0 i`).
- No cycle: the file imports only merged `RBM3D.Graph.BAExpand` and Mathlib. No external hypothesis is introduced,
  so no limit check is needed.
- Name clash (`grep -rnw` of the 17 public non-prefixed names as `def/theorem` heads over `RBM3D/` outside `Probe/`
  and this file; plus `BAExpandW` occurrences elsewhere): every count `0`. Unpinned helpers are `private` or
  `BAExpandW_`-prefixed (§3 (E)).

## 5. Compiled nonempty instances (all compiled in the build of §2; `grep -c '^example'` = 8)

| endpoint | instance (BAExpandW.lean) | data | open hypotheses |
|---|---|---|---|
| `baLweight_holds` | example `:1007` | `d=3,L=3,W=1` (N=27), `g0=0,E=0,m=i,t=1/2`, `x=0`, `P=X(true,e₀,0)·X(false,e₀,0)` | none (`baSelf_zero`, `norm_num`) |
| `baLweight_holds` | example `:1017` | `g0=1/2,E=3/10,t=1/2`, `x=e₀`, `P=X(true,e₀,0)` | `hSelf` only (allowed by the ticket at `g0 ≠ 0`) |
| `baLweight_holds` (t=0) | `baLweight_t0` `:992` | `t=0`: both sides `= 0` and equal | `hSelf` (a theorem, not the endpoint instance) |
| `baW_isUnit` | example `:1028` | (I6) data `g0=0,E=0,m=i,t=1/2` | none |
| `baW_mul`, `baM_row_sq`, `baM_symm` | examples `:1032/:1036/:1039` | same | none |
| `lanlw_val` on `baGcxy` | example `:1044` | same model data, `x=0 ≠ y=e₀`, `p` = the edge of `baGcxy` (`simp [lwSplit]`, `rfl rfl`) | none |
| `lanlw_val` on `baGcxx` | example `:1055` | same, internal `x` summed over `Idx 3 3 1` | none |

None degenerate: `N = 27`, `t = 1/2 ∈ (0,1)`, non-empty index types, nonzero `P`.

## 6. Paper deltas

Prove report (d) proposes `T2303a` (`1 + M⁺S⁺` read as the fine-lattice `(1 − M⁺S)⁻¹` with `S = t·svarF`, vs the
paper's block-level `Θ^{(+,+)}`), `T2303b` (`f` a resolvent polynomial, not a general differentiable `f`; cf. existing
D57/T2040d lineage), `T2303c` (`lanlw_val` only for a blue circled `p.1`; red case not stated). These cover every
Lean/paper difference found here. Also `baM_symm` is unconditional (stronger than needed): no delta required.

## 7. Observations (no RETURN)

- O1. The fully discharged instances use `g0 = 0` (`M = i·1` diagonal, `M⁺S = −S`); this is
  the data the ticket pins for (I5)–(I6); the `g0 = 1/2` example keeps `hSelf` as the ticket allows.
- O2. The prove report's preflight cites `1_2_Intro_model_result.tex:658-664`; not needed for any statement here.

## Verdict

| target | verdict |
|---|---|
| 1 `BAlweight` (pin), `baM_row_sq`, `baM_symm`, `baW_isUnit`, `baW_mul`, `baLweight_holds` | PASS |
| 2 `BAlwData`, `lanlwExt`, `lanlwT1`, `lanlwD`, `lanlwTerms` | PASS |
| 3(b) `lanlw_val` | PASS |
| (I5), (I6), two `lanlw_val` applications | PASS |

**T2303: PASS.** No dispatcher sign-off needed. Hub: add `import RBM3D.Graph.BAExpandW` after the last `import` of
`RBM3D.lean` at merge.
