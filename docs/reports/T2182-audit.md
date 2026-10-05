Auditor model: claude-opus-5-5

# T2182 audit, round 1 (S5-25 `Evolution/CltFar`, pin `STCltFar`): Mon Oct  5 07:25:27 UTC 2026

Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2182-audit1`, detached at `t/T2182` = `5b9f637` (base `a52eb85`).
Scratch: scratchpad `T2182/` (`pin.txt`, `lean.txt`, `build.out`, `deps.out`, `Precheck.lean`, `precheck.out`, `pre0.out`).

## 1. Files touched and frozen signatures
```
$ git diff --stat main...t/T2182
 RBM3D/Evolution/CltFar.lean | 1958 +++++++++++
 RBM3D/Test/Axioms.lean      |    1 -
$ git diff main...t/T2182 -- RBM3D/Test/Axioms.lean | grep '^[-+]'
-   `RBM.Gauss.Sizes.STCltFar, -- `lem;CLT`, far part (`3_5:2160-2250`); S5-01 (T2138, DECISIONS §40: owed)
$ git diff main...t/T2182 --stat -- RBM3D/Induction/Step5Pins.lean | wc -l
0
```
These are exactly the two sole writable files. The pin `STCltFar` / `STCltFarConcl` (`Step5Pins.lean:385-396`) is not modified.

## 2. Statements against the pins
```
$ ext() { awk '/^def CltFar\.(DomStmt|OffStmt|FlucStmt)/{p=1} p&&/^$/{p=0} p' "$1"; }
$ ext docs/tickets/checks/T2182-check.lean > pin.txt; ext RBM3D/Evolution/CltFar.lean > lean.txt
$ wc -l pin.txt lean.txt; diff pin.txt lean.txt; echo "diff exit $?"
      24 pin.txt
      24 lean.txt
diff exit 0
$ grep -nE "^(private )?(noncomputable )?(def|structure|class|instance|abbrev|opaque|theorem|example)" RBM3D/Evolution/CltFar.lean | grep -v private
73:def CltFar.DomStmt (d : ℕ) : Prop :=
81:def CltFar.OffStmt (d : ℕ) : Prop :=
92:def CltFar.FlucStmt (d : ℕ) : Prop :=
586:theorem cltFar_dom (d : ℕ) : CltFar.DomStmt d := by
1167:theorem cltFar_off (d : ℕ) : CltFar.OffStmt d := by
1505:theorem cltFar_fluc (d : ℕ) : CltFar.FlucStmt d := by
1757:theorem stCltFar_holds (d : ℕ) : STCltFar d := by
1890:example : InstIng5Concl (fun sz E s t => STCltFarConcl sz E s t) szCL zCL sCL tCL 1 :=
1895:example (n : ℕ) := szCL_cltFar_index_nonempty n
1900:example (h2 : STStep2Concl szCL (STflowE zCL) sCL tCL 1) :
1919:example (h2 : STStep2Concl szCL (STflowE zCL) sCL tCL 1) :
1931:example (hK : STKbound szCL (STflowE zCL)) (hKw : STKward szCL (STflowE zCL)) (ha : STLK szCL (STflowE zCL) sCL)
```
- Targets 1-3: the three definitions are byte-identical to the check file (namespace line dropped); each theorem has the form
  `theorem … (d : ℕ) : CltFar.…Stmt d`, as the ticket requires. The hypotheses, quantifier order (`τ D` before `∀ᶠ n`; `σ, a` inside),
  the exponents (`N^τ`, `N^{-D₁}`, `W^{-D}`, `N^{-D'}`, `A^{-6/5}/(|a₁-a₂|^{d-2}+1)`, `c_n = (1-s)²/(g⁴A^{6/5})`) and the index ranges
  are those of the pin.
- Target 4: `stCltFar_holds (d : ℕ) : STCltFar d` uses the merged pin, which is not restated locally (only uses of `STCltFar` in the
  file: `:1757`, the instance `:1890`, comments). The proof introduces exactly the binders of `STIngR5` (`:1758-1762`), takes `𝔠_d`
  from `stCltIso_holds` (`:1759-1760`) and does not strengthen or weaken the conclusion.

## 3. Hidden hypotheses, vacuity, cycles
- The file adds no structure, class or instance. The private definitions are `cltFar_c3`, `cltFar_c0`, `cltFarZ`, `cltFarKp`
  (numerical constants) and `CltFarH5` (`:652`, a Prop). `CltFarH5` never appears in a public statement: it is derived at `:665`
  (`cltFar_H5_at`) from the merged `prop5Decay_holds`.
- External inputs of the targets: `STGdecayW` (a field of `STStep2Concl`, another gate's pin) and, in target 3, `STCltIsoConcl`. In
  target 4, `STCltIsoConcl` is not assumed: the merged theorem `stCltIso_holds` produces it from the premises of `STIngR5`
  (`:1759-1763`). No new external hypothesis is introduced, so lesson 14 does not apply.
- Cycles: the dependencies are merged modules (`CltMoments2`, `MeanFar`, `CltStep`, `Step5Kit`). `STCltFar` occurs only as the
  conclusion of target 4.

## 4. Compiled nonempty instances (`d = 3`, `szCL`, `𝔠 = 1/6`, `𝔡 = 1/10`, `κ = 1/10`, `Cd = 1`, `s ≡ 0`, `t = 1 − L⁻²`)
| target | example | deterministic hypotheses discharged | open (other gates' pins) | nondegenerate data |
|---|---|---|---|---|
| 4 `stCltFar_holds` | `:1890` `inst_cltFar (stCltFar_holds 3) 1 one_pos` | all, inside merged `inst_cltFar` | the nine premises of `STIngR5`, inside `InstIng5Concl` | index set nonempty at every `n` (`:1895`, `szCL_cltFar_index_nonempty`) |
| 1 `cltFar_dom` | `:1900` | `szCL_admissible`, `s<1` (`cltFar_sCL_lt`), `s≤t` (`szCL_hst`), `szCL_reg5I` | `h2 : STStep2Concl` (`h2.2.2`) | `σ=(+,−)`, `(τ,D₁)=(1,1)`, applied at window label `β=(0,0)` (window condition proved by `positivity`) |
| 2 `cltFar_off` | `:1919` | `0<κ`, Admissible, `|E_n| ≤ 1/2 ≤ 2−κ` (`abs_lemE_le`), `0≤s`, `s<t`, `t<1`, `STReg5I` | `h2` | `(D,D')=(1,1)` |
| 3 `cltFar_fluc` | `:1931` | as target 2, and `σ 0 ≠ σ 1` by `decide` | `h2` and the eight further pins `STKbound…STLKU`; `STCltIsoConcl` comes from merged `inst_cltIso (stCltIso_holds 3)` | `(τ,D)=(1/10,1)`, `σ=(+,−)`, `a=(x_n,0)` |

This matches the list in the ticket. None of the instances uses `N = 0`, an empty index set, a collapsed window or a `False` premise.

## 5. Build, axioms and forbidden tokens (audit worktree)
```
$ lake build RBM3D.Evolution.CltFar 2>&1 | grep -E "CltFar|error|Build completed"; echo exit=$?
info: RBM3D/Evolution/CltFar.lean:1951:0: 'RBM.Gauss.Sizes.cltFar_dom' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM3D/Evolution/CltFar.lean:1952:0: 'RBM.Gauss.Sizes.cltFar_off' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM3D/Evolution/CltFar.lean:1953:0: 'RBM.Gauss.Sizes.cltFar_fluc' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM3D/Evolution/CltFar.lean:1954:0: 'RBM.Gauss.Sizes.stCltFar_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
Build completed successfully (3819 jobs).
exit=0            (no error line; no warning line on CltFar.lean)
$ grep -nE "sorry|admit|native_decide|^\s*axiom|maxHeartbeats|implemented_by|extern|unsafe" RBM3D/Evolution/CltFar.lean; echo "grep exit $?"
grep exit 1
```
Registry pre-check: I built every module imported by `RBM3D.lean` on the branch with `lake build`, then ran the root file with one extra
`import RBM3D.Evolution.CltFar` after the last import (`Precheck.lean`). As a control I also ran it without that import (`Pre0.lean`):
```
$ grep '^import' Precheck.lean | sed 's/import //' | xargs lake build | tail -1      → Build completed successfully (3977 jobs).  exit 0
$ lake env lean Precheck.lean; echo exit=$?
axiom audit: 5338 theorems, 1889 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
registry: 2 borrowed + 112 owed + 56 structural; 70 registered premise(s) carry nothing yet: [...]
exit=0
$ lake env lean Pre0.lean; echo exit=$?      # the branch's RBM3D.lean, without the CltFar import
Pre0.lean:224:0: error: axiom audit: 1 premise(s) that no theorem of this development proves are in none of `borrowedProps`, `owedProps`, `structuralPr…
exit=1
```
The registry line can be deleted only together with the root import that the hub adds at merge (CLAUDE.md §3 (A) 4). With that import
the check passes. The prove report (b) says the same. The hub still runs the full `lake build` at merge.

## 6. Paper deltas
`grep -n T2182 docs/paper-deltas.md` returns no hit, as expected: the entries are proposed in the prove report (d) as `T2182a`–`T2182f`.
| Lean/paper difference | candidate |
|---|---|
| `(eq:ells_to_ellt)`, `(eq:ells_to_ellt2)` are carried by the index set but not used | `T2182a` |
| `(eq:propcalB)` with explicit `(Λ', q₁) = (N^τ, N^{-D₁})`; the off-window `W^{-D}` is one event for all `(σ, a)` (targets 1-2) | `T2182b` |
| explicit `p = ⌈(D+2)/τ⌉`, `D₁`, `D'`, `D_w`, `D₀` in place of "any fixed `p`" and `≺` | `T2182c` |
| `‖Θ_t‖ ≤ c_Θ/g²` and the use of `1−s ≤ g²` hidden in the paper's `≲` (`3_5:2204-2211`) | `T2182d` |
| `≺` over the index set as an explicit finite union (`≤ 4N²`) inside `P` | `T2182e` |
| `3 ≤ d` (DECISIONS §36) | `T2182f` |
This covers the four candidates the ticket expected, plus two more (d, f). Target 4 is the pin as stated, so it adds no new difference.

## 7. Observations (not RETURN)
- O1. Consumer limit (prove report (b), `limit2.py`): along `szCL`, the eventual thresholds are `n* ≈ 8.5·10³ – 9.4·10³`
  (`p = 120`, coming from `cltFar_fluc` at `(τ/2, D+3) = (1/20, 4)`). The threshold is finite, explicit, and comes from `p = ⌈(D+2)/τ⌉`
  against `(log N)^{24p}`. It is larger than T2169's `n ≈ 10³`. No instance relies on it being large. Recorded for the dispatcher;
  no statement, instance or build is affected.
- O2. Prove report (b): several narrative lines are long. The report is 243 lines, within the limit.

## Verdict
| target | statement | hidden/vacuity/cycle | instance | build/axioms | deltas | verdict |
|---|---|---|---|---|---|---|
| 1 `cltFar_dom` | = pin | none | `:1900` | ok | T2182b,c | PASS |
| 2 `cltFar_off` | = pin | none | `:1919` | ok | T2182b,c | PASS |
| 3 `cltFar_fluc` | = pin | none | `:1931` | ok | T2182c,d | PASS |
| 4 `stCltFar_holds` | merged `STCltFar` | none | `:1890` (+`:1895`) | ok; registry ok with the root import | T2182a,e,f | PASS |

Overall: **PASS**. No dispatcher sign-off is needed.
