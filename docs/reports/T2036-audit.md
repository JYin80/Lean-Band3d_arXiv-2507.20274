Auditor model: claude-opus-5-5

# T2036 audit, round 1: KL6 `KLK_ward` (`lem_WI_K`, `(WI_calK)`), `RBM3D/Loop/KLWard.lean`

Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2036-audit1` (detached at `t/T2036` = 9dcb3a6). Written Sat Oct  3 06:31:03 UTC 2026 (`date -u`).
Scripts are in `scratchpad/T2036_aud/` (session scratchpad).

## 0. Diff scope
```
$ git diff --name-only main...t/T2036
RBM3D/Loop/KLWard.lean
$ git log --oneline main..t/T2036
9dcb3a6 T2036: KL6 Ward identity KLK_ward (every n, both charge orders), flip lemma KLWard_flip
```
The only writable file is touched. `RBM3D/Test/Axioms.lean` is untouched (no registry line was needed; see §4). No merged file changed, so no frozen signature changed.

## 1. Statement against the pin (target 1, `KLK_ward`)
```
$ sed -n '/^def KLwardPin : Prop :=/,/^$/p' docs/tickets/checks/T2036-check.lean | sed 1d | tr -s ' \n' ' ' > pin.txt
$ sed -n '/^theorem KLK_ward :/,/:= by$/p' RBM3D/Loop/KLWard.lean | sed 1d | sed 's/ := by$//' | tr -s ' \n' ' ' > thm.txt
$ diff pin.txt thm.txt && echo "pin body == KLK_ward type (whitespace-normalised)"
pin body == KLK_ward type (whitespace-normalised)
```
Elaborated check (`AuditT2036.lean`, `import RBM3D.Loop.KLWard`; the pin copied verbatim from the check file into `RBM.Loop.T2036Audit`):
```
example : KLwardPin := KLK_ward
example : type_of% @KLK_ward = KLwardPin := rfl
$ lake env lean AuditT2036.lean ; echo exit=$?      -> exit=0 (output in §4)
```
Against the paper (`paper/tex/1_2_Intro_model_result.tex:1034-1044`):
```
1035: Given $\bsig\in\{+,-\}^n$ with $n\ge 2$ and $\sigma_1=-\sig_{n}$, ...
1040: \sum_{a_n}{\cal K}^{(n)}_{t, \bsig, \ba}=
1041: \frac{1}{2\ii W^d\eta_t}\left( {\cal K}^{(n-1)}_{t, \wh\bsig^{(+,n)}, \wh\ba^{(n)}}- {\cal K}^{(n-1)}_{t, \wh\bsig^{(-,n)}, \wh\ba^{(n)}}\right)
1043: \wh\bsig^{(\pm,n)}:=(\pm, \sigma_2, \cdots \sigma_{n-1}) ... \wh\ba^{(n)}:=(a_1, a_2,\cdots, a_{n-1})
```
Lean: `σ = s :: μ ++ [!s]` (so `σ₁ = −σₙ`, `n = |μ|+2 ≥ 2`, every `μ`, both `s`); `a ++ [x]` with `a.length = μ.length + 1` (labels `a₁..a_{n−1}` arbitrary, `a_n = x` summed over `Zd d L`); right side `(2 i W^d η_t)⁻¹ (𝒦_{(+,μ),a} − 𝒦_{(−,μ),a})` with `η_t = Gauss.etaT E t = (1 − t) * (mE E).im` (`GLoop.lean:75`, matches `(eta)`). Exponent `W^d`, no `L^2`, no `3 ≤ d`. Quantifier order: all parameters fixed before `t`, `s`, `μ`, `a` — the pin's order.
Hypotheses: `3 ≤ L` (D1), `1 ≤ W`, `|E| < 2` (bulk, needed for `η_t > 0`), `0 ≤ t < 1` (T2004d, signed in DECISIONS §15), `g` any real. Not a special case: every `n ≥ 2` and both charge orders. `𝒦 = KLK` is the concrete tree sum (`KLTree.lean:145`, `KLgen d L g W (mSigma E) t I`), not a choice from an existence hypothesis.
**Statement: PASS.**

## 2. Vacuity, hidden hypotheses, cycles
- `KLK_ward` has numeric hypotheses only; no structure argument and no `Prop`-valued hypothesis (`IsKLoop` appears only inside the proof, discharged by the merged `KLK_isKLoop`).
- Dependencies (all merged on `main`):
```
$ for n in KLK_isKLoop KLK_unique KLK_rotate KLretire_twoLoopBounded KLward_two KLK_one; do git grep -l -E "^theorem $n( |$)" main -- RBM3D; done
KLK_isKLoop: main:RBM3D/Loop/KLTreeDeriv.lean
KLK_unique: main:RBM3D/Loop/KLUnique.lean
KLK_rotate: main:RBM3D/Loop/KLUnique.lean
KLretire_twoLoopBounded: main:RBM3D/Loop/KLUnique.lean
KLward_two: main:RBM3D/Loop/KLTree.lean
KLK_one: main:RBM3D/Loop/KLTree.lean
```
  Signatures read: `KLK_isKLoop`, `KLK_unique`, `KLK_rotate` take only `3 ≤ L`, `1 ≤ W`, `|E| < 2`, `t ∈ Ico 0 1` and length/WF side conditions; `KLretire_twoLoopBounded` takes an `IsKLoop` family (supplied by `KLK_isKLoop`); `KLward_two` is the `n = 2` case, numeric hypotheses only.
- Imports: `RBM3D.Loop.KLUnique`, `Mathlib.Analysis.Calculus.Deriv.Star`; no cycle.
- `s = false` is reduced to `s = true` through `KLWard_flip` (`𝒦(σ.map not) = conj 𝒦(σ)`, by `KLK_unique`) and `conj κ_t = −κ_t` (`KLWard_conj_kappa`), proved in the file. Registry pre-check (§4): no new premise.
**PASS.**

## 3. Compiled nonempty instances (same file, lines 1179–1224)
```
theorem KLWardInst_ward_true :
    ∑ x : Zd 3 5, KLK 3 5 (1 / 2) 2 0 (9 / 10) ⟨true :: [false] ++ [!true], [0, 1] ++ [x]⟩ = ... := by
  simpa using KLK_ward 3 5 2 (1 / 2) 0 (by norm_num) (by norm_num) (by norm_num) (9 / 10)
    (by norm_num) (by norm_num) true [false] [0, 1] rfl
theorem KLWardInst_ward_false :   -- same data, s = false
  simpa using KLK_ward 3 5 2 (1 / 2) 0 (by norm_num) (by norm_num) (by norm_num) (9 / 10)
    (by norm_num) (by norm_num) false [false] [0, 1] rfl
theorem KLWardInst_ward_two_false   -- n = 2, μ = [], a = [0]
theorem KLWardInst_ward_four_false  -- n = 4, μ = [true,false], a = [0,1,2]
theorem KLWardInst_flip             -- KLWard_flip at n = 3
```
Data: `d = 3, L = 5, W = 2, g = 1/2, E = 0, t = 9/10, μ = [false], a = [0,1]`. These are the ticket's `KLinst_ward` data, with both `s`. Every deterministic hypothesis (`3 ≤ 5`, `1 ≤ 2`, `|0| < 2`, `0 ≤ 9/10`, `9/10 < 1`, length) is discharged by `norm_num`/`rfl`. Nothing is left as a hypothesis. The data are nondegenerate: `N = 1000`, `η_t = 1/10`, distinct labels. Prove report (a)(ii) gives both sides `≈ −0.0232 i ≠ 0` numerically. All five compile (build in §4).
**PASS.**

## 4. Build and axioms
```
$ lake build RBM3D.Loop.KLWard ; echo exit $?
✔ [3246/3246] Built RBM3D.Loop.KLWard (11s)
Build completed successfully (3246 jobs).
exit 0
$ grep -ciE "warning|error" build.log
0
$ lake env lean AuditT2036.lean ; echo exit=$?
'RBM.Loop.KLK_ward' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Loop.KLWard_flip' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Loop.KLWardInst_ward_true' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Loop.KLWardInst_ward_false' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Loop.KLWardInst_ward_two_false' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Loop.KLWardInst_ward_four_false' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Loop.KLWardInst_flip' depends on axioms: [propext, Classical.choice, Quot.sound]
exit=0
$ grep -nE "sorry|admit|native_decide|^axiom|^\s*axiom |opaque|unsafe|implemented_by|extern" RBM3D/Loop/KLWard.lean
(no output)
$ grep -n set_option RBM3D/Loop/KLWard.lean
63:set_option linter.style.longLine false
$ lake build RBM3D ; echo exit=$?      (root, without KLWard import)
info: RBM3D.lean:74:0: axiom audit: 1166 theorems, 419 definitions, 0 axioms in `RBM` ...
premises found by scanning: 12 (borrowed 2, owed 0, structural 10).
Build completed successfully (3734 jobs).
exit=0
$ printf 'import RBM3D\nimport RBM3D.Loop.KLWard\n#assert_rbm_axioms\n' > precheck.lean; lake env lean precheck.lean   (DECISIONS §20)
axiom audit: 1174 theorems, 419 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
All within [propext, Classical.choice, Quot.sound]; no project axioms ...
premises found by scanning: 12 (borrowed 2, owed 0, structural 10).
exit=0
```
The premise count is 12 both without and with the module, so `RBM3D/Test/Axioms.lean` needs no registry line.
Name clash:
```
$ git grep -n -E "KLK_ward|KLWard_flip|KLWardInst" main -- RBM3D | wc -l
       0
```
Public names: `KLK_ward` (pinned), `KLWard_flip` and `KLWardInst_*` (all with the file stem, §3 (E)). The other helpers are `private`.
**PASS.**

## 5. Paper deltas
The Lean statement differs from `lem_WI_K` only in these ways:
- `t ∈ [0,1)`: T2004d, accepted in DECISIONS §15 (numbered at merge).
- `3 ≤ L`: D1.
- The random band matrix model only: D6.
- `|E| < 2` and `1 ≤ W`: the setting of `(eta)`/`m(E)`, with `η_t > 0`.

The full lemma is proved, for every `n ≥ 2` and both charge orders, with no `[YY_25]` input; it is not weaker than the paper. No new candidate is needed, which matches prove report (d).
**PASS.**

## Observations (no effect on the verdict)
- O1. In prove report (a), the ticket's numerical tolerance of 2e-15 is exceeded at `L = 5` (3.11e-15 absolute, relative 3.4e-15). The report states this itself. It changes no statement.
- O2. The module has 1224 lines; design row KL6 estimated 950.
- O3. `set_option linter.style.longLine false` is at file level; it affects style only.

## Verdict
| Target | Statement | Hidden hyp./cycle | Instance | Build/axioms | Paper deltas | Verdict |
|---|---|---|---|---|---|---|
| `KLK_ward` | = pin (script + `rfl`) | none | `KLWardInst_ward_true/false` (+ n=2, n=4) | exit 0, standard 3 | covered (T2004d, D1, D6) | **PASS** |

Ticket T2036: **PASS**. No dispatcher sign-off needed. Hub: add `import RBM3D.Loop.KLWard` after the last `import` line of `RBM3D.lean`.
