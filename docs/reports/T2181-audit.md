Auditor model: claude-opus-5-5

# T2181 audit (round 1): S5-07 `lemDecCalE_dif` (`Path/LemDecCalEdif2`)

Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2181-audit1`, detached at `t/T2181` = `67118f1`.
Scratch: `scratchpad/T2181/` (`ax.lean`, `sig.lean`, `instdiff.py`, `pre.lean`).

## 1. Statement (target 1)

```
$ lake env lean ax.lean
RBM.Path.lemDecCalE_dif : ∀ (d : ℕ), RBM.Path.LemDecCalE_dif d
'RBM.Path.lemDecCalE_dif' depends on axioms: [propext, Classical.choice, Quot.sound]
-- example : ∀ d : ℕ, RBM.Path.LemDecCalE_dif d := RBM.Path.lemDecCalE_dif   (check-file lemDecCalE_difTarget): no error
def RBM.Path.E2HypDif ... := E2Hyp sz n E u D Λ K₀ J M ∧ (L^d * W^(6d))^2 ≤ W^D ∧
   (∀ σ : Fin 4 → Bool, ∀ a, ‖STLM n E u M σ a‖ ≤ Λ * (W^d(1-u))⁻¹^3) ∧
   (∀ σ : Fin 6 → Bool, ∀ a, ‖STLM n E u M σ a‖ ≤ Λ * (W^d(1-u))⁻¹^5)
def RBM.Path.lossE2dif := fun d L W Λ K₀ => lossE2 d L W Λ K₀ * (729 ^ d * (1 + log (L^d * W^(6d))) ^ (2d))
$ sed -n 852p RBM3D/Path/LemDecCalEdif2.lean
theorem lemDecCalE_dif (d : ℕ) : LemDecCalE_dif d := by
$ git diff --stat main...t/T2181 -- RBM3D/Path/LemDecCalEdif.lean RBM3D/Path/LemDecCalE.lean RBM3D/Induction/Step5Pins.lean RBM3D/Test/Axioms.lean | wc -l
0
```
- The target's type is the merged pin `LemDecCalE_dif d` (`Path/LemDecCalEdif.lean:80`, T2171, audited there
  against `res_deccalE_dif` and `Step5Pins.lean:178-186`), verbatim by definitional name, for every `d`; no
  `(hd : 3 ≤ d)` added (it is the first conjunct of `E2Hyp`). The pin, `E2HypDif`, `lossE2dif` are unchanged (0 diff lines).
- Quantifiers: `∀ sz n E u D Λ K₀ J M, E2HypDif … → ∀ σ a a', range → bound` — every `σ : Fin 2 → Bool`, every
  `a, a'` with `|a_i − a'_i|_∞ ≤ (log W)^{3/2}`; the proof is `intro …; by_cases` on the pin's indicator and does
  not specialise `σ` (`sed -n 852,859p`: `near_case h σ a a' hn` / `far_case h σ a a' (hr 0) (hr 1) …`).
- Not a special case or conditional adapter: no premise beyond the pin's. **Statement: PASS.**

## 2. Vacuity, hidden hypotheses, cycles

```
$ grep -nE "^(theorem|lemma|def|example|private|abbrev|instance|structure|class)" RBM3D/Path/LemDecCalEdif2.lean | awk '{print $1,$2,$3}'
  29 `private theorem lemDecCalEdif2_*` (lines 48–922), `theorem lemDecCalE_dif` (852), `example` (944), `example` (986)
  -- no def/structure/class/instance in the new file
$ grep -n "^import" RBM3D/Path/LemDecCalEdif2.lean
6:import RBM3D.Path.LemDecCalEdif
$ grep -n "LemDecCalEdif_cut_near\|LemDecCalEdif_cut_far\|LemDecCalEdif_STeeM_le" RBM3D/Path/LemDecCalEdif2.lean
452:    have c1 := LemDecCalEdif_cut_near h (σ 0) (σ 1) (a 0) (a 1) (a' 0) (a' 1) b b'
453:    have c2 := LemDecCalEdif_cut_near h (σ 1) (σ 0) (a 1) (a 0) (a' 1) (a' 0) b b'
457:    refine (LemDecCalEdif_STeeM_le sz n E u M σ a a').trans ?_
677:    have c1 := LemDecCalEdif_cut_far h (σ 0) (σ 1) (a 0) (a 1) (a' 0) (a' 1) b b' h1 h2 hb' hd
678:    have c2 := LemDecCalEdif_cut_far h (σ 1) (σ 0) (a 1) (a 0) (a' 1) (a' 0) b b' h2 h1 hb' hd'
691:    refine (LemDecCalEdif_STeeM_le sz n E u M σ a a').trans ?_
$ grep -nE "J ≤ |hJW" RBM3D/Path/LemDecCalEdif2.lean      # the J ≤ W conjunct of E2Hyp
26:, 27:, 493:  (docstrings only)
565:  have hJJ : J ≤ (1 - u)⁻¹ * J ^ 3 := by
566:    have h1 : J ≤ J ^ 3 := le_self_pow₀ hJ1 (by norm_num)
$ sed -n 79,80p   (lemDecCalEdif2_basic: the only destructuring of E2Hyp)
  obtain ⟨hd3, hE, hu0, hu1, hlam, hlamu, hlamW, hΛ, hK, hlog, hfloor, hH, h6, h78, h9, hJ1,
    -⟩ := h
```
- No structure field carries a hypothesis; the only premise is the merged `E2HypDif` (T2171's pin).
- Dependencies are merged results (T2171 `cut_near`, `cut_far`, `STeeM_le`; T2164 `e2`, `e10a`, `sum_tail_tail`,
  `floor_A`; `sum_norm_SB_row`, `card_Zd`); the new module imports only `Path/LemDecCalEdif`: no cycle.
- The conjunct `J ≤ W` is discarded by the trailing `-` and named nowhere in the new file (the merged T2171 cut
  lemmas are out of scope). No external hypothesis is introduced, so no new limit check is due. **PASS.**

## 3. Compiled nonempty instances

```
$ python3 instdiff.py      # example bodies vs check-file instNear / instFar (verbatim line comparison)
instNear example line 944 lines 10 10 IDENTICAL
instFar example line 986 lines 11 11 IDENTICAL
$ lake env lean sig.lean
RBM.Path.LemDecCalEdif_inst_a : RBM.Path.E2HypDif sz0 1 (1 / 2) 0 38 1 1 1 0
RBM.Path.LemDecCalEdif_inst_b : RBM.Path.E2HypDif szCL 0 (1 / 2) 0 42 1 1 1 0
'RBM.Path.LemDecCalEdif_inst_a' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Path.LemDecCalEdif_inst_b' depends on axioms: [propext, Classical.choice, Quot.sound]
$ grep -n "lemDecCalE_dif 3" RBM3D/Path/LemDecCalEdif2.lean
  refine ⟨?_, lemDecCalE_dif 3 sz0 1 (1 / 2) 0 38 1 1 1 _ hI ![true, true] a a hrange⟩
  refine ⟨?_, lemDecCalE_dif 3 szCL 0 (1 / 2) 0 42 1 1 1 _ hI ![true, false] a a' hrange⟩
```
- Both `example`s have no binders: every hypothesis of `lemDecCalE_dif` is discharged at concrete data —
  `E2HypDif` by the merged closed theorems `_inst_a`/`_inst_b`, the range premise by `zdistInf` computations
  (`unfold zdistInf; decide`) and `szCL_one_le_log_W`; each also proves `0 < R` and its branch (`hbr`):
  (a) `sz0, n=1` (`L=8, W=1024, D=38`), `σ=(+,+)`, `|a₀−a₁|_∞ = 1 ≤ 4ℓ*`, near;
  (b) `szCL, n=0` (`L=2·24⁵, W=2^24, D=42`), `σ=(+,−)`, `|a₀−a₁|_∞ = 300 > 4ℓ*` (`lemDecCalEdif2_inst_ell`),
  `|a₀−a'₀|_∞ = 1`, `|a₁−a'₁|_∞ = 0`, far.
- Nondegenerate in the CLAUDE.md §4 sense: `d=3`, `L ≥ 8`, nonempty lattice, nontrivial window `u=0 < 1`,
  no `False` premise, both branches of the indicator exercised, `a ≠ a'` in (b). **PASS.**

## 4. Build, axioms, hygiene, diff

```
$ lake build RBM3D.Path.LemDecCalEdif2 2>&1 | grep -E "^error|LemDecCalEdif2|Build completed|failed"
Build completed successfully (3818 jobs).
$ ls .lake/build/lib/lean/RBM3D/Path/LemDecCalEdif2.olean   # built here (absent from the copied main cache)
Oct 4 23:51 .lake/build/lib/lean/RBM3D/Path/LemDecCalEdif2.olean
$ grep -nE "sorry|admit|native_decide|^axiom|^\s*axiom|maxHeartbeats|set_option|opaque|implemented_by|extern" RBM3D/Path/LemDecCalEdif2.lean
35:set_option linter.style.longLine false
36:set_option linter.unusedSectionVars false
$ git -C /Users/junyin/Lean_proof/RBM3D diff --name-only main...t/T2181
RBM3D/Path/LemDecCalEdif2.lean
$ lake env lean pre.lean     # import RBM3D; import RBM3D.Path.LemDecCalEdif2; #assert_rbm_axioms
exit 0
axiom audit: 5335 theorems, 1886 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
$ grep -c "LemDecCalE_dif\|lemDecCalE_dif" pre.out
0
```
- Only the three standard axioms; no `sorry`/`admit`/`axiom`/`native_decide`; the two `set_option`s are linters.
- Diff touches only the sole writable file `RBM3D/Path/LemDecCalEdif2.lean`; `Test/Axioms.lean` untouched (no new
  `Prop`; the registry lists neither name). Frozen signatures untouched. **PASS.**

## 5. Paper deltas

```
$ grep -nE "T2171[a-e]|T2181" docs/paper-deltas.md | cut -c1-90
1387:- **D428（T2171a）**：四、六圈界是 `E2HypDif` 的前提（RBM2D `goodSet` 条款 2，`k = 4, 6`），…
1388:- **D429（T2171b）**：下限 `(L^dW^{6d})² ≤ W^D`，强于 D374 的 `L^dW^{2d} ≤ W^D` …
1389:- **D430（T2171c）**：`σ ∈ {+,−}²` 全部四种（RBM2D 只 `(+,−)`）。
1390:- **D431（T2171d）**：`lossE2dif = lossE2·729^d(1+log(L^dW^{6d}))^{2d}` 是 `res_deccalE_dif` 中 `≺` 的显式损失。
1391:- **D432（T2171e）**：`_cut_far` 的四圈因子写作 `Λ((W^d(1−u))^{-1})^{3/2}` …
```
- The statement is T2171's pin; its Lean/paper differences are D428–D432 (already appended). The prove report (d)
  proposes the proof-level candidates T2181a (`J ≤ W` unused), T2181b (single far term), T2181c (`convTailT` →
  `LemDecCalE_sum_tail_tail`). No uncovered statement difference. **PASS.**

## 6. Observations (no RETURN)

- O1. At the pinned data `M = 0`, `a₀ ≠ a₁`, the left side `‖STeeM‖` is `0` (prove report (a), `inst.py`), so the
  inequality conjunct of both examples is trivially true at those values; the instances are the dispatcher's
  check-file pins, verbatim, with every premise discharged and `0 < R` proved. Not a §4 degeneracy (no `N = 0`,
  empty index, collapsed window or `False` premise). The dispatcher may wish a nonzero-left-side instance
  (`a = a' = (0,0)` per (a)) for S5-09.
- O2. The route deviates from the ticket's suggestion without statement effect: `LemDecCalE_e1`, `_e1_rpow`,
  `_tailT_anti` are unused (report (b) item 7).
- O3. Report (a) row 11 uses `(1+log W)³ ≥ 125` while the Lean proof uses `≥ 1` (report (b) item 6); the Lean
  slack table (`rows_lean.py`, minimum factor 3.1e7 for `F1+F2`) is the binding one. No defect.

## Verdict

| target | statement | no vacuity / hidden hyp / cycle | instance | build + axioms + diff | paper deltas | verdict |
|---|---|---|---|---|---|---|
| `lemDecCalE_dif (d) : LemDecCalE_dif d` | PASS | PASS | PASS | PASS | PASS | **PASS** |

T2181: **PASS**. No dispatcher sign-off needed.
