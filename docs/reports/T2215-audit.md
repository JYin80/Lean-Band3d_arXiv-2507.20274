Auditor model: claude-opus-5-5

# T2215 audit (round 1) — S5-10a `Induction/TailtoTailSq` — Mon Oct  5 21:46:37 UTC 2026

Branch `t/T2215` at 407e366 (merge-base 14513ee); audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2215-audit1` (detached).
Scratch scripts in the auditor scratchpad `T2215/` (`diff.py`, `ax.lean`, `reg.lean`, `h3.py`).

## 1. Statements against the pins (script diff, binder line and name stripped)

```
$ python3 diff.py     # body of `def <pin> … :=` in docs/tickets/checks/T2215-check.lean vs body of `theorem <name> … :` up to `:= by`, whitespace-normalised
TailtoTailSq_kernelGen_pin vs tailtoTailSq_kernelGen : IDENTICAL 1020 chars
TailtoTailSq_kernel_pin vs tailtoTailSq_kernel : IDENTICAL 990 chars
TailtoTailSq_instC_pin vs inst_tailtoTailSq_c : IDENTICAL 924 chars
```
All three statements are token-identical to the dispatcher's compiled pins. So the hypotheses, quantifier order (`3 ≤ d → ∀ L [NeZero L], 3 ≤ L → ∀ g W D D₂ E v w p Y …`), the
near condition `∀ i, zdistInf(b_i - b'_i) ≤ (log W)^{(3/2:ℝ)}`, (H3) in the `hkell` form `(1/8)((log W)^{3/2}·ellT L g w) ≤ zdistInf(x-y)`,
the constant `18·exp(8d+2)`, the far term `4·Y·L^d·ρ³·W^{-D₂}` and `ρ = (1-v)/(1-w)` all match the ticket's mathematics ((P1)–(P3)). This is the general
statement for any tensor `X` (7g) and the `STeeUM` form (7). It is not a special case. Target 7's proof is a direct application of 7g at `X = STeeM sz n E v H σ`
(file `:952-954`). `L`, `W` come from `sz.three_le_L`, `sz.W_pos`.

## 2. Hidden hypotheses, vacuity, cycles

```
$ grep -nE "^\s*(@\[[^]]*\]\s*)?(noncomputable )?(theorem|lemma|def|abbrev|instance|structure|class|example)\b" TailtoTailSq.lean | grep -v private
906:theorem tailtoTailSq_kernelGen (d : ℕ) :
932:theorem tailtoTailSq_kernel {d : ℕ} (sz : Sizes d) :
958:example := tailtoTailSq_kernel SizesInst.sz0
965:theorem inst_tailtoTailSq_c :
1018:example (H : Matrix (Idx 3 (SizesInst.sz0.L 1) (SizesInst.sz0.W 1))
$ sed -n 6,7p TailtoTailSq.lean
import RBM3D.Induction.TailtoTail
import RBM3D.Induction.Step5Cases
$ grep -rn "tailtoTailSq_kernelGen\|tailtoTailSq_kernel\b\|inst_tailtoTailSq_c" RBM3D RBM3D.lean | wc -l   # main worktree
       0
$ grep -c "TailtoTail.lean:" TailtoTailSq.lean      # port citations of the copied private helpers
20
```
- No new structure and no `Prop` definition. All premises are explicit arrows in the signature. The file has 30 `private` declarations, all prefixed `tailtoTailSq_`.
- It imports only two merged modules (as the ticket requires) and does not import `RBM3D`, so there is no cycle.
- (H3) is the ticket's external-style premise, supplied downstream by `lemDecCalEPrec_kell`. **Limit check at instance (c)**, computed independently by FFT on `Z_20^3`:
```
$ python3 h3.py       # Θ_w = (1 - w S^(B))^{-1}, S^(B) as in Defs/Block.lean (a=(1+2dg²)^{-1} at 0, g²a at zdistD=1)
ellT= 1 threshold= 1.060168949018333 log64= 4.1588830833596715
max|Theta| on zdistInf>=thr: 2.816617436549959e-10   64^-5= 9.313225746154785e-10  min Theta re: -4.440892100022687e-17
max zdistInf: 10  lstar= 8.481351592146664
```
  So (H3) holds at instance (c) with ratio 0.30 and the premise is not contradictory. Because `max zdistInf = 10 > ℓ* = 8.48`, the near and far branches of `X` both occur.

## 3. Compiled nonempty instances

- **7g** has `inst_tailtoTailSq_c` (`:965`). It applies `tailtoTailSq_kernelGen` at `d = 3, L = 20, g = 1/64, W = 64, D = 8, D₂ = 5, E = 0, v = 1/32, w = 1/16, p = Y = 1`.
  - `X` is the concrete tensor `if near then T_{v,8}(|b₀-b₁|)² else 1`.
  - Discharged in the proof: `3 ≤ 3`, `3 ≤ 20`, `0 < 64`, `|0| ≤ 2`, `0 ≤ 1/32 ≤ 1/16 < 1`, `(1/64)² ≤ 15/16`, `0 ≤ 1`, and `4 ≤ log 64` (`tailtoTailSq_four_le_log64`, via `Real.log_two_gt_d9`).
  - (H1) is discharged by `if_pos` and `Complex.norm_real`. (H2) is discharged by `hT1 : T_{1/32,8}(r)² ≤ 1` and `‖1‖ = 1`.
  - Only (H3) stays a hypothesis, as the ticket prescribes. Section 2 shows it is satisfiable.
  - The data are nondegenerate: `L = 20`, `8000` sites, a non-collapsed window `v < w`, and both far and near pairs present.
- **7** has two instances.
  - `example := tailtoTailSq_kernel SizesInst.sz0` (`:958`) is exactly the ticket's prescribed instance.
  - The prover added an example (`:1018`) at `sz0`, `n = 1`, which discharges every scalar premise (`|0| ≤ 2`, `v,w`, `lam² ≤ 15/16`, `4 ≤ log 1024`, `0 ≤ p, Y`).
  - In both examples (H1)–(H3) about `STeeM … H` stay hypotheses. These are the outputs of other gates (`lemDecCalEPrec_Bounds` conj. 3, `difRep2_norm_STeeM_le_N`, `lemDecCalEPrec_kell`), as the ticket prescribes.
- Both compile: section 4 builds with exit 0.

## 4. Build, axioms, forbidden tokens, diff scope

```
$ lake build RBM3D.Induction.TailtoTailSq > build.log 2>&1; echo "exit=$?"
exit=0
$ grep -c "error" build.log ; tail -1 build.log
0
Build completed successfully (3778 jobs).
$ grep "TailtoTailSq" build.log | grep -E "error|warning"      # (no output)
$ lake env lean ax.lean
'RBM.Gauss.Sizes.tailtoTailSq_kernelGen' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.tailtoTailSq_kernel' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.inst_tailtoTailSq_c' depends on axioms: [propext, Classical.choice, Quot.sound]
exit=0
$ grep -nE "sorry|admit|native_decide|^axiom|^\s*axiom " RBM3D/Induction/TailtoTailSq.lean; echo $?
1
$ git diff --stat main...HEAD
 RBM3D/Induction/TailtoTailSq.lean | 1043 +++++++++++++++++++++++++++++++++++++
 1 file changed, 1043 insertions(+)
$ printf 'import RBM3D\nimport RBM3D.Induction.TailtoTailSq\n#assert_rbm_axioms\n' > reg.lean; lake env lean reg.lean > reg.log 2>&1; echo "exit=$?"
exit=0
$ grep -ciE "error|fail|unregistered|unlisted" reg.log ; head -4 reg.log
0
axiom audit: 6437 theorems, 2222 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
All within [propext,
 Classical.choice,
 Quot.sound]; no project axioms: what the paper cites rather than proves is carried as hypotheses, not asserted.
```
The diff touches only the sole writable file. `Test/Axioms.lean` is untouched and no registry line is needed. No frozen signature is touched because the file is new.
The full `lake build` is run by the hub at merge.

## 5. Paper deltas

The paper states no kernel lemma: it uses BDG with `(res_deccalE_dif)`, `3_5:2364-2383`. Prove report (d) (`T2215-prove.md:226-227`) proposes:
- **T2215a** (= T2209c): the squared-profile TailtoTail statement itself, with its near/far split at `(log W)^{3/2}` and the constant `18e^{8d+2}`.
- **T2215b**: the far remainder `4YL^dρ³W^{-D₂}`, with a separate `D₂` and the crude `Y` (the paper has `W^{-D+C}` with one `D`).

The (P3) form choices (`0 < g` dropped, `(W^{-D})²` for `W^{-2D}`, explicit `C₇`) are not paper differences beyond T2215a, because the paper has no statement to differ from. Coverage is complete.

## 6. Observations (no effect on statement, instance, build, axioms or delta coverage)

- O1. Target 7's instances keep (H1)/(H2) about `STeeM … H` as hypotheses, which is the ticket's prescription.
  - At `p = Y = 1`, `W = 1024` in the extra example (`:1018`), whether some `H` satisfies (H1) is not shown.
  - The nondegeneracy of the mathematics rests on instance (c) of 7g. Target 7 is its direct application at `X = STeeM`.
- O2. The conclusion's constant `18e^{8d+2}` (≈ 3.5e12 at `d = 3`) is loose, which is allowed by CLAUDE.md §7 ("constants need not be optimal"). It is a conclusion constant, not a hypothesis witness.

## Verdict

| Target | Statement | Hidden hyp./vacuity/cycle | Instance | Build/axioms | Paper deltas | Verdict |
|---|---|---|---|---|---|---|
| `tailtoTailSq_kernelGen` (7g) | identical to pin | none; (H3) satisfiable (0.30 ratio) | `inst_tailtoTailSq_c`, nondegenerate | exit 0, 3 std axioms | T2215a, T2215b | **PASS** |
| `tailtoTailSq_kernel` (7) | identical to pin | none | `:958` (prescribed), `:1018` | exit 0, 3 std axioms | T2215a | **PASS** |
| `inst_tailtoTailSq_c` | identical to pin | — | is the instance | exit 0, 3 std axioms | — | **PASS** |

Overall: **PASS**. No dispatcher sign-off needed.
