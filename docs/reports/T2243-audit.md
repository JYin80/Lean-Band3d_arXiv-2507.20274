Auditor model: claude-opus-5-5

# T2243 (LW-14b, `Graph/LWExpTerm2`) — audit round 1 (written Tue Oct  6 04:01:52 UTC 2026)

Branch `t/T2243` = 7fc8e8e; audit worktree `../RBM3D-wt/T2243-audit1` (detached at 7fc8e8e). `SP` = auditor scratchpad `T2243/`.

## 1. Scope, build, forbidden tokens
```
$ git diff --name-only main...t/T2243
RBM3D/Graph/LWExpTerm2.lean
RBM3D/Test/Axioms.lean
$ git diff main...t/T2243 -- RBM3D/Test/Axioms.lean | grep -c '^-[^-]'      # deleted registry lines
0
$ lake build RBM3D.Graph.LWExpTerm2 | tail -1 ; grep -c '^error' build.log ; grep -c LWExpTerm2 build.log
Build completed successfully (3856 jobs).
0
1            # the single line "✔ [3856/3856] Built RBM3D.Graph.LWExpTerm2 (15s)": no warning in the new file
$ lake build RBM3D | tail -1     # root (registry module rebuilt with the branch's Axioms.lean)
Build completed successfully (4045 jobs).
$ grep -cE '\bsorry\b|\badmit\b|native_decide|^\s*axiom ' RBM3D/Graph/LWExpTerm2.lean
0
```
Imports (lines 6-11): `LWExpTerm`, `LWGGExp`, `LWSizeClaim`, `Step6Kit`, `Step5Kit`, `Green.IBPPoly`, as the ticket requires; the file does not import `RBM3D`. Only new files and added registry lines; no merged signature is touched.

## 2. Statements against the pins (script)
`SP/pincheck.lean`: the check file's section 2 is copied verbatim into `namespace T2243Check`, then `Iff.rfl`/`rfl` for the six pins, and `@name` for targets 7-9:
```
example {d} (sz : Sizes d) K : T2243Check.LWExpKerPin sz K ↔ LWExpKer sz K := Iff.rfl
example {d} (sz : Sizes d) n E t : T2243Check.LWExpKpPin sz n E t = LWExpKp sz n E t := rfl
example d : T2243Check.LWExpI1KPin d ↔ LWExpI1K d := Iff.rfl        (likewise I23K, I41K, G5')
example : ∀ d, T2243Check.LwCutExpOfTermsPin d := @lwCutExp_of_terms
example : ∀ d, T2243Check.LwExpG5OfG5'Pin d := @lwExpG5_of_G5'
example : ∀ d, T2243Check.LwExpI1OfKPin d := @lwExpI1_of_K
example : ∀ d, T2243Check.LwExpI41OfKPin d := @lwExpI41_of_K
example : LWExpKer sz0 (fun n => SB 3 (sz0.L n) (sz0.lam n)) := RBM.Gauss.LWInst.lwExpTerm2_inst_ker_SB
$ lake env lean SP/pincheck.lean ; echo exit=$?      # 10 pin defs, 11 examples
exit=0
```
A text diff (check-file section 2 with `Pin` removed vs. `LWExpTerm2.lean:66-150`, comments removed) shows only docstring continuation lines; the code lines are identical.

The target 7 conclusion is the merged `LWCutExp d` (`LWExpTerm.lean:52`). Its quantifier order is `3 ≤ d → ∀ κ ε 𝔡 … → STFlow → 0 ≤ t ≤ lemT → 5 ST laws → Prec` over the index set `ĝ²/L^d ≤ 1-t`, and the bound is `(1-t)⁻¹ B^{5/2}`; this is unchanged.

Unpinned targets 3-5 (signatures read from the file):
- `lwExpTerm2_ker_SB : LWExpKer sz (fun n => SB d (sz.L n) (sz.lam n))`, with no hypothesis (`:1741`).
- `lwExpTerm2_ker_Kp (hd : 3 ≤ d) (hκ : 0 < κ) (hz : STFlow …) (ht0 : ∀ n, 0 ≤ t n) (htz : ∀ n, t n ≤ lemT (z n))` (`:1794`). `t ≤ lemT` replaces the ticket's `t < 1` and implies it (`st5_t_lt_one`); `3 ≤ d` is needed by `lwSplus_decay`. Every pin carries both. The constants are uniform in `n` through the finite patch `lwExpTerm2_ker_of_eventually` (`:1655`). The proof is the one the ticket asked for.
- `lwExpTerm2_Kp_split (hE : |E| < 2) (0 ≤ t) (t < 1) : t•(SB * K⁺) = (m²)⁻¹•(K⁺ − t•SB)` (`:1173`). This is the ticket's identity, verbatim in form.
- `lwExpTerm2_cut_conj : conj (LWcut … false σ ac ao ω) = LWcut … true (!σ) ao ac ω` (`:1627`), pathwise. `lwExpTerm2_norm_cut_false` (`:1944`) gives the ticket's equality of norms of expectations.
- `lwExpTerm2_cut_expand (hG : GaussIBP sz) (|E|<2) (0<t) (t<1)` (`:1516`) gives `𝔼 LWcut(true,σ,ac,ao) = P_a + t P_b(true) + t P_b(false) + m P_d + t P_c`, with kernel `KK = S^B(m·1 + m³K⁺)` (`:1263`). `t = 0` is `lwExpTerm2_cut_zero` (`:1869`).

## 3. Hidden hypotheses, vacuity, cycles
- Every pin is a plain `Prop` implication; there are no structure fields. `LWExpKer` is an explicit premise of the three K-pins. For the only kernel used, `lwExpTerm2_KK`, it is discharged by `lwExpTerm2_ker_KK` (`:1843`, from `ker_SB_mul`, `ker_add`, `ker_smul`, `ker_one`, `ker_Kp`).
- In `lwCutExp_of_terms` (`:1956-2023`), `GaussIBP sz` is the merged theorem `gaussIBP sz`, and `B ≤ 1` eventually is the merged `st5_Bctl_le_one`. `η⁻¹ ≤ (2/√(2κ))(1-t)⁻¹` is `lwExpTerm2_eta_inv_le` (`st6_mE_im_ge`), and `t < 1` is `st5_t_lt_one`.
- The five term bounds are obtained by applying the pins at concrete indices, e.g. `a1 ((true, ![σ, true]), ![ao, ac])` and `a5 ⟨((true, σ), ![ao, ac]), hg⟩`. Each instantiation is accepted by Lean only if `P_a…P_d` are definitionally the pins' left sides, so the identification (target 6) is kernel-checked.
- `σc = false` is reduced to `σc = true` by `lwExpTerm2_norm_cut_false`.
- No cycle: the new module imports only merged modules, and no premise is the conclusion.
- The four term pins are other gates' owed pins (LW-14d: `I1K`, `I23K`, `I41K`; LW-14c: `G5'`), registered in `owedProps` (§5). The section (a) preflight tested their truth: an MC ratio of at most 0.08 of the bound for `σo = ±`, and the `(+,+)` 2-loop argument for `I41K`. They are not proved here, which is the ticket's design.

## 4. Axioms (`SP/pincheck.lean`, verbatim output lines)
```
'RBM.Gauss.Sizes.lwCutExp_of_terms' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.lwExpG5_of_G5'' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.lwExpI1_of_K' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.lwExpI41_of_K' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.lwExpTerm2_ker_SB' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.lwExpTerm2_ker_Kp' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.lwExpTerm2_Kp_split' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.lwExpTerm2_cut_expand' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.lwExpTerm2_cut_conj' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.lwExpTerm2_norm_cut_false' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.LWInst.lwExpTerm2_inst_cut' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.LWInst.lwExpTerm2_inst_ker_Kp' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.LWInst.lwExpTerm2_inst_expand' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## 5. Registry pre-check (`import RBM3D` + `import RBM3D.Graph.LWExpTerm2` + `#assert_rbm_axioms`)
```
$ lake env lean SP/pre.lean ; echo pre exit $?
axiom audit: 7104 theorems, 2389 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
  RBM.Gauss.Sizes.LWtermEXP: 23 [no certificate]
  RBM.Gauss.Sizes.LWCutExp: 3 [no certificate]
  RBM.Gauss.Sizes.LWExpI1K: 4 [no certificate]
  RBM.Gauss.Sizes.LWExpI23K: 2 [no certificate]
  RBM.Gauss.Sizes.LWExpI41K: 4 [no certificate]
  RBM.Gauss.Sizes.LWExpG5': 4 [no certificate]
registry: 2 borrowed + 147 owed + 90 structural + 7 refuted; 114 registered premise(s) carry nothing yet: [...]
pre exit 0
```
The four lines are added to `owedProps` with comments. `LWCutExp` and `LWtermEXP` stay. `LWExpKer` is not flagged, so `structuralProps` is untouched, as the ticket specifies.

## 6. Compiled nonempty instances (`LWExpTerm2.lean:2064-2114`, `d = 3`, `sz0`, `z0`, `tInst = 1/16`)
- **Target 7 (endpoint):** `lwExpTerm2_inst_cut` is `inst_LWtermEXP (lwTermEXP_of_cut 3 (lwCutExp_of_terms 3 h1 h23 h41 h5)) hLE hLW hLmax hLK hDec`.
  - Hypotheses that remain: only the four term pins and the five ST laws (other gates' pins).
  - Discharged in the merged `inst_LWtermEXP` (`LWPins.lean:666`): `3 ≤ 3`, `κ = ε = 𝔡 = 1/10 > 0`, `flow_z0`, and `tInst_range`.
  - The index set `ĝ²/L³ ≤ 1 - tInst` is nonempty. Preflight `pre.py`, col. 9, gives `True` at n = 0, 1, 2, 5, 50.
- **Target 3:** `lwExpTerm2_inst_ker_SB`, `_ker_Kp` and `_ker_KK` have no hypothesis.
- **Targets 3-5 at `n = 0`** (`L = 4`, `W = 32`, `t = 1/16 > 0`): `_Kp_split`, `_conj`, and `_expand` (with `gaussIBP sz0` discharged), all with no hypothesis.
- **Targets 8, 9:** `lwExpTerm2_inst_G5`, `_I1` and `_I41`. Each has a single hypothesis, the unproved owed pin, which is the theorem's only premise.

None of these instances is degenerate: `N = 0`, an empty index set, a collapsed window or a `False` premise does not occur.

## 7. Paper deltas (prove report (d))
- **Ticket expected (a):** `J₄₂` needs an `S⁺` edge, `B:34`. Covered by `T2243a`, which also records that `I_i` and `J_i` merge into the kernel `m + m³S⁺`.
- **Ticket expected (b):** the all-`+` 5-loop and the `(+,+)` 2-loops at `σo = +`, `B:14`. Covered by `T2243b`.
- **Other Lean/paper differences:**
  - The explicit `η⁻¹ ≤ (2/√(2κ))(1-t)⁻¹` and `B ≤ 1`: `T2243c`.
  - `LWExpKer` taken `∀ n` through the finite patch: `T2243d`.
  - The general-`K` term pins are dispatcher pins, already described in `T2243a`.
- No uncovered difference was found.

## 8. Observations (no statement, instance, build, axiom or paper-delta effect)
- O1. Targets 5-6 deviate from the ticket's ten-term plan. `lwExpTerm2_cut_expand` gives 5 combined terms (`I_i + J_i`) with the kernel `KK = S^B(m + m³K⁺)` and `I₄₂ + J₄₂ = m·P_d[K⁺]`, using `lwExpTerm2_tKK` (from `Kp_split`).
  - `cut_expand` is an unpinned helper.
  - The pins are applied at `K = KK`, which is admissible because they quantify over all `LWExpKer` kernels.
  - `LWExpG5'` is used only at `p.1.1.1 = true`; the `S^B` branch serves target 8.
  - The prove report states the deviation (narrative, bullet 3). Recorded for the dispatcher's LW-14c/d planning: LW-14d needs the K-pins only at a kernel of the form `S^B·(…)`.
- O2. `lwExpTerm2_ker_Kp` assumes `t ≤ lemT z` and `3 ≤ d` rather than the ticket's literal `0 ≤ t < 1`. As noted in §2, every consumer has both.
- O3. **For the hub (merge rule (A) 3):** `main` has moved to d822fd7 since the branch point 25362ad, and the two-dot `git diff main t/T2243 -- RBM3D/Test/Axioms.lean` shows `+30/−73` because of other tickets' registry edits on `main`. Copying the branch's `Axioms.lean` would revert those edits. Bring in only the 4-line hunk: `git diff main...t/T2243 -- RBM3D/Test/Axioms.lean | patch --dry-run` applies cleanly to `main:RBM3D/Test/Axioms.lean` (`patch exit 0`). `LWExpTerm2.lean` is new, so it has no conflict.

## Verdict
| target | verdict |
|---|---|
| 1 vocabulary `LWExpKer`, `LWExpKp` | PASS (verbatim, `Iff.rfl`/`rfl`) |
| 2 pins `LWExpI1K`, `LWExpI23K`, `LWExpI41K`, `LWExpG5'` | PASS (verbatim; registered owed) |
| 3 kernel facts `ker_SB`, `ker_Kp`, `Kp_split` | PASS (O2) |
| 4 conjugation `cut_conj`, `norm_cut_false` | PASS |
| 5 expansion `cut_expand`, `cut_zero` | PASS (O1) |
| 6 identification | PASS (kernel-checked by defeq in target 7) |
| 7 `lwCutExp_of_terms` | PASS |
| 8 `lwExpG5_of_G5'` | PASS |
| 9 `lwExpI1_of_K`, `lwExpI41_of_K` | PASS |
| 10 instances | PASS |

**T2243: PASS.** No dispatcher sign-off needed. The hub should note O3 at merge.
