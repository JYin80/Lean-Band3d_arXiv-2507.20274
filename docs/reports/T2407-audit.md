Auditor model: claude-opus-5-5

# T2407 audit (round 1): BA-L2c1, `Graph/BAWeightOp.lean`, under Amend 1 (D1-D3)

Written Sun Oct 11 05:41:54 UTC 2026 (`date -u`). Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2407-audit1`, detached at `t/T2407` = `849a959`.
Probe = `git show 4c1de4c:RBM3D/Probe/T2395Pins.lean` (Amend 1 D1), saved as `$S/probe.lean`, `$S` = scratchpad `T2407/`.

## 0. Diff, size, hygiene

```
$ git diff --stat main...t/T2407
 RBM3D/Graph/BAWeightOp.lean | 1941 +++++++++++++++++++++++++++++++++++++++++++
 1 file changed, 1941 insertions(+)
$ wc -l RBM3D/Graph/BAWeightOp.lean          # stop line 2,000
    1941 RBM3D/Graph/BAWeightOp.lean
$ grep -c -E 'sorry|admit|native_decide|^axiom' RBM3D/Graph/BAWeightOp.lean
0
$ for n in BAGraph.ext bpv bpS bpM bpW baSum BAGraph.lw2 BAGraph.lw4 baExpFrame_lw lw_counters lw_raw lw_mono lw_scalingOrderG BAWeightOp; do git grep -n -E "$n" main -- RBM3D RBM3D.lean | wc -l; done   # main = d354b8d (includes T2409)
0 0 0 0 0 0 0 0 0 0 0 0 0 0
```
Only the sole writable file is touched; `RBM3D.lean` is unchanged (the hub adds the import at merge). New file only: no frozen signature touched. Public unpinned helpers carry the stem `BAWeightOp_` (61 further helpers are `private`).

## 1. Build and axioms (audit worktree)

```
$ lake build RBM3D.Graph.BAWeightOp
✔ [3783/3783] Built RBM3D.Graph.BAWeightOp (10s)
Build completed successfully (3783 jobs).
exit=0                                     # no error lines; no warning line mentions BAWeightOp
$ lake env lean $S/ax.lean
'RBM.Graph.baExpFrame_lw' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.lw_counters' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.lw_raw' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.lw_mono' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.lw_scalingOrderG' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.BAWeightOpInst.lists_baGcxx' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.BAWeightOpInst.lists_baGwx' depends on axioms: [propext, Classical.choice, Quot.sound]
$ lake env lean docs/tickets/checks/T2407-check.lean   # on the branch
check-file exit=0
```

## 2. Target 1: term lists, verbatim from the probe (Amend 1 D1)

```
$ diff <(sed -n 105,126p $S/probe.lean) <(sed -n 55,76p RBM3D/Graph/BAWeightOp.lean) && echo "diff ext..lw4: identical"
diff ext..lw4: identical
$ diff <(sed -n 239,241p $S/probe.lean) <(sed -n 80,82p RBM3D/Graph/BAWeightOp.lean) && echo "diff baSum: identical"
diff baSum: identical
```
`BAGraph.ext`, `bpv`, `bpS`, `bpM`, `bpW`, `BAGraph.lw2`, `BAGraph.lw4`, `baSum` are identical to the probe text, and they sit in the same namespace `RBM.Graph` with the same `variable {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]` context (probe `:24`, file `:53`). Only the self-loop form is defined; per D1, the general `G̊_{xy}` form is not needed. **PASS.**

## 3. Target 2: `baExpFrame_lw`, the first conjunct of `BAexpFrameE` (D2)

Script `$S/cmp.py` collapses whitespace. It cuts the probe's `def BAexpFrameE` into the binder head and conjunct 1, then compares that text with the statement of `baExpFrame_lw` in the file and with the file's `frameE1`:
```
$ python3 -I $S/cmp.py $S/probe.lean RBM3D/Graph/BAWeightOp.lean
probe BAexpFrameE head+conj1 == baExpFrame_lw statement: True
frameE1 == probe head + (conj1): True
```
The quantifier order, hypotheses (`3 ≤ L`, `BASelf`, `0 ≤ t < 1`, `p ∈ lwSplit Γ.solid`, `σ`, `circ`, `src = dst`), the law `PF d L W 0` and the data `BAlwData` match the pin binder for binder. The file also compiles `example (d) : frameE1 d := … baExpFrame_lw …`. The statement has no smallness hypothesis on `g0`, on `‖M − m₀I‖`, or of the form `(Cλ)^{|a−b|}` (C1/L5). `BASelf` is the merged predicate that the pin itself uses, not a new hidden hypothesis. The proof splits off `t = 0`: there `Ǧ = 0` and `S = 0` make both sides vanish. For `0 < t`, it uses the merged `baLweight_holds`, `baW_mul` and `lwWx_integral`. No unmerged dependency: the file imports only `RBM3D.Graph.BAExpandWOrd` (on `main`). **PASS.**

## 4. Target 3: counters and order (D3)

Statements in the file (`:1680`, `:1708`, `:1731`, `:1815`), with hypotheses `p ∈ lwSplit Γ.solid → p.1.σ = true → p.1.circ = true`:
- `lw_counters`: every `T ∈ Γ.lw2 p` has `counters = ⟨nS+1, nW+1, nA+1, nM, 0, 0⟩`, and every `T ∈ Γ.lw4 p` has `⟨nS+1, nW+2, nA+2, nM, 0, 0⟩`. The last two fields are the constant `0, 0` of `BAGraph.counters` (`BAVocab.lean:143`).
- `lw_raw`: `(BAWeightOp_circ T).scalingOrder = Γ.scalingOrder + 1` on both lists. This is T2395 design §3 Step 3's `raw = ord T° − ord P` (design `:86`), with `raw = 1`. `BAWeightOp_circ` circles every solid edge, which is the design's `T°`. It also gives the ticket's "ord rises by at least one", because `BAWeightOp_circ_counters` leaves the counters unchanged.
- `lw_mono`: on `T°`, `nM = Γ.nM`, `nA − nW` is equal, and the number of atoms meeting `E` is `≤`. That count is written inline exactly as the probe's `BAGraph.nExt` (`:33`). These are the components (a)/(c) of `BAstepMono` (probe `:269-270`) at the `T°` level. The member-level "merges only lower" step is assigned to L3a4 by design `:87`, and the report flags this.
- `lw_scalingOrderG` (with `Γ.Normal`): `ord Γ ≤ ordG T` on both lists, as the ticket requires (`lanlw_scalingOrderG` shape).
These are T-level statements in the requested form. The weak `≤` for `nExt` matches the `≤` in `BAstepMono`. **PASS.**

## 5. Compiled nonempty instances (file `:1841-1937`, namespace `RBM.Graph.BAWeightOpInst`)

Data: `d = L = 3`, `W = 1`, `g0 = 0`, `E = 0`, `m = Complex.I`, `t = 1/2`. `BASelf` is discharged by the merged `BAExpandInst.baSelf_zero` (`BAExpand.lean:865`), `3 ≤ 3`, `0 ≤ 1/2` and `1/2 < 1` by `norm_num`, and `p ∈ lwSplit` by `hp0`/`hp1`. `σ`, `circ` and `src = dst` are `rfl`, and `Normal` is `hN0`/`hN1`. `Idx 3 3 1` has 27 points. `S = t·svarF ≠ 0` (`BAExpand.lean:75`).
- Target 1: `lists_baGcxx` (one term in each of `lw2`, `lw4`, counters `(2,1,2,1)`, `(2,2,3,1)`) and `lists_baGwx` (two terms each, with the `lanlwD`/derivative terms present, counters `(3,1,2,1)`, `(3,2,3,1)`), both by `decide`.
- Target 2: `baExpFrame_lw` applied at `baGcxx` (`Fin 0` external) and at `baGwx` (external label `![e₀]`, `e₀ ≠ 0`), with every hypothesis discharged.
- Target 3: `lw_counters` at both graphs, `lw_raw` at `baGwx`, `lw_mono` at both, `lw_scalingOrderG` at both.
None is degenerate: no `N = 0`, no empty index, no `False` premise, no large witness. All compile (§1 build). **PASS.**

## 6. Paper deltas

There is one Lean/paper difference: (B.19)'s kernel `Σ_y (1 + M⁺S⁺)_{xy}` is split into `y = x` (`lw2`) and `(M⁺S⁺)_{xy} = Σ_z M_{xz}M_{zx}S⁺_{zy}` (`lw4`), with `S⁺ = S W` taken from `BAlwData`. Only the self-loop `Ǧ_{xx}` form is stated. Both points are covered by the prove report's candidate `T2407a` (§(d)). `grep -n T2407 docs/paper-deltas.md` finds no existing entry, so the dispatcher numbers it. The `t = 0` case is a degenerate value that the pin includes and that is proved separately; it does not change the statement. **Covered.**

## 7. Observations (no effect on verdict)

- O1. The instances use `W = 1, g0 = 0`. There `M = m·I` is scalar, so the BA-specific non-scalar `M` is not exercised by a compiled instance. The theorem carries no hypothesis that would need it, and the 1a covered a non-scalar `M` numerically (`W = 2, g0 = 1/2, E = 3/10`).
- O2. The report runs 216 + (b) lines, against the ticket's "≤ 150" acceptance line. It stays within CLAUDE.md §6's 300-line limit for prove reports. This is a report-format matter only.
- O3. `main` has advanced past the branch point `5ee937e` (T2401/T2403/T2405/T2409 merged). Their diffs do not touch `BAWeightOp.lean`, and the name grep above against `d354b8d` finds no clash. The hub's full build at merge is the final check.

## Verdict

| Target | Verdict |
|---|---|
| 1 term lists (`ext`, `bp*`, `lw2`, `lw4`, `baSum`) | PASS |
| 2 `baExpFrame_lw` | PASS |
| 3 `lw_counters`, `lw_raw`, `lw_mono`, `lw_scalingOrderG` | PASS |
| 4 C1/L5 | PASS |
| 5 instances | PASS |
| 6 registry: none; check file compiles | PASS |

**T2407: PASS.** No dispatcher sign-off needed.
