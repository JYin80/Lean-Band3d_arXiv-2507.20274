Auditor model: claude-opus-5-5

# T2390 audit, round 1 (stage 2 after 1b; BA-G3a `RBM3D/BA/GreenCore.lean`): Sun Oct 11 00:47:29 UTC 2026

Inputs: ticket `docs/tickets/T2390.md`, Amend 1 (D2: `BAGbEXPii'` not pinned, merged `BAGbEXPii` stands in, T2390d), prove report (a), (a″), (a′), (b)-(d), 1a-audit round 2 (PASS). Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2390-audit1`, detached at `e34b6d6` (= `t/T2390`). Merge base with main: `5d3d24b`; main = `d859e60`.

**Verdict: PASS** (all G3a targets). No dispatcher sign-off needed.

## 1. Build, axioms, hygiene, scope (audit worktree)
```
$ lake build RBM3D.BA.GreenCore 2>&1 | tail -2; echo exit=$?
Build completed successfully (3777 jobs).
exit=0
$ grep -c "declaration uses 'sorry'" build.out ; grep -c error build.out
0
0
$ grep -nE "\b(sorry|admit|axiom|native_decide)\b" RBM3D/BA/GreenCore.lean RBM3D/Probe/T2390Pins.lean; echo grep-exit=$?
grep-exit=1
$ # ax.lean = import RBM3D.BA.GreenCore + `#print axioms RBM.BA.<n>` for every `theorem`/`def` of the file (84)
$ lake env lean ax.lean > ax.out; echo exit=$?; grep -c "" ax.out; grep -c "depends on axioms: \[propext, Classical.choice, Quot.sound\]$" ax.out
exit=0
84
84
$ grep -E "BAStab'|BAGbEXPij''|GreenCore_(diag|coupled|Xstar|Xi|Rbound)'" ax.out
'RBM.BA.GreenCore_Rbound' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.GreenCore_Xstar' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.GreenCore_Xi' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BAStab' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.GreenCore_coupled' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.GreenCore_diag' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BAGbEXPij'' depends on axioms: [propext, Classical.choice, Quot.sound]
$ lake env lean docs/tickets/checks/T2390-check.lean > check.out 2>&1; echo check-exit=$?; grep -c error check.out
check-exit=0
0
$ printf 'import RBM3D\nimport RBM3D.BA.GreenCore\n#assert_rbm_axioms\n' > pre.lean; lake env lean pre.lean > pre.out; echo pre-exit=$?; grep -E "BAStab:|BAGbEXPij':" pre.out
pre-exit=0
  RBM.BA.BAStab: 1 [no certificate]
  RBM.BA.BAGbEXPij': 0 [no certificate]
$ wc -l < RBM3D/BA/GreenCore.lean          # stop line 2000
    1981
$ git diff --stat main...HEAD
 RBM3D/BA/GreenCore.lean     | 1981 +++
 RBM3D/Probe/T2390Pins.lean  |  176 ++++
 RBM3D/Test/Axioms.lean      |    2 +
 docs/reports/T2390/inst.out |    4 +
 docs/reports/T2390/inst.py  |   14 +
 docs/reports/T2390/sz0.out  |    3 +
 docs/reports/T2390/sz0.py   |    7 +
$ git diff main...HEAD --name-only | grep -vE "^(RBM3D/BA/GreenCore.lean|RBM3D/Test/Axioms.lean|RBM3D.lean|RBM3D/Probe/T2390Pins.lean|docs/reports/T2390/.*)$"; echo outside-exit=$?
outside-exit=1
$ grep -E "^(theorem|def|abbrev) " RBM3D/BA/GreenCore.lean | awk '{print $2}' | grep -v '^GreenCore_'
BAStab
BAGbEXPij'
$ git grep -n -e GreenCore -e BAStab -e "BAGbEXPij'" main -- RBM3D RBM3D.lean | wc -l
       0
```
Every file is a sole writable file of the ticket: the 1a files are the probe and `docs/reports/T2390/*`, the 1b files are `GreenCore.lean` and `Test/Axioms.lean`. No existing declaration is edited, so no frozen signature is touched. The `Test/Axioms.lean` diff adds exactly two `owedProps` lines (`BAStab`, `BAGbEXPij'`). Every public name is either pinned or carries the `GreenCore_` stem (§3 (E)).

## 2. Statements against the pins and the 1a mathematics
**Pins (`BAStab`, `BAGbEXPij'` with its three defs) against the probe that the 1a-audit round 2 PASSed** (whitespace-collapsed `def` blocks):
```
$ python3 -I pd.py RBM3D/Probe/T2390Pins.lean RBM3D/BA/GreenCore.lean
BAGbEXPij' identical
BAStab identical
GreenCore_decayConcl DIFF: [('(STblk', '(Sizes.STblk'), ('(STblk', '(Sizes.STblk')]
GreenCore_decayRHS identical
GreenCore_loopPrem identical
$ grep -rn "def STblk" RBM3D; grep -n "^open" RBM3D/Probe/T2390Pins.lean
RBM3D/Induction/Defs.lean:73:def STblk (n : ℕ) (x : Idx d (sz.L n) (sz.W n)) : Zd d (sz.L n) :=   (namespace RBM.Gauss.Sizes, :57)
RBM3D/Probe/T2390Pins.lean:31:open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes
```
Both spellings name the same constant `RBM.Gauss.Sizes.STblk`, so the pins are identical to the audited probe. I re-read `BAGbEXPij'` (`GreenCore.lean:1644-1657`) against `7_8:1916-1946`:
- order: `∀ κ ε 𝔡`, then `∃ c > 0`, then `∀ 𝔠 sz z`, `BAFlow`, `t ∈ [0, T₀]`, `ε₀ > 0`, `D > 0`;
- windows: `0 < Φ ≤ W^{-ε₀}` and `W^{-d/2} ≤ Ψ ≤ W^{-ε₀}`;
- the premise is `1_Ω 𝓛^{(2)}_{(-,+)} ≺ Φ²`; the conclusion is `Σ Φ e^{-c(|a'-a|+|b'-b|)} + Ψ e^{-c|a-b|} + W^{-D}` in `zdistInf`.

Its differences from the paper are the event form, `x ≠ y`, the order of `c` and the dropped `(initialGT2)` premise; T2390a, e and f cover them. `BAGbEXPii'` is absent, as Amend 1 D2 decides.

**1b targets (row map G.8 / (a′): R1-R5)**, read from the signatures (`targets.py` output in (b) of the prove report, re-checked by line):
| row | Lean (line) | against the 1a | verdict |
|---|---|---|---|
| R1 | `E1` 84, `E1'` 115, `E0` 755, `E2` 642, `Delta_col` 780, `Delta_row` 1214, `E3` 1253 | exact identities (E0)-(E3), (E1′) of G.2; hypotheses are only the resolvent identities, Kronecker `M`, `M_aa = m`, `G_uu ≠ 0` | PASS |
| R2 | `m1` 400, `Xrow_sq` 450, `Xcol_sq` 468, `eps1_loc` 563, `eps2_loc` 584, `Qxd_sq` 702, `Arow_four` 729, `Acol_sq` 796, `crude` 501, `apriori` 524, `Xcol_avg` 855 | (m1), (L1), the `ε`, `Q^{XD}`, `X_ww` bounds of (a′) D3.1. LDE inputs are the per-sample events `LDERow/LDECol/LDEQuad … (svar … 0) Φ` and `‖X_ii‖² ≤ Φ svar_ii`: the four components of `BALDEin` (`GreenLDE.lean:84-105`) with `Φ` in place of `≺` | PASS |
| R3 | `twoSided` 903, `Rstar` 320, `Rbound` 972, `Xstar` 1066, `Xi` 1130 | (R1), (R*), (X*), (Ξ) of (a′) D3.2-D3.3. The closure is local (kernel `e^{-(c₀/2)|c-b''|}`, no `sup R`), under `(C1) 8ρ c₀⁻¹S ϑ ≤ 1` (`GreenCore_theta`, 965). (X*) holds for all `u, y`, stronger than (a′)'s `u ≠ y` | PASS |
| R4 | `coupled` 1276, `diag` 1361 | `‖Δ‖ ≤ ρ(1+ρ₂K_Θ)‖𝒦‖` from (E3) and the stability hypothesis; the diagonal law on `Ω ∩ LDE` with `K_BA δ ≤ 1/2`, `‖G-M‖²_max ≤ 8K_BA²((9/4)A_b + X_b)`, linear in `(max 𝓛, W^{-d})`. Stability enters only as `BAStab` (G3b's owed pin) | PASS |
| R5 | `BAStab` 1268, `BAGbEXPij'` 1644, registry lines | as pinned (above) | PASS |

C1 check. The hypotheses about `M` across R2-R4 are the following:
- Kronecker `hM`, `hMd`;
- `κ ≤ ‖m‖ ≤ 1`, `‖Mb‖ ≤ 1`;
- `hdec` (`c₀⁻¹e^{-c₀|a-b|}`);
- the `ℓ¹` sums `hρ`, `hS`, `hρ₂`;
- `D = g₀Ψ` with `0 ≤ g₀`.

No hypothesis is of the form `g ≤ W^{-ε}`, smallness of `‖M − m₀I‖`, or `(Cλ)^{|a-b|}`.

## 3. Vacuity, hidden hypotheses, cycles
- The file defines no `structure` or `class`. Every hypothesis is an explicit argument. `GreenCore_carrier` (1532) proves the resolvent and Kronecker identities of the BA carrier from `BAFlow`; it assumes none of them.
- No theorem assumes `BAGbEXPij'`, `BAGbEXPii` or `BAStab` as a Prop to prove itself. `BAStab` is only a hypothesis of `diag`, and is owed to G3b. No cycle.
- External hypotheses: none new. `BALDEin` is merged (T2389, `baLDEin_holds`). Its events enter as the deterministic `LDE*` hypotheses.

## 4. Compiled nonempty instances (same file; they compile in the build of §1)
`example` lines: 1659 1915 1917 1919 1921 1923 1925 1927 1930 1931 1932 1933 1934 1937 1938 1941 1943 1947 1953 1958 1962 1968 1973.

The data are `d = 3`, `sz0` at `n = 3` (`L = 16`, `W = 32768`), the merged flow `FlowPinsInst.flow_sz0` (`κ = 1/2, ε = 1/10, 𝔠 = 1/6, 𝔡 = 1/10`), and the actual BA carrier (`GreenCore_Gc = blockMat BAGt …`).

- R1 (1915-1927) holds at `t = 1/2` for **every** sample `ω`.
- R2-R4 (1930-1973) hold at the sample `ω₀ = 0` (`X = 0`), `t₁ = 10⁻¹¹ > 0`. The constants are `Φ = 1`, `δ = 2·10⁻⁷`, `ρ = S = 4096`, `ρ₂ = 1`, `K_Θ = 256`, and `K_BA δ = 4096·257·2·10⁻⁷ ≈ 0.21 ≤ 1/2`.
  - `G ≠ M` is proved (`iΔ`, 1902).
  - Every deterministic hypothesis is discharged by a proof term: `Om`, `iwd`, `iLDE`, `iC1n`, `kern` (from `BAMB_decay_large` and Ward), `loop_le`.
  - `BAStab … t₁ 256` is proved (`istabBA`, 1861), not assumed.
- R5 (1659) instantiates `BAGbEXPij' 3` at `sz0`, `flow_sz0`, `t ≡ 1/2 ≤ T₀`, `ε₀ = 1/10`, `Φ ≡ W^{-1/10}`, `Ψ = W^{-1}`. The windows, `BAFlow` and `t`-range are discharged. The owed pin itself and `GreenCore_loopPrem` (the paper's premise `(eq:def_Psit)`) stay hypotheses, as §4 step 2 allows.

None of the instances is degenerate: `N > 0`, the index set is nonempty, the window `[W^{-3/2}, W^{-ε₀}]` is nonempty, no premise is `False`, and no witness is astronomically large. Amend 1 D4 is met: `t > 0`, `Δ ≠ 0`, numeric `K`, `ρ`, `δ` with `Kδ ≤ 1/2`.

## 5. Paper deltas
The candidates are T2390a-g (1a: (G.9), (a″), (a′); T2390d from Amend 1) and T2390h, j, k, l, m (1b, (d); T2390i withdrawn). Each Lean/paper difference of the targets is covered:
- the pin shape (a, e, f);
- `BAGbEXPii` standing in (d);
- the stability constant and the `BAStab` form (b, k);
- the rate `c_λ` and the unused `W^{-D}` (g);
- the constants of (R*) and (C1) (h);
- the deterministic diagonal law with the uniform loop bound `Lm` (j);
- (X*) and (Ξ) with their constants (l, m).

No entry in `docs/paper-deltas.md` has a T2390 tag yet (`grep -n T2390 docs/paper-deltas.md`: no output). The dispatcher appends them.

## 6. Observations (no RETURN)
- **O1 (merge: important for the hub).** `RBM3D/Test/Axioms.lean`: main moved from the merge base `5d3d24b` to `d859e60` and **removed** three `owedProps` lines (`BAEKSumDecay1`, `BAEKSumDecayNAL`, `BAEKSumDecay2`). Copying the branch file would bring those lines back. Apply only the branch's 2-line hunk (`git merge-tree --write-tree main t/T2390`: exit 0, clean).
- **O2.** Do not merge `RBM3D/Probe/T2390Pins.lean`: it is a 1a probe, "never merged". `docs/reports/T2390/*` are 1a report scripts.
- **O3.** The R2-R4 instances use the zero sample `X = 0`. At that sample the left sides of `Xrow_sq`, `Xcol_sq` and `Xstar` vanish, so their conclusions are trivially true there. The hypotheses are still met jointly at `Δ ≠ 0`, `t > 0`. The prover discloses this ((d).1). An `X ≠ 0` sample satisfying the LDE events is not exhibited.
- **O4.** `twoSided` uses `ϑ = α² + 26κ⁻²Φδ²` (from the a priori `R ≤ (13/4)δ²`), where (a′) D3.2 has `8κ⁻²`. The constant enters `(C1)` through `GreenCore_theta`; covered in spirit by T2390h.
- **O5.** `diag`'s right side is of order `K_BA²Φ²(max𝓛 + W^{-d})`: `R0` carries `Φ`, and `X_b` multiplies it by `Φ`. G.3 states `Φ`. This is an `N^τ` loss under `≺`; covered by T2390j.
- **O6.** The registry pre-check above ran in the audit worktree. There, `import RBM3D` comes from the copied main build cache, so its premise count (121) differs from the prover's (124). Exit 0 either way. The hub's full build at merge is authoritative.
