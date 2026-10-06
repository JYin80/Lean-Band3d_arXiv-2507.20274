Auditor model: claude-opus-5-5

# T2271 audit (UN-22, `RBM3D/Universality/UywKernel.lean`), round 1, Tue Oct  6 08:43:03 UTC 2026

Branch `t/T2271` at 4f0ce83 (merge-base with main f515695). Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2271-audit1` (detached).
Scratch files: `<scratchpad>/T2271/` (`T2271-auditcheck.lean`, `reg.lean`, `build.log`, `check.out`, `reg.out`).

## 1. Scope of the diff
```
$ git diff --name-only main...t/T2271
RBM3D/Universality/UywKernel.lean
$ git diff --stat main...t/T2271 -- RBM3D/Test/Axioms.lean | wc -l
0
$ grep -n "^import" RBM3D/Universality/UywKernel.lean
6:import RBM3D.Universality.JakKernel
$ grep -nE "sorry|admit|native_decide|^axiom" RBM3D/Universality/UywKernel.lean | wc -l
0
$ grep -nE "^\s*(structure|class|instance|axiom|opaque)" RBM3D/Universality/UywKernel.lean
(no output)
```
Only the sole writable file. No registry line (matches the ticket's expectation). Imports only `JakKernel`. No structure or class, so no hypothesis hidden in a field. 1470 lines, under the ticket's 1500 split threshold.

## 2. Build and axioms (audit worktree)
```
$ lake build RBM3D.Universality.UywKernel      (exit=0)
Build completed successfully (3331 jobs).
$ grep -E "^(warning|error).*UywKernel" build.log | wc -l
0
$ grep "UywKernel.lean" build.log
1456:0: 'RBM.Univ.blockM2_self' depends on axioms: [propext, Classical.choice, Quot.sound]
1457:0: 'RBM.Univ.blockM2_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
1458:0: 'RBM.Univ.green_spectral_identity_blockM2' depends on axioms: [propext, Classical.choice, Quot.sound]
1459:0: 'RBM.Univ.measure_bad2_le_of_queBadMat' depends on axioms: [propext, Classical.choice, Quot.sound]
1460:0: 'RBM.Univ.uyw_pointwise_good' depends on axioms: [propext, Classical.choice, Quot.sound]
1461:0: 'RBM.Univ.uyw_pointwise_crude' depends on axioms: [propext, Classical.choice, Quot.sound]
1462:0: 'RBM.Univ.UywKernelInst.blockM2_le_432' depends on axioms: [propext, Classical.choice, Quot.sound]
1463:0: 'RBM.Univ.UywKernelInst.inst_self' depends on axioms: [propext, Classical.choice, Quot.sound]
1464:0: 'RBM.Univ.UywKernelInst.inst_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
1465:0: 'RBM.Univ.UywKernelInst.inst_identity2' depends on axioms: [propext, Classical.choice, Quot.sound]
1466:0: 'RBM.Univ.UywKernelInst.inst_bad2' depends on axioms: [propext, Classical.choice, Quot.sound]
1467:0: 'RBM.Univ.UywKernelInst.inst_good' depends on axioms: [propext, Classical.choice, Quot.sound]
1468:0: 'RBM.Univ.UywKernelInst.inst_crude' depends on axioms: [propext, Classical.choice, Quot.sound]
```
Registry pre-check (`import RBM3D` + `import RBM3D.Universality.UywKernel` + `#assert_rbm_axioms`):
```
$ lake env lean reg.lean ; echo exit=$?
exit=0
axiom audit: 7922 theorems, 2614 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
All within [propext, Classical.choice, Quot.sound]; no project axioms: ...
```

## 3. Statements against the pin (check file `docs/tickets/checks/T2271-check.lean`)
Vocabulary, as a text diff:
```
$ diff <(sed -n '/^noncomputable def blockM2 /,/if α = β then 1 else 0))/p' T2271-check.lean) \
       <(sed -n '/^noncomputable def blockM2 /,/if α = β then 1 else 0))/p' UywKernel.lean) && echo identical
blockM2 body: identical
```
Elaboration check. `T2271-auditcheck.lean` is the dispatcher's check file with `import RBM3D.Universality.UywKernel` added. The check's `blockM2` is renamed `blockM2chk`, so every `T2271_*` body uses the library's `RBM.Univ.blockM2`. These lines are appended:
```
example : @blockM2chk = @RBM.Univ.blockM2 := rfl
example : T2271_blockM2_self := @RBM.Univ.blockM2_self
example : T2271_blockM2_eq := @RBM.Univ.blockM2_eq
example : T2271_green_spectral_identity_blockM2 := @RBM.Univ.green_spectral_identity_blockM2
example : T2271_measure_bad2_le_of_queBadMat := @RBM.Univ.measure_bad2_le_of_queBadMat
example : T2271_uyw_pointwise_good := @RBM.Univ.uyw_pointwise_good
example : T2271_uyw_pointwise_crude := @RBM.Univ.uyw_pointwise_crude
example : T2271_H1 = RBM.Univ.UywKernelInst.H1 := rfl
example : T2271_y0 = RBM.Univ.UywKernelInst.y0 := rfl
example : T2271_blockM2_le_432 := @RBM.Univ.UywKernelInst.blockM2_le_432
example : T2271_inst_self := RBM.Univ.UywKernelInst.inst_self
example : T2271_inst_bad2 := RBM.Univ.UywKernelInst.inst_bad2
example : T2271_inst_good := RBM.Univ.UywKernelInst.inst_good
example : T2271_inst_crude := RBM.Univ.UywKernelInst.inst_crude
-- consumer: target 4b applied at the UNUyw integrand data (H = ouMat (UNModel.band sz) n t ω,
-- lam = sz.lam n, u₁ = z i, u₂ = z j, hL := sz.three_le_L n, hH := ouMat_isHermitian _ n t ω)
example : ∀ d sz n nf t ω z s i j y b₁ b₂, (∀ k, 0 < (z k).im) → <check §3 shape> :=
  fun ... hz => RBM.Univ.uyw_pointwise_crude (sz.three_le_L n) (sz.lam n) (ouMat_isHermitian _ n t ω) nf s z (z i) (z j) (hz i) (hz j) hz y b₁ b₂
$ lake env lean T2271-auditcheck.lean ; echo exit=$?
exit=0
$ grep -c error check.out
0
```
Every pinned target and instance is accepted against its check body. The consumer shape of check §3 is discharged by target 4b with `3 ≤ L` from `Sizes`. So the target-4 left side matches the `UNUyw` integrand token for token.

Mathematical reading of the statements:
- **`blockM2` (vocabulary).** It is the `2d+1`-weight `SBR` average with `δ_{αβ}`, as pinned. `blockM2_eq` proves it equals `N ∑_x ψ_α(x) conj ψ_β(x) S°_{xy}`, the paper's pair moment. So the redefinition is pinned to the paper's quantity by a proved identity, not by a docstring.
- **Target 1a (`blockM2_self`).** No hypotheses. It is the diagonal identity with the merged `blockM`.
- **Target 1b (`blockM2_eq`).** It needs only `3 ≤ L`, which the row sum `sum_SBR_row` requires. It holds for every `lam` and every `d`.
- **Target 2 (`green_spectral_identity_blockM2`).** It needs `3 ≤ L`, `0 < Im z₁`, `0 < Im z₂`, and holds for all `σ₁, σ₂`. The product form `p*p` and `Gres*Gres` matches `UNUyw`.
- **Target 3 (`measure_bad2_le_of_queBadMat`).** Its hypotheses (`3 ≤ L`, `1 ≤ W`, `0 < 𝔡`, `(eq:WO)` `W^{-d/2+𝔡} ≤ lam`, a per-block `queBadMat` bound `≤ p`) are those of the merged `measure_bad_le_of_queBadMat`. The parameters are `(ε₀, c) = (𝔡/3, 𝔡/6)`, window `N⁻¹W^{𝔡/3}` and threshold `W^{-𝔡/6}`, and the constant is `2d+1`. These match `UNOUQUE`'s `queBadMat … (𝔡/3) (𝔡/6) E a`.
  - The only probabilistic hypothesis is the per-block bound, which the ticket requires. It is a hypothesis of the theorem, not a hidden premise.
- **Targets 4a/4b.** The binders are the RBM2D shape with `lam` explicit after `hL`, and `N = (W L)^d`. No `3 ≤ d` hypothesis and no `L`–`W` relation (§29 (3)).

No circular dependency: the new file imports only merged `JakKernel` (closure `JakSpectral`, `Pins`, `Sizes`, `FineModel`, `Gap`, `Props4`, `GLoopFlow`). It states no pin.

## 4. Compiled nonempty instances (same file, `UywKernelInst`, `d = 3`, `L = 3`, `W = 2`, `N = 216`)
| target | instance | data and discharge |
|---|---|---|
| 1a | `inst_self` | `H1 = 1`, `lam = 1/2`, `a₀ = 0`, `α = y0` |
| 1b | `inst_eq` (extra) | `y0`, `α = y0 ≠ β = y1`, `3 ≤ 3` by `norm_num` |
| 2 | `inst_identity2` (extra) | `z₁ = z₂ = I`, `σ = (true,false)`, `0 < I.im` |
| 3 | `inst_bad2` | `dirac ()`, `𝔡 = 1/10`, `lam = 1`, `E = 0`, `p = 1`; `hlam` by `rpow_le_one_of_one_le_of_nonpos`, `hp` by `prob_le_one` |
| 4a | `inst_good` | `θ = 432` (`hBad` from `blockM2_le_432`, a proved bound), `Ag = 107352`, `Ab = 864` (`hAg`, `hAb` by `norm_num`), grid events by `JakKernelInst.gridGood_one` |
| 4b | `inst_crude` | `u₁ = u₂ = w 0 = I`, `s = {0}` |
| 4a/4b | two `example`s at `H2 = diag((x 0).val)` (non-scalar) | `u₁ = 1/2+i`, `u₂ = -1+i`, `Bad a ↔ a = 0` (nontrivial `if`) |

Every deterministic hypothesis is discharged. No `N = 0`, no empty index, no `False` premise (`Bad ≡ False` is a predicate parameter, not a premise), and the witnesses are not astronomically large.

In `inst_bad2`, `p = 1` makes the conclusion `≤ 7` weak but it is the pinned instance, and every hypothesis, including `(eq:WO)`, is discharged at the concrete data. The ticket accepts this as an instance of a union bound whose per-block probability is hypothesised.

## 5. Name clashes (`git grep -nw <name> main -- 'RBM3D/*.lean' RBM3D.lean | wc -l`)
```
blockM2: 0  blockM2_self: 0  blockM2_eq: 0  green_spectral_identity_blockM2: 0
measure_bad2_le_of_queBadMat: 0  uyw_pointwise_good: 0  uyw_pointwise_crude: 0  UywKernelInst: 0
blockM2_le_432: 0  inst_self: 0  inst_eq: 0  inst_identity2: 0  inst_bad2: 0  y1: 0
inst_good: 2  inst_crude: 2  H2: 30  H2_herm: 5   (all in other namespaces, e.g. JakKernelInst; the full names in RBM.Univ.UywKernelInst are fresh)
```

## 6. Paper deltas
The prove report §(d) proposes **T2271a**, the design/portmap note: line estimate 1170 → 1470, and the `2d+1`-weight `δ_{αβ}` form of `blockM2` against RBM2D's `1/5` average. This is the candidate the ticket anticipated. The targets are deterministic layers of `(uywy7723r3rf)` (`1_2:569-577`) and state no paper theorem. The one form difference, the `d ≥ 3` `blockM2`, is covered by T2271a, and `blockM2_eq` ties it to the paper's `N ∑_x ψ_α conj ψ_β S°_{xy}`. No uncovered statement difference.

## 7. Observations (no effect on the verdict)
- O1. Some public names are not in the pin: `UywKernelInst.y1`, `H1_herm`, `inst_eq`, `inst_identity2`, `H2`, `H2_herm`. They live in the ticket-mandated instance namespace `RBM.Univ.UywKernelInst`, which carries the file stem, so this is acceptable under §3 (E) / TEAM §9.6.
- O2. Since branching, main has advanced from f515695 to c22b80b. The three-dot diff still touches only the sole writable file. The full `lake build` at merge is the hub's job.
- O3. Not targets, as the ticket says: the pins `UNUyw`, `UNJakUywRow`, `UNUywk`, `UNJakUywRowk`, `UNJakUywRowBA` stay owed, and the registry is unchanged.

## Verdict
| target | verdict |
|---|---|
| 1 `blockM2`, `blockM2_self`, `blockM2_eq` | PASS |
| 2 `green_spectral_identity_blockM2` | PASS |
| 3 `measure_bad2_le_of_queBadMat` | PASS |
| 4a `uyw_pointwise_good`, 4b `uyw_pointwise_crude` | PASS |
| 5 instances `blockM2_le_432`, `inst_self`, `inst_bad2`, `inst_good`, `inst_crude` | PASS |

**T2271: PASS.** No dispatcher sign-off needed.
