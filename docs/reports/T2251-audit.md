Auditor model: claude-opus-5-5
# T2251 audit (UN-19, `Universality/JakSpectral`), round 1 — Tue Oct  6 04:19:22 UTC 2026

Branch `t/T2251` at b9e249e; main at 9403c24 (ancestor of the branch); audit worktree
`/Users/junyin/Lean_proof/RBM3D-wt/T2251-audit1` (detached at b9e249e). Ticket `docs/tickets/T2251.md`,
check `docs/tickets/checks/T2251-check.lean`, prove report `docs/reports/T2251-prove.md`.

**Verdict: PASS** (all 12 targets and the 5 instances of target 6).

## 1. Scope of the diff
```
$ git diff --stat main...t/T2251
 RBM3D/Universality/JakSpectral.lean | 675 ++++++++++++++++++++++++++++++++++++
 1 file changed, 675 insertions(+)
$ git diff main...t/T2251 -- RBM3D/Test/Axioms.lean | wc -l
       0
$ grep -nE "sorry|admit|native_decide|^axiom|^\s*axiom " RBM3D/Universality/JakSpectral.lean; echo grep-exit=$?
grep-exit=1
```
Only the sole writable file is touched; `Axioms.lean` untouched (as the ticket expects); no frozen file
changed. Imports: `RBM3D.Universality.Pins` and three Mathlib modules only (file lines 6-9).

## 2. Build and axioms (audit worktree)
```
$ lake build RBM3D.Universality.JakSpectral
ℹ [3329/3329] Built RBM3D.Universality.JakSpectral (5.6s)
Build completed successfully (3329 jobs).
exit=0
$ grep -c "warning: RBM3D/Universality/JakSpectral" build.log
0
$ grep "depends on axioms" build.log   (17 lines, all identical axiom set)
:657 'RBM.Univ.Gres_sq_apply_self' depends on axioms: [propext, Classical.choice, Quot.sound]
:658 'RBM.Univ.Gres_apply_self_spectral' depends on axioms: [propext, Classical.choice, Quot.sound]
:659 'RBM.Univ.Gres_sq_apply_self_spectral' depends on axioms: [propext, Classical.choice, Quot.sound]
:660 'RBM.Univ.spectralGsigPole_norm_eq_spectralPole' depends on axioms: [propext, Classical.choice, Quot.sound]
:661 'RBM.Univ.isOrthoEigenbasis_eigenvectorBasis' depends on axioms: [propext, Classical.choice, Quot.sound]
:662 'RBM.Univ.blockM_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
:663 'RBM.Univ.blockM_eq_unMy' depends on axioms: [propext, Classical.choice, Quot.sound]
:664 'RBM.Univ.green_spectral_identity_blockM' depends on axioms: [propext, Classical.choice, Quot.sound]
:665 'RBM.Univ.norm_green_spectral_identity_blockM_le' depends on axioms: [propext, Classical.choice, Quot.sound]
:666 'RBM.Univ.sum_norm_blockM_le' depends on axioms: [propext, Classical.choice, Quot.sound]
:667 'RBM.Univ.unBadY_of_blockM' depends on axioms: [propext, Classical.choice, Quot.sound]
:668 'RBM.Univ.measure_bad_le_of_queBadMat' depends on axioms: [propext, Classical.choice, Quot.sound]
:669 'RBM.Univ.JakSpectralInst.inst_spectral' depends on axioms: [propext, Classical.choice, Quot.sound]
:670 'RBM.Univ.JakSpectralInst.inst_block' depends on axioms: [propext, Classical.choice, Quot.sound]
:671 'RBM.Univ.JakSpectralInst.inst_identity' depends on axioms: [propext, Classical.choice, Quot.sound]
:672 'RBM.Univ.JakSpectralInst.inst_mass' depends on axioms: [propext, Classical.choice, Quot.sound]
:673 'RBM.Univ.JakSpectralInst.inst_bad' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## 3. Statements against the pins (elaboration diff, strongest form)
Scratch file `AuditCheck.lean` (scratchpad `T2251/`, 266 lines, uncommitted): `import RBM3D` +
`import RBM3D.Universality.JakSpectral`; check section 2.1 copied verbatim into `RBM.Univ.T2251Check` and
shown definitionally equal (`rfl`) to the library vocabulary; check sections 2.2-2.7 copied verbatim into
`RBM.Univ.T2251Audit` (where `blockM`, `spectralPole`, … resolve to the library names) and each pin
`T2251_<name>` inhabited by the library theorem `@<name>` with no proof term in between; then each instance
applied at `Matrix.isHermitian_one`; then `#assert_rbm_axioms`.
```
-- 2.1 vocabulary (check body = library body)
example … : T2251Check.blockM d L W lam hH a0 α = RBM.Univ.blockM d L W lam hH a0 α := rfl  -- same for spectralPole, spectralGsigPole, siteBlock
example : T2251_Gres_sq_apply_self := @Gres_sq_apply_self
example : T2251_Gres_apply_self_spectral := @Gres_apply_self_spectral
example : T2251_Gres_sq_apply_self_spectral := @Gres_sq_apply_self_spectral
example : T2251_spectralGsigPole_norm_eq_spectralPole := @spectralGsigPole_norm_eq_spectralPole
example : T2251_isOrthoEigenbasis_eigenvectorBasis := @isOrthoEigenbasis_eigenvectorBasis
example : T2251_blockM_eq := @blockM_eq
example : T2251_blockM_eq_unMy := @blockM_eq_unMy
example : T2251_green_spectral_identity_blockM := @green_spectral_identity_blockM
example : T2251_norm_green_spectral_identity_blockM_le := @norm_green_spectral_identity_blockM_le
example : T2251_sum_norm_blockM_le := @sum_norm_blockM_le
example : T2251_unBadY_of_blockM := @unBadY_of_blockM
example : T2251_measure_bad_le_of_queBadMat := @measure_bad_le_of_queBadMat
example : T2251_H1 = JakSpectralInst.H1 := rfl
example : T2251_y0 = JakSpectralInst.y0 := rfl
example : T2251_a0 = JakSpectralInst.a0 := rfl
example : T2251_inst_spectral := JakSpectralInst.inst_spectral
example : T2251_inst_block := JakSpectralInst.inst_block
example : T2251_inst_identity := JakSpectralInst.inst_identity
example : T2251_inst_mass := JakSpectralInst.inst_mass
example : T2251_inst_bad := JakSpectralInst.inst_bad
-- nonvacuity: instances applied at the concrete Hermitian witness
example := JakSpectralInst.inst_spectral Matrix.isHermitian_one
example := JakSpectralInst.inst_block Matrix.isHermitian_one
example := JakSpectralInst.inst_identity Matrix.isHermitian_one
example := JakSpectralInst.inst_mass Matrix.isHermitian_one
example := JakSpectralInst.inst_bad (fun _ => Matrix.isHermitian_one)
end RBM.Univ.T2251Audit
$ lake env lean AuditCheck.lean; echo exit=$?      (error/warning/sorry lines: none)
exit=0
axiom audit: 7491 theorems, 2542 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
premises found by scanning: 154 (borrowed 1, owed 102, structural 38, refuted 6, superseded 7).
registry: 2 borrowed + 155 owed + 98 structural + 7 refuted + 7 superseded; …
```
Every target statement is the check pin exactly (up to `Type*` for `Type`, which `@name` instantiates at
universe 0); the instance data `H1`, `y0`, `a0` equal `T2251_H1`, `T2251_y0`, `T2251_a0` by `rfl`. Importing
`RBM3D` and the new module together elaborates: no public name of the file clashes with the library.
The registry pre-check passes (exit 0, owed count 155 unchanged because `Axioms.lean` is unchanged).

Mathematical reading of the pins against the ticket:
- 1a-1e: `Gres H w true * Gres H w true`, `Gres H z σ` (pole at `z` or `z̄`), any finite `n`; 1a needs
  `∀ α, λ_α ≠ w`, 1b/1c need `0 < Im z` (the `UNJak` window gives it). Matches ticket design rows 1-2.
- 2a/2b: `blockM` = `∑_b SBR d L lam b a₀ ((N/W^d) ∑_{x∈[b]} |ψ_α(x)|² - 1)` (2d+1 weights, ticket (b));
  only `3 ≤ L`, every `lam`, no `3 ≤ d`. 2b links to merged `unMy` (`Pins.lean:1139-1141`).
- 3a/3b: left side is the `UNJak` integrand `(Gres M z b₁ * Gres M z b₁) x x * scirc … x y * Gres M z b₂ y y`
  token for token (check section 3 consumer `example` also elaborates on main per the release check).
- 4: `∑_α ‖M_{a₀,α}‖ ≤ 2 * ((W L)^d : ℕ)`, constant `2N` explicit.
- 5a: window `(((W*L)^d:ℕ):ℝ)⁻¹ * W^(𝔡/3)` and threshold `W^(-(𝔡/6))` coincide token for token with
  `UNBadY` (`Pins.lean:1147-1150`); 5b has exactly the hypotheses of the merged `unBadY_measure_le`
  (`Pins.lean:1320-1325`: `3 ≤ L`, `1 ≤ W`, `0 < 𝔡`, `W^(-d/2+𝔡) ≤ lam`, per-block `queBadMat` bound `p`) and
  the same conclusion constant `(2d+1) p`; it is the general restatement, not a special case.

## 4. Hidden hypotheses, vacuity, cycles
- New defs `spectralPole`, `spectralGsigPole`, `siteBlock`, `blockM` are not `Prop`; no structure/class.
- No owed, refuted or superseded pin appears as a hypothesis of any new theorem (statements in §3); the
  only `Prop` from the registry in a statement is the structural `queBadMat` inside a measure bound (5b)
  and `UNBadY` as the conclusion of 5a.
- Dependencies: merged `Pins` + Mathlib; 5b = `measure_mono` (5a) + merged `unBadY_measure_le` (`:568-570`).

## 5. Compiled nonempty instances (target 6, file `:573-655`)
Data `d=3, L=3, W=2` (`N=216`), `H=1`, `y=a₀=0`, `z=I`, `lam=1/2` (`1` in `inst_bad`); hypotheses discharged:
- `inst_spectral`, `inst_block`, `inst_identity`, `inst_mass`: `λ_α ≠ I` from `I.im ≠ 0`; `0 < I.im`; `3 ≤ 3`.
- `inst_bad`: `P = Measure.dirac ()`, `Hr ≡ 1`, `𝔡 = 1/10`, `E = 1`, `p = 1`; `3 ≤ 3`, `1 ≤ 2`, `0 < 1/10`
  by `norm_num`; `2^(-3/2+1/10) ≤ 1` by `Real.rpow_le_one_of_one_le_of_nonpos`; per-block bound by
  `prob_le_one`.
The instances quantify the Hermitian proof (`∀ hH`), as the check pins 2.7 do; §3 above applies each at
`Matrix.isHermitian_one` and compiles, so none is vacuous. No `N = 0`, empty index, collapsed window or
`False` premise.

## 6. Paper deltas
- Lean statements = ticket pins (§3); the only paper-level reading, the `S^{(B)}`-weighted `M_{y,α}` with
  `2d+1` blocks, is already in `docs/paper-deltas.md:1341` (D382, T2162a).
- Design-table candidate T2251a (portmap row UN-19 counts merged UN-01 items; RBM2D
  `measure_bad_le_of_queBadMat` restated at `UNBadY` data) is proposed in prove report `(d)` line 278.

## 7. Observations (no effect on verdict)
- O1. `inst_bad` takes `p = 1`, so its conclusion (`δ(·) ≤ 7`) is also true trivially; the instance still
  applies 5b at nondegenerate data with every hypothesis discharged, exactly as the ticket pins it.
- O2. Private helpers `I_im_ne`, `I_im_pos` (`:582-584`) lack the `JakSpectral_` prefix; `private` suffices (§3 (E)).

## Verdict per target
| target | statement | instance | build/axioms | verdict |
|---|---|---|---|---|
| 1a-1e (`Gres_sq_apply_self`, `Gres_apply_self_spectral`, `Gres_sq_apply_self_spectral`, `spectralGsigPole_norm_eq_spectralPole`, `isOrthoEigenbasis_eigenvectorBasis`) | = pin | `inst_spectral` | ok | PASS |
| 2a-2b (`blockM_eq`, `blockM_eq_unMy`) | = pin | `inst_block` | ok | PASS |
| 3a-3b (`green_spectral_identity_blockM`, `norm_green_spectral_identity_blockM_le`) | = pin | `inst_identity` | ok | PASS |
| 4 (`sum_norm_blockM_le`) | = pin | `inst_mass` | ok | PASS |
| 5a-5b (`unBadY_of_blockM`, `measure_bad_le_of_queBadMat`) | = pin | `inst_bad` (5a through 5b) | ok | PASS |
| 6 (`inst_*`) | = check 2.7 | applied at `isHermitian_one` | ok | PASS |

No dispatcher sign-off needed.
