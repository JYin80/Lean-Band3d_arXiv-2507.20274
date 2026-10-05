Auditor model: claude-opus-5-5

# T2177 audit (round 1) — Mon Oct  5 06:01:33 UTC 2026

Branch `t/T2177` at `dc24260`; audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2177-audit1` (detached).
Source: RBM2D `c9a24cf` (`Universality/OU.lean`, `Universality/EigenMeasurable.lean`), read by `git show`.

## 1. Scope of the diff
```
$ git diff --name-only main...t/T2177
RBM3D/Universality/EigenMeasurable.lean
RBM3D/Universality/OU.lean
```
Both are the ticket's sole writable files (new). No frozen signature is touched.

## 2. Build and axioms (audit worktree)
```
$ lake build RBM3D.Universality.OU RBM3D.Universality.EigenMeasurable   (exit 0)
info: OU.lean:306:0: 'RBM.Univ.ouSample_law' depends on axioms: [propext, Classical.choice, Quot.sound]
info: OU.lean:307:0: 'RBM.Univ.ouMat_zero_map' depends on axioms: [propext, Classical.choice, Quot.sound]
info: OU.lean:308:0: 'RBM.Univ.seqXmat_map_eq_ouMat_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
info: OU.lean:302..305: isProbabilityMeasure_ouP, ouMat_eq_Xmat_ouSample, measurable_ouSample,
      measurable_ouMat: [propext, Classical.choice, Quot.sound] (each)
info: EigenMeasurable.lean:589:0: 'RBM.Univ.eigenvalues₀_abs_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound]
info: EigenMeasurable.lean:590:0: 'RBM.Univ.measurable_corrSum' depends on axioms: [propext, Classical.choice, Quot.sound]
info: EigenMeasurable.lean:591:0: 'RBM.Univ.measurable_kPoint_eigenvalues' depends on axioms: [propext, Classical.choice, Quot.sound]
info: EigenMeasurable.lean:592:0: 'RBM.Univ.integral_kPoint_eq_of_map_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
Build completed successfully (3331 jobs).
warnings (new files only): unusedSectionVars/unused hypothesis linter at EigenMeasurable.lean:292,295
  (private helper, ported verbatim); `dif_pos` deprecated at :407, :442; flexible `simp [Hw]` at :524.
$ grep -nE "\bsorry\b|\badmit\b|^axiom|native_decide" RBM3D/Universality/{OU,EigenMeasurable}.lean
(no output; exit 1)
```

## 3. Statements against the source (script `stmt.py`: extract, whitespace-normalise, compare)
```
ouSample_law DIFFERS
  RBM2D: theorem ouSample_law {t : ℝ} (ht : 0 ≤ t) : (ouP L W).map (ouSample L W t) = Measure.infinitePi (fun c => gaussianReal 0 (ouVar L W t c)) :=
  RBM3D: theorem ouSample_law (sz : Sizes d) (n : ℕ) {t : ℝ} (ht : 0 ≤ t) : (ouP (UNModel.band sz) n).map (ouSample sz n t) = Measure.infinitePi (fun c => gaussianReal 0 (ouVar d (sz.L n) (sz.W n) (sz.lam n) t c)) :=
ouMat_zero_map DIFFERS
  RBM2D: theorem ouMat_zero_map : (ouP L W).map (ouMat L W 0) = (P L W).map (Xmat L W) :=
  RBM3D: theorem ouMat_zero_map (M : UNModel sz) (n : ℕ) : (ouP M n).map (ouMat M n 0) = M.μ.map (M.H n) :=
measurable_corrSum IDENTICAL
measurable_kPoint_eigenvalues IDENTICAL
eigenvalues₀_abs_sub_le IDENTICAL
integral_kPoint_eq_of_map_eq IDENTICAL
```
Body of `EigenMeasurable` (source lines 30-482 vs branch 30-500):
```
$ diff <(sed -n 30,482p src_EM.lean) <(sed -n 30,500p RBM3D/Universality/EigenMeasurable.lean)
1d0   < noncomputable section          (moved above the namespace)
256d254 < open RBM.Endpoints           (kPoint now RBM.Univ.kPoint)
257a256 > (blank)
453a453,471 > instance section (EigenMeasurableCheck: A3, B3, ...)
```
`kPoint` (RBM3D `Pins.lean:77`) vs RBM2D `Endpoints.lean:202`: bodies identical
(`(card ι)^k / descFactorial * Σ_{f : Fin k ↪ ι} O (fun j => card ι * (lam (f j) - E))`).

Reading of the two differences:
- `ouSample_law`: the RBM3D carrier is the merged pin `ouP M n = M.μ.prod (gueP d (L n) (W n))` on
  `SeqΩ sz × Ω` (`Pins.lean:145`). `ouSample` reads the first factor through `slice sz n`; `seqP_map_slice`
  (`FineModel.lean:184`) gives `(seqP sz).map (slice sz n) = PF d (L n) (W n) (sz.lam n)`, so the coupling
  `g = sz.lam n` in `ouVar` is the variance profile `gvarF` of the size-`n` band law. Variance
  `e^{-t} S_c + (1-e^{-t}) N⁻¹_c`, `0 ≤ t`, as in the source; `N = (W L)^d` via `gueVar` (`Pins.lean:61`).
  Stated for `UNModel.band sz` only: the same model as the RBM2D source (`P L W`); an abstract `M` has
  no Gaussian law. Covered by candidate `T2177a`.
- `ouMat_zero_map`: a generalisation to every `UNModel` (uses `M.meas`, `ouMat_zero`); the source's band
  form is `seqXmat_map_eq_ouMat_zero` (`(UNModel.band sz).H = seqXmat sz`). Covered by `T2177b`.
- Signature changes of the helpers `measurable_ouMat`, `ouSample`, ... covered by `T2177c`.
No `d = 2` dependence: the EigenMeasurable statements are over a generic `Fintype ι`; OU uses `Zd`-based `Idx d`.

## 4. Hidden hypotheses, vacuity, cycles
- `UNModel` fields (`Pins.lean:104-111`): `μ`, `prob`, `H`, `herm`, `meas`: structural data of the model,
  no analytic assumption; discharged by `UNModel.band` (merged, T2174) in every instance.
- Endpoint hypotheses: `ht : 0 ≤ t` (`ouSample_law`); `hm`/`hmeas : Measurable`, `hH : Hermitian`,
  `hO : Continuous O` (measurability endpoints). No external hypothesis, no borrowed pin.
- Imports: `OU` <- `RBM3D.Universality.Pins` (merged f8ad4b4) + Mathlib; `EigenMeasurable` <- `OU` + Mathlib.
  No cycle; all dependencies merged.

## 5. Compiled nonempty instances (in the files; compiled by the build in §2)
| Endpoint | Instance (file:line) | Data |
|---|---|---|
| `ouSample_law` | `OU.lean` OUCheck examples, `t = 1`, `1/2`, `0` | `UNModel.band sz0`, `n = 0` (`d = 3`, `L = 4`, `W = 32`, `N = 128^3`); `ht` by `zero_le_one`/`norm_num`/`le_rfl` |
| `ouMat_zero_map` | `OU.lean` OUCheck example | `UNModel.band sz0`, `n = 0` |
| `measurable_corrSum` | `EigenMeasurable.lean:527-530`, `:539-545` | `Hw w = [[1,w,0],[w,2,0],[0,0,3]]` on `Fin 3`, `k = 2`, `O = exp(-x0²-x1²)`; and `𝐇_1` of `UNModel.band sz0` |
| `measurable_kPoint_eigenvalues` | `EigenMeasurable.lean:533-535`, `:548-551` | same, `k = 2`, `E = 0` |
`Fin 2 ↪ Fin 3` is nonempty (6 embeddings); `ouVar_one_gue_weight_pos` proves the GUE weight is `> 0` at `t = 1`.
All deterministic hypotheses (`measurable_Hw`, `Hw_herm`, `O2_cont`, `measurable_ouMat`, `ouMat_isHermitian`)
are proved terms. No `N = 0`, empty index, collapsed window or `False` premise. Ticket's requested
instances (`band sz0`, `n = 0`; `k = 2`) are present.

## 6. Paper deltas
Every Lean/source statement difference (§3) is proposed in the prove report §(d) as `T2177a`, `T2177b`,
`T2177c`. `grep -n T2177 docs/paper-deltas.md`: no entry yet (dispatcher appends on merge).

## 7. Observations (no RETURN)
- Instance-section names `OUCheck.ouVar_zero`, `OUCheck.ouVar_one_gue_weight_pos`, `EigenMeasurableCheck.A3`,
  `B3`, `Hw`, `Hw_herm`, `measurable_Hw`, `T3aStmt(_holds)`, `T3bStmt(_holds)` are public, inside
  file-stem namespaces (`OUCheck`, `EigenMeasurableCheck`), so §3 (E) is met by the namespace prefix.
- Prove report: RBM2D HEAD `9e0f275` moved since `c9a24cf` (diff --stat pasted); the port is against `c9a24cf`.
- Lint warnings listed in §2 (deprecated `dif_pos`, flexible `simp`) do not affect statements.

## Verdict
| Target | Verdict |
|---|---|
| `ouSample_law` | PASS |
| `ouMat_zero_map` | PASS |
| `measurable_corrSum` | PASS |
| `measurable_kPoint_eigenvalues` | PASS |

Overall: **PASS**. No dispatcher sign-off needed.
