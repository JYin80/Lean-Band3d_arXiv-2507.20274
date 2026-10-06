Auditor model: claude-opus-5-5

# T2293 (UN-41) audit, round 1. `date -u`: Tue Oct  6 12:46:22 UTC 2026
Branch `t/T2293` at `408c53a`; main at `1ba63a2`. Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2293-audit1` (detached).
Scratch files: `<scratchpad>/T2293/` (`audit_pins.lean`, `ax.lean`, `reg.lean`, `a.txt`/`b.txt`).

## 1. Diff scope, hygiene, build
```
$ git diff --name-status main...t/T2293
A	RBM3D/Universality/GUEPhase/EntryTail.lean
$ grep -cE 'sorry|admit|native_decide|^axiom' RBM3D/Universality/GUEPhase/EntryTail.lean
0
$ lake build RBM3D.Universality.GUEPhase.EntryTail 2>&1 | grep -E "error|Build completed"
Build completed successfully (3360 jobs).
```
Only the sole writable file (new) is touched; `RBM3D/Test/Axioms.lean` untouched; no merged file or frozen signature changed.

## 2. Axioms (all 102 public `theorem`/`def`/`structure` names of the file, extracted by awk)
```
$ lake env lean ax.lean > ax.out; echo exit=$?      # 102 `#print axioms` lines
exit=0
$ grep -o "depends on axioms: .*" ax.out | sort | uniq -c
 101 depends on axioms: [propext, Classical.choice, Quot.sound]
   1 depends on axioms: [propext, Quot.sound]
```
Registry pre-check (`import RBM3D` + `import RBM3D.Universality.GUEPhase.EntryTail` + `#assert_rbm_axioms`):
```
$ lake env lean reg.lean > reg.out; echo exit=$?
exit=0
axiom audit: 8499 theorems, 2793 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
$ grep -c error reg.out; grep -cE "GUEEntryMix|MixProfOK|EntryTail|mixMat" reg.out
0
0
```
No premise-ledger entry names this module; no registry line is owed (matches the ticket's expectation).

## 3. Statements against the pins (compiled)
`audit_pins.lean` = `import RBM3D` + the module + check file lines 145-379 copied verbatim + one `example` per T2293 pin
(`intro …; exact RBM.Univ.<target> …`) + the four vocabulary examples.
```
$ diff <(sed -n '145,379p' docs/tickets/checks/T2293-check.lean) <(sed -n '3,237p' audit_pins.lean) && echo VERBATIM_OK
VERBATIM_OK
$ lake env lean audit_pins.lean 2>&1 | grep -v "^warning\|linter\|^Note"; echo exit=$?
exit=0
```
Pins closed by the library theorem (21): `T2293_mixMat_isHermitian`, `_ouMat_eq_mixMat`, `_mixMat_zero_right`,
`_mixMat_zero_left`, `_mixMat_eq_Xmat_mixSample`, `_measurable_mixSample`, `_measurable_mixMat`, `_mixSample_law`,
`_ouP_mixSample_preimage`, `_mixEntry_mixVar_coe`, `_mixEntry_sigRow_gvarF`, `_mixEntry_sigRow_mixVar`,
`_mixEntry_mixVar_diag`, `_mixEntry_Smix_diag_pos`, `_mixProfOK`, `_mixEntry_quad_tail`, `_mixEntry_row_tail`,
`_mixEntry_col_tail`, `_mixEntry_diag_tail`, `_mixEntry_greenBlk_eq`, `_mixEntry_det`.
Vocabulary: `mixMat … = mixMatV …` (`rfl`), `mixSample … = mixSampleV …` (`rfl`), `GUEEntryMix d ↔ GUEEntryMixV d`
(`Iff.rfl`), `MixProfOK v S ↔ MixProfOKV d L W v S` (field-wise, both directions). Each `exact` uses only the
pin's own hypotheses; no extra hypothesis was needed, so no target is a special case of its pin.

`GUEEntryMix` against its RBM2D source (`c9a24cf:…/EntryTail.lean:112-131` vs `EntryTail.lean:94-113`):
```
$ diff a.txt b.txt   (abridged to the changed tokens)
< def GUEEntryMix : Prop :=
<   ∀ 𝔠 : ℝ, 0 < 𝔠 → ∀ d : Sizes, Admissible 𝔠 d → ∀ κ : ℝ, 0 < κ →
> def GUEEntryMix (d : ℕ) : Prop :=
>   ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 → ∀ κ : ℝ, 0 < κ →
<   (∀ n, K n ≤ (d.size n) ^ n0) → …            > (∀ n, K n ≤ (sz.size n) ^ n0) → …
<     ouP (d.L n) (d.W n) {ω | … Idx (d.L n) (d.W n) …
>     ouP (UNModel.band sz) n {ω | … Idx d (sz.L n) (sz.W n) …
<               (mixMat (d.L n) (d.W n) (a n k) (b n k) ω) + (((d.W n : ℕ) : ℝ) ^ 2)⁻¹) <
>                 (mixMat sz n (a n k) (b n k) ω) + (((sz.W n : ℕ) : ℝ) ^ d)⁻¹) <
```
The only changes are the ticket's import map and d ≥ 3 list: carrier, `Admissible` (it contains `0 < 𝔠`, `0 < 𝔡`,
`WO 𝔡`), `W^{-2} ↦ W^{-d}`. Quantifier order (fixed parameters before `∀ᶠ n`), `K n ≤ N^{n0}`, `N^τ`, `N^{-D}`,
`δ ≤ N^{-c₀}` and the a priori event are unchanged. `3 ≤ d` is not in the pin (as pinned).

`mixEntry_det` hypotheses: `3 ≤ d`, `3 ≤ L`, `M` Hermitian, `0 < g ≤ Λ`, `0 < κ`, `|E| ≤ 2-κ`, `0 ≤ a, b`,
`0 < a+b < 1`, `llErr ≤ δ ≤ mixDelta d Λ κ`, `1 ≤ Φ`, `36Φδ² ≤ 1`, four LDE inputs at `Smix d L W g a b`;
conclusion `llErr² ≤ mixCdet d Λ κ · Φ² · maxLoopPM`: identical to `T2293_mixEntry_det` (compiled above).

## 4. Vacuity, hidden hypotheses, cycles
- `MixProfOK` (structure, fields `symm`/`off`/`diag`) is the pinned profile hypothesis of the four tails, equal to
  `MixProfOKV` (§3); it is discharged at the real profile by `mixProfOK` and in every tail instance. Not hidden.
- `GUEEntryMix` is a `Prop` definition; no theorem of the file assumes it
  (`grep -n GUEEntryMix EntryTail.lean`: only the definition `:94` and docstrings `:18`, `:85`). It is proved in T2293b.
- The file imports only `RBM3D.Universality.GUEPhase.EntryDet` (merged, 7a8a4eb); every dependency is merged;
  no assumed-and-unproved premise (registry output §2). No cycle.
- No external hypothesis is introduced (§95 (4): no ML input).

## 5. Compiled nonempty instances (namespace `RBM.Univ.EntryTailCheck`, all in the module build of §1)
Read in the file (`:920-1415`); every endpoint has an instance with each hypothesis discharged:
| target | instance | data |
|---|---|---|
| `mixMat_isHermitian`, `ouMat_eq_mixMat`, `mixMat_zero_{right,left}`, `mixMat_eq_Xmat_mixSample`, `measurable_mix{Mat,Sample}` | `inst_…` | `sz0`, `n = 0` (`L = 4`, `W = 32`), `(1/4,1/4)`, `t = 1` |
| `mixSample_law`, `ouP_mixSample_preimage` | `inst_mixSample_law`, `inst_ouP_mixSample_preimage` | `sz0`, `n = 0`, `(1/4,1/4)` (`0 ≤ a, b` by `norm_num`), `A = univ` |
| profile identities, `mixProfOK` | `inst_mixEntry_*`, `inst_mixProfOK` | `Idx 3 3 2` (`N = 216`), `g = 1`, `(1/4,1/4)`, `0 ≠ ![1,0,0]` (`inst_x1_ne`, `decide`) |
| four tails | `inst_mixEntry_{quad,row,col,diag}_tail` (+ `_sharp`, `λ = Λ = 4`, `q = 0`) | `v = mixVar 3 3 2 1 (1/4) (1/4)` (`mixVar_tagFree`), `S = Smix …`, `z = zt 0 (1/2)` (`Im = 1/2`, proved), `Λ = lam = 2`, `q = 1` |
| `mixEntry_greenBlk_eq` | `inst_mixEntry_greenBlk_eq` | `E = 0`, `u = 1/2`, `M = 0` |
| `mixEntry_det` | `inst_mixEntry_det` (ticket form, LDE inputs as hypotheses) and `inst_mixEntry_det_full` | full: `M = 0`, `E = 0`, `g = Λ = κ = 1`, `Φ = 256`, `δ = min (mixDelta 3 1 1) (1/100) > 0`, `u = δ/(1+δ) ∈ (0,1)`, `(a,b) = (u/2,u/2)`; `llErr ≤ δ`, row/col/quad/diag inputs proved in `inst_det_zero` |
`inst_mixEntry_det_full` has no hypotheses (statement `(i j : Idx 3 3 2) : llErrMat … ≤ mixCdet 3 1 1 * 256^2 * maxLoopPM …`).
No instance uses `N = 0`, an empty index type, a collapsed window or a `False` premise. `GUEEntryMix` is a definition
(its instance is T2293b's `inst_entryMix`).

## 6. Name clashes
```
$ for x in <102 public names>; do git grep -wn "$x" main -- 'RBM3D/*.lean'; done | wc -l
names=102 hits_in_main=0
```

## 7. Paper-delta coverage
| Lean/paper difference | covered by |
|---|---|
| carrier `ouP (UNModel.band sz) n` with coupling `sz.lam n`; `sz.Admissible 𝔠 𝔡` in `GUEEntryMix` | `T2293a` (prove report (d)) |
| error term `W^{-d}` (RBM2D `W^{-2}`), slack | `T2293b` (prove report (d)) |
| class T split: band here, BA in BA-C3; tails kind-free | `T2293c` (prove report (d)) |
| `mixEntry_det`: `0 < g ≤ Λ`, `L`-free `mixDelta/mixCdet d Λ κ` | merged D589 (T2278a-c, `docs/paper-deltas.md:1548`) |
| quadratic tail at shift `A = 0` of `gaussLaw_quad_tail` | merged D484 (T2196a, `:1443`) |
| rename `mixEntry_sigRow_gvar ↦ mixEntry_sigRow_gvarF` | name only, no statement delta (ticket) |

## 8. Observations (no effect on statement, instance, build, axioms or delta coverage)
- O1: at the ticket's tail data (`Λ = lam = 2`, `q = 1`) the quad/row/col bounds are `≥ 1`; the file adds `_sharp`
  instances with bounds `1/2`, `2/9`. Not required, recorded only.
- O2: the prove report's registry counts (8476 theorems) differ from the count here (8499) because main advanced
  since the prover's run; the ledger contains no name of this module either way.

## 9. Verdicts
| target | verdict |
|---|---|
| `mixMat`, `mixMat_isHermitian`, `ouMat_eq_mixMat`, `mixMat_zero_right`, `mixMat_zero_left` | PASS |
| `GUEEntryMix d` (definition) | PASS |
| `mixSample`, `measurable_mixSample`, `mixMat_eq_Xmat_mixSample`, `measurable_mixMat` | PASS |
| `mixSample_law`, `ouP_mixSample_preimage` | PASS |
| `mixEntry_mixVar_coe`, `mixEntry_sigRow_gvarF`, `mixEntry_sigRow_mixVar`, `mixEntry_mixVar_diag`, `mixEntry_Smix_diag_pos` | PASS |
| `MixProfOK`, `mixProfOK`, `mixEntry_minor_eq`, `mixEntry_meas_*` | PASS |
| `mixEntry_quad_tail`, `mixEntry_row_tail`, `mixEntry_col_tail`, `mixEntry_diag_tail` | PASS |
| `mixEntry_relabel_*` | PASS |
| `mixEntry_greenBlk_eq`, `mixEntry_det` | PASS |

**Overall: PASS.** No dispatcher sign-off needed.
