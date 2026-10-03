Auditor model: claude-opus-5-5

# T2063 audit (round 1) — S1-31 `Induction/ConArgDet` (WardResolvent + ConArgDet port)

`date -u`: Sat Oct  3 19:47:52 UTC 2026. Worktree `RBM3D-wt/T2063-audit1` at `t/T2063` = `e4d26e2` (base `2be5aaf`).

## 0. Diff scope

```
$ git diff --name-only main...t/T2063
RBM3D/Induction/ConArgDet.lean            (new, 1611 lines; sole writable file; Test/Axioms.lean untouched)
$ grep -n import RBM3D/Induction/ConArgDet.lean     (EntryCore: ST1-COMMON item 11, `green` imported)
6:import RBM3D.Induction.Split  7:import RBM3D.Loop.GLoop  8:import RBM3D.Green.EntryCore  9:import Mathlib.Algebra.Order.Chebyshev
$ grep -n "sorry\|admit\|^axiom\| axiom \|native_decide\|^structure\|^class\|set_option\|opaque" ConArgDet.lean
(no output)
```

## 1. Statements (script diff against the ticket's pin = RBM2D `c9a24cf` statements, renamed by ST1-COMMON item 2)

Script `sd.py` (own; comments stripped; every non-private `theorem/lemma/def/abbrev` of RBM2D
`Hierarchy/WardResolvent.lean` + `Induction/ConArgDet.lean` at `c9a24cf` vs the new file, text up to `:=`,
whitespace-normalised; rename map `BlockIndex L W→Vtx d L W`, `Z2 L→Zd d L`, `gloop L W→loopL d L W`,
`{gloopProd,gchain,gchainMixed,Eblk,loopMax,IsGLoopProd,blockCols,blockSel} L W→… d L W`, `LoopIdx→Loop.LoopIdx`,
`(W:ℂ)⁻¹^2→((W:ℂ)^d)⁻¹`, `(W:ℝ)⁻¹^2→((W:ℝ)^d)⁻¹`, `(W:𝕂)^2→(W:𝕂)^d`, `Fin W × Fin W→Fin (W^d)`,
`Gauss.spectralZ→zt`, `Gauss.spectralM→mE`, `Path.etaT→Gauss.etaT`, `Gsig→Gres`):
```
MISSING Gsig_eq_green_zSig / MISSING Gsig_eq_add_smul_mul / MISSING Gsig_mul_conjTranspose   (3 lines, joined)
2D 59 3D 59 same 55 differ 1
DIFF gchainMixed
 2D: (L W : ℕ) [NeZero L] [NeZero W] (H : Matrix (Vtx d L W) …) (z w : ℂ) (τ : List Bool) (a : List (Zd d L)) (l : ℕ) : …
 3D: (d L W : ℕ) [NeZero L] [NeZero W] (H : Matrix (Vtx d L W) …) (z w : ℂ) (τ : List Bool) (a : List (Zd d L)) (l : ℕ) : …
3D only ['Gres_eq_green_zSig', 'Gres_eq_add_smul_mul', 'Gres_mul_conjTranspose']
```
The three MISSING are the three `3D only` `Gres_*` (name follows `Gsig→Gres`; read by hand: statements equal after
the map). The only residual difference is the added binder `d`. No declaration dropped (59 = 59).

The five key targets, RBM2D `c9a24cf` vs RBM3D (read side by side):
- `green_sub_green` (WR:25 → :73) identical; `sum_gloop_ward_last_div` (WR:159 → :312) denominator `2i W^2 Im z →
  2i W^d Im z`, hypotheses `hz, hz', hη : z.im ≠ 0, hμ` unchanged; `ztTilde_arith` (CAD:537 → :850) `∃ C > 0, ∀ E t₁ t₂`,
  quantifier order kept (`C = C(c, κ)`); `trace_gram_rpow_le` (CAD:834 → :1147) `W^2 → W^d`;
  `loopMax_two_mul_le_tilde` (CAD:1019 → :1334) dimension-free, constant `m+1`.

Against the paper: `WI_calL` (`1_2:1036-1042`) is `Σ_{a_n} 𝓛^{(n)} = (2i W^d η_t)^{-1}(𝓛^{(n-1)}_{(+,σ₂..)} − 𝓛^{(n-1)}_{(−,σ₂..)})`
for `σ₁ = −σ_n`, `n ≥ 2`. The Lean statement is `σ = (+, μ, −)`, `n = |μ|+2 ≥ 2`, factor `W^d` (correct for
`E_a = W^{-d}1_{[a]}`, `GLoop.lean:55`), `Im z` in place of `η_t` (= `Im z_t`). The case `σ₁ = −, σ_n = +` is not
stated: a special case of `WI_calL` — exactly the ticket's pin (RBM2D's statement), and declared in report (d) `T2063a`.

`d`-dimensional exponents: every `W^2`/`W^{-2}` of the pinned statements became `W^d`/`W^{-d}` (diff above); no
`ℓ_t`, `N`, or `zdist` enters any target statement. All statements are proved in Lean for every `d`, so none is
"false at `d ≥ 3` as ported".

Import cut `Path/Scales`: RBM2D uses only `Path.etaT` from it.
```
$ git -C ../RBM2D show c9a24cf:RBM2D/Path/Scales.lean | grep -n "def etaT"
38:def etaT (E u : ℝ) : ℝ := (1 - u) * (spectralM E).im
$ sed -n 75p RBM3D/Loop/GLoop.lean
noncomputable def etaT : ℝ := (1 - t) * (mE E).im
```
Same definition; it is the merged MD-layer `RBM.Gauss.etaT`, so no ST-2 helper is needed (observation O1).

Statement verdict: all five targets match the pin.
## 2. Hidden hypotheses, vacuity, cycles

- No `structure`/`class` (grep above). Only new `Prop` def: `IsGLoopProd` (`:894`), internal, produced by
  `isGLoopProd_one`/`IsGLoopProd.mul`, not a hypothesis of any target. Target hypotheses are all deterministic
  (`IsUnit`, `IsHermitian`, `0 < Im`, `1 ≤ m, p`, lengths, `0 < c, κ`); no external hypothesis; imports merged only.
- Reuse list of the ticket: `loopMax_odd_sq_le`, `norm_gloop_le_of_le_abs_im` are not duplicated
  (`grep -c` in ConArgDet.lean = 0; they stay at `Split.lean:598,757`); `norm_gloop_le_of_symIdx_le` is used from
  `Split.lean:563`. `gloop`/`Gsig` are not copied; statements use the merged general `loopL`/`Gres`/`loopMax`
  (`GLoopFlow.lean:74,123`, `Split.lean:515`), the same objects as T2033; bridges `Gsig_eq_Gres`, `gloop_eq_loopM`,
  `loopM_eq_loopL` exist (`GLoopFlow.lean:86,96,~127`) for S1-32.

Name clashes of the 59 public names:
```
$ (loop over names.txt) grep -rnE "(theorem|lemma|def|abbrev) <name>( |$)" RBM3D, excluding ConArgDet.lean
clashes=0 of 59                              [audit worktree, base 2be5aaf]
$ (same) git grep … main -- RBM3D
clashes on main 9982c75: 0
```

## 3. Compiled nonempty instances (`section Checks`, `ConArgDet.lean:1352-1609`)

Data: `d = 3, L = 3, W = 2` (`Vtx 3 3 2`, 216 sites, 27 labels, block fibre `Fin 8`); `cad_Hd = diag(x.2)`
(values 0..7, Hermitian, not scalar); `z = zt 0 (1/2)`, `Im z = 1/2`; `w = ztTilde 0 (1/4) (1/2)`, `Im w = 3√2/4`. All discharged.
```
:1403 example … := green_sub_green (isUnit_sub_smul_one_of_im_ne_zero cad_Hd_herm cad_z_pos.ne')
                                   (isUnit_sub_smul_one_of_im_ne_zero cad_Hd_herm cad_im_w.ne')
:1413 example … := sum_gloop_ward_last_div 3 3 2 (…cad_z_pos.ne') (…(cad_conj_im_ne cad_z_pos)) cad_z_pos.ne'
                                   [false, true] 0 [0, 1] rfl                       -- loop of length 4, Σ over Zd 3 3
:1451 example : ∃ C > 0, (5 bounds at E = 1/2, t₁ = 1/4, t₂ = 1/2) :=
        ztTilde_arith (c := 1/4) (κ := 1) … applied with c ≤ t₁ ≤ t₂ ≤ 1, |1/2| ≤ 2 − 1
:1465 example … := loopMax_two_mul_le_tilde cad_Hd_herm cad_z_pos cad_im_w le_rfl le_rfl   -- m = 1, p = 1 (:1476 m = p = 2)
:1488 example … := trace_gram_rpow_le cad_Hd_herm cad_im_w rfl 0 le_rfl   -- τ = (+), b = 0, p = 1 (:1498 τ = (+,−), b = 2, p = 2)
:1571 private theorem cad_ward_div_value  (H = 0, z = i: value check of the W^{-d} = 1/8 factor)
```
No `N = 0`, empty index, collapsed window, `False` premise or large witness. Every endpoint theorem has an instance.

## 4. Build and axioms (audit worktree)

```
$ lake build RBM3D.Induction.ConArgDet
✔ [3301/3301] Built RBM3D.Induction.ConArgDet (5.0s)
Build completed successfully (3301 jobs).
$ lake env lean ax5.lean ; echo exit=$?
'RBM.green_sub_green' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.sum_gloop_ward_last_div' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Ind.ztTilde_arith' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Ind.trace_gram_rpow_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Ind.loopMax_two_mul_le_tilde' depends on axioms: [propext, Classical.choice, Quot.sound]
exit=0
$ lake env lean ax.lean | (count lines)        # #print axioms of all 59 public declarations
59 lines "depends on axioms: [propext, Classical.choice, Quot.sound]"
$ lake build RBM3D        # library at branch base, before registry pre-check:  Build completed successfully (3784 jobs).
$ lake env lean reg.lean ; echo exit=$?        # import RBM3D; import RBM3D.Induction.ConArgDet; #assert_rbm_axioms
axiom audit: 2216 theorems, 890 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
All within [propext, Classical.choice, Quot.sound]; no project axioms: …
premises found by scanning: 45 (borrowed 2, owed 31, structural 12).
exit=0
```
Premise count 45 = prove report's baseline (no new premise, no registry line). No existing file touched.

## 5. Paper deltas

| Lean/paper difference | Coverage |
|---|---|
| `sum_gloop_ward_last(_div)`: only `σ₁ = +, σ_n = −` of `WI_calL`; `Im z` for `η_t` | prove report (d) `T2063a` |
| ConArgDet is the deterministic part of `lem_ConArg` (fixed Hermitian `H`, `C_m = m+1`); probabilistic statement is S1-32 | `T2063b` |
| Ward lemmas for an arbitrary matrix `H` with `IsUnit` hypotheses (more general than `G_t`) | generalisation, no restriction; no delta needed |
| `lem_ConArg` only for `t < 1` | existing D26 (pin `STConArg`), not this file |

## 6. Observations (no statement/instance/build/axiom/delta effect)

- O1. The ticket asks for the `Path/Scales` helper to be copied `private`; the only helper is `Path.etaT`, which
  is definitionally the merged MD-layer `Gauss.etaT` (§1). Reusing it is the better choice; no ST-2 import.
- O2. 52 of the 59 public names are used only inside RBM2D's two files (report (d)); they stay public because
  the ticket says "every other public declaration is ported". Privatising is a dispatcher matter, not a defect.
- O3. Branch base `2be5aaf` is behind main `9982c75` (T2066, T2067 merged since); the diff adds one new file and
  no name clashes on main; the hub's full build at merge is the check.

## Verdict

| Target | Statement | Vacuity/hidden | Instance | Build/axioms | Deltas | Verdict |
|---|---|---|---|---|---|---|
| `green_sub_green` | = pin | none | :1403 | ok | n/a | PASS |
| `sum_gloop_ward_last_div` | = pin (`W^d`) | none | :1413 | ok | T2063a | PASS |
| `ztTilde_arith` | = pin | none | :1451 | ok | — | PASS |
| `trace_gram_rpow_le` | = pin (`W^d`) | none | :1488, :1498 | ok | T2063b | PASS |
| `loopMax_two_mul_le_tilde` | = pin | none | :1465, :1476 | ok | T2063b | PASS |

**T2063: PASS.** No dispatcher sign-off needed.
