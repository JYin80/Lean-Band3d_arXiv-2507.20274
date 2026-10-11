Auditor model: claude-opus-5-5

# T2415 audit (round 1) — Sun Oct 11 09:27:15 UTC 2026

Branch `t/T2415` @ 57fa504; audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2415-audit1` (detached).
**Overall verdict: PASS** (targets 1–4, 6; target 5 is "not here", target 7 "none").

## 1. Diff, size, hygiene
```
$ git log --oneline main..t/T2415
57fa504 T2415: BA Step 2 carrier baStep2Mat, baStep2Data, bridges, baStep2Fam (row T8-BA)
$ git diff --stat main...t/T2415
 RBM3D.lean            |   1 +
 RBM3D/BA/Step2BA.lean | 209 ++++++++++++++++++++++++++++++++++++++++++++++++++
$ git diff main...t/T2415 -- RBM3D.lean
@@ -451,6 +451,7 @@ import RBM3D.BA.GreenLocal
 import RBM3D.Graph.BASizeClaim2
+import RBM3D.BA.Step2BA
 /-! Hard axiom audit ... -/
 #assert_rbm_axioms                      (still last)
$ grep -nE "sorry|admit|native_decide|^axiom|implemented_by|extern" RBM3D/BA/Step2BA.lean | wc -l
       0
$ grep -rn "import RBM3D.BA.Step2BA" RBM3D RBM3D.lean
RBM3D.lean:454:import RBM3D.BA.Step2BA        (not in the certificate lane: no module imports it)
```
Only the two sole writable files; no merged file touched, so no frozen signature changed. 209 lines vs stop line 900.

## 2. Build and axioms (audit worktree)
```
$ lake build RBM3D.BA.Step2BA
✔ [3737/3737] Built RBM3D.BA.Step2BA (3.6s)
Build completed successfully (3737 jobs).        (0 error lines; no warning from Step2BA)
$ lake env lean docs/tickets/checks/T2415-check.lean ; echo $?
0                                                 (0 error lines)
$ lake env lean <scratch>/Ax.lean   (#print axioms of all 16 public decls + the instance inputs)
'RBM.BA.baStep2Mat' / '_toFlowFM' / '_LM' / '_GMM' / '_KI' / '_Hpath' / '_Pp'   depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baStep2Data' / '_toFlowFM' / '_T0' / '_flowOK'                         depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BAStep2_iff_STStep2G'                                                   depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baStep2Fam' / '_K' / '_m' / '_lam_pos_le'                               depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.FlowPinsInst.flow_sz0', 'RBM.BA.FlowPinsInst.t0_sz0'                    depends on axioms: [propext, Classical.choice, Quot.sound]
```
(18 lines printed verbatim, each `[propext, Classical.choice, Quot.sound]`; condensed here by name group.)

## 3. Target 1 `baStep2Mat sz lam0 E : Step2Mat sz` — PASS
Field-by-field against `Step2Mat` (`Chain/Step2Gen.lean:77-93`) and the BA objects (`BA/FlowPins.lean:250-305`):

| field | Lean (Step2BA.lean) | BA source | agreement (checked) |
|---|---|---|---|
| `toFlowFM` | `baFM sz lam0 E` (l.55) | `FlowPins:321` | `baStep2Mat_toFlowFM` rfl |
| `LM` | `loopFine … H (ztOf (BAmF …) (E n) u) σ a` (l.57) | `BALloop` = same at `H = seqHflowBA lam0 n t ω` | `baStep2Mat_LM` rfl |
| `GMM` | `Gres H z_u true x y - BAMfine …` (l.59) | `BAGM = BAGt - BAMfine` | `baStep2Mat_GMM` rfl |
| `LIM` | `loopL … (blockMat … H) z_u I` (l.61) | band `STLIM` (`Step2Defs:713`) with `zt E τ` → `z_u` | shape identical; same `z_u` as `LM` |
| `KI` | `BAKsol … (BAMsigma (BAMB (lam0 n) E_n m)) (PropSpin m) u I` (l.64) | `BAKloop` (`FlowPins:298`) | `baStep2Mat_KI` rfl at `KLloopOf σ a` |
| `Pp` (BAT-C1) | `pathP (sz.withLam 0)` (l.68) | law of `BAStep2`: `seqP (sz.withLam 0)`; `pathP` = `infinitePi` of `seqP` (`Walk:58`) | `baStep2Mat_Pp` rfl |
| `Hpath` (BAT-C1) | `(lam0 n) • PsiI + pathH (sz.withLam 0) s t K n k ω` (l.70) | `seqHflowBA` (`BlockAnderson:81-84`): `(lam0 n) • PsiI + seqHflow (sz.withLam 0)` | `baStep2Mat_Hpath` rfl; matches `pathH` docstring "add `ilambda_0 Ψ` and use `sz.withLam 0`" |

All types are fixed by `Step2Mat`; the definitions are data (no Prop fields), so nothing is hidden. The `show Matrix … from pathH …` cast in `Hpath` is a definitional retype (`(sz.withLam 0).L = sz.L`), not a change of content.

## 4. Target 2 `baStep2Data sz z : Step2Data sz` — PASS
```
123 def baStep2Data … where
124   toStep2Mat := baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)
125   T0 := BAflowT0 sz z
126   flowOK := fun κ ε 𝔠 𝔡 => BAFlow sz κ ε 𝔠 𝔡 z
127   flowOK_adm := fun h => h.1
128   flowOK_T := fun hκ h n => Step2BA_T0_lt_one hκ h n
129   L_swap := fun n t a b ω => Step2Gen_loopFine_swap _ _ a b
```
- Fields as pinned (`T0`, `flowOK`, `toStep2Mat`). The three facts are *proved* fields, not assumptions: `flowOK_adm` = first conjunct of `BAFlow` (`FlowPins:389-390`); `flowOK_T` from `BAt0_lt_one` with `0 < Im z_n` (`N^{-1+ε} ≤ Im z_n`, `rpow_pos_of_pos`) and `0 < Im m` (`κ ≤ Im m` of `BAdom`), using `0 < κ` exactly as the field's signature allows; `L_swap` reuses the private `Step2Gen_loopFine_swap` via `open private` (l.35), stated for arbitrary `H, z`, so model-free — the ticket asked to say which, and the file/report say "reused".
- No cycle: imports only `BA.FlowPins`, `Chain.Step2Gen`; no use of the T2414 drift kernel.

## 5. Target 3 bridges — PASS
```
$ python3 (normalize whitespace; compare ticket pin text with the statement of BAStep2_iff_STStep2G on t/T2415)
pin == lean: True
```
`BAStep2_iff_STStep2G := Iff.rfl` compiles; `baStep2Data_toFlowFM : … = baFMz sz z := rfl`, `baStep2Data_T0 : … = BAflowT0 sz z := rfl` compile (statements as pinned).

## 6. Target 4 energy family — PASS
`def baStep2Fam sz E : Step2Mat sz := baStep2Mat sz sz.lam E` (one line, as the ticket permits). Supporting rfl facts `baStep2Fam_K`
(`(baStep2Fam (sz.withLam lam0) E).K = (baFM sz lam0 E).K`), `baStep2Fam_m`, and the proved `baStep2Fam_lam_pos_le`
(`0 < g_n → 0 < g₀_n ≤ g_n` for `sz.withLam (BAflowLam0 sz z)`, from `BAt0_pos`, `BAg0_le`). The recipe for T3-BA (apply the pins at
`sz' = sz.withLam (BAflowLam0 sz z)`; `WO` is eventual in `n`) is recorded in the prove report (iv), (a′), (d). This is a design proposal for a
held ticket, not a statement claimed here.

## 7. Compiled nonempty instances (target 6) — PASS
File l.184-205, `d = 3`, `sz0` (`Defs/Sizes.lean:260`: `L_n = 4(n+1)`, `W_n = (2(n+1))^5`, `g_n = (2(n+1))^{-6}`), `z = zSeq`
(`FlowPins:1181`), `(κ, ε, 𝔠, 𝔡) = (1/2, 1/10, 1/6, 1/10)`:
- `example : (baStep2Data sz0 zSeq).flowOK (1/2) (1/10) (1/6) (1/10) := flow_sz0` — discharged by the merged theorem
  `flow_sz0 : BAFlow sz0 (1/2) (1/10) (1/6) (1/10) zSeq` (axioms standard, §2), not by a hypothesis.
- `example (n) : (baStep2Data sz0 zSeq).T0 n < 1 := …flowOK_T (by norm_num) flow_sz0 n`, and `2/3 ≤ T0 0 < 1` via `t0_sz0`.
- further examples for `flowOK_adm`, `L_swap` (n = 0, `L = 4`), `baStep2Fam_lam_pos_le`.
Nondegenerate: `n = 0` has `L = 4`, `W = 32`, `N = 2097152`, `g = 1/64` (`sz0_values`), `0 < κ`, `t₀ ∈ [2/3, 1)`. No undischarged hypothesis;
no external pin. Audit-side re-check (scratch file, compiled with exit 0):
```
example : (baStep2Data sz0 zSeq).T0 0 < 1 ∧ (baStep2Data sz0 zSeq).flowOK (1/2) (1/10) (1/6) (1/10) :=
  ⟨(baStep2Data sz0 zSeq).flowOK_T (by norm_num) flow_sz0 0, flow_sz0⟩
FlowPinsInst.flow_sz0 : BAFlow RBM.Gauss.SizesInst.sz0 (1 / 2) (1 / 10) (1 / 6) (1 / 10) FlowPinsInst.zSeq
RBM.Gauss.SizesInst.sz0 : RBM.Gauss.Sizes 3
```

## 8. Paper deltas
The file instantiates merged definitions (`baFM`, `BAKsol`, `seqHflowBA`, `BAFlow`, `BAStep2`) and adds no statement about the paper;
`Pp`/`Hpath` follow `seqHflowBA` ((MBM) `1_2:686` with `H_0 = g₀Ψ`, `S^{(B)}(0) = I`). No Lean/paper statement difference is introduced;
"no candidates" (prove report (d)) is accepted.

## 9. Observations (no verdict effect)
- O1. The prove report is 191 lines; the ticket's acceptance list says ≤ 150 (CLAUDE.md §6 allows 300). It changes no statement,
  instance, build, axiom or delta coverage.
- O2. Prove report §(c) "Verified absent: none checked" — fine, no absent name is relied on.
- O3. `set_option linter.unusedVariables false` is file-wide (cosmetic).

## Verdict
| target | verdict |
|---|---|
| 1 `baStep2Mat` (+BAT-C1 `Pp`, `Hpath`) | PASS |
| 2 `baStep2Data` (three facts) | PASS |
| 3 bridges incl. `BAStep2_iff_STStep2G` | PASS |
| 4 `baStep2Fam` | PASS |
| 6 instances | PASS |

**T2415: PASS.** No dispatcher sign-off needed.
