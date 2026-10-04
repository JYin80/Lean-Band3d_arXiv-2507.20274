Auditor model: claude-opus-5-5

# T2102 audit (round 1): ST2-09 `Induction/EMn2Poly.lean`, pin `STEMn2Poly`

Written Sun Oct  4 03:39:51 UTC 2026 (`date -u`). Audit worktree `RBM3D-wt/T2102-audit1`, detached at `db20bf8` (`t/T2102`).
Target: `stEMn2Poly_holds (d : ℕ) : STEMn2Poly d` (the ticket's second branch: proved outright, no `STGbEXP*`).

## 1. Statement

The target's type is the merged pin itself. The pin is unchanged on the branch and equal on current `main`:
```
$ lake env lean ax.lean     # import RBM3D.Induction.EMn2Poly
stEMn2Poly_holds : ∀ (d : ℕ), STEMn2Poly d
$ git diff main...t/T2102 -- RBM3D/Induction/Step2Defs.lean RBM3D/Test/Axioms.lean RBM3D.lean | wc -l
       0
$ git diff t/T2102 main --stat -- RBM3D/Induction/{Step2Defs,ContractPt,Defs}.lean RBM3D/Defs/StochDomAt.lean
(no output, rc=0)
```
Pin (`Step2Defs.lean:441–450`, merged) checked against the paper `lem: EMn2_N` (`3_5:427–432`):
```
\left( {\cal E}\otimes  {\cal E} \right)^{M}_{t, \bsig, \ba, \ba} \prec \frac{1}{\eta_t}\Psi_t(0) \cdot  \Psi_t^4\p{ |a-b|} .
```
- Hypotheses: `STFlow`, `0 ≤ t ≤ lemT z`, `0 < ε₀`, `STPsiClass`, `STInitialGT2`, `STLWassm` ("setting of lem:LWterm"); same as the ticket.
- Quantifiers: fixed `κ ε 𝔡 𝔠 sz z t ε₀ Ψ` before `Prec` (eventual in `N`); `U n = Fin 2 × (Fin 2 → Bool) × (Fin 2 → Zd d L)`, i.e. all `k ∈ {1,2}`, all four `σ`, all `(a,b)`: the paper's ranges.
- Bound: `(etaT)⁻¹ * Ψ n 0 * Ψ n |a-b| ^ 4`, no extra loss; `(𝓔⊗𝓔)^{M,(2;k)}` is `STEEk`/`STEEkM` (`Step2Defs.lean:131`, `(σ,σ,σ,-σ,-σ,-σ)` pattern, `W^d Σ SB 𝓛⁶`).
- Not a special case or conditional adapter: no added hypothesis, all `d`.
Statement: **PASS**.

## 2. Vacuity, hidden hypotheses, cycles

```
$ grep -nE "^(private )?(structure|class|instance)" RBM3D/Induction/EMn2Poly.lean     (no output)
$ grep -n "STGbEXP" RBM3D/Induction/EMn2Poly.lean                                     (no output)
$ grep -n "theorem stEMn2Poly_holds" -A3 RBM3D/Induction/EMn2Poly.lean
838:theorem stEMn2Poly_holds (d : ℕ) : STEMn2Poly d := by
839-  intro κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow t ht0 htT ε₀ hε₀ Ψ hΨ hI hA
840-  obtain ⟨hΨ1, hΨmono, hΨwin, C₁, C₂, hC₁, hC₂, hratio⟩ := hΨ
841-  obtain ⟨c, hc, hwin⟩ := hΨwin 1
```
- No new structure, class or hypothesis-carrying field. The only upstream theorem used is the merged `stContractPt_holds` (T2094, `ContractPt.lean:463`), at l. 504 (partner, S₂) and l. 567 (S₁). No pin is assumed; no cycle.
- The partner `(eq_sym_loop_bound2)` (`3_5:758`), which the ticket requires here, is `emn2Poly_contractPt_partner` (l. 496): the merged pin at `((¬σ₀,¬σ₁), b, a)` after the rotation `emn2Poly_loop6_rot` (l. 250).
- Premises are satisfiable together: `STFlow` (`flow_z0`), `STPsiClass` (`Ψ0_class`) and the time bounds are discharged at the merged `sz0` data in §3. `STInitialGT2`, `STLWassm` are the stochastic induction premises of the pin (Step 1 / ST-6 inputs). Their limit check is the report's (a)/(ii) `limit.py` table: `max L²/Ψ₀²` falls as `≈ 1.07/W`, and `‖G-M‖_max ≤ W^{-3/2}` at `W = 2,3,4`, `λ ∈ {1/64, 1}`.
- `STInitialGT2` and the `0 ≤ t` premise are unused by the proof (report b.9.1). This is allowed for a pinned statement and is proposed as delta `T2102a`.
**PASS**.

## 3. Compiled nonempty instance

`RBM3D/Induction/EMn2Poly.lean:968–976` (endpoint at `d = 3`):
```
example (hI : STInitialGT2 sz0 (STflowE z0) tInst (1 / 20) (fun n => Ψ0 n 0))
    (hA : STLWassm sz0 (STflowE z0) tInst Ψ0) :
    Prec sz0 (U := fun n => Fin 2 × (Fin 2 → Bool) × (Fin 2 → Zd 3 (sz0.L n))) ... :=
  stEMn2Poly_holds 3 (1 / 10) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 6)
    sz0 z0 flow_z0 tInst (fun n => by simp only [tInst]; norm_num) sixteenth_le_lemT (1 / 20)
    (by norm_num) Ψ0 Ψ0_class hI hA
```
- The deterministic hypotheses are discharged at the merged nondegenerate `sz0` data: `L = 4(n+1)`, `W = (2(n+1))^5`, `t ≡ 1/16`, `ε₀ = 1/20`, `Ψ = W^{-1}`. The two remaining hypotheses are the stochastic premises (§2).
- A second `example` (l. 980) discharges the merged `inst_EMn2Poly (stEMn2Poly_holds 3) hI hA`.
- The deterministic core `emn2_ee_le` is applied (l. 1012) at a concrete non-block-diagonal Hermitian `H_{ij} = i₀ + j₀` on `Idx 3 3 2` (`N = 216`, proved by `example` at l. 1006), with `z = 1/2 + i/4`, `σ = (+,-)`, `b = (1,1,1)`, and every hypothesis discharged.
- Not degenerate: no `N = 0`, empty index, collapsed window or `False` premise. All of these compile (§4 build).
**PASS**.

## 4. Build, axioms, hygiene, diff

```
$ lake build RBM3D.Induction.EMn2Poly 2>&1 | grep -nE "EMn2Poly|Build completed|error"
53:✔ [3722/3722] Built RBM3D.Induction.EMn2Poly (17s)
54:Build completed successfully (3722 jobs).
```
The module itself prints no warning lines. The other warnings come from merged upstream files (LaplaceGauss, HeatProduct, PropUnit, Step34Pins, Walk, Stop, Step2Defs).
```
$ lake env lean ax.lean
'RBM.Gauss.Sizes.stEMn2Poly_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.emn2Poly_contractPt_partner' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.emn2Poly_loop6_rot' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.emn2Poly_norm_loop4_alt_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.emn2Poly_norm_loop3_le' depends on axioms: [propext, Classical.choice, Quot.sound]
exit 0
$ grep -nEw "sorry|admit|axiom|native_decide|sorryAx|set_option" RBM3D/Induction/EMn2Poly.lean
49:set_option linter.style.longLine false
$ git diff --name-only main...t/T2102
RBM3D/Induction/EMn2Poly.lean
$ sed -n 1,10p RBM3D/Induction/EMn2Poly.lean | grep import
import RBM3D.Induction.ContractPt
import RBM3D.Induction.Step2Defs
```
- The diff touches only a sole writable file. Imports are within the allowed set, and `RBM3D` itself is not imported.
- Frozen signatures are untouched: Step2Defs, ContractPt and the registry show zero diff.
- Public names: the pinned `stEMn2Poly_holds`, plus four helpers prefixed with the file stem `emn2Poly_` (§3 (E)). The other 37 declarations are `private`.
**PASS**.

## 5. Paper deltas

```
$ grep -n "T2102\|EMn2Poly" docs/paper-deltas.md      (no output: candidates not yet appended)
```
The report's (d) proposes two candidates that cover the Lean/paper differences:
- `T2102a`: proof route. F1/F2 block Cauchy–Schwarz replaces `(GijGEX)`/`(GiiGEX)`. `(initialGT2)` is unused. The statement is unchanged.
- `T2102b`: the 4-loop charge pattern of `(eq_sym_loop_bound2)` as formalized (`(-σ₁,σ₁,-σ₁,σ₁)` at `(c,a,c,a)`) differs from the paper's `σ^{(alt)}` at `3_5:758`.

The target statement equals the paper's `(eq:MG_conclusion)`, so there is no statement delta beyond these. Coverage is complete. **PASS**.

## Observations (no verdict effect)

1. `RBM3D/Test/Axioms.lean` is not touched. The `STEMn2Poly` owed line (l. 134) stays. The ticket says "can go" (optional). Report (d).3 explains the plain-build dependency. The dispatcher or hub may drop the line at or after merge.
2. The ticket's import list allowed `RBM3D.Path.QVIdentity`. It is not imported and not needed.
3. Report (a) steps 4, 6, 7 (route through `STGbEXPij`) are superseded by (a′). The final target is the outright form.

## Verdict

| target | statement | vacuity/cycle | instance | build/axioms | deltas | verdict |
|---|---|---|---|---|---|---|
| `stEMn2Poly_holds : ∀ d, STEMn2Poly d` | PASS | PASS | PASS | PASS | PASS | **PASS** |

**T2102: PASS.** No dispatcher sign-off needed.
