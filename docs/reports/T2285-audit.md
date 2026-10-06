Auditor model: claude-opus-5-5

# T2285 audit (round 1) — BA-D6 `BA/Boundary` — Tue Oct  6 11:02:27 UTC 2026

Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2285-audit1`, detached at `t/T2285` = 06e86c6.

## 0. Diff scope
```
$ git diff --stat main...t/T2285
 RBM3D/BA/Boundary.lean | 349 +++++++++++++++++++++++++++++++++++++++++++++++++
 1 file changed, 349 insertions(+)
```
Only the sole writable file; `RBM3D/Test/Axioms.lean` untouched (the pre-check flagged nothing, §4). No merged file (in particular
`MFixedPoint.lean`, the pin `BAmBoundary`) is modified.

## 1. Statements against the pins (compiled script equality)
Scratch file = check file's imports + `import RBM3D.BA.Boundary` + the rest of `docs/tickets/checks/T2285-check.lean`
(trailing `end`s removed) + the block below.
```
namespace RBM.BA.T2285Check
example : BASelf_of_tendsto_pin := @RBM.BA.BASelf_of_tendsto
example : BAm_tendsto_of_self_pin := @RBM.BA.BAm_tendsto_of_self
example : BAm_im_tendsto_zero_pin := @RBM.BA.BAm_im_tendsto_zero
example : BArho_tendsto_pin := @RBM.BA.BArho_tendsto
example : baMBoundary_holds_pin := @RBM.BA.baMBoundary_holds
end RBM.BA.T2285Check
end
#print axioms RBM.BA.BASelf_of_tendsto   (… and the other four)
$ lake env lean $S/eq.lean >/dev/null 2>&1; echo "lean exit=$?"
lean exit=0
```
All five public theorems elaborate against the dispatcher's pins with `@`-application (binder order and types identical).
`baMBoundary_holds_pin := ∀ d, BAmBoundary d`, where `BAmBoundary` is the merged pin, unchanged (`MFixedPoint.lean:547-555`):
```
def BAmBoundary : Prop :=
  ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → ∀ E : ℝ,
    haveI : NeZero L := ⟨by omega⟩
    (∀ m : ℂ, BASelf d L g (E : ℂ) m →
      Tendsto (fun η : ℝ => BAm d L g ((E : ℂ) + (η : ℂ) * Complex.I)) (𝓝[>] (0 : ℝ)) (𝓝 m)) ∧
    ((¬ ∃ m : ℂ, BASelf d L g (E : ℂ) m) →
      Tendsto (fun η : ℝ => (BAm d L g ((E : ℂ) + (η : ℂ) * Complex.I)).im) (𝓝[>] (0 : ℝ)) (𝓝 0))
```
Against the paper (`1_2:624-629`, `1_2:715`): `(self_m)` with `Im m > 0`, and `m(E, g) ≡ m(E + i0_+, g)`. Clause 1 is the
identification at real `E` where a solution with `Im m > 0` exists; clause 2 is the gap/edge case. Proved for every `d`
(no `3 ≤ d` binder), all `L ≥ 3`, `g > 0`, every real `E`: the general statement, not a special case. `BArho_tendsto`
gives `ρ_N(E) = π⁻¹ lim Im m(E + iη)` at every real `E` (the consumer form named in the ticket).
`BAm_im_tendsto_zero` carries neither `3 ≤ L` nor `0 < g` (stronger than the pin's clause 2, as the ticket specifies).

## 2. Hidden hypotheses, vacuity, cycles
- Public hypotheses: `[NeZero L]`, `3 ≤ L`, `0 < g`, `BASelf d L g (E:ℂ) m` (merged data predicate, `MFixedPoint.lean:193`:
  `0 < m.im ∧ m = (L^d)⁻¹ * (BAMB d L g z m).trace`), `¬ ∃ m, BASelf …`, and in `BASelf_of_tendsto` convergence of
  sequences, `0 ≤ Im zₖ`, `0 < Im m`. No structure with Prop fields; no `def … : Prop` added.
- Declarations (grep of `^theorem|^private|^def|^example`): 1 private def `Boundary_F`, 7 private theorems (`Boundary_`
  prefix), 5 public theorems, 6 examples. No new public definition.
- Dependencies are merged (`RBM3D.BA.CouplingWindow`, `RBM3D.BA.FlowPins`, Mathlib); `RBM3D.BA.Ward` / `FreeConvStability`
  not imported (imports at `Boundary.lean:6-13` are exactly the ticket's list). The pin is concluded, nothing assumes it:
  no cycle. No external hypothesis is introduced (unconditional proof), so no limit check is needed.
- Route (M2): IFT (`HasStrictDerivAt.localInverse`), stated in the prove report `:26`, `:234`.

## 3. Compiled nonempty instances (`Boundary.lean:313-347`, namespace `RBM.BA.BoundaryInst`, `d = 3`, `L = 4`)
```
example : BAmBoundary 3 := baMBoundary_holds 3                                                    -- (I1)
example : Tendsto (fun η : ℝ => BAm 3 4 g0P ((EP : ℂ) + (η : ℂ) * Complex.I)) (𝓝[>] (0 : ℝ)) (𝓝 m0P) :=
  BAm_tendsto_of_self 3 4 (by norm_num) g0P g0P_pos EP m0P flowP_data.2.2                          -- (I2)
private theorem Boundary_none_10_63 : ¬ ∃ m : ℂ, BASelf 3 4 10 ((63 : ℝ) : ℂ) m := by
  rintro ⟨m, hm⟩
  exact baSelf_none_of_gt 3 4 10 63 (by norm_num) m hm
example : Tendsto (fun η : ℝ => (BAm 3 4 10 (((63 : ℝ) : ℂ) + (η : ℂ) * Complex.I)).im) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
  BAm_im_tendsto_zero 3 4 10 63 Boundary_none_10_63                                               -- (I3)
example : Tendsto (fun η : ℝ => (BAm 3 4 g0P ((EP : ℂ) + (η : ℂ) * Complex.I)).im / Real.pi) (𝓝[>] (0 : ℝ))
    (𝓝 (BArho 3 4 g0P EP)) :=
  BArho_tendsto 3 4 (by norm_num) g0P g0P_pos EP                                                   -- (I4a)
example : … (BAm 3 4 10 (((63 : ℝ) : ℂ) + …)).im / Real.pi) … (𝓝 (BArho 3 4 10 63)) :=
  BArho_tendsto 3 4 (by norm_num) 10 (by norm_num) 63                                              -- (I4b)
example : BASelf 3 4 g0P (EP : ℂ) m0P :=
  BASelf_of_tendsto 3 4 g0P (EP : ℂ) m0P (fun _ => (EP : ℂ)) (fun _ => m0P) tendsto_const_nhds tendsto_const_nhds
    (fun _ => by simp) (fun _ => flowP_data.2.2) flowP_data.2.2.1                                 -- (I5)
```
Every hypothesis is discharged at concrete data: `3 ≤ 4`, `g0P_pos`, the merged real-axis solution `flowP_data.2.2`
(`Im m0P > 0`, so clause 1's premise is non-vacuous), the gap fact `baSelf_none_of_gt` at `E = 63 > 62` (clause 2's premise
non-vacuous). Nondegenerate: `N = 4^3 = 64`, `g ∈ {g0P ≈ 4.67, 10}`. (I5) uses constant sequences; it is a nonempty
instance of a non-endpoint lemma whose non-trivial use is inside `BAm_im_tendsto_zero` (compiled via (I3)). Accepted.

## 4. Build, axioms, hygiene
```
$ lake build RBM3D.BA.Boundary 2>&1 | grep -v "^✔\|^info: \[" | tail -2
Note: This linter can be disabled with `set_option linter.style.longLine false`
Build completed successfully (3739 jobs).
$ lake env lean RBM3D/BA/Boundary.lean   # fresh elaboration, no cache
exit=0, no `error` lines
$ lake env lean $S/eq.lean 2>&1 | grep "depends on axioms"
'RBM.BA.BASelf_of_tendsto' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BAm_tendsto_of_self' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BAm_im_tendsto_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BArho_tendsto' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baMBoundary_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
$ grep -nE "sorry|admit|native_decide|^axiom|^\s*axiom " RBM3D/BA/Boundary.lean; echo "exit=$?"
exit=1
$ printf 'import RBM3D\nimport RBM3D.BA.Boundary\n#assert_rbm_axioms\n' > $S/reg.lean; lake env lean $S/reg.lean > $S/reg.out 2>&1; echo "exit=$?"; grep -c error $S/reg.out
exit=0
0
axiom audit: 8190 theorems, 2656 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
All within [propext,
```
Warnings are only `linter.style.longLine` (docstring lines > 100 chars). The hub runs the full `lake build` at merge.

Name-clash grep (`RBM3D/`, `Probe/` excluded, on the branch) and `T2283.md`:
```
BASelf_of_tendsto: RBM3D/BA/Boundary.lean
BAm_tendsto_of_self: RBM3D/BA/Boundary.lean
BAm_im_tendsto_zero: RBM3D/BA/Boundary.lean
BArho_tendsto: RBM3D/BA/Boundary.lean
baMBoundary_holds: RBM3D/BA/Boundary.lean
BoundaryInst: RBM3D/BA/Boundary.lean
T2283.md hits: 0
```
Only the new file declares them.

## 5. Paper deltas
No new Lean/paper statement difference arises. The Lean statements are the merged pin (`BAmBoundary`) and its
components, already covered by D471 (T2189a, `docs/paper-deltas.md:1430`: `BAm` at real `E` is the real-axis solution, the
identification with `m(E + i0)` was owed by `BAmBoundary`, now proved), and the block-lattice normalisation by D472. The
prove report (d) cites D471 and proposes no new candidate. This is correct. D471's "owed" part can be marked closed at merge.

## 6. Observations (no effect on verdict)
- O1: 4 `linter.style.longLine` warnings (`Boundary.lean:26, 31, 32, 33`), in the module docstring.
- O2: clause 2 / `BAm_im_tendsto_zero` controls only `Im m`, as the merged pin specifies. Convergence of `Re m(E + iη)`
  in the gap is not claimed. This matches the pin and is not needed by the listed consumers.

## Verdict
| Target | Statement | Hidden hyp / vacuity / cycle | Instance | Build / axioms | Deltas | Verdict |
|---|---|---|---|---|---|---|
| `BASelf_of_tendsto` | = pin | none | (I5) | ok | D471 | PASS |
| `BAm_tendsto_of_self` | = pin | none | (I2) | ok | D471 | PASS |
| `BAm_im_tendsto_zero` | = pin | none | (I3) | ok | D471 | PASS |
| `BArho_tendsto` | = pin | none | (I4a,b) | ok | D471 | PASS |
| `baMBoundary_holds` | = `∀ d, BAmBoundary d` | none | (I1) | ok | D471 | PASS |

**T2285: PASS.** No dispatcher sign-off needed.
