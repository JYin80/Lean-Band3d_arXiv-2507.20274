Auditor model: claude-opus-5-5

# T2104 audit (ST2-27: Path/DuhamelTail, Induction/GridDuhamelN), round 1 — Sun Oct  4 03:36:27 UTC 2026

Branch `t/T2104` at `b3f7b96`; audit worktree `RBM3D-wt/T2104-audit1` (detached). Ticket has no pinned
statement text (check file is `#check` of upstream names only), so statements are checked against the
RBM2D source at `c9a24cf` (the ticket's port target) and the paper (`3_5:108-139`, `1_2:1070-1071`).

## 1. Diff scope, build, hygiene

```
$ git diff --stat main...t/T2104 ; git log --oneline main..t/T2104
 RBM3D/Induction/GridDuhamelN.lean | 778 +++++++++++++++++++++++++++++++
 RBM3D/Path/DuhamelTail.lean       | 951 ++++++++++++++++++++++++++++++++++++++
 2 files changed, 1729 insertions(+)
b3f7b96 T2104: Path/DuhamelTail and Induction/GridDuhamelN (ST2-27)
5a98912 T2104: Path/DuhamelTail (stoppedAzuma108 and generic Duhamel tails)
$ lake build RBM3D.Path.DuhamelTail RBM3D.Induction.GridDuhamelN   (audit worktree; error lines: none)
Build completed successfully (3759 jobs).   [exit code 0]
$ git diff main...t/T2104 | grep -nE "^\+.*\b(sorry|admit|native_decide)\b|^\+axiom "
(no output)
$ git grep -nE "^(theorem|def|noncomputable def|lemma) (Ugen|AvecN|martIncN|predIncN|StoppedDuhamelN|StoppedAzumaN|stoppedEdge|StoppedAzuma108|Ugen_two_eq_Uop|AvecN_two)\b" main -- RBM3D
(no output: no clash)
```
Only new files, both sole-writable; `RBM3D/Test/Axioms.lean` untouched; no frozen signature touched.
Imports: `DuhamelTail` <- `Path.{Expansion,Azuma,Kernel,Stop,UBounds,StepDecompLoop}`; `GridDuhamelN` <-
`Path.{Expansion,Azuma,Kernel,Stop}`, `Kernel.Evolution`; all merged on `main`, neither file imports the other
or `RBM3D`: no cycle.

## 2. Axioms and registry pre-check (scratch `ax.lean`: `import RBM3D` + both modules + `#print axioms` + `#assert_rbm_axioms`)

```
$ lake env lean scratchpad/T2104/ax.lean > ax.out; echo $?
lean exit=0
$ grep -c "depends on axioms: \[propext, Classical.choice, Quot.sound\]" ax.out ; grep -ciE "error|sorryAx|unregistered" ax.out
17
0
$ grep -E "^'RBM" ax.out | cut -d"'" -f2 | tr '\n' ' '
RBM.Path.StoppedAzuma108 RBM.Path.stoppedAzuma108 RBM.Path.stoppedAzuma108_at RBM.Path.stopped_duhamel_azuma_tail_fixed RBM.Path.stopped_duhamel_azuma_union RBM.Path.stopped_duhamel_cheb_tail RBM.Path.stopped_duhamel_det_bound RBM.Ind.GridDuhamelN_Ugen_add RBM.Ind.GridDuhamelN_Ugen_self RBM.Ind.GridDuhamelN_Ugen_comp RBM.Ind.GridDuhamelN_UgenHom RBM.Ind.GridDuhamelN_Ugen_duhamel_telescope RBM.Ind.stoppedDuhamelN RBM.Ind.stoppedDuhamelN_at RBM.Ind.stoppedAzumaN RBM.Ind.stoppedDuhamel105_of_stoppedDuhamelN RBM.Ind.Ugen_two_eq_Uop 
$ grep "axiom audit" ax.out
axiom audit: 3280 theorems, 1193 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
```

## 3. Statements: RBM2D@c9a24cf vs RBM3D (script `sd.py`/`sb.py`: token diff after the renames
`Z2 L -> Zd d L`, `(L) [NeZero L] -> (d L) [NeZero L] (g)`, `Uop/Ugen L -> Uop/Ugen d L g`, `d : Sizes -> sz`, `spectralM -> mE`;
`sb.py` also compares the bodies of the Prop-valued pins)

```
stoppedEdge : identical after renames
stoppedEdge_apply : identical after renames
stopped_duhamel_azuma_tail_fixed : identical after renames
stopped_duhamel_azuma_union : identical after renames
stopped_duhamel_cheb_tail : [('replace', '4', '(2 * d)')]
stopped_duhamel_det_bound : identical after renames
stoppedAzuma108 : [('replace', 'd', 'sz')]
GridDuhamelN_Ugen_add : [('delete', '[NeZero k]', '')]
GridDuhamelN_Ugen_self : [('delete', '[NeZero k]', '')]
GridDuhamelN_Ugen_comp : [('delete', '[NeZero k]', '')]
GridDuhamelN_UgenHom : [('delete', '[NeZero k]', '')]
GridDuhamelN_Ugen_duhamel_telescope : [('delete', '[NeZero k]', '')]
stoppedDuhamelN : [('replace', 's', ': ℕ → ℝ) (s'), ('replace', 'd', 'sz')]
stoppedAzumaN : [('replace', 's', ': ℕ → ℝ) (s'), ('replace', 'd', 'sz')]
martIncN : identical after renames
predIncN : [('delete', '[NeZero k]', '')]
StoppedAzuma108 : [('replace', '(Complex.normSq', '((Complex.normSq'), ('insert', '', ': ℝ)'), ('replace', '(Complex.normSq', '((Complex.normSq'), ('insert', '', ': ℝ)'), ('replace', '(Complex.normSq', '((Complex.normSq'), ('insert', '', ': ℝ)')]
StoppedDuhamelN : [('delete', '[NeZero k]', '')]
StoppedAzumaN : [('delete', '[NeZero k]', '')]
```
Reading of the differences:
* `L^4 -> L^(2*d)` (`cheb_tail`): the label count `card (Zd d L × Zd d L) = L^(2d)`; correct `d`-dimensional exponent.
* `[NeZero k]` dropped (Ugen family, `predIncN`, `StoppedDuhamelN`, `StoppedAzumaN`): `Ugen := UN d L g (fun i => mSigma E (σ i))`
  uses the merged `cycProd m i = m i * m (finRotate k i)` (`Kernel/Evolution:49`), which is RBM2D's `σ (i+1)` on `Fin k`;
  removing the instance only adds the cases `k = 0, 1` (a generalization; paper `DefTHUST` has `n ≥ 2`). Proposed T2104a.
* `StoppedAzuma108`: only an explicit `(… : ℝ)` ascription on `Complex.normSq (mE E)` (same value; same form as the merged
  `StoppedDuhamel105`, `Expansion:74`).
* `stoppedDuhamelN`/`stoppedAzumaN` binder `(E s t : ℕ → ℝ)` split into `(E : ℕ → ℝ) (s t : ℕ → ℝ)`: same type.
* `AvecN` body (not in the table): RBM2D `gloop … - KLoop.Kcal …`; RBM3D `sz.STLKM n (E n) u_j (pathH …) σ a`
  = `STLM - STKloop` (`Step2Defs:60-70`), the merged `(𝓛-𝒦)` vocabulary; `AvecN_two` is `rfl` to the merged `Avec`.
Kernel against the paper: `def_Ustz` (`3_5:116-118`) is `Π_i ((1 - s M^{(σ_i,σ_{i+1})} S)/(1 - t M^{(σ_i,σ_{i+1})} S))_{a_i b_i}`
with cyclic `σ_{n+1} = σ_1` and, for RBM, `M^{(σ,σ')} = m(σ)m(σ') I` (`1_2:1071`); `uKer μ s t = (1 - (sμ)•SB) * Theta (tμ)`
(`Evolution:56`) and `mSigma E s = if s then mE E else conj (mE E)` (`Semicircle:85`) match. Reduction at `n = 2`
(ticket): `Ugen_two_eq_Uop`, `AvecN_two`, `martIncN_two`, `predIncN_two`, `stoppedDuhamel105_of_stoppedDuhamelN` compile.
Quantifiers: the pins keep RBM2D's `∀ n` premises (as D188); `_at` forms `stoppedDuhamelN_at` (premises at `n` only),
`stoppedAzuma108_at`, `stoppedAzumaN_at` (no window premises: stronger) exist (DECISIONS §29 (4)).

## 4. Vacuity, hidden hypotheses, cycles
* No new structure; `Sizes`/`sz0` are merged. `StoppedAzuma108`, `StoppedDuhamelN`, `StoppedAzumaN` are proved
  (`stoppedAzuma108`, `stoppedDuhamelN`, `stoppedAzumaN`), not assumed; `StoppedDuhamelN` appears as a hypothesis only in the
  bridge `stoppedDuhamel105_of_stoppedDuhamelN`, whose example discharges it with `stoppedDuhamelN`.
* The conditional sub-Gaussian premise inside `StoppedAzuma108`/`StoppedAzumaN` is RBM2D's pin form (Azuma route, paper-delta
  D21: "BDG 换成 Azuma 与 Doob"), not a new external input. It is satisfiable at the instance data: `martInc` is bounded
  (`AvecN` is a resolvent loop at `u_j ≤ 1/2 < 1` minus a deterministic loop) and has conditional mean zero given `F_j`, and
  `{j < τ}` is `F_j`-measurable, so conditional Hoeffding gives a finite proxy `c_j`. Not vacuous.
* `stopped_duhamel_det_bound` is a conditional adapter (`hFwd` assumed, as in RBM2D); the report says so (d).

## 5. Compiled nonempty instances (13 `example`s; all elaborate in the build of §1)
| Endpoint | Instance (file:line) | Data | Hypotheses |
|---|---|---|---|
| `StoppedAzuma108`/`stoppedAzuma108` | DuhamelTail:844 | `sz0` (`d=3`, `L_0=4`), `n=0`, `E=0`, `s=1/10,t=1/2,K=4`, `k=2`, `τ≡3` (2 live terms) | all deterministic discharged; sub-Gaussian kept (§4) |
| same | DuhamelTail:873, :896 | `τ≡0,c≡0` (sub-G discharged by `fun_zero`); boundary `k=0` | all discharged |
| `stopped_duhamel_det_bound` | DuhamelTail:914 | `d=L=3`, `g=1/2`, `ξ=1`, `u_j=j/10`, `τ≡3`, `R_j = U_{t,u_{j+1}}1 ≠ 0` | all discharged |
| `GridDuhamelN_Ugen_add/_self/_comp/_UgenHom` | GridDuhamelN:644,651,657,665 | `d=L=3`, `g=1/2`, `E=0`, `σ=(+,+,-)` (non-constant), times `1/4,1/2,3/4` | all discharged |
| `GridDuhamelN_Ugen_duhamel_telescope` | GridDuhamelN:672 | same, `u_j=j/10`, `m=3` | all discharged |
| `stoppedDuhamelN` | GridDuhamelN:689 | `sz0`, `n=0`, `k=3`, `τ≡3`, `j=4` (`min=3 ≤ K=4`) | all discharged |
| `stoppedDuhamel105_of_stoppedDuhamelN` | GridDuhamelN:714 | `sz0`, `E=0` | discharged by `stoppedDuhamelN` |
| `stoppedAzumaN` | GridDuhamelN:721, :752 | `sz0`, `k=3`, `τ≡3`, `m=2`; companion `τ≡0,c≡0` | as `stoppedAzuma108` |
None has `N = 0`, an empty index type, a collapsed window or a `False` premise; the arbitrary tensors `A` are universally
quantified (stronger than one tensor).

## 6. Paper-delta coverage
* `[NeZero k]` dropped / `Ugen` = merged `UN`: T2104a. Energy sequence `E : ℕ → ℝ` in the `*N` pins vs scalar in the merged
  pins: T2104b. `_at` forms: T2104c (with D188). `L^(2d)` label count: T2104d. Grid-discrete pathwise `int_K-L_ST`: D190/D162.
  Azuma tail with sub-Gaussian proxies in place of the BDG bound `alu9_STime`: D21 (and D90 for `STGridRepN`).
  No Lean/paper statement difference without a candidate or an entry.

## 7. Verdicts
| Target | Statement | Vacuity/hidden/cycle | Instance | Build/axioms | Deltas | Verdict |
|---|---|---|---|---|---|---|
| `StoppedAzuma108` (+`stoppedAzuma108`, `_at`) | RBM2D-identical | none | sz0, τ≡3 | ok | D21, T2104c | PASS |
| `GridDuhamelN_Ugen_add` | = RBM2D minus `[NeZero k]` | none | yes | ok | T2104a | PASS |
| `GridDuhamelN_Ugen_self` | idem | none | yes | ok | T2104a | PASS |
| `GridDuhamelN_Ugen_comp` | idem | none | yes | ok | T2104a | PASS |
| `GridDuhamelN_UgenHom` | idem | none | yes (`_apply`) | ok | T2104a | PASS |
| `GridDuhamelN_Ugen_duhamel_telescope` | idem | none | yes, m=3 | ok | T2104a | PASS |
| `stoppedDuhamelN` (`StoppedDuhamelN`) | idem | none | sz0, τ≡3 | ok | T2104a,b,c, D188, D190 | PASS |

## 8. Observations (no effect on statement, instance, build, axioms or coverage)
* O1. `stopped_duhamel_azuma_union` and `stopped_duhamel_cheb_tail` (ported, not consumed by P.1) carry no instance; the report
  says so. Same treatment as T2021-audit O2. A later consumer should instantiate them.
* O2. Prove report (d) T2104d cites "D10" for the BDG→Azuma replacement; paper-deltas D10 is about `(Owx)/(Oe2x)`; the entry
  that covers it is D21 (and D90).
* O3. The prove report's `#print axioms` list names 30 symbols incl. `Ind.AvecN` etc.; I re-ran 17 of them (§2) and the
  full `#assert_rbm_axioms` with both modules imported: exit 0.
* O4. `DuhamelTail` imports `Path.UBounds` (merged, T2097) for `uopBack`, outside the ticket's listed imports; the ticket allows
  importing "the merged files they need".

Verdict: **PASS** (all targets). No dispatcher sign-off needed.
