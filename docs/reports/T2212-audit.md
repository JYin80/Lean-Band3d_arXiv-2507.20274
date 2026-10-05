Auditor model: claude-opus-5-5

# T2212 audit (round 1) — UN-26b `Universality/GUEPhase/BootstrapAt`

Mon Oct  5 20:46:56 UTC 2026. Audit worktree `RBM3D-wt/T2212-audit1`, detached at `67194e3` (t/T2212); merge-base with main `8a43715`;
no upstream file of this module (`GUEPhase/Bootstrap`, `Defs/StochDomAt`, `PerTimeCalc`, `Defs/Domination`, `Loop/TreeRep`, `Defs/Lattice`) changed on main since.
Scratch files: scratchpad `T2212/audit/` (`AuditPins.lean`, `AuditAx.lean`, `src_body.lean`, `new_body.lean`).

## 1. Build, axioms, hygiene, diff scope

```
$ date -u; lake build RBM3D.Universality.GUEPhase.BootstrapAt
Mon Oct  5 20:45:40 UTC 2026
Build completed successfully (3252 jobs).
exit=0

$ lake env lean AuditAx.lean      # #print axioms, 7 public targets + 10 instances (prefix RBM.Univ.GUEPhase. stripped)
UnifDetDomAt' depends on axioms: [propext, Classical.choice, Quot.sound]
unifDetDom_iff_at_id' depends on axioms: [propext, Classical.choice, Quot.sound]
eventually_size_rpow_le_of_neg' depends on axioms: [propext, Classical.choice, Quot.sound]
stochDomAt_of_forall_highProbAt' depends on axioms: [propext, Classical.choice, Quot.sound]
eq736_detDomAt' depends on axioms: [propext, Classical.choice, Quot.sound]
eq728GAt' depends on axioms: [propext, Classical.choice, Quot.sound]
eq727GEAt' depends on axioms: [propext, Classical.choice, Quot.sound]
BootstrapAtCheck.inst_unifDetDom_iff_at_id' ... inst_eq728GAt_chain' (10 lines): each [propext, Classical.choice, Quot.sound]
ax exit=0

$ grep -nE "sorry|admit|native_decide|^axiom| axiom " RBM3D/Universality/GUEPhase/BootstrapAt.lean; echo "grep exit=$?"
grep exit=1
$ grep -nE "3 ≤ d|hd :" RBM3D/Universality/GUEPhase/BootstrapAt.lean
27:dimension-free.  All statements hold for every `d` (no `3 ≤ d`).  The section `BootstrapAtCheck`   # docstring only
$ git diff --stat main...t/T2212
 RBM3D/Universality/GUEPhase/BootstrapAt.lean | 1142 ++++++++++++++++++++++++++
 1 file changed, 1142 insertions(+)
```
Only a sole writable file is touched; `RBM3D/Test/Axioms.lean` untouched (prover's registry pre-check exit 0, nothing flagged; consistent with
`UnifDetDomAt` being both hypothesis and conclusion of proved theorems). No merged file or frozen signature touched.

## 2. Statements against the check-file pins (script)

Check file §2 (`sed` from `/-! ## 2. Vocabulary` to `end RBM.Univ.GUEPhase.T2212Check`, verbatim) + the examples below, in the audit worktree:
```
$ head -3 AuditPins.lean
import RBM3D.Universality.GUEPhase.BootstrapAt
import RBM3D.Defs.Sizes
import RBM3D.Defs.Domination
$ tail (examples)
example : T2212Check.T2212_unifDetDom_iff_at_id := fun {U} f g => @unifDetDom_iff_at_id.{0} U f g
example : T2212Check.T2212_eventually_size_rpow_le_of_neg := fun {size} hsize {a ρ} ha hρ => eventually_size_rpow_le_of_neg hsize ha hρ
example : T2212Check.T2212_stochDomAt_of_forall_highProbAt := fun {Ω} _ {P} {size} {U} {ξ ζ} h => @stochDomAt_of_forall_highProbAt.{0,0} Ω _ P size U ξ ζ h
example : T2212Check.T2212_eq736_detDomAt := fun size hsize d Lf Wf _ Kt n t1 t0 ht10 lam hlam hanti hlamc hK {τU} hτU h730 h732 => eq736_detDomAt size hsize d Lf Wf Kt n t1 t0 ht10 lam hlam hanti hlamc hK hτU h730 h732
example : T2212Check.T2212_eq728GAt := @RBM.Univ.GUEPhase.eq728GAt.{0}
example : T2212Check.T2212_eq727GEAt := @RBM.Univ.GUEPhase.eq727GEAt.{0}
example : T2212Check.T2212_inst_bounds := RBM.Univ.GUEPhase.BootstrapAtCheck.inst_bounds
example (size : ℕ → ℕ) {U : ℕ → Type} (f g : ∀ N, U N → ℝ) : T2212Check.UnifDetDomAtV size f g = RBM.Univ.GUEPhase.UnifDetDomAt size f g := rfl
$ date -u; lake env lean AuditPins.lean; echo "pins exit=$?"
Mon Oct  5 20:46:26 UTC 2026
pins exit=0
```
(A first run failed only on my own lambda for target 2, `fun hsize ha hρ` without the implicit `{a ρ}` binders; fixed in the example, not in the library.)

Ported body vs RBM2D source (`git show c9a24cf:RBM2D/Universality/GUEPhase/BootstrapAt.lean`, `section LBootstrapG` … `end TargetsAt`, 712 vs 717 lines):
```
$ diff src_body.lean new_body.lean | grep '^[<>]'     # complete output, docstring lines included
> theorem unifDetDom_iff_at_id {U : ℕ → Type*} (f g : ∀ N, U N → ℝ) :
>     UnifDetDom f g ↔ UnifDetDomAt id f g := Iff.rfl        (+ its 2-line docstring, 1 blank)
< theorem eq736_detDomAt (size : ℕ → ℕ) (hsize : Tendsto size atTop atTop)
> theorem eq736_detDomAt (size : ℕ → ℕ) (hsize : Tendsto size atTop atTop) (d : ℕ)
<     (Kt : ∀ N, ℝ → LoopIdx (Z2 (Lf N)) → ℂ) (n : ℕ) (t1 t0 : ℕ → ℝ)
>     (Kt : ∀ N, ℝ → LoopIdx (Zd d (Lf N)) → ℂ) (n : ℕ) (t1 t0 : ℕ → ℝ)
<     (hK : ∀ N, ∀ t ∈ Icc (t1 N) (t0 N), ∀ I : LoopIdx (Z2 (Lf N)), I.WF → 2 ≤ I.length →
>     (hK : ∀ N, ∀ t ∈ Icc (t1 N) (t0 N), ∀ I : LoopIdx (Zd d (Lf N)), I.WF → 2 ≤ I.length →
<       HasDerivWithinAt (fun s => Kt N s I) (primRhsGUE (Lf N) (Wf N) (Kt N t) I)
>       HasDerivWithinAt (fun s => Kt N s I) (primRhsGUE d (Lf N) (Wf N) (Kt N t) I)
<       (((Wf N * Lf N) ^ 2 : ℕ) : ℝ) * (t - t1 N) ≤ ((size N : ℕ) : ℝ) ^ (-τU) * lam N t)
<     (h732 : UnifDetDomAt size (fun N (I : LoopSet (Lf N) n) => ‖Kt N (t1 N) I.1‖)
>       (((Wf N * Lf N) ^ d : ℕ) : ℝ) * (t - t1 N) ≤ ((size N : ℕ) : ℝ) ^ (-τU) * lam N t)
>     (h732 : UnifDetDomAt size (fun N (I : LoopSet d (Lf N) n) => ‖Kt N (t1 N) I.1‖)
<     UnifDetDomAt size (fun N (p : Path.TimeIcc t1 t0 N × LoopSet (Lf N) n) => ‖Kt N p.1 p.2.1‖)
>     UnifDetDomAt size (fun N (p : Path.TimeIcc t1 t0 N × LoopSet d (Lf N) n) => ‖Kt N p.1 p.2.1‖)
<   have key := eq736 (Lf N) (Wf N) (Kt N) (ht10 N) (lam N) (hlam N) (hanti N) (hlamc N) (hK N)
>   have key := eq736 d (Lf N) (Wf N) (Kt N) (ht10 N) (lam N) (hlam N) (hanti N) (hlamc N) (hK N)
  (+ 2 docstring lines of eq736_detDomAt: `Z2 ↦ Zd d`, `^2 ↦ ^d`)
$ git -C ../RBM2D --no-optional-locks diff --stat c9a24cf HEAD -- RBM2D/Universality/GUEPhase/BootstrapAt.lean
 RBM2D/Universality/GUEPhase/BootstrapAt.lean | 128 +++------------------------
 1 file changed, 12 insertions(+), 116 deletions(-)
```
So the six private pathwise/cond lemmas (`BootstrapAt_rhs746G_self`, `_eq728_pathG`, `_cond728G`, `_gEven_oddBound`, `_eq727_pathGE`,
`_gEven_cond727G`, all `private`, prefix `BootstrapAt_`) and targets 1–3, 5, 6 are byte-identical to the source; target 4 differs exactly by
the import map of the ticket (`Zd d`, `primRhsGUE d`, `LoopSet d`, `(W L)^d`, `d` explicit after `hsize`). No source declaration dropped.

Merged dependency (no hidden `3 ≤ d`, no structure field): `eq736 (d L W : ℕ) [NeZero L] … (hsmall : … (((W * L) ^ d : ℕ) : ℝ) * (t - t1) ≤ ε * lam t)
(hε : 4 * ((n : ℝ) ^ 2) * n * A * ε < 1)` (`Bootstrap.lean`); `UnifDetDom f g := ∀ τ > 0, ∀ᶠ N in atTop, ∀ u, f N u ≤ (N : ℝ) ^ τ * g N u`
(`Defs/Domination.lean:52`), so `unifDetDom_iff_at_id` is a genuine `Iff.rfl` at `size = id`.

## 3. Per-target findings

| target | statement vs pin | hidden hyp / vacuity / cycle | compiled nonempty instance (file:line) | verdict |
|---|---|---|---|---|
| 1 `UnifDetDomAt` (def) | `rfl` = `UnifDetDomAtV` | plain `Prop`, no structure | used nondegenerately in 4, 6 | PASS |
| 1′ `unifDetDom_iff_at_id` | pin exit 0 | `Iff.rfl` | `inst_unifDetDom_iff_at_id` `:843`: `f N = (N+1)⁻¹`, `g ≡ 1` | PASS |
| 2 `eventually_size_rpow_le_of_neg` | pin exit 0 | — | `:850`: `size N = N+1`, `a = −1`, `ρ = 1/2` | PASS |
| 3 `stochDomAt_of_forall_highProbAt` | pin exit 0 | — | `:856`: `P = δ_()`, `ξ = ζ ≡ 1`, events via `HighProbAt.of_eventually_univ` | PASS |
| 4 `eq736_detDomAt` | pin exit 0; source + import map | all hyps explicit; deps merged | `inst_eq736_detDomAt_tight` `:899`: `d=3, L≡3, W≡2, n=2`, `K = kTight ≠ 0` solving `K' = primRhsGUE` (`kTight_hasDerivAt`, `primRhsGUE_const_len_two`), window `[0, 1/(N+1)]`, `λ ≡ 7000`, `τU = 1`, (7.30) and `h732` proved | PASS |
| 5 `eq728GAt` | pin exit 0; verbatim | all hyps explicit | `inst_eq728GAt_chain` `:1126`: `n₀ = 2`, `L_m = x^{m−1}`, `D_m = x^m` (`x = 1/(N+1)` > 0), `h727 := inst_eq727GEAt_pos` (index `Icc 2 (2*2)`, UN-50 chaining), `h746` from `DmD_le_rhs746G` | PASS |
| 6 `eq727GEAt` | pin exit 0; verbatim | all hyps explicit | `inst_eq727GEAt_pos` `:1101`: `n₀ = 2*2` (`even_two_mul 2`), `K_m = x^{m−1} − x^m`; `hLDK`, `hDLK`, `hodd` (`LmD_odd`), `hK`, `h745` all proved | PASS |

Every deterministic hypothesis of each instance is discharged at the concrete data (read at `:843-1136`): `NfD_pos`, `t10D`, `η ≡ 1 > 0`,
antitonicity `le_rfl`, continuity `continuousOn_const`, `h730At`, `hscaleAt` (`Eventually.of_forall`), nonnegativity, the derivative.
No `N = 0` collapse, no empty index (`Icc 1 2`, `Icc 2 4`, `LoopSet 3 3 2`), window `[0, 1/(N+1)]` has positive length, no `False`
premise, no large witness (thresholds are `size ≥ 1`). The zero instances `:867`, `:958`, `:973` are additional (RBM2D pattern).
No external hypothesis (class G: `P`, `size`, `Nf` abstract; the only limits are `∀ᶠ N` along `size → ∞`, discharged at `size N = N+1`).

§29 checklist (spot-checked in the signatures, §2 above): window `Icc (t1 N) (t0 N)` with `ht10`; no `t < 1`; no `L`–`W` relation;
`size` not tied to `(W L)^d` in target 4; `∀ᶠ` only in `h730`, `hscale` and the `≺`'s; scale `size N` throughout.

## 4. Paper deltas

- `(W L)^d` in (7.30) of `eq736_detDomAt`: covered by D521 (`docs/paper-deltas.md:1480`, T2202b).
- `T2212a` (Lean structure: `≺` along `size N`; index forms by `Iff.rfl`), `T2212b` (even-length bootstrap of (7.27) with
  `L_{2l+1} ≤ √(L_{2l}L_{2l+2})`), `T2212c` (explicit smallness constants / thresholds): proposed in the prove report (d). Coverage complete.

## 5. Observations (no effect on statement, instance, build, axioms or delta coverage)

- O1. Instance helpers `xD`, `LmD`, `DmD`, `KmD`, `zero_stochDomAt`, `rhs745G_nonneg`, … are public without a `BootstrapAt_` stem prefix;
  they live in the ticket-mandated namespace `RBM.Univ.GUEPhase.BootstrapAtCheck`, so no clash risk with library names.
- O2. `open … BootstrapCheck` (`:763`) together with local `NfD`, `t0D`, … : no ambiguity today (build passes); a future addition of
  same-named data to merged `BootstrapCheck` would make these references ambiguous.
- O3. `T2212b`: the prove report compares with RBM1D C.7 only; [YY_25] §7.2 is not a project source, so the paper side remains unverified
  (dispatcher bookkeeping when numbering the delta).
- O4. The full `lake build` with the root import was not run here (hub runs it at merge per §3 (A) 5).

## Verdict

All targets (1, 1′, 2, 3, 4, 5, 6): **PASS**. No dispatcher sign-off needed.
