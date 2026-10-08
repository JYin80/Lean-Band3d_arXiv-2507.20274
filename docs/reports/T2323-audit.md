Auditor model: claude-opus-5-5

# T2323 audit (round 1) — UN-31b `GUEPhase/ProcK.lean`, target `gueKproc_detDom`

`date -u`: Thu Oct  8 09:36:29 UTC 2026. Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2323-audit1`,
detached at `t/T2323` = `c05626e`. Scratch files: `<scratchpad>/T2323/{eq,neg,ax,reg}.lean`.

## 1. Statement against the pin (check file §2)

```
$ cat eq.lean | grep -nE "^import|^def T2323|^example"   (check imports + ProcK + check §2 verbatim + equality example)
1:import RBM3D.Universality.GUEPhase.Proc
2:import RBM3D.Induction.Defs
3:import RBM3D.Universality.GUEPhase.ProcK
23:def T2323_gueKproc_detDom : Prop :=
42:example : Prop := T2323_gueKproc_detDom
46:example : RBM.Univ.GUEPhase.T2323Check.T2323_gueKproc_detDom := @RBM.Univ.GUEPhase.gueKproc_detDom
$ lake env lean eq.lean; echo $?
eq exit=0
$ # negative control: delete the `hell` line from the pin
$ diff eq.lean neg.lean | head -3 ; lake env lean neg.lean 2>&1 | grep -c error
29c29
<     (∀ᶠ n : ℕ in atTop, ((sz.L n : ℕ) : ℝ) ^ d * (1 - t1 n) ≤ sz.lam n ^ 2) →
---
1
```

The definitional equality with the pin holds (binders in pin order, `hscale` kept), and the control
shows the check rejects a different statement. Against the ticket's mathematics:
- `hell : ∀ᶠ n, L^d (1 - t₁) ≤ ilambda²` is the ticket's zero-mode condition (§141).
- `hKb : sz.STKbound E` is the T2153a-style pin.
- `hKinit` identifies `Kt n (t1 n)` with `STKloop` on `loopOf σ a`.
- Conclusion: `∀ ε > 0, ∀ᶠ n, ∀ t ∈ [t₁,t₀], ∀ m ∈ [2, 2n₀], gueKproc ≤ N^ε (N η_t)^{-(m-1)}`.

Comparison with the RBM2D source (`Proc.lean:1247`, RBM2D HEAD `9e0f275`, `grep -A22`):

| RBM2D | here |
|---|---|
| `hell : (d.L n)^2 (1 - t1 n) ≤ 1` | `L^d (1 - t1 n) ≤ lam n ^ 2` |
| (none) | `hKb : sz.STKbound E` |
| `hKinit : ∀ n I, Kt n (t1 n) I = KLoop.Kcal …` | `∀ n σ a, Kt n (t1 n) (loopOf σ a) = STKloop …` |

All the other binders and the conclusion are the same after the renames. The prove report's T2323a
(d)(1)-(3) covers exactly these three differences.

Read: `STKbound` (`Induction/Defs.lean:174`) is `∀ τ ∈ [0,1)^ℕ, ∀ k ≥ 1, Prec (‖STKloop‖) (Bctl^{k-1})`.
`ProcK_stKbound_eventually` (`ProcK.lean:342`) instantiates it at `τ = t₁` and `D = 1`. Once `N ≥ 2`,
the bad event has `P ≤ N^{-1} < 1 = P(univ)`, so the deterministic inequality follows by contradiction.
This is sound. `ProcK_Bctl_le` (`:365`) proves `Bctl ≤ 2 (N η)⁻¹` from `hell`, `Im m ≤ 1` and
`size = W^d L^d`, as in the ticket.

**Statement: PASS.**

## 2. Vacuity, hidden hypotheses, cycles

- The target's hypotheses are all explicit binders. `Sizes` has the fields `L, W, lam, three_le_L, W_pos`
  (see `szToy`, `ProcK.lean:760-765`), so no field hides a hypothesis.
- No cycle: the only import is the merged `RBM3D.Universality.GUEPhase.Proc`.
  `$ grep -n "^import" ProcK.lean` gives `6:import RBM3D.Universality.GUEPhase.Proc`.
  `Induction.Defs` is transitive, which the ticket allows ("drop if transitive").
- External/owed inputs:
  - `hKb` is `STKbound`, another gate's pin (KL7; `stKbound_of_flow`, `Loop/KLFinal.lean:302`). The ticket allows it.
  - `hKinit` and `hK` define the Duhamel family. The ticket says they "stay hypotheses of the instance".
  - Prove report (a) gives a leading-term limit check of `STKbound` at `k = 2` (script ii-ext).
  - `hell` is deterministic and is discharged in the instance (§3).

**PASS.**

## 3. Compiled nonempty instances

The instances are at `ProcK.lean:740-963`, namespace `RBM.Univ.GUEPhase.ProcKInst`.

Conversion at the ticket's numbers (`d=3, L=3, W=2, ilambda=1, 1-t₁=1/27`, `E=0`):
- `szToy_Bctl : Bctl = 55/224`, `szToy_scale : N η = 8`, `szToy_conv`.
- `example … := ProcK_Bctl_le szToy 0 (E := 0) …` applies the conversion lemma with `hell` at equality.

`gueKproc_detDom` instance (`:934-951`) at the merged `SizesInst.sz0` (`d = 3`, `N = 2^21 (n+1)^18`):
- Parameters: `κ = 1/10`, `τU = 1/1000`, `n₀ = 2`, `E = 0`, `1-t₀ = N^{1/500}/N`, `t₀-t₁ = N^{-1/1000}(1-t₀)/2`.
- Discharged in the example: `hκ`, `hτU`, `hE`, `ht1` (`t1_nonneg`), `ht10`, `ht0`, `hsz` (`Sizes.tendsto_size sz0 sz0_tendsto`).
- Also discharged, through `Eventually.of_forall`: `h730_at`, `hscale_at`, `hell_at`. All three are proved for every `n`.
- Hypotheses left open: `hKb`, `hKinit`, `hK` only, as the ticket allows.
- `example (n) : 0 < t1 n ∧ t1 n < t0 n ∧ t0 n < 1` (`:953`) shows the window is not collapsed.

The instance is not degenerate: `N ≥ 2^21`, `n₀ = 2` (so `m ∈ {2,3,4}`), the window is genuine, and the
witness is not astronomical (it holds at every `n`, from `n = 0`). The `GridCheck` times violate `hell`
(prove report F1/T2323b). Using new times on the `GridCheck` sizes is what the ticket wrote ("where
possible"). Both examples compile (§4).

**PASS.**

## 4. Build, axioms, hygiene, diff

```
$ lake build RBM3D.Universality.GUEPhase.ProcK 2>&1 | grep -E "error|declaration uses|Build completed"
Build completed successfully (3757 jobs).
$ lake env lean ax.lean
'RBM.Univ.GUEPhase.gueKproc_detDom' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.GUEPhase.ProcKInst.szToy_conv' depends on axioms: [propext, Classical.choice, Quot.sound]
exit=0
$ lake env lean reg.lean   (import RBM3D; import …ProcK; #assert_rbm_axioms) | tail -2
non-vacuity certificates: 0 of 138 premises in the two ledgers; the rest are not known to be satisfiable (`RBM3D/Test/InterfaceShape.lean` says what each would take)
exit=0
$ grep -nE "sorry|admit|native_decide|^axiom|^\s*axiom " RBM3D/Universality/GUEPhase/ProcK.lean; echo $?
grep-exit=1
$ git diff --stat main...t/T2323 ; git diff --name-status main...t/T2323
 RBM3D/Universality/GUEPhase/ProcK.lean | 963 +++++++++++++++++++++++++++++++++
 1 file changed, 963 insertions(+)
A	RBM3D/Universality/GUEPhase/ProcK.lean
$ grep -nE "^(theorem|lemma|def|abbrev|noncomputable def|instance)" ProcK.lean   (public decls)
553:theorem gueKproc_detDom …
760:def szToy : Sizes 3 where
767:theorem szToy_Bctl …   771:theorem szToy_scale …   777:theorem szToy_conv :
$ grep -rn "gueKproc_detDom\|ProcKInst" RBM3D --include='*.lean' | grep -v Probe/   (on main)
RBM3D/Universality/GUEPhase/Proc.lean:19:`gueKproc_detDom`, is T2323 = UN-31b).  (docstring only)
```

- Only the sole writable file is touched, and it is new.
- No frozen signature or merged file changed.
- Public names: the pinned target, plus the `szToy*` declarations in the ticket's instance namespace `ProcKInst`.
- Every other helper is `private`.

**PASS.** The hub still runs the full `lake build` at merge.

## 5. Paper deltas

Every Lean/statement difference (§1 table) is in the candidate `T2323a`, prove report (d):
- `hell` at `L^d(1-t₁) ≤ ilambda²`;
- the new `hKb`;
- `hKinit` restricted to `loopOf σ a`.

`T2323b` records the instance-data finding (the `GridCheck` times are outside the zero-mode regime; the
consumers' `t₁` must satisfy `hell`). `grep -n "T2323" docs/paper-deltas.md` finds no existing entry,
which is expected: the dispatcher appends them. **PASS.**

## Observations (no effect on the verdict)

- O1. The theorem depends on the owed pin `STKbound` and on `hell`. It is not RBM2D's unconditional
  statement, and the prove report says so ((b) narrative). The consumers (UN-33…UN-52) still have to
  discharge `hKb` and `hell`. Preflight (a)'s argument that the `Grid.lean:558` `t₁` satisfies `hell`
  is a lead, not checked in Lean.
- O2. The registry pre-check prints the existing ledger summary "0 of 138 premises" with exit 0. No
  new registry line was expected (ticket).

## Verdict

| target | verdict |
|---|---|
| `RBM.Univ.GUEPhase.gueKproc_detDom` | **PASS** |

No dispatcher sign-off needed.
