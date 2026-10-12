Auditor model: claude-opus-5-5

# T2444 audit, round 1 (BA-L L3c3b `Graph/BAZetaExp`) — Mon Oct 12 09:48:17 UTC 2026

Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2444-audit1`, detached at `t/T2444` = `617661a`; merge base `9eaf866`.

## 1. Diff, hygiene, build, axioms

```
$ git diff --name-only main...t/T2444
RBM3D.lean
RBM3D/Graph/BAZetaExp.lean
$ git diff main...t/T2444 -- RBM3D.lean | grep '^[+-][^+-]'
+import RBM3D.Graph.BAZetaExp
$ grep -n "^import" RBM3D.lean | tail -2 ; tail -1 RBM3D.lean
496:import RBM3D.Graph.BAStepS
497:import RBM3D.Graph.BAZetaExp
#assert_rbm_axioms
$ grep -nE "\bsorry\b|\badmit\b|native_decide|^\s*axiom\b|^inductive|^structure|^class " RBM3D/Graph/BAZetaExp.lean | wc -l
       0
$ grep -nE "^(theorem|lemma|def|abbrev|instance)" RBM3D/Graph/BAZetaExp.lean    # public declarations
62:def LWXiEgL ...
74:theorem LWXiEgL_bandFM ...
83:def BAZetaExpClaim (d : ℕ) : Prop :=
325:theorem baZetaExpClaim_holds (d : ℕ) : BAZetaExpClaim d := by
$ grep -nE "^private (theorem|lemma|def) " RBM3D/Graph/BAZetaExp.lean | grep -v "BAZetaExp_" | wc -l   # §3 (E)
       0
$ git diff --quiet main...t/T2444 -- RBM3D/Test/Axioms.lean && echo "Test/Axioms.lean unchanged"
Test/Axioms.lean unchanged
$ wc -l RBM3D/Graph/BAZetaExp.lean      # stop line 2000
     591 RBM3D/Graph/BAZetaExp.lean
$ lake build RBM3D.Graph.BAZetaExp > build.log 2>&1; echo exit $?; grep -c error build.log; tail -1 build.log
exit 0
0
Build completed successfully (4003 jobs).
$ lake build > full.log 2>&1; echo exit $?; grep -E "^error" full.log | wc -l; tail -1 full.log   # with root import, runs #assert_rbm_axioms
exit 0
       0
Build completed successfully (4268 jobs).
$ lake env lean ax.lean     # import RBM3D.Graph.BAZetaExp; #print axioms ...
'RBM.Graph.LWXiEgL' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.LWXiEgL_bandFM' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.BAZetaExpClaim' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.baZetaExpClaim_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
$ lake env lean docs/tickets/checks/T2444-check.lean > chk.log 2>&1; echo "check exit $?"; grep -c error chk.log
check exit 0
0
```

## 2. Statements against the pins (script diff, whitespace-normalised, after renaming `T2444_` names)

```
$ python3 -I sdiff.py docs/tickets/checks/T2444-check.lean RBM3D/Graph/BAZetaExp.lean
def LWXiEgL IDENTICAL
def BAZetaExpClaim IDENTICAL
$ cmp <worktree check file> /Users/junyin/Lean_proof/RBM3D/docs/tickets/checks/T2444-check.lean && echo same-check-file
same-check-file
```

`LWXiEgL_bandFM` (`:74-76`): `LWXiEgL (bandFM sz E) (Sizes.seqP sz) t ℓ D ξ ↔ LWXiE sz E t ℓ D ξ := Iff.rfl`, exactly the
check file's bridge shape. `baZetaExpClaim_holds (d : ℕ) : BAZetaExpClaim d` (`:325`): general `d`, no extra binders.

Band pin vs BA pin (radius premise verbatim, quantifier order kept: fixed `κ ε 𝔡 𝔠 sz z`, then `t`, class data, `ε₁`, entry law,
then `D`, `ρ`, radius, `D₁`):
```
$ grep -n "^def LWXiExpClaim" -A 14 RBM3D/Graph/LWXiExp.lean | grep -n "sqrt\|LWAssmExp\|∀ D"
3:70-    ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ lemT (z n)) → ∀ (ε₀ : ℝ) (Ψ ℓ : ℕ → ℝ), LWAssmExp sz (STflowE z) t ε₀ Ψ ℓ →
6:73-        ∀ D : ℝ, 0 < D → ∀ ρ : ℕ → ℝ, (∀ n, 0 ≤ ρ n) →
7:74-          (∀ τ : ℝ, 0 < τ → ∀ᶠ n in atTop, Real.sqrt (ρ n) ≤ τ * Real.log ((sz.size n : ℕ) : ℝ)) →
```
The BA pin replaces `lemT`→`BAflowT0`, `LWAssmExp`→`LWAssmExpgL (baFMz sz z) (seqP (sz.withLam 0))`, adds the entry law
`‖G_t − M‖ ≺ W^{-ε₁}` and the floor premise `max (2D) (1/𝔠) ≤ D₁`, all as pinned by the ticket. Threshold: the 1a verdict (i)
is `max (2D) (1/𝔠)` (not T2435 E4's `D + d`), and the proof uses exactly the two halves (`:331-332`: `hD₁a : 2D ≤ D₁` used in
`hfl` `:429-434`; `hD₁b : 1/𝔠 ≤ D₁` used in `BAAuxGraph2_floorL_le` `:490`). No larger threshold: no stop.

## 3. Hidden hypotheses, vacuity, cycles

```
$ lake env lean ax.lean   # (continued)
def RBM.BA.LWAssmExpgL := fun {d} {sz} C μ t ε₀ Ψ ℓ =>
  0 < ε₀ ∧ sz.LWWindow ε₀ Ψ ∧ RBM.BA.STInitialGT2gL C μ t ε₀ Ψ ∧ (∀ (n : ℕ), 0 ≤ ℓ n) ∧
    (∀ (n : ℕ), ℓ n ≤ Real.log ↑(sz.W n) ^ 10 * RBM.ellT (sz.L n) (sz.lam n) (t n)) ∧ RBM.BA.LWLoopExpgL C μ t ℓ
def RBM.BA.PrecL := fun {d} sz μ {U} ξ ζ => RBM.StochDomAt μ sz.size ξ ζ
def RBM.BA.BAFlow := fun {d} sz κ ε 𝔠 𝔡 z => sz.Admissible 𝔠 𝔡 ∧ ∀ (n : ℕ), RBM.BA.BAdom d (sz.L n) (sz.size n) (sz.lam n) κ ε (z n)
```
- No new `structure`/`class`/`inductive` (grep §1: 0). The targets are `Prop` defs whose premises are explicit binders.
- `LWAssmExpgL` (with `STInitialGT2gL`, `LWLoopExpgL`) and the entry law occur only inside `BAZetaExpClaim` and as `example`
  binders; no public theorem binds them (public list §1). This is the ticket's target 5 (registry: none).
- Dependencies are merged modules only (imports `:6-11`: `LWXiExp`, `BAAuxGraph2B`, `LWGen`, `LWPinsBA`, `FlowPins`, `GreenLDE`);
  the full build passed. No cycle.
- The only external inputs are the ticket's authorized hypotheses (other gates' pins). The deterministic radius premise has a
  Lean-proved limit check at the instance (`BAZetaExp_ρ0_rad`, `:520-534`: `√(log N) ≤ τ log N` once `log N ≥ τ⁻²`).

## 4. Compiled nonempty instances (`:564-585`, compiled in the module build of §1)

| Endpoint | Instance | Data | Hypotheses left |
|---|---|---|---|
| `baZetaExpClaim_holds` | example `:570-580` | `d = 3`, `sz0` (`L=4(n+1)`, `W=(2(n+1))^5`, `λ=(2(n+1))^{-6}`), `zSeq`, `flow_sz0` (`κ=1/2`, `ε=𝔡=1/10`, `𝔠=1/6`), `t ≡ 1/2` (`half_lt_t0`), `ε₀=1/10`, `Ψ=W^{-1/2}`, `ℓ ≡ 0`, `ε₁=1/20`, `ρ = log N`, any `D>0`, `D₁ = max (2D) 6` (`1/𝔠 = 6` by `norm_num`) | `STInitialGT2gL`, `LWLoopExpgL`, entry law (allowed by ticket target 4) |
| conj. 2 index set | example `:564-565` | `{p // λ²/L² < 1/2}` nonempty at every `n` (witness `(0,0)`, `BAZetaExp_strict`) | none |
| `LWXiEgL_bandFM` | example `:583-585` | `sz0`, `E ≡ 0`, `t ≡ 1/2`, `ℓ ≡ 0`, `D = 1`, `ξ ≡ 1` | none |

Every deterministic hypothesis of `baZetaExpClaim_holds` is discharged in the example: `3 ≤ 3`, positivity of `κ ε 𝔡`, `BAFlow`
(`flow_sz0`), `0 ≤ t`, `t ≤ BAflowT0`, the deterministic conjuncts of `LWAssmExpgL` (`0 < ε₀`, window `BAZetaExp_Ψ0_window`,
`0 ≤ ℓ`, `ℓ ≤ (log W)^{10} ellT` by `BAZetaExp_ell0`), `0 < ε₁`, `0 ≤ ρ`, the radius premise, the `D₁` threshold. Not
degenerate: `N = (WL)^3 ≥ 2097152`, nonempty index sets, `t = 1/2` strictly inside the window, no `False` premise, witnesses
are fixed small numbers (`D₁ = max(2D,6)`, `ρ = log N`). The instance is universal in `D > 0`; this covers every concrete `D`.

## 5. Paper deltas

Lean/paper differences of the targets and their coverage (proposed in `T2444-prove.md` (d)):
- the floor exponent `D₁` with premise `max (2D) (1/𝔠) ≤ D₁` (`claim:xi`, `7_8:884-890`, has neither): `T2444a`;
- the carrier form (`FlowFM`, law `seqP (sz.withLam 0)`, profile and subtype read `sz.lam`): `T2444b`;
- the radius premise "`√ρ ≤ τ log N` eventually ∀τ" in place of the paper's radius `(log W)^{3/2}`: `T2444c` (band's verbatim);
- `ζ` in place of `ξ` (the BA variables): the L3c3a delta (`T2435a`/`b`, per the ticket), not new here.
All differences are covered.

## 6. Observations (no RETURN)

- O1. The branch's `RBM3D.lean` is based on `9eaf866`; `main` is now `74af906` (T2434 merge). The import line is a union at
  merge (ticket: "`RBM3D.lean`: union"); the hub's merge build decides.
- O2. Prove report (b) shows statement extraction and the instances by script; the report is 211 lines (limit 250/300).
- O3. Ticket-named public helpers not called (`_zdistInf_tri_real`, `_zetaSq_nonneg`, `_pair_sum`, `_card_ball`, `_num`) are
  stated in the report; a private `BAZetaExp_num` variant without `+1` is used. No statement effect.

## 7. Verdicts

| Target | Verdict |
|---|---|
| 1. `LWXiEgL`, `LWXiEgL_bandFM` | PASS |
| 2. `BAZetaExpClaim`, `baZetaExpClaim_holds` | PASS |
| 3. helpers (private, stem `BAZetaExp_`) | PASS |
| 4. instances | PASS |
| 5. registry (none) | PASS |

Ticket T2444: **PASS**. No dispatcher sign-off needed.
