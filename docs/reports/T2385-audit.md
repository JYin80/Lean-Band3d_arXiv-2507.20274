Auditor model: claude-opus-5-5

# T2385 (BA-K08a, `RBM3D/BA/KSumZeroA.lean`): stage-2 audit, round 1

Written Sat Oct 10 13:39:17 UTC 2026 (`date -u`). Branch `t/T2385` at `ab58d55`; main at `b7efc3b`. Audit worktree
`/Users/junyin/Lean_proof/RBM3D-wt/T2385-audit1` (detached at `ab58d55`). Scratch: `$S/T2385/aud`
(`$S` = this session's scratchpad). Pins: the six statements of `T2385-prove.md` (a+)(iv), which `T2385-1a-audit.md` passed.

## 1. Diff scope, forbidden tokens, names
```
$ git diff --name-only main...HEAD
RBM3D/BA/KSumZeroA.lean
$ wc -l RBM3D/BA/KSumZeroA.lean            # stop line 2400
    1195 RBM3D/BA/KSumZeroA.lean
$ grep -nE '\bsorry\b|\badmit\b|native_decide|^\s*axiom\b|@\[implemented_by|unsafe|opaque' RBM3D/BA/KSumZeroA.lean
(no output)
$ grep -nE '^(theorem|lemma|def|noncomputable def|abbrev|structure|instance)' RBM3D/BA/KSumZeroA.lean
55:theorem baSigmaPi_slice ...      131:theorem baK_sumAll_eq_layers ...   534:theorem baK_sumAll_le ...
1042:theorem baSigmaPi_total_le ... 1058:theorem baSig_signed_sum_unif ...  1079:theorem baSig_signed_sum ...
$ grep -cE '^private (theorem|lemma|def|noncomputable def)' ...   -> 33 ; those without stem `KSumZeroA_` -> (none)
$ for n in <6 public names> KSumZeroA_; do grep -rlw -- "$n" RBM3D | grep -v BA/KSumZeroA.lean | wc -l; done
baSigmaPi_slice: 0  baK_sumAll_eq_layers: 0  baK_sumAll_le: 0  baSigmaPi_total_le: 0
baSig_signed_sum_unif: 0  baSig_signed_sum: 0  KSumZeroA_: 0
```
Only the sole writable file is touched; it is new, so no frozen signature is changed. No new `def`/`structure`: no hidden
hypothesis can sit in a structure field of this file.

## 2. Statements against the pins (script)
`ext.py` extracts `theorem NAME … := by` from the file, and the backticked statement of each bullet of (a+)(iv), with
`S(d,L,g,E,m)` replaced by `(BAMsigma d L (BAMB d L g (E : ℂ) m))`; whitespace is normalised, then the strings are compared.
```
$ python3 -I ext.py
baSigmaPi_slice IDENTICAL
baK_sumAll_eq_layers IDENTICAL
baK_sumAll_le IDENTICAL
baSigmaPi_total_le IDENTICAL
baSig_signed_sum_unif IDENTICAL
baSig_signed_sum IDENTICAL
```
Section context (pinned as "`{d L n : ℕ} [NeZero L] [NeZero n]`"): `section Slice` line 50 `variable {d L n : ℕ} [NeZero L] [NeZero n]`;
`section Layers` lines 96, 125 `variable {d L : ℕ} [NeZero L]`, `variable {n : ℕ} [NeZero n]`. Matches.

**Against the ticket's mathematics and the downstream pin.** The conclusion of `baSig_signed_sum` is, character for character,
the first bound clause of `SigSumZeroAbs` (`Loop/KLIndStepA.lean:1036-1050`) at `Sig := BASig d n L g E m t`:
```
SigSumZeroAbs, clause 3a:  ‖∑ δ ∈ Finset.univ.filter (fun δ : Fin n → Zd d (L i) => δ r = x), Sig i σ δ‖ ≤ C * (1 - t i)
baSig_signed_sum:          ‖∑ δ ∈ Finset.univ.filter (fun δ : Fin n → Zd d (L i) => δ r = x), BASig d n L g E m t i σ δ‖ ≤ C * (1 - t i)
BASig (KMolecule.lean:74-76) := BASigmaPi d (L i) n (BAMsigma d (L i) (BAMB d (L i) (g i) ((E i : ℝ) : ℂ) (m i))) (t i) σ ∅ δ
```
- Quantifier order: `∃ C > 0` before `i, σ, r, x` (family form) and before `L, g, E, m, t, σ, r, x` (uniform form); `C` depends
  on `(d, n, Λ, κ)` only, no smallness of `g` (supervisor 1155 C1). `C` is independent of `Q` (stronger than `∀ Q, ∃ C`).
- Hypotheses of `baSig_signed_sum` are those of `baSig_decay` (`KPure.lean:632-635`) except `ht1 : t i < 1` (strict, vs `≤ 1`)
  and `hn : 3 ≤ n` (also in `baSig_decay`). Both are recorded as `T2385b` (N0: at `n = 2` the signed slice sum is `1`).
  `SigSumZeroAbs` itself carries no range; K08b's assembly must carry `3 ≤ n`, `t i < 1` (as `sigSumZeroAbs_band`). Not a
  defect of this ticket: the ticket's target is the bound at alternating `σ`, and (a+)(iv) fixed these ranges, audited in 1a.
- Loss: exactly one power of `(1 − t)`; slice at every root `r` (paper: root `b_1`), every label `x`. Dimension `d` free with
  `3 ≤ d`; `L ≥ 3` free; `W` free with `1 ≤ W` in the Ward bound (`T2385d`).
- `baK_sumAll_le`: `‖Σ_a 𝒦‖ ≤ B L^d (W^d (1−t) Im m)^{-(n−1)}`, `B` before all data, every `σ`, `n ≥ 1`: the (a) T1 statement
  with `η_t = (1−t) Im m`. `baSigmaPi_total_le`: every layer `π`, alternating `σ`, `C L^d (1−t)`: the A5 invariant.
- `baK_sumAll_eq_layers` (an identity) and `baSigmaPi_slice` (an identity, any shift-invariant `M`) are not endpoint bounds;
  their extra hypotheses only restrict them and they are used internally.

Verdict on statements: all six match the audited pins and the ticket's mathematics. No special case is passed off as general.

## 3. Vacuity, hidden hypotheses, cycles
- Every hypothesis is in the signature (no structure argument introduced by this file). `BAReal` is a merged predicate,
  satisfied by the merged flow point (`P.real`, used in every instance below), so the premises are jointly satisfiable at
  nondegenerate data.
- No external hypothesis, no pin left as a hypothesis (`Step2LocalPT`-type premises: none). Imports: `BA.KPure`, `BA.KWard`,
  `BA.KInduct`, `BA.KMolecule`, `Loop.KLMolecule` (all merged on main); the new file is imported by nothing: no cycle.
- Registry pre-check (below): `0 axioms in RBM`; the new file adds no premise to either ledger.

## 4. Compiled nonempty instances (namespace `RBM.BA.KSumZeroAInst`, lines 1096-1193; compiled in the build of §5)
Datum: merged flow point `P : FlowPt 4 10` of `(d, L) = (3, 4)` (`#check @RBM.BA.MFixedPointInst.P` →
`RBM.BA.MFixedPointInst.FlowPt 4 10`), `Λ = 10`, `κ = P.m0.im` (`P.real.1.1 : 0 < κ`), `g = P.g0` (`P.g0_pos`, `P.g0_le`).
| endpoint | instance(s) | data | every hypothesis discharged by |
|---|---|---|---|
| `baSigmaPi_slice` | l.1108 | `n=4`, `t=1/2`, `σ=KLsigAlt 4`, `π=∅`, `r=0,x=0` | `BAMsigma_shift` |
| `baK_sumAll_eq_layers` | two | `W=1, t=1/2`; `W=2, t=999/1000`; `n=4` | `P.real`, `norm_num`, `decide` (alternation) |
| `baK_sumAll_le` | two | `n=4, W=2, t=1/2, σ=KLsigAlt 4`; `n=3, W=1, t=999/1000, σ≡true` | `P.real`, `P.g0_pos/le`, `norm_num` |
| `baSigmaPi_total_le` | two | `n=4, π=∅, t=999/1000`; `n=6, π={(0,3)}, t=1/2` | as above, `decide` |
| `baSig_signed_sum_unif` | one | `n=4, t=1/2, r=0, x=0` | as above |
| `baSig_signed_sum` | one (term-mode) | `ι=Unit`, `L≡4`, `t≡999/1000`, all `σ, r, x` | `P.real`, `norm_num` for `3≤4`, `0≤t`, `t<1` |
Nondegeneracy, decided in the file: `KLsigAlt 4`, `KLsigAlt 6` cyclically alternating (`by decide`);
`KLTSPlong 4 (KLsigAlt 4) ∅ = TSP 4`, `(TSP 4).card = 3`; `{(0,3)} ∈ KLTSPlong 6 (KLsigAlt 6) {(0,3)}` (the long layer
exercising the cut recursion is nonempty). `L = 4 ≥ 3`, `t ∈ {1/2, 999/1000}` strictly inside `[0,1)`, `g0 ∈ (0,10]`,
`W ∈ {1,2}`: no `N = 0`, empty index, collapsed window, `False` premise, or astronomical witness. The `∃ C` instances obtain
`C` from the theorem (`obtain ⟨C, hC, h⟩ := …`) and apply `h` at the data; none is closed by choosing `C` by hand.

## 5. Build, check file, registry, axioms (audit worktree)
```
$ lake build RBM3D.BA.KSumZeroA > build.log 2>&1; echo exit=$?
exit=0
$ grep -c error build.log ; grep -c 'KSumZeroA.lean:' build.log ; tail -1 build.log
0
0
Build completed successfully (3771 jobs).
$ lake env lean docs/tickets/checks/T2385-check.lean > chk.out 2>&1; echo check-exit=$?; grep -c error chk.out
check-exit=0
0
$ lake build RBM3D > full.log 2>&1; echo fullbuild-exit=$?; tail -1 full.log     # needed for the registry pre-check
fullbuild-exit=0
Build completed successfully (4198 jobs).
$ lake env lean reg.lean      # import RBM3D; import RBM3D.BA.KSumZeroA; #assert_rbm_axioms   (first lines)
axiom audit: 11030 theorems, 3225 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
All within [propext,
 Classical.choice,
 Quot.sound]; no project axioms: what the paper cites rather than proves is carried as hypotheses, not asserted.
reg-exit=0
$ lake env lean ax.lean
'RBM.BA.baSigmaPi_slice' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baK_sumAll_eq_layers' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baK_sumAll_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baSigmaPi_total_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baSig_signed_sum_unif' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baSig_signed_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
```
(The hub's merge build adds the root import; `lake build RBM3D` above is on the branch without it.)

## 6. Paper deltas
Paper `A_deterministic_estimates.tex:731-734`: `(eq:Sigma-empty-sum-zero)`, `Σ_{b∖{b_1}} Σ^{(∅)}(t,σ,b) = O(|1−t|)`, cited
from [YY_25 L3.10], [RBSO1D L4.29]. Lean/paper differences and their coverage in the prove report (d):
| difference | candidate |
|---|---|
| the estimate is proved here (Ward identity + cut factorisation + translation), not cited | `T2385a` |
| ranges `3 ≤ n`, `t < 1` (false at `n = 2`; `SigSumZeroAbs` has no range) | `T2385b` |
| uniform constants `C(d,n,Λ,κ)` vs the paper's `O(·)`/`≺` | `T2385c` |
| `1 ≤ W` in the Ward-sum statements (`0⁻¹ = 0` at `W = 0`) | `T2385d` |
| bound for every layer `π` (`baSigmaPi_total_le`), not stated in the paper | `T2385e` |
Every statement difference has a candidate. `grep -n T2385 docs/paper-deltas.md`: no entry yet (the dispatcher appends them).

## 7. Observations (no effect on statements, instances, build, axioms or delta coverage)
- O1. Root `r` and label `x` are arbitrary in Lean, the paper fixes `b_1`: a strengthening; could be folded into `T2385c`.
- O2. `baK_sumAll_eq_layers` carries hypotheses (`BAReal`, `0 < g`, `3 ≤ L`, alternation) beyond what an identity of
  column sums strictly needs; harmless (pinned in 1a, used only at `W = 1` internally and in instances).
- O3. `baSig_signed_sum`'s `C` is uniform in `Q`, so K08b can take `max` with its weighted constant when assembling
  `SigSumZeroAbs` (whose `∃ C` sits after `∀ Q`).

## Verdict
| target | verdict |
|---|---|
| `baSigmaPi_slice` | PASS |
| `baK_sumAll_eq_layers` | PASS |
| `baK_sumAll_le` (Ward bound for sums of `𝒦`) | PASS |
| `baSigmaPi_total_le` | PASS |
| `baSig_signed_sum_unif` (signed sum-zero, uniform) | PASS |
| `baSig_signed_sum` (signed clause of `SigSumZeroAbs` at `BASig`) | PASS |
| instances at `P` of `(3,4)` | PASS |
No dispatcher sign-off needed. **PASS.**
