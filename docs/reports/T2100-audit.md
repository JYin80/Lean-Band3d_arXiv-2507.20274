Auditor model: claude-opus-5-5
# T2100 audit (round 1) — KL10a `RBM3D/Loop/KLIndStepA.lean`
Time: Sun Oct  4 02:55:58 UTC 2026 (`date -u`). Branch `t/T2100` at `b8f3f3f`; audit worktree `RBM3D-wt/T2100-audit1` (detached).
Main at `54c61da`, merge base `c5bbae7`; `git diff --stat c5bbae7 main -- RBM3D/Loop/{KLMolecule,KBound,KLTree}.lean` is empty (imports unchanged).

**Verdict: PASS** (all five target groups).

## 1. Scope, build, hygiene, axioms
```
$ git diff --name-status main...HEAD
A	RBM3D/Loop/KLIndStepA.lean
$ lake build RBM3D.Loop.KLIndStepA        # fresh olean, 02:54 UTC
Build completed successfully (3255 jobs).
exit=0                                      # no error/warning lines in the log
$ grep -nE "\bsorry\b|\badmit\b|^axiom|native_decide" RBM3D/Loop/KLIndStepA.lean
none
$ # #print axioms of all 38 public theorem/def names of the file (scratchpad/T2100/Ax.lean)
print lines: 38
std3 lines: 38        # every one: [propext, Classical.choice, Quot.sound]
$ # name clash: each public name grepped as (theorem|lemma|def|abbrev|structure) <name> on main 54c61da
clash check on main 54c61da: done (38 names)   # no CLASH line
$ grep -n "^import" RBM3D/Loop/KLIndStepA.lean
6:import Batteries.Tactic.OpenPrivate
7:import RBM3D.Loop.KLMolecule
8:import RBM3D.Loop.KBound
```
Only the sole writable file is touched; no frozen signature edited; `RBM3D` not imported.

## 2. Statements against the ticket

### Target 1 `KLindStep_nonAlt` — PASS
Script diff of the check-file pin body `KLindStepAt` against the theorem (whitespace and `Finset.` normalised):
```
$ diff pin.txt lean.txt
2c2
<  ∀ a : Fin n → Zd d p.L,
---
>  (¬ ∀ j, σ j ≠ σ (j + 1)) → ∀ a : Fin n → Zd d p.L,
diff exit=1
```
The only difference is the non-alternating hypothesis that the ticket asks for (with `σ r ≠ σ (r+1)` it gives a short `j ≠ r`).
Outer hypotheses: `3 ≤ d`, `3 ≤ n`, `0 < κ`, `0 < gmax`, `KLPT d κ gmax`, the same as `KLindStepPin`. Quantifier order `∀ τ>0, ∃ C>0, ∀ p σ r` is kept, so `C = C(d,n,κ,gmax,τ)`.
The companion `KLindStep_nonAlt_noloss` (`∃ C, ∀ p σ j r, j ≠ r → σ j = σ (j+1) → … ≤ C B_{t,0}^{n-2}`) is a stronger version with no loss (candidate T2100c).

### Target 2 `KLf0/KLf1/KLf2`, `KLf_split`, `KLf1_neg`, `KLf2_neg` — PASS
These are defined for any `f : Zd d L → ℂ`, which is more general than the ticket. The ticket uses them at `f = Θ_t(a, b+·)`, and `KLIndStepA_thetaEdge_long` gives `thetaEdge … s s' = Theta` for `s ≠ s'`, so a long leaf is `Θ_t`. The definitions match ticket item 2 verbatim (`f₀=f 0`, `f₁=½f s−½f(−s)`, `f₂=½f s+½f(−s)−f 0`).

### Target 3 `(eq:f12)` — PASS
`KLf0_bound`: `∃ C>0, ∀ p a b, ‖KLf0 (Θ_t(a,b+·))‖ ≤ C·B_{t,0}`.
`KLf12_bound (hd : 3 ≤ d) (hPT) τ (hτ)`: `∃ C>0, ∀ p a b s`, **every `s`**, with
- `‖f₁‖ ≤ C L^τ (g²+|1−t|)⁻¹ (|s|+1)^{d−1} ((|a−b|+1)^{d−1})⁻¹`;
- `‖f₂‖ ≤ C L^τ (g²+|1−t|)⁻¹ (|s|+1)^{d} ((|a−b|+1)^{d})⁻¹`.

So `q₁ = d−1` and `q₂ = d`, and `C` is chosen before `p`, so it is uniform in `L, g, t, E`. This matches item 3.
`KLf_crude_bound` (all three parts `≤ C B_{t,0}`) is an extra lemma.

### Target 4 `KLSigmaPi_reflect` — PASS
The Lean statement is `Σ^{(∅)}(σ, fun i => c − δ i) = Σ^{(∅)}(σ, δ)` for every `c` and `δ`. With `δ = b₁+s` and `c = 2b₁` this is the ticket's `Σ(b₁+s) = Σ(b₁−s)`, so it is a general form.
The extra hypothesis `hκ : 0 < κ` is a deterministic numeric fact and is discharged in the instance.
Supporting results: `KLslice_f1_vanish` (group G1 is exactly 0 on every slice), `KLIndStepA_SigmaPi_add_const`, `KLIndStepA_sum_slice_root`.

### Target 5 lattice sums — PASS
All use `d = k+2` with `zdistD`, and all are uniform in `L`:

| ticket item | Lean |
|---|---|
| `p=d−2`: `≤ C L²` | `KLlat_pow_sub_two` |
| `p=d−1`: `≤ 2^d (d+1) L` | `KLlat_pow_sub_one` |
| `p=d`: `≤ 2^d(1+log(dL+1))`, `C(1+log L)`, `C L^τ` | `KLlat_pow_dim`, `KLlat_pow_dim_logL`, `KLlat_pow_dim_rpow` |
| pair sum `(d−1,d−1)`: `C(1+log L)` and `C L^τ` | `KLlat_pair`, `KLlat_pair_logL`, `KLlat_pair_rpow`, via merged `inv_pow_pair_le` |
| `log L ≤ C_τ L^τ` | `KLlat_log_le`, `KLlat_log_le_logL` |
| `(g²+|1−t|)⁻¹ ≤ B_{t,0}` | `KLlat_inv_le_Bparam` |
| `Σ_b ‖Θ_t(a,b)‖ ≤ (1−t)⁻¹` | `KLlat_sum_norm_Theta_row_le` (the same as `(1−t)Σ ≤ 1` for `t<1`) |

The paper's pair sum (tex line 776) is `≲ B^{n−2}` (O(1)), while Lean proves `O(1+log L)`. The paper's own estimate is stated under `≺`, which permits an `L^τ` loss, so this is no statement delta.

### Additional public results for KL10b (preflight (a) line 24; report (d) 2)
- `KLIndStepA_sumZero_signed` and `KLsumZero_weighted`: for alternating `σ`, every root `r`, every `x`, `‖Σ_{δ_r=x}Σ‖ ≤ C(1−t)` and `Σ_{δ_r=x}‖Σ‖(maxDist+1)^Q ≤ C(g²+(1−t))`.
- `KLIndStepA_alt_cases` and `KLIndStepA_Qlayer_not`.

Their hypotheses are `3≤d, 3≤n, 0<κ, 0<gmax, KLShort d κ gmax`. `KLShort` is discharged by the merged `KLShort_holds d κ gmax hd hκ hg` (signature read at `KLMolecule.lean:341`).

## 3. Hidden hypotheses, vacuity, cycles
```
RBM3D/Loop/KLTree.lean:250 structure KLPar (κ gmax) : L W hL:3≤L hW:1≤W g hg0:0<g hg1:g≤gmax E hE:|E|≤2-κ t ht0:0≤t ht1:t<1
RBM3D/Loop/KLTree.lean:321 structure KLPT (d κ gmax) : Prop := decay short diffOne diffTwo zeroMode
```
- `KLPar` holds the parameter range only, with no estimate fields. `KLPT` is the ticket-authorised hypothesis, the KL14 pin. No new hypothesis `Prop` is introduced, and `RBM3D/Test/Axioms.lean` is untouched (the ticket expects no new hypothesis).
- No cycle: the file imports only merged modules (`KLMolecule`, `KBound`, and through them `KLTree`).
- The time domain is `0 ≤ t < 1` (from `KLPar`). The constants are existential before `∀ p`, so they never depend on `L, g, t, E`.

## 4. Compiled nonempty instances (15 `example`s, all in the module, which builds)
All instances use the probe data `KLinstPar : KLPar 1 1` (`KLTree.lean:857`): `L=5, W=2, g=1/2, E=0, t=9/10`, with `d=3`. Every deterministic hypothesis is discharged with `decide`, `norm_num` or `one_pos`.

| target | data | remaining hypothesis |
|---|---|---|
| 1 `KLindStep_nonAlt` | `n=3`, `σ=(+,−,+)`, `r=0` (long), short leaf `j=2`, `a=(0,1,2)`, `τ=1` | `KLPT 3 1 1` |
| 1 `KLindStep_nonAlt` | `n=4`, `σ=(+,+,+,−)`, `r=2`, `a=(0,1,2,3)` | `KLPT 3 1 1` |
| 1 `_noloss` | `n=3`, `j=2`, `r=0` | `KLPT 3 1 1` |
| 2 | `s=(1,2,0)` with `s ≠ −s` (decide), `f=Θ_t(0,(1,1,1)+·)` | none |
| 3 | `a=0`, `b=(1,1,1)`, `s=(2,1,0)` (`|s|=3 > |a−b|/2`: zero-mode branch), `τ=1` | `KLPT 3 1 1` |
| 4 | reflection `2−a ≠ a` (decide), `KLslice_f1_vanish` at slice `δ_0=(1,1,1)`, leaf 1 | none |
| 5 | `a=(1,2,3)`, `a'=0`, `L=5`, `τ=1`, all forms | none |
| weighted/signed | `n=4`, `σ^{alt}` with `r=1`, and `¬σ^{alt}` with `r=2,3` | none (`KLShort_holds`) |

The weighted instance is nondegenerate. It proves `‖Σ_{δ_1=0}Σ‖ = 1/19` (merged `KLMolecule_inst_signed_val` moved to root 1), which shows the weighted sum is `≥ 1/19 > 0`.
`KLPT 3 1 1` is the KL14 pin, not yet proved, so it may stay as a hypothesis (CLAUDE.md §4 step 2; the ticket says "`KLPT 3 1 1` as an instance hypothesis").

## 5. Paper deltas
Lean/paper differences and where they are covered (all are proposed in the prove report (a) l.52 and (d) 4–7):
- T2100a: `(eq:f12)` holds for every `s` with `(|s|+1)^{d−1}` and `(|s|+1)^d`; the paper states it for `|s| ≺ 1` (tex l.748).
- T2100b: `(eq:Sigma-empty-sum-zero)` is used in a weighted form (`KLsumZero_weighted`).
- T2100c: case (i) holds without loss.
- T2100d: the profile `(|x|+1)^p` is used in place of `|x|^p+1`.

There is no uncovered statement difference. The general reflection centre in `KLSigmaPi_reflect` and the general `f` in `KLf*` strictly generalise the ticket form and do not change the paper statement.

## 6. Observations (no effect on verdict)
- O1. The file uses `open private … from RBM3D.Loop.KLMolecule / KLTree` (Batteries) to reach 7 private merged lemmas instead of copying them.
  - This does not affect the statements or the axioms (all 38 are standard).
  - It couples the file to the private names in `KLMolecule.lean`, so a later rename there breaks this module, not `main`'s statements.
  - For the dispatcher: decide whether to promote those helpers to public names in a later ticket.
- O2. `KLf12_bound` takes `hd : 3 ≤ d`; `KLf0_bound` does not need it. This is harmless.
- O3. KL10b still owes the `Finset.prod_add` expansion and the glue `nonAlt ∨ alt` (report (d) 2), as the ticket intends.
