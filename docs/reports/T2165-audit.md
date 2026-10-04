Auditor model: claude-opus-5-5
# T2165 audit (round 2) — Sun Oct  4 23:38:24 UTC 2026
Branch `t/T2165` @ `1dde590`, merge base `69b1099`. Audit worktree: `/Users/junyin/Lean_proof/RBM3D-wt/T2165-audit2` (detached).
The ticket pins no Lean text (the check file has only `#check` lines for upstream names), so each statement is checked against the ticket's mathematics and `3_5:2213-2242`.

## Repair delta (round 1 RETURN: no instance of `cltMom1_simplecalculus_ell`)
```
$ git diff --stat 7587804 1dde590
 RBM3D/Evolution/CltMoments1.lean | 4 ++++
+example := cltMom1_simplecalculus_ell (d := 3) (L := 83) (by norm_num) (q := 2) le_rfl (ρ := 40) (ℓ := 1)
+  le_rfl (by norm_num) (0 : Zd 3 83) cltMom1_a₂
```
Only the example and its docstring were added. Premises discharged: `1 ≤ ℓ = 1`, `ℓ = 1 ≤ ρ = 40`. The far set is nonempty (example at `:2048`, `b = (41,41,41)`).

## Build, scope, hygiene, axioms
```
$ git diff --name-only main...t/T2165
RBM3D/Evolution/CltMoments1.lean
$ lake build RBM3D.Evolution.CltMoments1 | grep -E 'error|declaration uses|Build completed'
Build completed successfully (3815 jobs).
exit=0
$ grep -cE '\bsorry\b|\badmit\b|native_decide|^axiom ' RBM3D/Evolution/CltMoments1.lean
0
$ git diff main...HEAD -- RBM3D/Test/Axioms.lean | wc -l
0
$ (59 public names; git grep -F <name> main -- 'RBM3D/*.lean')
public names: 59, occurrences on main: 0
$ lake env lean scratchpad/T2165/ax.lean        (#print axioms)
cltMom1_clusters, cltMom1_not_paired_iff, cltMom1_iso_hyp_iff, cltMom1_weight_a1, cltMom1_weight_a2,
cltMom1_comparable_weights, cltMom1_scale_comparable, cltMom1_scale_bd1, cltMom1_cluster_sum_C4,
cltMom1_simplecalculus, cltMom1_simplecalculus_ell, cltMom1_exponent_count, cltMom1_exponent_count_eq,
cltMom1_prod_exponent_exact, cltMom1_clusterSum_le, cltMom1_paired_moment_le
  : [propext, Classical.choice, Quot.sound]
cltMom1_exponent_identity : [propext, Quot.sound]
```
Imports (`:6-12`) are only the merged `Induction/Step5Pins`, `Evolution/{CltStep,MeanFar}`, `Defs/{Shells,RadialSum}` and `Propagator/{Prop5Hold,Prop6Hold}`. The file does not import `RBM3D`, declares no structure, and changes no frozen signature (it is a new file).

## Statements
**T1 clusters: PASS.** `cltMom1_clusters` (`:855`) takes `1 ≤ p`, `0 ≤ R`, `b : Fin (2p) → (Fin 2 → Zd d L)` and `Paired R b`, and gives a retraction `φ` with:
- every fibre of size `≥ 2`;
- `#free φ ≤ p`;
- every member within `2R` and within `2pR` (`zdistInf`, first labels) of its representative;
- `#{φ | Cluster φ} ≤ (2p)^{2p}`.

The construction is RBM2D's separated set with separation `2R`, not the paper's components (`3_5:2225`). The ticket allows either, and the report says which (candidate `T2165a`).
The complement of the pairing condition is the isolation hypothesis of `STCltIsoConcl`. Script diff:
```
$ P=Step5Pins.lean:420-421 (strip trailing →, (s n)->s); Q=CltMoments1.lean:896-897 (strip trailing ↔)
identical (after stripping trailing →/↔, (s n)->s)
```
`cltMom1_iso_hyp_iff : (pin hypothesis) ↔ ¬ Paired (10 lw³ ℓ_s) b`. `Paired` uses a strict `<` (`:483`), so the complement is literally `10lw³ℓ_s ≤ |·|`. The paper uses `≤`/`≥`, which overlap at equality (`T2165a`).

**T2 weights: PASS.**
- `cltMom1_weight_a1` (`:938`): `g²‖Θ‖ ≤ C(1+2^{d−1})/(|a−b|^{d−2}+1)`.
  - Premises: `3 ≤ L`, `0 < g ≤ Λ`, `0 ≤ t < 1`, regime (i) `g²/L² ≤ 1−t`, `‖m‖ = 1`.
  - It holds without the far-region premise, so it is stronger than the ticket's form.
  - The zero mode `(L^d(1−t))⁻¹` and its absorption by the regime are stated in the docstring (`:932-935`; route `meanFar_T1`, from `prop5Decay_holds`).
- `cltMom1_weight_a2` (`:973`): bound `C·d·w/(|a₂−b₁|^{d−1}+1)`.
  - Premises: `κ ≤ Im m`, `2dw ≤ ρ < |a₂−b₁|`, `|b₁−b₂| ≤ w`.
  - The BD1 premise `|r|₁ ≤ ½|a|₁` is derived inside the proof from `zdistD_le_mul_zdistInf` and `zdistInf_le_zdistD`.
  - At `w = lw³ℓ_s` this is the ticket's form; `cltMom1_scale_bd1` gives `lw ≥ 2d ⇒ 2d·lw³ℓ ≤ lw⁴ℓ`.
  - The window numerator `w` instead of the paper's `ℓ_s` is candidate `T2165b`.
- `∃ C` is inherited from the existential pins `prop5Decay_holds` and `prop6Diff1_holds`.

**T3 comparability: PASS.** `cltMom1_comparable_weights` (`:1096`): the two-sided `2^d` comparison of both profiles at `b`, `b'`.
- Exact premises: `2r ≤ ρ`, `0 ≤ r`, `0 ≤ λ`, both `ρ < |a_i−b|`, `|b−b'| ≤ r`, `2 ≤ d`.
- `cltMom1_scale_comparable` turns `40p ≤ lw` into `2·(2p·10lw³ℓ) ≤ lw⁴ℓ`, the ticket's `log W ≥ 40p` at `r = 2pR`.

**T4 per-cluster sum: PASS.** `cltMom1_cluster_sum_C4` (`:1342`): `3 ≤ d`, `1 ≤ w`, `m = |A|−1`. It bounds the sum over the representative's `b₂` and over the `m` other labels (in the ball of radius `20w = 2R`) of the window profiles `G_w`:
`Σ ≤ (41^d)^m (d4^d)^{m+1} w^{(d+2)m+2}`.
Here `G_w(x) = 1[|x|_∞ ≤ w]/(|x|^{d−2}+1)` (`:1180`) is the paper's `|b₁−b₂| ≤ (log W)³ℓ_s` window. The constant is explicit and the exponent is exactly `(d+2)(|A|−1)+2`.

**T5 `(eq:simplecalculus)`: PASS.**
- `cltMom1_simplecalculus` (`:1536`), general form: `3 ≤ d`, `2 ≤ q`, `0 < ρ`, `0 ≤ λ`; the sum is over `{b : ρ < |a₁−b| ∧ ρ < |a₂−b|}`; the bound is `2cs(3·2^{2d−3})^q (|a₁−a₂|^{d−2}+1)^{−q} λ^q/ρ^{(d−1)q−d}`.
- `cltMom1_simplecalculus_ell` (`:1622`), ticket-literal form: premises `1 ≤ ℓ ≤ ρ`, right side `ℓ^d/(ℓ^{d−2})^q`.
- This matches `3_5:2232-2234`, with the far cutoff as `ρ` (`ρ = lw⁴ℓ ≥ ℓ` by `cltMom1_scale_ell_le`).
- Where `(d−1)q > d` is used and why `q = 1` fails: docstring `:1531-1533` and preflight (a).

**T6 exponent count: PASS.**
- `cltMom1_exponent_identity` (in `ℤ`, `ring`).
- `cltMom1_exponent_count_eq`: cluster factor `= ℓ^{4|A|} lw^{d+(13−d)|A|}`.
- `cltMom1_prod_exponent_exact`: product over clusters `= ℓ^{4n} lw^{d r+(13−d)n}`.
- Assembly, `cltMom1_clusterSum_le` / `cltMom1_paired_moment_le` (`:1879`, `:1922`): `≤ (2p)^{2p}(2cs)^p (C_d M lw^{12})^{2p} (ℓ⁴/(|a₁−a₂|^{d−2}+1))^{2p}`.
- The assembly's deterministic hypothesis `hzu` sits in the signature (`:1881-1884`, `:1924-1927`), not in a structure. It is S5-24's interface, to be supplied from T2 and T3.

§29 (5)–(7):
- No `Prec`.
- Every premise is in a signature.
- Every distance is `zdistInf`. The far region is written `a−b` here and `b−a` in `STfFar`; `cltMom1_zdistInf_sub_comm` (`:102`) bridges the two.

## No vacuity, no hidden hypothesis, no cycle
- There are no new structures. The new `Prop` defs are witnessed: `CltMom1.Cluster` by `cltMom1_cluster_inst` (`:1960`), `CltMom1.Paired` by `cltMom1_b_paired` (`:1967`), and `¬Paired` by the example at `:1984`.
- Dependencies are all merged on `main`: `prop5Decay_holds`, `prop6Diff1_holds`, `meanFar_T1`, `Theta_apply_add_right_of_three_le`, `zdistD_le_mul_zdistInf`. No external hypothesis.

## Compiled nonempty instances (section 9, `d = 3`, `L = 83`, `p = 1`; all compile in the build above)
```
$ grep -n '^example' RBM3D/Evolution/CltMoments1.lean | cut -c1-70
1980:example := cltMom1_clusters (d := 3) (L := 83) (p := 1) le_rfl (R := 
1984:example : ¬ CltMom1.Paired (10 : ℝ)
2001:example : ∃ C ... cltMom1_weight_a1 (at b = (41,41,41), g = 1/2, t = 9/10, m = i)
2008:example : ∃ C ... cltMom1_weight_a2 (b₁ = (36,41,41), b₂ = (36,41,40), w = 1, ρ = 40)
2023:example := cltMom1_comparable_weights (d := 3) (L := 83) (r := 20) (ρ := 40
2037:example := cltMom1_cluster_sum_C4 (d := 3) (L := 83) (by norm_num) (w := 1)
2040:example := cltMom1_simplecalculus (d := 3) (L := 83) (by norm_num) (q := 2)
2044:example := cltMom1_simplecalculus_ell (d := 3) (L := 83) (by norm_num) (q :
2048:example : (Finset.univ.filter ... ).Nonempty        (T5 far set)
2062-2075: exponent_identity / _nat / _count / _count_eq / prod_exponent_exact / scale_comparable / scale_bd1
2123:example := cltMom1_clusterSum_le ... (z := cltMom1_z) cltMom1_z_nonneg cltMom1_z_hzu
2127:example := cltMom1_paired_moment_le ... (same data)
```
Every instance is nondegenerate:
- T1 uses a paired configuration (first labels at distance 5 < R = 10).
- T2a, T2b and T3 use far points at `|·|_∞ = 41 > ρ = 40`, regime `1/27556 ≤ 1/10`, with every premise discharged by `decide`/`norm_num`.
- T4 uses `m = 1`, `w = 1`.
- T5 uses `q = 2` with a nonempty far set.
- In the assembly, `z` is a point mass with `c > 0` (`cltMom1_c_pos`). The paired diagonal `(b⁰, b⁰)` contributes `c² > 0`, so the left side is nonzero.

## Paper deltas
Report (d) proposes four candidates; `grep T2165 docs/paper-deltas.md` finds none yet (the dispatcher appends them).
- `T2165a`: strict pairing; clusters are a `2R`-separated cover, not components.
- `T2165b`: window numerator `w`; the `λ^qρ^{−((d−1)q−d)}` form.
- `T2165c`: explicit `lw^{12}` per index (`lw^{24p}` in total).
- `T2165d`: the scale premises `lw ≥ 40p` and `lw ≥ 2d`, carried as `2r ≤ ρ` and `2dw ≤ ρ`.

Together they cover every Lean/paper difference found above.

## Observations (no verdict impact)
- `cltMom1_iso_hyp_iff` has no premise to discharge (an iff at arbitrary `sz`). The `cltMom1_not_paired_iff` example covers it.
- Unpinned public helpers are in namespace `CltMom1.` or prefixed `cltMom1_` (rule (E)).
- The instance-list line numbers in report (b) refer to `7587804`; the repair section gives the `+4` offset.

## Verdict
T1–T6: **PASS**: statement, no vacuity or hidden hypothesis, compiled nonempty instance, build, axioms, scope, paper-delta coverage. Round 1's RETURN item is resolved by `1dde590`. No dispatcher sign-off needed.
