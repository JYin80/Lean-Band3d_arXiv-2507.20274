Auditor model: claude-opus-5-5

# T2109 audit (ST2-10, `Induction/EMn2Exp1`), round 1 — Sun Oct  4 06:25:06 UTC 2026

Branch `t/T2109` at `06a008f` (merge-base with `main`: `ec0e7d5`); audit worktree
`/Users/junyin/Lean_proof/RBM3D-wt/T2109-audit1` (detached). Scratch: `scratchpad/T2109/`.

## 1. Scope, hygiene, build, axioms

```
$ git diff --name-only main...t/T2109
RBM3D/Induction/EMn2Exp1.lean
$ git diff main...t/T2109 -- RBM3D/Induction/Step2Defs.lean RBM3D/Test/Axioms.lean RBM3D.lean | wc -l
       0
$ grep -nEw "sorry|admit|axiom|native_decide" RBM3D/Induction/EMn2Exp1.lean | wc -l
       0
$ git grep -n "emn2Exp_\|emn2ExpS\|emn2ExpE\|emn2ExpP\|emn2ExpK" main -- RBM3D RBM3D.lean | wc -l   # name clash on main
       0
$ lake build RBM3D.Induction.EMn2Exp1 > build.out 2>&1; echo "exit $?"
exit 0
$ grep -n "EMn2Exp1" build.out; grep -c "EMn2Exp1.lean" build.out; grep -c "^error" build.out; tail -1 build.out
332:✔ [3767/3767] Built RBM3D.Induction.EMn2Exp1 (7.8s)
0
0
Build completed successfully (3767 jobs).
```
`lake env lean scratchpad/T2109/audit_check.lean` (excerpt, verbatim):
```
'RBM.Gauss.Sizes.emn2Exp_near' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.emn2Exp_far12' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.emn2Exp_S12_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.emn2Exp_cover' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.emn2Exp_profile_cmp' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.emn2Exp_profile_shift' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.emn2Exp_scale_gap' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.emn2Exp_trunc_cmp' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.emn2Exp_EEk_cover' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.emn2Exp_EEk_split' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.emn2Exp_of_far3' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.emn2Exp_kellStar_far' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.emn2Exp_ev_exp_pow' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.emn2Exp_one_le_K' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.emn2Exp_STprof_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.emn2ExpEllStar_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.emn2ExpSw' depends on axioms: [propext]
```

## 2. Statements against the pin `STEMn2Exp` (`Step2Defs.lean:456-473`) and the ticket

Premise blocks (script diff, leading whitespace stripped):
```
$ for s in 1207 1466; do diff <(sed -n 457,467p Step2Defs.lean|sed 's/^ *//') <(sed -n "$s,$((s+10))p" EMn2Exp1.lean|sed 's/^ *//') >/dev/null; echo "$s: $?"; done
1207: 0      # emn2Exp_near: premises identical to the pin's
1466: 0      # emn2Exp_far12: premises identical to the pin's
$ diff <(sed -n 457,473p Step2Defs.lean|sed 's/^ *//') <(sed -n 1735,1751p EMn2Exp1.lean|sed 's/^ *//;s/ := by$//'); echo $?
0            # emn2Exp_of_far3: conclusion = the pin body verbatim
```
Defeq check, every `d` (`scratchpad/T2109/audit_check2.lean`, `lake env lean`, exit 0):
```
example (d : ℕ) := fun h3 => (emn2Exp_of_far3 d h3 : STEMn2Exp d)
'RBM.Gauss.Sizes.stEMn2Poly_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.stContractPt_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
```
`stEMn2Poly_holds : ∀ (d : ℕ), STEMn2Poly d` and `stContractPt_holds : ∀ (d : ℕ), STContractPt d`
are unconditional theorems on `main` (`90a2761` T2102, `2b7c4f6` T2094); `kellStarEv` is from `5bef95c` T2097.

Per target (ticket items 1–3; cut with ST2-11 as the ticket's default):

| target | Lean | check | verdict |
|---|---|---|---|
| 1a scales `ℓ*`, `ℓ†` (`(eq:cutoff_scales)`) | `emn2ExpEllStar` = `(log W)^{3/2} ℓ_t`, `emn2ExpEllDag` = `(log W)^{7/4} ℓ_t`; `emn2ExpEllStar_eq := rfl` against `KellStarEv`'s inline scale | exponents match `3_5:830` | PASS |
| 1b `Ψ_t(r)² ≍ W^{-d}𝒯̃(r)`, `r ≤ ℓ†` (`3_5:833-836`) | `emn2Exp_trunc_cmp`: literal `Ψ² = W^{-d}B_{t,r∧ℓ}`; (i) `Ψ² ≤ exp((log W)^{7/8}) P(r)` unconditional; (ii) `P(r) ≤ Ψ²` under `W^{-D} ≤ B_{t,r∧ℓ}` | (ii)'s side condition is the paper's "large `D`"; loss `exp((log W)^{7/8}) = N^{o(1)}` | PASS (deltas T2109b, T2109e) |
| 1c `𝒯̃(|b-c'|) ≺ 𝒯̃(|a-b|)`, two cases `3_5:851-853` | `emn2Exp_profile_cmp`: `r > ℓ†`, `m > ℓ ∨ r ≤ m+ℓ*+1` ⇒ `P(m) ≤ K_n P(r)`, `K_n = 2^{d-2}exp(2(log W)^{3/4})`; hyp. `2(ℓ*+1) ≤ ℓ†` (eventually: `emn2Exp_scale_gap`) | both cases of the paper, `m ≥ r-(ℓ*+1)` as in `3_5:851` | PASS (T2109a) |
| 2 near case `|a-b| ≤ ℓ†` | `emn2Exp_near`: pin's premises (diff 0) ⇒ `Prec(‖EE_k‖·1_{r≤ℓ†}) ≺ η⁻¹ Bctl^{1/2} P(r)²` | RHS ≤ pin RHS (`Ĵ ≥ 0`, stronger); via `stEMn2Poly_holds` at `Ψ'`; no premise of `STEMn2Poly` left as hypothesis | PASS (T2109b) |
| 3a cover `(eq;S123)` | `emn2Exp_cover`, `emn2Exp_EEk_cover`, `emn2Exp_EEk_split` (both cuts `k`) | `‖EE_k‖ ≤ S̃₁+S̃₂+S̃₃` proved, so the region sums are tied to the pin's object; `R₃` reading = T2109d | PASS |
| 3b `S̃₁+S̃₂` deterministic | `emn2Exp_S12_le`: `‖𝓛²_{(s,-s)}‖ ≤ y²P`, `P(m) ≤ K P(r)` on both cases ⇒ `S̃₁+S̃₂ ≤ 2·3^d η⁻¹ K y⁵ √P(0) P(r)²` | matches `(eq:boundwtS_1)` ×2; no `(GijGEX)` (T2109c) | PASS |
| 3c `S̃₁+S̃₂` far case, model level | `emn2Exp_far12`: pin's premises (diff 0) ⇒ `Prec((S̃₁+S̃₂)·1_{r>ℓ†}) ≺ η⁻¹ Bctl^{1/2} P(r)²` | `ℓ*` evaluated at `u = t n`; `K_n`, `√(1+cB⁻¹)` absorbed eventually (`emn2Exp_ev_exp_pow`) | PASS (T2109e) |
| assembly (extra) | `emn2Exp_of_far3`: `h3` (`S̃₃·1_{r>ℓ†}` bound, ST2-11) ⇒ pin body | conditional adapter; **not** a proof of `STEMn2Exp`; `STEMn2Exp` stays owed (registry untouched) | PASS as conditional |

Quantifier order and parameters: `κ ε 𝔡`, `𝔠 sz z`, `STFlow`, `t` with `0 ≤ t ≤ lemT`, `ε₀`, `Ψ`
window `∀ᶠ`, `ℓ` range `∀ᶠ`, `STLWassmExp ∀D`, then `∀ D` and `Prec` (eventual): identical to the pin
(DECISIONS §29 (1),(4)); no `L^d ≤ W^K` premise added (§29 (3)); constants `3^d`, `2^{d-2}`, `cB(𝔡)`
free of `W, L, λ, D`; the `N^{o(1)}` losses are inside `≺`.

## 3. Hidden hypotheses, vacuity, cycles

- No new `structure`/`class`; new `def`s (`emn2ExpEllStar/EllDag/Pf/K/S1/S2/S3/S1M/S2M/S3M/Sw/PsiSq/Psi`)
  are plain functions. `emn2Exp_near` and `emn2Exp_far12` carry no hypothesis beyond the pin's premises
  (diff exit 0 above). Their proofs use only merged, unconditional theorems (axioms above).
- No cycle: the module imports `EMn2Poly`, `Step2Iterate`, `KellStar` (merged); `STEMn2Exp` is not
  assumed anywhere except as the *conclusion* shape of `emn2Exp_of_far3` (its `h3` is the `S̃₃` bound).
- External hypotheses: none new. `STInitialGT2`, `STLWassmExp` are registered pins of other gates (prove
  report b.5 registry diff); `h3` is ST2-11's target.

## 4. Compiled nonempty instances (same file, `RBM.Gauss.EMn2Exp1Inst`, 19 `example`s; built above)

All 16 public theorems are applied (read at lines 1851–2120):
- `emn2Exp_cover`, `emn2Exp_S12_le`: `d=3, L=3, W=2` (`N=216`), Hermitian `H_ij=(i)_0+(j)_0`,
  `z=1/2+i/4`, `σ=(+,-)`, `a=0`, `b=(1,1,1)`; `S12_le` with `y=η⁻¹`, `P≡1`, `K=1`, `h2` discharged by
  `norm_loopM_le`, `hK` by `simp`.
- `emn2Exp_profile_shift` (both cases), `emn2Exp_scale_gap`, `emn2Exp_profile_cmp` (both cases at `szA`,
  `W=2^{400}`), `emn2Exp_trunc_cmp` (`sz0`, `n=0`, `r=1 ≤ ℓ†`), `emn2Exp_ev_exp_pow`, `emn2Exp_EEk_cover`,
  `emn2Exp_EEk_split` (`sz0`, `n=0`, both `k`, every `ω`), `emn2Exp_kellStar_far` (`sz0`, all deterministic
  hypotheses discharged: `sz0_tendsto`, `sz0_bandwidth`, `sz0_rangeCond`, `sz0_lam_ev`), the three `rfl`/`1 ≤ K` lemmas.
- `emn2Exp_near`, `emn2Exp_far12`: `d=3`, `sz0`, `κ=ε=𝔡=1/10`, `𝔠=1/6`, `z0` (`flow_z0`), `t≡1/16`
  (`sixteenth_le_lemT`), `ε₀=1/20`, `Ψ=W^{-1}` (`Ψ1_window`), `ℓ=ℓ_t` (`ℓ_range_inst`), any `D>0`;
  remaining hypotheses `hI : STInitialGT2`, `hA : STLWassmExp` (other gates' pins; allowed).
- `emn2Exp_of_far3`: `example (h3 : …) : STEMn2Exp 3 := emn2Exp_of_far3 3 h3`.
No `N=0`, empty index, collapsed window (`ℓ=ℓ_t ≥ 1`, not `0`) or `False` premise.

## 5. Paper deltas

Every Lean/paper difference found is proposed in the prove report (d): T2109a (`2(ℓ*+1) ≤ ℓ†` used,
eventual), T2109b (`Ψ'` with `+W^{-D}`, cap `W^{-ε'}`, `ℓ⁺`; `trunc_cmp` (ii) side condition),
T2109c (no `(GijGEX)`), T2109d (reading of `R₃`, cover constant 1), T2109e (explicit losses `K_n`,
`√(1+cB⁻¹)`, `exp((log W)^{7/8})`), T2109f (unused premises kept). The near/far12 conclusions are
stronger than the pin (no `Ĵ`); no delta needed. Coverage complete.

## 6. Observations (no effect on verdict)

- O1. `emn2Exp_scale_gap` assumes `(log W)^{1/4} ≥ 4` (`W ≥ e^{256}`), so its and `profile_cmp`'s
  instances use `szA` with `W = 2^{400}`. The sharp threshold is `log W ≳ 16.94` (report (a) row 5);
  the constant is non-optimal (allowed, CLAUDE.md §7), the hypothesis is discharged eventually inside
  `emn2Exp_far12`, whose own instance is at `sz0`. Not a degenerate witness of an endpoint.
- O2. The `S12_le` instance (`L=3`, `ℓ*=1`) has every pair in `R₁` and `S̃₃` empty, with `P≡1`; the
  hypotheses are still genuinely discharged at a non-trivial `H`.
- O3. Public helper names use the prefix `emn2Exp` (stem `EMn2Exp1`), same convention as merged
  `emn2Poly_*`; no clash on `main`.
- O4. The file imports `RBM3D.Induction.Step2Iterate` in addition to the two named imports ("the merged
  files they need"; merged on `main`).

## Verdict

| target | verdict |
|---|---|
| 1 (scales, `Ψ² ≍ W^{-d}𝒯̃`, two-case comparison) | PASS |
| 2 (near case `emn2Exp_near`) | PASS |
| 3 (`S̃₁`, `S̃₂`: cover, `emn2Exp_S12_le`, `emn2Exp_far12`) | PASS |
| assembly `emn2Exp_of_far3` (conditional on ST2-11's `S̃₃`) | PASS (pin `STEMn2Exp` stays owed) |

**T2109: PASS.** No dispatcher sign-off needed.
