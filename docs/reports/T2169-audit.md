Auditor model: claude-opus-5-5

# T2169 audit, round 1 (S5-24, `RBM3D/Evolution/CltMoments2.lean`), Mon Oct  5 04:24:06 UTC 2026

Audited commit `6931a27` on `t/T2169`, detached worktree `RBM3D-wt/T2169-audit1`.

## 1. Files touched, forbidden tokens
```
$ git diff --name-only main...t/T2169
RBM3D/Evolution/CltMoments2.lean
$ git diff main...t/T2169 -- RBM3D.lean RBM3D/Test/Axioms.lean | wc -l
       0
$ grep -nE "sorry|admit|native_decide|^axiom|\baxiom\b" RBM3D/Evolution/CltMoments2.lean | head
(no output)
```
Only a sole writable file is touched. No frozen signature is changed: the diff adds one new file.

## 2. Build and axioms (audit worktree)
```
$ lake build RBM3D.Evolution.CltMoments2      # error lines + tail
ℹ [3817/3817] Built RBM3D.Evolution.CltMoments2 (6.5s)
info: ...CltMoments2.lean:1693:0: 'RBM.Evol.cltMom2_expand' depends on axioms: [propext, Classical.choice, Quot.sound]
info: ...:1694:0: 'RBM.Evol.cltMom2_moment_le' depends on axioms: [propext, Classical.choice, Quot.sound]
info: ...:1695:0: 'RBM.Evol.cltMom2_markov' depends on axioms: [propext, Classical.choice, Quot.sound]
info: ...:1696:0: 'RBM.Evol.cltMom2_decomp' depends on axioms: [propext, Classical.choice, Quot.sound]
info: ...:1697:0: 'RBM.Evol.cltMom2_norm_stcltB_le' depends on axioms: [propext, Classical.choice, Quot.sound]
info: ...:1698:0: 'RBM.Evol.cltMom2_weight_le' depends on axioms: [propext, Classical.choice, Quot.sound]
info: ...:1699:0: 'RBM.Evol.cltMom2_hzu' depends on axioms: [propext, Classical.choice, Quot.sound]
info: ...:1700:0: 'RBM.Evol.cltMom2_moment_fixed' depends on axioms: [propext, Classical.choice, Quot.sound]
info: ...:1701:0: 'RBM.Evol.cltMom2_tail_eventually' depends on axioms: [propext, Classical.choice, Quot.sound]
Build completed successfully (3817 jobs).
exit 0
$ grep -c "error" build.log
0
$ lake env lean RBM3D/Evolution/CltMoments2.lean     # independent recompile
exit 0     (no error/sorry lines)
$ lake env lean precheck.lean   # import RBM3D; import RBM3D.Evolution.CltMoments2; #assert_rbm_axioms
exit 0
axiom audit: 5124 theorems, 1780 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
premises found by scanning: 82 (borrowed 0, owed 63, structural 19).
$ grep -c CltMom2 precheck.out
0
```
The registry finds no new premise, so no `structuralProps` line is owed. That matches the untouched `Test/Axioms.lean`.

## 3. Statements against the pin (target 1, and targets 3–6 by type)
```
$ awk '/^namespace RBM.Evol.T2169Check/{f=1;next} /^end RBM.Evol.T2169Check/{f=0} f' docs/tickets/checks/T2169-check.lean \
    | grep -v "^open" | sed '/^\s*$/d' > pin.txt              # 132 lines
$ sed -n 79,225p RBM3D/Evolution/CltMoments2.lean | grep -v "^open" | sed '/^\s*$/d' > lean1.txt   # 132 lines
$ diff pin.txt lean1.txt; echo "diff exit $?"
diff exit 0
$ grep -n "^open" (file / check)      # the stripped `open` lines sit at the same relative position
file 105 / check 130: open Classical in   (same offset 25 from section start; both precede CltMom2.off)
```
The seven definitions (`Z, fluc, off, BY, DomHyp, IsoHyp, rhs`) and the six `…Stmt` match the check file exactly, docstrings included.
```
$ grep -nE "^theorem cltMom2_(decomp|norm_stcltB_le|weight_le|hzu|moment_fixed|tail_eventually)" CltMoments2.lean
975:theorem cltMom2_decomp (d : ℕ) : CltMom2.DecompStmt d := by
992:theorem cltMom2_norm_stcltB_le (d : ℕ) : CltMom2.BYStmt d := by
1009:theorem cltMom2_weight_le (d : ℕ) : CltMom2.WeightStmt d := by
1090:theorem cltMom2_hzu : CltMom2.HzuStmt := by
1147:theorem cltMom2_moment_fixed (d : ℕ) : CltMom2.MomentStmt d := by
1198:theorem cltMom2_tail_eventually (d : ℕ) : CltMom2.TailStmt d := by
```
IsoHyp compared with the inner clause of `STCltIsoConcl` (Step5Pins.lean:417-424), with `(E n)↦E`, `(s n)↦s`, `W^(-D)↦εf`, and whitespace normalised:
```
$ sed -n 417,424p Step5Pins.lean | tr -s ' \n' ' ' | sed -e 's/(E n)/E/g' -e 's/(s n)/s/g' -e 's/((sz.W n : ℕ) : ℝ) ^ (-D)/εf/' > iso_pin.txt
$ sed -n 139,145p CltMoments2.lean | tr -s ' \n' ' ' > iso_lean.txt ; cmp iso_pin.txt iso_lean.txt && echo IDENTICAL
IDENTICAL
```
`DecompStmt` has the literal left side `STfFar … ω - ∫ STfFar …`. Its far cutoff uses the orientation `b₁ - a_i` of `STfFar` (`Step5Pins.lean:362-365`). `TailStmt` keeps its parameter order: `M` comes after `(d,Λ,κ)`, and `p, D` come before `∀ᶠ n`. Its only `∀ᶠ` is that of `STCltIsoConcl`, and it has no `∀ n` premise.

**Target 2** is the prover's Lean form. The ticket fixes its hypotheses, which are checked here.
- `cltMom2_moment_le` (`:628-649`) has these hypotheses: `3 ≤ d`, `1 ≤ lw`, `1 ≤ ℓ`, `0 ≤ Mz`, `0 ≤ q₁`, `0 ≤ εf`, `hYm`, `hYB`, `hZ` (`lw³ℓ < |β₀-β₁| → Z β = 0`), `hzu` (that of `cltMom1_paired_moment_le`, CltMoments1.lean:1922-1930, at `z = ‖Z‖·(1/(|β₀-β₁|^{d-2}+1))`), `hdom` (the window tail) and `hiso` (all-window tuples with an isolated first label at `10·lw³ℓ`).
- Its right side is `2^{2p}(Λ'^{2p}+(B(w^{d-2}+1))^{2p}·card·q₁)·PB + εf(Σ‖Z‖)^{2p}`. Here `PB` is literally the right side of `cltMom1_paired_moment_le`. This is the ticket's formula, with no extra hypothesis.
- `CltMom2.X` (`:234`) has the `STcltX` shape and the convention `decide (p ≤ k.val)`.
- `cltMom2_markov` has the same hypotheses:
```
$ diff <(sed -n 628,642p F) <(sed -n 747,761p F)
1c1  (theorem name only)     15c15  (trailing ` :` only)
```
It adds `θ > 0` and has the conclusion `P{θ < ‖Σ‖} ≤ ofReal(rhs/θ^{2p})`. `cltMom2_expand` is `cltm_expand` with the two-label sum.

## 4. Hidden hypotheses, vacuity, cycles
- No new `structure` or class is introduced. `DomHyp` and `IsoHyp` are explicit `Prop` premises of `MomentStmt`/`TailStmt`. They are the per-`n` data conditions that the ticket pins (§16/§20), and they are not structure fields.
- Imports are `RBM3D.Evolution.CltMoments1` and `RBM3D.Gauss.Domination` (both merged on `main`) plus two Mathlib files. The branch diff touches nothing else, so every dependency is a merged result and there is no cycle.
- External hypothesis `STCltIsoConcl`: the limit check is preflight script C (prove report (a), rows 16, lines 54-64). It gives the concrete threshold `n ≈ 10³` at `(τ,D)=(1/10,1)`, `p=20`, for `M_w ∈ {1,10³,10⁶}`. `DomHyp` is supplied concretely at `szCL` with `q₁ = 0` (§5).

## 5. Compiled nonempty instances (all compile; §2 exit 0)
```
$ grep -n "^example" CltMoments2.lean
1333 cltMom2_expand  1339 cltMom2_moment_le  1346 cltMom2_markov  1406 cltMom2_hzu  1523 cltMom2_norm_stcltB_le
1529 cltMom2_weight_le  1543 cltMom2_decomp  1555 cltMom2_moment_fixed  1604 cltMom2_tail_eventually
1628 nonvacuity of the Z-region   1666 nonvacuity of the pairing
```
Each endpoint theorem was checked by reading its example.
- **expand / moment_le / markov** (`:1333-1350`): `Ω = Bool` uniform, `Y = ±1` (`𝔼Y = 0` proved, non-constant); `d=3`, `L=83`, `p=1`, `lw=ℓ=Mz=1`, `Λ'=2`, `q₁=0`, `εf=1`, `θ=1`; `Z` the point mass `2c` at `β⁰`, `c = uw·G > 0` (`cltMom2_c_pos`). `hZ`, `hzu`, `hdom` (empty event), `hiso` discharged by `cltMom2_toy_*`. Nondegenerate.
- **hzu** (`:1406`): `d=3`, `L=83`, `w=1`, `ρ=40`, `M=1`; `z` a two-point row at `β⁰`, `β'` with value `c₄₀ > 0` (first labels at distance 5 ≤ 20, by `decide`); conclusion at `β'` with `4^3·M`; every premise discharged (stronger than the ticket's point mass).
- **norm_stcltB_le, weight_le, decomp** (`:1523-1553`) use `szCL` for every `n`, with `E=0`, `s=sCL n`, `t=tCL n`, `σ=(+,-)`, `a=(0,0)`, `Λ=1`, `κ=1/2`.
  - The deterministic premises are discharged: `|E|<2`, `s<1`, `0<g≤1`, `0≤t<1`, the regime `(szCL_reg5I n).1`, `6 ≤ log W_n` and `1/2 ≤ Im mE 0`.
- **moment_fixed** (`:1555`): every `n ≥ 34`, `p=1`, `Λ'=BY(w+1)`, `q₁=0`, `εf=(2BY)²`; `DomHyp` by `cltMom2_domHyp_zero` (empty event), `IsoHyp` by `cltMom2_isoHyp_envelope`, `40 ≤ log W_n` by `cltMom2_log_W_ge40`; no premise left open.
- **tail_eventually** (`:1604`): `(szCL, STflowE zCL, sCL, tCL)`, `Λ=1`, `κ=1/20`, `p=1`, `D=1`; `STCltIsoConcl` from `inst_cltIso (stCltIso_holds 3) 1 one_pos`. The nine example hypotheses (`STKbound`, `STKward`, `STLK`, `STDecay`, `STDecayStrong`, `STStep1Loop`, `STStep2Concl`, `STLmaxU`, `STLKU`) are other gates' stochastic pins of `InstIng5Concl`. Every per-`n` premise is discharged for `n ≥ 34` (`|E_n| ≤ 1/2` by `abs_lemE_le`, `1/2 ≤ Im mE(E_n)`, `DomHyp` with `q₁=0`).
- **Nonvacuity** (`:1628`, `:1666`): for every `n`, `β⁰ = (x_n, x_n)` lies in the region of `CltMom2.Z` (far at `(n+24)^5 > (log W)^4`, window `0`). The pair `(β⁰,β⁰)` is `Paired` at `10w`.

The data are not degenerate: there is no `N = 0`, no empty index set, no `False` premise and no astronomically large witness. The thresholds are `n ≥ 34` and `L = 83`.

## 6. Paper deltas
Every Lean/paper statement difference below is covered by an existing entry or a proposed candidate (prove report (d)):

| Difference | Coverage |
|---|---|
| strict pairing and its complement | D391 |
| window numerator at `a₂` | D392 |
| explicit `lw^{24p}` | D393, T2169d |
| `log W ≥ 40`, `log W ≥ 2d` premises | D394, T2169c |
| `≺ ⟹ 𝔼` as `DomHyp` with envelope `BY` and tail `(Λ',q₁)` | D370, T2169a |
| `O(W^{-D})` kept as the separate term `CltMom2.off` | T2169b |
| `4^d` comparability, `M_w = C₅(1+2^{d-1})C₆d` with regime `g²/L² ≤ 1-t` | T2169c |
| one-`n` bound with explicit `Λ', q₁, εf`, centring `2^{2p}` | T2169d |

`grep -c T2169 docs/paper-deltas.md` gives 0, so the four candidates are still waiting for the dispatcher to number them.

## 7. Observations (not RETURN)
- O1: the prover cites `../RBM2D` at `c9a24cf`, and `diff --stat c9a24cf HEAD` shows later changes to `CltMoments.lean`. Since the ticket pins the port to `c9a24cf`, these later changes do not matter here.
- O2: two instance deviations, both recorded in prove report (b): the `hzu` instance uses a two-point row (stronger than the ticket's point mass); target 6 uses `abs_lemE_le` instead of `v3_premises_of_stFlow`/`nqGood1_mE_im_ge`. Neither changes a statement or weakens an instance.
- O3: `TailStmt` restricts to `σ 0 ≠ σ 1`. This is inherited verbatim from the pin `STCltIsoConcl` (case (i)), so it is not a new difference.

## Verdict per target
| Target | Verdict |
|---|---|
| 1 vocabulary/statements | PASS |
| 2 `cltMom2_expand`, `cltMom2_moment_le`, `cltMom2_markov` | PASS |
| 3 `cltMom2_decomp` | PASS |
| 4a/4b/4c `cltMom2_norm_stcltB_le`, `cltMom2_weight_le`, `cltMom2_hzu` | PASS |
| 5 `cltMom2_moment_fixed` | PASS |
| 6 `cltMom2_tail_eventually` | PASS |

**Overall: PASS.** No dispatcher sign-off needed.
