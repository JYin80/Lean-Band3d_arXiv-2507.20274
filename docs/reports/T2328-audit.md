Auditor model: claude-opus-5-5

# T2328 audit (round 1) — S5-13 `Induction/EtermsMid`, `stEtermsMid_of_LWT`

Written Thu Oct  8 11:15:44 UTC 2026 (`date -u`). Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2328-audit1`, detached at `t/T2328` = 0174c09
(merge-base with `main` = 4fa6d31). Scratch files: `<scratchpad>/T2328/{ax,eq,reg}.lean`, `build.log`, `reg.log`.

## 1. Statement against the pin

```
$ grep -n '^theorem stEtermsMid_of_LWT' RBM3D/Induction/EtermsMid.lean
1670:theorem stEtermsMid_of_LWT (d : ℕ) (hLWT : STLWT d) : STEtermsMid d := by
$ grep -n 'def T2328_stEtermsMid_of_LWT' docs/tickets/checks/T2328-check.lean
49:def T2328_stEtermsMid_of_LWT : Prop := ∀ d : ℕ, STLWT d → STEtermsMid d
```
Check-file equality (scratch = check-file imports + `import RBM3D.Induction.EtermsMid` + check section 2 + the ticket's `example`):
```
$ tail -3 eq.lean
example : Prop := T2328_stEtermsMid_of_LWT
example : RBM.Gauss.Sizes.T2328Check.T2328_stEtermsMid_of_LWT := RBM.Gauss.Sizes.stEtermsMid_of_LWT
end RBM.Gauss.Sizes.T2328Check
$ lake env lean eq.lean; echo "eq exit=$?"
eq exit=0
```
`STEtermsMid d := STIngR5 d STReg5Mid (fun sz E s t => STEtermsMidConcl sz E s t)` (`Step5Pins.lean:275`, merged, untouched:
`git diff main...t/T2328 -- RBM3D/Induction/Step5Pins.lean RBM3D/Induction/Step2Defs.lean` is empty). The conclusion
`STEtermsMidConcl` (`:259`) has `∀ D > 0` and, uniformly over `STIdx2 sz s t` (`u ∈ [s,t]`, `σ ∈ {±}²`, `a ∈ (Z_L^d)²`; `Fin 2` for `k`),
the bounds `A^{-1/3} η_u⁻¹ W^{-d}𝒯̃^L_{u,D}`, `A^{-1/2} η_u⁻¹ W^{-d}𝒯̃^L_{u,D}`, `A^{-1/2} η_u⁻¹ (W^{-d}𝒯̃^L_{u,D})²` with
`A = STAI = ilambda² W^d` and the scale `ℓ = L` (`(sz.L n : ℝ)`). Against the paper:
(Paper `3_5:1968-1979`, `(S5WG+M000)`, `(S5WG+M)`, read in the TeX: the same three right-hand sides with `(ilambda²W^d)^{-1/3}`, `^{-1/2}`, `^{-1/2}`.)
Exponents `1/3, 1/2, 1/2`, the scale `L`, the `η_u⁻¹` factor, the square on the third term, the window (`STReg5Mid`:
`ilambda²/L^d ≤ 1-t ∧ 1-s ≤ ilambda²`, cases (i)+(ii) of `3_5:1939`) and the parameter order of `STIngR5` (constants `κ ε 𝔡 C_d`,
then `∃ 𝔠_d ∈ (0, 1/100]`, then `𝔠`, sizes, flow, times) all agree. The target is the general pin, not a special case:
the only added hypothesis is `STLWT d`, which the ticket prescribes as an owed pin of the LW gate.

## 2. Vacuity, hidden hypotheses, cycles

```
$ grep -nE '^\s*(private )?(def|abbrev|structure|class|instance|axiom|opaque)\b' RBM3D/Induction/EtermsMid.lean
181:private def etermsMid_Kf (n : ℕ) (u : ℝ) : ℝ :=
378:private def etermsMid_Theta (n : ℕ) : ℝ := 2 * STAI sz n ^ (-(1 / 6) : ℝ) + (((sz.W n : ℕ) : ℝ) ^ d)⁻¹
$ grep -nE '^(theorem|lemma)' RBM3D/Induction/EtermsMid.lean ; grep -cE '^private (theorem|lemma)' RBM3D/Induction/EtermsMid.lean
1670:theorem stEtermsMid_of_LWT (d : ℕ) (hLWT : STLWT d) : STEtermsMid d := by
53
$ grep -nE 'sorry|admit|native_decide|^axiom|^\s*axiom ' RBM3D/Induction/EtermsMid.lean
(no output)
$ grep -nE '^import' RBM3D/Induction/EtermsMid.lean
6:import RBM3D.Induction.EMn2Exp2
7:import RBM3D.Induction.NewKLKL
8:import RBM3D.Induction.LemDecCalELip
```
- No new structure or class; the two private defs are scalar functions (a scale `K_u`, a control `Θ`), not hypotheses.
- The proof (lines 1670-1713) consumes from the pin only `hflow`, `hs`, `hst`, `htz`, `hReg`, `hCon`, `hStep2`
  (`STLocalEntryU`, `STGdecayW`); merged deterministic lemmas `stK2decay_holds`, `stNewKLKL_holds`, `stEMn2Exp_holds`, `ST_Bdata_holds`,
  `v3_premises_of_stFlow`. `STLWT d` is the only external hypothesis (owed, LW gate; producer `STLWT_of_LWtermExp`, `Step2Events.lean:1427`).
  Limit check of its premises along the instance: prove report (a)(ii), script output (`log Ψ / log W → -0.29 ∈ (-3/2, -1/20)`).
- Cycle: `LemDecCalELip` imports `Step5Pins`, `NetLift2`, `Propagator.Deriv`, `Props4` (prove report (a′), script); none imports `EtermsMid`
  (the module did not exist on `main`). The build below would fail on a cycle.
- `STIngR5` premises that are pins of other Step-5 gates are not used; `STLWT` is not circular with `STEtermsMid`
  (`STLWT` is a Step-2 LW statement, `Step2Defs.lean:421`, with no Step-5 content).

## 3. Compiled nonempty instance

```
$ sed -n 1731,1738p RBM3D/Induction/EtermsMid.lean
example (hLWT : STLWT 3) :
    InstIng5Concl (fun sz E s t => STEtermsMidConcl sz E s t) szB zB (fun _ => 7 / 8) (fun _ => 15 / 16) 1 :=
  inst_etermsMid (stEtermsMid_of_LWT 3 hLWT) 1 one_pos
example (hLWT : STLWT 3) :
    InstIng5Concl (fun sz E s t => STEtermsMidConcl sz E s t) szB zB (fun _ => 7 / 8) (fun _ => 15 / 16) 100 :=
  inst_etermsMid (stEtermsMid_of_LWT 3 hLWT) 100 (by norm_num)
```
`inst_etermsMid` (merged, `Step5Pins.lean`) = `inst_ing5_I STReg5Mid _ h (st5_reg5I_mid _ szB_reg5I)`, which discharges, at `d = 3`,
`κ = ε = 𝔡 = 1/10`, `𝔠 = 1/6`, data `szB` (`L = 4`, `W_n = n+4 → ∞`, `ilambda = 1`), flow `zB_n = 1/2 + i/64`, `(s,t) = (7/8, 15/16)`:
`STFlow` (`flow_zB`), `0 ≤ s`, `s < t`, `t ≤ lemT` (`szB_flow_ht`), the window (`1/64 ≤ 1-t = 1/16 ≤ 1-s = 1/8 ≤ 1`) and
`STConStInd` at every `𝔠_d > 0`. What remains a premise of `InstIng5Concl` are the stochastic Step 1-4 conclusions and the `s`-hypotheses
(`STKbound`, `STKward`, `STLK`, `STDecay`, `STDecayStrong`, `STStep1Loop`, `STStep2Concl`, `STLmaxU`, `STLKU`): other gates' pins, allowed
by CLAUDE.md §4 step 2. The index set (`u ∈ [7/8, 15/16]`, `σ`, `a ∈ (Z_4^3)²`) is nonempty; no `False` premise, no collapsed window,
no astronomically large witness. Two further `example`s (lines 1741, 1746) check `1/(2A) ≤ W^{-d}B_{u,0} ≤ 2/A` at `(szB, u = 15/16)` and the
exponent arithmetic `ρ^{C_d} Δ^{1/5} ≤ 2 A^{-1/6}` at `A = 8, C_d = 1, 𝔠_d = 1/100, ρ = 101/100`. All compile (build below).
Verdict on instances: present and nondegenerate.

## 4. Build and axioms

```
$ lake build RBM3D.Induction.EtermsMid ; echo exit=$?
⚠ [3819/3819] Built RBM3D.Induction.EtermsMid (11s)
Build completed successfully (3819 jobs).
exit=0
$ grep -c 'error' build.log
0
$ sed -n '476,$p' build.log | grep -E '^(warning|error)' | grep -v longLine | wc -l
0
$ cat ax.lean; lake env lean ax.lean; echo "ax exit=$?"
import RBM3D.Induction.EtermsMid
#print axioms RBM.Gauss.Sizes.stEtermsMid_of_LWT
'RBM.Gauss.Sizes.stEtermsMid_of_LWT' depends on axioms: [propext, Classical.choice, Quot.sound]
ax exit=0
```
Registry pre-check (`reg.lean` = `import RBM3D` + `import RBM3D.Induction.EtermsMid` + `#assert_rbm_axioms`, after `lake build RBM3D.Test.Axioms`):
```
$ lake build RBM3D.Test.Axioms 2>&1 | grep -E 'Built RBM3D.Test|Build completed'
✔ [2/2] Built RBM3D.Test.Axioms (3.3s)
Build completed successfully (2 jobs).
$ lake env lean reg.lean > reg.log 2>&1; echo "reg exit=$?"
reg exit=0
$ head -1 reg.log ; grep -nE 'error' reg.log | wc -l ; grep -n 'STEtermsMid' reg.log
axiom audit: 9913 theorems, 2976 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
0
85:  RBM.Gauss.Sizes.STEtermsMid: 6 [no certificate]
182: RBM.Gauss.Sizes.STEtermsMid,
```
Files touched:
```
$ git diff --stat main...t/T2328
 RBM3D/Induction/EtermsMid.lean | 1757 ++++++++++++++++++++++++++++++++++++++++
 RBM3D/Test/Axioms.lean         |    2 +-
 2 files changed, 1758 insertions(+), 1 deletion(-)
$ git diff main...t/T2328 -- RBM3D/Test/Axioms.lean | grep '^[-+] '
-   `RBM.Gauss.Sizes.STEtermsMid, -- `(S5WG+M000)`, `(S5WG+M)` (`3_5:1961-1979`); S5-01 (T2138, DECISIONS §40: owed)
+   `RBM.Gauss.Sizes.STEtermsMid, -- `(S5WG+M000)`, `(S5WG+M)` (`3_5:1961-1979`); S5-01 (T2138, DECISIONS §40: owed); proved from `STLWT` by `stEtermsMid_of_LWT` (T2328, S5-13)
```
Only the two sole writable files; the registry edit is the comment of the `STEtermsMid` line only, as the ticket asks. No frozen signature touched.
Name clash: `grep -rn -e stEtermsMid_of_LWT -e EtermsMidInst RBM3D` outside the new file: only the registry comment line.
(The full `lake build` is run by the hub at merge.)

## 5. Paper deltas

Lean/paper differences of this ticket and their coverage (prove report (d)):
- `D`-shifts (`STGdecayW` at `D+2d`, `lem:newKLK` at `D+d`) — `T2328a`.
- `lem: EWGn2_N`/`lem: EMn2_N` "at `ℓ = L`" outside their range `ℓ ≤ (log W)^{10}ℓ_u`; Lean uses `K_u = min(L, (log W)^{10}ℓ_u)` — `T2328b`.
- explicit `𝔠_d = min(1/100, 1/(30 C_d))` and constant 2 in place of `Δ_u^{1/6}` — `T2328c`.
- uniformity in `u` via the net lift (`STLWT`, `STEMn2Exp` are single-time) — `T2328d`.
- unused Step 1-4 premises of the pin — `T2328e`.
`grep -n T2328 docs/paper-deltas.md`: no entries yet (candidates only, for the dispatcher to number). Every difference I found is covered.

## 6. Observations (no statement, instance, build, axiom or delta change)

- O1. The ticket says "Imports (exactly; …)" `EMn2Exp2`, `NewKLKL`; the file adds `import RBM3D.Induction.LemDecCalELip` (merged module, no cycle,
  needed for the Hölder moduli of the net lift). Reported by the prover as a ticket defect (F1). Does not change the statement or the axioms.
- O2. Size 1757 lines against the estimate 700/900/1300 and the stop rule (1500 at a section boundary); reported in prove report (d) item 2.

## Verdict

- `stEtermsMid_of_LWT`: **PASS**. Statement equals the pin (check-file equality exit 0); no hidden hypotheses or cycle; compiled
  nondegenerate instances at `d = 3`; module builds; axioms are the three standard ones; only the sole writable files are touched;
  the paper deltas are proposed as `T2328a`–`T2328e`.
