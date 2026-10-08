Auditor model: claude-opus-5-5

# T2321 audit (round 1): Thu Oct  8 04:23:39 UTC 2026

Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2321-audit1`, detached at `t/T2321` = `f4809fb` (merge base `e89ef53`;
`git log e89ef53..main -- RBM3D/` is empty, so the RBM3D/ tree has not changed on `main` since the base).

## 1. Scope, hygiene, name clash
```
$ git diff --name-status main...t/T2321
A	RBM3D/Induction/Step4.lean
M	RBM3D/Test/Axioms.lean
$ git diff main...t/T2321 | grep -nE "^\+.*\b(sorry|admit|axiom|native_decide)\b" | grep -v "print axioms\|depends on axioms"
(no output)
$ git diff main...t/T2321 -- RBM3D/Test/Axioms.lean | grep -c "^[-+] "
4      # -STStep3I, -STStep4I, -STStep4II (owedProps); +STStep3I (supersededProps, the ticket's comment verbatim)
$ for n in ...; git grep -n -F "$n" main -- RBM3D | grep -v RBM3D/Probe/ | wc -l
stStep4I_holds: 0  stStep4II_holds: 0  ST_mainInd_of_pins': 0  Step4Inst: 0  step4R_mono: 0  step4_of_ing: 0
step4_skeleton: 1 (docstring, IterationsA.lean:1358)  inst_step4R_dis: 0  Step4Concl: 0 as a whole word (`git grep -w`)
```
Imports of `Step4.lean` (lines 6-10) are exactly the ticket's five. No merged file other than the registry lines is touched.

## 2. Build and axioms (audit worktree)
```
$ lake build RBM3D.Induction.Step4      # errors: 0
info: RBM3D/Induction/Step4.lean:303:0: 'RBM.Ind.stStep4I_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM3D/Induction/Step4.lean:304:0: 'RBM.Ind.stStep4II_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM3D/Induction/Step4.lean:305:0: 'RBM.Gauss.Sizes.ST_mainInd_of_pins'' depends on axioms: [propext, Classical.choice, Quot.sound]
info: ...:306-312: inst_step4R_dis, inst_stStep4I, inst_stStep4II, inst_stStep4I', inst_stStep4II', inst_mainInd3'_data, inst_mainInd3'_sz0: [propext, Classical.choice, Quot.sound]
Build completed successfully (3935 jobs).
exit 0
```
Registry pre-check (scratch file = the 358 `import` lines of `RBM3D.lean` + `import RBM3D.Induction.Step4` + `#assert_rbm_axioms`,
after `lake build <all root imports> RBM3D.Induction.Step4` → `Build completed successfully (4126 jobs).`):
```
$ lake env lean precheck.lean ; echo exit $?
axiom audit: ... 0 axioms in `RBM` ... All within [propext, Classical.choice, Quot.sound]
premises found by scanning: 147 (borrowed 1, owed 87, structural 41, refuted 6, superseded 12).
registry: 2 borrowed + 137 owed + 105 structural + 7 refuted + 13 superseded; ...
exit 0
```
So the move of `STStep3I` to `supersededProps` is accepted while the unprimed `ST_mainInd_of_pins` still takes it.
Without the root import, `#assert_rbm_axioms` reports `STStep4I/II` unregistered (prove report b.4); that is expected and is the hub's import at merge.

## 3. Statements against the pin (check file section 2)
```
$ (check imports + import RBM3D.Induction.Step4 + check-file section 2 defs +)
example : RBM.Ind.T2321Check.T2321_stStep4I := RBM.Ind.stStep4I_holds
example : RBM.Ind.T2321Check.T2321_stStep4II := RBM.Ind.stStep4II_holds
example : RBM.Ind.T2321Check.T2321_mainInd_of_pins' := RBM.Gauss.Sizes.ST_mainInd_of_pins'
$ lake env lean checkeq.lean ; echo exit $?
exit 0
```
Lean text (Step4.lean:189, 193, 209-211):
```
theorem stStep4I_holds : ∀ d : ℕ, STStep4I d := fun d => step4_of_ing d STCaseI (stOeqQt'_holds d)
theorem stStep4II_holds : ∀ d : ℕ, STStep4II d := fun d => step4_of_ing d STCaseII (stOeqQtNZ'_holds d)
theorem ST_mainInd_of_pins' (d : ℕ) (h2 : STStep2 d) (h3III : STStep3R d STReg5III)
    (h3I : STStep3R d STReg5I) (h3II : STStep3II d) (h5I : STStep5I d) (h5II : STStep5II d)
    (h6I : STStep6I d) (h6II : STStep6II d) (h6III : STStep6III d) : STMainInd d
```
Targets 1-2 are the merged pins `STStep4I/II = STStep4R d STCaseI/II` (Step34Pins.lean:261-280): constants first
(`κ ε 𝔡`, `C_d`, then `∃ 𝔠d ∈ (0,1/100]`), then `𝔠, sz, z, STFlow`, `s,t` with `0 ≤ s < t ≤ lemT`, the regime, `STKbound`, `STKward`,
`STLK s`, `STConStInd 𝔠d`, `STStep1Loop`, `STStep2Concl`, `STLmaxU` ⟹ `STLKU` (every `k ≥ 1`, uniformly in `u ∈ [s,t]`, bound `B_u^k`).
This is `(Eq:L-KGt-flow)` (`1_2:1371`) at both cases of `3_5:1604`. Target 3: the binder order is the pin's.

Mathematics against the paper (`3_5:1602-1613`, `(saww02)`): the paper sets `Ξ^{(L)} ≡ 1` (from `(Eq:LGxb)`) and `Ξ^{(L-K)}_1 ≡ 1`
(from `(Gt_avgbound_flow)`), gets `Ξ̂_n ≺ (W^{-d}B_{s,0})^{-1/(4p)} + max_{n'=2}^{n-1} Ξ_{n'}`, and inducts from `n = 2`. The proof
(`step4_skeleton`, :60-148) does this: `hXiL` from `STLmaxU` (`st_prec_one_add_sup`), base `k = 1` from `STAvgU`
(`iterationsA_avg_of_STAvgU`), strong induction for `k ≥ 2` through `STXiBoot'` with `XL = XLK = 1`; `B_s ≥ N^{-2}` (`st_Bctl_ge`
at `u = s n`) and `p > 2/τ` give `B_s^{-1/(4p)} ≤ N^{τ/4}`; `st_prec_of_xi` gives `STLKU`. `STXiBoot'` (NQEndFlow.lean:95) has
`lo = 1` and no `B^{1/6}·XLK` term (checked above: the ticket's "lo = 2"/"B_u^{1/6}" text refers to `STNQConcl''`; no effect on
any statement). `𝔠d` is the bootstrap pin's (already `∈ (0,1/100]`, same `∃` position), so no `min` is needed.

## 4. Hidden hypotheses, vacuity, cycles
- `stOeqQt'_holds : ∀ d, STOeqQt' d` (QtXiRoundLift.lean:736) and `stOeqQtNZ'_holds : ∀ d, STOeqQtNZ' d` (QtNonzeroBoot.lean:1074)
  are merged theorems; `STOeqQt'/STOeqQtNZ' = STIngR d STCaseI/II STXiBoot'` (NQEndFlow.lean:127,130). Not hypotheses.
- `step4_of_ing` uses only `STIngR`'s hypotheses plus `STLmaxU`, `STStep2Concl.2.1 = STAvgU`; side conditions from the flow:
  `t < 1` (`st5_t_lt_one`), `size → ∞` (`hflow.1.2.2.1`), `0 < lam ≤ 𝔡⁻¹` eventually (`WO 𝔡`, `st5_eventually_A_ge_one`).
- No structure field carries a hypothesis; `step4R_mono` only weakens the regime (`STReg5III/I ⊆ STCaseI` by the merged
  `st_caseI_of_reg5III/I`). No import of T2320's `Step3.lean`; Step-3 regime pins enter `ST_mainInd_of_pins'` as hypotheses.
- No new external hypothesis (no limit check needed).

## 5. Compiled nonempty instances (namespace `RBM.Ind.Step4Inst`, `d = 3`, `κ = ε = 𝔡 = 1/10`, `𝔠 = 1/6`, `C_d = 1`)
```
$ #check (in checkeq.lean, exit 0 above)
inst_stStep4I : Step4Concl sz0 z0 sInst tInst 1
RBM.Ind.Step4Inst.inst_stStep4II : Step4Concl szB zB (fun x => 15 / 16) (fun x => 31 / 32) 1
RBM.Ind.Step4Inst.inst_mainInd3'_sz0 : STStep2 3 → STStep3R 3 STReg5III → STStep3R 3 STReg5I → STStep3II 3 → STStep5I 3 →
  STStep5II 3 → STStep6I 3 → STStep6II 3 → STStep6III 3 → InstMainIndRConcl STAny sz0 z0 sInst tInst
RBM.Gauss.Step34Inst.sz0_caseI : sz0.STCaseI sInst tInst
RBM.Gauss.Step34Inst.szB_caseII : szB.STCaseII (fun x => 15 / 16) fun x => 31 / 32
```
Data (merged definitions): `sz0`: `L = 4(n+1)`, `W = (2(n+1))^5`, `lam = (2(n+1))^{-6}` (Defs/Sizes.lean:260); `sInst ≡ 0`,
`tInst ≡ 1/16` (Induction/Defs.lean:439); `szB`: `L = 4`, `W = n+4`, `lam = 1` (Step34Pins.lean:710), `zB ≡ 1/2 + i/64`;
case (ii) `1 - 15/16 = 1/16 = lam²/L²`. Discharged in the instances: `3 ≤ d`, `STFlow` (`flow_z0`, `flow_zB`), `0 ≤ s < t ≤ lemT`,
the regime, `C_d > 0`, `STKbound`, `STKward` (`stKbound_of_flow`, `stKward_of_flow`), `(con_st_ind)` for every `𝔠_d > 0`
(`sz0_con`, `conStInd_const`). Kept as premises (other gates' stochastic pins): `STLK s`, `STStep1Loop`, `STStep2Concl`,
`STLmaxU` (Step 3, T2320) for T1/T2; the nine step pins for T3. No `N = 0`, empty index, collapsed window or `False` premise.
`InstMainIndRConcl` (MainIndRegimes.lean:830) is an `∃ 𝔠d` with an implication from the stochastic premises at `s`; no vacuity.

## 6. Paper deltas
- Hypothesis set of `STStep4R` (premises `STLK s`, `STKbound`, `STKward` instead of the full `lem:main_ind` assumptions): D56 (`T2041i`).
- R2* first summand at `B_{s,0}` (`STXiBoot'`): D563 (`T2246a`). Note: the paper's `(saww02)` itself already has `B_{s,0}`.
- Step 3 in `ST_mainInd_of_pins'` at the regimes `STReg5III/I` instead of `STCaseI`: a Lean assembly choice (DECISIONS §132-§133),
  `lem:main_ind`'s statement `STMainInd d` is unchanged; no new delta needed. No uncovered Lean/paper difference found.

## 7. Observations (no RETURN)
- O1. Prove report b.5 counts `ST_mainInd_of_pins': 1` hit outside Step4.lean (the new registry comment in Axioms.lean); harmless.
- O2. `Step4Concl`, `inst_step4R_dis` are public names in the ticket's instance namespace `RBM.Ind.Step4Inst` (no clash).
- O3. Merge order: T2320 also edits the `STStep3I` owed line; the hub resolves that single registry line at merge (ticket sibling scan).
- O4. `inst_mainInd3'_data` at `(szB, 0, 31/32)` relies on `conStInd_const` (an `∀ᶠ` with a large threshold at `𝔠d = 1/100`); the
  second instance `inst_mainInd3'_sz0` at `(sz0, 0, 1/16)` is a nondegenerate instance with threshold `n = 0` (prove report (a)(ii)).

## 8. Verdicts
- T1 `RBM.Ind.stStep4I_holds`: **PASS**.
- T2 `RBM.Ind.stStep4II_holds`: **PASS**.
- T3 `RBM.Gauss.Sizes.ST_mainInd_of_pins'`: **PASS**.
- Registry edit: **PASS** (pre-check exit 0 with the move to `supersededProps`).
Ticket T2321: **PASS**. No dispatcher sign-off needed.
