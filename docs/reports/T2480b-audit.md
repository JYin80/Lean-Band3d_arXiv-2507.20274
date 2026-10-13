Auditor model: claude-opus-5-5

# T2480b (U2b of T2480: `Chain/B45Gen`, targets 7-9 and their part of 10-11) — audit round 1
Audit worktree `../RBM3D-wt/T2480b-audit1`, detached at `t/T2480b` = df3973e4; merge base with `main` 86eb22f2; `date -u` at the build: Tue Oct 13 02:30:41 UTC 2026.

## 1. Diff, G1, hygiene, layering
```
$ git diff --name-only main...HEAD
RBM3D.lean
RBM3D/Chain/B45Gen.lean
RBM3D/Test/Axioms.lean
$ git diff main...HEAD -- RBM3D/Induction RBM3D/Loop RBM3D/BA RBM3D/Chain/{Carrier,Step2Gen,Step34Gen,DecayGen,StepDecompGen,ZeroModeGen,Step5CasesGen,Step5KerGen,KDecayGen,SEforLnGen,SEforLnGen2}.lean | wc -l   ->   0
$ grep -nE "\bsorry\b|\badmit\b|native_decide|^axiom" RBM3D/Chain/B45Gen.lean | wc -l   ->   0
$ grep -n "^import" RBM3D/Chain/B45Gen.lean
6:import RBM3D.Chain.KDecayGen
7:import RBM3D.Chain.Step34Gen
8:import RBM3D.Chain.DecayGen
9:import RBM3D.Chain.ZeroModeGen
10:import RBM3D.Chain.Step5CasesGen
11:import RBM3D.Induction.B45
$ grep -rln "import RBM3D.Chain.B45Gen" RBM3D RBM3D.lean   ->   RBM3D.lean
$ wc -l RBM3D/Chain/B45Gen.lean  ->  1244   (stop line 2,000; reserve rule 1,800: B45Gen2 not created)
```
Root import: `RBM3D.lean:562 import RBM3D.Chain.B45Gen` is the last import line; `#assert_rbm_axioms` stays last. Registry diff
(`Test/Axioms.lean`): comment text only — the `STKcalDecaygL` reader list and three owner texts rewritten to "generic: <name> (T2480); BA: U2-BA"
(`STSEforLnConclgL`, `STSEforLngL`, `STEKDecaygL`), as the ticket's Registry paragraph asks. No new scan line.

## 2. Ticket greps
```
$ U-C4: grep -nE "^(noncomputable )?(private )?def" RBM3D/Chain/B45Gen.lean
61:def B45Gen_Facts (d : ℕ) (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ),        (a Prop class)
637:private def B45Gen_farXi {sz : Sizes d} (C : FlowFM sz) (s t : ℕ → ℝ) (k : ℕ          (ℝ-valued, no kernel)
$ TN-C4 (STGridRepNgL|ST_gridMart_of_repN) / UBA-C1 (-w gK) / C6 class-(t) names: counts
0
0
0
$ X1-C1 pattern of the ticket; hits per region (band discharge 73-106, band re-derivation 1044-1069, instances 1071-1244, else)
  OTHER 29:  `sz.lam` (size level).  The condition `N⁻¹ ≤ 1 - t` that the band takes from `STFlow` (`v3_premises_of_stFlow`) is a hypothesis
OTHER 1          (module docstring)
band-rederive 7
instances 63
band-discharge 11
```
`sz.lam` occurs in the generic part only inside `ellT`, `Bparam`, `Bctl` and the mollifier (lines 319-440): size level.

## 3. Build and axioms
```
$ lake build RBM3D.Chain.B45Gen
Build completed successfully (3799 jobs).
$ lake build            # whole library, runs #assert_rbm_axioms
premises found by scanning: 126 (borrowed 1, owed 59, structural 46, refuted 6, superseded 14).
Build completed successfully (4333 jobs).
$ lake env lean docs/tickets/checks/T2480-check.lean | grep -c error
0
$ lake env lean T2480b/aud2.lean   (scratch; #print axioms lines)
'RBM.BA.B45Gen_Facts' / 'b45Gen_facts_band' / 'B45_ward_fing' / 'B45_norm_kappag' / 'B45_Psum_LK_leg' / 'B45_norm_ThetaN_leg' / 'B45_B4_leg' /
'B45_scalesg' / 'B45_detg' / 'B45_det2g' / 'stWardTypePgL_of' / 'stB45gL_of' / 'stWardTypePPingL_of' / 'stB45PingL_of' /
'stWardTypePPin_gen_band' / 'stB45Pin_gen_band'  — each: depends on axioms: [propext, Classical.choice, Quot.sound]   (16 of 16)
```

## 4. Statements against the pins (scratch `aud2.lean` = check-file lines 298-329 verbatim + the auditor checks below)
```
example : B45Gen_Facts = T2480_B45Facts := rfl
aud2.lean:45:43: error: Type mismatch  rfl ... but is expected to have type  B45Gen_Facts = T2480_B45Facts
-- compile with no error:
example : ∀ d law Flow mk T0, (∀ sz, IsProbabilityMeasure (law sz)) → Step5CasesGen_FlowFacts d Flow mk T0 → B45Gen_Facts d Flow mk →
    (∀ sz κ ε 𝔠 𝔡 z, 0 < κ → Flow sz κ ε 𝔠 𝔡 z → STKcalDecaygL (mk sz z)) → STWardTypePPingL d STCaseI law Flow mk T0 := fun d => stWardTypePPingL_of d STCaseI
example : <same, conclusion STB45PingL d STCaseI law Flow mk T0> := fun d => stB45PingL_of d STCaseI
example (d) (Flow) (mk) : B45Gen_Facts d Flow mk → T2480_B45Facts d Flow mk := ...           (drop the two added conjuncts)
example (d) : T2480_B45Facts d (STFlow …) (fun sz z => bandFM sz (STflowE z)) := ... b45Gen_facts_band ...   (check-file band shape)
```
Class diff (B45Gen.lean:61-69 against check `:302-309`, by eye on the script-extracted texts, prove report B3/B4): `B45Gen_Facts` = `T2480_B45Facts`
plus two conjuncts after `DecayGen_WardPair`:
```
(∀ n : ℕ, ((mk sz z).m n).im ≤ 1)
(∀ n : ℕ, ZeroModeGen_KerSums (mk sz z) n)
```
Every other conjunct, the quantifier order, the window `0 ≤ t < 1` and `C₆/(1-t)` are verbatim.

**Target 7** (`B45Gen_Facts`). Pinned class + 2 fields. The check header (`T2480-check.lean:8-9`) allows "a class field may be added or dropped
only with a named band discharge, reported in 1a (iii)"; the 1a deferred (iii) to 1b (`T2480-prove.md:30`), and 1b reports the two fields in
(a′) with named band discharges, both used in `b45Gen_facts_band` (B45Gen.lean:89-90): `norm_mE` + `Complex.im_le_norm`, `zeroModeGen_kerSums_band`
(merged, U1s1). Necessity check (signatures): no premise of the pins yields either fact —
```
Step5CasesGen.lean:144  sz.Admissible 𝔠 𝔡 ∧ (∀ n, T0 sz z n < 1) ∧ (∀ n, κm ≤ ((mk sz z).m n).im) ∧ ∀ n t, eta = (1 - t) * Im m
DecayGen.lean:91        def DecayGen_Spec (κm : ℝ) : Prop := 0 < κm ∧ (∀ n, κm ≤ (C.m n).im) ∧ ∀ n t, C.eta n t = (1 - t) * (C.m n).im
```
(lower bound on `Im m` only; no column-sum constancy). Uses: `ZeroModeGen_thetaKer_colConst … hker` at B45Gen.lean:260 (slots `i ≥ 1`, the band
`B45_slot_succ` turns `Σ_b G(a_i,b)` into `Σ_c G(c,a_i)`, Induction/B45.lean:744-749); `him1` at :386 (`η_u ≤ 1-u`). Without an upper bound on
`Im m_n`, an `η_u⁻¹` bound is not implied by a `(1-u)⁻¹` bound; the reason is sound. No counterexample to the pinned version was compiled
(none needed for the audit). BA: `Im m ≤ 1` is in the ticket's BA list (`BAm_norm_le_one`); `ZeroModeGen_KerSums` at BA is **not** in the
ticket's list for U2-BA (with `S = 1` at BA it reduces to constant row/column sums of `Step2Kern_Mss`). Verdict: **PASS, needs dispatcher sign-off**
(the binding class text changes, as U2a's two additions were ratified in §284 (2); U2-BA inherits one extra discharge).

**Target 8 (a)** (`stWardTypePgL_of`, `stB45gL_of`; prove report B3). Conclusions `STWardTypePgL C μ s t`, `STB45gL C μ s t` exact (merged U3s1
texts, `Step34Gen.lean:284, 295`). Hypothesis list (shape, not binding): `3 ≤ d`, `DecayGen_Spec`, `Im m ≤ 1`, `Admissible`, `WardCls`,
`WardPair`, `KerSums`, row/column sums, `STKcalDecaygL` (explicit, as the ticket's answer (5) requires), `0 ≤ s`, `t < 1`, eventual
`N⁻¹ ≤ 1 - t_n`, `STGdecayWgL`. The last deterministic one replaces the band's `STFlow`-derived `hrange`; in the pins it is derived from
`STConStInd` (B45Gen_invN_of_conStInd). No band object in the statements (X1-C1 above). **PASS.**
**Target 8 (b)** (eight public successors): the axioms list above; `B45_ward_fing`, `B45_scalesg` are checked against the band forms in the
instances (B45Gen.lean:1222-1243). **PASS.**

**Target 9** (`stWardTypePPingL_of`, `stB45PingL_of`). With `B45Gen_Facts` in place of `T2480_B45Facts`, the pins equal `T2480_WardTypePPinOf`,
`T2480_B45PinOf` (the two `example`s above compile); `R` is universally quantified (ticket: "for every `R` if the proof reads no regime"),
stronger than the pinned `STCaseI` in that respect. As stated against the literal pin text they are weaker (stronger class premise): this is
the same delta as target 7, no separate one. Band re-derivations `stWardTypePPin_gen_band : STWardTypePPin 3`, `stB45Pin_gen_band : STB45Pin 3`
compile with no hypothesis. **PASS, under the target 7 sign-off.**

## 5. Vacuity, hidden hypotheses, cycles
- `B45Gen_Facts` is a `def … : Prop`, not a structure; all fields visible in the pin types; `STKcalDecaygL` explicit.
- Dependencies are merged names (`stDecayLoopUgL_of_step2`, `QopAlgebra_commutator_ThetaNg`, `ZeroModeGen_*`, `DecayGen_*`, `Step5CasesGen_*`);
  `B45Gen` is imported only by `RBM3D.lean`: no cycle. `open private`: `B45_slot_zero B45_slot_succ B45_norm_colsum` (Induction/B45),
  `ZeroModeGen_thetaKer_colConst` (Chain/ZeroModeGen) — read, not deleted or edited.
- External/other-gate hypotheses: `STGdecayWgL` (Step 2 output, T1 / T1-BA) and `STKcalDecaygL` (registered; band `bandFM_STKcalDecay`,
  used to discharge it in every instance). Limit check of `STKcalDecaygL` at the instance: `T2480-prove.md:59` (k = 2, μ = 1, 1-u to 1e-50).

## 6. Compiled nonempty instances (B45Gen.lean:1072-1244; compiled in the build above)
Data: `d = 3`, `sz0` (`L = 4(n+1)`, `W = (2(n+1))^5`, `lam = (2(n+1))^{-6}`), `flow_z0 : STFlow sz0 (1/10) (1/10) (1/6) (1/10) z0`, window
`[0, 1/16]`, carrier `bandFM sz0 (STflowE z0)`, law `seqP sz0`, `m = 1`, mollifier `QopAlgebra_mollifier`, `X ≡ 1`.
| endpoint | instance | left as hypothesis | verdict |
|---|---|---|---|
| target 7 class | `:1100`, all 7 conjuncts at `(sz0, z0)` from `b45Gen_facts_band` | none | nondegenerate |
| `stWardTypePgL_of` | `:1111` (band `STWardTypeP`), `:1134` (`m = 1`, applied to mollifier, `X ≡ 1`) | `STGdecayWgL` (other gate), `Ξ̂ ≺ X` (induction input) | nondegenerate |
| `stB45gL_of` | `:1122`, `:1154` (same) | same | nondegenerate |
| `stWardTypePPingL_of` | `:1181` (`STCaseI`), `:1188` (`STAny`), `:1203` applied at `(sz0, z0, 0, 1/16)` | Step 2 / `STKbound`/`STKward`/`STLK` inputs of `STIngRgL` at `:1203` | nondegenerate |
| `stB45PingL_of` | `:1195` (`STCaseI`) | none | nondegenerate |
| index set | `:1095`: `Nonempty (TimeIcc 0 (1/16) n × {σ alternating} × (Fin 2 → Zd 3 (sz0.L n)))` | — | nonempty |
Every deterministic premise (`3 ≤ d`, `Admissible`, `DecayGen_Spec`, carrier facts, `STKcalDecaygL`, `t < 1`, eventual `N⁻¹ ≤ 15/16`) is
discharged at the data (`inst_hN`, `:1089`). No `N = 0`, empty index, collapsed window, `False` premise or huge witness. **PASS.**

## 7. Paper deltas
Lean/paper differences of this half: (1) `(eq:Ward_typeP)`, `(y27kasdfg)` over a flow carrier; (2) constant column sums of the Θ kernel
(`ZeroModeGen_KerSums`) and `Im m ≤ 1` as carrier inputs; (3) eventual `N⁻¹ ≤ 1 - t_n` as a hypothesis of 8 (a); (4) mollifier at `sz.lam`.
All four are in the candidate `T2480c` (prove report (d) 4). (1) overlaps U2a's `T2480a`. `docs/paper-deltas.md` has no `T2480*` entry yet
(numbered at merge, §269 (8)). Covered.

## 8. Observations (no RETURN)
- O1. Prove report B4 cites `classdiff.py` without pasting it; the auditor's checks above give the same diff.
- O2. `hlaw : ∀ sz, IsProbabilityMeasure (law sz)` is unused by both pins (kept for the pin shape).
- O3. Row total 4,181 lines (+ U2-BA twin) is past the 1.5× line; the notice REQ exists (§284 (3)); no action here.

## 9. Verdicts
| target | verdict |
|---|---|
| 7 `B45Gen_Facts` | PASS — **needs dispatcher sign-off** for the two added class fields (`Im m ≤ 1`, `ZeroModeGen_KerSums`; band discharges named; U2-BA owes `KerSums` at BA) |
| 8 (a) `stWardTypePgL_of`, `stB45gL_of` | PASS |
| 8 (b) eight generic successors | PASS |
| 9 `stWardTypePPingL_of`, `stB45PingL_of` (every `R`) | PASS under the target 7 sign-off |
| 10 / 11 (U2b part) band re-derivations, instances / G1 | PASS / PASS (diff 0) |
Overall U2b: **PASS, needs dispatcher sign-off** (target 7 class text, hence the target 9 pin hypothesis). No repair list: a refusal needs a new route.
