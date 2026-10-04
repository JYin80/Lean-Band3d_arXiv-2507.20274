Auditor model: claude-opus-5-5
# T2134 audit (round 2): Sun Oct  4 15:53:36 UTC 2026
Branch `t/T2134` @ `7b2b789` (repair of round 1 at `36fbd3c`), base `3389d24`; audit worktree `../RBM3D-wt/T2134-audit2` (detached). Ticket type: report only (design); the probe `RBM3D/Probe/T2134Pins.lean` stays on the branch. Scratch: `<scratchpad>/T2134/audit2/`.

## 1. Diff scope, build, axioms, hygiene
```
$ git diff --name-only main...t/T2134
RBM3D/Probe/T2134Pins.lean
$ git diff --stat 36fbd3c 7b2b789
 RBM3D/Probe/T2134Pins.lean | 387 ++++++++++++++++++++++++++++++++++++++++++++-
 1 file changed, 380 insertions(+), 7 deletions(-)
$ diff <(git show 36fbd3c:RBM3D/Probe/T2134Pins.lean | head -1708) <(head -1708 RBM3D/Probe/T2134Pins.lean) && echo ...
lines 1-1708 (pins, skeletons) identical to round-1 commit 36fbd3c
$ git diff 36fbd3c 7b2b789 | grep "^-"      (all deleted lines)
-* case (iv) `szG`, `(s,t) = (5/8, 3/4)`:       `1-t = 1/4 ≤ 1-s = 3/8 ≤ 25/64`.
-/-- `lem;CLT` at `(szB, zB, 7/8, 15/16)`. -/
-    InstIng5Concl (fun sz E s t => STCltFarConcl sz E s t) szB zB (fun _ => 7 / 8) (fun _ => 15 / 16) Cd :=
-  inst_ing5_I STReg5I _ h szB_reg5I Cd hCd
-/-- `(eq:bound_isolated)` at `(szB, zB, 7/8, 15/16)`. -/
-    InstIng5Concl (fun sz E s t => STCltIsoConcl sz E s t) szB zB (fun _ => 7 / 8) (fun _ => 15 / 16) Cd :=
-  inst_ing5_I STReg5I _ h szB_reg5I Cd hCd
$ time lake build RBM3D.Probe.T2134Pins > build.out 2>&1; echo exit=$?; tail -2 build.out
exit=0
Build completed successfully (3774 jobs).
$ grep -E "warning|error" build.out | grep -c Probe
0            (39 warning lines, all in merged files Step2Defs/Step34Pins/KLFinal)
$ grep "depends on axioms" build.out | sed 's/.*depends on axioms: //' | sort | uniq -c
  99 [propext, Classical.choice, Quot.sound]
$ comm -3 <theorem names declared> <#print axioms names>
of           (the docstring word "theorem of"; every one of the 99 theorems has its #print axioms line)
$ grep -nwE "sorry|admit|native_decide|axiom" RBM3D/Probe/T2134Pins.lean | grep -v "print axioms"
(none)
```
Only the sole writable probe file is on the branch; the prove report (300 lines, line 1 `Prover model: claude-sonnet-5-5`) and `T2134-portmap.md` are in the main worktree. No frozen signature is touched.

## 2. Statements
The pins, `STIngR5`, `STStep5Concl`, the regimes and the skeletons (lines 1-1708) are byte-identical to the round-1 commit (§1). The round-1 statement checks against `1_2:1290-1300`, `1_2:1376-1388`, `3_5:1935-2383` therefore stand unchanged: every pin PASS on its statement (round-1 table: `STStep5I..IV`, `STStep5`, `ST_step5_assembly`, `STTailtoTail`, `STLemDecCalE`, `STPfStep5`, `STEtermsMid`, `STDuhamelI/II`, `STIniTermI/II`, `STWardII`, `STCltFar`, `STCltIso`, `STExpInv`, `STNewKLKL`). Constants before the sequence (`∀ κ ε 𝔡 C_d, ∃ 𝔠_d ∈ (0,1/100], ∀ 𝔠 sz z`); no hypothesis in a structure field; no pin depends on itself; the skeletons use only merged declarations and probe pins as hypotheses.

## 3. Round-1 Required items
### Item 1 and 2: CLT instances at nondegenerate data
New data `szCL`: `m = n+24`, `L_n = 2m^5`, `W_n = 2^m`, `ilambda = 1`, `z_n = 1/2 + i/(2L_n²)`, `s ≡ 0`, `1-t_n = L_n^{-2}`. `inst_cltFar`, `inst_cltIso` now go through the generic `inst_ing5` with every deterministic hypothesis discharged by a named lemma: `flow_zCL : STFlow szCL (1/10) (1/10) (1/6) (1/10) zCL`, `0 ≤ s`, `szCL_hst : s < t`, `lemT_zCL : t ≤ lemT z`, `szCL_reg5I`, `szCL_con` (`STConStInd` for every `𝔠_d > 0`). Auditor check (`AuditCLT.lean`, outside the repo):
```
$ cat AuditCLT.lean   (excerpt)
abbrev UFar (n : ℕ) : Type := {p : {σ : Fin 2 → Bool // σ 0 ≠ σ 1} × (Fin 2 → Zd 3 (szCL.L n)) //
   log(W)^5 * ellT .. (sCL n) ≤ ellT .. (tCL n) ∧ |a₁-a₂| ≤ 1/2 log(W)^(3/2) ellT(t) + log(W)^(5/2) ellT(s)}   -- typed in full
example (n : ℕ) : Nonempty (UFar n) := szCL_cltFar_index_nonempty n
-- the U of STCltFarConcl at szCL is definitionally UFar:
example (E : ℕ → ℝ) (h : STCltFarConcl szCL E sCL tCL) : ∃ ξ ζ, Prec szCL (U := UFar) ξ ζ := ⟨_, _, h⟩
-- the isolation witness discharges the premises of STCltIsoConcl at p = 1 (the conclusion is a real W^{-D} bound):
example (E) (h : STCltIsoConcl szCL E sCL tCL) (D) (hD : 0 < D) : ∀ᶠ n in atTop, ∀ σ, σ 0 ≠ σ 1 →
    ∃ b : Fin (2 * 1) → (Fin 2 → Zd 3 (szCL.L n)), ‖∫ ω, ∏ k, STcltX szCL n (E n) (sCL n) σ (b k) (decide (1 ≤ k.val)) ω ∂(szCL.seqP)‖
      ≤ ((szCL.W n : ℕ) : ℝ) ^ (-D) := by
  filter_upwards [h 1 le_rfl D hD] with n hn σ hσ
  obtain ⟨b, hb1, hb2⟩ := szCL_cltIso_witness n
  exact ⟨b, hn σ hσ b hb1 hb2⟩
-- regime (i) at szCL hits both boundaries:
example (n : ℕ) : szCL.lam n ^ 2 / ((szCL.L n : ℕ) : ℝ) ^ 2 = 1 - tCL n ∧ 1 - sCL n = szCL.lam n ^ 2
$ lake env lean AuditCLT.lean; echo exit=$?
inst_cltFar : STCltFar 3 → ∀ (Cd : ℝ), 0 < Cd → InstIng5Concl (fun {d} sz E s t => sz.STCltFarConcl E s t) szCL zCL sCL tCL Cd
inst_cltIso : STCltIso 3 → ∀ (Cd : ℝ), 0 < Cd → InstIng5Concl (fun {d} sz E s t => sz.STCltIsoConcl E s t) szCL zCL sCL tCL Cd
'RBM.Gauss.T2134Inst.inst_cltFar' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.T2134Inst.inst_cltIso' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.T2134Inst.szCL_cltFar_index_nonempty' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.T2134Inst.szCL_cltIso_witness' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.T2134Inst.szCL_con' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.T2134Inst.flow_zCL' depends on axioms: [propext, Classical.choice, Quot.sound]
exit=0
```
So the index set of `STCltFarConcl` is nonempty at every `n` (element `σ = (+,-)`, `a = (x_n, 0)`, `|a₁-a₂| = L_n/2`), and a `p = 1` configuration meets the window and isolation premises of `STCltIsoConcl` at every `n`. The data hit both boundaries of case (i) (`1-t = g²/L²`, `1-s = g²`) and sit in the large-`ρ` branch of `(eq:assmtlarge)` (`ρ = L_n² = 4m^{10} > (log W_n)^{10} = (m log 2)^{10}`), which is the branch where `lem;CLT` is used. **Item 1: done. Item 2: done.**

Size of the data (not a defect): `W_0 = 2^24`, `L_0 ≈ 1.6·10^7`. The pin forces this scale. Its index condition needs `ℓ_t/ℓ_s ≥ (log W)^5` with `ℓ_t ≤ L`, and `Bandwidth (1/6)` needs `L ≤ W`. Together they give `(log W)^5 ≤ W`, i.e. `W ≳ 3·10^5`. The witness is therefore within the paper's own asymptotic regime. It does not make a hypothesis hold vacuously.

### Item 3: paper-delta for the conditional form of `STDuhamelConcl`
```
$ grep -n "T2134j" docs/reports/T2134-prove.md | cut -c1-140
278:- `T2134j` (repair, audit round 1, Required 3): the integrated hierarchy `(iois-mtx2)` (`3_5:2067`) bounds `(𝓛-𝒦)_t` by the random initia
```
It covers case (i) (`STDuhamelI`, `Q = ∅`) and case (ii) (`STDuhamelII`). **Done.**

### Item 4: disclosure of index sets per instance
b.5 (lines 185-208), b.10 item 10 and portmap P.7c now state, for each instance, whether the conclusion's index set is nonempty at the data. One exception is disclosed: the conjunct `STDecayStrongU` (index `g² ≤ 1-t`) is empty in `inst_step5I/II/IV`, `inst_step5IV_proved`, `inst_skeletonI/II`. This emptiness is forced by the paper and is not a choice of data. In cases (i), (ii), (iv), `s < t` gives `1-t < 1-s ≤ g²`, and `(Eq:Gdecay+s<g_flow)` is stated only for `1-t ≥ g²` (1_2:1384). The main conjunct `STGdecayW … 0` of those instances is nonempty (`TimeIcc`, all `σ, a`), and `STDecayStrongU` is nonempty at `sz0` (`inst_step5`, `inst_step5III`, `inst_skeletonIII`, `inst_pfStep5`). **Done.**

## 4. Compiled nonempty instances (all endpoint pins)
28 `inst_*` theorems compile (build §1). Data: case (i) `(szB, zB, 7/8, 15/16)`; CLT of case (i) `(szCL, zCL, 0, 1-L_n^{-2})`; (ii) `(szB, zB, 15/16, 31/32)`; (iii) `(sz0, z0, 0, 1/16)`; (iv) `(szG, zB, 5/8, 3/4)`. The deterministic hypotheses of `STIngR5` are discharged. The stochastic premises are other gates' pins (`STKbound`, `STKward`, `STLK`, `STDecay`, `STDecayStrong`, `STStep1Loop`, `STStep2Concl`, `STLmaxU`, `STLKU`) and stay as hypotheses, which the rules allow. Extreme inputs per case: round-1 `AuditExtreme.lean` (case (i) at `1-s = g²`, `1-t = g²/L²`; case (iv) at `1-s = g²/L³`; tailtoTail at `s = t = 0`, `1-t = g²`) plus `szCL` above. The probe instances are unchanged.

## 5. Paper deltas
Candidates `T2134a`–`T2134j` in prove report (d) cover the differences found in round 1. The new `T2134j` closes the one uncovered major item. Two minor differences remain uncovered (round-1 §5): `STCltIso` drops the far-from-`a` restriction, and `STTailtoTail` allows any real `D`. Both are stronger forms, so they are recorded as Observation 4 and are not grounds for a RETURN.

## 6. Verdict per target
| target | verdict |
|---|---|
| 1 inventory (script output, file:line at `c9a24cf`) | PASS |
| 2 pins (all 18; statements unchanged since round 1) | PASS |
| 3 exponent table, 4 routes, 6 split (29 tickets, band 25–40) | PASS |
| 5 compiled skeletons (cases (i)–(iv), assembly `STDecay ∧ STDecayStrong`) | PASS |
| 7 instances (28, incl. `inst_cltFar`, `inst_cltIso` at `szCL` with compiled nonempty index / isolation witness) | PASS |
| build / axioms / hygiene / scope | PASS |

**Overall: PASS.** The ticket is report-only, so the probe stays on the branch. The prove report (d) "Open / for the dispatcher" asks for sign-off on candidates `T2134a`–`T2134j` and on the registry classes. That is the normal dispatcher numbering step (CLAUDE.md §1); no audit decision depends on it.

### Observations (no RETURN)
1. `inst_newKLKL` is at `H = 0`, `u = 0` (`δ₀` is existential; precedent T2039 O3).
2. Route of `STStep5` (S5-29, gluing sub-intervals): the case pins need `STStep2Concl` on each sub-interval with loss base `s'`. The regime is per `n`, while the pins quantify `∀ n`. Segments are strict `s < t`. Row S5-29 lists no ST-2 dependency. This is for the dispatcher to settle when S5-29 is ticketed (carried over from round 1).
3. Premises `STKbound`, `STKward`, `STStep1Loop`, `STStep2Concl` are marked "not listed" in the registry paragraph. They are owed by KL7, KL12, ST-1 and ST-2.
4. Paper-delta coverage: no candidate yet covers `STCltIso` without the far-from-`a` condition, or `STTailtoTail` for any real `D`. Both are stronger than the paper. The dispatcher may fold them into `T2134e` / `T2134b`.
5. `szCL` is large (`W_0 = 2^24`), but this is forced by the pin's index condition together with `Bandwidth (1/6)` (§3).
6. The prove report is exactly 300 lines (the limit). Sections b.1, b.8 and (c) describe `36fbd3c`; the repair section updates the counts to `7b2b789` (2434 lines, 99 theorems), which agree with the §1 outputs above.
